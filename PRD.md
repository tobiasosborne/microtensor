# MicroTensor — Product Requirements Document

**Verified tensor algebra: Julia computes, Lean 4 proves.**

Version 0.1 — March 2026

---

## 1. Problem statement

Computer algebra systems produce results without proofs. When TensorGR.jl simplifies R_{abcd} + R_{abdc} to zero, the only evidence of correctness is that the test suite passes. If the canonicaliser has a sign bug, downstream results are silently wrong. Published calculations inherit this uncertainty.

Lean 4 can produce machine-checked proofs of algebraic identities, but it is too slow for large-scale symbolic computation. Nobody will do a 10,000-term tensor simplification in Lean.

MicroTensor closes the gap: Julia does the computation (fast), emits a proof trace (a sequence of rewrite steps), and Lean replays the trace to produce a verified proof (correct by construction). The trace is the bridge. Julia is the oracle; Lean is the kernel.

**This is a prototype.** Its purpose is to validate that the loop works, identify what's hard, and inform the design of the full system (Theoria). It needs to work for one identity. Everything else is future work.

---

## 2. Goals and non-goals

### Goals

**G1.** Close the full loop for one tensor identity: R_{abcd} + R_{abdc} = 0. Julia computes it, emits a JSON proof trace, a replayer generates a Lean 4 file, `lake build` typechecks the proof.

**G2.** The Julia and Lean sides share an IR. Same constructors, same fields, same semantics. The JSON interchange format is a direct serialisation of this shared IR.

**G3.** The Lean proof is built from a small set of axioms (rewrite rules) that are individually obvious. The proof is a chain of `rw` applications — one per trace step.

**G4.** The system extends to a second identity (e.g., R_{abcd} + R_{bacd} = 0) by adding zero new axioms and one new test case.

**G5.** All design decisions, surprises, and failures are recorded in NOTES.md for the benefit of the full system design.

### Non-goals

**N1.** Generality. This handles sums of tensors related by slot symmetry, nothing else. No products, no contractions, no derivatives, no metrics, no Grassmann parity.

**N2.** Performance. Expression trees can be depth 10, not depth 10,000. The Lean proof can take seconds to check.

**N3.** Automation of the Lean side. The replayer generates `.lean` source as text. It does not need to use the Lean API, metaprogramming, or tactic frameworks.

**N4.** Replacing TensorGR.jl. MicroTensor is standalone. It does not depend on or modify TensorGR.jl. It informs the future extraction of IndexAlgebra.jl but does not attempt it.

**N5.** Proving the axioms from a semantic model. The axioms are axioms, not theorems. They define the equational theory. Deriving them from multilinear algebra is a separate project.

---

## 3. Architecture

### 3.1 Three components

```
┌──────────────────┐     JSON trace      ┌──────────────┐
│  Julia            │ ──────────────────→ │  Replayer     │
│  MicroTensor.jl   │                     │  (script)     │
│                   │                     │               │
│  • IR types       │                     │  Reads JSON,  │
│  • Simplifier     │                     │  emits .lean  │
│  • Trace emitter  │                     │  source       │
└──────────────────┘                     └──────┬───────┘
                                                │ .lean file
                                                ▼
                                         ┌──────────────┐
                                         │  Lean 4       │
                                         │               │
                                         │  • IR types   │
                                         │  • Axioms     │
                                         │  • Generated  │
                                         │    proof      │
                                         │               │
                                         │  lake build   │
                                         │  → ✓ or ✗     │
                                         └──────────────┘
```

The replayer is the simplest component: it templates Lean source from structured data. It can be written in Julia, Python, or bash. Pick whatever gets it working fastest.

### 3.2 Shared IR

Both sides implement the same algebraic data type.

**Index:**
```
Index := { name : String, position : Up | Down }
```

**Expressions:**
```
TExpr :=
  | Zero
  | Scalar(num : Int, den : Int)           -- rational number
  | Tensor(name : String, indices : [Index])
  | SMul(num : Int, den : Int, expr : TExpr) -- scalar multiple
  | Sum(left : TExpr, right : TExpr)        -- binary sum
```

**Design notes:**
- Binary `Sum`, not n-ary. Lean induction works on binary constructors. Julia flattens via smart constructors.
- Rationals as `(num, den)` pairs, not a language-specific rational type. JSON-friendly, language-agnostic.
- `SMul` is separate from `Scalar * Tensor` because it's the normal form that `Collect` produces. Having it as a constructor avoids pattern-matching gymnastics.
- No `Prod` (tensor product). The MVP doesn't need contraction or multi-tensor expressions.

### 3.3 Registry

A list of symmetry declarations:

```
Symmetry :=
  | Antisym(tensor : String, slot1 : Nat, slot2 : Nat)
  | Sym(tensor : String, slot1 : Nat, slot2 : Nat)
```

Slots are 1-indexed in Julia, 0-indexed in Lean (each side uses its native convention). The JSON schema uses the Julia convention (1-indexed). The Lean replayer adjusts.

Actually — pick one convention and stick with it everywhere. **Use 0-indexed in the JSON schema and Lean. Use 1-indexed in Julia internally but convert on serialisation.** The conversion is `slot - 1` at the JSON boundary. One place, one direction, no confusion.

### 3.4 Proof steps

```
ProofStep :=
  | SwapSlots(tensor : String, slot1 : Nat, slot2 : Nat, path : [Nat])
  | Collect(path : [Nat])
  | ZeroElim(path : [Nat])
  | SumZero(path : [Nat])
```

`path` addresses a subtree: `[]` = root, `[0]` = left child of root, `[1]` = right child, `[1,0]` = left child of right child of root, etc.

Each step is self-contained: given the current expression and the step, the next expression is deterministic. The Lean verifier checks each step by applying the corresponding axiom via `rw`.

### 3.5 Proof trace (the JSON interchange)

```json
{
  "registry": [ <symmetry declarations> ],
  "expr": <TExpr>,
  "steps": [ <ProofStep>, ... ],
  "result": <TExpr>
}
```

The `result` field is redundant (computable from `expr` + `steps`) but useful for debugging: Julia asserts the trace replays to `result`, and the Lean side can sanity-check before attempting the proof.

### 3.6 Axiom set (Lean)

Seven axioms. Each corresponds to one kind of proof step.

| # | Name | Statement | Used by step |
|---|------|-----------|-------------|
| 1 | `antisym_swap` | `tensor(R, swap(idxs, i, j)) = smul(-1, 1, tensor(R, idxs))` | `SwapSlots` |
| 2 | `sym_swap` | `tensor(R, swap(idxs, i, j)) = tensor(R, idxs)` | `SwapSlots` (symmetric case) |
| 3 | `tensor_as_smul` | `tensor(R, idxs) = smul(1, 1, tensor(R, idxs))` | `Collect` (normalises bare tensors) |
| 4 | `collect_smul` | `sum(smul(a,d,e), smul(b,d',e)) = smul(a*d'+b*d, d*d', e)` | `Collect` |
| 5 | `smul_zero` | `smul(0, d, e) = zero` | `ZeroElim` |
| 6 | `sum_zero_left` | `sum(zero, e) = e` | `SumZero` |
| 7 | `sum_zero_right` | `sum(e, zero) = e` | `SumZero` |

Plus one structural lemma:
| 8 | `smul_smul` | `smul(a,b, smul(c,d, e)) = smul(a*c, b*d, e)` | `SwapSlots` (when swapping inside `SMul`) |

These axioms are the *definition* of the equational theory. They are obviously consistent (standard linear algebra provides a model). They are declared as `axiom` in Lean, not proved from deeper foundations.

---

## 4. Data flow for target identity

**Input:** R_{abcd} + R_{abdc} with registry declaring Antisym(:R, 3, 4).

**Julia computation:**

1. Build `Sum(Tensor("R",[a,b,c,d]), Tensor("R",[a,b,d,c]))`.
2. Observe: right tensor differs from left in slots 3,4. Registry says these slots are antisymmetric.
3. **Step 1 (SwapSlots):** Apply antisymmetry to right term. `Tensor("R",[a,b,d,c])` → `SMul(-1,1, Tensor("R",[a,b,c,d]))`.
4. Expression is now: `Sum(Tensor("R",[a,b,c,d]), SMul(-1,1,Tensor("R",[a,b,c,d])))`.
5. **Step 2 (Collect):** Both summands are scalar multiples of the same tensor (the left is implicitly `SMul(1,1,...)`). Collect: `SMul(1*1 + (-1)*1, 1*1, Tensor("R",[a,b,c,d]))` = `SMul(0,1,...)`.
6. **Step 3 (ZeroElim):** `SMul(0,1,...)` → `Zero`.

**Emitted trace:** 3 steps. JSON ≈ 30 lines.

**Generated Lean proof:**

```lean
theorem riemann_antisym_34 :
    sum (tensor "R" [a,b,c,d]) (tensor "R" [a,b,d,c]) = zero := by
  -- Step 1: swap slots 2,3 (0-indexed) in right summand
  conv_rhs => rw [show [a,b,d,c] = [a,b,c,d].swap 2 3 from by native_decide]  -- if needed
  rw [antisym_swap ...]
  -- Step 2: normalise left tensor, then collect
  rw [tensor_as_smul ...]
  rw [collect_smul ...]
  -- Step 3: zero elimination
  rw [smul_zero]
```

Exact syntax will be determined by what Lean accepts. The replayer generates this text mechanically from the trace.

---

## 5. Component specifications

### 5.1 Julia: MicroTensor.jl

**File:** `julia/MicroTensor.jl`

A single-file Julia module. No dependencies except JSON.jl (stdlib-adjacent, `Pkg.add("JSON")`).

**Exports:**
- IR types: `Index`, `TExpr` subtypes (`TeZero`, `TeScalar`, `TeTensor`, `TeSMul`, `TeSum`)
- Smart constructors: `te_zero()`, `te_scalar(v)`, `te_tensor(name, idxs)`, `te_smul(c, e)`, `te_sum(a, b)`
- Index helpers: `up(s)`, `down(s)`
- Registry: `Registry`, `Antisym`, `Sym`
- Core function: `simplify_traced(expr, registry) → ProofTrace`
- Serialisation: `emit_trace(trace; io=stdout)`

**Simplifier:** The MVP simplifier is not a general-purpose engine. It handles exactly one pattern: `Sum(T₁, T₂)` where T₁ and T₂ are tensors (possibly with scalar prefactors) that differ only by a slot swap. It:

1. Compares index lists to find differing slots.
2. Checks the registry for a symmetry declaration on those slots.
3. Applies the swap (introducing a sign for antisymmetry).
4. Collects the scalar coefficients.
5. Eliminates zeros.

Each step is recorded in the trace.

**Test:** `julia/test_emit.jl` builds R_{abcd} + R_{abdc}, simplifies, asserts result is zero, emits JSON trace.

### 5.2 Lean: MicroTensor library

**Files:** `lean/MicroTensor.lean`, `lean/Rules.lean`

`MicroTensor.lean` defines the inductive `TExpr` type and helper functions (`List.swap`, etc.). Must derive `BEq` and `DecidableEq` on `Position`, `Index`, and `TExpr` so that `native_decide` works for concrete equality checks.

`Rules.lean` declares the 7–8 axioms listed in §3.6. Each axiom is a universally quantified equation between `TExpr` values.

**Critical requirement:** `lake build` must succeed on these two files alone, with no errors and no `sorry`. This validates the axiom set is syntactically coherent and the types are well-formed.

### 5.3 Lean: Example.lean (hand-written proof)

**File:** `lean/Example.lean`

A hand-written proof of `sum (tensor "R" [a,b,c,d]) (tensor "R" [a,b,d,c]) = zero`. This is the proof the replayer will auto-generate. Writing it by hand first:
- Validates the axiom set is sufficient (you can actually build the proof).
- Discovers what Lean syntax/tactics the replayer needs to emit.
- Identifies elaboration issues (implicit arguments, `native_decide` performance, etc.).

If `Example.lean` typechecks, the Lean side is done. Everything after is automation.

### 5.4 Replayer

**File:** `scripts/replay.jl` (or `.py` or `.sh` — language doesn't matter)

**Input:** JSON proof trace on stdin or as file argument.
**Output:** A `.lean` file on stdout containing a theorem + proof.

The replayer:
1. Parses the JSON.
2. Extracts the expression and steps.
3. Generates Lean `def` statements for each index used.
4. Generates the theorem statement: `theorem <name> : <expr> = <result>`.
5. Generates the proof body: a sequence of `rw [...]` calls, one per step.
6. Writes the complete `.lean` file with imports.

The generated file must typecheck under `lake build`.

### 5.5 End-to-end script

**File:** `scripts/prove.sh`

```bash
julia julia/test_emit.jl > trace.json
julia scripts/replay.jl trace.json > lean/Generated.lean  # or python/bash
cd lean && lake build
```

Exit 0 = proof verified. Exit nonzero = something failed.

---

## 6. File layout

```
theoria-proto/
├── README.md                 # Overview, branch strategy
├── QUICKSTART.md             # How to get started
├── NOTES.md                  # Running design notes
├── PRD.md                    # This document
├── shared/
│   ├── ir.md                 # IR specification (the contract)
│   └── schema.json           # JSON schema for proof traces
├── julia/
│   ├── MicroTensor.jl        # IR + simplifier + trace emitter
│   └── test_emit.jl          # Test: R_{abcd} + R_{abdc} = 0
├── lean/
│   ├── lakefile.lean          # Lake build config
│   ├── lean-toolchain         # Lean version pin
│   ├── MicroTensor.lean       # IR types
│   ├── Rules.lean             # Axioms
│   └── Example.lean           # Hand-written proof (template for replayer)
└── scripts/
    ├── prove.sh               # End-to-end script
    └── replay.jl              # Trace → .lean generator (or .py/.sh)
```

---

## 7. Build order

The dependency order is strict. Do not skip ahead.

**Step 1: Lean library (`MicroTensor.lean` + `Rules.lean`).**
Get `lake build` to succeed with just these two files. This forces you to resolve all type-level issues (DecidableEq, List.swap, axiom syntax) before writing any proofs.

**Step 2: Hand-written proof (`Example.lean`).**
Write the proof manually. This discovers the exact `rw` invocations the replayer must generate. If a step doesn't work (e.g., Lean can't unify the `rw` target), adjust the axiom formulation in Rules.lean until it does. Iterate until `lake build` passes with all three files.

**Step 3: Julia (`MicroTensor.jl` + `test_emit.jl`).**
Get `julia test_emit.jl` to produce valid JSON. Verify the JSON matches what `Example.lean` proves (same expression, same steps in the same order).

**Step 4: Replayer.**
Write the replay script. Test: `replay.jl trace.json` produces output that matches `Example.lean` (modulo variable names and formatting). Check: the generated `.lean` file typechecks.

**Step 5: End-to-end.**
Run `prove.sh`. If it passes, the loop is closed. Commit.

**Step 6: Second identity.**
Add a test for R_{abcd} + R_{bacd} = 0 (antisymmetry in slots 1,2). This should require zero changes to the Lean library and zero new axioms — only a new Julia test case and a new invocation of the replayer. If it requires changes, record why in NOTES.md.

---

## 8. Test strategy

### 8.1 Lean-side tests

The Lean typechecker IS the test. If `lake build` passes, the proofs are correct. There are no separate test files. The proofs are the tests.

### 8.2 Julia-side tests

`test_emit.jl` is the test. It:
- Constructs the expression.
- Calls `simplify_traced`.
- Asserts the result is `TeZero`.
- Asserts the trace has exactly 3 steps.
- Emits the trace to stdout.

Add more test files for additional identities. Each test file is self-contained.

### 8.3 Integration test

`scripts/prove.sh` is the integration test. It runs the full loop. CI (if any) runs this script.

---

## 9. Risks and mitigations

### R1: Lean elaboration fights the proof structure (HIGH probability)

The `rw` tactic may not find the rewrite target, or may need explicit type annotations, or may apply the rule in the wrong direction.

**Mitigation:** Step 2 (hand-written proof) exists precisely to discover these issues. Adjust axiom formulations, add `@[simp]` attributes, or use `conv` tactics as needed. Record what works in NOTES.md — the replayer will mimic whatever syntax the hand-written proof uses.

### R2: `native_decide` is slow or fails (MEDIUM probability)

The proof may need `native_decide` to show that `[a,b,d,c] = [a,b,c,d].swap 2 3` (a concrete list equality). If `native_decide` chokes, alternatives are:
- `decide` (slower but always works for decidable props)
- Have the replayer emit an explicit `rfl`-based proof
- Restructure the axioms to avoid needing the list equality (e.g., make `antisym_swap` take the swapped indices directly rather than via `List.swap`)

### R3: The simplifier is too naive (LOW probability, LOW impact)

The MVP simplifier only handles two-term sums where the terms differ by one slot swap. More complex identities (three-term Bianchi, nested products) are out of scope. This is not a risk for the MVP — it's a deliberate limitation.

### R4: The JSON is too verbose or too terse (LOW probability)

If the trace format turns out to be inconvenient, change it. The schema is a prototype. The architectural insight (Julia computes, emits trace, Lean replays) does not depend on JSON field names.

---

## 10. Success criteria

1. `cd lean && lake build` passes, including a proof (hand-written or generated) of R_{abcd} + R_{abdc} = 0.

2. `julia julia/test_emit.jl` produces a valid JSON trace with 3 proof steps.

3. The replayer converts the trace to a `.lean` file that typechecks.

4. `scripts/prove.sh` runs end-to-end with exit code 0.

5. A second identity (R_{abcd} + R_{bacd} = 0) works without modifying the Lean axioms.

6. NOTES.md contains at least 3 entries documenting things learned.

---

## 11. What we learn from this

The prototype answers these questions for the Theoria design:

- **Is the axiom approach viable, or do we need a semantic model?** If the axiom set works cleanly for the MVP identities, it's viable. If we keep needing ad-hoc axioms for each new identity, we need a model.

- **How does `rw`-chain proof generation scale?** If the hand-written proof for one identity takes 4 `rw` steps, and each new identity adds ~4 steps, the replayer is straightforward. If the proof structure varies wildly between identities, the replayer needs to be smarter.

- **What is the right granularity for proof steps?** The MVP has fine-grained steps (one per rewrite). Maybe coarser steps ("canonicalise this subtree") would be better. The prototype reveals the right level.

- **What are the Lean elaboration pain points?** Every issue encountered in Step 2 (hand-written proof) is a data point for the full system's Lean library design.

- **Is the shared IR the right IR?** If the Julia and Lean representations diverge during development (because one side needs something the other doesn't), that's a signal to revisit the IR design.
