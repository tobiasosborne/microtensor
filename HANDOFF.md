# Handoff: MicroTensor — Current State & Next Steps

## What This Project Is

A verified tensor algebra pipeline: Julia CAS computes tensor identities
(e.g., Riemann antisymmetry, Bianchi identity, index canonicalization),
emits JSON proof traces, and a Lean 4 kernel replays them into
machine-checked proofs backed by Mathlib.

**Repo:** https://github.com/tobiasosborne/microtensor (GPL-3.0)

**Aspirational target:** TensorGR.jl (`../TensorGR.jl`) — a full-featured
tensor CAS with xperm canonicalization, covariant derivatives, metric
contraction, perturbation theory, and exterior calculus. MicroTensor aims
to verify a growing subset of TensorGR.jl's output.

## Branches

| Branch | Status | Description |
|--------|--------|-------------|
| `master` | old | Original MVP with 7 axioms on TExpr |
| `mathlib-foundations` | **current** | Axiom-free kernel + canonicalization via traced permutations |

**TODO:** Merge `mathlib-foundations` into `master`.

## Architecture (mathlib-foundations)

```
Julia CAS                    JSON trace                Lean 4 + Mathlib
─────────────                ──────────                ────────────────
MicroTensor.jl  ──emit──►  trace.json  ──replay.jl──►  Generated.lean
(compute identity)          (rewrite steps)            (verified proof)
```

The flow is Julia-driven: Julia computes the identity, emits a trace,
the replayer generates a `.lean` proof, and `lake build` verifies it.

### Key Files

| File | Purpose |
|------|---------|
| `lean/MicroTensor.lean` | IR types (`TExpr`, `Index`, `Position`), `ratCoeff`, `TEnv` (registry-aware, with `mul` for products), `TExpr.eval`, `List.swap`, `List.cyclicPerm3` |
| `lean/Rules.lean` | 9 theorems about `eval` (including `eval_sym_swap`), proved via Mathlib |
| `lean/Example.lean` | Hand-written proof: R_{abcd} + R_{abdc} = 0 |
| `lean/Generated.lean` | Machine-generated: antisym R slots 2,3 |
| `lean/Generated2.lean` | Machine-generated: antisym R slots 0,1 |
| `lean/Generated3.lean` | Machine-generated: Bianchi identity |
| `lean/Generated4.lean` | Machine-generated: metric tensor symmetry g_{ba} = g_{ab} |
| `lean/Generated5.lean` | Machine-generated: canonicalize R_{badc} → R_{abcd} (multi-swap) |
| `lean/lakefile.lean` | Lake config, Mathlib dependency |
| `lean/lean-toolchain` | `leanprover/lean4:v4.29.0-rc6` (pinned to Mathlib) |
| `scripts/replay.jl` | Trace → Lean proof generator (handles antisym, sym, bianchi, multi-swap chains) |
| `julia/MicroTensor.jl` | Julia-side tensor CAS + trace emitter + `canonicalize_traced` + `perm_to_transpositions` |
| `shared/ir.md` | IR specification shared between Julia and Lean |
| `trace.json` – `trace5.json` | Example traces (antisym, bianchi, sym, canonicalization) |
| `trace_canon.json` | CAS-generated canonicalization trace (integration test artifact) |

### Registry-Aware TEnv

`TEnv` carries symmetry predicates that declare which (tensor, slot)
combinations have which symmetries. Constraints are conditional:

```lean
structure TEnv (M : Type*) [AddCommGroup M] where
  lookup    : String → List Index → M
  mul       : M → M → M              -- binary op for tensor products
  isAntisym : String → Nat → Nat → Prop
  isSym     : String → Nat → Nat → Prop
  isBianchi : String → Nat → Nat → Nat → Prop
  swap_neg  : ∀ ... isAntisym name s1 s2 → ... lookup (swap) = -lookup
  swap_id   : ∀ ... isSym name s1 s2 → ... lookup (swap) = lookup
  bianchi   : ∀ ... isBianchi name s1 s2 s3 → ... cyclic sum = 0
```

Generated proofs take symmetry declarations as theorem hypotheses:
```lean
theorem canon_proof
    (h_antisym_R_0_1 : env.isAntisym "R" 0 1)
    (h_antisym_R_2_3 : env.isAntisym "R" 2 3) :
    (tensor "R" [b,a,d,c]).eval env = (tensor "R" [a,b,c,d]).eval env := by ...
```

### Proof Tactic Patterns

The 9 theorems use these patterns:

| Theorem | Key tactics |
|---------|------------|
| `eval_sum_zero_left/right` | `simp [TExpr.eval]` |
| `eval_smul_zero` | `simp [TExpr.eval, ratCoeff]` |
| `eval_tensor_as_smul` | `simp [TExpr.eval, ratCoeff]` |
| `eval_smul_smul` | `smul_smul` + case split on zero denoms + `field_simp` |
| `eval_collect_smul` | `add_smul` + `field_simp` (requires nonzero denoms) |
| `eval_antisym_swap` | `simp` + `env.swap_neg` (takes `isAntisym` hypothesis) |
| `eval_sym_swap` | `simp` + `env.swap_id` (takes `isSym` hypothesis) |
| `eval_bianchi` | `simp` + `env.bianchi` (takes `isBianchi` hypothesis) |

**Generated proofs** (from replayer) follow three patterns:

Antisymmetry (sum cancellation):
```lean
simp only [TExpr.eval]
rw [hs1, env.swap_neg "R" [...] s1 s2 h_antisym (by decide) (by decide)]
exact add_neg_cancel _
```

Canonicalization (multi-swap chain):
```lean
simp only [TExpr.eval]
rw [hs1, env.swap_neg "R" [...] 0 1 h_antisym_01 (by decide) (by decide)]
rw [hs2, env.swap_neg "R" [...] 2 3 h_antisym_23 (by decide) (by decide)]
simp  -- resolves nested negations (neg_neg)
```

Bianchi identity (cyclic permutation):
```lean
simp only [TExpr.eval]
rw [h1, h2]
exact env.bianchi "R" [...] 1 2 3 h_bianchi (by decide) (by decide) (by decide)
```

### Known Design Decisions

1. **`collect_smul` requires nonzero denominators.** Discharged with `(by norm_num)`.
2. **`smul_smul` handles zero denominators via case split.**
3. **`TExpr.eval` is `noncomputable`.** Uses ℚ division; fine for proofs.
4. **`TExpr.scalar` maps to `0`.** Arbitrary; refine if scalar rules are added.
5. **`perm_to_transpositions` uses bubble-sort decomposition.** O(n²) worst-case.
   Tracked as `g9z.7` to replace with cycle decomposition for minimal transposition count.

## What's Working

- `lake build` passes all 8 targets (808 jobs, 0 errors)
- `lean_verify` shows only Lean built-in axioms (propext, Classical.choice, Quot.sound)
- Zero `axiom` declarations, zero `sorry`s
- Replayer generates valid eval-based proofs for antisym, sym, bianchi, and multi-swap chains
- All traces round-trip correctly:
  - `trace.json` — antisymmetry in slots 2,3: R_{abcd} + R_{abdc} = 0
  - `trace2.json` — antisymmetry in slots 0,1: R_{abcd} + R_{bacd} = 0
  - `trace3.json` — first Bianchi identity: R_{abcd} + R_{adbc} + R_{acdb} = 0
  - `trace4.json` — metric symmetry: g_{ba} = g_{ab}
  - `trace_canon.json` — canonicalization: R_{badc} = R_{abcd} (CAS-generated, 2 swaps)
- Julia CAS: `canonicalize_traced`, `perm_to_transpositions`, `riemann_symmetries`
- `.gitignore` covers `.lake/` build artifacts

## What's Next — Tracked in Beads

Work is tracked via `bd` (beads). Run `bd list` to see all issues.

### Workstream 1: Canonicalization — COMPLETE (`microtensor-g9z`)

All 6 tasks closed. Full pipeline working: Julia CAS decomposes permutations
into transpositions, emits traced swap steps, replayer generates Lean proofs
with registry-aware symmetry hypotheses, `lake build` verifies.

One follow-up: `g9z.7` (P3) — replace bubble-sort decomposition with
cycle-decomposition for minimal transposition count.

### Workstream 2: Tensor Products + Index Contraction (`microtensor-4hj`)

Add tensor product and index contraction to the verified pipeline. Unlocks
contracted quantities like g^{ab}R_{abcd} = Ric_{cd} and scalar invariants.

**Dependency chain:**
```
4hj.1  TExpr.prod IR ──┬──► 4hj.2  eval for products ──┬──► 4hj.3  Product rules ──────────┐
  ✓ DONE                │     ✓ DONE                     │     ✓ DONE                         ├──► 4hj.7  Julia CAS ──► 4hj.8  Replayer ──┐
                        └──► 4hj.4  TExpr.contract IR ───┴──► 4hj.5  Contract semantics ──┬──┘     ✓ DONE                                ├──► 4hj.9  Integration test
                              ✓ DONE                           ✓ DONE                      └──► 4hj.6  Metric contraction ────────────────┘
```

**Completed:**
- `4hj.1` — TExpr.prod in IR (Lean + Julia + replayer + spec)
- `4hj.2` — eval via `env.mul : M → M → M` with bilinearity constraints in TEnv
- `4hj.3` — 6 product rule theorems (distribute over sum, factor out smul, zero)
- `4hj.4` — TExpr.contract IR (Lean + Julia + replayer + spec)
- `4hj.5` — Contract eval via `env.contractAt : Nat → Nat → M → M` (linear);
  3 contraction rule theorems (distribute over sum, factor out smul, zero)
- `4hj.7` — Julia CAS: product proof steps (ProdSmulLeft/Right, ProdSumLeft/Right,
  ProdZeroLeft/Right), rule application functions, index analysis (all_indices,
  dummy_pairs, free_indices)

**Ready tasks (no blockers):** `4hj.6` (metric contraction), `4hj.8` (replayer for products)

### Recommended starting point

4hj.1–4hj.5 and 4hj.7 are done. Two tasks remain before the integration test:

- **`4hj.6`** — metric contraction rules. Add `isMetric` predicate to TEnv and
  a constraint relating `contractAt` + `mul` + `lookup` for metric tensors.
  E.g., contracting g^{ab} ⊗ R_{bcde} over b gives R^a_{cde}. This is the
  last Lean theorem needed for the contraction pipeline.
- **`4hj.8`** — replayer support for product/contraction proof steps. Add
  handling for ProdSmulLeft/Right, ProdSumLeft/Right, ProdZeroLeft/Right
  in the Lean proof generator.

### Other items (not yet tracked)

- **Merge `mathlib-foundations` into `master`** — trivial fast-forward merge
- **CI pipeline** — GitHub Actions with `lake exe cache get`
- **AlternatingMap** — replace swap_neg with Mathlib's `AlternatingMap.map_swap`
- **Pair symmetry** — R_{abcd} = R_{cdab} requires swapping two pairs simultaneously

## Build Instructions

```bash
cd lean
lake update                  # fetch Mathlib (first time only)
lake exe cache get           # download prebuilt Mathlib oleans (~8000 files)
lake build                   # build all targets (808 jobs)

# Regenerate from traces
cd ..
julia scripts/replay.jl trace.json generated_proof > lean/Generated.lean
julia scripts/replay.jl trace2.json generated_proof_12 Proof12 > lean/Generated2.lean
julia scripts/replay.jl trace3.json bianchi_proof Bianchi > lean/Generated3.lean
julia scripts/replay.jl trace4.json metric_sym_proof MetricSym > lean/Generated4.lean
julia scripts/replay.jl trace_canon.json canon_integration Canon > lean/Generated5.lean
```

## Verification

```bash
# No custom axioms
grep -n "^axiom" lean/Rules.lean       # should return nothing

# Via Lean MCP (in Claude Code):
lean_verify file_path="lean/Rules.lean" theorem_name="eval_sym_swap"
# Should show only: propext, Classical.choice, Quot.sound

# Issue tracker
bd list                                # see all tracked work
bd show microtensor-4hj                # products+contraction epic details
```
