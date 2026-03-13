# Handoff: MicroTensor — Current State & Next Steps

## What This Project Is

A verified tensor algebra pipeline: Julia CAS computes tensor identities
(e.g., Riemann antisymmetry, Bianchi identity), emits JSON proof traces, and
a Lean 4 kernel replays them into machine-checked proofs backed by Mathlib.

**Repo:** https://github.com/tobiasosborne/microtensor (GPL-3.0)

**Aspirational target:** TensorGR.jl (`../TensorGR.jl`) — a full-featured
tensor CAS with xperm canonicalization, covariant derivatives, metric
contraction, perturbation theory, and exterior calculus. MicroTensor aims
to verify a growing subset of TensorGR.jl's output.

## Branches

| Branch | Status | Description |
|--------|--------|-------------|
| `master` | old | Original MVP with 7 axioms on TExpr |
| `mathlib-foundations` | **current** | All axioms eliminated via Mathlib semantic eval + Bianchi identity |

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
| `lean/MicroTensor.lean` | IR types (`TExpr`, `Index`, `Position`), `ratCoeff`, `TEnv`, `TExpr.eval`, `List.swap`, `List.cyclicPerm3` |
| `lean/Rules.lean` | 8 theorems about `eval` (formerly axioms), proved via Mathlib |
| `lean/Example.lean` | Hand-written proof: R_{abcd} + R_{abdc} = 0 |
| `lean/Generated.lean` | Machine-generated proof from `trace.json` |
| `lean/Generated2.lean` | Machine-generated proof from `trace2.json` |
| `lean/Generated3.lean` | Machine-generated Bianchi identity proof from `trace3.json` |
| `lean/lakefile.lean` | Lake config, Mathlib dependency |
| `lean/lean-toolchain` | `leanprover/lean4:v4.29.0-rc6` (pinned to Mathlib) |
| `scripts/replay.jl` | Trace → Lean proof generator |
| `julia/MicroTensor.jl` | Julia-side tensor CAS + trace emitter |
| `shared/ir.md` | IR specification shared between Julia and Lean |
| `trace.json`, `trace2.json` | Example traces (antisym slots 2,3 and 0,1) |
| `trace3.json` | Bianchi identity trace (cyclic perm of slots 1,2,3) |

### How Axiom Elimination Works

**Problem:** `TExpr` is a free inductive type — `sum zero e ≠ e` at the term
level, so equational rules can't be theorems about `TExpr` equality.

**Solution:** Define `TExpr.eval : TExpr → M` mapping into any `Module ℚ M`.
The rules become theorems about `eval`:

```
eval env (sum zero e) = eval env e          -- zero_add in M
eval env (smul 0 d e) = eval env zero       -- zero_smul in M
eval env (smul a_n a_d (smul b_n b_d e))    -- smul_smul in M
  = eval env (smul (a_n*b_n) (a_d*b_d) e)
```

**Environment (`TEnv M`)** carries three things:
- `lookup : String → List Index → M` — maps tensor configs to module elements
- `swap_neg` — antisymmetry constraint: swapping in-bounds slots negates the lookup
- `bianchi` — first Bianchi identity: cyclic permutation of 3 slots sums to zero

**Mathlib imports** (via `MicroTensor.lean`):
- `Mathlib.Algebra.Order.Field.Rat` — `Field ℚ` instance
- `Mathlib.Algebra.Module.Basic` — `Module`, `smul_smul`, `add_smul`, etc.
- `Mathlib.Tactic.FieldSimp` — `field_simp` for fraction arithmetic

### Proof Tactic Patterns

The 8 theorems use these patterns:

| Theorem | Key tactics |
|---------|------------|
| `eval_sum_zero_left/right` | `simp [TExpr.eval]` (uses `zero_add`/`add_zero`) |
| `eval_smul_zero` | `simp [TExpr.eval, ratCoeff]` (uses `zero_div`, `zero_smul`) |
| `eval_tensor_as_smul` | `simp [TExpr.eval, ratCoeff]` (uses `one_div_one`, `one_smul`) |
| `eval_smul_smul` | `smul_smul` + case split on zero denoms + `field_simp` |
| `eval_collect_smul` | `add_smul` + `field_simp` (requires `(a_d : ℚ) ≠ 0`, `(b_d : ℚ) ≠ 0`) |
| `eval_antisym_swap` | `simp` + `env.swap_neg` |
| `eval_bianchi` | `simp` + `env.bianchi` |

**Generated proofs** (from replayer) follow two patterns:

Antisymmetry (2-term, single swap):
```lean
simp only [TExpr.eval]                    -- unfold to module ops
rw [h_swap, env.swap_neg "R" [...] ...]   -- apply antisymmetry
exact add_neg_cancel _                     -- x + (-x) = 0
```

Bianchi identity (3-term, cyclic permutation):
```lean
simp only [TExpr.eval]                    -- unfold to module ops
rw [h1, h2]                               -- rewrite indices as cyclicPerm3
exact env.bianchi "R" [...] s1 s2 s3 ...  -- apply Bianchi constraint
```

### Known Design Decisions

1. **`collect_smul` requires nonzero denominators.** The fraction identity
   `a/b + c/d = (ad+bc)/bd` fails when `b=0` or `d=0` in ℚ. The replayer
   discharges these with `(by norm_num)` since denominators are always nonzero
   literal ints in practice.

2. **`smul_smul` handles zero denominators via case split.** The multiplication
   identity `(a/b)*(c/d) = (ac)/(bd)` holds even when `b=0` or `d=0` (both
   sides are 0). Proved by `by_cases` on `(a_d : ℚ) = 0`.

3. **`TExpr.eval` is `noncomputable`.** It uses ℚ division which is
   noncomputable in Lean. This is fine — we only need it for proofs, not
   code extraction.

4. **`TExpr.scalar` maps to `0`.** No axiom mentions `scalar`, so the
   interpretation is arbitrary. Could be refined later if scalar rules are added.

5. **`TEnv.swap_neg` and `TEnv.bianchi` are unconditional.** They say ALL
   tensors satisfy antisymmetry and the Bianchi identity for ALL in-bounds
   slot combinations, matching the original axiom's universality. The
   Julia-side registry check ensures they are only *applied* for declared
   symmetries.

## What's Working

- `lake build` passes all 6 targets (804 jobs, 0 errors)
- `lean_verify` shows only Lean built-in axioms (propext, Classical.choice, Quot.sound)
- Zero `axiom` declarations, zero `sorry`s
- Replayer (`scripts/replay.jl`) generates valid eval-based proofs from traces
- All three traces round-trip correctly:
  - `trace.json` — antisymmetry in slots 2,3: R_{abcd} + R_{abdc} = 0
  - `trace2.json` — antisymmetry in slots 0,1: R_{abcd} + R_{bacd} = 0
  - `trace3.json` — first Bianchi identity: R_{abcd} + R_{adbc} + R_{acdb} = 0
- `.gitignore` covers `.lake/` build artifacts

## What's Next — Tracked in Beads

Work is tracked via `bd` (beads). Run `bd list` to see all issues.

### Workstream 1: Canonicalization via Traced Permutations (`microtensor-g9z`)

Connect TensorGR.jl's xperm canonicalization engine to MicroTensor's verified
kernel. Decompose canonical permutations into elementary transpositions, emit
each as a SwapSlots step, let Lean verify each swap.

**Dependency chain:**
```
g9z.1  swap_id + eval_sym_swap ──┬──► g9z.2  Sym in replayer ──┐
                                 │                              ├──► g9z.4  Multi-swap chains ──┐
                                 │    g9z.3  Perm decomposition ┘                               ├──► g9z.6  Integration test
                                 └──► g9z.5  Compound symmetries ───────────────────────────────┘
```

**Ready tasks (no blockers):** `g9z.1`, `g9z.3`

### Workstream 2: Tensor Products + Index Contraction (`microtensor-4hj`)

Add tensor product and index contraction to the verified pipeline. Unlocks
contracted quantities like g^{ab}R_{abcd} = Ric_{cd} and scalar invariants.

**Dependency chain:**
```
4hj.1  TExpr.prod IR ──┬──► 4hj.2  eval for products ──┬──► 4hj.3  Product rules ──────────┐
                        │                                │                                    ├──► 4hj.7  Julia CAS ──► 4hj.8  Replayer ──┐
                        └──► 4hj.4  TExpr.contract IR ───┴──► 4hj.5  Contract semantics ──┬──┘                                           ├──► 4hj.9  Integration test
                                                                                           └──► 4hj.6  Metric contraction ────────────────┘
```

**Ready task (no blockers):** `4hj.1`

### Recommended starting point

Start with **Workstream 1** — it builds directly on existing infrastructure
(SwapSlots, swap_neg are already working) and requires the least new Lean
design work. The entry point is `g9z.1` (add swap_id to TEnv).

**Workstream 2** is higher impact but needs significant new Lean design
(bilinear maps for products, contraction semantics). Start with `4hj.1`
(add prod to IR) once Workstream 1 has momentum.

### Other items (not yet tracked)

- **Merge `mathlib-foundations` into `master`** — trivial fast-forward merge
- **CI pipeline** — GitHub Actions with `lake exe cache get`
- **Registry-aware TEnv** — make constraints conditional on declared symmetries
- **AlternatingMap** — replace swap_neg with Mathlib's `AlternatingMap.map_swap`

## Build Instructions

```bash
cd lean
lake update                  # fetch Mathlib (first time only)
lake exe cache get           # download prebuilt Mathlib oleans (~8000 files)
lake build                   # build all targets

# Regenerate from traces
cd ..
julia scripts/replay.jl trace.json generated_proof > lean/Generated.lean
julia scripts/replay.jl trace2.json generated_proof_12 Proof12 > lean/Generated2.lean
julia scripts/replay.jl trace3.json bianchi_proof Bianchi > lean/Generated3.lean
```

## Verification

```bash
# No custom axioms
grep -n "^axiom" lean/Rules.lean       # should return nothing

# Via Lean MCP (in Claude Code):
lean_verify file_path="lean/Rules.lean" theorem_name="eval_antisym_swap"
# Should show only: propext, Classical.choice, Quot.sound

# Issue tracker
bd list                                # see all tracked work
bd show microtensor-g9z                # canonicalization epic details
bd show microtensor-4hj                # products+contraction epic details
```
