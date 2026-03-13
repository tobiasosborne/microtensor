# Handoff: MicroTensor — Current State & Next Steps

## What This Project Is

A verified tensor algebra pipeline: Julia CAS computes tensor identities
(e.g., Riemann antisymmetry, Bianchi identity), emits JSON proof traces, and
a Lean 4 kernel replays them into machine-checked proofs backed by Mathlib.

**Repo:** https://github.com/tobiasosborne/microtensor (GPL-3.0)

## Branches

| Branch | Status | Description |
|--------|--------|-------------|
| `master` | old | Original MVP with 7 axioms on TExpr |
| `mathlib-foundations` | **current** | All axioms eliminated via Mathlib semantic eval |

## Architecture (mathlib-foundations)

```
Julia CAS                    JSON trace                Lean 4 + Mathlib
─────────────                ──────────                ────────────────
MicroTensor.jl  ──emit──►  trace.json  ──replay.jl──►  Generated.lean
(compute identity)          (rewrite steps)            (verified proof)
```

### Key Files

| File | Purpose |
|------|---------|
| `lean/MicroTensor.lean` | IR types (`TExpr`, `Index`, `Position`), `ratCoeff`, `TEnv`, `TExpr.eval` |
| `lean/Rules.lean` | 7 theorems about `eval` (formerly axioms), proved via Mathlib |
| `lean/Example.lean` | Hand-written proof: R_{abcd} + R_{abdc} = 0 |
| `lean/Generated.lean` | Machine-generated proof from `trace.json` |
| `lean/Generated2.lean` | Machine-generated proof from `trace2.json` |
| `lean/lakefile.lean` | Lake config, Mathlib dependency |
| `lean/lean-toolchain` | `leanprover/lean4:v4.29.0-rc6` (pinned to Mathlib) |
| `scripts/replay.jl` | Trace → Lean proof generator |
| `julia/MicroTensor.jl` | Julia-side tensor CAS + trace emitter |
| `shared/ir.md` | IR specification shared between Julia and Lean |
| `trace.json`, `trace2.json` | Example traces (antisym slots 2,3 and 0,1) |

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

**Environment (`TEnv M`)** carries two things:
- `lookup : String → List Index → M` — maps tensor configs to module elements
- `swap_neg` — antisymmetry constraint: swapping in-bounds slots negates the lookup

**Mathlib imports** (via `MicroTensor.lean`):
- `Mathlib.Algebra.Order.Field.Rat` — `Field ℚ` instance
- `Mathlib.Algebra.Module.Basic` — `Module`, `smul_smul`, `add_smul`, etc.
- `Mathlib.Tactic.FieldSimp` — `field_simp` for fraction arithmetic

### Proof Tactic Patterns

The 7 theorems use these patterns:

| Theorem | Key tactics |
|---------|------------|
| `eval_sum_zero_left/right` | `simp [TExpr.eval]` (uses `zero_add`/`add_zero`) |
| `eval_smul_zero` | `simp [TExpr.eval, ratCoeff]` (uses `zero_div`, `zero_smul`) |
| `eval_tensor_as_smul` | `simp [TExpr.eval, ratCoeff]` (uses `one_div_one`, `one_smul`) |
| `eval_smul_smul` | `smul_smul` + case split on zero denoms + `field_simp` |
| `eval_collect_smul` | `add_smul` + `field_simp` (requires `(a_d : ℚ) ≠ 0`, `(b_d : ℚ) ≠ 0`) |
| `eval_antisym_swap` | `simp` + `env.swap_neg` |

**Generated proofs** (from replayer) follow a 3-line pattern:
```lean
simp only [TExpr.eval]                    -- unfold to module ops
rw [h_swap, env.swap_neg "R" [...] ...]   -- apply antisymmetry
exact add_neg_cancel _                     -- x + (-x) = 0
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

5. **`TEnv.swap_neg` is unconditional.** It says ALL tensors are antisymmetric
   in ALL in-bounds slot pairs, matching the original axiom's universality. The
   Julia-side registry check ensures it's only *applied* for declared symmetries.

## What's Working

- `lake build` passes all 5 targets (802 jobs, 0 errors)
- `lean_verify` shows only Lean built-in axioms (propext, Classical.choice, Quot.sound)
- Zero `axiom` declarations, zero `sorry`s
- Replayer (`scripts/replay.jl`) generates valid eval-based proofs from traces
- Both example traces (`trace.json`, `trace2.json`) round-trip correctly

## What's Next

### Immediate (high value, low effort)

1. **Merge `mathlib-foundations` into `master`.** The axiom elimination is
   complete and fully tested. No reason to keep it on a branch.

2. **Add `.gitignore` for `.lake/`.** The Mathlib build artifacts are large.
   Ensure `.lake/` is not committed.

3. **Bianchi identity trace.** The current traces only test two-term antisymmetry
   (`R_abcd + R_abdc = 0`). Generate a Bianchi identity trace
   (`R_abcd + R_acdb + R_adbc = 0`) from the Julia side and verify the replayer
   handles it. This requires multi-swap proofs — the replayer's closing tactic
   (`add_neg_cancel`) won't suffice; it'll need `simp` with module lemmas or
   `linarith`.

4. **Symmetry support.** The `Symmetry.sym` constructor exists in the IR but
   has no corresponding rule. Add `eval_sym_swap` for symmetric tensors
   (swap doesn't negate). This needs a richer `TEnv` with both `swap_neg`
   (for antisym) and `swap_id` (for sym) constraints.

### Medium-term

5. **Contraction / trace rule.** Tensor contraction (summing over a repeated
   index) is the next algebraic operation to support. Requires extending TExpr
   with a `contract` constructor and proving the contraction rule semantically.

6. **Product / outer product.** The IR currently has `sum` but no `product`.
   Adding tensor products requires `TExpr.prod` and corresponding eval into
   a tensor algebra or graded module.

7. **Refine `TEnv.swap_neg` to be registry-aware.** Currently swap_neg is
   unconditional (all tensors antisymmetric). A more refined version would
   check the registry:
   ```lean
   structure TEnv (M : Type*) [AddCommGroup M] where
     lookup : String → List Index → M
     registry : Registry
     antisym_constraint : ∀ name idxs s1 s2,
       registry.hasAntisym name s1 s2 = true →
       s1 < idxs.length → s2 < idxs.length →
       lookup name (idxs.swap s1 s2) = -(lookup name idxs)
   ```

8. **Option B: AlternatingMap.** Replace the environment constraint with
   Mathlib's `AlternatingMap` to get `swap_neg` from `AlternatingMap.map_swap`
   rather than postulating it. More mathematically principled but requires
   modeling indices as `Fin n`.

### Longer-term

9. **CI pipeline.** GitHub Actions running `lake build` on push. Use
   `lake exe cache get` to avoid rebuilding Mathlib from source.

10. **Multiple tensor species.** Support tensors with different symmetry
    properties (some symmetric, some antisymmetric, some with no symmetry)
    in the same proof.

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
```

## Verification

```bash
# No custom axioms
grep -n "^axiom" lean/Rules.lean       # should return nothing

# Via Lean MCP (in Claude Code):
lean_verify file_path="lean/Rules.lean" theorem_name="eval_antisym_swap"
# Should show only: propext, Classical.choice, Quot.sound
```
