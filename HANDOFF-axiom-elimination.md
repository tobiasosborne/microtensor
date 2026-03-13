# Handoff: Eliminate All Axioms Using Mathlib

## Goal

Replace all 7 `axiom` declarations in `lean/Rules.lean` with `theorem`s proved
from Mathlib's mathematical foundations. When done, `lean/Rules.lean` should have
zero axioms and zero sorries, and `lake build` should still pass for all targets.

## Current State

**Branch:** Create `mathlib-foundations` from `master`.

**The 7 axioms** (in `lean/Rules.lean`):

```lean
axiom antisym_swap (name : String) (idxs : List Index) (s1 s2 : Nat)
    (h : s1 < idxs.length) (h2 : s2 < idxs.length) :
    tensor name (idxs.swap s1 s2) = smul (-1) 1 (tensor name idxs)

axiom collect_smul (a_n a_d b_n b_d : Int) (e : TExpr) :
    sum (smul a_n a_d e) (smul b_n b_d e) =
    smul (a_n * b_d + b_n * a_d) (a_d * b_d) e

axiom tensor_as_smul (name : String) (idxs : List Index) :
    tensor name idxs = smul 1 1 (tensor name idxs)

axiom smul_zero (d : Int) (e : TExpr) :
    smul 0 d e = zero

axiom sum_zero_left (e : TExpr) : sum zero e = e
axiom sum_zero_right (e : TExpr) : sum e zero = e

axiom smul_smul (a_n a_d b_n b_d : Int) (e : TExpr) :
    smul a_n a_d (smul b_n b_d e) = smul (a_n * b_n) (a_d * b_d) e
```

**Why these are axioms today:** `TExpr` is a free inductive type. `sum zero e`
is literally a different constructor from `e`, so `sum zero e = e` is *false*
at the term level. The axioms define an equational theory on syntax trees.

## Strategy: Semantic Interpretation

Replace the syntactic approach with a semantic one. Define an interpretation
function that maps `TExpr` values into an actual mathematical structure where
the axioms are provable theorems.

### Step 1: Add Mathlib dependency

In `lean/lakefile.lean`, add Mathlib. This will be slow to build the first time.

```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
```

Update `lean/lean-toolchain` to match Mathlib's required version. Check
`mathlib4/lean-toolchain` on GitHub for the current pin.

### Step 2: Choose the interpretation target

The simplest model that captures all axioms: interpret `TExpr` as an element
of a `Module ℚ M` where `M` is an additive commutative group with ℚ-scalar action.

Concretely, the interpretation maps:
- `TExpr.zero` → `0 : M`
- `TExpr.sum a b` → `eval a + eval b`
- `TExpr.smul n d e` → `(n / d : ℚ) • eval e`
- `TExpr.scalar n d` → `(n / d : ℚ) • 1` (or just ignore for MVP)
- `TExpr.tensor name idxs` → looked up from an environment/context

The hardest part is `TExpr.tensor`. Each unique `(name, idxs)` pair maps to
a value in `M`. The `antisym_swap` axiom constrains how related lookups relate.

### Step 3: Define the interpretation

```lean
-- An environment maps tensor configurations to values in M
structure TEnv (M : Type*) where
  lookup : String → List Index → M

-- The interpretation
def eval [AddCommGroup M] [Module ℚ M] (env : TEnv M) : TExpr → M
  | .zero => 0
  | .scalar n d => (n / d : ℚ) • (1 : M)  -- needs One M or skip
  | .tensor name idxs => env.lookup name idxs
  | .smul n d e => (n / d : ℚ) • eval env e
  | .sum a b => eval env a + eval env b
```

### Step 4: State and prove each axiom as a theorem about `eval`

**Easy axioms (just module theory):**

| Axiom | Proof sketch |
|-------|-------------|
| `sum_zero_left` | `eval env (sum zero e) = 0 + eval env e = eval env e` via `zero_add` |
| `sum_zero_right` | via `add_zero` |
| `smul_zero` | `eval env (smul 0 d e) = (0/d : ℚ) • eval env e = 0 • eval env e = 0` via `zero_div`, `zero_smul` |
| `tensor_as_smul` | `eval env (tensor n i) = env.lookup n i = 1 • env.lookup n i = (1/1) • eval env (tensor n i)` via `one_smul` |
| `smul_smul` | `(a_n/a_d) • ((b_n/b_d) • x) = (a_n*b_n)/(a_d*b_d) • x` via `smul_smul` + rational arithmetic |
| `collect_smul` | `(a_n/a_d) • x + (b_n/b_d) • x = ((a_n*b_d + b_n*a_d)/(a_d*b_d)) • x` via `add_smul` + rational arithmetic |

**Hard axiom (needs alternating maps):**

| Axiom | Proof sketch |
|-------|-------------|
| `antisym_swap` | Requires the environment to satisfy an antisymmetry constraint. See below. |

### Step 5: Handle `antisym_swap`

This is the crux. The axiom says: for an antisymmetric tensor, swapping two
slots negates the value. This is exactly `AlternatingMap.map_swap` from Mathlib:

```
AlternatingMap.map_swap : g (v ∘ Equiv.swap i j) = -g v
```

**Option A: Constrained environment.** Add a field to `TEnv` that says
"for tensors declared antisymmetric in the registry, swapping those slots
negates the lookup." Then `antisym_swap` follows from this constraint.

```lean
structure TEnv (M : Type*) where
  lookup : String → List Index → M
  antisym_constraint : ∀ name s1 s2 idxs,
    registry.hasAntisym name s1 s2 →
    lookup name (idxs.swap s1 s2) = -(lookup name idxs)
```

Then `antisym_swap` becomes:
```lean
theorem antisym_swap ... :
    eval env (tensor name (idxs.swap s1 s2)) = eval env (smul (-1) 1 (tensor name idxs)) := by
  simp [eval]
  rw [env.antisym_constraint ...]
  ring  -- or simp with neg_smul, one_smul etc.
```

**Option B: Use AlternatingMap directly.** Model each tensor as an
`AlternatingMap` applied to its indices. Then `antisym_swap` follows from
`AlternatingMap.map_swap`. This is more mathematically principled but requires
more Mathlib machinery (the index type needs to be `Fin n` or similar).

**Recommendation: Start with Option A.** It's simpler and sufficient. The
constraint is an assumption on the environment, not a deep mathematical fact.
Option B can be explored later for more mathematical purity.

### Step 6: Change the proof structure

Currently the proofs say `expr = result` where `=` is Lean equality on `TExpr`.
After the change, proofs say `eval env expr = eval env result` where `=` is
equality in `M`.

The theorem in `Example.lean` becomes:
```lean
theorem riemann_antisym_34 (env : TEnv M)
    (h_antisym : env.antisym_for "R" 2 3) :
    eval env (sum (tensor "R" [a, b, c, d]) (tensor "R" [a, b, d, c])) = 0 := by
  ...
```

The replayer must be updated to emit this new form.

### Step 7: Update downstream

- `lean/Example.lean` — rewrite proofs using `eval`
- `lean/Generated.lean`, `lean/Generated2.lean` — regenerate via updated replayer
- `scripts/replay.jl` — emit the new proof structure
- `lean/lakefile.lean` — add Mathlib dependency

## Mathlib Lemmas Needed

Found via leansearch/loogle — all confirmed to exist:

| Lemma | Module | What it proves |
|-------|--------|---------------|
| `zero_add` | core | `0 + a = a` |
| `add_zero` | core | `a + 0 = a` |
| `zero_smul` | `Mathlib.Algebra.GroupWithZero.Action.Defs` | `0 • m = 0` |
| `one_smul` | core / `Mathlib.Algebra.Module.Defs` | `1 • m = m` |
| `add_smul` | `Mathlib.Algebra.Module.Defs` | `(r + s) • x = r • x + s • x` |
| `smul_smul` | `Mathlib.Algebra.GroupWithZero.Action.Defs` | `a • (b • x) = (a * b) • x` |
| `AlternatingMap.map_swap` | `Mathlib.LinearAlgebra.Alternating.Basic` | `g (v ∘ swap i j) = -g v` |
| `neg_smul` | `Mathlib.Algebra.Module.Defs` | `(-r) • x = -(r • x)` |

## Key Challenges

1. **Rational arithmetic in smul.** The current IR stores `(num, den)` pairs.
   The interpretation uses `(n : Int) / (d : Int) : ℚ`. Proving
   `(a_n * b_d + b_n * a_d) / (a_d * b_d)` equals the sum of rationals
   requires `field_simp` or `ring` on ℚ. Should work but may be fiddly.

2. **Lean toolchain alignment.** Mathlib pins a specific Lean version. The
   current project uses v4.27.0. Check if Mathlib supports this version;
   if not, update `lean-toolchain` to match Mathlib's pin.

3. **Build time.** First `lake build` with Mathlib will download and build
   a lot. Subsequent builds are incremental. Consider using `lake exe cache get`
   to download pre-built oleans.

4. **The `tensor_as_smul` axiom.** This says `tensor n i = smul 1 1 (tensor n i)`.
   Under interpretation: `env.lookup n i = (1/1) • env.lookup n i`. This is
   just `one_smul` (since 1/1 = 1 in ℚ). But we need to show `(1 : Int) / (1 : Int) = (1 : ℚ)`
   which should be `Int.cast_one` + `div_one` or similar.

5. **Keeping TExpr.** The `TExpr` inductive type stays. The axioms are REPLACED
   with theorems about `eval`. The Julia side doesn't change at all — it still
   emits the same JSON traces. Only the Lean proof structure changes.

## Files to Modify

- `lean/lakefile.lean` — add Mathlib dependency, update toolchain
- `lean/lean-toolchain` — match Mathlib's pin
- `lean/MicroTensor.lean` — add `TEnv`, `eval` function
- `lean/Rules.lean` — replace all `axiom` with `theorem` + proofs
- `lean/Example.lean` — update proof to use `eval`
- `scripts/replay.jl` — update proof generation
- `lean/Generated.lean`, `lean/Generated2.lean` — regenerate

## Verification

Run `lake build` (all targets). Then:

```bash
# Check no axioms remain (except Lean's built-in ones)
grep -n "^axiom" lean/Rules.lean  # should return nothing
```

Use the Lean MCP tool `lean_verify` on key theorems to confirm they don't
depend on any custom axioms.

## Build Order

1. Add Mathlib, get `lake build MicroTensor` working
2. Define `TEnv` and `eval` in MicroTensor.lean
3. Replace the 6 easy axioms in Rules.lean with theorems (everything except `antisym_swap`)
4. Replace `antisym_swap` with a theorem using the constrained environment
5. Update Example.lean proof
6. Update replayer and regenerate Generated files
7. Full `lake build` — all targets, no axioms, no sorries
