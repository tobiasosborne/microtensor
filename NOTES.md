# Design Notes

Running notes on decisions made, questions open, and things learned.

## Decision: axioms, not theorems (for now)

The Lean `Rules.lean` uses `axiom` for the tensor algebra rules. This is deliberate.

**Why axioms:** We're defining an equational theory (free tensor algebra with symmetries). The axioms are the *definition* of what equality means for tensor expressions. They're not derived from a deeper foundation — they *are* the foundation.

**Why this is safe:** The axioms are obviously consistent — multilinear maps on a finite-dimensional vector space provide a model. Any contradiction would mean linear algebra is inconsistent.

**When to replace with theorems:** Once we have a *semantic model* in Lean (tensor products of modules, multilinear maps), we can derive the rewrite rules as theorems from that model. This is a Lean-side project that's independent of the Julia pipeline. The axioms are a stable interface: downstream proofs don't care whether `antisym_swap` is an axiom or a theorem.

**Risk:** Lean's axiom system is consistent only if the axioms are. If we accidentally introduce a contradictory axiom, Lean's kernel will happily derive `False`. Mitigation: keep the axiom set minimal and obviously sound. The MVP has 7 axioms, all of which are standard properties of multilinear algebra.

## Decision: rationals as (Int, Int), not as a Lean type

The IR represents rationals as numerator/denominator pairs rather than using Lean's `Rat` type or Mathlib's `ℚ`. Reason: the JSON interchange format needs to be language-agnostic. Both Julia and Lean can reconstruct their native rational type from (num, den).

This means the `collect_smul` axiom does rational arithmetic at the level of integer pairs: `(a_n/a_d) + (b_n/b_d) = (a_n*b_d + b_n*a_d) / (a_d*b_d)`. This is correct but doesn't reduce (6/4 ≠ 3/2 in this representation). If this causes problems, add a `reduce` axiom: `smul (n*g) (d*g) e = smul n d e` for nonzero g.

## Open: binary vs n-ary sums

The current Julia code uses binary `TeSum` but the smart constructor `te_sum` could flatten. The Lean side uses binary `TExpr.sum`. For the MVP this is fine — we only have two-term sums.

**Explore in branch `julia-binary`:** change the entire Julia IR to binary. Measure impact on TensorGR.jl benchmarks (do sums of 100+ terms slow down?).

**Explore in branch `julia-nary`:** keep n-ary in Julia, write a `to_binary` function for Lean export. This is probably the right long-term answer but adds a translation step.

## Open: path encoding

Currently proof steps specify tree position as `Vector{Int}` (0 = left child, 1 = right child). This works for binary trees but is fragile if the tree structure changes between steps.

Alternative: use *expression hashing*. Each step says "apply rule R to the subtree with hash H." The verifier finds the subtree by hash. This is more robust but requires a canonical hashing scheme.

Another alternative: *flat addressing*. Number the nodes in pre-order. Step says "apply rule R to node 7." Simpler than paths but depends on the tree shape.

Experiment with paths first (simplest), switch if it breaks.

## Open: how much registry to export

Current: export all symmetry declarations. But for a proof of R_{abcd} + R_{abdc} = 0, we only *use* the antisymmetry of slots 3,4. The proof doesn't reference the slot 1,2 antisymmetry.

**Minimal export:** only the symmetries that appear in proof steps. Smaller JSON, tighter proofs, but the registry isn't a complete description of the theory.

**Full export:** all symmetries. Larger but the Lean file is self-contained.

For MVP: full export (easier). Revisit when traces get large.

## Open: `native_decide` vs explicit proof

In `Example.lean`, we use `native_decide` to show that `[a,b,d,c] = [a,b,c,d].swap 2 3`. This is a concrete list equality on ground terms — decidable, but requires `DecidableEq` on `Index`.

Alternative: have the Julia side emit the proof that the indices match (it knows exactly which slots were swapped). This avoids `native_decide` and might be faster for large index lists.

For MVP: `native_decide` (less code to generate). Profile if it becomes slow.

## Exploration branches planned

### `lean-tactic` (first priority)
The approach in `Example.lean`: generate `by rw [...]` tactic proofs. Test:
- Does it scale to 10 steps? 100?
- How fast is `lake build` for a file with 50 proved theorems?
- Does `native_decide` cause trouble?

### `lean-term`
Generate proof terms directly: `Eq.trans (antisym_swap ...) (Eq.trans (collect_smul ...) (smul_zero ...))`. Should be faster to check but harder to debug when something goes wrong.

### `lean-decide`
The nuclear option: define a `canon` function in Lean (a simplified version of what Julia does), prove it correct, then every identity is `by native_decide` with no trace at all. The proof is: "both sides have the same canonical form, and canon is correct, therefore they're equal."

Pros: no trace needed, minimal Julia→Lean data transfer, proofs are one line.
Cons: requires verifying the canonicaliser in Lean, which is a serious project (essentially porting a miniature xperm.c to Lean and proving it correct).

Worth exploring to see how far we get with a simple canonicaliser (just sort by index name, no xperm.c group theory).

### `julia-binary`
Binary IR throughout Julia. See notes above.

### `julia-nary`
N-ary IR in Julia, binary for Lean export.

## Learned: Lean 4 v4.27.0 API changes (2026-03-13)

The draft code targeted Lean 4 v4.15.0. We're on v4.27.0 (latest via elan). Key breakages:

- **`List.get?` is gone.** Replaced by `l[i]?` (bracket syntax with `?`).
- **`List.enum` is gone.** Replaced by `List.mapIdx` which takes `(idx : Nat) → α → β`.
- **`autoImplicit := false`** means every type variable needs explicit binding. The draft `List.swap (l : List α)` fails — need `{α : Type}`.

Fix was straightforward: rewrote `List.swap` from 6 lines to 5 using `l[i]?` and `mapIdx`.

## Learned: smart constructors swallow trace steps (2026-03-13)

The Julia smart constructor `te_smul(0, e)` returns `TeZero()` immediately. This meant `apply_collect` (which calls `te_smul`) was producing zero directly, so the `ZeroElim` step was never recorded in the trace. The Lean proof needs the explicit `smul_zero` rewrite.

**Fix:** Use raw constructors (`TeSMul(coeff, expr)`) in the traced code path. Smart constructors are fine for user-facing API but wrong for trace emission where every intermediate state matters.

Same issue affected `apply_swap`: `te_smul(-1, tensor)` would trigger the smart constructor's `c == -1` path. Switched to `TeSMul(-1//1, tensor)`.

**Lesson for Theoria:** Traced execution and normal execution need different constructors. Consider a `@traced` macro or a mode flag.

## Learned: 0-indexed vs 1-indexed slot convention (2026-03-13)

The PRD initially waffled between Julia's 1-indexed and Lean's 0-indexed convention for slots. We settled on: **0-indexed in JSON and Lean, 1-indexed in Julia internally, convert at the serialization boundary** (`slot - 1` in `step_to_dict` and `sym_to_dict`).

This works cleanly. The conversion is in exactly two functions. The replayer reads 0-indexed values and passes them straight to Lean's `List.swap`.

## Learned: the axiom set is sufficient and stable (2026-03-13)

The 7 axioms in Rules.lean proved R_{abcd} + R_{abdc} = 0 (slots 2,3) AND R_{abcd} + R_{bacd} = 0 (slots 0,1) with zero changes. The proof structure is identical: `antisym_swap` → `tensor_as_smul` → `collect_smul` → `smul_zero`. The only thing that changes is the slot numbers and index lists.

This strongly suggests the axiom set is right for all pairwise slot-symmetry identities. The `smul_smul` axiom (for nested scalar multiples) wasn't needed for these two cases but will be needed when swapping inside an already-scaled tensor.

## Status: MVP complete (2026-03-13)

All PRD success criteria met:
1. ✅ `lake build` passes (hand-written + generated proofs)
2. ✅ Julia emits valid 3-step JSON traces
3. ✅ Replayer (`scripts/replay.jl`) converts traces to typechecking `.lean` files
4. ✅ `scripts/prove.sh` runs end-to-end with exit 0
5. ✅ Second identity works with zero axiom changes
6. ✅ NOTES.md has findings (this section)

## Next concrete steps

1. **Explore `lean-term` branch** — generate proof terms instead of tactic proofs. Should be faster to check.

2. **Explore `lean-decide` branch** — build a canonicalizer in Lean, prove it correct, then every identity is `by native_decide`. Eliminates the trace entirely.

3. **Fix `schema.json`** — still says `"minimum": 1` for slots but we use 0-indexed now.

4. **Try a 3-term identity** — e.g., the first Bianchi identity R_{a[bcd]} = 0. This requires the simplifier to handle more than two-term sums and will stress-test the trace format.
