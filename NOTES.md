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

## Learned: Lean `rw` rewrites ALL occurrences (2026-03-13)

`rw [rule]` in Lean 4 replaces every occurrence of the matched pattern simultaneously, not just the first. This broke the proof when `tensor_as_smul` was applied after `antisym_swap`:

After swap: `sum (tensor R [a,b,c,d]) (smul (-1) 1 (tensor R [a,b,c,d]))`
After `rw [tensor_as_smul]`: `sum (smul 1 1 (tensor R [a,b,c,d])) (smul (-1) 1 (smul 1 1 (tensor R [a,b,c,d])))`

The inner tensor inside `smul (-1) 1 (...)` also got wrapped, creating a nested `smul` that `collect_smul` can't match.

**Fix:** Apply `tensor_as_smul` BEFORE the swap step. At that point the index lists differ (`[a,b,c,d]` vs `[a,b,d,c]`) so `rw` only matches the left summand.

**Also:** `omega` can't prove `2 < [a,b,c,d].length` because it can't unfold `List.length`. Use `by decide` instead — it evaluates the concrete computation.

**Also:** `rw [smul_zero]` can't match `smul (1*1 + -1*1) (1*1) e` because the pattern `smul 0 d e` requires literal `0`, and `1*1 + -1*1` isn't reduced by the rewriter. Use `exact smul_zero (1*1) e` instead — the kernel reduces the arithmetic during type checking.

**Lesson for Theoria:** The replayer must be aware of Lean's rewrite semantics. Step ordering matters. Using `exact` with partially-evaluated terms is more robust than `rw` for the final step.

## Learned: `@[default_target]` only builds marked targets (2026-03-13)

`lake build` only builds targets marked `@[default_target]`. The original lakefile only marked `MicroTensor`, so Example.lean, Generated.lean etc. were silently never typechecked. All `lean_lib` entries need the attribute.

## Status: MVP complete (2026-03-13)

All PRD success criteria met:
1. ✅ `lake build` passes (hand-written + generated proofs)
2. ✅ Julia emits valid 3-step JSON traces
3. ✅ Replayer (`scripts/replay.jl`) converts traces to typechecking `.lean` files
4. ✅ `scripts/prove.sh` runs end-to-end with exit 0
5. ✅ Second identity works with zero axiom changes
6. ✅ NOTES.md has findings (this section)

## Explored: `lean-term` branch — term-mode proofs (2026-03-13)

**Result: works, straightforward for this pattern.**

The term-mode proof uses `Eq.trans` chains and `congrArg` for targeted rewrites:
- `congrArg (sum · rhs) proof` rewrites the left argument of sum
- `congrArg (sum lhs) proof` rewrites the right argument
- `h1.trans (h2.trans (h3.trans h4))` chains the steps

**Advantages over tactic mode:**
- No `rw` surprises: `congrArg` targets exactly one position, no risk of rewriting too many occurrences
- No need for `conv` workarounds
- The replayer has explicit control over which subterm to rewrite

**Disadvantages:**
- More verbose (~15 lines vs ~10 for tactic)
- Must spell out intermediate types (the replayer must track the expression state, which it already does)
- Needs a helper lemma for the index swap (`idx_swap_23`) because `▸` (subst) works differently in term mode

**Verdict:** Term mode is the better choice for generated proofs. The verbosity doesn't matter (it's auto-generated), and the explicit control avoids the `rw` pitfalls that required the tensor_as_smul reordering hack.

## Explored: `lean-decide` branch — canonicalizer (2026-03-13)

**Result: works for computational verification, but proves a weaker statement.**

Built a `canon : TExpr → Registry → TExpr` function in Lean that normalizes expressions (find differing slots, check registry, apply symmetry, collect coefficients, eliminate zeros). Both identities proved with one-line `by native_decide`.

**Key findings:**
- The canonicalizer is ~50 lines of Lean. It's a direct port of the Julia simplifier logic.
- `native_decide` needs `DecidableEq` on `TExpr` and `Symmetry` (derived easily).
- `List.enum` doesn't exist in v4.27.0; had to write recursive `diffSlots` manually.
- The proofs are one line each, no trace needed.

**The gap:** This proves `canon(expr, reg) = zero` (a computational fact about the `canon` function), NOT `expr = zero` (the algebraic identity under the axioms). To bridge this gap, we'd need to prove `canon` correct: that each step of canonicalization corresponds to a valid axiom application. This is essentially proving the canonicalizer is a model of the equational theory — a serious project.

**When to use which approach:**
- **Trace replay (master):** Proves `expr = zero` directly. Each step is justified by an axiom. The proof is in the language of the theory.
- **Canonicalizer (lean-decide):** Proves the computation produces zero. Faster to check, no trace overhead, but the proof doesn't reference the axioms at all.

For the prototype, the trace replay approach is correct. The canonicalizer is interesting for exploration but doesn't replace it.

## Next concrete steps

1. ✅ ~~Fix `schema.json`~~ — done (0-indexed)
2. **Merge `lean-term` approach** into the replayer — generate term-mode proofs by default
3. **Try a 3-term identity** — e.g., the first Bianchi identity R_{a[bcd]} = 0
4. **Merge `lean-decide` DecidableEq** additions into master (useful regardless)
