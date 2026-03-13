/-
  Example.lean — Hand-written proof of R_{abcd} + R_{abdc} = 0.

  This is what the trace replayer should auto-generate.
  Writing it by hand first to validate the axiom set works.
-/

import MicroTensor
import Rules

open TExpr

-- Define the indices
def a : Index := ⟨"a", .down⟩
def b : Index := ⟨"b", .down⟩
def c : Index := ⟨"c", .down⟩
def d : Index := ⟨"d", .down⟩

-- The proof:
-- Key insight: do tensor_as_smul BEFORE the swap, so rw only hits the left summand
-- (the index lists differ, so the pattern only matches one side).
theorem riemann_antisym_34 :
    sum (tensor "R" [a, b, c, d]) (tensor "R" [a, b, d, c]) = zero := by
  -- Step 1: Wrap left tensor as smul 1 1 (indices differ, so only left matches)
  rw [tensor_as_smul "R" [a, b, c, d]]
  -- Step 2: Show the right indices are a swap of the canonical order
  have h_swap : [a, b, d, c] = ([a, b, c, d].swap 2 3) := by native_decide
  rw [h_swap]
  -- Step 3: Apply antisymmetry
  rw [antisym_swap "R" [a, b, c, d] 2 3 (by decide) (by decide)]
  -- Step 4: Collect: smul(1,1,e) + smul(-1,1,e) = smul(0,1,e)
  rw [collect_smul 1 1 (-1) 1 (tensor "R" [a, b, c, d])]
  -- Step 5: Zero elimination (kernel reduces 1*1 + -1*1 = 0 definitionally)
  exact smul_zero (1 * 1) (tensor "R" [a, b, c, d])
