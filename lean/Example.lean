/-
  Example.lean — Hand-written proof of R_{abcd} + R_{abdc} = 0.

  The proof works by evaluating tensor expressions into a ℚ-module
  and using the environment's antisymmetry constraint.
-/

import MicroTensor
import Rules

open TExpr

-- Define the indices
def a : Index := ⟨"a", .down⟩
def b : Index := ⟨"b", .down⟩
def c : Index := ⟨"c", .down⟩
def d : Index := ⟨"d", .down⟩

variable {M : Type*} [AddCommGroup M] [Module ℚ M] (env : TEnv M)

-- The proof: R_{abcd} + R_{abdc} = 0 under evaluation
theorem riemann_antisym_34 :
    (sum (tensor "R" [a, b, c, d]) (tensor "R" [a, b, d, c])).eval env =
    zero.eval env := by
  -- Unfold eval to module operations
  simp only [TExpr.eval]
  -- Show swapped indices match a slot swap
  have h_swap : [a, b, d, c] = ([a, b, c, d].swap 2 3) := by native_decide
  rw [h_swap, env.swap_neg "R" [a, b, c, d] 2 3 (by decide) (by decide)]
  -- x + (-x) = 0
  exact add_neg_cancel _
