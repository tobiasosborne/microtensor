import MicroTensor
import Rules

open TExpr

namespace Proof12

def idx_a : Index := ⟨"a", .down⟩
def idx_b : Index := ⟨"b", .down⟩
def idx_c : Index := ⟨"c", .down⟩
def idx_d : Index := ⟨"d", .down⟩

theorem generated_proof_12 :
    sum (tensor "R" [idx_a, idx_b, idx_c, idx_d]) (tensor "R" [idx_b, idx_a, idx_c, idx_d]) = zero := by
  -- Normalize bare tensor to smul form (before swap, indices differ)
  rw [tensor_as_smul "R" [idx_a, idx_b, idx_c, idx_d]]
  -- Step 1: swap slots 0,1 of R
  have h1 : [idx_b, idx_a, idx_c, idx_d] = ([idx_a, idx_b, idx_c, idx_d]).swap 0 1 := by native_decide
  rw [h1]
  rw [antisym_swap "R" [idx_a, idx_b, idx_c, idx_d] 0 1 (by decide) (by decide)]
  -- Step 2: collect
  rw [collect_smul 1 1 (-1) 1 (tensor "R" [idx_a, idx_b, idx_c, idx_d])]
  -- Step 3: zero elimination
  exact smul_zero (1) (tensor "R" [idx_a, idx_b, idx_c, idx_d])

end Proof12

