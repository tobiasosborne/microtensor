import MicroTensor
import Rules

open TExpr

def idx_a : Index := ⟨"a", .down⟩
def idx_b : Index := ⟨"b", .down⟩
def idx_c : Index := ⟨"c", .down⟩
def idx_d : Index := ⟨"d", .down⟩

theorem generated_proof :
    sum (tensor "R" [idx_a, idx_b, idx_c, idx_d]) (tensor "R" [idx_a, idx_b, idx_d, idx_c]) = zero := by
  -- Normalize bare tensor to smul form (before swap, indices differ)
  rw [tensor_as_smul "R" [idx_a, idx_b, idx_c, idx_d]]
  -- Step 1: swap slots 2,3 of R
  have h1 : [idx_a, idx_b, idx_d, idx_c] = ([idx_a, idx_b, idx_c, idx_d]).swap 2 3 := by native_decide
  rw [h1]
  rw [antisym_swap "R" [idx_a, idx_b, idx_c, idx_d] 2 3 (by decide) (by decide)]
  -- Step 2: collect
  rw [collect_smul 1 1 (-1) 1 (tensor "R" [idx_a, idx_b, idx_c, idx_d])]
  -- Step 3: zero elimination
  exact smul_zero (1) (tensor "R" [idx_a, idx_b, idx_c, idx_d])

