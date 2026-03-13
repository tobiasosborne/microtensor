import MicroTensor
import Rules

open TExpr

def idx_a : Index := ⟨"a", .down⟩
def idx_b : Index := ⟨"b", .down⟩
def idx_c : Index := ⟨"c", .down⟩
def idx_d : Index := ⟨"d", .down⟩

theorem generated_proof :
    sum (tensor "R" [idx_a, idx_b, idx_c, idx_d]) (tensor "R" [idx_a, idx_b, idx_d, idx_c]) = zero := by
  -- Step 1: swap slots 2,3 of R
  have h1 : [⟨"a", .down⟩, ⟨"b", .down⟩, ⟨"d", .down⟩, ⟨"c", .down⟩] = [⟨"a", .down⟩, ⟨"b", .down⟩, ⟨"c", .down⟩, ⟨"d", .down⟩] |>.swap 2 3 := by native_decide
  rw [h1]
  rw [antisym_swap "R" [⟨"a", .down⟩, ⟨"b", .down⟩, ⟨"c", .down⟩, ⟨"d", .down⟩] 2 3 (by omega) (by omega)]
  -- Step 2: collect
  rw [tensor_as_smul "R" [⟨"a", .down⟩, ⟨"b", .down⟩, ⟨"c", .down⟩, ⟨"d", .down⟩]]
  rw [collect_smul 1 1 (-1) 1 (tensor "R" [⟨"a", .down⟩, ⟨"b", .down⟩, ⟨"c", .down⟩, ⟨"d", .down⟩])]
  -- Step 3: zero elimination
  rw [smul_zero]

