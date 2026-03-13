import MicroTensor
import Rules

open TExpr

def idx_a : Index := ⟨"a", .down⟩
def idx_b : Index := ⟨"b", .down⟩
def idx_c : Index := ⟨"c", .down⟩
def idx_d : Index := ⟨"d", .down⟩

variable {M : Type*} [AddCommGroup M] [Module ℚ M] (env : TEnv M)

theorem generated_proof :
    (sum (tensor "R" [idx_a, idx_b, idx_c, idx_d]) (tensor "R" [idx_a, idx_b, idx_d, idx_c])).eval env =
    (zero).eval env := by
  simp only [TExpr.eval]
  have hs1 : [idx_a, idx_b, idx_d, idx_c] = ([idx_a, idx_b, idx_c, idx_d]).swap 2 3 := by native_decide
  rw [hs1, env.swap_neg "R" [idx_a, idx_b, idx_c, idx_d] 2 3 (by decide) (by decide)]
  exact add_neg_cancel _

