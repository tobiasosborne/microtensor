import MicroTensor
import Rules

open TExpr

namespace Bianchi

def idx_a : Index := ⟨"a", .down⟩
def idx_b : Index := ⟨"b", .down⟩
def idx_c : Index := ⟨"c", .down⟩
def idx_d : Index := ⟨"d", .down⟩

variable {M : Type*} [AddCommGroup M] [Module ℚ M] (env : TEnv M)

theorem bianchi_proof :
    (sum (tensor "R" [idx_a, idx_b, idx_c, idx_d]) (sum (tensor "R" [idx_a, idx_d, idx_b, idx_c]) (tensor "R" [idx_a, idx_c, idx_d, idx_b]))).eval env =
    (zero).eval env := by
  simp only [TExpr.eval]
  have h1 : [idx_a, idx_d, idx_b, idx_c] = ([idx_a, idx_b, idx_c, idx_d]).cyclicPerm3 1 2 3 := by native_decide
  have h2 : [idx_a, idx_c, idx_d, idx_b] = (([idx_a, idx_b, idx_c, idx_d]).cyclicPerm3 1 2 3).cyclicPerm3 1 2 3 := by native_decide
  rw [h1, h2]
  exact env.bianchi "R" [idx_a, idx_b, idx_c, idx_d] 1 2 3 (by decide) (by decide) (by decide)

end Bianchi

