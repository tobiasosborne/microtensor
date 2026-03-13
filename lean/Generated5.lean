import MicroTensor
import Rules

open TExpr

namespace Canon

def idx_a : Index := ⟨"a", .down⟩
def idx_b : Index := ⟨"b", .down⟩
def idx_c : Index := ⟨"c", .down⟩
def idx_d : Index := ⟨"d", .down⟩

variable {M : Type*} [AddCommGroup M] [Module ℚ M] (env : TEnv M)

theorem canon_integration
    (h_antisym_R_0_1 : env.isAntisym "R" 0 1)
    (h_antisym_R_2_3 : env.isAntisym "R" 2 3)
    :
    (tensor "R" [idx_b, idx_a, idx_d, idx_c]).eval env =
    (tensor "R" [idx_a, idx_b, idx_c, idx_d]).eval env := by
  simp only [TExpr.eval]
  have hs1 : [idx_b, idx_a, idx_d, idx_c] = ([idx_a, idx_b, idx_d, idx_c]).swap 0 1 := by native_decide
  rw [hs1, env.swap_neg "R" [idx_a, idx_b, idx_d, idx_c] 0 1 h_antisym_R_0_1 (by decide) (by decide)]
  have hs2 : [idx_a, idx_b, idx_d, idx_c] = ([idx_a, idx_b, idx_c, idx_d]).swap 2 3 := by native_decide
  rw [hs2, env.swap_neg "R" [idx_a, idx_b, idx_c, idx_d] 2 3 h_antisym_R_2_3 (by decide) (by decide)]
  simp

end Canon

