import MicroTensor
import Rules

open TExpr

namespace MetricSym

def idx_a : Index := ⟨"a", .down⟩
def idx_b : Index := ⟨"b", .down⟩

variable {M : Type*} [AddCommGroup M] [Module ℚ M] (env : TEnv M)

theorem metric_sym_proof
    (h_sym_g_0_1 : env.isSym "g" 0 1)
    :
    (tensor "g" [idx_b, idx_a]).eval env =
    (tensor "g" [idx_a, idx_b]).eval env := by
  simp only [TExpr.eval]
  have hs1 : [idx_b, idx_a] = ([idx_a, idx_b]).swap 0 1 := by native_decide
  rw [hs1, env.swap_id "g" [idx_a, idx_b] 0 1 h_sym_g_0_1 (by decide) (by decide)]

end MetricSym

