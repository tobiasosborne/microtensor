/-
  Rules.lean — Verified rewrite rules for tensor expressions.

  Each rule is a theorem proved from Mathlib's module algebra,
  via the semantic evaluation function `TExpr.eval`. The trace
  replayer applies these theorems in sequence to produce a checked proof.

  The rules correspond to:
    1. Slot antisymmetry: R_{...i...j...} = -R_{...j...i...}
    2. Scalar collection: a·e + b·e = (a+b)·e
    3. Zero elimination: 0·e = 0
    4. Sum identity: 0 + e = e, e + 0 = e
    5. SMul composition: a·(b·e) = (a*b)·e
-/

import MicroTensor

open TExpr

variable {M : Type*} [AddCommGroup M] [Module ℚ M] (env : TEnv M)

-- ─────────────────────────────────────────────────────────────
-- Rule 1: Slot antisymmetry
-- Swapping antisymmetric slots negates the tensor.
-- ─────────────────────────────────────────────────────────────

theorem eval_antisym_swap (name : String) (idxs : List Index) (s1 s2 : Nat)
    (ha : env.isAntisym name s1 s2)
    (h : s1 < idxs.length) (h2 : s2 < idxs.length) :
    (tensor name (idxs.swap s1 s2)).eval env =
    (smul (-1) 1 (tensor name idxs)).eval env := by
  simp [TExpr.eval, ratCoeff]
  exact env.swap_neg name idxs s1 s2 ha h h2

-- ─────────────────────────────────────────────────────────────
-- Rule 1a: Slot symmetry
-- Swapping symmetric slots preserves the tensor.
-- ─────────────────────────────────────────────────────────────

theorem eval_sym_swap (name : String) (idxs : List Index) (s1 s2 : Nat)
    (hs : env.isSym name s1 s2)
    (h : s1 < idxs.length) (h2 : s2 < idxs.length) :
    (tensor name (idxs.swap s1 s2)).eval env =
    (tensor name idxs).eval env := by
  simp [TExpr.eval]
  exact env.swap_id name idxs s1 s2 hs h h2

-- ─────────────────────────────────────────────────────────────
-- Rule 1b: First Bianchi identity
-- Cyclic permutation of three slots sums to zero.
-- ─────────────────────────────────────────────────────────────

theorem eval_bianchi (name : String) (idxs : List Index) (s1 s2 s3 : Nat)
    (hb : env.isBianchi name s1 s2 s3)
    (h1 : s1 < idxs.length) (h2 : s2 < idxs.length) (h3 : s3 < idxs.length) :
    (sum (tensor name idxs)
         (sum (tensor name (idxs.cyclicPerm3 s1 s2 s3))
              (tensor name ((idxs.cyclicPerm3 s1 s2 s3).cyclicPerm3 s1 s2 s3)))).eval env =
    zero.eval env := by
  simp [TExpr.eval]
  exact env.bianchi name idxs s1 s2 s3 hb h1 h2 h3

-- ─────────────────────────────────────────────────────────────
-- Rule 2: Scalar collection
-- a·e + b·e = (a+b)·e (with rational arithmetic)
-- ─────────────────────────────────────────────────────────────

theorem eval_collect_smul (a_n a_d b_n b_d : Int) (e : TExpr)
    (ha : (a_d : ℚ) ≠ 0) (hb : (b_d : ℚ) ≠ 0) :
    (sum (smul a_n a_d e) (smul b_n b_d e)).eval env =
    (smul (a_n * b_d + b_n * a_d) (a_d * b_d) e).eval env := by
  simp only [TExpr.eval, ← add_smul]
  congr 1
  simp only [ratCoeff, Int.cast_mul, Int.cast_add]
  field_simp

theorem eval_tensor_as_smul (name : String) (idxs : List Index) :
    (tensor name idxs).eval env =
    (smul 1 1 (tensor name idxs)).eval env := by
  simp [TExpr.eval, ratCoeff]

-- ─────────────────────────────────────────────────────────────
-- Rule 3: Zero elimination
-- 0·e = 0
-- ─────────────────────────────────────────────────────────────

theorem eval_smul_zero (d : Int) (e : TExpr) :
    (smul 0 d e).eval env = zero.eval env := by
  simp [TExpr.eval, ratCoeff]

-- ─────────────────────────────────────────────────────────────
-- Rule 4: Sum identity
-- 0 + e = e, e + 0 = e
-- ─────────────────────────────────────────────────────────────

theorem eval_sum_zero_left (e : TExpr) :
    (sum zero e).eval env = e.eval env := by
  simp [TExpr.eval]

theorem eval_sum_zero_right (e : TExpr) :
    (sum e zero).eval env = e.eval env := by
  simp [TExpr.eval]

-- ─────────────────────────────────────────────────────────────
-- Rule 5: SMul composition
-- a·(b·e) = (a*b)·e
-- ─────────────────────────────────────────────────────────────

theorem eval_smul_smul (a_n a_d b_n b_d : Int) (e : TExpr) :
    (smul a_n a_d (smul b_n b_d e)).eval env =
    (smul (a_n * b_n) (a_d * b_d) e).eval env := by
  simp only [TExpr.eval, _root_.smul_smul]
  congr 1
  simp only [ratCoeff, Int.cast_mul]
  by_cases ha : (a_d : ℚ) = 0 <;> simp_all [div_zero]
  by_cases hb : (b_d : ℚ) = 0 <;> simp_all [div_zero, mul_zero]
  field_simp
