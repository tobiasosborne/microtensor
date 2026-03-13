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

-- The two terms
def R_abcd := tensor "R" [a, b, c, d]
def R_abdc := tensor "R" [a, b, d, c]   -- slots 2,3 swapped (0-indexed)

-- The expression to simplify
def expr := sum R_abcd R_abdc

-- Note: R_abdc is R with slots 2,3 (0-indexed) swapped relative to R_abcd.
-- So: tensor "R" [a,b,d,c] = (List.swap [a,b,c,d] 2 3) applied to "R"

-- We need: [a,b,d,c] = [a,b,c,d].swap 2 3
-- This is a concrete list equality, should be decidable.

-- The proof, step by step:
theorem riemann_antisym_34 :
    sum (tensor "R" [a, b, c, d]) (tensor "R" [a, b, d, c]) = zero := by
  -- Step 1: R_{abdc} = R with slots 2,3 swapped = -1 · R_{abcd}
  -- We need to show [a,b,d,c] = [a,b,c,d].swap 2 3
  -- Then apply antisym_swap
  have h_swap : [a, b, d, c] = [a, b, c, d].swap 2 3 := by native_decide
  rw [h_swap]
  rw [antisym_swap "R" [a, b, c, d] 2 3 (by omega) (by omega)]
  -- Now: sum (tensor "R" [a,b,c,d]) (smul (-1) 1 (tensor "R" [a,b,c,d]))
  -- Step 2: Rewrite left as smul 1 1
  rw [tensor_as_smul "R" [a, b, c, d]]
  -- Now: sum (smul 1 1 (tensor "R" [a,b,c,d])) (smul (-1) 1 (tensor "R" [a,b,c,d]))
  -- Step 3: Collect: (1/1 + (-1)/1) = 0/1
  rw [collect_smul 1 1 (-1) 1 (tensor "R" [a, b, c, d])]
  -- Now: smul (1*1 + (-1)*1) (1*1) (tensor "R" [a,b,c,d])
  -- = smul 0 1 (tensor "R" [a,b,c,d])
  -- Step 4: Zero elimination
  rw [smul_zero]


-- Alternate, more concise version
theorem riemann_antisym_34' :
    sum (tensor "R" [a, b, c, d]) (tensor "R" [a, b, d, c]) = zero := by
  have h : [a, b, d, c] = [a, b, c, d].swap 2 3 := by native_decide
  rw [h, antisym_swap "R" _ 2 3 (by omega) (by omega),
      tensor_as_smul, collect_smul, smul_zero]
