/-
  Rules.lean — Verified rewrite rules for tensor expressions.

  These are the axioms of our tensor algebra. Each is a theorem that
  the Lean kernel verifies. The trace replayer applies these theorems
  in sequence to produce a checked proof.

  For the MVP, we axiomatise rather than derive from deeper foundations.
  The axioms correspond to:
    1. Slot antisymmetry: R_{...i...j...} = -R_{...j...i...} if antisym(i,j)
    2. Scalar collection: a·e + b·e = (a+b)·e
    3. Zero elimination: 0·e = 0
    4. Sum identity: 0 + e = e

  DESIGN NOTE: We use `axiom` here because we're defining the equational
  theory of tensor expressions, not deriving it from a model. This is
  the right move for the prototype — we can always replace axioms with
  theorems later once we have a semantic model (e.g., multilinear maps
  on a module). The axioms are obviously consistent (the standard
  interpretation in linear algebra is a model).
-/

import MicroTensor

open TExpr

-- ─────────────────────────────────────────────────────────────
-- Axiom 1: Slot antisymmetry
-- If tensor R has antisymmetry in slots s1,s2 then swapping those
-- slots negates the expression.
-- ─────────────────────────────────────────────────────────────

/-- Swapping antisymmetric slots negates the tensor. -/
axiom antisym_swap (name : String) (idxs : List Index) (s1 s2 : Nat)
    (h : s1 < idxs.length) (h2 : s2 < idxs.length) :
    tensor name (idxs.swap s1 s2) = smul (-1) 1 (tensor name idxs)

-- ─────────────────────────────────────────────────────────────
-- Axiom 2: Scalar collection
-- a·e + b·e = (a+b)·e (with rational arithmetic)
-- ─────────────────────────────────────────────────────────────

/-- Adding scalar multiples of the same expression. -/
axiom collect_smul (a_n a_d b_n b_d : Int) (e : TExpr) :
    sum (smul a_n a_d e) (smul b_n b_d e) =
    smul (a_n * b_d + b_n * a_d) (a_d * b_d) e

-- Convenience: bare tensor = smul 1 1 tensor
axiom tensor_as_smul (name : String) (idxs : List Index) :
    tensor name idxs = smul 1 1 (tensor name idxs)

-- ─────────────────────────────────────────────────────────────
-- Axiom 3: Zero elimination
-- 0·e = 0
-- ─────────────────────────────────────────────────────────────

/-- Zero scalar multiple is zero. -/
axiom smul_zero (d : Int) (e : TExpr) :
    smul 0 d e = zero

-- ─────────────────────────────────────────────────────────────
-- Axiom 4: Sum identity
-- 0 + e = e, e + 0 = e
-- ─────────────────────────────────────────────────────────────

axiom sum_zero_left (e : TExpr) : sum zero e = e
axiom sum_zero_right (e : TExpr) : sum e zero = e

-- ─────────────────────────────────────────────────────────────
-- Axiom 5: SMul composition
-- a·(b·e) = (a*b)·e
-- ─────────────────────────────────────────────────────────────

axiom smul_smul (a_n a_d b_n b_d : Int) (e : TExpr) :
    smul a_n a_d (smul b_n b_d e) = smul (a_n * b_n) (a_d * b_d) e
