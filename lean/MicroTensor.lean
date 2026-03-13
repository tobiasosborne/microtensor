/-
  MicroTensor.lean — Minimal tensor expression IR for verified algebra.

  This must match shared/ir.md and julia/MicroTensor.jl exactly.
  The types are deliberately simple (no dependent indices) for the MVP.

  The semantic evaluation function `TExpr.eval` maps expressions into a
  ℚ-module, allowing us to replace axioms with Mathlib-backed theorems.
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.FieldSimp

/-- Index position: upper (contravariant) or lower (covariant). -/
inductive Position where
  | up
  | down
  deriving Repr, BEq, DecidableEq

/-- A tensor index: a name and a position. -/
structure Index where
  name : String
  position : Position
  deriving Repr, BEq, DecidableEq

/-- Tensor expression IR. Binary sums, no products (MVP). -/
inductive TExpr where
  | zero : TExpr
  | scalar : Int → Int → TExpr   -- numerator, denominator (rational)
  | tensor : String → List Index → TExpr
  | smul : Int → Int → TExpr → TExpr  -- coeff num, den, inner expr
  | sum : TExpr → TExpr → TExpr
  deriving Repr, BEq

/-- Symmetry declaration for a tensor. -/
inductive Symmetry where
  | antisym : String → Nat → Nat → Symmetry  -- tensor name, slot1, slot2
  | sym : String → Nat → Nat → Symmetry
  deriving Repr, BEq

/-- A registry is just a list of symmetry declarations. -/
def Registry := List Symmetry

/-- Check if a registry declares antisymmetry for given tensor and slots. -/
def Registry.hasAntisym (reg : Registry) (name : String) (s1 s2 : Nat) : Bool :=
  reg.any fun
    | .antisym n a b => n == name && a == s1 && b == s2
    | _ => false

/-- Swap two elements in a list by index (0-based in Lean). -/
def List.swap {α : Type} (l : List α) (i j : Nat) : List α :=
  match l[i]?, l[j]? with
  | some vi, some vj =>
    l.mapIdx fun k v =>
      if k == i then vj
      else if k == j then vi
      else v
  | _, _ => l

-- ─────────────────────────────────────────────────────────────
-- Semantic evaluation: map TExpr into a ℚ-module
-- ─────────────────────────────────────────────────────────────

/-- Rational coefficient from integer numerator/denominator pair. -/
def ratCoeff (n d : Int) : ℚ := (n : ℚ) / (d : ℚ)

/-- An environment maps tensor configurations to values in M,
    subject to an antisymmetry constraint on slot swaps. -/
structure TEnv (M : Type*) [AddCommGroup M] where
  lookup : String → List Index → M
  swap_neg : ∀ (name : String) (idxs : List Index) (s1 s2 : Nat),
    s1 < idxs.length → s2 < idxs.length →
    lookup name (idxs.swap s1 s2) = -(lookup name idxs)

/-- Interpret a tensor expression in a ℚ-module via an environment. -/
noncomputable def TExpr.eval {M : Type*} [AddCommGroup M] [Module ℚ M]
    (env : TEnv M) : TExpr → M
  | .zero => 0
  | .scalar _ _ => 0
  | .tensor name idxs => env.lookup name idxs
  | .smul n d e => ratCoeff n d • e.eval env
  | .sum a b => a.eval env + b.eval env
