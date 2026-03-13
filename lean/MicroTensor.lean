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

/-- Tensor expression IR. Binary sums, products, and contraction. -/
inductive TExpr where
  | zero : TExpr
  | scalar : Int → Int → TExpr   -- numerator, denominator (rational)
  | tensor : String → List Index → TExpr
  | smul : Int → Int → TExpr → TExpr  -- coeff num, den, inner expr
  | sum : TExpr → TExpr → TExpr
  | prod : TExpr → TExpr → TExpr      -- tensor product (binary)
  | contract : Nat → Nat → TExpr → TExpr  -- index contraction at slot positions
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

/-- Cyclic permutation of three positions in a list: i←k, j←i, k←j. -/
def List.cyclicPerm3 {α : Type} (l : List α) (i j k : Nat) : List α :=
  match l[i]?, l[j]?, l[k]? with
  | some vi, some vj, some vk =>
    l.mapIdx fun idx v =>
      if idx == i then vk
      else if idx == j then vi
      else if idx == k then vj
      else v
  | _, _, _ => l

-- ─────────────────────────────────────────────────────────────
-- Semantic evaluation: map TExpr into a ℚ-module
-- ─────────────────────────────────────────────────────────────

/-- Rational coefficient from integer numerator/denominator pair. -/
def ratCoeff (n d : Int) : ℚ := (n : ℚ) / (d : ℚ)

/-- An environment maps tensor configurations to values in M,
    with registry-aware symmetry constraints. The predicates `isAntisym`,
    `isSym`, `isBianchi` declare which (tensor, slot) combinations have
    which symmetries; the constraints are conditional on these.
    `mul` is a bilinear operation for evaluating tensor products.
    `contractAt` is a linear operation for evaluating index contractions. -/
structure TEnv (M : Type*) [AddCommGroup M] [Module ℚ M] where
  lookup : String → List Index → M
  mul : M → M → M
  mul_add_left : ∀ (a b c : M), mul (a + b) c = mul a c + mul b c
  mul_add_right : ∀ (a b c : M), mul a (b + c) = mul a b + mul a c
  smul_mul_left : ∀ (r : ℚ) (a b : M), mul (r • a) b = r • mul a b
  smul_mul_right : ∀ (r : ℚ) (a b : M), mul a (r • b) = r • mul a b
  mul_zero_left : ∀ (a : M), mul 0 a = 0
  mul_zero_right : ∀ (a : M), mul a 0 = 0
  contractAt : Nat → Nat → M → M
  contractAt_add : ∀ (i j : Nat) (a b : M),
    contractAt i j (a + b) = contractAt i j a + contractAt i j b
  contractAt_smul : ∀ (i j : Nat) (r : ℚ) (a : M),
    contractAt i j (r • a) = r • contractAt i j a
  contractAt_zero : ∀ (i j : Nat), contractAt i j 0 = 0
  isAntisym : String → Nat → Nat → Prop
  isSym : String → Nat → Nat → Prop
  isBianchi : String → Nat → Nat → Nat → Prop
  swap_neg : ∀ (name : String) (idxs : List Index) (s1 s2 : Nat),
    isAntisym name s1 s2 →
    s1 < idxs.length → s2 < idxs.length →
    lookup name (idxs.swap s1 s2) = -(lookup name idxs)
  swap_id : ∀ (name : String) (idxs : List Index) (s1 s2 : Nat),
    isSym name s1 s2 →
    s1 < idxs.length → s2 < idxs.length →
    lookup name (idxs.swap s1 s2) = lookup name idxs
  bianchi : ∀ (name : String) (idxs : List Index) (s1 s2 s3 : Nat),
    isBianchi name s1 s2 s3 →
    s1 < idxs.length → s2 < idxs.length → s3 < idxs.length →
    lookup name idxs +
    (lookup name (idxs.cyclicPerm3 s1 s2 s3) +
     lookup name ((idxs.cyclicPerm3 s1 s2 s3).cyclicPerm3 s1 s2 s3)) = 0

/-- Interpret a tensor expression in a ℚ-module via an environment. -/
noncomputable def TExpr.eval {M : Type*} [AddCommGroup M] [Module ℚ M]
    (env : TEnv M) : TExpr → M
  | .zero => 0
  | .scalar _ _ => 0
  | .tensor name idxs => env.lookup name idxs
  | .smul n d e => ratCoeff n d • e.eval env
  | .sum a b => a.eval env + b.eval env
  | .prod a b => env.mul (a.eval env) (b.eval env)
  | .contract i j e => env.contractAt i j (e.eval env)
