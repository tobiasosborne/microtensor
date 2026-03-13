# MicroTensor IR Specification

The minimal IR for the prototype. Both Julia and Lean implement this exactly.

## Index

```
Index := { name : String, position : "up" | "down" }
```

No bundle/type distinctions yet. Just Lorentz indices.

## Expressions

```
TExpr :=
  | Zero
  | Scalar(value : Rational)
  | Tensor(name : String, indices : List Index)
  | SMul(coeff : Rational, expr : TExpr)
  | Sum(left : TExpr, right : TExpr)
```

Binary `Sum` only. N-ary sums in Julia are flattened to right-associated binary:
`a + b + c` = `Sum(a, Sum(b, c))`.

No `Prod` (tensor products) in the MVP — we only need single tensors and their sums.

## Symmetry declarations

```
Symmetry :=
  | Antisym(tensor : String, slot1 : Nat, slot2 : Nat)
  | Sym(tensor : String, slot1 : Nat, slot2 : Nat)
```

## Proof steps

```
ProofStep :=
  | SwapSlots(tensor : String, slot1 : Nat, slot2 : Nat, path : List Nat)
    -- Apply slot symmetry to the tensor at the given tree position.
    -- For Antisym: introduces factor of -1.
    -- For Sym: no sign change.
    -- `path` is the sequence of child selections from root (0 = left, 1 = right).

  | Collect(path : List Nat)
    -- At the given position, find Sum(SMul(a, e), SMul(b, e)) or equivalent,
    -- replace with SMul(a+b, e).
    -- Also handles bare Tensor as SMul(1, Tensor(...)).

  | ZeroElim(path : List Nat)
    -- At the given position, replace SMul(0, e) with Zero.

  | SumZero(path : List Nat)
    -- At the given position, replace Sum(Zero, e) with e or Sum(e, Zero) with e.
```

## Trace format

```json
{
  "registry": [
    {"name": "R", "rank": 4, "symmetries": [{"type": "antisym", "slots": [2, 3]}]}
  ],
  "expr": <TExpr as JSON>,
  "steps": [<ProofStep as JSON>, ...],
  "result": <TExpr as JSON>
}
```

## Semantics

Two expressions are **equal** if one can be transformed into the other by a finite sequence of proof steps. Each step is locally checkable: the Lean verifier checks that the rule is applicable at the specified position and that applying it produces the claimed result.

## What is deliberately NOT in the MVP

- Tensor products (contractions, index raising/lowering)
- Derivatives
- Metric
- Grassmann parity
- Dependent typing on index signatures
- Canonicalisation (xperm.c) — we do manual symmetry application instead
- Any CAS integration

All of these are future work. The MVP proves one identity with three rules.
