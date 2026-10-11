import BooleanAlgebrasDoneRight.Trivial
import BooleanAlgebrasDoneRight.Examples.Set

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# The one-element power set algebra

The power set of the empty set is the canonical set-theoretic example of the
trivial Boolean algebra.  Its carrier contains exactly one element, namely the
empty set.
-/

universe u v

namespace BooleanAlgebrasDoneRight

open BooleanOps

namespace SetExamples

/-- The power set algebra of the empty set. -/
abbrev EmptyPowerSetAlgebra (α : Type u) : Type u :=
  PowerSetAlgebra (∅ : Set α)

/-- The power set of the empty set has at most one element. -/
instance emptyPowerSetSubsingleton (α : Type u) :
    Subsingleton (EmptyPowerSetAlgebra α) where
  allEq a b := by
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      exact (a.2 hx).elim
    · intro hx
      exact (b.2 hx).elim

/-- In the power set algebra of the empty set, zero and one coincide. -/
@[simp] theorem emptyPowerSet_zero_eq_one (α : Type u) :
    (zero : EmptyPowerSetAlgebra α) = one :=
  Subsingleton.elim _ _

/-- The power set algebra of the empty set has cardinality one. -/
@[simp] theorem emptyPowerSet_cardinality (α : Type u) :
    BooleanAlgebra.cardinality (EmptyPowerSetAlgebra α) = 1 :=
  BooleanAlgebra.cardinality_eq_one_of_subsingleton _

/-- Every one-element Boolean algebra is isomorphic to the power set algebra
of the empty set. -/
theorem emptyPowerSet_isomorphic_of_subsingleton
    (α : Type u) (A : Type v)
    [BooleanAlgebra A] [Subsingleton A] :
    BooleanAlgebra.Isomorphic (EmptyPowerSetAlgebra α) A :=
  BooleanAlgebra.isomorphic_of_subsingleton _ _

end SetExamples

end BooleanAlgebrasDoneRight
