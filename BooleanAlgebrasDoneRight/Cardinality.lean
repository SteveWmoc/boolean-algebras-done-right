import Mathlib.SetTheory.Cardinal.Defs
import BooleanAlgebrasDoneRight.Basic

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# Cardinality of a Boolean algebra

The cardinality of a Boolean algebra is, by definition, the cardinality of its
underlying carrier type.
-/

universe u

namespace BooleanAlgebrasDoneRight

namespace BooleanAlgebra

/-- The cardinality of a Boolean algebra is the cardinality of its carrier. -/
def cardinality (α : Type u) [BooleanAlgebra α] : Cardinal.{u} :=
  Cardinal.mk α

@[simp] theorem cardinality_eq_mk (α : Type u) [BooleanAlgebra α] :
    cardinality α = Cardinal.mk α :=
  rfl

end BooleanAlgebra

end BooleanAlgebrasDoneRight
