import BooleanAlgebrasDoneRight.Hom

/-!
# Symmetric difference

Symmetric difference is defined by `x Δ y = x · (-y) + y · (-x)`,
using the intrinsic Boolean operations. It is the candidate addition for
the associated Boolean ring.
-/

universe u v

namespace BooleanAlgebrasDoneRight

open BooleanOps

namespace BooleanAlgebra

variable {α : Type u} [BooleanAlgebra α]

/-- Symmetric difference, expressed in the Boolean algebra signature. -/
def symmDiff (x y : α) : α :=
  join (meet x (compl y)) (meet y (compl x))

theorem symmDiff_comm (x y : α) : symmDiff x y = symmDiff y x :=
  join_comm _ _

@[simp] theorem symmDiff_zero (x : α) : symmDiff x zero = x := by
  simp [symmDiff]

@[simp] theorem zero_symmDiff (x : α) : symmDiff zero x = x := by
  rw [symmDiff_comm, symmDiff_zero]

@[simp] theorem symmDiff_self (x : α) : symmDiff x x = zero := by
  simp [symmDiff, meet_compl]

@[simp] theorem symmDiff_one (x : α) : symmDiff x one = compl x := by
  simp [symmDiff]

@[simp] theorem one_symmDiff (x : α) : symmDiff one x = compl x := by
  rw [symmDiff_comm, symmDiff_one]

@[simp] theorem symmDiff_compl (x : α) : symmDiff x (compl x) = one := by
  simp [symmDiff, join_compl]

/-- Intrinsic Boolean homomorphisms preserve symmetric difference. -/
@[simp] theorem Hom.map_symmDiff {β : Type v} [BooleanAlgebra β]
    (f : Hom α β) (x y : α) : f (symmDiff x y) = symmDiff (f x) (f y) := by
  simp only [symmDiff, Hom.map_join, Hom.map_meet, Hom.map_compl]

end BooleanAlgebra

end BooleanAlgebrasDoneRight
