import BooleanAlgebrasDoneRight.Hom
import BooleanAlgebrasDoneRight.Order
import Mathlib.Order.SymmDiff

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

section RingLaws

-- Use the lattice already derived from the intrinsic algebraic axioms.
-- This instance is local and retains every original operation.
local instance : DistribLattice α := distribLattice α
local instance : _root_.BooleanAlgebra α where
  toDistribLattice := distribLattice α
  compl := BooleanOps.compl
  bot := zero
  top := one
  bot_le := zero_le
  le_top := le_one
  inf_compl_le_bot x := le_of_eq (meet_compl x)
  top_le_sup_compl x := le_of_eq (join_compl x).symm

/-- Symmetric difference vanishes exactly on equal arguments. -/
@[simp] theorem symmDiff_eq_zero_iff (x y : α) : symmDiff x y = zero ↔ x = y := by
  change _root_.symmDiff x y = ⊥ ↔ x = y
  exact _root_.symmDiff_eq_bot

theorem eq_iff_symmDiff_eq_zero (x y : α) : x = y ↔ symmDiff x y = zero :=
  (symmDiff_eq_zero_iff x y).symm

/-- Symmetric difference is associative. -/
theorem symmDiff_assoc (x y z : α) :
    symmDiff (symmDiff x y) z = symmDiff x (symmDiff y z) := by
  change _root_.symmDiff (_root_.symmDiff x y) z =
    _root_.symmDiff x (_root_.symmDiff y z)
  exact _root_.symmDiff_assoc

/-- Meet distributes over symmetric difference. -/
theorem meet_symmDiff_distrib (x y z : α) :
    meet x (symmDiff y z) = symmDiff (meet x y) (meet x z) := by
  change x ⊓ _root_.symmDiff y z = _root_.symmDiff (x ⊓ y) (x ⊓ z)
  exact _root_.inf_symmDiff_distrib_left

end RingLaws

end BooleanAlgebra

end BooleanAlgebrasDoneRight
