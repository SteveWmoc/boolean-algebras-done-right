import BooleanAlgebrasDoneRight.Basic
import Mathlib.Order.Lattice

/-!
# The order and lattice derived from Boolean operations

Define `BooleanAlgebra.le x y` by `join x y = y`. Idempotence,
commutativity, and associativity prove the partial-order laws. Absorption
identifies the same relation with `meet x y = x`.

`BooleanAlgebra.partialOrder` packages the derived relation as a Lean
partial order. It is an explicit construction, so callers can install it
locally without overriding an existing order on the carrier.
-/

universe u

namespace BooleanAlgebrasDoneRight

open BooleanOps

namespace LatticeTheory

/-- In any lattice, meet distributing over join implies the dual law. -/
theorem sup_distrib_inf_of_inf_distrib_sup {α : Type u} [Lattice α]
    (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) :
    ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) := by
  letI : DistribLattice α := DistribLattice.ofInfSupLe
    (fun x y z => le_of_eq (h x y z))
  exact sup_inf_left

/-- In any lattice, join distributing over meet implies the dual law. -/
theorem inf_distrib_sup_of_sup_distrib_inf {α : Type u} [Lattice α]
    (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) :
    ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  letI : DistribLattice α :=
    { toLattice := inferInstance
      le_sup_inf := fun x y z => le_of_eq (h x y z).symm }
  exact inf_sup_left

/-- Either distributive identity suffices in an arbitrary lattice. -/
theorem distributive_iff {α : Type u} [Lattice α] :
    (∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) ↔
      (∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) :=
  ⟨sup_distrib_inf_of_inf_distrib_sup, inf_distrib_sup_of_sup_distrib_inf⟩

end LatticeTheory

namespace BooleanAlgebra

variable {α : Type u} [BooleanAlgebra α]

/-- The order determined by the Boolean join operation. -/
def le (x y : α) : Prop := join x y = y

theorem le_iff_join_eq (x y : α) : le x y ↔ join x y = y := Iff.rfl

theorem le_iff_meet_eq (x y : α) : le x y ↔ meet x y = x :=
  join_eq_right_iff_meet_eq_left x y

theorem le_refl (x : α) : le x x := join_idem x

theorem le_antisymm {x y : α} (hxy : le x y) (hyx : le y x) : x = y :=
  hyx.symm.trans ((join_comm y x).trans hxy)

theorem le_trans {x y z : α} (hxy : le x y) (hyz : le y z) : le x z := by
  change join x y = y at hxy
  change join y z = z at hyz
  change join x z = z
  calc
    join x z = join x (join y z) := congrArg (join x) hyz.symm
    _ = join (join x y) z := (join_assoc x y z).symm
    _ = join y z := congrArg (fun a => join a z) hxy
    _ = z := hyz

/-- The canonical partial order derived from the algebraic Boolean laws. -/
abbrev partialOrder (α : Type u) [BooleanAlgebra α] : PartialOrder α where
  le := BooleanAlgebra.le
  le_refl := BooleanAlgebra.le_refl
  le_trans := fun _ _ _ => BooleanAlgebra.le_trans
  le_antisymm := fun _ _ => BooleanAlgebra.le_antisymm

/-- Join is an upper bound of its left argument. -/
theorem le_join_left (x y : α) : le x (join x y) :=
  (le_iff_meet_eq x (join x y)).mpr (meet_absorb_join x y)

/-- Join is an upper bound of its right argument. -/
theorem le_join_right (x y : α) : le y (join x y) := by
  rw [join_comm x y]
  exact le_join_left y x

/-- Join is the least of the common upper bounds. -/
theorem join_le {x y z : α} (hx : le x z) (hy : le y z) : le (join x y) z := by
  change join x z = z at hx
  change join y z = z at hy
  change join (join x y) z = z
  calc
    join (join x y) z = join x (join y z) := join_assoc x y z
    _ = join x z := congrArg (join x) hy
    _ = z := hx

/-- Meet is a lower bound of its left argument. -/
theorem meet_le_left (x y : α) : le (meet x y) x := by
  change join (meet x y) x = x
  exact (join_comm (meet x y) x).trans (join_absorb_meet x y)

/-- Meet is a lower bound of its right argument. -/
theorem meet_le_right (x y : α) : le (meet x y) y := by
  rw [meet_comm x y]
  exact meet_le_left y x

/-- Meet is the greatest of the common lower bounds. -/
theorem le_meet {x y z : α} (hx : le z x) (hy : le z y) : le z (meet x y) := by
  apply (le_iff_meet_eq z (meet x y)).mpr
  have hzx := (le_iff_meet_eq z x).mp hx
  have hzy := (le_iff_meet_eq z y).mp hy
  calc
    meet z (meet x y) = meet (meet z x) y := (meet_assoc z x y).symm
    _ = meet z y := congrArg (fun a => meet a y) hzx
    _ = z := hzy

theorem join_le_iff (x y z : α) :
    le (join x y) z ↔ le x z ∧ le y z :=
  ⟨fun h => ⟨le_trans (le_join_left x y) h, le_trans (le_join_right x y) h⟩,
    fun h => join_le h.1 h.2⟩

theorem le_meet_iff (x y z : α) :
    le z (meet x y) ↔ le z x ∧ le z y :=
  ⟨fun h => ⟨le_trans h (meet_le_left x y), le_trans h (meet_le_right x y)⟩,
    fun h => le_meet h.1 h.2⟩

/-- The derived lattice has the original join as supremum and meet as infimum. -/
abbrev lattice (α : Type u) [BooleanAlgebra α] : Lattice α where
  toPartialOrder := partialOrder α
  sup := join
  inf := meet
  le_sup_left := le_join_left
  le_sup_right := le_join_right
  sup_le := fun _ _ _ => join_le
  inf_le_left := meet_le_left
  inf_le_right := meet_le_right
  le_inf := fun _ _ _ => le_meet

/-- The derived lattice is distributive; the meet distributive law alone suffices. -/
abbrev distribLattice (α : Type u) [BooleanAlgebra α] : DistribLattice α := by
  letI := lattice α
  exact DistribLattice.ofInfSupLe
    (fun x y z => le_of_eq (meet_distrib_join x y z))

end BooleanAlgebra

end BooleanAlgebrasDoneRight
