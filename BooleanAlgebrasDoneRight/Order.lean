import BooleanAlgebrasDoneRight.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Disjoint

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
  let : DistribLattice α := DistribLattice.ofInfSupLe
    (fun x y z => le_of_eq (h x y z))
  exact sup_inf_left

/-- In any lattice, join distributing over meet implies the dual law. -/
theorem inf_distrib_sup_of_sup_distrib_inf {α : Type u} [Lattice α]
    (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) :
    ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  let : DistribLattice α :=
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

/-- Join is monotone in both arguments. -/
theorem join_mono {x x' y y' : α} (hx : le x x') (hy : le y y') :
    le (join x y) (join x' y') :=
  join_le (le_trans hx (le_join_left x' y')) (le_trans hy (le_join_right x' y'))

/-- Meet is monotone in both arguments. -/
theorem meet_mono {x x' y y' : α} (hx : le x x') (hy : le y y') :
    le (meet x y) (meet x' y') :=
  le_meet (le_trans (meet_le_left x y) hx) (le_trans (meet_le_right x y) hy)

theorem join_mono_left {x x' : α} (h : le x x') (y : α) :
    le (join x y) (join x' y) :=
  join_mono h (le_refl y)

theorem join_mono_right (x : α) {y y' : α} (h : le y y') :
    le (join x y) (join x y') :=
  join_mono (le_refl x) h

theorem meet_mono_left {x x' : α} (h : le x x') (y : α) :
    le (meet x y) (meet x' y) :=
  meet_mono h (le_refl y)

theorem meet_mono_right (x : α) {y y' : α} (h : le y y') :
    le (meet x y) (meet x y') :=
  meet_mono (le_refl x) h

/-- Complement reverses the derived order. -/
theorem compl_le_compl {x y : α} (h : le x y) : le (compl y) (compl x) := by
  apply (le_iff_meet_eq (compl y) (compl x)).mpr
  calc
    meet (compl y) (compl x) = meet (compl x) (compl y) := meet_comm _ _
    _ = compl (join x y) := (compl_join x y).symm
    _ = compl y := congrArg BooleanOps.compl h

/-- Complementation reverses and reflects the derived order. -/
@[simp] theorem compl_le_compl_iff (x y : α) :
    le (compl y) (compl x) ↔ le x y := by
  constructor
  · intro h
    simpa only [compl_compl] using compl_le_compl h
  · exact compl_le_compl

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

/-- Zero is the least element of the derived order. -/
theorem zero_le (x : α) : le zero x := zero_join x

/-- One is the greatest element of the derived order. -/
theorem le_one (x : α) : le x one := join_one x

theorem le_zero_iff (x : α) : le x zero ↔ x = zero :=
  ⟨fun h => le_antisymm h (zero_le x), by intro h; subst x; exact le_refl zero⟩

theorem one_le_iff (x : α) : le one x ↔ x = one :=
  ⟨fun h => le_antisymm (le_one x) h, by intro h; subst x; exact le_refl one⟩

/-- Bounds for the derived distributive lattice, with bottom zero and top one.

Install `distribLattice α` and then `boundedOrder α` locally to use
the bounded distributive lattice API. -/
abbrev boundedOrder (α : Type u) [BooleanAlgebra α] :
    letI := distribLattice α
    BoundedOrder α := by
  letI := distribLattice α
  exact
    { bot := zero
      top := one
      bot_le := zero_le
      le_top := le_one }

section Complements

local instance : DistribLattice α := distribLattice α
local instance : BoundedOrder α := boundedOrder α

/-- The original Boolean complement is a complement in the derived lattice. -/
theorem isCompl_compl (x : α) : IsCompl x (compl x) :=
  IsCompl.of_eq (meet_compl x) (join_compl x)

/-- Lattice complements agree exactly with the original Boolean complement. -/
theorem isCompl_iff_eq_compl (x y : α) : IsCompl x y ↔ y = compl x := by
  constructor
  · intro h
    exact eq_compl_of_join_eq_one_of_meet_eq_zero h.sup_eq_top h.inf_eq_bot
  · intro h
    subst y
    exact isCompl_compl x

/-- Every element of the derived bounded distributive lattice has a complement. -/
theorem complementedLattice (α) [BooleanAlgebra α] : ComplementedLattice α where
  exists_isCompl x := ⟨compl x, isCompl_compl x⟩

end Complements

end BooleanAlgebra

end BooleanAlgebrasDoneRight
