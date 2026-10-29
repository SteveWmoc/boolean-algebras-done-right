import BooleanAlgebrasDoneRight.BooleanRing
import BooleanAlgebrasDoneRight.SymmetricDifference
import BooleanAlgebrasDoneRight.Iso

/-!
# Boolean algebra–Boolean ring correspondence

The constructions use tagged copies of the carrier, so Boolean join and
ring addition can coexist without competing instances. Both round trips
are isomorphic to the original structure by the identity map.
-/

universe u

namespace BooleanAlgebrasDoneRight
namespace BooleanRingCorrespondence

open BooleanOps

/-- The Mathlib lattice presentation of an intrinsic Boolean algebra. -/
abbrev toMathlib (A : Type u) [BooleanAlgebra A] : _root_.BooleanAlgebra A where
  toDistribLattice := BooleanAlgebra.distribLattice A
  compl := BooleanOps.compl
  bot := zero
  top := one
  bot_le := BooleanAlgebra.zero_le
  le_top := BooleanAlgebra.le_one
  inf_compl_le_bot x := by
    change BooleanAlgebra.le (meet x (BooleanOps.compl x)) zero
    rw [BooleanAlgebra.meet_compl]
    exact BooleanAlgebra.le_refl zero
  top_le_sup_compl x := by
    change BooleanAlgebra.le one (join x (BooleanOps.compl x))
    rw [BooleanAlgebra.join_compl]
    exact BooleanAlgebra.le_refl one

/-- The intrinsic algebraic presentation of a Mathlib Boolean algebra. -/
abbrev ofMathlib (A : Type u) [_root_.BooleanAlgebra A] : BooleanAlgebra A where
  meet := (· ⊓ ·)
  join := (· ⊔ ·)
  compl := Compl.compl
  zero := ⊥
  one := ⊤
  meet_assoc := inf_assoc
  meet_comm := inf_comm
  join_assoc := sup_assoc
  join_comm := sup_comm
  join_absorb_meet := sup_inf_self
  meet_absorb_join := inf_sup_self
  meet_distrib_join := inf_sup_left
  join_distrib_meet := sup_inf_left
  join_compl := sup_compl_eq_top
  meet_compl := inf_compl_eq_bot

/-- The carrier of the Boolean ring associated to a Boolean algebra. -/
def RingOf (A : Type u) : Type u := A

instance ringOfBooleanRing (A : Type u) [BooleanAlgebra A] : BooleanRing (RingOf A) :=
  @ _root_.BooleanAlgebra.toBooleanRing A (toMathlib A)

/-- The carrier of the Boolean algebra associated to a Boolean ring. -/
def AlgebraOf (R : Type u) : Type u := R

instance algebraOfBooleanAlgebra (R : Type u) [BooleanRing R] : BooleanAlgebra (AlgebraOf R) :=
  @ofMathlib R (@ _root_.BooleanRing.toBooleanAlgebra R inferInstance)

section AlgebraToRing

variable {A : Type u} [BooleanAlgebra A]

@[simp] theorem ringOf_add (x y : RingOf A) :
    x + y = BooleanAlgebra.symmDiff (α := A) x y := rfl

@[simp] theorem ringOf_mul (x y : RingOf A) :
    x * y = meet (α := A) x y := rfl

@[simp] theorem ringOf_neg (x : RingOf A) : -x = x := rfl
@[simp] theorem ringOf_zero : (0 : RingOf A) = (zero : A) := rfl
@[simp] theorem ringOf_one : (1 : RingOf A) = (one : A) := rfl

/-- Algebra to ring to algebra recovers all original Boolean operations. -/
def algebraRoundTripIso (A : Type u) [BooleanAlgebra A] :
    BooleanAlgebra.Iso (AlgebraOf (RingOf A)) A := by
  letI := toMathlib A
  exact
    { toHom :=
        { toFun := fun x => x
          map_zero' := rfl
          map_one' := rfl
          map_join' := fun x y => _root_.symmDiff_symmDiff_inf
          map_meet' := fun _ _ => rfl
          map_compl' := fun x => BooleanAlgebra.one_symmDiff (α := A) x }
      bijective' := Function.bijective_id }

end AlgebraToRing

section RingToAlgebra

variable {R : Type u} [BooleanRing R]

@[simp] theorem algebraOf_meet (x y : AlgebraOf R) :
    meet x y = (x : R) * (y : R) := rfl

@[simp] theorem algebraOf_join (x y : AlgebraOf R) :
    join x y = (x : R) + (y : R) + (x : R) * (y : R) := rfl

@[simp] theorem algebraOf_compl (x : AlgebraOf R) :
    BooleanOps.compl x = (1 : R) + (x : R) := rfl

@[simp] theorem algebraOf_zero : (zero : AlgebraOf R) = (0 : R) := rfl
@[simp] theorem algebraOf_one : (one : AlgebraOf R) = (1 : R) := rfl

/-- Ring to algebra to ring recovers the original unital ring operations. -/
def ringRoundTripEquiv (R : Type u) [BooleanRing R] : RingOf (AlgebraOf R) ≃+* R where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl
  map_add' := fun x y => _root_.ofBoolAlg_symmDiff (α := R) x y

end RingToAlgebra

end BooleanRingCorrespondence
end BooleanAlgebrasDoneRight
