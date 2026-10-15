import BooleanAlgebrasDoneRight.Order
import BooleanAlgebrasDoneRight.Iso
import Mathlib.Order.Hom.BoundedLattice

/-!
# Algebraic and order isomorphisms

For the derived orders, Boolean algebra isomorphisms are exactly order
isomorphisms. Order determines the binary suprema and infima, the bounds,
and then the unique complement. All instances below are local.
-/

universe u v

namespace BooleanAlgebrasDoneRight

open BooleanOps

namespace BooleanAlgebra

variable {A : Type u} {B : Type v} [BooleanAlgebra A] [BooleanAlgebra B]

local instance : DistribLattice A := distribLattice A
local instance : DistribLattice B := distribLattice B
local instance : BoundedOrder A := boundedOrder A
local instance : BoundedOrder B := boundedOrder B

/-- An algebraic isomorphism preserves and reflects the derived order. -/
theorem Iso.le_iff (e : Iso A B) (x y : A) : le (e x) (e y) ↔ le x y := by
  change join (e x) (e y) = e y ↔ join x y = y
  rw [← e.toHom.map_join]
  exact e.injective.eq_iff

/-- Regard an algebraic isomorphism as an isomorphism of the derived orders. -/
noncomputable def Iso.toOrderIso (e : Iso A B) : A ≃o B where
  toEquiv := Equiv.ofBijective e e.bijective
  map_rel_iff' := e.le_iff _ _

@[simp] theorem Iso.toOrderIso_apply (e : Iso A B) (x : A) :
    e.toOrderIso x = e x := rfl

/-- An order isomorphism preserves the unique Boolean complement. -/
theorem orderIso_map_compl (e : A ≃o B) (x : A) :
    e (compl x) = compl (e x) := by
  apply eq_compl_of_join_eq_one_of_meet_eq_zero
  · calc
      join (e x) (e (compl x)) = e (join x (compl x)) := (map_sup e x (compl x)).symm
      _ = e one := congrArg e (join_compl x)
      _ = one := map_top e
  · calc
      meet (e x) (e (compl x)) = e (meet x (compl x)) := (map_inf e x (compl x)).symm
      _ = e zero := congrArg e (meet_compl x)
      _ = zero := map_bot e

/-- An isomorphism of the derived orders preserves the full Boolean signature. -/
def isoOfOrderIso (e : A ≃o B) : Iso A B where
  toHom :=
    { toFun := e
      map_zero' := map_bot e
      map_one' := map_top e
      map_join' := map_sup e
      map_meet' := map_inf e
      map_compl' := orderIso_map_compl e }
  bijective' := e.bijective

@[simp] theorem isoOfOrderIso_apply (e : A ≃o B) (x : A) :
    isoOfOrderIso e x = e x := rfl

/-- Boolean algebras are algebraically isomorphic iff their derived orders are isomorphic. -/
theorem isomorphic_iff_orderIso : Isomorphic A B ↔ Nonempty (A ≃o B) :=
  ⟨fun ⟨e⟩ => ⟨e.toOrderIso⟩, fun ⟨e⟩ => ⟨isoOfOrderIso e⟩⟩

end BooleanAlgebra

end BooleanAlgebrasDoneRight
