import BooleanAlgebrasDoneRight.Hom

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# Boolean algebra isomorphisms

An isomorphism of Boolean algebras is defined intrinsically as a bijective
Boolean homomorphism. Two Boolean algebras are isomorphic when such an
isomorphism exists.
-/

universe u v

namespace BooleanAlgebrasDoneRight

namespace BooleanAlgebra

/-- An isomorphism from the Boolean algebra `A` to the Boolean algebra `B`
is a bijective Boolean homomorphism. -/
structure Iso (A : Type u) (B : Type v) [BooleanAlgebra A] [BooleanAlgebra B] where
  toHom : Hom A B
  bijective' : Function.Bijective toHom

instance {A : Type u} {B : Type v} [BooleanAlgebra A] [BooleanAlgebra B] :
    CoeFun (Iso A B) (fun _ => A → B) :=
  ⟨fun e => e.toHom.toFun⟩

variable {A : Type u} {B : Type v} [BooleanAlgebra A] [BooleanAlgebra B]

/-- The underlying map of an isomorphism is bijective. -/
theorem Iso.bijective (e : Iso A B) : Function.Bijective e :=
  e.bijective'

/-- The underlying map of an isomorphism is injective. -/
theorem Iso.injective (e : Iso A B) : Function.Injective e :=
  e.bijective'.1

/-- The underlying map of an isomorphism is surjective. -/
theorem Iso.surjective (e : Iso A B) : Function.Surjective e :=
  e.bijective'.2

/-- The identity isomorphism of a Boolean algebra. -/
def Iso.refl (A : Type u) [BooleanAlgebra A] : Iso A A where
  toHom := Hom.id A
  bijective' := by
    constructor
    · intro x y h
      exact h
    · intro y
      exact ⟨y, rfl⟩

@[simp] theorem Iso.refl_apply (x : A) :
    Iso.refl A x = x :=
  rfl

/-- Two Boolean algebras are isomorphic when there exists an isomorphism
between them. -/
def Isomorphic (A : Type u) (B : Type v) [BooleanAlgebra A] [BooleanAlgebra B] : Prop :=
  Nonempty (Iso A B)

/-- Every Boolean algebra is isomorphic to itself. -/
theorem isomorphic_refl (A : Type u) [BooleanAlgebra A] :
    Isomorphic A A :=
  ⟨Iso.refl A⟩

end BooleanAlgebra

end BooleanAlgebrasDoneRight
