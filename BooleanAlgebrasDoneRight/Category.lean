import Mathlib.CategoryTheory.Category.Basic
import BooleanAlgebrasDoneRight.Hom

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# The category of Boolean algebras

Boolean algebras are bundled as objects, and the morphisms are exactly the
intrinsic Boolean homomorphisms defined in `Hom.lean`.

Composition and identities are inherited from Boolean homomorphisms.
-/

universe u

namespace BooleanAlgebrasDoneRight

open CategoryTheory

/-- The category whose objects are Boolean algebras in the algebra-first
presentation. -/
structure BoolAlg where
  carrier : Type u
  [str : BooleanAlgebra carrier]

attribute [instance] BoolAlg.str

namespace BoolAlg

instance : CoeSort BoolAlg (Type u) :=
  ⟨BoolAlg.carrier⟩

/-- Bundle a Boolean algebra as an object of `BoolAlg`. -/
abbrev of (A : Type u) [BooleanAlgebra A] : BoolAlg :=
  ⟨A⟩

/-- Boolean algebras and Boolean homomorphisms form a category. -/
instance : Category.{u} BoolAlg where
  Hom A B := BooleanAlgebra.Hom A B
  id A := BooleanAlgebra.Hom.id A
  comp f g := g.comp f
  id_comp := by
    intro A B f
    cases f
    rfl
  comp_id := by
    intro A B f
    cases f
    rfl
  assoc := by
    intro W X Y Z f g h
    cases f
    cases g
    cases h
    rfl

/-- Regard a categorical morphism as the underlying intrinsic Boolean
homomorphism. -/
abbrev hom {A B : BoolAlg} (f : A ⟶ B) : BooleanAlgebra.Hom A B :=
  f

@[simp] theorem id_apply {A : BoolAlg} (x : A) :
    hom (𝟙 A) x = x :=
  rfl

@[simp] theorem comp_apply {A B C : BoolAlg}
    (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    hom (f ≫ g) x = hom g (hom f x) :=
  rfl

end BoolAlg

end BooleanAlgebrasDoneRight
