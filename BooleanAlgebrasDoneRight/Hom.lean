import BooleanAlgebrasDoneRight.Basic

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# Intrinsic Boolean homomorphisms

A homomorphism of Boolean algebras is a map preserving the entire primitive
Boolean signature: zero, one, join, meet, and complement.

This definition is intrinsic to Boolean algebras.  It does not pass through
lattice homomorphisms or any derived order structure.
-/

universe u v w

namespace BooleanAlgebrasDoneRight

open BooleanOps

namespace BooleanAlgebra

/-- A homomorphism from the Boolean algebra `A` to the Boolean algebra `B`.

The preservation laws are exactly the preservation laws for the primitive
Boolean signature. -/
structure Hom (A : Type u) (B : Type v) [BooleanAlgebra A] [BooleanAlgebra B] where
  toFun : A → B
  map_zero' : toFun (zero : A) = (zero : B)
  map_one' : toFun (one : A) = (one : B)
  map_join' : ∀ x y : A, toFun (join x y) = join (toFun x) (toFun y)
  map_meet' : ∀ x y : A, toFun (meet x y) = meet (toFun x) (toFun y)
  map_compl' : ∀ x : A, toFun (compl x) = compl (toFun x)

instance {A : Type u} {B : Type v} [BooleanAlgebra A] [BooleanAlgebra B] :
    CoeFun (Hom A B) (fun _ => A → B) :=
  ⟨Hom.toFun⟩

/-- Boolean homomorphisms are determined by their underlying functions. -/
@[ext] theorem Hom.ext {A : Type u} {B : Type v}
    [BooleanAlgebra A] [BooleanAlgebra B]
    {f g : Hom A B} (h : f.toFun = g.toFun) :
    f = g := by
  cases f
  cases g
  cases h
  rfl

variable {A : Type u} {B : Type v} {C : Type w}
  [BooleanAlgebra A] [BooleanAlgebra B] [BooleanAlgebra C]

@[simp] theorem Hom.map_zero (f : Hom A B) :
    f (zero : A) = (zero : B) :=
  f.map_zero'

@[simp] theorem Hom.map_one (f : Hom A B) :
    f (one : A) = (one : B) :=
  f.map_one'

@[simp] theorem Hom.map_join (f : Hom A B) (x y : A) :
    f (join x y) = join (f x) (f y) :=
  f.map_join' x y

@[simp] theorem Hom.map_meet (f : Hom A B) (x y : A) :
    f (meet x y) = meet (f x) (f y) :=
  f.map_meet' x y

@[simp] theorem Hom.map_compl (f : Hom A B) (x : A) :
    f (compl x) = compl (f x) :=
  f.map_compl' x

/-- The identity Boolean homomorphism. -/
def Hom.id (A : Type u) [BooleanAlgebra A] : Hom A A where
  toFun := fun x => x
  map_zero' := rfl
  map_one' := rfl
  map_join' := by intro x y; rfl
  map_meet' := by intro x y; rfl
  map_compl' := by intro x; rfl

@[simp] theorem Hom.id_apply (x : A) :
    Hom.id A x = x :=
  rfl

/-- Composition of Boolean homomorphisms. -/
def Hom.comp (g : Hom B C) (f : Hom A B) : Hom A C where
  toFun := fun x => g (f x)
  map_zero' := by simp
  map_one' := by simp
  map_join' := by intro x y; simp
  map_meet' := by intro x y; simp
  map_compl' := by intro x; simp

@[simp] theorem Hom.comp_apply (g : Hom B C) (f : Hom A B) (x : A) :
    g.comp f x = g (f x) :=
  rfl

end BooleanAlgebra

end BooleanAlgebrasDoneRight
