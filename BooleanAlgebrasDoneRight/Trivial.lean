import BooleanAlgebrasDoneRight.Cardinality
import BooleanAlgebrasDoneRight.Iso

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# Trivial Boolean algebras

This file develops the one-element case.  A Boolean algebra is one-element
exactly when its carrier is a subsingleton, equivalently when zero equals one.

The trivial Boolean algebra is terminal among Boolean algebras: every Boolean
algebra admits a unique homomorphism into a subsingleton Boolean algebra.
Any two one-element Boolean algebras are isomorphic.
-/

universe u v

namespace BooleanAlgebrasDoneRight

open BooleanOps

namespace BooleanAlgebra

/-- If zero equals one, every element equals zero. -/
theorem eq_zero_of_zero_eq_one {A : Type u} [BooleanAlgebra A]
    (h : (zero : A) = one) (x : A) :
    x = zero := by
  calc
    x = meet x one := (meet_one x).symm
    _ = meet x zero := by rw [← h]
    _ = zero := meet_zero x

/-- A Boolean algebra has at most one element exactly when zero equals one. -/
theorem subsingleton_iff_zero_eq_one (A : Type u) [BooleanAlgebra A] :
    Subsingleton A ↔ (zero : A) = one := by
  constructor
  · intro h
    exact @Subsingleton.elim A h zero one
  · intro h
    constructor
    intro x y
    exact (eq_zero_of_zero_eq_one h x).trans
      (eq_zero_of_zero_eq_one h y).symm

/-- A one-element Boolean algebra has cardinality one. -/
@[simp] theorem cardinality_eq_one_of_subsingleton
    (A : Type u) [BooleanAlgebra A] [Subsingleton A] :
    cardinality A = 1 := by
  have : Nonempty A := ⟨zero⟩
  exact Cardinal.mk_eq_one A

/-- There is a canonical homomorphism from any Boolean algebra into a
one-element Boolean algebra. -/
def Hom.toSubsingleton (A : Type u) (B : Type v)
    [BooleanAlgebra A] [BooleanAlgebra B] [Subsingleton B] :
    Hom A B where
  toFun := fun _ => zero
  map_zero' := rfl
  map_one' := Subsingleton.elim _ _
  map_join' := by
    intro x y
    exact Subsingleton.elim _ _
  map_meet' := by
    intro x y
    exact Subsingleton.elim _ _
  map_compl' := by
    intro x
    exact Subsingleton.elim _ _

@[simp] theorem Hom.toSubsingleton_apply
    (A : Type u) (B : Type v)
    [BooleanAlgebra A] [BooleanAlgebra B] [Subsingleton B] (x : A) :
    Hom.toSubsingleton A B x = (zero : B) :=
  rfl

/-- The homomorphism into a one-element Boolean algebra is unique. -/
theorem Hom.eq_toSubsingleton
    {A : Type u} {B : Type v}
    [BooleanAlgebra A] [BooleanAlgebra B] [Subsingleton B]
    (f : Hom A B) :
    f = Hom.toSubsingleton A B := by
  apply Hom.ext
  funext x
  exact Subsingleton.elim _ _

/-- A homomorphism from a one-element Boolean algebra can exist only when
the codomain is also one-element. -/
theorem subsingleton_of_hom_from_subsingleton
    {A : Type u} {B : Type v}
    [BooleanAlgebra A] [BooleanAlgebra B] [Subsingleton A]
    (f : Hom A B) :
    Subsingleton B := by
  rw [subsingleton_iff_zero_eq_one]
  calc
    (zero : B) = f (zero : A) := f.map_zero.symm
    _ = f (one : A) := by
      rw [Subsingleton.elim (zero : A) one]
    _ = one := f.map_one

/-- If the domain is one-element, there exists a Boolean homomorphism into
`B` exactly when `B` is one-element. -/
theorem nonempty_hom_from_subsingleton_iff
    (A : Type u) (B : Type v)
    [BooleanAlgebra A] [BooleanAlgebra B] [Subsingleton A] :
    Nonempty (Hom A B) ↔ Subsingleton B := by
  constructor
  · rintro ⟨f⟩
    exact subsingleton_of_hom_from_subsingleton f
  · intro h
    let : Subsingleton B := h
    exact ⟨Hom.toSubsingleton A B⟩

/-- Any two one-element Boolean algebras are isomorphic. -/
def Iso.ofSubsingleton (A : Type u) (B : Type v)
    [BooleanAlgebra A] [BooleanAlgebra B]
    [Subsingleton A] [Subsingleton B] :
    Iso A B where
  toHom := Hom.toSubsingleton A B
  bijective' := by
    constructor
    · intro x y _
      exact Subsingleton.elim x y
    · intro y
      refine ⟨zero, ?_⟩
      exact Subsingleton.elim _ _

/-- Any two one-element Boolean algebras are isomorphic. -/
theorem isomorphic_of_subsingleton
    (A : Type u) (B : Type v)
    [BooleanAlgebra A] [BooleanAlgebra B]
    [Subsingleton A] [Subsingleton B] :
    Isomorphic A B :=
  ⟨Iso.ofSubsingleton A B⟩

end BooleanAlgebra

end BooleanAlgebrasDoneRight
