import Mathlib.Data.SetLike.Basic
import BooleanAlgebrasDoneRight.Hom

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# Boolean subalgebras as substructures

A subalgebra is a subset closed under the entire primitive Boolean signature:
meet, join, complement, zero, and one. Its operations are restrictions of the
ambient operations, and all Boolean identities are inherited.

Thus this is an algebraic substructure definition; no order or lattice
structure is used to specify closure.
-/

universe u

namespace BooleanAlgebrasDoneRight

open BooleanOps

namespace BooleanAlgebra

/-- A substructure of the primitive Boolean signature on `A`. -/
structure Subalgebra (A : Type u) [BooleanAlgebra A] where
  carrier : Set A
  zero_mem' : (zero : A) ∈ carrier
  one_mem' : (one : A) ∈ carrier
  meet_mem' : ∀ {x y : A}, x ∈ carrier → y ∈ carrier → meet x y ∈ carrier
  join_mem' : ∀ {x y : A}, x ∈ carrier → y ∈ carrier → join x y ∈ carrier
  compl_mem' : ∀ {x : A}, x ∈ carrier → compl x ∈ carrier

namespace Subalgebra

variable {A : Type u} [BooleanAlgebra A]

instance : SetLike (Subalgebra A) A where
  coe := carrier
  coe_injective := by
    intro S T h
    cases S
    cases T
    cases h
    rfl

/-- Subalgebras are determined by membership in their carriers. -/
@[ext] theorem ext {S T : Subalgebra A}
    (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp] theorem zero_mem (S : Subalgebra A) : (zero : A) ∈ S :=
  S.zero_mem'

@[simp] theorem one_mem (S : Subalgebra A) : (one : A) ∈ S :=
  S.one_mem'

theorem meet_mem (S : Subalgebra A) {x y : A}
    (hx : x ∈ S) (hy : y ∈ S) : meet x y ∈ S :=
  S.meet_mem' hx hy

theorem join_mem (S : Subalgebra A) {x y : A}
    (hx : x ∈ S) (hy : y ∈ S) : join x y ∈ S :=
  S.join_mem' hx hy

theorem compl_mem (S : Subalgebra A) {x : A}
    (hx : x ∈ S) : compl x ∈ S :=
  S.compl_mem' hx

/-- Restrict the ambient Boolean operations to the substructure. -/
instance booleanAlgebra (S : Subalgebra A) : BooleanAlgebra S where
  meet x y := ⟨meet x.1 y.1, S.meet_mem x.2 y.2⟩
  join x y := ⟨join x.1 y.1, S.join_mem x.2 y.2⟩
  compl x := ⟨compl x.1, S.compl_mem x.2⟩
  zero := ⟨zero, S.zero_mem⟩
  one := ⟨one, S.one_mem⟩
  meet_assoc := by
    intro x y z
    apply Subtype.ext
    exact BooleanAlgebra.meet_assoc x.1 y.1 z.1
  meet_comm := by
    intro x y
    apply Subtype.ext
    exact BooleanAlgebra.meet_comm x.1 y.1
  join_assoc := by
    intro x y z
    apply Subtype.ext
    exact BooleanAlgebra.join_assoc x.1 y.1 z.1
  join_comm := by
    intro x y
    apply Subtype.ext
    exact BooleanAlgebra.join_comm x.1 y.1
  join_absorb_meet := by
    intro x y
    apply Subtype.ext
    exact BooleanAlgebra.join_absorb_meet x.1 y.1
  meet_absorb_join := by
    intro x y
    apply Subtype.ext
    exact BooleanAlgebra.meet_absorb_join x.1 y.1
  meet_distrib_join := by
    intro x y z
    apply Subtype.ext
    exact BooleanAlgebra.meet_distrib_join x.1 y.1 z.1
  join_distrib_meet := by
    intro x y z
    apply Subtype.ext
    exact BooleanAlgebra.join_distrib_meet x.1 y.1 z.1
  join_compl := by
    intro x
    apply Subtype.ext
    exact BooleanAlgebra.join_compl x.1
  meet_compl := by
    intro x
    apply Subtype.ext
    exact BooleanAlgebra.meet_compl x.1

/-- Constants in the signature ensure every subalgebra is nonempty. -/
instance (S : Subalgebra A) : Nonempty S :=
  ⟨⟨zero, S.zero_mem⟩⟩

@[simp] theorem coe_meet (S : Subalgebra A) (x y : S) :
    ((meet x y : S) : A) = meet (x : A) (y : A) := rfl

@[simp] theorem coe_join (S : Subalgebra A) (x y : S) :
    ((join x y : S) : A) = join (x : A) (y : A) := rfl

@[simp] theorem coe_compl (S : Subalgebra A) (x : S) :
    ((compl x : S) : A) = compl (x : A) := rfl

@[simp] theorem coe_zero (S : Subalgebra A) :
    ((zero : S) : A) = (zero : A) := rfl

@[simp] theorem coe_one (S : Subalgebra A) :
    ((one : S) : A) = (one : A) := rfl

/-- The canonical inclusion preserves the entire Boolean signature. -/
def subtype (S : Subalgebra A) : Hom S A where
  toFun := fun x => x.1
  map_zero' := rfl
  map_one' := rfl
  map_join' := by intro x y; rfl
  map_meet' := by intro x y; rfl
  map_compl' := by intro x; rfl

@[simp] theorem subtype_apply (S : Subalgebra A) (x : S) :
    S.subtype x = (x : A) := rfl

theorem subtype_injective (S : Subalgebra A) :
    Function.Injective S.subtype := by
  intro x y h
  exact Subtype.ext h

end Subalgebra

end BooleanAlgebra

end BooleanAlgebrasDoneRight
