import BooleanAlgebrasDoneRight.Subalgebra
import BooleanAlgebrasDoneRight.Examples.Set

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# Algebras of subsets of a set

An algebra of subsets of `X` is a Boolean subalgebra of `PowerSetAlgebra X`.
It can equivalently be specified by a family of subsets of `X` containing
the empty set and `X`, and closed under binary intersection, binary union,
and complement relative to `X`.

Only finite Boolean operations are required. No closure under countable
unions or arbitrary unions is assumed.
-/

universe u

namespace BooleanAlgebrasDoneRight

open BooleanOps

namespace SetExamples

variable {α : Type u}

/-- An algebra of subsets of `X`, presented as an algebraic substructure. -/
abbrev SetAlgebra (X : Set α) :=
  BooleanAlgebra.Subalgebra (PowerSetAlgebra X)

/-- The concrete closure conditions for a family to be an algebra of subsets
of `X`. Complements are taken relative to `X`. -/
structure IsSetAlgebra (X : Set α) (F : Set (Set α)) : Prop where
  subset_mem : ∀ {s : Set α}, s ∈ F → s ⊆ X
  empty_mem : ∅ ∈ F
  space_mem : X ∈ F
  inter_mem : ∀ {s t : Set α}, s ∈ F → t ∈ F → s ∩ t ∈ F
  union_mem : ∀ {s t : Set α}, s ∈ F → t ∈ F → s ∪ t ∈ F
  compl_mem : ∀ {s : Set α}, s ∈ F → X \ s ∈ F

namespace SetAlgebra

variable {X : Set α}

/-- Construct the subalgebra from a family satisfying the concrete closure
conditions. -/
def ofFamily (F : Set (Set α)) (hF : IsSetAlgebra X F) : SetAlgebra X where
  carrier := {a | (a : Set α) ∈ F}
  zero_mem' := hF.empty_mem
  one_mem' := hF.space_mem
  meet_mem' := by
    intro a b ha hb
    exact hF.inter_mem ha hb
  join_mem' := by
    intro a b ha hb
    exact hF.union_mem ha hb
  compl_mem' := by
    intro a ha
    exact hF.compl_mem ha

@[simp] theorem mem_ofFamily (F : Set (Set α)) (hF : IsSetAlgebra X F)
    (a : PowerSetAlgebra X) :
    a ∈ ofFamily F hF ↔ (a : Set α) ∈ F := Iff.rfl

/-- Forget the subset proofs to obtain the underlying family of sets. -/
def toFamily (S : SetAlgebra X) : Set (Set α) :=
  {s | ∃ a : PowerSetAlgebra X, a ∈ S ∧ (a : Set α) = s}

/-- Membership in the family agrees with membership in the subalgebra. -/
@[simp] theorem mem_toFamily (S : SetAlgebra X) (a : PowerSetAlgebra X) :
    (a : Set α) ∈ S.toFamily ↔ a ∈ S := by
  constructor
  · rintro ⟨b, hb, hba⟩
    have h : b = a := Subtype.ext hba
    exact h ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- Every Boolean subalgebra of the power set gives an algebra of subsets. -/
theorem isSetAlgebra_toFamily (S : SetAlgebra X) :
    IsSetAlgebra X S.toFamily where
  subset_mem := by
    rintro s ⟨a, _, ha⟩
    rw [← ha]
    exact a.2
  empty_mem := ⟨zero, S.zero_mem, rfl⟩
  space_mem := ⟨one, S.one_mem, rfl⟩
  inter_mem := by
    rintro s t ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨meet a b, S.meet_mem ha hb, rfl⟩
  union_mem := by
    rintro s t ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨join a b, S.join_mem ha hb, rfl⟩
  compl_mem := by
    rintro s ⟨a, ha, rfl⟩
    exact ⟨compl a, S.compl_mem ha, rfl⟩

/-- Constructing a subalgebra and forgetting subset proofs recovers exactly
the original family. -/
@[simp] theorem toFamily_ofFamily (F : Set (Set α)) (hF : IsSetAlgebra X F) :
    (ofFamily F hF).toFamily = F := by
  apply Set.ext
  intro s
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hs
    exact ⟨⟨s, hF.subset_mem hs⟩, hs, rfl⟩

/-- Forgetting subset proofs and reconstructing recovers the subalgebra. -/
@[simp] theorem ofFamily_toFamily (S : SetAlgebra X) :
    ofFamily S.toFamily S.isSetAlgebra_toFamily = S := by
  apply BooleanAlgebra.Subalgebra.ext
  intro a
  exact S.mem_toFamily a

/-- The two presentations are equivalent: subalgebras of the power set
algebra and families satisfying the concrete closure conditions. -/
def equivFamilies (X : Set α) :
    SetAlgebra X ≃ {F : Set (Set α) // IsSetAlgebra X F} where
  toFun S := ⟨S.toFamily, S.isSetAlgebra_toFamily⟩
  invFun F := ofFamily F.1 F.2
  left_inv := ofFamily_toFamily
  right_inv F := by
    apply Subtype.ext
    exact toFamily_ofFamily F.1 F.2

end SetAlgebra

end SetExamples

end BooleanAlgebrasDoneRight
