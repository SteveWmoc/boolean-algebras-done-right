import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Tactic.Tauto
import BooleanAlgebrasDoneRight.Basic

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# Boolean algebras of sets

The first concrete example is the power set algebra.  If `X` is a set, its
power set `𝒫 X` is made into a Boolean algebra by union, intersection,
relative complement in `X`, the empty set, and `X` itself.
-/

universe u

namespace BooleanAlgebrasDoneRight

open BooleanOps

namespace SetExamples

variable {α : Type u}

/-- The carrier of the power set algebra on `X`: the type of subsets of `X`. -/
abbrev PowerSetAlgebra (X : Set α) : Type u :=
  ↥(Set.powerset X)

private def psMeet {X : Set α}
    (a b : PowerSetAlgebra X) : PowerSetAlgebra X :=
  ⟨a.1 ∩ b.1, by
    intro x hx
    exact a.2 hx.1⟩

private def psJoin {X : Set α}
    (a b : PowerSetAlgebra X) : PowerSetAlgebra X :=
  ⟨a.1 ∪ b.1, by
    intro x hx
    rcases hx with hx | hx
    · exact a.2 hx
    · exact b.2 hx⟩

private def psCompl {X : Set α}
    (a : PowerSetAlgebra X) : PowerSetAlgebra X :=
  ⟨X \ a.1, by
    intro x hx
    exact hx.1⟩

private def psZero (X : Set α) : PowerSetAlgebra X :=
  ⟨∅, by
    intro x hx
    exact False.elim hx⟩

private def psOne (X : Set α) : PowerSetAlgebra X :=
  ⟨X, by
    intro x hx
    exact hx⟩

/-- The power set `𝒫 X`, with union, intersection, relative complement,
`∅`, and `X`, is a Boolean algebra. -/
instance powerSetBooleanAlgebra (X : Set α) :
    BooleanAlgebra (PowerSetAlgebra X) where
  meet := psMeet
  join := psJoin
  compl := psCompl
  zero := psZero X
  one := psOne X
  meet_assoc := by
    intro a b c
    apply Subtype.ext
    ext x
    simp [psMeet, and_assoc]
  meet_comm := by
    intro a b
    apply Subtype.ext
    ext x
    simp [psMeet, and_comm]
  join_assoc := by
    intro a b c
    apply Subtype.ext
    ext x
    simp [psJoin, or_assoc]
  join_comm := by
    intro a b
    apply Subtype.ext
    ext x
    simp [psJoin, or_comm]
  join_absorb_meet := by
    intro a b
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx
      · exact hx.1
    · intro hx
      exact Or.inl hx
  meet_absorb_join := by
    intro a b
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, Or.inl hx⟩
  meet_distrib_join := by
    intro a b c
    apply Subtype.ext
    ext x
    simp only [psMeet, psJoin, Set.mem_inter_iff, Set.mem_union]
    tauto
  join_distrib_meet := by
    intro a b c
    apply Subtype.ext
    ext x
    simp only [psJoin, psMeet, Set.mem_union, Set.mem_inter_iff]
    tauto
  join_compl := by
    intro a
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact a.2 hx
      · exact hx.1
    · intro hx
      by_cases ha : x ∈ a.1
      · exact Or.inl ha
      · exact Or.inr ⟨hx, ha⟩
  meet_compl := by
    intro a
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      exact (hx.2.2 hx.1).elim
    · intro hx
      exact False.elim hx

@[simp] theorem val_meet {X : Set α} (a b : PowerSetAlgebra X) :
    ((meet a b : PowerSetAlgebra X) : Set α) = a.1 ∩ b.1 :=
  rfl

@[simp] theorem val_join {X : Set α} (a b : PowerSetAlgebra X) :
    ((join a b : PowerSetAlgebra X) : Set α) = a.1 ∪ b.1 :=
  rfl

@[simp] theorem val_compl {X : Set α} (a : PowerSetAlgebra X) :
    ((compl a : PowerSetAlgebra X) : Set α) = X \ a.1 :=
  rfl

@[simp] theorem val_zero (X : Set α) :
    ((zero : PowerSetAlgebra X) : Set α) = ∅ :=
  rfl

@[simp] theorem val_one (X : Set α) :
    ((one : PowerSetAlgebra X) : Set α) = X :=
  rfl

end SetExamples

end BooleanAlgebrasDoneRight
