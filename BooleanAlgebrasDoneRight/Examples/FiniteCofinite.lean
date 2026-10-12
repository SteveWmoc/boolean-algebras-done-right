import Mathlib.Data.Set.Finite.Basic
import BooleanAlgebrasDoneRight.Examples.SetAlgebra

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# The finite-cofinite algebra

The finite-cofinite family on `X` consists of subsets `s ⊆ X` for which
either `s` or its relative complement `X \ s` is finite. It is an algebra
of subsets of `X`, and hence a Boolean subalgebra of the power set algebra.

This construction works for every `X`, including finite and empty sets.
When `X` is finite, the family is the entire power set.
-/

universe u

namespace BooleanAlgebrasDoneRight

namespace SetExamples

variable {α : Type u}

/-- The family of finite or relatively cofinite subsets of `X`. -/
def finiteCofiniteFamily (X : Set α) : Set (Set α) :=
  {s | s ⊆ X ∧ (s.Finite ∨ (X \ s).Finite)}

@[simp] theorem mem_finiteCofiniteFamily (X s : Set α) :
    s ∈ finiteCofiniteFamily X ↔ s ⊆ X ∧ (s.Finite ∨ (X \ s).Finite) :=
  Iff.rfl

/-- Finite and relatively cofinite subsets form an algebra of subsets. -/
theorem isSetAlgebra_finiteCofiniteFamily (X : Set α) :
    IsSetAlgebra X (finiteCofiniteFamily X) where
  subset_mem := fun hs => hs.1
  empty_mem := ⟨Set.empty_subset X, Or.inl Set.finite_empty⟩
  space_mem := ⟨Set.Subset.refl X, Or.inr (by simp)⟩
  inter_mem := by
    rintro s t ⟨hsX, hs⟩ ⟨htX, ht⟩
    refine ⟨fun x hx => hsX hx.1, ?_⟩
    rcases hs with hs | hs
    · exact Or.inl (hs.inter_of_left t)
    · rcases ht with ht | ht
      · exact Or.inl (ht.inter_of_right s)
      · right
        apply (hs.union ht).subset
        intro x hx
        by_cases hxs : x ∈ s
        · exact Or.inr ⟨hx.1, fun hxt => hx.2 ⟨hxs, hxt⟩⟩
        · exact Or.inl ⟨hx.1, hxs⟩
  union_mem := by
    rintro s t ⟨hsX, hs⟩ ⟨htX, ht⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact hsX hx
      · exact htX hx
    · rcases hs with hs | hs
      · rcases ht with ht | ht
        · exact Or.inl (hs.union ht)
        · right
          apply ht.subset
          intro x hx
          exact ⟨hx.1, fun hxt => hx.2 (Or.inr hxt)⟩
      · right
        apply hs.subset
        intro x hx
        exact ⟨hx.1, fun hxs => hx.2 (Or.inl hxs)⟩
  compl_mem := by
    rintro s ⟨_, hs⟩
    refine ⟨fun _ hx => hx.1, ?_⟩
    rcases hs with hs | hs
    · right
      apply hs.subset
      intro x hx
      by_cases hxs : x ∈ s
      · exact hxs
      · exact (hx.2 ⟨hx.1, hxs⟩).elim
    · exact Or.inl hs

/-- The finite-cofinite subalgebra of the power set algebra on `X`. -/
def finiteCofiniteSetAlgebra (X : Set α) : SetAlgebra X :=
  SetAlgebra.ofFamily (finiteCofiniteFamily X)
    (isSetAlgebra_finiteCofiniteFamily X)

/-- The carrier of the finite-cofinite Boolean algebra on `X`.

Its Boolean algebra instance is inherited from the power set subalgebra:
union, intersection, relative complement, the empty set, and `X`. -/
abbrev FiniteCofiniteAlgebra (X : Set α) : Type u :=
  finiteCofiniteSetAlgebra X

/-- The finite-cofinite algebra inherits all Boolean identities. -/
instance finiteCofiniteBooleanAlgebra (X : Set α) :
    BooleanAlgebra (FiniteCofiniteAlgebra X) :=
  BooleanAlgebra.Subalgebra.booleanAlgebra (finiteCofiniteSetAlgebra X)

@[simp] theorem mem_finiteCofiniteSetAlgebra (X : Set α)
    (s : PowerSetAlgebra X) :
    s ∈ finiteCofiniteSetAlgebra X ↔
      (s : Set α).Finite ∨ (X \ (s : Set α)).Finite := by
  change (s.1 ⊆ X ∧ (s.1.Finite ∨ (X \ s.1).Finite)) ↔ _
  exact and_iff_right s.2

/-- The family recovered from the subalgebra is exactly the finite-cofinite
family. -/
@[simp] theorem toFamily_finiteCofiniteSetAlgebra (X : Set α) :
    (finiteCofiniteSetAlgebra X).toFamily = finiteCofiniteFamily X :=
  SetAlgebra.toFamily_ofFamily _ _

/-- If `X` is finite, every subset is finite, so the family is the full
power set. This also covers `X = ∅`. -/
theorem finiteCofiniteFamily_eq_powerset {X : Set α} (hX : X.Finite) :
    finiteCofiniteFamily X = Set.powerset X := by
  apply Set.ext
  intro s
  constructor
  · intro hs
    exact hs.1
  · intro hs
    exact ⟨hs, Or.inl (hX.subset hs)⟩

end SetExamples

end BooleanAlgebrasDoneRight
