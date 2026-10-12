import Mathlib.SetTheory.Cardinal.Arithmetic
import BooleanAlgebrasDoneRight.Cardinality
import BooleanAlgebrasDoneRight.Examples.FiniteCofinite

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# Cardinality of the finite-cofinite algebra

For infinite `X`, the finite-cofinite algebra has cardinality `#X`.
Singletons give the lower bound. Finite subsets and their relative
complements give a surjection from two copies of `Finset X`, giving the
upper bound. Consequently every infinite cardinal is the cardinality of
a Boolean algebra.
-/

universe u

namespace BooleanAlgebrasDoneRight

open BooleanOps

namespace SetExamples

variable {α : Type u}

/-- Regard a finite subset of `X` as an element of its finite-cofinite
algebra. -/
def finiteCofiniteSingleton (X : Set α) (x : X) : FiniteCofiniteAlgebra X :=
  ⟨⟨{x.1}, by
    intro y hy
    have h : y = x.1 := Set.mem_singleton_iff.mp hy
    exact h ▸ x.2⟩,
    ⟨by
      intro y hy
      have h : y = x.1 := Set.mem_singleton_iff.mp hy
      exact h ▸ x.2,
      Or.inl (Set.finite_singleton x.1)⟩⟩

/-- Distinct points give distinct singleton elements. -/
theorem finiteCofiniteSingleton_injective (X : Set α) :
    Function.Injective (finiteCofiniteSingleton X) := by
  intro x y h
  apply Subtype.ext
  apply Set.singleton_injective
  exact congrArg (fun a : FiniteCofiniteAlgebra X => a.1.1) h

/-- Embed a finset of points of `X` as a finite subset of `X`. -/
def finiteCofiniteOfFinset (X : Set α) (t : Finset X) :
    FiniteCofiniteAlgebra X :=
  ⟨⟨Subtype.val '' (t : Set X), by
    rintro y ⟨x, _, rfl⟩
    exact x.2⟩,
    ⟨by
      rintro y ⟨x, _, rfl⟩
      exact x.2,
      Or.inl (t.finite_toSet.image Subtype.val)⟩⟩

private theorem exists_finset_image {X s : Set α} (hs : s ⊆ X)
    (hf : s.Finite) :
    ∃ t : Finset X, Subtype.val '' (t : Set X) = s := by
  obtain ⟨t, ht⟩ :=
    (hf.preimage (f := fun x : X => x.1) Subtype.val_injective.injOn).exists_finset_coe
  refine ⟨t, ?_⟩
  rw [ht]
  apply Set.ext
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hs hx⟩, hx, rfl⟩

/-- Enumerate finite subsets and their relative complements. -/
def finiteCofiniteFromSum (X : Set α) :
    Finset X ⊕ Finset X → FiniteCofiniteAlgebra X
  | .inl t => finiteCofiniteOfFinset X t
  | .inr t => compl (finiteCofiniteOfFinset X t)

/-- Every element is a finite subset or the complement of a finite subset. -/
theorem finiteCofiniteFromSum_surjective (X : Set α) :
    Function.Surjective (finiteCofiniteFromSum X) := by
  intro a
  rcases (mem_finiteCofiniteSetAlgebra X a.1).mp a.2 with hf | hf
  · obtain ⟨t, ht⟩ := exists_finset_image a.1.2 hf
    refine ⟨.inl t, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact ht
  · obtain ⟨t, ht⟩ :=
      exists_finset_image (fun _ hx => hx.1) hf
    refine ⟨.inr t, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change X \ (Subtype.val '' (t : Set X)) = a.1.1
    rw [ht]
    apply Set.ext
    intro x
    constructor
    · intro hx
      by_cases hxs : x ∈ a.1.1
      · exact hxs
      · exact (hx.2 ⟨hx.1, hxs⟩).elim
    · intro hx
      exact ⟨a.1.2 hx, fun h => h.2 hx⟩

/-- The finite-cofinite Boolean algebra of an infinite set has the same
cardinality as the set itself. -/
theorem finiteCofinite_cardinality {X : Set α} (hX : X.Infinite) :
    BooleanAlgebra.cardinality (FiniteCofiniteAlgebra X) = Cardinal.mk X := by
  have : Infinite X := Set.infinite_coe_iff.mpr hX
  change Cardinal.mk (FiniteCofiniteAlgebra X) = Cardinal.mk X
  apply le_antisymm
  · calc
      Cardinal.mk (FiniteCofiniteAlgebra X) ≤
          Cardinal.mk (Finset X ⊕ Finset X) :=
        Cardinal.mk_le_of_surjective (finiteCofiniteFromSum_surjective X)
      _ = Cardinal.mk X := by
        simp only [Cardinal.mk_sum, Cardinal.lift_id,
          Cardinal.mk_finset_of_infinite, Cardinal.add_mk_eq_self]
  · exact Cardinal.mk_le_of_injective (finiteCofiniteSingleton_injective X)

/-- Explicit cardinal-parameter form of the result. -/
theorem finiteCofinite_cardinality_eq {X : Set α} (hX : X.Infinite)
    {κ : Cardinal.{u}} (hκ : Cardinal.mk X = κ) :
    BooleanAlgebra.cardinality (FiniteCofiniteAlgebra X) = κ :=
  (finiteCofinite_cardinality hX).trans hκ

end SetExamples

namespace BooleanAlgebra

/-- Every infinite cardinal is realized by a Boolean algebra, namely the
finite-cofinite algebra on a representative type of that cardinal. -/
theorem exists_of_infinite_cardinality (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ) :
    ∃ (A : Type u) (hA : BooleanAlgebra A), @cardinality A hA = κ := by
  have : Infinite κ.out := Cardinal.aleph0_le_mk_iff.mp (by simpa using hκ)
  refine ⟨SetExamples.FiniteCofiniteAlgebra (Set.univ : Set κ.out),
    inferInstance, ?_⟩
  rw [SetExamples.finiteCofinite_cardinality Set.infinite_univ,
    Cardinal.mk_univ, Cardinal.mk_out]

end BooleanAlgebra

end BooleanAlgebrasDoneRight
