import Mathlib.Topology.Clopen
import BooleanAlgebrasDoneRight.Examples.SetAlgebra

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# The Boolean algebra of clopen sets

For any topological space `X`, its clopen subsets form a subalgebra of
the power set algebra on `X`. The empty set and whole space are clopen,
and clopen sets are closed under binary intersection, binary union, and
complement.

No separation, compactness, or nonemptiness assumptions are needed.
-/

universe u

namespace BooleanAlgebrasDoneRight

open BooleanOps

namespace SetExamples

/-- The family of subsets that are both closed and open. -/
def clopenFamily (X : Type u) [TopologicalSpace X] : Set (Set X) :=
  {s | IsClopen s}

@[simp] theorem mem_clopenFamily (X : Type u) [TopologicalSpace X] (s : Set X) :
    s ∈ clopenFamily X ↔ IsClopen s := Iff.rfl

/-- The clopen subsets form an algebra of subsets of the whole space. -/
theorem isSetAlgebra_clopenFamily (X : Type u) [TopologicalSpace X] :
    IsSetAlgebra (Set.univ : Set X) (clopenFamily X) where
  subset_mem := fun _ => Set.subset_univ _
  empty_mem := isClopen_empty
  space_mem := isClopen_univ
  inter_mem := fun hs ht => hs.inter ht
  union_mem := fun hs ht => hs.union ht
  compl_mem := by
    intro s hs
    change IsClopen ((Set.univ : Set X) \ s)
    have h : (Set.univ : Set X) \ s = sᶜ := by
      ext x
      simp
    rw [h]
    exact hs.compl

/-- The clopen subalgebra of the power set algebra on `X`. -/
def clopenSetAlgebra (X : Type u) [TopologicalSpace X] :
    SetAlgebra (Set.univ : Set X) :=
  SetAlgebra.ofFamily (clopenFamily X) (isSetAlgebra_clopenFamily X)

/-- The carrier of the Boolean algebra of clopen subsets. -/
abbrev ClopenAlgebra (X : Type u) [TopologicalSpace X] : Type u :=
  clopenSetAlgebra X

/-- The clopen algebra inherits all Boolean identities from the power set
algebra. -/
instance clopenBooleanAlgebra (X : Type u) [TopologicalSpace X] :
    BooleanAlgebra (ClopenAlgebra X) :=
  BooleanAlgebra.Subalgebra.booleanAlgebra (clopenSetAlgebra X)

@[simp] theorem mem_clopenSetAlgebra (X : Type u) [TopologicalSpace X]
    (s : PowerSetAlgebra (Set.univ : Set X)) :
    s ∈ clopenSetAlgebra X ↔ IsClopen (s : Set X) := Iff.rfl

@[simp] theorem toFamily_clopenSetAlgebra (X : Type u) [TopologicalSpace X] :
    (clopenSetAlgebra X).toFamily = clopenFamily X :=
  SetAlgebra.toFamily_ofFamily _ _

/-- The carrier is equivalent to the usual subtype of clopen subsets,
without the redundant proof that every subset lies in the whole space. -/
def clopenEquiv (X : Type u) [TopologicalSpace X] :
    ClopenAlgebra X ≃ {s : Set X // IsClopen s} where
  toFun a := ⟨a.1.1, a.2⟩
  invFun s := ⟨⟨s.1, Set.subset_univ _⟩, s.2⟩
  left_inv _a := Subtype.ext (Subtype.ext rfl)
  right_inv _s := Subtype.ext rfl

@[simp] theorem clopen_val_meet (X : Type u) [TopologicalSpace X]
    (a b : ClopenAlgebra X) :
    (meet a b).1.1 = a.1.1 ∩ b.1.1 := rfl

@[simp] theorem clopen_val_join (X : Type u) [TopologicalSpace X]
    (a b : ClopenAlgebra X) :
    (join a b).1.1 = a.1.1 ∪ b.1.1 := rfl

@[simp] theorem clopen_val_compl (X : Type u) [TopologicalSpace X]
    (a : ClopenAlgebra X) :
    (compl a).1.1 = a.1.1ᶜ := by
  change Set.univ \ a.1.1 = a.1.1ᶜ
  ext x
  simp

@[simp] theorem clopen_val_zero (X : Type u) [TopologicalSpace X] :
    (zero : ClopenAlgebra X).1.1 = ∅ := rfl

@[simp] theorem clopen_val_one (X : Type u) [TopologicalSpace X] :
    (one : ClopenAlgebra X).1.1 = Set.univ := rfl

end SetExamples

end BooleanAlgebrasDoneRight
