import BooleanAlgebrasDoneRight.Logic.Propositional
import BooleanAlgebrasDoneRight.Trivial

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# The propositional Lindenbaum–Tarski algebra

For any theory `T`, quotient formulas by `T ⊢ p ↔ q`. Congruence of
provable equivalence makes conjunction, disjunction, and negation
well-defined on classes. Classical tautologies establish all ten Boolean
identities.

No consistency assumption is needed. The quotient is trivial exactly when
the theory proves falsity. The first-order calculus is a separate extension;
this module formalizes the classical propositional case.
-/

universe u

namespace BooleanAlgebrasDoneRight.LogicExamples

variable {Atom : Type u}

/-- Provable equivalence is an equivalence relation. -/
def lindenbaumSetoid (T : Set (Formula Atom)) : Setoid (Formula Atom) where
  r := Provable.Equivalent T
  iseqv := ⟨Provable.equivalent_refl, fun h => Provable.equivalent_symm h,
    fun h₁ h₂ => Provable.equivalent_trans h₁ h₂⟩

/-- Formulas modulo provable equivalence relative to an arbitrary theory. -/
def LindenbaumAlgebra (T : Set (Formula Atom)) : Type u :=
  Quotient (lindenbaumSetoid T)

namespace LindenbaumAlgebra

variable (T : Set (Formula Atom))

/-- The class of a formula. -/
def classOf (p : Formula Atom) : LindenbaumAlgebra T :=
  Quotient.mk (lindenbaumSetoid T) p

@[simp] theorem classOf_eq_iff (p q : Formula Atom) :
    classOf T p = classOf T q ↔ Provable.Equivalent T p q :=
  ⟨Quotient.exact, Quotient.sound⟩

instance booleanOps : BooleanOps (LindenbaumAlgebra T) where
  meet x y := Quotient.liftOn₂ x y (fun p q => classOf T (.conj p q))
    (fun _ _ _ _ hp hq => Quotient.sound (Provable.equivalent_conj hp hq))
  join x y := Quotient.liftOn₂ x y (fun p q => classOf T (.disj p q))
    (fun _ _ _ _ hp hq => Quotient.sound (Provable.equivalent_disj hp hq))
  compl x := Quotient.liftOn x (fun p => classOf T (.neg p))
    (fun _ _ h => Quotient.sound (Provable.equivalent_neg h))
  zero := classOf T .falsum
  one := classOf T .verum

/-- Classical propositional derivability supplies a Boolean algebra on the
quotient; the operations do not depend on representative choices. -/
instance booleanAlgebra : BooleanAlgebra (LindenbaumAlgebra T) where
  toBooleanOps := inferInstance
  meet_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro p q r
    apply Quotient.sound
    apply Provable.equivalent_of_valid
    intro v
    simp only [Formula.eval]
    tauto
  meet_comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro p q
    apply Quotient.sound
    apply Provable.equivalent_of_valid
    intro v
    simp only [Formula.eval]
    tauto
  join_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro p q r
    apply Quotient.sound
    apply Provable.equivalent_of_valid
    intro v
    simp only [Formula.eval]
    tauto
  join_comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro p q
    apply Quotient.sound
    apply Provable.equivalent_of_valid
    intro v
    simp only [Formula.eval]
    tauto
  join_absorb_meet := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro p q
    apply Quotient.sound
    apply Provable.equivalent_of_valid
    intro v
    simp only [Formula.eval]
    tauto
  meet_absorb_join := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro p q
    apply Quotient.sound
    apply Provable.equivalent_of_valid
    intro v
    simp only [Formula.eval]
    tauto
  meet_distrib_join := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro p q r
    apply Quotient.sound
    apply Provable.equivalent_of_valid
    intro v
    simp only [Formula.eval]
    tauto
  join_distrib_meet := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro p q r
    apply Quotient.sound
    apply Provable.equivalent_of_valid
    intro v
    simp only [Formula.eval]
    tauto
  join_compl := by
    intro x
    refine Quotient.inductionOn x ?_
    intro p
    apply Quotient.sound
    apply Provable.equivalent_of_valid
    intro v
    simp only [Formula.eval]
    tauto
  meet_compl := by
    intro x
    refine Quotient.inductionOn x ?_
    intro p
    apply Quotient.sound
    apply Provable.equivalent_of_valid
    intro v
    simp only [Formula.eval]
    tauto

open BooleanOps

@[simp] theorem classOf_conj (p q : Formula Atom) :
    classOf T (.conj p q) = meet (classOf T p) (classOf T q) := rfl

@[simp] theorem classOf_disj (p q : Formula Atom) :
    classOf T (.disj p q) = join (classOf T p) (classOf T q) := rfl

@[simp] theorem classOf_neg (p : Formula Atom) :
    classOf T (.neg p) = compl (classOf T p) := rfl

@[simp] theorem classOf_falsum : classOf T .falsum = zero := rfl

@[simp] theorem classOf_verum : classOf T .verum = one := rfl

/-- A formula represents truth exactly when it is provable from the theory. -/
theorem classOf_eq_one_iff (p : Formula Atom) :
    classOf T p = one ↔ Provable T p :=
  (classOf_eq_iff T p .verum).trans (Provable.equivalent_verum_iff p)

/-- Inconsistent theories give exactly the one-element Boolean algebra. -/
theorem subsingleton_iff_provable_falsum :
    Subsingleton (LindenbaumAlgebra T) ↔ Provable T .falsum := by
  rw [BooleanAlgebra.subsingleton_iff_zero_eq_one]
  exact classOf_eq_one_iff T .falsum

end LindenbaumAlgebra

end BooleanAlgebrasDoneRight.LogicExamples
