import BooleanAlgebrasDoneRight.Logic.FirstOrder
import BooleanAlgebrasDoneRight.Trivial

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# The first-order Lindenbaum–Tarski algebra

For any first-order language and theory of sentences, quotient all formulas
with natural-number free variables by provable biconditional equivalence.
Boolean operations descend to the quotient. Universal quantification also
descends, by congruence derived from generalization and universal distribution.

This construction uses the inductive predicate calculus in `FirstOrder.lean`.
It does not identify provability with semantic consequence or invoke a
completeness theorem. No consistency assumption is required.
-/

universe u v

namespace BooleanAlgebrasDoneRight.FirstOrderLogic

variable {L : _root_.FirstOrder.Language.{u, v}}

def lindenbaumSetoid (T : L.Theory) : Setoid (F L) where
  r := Provable.Equivalent T
  iseqv := ⟨Provable.equivalent_refl, fun h => Provable.equivalent_symm h,
    fun h₁ h₂ => Provable.equivalent_trans h₁ h₂⟩

/-- First-order formulas modulo provable equivalence relative to `T`. -/
def LindenbaumAlgebra (T : L.Theory) : Type max u v :=
  Quotient (lindenbaumSetoid T)

namespace LindenbaumAlgebra

variable (T : L.Theory)

def classOf (p : F L) : LindenbaumAlgebra T :=
  Quotient.mk (lindenbaumSetoid T) p

@[simp] theorem classOf_eq_iff (p q : F L) :
    classOf T p = classOf T q ↔ Provable.Equivalent T p q := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound (s := lindenbaumSetoid T) h

/-- Class equality is exactly provability of Mathlib's first-order biconditional. -/
theorem classOf_eq_iff_provable_iff (p q : F L) :
    classOf T p = classOf T q ↔ Provable T (p.iff q) :=
  (classOf_eq_iff T p q).trans (Provable.equivalent_iff_provable_iff p q)

instance booleanOps : BooleanOps (LindenbaumAlgebra T) where
  meet x y := Quotient.liftOn₂ x y (fun p q => classOf T (conj p q))
    (fun _ _ _ _ hp hq => Quotient.sound (Provable.equivalent_conj hp hq))
  join x y := Quotient.liftOn₂ x y (fun p q => classOf T (disj p q))
    (fun _ _ _ _ hp hq => Quotient.sound (Provable.equivalent_disj hp hq))
  compl x := Quotient.liftOn x (fun p => classOf T (neg p))
    (fun _ _ h => Quotient.sound (Provable.equivalent_neg h))
  zero := classOf T falsum
  one := classOf T verum

instance booleanAlgebra : BooleanAlgebra (LindenbaumAlgebra T) where
  toBooleanOps := inferInstance
  meet_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro p q r
    apply Quotient.sound
    apply Provable.equivalent_of_valid (.conj (.conj (.atom p) (.atom q)) (.atom r)) (.conj (.atom p) (.conj (.atom q) (.atom r)))
    intro w
    simp only [LogicExamples.Formula.eval]
    tauto
  meet_comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro p q
    apply Quotient.sound
    apply Provable.equivalent_of_valid (.conj (.atom p) (.atom q)) (.conj (.atom q) (.atom p))
    intro w
    simp only [LogicExamples.Formula.eval]
    tauto
  join_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro p q r
    apply Quotient.sound
    apply Provable.equivalent_of_valid (.disj (.disj (.atom p) (.atom q)) (.atom r)) (.disj (.atom p) (.disj (.atom q) (.atom r)))
    intro w
    simp only [LogicExamples.Formula.eval]
    tauto
  join_comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro p q
    apply Quotient.sound
    apply Provable.equivalent_of_valid (.disj (.atom p) (.atom q)) (.disj (.atom q) (.atom p))
    intro w
    simp only [LogicExamples.Formula.eval]
    tauto
  join_absorb_meet := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro p q
    apply Quotient.sound
    apply Provable.equivalent_of_valid (.disj (.atom p) (.conj (.atom p) (.atom q))) (.atom p)
    intro w
    simp only [LogicExamples.Formula.eval]
    tauto
  meet_absorb_join := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro p q
    apply Quotient.sound
    apply Provable.equivalent_of_valid (.conj (.atom p) (.disj (.atom p) (.atom q))) (.atom p)
    intro w
    simp only [LogicExamples.Formula.eval]
    tauto
  meet_distrib_join := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro p q r
    apply Quotient.sound
    apply Provable.equivalent_of_valid (.conj (.atom p) (.disj (.atom q) (.atom r))) (.disj (.conj (.atom p) (.atom q)) (.conj (.atom p) (.atom r)))
    intro w
    simp only [LogicExamples.Formula.eval]
    tauto
  join_distrib_meet := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro p q r
    apply Quotient.sound
    apply Provable.equivalent_of_valid (.disj (.atom p) (.conj (.atom q) (.atom r))) (.conj (.disj (.atom p) (.atom q)) (.disj (.atom p) (.atom r)))
    intro w
    simp only [LogicExamples.Formula.eval]
    tauto
  join_compl := by
    intro x
    refine Quotient.inductionOn x ?_
    intro p
    apply Quotient.sound
    apply Provable.equivalent_of_valid (.disj (.atom p) (.neg (.atom p))) .verum
    intro w
    simp only [LogicExamples.Formula.eval]
    tauto
  meet_compl := by
    intro x
    refine Quotient.inductionOn x ?_
    intro p
    apply Quotient.sound
    apply Provable.equivalent_of_valid (.conj (.atom p) (.neg (.atom p))) .falsum
    intro w
    simp only [LogicExamples.Formula.eval]
    tauto

open BooleanOps

@[simp] theorem classOf_conj (p q : F L) :
    classOf T (conj p q) = meet (classOf T p) (classOf T q) := rfl

@[simp] theorem classOf_disj (p q : F L) :
    classOf T (disj p q) = join (classOf T p) (classOf T q) := rfl

@[simp] theorem classOf_neg (p : F L) :
    classOf T (neg p) = compl (classOf T p) := rfl

@[simp] theorem classOf_falsum : classOf T falsum = zero := rfl
@[simp] theorem classOf_verum : classOf T verum = one := rfl

theorem classOf_eq_one_iff (p : F L) :
    classOf T p = one ↔ Provable T p :=
  (classOf_eq_iff T p verum).trans (Provable.equivalent_verum_iff p)

/-- Every theory sentence represents truth in its Lindenbaum algebra. -/
theorem classOf_sentence_eq_one {p : L.Sentence} (hp : p ∈ T) :
    classOf T (sentenceAsFormula p) = one :=
  (classOf_eq_one_iff T _).mpr (Provable.hypothesis p hp)

theorem subsingleton_iff_provable_falsum :
    Subsingleton (LindenbaumAlgebra T) ↔ Provable T falsum := by
  rw [BooleanAlgebra.subsingleton_iff_zero_eq_one]
  exact classOf_eq_one_iff T falsum

/-- Universal quantification is independent of the chosen representative. -/
def all (x : ℕ) (a : LindenbaumAlgebra T) : LindenbaumAlgebra T :=
  Quotient.liftOn a (fun p => classOf T (forallVar x p))
    (fun _ _ h => Quotient.sound (Provable.equivalent_forall x h))

@[simp] theorem classOf_forall (x : ℕ) (p : F L) :
    classOf T (forallVar x p) = all T x (classOf T p) := rfl

end LindenbaumAlgebra

end BooleanAlgebrasDoneRight.FirstOrderLogic
