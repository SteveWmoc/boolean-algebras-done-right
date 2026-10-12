import Mathlib.ModelTheory.Syntax
import BooleanAlgebrasDoneRight.Logic.Propositional

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# Classical first-order derivability

Mathlib supplies first-order terms and formulas, with bound variables tracked
by de Bruijn indices. Free variables here are natural numbers. A theory is an
arbitrary set of sentences, embedded as formulas without free variables.

The Hilbert calculus has propositional tautology instances, universal
instantiation, universal distribution, vacuous generalization, equality
reflexivity and substitution, modus ponens, and universal generalization.
The last rule is unrestricted because all theory hypotheses are sentences.
Material implication is defined as negation followed by disjunction, matching
the propositional calculus. No semantic-entailment rule is included.
-/

universe u v

namespace BooleanAlgebrasDoneRight.FirstOrderLogic

variable {L : _root_.FirstOrder.Language.{u, v}}

/-- Mathlib first-order formulas with natural-number free variables. -/
abbrev F (L : _root_.FirstOrder.Language.{u, v}) := L.Formula ℕ

/-- Propositional expressions whose atoms are arbitrary first-order formulas. -/
abbrev P (L : _root_.FirstOrder.Language.{u, v}) := LogicExamples.Formula (F L)

def conj (p q : F L) : F L := p ⊓ q
def disj (p q : F L) : F L := p ⊔ q
def neg (p : F L) : F L := p.not
def falsum : F L := ⊥
def verum : F L := ⊤
def implies (p q : F L) : F L := disj (neg p) q
def bicond (p q : F L) : F L := conj (implies p q) (implies q p)

/-- Substitute first-order formulas into a propositional expression. -/
def interpret : P L → F L
  | .atom p => p
  | .falsum => falsum
  | .verum => verum
  | .conj p q => conj (interpret p) (interpret q)
  | .disj p q => disj (interpret p) (interpret q)
  | .neg p => neg (interpret p)

/-- Bind the free variable `x`, using Mathlib's capture-avoiding relabelling. -/
def forallVar (x : ℕ) (p : F L) : F L :=
  (_root_.FirstOrder.Language.BoundedFormula.relabel (β := ℕ) (n := 1)
    (fun y => if y = x then Sum.inr (0 : Fin 1) else Sum.inl y) p).all

/-- Capture-avoiding substitution of a term for one free variable. -/
def substVar (x : ℕ) (t : L.Term ℕ) (p : F L) : F L :=
  p.subst (fun y => if y = x then t else .var y)

/-- Embed a closed theory sentence into the formula type. -/
def sentenceAsFormula (p : L.Sentence) : F L :=
  _root_.FirstOrder.Language.Formula.relabel Empty.elim p

/-- Derivability from a theory of sentences in classical predicate calculus
with equality. Quantifier axioms use capture-avoiding term substitution. -/
inductive Provable (T : L.Theory) : F L → Prop
  | hypothesis (p : L.Sentence) : p ∈ T → Provable T (sentenceAsFormula p)
  | propositional (p : P L) :
      (∀ w : F L → Prop, p.eval w) → Provable T (interpret p)
  | universalInst (x : ℕ) (p : F L) (t : L.Term ℕ) :
      Provable T (implies (forallVar x p) (substVar x t p))
  | universalDist (x : ℕ) (p q : F L) :
      Provable T (implies (forallVar x (implies p q))
        (implies (forallVar x p) (forallVar x q)))
  | universalVacuous (x : ℕ) (p : F L) :
      x ∉ p.freeVarFinset → Provable T (implies p (forallVar x p))
  | equalityRefl (t : L.Term ℕ) : Provable T (t.equal t)
  | equalitySubst (x : ℕ) (p : F L) (t s : L.Term ℕ) :
      Provable T (implies (t.equal s)
        (implies (substVar x t p) (substVar x s p)))
  | mp {p q : F L} : Provable T (implies p q) → Provable T p → Provable T q
  | generalize (x : ℕ) {p : F L} : Provable T p → Provable T (forallVar x p)

namespace Provable

variable {T : L.Theory} {p q r p' q' : F L}

/-- Lift a propositional derivation after substituting first-order formulas. -/
theorem lift {S : Set (P L)} {a : P L} (ha : LogicExamples.Provable S a)
    (hS : ∀ b ∈ S, Provable T (interpret b)) : Provable T (interpret a) := by
  induction ha with
  | hypothesis h => exact hS _ h
  | tautology h => exact propositional _ h
  | mp _h₁ _h₂ ih₁ ih₂ => exact mp ih₁ ih₂

/-- Propositional premises whose interpretations are already provable. -/
def propTheory (T : L.Theory) : Set (P L) := {a | Provable T (interpret a)}

theorem fromProp {a : P L} (ha : LogicExamples.Provable (propTheory T) a) :
    Provable T (interpret a) :=
  lift ha (fun _ h => h)

/-- Provable first-order biconditional equivalence. -/
def Equivalent (T : L.Theory) (p q : F L) : Prop := Provable T (bicond p q)

/-- Propositional tautological equivalences remain provable for arbitrary
first-order formulas, including quantified ones. -/
theorem equivalent_of_valid (a b : P L)
    (h : ∀ w : F L → Prop, a.eval w ↔ b.eval w) :
    Equivalent T (interpret a) (interpret b) :=
  fromProp (LogicExamples.Provable.equivalent_of_valid h)

theorem equivalent_refl (p : F L) : Equivalent T p p :=
  fromProp (LogicExamples.Provable.equivalent_refl (.atom p))

theorem equivalent_symm (h : Equivalent T p q) : Equivalent T q p := by
  have h' : LogicExamples.Provable.Equivalent (propTheory T) (.atom p) (.atom q) :=
    .hypothesis h
  exact fromProp (LogicExamples.Provable.equivalent_symm h')

theorem equivalent_trans (h₁ : Equivalent T p q) (h₂ : Equivalent T q r) :
    Equivalent T p r := by
  have h₁' : LogicExamples.Provable.Equivalent (propTheory T) (.atom p) (.atom q) :=
    .hypothesis h₁
  have h₂' : LogicExamples.Provable.Equivalent (propTheory T) (.atom q) (.atom r) :=
    .hypothesis h₂
  exact fromProp (LogicExamples.Provable.equivalent_trans h₁' h₂')

theorem equivalent_conj (hp : Equivalent T p p') (hq : Equivalent T q q') :
    Equivalent T (conj p q) (conj p' q') := by
  have hp' : LogicExamples.Provable.Equivalent (propTheory T) (.atom p) (.atom p') :=
    .hypothesis hp
  have hq' : LogicExamples.Provable.Equivalent (propTheory T) (.atom q) (.atom q') :=
    .hypothesis hq
  exact fromProp (LogicExamples.Provable.equivalent_conj hp' hq')

theorem equivalent_disj (hp : Equivalent T p p') (hq : Equivalent T q q') :
    Equivalent T (disj p q) (disj p' q') := by
  have hp' : LogicExamples.Provable.Equivalent (propTheory T) (.atom p) (.atom p') :=
    .hypothesis hp
  have hq' : LogicExamples.Provable.Equivalent (propTheory T) (.atom q) (.atom q') :=
    .hypothesis hq
  exact fromProp (LogicExamples.Provable.equivalent_disj hp' hq')

theorem equivalent_neg (h : Equivalent T p q) :
    Equivalent T (neg p) (neg q) := by
  have h' : LogicExamples.Provable.Equivalent (propTheory T) (.atom p) (.atom q) :=
    .hypothesis h
  exact fromProp (LogicExamples.Provable.equivalent_neg h')

theorem conj_intro (hp : Provable T p) (hq : Provable T q) :
    Provable T (conj p q) := by
  have hp' : LogicExamples.Provable (propTheory T) (.atom p) := .hypothesis hp
  have hq' : LogicExamples.Provable (propTheory T) (.atom q) := .hypothesis hq
  exact fromProp (LogicExamples.Provable.conj_intro hp' hq')

theorem implies_of_equivalent (h : Equivalent T p q) : Provable T (implies p q) := by
  have h' : LogicExamples.Provable.Equivalent (propTheory T) (.atom p) (.atom q) :=
    .hypothesis h
  apply fromProp (a := (LogicExamples.Formula.atom p).implies (.atom q))
  apply LogicExamples.Provable.consequence h'
  intro w hw
  simp only [LogicExamples.Formula.eval_bicond] at hw
  simp only [LogicExamples.Formula.implies, LogicExamples.Formula.eval]
  tauto

/-- Universal quantification preserves provable equivalence. -/
theorem equivalent_forall (x : ℕ) (h : Equivalent T p q) :
    Equivalent T (forallVar x p) (forallVar x q) := by
  have hpq := mp (universalDist x p q) (generalize x (implies_of_equivalent h))
  have hqp := mp (universalDist x q p)
    (generalize x (implies_of_equivalent (equivalent_symm h)))
  exact conj_intro hpq hqp

/-- Universal instantiation is an actual derivable inference. -/
theorem forall_elim (x : ℕ) (t : L.Term ℕ) (hp : Provable T (forallVar x p)) :
    Provable T (substVar x t p) :=
  mp (universalInst x p t) hp

theorem equivalent_verum_iff (p : F L) :
    Equivalent T p verum ↔ Provable T p := by
  constructor
  · intro h
    have h' : LogicExamples.Provable.Equivalent (propTheory T) (.atom p) .verum :=
      .hypothesis h
    exact fromProp ((LogicExamples.Provable.equivalent_verum_iff (.atom p)).mp h')
  · intro hp
    have hp' : LogicExamples.Provable (propTheory T) (.atom p) := .hypothesis hp
    exact fromProp ((LogicExamples.Provable.equivalent_verum_iff (.atom p)).mpr hp')

end Provable

end BooleanAlgebrasDoneRight.FirstOrderLogic
