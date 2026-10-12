import Mathlib.Tactic.Tauto

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# Classical propositional syntax and derivability

Formulas have arbitrary atoms. A theory is any set of formulas.
Derivations use theory axioms, classical tautologies, and modus ponens.
Tautologies are axiom schemata supplied with proofs of their validity;
the derivability relation itself is inductive, not semantic equivalence.
-/

universe u

namespace BooleanAlgebrasDoneRight.LogicExamples

/-- Propositional formulas over an arbitrary type of atoms. -/
inductive Formula (Atom : Type u)
  | atom : Atom → Formula Atom
  | falsum : Formula Atom
  | verum : Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom
  | disj : Formula Atom → Formula Atom → Formula Atom
  | neg : Formula Atom → Formula Atom

namespace Formula

variable {Atom : Type u}

/-- Material implication. -/
def implies (p q : Formula Atom) : Formula Atom := .disj (.neg p) q

/-- Biconditional, defined using implication and conjunction. -/
def bicond (p q : Formula Atom) : Formula Atom := .conj (implies p q) (implies q p)

/-- Interpret a formula under a truth assignment to its atoms. -/
def eval : Formula Atom → (Atom → Prop) → Prop
  | .atom a, v => v a
  | .falsum, _ => False
  | .verum, _ => True
  | .conj p q, v => eval p v ∧ eval q v
  | .disj p q, v => eval p v ∨ eval q v
  | .neg p, v => ¬ eval p v

@[simp] theorem eval_bicond (p q : Formula Atom) (v : Atom → Prop) :
    eval (bicond p q) v ↔ (eval p v ↔ eval q v) := by
  simp only [bicond, implies, eval]
  tauto

end Formula

variable {Atom : Type u}

/-- A proof from an arbitrary theory, in a classical propositional calculus
with all tautologies as logical axioms and modus ponens as inference rule. -/
inductive Provable (T : Set (Formula Atom)) : Formula Atom → Prop
  | axiom {p : Formula Atom} : p ∈ T → Provable T p
  | tautology {p : Formula Atom} :
      (∀ v : Atom → Prop, p.eval v) → Provable T p
  | mp {p q : Formula Atom} :
      Provable T (p.implies q) → Provable T p → Provable T q

namespace Provable

variable {T : Set (Formula Atom)} {p q r p' q' : Formula Atom}

/-- Derivable formulas hold in every truth assignment satisfying the theory. -/
theorem sound (hp : Provable T p) (v : Atom → Prop)
    (hv : ∀ a ∈ T, Formula.eval a v) : Formula.eval p v := by
  induction hp with
  | axiom h => exact hv _ h
  | tautology h => exact h v
  | mp _hi _hp ih ip =>
    change (¬ _ ∨ _) at ih
    tauto

/-- A provable formula implies any of its tautological consequences. -/
theorem consequence (hp : Provable T p)
    (h : ∀ v : Atom → Prop, p.eval v → q.eval v) : Provable T q := by
  apply mp (p := p)
  · apply tautology
    intro v
    change ¬ p.eval v ∨ q.eval v
    have hv := h v
    tauto
  · exact hp

theorem conj_intro (hp : Provable T p) (hq : Provable T q) :
    Provable T (.conj p q) := by
  have h : Provable T (p.implies (q.implies (.conj p q))) := by
    apply tautology
    intro v
    simp only [Formula.implies, Formula.eval]
    tauto
  exact mp (mp h hp) hq

/-- Provable equivalence relative to the theory. -/
def Equivalent (T : Set (Formula Atom)) (p q : Formula Atom) : Prop :=
  Provable T (p.bicond q)

/-- A tautological biconditional gives provable equivalence. -/
theorem equivalent_of_valid (h : ∀ v : Atom → Prop, p.eval v ↔ q.eval v) :
    Equivalent T p q := by
  apply tautology
  intro v
  exact (Formula.eval_bicond p q v).mpr (h v)

theorem equivalent_refl (p : Formula Atom) : Equivalent T p p :=
  equivalent_of_valid (fun _ => Iff.rfl)

theorem equivalent_symm (h : Equivalent T p q) : Equivalent T q p :=
  consequence h (by
    intro v hv
    exact (Formula.eval_bicond q p v).mpr ((Formula.eval_bicond p q v).mp hv).symm)

theorem equivalent_trans (hpq : Equivalent T p q) (hqr : Equivalent T q r) :
    Equivalent T p r :=
  consequence (conj_intro hpq hqr) (by
    intro v hv
    change Formula.eval (p.bicond q) v ∧ Formula.eval (q.bicond r) v at hv
    exact (Formula.eval_bicond p r v).mpr
      (((Formula.eval_bicond p q v).mp hv.1).trans
        ((Formula.eval_bicond q r v).mp hv.2)))

theorem equivalent_conj (hp : Equivalent T p p') (hq : Equivalent T q q') :
    Equivalent T (.conj p q) (.conj p' q') :=
  consequence (conj_intro hp hq) (by
    intro v hv
    apply (Formula.eval_bicond _ _ v).mpr
    exact and_congr ((Formula.eval_bicond p p' v).mp hv.1)
      ((Formula.eval_bicond q q' v).mp hv.2))

theorem equivalent_disj (hp : Equivalent T p p') (hq : Equivalent T q q') :
    Equivalent T (.disj p q) (.disj p' q') :=
  consequence (conj_intro hp hq) (by
    intro v hv
    apply (Formula.eval_bicond _ _ v).mpr
    exact or_congr ((Formula.eval_bicond p p' v).mp hv.1)
      ((Formula.eval_bicond q q' v).mp hv.2))

theorem equivalent_neg (h : Equivalent T p q) :
    Equivalent T (.neg p) (.neg q) :=
  consequence h (by
    intro v hv
    apply (Formula.eval_bicond _ _ v).mpr
    exact not_congr ((Formula.eval_bicond p q v).mp hv))

/-- The truth class consists exactly of the provable formulas. -/
theorem equivalent_verum_iff (p : Formula Atom) :
    Equivalent T p .verum ↔ Provable T p := by
  constructor
  · intro h
    exact consequence h (fun v hv => ((Formula.eval_bicond p .verum v).mp hv).mpr
      True.intro)
  · intro hp
    exact consequence hp (fun v hv => (Formula.eval_bicond p .verum v).mpr
      ⟨fun _ => True.intro, fun _ => hv⟩)

end Provable

end BooleanAlgebrasDoneRight.LogicExamples
