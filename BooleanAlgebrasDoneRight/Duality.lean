import BooleanAlgebrasDoneRight.Dual

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# The duality principle for Boolean-algebra statements

Terms use variables, zero, one, meet, join, and complement. Statements use
equations, logical connectives, and quantification over algebra elements.
Dualization swaps the algebra operations and constants; logical connectives,
quantifiers, variables, and Boolean complement are unchanged.

Both syntactic dualization operations are involutions. Evaluating a statement
in the dual algebra is equivalent to evaluating its dual in the original
algebra. Hence universal validity is preserved by dualization.
-/

universe u

namespace BooleanAlgebrasDoneRight.BooleanDuality

/-- Terms in the intrinsic Boolean-algebra signature. -/
inductive Term
  | var : ℕ → Term
  | zero : Term
  | one : Term
  | meet : Term → Term → Term
  | join : Term → Term → Term
  | compl : Term → Term

namespace Term

def dual : Term → Term
  | .var x => .var x
  | .zero => .one
  | .one => .zero
  | .meet s t => .join s.dual t.dual
  | .join s t => .meet s.dual t.dual
  | .compl t => .compl t.dual

@[simp] theorem dual_dual (t : Term) : t.dual.dual = t := by
  induction t <;> simp_all [dual]

def eval {A : Type u} [BooleanAlgebra A] : Term → (ℕ → A) → A
  | .var x, env => env x
  | .zero, _ => BooleanOps.zero
  | .one, _ => BooleanOps.one
  | .meet s t, env => BooleanOps.meet (s.eval env) (t.eval env)
  | .join s t, env => BooleanOps.join (s.eval env) (t.eval env)
  | .compl t, env => BooleanOps.compl (t.eval env)

/-- Term evaluation in the dual algebra exchanges exactly the signature
symbols swapped by syntactic dualization. -/
theorem eval_dual {A : Type u} [BooleanAlgebra A] (t : Term) (env : ℕ → A) :
    Dual.ofDual (t.eval (fun x => Dual.toDual (env x))) = t.dual.eval env := by
  induction t <;> simp_all [eval, dual]

end Term

/-- First-order statements in the Boolean-algebra signature. Logical truth
and falsity are distinct from the algebra's constants zero and one. -/
inductive Statement
  | truth : Statement
  | falsity : Statement
  | eq : Term → Term → Statement
  | neg : Statement → Statement
  | conj : Statement → Statement → Statement
  | disj : Statement → Statement → Statement
  | imp : Statement → Statement → Statement
  | iff : Statement → Statement → Statement
  | all : ℕ → Statement → Statement
  | ex : ℕ → Statement → Statement

/-- Assign a value to one variable while preserving the others. -/
def setVar {A : Type u} (env : ℕ → A) (x : ℕ) (a : A) : ℕ → A :=
  fun y => if y = x then a else env y

theorem map_setVar {A : Type u} (env : ℕ → A) (x : ℕ) (a : A) :
    (fun y => Dual.toDual (setVar env x a y)) =
      setVar (fun y => Dual.toDual (env y)) x (Dual.toDual a) := by
  funext y
  by_cases h : y = x <;> simp [setVar, h]

namespace Statement

def dual : Statement → Statement
  | .truth => .truth
  | .falsity => .falsity
  | .eq s t => .eq s.dual t.dual
  | .neg p => .neg p.dual
  | .conj p q => .conj p.dual q.dual
  | .disj p q => .disj p.dual q.dual
  | .imp p q => .imp p.dual q.dual
  | .iff p q => .iff p.dual q.dual
  | .all x p => .all x p.dual
  | .ex x p => .ex x p.dual

@[simp] theorem dual_dual (p : Statement) : p.dual.dual = p := by
  induction p <;> simp_all [dual]

def eval {A : Type u} [BooleanAlgebra A] : Statement → (ℕ → A) → Prop
  | .truth, _ => True
  | .falsity, _ => False
  | .eq s t, env => s.eval env = t.eval env
  | .neg p, env => ¬ p.eval env
  | .conj p q, env => p.eval env ∧ q.eval env
  | .disj p q, env => p.eval env ∨ q.eval env
  | .imp p q, env => p.eval env → q.eval env
  | .iff p q, env => p.eval env ↔ q.eval env
  | .all x p, env => ∀ a, p.eval (setVar env x a)
  | .ex x p, env => ∃ a, p.eval (setVar env x a)

/-- Evaluating a statement in the dual is the same as evaluating the
dual statement in the original algebra. -/
theorem eval_dual {A : Type u} [BooleanAlgebra A] (p : Statement) (env : ℕ → A) :
    p.eval (fun x => Dual.toDual (env x)) ↔ p.dual.eval env := by
  induction p generalizing env with
  | truth => rfl
  | falsity => rfl
  | eq s t =>
    change Dual.ofDual (s.eval (fun x => Dual.toDual (env x))) =
      Dual.ofDual (t.eval (fun x => Dual.toDual (env x))) ↔ _
    rw [Term.eval_dual, Term.eval_dual]
  | neg p ih => exact not_congr (ih env)
  | conj p q ihp ihq => exact and_congr (ihp env) (ihq env)
  | disj p q ihp ihq => exact or_congr (ihp env) (ihq env)
  | imp p q ihp ihq => exact imp_congr (ihp env) (ihq env)
  | iff p q ihp ihq => exact iff_congr (ihp env) (ihq env)
  | all x p ih =>
    constructor
    · intro h a
      apply (ih (setVar env x a)).mp
      simpa only [map_setVar] using h (Dual.toDual a)
    · intro h a
      have h' := (ih (setVar env x (Dual.ofDual a))).mpr (h (Dual.ofDual a))
      simpa only [map_setVar, Dual.toDual_ofDual] using h'
  | ex x p ih =>
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨Dual.ofDual a, (ih (setVar env x (Dual.ofDual a))).mp ?_⟩
      simpa only [map_setVar, Dual.toDual_ofDual] using ha
    · rintro ⟨a, ha⟩
      refine ⟨Dual.toDual a, ?_⟩
      have h' := (ih (setVar env x a)).mpr ha
      simpa only [map_setVar] using h'

/-- Validity for all Boolean algebras and assignments in a fixed universe.
The duality theorem is universe-polymorphic. -/
def Valid (p : Statement) : Prop :=
  ∀ (A : Type u) (hA : BooleanAlgebra A) (env : ℕ → A), @eval A hA p env

/-- The duality principle: a statement valid in every Boolean algebra has a
dual statement valid in every Boolean algebra. -/
theorem Valid.dual {p : Statement} (h : Valid.{u} p) : Valid.{u} p.dual := by
  intro A hA env
  haveI := hA
  exact (eval_dual p env).mp (h (Dual A) inferInstance (fun x => Dual.toDual (env x)))

/-- Universal validity is equivalent to validity of the dual statement. -/
theorem valid_dual_iff (p : Statement) : Valid.{u} p.dual ↔ Valid.{u} p := by
  constructor
  · intro h
    simpa only [dual_dual] using h.dual
  · intro h
    exact h.dual

end Statement

end BooleanAlgebrasDoneRight.BooleanDuality
