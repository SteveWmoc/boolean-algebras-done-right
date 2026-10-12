import BooleanAlgebrasDoneRight.Logic.FirstOrderLindenbaum
import BooleanAlgebrasDoneRight.Subalgebra

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# Subalgebras with a fixed finite set of free variables

For a finite set `V` of variable names, take the classes that have a
representative whose free variables lie in `V`. This is a Boolean subalgebra
of the first-order Lindenbaum algebra.

The existential representative condition is essential: provably equivalent
formulas need not have identical syntactic free-variable sets. Membership
therefore does not require every representative to use only variables in `V`.

Negation adds no free variables, while conjunction and disjunction take the
union of their operands' free variables. The constants have none. Enlarging
`V` enlarges the subalgebra, and every class belongs to one such subalgebra.
-/

universe u v

namespace BooleanAlgebrasDoneRight.FirstOrderLogic

variable {L : _root_.FirstOrder.Language.{u, v}}

@[simp] theorem freeVars_falsum :
    (falsum : F L).freeVarFinset = ∅ := rfl

@[simp] theorem freeVars_verum :
    (verum : F L).freeVarFinset = ∅ := by
  change (∅ : Finset ℕ) ∪ ∅ = ∅
  simp

@[simp] theorem freeVars_neg (p : F L) :
    (neg p).freeVarFinset = p.freeVarFinset := by
  change p.freeVarFinset ∪ ∅ = p.freeVarFinset
  simp

@[simp] theorem freeVars_conj (p q : F L) :
    (conj p q).freeVarFinset = p.freeVarFinset ∪ q.freeVarFinset := by
  change (p.freeVarFinset ∪ (q.freeVarFinset ∪ ∅)) ∪ ∅ =
    p.freeVarFinset ∪ q.freeVarFinset
  simp

@[simp] theorem freeVars_disj (p q : F L) :
    (disj p q).freeVarFinset = p.freeVarFinset ∪ q.freeVarFinset := by
  change (p.freeVarFinset ∪ ∅) ∪ q.freeVarFinset =
    p.freeVarFinset ∪ q.freeVarFinset
  simp

/-- Classes admitting a representative with all free variables in `V`. -/
def variableSubalgebra (T : L.Theory) (V : Finset ℕ) :
    BooleanAlgebra.Subalgebra (LindenbaumAlgebra T) where
  carrier := {a | ∃ p : F L,
    p.freeVarFinset ⊆ V ∧ LindenbaumAlgebra.classOf T p = a}
  zero_mem' := ⟨falsum, by simp, rfl⟩
  one_mem' := ⟨verum, by simp, rfl⟩
  meet_mem' := by
    rintro a b ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    refine ⟨conj p q, ?_, LindenbaumAlgebra.classOf_conj T p q⟩
    rw [freeVars_conj]
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hp hx
    · exact hq hx
  join_mem' := by
    rintro a b ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    refine ⟨disj p q, ?_, LindenbaumAlgebra.classOf_disj T p q⟩
    rw [freeVars_disj]
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hp hx
    · exact hq hx
  compl_mem' := by
    rintro a ⟨p, hp, rfl⟩
    refine ⟨neg p, ?_, LindenbaumAlgebra.classOf_neg T p⟩
    simpa only [freeVars_neg] using hp

@[simp] theorem mem_variableSubalgebra (T : L.Theory) (V : Finset ℕ)
    (a : LindenbaumAlgebra T) :
    a ∈ variableSubalgebra T V ↔
      ∃ p : F L, p.freeVarFinset ⊆ V ∧ LindenbaumAlgebra.classOf T p = a :=
  Iff.rfl

/-- A formula's class belongs iff it is provably equivalent to a representative
whose free variables lie in `V`. -/
theorem classOf_mem_variableSubalgebra_iff (T : L.Theory) (V : Finset ℕ) (p : F L) :
    LindenbaumAlgebra.classOf T p ∈ variableSubalgebra T V ↔
      ∃ q : F L, q.freeVarFinset ⊆ V ∧ Provable T (q.iff p) := by
  simp only [mem_variableSubalgebra, LindenbaumAlgebra.classOf_eq_iff_provable_iff]

theorem classOf_mem_variableSubalgebra (T : L.Theory) (V : Finset ℕ)
    (p : F L) (hp : p.freeVarFinset ⊆ V) :
    LindenbaumAlgebra.classOf T p ∈ variableSubalgebra T V :=
  ⟨p, hp, rfl⟩

/-- The carrier inherits the Boolean algebra and its injective inclusion. -/
abbrev VariableAlgebra (T : L.Theory) (V : Finset ℕ) : Type max u v :=
  variableSubalgebra T V

instance variableBooleanAlgebra (T : L.Theory) (V : Finset ℕ) :
    BooleanAlgebra (VariableAlgebra T V) :=
  BooleanAlgebra.Subalgebra.booleanAlgebra (variableSubalgebra T V)

/-- Increasing the allowed variables increases the carrier subset. -/
theorem variableSubalgebra_mono (T : L.Theory) {V W : Finset ℕ} (hVW : V ⊆ W) :
    (variableSubalgebra T V : Set (LindenbaumAlgebra T)) ⊆
      (variableSubalgebra T W : Set (LindenbaumAlgebra T)) := by
  rintro a ⟨p, hp, ha⟩
  exact ⟨p, fun x hx => hVW (hp hx), ha⟩

/-- Every formula uses finitely many free variables, so these subalgebras cover
the entire first-order Lindenbaum algebra. -/
theorem exists_variableSubalgebra_mem (T : L.Theory) (a : LindenbaumAlgebra T) :
    ∃ V : Finset ℕ, a ∈ variableSubalgebra T V := by
  refine Quotient.inductionOn a ?_
  intro p
  exact ⟨p.freeVarFinset, p, fun _ h => h, rfl⟩

end BooleanAlgebrasDoneRight.FirstOrderLogic
