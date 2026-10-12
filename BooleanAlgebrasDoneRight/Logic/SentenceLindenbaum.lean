import BooleanAlgebrasDoneRight.Logic.VariableSubalgebra
import BooleanAlgebrasDoneRight.Iso

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# The sentence Lindenbaum–Tarski algebra

A sentence is a formula with no free variables. We represent sentences as
closed formulas in the same natural-number variable syntax as `FormulaAlgebra`.
The Lindenbaum–Tarski algebra of `T` is their quotient by provable equivalence.

Its canonical map into the formula algebra identifies it, as a Boolean
algebra, with the subalgebra of classes admitting a closed representative:
`variableSubalgebra T ∅`. Other representatives may have free variables.
-/

universe u v

namespace BooleanAlgebrasDoneRight.FirstOrderLogic

variable {L : _root_.FirstOrder.Language.{u, v}}

/-- Sentences represented by formulas with an empty free-variable set. -/
abbrev ClosedFormula (L : _root_.FirstOrder.Language.{u, v}) :=
  {p : F L // p.freeVarFinset = ∅}

namespace ClosedFormula

def conj (p q : ClosedFormula L) : ClosedFormula L :=
  ⟨FirstOrderLogic.conj p.1 q.1, by simp [p.2, q.2]⟩

def disj (p q : ClosedFormula L) : ClosedFormula L :=
  ⟨FirstOrderLogic.disj p.1 q.1, by simp [p.2, q.2]⟩

def neg (p : ClosedFormula L) : ClosedFormula L :=
  ⟨FirstOrderLogic.neg p.1, by simp [p.2]⟩

def falsum : ClosedFormula L := ⟨FirstOrderLogic.falsum, freeVars_falsum⟩
def verum : ClosedFormula L := ⟨FirstOrderLogic.verum, freeVars_verum⟩

end ClosedFormula

/-- Provable equivalence restricted to sentences. -/
def sentenceSetoid (T : L.Theory) : Setoid (ClosedFormula L) where
  r p q := Provable.Equivalent T p.1 q.1
  iseqv := ⟨fun p => Provable.equivalent_refl p.1,
    fun h => Provable.equivalent_symm h,
    fun h₁ h₂ => Provable.equivalent_trans h₁ h₂⟩

/-- The Lindenbaum–Tarski algebra of `T`: sentences modulo provable
biconditional equivalence. -/
def LindenbaumAlgebra (T : L.Theory) : Type max u v :=
  Quotient (sentenceSetoid T)

namespace LindenbaumAlgebra

variable (T : L.Theory)

def classOf (p : ClosedFormula L) : LindenbaumAlgebra T :=
  Quotient.mk (sentenceSetoid T) p

@[simp] theorem classOf_eq_iff (p q : ClosedFormula L) :
    classOf T p = classOf T q ↔ Provable T (p.1.iff q.1) := by
  constructor
  · intro h
    exact (Provable.equivalent_iff_provable_iff p.1 q.1).mp (Quotient.exact h)
  · intro h
    exact Quotient.sound (s := sentenceSetoid T)
      ((Provable.equivalent_iff_provable_iff p.1 q.1).mpr h)

/-- The canonical map from sentence classes to the closed-variable subalgebra. -/
def toClosedSubalgebra (a : LindenbaumAlgebra T) : VariableAlgebra T ∅ :=
  Quotient.liftOn a
    (fun p => ⟨FormulaAlgebra.classOf T p.1, p.1, by simp [p.2], rfl⟩)
    (by
      intro p q h
      apply Subtype.ext
      exact Quotient.sound (s := formulaSetoid T) h)

theorem toClosedSubalgebra_injective :
    Function.Injective (toClosedSubalgebra T) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro p q h
  apply Quotient.sound (s := sentenceSetoid T)
  exact Quotient.exact (s := formulaSetoid T) (congrArg Subtype.val h)

theorem toClosedSubalgebra_surjective :
    Function.Surjective (toClosedSubalgebra T) := by
  intro a
  obtain ⟨p, hp, ha⟩ := a.2
  have hclosed : p.freeVarFinset = ∅ := Finset.subset_empty.mp hp
  refine ⟨classOf T ⟨p, hclosed⟩, ?_⟩
  apply Subtype.ext
  exact ha

instance booleanOps : BooleanOps (LindenbaumAlgebra T) where
  meet a b := Quotient.liftOn₂ a b (fun p q => classOf T (ClosedFormula.conj p q))
    (fun _ _ _ _ hp hq => Quotient.sound (s := sentenceSetoid T)
      (Provable.equivalent_conj hp hq))
  join a b := Quotient.liftOn₂ a b (fun p q => classOf T (ClosedFormula.disj p q))
    (fun _ _ _ _ hp hq => Quotient.sound (s := sentenceSetoid T)
      (Provable.equivalent_disj hp hq))
  compl a := Quotient.liftOn a (fun p => classOf T (ClosedFormula.neg p))
    (fun _ _ h => Quotient.sound (s := sentenceSetoid T) (Provable.equivalent_neg h))
  zero := classOf T ClosedFormula.falsum
  one := classOf T ClosedFormula.verum

open BooleanOps

@[simp] theorem toClosedSubalgebra_meet (a b : LindenbaumAlgebra T) :
    toClosedSubalgebra T (meet a b) =
      meet (toClosedSubalgebra T a) (toClosedSubalgebra T b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  rfl

@[simp] theorem toClosedSubalgebra_join (a b : LindenbaumAlgebra T) :
    toClosedSubalgebra T (join a b) =
      join (toClosedSubalgebra T a) (toClosedSubalgebra T b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  rfl

@[simp] theorem toClosedSubalgebra_compl (a : LindenbaumAlgebra T) :
    toClosedSubalgebra T (compl a) = compl (toClosedSubalgebra T a) := by
  refine Quotient.inductionOn a ?_
  intro p
  rfl

@[simp] theorem toClosedSubalgebra_zero :
    toClosedSubalgebra T (zero : LindenbaumAlgebra T) = zero := rfl

@[simp] theorem toClosedSubalgebra_one :
    toClosedSubalgebra T (one : LindenbaumAlgebra T) = one := rfl

/-- The Boolean identities are reflected by the injective inclusion into the
empty-variable subalgebra. -/
instance booleanAlgebra : BooleanAlgebra (LindenbaumAlgebra T) where
  toBooleanOps := inferInstance
  meet_assoc := by
    intro a b c
    apply toClosedSubalgebra_injective T
    simp only [toClosedSubalgebra_meet]
    exact BooleanAlgebra.meet_assoc (toClosedSubalgebra T a) (toClosedSubalgebra T b) (toClosedSubalgebra T c)
  meet_comm := by
    intro a b
    apply toClosedSubalgebra_injective T
    simp only [toClosedSubalgebra_meet]
    exact BooleanAlgebra.meet_comm (toClosedSubalgebra T a) (toClosedSubalgebra T b)
  join_assoc := by
    intro a b c
    apply toClosedSubalgebra_injective T
    simp only [toClosedSubalgebra_join]
    exact BooleanAlgebra.join_assoc (toClosedSubalgebra T a) (toClosedSubalgebra T b) (toClosedSubalgebra T c)
  join_comm := by
    intro a b
    apply toClosedSubalgebra_injective T
    simp only [toClosedSubalgebra_join]
    exact BooleanAlgebra.join_comm (toClosedSubalgebra T a) (toClosedSubalgebra T b)
  join_absorb_meet := by
    intro a b
    apply toClosedSubalgebra_injective T
    simp only [toClosedSubalgebra_meet, toClosedSubalgebra_join]
    exact BooleanAlgebra.join_absorb_meet (toClosedSubalgebra T a) (toClosedSubalgebra T b)
  meet_absorb_join := by
    intro a b
    apply toClosedSubalgebra_injective T
    simp only [toClosedSubalgebra_meet, toClosedSubalgebra_join]
    exact BooleanAlgebra.meet_absorb_join (toClosedSubalgebra T a) (toClosedSubalgebra T b)
  meet_distrib_join := by
    intro a b c
    apply toClosedSubalgebra_injective T
    simp only [toClosedSubalgebra_meet, toClosedSubalgebra_join]
    exact BooleanAlgebra.meet_distrib_join (toClosedSubalgebra T a) (toClosedSubalgebra T b) (toClosedSubalgebra T c)
  join_distrib_meet := by
    intro a b c
    apply toClosedSubalgebra_injective T
    simp only [toClosedSubalgebra_meet, toClosedSubalgebra_join]
    exact BooleanAlgebra.join_distrib_meet (toClosedSubalgebra T a) (toClosedSubalgebra T b) (toClosedSubalgebra T c)
  join_compl := by
    intro a
    apply toClosedSubalgebra_injective T
    simp only [toClosedSubalgebra_join, toClosedSubalgebra_compl, toClosedSubalgebra_one]
    exact BooleanAlgebra.join_compl (toClosedSubalgebra T a)
  meet_compl := by
    intro a
    apply toClosedSubalgebra_injective T
    simp only [toClosedSubalgebra_meet, toClosedSubalgebra_compl, toClosedSubalgebra_zero]
    exact BooleanAlgebra.meet_compl (toClosedSubalgebra T a)

/-- The sentence quotient is isomorphic to the empty-variable subalgebra. -/
def closedSubalgebraIso :
    BooleanAlgebra.Iso (LindenbaumAlgebra T) (VariableAlgebra T ∅) where
  toHom :=
    { toFun := toClosedSubalgebra T
      map_zero' := toClosedSubalgebra_zero T
      map_one' := toClosedSubalgebra_one T
      map_join' := toClosedSubalgebra_join T
      map_meet' := toClosedSubalgebra_meet T
      map_compl' := toClosedSubalgebra_compl T }
  bijective' := ⟨toClosedSubalgebra_injective T, toClosedSubalgebra_surjective T⟩

/-- The canonical injective inclusion into the larger formula algebra. -/
def inclusion : BooleanAlgebra.Hom (LindenbaumAlgebra T) (FormulaAlgebra T) :=
  (variableSubalgebra T ∅).subtype.comp (closedSubalgebraIso T).toHom

theorem inclusion_injective : Function.Injective (inclusion T) :=
  (variableSubalgebra T ∅).subtype_injective.comp (closedSubalgebraIso T).injective

@[simp] theorem inclusion_classOf (p : ClosedFormula L) :
    inclusion T (classOf T p) = FormulaAlgebra.classOf T p.1 := rfl

theorem mem_range_inclusion_iff (a : FormulaAlgebra T) :
    a ∈ Set.range (inclusion T) ↔ a ∈ variableSubalgebra T ∅ := by
  constructor
  · rintro ⟨b, rfl⟩
    exact (toClosedSubalgebra T b).2
  · intro ha
    obtain ⟨b, hb⟩ := toClosedSubalgebra_surjective T ⟨a, ha⟩
    exact ⟨b, congrArg Subtype.val hb⟩

theorem classOf_eq_one_iff (p : ClosedFormula L) :
    classOf T p = one ↔ Provable T p.1 := by
  constructor
  · intro h
    have h' := congrArg (inclusion T) h
    exact (FormulaAlgebra.classOf_eq_one_iff T p.1).mp h'
  · intro h
    apply inclusion_injective T
    exact (FormulaAlgebra.classOf_eq_one_iff T p.1).mpr h

theorem subsingleton_iff_provable_falsum :
    Subsingleton (LindenbaumAlgebra T) ↔ Provable T FirstOrderLogic.falsum := by
  rw [BooleanAlgebra.subsingleton_iff_zero_eq_one]
  exact classOf_eq_one_iff T ClosedFormula.falsum

end LindenbaumAlgebra

end BooleanAlgebrasDoneRight.FirstOrderLogic
