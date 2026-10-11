import Mathlib.SetTheory.Cardinal.Order
import BooleanAlgebrasDoneRight.Cardinality
import BooleanAlgebrasDoneRight.Examples.Set

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# The two-element Boolean algebra

If `X = {x}` is a singleton, then its power set algebra has exactly two
elements, namely `∅` and `{x}`.  The canonical two-element Boolean algebra
`Two` is obtained by taking a singleton subset of `Unit`.

The primitive Boolean operations therefore admit the familiar truth tables on
the two values `zero` and `one`.
-/

universe u

namespace BooleanAlgebrasDoneRight

open BooleanOps

namespace SetExamples

variable {α : Type u}

/-- The power set algebra of a singleton. -/
abbrev SingletonPowerSetAlgebra (x : α) : Type u :=
  PowerSetAlgebra ({x} : Set α)

/-- Every element of the power set algebra of a singleton is either zero or
one. -/
theorem singletonPowerSet_eq_zero_or_eq_one (x : α)
    (a : SingletonPowerSetAlgebra x) :
    a = zero ∨ a = one := by
  by_cases hx : x ∈ (a : Set α)
  · right
    apply Subtype.ext
    ext y
    change y ∈ (a : Set α) ↔ y ∈ ({x} : Set α)
    constructor
    · intro hy
      exact a.2 hy
    · intro hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact hx
  · left
    apply Subtype.ext
    ext y
    change y ∈ (a : Set α) ↔ y ∈ (∅ : Set α)
    constructor
    · intro hy
      have hyx : y = x := Set.mem_singleton_iff.mp (a.2 hy)
      subst y
      exact (hx hy).elim
    · intro hy
      exact False.elim hy

/-- In the power set algebra of a singleton, zero and one are distinct. -/
theorem singletonPowerSet_zero_ne_one (x : α) :
    (zero : SingletonPowerSetAlgebra x) ≠ one := by
  intro h
  have hsets := congrArg
    (fun a : SingletonPowerSetAlgebra x => (a : Set α)) h
  have hx : x ∈ ({x} : Set α) := by simp
  rw [val_zero, val_one] at hsets
  have : x ∈ (∅ : Set α) := by
    rw [hsets]
    exact hx
  simpa using this

/-- The power set algebra of a singleton is equivalent, as a type, to
`Bool`. -/
noncomputable def singletonPowerSetEquivBool (x : α) :
    SingletonPowerSetAlgebra x ≃ Bool where
  toFun a := if a = (zero : SingletonPowerSetAlgebra x) then false else true
  invFun b := match b with
    | false => zero
    | true => one
  left_inv a := by
    rcases singletonPowerSet_eq_zero_or_eq_one x a with h | h
    · subst a
      simp
    · subst a
      simp [singletonPowerSet_zero_ne_one x]
  right_inv b := by
    cases b <;> simp [singletonPowerSet_zero_ne_one x]

/-- The power set algebra of a singleton has cardinality two. -/
@[simp] theorem singletonPowerSet_cardinality (x : α) :
    BooleanAlgebra.cardinality (SingletonPowerSetAlgebra x) = 2 := by
  calc
    BooleanAlgebra.cardinality (SingletonPowerSetAlgebra x) =
        Cardinal.mk (SingletonPowerSetAlgebra x) := rfl
    _ = Cardinal.mk Bool := (singletonPowerSetEquivBool x).cardinal_eq
    _ = 2 := Cardinal.mk_bool

/-- The canonical two-element Boolean algebra, denoted `Two`. -/
abbrev Two : Type :=
  SingletonPowerSetAlgebra (α := Unit) ()

/-- Every element of `Two` is either zero or one. -/
theorem two_eq_zero_or_eq_one (a : Two) :
    a = zero ∨ a = one :=
  singletonPowerSet_eq_zero_or_eq_one () a

/-- The two elements of `Two` are distinct. -/
theorem two_zero_ne_one : (zero : Two) ≠ one :=
  singletonPowerSet_zero_ne_one ()

/-- The Boolean algebra `Two` has cardinality two. -/
@[simp] theorem two_cardinality :
    BooleanAlgebra.cardinality Two = 2 :=
  singletonPowerSet_cardinality ()

/-- Truth table for join on the two-element Boolean algebra:
`0 + 0 = 0`, `0 + 1 = 1`, `1 + 0 = 1`, `1 + 1 = 1`. -/
theorem two_join_truth_table :
    join (zero : Two) zero = zero ∧
    join (zero : Two) one = one ∧
    join (one : Two) zero = one ∧
    join (one : Two) one = one := by
  simp

/-- Truth table for meet on the two-element Boolean algebra:
`0 · 0 = 0`, `0 · 1 = 0`, `1 · 0 = 0`, `1 · 1 = 1`. -/
theorem two_meet_truth_table :
    meet (zero : Two) zero = zero ∧
    meet (zero : Two) one = zero ∧
    meet (one : Two) zero = zero ∧
    meet (one : Two) one = one := by
  simp

/-- Truth table for complement on the two-element Boolean algebra:
`-0 = 1` and `-1 = 0`. -/
theorem two_compl_truth_table :
    compl (zero : Two) = one ∧
    compl (one : Two) = zero := by
  simp

end SetExamples

end BooleanAlgebrasDoneRight
