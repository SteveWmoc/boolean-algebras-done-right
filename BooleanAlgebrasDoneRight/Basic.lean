import BooleanAlgebrasDoneRight.Signature

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# Boolean algebras: algebraic axioms and elementary identities

A Boolean algebra is presented here as a finitary algebraic structure, not as
an ordered or lattice-theoretic structure.  Its primitive signature consists
of two binary operations, one unary operation, and two constants.

The laws are ten equations: associativity and commutativity of both binary
operations, the two absorption laws, the two distributive laws, and the two
complementation laws.  Idempotence, neutral and absorbing laws for the
constants, uniqueness and involutivity of complement, and De Morgan's laws are
derived below.

No order relation or lattice structure is assumed in this file.
-/

universe u

namespace BooleanAlgebrasDoneRight

open BooleanOps

/-- A Boolean algebra in the algebra-first presentation.

The primitive data are supplied by `BooleanOps`.  The ten fields below are
purely equational laws in that signature; in particular, no order or lattice
structure occurs in the definition. -/
class BooleanAlgebra (α : Type u) extends BooleanOps α where
  meet_assoc : ∀ x y z : α, meet (meet x y) z = meet x (meet y z)
  meet_comm : ∀ x y : α, meet x y = meet y x
  join_assoc : ∀ x y z : α, join (join x y) z = join x (join y z)
  join_comm : ∀ x y : α, join x y = join y x
  join_absorb_meet : ∀ x y : α, join x (meet x y) = x
  meet_absorb_join : ∀ x y : α, meet x (join x y) = x
  meet_distrib_join : ∀ x y z : α,
    meet x (join y z) = join (meet x y) (meet x z)
  join_distrib_meet : ∀ x y z : α,
    join x (meet y z) = meet (join x y) (join x z)
  join_compl : ∀ x : α, join x (compl x) = one
  meet_compl : ∀ x : α, meet x (compl x) = zero

namespace BooleanAlgebra

variable {α : Type u} [BooleanAlgebra α]

/-- Join is idempotent; this is derived from the absorption laws. -/
@[simp] theorem join_idem (x : α) : join x x = x := by
  calc
    join x x = join x (meet x (join x x)) := by
      rw [BooleanAlgebra.meet_absorb_join]
    _ = x := BooleanAlgebra.join_absorb_meet x (join x x)

/-- Meet is idempotent; this is derived from the absorption laws. -/
@[simp] theorem meet_idem (x : α) : meet x x = x := by
  calc
    meet x x = meet x (join x (meet x x)) := by
      rw [BooleanAlgebra.join_absorb_meet]
    _ = x := BooleanAlgebra.meet_absorb_join x (meet x x)

/-- The join and meet equations give equivalent characterizations of the order. -/
theorem join_eq_right_iff_meet_eq_left (x y : α) :
    join x y = y ↔ meet x y = x := by
  constructor
  · intro h
    calc
      meet x y = meet x (join x y) := congrArg (meet x) h.symm
      _ = x := BooleanAlgebra.meet_absorb_join x y
  · intro h
    calc
      join x y = join y x := BooleanAlgebra.join_comm x y
      _ = join y (meet x y) := congrArg (join y) h.symm
      _ = join y (meet y x) := congrArg (join y) (BooleanAlgebra.meet_comm x y)
      _ = y := BooleanAlgebra.join_absorb_meet y x

/-- `zero` is a right identity for join. -/
@[simp] theorem join_zero (x : α) : join x zero = x := by
  calc
    join x zero = join x (meet x (compl x)) := by
      rw [BooleanAlgebra.meet_compl]
    _ = x := BooleanAlgebra.join_absorb_meet x (compl x)

/-- `zero` is a left identity for join. -/
@[simp] theorem zero_join (x : α) : join zero x = x := by
  calc
    join zero x = join x zero := BooleanAlgebra.join_comm zero x
    _ = x := join_zero x

/-- `one` is a right identity for meet. -/
@[simp] theorem meet_one (x : α) : meet x one = x := by
  calc
    meet x one = meet x (join x (compl x)) := by
      rw [BooleanAlgebra.join_compl]
    _ = x := BooleanAlgebra.meet_absorb_join x (compl x)

/-- `one` is a left identity for meet. -/
@[simp] theorem one_meet (x : α) : meet one x = x := by
  calc
    meet one x = meet x one := BooleanAlgebra.meet_comm one x
    _ = x := meet_one x

/-- `zero` is absorbing for meet. -/
@[simp] theorem meet_zero (x : α) : meet x zero = zero := by
  calc
    meet x zero = meet x (meet x (compl x)) := by
      rw [BooleanAlgebra.meet_compl]
    _ = meet (meet x x) (compl x) :=
      (BooleanAlgebra.meet_assoc x x (compl x)).symm
    _ = meet x (compl x) := by rw [meet_idem]
    _ = zero := BooleanAlgebra.meet_compl x

/-- `zero` is absorbing for meet on the left. -/
@[simp] theorem zero_meet (x : α) : meet zero x = zero := by
  calc
    meet zero x = meet x zero := BooleanAlgebra.meet_comm zero x
    _ = zero := meet_zero x

/-- `one` is absorbing for join. -/
@[simp] theorem join_one (x : α) : join x one = one := by
  calc
    join x one = join x (join x (compl x)) := by
      rw [BooleanAlgebra.join_compl]
    _ = join (join x x) (compl x) :=
      (BooleanAlgebra.join_assoc x x (compl x)).symm
    _ = join x (compl x) := by rw [join_idem]
    _ = one := BooleanAlgebra.join_compl x

/-- `one` is absorbing for join on the left. -/
@[simp] theorem one_join (x : α) : join one x = one := by
  calc
    join one x = join x one := BooleanAlgebra.join_comm one x
    _ = one := join_one x

/-- The complement law with the complemented element written first. -/
@[simp] theorem compl_join_self (x : α) : join (compl x) x = one := by
  calc
    join (compl x) x = join x (compl x) := BooleanAlgebra.join_comm (compl x) x
    _ = one := BooleanAlgebra.join_compl x

/-- The meet-complement law with the complemented element written first. -/
@[simp] theorem compl_meet_self (x : α) : meet (compl x) x = zero := by
  calc
    meet (compl x) x = meet x (compl x) := BooleanAlgebra.meet_comm (compl x) x
    _ = zero := BooleanAlgebra.meet_compl x

/-- An element disjoint from `x` whose join with `x` is `one` is the
complement of `x`.  Thus complements are unique. -/
theorem eq_compl_of_join_eq_one_of_meet_eq_zero {x y : α}
    (hjoin : join x y = one) (hmeet : meet x y = zero) :
    y = compl x := by
  have hy : y = meet y (compl x) := by
    calc
      y = meet y one := (meet_one y).symm
      _ = meet y (join x (compl x)) := by
        rw [BooleanAlgebra.join_compl]
      _ = join (meet y x) (meet y (compl x)) :=
        BooleanAlgebra.meet_distrib_join y x (compl x)
      _ = join zero (meet y (compl x)) := by
        rw [BooleanAlgebra.meet_comm y x, hmeet]
      _ = meet y (compl x) := zero_join _
  have hx : compl x = meet y (compl x) := by
    calc
      compl x = meet (compl x) one := (meet_one (compl x)).symm
      _ = meet (compl x) (join x y) := by rw [hjoin]
      _ = join (meet (compl x) x) (meet (compl x) y) :=
        BooleanAlgebra.meet_distrib_join (compl x) x y
      _ = join zero (meet (compl x) y) := by rw [compl_meet_self]
      _ = meet (compl x) y := zero_join _
      _ = meet y (compl x) := BooleanAlgebra.meet_comm (compl x) y
  exact hy.trans hx.symm

/-- Complement is involutive. -/
@[simp] theorem compl_compl (x : α) : compl (compl x) = x := by
  symm
  apply eq_compl_of_join_eq_one_of_meet_eq_zero
  · exact compl_join_self x
  · exact compl_meet_self x

/-- The complement of `zero` is `one`. -/
@[simp] theorem compl_zero : compl (zero : α) = one := by
  symm
  apply eq_compl_of_join_eq_one_of_meet_eq_zero
  · exact zero_join one
  · exact meet_one zero

/-- The complement of `one` is `zero`. -/
@[simp] theorem compl_one : compl (one : α) = zero := by
  symm
  apply eq_compl_of_join_eq_one_of_meet_eq_zero
  · exact join_zero one
  · exact meet_zero one

/-- De Morgan's law for join. -/
theorem compl_join (x y : α) :
    compl (join x y) = meet (compl x) (compl y) := by
  have hx : join (join x y) (compl x) = one := by
    calc
      join (join x y) (compl x) = join (compl x) (join x y) :=
        BooleanAlgebra.join_comm (join x y) (compl x)
      _ = join (join (compl x) x) y :=
        (BooleanAlgebra.join_assoc (compl x) x y).symm
      _ = join one y := by rw [compl_join_self]
      _ = one := one_join y
  have hy : join (join x y) (compl y) = one := by
    calc
      join (join x y) (compl y) = join x (join y (compl y)) :=
        BooleanAlgebra.join_assoc x y (compl y)
      _ = join x one := by rw [BooleanAlgebra.join_compl]
      _ = one := join_one x
  have mx : meet x (meet (compl x) (compl y)) = zero := by
    calc
      meet x (meet (compl x) (compl y)) =
          meet (meet x (compl x)) (compl y) :=
        (BooleanAlgebra.meet_assoc x (compl x) (compl y)).symm
      _ = meet zero (compl y) := by rw [BooleanAlgebra.meet_compl]
      _ = zero := zero_meet _
  have my : meet y (meet (compl x) (compl y)) = zero := by
    calc
      meet y (meet (compl x) (compl y)) =
          meet y (meet (compl y) (compl x)) := by
        rw [BooleanAlgebra.meet_comm (compl x) (compl y)]
      _ = meet (meet y (compl y)) (compl x) :=
        (BooleanAlgebra.meet_assoc y (compl y) (compl x)).symm
      _ = meet zero (compl x) := by rw [BooleanAlgebra.meet_compl]
      _ = zero := zero_meet _
  symm
  apply eq_compl_of_join_eq_one_of_meet_eq_zero
  · calc
      join (join x y) (meet (compl x) (compl y)) =
          meet (join (join x y) (compl x))
            (join (join x y) (compl y)) :=
        BooleanAlgebra.join_distrib_meet (join x y) (compl x) (compl y)
      _ = meet one one := by rw [hx, hy]
      _ = one := meet_idem one
  · calc
      meet (join x y) (meet (compl x) (compl y)) =
          meet (meet (compl x) (compl y)) (join x y) :=
        BooleanAlgebra.meet_comm (join x y) (meet (compl x) (compl y))
      _ = join
          (meet (meet (compl x) (compl y)) x)
          (meet (meet (compl x) (compl y)) y) :=
        BooleanAlgebra.meet_distrib_join (meet (compl x) (compl y)) x y
      _ = join
          (meet x (meet (compl x) (compl y)))
          (meet y (meet (compl x) (compl y))) := by
        rw [BooleanAlgebra.meet_comm (meet (compl x) (compl y)) x,
          BooleanAlgebra.meet_comm (meet (compl x) (compl y)) y]
      _ = join zero zero := by rw [mx, my]
      _ = zero := join_idem zero

/-- De Morgan's law for meet. -/
theorem compl_meet (x y : α) :
    compl (meet x y) = join (compl x) (compl y) := by
  have h := congrArg compl (compl_join (compl x) (compl y))
  simpa using h.symm

end BooleanAlgebra

end BooleanAlgebrasDoneRight
