import BooleanAlgebrasDoneRight.Iso

/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-/

/-!
# Dual Boolean algebras

The dual has the same carrier and complement, with meet and join exchanged
and zero and one exchanged. Each defining Boolean law is supplied by its
partner in the original algebra. This lets existing proofs be reused on
`Dual A` without deriving the dual identity again.
-/

universe u

namespace BooleanAlgebrasDoneRight

open BooleanOps

/-- A type tag for the dual Boolean algebra. -/
def Dual (A : Type u) : Type u := A

namespace Dual

variable {A : Type u}

def toDual (a : A) : Dual A := a
def ofDual (a : Dual A) : A := a

@[simp] theorem ofDual_toDual (a : A) : ofDual (toDual a) = a := rfl
@[simp] theorem toDual_ofDual (a : Dual A) : toDual (ofDual a) = a := rfl

instance booleanAlgebra [BooleanAlgebra A] : BooleanAlgebra (Dual A) where
  meet a b := toDual (join (ofDual a) (ofDual b))
  join a b := toDual (meet (ofDual a) (ofDual b))
  compl a := toDual (compl (ofDual a))
  zero := toDual (one : A)
  one := toDual (zero : A)
  meet_assoc := fun a b c => BooleanAlgebra.join_assoc (ofDual a) (ofDual b) (ofDual c)
  meet_comm := fun a b => BooleanAlgebra.join_comm (ofDual a) (ofDual b)
  join_assoc := fun a b c => BooleanAlgebra.meet_assoc (ofDual a) (ofDual b) (ofDual c)
  join_comm := fun a b => BooleanAlgebra.meet_comm (ofDual a) (ofDual b)
  join_absorb_meet := fun a b => BooleanAlgebra.meet_absorb_join (ofDual a) (ofDual b)
  meet_absorb_join := fun a b => BooleanAlgebra.join_absorb_meet (ofDual a) (ofDual b)
  meet_distrib_join := fun a b c =>
    BooleanAlgebra.join_distrib_meet (ofDual a) (ofDual b) (ofDual c)
  join_distrib_meet := fun a b c =>
    BooleanAlgebra.meet_distrib_join (ofDual a) (ofDual b) (ofDual c)
  join_compl := fun a => BooleanAlgebra.meet_compl (ofDual a)
  meet_compl := fun a => BooleanAlgebra.join_compl (ofDual a)

variable [BooleanAlgebra A]

@[simp] theorem ofDual_meet (a b : Dual A) :
    ofDual (meet a b) = join (ofDual a) (ofDual b) := rfl

@[simp] theorem ofDual_join (a b : Dual A) :
    ofDual (join a b) = meet (ofDual a) (ofDual b) := rfl

@[simp] theorem ofDual_compl (a : Dual A) :
    ofDual (compl a) = compl (ofDual a) := rfl

@[simp] theorem ofDual_zero : ofDual (zero : Dual A) = (one : A) := rfl
@[simp] theorem ofDual_one : ofDual (one : Dual A) = (zero : A) := rfl

/-- Dualizing twice returns an isomorphic Boolean algebra. -/
def doubleDualIso (A : Type u) [BooleanAlgebra A] :
    BooleanAlgebra.Iso (Dual (Dual A)) A where
  toHom :=
    { toFun := fun a => ofDual (ofDual a)
      map_zero' := rfl
      map_one' := rfl
      map_join' := by intro a b; rfl
      map_meet' := by intro a b; rfl
      map_compl' := by intro a; rfl }
  bijective' := by
    constructor
    · intro a b h
      exact congrArg (fun x : A => toDual (toDual x)) h
    · intro a
      exact ⟨toDual (toDual a), rfl⟩

/-- A proof-reuse example: the dual of the join-one law is the meet-zero law. -/
theorem meet_zero_from_dual (a : A) : meet a zero = zero := by
  have h := BooleanAlgebra.join_one (α := Dual A) (toDual a)
  simpa using congrArg ofDual h

end Dual

end BooleanAlgebrasDoneRight
