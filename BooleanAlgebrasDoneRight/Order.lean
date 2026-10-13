import BooleanAlgebrasDoneRight.Basic
import Mathlib.Order.Basic

/-!
# The partial order derived from Boolean operations

Define `BooleanAlgebra.le x y` by `join x y = y`. Idempotence,
commutativity, and associativity prove the partial-order laws. Absorption
identifies the same relation with `meet x y = x`.

`BooleanAlgebra.partialOrder` packages the derived relation as a Lean
partial order. It is an explicit construction, so callers can install it
locally without overriding an existing order on the carrier.
-/

universe u

namespace BooleanAlgebrasDoneRight

open BooleanOps

namespace BooleanAlgebra

variable {α : Type u} [BooleanAlgebra α]

/-- The order determined by the Boolean join operation. -/
def le (x y : α) : Prop := join x y = y

theorem le_iff_join_eq (x y : α) : le x y ↔ join x y = y := Iff.rfl

theorem le_iff_meet_eq (x y : α) : le x y ↔ meet x y = x :=
  join_eq_right_iff_meet_eq_left x y

theorem le_refl (x : α) : le x x := join_idem x

theorem le_antisymm {x y : α} (hxy : le x y) (hyx : le y x) : x = y :=
  hyx.symm.trans ((join_comm y x).trans hxy)

theorem le_trans {x y z : α} (hxy : le x y) (hyz : le y z) : le x z := by
  change join x y = y at hxy
  change join y z = z at hyz
  change join x z = z
  calc
    join x z = join x (join y z) := congrArg (join x) hyz.symm
    _ = join (join x y) z := (join_assoc x y z).symm
    _ = join y z := congrArg (fun a => join a z) hxy
    _ = z := hyz

/-- The canonical partial order derived from the algebraic Boolean laws. -/
abbrev partialOrder (α : Type u) [BooleanAlgebra α] : PartialOrder α where
  le := BooleanAlgebra.le
  le_refl := BooleanAlgebra.le_refl
  le_trans := fun _ _ _ => BooleanAlgebra.le_trans
  le_antisymm := fun _ _ => BooleanAlgebra.le_antisymm

end BooleanAlgebra

end BooleanAlgebrasDoneRight
