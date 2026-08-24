/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
-

/-!
# Boolean-algebra signature

This file records only the finitary algebraic signature of Boolean algebras:
two binary operations, one unary operation, and two constants.

No order or lattice structure is assumed here.  The choice of equational axiom
basis is intentionally left to `Basic.lean` after comparison with the classical
references and after prototyping the resulting API.
-/

universe u

namespace BooleanAlgebrasDoneRight

/-- The raw finitary signature of a Boolean algebra on a carrier `α`.

The fields are deliberately algebraic.  In particular, there is no primitive
order relation and no inherited lattice structure. -/
class BooleanOps (α : Type u) where
  meet : α → α → α
  join : α → α → α
  compl : α → α
  zero : α
  one : α

end BooleanAlgebrasDoneRight
