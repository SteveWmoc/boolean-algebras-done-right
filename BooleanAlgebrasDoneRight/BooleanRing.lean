import Mathlib.Algebra.Ring.BooleanRing

/-!
# Idempotent elements and Boolean rings

We use Mathlib's definitions directly:

* `IsIdempotentElem x` means `x * x = x`. It is defined for any
  multiplication, hence in particular for every ring.
* `BooleanRing R` extends the unital `Ring R` structure with
  `∀ x : R, IsIdempotentElem x`.

Commutativity and nontriviality are not assumptions in this definition.
In particular the zero ring is allowed. Mathlib derives commutativity
from universal idempotence.

`booleanRingOfIdempotents` equips an existing unital ring with a Boolean
ring structure without changing its ring operations.
-/

universe u

namespace BooleanAlgebrasDoneRight

/-- A unital ring in which every element is idempotent is a Boolean ring.

The underlying ring structure is exactly the supplied one; commutativity
does not need to be assumed. -/
abbrev booleanRingOfIdempotents (R : Type u) [Ring R]
    (h : ∀ x : R, IsIdempotentElem x) : BooleanRing R where
  toRing := inferInstance
  isIdempotentElem := h

end BooleanAlgebrasDoneRight
