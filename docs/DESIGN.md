# Design notes

This document records current architectural commitments.  It is deliberately
short and may evolve as the formalization teaches us more.

## D001 — Algebra first

A Boolean algebra is treated fundamentally as an algebraic structure with a
finitary signature of arities `(2, 2, 1, 0, 0)`: two binary operations, one
unary operation, and two constants.

Order and lattice structure are derived from the Boolean identities.  They are
not part of the foundational definition.

## D002 — Intrinsic homomorphisms

A Boolean homomorphism is first a homomorphism of the Boolean signature.
Monotonicity and preservation of the derived order/lattice structure are
proved consequences.

## D003 — Mathlib is an interoperability target

The project may depend on Mathlib for general infrastructure, tactics, and
unrelated mathematics.  Mathlib's existing lattice-first `BooleanAlgebra`
hierarchy does not determine the foundational presentation here.

Interoperability belongs in an explicit bridge layer.  Derived global
instances should be introduced only after checking for typeclass diamonds and
other coherence problems.

## D004 — References guide mathematics, applications guide priority

Classical references include Halmos, Sikorski, and the *Handbook of Boolean
Algebras*.  They guide terminology, theorem statements, and mathematical
scope, but the project is not a page-by-page formalization of any one source.

Boolean-valued mathematics is an important downstream consumer and provides
feedback about which reusable Boolean-algebra results deserve priority.

## D005 — Do not freeze unknown future architecture

The roadmap is living.  Near-term interfaces should be tested on concrete
examples and downstream applications before large parts of the library depend
on them.
