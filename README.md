# Boolean Algebras Done Right

An algebra-first Lean 4 development of Boolean algebras, their homomorphisms, representations, and infinitary theory.

The guiding principle is simple:

> Boolean algebras are treated as algebraic structures; their order and lattice structure are derived.

The project takes the Boolean signature

- two binary operations,
- one unary complement operation,
- two distinguished constants,

as foundational. Order-theoretic structure is then proved from the Boolean identities rather than assumed at the definition site. In particular, Boolean homomorphisms are intended to be defined intrinsically as homomorphisms of this algebraic signature.

The long-term development is informed by classical sources including Halmos, Sikorski, and the *Handbook of Boolean Algebras*, while remaining driven by formalization needs arising in Boolean-valued mathematics.

## Initial plan

The first milestone is deliberately small:

1. choose and formalize a clean equational axiom system for Boolean algebras;
2. derive the elementary identities;
3. derive the canonical partial order and bounded distributive lattice structure;
4. define intrinsic Boolean homomorphisms and prove their basic API;
5. verify the design on algebras of sets;
6. provide explicit interoperability with Mathlib where useful.

The internal roadmap is a living document. The project does not aim to formalize every theorem in the classical literature before applications can move forward.

## Status

Initial setup in progress.
