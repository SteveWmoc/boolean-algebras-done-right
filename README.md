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

The primitive Boolean signature and equational axioms, elementary identities,
derived order, intrinsic homomorphisms and isomorphisms, and the category of
Boolean algebras are implemented. Concrete examples include power set,
trivial, and two-element algebras.

`BooleanAlgebra.Subalgebra A` describes substructures as subsets closed under
meet, join, complement, zero, and one. Each subalgebra inherits a Boolean
algebra structure on its carrier subtype. `S.subtype : BooleanAlgebra.Hom S A`
is the canonical injective inclusion, with simplification lemmas for all five
primitive operations.

`SetExamples.SetAlgebra X` specializes subalgebras to the power set algebra
of `X`. `IsSetAlgebra X F` states the concrete family conditions: every member
is a subset of `X`, the family contains the empty set and `X`, and it is closed
under binary intersection, binary union, and relative complement in `X`.
`SetAlgebra.equivFamilies X` proves the two presentations equivalent. Each
`SetAlgebra X` inherits its Boolean algebra and inclusion homomorphism from
the general subalgebra API.

`SetExamples.FiniteCofiniteAlgebra X` is the Boolean algebra of subsets `s ⊆ X`
for which `s` or `X \\ s` is finite. Its closure under the Boolean operations
is proved through `IsSetAlgebra`, so its Boolean identities are inherited.
For finite `X`, the finite-cofinite family equals the full power set.

For infinite `X`, `SetExamples.finiteCofinite_cardinality` proves that this
algebra has cardinality `Cardinal.mk X`. The construction yields
`BooleanAlgebra.exists_of_infinite_cardinality`: every infinite cardinal
is realized by a Boolean algebra.

For any topological space `X`, `SetExamples.ClopenAlgebra X` is the Boolean
algebra of clopen subsets, constructed as a power set subalgebra.
`clopenEquiv X` identifies its carrier with the subtype of clopen sets;
the operation lemmas identify meet, join, and complement with intersection,
union, and set complement. No separation or compactness assumptions are needed.
