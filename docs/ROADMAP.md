# Roadmap

This roadmap is intentionally living and near-term.  It records the direction
of travel without pretending that every dependency several chapters ahead is
already known.

## M001 — Algebraic core

- choose a standard equational axiom basis for the Boolean signature;
- define the Boolean-algebra laws without primitive order structure;
- derive elementary identities, including absorption, involution, and the usual
  interaction of complement with the binary operations;
- settle notation and the split, if any, between raw operations and lawful
  Boolean algebras.

Acceptance criterion: the core theory is usable without importing or assuming
Mathlib's lattice-first Boolean-algebra structure.

## M002 — Derived order and lattice theory

- define the canonical order from the algebraic operations;
- prove that it is a partial order;
- prove that the Boolean operations give infimum and supremum;
- derive bounded distributive lattice structure;
- derive the standard order/complement identities.

Acceptance criterion: ordinary order-theoretic reasoning is available as a
consequence of the algebraic core.

## M003 — Intrinsic homomorphisms

- define Boolean homomorphisms intrinsically;
- provide identity, composition, extensionality, and coercion-to-function API;
- prove preservation of the derived order and lattice structure;
- develop embeddings/isomorphisms as needed.

Acceptance criterion: the category of Boolean algebras can be developed without
defining its morphisms as a subcategory of lattice morphisms.

## M004 — First examples and interoperability

- algebras of sets;
- finite examples useful for testing;
- explicit bridges to Mathlib's order/lattice infrastructure where coherent;
- document any unavoidable incompatibilities or typeclass-coherence hazards.

Acceptance criterion: the foundational API is validated on concrete models and
can interact with Mathlib without making Mathlib's presentation foundational.

## Later directions

The next subjects will be chosen in response to both the classical theory and
Boolean-valued applications.  Likely early themes include relative algebras,
disjoint families and partitions, subalgebras and homomorphism theory,
ideals/filters/quotients, completeness, and standard representation examples.

These are directions rather than frozen milestones until the preceding API has
been exercised in real formalizations.
