

= Introduction

The _Univalent Foundations Program_ initiated by Vladimir Voevodsky introduces the idea of univalence to type theory, where the equality of types is equivalent to type equivalence. A consequence of this is that we can perform proof transfer for equivalent types. However, univalence is an axiom, thus when a theorem prover encounters it as a term, it gets stuck.

The `Trocq` calculus by Cyril Cohen et al. uses logical relations to express the equality of terms and internalizes it into its calculus. Thus univalence expressed as one of these relations is computable.

`Trocq` takes a step further and generalizes the relation for type equality by indexing it with a product of lattice elements, which expresses the relationship between the types. For example, the index $(4,4)$ are equivalent types ala univalence, $(3,3)$ are isomorphic types, and $(1,0)$ are types where there is a function from the left type to the right.

Different proofs depending on their type have varying requirements of index or equality level to automate proof transfer. The `Trocq` metaprogram has computed for itself the required levels for its basic type constructors which then determines the required level for any user constructed proof. Thus, `Trocq` can be seen as a general calculus for proof transfer.

== Objectives

1. This project initially serves as an exploration into learning how logical relations and parametricity are used to express univalence computationally. It will achieve this aim by understanding the `Trocq` calculus. @trocq
2. Additionally, we will attempt to formalize some proofs using the parametricity plugin for Coq. @trocqgithub