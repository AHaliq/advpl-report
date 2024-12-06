#import "@preview/curryst:0.3.0": rule, proof-tree
#import "../preamble/dtt.typ" : *
#import "../preamble/catt.typ" : *

= Description and Objectives

The _Univalent Foundations Program_ initiated by the late Vladimir Voevodsky introduces the idea of univalence to type theory, where the equality of types is equivalent to type equivalence. A consequence of this is that we can perform proof transfer for equivalent types. However, univalence is an axiom, thus when a theorem prover encounters it as a term, it gets stuck.

#figure(
  $
    ua : Id(UU, A, B) equiv (A equiv B)
  $,
  caption: [Univalence Axiom],
)

The `Trocq` calculus by Cyril Cohen et al. uses logical relations to express the equality of terms and internalizes it into its calculus via _Univalent Parametricity Sequents_ $hyu$ and parametricity contexts $Xi$ which are a list of equal terms and its witness. Thus univalence expressed as one of these relations is computable.

#figure(
  proof-tree(
    rule(
      name: [UParam-sort],
      $Xi hyu UU_i ~ UU_i ∵ p_(square_i)^(top,top)$,
    ),
  ),
  caption: [Univalence as a Logical Relation where $"rel"(p_(square_i)^(top,top)) = sqr^top$]
)

`Trocq` takes a step further and generalizes the relation for type equality by indexing it with a product of lattice elements, which expresses the relationship between the types. For example, the index $(4,4)$ are equivalent types ala univalence, $(3,3)$ are isomorphic types, and $(1,0)$ are types where there is a function from the left type to the right.

#figure(
  $
    sqr^((4,4)) (A,B) &= A equiv B \
    sqr^((3,3)) (A,B) &= A iso B \
    sqr^((1,0)) (A,B) &= A -> B
  $,
  caption: [Instantiations of the general type equality relation]
)

Different proofs depending on their type have varying requirements of index or equality level to automate proof transfer. The `Trocq` metaprogram has computed for itself the required levels for its basic type constructors which then determines the required level for any user constructed proof. Thus, `Trocq` can be seen as a general calculus for proof transfer.

This project serves as an exploration into learning how logical relations and parametricity are used to express univalence computationally. We will achieve this aim by understanding and describing the `Trocq` calculus @trocq and attempt to formalize some proofs using the `Trocq` parametricity plugin for Coq. @trocqgithub