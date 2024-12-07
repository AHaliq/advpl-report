#import "@preview/codly:1.1.1": *
#import "@preview/codly-languages:0.1.1": *
#import "../preamble/dtt.typ": *
#import "../preamble/catt.typ": *
#show: codly-init.with()

= Formalization Project

One motivation for proof transfer is the case of formalization projects of modular arithmetic in cryptography. Often in these projects their types are defined in slightly different ways, thus the same proofs are often repeated. `Trcoq` could provide a way for projects to use proofs from other projects despite the differences in their type definitions.

Another motivation is for optimal target types. For example, we could make a logically intuitive proof in `nat` and then transfer it to a more efficient type like `bigN` or `N`.

In this project we attempt to understand how the plugin is used and try to perform some basic proofs ourselves.

== Reflexive `nat` relation

In @trocqgithub `theories/Param_nat.v` we see that there is a reflexive relation defined for `nat` in lines 20 - 23.

#codly(languages: codly-languages)
```Coq
Inductive natR : nat -> nat -> Type :=
  | OR : natR O O
  | SR : forall (n n' : nat), natR n n' -> natR (S n) (S n').
```

Then there the lemma `natR_irrelevant` shows that any two parametricity witnesses for the same pair of terms are equal.

The code then attempts to construct $sqr^((4,4)) ($`nat`$,$`nat`$)$. The data required are defined as follows:

#figure(table(
  columns: 5,
  align: (center, center, center, center, center),
  [lattice data], $1$, $2_a$, $2_b$, $4$,
  [coq definition], `map_nat`, `map_in_R_nat`, `R_in_map_nat'`, `R_in_mapK_nat`,
))

Finally the relation $sqr^((4,4)) ($`nat`$,$`nat`$)$ is defined in `Param44_nat` in line 96.

== `isEven` holds under parametricity

In spirit of our motivating example of `isEven`, we will show that two related `nat` terms will yield the same result for `isEven`.

#codly(languages: codly-languages)
```Coq
Fixpoint isEven (n : nat) : bool :=
  match n with
  | O => true
  | (S x) => ~~ (isEven x)
  end.
```
This is our recursive definition of `isEven` where `O` is even and for each `S` the result is negated. We then show that if `n1` and `n1'` are in relation then `isEven n1 = isEven n1'`.

#codly(languages: codly-languages)
```Coq
Definition Param_isEven :
  forall (n1 n1' : nat) (n1R : natR n1 n1'), isEven n1 = isEven n1'.
Proof.
  intros n1 n1' n1R.
  induction n1R as [|n1 n1' n1R IHn1R].
  - reflexivity.
  - simpl. rewrite IHn1R. reflexivity.
Defined.
```

== Heterogeneous Diagonals

Let's try to define a relation for `nat` and Coq's bignum library's `bigN` type. If we were to look at `natR`, we have a relation constructor per constructor of the type. Unfortunately for `bigN` it is a type defined using a macro over a cylic type `ZnZ`. Thus instead we define the diagonal over definitions of `ZnZ`.

#codly(languages: codly-languages)
```Coq
Inductive natR : nat -> BigN.t -> Type :=
  | ZeroR : natR O BigN.zero
  | OneR : natR (S O) BigN.one
  | TwoR : natR (S (S O)) BigN.two
  | SuccR : forall (n : nat) (n' : BigN.t),
      natR n n' -> natR (S n) (BigN.succ n').
```

The rest of the progress in this direction is described in @bignproblem