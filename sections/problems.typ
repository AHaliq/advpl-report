#import "../preamble/dtt.typ": *
#import "../preamble/catt.typ": *
#import "@preview/codly:1.1.1": *
#import "@preview/codly-languages:0.1.1": *
#show: codly-init.with()

= Problems Encountered

== Understanding the table Fig.2 in @trocq

The tables of Fig.2 of @trocq was notationally confusing to read at first. Once we understood that $cal(D)_Pi (m,0)_1$ where the subscript $1$ is the first projection of the pair of pairs, i.e. the first pair, then the table made much more sense.

== Attempt at following tutorial of plugin

We tried to follow the first example in `artifact-doc/TUTORIAL.md` in @trocqgithub.

What we first found is an error using  the code `RN0 : RN 0%N 0%nat` in line 52. We replaced it with `RN0 : RN N0%N 0%nat` naively to remove the error.

We were able to define `RN`.

#codly(languages: codly-languages)
```Coq
Definition RN : Param44.Rel N nat :=
  Iso.toParamSym (Iso.Build of_natK to_natK).
```

However we could not proceed with the rest of the proof since `.+1%N` is not defined in the tutorial.

== Constructing the data for $sqr ($`nat`$,$`BigN`$)$<bignproblem>

Ideally we would need the following data for type equivalence between `nat` and `BigN`:
- $1$ : map from `nat` $->$ `BigN`
- $2_a$: identifications (under equivalence coercion) to diagonal
- $2_b$: diagonal to identification (under equivalence coercion)
- $4$: composition of the above two is identity and that this is proof irrelevant

Despite the benefit that `Trocq` allows weaker structures, even if we were to proof transfer something that only requires level `(1,0)`, a map from `nat` to `BigN` does not exist in the coq bignum library.

Thus in this project, we only managed to define the diagonal for `BigN` and `nat` and not the map due to the complexity of how `BigN` is defined with a macro over `ZnZ`.

== Attempt `isEven` hold parametrically for `BigN`

Even with just the diagonal we could still attempt to show parametricity for `isEven` between `nat` and `BigN`. First we define `isEven` for `BigN`:

#codly(languages: codly-languages)
```Coq
Definition isEvenBigN (n : BigN.t) : bool :=
  BigN.eqb (BigN.modulo n BigN.two) BigN.zero.
```

One might try the following proof:

#codly(languages: codly-languages)
```Coq
Definition Param_isEven :
  forall (n1 : nat) (n1' : BigN.t) (n1R : natR n1 n1'),
    isEven n1 = isEvenBigN n1'.
Proof.
  intros n1 n1' n1R.
  induction n1R as [| | |n1 n1' n1R IHn1R].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHn1R.
  ???
Defined.
```
At the point of `???` we still have to show that

```
n1 : nat 
n1' : bigN 
n1R : natR n1 n1' 
IHn1R : isEven n1 = isEvenBigN n1' 
----------------------------------
(if isEvenBigN n1' then false else true) = isEvenBigN (BigN.succ n1')
```

Intuitively we know if a number is even, then its successor is odd. But to prove this formally would require us to induct on the definition of `isEvenBigN` which is defined in terms of `BigN.t` which is defined in terms of a complex `ZnZ` type. What we would want to do here is to actually perform proof transfer of `isEven` from `nat`. But as mentioned before, we were unable to construct the type relation $sqr ($`nat`$,$`BigN`$)$ to use the `Trocq` tactic to proof transfer.

Alternatively, if we could get the symmetric relation from `BigN` to `nat`, instead of `rewrite IHn1R` we could rewrite with its symmetric on the right hand side to get the expression in terms of `nat` which we could then inductively show that the successor of an even number is odd.

== Figure out how `BigN` is defined

`BigN` as a module is defined in @bignumgithub in `BigN/BigN.v` line 31.

#codly(languages: codly-languages)
```Coq
Module BigN <: NType <: OrderedTypeFull <: TotalOrder :=
  NMake.Make Uint63Cyclic
  <+ NTypeIsNAxioms
  <+ NBasicProp [no inline] <+ NExtraProp [no inline]
  <+ HasEqBool2Dec [no inline]
  <+ MinMaxLogicalProperties [no inline]
  <+ MinMaxDecProperties [no inline].
```

We can see that a helper function defines the module `NMake.Make`.

This helper function is defined in `BigN/NMake.v` line 22.

#codly(languages: codly-languages)
```Coq
Module Make (W0:CyclicType) <: NType.
   Include NMake_gen.Make W0.
   ...
```

The body of this abstract module is defined via a macro call `NMake_gen.Make` at line 28.

This is where our progress to figure out the constructors of `BigN` stops.

We could also follow the trail of the underlying type provided as an argument to `NMake.Make` which is `Uint63Cyclic`.

This is a type part of the standard library in `Library Coq.Numbers.Cyclic.Int63.Cyclic63`

#codly(languages: codly-languages)
```Coq
Module Uint63Cyclic <: CyclicType.
  Definition t := int.
  Definition ops := int_ops.
  Definition specs := int_specs.
End Uint63Cyclic.
```

We can see that its a "submodule" of `CyclicType` which is defined in `Library Coq.Numbers.Cyclic.Abstract.CyclicAxioms`.

#codly(languages: codly-languages)
```Coq
Module Type CyclicType.
 Parameter t : Set.
 Declare Instance ops : ZnZ.Ops t.
 Declare Instance specs : ZnZ.Specs ops.
End CyclicType.
```

We can see that the module is defined in terms of `ZnZ.Ops` and `ZnZ.Specs`

The types these interfaces use are `positive`, `Z` and `N`.

#codly(languages: codly-languages)
```Coq
Inductive positive : Set :=
  | xI : positive -> positive
  | xO : positive -> positive
  | xH : positive.
```

`positive` is an inductive type modelling sequence of bits. `N` then is just a wrapper around `positive` using constructor `Npos` with a zero element `N0`. `Z` then has two wrappers `Npos, Nneg` for each polarity and of course the zero element `Z0`.

However most of the operations uses the type `t`, in our case for `Unit63Cyclic` this is `int`.

The exact arithmetic operation implementation is defined in `Library Coq.Numbers.Cyclic.Int63.Uint63`. For example addition is as follows

#codly(languages: codly-languages)
```Coq
Notation add := add (only parsing).
```

However here we note that `add` is simply notation, but there is however another file that says it is how cylic type operations are defined. `Library Coq.Numbers.NatInt.NZAdd`