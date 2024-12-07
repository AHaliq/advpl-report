= Conclusion

With an understanding of `Trocq` calculus, we were able to read the Coq code in @trocqgithub and understand how the logical relations were constructed then provided to the plugin. We then attempted to construct some basic parametricity proofs using just the relations. This is shown in the parametricity proof if `isEven` in the reflexive relation on `nat`.

We then tried to explore heterogeneous diagonals between `nat` and `BigN` but were unable to construct the map between the two types due to the complexity of the `BigN` type, which is a bottleneck of competency in Coq and not the `Trocq` calculus.

In conclusion, we have learned how logical relations and parametricity are used to express univalence computationally and more general relations of equality such that we can do proof transfer. And we were able to engage with the codebase using the `Trocq` plugin for Coq to construct some basic proofs.