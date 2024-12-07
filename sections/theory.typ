#import "@preview/cetz:0.3.1"
#import "@preview/fletcher:0.5.2" as fletcher: node, edge, diagram
#import "@preview/ctheorems:1.1.3": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "@preview/numbly:0.1.0": numbly
#import "../preamble/dtt.typ": *
#import "../preamble/catt.typ": *

= Understanding `Trocq`

== Logical Relations Primer

Logical relations are relations that express some property of interest. We have seen in this course how we can define a relation $bold(upright("Safe"))_P (e)$ on expressions $e$ in system F. In this scenario, our logical relations are unary, making them a predicate. Moreover the predicates are defined using first order logic and set theoretic constructions. From this we can construct the abstraction theorem that makes our property of interest; in this case safety of system F, _parametric_.

#figure(
  $
    forall xi, v s. [| Delta hy Gamma |]_xi (v s) ==> [| Delta hy tau |]^upright(bold(E))_xi (e[v s slash x s])
  $,
  caption: [Abstraction Theorem for safety of System F: if $v s$ is a list of terms that is safe as the context $Gamma$, then substituting $x s$ with it in $e$ results in a safe expression still],
)

== Raw Parametricity Translations

In `Trocq`, the logical relations are binary relations on terms. They express term equality and are part of the "data" in the witness of the equality of terms. They are defined inductively just as in the relations for system F safety.

#figure(
  $
    [| angle.l angle.r |] &= angle.l angle.r \
    [| Gamma, x:A |] &= [| Gamma |], x : A, x' : A', x_R : [|A|] x x' \
    [| x |] &= x_R \
    [| UU_i |] &= lambda A, A'. A -> A' -> UU_i \
    [| A B |] &= [| A |] B B' [| B |] \
    [| lambda x : A, t |] &= lambda x : A, x' : A', x_R : [| A |] x x'. [| t |] \
    [| Pi(x : A, B) |] &= lambda f, f'. Pi(x : A, x' : A', x_R : [|A|]x x', [|B|]f(x)f'(x'))
  $,
  caption: [Relations in `Trocq`],
)

Note how the relation between types $[| UU_i |]$ is still not univalent but simply a relation expressed in type theory.

== Univalent Parametricity Translations

To make the relation univalent we can redefine it as follows

#figure(
  $
    [| UU_i |] A B = Sigma(R : A -> B -> UU_i, e : A equiv B, Pi(a : A, b : B, R a b equiv Id(A, a, attach(arrow.b, br: e)(b))))
  $,
  caption: [Univalent Type Equality Relation in `Trocq`],
)
Which can be intuitively visualized with the following diagram where the relation $R$ is equivalent to the identification of $a$ and $b$ coerced to type $A$ under the equivalence $e$.
#figure(
  diagram(
    cell-size: 10mm,
    $
      A
  #edge("rr", $R$, "<->", shift: 0pt, label-anchor: "south", label-sep: 0em, bend: 30deg)
  #edge("rr", $\_ : Id(A,a,attach(arrow.b, br: e)(b))$, "<->", shift: 0pt, label-anchor: "north", label-sep: 0em, bend: -30deg)
  #edge((1,-0.25),(1,0.25), $equiv$, "<..>")
  & &
B
    $,
  ),
  caption: [Diagram for $[| UU_i |]$],
)

Thus we say that $p$ is a parametricity witness of type equality $A$ and $B$ with the following notation

#figure(
  $
    p : [| UU_i |] A B
  $,
  caption: [Parametricity Witness of Type Equality],
)

The standard book HoTT definition for equivalence $A equiv B$ is given as a contractible fibre. However it is also proposed that a more symmetric definition in terms of relations can be done as well. The proof is explored in lemma 2 of @trocq.

#figure(
  $
    "isContr"(T) &= Sigma(t : T, Pi(t' : T, Id(T,t,t'))) \
    "isFun"(R) &= Pi(a : A, "isContr"(Sigma(b : B, R(a,b)))) \
    A equiv B &= underbrace(Sigma(f : A -> B, "isEquiv"(f)), "contractible fibre") = underbrace(Sigma(R, "isFun"(R) times "isFun"(R^(-1))), "functional relation") \
    &script("where" R^(-1) (b,a) = R(a,b))
  $,
  caption: [Symmetric redefinition of equivalence],
)

The key type here $"isFun"$ expresses that a relation is a functional relation. `Trocq` redefines this as well such that it can define equivalences of different levels, from less information to most being equivalence. The proof is explored in lemma 4 of @trocq.

#figure($
  "isFun"(R) = "isUmap"( R ) = Sigma(
    &m : A -> B, && 1 & -> \
    &g_1 : Pi(a : A, b : B, Id(B, m(a), b) -> R(a, b)),  && 2_a & arrow.t \
    &g_2 : Pi(a : A, b : B, R(a, b) -> Id(B, m(a), b)), && 2_b & arrow.b \
    &Pi(a : A, b : B, g_1(a,b) comp g_2(a,b) =^dot_dot id)) && 4 & equiv
$)

The right most column labels the data required to express equivalence. $1$ being a map from $A$ to $B$, $2_a$ being the map from identifications to relations and $2_b$ being the map from relations to identifications. The last row expresses that the composition of the maps is functionally extensional to the identity function. This is how we define the logical relation for univalent type equality.

#figure(
  $
    sqr^top (A,B) = Sigma (R : A -> B -> UU_i, "isUmap"(R) times "isUmap"(R^(-1)))
  $,
  caption: [Equivalence as a logical relation],
)

== Generalized Type Equality Relation

The objective of `Trocq` is to be a calculus for proof transfer. If we stop our definition here this would require for any proof transfer to be done we will always need enough data such that $sqr^top$ holds between the two types we wish to transfer proofs between. This is too strong a condition for some proofs. Thus `Trocq` generalizes the relation to levels of information between types.

This generalization is done by indexing the relation with a product of lattice elements. The lattice elements are defined as follows

#figure(
  cetz.canvas({
    import cetz.draw: *
    circle((-2, 0), radius: (0.1, 0.1), fill: black, anchor: "mid", name: "0")
    circle((0, 0), radius: (0.1, 0.1), fill: black, anchor: "mid", name: "1")
    circle((2, 1), radius: (0.1, 0.1), fill: black, anchor: "mid", name: "2_a")
    circle((2, -1), radius: (0.1, 0.1), fill: black, anchor: "mid", name: "2_b")
    circle((4, 0), radius: (0.1, 0.1), fill: black, anchor: "mid", name: "3")
    circle((6, 0), radius: (0.1, 0.1), fill: black, anchor: "mid", name: "4")
    content((-2, 1), $0$, anchor: "north")
    content((-2, -0.5), [no data], anchor: "south")
    content((0, 1), $1$, anchor: "north")
    content((0, -0.5), [$->$], anchor: "south")
    content((2, 2), $2_a$, anchor: "north")
    content((2, 0.5), [$arrow.t$], anchor: "south")
    content((2, -0), $2_b$, anchor: "north")
    content((2, -1.5), [$arrow.b$], anchor: "south")
    content((4, 1), $3$, anchor: "north")
    content((4, -0.5), [$iso$], anchor: "south")
    content((6, 1), $4$, anchor: "north")
    content((6, -0.5), [$equiv$], anchor: "south")
    line("0.east", "1.west", name: "line0", mark: (end: ">", start: none))
    line("1.east", "2_a.west", name: "line1", mark: (end: ">", start: none))
    line("1.east", "2_b.west", name: "line2", mark: (end: ">", start: none))
    line("2_a.east", "3.west", name: "line3", mark: (end: ">", start: none))
    line("2_b.east", "3.west", name: "line4", mark: (end: ">", start: none))
    line("3.east", "4.west", name: "line5", mark: (end: ">", start: none))
  }),
)

Instead of $"isUmap"$, our type equality relation is now generalized with $M$

#figure(
  $
    sqr^((n,m)) (A, B) &= Sigma(R : A -> B -> UU, M_n (R) times M_m (R^(-1))) \
  $,
  caption: [Generalized Type Equality Relation],
)

Clearly we would want $sqr^top = sqr^((4,4))$ to be equivalence thus we would need $M_4 = "isUmap"$. Recall the definition of $"isUmap"$ from before, if we remove some of the terms / "data" in $M_4$ we will get the lower levels $M_3$, and so on. This is the idea for the definition of $M$.

#figure($
  M_0(R) &= tt \
  M_1(R) &= A -> B \
  M_(2_a) (R) &= Sigma(m : A -> B, G_(2_a)(m,R)) script("where" G_(2_a)(m,R) = Pi(a : A, b: B, Id(B, m(a), b) -> R(a,b))) \
  M_(2_b) ( R ) &= Sigma(m : A -> B, G_(2_b)(m,R)) script("where" G_(2_b)(m,R) = Pi(a : A, b: B, R(a,b) -> Id(B, m(a), b))) \
  M_3(R) &= Sigma(m : A -> B, (G_(2_a)(m,R) times G_(2_b)(m,R))) \
  M_4(R) &= Sigma(m : A -> B, Sigma(g_1 : G_(2_a)(m,R), g_2 : G_(2_b)(m,R), g_1(a,b) comp g_2(a,b) =^dot_dot id))
$)

Since our definition is symmetric, we have that $sqr^((m,n)) (A,B) &= sqr^((n,m)) (B,A)$

And as promised in the introduction, we have the following instantiations

#figure(
  $
    sqr^top = sqr^((4,4)) &= A equiv B \
    sqr^((3,3)) &= A iso B \
    sqr^((1,0)) &= A -> B \
  $,
  caption: [Instantiations of the general type equality relation],
)

Revisiting the univalent parametricity translation, we define $p_square^(alpha, beta)$ as a parametricity witness of the relation $sqr^beta$, in other words

#figure($
  p_square_i^(alpha, beta) : sqr_(i+1)^beta UU_i UU_i \
  "rel"(p_square_i^(alpha, beta)) = sqr_i^alpha
$)

Note the subscript $i$ here is the cumulative universe level as standard in HoTT wheras the superscript $beta$ is the index we just introduced which we will call equality level. Thus we can see that $p$ is witness of equality level $beta$ at cumulative level $i+1$, which contains the relation for equality on level $alpha$ at cumulative level $i$; the cumulative level below.

== Minimum Required Data

However not all elements $(alpha,beta)$ is a valid index for $p_square$ as some combinations lack the required data from one side to construct the relation. The set of permissible indices is defined as follows

#figure(
  $
    cal(D)_square = {(alpha,beta) in cal(A)^2 | alpha = top or beta in {0,1,2_a}^2}
  $,
  caption: [Permissible indices for $sqr$],
)

These are the requirements for arbitrary types. We have other constraints for type formers. Lets look at $Pi$ types.

#figure(
  proof-tree(
    rule(
      $Gamma hy p_Pi^gamma (A_R,B_R) : sqr^gamma (Pi(x : A, B), Pi(x' : A', B'))$,
      $Gamma hy A_R : sqr^alpha (A, A')$,
      $Gamma, x : A, x' : A', x_R : A_R (x, x') hy B_R : sqr^beta (B, B')$,
    ),
  ),
  caption: [Constructing parametricity witness for $Pi$ types],
)

We have that the first arguments $A, A'$ are equal at level $alpha$ wheras the second arguments $B, B'$ are equal at level $beta$. The resulting relation is at level $gamma$ which depends on $alpha$ and $beta$.

#figure($
  D_Pi (gamma) &= (alpha, beta) \
  D_Pi (m,n) &= ((m_A, n_A), (m_B, n_B)) \
$)

Instead of directly computing $p_Pi^((m,n))$ or $D_Pi (m,n)$ we compute $D_Pi (m,0)$ and $D_Pi (0,n)$. By symmetry we can compute $D_Pi (0,n)$ via computing $D_Pi (n,0)$. In other words it is sufficient to only tabulate $D_Pi (x, 0)$. The resulting values can be mapped as follows:

#figure($
  D_Pi (m,0) &= ((0, n_A), (m_B, 0)) \
  D_Pi (n,0) &= ((0, m_A), (n_B, 0))
$)

And the tabulated values for dependent products $Pi$ and non dependent functions $->$ computed by the `Trocq` metaprogram are as follows

#figure(
  table(
    columns: 9,
    align: (center + horizon, center, center, center, center, center, center, center, center),
    table.cell(rowspan: 1)[$m$],
    table.cell(colspan: 4)[$D_Pi (m,0)$],
    table.cell(colspan: 4)[$D_-> (m,0)$],
    $0$, $0$, $0$, $0$, $0$, $0$, $0$, $0$, $0$,
    $1$, $0$, $2_a$, $1$, $0$, $0$, table.cell(fill: orange.lighten(80%), $1$), $1$, $0$,
    $2_a$, $0$, $4$, $2_a$, $0$, $0$, table.cell(fill: orange.lighten(80%), $2_b$), $2_a$, $0$,
    $2_b$, $0$, $2_a$, $2_b$, $0$, $0$, $2_a$, $2_b$, $0$,
    $3$, $0$, $4$, $3$, $0$, $0$, table.cell(fill: orange.lighten(80%), $3$), $3$, $0$,
    $4$, $0$, $4$, $4$, $0$, $0$, $4$, $4$, $0$
  ),
)

Notice how we require less "data" for non dependent functions as compared to dependent $Pi$ types. Thus it is useful to compute these tables for our primitive type constructors rather than just use $cal(D)_square$; our most general constraint, for all types.

== Internalizing the Relation into a type theory

To internalize the relation, `Trocq` uses parametricity context $Xi$ which are a list of triples $(x,x',x_R)$ for the two terms that are equal along with its parametricity witness.

#figure(
  $
    Xi ::= epsilon | Xi, x ~ x' ∵ x_R
  $,
  caption: [Parametricity Context],
)

The entries are unique such that the following rule holds

#figure(
  proof-tree(
    rule(
      name: [defn-eq-param],
      $Xi hy (M',M_R) = (N', N_R)$,
      $Xi hy M ~ M' ∵ M_R$,
      $Xi hy M ~ N' ∵ N_R$,
    ),
  ),
)

If $M$ holds in relation with two terms, then those two terms (along with their parametricity witnesses) are definitionally equal.

The typing context $Gamma$ and parametricity context $Xi$ "interacts" with the admissability operator which expresses the following:

#figure($
  Gamma trir Xi <=> ((Xi hy Gamma(x) ~ A' ∵ A_R) => (Gamma(x') = A' and Gamma(x_R) = A_R (x,x')))
$)

If the type of $x$; $Gamma(x)$ is in relation with $A'$ then it must be that the type of $x'$ is $A'$ and that the type of the parametricity witness $x_R$ is the parametricity witness of the types equality instantiated on both terms $x$ and $x'$.

Recall that the parametricity witness of type equality is $p_square$ which is defined from $sqr$, thus to internalize univalence, we need the following rule

#figure(
  proof-tree(
    rule(
      name: [UParam-sort],
      $Xi hyu UU_i ~ UU_i ∵ p_(square_i)^(top,top)$,
    ),
  ),
)

To handle weaker relations; indices less than $(top, top)$, we would need to internalize equality levels. This is done through annotation in $"CC"_omega^+$. These annotation are related by the lattice we have defined before, thus we can internalize this structure via a subtyping relation. Enriched with this structure, the sequents are notated as $hyp$.

#figure(
  proof-tree(
    rule(
      name: [SubSort],
      $Gamma hyp UU_i^alpha subt UU_j^beta$,
      $alpha >= beta$,
      $i <= j$,
    ),
  ),
)
#figure(
  proof-tree(
    rule(
      name: [SubConv],
      $Gamma hyp A subt B$,
      $Gamma hyp A : K$,
      $Gamma hyp B : K$,
      $A #math.equiv B$,
    ),
  ),
)
#figure(
  proof-tree(
    rule(
      name: [Sort+],
      $Gamma hyp UU_i^alpha : UU_(i+1)^beta$,
      $(alpha, beta) in cal(D)_square$,
    ),
  ),
)
#figure(
  proof-tree(
    rule(
      name: [Conv+],
      $Gamma hyp M : B$,
      $Gamma hyp M : A$,
      $Gamma hyp A subt B$,
    ),
  ),
  caption: [Subtyping relation where $K := UU_i | Pi(x : A, K)$],
)

Recall the admissability operator $Gamma trir Xi$. To internalize this, we augment our parametricity context $Xi$ with types such that we have $Delta$ as follows

#figure(
  $
    Delta ::= epsilon | Delta, x @ A ~ x' ∵ x_R
  $,
  caption: [Parametricity Context with Type information],
)

Intuitively, we can read that $x$ is a term of type $A$ in relation with term $x'$ with parametricity witness $x_R$.

`Trocq` also has a "down casting" operator for equality levels.

#figure($
  attach(arrows.bb, br: (p,q), tr: (m,n)) angle.l R, M^->, M^<- angle.r &:= angle.l R, attach(arrow.b, tr: m, br: p) M^->, attach(arrow.b, tr: n, br: q) M^<- angle.r \
  attach(arrow.b.double, tr: UU_i^alpha, br: UU_i^alpha') t_R &= attach(arrows.bb, tr: alpha, br: alpha') t_R \
  attach(arrow.b.double, tr: A, br: A') M_R &= M_R \
  attach(arrow.b.double, tr: Pi(x : A, B), br: Pi(x : A', B')) M_R &= lambda x, x', x_R. attach(arrows.bb, tr: B, br: B') (M_R (x,x',attach(arrow.b.double, tr: A', br: A) x_R))
$)

Thus finally we can express univalence and our general equality relation as a rule in `Trocq` calculus as follows

#figure(
  proof-tree(
    rule(
      name: [TrocqSort],
      $Delta hyt UU_i^alpha @ UU_(i+1)^beta ~ UU_i^alpha ∵ p_(UU_i)^(alpha,beta)$,
      $(alpha, beta) in cal(D)_square$,
    ),
  ),
)

and the rule for down casting

#figure(
  proof-tree(
    rule(
      name: [TrocqConv],
      $Delta hyt M @ B ~ M' ∵ attach(arrow.b.double, br: B, tr: A) M_R$,
      $Delta hyt M @ A ~ M' ∵ M_R$,
      $gamma(Delta) hyp A subt B$,
    ),
  ),
)

Our parametricity property of equality is thus expressed as the abstraction theorem in the rule

#figure(
  proof-tree(
    rule(
      name: [TrocqAbs-Thm],
      $gamma(Delta) hyp M' : A' #h(2em) gamma(Delta) hyp M_R : "rel"(A_R)(M, M')$,
      $gamma(Delta) hyp$,
      $gamma(Delta) hyp M : A$,
      $Delta hyt M @ A ~ M' ∵ M_R$,
      $Delta hyt A @ UU_i^alpha ~ A' ∵ A_R$,
    ),
  ),
)

We can visualize that the theorem is completing the following square

#figure(diagram(cell-size: 5mm,
$
  M
    #edge("r", $M_R$)
    #edge("d", $:$, "->") &
  M'
    #edge("d", $:$, "-->") \
  A
    #edge("r", $A_R$) &
  A'
$))

== Summary of Theory

We have seen how we can redefine univalence from a contractible fibre to a symmetric relation $sqr^top$. `Trocq` goes further to generalize this on a lattice. The parametricity witnesses of these relations have constraints $cal(D)$ which for arbitrary types is expressed as $cal(D)_square$. However primitive type constructs are more relaxed, thus the `Trocq` metaprogram computes the requirements for them. We then internalize the $sqr$ relation into a type theory by first handling identifications / equality of terms as judgements in the parametricity context $Xi$. We then augment it with $sqr$ and interaction with type information $Gamma$ which consequently requires a subtyping relation and down casting operator. Finally we can express our parametricity property of equality as an abstraction theorem in the framework of logical relations internalized in our type theory itself. Now we have a computational calculus to automate proof transfer for equivalent types and weaker relations too.