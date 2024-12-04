#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#let Ob(category) = $attach(br: category, upright(bold("Ob")))$
#let Hom(category,s:none,t:none) = $attach(br: category, upright(bold("Hom")))#if s != none and t != none { $(#s,#t)$ }$
#let arr(f,a,b) = $#f: #a -> #b$
#let comp = $compose$
#let iso = $tilde.equiv$
#let op(category) = $attach(tr: "op", category)$
#let slice(category,obj) = $#category slash #obj$
#let coslice(category,obj) = $#category backslash #obj$
#let Set = $upright(bold("Sets"))$
#let Rel = $upright(bold("Rel"))$
#let Mon = $upright(bold("Monoids"))$
#let Pos = $upright(bold("Posets"))$
#let dom = $upright(bold("dom"))$

// diagram macros
#let sstroke = 1pt + silver
#let corner-mark = (
  inherit: "straight",
  sharpness: 45deg,
  stroke: black,
  rev: false,
  
)
#let corner(..a) = edge(..a, stroke: white, marks: (corner-mark,))
