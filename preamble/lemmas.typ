#import "@preview/lemmify:0.1.6": *
#import "@preview/showybox:2.0.1": showybox

// Define default theorem environments.
#let (
  theorem, lemma, corollary,
  remark, proposition, example,
  proof, definition, rules: thm-rules
) = default-theorems(
  "thm-group",
  lang: "en",
  thm-numbering: thm-numbering-heading.with(max-heading-level: 1)
)

#let exercise(name, body) = showybox(
  frame: (
    border-color: silver,
  ) 
)[
#underline(smallcaps([Exercise #name:])) #body
]