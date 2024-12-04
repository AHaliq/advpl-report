#import "lemmas.typ": *

#let std-bibliography = bibliography

#let setup(
  title,
  author,
  authorid: "",
  subtitle: "",
  date: datetime.today(),
  preface: none,
  table-of-contents: outline(),
  bibliography: none,
  body,
) = {
  set text(lang: "en")
  set page(paper: "a4")
  set document(title: title, author: author)
  set text(font: ("Libertinus Serif", "Linux Libertine"), size: 11pt)
  // preamble
  
  page([
    #align(left + horizon, block(width: 90%)[
      #let v-space = v(2em, weak: true)
      #text(3em)[*#title*]

      #v-space
      #text(1.6em, subtitle)
      #grid(
        columns: (auto, 1fr),
        align: (left + horizon, left + horizon),
        text(
          size: 1.2em,
          font: ("AU Passata"),
        )[#upper[*Aarhus Universitet* #h(0.3em)]],
        image("../resources/au_logo_black.png", width: 0.7cm)
      )
    ])
    #align(left + bottom, block(width: 90%)[
      #grid(
        columns: (auto, 1fr),
        align: (left + horizon, left + horizon),
        text(1.4em)[#author #h(0.5em)],
        text(1.2em)[[#raw(authorid)]]
      )
      

      #if date != none {
        // Display date as MMMM DD, YYYY
        text(date.display("[month repr:long] [day padding:zero], [year repr:full]"))
      }
    ])
  ])
  // cover page

  if preface != none {
    page(
      align(center + horizon)[#preface]
    )
  }
  // preface page

  set outline(
    indent: auto,
    fill: box(width: 1fr, repeat[#text(silver)[-]])
  )
  if table-of-contents != none {
    table-of-contents
  }
  // table of contents

  set page(
    footer: context {
      // Get current page number.
      let i = counter(page).at(here()).first()

      // Align right for even pages and left for odd.
      let is-odd = calc.odd(i)
      let aln = if is-odd { right } else { left }

      // Are we on a page that starts a chapter?
      let target = heading.where(level: 1)
      if query(target).any(it => it.location().page() == i) {
        return align(aln)[#i]
      }

      // Find the chapter of the section we are currently in.
      let before = query(target.before(here()))
      if before.len() > 0 {
        let current = before.last()
        let gap = 1.75em
        let chapter = upper(text(size: 0.68em, current.body))
        if is-odd {
          align(aln)[#chapter #h(gap) #i]
        } else {
          align(aln)[#i #h(gap) #chapter]
        }
      }
    }
  )
  
  {
    // Custom Heading Styling
    set heading(numbering: "1.1.1")
    show heading.where(level: 1): it => {
      colbreak(weak: true)
      [§#counter(heading).display() #it.body]
    }
    // Custom Table Styling
    set table(
      fill: (x,y) => if y == 0 {
        silver
      },
      stroke: (x,y) => if x == 0 and y == 1 {(
        top: (thickness: 1pt, paint:silver),
        right: (thickness: 1pt, paint:silver)
      )} else if y == 1 {(
        top: (thickness: 1pt, paint:silver)
      )} else if x == 0 {(
        right: (thickness: 1pt, paint:silver)
      )} else if y > 1 {(
        top: (thickness: 1pt, paint:silver)
      )},
      inset: 7pt,
    )
    show table.cell.where(y: 0): smallcaps
    
    // Setup lemmify
    show: thm-rules

    body
  }

  // Display bibliography.
  if bibliography != none {
    pagebreak()
    show std-bibliography: set text(0.85em)
    // Use default paragraph properties for bibliography.
    show std-bibliography: set par(leading: 0.65em, justify: false, linebreaks: auto)
    bibliography
  }
  // bibliography
}