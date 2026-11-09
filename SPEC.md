# Spec: a Lean 4 formalization of Goldblatt's *Lectures on the Hyperreals*

## Goal

Formalize, chapter by chapter, the definitions, theorems and exercises of
Robert Goldblatt, *Lectures on the Hyperreals: An Introduction to Nonstandard
Analysis* (Springer GTM 188, 1998) in Lean 4 on top of Mathlib, and publish the
result as a literate Verso site in which every chapter of the book is one page.

The library **is** the site: `lake query :literateHtml` renders each module's
module docs (`/-! ... -/`), declaration docstrings and code into a page.

## Non-goals

* Reproducing the book. The book is under copyright. Prose in this repository is
  original exposition written for this project; it cites the book by section and
  theorem number ("Goldblatt, Theorem 5.6.1") and never copies its sentences.
  The PDF and any text extracted from it are never committed.
* Re-proving Mathlib. Where Mathlib already has the object (`Filter`,
  `Ultrafilter`, `Hyperreal`, `Hyperreal.st`, ...), we use it and prove the
  book's statement about it, in the book's formulation.

## Model

Parts I–III work in the concrete ultrapower `ℝ* = Hyperreal =
(hyperfilter ℕ).Germ ℝ`, exactly the construction of the book's Chapter 3 with
index set `ℕ`. Enlargements `*A`, extensions `*f` and internal sets are germs
of sequences. Part IV (universes, superstructures, enlargements, saturation) is
developed in its own generality; Part V applies it.

## Layout

| Module | Book chapter |
|---|---|
| `Goldblatt.Ch01_WhatAreTheHyperreals` | 1 What Are the Hyperreals? (overview page) |
| `Goldblatt.Ch02_LargeSets` | 2 Large Sets |
| `Goldblatt.Ch03_Ultrapower` | 3 Ultrapower Construction of the Hyperreals |
| `Goldblatt.Ch04_Transfer` | 4 The Transfer Principle |
| `Goldblatt.Ch05_GreatAndSmall` | 5 Hyperreals Great and Small |
| `Goldblatt.Ch06_Sequences` | 6 Convergence of Sequences and Series |
| `Goldblatt.Ch07_Continuity` | 7 Continuous Functions |
| `Goldblatt.Ch08_Differentiation` | 8 Differentiation |
| `Goldblatt.Ch09_RiemannIntegral` | 9 The Riemann Integral |
| `Goldblatt.Ch10_Topology` | 10 Topology of the Reals |
| `Goldblatt.Ch11_InternalSets` | 11 Internal and External Sets |
| `Goldblatt.Ch12_InternalFunctions` | 12 Internal Functions and Hyperfinite Sets |
| `Goldblatt.Ch13_Universes` | 13 Universes and Frameworks |
| `Goldblatt.Ch14_Enlargements` | 14 The Existence of Nonstandard Entities |
| `Goldblatt.Ch15_Saturation` | 15 Permanence, Comprehensiveness, Saturation |
| `Goldblatt.Ch16_LoebMeasure` | 16 Loeb Measure |
| `Goldblatt.Ch17_Ramsey` | 17 Ramsey Theory |
| `Goldblatt.Ch18_Completion` | 18 Completion by Enlargement |
| `Goldblatt.Ch19_HyperfiniteApproximation` | 19 Hyperfinite Approximation |

A chapter that grows past ~1500 lines may be split into
`Goldblatt/ChNN_Name/Part.lean` submodules imported by the chapter module.

## Conventions

* Toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`, Verso `v4.35.0`.
* Everything lives in `namespace Goldblatt`. Files start with `import Mathlib`
  and imports of earlier chapters (no `module` keyword).
* `autoImplicit` is off. `doc.verso` is on, so module docs and docstrings are
  **Verso markup**, not Markdown:
  * inline math is ``$`\varepsilon \simeq 0` ``, display math is ``$$`...` ``
    (KaTeX);
  * refer to Lean names with ``{name}`Hyperreal.st` `` (checked) and to Lean
    terms with ``{lean}`(1 : ℝ*)` `` (elaborated); use ``{lit}`text` `` for
    literal code-styled text. Bare backticks produce a warning;
  * headings in module docs are `#`, `##`, ... and must nest without skipping
    levels; one `#` title per file;
  * `*bold*`, `_emph_`; characters such as `*`, `_`, `[`, `{`, `$` are markup
    and must be avoided or escaped in prose (write "star-A" or use math
    ``$`{}^*A` ``). The markup reference is
    `.lake/packages/verso/doc/UsersGuide/Markup.lean`.
* Each chapter module opens with a module doc: `# N. Chapter title`, a short
  original overview, and a `##` section per book section it formalizes.
  Sections of the file follow the book's order.
* Every formalized item has a docstring that begins with its book reference in
  bold, e.g. `**Theorem 5.6.1** (existence of shadows).`, followed by an
  original informal statement in mathematical English with KaTeX, and, where the
  Lean statement differs in shape from the book's, one sentence saying how.
* Names are descriptive Mathlib-style (`limited_iff_exists_shadow`), not
  numbered. Book numbering goes in the docstring.
* Proofs follow the book's nonstandard argument when practical (that is the
  point of the project); a proof by appeal to Mathlib's standard theorem is
  acceptable only for results the book itself assumes as known.

## Honesty rules

* No `axiom`, no `native_decide`, no `sorryAx` hidden behind `opaque`.
  Only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
* A statement must say what the book says. Never weaken a statement, add a
  hypothesis that trivialises it, or prove a vacuous variant to get a green
  build. If the book's statement is false or ambiguous as written, formalize
  the corrected statement and say so in the docstring.
* If a proof cannot be completed, leave the faithful statement with `sorry` and
  record it in the coverage ledger. A typed `sorry` is a specification; a
  weakened theorem is a lie.
* `COVERAGE.md` lists every numbered theorem, lemma, corollary and exercise of
  the book with its status: `proved`, `sorry`, `mathlib` (direct alias of an
  existing Mathlib result), `prose` (discussion with no formal content) or
  `omitted` (with reason).

## Done

* `lake build` succeeds with no errors.
* `lake query :literateHtml` produces the site; it is deployed to GitHub Pages.
* `COVERAGE.md` accounts for every numbered item of chapters 2–19.
* `#print axioms` on every chapter's theorems shows only standard axioms plus
  `sorryAx` exactly where the ledger says `sorry`.
