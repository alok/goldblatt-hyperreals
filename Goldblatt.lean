import Goldblatt.Ch01_WhatAreTheHyperreals
import Goldblatt.Ch02_LargeSets
import Goldblatt.Ch03_Ultrapower
import Goldblatt.Ch04_Transfer
import Goldblatt.Ch05_GreatAndSmall
import Goldblatt.Ch06_Sequences
import Goldblatt.Ch07_Continuity
import Goldblatt.Ch11_InternalSets
import Goldblatt.Ch12_InternalFunctions
import Goldblatt.Ch13_Universes
import Goldblatt.Ch14_Enlargements
import Goldblatt.Ch17_Ramsey

/-!
# Lectures on the Hyperreals, formalized

This site is a Lean 4 formalization, on top of Mathlib, of Robert Goldblatt's
_Lectures on the Hyperreals: An Introduction to Nonstandard Analysis_
(Springer Graduate Texts in Mathematics 188, 1998). Every page is a Lean module:
the prose you read is the module's documentation and the statements and proofs
underneath it are checked by Lean each time the site is built.

The exposition here is original and cites the book by section and theorem number;
it is a companion to the book, not a replacement for it.

## How to read it

Each chapter of the book is one page (long chapters have sub-pages). Within a page
the sections follow the book's order, and every definition, theorem and exercise
carries its book number in bold at the start of its description. Hover over any
name in the code to see its type, and click it to jump to its definition.

The hyperreals of Parts I to III are the concrete ultrapower
$`{}^*\mathbb{R} = \mathbb{R}^{\mathbb{N}} / \mathcal{F}` for a nonprincipal
ultrafilter $`\mathcal{F}` on $`\mathbb{N}`, which is Mathlib's {name}`Hyperreal`.

## Chapters

*Part I: Foundations*

1. [What Are the Hyperreals?](Goldblatt/Ch01_WhatAreTheHyperreals/)
2. [Large Sets](Goldblatt/Ch02_LargeSets/)
3. [Ultrapower Construction of the Hyperreals](Goldblatt/Ch03_Ultrapower/)
4. [The Transfer Principle](Goldblatt/Ch04_Transfer/)
5. [Hyperreals Great and Small](Goldblatt/Ch05_GreatAndSmall/)

*Part II: Basic Analysis*

6. [Convergence of Sequences and Series](Goldblatt/Ch06_Sequences/)
7. [Continuous Functions](Goldblatt/Ch07_Continuity/)
8. Differentiation (in progress)
9. The Riemann Integral (in progress)
10. Topology of the Reals (in progress)

*Part III: Internal and External Entities*

11. [Internal and External Sets](Goldblatt/Ch11_InternalSets/)
12. [Internal Functions and Hyperfinite Sets](Goldblatt/Ch12_InternalFunctions/)

*Part IV: Nonstandard Frameworks*

13. [Universes and Frameworks](Goldblatt/Ch13_Universes/)
14. [The Existence of Nonstandard Entities](Goldblatt/Ch14_Enlargements/)
15. Permanence, Comprehensiveness, Saturation (in progress)

*Part V: Applications*

16. Loeb Measure (in progress)
17. [Ramsey Theory](Goldblatt/Ch17_Ramsey/)
18. Completion by Enlargement (in progress)
19. Hyperfinite Approximation (in progress)

## What is checked

The library uses no axioms beyond Lean's three standard ones, and a statement that
could not be proved is left with an explicit {lit}`sorry` rather than weakened.
The repository's {lit}`COVERAGE.md` lists every numbered item of the book with its
status.
-/
