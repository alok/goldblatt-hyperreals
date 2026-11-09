import Goldblatt.Ch13_Universes.Sets
import Goldblatt.Ch13_Universes.Language
import Goldblatt.Ch13_Universes.Framework
import Goldblatt.Ch13_Universes.Internal
import Goldblatt.Ch13_Universes.Hyperfinite

/-!
# 13. Universes and Frameworks

Parts I to III of the book work inside one model, the ultrapower of the real numbers, and
every transfer argument there is in the end a computation with sequences modulo an
ultrafilter. Part IV starts again from an abstract standpoint. Its first chapter asks what a
"mathematical world" has to contain for analysis to be carried out inside it, answers with
the notion of a _universe_ (a strongly transitive set closed under pairs, unions and power
sets, built over a set of individuals), attaches to a universe a formal language in which all
quantifiers are bounded, and then defines a _nonstandard framework_: a map from one universe
to another that satisfies the transfer principle for that language. From then on nothing is
computed in a model. Standard, internal and external entities, the internal set definition
principle, hyperfinite sets and their internal cardinality are all defined and studied from
the transfer principle alone.

This chapter is the foundation for Chapters 14 to 19, so the notions are set up in full
generality and independently of the ultrapower of Parts I to III. Existence of frameworks is
not proved here; that is Chapter 14.

The formalization is long and is split over five pages; this page is the overview, the
record of the design decisions, and the index.

## The five parts

* {lit}`Goldblatt.Ch13_Universes.Sets` covers Sections 13.1 to 13.6: pairs, tuples, relations
  and functions as sets, strong transitivity, universes and every closure property in the
  book's list, superstructures, the proof that a superstructure is a universe and is the
  smallest one, and the existence of a superstructure over (a copy of) any set.
* {lit}`Goldblatt.Ch13_Universes.Language` covers Section 13.7: terms, formulas with bounded
  quantifiers, satisfaction, sentences, and the transform of a formula.
* {lit}`Goldblatt.Ch13_Universes.Framework` covers Sections 13.8 and 13.9: the structure
  {name}`Goldblatt.NonstandardFramework`, every preservation property of the transfer map in
  the book's list, Exercise 13.8.2, standard entities and Theorem 13.9.2.
* {lit}`Goldblatt.Ch13_Universes.Internal` covers Sections 13.10 to 13.12, 13.15 and 13.16:
  internal entities and Theorem 13.10.1, the internal set definition principle, every closure
  property of internal sets, Theorem 13.12.1 and the internal function definition principle.
* {lit}`Goldblatt.Ch13_Universes.Hyperfinite` covers what needs the real numbers among the
  individuals: the internal least number principle and internal induction, Theorem 13.14.1
  on external images, and hyperfinite sets with Theorem 13.17.1.

## The sections of the chapter

* 13.1 What Do We Need in the Mathematical World? (part 1).
* 13.2 Pairs Are Enough (part 1).
* 13.3 Actually, Sets Are Enough (part 1).
* 13.4 Strong Transitivity (part 1).
* 13.5 Universes (part 1).
* 13.6 Superstructures (part 1).
* 13.7 The Language of a Universe (part 2).
* 13.8 Nonstandard Frameworks (part 3).
* 13.9 Standard Entities (part 3; the examples with numbers in part 5).
* 13.10 Internal Entities (part 4).
* 13.11 Closure Properties of Internal Sets (part 4).
* 13.12 Transformed Power Sets (part 4; the applications to the natural numbers in part 5).
* 13.13 Exercises on Internal Sets and Functions (part 5).
* 13.14 External Images Are External (part 5).
* 13.15 Internal Set Definition Principle (part 4).
* 13.16 Internal Function Definition Principle (part 4).
* 13.17 Hyperfiniteness (part 5).
* 13.18 Exercises on Hyperfinite Sets and Sizes (part 5).
* 13.19 Hyperfinite Summation (part 5).
* 13.20 Exercises on Hyperfinite Sums (part 5).

## Design of the formalization

*Sets.* The ambient set theory is Mathlib's model {name}`ZFSet` of ZFC. Ordered pairs are
{name}`ZFSet.pair` (the Kuratowski pair), products are {name}`ZFSet.prod`, functions from one
set to another are {name}`ZFSet.IsFunc`, and the set of all of them is {name}`ZFSet.funs`.
Tuples of length other than two are functions on numerals, as in the book
({name}`Goldblatt.tuple`).

*Individuals.* The book's universes contain individuals, objects that are not sets and have
no members. {name}`ZFSet` has no such objects, so the formalization uses the condition the
book itself writes down in Section 13.5: an individual of a universe $`\mathbb U` is a
nonempty set none of whose members belongs to $`\mathbb U`
({name}`Goldblatt.IsIndividual`). Its members are invisible from inside $`\mathbb U`.
Everything else follows from taking this seriously.

* A _set of_ $`\mathbb U` is a member of $`\mathbb U` that is not an individual
  ({name}`Goldblatt.IsSetOf`). The closure axioms of a universe are stated for sets of
  $`\mathbb U`, as in the book, where uppercase letters are reserved for sets.
* Transitivity is read inside the universe ({name}`Goldblatt.TransitiveIn`): a transitive
  set contains the members, belonging to $`\mathbb U`, of its members.
* A superstructure is a universe over $`X` when the members of $`X` are individuals relative
  to it ({name}`Goldblatt.IsBaseSet`). In the book this holds by decree. Here it is a
  hypothesis, and {name}`Goldblatt.exists_isBaseSet` shows that every type has a copy in
  {name}`ZFSet` satisfying it.
* A binary relation of a universe is a set of pairs of members of the universe
  ({name}`Goldblatt.RelIn`). This excludes an individual that happens to be a pair of
  invisible objects, a case that cannot arise in the book.
* The positive integers that index tuples are von Neumann numerals
  ({name}`Goldblatt.num`). Every universe contains them, so the book's standing assumption
  that a universe contains the positive integers is not needed, and they are fixed by every
  transfer map.

*Language.* The language of a universe is a deep embedding: inductive types
{name}`Goldblatt.Term` and {name}`Goldblatt.Formula`, with satisfaction
{name}`Goldblatt.Sat` defined by recursion. Bounded quantifiers range over the members of the
bound that belong to the universe. This is what makes the book's sentence "every member of
$`X` is nonempty and has no members" true, and it agrees with the plain reading whenever the
bound is a set of the universe. An atomic formula containing an undefined term is false; the
book instead restricts attention to defined sentences, and the two conventions agree on
formulas whose terms are always defined.

*Frameworks.* {name}`Goldblatt.NonstandardFramework` is a structure whose fields are the
book's axioms: a universe over $`X`, a second universe, a map between them that fixes the
members of $`X` and the empty set, and transfer for all sentences of the deep embedding.
Every result of Sections 13.8 to 13.17 is proved from these fields. Where the book assumes
that the real numbers are individuals, the structure {name}`Goldblatt.RealFramework` adds an
injection of the reals into $`X`.

*Sentences that had to be adjusted.* In two proofs the sentence the book transfers is true
only if a quantified entity is a set and not an individual: the proof of Theorem 13.12.1 and
the second half of the proof of Theorem 13.17.1. The formal proofs transfer the sentence with
the clause "$`x` is empty or has a member" added. The theorems themselves are unchanged.

*Internal definition principles.* The internal set and function definition principles are
proved in two forms. In the parameter form the formula or term is the transform of one from
the language of $`\mathbb U`, with internal entities assigned to its free variables
({name}`Goldblatt.NonstandardFramework.internal_sep`,
{name}`Goldblatt.NonstandardFramework.internal_of_term`); this is the form used in
applications. The book's form, for a formula or term of the language of $`\mathbb U'` whose
constants are internal, follows by replacing the constants by variables, which is how the
book's proof begins ({name}`Goldblatt.NonstandardFramework.internal_sep_of_internal_consts`,
{name}`Goldblatt.NonstandardFramework.internal_of_term_of_internal_consts`).

*What is not formalized.* The book defines the sum of an internal function over a
hyperfinite set as the sum of the set of its values, which is the intended sum only for
injective functions. The sum of a hyperfinite set of hyperreals is defined here
({name}`Goldblatt.RealFramework.hsum`), but the sum of a function and the exercises of
Section 13.20 about it are not. Also not formalized: Exercise 13.13 (2), Exercise 13.18 (4),
and the examples of Sections 13.8 and 13.9 about sets and intervals of real numbers,
including Exercise 13.9.1.
-/
