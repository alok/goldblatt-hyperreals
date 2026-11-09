import Goldblatt.Ch04_Transfer.Language
import Goldblatt.Ch04_Transfer.Los
import Goldblatt.Ch04_Transfer.Applications

/-!
# 4. The Transfer Principle

Chapter 3 built the hyperreals as an ultrapower and, one notion at a time, extended sets,
functions and relations from the reals to the hyperreals by the almost-all criterion. This
chapter explains what all those extensions have in common: any statement about the reals that
can be written in a suitable formal language is true if and only if the corresponding statement
about the hyperreals, its _star-transform_, is true. This is the transfer principle. Once it is
available, the ultrapower can be forgotten: the following chapters use only that the hyperreals
are an ordered field extending the reals, that they contain unlimited numbers, and that transfer
holds.

The book states the transfer principle and the theorem of Łoś that underlies it, and argues for
them by examples. Here both are proved. The formal language is defined as a datatype, its truth
conditions are the book's, including the conventions about partial functions and undefined
terms, the star-transform is a function on formulas, and the theorem of Łoś is proved by
induction on formulas from the almost-all toolkit of Chapter 3. The worked examples and
exercises of the chapter are then formal sentences, settled by applying the transfer theorem.

The formalization is split over three pages; this page is the overview and the index.

## The three parts

* {lit}`Goldblatt.Ch04_Transfer.Language` covers Sections 4.2 to 4.4: relational structures,
  the full structure and its enlargement, Exercise 4.2.1, the terms and formulas of the
  language with bounded quantifiers, what a term names, defined formulas, truth, sentences,
  substitution of constants, and the star-transform.
* {lit}`Goldblatt.Ch04_Transfer.Los` covers Sections 4.6 and 4.5, in that order: the theorem of
  Łoś for terms and formulas, and from it the transfer principle, transfer with parameters,
  universal transfer and existential transfer.
* {lit}`Goldblatt.Ch04_Transfer.Applications` covers the examples: the illustrations of
  Section 4.3, the six examples of Section 4.1 with Exercise 4.1.1, the examples of Section 4.5
  with Exercise 4.5.1, and the three points of Section 4.7. Exercise 4.4.1 is answered
  throughout that page, by the lemmas that compute the star-transform of each example.

## The sections of the chapter

* 4.1 Transforming Statements (part 3). It opens the book's chapter as motivation; here it
  comes after the theory, because its examples are proved by transfer.
* 4.2 Relational Structures (part 1).
* 4.3 The Language of a Relational Structure (part 1; examples in part 3).
* 4.4 Star-Transforms (part 1; Exercise 4.4.1 in part 3).
* 4.5 The Transfer Principle (the principle in part 2; the examples in part 3).
* 4.6 Justifying Transfer (part 2).
* 4.7 Extending Transfer (part 3).

## The main results

* The language: {name}`Goldblatt.Term`, {name}`Goldblatt.Formula`, with semantics
  {name}`Goldblatt.Term.Names`, {name}`Goldblatt.Formula.Defined` and
  {name}`Goldblatt.Formula.Holds`, and the star-transform {name}`Goldblatt.Formula.star`.
* The theorem of Łoś: {name}`Goldblatt.Formula.los`, with its two halves
  {name}`Goldblatt.Formula.holds_star_germ` and {name}`Goldblatt.Formula.defined_star_germ`.
* The transfer principle: {name}`Goldblatt.Formula.transfer`, and its companions
  {name}`Goldblatt.Formula.transfer_defined`, {name}`Goldblatt.Formula.holds_star_of`,
  {name}`Goldblatt.Formula.universal_transfer` and
  {name}`Goldblatt.Formula.existential_transfer`.

## Conventions of the formalization

* Everything is done for an arbitrary type and its star type in the sense of Chapter 3. For the
  reals the star type is the type of hyperreals, and the enlargements and extensions that
  interpret the starred symbols are those of Chapter 3: {name}`Goldblatt.starSet` for the bound
  of a quantifier, {name}`Goldblatt.starRel` for a relation symbol and
  {name}`Goldblatt.starMapOnN` for a function symbol.
* There is one type of formulas for each universe, namely the language of the full structure on
  it. The star-transform maps formulas over a type to formulas over its star type, and its
  values lie in the language of the enlarged structure
  ({name}`Goldblatt.Formula.star_over`). Truth in the enlarged structure is truth of a formula
  over the star type; no second definition of truth is needed.
* Variables are named by natural numbers, and a quantifier names the variable it binds. Where
  the book substitutes constants for free variables, we give the variables values; the two agree
  ({name}`Goldblatt.Formula.holds_subst`). A valuation may leave variables without a value,
  which is how "closed term" and "defined formula" are expressed.
* The book's transfer principle is stated for defined sentences. The theorems here need neither
  hypothesis: they hold for every formula, evaluated under the empty valuation, and say in
  addition that a sentence is defined if and only if its transform is.
* A function symbol is a partial function: a domain together with a function on it. Total
  functions are the case in which the domain is everything, and the notation of Section 4.3 for
  them is provided separately.
-/
