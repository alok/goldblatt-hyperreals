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

Everything in this chapter lives in the namespace {lit}`Goldblatt.Transfer`, because Chapter 13
defines a second formal language, for universes, whose terms and formulas would otherwise
have the same names.

## The three parts

* {lit}`Goldblatt.Ch04_Transfer.Language` covers Sections 4.2 to 4.4: relational structures,
  the full structure and its enlargement, Exercise 4.2.1, the terms and formulas of the
  language with bounded quantifiers, what a term names, defined formulas, truth, sentences,
  substitution of constants, and the star-transform.
* {lit}`Goldblatt.Ch04_Transfer.Los` covers Sections 4.6 and 4.5, in that order: the theorem of
  Łoś for terms and formulas, and from it the transfer principle, transfer with parameters,
  universal transfer and existential transfer.
* {lit}`Goldblatt.Ch04_Transfer.Applications` covers the examples: the illustrations of
  Sections 4.3 and 4.4, the six examples of Section 4.1 with Exercise 4.1.1, the examples of
  Section 4.5 with Exercise 4.5.1, the substitution example of Section 4.6, and the three points
  of Section 4.7. Exercise 4.4.1 is
  answered throughout that page, by the lemmas that compute the star-transform of each example.

The order of the parts is the order of logical dependence, not the order of the book: the book
opens with examples, states transfer, and justifies it last, while here the language comes
first, then the theorem of Łoś, then transfer, and the examples are proved at the end by
applying it. The sections below follow the book's numbering and say where each is formalized.

## 4.1 Transforming Statements

Six statements about the reals and their counterparts about the hyperreals: the
Eudoxus–Archimedes principle ({name}`Goldblatt.Transfer.exists_hyperNat_gt`, and
{name}`Goldblatt.Transfer.exists_hyperNat_gt'` for the book's first formulation), density of the rationals
({name}`Goldblatt.Transfer.exists_hyperRat_btwn`), finiteness
({name}`Goldblatt.Transfer.starSet_of_finite_by_transfer`), finitary set operations
({name}`Goldblatt.Transfer.starSet_union_by_transfer`), discreteness of the natural numbers
({name}`Goldblatt.Transfer.hyperNat_eq_or_eq_add_one`, {name}`Goldblatt.Transfer.one_le_of_mem_starSet_posNat`)
and unbounded sets ({name}`Goldblatt.Transfer.exists_gt_of_exists_unlimited_mem_starSet`). These same
theorems answer Exercise 4.1.1. They are in part 3, proved by transfer.

## 4.2 Relational Structures

{name}`Goldblatt.Transfer.RelStructure`, the full structure {name}`Goldblatt.Transfer.RelStructure.full` and the
enlarged structure {name}`Goldblatt.Transfer.RelStructure.star`, with Exercise 4.2.1
({name}`Goldblatt.Transfer.unaryRel_image_of_notMem_star`,
{name}`Goldblatt.Transfer.number_systems_ne_starSet`). Part 1.

## 4.3 The Language of a Relational Structure

Terms and formulas ({name}`Goldblatt.Transfer.Term`, {name}`Goldblatt.Transfer.Formula`), what a term names
({name}`Goldblatt.Transfer.Term.Names`), defined terms and formulas, sentences
({name}`Goldblatt.Transfer.Formula.IsSentence`), the truth conditions ({name}`Goldblatt.Transfer.Formula.Holds`,
{name}`Goldblatt.Transfer.Formula.isTrue_all_iff`, {name}`Goldblatt.Transfer.Formula.isTrue_ex_iff`) and the
language of a structure ({name}`Goldblatt.Transfer.Formula.Over`). Part 1; the book's two illustrations,
of free and bound occurrences ({name}`Goldblatt.Transfer.freeBoundExample'`) and of an undefined term
({name}`Goldblatt.Transfer.isTrue_tanOddSentence`), are in part 3.

## 4.4 Star-Transforms

The transform {name}`Goldblatt.Transfer.Formula.star`, the fact that it lands in the language of the
enlarged structure ({name}`Goldblatt.Transfer.Formula.star_over`), and the lemmas that justify dropping
the stars from familiar symbols. Part 1. The two transforms the book displays
({name}`Goldblatt.Transfer.holds_star_pi_lt_app`, {name}`Goldblatt.Transfer.holds_star_sin_exp_mem_rat`) and
Exercise 4.4.1 are in part 3.

## 4.5 The Transfer Principle

{name}`Goldblatt.Transfer.Formula.transfer`, with {name}`Goldblatt.Transfer.Formula.universal_transfer` and
{name}`Goldblatt.Transfer.Formula.existential_transfer`, in part 2. The examples are in part 3: the field
axioms, the enlargement of an interval, identities between extended functions, the bounded
sequence ({name}`Goldblatt.Transfer.bounded_of_hyperSeq_limited`), and Exercise 4.5.1, for which every
assertion of Exercises 3.10 is proved again by transfer.

## 4.6 Justifying Transfer

The theorem of Łoś, {name}`Goldblatt.Transfer.Formula.los`, proved by induction on formulas, and the
almost-all criteria of Chapter 3 recovered as its atomic cases. Part 2, where it precedes
Section 4.5 because transfer is deduced from it. The section's example of substitution
notation, with the theorem of Łoś applied to it
({name}`Goldblatt.Transfer.isTrue_star_sumSquaresFormula_subst_ofSeq`), is in part 3.

## 4.7 Extending Transfer

Transfer for other structures ({name}`Goldblatt.Transfer.transfer_complex`); sentences with nonstandard
constants, which belong to the language of the enlarged structure but are not transforms
({name}`Goldblatt.Transfer.omegaBoundSentence_over`, {name}`Goldblatt.Transfer.omegaBoundSentence_ne_star`,
{name}`Goldblatt.Transfer.Formula.consts_star_subset`); and Dedekind completeness, each instance of which
transfers ({name}`Goldblatt.Transfer.exists_isLUB_starSet`) while the statement about all sets fails
({name}`Goldblatt.Transfer.not_dedekindComplete_hyperreal`), so that no formula expresses completeness
in both structures ({name}`Goldblatt.Transfer.no_formula_expresses_dedekind`). Part 3.

## The main results

* The language: {name}`Goldblatt.Transfer.Term`, {name}`Goldblatt.Transfer.Formula`, with semantics
  {name}`Goldblatt.Transfer.Term.Names`, {name}`Goldblatt.Transfer.Formula.Defined` and
  {name}`Goldblatt.Transfer.Formula.Holds`, and the star-transform {name}`Goldblatt.Transfer.Formula.star`.
* The theorem of Łoś: {name}`Goldblatt.Transfer.Formula.los`, with its two halves
  {name}`Goldblatt.Transfer.Formula.holds_star_germ` and {name}`Goldblatt.Transfer.Formula.defined_star_germ`.
* The transfer principle: {name}`Goldblatt.Transfer.Formula.transfer`, and its companions
  {name}`Goldblatt.Transfer.Formula.transfer_defined`, {name}`Goldblatt.Transfer.Formula.holds_star_of`,
  {name}`Goldblatt.Transfer.Formula.universal_transfer` and
  {name}`Goldblatt.Transfer.Formula.existential_transfer`.

## Conventions of the formalization

* Everything is done for an arbitrary type and its star type in the sense of Chapter 3. For the
  reals the star type is the type of hyperreals, and the enlargements and extensions that
  interpret the starred symbols are those of Chapter 3: {name}`Goldblatt.starSet` for the bound
  of a quantifier, {name}`Goldblatt.starRel` for a relation symbol and
  {name}`Goldblatt.starMapOnN` for a function symbol.
* There is one type of formulas for each universe, namely the language of the full structure on
  it. The star-transform maps formulas over a type to formulas over its star type, and its
  values lie in the language of the enlarged structure
  ({name}`Goldblatt.Transfer.Formula.star_over`). Truth in the enlarged structure is truth of a formula
  over the star type; no second definition of truth is needed.
* Variables are named by natural numbers, and a quantifier names the variable it binds. Where
  the book substitutes constants for free variables, we give the variables values; the two agree
  ({name}`Goldblatt.Transfer.Formula.holds_subst`). A valuation may leave variables without a value,
  which is how "closed term" and "defined formula" are expressed.
* The book's transfer principle is stated for defined sentences. The theorems here need neither
  hypothesis: they hold for every formula, evaluated under the empty valuation, and say in
  addition that a sentence is defined if and only if its transform is.
* A function symbol is a partial function: a domain together with a function on it. Total
  functions are the case in which the domain is everything, and the notation of Section 4.3 for
  them is provided separately.
-/
