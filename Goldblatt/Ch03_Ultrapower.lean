import Goldblatt.Ch03_Ultrapower.Construction
import Goldblatt.Ch03_Ultrapower.Enlargement
import Goldblatt.Ch03_Ultrapower.Extension

/-!
# 3. Ultrapower Construction of the Hyperreals

Chapter 2 isolated the notion of a _large_ set of indices: a member of a fixed nonprincipal
ultrafilter on the natural numbers. This chapter uses it to build the hyperreal field. Two real
sequences are identified when they agree at almost all indices, and the set of equivalence
classes inherits addition, multiplication and order from the reals, one index at a time. The
result is an ordered field that contains a copy of the reals together with infinitesimal and
unlimited elements.

The recurring theme is the _almost-all criterion_: a statement about classes of sequences holds
exactly when the corresponding statement about their terms holds at almost all indices. Every
definition of the chapter (equality, order, membership of an enlarged set, the value of an
extended function, an enlarged relation) is an instance of it, and Chapter 4 turns it into the
transfer principle.

The formalization of the chapter is long, so it is split over three pages; this page is the
overview and the index.

## The three parts

* {lit}`Goldblatt.Ch03_Ultrapower.Construction` covers Sections 3.1 to 3.8: the ring of real
  sequences, agreement almost everywhere and its exercises, the notation of statement values
  and the Boolean laws for "almost all", the ultrapower as an ordered field (Theorem 3.6.1),
  the inclusion of the reals (Theorem 3.7.1), and the infinitesimal $`\varepsilon` and the
  unlimited $`\omega`.
* {lit}`Goldblatt.Ch03_Ultrapower.Enlargement` covers Sections 3.9 and 3.10: the enlargement
  of a set, the theorem that exactly the infinite sets have nonstandard members
  (Theorem 3.9.1), and the exercises on enlargements, together with the enlarged number
  systems of hypernatural, hyperinteger and hyperrational numbers.
* {lit}`Goldblatt.Ch03_Ultrapower.Extension` covers Sections 3.11 to 3.16: the extension of
  functions and its exercises, partial functions and hypersequences, the enlargement of
  relations of any finite arity and its exercises, and the discussion of uniqueness.

## The sections of the chapter

Each section of the book's chapter is a section of one of the three parts, under the same number.

* 3.1 The Ring of Real-Valued Sequences (part 1).
* 3.2 Equivalence Modulo an Ultrafilter (part 1).
* 3.3 Exercises on Almost-Everywhere Agreement (part 1).
* 3.4 A Suggestive Logical Notation (part 1).
* 3.5 Exercises on Statement Values (part 1).
* 3.6 The Ultrapower (part 1).
* 3.7 Including the Reals in the Hyperreals (part 1).
* 3.8 Infinitesimals and Unlimited Numbers (part 1).
* 3.9 Enlarging Sets (part 2).
* 3.10 Exercises on Enlargement (part 2).
* 3.11 Extending Functions (part 3).
* 3.12 Exercises on Extensions (part 3).
* 3.13 Partial Functions and Hypersequences (part 3).
* 3.14 Enlarging Relations (part 3).
* 3.15 Exercises on Enlarged Relations (part 3).
* 3.16 Is the Hyperreal System Unique? (part 3).

## Conventions of the formalization

* The index ultrafilter is Mathlib's {name}`Filter.hyperfilter` on the natural numbers, as fixed
  at the end of Chapter 2. "For almost all $`n`" is the Mathlib phrase
  {lit}`∀ᶠ n in hyperfilter ℕ, ...`.
* The hyperreals are Mathlib's {name}`Hyperreal`, written {lit}`ℝ*`, which is by definition the
  type of germs of real sequences along the hyperfilter. The class of a sequence is
  {name}`Hyperreal.ofSeq`. Section 3.6 shows that this is literally the quotient the book
  constructs.
* The book indexes sequences by $`1, 2, 3, \dots`; Lean's natural numbers start at $`0`. The
  sequence $`(1, \tfrac12, \tfrac13, \dots)` is therefore written $`n \mapsto 1/(n+1)`, and
  Mathlib's sample infinitesimal is the class of $`(0, 1, \tfrac12, \tfrac13, \dots)`, which
  differs from it by a shift and one term.
* Enlargement of sets, extension of functions and enlargement of relations are developed for an
  arbitrary type in place of the reals, because later chapters need the enlargements of the
  natural numbers, of sets of pairs, and so on. The ultrapower of a type is
  {name}`Goldblatt.Ultrapower`. The _star type_ of a type, the type in which its enlargements
  live, is named by the class {name}`Goldblatt.StarType`: it is the type of hyperreals for the
  reals and the ultrapower for every other type. All definitions and theorems are stated for an
  arbitrary star type, so one statement serves both.
* Consequently the enlargement {name}`Goldblatt.starSet` of a set of elements of a type does not
  have the fixed type "set of germs". For a set of reals it is a set of hyperreals, typed
  {lit}`Set ℝ*`. For a set in any other type, including the type of pairs of reals, the type of
  tuples of reals and the type of natural numbers, it is a set in the ultrapower
  {lit}`Ultrapower _` of that type. The hyperreals and the ultrapower of the reals are the same
  type by definition, and both instances use the identity identification, so nothing is lost;
  but statements should be written against the star type and not against a type of germs.
* The notation {lit}`⋆` elaborates its argument without looking at the type expected of the
  result, so the star type is always the one found by instance resolution from the type of the
  argument: writing a type ascription around {lit}`⋆A` does not change which star type is
  chosen, it only has to agree with it up to unfolding.
* The book's prefix star is the notation {lit}`⋆`: {lit}`⋆A` is the enlargement
  {name}`Goldblatt.starSet` of a set, {lit}`⋆f` the extension {name}`Goldblatt.starMap` of a
  function, and for a two-place function or relation it produces {name}`Goldblatt.starMap₂` or
  {name}`Goldblatt.starRel₂`. The enlarged number systems are {lit}`ℕ*`, {lit}`ℤ*` and
  {lit}`ℚ*`, subsets of the hyperreals.

## The almost-all toolkit

Later chapters prove statements about the ultrapower by choosing representing sequences and
reducing to a statement about almost all indices. The lemmas that carry this out are collected
here by name.

* Representatives: {name}`Goldblatt.hyperreal_exists_rep` for hyperreals,
  {name}`Goldblatt.Ultrapower.ofSeq_surjective` in general, and
  {name}`Goldblatt.Ultrapower.exists_rep_tuple` for tuples.
* Atomic statements: {name}`Goldblatt.ofSeq_eq_ofSeq_iff`, {name}`Goldblatt.ofSeq_lt_ofSeq_iff` and
  {name}`Goldblatt.ofSeq_le_ofSeq_iff` for hyperreals; {name}`Goldblatt.ofSeq_mem_starSet`,
  {name}`Goldblatt.starMap_ofSeq`, {name}`Goldblatt.starMap₂_ofSeq`,
  {name}`Goldblatt.starRel₂_ofSeq` and {name}`Goldblatt.starRel_ofSeq` in general.
* Connectives: {name}`Goldblatt.almostAll_and`, {name}`Goldblatt.almostAll_or`,
  {name}`Goldblatt.almostAll_not`, {name}`Goldblatt.almostAll_imp`,
  {name}`Goldblatt.almostAll_iff` and {name}`Goldblatt.almostAll_const`.
* Quantifiers: {name}`Goldblatt.almostAll_exists_iff` and
  {name}`Goldblatt.almostAll_forall_iff` on the side of sequences, and on the side of the
  ultrapower {name}`Goldblatt.exists_starRel₂_ofSeq`, {name}`Goldblatt.forall_starRel₂_ofSeq`
  and their bounded forms {name}`Goldblatt.exists_mem_starSet_starRel₂_ofSeq` and
  {name}`Goldblatt.forall_mem_starSet_starRel₂_ofSeq`.
-/
