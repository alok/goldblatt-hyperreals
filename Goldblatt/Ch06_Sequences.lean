import Goldblatt.Ch06_Sequences.Convergence
import Goldblatt.Ch06_Sequences.LimSup
import Goldblatt.Ch06_Sequences.Series

/-!
# 6. Convergence of Sequences and Series

A real sequence $`s` is a function on the natural numbers, so it extends to a hypersequence
defined on the hypernatural numbers (Section 3.13). Its values at unlimited hypernaturals are
the _extended terms_ of the sequence, and together they form its _extended tail_. This
chapter shows that the classical notions of the theory of sequences are statements about the
extended tail, usually simpler ones than the standard definitions: a quantifier over
tolerances and a quantifier over indices are replaced by a single statement about
infinitely close numbers.

* The sequence converges to $`L` exactly when every extended term is infinitely close to
  $`L`.
* It is bounded exactly when every extended term is limited, and it diverges to infinity
  exactly when every extended term is positive unlimited.
* It is Cauchy exactly when all extended terms are infinitely close to one another.
* $`L` is a cluster point exactly when some extended term is infinitely close to $`L`.
* For a bounded sequence, the limit superior and the limit inferior are the largest and the
  smallest shadow of an extended term.
* A series converges exactly when its block sums between unlimited indices are infinitesimal.

From these characterisations the chapter derives the monotone convergence theorem, the
algebra of limits, Cauchy's criterion, the Bolzano-Weierstrass theorem, the standard facts
about limits superior and inferior, and the convergence tests for series.

Each characterisation is stated for the corresponding notion of Mathlib (convergence along
{name}`Filter.atTop`, {name}`CauchySeq`, {name}`MapClusterPt`, {name}`Filter.limsup`), so
that it can be used as a bridge in either direction. The proofs are nonstandard and follow
the book: where the book appeals to transfer for a particular sentence, the corresponding
fact is proved here from the almost-everywhere criteria of Chapter 3, using that an unlimited
hypernatural is the class of a sequence of natural numbers that tends to infinity along the
index ultrafilter.

The formalization of the chapter is split over three pages; this page is the overview and
the index.

## The three parts

* {lit}`Goldblatt.Ch06_Sequences.Convergence` covers Sections 6.1 to 6.7. It begins with a
  preliminary section on extended terms, which contains the two transfer principles used
  throughout: a property holds at all unlimited hypernaturals exactly when it holds from some
  standard index on, and at some unlimited hypernatural exactly when it holds at arbitrarily
  large standard indices. Then come Theorem 6.1.1, monotone convergence (Theorem 6.2.1) with
  the limit of the powers of a number between zero and one, uniqueness and algebra of limits
  (Theorem 6.3.1), boundedness and divergence (Theorems 6.4.1 and 6.4.2), Cauchy sequences
  (Theorems 6.5.1 and 6.5.2), cluster points and the Bolzano-Weierstrass theorem (Theorems
  6.6.1 and 6.6.2), and the exercises of Section 6.7.
* {lit}`Goldblatt.Ch06_Sequences.LimSup` covers Sections 6.8 and 6.9: the limit superior and
  inferior of a bounded sequence, Exercise 6.8.1 and Theorems 6.8.2 to 6.8.5, the definition
  for arbitrary sequences with values in the extended reals, the agreement of all of these
  with Mathlib's definitions, and the exercises of Section 6.9.
* {lit}`Goldblatt.Ch06_Sequences.Series` covers Sections 6.10 and 6.11: partial sums,
  hyperfinite sums and block sums, the Cauchy criterion for series, absolute convergence, and
  the eleven exercises, including the comparison tests, the geometric series, the ratio test
  and the alternating series test.

## The sections of the chapter

Each section of the book's chapter is a section of one of the three parts, under the same
number.

* 6.1 Convergence (part 1).
* 6.2 Monotone Convergence (part 1).
* 6.3 Limits (part 1).
* 6.4 Boundedness and Divergence (part 1).
* 6.5 Cauchy Sequences (part 1).
* 6.6 Cluster Points (part 1).
* 6.7 Exercises on Limits and Cluster Points (part 1).
* 6.8 Limits Superior and Inferior (part 2).
* 6.9 Exercises on lim sup and lim inf (part 2).
* 6.10 Series (part 3).
* 6.11 Exercises on Convergence of Series (part 3).

## Conventions and deviations

Sequences and series are indexed from zero, where the book indexes from one. The partial sum
with index $`n` is the sum of the first $`n` terms, so it corresponds to the book's
$`s_n`.

Three statements differ from the printed text, and each difference is explained at the
statement. Exercise 6.11(6) is false as printed when the ratios converge to zero; it is
proved for a nonzero limit, and a counterexample to the printed form is included. Exercise
6.11(8) assumes that the terms are nonzero, and the first inequality of its part (c) is strict
only from the second term on: it is proved in the weak form for every index and in the book's
strict form for every positive index. In the ratio tests the limits superior and inferior are taken in the extended
reals, so that an unbounded sequence of ratios has limit superior plus infinity.

## Names for later chapters

The lemma {name}`Goldblatt.tendsto_iff_forall_unlimited_infClose` is Theorem 6.1.1. Its
forward half is {name}`Goldblatt.hyperSeq_infClose_of_tendsto`. The extended tail of a sequence
is the set {name}`Goldblatt.extendedTail`. The transfer principles for the terms of a sequence
are {name}`Goldblatt.forall_unlimited_hyperSeq_mem_starSet_iff` and
{name}`Goldblatt.exists_unlimited_hyperSeq_mem_starSet_iff`, and unlimited hypernaturals are
reduced to sequences of natural numbers by
{name}`Goldblatt.exists_hnat_of_mem_unlimitedHyperNat`. The limits superior and inferior are
{name}`Goldblatt.limSup` and {name}`Goldblatt.limInf` for bounded sequences and
{name}`Goldblatt.limSupE` and {name}`Goldblatt.limInfE` in general, and the series notions are
{name}`Goldblatt.partialSum`, {name}`Goldblatt.SeriesSum`, {name}`Goldblatt.SeriesConverges`,
{name}`Goldblatt.hyperSum` and {name}`Goldblatt.hyperSumIcc`.
-/
