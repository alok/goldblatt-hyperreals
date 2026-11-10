import Goldblatt.Ch16_LoebMeasure.Rings
import Goldblatt.Ch16_LoebMeasure.Outer
import Goldblatt.Ch16_LoebMeasure.Loeb
import Goldblatt.Ch16_LoebMeasure.Internal
import Goldblatt.Ch16_LoebMeasure.Lebesgue

/-!
# 16. Loeb Measure

A measure in the standard sense lives on a collection of sets that is closed under countable
unions. An internal collection of sets is almost never closed in that way: by countable
saturation, a countable union of internal sets is internal only when it is already the union
of finitely many of them. Loeb's observation is that this failure is exactly what is needed to
build standard measures out of internal ones. If an internal function on an internal ring of
sets is finitely additive, then taking shadows of its values gives a real-valued function for
which countable additivity on the ring holds for free, because the only countable disjoint
unions that stay in the ring are finite unions with empty tails. The classical extension
procedure of Carathéodory then turns it into a complete countably additive measure on a
sigma-algebra: the _Loeb measure_.

The chapter reviews the measure theory it needs (rings and algebras of sets, measures on
rings, outer measures, Lebesgue measure), constructs Loeb measures, characterises the Loeb
measurable sets as the sets that can be approximated from inside and outside by internal sets,
and ends with the representation of Lebesgue measure on the real line by a counting measure
with infinitesimal weights on a hyperfinite grid.

## Design decision: the ultrapower as the saturated enlargement

The book works in an arbitrary countably saturated enlargement of a universe. This chapter is
formalized in the concrete ultrapower over the natural numbers of Chapters 3, 11 and 12, which
is countably saturated ({name}`Goldblatt.iInter_nonempty_of_isInternalSet`, Theorem 11.10.1).
The consequences are these.

* An internal set is the class of a sequence of sets, an internal ring of internal sets is
  the class of a sequence of rings, and an internal finitely additive function is the class of
  a sequence of finitely additive functions ({name}`Goldblatt.InternalMeasure`). The values of
  an internal measure are classes of sequences of extended nonnegative reals
  ({name}`Goldblatt.HyperENNReal`), and the shadow of such a value is the limit of the sequence
  along the index ultrafilter ({name}`Goldblatt.loebSh`); on limited hyperreals this is the
  shadow of Chapter 5 and on unlimited ones it is $`\infty`
  ({name}`Goldblatt.loebSh_of_limited`, {name}`Goldblatt.loebSh_of_posUnlimited`), as in the
  book.
* The book's appeals to sequential comprehensiveness and overflow (Lemmas 16.5.1 and 16.6.2)
  are replaced by direct appeals to countable saturation, applied to internal sets of sets.
  The three facts about an internal measure space that the measure theory needs are collected
  in the structure {name}`Goldblatt.LoebPremeasure`; Sections 16.5 to 16.7 are proved from
  that structure alone, and {name}`Goldblatt.InternalMeasure.toLoebPremeasure` shows that
  every internal measure in the ultrapower provides one.
* The Loeb measure is a genuine Mathlib measure,
  {name}`Goldblatt.LoebPremeasure.loebMeasure`, on the Mathlib measurable space
  {name}`Goldblatt.LoebPremeasure.loebSpace` of Loeb measurable sets. Rings, measures on rings
  and outer measures are stated in the book's form and tied to Mathlib's
  {name}`MeasureTheory.IsSetRing`, {name}`MeasurableSpace`,
  {name}`MeasureTheory.OuterMeasure` and Carathéodory measurability. Lebesgue measurability in
  the book's sense is proved equivalent to null-measurability for Mathlib's Lebesgue measure
  ({name}`Goldblatt.lebesgueMeasurable_iff_nullMeasurableSet`).
* A hypernatural is the class of a sequence of natural numbers, and the grid of Section 16.8
  is built from such a sequence; {name}`Goldblatt.exists_grid_representation` restates the
  final theorem for an arbitrary unlimited hypernatural.

Three statements of the book are corrected, each with a note in the docstring: the covering
property of the outer measure needs a set of finite outer measure
({name}`Goldblatt.exists_monotone_cover`), the squeezing property of complete measures needs
finite measure ({name}`Goldblatt.isCaratheodory_of_between`), and Lemma 16.5.1 holds for every
set, measurable or not ({name}`Goldblatt.LoebPremeasure.outer_eq_iInf`). The book has no
exercises in this chapter.

## The five parts

* {lit}`Goldblatt.Ch16_LoebMeasure.Rings`: Sections 16.1 and 16.2.
* {lit}`Goldblatt.Ch16_LoebMeasure.Outer`: Sections 16.3 and 16.4.
* {lit}`Goldblatt.Ch16_LoebMeasure.Loeb`: Sections 16.5, 16.6 and 16.7, from the three
  saturation properties.
* {lit}`Goldblatt.Ch16_LoebMeasure.Internal`: internal measures in the ultrapower, the
  saturation properties, and the examples of Sections 16.1 and 16.2 that involve internal sets.
* {lit}`Goldblatt.Ch16_LoebMeasure.Lebesgue`: Section 16.8.

## 16.1 Rings and Algebras

Part 1 defines rings, algebras, sigma-rings and sigma-algebras of sets
({name}`Goldblatt.IsRingOfSets`, {name}`Goldblatt.IsAlgebraOfSets`,
{name}`Goldblatt.IsSigmaRing`, {name}`Goldblatt.IsSigmaAlgebra`), the generated sigma-algebra
({name}`Goldblatt.sigmaGenerated`), and proves the first four examples: finite, cofinite and
countable sets, the ring of finite unions of left-open intervals
({name}`Goldblatt.leftOpenRing`) and the Borel sets. Part 4 has the two examples about
internal sets. The internal subsets of the hyperfinite set of hypernaturals from $`1` to
$`N` form an algebra of subsets of it
({name}`Goldblatt.isRingOfSets_internal_subsets`,
{name}`Goldblatt.setOf_hyperNat_one_le_le_mem_internal_subsets`) that is not a sigma-algebra
({name}`Goldblatt.not_isSigmaRing_internal_subsets`). If the union of a sequence of members of
an internal ring is in the ring, then finitely many terms already have that union
({name}`Goldblatt.InternalMeasure.exists_iUnion_eq_biUnion_le_of_mem_sets`), so the union of
a strictly increasing sequence, or of a pairwise disjoint sequence with infinitely many
nonempty terms, is not in the ring
({name}`Goldblatt.InternalMeasure.iUnion_notMem_sets_of_ssubset`,
{name}`Goldblatt.InternalMeasure.iUnion_notMem_sets_of_pairwise_disjoint`). The enlargement of
an algebra is an algebra ({name}`Goldblatt.InternalMeasure.isAlgebraOfSets_sets`), and the
star-Borel sets are an algebra that is not a sigma-algebra
({name}`Goldblatt.InternalMeasure.not_isSigmaRing_sets_starBorel`). The closure of the
enlargement of a sigma-algebra under unions of internal sequences is not formalized.

## 16.2 Measures

Part 1 defines finitely additive functions and measures on a ring
({name}`Goldblatt.IsFinitelyAdditive`, {name}`Goldblatt.IsMeasureOnRing`) and proves the
listed consequences: finite additivity, monotonicity, subtractivity, continuity along
increasing sequences, and the examples of the counting measure and of Lebesgue measure on
intervals. Parts 3 and 4 have the nonstandard examples: the shadow of an internal finitely
additive function is a measure on its internal ring
({name}`Goldblatt.LoebPremeasure.isMeasureOnRing`,
{name}`Goldblatt.InternalMeasure.isMeasureOnRing_μL`), the weighted counting functions on a
hyperfinite set ({name}`Goldblatt.InternalMeasure.weighted`) and their expression as
hyperfinite sums in the sense of Section 12.7
({name}`Goldblatt.InternalMeasure.μ_weighted_eq_internalSum`), the fact that every internal
finitely additive function on the internal subsets of a hyperfinite set is one of them
({name}`Goldblatt.InternalMeasure.μ_eq_μ_weighted_singleton`), and the normalised counting
measure ({name}`Goldblatt.InternalMeasure.counting`) with its formula in terms of internal
cardinalities ({name}`Goldblatt.InternalMeasure.μ_counting_eq_internalCard`). That the extended
shadow is the function the book defines by cases on the whole enlargement of
$`[0, \infty]` is {name}`Goldblatt.loebSh_eq_top_or_exists`.

## 16.3 Outer Measures

Part 2 defines the outer measure of a function on a ring ({name}`Goldblatt.ringOuter`) with
the book's formula ({name}`Goldblatt.ringOuter_apply`) and proves the listed properties:
agreement with the measure on the ring, monotonicity, countable subadditivity, increasing
covers, the reduction of measurability to sets of finite outer measure, measurability of the
members of the ring and of null sets, countable additivity and completeness on the measurable
sets ({name}`Goldblatt.caratheodoryMeasure`), uniqueness of the extension of a
sigma-finite measure ({name}`Goldblatt.measure_eq_ringOuter`), and the two consequences of
completeness for sets squeezed between measurable sets of equal finite measure
({name}`Goldblatt.isCaratheodory_of_subset_diff`, {name}`Goldblatt.isCaratheodory_of_between`).

## 16.4 Lebesgue Measure

Part 2 defines Lebesgue outer measure from the ring of left-open intervals
({name}`Goldblatt.lebesgueOuter`), identifies it with Mathlib's Lebesgue measure
({name}`Goldblatt.lebesgueOuter_apply`), and proves the three facts used later: uniqueness on
the Borel sets, Borel sets inside and outside a measurable set with null difference, and the
criterion of approximation by closed and open sets. The existence of a set that is not
Lebesgue measurable is mentioned in the book without proof and is not formalized.

## 16.5 Loeb Measures

Part 3 defines the outer measure, the Loeb measurable sets and the Loeb measure of a
{name}`Goldblatt.LoebPremeasure`, and proves Lemma 16.5.1
({name}`Goldblatt.LoebPremeasure.outer_eq_iInf`) and Lemma 16.5.2
({name}`Goldblatt.LoebPremeasure.outer_eq_iSup`). Part 4 proves the saturation steps
({name}`Goldblatt.InternalMeasure.exists_upper`,
{name}`Goldblatt.InternalMeasure.exists_between`), and shows that the presentation of an
internal measure by a sequence of rings with finitely additive functions covers every internal
finitely additive function on an internal ring
({name}`Goldblatt.eventually_isRingOfSets_of_internalCollection`,
{name}`Goldblatt.eventually_isFinitelyAdditive_of_internalCollection`,
{name}`Goldblatt.InternalMeasure.ofEventually`).

## 16.6 Approximability

Part 3 defines approximable sets ({name}`Goldblatt.LoebPremeasure.Approximable`) and proves
Lemmas 16.6.1 to 16.6.4. Part 4 proves that the definition agrees with the book's first
formulation in terms of the internal measure
({name}`Goldblatt.InternalMeasure.approximable_iff`).

## 16.7 Loeb Measure as Approximability

Part 3 proves Theorem 16.7.1
({name}`Goldblatt.LoebPremeasure.loebMeasurable_iff_forall_approximable`).

## 16.8 Lebesgue Measure via Loeb Measure

Part 5 builds the hyperfinite grid ({name}`Goldblatt.hyperGrid`) with its counting measure of
weight $`1/N` ({name}`Goldblatt.gridMeasure`, {name}`Goldblatt.gridLoeb`), proves Theorem
16.8.1 ({name}`Goldblatt.gridLoeb_μL_Ioo`), Lemma 16.8.3
({name}`Goldblatt.loebMeasurable_shInv_of_measurableSet`,
{name}`Goldblatt.outer_shInv_eq_volume`) and Theorem 16.8.2
({name}`Goldblatt.lebesgueMeasurable_iff_loebMeasurable_shInv`,
{name}`Goldblatt.volume_eq_loebMeasure_shInv`), together with the remarks of the section,
among them that every real number lies between two adjacent grid points in its halo
({name}`Goldblatt.exists_mem_hyperGrid_le_lt`). Theorem 16.8.1 is proved by counting grid
points index by index, not with the internal least and greatest grid points of the book's
argument.
-/
