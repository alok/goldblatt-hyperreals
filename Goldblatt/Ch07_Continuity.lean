import Goldblatt.Ch07_Continuity.Limits
import Goldblatt.Ch07_Continuity.Intervals
import Goldblatt.Ch07_Continuity.FunctionSequences

/-!
# 7. Continuous Functions

Chapter 6 read the behaviour of a sequence off its extended terms. This chapter does the same
for functions of a real variable: the standard notions of continuity, limit, uniform
continuity and uniform convergence, each of which is defined with two or three alternating
quantifiers, become statements that the extension of the function preserves infinite
closeness at certain points.

* A function is continuous at a real point $`c` exactly when its extension maps every point
  infinitely close to $`c` to a point infinitely close to $`f(c)`. This is Cauchy's
  description of continuity from 1821, made precise.
* The limit of $`f` at $`c` is $`L` exactly when the extension maps the points infinitely
  close to $`c` and different from $`c` into the halo of $`L`; one-sided limits, infinite
  limits and limits at infinity are obtained by changing which points are considered and
  where they are sent.
* A function is uniformly continuous on a set $`A` exactly when its extension preserves
  infinite closeness at all pairs of points of the enlargement of $`A`, and not just at
  pairs with one real member.
* A sequence of functions converges uniformly on $`A` exactly when its extended terms are
  infinitely close to the limit function at all points of the enlargement of $`A`, and not
  just at the real ones.

With these characterisations the chapter proves the intermediate value theorem and the
extreme value theorem by dividing an interval into an unlimited number of parts of
infinitesimal width, shows that a continuous function on a closed bounded interval is
uniformly continuous by taking shadows, proves that a contraction mapping has a fixed point
by taking the shadow of an extended term of the sequence of iterates, and proves in two ways
that a uniform limit of continuous functions is continuous. Along the way it meets the first
permanence principle: a property that holds on an infinitesimal neighbourhood of a real
point holds on a real neighbourhood.

The formalization of the chapter is split over three pages; this page is the overview and
the index.

## The three parts

* {lit}`Goldblatt.Ch07_Continuity.Limits` covers Sections 7.1 to 7.4. It begins with a
  preliminary section containing the two transfer tools used throughout the chapter. Then
  come Theorem 7.1.1, Corollary 7.1.2 and Theorem 7.1.3, the continuity of the sine and
  cosine functions, the seven characterisations of limits of Section 7.3, and the exercises
  of Section 7.4, including the five test functions of Exercise 7.4(3).
* {lit}`Goldblatt.Ch07_Continuity.Intervals` covers Sections 7.5 to 7.11: the intermediate
  value theorem and the extreme value theorem with the book's proofs by infinitesimal
  partitions, Theorems 7.7.1 and 7.7.2 on uniform continuity with the exercises of Section
  7.8, Lipschitz functions and the fixed point theorem for contraction mappings (Theorem
  7.9.1), Cauchy's permanence principle, and the exercises of Section 7.11.
* {lit}`Goldblatt.Ch07_Continuity.FunctionSequences` covers Sections 7.12 to 7.15: the
  hypersequence of functions associated with a sequence of functions, Theorems 7.12.1 and
  7.12.2, the example of the powers on the unit interval, both proofs of Theorem 7.13.1,
  Theorem 7.14.1, and the closing historical section.

## The sections of the chapter

Each section of the book's chapter is a section of one of the three parts, under the same
number.

* 7.1 Cauchy's Account of Continuity (part 1).
* 7.2 Continuity of the Sine Function (part 1).
* 7.3 Limits of Functions (part 1).
* 7.4 Exercises on Limits (part 1).
* 7.5 The Intermediate Value Theorem (part 2).
* 7.6 The Extreme Value Theorem (part 2).
* 7.7 Uniform Continuity (part 2).
* 7.8 Exercises on Uniform Continuity (part 2).
* 7.9 Contraction Mappings and Fixed Points (part 2).
* 7.10 A First Look at Permanence (part 2).
* 7.11 Exercises on Permanence of Functions (part 2).
* 7.12 Sequences of Functions (part 3).
* 7.13 Continuity of a Uniform Limit (part 3).
* 7.14 Continuity in the Extended Hypersequence (part 3).
* 7.15 Was Cauchy Right? (part 3).

## Conventions and deviations

* A function "defined on a set $`A`" is a total function of type {lit}`ℝ → ℝ` together with
  the set $`A`. Continuity relative to $`A` is {name}`ContinuousWithinAt` and
  {name}`ContinuousOn`, uniform continuity on $`A` is {name}`UniformContinuousOn`, and
  uniform convergence on $`A` is {name}`TendstoUniformlyOn`. On the hyperreal side the
  variable ranges over the enlargement of $`A`. Values of the function outside $`A` play no
  role in any statement.
* Limits are convergence of filters. The filters are named in Section 7.3 of part 1; for
  example the two-sided limit at $`c` along $`A` is taken along {lit}`𝓝[A \ {c}] c`.
* Theorem 7.1.3 is proved without the book's assumption that $`c` belongs to $`A`, and its
  condition (3) is shown to imply continuity for any positive radius, infinitesimal or not.
* Where the book says "by transfer", the proof here works with representing sequences and
  the almost-all criteria of Chapter 3. An unlimited hypernatural is the class of a sequence
  of natural numbers tending to infinity along the index ultrafilter, as in Chapter 6.
* The hypersequence of functions of Section 7.12 takes a hyperreal index and uses its
  integer part, in the same way as the hypersequences of Chapter 6; the book's index set of
  hypernaturals is a subset of the hyperreals.
* In Section 7.12 the book shows that the powers do not converge uniformly on the unit
  interval by a permanence argument that it only justifies in Chapter 15. Here an explicit
  point and index are exhibited instead.
* Exercise 7.4(3) asks for a discussion of five functions. It is formalized as five precise
  statements about where each function is continuous; for the first two functions only the
  behaviour at the origin, the point of interest, is treated.
* Section 7.15 is a historical discussion and has no formal content.

## Names for later chapters

Continuity at a point is characterised by {name}`Goldblatt.continuousAt_iff_infClose`
(Theorem 7.1.1), relative to a set by {name}`Goldblatt.continuousWithinAt_iff_infClose` and
{name}`Goldblatt.continuousOn_iff_infClose` (Theorem 7.1.3), with the forward directions
available as {name}`ContinuousAt.starMap_infClose` and
{name}`ContinuousWithinAt.starMap_infClose`. The criterion with an infinitesimal radius is
{name}`Goldblatt.continuousWithinAt_of_exists_radius`.

Limits are characterised by {name}`Goldblatt.tendsto_punctured_nhds_iff_infClose` (the form
needed for derivatives), {name}`Goldblatt.tendsto_nhdsWithin_diff_singleton_iff_infClose`,
{name}`Goldblatt.tendsto_nhdsWithin_Ioi_iff_infClose`,
{name}`Goldblatt.tendsto_nhdsWithin_Iio_iff_infClose`,
{name}`Goldblatt.tendsto_atTop_nhds_iff_infClose` and their variants. All of them are
instances of {name}`Goldblatt.tendsto_iff_starMap_mem_filterMonad`, which can be used for
any other countably generated filter.

Uniform continuity is characterised by {name}`Goldblatt.uniformContinuousOn_iff_infClose`
and {name}`Goldblatt.uniformContinuous_iff_infClose` (Theorem 7.7.1), and uniform
convergence by {name}`Goldblatt.tendstoUniformlyOn_iff_infClose` (Theorem 7.12.2), where the
hypersequence of functions is {name}`Goldblatt.hyperFunSeq`.

For work on a closed bounded interval, the partition points are
{name}`Goldblatt.partitionPoint`, and the fact that members of the enlargement of the
interval have shadows in the interval is {name}`Goldblatt.infClose_sh_of_mem_starSet_Icc`.
The classical theorems are {name}`Goldblatt.intermediate_value_Icc`,
{name}`Goldblatt.extreme_value_Icc` and
{name}`Goldblatt.uniformContinuousOn_Icc_of_continuousOn`. Cauchy's permanence principle is
{name}`Goldblatt.cauchy_principle_tfae`, with core
{name}`Goldblatt.exists_real_radius_of_hyperreal_radius`.

The extension of a function commutes with the pointwise operations by
{name}`Goldblatt.starMap_add_apply`, {name}`Goldblatt.starMap_sub_apply`,
{name}`Goldblatt.starMap_mul_apply`, {name}`Goldblatt.starMap_div_apply`,
{name}`Goldblatt.starMap_neg_apply` and {name}`Goldblatt.starMap_abs_apply`, and pointwise
equations and inequalities on a set transfer to its enlargement by
{name}`Goldblatt.starMap_congr_of_mem`, {name}`Goldblatt.starMap_le_starMap_of_mem` and
{name}`Goldblatt.starMap_lt_starMap_of_mem`.
-/
