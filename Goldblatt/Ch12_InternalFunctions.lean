import Goldblatt.Ch12_InternalFunctions.Functions
import Goldblatt.Ch12_InternalFunctions.Hyperfinite
import Goldblatt.Ch12_InternalFunctions.Sums

/-!
# 12. Internal Functions and Hyperfinite Sets

Chapter 11 built internal sets from sequences of sets. This chapter applies the same
construction to functions and then studies the internal sets that play the part of finite sets
in the nonstandard world.

A sequence of partial functions determines one partial function on the ultrapower, whose
value at the class of a sequence of points is the class of the sequence of values. Functions
of this kind are _internal_. Like internal sets they are decided by almost all terms of the
defining sequence, and the usual operations on functions (image, inverse image, composition,
inverse, pointwise arithmetic) can be carried out term by term, so they preserve internality.

An internal set is _hyperfinite_ when almost all of its defining sets are finite. A hyperfinite
set has a hypernatural number of elements, its _internal cardinality_, and it behaves like a
finite set with respect to internal objects: it has a greatest and a least element, it can be
counted by an internal bijection with an initial segment of the hypernaturals, and an internal
injection of it into itself is onto. An internal function can be summed over a hyperfinite set.
The chapter ends by writing the integral of a function over an interval as the shadow of such
a sum, taken over a partition of the interval into infinitely many subintervals of
infinitesimal width.

The formalization is split over three pages; this page is the overview and the index.

## The three parts

* {lit}`Goldblatt.Ch12_InternalFunctions.Functions` covers Sections 12.1 and 12.2: internal
  functions, Theorem 12.1.1, and the eight exercises on their properties.
* {lit}`Goldblatt.Ch12_InternalFunctions.Hyperfinite` covers Sections 12.3 to 12.6: hyperfinite
  sets and internal cardinality with the examples of the text, the exercises on
  hyperfiniteness, Theorem 12.5.1 on counting, and the hyperfinite pigeonhole principle.
* {lit}`Goldblatt.Ch12_InternalFunctions.Sums` covers Section 12.7: hyperfinite sums and the
  integral as a hyperfinite sum.

## 12.1 Internal Functions

Part 1. The internal function of a sequence of partial functions, its domain, the almost-all
criterion for its values, and Theorem 12.1.1: two sequences define the same internal function
if and only if they agree at almost all indices.

## 12.2 Exercises on Properties of Internal Functions

Part 1. Images and inverse images of internal sets, composition, injectivity, inverses, sums,
products and multiples of internal functions; the least upper bound of the range of an
internal function with infinitesimal values; a second proof that infinite sets of reals are
external.

## 12.3 Hyperfinite Sets

Part 2. Hyperfinite sets, internal cardinality, and the examples: initial segments of the
hypernaturals, hyperfinite grids and uniform partitions, finite sets, and hyperfinite
approximations of countable sets.

## 12.4 Exercises on Hyperfiniteness

Part 2. Greatest and least elements, unions and intersections with the inclusion-exclusion
formula, and internal subsets of hyperfinite sets.

## 12.5 Counting a Hyperfinite Set

Part 2. Theorem 12.5.1: a set is hyperfinite of internal cardinality $`N` exactly when it is
the range of an injective internal function defined on $`\{1, \dots, N\}`.

## 12.6 Hyperfinite Pigeonhole Principle

Part 2. Theorem 12.6.1: an internal set is hyperfinite exactly when every internal injection of
it into itself is onto; a function that is not internal.

## 12.7 Integrals as Hyperfinite Sums

Part 3. The sum of an internal function over a hyperfinite set and its properties; the
hyperfinite partition of an interval; the integral of a continuous function as the shadow of a
hyperfinite Riemann sum.

## Conventions of the formalization

* A partial function is an element of Mathlib's type {name}`PFun`, so it carries its domain and
  two partial functions are equal exactly when they have the same domain and the same values.
  The internal function $`[f_n]` of a sequence of partial functions is
  {name}`Goldblatt.internalPFun`, with defining property
  {name}`Goldblatt.ofSeq_mem_internalPFun`; for sequences of total functions there is the total
  version {name}`Goldblatt.internalMap`. The predicate "is internal" is
  {name}`Goldblatt.IsInternalPFun`, which takes the underlying types as explicit arguments, and
  {name}`Goldblatt.IsInternalFun` for hyperreal functions.
* The auxiliary notions for partial functions that Mathlib does not have are defined on the
  first page: injectivity {name}`Goldblatt.PInjective`, the inverse {name}`Goldblatt.pinv`, the
  restriction {name}`Goldblatt.prestrict`, pointwise sum and product {name}`Goldblatt.padd` and
  {name}`Goldblatt.pmul`. Sums and products are defined on the intersection of the domains,
  compositions wherever they make sense, and images over the part of a set where the function
  is defined, so the side conditions of the exercises on domains are not needed.
* Hyperfiniteness is {name}`Goldblatt.IsHyperfiniteSet` (for sets of hyperreals,
  {name}`Goldblatt.IsHyperfinite`), the internal cardinality is {name}`Goldblatt.internalCard`
  (for sets of hyperreals, {name}`Goldblatt.hcard`), and the hyperfinite sum is
  {name}`Goldblatt.internalSum` (for hyperreal functions, {name}`Goldblatt.hsum`). The last two
  are total functions with junk values outside their intended domain, and are computed on
  defining sequences by {name}`Goldblatt.internalCard_internalSet` and
  {name}`Goldblatt.internalSum_internalPFun`.
* Lean's natural numbers start at $`0`. The book's segment $`\{1, \dots, N\}` is kept in
  Theorem 12.5.1, and the examples are given both from $`1` and from $`0`.
* Four statements of the book are corrected or sharpened, each with a note in the docstring.
  Exercises 12.2(7) and 12.4(1) need a nonempty set. The uniform partition of Section 12.3 has
  $`N + 1` points only if its end points are distinct. The example of a function that is not
  internal in Section 12.6 is argued in the book from the pigeonhole principle applied to the
  set of all hypernaturals, which is not hyperfinite; the proof here applies the principle to
  an initial segment. In Section 12.7 the hyperfinite sum over the partition and the extended
  Riemann sum of Section 9.1 are infinitely close but in general not equal, because they give
  different widths to the last subinterval.
* The final theorem of Section 12.7 is stated in the book for Riemann integrable functions and
  rests on Chapter 9. Here it is proved for continuous functions, with Mathlib's interval
  integral; the standard ingredient is the convergence of Riemann sums of a continuous function
  ({name}`Goldblatt.abs_riemannSum_sub_integral_lt`), and the nonstandard step is
  {name}`Goldblatt.infClose_starMap_riemannSum_integral`.
-/
