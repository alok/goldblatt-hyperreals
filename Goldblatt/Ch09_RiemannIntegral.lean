import Goldblatt.Ch09_RiemannIntegral.Sums
import Goldblatt.Ch09_RiemannIntegral.Integral
import Goldblatt.Ch09_RiemannIntegral.Properties

/-!
# 9. The Riemann Integral

The definite integral of a function over an interval measures the area under its graph. The
standard definition approximates that area from above and from below by finitely many
rectangles standing on the subintervals of a partition, and calls the function integrable when
the two kinds of approximation can be made to agree. Leibniz thought of the integral
differently, as an actual sum of infinitely many rectangles of infinitely small width. This
chapter shows that the two views coincide once infinitesimal widths are available.

* For a positive real width $`\Delta x`, cut $`[a, b]` into subintervals of width
  $`\Delta x` (the last one possibly shorter) and form the upper sum $`U_a^b(f, \Delta x)`,
  the lower sum $`L_a^b(f, \Delta x)` and the ordinary Riemann sum $`S_a^b(f, \Delta x)`.
  These are real functions of $`\Delta x`, so they extend to the hyperreals and have values
  at positive infinitesimal widths.
* A bounded function is Riemann integrable exactly when the extended upper and lower sums are
  infinitely close at every positive infinitesimal width, and then
  $$`\int_a^b f(x)\,dx = \operatorname{sh}\bigl(S_a^b(f, \Delta x)\bigr)`
  for any positive infinitesimal $`\Delta x`.
* Continuous functions satisfy the criterion because they are uniformly continuous on
  $`[a, b]` (Chapter 7); monotonic functions satisfy it by a telescoping sum.
* The algebraic and order properties of the integral are properties of finite sums,
  transferred to an infinitesimal width and then pushed through the shadow map.
* The derivative of the area function is the integrand, because the area of an infinitely
  thin strip divided by its width lies between two values of the function at points
  infinitely close together. The fundamental theorem of calculus follows.

The formalization of the chapter is split over three pages; this page is the overview and
the index.

## The three parts

* {lit}`Goldblatt.Ch09_RiemannIntegral.Sums` covers Section 9.1: partitions and their upper,
  lower and ordinary Riemann sums, the inequalities among them, the partition determined by
  a width, the extension of the three sums to hyperreal widths with the transferred
  inequalities, Theorem 9.1.1 and Exercise 9.1.2.
* {lit}`Goldblatt.Ch09_RiemannIntegral.Integral` covers Section 9.2: Riemann integrability
  and the Riemann integral, the characterisation of integrability by infinitesimal widths,
  the formula for the integral as a shadow, the integrability of continuous and monotonic
  functions, an example of a bounded function that is not integrable, and Exercise 9.2.1.
* {lit}`Goldblatt.Ch09_RiemannIntegral.Properties` covers Sections 9.3 to 9.5: the five
  standard properties of the integral (Exercise 9.3.1), Theorems 9.4.1 and 9.4.2, the
  comparison with Mathlib's integral, and the exercise on average values.

## 9.1 Riemann Sums

A partition of $`[a, b]` is {name}`Goldblatt.IntervalPartition`, and its three sums are
{name}`Goldblatt.IntervalPartition.upperSum`, {name}`Goldblatt.IntervalPartition.lowerSum`
and {name}`Goldblatt.IntervalPartition.ordSum`. The chain of inequalities between them and
the bounds $`m(b - a)` and $`M(b - a)` is
{name}`Goldblatt.IntervalPartition.lowerSum_ordSum_upperSum_chain`; the fact that a lower sum
never exceeds an upper sum is {name}`Goldblatt.IntervalPartition.lowerSum_le_upperSum`; and
the effect of refining a partition is {name}`Goldblatt.IntervalPartition.Refines.upperSum_le`
and {name}`Goldblatt.IntervalPartition.Refines.lowerSum_le`.

The partition of width $`\Delta x` is {name}`Goldblatt.meshPartition`, with points
{name}`Goldblatt.meshPoint` and {name}`Goldblatt.meshCard` subintervals. Its sums, as real
functions of the width, are {name}`Goldblatt.upperSum`, {name}`Goldblatt.lowerSum` and
{name}`Goldblatt.ordSum`, and their extensions to the hyperreals are
{name}`Goldblatt.hyperUpperSum`, {name}`Goldblatt.hyperLowerSum` and
{name}`Goldblatt.hyperOrdSum`. The transferred inequalities are
{name}`Goldblatt.hyperLowerSum_hyperOrdSum_hyperUpperSum_chain` and
{name}`Goldblatt.hyperLowerSum_le_hyperUpperSum`. For an infinitesimal width the number of
subintervals is unlimited ({name}`Goldblatt.hyperMeshCard_mem_unlimitedHyperNat`), and for
every positive hyperreal width it is the least hypernatural $`n` with
$`a + n\,\Delta x \ge b` ({name}`Goldblatt.hyperMeshCard_spec`,
{name}`Goldblatt.hyperMeshCard_le_of_le_add_mul`).

Theorem 9.1.1 is {name}`Goldblatt.hyperLowerSum_infClose_hyperUpperSum_of_continuousOn`, with
its real form {name}`Goldblatt.exists_points_upperSum_sub_lowerSum_le` and the transferred
statements (i) and (ii) of its proof in
{name}`Goldblatt.exists_hyper_points_hyperUpperSum_sub_hyperLowerSum_le`. Exercise 9.1.2 is
{name}`Goldblatt.upperSum_sub_lowerSum_le_of_monotoneOn`,
{name}`Goldblatt.upperSum_sub_lowerSum_le_of_antitoneOn` and
{name}`Goldblatt.hyperLowerSum_infClose_hyperUpperSum_of_monotonic`.

## 9.2 The Integral as the Shadow of Riemann Sums

Integrability with a given integral is {name}`Goldblatt.HasRiemannIntegral`, integrability is
{name}`Goldblatt.RiemannIntegrableOn`, and the integral is {name}`Goldblatt.riemannIntegral`.
The standard characterisation by conditions (1) and (2) of the book is
{name}`Goldblatt.hasRiemannIntegral_iff_conditions`.

The main results are {name}`Goldblatt.hasRiemannIntegral_sh_of_infClose` (if the lower and
upper sums of one infinitesimal width are infinitely close, the function is integrable and the
integral is the shadow of the Riemann sum), its converse
{name}`Goldblatt.HasRiemannIntegral.hyperLowerSum_infClose_hyperUpperSum`, the resulting
equivalence {name}`Goldblatt.riemannIntegrableOn_iff_forall_infClose`, and the book's formula
(iii), {name}`Goldblatt.RiemannIntegrableOn.riemannIntegral_eq_sh`. Continuous and monotonic
functions are integrable by {name}`Goldblatt.riemannIntegrableOn_of_continuousOn`,
{name}`Goldblatt.riemannIntegrableOn_of_monotoneOn` and
{name}`Goldblatt.riemannIntegrableOn_of_antitoneOn`. The integral is the limit of the Riemann
sums as the width tends to zero ({name}`Goldblatt.RiemannIntegrableOn.tendsto_ordSum`).
The indicator function of the rationals is not integrable
({name}`Goldblatt.not_riemannIntegrableOn_ratIndicator`).

Exercise 9.2.1 is {name}`Goldblatt.RiemannIntegrableOn.hyperSeq_lowerSumN_infClose`,
{name}`Goldblatt.riemannIntegrableOn_iff_forall_unlimited` and
{name}`Goldblatt.RiemannIntegrableOn.riemannIntegral_eq_sh_hyperSeq`.

## 9.3 Standard Properties of the Integral

The five properties are {name}`Goldblatt.RiemannIntegrableOn.riemannIntegral_const_mul`,
{name}`Goldblatt.RiemannIntegrableOn.riemannIntegral_add`,
{name}`Goldblatt.RiemannIntegrableOn.riemannIntegral_add_adjacent`,
{name}`Goldblatt.riemannIntegral_mono` and {name}`Goldblatt.riemannIntegral_mem_Icc`. The
book's equation (iv), on which its proof of the third property rests, is
{name}`Goldblatt.meshSumOf_split` for real widths and
{name}`Goldblatt.hyperOrdSum_add_adjacent` for an infinitesimal width.

## 9.4 Differentiating the Area Function

Theorem 9.4.1 is {name}`Goldblatt.hasDerivWithinAt_riemannIntegral`, proved by transfer of
the real inequality (v), {name}`Goldblatt.exists_points_areaQuotient`, to
{name}`Goldblatt.exists_hyper_points_areaQuotient`. Theorem 9.4.2, the
fundamental theorem of calculus, is
{name}`Goldblatt.riemannIntegral_eq_sub_of_hasDerivWithinAt`.

## 9.5 Exercise on Average Function Values

The sample average is {name}`Goldblatt.sampleAverage` and the exercise is
{name}`Goldblatt.hyperSeq_sampleAverage_infClose`.

## Conventions and deviations

* A function on $`[a, b]` is a total function of type {lit}`ℝ → ℝ` together with the two end
  points; its values outside the interval play no role. Boundedness on a set is
  {name}`Goldblatt.BoundedOn`. The least upper bound and greatest lower bound of the function
  on a subinterval are {name}`Goldblatt.supOn` and {name}`Goldblatt.infOn`.
* The Riemann integral is defined directly, as the least upper bound of the lower sums, and
  integrability as in the book. It is _not_ defined as Mathlib's integral. For continuous
  functions the two agree: this is {name}`Goldblatt.riemannIntegral_eq_intervalIntegral`,
  proved from Theorems 9.4.1 and 9.4.2.
* All statements require $`a \le b`, either as a hypothesis or as a consequence of
  integrability; the sample averages of Section 9.5, which divide by $`b - a`, require
  $`a < b`. The integral over a degenerate interval is $`0`
  ({name}`Goldblatt.riemannIntegral_self`). No convention is made for $`\int_a^b` with
  $`b < a`; no function is integrable on a reversed interval in the sense used here.
* The sums of width $`\Delta x` are total functions of a real $`\Delta x`, as is needed in
  order to extend them. They have their intended meaning only for $`\Delta x > 0`, and every
  theorem about them carries that hypothesis.
* The book refers to refinements for the inequality $`L(f, P_1) \le U(f, P_2)`. The proof
  here counts the lengths of the intersections of the subintervals of the two partitions,
  which is the same argument without constructing the common refinement
  ({name}`Goldblatt.IntervalPartition.sum_mul_le_sum_mul`).
* In Section 9.2 the book quotes from the standard theory that for an integrable function
  the upper and lower sums of width $`\Delta x` approach each other as $`\Delta x` tends to
  zero. That fact is proved here from an explicit estimate
  ({name}`Goldblatt.upperSum_le_add_mul`), which is transferred to infinitesimal widths; its
  standard form is
  {name}`Goldblatt.RiemannIntegrableOn.exists_pos_forall_upperSum_sub_lowerSum_lt`.
* Theorem 9.4.1 is stated with the derivative relative to $`[a, b]`
  ({name}`HasDerivWithinAt`), which at interior points is the ordinary derivative and at the
  end points the one-sided derivative, as in the book.
* Exercise 9.5 is proved for all integrable functions; the book's statement for continuous
  functions is a special case.

## Names for later chapters

The partition of $`[a, b]` by a width and its Riemann sum are
{name}`Goldblatt.meshCard`, {name}`Goldblatt.meshPoint` and {name}`Goldblatt.ordSum`. They
the definitions that later chapters should use. The part of Chapter 12 on hyperfinite sums
currently carries its own copies, given by the same formulas, so the two are equal by
unfolding; that file is not imported here and replacing its copies by these names is left to
it. For an integrable function the Riemann
sums converge to the integral ({name}`Goldblatt.RiemannIntegrableOn.tendsto_ordSum`), and an
integrable function is bounded ({name}`Goldblatt.RiemannIntegrableOn.boundedOn`); these are
the two facts about integrability that Section 12.7 needs.

The transfer tools for functions of a positive width are
{name}`Goldblatt.starMap_le_starMap_of_pos` (universal) and
{name}`Goldblatt.exists_pos_lt_of_starMap_lt` (existential), and the values of the extended
sums at the class of a sequence of widths are {name}`Goldblatt.hyperUpperSum_ofSeq`,
{name}`Goldblatt.hyperLowerSum_ofSeq` and {name}`Goldblatt.hyperOrdSum_ofSeq`.
-/
