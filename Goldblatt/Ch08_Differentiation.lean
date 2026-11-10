import Goldblatt.Ch08_Differentiation.Derivative
import Goldblatt.Ch08_Differentiation.Partial
import Goldblatt.Ch08_Differentiation.Taylor
import Goldblatt.Ch08_Differentiation.IncrementalEquation

/-!
# 8. Differentiation

The derivative was first computed as a ratio of infinitely small changes: the increment of a
quantity divided by the infinitesimal increment of the variable that produces it, with
whatever remains infinitely small then discarded. This chapter carries out that computation
in the hyperreals, where it is exact. The derivative of $`f` at a real point $`x` is the
shadow of the Newton quotient $`(f(x + \varepsilon) - f(x))/\varepsilon` for any nonzero
infinitesimal $`\varepsilon`, and it exists exactly when all these quotients have a common
shadow.

From this one characterisation the chapter develops the differential calculus with
infinitesimals in place of limits.

* The increment $`\Delta f` and the differential $`df` corresponding to an infinitesimal
  change $`\Delta x` differ by $`\varepsilon\,\Delta x` with $`\varepsilon` infinitesimal
  (the incremental equation). A differentiable function is therefore continuous.
* The rules for sums, products and quotients, and the chain rule, are computations with
  increments, as Leibniz performed them, justified by the arithmetic of infinite closeness.
* At a maximum or minimum inside an interval the Newton quotients with positive and negative
  increments have opposite signs, so the derivative is zero. Rolle's theorem, the mean value
  theorem and the tests for monotonicity follow from this and the extreme value theorem.
* The inverse of a continuous strictly monotone function is differentiable wherever the
  derivative of the function is not zero, because the Newton quotient of the inverse is the
  reciprocal of a Newton quotient of the function.
* For a smooth function of two variables the increment differs from the total differential
  by $`\varepsilon\,\Delta x + \delta\,\Delta y` with $`\varepsilon, \delta` infinitesimal.
  The proof transfers the mean value theorem to a slice of the function through a nonreal
  point.
* A Taylor series converges to its function at $`x` exactly when the remainders of unlimited
  order at $`x` are infinitesimal; Taylor's formula, transferred to unlimited orders, shows
  this for the cosine and the exponential function. Read at an infinitesimal distance from
  the centre, Taylor's formula approximates the function by a polynomial of degree $`n` in
  the increment with an error infinitely smaller than the $`n`-th power of the increment.
* The incremental equation holds at the nonreal points well inside an interval exactly when
  the derivative is continuous on the interval.

The formalization of the chapter is split over four pages; this page is the overview and the
index.

## The four parts

* {lit}`Goldblatt.Ch08_Differentiation.Derivative` covers Sections 8.1 to 8.6: Theorem 8.1.1
  with the one-sided variants and Exercise 8.1.2, increments and differentials with Theorems
  8.2.1 and 8.2.2, the three rules of Section 8.3, the chain rule, the critical point theorem
  with Rolle's theorem, the mean value theorem and the monotonicity tests, and the inverse
  function theorem.
* {lit}`Goldblatt.Ch08_Differentiation.Partial` covers Sections 8.7 and 8.8: infinite
  closeness in the hyperreal plane, continuity and smoothness of functions of two variables,
  Theorem 8.7.1, and the two exercises on partial derivatives.
* {lit}`Goldblatt.Ch08_Differentiation.Taylor` covers Sections 8.9 and 8.10: Taylor
  polynomials and remainders, the two convergence criteria, Taylor's formula with Lagrange's
  remainder and with the remainder of Exercise 8.10.2, its transfer to hypernatural orders,
  the Maclaurin series of the cosine and (Exercise 8.9.1) of the exponential function,
  Theorem 8.10.1 and Exercise 8.10.2.
* {lit}`Goldblatt.Ch08_Differentiation.IncrementalEquation` covers Sections 8.11 and 8.12:
  points well inside an interval, Theorem 8.11.1, and the two exercises of Section 8.12.

## The sections of the chapter

Each section of the book's chapter is a section of one of the four parts, under the same
number.

* 8.1 The Derivative (part 1).
* 8.2 Increments and Differentials (part 1).
* 8.3 Rules for Derivatives (part 1).
* 8.4 Chain Rule (part 1).
* 8.5 Critical Point Theorem (part 1).
* 8.6 Inverse Function Theorem (part 1).
* 8.7 Partial Derivatives (part 2).
* 8.8 Exercises on Partial Derivatives (part 2).
* 8.9 Taylor Series (part 3).
* 8.10 Incremental Approximation by Taylor's Formula (part 3).
* 8.11 Extending the Incremental Equation (part 4).
* 8.12 Exercises on Increments and Derivatives (part 4).

## Conventions and deviations

* A real function is a total function of type {lit}`ℝ → ℝ`, as in Chapter 7. "$`f` is
  differentiable at $`x` with derivative $`L`" is Mathlib's {name}`HasDerivAt`, the
  derivative function is {name}`deriv`, one-sided derivatives are {name}`HasDerivWithinAt`
  on a ray, and derivatives of higher order are {name}`iteratedDeriv`. The book's clause
  "$`f(x + \varepsilon)` is defined" has no counterpart for total functions.
* The results of Sections 8.3, 8.4 and 8.6 are theorems of Mathlib. They are proved here from
  Theorem 8.1.1 by the book's infinitesimal arguments, without Mathlib's rules. Mathlib's
  rules are used only for bookkeeping that the book treats as known: differentiating a
  function minus a polynomial in Sections 8.5 and 8.9, the partial derivatives of the
  example of a smooth function in Section 8.7, and the derivative of the example in
  Exercise 8.12(2) away from the origin.
* Rolle's theorem is stated for $`f(a) = f(b)`; the book states the case
  $`f(a) = f(b) = 0`.
* In Section 8.6 the inverse is a total function $`g` with $`g(f(t)) = t` on the interval.
* In Section 8.7 a function is smooth at a point, with given partial derivative functions,
  if these are the partial derivatives on a neighbourhood of the point and are continuous at
  the point ({name}`Goldblatt.SmoothAt`). The neighbourhood is implicit in the book.
* Taylor's formula with Lagrange's remainder, which the book quotes, is proved from Rolle's
  theorem. The hypothesis "$`f` can be differentiated $`n + 1` times on an interval $`J`" is
  the differentiability at every point of $`J` of the derivatives of order at most $`n`. The
  interval is any order-connected set; openness enters only where a neighbourhood of a point
  is needed.
* The second form of the remainder (Exercise 8.10.2) is proved assuming only $`n`
  derivatives on the interval, one fewer than the book assumes.
* Where the book says "by transfer", the proof works with representing sequences and the
  almost-all criteria of Chapter 3. A point $`c` between two others, whose existence is to
  be transferred, is chosen for each index and $`c` is the class of the chosen sequence.
* Functions with hypernatural index (derivatives, Taylor polynomials and remainders of
  unlimited order) are values of {name}`Goldblatt.hyperFunSeq` from Section 7.12.
* The example of a function whose Taylor series converges to a different function, quoted in
  Section 8.9 as well known, is not formalized.

## Names for later chapters

The derivative is characterised by {name}`Goldblatt.hasDerivAt_iff_infClose` (Theorem 8.1.1),
relative to a set by {name}`Goldblatt.hasDerivWithinAt_iff_infClose`, with the forward
direction available as {name}`HasDerivAt.newtonQuotient_infClose` and the formula for the
derivative as a shadow as {name}`Goldblatt.deriv_eq_sh_newtonQuotient`. The incremental
equation is {name}`HasDerivAt.incremental_equation`; increments and differentials are
{name}`Goldblatt.increment` and {name}`Goldblatt.differential`.

The mean value theorem is {name}`Goldblatt.exists_deriv_eq_slope_of_continuousOn`, and in
the form suited to transfer {name}`Goldblatt.exists_sub_eq_deriv_mul_sub`; its transfer to
two hyperreal points is {name}`Goldblatt.exists_mem_uIcc_starMap_sub_eq`. Rolle's theorem is
{name}`Goldblatt.exists_deriv_eq_zero_of_eq`.

Taylor polynomials, terms and remainders are {name}`Goldblatt.taylorPoly`,
{name}`Goldblatt.taylorTerm` and {name}`Goldblatt.taylorRem`. Taylor's formula is
{name}`Goldblatt.exists_taylorRem_eq_lagrange`, and the infinitesimal form is
{name}`Goldblatt.exists_infinitesimal_taylor_increment_of_differentiable`.

Points well inside an interval are {name}`Goldblatt.WellInside`, with
{name}`Goldblatt.wellInside_coe_iff` for a real interval. Existential transfer of a point
between two others is {name}`Goldblatt.exists_mem_uIcc_starMap_eq_mul` and
{name}`Goldblatt.exists_mem_uIcc_hyperFunSeq_eq_mul`, with
{name}`Goldblatt.ofSeq_mem_uIcc` and {name}`Goldblatt.infClose_of_mem_uIcc` as the basic
facts.
-/
