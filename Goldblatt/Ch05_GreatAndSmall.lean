import Goldblatt.Ch05_GreatAndSmall.Arithmetic
import Goldblatt.Ch05_GreatAndSmall.Shadows
import Goldblatt.Ch05_GreatAndSmall.Hypernaturals

/-!
# 5. Hyperreals Great and Small

Chapter 3 built the hyperreal field and Chapter 4 explained why it has the same first-order
properties as the reals. This chapter looks at what is new in it: the numbers that are not
real. A hyperreal is compared with the real numbers and classified as _limited_ (between two
reals), _unlimited_ (beyond all reals), _infinitesimal_ (closer to zero than every nonzero
real) or _appreciable_ (limited and not infinitesimal). The arithmetic of these classes is
worked out in full. It shows that the limited numbers form a ring in which the infinitesimals
are an ideal.

Two equivalence relations organize the hyperreal line. Numbers with infinitesimal difference
are _infinitely close_, and the classes are the _halos_; numbers with limited difference are
at _limited distance_, and the classes are the _galaxies_. The central result is that every
limited hyperreal is infinitely close to exactly one real number, its _shadow_. Taking shadows
is a ring homomorphism from the limited numbers onto the reals with kernel the infinitesimals,
so the real field is the quotient of the limited hyperreals by the infinitesimals. The
existence of shadows is proved from the completeness of the reals, and conversely it implies
completeness.

The chapter ends with the hypernatural numbers: their order structure (the natural numbers
followed by a dense family of copies of the integers), divisibility and prime factors, and a
nonstandard proof that there are infinitely many primes.

The formalization of the chapter is long, so it is split over three pages; this page is the
overview and the index.

## The three parts

* {lit}`Goldblatt.Ch05_GreatAndSmall.Arithmetic` covers the opening remark on hyperrationals
  and Sections 5.1 to 5.3: the four size classes with their reformulations, every rule of the
  table of arithmetic and the indeterminate forms, the ring of limited numbers and its ideal
  of infinitesimals, the hyperreal power function of Exercise 5.2.1 and roots of hypernatural
  order.
* {lit}`Goldblatt.Ch05_GreatAndSmall.Shadows` covers Sections 5.4 to 5.9: infinite closeness,
  limited distance, halos and galaxies with their exercises, the shadow of a limited
  hyperreal (Theorem 5.6.1), its algebraic properties (Theorem 5.6.2), the isomorphism of the
  quotient of the limited numbers by the infinitesimals with the reals (Theorem 5.6.3), the
  exercises on infinite closeness, and the equivalence between the existence of shadows and
  completeness (Theorem 5.8.1 and Exercise 5.9).
* {lit}`Goldblatt.Ch05_GreatAndSmall.Hypernaturals` covers Sections 5.10 to 5.12: the order
  structure of the hypernaturals and of the hyperintegers, divisibility and hyperprimes, and
  the nonstandard proof of the infinitude of the primes.

## The sections of the chapter

Each section of the book's chapter is a section of one of the three parts, under the same
number.

* 5.1 (Un)limited, Infinitesimal, and Appreciable Numbers (part 1).
* 5.2 Arithmetic of Hyperreals (part 1).
* 5.3 On the Use of "Finite" and "Infinite" (part 1).
* 5.4 Halos, Galaxies, and Real Comparisons (part 2).
* 5.5 Exercises on Halos and Galaxies (part 2).
* 5.6 Shadows (part 2).
* 5.7 Exercises on Infinite Closeness (part 2).
* 5.8 Shadows and Completeness (part 2).
* 5.9 Exercise on Dedekind Completeness (part 2).
* 5.10 The Hypernaturals (part 3).
* 5.11 Exercises on Hyperintegers and Primes (part 3).
* 5.12 On the Existence of Infinitely Many Primes (part 3).

## Conventions of the formalization

* The size classes are the predicates {name}`Goldblatt.Limited`,
  {name}`Goldblatt.Unlimited`, {name}`Goldblatt.Infinitesimal` and
  {name}`Goldblatt.Appreciable` on the hyperreals, defined exactly as in the book. In proofs
  one uses their characterizations through the absolute value:
  {name}`Goldblatt.limited_iff_abs_lt`, {name}`Goldblatt.unlimited_iff_abs_gt`,
  {name}`Goldblatt.infinitesimal_iff_abs_lt` and {name}`Goldblatt.appreciable_iff_abs`.
  The sets of limited and of infinitesimal numbers are written {lit}`𝕃` and {lit}`𝕀`; as
  algebraic objects they are {name}`Goldblatt.limitedSubring` and
  {name}`Goldblatt.infinitesimalIdeal`.
* Infinite closeness, the book's $`b \simeq c`, is {name}`Goldblatt.InfClose` and is written
  {lit}`b ≊ c`. The book's symbol is Lean's notation for an equivalence of types and cannot
  be reused between numbers. Limited distance $`b \sim c` is {name}`Goldblatt.LimClose`,
  written {lit}`b ∼ c`. Halos and galaxies are {name}`Goldblatt.hal` and
  {name}`Goldblatt.gal`.
* The shadow is {name}`Goldblatt.sh`, a function from the hyperreals to the reals that takes
  the value $`0` at unlimited arguments. The basic facts are
  {name}`Goldblatt.Limited.infClose_sh` (a limited number is infinitely close to its shadow)
  and {name}`Goldblatt.sh_eq_of_infClose` (a real infinitely close to a number is its shadow).
* Mathlib measures size by the Archimedean class {name}`ArchimedeanClass.mk` and has the
  standard part function {name}`ArchimedeanClass.stdPart`. The bridge lemmas are
  {name}`Goldblatt.limited_iff_mk_nonneg`, {name}`Goldblatt.infinitesimal_iff_mk_pos`,
  {name}`Goldblatt.unlimited_iff_mk_neg`, {name}`Goldblatt.appreciable_iff_mk_eq_zero` and
  {name}`Goldblatt.sh_eq_stdPart`.
* Extensions of particular real functions are named with a leading h:
  {name}`Goldblatt.hroot`, {name}`Goldblatt.hpow`, {name}`Goldblatt.hsqrt`,
  {name}`Goldblatt.hfloor`, {name}`Goldblatt.hsin`, {name}`Goldblatt.hcos`,
  {name}`Goldblatt.htan`. Each comes with a lemma computing it on the class of a sequence.
* Transfer arguments are carried out on representing sequences, with the almost-all toolkit of
  Chapter 3. For the hypernaturals the class of a sequence of natural numbers is
  {name}`Goldblatt.hnat`, and divisibility in the hypernaturals is {name}`Goldblatt.HDvd`,
  written {lit}`a ∣ₕ b`.
* Section 5.8 asks for a theorem of the form "the existence of shadows implies completeness".
  For Lean's real numbers this would be vacuous, so the theorem is proved for an arbitrary
  ordered field, with the hypothesis {name}`Goldblatt.ShadowProperty` about its ultrapower;
  the statements for the reals are then special cases.
-/
