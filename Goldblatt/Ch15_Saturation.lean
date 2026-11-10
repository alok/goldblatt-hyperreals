import Goldblatt.Ch15_Saturation.Codes
import Goldblatt.Ch15_Saturation.Hyperreals
import Goldblatt.Ch15_Saturation.Permanence
import Goldblatt.Ch15_Saturation.Uniform
import Goldblatt.Ch15_Saturation.Comprehensive
import Goldblatt.Ch15_Saturation.Ultrapower
import Goldblatt.Ch15_Saturation.Saturation

/-!
# 15. Permanence, Comprehensiveness, Saturation

Chapters 13 and 14 set up nonstandard frameworks and showed that enlargements exist. This
chapter collects the principles of reasoning that make a framework useful, in the generality
of a transfer map between two universes, where they apply to properties that mention
arbitrary internal entities. There are three groups.

_Permanence._ An internal property that holds on all of an external set (the standard
natural numbers from some point on, a halo, the limited numbers) holds on a larger internal
set. Overflow and underflow are the best known cases. A consequence is Robinson's sequential
lemma: an internal hypersequence with infinitesimal terms at all standard indices has
infinitesimal terms up to some unlimited index. It gives a short proof that a uniform limit
of continuous functions is continuous.

_Comprehensiveness._ A function from a standard set to an internal set need not belong to
either universe, and the question is whether it extends to an internal function on the
transform of its domain. Frameworks in which it always does are called comprehensive. The
ultrapower of Chapter 14 is comprehensive.

_Saturation._ A framework is countably saturated when every decreasing sequence of nonempty
internal sets has a common member. For a framework over the real numbers this is equivalent
to countable comprehensiveness together with the existence of an unlimited hypernatural
number. The enlargements of Chapter 14 are countably saturated, and these are the
frameworks used in Part V of the book. Saturation for collections of larger
cardinality is defined, and its basic properties are proved.

The standing assumption of the chapter is that the framework has the real numbers among its
individuals ({name}`Goldblatt.RealFramework`) and has a hypernatural number that is not a
natural number. The second assumption is written out as a hypothesis wherever it is used.

The formalization is split over seven pages; this page is the overview and the index.

## The seven parts

* {module}`Goldblatt.Ch15_Saturation.Codes` is preparatory. It turns relations between real
  numbers into sets of the standard universe and restates the transfer principle for them,
  so that a fact about real numbers transfers to the hyperreals of an arbitrary framework
  without a formula being written.
* {module}`Goldblatt.Ch15_Saturation.Hyperreals` is preparatory. It defines the strict order of
  the hyperreals, infinitesimal, limited and unlimited hyperreals and the relation of being
  infinitely close, in an arbitrary framework over the reals.
* {module}`Goldblatt.Ch15_Saturation.Permanence` covers Sections 15.1 and 15.2.
* {module}`Goldblatt.Ch15_Saturation.Uniform` covers Section 15.3.
* {module}`Goldblatt.Ch15_Saturation.Comprehensive` covers the definitions of Section 15.4,
  Theorems 15.4.2 and 15.4.3 and Exercise 15.4.4.
* {module}`Goldblatt.Ch15_Saturation.Ultrapower` covers the part of Section 15.4 about the
  ultrapower, Exercise 15.4.1, and the existence of countably saturated enlargements.
* {module}`Goldblatt.Ch15_Saturation.Saturation` covers Section 15.5.

## 15.1 Permanence Principles

Part 3. Each of the five statements of Theorem 15.1.1 is proved for an internal set and, as
in the book, for an internal formula with one free variable
({name}`Goldblatt.NonstandardFramework.IsInternalFormula`,
{name}`Goldblatt.NonstandardFramework.TrueAt`): overflow
({name}`Goldblatt.RealFramework.overflow_set`, {name}`Goldblatt.RealFramework.overflow`),
underflow ({name}`Goldblatt.RealFramework.underflow_set`,
{name}`Goldblatt.RealFramework.underflow`), permanence from a halo to a real neighbourhood
({name}`Goldblatt.RealFramework.near_permanence_set`,
{name}`Goldblatt.RealFramework.near_permanence`), from arbitrarily large or small reals to
unlimited hyperreals ({name}`Goldblatt.RealFramework.exists_posUnlimited_mem`,
{name}`Goldblatt.RealFramework.exists_negUnlimited_mem`,
{name}`Goldblatt.RealFramework.exists_unlimited_trueAt`), and from the limited numbers above
a real to an interval with an unlimited end point
({name}`Goldblatt.RealFramework.exists_posUnlimited_forall_mem`,
{name}`Goldblatt.RealFramework.exists_posUnlimited_forall_trueAt`). Exercise 15.1.2 is
{name}`Goldblatt.RealFramework.exists_nat_bound_of_limited_values`. Two of the further
permanence results that the book leaves to the reader are proved because they are used
later ({name}`Goldblatt.RealFramework.exists_nat_bound_of_forall_limited`,
{name}`Goldblatt.RealFramework.exists_posUnlimited_interval_subset`).

## 15.2 Robinson's Sequential Lemma

Part 3. Lemma 15.2.1 is {name}`Goldblatt.RealFramework.robinson_sequential_lemma`, with the
version for hypersequences defined up to an unlimited index
({name}`Goldblatt.RealFramework.robinson_function`). Exercise 15.2.2 is
{name}`Goldblatt.RealFramework.robinson_near_sequence` and, in general form,
{name}`Goldblatt.RealFramework.robinson_near`. Theorem 15.2.3 is
{name}`Goldblatt.RealFramework.infinitesimal_on_unlimited_interval`.

## 15.3 Uniformly Converging Sequences of Functions

Part 4. The extended sequence $`{}^*f_n(x)` is {name}`Goldblatt.RealFramework.hseq`, and for
every hypernatural $`n` the function $`{}^*f_n` is internal
({name}`Goldblatt.RealFramework.exists_internal_hseq`). It agrees with the book's definition
of $`{}^*f_n` as the value at $`n` of the transform of the sequence $`n \mapsto f_n`, a
function from $`\mathbb N` into a function space ({name}`Goldblatt.RealFramework.seqSet`,
{name}`Goldblatt.RealFramework.app_star_seqSet_spec`,
{name}`Goldblatt.RealFramework.app_app_star_seqSet`). Uniform
convergence is equivalent to condition (i) of the book
({name}`Goldblatt.RealFramework.tendstoUniformlyOn_iff_near`; the direction asked for in
Exercise 15.3.1 is {name}`Goldblatt.RealFramework.tendstoUniformlyOn_of_near`). The proof
that a uniform limit of continuous functions is continuous is
{name}`Goldblatt.RealFramework.continuousWithinAt_of_tendstoUniformlyOn`, and the classical
statement for a closed interval is {name}`Goldblatt.continuousOn_of_tendstoUniformlyOn_Icc`.

## 15.4 Comprehensiveness

Parts 5 and 6. The definitions are {name}`Goldblatt.NonstandardFramework.Comprehensive`,
{name}`Goldblatt.NonstandardFramework.CountablyComprehensive`,
{name}`Goldblatt.RealFramework.SequentiallyComprehensive` and
{name}`Goldblatt.NonstandardFramework.CountablySaturated`. The ultrapower is comprehensive
({name}`Goldblatt.BoundedUltrapower.comprehensive_framework`), by the construction
{name}`Goldblatt.BoundedUltrapower.Reps.ext`, whose action is computed in
{name}`Goldblatt.BoundedUltrapower.Reps.ext_app`. Exercise 15.4.1 is
{name}`Goldblatt.BoundedUltrapower.Reps.eq_star_of_ext_app_ne` and
{name}`Goldblatt.BoundedUltrapower.exists_reps_ext_eq_star`. Theorem 15.4.2 is
{name}`Goldblatt.RealFramework.countablySaturated_tfae`. Theorem 15.4.3 is
{name}`Goldblatt.RealFramework.exists_unlimited_lt_of_countable`, and Exercise 15.4.4 is
{name}`Goldblatt.RealFramework.exists_internal_running_min` and
{name}`Goldblatt.RealFramework.exists_unlimited_lt_of_internal_seq`. Comprehensive,
countably saturated enlargements exist over any base set
({name}`Goldblatt.exists_countablySaturated_enlargement`; the ultrapower modulo a countably
incomplete ultrafilter is countably saturated by a direct diagonal argument,
{name}`Goldblatt.BoundedUltrapower.countablySaturated_framework`), and over the real numbers
together with any given type of further individuals
({name}`Goldblatt.exists_realFramework_countablySaturated`,
{name}`Goldblatt.exists_realFramework_countablySaturated_of_type`). In a countably saturated
framework every infinite internal set is uncountable
({name}`Goldblatt.NonstandardFramework.CountablySaturated.not_countable_of_infinite`), with
the two instances for hypernaturals mentioned in the book
({name}`Goldblatt.RealFramework.not_countable_gt`,
{name}`Goldblatt.RealFramework.not_countable_unlimited_lt`).

## 15.5 Saturation

Part 7. Countable saturation in terms of countable collections with the finite intersection
property is {name}`Goldblatt.NonstandardFramework.countablySaturated_iff_countable_fip`. The
definition of $`\kappa`-saturation is {name}`Goldblatt.NonstandardFramework.Saturated`
(for a set of internal sets, as in the book:
{name}`Goldblatt.NonstandardFramework.saturated_iff_set_fip`), and
countable saturation is $`\aleph_1`-saturation
({name}`Goldblatt.NonstandardFramework.saturated_aleph_one_iff`). The example of an
uncountable collection without a common member is
{name}`Goldblatt.RealFramework.fip_star_R_sdiff_singleton`; in a $`\kappa`-saturated
framework every infinite internal set has at least $`\kappa` members
({name}`Goldblatt.NonstandardFramework.Saturated.lift_le_mk_of_infinite`). The existence of
$`\kappa`-saturated enlargements is
{name}`Goldblatt.NonstandardFramework.exists_saturated_enlargement`, proved for
$`\kappa \le \aleph_1`
({name}`Goldblatt.NonstandardFramework.exists_saturated_enlargement_of_le_aleph_one`).
Exercise 15.5.1 is {name}`Goldblatt.NonstandardFramework.saturated_iff_concurrent`.

## Design of the formalization

*Hyperreals in a framework.* Parts I to III of the book compute with hyperreals as classes
of real sequences. In a framework there is only the transfer principle. The notions needed
here are defined from the transforms of relations on the reals: $`a < b` means that the pair
$`(a, b)` belongs to the transform of the relation $`<`, and $`a \simeq b` means that it
belongs to the transform of $`|x - y| < r` for every positive real $`r`. Arithmetic never has
to be performed on hyperreals: a condition such as $`|n \cdot s_n| < 1` is the transform of
a relation between real numbers, and a consequence of it is obtained by transferring an
implication between such relations, which is proved in Lean for real numbers. Part 1
provides the lemmas that do this.

*Internal sets without formulas.* The internal sets to which overflow and its relatives are
applied are obtained from the closure properties of internal sets in Chapter 13 (Boolean
operations, images and inverse images under internal relations, composites, domains and
ranges). The internal set definition principle is used once, to derive the statements for
internal formulas from those for internal sets.

*Internal sets and functions.* An internal set is an internal entity that is a set of the
nonstandard universe ({name}`Goldblatt.NonstandardFramework.InternalSet`). A function
$`f : A \to B` in the definition of comprehensiveness is any set of pairs.

*Cardinals.* In the definition of $`\kappa`-saturation the cardinal lives in the universe
level of the sets, and a collection of fewer than $`\kappa` internal sets is a family
indexed by a type of that level; the equivalence with collections given as sets is
{name}`Goldblatt.NonstandardFramework.saturated_iff_set_fip`.

*Corrections to the book.* Theorem 15.1.1 (5) is false as printed: an internal set can
contain every real number $`a \ge r` and omit a point infinitely close to $`r`
({name}`Goldblatt.RealFramework.exists_internal_set_reals_ge_not_interval`; for a formula,
{name}`Goldblatt.RealFramework.exists_internalFormula_reals_ge_not_interval`). The statement
proved has the hypothesis for all limited hyperreals $`a \ge r`, as in the analogous result of Section
11.6. In Exercise 15.4.4 the reciprocal is taken of $`\max(\underline s_n, 1)`. In Exercise
15.5.1 the element $`b` is required to lie in the range of the relation only when the set
$`A` is not empty. The overflow argument in the proof that sequential comprehensiveness implies
countable saturation is applied to a slightly different internal property than in the book.

*What is not proved.* The book states without proof that every superstructure has a
$`\kappa`-saturated enlargement for every cardinal $`\kappa`. The statement is
{name}`Goldblatt.NonstandardFramework.exists_saturated_enlargement`, and it is the only
statement of the chapter not fully proved: for $`\kappa \le \aleph_1` it is proved over
every base set, and for $`\kappa > \aleph_1` it is left open, since that case needs good
ultrafilters, which Mathlib does not have. The closing remarks of Section 15.5
on topological spaces are prose.
-/
