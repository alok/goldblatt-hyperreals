import Goldblatt.Ch11_InternalSets.Basic
import Goldblatt.Ch11_InternalSets.Definability
import Goldblatt.Ch11_InternalSets.Saturation

/-!
# 11. Internal and External Sets

In the ultrapower a point is the class of a sequence of points. This chapter applies the same
construction one level up: a sequence of _sets_ of standard elements determines a set of
elements of the ultrapower, by the almost-all criterion for membership. The sets obtained in
this way are the _internal_ sets, and all other sets are _external_. Enlargements are
internal, and so are intervals with hyperreal end points and initial segments of the
hypernaturals, but the sets that single out the standard world inside the nonstandard one
(the standard natural numbers, the reals, the limited numbers, the infinitesimals, the halos)
are external.

The distinction matters because the internal sets are exactly the sets to which the
properties of sets of reals transfer. A nonempty internal set of hypernaturals has a least
member, induction holds for internal sets, a bounded nonempty internal set of hyperreals has
a least upper bound. From these come the _permanence_ principles, which say that an internal
set cannot follow an external set exactly: overflow, underflow, and their continuous
analogues. Sets defined by first-order conditions from internal sets are internal (the
_internal set definition principle_), which is how internal sets are recognized in practice.
Finally the ultrapower is _countably saturated_: a decreasing sequence of nonempty internal
sets has a common point. Saturation produces nonstandard elements without transfer, makes
every infinite internal set uncountable, and shows that the shadow of an internal set is a
closed set of reals.

The formalization of the chapter is long, so it is split over three pages; this page is the
overview and the index.

## The three parts

* {lit}`Goldblatt.Ch11_InternalSets.Basic` covers Sections 11.1 to 11.6: internal sets and
  their examples, the Boolean algebra of internal sets with the almost-all criteria for
  inclusion and equality, the internal least number principle and internal induction, the
  overflow principle, internal order-completeness with its exercises, and the catalogue of
  external sets.
* {lit}`Goldblatt.Ch11_InternalSets.Definability` covers Sections 11.7 to 11.9: the internal
  set definition principle, the theorem that an internal set of reals is finite, the
  underflow principle, and the permanence theorem for halos.
* {lit}`Goldblatt.Ch11_InternalSets.Saturation` covers Sections 11.10 to 11.14: countable
  saturation and its corollaries, the nonstandard entities it creates, the size of internal
  sets, the closedness of the shadow of an internal set, and hyper-open sets.

## The sections of the chapter

Each section of the book's chapter is a section of one of the three parts, under the same
number.

* 11.1 Internal Sets (part 1).
* 11.2 Algebra of Internal Sets (part 1).
* 11.3 Internal Least Number Principle and Induction (part 1).
* 11.4 The Overflow Principle (part 1).
* 11.5 Internal Order-Completeness (part 1).
* 11.6 External Sets (part 1).
* 11.7 Defining Internal Sets (part 2).
* 11.8 The Underflow Principle (part 2).
* 11.9 Internal Sets and Permanence (part 2).
* 11.10 Saturation of Internal Sets (part 3).
* 11.11 Saturation Creates Nonstandard Entities (part 3).
* 11.12 The Size of an Internal Set (part 3).
* 11.13 Closure of the Shadow of an Internal Set (part 3).
* 11.14 Interval Topology and Hyper-Open Sets (part 3).

## Conventions of the formalization

* The internal set $`[A_n]` of a sequence of sets is {name}`Goldblatt.internalSet`, and its
  defining property is {name}`Goldblatt.ofSeq_mem_internalSet`. As in Chapter 3, the
  construction is made for an arbitrary type and its star type. The predicate "is internal"
  for a set in the star type of a type is {name}`Goldblatt.IsInternalSet`, which takes the
  type as an explicit argument; for sets of hyperreals it is abbreviated to
  {name}`Goldblatt.IsInternal`, and {name}`Goldblatt.IsExternal` is its negation.
* An internal set depends only on the germ of its defining sequence, so internal sets are
  the same thing as germs of set-valued sequences along the index ultrafilter:
  {name}`Goldblatt.internalSetEquiv`. In other words, an internal subset of the ultrapower
  of a type is an element of the ultrapower of its type of subsets.
* Lean's natural numbers start at $`0`, and the set of hypernaturals of Chapter 3 contains
  $`0`. Internal induction is therefore stated from $`0`
  ({name}`Goldblatt.IsInternal.induction`), with the book's form from $`1` as a corollary,
  and the intervals $`(0, \tfrac1n)` of the book appear as $`(0, \tfrac1{n+1})`.
* The principles for internal sets of hyperreals are stated in dot notation on a proof of
  internality: {name}`Goldblatt.IsInternal.exists_isLeast`,
  {name}`Goldblatt.IsInternal.overflow`, {name}`Goldblatt.IsInternal.underflow`,
  {name}`Goldblatt.IsInternal.exists_isLUB`,
  {name}`Goldblatt.IsInternal.exists_real_ball_subset`. Overflow and underflow do not need
  the book's hypothesis that the set consists of hypernaturals, and are stated without it.
* The internal set definition principle is proved in full for a small deeply embedded
  first-order language over internal relations, {name}`Goldblatt.IFormula`
  ({name}`Goldblatt.IFormula.starRealize_ofSeq` and
  {name}`Goldblatt.IFormula.isInternalSet_setOf_starRealize`). The definable sets needed in
  the proofs of underflow, of permanence for halos and of the closedness of shadows, and the
  sets of Exercise 11.7.1, are obtained from it by writing down the defining formula
  ({name}`Goldblatt.IFormula.isInternalSet_of_forall_iff`). A definable set can also be
  computed directly, by moving quantifiers inside "for almost all $`n`" with
  {name}`Goldblatt.forall_star_iff` and {name}`Goldblatt.exists_star_iff`; binary internal
  relations with their closure properties are {name}`Goldblatt.internalRel`.
* The transfer principle for sentences with a set symbol (the statement marked with a dagger
  in Section 11.7) is {name}`Goldblatt.SFormula.starRealize_of_forall_realize`, for a
  language {name}`Goldblatt.SFormula` with set symbols; as an example the internal least
  number principle is derived from it
  ({name}`Goldblatt.IsInternal.exists_isLeast_of_transfer`).
* Two exercises ask for the equivalence of two true statements about internal sets. To give
  such an equivalence content it is proved for an arbitrary class of sets with the one
  closure property the argument uses
  ({name}`Goldblatt.overflowPrinciple_iff_unboundedPrinciple`,
  {name}`Goldblatt.underflowPrinciple_iff_smallUnlimitedPrinciple`).
* Countable saturation is {name}`Goldblatt.iInter_nonempty_of_isInternalSet`, proved for the
  ultrapower over the natural numbers by the book's diagonal argument.
* Exercise 11.10.3 claims that the union of a strictly decreasing sequence of internal sets
  is external. That part of the exercise is false (such a union is its first term); the
  formalization proves the statement for increasing unions and for decreasing intersections
  and records the correction.
* The topologies of Section 10.5 that Section 11.14 refers to are restated in the namespace
  {lit}`Goldblatt.HyperTopology`, because this chapter does not depend on Chapter 10. They
  are to be identified with the definitions of the Chapter 10 page once that page exists.
* A few general facts about the predicates of Chapter 5 (positive unlimited numbers and
  integer parts) are proved here where they are first needed, for instance
  {name}`Goldblatt.PosUnlimited.hfloor`; they involve no internal sets.
-/
