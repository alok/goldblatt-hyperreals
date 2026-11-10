import Goldblatt.Ch14_Enlargements.Enlargement
import Goldblatt.Ch14_Enlargements.Collapse
import Goldblatt.Ch14_Enlargements.Los
import Goldblatt.Ch14_Enlargements.Terms
import Goldblatt.Ch14_Enlargements.Existence

/-!
# 14. The Existence of Nonstandard Entities

Chapter 13 defined a nonstandard framework as a map between two universes that satisfies the
transfer principle, and derived the theory of internal and hyperfinite sets from that
definition. Two questions were left open. The definition does not force anything nonstandard
to exist, since the identity map of a universe satisfies it, so results that need a
nonstandard hypernatural number had to assume one. And no framework other than the identity
was exhibited.

This chapter answers both. It isolates a property of frameworks, being an _enlargement_, from
which nonstandard entities of all kinds follow at once: infinitesimals, unlimited numbers,
nonstandard members of every infinite standard set, and hyperfinite sets that contain all
standard members of a given standard set. It shows that this property has two other
formulations, in terms of concurrent relations and of hyperfinite approximation. And it proves
that enlargements exist, by forming an ultrapower of a superstructure and collapsing it into a
second superstructure. The result is the enlargement theorem: over any set $`X` of individuals
the superstructure $`\mathbb U(X)` has an enlargement of the form $`\mathbb U({}^*X)`
({name}`Goldblatt.exists_enlargement`).

The book calls its account of the construction a sketch and leaves the verification as an
exercise. Here it is carried out in full, and it is the bulk of the chapter. The formalization
is split over five pages; this page is the overview and the index.

## The five parts

* {lit}`Goldblatt.Ch14_Enlargements.Enlargement` covers Sections 14.1 and 14.2 for an arbitrary
  framework: the definition of an enlargement, the examples of Section 14.1, concurrent
  relations and Theorem 14.2.1.
* {lit}`Goldblatt.Ch14_Enlargements.Collapse` begins Section 14.3: functions of bounded rank
  from an index set to a superstructure, the individuals of the ultrapower, and the collapsing
  map $`f \mapsto [f]` with its two basic properties.
* {lit}`Goldblatt.Ch14_Enlargements.Los` proves the theorem of Łoś by induction on formulas,
  relative to the terms of the formula.
* {lit}`Goldblatt.Ch14_Enlargements.Terms` treats tuples and function values, concludes that
  every bounded ultrapower is a nonstandard framework
  ({name}`Goldblatt.BoundedUltrapower.framework`), computes the transfer map, and proves
  Exercise 14.4(2).
* {lit}`Goldblatt.Ch14_Enlargements.Existence` chooses the ultrafilter on the finite subsets of
  the superstructure, proves the enlargement property in the two ways given in the book,
  answers Exercise 14.4(3), and states the enlargement theorem and its consequences for
  frameworks over the real numbers.

## 14.1 Enlargements

Part 1. The finite intersection property ({name}`Goldblatt.FIP`) and the enlargement property
({name}`Goldblatt.NonstandardFramework.IsEnlargement`). The four examples: positive
infinitesimals as the common members of the transformed intervals
({name}`Goldblatt.RealFramework.forall_mem_star_posIntervals_iff`,
{name}`Goldblatt.RealFramework.exists_pos_infinitesimal`) and nonzero infinitesimals from
punctured intervals ({name}`Goldblatt.RealFramework.exists_nonzero_infinitesimal`); unlimited
hyperreals ({name}`Goldblatt.RealFramework.exists_pos_unlimited`); nonstandard members of
infinite sets
({name}`Goldblatt.NonstandardFramework.IsEnlargement.exists_mem_star_notMem_im`); hyperfinite
approximations ({name}`Goldblatt.NonstandardFramework.IsEnlargement.exists_hyperfinite`). The
enlargement theorem announced at the end of the section is proved under 14.3.

## 14.2 Concurrence and Hyperfinite Approximation

Part 1. Concurrent relations ({name}`Goldblatt.Concurrent`) and the four examples, each with
the concurrency of the relation and the description of a bound of its transform: the two order
relations on the positive reals
({name}`Goldblatt.RealFramework.pos_infinitesimal_of_bound_gtRel`,
{name}`Goldblatt.RealFramework.pos_unlimited_of_bound_ltRel`), the nonidentity relation
({name}`Goldblatt.concurrent_neRel_iff`,
{name}`Goldblatt.NonstandardFramework.mem_star_notMem_im_of_bound_neRel`) and the membership
relation ({name}`Goldblatt.concurrent_memRel`). Theorem 14.2.1 is
{name}`Goldblatt.NonstandardFramework.enlargement_tfae`.

## 14.3 Enlargements as Ultrapowers

Parts 2 to 5. Functions of bounded rank and their rank
({name}`Goldblatt.BoundedUltrapower.Bdd`, {name}`Goldblatt.BoundedUltrapower.eventually_rank_eq_rk`),
the collapse $`f \mapsto [f]` ({name}`Goldblatt.BoundedUltrapower.col`,
{name}`Goldblatt.BoundedUltrapower.col_eq_iff`,
{name}`Goldblatt.BoundedUltrapower.col_mem_col_iff`), the theorem of Łoś
({name}`Goldblatt.BoundedUltrapower.los`), the framework
({name}`Goldblatt.BoundedUltrapower.framework`), the ultrafilter on the finite subsets of the
superstructure ({name}`Goldblatt.BoundedUltrapower.ultra`), the enlargement property
({name}`Goldblatt.BoundedUltrapower.isEnlargement_enlargement`), and the enlargement theorem
({name}`Goldblatt.exists_enlargement`).

## 14.4 Exercises on the Ultrapower Construction

Exercise (1), the details of the construction, is the content of parts 2 to 4. Exercise (2) is
{name}`Goldblatt.BoundedUltrapower.isFunction_col` and
{name}`Goldblatt.BoundedUltrapower.app_col_eq_iff` in part 4. Exercise (3) is
{name}`Goldblatt.BoundedUltrapower.ultra_ne_pure` in part 5.

## Design of the formalization

*Enlargements.* The enlargement property is a property of a framework
({name}`Goldblatt.NonstandardFramework.IsEnlargement`), because a framework in the sense of
Chapter 13 already carries its transfer map. Collections with the finite intersection property
and concurrent relations are members of the standard universe, and "finitely many" is
expressed with finite sets of Lean ({name}`Goldblatt.FIP`, {name}`Goldblatt.Concurrent`).

*The ultrapower.* The index set of an ultrapower is a type, and the functions on it are
functions of Lean into Mathlib's sets. The standard universe is a superstructure
$`\mathbb U(X)` over a set $`X` whose members are individuals in the sense of Chapter 13
({name}`Goldblatt.IsBaseSet`). The construction works for every ultrafilter on every index type
that is small relative to the universe level of the sets, and always yields a framework; only
the enlargement property needs the particular ultrafilter of Section 14.3.

*Individuals.* In Chapter 13 an individual of a universe is a nonempty set that has no member
in the universe. The collapse has to send the constant function at $`x \in X` to $`x` itself,
so the old individuals are kept, and it has to send every other function of rank zero to a new
individual. Both kinds must be individuals of the new superstructure. The new ones are built
with set-theoretic rank above that of $`\mathbb U(X)`, and a comparison of ranks shows that the
part of the new superstructure of low rank is the old one
({name}`Goldblatt.BoundedUltrapower.isBaseSet_base`).

*Transfer.* The transfer axiom of Chapter 13 covers all sentences of the deep embedding,
including those with undefined terms, which count as false. The theorem of Łoś is therefore
proved in the same generality ({name}`Goldblatt.BoundedUltrapower.los`): its statement for terms
includes that a term is defined at the classes of the functions if and only if it is defined
at almost all indices. This is done by expressing the conditions for definedness as bounded
formulas whose terms are variables, proving the theorem first for such formulas, and then
using it for the general case.

*Corrections and remarks.* The third example of Section 14.2 says that the nonidentity relation
on a set is concurrent exactly when the set is infinite; this needs the set to have at least
two members, and the hypothesis is added
({name}`Goldblatt.concurrent_neRel_iff`). Section 14.3 remarks that a nonprincipal ultrafilter
gives nonstandard members of the transform of the real numbers, with a reference to Chapter 3.
That argument is for the index set $`\mathbb N`. It is formalized for every nonprincipal
ultrafilter on $`\mathbb N`
({name}`Goldblatt.BoundedUltrapower.exists_mem_star_notMem_im_of_nonprincipal`) and, on an
arbitrary index set, for every countably incomplete ultrafilter
({name}`Goldblatt.BoundedUltrapower.exists_mem_star_notMem_im_of_countablyIncomplete`); for a
countably complete nonprincipal ultrafilter the remark would be false. Exercise 14.4(2) is
stated without a hypothesis on domains, as in the book; where the argument is outside the
domain it is a statement about the value convention of Chapter 13, under which such a value is
the empty set.

## Consequences for Chapter 13

Chapter 13 proves that the natural numbers, and the image of any infinite set, are external
under the hypothesis that a nonstandard hypernatural number exists. In an enlargement over the
real numbers that hypothesis is a theorem
({name}`Goldblatt.RealFramework.exists_nonstandard_nat`), and such enlargements exist
({name}`Goldblatt.exists_realFramework_isEnlargement`). So the standing assumptions of Part IV
are consistent, and from here on a framework can be taken to be an enlargement.
-/
