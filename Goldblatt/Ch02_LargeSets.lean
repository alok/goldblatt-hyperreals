import Mathlib

/-!
# 2. Large Sets

The hyperreals are going to be built from real sequences by identifying two sequences when they
agree on a "large" set of indices. This chapter pins down what "large" has to mean. The
requirements one is led to (the whole index set is large, large sets are closed under
intersection and under passing to supersets, the empty set is not large, and of a set and its
complement exactly one is large) are precisely the axioms of an _ultrafilter_. The chapter
develops the elementary theory of filters on a set $`I`, and ends with the one fact the
construction of Chapter 3 really needs: every infinite set carries a nonprincipal ultrafilter.

Two vocabularies are in play.

* The book treats a filter as a _collection of subsets_ $`\mathcal F \subseteq \mathcal P(I)`
  satisfying axioms. We formalize this literally, as predicates {lit}`IsFilter`,
  {lit}`IsProperFilter` and {lit}`IsUltrafilter` on a term of type
  {lit}`Set (Set I)`, and prove every numbered fact and exercise of the chapter in that form,
  by the book's elementary arguments (including the Zorn's lemma proof of the ultrafilter
  theorem).
* Mathlib has bundled types {name}`Filter` and {name}`Ultrafilter`. A Mathlib filter is what the
  book calls a filter, with one difference: the book reserves the word _proper_ for a filter
  that omits the empty set, and an ultrafilter is proper by definition, whereas in Mathlib
  properness is the separate type class {name}`Filter.NeBot` (the improper filter is the bottom
  element). The dictionary is made explicit in {lit}`IsFilter.toFilter`,
  {lit}`isProperFilter_sets_iff` and {lit}`ultrafilterEquiv`.

The final section fixes the index ultrafilter used by all later chapters: Mathlib's
{name}`Filter.hyperfilter` on the natural numbers, a nonprincipal ultrafilter. Its basic
properties are restated there under stable names.

The book assumes throughout that the index set $`I` is nonempty. We add that hypothesis (as
{lit}`Nonempty I`) exactly where a statement needs it.
-/

namespace Goldblatt

open Set Filter

variable {I : Type*} {F G H : Set (Set I)} {A B : Set I}

/-!
## 2.1 Infinitesimals as Variable Quantities

This section of the book is historical motivation with no formal content. Cauchy thought of an
infinitesimal as a variable quantity tending to zero, which suggests that a sequence converging
to zero should _represent_ an infinitely small number, with faster convergence meaning a
smaller number, and a sequence diverging to infinity should represent an infinitely large one.
The classical construction of the reals from Cauchy sequences cannot do this, since it sends
every null sequence to zero. A different equivalence relation on sequences is needed, and the
rest of the chapter looks for it.

## 2.2 Largeness

Two sequences are to be identified when their _agreement set_ is large. Reflexivity of the
resulting relation forces the whole index set to be large; transitivity is guaranteed if large
sets are closed under intersections and supersets, because of the inclusion
{lit}`agreementSet_inter_subset`; and the empty set must not be large, or all
sequences would be identified.

Cofinite sets satisfy all of this, but the quotient should also be _linearly ordered_ by
comparing sequences on a large set, and then the two alternating zero-one sequences show that
cofiniteness is too strict a notion: the set where the first is smaller is the set of even
indices, the set where the second is smaller is the set of odd indices, and neither is cofinite.
What is missing is the requirement that of a set and its complement, one is always large.
-/

/-- **Section 2.2, agreement set.** For sequences $`r` and $`s`, the set
$`E_{rs} = \{n : r_n = s_n\}` of indices where they agree. -/
def agreementSet {α : Type*} (r s : ℕ → α) : Set ℕ := {n | r n = s n}

/-- **Section 2.2.** A sequence agrees with itself everywhere, so $`E_{rr}` is all of
$`\mathbb N`; this is why the whole index set must count as large. -/
theorem agreementSet_self {α : Type*} (r : ℕ → α) : agreementSet r r = univ :=
  eq_univ_of_forall fun _ => rfl

/-- **Section 2.2.** Agreement sets are symmetric: $`E_{rs} = E_{sr}`. -/
theorem agreementSet_comm {α : Type*} (r s : ℕ → α) : agreementSet r s = agreementSet s r :=
  Set.ext fun _ => eq_comm

/-- **Section 2.2.** $`E_{rs} \cap E_{st} \subseteq E_{rt}`. This inclusion is what turns
"closed under intersections and supersets" into transitivity of the equivalence relation. -/
theorem agreementSet_inter_subset {α : Type*} (r s t : ℕ → α) :
    agreementSet r s ∩ agreementSet s t ⊆ agreementSet r t :=
  fun _ h => Eq.trans h.1 h.2

/-- **Section 2.2.** For real sequences $`r` and $`s`, the set $`L_{rs} = \{n : r_n < s_n\}`
of indices where $`r` is strictly below $`s`. -/
def lessSet (r s : ℕ → ℝ) : Set ℕ := {n | r n < s n}

/-- **Section 2.2.** The sequence $`1, 0, 1, 0, \dots` (indexed, as in the book, so that the
first term has index one: the value is one at odd indices and zero at even ones). Lean's naturals
start at zero, so there is one extra term at index zero, with value zero; the book's sequence is
the restriction to indices at least one. -/
def alternatingOneZero : ℕ → ℝ := fun n => if Odd n then 1 else 0

/-- **Section 2.2.** The sequence $`0, 1, 0, 1, \dots` (value zero at odd indices and one at
even ones). Lean's naturals start at zero, so there is one extra term at index zero, with value
one; the book's sequence is the restriction to indices at least one. -/
def alternatingZeroOne : ℕ → ℝ := fun n => if Odd n then 0 else 1

/-- **Section 2.2.** The two alternating sequences agree nowhere. -/
theorem agreementSet_alternating : agreementSet alternatingOneZero alternatingZeroOne = ∅ := by
  ext n
  by_cases h : Odd n <;> simp [agreementSet, alternatingOneZero, alternatingZeroOne, h]

/-- **Section 2.2.** The first alternating sequence is below the second exactly on the even
numbers. -/
theorem lessSet_alternatingOneZero :
    lessSet alternatingOneZero alternatingZeroOne = {n | Even n} := by
  ext n
  by_cases h : Odd n
  · simp [lessSet, alternatingOneZero, alternatingZeroOne, h, Nat.not_even_iff_odd.mpr h]
  · simp [lessSet, alternatingOneZero, alternatingZeroOne, h, Nat.not_odd_iff_even.mp h]

/-- **Section 2.2.** The second alternating sequence is below the first exactly on the odd
numbers. -/
theorem lessSet_alternatingZeroOne :
    lessSet alternatingZeroOne alternatingOneZero = {n | Odd n} := by
  ext n
  by_cases h : Odd n <;> simp [lessSet, alternatingOneZero, alternatingZeroOne, h]

/-- **Section 2.2.** There are infinitely many even numbers. -/
theorem infinite_setOf_even : {n : ℕ | Even n}.Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n)
    (fun _ _ h => Nat.eq_of_mul_eq_mul_left two_pos h) fun n => even_two_mul n

/-- **Section 2.2.** There are infinitely many odd numbers. -/
theorem infinite_setOf_odd : {n : ℕ | Odd n}.Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n + 1)
    (fun _ _ h => Nat.eq_of_mul_eq_mul_left two_pos (Nat.add_right_cancel h))
    fun n => odd_two_mul_add_one n

/-- **Section 2.2.** The even numbers and the odd numbers are complementary. -/
theorem compl_setOf_even : {n : ℕ | Even n}ᶜ = {n | Odd n} := by
  ext n
  simp

/-- **Section 2.2.** The set of even numbers is not cofinite, so "cofinite" cannot be the
notion of largeness that linearly orders the quotient. -/
theorem not_finite_compl_setOf_even : ¬ ({n : ℕ | Even n}ᶜ).Finite := by
  rw [compl_setOf_even]
  exact infinite_setOf_odd

/-- **Section 2.2.** The set of odd numbers is not cofinite either. -/
theorem not_finite_compl_setOf_odd : ¬ ({n : ℕ | Odd n}ᶜ).Finite := by
  rw [← compl_setOf_even, compl_compl]
  exact infinite_setOf_even

/-!
## 2.3 Filters

A filter on $`I` is a nonempty collection of subsets of $`I` closed under binary intersections
and under supersets. It is proper when it does not contain the empty set, and an ultrafilter
when it is proper and decides every subset: it contains the set or its complement. We set these
up as predicates on collections and connect them to Mathlib's bundled filters.
-/

/-- **Section 2.3, filter.** A collection $`\mathcal F \subseteq \mathcal P(I)` is a filter on
$`I` when it is nonempty, contains $`A \cap B` whenever it contains $`A` and $`B`, and contains
every superset of each of its members. As in the book, the collection of all subsets is allowed;
see {lit}`IsProperFilter`. -/
structure IsFilter (F : Set (Set I)) : Prop where
  /-- A filter is a nonempty collection. -/
  nonempty : F.Nonempty
  /-- Intersection axiom. -/
  inter_mem : ∀ {A B : Set I}, A ∈ F → B ∈ F → A ∩ B ∈ F
  /-- Superset axiom. -/
  superset_mem : ∀ {A B : Set I}, A ∈ F → A ⊆ B → B ∈ F

/-- **Section 2.3, proper filter.** A filter is proper when it does not contain the empty
set. -/
structure IsProperFilter (F : Set (Set I)) : Prop extends IsFilter F where
  /-- A proper filter omits the empty set. -/
  empty_notMem : ∅ ∉ F

/-- **Section 2.3, ultrafilter.** An ultrafilter is a proper filter that contains, for every
$`A \subseteq I`, either $`A` or its complement. -/
structure IsUltrafilter (F : Set (Set I)) : Prop extends IsProperFilter F where
  /-- An ultrafilter decides every set. -/
  mem_or_compl_mem : ∀ A : Set I, A ∈ F ∨ Aᶜ ∈ F

/-- **Section 2.3.** Every filter contains the whole index set $`I`. -/
theorem IsFilter.univ_mem (hF : IsFilter F) : univ ∈ F := by
  obtain ⟨A, hA⟩ := hF.nonempty
  exact hF.superset_mem hA (subset_univ A)

/-- **Section 2.3.** A filter contains the intersection of any finite subcollection of its
members. -/
theorem IsFilter.sInter_mem (hF : IsFilter F) (s : Finset (Set I))
    (hs : (↑s : Set (Set I)) ⊆ F) : ⋂₀ (↑s : Set (Set I)) ∈ F := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hF.univ_mem
  | insert A s _ ih =>
    rw [Finset.coe_insert, insert_subset_iff] at hs
    rw [Finset.coe_insert, sInter_insert]
    exact hF.inter_mem hs.1 (ih hs.2)

/-- **Section 2.3.** To show $`B \in \mathcal F` it suffices to find finitely many members
$`A_1, \dots, A_n` of $`\mathcal F` with $`A_1 \cap \dots \cap A_n \subseteq B`. -/
theorem IsFilter.mem_of_sInter_subset (hF : IsFilter F) (s : Finset (Set I))
    (hs : (↑s : Set (Set I)) ⊆ F) (hB : ⋂₀ (↑s : Set (Set I)) ⊆ B) : B ∈ F :=
  hF.superset_mem (hF.sInter_mem s hs) hB

/-- **Section 2.2.** The single requirement on large sets from which the filter axioms are
distilled: if $`A` and $`B` are large and $`A \cap B \subseteq C`, then $`C` is large. This is
the two-set case of {lit}`IsFilter.mem_of_sInter_subset`. -/
theorem IsFilter.mem_of_inter_subset (hF : IsFilter F) {A B C : Set I} (hA : A ∈ F) (hB : B ∈ F)
    (h : A ∩ B ⊆ C) : C ∈ F :=
  hF.superset_mem (hF.inter_mem hA hB) h

/-- **Section 2.2.** For an arbitrary collection $`\mathcal F`, the single requirement
"$`A, B \in \mathcal F` and $`A \cap B \subseteq C` imply $`C \in \mathcal F`" is equivalent to
the conjunction of closure under binary intersections and closure under supersets: take
$`C = A \cap B` for the first and $`B = A` for the second. -/
theorem filter_axioms_iff_mem_of_inter_subset (F : Set (Set I)) :
    ((∀ A B, A ∈ F → B ∈ F → A ∩ B ∈ F) ∧ (∀ A B, A ∈ F → A ⊆ B → B ∈ F)) ↔
      ∀ A B C, A ∈ F → B ∈ F → A ∩ B ⊆ C → C ∈ F := by
  constructor
  · rintro ⟨hinter, hsup⟩ A B C hA hB h
    exact hsup _ _ (hinter A B hA hB) h
  · intro h
    refine ⟨fun A B hA hB => h A B _ hA hB Subset.rfl, fun A B hA hAB => h A A B hA hA ?_⟩
    rw [inter_self]
    exact hAB

/-- **Section 2.3.** A filter is exactly a nonempty collection satisfying the single requirement
of Section 2.2. -/
theorem isFilter_iff_mem_of_inter_subset (F : Set (Set I)) :
    IsFilter F ↔ F.Nonempty ∧ ∀ A B C, A ∈ F → B ∈ F → A ∩ B ⊆ C → C ∈ F := by
  rw [← filter_axioms_iff_mem_of_inter_subset]
  exact ⟨fun h => ⟨h.nonempty, fun _ _ => h.inter_mem, fun _ _ => h.superset_mem⟩,
    fun h => ⟨h.1, fun {_ _} => h.2.1 _ _, fun {_ _} => h.2.2 _ _⟩⟩

/-- **Section 2.3.** A filter contains the empty set if and only if it is the whole power
set. -/
theorem IsFilter.empty_mem_iff (hF : IsFilter F) : ∅ ∈ F ↔ F = univ :=
  ⟨fun h => eq_univ_of_forall fun A => hF.superset_mem h (empty_subset A), fun h => h ▸ mem_univ _⟩

/-- **Section 2.3.** The power set of $`I` is a filter (the improper one). -/
theorem isFilter_univ : IsFilter (univ : Set (Set I)) where
  nonempty := ⟨univ, mem_univ _⟩
  inter_mem := fun _ _ => mem_univ _
  superset_mem := fun _ _ => mem_univ _

/-- **Section 2.3.** A filter is proper if and only if it is not the whole power set. -/
theorem IsFilter.isProperFilter_iff_ne_univ (hF : IsFilter F) : IsProperFilter F ↔ F ≠ univ :=
  ⟨fun h hu => h.empty_notMem (hF.empty_mem_iff.mpr hu),
    fun h => ⟨hF, fun he => h (hF.empty_mem_iff.mp he)⟩⟩

/-- **Section 2.3.** The one-element collection $`\{I\}` is a filter. -/
theorem isFilter_singleton_univ : IsFilter ({univ} : Set (Set I)) where
  nonempty := ⟨univ, rfl⟩
  inter_mem := by
    intro A B hA hB
    rw [mem_singleton_iff] at hA hB ⊢
    rw [hA, hB, inter_self]
  superset_mem := by
    intro A B hA hAB
    rw [mem_singleton_iff] at hA ⊢
    rw [hA] at hAB
    exact univ_subset_iff.mp hAB

/-- **Section 2.3.** $`\{I\}` is the smallest filter on $`I`: it is contained in every
filter. -/
theorem IsFilter.singleton_univ_subset (hF : IsFilter F) : ({univ} : Set (Set I)) ⊆ F :=
  singleton_subset_iff.mpr hF.univ_mem

/-- **Section 2.3.** The index set of a proper filter is nonempty. -/
theorem IsProperFilter.nonempty_index (hF : IsProperFilter F) : Nonempty I := by
  by_contra h
  rw [not_nonempty_iff] at h
  exact hF.empty_notMem (by simpa [Set.eq_empty_of_isEmpty (univ : Set I)] using hF.univ_mem)

/-- **Section 2.3.** Every member of a proper filter is a nonempty set. -/
theorem IsProperFilter.nonempty_of_mem (hF : IsProperFilter F) (hA : A ∈ F) : A.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  exact hF.empty_notMem hA

/-!
### The dictionary with Mathlib

The members of a Mathlib {name}`Filter` form a filter in the book's sense, and every filter in
the book's sense arises this way. Properness corresponds to {name}`Filter.NeBot`, and the
ultrafilters of the book correspond bijectively to the terms of Mathlib's {name}`Ultrafilter`.
-/

/-- **Section 2.3 (dictionary).** A filter in the book's sense, bundled as a Mathlib
{name}`Filter` with the same members. -/
def IsFilter.toFilter (hF : IsFilter F) : Filter I where
  sets := F
  univ_sets := hF.univ_mem
  sets_of_superset := fun hA hAB => hF.superset_mem hA hAB
  inter_sets := fun hA hB => hF.inter_mem hA hB

/-- **Section 2.3 (dictionary).** Membership in the bundled filter is membership in the
collection. -/
@[simp]
theorem IsFilter.mem_toFilter (hF : IsFilter F) : A ∈ hF.toFilter ↔ A ∈ F :=
  Iff.rfl

/-- **Section 2.3 (dictionary).** The collection of members of a Mathlib filter is a filter in
the book's sense. -/
theorem isFilter_sets (f : Filter I) : IsFilter f.sets where
  nonempty := ⟨univ, f.univ_sets⟩
  inter_mem := fun hA hB => f.inter_sets hA hB
  superset_mem := fun hA hAB => f.sets_of_superset hA hAB

/-- **Section 2.3 (dictionary).** A Mathlib filter is proper in the book's sense exactly when
it satisfies {name}`Filter.NeBot`, that is, when it is not the bottom filter. -/
theorem isProperFilter_sets_iff (f : Filter I) : IsProperFilter f.sets ↔ f.NeBot := by
  rw [neBot_iff, Ne, ← empty_mem_iff_bot]
  exact ⟨fun h => h.empty_notMem, fun h => ⟨isFilter_sets f, h⟩⟩

/-- **Section 2.3 (dictionary).** The bundled filter of a book filter satisfies
{name}`Filter.NeBot` exactly when the collection omits the empty set. -/
theorem IsFilter.toFilter_neBot_iff (hF : IsFilter F) : hF.toFilter.NeBot ↔ ∅ ∉ F := by
  rw [neBot_iff, Ne, ← empty_mem_iff_bot]
  rfl

/-- **Section 2.3 (dictionary).** The collection of members of a Mathlib ultrafilter is an
ultrafilter in the book's sense. -/
theorem isUltrafilter_sets (U : Ultrafilter I) : IsUltrafilter (U : Filter I).sets where
  toIsFilter := isFilter_sets _
  empty_notMem := U.empty_notMem
  mem_or_compl_mem := U.mem_or_compl_mem

/-- **Section 2.3 (dictionary).** An ultrafilter in the book's sense, bundled as a Mathlib
{name}`Ultrafilter` with the same members. -/
def IsUltrafilter.toUltrafilter (hF : IsUltrafilter F) : Ultrafilter I :=
  Ultrafilter.ofComplNotMemIff hF.toIsFilter.toFilter fun A => by
    constructor
    · intro h
      exact (hF.mem_or_compl_mem A).resolve_right h
    · intro hA hAc
      have h := hF.inter_mem hA hAc
      rw [inter_compl_self] at h
      exact hF.empty_notMem h

/-- **Section 2.3 (dictionary).** Membership in the bundled ultrafilter is membership in the
collection. -/
@[simp]
theorem IsUltrafilter.mem_toUltrafilter (hF : IsUltrafilter F) : A ∈ hF.toUltrafilter ↔ A ∈ F :=
  Iff.rfl

/-- **Section 2.3 (dictionary).** Ultrafilters on $`I` in the book's sense are the same thing
as terms of Mathlib's {name}`Ultrafilter`: the two bundling maps are mutually inverse. -/
def ultrafilterEquiv (I : Type*) : {F : Set (Set I) // IsUltrafilter F} ≃ Ultrafilter I where
  toFun F := F.2.toUltrafilter
  invFun U := ⟨(U : Filter I).sets, isUltrafilter_sets U⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Ultrafilter.ext fun _ => Iff.rfl

/-!
## 2.4 Examples of Filters

Four families of examples: the principal ultrafilter of all sets containing a given point; the
cofinite (Fréchet) filter; the filter generated by an arbitrary collection, with the principal
filter of supersets of a fixed set as a special case; and the union of a chain of filters. The
claim that on a finite index set every ultrafilter is principal belongs to Example (1) but its
proof uses Fact 2.5(5), so it appears below as
{lit}`IsUltrafilter.isPrincipal_of_finite`.
-/

/-- **Example 2.4(1), principal ultrafilter.** The collection
$`\mathcal F^i = \{A \subseteq I : i \in A\}` of all sets containing the point $`i`. -/
def principalUltrafilter (i : I) : Set (Set I) := {A | i ∈ A}

/-- **Example 2.4(1).** Membership in $`\mathcal F^i` means containing $`i`. -/
@[simp]
theorem mem_principalUltrafilter {i : I} : A ∈ principalUltrafilter i ↔ i ∈ A :=
  Iff.rfl

/-- **Example 2.4(1).** $`\mathcal F^i` is an ultrafilter. -/
theorem isUltrafilter_principalUltrafilter (i : I) : IsUltrafilter (principalUltrafilter i) where
  nonempty := ⟨univ, mem_univ i⟩
  inter_mem := fun hA hB => ⟨hA, hB⟩
  superset_mem := fun hA hAB => hAB hA
  empty_notMem := fun h => notMem_empty i h
  mem_or_compl_mem := fun A => Classical.em (i ∈ A)

/-- **Example 2.4(1), principal.** An ultrafilter (or any collection) is principal when it is
$`\mathcal F^i` for some point $`i`. -/
def IsPrincipal (F : Set (Set I)) : Prop := ∃ i, F = principalUltrafilter i

/-- **Example 2.4(1) (dictionary).** $`\mathcal F^i` is the collection of members of Mathlib's
principal ultrafilter {lit}`pure i`. -/
theorem principalUltrafilter_eq_pure_sets (i : I) :
    principalUltrafilter i = ((pure i : Ultrafilter I) : Filter I).sets :=
  rfl

/-- **Example 2.4(1) (dictionary).** A Mathlib ultrafilter is principal in the book's sense
exactly when it equals {lit}`pure i` for some $`i`. -/
theorem isPrincipal_sets_iff (U : Ultrafilter I) :
    IsPrincipal (U : Filter I).sets ↔ ∃ i, U = pure i := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, Ultrafilter.ext fun A => by
      have : A ∈ (U : Filter I).sets ↔ A ∈ principalUltrafilter i := by rw [hi]
      exact this⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

/-- **Example 2.4(2), cofinite filter.** The Fréchet filter
$`\mathcal F^{co} = \{A \subseteq I : I - A \text{ is finite}\}`. -/
def cofiniteFilter (I : Type*) : Set (Set I) := {A | Aᶜ.Finite}

/-- **Example 2.4(2).** Membership in $`\mathcal F^{co}` means having finite complement. -/
@[simp]
theorem mem_cofiniteFilter : A ∈ cofiniteFilter I ↔ Aᶜ.Finite :=
  Iff.rfl

/-- **Example 2.4(2).** The cofinite sets form a filter. -/
theorem isFilter_cofiniteFilter (I : Type*) : IsFilter (cofiniteFilter I) where
  nonempty := ⟨univ, by simp⟩
  inter_mem := by
    intro A B hA hB
    rw [mem_cofiniteFilter, compl_inter]
    exact hA.union hB
  superset_mem := fun hA hAB => hA.subset (compl_subset_compl.mpr hAB)

/-- **Example 2.4(2) (dictionary).** $`\mathcal F^{co}` is the collection of members of
Mathlib's {name}`Filter.cofinite`. -/
theorem cofiniteFilter_eq_cofinite_sets (I : Type*) :
    cofiniteFilter I = (Filter.cofinite : Filter I).sets := by
  ext A
  exact mem_cofinite.symm

/-- **Example 2.4(2).** The cofinite filter omits the empty set exactly when $`I` is
infinite. -/
theorem empty_notMem_cofiniteFilter_iff : ∅ ∉ cofiniteFilter I ↔ Infinite I := by
  rw [mem_cofiniteFilter, compl_empty, finite_univ_iff, not_finite_iff_infinite]

/-- **Example 2.4(2).** The cofinite filter is proper if and only if $`I` is infinite. -/
theorem isProperFilter_cofiniteFilter_iff : IsProperFilter (cofiniteFilter I) ↔ Infinite I :=
  ⟨fun h => empty_notMem_cofiniteFilter_iff.mp h.empty_notMem,
    fun h => ⟨isFilter_cofiniteFilter I, empty_notMem_cofiniteFilter_iff.mpr h⟩⟩

/-- **Example 2.4(2).** The cofinite filter is never an ultrafilter. If $`I` is finite it is
not proper; if $`I` is infinite, split a countably infinite subset into two infinite halves:
one half is a set that is neither cofinite nor has cofinite complement. -/
theorem not_isUltrafilter_cofiniteFilter (I : Type*) : ¬ IsUltrafilter (cofiniteFilter I) := by
  intro hU
  have : Infinite I := isProperFilter_cofiniteFilter_iff.mp hU.toIsProperFilter
  let e := Infinite.natEmbedding I
  have hE : (e '' {n | Even n}).Infinite := infinite_setOf_even.image e.injective.injOn
  have hO : (e '' {n | Odd n}).Infinite := infinite_setOf_odd.image e.injective.injOn
  have hsub : e '' {n | Odd n} ⊆ (e '' {n | Even n})ᶜ := by
    rintro _ ⟨n, hn, rfl⟩ ⟨m, hm, hmn⟩
    rw [e.injective hmn] at hm
    exact Nat.not_even_iff_odd.mpr hn hm
  rcases hU.mem_or_compl_mem (e '' {n | Even n}) with h | h
  · exact hO (h.subset hsub)
  · rw [mem_cofiniteFilter, compl_compl] at h
    exact hE h

/-- **Example 2.4(3), generated filter.** For a collection $`\mathcal H \subseteq \mathcal P(I)`,
the collection $`\mathcal F^{\mathcal H}` of all sets that include an intersection
$`B_1 \cap \dots \cap B_n` of finitely many members of $`\mathcal H`. The empty intersection is
$`I`, so for empty $`\mathcal H` this definition gives $`\{I\}`, which is the book's separate
convention for that case (see {lit}`generatedFilter_empty`). -/
def generatedFilter (H : Set (Set I)) : Set (Set I) :=
  {A | ∃ s : Finset (Set I), (↑s : Set (Set I)) ⊆ H ∧ ⋂₀ (↑s : Set (Set I)) ⊆ A}

/-- **Example 2.4(3), Exercise 2.7(4)(i), first half.** $`\mathcal F^{\mathcal H}` is a
filter. -/
theorem isFilter_generatedFilter (H : Set (Set I)) : IsFilter (generatedFilter H) where
  nonempty := ⟨univ, ∅, by simp, subset_univ _⟩
  inter_mem := by
    classical
    rintro A B ⟨s, hs, hsA⟩ ⟨t, ht, htB⟩
    refine ⟨s ∪ t, ?_, ?_⟩
    · rw [Finset.coe_union]
      exact union_subset hs ht
    · rw [Finset.coe_union, sInter_union]
      exact inter_subset_inter hsA htB
  superset_mem := by
    rintro A B ⟨s, hs, hsA⟩ hAB
    exact ⟨s, hs, hsA.trans hAB⟩

/-- **Example 2.4(3), Exercise 2.7(4)(i), second half.** $`\mathcal F^{\mathcal H}` includes
$`\mathcal H`. -/
theorem subset_generatedFilter (H : Set (Set I)) : H ⊆ generatedFilter H := by
  intro A hA
  exact ⟨{A}, by simpa using hA, by simp⟩

/-- **Example 2.4(3), Exercise 2.7(4)(ii).** $`\mathcal F^{\mathcal H}` is the smallest filter
including $`\mathcal H`: it is included in every filter that includes $`\mathcal H`. -/
theorem generatedFilter_subset (hG : IsFilter G) (hHG : H ⊆ G) : generatedFilter H ⊆ G := by
  rintro A ⟨s, hs, hsA⟩
  exact hG.mem_of_sInter_subset s (hs.trans hHG) hsA

/-- **Example 2.4(3).** Generating is monotone in the collection. -/
theorem generatedFilter_mono {H K : Set (Set I)} (h : H ⊆ K) :
    generatedFilter H ⊆ generatedFilter K :=
  generatedFilter_subset (isFilter_generatedFilter K) (h.trans (subset_generatedFilter K))

/-- **Example 2.4(3).** A filter is generated by itself. -/
theorem IsFilter.generatedFilter_eq (hF : IsFilter F) : generatedFilter F = F :=
  Subset.antisymm (generatedFilter_subset hF Subset.rfl) (subset_generatedFilter F)

/-- **Example 2.4(3).** The filter generated by the empty collection is $`\{I\}`. -/
theorem generatedFilter_empty : generatedFilter (∅ : Set (Set I)) = {univ} :=
  Subset.antisymm (generatedFilter_subset isFilter_singleton_univ (empty_subset _))
    (isFilter_generatedFilter ∅).singleton_univ_subset

/-- **Example 2.4(3) (dictionary).** $`\mathcal F^{\mathcal H}` is the collection of members
of Mathlib's {name}`Filter.generate`. -/
theorem generatedFilter_eq_generate_sets (H : Set (Set I)) :
    generatedFilter H = (Filter.generate H).sets := by
  ext A
  change A ∈ generatedFilter H ↔ A ∈ Filter.generate H
  rw [mem_generate_iff]
  constructor
  · rintro ⟨s, hs, hsA⟩
    exact ⟨↑s, hs, s.finite_toSet, hsA⟩
  · rintro ⟨t, ht, hfin, htA⟩
    exact ⟨hfin.toFinset, by simpa using ht, by simpa using htA⟩

/-- **Example 2.4(3), principal filter.** The collection $`\{A \subseteq I : A \supseteq B\}`
of all supersets of a fixed set $`B`. -/
def principalFilter (B : Set I) : Set (Set I) := {A | B ⊆ A}

/-- **Example 2.4(3).** If $`\mathcal H` has the single member $`B`, the filter it generates is
the principal filter of all supersets of $`B`. -/
theorem generatedFilter_singleton (B : Set I) : generatedFilter {B} = principalFilter B := by
  ext A
  constructor
  · rintro ⟨s, hs, hsA⟩
    refine Subset.trans (subset_sInter fun C hC => ?_) hsA
    rw [mem_singleton_iff.mp (hs hC)]
  · intro hBA
    exact (isFilter_generatedFilter {B}).superset_mem
      (subset_generatedFilter {B} (mem_singleton B)) hBA

/-- **Example 2.4(3).** The principal filter of supersets of $`B` is a filter. -/
theorem isFilter_principalFilter (B : Set I) : IsFilter (principalFilter B) :=
  generatedFilter_singleton B ▸ isFilter_generatedFilter {B}

/-- **Example 2.4(3) (dictionary).** The principal filter of supersets of $`B` is the
collection of members of Mathlib's {name}`Filter.principal`. -/
theorem principalFilter_eq_principal_sets (B : Set I) :
    principalFilter B = (𝓟 B).sets := by
  ext A
  exact mem_principal.symm

/-- **Example 2.4(3).** The principal ultrafilter $`\mathcal F^i` is the principal filter
generated by the one-point set $`\{i\}`. -/
theorem principalUltrafilter_eq_principalFilter (i : I) :
    principalUltrafilter i = principalFilter {i} := by
  ext A
  change i ∈ A ↔ {i} ⊆ A
  exact singleton_subset_iff.symm

/-- **Example 2.4(4).** The union of a family of filters that is linearly ordered by inclusion
is a filter. The family must be nonempty (the empty union is the empty collection, which is not
a filter); the book leaves this implicit. -/
theorem isFilter_iUnion_of_chain {X : Type*} [Nonempty X] (𝓕 : X → Set (Set I))
    (h𝓕 : ∀ x, IsFilter (𝓕 x)) (hchain : ∀ x y, 𝓕 x ⊆ 𝓕 y ∨ 𝓕 y ⊆ 𝓕 x) :
    IsFilter (⋃ x, 𝓕 x) where
  nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨univ, mem_iUnion.mpr ⟨x, (h𝓕 x).univ_mem⟩⟩
  inter_mem := by
    intro A B hA hB
    obtain ⟨x, hx⟩ := mem_iUnion.mp hA
    obtain ⟨y, hy⟩ := mem_iUnion.mp hB
    rcases hchain x y with h | h
    · exact mem_iUnion.mpr ⟨y, (h𝓕 y).inter_mem (h hx) hy⟩
    · exact mem_iUnion.mpr ⟨x, (h𝓕 x).inter_mem hx (h hy)⟩
  superset_mem := by
    intro A B hA hAB
    obtain ⟨x, hx⟩ := mem_iUnion.mp hA
    exact mem_iUnion.mpr ⟨x, (h𝓕 x).superset_mem hx hAB⟩

/-- **Example 2.4(4), set form.** The union of a nonempty chain of filters, given as a set of
collections that is a chain for inclusion, is a filter. This is the form used with Zorn's
lemma. -/
theorem isFilter_sUnion_of_chain (c : Set (Set (Set I))) (hne : c.Nonempty)
    (hc : ∀ F ∈ c, IsFilter F) (hchain : IsChain (· ⊆ ·) c) : IsFilter (⋃₀ c) := by
  rw [sUnion_eq_iUnion]
  have : Nonempty c := hne.to_subtype
  exact isFilter_iUnion_of_chain (fun x : c => (x : Set (Set I))) (fun x => hc x.1 x.2)
    fun x y => hchain.total x.2 y.2

/-- **Example 2.4(4), proper form.** The union of a nonempty chain of proper filters is a proper
filter. -/
theorem isProperFilter_sUnion_of_chain (c : Set (Set (Set I))) (hne : c.Nonempty)
    (hc : ∀ F ∈ c, IsProperFilter F) (hchain : IsChain (· ⊆ ·) c) : IsProperFilter (⋃₀ c) where
  toIsFilter := isFilter_sUnion_of_chain c hne (fun F hF => (hc F hF).toIsFilter) hchain
  empty_notMem := by
    rintro ⟨F, hF, h⟩
    exact (hc F hF).empty_notMem h

/-!
## 2.5 Facts About Filters

The eight facts of this section are the working toolkit of the chapter. Facts (1) and (2)
repackage the axioms; (3), (4) and (5) say how an ultrafilter interacts with intersections,
unions, complements and finite sets, ending with the property on which the hyperreals rest: a
nonprincipal ultrafilter contains every cofinite set. Facts (7) and (8) introduce the finite
intersection property. Fact (6), that ultrafilters are exactly the maximal proper filters, is
proved in the book through Exercise 2.7(5), which uses the finite intersection property; so in
this file it comes last in the section, after (7) and (8), together with that exercise.
-/

/-- **Fact 2.5(1).** The intersection and superset axioms together are equivalent to the single
requirement that $`A \cap B \in \mathcal F` if and only if $`A \in \mathcal F` and
$`B \in \mathcal F`. -/
theorem filter_axioms_iff_inter_mem_iff (F : Set (Set I)) :
    ((∀ A B : Set I, A ∈ F → B ∈ F → A ∩ B ∈ F) ∧ (∀ A B : Set I, A ∈ F → A ⊆ B → B ∈ F)) ↔
      ∀ A B : Set I, A ∩ B ∈ F ↔ A ∈ F ∧ B ∈ F := by
  constructor
  · rintro ⟨hi, hs⟩ A B
    exact ⟨fun h => ⟨hs _ _ h inter_subset_left, hs _ _ h inter_subset_right⟩,
      fun h => hi A B h.1 h.2⟩
  · intro h
    refine ⟨fun A B hA hB => (h A B).mpr ⟨hA, hB⟩, fun A B hA hAB => ?_⟩
    have hAB' : A ∩ B = A := inter_eq_left.mpr hAB
    have hmem : A ∩ B ∈ F := by rw [hAB']; exact hA
    exact ((h A B).mp hmem).2

/-- **Fact 2.5(1), bundled.** A collection is a filter if and only if it is nonempty and
$`A \cap B \in \mathcal F \iff A \in \mathcal F \text{ and } B \in \mathcal F` for all
$`A, B`. -/
theorem isFilter_iff_inter_mem_iff :
    IsFilter F ↔ F.Nonempty ∧ ∀ A B : Set I, A ∩ B ∈ F ↔ A ∈ F ∧ B ∈ F := by
  rw [← filter_axioms_iff_inter_mem_iff]
  exact ⟨fun h => ⟨h.nonempty, fun _ _ => h.inter_mem, fun _ _ => h.superset_mem⟩,
    fun h => ⟨h.1, fun hA hB => h.2.1 _ _ hA hB, fun hA hAB => h.2.2 _ _ hA hAB⟩⟩

/-- **Fact 2.5(1), for a filter.** In a filter, $`A \cap B` is a member if and only if both
$`A` and $`B` are. -/
theorem IsFilter.inter_mem_iff (hF : IsFilter F) : A ∩ B ∈ F ↔ A ∈ F ∧ B ∈ F :=
  (isFilter_iff_inter_mem_iff.mp hF).2 A B

/-- **Fact 2.5(2).** A collection satisfying the superset axiom is nonempty if and only if it
contains $`I`. (Consequently $`\{I\} \subseteq \mathcal F` for every filter; see
{name}`Goldblatt.IsFilter.singleton_univ_subset`.) -/
theorem nonempty_iff_univ_mem_of_superset (hsup : ∀ A B : Set I, A ∈ F → A ⊆ B → B ∈ F) :
    F.Nonempty ↔ univ ∈ F :=
  ⟨fun ⟨A, hA⟩ => hsup A univ hA (subset_univ A), fun h => ⟨univ, h⟩⟩

/-- **Fact 2.5(3), intersections.** In an ultrafilter, $`A \cap B` is a member if and only if
both $`A` and $`B` are. -/
theorem IsUltrafilter.inter_mem_iff (hF : IsUltrafilter F) : A ∩ B ∈ F ↔ A ∈ F ∧ B ∈ F :=
  hF.toIsFilter.inter_mem_iff

/-- **Fact 2.5(3), complements.** In an ultrafilter, $`A^c` is a member if and only if $`A` is
not. -/
theorem IsUltrafilter.compl_mem_iff (hF : IsUltrafilter F) : Aᶜ ∈ F ↔ A ∉ F := by
  constructor
  · intro hAc hA
    have h := hF.inter_mem hA hAc
    rw [inter_compl_self] at h
    exact hF.empty_notMem h
  · intro hA
    exact (hF.mem_or_compl_mem A).resolve_left hA

/-- **Fact 2.5(3), unions.** In an ultrafilter, $`A \cup B` is a member if and only if $`A` is
or $`B` is. -/
theorem IsUltrafilter.union_mem_iff (hF : IsUltrafilter F) : A ∪ B ∈ F ↔ A ∈ F ∨ B ∈ F := by
  constructor
  · intro hAB
    by_contra hcon
    rw [not_or] at hcon
    have h := hF.inter_mem (hF.compl_mem_iff.mpr hcon.1) (hF.compl_mem_iff.mpr hcon.2)
    rw [← compl_union] at h
    exact hF.compl_mem_iff.mp h hAB
  · rintro (h | h)
    · exact hF.superset_mem h subset_union_left
    · exact hF.superset_mem h subset_union_right

/-- **Section 2.2 and Fact 2.5(3).** A set and its complement are never both large: no proper
filter contains both $`A` and $`A^c`. -/
theorem IsProperFilter.not_mem_and_compl_mem (hF : IsProperFilter F) (A : Set I) :
    ¬ (A ∈ F ∧ Aᶜ ∈ F) := by
  rintro ⟨hA, hAc⟩
  have h := hF.inter_mem hA hAc
  rw [inter_compl_self] at h
  exact hF.empty_notMem h

/-- **Sections 2.2 and 2.3, characterisation of ultrafilters.** A filter is an ultrafilter if
and only if the complement of a set is a member precisely when the set is not. -/
theorem IsFilter.isUltrafilter_iff_compl_mem_iff (hF : IsFilter F) :
    IsUltrafilter F ↔ ∀ A : Set I, Aᶜ ∈ F ↔ A ∉ F := by
  constructor
  · intro h A
    exact h.compl_mem_iff
  · intro h
    refine ⟨⟨hF, fun he => ?_⟩, fun A => ?_⟩
    · have hu : (∅ : Set I)ᶜ ∈ F := by rw [compl_empty]; exact hF.univ_mem
      exact (h ∅).mp hu he
    · by_cases hA : A ∈ F
      · exact Or.inl hA
      · exact Or.inr ((h A).mpr hA)

/-- **Sections 2.2 and 2.3, characterisation of ultrafilters.** A filter is an ultrafilter if
and only if, for every $`A \subseteq I`, exactly one of $`A` and $`A^c` is a member. This is the
form in which the requirement on "large" sets is reached in Section 2.2. -/
theorem IsFilter.isUltrafilter_iff_xor (hF : IsFilter F) :
    IsUltrafilter F ↔ ∀ A : Set I, Xor (A ∈ F) (Aᶜ ∈ F) := by
  rw [hF.isUltrafilter_iff_compl_mem_iff]
  refine forall_congr' fun A => ?_
  rw [xor_def]
  tauto

/-- **Fact 2.5(4), existence.** If an ultrafilter contains a finite union
$`A_1 \cup \dots \cup A_n`, it contains one of the $`A_i`. (No disjointness is needed for
this half.) -/
theorem IsUltrafilter.exists_mem_of_biUnion_mem {ι : Type*} (hF : IsUltrafilter F)
    (s : Finset ι) (A : ι → Set I) (hU : (⋃ i ∈ s, A i) ∈ F) : ∃ i ∈ s, A i ∈ F := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty] at hU
    exact absurd hU hF.empty_notMem
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert, hF.union_mem_iff] at hU
    rcases hU with h | h
    · exact ⟨a, Finset.mem_insert_self a s, h⟩
    · obtain ⟨i, hi, hiF⟩ := ih h
      exact ⟨i, Finset.mem_insert_of_mem hi, hiF⟩

/-- **Fact 2.5(4).** Let $`\mathcal F` be an ultrafilter and $`A_1, \dots, A_n` finitely many
pairwise disjoint sets whose union belongs to $`\mathcal F`. Then $`A_i \in \mathcal F` for
exactly one index $`i`. The finite family is given as a function on a finite set of indices. -/
theorem IsUltrafilter.existsUnique_mem_of_biUnion_mem {ι : Type*} (hF : IsUltrafilter F)
    (s : Finset ι) (A : ι → Set I) (hdisj : (↑s : Set ι).PairwiseDisjoint A)
    (hU : (⋃ i ∈ s, A i) ∈ F) : ∃! i, i ∈ s ∧ A i ∈ F := by
  obtain ⟨i, hi, hiF⟩ := hF.exists_mem_of_biUnion_mem s A hU
  refine ⟨i, ⟨hi, hiF⟩, ?_⟩
  rintro j ⟨hj, hjF⟩
  by_contra hne
  have hd : Disjoint (A j) (A i) := hdisj (Finset.mem_coe.mpr hj) (Finset.mem_coe.mpr hi) hne
  have h := hF.inter_mem hjF hiF
  rw [hd.inter_eq] at h
  exact hF.empty_notMem h

/-- **Fact 2.5(5), first step.** If an ultrafilter contains a finite set $`A`, then it contains
a one-element set $`\{i\}` with $`i \in A`. -/
theorem IsUltrafilter.exists_singleton_mem_of_finite_mem (hF : IsUltrafilter F) (hA : A ∈ F)
    (hfin : A.Finite) : ∃ i ∈ A, ({i} : Set I) ∈ F := by
  have hU : (⋃ i ∈ hfin.toFinset, ({i} : Set I)) = A := by
    ext x
    simp
  obtain ⟨i, hi, hiF⟩ :=
    hF.exists_mem_of_biUnion_mem hfin.toFinset (fun i => ({i} : Set I)) (by rw [hU]; exact hA)
  exact ⟨i, hfin.mem_toFinset.mp hi, hiF⟩

/-- **Fact 2.5(5), second step.** An ultrafilter containing the one-element set $`\{i\}` is the
principal ultrafilter $`\mathcal F^i`. -/
theorem IsUltrafilter.eq_principalUltrafilter_of_singleton_mem (hF : IsUltrafilter F) {i : I}
    (hi : ({i} : Set I) ∈ F) : F = principalUltrafilter i := by
  ext A
  constructor
  · intro hA
    change i ∈ A
    by_contra hiA
    have h := hF.inter_mem hA hi
    rw [inter_singleton_eq_empty.mpr hiA] at h
    exact hF.empty_notMem h
  · intro hiA
    exact hF.superset_mem hi (singleton_subset_iff.mpr hiA)

/-- **Fact 2.5(5).** An ultrafilter that contains a finite set is principal. -/
theorem IsUltrafilter.isPrincipal_of_finite_mem (hF : IsUltrafilter F) (hA : A ∈ F)
    (hfin : A.Finite) : IsPrincipal F := by
  obtain ⟨i, -, hi⟩ := hF.exists_singleton_mem_of_finite_mem hA hfin
  exact ⟨i, hF.eq_principalUltrafilter_of_singleton_mem hi⟩

/-- **Fact 2.5(5), the critical property.** A nonprincipal ultrafilter contains every cofinite
set. This is what later makes sequences tending to zero infinitesimal and sequences tending to
infinity unlimited. -/
theorem IsUltrafilter.cofiniteFilter_subset (hF : IsUltrafilter F) (hnp : ¬ IsPrincipal F) :
    cofiniteFilter I ⊆ F := by
  intro A hA
  rcases hF.mem_or_compl_mem A with h | h
  · exact h
  · exact absurd (hF.isPrincipal_of_finite_mem h hA) hnp

/-- **Fact 2.5(5), converse.** A principal ultrafilter omits a cofinite set, namely the
complement of its generating point. Hence an ultrafilter is nonprincipal if and only if it
contains all cofinite sets. -/
theorem IsUltrafilter.not_isPrincipal_iff_cofiniteFilter_subset (hF : IsUltrafilter F) :
    ¬ IsPrincipal F ↔ cofiniteFilter I ⊆ F := by
  refine ⟨hF.cofiniteFilter_subset, ?_⟩
  rintro hsub ⟨i, rfl⟩
  have h : ({i} : Set I)ᶜ ∈ principalUltrafilter i :=
    hsub (by rw [mem_cofiniteFilter, compl_compl]; exact finite_singleton i)
  exact h rfl

/-- **Fact 2.5(5), restated.** A nonprincipal ultrafilter contains no finite set. -/
theorem IsUltrafilter.not_finite_of_mem (hF : IsUltrafilter F) (hnp : ¬ IsPrincipal F)
    (hA : A ∈ F) : A.Infinite :=
  fun hfin => hnp (hF.isPrincipal_of_finite_mem hA hfin)

/-- **Example 2.4(1), second claim; Exercise 2.7(3).** On a finite index set every ultrafilter
is principal: the whole (finite) index set is a member, so Fact 2.5(5) applies. -/
theorem IsUltrafilter.isPrincipal_of_finite [Finite I] (hF : IsUltrafilter F) : IsPrincipal F :=
  hF.isPrincipal_of_finite_mem hF.univ_mem finite_univ

/-- **Fact 2.5(7), finite intersection property.** A collection $`\mathcal H` has the finite
intersection property (fip) when every nonempty finite subcollection has nonempty
intersection. -/
def HasFIP (H : Set (Set I)) : Prop :=
  ∀ s : Finset (Set I), s.Nonempty → (↑s : Set (Set I)) ⊆ H →
    (⋂₀ (↑s : Set (Set I))).Nonempty

/-- **Fact 2.5(7).** Failure of the finite intersection property is witnessed by a nonempty
finite subcollection with empty intersection. -/
theorem not_hasFIP_iff :
    ¬ HasFIP H ↔ ∃ s : Finset (Set I), s.Nonempty ∧ (↑s : Set (Set I)) ⊆ H ∧
      ⋂₀ (↑s : Set (Set I)) = ∅ := by
  simp only [HasFIP, not_forall, not_nonempty_iff_eq_empty, exists_prop]

/-- **Fact 2.5(7).** The finite intersection property passes to subcollections. -/
theorem HasFIP.mono {H K : Set (Set I)} (hK : HasFIP K) (h : H ⊆ K) : HasFIP H :=
  fun s hne hs => hK s hne (hs.trans h)

/-- **Fact 2.5(7).** The filter $`\mathcal F^{\mathcal H}` generated by $`\mathcal H` omits the
empty set if and only if $`\mathcal H` has the finite intersection property. The index set must
be nonempty, as it is throughout the book: on an empty index set the empty collection has the
fip vacuously but generates the improper filter. -/
theorem empty_notMem_generatedFilter_iff [Nonempty I] (H : Set (Set I)) :
    ∅ ∉ generatedFilter H ↔ HasFIP H := by
  constructor
  · intro h s _ hs
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    exact h ⟨s, hs, hne.subset⟩
  · rintro h ⟨s, hs, hsub⟩
    rcases s.eq_empty_or_nonempty with rfl | hne
    · obtain ⟨x⟩ := ‹Nonempty I›
      exact hsub (by simp : x ∈ ⋂₀ (↑(∅ : Finset (Set I)) : Set (Set I)))
    · obtain ⟨x, hx⟩ := h s hne hs
      exact hsub hx

/-- **Fact 2.5(7).** The filter generated by $`\mathcal H` is proper if and only if
$`\mathcal H` has the finite intersection property. -/
theorem isProperFilter_generatedFilter_iff [Nonempty I] (H : Set (Set I)) :
    IsProperFilter (generatedFilter H) ↔ HasFIP H :=
  ⟨fun h => (empty_notMem_generatedFilter_iff H).mp h.empty_notMem,
    fun h => ⟨isFilter_generatedFilter H, (empty_notMem_generatedFilter_iff H).mpr h⟩⟩

/-- **Fact 2.5(7), consequence.** Every proper filter has the finite intersection property. -/
theorem IsProperFilter.hasFIP (hF : IsProperFilter F) : HasFIP F :=
  fun s _ hs => hF.nonempty_of_mem (hF.sInter_mem s hs)

/-- **Fact 2.5(7), consequence.** On a nonempty index set, a collection has the finite
intersection property if and only if it is included in some proper filter. -/
theorem hasFIP_iff_exists_isProperFilter [Nonempty I] :
    HasFIP H ↔ ∃ F, IsProperFilter F ∧ H ⊆ F :=
  ⟨fun h => ⟨generatedFilter H, (isProperFilter_generatedFilter_iff H).mpr h,
    subset_generatedFilter H⟩, fun ⟨_, hF, hHF⟩ => hF.hasFIP.mono hHF⟩

/-- **Fact 2.5(8), auxiliary** (also used for Exercise 2.7(5)(i)). A point of $`A` lying in every member of $`s` other than $`A` lies in every
member of $`s`. -/
private theorem mem_sInter_of_mem_sInter_erase [DecidableEq (Set I)] {s : Finset (Set I)}
    {x : I} (hx : x ∈ ⋂₀ (↑(s.erase A) : Set (Set I))) (hxA : x ∈ A) :
    x ∈ ⋂₀ (↑s : Set (Set I)) := by
  rw [mem_sInter] at hx ⊢
  intro C hC
  by_cases hCA : C = A
  · rw [hCA]
    exact hxA
  · exact hx C (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hCA, Finset.mem_coe.mp hC⟩))

/-- **Fact 2.5(8), auxiliary** (also used for Exercise 2.7(5)(i)). Removing $`A` from a finite subcollection of $`\mathcal H \cup \{A\}` leaves a
subcollection of $`\mathcal H`. -/
private theorem coe_erase_subset_of_subset_insert [DecidableEq (Set I)] {s : Finset (Set I)}
    (hs : (↑s : Set (Set I)) ⊆ insert A H) : (↑(s.erase A) : Set (Set I)) ⊆ H := by
  intro C hC
  rw [Finset.mem_coe, Finset.mem_erase] at hC
  exact (mem_insert_iff.mp (hs (Finset.mem_coe.mpr hC.2))).resolve_left hC.1

/-- **Fact 2.5(8).** If $`\mathcal H` has the finite intersection property then, for any
$`A \subseteq I`, at least one of $`\mathcal H \cup \{A\}` and $`\mathcal H \cup \{A^c\}` has
it too. The index set must be nonempty, as it is throughout the book (on an empty index set the
empty collection is a counterexample). -/
theorem HasFIP.insert_or_insert_compl [Nonempty I] (hH : HasFIP H) (A : Set I) :
    HasFIP (insert A H) ∨ HasFIP (insert Aᶜ H) := by
  classical
  by_contra hcon
  rw [not_or, not_hasFIP_iff, not_hasFIP_iff] at hcon
  obtain ⟨⟨s, -, hs, hs0⟩, ⟨t, -, ht, ht0⟩⟩ := hcon
  have key : ∀ x, x ∉ ⋂₀ (↑(s.erase A ∪ t.erase Aᶜ) : Set (Set I)) := by
    intro x hx
    rw [Finset.coe_union, sInter_union] at hx
    by_cases hxA : x ∈ A
    · have h := mem_sInter_of_mem_sInter_erase hx.1 hxA
      rw [hs0] at h
      exact h
    · have h := mem_sInter_of_mem_sInter_erase hx.2 (mem_compl hxA)
      rw [ht0] at h
      exact h
  have hsub : (↑(s.erase A ∪ t.erase Aᶜ) : Set (Set I)) ⊆ H := by
    rw [Finset.coe_union]
    exact union_subset (coe_erase_subset_of_subset_insert hs)
      (coe_erase_subset_of_subset_insert ht)
  rcases (s.erase A ∪ t.erase Aᶜ).eq_empty_or_nonempty with he | hne
  · obtain ⟨x⟩ := ‹Nonempty I›
    exact key x (by rw [he]; simp)
  · obtain ⟨x, hx⟩ := hH _ hne hsub
    exact key x hx

/-- **Exercise 2.7(5)(i).** For a proper filter $`\mathcal F` and a set $`A`, the collection
$`\mathcal F \cup \{A^c\}` has the finite intersection property if and only if
$`A \notin \mathcal F`. -/
theorem IsProperFilter.hasFIP_insert_compl_iff (hF : IsProperFilter F) (A : Set I) :
    HasFIP (insert Aᶜ F) ↔ A ∉ F := by
  classical
  constructor
  · intro h hA
    have hs : (↑({A, Aᶜ} : Finset (Set I)) : Set (Set I)) ⊆ insert Aᶜ F := by
      intro C hC
      rw [Finset.coe_insert, Finset.coe_singleton] at hC
      rcases hC with rfl | hC
      · exact mem_insert_of_mem _ hA
      · exact mem_insert_iff.mpr (Or.inl hC)
    obtain ⟨x, hx⟩ := h {A, Aᶜ} (Finset.insert_nonempty _ _) hs
    rw [Finset.coe_insert, Finset.coe_singleton, sInter_insert, sInter_singleton] at hx
    exact hx.2 hx.1
  · intro hA s _ hs
    have hmem : ⋂₀ (↑(s.erase Aᶜ) : Set (Set I)) ∈ F :=
      hF.sInter_mem _ (coe_erase_subset_of_subset_insert hs)
    have hnot : ¬ ⋂₀ (↑(s.erase Aᶜ) : Set (Set I)) ⊆ A := fun h => hA (hF.superset_mem hmem h)
    obtain ⟨x, hx, hxA⟩ := not_subset.mp hnot
    exact ⟨x, mem_sInter_of_mem_sInter_erase hx (mem_compl hxA)⟩

/-- **Fact 2.5(6), Exercise 2.7(5)(ii).** A collection is an ultrafilter if and only if it is a
maximal proper filter: a proper filter that is not strictly included in any proper filter. For
the nontrivial direction, if $`A \notin \mathcal F` then by part (i) of the exercise
$`\mathcal F \cup \{A^c\}` has the fip, so it generates a proper filter extending
$`\mathcal F`, which by maximality is $`\mathcal F` itself; hence $`A^c \in \mathcal F`. -/
theorem isUltrafilter_iff_maximal :
    IsUltrafilter F ↔ IsProperFilter F ∧ ∀ G, IsProperFilter G → F ⊆ G → G = F := by
  constructor
  · intro hF
    refine ⟨hF.toIsProperFilter, fun G hG hFG => Subset.antisymm (fun A hA => ?_) hFG⟩
    by_contra hAF
    exact hG.not_mem_and_compl_mem A ⟨hA, hFG (hF.compl_mem_iff.mpr hAF)⟩
  · rintro ⟨hF, hmax⟩
    refine ⟨hF, fun A => ?_⟩
    by_cases hA : A ∈ F
    · exact Or.inl hA
    · right
      have : Nonempty I := hF.nonempty_index
      have hfip : HasFIP (insert Aᶜ F) := (hF.hasFIP_insert_compl_iff A).mpr hA
      have hG : IsProperFilter (generatedFilter (insert Aᶜ F)) :=
        (isProperFilter_generatedFilter_iff _).mpr hfip
      have hFG : F ⊆ generatedFilter (insert Aᶜ F) :=
        (subset_insert _ _).trans (subset_generatedFilter _)
      rw [← hmax _ hG hFG]
      exact subset_generatedFilter _ (mem_insert _ _)

/-- **Fact 2.5(6), order-theoretic form.** The ultrafilters are exactly the maximal elements,
for inclusion, among proper filters, stated with Mathlib's {name}`Maximal`. -/
theorem isUltrafilter_iff_maximal_isProperFilter : IsUltrafilter F ↔ Maximal IsProperFilter F := by
  rw [isUltrafilter_iff_maximal]
  exact ⟨fun h => ⟨h.1, fun G hG hFG => (h.2 G hG hFG).le⟩,
    fun h => ⟨h.1, fun G hG hFG => Subset.antisymm (h.2 hG hFG) hFG⟩⟩

/-!
## 2.6 Zorn's Lemma

One could try to build an ultrafilter greedily: enumerate the subsets of $`I` and decide each
in turn, with Fact 2.5(8) guaranteeing that the finite intersection property survives every
decision. Such an enumeration needs a well-ordering of the power set and a transfinite
recursion along it; Zorn's lemma, an equivalent of the axiom of choice, packages that recursion
once and for all. The book sketches
how Zorn's lemma follows from the axiom of choice and then uses it as a black box; we likewise
take it from Mathlib, where it is proved from {name}`Classical.choice`.

The application is the ultrafilter theorem (Theorem 2.6.1): a collection with the fip extends
to an ultrafilter. The proof below is the book's: the proper filters including the given
collection are closed under unions of chains by Example 2.4(4), so Zorn's lemma yields a maximal
one, which is an ultrafilter by Fact 2.5(6). Its corollary, the existence of nonprincipal
ultrafilters on every infinite set, is the foundation of the ultrapower construction.
-/

/-- **Section 2.6, Zorn's lemma.** If every chain in a partially ordered set $`P` has an upper
bound in $`P`, then $`P` has a maximal element: an element $`m` such that no $`q` satisfies
$`m \le q` and $`q \ne m`. This is Mathlib's {name}`zorn_le` restated in the book's wording. -/
theorem zorn_lemma {P : Type*} [PartialOrder P]
    (h : ∀ c : Set P, IsChain (· ≤ ·) c → ∃ ub : P, ∀ p ∈ c, p ≤ ub) :
    ∃ m : P, ∀ q : P, m ≤ q → q = m := by
  obtain ⟨m, hm⟩ := zorn_le (α := P) fun c hc => h c hc
  exact ⟨m, fun q hq => le_antisymm (hm hq) hq⟩

/-- **Theorem 2.6.1 (ultrafilter theorem), with maximality data.** Any proper filter on $`I`
is included in an ultrafilter. This is the Zorn's lemma step of the book's proof. -/
theorem IsProperFilter.exists_isUltrafilter_superset (hF : IsProperFilter F) :
    ∃ U, IsUltrafilter U ∧ F ⊆ U := by
  obtain ⟨M, hFM, hmax⟩ :=
    zorn_subset_nonempty {G : Set (Set I) | IsProperFilter G ∧ F ⊆ G}
      (fun c hcS hchain hne =>
        ⟨⋃₀ c, ⟨isProperFilter_sUnion_of_chain c hne (fun G hG => (hcS hG).1) hchain,
          let ⟨G, hG⟩ := hne
          (hcS hG).2.trans (subset_sUnion_of_mem hG)⟩,
          fun G hG => subset_sUnion_of_mem hG⟩)
      F ⟨hF, Subset.rfl⟩
  refine ⟨M, isUltrafilter_iff_maximal.mpr ⟨hmax.prop.1, fun G hG hMG => ?_⟩, hFM⟩
  exact Subset.antisymm (hmax.2 ⟨hG, hmax.prop.2.trans hMG⟩ hMG) hMG

/-- **Theorem 2.6.1 (ultrafilter theorem).** Any collection of subsets of a nonempty set $`I`
that has the finite intersection property can be extended to an ultrafilter on $`I`. -/
theorem HasFIP.exists_isUltrafilter_superset [Nonempty I] (hH : HasFIP H) :
    ∃ U, IsUltrafilter U ∧ H ⊆ U := by
  obtain ⟨U, hU, hHU⟩ :=
    ((isProperFilter_generatedFilter_iff H).mpr hH).exists_isUltrafilter_superset
  exact ⟨U, hU, (subset_generatedFilter H).trans hHU⟩

/-- **Theorem 2.6.1, converse.** A collection included in an ultrafilter has the finite
intersection property, so on a nonempty index set the fip characterises the collections that
extend to ultrafilters. -/
theorem hasFIP_iff_exists_isUltrafilter [Nonempty I] :
    HasFIP H ↔ ∃ U, IsUltrafilter U ∧ H ⊆ U :=
  ⟨HasFIP.exists_isUltrafilter_superset,
    fun ⟨_, hU, hHU⟩ => hU.toIsProperFilter.hasFIP.mono hHU⟩

/-- **Corollary 2.6.2, preliminary.** On an infinite set the cofinite filter has the finite
intersection property. -/
theorem hasFIP_cofiniteFilter (I : Type*) [Infinite I] : HasFIP (cofiniteFilter I) :=
  (isProperFilter_cofiniteFilter_iff.mpr ‹Infinite I›).hasFIP

/-- **Corollary 2.6.2.** Every infinite set carries a nonprincipal ultrafilter: extend the
cofinite filter to an ultrafilter; it contains the complement of every one-point set, so it is
not principal. -/
theorem exists_isUltrafilter_not_isPrincipal (I : Type*) [Infinite I] :
    ∃ F : Set (Set I), IsUltrafilter F ∧ ¬ IsPrincipal F := by
  obtain ⟨F, hF, hsub⟩ := (hasFIP_cofiniteFilter I).exists_isUltrafilter_superset
  exact ⟨F, hF, hF.not_isPrincipal_iff_cofiniteFilter_subset.mpr hsub⟩

/-- **Corollary 2.6.2 and Exercise 2.7(3), combined.** A set carries a nonprincipal ultrafilter
if and only if it is infinite. -/
theorem exists_isUltrafilter_not_isPrincipal_iff (I : Type*) :
    (∃ F : Set (Set I), IsUltrafilter F ∧ ¬ IsPrincipal F) ↔ Infinite I := by
  constructor
  · rintro ⟨F, hF, hnp⟩
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    exact hnp hF.isPrincipal_of_finite
  · intro h
    exact exists_isUltrafilter_not_isPrincipal I

/-- **Corollary 2.6.2, in Mathlib's vocabulary.** On an infinite type there is a term of
{name}`Ultrafilter` different from every principal ultrafilter {lit}`pure i`. -/
theorem exists_ultrafilter_ne_pure (I : Type*) [Infinite I] :
    ∃ U : Ultrafilter I, ∀ i : I, U ≠ pure i := by
  obtain ⟨F, hF, hnp⟩ := exists_isUltrafilter_not_isPrincipal I
  refine ⟨hF.toUltrafilter, fun i h => hnp ⟨i, ?_⟩⟩
  ext A
  rw [← hF.mem_toUltrafilter, h]
  rfl

/-- **Section 2.6, closing remark, in Mathlib's vocabulary.** The book notes without proof that
an infinite set $`I` carries as many nonprincipal ultrafilters as there are members of
$`\mathcal P(\mathcal P(I))`. This form counts terms of Mathlib's bundled {name}`Ultrafilter`
other than the {lit}`pure i`, and writes the answer as a cardinal power; the statement about
the chapter's own objects is {lit}`mk_isUltrafilter_not_isPrincipal`. It is derived from Mathlib's count
{name}`Cardinal.mk_ultrafilter_of_infinite` of all ultrafilters: removing the principal ones,
of which there are only as many as points of $`I`, does not change the cardinality
$`2^{2^{|I|}}`. -/
theorem mk_nonprincipal_ultrafilter (I : Type*) [Infinite I] :
    Cardinal.mk {U : Ultrafilter I // ∀ i : I, U ≠ pure i} =
      2 ^ (2 ^ Cardinal.mk I : Cardinal) := by
  have hrange : Cardinal.mk (range (pure : I → Ultrafilter I)) < Cardinal.mk (Ultrafilter I) := by
    rw [Cardinal.mk_ultrafilter_of_infinite]
    exact Cardinal.mk_range_le.trans_lt
      ((Cardinal.cantor _).trans (Cardinal.cantor _))
  have : Infinite (Ultrafilter I) := Infinite.of_injective pure Ultrafilter.pure_injective
  rw [← Cardinal.mk_ultrafilter_of_infinite, ← Cardinal.mk_compl_of_infinite _ hrange]
  refine Cardinal.mk_congr (Equiv.subtypeEquivRight fun U => ?_)
  simp only [mem_compl_iff, mem_range, not_exists]
  exact forall_congr' fun i => ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩

/-- **Section 2.6, closing remark.** On an infinite set $`I`, the collection of nonprincipal
ultrafilters (in the sense of this chapter: collections of subsets satisfying
{name}`Goldblatt.IsUltrafilter` and not {name}`Goldblatt.IsPrincipal`) has the same cardinality
as $`\mathcal P(\mathcal P(I))`. The book states this without proof; here it is transported
from {name}`Goldblatt.mk_nonprincipal_ultrafilter` along {name}`Goldblatt.ultrafilterEquiv`. -/
theorem mk_isUltrafilter_not_isPrincipal (I : Type*) [Infinite I] :
    Cardinal.mk {F : Set (Set I) // IsUltrafilter F ∧ ¬ IsPrincipal F} =
      Cardinal.mk (Set (Set I)) := by
  rw [Cardinal.mk_set, Cardinal.mk_set, ← mk_nonprincipal_ultrafilter I]
  refine Cardinal.mk_congr ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans
    ((ultrafilterEquiv I).subtypeEquiv fun F => ?_))
  rw [← not_exists, ← isPrincipal_sets_iff]
  rfl

/-- **Section 2.6, closing remark.** The same count as a bijection: on an infinite set $`I` the
nonprincipal ultrafilters are in one-to-one correspondence with the members of
$`\mathcal P(\mathcal P(I))`. -/
theorem nonempty_equiv_isUltrafilter_not_isPrincipal (I : Type*) [Infinite I] :
    Nonempty ({F : Set (Set I) // IsUltrafilter F ∧ ¬ IsPrincipal F} ≃ Set (Set I)) :=
  Cardinal.eq.mp (mk_isUltrafilter_not_isPrincipal I)

/-!
## 2.7 Exercises on Filters

Exercises (3), (4) and (5) have already been proved above, because the main line of the chapter
depends on them: (3) is {name}`Goldblatt.IsUltrafilter.isPrincipal_of_finite`, (4) is
{name}`Goldblatt.isFilter_generatedFilter`, {name}`Goldblatt.subset_generatedFilter` and
{name}`Goldblatt.generatedFilter_subset`, and (5) is
{name}`Goldblatt.IsProperFilter.hasFIP_insert_compl_iff` and
{name}`Goldblatt.isUltrafilter_iff_maximal`. The remaining two are existence statements.
-/

/-- **Exercise 2.7(1).** Every nonempty subset $`A` of $`I` belongs to some ultrafilter on
$`I`. The principal ultrafilter at a point of $`A` will do; the same follows from the
ultrafilter theorem applied to the one-member collection $`\{A\}`. -/
theorem exists_isUltrafilter_mem (hA : A.Nonempty) : ∃ F, IsUltrafilter F ∧ A ∈ F := by
  obtain ⟨i, hi⟩ := hA
  exact ⟨principalUltrafilter i, isUltrafilter_principalUltrafilter i, hi⟩

/-- **Exercise 2.7(1), converse.** A set belonging to an ultrafilter is nonempty. -/
theorem exists_isUltrafilter_mem_iff : (∃ F, IsUltrafilter F ∧ A ∈ F) ↔ A.Nonempty :=
  ⟨fun ⟨_, hF, hA⟩ => hF.toIsProperFilter.nonempty_of_mem hA, exists_isUltrafilter_mem⟩

/-- **Exercise 2.7(2), general form.** Every infinite subset $`A` of $`I` belongs to some
nonprincipal ultrafilter on $`I`: by Exercise 2.7(5)(i) the cofinite filter together with $`A`
has the fip (the complement of $`A` is not cofinite), and an ultrafilter extending that
collection contains all cofinite sets, so it is nonprincipal. -/
theorem exists_isUltrafilter_not_isPrincipal_mem (hA : A.Infinite) :
    ∃ F, IsUltrafilter F ∧ ¬ IsPrincipal F ∧ A ∈ F := by
  have : Infinite I := by
    have := hA.to_subtype
    exact Infinite.of_injective (Subtype.val : A → I) Subtype.val_injective
  have hfip : HasFIP (insert Aᶜᶜ (cofiniteFilter I)) :=
    ((isProperFilter_cofiniteFilter_iff.mpr ‹Infinite I›).hasFIP_insert_compl_iff Aᶜ).mpr
      (by rw [mem_cofiniteFilter, compl_compl]; exact hA)
  rw [compl_compl] at hfip
  obtain ⟨F, hF, hsub⟩ := hfip.exists_isUltrafilter_superset
  exact ⟨F, hF, hF.not_isPrincipal_iff_cofiniteFilter_subset.mpr ((subset_insert _ _).trans hsub),
    hsub (mem_insert _ _)⟩

/-- **Exercise 2.7(2), converse of the general form.** A set belongs to some nonprincipal
ultrafilter if and only if it is infinite. -/
theorem exists_isUltrafilter_not_isPrincipal_mem_iff :
    (∃ F, IsUltrafilter F ∧ ¬ IsPrincipal F ∧ A ∈ F) ↔ A.Infinite :=
  ⟨fun ⟨_, hF, hnp, hA⟩ => hF.not_finite_of_mem hnp hA, exists_isUltrafilter_not_isPrincipal_mem⟩

/-- **Exercise 2.7(2), first half.** There is a nonprincipal ultrafilter on $`\mathbb N`
containing the set of even numbers. -/
theorem exists_isUltrafilter_not_isPrincipal_even :
    ∃ F : Set (Set ℕ), IsUltrafilter F ∧ ¬ IsPrincipal F ∧ {n | Even n} ∈ F :=
  exists_isUltrafilter_not_isPrincipal_mem infinite_setOf_even

/-- **Exercise 2.7(2), second half.** There is a nonprincipal ultrafilter on $`\mathbb N`
containing the set of odd numbers. -/
theorem exists_isUltrafilter_not_isPrincipal_odd :
    ∃ F : Set (Set ℕ), IsUltrafilter F ∧ ¬ IsPrincipal F ∧ {n | Odd n} ∈ F :=
  exists_isUltrafilter_not_isPrincipal_mem infinite_setOf_odd

/-- **Exercise 2.7(2), answering the question of Section 2.2.** The two ultrafilters of the
exercise are necessarily different, since no ultrafilter contains both the evens and the odds.
So "which of the evens and the odds is large" has no canonical answer: both choices occur. -/
theorem exists_isUltrafilter_even_ne_odd :
    ∃ F G : Set (Set ℕ), (IsUltrafilter F ∧ ¬ IsPrincipal F ∧ {n | Even n} ∈ F) ∧
      (IsUltrafilter G ∧ ¬ IsPrincipal G ∧ {n | Odd n} ∈ G) ∧ F ≠ G := by
  obtain ⟨F, hF, hFnp, hFe⟩ := exists_isUltrafilter_not_isPrincipal_even
  obtain ⟨G, hG, hGnp, hGo⟩ := exists_isUltrafilter_not_isPrincipal_odd
  refine ⟨F, G, ⟨hF, hFnp, hFe⟩, ⟨hG, hGnp, hGo⟩, ?_⟩
  rintro rfl
  rw [← compl_setOf_even] at hGo
  exact hF.toIsProperFilter.not_mem_and_compl_mem _ ⟨hFe, hGo⟩

/-!
## The index ultrafilter of this project

Chapter 3 needs one nonprincipal ultrafilter on the natural numbers, fixed once and for all.
The book picks an arbitrary one, supplied by Corollary 2.6.2. This project uses Mathlib's
choice, {name}`Filter.hyperfilter`: an ultrafilter extending the cofinite filter, available on
any infinite type. Mathlib's {name}`Hyperreal` is by definition the ultrapower of the reals
over the hyperfilter on the natural numbers.

The lemmas below record, under stable names and for an arbitrary infinite index type, that the
hyperfilter is a nonprincipal ultrafilter in the book's sense and has the closure properties of
Section 2.5. For subsets of the natural numbers they are followed by the forms most used later:
a property holding from some index on holds on a large set.
-/

section Hyperfilter

variable {J : Type*} [Infinite J] {S T : Set J}

/-- **Index ultrafilter.** The members of the hyperfilter form an ultrafilter in the book's
sense. -/
theorem isUltrafilter_hyperfilter (J : Type*) [Infinite J] :
    IsUltrafilter (hyperfilter J : Filter J).sets :=
  isUltrafilter_sets _

/-- **Index ultrafilter.** The hyperfilter is different from every principal ultrafilter. -/
theorem hyperfilter_ne_pure (j : J) : hyperfilter J ≠ pure j := by
  intro h
  have hmem : ({j} : Set J) ∈ hyperfilter J := by
    rw [h]
    exact mem_singleton j
  exact (finite_singleton j).notMem_hyperfilter hmem

/-- **Index ultrafilter.** The hyperfilter is nonprincipal in the book's sense. -/
theorem not_isPrincipal_hyperfilter (J : Type*) [Infinite J] :
    ¬ IsPrincipal (hyperfilter J : Filter J).sets := by
  rw [isPrincipal_sets_iff]
  rintro ⟨j, hj⟩
  exact hyperfilter_ne_pure j hj

/-- **Index ultrafilter, Fact 2.5(5).** The hyperfilter contains every cofinite set. -/
theorem cofiniteFilter_subset_hyperfilter (J : Type*) [Infinite J] :
    cofiniteFilter J ⊆ (hyperfilter J : Filter J).sets :=
  fun _ hS => mem_hyperfilter_of_finite_compl hS

/-- **Index ultrafilter, Fact 2.5(5).** A set with finite complement is large. -/
theorem mem_hyperfilter_of_compl_finite (hS : Sᶜ.Finite) : S ∈ hyperfilter J :=
  mem_hyperfilter_of_finite_compl hS

/-- **Index ultrafilter, Fact 2.5(5).** A finite set is not large. -/
theorem notMem_hyperfilter_of_finite (hS : S.Finite) : S ∉ hyperfilter J :=
  hS.notMem_hyperfilter

/-- **Index ultrafilter, Fact 2.5(5).** Every large set is infinite. -/
theorem infinite_of_mem_hyperfilter (hS : S ∈ hyperfilter J) : S.Infinite :=
  fun hfin => hfin.notMem_hyperfilter hS

/-- **Index ultrafilter.** No one-point set is large. -/
theorem singleton_notMem_hyperfilter (j : J) : ({j} : Set J) ∉ hyperfilter J :=
  (finite_singleton j).notMem_hyperfilter

/-- **Index ultrafilter.** The whole index set is large. -/
theorem univ_mem_hyperfilter (J : Type*) [Infinite J] : (univ : Set J) ∈ hyperfilter J :=
  Filter.univ_mem

/-- **Index ultrafilter.** The empty set is not large. -/
theorem empty_notMem_hyperfilter (J : Type*) [Infinite J] : (∅ : Set J) ∉ hyperfilter J :=
  (hyperfilter J).empty_notMem

/-- **Index ultrafilter.** Supersets of large sets are large. -/
theorem mem_hyperfilter_of_superset (hS : S ∈ hyperfilter J) (hST : S ⊆ T) :
    T ∈ hyperfilter J :=
  Filter.mem_of_superset hS hST

/-- **Index ultrafilter, Fact 2.5(3).** An intersection is large if and only if both sets
are. -/
theorem inter_mem_hyperfilter_iff : S ∩ T ∈ hyperfilter J ↔ S ∈ hyperfilter J ∧ T ∈ hyperfilter J :=
  Filter.inter_mem_iff

/-- **Index ultrafilter, Fact 2.5(3).** A union is large if and only if one of the sets is. -/
theorem union_mem_hyperfilter_iff : S ∪ T ∈ hyperfilter J ↔ S ∈ hyperfilter J ∨ T ∈ hyperfilter J :=
  Ultrafilter.union_mem_iff

/-- **Index ultrafilter, Fact 2.5(3).** A complement is large if and only if the set is not. -/
theorem compl_mem_hyperfilter_iff : Sᶜ ∈ hyperfilter J ↔ S ∉ hyperfilter J :=
  Ultrafilter.compl_mem_iff_notMem

/-- **Index ultrafilter.** Of a set and its complement, exactly one is large. -/
theorem xor_mem_hyperfilter (S : Set J) : Xor (S ∈ hyperfilter J) (Sᶜ ∈ hyperfilter J) :=
  ((isFilter_sets _).isUltrafilter_iff_xor.mp (isUltrafilter_hyperfilter J)) S

/-- **Index ultrafilter, Fact 2.5(4).** If finitely many pairwise disjoint sets have a large
union, exactly one of them is large. -/
theorem existsUnique_mem_hyperfilter_of_biUnion_mem {ι : Type*} (s : Finset ι) (A : ι → Set J)
    (hdisj : (↑s : Set ι).PairwiseDisjoint A) (hU : (⋃ i ∈ s, A i) ∈ hyperfilter J) :
    ∃! i, i ∈ s ∧ A i ∈ hyperfilter J :=
  (isUltrafilter_hyperfilter J).existsUnique_mem_of_biUnion_mem s A hdisj hU

/-- **Index ultrafilter.** A final segment $`\{n : N \le n\}` of the natural numbers is
large. -/
theorem setOf_le_mem_hyperfilter (N : ℕ) : {n : ℕ | N ≤ n} ∈ hyperfilter ℕ :=
  Nat.hyperfilter_le_atTop (mem_atTop N)

/-- **Index ultrafilter.** A property of natural numbers that holds from some index on holds on
a large set. -/
theorem eventually_hyperfilter_of_forall_ge {p : ℕ → Prop} (N : ℕ) (h : ∀ n, N ≤ n → p n) :
    ∀ᶠ n in hyperfilter ℕ, p n :=
  mem_hyperfilter_of_superset (setOf_le_mem_hyperfilter N) h

/-- **Index ultrafilter.** A property that holds eventually along the natural numbers holds on a
large set. -/
theorem eventually_hyperfilter_of_eventually_atTop {p : ℕ → Prop} (h : ∀ᶠ n in atTop, p n) :
    ∀ᶠ n in hyperfilter ℕ, p n :=
  Nat.hyperfilter_le_atTop h

/-- **Index ultrafilter.** A property that holds on a large set of natural numbers holds at
arbitrarily large indices. -/
theorem exists_ge_of_eventually_hyperfilter {p : ℕ → Prop} (h : ∀ᶠ n in hyperfilter ℕ, p n)
    (N : ℕ) : ∃ n, N ≤ n ∧ p n := by
  obtain ⟨n, hn⟩ := Filter.nonempty_of_mem (Filter.inter_mem (setOf_le_mem_hyperfilter N) h)
  exact ⟨n, hn.1, hn.2⟩

/-- **Index ultrafilter, the question of Section 2.2.** Exactly one of the set of even numbers
and the set of odd numbers is large. -/
theorem xor_even_odd_mem_hyperfilter :
    Xor ({n : ℕ | Even n} ∈ hyperfilter ℕ) ({n : ℕ | Odd n} ∈ hyperfilter ℕ) := by
  rw [← compl_setOf_even]
  exact xor_mem_hyperfilter _

end Hyperfilter

end Goldblatt
