import Goldblatt.Ch11_InternalSets
import Goldblatt.Ch12_InternalFunctions

/-!
# 16 (part 1). Rings, Algebras and Measures: Sections 16.1 and 16.2

This is the first of five parts of Chapter 16 (the overview is on the chapter page
{lit}`Goldblatt.Ch16_LoebMeasure`). It reviews the standard vocabulary of measure theory in the
book's own formulation: rings, algebras, sigma-rings and sigma-algebras of subsets of a set,
and finitely additive and countably additive functions on a ring with values in
$`[0, \infty]`. Each notion is tied to its Mathlib counterpart, and the standard examples of
the two sections are proved. The examples that involve internal sets are in part 4.
-/

universe u

namespace Goldblatt

open Set Filter MeasureTheory Function
open scoped ENNReal Topology

/-!
## 16.1 Rings and Algebras

A measure assigns a size to the members of a collection of subsets of a set $`S`, and the
collection has to be closed under enough set operations for additivity to make sense. The
weakest structure used in the chapter is a _ring_: a nonempty collection closed under
differences and binary unions. An _algebra_ is a ring that contains $`S`, a _sigma-ring_ is a
ring closed under countable unions, and a _sigma-algebra_ is both. In this formalization the
underlying set $`S` is a type, and a collection of subsets is a set of sets.
-/

section Rings

variable {S : Type u}

/-- **Section 16.1.** A _ring_ of subsets of $`S`: a nonempty collection $`\mathcal A` such
that $`A - B` and $`A \cup B` belong to $`\mathcal A` whenever $`A` and $`B` do. -/
structure IsRingOfSets (𝒜 : Set (Set S)) : Prop where
  /-- A ring has a member. -/
  nonempty : 𝒜.Nonempty
  /-- A ring is closed under differences. -/
  diff_mem : ∀ ⦃A B : Set S⦄, A ∈ 𝒜 → B ∈ 𝒜 → A \ B ∈ 𝒜
  /-- A ring is closed under binary unions. -/
  union_mem : ∀ ⦃A B : Set S⦄, A ∈ 𝒜 → B ∈ 𝒜 → A ∪ B ∈ 𝒜

namespace IsRingOfSets

variable {𝒜 : Set (Set S)}

/-- **Section 16.1.** The empty set belongs to every ring, because $`A - A = \emptyset`. -/
theorem empty_mem (h : IsRingOfSets 𝒜) : ∅ ∈ 𝒜 := by
  obtain ⟨A, hA⟩ := h.nonempty
  simpa using h.diff_mem hA hA

/-- **Section 16.1.** A ring is closed under intersections, because
$`A \cap B = A - (A - B)`. -/
theorem inter_mem (h : IsRingOfSets 𝒜) {A B : Set S} (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) : A ∩ B ∈ 𝒜 := by
  have := h.diff_mem hA (h.diff_mem hA hB)
  rwa [sdiff_sdiff_right_self] at this

/-- **Section 16.1.** A ring is closed under symmetric differences, because
$`A \mathbin\Delta B = (A - B) \cup (B - A)`. -/
theorem symmDiff_mem (h : IsRingOfSets 𝒜) {A B : Set S} (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) :
    symmDiff A B ∈ 𝒜 :=
  h.union_mem (h.diff_mem hA hB) (h.diff_mem hB hA)

/-- **Section 16.1.** A ring is closed under finite unions. -/
theorem biUnion_finset_mem (h : IsRingOfSets 𝒜) {ι : Type*} (s : Finset ι) {A : ι → Set S}
    (hA : ∀ i ∈ s, A i ∈ 𝒜) : ⋃ i ∈ s, A i ∈ 𝒜 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.empty_mem
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    exact h.union_mem (hA a (Finset.mem_insert_self a s))
      (ih fun i hi => hA i (Finset.mem_insert_of_mem hi))

/-- **Section 16.1.** A ring is closed under unions over an initial segment of the natural
numbers. -/
theorem biUnion_le_mem (h : IsRingOfSets 𝒜) {A : ℕ → Set S} (hA : ∀ n, A n ∈ 𝒜) (k : ℕ) :
    ⋃ n ≤ k, A n ∈ 𝒜 := by
  have : ⋃ n ≤ k, A n = ⋃ n ∈ Finset.range (k + 1), A n := by
    ext x; simp
  rw [this]
  exact h.biUnion_finset_mem _ fun i _ => hA i

/-- **Section 16.1.** A ring is closed under intersections over an initial segment of the
natural numbers. -/
theorem biInter_le_mem (h : IsRingOfSets 𝒜) {A : ℕ → Set S} (hA : ∀ n, A n ∈ 𝒜) (k : ℕ) :
    ⋂ n ≤ k, A n ∈ 𝒜 := by
  induction k with
  | zero => simpa using hA 0
  | succ k ih =>
    have : ⋂ n ≤ k + 1, A n = (⋂ n ≤ k, A n) ∩ A (k + 1) := by
      ext x
      simp only [mem_iInter, mem_inter_iff]
      constructor
      · intro hx
        exact ⟨fun n hn => hx n (Nat.le_succ_of_le hn), hx _ le_rfl⟩
      · rintro ⟨h1, h2⟩ n hn
        rcases Nat.of_le_succ hn with hn | rfl
        · exact h1 n hn
        · exact h2
    rw [this]
    exact h.inter_mem ih (hA _)

/-- The terms of the disjoint sequence obtained from a sequence of members of a ring belong to
the ring. -/
theorem disjointed_mem (h : IsRingOfSets 𝒜) {A : ℕ → Set S} (hA : ∀ n, A n ∈ 𝒜) (n : ℕ) :
    disjointed A n ∈ 𝒜 := by
  cases n with
  | zero => simpa using hA 0
  | succ n =>
    rw [disjointed_add_one]
    have : partialSups A n = ⋃ i ≤ n, A i := by
      ext x; simp [partialSups_eq_biSup]
    rw [this]
    exact h.diff_mem (hA _) (h.biUnion_le_mem hA n)

/-- **Section 16.1, in Mathlib's terms.** A ring of sets in the sense of the book is a ring of
sets in the sense of Mathlib. -/
theorem isSetRing (h : IsRingOfSets 𝒜) : IsSetRing 𝒜 :=
  ⟨h.empty_mem, fun _ _ hA hB => h.union_mem hA hB, fun _ _ hA hB => h.diff_mem hA hB⟩

end IsRingOfSets

/-- **Section 16.1, in Mathlib's terms.** The book's rings of sets are exactly Mathlib's. -/
theorem isRingOfSets_iff_isSetRing {𝒜 : Set (Set S)} : IsRingOfSets 𝒜 ↔ IsSetRing 𝒜 :=
  ⟨fun h => h.isSetRing, fun h =>
    ⟨⟨∅, h.empty_mem⟩, fun _ _ hA hB => h.sdiff_mem hA hB, fun _ _ hA hB => h.union_mem hA hB⟩⟩

/-- **Section 16.1.** An _algebra_ of subsets of $`S`: a ring that contains $`S` itself. -/
structure IsAlgebraOfSets (𝒜 : Set (Set S)) : Prop extends IsRingOfSets 𝒜 where
  /-- An algebra contains the whole set. -/
  univ_mem : univ ∈ 𝒜

/-- **Section 16.1.** An algebra is closed under complements. -/
theorem IsAlgebraOfSets.compl_mem {𝒜 : Set (Set S)} (h : IsAlgebraOfSets 𝒜) {A : Set S}
    (hA : A ∈ 𝒜) : Aᶜ ∈ 𝒜 := by
  rw [compl_eq_univ_sdiff]
  exact h.diff_mem h.univ_mem hA

/-- **Section 16.1.** A ring is an algebra if and only if it is closed under complements. -/
theorem IsRingOfSets.isAlgebraOfSets_iff_compl {𝒜 : Set (Set S)} (h : IsRingOfSets 𝒜) :
    IsAlgebraOfSets 𝒜 ↔ ∀ A ∈ 𝒜, Aᶜ ∈ 𝒜 :=
  ⟨fun hA _ => hA.compl_mem, fun hc => ⟨h, by simpa using hc ∅ h.empty_mem⟩⟩

/-- **Section 16.1.** If $`\mathcal A` is a ring, then the collection of the members of
$`\mathcal A` and their complements is an algebra. -/
theorem IsRingOfSets.isAlgebraOfSets_union_compl {𝒜 : Set (Set S)} (h : IsRingOfSets 𝒜) :
    IsAlgebraOfSets (𝒜 ∪ compl '' 𝒜) := by
  refine ⟨⟨⟨∅, Or.inl h.empty_mem⟩, ?_, ?_⟩, Or.inr ⟨∅, h.empty_mem, compl_empty⟩⟩
  · rintro A B (hA | ⟨A, hA, rfl⟩) (hB | ⟨B, hB, rfl⟩)
    · exact Or.inl (h.diff_mem hA hB)
    · refine Or.inl ?_
      rw [sdiff_compl]
      exact h.inter_mem hA hB
    · refine Or.inr ⟨A ∪ B, h.union_mem hA hB, ?_⟩
      rw [compl_union, sdiff_eq]
    · refine Or.inl ?_
      have : Aᶜ \ Bᶜ = B \ A := by rw [sdiff_compl, inter_comm, sdiff_eq]
      rw [this]
      exact h.diff_mem hB hA
  · rintro A B (hA | ⟨A, hA, rfl⟩) (hB | ⟨B, hB, rfl⟩)
    · exact Or.inl (h.union_mem hA hB)
    · refine Or.inr ⟨B \ A, h.diff_mem hB hA, ?_⟩
      rw [sdiff_eq, compl_inter, compl_compl, union_comm]
    · refine Or.inr ⟨A \ B, h.diff_mem hA hB, ?_⟩
      rw [sdiff_eq, compl_inter, compl_compl]
    · refine Or.inr ⟨A ∩ B, h.inter_mem hA hB, ?_⟩
      rw [compl_inter]

/-- **Section 16.1.** The algebra of the members of a ring $`\mathcal A` and their complements
is the smallest algebra that includes $`\mathcal A`. -/
theorem IsAlgebraOfSets.union_compl_subset {𝒜 ℬ : Set (Set S)} (hℬ : IsAlgebraOfSets ℬ)
    (h : 𝒜 ⊆ ℬ) : 𝒜 ∪ compl '' 𝒜 ⊆ ℬ := by
  rintro A (hA | ⟨A, hA, rfl⟩)
  · exact h hA
  · exact hℬ.compl_mem (h hA)

/-- **Section 16.1.** A _sigma-ring_: a ring that is closed under countable unions. -/
structure IsSigmaRing (𝒜 : Set (Set S)) : Prop extends IsRingOfSets 𝒜 where
  /-- A sigma-ring is closed under countable unions. -/
  iUnion_mem : ∀ ⦃A : ℕ → Set S⦄, (∀ n, A n ∈ 𝒜) → ⋃ n, A n ∈ 𝒜

/-- **Section 16.1.** A sigma-ring is closed under countable intersections, because
$`\bigcap_n A_n = A_0 - \bigcup_n (A_0 - A_n)`. -/
theorem IsSigmaRing.iInter_mem {𝒜 : Set (Set S)} (h : IsSigmaRing 𝒜) {A : ℕ → Set S}
    (hA : ∀ n, A n ∈ 𝒜) : ⋂ n, A n ∈ 𝒜 := by
  have : ⋂ n, A n = A 0 \ ⋃ n, (A 0 \ A n) := by
    ext x
    simp only [mem_iInter, Set.mem_sdiff, mem_iUnion, not_exists, not_and, not_not]
    exact ⟨fun hx => ⟨hx 0, fun n _ => hx n⟩, fun hx n => hx.2 n hx.1⟩
  rw [this]
  exact h.diff_mem (hA 0) (h.iUnion_mem fun n => h.diff_mem (hA 0) (hA n))

/-- **Section 16.1.** A _sigma-algebra_: a sigma-ring that is an algebra. -/
structure IsSigmaAlgebra (𝒜 : Set (Set S)) : Prop extends IsSigmaRing 𝒜 where
  /-- A sigma-algebra contains the whole set. -/
  univ_mem : univ ∈ 𝒜

/-- A sigma-algebra is an algebra. -/
theorem IsSigmaAlgebra.isAlgebraOfSets {𝒜 : Set (Set S)} (h : IsSigmaAlgebra 𝒜) :
    IsAlgebraOfSets 𝒜 :=
  ⟨h.toIsRingOfSets, h.univ_mem⟩

/-- **Section 16.1, in Mathlib's terms.** The measurable sets of a Mathlib measurable space
form a sigma-algebra in the sense of the book. -/
theorem isSigmaAlgebra_measurableSet (m : MeasurableSpace S) :
    IsSigmaAlgebra {A : Set S | MeasurableSet[m] A} :=
  ⟨⟨⟨⟨∅, MeasurableSet.empty⟩, fun _ _ hA hB => hA.diff hB, fun _ _ hA hB => hA.union hB⟩,
    fun _ hA => MeasurableSet.iUnion hA⟩, MeasurableSet.univ⟩

/-- **Section 16.1, in Mathlib's terms.** A sigma-algebra in the sense of the book is the
collection of measurable sets of a Mathlib measurable space. -/
@[instance_reducible] def IsSigmaAlgebra.measurableSpace {𝒜 : Set (Set S)} (h : IsSigmaAlgebra 𝒜) :
    MeasurableSpace S where
  MeasurableSet' A := A ∈ 𝒜
  measurableSet_empty := h.empty_mem
  measurableSet_compl _ hA := h.isAlgebraOfSets.compl_mem hA
  measurableSet_iUnion _ hA := h.iUnion_mem hA

/-- **Section 16.1, in Mathlib's terms.** A collection of sets is a sigma-algebra if and only
if it is the collection of measurable sets of a measurable space. -/
theorem isSigmaAlgebra_iff_exists_measurableSpace {𝒜 : Set (Set S)} :
    IsSigmaAlgebra 𝒜 ↔ ∃ m : MeasurableSpace S, 𝒜 = {A | MeasurableSet[m] A} :=
  ⟨fun h => ⟨h.measurableSpace, rfl⟩, by
    rintro ⟨m, rfl⟩
    exact isSigmaAlgebra_measurableSet m⟩

/-- **Section 16.1.** The intersection of any family of sigma-algebras is a sigma-algebra. -/
theorem isSigmaAlgebra_sInter {𝔖 : Set (Set (Set S))} (h : ∀ 𝒜 ∈ 𝔖, IsSigmaAlgebra 𝒜) :
    IsSigmaAlgebra (⋂₀ 𝔖) :=
  ⟨⟨⟨⟨∅, fun 𝒜 h𝒜 => (h 𝒜 h𝒜).empty_mem⟩,
    fun _ _ hA hB 𝒜 h𝒜 => (h 𝒜 h𝒜).diff_mem (hA 𝒜 h𝒜) (hB 𝒜 h𝒜),
    fun _ _ hA hB 𝒜 h𝒜 => (h 𝒜 h𝒜).union_mem (hA 𝒜 h𝒜) (hB 𝒜 h𝒜)⟩,
    fun _ hA 𝒜 h𝒜 => (h 𝒜 h𝒜).iUnion_mem fun n => hA n 𝒜 h𝒜⟩,
    fun 𝒜 h𝒜 => (h 𝒜 h𝒜).univ_mem⟩

/-- **Section 16.1.** The sigma-algebra $`\mathcal S(\mathcal A)` _generated_ by a collection
$`\mathcal A` of subsets of $`S`: the intersection of all sigma-algebras that include
$`\mathcal A`. -/
def sigmaGenerated (𝒜 : Set (Set S)) : Set (Set S) := ⋂₀ {ℬ | IsSigmaAlgebra ℬ ∧ 𝒜 ⊆ ℬ}

/-- **Section 16.1.** $`\mathcal S(\mathcal A)` is a sigma-algebra. -/
theorem isSigmaAlgebra_sigmaGenerated (𝒜 : Set (Set S)) : IsSigmaAlgebra (sigmaGenerated 𝒜) :=
  isSigmaAlgebra_sInter fun _ h => h.1

/-- **Section 16.1.** $`\mathcal S(\mathcal A)` includes $`\mathcal A`. -/
theorem subset_sigmaGenerated (𝒜 : Set (Set S)) : 𝒜 ⊆ sigmaGenerated 𝒜 :=
  fun _ hA _ hℬ => hℬ.2 hA

/-- **Section 16.1.** $`\mathcal S(\mathcal A)` is the smallest sigma-algebra that includes
$`\mathcal A`. -/
theorem sigmaGenerated_subset {𝒜 ℬ : Set (Set S)} (hℬ : IsSigmaAlgebra ℬ) (h : 𝒜 ⊆ ℬ) :
    sigmaGenerated 𝒜 ⊆ ℬ :=
  sInter_subset_of_mem ⟨hℬ, h⟩

/-- **Section 16.1, in Mathlib's terms.** The members of $`\mathcal S(\mathcal A)` are the
measurable sets of the measurable space generated by $`\mathcal A`. -/
theorem sigmaGenerated_eq (𝒜 : Set (Set S)) :
    sigmaGenerated 𝒜 = {A | MeasurableSet[MeasurableSpace.generateFrom 𝒜] A} := by
  apply Subset.antisymm
  · exact sigmaGenerated_subset (isSigmaAlgebra_measurableSet _)
      fun A hA => MeasurableSpace.measurableSet_generateFrom hA
  · intro A hA ℬ hℬ
    exact MeasurableSpace.generateFrom_le (m := hℬ.1.measurableSpace) (fun B hB => hℬ.2 hB) A hA

/-- **Section 16.1, example 1.** The collection of all subsets of $`S` is a sigma-algebra. -/
theorem isSigmaAlgebra_univ : IsSigmaAlgebra (univ : Set (Set S)) :=
  ⟨⟨⟨⟨∅, trivial⟩, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩, fun _ _ => trivial⟩, trivial⟩

/-- **Section 16.1, example 2.** The finite subsets of $`S` form a ring. -/
theorem isRingOfSets_finite : IsRingOfSets {A : Set S | A.Finite} :=
  ⟨⟨∅, finite_empty⟩, fun _ _ hA _ => hA.sdiff, fun _ _ hA hB => hA.union hB⟩

/-- **Section 16.1, example 2.** If $`S` is infinite, the ring of finite subsets of $`S` is not
an algebra. -/
theorem not_isAlgebraOfSets_finite [Infinite S] : ¬ IsAlgebraOfSets {A : Set S | A.Finite} :=
  fun h => infinite_univ h.univ_mem

/-- **Section 16.1, example 2.** The finite or cofinite subsets of $`S` form an algebra. -/
theorem isAlgebraOfSets_finite_or_cofinite :
    IsAlgebraOfSets {A : Set S | A.Finite ∨ Aᶜ.Finite} := by
  refine ⟨⟨⟨∅, Or.inl finite_empty⟩, ?_, ?_⟩, Or.inr (by simp)⟩
  · rintro A B (hA | hA) (hB | hB)
    · exact Or.inl hA.sdiff
    · exact Or.inl hA.sdiff
    · refine Or.inr ?_
      rw [sdiff_eq, compl_inter, compl_compl]
      exact hA.union hB
    · refine Or.inl ?_
      rw [sdiff_eq]
      exact hB.subset inter_subset_right
  · rintro A B (hA | hA) (hB | hB)
    · exact Or.inl (hA.union hB)
    · exact Or.inr (hB.subset (compl_subset_compl.2 subset_union_right))
    · exact Or.inr (hA.subset (compl_subset_compl.2 subset_union_left))
    · exact Or.inr (hA.subset (compl_subset_compl.2 subset_union_left))

/-- **Section 16.1, example 2.** If $`S` is infinite, the algebra of finite or cofinite subsets
of $`S` is not a sigma-algebra: a sequence of distinct points gives countably many singletons
whose union is neither finite nor cofinite, when every other point of the sequence is
taken. -/
theorem not_isSigmaAlgebra_finite_or_cofinite [Infinite S] :
    ¬ IsSigmaAlgebra {A : Set S | A.Finite ∨ Aᶜ.Finite} := by
  intro h
  let e := Infinite.natEmbedding S
  have hmem := h.iUnion_mem (A := fun n => {e (2 * n)}) fun n => Or.inl (finite_singleton _)
  have h1 : (⋃ n, ({e (2 * n)} : Set S)).Infinite := by
    have : ⋃ n, ({e (2 * n)} : Set S) = range fun n => e (2 * n) := by ext x; simp [eq_comm]
    rw [this]
    exact infinite_range_of_injective fun m n hmn => by
      have := e.injective hmn
      omega
  have h2 : (⋃ n, ({e (2 * n)} : Set S))ᶜ.Infinite := by
    refine (infinite_range_of_injective (f := fun n => e (2 * n + 1)) fun m n hmn => by
      have := e.injective hmn
      omega).mono ?_
    rintro _ ⟨n, rfl⟩
    simp only [mem_compl_iff, mem_iUnion, mem_singleton_iff, not_exists]
    intro m hm
    have := e.injective hm
    omega
  rcases hmem with hf | hf
  · exact h1 hf
  · exact h2 hf

/-- **Section 16.1, example 2.** The countable subsets of $`S` form a sigma-ring. -/
theorem isSigmaRing_countable : IsSigmaRing {A : Set S | A.Countable} :=
  ⟨⟨⟨∅, countable_empty⟩, fun _ _ hA _ => hA.mono sdiff_subset, fun _ _ hA hB => hA.union hB⟩,
    fun _ hA => countable_iUnion hA⟩

/-- **Section 16.1, example 2.** If $`S` is uncountable, the sigma-ring of countable subsets of
$`S` is not an algebra. -/
theorem not_isAlgebraOfSets_countable [Uncountable S] :
    ¬ IsAlgebraOfSets {A : Set S | A.Countable} :=
  fun h => not_countable_univ h.univ_mem

end Rings

/-!
### The ring of left-open intervals and the Borel sets

The ring from which Lebesgue measure is built consists of the finite unions of bounded
intervals $`(a, b]` of real numbers. It is not an algebra and not a sigma-ring, and the
sigma-algebra it generates is the Borel algebra.
-/

section LeftOpen

/-- **Section 16.1, example 3.** The collection $`\mathcal C_{\mathbb R}` of finite unions of
left-open intervals $`(a, b]` of real numbers. (For $`b \le a` the interval is empty.) The
intervals of a union may overlap; that every member is also a disjoint union of such intervals
is {lit}`Goldblatt.exists_pairwiseDisjoint_of_mem_leftOpenRing`. -/
def leftOpenRing : Set (Set ℝ) := {A | ∃ s : Finset (ℝ × ℝ), A = ⋃ p ∈ s, Ioc p.1 p.2}

/-- **Section 16.1, example 3.** Every left-open interval belongs to
$`\mathcal C_{\mathbb R}`. -/
theorem Ioc_mem_leftOpenRing (a b : ℝ) : Ioc a b ∈ leftOpenRing :=
  ⟨{(a, b)}, by simp⟩

/-- **Section 16.1, example 3.** $`\mathcal C_{\mathbb R}` is a ring. The difference of two
left-open intervals is $`(a, b] - (c, d] = (a, \min(b, c)] \cup (\max(a, d), b]`. -/
theorem isRingOfSets_leftOpenRing : IsRingOfSets leftOpenRing := by
  classical
  have hunion : ∀ A B : Set ℝ, A ∈ leftOpenRing → B ∈ leftOpenRing → A ∪ B ∈ leftOpenRing := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s ∪ t, by rw [Finset.set_biUnion_union]⟩
  have hunions : ∀ (s : Finset (ℝ × ℝ)) (f : ℝ × ℝ → Set ℝ),
      (∀ p ∈ s, f p ∈ leftOpenRing) → ⋃ p ∈ s, f p ∈ leftOpenRing := by
    intro s f
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨∅, by simp⟩
    | insert a s _ ih =>
      intro hf
      rw [Finset.set_biUnion_insert]
      exact hunion _ _ (hf a (Finset.mem_insert_self a s))
        (ih fun p hp => hf p (Finset.mem_insert_of_mem hp))
  have hdiff1 : ∀ (A : Set ℝ) (c d : ℝ), A ∈ leftOpenRing → A \ Ioc c d ∈ leftOpenRing := by
    rintro _ c d ⟨s, rfl⟩
    have hd : (⋃ p ∈ s, Ioc p.1 p.2) \ Ioc c d = ⋃ p ∈ s, (Ioc p.1 p.2 \ Ioc c d) := by
      ext x
      simp only [Set.mem_sdiff, mem_iUnion]
      constructor
      · rintro ⟨⟨p, hp, hx⟩, hn⟩
        exact ⟨p, hp, hx, hn⟩
      · rintro ⟨p, hp, hx, hn⟩
        exact ⟨⟨p, hp, hx⟩, hn⟩
    rw [hd]
    refine hunions s _ fun p _ => ?_
    have : Ioc p.1 p.2 \ Ioc c d = Ioc p.1 (min p.2 c) ∪ Ioc (max p.1 d) p.2 := by
      ext x
      simp only [Set.mem_sdiff, mem_Ioc, mem_union, le_min_iff, max_lt_iff, not_and, not_le]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        by_cases hc : c < x
        · exact Or.inr ⟨⟨h1, h3 hc⟩, h2⟩
        · exact Or.inl ⟨h1, h2, not_lt.1 hc⟩
      · rintro (⟨h1, h2, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨⟨h1, h2⟩, fun hc => absurd hc (not_lt.2 h3)⟩
        · exact ⟨⟨h1, h3⟩, fun _ => h2⟩
    rw [this]
    exact hunion _ _ (Ioc_mem_leftOpenRing _ _) (Ioc_mem_leftOpenRing _ _)
  refine ⟨⟨∅, ⟨∅, by simp⟩⟩, ?_, fun A B => hunion A B⟩
  rintro A _ hA ⟨t, rfl⟩
  induction t using Finset.induction_on with
  | empty => simpa using hA
  | insert a t _ ih =>
    rw [Finset.set_biUnion_insert, ← sdiff_sdiff, sdiff_sdiff_comm]
    exact hdiff1 _ _ _ ih

/-- **Section 16.1, example 3.** Each nonempty member of $`\mathcal C_{\mathbb R}` has a
greatest element. -/
theorem exists_isGreatest_of_mem_leftOpenRing {A : Set ℝ} (hA : A ∈ leftOpenRing)
    (hne : A.Nonempty) : ∃ m, IsGreatest A m := by
  classical
  obtain ⟨s, rfl⟩ := hA
  induction s using Finset.induction_on with
  | empty => simp at hne
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert] at hne ⊢
    by_cases h1 : (Ioc a.1 a.2).Nonempty
    · have hg : IsGreatest (Ioc a.1 a.2) a.2 :=
        ⟨right_mem_Ioc.2 (nonempty_Ioc.1 h1), fun x hx => hx.2⟩
      by_cases h2 : (⋃ p ∈ s, Ioc p.1 p.2).Nonempty
      · obtain ⟨m, hm⟩ := ih h2
        exact ⟨_, hg.union hm⟩
      · rw [not_nonempty_iff_eq_empty.1 h2, union_empty]
        exact ⟨_, hg⟩
    · rw [not_nonempty_iff_eq_empty.1 h1, empty_union] at hne ⊢
      exact ih hne

/-- **Section 16.1, example 3.** $`\mathcal C_{\mathbb R}` is not an algebra: the real line has
no greatest element. -/
theorem not_isAlgebraOfSets_leftOpenRing : ¬ IsAlgebraOfSets leftOpenRing := by
  intro h
  obtain ⟨m, hm⟩ := exists_isGreatest_of_mem_leftOpenRing h.univ_mem univ_nonempty
  exact absurd (hm.2 (mem_univ (m + 1))) (by simp)

/-- **Section 16.1, example 3.** The open interval $`(0, 1)` does not belong to
$`\mathcal C_{\mathbb R}`, because it has no greatest element. -/
theorem Ioo_zero_one_notMem_leftOpenRing : Ioo (0 : ℝ) 1 ∉ leftOpenRing := by
  intro h
  obtain ⟨m, hm⟩ := exists_isGreatest_of_mem_leftOpenRing h ⟨1 / 2, by norm_num⟩
  have h1 := hm.1
  have := hm.2 (show (m + 1) / 2 ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [h1.1], by linarith [h1.2]⟩)
  linarith [h1.2]

/-- **Section 16.1, example 3.** The open interval $`(0, 1)` is the union of the intervals
$`(0, 1 - \tfrac1{n+1}]`, all of which belong to $`\mathcal C_{\mathbb R}`; so
$`\mathcal C_{\mathbb R}` is not closed under countable unions. -/
theorem Ioo_zero_one_eq_iUnion_Ioc :
    Ioo (0 : ℝ) 1 = ⋃ n : ℕ, Ioc (0 : ℝ) (1 - 1 / ((n : ℝ) + 1)) := by
  ext x
  simp only [mem_Ioo, mem_iUnion, mem_Ioc]
  constructor
  · rintro ⟨h0, h1⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h1)
    exact ⟨n, h0, by linarith⟩
  · rintro ⟨n, h0, h1⟩
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨h0, by linarith⟩

/-- **Section 16.1, example 3.** $`\mathcal C_{\mathbb R}` is not a sigma-ring. -/
theorem not_isSigmaRing_leftOpenRing : ¬ IsSigmaRing leftOpenRing := fun h =>
  Ioo_zero_one_notMem_leftOpenRing
    (Ioo_zero_one_eq_iUnion_Ioc ▸ h.iUnion_mem fun _ => Ioc_mem_leftOpenRing _ _)

/-- **Section 16.1, example 3.** The interval $`(0, 1]` is the union of the pairwise disjoint
intervals $`(\tfrac1{n+2}, \tfrac1{n+1}]`, so $`\mathcal C_{\mathbb R}` does contain some
countable unions that are not finite unions. -/
theorem Ioc_zero_one_eq_iUnion_Ioc :
    Ioc (0 : ℝ) 1 = ⋃ n : ℕ, Ioc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)) ∧
      Pairwise (Disjoint on fun n : ℕ => Ioc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) := by
  constructor
  · ext x
    simp only [mem_Ioc, mem_iUnion]
    constructor
    · rintro ⟨h0, h1⟩
      have hex : ∃ n : ℕ, 1 / ((n : ℝ) + 2) < x := by
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt h0
        exact ⟨n, lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by linarith)) hn⟩
      classical
      refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
      by_cases h : Nat.find hex = 0
      · rw [h]; simpa using h1
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
        have := Nat.find_min hex (m := k) (by omega)
        rw [hk]
        push_cast
        rw [not_lt] at this
        convert this using 2
        ring
    · rintro ⟨n, h0, h1⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      refine ⟨by linarith, h1.trans ?_⟩
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · have key : ∀ m n : ℕ, m < n →
        Disjoint (Ioc (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 1)))
          (Ioc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) := by
      intro m n hmn
      rw [Set.disjoint_left]
      rintro x ⟨h1, _⟩ ⟨_, h2⟩
      have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 2) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
        linarith
      linarith
    intro m n hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · exact key m n h
    · exact (key n m h).symm

/-- **Section 16.1, example 3.** Every member of $`\mathcal C_{\mathbb R}` is a _disjoint_
union of finitely many left-open intervals. The proof removes the intervals one at a time:
taking $`(c, d]` away from a disjoint union of intervals $`(a, b]` leaves the disjoint union of
the intervals $`(a, \min(b, c)]` and $`(\max(a, d), b]`, and then $`(c, d]` can be added back
as one more piece. -/
theorem exists_pairwiseDisjoint_of_mem_leftOpenRing {A : Set ℝ} (hA : A ∈ leftOpenRing) :
    ∃ s : Finset (ℝ × ℝ), A = ⋃ p ∈ s, Ioc p.1 p.2 ∧
      (s : Set (ℝ × ℝ)).PairwiseDisjoint fun p => Ioc p.1 p.2 := by
  classical
  have hdiff : ∀ (s : Finset (ℝ × ℝ)) (c d : ℝ), c ≤ d →
      (s : Set (ℝ × ℝ)).PairwiseDisjoint (fun p => Ioc p.1 p.2) →
      ∃ t : Finset (ℝ × ℝ), (⋃ p ∈ s, Ioc p.1 p.2) \ Ioc c d = ⋃ p ∈ t, Ioc p.1 p.2 ∧
        (t : Set (ℝ × ℝ)).PairwiseDisjoint fun p => Ioc p.1 p.2 := by
    intro s c d hcd hs
    let g : ℝ × ℝ → Finset (ℝ × ℝ) := fun p => {(p.1, min p.2 c), (max p.1 d, p.2)}
    have hg : ∀ p : ℝ × ℝ, ⋃ q ∈ g p, Ioc q.1 q.2 = Ioc p.1 p.2 \ Ioc c d := by
      intro p
      ext x
      simp only [g, Finset.mem_insert, Finset.mem_singleton, mem_iUnion, exists_prop, exists_eq_or_imp,
        exists_eq_left, Set.mem_sdiff, mem_Ioc, le_min_iff, max_lt_iff, not_and, not_le]
      constructor
      · rintro (⟨h1, h2, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨⟨h1, h2⟩, fun hc => absurd hc (not_lt.2 h3)⟩
        · exact ⟨⟨h1, h3⟩, fun _ => h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        by_cases hc : c < x
        · exact Or.inr ⟨⟨h1, h3 hc⟩, h2⟩
        · exact Or.inl ⟨h1, h2, not_lt.1 hc⟩
    refine ⟨s.biUnion g, ?_, ?_⟩
    · rw [Finset.set_biUnion_biUnion]
      simp_rw [hg]
      ext x
      simp only [Set.mem_sdiff, mem_iUnion, exists_prop]
      constructor
      · rintro ⟨⟨p, hp, hx⟩, hn⟩
        exact ⟨p, hp, hx, hn⟩
      · rintro ⟨p, hp, hx, hn⟩
        exact ⟨⟨p, hp, hx⟩, hn⟩
    · rw [Finset.coe_biUnion]
      refine Set.PairwiseDisjoint.biUnion_finset ?_ fun p _ => ?_
      · refine hs.mono fun p => ?_
        change (g p).sup (fun q => Ioc q.1 q.2) ≤ Ioc p.1 p.2
        rw [Finset.sup_set_eq_biUnion, hg]
        exact sdiff_subset
      · simp only [g, Finset.coe_insert, Finset.coe_singleton]
        refine (Set.pairwiseDisjoint_singleton _ _).insert fun q hq _ => ?_
        rw [mem_singleton_iff] at hq
        subst hq
        rw [Set.disjoint_left]
        rintro x ⟨_, h1⟩ ⟨h2, _⟩
        have := (le_min_iff.1 h1).2
        have := (max_lt_iff.1 h2).2
        linarith
  obtain ⟨s, rfl⟩ := hA
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | insert a s _ ih =>
    obtain ⟨t, ht, htd⟩ := ih
    rw [Finset.set_biUnion_insert, ht]
    rcases le_or_gt a.1 a.2 with ha | ha
    · obtain ⟨t', ht', htd'⟩ := hdiff t a.1 a.2 ha htd
      refine ⟨insert a t', ?_, ?_⟩
      · rw [Finset.set_biUnion_insert, ← ht', union_sdiff_self]
      · rw [Finset.coe_insert]
        refine htd'.insert fun q hq _ => ?_
        have hsub : Ioc q.1 q.2 ⊆ (⋃ p ∈ t, Ioc p.1 p.2) \ Ioc a.1 a.2 := by
          rw [ht']
          exact subset_biUnion_of_mem (u := fun p : ℝ × ℝ => Ioc p.1 p.2) hq
        exact disjoint_sdiff_right.mono_right hsub
    · rw [Ioc_eq_empty (not_lt.2 ha.le), empty_union]
      exact ⟨t, rfl, htd⟩

/-- **Section 16.1, example 4.** The sigma-algebra generated by $`\mathcal C_{\mathbb R}` is
the Borel sigma-algebra $`\mathcal B_{\mathbb R}` of the real line. -/
theorem generateFrom_leftOpenRing : MeasurableSpace.generateFrom leftOpenRing = borel ℝ := by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨s, rfl⟩
    borelize ℝ
    exact s.measurableSet_biUnion fun p _ => measurableSet_Ioc
  · rw [borel_eq_generateFrom_Ioc ℝ]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨l, u, -, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom (Ioc_mem_leftOpenRing l u)

/-- **Section 16.1, example 4.** The Borel sets of the real line are the members of the
sigma-algebra $`\mathcal S(\mathcal C_{\mathbb R})`. -/
theorem sigmaGenerated_leftOpenRing :
    sigmaGenerated leftOpenRing = {B : Set ℝ | MeasurableSet[borel ℝ] B} := by
  rw [sigmaGenerated_eq, generateFrom_leftOpenRing]

/-- **Section 16.1, example 4.** The Borel sigma-algebra of the real line is also generated by
the open intervals. -/
theorem generateFrom_Ioo_eq_borel :
    MeasurableSpace.generateFrom {A : Set ℝ | ∃ a b : ℝ, A = Ioo a b} = borel ℝ := by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨a, b, rfl⟩
    borelize ℝ
    exact measurableSet_Ioo
  · rw [Real.borel_eq_generateFrom_Ioo_rat]
    refine MeasurableSpace.generateFrom_le ?_
    simp only [mem_iUnion, mem_singleton_iff]
    rintro _ ⟨a, b, -, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom ⟨a, b, rfl⟩

/-- **Section 16.1, example 4.** The Borel sigma-algebra of the real line is generated by the
open sets; this is Mathlib's definition. -/
theorem generateFrom_isOpen_eq_borel :
    MeasurableSpace.generateFrom {A : Set ℝ | IsOpen A} = borel ℝ := rfl

end LeftOpen

/-!
## 16.2 Measures

Let $`\mathcal A` be a ring of subsets of $`S`. A function $`\mu` from $`\mathcal A` to
$`[0, \infty]` with $`\mu(\emptyset) = 0` is _finitely additive_ if it is additive on disjoint
pairs, and a _measure_ if it is additive on every pairwise disjoint sequence of members of
$`\mathcal A` whose union happens to lie in $`\mathcal A`. The values are taken in Mathlib's
extended nonnegative reals, and $`\mu` is a function on all subsets of $`S` of which only the
values on $`\mathcal A` matter.
-/

section Measures

variable {S : Type u}

/-- **Section 16.2, condition M2.** A function $`\mu` with values in $`[0, \infty]` is
_finitely additive_ on $`\mathcal A` if $`\mu(\emptyset) = 0` and
$`\mu(A \cup B) = \mu(A) + \mu(B)` for disjoint $`A, B \in \mathcal A`. -/
structure IsFinitelyAdditive (𝒜 : Set (Set S)) (μ : Set S → ℝ≥0∞) : Prop where
  /-- The empty set has measure zero. -/
  empty : μ ∅ = 0
  /-- Additivity on disjoint pairs. -/
  union : ∀ ⦃A B : Set S⦄, A ∈ 𝒜 → B ∈ 𝒜 → Disjoint A B → μ (A ∪ B) = μ A + μ B

/-- **Section 16.2, condition M1.** A function $`\mu` with values in $`[0, \infty]` is a
_measure_ on $`\mathcal A` if $`\mu(\emptyset) = 0` and
$`\mu(\bigcup_n A_n) = \sum_n \mu(A_n)` for every sequence of pairwise disjoint members of
$`\mathcal A` whose union belongs to $`\mathcal A` (countable additivity). -/
structure IsMeasureOnRing (𝒜 : Set (Set S)) (μ : Set S → ℝ≥0∞) : Prop where
  /-- The empty set has measure zero. -/
  empty : μ ∅ = 0
  /-- Countable additivity. -/
  iUnion : ∀ ⦃A : ℕ → Set S⦄, (∀ n, A n ∈ 𝒜) → Pairwise (Disjoint on A) → ⋃ n, A n ∈ 𝒜 →
    μ (⋃ n, A n) = ∑' n, μ (A n)

variable {𝒜 : Set (Set S)} {μ : Set S → ℝ≥0∞}

/-- **Section 16.2.** A measure on a ring is finitely additive. -/
theorem IsMeasureOnRing.isFinitelyAdditive (h : IsMeasureOnRing 𝒜 μ) (hR : IsRingOfSets 𝒜) :
    IsFinitelyAdditive 𝒜 μ := by
  refine ⟨h.empty, fun A B hA hB hAB => ?_⟩
  let F : ℕ → Set S := fun n => if n = 0 then A else if n = 1 then B else ∅
  have hF : ⋃ n, F n = A ∪ B := by
    ext x
    simp only [mem_iUnion, mem_union, F]
    constructor
    · rintro ⟨n, hn⟩
      split_ifs at hn with h0 h1
      · exact Or.inl hn
      · exact Or.inr hn
      · exact absurd hn (notMem_empty x)
    · rintro (hx | hx)
      · exact ⟨0, by simpa using hx⟩
      · exact ⟨1, by simpa using hx⟩
  have hmem : ∀ n, F n ∈ 𝒜 := fun n => by
    simp only [F]; split_ifs
    exacts [hA, hB, hR.empty_mem]
  have hdisj : Pairwise (Disjoint on F) := by
    intro m n hmn
    simp only [Function.onFun, F]
    split_ifs with h1 h2 h3 h4 h5 h6 <;>
      first | exact hAB | exact hAB.symm | (exfalso; omega) | simp
  have := h.iUnion hmem hdisj (hF ▸ hR.union_mem hA hB)
  rw [hF, tsum_eq_sum (s := {0, 1}) (fun n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [F, hn.1, hn.2, h.empty])] at this
  simpa [F] using this

namespace IsFinitelyAdditive

/-- **Section 16.2.** A finitely additive function on a ring is additive on finite families of
pairwise disjoint members of the ring. -/
theorem biUnion_finset (h : IsFinitelyAdditive 𝒜 μ) (hR : IsRingOfSets 𝒜) {ι : Type*}
    (s : Finset ι) {A : ι → Set S} (hA : ∀ i ∈ s, A i ∈ 𝒜)
    (hd : (s : Set ι).PairwiseDisjoint A) : μ (⋃ i ∈ s, A i) = ∑ i ∈ s, μ (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.empty]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    rw [h.union (hA a (Finset.mem_insert_self a s))
      (hR.biUnion_finset_mem s fun i hi => hA i (Finset.mem_insert_of_mem hi)) ?_,
      ih (fun i hi => hA i (Finset.mem_insert_of_mem hi))
        (hd.subset (by simp [Finset.coe_insert]))]
    rw [disjoint_iUnion₂_right]
    intro i hi
    exact hd (by simp) (by simp [hi]) (fun hai => ha (hai ▸ hi))

/-- **Section 16.2.** A finitely additive function on a ring is monotonic. -/
theorem mono (h : IsFinitelyAdditive 𝒜 μ) (hR : IsRingOfSets 𝒜) {A B : Set S} (hA : A ∈ 𝒜)
    (hB : B ∈ 𝒜) (hAB : A ⊆ B) : μ A ≤ μ B := by
  have := h.union hA (hR.diff_mem hB hA) disjoint_sdiff_right
  rw [union_sdiff_cancel hAB] at this
  rw [this]
  exact le_self_add

/-- **Section 16.2.** A finitely additive function on a ring is subtractive:
$`\mu(B - A) = \mu(B) - \mu(A)` when $`A \subseteq B` and $`\mu(B) < \infty`. The proof only
needs $`\mu(A) < \infty`. -/
theorem diff (h : IsFinitelyAdditive 𝒜 μ) (hR : IsRingOfSets 𝒜) {A B : Set S} (hA : A ∈ 𝒜)
    (hB : B ∈ 𝒜) (hAB : A ⊆ B) (hfin : μ A ≠ ∞) : μ (B \ A) = μ B - μ A := by
  have := h.union hA (hR.diff_mem hB hA) disjoint_sdiff_right
  rw [union_sdiff_cancel hAB] at this
  rw [this, ENNReal.add_sub_cancel_left hfin]

/-- A finitely additive function on a ring is subadditive on pairs. -/
theorem union_le (h : IsFinitelyAdditive 𝒜 μ) (hR : IsRingOfSets 𝒜) {A B : Set S} (hA : A ∈ 𝒜)
    (hB : B ∈ 𝒜) : μ (A ∪ B) ≤ μ A + μ B := by
  have := h.union hA (hR.diff_mem hB hA) disjoint_sdiff_right
  rw [union_sdiff_self] at this
  rw [this]
  gcongr
  exact h.mono hR (hR.diff_mem hB hA) hB sdiff_subset

end IsFinitelyAdditive

/-- **Section 16.2.** Countable additivity implies continuity along increasing sequences: if
$`(A_n)` is an increasing sequence of members of the ring whose union is in the ring, then
$`\mu(\bigcup_n A_n) = \sup_n \mu(A_n)`. -/
theorem IsMeasureOnRing.iUnion_eq_iSup (h : IsMeasureOnRing 𝒜 μ) (hR : IsRingOfSets 𝒜)
    {A : ℕ → Set S} (hA : ∀ n, A n ∈ 𝒜) (hmono : Monotone A) (hU : ⋃ n, A n ∈ 𝒜) :
    μ (⋃ n, A n) = ⨆ n, μ (A n) := by
  have hfa := h.isFinitelyAdditive hR
  have hD : ∀ n, disjointed A n ∈ 𝒜 := hR.disjointed_mem hA
  have hsum : ∀ n, ∑ i ∈ Finset.range (n + 1), μ (disjointed A i) = μ (A n) := by
    intro n
    rw [← hfa.biUnion_finset hR _ (fun i _ => hD i)
      (fun i _ j _ hij => disjoint_disjointed A hij)]
    congr 1
    rw [biUnion_range_succ_disjointed, hmono.partialSups_eq]
  rw [← iUnion_disjointed, h.iUnion hD (disjoint_disjointed A) (by rwa [iUnion_disjointed]),
    ENNReal.tsum_eq_iSup_nat]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    cases n with
    | zero => simp
    | succ n => rw [hsum n]; exact le_iSup (fun n => μ (A n)) n
  · refine iSup_le fun n => ?_
    rw [← hsum n]
    exact le_iSup (fun n => ∑ i ∈ Finset.range n, μ (disjointed A i)) (n + 1)

/-- **Section 16.2.** Continuity along increasing sequences, as a limit:
$`\mu(\bigcup_n A_n) = \lim_{n \to \infty} \mu(A_n)`. -/
theorem IsMeasureOnRing.tendsto_iUnion (h : IsMeasureOnRing 𝒜 μ) (hR : IsRingOfSets 𝒜)
    {A : ℕ → Set S} (hA : ∀ n, A n ∈ 𝒜) (hmono : Monotone A) (hU : ⋃ n, A n ∈ 𝒜) :
    Tendsto (fun n => μ (A n)) atTop (𝓝 (μ (⋃ n, A n))) := by
  rw [h.iUnion_eq_iSup hR hA hmono hU]
  exact tendsto_atTop_iSup fun m n hmn =>
    (h.isFinitelyAdditive hR).mono hR (hA m) (hA n) (hmono hmn)

/-- **Section 16.2.** A measure on a ring is countably subadditive on the ring: if a member
$`B` of the ring is covered by a sequence $`(A_n)` of members, then
$`\mu(B) \le \sum_n \mu(A_n)`. -/
theorem IsMeasureOnRing.le_tsum_of_subset_iUnion (h : IsMeasureOnRing 𝒜 μ)
    (hR : IsRingOfSets 𝒜) {B : Set S} (hB : B ∈ 𝒜) {A : ℕ → Set S} (hA : ∀ n, A n ∈ 𝒜)
    (hBA : B ⊆ ⋃ n, A n) : μ B ≤ ∑' n, μ (A n) := by
  have hfa := h.isFinitelyAdditive hR
  have hD : ∀ n, B ∩ disjointed A n ∈ 𝒜 := fun n => hR.inter_mem hB (hR.disjointed_mem hA n)
  have hU : ⋃ n, B ∩ disjointed A n = B := by
    rw [← inter_iUnion, iUnion_disjointed, inter_eq_left.2 hBA]
  have := h.iUnion hD (fun m n hmn => (disjoint_disjointed A hmn).mono inter_subset_right
    inter_subset_right) (hU.symm ▸ hB)
  rw [hU] at this
  rw [this]
  exact ENNReal.tsum_le_tsum fun n => hfa.mono hR (hD n) (hA n)
    (inter_subset_right.trans (disjointed_subset A n))

/-- **Section 16.2, in Mathlib's terms.** A Mathlib measure, restricted to a collection of
measurable sets, is a measure in the sense of the book. -/
theorem isMeasureOnRing_of_measure {m : MeasurableSpace S} (ν : Measure S)
    (h𝒜 : ∀ A ∈ 𝒜, MeasurableSet A) : IsMeasureOnRing 𝒜 ν :=
  ⟨measure_empty, fun _ hA hd _ => measure_iUnion hd fun n => h𝒜 _ (hA n)⟩

/-- **Section 16.2.** A member $`A` of the ring is $`\mu`-_finite_ if $`\mu(A) < \infty`; the
function $`\mu` is _sigma-finite_ if $`S` is the union of countably many $`\mu`-finite members
of the ring. -/
def IsSigmaFiniteOn (𝒜 : Set (Set S)) (μ : Set S → ℝ≥0∞) : Prop :=
  ∃ A : ℕ → Set S, (∀ n, A n ∈ 𝒜 ∧ μ (A n) < ∞) ∧ ⋃ n, A n = univ

/-- **Section 16.2, example 1.** The _counting measure_ $`\mu_c`: the number of elements of a
finite set, and $`\infty` for an infinite set. It agrees with Mathlib's counting measure
({lit}`Goldblatt.countingMeasure_eq_count`). -/
noncomputable def countingMeasure (A : Set S) : ℝ≥0∞ := A.encard

/-- **Section 16.2, example 1.** The counting measure of a finite set is its number of
elements. -/
theorem countingMeasure_of_finite {A : Set S} (hA : A.Finite) :
    countingMeasure A = A.ncard := by
  rw [countingMeasure, ← hA.cast_ncard_eq]; rfl

/-- **Section 16.2, example 1.** The counting measure of an infinite set is $`\infty`. -/
theorem countingMeasure_of_infinite {A : Set S} (hA : A.Infinite) : countingMeasure A = ∞ := by
  rw [countingMeasure, hA.encard_eq]; rfl

/-- **Section 16.2, example 1, in Mathlib's terms.** The counting measure of the book is
Mathlib's counting measure {name}`MeasureTheory.Measure.count`, on every set, whenever
singletons are measurable. -/
theorem countingMeasure_eq_count [MeasurableSpace S] [MeasurableSingletonClass S]
    (A : Set S) :
    countingMeasure A = Measure.count A := by
  by_cases hA : A.Finite
  · rw [Measure.count_apply hA.measurableSet]; rfl
  · rw [countingMeasure_of_infinite hA, Measure.count_apply_infinite hA]

/-- **Section 16.2, example 1.** The counting measure is a measure on the sigma-algebra of all
subsets of $`S`, and so on every collection of subsets: on the ring of finite sets and on the
algebra of finite or cofinite sets in particular. -/
theorem isMeasureOnRing_countingMeasure (𝒜 : Set (Set S)) :
    IsMeasureOnRing 𝒜 (countingMeasure : Set S → ℝ≥0∞) := by
  let _inst : MeasurableSpace S := ⊤
  have : (countingMeasure : Set S → ℝ≥0∞) = (Measure.count : Measure S) := by
    funext A
    rw [Measure.count_apply MeasurableSpace.measurableSet_top]; rfl
  rw [this]
  exact isMeasureOnRing_of_measure _ fun _ _ => MeasurableSpace.measurableSet_top

/-- **Section 16.2, example 1.** The counting measure on all subsets of $`S` is sigma-finite if
and only if $`S` is countable. -/
theorem isSigmaFiniteOn_countingMeasure_iff :
    IsSigmaFiniteOn (univ : Set (Set S)) countingMeasure ↔ Countable S := by
  constructor
  · rintro ⟨A, hA, hU⟩
    rw [← countable_univ_iff, ← hU]
    refine countable_iUnion fun n => Set.Finite.countable ?_
    by_contra hinf
    have := (hA n).2
    rw [countingMeasure_of_infinite hinf] at this
    exact lt_irrefl _ this
  · intro hS
    rcases isEmpty_or_nonempty S with hE | hN
    · exact ⟨fun _ => ∅, fun _ => ⟨trivial, by simp [countingMeasure]⟩,
        by simp [eq_univ_iff_forall]⟩
    · obtain ⟨f, hf⟩ := exists_surjective_nat S
      refine ⟨fun n => {f n}, fun n => ⟨trivial, ?_⟩, ?_⟩
      · rw [countingMeasure_of_finite (finite_singleton _)]
        exact ENNReal.natCast_lt_top _
      · rw [eq_univ_iff_forall]
        intro x
        obtain ⟨n, rfl⟩ := hf x
        exact mem_iUnion.2 ⟨n, rfl⟩

/-- **Section 16.2, example 2.** Lebesgue measure is a measure on the ring
$`\mathcal C_{\mathbb R}` of finite unions of left-open intervals. (The book builds
$`\lambda` on this ring by additive extension of the length of intervals; here it is the
restriction of Mathlib's Lebesgue measure, and
{lit}`Goldblatt.eq_volume_of_isFinitelyAdditive_leftOpenRing` shows that it is the only
additive extension.) -/
theorem isMeasureOnRing_volume_leftOpenRing :
    IsMeasureOnRing leftOpenRing (volume : Set ℝ → ℝ≥0∞) :=
  isMeasureOnRing_of_measure _ fun _ ⟨s, hs⟩ =>
    hs ▸ s.measurableSet_biUnion fun _ _ => measurableSet_Ioc

/-- **Section 16.2, example 2.** The measure of a left-open interval is its length:
$`\lambda((a, b]) = b - a`. -/
theorem volume_Ioc_eq (a b : ℝ) : volume (Ioc a b) = ENNReal.ofReal (b - a) := Real.volume_Ioc

/-- **Section 16.2, example 2.** The Lebesgue measure of a disjoint union of left-open
intervals is the sum of their lengths. With
{name}`Goldblatt.exists_pairwiseDisjoint_of_mem_leftOpenRing` this is the book's formula for
$`\lambda` on every member of $`\mathcal C_{\mathbb R}`. -/
theorem volume_biUnion_Ioc_of_pairwiseDisjoint (s : Finset (ℝ × ℝ))
    (hs : (s : Set (ℝ × ℝ)).PairwiseDisjoint fun p => Ioc p.1 p.2) :
    volume (⋃ p ∈ s, Ioc p.1 p.2) = ∑ p ∈ s, ENNReal.ofReal (p.2 - p.1) := by
  rw [measure_biUnion_finset hs fun p _ => measurableSet_Ioc]
  exact Finset.sum_congr rfl fun p _ => Real.volume_Ioc

/-- **Section 16.2, example 2.** Lebesgue measure on $`\mathcal C_{\mathbb R}` is _the_
additive extension of the length of intervals: a finitely additive function on
$`\mathcal C_{\mathbb R}` with $`\mu((a, b]) = b - a` for all $`a \le b` agrees with
$`\lambda` on every member of the ring. The book defines $`\lambda` on the ring as this
extension; here existence is supplied by Mathlib's Lebesgue measure
({name}`Goldblatt.isMeasureOnRing_volume_leftOpenRing`, {name}`Goldblatt.volume_Ioc_eq`) and
uniqueness is proved from the disjoint normal form of the members of the ring. -/
theorem eq_volume_of_isFinitelyAdditive_leftOpenRing {μ : Set ℝ → ℝ≥0∞}
    (h : IsFinitelyAdditive leftOpenRing μ)
    (hI : ∀ a b : ℝ, a ≤ b → μ (Ioc a b) = ENNReal.ofReal (b - a)) :
    ∀ A ∈ leftOpenRing, μ A = volume A := by
  intro A hA
  obtain ⟨s, rfl, hs⟩ := exists_pairwiseDisjoint_of_mem_leftOpenRing hA
  rw [h.biUnion_finset isRingOfSets_leftOpenRing s (fun p _ => Ioc_mem_leftOpenRing _ _) hs,
    volume_biUnion_Ioc_of_pairwiseDisjoint s hs]
  refine Finset.sum_congr rfl fun p _ => ?_
  rcases le_or_gt p.1 p.2 with hp | hp
  · exact hI _ _ hp
  · rw [Ioc_eq_empty (not_lt.2 hp.le), h.empty, ENNReal.ofReal_of_nonpos (by linarith)]

/-- **Section 16.2, example 2.** Lebesgue measure on $`\mathcal C_{\mathbb R}` is sigma-finite,
because the real line is the union of the intervals $`(-n, n]`. -/
theorem isSigmaFiniteOn_volume_leftOpenRing :
    IsSigmaFiniteOn leftOpenRing (volume : Set ℝ → ℝ≥0∞) := by
  refine ⟨fun n => Ioc (-(n : ℝ)) n, fun n => ⟨Ioc_mem_leftOpenRing _ _, ?_⟩, ?_⟩
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  · rw [eq_univ_iff_forall]
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact mem_iUnion.2 ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

end Measures

end Goldblatt
