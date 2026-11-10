import Goldblatt.Ch16_LoebMeasure.Rings

/-!
# 16 (part 2). Outer Measures and Lebesgue Measure: Sections 16.3 and 16.4

This is the second of five parts of Chapter 16 (the overview is on the chapter page
{lit}`Goldblatt.Ch16_LoebMeasure`). It reviews the extension procedure of Carathéodory: a
measure on a ring of sets defines an outer measure on all subsets, the sets that split every
set additively form a sigma-algebra that includes the ring, and the outer measure is a complete
measure on that sigma-algebra. Lebesgue measure is the instance of this construction that
starts from the length of left-open intervals; it is identified here with Mathlib's Lebesgue
measure, and the three facts about it that the last section of the chapter needs are proved.
-/

universe u

namespace Goldblatt

open Set Filter MeasureTheory Function
open scoped ENNReal Topology

/-!
## 16.3 Outer Measures

Let $`\mu` be a measure on a ring $`\mathcal A` of subsets of $`S`. The _outer measure_
$`\mu^+(B)` of an arbitrary subset $`B` is the infimum of the sums $`\sum_n \mu(A_n)` over all
sequences of members of the ring that cover $`B` (and $`\infty` if there is no such sequence).
The outer measure is built here with Mathlib's outer measure bounded by a function, applied to
the function that is $`\mu` on the ring and $`\infty` elsewhere, and the book's formula is a
theorem. Measurability with respect to $`\mu^+` is Mathlib's Carathéodory condition.
-/

section Outer

variable {S : Type u} {𝒜 : Set (Set S)} {μ : Set S → ℝ≥0∞}

/-- The function that agrees with $`\mu` on the ring and is $`\infty` elsewhere. -/
noncomputable def ringExtend (𝒜 : Set (Set S)) (μ : Set S → ℝ≥0∞) (B : Set S) : ℝ≥0∞ :=
  ⨅ _ : B ∈ 𝒜, μ B

/-- On the ring the extended function is $`\mu`. -/
theorem ringExtend_of_mem {B : Set S} (hB : B ∈ 𝒜) : ringExtend 𝒜 μ B = μ B := by
  simp [ringExtend, hB]

/-- Off the ring the extended function is $`\infty`. -/
theorem ringExtend_of_notMem {B : Set S} (hB : B ∉ 𝒜) : ringExtend 𝒜 μ B = ∞ := by
  simp [ringExtend, hB]

/-- **Section 16.3.** The _outer measure_ $`\mu^+` defined by a function $`\mu` on a ring
$`\mathcal A`: the largest outer measure that is at most $`\mu` on the ring. -/
noncomputable def ringOuter (𝒜 : Set (Set S)) (μ : Set S → ℝ≥0∞) : OuterMeasure S :=
  OuterMeasure.boundedBy (ringExtend 𝒜 μ)

/-- **Section 16.3, the definition of the outer measure.**
$`\mu^+(B) = \inf \{\sum_n \mu(A_n) : A_n \in \mathcal A,\ B \subseteq \bigcup_n A_n\}`. -/
theorem ringOuter_apply (hR : IsRingOfSets 𝒜) (h0 : μ ∅ = 0) (B : Set S) :
    ringOuter 𝒜 μ B =
      ⨅ (A : ℕ → Set S) (_ : ∀ n, A n ∈ 𝒜) (_ : B ⊆ ⋃ n, A n), ∑' n, μ (A n) := by
  have h0' : ringExtend 𝒜 μ ∅ = 0 := by rw [ringExtend_of_mem hR.empty_mem, h0]
  rw [ringOuter, OuterMeasure.boundedBy_eq_ofFunction h0',
    OuterMeasure.ofFunction_eq_iInf_mem _ h0' (P := fun A => A ∈ 𝒜)
      (fun A hA => ringExtend_of_notMem hA)]
  refine iInf_congr fun A => iInf_congr fun hA => iInf_congr fun _ => ?_
  exact tsum_congr fun n => ringExtend_of_mem (hA n)

/-- **Section 16.3.** The outer measure of a member of the ring is at most its measure. -/
theorem ringOuter_le_of_mem {B : Set S} (hB : B ∈ 𝒜) : ringOuter 𝒜 μ B ≤ μ B :=
  (OuterMeasure.boundedBy_le B).trans_eq (ringExtend_of_mem hB)

/-- **Section 16.3.** The outer measure of a set is at most the sum of the measures of the
terms of any sequence of members of the ring that covers it. -/
theorem ringOuter_le_tsum {B : Set S} {A : ℕ → Set S} (hA : ∀ n, A n ∈ 𝒜)
    (hB : B ⊆ ⋃ n, A n) : ringOuter 𝒜 μ B ≤ ∑' n, μ (A n) :=
  calc ringOuter 𝒜 μ B ≤ ringOuter 𝒜 μ (⋃ n, A n) := measure_mono hB
    _ ≤ ∑' n, ringOuter 𝒜 μ (A n) := measure_iUnion_le _
    _ ≤ ∑' n, μ (A n) := ENNReal.tsum_le_tsum fun n => ringOuter_le_of_mem (hA n)

/-- **Section 16.3.** The outer measure agrees with $`\mu` on the ring:
$`\mu^+(B) = \mu(B)` for $`B \in \mathcal A`. This is where countable additivity of $`\mu` is
used. -/
theorem ringOuter_eq_of_mem (hμ : IsMeasureOnRing 𝒜 μ) (hR : IsRingOfSets 𝒜) {B : Set S}
    (hB : B ∈ 𝒜) : ringOuter 𝒜 μ B = μ B := by
  refine le_antisymm (ringOuter_le_of_mem hB) ?_
  rw [ringOuter_apply hR hμ.empty]
  exact le_iInf fun A => le_iInf fun hA => le_iInf fun hBA =>
    hμ.le_tsum_of_subset_iUnion hR hB hA hBA

/-- **Section 16.3.** $`\mu^+(\emptyset) = 0`. -/
theorem ringOuter_empty : ringOuter 𝒜 μ ∅ = 0 := measure_empty

/-- **Section 16.3, monotonicity.** If $`A \subseteq B` then $`\mu^+(A) \le \mu^+(B)`. -/
theorem ringOuter_mono {A B : Set S} (h : A ⊆ B) : ringOuter 𝒜 μ A ≤ ringOuter 𝒜 μ B :=
  measure_mono h

/-- **Section 16.3, countable subadditivity.**
$`\mu^+(\bigcup_n A_n) \le \sum_n \mu^+(A_n)` for every sequence of subsets of $`S`. -/
theorem ringOuter_iUnion_le (A : ℕ → Set S) :
    ringOuter 𝒜 μ (⋃ n, A n) ≤ ∑' n, ringOuter 𝒜 μ (A n) :=
  measure_iUnion_le _

/-- **Section 16.3.** For a set $`B` of finite outer measure and $`\varepsilon > 0` there is an
increasing sequence $`A_0 \subseteq A_1 \subseteq \cdots` of members of the ring that covers
$`B` and has $`\mu^+(\bigcup_n A_n) \le \mu^+(B) + \varepsilon`.

The book states this for every $`B`, but a set of infinite outer measure need not be covered by
any sequence of members of a ring (take the ring of finite subsets of an uncountable set), so
the hypothesis $`\mu^+(B) < \infty` is needed. -/
theorem exists_monotone_cover (hR : IsRingOfSets 𝒜) (h0 : μ ∅ = 0) {B : Set S}
    (hB : ringOuter 𝒜 μ B ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ A : ℕ → Set S, (∀ n, A n ∈ 𝒜) ∧ Monotone A ∧ B ⊆ ⋃ n, A n ∧
      ringOuter 𝒜 μ (⋃ n, A n) ≤ ringOuter 𝒜 μ B + ε := by
  have h := ENNReal.lt_add_right hB hε
  conv_lhs at h => rw [ringOuter_apply hR h0]
  simp only [iInf_lt_iff] at h
  obtain ⟨A, hA, hBA, hlt⟩ := h
  have hU : ⋃ n, ⋃ i ≤ n, A i = ⋃ n, A n := by
    ext x
    simp only [mem_iUnion, exists_prop]
    exact ⟨fun ⟨_, i, _, hx⟩ => ⟨i, hx⟩, fun ⟨i, hx⟩ => ⟨i, i, le_rfl, hx⟩⟩
  refine ⟨fun n => ⋃ i ≤ n, A i, fun n => hR.biUnion_le_mem hA n, ?_, ?_, ?_⟩
  · intro m n hmn x hx
    simp only [mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨i, hi, hx⟩ := hx
    exact ⟨i, hi.trans hmn, hx⟩
  · rw [hU]; exact hBA
  · rw [hU]; exact (ringOuter_le_tsum hA Subset.rfl).trans hlt.le

/-- **Section 16.3.** A set of finite outer measure is covered by a sequence of members of the
ring of finite measure. -/
theorem exists_finite_cover (hR : IsRingOfSets 𝒜) (h0 : μ ∅ = 0) {B : Set S}
    (hB : ringOuter 𝒜 μ B ≠ ∞) :
    ∃ A : ℕ → Set S, (∀ n, A n ∈ 𝒜) ∧ (∀ n, μ (A n) ≠ ∞) ∧ B ⊆ ⋃ n, A n := by
  have h := lt_top_iff_ne_top.2 hB
  rw [ringOuter_apply hR h0] at h
  simp only [iInf_lt_iff] at h
  obtain ⟨A, hA, hBA, hlt⟩ := h
  exact ⟨A, hA, fun n => ne_top_of_le_ne_top hlt.ne (ENNReal.le_tsum (f := fun n => μ (A n)) n), hBA⟩

/-- **Section 16.3.** A set $`B` is $`\mu^+`-_measurable_ if it splits every set $`E`
additively: $`\mu^+(E) = \mu^+(E \cap B) + \mu^+(E - B)`. This is Mathlib's Carathéodory
condition for the outer measure. -/
theorem isCaratheodory_ringOuter_iff {B : Set S} :
    (ringOuter 𝒜 μ).IsCaratheodory B ↔
      ∀ E : Set S, ringOuter 𝒜 μ E = ringOuter 𝒜 μ (E ∩ B) + ringOuter 𝒜 μ (E \ B) :=
  Iff.rfl

/-- **Section 16.3.** For a set to be measurable it is enough that
$`\mu^+(E) \ge \mu^+(E \cap B) + \mu^+(E - B)` whenever $`\mu^+(E) < \infty`. This holds for
every outer measure. -/
theorem isCaratheodory_of_forall_ne_top {m : OuterMeasure S} {B : Set S}
    (h : ∀ E : Set S, m E ≠ ∞ → m (E ∩ B) + m (E \ B) ≤ m E) : m.IsCaratheodory B := by
  rw [OuterMeasure.isCaratheodory_iff_le']
  intro E
  by_cases hE : m E = ∞
  · rw [hE]; exact le_top
  · exact h E hE

/-- **Section 16.3.** All members of the ring are $`\mu^+`-measurable. Finite additivity is
enough for this. -/
theorem isCaratheodory_of_mem (hμ : IsFinitelyAdditive 𝒜 μ) (hR : IsRingOfSets 𝒜) {A : Set S}
    (hA : A ∈ 𝒜) : (ringOuter 𝒜 μ).IsCaratheodory A := by
  refine OuterMeasure.boundedBy_caratheodory fun t => ?_
  by_cases ht : t ∈ 𝒜
  · have hu : t ∩ A ∪ t \ A = t := by
      ext x; simp only [mem_union, mem_inter_iff, Set.mem_sdiff]; tauto
    rw [ringExtend_of_mem ht, ringExtend_of_mem (hR.inter_mem ht hA),
      ringExtend_of_mem (hR.diff_mem ht hA),
      ← hμ.union (hR.inter_mem ht hA) (hR.diff_mem ht hA)
        (Set.disjoint_left.2 fun x hx hx' => hx'.2 hx.2), hu]
  · rw [ringExtend_of_notMem ht]; exact le_top

/-- **Section 16.3.** The class $`\mathcal A(\mu)` of $`\mu^+`-measurable sets is a
sigma-algebra: it is the collection of measurable sets of Mathlib's Carathéodory measurable
space. -/
theorem isSigmaAlgebra_isCaratheodory (m : OuterMeasure S) :
    IsSigmaAlgebra {B : Set S | m.IsCaratheodory B} :=
  isSigmaAlgebra_measurableSet m.caratheodory

/-- **Section 16.3.** $`\mathcal A(\mu)` includes the sigma-algebra $`\mathcal S(\mathcal A)`
generated by the ring. -/
theorem generateFrom_le_caratheodory (hμ : IsFinitelyAdditive 𝒜 μ) (hR : IsRingOfSets 𝒜) :
    MeasurableSpace.generateFrom 𝒜 ≤ (ringOuter 𝒜 μ).caratheodory :=
  MeasurableSpace.generateFrom_le fun _ hA => isCaratheodory_of_mem hμ hR hA

/-- **Section 16.3.** $`\mathcal S(\mathcal A) \subseteq \mathcal A(\mu)`, in the book's
formulation. -/
theorem sigmaGenerated_subset_isCaratheodory (hμ : IsFinitelyAdditive 𝒜 μ)
    (hR : IsRingOfSets 𝒜) : sigmaGenerated 𝒜 ⊆ {B | (ringOuter 𝒜 μ).IsCaratheodory B} := by
  rw [sigmaGenerated_eq]
  exact fun B hB => generateFrom_le_caratheodory hμ hR B hB

/-- **Section 16.3.** All $`\mu^+`-null sets are $`\mu^+`-measurable. -/
theorem isCaratheodory_of_null {m : OuterMeasure S} {B : Set S} (h : m B = 0) :
    m.IsCaratheodory B :=
  m.isCaratheodory_of_measure_eq_zero h

/-- **Section 16.3.** The outer measure $`\mu^+`, as a Mathlib measure on the sigma-algebra
$`\mathcal A(\mu)` of $`\mu^+`-measurable sets. -/
noncomputable def caratheodoryMeasure (m : OuterMeasure S) : @Measure S m.caratheodory :=
  @OuterMeasure.toMeasure S m.caratheodory m le_rfl

/-- **Section 16.3.** On a $`\mu^+`-measurable set the measure is the outer measure. -/
theorem caratheodoryMeasure_apply (m : OuterMeasure S) {B : Set S} (hB : m.IsCaratheodory B) :
    caratheodoryMeasure m B = m B :=
  @toMeasure_apply S m.caratheodory m le_rfl B hB

/-- On an arbitrary set the measure on $`\mathcal A(\mu)` is at least the outer measure. -/
theorem le_caratheodoryMeasure_apply (m : OuterMeasure S) (B : Set S) :
    m B ≤ caratheodoryMeasure m B :=
  @le_toMeasure_apply S m.caratheodory m le_rfl B

/-- **Section 16.3.** $`\mu^+` is countably additive on $`\mathcal A(\mu)`: it is a measure
there in the sense of Section 16.2, and hence also on $`\mathcal S(\mathcal A)`. -/
theorem isMeasureOnRing_isCaratheodory (m : OuterMeasure S) :
    IsMeasureOnRing {B : Set S | m.IsCaratheodory B} m :=
  ⟨measure_empty, fun _ hA hd _ => m.iUnion_eq_of_caratheodory hA hd⟩

/-- **Section 16.3.** $`\mu^+` is a _complete_ measure on $`\mathcal A(\mu)`: every subset of a
measurable null set is measurable. -/
theorem isCaratheodory_of_subset_null {m : OuterMeasure S} {A B : Set S} (hAB : A ⊆ B)
    (hB : m B = 0) : m.IsCaratheodory A :=
  isCaratheodory_of_null (measure_mono_null hAB hB)

/-- **Section 16.3.** Completeness, in Mathlib's terms. -/
theorem isComplete_caratheodoryMeasure (m : OuterMeasure S) :
    @Measure.IsComplete S m.caratheodory (caratheodoryMeasure m) :=
  @Measure.IsComplete.mk S m.caratheodory (caratheodoryMeasure m) fun B hB =>
    isCaratheodory_of_null (le_antisymm ((le_caratheodoryMeasure_apply m B).trans_eq hB) zero_le)

/-- **Section 16.3.** If $`A \subseteq C \subseteq B` with $`A` and $`B` measurable and
$`\mu^+(A) = \mu^+(B) < \infty`, then $`C` is measurable and
$`\mu^+(C) = \mu^+(A) = \mu^+(B)`.

The book omits the finiteness hypothesis, but without it the statement fails: for Lebesgue
measure take $`A = [0, \infty)` and $`B = \mathbb R`. -/
theorem isCaratheodory_of_between {m : OuterMeasure S} {A B C : Set S}
    (hA : m.IsCaratheodory A) (hAC : A ⊆ C) (hCB : C ⊆ B) (hAB : m A = m B)
    (hfin : m A ≠ ∞) : m.IsCaratheodory C ∧ m C = m A := by
  have h1 := hA B
  rw [inter_eq_right.2 (hAC.trans hCB), ← hAB] at h1
  have h0 : m (B \ A) = 0 := by
    have : m A + 0 = m A + m (B \ A) := by rw [add_zero]; exact h1
    exact ((ENNReal.add_right_inj hfin).1 this).symm
  have hC : C = A ∪ (C \ A) := by rw [union_sdiff_cancel hAC]
  refine ⟨?_, le_antisymm ?_ (measure_mono hAC)⟩
  · rw [hC]
    exact m.isCaratheodory_union hA
      (isCaratheodory_of_subset_null (sdiff_subset_sdiff_left hCB) h0)
  · rw [hAB]; exact measure_mono hCB

/-- **Section 16.3, uniqueness of the extension.** Let $`\mu` be a sigma-finite measure on a
ring $`\mathcal A`, and let $`\nu` be a measure on a sigma-algebra that includes
$`\mathcal A` and is included in $`\mathcal A(\mu)`. If $`\nu` agrees with $`\mu` on
$`\mathcal A`, then $`\nu` agrees with $`\mu^+` on its whole sigma-algebra. In particular
$`\mu^+` is the only extension of $`\mu` to a measure on $`\mathcal S(\mathcal A)`, and the
only one on $`\mathcal A(\mu)`. -/
theorem measure_eq_ringOuter (hμ : IsMeasureOnRing 𝒜 μ) (hR : IsRingOfSets 𝒜)
    (hσ : IsSigmaFiniteOn 𝒜 μ) (m : MeasurableSpace S) (hm1 : ∀ A ∈ 𝒜, MeasurableSet[m] A)
    (hm2 : m ≤ (ringOuter 𝒜 μ).caratheodory) (ν : @Measure S m) (hν : ∀ A ∈ 𝒜, ν A = μ A)
    {B : Set S} (hB : MeasurableSet[m] B) : ν B = ringOuter 𝒜 μ B := by
  have hle : ∀ E : Set S, ν E ≤ ringOuter 𝒜 μ E := by
    have : ν.toOuterMeasure ≤ ringOuter 𝒜 μ :=
      OuterMeasure.le_boundedBy.2 fun s => le_iInf fun hs => (hν s hs).le
    exact fun E => this E
  have hfa := hμ.isFinitelyAdditive hR
  have key : ∀ A ∈ 𝒜, μ A ≠ ∞ → ν (A ∩ B) = ringOuter 𝒜 μ (A ∩ B) := by
    intro A hA hfin
    have h1 : ν (A ∩ B) + ν (A \ B) = ν A := measure_inter_add_sdiff A hB
    have h2 := hm2 B hB A
    rw [ringOuter_eq_of_mem hμ hR hA, ← hν A hA, ← h1] at h2
    refine le_antisymm (hle _) ?_
    by_contra hlt
    rw [not_le] at hlt
    have hfin' : ν (A \ B) ≠ ∞ :=
      ne_top_of_le_ne_top (by rw [hν A hA]; exact hfin) (measure_mono sdiff_subset)
    exact absurd h2 (ENNReal.add_lt_add_of_lt_of_le hfin' hlt (hle _)).ne
  obtain ⟨A, hA, hU⟩ := hσ
  have hD : ∀ n, disjointed A n ∈ 𝒜 := hR.disjointed_mem fun n => (hA n).1
  have hDfin : ∀ n, μ (disjointed A n) ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (hA n).2.ne
      (hfa.mono hR (hD n) (hA n).1 (disjointed_subset A n))
  have hBU : B = ⋃ n, disjointed A n ∩ B := by
    rw [← iUnion_inter, iUnion_disjointed, hU, univ_inter]
  have hdisj : Pairwise (Disjoint on fun n => disjointed A n ∩ B) := fun i j hij =>
    (disjoint_disjointed A hij).mono inter_subset_left inter_subset_left
  have hcar : ∀ n, (ringOuter 𝒜 μ).IsCaratheodory (disjointed A n ∩ B) := fun n =>
    (ringOuter 𝒜 μ).isCaratheodory_inter (isCaratheodory_of_mem hfa hR (hD n)) (hm2 B hB)
  calc ν B = ν (⋃ n, disjointed A n ∩ B) := by rw [← hBU]
    _ = ∑' n, ν (disjointed A n ∩ B) :=
      measure_iUnion hdisj fun n => (hm1 _ (hD n)).inter hB
    _ = ∑' n, ringOuter 𝒜 μ (disjointed A n ∩ B) :=
      tsum_congr fun n => key _ (hD n) (hDfin n)
    _ = ringOuter 𝒜 μ (⋃ n, disjointed A n ∩ B) :=
      ((ringOuter 𝒜 μ).iUnion_eq_of_caratheodory hcar hdisj).symm
    _ = ringOuter 𝒜 μ B := by rw [← hBU]

end Outer

/-!
## 16.4 Lebesgue Measure

Lebesgue outer measure is the outer measure of Section 16.3 for the ring of finite unions of
left-open intervals with the length of intervals as the measure, and the Lebesgue measurable
sets are the sets that are measurable for it. Both are identified with Mathlib's notions: the
outer measure is the outer measure of Mathlib's Lebesgue measure, and a set is Lebesgue
measurable exactly when it is null-measurable for that measure. The three facts listed in the
book are then proved in the form in which Section 16.8 uses them.
-/

section Lebesgue

/-- **Section 16.4.** _Lebesgue outer measure_ $`\lambda^+`: the outer measure defined by the
measure $`\lambda` on the ring $`\mathcal C_{\mathbb R}`. -/
noncomputable def lebesgueOuter : OuterMeasure ℝ := ringOuter leftOpenRing volume

/-- **Section 16.4.** A set of reals is _Lebesgue measurable_ if it is
$`\lambda^+`-measurable. -/
def LebesgueMeasurable (B : Set ℝ) : Prop := lebesgueOuter.IsCaratheodory B

/-- **Section 16.4.** Every Borel set is Lebesgue measurable. -/
theorem borel_le_caratheodory_lebesgueOuter : borel ℝ ≤ lebesgueOuter.caratheodory := by
  rw [← generateFrom_leftOpenRing]
  exact generateFrom_le_caratheodory
    (isMeasureOnRing_volume_leftOpenRing.isFinitelyAdditive isRingOfSets_leftOpenRing)
    isRingOfSets_leftOpenRing

/-- **Section 16.4.** Lebesgue outer measure, restricted to the Borel sets, is Mathlib's
Lebesgue measure. -/
theorem lebesgueOuter_toMeasure_eq_volume :
    lebesgueOuter.toMeasure ((BorelSpace.measurable_eq (α := ℝ)).le.trans
      borel_le_caratheodory_lebesgueOuter) = volume := by
  set ν := lebesgueOuter.toMeasure ((BorelSpace.measurable_eq (α := ℝ)).le.trans
    borel_le_caratheodory_lebesgueOuter) with hν
  have hIoc : ∀ a b : ℝ, ν (Ioc a b) = volume (Ioc a b) := fun a b => by
    rw [hν, toMeasure_apply _ _ measurableSet_Ioc]
    exact ringOuter_eq_of_mem isMeasureOnRing_volume_leftOpenRing isRingOfSets_leftOpenRing
      (Ioc_mem_leftOpenRing a b)
  have : IsLocallyFiniteMeasure ν := ⟨fun x => ⟨Ioo (x - 1) (x + 1),
    Ioo_mem_nhds (by linarith) (by linarith),
    lt_of_le_of_lt (measure_mono Ioo_subset_Ioc_self) (by
      rw [hIoc, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)⟩⟩
  exact Measure.ext_of_Ioc ν volume fun a b _ => hIoc a b

/-- **Section 16.4.** Lebesgue outer measure is the outer measure of Mathlib's Lebesgue
measure: $`\lambda^+(B)` is the value of {lit}`volume` on $`B`, for every set $`B`. -/
theorem lebesgueOuter_apply (B : Set ℝ) : lebesgueOuter B = volume B := by
  apply le_antisymm
  · obtain ⟨t, hBt, ht, hvol⟩ := exists_measurable_superset volume B
    rw [← hvol]
    conv_rhs => rw [← lebesgueOuter_toMeasure_eq_volume]
    rw [toMeasure_apply _ _ ht]
    exact measure_mono hBt
  · have : (volume : Measure ℝ).toOuterMeasure ≤ lebesgueOuter :=
      OuterMeasure.le_boundedBy.2 fun s => le_iInf fun _ => le_rfl
    exact this B

/-- **Section 16.4, in Mathlib's terms.** A set of reals is Lebesgue measurable in the sense of
the book (measurable for the outer measure) if and only if it is null-measurable for Mathlib's
Lebesgue measure, that is, measurable for its completion. -/
theorem lebesgueMeasurable_iff_nullMeasurableSet {B : Set ℝ} :
    LebesgueMeasurable B ↔ NullMeasurableSet B volume := by
  have hcar : ∀ {C : Set ℝ}, LebesgueMeasurable C ↔
      ∀ E : Set ℝ, volume E = volume (E ∩ C) + volume (E \ C) := by
    intro C
    simp only [LebesgueMeasurable, OuterMeasure.IsCaratheodory, lebesgueOuter_apply]
  have hborel : ∀ {C : Set ℝ}, MeasurableSet C → LebesgueMeasurable C := fun hC =>
    borel_le_caratheodory_lebesgueOuter _ ((BorelSpace.measurable_eq (α := ℝ)).le _ hC)
  have hnull : ∀ {C : Set ℝ}, volume C = 0 → LebesgueMeasurable C := fun hC =>
    isCaratheodory_of_null (by rw [lebesgueOuter_apply]; exact hC)
  constructor
  · intro hB
    have key : ∀ n : ℕ, NullMeasurableSet (B ∩ Ioc (-(n : ℝ)) n) volume := by
      intro n
      have hBn : LebesgueMeasurable (B ∩ Ioc (-(n : ℝ)) n) :=
        lebesgueOuter.isCaratheodory_inter hB (hborel measurableSet_Ioc)
      have hfin : volume (B ∩ Ioc (-(n : ℝ)) n) ≠ ∞ :=
        ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
          (measure_mono inter_subset_right)
      have h1 := hcar.1 hBn (toMeasurable volume (B ∩ Ioc (-(n : ℝ)) n))
      rw [inter_eq_right.2 (subset_toMeasurable _ _), measure_toMeasurable] at h1
      have h2 : volume (toMeasurable volume (B ∩ Ioc (-(n : ℝ)) n) \ (B ∩ Ioc (-(n : ℝ)) n))
          = 0 := by
        have : volume (B ∩ Ioc (-(n : ℝ)) n) + 0 = volume (B ∩ Ioc (-(n : ℝ)) n) +
            volume (toMeasurable volume (B ∩ Ioc (-(n : ℝ)) n) \ (B ∩ Ioc (-(n : ℝ)) n)) := by
          rw [add_zero]; exact h1
        exact ((ENNReal.add_right_inj hfin).1 this).symm
      have h3 : B ∩ Ioc (-(n : ℝ)) n = toMeasurable volume (B ∩ Ioc (-(n : ℝ)) n) \
          (toMeasurable volume (B ∩ Ioc (-(n : ℝ)) n) \ (B ∩ Ioc (-(n : ℝ)) n)) := by
        rw [Set.sdiff_sdiff_right_self, inter_eq_right.2 (subset_toMeasurable _ _)]
      rw [h3]
      exact (measurableSet_toMeasurable _ _).nullMeasurableSet.diff (NullMeasurableSet.of_null h2)
    have hBU : B = ⋃ n : ℕ, B ∩ Ioc (-(n : ℝ)) n := by
      rw [← inter_iUnion]
      refine (inter_eq_left.2 fun x _ => ?_).symm
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      exact mem_iUnion.2 ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    rw [hBU]
    exact NullMeasurableSet.iUnion key
  · intro hB
    obtain ⟨t, hBt, ht, hae⟩ := hB.exists_measurable_superset_ae_eq
    have h0 : volume (t \ B) = 0 := (ae_eq_set.1 hae).1
    have : B = t \ (t \ B) := by rw [Set.sdiff_sdiff_right_self, inter_eq_right.2 hBt]
    rw [this]
    exact lebesgueOuter.isCaratheodory_sdiff (hborel ht) (hnull h0)

/-- **Section 16.4, fact 1.** Lebesgue measure is the only measure on the Borel sets that
gives every open interval its length: a Borel measure with $`\nu((a, b)) = b - a` for all
$`a, b` is Lebesgue measure. -/
theorem eq_volume_of_forall_Ioo (ν : Measure ℝ)
    (h : ∀ a b : ℝ, ν (Ioo a b) = ENNReal.ofReal (b - a)) : ν = volume := by
  have : IsLocallyFiniteMeasure ν := ⟨fun x => ⟨Ioo (x - 1) (x + 1),
    Ioo_mem_nhds (by linarith) (by linarith), by rw [h]; exact ENNReal.ofReal_lt_top⟩⟩
  exact Real.measure_ext_Ioo_rat fun a b => by rw [h, Real.volume_Ioo]

/-- **Section 16.4, fact 2.** For a Lebesgue measurable set $`B` there are Borel sets
$`C \subseteq B \subseteq D` with $`\lambda(D - C) = 0`, and hence
$`\lambda(B) = \lambda(C) = \lambda(D)`. -/
theorem LebesgueMeasurable.exists_borel_between {B : Set ℝ} (hB : LebesgueMeasurable B) :
    ∃ C D : Set ℝ, MeasurableSet C ∧ MeasurableSet D ∧ C ⊆ B ∧ B ⊆ D ∧ volume (D \ C) = 0 ∧
      volume C = volume B ∧ volume D = volume B := by
  have hB' := lebesgueMeasurable_iff_nullMeasurableSet.1 hB
  obtain ⟨C, hCB, hC, hCae⟩ := hB'.exists_measurable_subset_ae_eq
  obtain ⟨D, hBD, hD, hDae⟩ := hB'.exists_measurable_superset_ae_eq
  exact ⟨C, D, hC, hD, hCB, hBD, (ae_eq_set.1 (hDae.trans hCae.symm)).1, measure_congr hCae,
    measure_congr hDae⟩

/-- **Section 16.4, fact 3.** A set $`B` of reals is Lebesgue measurable if for every
$`\varepsilon > 0` there are a closed set $`C_\varepsilon \subseteq B` and an open set
$`D_\varepsilon \supseteq B` with $`\lambda(D_\varepsilon - C_\varepsilon) < \varepsilon`. -/
theorem lebesgueMeasurable_of_forall_exists_closed_open {B : Set ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C D : Set ℝ, IsClosed C ∧ IsOpen D ∧ C ⊆ B ∧ B ⊆ D ∧
      volume (D \ C) < ENNReal.ofReal ε) : LebesgueMeasurable B := by
  rw [lebesgueMeasurable_iff_nullMeasurableSet]
  choose C D hC hD hCB hBD hvol using fun n : ℕ =>
    h (1 / ((n : ℝ) + 1)) (by positivity)
  have hnull : volume ((⋂ n, D n) \ ⋃ n, C n) = 0 := by
    have hle : ∀ n : ℕ, volume ((⋂ n, D n) \ ⋃ n, C n) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
      fun n => (measure_mono (sdiff_subset_sdiff (iInter_subset D n) (subset_iUnion C n))).trans
        (hvol n).le
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using this
    exact le_antisymm (ge_of_tendsto' hlim hle) zero_le
  have hBU : B = (⋃ n, C n) ∪ (B \ ⋃ n, C n) := by
    rw [union_sdiff_cancel (iUnion_subset hCB)]
  rw [hBU]
  exact (MeasurableSet.iUnion fun n => (hC n).measurableSet).nullMeasurableSet.union
    (NullMeasurableSet.of_null (measure_mono_null
      (sdiff_subset_sdiff_left (subset_iInter hBD)) hnull))

end Lebesgue

end Goldblatt
