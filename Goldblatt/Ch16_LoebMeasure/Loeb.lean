import Goldblatt.Ch16_LoebMeasure.Outer

/-!
# 16 (part 3). Loeb Measures and Approximability: Sections 16.5 to 16.7

This is the third of five parts of Chapter 16 (the overview is on the chapter page
{lit}`Goldblatt.Ch16_LoebMeasure`). It contains the measure theory of Loeb's construction:
the Loeb measure of an internal finitely additive measure, the two approximation lemmas, the
notion of approximability, and the characterisation of the Loeb measurable sets.

The arguments of these sections use the internal measure space in exactly three ways, each of
them an appeal to countable saturation (the book phrases the second and third through
sequential comprehensiveness and overflow). This part isolates the three consequences in a
structure and derives Sections 16.5 to 16.7 from it; part 4 shows that every internal finitely
additive measure on an internal ring in the ultrapower gives such a structure.
-/

universe u

namespace Goldblatt

open Set Filter MeasureTheory Function
open scoped ENNReal Topology

/-- An extended nonnegative real that is at most $`\tfrac1{n+1}` for every natural number
$`n` is zero. -/
theorem eq_zero_of_forall_le_one_div {x : ℝ≥0∞}
    (h : ∀ n : ℕ, x ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1))) : x = 0 := by
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using this
  exact le_antisymm (ge_of_tendsto' hlim h) zero_le

/-!
## 16.5 Loeb Measures

Let $`\mu` be an internal finitely additive function on an internal ring $`\mathcal A` of
subsets of an internal set, with values in the nonnegative hyperreals extended by
$`\infty`. Taking shadows gives a function $`\mu_L` on $`\mathcal A` with values in
$`[0, \infty]`, which is finitely additive, and which is in fact a measure on the ring because
a countable union of members of $`\mathcal A` that lies in $`\mathcal A` is a finite union
(Example 4 of Section 16.2). The outer measure of $`\mu_L` then yields a complete measure on a
sigma-algebra that includes $`\mathcal A`: the _Loeb measure_ of $`\mu`.
-/

/-- **Sections 16.2 (example 4) and 16.5.** The data from which a Loeb measure is built, after
shadows have been taken: a ring of subsets of $`T`, a finitely additive function $`\mu_L` on
it, and the three consequences of countable saturation on which the chapter rests.

* A countable union of members of the ring that belongs to the ring is a finite union
  (Section 16.1, example 6).
* An increasing sequence of members whose measures are bounded by $`r` lies inside a single
  member of measure at most $`r` (the overflow step in the proof of Lemma 16.5.1).
* If $`(C_n)` increases, $`(D_n)` decreases and every $`C_m` is included in every $`D_n`,
  then some member of the ring lies between all the $`C_n` and all the $`D_n` (the overflow
  step in the proof of Lemma 16.6.2).

The structure {lit}`Goldblatt.InternalMeasure.toLoebPremeasure` of part 4 shows that an
internal finitely additive measure on an internal ring has all these properties. -/
structure LoebPremeasure (T : Type u) where
  /-- The ring $`\mathcal A`. -/
  ring : Set (Set T)
  /-- The function $`\mu_L`, the shadow of the internal measure. -/
  μL : Set T → ℝ≥0∞
  /-- $`\mathcal A` is a ring of sets. -/
  isRing : IsRingOfSets ring
  /-- $`\mu_L` is finitely additive. -/
  isFinitelyAdditive : IsFinitelyAdditive ring μL
  /-- A countable union of members of the ring that is in the ring is a finite union. -/
  finite_union : ∀ ⦃A : ℕ → Set T⦄, (∀ n, A n ∈ ring) → ⋃ n, A n ∈ ring →
    ∃ k, ⋃ n, A n = ⋃ n ≤ k, A n
  /-- An increasing sequence of members of measure at most $`r` has an upper bound of measure
  at most $`r` in the ring. -/
  exists_upper : ∀ ⦃A : ℕ → Set T⦄ (r : ℝ≥0∞), (∀ n, A n ∈ ring) → Monotone A →
    (∀ n, μL (A n) ≤ r) → ∃ D ∈ ring, (∀ n, A n ⊆ D) ∧ μL D ≤ r
  /-- An increasing sequence lying below a decreasing sequence can be separated from it by a
  member of the ring. -/
  exists_between : ∀ ⦃C D : ℕ → Set T⦄, (∀ n, C n ∈ ring) → (∀ n, D n ∈ ring) → Monotone C →
    Antitone D → (∀ m n, C m ⊆ D n) → ∃ K ∈ ring, ∀ n, C n ⊆ K ∧ K ⊆ D n

namespace LoebPremeasure

variable {T : Type u} (P : LoebPremeasure T)

/-- **Section 16.2, examples 3 and 4.** $`\mu_L` is a measure on the ring $`\mathcal A`: it is
countably additive. If the union of a pairwise disjoint sequence of members of the ring is in
the ring, then it is the union of finitely many terms, the remaining terms are empty, and
countable additivity reduces to finite additivity. -/
theorem isMeasureOnRing : IsMeasureOnRing P.ring P.μL := by
  refine ⟨P.isFinitelyAdditive.empty, fun A hA hd hU => ?_⟩
  obtain ⟨k, hk⟩ := P.finite_union hA hU
  have hzero : ∀ m, k < m → A m = ∅ := by
    intro m hm
    by_contra hne
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
    have hx' : x ∈ ⋃ n ≤ k, A n := hk ▸ mem_iUnion.2 ⟨m, hx⟩
    simp only [mem_iUnion, exists_prop] at hx'
    obtain ⟨n, hn, hxn⟩ := hx'
    exact Set.disjoint_left.1 (hd (show n ≠ m by omega)) hxn hx
  have hU' : ⋃ n, A n = ⋃ n ∈ Finset.range (k + 1), A n := by
    rw [hk]; ext x; simp
  rw [hU', P.isFinitelyAdditive.biUnion_finset P.isRing _ (fun i _ => hA i)
      (fun i _ j _ hij => hd hij),
    tsum_eq_sum (s := Finset.range (k + 1)) (fun m hm => by
      rw [hzero m (by have := Finset.mem_range.not.1 hm; omega)]
      exact P.isFinitelyAdditive.empty)]

/-- **Section 16.5.** The outer measure $`\mu_L^+` on all subsets of $`T`. -/
noncomputable def outer : OuterMeasure T := ringOuter P.ring P.μL

/-- **Section 16.5.** $`\mu_L^+` agrees with $`\mu_L` on the ring. -/
theorem outer_eq_of_mem {A : Set T} (hA : A ∈ P.ring) : P.outer A = P.μL A :=
  ringOuter_eq_of_mem P.isMeasureOnRing P.isRing hA

/-- **Section 16.5.** A subset of $`T` is _Loeb measurable_ (with respect to the internal
measure) if it is $`\mu_L^+`-measurable. -/
def LoebMeasurable (B : Set T) : Prop := P.outer.IsCaratheodory B

/-- **Section 16.5.** The sigma-algebra $`\mathcal A(\mu_L)` of Loeb measurable sets, as a
Mathlib measurable space. -/
@[instance_reducible] noncomputable def loebSpace : MeasurableSpace T := P.outer.caratheodory

/-- **Section 16.5.** The _Loeb measure_ $`\mu_L` determined by the internal measure: the
restriction of $`\mu_L^+` to the Loeb measurable sets, as a Mathlib measure on the Loeb
sigma-algebra. -/
noncomputable def loebMeasure : @Measure T P.loebSpace := caratheodoryMeasure P.outer

/-- **Section 16.5.** The Loeb measurable sets are the measurable sets of the Loeb
sigma-algebra. -/
theorem measurableSet_loebSpace_iff {B : Set T} :
    MeasurableSet[P.loebSpace] B ↔ P.LoebMeasurable B := Iff.rfl

/-- **Section 16.5.** The Loeb measure of a Loeb measurable set is its outer measure. -/
theorem loebMeasure_apply {B : Set T} (hB : P.LoebMeasurable B) :
    P.loebMeasure B = P.outer B :=
  caratheodoryMeasure_apply P.outer hB

/-- **Section 16.5.** Every member of the ring $`\mathcal A` is Loeb measurable. -/
theorem loebMeasurable_of_mem {A : Set T} (hA : A ∈ P.ring) : P.LoebMeasurable A :=
  isCaratheodory_of_mem P.isFinitelyAdditive P.isRing hA

/-- **Section 16.5.** The Loeb measure extends $`\mu_L` from the ring. -/
theorem loebMeasure_of_mem {A : Set T} (hA : A ∈ P.ring) : P.loebMeasure A = P.μL A := by
  rw [P.loebMeasure_apply (P.loebMeasurable_of_mem hA), P.outer_eq_of_mem hA]

/-- **Section 16.5.** The Loeb sigma-algebra includes the sigma-algebra generated by the
ring. -/
theorem generateFrom_le_loebSpace : MeasurableSpace.generateFrom P.ring ≤ P.loebSpace :=
  generateFrom_le_caratheodory P.isFinitelyAdditive P.isRing

/-- **Section 16.5.** The Loeb measure is complete: every subset of a Loeb measurable set of
measure zero is Loeb measurable. -/
theorem isComplete_loebMeasure : @Measure.IsComplete T P.loebSpace P.loebMeasure :=
  isComplete_caratheodoryMeasure P.outer

/-- **Section 16.5.** A set of outer measure zero is Loeb measurable. -/
theorem loebMeasurable_of_null {B : Set T} (hB : P.outer B = 0) : P.LoebMeasurable B :=
  isCaratheodory_of_null hB

/-- **Section 16.5.** The Loeb measurable sets are closed under intersections. -/
theorem LoebMeasurable.inter {P : LoebPremeasure T} {A B : Set T} (hA : P.LoebMeasurable A)
    (hB : P.LoebMeasurable B) : P.LoebMeasurable (A ∩ B) :=
  P.outer.isCaratheodory_inter hA hB

/-- **Section 16.5.** The Loeb measurable sets are closed under unions. -/
theorem LoebMeasurable.union {P : LoebPremeasure T} {A B : Set T} (hA : P.LoebMeasurable A)
    (hB : P.LoebMeasurable B) : P.LoebMeasurable (A ∪ B) :=
  P.outer.isCaratheodory_union hA hB

/-- **Section 16.5.** The Loeb measurable sets are closed under differences. -/
theorem LoebMeasurable.diff {P : LoebPremeasure T} {A B : Set T} (hA : P.LoebMeasurable A)
    (hB : P.LoebMeasurable B) : P.LoebMeasurable (A \ B) :=
  P.outer.isCaratheodory_sdiff hA hB

/-- **Section 16.5.** The Loeb measurable sets are closed under countable unions. -/
theorem LoebMeasurable.iUnion {P : LoebPremeasure T} {A : ℕ → Set T}
    (hA : ∀ n, P.LoebMeasurable (A n)) : P.LoebMeasurable (⋃ n, A n) :=
  P.outer.isCaratheodory_iUnion hA

/-- **Lemma 16.5.1**, the approximation step: a set $`B` is included in a member of the ring
whose measure exceeds $`\mu_L^+(B)` by at most $`\varepsilon`. An increasing sequence of
members of the ring that covers $`B` with total outer measure at most
$`\mu_L^+(B) + \varepsilon` is bounded above by a single member of the ring of measure at most
$`\mu_L^+(B) + \varepsilon`: this is where saturation enters. -/
theorem exists_superset_le_add {B : Set T} (hB : P.outer B ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ D ∈ P.ring, B ⊆ D ∧ P.μL D ≤ P.outer B + ε := by
  obtain ⟨A, hA, hmono, hBA, hle⟩ :=
    exists_monotone_cover P.isRing P.isFinitelyAdditive.empty hB hε
  obtain ⟨D, hD, hAD, hDle⟩ := P.exists_upper (P.outer B + ε) hA hmono fun n =>
    (P.outer_eq_of_mem (hA n)).symm.le.trans ((measure_mono (subset_iUnion A n)).trans hle)
  exact ⟨D, hD, hBA.trans (iUnion_subset hAD), hDle⟩

/-- **Lemma 16.5.1.** The outer measure of a set is the infimum of the measures of the members
of the ring that include it: $`\mu_L^+(B) = \inf \{\mu_L(A) : B \subseteq A \in \mathcal A\}`.
The book states this for Loeb measurable $`B`; the proof does not use measurability. -/
theorem outer_eq_iInf (B : Set T) :
    P.outer B = ⨅ (A : Set T) (_ : A ∈ P.ring) (_ : B ⊆ A), P.μL A := by
  apply le_antisymm
  · exact le_iInf fun A => le_iInf fun hA => le_iInf fun hBA =>
      (measure_mono hBA).trans_eq (P.outer_eq_of_mem hA)
  · by_cases hB : P.outer B = ∞
    · rw [hB]; exact le_top
    · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      obtain ⟨D, hD, hBD, hle⟩ :=
        P.exists_superset_le_add hB (ε := ε) (by exact_mod_cast hε.ne')
      exact iInf_le_of_le D (iInf_le_of_le hD (iInf_le_of_le hBD hle))

/-- **Lemma 16.5.1**, in the book's formulation: if $`B` is Loeb measurable, then
$`\mu_L(B) = \inf \{\mu_L(A) : B \subseteq A \in \mathcal A\}`. -/
theorem loebMeasure_eq_iInf {B : Set T} (hB : P.LoebMeasurable B) :
    P.loebMeasure B = ⨅ (A : Set T) (_ : A ∈ P.ring) (_ : B ⊆ A), P.μL A := by
  rw [P.loebMeasure_apply hB, P.outer_eq_iInf]

/-- **Lemma 16.5.2**, the approximation step: a Loeb measurable set $`B` of finite measure
includes a member of the ring whose measure is within $`\varepsilon` of that of $`B`. The proof
is the book's: take $`D \supseteq B` in the ring of finite measure, approximate $`D - B` from
outside by $`C \subseteq D`, and use $`D - C`. -/
theorem exists_subset_le_add {B : Set T} (hB : P.LoebMeasurable B) (hfin : P.outer B ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ A ∈ P.ring, A ⊆ B ∧ P.outer B ≤ P.μL A + ε := by
  obtain ⟨D, hD, hBD, hDle⟩ := P.exists_superset_le_add hfin one_ne_zero
  have hDfin : P.outer D ≠ ∞ := by
    rw [P.outer_eq_of_mem hD]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.one_ne_top⟩) hDle
  have hDBfin : P.outer (D \ B) ≠ ∞ := ne_top_of_le_ne_top hDfin (measure_mono sdiff_subset)
  obtain ⟨C, hC, hDBC, hCle⟩ := P.exists_superset_le_add hDBfin hε
  have hC' : C ∩ D ∈ P.ring := P.isRing.inter_mem hC hD
  have hA : D \ (C ∩ D) ∈ P.ring := P.isRing.diff_mem hD hC'
  have hAB : D \ (C ∩ D) ⊆ B := by
    intro x hx
    by_contra hxB
    exact hx.2 ⟨hDBC ⟨hx.1, hxB⟩, hx.1⟩
  refine ⟨D \ (C ∩ D), hA, hAB, ?_⟩
  have h1 : P.outer (C ∩ D) = P.outer (C ∩ D ∩ B) + P.outer ((C ∩ D) \ B) := hB (C ∩ D)
  have h2 : P.outer (C ∩ D) ≤ P.outer (D \ B) + ε := by
    rw [P.outer_eq_of_mem hC']
    exact (P.isFinitelyAdditive.mono P.isRing hC' hC inter_subset_left).trans hCle
  have h3 : P.outer (D \ B) ≤ P.outer ((C ∩ D) \ B) :=
    measure_mono fun x hx => ⟨⟨hDBC hx, hx.1⟩, hx.2⟩
  have h4 : P.outer (C ∩ D ∩ B) ≤ ε := by
    have : P.outer (C ∩ D ∩ B) + P.outer (D \ B) ≤ ε + P.outer (D \ B) :=
      calc P.outer (C ∩ D ∩ B) + P.outer (D \ B)
          ≤ P.outer (C ∩ D ∩ B) + P.outer ((C ∩ D) \ B) := by gcongr
        _ = P.outer (C ∩ D) := h1.symm
        _ ≤ P.outer (D \ B) + ε := h2
        _ = ε + P.outer (D \ B) := add_comm _ _
    exact (ENNReal.add_le_add_iff_right hDBfin).1 this
  have h5 : B ⊆ D \ (C ∩ D) ∪ (C ∩ D ∩ B) := by
    intro x hx
    by_cases hxC : x ∈ C ∩ D
    · exact Or.inr ⟨hxC, hx⟩
    · exact Or.inl ⟨hBD hx, hxC⟩
  calc P.outer B ≤ P.outer (D \ (C ∩ D) ∪ (C ∩ D ∩ B)) := measure_mono h5
    _ ≤ P.outer (D \ (C ∩ D)) + P.outer (C ∩ D ∩ B) := measure_union_le _ _
    _ ≤ P.μL (D \ (C ∩ D)) + ε := by
      rw [P.outer_eq_of_mem hA]; gcongr

/-- **Lemma 16.5.2.** If $`B` is Loeb measurable and of finite Loeb measure, then
$`\mu_L(B) = \sup \{\mu_L(A) : A \subseteq B,\ A \in \mathcal A\}`. -/
theorem outer_eq_iSup {B : Set T} (hB : P.LoebMeasurable B) (hfin : P.outer B ≠ ∞) :
    P.outer B = ⨆ (A : Set T) (_ : A ∈ P.ring) (_ : A ⊆ B), P.μL A := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨A, hA, hAB, hle⟩ :=
      P.exists_subset_le_add hB hfin (ε := ε) (by exact_mod_cast hε.ne')
    refine hle.trans ?_
    gcongr
    exact le_iSup_of_le A (le_iSup_of_le hA (le_iSup_of_le hAB le_rfl))
  · exact iSup_le fun A => iSup_le fun hA => iSup_le fun hAB =>
      (P.outer_eq_of_mem hA).symm.le.trans (measure_mono hAB)

/-- **Lemma 16.5.2**, for the Loeb measure. -/
theorem loebMeasure_eq_iSup {B : Set T} (hB : P.LoebMeasurable B)
    (hfin : P.loebMeasure B ≠ ∞) :
    P.loebMeasure B = ⨆ (A : Set T) (_ : A ∈ P.ring) (_ : A ⊆ B), P.μL A := by
  rw [P.loebMeasure_apply hB] at hfin ⊢
  exact P.outer_eq_iSup hB hfin

/-!
## 16.6 Approximability

A subset $`B` of $`T` is _approximable_ if it can be squeezed between two members of the ring
whose difference has arbitrarily small measure. For sets of finite outer measure this is the
same as Loeb measurability. The definition here is the book's second formulation, in terms of
$`\mu_L`; part 4 proves that it is equivalent to the first, in terms of the internal measure
itself.
-/

/-- **Section 16.6.** A set $`B` is $`\mu`-_approximable_ if for every real
$`\varepsilon > 0` there are $`C_\varepsilon, D_\varepsilon \in \mathcal A` with
$`C_\varepsilon \subseteq B \subseteq D_\varepsilon` and
$`\mu_L(D_\varepsilon - C_\varepsilon) < \varepsilon`. -/
def Approximable (B : Set T) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C ∈ P.ring, ∃ D ∈ P.ring, C ⊆ B ∧ B ⊆ D ∧
    P.μL (D \ C) < ENNReal.ofReal ε

/-- **Lemma 16.6.1.** A Loeb measurable set of finite Loeb measure is approximable. -/
theorem LoebMeasurable.approximable {P : LoebPremeasure T} {B : Set T}
    (hB : P.LoebMeasurable B) (hfin : P.outer B ≠ ∞) : P.Approximable B := by
  intro ε hε
  have hδ : ENNReal.ofReal (ε / 4) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  obtain ⟨D, hD, hBD, hDle⟩ := P.exists_superset_le_add hfin hδ
  obtain ⟨C, hC, hCB, hCle⟩ := P.exists_subset_le_add hB hfin hδ
  refine ⟨C, hC, D, hD, hCB, hBD, ?_⟩
  have hCD : C ⊆ D := hCB.trans hBD
  have hCfin : P.μL C ≠ ∞ := by
    rw [← P.outer_eq_of_mem hC]
    exact ne_top_of_le_ne_top hfin (measure_mono hCB)
  have hadd : P.μL (D \ C) + P.μL C = P.μL D := by
    have := P.isFinitelyAdditive.union hC (P.isRing.diff_mem hD hC) disjoint_sdiff_right
    rw [union_sdiff_cancel hCD] at this
    rw [this, add_comm]
  have hle : P.μL (D \ C) + P.μL C ≤
      ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + P.μL C :=
    calc P.μL (D \ C) + P.μL C = P.μL D := hadd
      _ ≤ P.outer B + ENNReal.ofReal (ε / 4) := hDle
      _ ≤ P.μL C + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by gcongr
      _ = ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + P.μL C := by ring
  refine lt_of_le_of_lt ((ENNReal.add_le_add_iff_right hCfin).1 hle) ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_lt_ofReal_iff hε]
  linarith

/-- **Lemma 16.6.2.** If $`B` is approximable, then some member $`A` of the ring is almost
equal to $`B`: the symmetric difference of $`A` and $`B` has outer measure zero. The inner
approximations are made increasing and the outer ones decreasing, and saturation gives a member
of the ring between all of them. -/
theorem Approximable.exists_symmDiff_null {P : LoebPremeasure T} {B : Set T}
    (hB : P.Approximable B) : ∃ A ∈ P.ring, P.outer (symmDiff A B) = 0 := by
  choose C' hC' D' hD' hCB hBD hlt using fun n : ℕ =>
    hB (1 / ((n : ℝ) + 1)) (by positivity)
  have hC : ∀ n, ⋃ i ≤ n, C' i ∈ P.ring := P.isRing.biUnion_le_mem hC'
  have hD : ∀ n, ⋂ i ≤ n, D' i ∈ P.ring := P.isRing.biInter_le_mem hD'
  have hCsub : ∀ n, ⋃ i ≤ n, C' i ⊆ B := fun n => iUnion₂_subset fun i _ => hCB i
  have hDsup : ∀ n, B ⊆ ⋂ i ≤ n, D' i := fun n => subset_iInter₂ fun i _ => hBD i
  obtain ⟨K, hK, hKb⟩ := P.exists_between hC hD
    (fun m n hmn x hx => by
      simp only [mem_iUnion, exists_prop] at hx ⊢
      obtain ⟨i, hi, hx⟩ := hx
      exact ⟨i, hi.trans hmn, hx⟩)
    (fun m n hmn x hx => by
      simp only [mem_iInter] at hx ⊢
      exact fun i hi => hx i (hi.trans hmn))
    (fun m n => (hCsub m).trans (hDsup n))
  refine ⟨K, hK, eq_zero_of_forall_le_one_div fun n => ?_⟩
  have hsub : symmDiff K B ⊆ D' n \ C' n := by
    have h1 : C' n ⊆ ⋃ i ≤ n, C' i := fun x hx => mem_iUnion₂.2 ⟨n, le_rfl, hx⟩
    have h2 : ⋂ i ≤ n, D' i ⊆ D' n := fun x hx => mem_iInter₂.1 hx n le_rfl
    rintro x (⟨hxK, hxB⟩ | ⟨hxB, hxK⟩)
    · exact ⟨h2 ((hKb n).2 hxK), fun hxC => hxB (hCB n hxC)⟩
    · exact ⟨hBD n hxB, fun hxC => hxK ((hKb n).1 (h1 hxC))⟩
  calc P.outer (symmDiff K B) ≤ P.outer (D' n \ C' n) := measure_mono hsub
    _ = P.μL (D' n \ C' n) := P.outer_eq_of_mem (P.isRing.diff_mem (hD' n) (hC' n))
    _ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := (hlt n).le

/-- **Lemma 16.6.3.** An approximable set is Loeb measurable. By Lemma 16.6.2 it differs from
a member $`A` of the ring by a set of outer measure zero; since $`A` and all null sets are
measurable, so is $`B = (A \cup (B - A)) - (A - B)`. (The book verifies the splitting condition
by hand.) -/
theorem Approximable.loebMeasurable {P : LoebPremeasure T} {B : Set T}
    (hB : P.Approximable B) : P.LoebMeasurable B := by
  obtain ⟨A, hA, hnull⟩ := hB.exists_symmDiff_null
  have h1 : P.LoebMeasurable (B \ A) :=
    P.loebMeasurable_of_null (measure_mono_null (fun x hx => Or.inr hx) hnull)
  have h2 : P.LoebMeasurable (A \ B) :=
    P.loebMeasurable_of_null (measure_mono_null (fun x hx => Or.inl hx) hnull)
  have : B = (A ∪ B \ A) \ (A \ B) := by
    ext x
    simp only [mem_union, Set.mem_sdiff]
    tauto
  rw [this]
  exact ((P.loebMeasurable_of_mem hA).union h1).diff h2

/-- **Lemma 16.6.4.** A set of finite outer measure is Loeb measurable if and only if it is
approximable. -/
theorem loebMeasurable_iff_approximable {B : Set T} (hfin : P.outer B ≠ ∞) :
    P.LoebMeasurable B ↔ P.Approximable B :=
  ⟨fun h => h.approximable hfin, fun h => h.loebMeasurable⟩

/-!
## 16.7 Loeb Measure as Approximability

The lemmas of the last section give a description of the Loeb measurable sets that does not
mention the outer measure: a set is Loeb measurable exactly when its intersection with every
member of the ring of finite measure is approximable. Together with Lemma 16.5.1 for the value
of the measure, this could serve as a direct definition of the Loeb measure space.
-/

/-- **Theorem 16.7.1.** A subset $`B` of $`T` is Loeb measurable if and only if $`B \cap A` is
approximable for every $`A` in the ring with $`\mu_L(A) < \infty`. -/
theorem loebMeasurable_iff_forall_approximable {B : Set T} :
    P.LoebMeasurable B ↔ ∀ A ∈ P.ring, P.μL A ≠ ∞ → P.Approximable (B ∩ A) := by
  constructor
  · intro hB A hA hfin
    refine (hB.inter (P.loebMeasurable_of_mem hA)).approximable ?_
    exact ne_top_of_le_ne_top (by rwa [P.outer_eq_of_mem hA]) (measure_mono inter_subset_right)
  · intro h
    refine isCaratheodory_of_forall_ne_top fun E hE => ?_
    have hEB : P.outer (E ∩ B) ≠ ∞ := ne_top_of_le_ne_top hE (measure_mono inter_subset_left)
    obtain ⟨A, hA, hAfin, hcov⟩ :=
      exists_finite_cover P.isRing P.isFinitelyAdditive.empty hEB
    have hG : P.LoebMeasurable (⋃ n, B ∩ A n) :=
      LoebMeasurable.iUnion fun n => (h (A n) (hA n) (hAfin n)).loebMeasurable
    have h1 : E ∩ ⋃ n, B ∩ A n = E ∩ B := by
      ext x
      simp only [mem_inter_iff, mem_iUnion]
      constructor
      · rintro ⟨hxE, n, hxB, -⟩
        exact ⟨hxE, hxB⟩
      · rintro ⟨hxE, hxB⟩
        obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov ⟨hxE, hxB⟩)
        exact ⟨hxE, n, hxB, hn⟩
    have h2 : E \ ⋃ n, B ∩ A n = E \ B := by
      rw [← sdiff_inter_self_eq_sdiff, inter_comm, h1, inter_comm, sdiff_inter_self_eq_sdiff]
    have := hG E
    rw [h1, h2] at this
    exact this.ge

end LoebPremeasure

end Goldblatt
