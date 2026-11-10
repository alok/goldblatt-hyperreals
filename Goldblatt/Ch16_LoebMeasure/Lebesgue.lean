import Goldblatt.Ch16_LoebMeasure.Internal

/-!
# 16 (part 5). Lebesgue Measure via Loeb Measure: Section 16.8

This is the last of five parts of Chapter 16 (the overview is on the chapter page
{lit}`Goldblatt.Ch16_LoebMeasure`). For an unlimited hypernatural $`N`, the hyperfinite grid
of the points $`k/N` with $`|k| \le N^2` carries the internal counting measure that gives
each point the infinitesimal weight $`1/N`. Its Loeb measure represents Lebesgue measure: a
set $`B` of reals is Lebesgue measurable exactly when the set of grid points infinitely close
to points of $`B` is Loeb measurable, and then the two measures agree.

A hypernatural is the class of a sequence $`(\nu_n)` of natural numbers (Section 5.10), and
the construction is carried out in terms of such a sequence: the grid is the internal set of
the finite grids for the $`\nu_n`.
-/

namespace Goldblatt

open Set Filter MeasureTheory Function Ultrapower
open scoped ENNReal Topology Hyperreal

/-!
## 16.8 Lebesgue Measure via Loeb Measure

The first step counts the grid points in a real interval: for the standard grid of mesh
$`1/N` the number of points in $`(a, b)` differs from $`(b - a)N` by at most one, so the
normalised count tends to $`b - a` along the index ultrafilter when $`N` is unlimited
(Theorem 16.8.1). The inverse shadow then transports the Loeb measure to a measure on the
Borel sets of the real line which gives intervals their length and is therefore Lebesgue
measure (Lemma 16.8.3), and approximation of Loeb measurable sets by internal sets, whose
shadows are closed, gives the converse (Theorem 16.8.2).
-/

section FiniteGrid

/-- **Section 16.8.** The finite grid of mesh $`1/N`: the points $`k/N` for integers $`k`
with $`|k| \le N^2`. -/
noncomputable def gridFinset (N : ℕ) : Finset ℝ :=
  (Finset.Icc (-((N : ℤ) ^ 2)) ((N : ℤ) ^ 2)).image fun k : ℤ => (k : ℝ) / N

theorem mem_gridFinset {N : ℕ} {x : ℝ} :
    x ∈ gridFinset N ↔ ∃ k : ℤ, |k| ≤ (N : ℤ) ^ 2 ∧ x = (k : ℝ) / N := by
  simp only [gridFinset, Finset.mem_image, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

/-- The grid points in a real interval $`(a, b)` with $`|a|, |b| < N` are the points $`k/N`
for the integers $`k` strictly between $`aN` and $`bN`. -/
theorem coe_gridFinset_inter_Ioo {N : ℕ} (hN : 0 < N) {a b : ℝ} (ha : |a| < N) (hb : |b| < N) :
    (↑(gridFinset N) ∩ Ioo a b : Set ℝ) =
      (fun k : ℤ => (k : ℝ) / N) '' ↑(Finset.Ioo ⌊a * N⌋ ⌈b * N⌉) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  ext x
  simp only [mem_inter_iff, Finset.mem_coe, mem_gridFinset, mem_Ioo, mem_image, Finset.mem_Ioo,
    Int.floor_lt, Int.lt_ceil]
  constructor
  · rintro ⟨⟨k, -, rfl⟩, h1, h2⟩
    exact ⟨k, ⟨(lt_div_iff₀ hN').1 h1, (div_lt_iff₀ hN').1 h2⟩, rfl⟩
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨k, ?_, rfl⟩, (lt_div_iff₀ hN').2 h1, (div_lt_iff₀ hN').2 h2⟩
    have h3 : -((N : ℝ) ^ 2) < (k : ℝ) := by nlinarith [(abs_lt.1 ha).1]
    have h4 : (k : ℝ) < (N : ℝ) ^ 2 := by nlinarith [(abs_lt.1 hb).2]
    rw [abs_le]
    exact ⟨by exact_mod_cast h3.le, by exact_mod_cast h4.le⟩

/-- The number of grid points in $`(a, b)`. -/
theorem ncard_gridFinset_inter_Ioo {N : ℕ} (hN : 0 < N) {a b : ℝ} (ha : |a| < N)
    (hb : |b| < N) :
    (↑(gridFinset N) ∩ Ioo a b : Set ℝ).ncard = (⌈b * N⌉ - ⌊a * N⌋ - 1).toNat := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [coe_gridFinset_inter_Ioo hN ha hb, Set.ncard_image_of_injective _ (fun k l hkl => by
    have := (div_left_inj' hN').1 hkl
    exact_mod_cast this), Set.ncard_coe_finset, Int.card_Ioo]

/-- **Theorem 16.8.1, the count.** The number of grid points in $`(a, b)` differs from
$`(b - a)N` by at most one. -/
theorem abs_ncard_gridFinset_inter_Ioo_sub_le {N : ℕ} (hN : 0 < N) {a b : ℝ} (hab : a ≤ b)
    (ha : |a| < N) (hb : |b| < N) :
    |((↑(gridFinset N) ∩ Ioo a b : Set ℝ).ncard : ℝ) - (b - a) * N| ≤ 1 := by
  rw [ncard_gridFinset_inter_Ioo hN ha hb]
  have h1 := Int.le_ceil (b * N)
  have h2 := Int.ceil_lt_add_one (b * N)
  have h3 := Int.floor_le (a * N)
  have h4 := Int.lt_floor_add_one (a * N)
  have e : (b - a) * N = b * N - a * N := by ring
  rcases le_or_gt 0 (⌈b * N⌉ - ⌊a * N⌋ - 1) with h | h
  · have hc : (((⌈b * N⌉ - ⌊a * N⌋ - 1).toNat : ℕ) : ℝ) = (⌈b * N⌉ : ℝ) - ⌊a * N⌋ - 1 := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
      push_cast
      ring
    rw [hc, e, abs_le]
    constructor <;> linarith
  · have hz : (⌈b * N⌉ - ⌊a * N⌋ - 1).toNat = 0 := Int.toNat_of_nonpos h.le
    have h' : ((⌈b * N⌉ : ℝ) - ⌊a * N⌋ - 1) < 0 := by exact_mod_cast h
    have hN' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hnn : 0 ≤ (b - a) * N := mul_nonneg (sub_nonneg.2 hab) hN'
    rw [hz, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hnn, e]
    linarith

end FiniteGrid

section Grid

variable (ν : ℕ → ℕ)

/-- **Section 16.8.** The hyperfinite grid $`S = \{k/N : k \in {}^*\mathbb Z,\ |k| \le N^2\}`
for the hypernatural $`N = [\nu_n]`: the internal set of the finite grids of mesh
$`1/\nu_n`. -/
def hyperGrid : Set ℝ* := internalSet fun n => (gridFinset (ν n) : Set ℝ)

/-- **Section 16.8.** The grid is a hyperfinite set. -/
theorem isHyperfinite_hyperGrid : IsHyperfinite (hyperGrid ν) :=
  isHyperfiniteSet_internalSet_finset _

/-- **Section 16.8.** The grid is the set of the hyperreals $`k/N` for hyperintegers $`k` with
$`|k| \le N^2`, where $`N = [\nu_n]`. -/
theorem mem_hyperGrid_iff {x : ℝ*} :
    x ∈ hyperGrid ν ↔ ∃ k ∈ ℤ*, |k| ≤ hnat ν ^ 2 ∧ x = k / hnat ν := by
  classical
  constructor
  · intro hx
    obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
    have hr := hyperreal_ofSeq_mem_internalSet.1 hx
    let κ : ℕ → ℤ := fun n =>
      if h : ∃ k : ℤ, |k| ≤ (ν n : ℤ) ^ 2 ∧ r n = (k : ℝ) / ν n then h.choose else 0
    have hκ : ∀ᶠ n in hyperfilter ℕ, |κ n| ≤ (ν n : ℤ) ^ 2 ∧ r n = (κ n : ℝ) / ν n := by
      filter_upwards [hr] with n hn
      have h := mem_gridFinset.1 (Finset.mem_coe.1 hn)
      have hk : κ n = h.choose := dite_eq_left_of_eq_true (eq_true h)
      rw [hk]
      exact h.choose_spec
    refine ⟨hint κ, hint_mem_hyperInt κ, ?_, ?_⟩
    · change Hyperreal.ofSeq (fun n => |(κ n : ℝ)|) ≤ Hyperreal.ofSeq fun n => (ν n : ℝ) ^ 2
      rw [ofSeq_le_ofSeq_iff]
      filter_upwards [hκ] with n hn
      exact_mod_cast hn.1
    · change Hyperreal.ofSeq r = Hyperreal.ofSeq fun n => (κ n : ℝ) / (ν n : ℝ)
      rw [ofSeq_eq_ofSeq_iff]
      exact hκ.mono fun n hn => hn.2
  · rintro ⟨k, hk, hle, rfl⟩
    obtain ⟨κ, rfl⟩ := exists_hint_eq hk
    have hle' : Hyperreal.ofSeq (fun n => |(κ n : ℝ)|) ≤
        Hyperreal.ofSeq fun n => (ν n : ℝ) ^ 2 := hle
    rw [ofSeq_le_ofSeq_iff] at hle'
    change Hyperreal.ofSeq (fun n => (κ n : ℝ) / (ν n : ℝ)) ∈ _
    refine hyperreal_ofSeq_mem_internalSet.2 ?_
    filter_upwards [hle'] with n hn
    exact Finset.mem_coe.2 (mem_gridFinset.2 ⟨κ n, by exact_mod_cast hn, rfl⟩)

/-- **Section 16.8.** The internal measure $`\mu(A) = |A|/N` on the algebra of internal
subsets of the grid: the weighted counting function that gives each grid point the weight
$`1/N`. -/
noncomputable def gridMeasure : InternalMeasure ℝ :=
  InternalMeasure.weighted (fun n => gridFinset (ν n)) fun n _ => ((ν n : ℕ) : ℝ≥0∞)⁻¹

/-- **Section 16.8.** The Loeb measure space $`(S, \mathcal A(\mu_L), \mu_L)` of the grid. -/
noncomputable def gridLoeb : LoebPremeasure ℝ* := (gridMeasure ν).toLoebPremeasure

theorem gridMeasure_m (n : ℕ) (B : Set ℝ) :
    (gridMeasure ν).m n B =
      ((↑(gridFinset (ν n)) ∩ B : Set ℝ).ncard : ℝ≥0∞) * ((ν n : ℕ) : ℝ≥0∞)⁻¹ :=
  sum_indicator_const (gridFinset (ν n)) B (((ν n : ℕ) : ℝ≥0∞)⁻¹)

/-- **Section 16.8.** The ring of the grid measure is the algebra $`\mathcal P_I(S)` of all
internal subsets of the grid. -/
theorem mem_gridLoeb_ring_iff {X : Set ℝ*} :
    X ∈ (gridLoeb ν).ring ↔ IsInternal X ∧ X ⊆ hyperGrid ν :=
  InternalMeasure.mem_sets_weighted_iff

/-- The grid itself belongs to the ring. -/
theorem hyperGrid_mem_ring : hyperGrid ν ∈ (gridLoeb ν).ring :=
  InternalMeasure.internalSet_mem_sets_weighted _ _

variable {ν}

/-- If $`N = [\nu_n]` is unlimited then $`\nu_n` exceeds any given natural number for almost
all $`n`. -/
theorem eventually_lt_of_unlimited_hnat (hν : Unlimited (hnat ν)) (M : ℕ) :
    ∀ᶠ n in hyperfilter ℕ, M < ν n := by
  have h1 := unlimited_iff_forall_nat.1 hν M
  rw [abs_of_nonneg (hyperNat_nonneg (hnat_mem_hyperNat ν))] at h1
  have h2 : Hyperreal.ofSeq (fun _ => (M : ℝ)) < Hyperreal.ofSeq fun n => (ν n : ℝ) := h1
  rw [ofSeq_lt_ofSeq_iff] at h2
  exact h2.mono fun n hn => by exact_mod_cast hn

/-- **Section 16.8.** The internal measure of an internal subset $`A` of the grid is
$`\mu(A) = |A|/N`, the internal cardinality of $`A` divided by $`N`. -/
theorem gridMeasure_μ_eq (hν : Unlimited (hnat ν)) {X : Set ℝ*} (hX : X ∈ (gridLoeb ν).ring) :
    (gridMeasure ν).μ X = hyperENNRealOfHyperreal (hcard X / hnat ν) := by
  obtain ⟨B, rfl, hB⟩ := hX
  rw [InternalMeasure.μ_internalSet, hcard, internalCard_internalSet]
  change _ = Germ.ofFun fun n => ENNReal.ofReal (((B n).ncard : ℝ) / (ν n : ℝ))
  refine Germ.coe_eq.2 ?_
  filter_upwards [hB, eventually_lt_of_unlimited_hnat hν 0] with n hn hpos
  have hpos' : (0 : ℝ) < ν n := by exact_mod_cast hpos
  rw [gridMeasure_m, inter_eq_right.2 hn, ENNReal.ofReal_div_of_pos hpos', ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, div_eq_mul_inv]

/-- The grid points in the hyperreal interval with real end points $`a, b`, as an internal
set. -/
theorem hyperGrid_inter_Ioo (ν : ℕ → ℕ) (a b : ℝ) :
    hyperGrid ν ∩ Ioo (a : ℝ*) b =
      internalSet fun n => (↑(gridFinset (ν n)) ∩ Ioo a b : Set ℝ) := by
  change hyperGrid ν ∩ Ioo (Hyperreal.ofSeq fun _ => a) (Hyperreal.ofSeq fun _ => b) = _
  rw [← internalSet_Ioo, hyperGrid, internalSet_inter]

/-- The set of grid points in a real interval is internal, so it belongs to the ring. -/
theorem hyperGrid_inter_Ioo_mem_ring (ν : ℕ → ℕ) (a b : ℝ) :
    hyperGrid ν ∩ Ioo (a : ℝ*) b ∈ (gridLoeb ν).ring := by
  rw [hyperGrid_inter_Ioo]
  exact ⟨_, rfl, Eventually.of_forall fun n => inter_subset_left⟩

/-- **Theorem 16.8.1, the limit.** The normalised number of points of the $`n`-th grid in
$`(a, b)` tends to $`b - a` along the index ultrafilter. -/
theorem tendsto_gridMeasure_Ioo (hν : Unlimited (hnat ν)) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => (gridMeasure ν).m n (↑(gridFinset (ν n)) ∩ Ioo a b)) (hyperfilter ℕ)
      (𝓝 (ENNReal.ofReal (b - a))) := by
  have hreal : Tendsto
      (fun n => ((↑(gridFinset (ν n)) ∩ Ioo a b : Set ℝ).ncard : ℝ) / ν n) (hyperfilter ℕ)
      (𝓝 (b - a)) := by
    rw [Metric.tendsto_nhds]
    intro e he
    obtain ⟨M, hM⟩ := exists_nat_gt (max (max |a| |b|) (1 / e))
    filter_upwards [eventually_lt_of_unlimited_hnat hν M] with n hn
    have hMn : (M : ℝ) < ν n := by exact_mod_cast hn
    have ha : |a| < ν n :=
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) (hM.trans hMn)
    have hb : |b| < ν n :=
      lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) (hM.trans hMn)
    have he' : 1 / e < ν n := lt_of_le_of_lt (le_max_right _ _) (hM.trans hMn)
    have hpos : (0 : ℝ) < ν n := lt_of_le_of_lt (abs_nonneg a) ha
    have hN : 0 < ν n := by exact_mod_cast hpos
    have hbd := abs_ncard_gridFinset_inter_Ioo_sub_le hN hab ha hb
    rw [Real.dist_eq]
    have hrw : ((↑(gridFinset (ν n)) ∩ Ioo a b : Set ℝ).ncard : ℝ) / ν n - (b - a) =
        (((↑(gridFinset (ν n)) ∩ Ioo a b : Set ℝ).ncard : ℝ) - (b - a) * ν n) / ν n := by
      field_simp
    rw [hrw, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
    have := (div_lt_iff₀ he).1 he'
    linarith
  refine ((ENNReal.continuous_ofReal.tendsto _).comp hreal).congr' ?_
  filter_upwards [eventually_lt_of_unlimited_hnat hν 0] with n hn
  have hpos : (0 : ℝ) < ν n := by exact_mod_cast hn
  rw [gridMeasure_m, ← inter_assoc, inter_self]
  simp only [Function.comp_apply]
  rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    div_eq_mul_inv]

/-- **Theorem 16.8.1.** For real numbers $`a` and $`b`,
$`\mu_L(\{s \in S : a < s < b\}) = b - a`: the weighted number of grid points between $`a`
and $`b` is the length of the interval. (For $`b \le a` both sides are zero.) -/
theorem gridLoeb_μL_Ioo (hν : Unlimited (hnat ν)) (a b : ℝ) :
    (gridLoeb ν).μL (hyperGrid ν ∩ Ioo (a : ℝ*) b) = ENNReal.ofReal (b - a) := by
  rcases le_or_gt a b with hab | hab
  · rw [hyperGrid_inter_Ioo]
    exact tendsto_nhds_unique ((gridMeasure ν).tendsto_μL _) (tendsto_gridMeasure_Ioo hν hab)
  · have h0 : Ioo (a : ℝ*) b = ∅ := Ioo_eq_empty (not_lt.2 (Hyperreal.coe_le_coe.2 hab.le))
    rw [h0, inter_empty, ENNReal.ofReal_of_nonpos (by linarith)]
    exact (gridLoeb ν).isFinitelyAdditive.empty

/-- **Theorem 16.8.1**, for the Loeb measure: the set of grid points between $`a` and $`b`
is Loeb measurable and has Loeb measure $`b - a`. -/
theorem gridLoeb_loebMeasure_Ioo (hν : Unlimited (hnat ν)) (a b : ℝ) :
    (gridLoeb ν).loebMeasure (hyperGrid ν ∩ Ioo (a : ℝ*) b) = ENNReal.ofReal (b - a) := by
  rw [(gridLoeb ν).loebMeasure_of_mem (hyperGrid_inter_Ioo_mem_ring ν a b), gridLoeb_μL_Ioo hν]

end Grid

section InverseShadow

variable (ν : ℕ → ℕ)

/-- **Section 16.8.** The _inverse shadow_ $`\operatorname{sh}^{-1}(B)` of a set $`B` of
reals: the set of limited grid points whose shadow is in $`B`. -/
def shInv (B : Set ℝ) : Set ℝ* := {s | s ∈ hyperGrid ν ∧ Limited s ∧ sh s ∈ B}

/-- **Section 16.8.** The inverse shadow of $`B` is the set of grid points that are infinitely
close to some member of $`B`. -/
theorem mem_shInv_iff_exists_infClose {B : Set ℝ} {s : ℝ*} :
    s ∈ shInv ν B ↔ s ∈ hyperGrid ν ∧ ∃ r ∈ B, s ≊ (r : ℝ*) := by
  constructor
  · rintro ⟨hs, hl, hB⟩
    exact ⟨hs, sh s, hB, hl.infClose_sh⟩
  · rintro ⟨hs, r, hr, hsr⟩
    exact ⟨hs, limited_of_infClose_coe hsr, by rwa [sh_eq_of_infClose hsr]⟩

theorem shInv_empty : shInv ν ∅ = ∅ := by
  ext s; simp [shInv]

theorem shInv_mono {A B : Set ℝ} (h : A ⊆ B) : shInv ν A ⊆ shInv ν B :=
  fun _ hs => ⟨hs.1, hs.2.1, h hs.2.2⟩

/-- **Section 16.8.** $`\operatorname{sh}^{-1}(A - B) = \operatorname{sh}^{-1}(A) -
\operatorname{sh}^{-1}(B)`. -/
theorem shInv_diff (A B : Set ℝ) : shInv ν (A \ B) = shInv ν A \ shInv ν B := by
  ext s
  simp only [shInv, mem_ofPred_eq, Set.mem_sdiff]
  tauto

theorem shInv_inter (A B : Set ℝ) : shInv ν (A ∩ B) = shInv ν A ∩ shInv ν B := by
  ext s
  simp only [shInv, mem_ofPred_eq, mem_inter_iff]
  tauto

theorem shInv_compl (B : Set ℝ) : shInv ν Bᶜ = shInv ν univ \ shInv ν B := by
  rw [← shInv_diff, compl_eq_univ_sdiff]

/-- **Section 16.8.** $`\operatorname{sh}^{-1}(\bigcup_n A_n) =
\bigcup_n \operatorname{sh}^{-1}(A_n)`. -/
theorem shInv_iUnion {ι : Sort*} (A : ι → Set ℝ) : shInv ν (⋃ i, A i) = ⋃ i, shInv ν (A i) := by
  ext s
  simp only [shInv, mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨h1, h2, i, hi⟩
    exact ⟨i, h1, h2, hi⟩
  · rintro ⟨i, h1, h2, hi⟩
    exact ⟨h1, h2, i, hi⟩

/-- **Section 16.8.** The inverse shadow of the real line is the set of limited grid points,
the union of the internal sets $`S \cap {}^*(-n, n)`. -/
theorem shInv_univ_eq_iUnion :
    shInv ν univ = ⋃ n : ℕ, hyperGrid ν ∩ Ioo (((-(n : ℝ) : ℝ) : ℝ*)) ((n : ℝ) : ℝ*) := by
  ext s
  simp only [shInv, mem_ofPred_eq, mem_univ, and_true, mem_iUnion, mem_inter_iff, mem_Ioo]
  constructor
  · rintro ⟨hs, hl⟩
    obtain ⟨n, hn⟩ := limited_iff_exists_nat.1 hl
    exact ⟨n, hs, (abs_lt.1 hn).1, (abs_lt.1 hn).2⟩
  · rintro ⟨n, hs, h1, h2⟩
    exact ⟨hs, _, _, h1, h2⟩

/-- **Section 16.8.** The set $`\operatorname{sh}^{-1}(\mathbb R)` of limited grid points is
Loeb measurable, although it is not internal. -/
theorem loebMeasurable_shInv_univ : (gridLoeb ν).LoebMeasurable (shInv ν univ) := by
  rw [shInv_univ_eq_iUnion]
  exact LoebPremeasure.LoebMeasurable.iUnion fun n =>
    (gridLoeb ν).loebMeasurable_of_mem (hyperGrid_inter_Ioo_mem_ring ν _ _)

/-- **Lemma 16.8.3, first step.** The inverse shadow of an open interval $`(a, b)` is the
union of the increasing sequence of internal sets
$`S \cap {}^*(a + \tfrac1{n+1}, b - \tfrac1{n+1})`. -/
theorem shInv_Ioo_eq_iUnion (a b : ℝ) :
    shInv ν (Ioo a b) = ⋃ n : ℕ, hyperGrid ν ∩
      Ioo (((a + 1 / ((n : ℝ) + 1) : ℝ)) : ℝ*) ((b - 1 / ((n : ℝ) + 1) : ℝ) : ℝ*) := by
  ext s
  simp only [shInv, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_Ioo]
  constructor
  · rintro ⟨hs, hl, h1, h2⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min (sub_pos.2 h1) (sub_pos.2 h2))
    refine ⟨n, hs, hl.lt_of_lt_sh ?_, hl.lt_of_sh_lt ?_⟩
    · linarith [hn.trans_le (min_le_left _ _)]
    · linarith [hn.trans_le (min_le_right _ _)]
  · rintro ⟨n, hs, h1, h2⟩
    have hl : Limited s := ⟨_, _, h1, h2⟩
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨hs, hl, by linarith [hl.le_sh h1.le], by linarith [hl.sh_le h2.le]⟩

/-- **Lemma 16.8.3, first step.** The inverse shadow of an open interval is Loeb
measurable. -/
theorem loebMeasurable_shInv_Ioo (a b : ℝ) : (gridLoeb ν).LoebMeasurable (shInv ν (Ioo a b)) := by
  rw [shInv_Ioo_eq_iUnion]
  exact LoebPremeasure.LoebMeasurable.iUnion fun n =>
    (gridLoeb ν).loebMeasurable_of_mem (hyperGrid_inter_Ioo_mem_ring ν _ _)

/-- **Section 16.8.** The class $`\mathcal M` of the sets $`B` of reals whose inverse shadow
is Loeb measurable is a sigma-algebra, here a Mathlib measurable space on the real line. -/
@[instance_reducible] def shadowSpace : MeasurableSpace ℝ where
  MeasurableSet' B := (gridLoeb ν).LoebMeasurable (shInv ν B)
  measurableSet_empty := by
    rw [shInv_empty]; exact (gridLoeb ν).outer.isCaratheodory_empty
  measurableSet_compl B hB := by
    rw [shInv_compl]; exact (loebMeasurable_shInv_univ ν).diff hB
  measurableSet_iUnion f hf := by
    rw [shInv_iUnion]; exact LoebPremeasure.LoebMeasurable.iUnion hf

/-- **Lemma 16.8.3.** $`\mathcal M` includes the Borel algebra, because it is a sigma-algebra
that contains the open intervals. -/
theorem borel_le_shadowSpace : borel ℝ ≤ shadowSpace ν := by
  rw [Real.borel_eq_generateFrom_Ioo_rat]
  refine MeasurableSpace.generateFrom_le ?_
  simp only [mem_iUnion, mem_singleton_iff]
  rintro _ ⟨a, b, -, rfl⟩
  exact loebMeasurable_shInv_Ioo ν a b

/-- **Lemma 16.8.3.** The inverse shadow of a Borel set is Loeb measurable. -/
theorem loebMeasurable_shInv_of_measurableSet {B : Set ℝ} (hB : MeasurableSet B) :
    (gridLoeb ν).LoebMeasurable (shInv ν B) :=
  borel_le_shadowSpace ν B ((BorelSpace.measurable_eq (α := ℝ)).le B hB)

/-- **Section 16.8.** The measure $`\nu(B) = \mu_L(\operatorname{sh}^{-1}(B))` on the Borel
sets of the real line. -/
noncomputable def shadowMeasure : Measure ℝ :=
  Measure.ofMeasurable (fun B _ => (gridLoeb ν).outer (shInv ν B))
    (by rw [shInv_empty]; exact measure_empty)
    (fun f hf hd => by
      rw [shInv_iUnion]
      exact (gridLoeb ν).outer.iUnion_eq_of_caratheodory
        (fun i => loebMeasurable_shInv_of_measurableSet ν (hf i))
        (fun i j hij => Set.disjoint_left.2 fun s hs hs' =>
          Set.disjoint_left.1 (hd hij) hs.2.2 hs'.2.2))

theorem shadowMeasure_apply {B : Set ℝ} (hB : MeasurableSet B) :
    shadowMeasure ν B = (gridLoeb ν).outer (shInv ν B) :=
  Measure.ofMeasurable_apply _ hB

variable {ν}

/-- **Lemma 16.8.3, second step.** $`\mu_L(\operatorname{sh}^{-1}((a, b))) = b - a`, by
Theorem 16.8.1 and continuity of the Loeb measure along the increasing sequence of internal
sets that exhausts the inverse shadow. -/
theorem outer_shInv_Ioo (hν : Unlimited (hnat ν)) (a b : ℝ) :
    (gridLoeb ν).outer (shInv ν (Ioo a b)) = ENNReal.ofReal (b - a) := by
  have hmem : ∀ n : ℕ, (gridLoeb ν).outer.IsCaratheodory (hyperGrid ν ∩
      Ioo (((a + 1 / ((n : ℝ) + 1) : ℝ)) : ℝ*) ((b - 1 / ((n : ℝ) + 1) : ℝ) : ℝ*)) := fun n =>
    (gridLoeb ν).loebMeasurable_of_mem (hyperGrid_inter_Ioo_mem_ring ν _ _)
  have hmono : Monotone fun n : ℕ => hyperGrid ν ∩
      Ioo (((a + 1 / ((n : ℝ) + 1) : ℝ)) : ℝ*) ((b - 1 / ((n : ℝ) + 1) : ℝ) : ℝ*) := by
    intro m n hmn
    have h : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
    exact inter_subset_inter_right _ (Ioo_subset_Ioo (Hyperreal.coe_le_coe.2 (by linarith))
      (Hyperreal.coe_le_coe.2 (by linarith)))
  rw [shInv_Ioo_eq_iUnion,
    (isMeasureOnRing_isCaratheodory (gridLoeb ν).outer).iUnion_eq_iSup
      (isSigmaAlgebra_isCaratheodory (gridLoeb ν).outer).toIsSigmaRing.toIsRingOfSets hmem hmono
      (LoebPremeasure.LoebMeasurable.iUnion hmem)]
  have hval : ∀ n : ℕ, (gridLoeb ν).outer (hyperGrid ν ∩
      Ioo (((a + 1 / ((n : ℝ) + 1) : ℝ)) : ℝ*) ((b - 1 / ((n : ℝ) + 1) : ℝ) : ℝ*)) =
      ENNReal.ofReal ((b - 1 / ((n : ℝ) + 1)) - (a + 1 / ((n : ℝ) + 1))) := fun n => by
    rw [(gridLoeb ν).outer_eq_of_mem (hyperGrid_inter_Ioo_mem_ring ν _ _), gridLoeb_μL_Ioo hν]
  simp only [hval]
  have hlim : Tendsto (fun n : ℕ =>
      ENNReal.ofReal ((b - 1 / ((n : ℝ) + 1)) - (a + 1 / ((n : ℝ) + 1)))) atTop
      (𝓝 (ENNReal.ofReal (b - a))) := by
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have := ((tendsto_const_nhds (x := b)).sub h0).sub ((tendsto_const_nhds (x := a)).add h0)
    simp only [sub_zero, add_zero] at this
    exact ENNReal.tendsto_ofReal this
  refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal ?_)
    (le_of_tendsto' hlim fun n => le_iSup (fun n : ℕ =>
      ENNReal.ofReal ((b - 1 / ((n : ℝ) + 1)) - (a + 1 / ((n : ℝ) + 1)))) n)
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- **Lemma 16.8.3.** The measure $`\nu` on the Borel sets is Lebesgue measure, because it
agrees with Lebesgue measure on the open intervals. -/
theorem shadowMeasure_eq_volume (hν : Unlimited (hnat ν)) : shadowMeasure ν = volume :=
  eq_volume_of_forall_Ioo _ fun a b => by
    rw [shadowMeasure_apply ν measurableSet_Ioo, outer_shInv_Ioo hν]

/-- **Lemma 16.8.3.** For every Borel set $`B`,
$`\mu_L(\operatorname{sh}^{-1}(B)) = \lambda(B)`. -/
theorem outer_shInv_eq_volume (hν : Unlimited (hnat ν)) {B : Set ℝ} (hB : MeasurableSet B) :
    (gridLoeb ν).outer (shInv ν B) = volume B := by
  rw [← shadowMeasure_apply ν hB, shadowMeasure_eq_volume hν]

/-- **Theorem 16.8.2, first half.** If $`B` is Lebesgue measurable, then its inverse shadow is
Loeb measurable and $`\mu_L(\operatorname{sh}^{-1}(B)) = \lambda(B)`. The set $`B` lies
between two Borel sets whose difference is null; their inverse shadows are Loeb measurable
with a null difference, and the Loeb measure is complete. -/
theorem LebesgueMeasurable.loebMeasurable_shInv (hν : Unlimited (hnat ν)) {B : Set ℝ}
    (hB : LebesgueMeasurable B) :
    (gridLoeb ν).LoebMeasurable (shInv ν B) ∧ (gridLoeb ν).outer (shInv ν B) = volume B := by
  obtain ⟨C, D, hC, hD, hCB, hBD, hnull, hCvol, hDvol⟩ := hB.exists_borel_between
  have h0 : (gridLoeb ν).outer (shInv ν D \ shInv ν C) = 0 := by
    rw [← shInv_diff, outer_shInv_eq_volume hν (hD.diff hC), hnull]
  have hCm := loebMeasurable_shInv_of_measurableSet ν hC
  have hrest : (gridLoeb ν).LoebMeasurable (shInv ν B \ shInv ν C) :=
    (gridLoeb ν).loebMeasurable_of_null
      (measure_mono_null (sdiff_subset_sdiff_left (shInv_mono ν hBD)) h0)
  have hBeq : shInv ν B = shInv ν C ∪ (shInv ν B \ shInv ν C) := by
    rw [union_sdiff_cancel (shInv_mono ν hCB)]
  refine ⟨by rw [hBeq]; exact hCm.union hrest, le_antisymm ?_ ?_⟩
  · rw [← hDvol, ← outer_shInv_eq_volume hν hD]
    exact measure_mono (shInv_mono ν hBD)
  · rw [← hCvol, ← outer_shInv_eq_volume hν hC]
    exact measure_mono (shInv_mono ν hCB)

/-- **Theorem 16.8.2, second half, the finite case.** If the inverse shadow of $`B` is Loeb
measurable of finite Loeb measure, then $`B` is Lebesgue measurable. The inverse shadow is
approximable by internal sets $`C \subseteq \operatorname{sh}^{-1}(B) \subseteq D`; the shadow
of $`C` is a closed subset of $`B`, the complement of the shadow of $`S - D` is an open
superset of $`B`, and the Lebesgue measure of their difference is at most
$`\mu_L(D - C)`. -/
theorem lebesgueMeasurable_of_loebMeasurable_shInv_of_ne_top (hν : Unlimited (hnat ν))
    {B : Set ℝ} (hB : (gridLoeb ν).LoebMeasurable (shInv ν B))
    (hfin : (gridLoeb ν).outer (shInv ν B) ≠ ∞) : LebesgueMeasurable B := by
  refine lebesgueMeasurable_of_forall_exists_closed_open fun e he => ?_
  obtain ⟨C, hC, D, hD, hCB, hBD, hlt⟩ := hB.approximable hfin e he
  have hCint : IsInternal C := (gridMeasure ν).isInternalSet_of_mem_sets hC
  have hSD : IsInternal (hyperGrid ν \ D) :=
    (isInternalSet_internalSet _).diff ((gridMeasure ν).isInternalSet_of_mem_sets hD)
  refine ⟨shSet C, (shSet (hyperGrid ν \ D))ᶜ, hCint.isClosed_shSet,
    hSD.isClosed_shSet.isOpen_compl, ?_, ?_, ?_⟩
  · rintro r ⟨x, hx, -, rfl⟩
    exact (hCB hx).2.2
  · rintro r hr ⟨x, hx, hxl, rfl⟩
    exact hx.2 (hBD ⟨hx.1, hxl, hr⟩)
  · have hBorel : MeasurableSet ((shSet (hyperGrid ν \ D))ᶜ \ shSet C) :=
      hSD.isClosed_shSet.isOpen_compl.measurableSet.diff hCint.isClosed_shSet.measurableSet
    rw [← outer_shInv_eq_volume hν hBorel]
    refine lt_of_le_of_lt ?_ hlt
    rw [← (gridLoeb ν).outer_eq_of_mem ((gridLoeb ν).isRing.diff_mem hD hC)]
    refine measure_mono ?_
    rintro x ⟨hxS, hxl, hxU, hxC⟩
    refine ⟨?_, fun hxC' => hxC ⟨x, hxC', hxl, rfl⟩⟩
    by_contra hxD
    exact hxU ⟨x, ⟨hxS, hxD⟩, hxl, rfl⟩

/-- **Theorem 16.8.2, second half.** If the inverse shadow of $`B` is Loeb measurable, then
$`B` is Lebesgue measurable: $`B` is the union of the sets $`B \cap (-n, n)`, whose inverse
shadows are Loeb measurable of measure at most $`2n`. -/
theorem lebesgueMeasurable_of_loebMeasurable_shInv (hν : Unlimited (hnat ν)) {B : Set ℝ}
    (hB : (gridLoeb ν).LoebMeasurable (shInv ν B)) : LebesgueMeasurable B := by
  have hBU : B = ⋃ n : ℕ, B ∩ Ioo (-(n : ℝ)) n := by
    rw [← inter_iUnion]
    refine (inter_eq_left.2 fun x _ => ?_).symm
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact mem_iUnion.2 ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  rw [hBU]
  refine lebesgueOuter.isCaratheodory_iUnion fun n => ?_
  refine lebesgueMeasurable_of_loebMeasurable_shInv_of_ne_top hν ?_ ?_
  · rw [shInv_inter]
    exact hB.inter (loebMeasurable_shInv_Ioo ν _ _)
  · refine ne_top_of_le_ne_top ?_ (measure_mono (shInv_mono ν inter_subset_right))
    rw [outer_shInv_Ioo hν]
    exact ENNReal.ofReal_ne_top

/-- **Theorem 16.8.2.** A set $`B` of real numbers is Lebesgue measurable if and only if its
inverse shadow $`\operatorname{sh}^{-1}(B)` in the hyperfinite grid is Loeb measurable. -/
theorem lebesgueMeasurable_iff_loebMeasurable_shInv (hν : Unlimited (hnat ν)) {B : Set ℝ} :
    LebesgueMeasurable B ↔ (gridLoeb ν).LoebMeasurable (shInv ν B) :=
  ⟨fun h => (h.loebMeasurable_shInv hν).1, lebesgueMeasurable_of_loebMeasurable_shInv hν⟩

/-- **Theorem 16.8.2.** When $`B` is Lebesgue measurable, its Lebesgue measure is the Loeb
measure of the set of grid points infinitely close to points of $`B`:
$`\lambda(B) = \mu_L(\operatorname{sh}^{-1}(B))`. -/
theorem volume_eq_loebMeasure_shInv (hν : Unlimited (hnat ν)) {B : Set ℝ}
    (hB : LebesgueMeasurable B) : volume B = (gridLoeb ν).loebMeasure (shInv ν B) := by
  obtain ⟨h1, h2⟩ := hB.loebMeasurable_shInv hν
  rw [(gridLoeb ν).loebMeasure_apply h1, h2]

/-- **Theorem 16.8.2**, for Mathlib's notion of measurability: a set of reals is
null-measurable for Lebesgue measure if and only if its inverse shadow is Loeb measurable. -/
theorem nullMeasurableSet_iff_loebMeasurable_shInv (hν : Unlimited (hnat ν)) {B : Set ℝ} :
    NullMeasurableSet B volume ↔ (gridLoeb ν).LoebMeasurable (shInv ν B) := by
  rw [← lebesgueMeasurable_iff_nullMeasurableSet, lebesgueMeasurable_iff_loebMeasurable_shInv hν]

/-- **Theorem 16.8.2**, in terms of the hypernatural $`N`: every unlimited hypernatural $`N`
is the class of a sequence for which the grid of the points $`k/N` with $`|k| \le N^2`
represents Lebesgue measure by its Loeb measure. -/
theorem exists_grid_representation {N : ℝ*} (hN : N ∈ ℕ*) (hU : Unlimited N) :
    ∃ ν : ℕ → ℕ, N = hnat ν ∧
      (∀ x : ℝ*, x ∈ hyperGrid ν ↔ ∃ k ∈ ℤ*, |k| ≤ N ^ 2 ∧ x = k / N) ∧
      ∀ B : Set ℝ, (LebesgueMeasurable B ↔ (gridLoeb ν).LoebMeasurable (shInv ν B)) ∧
        (LebesgueMeasurable B → volume B = (gridLoeb ν).loebMeasure (shInv ν B)) := by
  obtain ⟨ν, rfl⟩ := exists_hnat_eq hN
  exact ⟨ν, rfl, fun x => mem_hyperGrid_iff ν, fun B =>
    ⟨lebesgueMeasurable_iff_loebMeasurable_shInv hU, volume_eq_loebMeasure_shInv hU⟩⟩

end InverseShadow

end Goldblatt
