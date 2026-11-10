import Goldblatt.Ch16_LoebMeasure.Loeb

/-!
# 16 (part 4). Internal Measures in the Ultrapower

This is the fourth of five parts of Chapter 16 (the overview is on the chapter page
{lit}`Goldblatt.Ch16_LoebMeasure`). It supplies the nonstandard input for Sections 16.5 to
16.7 in the ultrapower of Chapters 3, 11 and 12, and proves the examples of Sections 16.1 and
16.2 that involve internal sets.

An internal ring of internal sets is given by a sequence of rings of sets, and an internal
finitely additive function on it by a sequence of finitely additive functions; its values are
classes of sequences of extended nonnegative reals. The shadow of such a value is the limit
of the sequence along the index ultrafilter, which always exists in $`[0, \infty]`. Countable
saturation of the ultrapower (Theorem 11.10.1), applied to internal sets of points and to
internal sets of sets, gives the three properties required by part 3, so that every internal
measure has a Loeb measure.
-/

universe u

namespace Goldblatt

open Set Filter MeasureTheory Function Ultrapower
open scoped ENNReal Topology Hyperreal

/-!
## The extended nonnegative hyperreals and their shadows

The book lets an internal measure take values in the enlargement of $`[0, \infty]`. In the
ultrapower that enlargement is the type of classes of sequences of extended nonnegative reals.
Its shadow map sends a class to the limit of any representing sequence along the index
ultrafilter; by compactness of $`[0, \infty]` the limit exists. On the classes that come from
nonnegative hyperreals this is the book's definition: the shadow of a limited number, and
$`\infty` for an unlimited one.
-/

section Shadow

/-- **Section 16.2, example 3.** The enlargement of $`[0, \infty]`: classes of sequences of
extended nonnegative reals. -/
abbrev HyperENNReal : Type := Ultrapower ℝ≥0∞

/-- **Section 16.2, example 4.** The extended shadow of an element of the enlargement of
$`[0, \infty]`: the limit of a representing sequence along the index ultrafilter. -/
noncomputable def loebSh (x : HyperENNReal) : ℝ≥0∞ :=
  Germ.liftOn x (fun f => (Ultrafilter.map f (hyperfilter ℕ)).lim) fun f g h => by
    have : Ultrafilter.map f (hyperfilter ℕ) = Ultrafilter.map g (hyperfilter ℕ) :=
      Ultrafilter.coe_injective (Filter.map_congr h)
    simp only [this]

/-- A sequence of extended nonnegative reals converges along the index ultrafilter to the
extended shadow of its class. -/
theorem tendsto_loebSh (f : ℕ → ℝ≥0∞) :
    Tendsto f (hyperfilter ℕ) (𝓝 (loebSh (Germ.ofFun f))) :=
  (Ultrafilter.map f (hyperfilter ℕ)).le_nhds_lim

/-- The extended shadow of the class of a sequence is its limit along the index ultrafilter,
whenever a limit is known. -/
theorem loebSh_eq_of_tendsto {f : ℕ → ℝ≥0∞} {a : ℝ≥0∞}
    (h : Tendsto f (hyperfilter ℕ) (𝓝 a)) : loebSh (Germ.ofFun f) = a :=
  tendsto_nhds_unique (tendsto_loebSh f) h

/-- The extended shadow of a standard element is that element. -/
theorem loebSh_const (r : ℝ≥0∞) : loebSh (↑r : HyperENNReal) = r :=
  loebSh_eq_of_tendsto (f := fun _ => r) tendsto_const_nhds

/-- The extended shadow is additive. -/
theorem loebSh_add (x y : HyperENNReal) : loebSh (x + y) = loebSh x + loebSh y := by
  induction x, y using Germ.inductionOn₂ with
  | _ f g => exact loebSh_eq_of_tendsto (f := f + g) ((tendsto_loebSh f).add (tendsto_loebSh g))

/-- The extended shadow is monotone. -/
theorem loebSh_mono {x y : HyperENNReal} (h : x ≤ y) : loebSh x ≤ loebSh y := by
  induction x, y using Germ.inductionOn₂ with
  | _ f g => exact le_of_tendsto_of_tendsto (tendsto_loebSh f) (tendsto_loebSh g) (Germ.coe_le.1 h)

/-- If $`x \le r` for a standard $`r`, then the extended shadow of $`x` is at most $`r`. -/
theorem loebSh_le_of_le_const {x : HyperENNReal} {r : ℝ≥0∞} (h : x ≤ (↑r : HyperENNReal)) :
    loebSh x ≤ r := by
  have := loebSh_mono h
  rwa [loebSh_const] at this

/-- If the extended shadow of $`x` is less than a standard $`r`, then $`x < r`. -/
theorem lt_const_of_loebSh_lt {x : HyperENNReal} {r : ℝ≥0∞} (h : loebSh x < r) :
    x < (↑r : HyperENNReal) := by
  induction x using Germ.inductionOn with
  | _ f => exact Germ.coe_lt.2 ((tendsto_loebSh f).eventually (eventually_lt_nhds h))

/-- The inclusion of the nonnegative hyperreals in the enlargement of $`[0, \infty]`
(negative numbers are sent to zero). -/
noncomputable def hyperENNRealOfHyperreal (h : ℝ*) : HyperENNReal := Germ.map ENNReal.ofReal h

/-- A real sequence whose class is limited converges along the index ultrafilter to the
shadow of the class. -/
theorem tendsto_sh_ofSeq {f : ℕ → ℝ} (hl : Limited (Hyperreal.ofSeq f)) :
    Tendsto f (hyperfilter ℕ) (𝓝 (sh (Hyperreal.ofSeq f))) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have h1 := infClose_iff_abs_lt.1 hl.infClose_sh η hη
  have h2 : |Hyperreal.ofSeq f - (sh (Hyperreal.ofSeq f) : ℝ*)| =
      Hyperreal.ofSeq fun n => |f n - sh (Hyperreal.ofSeq f)| := rfl
  rw [h2] at h1
  exact (ofSeq_lt_ofSeq_iff (s := fun _ => η)).1 h1

/-- **Section 16.2, example 4**, the definition of $`\mu_L` in the book's terms: on a limited
nonnegative hyperreal the extended shadow is the shadow of Chapter 5. -/
theorem loebSh_of_limited {h : ℝ*} (hl : Limited h) :
    loebSh (hyperENNRealOfHyperreal h) = ENNReal.ofReal (sh h) := by
  obtain ⟨f, rfl⟩ := hyperreal_exists_rep h
  exact loebSh_eq_of_tendsto (f := fun n => ENNReal.ofReal (f n))
    ((ENNReal.continuous_ofReal.tendsto _).comp (tendsto_sh_ofSeq hl))

/-- **Section 16.2, example 4**, the definition of $`\mu_L` in the book's terms: on a positive
unlimited hyperreal the extended shadow is $`\infty`. -/
theorem loebSh_of_posUnlimited {h : ℝ*} (hu : PosUnlimited h) :
    loebSh (hyperENNRealOfHyperreal h) = ∞ := by
  obtain ⟨f, rfl⟩ := hyperreal_exists_rep h
  refine loebSh_eq_of_tendsto (f := fun n => ENNReal.ofReal (f n)) ?_
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro x
  have := (ofSeq_lt_ofSeq_iff (r := fun _ => (x : ℝ))).1 (hu x)
  filter_upwards [this] with n hn
  rw [← ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt x.coe_nonneg hn)).2 hn

end Shadow

/-!
## Internal measures and their Loeb measures

The data of Section 16.5 in the ultrapower: a sequence of rings of subsets of $`\beta` and a
sequence of finitely additive functions on them. The members of the internal ring are the
internal sets $`[B_n]` with $`B_n` in the $`n`-th ring for almost all $`n`, and the internal
measure of $`[B_n]` is the class of the sequence of the measures of the $`B_n`.
-/

/-- **Section 16.5.** An internal ring of internal subsets of the star type of $`\beta`
together with an internal finitely additive function on it, presented by sequences: the
$`n`-th ring $`\mathcal A_n` and the $`n`-th finitely additive function $`\mu_n`.

In the ultrapower an internal collection of sets that is a ring is the class of a sequence of
collections almost all of which are rings, and such a sequence can be changed on a negligible
set of indices to consist of rings only; so nothing is lost by requiring every term to be a
ring, and likewise for finite additivity. -/
structure InternalMeasure (β : Type u) where
  /-- The sequence of rings. -/
  𝔄 : ℕ → Set (Set β)
  /-- The sequence of finitely additive functions. -/
  m : ℕ → Set β → ℝ≥0∞
  /-- Each term of the first sequence is a ring. -/
  isRing : ∀ n, IsRingOfSets (𝔄 n)
  /-- Each term of the second sequence is finitely additive. -/
  isFinitelyAdditive : ∀ n, IsFinitelyAdditive (𝔄 n) (m n)

namespace InternalMeasure

variable {β βS : Type u} [StarType β βS] (I : InternalMeasure β)

/-- **Section 16.5.** The internal ring $`\mathcal A`: the internal sets $`[B_n]` such that
$`B_n \in \mathcal A_n` for almost all $`n`. -/
def sets : Set (Set βS) :=
  {X | ∃ B : ℕ → Set β, X = internalSet B ∧ ∀ᶠ n in hyperfilter ℕ, B n ∈ I.𝔄 n}

/-- Membership of $`[B_n]` in the internal ring does not depend on the defining sequence. -/
theorem internalSet_mem_sets {B : ℕ → Set β} :
    (internalSet B : Set βS) ∈ I.sets ↔ ∀ᶠ n in hyperfilter ℕ, B n ∈ I.𝔄 n := by
  constructor
  · rintro ⟨B', hBB', hB'⟩
    filter_upwards [internalSet_eq_iff.1 hBB', hB'] with n h1 h2
    rwa [h1]
  · exact fun h => ⟨B, rfl, h⟩

/-- Every member of the internal ring is an internal set. -/
theorem isInternalSet_of_mem_sets {X : Set βS} (hX : X ∈ I.sets) : IsInternalSet β X := by
  obtain ⟨B, rfl, -⟩ := hX
  exact ⟨B, rfl⟩

open Classical in
/-- **Section 16.5.** The internal measure $`\mu`: its value at $`[B_n]` is the class of the
sequence $`(\mu_n(B_n))`. (At a set that is not internal the value is zero.) -/
noncomputable def μ (X : Set βS) : HyperENNReal :=
  if h : IsInternalSet β X then Germ.ofFun fun n => I.m n (h.choose n) else 0

/-- **Section 16.5.** The internal measure of $`[B_n]` is the class of the sequence
$`(\mu_n(B_n))`, whatever sequence defines the set. -/
theorem μ_internalSet (B : ℕ → Set β) :
    I.μ (internalSet B : Set βS) = Germ.ofFun fun n => I.m n (B n) := by
  have h : IsInternalSet β (internalSet B : Set βS) := ⟨B, rfl⟩
  rw [μ, dite_eq_left_of_eq_true (eq_true h)]
  refine Germ.coe_eq.2 ?_
  filter_upwards [internalSet_eq_iff.1 h.choose_spec] with n hn
  rw [hn]

/-- **Section 16.2, example 4.** The function $`\mu_L`: the extended shadow of the internal
measure, $`\mu_L(A) = \operatorname{sh}(\mu(A))` if $`\mu(A)` is limited and
$`\mu_L(A) = \infty` otherwise. -/
noncomputable def μL (X : Set βS) : ℝ≥0∞ := loebSh (I.μ X)

/-- $`\mu_L([B_n])` is the limit of $`\mu_n(B_n)` along the index ultrafilter. -/
theorem tendsto_μL (B : ℕ → Set β) :
    Tendsto (fun n => I.m n (B n)) (hyperfilter ℕ) (𝓝 (I.μL (internalSet B : Set βS))) := by
  rw [μL, μ_internalSet]
  exact tendsto_loebSh _

/-- **Section 16.5.** The internal ring is a ring of sets. -/
theorem isRingOfSets_sets : IsRingOfSets (I.sets : Set (Set βS)) := by
  refine ⟨⟨∅, fun _ => ∅, ?_, Eventually.of_forall fun n => (I.isRing n).empty_mem⟩, ?_, ?_⟩
  · rw [← starSet_eq_internalSet, starSet_empty]
  · rintro _ _ ⟨A, rfl, hA⟩ ⟨B, rfl, hB⟩
    rw [internalSet_diff]
    exact ⟨_, rfl, by filter_upwards [hA, hB] with n h1 h2 using (I.isRing n).diff_mem h1 h2⟩
  · rintro _ _ ⟨A, rfl, hA⟩ ⟨B, rfl, hB⟩
    rw [internalSet_union]
    exact ⟨_, rfl, by filter_upwards [hA, hB] with n h1 h2 using (I.isRing n).union_mem h1 h2⟩

/-- **Section 16.2, example 4.** $`\mu_L` is finitely additive on the internal ring. -/
theorem isFinitelyAdditive_μL : IsFinitelyAdditive (I.sets : Set (Set βS)) I.μL := by
  constructor
  · have h : (∅ : Set βS) = internalSet fun _ => (∅ : Set β) := by
      rw [← starSet_eq_internalSet, starSet_empty]
    rw [h]
    refine tendsto_nhds_unique (I.tendsto_μL _) ?_
    simp only [(I.isFinitelyAdditive _).empty]
    exact tendsto_const_nhds
  · rintro _ _ ⟨A, rfl, hA⟩ ⟨B, rfl, hB⟩ hAB
    have hd : ∀ᶠ n in hyperfilter ℕ, Disjoint (A n) (B n) := by
      have := internalSet_eq_empty_iff.1
        ((internalSet_inter A B).symm.trans (Set.disjoint_iff_inter_eq_empty.1 hAB))
      exact this.mono fun n hn => Set.disjoint_iff_inter_eq_empty.2 hn
    have h1 := (I.tendsto_μL (βS := βS) A).add (I.tendsto_μL (βS := βS) B)
    have h2 := I.tendsto_μL (βS := βS) fun n => A n ∪ B n
    rw [← internalSet_union A B] at h2
    refine tendsto_nhds_unique h2 (h1.congr' ?_)
    filter_upwards [hA, hB, hd] with n hA hB hd
    exact ((I.isFinitelyAdditive n).union hA hB hd).symm

/-- **Lemma 16.5.1, the saturation step.** An increasing sequence of members of the internal
ring whose $`\mu_L`-measures are at most $`r` is included in a single member of
$`\mu_L`-measure at most $`r`. The book extends the sequence to an internal hypersequence and
applies overflow; here countable saturation is applied to the internal sets of sets
$`\{D \in \mathcal A : A_k \subseteq D,\ \mu(D) \le r + \tfrac1{k+1}\}`, which decrease and
are nonempty. -/
theorem exists_upper {A : ℕ → Set βS} (r : ℝ≥0∞) (hA : ∀ k, A k ∈ I.sets) (hmono : Monotone A)
    (hr : ∀ k, I.μL (A k) ≤ r) : ∃ D ∈ I.sets, (∀ k, A k ⊆ D) ∧ I.μL D ≤ r := by
  choose a ha ha' using hA
  let η : ℕ → ℝ≥0∞ := fun k => ((k + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hη : ∀ k, η (k + 1) ≤ η k := fun k =>
    ENNReal.inv_le_inv.2 (by exact_mod_cast Nat.le_succ (k + 1))
  let X : ℕ → Set (Ultrapower (Set β)) := fun k =>
    internalSet fun n => {K | K ∈ I.𝔄 n ∧ a k n ⊆ K ∧ I.m n K ≤ r + η k}
  have hsub : ∀ k, ∀ᶠ n in hyperfilter ℕ, a k n ⊆ a (k + 1) n := fun k =>
    internalSet_subset_iff.1 (by
      rw [← ha k, ← ha (k + 1)]; exact hmono (Nat.le_succ k) : (internalSet (a k) : Set βS) ⊆ _)
  have hne : ∀ k, (X k).Nonempty := by
    intro k
    refine ⟨ofSeq (a k), ofSeq_mem_internalSet.2 ?_⟩
    have hle : ∀ᶠ n in hyperfilter ℕ, I.m n (a k n) ≤ r + η k := by
      by_cases hrt : r = ∞
      · exact Eventually.of_forall fun n => by rw [hrt, top_add]; exact le_top
      · have hlt : I.μL (A k) < r + η k :=
          lt_of_le_of_lt (hr k) (ENNReal.lt_add_right hrt (by simp [η]))
        have := I.tendsto_μL (βS := βS) (a k)
        rw [← ha k] at this
        exact (this.eventually (eventually_lt_nhds hlt)).mono fun n hn => hn.le
    filter_upwards [ha' k, hle] with n h1 h2
    exact ⟨h1, Subset.rfl, h2⟩
  have hdec : ∀ k, X (k + 1) ⊆ X k := by
    intro k
    refine internalSet_subset_iff.2 ?_
    filter_upwards [hsub k] with n hn K hK
    exact ⟨hK.1, hn.trans hK.2.1, hK.2.2.trans (by gcongr; exact hη k)⟩
  obtain ⟨G, hG⟩ := iInter_nonempty_of_isInternalSet (α := Set β)
    (fun k => isInternalSet_internalSet _) hne hdec
  obtain ⟨κ, rfl⟩ := ofSeq_surjective (α := Set β) G
  have hκ : ∀ k, ∀ᶠ n in hyperfilter ℕ,
      κ n ∈ I.𝔄 n ∧ a k n ⊆ κ n ∧ I.m n (κ n) ≤ r + η k := fun k =>
    ofSeq_mem_internalSet.1 (mem_iInter.1 hG k)
  refine ⟨internalSet κ, ⟨κ, rfl, (hκ 0).mono fun n h => h.1⟩, fun k => ?_, ?_⟩
  · rw [ha k]
    exact internalSet_subset_iff.2 ((hκ k).mono fun n h => h.2.1)
  · have hk : ∀ k, I.μL (internalSet κ : Set βS) ≤ r + η k := fun k =>
      le_of_tendsto (I.tendsto_μL κ) ((hκ k).mono fun n h => h.2.2)
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    obtain ⟨k, hk'⟩ := ENNReal.exists_inv_nat_lt (a := (δ : ℝ≥0∞)) (by exact_mod_cast hδ.ne')
    refine (hk k).trans ?_
    gcongr
    exact (ENNReal.inv_le_inv.2 (by exact_mod_cast Nat.le_succ k)).trans hk'.le

/-- **Lemma 16.6.2, the saturation step.** If $`(C_k)` is an increasing and $`(D_k)` a
decreasing sequence of members of the internal ring with every $`C_j` included in every
$`D_k`, then some member $`K` of the ring has $`C_k \subseteq K \subseteq D_k` for all $`k`.
The book extends the sequences to internal hypersequences and takes $`D_K` for an unlimited
$`K` given by overflow; here countable saturation is applied to the internal sets of sets
$`\{K \in \mathcal A : C_k \subseteq K \subseteq D_k\}`. -/
theorem exists_between {C D : ℕ → Set βS} (hC : ∀ k, C k ∈ I.sets) (hD : ∀ k, D k ∈ I.sets)
    (hCmono : Monotone C) (hDanti : Antitone D) (hCD : ∀ j k, C j ⊆ D k) :
    ∃ K ∈ I.sets, ∀ k, C k ⊆ K ∧ K ⊆ D k := by
  choose c hc hc' using hC
  choose d hd hd' using hD
  let X : ℕ → Set (Ultrapower (Set β)) := fun k =>
    internalSet fun n => {K | K ∈ I.𝔄 n ∧ c k n ⊆ K ∧ K ⊆ d k n}
  have hcsub : ∀ k, ∀ᶠ n in hyperfilter ℕ, c k n ⊆ c (k + 1) n := fun k =>
    internalSet_subset_iff.1 (by
      rw [← hc k, ← hc (k + 1)]; exact hCmono (Nat.le_succ k) : (internalSet (c k) : Set βS) ⊆ _)
  have hdsub : ∀ k, ∀ᶠ n in hyperfilter ℕ, d (k + 1) n ⊆ d k n := fun k =>
    internalSet_subset_iff.1 (by
      rw [← hd k, ← hd (k + 1)]; exact hDanti (Nat.le_succ k) :
        (internalSet (d (k + 1)) : Set βS) ⊆ _)
  have hcd : ∀ k, ∀ᶠ n in hyperfilter ℕ, c k n ⊆ d k n := fun k =>
    internalSet_subset_iff.1 (by
      rw [← hc k, ← hd k]; exact hCD k k : (internalSet (c k) : Set βS) ⊆ _)
  have hne : ∀ k, (X k).Nonempty := fun k =>
    ⟨ofSeq (c k), ofSeq_mem_internalSet.2 (by
      filter_upwards [hc' k, hcd k] with n h1 h2 using ⟨h1, Subset.rfl, h2⟩)⟩
  have hdec : ∀ k, X (k + 1) ⊆ X k := by
    intro k
    refine internalSet_subset_iff.2 ?_
    filter_upwards [hcsub k, hdsub k] with n h1 h2 K hK
    exact ⟨hK.1, h1.trans hK.2.1, hK.2.2.trans h2⟩
  obtain ⟨G, hG⟩ := iInter_nonempty_of_isInternalSet (α := Set β)
    (fun k => isInternalSet_internalSet _) hne hdec
  obtain ⟨κ, rfl⟩ := ofSeq_surjective (α := Set β) G
  have hκ : ∀ k, ∀ᶠ n in hyperfilter ℕ, κ n ∈ I.𝔄 n ∧ c k n ⊆ κ n ∧ κ n ⊆ d k n := fun k =>
    ofSeq_mem_internalSet.1 (mem_iInter.1 hG k)
  refine ⟨internalSet κ, ⟨κ, rfl, (hκ 0).mono fun n h => h.1⟩, fun k => ⟨?_, ?_⟩⟩
  · rw [hc k]
    exact internalSet_subset_iff.2 ((hκ k).mono fun n h => h.2.1)
  · rw [hd k]
    exact internalSet_subset_iff.2 ((hκ k).mono fun n h => h.2.2)

/-- **Section 16.1, example 6.** In an internal ring, the union of a countable sequence of
members can belong to the ring only if it is the union of finitely many of its terms. This is
Corollary 11.10.2 of countable saturation, and it is the fact on which Loeb measure is
founded. -/
theorem exists_iUnion_eq_biUnion_le_of_mem_sets {A : ℕ → Set βS} (hA : ∀ n, A n ∈ I.sets)
    (hU : ⋃ n, A n ∈ I.sets) : ∃ k, ⋃ n, A n = ⋃ n ≤ k, A n :=
  exists_iUnion_eq_biUnion_le (fun n => I.isInternalSet_of_mem_sets (hA n))
    (I.isInternalSet_of_mem_sets hU)

/-- **Section 16.1, example 6.** The union of a strictly increasing sequence of members of an
internal ring is not in the ring; so an internal ring with such a sequence is not a
sigma-ring. -/
theorem iUnion_notMem_sets_of_ssubset {A : ℕ → Set βS} (hA : ∀ n, A n ∈ I.sets)
    (hinc : ∀ n, A n ⊂ A (n + 1)) : ⋃ n, A n ∉ I.sets := fun hU =>
  not_isInternalSet_iUnion_of_ssubset_succ (fun n => I.isInternalSet_of_mem_sets (hA n)) hinc
    (I.isInternalSet_of_mem_sets hU)

/-- **Section 16.5.** Every internal finitely additive measure on an internal ring has the
three saturation properties of part 3, and therefore a Loeb measure. -/
noncomputable def toLoebPremeasure : LoebPremeasure βS where
  ring := I.sets
  μL := I.μL
  isRing := I.isRingOfSets_sets
  isFinitelyAdditive := I.isFinitelyAdditive_μL
  finite_union _ hA hU := I.exists_iUnion_eq_biUnion_le_of_mem_sets hA hU
  exists_upper _ r hA hmono hr := I.exists_upper r hA hmono hr
  exists_between _ _ hC hD hCmono hDanti hCD := I.exists_between hC hD hCmono hDanti hCD

/-- The ring of the Loeb premeasure of an internal measure is its internal ring. -/
@[simp] theorem toLoebPremeasure_ring : (I.toLoebPremeasure (βS := βS)).ring = I.sets := rfl

/-- The function of the Loeb premeasure of an internal measure is $`\mu_L`. -/
@[simp] theorem toLoebPremeasure_μL : (I.toLoebPremeasure (βS := βS)).μL = I.μL := rfl

/-- **Section 16.2, example 4.** $`\mu_L` is countably additive on the internal ring: it is a
measure there. -/
theorem isMeasureOnRing_μL : IsMeasureOnRing (I.sets : Set (Set βS)) I.μL :=
  (I.toLoebPremeasure (βS := βS)).isMeasureOnRing

/-- **Section 16.6**, the definition of approximability in terms of the internal measure
itself: $`B` is approximable if and only if for every real $`\varepsilon > 0` there are
$`C, D` in the internal ring with $`C \subseteq B \subseteq D` and
$`\mu(D - C) < \varepsilon`, the inequality being between elements of the enlargement of
$`[0, \infty]`. This is equivalent to the formulation with $`\mu_L` because
$`\mu(A) \simeq \mu_L(A)`. -/
theorem approximable_iff {B : Set βS} :
    (I.toLoebPremeasure (βS := βS)).Approximable B ↔
      ∀ η : ℝ, 0 < η → ∃ C ∈ I.sets, ∃ D ∈ I.sets, C ⊆ B ∧ B ⊆ D ∧
        I.μ (D \ C) < (↑(ENNReal.ofReal η) : HyperENNReal) := by
  constructor
  · intro h η hη
    obtain ⟨C, hC, D, hD, hCB, hBD, hlt⟩ := h η hη
    exact ⟨C, hC, D, hD, hCB, hBD, lt_const_of_loebSh_lt hlt⟩
  · intro h η hη
    obtain ⟨C, hC, D, hD, hCB, hBD, hlt⟩ := h (η / 2) (by positivity)
    refine ⟨C, hC, D, hD, hCB, hBD, lt_of_le_of_lt (loebSh_le_of_le_const hlt.le) ?_⟩
    rw [ENNReal.ofReal_lt_ofReal_iff hη]
    linarith

end InternalMeasure

/-!
## Weighted counting measures on hyperfinite sets

The examples of Section 16.2: on a hyperfinite set $`S = [S_n]`, an internal weighting
$`w = [w_n]` defines the internal measure that sends an internal subset $`A = [A_n]` of
$`S` to the hyperfinite sum of the weights of its points, the class of the sums
$`\sum_{x \in A_n} w_n(x)`. Its ring is the algebra of all internal subsets of $`S`. The
uniform weighting $`1/|S|` gives the normalised counting measure $`|A|/|S|`.
-/

section Weighted

variable {β βS : Type u} [StarType β βS]

/-- A sum of a constant over the points of a finite set that lie in $`B` is the number of
those points times the constant. -/
theorem sum_indicator_const (s : Finset β) (B : Set β) (c : ℝ≥0∞) :
    ∑ x ∈ s, B.indicator (fun _ => c) x = ((↑s ∩ B : Set β).ncard : ℝ≥0∞) * c := by
  classical
  have hfin : (↑s ∩ B : Set β).Finite := s.finite_toSet.subset inter_subset_left
  have h1 : ∑ x ∈ s, B.indicator (fun _ => c) x = ∑ _x ∈ hfin.toFinset, c := by
    rw [← Finset.sum_subset (s₁ := hfin.toFinset) (fun x hx => (hfin.mem_toFinset.1 hx).1)
      (fun x hx hx' => Set.indicator_of_notMem
        (fun hxB => hx' (hfin.mem_toFinset.2 ⟨hx, hxB⟩)) _)]
    exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (hfin.mem_toFinset.1 hx).2 _
  rw [h1, Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card _ hfin]

/-- **Section 16.2, example 5.** The _weighted counting function_ $`\mu_w` on the internal
subsets of the hyperfinite set $`S = [S_n]`, for the internal weighting $`w = [w_n]`:
$`\mu_w(A) = \sum_{s \in A} w(s)`. -/
noncomputable def InternalMeasure.weighted (s : ℕ → Finset β) (w : ℕ → β → ℝ≥0∞) :
    InternalMeasure β where
  𝔄 n := {B | B ⊆ ↑(s n)}
  m n B := ∑ x ∈ s n, B.indicator (w n) x
  isRing n := ⟨⟨∅, empty_subset _⟩, fun _ _ hA _ => sdiff_subset.trans hA,
    fun _ _ hA hB => union_subset hA hB⟩
  isFinitelyAdditive n := ⟨by simp, fun A B _ _ hAB => by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ =>
      congrFun (Set.indicator_union_of_disjoint hAB (w n)) x⟩

/-- **Section 16.2, example 5.** The ring of the weighted counting function is the algebra
$`\mathcal P_I(S)` of all internal subsets of $`S`. -/
theorem InternalMeasure.mem_sets_weighted_iff {s : ℕ → Finset β} {w : ℕ → β → ℝ≥0∞}
    {X : Set βS} :
    X ∈ (InternalMeasure.weighted s w).sets ↔
      IsInternalSet β X ∧ X ⊆ internalSet fun n => (s n : Set β) := by
  constructor
  · rintro ⟨B, rfl, hB⟩
    exact ⟨⟨B, rfl⟩, internalSet_subset_iff.2 hB⟩
  · rintro ⟨⟨B, rfl⟩, hsub⟩
    exact ⟨B, rfl, internalSet_subset_iff.1 hsub⟩

/-- **Section 16.2, example 5.** The hyperfinite set $`S` itself belongs to the ring: the
internal subsets of $`S` form an algebra of subsets of $`S`. -/
theorem InternalMeasure.internalSet_mem_sets_weighted (s : ℕ → Finset β) (w : ℕ → β → ℝ≥0∞) :
    (internalSet (fun n => (s n : Set β)) : Set βS) ∈ (InternalMeasure.weighted s w).sets :=
  ⟨_, rfl, Eventually.of_forall fun _ => Subset.rfl⟩

/-- **Section 16.2, example 5.** Every internal finitely additive function on the internal
subsets of a hyperfinite set is a weighted counting function, with weights
$`w(s) = \mu(\{s\})`: for each index, the measure of a subset of the finite set is the sum of
the measures of its singletons. -/
theorem InternalMeasure.m_eq_sum_singleton (I : InternalMeasure β) (s : ℕ → Finset β)
    (h𝔄 : ∀ n, I.𝔄 n = {B | B ⊆ ↑(s n)}) (n : ℕ) {B : Set β} (hB : B ⊆ ↑(s n)) :
    I.m n B = ∑ x ∈ s n, B.indicator (fun x => I.m n {x}) x := by
  classical
  have hfin : B.Finite := (s n).finite_toSet.subset hB
  have hB' : B = ⋃ x ∈ hfin.toFinset, ({x} : Set β) := by
    ext x; simp
  have hsing : ∀ x ∈ hfin.toFinset, ({x} : Set β) ∈ I.𝔄 n := fun x hx => by
    rw [h𝔄 n]
    exact singleton_subset_iff.2 (hB (hfin.mem_toFinset.1 hx))
  have h1 : I.m n B = ∑ x ∈ hfin.toFinset, I.m n {x} := by
    conv_lhs => rw [hB']
    exact (I.isFinitelyAdditive n).biUnion_finset (I.isRing n) _ hsing
      (fun x _ y _ hxy => disjoint_singleton.2 hxy)
  rw [h1, ← Finset.sum_subset (s₁ := hfin.toFinset) (fun x hx => hB (hfin.mem_toFinset.1 hx))
    (fun x _ hx' => Set.indicator_of_notMem (fun hxB => hx' (hfin.mem_toFinset.2 hxB)) _)]
  exact Finset.sum_congr rfl fun x hx =>
    (Set.indicator_of_mem (hfin.mem_toFinset.1 hx) (fun x => I.m n {x})).symm

/-- **Section 16.2, example 3.** The normalised counting measure $`\mu(A) = |A|/|S|` on the
internal subsets of a hyperfinite set $`S = [S_n]`: the weighted counting function with the
uniform weight $`1/|S|`. -/
noncomputable def InternalMeasure.counting (s : ℕ → Finset β) : InternalMeasure β :=
  InternalMeasure.weighted s fun n _ => ((s n).card : ℝ≥0∞)⁻¹

/-- **Section 16.2, example 3.** For the normalised counting measure on a nonempty hyperfinite
set $`S`, $`\mu_L(S) = 1`. -/
theorem InternalMeasure.μL_counting_univ {s : ℕ → Finset β}
    (hs : ∀ᶠ n in hyperfilter ℕ, (s n).Nonempty) :
    (InternalMeasure.counting s).μL (internalSet (fun n => (s n : Set β)) : Set βS) = 1 := by
  refine tendsto_nhds_unique ((InternalMeasure.counting s).tendsto_μL _)
    (tendsto_const_nhds.congr' ?_)
  filter_upwards [hs] with n hn
  change (1 : ℝ≥0∞) = ∑ x ∈ s n, (s n : Set β).indicator (fun _ => ((s n).card : ℝ≥0∞)⁻¹) x
  rw [sum_indicator_const, inter_self, Set.ncard_coe_finset,
    ENNReal.mul_inv_cancel (by exact_mod_cast hn.card_ne_zero) (ENNReal.natCast_ne_top _)]

/-- **Section 16.2, example 3.** The normalised counting measure takes values between $`0` and
$`1`: $`\mu_L(A) \le 1` for every internal subset $`A` of $`S`. -/
theorem InternalMeasure.μL_counting_le_one {s : ℕ → Finset β} (B : ℕ → Set β) :
    (InternalMeasure.counting s).μL (internalSet B : Set βS) ≤ 1 := by
  refine le_of_tendsto ((InternalMeasure.counting s).tendsto_μL B) (Eventually.of_forall fun n => ?_)
  change ∑ x ∈ s n, (B n).indicator (fun _ => ((s n).card : ℝ≥0∞)⁻¹) x ≤ 1
  rw [sum_indicator_const]
  rcases (s n).eq_empty_or_nonempty with h | h
  · simp [h]
  · calc ((↑(s n) ∩ B n : Set β).ncard : ℝ≥0∞) * ((s n).card : ℝ≥0∞)⁻¹
        ≤ ((s n).card : ℝ≥0∞) * ((s n).card : ℝ≥0∞)⁻¹ := by
          gcongr
          rw [← Set.ncard_coe_finset (s n)]
          exact Set.ncard_le_ncard inter_subset_left (s n).finite_toSet
      _ = 1 := ENNReal.mul_inv_cancel (by exact_mod_cast h.card_ne_zero)
          (ENNReal.natCast_ne_top _)

end Weighted

/-!
## The algebra of internal subsets of a hyperfinite set is not a sigma-algebra

Example 5 of Section 16.1: the internal subsets of $`S = \{1, \dots, N\}`, for an unlimited
hypernatural $`N`, form an algebra of subsets of $`S` that is not closed under countable
unions, because it contains every singleton $`\{n\}` of a standard positive integer but not
their union, the external set of standard positive integers.
-/

/-- **Section 16.1, example 5.** For an unlimited hypernatural $`N`, the collection
$`\mathcal P_I(S)` of internal subsets of $`S = \{1, \dots, N\}` is a ring that contains
$`S`. -/
theorem isRingOfSets_internal_subsets (S : Set ℝ*) :
    IsRingOfSets {X : Set ℝ* | IsInternal X ∧ X ⊆ S} :=
  ⟨⟨∅, isInternal_empty, empty_subset _⟩,
    fun _ _ hA hB => ⟨hA.1.diff hB.1, sdiff_subset.trans hA.2⟩,
    fun _ _ hA hB => ⟨hA.1.union hB.1, union_subset hA.2 hB.2⟩⟩

/-- **Section 16.1, example 5.** For an unlimited hypernatural $`N`, the algebra of internal
subsets of $`S = \{1, \dots, N\}` is not a sigma-ring: the union of the singletons of the
standard positive integers is countably infinite, so it is not internal. -/
theorem not_isSigmaRing_internal_subsets {N : ℝ*} (hN : N ∈ ℕ*) (hU : Unlimited N) :
    ¬ IsSigmaRing {X : Set ℝ* | IsInternal X ∧ X ⊆ {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ N}} := by
  intro h
  have hmem := h.iUnion_mem (A := fun n : ℕ => {((n + 1 : ℕ) : ℝ*)}) fun n =>
    ⟨isInternal_singleton _, singleton_subset_iff.2
      (natCast_mem_setOf_hyperNat_one_le_le hN hU (Nat.succ_le_succ (Nat.zero_le n)))⟩
  have hc : (⋃ n : ℕ, ({((n + 1 : ℕ) : ℝ*)} : Set ℝ*)).Countable :=
    countable_iUnion fun _ => countable_singleton _
  have hfin := IsInternalSet.finite_of_countable hmem.1 hc
  have hinf : (⋃ n : ℕ, ({((n + 1 : ℕ) : ℝ*)} : Set ℝ*)).Infinite := by
    have : ⋃ n : ℕ, ({((n + 1 : ℕ) : ℝ*)} : Set ℝ*) = range fun n : ℕ => ((n + 1 : ℕ) : ℝ*) := by
      ext x; simp [eq_comm]
    rw [this]
    exact infinite_range_of_injective fun m n hmn => by
      have : (m + 1 : ℕ) = n + 1 := Nat.cast_injective hmn
      omega
  exact hinf hfin

end Goldblatt
