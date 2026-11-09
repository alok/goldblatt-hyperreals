import Goldblatt.Ch06_Sequences.Convergence

/-!
# 6 (part 2). Limits Superior and Inferior: Sections 6.8 and 6.9

This is the second of three parts of Chapter 6 (the overview is on the chapter page
{lit}`Goldblatt.Ch06_Sequences`). It defines the limit superior and the limit inferior of a
bounded real sequence as the largest and the smallest cluster point, that is, as the largest
and the smallest shadow of an extended term, proves the book's theorems about them, extends
the definitions to arbitrary sequences with values in the extended reals, and shows that
these definitions agree with Mathlib's.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## 6.8 Limits Superior and Inferior

Let $`s` be a bounded real sequence and $`C_s` its set of cluster points. By Theorem 6.6.1
this is the set of shadows of the extended terms. It is nonempty by the Bolzano-Weierstrass
theorem, and every bound of the sequence is a bound of $`C_s`. Its supremum is the _limit
superior_ of $`s` and its infimum is the _limit inferior_. Both are themselves cluster points
(Exercise 6.8.1), so they are the largest and the smallest cluster point.

The theorems of the section are proved from this description: a characterisation of the limit
superior by the extended terms (Theorem 6.8.2), convergence as equality of the two limits
(Theorem 6.8.3), the approximation properties (Theorem 6.8.4), and the classical formula as
the limit of the suprema of the tails (Theorem 6.8.5). The section ends with the definition
for unbounded sequences. Each definition is compared with Mathlib's {name}`Filter.limsup`.
-/

section LimSup

variable {s : ℕ → ℝ} {L : ℝ} {N : ℝ*}

/-- A bounded sequence is bounded above. -/
theorem bddAbove_range_of_bounded (hb : ∃ b : ℝ, ∀ n, |s n| < b) : BddAbove (range s) := by
  obtain ⟨b, hb⟩ := hb
  exact ⟨b, by rintro _ ⟨n, rfl⟩; exact (abs_lt.1 (hb n)).2.le⟩

/-- A bounded sequence is bounded below. -/
theorem bddBelow_range_of_bounded (hb : ∃ b : ℝ, ∀ n, |s n| < b) : BddBelow (range s) := by
  obtain ⟨b, hb⟩ := hb
  exact ⟨-b, by rintro _ ⟨n, rfl⟩; exact (abs_lt.1 (hb n)).1.le⟩

/-- The sequence of negatives of a bounded sequence is bounded. -/
theorem bounded_neg (hb : ∃ b : ℝ, ∀ n, |s n| < b) : ∃ b : ℝ, ∀ n, |(fun n => -s n) n| < b := by
  simpa using hb

/-- **Section 6.8.** Every real upper bound of a sequence is an upper bound of its set of
cluster points. -/
theorem bddAbove_clusterSet (hb : BddAbove (range s)) : BddAbove (clusterSet s) := by
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, fun c hc => ?_⟩
  obtain ⟨N, -, h⟩ := mem_clusterSet_iff.1 hc
  exact coe_le_coe_of_infClose_le h.symm (hyperSeq_le_coe (fun n => hb ⟨n, rfl⟩) N)

/-- **Section 6.8.** Every real lower bound of a sequence is a lower bound of its set of
cluster points. -/
theorem bddBelow_clusterSet (hb : BddBelow (range s)) : BddBelow (clusterSet s) := by
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, fun c hc => ?_⟩
  obtain ⟨N, -, h⟩ := mem_clusterSet_iff.1 hc
  exact coe_le_coe_of_le_infClose (coe_le_hyperSeq (fun n => hb ⟨n, rfl⟩) N) h

/-- **Section 6.8.** A bounded sequence has a cluster point (Theorem 6.6.2). -/
theorem clusterSet_nonempty_of_bounded (hb : ∃ b : ℝ, ∀ n, |s n| < b) :
    (clusterSet s).Nonempty :=
  exists_mapClusterPt_of_bounded hb

/-- The cluster points of the sequence of negatives are the negatives of the cluster points.
-/
theorem mem_clusterSet_neg_iff : L ∈ clusterSet (fun n => -s n) ↔ -L ∈ clusterSet s := by
  rw [mem_clusterSet_iff, mem_clusterSet_iff]
  refine exists_congr fun N => and_congr_right fun _ => ?_
  rw [hyperSeq_neg, Hyperreal.coe_neg]
  constructor
  · intro h
    simpa using h.neg
  · intro h
    simpa using h.neg

/-- The set of cluster points of the sequence of negatives. -/
theorem clusterSet_neg (s : ℕ → ℝ) : clusterSet (fun n => -s n) = -clusterSet s := by
  ext L
  rw [mem_clusterSet_neg_iff, Set.mem_neg]

/-- **Section 6.8, definition.** The _limit superior_ of a bounded real sequence is the least
upper bound of its set of cluster points:
$`\limsup s_n = \sup\{\operatorname{sh}(s_N) : N \text{ unlimited}\}`. For an unbounded
sequence this real number has no significance; the general definition is
{lit}`limSupE`. -/
def limSup (s : ℕ → ℝ) : ℝ := sSup (clusterSet s)

/-- **Section 6.8, definition.** The _limit inferior_ of a bounded real sequence is the
greatest lower bound of its set of cluster points:
$`\liminf s_n = \inf\{\operatorname{sh}(s_N) : N \text{ unlimited}\}`. -/
def limInf (s : ℕ → ℝ) : ℝ := sInf (clusterSet s)

/-- **Section 6.8.** For a bounded sequence the limit superior is the supremum of the shadows
of the extended terms. -/
theorem limSup_eq_sSup_image_sh (hb : ∃ b : ℝ, ∀ n, |s n| < b) :
    limSup s = sSup ((fun N => sh (hyperSeq s N)) '' unlimitedHyperNat) := by
  rw [limSup, clusterSet_eq_image_sh hb]

/-- **Section 6.8.** For a bounded sequence the limit inferior is the infimum of the shadows
of the extended terms. -/
theorem limInf_eq_sInf_image_sh (hb : ∃ b : ℝ, ∀ n, |s n| < b) :
    limInf s = sInf ((fun N => sh (hyperSeq s N)) '' unlimitedHyperNat) := by
  rw [limInf, clusterSet_eq_image_sh hb]

/-- The limit inferior is minus the limit superior of the sequence of negatives. -/
theorem limInf_eq_neg_limSup_neg (s : ℕ → ℝ) : limInf s = -limSup fun n => -s n := by
  rw [limInf, limSup, clusterSet_neg, Real.sInf_def]

/-- The limit superior is minus the limit inferior of the sequence of negatives. -/
theorem limSup_eq_neg_limInf_neg (s : ℕ → ℝ) : limSup s = -limInf fun n => -s n := by
  rw [limInf_eq_neg_limSup_neg]
  simp

/-- **Section 6.8.** The shadow of every extended term of a bounded sequence is at most the
limit superior. -/
theorem sh_hyperSeq_le_limSup (hb : ∃ b : ℝ, ∀ n, |s n| < b) (hN : N ∈ unlimitedHyperNat) :
    sh (hyperSeq s N) ≤ limSup s :=
  le_csSup (bddAbove_clusterSet (bddAbove_range_of_bounded hb))
    (sh_hyperSeq_mem_clusterSet hN (bounded_iff_forall_unlimited_limited.1 hb N hN))

/-- **Section 6.8.** The shadow of every extended term of a bounded sequence is at least the
limit inferior. -/
theorem limInf_le_sh_hyperSeq (hb : ∃ b : ℝ, ∀ n, |s n| < b) (hN : N ∈ unlimitedHyperNat) :
    limInf s ≤ sh (hyperSeq s N) :=
  csInf_le (bddBelow_clusterSet (bddBelow_range_of_bounded hb))
    (sh_hyperSeq_mem_clusterSet hN (bounded_iff_forall_unlimited_limited.1 hb N hN))

/-- **Section 6.8, principle (a) at work.** If a sequence is bounded above and every cluster
point is below the real number $`r`, then some standard tail of the sequence is below $`r`.
An extended term is not positive unlimited; if it is negative unlimited it is below $`r`, and
otherwise it is limited with shadow a cluster point, hence below $`r`. -/
theorem eventually_lt_of_forall_clusterSet_lt {r : ℝ} (hb : BddAbove (range s))
    (hr : ∀ c ∈ clusterSet s, c < r) : ∀ᶠ n in atTop, s n < r := by
  rw [← forall_unlimited_hyperSeq_lt_iff]
  intro N hN
  have hpos := bddAbove_range_iff_forall_unlimited_not_posUnlimited.1 hb N hN
  by_cases hneg : NegUnlimited (hyperSeq s N)
  · exact hneg r
  · have hl : Limited (hyperSeq s N) :=
      limited_iff_not_posUnlimited_and_not_negUnlimited.2 ⟨hpos, hneg⟩
    exact hl.lt_of_sh_lt (hr _ (sh_hyperSeq_mem_clusterSet hN hl))

/-- The mirror image of {lit}`eventually_lt_of_forall_clusterSet_lt`: if a sequence is bounded
below and every cluster point is above $`r`, then some standard tail is above $`r`. -/
theorem eventually_gt_of_forall_clusterSet_gt {r : ℝ} (hb : BddBelow (range s))
    (hr : ∀ c ∈ clusterSet s, r < c) : ∀ᶠ n in atTop, r < s n := by
  rw [← forall_unlimited_lt_hyperSeq_iff]
  intro N hN
  have hneg := bddBelow_range_iff_forall_unlimited_not_negUnlimited.1 hb N hN
  by_cases hpos : PosUnlimited (hyperSeq s N)
  · exact hpos r
  · have hl : Limited (hyperSeq s N) :=
      limited_iff_not_posUnlimited_and_not_negUnlimited.2 ⟨hpos, hneg⟩
    exact hl.lt_of_lt_sh (hr _ (sh_hyperSeq_mem_clusterSet hN hl))

/-- **Section 6.8, principle (b) at work.** If $`c` is a cluster point and $`r < c`, then
$`r < s_n` for arbitrarily large $`n`: an extended term with shadow $`c` is above $`r`. -/
theorem frequently_gt_of_mem_clusterSet {c r : ℝ} (hc : c ∈ clusterSet s) (hr : r < c) :
    ∃ᶠ n in atTop, r < s n := by
  rw [← exists_unlimited_lt_hyperSeq_iff]
  obtain ⟨N, hN, h⟩ := mem_clusterSet_iff.1 hc
  exact ⟨N, hN, (limited_of_infClose_coe h).lt_of_lt_sh (by rwa [sh_eq_of_infClose h])⟩

/-- The mirror image of {lit}`frequently_gt_of_mem_clusterSet`: if $`c` is a cluster point and
$`c < r`, then $`s_n < r` for arbitrarily large $`n`. -/
theorem frequently_lt_of_mem_clusterSet {c r : ℝ} (hc : c ∈ clusterSet s) (hr : c < r) :
    ∃ᶠ n in atTop, s n < r := by
  rw [← exists_unlimited_hyperSeq_lt_iff]
  obtain ⟨N, hN, h⟩ := mem_clusterSet_iff.1 hc
  exact ⟨N, hN, (limited_of_infClose_coe h).lt_of_sh_lt (by rwa [sh_eq_of_infClose h])⟩

/-- **Exercise 6.8.1, limit superior.** The limit superior of a bounded sequence is a cluster
point of the sequence. Given a positive real $`e`, there is a cluster point $`c` with
$`\Lambda - e < c \le \Lambda`, where $`\Lambda` is the limit superior. It is the shadow of an
extended term, which therefore lies in the enlargement of $`(\Lambda - e, \Lambda + e)`. By
principle (b) this interval contains terms of arbitrarily large standard index. -/
theorem limSup_mem_clusterSet (hb : ∃ b : ℝ, ∀ n, |s n| < b) : limSup s ∈ clusterSet s := by
  have hA := bddAbove_clusterSet (bddAbove_range_of_bounded hb)
  change MapClusterPt (limSup s) atTop s
  rw [mapClusterPt_iff_forall_exists]
  intro e he m
  obtain ⟨c, hc, hlt⟩ := exists_lt_of_lt_csSup (clusterSet_nonempty_of_bounded hb)
    (show limSup s - e < sSup (clusterSet s) by rw [← limSup]; linarith)
  have hle : c ≤ limSup s := le_csSup hA hc
  obtain ⟨N, hN, h⟩ := mem_clusterSet_iff.1 hc
  have hl := limited_of_infClose_coe h
  have hsh := sh_eq_of_infClose h
  have hf : ∃ᶠ n in atTop, s n ∈ Ioo (limSup s - e) (limSup s + e) := by
    rw [← exists_unlimited_hyperSeq_mem_starSet_iff, starSet_Ioo_real]
    exact ⟨N, hN, hl.lt_of_lt_sh (by rw [hsh]; exact hlt),
      hl.lt_of_sh_lt (by rw [hsh]; linarith)⟩
  obtain ⟨n, hn, hn1, hn2⟩ := frequently_atTop.1 hf (m + 1)
  exact ⟨n, hn, abs_lt.2 ⟨by linarith, by linarith⟩⟩

/-- **Exercise 6.8.1, limit inferior.** The limit inferior of a bounded sequence is a cluster
point of the sequence. -/
theorem limInf_mem_clusterSet (hb : ∃ b : ℝ, ∀ n, |s n| < b) : limInf s ∈ clusterSet s := by
  have h := limSup_mem_clusterSet (bounded_neg hb)
  rwa [mem_clusterSet_neg_iff, ← limInf_eq_neg_limSup_neg] at h

/-- **Section 6.8.** The limit superior of a bounded sequence is the maximum of its set of
cluster points. -/
theorem isGreatest_limSup (hb : ∃ b : ℝ, ∀ n, |s n| < b) :
    IsGreatest (clusterSet s) (limSup s) :=
  ⟨limSup_mem_clusterSet hb, fun _ hc =>
    le_csSup (bddAbove_clusterSet (bddAbove_range_of_bounded hb)) hc⟩

/-- **Section 6.8.** The limit inferior of a bounded sequence is the minimum of its set of
cluster points. -/
theorem isLeast_limInf (hb : ∃ b : ℝ, ∀ n, |s n| < b) : IsLeast (clusterSet s) (limInf s) :=
  ⟨limInf_mem_clusterSet hb, fun _ hc =>
    csInf_le (bddBelow_clusterSet (bddBelow_range_of_bounded hb)) hc⟩

/-- The limit inferior of a bounded sequence is at most its limit superior. -/
theorem limInf_le_limSup (hb : ∃ b : ℝ, ∀ n, |s n| < b) : limInf s ≤ limSup s :=
  (isLeast_limInf hb).2 (limSup_mem_clusterSet hb)

/-- **Theorem 6.8.2.** For a bounded real sequence $`s`, a real number $`L` equals the limit
superior of $`s` if and only if (1) $`s_N < L` or $`s_N \simeq L` for every unlimited $`N`,
and (2) $`s_N \simeq L` for at least one unlimited $`N`. -/
theorem eq_limSup_iff (hb : ∃ b : ℝ, ∀ n, |s n| < b) :
    L = limSup s ↔
      (∀ N ∈ unlimitedHyperNat, hyperSeq s N < L ∨ hyperSeq s N ≊ (L : ℝ*)) ∧
        ∃ N ∈ unlimitedHyperNat, hyperSeq s N ≊ (L : ℝ*) := by
  constructor
  · rintro rfl
    refine ⟨fun N hN => ?_, mem_clusterSet_iff.1 (limSup_mem_clusterSet hb)⟩
    have hl := bounded_iff_forall_unlimited_limited.1 hb N hN
    rcases (sh_hyperSeq_le_limSup hb hN).lt_or_eq with h | h
    · exact Or.inl (hl.lt_of_sh_lt h)
    · right
      rw [← h]
      exact hl.infClose_sh
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · exact (isGreatest_limSup hb).2 (mem_clusterSet_iff.2 h2)
    · obtain ⟨N, hN, h⟩ := mem_clusterSet_iff.1 (limSup_mem_clusterSet hb)
      rcases h1 N hN with h' | h'
      · exact coe_le_coe_of_infClose_le h.symm h'.le
      · exact (infClose_coe_iff.1 (h.symm.trans h')).le

/-- **Theorem 6.8.2, limit inferior** (the formulation that the book leaves as an exercise).
For a bounded real sequence $`s`, a real number $`L` equals the limit inferior of $`s` if and
only if (1) $`L < s_N` or $`s_N \simeq L` for every unlimited $`N`, and (2)
$`s_N \simeq L` for at least one unlimited $`N`. -/
theorem eq_limInf_iff (hb : ∃ b : ℝ, ∀ n, |s n| < b) :
    L = limInf s ↔
      (∀ N ∈ unlimitedHyperNat, (L : ℝ*) < hyperSeq s N ∨ hyperSeq s N ≊ (L : ℝ*)) ∧
        ∃ N ∈ unlimitedHyperNat, hyperSeq s N ≊ (L : ℝ*) := by
  constructor
  · rintro rfl
    refine ⟨fun N hN => ?_, mem_clusterSet_iff.1 (limInf_mem_clusterSet hb)⟩
    have hl := bounded_iff_forall_unlimited_limited.1 hb N hN
    rcases (limInf_le_sh_hyperSeq hb hN).lt_or_eq with h | h
    · exact Or.inl (hl.lt_of_lt_sh h)
    · right
      rw [h]
      exact hl.infClose_sh
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · obtain ⟨N, hN, h⟩ := mem_clusterSet_iff.1 (limInf_mem_clusterSet hb)
      rcases h1 N hN with h' | h'
      · exact coe_le_coe_of_le_infClose h'.le h
      · exact (infClose_coe_iff.1 (h'.symm.trans h)).le
    · exact (isLeast_limInf hb).2 (mem_clusterSet_iff.2 h2)

/-- **Theorem 6.8.3.** A bounded real sequence converges to $`L` if and only if its limit
superior and its limit inferior are both equal to $`L`. -/
theorem tendsto_iff_limSup_eq_and_limInf_eq (hb : ∃ b : ℝ, ∀ n, |s n| < b) :
    Tendsto s atTop (𝓝 L) ↔ limSup s = L ∧ limInf s = L := by
  constructor
  · intro hT
    have key : ∀ c ∈ clusterSet s, c = L := fun c hc => by
      obtain ⟨N, hN, h⟩ := mem_clusterSet_iff.1 hc
      exact infClose_coe_iff.1 (h.symm.trans (hyperSeq_infClose_of_tendsto hT hN))
    exact ⟨key _ (limSup_mem_clusterSet hb), key _ (limInf_mem_clusterSet hb)⟩
  · rintro ⟨h1, h2⟩
    rw [tendsto_iff_forall_unlimited_infClose]
    intro N hN
    have hl := bounded_iff_forall_unlimited_limited.1 hb N hN
    have : sh (hyperSeq s N) = L :=
      le_antisymm (h1 ▸ sh_hyperSeq_le_limSup hb hN) (h2 ▸ limInf_le_sh_hyperSeq hb hN)
    rw [← this]
    exact hl.infClose_sh

/-- **Theorem 6.8.4 (1).** For a bounded real sequence and a positive real $`e`, some standard
tail of the sequence lies below $`\limsup s + e`: every extended term has shadow at most the
limit superior, so it is below $`\limsup s + e`, and principle (a) applies. -/
theorem eventually_lt_limSup_add (hb : ∃ b : ℝ, ∀ n, |s n| < b) {e : ℝ} (he : 0 < e) :
    ∀ᶠ n in atTop, s n < limSup s + e :=
  eventually_lt_of_forall_clusterSet_lt (bddAbove_range_of_bounded hb) fun c hc => by
    linarith [(isGreatest_limSup hb).2 hc]

/-- **Theorem 6.8.4 (1)**, as a statement about finite sets: $`s_n < \limsup s + e` for all but
finitely many $`n`. -/
theorem finite_setOf_limSup_add_le (hb : ∃ b : ℝ, ∀ n, |s n| < b) {e : ℝ} (he : 0 < e) :
    {n | limSup s + e ≤ s n}.Finite := by
  have h := eventually_lt_limSup_add hb he
  rw [← Nat.cofinite_eq_atTop, eventually_cofinite] at h
  simpa using h

/-- **Theorem 6.8.4 (2).** For a bounded real sequence and a positive real $`e`,
$`\limsup s - e < s_n` for arbitrarily large $`n`: the limit superior is the shadow of an
extended term, which is above $`\limsup s - e`, and principle (b) applies. -/
theorem frequently_limSup_sub_lt (hb : ∃ b : ℝ, ∀ n, |s n| < b) {e : ℝ} (he : 0 < e) :
    ∃ᶠ n in atTop, limSup s - e < s n :=
  frequently_gt_of_mem_clusterSet (limSup_mem_clusterSet hb) (by linarith)

/-- **Theorem 6.8.4 (2)**, as a statement about infinite sets: $`\limsup s - e < s_n` for
infinitely many $`n`. -/
theorem infinite_setOf_limSup_sub_lt (hb : ∃ b : ℝ, ∀ n, |s n| < b) {e : ℝ} (he : 0 < e) :
    {n | limSup s - e < s n}.Infinite :=
  Nat.frequently_atTop_iff_infinite.1 (frequently_limSup_sub_lt hb he)

/-- **Section 6.8.** The supremum $`S_n = \sup_{m \ge n} s_m` of the standard tail of the
sequence that starts at $`n`. -/
def tailSup (s : ℕ → ℝ) (n : ℕ) : ℝ := sSup (s '' Ici n)

/-- A term of the tail is at most the supremum of the tail. -/
theorem le_tailSup (hb : BddAbove (range s)) {m n : ℕ} (h : n ≤ m) : s m ≤ tailSup s n :=
  le_csSup (hb.mono (image_subset_range _ _)) ⟨m, h, rfl⟩

/-- **Section 6.8.** The sequence of tail suprema is nonincreasing. -/
theorem tailSup_antitone (hb : BddAbove (range s)) : Antitone (tailSup s) := fun _ _ h =>
  csSup_le_csSup (hb.mono (image_subset_range _ _)) (nonempty_Ici.image _)
    (image_mono (Ici_subset_Ici.2 h))

/-- **Theorem 6.8.5.** For a bounded real sequence $`s`, the suprema of the tails converge to
the limit superior:
$$`\limsup_{n\to\infty} s_n = \lim_{n\to\infty} \Bigl(\sup_{m \ge n} s_m\Bigr).`
The tail suprema are nonincreasing and bounded below, so they converge to their greatest lower
bound $`L` by Theorem 6.2.1. The limit superior is the shadow of an extended term $`s_N`, and
$`s_N \le S_m` for every standard $`m` by transfer, so the limit superior is a lower bound of
the tail suprema and is at most $`L`. If it were smaller, Theorem 6.8.4 (1) would give a tail
whose supremum is below $`L`. -/
theorem tendsto_tailSup_limSup (hb : ∃ b : ℝ, ∀ n, |s n| < b) :
    Tendsto (tailSup s) atTop (𝓝 (limSup s)) := by
  have hA := bddAbove_range_of_bounded hb
  obtain ⟨l, hl⟩ := bddBelow_range_of_bounded hb
  have hbelow : BddBelow (range (tailSup s)) :=
    ⟨l, by rintro _ ⟨n, rfl⟩; exact (hl ⟨n, rfl⟩).trans (le_tailSup hA le_rfl)⟩
  obtain ⟨L, hglb, hL⟩ := Antitone.exists_isGLB_tendsto (tailSup_antitone hA) hbelow
  have hii : ∀ m, limSup s ≤ tailSup s m := by
    intro m
    obtain ⟨N, hN, h⟩ := mem_clusterSet_iff.1 (limSup_mem_clusterSet hb)
    refine coe_le_coe_of_infClose_le h.symm ?_
    obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
    rw [hyperSeq_hnat, coe_eq_ofSeq_const, ofSeq_le_ofSeq_iff]
    exact (tendsto_atTop.1 hk m).mono fun n hn => le_tailSup hA hn
  have h1 : limSup s ≤ L := hglb.2 (by rintro _ ⟨m, rfl⟩; exact hii m)
  have h2 : L ≤ limSup s := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n0, hn0⟩ :=
      eventually_atTop.1 (eventually_lt_limSup_add hb (half_pos (sub_pos.2 hlt)))
    have h3 : tailSup s n0 ≤ limSup s + (L - limSup s) / 2 :=
      csSup_le (nonempty_Ici.image _) (by rintro _ ⟨m, hm, rfl⟩; exact (hn0 m hm).le)
    have h4 : L ≤ tailSup s n0 := hglb.1 ⟨n0, rfl⟩
    linarith
  rwa [le_antisymm h1 h2]

/-- **Theorem 6.8.5**, infimum form: the limit superior of a bounded sequence is the greatest
lower bound of its tail suprema. -/
theorem limSup_eq_iInf_tailSup (hb : ∃ b : ℝ, ∀ n, |s n| < b) :
    limSup s = ⨅ n, tailSup s n := by
  have hA := bddAbove_range_of_bounded hb
  obtain ⟨l, hl⟩ := bddBelow_range_of_bounded hb
  have hbelow : BddBelow (range (tailSup s)) :=
    ⟨l, by rintro _ ⟨n, rfl⟩; exact (hl ⟨n, rfl⟩).trans (le_tailSup hA le_rfl)⟩
  obtain ⟨L, hglb, hL⟩ := Antitone.exists_isGLB_tendsto (tailSup_antitone hA) hbelow
  rw [limit_unique (tendsto_tailSup_limSup hb) hL]
  exact (hglb.csInf_eq (range_nonempty _)).symm

/-- **Section 6.8, agreement with Mathlib.** For a bounded real sequence the limit superior
defined from cluster points is Mathlib's {name}`Filter.limsup` along {name}`Filter.atTop`. -/
theorem limSup_eq_limsup (hb : ∃ b : ℝ, ∀ n, |s n| < b) : limSup s = limsup s atTop := by
  obtain ⟨u, hu⟩ := bddAbove_range_of_bounded hb
  obtain ⟨l, hl⟩ := bddBelow_range_of_bounded hb
  have h2 : IsBoundedUnder (· ≤ ·) atTop s := isBoundedUnder_of ⟨u, fun n => hu ⟨n, rfl⟩⟩
  have h1 : IsCoboundedUnder (· ≤ ·) atTop s :=
    (isBoundedUnder_of ⟨l, fun n => hl ⟨n, rfl⟩⟩ :
      IsBoundedUnder (· ≥ ·) atTop s).isCoboundedUnder_le
  apply le_antisymm
  · rw [le_limsup_iff' h1 h2]
    intro y hy
    exact (frequently_limSup_sub_lt hb (sub_pos.2 hy)).mono fun n hn => by linarith
  · rw [limsup_le_iff' h1 h2]
    intro y hy
    exact (eventually_lt_limSup_add hb (sub_pos.2 hy)).mono fun n hn => by linarith

/-- **Section 6.8, agreement with Mathlib.** For a bounded real sequence the limit inferior
defined from cluster points is Mathlib's {name}`Filter.liminf` along {name}`Filter.atTop`. -/
theorem limInf_eq_liminf (hb : ∃ b : ℝ, ∀ n, |s n| < b) : limInf s = liminf s atTop := by
  obtain ⟨u, hu⟩ := bddAbove_range_of_bounded hb
  obtain ⟨l, hl⟩ := bddBelow_range_of_bounded hb
  have h2 : IsBoundedUnder (· ≥ ·) atTop s := isBoundedUnder_of ⟨l, fun n => hl ⟨n, rfl⟩⟩
  have h1 : IsCoboundedUnder (· ≥ ·) atTop s :=
    (isBoundedUnder_of ⟨u, fun n => hu ⟨n, rfl⟩⟩ :
      IsBoundedUnder (· ≤ ·) atTop s).isCoboundedUnder_ge
  have hmem := limInf_mem_clusterSet hb
  have hleast := isLeast_limInf hb
  apply le_antisymm
  · rw [le_liminf_iff' h1 h2]
    intro y hy
    exact (eventually_gt_of_forall_clusterSet_gt ⟨l, hl⟩
      fun c hc => lt_of_lt_of_le hy (hleast.2 hc)).mono fun n hn => hn.le
  · rw [liminf_le_iff' h1 h2]
    intro y hy
    exact (frequently_lt_of_mem_clusterSet hmem hy).mono fun n hn => hn.le

/-!
### Unbounded sequences

For an arbitrary real sequence the limit superior is defined by cases, with values in the
extended real line. If the sequence is not bounded above, the limit superior is
$`+\infty`; in this case some extended term is positive unlimited. If it is bounded above
and diverges to minus infinity, the limit superior is $`-\infty`; in this case every extended
term is negative unlimited and there are no cluster points. Otherwise some extended term is
limited, the set of cluster points is nonempty and bounded above, and the limit superior is
its least upper bound. The definition of the limit inferior (Exercise 6.9(1)) is the mirror
image. Both agree with Mathlib's limit superior and inferior of the sequence regarded as a
sequence of extended reals.
-/

open Classical in
/-- **Section 6.8, limit superior of an arbitrary real sequence.** The value is
$`+\infty` if the sequence is not bounded above, $`-\infty` if it diverges to minus infinity,
and the least upper bound of the set of cluster points otherwise. -/
def limSupE (s : ℕ → ℝ) : EReal :=
  if ¬ BddAbove (range s) then ⊤
  else if Tendsto s atTop atBot then ⊥
  else ((sSup (clusterSet s) : ℝ) : EReal)

open Classical in
/-- **Exercise 6.9(1), limit inferior of an arbitrary real sequence.** The value is
$`-\infty` if the sequence is not bounded below, $`+\infty` if it diverges to infinity, and
the greatest lower bound of the set of cluster points otherwise. -/
def limInfE (s : ℕ → ℝ) : EReal :=
  if ¬ BddBelow (range s) then ⊥
  else if Tendsto s atTop atTop then ⊤
  else ((sInf (clusterSet s) : ℝ) : EReal)

/-- **Section 6.8, case (1).** A sequence that is not bounded above has a positive unlimited
extended term. -/
theorem exists_unlimited_posUnlimited_of_not_bddAbove (h : ¬ BddAbove (range s)) :
    ∃ N ∈ unlimitedHyperNat, PosUnlimited (hyperSeq s N) := by
  by_contra hne
  push Not at hne
  exact h (bddAbove_range_iff_forall_unlimited_not_posUnlimited.2 hne)

/-- **Section 6.8, case (2)(i).** A sequence that diverges to minus infinity is bounded above:
none of its extended terms is positive unlimited, since all are negative unlimited. -/
theorem bddAbove_range_of_tendsto_atBot (h : Tendsto s atTop atBot) : BddAbove (range s) :=
  bddAbove_range_iff_forall_unlimited_not_posUnlimited.2 fun N hN hpos =>
    absurd (hpos 0) (not_lt.2 ((tendsto_atBot_iff_forall_unlimited_negUnlimited.1 h N hN) 0).le)

/-- **Section 6.8, case (2)(i).** A sequence that diverges to minus infinity has no cluster
points, because it has no limited extended terms. -/
theorem clusterSet_eq_empty_of_tendsto_atBot (h : Tendsto s atTop atBot) :
    clusterSet s = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro c hc
  obtain ⟨N, hN, hcl⟩ := mem_clusterSet_iff.1 hc
  exact (tendsto_atBot_iff_forall_unlimited_negUnlimited.1 h N hN).unlimited.not_limited
    (limited_of_infClose_coe hcl)

/-- **Section 6.8, case (2)(ii).** A sequence that is bounded above and does not diverge to
minus infinity has a limited extended term, so its set of cluster points is nonempty. -/
theorem clusterSet_nonempty_of_bddAbove_of_not_tendsto_atBot (hb : BddAbove (range s))
    (h : ¬ Tendsto s atTop atBot) : (clusterSet s).Nonempty := by
  rw [tendsto_atBot_iff_forall_unlimited_negUnlimited] at h
  push Not at h
  obtain ⟨N, hN, hneg⟩ := h
  have hl : Limited (hyperSeq s N) := limited_iff_not_posUnlimited_and_not_negUnlimited.2
    ⟨bddAbove_range_iff_forall_unlimited_not_posUnlimited.1 hb N hN, hneg⟩
  exact ⟨_, sh_hyperSeq_mem_clusterSet hN hl⟩

/-- The extended limit superior of a sequence that is not bounded above is $`+\infty`. -/
theorem limSupE_of_not_bddAbove (h : ¬ BddAbove (range s)) : limSupE s = ⊤ := by
  rw [limSupE, ite_eq_left h]

/-- The extended limit superior of a sequence that diverges to minus infinity is
$`-\infty`. -/
theorem limSupE_of_tendsto_atBot (h : Tendsto s atTop atBot) : limSupE s = ⊥ := by
  rw [limSupE, ite_eq_right (not_not.2 (bddAbove_range_of_tendsto_atBot h)), ite_eq_left h]

/-- The extended limit superior of a sequence that is bounded above and does not diverge to
minus infinity is the least upper bound of its cluster points. -/
theorem limSupE_of_bddAbove_of_not_tendsto_atBot (hb : BddAbove (range s))
    (h : ¬ Tendsto s atTop atBot) : limSupE s = ((sSup (clusterSet s) : ℝ) : EReal) := by
  rw [limSupE, ite_eq_right (not_not.2 hb), ite_eq_right h]

/-- **Section 6.8.** For a bounded sequence the extended limit superior is the real limit
superior. -/
theorem limSupE_eq_coe_limSup (hb : ∃ b : ℝ, ∀ n, |s n| < b) :
    limSupE s = ((limSup s : ℝ) : EReal) := by
  refine limSupE_of_bddAbove_of_not_tendsto_atBot (bddAbove_range_of_bounded hb) fun h => ?_
  exact (tendsto_atBot_iff_forall_unlimited_negUnlimited.1 h ω
    omega_mem_unlimitedHyperNat).unlimited.not_limited
    (bounded_iff_forall_unlimited_limited.1 hb ω omega_mem_unlimitedHyperNat)

/-- **Section 6.8, agreement with Mathlib for arbitrary sequences.** The extended limit
superior defined by cases is Mathlib's limit superior of the sequence regarded as a sequence
of extended real numbers. -/
theorem limSupE_eq_limsup (s : ℕ → ℝ) :
    limSupE s = limsup (fun n => (s n : EReal)) atTop := by
  by_cases hb : BddAbove (range s)
  · by_cases hbot : Tendsto s atTop atBot
    · rw [limSupE_of_tendsto_atBot hbot]
      symm
      rw [← le_bot_iff, limsup_le_iff']
      intro y hy
      obtain ⟨r, -, hr⟩ := EReal.exists_between_coe_real hy
      exact (hbot.eventually (eventually_le_atBot r)).mono fun n hn =>
        (EReal.coe_le_coe_iff.2 hn).trans hr.le
    · rw [limSupE_of_bddAbove_of_not_tendsto_atBot hb hbot]
      have hne := clusterSet_nonempty_of_bddAbove_of_not_tendsto_atBot hb hbot
      have hC := bddAbove_clusterSet hb
      apply le_antisymm
      · rw [le_limsup_iff']
        intro y hy
        obtain ⟨r, hyr, hr⟩ := EReal.exists_between_coe_real hy
        obtain ⟨c, hc, hrc⟩ := exists_lt_of_lt_csSup hne (EReal.coe_lt_coe_iff.1 hr)
        exact (frequently_gt_of_mem_clusterSet hc hrc).mono fun n hn =>
          hyr.le.trans (EReal.coe_le_coe_iff.2 hn.le)
      · rw [limsup_le_iff']
        intro y hy
        obtain ⟨r, hr, hry⟩ := EReal.exists_between_coe_real hy
        exact (eventually_lt_of_forall_clusterSet_lt hb fun c hc =>
          lt_of_le_of_lt (le_csSup hC hc) (EReal.coe_lt_coe_iff.1 hr)).mono fun n hn =>
          (EReal.coe_le_coe_iff.2 hn.le).trans hry.le
  · rw [limSupE_of_not_bddAbove hb]
    symm
    rw [← top_le_iff, le_limsup_iff']
    intro y hy
    obtain ⟨r, hyr, -⟩ := EReal.exists_between_coe_real hy
    obtain ⟨N, hN, hpos⟩ := exists_unlimited_posUnlimited_of_not_bddAbove hb
    exact ((exists_unlimited_lt_hyperSeq_iff s r).1 ⟨N, hN, hpos r⟩).mono fun n hn =>
      hyr.le.trans (EReal.coe_le_coe_iff.2 hn.le)

/-- **Exercise 6.9(1).** The extended limit inferior of a sequence is minus the extended limit
superior of the sequence of negatives. -/
theorem limInfE_eq_neg_limSupE_neg (s : ℕ → ℝ) : limInfE s = -limSupE fun n => -s n := by
  have hbdd : BddAbove (range fun n => -s n) ↔ BddBelow (range s) := by
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨-b, ?_⟩
      rintro _ ⟨n, rfl⟩
      have := hb ⟨n, rfl⟩
      simp only at this
      linarith
    · rintro ⟨b, hb⟩
      exact ⟨-b, by rintro _ ⟨n, rfl⟩; exact neg_le_neg (hb ⟨n, rfl⟩)⟩
  have htend : Tendsto (fun n => -s n) atTop atBot ↔ Tendsto s atTop atTop :=
    tendsto_neg_atBot_iff
  by_cases h1 : BddBelow (range s)
  · by_cases h2 : Tendsto s atTop atTop
    · rw [limInfE, limSupE, ite_eq_right (not_not.2 h1), ite_eq_left h2,
        ite_eq_right (not_not.2 (hbdd.2 h1)), ite_eq_left (htend.2 h2)]
      simp
    · rw [limInfE, limSupE, ite_eq_right (not_not.2 h1), ite_eq_right h2,
        ite_eq_right (not_not.2 (hbdd.2 h1)), ite_eq_right (mt htend.1 h2), clusterSet_neg,
        Real.sInf_def, EReal.coe_neg]
  · rw [limInfE, limSupE, ite_eq_left h1, ite_eq_left (mt hbdd.1 h1)]
    simp

/-- **Exercise 6.9(1), agreement with Mathlib.** The extended limit inferior defined by cases
is Mathlib's limit inferior of the sequence regarded as a sequence of extended real numbers.
-/
theorem limInfE_eq_liminf (s : ℕ → ℝ) :
    limInfE s = liminf (fun n => (s n : EReal)) atTop := by
  rw [limInfE_eq_neg_limSupE_neg, limSupE_eq_limsup]
  have : (fun n => ((-s n : ℝ) : EReal)) = -fun n => (s n : EReal) := by
    funext n
    simp
  rw [this, EReal.limsup_neg, neg_neg]

/-- For a bounded sequence the extended limit inferior is the real limit inferior. -/
theorem limInfE_eq_coe_limInf (hb : ∃ b : ℝ, ∀ n, |s n| < b) :
    limInfE s = ((limInf s : ℝ) : EReal) := by
  rw [limInfE_eq_neg_limSupE_neg, limSupE_eq_coe_limSup (bounded_neg hb),
    limInf_eq_neg_limSup_neg, EReal.coe_neg]

/-- **Section 6.8, general form of Theorem 6.8.4 (1).** If the extended limit superior of a
real sequence is below the real number $`r`, then some standard tail of the sequence is below
$`r`. -/
theorem eventually_lt_of_limSupE_lt {r : ℝ} (h : limSupE s < r) : ∀ᶠ n in atTop, s n < r := by
  by_cases hb : BddAbove (range s)
  · by_cases hbot : Tendsto s atTop atBot
    · exact hbot.eventually (eventually_lt_atBot r)
    · rw [limSupE_of_bddAbove_of_not_tendsto_atBot hb hbot, EReal.coe_lt_coe_iff] at h
      exact eventually_lt_of_forall_clusterSet_lt hb fun c hc =>
        lt_of_le_of_lt (le_csSup (bddAbove_clusterSet hb) hc) h
  · rw [limSupE_of_not_bddAbove hb] at h
    exact absurd h (not_lt.2 le_top)

/-- **Exercise 6.9(2), general form.** If the extended limit inferior of a real sequence is
above the real number $`r`, then some standard tail of the sequence is above $`r`. -/
theorem eventually_gt_of_lt_limInfE {r : ℝ} (h : (r : EReal) < limInfE s) :
    ∀ᶠ n in atTop, r < s n := by
  rw [limInfE_eq_neg_limSupE_neg, EReal.lt_neg_comm, ← EReal.coe_neg] at h
  exact (eventually_lt_of_limSupE_lt h).mono fun n hn => by linarith

end LimSup

/-!
## 6.9 Exercises on lim sup and lim inf

The first exercise, the definition of the limit inferior of an arbitrary sequence, is
{lit}`limInfE` above. The second asks for the counterparts for the limit inferior of Theorems
6.8.4 and 6.8.5; they are obtained from those theorems by passing to the sequence of
negatives. The third combines the two halves: every interval that is slightly larger than the
interval from the limit inferior to the limit superior contains a standard tail.
-/

section ExercisesLimSup

variable {s : ℕ → ℝ}

/-- **Exercise 6.9(2), counterpart of Theorem 6.8.4 (1).** For a bounded real sequence and a
positive real $`e`, some standard tail of the sequence lies above $`\liminf s - e`. -/
theorem eventually_limInf_sub_lt (hb : ∃ b : ℝ, ∀ n, |s n| < b) {e : ℝ} (he : 0 < e) :
    ∀ᶠ n in atTop, limInf s - e < s n :=
  eventually_gt_of_forall_clusterSet_gt (bddBelow_range_of_bounded hb) fun c hc => by
    linarith [(isLeast_limInf hb).2 hc]

/-- **Exercise 6.9(2), counterpart of Theorem 6.8.4 (2).** For a bounded real sequence and a
positive real $`e`, $`s_n < \liminf s + e` for arbitrarily large $`n`. -/
theorem frequently_lt_limInf_add (hb : ∃ b : ℝ, ∀ n, |s n| < b) {e : ℝ} (he : 0 < e) :
    ∃ᶠ n in atTop, s n < limInf s + e :=
  frequently_lt_of_mem_clusterSet (limInf_mem_clusterSet hb) (by linarith)

/-- **Exercise 6.9(2), counterpart of Theorem 6.8.4 (2)**, as a statement about infinite sets.
-/
theorem infinite_setOf_lt_limInf_add (hb : ∃ b : ℝ, ∀ n, |s n| < b) {e : ℝ} (he : 0 < e) :
    {n | s n < limInf s + e}.Infinite :=
  Nat.frequently_atTop_iff_infinite.1 (frequently_lt_limInf_add hb he)

/-- **Exercise 6.9(2).** The infimum $`\inf_{m \ge n} s_m` of the standard tail of the sequence
that starts at $`n`. -/
def tailInf (s : ℕ → ℝ) (n : ℕ) : ℝ := sInf (s '' Ici n)

/-- The tail infimum is minus the tail supremum of the sequence of negatives. -/
theorem tailInf_eq_neg_tailSup_neg (s : ℕ → ℝ) (n : ℕ) :
    tailInf s n = -tailSup (fun m => -s m) n := by
  rw [tailInf, tailSup, Real.sInf_def]
  congr 2
  ext x
  simp only [Set.mem_neg, mem_image, mem_Ici]
  constructor
  · rintro ⟨m, hm, h⟩
    exact ⟨m, hm, by linarith⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨m, hm, by linarith⟩

/-- **Exercise 6.9(2), counterpart of Theorem 6.8.5.** For a bounded real sequence $`s`, the
infima of the tails converge to the limit inferior:
$$`\liminf_{n\to\infty} s_n = \lim_{n\to\infty} \Bigl(\inf_{m \ge n} s_m\Bigr).` -/
theorem tendsto_tailInf_limInf (hb : ∃ b : ℝ, ∀ n, |s n| < b) :
    Tendsto (tailInf s) atTop (𝓝 (limInf s)) := by
  have h := limit_const_mul (-1) (tendsto_tailSup_limSup (bounded_neg hb))
  rw [limInf_eq_neg_limSup_neg]
  have hfun : tailInf s = fun n => -1 * tailSup (fun m => -s m) n := by
    funext n
    rw [tailInf_eq_neg_tailSup_neg]
    ring
  rw [hfun]
  simpa using h

/-- **Exercise 6.9(3).** For a bounded real sequence and a positive real $`e`, there is an
$`n` such that the standard tail $`s_n, s_{n+1}, \dots` lies in the interval
$`(\liminf s - e, \limsup s + e)`. -/
theorem exists_tail_subset_Ioo (hb : ∃ b : ℝ, ∀ n, |s n| < b) {e : ℝ} (he : 0 < e) :
    ∃ n, ∀ m, n ≤ m → s m ∈ Ioo (limInf s - e) (limSup s + e) :=
  eventually_atTop.1 ((eventually_limInf_sub_lt hb he).and (eventually_lt_limSup_add hb he))

/-- **Section 6.8, non-vacuity.** The bounded sequence $`(-1)^n` does not converge: its limit
superior is $`1` and its limit inferior is $`-1`. The extended terms at even unlimited
hypernaturals are $`1` and those at odd ones are $`-1`. -/
theorem limSup_limInf_neg_one_pow :
    limSup (fun n : ℕ => (-1 : ℝ) ^ n) = 1 ∧ limInf (fun n : ℕ => (-1 : ℝ) ^ n) = -1 := by
  set s : ℕ → ℝ := fun n => (-1 : ℝ) ^ n with hs
  have hb : ∃ b : ℝ, ∀ n, |s n| < b := ⟨2, fun n => by simp [hs]⟩
  have hval : ∀ N ∈ unlimitedHyperNat, hyperSeq s N = 1 ∨ hyperSeq s N = -1 := by
    intro N hN
    obtain ⟨k, -, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
    rcases almostAll_or.1 (Eventually.of_forall fun n => em (Even (k n))) with he | ho
    · left
      rw [hyperSeq_hnat]
      change _ = Hyperreal.ofSeq fun _ => 1
      rw [ofSeq_eq_ofSeq_iff]
      exact he.mono fun n hn => hn.neg_one_pow
    · right
      rw [hyperSeq_hnat]
      change _ = Hyperreal.ofSeq fun _ => -1
      rw [ofSeq_eq_ofSeq_iff]
      exact ho.mono fun n hn => (Nat.not_even_iff_odd.1 hn).neg_one_pow
  have hk2 : Tendsto (fun n : ℕ => 2 * n) (hyperfilter ℕ) atTop :=
    (tendsto_atTop_mono (fun n => show id n ≤ 2 * n by simp only [id]; omega)
      tendsto_id).mono_left Nat.hyperfilter_le_atTop
  have hk1 : Tendsto (fun n : ℕ => 2 * n + 1) (hyperfilter ℕ) atTop :=
    (tendsto_atTop_mono (fun n => show id n ≤ 2 * n + 1 by simp only [id]; omega)
      tendsto_id).mono_left Nat.hyperfilter_le_atTop
  have h1 : hyperSeq s (hnat fun n : ℕ => 2 * n) = ((1 : ℝ) : ℝ*) := by
    rw [hyperSeq_hnat, coe_eq_ofSeq_const, ofSeq_eq_ofSeq_iff]
    exact Eventually.of_forall fun n => by simp [hs, pow_mul]
  have h2 : hyperSeq s (hnat fun n : ℕ => 2 * n + 1) = ((-1 : ℝ) : ℝ*) := by
    rw [hyperSeq_hnat, coe_eq_ofSeq_const, ofSeq_eq_ofSeq_iff]
    exact Eventually.of_forall fun n => by simp [hs, pow_succ, pow_mul]
  constructor
  · symm
    rw [eq_limSup_iff hb]
    refine ⟨fun N hN => ?_, _, hnat_mem_unlimitedHyperNat_iff.2 hk2, by rw [h1]⟩
    rcases hval N hN with h | h
    · right
      rw [h, Hyperreal.coe_one]
    · left
      rw [h, Hyperreal.coe_one]
      norm_num
  · symm
    rw [eq_limInf_iff hb]
    refine ⟨fun N hN => ?_, _, hnat_mem_unlimitedHyperNat_iff.2 hk1, by rw [h2]⟩
    rcases hval N hN with h | h
    · left
      rw [h, Hyperreal.coe_neg, Hyperreal.coe_one]
      norm_num
    · right
      rw [h, Hyperreal.coe_neg, Hyperreal.coe_one]

end ExercisesLimSup

end Goldblatt
