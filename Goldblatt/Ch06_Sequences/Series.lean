import Goldblatt.Ch06_Sequences.LimSup

/-!
# 6 (part 3). Series: Sections 6.10 and 6.11

This is the third of three parts of Chapter 6 (the overview is on the chapter page
{lit}`Goldblatt.Ch06_Sequences`). A series converges when its sequence of partial sums does,
so the results on sequences apply to the hypersequence of partial sums, whose values at
unlimited hypernaturals are hyperfinite sums. The part proves the nonstandard forms of
convergence of a series and of the Cauchy criterion, and works through the exercises: the
rules for combining series, the comparison tests, the geometric series, the ratio test in both
directions, and the alternating series test.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## 6.10 Series

The book indexes a series from $`1` and writes $`\sum_1^n a_i` for the partial sum
$`s_n = a_1 + \dots + a_n` and $`\sum_m^n a_i` for $`s_n - s_{m-1}`. Here sequences are
indexed from $`0`. The partial sum {lit}`partialSum a n` is the sum of the first $`n` terms,
$`a_0 + \dots + a_{n-1}`, and it plays the role of the book's $`s_n`. Its extension to the
hyperreals is {lit}`hyperSum a N`, the hyperfinite sum of the first $`N` terms. The block sum
$`\sum_{i=M}^{N} a_i` is {lit}`hyperSumIcc a M N`, defined as the difference of the partial
sums up to $`N + 1` and up to $`M`, exactly as in the book.

A series is said to converge when the sequence of its partial sums converges. This is weaker
than Mathlib's {name}`Summable`, which asks for unconditional convergence; the two agree for
series of nonnegative terms, and {name}`HasSum` always implies convergence of the partial
sums to the same value.

The main statements are: the sum is $`L` exactly when every hyperfinite sum of unlimited
length is infinitely close to $`L`; the series converges exactly when every block sum between
unlimited indices is infinitesimal (the Cauchy criterion); and the terms of a convergent
series tend to zero.
-/

section Series

variable {a b : ℕ → ℝ} {L : ℝ} {M N : ℝ*}

/-- **Section 6.10.** The partial sum $`s_n = a_0 + \dots + a_{n-1}` of the first $`n` terms
of a series. -/
def partialSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, a i

/-- **Section 6.10.** The series $`\sum a_i` has sum $`L` if its partial sums converge to
$`L`. -/
def SeriesSum (a : ℕ → ℝ) (L : ℝ) : Prop := Tendsto (partialSum a) atTop (𝓝 L)

/-- **Section 6.10.** The series $`\sum a_i` converges if its sequence of partial sums
converges. -/
def SeriesConverges (a : ℕ → ℝ) : Prop := ∃ L : ℝ, SeriesSum a L

/-- **Section 6.10.** The extended partial sum: for a hypernatural $`N`, the hyperfinite sum
$`\sum_{i < N} a_i` of the first $`N` terms. It is the value at $`N` of the hypersequence of
partial sums. -/
def hyperSum (a : ℕ → ℝ) (N : ℝ*) : ℝ* := hyperSeq (partialSum a) N

/-- **Section 6.10.** The block sum $`\sum_{i=M}^{N} a_i` for hypernaturals $`M \le N`, defined
as the difference of two extended partial sums. -/
def hyperSumIcc (a : ℕ → ℝ) (M N : ℝ*) : ℝ* := hyperSum a (N + 1) - hyperSum a M

/-- The partial sum of $`n + 1` terms. -/
theorem partialSum_succ (a : ℕ → ℝ) (n : ℕ) : partialSum a (n + 1) = partialSum a n + a n :=
  Finset.sum_range_succ _ _

/-- The partial sums of a series of nonnegative terms are nondecreasing. -/
theorem partialSum_mono (h : ∀ i, 0 ≤ a i) : Monotone (partialSum a) := fun _ _ hmn =>
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn) fun i _ _ => h i

/-- The partial sums of a series of nonnegative terms are nonnegative. -/
theorem partialSum_nonneg (h : ∀ i, 0 ≤ a i) (n : ℕ) : 0 ≤ partialSum a n :=
  Finset.sum_nonneg fun i _ => h i

/-- A difference of partial sums is a block sum. -/
theorem partialSum_succ_sub (a : ℕ → ℝ) {m n : ℕ} (h : m ≤ n) :
    partialSum a (n + 1) - partialSum a m = ∑ i ∈ Finset.Icc m n, a i := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub _ (show m ≤ n + 1 by omega)]
  rfl

/-- The partial sums of a termwise sum. -/
theorem partialSum_add (a b : ℕ → ℝ) :
    partialSum (fun i => a i + b i) = fun n => partialSum a n + partialSum b n := by
  funext n
  exact Finset.sum_add_distrib

/-- The partial sums of a termwise difference. -/
theorem partialSum_sub (a b : ℕ → ℝ) :
    partialSum (fun i => a i - b i) = fun n => partialSum a n - partialSum b n := by
  funext n
  exact Finset.sum_sub_distrib _ _

/-- The partial sums of a constant multiple. -/
theorem partialSum_const_mul (c : ℝ) (a : ℕ → ℝ) :
    partialSum (fun i => c * a i) = fun n => c * partialSum a n := by
  funext n
  exact (Finset.mul_sum _ _ _).symm

/-- At a standard natural number the extended partial sum is the partial sum. -/
theorem hyperSum_natCast (a : ℕ → ℝ) (n : ℕ) : hyperSum a (n : ℝ*) = (partialSum a n : ℝ*) :=
  hyperSeq_natCast_real _ n

/-- Transfer of $`s_{n+1} = s_n + a_n`: the hyperfinite sum of $`N + 1` terms is the sum of
$`N` terms plus the term $`a_N`. -/
theorem hyperSum_add_one (a : ℕ → ℝ) (hN : N ∈ ℕ*) :
    hyperSum a (N + 1) = hyperSum a N + hyperSeq a N := by
  rw [hyperSum, hyperSeq_add_one _ hN, hyperSum, ← hyperSeq_add]
  congr 1
  funext n
  exact partialSum_succ a n

/-- **Section 6.10.** The block sum from $`N` to $`N` is the single term $`a_N`. This is the
case $`m = n` of the book's block sums. -/
theorem hyperSumIcc_self (a : ℕ → ℝ) (hN : N ∈ ℕ*) : hyperSumIcc a N N = hyperSeq a N := by
  rw [hyperSumIcc, hyperSum_add_one a hN, add_sub_cancel_left]

/-- The extended partial sums of a constant multiple. -/
theorem hyperSum_const_mul (c : ℝ) (a : ℕ → ℝ) (x : ℝ*) :
    hyperSum (fun i => c * a i) x = c * hyperSum a x := by
  rw [hyperSum, partialSum_const_mul, hyperSeq_const_mul, hyperSum]

/-- The block sums of a constant multiple. -/
theorem hyperSumIcc_const_mul (c : ℝ) (a : ℕ → ℝ) (M N : ℝ*) :
    hyperSumIcc (fun i => c * a i) M N = c * hyperSumIcc a M N := by
  rw [hyperSumIcc, hyperSum_const_mul, hyperSum_const_mul, hyperSumIcc, mul_sub]

/-- **Section 6.10, block sums in the ultrapower.** For hypernaturals $`[k_n] \le [l_n]` the
block sum of the series between them is the class of the sequence of standard block sums
$`\sum_{i=k_n}^{l_n} a_i`. Every transfer of a statement about finite block sums goes through
this formula. -/
theorem hyperSumIcc_hnat (a : ℕ → ℝ) {k l : ℕ → ℕ} (h : hnat k ≤ hnat l) :
    hyperSumIcc a (hnat k) (hnat l) =
      Hyperreal.ofSeq fun n => ∑ i ∈ Finset.Icc (k n) (l n), a i := by
  rw [hyperSumIcc, hyperSum, hyperSum, ← hnat_const_one, hnat_add, hyperSeq_hnat, hyperSeq_hnat]
  change Hyperreal.ofSeq (fun n => partialSum a (l n + 1) - partialSum a (k n)) = _
  rw [ofSeq_eq_ofSeq_iff]
  exact (hnat_le_hnat_iff.1 h).mono fun n hn => partialSum_succ_sub a hn

/-- Transfer of termwise comparison of block sums: if $`a_i \le b_i` for all standard
$`i \ge j`, then $`\sum_M^N a_i \le \sum_M^N b_i` for all hypernaturals $`j \le M \le N`. -/
theorem hyperSumIcc_le_hyperSumIcc {j : ℕ} (h : ∀ i, j ≤ i → a i ≤ b i) (hM : M ∈ ℕ*)
    (hN : N ∈ ℕ*) (hjM : (j : ℝ*) ≤ M) (hMN : M ≤ N) :
    hyperSumIcc a M N ≤ hyperSumIcc b M N := by
  obtain ⟨k, rfl⟩ := exists_hnat_eq hM
  obtain ⟨l, rfl⟩ := exists_hnat_eq hN
  rw [hyperSumIcc_hnat a hMN, hyperSumIcc_hnat b hMN, ofSeq_le_ofSeq_iff]
  rw [natCast_eq_hnat, hnat_le_hnat_iff] at hjM
  exact hjM.mono fun n hn =>
    Finset.sum_le_sum fun i hi => h i (hn.trans (Finset.mem_Icc.1 hi).1)

/-- Transfer of nonnegativity of block sums: if $`0 \le a_i` for all standard $`i \ge j`, then
$`0 \le \sum_M^N a_i` for all hypernaturals $`j \le M \le N`. -/
theorem hyperSumIcc_nonneg {j : ℕ} (h : ∀ i, j ≤ i → 0 ≤ a i) (hM : M ∈ ℕ*) (hN : N ∈ ℕ*)
    (hjM : (j : ℝ*) ≤ M) (hMN : M ≤ N) : 0 ≤ hyperSumIcc a M N := by
  obtain ⟨k, rfl⟩ := exists_hnat_eq hM
  obtain ⟨l, rfl⟩ := exists_hnat_eq hN
  rw [hyperSumIcc_hnat a hMN]
  change Hyperreal.ofSeq (fun _ => 0) ≤ _
  rw [ofSeq_le_ofSeq_iff]
  rw [natCast_eq_hnat, hnat_le_hnat_iff] at hjM
  exact hjM.mono fun n hn =>
    Finset.sum_nonneg fun i hi => h i (hn.trans (Finset.mem_Icc.1 hi).1)

/-- Transfer of the triangle inequality for block sums:
$`|\sum_M^N a_i| \le \sum_M^N |a_i|` for hypernaturals $`M \le N`. -/
theorem abs_hyperSumIcc_le (a : ℕ → ℝ) (hM : M ∈ ℕ*) (hN : N ∈ ℕ*) (hMN : M ≤ N) :
    |hyperSumIcc a M N| ≤ hyperSumIcc (fun i => |a i|) M N := by
  obtain ⟨k, rfl⟩ := exists_hnat_eq hM
  obtain ⟨l, rfl⟩ := exists_hnat_eq hN
  rw [hyperSumIcc_hnat a hMN, hyperSumIcc_hnat _ hMN, abs_ofSeq, ofSeq_le_ofSeq_iff]
  exact Eventually.of_forall fun n => Finset.abs_sum_le_sum_abs _ _

/-- **Section 6.10, first statement.** The series $`\sum a_i` has sum $`L` if and only if the
hyperfinite sum of the first $`N` terms is infinitely close to $`L` for every unlimited
$`N`. -/
theorem seriesSum_iff_forall_unlimited_infClose :
    SeriesSum a L ↔ ∀ N ∈ unlimitedHyperNat, hyperSum a N ≊ (L : ℝ*) :=
  tendsto_iff_forall_unlimited_infClose

/-- **Section 6.10.** The sum of a convergent series is the shadow of any of its hyperfinite
sums of unlimited length. -/
theorem SeriesSum.eq_sh (h : SeriesSum a L) (hN : N ∈ unlimitedHyperNat) :
    L = sh (hyperSum a N) :=
  (sh_hyperSeq_of_tendsto h hN).symm

/-- **Section 6.10, second statement (Cauchy criterion for series).** The series
$`\sum a_i` converges if and only if the block sum $`\sum_{i=M}^{N} a_i` is infinitesimal for
all unlimited hypernaturals $`M \le N`. This is Cauchy's convergence criterion (Theorem
6.5.2) for the sequence of partial sums. -/
theorem seriesConverges_iff_forall_unlimited_hyperSumIcc :
    SeriesConverges a ↔
      ∀ M ∈ unlimitedHyperNat, ∀ N ∈ unlimitedHyperNat, M ≤ N →
        Infinitesimal (hyperSumIcc a M N) := by
  rw [SeriesConverges]
  change (∃ L : ℝ, Tendsto (partialSum a) atTop (𝓝 L)) ↔ _
  rw [← cauchySeq_iff_exists_tendsto, cauchySeq_iff_forall_unlimited_infClose]
  constructor
  · intro h M hM N hN _
    exact h (N + 1) (add_one_mem_unlimitedHyperNat hN) M hM
  · intro h
    have key : ∀ M ∈ unlimitedHyperNat, ∀ N ∈ unlimitedHyperNat, M ≤ N →
        hyperSeq (partialSum a) N ≊ hyperSeq (partialSum a) M := by
      intro M hM N hN hMN
      rcases hMN.eq_or_lt with rfl | hlt
      · exact InfClose.refl _
      · have hM1 : M + 1 ≤ N := add_one_le_of_lt_of_mem_hyperInt
          (hyperNat_subset_hyperInt hM.1) (hyperNat_subset_hyperInt hN.1) hlt
        have hN0 : N ≠ 0 := (mem_unlimitedHyperNat.1 hN).2.ne_zero
        have hN1 : N - 1 ∈ unlimitedHyperNat :=
          mem_unlimitedHyperNat_of_le hM (sub_one_mem_hyperNat hN.1 hN0) (by linarith)
        have := h M hM (N - 1) hN1 (by linarith)
        rw [hyperSumIcc, sub_add_cancel] at this
        exact this
    intro M hM N hN
    rcases le_total M N with hMN | hNM
    · exact (key M hM N hN hMN).symm
    · exact key N hN M hM hNM

/-- **Section 6.10.** If the series $`\sum a_i` converges then $`a_N \simeq 0` for every
unlimited $`N`: this is the Cauchy criterion for the block from $`N` to $`N`. -/
theorem SeriesConverges.infinitesimal_hyperSeq (h : SeriesConverges a)
    (hN : N ∈ unlimitedHyperNat) : Infinitesimal (hyperSeq a N) := by
  rw [← hyperSumIcc_self a hN.1]
  exact seriesConverges_iff_forall_unlimited_hyperSumIcc.1 h N hN N hN le_rfl

/-- **Section 6.10, third statement.** If the series $`\sum a_i` converges then
$`\lim_{i \to \infty} a_i = 0`. -/
theorem SeriesConverges.tendsto_zero (h : SeriesConverges a) : Tendsto a atTop (𝓝 0) := by
  rw [tendsto_iff_forall_unlimited_infClose]
  intro N hN
  rw [Hyperreal.coe_zero, ← infinitesimal_iff_infClose_zero]
  exact h.infinitesimal_hyperSeq hN

/-- **Section 6.10, absolute convergence.** An absolutely convergent series converges. For
unlimited $`M \le N`, the block sum of the series is bounded in absolute value by the block
sum of the absolute values, which is infinitesimal. -/
theorem seriesConverges_of_abs (h : SeriesConverges fun i => |a i|) : SeriesConverges a := by
  rw [seriesConverges_iff_forall_unlimited_hyperSumIcc] at *
  intro M hM N hN hMN
  exact (h M hM N hN hMN).of_abs_le
    ((abs_hyperSumIcc_le a hM.1 hN.1 hMN).trans (le_abs_self _))

/-- **Section 6.10, agreement with Mathlib.** If a series has sum $`L` in Mathlib's sense of
unconditional summation, then its partial sums converge to $`L`. -/
theorem seriesSum_of_hasSum (h : HasSum a L) : SeriesSum a L :=
  h.tendsto_sum_nat

/-- **Section 6.10, agreement with Mathlib.** For a series of nonnegative terms, convergence
of the partial sums is the same as Mathlib's summability. -/
theorem seriesConverges_iff_summable_of_nonneg (h : ∀ i, 0 ≤ a i) :
    SeriesConverges a ↔ Summable a := by
  constructor
  · rintro ⟨L, hL⟩
    exact ((hasSum_iff_tendsto_nat_of_nonneg h L).2 hL).summable
  · rintro ⟨L, hL⟩
    exact ⟨L, seriesSum_of_hasSum hL⟩

/-- **Section 6.10, agreement with Mathlib.** Absolute convergence in the sense of the book is
Mathlib's summability of a real series. -/
theorem seriesConverges_abs_iff_summable : (SeriesConverges fun i => |a i|) ↔ Summable a := by
  rw [seriesConverges_iff_summable_of_nonneg fun i => abs_nonneg (a i)]
  exact summable_abs_iff

end Series

/-!
## 6.11 Exercises on Convergence of Series

The exercises apply the two criteria of Section 6.10. Exercise (6) is false as printed when
the ratios $`a_i / b_i` converge to zero; the statement is proved with the hypothesis that
the limit is nonzero, the half that survives without it is proved separately, and a
counterexample to the printed statement is given. In Exercise (8) the terms are assumed
nonzero, which the book needs implicitly for the ratios to be defined, and the inequality of
part (c) is weak, since it is an equality for $`n = 0`.
-/

section ExercisesSeries

variable {a b : ℕ → ℝ} {L L' c : ℝ} {M N : ℝ*}

/-- **Exercise 6.11(1).** The harmonic series $`\sum 1/(i+1)` diverges, although its term
$`a_N` is infinitesimal for every unlimited $`N`. The block sum from $`\omega` to
$`2\omega` has $`\omega + 1` terms, each at least $`1/(2\omega + 1)`, so it is at least
$`1/2` and is not infinitesimal; the Cauchy criterion fails. -/
theorem exists_diverging_series_with_infinitesimal_terms :
    ∃ a : ℕ → ℝ, ¬ SeriesConverges a ∧
      ∀ N ∈ unlimitedHyperNat, Infinitesimal (hyperSeq a N) := by
  refine ⟨fun i => 1 / ((i : ℝ) + 1), fun hconv => ?_, fun N hN => ?_⟩
  · have hk1 : Tendsto (fun n : ℕ => n) (hyperfilter ℕ) atTop :=
      tendsto_id.mono_left Nat.hyperfilter_le_atTop
    have hk2 : Tendsto (fun n : ℕ => 2 * n) (hyperfilter ℕ) atTop :=
      (tendsto_atTop_mono (fun n => show id n ≤ 2 * n by simp only [id]; omega)
        tendsto_id).mono_left Nat.hyperfilter_le_atTop
    have hle : hnat (fun n : ℕ => n) ≤ hnat fun n : ℕ => 2 * n :=
      hnat_le_hnat_iff.2 (Eventually.of_forall fun n => by omega)
    have hinf := seriesConverges_iff_forall_unlimited_hyperSumIcc.1 hconv _
      (hnat_mem_unlimitedHyperNat_iff.2 hk1) _ (hnat_mem_unlimitedHyperNat_iff.2 hk2) hle
    have hge : ((1 / 2 : ℝ) : ℝ*) ≤
        hyperSumIcc (fun i : ℕ => 1 / ((i : ℝ) + 1)) (hnat fun n : ℕ => n)
          (hnat fun n : ℕ => 2 * n) := by
      rw [hyperSumIcc_hnat _ hle, coe_eq_ofSeq_const, ofSeq_le_ofSeq_iff]
      refine Eventually.of_forall fun n => ?_
      have h1 : (Finset.Icc n (2 * n)).card • (1 / (2 * (n : ℝ) + 1)) ≤
          ∑ i ∈ Finset.Icc n (2 * n), 1 / ((i : ℝ) + 1) := by
        apply Finset.card_nsmul_le_sum
        intro i hi
        have hi2 : (i : ℝ) ≤ 2 * n := by exact_mod_cast (Finset.mem_Icc.1 hi).2
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      have h2 : (Finset.Icc n (2 * n)).card = n + 1 := by
        rw [Nat.card_Icc]
        omega
      rw [h2, nsmul_eq_mul] at h1
      refine le_trans ?_ h1
      push_cast
      rw [mul_one_div, div_le_div_iff₀ two_pos (by positivity)]
      linarith
    have := infinitesimal_iff_abs_lt.1 hinf (1 / 2) (by norm_num)
    exact absurd (lt_of_le_of_lt (hge.trans (le_abs_self _)) this) (lt_irrefl _)
  · have h := hyperSeq_infClose_of_tendsto
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) hN
    rwa [Hyperreal.coe_zero, ← infinitesimal_iff_infClose_zero] at h

/-- **Exercise 6.11(2), sums.** If $`\sum a_i = L` and $`\sum b_i = L'` then
$`\sum (a_i + b_i) = L + L'`. -/
theorem SeriesSum.add (ha : SeriesSum a L) (hb : SeriesSum b L') :
    SeriesSum (fun i => a i + b i) (L + L') := by
  rw [SeriesSum, partialSum_add]
  exact limit_add ha hb

/-- **Exercise 6.11(2), differences.** If $`\sum a_i = L` and $`\sum b_i = L'` then
$`\sum (a_i - b_i) = L - L'`. -/
theorem SeriesSum.sub (ha : SeriesSum a L) (hb : SeriesSum b L') :
    SeriesSum (fun i => a i - b i) (L - L') := by
  rw [SeriesSum, partialSum_sub]
  exact limit_sub ha hb

/-- **Exercise 6.11(2), constant multiples.** If $`\sum a_i = L` then
$`\sum c a_i = cL`. -/
theorem SeriesSum.const_mul (c : ℝ) (ha : SeriesSum a L) :
    SeriesSum (fun i => c * a i) (c * L) := by
  rw [SeriesSum, partialSum_const_mul]
  exact limit_const_mul c ha

/-- **Exercise 6.11(3), key step.** If a series of nonnegative terms has a limited hyperfinite
sum of some unlimited length $`N`, then it converges. The partial sums are nondecreasing, so
every standard partial sum is at most the limited sum to $`N`, which is below some real
number; monotone convergence (Theorem 6.2.1) applies. -/
theorem seriesConverges_of_exists_limited_of_nonneg (h : ∀ i, 0 ≤ a i)
    (hl : ∃ N ∈ unlimitedHyperNat, Limited (hyperSum a N)) : SeriesConverges a := by
  obtain ⟨N, hN, hl⟩ := hl
  obtain ⟨r, hr⟩ := limited_iff_abs_lt.1 hl
  have hbdd : BddAbove (range (partialSum a)) := by
    refine ⟨r, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 : (partialSum a n : ℝ*) ≤ hyperSum a N := by
      rw [← hyperSum_natCast]
      exact hyperSeq_mono (partialSum_mono h) (natCast_mem_hyperNat n) hN.1
        (natCast_lt_of_mem_unlimitedHyperNat hN n).le
    exact Hyperreal.coe_le_coe.1 ((h1.trans (le_abs_self _)).trans hr.le)
  obtain ⟨L, -, hL⟩ := Monotone.exists_isLUB_tendsto (partialSum_mono h) hbdd
  exact ⟨L, hL⟩

/-- **Exercise 6.11(3), first equivalence.** A series of nonnegative terms converges if and
only if its hyperfinite sum of length $`N` is limited for every unlimited $`N`. -/
theorem seriesConverges_iff_forall_limited_of_nonneg (h : ∀ i, 0 ≤ a i) :
    SeriesConverges a ↔ ∀ N ∈ unlimitedHyperNat, Limited (hyperSum a N) := by
  constructor
  · rintro ⟨L, hL⟩ N hN
    exact limited_of_infClose_coe (seriesSum_iff_forall_unlimited_infClose.1 hL N hN)
  · intro hl
    exact seriesConverges_of_exists_limited_of_nonneg h
      ⟨ω, omega_mem_unlimitedHyperNat, hl ω omega_mem_unlimitedHyperNat⟩

/-- **Exercise 6.11(3), second equivalence.** For a series of nonnegative terms, the
hyperfinite sums of unlimited length are all limited if and only if one of them is. -/
theorem forall_limited_iff_exists_limited_of_nonneg (h : ∀ i, 0 ≤ a i) :
    (∀ N ∈ unlimitedHyperNat, Limited (hyperSum a N)) ↔
      ∃ N ∈ unlimitedHyperNat, Limited (hyperSum a N) := by
  constructor
  · intro hl
    exact ⟨ω, omega_mem_unlimitedHyperNat, hl ω omega_mem_unlimitedHyperNat⟩
  · intro hl
    exact (seriesConverges_iff_forall_limited_of_nonneg h).1
      (seriesConverges_of_exists_limited_of_nonneg h hl)

/-- **Exercise 6.11(4) (comparison test).** Let $`0 \le a_i \le b_i` for all $`i`. If
$`\sum b_i` converges then so does $`\sum a_i`. By transfer the hyperfinite sums of $`a` lie
between $`0` and those of $`b`, which are limited, so result (3) applies. -/
theorem seriesConverges_of_nonneg_of_le (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hb : SeriesConverges b) : SeriesConverges a := by
  have hb0 : ∀ i, 0 ≤ b i := fun i => (ha i).trans (hab i)
  rw [seriesConverges_iff_forall_limited_of_nonneg ha]
  intro N hN
  have hlb := (seriesConverges_iff_forall_limited_of_nonneg hb0).1 hb N hN
  have h0 : (0 : ℝ*) ≤ hyperSum a N := by
    have := coe_le_hyperSeq (partialSum_nonneg ha) N
    rw [Hyperreal.coe_zero] at this
    exact this
  have h1 : hyperSum a N ≤ hyperSum b N :=
    hyperSeq_le_hyperSeq (fun n => Finset.sum_le_sum fun i _ => hab i) N
  exact hlb.of_abs_le (by rw [abs_of_nonneg h0]; exact h1.trans (le_abs_self _))

/-- **Exercise 6.11(5), comparison from some index on.** If $`0 \le a_i \le b_i` for all
$`i \ge j` and $`\sum b_i` converges, then $`\sum a_i` converges. For unlimited
$`M \le N` the block sum of $`a` lies between $`0` and the block sum of $`b`, which is
infinitesimal; the Cauchy criterion applies. -/
theorem seriesConverges_of_forall_ge_le {j : ℕ} (ha : ∀ i, j ≤ i → 0 ≤ a i)
    (hab : ∀ i, j ≤ i → a i ≤ b i) (hb : SeriesConverges b) : SeriesConverges a := by
  rw [seriesConverges_iff_forall_unlimited_hyperSumIcc] at *
  intro M hM N hN hMN
  have hjM : (j : ℝ*) ≤ M := (natCast_lt_of_mem_unlimitedHyperNat hM j).le
  have h0 := hyperSumIcc_nonneg ha hM.1 hN.1 hjM hMN
  have h1 := hyperSumIcc_le_hyperSumIcc hab hM.1 hN.1 hjM hMN
  exact (hb M hM N hN hMN).of_abs_le (by rw [abs_of_nonneg h0]; exact h1.trans (le_abs_self _))

/-- **Exercise 6.11(5), the equivalence.** The condition $`a_N \le b_N` for all unlimited
$`N` is equivalent to the existence of a standard $`k` with $`a_n \le b_n` for all
$`n \ge k`. This is principle (a). -/
theorem forall_unlimited_hyperSeq_le_iff :
    (∀ N ∈ unlimitedHyperNat, hyperSeq a N ≤ hyperSeq b N) ↔ ∃ k, ∀ n, k ≤ n → a n ≤ b n := by
  rw [← eventually_atTop, eventually_atTop_iff_forall_tendsto_hyperfilter]
  constructor
  · intro h k hk
    have := h _ (hnat_mem_unlimitedHyperNat_iff.2 hk)
    rwa [hyperSeq_hnat, hyperSeq_hnat, ofSeq_le_ofSeq_iff] at this
  · intro h N hN
    obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
    rw [hyperSeq_hnat, hyperSeq_hnat, ofSeq_le_ofSeq_iff]
    exact h k hk

/-- **Exercise 6.11(5) (comparison test, weak form).** Let $`\sum a_i` be a series of
nonnegative terms with $`a_N \le b_N` for all unlimited $`N`. If $`\sum b_i` converges then
so does $`\sum a_i`. -/
theorem seriesConverges_of_forall_unlimited_le (ha : ∀ i, 0 ≤ a i)
    (hab : ∀ N ∈ unlimitedHyperNat, hyperSeq a N ≤ hyperSeq b N) (hb : SeriesConverges b) :
    SeriesConverges a := by
  obtain ⟨k, hk⟩ := forall_unlimited_hyperSeq_le_iff.1 hab
  exact seriesConverges_of_forall_ge_le (fun i _ => ha i) hk hb

/-- **Exercise 6.11(6), key step.** Let $`b` have positive terms and let $`a_i / b_i`
converge to the real number $`c`. Then there is a standard $`j` with
$`a_i \le (c + 1) b_i` for all $`i \ge j`: for unlimited $`N` the ratio $`a_N / b_N` is
infinitely close to $`c`, hence below $`c + 1`, and principle (a) applies. -/
theorem exists_forall_ge_le_mul_of_tendsto_div (hb : ∀ i, 0 < b i)
    (hc : Tendsto (fun i => a i / b i) atTop (𝓝 c)) :
    ∃ j, ∀ i, j ≤ i → a i ≤ (c + 1) * b i := by
  have h : ∀ᶠ i in atTop, a i / b i < c + 1 := by
    rw [← forall_unlimited_hyperSeq_lt_iff]
    intro N hN
    have h := hyperSeq_infClose_of_tendsto hc hN
    exact (limited_of_infClose_coe h).lt_of_sh_lt (by rw [sh_eq_of_infClose h]; linarith)
  obtain ⟨j, hj⟩ := eventually_atTop.1 h
  exact ⟨j, fun i hi => ((div_lt_iff₀ (hb i)).1 (hj i hi)).le⟩

/-- **Exercise 6.11(6), the half that holds for every limit.** Let $`\sum a_i` and
$`\sum b_i` be series of positive terms such that $`a_i / b_i` converges. For unlimited
$`M \le N`, if $`\sum_M^N b_i` is infinitesimal then so is $`\sum_M^N a_i`. -/
theorem infinitesimal_hyperSumIcc_of_tendsto_div (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : Tendsto (fun i => a i / b i) atTop (𝓝 c)) (hM : M ∈ unlimitedHyperNat)
    (hN : N ∈ unlimitedHyperNat) (hMN : M ≤ N) (h : Infinitesimal (hyperSumIcc b M N)) :
    Infinitesimal (hyperSumIcc a M N) := by
  obtain ⟨j, hj⟩ := exists_forall_ge_le_mul_of_tendsto_div hb hc
  have hjM : (j : ℝ*) ≤ M := (natCast_lt_of_mem_unlimitedHyperNat hM j).le
  have h1 : hyperSumIcc a M N ≤ ((c + 1 : ℝ) : ℝ*) * hyperSumIcc b M N := by
    rw [← hyperSumIcc_const_mul]
    exact hyperSumIcc_le_hyperSumIcc hj hM.1 hN.1 hjM hMN
  have h0 : 0 ≤ hyperSumIcc a M N :=
    hyperSumIcc_nonneg (j := 0) (fun i _ => (ha i).le) hM.1 hN.1
      (by simpa using hyperNat_nonneg hM.1) hMN
  have h2 : Infinitesimal (((c + 1 : ℝ) : ℝ*) * hyperSumIcc b M N) :=
    (limited_coe _).mul_infinitesimal h
  exact h2.of_abs_le (by rw [abs_of_nonneg h0]; exact h1.trans (le_abs_self _))

/-- **Exercise 6.11(6), corrected statement.** Let $`\sum a_i` and $`\sum b_i` be series of
positive terms such that $`a_i / b_i` converges to a nonzero real number. Then for unlimited
$`M \le N`, the block sum $`\sum_M^N a_i` is infinitesimal if and only if $`\sum_M^N b_i` is.
The book omits the hypothesis that the limit is nonzero, without which the implication from
$`a` to $`b` fails ({lit}`exists_tendsto_div_seriesConverges_not_seriesConverges`). -/
theorem infinitesimal_hyperSumIcc_iff_of_tendsto_div (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : Tendsto (fun i => a i / b i) atTop (𝓝 c)) (hc0 : c ≠ 0)
    (hM : M ∈ unlimitedHyperNat) (hN : N ∈ unlimitedHyperNat) (hMN : M ≤ N) :
    Infinitesimal (hyperSumIcc a M N) ↔ Infinitesimal (hyperSumIcc b M N) := by
  have hc' : Tendsto (fun i => b i / a i) atTop (𝓝 (1 / c)) := by
    have := limit_div (tendsto_const_nhds (x := (1 : ℝ))) hc hc0
    refine this.congr fun i => ?_
    rw [one_div_div]
  exact ⟨infinitesimal_hyperSumIcc_of_tendsto_div hb ha hc' hM hN hMN,
    infinitesimal_hyperSumIcc_of_tendsto_div ha hb hc hM hN hMN⟩

/-- **Exercise 6.11(6), deduction, the half that holds for every limit.** If $`\sum a_i` and
$`\sum b_i` are series of positive terms such that $`a_i / b_i` converges, and $`\sum b_i`
converges, then $`\sum a_i` converges. -/
theorem seriesConverges_of_tendsto_div (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : Tendsto (fun i => a i / b i) atTop (𝓝 c)) (h : SeriesConverges b) :
    SeriesConverges a := by
  rw [seriesConverges_iff_forall_unlimited_hyperSumIcc] at *
  intro M hM N hN hMN
  exact infinitesimal_hyperSumIcc_of_tendsto_div ha hb hc hM hN hMN (h M hM N hN hMN)

/-- **Exercise 6.11(6), deduction, corrected statement.** If $`\sum a_i` and $`\sum b_i` are
series of positive terms such that $`a_i / b_i` converges to a nonzero real number, then
either both series converge or both diverge. -/
theorem seriesConverges_iff_of_tendsto_div (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : Tendsto (fun i => a i / b i) atTop (𝓝 c)) (hc0 : c ≠ 0) :
    SeriesConverges a ↔ SeriesConverges b := by
  rw [seriesConverges_iff_forall_unlimited_hyperSumIcc,
    seriesConverges_iff_forall_unlimited_hyperSumIcc]
  exact forall₂_congr fun M hM => forall₂_congr fun N hN => imp_congr_right fun hMN =>
    infinitesimal_hyperSumIcc_iff_of_tendsto_div ha hb hc hc0 hM hN hMN

/-- **Exercise 6.11(7), preliminary.** If $`|c| < 1` then $`c^n` converges to $`0`. The
powers lie between $`-d^n` and $`d^n` for $`d = (|c| + 1)/2`, a number strictly between
$`0` and $`1`, whose powers converge to $`0` by the application in Section 6.2. -/
theorem tendsto_pow_zero_of_abs_lt_one (hc : |c| < 1) :
    Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) := by
  have hd0 : 0 < (|c| + 1) / 2 := by positivity
  have hd1 : (|c| + 1) / 2 < 1 := by linarith
  have hcd : |c| ≤ (|c| + 1) / 2 := by linarith
  have hd := tendsto_pow_zero_of_pos_of_lt_one hd0 hd1
  have hd' := limit_const_mul (-1) hd
  rw [mul_zero] at hd'
  have hbound : ∀ n : ℕ, |c ^ n| ≤ ((|c| + 1) / 2) ^ n := fun n => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg c) hcd n
  refine limit_squeeze hd' hd (fun n => ?_) fun n => ?_
  · have := (abs_le.1 (hbound n)).1
    linarith
  · exact (abs_le.1 (hbound n)).2

/-- **Exercise 6.11(7), the identity.** For $`c \ne 1` the hyperfinite geometric sum is
$`\sum_{i<N} c^i = (1 - c^N)/(1 - c)`, by transfer of the identity for finite sums. -/
theorem hyperSum_geometric (hc : c ≠ 1) (x : ℝ*) :
    hyperSum (fun i => c ^ i) x = (1 - hyperSeq (fun n : ℕ => c ^ n) x) / (1 - c) := by
  have h : partialSum (fun i => c ^ i) = fun n : ℕ => (1 - c ^ n) / (1 - c) := by
    funext n
    rw [partialSum, geom_sum_eq hc, ← neg_sub (c ^ n) 1, ← neg_sub c 1, neg_div_neg_eq]
  have h1 : ((1 - c : ℝ) : ℝ*) = 1 - (c : ℝ*) := by
    rw [Hyperreal.coe_sub, Hyperreal.coe_one]
  rw [hyperSum, h, hyperSeq_div, hyperSeq_sub, hyperSeq_const, hyperSeq_const,
    Hyperreal.coe_one, h1]

/-- **Exercise 6.11(7)(a).** If $`|c| < 1` then the geometric series $`\sum c^i` converges,
with sum $`1/(1-c)`. For unlimited $`N` the power $`c^N` is infinitesimal, so the hyperfinite
sum $`(1 - c^N)/(1 - c)` is infinitely close to $`1/(1-c)`. -/
theorem seriesSum_geometric (hc : |c| < 1) : SeriesSum (fun i => c ^ i) (1 / (1 - c)) := by
  have hc1 : c ≠ 1 := fun h => by rw [h, abs_one] at hc; exact lt_irrefl _ hc
  rw [seriesSum_iff_forall_unlimited_infClose]
  intro N hN
  have hpow := hyperSeq_infClose_of_tendsto (tendsto_pow_zero_of_abs_lt_one hc) hN
  rw [Hyperreal.coe_zero] at hpow
  have h1 : (1 : ℝ*) - hyperSeq (fun n : ℕ => c ^ n) N ≊ 1 - 0 := (InfClose.refl 1).sub hpow
  have h2 := h1.mul_right (limited_coe (1 - c)⁻¹)
  rw [hyperSum_geometric hc1, div_eq_mul_inv, one_div, Hyperreal.coe_inv, Hyperreal.coe_sub,
    Hyperreal.coe_one]
  simpa [Hyperreal.coe_inv, Hyperreal.coe_sub] using h2

/-- **Exercise 6.11(7)(a)**, as a statement of convergence. -/
theorem seriesConverges_geometric (hc : |c| < 1) : SeriesConverges fun i => c ^ i :=
  ⟨_, seriesSum_geometric hc⟩

/-- **Exercise 6.11(7)(b).** If $`|c| < 1` then the block sum $`\sum_{i=M}^{N} c^i` is
infinitesimal for all unlimited $`M \le N`. This is result (a) with the Cauchy criterion. -/
theorem infinitesimal_hyperSumIcc_geometric (hc : |c| < 1) (hM : M ∈ unlimitedHyperNat)
    (hN : N ∈ unlimitedHyperNat) (hMN : M ≤ N) :
    Infinitesimal (hyperSumIcc (fun i => c ^ i) M N) :=
  seriesConverges_iff_forall_unlimited_hyperSumIcc.1 (seriesConverges_geometric hc)
    M hM N hN hMN

/-- **Exercise 6.11(6), counterexample to the printed statement.** For $`a_i = 2^{-i}` and
$`b_i = 1`, both series have positive terms and $`a_i / b_i` converges (to $`0`), but
$`\sum a_i` converges and $`\sum b_i` diverges. So the block sums of $`a` between unlimited
indices are infinitesimal while those of $`b` are not, and the printed claim needs the limit
of the ratios to be nonzero. -/
theorem exists_tendsto_div_seriesConverges_not_seriesConverges :
    ∃ a b : ℕ → ℝ, (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧
      (∃ c : ℝ, Tendsto (fun i => a i / b i) atTop (𝓝 c)) ∧
      SeriesConverges a ∧ ¬ SeriesConverges b := by
  have hhalf : |(1 / 2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  refine ⟨fun i => (1 / 2 : ℝ) ^ i, fun _ => 1, fun i => by positivity, fun _ => one_pos,
    ⟨0, ?_⟩, seriesConverges_geometric hhalf, fun h => ?_⟩
  · simpa using tendsto_pow_zero_of_abs_lt_one hhalf
  · exact one_ne_zero (limit_unique tendsto_const_nhds h.tendsto_zero)

/-- Transfer of nonvanishing: if no term of the sequence is zero then no value of the extended
sequence is zero. -/
theorem hyperSeq_ne_zero (ha : ∀ i, a i ≠ 0) (x : ℝ*) : hyperSeq a x ≠ 0 := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  intro h
  have h' : Hyperreal.ofSeq (fun n => a ⌊r n⌋₊) = Hyperreal.ofSeq fun _ => 0 := h
  rw [ofSeq_eq_ofSeq_iff] at h'
  obtain ⟨n, hn⟩ := h'.exists
  exact ha _ hn

/-- The extended sequence of ratios of consecutive absolute values is the ratio of the
absolute values of consecutive extended terms. -/
theorem hyperSeq_ratio (a : ℕ → ℝ) (hN : N ∈ ℕ*) :
    hyperSeq (fun i => |a (i + 1)| / |a i|) N = |hyperSeq a (N + 1)| / |hyperSeq a N| := by
  have e1 : hyperSeq (fun i => |a (i + 1)|) N = |hyperSeq a (N + 1)| := by
    rw [hyperSeq_add_one a hN]
    exact hyperSeq_abs (fun i => a (i + 1)) N
  rw [hyperSeq_div, e1, hyperSeq_abs]

/-- **Exercise 6.11(8)(a).** Suppose that no $`a_i` is zero and that the limit superior of the
ratios $`|a_{i+1}| / |a_i|` is smaller than $`1`. Then there is a positive real $`c < 1` with
$`|a_{N+1}| < c\,|a_N|` for all unlimited $`N`. The limit superior is taken in the extended
reals ({lit}`limSupE`), so that the hypothesis also says that the ratios are bounded above.
-/
theorem exists_forall_unlimited_ratio_lt (ha : ∀ i, a i ≠ 0)
    (h : limSupE (fun i => |a (i + 1)| / |a i|) < 1) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      ∀ N ∈ unlimitedHyperNat, |hyperSeq a (N + 1)| < c * |hyperSeq a N| := by
  obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real h
  have hy2' : y < 1 := by exact_mod_cast hy2
  refine ⟨max y (1 / 2), lt_max_of_lt_right (by norm_num), max_lt hy2' (by norm_num), ?_⟩
  intro N hN
  have hlt : limSupE (fun i => |a (i + 1)| / |a i|) < ((max y (1 / 2) : ℝ) : EReal) :=
    lt_of_lt_of_le hy1 (EReal.coe_le_coe_iff.2 (le_max_left _ _))
  have := (forall_unlimited_hyperSeq_lt_iff _ _).2 (eventually_lt_of_limSupE_lt hlt) N hN
  rw [hyperSeq_ratio a hN.1] at this
  exact (div_lt_iff₀ (abs_pos.2 (hyperSeq_ne_zero ha N))).1 this

/-- **Exercise 6.11(8)(b).** Under the hypotheses of the ratio test there are a positive real
$`c < 1` and a standard $`k` with $`|a_{n+1}| < c\,|a_n|` for all $`n \ge k`. This follows
from part (a) by principle (a). -/
theorem exists_forall_ge_ratio_lt (ha : ∀ i, a i ≠ 0)
    (h : limSupE (fun i => |a (i + 1)| / |a i|) < 1) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ k : ℕ, ∀ n, k ≤ n → |a (n + 1)| < c * |a n| := by
  obtain ⟨c, hc0, hc1, hc⟩ := exists_forall_unlimited_ratio_lt ha h
  refine ⟨c, hc0, hc1, ?_⟩
  have hev : ∀ᶠ n in atTop, |a (n + 1)| / |a n| < c := by
    rw [← forall_unlimited_hyperSeq_lt_iff]
    intro N hN
    rw [hyperSeq_ratio a hN.1]
    exact (div_lt_iff₀ (abs_pos.2 (hyperSeq_ne_zero ha N))).2 (hc N hN)
  obtain ⟨k, hk⟩ := eventually_atTop.1 hev
  exact ⟨k, fun n hn => (div_lt_iff₀ (abs_pos.2 (ha n))).1 (hk n hn)⟩

/-- **Exercise 6.11(8)(c), first inequality.** If $`|a_{n+1}| < c\,|a_n|` for all
$`n \ge k`, with $`c \ge 0`, then $`|a_{k+n}| \le c^n |a_k|` for all $`n`. The book writes a
strict inequality, which fails for $`n = 0`. -/
theorem abs_le_pow_mul_abs_of_ratio {k : ℕ} (hc : 0 ≤ c)
    (h : ∀ n, k ≤ n → |a (n + 1)| < c * |a n|) (n : ℕ) : |a (k + n)| ≤ c ^ n * |a k| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : |a (k + n + 1)| < c * |a (k + n)| := h (k + n) (Nat.le_add_right k n)
    have h2 : c * |a (k + n)| ≤ c * (c ^ n * |a k|) := mul_le_mul_of_nonneg_left ih hc
    rw [← add_assoc, pow_succ]
    calc |a (k + n + 1)| ≤ c * (c ^ n * |a k|) := h1.le.trans h2
      _ = c ^ n * c * |a k| := by ring

/-- **Exercise 6.11(8)(c), second inequality.** If $`|a_{n+1}| < c\,|a_n|` for all
$`n \ge k`, with $`c \ge 0`, then for all $`m` and $`n`
$$`\sum_{i=k+m}^{k+n} |a_i| \le \Bigl(\sum_{i=m}^{n} c^i\Bigr) |a_k|.` -/
theorem sum_Icc_abs_le_of_ratio {k : ℕ} (hc : 0 ≤ c)
    (h : ∀ n, k ≤ n → |a (n + 1)| < c * |a n|) (m n : ℕ) :
    ∑ i ∈ Finset.Icc (k + m) (k + n), |a i| ≤ (∑ i ∈ Finset.Icc m n, c ^ i) * |a k| := by
  rw [← Finset.image_add_left_Icc,
    Finset.sum_image (fun x _ y _ hxy => Nat.add_left_cancel hxy), Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => abs_le_pow_mul_abs_of_ratio hc h i

/-- **Exercise 6.11(8)(d) (ratio test, convergence).** Suppose that no $`a_i` is zero and that
$$`\limsup_{i\to\infty} \frac{|a_{i+1}|}{|a_i|} < 1.`
Then the series $`\sum a_i` is absolutely convergent. With $`c` and $`k` as in part (b), the
inequality of part (c) gives $`|a_i| \le (|a_k| / c^k)\, c^i` for $`i \ge k`, so for unlimited
$`M \le N` the block sum $`\sum_M^N |a_i|` is at most a real multiple of the block sum of the
geometric series, which is infinitesimal by result 7(b).

The hypothesis that the terms are nonzero is implicit in the book, where the ratios must be
defined. It cannot be dropped in Lean, where division by zero gives zero. -/
theorem seriesConverges_abs_of_limSupE_ratio_lt_one (ha : ∀ i, a i ≠ 0)
    (h : limSupE (fun i => |a (i + 1)| / |a i|) < 1) : SeriesConverges fun i => |a i| := by
  obtain ⟨c, hc0, hc1, k, hk⟩ := exists_forall_ge_ratio_lt ha h
  have hgeo : SeriesConverges fun i => |a k| / c ^ k * c ^ i :=
    ⟨_, (seriesSum_geometric (by rw [abs_of_pos hc0]; exact hc1)).const_mul _⟩
  refine seriesConverges_of_forall_ge_le (j := k) (fun i _ => abs_nonneg _) (fun i hi => ?_) hgeo
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hi
  have := abs_le_pow_mul_abs_of_ratio hc0.le hk n
  have hck : c ^ k ≠ 0 := (pow_pos hc0 k).ne'
  calc |a (k + n)| ≤ c ^ n * |a k| := this
    _ = |a k| / c ^ k * c ^ (k + n) := by
      rw [pow_add]
      field_simp

/-- **Exercise 6.11(8) (ratio test, convergence).** Under the hypotheses of the ratio test the
series $`\sum a_i` converges. -/
theorem seriesConverges_of_limSupE_ratio_lt_one (ha : ∀ i, a i ≠ 0)
    (h : limSupE (fun i => |a (i + 1)| / |a i|) < 1) : SeriesConverges a :=
  seriesConverges_of_abs (seriesConverges_abs_of_limSupE_ratio_lt_one ha h)

/-- **Exercise 6.11(9)(a), first part.** If the limit inferior of the ratios
$`|a_{i+1}| / |a_i|` is greater than $`1`, then $`|a_{N+1}| > |a_N|` for all unlimited
$`N`. The limit inferior is taken in the extended reals ({lit}`limInfE`); the value
$`+\infty` is allowed, which makes the statement slightly more general than the book's. -/
theorem abs_hyperSeq_lt_abs_hyperSeq_add_one
    (h : 1 < limInfE (fun i => |a (i + 1)| / |a i|)) (hN : N ∈ unlimitedHyperNat) :
    |hyperSeq a N| < |hyperSeq a (N + 1)| := by
  have h' : ((1 : ℝ) : EReal) < limInfE (fun i => |a (i + 1)| / |a i|) := by exact_mod_cast h
  have := (forall_unlimited_lt_hyperSeq_iff _ _).2 (eventually_gt_of_lt_limInfE h') N hN
  rw [hyperSeq_ratio a hN.1, Hyperreal.coe_one] at this
  rcases (abs_nonneg (hyperSeq a N)).eq_or_lt with h0 | h0
  · rw [← h0, div_zero] at this
    exact absurd this (not_lt.2 zero_le_one)
  · simpa using (lt_div_iff₀ h0).1 this

/-- **Exercise 6.11(9)(a), second part.** If the limit inferior of the ratios
$`|a_{i+1}| / |a_i|` is greater than $`1`, then there is a standard $`k` with
$`|a_n| > |a_k| > 0` for all $`n > k`. -/
theorem exists_forall_gt_abs_lt (h : 1 < limInfE (fun i => |a (i + 1)| / |a i|)) :
    ∃ k : ℕ, 0 < |a k| ∧ ∀ n, k < n → |a k| < |a n| := by
  have hev : ∀ᶠ n in atTop, |a n| - |a (n + 1)| < 0 := by
    rw [← forall_unlimited_hyperSeq_lt_iff]
    intro N hN
    have e1 : hyperSeq (fun i => |a (i + 1)|) N = |hyperSeq a (N + 1)| := by
      rw [hyperSeq_add_one a hN.1]
      exact hyperSeq_abs (fun i => a (i + 1)) N
    rw [hyperSeq_sub (fun i => |a i|) (fun i => |a (i + 1)|), e1, hyperSeq_abs,
      Hyperreal.coe_zero]
    linarith [abs_hyperSeq_lt_abs_hyperSeq_add_one h hN]
  obtain ⟨k, hk⟩ := eventually_atTop.1 hev
  have hstep : ∀ n, k ≤ n → |a n| < |a (n + 1)| := fun n hn => by linarith [hk n hn]
  refine ⟨k + 1, lt_of_le_of_lt (abs_nonneg _) (hstep k le_rfl), fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => exact hstep (k + 1) (Nat.le_succ k)
  | succ n hn ih => exact ih.trans (hstep n (by omega))

/-- **Exercise 6.11(9)(b) (ratio test, divergence).** If
$$`\liminf_{i\to\infty} \frac{|a_{i+1}|}{|a_i|} > 1`
then the series $`\sum a_i` diverges. With $`k` as in part (a), every extended term satisfies
$`|a_N| > |a_k| > 0` by transfer, so $`a_N` is not infinitesimal, whereas the terms of a
convergent series are infinitesimal at unlimited indices. -/
theorem not_seriesConverges_of_one_lt_limInfE_ratio
    (h : 1 < limInfE (fun i => |a (i + 1)| / |a i|)) : ¬ SeriesConverges a := by
  intro hconv
  obtain ⟨k, hk0, hk⟩ := exists_forall_gt_abs_lt h
  have hω := omega_mem_unlimitedHyperNat
  have h1 : ((|a k| : ℝ) : ℝ*) < hyperSeq (fun i => |a i|) ω :=
    (forall_unlimited_lt_hyperSeq_iff _ _).2
      ((eventually_gt_atTop k).mono fun n hn => hk n hn) ω hω
  rw [hyperSeq_abs] at h1
  have h2 := infinitesimal_iff_abs_lt.1 (hconv.infinitesimal_hyperSeq hω) |a k| hk0
  exact lt_irrefl _ (h1.trans h2)

/-- **Exercise 6.11(10).** For every real number $`x` and every unlimited hypernatural $`N`,
the hyperreal $`x^N / N!` is infinitesimal. For $`x \ne 0` the ratios of consecutive terms of
$`a_i = x^i / i!` are $`|x|/(i+1)`, which converge to $`0`; so their limit superior is $`0`,
the ratio test gives convergence of the series, and the terms of a convergent series are
infinitesimal at unlimited indices. -/
theorem infinitesimal_pow_div_factorial (x : ℝ) (hN : N ∈ unlimitedHyperNat) :
    Infinitesimal (hyperSeq (fun n : ℕ => x ^ n / (n.factorial : ℝ)) N) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have ht : Tendsto (fun n : ℕ => (0 : ℝ) ^ n / (n.factorial : ℝ)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [zero_pow (by omega), zero_div]
    have := hyperSeq_infClose_of_tendsto ht hN
    rwa [Hyperreal.coe_zero, ← infinitesimal_iff_infClose_zero] at this
  · set a : ℕ → ℝ := fun n => x ^ n / (n.factorial : ℝ) with ha
    have hne : ∀ i, a i ≠ 0 := fun i =>
      div_ne_zero (pow_ne_zero i hx) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i))
    have hratio : ∀ i, |a (i + 1)| / |a i| = |x| * (1 / ((i : ℝ) + 1)) := by
      intro i
      have hstep : a (i + 1) = a i * (x / ((i : ℝ) + 1)) := by
        simp only [ha, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
        have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
        have h2 : (i.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)
        field_simp
      have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      rw [hstep, abs_mul, mul_div_cancel_left₀ _ (abs_ne_zero.2 (hne i)), abs_div,
        abs_of_pos hpos, mul_one_div]
    have ht : Tendsto (fun i : ℕ => |a (i + 1)| / |a i|) atTop (𝓝 0) := by
      have := limit_const_mul |x| (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [mul_zero] at this
      exact this.congr fun i => (hratio i).symm
    have hb : ∃ b : ℝ, ∀ n, |(fun i : ℕ => |a (i + 1)| / |a i|) n| < b := by
      refine ⟨|x| + 1, fun n => ?_⟩
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hpos]
        linarith
      change |(|a (n + 1)| / |a n|)| < |x| + 1
      rw [hratio n, abs_of_nonneg (by positivity)]
      nlinarith [abs_nonneg x]
    have hlim : limSupE (fun i : ℕ => |a (i + 1)| / |a i|) < 1 := by
      rw [limSupE_eq_coe_limSup hb, ((tendsto_iff_limSup_eq_and_limInf_eq hb).1 ht).1]
      exact_mod_cast zero_lt_one
    exact (seriesConverges_of_limSupE_ratio_lt_one hne hlim).infinitesimal_hyperSeq hN

/-- **Exercise 6.11(11), nonnegativity.** A nonincreasing real sequence that converges to
$`0` has nonnegative terms: each term is at least the extended term $`a_\omega`, which is
infinitely close to $`0`. -/
theorem nonneg_of_antitone_of_tendsto_zero (hanti : Antitone a)
    (h0 : Tendsto a atTop (𝓝 0)) (i : ℕ) : 0 ≤ a i := by
  have hω := omega_mem_unlimitedHyperNat
  have h1 : hyperSeq a ω ≤ (a i : ℝ*) := by
    have hmono : Monotone fun n => -a n := fun m n h => neg_le_neg (hanti h)
    have := hyperSeq_mono hmono (natCast_mem_hyperNat i) hω.1
      (natCast_lt_of_mem_unlimitedHyperNat hω i).le
    rw [hyperSeq_neg, hyperSeq_neg, hyperSeq_natCast_real] at this
    linarith
  exact coe_le_coe_of_infClose_le (hyperSeq_infClose_of_tendsto h0 hω).symm h1

/-- **Exercise 6.11(11), alternating blocks.** For a nonincreasing sequence of nonnegative
reals, an alternating sum of consecutive terms starting with a plus sign at $`a_m` lies
between $`0` and $`a_m`. -/
theorem alternating_block_bounds (hanti : Antitone a) (hnn : ∀ i, 0 ≤ a i) (d m : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (d + 1), (-1 : ℝ) ^ i * a (m + i) ∧
      ∑ i ∈ Finset.range (d + 1), (-1 : ℝ) ^ i * a (m + i) ≤ a m := by
  induction d generalizing m with
  | zero => simp [hnn m]
  | succ d ih =>
    rw [Finset.sum_range_succ']
    have h := ih (m + 1)
    have heq : ∑ i ∈ Finset.range (d + 1), (-1 : ℝ) ^ (i + 1) * a (m + (i + 1)) =
        -∑ i ∈ Finset.range (d + 1), (-1 : ℝ) ^ i * a (m + 1 + i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ, show m + (i + 1) = m + 1 + i by omega]
      ring
    rw [heq]
    have hm : a (m + 1) ≤ a m := hanti (Nat.le_succ m)
    simp only [pow_zero, one_mul, add_zero]
    constructor <;> linarith [h.1, h.2]

/-- **Exercise 6.11(11), the inequality.** For a nonincreasing sequence of nonnegative reals
and $`m \le n`,
$$`\Bigl|\sum_{i=m}^{n} (-1)^i a_i\Bigr| \le a_m.`
The book's series starts at $`i = 1` with the sign $`(-1)^{i+1}`; indexing from $`0` the sign
is $`(-1)^i`. -/
theorem abs_sum_Icc_alternating_le (hanti : Antitone a) (hnn : ∀ i, 0 ≤ a i) {m n : ℕ}
    (h : m ≤ n) : |∑ i ∈ Finset.Icc m n, (-1 : ℝ) ^ i * a i| ≤ a m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hsum : ∑ i ∈ Finset.Icc m (m + d), (-1 : ℝ) ^ i * a i =
      (-1) ^ m * ∑ i ∈ Finset.range (d + 1), (-1 : ℝ) ^ i * a (m + i) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    have : m + d + 1 - m = d + 1 := by omega
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_add]
    ring
  have hb := alternating_block_bounds hanti hnn d m
  rw [hsum, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hb.1]
  exact hb.2

/-- **Exercise 6.11(11) (Leibniz's alternating series test).** If the real sequence $`a` is
nonincreasing and converges to $`0`, then the alternating series $`\sum (-1)^i a_i`
converges. By transfer of the inequality above, the block sum between unlimited
$`M \le N` is bounded in absolute value by $`a_M`, which is infinitesimal. -/
theorem seriesConverges_alternating (hanti : Antitone a) (h0 : Tendsto a atTop (𝓝 0)) :
    SeriesConverges fun i => (-1 : ℝ) ^ i * a i := by
  have hnn := nonneg_of_antitone_of_tendsto_zero hanti h0
  rw [seriesConverges_iff_forall_unlimited_hyperSumIcc]
  intro M hM N hN hMN
  have hinf : Infinitesimal (hyperSeq a M) := by
    have := hyperSeq_infClose_of_tendsto h0 hM
    rwa [Hyperreal.coe_zero, ← infinitesimal_iff_infClose_zero] at this
  refine hinf.of_abs_le (le_trans ?_ (le_abs_self _))
  obtain ⟨k, rfl⟩ := exists_hnat_eq hM.1
  obtain ⟨l, rfl⟩ := exists_hnat_eq hN.1
  rw [hyperSumIcc_hnat _ hMN, abs_ofSeq, hyperSeq_hnat, ofSeq_le_ofSeq_iff]
  exact (hnat_le_hnat_iff.1 hMN).mono fun n hn => abs_sum_Icc_alternating_le hanti hnn hn

end ExercisesSeries

end Goldblatt
