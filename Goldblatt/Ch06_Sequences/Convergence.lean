import Mathlib
import Goldblatt.Ch02_LargeSets
import Goldblatt.Ch03_Ultrapower
import Goldblatt.Ch05_GreatAndSmall

/-!
# 6 (part 1). Convergence, Boundedness and Cluster Points: Sections 6.1 to 6.7

This is the first of three parts of Chapter 6 (the overview is on the chapter page
{lit}`Goldblatt.Ch06_Sequences`). It sets up the extended terms of a real sequence and the two
transfer principles that move statements between the standard tails and the extended tail,
and then proves the nonstandard characterisations of convergence, boundedness, divergence to
infinity, the Cauchy property and cluster points, with the theorems that the book derives
from them: monotone convergence, the algebra of limits, Cauchy's criterion and the
Bolzano-Weierstrass theorem.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## Extended terms

A real sequence $`s` extends to the hypersequence {lit}`hyperSeq s` of Section 3.13. Its value
at an unlimited hypernatural $`N` is an _extended term_ $`s_N`, and the extended terms
together form the _extended tail_ of the sequence. This preliminary section is the technical
base of the chapter. It is not a numbered section of the book: it collects what the book
obtains by quoting the transfer principle for one sentence at a time.

In the ultrapower, a hypernatural is the class of a sequence $`k` of natural numbers, and the
extended term at that hypernatural is the class of the sequence $`n \mapsto s_{k_n}`. The
hypernatural is unlimited exactly when $`k_n` tends to infinity along the index ultrafilter.
So a statement about all extended terms is a statement about all the sequences
$`n \mapsto s_{k_n}` with $`k` tending to infinity along the ultrafilter, and it can be
compared with the behaviour of $`s` on its standard tails. The comparison is made by two
principles, which the book states in Section 6.8:

* a property that holds for every unlimited hypernatural holds for all but finitely many
  standard natural numbers, and conversely;
* a property that holds for some unlimited hypernatural holds for infinitely many standard
  natural numbers, and conversely.
-/

section ExtendedTerms

variable {s t : ℕ → ℝ} {N M x : ℝ*}

/-- **Chapter 6, extended terms.** The value of the hypersequence at the class of a real
sequence $`r` is the class of $`n \mapsto s_{\lfloor r_n \rfloor}`. -/
theorem hyperSeq_ofSeq (s : ℕ → ℝ) (r : ℕ → ℝ) :
    hyperSeq s (Hyperreal.ofSeq r) = Hyperreal.ofSeq fun n => s ⌊r n⌋₊ := rfl

/-- **Chapter 6, extended terms.** At the hypernatural $`[k_n]` the extended sequence takes
the value $`[s_{k_n}]`. -/
theorem hyperSeq_hnat (s : ℕ → ℝ) (k : ℕ → ℕ) :
    hyperSeq s (hnat k) = Hyperreal.ofSeq fun n => s (k n) :=
  hyperSeq_ofSeq_natCast s k

/-- **Chapter 6, extended terms.** At a standard natural number the extended sequence takes
the standard value. -/
theorem hyperSeq_natCast_real (s : ℕ → ℝ) (n : ℕ) : hyperSeq s (n : ℝ*) = (s n : ℝ*) :=
  hyperSeq_natCast s n

/-- Transfer of a termwise inequality: if $`s_n \le t_n` for all $`n` then the same holds for
the extended sequences at every argument. -/
theorem hyperSeq_le_hyperSeq (h : ∀ n, s n ≤ t n) (x : ℝ*) : hyperSeq s x ≤ hyperSeq t x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [hyperSeq_ofSeq, hyperSeq_ofSeq, ofSeq_le_ofSeq_iff]
  exact Eventually.of_forall fun n => h _

/-- The extension of a constant sequence is constant. -/
theorem hyperSeq_const (c : ℝ) (x : ℝ*) : hyperSeq (fun _ => c) x = (c : ℝ*) := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- Transfer of an upper bound: if $`s_n \le b` for all $`n` then every value of the extended
sequence is at most $`b`. -/
theorem hyperSeq_le_coe {b : ℝ} (h : ∀ n, s n ≤ b) (x : ℝ*) : hyperSeq s x ≤ b := by
  simpa [hyperSeq_const] using hyperSeq_le_hyperSeq (t := fun _ => b) h x

/-- Transfer of a lower bound: if $`b \le s_n` for all $`n` then every value of the extended
sequence is at least $`b`. -/
theorem coe_le_hyperSeq {b : ℝ} (h : ∀ n, b ≤ s n) (x : ℝ*) : (b : ℝ*) ≤ hyperSeq s x := by
  simpa [hyperSeq_const] using hyperSeq_le_hyperSeq (s := fun _ => b) h x

/-- The extension of a termwise sum is the sum of the extensions. -/
theorem hyperSeq_add (s t : ℕ → ℝ) (x : ℝ*) :
    hyperSeq (fun n => s n + t n) x = hyperSeq s x + hyperSeq t x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- The extension of a termwise difference is the difference of the extensions. -/
theorem hyperSeq_sub (s t : ℕ → ℝ) (x : ℝ*) :
    hyperSeq (fun n => s n - t n) x = hyperSeq s x - hyperSeq t x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- The extension of the termwise negative is the negative of the extension. -/
theorem hyperSeq_neg (s : ℕ → ℝ) (x : ℝ*) : hyperSeq (fun n => -s n) x = -hyperSeq s x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- The extension of a termwise product is the product of the extensions. -/
theorem hyperSeq_mul (s t : ℕ → ℝ) (x : ℝ*) :
    hyperSeq (fun n => s n * t n) x = hyperSeq s x * hyperSeq t x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- The extension of a constant multiple is the constant multiple of the extension. -/
theorem hyperSeq_const_mul (c : ℝ) (s : ℕ → ℝ) (x : ℝ*) :
    hyperSeq (fun n => c * s n) x = c * hyperSeq s x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- The extension of a termwise quotient is the quotient of the extensions. -/
theorem hyperSeq_div (s t : ℕ → ℝ) (x : ℝ*) :
    hyperSeq (fun n => s n / t n) x = hyperSeq s x / hyperSeq t x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- The extension of the termwise absolute value is the absolute value of the extension. -/
theorem hyperSeq_abs (s : ℕ → ℝ) (x : ℝ*) : hyperSeq (fun n => |s n|) x = |hyperSeq s x| := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [hyperSeq_ofSeq, hyperSeq_ofSeq, abs_ofSeq]

/-- **Chapter 6, extended terms.** The hypernatural $`[k_n]` is unlimited if and only if
$`k_n` tends to infinity along the index ultrafilter: for every $`m`, almost all $`k_n`
exceed $`m`. -/
theorem hnat_mem_unlimitedHyperNat_iff {k : ℕ → ℕ} :
    hnat k ∈ unlimitedHyperNat ↔ Tendsto k (hyperfilter ℕ) atTop := by
  rw [mem_unlimitedHyperNat, unlimited_iff_forall_nat,
    abs_of_nonneg (hyperNat_nonneg (hnat_mem_hyperNat k)), tendsto_atTop]
  constructor
  · rintro ⟨-, h⟩ m
    have := h m
    rw [natCast_eq_hnat, hnat_lt_hnat_iff] at this
    exact this.mono fun n hn => hn.le
  · intro h
    refine ⟨hnat_mem_hyperNat k, fun m => ?_⟩
    rw [natCast_eq_hnat, hnat_lt_hnat_iff]
    exact (h (m + 1)).mono fun n hn => hn

/-- **Chapter 6, extended terms.** Every unlimited hypernatural is the class of a sequence of
natural numbers that tends to infinity along the index ultrafilter. -/
theorem exists_hnat_of_mem_unlimitedHyperNat (hN : N ∈ unlimitedHyperNat) :
    ∃ k : ℕ → ℕ, Tendsto k (hyperfilter ℕ) atTop ∧ N = hnat k := by
  obtain ⟨k, rfl⟩ := exists_hnat_eq hN.1
  exact ⟨k, hnat_mem_unlimitedHyperNat_iff.1 hN, rfl⟩

/-- An unlimited hypernatural exceeds every standard natural number. -/
theorem natCast_lt_of_mem_unlimitedHyperNat (hN : N ∈ unlimitedHyperNat) (n : ℕ) :
    (n : ℝ*) < N :=
  natCast_lt_of_mem_hyperNat_of_notMem_range hN.1 hN.2 n

/-- A hypernatural above an unlimited hypernatural is unlimited. -/
theorem mem_unlimitedHyperNat_of_le (hM : M ∈ unlimitedHyperNat) (hN : N ∈ ℕ*) (h : M ≤ N) :
    N ∈ unlimitedHyperNat := by
  refine ⟨hN, ?_⟩
  rintro ⟨n, rfl⟩
  exact absurd h (not_le.2 (natCast_lt_of_mem_unlimitedHyperNat hM n))

/-- The successor of an unlimited hypernatural is an unlimited hypernatural. -/
theorem add_one_mem_unlimitedHyperNat (hN : N ∈ unlimitedHyperNat) :
    N + 1 ∈ unlimitedHyperNat :=
  mem_unlimitedHyperNat_of_le hN
    (add_mem_hyperNat hN.1 (by simpa using natCast_mem_hyperNat 1)) (by linarith)

/-- Transfer of the shift of index: $`s_{N+1}` is the extended term at $`N` of the shifted
sequence $`n \mapsto s_{n+1}`. -/
theorem hyperSeq_add_one (s : ℕ → ℝ) (hN : N ∈ ℕ*) :
    hyperSeq s (N + 1) = hyperSeq (fun n => s (n + 1)) N := by
  obtain ⟨k, rfl⟩ := exists_hnat_eq hN
  rw [← hnat_const_one, hnat_add, hyperSeq_hnat, hyperSeq_hnat]

/-- Transfer of monotonicity: the extension of a nondecreasing sequence is nondecreasing on
the hypernaturals. -/
theorem hyperSeq_mono (hs : Monotone s) (hM : M ∈ ℕ*) (hN : N ∈ ℕ*) (h : M ≤ N) :
    hyperSeq s M ≤ hyperSeq s N := by
  obtain ⟨k, rfl⟩ := exists_hnat_eq hM
  obtain ⟨l, rfl⟩ := exists_hnat_eq hN
  rw [hyperSeq_hnat, hyperSeq_hnat, ofSeq_le_ofSeq_iff]
  exact (hnat_le_hnat_iff.1 h).mono fun n hn => hs hn

/-- Transfer of a property that holds from some index on: if $`P(n)` holds for all standard
$`n \ge j`, then for every hypernatural $`[k_n] \ge j` it holds at almost all $`k_n`. -/
theorem eventually_of_natCast_le_hnat {P : ℕ → Prop} {j : ℕ} {k : ℕ → ℕ}
    (h : ∀ n, j ≤ n → P n) (hk : (j : ℝ*) ≤ hnat k) : ∀ᶠ n in hyperfilter ℕ, P (k n) := by
  rw [natCast_eq_hnat, hnat_le_hnat_iff] at hk
  exact hk.mono fun n hn => h _ hn

/-- **Section 6.8, principle (a), sequence form.** A property of natural numbers holds from
some point on if and only if, for every sequence $`k` of natural numbers tending to infinity
along the index ultrafilter, it holds at almost all $`k_n`. The forward direction is
universal transfer. The reverse direction is existential transfer: if the property failed
arbitrarily far out, choosing a failure beyond each $`n` would give a sequence $`k` tending to
infinity at whose terms the property always fails. -/
theorem eventually_atTop_iff_forall_tendsto_hyperfilter {P : ℕ → Prop} :
    (∀ᶠ n in atTop, P n) ↔
      ∀ k : ℕ → ℕ, Tendsto k (hyperfilter ℕ) atTop → ∀ᶠ n in hyperfilter ℕ, P (k n) := by
  constructor
  · intro h k hk
    exact hk.eventually h
  · intro h
    by_contra hne
    rw [not_eventually, frequently_atTop] at hne
    choose k hk hk' using hne
    have hkt : Tendsto k (hyperfilter ℕ) atTop :=
      (tendsto_atTop_mono hk tendsto_id).mono_left Nat.hyperfilter_le_atTop
    obtain ⟨n, hn⟩ := (h k hkt).exists
    exact hk' n hn

/-- **Section 6.8, principle (b), sequence form.** A property of natural numbers holds for
arbitrarily large standard numbers if and only if there is a sequence $`k` tending to infinity
along the index ultrafilter such that it holds at almost all $`k_n`. -/
theorem frequently_atTop_iff_exists_tendsto_hyperfilter {P : ℕ → Prop} :
    (∃ᶠ n in atTop, P n) ↔
      ∃ k : ℕ → ℕ, Tendsto k (hyperfilter ℕ) atTop ∧ ∀ᶠ n in hyperfilter ℕ, P (k n) := by
  rw [Filter.Frequently, eventually_atTop_iff_forall_tendsto_hyperfilter]
  simp only [not_forall, almostAll_not, not_not, exists_prop]

/-- **Section 6.8, principle (a).** If a property holds for all unlimited hypernaturals then
it holds for all but finitely many standard natural numbers, and conversely. Here the property
is membership in a set $`A` of natural numbers, read on the hypernaturals as membership in the
enlargement of $`A`. -/
theorem forall_unlimited_mem_starSet_iff (A : Set ℕ) :
    (∀ N ∈ unlimitedHyperNat, N ∈ ⋆((fun n : ℕ => (n : ℝ)) '' A)) ↔ ∀ᶠ n in atTop, n ∈ A := by
  rw [eventually_atTop_iff_forall_tendsto_hyperfilter]
  have key : ∀ k : ℕ → ℕ, hnat k ∈ ⋆((fun n : ℕ => (n : ℝ)) '' A) ↔
      ∀ᶠ n in hyperfilter ℕ, k n ∈ A := by
    intro k
    rw [hnat, hyperreal_ofSeq_mem_starSet]
    simp
  constructor
  · intro h k hk
    exact (key k).1 (h _ (hnat_mem_unlimitedHyperNat_iff.2 hk))
  · intro h N hN
    obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
    exact (key k).2 (h k hk)

/-- **Section 6.8, principle (b).** If a property holds for some unlimited hypernatural then
it holds for arbitrarily large standard natural numbers, and conversely. -/
theorem exists_unlimited_mem_starSet_iff (A : Set ℕ) :
    (∃ N ∈ unlimitedHyperNat, N ∈ ⋆((fun n : ℕ => (n : ℝ)) '' A)) ↔ ∃ᶠ n in atTop, n ∈ A := by
  rw [frequently_atTop_iff_exists_tendsto_hyperfilter]
  have key : ∀ k : ℕ → ℕ, hnat k ∈ ⋆((fun n : ℕ => (n : ℝ)) '' A) ↔
      ∀ᶠ n in hyperfilter ℕ, k n ∈ A := by
    intro k
    rw [hnat, hyperreal_ofSeq_mem_starSet]
    simp
  constructor
  · rintro ⟨N, hN, h⟩
    obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
    exact ⟨k, hk, (key k).1 h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨hnat k, hnat_mem_unlimitedHyperNat_iff.2 hk, (key k).2 h⟩

/-- **Section 6.8, principle (a), for the terms of a sequence.** The whole extended tail of
$`s` lies in the enlargement of a set $`A` of reals if and only if some standard tail of $`s`
lies in $`A`. -/
theorem forall_unlimited_hyperSeq_mem_starSet_iff (s : ℕ → ℝ) (A : Set ℝ) :
    (∀ N ∈ unlimitedHyperNat, hyperSeq s N ∈ ⋆A) ↔ ∀ᶠ n in atTop, s n ∈ A := by
  rw [eventually_atTop_iff_forall_tendsto_hyperfilter]
  constructor
  · intro h k hk
    have := h _ (hnat_mem_unlimitedHyperNat_iff.2 hk)
    rwa [hyperSeq_hnat, hyperreal_ofSeq_mem_starSet] at this
  · intro h N hN
    obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
    rw [hyperSeq_hnat, hyperreal_ofSeq_mem_starSet]
    exact h k hk

/-- **Section 6.8, principle (b), for the terms of a sequence.** Some extended term of $`s`
lies in the enlargement of a set $`A` of reals if and only if $`s_n \in A` for arbitrarily
large standard $`n`. -/
theorem exists_unlimited_hyperSeq_mem_starSet_iff (s : ℕ → ℝ) (A : Set ℝ) :
    (∃ N ∈ unlimitedHyperNat, hyperSeq s N ∈ ⋆A) ↔ ∃ᶠ n in atTop, s n ∈ A := by
  rw [frequently_atTop_iff_exists_tendsto_hyperfilter]
  constructor
  · rintro ⟨N, hN, h⟩
    obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
    rw [hyperSeq_hnat, hyperreal_ofSeq_mem_starSet] at h
    exact ⟨k, hk, h⟩
  · rintro ⟨k, hk, h⟩
    refine ⟨hnat k, hnat_mem_unlimitedHyperNat_iff.2 hk, ?_⟩
    rwa [hyperSeq_hnat, hyperreal_ofSeq_mem_starSet]

/-- Principle (a) for strict upper bounds: every extended term is below the real number $`r`
if and only if some standard tail is below $`r`. -/
theorem forall_unlimited_hyperSeq_lt_iff (s : ℕ → ℝ) (r : ℝ) :
    (∀ N ∈ unlimitedHyperNat, hyperSeq s N < r) ↔ ∀ᶠ n in atTop, s n < r := by
  simpa [starSet_Iio_real] using forall_unlimited_hyperSeq_mem_starSet_iff s (Iio r)

/-- Principle (a) for strict lower bounds: every extended term is above the real number $`r`
if and only if some standard tail is above $`r`. -/
theorem forall_unlimited_lt_hyperSeq_iff (s : ℕ → ℝ) (r : ℝ) :
    (∀ N ∈ unlimitedHyperNat, (r : ℝ*) < hyperSeq s N) ↔ ∀ᶠ n in atTop, r < s n := by
  simpa [starSet_Ioi_real] using forall_unlimited_hyperSeq_mem_starSet_iff s (Ioi r)

/-- Principle (b) for strict upper bounds: some extended term is below the real number $`r`
if and only if $`s_n < r` for arbitrarily large standard $`n`. -/
theorem exists_unlimited_hyperSeq_lt_iff (s : ℕ → ℝ) (r : ℝ) :
    (∃ N ∈ unlimitedHyperNat, hyperSeq s N < r) ↔ ∃ᶠ n in atTop, s n < r := by
  simpa [starSet_Iio_real] using exists_unlimited_hyperSeq_mem_starSet_iff s (Iio r)

/-- Principle (b) for strict lower bounds: some extended term is above the real number $`r`
if and only if $`r < s_n` for arbitrarily large standard $`n`. -/
theorem exists_unlimited_lt_hyperSeq_iff (s : ℕ → ℝ) (r : ℝ) :
    (∃ N ∈ unlimitedHyperNat, (r : ℝ*) < hyperSeq s N) ↔ ∃ᶠ n in atTop, r < s n := by
  simpa [starSet_Ioi_real] using exists_unlimited_hyperSeq_mem_starSet_iff s (Ioi r)

/-- The distance between two classes is below a real number if and only if the distance
between the terms is below it almost everywhere. -/
theorem abs_ofSeq_sub_ofSeq_lt_iff {f g : ℕ → ℝ} {r : ℝ} :
    |Hyperreal.ofSeq f - Hyperreal.ofSeq g| < r ↔ ∀ᶠ n in hyperfilter ℕ, |f n - g n| < r := by
  have : Hyperreal.ofSeq f - Hyperreal.ofSeq g = Hyperreal.ofSeq fun n => f n - g n := rfl
  rw [this, abs_ofSeq, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]

/-- Two classes are infinitely close if and only if, for every positive real
$`\varepsilon`, the terms are within $`\varepsilon` of each other almost everywhere. -/
theorem ofSeq_infClose_ofSeq_iff {f g : ℕ → ℝ} :
    Hyperreal.ofSeq f ≊ Hyperreal.ofSeq g ↔
      ∀ η : ℝ, 0 < η → ∀ᶠ n in hyperfilter ℕ, |f n - g n| < η := by
  rw [infClose_iff_abs_lt]
  exact forall₂_congr fun η _ => abs_ofSeq_sub_ofSeq_lt_iff

/-- **Chapter 6, extended terms.** The class of a real sequence $`f` is infinitely close to
the real number $`L` if and only if $`f` converges to $`L` along the index ultrafilter. -/
theorem ofSeq_infClose_coe_iff {f : ℕ → ℝ} {L : ℝ} :
    Hyperreal.ofSeq f ≊ (L : ℝ*) ↔ Tendsto f (hyperfilter ℕ) (𝓝 L) := by
  rw [coe_eq_ofSeq_const, ofSeq_infClose_ofSeq_iff, Metric.tendsto_nhds]
  simp only [Real.dist_eq, gt_iff_lt]

/-- The extended term at $`[k_n]` is infinitely close to $`L` if and only if $`s_{k_n}`
converges to $`L` along the index ultrafilter. -/
theorem hyperSeq_hnat_infClose_coe_iff {k : ℕ → ℕ} {L : ℝ} :
    hyperSeq s (hnat k) ≊ (L : ℝ*) ↔ Tendsto (fun n => s (k n)) (hyperfilter ℕ) (𝓝 L) := by
  rw [hyperSeq_hnat, ofSeq_infClose_coe_iff]

/-- A hyperreal squeezed between two hyperreals that are infinitely close to $`c` is
infinitely close to $`c`. -/
theorem infClose_of_le_of_le {a b c : ℝ*} (h₁ : a ≤ x) (h₂ : x ≤ b) (ha : a ≊ c)
    (hb : b ≊ c) : x ≊ c := by
  rw [infClose_iff_abs_lt] at *
  intro r hr
  have h1 := abs_lt.1 (ha r hr)
  have h2 := abs_lt.1 (hb r hr)
  rw [abs_lt]
  constructor <;> linarith

/-- $`-b` is positive unlimited exactly when $`b` is negative unlimited. -/
theorem posUnlimited_neg_iff {b : ℝ*} : PosUnlimited (-b) ↔ NegUnlimited b := by
  constructor
  · intro h r
    have := h (-r)
    rw [Hyperreal.coe_neg] at this
    linarith
  · intro h r
    have := h (-r)
    rw [Hyperreal.coe_neg] at this
    linarith

/-- A hyperreal is limited exactly when it is neither positive unlimited nor negative
unlimited. -/
theorem limited_iff_not_posUnlimited_and_not_negUnlimited {b : ℝ*} :
    Limited b ↔ ¬ PosUnlimited b ∧ ¬ NegUnlimited b := by
  rw [← not_unlimited_iff_limited, Unlimited, not_or]

/-- If the extended sequence takes an unlimited value at a hypernatural $`N`, then $`N` is
unlimited, because at a standard $`n` the value is the real number $`s_n`. -/
theorem mem_unlimitedHyperNat_of_not_limited_hyperSeq (hN : N ∈ ℕ*)
    (h : ¬ Limited (hyperSeq s N)) : N ∈ unlimitedHyperNat := by
  refine ⟨hN, ?_⟩
  rintro ⟨n, rfl⟩
  exact h (by rw [hyperSeq_natCast_real]; exact limited_coe _)

end ExtendedTerms

/-!
## 6.1 Convergence

The standard definition says that every interval $`(L - \varepsilon, L + \varepsilon)`
contains a standard tail of the sequence. The nonstandard characterisation replaces the
family of tails by the single extended tail and the family of intervals by the single halo of
$`L`: the sequence converges to $`L` exactly when every extended term is infinitely close to
$`L`. This is the lemma {lit}`tendsto_iff_forall_unlimited_infClose`, stated for Mathlib's
notion of convergence of a sequence, and it is the entry point for the later chapters.
-/

section Convergence

variable {s t : ℕ → ℝ} {L M : ℝ} {N : ℝ*}

/-- **Theorem 6.1.1.** A real sequence $`s` converges to the real number $`L` if and only if
$`s_N \simeq L` for every unlimited hypernatural $`N`. Convergence is Mathlib's
{lit}`Tendsto s atTop (𝓝 L)`.

For the forward direction, a tail of $`s` within $`\varepsilon` of $`L` transfers to the
extended sequence beyond a standard index, and every unlimited $`N` is beyond it. For the
converse, the extended tail lies in the enlargement of
$`(L - \varepsilon, L + \varepsilon)`, so by principle (a) some standard tail lies in the
interval. -/
theorem tendsto_iff_forall_unlimited_infClose :
    Tendsto s atTop (𝓝 L) ↔ ∀ N ∈ unlimitedHyperNat, hyperSeq s N ≊ (L : ℝ*) := by
  constructor
  · intro h N hN
    obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
    exact hyperSeq_hnat_infClose_coe_iff.2 (h.comp hk)
  · intro h
    rw [Metric.tendsto_nhds]
    intro η hη
    rw [eventually_atTop_iff_forall_tendsto_hyperfilter]
    intro k hk
    exact Metric.tendsto_nhds.1
      (hyperSeq_hnat_infClose_coe_iff.1 (h _ (hnat_mem_unlimitedHyperNat_iff.2 hk))) η hη

/-- **Theorem 6.1.1**, forward direction as a rule: the extended terms of a sequence that
converges to $`L` are infinitely close to $`L`. -/
theorem hyperSeq_infClose_of_tendsto (h : Tendsto s atTop (𝓝 L)) (hN : N ∈ unlimitedHyperNat) :
    hyperSeq s N ≊ (L : ℝ*) :=
  tendsto_iff_forall_unlimited_infClose.1 h N hN

/-- **Theorem 6.1.1**, in terms of halos: $`s` converges to $`L` if and only if the extended
tail of $`s` is contained in the halo of $`L`. -/
theorem tendsto_iff_extendedTail_subset_hal :
    Tendsto s atTop (𝓝 L) ↔ hyperSeq s '' unlimitedHyperNat ⊆ hal (L : ℝ*) := by
  rw [tendsto_iff_forall_unlimited_infClose, image_subset_iff]
  exact forall₂_congr fun N _ => by rw [mem_preimage, mem_hal, infClose_comm]

/-- **Theorem 6.1.1, consequence.** The limit of a convergent sequence is the shadow of each
of its extended terms. -/
theorem sh_hyperSeq_of_tendsto (h : Tendsto s atTop (𝓝 L)) (hN : N ∈ unlimitedHyperNat) :
    sh (hyperSeq s N) = L :=
  sh_eq_of_infClose (hyperSeq_infClose_of_tendsto h hN)

/-- **Section 6.1, non-vacuity.** The sequence $`1/(n+1)` converges to $`0`, and its extended
term at $`\omega` is a nonzero infinitesimal. -/
theorem hyperSeq_one_div_omega :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) ∧
      Infinitesimal (hyperSeq (fun n : ℕ => 1 / ((n : ℝ) + 1)) ω) ∧
      hyperSeq (fun n : ℕ => 1 / ((n : ℝ) + 1)) ω ≠ 0 := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine ⟨h, ?_, ?_⟩
  · have := hyperSeq_infClose_of_tendsto h omega_mem_unlimitedHyperNat
    rwa [Hyperreal.coe_zero, ← infinitesimal_iff_infClose_zero] at this
  · rw [hyperSeq_omega]
    intro h0
    have h0' : Hyperreal.ofSeq (fun n : ℕ => 1 / ((n : ℝ) + 1)) = Hyperreal.ofSeq fun _ => 0 := h0
    rw [ofSeq_eq_ofSeq_iff] at h0'
    obtain ⟨n, hn⟩ := h0'.exists
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

end Convergence

/-!
## 6.2 Monotone Convergence

The first application is a proof that a bounded monotone sequence converges. For a
nondecreasing sequence bounded above, every extended term is limited, and its shadow is shown
to be the least upper bound of the set of terms. A set has only one least upper bound, so all
extended terms have the same shadow and the sequence converges to it by Theorem 6.1.1. The
section ends with the book's example: the powers of a number strictly between $`0` and $`1`
converge to $`0`.
-/

section MonotoneConvergence

variable {s : ℕ → ℝ} {N : ℝ*}

/-- **Theorem 6.2.1, key step.** For a nondecreasing real sequence that is bounded above,
every extended term is limited and its shadow is the least upper bound of the set of terms.
-/
theorem Monotone.isLUB_sh_hyperSeq (hs : Monotone s) (hb : BddAbove (range s))
    (hN : N ∈ unlimitedHyperNat) :
    Limited (hyperSeq s N) ∧ IsLUB (range s) (sh (hyperSeq s N)) := by
  obtain ⟨b, hb⟩ := hb
  have hle : ∀ n, s n ≤ b := fun n => hb ⟨n, rfl⟩
  have hup : hyperSeq s N ≤ b := hyperSeq_le_coe hle N
  have hlow : ∀ n : ℕ, (s n : ℝ*) ≤ hyperSeq s N := fun n => by
    rw [← hyperSeq_natCast_real]
    exact hyperSeq_mono hs (natCast_mem_hyperNat n) hN.1
      (natCast_lt_of_mem_unlimitedHyperNat hN n).le
  have hlim : Limited (hyperSeq s N) :=
    ⟨s 0 - 1, b + 1, lt_of_lt_of_le (Hyperreal.coe_lt_coe.2 (by linarith)) (hlow 0),
      lt_of_le_of_lt hup (Hyperreal.coe_lt_coe.2 (by linarith))⟩
  refine ⟨hlim, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact hlim.le_sh (hlow n)
  · intro r hr
    exact hlim.sh_le (hyperSeq_le_coe (fun n => hr ⟨n, rfl⟩) N)

/-- **Theorem 6.2.1 (1).** A nondecreasing real sequence that is bounded above converges, and
its limit is the least upper bound of its terms. The limit is produced as the common shadow
of the extended terms. -/
theorem Monotone.exists_isLUB_tendsto (hs : Monotone s) (hb : BddAbove (range s)) :
    ∃ L : ℝ, IsLUB (range s) L ∧ Tendsto s atTop (𝓝 L) := by
  obtain ⟨hlim, hlub⟩ := Monotone.isLUB_sh_hyperSeq hs hb omega_mem_unlimitedHyperNat
  refine ⟨_, hlub, tendsto_iff_forall_unlimited_infClose.2 fun N hN => ?_⟩
  obtain ⟨hlimN, hlubN⟩ := Monotone.isLUB_sh_hyperSeq hs hb hN
  rw [← hlubN.unique hlub]
  exact hlimN.infClose_sh

/-- **Theorem 6.2.1 (2).** A nonincreasing real sequence that is bounded below converges, and
its limit is the greatest lower bound of its terms. This is case (1) applied to the sequence
of negatives. -/
theorem Antitone.exists_isGLB_tendsto (hs : Antitone s) (hb : BddBelow (range s)) :
    ∃ L : ℝ, IsGLB (range s) L ∧ Tendsto s atTop (𝓝 L) := by
  obtain ⟨b, hb⟩ := hb
  have hmono : Monotone fun n => -s n := fun m n h => neg_le_neg (hs h)
  have hbdd : BddAbove (range fun n => -s n) :=
    ⟨-b, by rintro _ ⟨n, rfl⟩; exact neg_le_neg (hb ⟨n, rfl⟩)⟩
  obtain ⟨L, hlub, hL⟩ := Monotone.exists_isLUB_tendsto hmono hbdd
  refine ⟨-L, ⟨?_, ?_⟩, tendsto_iff_forall_unlimited_infClose.2 fun N hN => ?_⟩
  · rintro _ ⟨n, rfl⟩
    have := hlub.1 ⟨n, rfl⟩
    simp only at this
    linarith
  · intro r hr
    have : L ≤ -r := hlub.2 (by rintro _ ⟨n, rfl⟩; exact neg_le_neg (hr ⟨n, rfl⟩))
    linarith
  · have h := (hyperSeq_infClose_of_tendsto hL hN).neg
    rwa [hyperSeq_neg, neg_neg, ← Hyperreal.coe_neg] at h

/-- **Theorem 6.2.1.** A real sequence converges if it is nondecreasing and bounded above, or
nonincreasing and bounded below. -/
theorem exists_tendsto_of_monotone_or_antitone
    (h : (Monotone s ∧ BddAbove (range s)) ∨ (Antitone s ∧ BddBelow (range s))) :
    ∃ L : ℝ, Tendsto s atTop (𝓝 L) := by
  rcases h with ⟨hs, hb⟩ | ⟨hs, hb⟩
  · obtain ⟨L, -, hL⟩ := Monotone.exists_isLUB_tendsto hs hb
    exact ⟨L, hL⟩
  · obtain ⟨L, -, hL⟩ := Antitone.exists_isGLB_tendsto hs hb
    exact ⟨L, hL⟩

/-- **Section 6.2, application.** If $`0 < c < 1` then $`c^n` converges to $`0`. The sequence
is nonincreasing and bounded below, so it has a limit $`L`. For an unlimited $`N`, both
$`c^N` and $`c^{N+1} = c \cdot c^N` are infinitely close to $`L`, so $`L \simeq cL`; both
sides are real, so $`L = cL` and therefore $`L = 0`. -/
theorem tendsto_pow_zero_of_pos_of_lt_one {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) := by
  have hanti : Antitone fun n : ℕ => c ^ n := fun m n h =>
    pow_le_pow_of_le_one h0.le h1.le h
  have hbdd : BddBelow (range fun n : ℕ => c ^ n) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact pow_nonneg h0.le n⟩
  obtain ⟨L, -, hL⟩ := Antitone.exists_isGLB_tendsto hanti hbdd
  have hω := omega_mem_unlimitedHyperNat
  have h1' : hyperSeq (fun n : ℕ => c ^ n) (ω + 1) ≊ (L : ℝ*) :=
    hyperSeq_infClose_of_tendsto hL (add_one_mem_unlimitedHyperNat hω)
  have h2 : hyperSeq (fun n : ℕ => c ^ n) (ω + 1) =
      c * hyperSeq (fun n : ℕ => c ^ n) ω := by
    rw [hyperSeq_add_one _ hω.1, ← hyperSeq_const_mul]
    congr 1
    funext n
    rw [pow_succ, mul_comm]
  have h3 : (c : ℝ*) * hyperSeq (fun n : ℕ => c ^ n) ω ≊ (c : ℝ*) * (L : ℝ*) :=
    (hyperSeq_infClose_of_tendsto hL hω).mul_left (limited_coe c)
  have h4 : (L : ℝ*) ≊ ((c * L : ℝ) : ℝ*) := by
    rw [Hyperreal.coe_mul]
    exact h1'.symm.trans (h2 ▸ h3)
  have h5 : L = c * L := infClose_coe_iff.1 h4
  have hL0 : L = 0 := by
    have : (1 - c) * L = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  rwa [hL0] at hL

end MonotoneConvergence

/-!
## 6.3 Limits

A sequence has at most one limit, since an extended term cannot be infinitely close to two
different real numbers. The algebra of limits follows from the corresponding rules for
infinite closeness (Exercise 5.7(1)): sums, constant multiples, products and quotients of
convergent sequences converge to the expected limits.
-/

section Limits

variable {s t : ℕ → ℝ} {L M : ℝ}

/-- **Section 6.3, uniqueness of limits.** A real sequence has at most one limit: an extended
term is infinitely close to both limits, so the limits are infinitely close real numbers and
hence equal. -/
theorem limit_unique (hL : Tendsto s atTop (𝓝 L)) (hM : Tendsto s atTop (𝓝 M)) : L = M :=
  infClose_coe_iff.1
    ((hyperSeq_infClose_of_tendsto hL omega_mem_unlimitedHyperNat).symm.trans
      (hyperSeq_infClose_of_tendsto hM omega_mem_unlimitedHyperNat))

/-- **Theorem 6.3.1 (1).** If $`s_n \to L` and $`t_n \to M` then $`s_n + t_n \to L + M`. -/
theorem limit_add (hs : Tendsto s atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 M)) :
    Tendsto (fun n => s n + t n) atTop (𝓝 (L + M)) := by
  rw [tendsto_iff_forall_unlimited_infClose]
  intro N hN
  rw [hyperSeq_add, Hyperreal.coe_add]
  exact (hyperSeq_infClose_of_tendsto hs hN).add (hyperSeq_infClose_of_tendsto ht hN)

/-- **Theorem 6.3.1 (2).** If $`s_n \to L` then $`c s_n \to cL` for every real $`c`. -/
theorem limit_const_mul (c : ℝ) (hs : Tendsto s atTop (𝓝 L)) :
    Tendsto (fun n => c * s n) atTop (𝓝 (c * L)) := by
  rw [tendsto_iff_forall_unlimited_infClose]
  intro N hN
  rw [hyperSeq_const_mul, Hyperreal.coe_mul]
  exact (hyperSeq_infClose_of_tendsto hs hN).mul_left (limited_coe c)

/-- **Theorem 6.3.1 (3).** If $`s_n \to L` and $`t_n \to M` then $`s_n t_n \to LM`. -/
theorem limit_mul (hs : Tendsto s atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 M)) :
    Tendsto (fun n => s n * t n) atTop (𝓝 (L * M)) := by
  rw [tendsto_iff_forall_unlimited_infClose]
  intro N hN
  have h1 := hyperSeq_infClose_of_tendsto hs hN
  have h2 := hyperSeq_infClose_of_tendsto ht hN
  rw [hyperSeq_mul, Hyperreal.coe_mul]
  exact h1.mul h2 (limited_of_infClose_coe h1) (limited_of_infClose_coe h2)

/-- **Theorem 6.3.1 (4).** If $`s_n \to L` and $`t_n \to M` with $`M \ne 0` then
$`s_n / t_n \to L / M`. -/
theorem limit_div (hs : Tendsto s atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 M)) (hM : M ≠ 0) :
    Tendsto (fun n => s n / t n) atTop (𝓝 (L / M)) := by
  rw [tendsto_iff_forall_unlimited_infClose]
  intro N hN
  have h1 := hyperSeq_infClose_of_tendsto hs hN
  have h2 := hyperSeq_infClose_of_tendsto ht hN
  rw [hyperSeq_div, Hyperreal.coe_div]
  refine h1.div h2 (limited_of_infClose_coe h1) (limited_of_infClose_coe h2) fun h0 => hM ?_
  rw [← Hyperreal.coe_zero] at h0
  exact infClose_coe_iff.1 (h2.symm.trans h0)

/-- **Theorem 6.3.1, supplement.** If $`s_n \to L` and $`t_n \to M` then
$`s_n - t_n \to L - M`. The book does not list differences; the proof is the same. -/
theorem limit_sub (hs : Tendsto s atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 M)) :
    Tendsto (fun n => s n - t n) atTop (𝓝 (L - M)) := by
  rw [tendsto_iff_forall_unlimited_infClose]
  intro N hN
  rw [hyperSeq_sub, Hyperreal.coe_sub]
  exact (hyperSeq_infClose_of_tendsto hs hN).sub (hyperSeq_infClose_of_tendsto ht hN)

end Limits

/-!
## 6.4 Boundedness and Divergence

A sequence is bounded exactly when all of its extended terms are limited. The two halves of
the statement can be separated: boundedness above means that no extended term is positive
unlimited, and boundedness below means that none is negative unlimited. At the other extreme,
the sequence diverges to infinity exactly when every extended term is positive unlimited.

The implication from the extended terms to a standard bound is an existential transfer. In
the ultrapower it reads as follows: if the sequence had no upper bound, choosing for each
$`j` a term above $`j` would produce a hypernatural at which the extended sequence is positive
unlimited, and that hypernatural cannot be standard.
-/

section Boundedness

variable {s : ℕ → ℝ} {N : ℝ*}

/-- **Section 6.4, refinement of Theorem 6.4.1.** A real sequence is bounded above if and only
if it has no positive unlimited extended term. -/
theorem bddAbove_range_iff_forall_unlimited_not_posUnlimited :
    BddAbove (range s) ↔ ∀ N ∈ unlimitedHyperNat, ¬ PosUnlimited (hyperSeq s N) := by
  constructor
  · rintro ⟨b, hb⟩ N - h
    exact absurd (hyperSeq_le_coe (fun n => hb ⟨n, rfl⟩) N) (not_le.2 (h b))
  · intro h
    by_contra hne
    rw [not_bddAbove_iff] at hne
    have hne' : ∀ j : ℕ, ∃ n, (j : ℝ) < s n := fun j => by
      obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hne j
      exact ⟨n, hn⟩
    choose k hk using hne'
    have hpos : PosUnlimited (hyperSeq s (hnat k)) := by
      intro r
      rw [hyperSeq_hnat, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
      obtain ⟨m, hm⟩ := exists_nat_gt r
      exact eventually_hyperfilter_of_forall_ge m fun n hn =>
        lt_trans (lt_of_lt_of_le hm (Nat.cast_le.2 hn)) (hk n)
    exact h _ (mem_unlimitedHyperNat_of_not_limited_hyperSeq (hnat_mem_hyperNat k)
      hpos.unlimited.not_limited) hpos

/-- **Section 6.4, refinement of Theorem 6.4.1.** A real sequence is bounded below if and only
if it has no negative unlimited extended term. -/
theorem bddBelow_range_iff_forall_unlimited_not_negUnlimited :
    BddBelow (range s) ↔ ∀ N ∈ unlimitedHyperNat, ¬ NegUnlimited (hyperSeq s N) := by
  have h := bddAbove_range_iff_forall_unlimited_not_posUnlimited (s := fun n => -s n)
  simp only [hyperSeq_neg, posUnlimited_neg_iff] at h
  rw [← h]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨-b, by rintro _ ⟨n, rfl⟩; exact neg_le_neg (hb ⟨n, rfl⟩)⟩
  · rintro ⟨b, hb⟩
    refine ⟨-b, ?_⟩
    rintro _ ⟨n, rfl⟩
    have := hb ⟨n, rfl⟩
    simp only at this
    linarith

/-- **Theorem 6.4.1.** A real sequence is bounded, in the sense that $`|s_n| < b` for some
real $`b` and all $`n`, if and only if all of its extended terms are limited. -/
theorem bounded_iff_forall_unlimited_limited :
    (∃ b : ℝ, ∀ n, |s n| < b) ↔ ∀ N ∈ unlimitedHyperNat, Limited (hyperSeq s N) := by
  constructor
  · rintro ⟨b, hb⟩ N -
    rw [limited_iff_abs_lt]
    refine ⟨b + 1, ?_⟩
    have h := hyperSeq_le_coe (s := fun n => |s n|) (fun n => (hb n).le) N
    rw [hyperSeq_abs] at h
    exact lt_of_le_of_lt h (Hyperreal.coe_lt_coe.2 (by linarith))
  · intro h
    obtain ⟨u, hu⟩ := bddAbove_range_iff_forall_unlimited_not_posUnlimited.2 fun N hN =>
      (limited_iff_not_posUnlimited_and_not_negUnlimited.1 (h N hN)).1
    obtain ⟨l, hl⟩ := bddBelow_range_iff_forall_unlimited_not_negUnlimited.2 fun N hN =>
      (limited_iff_not_posUnlimited_and_not_negUnlimited.1 (h N hN)).2
    refine ⟨max |l| |u| + 1, fun n => ?_⟩
    have := abs_le_max_abs_abs (hl ⟨n, rfl⟩) (hu ⟨n, rfl⟩)
    linarith

/-- **Theorem 6.4.1**, for Mathlib's notion of a bounded set: the set of terms of a real
sequence is bounded if and only if all extended terms are limited. -/
theorem isBounded_range_iff_forall_unlimited_limited :
    Bornology.IsBounded (range s) ↔ ∀ N ∈ unlimitedHyperNat, Limited (hyperSeq s N) := by
  rw [← bounded_iff_forall_unlimited_limited, isBounded_iff_forall_norm_le]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C + 1, fun n => by have := hC _ ⟨n, rfl⟩; rw [Real.norm_eq_abs] at this; linarith⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, by rintro _ ⟨n, rfl⟩; rw [Real.norm_eq_abs]; exact (hb n).le⟩

/-- **Theorem 6.4.1, consequence.** If all extended terms of a sequence are limited then the
extended sequence is limited at every hypernatural, standard or not. This is the first step
of the book's proof of the converse half. -/
theorem limited_hyperSeq_of_forall_unlimited
    (h : ∀ N ∈ unlimitedHyperNat, Limited (hyperSeq s N)) (hN : N ∈ ℕ*) :
    Limited (hyperSeq s N) :=
  by_contra fun hl => hl (h N (mem_unlimitedHyperNat_of_not_limited_hyperSeq hN hl))

/-- **Theorem 6.4.2 (1).** A real sequence diverges to infinity if and only if all of its
extended terms are positive unlimited. Divergence to infinity is Mathlib's
{lit}`Tendsto s atTop atTop`. -/
theorem tendsto_atTop_iff_forall_unlimited_posUnlimited :
    Tendsto s atTop atTop ↔ ∀ N ∈ unlimitedHyperNat, PosUnlimited (hyperSeq s N) := by
  constructor
  · intro h N hN r
    obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
    rw [hyperSeq_hnat, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
    exact (h.comp hk).eventually (eventually_gt_atTop r)
  · intro h
    rw [tendsto_atTop]
    intro r
    exact ((forall_unlimited_lt_hyperSeq_iff s r).1 fun N hN => h N hN r).mono fun n hn => hn.le

/-- **Theorem 6.4.2 (2).** A real sequence diverges to minus infinity if and only if all of
its extended terms are negative unlimited. -/
theorem tendsto_atBot_iff_forall_unlimited_negUnlimited :
    Tendsto s atTop atBot ↔ ∀ N ∈ unlimitedHyperNat, NegUnlimited (hyperSeq s N) := by
  constructor
  · intro h N hN r
    obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
    rw [hyperSeq_hnat, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
    exact (h.comp hk).eventually (eventually_lt_atBot r)
  · intro h
    rw [tendsto_atBot]
    intro r
    exact ((forall_unlimited_hyperSeq_lt_iff s r).1 fun N hN => h N hN r).mono fun n hn => hn.le

/-- **Section 6.4, book definition of divergence to infinity.** The book says that $`s`
diverges to infinity if for each real $`r` some standard tail lies above $`r`. This is
Mathlib's {lit}`Tendsto s atTop atTop`. -/
theorem tendsto_atTop_iff_forall_exists_tail :
    Tendsto s atTop atTop ↔ ∀ r : ℝ, ∃ n, ∀ m, n ≤ m → r < s m := by
  rw [tendsto_atTop]
  constructor
  · intro h r
    obtain ⟨n, hn⟩ := eventually_atTop.1 (h (r + 1))
    exact ⟨n, fun m hm => by linarith [hn m hm]⟩
  · intro h r
    obtain ⟨n, hn⟩ := h r
    exact eventually_atTop.2 ⟨n, fun m hm => (hn m hm).le⟩

end Boundedness

/-!
## 6.5 Cauchy Sequences

A sequence is Cauchy when its terms are eventually within any prescribed distance of each
other. In nonstandard terms this says that all extended terms are infinitely close to one
another. Cauchy's convergence criterion then has a short proof. An extended term of a Cauchy
sequence is limited, so it has a shadow; every other extended term is infinitely close to it
and hence to that shadow; by Theorem 6.1.1 the sequence converges to the shadow.
-/

section Cauchy

variable {s : ℕ → ℝ}

/-- **Theorem 6.5.1.** A real sequence is Cauchy if and only if $`s_M \simeq s_N` for all
unlimited hypernaturals $`M` and $`N`. The Cauchy property is Mathlib's {name}`CauchySeq`. -/
theorem cauchySeq_iff_forall_unlimited_infClose :
    CauchySeq s ↔
      ∀ M ∈ unlimitedHyperNat, ∀ N ∈ unlimitedHyperNat, hyperSeq s M ≊ hyperSeq s N := by
  rw [Metric.cauchySeq_iff]
  constructor
  · intro h M hM N hN
    obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hM
    obtain ⟨l, hl, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
    rw [hyperSeq_hnat, hyperSeq_hnat, ofSeq_infClose_ofSeq_iff]
    intro η hη
    obtain ⟨j, hj⟩ := h η hη
    filter_upwards [tendsto_atTop.1 hk j, tendsto_atTop.1 hl j] with n hkn hln
    exact hj _ hkn _ hln
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨η, hη, hne⟩ := hne
    choose k hk l hl hd using hne
    have hkt : Tendsto k (hyperfilter ℕ) atTop :=
      (tendsto_atTop_mono hk tendsto_id).mono_left Nat.hyperfilter_le_atTop
    have hlt : Tendsto l (hyperfilter ℕ) atTop :=
      (tendsto_atTop_mono hl tendsto_id).mono_left Nat.hyperfilter_le_atTop
    have := h _ (hnat_mem_unlimitedHyperNat_iff.2 hkt) _ (hnat_mem_unlimitedHyperNat_iff.2 hlt)
    rw [hyperSeq_hnat, hyperSeq_hnat, ofSeq_infClose_ofSeq_iff] at this
    obtain ⟨n, hn⟩ := (this η hη).exists
    exact absurd hn (not_lt.2 (hd n))

/-- **Theorem 6.5.2, first step.** The extended terms of a Cauchy sequence are limited. From
some standard index $`j` on, the terms are within $`1` of $`s_j`; by transfer every extended
term is within $`1` of the real number $`s_j`. This replaces the appeal to the standard fact
that Cauchy sequences are bounded. -/
theorem CauchySeq.limited_hyperSeq (h : CauchySeq s) {N : ℝ*} (hN : N ∈ unlimitedHyperNat) :
    Limited (hyperSeq s N) := by
  obtain ⟨j, hj⟩ := Metric.cauchySeq_iff.1 h 1 one_pos
  obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
  have h1 : |hyperSeq s (hnat k) - (s j : ℝ*)| < (1 : ℝ) := by
    rw [hyperSeq_hnat, coe_eq_ofSeq_const (s j), abs_ofSeq_sub_ofSeq_lt_iff]
    exact (tendsto_atTop.1 hk j).mono fun n hn => hj _ hn _ le_rfl
  have h2 : Limited (hyperSeq s (hnat k) - (s j : ℝ*)) := limited_iff_abs_lt.2 ⟨1, h1⟩
  simpa using h2.add (limited_coe (s j))

/-- **Theorem 6.5.2 (Cauchy's convergence criterion).** A real sequence converges if and only
if it is Cauchy. -/
theorem cauchySeq_iff_exists_tendsto : CauchySeq s ↔ ∃ L : ℝ, Tendsto s atTop (𝓝 L) := by
  constructor
  · intro h
    have hc := cauchySeq_iff_forall_unlimited_infClose.1 h
    have hω := omega_mem_unlimitedHyperNat
    refine ⟨sh (hyperSeq s ω), tendsto_iff_forall_unlimited_infClose.2 fun N hN => ?_⟩
    exact (hc N hN ω hω).trans (CauchySeq.limited_hyperSeq h hω).infClose_sh
  · rintro ⟨L, hL⟩
    rw [cauchySeq_iff_forall_unlimited_infClose]
    intro M hM N hN
    exact (hyperSeq_infClose_of_tendsto hL hM).trans (hyperSeq_infClose_of_tendsto hL hN).symm

end Cauchy

/-!
## 6.6 Cluster Points

A real number $`L` is a cluster point of a sequence if every interval around $`L` contains
terms with arbitrarily large index. The nonstandard characterisation is the existential
counterpart of Theorem 6.1.1: $`L` is a cluster point exactly when some extended term is
infinitely close to $`L`. Consequently the cluster points of a sequence are the shadows of
its limited extended terms, and a bounded sequence, all of whose extended terms are limited,
has a cluster point. This is the Bolzano-Weierstrass theorem.

Cluster points are Mathlib's {name}`MapClusterPt` along the filter {name}`Filter.atTop`.
-/

section ClusterPoints

variable {s : ℕ → ℝ} {L : ℝ} {N : ℝ*}

/-- **Section 6.6, definition of a cluster point.** $`L` is a cluster point of $`s` in
Mathlib's sense if and only if the book's sentence (i) holds: for every positive real
$`\varepsilon` and every $`m` there is an $`n > m` with $`|s_n - L| < \varepsilon`. -/
theorem mapClusterPt_iff_forall_exists :
    MapClusterPt L atTop s ↔ ∀ η : ℝ, 0 < η → ∀ m : ℕ, ∃ n, m < n ∧ |s n - L| < η := by
  rw [mapClusterPt_iff_frequently]
  constructor
  · intro h η hη m
    obtain ⟨n, hn, hn'⟩ := frequently_atTop.1 (h _ (Metric.ball_mem_nhds L hη)) (m + 1)
    exact ⟨n, hn, by rwa [Metric.mem_ball, Real.dist_eq] at hn'⟩
  · intro h U hU
    obtain ⟨η, hη, hηU⟩ := Metric.mem_nhds_iff.1 hU
    rw [frequently_atTop]
    intro m
    obtain ⟨n, hn, hn'⟩ := h η hη m
    exact ⟨n, hn.le, hηU (by rwa [Metric.mem_ball, Real.dist_eq])⟩

/-- **Theorem 6.6.1.** A real number $`L` is a cluster point of the real sequence $`s` if and
only if $`s_N \simeq L` for some unlimited hypernatural $`N`.

For the forward direction choose, beyond each $`j`, an index $`k_j` with
$`|s_{k_j} - L| < 1/(j+1)`; the hypernatural $`[k_j]` is unlimited and the extended term there
is infinitely close to $`L`. For the converse, the extended term lies in the enlargement of
$`(L - \varepsilon, L + \varepsilon)`, so by principle (b) the interval contains terms of
arbitrarily large standard index. -/
theorem mapClusterPt_iff_exists_unlimited_infClose :
    MapClusterPt L atTop s ↔ ∃ N ∈ unlimitedHyperNat, hyperSeq s N ≊ (L : ℝ*) := by
  rw [mapClusterPt_iff_forall_exists]
  constructor
  · intro h
    have h' : ∀ j : ℕ, ∃ n, j < n ∧ |s n - L| < 1 / ((j : ℝ) + 1) := fun j =>
      h _ (by positivity) j
    choose k hk hk' using h'
    have hkt : Tendsto k (hyperfilter ℕ) atTop :=
      (tendsto_atTop_mono (fun n => (hk n).le) tendsto_id).mono_left Nat.hyperfilter_le_atTop
    refine ⟨hnat k, hnat_mem_unlimitedHyperNat_iff.2 hkt, ?_⟩
    rw [hyperSeq_hnat, coe_eq_ofSeq_const, ofSeq_infClose_ofSeq_iff]
    intro η hη
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hη
    refine eventually_hyperfilter_of_forall_ge j fun n hn => lt_trans (hk' n) ?_
    refine lt_of_le_of_lt ?_ hj
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.succ_le_succ hn
  · rintro ⟨N, hN, h⟩ η hη m
    obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
    rw [hyperSeq_hnat, coe_eq_ofSeq_const, ofSeq_infClose_ofSeq_iff] at h
    have hf : ∃ᶠ n in atTop, |s n - L| < η :=
      frequently_atTop_iff_exists_tendsto_hyperfilter.2 ⟨k, hk, h η hη⟩
    obtain ⟨n, hn, hn'⟩ := frequently_atTop.1 hf (m + 1)
    exact ⟨n, hn, hn'⟩

/-- **Section 6.6.** The set $`C_s` of cluster points of a real sequence $`s`. -/
def clusterSet (s : ℕ → ℝ) : Set ℝ := {L | MapClusterPt L atTop s}

/-- Membership in the set of cluster points, in nonstandard terms. -/
theorem mem_clusterSet_iff :
    L ∈ clusterSet s ↔ ∃ N ∈ unlimitedHyperNat, hyperSeq s N ≊ (L : ℝ*) :=
  mapClusterPt_iff_exists_unlimited_infClose

/-- **Section 6.6.** The shadow of a limited extended term is a cluster point of the
sequence. -/
theorem sh_hyperSeq_mem_clusterSet (hN : N ∈ unlimitedHyperNat) (hl : Limited (hyperSeq s N)) :
    sh (hyperSeq s N) ∈ clusterSet s :=
  mem_clusterSet_iff.2 ⟨N, hN, hl.infClose_sh⟩

/-- **Section 6.6.** The cluster points of a real sequence are precisely the shadows of its
limited extended terms. -/
theorem clusterSet_eq_shadows (s : ℕ → ℝ) :
    clusterSet s =
      {L | ∃ N ∈ unlimitedHyperNat, Limited (hyperSeq s N) ∧ sh (hyperSeq s N) = L} := by
  ext L
  rw [mem_clusterSet_iff]
  constructor
  · rintro ⟨N, hN, h⟩
    exact ⟨N, hN, limited_of_infClose_coe h, sh_eq_of_infClose h⟩
  · rintro ⟨N, hN, hl, rfl⟩
    exact ⟨N, hN, hl.infClose_sh⟩

/-- **Section 6.8, opening.** For a bounded sequence the set of cluster points is the set of
shadows of the extended tail: $`C_s = \{\operatorname{sh}(s_N) : N \text{ unlimited}\}`. -/
theorem clusterSet_eq_image_sh (hb : ∃ b : ℝ, ∀ n, |s n| < b) :
    clusterSet s = (fun N => sh (hyperSeq s N)) '' unlimitedHyperNat := by
  have hl := bounded_iff_forall_unlimited_limited.1 hb
  rw [clusterSet_eq_shadows]
  ext L
  constructor
  · rintro ⟨N, hN, -, rfl⟩
    exact ⟨N, hN, rfl⟩
  · rintro ⟨N, hN, rfl⟩
    exact ⟨N, hN, hl N hN, rfl⟩

/-- **Theorem 6.6.2 (Bolzano-Weierstrass).** Every bounded sequence of real numbers has a
cluster point: the shadow of any extended term. -/
theorem exists_mapClusterPt_of_bounded (hb : ∃ b : ℝ, ∀ n, |s n| < b) :
    ∃ L : ℝ, MapClusterPt L atTop s :=
  ⟨_, sh_hyperSeq_mem_clusterSet omega_mem_unlimitedHyperNat
    (bounded_iff_forall_unlimited_limited.1 hb ω omega_mem_unlimitedHyperNat)⟩

/-- **Section 6.6, subsequences.** A cluster point in the sense of the book is the limit of a
subsequence, and conversely. The book states the forward implication as a known consequence
of sentence (i); this is Mathlib's theorem, recorded to tie the two notions together. -/
theorem mapClusterPt_iff_exists_subseq :
    MapClusterPt L atTop s ↔
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (s ∘ φ) atTop (𝓝 L) := by
  constructor
  · intro h
    exact subseq_tendsto_of_neBot h
  · rintro ⟨φ, hφ, h⟩
    exact (h.mapClusterPt).of_comp hφ.tendsto_atTop

end ClusterPoints

/-!
## 6.7 Exercises on Limits and Cluster Points

The four exercises are consequences of the characterisations above. Limits respect the order,
a sequence squeezed between two sequences with a common limit has that limit, a convergent
sequence has exactly one cluster point, and a bounded sequence with exactly one cluster point
converges. The last statement fails without boundedness, and a counterexample is given.
-/

section ExercisesLimits

variable {r s t : ℕ → ℝ} {L M : ℝ}

/-- **Exercise 6.7(1).** If $`s_n \to L`, $`t_n \to M` and $`s_n \le t_n` for all $`n`, then
$`L \le M`. -/
theorem limit_le_limit (hs : Tendsto s atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 M))
    (h : ∀ n, s n ≤ t n) : L ≤ M :=
  coe_le_coe_of_infClose_le_infClose
    (hyperSeq_infClose_of_tendsto hs omega_mem_unlimitedHyperNat).symm
    (hyperSeq_le_hyperSeq h ω)
    (hyperSeq_infClose_of_tendsto ht omega_mem_unlimitedHyperNat)

/-- **Exercise 6.7(2).** If $`r_n \le s_n \le t_n` for all $`n` and the sequences $`r` and
$`t` converge to the same limit $`L`, then $`s` converges to $`L`. -/
theorem limit_squeeze (hr : Tendsto r atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 L))
    (h₁ : ∀ n, r n ≤ s n) (h₂ : ∀ n, s n ≤ t n) : Tendsto s atTop (𝓝 L) :=
  tendsto_iff_forall_unlimited_infClose.2 fun N hN =>
    infClose_of_le_of_le (hyperSeq_le_hyperSeq h₁ N) (hyperSeq_le_hyperSeq h₂ N)
      (hyperSeq_infClose_of_tendsto hr hN) (hyperSeq_infClose_of_tendsto ht hN)

/-- **Exercise 6.7(3).** A convergent real sequence has exactly one cluster point, namely its
limit. -/
theorem existsUnique_mapClusterPt_of_tendsto (hs : Tendsto s atTop (𝓝 L)) :
    ∃! c : ℝ, MapClusterPt c atTop s := by
  refine ⟨L, ?_, ?_⟩
  · exact mapClusterPt_iff_exists_unlimited_infClose.2
      ⟨ω, omega_mem_unlimitedHyperNat, hyperSeq_infClose_of_tendsto hs omega_mem_unlimitedHyperNat⟩
  · intro c hc
    obtain ⟨N, hN, h⟩ := mapClusterPt_iff_exists_unlimited_infClose.1 hc
    exact infClose_coe_iff.1 (h.symm.trans (hyperSeq_infClose_of_tendsto hs hN))

/-- **Exercise 6.7(4), bounded case.** A bounded real sequence with exactly one cluster point
$`L` converges to $`L`: every extended term is limited, its shadow is a cluster point, so the
shadow is $`L`. -/
theorem tendsto_of_bounded_of_unique_mapClusterPt (hb : ∃ b : ℝ, ∀ n, |s n| < b)
    (hL : ∀ c : ℝ, MapClusterPt c atTop s → c = L) : Tendsto s atTop (𝓝 L) := by
  rw [tendsto_iff_forall_unlimited_infClose]
  intro N hN
  have hl := bounded_iff_forall_unlimited_limited.1 hb N hN
  have := hL _ (sh_hyperSeq_mem_clusterSet hN hl)
  rw [← this]
  exact hl.infClose_sh

/-- **Exercise 6.7(4), unbounded case.** Without boundedness the conclusion fails. The
sequence that is $`n` at even $`n` and $`0` at odd $`n` has $`0` as its only cluster point
but does not converge. An extended term at an even unlimited $`N` is $`N` itself, which is
unlimited, and an extended term at an odd unlimited $`N` is $`0`. -/
theorem exists_unique_mapClusterPt_not_tendsto :
    ∃ s : ℕ → ℝ, (∃! c : ℝ, MapClusterPt c atTop s) ∧ ¬ ∃ L : ℝ, Tendsto s atTop (𝓝 L) := by
  let s : ℕ → ℝ := fun n => if Even n then (n : ℝ) else 0
  have hval : ∀ k : ℕ → ℕ, Tendsto k (hyperfilter ℕ) atTop →
      Unlimited (hyperSeq s (hnat k)) ∨ hyperSeq s (hnat k) = 0 := by
    intro k hk
    rcases almostAll_or.1 (Eventually.of_forall fun n => em (Even (k n))) with he | ho
    · left
      have : hyperSeq s (hnat k) = hnat k := by
        rw [hyperSeq_hnat, hnat, ofSeq_eq_ofSeq_iff]
        exact he.mono fun n hn => ite_eq_left hn
      rw [this]
      exact (mem_unlimitedHyperNat.1 (hnat_mem_unlimitedHyperNat_iff.2 hk)).2
    · right
      rw [hyperSeq_hnat]
      change _ = Hyperreal.ofSeq fun _ => 0
      rw [ofSeq_eq_ofSeq_iff]
      exact ho.mono fun n hn => ite_eq_right hn
  refine ⟨s, ⟨0, ?_, ?_⟩, ?_⟩
  · change MapClusterPt 0 atTop s
    rw [mapClusterPt_iff_exists_unlimited_infClose]
    have hk : Tendsto (fun n : ℕ => 2 * n + 1) (hyperfilter ℕ) atTop :=
      (tendsto_atTop_mono (fun n => show id n ≤ 2 * n + 1 by simp only [id]; omega)
        tendsto_id).mono_left Nat.hyperfilter_le_atTop
    refine ⟨_, hnat_mem_unlimitedHyperNat_iff.2 hk, ?_⟩
    have : hyperSeq s (hnat fun n : ℕ => 2 * n + 1) = 0 := by
      rw [hyperSeq_hnat]
      change _ = Hyperreal.ofSeq fun _ => 0
      rw [ofSeq_eq_ofSeq_iff]
      exact Eventually.of_forall fun n => ite_eq_right (by simp)
    rw [this, Hyperreal.coe_zero]
  · intro c hc
    obtain ⟨N, hN, h⟩ := mapClusterPt_iff_exists_unlimited_infClose.1 hc
    obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
    rcases hval k hk with hu | h0
    · exact absurd (limited_of_infClose_coe h) hu.not_limited
    · rw [h0, ← Hyperreal.coe_zero] at h
      exact (infClose_coe_iff.1 h).symm
  · rintro ⟨L, hL⟩
    have hk : Tendsto (fun n : ℕ => 2 * n) (hyperfilter ℕ) atTop :=
      (tendsto_atTop_mono (fun n => show id n ≤ 2 * n by simp only [id]; omega)
        tendsto_id).mono_left Nat.hyperfilter_le_atTop
    have hN := hnat_mem_unlimitedHyperNat_iff.2 hk
    have h := hyperSeq_infClose_of_tendsto hL hN
    have : hyperSeq s (hnat fun n : ℕ => 2 * n) = hnat fun n : ℕ => 2 * n := by
      rw [hyperSeq_hnat, hnat, ofSeq_eq_ofSeq_iff]
      exact Eventually.of_forall fun n => ite_eq_left (by simp)
    rw [this] at h
    exact (mem_unlimitedHyperNat.1 hN).2.not_limited (limited_of_infClose_coe h)

end ExercisesLimits

end Goldblatt
