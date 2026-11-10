import Goldblatt.Ch09_RiemannIntegral.Integral

/-!
# 9 (part 3). Properties of the Integral and the Fundamental Theorem: Sections 9.3 to 9.5

This is the third of three parts of Chapter 9 (the overview is on the chapter page
{lit}`Goldblatt.Ch09_RiemannIntegral`). It derives the standard properties of the integral
from the formula $`\int_a^b f = \operatorname{sh}\bigl(S_a^b(f, \Delta x)\bigr)`, proves that
the area function of a continuous function is differentiable with derivative the integrand
(Theorem 9.4.1), deduces the fundamental theorem of calculus (Theorem 9.4.2), identifies the
integral of a continuous function with Mathlib's interval integral, and solves the exercise
of Section 9.5 on average values.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## 9.3 Standard Properties of the Integral

Each property of the integral listed in the book is proved in the same way. The corresponding
property of ordinary Riemann sums holds for every real width $`\Delta x > 0`, because it is a
statement about finite sums. By transfer it holds for a positive infinitesimal width. Taking
shadows, and using that the shadow of the Riemann sum is the integral, gives the property of
the integral. For the first three properties one must also know that the new function is
integrable, which is obtained from the criterion of Section 9.2: the difference between its
upper and lower sums is bounded in terms of those of the given functions.

The book proves the third property (juxtaposition of intervals) and leaves the others as
Exercise 9.3.1.
-/

section Algebra

variable {f g : ℝ → ℝ} {A : Set ℝ} {a b c I J t : ℝ} {Δ : ℝ*}

/-- A real multiple of a bounded function is bounded. -/
theorem BoundedOn.const_mul (h : BoundedOn f A) (c : ℝ) : BoundedOn (fun x => c * f x) A :=
  let ⟨B, hB⟩ := h
  ⟨|c| * B, fun x hx => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB x hx) (abs_nonneg c)⟩

/-- The sum of two bounded functions is bounded. -/
theorem BoundedOn.add (hf : BoundedOn f A) (hg : BoundedOn g A) :
    BoundedOn (fun x => f x + g x) A :=
  let ⟨B, hB⟩ := hf
  let ⟨C, hC⟩ := hg
  ⟨B + C, fun x hx => (abs_add_le _ _).trans (add_le_add (hB x hx) (hC x hx))⟩

/-- **Exercise 9.3.1, real form (multiples).** $`S_a^b(cf, \Delta x) = c\,S_a^b(f, \Delta x)`. -/
theorem ordSum_const_mul (f : ℝ → ℝ) (a b t c : ℝ) :
    ordSum (fun x => c * f x) a b t = c * ordSum f a b t := by
  simp only [ordSum, meshSumOf, Finset.mul_sum, mul_assoc]

/-- **Exercise 9.3.1, real form (sums).**
$`S_a^b(f + g, \Delta x) = S_a^b(f, \Delta x) + S_a^b(g, \Delta x)`. -/
theorem ordSum_add (f g : ℝ → ℝ) (a b t : ℝ) :
    ordSum (fun x => f x + g x) a b t = ordSum f a b t + ordSum g a b t := by
  simp only [ordSum, meshSumOf, add_mul, Finset.sum_add_distrib]

/-- **Exercise 9.3.1, real form (monotonicity).** If $`f \le g` on $`[a, b]` then
$`S_a^b(f, \Delta x) \le S_a^b(g, \Delta x)` for real $`\Delta x > 0`. -/
theorem ordSum_le_ordSum (hab : a ≤ b) (ht : 0 < t) (h : ∀ x ∈ Icc a b, f x ≤ g x) :
    ordSum f a b t ≤ ordSum g a b t := by
  change (meshPartition hab ht).ordSum f ≤ (meshPartition hab ht).ordSum g
  exact (meshPartition hab ht).sum_le_sum fun j hj => mul_le_mul_of_nonneg_right
    (h _ ((meshPartition hab ht).Icc_subset hj
      (left_mem_Icc.2 ((meshPartition hab ht).lt_succ j hj).le)))
    (sub_nonneg.2 ((meshPartition hab ht).lt_succ j hj).le)

/-- **Exercise 9.3.1, real form (constants).** The Riemann sums of a constant function $`m`
are all equal to $`m(b - a)`. -/
theorem ordSum_const (hab : a ≤ b) (ht : 0 < t) (m : ℝ) :
    ordSum (fun _ => m) a b t = m * (b - a) :=
  (meshPartition hab ht).sum_const_mul m

/-- **Exercise 9.3.1, by transfer (multiples).**
$`S_a^b(cf, \Delta x) = c\,S_a^b(f, \Delta x)` for every hyperreal $`\Delta x`. -/
theorem hyperOrdSum_const_mul (f : ℝ → ℝ) (a b c : ℝ) (Δ : ℝ*) :
    hyperOrdSum (fun x => c * f x) a b Δ = c * hyperOrdSum f a b Δ := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep Δ
  change Hyperreal.ofSeq (fun n => ordSum (fun x => c * f x) a b (r n)) =
    Hyperreal.ofSeq (fun n => c * ordSum f a b (r n))
  simp only [ordSum_const_mul]

/-- **Exercise 9.3.1, by transfer (sums).**
$`S_a^b(f + g, \Delta x) = S_a^b(f, \Delta x) + S_a^b(g, \Delta x)` for every hyperreal
$`\Delta x`. -/
theorem hyperOrdSum_add (f g : ℝ → ℝ) (a b : ℝ) (Δ : ℝ*) :
    hyperOrdSum (fun x => f x + g x) a b Δ = hyperOrdSum f a b Δ + hyperOrdSum g a b Δ := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep Δ
  change Hyperreal.ofSeq (fun n => ordSum (fun x => f x + g x) a b (r n)) =
    Hyperreal.ofSeq (fun n => ordSum f a b (r n) + ordSum g a b (r n))
  simp only [ordSum_add]

/-- **Exercise 9.3.1, by transfer (monotonicity).** If $`f \le g` on $`[a, b]` then
$`S_a^b(f, \Delta x) \le S_a^b(g, \Delta x)` for every positive hyperreal $`\Delta x`. -/
theorem hyperOrdSum_le_hyperOrdSum (hab : a ≤ b) (hΔ : 0 < Δ) (h : ∀ x ∈ Icc a b, f x ≤ g x) :
    hyperOrdSum f a b Δ ≤ hyperOrdSum g a b Δ :=
  starMap_le_starMap_of_pos (fun _ ht => ordSum_le_ordSum hab ht h) hΔ

/-- **Exercise 9.3.1, tool.** For real $`\Delta x > 0`, the difference between the upper and
lower sums of $`cf` is at most $`|c|` times that of $`f`: on each subinterval the oscillation
of $`cf` is at most $`|c|` times the oscillation of $`f`. -/
theorem upperSum_sub_lowerSum_const_mul_le (hf : BoundedOn f (Icc a b)) (hab : a ≤ b)
    (ht : 0 < t) (c : ℝ) :
    upperSum (fun x => c * f x) a b t - lowerSum (fun x => c * f x) a b t ≤
      |c| * (upperSum f a b t - lowerSum f a b t) := by
  obtain ⟨P, hP⟩ : ∃ P : IntervalPartition a b, P = meshPartition hab ht := ⟨_, rfl⟩
  have e1 : upperSum (fun x => c * f x) a b t - lowerSum (fun x => c * f x) a b t =
      P.upperSum (fun x => c * f x) - P.lowerSum (fun x => c * f x) := by rw [hP]; rfl
  have e2 : upperSum f a b t - lowerSum f a b t = P.upperSum f - P.lowerSum f := by
    rw [hP]; rfl
  rw [e1, e2, P.upperSum_sub_lowerSum, P.upperSum_sub_lowerSum, IntervalPartition.sum,
    IntervalPartition.sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have hlt := (P.lt_succ j hj').le
  have hfj := hf.mono (P.Icc_subset hj')
  have hosc : supOn (fun x => c * f x) (P.pt j) (P.pt (j + 1)) -
      infOn (fun x => c * f x) (P.pt j) (P.pt (j + 1)) ≤
      |c| * (supOn f (P.pt j) (P.pt (j + 1)) - infOn f (P.pt j) (P.pt (j + 1))) :=
    supOn_sub_infOn_le hlt fun s hs u hu => by
      have h1 := le_supOn hfj hu
      have h2 := infOn_le hfj hu
      have h3 := le_supOn hfj hs
      have h4 := infOn_le hfj hs
      calc c * f u - c * f s = c * (f u - f s) := by ring
        _ ≤ |c * (f u - f s)| := le_abs_self _
        _ = |c| * |f u - f s| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg c)
  calc _ ≤ (|c| * (supOn f (P.pt j) (P.pt (j + 1)) - infOn f (P.pt j) (P.pt (j + 1)))) *
        (P.pt (j + 1) - P.pt j) := mul_le_mul_of_nonneg_right hosc (sub_nonneg.2 hlt)
    _ = _ := by ring

/-- **Exercise 9.3.1, tool.** For real $`\Delta x > 0`, the difference between the upper and
lower sums of $`f + g` is at most the sum of those of $`f` and of $`g`. -/
theorem upperSum_sub_lowerSum_add_le (hf : BoundedOn f (Icc a b)) (hg : BoundedOn g (Icc a b))
    (hab : a ≤ b) (ht : 0 < t) :
    upperSum (fun x => f x + g x) a b t - lowerSum (fun x => f x + g x) a b t ≤
      (upperSum f a b t - lowerSum f a b t) + (upperSum g a b t - lowerSum g a b t) := by
  obtain ⟨P, hP⟩ : ∃ P : IntervalPartition a b, P = meshPartition hab ht := ⟨_, rfl⟩
  have e1 : upperSum (fun x => f x + g x) a b t - lowerSum (fun x => f x + g x) a b t =
      P.upperSum (fun x => f x + g x) - P.lowerSum (fun x => f x + g x) := by rw [hP]; rfl
  have e2 : upperSum f a b t - lowerSum f a b t = P.upperSum f - P.lowerSum f := by
    rw [hP]; rfl
  have e3 : upperSum g a b t - lowerSum g a b t = P.upperSum g - P.lowerSum g := by
    rw [hP]; rfl
  rw [e1, e2, e3, P.upperSum_sub_lowerSum, P.upperSum_sub_lowerSum, P.upperSum_sub_lowerSum,
    IntervalPartition.sum, IntervalPartition.sum, IntervalPartition.sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have hlt := (P.lt_succ j hj').le
  have hfj := hf.mono (P.Icc_subset hj')
  have hgj := hg.mono (P.Icc_subset hj')
  have hosc : supOn (fun x => f x + g x) (P.pt j) (P.pt (j + 1)) -
      infOn (fun x => f x + g x) (P.pt j) (P.pt (j + 1)) ≤
      (supOn f (P.pt j) (P.pt (j + 1)) - infOn f (P.pt j) (P.pt (j + 1))) +
      (supOn g (P.pt j) (P.pt (j + 1)) - infOn g (P.pt j) (P.pt (j + 1))) :=
    supOn_sub_infOn_le hlt fun s hs u hu => by
      have h1 := le_supOn hfj hu
      have h4 := infOn_le hfj hs
      have h5 := le_supOn hgj hu
      have h8 := infOn_le hgj hs
      change f u + g u - (f s + g s) ≤ _
      linarith
  calc _ ≤ ((supOn f (P.pt j) (P.pt (j + 1)) - infOn f (P.pt j) (P.pt (j + 1))) +
        (supOn g (P.pt j) (P.pt (j + 1)) - infOn g (P.pt j) (P.pt (j + 1)))) *
        (P.pt (j + 1) - P.pt j) := mul_le_mul_of_nonneg_right hosc (sub_nonneg.2 hlt)
    _ = _ := by ring

/-- **Exercise 9.3.1, first property.** If $`f` is integrable on $`[a, b]` with integral
$`I`, then $`cf` is integrable with integral $`cI`. -/
theorem HasRiemannIntegral.const_mul (h : HasRiemannIntegral f a b I) (c : ℝ) :
    HasRiemannIntegral (fun x => c * f x) a b (c * I) := by
  have hab := h.le
  have hε : PosInfinitesimal (ε : ℝ*) := epsilon_pos_infinitesimal
  have hfc := h.1.const_mul c
  have hle : hyperUpperSum (fun x => c * f x) a b ε - hyperLowerSum (fun x => c * f x) a b ε ≤
      ((|c| : ℝ) : ℝ*) * (hyperUpperSum f a b ε - hyperLowerSum f a b ε) := by
    obtain ⟨r, hr⟩ := hyperreal_exists_rep (ε : ℝ*)
    have hr0 : 0 < Hyperreal.ofSeq r := hr ▸ hε.1
    rw [hr]
    change Hyperreal.ofSeq (fun n => upperSum (fun x => c * f x) a b (r n) -
      lowerSum (fun x => c * f x) a b (r n)) ≤
      Hyperreal.ofSeq (fun n => |c| * (upperSum f a b (r n) - lowerSum f a b (r n)))
    exact ofSeq_le_ofSeq_iff.2 ((zero_lt_ofSeq_iff.1 hr0).mono fun n hn =>
      upperSum_sub_lowerSum_const_mul_le h.1 hab hn c)
  have hLU : hyperLowerSum (fun x => c * f x) a b ε ≊ hyperUpperSum (fun x => c * f x) a b ε :=
    infClose_of_le_of_sub_le (hyperLowerSum_le_hyperUpperSum hfc hab hε.1 hε.1) hle
      ((limited_coe |c|).mul_infinitesimal (h.hyperLowerSum_infClose_hyperUpperSum hε).symm)
  have key := hasRiemannIntegral_sh_of_infClose hfc hab hε hLU
  have hsh : sh (hyperOrdSum (fun x => c * f x) a b ε) = c * I := by
    refine sh_eq_of_infClose ?_
    rw [hyperOrdSum_const_mul, Hyperreal.coe_mul]
    exact (h.hyperOrdSum_infClose hε).mul_left (limited_coe c)
  rwa [hsh] at key

/-- **Exercise 9.3.1, second property.** If $`f` and $`g` are integrable on $`[a, b]` with
integrals $`I` and $`J`, then $`f + g` is integrable with integral $`I + J`. -/
theorem HasRiemannIntegral.add (hf : HasRiemannIntegral f a b I) (hg : HasRiemannIntegral g a b J) :
    HasRiemannIntegral (fun x => f x + g x) a b (I + J) := by
  have hab := hf.le
  have hε : PosInfinitesimal (ε : ℝ*) := epsilon_pos_infinitesimal
  have hfg := hf.1.add hg.1
  have hle : hyperUpperSum (fun x => f x + g x) a b ε - hyperLowerSum (fun x => f x + g x) a b ε ≤
      (hyperUpperSum f a b ε - hyperLowerSum f a b ε) +
      (hyperUpperSum g a b ε - hyperLowerSum g a b ε) := by
    obtain ⟨r, hr⟩ := hyperreal_exists_rep (ε : ℝ*)
    have hr0 : 0 < Hyperreal.ofSeq r := hr ▸ hε.1
    rw [hr]
    change Hyperreal.ofSeq (fun n => upperSum (fun x => f x + g x) a b (r n) -
      lowerSum (fun x => f x + g x) a b (r n)) ≤
      Hyperreal.ofSeq (fun n => (upperSum f a b (r n) - lowerSum f a b (r n)) +
        (upperSum g a b (r n) - lowerSum g a b (r n)))
    exact ofSeq_le_ofSeq_iff.2 ((zero_lt_ofSeq_iff.1 hr0).mono fun n hn =>
      upperSum_sub_lowerSum_add_le hf.1 hg.1 hab hn)
  have hLU : hyperLowerSum (fun x => f x + g x) a b ε ≊ hyperUpperSum (fun x => f x + g x) a b ε :=
    infClose_of_le_of_sub_le (hyperLowerSum_le_hyperUpperSum hfg hab hε.1 hε.1) hle
      (Infinitesimal.add (hf.hyperLowerSum_infClose_hyperUpperSum hε).symm
        (hg.hyperLowerSum_infClose_hyperUpperSum hε).symm)
  have key := hasRiemannIntegral_sh_of_infClose hfg hab hε hLU
  have hsh : sh (hyperOrdSum (fun x => f x + g x) a b ε) = I + J := by
    refine sh_eq_of_infClose ?_
    rw [hyperOrdSum_add, Hyperreal.coe_add]
    exact (hf.hyperOrdSum_infClose hε).add (hg.hyperOrdSum_infClose hε)
  rwa [hsh] at key

/-- **Section 9.3, first property.** If $`f` is integrable on $`[a, b]` then so is $`cf`. -/
theorem RiemannIntegrableOn.const_mul (h : RiemannIntegrableOn f a b) (c : ℝ) :
    RiemannIntegrableOn (fun x => c * f x) a b :=
  ⟨_, h.hasRiemannIntegral.const_mul c⟩

/-- **Section 9.3, first property.** For $`f` integrable on $`[a, b]`,
$$`\int_a^b c f(x)\,dx = c \int_a^b f(x)\,dx.` -/
theorem RiemannIntegrableOn.riemannIntegral_const_mul (h : RiemannIntegrableOn f a b) (c : ℝ) :
    riemannIntegral (fun x => c * f x) a b = c * riemannIntegral f a b :=
  (h.hasRiemannIntegral.const_mul c).riemannIntegral_eq

/-- **Section 9.3, second property.** If $`f` and $`g` are integrable on $`[a, b]` then so
is $`f + g`. -/
theorem RiemannIntegrableOn.add (hf : RiemannIntegrableOn f a b) (hg : RiemannIntegrableOn g a b) :
    RiemannIntegrableOn (fun x => f x + g x) a b :=
  ⟨_, hf.hasRiemannIntegral.add hg.hasRiemannIntegral⟩

/-- **Section 9.3, second property.** For $`f` and $`g` integrable on $`[a, b]`,
$$`\int_a^b \bigl(f(x) + g(x)\bigr)\,dx = \int_a^b f(x)\,dx + \int_a^b g(x)\,dx.` -/
theorem RiemannIntegrableOn.riemannIntegral_add (hf : RiemannIntegrableOn f a b)
    (hg : RiemannIntegrableOn g a b) :
    riemannIntegral (fun x => f x + g x) a b = riemannIntegral f a b + riemannIntegral g a b :=
  (hf.hasRiemannIntegral.add hg.hasRiemannIntegral).riemannIntegral_eq

/-- **Section 9.3, fourth property.** If $`f` and $`g` are integrable on $`[a, b]` and
$`f(x) \le g(x)` on $`[a, b]`, then
$$`\int_a^b f(x)\,dx \le \int_a^b g(x)\,dx.` -/
theorem riemannIntegral_mono (hf : RiemannIntegrableOn f a b) (hg : RiemannIntegrableOn g a b)
    (h : ∀ x ∈ Icc a b, f x ≤ g x) : riemannIntegral f a b ≤ riemannIntegral g a b := by
  have hε : PosInfinitesimal (ε : ℝ*) := epsilon_pos_infinitesimal
  rw [hf.riemannIntegral_eq_sh hε, hg.riemannIntegral_eq_sh hε]
  exact sh_le_sh (limited_hyperOrdSum hf.boundedOn hf.le hε.1)
    (limited_hyperOrdSum hg.boundedOn hf.le hε.1) (hyperOrdSum_le_hyperOrdSum hf.le hε.1 h)

/-- **Section 9.3, fifth property (lower bound).** If $`f` is integrable on $`[a, b]` and
$`m \le f(x)` on $`[a, b]`, then $`m(b - a) \le \int_a^b f(x)\,dx`. -/
theorem le_riemannIntegral {m : ℝ} (hf : RiemannIntegrableOn f a b)
    (h : ∀ x ∈ Icc a b, m ≤ f x) : m * (b - a) ≤ riemannIntegral f a b := by
  have hε : PosInfinitesimal (ε : ℝ*) := epsilon_pos_infinitesimal
  have h1 : ((m * (b - a) : ℝ) : ℝ*) ≤ hyperOrdSum f a b ε := by
    have := starMap_le_starMap_of_pos (F := fun _ => m * (b - a)) (G := ordSum f a b)
      (fun t ht => (ordSum_const hf.le ht m).ge.trans (ordSum_le_ordSum hf.le ht h)) hε.1
    rwa [starMap_const_apply] at this
  exact coe_le_coe_of_le_infClose h1 (hf.hyperOrdSum_infClose hε)

/-- **Section 9.3, fifth property (upper bound).** If $`f` is integrable on $`[a, b]` and
$`f(x) \le M` on $`[a, b]`, then $`\int_a^b f(x)\,dx \le M(b - a)`. -/
theorem riemannIntegral_le {M : ℝ} (hf : RiemannIntegrableOn f a b)
    (h : ∀ x ∈ Icc a b, f x ≤ M) : riemannIntegral f a b ≤ M * (b - a) := by
  have hε : PosInfinitesimal (ε : ℝ*) := epsilon_pos_infinitesimal
  have h1 : hyperOrdSum f a b ε ≤ ((M * (b - a) : ℝ) : ℝ*) := by
    have := starMap_le_starMap_of_pos (F := ordSum f a b) (G := fun _ => M * (b - a))
      (fun t ht => (ordSum_le_ordSum hf.le ht h).trans (ordSum_const hf.le ht M).le) hε.1
    rwa [starMap_const_apply] at this
  exact coe_le_coe_of_infClose_le (hf.hyperOrdSum_infClose hε).symm h1

/-- **Section 9.3, fifth property.** If $`m \le f(x) \le M` on $`[a, b]` then
$$`m(b - a) \le \int_a^b f(x)\,dx \le M(b - a).` -/
theorem riemannIntegral_mem_Icc {m M : ℝ} (hf : RiemannIntegrableOn f a b)
    (h : ∀ x ∈ Icc a b, m ≤ f x ∧ f x ≤ M) :
    riemannIntegral f a b ∈ Icc (m * (b - a)) (M * (b - a)) :=
  ⟨le_riemannIntegral hf fun x hx => (h x hx).1, riemannIntegral_le hf fun x hx => (h x hx).2⟩

/-- **Section 9.3, example.** The integral of a constant function:
$`\int_a^b m\,dx = m(b - a)`. -/
theorem riemannIntegral_const (hab : a ≤ b) (m : ℝ) :
    riemannIntegral (fun _ => m) a b = m * (b - a) := by
  have h := riemannIntegrableOn_of_continuousOn hab (f := fun _ => m) continuousOn_const
  exact le_antisymm (riemannIntegral_le h fun _ _ => le_rfl) (le_riemannIntegral h fun _ _ => le_rfl)

end Algebra

/-!
### Juxtaposition of intervals

For the third property the book takes $`\Delta x = (c - a)/n`, so that $`c` is a point of the
partition of $`[a, b]` of width $`\Delta x`. Then the partition of $`[a, b]` is the partition
of $`[a, c]` followed by the partition of $`[c, b]`, and every sum over the subintervals
splits accordingly. This is true for each standard $`n`, hence for an unlimited $`N`, where
$`\Delta x` is infinitesimal. Applied to the differences between upper and lower sums it
shows that $`f` is integrable on the two smaller intervals; applied to ordinary Riemann sums
and followed by the shadow map it gives the equation between the integrals.
-/

section Juxtaposition

variable {f : ℝ → ℝ} {a b c d I : ℝ}

/-- The partition of $`[a, b]` of width $`(b - a)/n` has exactly $`n` subintervals. -/
theorem meshCard_div_natCast (n : ℕ) (hab : a < b) :
    meshCard a b ((b - a) / n) = n := by
  have h : (b - a) / ((b - a) / n) = n := by
    rw [div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self (sub_pos.2 hab).ne', mul_one]
  rw [meshCard, h, Nat.ceil_natCast]

/-- The points of the partition of $`[a, b]` of width $`(b - a)/n` are
$`a + k(b - a)/n` for $`k \le n`. -/
theorem meshPoint_div_of_le {n k : ℕ} (hn : n ≠ 0) (hab : a ≤ b) (hk : k ≤ n) :
    meshPoint a b ((b - a) / n) k = a + k * ((b - a) / n) := by
  refine min_eq_left ?_
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : (n : ℝ) * ((b - a) / n) = b - a := by field_simp
  have h2 : (k : ℝ) * ((b - a) / n) ≤ n * ((b - a) / n) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk)
      (div_nonneg (sub_nonneg.2 hab) (Nat.cast_nonneg n))
  linarith

/-- **Section 9.3, equation (iv), real form.** Let $`a < c \le b` and
$`\Delta x = (c - a)/n` with $`n` a positive integer. Then every sum over the partition of
$`[a, b]` of width $`\Delta x` is the sum over the partition of $`[a, c]` plus the sum over
the partition of $`[c, b]`. -/
theorem meshSumOf_split (G : ℝ → ℝ → ℝ) {n : ℕ} (hn : n ≠ 0) (hac : a < c) (hcb : c ≤ b) :
    meshSumOf G a b ((c - a) / n) =
      meshSumOf G a c ((c - a) / n) + meshSumOf G c b ((c - a) / n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have h1 : meshCard a c ((c - a) / n) = n := meshCard_div_natCast n hac
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (c - a) / n := ⟨_, rfl⟩
  rw [← ht] at h1 ⊢
  have ht0 : 0 < t := by rw [ht]; exact div_pos (sub_pos.2 hac) hn'
  have hnt : (n : ℝ) * t = c - a := by rw [ht]; field_simp
  have h2 : meshCard a b t = n + meshCard c b t := by
    have h3 : (b - a) / t = (b - c) / t + n := by
      field_simp
      linarith
    rw [meshCard, h3, Nat.ceil_add_natCast (div_nonneg (sub_nonneg.2 hcb) ht0.le)]
    exact Nat.add_comm _ _
  have hp1 : ∀ k ≤ n, meshPoint a b t k = meshPoint a c t k := by
    intro k hk
    have : (k : ℝ) * t ≤ n * t := mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) ht0.le
    rw [meshPoint, meshPoint, min_eq_left (by linarith), min_eq_left (by linarith)]
  have hp2 : ∀ k, meshPoint a b t (n + k) = meshPoint c b t k := by
    intro k
    rw [meshPoint, meshPoint]
    congr 1
    push_cast
    linarith
  rw [meshSumOf, h2, Finset.sum_range_add, meshSumOf, meshSumOf, h1]
  congr 1
  · exact Finset.sum_congr rfl fun k hk => by
      have := Finset.mem_range.1 hk
      rw [hp1 k (by omega), hp1 (k + 1) (by omega)]
  · exact Finset.sum_congr rfl fun k _ => by rw [hp2 k, Nat.add_assoc n k 1, hp2 (k + 1)]

/-- **Section 9.3, equation (iv), by transfer.** Let $`a < c \le b` and
$`\Delta x = (c - a)/N` with $`N` an unlimited hypernatural. Then the extended sums over the
partitions of width $`\Delta x` satisfy the same splitting as for standard $`n`. -/
theorem starMap_meshSumOf_split (G : ℝ → ℝ → ℝ) (hac : a < c) (hcb : c ≤ b) {N : ℝ*}
    (hN : N ∈ unlimitedHyperNat) :
    ⋆(meshSumOf G a b) (((c - a : ℝ) : ℝ*) / N) =
      ⋆(meshSumOf G a c) (((c - a : ℝ) : ℝ*) / N) +
        ⋆(meshSumOf G c b) (((c - a : ℝ) : ℝ*) / N) := by
  obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
  change Hyperreal.ofSeq (fun n => meshSumOf G a b ((c - a) / k n)) =
    Hyperreal.ofSeq (fun n => meshSumOf G a c ((c - a) / k n) + meshSumOf G c b ((c - a) / k n))
  rw [ofSeq_eq_ofSeq_iff]
  filter_upwards [(tendsto_atTop.1 hk) 1] with n hn
  exact meshSumOf_split G (by omega) hac hcb

/-- **Section 9.3, equation (iv).** For $`a < c \le b` and $`\Delta x = (c - a)/N` with $`N`
an unlimited hypernatural,
$$`S_a^b(f, \Delta x) = S_a^c(f, \Delta x) + S_c^b(f, \Delta x).` -/
theorem hyperOrdSum_add_adjacent (f : ℝ → ℝ) (hac : a < c) (hcb : c ≤ b) {N : ℝ*}
    (hN : N ∈ unlimitedHyperNat) :
    hyperOrdSum f a b (((c - a : ℝ) : ℝ*) / N) =
      hyperOrdSum f a c (((c - a : ℝ) : ℝ*) / N) + hyperOrdSum f c b (((c - a : ℝ) : ℝ*) / N) :=
  starMap_meshSumOf_split _ hac hcb hN

/-- **Section 9.3, third property (juxtaposition).** If $`f` is integrable on $`[a, b]` with
integral $`I` and $`a \le c \le b`, then $`f` is integrable on $`[a, c]` and on $`[c, b]`,
and $`I` is the sum of the two integrals. -/
theorem HasRiemannIntegral.exists_split (h : HasRiemannIntegral f a b I) (hac : a ≤ c)
    (hcb : c ≤ b) :
    ∃ I₁ I₂ : ℝ, HasRiemannIntegral f a c I₁ ∧ HasRiemannIntegral f c b I₂ ∧ I = I₁ + I₂ := by
  rcases hac.eq_or_lt with rfl | hac
  · exact ⟨0, I, hasRiemannIntegral_self f a, h, (zero_add I).symm⟩
  have hω := omega_mem_unlimitedHyperNat
  have hΔ := posInfinitesimal_width hac hω
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ*, Δ = ((c - a : ℝ) : ℝ*) / ω := ⟨_, rfl⟩
  rw [← hΔdef] at hΔ
  have hf1 : BoundedOn f (Icc a c) := h.1.mono (Icc_subset_Icc le_rfl hcb)
  have hf2 : BoundedOn f (Icc c b) := h.1.mono (Icc_subset_Icc hac.le le_rfl)
  have eU : hyperUpperSum f a b Δ = hyperUpperSum f a c Δ + hyperUpperSum f c b Δ := by
    rw [hΔdef]; exact starMap_meshSumOf_split _ hac hcb hω
  have eL : hyperLowerSum f a b Δ = hyperLowerSum f a c Δ + hyperLowerSum f c b Δ := by
    rw [hΔdef]; exact starMap_meshSumOf_split _ hac hcb hω
  have eS : hyperOrdSum f a b Δ = hyperOrdSum f a c Δ + hyperOrdSum f c b Δ := by
    rw [hΔdef]; exact starMap_meshSumOf_split _ hac hcb hω
  have hi : Infinitesimal (hyperUpperSum f a b Δ - hyperLowerSum f a b Δ) :=
    (h.hyperLowerSum_infClose_hyperUpperSum hΔ).symm
  have l1 := hyperLowerSum_le_hyperUpperSum hf1 hac.le hΔ.1 hΔ.1
  have l2 := hyperLowerSum_le_hyperUpperSum hf2 hcb hΔ.1 hΔ.1
  have c1 : hyperLowerSum f a c Δ ≊ hyperUpperSum f a c Δ :=
    infClose_of_le_of_sub_le l1 (by rw [eU, eL]; linarith) hi
  have c2 : hyperLowerSum f c b Δ ≊ hyperUpperSum f c b Δ :=
    infClose_of_le_of_sub_le l2 (by rw [eU, eL]; linarith) hi
  refine ⟨_, _, hasRiemannIntegral_sh_of_infClose hf1 hac.le hΔ c1,
    hasRiemannIntegral_sh_of_infClose hf2 hcb hΔ c2, ?_⟩
  rw [← sh_add (limited_hyperOrdSum hf1 hac.le hΔ.1) (limited_hyperOrdSum hf2 hcb hΔ.1), ← eS]
  exact (sh_eq_of_infClose (h.hyperOrdSum_infClose hΔ)).symm

/-- **Section 9.3, third property.** A function integrable on $`[a, b]` is integrable on
$`[a, c]` for $`a \le c \le b`. -/
theorem RiemannIntegrableOn.left (h : RiemannIntegrableOn f a b) (hac : a ≤ c) (hcb : c ≤ b) :
    RiemannIntegrableOn f a c := by
  obtain ⟨I₁, _, h1, -, -⟩ := h.hasRiemannIntegral.exists_split hac hcb
  exact ⟨I₁, h1⟩

/-- **Section 9.3, third property.** A function integrable on $`[a, b]` is integrable on
$`[c, b]` for $`a \le c \le b`. -/
theorem RiemannIntegrableOn.right (h : RiemannIntegrableOn f a b) (hac : a ≤ c) (hcb : c ≤ b) :
    RiemannIntegrableOn f c b := by
  obtain ⟨_, I₂, -, h2, -⟩ := h.hasRiemannIntegral.exists_split hac hcb
  exact ⟨I₂, h2⟩

/-- A function integrable on $`[a, b]` is integrable on every subinterval $`[c, d]`. -/
theorem RiemannIntegrableOn.subinterval (h : RiemannIntegrableOn f a b) (hac : a ≤ c)
    (hcd : c ≤ d) (hdb : d ≤ b) : RiemannIntegrableOn f c d :=
  (h.left (hac.trans hcd) hdb).right hac hcd

/-- **Section 9.3, third property (juxtaposition).** If $`f` is integrable on $`[a, b]` and
$`a \le c \le b`, then
$$`\int_a^b f(x)\,dx = \int_a^c f(x)\,dx + \int_c^b f(x)\,dx.` -/
theorem RiemannIntegrableOn.riemannIntegral_add_adjacent (h : RiemannIntegrableOn f a b)
    (hac : a ≤ c) (hcb : c ≤ b) :
    riemannIntegral f a b = riemannIntegral f a c + riemannIntegral f c b := by
  obtain ⟨I₁, I₂, h1, h2, h3⟩ := h.hasRiemannIntegral.exists_split hac hcb
  rw [h1.riemannIntegral_eq, h2.riemannIntegral_eq, h3]

end Juxtaposition

/-!
## 9.4 Differentiating the Area Function

Let $`f` be continuous on $`[a, b]` and let $`F(x) = \int_a^x f(t)\,dt` be the area under the
graph from $`a` to $`x`. The increment of $`F` from $`x` to a nearby point $`y` is the area
of a thin strip, which lies between the areas of the rectangles of width $`y - x` whose
heights are the least and the greatest value of $`f` between $`x` and $`y`. So the difference
quotient of $`F` lies between two values of $`f` at points between $`x` and $`y`. This holds
for all real $`y \ne x` in the interval, hence by transfer for all hyperreal $`y` in its
enlargement. If $`y \simeq x`, the two points are infinitely close to $`x`, so by continuity
the two values of $`f` are infinitely close to $`f(x)`, and so is the difference quotient.
By Theorem 8.1.1, $`F'(x) = f(x)`.
-/

section AreaFunction

variable {f G : ℝ → ℝ} {a b x y : ℝ}

/-- **Theorem 9.4.1, real form (inequality (v)).** Let $`f` be continuous on $`[a, b]` and
$`F(x) = \int_a^x f(t)\,dt`. For distinct points $`x, y \in [a, b]` there are points
$`x_1, x_2` of $`[a, b]`, no further from $`x` than $`y` is, with
$$`f(x_2) \le \frac{F(y) - F(x)}{y - x} \le f(x_1).`
They are the points between $`x` and $`y` at which $`f` is greatest and least. The proof
uses juxtaposition of integrals and the bounds $`m(y - x) \le \int_x^y f \le M(y - x)`. -/
theorem exists_points_areaQuotient (hf : ContinuousOn f (Icc a b)) (hx : x ∈ Icc a b)
    (hy : y ∈ Icc a b) (hxy : y ≠ x) :
    ∃ x₁ ∈ Icc a b, ∃ x₂ ∈ Icc a b, |x₁ - x| ≤ |y - x| ∧ |x₂ - x| ≤ |y - x| ∧
      f x₂ ≤ (riemannIntegral f a y - riemannIntegral f a x) / (y - x) ∧
      (riemannIntegral f a y - riemannIntegral f a x) / (y - x) ≤ f x₁ := by
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · have hint : RiemannIntegrableOn f a x :=
      riemannIntegrableOn_of_continuousOn hx.1 (hf.mono (Icc_subset_Icc le_rfl hx.2))
    have hsplit := hint.riemannIntegral_add_adjacent hy.1 hlt.le
    have hsub : Icc y x ⊆ Icc a b := Icc_subset_Icc hy.1 hx.2
    have hint' := hint.right hy.1 hlt.le
    obtain ⟨x₂, h2, x₁, h1, hm⟩ := extreme_value_Icc hlt.le (hf.mono hsub)
    have hlow := le_riemannIntegral hint' (m := f x₂) fun t ht => (hm t ht).1
    have hupp := riemannIntegral_le hint' (M := f x₁) fun t ht => (hm t ht).2
    have hpos : 0 < x - y := sub_pos.2 hlt
    have hq : (riemannIntegral f a y - riemannIntegral f a x) / (y - x) =
        riemannIntegral f y x / (x - y) := by
      rw [div_eq_div_iff (sub_ne_zero.2 hxy) hpos.ne', hsplit]
      ring
    refine ⟨x₁, hsub h1, x₂, hsub h2, ?_, ?_, ?_, ?_⟩
    · rw [abs_of_nonpos (by linarith [h1.2]), abs_of_neg (by linarith)]
      linarith [h1.1]
    · rw [abs_of_nonpos (by linarith [h2.2]), abs_of_neg (by linarith)]
      linarith [h2.1]
    · rw [hq, le_div_iff₀ hpos]
      exact hlow
    · rw [hq, div_le_iff₀ hpos]
      exact hupp
  · have hint : RiemannIntegrableOn f a y :=
      riemannIntegrableOn_of_continuousOn hy.1 (hf.mono (Icc_subset_Icc le_rfl hy.2))
    have hsplit := hint.riemannIntegral_add_adjacent hx.1 hlt.le
    have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
    have hint' := hint.right hx.1 hlt.le
    obtain ⟨x₂, h2, x₁, h1, hm⟩ := extreme_value_Icc hlt.le (hf.mono hsub)
    have hlow := le_riemannIntegral hint' (m := f x₂) fun t ht => (hm t ht).1
    have hupp := riemannIntegral_le hint' (M := f x₁) fun t ht => (hm t ht).2
    have hpos : 0 < y - x := sub_pos.2 hlt
    have hq : riemannIntegral f a y - riemannIntegral f a x = riemannIntegral f x y := by
      rw [hsplit]; ring
    refine ⟨x₁, hsub h1, x₂, hsub h2, ?_, ?_, ?_, ?_⟩
    · rw [abs_of_nonneg (by linarith [h1.1]), abs_of_pos (by linarith)]
      linarith [h1.2]
    · rw [abs_of_nonneg (by linarith [h2.1]), abs_of_pos (by linarith)]
      linarith [h2.2]
    · rw [hq, le_div_iff₀ hpos]
      exact hlow
    · rw [hq, div_le_iff₀ hpos]
      exact hupp

/-- **Theorem 9.4.1.** If $`f` is continuous on $`[a, b]`, the area function
$`F(x) = \int_a^x f(t)\,dt` is differentiable on $`[a, b]` with derivative $`f`, where at
the end points the derivative is the one-sided one. In Lean: at each $`x \in [a, b]` the
function $`F` has derivative $`f(x)` relative to $`[a, b]`.

The proof is the book's: by transfer of {name}`exists_points_areaQuotient`, for
$`y \simeq x` in the enlargement of $`[a, b]` the difference quotient of $`F` lies between
the values of the extension of $`f` at two points infinitely close to $`x`, and these values
are infinitely close to $`f(x)` by continuity. Then Theorem 8.1.1 applies. -/
theorem hasDerivWithinAt_riemannIntegral (hf : ContinuousOn f (Icc a b)) (hx : x ∈ Icc a b) :
    HasDerivWithinAt (fun t => riemannIntegral f a t) (f x) (Icc a b) x := by
  rw [hasDerivWithinAt_iff_infClose]
  intro y hy hyx hne
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep y
  have hr := hyperreal_ofSeq_mem_starSet.1 hy
  have hne' : ∀ᶠ n in hyperfilter ℕ, r n ≠ x := by
    rw [(hyperfilter ℕ).eventually_not]
    intro h
    exact hne (by rw [coe_eq_ofSeq_const, ofSeq_eq_ofSeq_iff]; exact h)
  -- the points x₁, x₂ of the book, chosen at each index
  have hex : ∀ n, ∃ x₁ x₂ : ℝ, r n ∈ Icc a b → r n ≠ x →
      x₁ ∈ Icc a b ∧ x₂ ∈ Icc a b ∧ |x₁ - x| ≤ |r n - x| ∧ |x₂ - x| ≤ |r n - x| ∧
      f x₂ ≤ (riemannIntegral f a (r n) - riemannIntegral f a x) / (r n - x) ∧
      (riemannIntegral f a (r n) - riemannIntegral f a x) / (r n - x) ≤ f x₁ := by
    intro n
    by_cases h : r n ∈ Icc a b ∧ r n ≠ x
    · obtain ⟨x₁, h1, x₂, h2, h3⟩ := exists_points_areaQuotient hf hx h.1 h.2
      exact ⟨x₁, x₂, fun _ _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨a, a, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose x₁ x₂ hpts using hex
  have hev := hr.and hne'
  have hi : Infinitesimal (Hyperreal.ofSeq r - (x : ℝ*)) := hyx
  -- both points are in the enlargement of [a, b] and infinitely close to x
  have hX1 : Hyperreal.ofSeq x₁ ∈ ⋆(Icc a b) :=
    hyperreal_ofSeq_mem_starSet.2 (hev.mono fun n hn => (hpts n hn.1 hn.2).1)
  have hX2 : Hyperreal.ofSeq x₂ ∈ ⋆(Icc a b) :=
    hyperreal_ofSeq_mem_starSet.2 (hev.mono fun n hn => (hpts n hn.1 hn.2).2.1)
  have hX1x : Hyperreal.ofSeq x₁ ≊ (x : ℝ*) := by
    refine hi.of_abs_le ?_
    change |Hyperreal.ofSeq (fun n => x₁ n - x)| ≤ |Hyperreal.ofSeq (fun n => r n - x)|
    rw [abs_ofSeq, abs_ofSeq, ofSeq_le_ofSeq_iff]
    exact hev.mono fun n hn => (hpts n hn.1 hn.2).2.2.1
  have hX2x : Hyperreal.ofSeq x₂ ≊ (x : ℝ*) := by
    refine hi.of_abs_le ?_
    change |Hyperreal.ofSeq (fun n => x₂ n - x)| ≤ |Hyperreal.ofSeq (fun n => r n - x)|
    rw [abs_ofSeq, abs_ofSeq, ofSeq_le_ofSeq_iff]
    exact hev.mono fun n hn => (hpts n hn.1 hn.2).2.2.2.1
  have hf1 := continuousOn_iff_infClose.1 hf x hx _ hX1 hX1x
  have hf2 := continuousOn_iff_infClose.1 hf x hx _ hX2 hX2x
  -- the transfer of (v)
  have hlow : ⋆f (Hyperreal.ofSeq x₂) ≤
      (⋆(fun t => riemannIntegral f a t) (Hyperreal.ofSeq r) - ((riemannIntegral f a x : ℝ) : ℝ*)) /
        (Hyperreal.ofSeq r - (x : ℝ*)) := by
    change Hyperreal.ofSeq (fun n => f (x₂ n)) ≤ Hyperreal.ofSeq (fun n =>
      (riemannIntegral f a (r n) - riemannIntegral f a x) / (r n - x))
    exact ofSeq_le_ofSeq_iff.2 (hev.mono fun n hn => (hpts n hn.1 hn.2).2.2.2.2.1)
  have hupp : (⋆(fun t => riemannIntegral f a t) (Hyperreal.ofSeq r) -
      ((riemannIntegral f a x : ℝ) : ℝ*)) / (Hyperreal.ofSeq r - (x : ℝ*)) ≤
      ⋆f (Hyperreal.ofSeq x₁) := by
    change Hyperreal.ofSeq (fun n =>
      (riemannIntegral f a (r n) - riemannIntegral f a x) / (r n - x)) ≤
      Hyperreal.ofSeq (fun n => f (x₁ n))
    exact ofSeq_le_ofSeq_iff.2 (hev.mono fun n hn => (hpts n hn.1 hn.2).2.2.2.2.2)
  exact infClose_of_le_of_le hlow hupp hf2 hf1

/-- **Theorem 9.4.1, at interior points.** If $`f` is continuous on $`[a, b]` and
$`a < x < b`, the area function $`F(x) = \int_a^x f(t)\,dt` is differentiable at $`x` with
$`F'(x) = f(x)`. -/
theorem hasDerivAt_riemannIntegral (hf : ContinuousOn f (Icc a b)) (hx : x ∈ Ioo a b) :
    HasDerivAt (fun t => riemannIntegral f a t) (f x) x :=
  (hasDerivWithinAt_riemannIntegral hf (Ioo_subset_Icc_self hx)).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)

/-- **Theorem 9.4.1, continuity of the area function.** The area function of a function
continuous on $`[a, b]` is continuous on $`[a, b]`. -/
theorem continuousOn_riemannIntegral (hf : ContinuousOn f (Icc a b)) :
    ContinuousOn (fun t => riemannIntegral f a t) (Icc a b) :=
  fun _ hx => (hasDerivWithinAt_riemannIntegral hf hx).continuousWithinAt

/-- **Theorem 9.4.2 (Fundamental Theorem of Calculus).** If a function $`G` has the
continuous derivative $`f` on $`[a, b]` (one-sided at the end points), then
$$`\int_a^b f(x)\,dx = G(b) - G(a).`
As in the book, this follows from Theorem 9.4.1 by an argument without infinitesimals: with
$`F` the area function, $`G - F` has derivative zero on $`[a, b]`, so it is constant there
(Section 8.5), and $`F(a) = 0`. -/
theorem riemannIntegral_eq_sub_of_hasDerivWithinAt (hf : ContinuousOn f (Icc a b))
    (hG : ∀ x ∈ Icc a b, HasDerivWithinAt G (f x) (Icc a b) x) (hab : a ≤ b) :
    riemannIntegral f a b = G b - G a := by
  have hH : ∀ x ∈ Icc a b,
      HasDerivWithinAt (fun t => G t - riemannIntegral f a t) 0 (Icc a b) x := fun x hx => by
    have h := (hG x hx).sub (hasDerivWithinAt_riemannIntegral hf hx)
    rw [sub_self] at h
    exact h
  have hcont : ContinuousOn (fun t => G t - riemannIntegral f a t) (Icc a b) :=
    fun x hx => (hH x hx).continuousWithinAt
  have hd : ∀ t ∈ Ioo a b, HasDerivAt (fun t => G t - riemannIntegral f a t) 0 t :=
    fun t ht => (hH t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have h := eq_of_deriv_eq_zero_on_Ioo hcont hd (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)
  simp only [riemannIntegral_self] at h
  linarith

/-- **Theorem 9.4.2 (Fundamental Theorem of Calculus), two-sided form.** If $`G` is
differentiable at every point of $`[a, b]` with derivative $`f`, and $`f` is continuous on
$`[a, b]`, then $`\int_a^b f(x)\,dx = G(b) - G(a)`. -/
theorem riemannIntegral_eq_sub_of_hasDerivAt (hf : ContinuousOn f (Icc a b))
    (hG : ∀ x ∈ Icc a b, HasDerivAt G (f x) x) (hab : a ≤ b) :
    riemannIntegral f a b = G b - G a :=
  riemannIntegral_eq_sub_of_hasDerivWithinAt hf (fun x hx => (hG x hx).hasDerivWithinAt) hab

/-- **Section 9.4, example.** $`\int_0^1 x\,dx = \tfrac12`, by the fundamental theorem with
$`G(x) = x^2/2`. -/
theorem riemannIntegral_id_zero_one : riemannIntegral (fun x => x) 0 1 = 1 / 2 := by
  have hG : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := fun x _ => by
    have h := (hasDerivAt_pow 2 x).div_const 2
    convert h using 1
    simp
  rw [riemannIntegral_eq_sub_of_hasDerivAt (f := fun x : ℝ => x) continuousOn_id hG zero_le_one]
  norm_num

/-- **Chapter 9, bridge to Mathlib.** For a function continuous on $`[a, b]`, the Riemann
integral of this chapter is Mathlib's interval integral:
$`\int_a^b f(x)\,dx` in the sense of {name}`riemannIntegral` equals
{lit}`∫ x in a..b, f x`. Both integrals, as functions of the upper limit, have derivative
$`f` on $`[a, b]` (Theorem 9.4.1 here, and the corresponding Mathlib theorem), so the
identification is an instance of Theorem 9.4.2. -/
theorem riemannIntegral_eq_intervalIntegral (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    riemannIntegral f a b = ∫ t in a..b, f t := by
  have hint : ∀ x ∈ Icc a b, IntervalIntegrable f MeasureTheory.volume a x := fun x hx =>
    (hf.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1
  have hG : ∀ x ∈ Icc a b,
      HasDerivWithinAt (fun u => ∫ t in a..u, f t) (f x) (Icc a b) x := by
    intro x hx
    have : Fact (x ∈ Icc a b) := ⟨hx⟩
    exact intervalIntegral.integral_hasDerivWithinAt_right (hint x hx)
      (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x) (hf x hx)
  rw [riemannIntegral_eq_sub_of_hasDerivWithinAt hf hG hab]
  simp

end AreaFunction

/-!
## 9.5 Exercise on Average Function Values

The average of the values of $`f` at the $`n` points $`a + i(b - a)/n`, $`0 \le i < n`, is
the Riemann sum $`S_a^b(f, (b - a)/n)` divided by $`b - a`. For an unlimited $`N` the Riemann
sum is infinitely close to the integral, so the extended average at $`N` is infinitely close
to $`\frac{1}{b - a}\int_a^b f(x)\,dx`: the average value of $`f` on $`[a, b]` is the shadow
of the sample average over an unlimited number of equally spaced sample points.
-/

section Average

variable {f : ℝ → ℝ} {a b : ℝ} {N : ℝ*}

/-- **Section 9.5.** The _sample average_ $`\mathrm{Av}(n) = \bigl(f(x_0) + \cdots +
f(x_{n-1})\bigr)/n` of $`f` at the points $`x_i = a + i(b - a)/n`, which are the partition
points {name}`partitionPoint` of Section 7.5. -/
def sampleAverage (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, f (partitionPoint a b n i)) / n

/-- **Section 9.5.** For $`n \ge 1`, $`\mathrm{Av}(n)\,(b - a) = S_a^b(f, (b - a)/n)`. -/
theorem sampleAverage_mul_sub {n : ℕ} (hn : n ≠ 0) (hab : a < b) :
    sampleAverage f a b n * (b - a) = ordSumN f a b n := by
  rw [ordSumN, ordSum, meshSumOf, meshCard_div_natCast n hab, sampleAverage,
    div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [meshPoint_div_of_le hn hab.le hk'.le, meshPoint_div_of_le hn hab.le hk', partitionPoint]
  push_cast
  ring

/-- **Exercise 9.5, for integrable functions.** If $`f` is Riemann integrable on $`[a, b]`,
$`a < b`, and $`N` is an unlimited hypernatural, then
$$`\mathrm{Av}(N) \simeq \frac{1}{b - a}\int_a^b f(x)\,dx.` -/
theorem RiemannIntegrableOn.hyperSeq_sampleAverage_infClose (h : RiemannIntegrableOn f a b)
    (hab : a < b) (hN : N ∈ unlimitedHyperNat) :
    hyperSeq (sampleAverage f a b) N ≊ ((1 / (b - a) * riemannIntegral f a b : ℝ) : ℝ*) := by
  have hS := h.hyperOrdSum_infClose (posInfinitesimal_width hab hN)
  rw [← hyperSeq_ordSumN f a b hN.1] at hS
  obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
  have hne : b - a ≠ 0 := (sub_pos.2 hab).ne'
  have e : hyperSeq (sampleAverage f a b) (hnat k) =
      ((1 / (b - a) : ℝ) : ℝ*) * hyperSeq (ordSumN f a b) (hnat k) := by
    rw [hyperSeq_hnat, hyperSeq_hnat]
    change _ = Hyperreal.ofSeq (fun n => 1 / (b - a) * ordSumN f a b (k n))
    rw [ofSeq_eq_ofSeq_iff]
    filter_upwards [(tendsto_atTop.1 hk) 1] with n hn
    rw [← sampleAverage_mul_sub (by omega) hab]
    field_simp
  rw [e, Hyperreal.coe_mul]
  exact hS.mul_left (limited_coe _)

/-- **Exercise 9.5.** Let $`f` be continuous on $`[a, b]`, $`a < b`. If $`N` is an unlimited
hypernatural then
$$`\mathrm{Av}(N) \simeq \frac{1}{b - a}\int_a^b f(x)\,dx,`
so the average value of $`f` on $`[a, b]` is the shadow of $`\mathrm{Av}(N)`. -/
theorem hyperSeq_sampleAverage_infClose (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hN : N ∈ unlimitedHyperNat) :
    hyperSeq (sampleAverage f a b) N ≊ ((1 / (b - a) * riemannIntegral f a b : ℝ) : ℝ*) :=
  (riemannIntegrableOn_of_continuousOn hab.le hf).hyperSeq_sampleAverage_infClose hab hN

/-- **Exercise 9.5, shadow form.** For $`f` continuous on $`[a, b]`, $`a < b`, and $`N`
unlimited, $`\operatorname{sh}\bigl(\mathrm{Av}(N)\bigr) = \frac{1}{b - a}\int_a^b f(x)\,dx`. -/
theorem sh_hyperSeq_sampleAverage (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hN : N ∈ unlimitedHyperNat) :
    sh (hyperSeq (sampleAverage f a b) N) = 1 / (b - a) * riemannIntegral f a b :=
  sh_eq_of_infClose (hyperSeq_sampleAverage_infClose hab hf hN)

/-- **Exercise 9.5, standard form.** For $`f` continuous on $`[a, b]`, $`a < b`, the sample
averages converge to the average value of $`f`. -/
theorem tendsto_sampleAverage (hab : a < b) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (sampleAverage f a b) atTop (𝓝 (1 / (b - a) * riemannIntegral f a b)) :=
  tendsto_iff_forall_unlimited_infClose.2 fun _ hN => hyperSeq_sampleAverage_infClose hab hf hN

end Average

end Goldblatt
