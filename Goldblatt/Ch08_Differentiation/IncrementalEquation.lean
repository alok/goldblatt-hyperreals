import Goldblatt.Ch08_Differentiation.Taylor

/-!
# 8 (part 4). The Incremental Equation at Nonreal Points: Sections 8.11 and 8.12

This is the last of four parts of Chapter 8 (the overview is on the chapter page
{lit}`Goldblatt.Ch08_Differentiation`). The incremental equation of Theorem 8.2.2 holds at
every real point of differentiability. This part asks when it holds at hyperreal points, and
shows that for a function differentiable on a real open interval it holds at all points well
inside the enlarged interval exactly when the derivative is continuous on the interval
(Theorem 8.11.1, with Exercise 8.12(1) supplying one direction). Exercise 8.12(2) exhibits a
differentiable function with a discontinuous derivative and an infinitesimal point at which
the incremental equation fails.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## 8.11 Extending the Incremental Equation

A hyperreal $`x` is _well inside_ an interval $`(y, z)` if it lies in the interval and is
not infinitely close to either end point; equivalently, the whole halo of $`x` lies in the
interval. For a real interval $`(a, b)`, the points well inside its enlargement are exactly
the hyperreals infinitely close to a real point of $`(a, b)`.

Theorem 8.11.1 says that, for $`f` differentiable on $`(a, b)`, the derivative $`f'` is
continuous on $`(a, b)` if and only if
$`f(x + \Delta x) = f(x) + f'(x)\,\Delta x + \varepsilon\,\Delta x` with $`\varepsilon`
infinitesimal, for every $`x` well inside the enlarged interval and every infinitesimal
$`\Delta x`. Here $`f` and $`f'` stand for the extensions of the function and of its
derivative function. Assuming the equation, continuity is obtained by comparing the equation
at a real point $`c` for the increment $`\Delta = x - c` with the equation at $`x \simeq c`
for the increment $`-\Delta`. The converse is Exercise 8.12(1), proved in the next section.
-/

section WellInside

variable {f : ℝ → ℝ} {a b c : ℝ} {x y z Δ : ℝ*}

/-- **Section 8.11, well inside.** The relation "$`x` is _well inside_ $`(y, z)`" between
three hyperreals: $`x` lies strictly between $`y` and $`z` and stays at a non-infinitesimal
distance from both. -/
def WellInside (x y z : ℝ*) : Prop := y < x ∧ x < z ∧ ¬ x ≊ y ∧ ¬ x ≊ z

/-- **Section 8.11.** A hyperreal $`x` is well inside $`(y, z)` if and only if
$`y < x + \Delta x < z` for all infinitesimals $`\Delta x`. -/
theorem wellInside_iff_forall_infinitesimal :
    WellInside x y z ↔ ∀ Δ : ℝ*, Infinitesimal Δ → y < x + Δ ∧ x + Δ < z := by
  constructor
  · rintro ⟨hy, hz, hny, hnz⟩ Δ hΔ
    constructor
    · by_contra hcon
      rw [not_lt] at hcon
      refine hny (hΔ.of_abs_le ?_)
      rw [abs_of_pos (sub_pos.2 hy)]
      exact le_trans (by linarith) (neg_le_abs Δ)
    · by_contra hcon
      rw [not_lt] at hcon
      refine hnz (hΔ.of_abs_le ?_)
      rw [abs_of_neg (sub_neg.2 hz)]
      exact le_trans (by linarith) (le_abs_self Δ)
  · intro h
    have h0 := h 0 infinitesimal_zero
    rw [add_zero] at h0
    refine ⟨h0.1, h0.2, fun hxy => ?_, fun hxz => ?_⟩
    · have := (h (y - x) hxy.symm).1
      rw [add_sub_cancel] at this
      exact lt_irrefl _ this
    · have := (h (z - x) hxz.symm).2
      rw [add_sub_cancel] at this
      exact lt_irrefl _ this

/-- **Section 8.11.** A hyperreal $`x` is well inside $`(y, z)` if and only if the halo of
$`x` is included in the interval. -/
theorem wellInside_iff_hal_subset : WellInside x y z ↔ hal x ⊆ Ioo y z := by
  rw [wellInside_iff_forall_infinitesimal]
  constructor
  · intro h w hw
    have := h (w - x) (by
      have h1 : Infinitesimal (x - w) := hw
      simpa using h1.neg)
    rwa [add_sub_cancel] at this
  · intro h Δ hΔ
    refine h ?_
    rw [mem_hal, infClose_iff]
    simpa using hΔ.neg

/-- **Section 8.11.** A hyperreal infinitely close to a real point of $`(a, b)` is well
inside the enlarged interval. -/
theorem wellInside_of_infClose (hc : c ∈ Ioo a b) (hx : x ≊ c) : WellInside x a b := by
  rw [wellInside_iff_forall_infinitesimal]
  intro Δ hΔ
  have h1 : Infinitesimal (x - c + Δ) := Infinitesimal.add hx hΔ
  have h2 : x + Δ = (c : ℝ*) + (x - c + Δ) := by ring
  rw [h2]
  exact ⟨coe_lt_coe_add_infinitesimal hc.1 h1, coe_add_infinitesimal_lt_coe hc.2 h1⟩

/-- **Section 8.11.** A hyperreal well inside the enlargement of a real interval $`(a, b)`
is limited, and its shadow is a real point of $`(a, b)`. -/
theorem WellInside.infClose_sh (h : WellInside x a b) : x ≊ sh x ∧ sh x ∈ Ioo a b := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hIcc : x ∈ Icc (a : ℝ*) b := ⟨h1.le, h2.le⟩
  have hlim := limited_of_mem_Icc hIcc
  have hsh := sh_mem_Icc hIcc
  have hclose := hlim.infClose_sh
  refine ⟨hclose, lt_of_le_of_ne hsh.1 fun h => h3 (h ▸ hclose),
    lt_of_le_of_ne hsh.2 fun h => h4 (h ▸ hclose)⟩

/-- **Section 8.11.** The points well inside the enlargement of a real interval $`(a, b)`
are exactly the hyperreals infinitely close to a real point of the interval. -/
theorem wellInside_coe_iff : WellInside x a b ↔ ∃ c ∈ Ioo a b, x ≊ c :=
  ⟨fun h => ⟨sh x, h.infClose_sh.2, h.infClose_sh.1⟩, fun ⟨_, hc, hx⟩ =>
    wellInside_of_infClose hc hx⟩

/-- **Section 8.11.** A point well inside the enlargement of $`(a, b)` belongs to it, and
so does every point at an infinitesimal distance from it. -/
theorem WellInside.add_mem_starSet (h : WellInside x a b) (hΔ : Infinitesimal Δ) :
    x + Δ ∈ ⋆(Ioo a b) := by
  rw [starSet_Ioo_real]
  exact wellInside_iff_forall_infinitesimal.1 h Δ hΔ

/-- **Chapter 8, transfer tool (mean value theorem between two hyperreal points).** If $`f`
has derivative $`f'` at every point of a real interval $`J`, then for any two points $`x`,
$`y` of the enlargement of $`J` there is a hyperreal $`u` between them with
$`{}^*f(y) - {}^*f(x) = {}^*f'(u)\,(y - x)`. This is the transfer of the mean value theorem
of Section 8.5. -/
theorem exists_mem_uIcc_starMap_sub_eq {f' : ℝ → ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    (hd : ∀ t ∈ J, HasDerivAt f (f' t) t) (hx : x ∈ ⋆J) (hy : y ∈ ⋆J) :
    ∃ u ∈ uIcc x y, ⋆f y - ⋆f x = ⋆f' u * (y - x) := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
  have hr := hyperreal_ofSeq_mem_starSet.1 hx
  have hs := hyperreal_ofSeq_mem_starSet.1 hy
  have hstd : ∀ n, ∃ u : ℝ, r n ∈ J → s n ∈ J →
      u ∈ uIcc (r n) (s n) ∧ f (s n) - f (r n) = f' u * (s n - r n) := by
    intro n
    by_cases hn : r n ∈ J ∧ s n ∈ J
    · obtain ⟨u, hu, heq⟩ := exists_sub_eq_deriv_mul_sub (f := f) (f' := f')
        fun t ht => hd t (hJ.uIcc_subset hn.1 hn.2 ht)
      exact ⟨u, fun _ _ => ⟨hu, heq⟩⟩
    · exact ⟨r n, fun h1 h2 => absurd ⟨h1, h2⟩ hn⟩
  choose u hu using hstd
  refine ⟨Hyperreal.ofSeq u, ?_, ?_⟩
  · rw [ofSeq_mem_uIcc]
    filter_upwards [hr, hs] with n h1 h2 using (hu n h1 h2).1
  · have key : (Hyperreal.ofSeq fun n => f (s n) - f (r n)) =
        Hyperreal.ofSeq fun n => f' (u n) * (s n - r n) := by
      rw [ofSeq_eq_ofSeq_iff]
      filter_upwards [hr, hs] with n h1 h2 using (hu n h1 h2).2
    exact key

/-- **Theorem 8.11.1, the book's half.** For $`f` differentiable on the real interval
$`(a, b)`, the derivative $`f'` is continuous on $`(a, b)` as soon as the incremental
equation $`{}^*f(x + \Delta x) = {}^*f(x) + {}^*f'(x)\,\Delta x + \varepsilon\,\Delta x`,
with $`\varepsilon` infinitesimal depending on $`x` and $`\Delta x`, is valid for all
infinitesimal increments at every hyperreal point whose halo lies in the enlarged
interval. -/
theorem continuousOn_deriv_of_incremental_equation (hf : DifferentiableOn ℝ f (Ioo a b))
    (h : ∀ x : ℝ*, WellInside x a b → ∀ Δ : ℝ*, Infinitesimal Δ →
      ∃ η : ℝ*, Infinitesimal η ∧ ⋆f (x + Δ) = ⋆f x + ⋆(deriv f) x * Δ + η * Δ) :
    ContinuousOn (deriv f) (Ioo a b) := by
  intro c hc
  refine ContinuousAt.continuousWithinAt ?_
  rw [continuousAt_iff_infClose]
  intro x hx
  rcases eq_or_ne x c with rfl | hne
  · exact InfClose.refl _
  -- the increment `Δ = x - c`
  have hΔ : Infinitesimal (x - c) := hx
  have hΔ0 : x - (c : ℝ*) ≠ 0 := sub_ne_zero.2 hne
  -- the incremental equation at the real point `c`, for `Δ`
  have hder : HasDerivAt f (deriv f c) c :=
    (hf.differentiableAt (Ioo_mem_nhds hc.1 hc.2)).hasDerivAt
  obtain ⟨η, hη, h1⟩ := hder.incremental_equation hΔ
  rw [add_sub_cancel] at h1
  -- the assumed incremental equation at `x`, for `-Δ`
  obtain ⟨η', hη', h2⟩ := h x (wellInside_of_infClose hc hx) (-(x - c)) hΔ.neg
  have h3 : x + -(x - (c : ℝ*)) = c := by ring
  rw [h3, starMap_coe] at h2
  -- combining the two equations
  have key : (⋆(deriv f) x - (deriv f c : ℝ) - (η - η')) * (x - c) = 0 := by
    linear_combination h1 + h2
  have h4 : ⋆(deriv f) x - (deriv f c : ℝ) = η - η' :=
    sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_right hΔ0)
  rw [infClose_iff, h4]
  exact hη.sub hη'

end WellInside

/-!
## 8.12 Exercises on Increments and Derivatives

Exercise (1) proves the remaining half of Theorem 8.11.1. Let $`f'` be continuous on
$`(a, b)`, let $`x` be well inside the enlarged interval and let $`\Delta x` be a nonzero
infinitesimal. The mean value theorem, transferred, gives a hyperreal $`u` between $`x` and
$`x + \Delta x` at which $`f'(u)` equals the Newton quotient of $`f` at $`x`. Both $`u` and
$`x` are infinitely close to the shadow of $`x`, a real point of the interval at which
$`f'` is continuous, so $`f'(u) \simeq f'(x)`. Hence the Newton quotient at the hyperreal
point $`x` is infinitely close to $`f'(x)`, which is the incremental equation.

Exercise (2) shows that continuity cannot be dropped. The function $`f(x) = x^2 \sin(1/x)`,
with $`f(0) = 0`, is differentiable everywhere, with $`f'(0) = 0`, but
$`f'(x) = 2x\sin(1/x) - \cos(1/x)` for $`x \ne 0` has no limit at $`0`. At the infinitesimal
point $`x = 1/(2\pi N)` with $`N` unlimited we have $`f(x) = 0` and $`f'(x) = -1`, while
$`f` also vanishes at the point $`1/(2\pi N + \pi)`, which is at an infinitesimal distance
from $`x`; the Newton quotient for that increment is $`0`, not infinitely close to $`-1`.
This does not contradict Theorem 8.11.1 on the interval $`(0, 1)`, where $`f'` is
continuous, because $`x` is infinitely close to the end point $`0` and so not well inside.
-/

section Exercises

variable {f : ℝ → ℝ} {a b : ℝ} {x Δ N : ℝ*}

/-- **Exercise 8.12(1)(a).** When $`f'` exists and is continuous on $`(a, b)`, Newton
quotients compute the extended derivative also at nonreal points, provided they are well
inside the enlarged interval: at such a point $`x`, for every nonzero infinitesimal
$`\Delta x`,
$$`{}^*f'(x) \simeq \frac{{}^*f(x + \Delta x) - {}^*f(x)}{\Delta x}.` -/
theorem starMap_deriv_infClose_newtonQuotient (hf : DifferentiableOn ℝ f (Ioo a b))
    (hc : ContinuousOn (deriv f) (Ioo a b)) (hx : WellInside x a b) (hΔ : Infinitesimal Δ)
    (h0 : Δ ≠ 0) : ⋆(deriv f) x ≊ (⋆f (x + Δ) - ⋆f x) / Δ := by
  -- transfer of the mean value theorem
  obtain ⟨u, hu, heq⟩ := exists_mem_uIcc_starMap_sub_eq (f := f) (f' := deriv f)
    ordConnected_Ioo
    (fun t ht => (hf.differentiableAt (Ioo_mem_nhds ht.1 ht.2)).hasDerivAt)
    (by simpa using hx.add_mem_starSet infinitesimal_zero) (hx.add_mem_starSet hΔ)
  rw [add_sub_cancel_left] at heq
  have hq : (⋆f (x + Δ) - ⋆f x) / Δ = ⋆(deriv f) u := by
    rw [heq, mul_div_assoc, div_self h0, mul_one]
  rw [hq]
  -- the shadow of `x` and the continuity of the derivative there
  obtain ⟨hxs, hs⟩ := hx.infClose_sh
  have hcont : ContinuousAt (deriv f) (sh x) :=
    (hc _ hs).continuousAt (Ioo_mem_nhds hs.1 hs.2)
  have hxΔ : x + Δ ≊ x := by rw [infClose_iff]; simpa using hΔ
  have hux : u ≊ x := infClose_of_mem_uIcc hu (InfClose.refl _) hxΔ
  exact (hcont.starMap_infClose hxs).trans (hcont.starMap_infClose (hux.trans hxs)).symm

/-- **Exercise 8.12(1)(b).** When $`f'` exists and is continuous on $`(a, b)`, the
incremental equation is valid at every hyperreal $`x` well inside the enlarged interval: each
infinitesimal $`\Delta x` comes with an infinitesimal $`\varepsilon` such that
$$`{}^*f(x + \Delta x) = {}^*f(x) + {}^*f'(x)\,\Delta x + \varepsilon\,\Delta x.` -/
theorem exists_incremental_equation_of_wellInside (hf : DifferentiableOn ℝ f (Ioo a b))
    (hc : ContinuousOn (deriv f) (Ioo a b)) (hx : WellInside x a b) (hΔ : Infinitesimal Δ) :
    ∃ η : ℝ*, Infinitesimal η ∧ ⋆f (x + Δ) = ⋆f x + ⋆(deriv f) x * Δ + η * Δ := by
  rcases eq_or_ne Δ 0 with rfl | h0
  · exact ⟨0, infinitesimal_zero, by simp⟩
  refine ⟨(⋆f (x + Δ) - ⋆f x) / Δ - ⋆(deriv f) x,
    (starMap_deriv_infClose_newtonQuotient hf hc hx hΔ h0).symm, ?_⟩
  field_simp
  ring

/-- **Theorem 8.11.1.** For $`f` differentiable on a real interval $`(a, b)`, continuity of
$`f'` on $`(a, b)` is equivalent to the validity of the incremental equation
$$`{}^*f(x + \Delta x) = {}^*f(x) + {}^*f'(x)\,\Delta x + \varepsilon\,\Delta x,
  \qquad \varepsilon \simeq 0,`
with the extensions of $`f` and $`f'`, for all infinitesimal $`\Delta x` at every hyperreal
$`x` whose halo lies in the enlarged interval (that is, {name}`Goldblatt.WellInside` it). -/
theorem continuousOn_deriv_iff_incremental_equation (hf : DifferentiableOn ℝ f (Ioo a b)) :
    ContinuousOn (deriv f) (Ioo a b) ↔
      ∀ x : ℝ*, WellInside x a b → ∀ Δ : ℝ*, Infinitesimal Δ →
        ∃ η : ℝ*, Infinitesimal η ∧ ⋆f (x + Δ) = ⋆f x + ⋆(deriv f) x * Δ + η * Δ :=
  ⟨fun hc _ hx _ hΔ => exists_incremental_equation_of_wellInside hf hc hx hΔ,
    continuousOn_deriv_of_incremental_equation hf⟩

/-- **Theorem 8.11.1**, in the notation of increments and differentials of Section 8.2:
$`f'` is continuous on $`(a, b)` if and only if $`\Delta f = df + \varepsilon\,\Delta x`
with $`\varepsilon` infinitesimal at all points well inside the enlarged interval. -/
theorem continuousOn_deriv_iff_increment_eq (hf : DifferentiableOn ℝ f (Ioo a b)) :
    ContinuousOn (deriv f) (Ioo a b) ↔
      ∀ x : ℝ*, WellInside x a b → ∀ Δ : ℝ*, Infinitesimal Δ →
        ∃ η : ℝ*, Infinitesimal η ∧ increment f x Δ = differential f x Δ + η * Δ := by
  rw [continuousOn_deriv_iff_incremental_equation hf]
  refine forall₄_congr fun x _ Δ _ => exists_congr fun η => and_congr_right fun _ => ?_
  rw [increment, differential]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    linear_combination h

/-- **Exercise 8.12(2), the function.** $`f(x) = x^2 \sin(1/x)` for $`x \ne 0`, and
$`f(0) = 0`. -/
def sqSinInv (x : ℝ) : ℝ := if x = 0 then 0 else x ^ 2 * Real.sin (1 / x)

/-- **Exercise 8.12(2)(a).** $`|f(t)| \le t^2` for all real $`t`. -/
theorem abs_sqSinInv_le (t : ℝ) : |sqSinInv t| ≤ t ^ 2 := by
  unfold sqSinInv
  split_ifs with h
  · simp [h]
  · rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
    exact mul_le_of_le_one_right (sq_nonneg t) (Real.abs_sin_le_one _)

/-- **Exercise 8.12(2)(a).** $`f'(0)` exists and equals $`0`: by transfer
$`|{}^*f(\varepsilon)| \le \varepsilon^2`, so the Newton quotient of $`f` at $`0` with a
nonzero infinitesimal increment $`\varepsilon` is at most $`|\varepsilon|` in absolute
value. -/
theorem hasDerivAt_sqSinInv_zero : HasDerivAt sqSinInv 0 0 := by
  rw [hasDerivAt_iff_infClose]
  intro e he h0
  have hbound : |⋆sqSinInv e| ≤ e ^ 2 := by
    have := starMap_le_starMap_of_mem (A := univ) (f := fun t => |sqSinInv t|)
      (g := fun t => t ^ 2) (fun t _ => abs_sqSinInv_le t) (x := e)
      (by rw [starSet_univ]; exact mem_univ _)
    rwa [starMap_abs_apply, starMap_pow_apply] at this
  have hf0 : sqSinInv 0 = 0 := by simp [sqSinInv]
  rw [Hyperreal.coe_zero, zero_add, hf0, Hyperreal.coe_zero, sub_zero,
    ← infinitesimal_iff_infClose_zero]
  refine he.of_abs_le ?_
  rw [abs_div, div_le_iff₀ (abs_pos.2 h0), ← sq, sq_abs]
  exact hbound

/-- **Exercise 8.12(2)(a).** For $`t \ne 0` the derivative of $`f` is
$`f'(t) = 2t\sin(1/t) - \cos(1/t)`, by the rules of differentiation. -/
theorem hasDerivAt_sqSinInv_of_ne_zero {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt sqSinInv (2 * t * Real.sin (1 / t) - Real.cos (1 / t)) t := by
  have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
  have h1 := hp.fun_mul (hasDerivAt_inv ht).sin
  have h2 : sqSinInv =ᶠ[𝓝 t] fun s => s ^ 2 * Real.sin (s⁻¹) := by
    filter_upwards [isOpen_ne.mem_nhds ht] with s hs
    simp [sqSinInv, show s ≠ 0 from hs]
  convert h1.congr_of_eventuallyEq h2 using 1
  field_simp
  ring

/-- **Exercise 8.12(2)(a).** The function $`f` is differentiable at every real number. -/
theorem differentiable_sqSinInv : Differentiable ℝ sqSinInv := fun t => by
  rcases eq_or_ne t 0 with rfl | ht
  · exact hasDerivAt_sqSinInv_zero.differentiableAt
  · exact (hasDerivAt_sqSinInv_of_ne_zero ht).differentiableAt

/-- **Exercise 8.12(2), values at the special points.** For every natural number $`m`,
$`f` vanishes at $`1/(2\pi m)`. -/
theorem sqSinInv_one_div_nat_mul_two_pi (m : ℕ) :
    sqSinInv (1 / ((m : ℝ) * (2 * Real.pi))) = 0 := by
  unfold sqSinInv
  split_ifs with h
  · rfl
  · rw [one_div_one_div]
    have : Real.sin ((m : ℝ) * (2 * Real.pi)) = 0 := by
      simpa using Real.sin_add_nat_mul_two_pi 0 m
    rw [this, mul_zero]

/-- **Exercise 8.12(2), values at the special points.** For every natural number $`m`,
$`f` vanishes at $`1/(2\pi m + \pi)`. -/
theorem sqSinInv_one_div_nat_mul_two_pi_add_pi (m : ℕ) :
    sqSinInv (1 / ((m : ℝ) * (2 * Real.pi) + Real.pi)) = 0 := by
  unfold sqSinInv
  split_ifs with h
  · rfl
  · rw [one_div_one_div, Real.sin_add_pi]
    have : Real.sin ((m : ℝ) * (2 * Real.pi)) = 0 := by
      simpa using Real.sin_add_nat_mul_two_pi 0 m
    rw [this, neg_zero, mul_zero]

/-- **Exercise 8.12(2), values at the special points.** For every nonzero natural number
$`m`, the derivative of $`f` at $`1/(2\pi m)` is $`-1`. -/
theorem deriv_sqSinInv_one_div_nat_mul_two_pi {m : ℕ} (hm : m ≠ 0) :
    deriv sqSinInv (1 / ((m : ℝ) * (2 * Real.pi))) = -1 := by
  have h0 : 1 / ((m : ℝ) * (2 * Real.pi)) ≠ 0 :=
    one_div_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 hm) Real.two_pi_pos.ne')
  rw [(hasDerivAt_sqSinInv_of_ne_zero h0).deriv, one_div_one_div, Real.cos_nat_mul_two_pi]
  have : Real.sin ((m : ℝ) * (2 * Real.pi)) = 0 := by
    simpa using Real.sin_add_nat_mul_two_pi 0 m
  rw [this]
  ring

/-- **Exercise 8.12(2), the special points by transfer.** Let $`N` be an unlimited
hypernatural, $`x = 1/(2\pi N)` and $`x' = 1/(2\pi N + \pi)`. Then $`{}^*f(x) = 0`,
$`{}^*f(x') = 0` and $`{}^*f'(x) = -1`. -/
theorem starMap_sqSinInv_special (hN : N ∈ unlimitedHyperNat) :
    ⋆sqSinInv (1 / (N * ((2 * Real.pi : ℝ) : ℝ*))) = 0 ∧
      ⋆sqSinInv (1 / (N * ((2 * Real.pi : ℝ) : ℝ*) + (Real.pi : ℝ))) = 0 ∧
      ⋆(deriv sqSinInv) (1 / (N * ((2 * Real.pi : ℝ) : ℝ*))) = ((-1 : ℝ) : ℝ*) := by
  obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
  have hk0 : ∀ᶠ n in hyperfilter ℕ, k n ≠ 0 := hk.eventually (eventually_ne_atTop 0)
  have e1 : (1 / (hnat k * ((2 * Real.pi : ℝ) : ℝ*)) : ℝ*) =
      Hyperreal.ofSeq fun n => 1 / ((k n : ℝ) * (2 * Real.pi)) := rfl
  have e2 : (1 / (hnat k * ((2 * Real.pi : ℝ) : ℝ*) + (Real.pi : ℝ)) : ℝ*) =
      Hyperreal.ofSeq fun n => 1 / ((k n : ℝ) * (2 * Real.pi) + Real.pi) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, starMap_hyperreal_ofSeq, ← Hyperreal.coe_zero, coe_eq_ofSeq_const]
    exact congrArg Hyperreal.ofSeq (funext fun n => sqSinInv_one_div_nat_mul_two_pi (k n))
  · rw [e2, starMap_hyperreal_ofSeq, ← Hyperreal.coe_zero, coe_eq_ofSeq_const]
    exact congrArg Hyperreal.ofSeq
      (funext fun n => sqSinInv_one_div_nat_mul_two_pi_add_pi (k n))
  · rw [e1, starMap_hyperreal_ofSeq, coe_eq_ofSeq_const, ofSeq_eq_ofSeq_iff]
    exact hk0.mono fun n hn => deriv_sqSinInv_one_div_nat_mul_two_pi hn

/-- **Exercise 8.12(2).** For $`N` unlimited, the point $`x = 1/(2\pi N)` is a positive
infinitesimal. -/
theorem infinitesimal_one_div_mul_two_pi (hN : N ∈ unlimitedHyperNat) :
    Infinitesimal (1 / (N * ((2 * Real.pi : ℝ) : ℝ*))) ∧
      0 < 1 / (N * ((2 * Real.pi : ℝ) : ℝ*)) := by
  have hN' := mem_unlimitedHyperNat.1 hN
  have hpos : (0 : ℝ*) < N := lt_of_le_of_lt (by simp) (natCast_lt_of_mem_unlimitedHyperNat hN 0)
  have h2π : (0 : ℝ*) < ((2 * Real.pi : ℝ) : ℝ*) := by
    rw [← Hyperreal.coe_zero, Hyperreal.coe_lt_coe]
    exact Real.two_pi_pos
  refine ⟨?_, one_div_pos.2 (mul_pos hpos h2π)⟩
  rw [one_div]
  exact (hN'.2.mul_appreciable (appreciable_coe Real.two_pi_pos.ne')).inv_infinitesimal

/-- **Exercise 8.12(2)(a).** The derivative $`f'` is not continuous at $`0`: it takes the
value $`-1` at the infinitesimal $`1/(2\pi N)`, which is not infinitely close to
$`f'(0) = 0`. -/
theorem not_continuousAt_deriv_sqSinInv_zero : ¬ ContinuousAt (deriv sqSinInv) 0 := by
  intro h
  have hω := omega_mem_unlimitedHyperNat
  have hx := (infinitesimal_one_div_mul_two_pi hω).1
  have h1 := h.starMap_infClose (x := 1 / (ω * ((2 * Real.pi : ℝ) : ℝ*)))
    (by rw [Hyperreal.coe_zero]; exact infinitesimal_iff_infClose_zero.1 hx)
  rw [(starMap_sqSinInv_special hω).2.2, hasDerivAt_sqSinInv_zero.deriv, infClose_coe_iff] at h1
  norm_num at h1

/-- **Exercise 8.12(2)(b).** Let $`x = 1/(2\pi N)` with $`N` unlimited. Then there is an
infinitesimal $`\Delta x` such that the incremental equation
$`{}^*f(x + \Delta x) = {}^*f(x) + {}^*f'(x)\,\Delta x + \varepsilon\,\Delta x` fails for
every infinitesimal $`\varepsilon`. With $`\Delta x = 1/(2\pi N + \pi) - 1/(2\pi N)` the
equation reads $`0 = 0 - \Delta x + \varepsilon\,\Delta x`, which forces
$`\varepsilon = 1`. -/
theorem exists_infinitesimal_not_incremental_equation_sqSinInv (hN : N ∈ unlimitedHyperNat) :
    ∃ Δ : ℝ*, Infinitesimal Δ ∧ ¬ ∃ η : ℝ*, Infinitesimal η ∧
      ⋆sqSinInv (1 / (N * ((2 * Real.pi : ℝ) : ℝ*)) + Δ) =
        ⋆sqSinInv (1 / (N * ((2 * Real.pi : ℝ) : ℝ*))) +
          ⋆(deriv sqSinInv) (1 / (N * ((2 * Real.pi : ℝ) : ℝ*))) * Δ + η * Δ := by
  obtain ⟨h1, h2, h3⟩ := starMap_sqSinInv_special hN
  have hN' := mem_unlimitedHyperNat.1 hN
  set A : ℝ* := N * ((2 * Real.pi : ℝ) : ℝ*) with hA
  have hAun : Unlimited A := hN'.2.mul_appreciable (appreciable_coe Real.two_pi_pos.ne')
  have hA0 : A ≠ 0 := hAun.ne_zero
  have hBun : Unlimited (A + (Real.pi : ℝ)) := hAun.add_limited (limited_coe _)
  have hB0 : A + (Real.pi : ℝ) ≠ 0 := hBun.ne_zero
  have hπ : ((Real.pi : ℝ) : ℝ*) ≠ 0 := by
    rw [← Hyperreal.coe_zero, Ne, Hyperreal.coe_eq_coe]
    exact Real.pi_ne_zero
  refine ⟨1 / (A + (Real.pi : ℝ)) - 1 / A, ?_, ?_⟩
  · rw [one_div, one_div]
    exact hBun.inv_infinitesimal.sub hAun.inv_infinitesimal
  · rintro ⟨η, hη, heq⟩
    rw [add_sub_cancel, h1, h2, h3] at heq
    have hΔ0 : 1 / (A + (Real.pi : ℝ)) - 1 / A ≠ 0 := by
      rw [sub_ne_zero, Ne, one_div, one_div, inv_inj]
      intro h
      exact hπ (by linear_combination h)
    have hη1 : η = 1 := by
      have key : (η - 1) * (1 / (A + (Real.pi : ℝ)) - 1 / A) = 0 := by
        rw [Hyperreal.coe_neg, Hyperreal.coe_one] at heq
        linear_combination -heq
      exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_right hΔ0)
    rw [hη1] at hη
    exact appreciable_one.not_infinitesimal hη

/-- **Section 8.12, closing remark.** On the interval $`(0, 1)`, and indeed at every nonzero
real number, the derivative of $`f` is continuous. -/
theorem continuousOn_deriv_sqSinInv : ContinuousOn (deriv sqSinInv) {t : ℝ | t ≠ 0} := by
  have hinv : ContinuousOn (fun t : ℝ => 1 / t) {t : ℝ | t ≠ 0} :=
    continuousOn_const.div continuousOn_id fun _ ht => ht
  have hform : ContinuousOn (fun t : ℝ => 2 * t * Real.sin (1 / t) - Real.cos (1 / t))
      {t : ℝ | t ≠ 0} :=
    ((continuousOn_const.mul continuousOn_id).mul
      (Real.continuous_sin.comp_continuousOn hinv)).sub
      (Real.continuous_cos.comp_continuousOn hinv)
  exact hform.congr fun t ht => (hasDerivAt_sqSinInv_of_ne_zero ht).deriv

/-- **Section 8.12, closing remark.** The infinitesimal $`1/(2\pi N)` at which the
incremental equation fails is not well inside the enlargement of $`(0, 1)`, being
infinitely close to the end point $`0`; so Exercise (2) is consistent with Theorem 8.11.1
applied to the interval $`(0, 1)`, on which $`f'` is continuous. -/
theorem not_wellInside_one_div_mul_two_pi (hN : N ∈ unlimitedHyperNat) :
    ¬ WellInside (1 / (N * ((2 * Real.pi : ℝ) : ℝ*))) (0 : ℝ) (1 : ℝ) := fun h =>
  h.2.2.1 (by
    rw [Hyperreal.coe_zero]
    exact infinitesimal_iff_infClose_zero.1 (infinitesimal_one_div_mul_two_pi hN).1)

/-- **Section 8.12, closing remark.** At points well inside the enlargement of $`(0, 1)`
the incremental equation does hold for $`f`, by Theorem 8.11.1. -/
theorem exists_incremental_equation_sqSinInv (hx : WellInside x (0 : ℝ) (1 : ℝ))
    (hΔ : Infinitesimal Δ) :
    ∃ η : ℝ*, Infinitesimal η ∧
      ⋆sqSinInv (x + Δ) = ⋆sqSinInv x + ⋆(deriv sqSinInv) x * Δ + η * Δ :=
  exists_incremental_equation_of_wellInside differentiable_sqSinInv.differentiableOn
    (continuousOn_deriv_sqSinInv.mono fun _ ht => ht.1.ne') hx hΔ

end Exercises

end Goldblatt
