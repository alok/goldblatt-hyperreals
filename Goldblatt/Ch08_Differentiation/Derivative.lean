import Mathlib
import Goldblatt.Ch02_LargeSets
import Goldblatt.Ch03_Ultrapower
import Goldblatt.Ch05_GreatAndSmall
import Goldblatt.Ch06_Sequences
import Goldblatt.Ch07_Continuity

/-!
# 8 (part 1). The Derivative of a Function of One Variable: Sections 8.1 to 8.6

This is the first of four parts of Chapter 8 (the overview is on the chapter page
{lit}`Goldblatt.Ch08_Differentiation`). It characterises the derivative as the common shadow
of all Newton quotients with a nonzero infinitesimal increment, introduces increments and
differentials and proves the incremental equation, and then uses these to prove, with
infinitesimals in place of limits, that a differentiable function is continuous, the rules for
sums, products and quotients, the chain rule, the critical point theorem with its standard
consequences, and the inverse function theorem.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## Conventions and transfer tools

As in Chapter 7, a real function is a total function of type {lit}`ℝ → ℝ`, and the statement
"$`f` is differentiable at $`x` with derivative $`L`" is Mathlib's {name}`HasDerivAt`. The
book's phrase "$`f(x + \varepsilon)` is defined" therefore needs no counterpart: Mathlib's
notion of derivative at a point already requires the function to be given on a neighbourhood,
and a total function is defined everywhere. One-sided derivatives are expressed with
{name}`HasDerivWithinAt`.

This preliminary section is not a numbered section of the book. It collects a few transfer
facts that are used repeatedly: the extension of a composite, the transfer of strict
monotonicity, and the fact that a real open interval around $`x` contains the whole halo of
$`x`.
-/

section Tools

variable {f g : ℝ → ℝ} {A B : Set ℝ} {a b c x L : ℝ} {e y z : ℝ*}

/-- **Chapter 8, transfer tool.** The extension of a composite is the composite of the
extensions: $`{}^*(g \circ f)(z) = {}^*g({}^*f(z))`. -/
theorem starMap_comp_apply (g f : ℝ → ℝ) (z : ℝ*) : ⋆(fun t : ℝ => g (f t)) z = ⋆g (⋆f z) := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep z
  rfl

/-- **Chapter 8, transfer tool.** If $`f` is strictly increasing on $`A`, then
$`f(r) < {}^*f(z)` for every real $`r \in A` and every $`z \in {}^*A` with $`r < z`. -/
theorem coe_lt_starMap_of_strictMonoOn (hf : StrictMonoOn f A) {r : ℝ} (hr : r ∈ A)
    (hz : z ∈ ⋆A) (h : (r : ℝ*) < z) : ((f r : ℝ) : ℝ*) < ⋆f z := by
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep z
  rw [starMap_hyperreal_ofSeq, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
  rw [coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff] at h
  filter_upwards [hyperreal_ofSeq_mem_starSet.1 hz, h] with n h1 h2 using hf hr h1 h2

/-- **Chapter 8, transfer tool.** If $`f` is strictly increasing on $`A`, then
$`{}^*f(z) < f(r)` for every real $`r \in A` and every $`z \in {}^*A` with $`z < r`. -/
theorem starMap_lt_coe_of_strictMonoOn (hf : StrictMonoOn f A) {r : ℝ} (hr : r ∈ A)
    (hz : z ∈ ⋆A) (h : z < (r : ℝ*)) : ⋆f z < ((f r : ℝ) : ℝ*) := by
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep z
  rw [starMap_hyperreal_ofSeq, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
  rw [coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff] at h
  filter_upwards [hyperreal_ofSeq_mem_starSet.1 hz, h] with n h1 h2 using hf h1 hr h2

/-- **Chapter 8, tool.** The embedding of the reals in the hyperreals preserves powers. -/
theorem ofReal_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : ℝ*) = (r : ℝ*) ^ n :=
  map_pow Hyperreal.coeRingHom r n

/-- **Chapter 8, tool.** The embedding of the reals in the hyperreals preserves finite
sums. -/
theorem ofReal_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) :
    ((∑ i ∈ s, c i : ℝ) : ℝ*) = ∑ i ∈ s, (c i : ℝ*) :=
  map_sum Hyperreal.coeRingHom c s

/-- **Chapter 8, tool.** If $`c < x` are real and $`\varepsilon` is infinitesimal, then
$`c < x + \varepsilon`. -/
theorem coe_lt_coe_add_infinitesimal (h : c < x) (he : Infinitesimal e) :
    (c : ℝ*) < x + e := by
  have h1 := infinitesimal_iff_abs_lt.1 he (x - c) (sub_pos.2 h)
  have h2 := (abs_lt.1 h1).1
  rw [Hyperreal.coe_sub] at h2
  linarith

/-- **Chapter 8, tool.** If $`x < c` are real and $`\varepsilon` is infinitesimal, then
$`x + \varepsilon < c`. -/
theorem coe_add_infinitesimal_lt_coe (h : x < c) (he : Infinitesimal e) :
    (x : ℝ*) + e < c := by
  have h1 := infinitesimal_iff_abs_lt.1 he (c - x) (sub_pos.2 h)
  have h2 := (abs_lt.1 h1).2
  rw [Hyperreal.coe_sub] at h2
  linarith

/-- **Chapter 8, tool.** A real open interval containing the real number $`x` contains every
hyperreal $`x + \varepsilon` with $`\varepsilon` infinitesimal: the enlargement of the
interval includes the halo of each of its real points. -/
theorem coe_add_infinitesimal_mem_starSet_Ioo (hx : x ∈ Ioo a b) (he : Infinitesimal e) :
    (x : ℝ*) + e ∈ ⋆(Ioo a b) := by
  rw [starSet_Ioo_real]
  exact ⟨coe_lt_coe_add_infinitesimal hx.1 he, coe_add_infinitesimal_lt_coe hx.2 he⟩

/-- **Chapter 8, tool.** A neighbourhood of the real number $`x` contains, after enlargement,
every hyperreal $`x + \varepsilon` with $`\varepsilon` infinitesimal. -/
theorem coe_add_infinitesimal_mem_starSet_of_mem_nhds (hA : A ∈ 𝓝 x) (he : Infinitesimal e) :
    (x : ℝ*) + e ∈ ⋆A := by
  have h : (x : ℝ*) + e ∈ filterMonad (𝓝 x) := by
    rw [mem_filterMonad_nhds, infClose_iff]
    simpa using he
  exact h A hA

/-- **Chapter 8, tool.** The extension of the difference quotient of $`f` based at the real
point $`x`: at a hyperreal $`y` it is $`({}^*f(y) - f(x))/(y - x)`. -/
theorem starMap_slope_apply (f : ℝ → ℝ) (x : ℝ) (y : ℝ*) :
    ⋆(slope f x) y = (⋆f y - f x) / (y - x) := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep y
  have h : (⋆f (Hyperreal.ofSeq r) - ((f x : ℝ) : ℝ*)) / (Hyperreal.ofSeq r - (x : ℝ*)) =
      Hyperreal.ofSeq fun n => (f (r n) - f x) / (r n - x) := rfl
  rw [h, starMap_hyperreal_ofSeq]
  exact congrArg Hyperreal.ofSeq (funext fun n => slope_def_field f x (r n))

end Tools

/-!
## 8.1 The Derivative

The derivative of $`f` at $`x` is classically the limit of the Newton quotient
$`(f(x + h) - f(x))/h` as $`h` tends to $`0`. Chapter 7 characterised limits at a point: the
limit is $`L` exactly when the extension of the function sends every hyperreal infinitely
close to the point, and different from it, to a hyperreal infinitely close to $`L`. Applied to
the Newton quotient as a function of $`h` this gives Theorem 8.1.1: the derivative is $`L`
exactly when the quotient formed with any nonzero infinitesimal increment is infinitely close
to $`L`. Consequently the derivative is the shadow of any such quotient, which is how Leibniz
and Newton computed it. Restricting the sign of the increment gives the one-sided derivatives.
As a first application, Exercise 8.1.2 differentiates the sine function.
-/

section Derivative

variable {f g : ℝ → ℝ} {A : Set ℝ} {a b x L M : ℝ} {e y : ℝ*}

/-- **Theorem 8.1.1, relative to a set.** The function $`f` has derivative $`L` at the real
point $`x` relative to the set $`A` if and only if
$`({}^*f(y) - f(x))/(y - x) \simeq L` for every $`y \in {}^*A` with $`y \simeq x` and
$`y \ne x`. The book's proof is the one given here: apply the characterisation of limits of
Section 7.3 to the difference quotient. Taking $`A` to be the whole line, a right-hand ray or a
left-hand ray gives the derivative and the two one-sided derivatives. -/
theorem hasDerivWithinAt_iff_infClose :
    HasDerivWithinAt f L A x ↔
      ∀ y ∈ ⋆A, y ≊ x → y ≠ (x : ℝ*) → (⋆f y - f x) / (y - x) ≊ L := by
  rw [hasDerivWithinAt_iff_tendsto_slope, tendsto_nhdsWithin_diff_singleton_iff_infClose]
  simp only [starMap_slope_apply]

/-- **Theorem 8.1.1.** The real number $`L` is the derivative of $`f` at the real point $`x`
if and only if
$$`\frac{{}^*f(x + \varepsilon) - f(x)}{\varepsilon} \simeq L`
for every nonzero infinitesimal $`\varepsilon`. -/
theorem hasDerivAt_iff_infClose :
    HasDerivAt f L x ↔
      ∀ e : ℝ*, Infinitesimal e → e ≠ 0 → (⋆f (x + e) - f x) / e ≊ L := by
  rw [← hasDerivWithinAt_univ, hasDerivWithinAt_iff_infClose, starSet_univ]
  constructor
  · intro h e he h0
    have := h (x + e) (mem_univ _) (by rw [infClose_iff]; simpa using he) (by simpa using h0)
    simpa using this
  · intro h y _ hy hne
    have := h (y - x) hy (sub_ne_zero.2 hne)
    simpa using this

/-- **Theorem 8.1.1**, forward direction as a rule. -/
theorem _root_.HasDerivAt.newtonQuotient_infClose (h : HasDerivAt f L x)
    (he : Infinitesimal e) (h0 : e ≠ 0) : (⋆f (x + e) - f x) / e ≊ L :=
  hasDerivAt_iff_infClose.1 h e he h0

/-- **Section 8.1, the derivative as a shadow.** If $`f` is differentiable at $`x`, then
$$`f'(x) = \operatorname{sh}\left(\frac{{}^*f(x + \varepsilon) - f(x)}{\varepsilon}\right)`
for every nonzero infinitesimal $`\varepsilon`. -/
theorem deriv_eq_sh_newtonQuotient (h : DifferentiableAt ℝ f x) (he : Infinitesimal e)
    (h0 : e ≠ 0) : deriv f x = sh ((⋆f (x + e) - f x) / e) :=
  (sh_eq_of_infClose (h.hasDerivAt.newtonQuotient_infClose he h0)).symm

/-- **Section 8.1, differentiability.** A function is differentiable at $`x` if and only if
all Newton quotients with nonzero infinitesimal increment are limited and have the same
shadow. -/
theorem differentiableAt_iff_exists_infClose :
    DifferentiableAt ℝ f x ↔
      ∃ L : ℝ, ∀ e : ℝ*, Infinitesimal e → e ≠ 0 → (⋆f (x + e) - f x) / e ≊ L :=
  ⟨fun h => ⟨_, hasDerivAt_iff_infClose.1 h.hasDerivAt⟩,
    fun ⟨_, h⟩ => (hasDerivAt_iff_infClose.2 h).differentiableAt⟩

/-- **Section 8.1, right-hand derivative.** $`L` is the right-hand derivative of $`f` at
$`x` if and only if the Newton quotient is infinitely close to $`L` for every positive
infinitesimal increment. -/
theorem hasDerivWithinAt_Ioi_iff_infClose :
    HasDerivWithinAt f L (Ioi x) x ↔
      ∀ e : ℝ*, Infinitesimal e → 0 < e → (⋆f (x + e) - f x) / e ≊ L := by
  rw [hasDerivWithinAt_iff_infClose, starSet_Ioi_real]
  constructor
  · intro h e he h0
    have := h (x + e) (by simpa using h0) (by rw [infClose_iff]; simpa using he)
      (by simpa using h0.ne')
    simpa using this
  · intro h y hy hyx _
    have := h (y - x) hyx (sub_pos.2 hy)
    simpa using this

/-- **Section 8.1, left-hand derivative.** $`L` is the left-hand derivative of $`f` at $`x`
if and only if the Newton quotient is infinitely close to $`L` for every negative
infinitesimal increment. -/
theorem hasDerivWithinAt_Iio_iff_infClose :
    HasDerivWithinAt f L (Iio x) x ↔
      ∀ e : ℝ*, Infinitesimal e → e < 0 → (⋆f (x + e) - f x) / e ≊ L := by
  rw [hasDerivWithinAt_iff_infClose, starSet_Iio_real]
  constructor
  · intro h e he h0
    have := h (x + e) (by simpa using h0) (by rw [infClose_iff]; simpa using he)
      (by simpa using h0.ne)
    simpa using this
  · intro h y hy hyx _
    have := h (y - x) hyx (sub_neg.2 hy)
    simpa using this

/-- **Section 8.1.** A function has derivative $`L` at $`x` if and only if both one-sided
derivatives exist and equal $`L`: the nonzero infinitesimals are the positive ones together
with the negative ones. -/
theorem hasDerivAt_iff_Ioi_and_Iio :
    HasDerivAt f L x ↔ HasDerivWithinAt f L (Ioi x) x ∧ HasDerivWithinAt f L (Iio x) x := by
  rw [hasDerivAt_iff_infClose, hasDerivWithinAt_Ioi_iff_infClose,
    hasDerivWithinAt_Iio_iff_infClose]
  constructor
  · exact fun h => ⟨fun e he h0 => h e he h0.ne', fun e he h0 => h e he h0.ne⟩
  · rintro ⟨h1, h2⟩ e he h0
    rcases lt_or_gt_of_ne h0 with h | h
    · exact h2 e he h
    · exact h1 e he h

/-- **Section 8.1, non-vacuity.** The quantifier in Theorem 8.1.1 ranges over a nonempty
collection: there are positive and negative infinitesimals. -/
theorem exists_pos_and_neg_infinitesimal :
    (∃ e : ℝ*, Infinitesimal e ∧ 0 < e) ∧ ∃ e : ℝ*, Infinitesimal e ∧ e < 0 :=
  ⟨⟨ε, infinitesimal_epsilon, Hyperreal.epsilon_pos⟩,
    ⟨-ε, infinitesimal_epsilon.neg, neg_lt_zero.2 Hyperreal.epsilon_pos⟩⟩

/-- **Exercise 8.1.2.** The derivative of the sine function at a real number $`x` is
$`\cos x`. For a nonzero infinitesimal $`\varepsilon` the addition formula gives
$$`\frac{\sin(x + \varepsilon) - \sin x}{\varepsilon} =
  \sin x \cdot \frac{\cos\varepsilon - 1}{\varepsilon} +
  \cos x \cdot \frac{\sin\varepsilon}{\varepsilon},`
and by Exercise 5.7(2) the two quotients on the right are infinitely close to $`0` and $`1`
respectively. -/
theorem hasDerivAt_sin_infinitesimal (x : ℝ) : HasDerivAt Real.sin (Real.cos x) x := by
  rw [hasDerivAt_iff_infClose]
  intro e he h0
  have h1 : (⋆Real.sin ((x : ℝ*) + e) - ((Real.sin x : ℝ) : ℝ*)) / e =
      ((Real.sin x : ℝ) : ℝ*) * ((hcos e - 1) / e) + ((Real.cos x : ℝ) : ℝ*) * (hsin e / e) := by
    have h2 : ⋆Real.sin ((x : ℝ*) + e) = hsin ((x : ℝ*) + e) := rfl
    rw [h2, hsin_add, hsin_coe, hcos_coe]
    field_simp
    ring
  rw [h1]
  have h3 := (he.hcos_sub_one_div_infClose).mul_left (limited_coe (Real.sin x))
  have h4 := (he.hsin_div_infClose h0).mul_left (limited_coe (Real.cos x))
  have h5 := h3.add h4
  simpa using h5

/-- **Exercise 8.1.2, companion.** The derivative of the cosine function at a real number
$`x` is $`-\sin x`, by the same computation with the addition formula for the cosine. -/
theorem hasDerivAt_cos_infinitesimal (x : ℝ) : HasDerivAt Real.cos (-Real.sin x) x := by
  rw [hasDerivAt_iff_infClose]
  intro e he h0
  have h1 : (⋆Real.cos ((x : ℝ*) + e) - ((Real.cos x : ℝ) : ℝ*)) / e =
      ((Real.cos x : ℝ) : ℝ*) * ((hcos e - 1) / e) - ((Real.sin x : ℝ) : ℝ*) * (hsin e / e) := by
    have h2 : ⋆Real.cos ((x : ℝ*) + e) = hcos ((x : ℝ*) + e) := rfl
    rw [h2, hcos_add, hsin_coe, hcos_coe]
    field_simp
    ring
  rw [h1]
  have h3 := (he.hcos_sub_one_div_infClose).mul_left (limited_coe (Real.cos x))
  have h4 := (he.hsin_div_infClose h0).mul_left (limited_coe (Real.sin x))
  have h5 := h3.sub h4
  simpa using h5

end Derivative

/-!
## 8.2 Increments and Differentials

Fix a function $`f` and a point $`x`, and let $`\Delta x` be an infinitesimal change in the
variable. The corresponding _increment_ of $`f` is
$`\Delta f = f(x + \Delta x) - f(x)`, the change in the value along the graph, and the
_differential_ is $`df = f'(x)\,\Delta x`, the change along the tangent line. Theorem 8.1.1
says that $`\Delta f / \Delta x \simeq f'(x)`. Three things follow at once. The increment is
infinitesimal, so a differentiable function is continuous (Theorem 8.2.1). The differential is
infinitesimal. And the two differ by $`\varepsilon\,\Delta x` with $`\varepsilon`
infinitesimal, that is, by an amount that is infinitesimal even in comparison with
$`\Delta x`: this is the incremental equation (Theorem 8.2.2), which expresses that the
tangent is the best linear approximation to the graph.

Both notions are defined here at an arbitrary hyperreal point $`x`, using the extension of
$`f` and of its derivative, because Section 8.11 asks whether the incremental equation holds
at nonreal points. At a real point they reduce to the expressions above.
-/

section Increments

variable {f g : ℝ → ℝ} {x L M : ℝ} {e Δ : ℝ*}

/-- **Section 8.2, increment.** The increment $`\Delta f = {}^*f(x + \Delta x) - {}^*f(x)`
of $`f` at the hyperreal point $`x` corresponding to the change $`\Delta x`. In the book's
explicit notation this is $`\Delta f(x, \Delta x)`. -/
def increment (f : ℝ → ℝ) (x Δ : ℝ*) : ℝ* := ⋆f (x + Δ) - ⋆f x

/-- **Section 8.2, differential.** The differential $`df = {}^*f'(x)\,\Delta x` of $`f` at the
hyperreal point $`x` corresponding to the change $`\Delta x`, where $`f'` is the derivative
function of $`f` (Mathlib's {name}`deriv`). -/
def differential (f : ℝ → ℝ) (x Δ : ℝ*) : ℝ* := ⋆(deriv f) x * Δ

/-- **Section 8.2.** At a real point the increment is $`{}^*f(x + \Delta x) - f(x)`. -/
theorem increment_coe (f : ℝ → ℝ) (x : ℝ) (Δ : ℝ*) :
    increment f x Δ = ⋆f (x + Δ) - f x := rfl

/-- **Section 8.2.** At a real point the differential is $`f'(x)\,\Delta x`. -/
theorem differential_coe (f : ℝ → ℝ) (x : ℝ) (Δ : ℝ*) :
    differential f x Δ = (deriv f x : ℝ) * Δ := rfl

/-- **Section 8.2.** With $`dx = \Delta x`, the quotient of differentials is the derivative:
$`df/dx = f'(x)`. -/
theorem differential_div (f : ℝ → ℝ) (x : ℝ) {Δ : ℝ*} (h0 : Δ ≠ 0) :
    differential f x Δ / Δ = (deriv f x : ℝ) := by
  rw [differential_coe, mul_div_assoc, div_self h0, mul_one]

/-- **Section 8.2.** The increment of a function at a real point of differentiability is
infinitesimal whenever the change in the variable is: the Newton quotient is limited, being
infinitely close to the derivative, and $`\Delta f = (\Delta f/\Delta x)\,\Delta x`. -/
theorem _root_.HasDerivAt.infinitesimal_increment (h : HasDerivAt f L x)
    (he : Infinitesimal Δ) : Infinitesimal (increment f x Δ) := by
  rcases eq_or_ne Δ 0 with rfl | h0
  · simp [increment, infinitesimal_zero]
  have hq := h.newtonQuotient_infClose he h0
  have h1 : increment f x Δ = (⋆f (x + Δ) - f x) / Δ * Δ := by
    rw [increment_coe, div_mul_cancel₀ _ h0]
  rw [h1]
  exact (limited_of_infClose_coe hq).mul_infinitesimal he

/-- **Section 8.2.** If $`f` is differentiable at the real point $`x`, then
$`{}^*f(x + \Delta x) \simeq f(x)` for every infinitesimal $`\Delta x`. -/
theorem _root_.HasDerivAt.starMap_add_infClose (h : HasDerivAt f L x)
    (he : Infinitesimal Δ) : ⋆f (x + Δ) ≊ f x :=
  h.infinitesimal_increment he

/-- **Theorem 8.2.1.** If $`f` is differentiable at the real point $`x`, then $`f` is
continuous at $`x`: for $`y \simeq x` the increment $`{}^*f(y) - f(x)` corresponding to
$`\Delta x = y - x` is infinitesimal, which is the criterion of Theorem 7.1.1. -/
theorem continuousAt_of_hasDerivAt (h : HasDerivAt f L x) : ContinuousAt f x := by
  rw [continuousAt_iff_infClose]
  intro y hy
  have := h.starMap_add_infClose (Δ := y - x) hy
  simpa using this

/-- **Theorem 8.2.1**, for Mathlib's predicate of differentiability. -/
theorem continuousAt_of_differentiableAt (h : DifferentiableAt ℝ f x) : ContinuousAt f x :=
  continuousAt_of_hasDerivAt h.hasDerivAt

/-- **Section 8.2.** The differential at a real point is infinitesimal whenever the change in
the variable is, because the derivative is a real number and hence limited. -/
theorem infinitesimal_differential (f : ℝ → ℝ) (x : ℝ) (he : Infinitesimal Δ) :
    Infinitesimal (differential f x Δ) :=
  (limited_coe _).mul_infinitesimal he

/-- **Theorem 8.2.2 (Incremental Equation).** If $`f` has derivative $`L` at the real point
$`x` and $`\Delta x` is infinitesimal, then there is an infinitesimal $`\varepsilon`,
depending on $`x` and $`\Delta x`, such that
$$`{}^*f(x + \Delta x) = f(x) + L\,\Delta x + \varepsilon\,\Delta x.`
For $`\Delta x \ne 0` the number $`\varepsilon` is the difference between the Newton quotient
and $`L`. -/
theorem _root_.HasDerivAt.incremental_equation (h : HasDerivAt f L x)
    (he : Infinitesimal Δ) :
    ∃ η : ℝ*, Infinitesimal η ∧ ⋆f (x + Δ) = f x + L * Δ + η * Δ := by
  rcases eq_or_ne Δ 0 with rfl | h0
  · exact ⟨0, infinitesimal_zero, by simp [starMap_coe]⟩
  refine ⟨(⋆f (x + Δ) - f x) / Δ - L, h.newtonQuotient_infClose he h0, ?_⟩
  field_simp
  ring

/-- **Theorem 8.2.2 (Incremental Equation)**, in the notation of increments and
differentials. If $`f` is differentiable at the real point $`x` and $`\Delta x = dx` is
infinitesimal, then $`\Delta f` and $`df` are infinitesimal and there is an infinitesimal
$`\varepsilon` with $`\Delta f = df + \varepsilon\,dx`. -/
theorem incremental_equation_differential (h : DifferentiableAt ℝ f x)
    (he : Infinitesimal Δ) :
    Infinitesimal (increment f x Δ) ∧ Infinitesimal (differential f x Δ) ∧
      ∃ η : ℝ*, Infinitesimal η ∧ increment f x Δ = differential f x Δ + η * Δ := by
  refine ⟨h.hasDerivAt.infinitesimal_increment he, infinitesimal_differential f x he, ?_⟩
  obtain ⟨η, hη, heq⟩ := h.hasDerivAt.incremental_equation he
  exact ⟨η, hη, by rw [increment_coe, differential_coe, heq]; ring⟩

/-- **Section 8.2.** The difference between the increment and the differential is
infinitesimal compared to $`\Delta x`:
$$`\frac{\Delta f - df}{\Delta x} \simeq 0.`
(For $`\Delta x = 0` the quotient is $`0` by Lean's convention on division by zero.) -/
theorem increment_sub_differential_div_infClose (h : DifferentiableAt ℝ f x)
    (he : Infinitesimal Δ) : (increment f x Δ - differential f x Δ) / Δ ≊ 0 := by
  rw [← infinitesimal_iff_infClose_zero]
  obtain ⟨-, -, η, hη, heq⟩ := incremental_equation_differential h he
  rcases eq_or_ne Δ 0 with rfl | h0
  · simp [infinitesimal_zero]
  · rw [heq, add_sub_cancel_left, mul_div_assoc, div_self h0, mul_one]
    exact hη

/-- **Theorem 8.2.2, converse.** The incremental equation characterises the derivative: if
for every infinitesimal $`\Delta x` there is an infinitesimal $`\varepsilon` with
$`{}^*f(x + \Delta x) = f(x) + L\,\Delta x + \varepsilon\,\Delta x`, then $`L` is the
derivative of $`f` at $`x`. This is not stated in the book; it shows that the incremental
equation has the full strength of Theorem 8.1.1. -/
theorem hasDerivAt_of_incremental_equation
    (h : ∀ Δ : ℝ*, Infinitesimal Δ →
      ∃ η : ℝ*, Infinitesimal η ∧ ⋆f (x + Δ) = f x + L * Δ + η * Δ) :
    HasDerivAt f L x := by
  rw [hasDerivAt_iff_infClose]
  intro e he h0
  obtain ⟨η, hη, heq⟩ := h e he
  have : (⋆f (x + e) - f x) / e - L = η := by
    rw [heq]
    field_simp
    ring
  rw [infClose_iff, this]
  exact hη

end Increments

/-!
## 8.3 Rules for Derivatives

If $`f` and $`g` are differentiable at $`x`, then so are their sum, their product and (when
$`g(x) \ne 0`) their quotient, with the familiar formulas. Each rule is proved by computing
the Newton quotient of the combined function for a nonzero infinitesimal increment
$`\Delta x` in terms of the quotients $`\Delta f/\Delta x` and $`\Delta g/\Delta x`, and
then using the arithmetic of infinite closeness from Chapter 5. For the product this is
Leibniz's own computation,
$`\Delta(fg) = (\Delta f)\,g + f\,\Delta g + \Delta f\,\Delta g`, in which the last term
contributes $`\Delta f \cdot (\Delta g/\Delta x)`, an infinitesimal times a limited number.
The book proves the product rule and leaves the other two as exercises; all three are proved
here by infinitesimal arguments, without Mathlib's rules of differentiation.
-/

section Rules

variable {f g : ℝ → ℝ} {x L M : ℝ} {e : ℝ*}

/-- **Section 8.3, rule (1) (sum rule).** If $`f` and $`g` have derivatives $`L` and $`M`
at $`x`, then $`f + g` has derivative $`L + M` at $`x`: the Newton quotient of the sum is the
sum of the Newton quotients. -/
theorem hasDerivAt_add_of_hasDerivAt (hf : HasDerivAt f L x) (hg : HasDerivAt g M x) :
    HasDerivAt (fun t => f t + g t) (L + M) x := by
  rw [hasDerivAt_iff_infClose]
  intro e he h0
  have h1 := (hf.newtonQuotient_infClose he h0).add (hg.newtonQuotient_infClose he h0)
  rw [starMap_add_apply, Hyperreal.coe_add, Hyperreal.coe_add]
  convert h1 using 1
  ring

/-- **Section 8.3, rule (2) (Leibniz's rule).** If $`f` and $`g` have derivatives $`L` and
$`M` at $`x`, then $`fg` has derivative $`L\,g(x) + f(x)\,M` at $`x`. For a nonzero
infinitesimal $`\Delta x`,
$$`\frac{\Delta(fg)}{\Delta x} = \frac{\Delta f}{\Delta x}\,g(x) + f(x)\,\frac{\Delta g}{\Delta x}
  + \Delta f\,\frac{\Delta g}{\Delta x} \simeq L\,g(x) + f(x)\,M + 0,`
because $`\Delta f \simeq 0` and all the quantities involved are limited. -/
theorem hasDerivAt_mul_of_hasDerivAt (hf : HasDerivAt f L x) (hg : HasDerivAt g M x) :
    HasDerivAt (fun t => f t * g t) (L * g x + f x * M) x := by
  rw [hasDerivAt_iff_infClose]
  intro e he h0
  have hqf := hf.newtonQuotient_infClose he h0
  have hqg := hg.newtonQuotient_infClose he h0
  have h1 : (⋆(fun t => f t * g t) (x + e) - ((f x * g x : ℝ) : ℝ*)) / e =
      (⋆f (x + e) - f x) / e * g x + f x * ((⋆g (x + e) - g x) / e) +
        (⋆f (x + e) - f x) * ((⋆g (x + e) - g x) / e) := by
    rw [starMap_mul_apply, Hyperreal.coe_mul]
    field_simp
    ring
  rw [h1]
  have h2 := hqf.mul_right (limited_coe (g x))
  have h3 := hqg.mul_left (limited_coe (f x))
  have h4 : (⋆f (x + e) - f x) * ((⋆g (x + e) - g x) / e) ≊ 0 :=
    infinitesimal_iff_infClose_zero.1
      ((hf.infinitesimal_increment he).mul_limited (limited_of_infClose_coe hqg))
  have h5 := (h2.add h3).add h4
  simpa using h5

/-- **Section 8.3, rule (3) (quotient rule).** If $`f` and $`g` have derivatives $`L` and
$`M` at $`x` and $`g(x) \ne 0`, then $`f/g` has derivative
$`(L\,g(x) - f(x)\,M)/g(x)^2` at $`x`. For a nonzero infinitesimal $`\Delta x` the value
$`g(x + \Delta x)` is infinitely close to $`g(x)` and hence appreciable, and
$$`\frac{\Delta(f/g)}{\Delta x} =
  \frac{(\Delta f/\Delta x)\,g(x) - f(x)\,(\Delta g/\Delta x)}{g(x + \Delta x)\,g(x)}.` -/
theorem hasDerivAt_div_of_hasDerivAt (hf : HasDerivAt f L x) (hg : HasDerivAt g M x)
    (hgx : g x ≠ 0) :
    HasDerivAt (fun t => f t / g t) ((L * g x - f x * M) / g x ^ 2) x := by
  rw [hasDerivAt_iff_infClose]
  intro e he h0
  have hqf := hf.newtonQuotient_infClose he h0
  have hqg := hg.newtonQuotient_infClose he h0
  have hG : ⋆g (x + e) ≊ g x := hg.starMap_add_infClose he
  have hGa : Appreciable (⋆g (x + e)) := (appreciable_coe hgx).of_infClose hG.symm
  have hG0 : ⋆g (x + e) ≠ 0 := hGa.ne_zero
  have hgx' : ((g x : ℝ) : ℝ*) ≠ 0 := by simpa using hgx
  have h1 : (⋆(fun t => f t / g t) (x + e) - ((f x / g x : ℝ) : ℝ*)) / e =
      ((⋆f (x + e) - f x) / e * g x - f x * ((⋆g (x + e) - g x) / e)) /
        (⋆g (x + e) * g x) := by
    rw [starMap_div_apply, Hyperreal.coe_div]
    field_simp
    ring
  rw [h1]
  have h2 := (hqf.mul_right (limited_coe (g x))).sub (hqg.mul_left (limited_coe (f x)))
  have h3 := hG.mul_right (limited_coe (g x))
  have hden : Appreciable (⋆g (x + e) * g x) := hGa.mul (appreciable_coe hgx)
  have hnum : Limited ((⋆f (x + e) - f x) / e * g x - f x * ((⋆g (x + e) - g x) / e)) :=
    ((limited_of_infClose_coe hqf).mul (limited_coe _)).sub
      ((limited_coe _).mul (limited_of_infClose_coe hqg))
  have h4 := h2.div h3 hnum hden.limited
    (fun h => hden.not_infinitesimal (infinitesimal_iff_infClose_zero.2 h))
  convert h4 using 1
  rw [Hyperreal.coe_div, ofReal_pow]
  push_cast
  ring

/-- **Section 8.3, non-vacuity.** The rules compute the derivative of $`t \mapsto t^2` at
$`x` from that of the identity: the identity has derivative $`1`, since its Newton quotient
is $`\varepsilon/\varepsilon = 1`, and Leibniz's rule gives $`1 \cdot x + x \cdot 1`. -/
theorem hasDerivAt_sq_infinitesimal (x : ℝ) : HasDerivAt (fun t : ℝ => t * t) (x + x) x := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := by
    rw [hasDerivAt_iff_infClose]
    intro e _ h0
    rw [starMap_id_apply, add_sub_cancel_left, div_self h0, Hyperreal.coe_one]
  simpa using hasDerivAt_mul_of_hasDerivAt hid hid

end Rules

/-!
## 8.4 Chain Rule

If $`f` is differentiable at $`x` and $`g` is differentiable at $`f(x)`, then the composite
$`g \circ f` is differentiable at $`x` with derivative $`g'(f(x))\,f'(x)`. The infinitesimal
proof rests on one observation: the increment of $`g \circ f` at $`x` corresponding to
$`\Delta x` is the increment of $`g` at $`f(x)` corresponding to $`\Delta f`. Since
$`\Delta f` is infinitesimal, the incremental equation for $`g` applies to it, and dividing
by $`\Delta x` gives the result. Unlike the classical proof by limits, no special treatment
is needed for the case in which $`\Delta f = 0`, because the incremental equation holds for
every infinitesimal change, zero included.
-/

section ChainRule

variable {f g : ℝ → ℝ} {x L M : ℝ} {e : ℝ*}

/-- **Section 8.4 (Chain Rule).** If $`f` has derivative $`L` at $`x` and $`g` has derivative
$`M` at $`f(x)`, then $`g \circ f` has derivative $`M L` at $`x`. With
$`\Delta f = {}^*f(x + \Delta x) - f(x)`, the incremental equation for $`g` at $`f(x)` gives
an infinitesimal $`\varepsilon` with
$`\Delta(g \circ f) = M\,\Delta f + \varepsilon\,\Delta f`, so that
$$`\frac{\Delta(g \circ f)}{\Delta x} = M\,\frac{\Delta f}{\Delta x} +
  \varepsilon\,\frac{\Delta f}{\Delta x} \simeq M L + 0.` -/
theorem hasDerivAt_comp_of_hasDerivAt (hf : HasDerivAt f L x) (hg : HasDerivAt g M (f x)) :
    HasDerivAt (fun t => g (f t)) (M * L) x := by
  rw [hasDerivAt_iff_infClose]
  intro e he h0
  have hqf := hf.newtonQuotient_infClose he h0
  -- the increment of `f`, which is infinitesimal
  have hΔ : Infinitesimal (⋆f (x + e) - f x) := hf.infinitesimal_increment he
  -- the increment of `g ∘ f` at `x` is the increment of `g` at `f x` corresponding to `Δf`
  obtain ⟨η, hη, heq⟩ := hg.incremental_equation hΔ
  rw [add_sub_cancel] at heq
  have h1 : (⋆(fun t => g (f t)) (x + e) - ((g (f x) : ℝ) : ℝ*)) / e =
      M * ((⋆f (x + e) - f x) / e) + η * ((⋆f (x + e) - f x) / e) := by
    rw [starMap_comp_apply, heq]
    field_simp
    ring
  rw [h1]
  have h2 := hqf.mul_left (limited_coe M)
  have h3 : η * ((⋆f (x + e) - f x) / e) ≊ 0 :=
    infinitesimal_iff_infClose_zero.1 (hη.mul_limited (limited_of_infClose_coe hqf))
  have h4 := h2.add h3
  simpa using h4

end ChainRule

/-!
## 8.5 Critical Point Theorem

If $`f` has a maximum or a minimum at a point $`x` of an open interval and is differentiable
there, then $`f'(x) = 0`. In the infinitesimal proof the inequality $`f(t) \le f(x)`
transfers to all hyperreal points of the interval, in particular to $`x + \varepsilon` and
$`x - \varepsilon` for a positive infinitesimal $`\varepsilon`. The Newton quotient with the
positive increment is then at most $`0` and the one with the negative increment is at least
$`0`; both are infinitely close to the real number $`f'(x)`, which is therefore $`0`.

The book then lists three results that follow from the critical point theorem and the extreme
value theorem of Section 7.6 with no further use of infinitesimals or limits: Rolle's theorem,
the mean value theorem, and the description of functions whose derivative is zero, positive or
negative on an interval. They are derived here in that way. The auxiliary functions that
occur (a function minus a linear function) are differentiated with Mathlib's rules, which are
the rules of Section 8.3.
-/

section CriticalPoint

variable {f : ℝ → ℝ} {f' : ℝ → ℝ} {a b x L : ℝ}

/-- **Section 8.5 (Critical Point Theorem), maximum.** If $`f(t) \le f(x)` for all $`t` in
an open interval $`(a, b)` containing $`x`, and $`f` has derivative $`L` at $`x`, then
$`L = 0`. -/
theorem eq_zero_of_hasDerivAt_of_forall_le (hx : x ∈ Ioo a b)
    (hmax : ∀ t ∈ Ioo a b, f t ≤ f x) (h : HasDerivAt f L x) : L = 0 := by
  -- transfer: `*f y ≤ f x` for every hyperreal `y` in the enlarged interval
  have hT : ∀ y ∈ ⋆(Ioo a b), ⋆f y ≤ f x := fun y hy => by
    have := starMap_le_starMap_of_mem (g := fun _ => f x) hmax hy
    rwa [starMap_const_apply] at this
  have hε : Infinitesimal (ε : ℝ*) := infinitesimal_epsilon
  have hpos : (0 : ℝ*) < ε := Hyperreal.epsilon_pos
  -- the Newton quotient with positive increment is at most zero
  have h1 : (⋆f (x + ε) - f x) / ε ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.2 (hT _ (coe_add_infinitesimal_mem_starSet_Ioo hx hε))) hpos.le
  -- the Newton quotient with negative increment is at least zero
  have h2 : 0 ≤ (⋆f (x + -ε) - f x) / -ε :=
    div_nonneg_of_nonpos
      (sub_nonpos.2 (hT _ (coe_add_infinitesimal_mem_starSet_Ioo hx hε.neg)))
      (neg_nonpos.2 hpos.le)
  have e1 := h.newtonQuotient_infClose hε hpos.ne'
  have e2 := h.newtonQuotient_infClose hε.neg (neg_ne_zero.2 hpos.ne')
  have hle : L ≤ 0 := coe_le_coe_of_infClose_le e1.symm (by simpa using h1)
  have hge : (0 : ℝ) ≤ L := coe_le_coe_of_le_infClose (by simpa using h2) e2
  exact le_antisymm hle hge

/-- **Section 8.5 (Critical Point Theorem), minimum.** If $`f(x) \le f(t)` for all $`t` in an
open interval $`(a, b)` containing $`x`, and $`f` has derivative $`L` at $`x`, then
$`L = 0`. The case of a minimum is the case of a maximum for $`-f`, whose Newton quotients
are the negatives of those of $`f`. -/
theorem eq_zero_of_hasDerivAt_of_forall_ge (hx : x ∈ Ioo a b)
    (hmin : ∀ t ∈ Ioo a b, f x ≤ f t) (h : HasDerivAt f L x) : L = 0 := by
  have hneg : HasDerivAt (fun t => -f t) (-L) x := by
    rw [hasDerivAt_iff_infClose]
    intro e he h0
    have := (h.newtonQuotient_infClose he h0).neg
    rw [starMap_neg_apply, Hyperreal.coe_neg, Hyperreal.coe_neg]
    convert this using 1
    ring
  have := eq_zero_of_hasDerivAt_of_forall_le (f := fun t => -f t) hx
    (fun t ht => neg_le_neg (hmin t ht)) hneg
  linarith

/-- **Section 8.5 (Critical Point Theorem)**, for Mathlib's notion of a local extremum: if
$`f` has a local maximum or a local minimum at $`x` and has derivative $`L` there, then
$`L = 0`. -/
theorem eq_zero_of_hasDerivAt_of_isLocalExtr (hext : IsLocalExtr f x) (h : HasDerivAt f L x) :
    L = 0 := by
  rcases hext with hmin | hmax
  · obtain ⟨a, b, hx, hab⟩ := mem_nhds_iff_exists_Ioo_subset.1 hmin
    exact eq_zero_of_hasDerivAt_of_forall_ge hx (fun t ht => by have h' := hab ht; exact h') h
  · obtain ⟨a, b, hx, hab⟩ := mem_nhds_iff_exists_Ioo_subset.1 hmax
    exact eq_zero_of_hasDerivAt_of_forall_le hx (fun t ht => by have h' := hab ht; exact h') h

/-- **Section 8.5 (Rolle's Theorem).** Let $`f` be continuous on $`[a, b]` and differentiable
on $`(a, b)`, with $`a < b`. If $`f(a) = f(b)`, then $`f'(x) = 0` for some $`x \in (a, b)`.
The book states the case $`f(a) = f(b) = 0`. By the extreme value theorem $`f` attains a
greatest and a least value on $`[a, b]`. If one of them is attained in the open interval, the
critical point theorem applies there. Otherwise both are attained at the end points, where
the values agree, so $`f` is constant and every point of the open interval is a maximum. -/
theorem exists_deriv_eq_zero_of_eq (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t) (hfab : f a = f b) :
    ∃ x ∈ Ioo a b, f' x = 0 := by
  obtain ⟨c, hc, d, hd', hcd⟩ := extreme_value_Icc hab.le hf
  have hsub : Ioo a b ⊆ Icc a b := Ioo_subset_Icc_self
  by_cases hd1 : d ∈ Ioo a b
  · exact ⟨d, hd1, eq_zero_of_hasDerivAt_of_forall_le hd1 (fun t ht => (hcd t (hsub ht)).2)
      (hd d hd1)⟩
  by_cases hc1 : c ∈ Ioo a b
  · exact ⟨c, hc1, eq_zero_of_hasDerivAt_of_forall_ge hc1 (fun t ht => (hcd t (hsub ht)).1)
      (hd c hc1)⟩
  -- both extreme values are attained at end points, so they are equal
  have hend : ∀ {u : ℝ}, u ∈ Icc a b → u ∉ Ioo a b → f u = f a := fun {u} hu hu' => by
    rcases hu.1.eq_or_lt with h | h
    · rw [h]
    · rcases hu.2.eq_or_lt with h' | h'
      · rw [h', hfab]
      · exact absurd ⟨h, h'⟩ hu'
  have hfc := hend hc hc1
  have hfd := hend hd' hd1
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  refine ⟨(a + b) / 2, hm, eq_zero_of_hasDerivAt_of_forall_le hm (fun t ht => ?_) (hd _ hm)⟩
  have h1 := hcd t (hsub ht)
  have h2 := hcd ((a + b) / 2) (hsub hm)
  linarith

/-- **Section 8.5 (Mean Value Theorem).** Let $`f` be continuous on $`[a, b]` and
differentiable on $`(a, b)`, with $`a < b`. Then for some $`x \in (a, b)`,
$$`f'(x) = \frac{f(b) - f(a)}{b - a}.`
Rolle's theorem is applied to $`f` minus the linear function with the slope of the chord. -/
theorem exists_deriv_eq_slope_of_continuousOn (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t) :
    ∃ x ∈ Ioo a b, f' x = (f b - f a) / (b - a) := by
  set s : ℝ := (f b - f a) / (b - a) with hs
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
  obtain ⟨x, hx, hx0⟩ := exists_deriv_eq_zero_of_eq (f := fun t => f t - s * (t - a))
    (f' := fun t => f' t - s) hab
    (hf.sub (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
    (fun t ht => by
      have h1 : HasDerivAt (fun y : ℝ => s * (y - a)) s t := by
        simpa using ((hasDerivAt_id t).sub_const a).const_mul s
      exact (hd t ht).fun_sub h1)
    (by simp only [sub_self, mul_zero, sub_zero]; rw [hs]; field_simp; ring)
  exact ⟨x, hx, by linarith⟩

/-- **Section 8.5 (Mean Value Theorem)**, in product form and for end points in either order:
if $`f` is differentiable at every point between $`p` and $`q` inclusive, then there is a
point $`c` between $`p` and $`q` with $`f(q) - f(p) = f'(c)\,(q - p)`. For $`p = q` one takes
$`c = p`. This is the form that is transferred in Sections 8.7 and 8.12. -/
theorem exists_sub_eq_deriv_mul_sub {p q : ℝ} (hd : ∀ t ∈ uIcc p q, HasDerivAt f (f' t) t) :
    ∃ c ∈ uIcc p q, f q - f p = f' c * (q - p) := by
  have hcont : ContinuousOn f (uIcc p q) := fun t ht =>
    (continuousAt_of_hasDerivAt (hd t ht)).continuousWithinAt
  rcases lt_trichotomy p q with h | rfl | h
  · rw [uIcc_of_le h.le] at hd hcont ⊢
    obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope_of_continuousOn h hcont
      fun t ht => hd t (Ioo_subset_Icc_self ht)
    refine ⟨c, Ioo_subset_Icc_self hc, ?_⟩
    rw [hc']
    field_simp [sub_ne_zero.2 h.ne']
  · exact ⟨p, left_mem_uIcc, by simp⟩
  · rw [uIcc_of_ge h.le] at hd hcont ⊢
    obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope_of_continuousOn h hcont
      fun t ht => hd t (Ioo_subset_Icc_self ht)
    refine ⟨c, Ioo_subset_Icc_self hc, ?_⟩
    rw [hc']
    field_simp [sub_ne_zero.2 h.ne']
    ring

/-- **Section 8.5, third consequence (zero derivative).** If $`f` is continuous on $`[a, b]`
and $`f'` is zero on $`(a, b)`, then $`f` is constant on $`[a, b]`. -/
theorem eq_of_deriv_eq_zero_on_Ioo (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f 0 t) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    f s = f t := by
  have key : ∀ {s t : ℝ}, s ∈ Icc a b → t ∈ Icc a b → s < t → f s = f t := by
    intro s t hs ht hst
    obtain ⟨c, -, hc⟩ := exists_deriv_eq_slope_of_continuousOn (f' := fun _ => 0) hst
      (hf.mono (Icc_subset_Icc hs.1 ht.2))
      fun u hu => hd u ⟨lt_of_le_of_lt hs.1 hu.1, lt_of_lt_of_le hu.2 ht.2⟩
    have h0 : f t - f s = 0 := by
      have := hc.symm
      rwa [div_eq_zero_iff, or_iff_left (sub_ne_zero.2 hst.ne')] at this
    linarith
  rcases lt_trichotomy s t with h | rfl | h
  · exact key hs ht h
  · rfl
  · exact (key ht hs h).symm

/-- **Section 8.5, third consequence (positive derivative).** If $`f` is continuous on
$`[a, b]` and $`f'` is positive on $`(a, b)`, then $`f` is strictly increasing on
$`[a, b]`. -/
theorem strictMonoOn_of_deriv_pos_on_Ioo (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t) (hpos : ∀ t ∈ Ioo a b, 0 < f' t) :
    StrictMonoOn f (Icc a b) := by
  intro s hs t ht hst
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope_of_continuousOn hst
    (hf.mono (Icc_subset_Icc hs.1 ht.2))
    fun u hu => hd u ⟨lt_of_le_of_lt hs.1 hu.1, lt_of_lt_of_le hu.2 ht.2⟩
  have h1 := hpos c ⟨lt_of_le_of_lt hs.1 hc.1, lt_of_lt_of_le hc.2 ht.2⟩
  rw [hc', div_pos_iff_of_pos_right (sub_pos.2 hst)] at h1
  linarith

/-- **Section 8.5, third consequence (negative derivative).** If $`f` is continuous on
$`[a, b]` and $`f'` is negative on $`(a, b)`, then $`f` is strictly decreasing on
$`[a, b]`. -/
theorem strictAntiOn_of_deriv_neg_on_Ioo (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t) (hneg : ∀ t ∈ Ioo a b, f' t < 0) :
    StrictAntiOn f (Icc a b) := by
  intro s hs t ht hst
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope_of_continuousOn hst
    (hf.mono (Icc_subset_Icc hs.1 ht.2))
    fun u hu => hd u ⟨lt_of_le_of_lt hs.1 hu.1, lt_of_lt_of_le hu.2 ht.2⟩
  have h1 := hneg c ⟨lt_of_le_of_lt hs.1 hc.1, lt_of_lt_of_le hc.2 ht.2⟩
  rw [hc', div_neg_iff] at h1
  rcases h1 with ⟨_, h⟩ | ⟨h, _⟩
  · linarith
  · linarith

end CriticalPoint

/-!
## 8.6 Inverse Function Theorem

Let $`f` be continuous and strictly monotone on an open interval $`(a, b)`, and let $`g` be
its inverse function. If $`f` is differentiable at a point $`x` of the interval with
$`f'(x) \ne 0`, then $`g` is differentiable at $`y = f(x)` and $`g'(y) = 1/f'(x)`. One cannot
simply differentiate the identity $`g(f(x)) = x` by the chain rule, since the
differentiability of $`g` is the thing to be proved.

The infinitesimal proof takes a nonzero infinitesimal $`\Delta y` and shows first that
$`\Delta x = g(y + \Delta y) - g(y)` is infinitesimal: otherwise a real number $`r` would lie
strictly between $`g(y + \Delta y)` and $`x`, and by monotonicity the real number $`f(r)`
would lie strictly between $`y + \Delta y` and $`y`, which are infinitely close. Then
$`\Delta y` is the increment of $`f` at $`x` corresponding to $`\Delta x`, so the Newton
quotient of $`g` is the reciprocal of a Newton quotient of $`f`, and the reciprocal of a
hyperreal infinitely close to the nonzero real $`f'(x)` is infinitely close to $`1/f'(x)`.

In the formalization the inverse is a total function $`g` with $`g(f(t)) = t` for all $`t` in
$`(a, b)`. The intermediate value theorem of Section 7.5 shows that the values of $`f` fill a
real open interval around $`y`, so that $`g` is determined near $`y` by this condition.
-/

section InverseFunction

variable {f g : ℝ → ℝ} {a b x L : ℝ}

/-- **Section 8.6, first step.** Let $`f` be continuous and strictly increasing on $`(a, b)`
with left inverse $`g`, and let $`a < x_1 < x_2 < b`. Then every real $`t` strictly between
$`f(x_1)` and $`f(x_2)` is a value of $`f` on $`(x_1, x_2)`; hence $`g(t)` lies in
$`(x_1, x_2)` and $`f(g(t)) = t`. This is the book's remark that $`g` is defined on a real
open interval around $`y`, by the intermediate value theorem. -/
theorem inverse_mem_Ioo_of_strictMonoOn (hf : ContinuousOn f (Ioo a b))
    (hg : ∀ t ∈ Ioo a b, g (f t) = t) {x₁ x₂ : ℝ} (h1 : a < x₁) (h12 : x₁ ≤ x₂) (h2 : x₂ < b)
    {t : ℝ} (ht : t ∈ Ioo (f x₁) (f x₂)) : g t ∈ Ioo x₁ x₂ ∧ f (g t) = t := by
  have hsub : Icc x₁ x₂ ⊆ Ioo a b := fun u hu =>
    ⟨lt_of_lt_of_le h1 hu.1, lt_of_le_of_lt hu.2 h2⟩
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc h12 (hf.mono hsub) (Or.inl ht)
  have hgs : g t = s := by rw [← hfs, hg s (hsub (Ioo_subset_Icc_self hs))]
  rw [hgs]
  exact ⟨hs, hfs⟩

/-- **Section 8.6 (Inverse Function Theorem), increasing case.** Let $`f` be continuous and
strictly increasing on $`(a, b)`, and let $`g` satisfy $`g(f(t)) = t` for all $`t` in
$`(a, b)`. If $`f` has derivative $`L \ne 0` at a point $`x` of $`(a, b)`, then $`g` has
derivative $`1/L` at $`f(x)`. -/
theorem hasDerivAt_inverse_of_strictMonoOn (hf : ContinuousOn f (Ioo a b))
    (hmono : StrictMonoOn f (Ioo a b)) (hg : ∀ t ∈ Ioo a b, g (f t) = t) (hx : x ∈ Ioo a b)
    (hL : HasDerivAt f L x) (hL0 : L ≠ 0) : HasDerivAt g (1 / L) (f x) := by
  -- a closed subinterval `[x₁, x₂]` of `(a, b)` with `x` in its interior
  set x₁ : ℝ := (a + x) / 2 with hx₁
  set x₂ : ℝ := (x + b) / 2 with hx₂
  have ha1 : a < x₁ := by rw [hx₁]; linarith [hx.1]
  have h1x : x₁ < x := by rw [hx₁]; linarith [hx.1]
  have hx2 : x < x₂ := by rw [hx₂]; linarith [hx.2]
  have h2b : x₂ < b := by rw [hx₂]; linarith [hx.2]
  have hm1 : x₁ ∈ Ioo a b := ⟨ha1, by linarith⟩
  have hm2 : x₂ ∈ Ioo a b := ⟨by linarith, h2b⟩
  have hy : f x ∈ Ioo (f x₁) (f x₂) := ⟨hmono hm1 hx h1x, hmono hx hm2 hx2⟩
  have hstd := fun t (ht : t ∈ Ioo (f x₁) (f x₂)) =>
    inverse_mem_Ioo_of_strictMonoOn hf hg ha1 (by linarith) h2b ht
  rw [hasDerivAt_iff_infClose]
  intro Δy hΔy hΔy0
  rw [hg x hx]
  -- transfer: `u = *g (y + Δy)` lies in the enlarged interval and `*f u = y + Δy`
  have hmem : (f x : ℝ*) + Δy ∈ ⋆(Ioo (f x₁) (f x₂)) :=
    coe_add_infinitesimal_mem_starSet_Ioo hy hΔy
  set u : ℝ* := ⋆g ((f x : ℝ*) + Δy) with hu
  have hu12 : u ∈ ⋆(Ioo x₁ x₂) :=
    starMap_mem_starSet (fun t ht => (hstd t ht).1) hmem
  have hfu : ⋆f u = (f x : ℝ*) + Δy := by
    have := starMap_congr_of_mem (f := fun t => f (g t)) (g := fun t => t)
      (fun t ht => (hstd t ht).2) hmem
    rwa [starMap_comp_apply, starMap_id_apply] at this
  rw [starSet_Ioo_real] at hu12
  have huIcc : u ∈ Icc (x₁ : ℝ*) x₂ := ⟨hu12.1.le, hu12.2.le⟩
  have hulim : Limited u := limited_of_mem_Icc huIcc
  have hsh := sh_mem_Icc huIcc
  have huab : u ∈ ⋆(Ioo a b) := by
    rw [starSet_Ioo_real]
    exact ⟨lt_trans (Hyperreal.coe_lt_coe.2 ha1) hu12.1,
      lt_trans hu12.2 (Hyperreal.coe_lt_coe.2 h2b)⟩
  -- `u` is infinitely close to `x`: otherwise a real `r` separates them
  have hsx : sh u = x := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `sh u < r < x`, so `u < r`, hence `y + Δy < f r < y`
      set r : ℝ := (sh u + x) / 2 with hr
      have hr1 : sh u < r := by rw [hr]; linarith
      have hr2 : r < x := by rw [hr]; linarith
      have hrab : r ∈ Ioo a b := ⟨by linarith [hsh.1], by linarith [hx.2]⟩
      have h1 := starMap_lt_coe_of_strictMonoOn hmono hrab huab (hulim.lt_of_sh_lt hr1)
      have h2 : f r < f x := hmono hrab hx hr2
      rw [hfu] at h1
      have h3 := infinitesimal_iff_abs_lt.1 hΔy (f x - f r) (sub_pos.2 h2)
      have h4 := (abs_lt.1 h3).1
      rw [Hyperreal.coe_sub] at h4
      linarith
    · set r : ℝ := (sh u + x) / 2 with hr
      have hr1 : r < sh u := by rw [hr]; linarith
      have hr2 : x < r := by rw [hr]; linarith
      have hrab : r ∈ Ioo a b := ⟨by linarith [hx.1], by linarith [hsh.2]⟩
      have h1 := coe_lt_starMap_of_strictMonoOn hmono hrab huab (hulim.lt_of_lt_sh hr1)
      have h2 : f x < f r := hmono hx hrab hr2
      rw [hfu] at h1
      have h3 := infinitesimal_iff_abs_lt.1 hΔy (f r - f x) (sub_pos.2 h2)
      have h4 := (abs_lt.1 h3).2
      rw [Hyperreal.coe_sub] at h4
      linarith
  have hux : u ≊ x := hsx ▸ hulim.infClose_sh
  -- the increment `Δx` of `g` is a nonzero infinitesimal
  have hΔx : Infinitesimal (u - x) := hux
  have hΔx0 : u - x ≠ 0 := by
    intro h0
    rw [sub_eq_zero.1 h0, starMap_coe] at hfu
    exact hΔy0 (by simpa using hfu.symm)
  -- `Δy` is the increment of `f` at `x` corresponding to `Δx`
  have hq := hL.newtonQuotient_infClose hΔx hΔx0
  rw [add_sub_cancel, hfu, add_sub_cancel_left] at hq
  have hqa : Appreciable (Δy / (u - x)) := (appreciable_coe hL0).of_infClose hq.symm
  have hinv := hq.inv hqa
  rw [inv_div] at hinv
  simpa [one_div] using hinv

/-- **Section 8.6 (Inverse Function Theorem), decreasing case.** The same statement for a
function that is strictly decreasing on $`(a, b)`. It is reduced to the increasing case by
replacing $`f` with $`-f` and $`g` with $`s \mapsto g(-s)`, and undoing the change of sign
with the chain rule of Section 8.4. -/
theorem hasDerivAt_inverse_of_strictAntiOn (hf : ContinuousOn f (Ioo a b))
    (hanti : StrictAntiOn f (Ioo a b)) (hg : ∀ t ∈ Ioo a b, g (f t) = t) (hx : x ∈ Ioo a b)
    (hL : HasDerivAt f L x) (hL0 : L ≠ 0) : HasDerivAt g (1 / L) (f x) := by
  have hnegL : HasDerivAt (fun t => -f t) (-L) x := by
    rw [hasDerivAt_iff_infClose]
    intro e he h0
    have := (hL.newtonQuotient_infClose he h0).neg
    rw [starMap_neg_apply, Hyperreal.coe_neg, Hyperreal.coe_neg]
    convert this using 1
    ring
  have h1 := hasDerivAt_inverse_of_strictMonoOn (f := fun t => -f t) (g := fun s => g (-s))
    hf.neg (fun s hs t ht hst => neg_lt_neg (hanti hs ht hst))
    (fun t ht => by simpa using hg t ht) hx hnegL (neg_ne_zero.2 hL0)
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) (f x) := by
    rw [hasDerivAt_iff_infClose]
    intro e _ h0
    have : (⋆(fun s : ℝ => -s) ((f x : ℝ*) + e) - ((-f x : ℝ) : ℝ*)) / e = ((-1 : ℝ) : ℝ*) := by
      rw [starMap_neg_apply, starMap_id_apply, Hyperreal.coe_neg, Hyperreal.coe_neg,
        Hyperreal.coe_one]
      field_simp
      ring
    rw [this]
  have h2 := hasDerivAt_comp_of_hasDerivAt (g := fun s => g (-s)) hneg h1
  have h3 : (fun t : ℝ => g (- -t)) = g := funext fun t => by rw [neg_neg]
  rw [h3] at h2
  convert h2 using 1
  field_simp

/-- **Section 8.6 (Inverse Function Theorem).** Let $`f` be continuous and strictly monotone
(increasing or decreasing) on $`(a, b)`, and let $`g` be the inverse function of $`f`, in the
sense that $`g(f(t)) = t` for all $`t` in $`(a, b)`. If $`f` is differentiable at $`x` in
$`(a, b)` with $`f'(x) = L \ne 0`, then $`g` is differentiable at $`y = f(x)`, with
$`g'(y) = 1/L`. -/
theorem hasDerivAt_inverse (hf : ContinuousOn f (Ioo a b))
    (hmono : StrictMonoOn f (Ioo a b) ∨ StrictAntiOn f (Ioo a b))
    (hg : ∀ t ∈ Ioo a b, g (f t) = t) (hx : x ∈ Ioo a b)
    (hL : HasDerivAt f L x) (hL0 : L ≠ 0) : HasDerivAt g (1 / L) (f x) :=
  hmono.elim (fun h => hasDerivAt_inverse_of_strictMonoOn hf h hg hx hL hL0)
    fun h => hasDerivAt_inverse_of_strictAntiOn hf h hg hx hL hL0

/-- **Section 8.6, the hypothesis on the derivative is essential.** The cube function is
continuous and strictly increasing with inverse the cube root, but the inverse is not
differentiable at $`0`, where the derivative of the cube vanishes: for a positive
infinitesimal $`\varepsilon` the Newton quotient of the inverse at $`0` with increment
$`\varepsilon^3` is $`\varepsilon/\varepsilon^3 = 1/\varepsilon^2`, which is unlimited. -/
theorem not_differentiableAt_inverse_cube {g : ℝ → ℝ} (hg : ∀ t : ℝ, g (t ^ 3) = t) :
    ¬ DifferentiableAt ℝ g 0 := by
  intro h
  have he3 : Infinitesimal ((ε : ℝ*) ^ 3) := infinitesimal_epsilon.pow (by norm_num)
  have hε0 : (ε : ℝ*) ≠ 0 := Hyperreal.epsilon_ne_zero
  have hq := h.hasDerivAt.newtonQuotient_infClose he3 (pow_ne_zero 3 hε0)
  -- transfer of `g (t ^ 3) = t`
  have hT : ⋆g ((ε : ℝ*) ^ 3) = ε := by
    have := starMap_congr_of_mem (f := fun t : ℝ => g (t ^ 3)) (g := fun t => t) (A := univ)
      (fun t _ => hg t) (x := (ε : ℝ*)) (by rw [starSet_univ]; exact mem_univ _)
    rwa [starMap_comp_apply, starMap_pow_apply, starMap_id_apply] at this
  have hg0 : g 0 = 0 := by simpa using hg 0
  rw [Hyperreal.coe_zero, zero_add, hT, hg0, Hyperreal.coe_zero, sub_zero] at hq
  have hlim := limited_of_infClose_coe hq
  have hunl : Unlimited ((ε : ℝ*) / ε ^ 3) := by
    have h1 : (ε : ℝ*) / ε ^ 3 = (ε ^ 2)⁻¹ := by
      field_simp
    rw [h1]
    exact (infinitesimal_epsilon.pow two_ne_zero).inv_unlimited (pow_ne_zero 2 hε0)
  exact hlim.not_unlimited hunl

end InverseFunction

end Goldblatt
