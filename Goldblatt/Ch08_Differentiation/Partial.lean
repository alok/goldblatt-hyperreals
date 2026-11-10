import Goldblatt.Ch08_Differentiation.Derivative

/-!
# 8 (part 2). Partial Derivatives: Sections 8.7 and 8.8

This is the second of four parts of Chapter 8 (the overview is on the chapter page
{lit}`Goldblatt.Ch08_Differentiation`). It treats real functions of two variables: infinite
closeness in the hyperreal plane, continuity at a real point of the plane, smoothness, the
increment and the total differential, and the incremental equation for two variables (Theorem
8.7.1), whose proof transfers the mean value theorem to a hyperreal slice of the function.
The two exercises of Section 8.8 follow.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## 8.7 Partial Derivatives

A real function of two variables is a function {lit}`f : ℝ → ℝ → ℝ`; its extension takes two
hyperreal arguments. The partial derivative of $`f` with respect to the first variable at
$`(a, b)` is the derivative at $`a` of the function $`x \mapsto f(x, b)`, and similarly for
the second variable, so Theorem 8.1.1 describes both by Newton quotients with a nonzero
infinitesimal increment in one variable.

Two points of the hyperreal plane are infinitely close when their coordinates are, which is
the same as their Euclidean distance being infinitesimal. A function is continuous at a real
point $`(a, b)` when its extension maps the points infinitely close to $`(a, b)` to hyperreals
infinitely close to $`f(a, b)`; this is the two-variable form of Theorem 7.1.1 and is proved
here to be equivalent to Mathlib's continuity of the uncurried function on the plane. The
function is _smooth_ at $`(a, b)` if both partial derivatives exist near $`(a, b)` and are
continuous at $`(a, b)`.

The increment of $`f` at $`(a, b)` corresponding to changes $`\Delta x, \Delta y` is
$`\Delta f = f(a + \Delta x, b + \Delta y) - f(a, b)`, the change in height along the graph,
and the total differential $`df = f_x(a, b)\,\Delta x + f_y(a, b)\,\Delta y` is the change
along the tangent plane. Theorem 8.7.1 says that for a smooth function they differ by
$`\varepsilon\,\Delta x + \delta\,\Delta y` with $`\varepsilon, \delta` infinitesimal.

The proof splits the increment into a change in $`x` at height $`b` followed by a change in
$`y` at abscissa $`a + \Delta x`. The first is handled by the one-variable incremental
equation. The second is an increment of the function $`y \mapsto f(a + \Delta x, y)`, which
is not a real function, so that equation does not apply. Instead the mean value theorem for
the real functions $`y \mapsto f(a + x_0, y)` is transferred: it yields a hyperreal $`c`
between $`b` and $`b + \Delta y` at which the second change equals
$`f_y(a + \Delta x, c)\,\Delta y`, and continuity of $`f_y` at $`(a, b)` finishes the proof.
In the ultrapower the transfer is carried out on representatives: for almost all indices $`n`
the mean value theorem provides a real $`c_n`, and $`c` is the class of the sequence
$`(c_n)`.
-/

section Plane

variable {x₁ y₁ x₂ y₂ : ℝ*}

/-- **Section 8.7, infinite closeness in the plane.** Two points $`(x_1, y_1)` and
$`(x_2, y_2)` of the hyperreal plane have infinitely close coordinates,
$`x_1 \simeq x_2` and $`y_1 \simeq y_2`, if and only if their Euclidean distance
$`\sqrt{(x_1 - x_2)^2 + (y_1 - y_2)^2}` is infinitesimal. -/
theorem infinitesimal_hsqrt_dist_iff :
    Infinitesimal (hsqrt ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2)) ↔ x₁ ≊ x₂ ∧ y₁ ≊ y₂ := by
  have hz : 0 ≤ (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 := by positivity
  have hsq := hsqrt_sq hz
  constructor
  · intro h
    have h2 : Infinitesimal ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) := hsq ▸ h.pow two_ne_zero
    constructor
    · refine infinitesimal_of_pow (n := 2) (h2.of_abs_le ?_) two_ne_zero
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hz]
      nlinarith [sq_nonneg (y₁ - y₂)]
    · refine infinitesimal_of_pow (n := 2) (h2.of_abs_le ?_) two_ne_zero
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hz]
      nlinarith [sq_nonneg (x₁ - x₂)]
  · rintro ⟨h1, h2⟩
    refine infinitesimal_of_pow (n := 2) ?_ two_ne_zero
    rw [hsq]
    exact (Infinitesimal.pow h1 two_ne_zero).add (Infinitesimal.pow h2 two_ne_zero)

end Plane

section TwoVariables

variable {f fx fy : ℝ → ℝ → ℝ} {a b : ℝ} {x y Δx Δy : ℝ*}

/-- **Chapter 8, transfer tool.** A function between spaces, the first with a countably
generated filter, converges along that filter if and only if it converges along the index
ultrafilter on every sequence that converges along the index ultrafilter. This is the
ultrapower form of "limits by transfer" from Chapter 7, stated for sequences so that it can be
used for functions on the plane. -/
theorem tendsto_iff_forall_seq_hyperfilter {α β : Type*} {l : Filter α}
    [l.IsCountablyGenerated] {l' : Filter β} {F : α → β} :
    Tendsto F l l' ↔
      ∀ p : ℕ → α, Tendsto p (hyperfilter ℕ) l → Tendsto (F ∘ p) (hyperfilter ℕ) l' := by
  constructor
  · exact fun h p hp => h.comp hp
  · intro h
    by_contra hne
    obtain ⟨S, hS, hne⟩ : ∃ S ∈ l', F ⁻¹' S ∉ l := by
      simpa [tendsto_def] using hne
    obtain ⟨B, hB⟩ := l.exists_antitone_basis
    have hex : ∀ n, ∃ a ∈ B n, F a ∉ S := fun n => by
      by_contra hcon
      push Not at hcon
      exact hne (mem_of_superset (hB.mem n) hcon)
    choose r hrB hrS using hex
    have hr : Tendsto r (hyperfilter ℕ) l :=
      (hB.tendsto hrB).mono_left Nat.hyperfilter_le_atTop
    obtain ⟨n, hn⟩ := ((h r hr).eventually_mem hS).exists
    exact hrS n hn

/-- **Section 8.7, continuity in two variables.** A real function $`f` of two variables is
continuous at the real point $`(a, b)` if and only if $`{}^*f(x, y) \simeq f(a, b)` for all
hyperreals $`x \simeq a` and $`y \simeq b`. The left side is Mathlib's continuity of $`f` as
a function on the plane; the right side is the book's definition. -/
theorem continuousAt_uncurry_iff_infClose :
    ContinuousAt (Function.uncurry f) (a, b) ↔
      ∀ x y : ℝ*, x ≊ a → y ≊ b → ⋆f x y ≊ f a b := by
  rw [ContinuousAt, tendsto_iff_forall_seq_hyperfilter]
  constructor
  · intro h x y hx hy
    obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
    obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
    rw [ofSeq_infClose_coe_iff] at hx hy
    have := h (fun n => (r n, s n)) (hx.prodMk_nhds hy)
    exact ofSeq_infClose_coe_iff.2 this
  · intro h p hp
    have h1 : Tendsto (fun n => (p n).1) (hyperfilter ℕ) (𝓝 a) :=
      (continuous_fst.tendsto (a, b)).comp hp
    have h2 : Tendsto (fun n => (p n).2) (hyperfilter ℕ) (𝓝 b) :=
      (continuous_snd.tendsto (a, b)).comp hp
    have := h (Hyperreal.ofSeq fun n => (p n).1) (Hyperreal.ofSeq fun n => (p n).2)
      (ofSeq_infClose_coe_iff.2 h1) (ofSeq_infClose_coe_iff.2 h2)
    exact ofSeq_infClose_coe_iff.1 this

/-- **Chapter 8, transfer tool.** Fixing the second argument of the extension at a real
number $`b` gives the extension of the real function $`x \mapsto f(x, b)`. -/
theorem starMap₂_coe_right (f : ℝ → ℝ → ℝ) (x : ℝ*) (b : ℝ) :
    ⋆f x (b : ℝ*) = ⋆(fun t => f t b) x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- **Chapter 8, transfer tool.** Fixing the first argument of the extension at a real
number $`a` gives the extension of the real function $`y \mapsto f(a, y)`. -/
theorem starMap₂_coe_left (f : ℝ → ℝ → ℝ) (a : ℝ) (y : ℝ*) :
    ⋆f (a : ℝ*) y = ⋆(fun t => f a t) y := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep y
  rfl

/-- **Section 8.7, partial derivative in the first variable.** If $`L` is the partial
derivative of $`f` with respect to $`x` at $`(a, b)`, then for every nonzero infinitesimal
$`\Delta x`,
$$`L \simeq \frac{{}^*f(a + \Delta x, b) - f(a, b)}{\Delta x},`
and conversely. -/
theorem hasDerivAt_partial_fst_iff_infClose {L : ℝ} :
    HasDerivAt (fun x => f x b) L a ↔
      ∀ e : ℝ*, Infinitesimal e → e ≠ 0 → (⋆f (a + e) b - f a b) / e ≊ L := by
  rw [hasDerivAt_iff_infClose]
  simp only [starMap₂_coe_right]

/-- **Section 8.7, partial derivative in the second variable.** If $`L` is the partial
derivative of $`f` with respect to $`y` at $`(a, b)`, then for every nonzero infinitesimal
$`\Delta y`,
$$`L \simeq \frac{{}^*f(a, b + \Delta y) - f(a, b)}{\Delta y},`
and conversely. -/
theorem hasDerivAt_partial_snd_iff_infClose {L : ℝ} :
    HasDerivAt (fun y => f a y) L b ↔
      ∀ e : ℝ*, Infinitesimal e → e ≠ 0 → (⋆f a (b + e) - f a b) / e ≊ L := by
  rw [hasDerivAt_iff_infClose]
  simp only [starMap₂_coe_left]

/-- **Section 8.7, smoothness.** The function $`f` of two variables is _smooth_ at the real
point $`(a, b)`, with partial derivative functions $`f_x` and $`f_y`, if at every point of
some neighbourhood of $`(a, b)` the function $`f_x` gives the derivative of $`f` in the first
variable and $`f_y` gives the derivative of $`f` in the second variable, and $`f_x` and
$`f_y` are continuous at $`(a, b)`. The book says that the partial derivatives "exist and are
continuous at $`(a, b)`"; for continuity at the point to make sense they must exist on an
open disk about it, and this is made explicit here. -/
structure SmoothAt (f fx fy : ℝ → ℝ → ℝ) (a b : ℝ) : Prop where
  /-- Near $`(a, b)`, $`f_x` is the partial derivative of $`f` in the first variable. -/
  hasDerivAt_fst : ∀ᶠ p : ℝ × ℝ in 𝓝 (a, b), HasDerivAt (fun x => f x p.2) (fx p.1 p.2) p.1
  /-- Near $`(a, b)`, $`f_y` is the partial derivative of $`f` in the second variable. -/
  hasDerivAt_snd : ∀ᶠ p : ℝ × ℝ in 𝓝 (a, b), HasDerivAt (fun y => f p.1 y) (fy p.1 p.2) p.2
  /-- $`f_x` is continuous at $`(a, b)`. -/
  continuousAt_fst : ContinuousAt (Function.uncurry fx) (a, b)
  /-- $`f_y` is continuous at $`(a, b)`. -/
  continuousAt_snd : ContinuousAt (Function.uncurry fy) (a, b)

/-- **Section 8.7, non-vacuity.** The product function $`f(x, y) = xy` is smooth at every
point, with $`f_x(x, y) = y` and $`f_y(x, y) = x`. -/
theorem smoothAt_mul (a b : ℝ) :
    SmoothAt (fun x y => x * y) (fun _ y => y) (fun x _ => x) a b where
  hasDerivAt_fst := Eventually.of_forall fun p => by
    simpa using (hasDerivAt_id p.1).mul_const p.2
  hasDerivAt_snd := Eventually.of_forall fun p => by
    simpa using (hasDerivAt_id p.2).const_mul p.1
  continuousAt_fst := continuous_snd.continuousAt
  continuousAt_snd := continuous_fst.continuousAt

/-- **Section 8.7, increment.** The increment
$`\Delta f = {}^*f(x + \Delta x, y + \Delta y) - {}^*f(x, y)` of a function of two variables
at the point $`(x, y)` corresponding to the changes $`\Delta x, \Delta y`. -/
def increment₂ (f : ℝ → ℝ → ℝ) (x y Δx Δy : ℝ*) : ℝ* := ⋆f (x + Δx) (y + Δy) - ⋆f x y

/-- **Section 8.7, total differential.** The total differential
$`df = f_x(a, b)\,\Delta x + f_y(a, b)\,\Delta y` at the real point $`(a, b)`, given the
partial derivative functions. It is the change in height along the tangent plane. -/
def totalDifferential (fx fy : ℝ → ℝ → ℝ) (a b : ℝ) (Δx Δy : ℝ*) : ℝ* :=
  (fx a b : ℝ) * Δx + (fy a b : ℝ) * Δy

/-- **Section 8.7.** At a real point the increment is
$`{}^*f(a + \Delta x, b + \Delta y) - f(a, b)`. -/
theorem increment₂_coe (f : ℝ → ℝ → ℝ) (a b : ℝ) (Δx Δy : ℝ*) :
    increment₂ f a b Δx Δy = ⋆f (a + Δx) (b + Δy) - f a b := rfl

/-- **Theorem 8.7.1, equation (iv): the transferred mean value theorem.** Suppose that
$`f_y` is the partial derivative of $`f` in the second variable at all points of a
neighbourhood of the real point $`(a, b)`. Then for all infinitesimals $`\Delta x` and
$`\Delta y` there is a hyperreal $`c \simeq b` with
$$`{}^*f(a + \Delta x, b + \Delta y) - {}^*f(a + \Delta x, b) =
  {}^*f_y(a + \Delta x, c)\,\Delta y.`
For real $`x_0, y_0` small enough, the mean value theorem of Section 8.5 applied to
$`y \mapsto f(a + x_0, y)` gives a real $`c_0` between $`b` and $`b + y_0` with
$`f(a + x_0, b + y_0) - f(a + x_0, b) = f_y(a + x_0, c_0)\,y_0`. Applying this to the terms of
sequences representing $`\Delta x` and $`\Delta y` produces the sequence representing
$`c`. -/
theorem exists_infClose_partial_snd_increment
    (h : ∀ᶠ p : ℝ × ℝ in 𝓝 (a, b), HasDerivAt (fun y => f p.1 y) (fy p.1 p.2) p.2)
    (hx : Infinitesimal Δx) (hy : Infinitesimal Δy) :
    ∃ c : ℝ*, c ≊ b ∧ ⋆f (a + Δx) (b + Δy) - ⋆f (a + Δx) b = ⋆fy (a + Δx) c * Δy := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 h
  obtain ⟨u, rfl⟩ := hyperreal_exists_rep Δx
  obtain ⟨v, rfl⟩ := hyperreal_exists_rep Δy
  -- almost all terms of the two sequences are smaller than the radius
  have hu : ∀ᶠ n in hyperfilter ℕ, |u n| < ρ := by
    have := infinitesimal_iff_abs_lt.1 hx ρ hρ
    rwa [abs_ofSeq, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff] at this
  have hv : ∀ᶠ n in hyperfilter ℕ, |v n| < ρ := by
    have := infinitesimal_iff_abs_lt.1 hy ρ hρ
    rwa [abs_ofSeq, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff] at this
  -- the standard mean value theorem on the slice through `a + u n`
  have hstd : ∀ n, ∃ c : ℝ, |u n| < ρ → |v n| < ρ →
      |c - b| ≤ |v n| ∧ f (a + u n) (b + v n) - f (a + u n) b = fy (a + u n) c * v n := by
    intro n
    by_cases hn : |u n| < ρ ∧ |v n| < ρ
    · have hsub : ∀ t ∈ uIcc b (b + v n), |t - b| ≤ |v n| := fun t ht => by
        have := abs_sub_left_of_mem_uIcc ht
        simpa using this
      obtain ⟨c, hc, hc'⟩ := exists_sub_eq_deriv_mul_sub (f := fun y => f (a + u n) y)
        (f' := fun t => fy (a + u n) t) (p := b) (q := b + v n) fun t ht => by
          refine hball (y := (a + u n, t)) ?_
          rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
          exact ⟨by simpa using hn.1, lt_of_le_of_lt (hsub t ht) hn.2⟩
      exact ⟨c, fun _ _ => ⟨hsub c hc, by simpa using hc'⟩⟩
    · exact ⟨b, fun h1 h2 => absurd ⟨h1, h2⟩ hn⟩
  choose c hc using hstd
  refine ⟨Hyperreal.ofSeq c, ?_, ?_⟩
  · -- `c` lies between `b` and `b + Δy`
    refine hy.of_abs_le ?_
    have : |Hyperreal.ofSeq c - (b : ℝ*)| = Hyperreal.ofSeq fun n => |c n - b| := by
      rw [← abs_ofSeq]
      rfl
    rw [this, abs_ofSeq, ofSeq_le_ofSeq_iff]
    filter_upwards [hu, hv] with n h1 h2 using (hc n h1 h2).1
  · have key : (Hyperreal.ofSeq fun n => f (a + u n) (b + v n) - f (a + u n) b) =
        Hyperreal.ofSeq fun n => fy (a + u n) (c n) * v n := by
      rw [ofSeq_eq_ofSeq_iff]
      filter_upwards [hu, hv] with n h1 h2 using (hc n h1 h2).2
    exact key

/-- **Theorem 8.7.1 (Incremental Equation for Two Variables).** Near a real point $`(a, b)`
of smoothness, the increment of $`f` is the total differential up to an error that is
infinitely small compared with the increments of the variables: for any two infinitesimals
$`\Delta x` and $`\Delta y` there are infinitesimals $`\varepsilon` and $`\delta` with
$$`{}^*f(a + \Delta x, b + \Delta y) - f(a, b) =
  f_x(a, b)\,\Delta x + f_y(a, b)\,\Delta y + \varepsilon\,\Delta x + \delta\,\Delta y.` -/
theorem SmoothAt.incremental_equation (h : SmoothAt f fx fy a b) (hx : Infinitesimal Δx)
    (hy : Infinitesimal Δy) :
    ∃ η δ : ℝ*, Infinitesimal η ∧ Infinitesimal δ ∧
      ⋆f (a + Δx) (b + Δy) - f a b = fx a b * Δx + fy a b * Δy + η * Δx + δ * Δy := by
  -- (iii): the change in `x` at height `b`, by the one-variable incremental equation
  obtain ⟨η, hη, h3⟩ := (h.hasDerivAt_fst.self_of_nhds).incremental_equation hx
  rw [← starMap₂_coe_right] at h3
  -- (iv): the change in `y` at abscissa `a + Δx`, by the transferred mean value theorem
  obtain ⟨c, hc, h4⟩ := exists_infClose_partial_snd_increment h.hasDerivAt_snd hx hy
  have hxa : (a : ℝ*) + Δx ≊ a := by rw [infClose_iff]; simpa using hx
  have hδ : Infinitesimal (⋆fy (a + Δx) c - fy a b) :=
    continuousAt_uncurry_iff_infClose.1 h.continuousAt_snd _ _ hxa hc
  refine ⟨η, ⋆fy (a + Δx) c - fy a b, hη, hδ, ?_⟩
  linear_combination h4 + h3

/-- **Theorem 8.7.1 (Incremental Equation for Two Variables)**, in the notation of
increments and differentials: $`\Delta f = df + \varepsilon\,\Delta x + \delta\,\Delta y`
for some infinitesimals $`\varepsilon` and $`\delta`. -/
theorem SmoothAt.increment₂_eq (h : SmoothAt f fx fy a b) (hx : Infinitesimal Δx)
    (hy : Infinitesimal Δy) :
    ∃ η δ : ℝ*, Infinitesimal η ∧ Infinitesimal δ ∧
      increment₂ f a b Δx Δy = totalDifferential fx fy a b Δx Δy + η * Δx + δ * Δy := by
  obtain ⟨η, δ, hη, hδ, heq⟩ := h.incremental_equation hx hy
  exact ⟨η, δ, hη, hδ, by rw [increment₂_coe, totalDifferential, heq]⟩

/-- **Section 8.7.** For a smooth function the increment and the total differential are both
infinitesimal when the changes in the variables are. -/
theorem SmoothAt.infinitesimal_increment₂ (h : SmoothAt f fx fy a b) (hx : Infinitesimal Δx)
    (hy : Infinitesimal Δy) :
    Infinitesimal (increment₂ f a b Δx Δy) ∧
      Infinitesimal (totalDifferential fx fy a b Δx Δy) := by
  have hd : Infinitesimal (totalDifferential fx fy a b Δx Δy) :=
    ((limited_coe _).mul_infinitesimal hx).add ((limited_coe _).mul_infinitesimal hy)
  obtain ⟨η, δ, hη, hδ, heq⟩ := h.increment₂_eq hx hy
  refine ⟨?_, hd⟩
  rw [heq]
  exact (hd.add (hη.mul hx)).add (hδ.mul hy)

end TwoVariables

/-!
## 8.8 Exercises on Partial Derivatives

The first exercise is the two-variable form of Theorem 8.2.1: a smooth function is
continuous, because its increment is infinitesimal. The second measures the quality of the
approximation of the increment by the total differential: the error is infinitesimal not
just compared to $`1` but compared to the distance $`\Delta l` moved in the plane.
-/

section Exercises

variable {f fx fy : ℝ → ℝ → ℝ} {a b : ℝ} {x y Δx Δy : ℝ*}

/-- **Exercise 8.8(1).** If $`f` is smooth at $`(a, b)`, then it is continuous at
$`(a, b)`: for $`x \simeq a` and $`y \simeq b` the difference $`{}^*f(x, y) - f(a, b)` is the
increment corresponding to $`\Delta x = x - a` and $`\Delta y = y - b`, which is
infinitesimal by the incremental equation. -/
theorem SmoothAt.continuousAt (h : SmoothAt f fx fy a b) :
    ContinuousAt (Function.uncurry f) (a, b) := by
  rw [continuousAt_uncurry_iff_infClose]
  intro x y hx hy
  have := (h.infinitesimal_increment₂ (Δx := x - a) (Δy := y - b) hx hy).1
  rw [increment₂_coe, add_sub_cancel, add_sub_cancel] at this
  exact this

/-- **Exercise 8.8(2).** Let $`f` be smooth at $`(a, b)` and let $`\Delta x, \Delta y` be
infinitesimal. Then the difference between the increment and the total differential is
infinitely smaller than the distance $`\Delta l = \sqrt{\Delta x^2 + \Delta y^2}` between
$`(a, b)` and $`(a + \Delta x, b + \Delta y)`:
$$`\frac{\Delta f - df}{\Delta l} \simeq 0.`
By the incremental equation the numerator is $`\varepsilon\,\Delta x + \delta\,\Delta y`,
and $`|\Delta x|` and $`|\Delta y|` are at most $`\Delta l`, so the quotient is bounded in
absolute value by $`|\varepsilon| + |\delta|`. (If $`\Delta l = 0` the quotient is $`0` by
Lean's convention on division by zero.) -/
theorem SmoothAt.increment₂_sub_totalDifferential_div_infClose (h : SmoothAt f fx fy a b)
    (hx : Infinitesimal Δx) (hy : Infinitesimal Δy) :
    (increment₂ f a b Δx Δy - totalDifferential fx fy a b Δx Δy) /
      hsqrt (Δx ^ 2 + Δy ^ 2) ≊ 0 := by
  rw [← infinitesimal_iff_infClose_zero]
  obtain ⟨η, δ, hη, hδ, heq⟩ := h.increment₂_eq hx hy
  set l : ℝ* := hsqrt (Δx ^ 2 + Δy ^ 2) with hl
  have hz : 0 ≤ Δx ^ 2 + Δy ^ 2 := by positivity
  have hl0 : 0 ≤ l := hsqrt_nonneg _
  have hsq : l ^ 2 = Δx ^ 2 + Δy ^ 2 := hsqrt_sq hz
  have hxl : |Δx| ≤ l := abs_le_of_sq_le_sq (by rw [hsq]; nlinarith [sq_nonneg Δy]) hl0
  have hyl : |Δy| ≤ l := abs_le_of_sq_le_sq (by rw [hsq]; nlinarith [sq_nonneg Δx]) hl0
  have hnum : increment₂ f a b Δx Δy - totalDifferential fx fy a b Δx Δy =
      η * Δx + δ * Δy := by rw [heq]; ring
  rw [hnum]
  have hbound : Infinitesimal (|η| + |δ|) :=
    (hη.of_abs_le (by rw [abs_abs])).add (hδ.of_abs_le (by rw [abs_abs]))
  refine hbound.of_abs_le ?_
  rw [abs_of_nonneg (add_nonneg (abs_nonneg η) (abs_nonneg δ))]
  rcases hl0.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero, abs_zero]
    positivity
  · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    calc |η * Δx + δ * Δy| ≤ |η * Δx| + |δ * Δy| := abs_add_le _ _
      _ = |η| * |Δx| + |δ| * |Δy| := by rw [abs_mul, abs_mul]
      _ ≤ |η| * l + |δ| * l :=
        add_le_add (mul_le_mul_of_nonneg_left hxl (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hyl (abs_nonneg _))
      _ = (|η| + |δ|) * l := by ring

end Exercises

end Goldblatt
