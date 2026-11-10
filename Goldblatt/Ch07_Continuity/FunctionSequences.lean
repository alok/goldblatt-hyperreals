import Goldblatt.Ch07_Continuity.Intervals

/-!
# 7 (part 3). Sequences of Functions: Sections 7.12 to 7.15

This is the third of three parts of Chapter 7 (the overview is on the chapter page
{lit}`Goldblatt.Ch07_Continuity`). It extends a sequence of real functions to a hypersequence
of functions on the hyperreals, characterises pointwise and uniform convergence by the
behaviour of the extended terms, and gives two proofs that a uniform limit of continuous
functions is continuous: the book's mixed proof, and the purely infinitesimal proof that
rests on a continuity property of the extended terms.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## 7.12 Sequences of Functions

A sequence of functions $`f_n` on a set $`A` of reals is one function $`F(n, x) = f_n(x)` of
two arguments, and the extension of $`F` defines $`f_N(x)` for every hypernatural $`N` and
every hyperreal $`x`. For a standard $`n` this is the extension of $`f_n`, and for a real
$`x` the hypersequence $`N \mapsto f_N(x)` is the extension of the real sequence
$`n \mapsto f_n(x)`.

With this, pointwise convergence to $`f` on $`A` says that $`f_N(x) \simeq f(x)` for every
unlimited $`N` and every _real_ $`x \in A` (Theorem 7.12.1, immediate from Theorem 6.1.1),
while uniform convergence says the same for _every_ $`x` in the enlargement of $`A`
(Theorem 7.12.2). The relation between the two is the same as between continuity and uniform
continuity in Section 7.7.

As in Chapter 6 the hypernaturals are a set of hyperreals, and the extended sequence takes
a hyperreal index and uses its integer part; only its values at hypernatural indices matter.
The standard notions are pointwise convergence along {name}`Filter.atTop` and Mathlib's
{name}`TendstoUniformlyOn`.
-/

section FunctionSequences

variable {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {A : Set ℝ} {N x y : ℝ*}

/-- **Section 7.12.** The hypersequence of functions associated with a sequence
$`(f_n)` of real functions: the extension of the function of two arguments
$`F(n, x) = f_n(x)`. The value at the hypernatural $`N` and the hyperreal $`x` is the
book's $`f_N(x)`. -/
def hyperFunSeq (F : ℕ → ℝ → ℝ) : ℝ* → ℝ* → ℝ* := ⋆(fun t x : ℝ => F ⌊t⌋₊ x)

/-- **Section 7.12.** On classes of sequences the extended term is computed termwise. -/
theorem hyperFunSeq_ofSeq (F : ℕ → ℝ → ℝ) (t r : ℕ → ℝ) :
    hyperFunSeq F (Hyperreal.ofSeq t) (Hyperreal.ofSeq r) =
      Hyperreal.ofSeq fun n => F ⌊t n⌋₊ (r n) := rfl

/-- **Section 7.12.** At the hypernatural $`[k_n]` and the hyperreal $`[r_n]` the extended
term is the class of $`n \mapsto f_{k_n}(r_n)`. -/
theorem hyperFunSeq_hnat (F : ℕ → ℝ → ℝ) (k : ℕ → ℕ) (r : ℕ → ℝ) :
    hyperFunSeq F (hnat k) (Hyperreal.ofSeq r) = Hyperreal.ofSeq fun n => F (k n) (r n) := by
  rw [hnat, hyperFunSeq_ofSeq]
  simp only [Nat.floor_natCast]

/-- **Section 7.12.** For a standard index $`n`, the function $`f_n` of the hypersequence is
the extension of the original $`f_n`. -/
theorem hyperFunSeq_natCast (F : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ*) :
    hyperFunSeq F (n : ℝ*) x = ⋆(F n) x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [natCast_eq_hnat, hyperFunSeq_hnat, starMap_hyperreal_ofSeq]

/-- **Section 7.12.** For a real $`x`, the hypersequence $`N \mapsto f_N(x)` is the extension
of the real sequence $`n \mapsto f_n(x)`. -/
theorem hyperFunSeq_coe (F : ℕ → ℝ → ℝ) (x : ℝ) (hN : N ∈ ℕ*) :
    hyperFunSeq F N (x : ℝ*) = hyperSeq (fun n => F n x) N := by
  obtain ⟨k, rfl⟩ := exists_hnat_eq hN
  rw [coe_eq_ofSeq_const, hyperFunSeq_hnat, hyperSeq_hnat]

/-- **Theorem 7.12.1.** The sequence $`(f_n)` converges pointwise on $`A` to $`f` if and
only if $`f_N(x) \simeq f(x)` for every real $`x \in A` and every unlimited hypernatural
$`N`. -/
theorem tendsto_pointwise_iff_infClose :
    (∀ x ∈ A, Tendsto (fun n => F n x) atTop (𝓝 (f x))) ↔
      ∀ x ∈ A, ∀ N ∈ unlimitedHyperNat, hyperFunSeq F N (x : ℝ*) ≊ f x := by
  refine forall₂_congr fun x _ => ?_
  rw [tendsto_iff_forall_unlimited_infClose]
  exact forall₂_congr fun N hN => by rw [hyperFunSeq_coe F x hN.1]

/-- **Theorem 7.12.2.** The sequence $`(f_n)` converges uniformly on $`A` to $`f` if and
only if $`f_N(x) \simeq {}^*f(x)` for every $`x` in the enlargement of $`A` and every
unlimited hypernatural $`N`.

The book leaves the proof as an exercise. If the convergence is uniform, then for a real
tolerance there is a standard $`m` beyond which all $`f_n` are within the tolerance of $`f`
on $`A`; this transfers, and an unlimited $`N` is beyond $`m`. Conversely, if the convergence
is not uniform for some tolerance, choose indices $`k_m \ge m` and points $`r_m \in A` where
the tolerance is violated; the classes of these sequences are an unlimited hypernatural and a
point of the enlargement at which the extended term is not infinitely close to the limit. -/
theorem tendstoUniformlyOn_iff_infClose :
    TendstoUniformlyOn F f atTop A ↔
      ∀ x ∈ ⋆A, ∀ N ∈ unlimitedHyperNat, hyperFunSeq F N x ≊ ⋆f x := by
  rw [Metric.tendstoUniformlyOn_iff]
  constructor
  · intro h x hx N hN
    obtain ⟨k, hk, rfl⟩ := exists_hnat_of_mem_unlimitedHyperNat hN
    obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
    rw [hyperFunSeq_hnat, starMap_hyperreal_ofSeq, ofSeq_infClose_ofSeq_iff]
    intro η hη
    obtain ⟨m, hm⟩ := eventually_atTop.1 (h η hη)
    filter_upwards [tendsto_atTop.1 hk m, hyperreal_ofSeq_mem_starSet.1 hx] with n h1 h2
    have := hm _ h1 _ h2
    rwa [Real.dist_eq, abs_sub_comm] at this
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨η, hη, hne⟩ := hne
    have hex : ∀ m : ℕ, ∃ n, m ≤ n ∧ ∃ t ∈ A, η ≤ dist (f t) (F n t) := fun m => by
      obtain ⟨n, hn, h⟩ := frequently_atTop.1 hne m
      exact ⟨n, hn, h⟩
    choose k hk r hr hd using hex
    have hkt : Tendsto k (hyperfilter ℕ) atTop :=
      (tendsto_atTop_mono hk tendsto_id).mono_left Nat.hyperfilter_le_atTop
    have := h _ (hyperreal_ofSeq_mem_starSet.2 (Eventually.of_forall hr)) _
      (hnat_mem_unlimitedHyperNat_iff.2 hkt)
    rw [hyperFunSeq_hnat, starMap_hyperreal_ofSeq, ofSeq_infClose_ofSeq_iff] at this
    obtain ⟨n, hn⟩ := (this η hη).exists
    have := hd n
    rw [Real.dist_eq, abs_sub_comm] at this
    linarith

/-- **Theorem 7.12.2**, forward direction as a rule. -/
theorem _root_.TendstoUniformlyOn.hyperFunSeq_infClose (h : TendstoUniformlyOn F f atTop A)
    (hx : x ∈ ⋆A) (hN : N ∈ unlimitedHyperNat) : hyperFunSeq F N x ≊ ⋆f x :=
  tendstoUniformlyOn_iff_infClose.1 h x hx N hN

/-- **Section 7.12, example.** The pointwise limit of the powers $`x^n` on $`[0, 1]`: the
function that is $`0` on $`[0, 1)` and $`1` at $`1`. -/
def powLimit (x : ℝ) : ℝ := if x = 1 then 1 else 0

/-- **Section 7.12, example.** On $`[0, 1]` the sequence $`f_n(x) = x^n` converges pointwise
to the function that vanishes on $`[0, 1)` and is $`1` at $`1`. -/
theorem tendsto_pow_powLimit {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => t ^ n) atTop (𝓝 (powLimit t)) := by
  rcases ht.2.eq_or_lt with rfl | h1
  · simp [powLimit]
  · rw [powLimit, ite_eq_right h1.ne]
    rcases ht.1.eq_or_lt with rfl | h0
    · exact (tendsto_const_nhds (x := (0 : ℝ))).congr'
        (eventually_atTop.2 ⟨1, fun n hn => (zero_pow (by omega)).symm⟩)
    · exact tendsto_pow_zero_of_pos_of_lt_one h0 h1

/-- **Section 7.12, example, tool.** The extension of the $`n`-th power function is the
$`n`-th power. -/
theorem starMap_pow_apply (n : ℕ) (x : ℝ*) : ⋆(fun t : ℝ => t ^ n) x = x ^ n := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- **Section 7.12, example, tool.** If $`x \simeq 1` then $`x^n \simeq 1` for every
standard $`n`, by induction on $`n` from the fact that a product of limited numbers
infinitely close to $`1` is infinitely close to $`1` (Exercise 5.7(1)). -/
theorem pow_infClose_one (n : ℕ) (hx : x ≊ ((1 : ℝ) : ℝ*)) : x ^ n ≊ ((1 : ℝ) : ℝ*) := by
  rw [Hyperreal.coe_one] at *
  induction n with
  | zero => rw [pow_zero]
  | succ n ih =>
    have := ih.mul hx (limited_one.of_infClose ih.symm) (limited_one.of_infClose hx.symm)
    rwa [← pow_succ, one_mul] at this

/-- **Section 7.12, example, limited indices.** For a standard $`n`, if $`x \simeq 1` then
$`f_n(x) = x^n \simeq 1`. So for such $`x` all the standard terms of the hypersequence lie
in the halo of $`1`, and any index at which $`x^N` is infinitesimal must be unlimited. -/
theorem hyperFunSeq_pow_infClose_one (n : ℕ) (hx : x ≊ ((1 : ℝ) : ℝ*)) :
    hyperFunSeq (fun n t => t ^ n) (n : ℝ*) x ≊ ((1 : ℝ) : ℝ*) := by
  rw [hyperFunSeq_natCast, starMap_pow_apply]
  exact pow_infClose_one n hx

/-- **Section 7.12, example, the point at which uniformity fails.** There is a point $`x` of
the enlargement of $`[0, 1]` with $`x < 1` and $`x \simeq 1`, so that $`{}^*f(x) = 0`, for
which

* some unlimited $`N` has $`x^N = 1/2`, which is not infinitely close to $`0`, and
* some unlimited $`M` has $`x^K \simeq 0` for every hypernatural $`K \ge M`.

Together with {name}`hyperFunSeq_pow_infClose_one`, which says that $`x^n \simeq 1` for
standard $`n`, this is the picture described in the book: it takes infinitely long for the
powers of $`x` to become infinitesimal. Here $`x` is the class of the sequence of
$`(n+1)`-st roots of $`1/2`, $`N` is the class of $`n + 1`, and $`M` is the class of
$`(n+1)^2`. The book obtains $`M` by transfer of pointwise convergence for an arbitrary such
$`x`, and $`N` from a permanence principle that only becomes available in Chapter 15; the
explicit choice replaces both. -/
theorem exists_hyperFunSeq_pow_eq_half :
    ∃ x ∈ ⋆(Icc (0 : ℝ) 1), x < 1 ∧ x ≊ ((1 : ℝ) : ℝ*) ∧ ⋆powLimit x = 0 ∧
      (∃ N ∈ unlimitedHyperNat, hyperFunSeq (fun n t => t ^ n) N x = ((1 / 2 : ℝ) : ℝ*)) ∧
      ∃ M ∈ unlimitedHyperNat, ∀ K ∈ ℕ*, M ≤ K →
        hyperFunSeq (fun n t => t ^ n) K x ≊ 0 := by
  let r : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (1 / ((n : ℝ) + 1))
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hr0 : ∀ n, 0 < r n := fun n => Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : ∀ n, r n < 1 := fun n => Real.rpow_lt_one (by norm_num) (by norm_num) (hpos n)
  have hrp : ∀ n : ℕ, r n ^ (n + 1) = 1 / 2 := fun n => by
    simp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : 1 / ((n : ℝ) + 1) * ((n + 1 : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  have hlim : Tendsto r atTop (𝓝 1) := by
    have h := (Real.continuousAt_const_rpow (a := (1 / 2 : ℝ)) (b := 0)
      (by norm_num)).tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [Real.rpow_zero] at h
  refine ⟨Hyperreal.ofSeq r,
    hyperreal_ofSeq_mem_starSet.2 (Eventually.of_forall fun n => ⟨(hr0 n).le, (hr1 n).le⟩),
    ?_, ofSeq_infClose_coe_iff.2 (hlim.mono_left Nat.hyperfilter_le_atTop), ?_,
    ⟨hnat fun n => n + 1, hnat_mem_unlimitedHyperNat_iff.2
      ((tendsto_add_atTop_nat 1).mono_left Nat.hyperfilter_le_atTop), ?_⟩,
    ⟨hnat fun n => (n + 1) ^ 2, hnat_mem_unlimitedHyperNat_iff.2 (Tendsto.mono_left
      (tendsto_atTop_mono (fun n => (Nat.le_succ n).trans (Nat.le_self_pow two_ne_zero _))
        tendsto_id) Nat.hyperfilter_le_atTop), ?_⟩⟩
  · rw [← Hyperreal.coe_one, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
    exact Eventually.of_forall hr1
  · rw [starMap_hyperreal_ofSeq, ← Hyperreal.coe_zero, coe_eq_ofSeq_const]
    exact congrArg Hyperreal.ofSeq (funext fun n => ite_eq_right (hr1 n).ne)
  · rw [hyperFunSeq_hnat, coe_eq_ofSeq_const]
    exact congrArg Hyperreal.ofSeq (funext hrp)
  · intro K hK hMK
    obtain ⟨k, rfl⟩ := exists_hnat_eq hK
    rw [hnat_le_hnat_iff] at hMK
    rw [hyperFunSeq_hnat, ← Hyperreal.coe_zero, ofSeq_infClose_coe_iff]
    have hgeo : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) (hyperfilter ℕ) (𝓝 0) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)).mono_left Nat.hyperfilter_le_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgeo
      (Eventually.of_forall fun n => (pow_pos (hr0 n) _).le) (hMK.mono fun n hn => ?_)
    calc r n ^ k n ≤ r n ^ ((n + 1) ^ 2) := pow_le_pow_of_le_one (hr0 n).le (hr1 n).le hn
      _ = (r n ^ (n + 1)) ^ (n + 1) := by rw [← pow_mul, sq]
      _ = (1 / 2 : ℝ) ^ (n + 1) := by rw [hrp]

/-- **Section 7.12, example.** The convergence of $`x^n` on $`[0, 1]` is not uniform, by
Theorem 7.12.2: there are $`x` in the enlargement of $`[0, 1]` and an unlimited $`N` with
$`f_N(x) = 1/2` and $`{}^*f(x) = 0`, and these are not infinitely close. -/
theorem not_tendstoUniformlyOn_pow :
    ¬ TendstoUniformlyOn (fun n t => t ^ n) powLimit atTop (Icc (0 : ℝ) 1) := by
  intro h
  obtain ⟨x, hx, -, -, h2, ⟨N, hN, h1⟩, -⟩ := exists_hyperFunSeq_pow_eq_half
  have := h.hyperFunSeq_infClose hx hN
  rw [h1, h2, ← Hyperreal.coe_zero, infClose_coe_iff] at this
  norm_num at this

end FunctionSequences

/-!
## 7.13 Continuity of a Uniform Limit

A pointwise limit of continuous functions can be discontinuous, as the powers $`x^n` on
$`[0, 1]` show. A uniform limit cannot. The book's first proof combines the hyperreal
characterisation of continuity with the standard definition of uniform convergence. Let
$`c \in A` and $`x \simeq c` in the enlargement of $`A`, and let $`\varepsilon` be a positive
real. Choose a standard $`n` such that $`f_n` is within $`\varepsilon/4` of $`f` on all of
$`A`; by transfer this also holds at $`x`. In

$$`|f(x) - f(c)| \le |f(x) - f_n(x)| + |f_n(x) - f_n(c)| + |f_n(c) - f(c)|`

the outer terms are below $`\varepsilon/4` and the middle term is infinitesimal because
$`f_n` is continuous at $`c`. So $`|f(x) - f(c)| < \varepsilon` for every positive real
$`\varepsilon`.
-/

section UniformLimit

variable {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {A : Set ℝ} {N x y : ℝ*}

/-- **Theorem 7.13.1.** Uniform convergence preserves continuity: the limit $`f` of a
sequence of functions $`f_n` that converges uniformly on $`A` is continuous on $`A` as soon
as every $`f_n` is. This is the book's
first proof, with the $`\varepsilon/4` estimate. -/
theorem continuousOn_of_tendstoUniformlyOn (hF : ∀ n, ContinuousOn (F n) A)
    (hu : TendstoUniformlyOn F f atTop A) : ContinuousOn f A := by
  intro c hc
  rw [continuousWithinAt_iff_infClose]
  intro x hx hxc
  rw [infClose_iff_abs_lt]
  intro η hη
  have hη4 : (0 : ℝ) < η / 4 := by linarith
  obtain ⟨m, hm⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hu (η / 4) hη4)
  have hmA : ∀ t ∈ A, |F m t - f t| < η / 4 := fun t ht => by
    have := hm m le_rfl t ht
    rwa [Real.dist_eq, abs_sub_comm] at this
  -- transfer of the uniform estimate to the enlargement of A
  have h1 : |⋆(F m) x - ⋆f x| < ((η / 4 : ℝ) : ℝ*) := by
    have := starMap_lt_starMap_of_mem (f := fun t => |F m t - f t|) (g := fun _ => η / 4)
      hmA hx
    rwa [starMap_abs_apply (fun t => F m t - f t), starMap_sub_apply (F m) f,
      starMap_const_apply] at this
  have h2 : |((F m c : ℝ) : ℝ*) - (f c : ℝ)| < ((η / 4 : ℝ) : ℝ*) := by
    rw [← Hyperreal.coe_sub, ← Hyperreal.coe_abs]
    exact Hyperreal.coe_lt_coe.2 (hmA c hc)
  -- continuity of f_m at c
  have h3 : |⋆(F m) x - ((F m c : ℝ) : ℝ*)| < ((η / 4 : ℝ) : ℝ*) :=
    infClose_iff_abs_lt.1 ((hF m c hc).starMap_infClose hx hxc) _ hη4
  have h4 : ((η / 4 : ℝ) : ℝ*) + ((η / 4 : ℝ) : ℝ*) + ((η / 4 : ℝ) : ℝ*) < (η : ℝ*) := by
    rw [← Hyperreal.coe_add, ← Hyperreal.coe_add]
    exact Hyperreal.coe_lt_coe.2 (by linarith)
  rw [abs_lt] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

end UniformLimit

/-!
## 7.14 Continuity in the Extended Hypersequence

The proof above keeps the index $`n` standard. Could one instead take $`n` unlimited, so that
by Theorem 7.12.2 the two outer terms become infinitesimal? Then the middle term involves an
extended term $`f_N`, which is in general not the extension of a real function (its values at
real points need not be real), so Theorem 7.1.1 does not apply to it. What survives is the
weaker continuity property of Theorem 7.1.3(3): each $`f_N` maps some sufficiently small
infinitesimal neighbourhood of a point $`y` into the halo of $`f_N(y)`, though perhaps not
the whole halo of $`y`. This holds at every point $`y` of the enlargement of $`A`, real or
not (Theorem 7.14.1).

That is enough for a second proof of Theorem 7.13.1, with no inequality at all. Fix an
unlimited $`N` and let $`d` be the infinitesimal radius given by Theorem 7.14.1 at the point
$`c`. For $`x` in the enlargement of $`A` within $`d` of $`c`,

$$`{}^*f(x) \simeq f_N(x) \simeq f_N(c) \simeq f(c),`

the outer steps by uniform convergence. So $`f` satisfies condition (3) of Theorem 7.1.3 at
$`c`.
-/

section ExtendedHypersequence

variable {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {A : Set ℝ} {N x y : ℝ*}

/-- **Theorem 7.14.1.** If the functions $`f_n` are all continuous on $`A`, then for every
hypernatural $`N` and every $`y` in the enlargement of $`A` there is a positive
infinitesimal $`d` such that $`f_N(x) \simeq f_N(y)` for all $`x` in the enlargement of
$`A` with $`|x - y| < d`.

The book transfers the sentence "every $`f_n` is continuous at every point of $`A`" and
applies it with an infinitesimal tolerance. In the ultrapower: $`N` is the class of
$`(k_n)` and $`y` of $`(y_n)`; for almost all $`n` the function $`f_{k_n}` is continuous at
$`y_n`, so there is $`\delta_n > 0` such that points of $`A` within $`\delta_n` of $`y_n`
have $`f_{k_n}`-values within $`1/(n+1)` of $`f_{k_n}(y_n)`. The class of
$`\min(\delta_n, 1/(n+1))` is the required $`d`. -/
theorem exists_infinitesimal_radius_hyperFunSeq (hF : ∀ n, ContinuousOn (F n) A)
    (hN : N ∈ ℕ*) (hy : y ∈ ⋆A) :
    ∃ d : ℝ*, 0 < d ∧ Infinitesimal d ∧
      ∀ x ∈ ⋆A, |x - y| < d → hyperFunSeq F N x ≊ hyperFunSeq F N y := by
  obtain ⟨k, rfl⟩ := exists_hnat_eq hN
  obtain ⟨u, rfl⟩ := hyperreal_exists_rep y
  have huA := hyperreal_ofSeq_mem_starSet.1 hy
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hex : ∀ n : ℕ, ∃ δ : ℝ, 0 < δ ∧ (u n ∈ A → ∀ t ∈ A, |t - u n| < δ →
      |F (k n) t - F (k n) (u n)| < 1 / ((n : ℝ) + 1)) := fun n => by
    by_cases hn : u n ∈ A
    · obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.1 (hF (k n) (u n) hn) _ (hpos n)
      exact ⟨δ, hδ, fun _ t ht htu => by
        have := h ht (by rwa [Real.dist_eq])
        rwa [Real.dist_eq] at this⟩
    · exact ⟨1, one_pos, fun h => absurd h hn⟩
  choose δ hδ hδ' using hex
  let dn : ℕ → ℝ := fun n => min (δ n) (1 / ((n : ℝ) + 1))
  have hdn : ∀ n, 0 < dn n := fun n => lt_min (hδ n) (hpos n)
  refine ⟨Hyperreal.ofSeq dn, ?_, ?_, ?_⟩
  · have : Hyperreal.ofSeq (fun _ => (0 : ℝ)) < Hyperreal.ofSeq dn :=
      ofSeq_lt_ofSeq_iff.2 (Eventually.of_forall hdn)
    exact this
  · rw [infinitesimal_iff_infClose_zero, ← Hyperreal.coe_zero, ofSeq_infClose_coe_iff]
    refine Tendsto.mono_left ?_ Nat.hyperfilter_le_atTop
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hdn n).le) fun n => min_le_right _ _
  · intro x hx hxd
    obtain ⟨v, rfl⟩ := hyperreal_exists_rep x
    have e : Hyperreal.ofSeq v - Hyperreal.ofSeq u = Hyperreal.ofSeq fun n => v n - u n := rfl
    rw [e, abs_ofSeq, ofSeq_lt_ofSeq_iff] at hxd
    rw [hyperFunSeq_hnat, hyperFunSeq_hnat, ofSeq_infClose_ofSeq_iff]
    intro η hη
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hη
    have hge : ∀ᶠ n in hyperfilter ℕ, m ≤ n := eventually_hyperfilter_of_forall_ge m fun _ h => h
    filter_upwards [huA, hyperreal_ofSeq_mem_starSet.1 hx, hxd, hge] with n h1 h2 h3 h4
    have h5 := hδ' n h1 _ h2 (lt_of_lt_of_le h3 (min_le_left _ _))
    have h6 : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (m : ℝ) ≤ n := by exact_mod_cast h4
      linarith
    linarith

/-- **Theorem 7.13.1, second proof (Section 7.14).** A uniform limit of functions continuous
on $`A` is continuous on $`A`. This proof uses the hyperreal characterisation of uniform
convergence (Theorem 7.12.2) at an unlimited index, the continuity property of the extended
terms (Theorem 7.14.1), and the criterion of Theorem 7.1.3(3). -/
theorem continuousOn_of_tendstoUniformlyOn' (hF : ∀ n, ContinuousOn (F n) A)
    (hu : TendstoUniformlyOn F f atTop A) : ContinuousOn f A := by
  intro c hc
  have hcA : (c : ℝ*) ∈ ⋆A := coe_mem_starSet.2 hc
  have hω := omega_mem_unlimitedHyperNat
  obtain ⟨d, hd, -, h⟩ := exists_infinitesimal_radius_hyperFunSeq hF hω.1 hcA
  refine continuousWithinAt_of_exists_radius hd fun x hx hxd => ?_
  have e1 := hu.hyperFunSeq_infClose hx hω
  have e2 := hu.hyperFunSeq_infClose hcA hω
  rw [starMap_coe] at e2
  exact (e1.symm.trans (h x hx hxd)).trans e2

end ExtendedHypersequence

/-!
## 7.15 Was Cauchy Right?

The chapter closes with a historical remark and no new mathematics. In 1821 Cauchy stated
that the sum of a convergent series of continuous functions is continuous. Read with the
standard definitions this is false without uniform convergence, as the example of Section
7.12 shows. Read with infinitesimals it can be defended: if "continuous" is required of the
terms with infinitely large index as well, and "in the neighbourhood of a value" means at
all points infinitely close to it, then the hypotheses are of the kind used in Section 7.14,
where the argument does go through. The book refers to articles of Cleave and of Lakatos for
this reassessment. Nothing in this section is formalized, because it makes no formal claim
beyond the theorems of Sections 7.12 to 7.14.
-/

end Goldblatt
