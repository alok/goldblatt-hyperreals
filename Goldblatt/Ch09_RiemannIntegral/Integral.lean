import Goldblatt.Ch09_RiemannIntegral.Sums

/-!
# 9 (part 2). The Integral as the Shadow of Riemann Sums: Section 9.2

This is the second of three parts of Chapter 9 (the overview is on the chapter page
{lit}`Goldblatt.Ch09_RiemannIntegral`). It defines Riemann integrability and the Riemann
integral as in the standard theory, and proves the chapter's central result: a bounded
function is integrable exactly when its upper and lower sums of infinitesimal width are
infinitely close, and then the integral is the shadow of the Riemann sum of any positive
infinitesimal width.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## 9.2 The Integral as the Shadow of Riemann Sums

The standard definition says that a bounded function $`f` is Riemann integrable on
$`[a, b]` when the least upper bound of its lower sums equals the greatest lower bound of its
upper sums, the common value being the integral. This definition is taken over unchanged
({lit}`Goldblatt.RiemannIntegrableOn`, {lit}`Goldblatt.riemannIntegral`); the integral is
not defined in terms of Mathlib's integral.

The section then shows that the hyperreal Riemann sums of Section 9.1 capture this notion
completely.

* If the lower and upper sums for one positive infinitesimal width are infinitely close,
  then $`f` is integrable, and the integral is the shadow of the ordinary Riemann sum of that
  width. By Theorem 9.1.1 and Exercise 9.1.2 this applies to continuous and to monotonic
  functions.
* Conversely, if $`f` is integrable then for every positive infinitesimal width the lower,
  ordinary and upper sums are all infinitely close to the integral.

So the integral is $`\operatorname{sh}\bigl(S_a^b(f, \Delta x)\bigr)` for any positive
infinitesimal $`\Delta x`, which is Leibniz's sum of infinitely many infinitely thin
rectangles made precise.
-/

section Integrability

variable {f : ℝ → ℝ} {a b I : ℝ} {Δ Δ' : ℝ*}

/-- **Section 9.1.** The set of all lower Riemann sums $`L_a^b(f, P)` of $`f`, over all
partitions $`P` of $`[a, b]`. -/
def lowerSums (f : ℝ → ℝ) (a b : ℝ) : Set ℝ := range fun P : IntervalPartition a b => P.lowerSum f

/-- **Section 9.1.** The set of all upper Riemann sums $`U_a^b(f, P)` of $`f`, over all
partitions $`P` of $`[a, b]`. -/
def upperSums (f : ℝ → ℝ) (a b : ℝ) : Set ℝ := range fun P : IntervalPartition a b => P.upperSum f

/-- Every lower sum belongs to the set of lower sums. -/
theorem IntervalPartition.lowerSum_mem (P : IntervalPartition a b) (f : ℝ → ℝ) :
    P.lowerSum f ∈ lowerSums f a b := mem_range_self P

/-- Every upper sum belongs to the set of upper sums. -/
theorem IntervalPartition.upperSum_mem (P : IntervalPartition a b) (f : ℝ → ℝ) :
    P.upperSum f ∈ upperSums f a b := mem_range_self P

/-- **Section 9.1.** The bounded function $`f` is Riemann integrable on $`[a, b]` _with
integral_ $`I`: the real number $`I` is the least upper bound of the lower sums and also the
greatest lower bound of the upper sums of $`f`, taken over all partitions of $`[a, b]`. -/
def HasRiemannIntegral (f : ℝ → ℝ) (a b I : ℝ) : Prop :=
  BoundedOn f (Icc a b) ∧ IsLUB (lowerSums f a b) I ∧ IsGLB (upperSums f a b) I

/-- **Section 9.1.** The function $`f` is _Riemann integrable_ on $`[a, b]`: it is bounded
there, and some real number is both the least upper bound of its lower sums and the greatest
lower bound of its upper sums. -/
def RiemannIntegrableOn (f : ℝ → ℝ) (a b : ℝ) : Prop := ∃ I : ℝ, HasRiemannIntegral f a b I

/-- **Section 9.1.** The _Riemann integral_ $`\int_a^b f(x)\,dx`, defined as the least upper
bound of the lower sums of $`f` over all partitions of $`[a, b]`. For an integrable function
this is the number of the definition of integrability
({lit}`Goldblatt.RiemannIntegrableOn.hasRiemannIntegral`). The definition does not use
Mathlib's integral; the two are compared for continuous functions at the end of the
chapter. -/
def riemannIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ := sSup (lowerSums f a b)

/-- An interval on which some function is integrable is not reversed. -/
theorem HasRiemannIntegral.le (h : HasRiemannIntegral f a b I) : a ≤ b := by
  by_contra hab
  have hemp : lowerSums f a b = ∅ := by
    rw [lowerSums, range_eq_empty_iff]
    exact ⟨fun P => hab P.le⟩
  have h1 := h.2.1
  rw [hemp] at h1
  have h2 : I ≤ I - 1 := h1.2 fun _ hx => absurd hx (notMem_empty _)
  linarith

/-- The integral of the definition of integrability is {name}`riemannIntegral`. -/
theorem HasRiemannIntegral.riemannIntegral_eq (h : HasRiemannIntegral f a b I) :
    riemannIntegral f a b = I :=
  h.2.1.csSup_eq ⟨_, (meshPartition h.le one_pos).lowerSum_mem f⟩

/-- An integrable function has the integral {name}`riemannIntegral`. -/
theorem RiemannIntegrableOn.hasRiemannIntegral (h : RiemannIntegrableOn f a b) :
    HasRiemannIntegral f a b (riemannIntegral f a b) := by
  obtain ⟨I, hI⟩ := h
  rwa [hI.riemannIntegral_eq]

/-- An integrable function is bounded. -/
theorem RiemannIntegrableOn.boundedOn (h : RiemannIntegrableOn f a b) : BoundedOn f (Icc a b) :=
  h.hasRiemannIntegral.1

/-- An interval on which some function is integrable is not reversed. -/
theorem RiemannIntegrableOn.le (h : RiemannIntegrableOn f a b) : a ≤ b :=
  h.hasRiemannIntegral.le

/-- The integral of a function is unique. -/
theorem HasRiemannIntegral.unique {J : ℝ} (hI : HasRiemannIntegral f a b I)
    (hJ : HasRiemannIntegral f a b J) : I = J := by
  rw [← hI.riemannIntegral_eq, hJ.riemannIntegral_eq]

/-- **Section 9.1, conditions (1) and (2), sufficiency.** If $`f` is bounded,
$`L_a^b(f, P) \le I \le U_a^b(f, P)` for every partition $`P`, and for every real
$`\varepsilon > 0` some partition has $`U_a^b(f, P) - L_a^b(f, P) < \varepsilon`, then $`f`
is integrable on $`[a, b]` with integral $`I`. -/
theorem hasRiemannIntegral_of_conditions (hf : BoundedOn f (Icc a b))
    (h1 : ∀ P : IntervalPartition a b, P.lowerSum f ≤ I ∧ I ≤ P.upperSum f)
    (h2 : ∀ η : ℝ, 0 < η → ∃ P : IntervalPartition a b, P.upperSum f - P.lowerSum f < η) :
    HasRiemannIntegral f a b I := by
  refine ⟨hf, ⟨?_, fun c hc => ?_⟩, ⟨?_, fun c hc => ?_⟩⟩
  · rintro _ ⟨P, rfl⟩
    exact (h1 P).1
  · refine le_of_forall_pos_le_add fun η hη => ?_
    obtain ⟨P, hP⟩ := h2 η hη
    have := hc (P.lowerSum_mem f)
    linarith [(h1 P).2]
  · rintro _ ⟨P, rfl⟩
    exact (h1 P).2
  · refine le_of_forall_pos_le_add fun η hη => ?_
    obtain ⟨P, hP⟩ := h2 η hη
    have := hc (P.upperSum_mem f)
    linarith [(h1 P).1]

/-- **Section 9.2, by existential transfer.** If the lower and upper sums for some positive
hyperreal width are infinitely close, then for every real $`\varepsilon > 0` there is a
real width $`\Delta x > 0` with $`U_a^b(f, \Delta x) - L_a^b(f, \Delta x) < \varepsilon`. -/
theorem exists_pos_upperSum_sub_lowerSum_lt (hΔ : 0 < Δ)
    (h : hyperLowerSum f a b Δ ≊ hyperUpperSum f a b Δ) {η : ℝ} (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ upperSum f a b t - lowerSum f a b t < η := by
  refine exists_pos_lt_of_starMap_lt (F := fun t => upperSum f a b t - lowerSum f a b t)
    (G := fun _ => η) hΔ ?_
  rw [starMap_sub_apply, starMap_const_apply]
  have : Infinitesimal (hyperUpperSum f a b Δ - hyperLowerSum f a b Δ) := h.symm
  exact (le_abs_self _).trans_lt (infinitesimal_iff_abs_lt.1 this η hη)

/-- **Section 9.2.** Let $`\Delta x_1` and $`\Delta x_2` be positive hyperreals at each of
which the lower and upper sums of the bounded function $`f` are infinitely close. Then the
two upper sums are infinitely close. This is the book's comparison of $`L_1, U_1, L_2, U_2`:
since every lower sum is below every upper sum, $`U_1 - U_2 \le U_1 - L_1` and
$`U_2 - U_1 \le U_2 - L_2`. -/
theorem hyperUpperSum_infClose_hyperUpperSum (hf : BoundedOn f (Icc a b)) (hab : a ≤ b)
    (hΔ : 0 < Δ) (hΔ' : 0 < Δ') (h : hyperLowerSum f a b Δ ≊ hyperUpperSum f a b Δ)
    (h' : hyperLowerSum f a b Δ' ≊ hyperUpperSum f a b Δ') :
    hyperUpperSum f a b Δ ≊ hyperUpperSum f a b Δ' := by
  have h12 := hyperLowerSum_le_hyperUpperSum hf hab hΔ hΔ'
  have h21 := hyperLowerSum_le_hyperUpperSum hf hab hΔ' hΔ
  have e1 : Infinitesimal (hyperUpperSum f a b Δ - hyperLowerSum f a b Δ) := h.symm
  have e2 : Infinitesimal (hyperUpperSum f a b Δ' - hyperLowerSum f a b Δ') := h'.symm
  rw [infClose_iff_abs_lt]
  intro r hr
  have h1 := abs_lt.1 (infinitesimal_iff_abs_lt.1 e1 r hr)
  have h2 := abs_lt.1 (infinitesimal_iff_abs_lt.1 e2 r hr)
  rw [abs_lt]
  constructor <;> linarith

/-- **Section 9.2.** The ordinary Riemann sums of a bounded function for any two positive
hyperreal widths, at each of which the lower and upper sums are infinitely close, are
infinitely close to each other:
$`S_a^b(f, \Delta x_1) \simeq S_a^b(f, \Delta x_2)`. In particular this holds for any two
positive infinitesimal widths when $`f` is continuous or monotonic. -/
theorem hyperOrdSum_infClose_hyperOrdSum (hf : BoundedOn f (Icc a b)) (hab : a ≤ b)
    (hΔ : 0 < Δ) (hΔ' : 0 < Δ') (h : hyperLowerSum f a b Δ ≊ hyperUpperSum f a b Δ)
    (h' : hyperLowerSum f a b Δ' ≊ hyperUpperSum f a b Δ') :
    hyperOrdSum f a b Δ ≊ hyperOrdSum f a b Δ' := by
  have h1 := (infClose_between (hyperLowerSum_le_hyperOrdSum hf hab hΔ)
    (hyperOrdSum_le_hyperUpperSum hf hab hΔ) h).2
  have h2 := (infClose_between (hyperLowerSum_le_hyperOrdSum hf hab hΔ')
    (hyperOrdSum_le_hyperUpperSum hf hab hΔ') h').2
  exact h1.trans ((hyperUpperSum_infClose_hyperUpperSum hf hab hΔ hΔ' h h').trans h2.symm)

/-- **Section 9.2, the definition (iii) fulfils conditions (1) and (2).** Let $`f` be
bounded on $`[a, b]` and let $`\Delta x` be a positive infinitesimal with
$`L_a^b(f, \Delta x) \simeq U_a^b(f, \Delta x)`. Then $`f` is Riemann integrable on
$`[a, b]`, with integral
$$`\int_a^b f(x)\,dx = \operatorname{sh}\bigl(S_a^b(f, \Delta x)\bigr).`
For a standard partition $`P` the transferred inequalities give
$`L(f, P) \le U(f, \Delta x) \simeq S(f, \Delta x) \simeq L(f, \Delta x) \le U(f, P)`, so
the shadow lies between the real numbers $`L(f, P)` and $`U(f, P)`; and a real partition
with $`U - L < \varepsilon` exists by existential transfer. -/
theorem hasRiemannIntegral_sh_of_infClose (hf : BoundedOn f (Icc a b)) (hab : a ≤ b)
    (hΔ : PosInfinitesimal Δ) (h : hyperLowerSum f a b Δ ≊ hyperUpperSum f a b Δ) :
    HasRiemannIntegral f a b (sh (hyperOrdSum f a b Δ)) := by
  obtain ⟨h1, h2⟩ := infClose_between (hyperLowerSum_le_hyperOrdSum hf hab hΔ.1)
    (hyperOrdSum_le_hyperUpperSum hf hab hΔ.1) h
  have hSI : hyperOrdSum f a b Δ ≊ (sh (hyperOrdSum f a b Δ) : ℝ) :=
    (limited_hyperOrdSum hf hab hΔ.1).infClose_sh
  have hUI := h2.symm.trans hSI
  have hLI := h1.trans hSI
  refine hasRiemannIntegral_of_conditions hf (fun P => ⟨?_, ?_⟩) fun η hη => ?_
  · exact coe_le_coe_of_le_infClose (P.lowerSum_le_hyperUpperSum hf hΔ.1) hUI
  · exact coe_le_coe_of_infClose_le hLI.symm (P.hyperLowerSum_le_upperSum hf hΔ.1)
  · obtain ⟨t, ht, hlt⟩ := exists_pos_upperSum_sub_lowerSum_lt hΔ.1 h hη
    exact ⟨meshPartition hab ht, hlt⟩

/-- **Section 9.2, by transfer of the standard estimate.** With $`|f| \le B` on $`[a, b]`
and a standard partition $`P` with $`n` subintervals,
$`U_a^b(f, \Delta x) \le U_a^b(f, P) + 8Bn\,\Delta x` for every positive hyperreal
$`\Delta x`. -/
theorem hyperUpperSum_le_add_mul (P : IntervalPartition a b) {B : ℝ}
    (hB : ∀ x ∈ Icc a b, |f x| ≤ B) (hΔ : 0 < Δ) :
    hyperUpperSum f a b Δ ≤ ((P.upperSum f : ℝ) : ℝ*) + ((8 * B * P.n : ℝ) : ℝ*) * Δ := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep Δ
  change Hyperreal.ofSeq (fun n => upperSum f a b (r n)) ≤
    Hyperreal.ofSeq (fun n => P.upperSum f + 8 * B * P.n * r n)
  exact ofSeq_le_ofSeq_iff.2 ((zero_lt_ofSeq_iff.1 hΔ).mono fun n hn =>
    upperSum_le_add_mul P hB hn)

/-- **Section 9.2, by transfer of the standard estimate.** With $`|f| \le B` on $`[a, b]`
and a standard partition $`P` with $`n` subintervals,
$`L_a^b(f, P) - 8Bn\,\Delta x \le L_a^b(f, \Delta x)` for every positive hyperreal
$`\Delta x`. -/
theorem sub_mul_le_hyperLowerSum (P : IntervalPartition a b) {B : ℝ}
    (hB : ∀ x ∈ Icc a b, |f x| ≤ B) (hΔ : 0 < Δ) :
    ((P.lowerSum f : ℝ) : ℝ*) - ((8 * B * P.n : ℝ) : ℝ*) * Δ ≤ hyperLowerSum f a b Δ := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep Δ
  change Hyperreal.ofSeq (fun n => P.lowerSum f - 8 * B * P.n * r n) ≤
    Hyperreal.ofSeq (fun n => lowerSum f a b (r n))
  exact ofSeq_le_ofSeq_iff.2 ((zero_lt_ofSeq_iff.1 hΔ).mono fun n hn =>
    sub_mul_le_lowerSum P hB hn)

/-- **Section 9.2.** If $`f` is Riemann integrable on $`[a, b]` with integral $`I`, then the
upper sum of every positive infinitesimal width is infinitely close to $`I`. Given a real
$`\varepsilon > 0`, choose standard partitions $`P_1`, $`P_2` with
$`I - \varepsilon < L(f, P_1)` and $`U(f, P_2) < I + \varepsilon/2`. By transfer
$`L(f, P_1) \le U(f, \Delta x) \le U(f, P_2) + 8Bn\,\Delta x`, and the last term is
infinitesimal. -/
theorem HasRiemannIntegral.hyperUpperSum_infClose (h : HasRiemannIntegral f a b I)
    (hΔ : PosInfinitesimal Δ) : hyperUpperSum f a b Δ ≊ I := by
  obtain ⟨hf, hL, hU⟩ := h
  obtain ⟨B, hB⟩ := hf
  rw [infClose_iff_abs_lt]
  intro η hη
  obtain ⟨δ, hδ, hδη⟩ : ∃ δ : ℝ, 0 < δ ∧ δ + δ = η := ⟨η / 2, half_pos hη, add_halves η⟩
  obtain ⟨_, ⟨P1, rfl⟩, hP1, -⟩ := hL.exists_between (sub_lt_self I hη)
  obtain ⟨_, ⟨P2, rfl⟩, -, hP2⟩ := hU.exists_between (lt_add_of_pos_right I hδ)
  have h1 := P1.lowerSum_le_hyperUpperSum ⟨B, hB⟩ hΔ.1
  have h2 := hyperUpperSum_le_add_mul P2 hB hΔ.1
  have h3 := coe_mul_posInfinitesimal_lt (8 * B * P2.n) hΔ hδ
  have h4 : ((I - η : ℝ) : ℝ*) < (P1.lowerSum f : ℝ) := Hyperreal.coe_lt_coe.2 hP1
  have h5 : ((P2.upperSum f : ℝ) : ℝ*) < ((I + δ : ℝ) : ℝ*) := Hyperreal.coe_lt_coe.2 hP2
  have h6 : (η : ℝ*) = δ + δ := by rw [← hδη, Hyperreal.coe_add]
  rw [Hyperreal.coe_sub] at h4
  rw [Hyperreal.coe_add] at h5
  rw [abs_lt]
  constructor <;> linarith

/-- **Section 9.2.** If $`f` is Riemann integrable on $`[a, b]` with integral $`I`, then the
lower sum of every positive infinitesimal width is infinitely close to $`I`. -/
theorem HasRiemannIntegral.hyperLowerSum_infClose (h : HasRiemannIntegral f a b I)
    (hΔ : PosInfinitesimal Δ) : hyperLowerSum f a b Δ ≊ I := by
  obtain ⟨hf, hL, hU⟩ := h
  obtain ⟨B, hB⟩ := hf
  rw [infClose_iff_abs_lt]
  intro η hη
  obtain ⟨δ, hδ, hδη⟩ : ∃ δ : ℝ, 0 < δ ∧ δ + δ = η := ⟨η / 2, half_pos hη, add_halves η⟩
  obtain ⟨_, ⟨P1, rfl⟩, hP1, -⟩ := hL.exists_between (sub_lt_self I hδ)
  obtain ⟨_, ⟨P2, rfl⟩, -, hP2⟩ := hU.exists_between (lt_add_of_pos_right I hη)
  have h1 := P2.hyperLowerSum_le_upperSum ⟨B, hB⟩ hΔ.1
  have h2 := sub_mul_le_hyperLowerSum P1 hB hΔ.1
  have h3 := coe_mul_posInfinitesimal_lt (8 * B * P1.n) hΔ hδ
  have h4 : ((I - δ : ℝ) : ℝ*) < (P1.lowerSum f : ℝ) := Hyperreal.coe_lt_coe.2 hP1
  have h5 : ((P2.upperSum f : ℝ) : ℝ*) < ((I + η : ℝ) : ℝ*) := Hyperreal.coe_lt_coe.2 hP2
  have h6 : (η : ℝ*) = δ + δ := by rw [← hδη, Hyperreal.coe_add]
  rw [Hyperreal.coe_sub] at h4
  rw [Hyperreal.coe_add] at h5
  rw [abs_lt]
  constructor <;> linarith

/-- **Section 9.2.** If $`f` is Riemann integrable on $`[a, b]`, then for every positive
infinitesimal $`\Delta x`,
$$`L_a^b(f, \Delta x) \simeq U_a^b(f, \Delta x).` -/
theorem HasRiemannIntegral.hyperLowerSum_infClose_hyperUpperSum (h : HasRiemannIntegral f a b I)
    (hΔ : PosInfinitesimal Δ) : hyperLowerSum f a b Δ ≊ hyperUpperSum f a b Δ :=
  (h.hyperLowerSum_infClose hΔ).trans (h.hyperUpperSum_infClose hΔ).symm

/-- **Section 9.2.** If $`f` is Riemann integrable on $`[a, b]` with integral $`I`, then the
ordinary Riemann sum of every positive infinitesimal width is infinitely close to $`I`. -/
theorem HasRiemannIntegral.hyperOrdSum_infClose (h : HasRiemannIntegral f a b I)
    (hΔ : PosInfinitesimal Δ) : hyperOrdSum f a b Δ ≊ I :=
  infClose_of_le_of_le (hyperLowerSum_le_hyperOrdSum h.1 h.le hΔ.1)
    (hyperOrdSum_le_hyperUpperSum h.1 h.le hΔ.1) (h.hyperLowerSum_infClose hΔ)
    (h.hyperUpperSum_infClose hΔ)

/-- **Section 9.2, formula (iii).** For a Riemann integrable function and _any_ positive
infinitesimal $`\Delta x`,
$$`\int_a^b f(x)\,dx = \operatorname{sh}\bigl(S_a^b(f, \Delta x)\bigr).` -/
theorem RiemannIntegrableOn.riemannIntegral_eq_sh (h : RiemannIntegrableOn f a b)
    (hΔ : PosInfinitesimal Δ) : riemannIntegral f a b = sh (hyperOrdSum f a b Δ) :=
  (sh_eq_of_infClose (h.hasRiemannIntegral.hyperOrdSum_infClose hΔ)).symm

/-- **Section 9.2.** The ordinary Riemann sum of an integrable function for a positive
infinitesimal width is infinitely close to the integral. -/
theorem RiemannIntegrableOn.hyperOrdSum_infClose (h : RiemannIntegrableOn f a b)
    (hΔ : PosInfinitesimal Δ) : hyperOrdSum f a b Δ ≊ riemannIntegral f a b :=
  h.hasRiemannIntegral.hyperOrdSum_infClose hΔ

/-- **Section 9.2, the characterisation of integrability.** A function $`f` that is bounded
on $`[a, b]` is Riemann integrable there if and only if
$$`L_a^b(f, \Delta x) \simeq U_a^b(f, \Delta x)\quad\text{for all positive infinitesimals }\Delta x.` -/
theorem riemannIntegrableOn_iff_forall_infClose (hab : a ≤ b) :
    RiemannIntegrableOn f a b ↔ BoundedOn f (Icc a b) ∧
      ∀ Δ : ℝ*, PosInfinitesimal Δ → hyperLowerSum f a b Δ ≊ hyperUpperSum f a b Δ := by
  constructor
  · intro h
    exact ⟨h.boundedOn, fun Δ hΔ => h.hasRiemannIntegral.hyperLowerSum_infClose_hyperUpperSum hΔ⟩
  · rintro ⟨hf, h⟩
    have hη : PosInfinitesimal (ε : ℝ*) := epsilon_pos_infinitesimal
    exact ⟨_, hasRiemannIntegral_sh_of_infClose hf hab hη (h _ hη)⟩

/-- **Section 9.2.** For integrability it is enough that the lower and upper sums be
infinitely close for _one_ positive infinitesimal width: a bounded function $`f` is Riemann
integrable on $`[a, b]` if and only if
$`L_a^b(f, \Delta x) \simeq U_a^b(f, \Delta x)` for some positive infinitesimal
$`\Delta x`. -/
theorem riemannIntegrableOn_iff_exists_infClose (hab : a ≤ b) :
    RiemannIntegrableOn f a b ↔ BoundedOn f (Icc a b) ∧
      ∃ Δ : ℝ*, PosInfinitesimal Δ ∧ hyperLowerSum f a b Δ ≊ hyperUpperSum f a b Δ := by
  constructor
  · intro h
    have hη : PosInfinitesimal (ε : ℝ*) := epsilon_pos_infinitesimal
    exact ⟨h.boundedOn, ε, hη, h.hasRiemannIntegral.hyperLowerSum_infClose_hyperUpperSum hη⟩
  · rintro ⟨hf, Δ, hΔ, h⟩
    exact ⟨_, hasRiemannIntegral_sh_of_infClose hf hab hΔ h⟩

/-- **Section 9.1, conditions (1) and (2).** A function $`f` bounded on $`[a, b]` is Riemann
integrable with integral $`I` if and only if

1. $`L_a^b(f, P) \le I \le U_a^b(f, P)` for all partitions $`P` of $`[a, b]`, and
2. for every real $`\varepsilon > 0` there is a partition $`P` with
   $`U_a^b(f, P) - L_a^b(f, P) < \varepsilon`.

The partition in (2) is obtained here from an infinitesimal one by existential transfer. -/
theorem hasRiemannIntegral_iff_conditions :
    HasRiemannIntegral f a b I ↔ BoundedOn f (Icc a b) ∧
      (∀ P : IntervalPartition a b, P.lowerSum f ≤ I ∧ I ≤ P.upperSum f) ∧
      ∀ η : ℝ, 0 < η → ∃ P : IntervalPartition a b, P.upperSum f - P.lowerSum f < η := by
  constructor
  · intro h
    refine ⟨h.1, fun P => ⟨h.2.1.1 (P.lowerSum_mem f), h.2.2.1 (P.upperSum_mem f)⟩, fun η hη => ?_⟩
    have hε : PosInfinitesimal (ε : ℝ*) := epsilon_pos_infinitesimal
    obtain ⟨t, ht, hlt⟩ := exists_pos_upperSum_sub_lowerSum_lt hε.1
      (h.hyperLowerSum_infClose_hyperUpperSum hε) hη
    exact ⟨meshPartition h.le ht, hlt⟩
  · rintro ⟨hf, h1, h2⟩
    exact hasRiemannIntegral_of_conditions hf h1 h2

/-- **Section 9.2.** A function that is continuous on $`[a, b]` is Riemann integrable on
$`[a, b]`. -/
theorem riemannIntegrableOn_of_continuousOn (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    RiemannIntegrableOn f a b :=
  (riemannIntegrableOn_iff_forall_infClose hab).2 ⟨boundedOn_Icc_of_continuousOn hf,
    fun _ hΔ => hyperLowerSum_infClose_hyperUpperSum_of_continuousOn hab hf hΔ⟩

/-- **Section 9.2.** A function that is nondecreasing on $`[a, b]` is Riemann integrable on
$`[a, b]`. -/
theorem riemannIntegrableOn_of_monotoneOn (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) :
    RiemannIntegrableOn f a b :=
  (riemannIntegrableOn_iff_forall_infClose hab).2 ⟨boundedOn_Icc_of_monotoneOn hf,
    fun _ hΔ => hyperLowerSum_infClose_hyperUpperSum_of_monotoneOn hab hf hΔ⟩

/-- **Section 9.2.** A function that is nonincreasing on $`[a, b]` is Riemann integrable on
$`[a, b]`. -/
theorem riemannIntegrableOn_of_antitoneOn (hab : a ≤ b) (hf : AntitoneOn f (Icc a b)) :
    RiemannIntegrableOn f a b :=
  (riemannIntegrableOn_iff_forall_infClose hab).2 ⟨boundedOn_Icc_of_antitoneOn hf,
    fun _ hΔ => hyperLowerSum_infClose_hyperUpperSum_of_antitoneOn hab hf hΔ⟩

/-- **Section 9.2.** For a function continuous on $`[a, b]` and any positive infinitesimal
$`\Delta x`, $`\int_a^b f(x)\,dx = \operatorname{sh}\bigl(S_a^b(f, \Delta x)\bigr)`. -/
theorem riemannIntegral_eq_sh_of_continuousOn (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hΔ : PosInfinitesimal Δ) : riemannIntegral f a b = sh (hyperOrdSum f a b Δ) :=
  (riemannIntegrableOn_of_continuousOn hab hf).riemannIntegral_eq_sh hΔ

/-- **Chapter 9, tool.** A positive hyperreal that is infinitely close to $`0` is a positive
infinitesimal. -/
theorem posInfinitesimal_of_pos_of_infClose_zero (hpos : 0 < Δ) (h : Δ ≊ ((0 : ℝ) : ℝ*)) :
    PosInfinitesimal Δ := by
  refine ⟨hpos, fun r hr => ?_⟩
  have h' : Infinitesimal Δ := by simpa [infClose_iff] using h
  exact (le_abs_self _).trans_lt (infinitesimal_iff_abs_lt.1 h' r hr)

/-- **Section 9.2, the integral as a limit.** For a Riemann integrable function,
$$`\int_a^b f(x)\,dx = \lim_{\Delta x \to 0^+} S_a^b(f, \Delta x).`
This is the standard reading of formula (iii), by the characterisation of one-sided limits
in Section 7.3. -/
theorem RiemannIntegrableOn.tendsto_ordSum (h : RiemannIntegrableOn f a b) :
    Tendsto (ordSum f a b) (𝓝[>] 0) (𝓝 (riemannIntegral f a b)) := by
  have key := (tendsto_nhdsWithin_Ioi_iff_infClose (f := ordSum f a b) (A := univ) (c := 0)
    (L := riemannIntegral f a b)).2 fun x _ hx0 hpos =>
      h.hyperOrdSum_infClose (posInfinitesimal_of_pos_of_infClose_zero
        (by simpa using hpos) hx0)
  rwa [univ_inter] at key

/-- **Section 9.2, the standard approximation property.** For a Riemann integrable function
the difference $`U_a^b(f, \Delta x) - L_a^b(f, \Delta x)` tends to $`0` as $`\Delta x` tends
to $`0` through positive values. The book quotes this from the standard theory and transfers
it; here it is read off from the infinitesimal statement
{name}`HasRiemannIntegral.hyperLowerSum_infClose_hyperUpperSum`, which was proved from the
standard estimate {name}`upperSum_le_add_mul`. -/
theorem RiemannIntegrableOn.tendsto_upperSum_sub_lowerSum (h : RiemannIntegrableOn f a b) :
    Tendsto (fun t => upperSum f a b t - lowerSum f a b t) (𝓝[>] 0) (𝓝 0) := by
  have key := (tendsto_nhdsWithin_Ioi_iff_infClose
    (f := fun t => upperSum f a b t - lowerSum f a b t) (A := univ) (c := 0) (L := 0)).2
    fun x _ hx0 hpos => by
      have hx : PosInfinitesimal x :=
        posInfinitesimal_of_pos_of_infClose_zero (by simpa using hpos) hx0
      have hi : Infinitesimal (hyperUpperSum f a b x - hyperLowerSum f a b x) :=
        (h.hasRiemannIntegral.hyperLowerSum_infClose_hyperUpperSum hx).symm
      rw [starMap_sub_apply, infClose_iff, Hyperreal.coe_zero, sub_zero]
      exact hi
  rwa [univ_inter] at key

/-- **Section 9.2, the standard approximation property, with $`\varepsilon` and
$`\delta`.** If $`f` is Riemann integrable on $`[a, b]`, then for every real
$`\varepsilon > 0` there is a real $`\delta > 0` such that
$`U_a^b(f, \Delta x) - L_a^b(f, \Delta x) < \varepsilon` for all real $`\Delta x` with
$`0 < \Delta x < \delta`. -/
theorem RiemannIntegrableOn.exists_pos_forall_upperSum_sub_lowerSum_lt
    (h : RiemannIntegrableOn f a b) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → upperSum f a b t - lowerSum f a b t < η := by
  obtain ⟨δ, hδ, hδ'⟩ := (Metric.tendsto_nhdsWithin_nhds.1 h.tendsto_upperSum_sub_lowerSum) η hη
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  have := hδ' (mem_Ioi.2 ht) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; exact htδ)
  rw [Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans_lt this

/-- **Section 9.2.** The integral over a degenerate interval is zero: every function is
integrable on $`[a, a]`, with integral $`0`. -/
theorem hasRiemannIntegral_self (f : ℝ → ℝ) (a : ℝ) : HasRiemannIntegral f a a 0 := by
  have hf : BoundedOn f (Icc a a) := ⟨|f a|, fun x hx => by rw [le_antisymm hx.2 hx.1]⟩
  have hη : PosInfinitesimal (ε : ℝ*) := epsilon_pos_infinitesimal
  have h0 : ∀ g : ℝ → ℝ → ℝ, ∀ t : ℝ, meshSumOf g a a t = 0 := fun g t => by
    simp [meshSumOf, meshCard]
  have hU : hyperUpperSum f a a ε = 0 := by
    obtain ⟨r, hr⟩ := hyperreal_exists_rep (ε : ℝ*)
    rw [hr, hyperUpperSum_ofSeq]
    simp only [upperSum, h0]
    rfl
  have hL : hyperLowerSum f a a ε = 0 := by
    obtain ⟨r, hr⟩ := hyperreal_exists_rep (ε : ℝ*)
    rw [hr, hyperLowerSum_ofSeq]
    simp only [lowerSum, h0]
    rfl
  have hS : hyperOrdSum f a a ε = 0 := by
    obtain ⟨r, hr⟩ := hyperreal_exists_rep (ε : ℝ*)
    rw [hr, hyperOrdSum_ofSeq]
    simp only [ordSum, h0]
    rfl
  have := hasRiemannIntegral_sh_of_infClose hf le_rfl hη (by rw [hU, hL])
  rwa [hS, ← Hyperreal.coe_zero, sh_coe] at this

/-- **Section 9.2.** $`\int_a^a f(x)\,dx = 0`. -/
theorem riemannIntegral_self (f : ℝ → ℝ) (a : ℝ) : riemannIntegral f a a = 0 :=
  (hasRiemannIntegral_self f a).riemannIntegral_eq

end Integrability

/-!
### A bounded function that is not integrable

The definition of integrability is not vacuous in either direction: continuous and monotonic
functions satisfy it, and the function that is $`1` at rational points and $`0` at irrational
points (the third test function of Exercise 7.4(3)) does not. Every subinterval of every
partition contains rational and irrational points, so every upper sum is $`b - a` and every
lower sum is $`0`.
-/

section Dirichlet

variable {a b : ℝ}

/-- The values of the indicator function of the rationals lie between $`0` and $`1`. -/
theorem ratIndicator_mem_Icc (t : ℝ) : ratIndicator t ∈ Icc (0 : ℝ) 1 := by
  unfold ratIndicator
  split_ifs <;> constructor <;> norm_num

/-- The indicator function of the rationals is bounded on every set. -/
theorem boundedOn_ratIndicator (A : Set ℝ) : BoundedOn ratIndicator A :=
  ⟨1, fun t _ => abs_le.2 ⟨by linarith [(ratIndicator_mem_Icc t).1], (ratIndicator_mem_Icc t).2⟩⟩

/-- **Section 9.1, example.** Every upper sum of the indicator function of the rationals on
$`[a, b]` is $`b - a`. -/
theorem IntervalPartition.upperSum_ratIndicator (P : IntervalPartition a b) :
    P.upperSum ratIndicator = b - a := by
  have h : ∀ i < P.n, supOn ratIndicator (P.pt i) (P.pt (i + 1)) = 1 := fun i hi => by
    have hlt := P.lt_succ i hi
    refine le_antisymm (supOn_le hlt.le fun t _ => (ratIndicator_mem_Icc t).2) ?_
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hq : ratIndicator q = 1 := by simp [ratIndicator]
    rw [← hq]
    exact le_supOn (boundedOn_ratIndicator _) ⟨hq1.le, hq2.le⟩
  rw [← one_mul (b - a), ← P.sum_const_mul 1, IntervalPartition.upperSum, IntervalPartition.sum,
    IntervalPartition.sum]
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

/-- **Section 9.1, example.** Every lower sum of the indicator function of the rationals is
$`0`. -/
theorem IntervalPartition.lowerSum_ratIndicator (P : IntervalPartition a b) :
    P.lowerSum ratIndicator = 0 := by
  have h : ∀ i < P.n, infOn ratIndicator (P.pt i) (P.pt (i + 1)) = 0 := fun i hi => by
    have hlt := P.lt_succ i hi
    refine le_antisymm ?_ (le_infOn hlt.le fun t _ => (ratIndicator_mem_Icc t).1)
    obtain ⟨r, hr, hr1, hr2⟩ := exists_irrational_btwn hlt
    have hq : ratIndicator r = 0 := by simp [ratIndicator, hr]
    rw [← hq]
    exact infOn_le (boundedOn_ratIndicator _) ⟨hr1.le, hr2.le⟩
  rw [IntervalPartition.lowerSum, IntervalPartition.sum]
  exact Finset.sum_eq_zero fun i hi => by rw [h i (Finset.mem_range.1 hi), zero_mul]

/-- **Section 9.1, example.** The indicator function of the rationals is bounded but not
Riemann integrable on any interval $`[a, b]` with $`a < b`: condition (2) fails, since
$`U_a^b(f, P) - L_a^b(f, P) = b - a` for every partition. -/
theorem not_riemannIntegrableOn_ratIndicator (hab : a < b) :
    ¬ RiemannIntegrableOn ratIndicator a b := by
  rintro ⟨I, hI⟩
  obtain ⟨-, -, h2⟩ := hasRiemannIntegral_iff_conditions.1 hI
  obtain ⟨P, hP⟩ := h2 (b - a) (sub_pos.2 hab)
  rw [P.upperSum_ratIndicator, P.lowerSum_ratIndicator] at hP
  linarith

/-- **Section 9.2, example.** For the indicator function of the rationals on $`[a, b]`,
$`a < b`, the lower and upper sums of an infinitesimal width are _not_ infinitely close. -/
theorem not_infClose_hyperLowerSum_hyperUpperSum_ratIndicator (hab : a < b) {Δ : ℝ*}
    (hΔ : PosInfinitesimal Δ) :
    ¬ hyperLowerSum ratIndicator a b Δ ≊ hyperUpperSum ratIndicator a b Δ := fun h =>
  not_riemannIntegrableOn_ratIndicator hab
    ((riemannIntegrableOn_iff_exists_infClose hab.le).2 ⟨boundedOn_ratIndicator _, Δ, hΔ, h⟩)

end Dirichlet

/-!
### Exercise 9.2.1: Riemann sums indexed by the number of subintervals

Instead of the width, one can use the number $`n` of subintervals as the variable, taking
$`\Delta x = (b - a)/n`. The three sums become sequences, which extend to the hypernaturals
as in Chapter 6. For an unlimited $`N` the width $`(b - a)/N` is a positive infinitesimal, so
everything proved above applies: this is the development the exercise asks for.
-/

section ByCount

variable {f : ℝ → ℝ} {a b : ℝ} {N : ℝ*}

/-- **Exercise 9.2.1.** The upper Riemann sum $`U_a^b(f, n)` for the partition of $`[a, b]`
determined by the width $`(b - a)/n`. -/
def upperSumN (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ := upperSum f a b ((b - a) / n)

/-- **Exercise 9.2.1.** The lower Riemann sum $`L_a^b(f, n)` for the partition of $`[a, b]`
determined by the width $`(b - a)/n`. -/
def lowerSumN (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ := lowerSum f a b ((b - a) / n)

/-- **Exercise 9.2.1.** The ordinary Riemann sum $`S_a^b(f, n)` for the partition of
$`[a, b]` determined by the width $`(b - a)/n`. -/
def ordSumN (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ := ordSum f a b ((b - a) / n)

/-- **Exercise 9.2.1.** At a hypernatural $`N` the extended sequence of upper sums is the
extended upper sum of width $`(b - a)/N`. -/
theorem hyperSeq_upperSumN (f : ℝ → ℝ) (a b : ℝ) (hN : N ∈ ℕ*) :
    hyperSeq (upperSumN f a b) N = hyperUpperSum f a b (((b - a : ℝ) : ℝ*) / N) := by
  obtain ⟨k, rfl⟩ := exists_hnat_eq hN
  rw [hyperSeq_hnat]
  rfl

/-- **Exercise 9.2.1.** At a hypernatural $`N` the extended sequence of lower sums is the
extended lower sum of width $`(b - a)/N`. -/
theorem hyperSeq_lowerSumN (f : ℝ → ℝ) (a b : ℝ) (hN : N ∈ ℕ*) :
    hyperSeq (lowerSumN f a b) N = hyperLowerSum f a b (((b - a : ℝ) : ℝ*) / N) := by
  obtain ⟨k, rfl⟩ := exists_hnat_eq hN
  rw [hyperSeq_hnat]
  rfl

/-- **Exercise 9.2.1.** At a hypernatural $`N` the extended sequence of ordinary sums is the
extended ordinary sum of width $`(b - a)/N`. -/
theorem hyperSeq_ordSumN (f : ℝ → ℝ) (a b : ℝ) (hN : N ∈ ℕ*) :
    hyperSeq (ordSumN f a b) N = hyperOrdSum f a b (((b - a : ℝ) : ℝ*) / N) := by
  obtain ⟨k, rfl⟩ := exists_hnat_eq hN
  rw [hyperSeq_hnat]
  rfl

/-- **Exercise 9.2.1.** If $`a < b` and $`N` is an unlimited hypernatural, the width
$`(b - a)/N` is a positive infinitesimal. -/
theorem posInfinitesimal_width (hab : a < b) (hN : N ∈ unlimitedHyperNat) :
    PosInfinitesimal (((b - a : ℝ) : ℝ*) / N) := by
  have hN0 : (0 : ℝ*) < N := by simpa using natCast_lt_of_mem_unlimitedHyperNat hN 0
  have hpos : (0 : ℝ*) < ((b - a : ℝ) : ℝ*) / N :=
    div_pos (Hyperreal.coe_pos.2 (sub_pos.2 hab)) hN0
  have hinf := infinitesimal_width hN a b
  exact ⟨hpos, fun r hr => (le_abs_self _).trans_lt (infinitesimal_iff_abs_lt.1 hinf r hr)⟩

/-- **Exercise 9.2.1, first part.** If $`f` is Riemann integrable on $`[a, b]` (for instance
continuous or monotonic) and $`N` is an unlimited hypernatural, then
$$`L_a^b(f, N) \simeq S_a^b(f, N) \simeq U_a^b(f, N).` -/
theorem RiemannIntegrableOn.hyperSeq_lowerSumN_infClose (h : RiemannIntegrableOn f a b)
    (hab : a < b) (hN : N ∈ unlimitedHyperNat) :
    hyperSeq (lowerSumN f a b) N ≊ hyperSeq (ordSumN f a b) N ∧
      hyperSeq (ordSumN f a b) N ≊ hyperSeq (upperSumN f a b) N := by
  rw [hyperSeq_lowerSumN f a b hN.1, hyperSeq_ordSumN f a b hN.1, hyperSeq_upperSumN f a b hN.1]
  have hΔ := posInfinitesimal_width hab hN
  exact infClose_between (hyperLowerSum_le_hyperOrdSum h.boundedOn hab.le hΔ.1)
    (hyperOrdSum_le_hyperUpperSum h.boundedOn hab.le hΔ.1)
    (h.hasRiemannIntegral.hyperLowerSum_infClose_hyperUpperSum hΔ)

/-- **Exercise 9.2.1, second part (integrability by counting).** For $`a < b`, a bounded
function is Riemann integrable on $`[a, b]` if and only if
$`L_a^b(f, N) \simeq U_a^b(f, N)` for every unlimited hypernatural $`N`. -/
theorem riemannIntegrableOn_iff_forall_unlimited (hab : a < b) :
    RiemannIntegrableOn f a b ↔ BoundedOn f (Icc a b) ∧
      ∀ N ∈ unlimitedHyperNat, hyperSeq (lowerSumN f a b) N ≊ hyperSeq (upperSumN f a b) N := by
  constructor
  · intro h
    refine ⟨h.boundedOn, fun N hN => ?_⟩
    obtain ⟨h1, h2⟩ := h.hyperSeq_lowerSumN_infClose hab hN
    exact h1.trans h2
  · rintro ⟨hf, h⟩
    have hω := omega_mem_unlimitedHyperNat
    have := h _ hω
    rw [hyperSeq_lowerSumN f a b hω.1, hyperSeq_upperSumN f a b hω.1] at this
    exact (riemannIntegrableOn_iff_exists_infClose hab.le).2
      ⟨hf, _, posInfinitesimal_width hab hω, this⟩

/-- **Exercise 9.2.1, second part (the integral by counting).** For a function that is
Riemann integrable on $`[a, b]`, $`a < b`, and every unlimited hypernatural $`N`,
$$`\int_a^b f(x)\,dx = \operatorname{sh}\bigl(S_a^b(f, N)\bigr).` -/
theorem RiemannIntegrableOn.riemannIntegral_eq_sh_hyperSeq (h : RiemannIntegrableOn f a b)
    (hab : a < b) (hN : N ∈ unlimitedHyperNat) :
    riemannIntegral f a b = sh (hyperSeq (ordSumN f a b) N) := by
  rw [hyperSeq_ordSumN f a b hN.1]
  exact h.riemannIntegral_eq_sh (posInfinitesimal_width hab hN)

/-- **Exercise 9.2.1, second part (the integral as the limit of a sequence).** For a
function that is Riemann integrable on $`[a, b]`, $`a < b`, the sequence of Riemann sums
$`S_a^b(f, n)` converges to the integral. -/
theorem RiemannIntegrableOn.tendsto_ordSumN (h : RiemannIntegrableOn f a b) (hab : a < b) :
    Tendsto (ordSumN f a b) atTop (𝓝 (riemannIntegral f a b)) := by
  rw [tendsto_iff_forall_unlimited_infClose]
  intro N hN
  rw [hyperSeq_ordSumN f a b hN.1]
  exact h.hyperOrdSum_infClose (posInfinitesimal_width hab hN)

end ByCount

end Goldblatt
