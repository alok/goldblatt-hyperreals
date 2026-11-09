import Mathlib
import Goldblatt.Ch02_LargeSets
import Goldblatt.Ch03_Ultrapower
import Goldblatt.Ch05_GreatAndSmall
import Goldblatt.Ch06_Sequences

/-!
# 7 (part 1). Continuity and Limits of Functions: Sections 7.1 to 7.4

This is the first of three parts of Chapter 7 (the overview is on the chapter page
{lit}`Goldblatt.Ch07_Continuity`). It proves the infinitesimal characterisation of continuity
at a point, with and without a restricting domain, deduces the continuity of the sine function
from the addition formula, characterises the seven kinds of limit of a function listed in
Section 7.3, and works through the exercises on limits, including the five test functions of
Exercise 7.4(3).
-/

noncomputable section

universe u v

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## Functions on a domain, and the transfer tools of the chapter

The book considers a real function $`f` defined on a set $`A` of reals, and regards its
extension as defined on the enlargement of $`A`. In this formalization a function is total,
of type {lit}`ℝ → ℝ`, and the domain $`A` appears as a restriction in the statement: continuity
on $`A` is Mathlib's {name}`ContinuousWithinAt` and {name}`ContinuousOn`, and on the hyperreal
side the points $`x` are required to lie in the enlargement {lit}`⋆A`. The values of $`f`
outside $`A` never matter. For an open interval the enlargement is the hyperreal interval with
the same end points ({name}`starSet_Ioo_real`), which is the remark that opens the chapter.

This preliminary section is not a numbered section of the book. It collects, once and for all,
the two transfer arguments that the book repeats for each kind of limit.

The first tool handles every statement of the form "$`f(x)` tends to something as $`x` tends to
something". Such a statement is a convergence of filters. To a filter one associates the set of
those elements of the ultrapower that belong to the enlargement of each of its members; for the
neighbourhood filter of a real number $`c` this set is the halo of $`c`, and for the filter of
neighbourhoods of plus infinity it is the set of positive unlimited hyperreals. A function
converges along one filter to another exactly when its extension maps the first set into the
second. One direction is universal transfer. The other is existential transfer in its
ultrapower form: if the convergence fails, the failure is witnessed arbitrarily far along the
filter, and the sequence of witnesses is a nonstandard point at which the extension misbehaves.

The second tool is the permanence principle of Section 7.10: a set of reals whose enlargement
contains all points within some positive hyperreal distance of a real number $`c` already
contains all reals within some positive real distance of $`c`.
-/

section Tools

variable {α αS : Type u} {β βS : Type v} [StarType α αS] [StarType β βS]

/-- **Chapter 7, transfer tool.** The set of elements of the ultrapower that lie in the
enlargement of every member of a filter. For the neighbourhood filter of a real number this is
its halo, and for the filter at infinity it is the set of positive unlimited numbers. -/
def filterMonad (l : Filter α) : Set αS := {x | ∀ S ∈ l, x ∈ ⋆S}

/-- **Chapter 7, transfer tool.** The class of a sequence belongs to the set associated with a
filter exactly when the sequence converges to that filter along the index ultrafilter. -/
theorem ofSeq_mem_filterMonad {l : Filter α} {r : ℕ → α} :
    (ofSeq r : αS) ∈ filterMonad l ↔ Tendsto r (hyperfilter ℕ) l := by
  simp only [filterMonad, mem_ofPred_eq, ofSeq_mem_starSet, tendsto_def]
  rfl

/-- **Chapter 7, transfer tool**, for hyperreals. -/
theorem hyperreal_ofSeq_mem_filterMonad {l : Filter ℝ} {r : ℕ → ℝ} :
    Hyperreal.ofSeq r ∈ filterMonad l ↔ Tendsto r (hyperfilter ℕ) l :=
  ofSeq_mem_filterMonad

/-- **Chapter 7, transfer tool.** A filter that is larger has a larger associated set. -/
theorem filterMonad_mono {l l' : Filter α} (h : l ≤ l') :
    (filterMonad l : Set αS) ⊆ filterMonad l' :=
  fun _ hx S hS => hx S (h hS)

/-- **Chapter 7, transfer tool.** Restricting a filter to a set $`A` intersects its associated
set with the enlargement of $`A`. -/
theorem filterMonad_inf_principal (l : Filter α) (A : Set α) :
    (filterMonad (l ⊓ 𝓟 A) : Set αS) = filterMonad l ∩ ⋆A := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_inter_iff, ofSeq_mem_filterMonad, tendsto_inf, tendsto_principal,
    ofSeq_mem_starSet]

/-- **Chapter 7, transfer tool (limits by transfer).** Let $`f` be a function and let the
filter in the domain be countably generated, as are all filters on the real line used in this
chapter. Then $`f` converges along the first filter to the second if and only if the extension
of $`f` maps the set associated with the first filter into the set associated with the second.

The forward direction is universal transfer. For the converse, if the convergence fails then
there is a member $`S` of the target filter such that every member of the source filter
contains a point that $`f` sends outside $`S`; choosing such points in a decreasing basis of
the source filter gives a sequence whose class contradicts the hypothesis. -/
theorem tendsto_iff_starMap_mem_filterMonad {f : α → β} {l : Filter α} {l' : Filter β}
    [l.IsCountablyGenerated] :
    Tendsto f l l' ↔ ∀ x ∈ (filterMonad l : Set αS), ⋆f x ∈ (filterMonad l' : Set βS) := by
  constructor
  · intro h x hx
    obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
    rw [starMap_ofSeq, ofSeq_mem_filterMonad]
    exact h.comp (ofSeq_mem_filterMonad.1 hx)
  · intro h
    by_contra hne
    obtain ⟨S, hS, hne⟩ : ∃ S ∈ l', f ⁻¹' S ∉ l := by
      simpa [tendsto_def] using hne
    obtain ⟨B, hB⟩ := l.exists_antitone_basis
    have hex : ∀ n, ∃ a ∈ B n, f a ∉ S := fun n => by
      by_contra hcon
      push Not at hcon
      exact hne (mem_of_superset (hB.mem n) hcon)
    choose r hrB hrS using hex
    have hr : Tendsto r (hyperfilter ℕ) l :=
      (hB.tendsto hrB).mono_left Nat.hyperfilter_le_atTop
    have := h (ofSeq r) (ofSeq_mem_filterMonad.2 hr)
    rw [starMap_ofSeq, ofSeq_mem_filterMonad] at this
    obtain ⟨n, hn⟩ := (this.eventually_mem hS).exists
    exact hrS n hn

/-- **Chapter 7, transfer tool.** The set associated with the neighbourhood filter of a real
number $`c` is the halo of $`c`: the hyperreals infinitely close to $`c`. -/
theorem mem_filterMonad_nhds {x : ℝ*} {c : ℝ} : x ∈ filterMonad (𝓝 c) ↔ x ≊ c := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [hyperreal_ofSeq_mem_filterMonad, ofSeq_infClose_coe_iff]

/-- **Chapter 7, transfer tool.** The set associated with the filter at plus infinity is the
set of positive unlimited hyperreals. -/
theorem mem_filterMonad_atTop {x : ℝ*} : x ∈ filterMonad (atTop : Filter ℝ) ↔ PosUnlimited x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [hyperreal_ofSeq_mem_filterMonad, tendsto_atTop]
  constructor
  · intro h b
    rw [coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
    exact (h (b + 1)).mono fun n hn => by linarith
  · intro h b
    have := h b
    rw [coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff] at this
    exact this.mono fun n hn => hn.le

/-- **Chapter 7, transfer tool.** The set associated with the filter at minus infinity is the
set of negative unlimited hyperreals. -/
theorem mem_filterMonad_atBot {x : ℝ*} : x ∈ filterMonad (atBot : Filter ℝ) ↔ NegUnlimited x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [hyperreal_ofSeq_mem_filterMonad, tendsto_atBot]
  constructor
  · intro h b
    rw [coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
    exact (h (b - 1)).mono fun n hn => by linarith
  · intro h b
    have := h b
    rw [coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff] at this
    exact this.mono fun n hn => hn.le

variable {f g : ℝ → ℝ} {A S : Set ℝ} {c L M : ℝ} {x y : ℝ*}

/-- **Chapter 7, transfer tool.** Limits of a real function along a filter restricted to a set
$`S`: the extension has to send the points of the enlargement of $`S` that are associated with
the source filter to points associated with the target filter. -/
theorem tendsto_inf_principal_iff_filterMonad {l l' : Filter ℝ} [l.IsCountablyGenerated] :
    Tendsto f (l ⊓ 𝓟 S) l' ↔ ∀ x ∈ ⋆S, x ∈ filterMonad l → ⋆f x ∈ filterMonad l' := by
  rw [tendsto_iff_starMap_mem_filterMonad (αS := ℝ*) (βS := ℝ*), filterMonad_inf_principal]
  exact ⟨fun h x hS hx => h x ⟨hx, hS⟩, fun h x hx => h x hx.2 hx.1⟩

/-- **Chapter 7, transfer tool.** The extension of a pointwise sum is the sum of the
extensions. -/
theorem starMap_add_apply (f g : ℝ → ℝ) (x : ℝ*) :
    ⋆(fun t : ℝ => f t + g t) x = ⋆f x + ⋆g x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- **Chapter 7, transfer tool.** The extension of a pointwise difference is the difference of
the extensions. -/
theorem starMap_sub_apply (f g : ℝ → ℝ) (x : ℝ*) :
    ⋆(fun t : ℝ => f t - g t) x = ⋆f x - ⋆g x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- **Chapter 7, transfer tool.** The extension of a pointwise negative is the negative of the
extension. -/
theorem starMap_neg_apply (f : ℝ → ℝ) (x : ℝ*) : ⋆(fun t : ℝ => -f t) x = -⋆f x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- **Chapter 7, transfer tool.** The extension of a pointwise product is the product of the
extensions. -/
theorem starMap_mul_apply (f g : ℝ → ℝ) (x : ℝ*) :
    ⋆(fun t : ℝ => f t * g t) x = ⋆f x * ⋆g x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- **Chapter 7, transfer tool.** The extension of a pointwise quotient is the quotient of the
extensions. -/
theorem starMap_div_apply (f g : ℝ → ℝ) (x : ℝ*) :
    ⋆(fun t : ℝ => f t / g t) x = ⋆f x / ⋆g x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- **Chapter 7, transfer tool.** The extension of a constant function is constant. -/
theorem starMap_const_apply (b : ℝ) (x : ℝ*) : ⋆(fun _ : ℝ => b) x = (b : ℝ*) := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- **Chapter 7, transfer tool.** The extension of the identity function is the identity. -/
theorem starMap_id_apply (x : ℝ*) : ⋆(fun t : ℝ => t) x = x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- **Chapter 7, transfer tool (universal transfer of an inequality on a set).** If
$`f(t) \le g(t)` for all $`t \in A`, then the extensions satisfy the same inequality at all
points of the enlargement of $`A`. -/
theorem starMap_le_starMap_of_mem (h : ∀ t ∈ A, f t ≤ g t) (hx : x ∈ ⋆A) : ⋆f x ≤ ⋆g x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [starMap_hyperreal_ofSeq, starMap_hyperreal_ofSeq, ofSeq_le_ofSeq_iff]
  exact (hyperreal_ofSeq_mem_starSet.1 hx).mono fun n hn => h _ hn

/-- **Chapter 7, transfer tool (universal transfer of a strict inequality on a set).** -/
theorem starMap_lt_starMap_of_mem (h : ∀ t ∈ A, f t < g t) (hx : x ∈ ⋆A) : ⋆f x < ⋆g x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [starMap_hyperreal_ofSeq, starMap_hyperreal_ofSeq, ofSeq_lt_ofSeq_iff]
  exact (hyperreal_ofSeq_mem_starSet.1 hx).mono fun n hn => h _ hn

/-- **Chapter 7, transfer tool.** The extension of the absolute value of a function is the
absolute value of the extension. -/
theorem starMap_abs_apply (f : ℝ → ℝ) (x : ℝ*) : ⋆(fun t : ℝ => |f t|) x = |⋆f x| := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [starMap_hyperreal_ofSeq, starMap_hyperreal_ofSeq, abs_ofSeq]

/-- **Chapter 7, transfer tool.** Membership in the enlargement of a set defined by an equation
$`f(t) = b` between a function and a constant. -/
theorem mem_starSet_setOf_eq {b : ℝ} : x ∈ ⋆{t : ℝ | f t = b} ↔ ⋆f x = b := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [hyperreal_ofSeq_mem_starSet, starMap_hyperreal_ofSeq, coe_eq_ofSeq_const,
    ofSeq_eq_ofSeq_iff]
  rfl

/-- **Section 7.10, Cauchy's principle (core).** Let $`c` be real, let $`d` be a positive
hyperreal, and let $`S` be a set of reals. If every hyperreal $`x` with $`|x - c| < d`
belongs to the enlargement of $`S`, then there is a real $`\delta > 0` such that every real
within $`\delta` of $`c` belongs to $`S`.

This is the existential transfer step of Theorem 7.1.1 and the content of Section 7.10; it is
proved here because it is used from Section 7.1 on. In the ultrapower the argument runs as
follows. Write $`d` as the class of a sequence $`d_n`, positive for almost all $`n`. If no
real $`\delta` works, then for each such $`n` there is a real $`x_n` outside $`S` with
$`|x_n - c| < d_n`. The class of the sequence $`x_n` is within $`d` of $`c` and is not in the
enlargement of $`S`. -/
theorem exists_real_radius_of_hyperreal_radius {d : ℝ*} (hd : 0 < d)
    (h : ∀ x : ℝ*, |x - c| < d → x ∈ ⋆S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - c| < δ → t ∈ S := by
  by_contra hne
  push Not at hne
  obtain ⟨dn, rfl⟩ := hyperreal_exists_rep d
  have hpos : ∀ᶠ n in hyperfilter ℕ, 0 < dn n := by
    have : Hyperreal.ofSeq (fun _ => (0 : ℝ)) < Hyperreal.ofSeq dn := hd
    exact ofSeq_lt_ofSeq_iff.1 this
  have hex : ∀ n, ∃ t : ℝ, 0 < dn n → |t - c| < dn n ∧ t ∉ S := fun n => by
    by_cases hn : 0 < dn n
    · obtain ⟨t, ht, htS⟩ := hne (dn n) hn
      exact ⟨t, fun _ => ⟨ht, htS⟩⟩
    · exact ⟨c, fun h => absurd h hn⟩
  choose r hr using hex
  have hx : |Hyperreal.ofSeq r - (c : ℝ*)| < Hyperreal.ofSeq dn := by
    have e : Hyperreal.ofSeq r - (c : ℝ*) = Hyperreal.ofSeq fun n => r n - c := rfl
    rw [e, abs_ofSeq, ofSeq_lt_ofSeq_iff]
    exact hpos.mono fun n hn => (hr n hn).1
  have hmem := hyperreal_ofSeq_mem_starSet.1 (h _ hx)
  obtain ⟨n, hn, hn'⟩ := (hpos.and hmem).exists
  exact (hr n hn).2 hn'

end Tools

/-!
## 7.1 Cauchy's Account of Continuity

Cauchy described a continuous function as one for which an infinitely small change of the
variable produces an infinitely small change of the value. Theorem 7.1.1 makes this literally
true: a real function $`f` is continuous at a real point $`c` exactly when the extension of
$`f` maps the halo of $`c` into the halo of $`f(c)`. Corollary 7.1.2 adds a third equivalent
condition, in which the halo is replaced by some interval of positive infinitesimal radius
around $`c`; that it suffices to look at such an interval is the first instance of
permanence. Theorem 7.1.3 is the same statement for a function restricted to a set $`A`,
where $`x` ranges over the enlargement of $`A`.

The standard side of each statement is Mathlib's {name}`ContinuousAt`,
{name}`ContinuousWithinAt` or {name}`ContinuousOn`; these unfold to the book's
$`\varepsilon`-$`\delta` sentence by {name}`Metric.continuousAt_iff` and
{name}`Metric.continuousWithinAt_iff`.
-/

section Continuity

variable {f g : ℝ → ℝ} {A : Set ℝ} {c L : ℝ} {x y : ℝ*}

/-- **Theorem 7.1.3, (1) if and only if (2).** A real function $`f` is continuous at the real
point $`c` relative to the set $`A` if and only if $`{}^*f(x) \simeq f(c)` for every
$`x \in {}^*A` with $`x \simeq c`. The book assumes $`c \in A`; the equivalence holds without
that assumption. -/
theorem continuousWithinAt_iff_infClose :
    ContinuousWithinAt f A c ↔ ∀ x ∈ ⋆A, x ≊ c → ⋆f x ≊ f c := by
  rw [ContinuousWithinAt, nhdsWithin, tendsto_inf_principal_iff_filterMonad]
  simp only [mem_filterMonad_nhds]

/-- **Theorem 7.1.1.** A real function $`f` is continuous at the real point $`c` if and only
if $`{}^*f(x) \simeq f(c)` for every hyperreal $`x \simeq c`. -/
theorem continuousAt_iff_infClose :
    ContinuousAt f c ↔ ∀ x : ℝ*, x ≊ c → ⋆f x ≊ f c := by
  rw [← continuousWithinAt_univ, continuousWithinAt_iff_infClose, starSet_univ]
  simp

/-- **Theorem 7.1.1**, in the language of halos: $`f` is continuous at $`c` if and only if
$`{}^*f(\operatorname{hal}(c)) \subseteq \operatorname{hal}(f(c))`. -/
theorem continuousAt_iff_image_hal_subset :
    ContinuousAt f c ↔ ⋆f '' hal (c : ℝ*) ⊆ hal ((f c : ℝ) : ℝ*) := by
  rw [continuousAt_iff_infClose, image_subset_iff]
  exact forall_congr' fun x => by
    rw [mem_hal, mem_preimage, mem_hal, infClose_comm, infClose_comm (b := ⋆f x)]

/-- **Theorem 7.1.1**, forward direction as a rule. -/
theorem _root_.ContinuousAt.starMap_infClose (h : ContinuousAt f c) (hx : x ≊ c) :
    ⋆f x ≊ f c :=
  continuousAt_iff_infClose.1 h x hx

/-- **Theorem 7.1.3**, forward direction as a rule. -/
theorem _root_.ContinuousWithinAt.starMap_infClose (h : ContinuousWithinAt f A c)
    (hA : x ∈ ⋆A) (hx : x ≊ c) : ⋆f x ≊ f c :=
  continuousWithinAt_iff_infClose.1 h x hA hx

/-- **Theorem 7.1.3**, for continuity on a set: $`f` is continuous on $`A` if and only if
$`{}^*f(x) \simeq f(c)` whenever $`c \in A`, $`x \in {}^*A` and $`x \simeq c`. This is the
form quoted in Section 7.7: infinite closeness is preserved at the real points of the
enlargement. -/
theorem continuousOn_iff_infClose :
    ContinuousOn f A ↔ ∀ c ∈ A, ∀ x ∈ ⋆A, x ≊ c → ⋆f x ≊ f c :=
  forall₂_congr fun _ _ => continuousWithinAt_iff_infClose

/-- **Theorem 7.1.1**, for continuity everywhere. -/
theorem continuous_iff_infClose :
    Continuous f ↔ ∀ c : ℝ, ∀ x : ℝ*, x ≊ c → ⋆f x ≊ f c := by
  rw [continuous_iff_continuousAt]
  exact forall_congr' fun _ => continuousAt_iff_infClose

/-- **Theorem 7.1.3, (3) implies (1).** If there is a positive hyperreal $`d` such that
$`{}^*f(x) \simeq f(c)` for all $`x \in {}^*A` with $`|x - c| < d`, then $`f` is continuous
at $`c` relative to $`A`. In the book $`d` is infinitesimal; the proof does not use this.

This is the first half of the book's proof of Theorem 7.1.1. Fix a real
$`\varepsilon > 0`. All $`x` within $`d` of $`c` satisfy the transform of the property
"if $`t \in A` then $`|f(t) - f(c)| < \varepsilon`", so by Cauchy's principle
({name}`exists_real_radius_of_hyperreal_radius`, the existential transfer step) there is a
real $`\delta` such that all real $`t` within $`\delta` of $`c` have that property. -/
theorem continuousWithinAt_of_exists_radius {d : ℝ*} (hd : 0 < d)
    (h : ∀ x ∈ ⋆A, |x - c| < d → ⋆f x ≊ f c) : ContinuousWithinAt f A c := by
  rw [Metric.continuousWithinAt_iff]
  intro η hη
  have key : ∀ x : ℝ*, |x - c| < d → x ∈ ⋆{t : ℝ | t ∈ A → |f t - f c| < η} := by
    intro x hx
    obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
    rw [hyperreal_ofSeq_mem_starSet]
    simp only [mem_ofPred_eq]
    rw [almostAll_imp]
    intro hA
    have h1 := infClose_iff_abs_lt.1 (h _ (hyperreal_ofSeq_mem_starSet.2 hA) hx) η hη
    rwa [starMap_hyperreal_ofSeq, coe_eq_ofSeq_const, abs_ofSeq_sub_ofSeq_lt_iff] at h1
  obtain ⟨δ, hδ, hδ'⟩ := exists_real_radius_of_hyperreal_radius hd key
  exact ⟨δ, hδ, fun t ht htc => hδ' t htc ht⟩

/-- **Theorem 7.1.3.** For a real function $`f`, a set $`A` of reals and a real number $`c`,
the following are equivalent:

1. $`f` is continuous at $`c` relative to $`A`;
2. $`{}^*f(x) \simeq f(c)` for all $`x \in {}^*A` with $`x \simeq c`;
3. there is a positive infinitesimal $`d` such that $`{}^*f(x) \simeq f(c)` for all
   $`x \in {}^*A` with $`|x - c| < d`. -/
theorem continuousWithinAt_tfae (f : ℝ → ℝ) (A : Set ℝ) (c : ℝ) :
    List.TFAE [ContinuousWithinAt f A c,
      ∀ x ∈ ⋆A, x ≊ c → ⋆f x ≊ f c,
      ∃ d : ℝ*, 0 < d ∧ Infinitesimal d ∧ ∀ x ∈ ⋆A, |x - c| < d → ⋆f x ≊ f c] := by
  tfae_have 1 ↔ 2 := continuousWithinAt_iff_infClose
  tfae_have 2 → 3 := fun h =>
    ⟨ε, Hyperreal.epsilon_pos, infinitesimal_epsilon, fun x hA hx =>
      h x hA (infinitesimal_epsilon.of_abs_le (by
        rw [abs_of_pos Hyperreal.epsilon_pos]; exact hx.le))⟩
  tfae_have 3 → 1 := fun ⟨_, hd, _, h⟩ => continuousWithinAt_of_exists_radius hd h
  tfae_finish

/-- **Corollary 7.1.2.** For a real function $`f` and a real number $`c`, the following are
equivalent:

1. $`f` is continuous at $`c`;
2. $`{}^*f(x) \simeq f(c)` whenever $`x \simeq c`;
3. there is a positive infinitesimal $`d` such that $`{}^*f(x) \simeq f(c)` whenever
   $`|x - c| < d`. -/
theorem continuousAt_tfae (f : ℝ → ℝ) (c : ℝ) :
    List.TFAE [ContinuousAt f c,
      ∀ x : ℝ*, x ≊ c → ⋆f x ≊ f c,
      ∃ d : ℝ*, 0 < d ∧ Infinitesimal d ∧ ∀ x : ℝ*, |x - c| < d → ⋆f x ≊ f c] := by
  have := continuousWithinAt_tfae f univ c
  simpa only [continuousWithinAt_univ, starSet_univ, mem_univ, forall_const] using this

/-- **Corollary 7.1.2, (3) implies (1)**, as a rule. -/
theorem continuousAt_of_exists_radius {d : ℝ*} (hd : 0 < d)
    (h : ∀ x : ℝ*, |x - c| < d → ⋆f x ≊ f c) : ContinuousAt f c := by
  rw [← continuousWithinAt_univ]
  exact continuousWithinAt_of_exists_radius hd fun x _ hx => h x hx

end Continuity

/-!
## 7.2 Continuity of the Sine Function

As an illustration of Theorem 7.1.1, the sine function is continuous at every real $`c`. If
$`x \simeq c` then $`x = c + \varepsilon` with $`\varepsilon` infinitesimal, and the addition
formula, which holds for hyperreals by transfer, gives

$$`\sin x - \sin c = \sin c\,(\cos\varepsilon - 1) + \cos c\,\sin\varepsilon .`

By Exercise 5.7(2) the cosine of an infinitesimal is infinitely close to $`1` and its sine
is infinitesimal, while $`\sin c` and $`\cos c` are real; so the right-hand side is
infinitesimal. The same computation with the addition formula for the cosine gives the
continuity of the cosine.
-/

section Sine

/-- **Section 7.2, transfer of the addition formula.** For all hyperreals,
$`\sin(x + y) = \sin x \cos y + \cos x \sin y`. -/
theorem hsin_add (x y : ℝ*) : hsin (x + y) = hsin x * hcos y + hcos x * hsin y := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
  change Hyperreal.ofSeq (fun n => Real.sin (r n + s n)) =
    Hyperreal.ofSeq fun n => Real.sin (r n) * Real.cos (s n) + Real.cos (r n) * Real.sin (s n)
  exact congrArg Hyperreal.ofSeq (funext fun n => Real.sin_add _ _)

/-- **Section 7.2, transfer of the addition formula for the cosine.** For all hyperreals,
$`\cos(x + y) = \cos x \cos y - \sin x \sin y`. -/
theorem hcos_add (x y : ℝ*) : hcos (x + y) = hcos x * hcos y - hsin x * hsin y := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
  change Hyperreal.ofSeq (fun n => Real.cos (r n + s n)) =
    Hyperreal.ofSeq fun n => Real.cos (r n) * Real.cos (s n) - Real.sin (r n) * Real.sin (s n)
  exact congrArg Hyperreal.ofSeq (funext fun n => Real.cos_add _ _)

/-- **Section 7.2.** If $`x \simeq c` with $`c` real, then $`\sin x \simeq \sin c`. -/
theorem hsin_infClose_of_infClose {x : ℝ*} {c : ℝ} (hx : x ≊ c) :
    hsin x ≊ (Real.sin c : ℝ) := by
  have he : Infinitesimal (x - c) := hx
  have hxc : x = c + (x - c) := by ring
  rw [hxc, hsin_add]
  have h1 : (Real.sin c : ℝ*) * hcos (x - c) ≊ (Real.sin c : ℝ*) * 1 :=
    he.hcos_infClose.mul_left (limited_coe _)
  have h2 : (Real.cos c : ℝ*) * hsin (x - c) ≊ (Real.cos c : ℝ*) * 0 :=
    he.hsin_infClose.mul_left (limited_coe _)
  simpa using h1.add h2

/-- **Section 7.2.** If $`x \simeq c` with $`c` real, then $`\cos x \simeq \cos c`. -/
theorem hcos_infClose_of_infClose {x : ℝ*} {c : ℝ} (hx : x ≊ c) :
    hcos x ≊ (Real.cos c : ℝ) := by
  have he : Infinitesimal (x - c) := hx
  have hxc : x = c + (x - c) := by ring
  rw [hxc, hcos_add]
  have h1 : (Real.cos c : ℝ*) * hcos (x - c) ≊ (Real.cos c : ℝ*) * 1 :=
    he.hcos_infClose.mul_left (limited_coe _)
  have h2 : (Real.sin c : ℝ*) * hsin (x - c) ≊ (Real.sin c : ℝ*) * 0 :=
    he.hsin_infClose.mul_left (limited_coe _)
  simpa using h1.sub h2

/-- **Section 7.2 (continuity of the sine function).** The sine function is continuous at
every real number, by Theorem 7.1.1 and the addition formula. -/
theorem continuous_sin : Continuous Real.sin :=
  continuous_iff_infClose.2 fun _ _ hx => hsin_infClose_of_infClose hx

/-- **Section 7.2**, the same argument for the cosine. -/
theorem continuous_cos : Continuous Real.cos :=
  continuous_iff_infClose.2 fun _ _ hx => hcos_infClose_of_infClose hx

end Sine

/-!
## 7.3 Limits of Functions

The seven kinds of limit of a real function $`f` defined on a set $`A` are characterised in
the same way as continuity. In each case the standard statement is a convergence of filters
in Mathlib, and the hyperreal statement describes what the extension of $`f` does to the
points of the enlargement of $`A` that are infinitely close to $`c` (on one side, or on both
sides and different from $`c`), or that are positive or negative unlimited.

In Mathlib's vocabulary the right-hand limit at $`c` along $`A` is taken along the filter
{lit}`𝓝[A ∩ Ioi c] c`, the left-hand limit along {lit}`𝓝[A ∩ Iio c] c`, the two-sided limit
along {lit}`𝓝[A \ {c}] c`, and the limits at plus and minus infinity along {lit}`atTop ⊓ 𝓟 A`
and {lit}`atBot ⊓ 𝓟 A`. The book adds to the last two the proviso that positive (or negative)
unlimited members of the enlargement of $`A` exist; this is the condition that $`A` is
unbounded above (or below), proved separately as
{lit}`exists_posUnlimited_mem_starSet_iff` and {lit}`exists_negUnlimited_mem_starSet_iff`.
-/

section Limits

variable {f g : ℝ → ℝ} {A : Set ℝ} {c L M : ℝ} {x y : ℝ*}

/-- **Section 7.3, first item (right-hand limit).** $`\lim_{x \to c^+} f(x) = L` if and only
if $`{}^*f(x) \simeq L` for all $`x \in {}^*A` with $`x \simeq c` and $`x > c`. -/
theorem tendsto_nhdsWithin_Ioi_iff_infClose :
    Tendsto f (𝓝[A ∩ Ioi c] c) (𝓝 L) ↔
      ∀ x ∈ ⋆A, x ≊ c → (c : ℝ*) < x → ⋆f x ≊ L := by
  rw [nhdsWithin, tendsto_inf_principal_iff_filterMonad, starSet_inter, starSet_Ioi_real]
  simp only [mem_inter_iff, mem_Ioi, mem_filterMonad_nhds, and_imp]
  exact ⟨fun h x hA hx hc => h x hA hc hx, fun h x hA hc hx => h x hA hx hc⟩

/-- **Section 7.3, second item (left-hand limit).** $`\lim_{x \to c^-} f(x) = L` if and only
if $`{}^*f(x) \simeq L` for all $`x \in {}^*A` with $`x \simeq c` and $`x < c`. -/
theorem tendsto_nhdsWithin_Iio_iff_infClose :
    Tendsto f (𝓝[A ∩ Iio c] c) (𝓝 L) ↔
      ∀ x ∈ ⋆A, x ≊ c → x < (c : ℝ*) → ⋆f x ≊ L := by
  rw [nhdsWithin, tendsto_inf_principal_iff_filterMonad, starSet_inter, starSet_Iio_real]
  simp only [mem_inter_iff, mem_Iio, mem_filterMonad_nhds, and_imp]
  exact ⟨fun h x hA hx hc => h x hA hc hx, fun h x hA hc hx => h x hA hx hc⟩

/-- **Section 7.3, third item (two-sided limit).** $`\lim_{x \to c} f(x) = L` if and only if
$`{}^*f(x) \simeq L` for all $`x \in {}^*A` with $`x \simeq c` and $`x \ne c`. -/
theorem tendsto_nhdsWithin_diff_singleton_iff_infClose :
    Tendsto f (𝓝[A \ {c}] c) (𝓝 L) ↔
      ∀ x ∈ ⋆A, x ≊ c → x ≠ (c : ℝ*) → ⋆f x ≊ L := by
  rw [nhdsWithin, tendsto_inf_principal_iff_filterMonad, starSet_diff, starSet_singleton_real]
  simp only [Set.mem_sdiff, mem_singleton_iff, mem_filterMonad_nhds, and_imp]
  exact ⟨fun h x hA hx hc => h x hA hc hx, fun h x hA hc hx => h x hA hx hc⟩

/-- **Section 7.3, third item**, for a function defined near $`c`: the limit along the
punctured neighbourhoods of $`c` is $`L` if and only if $`{}^*f(x) \simeq L` for all
hyperreal $`x \simeq c` with $`x \ne c`. This is the form used for derivatives. -/
theorem tendsto_punctured_nhds_iff_infClose :
    Tendsto f (𝓝[≠] c) (𝓝 L) ↔ ∀ x : ℝ*, x ≊ c → x ≠ (c : ℝ*) → ⋆f x ≊ L := by
  have := tendsto_nhdsWithin_diff_singleton_iff_infClose (f := f) (A := univ) (c := c) (L := L)
  rw [starSet_univ, ← compl_eq_univ_sdiff] at this
  simpa using this

/-- **Section 7.3**, the limit along all neighbourhoods of $`c`: $`f` tends to $`L` at $`c`
if and only if $`{}^*f(x) \simeq L` for all hyperreal $`x \simeq c`. -/
theorem tendsto_nhds_iff_infClose :
    Tendsto f (𝓝 c) (𝓝 L) ↔ ∀ x : ℝ*, x ≊ c → ⋆f x ≊ L := by
  rw [tendsto_iff_starMap_mem_filterMonad (αS := ℝ*) (βS := ℝ*)]
  simp only [mem_filterMonad_nhds]

/-- **Section 7.3, fourth item (infinite limit).** $`\lim_{x \to c} f(x) = +\infty` if and
only if $`{}^*f(x)` is positive unlimited for all $`x \in {}^*A` with $`x \simeq c` and
$`x \ne c`. -/
theorem tendsto_nhdsWithin_diff_singleton_atTop_iff :
    Tendsto f (𝓝[A \ {c}] c) atTop ↔
      ∀ x ∈ ⋆A, x ≊ c → x ≠ (c : ℝ*) → PosUnlimited (⋆f x) := by
  rw [nhdsWithin, tendsto_inf_principal_iff_filterMonad, starSet_diff, starSet_singleton_real]
  simp only [Set.mem_sdiff, mem_singleton_iff, mem_filterMonad_nhds, mem_filterMonad_atTop, and_imp]
  exact ⟨fun h x hA hx hc => h x hA hc hx, fun h x hA hc hx => h x hA hx hc⟩

/-- **Section 7.3, fifth item (infinite limit).** $`\lim_{x \to c} f(x) = -\infty` if and
only if $`{}^*f(x)` is negative unlimited for all $`x \in {}^*A` with $`x \simeq c` and
$`x \ne c`. -/
theorem tendsto_nhdsWithin_diff_singleton_atBot_iff :
    Tendsto f (𝓝[A \ {c}] c) atBot ↔
      ∀ x ∈ ⋆A, x ≊ c → x ≠ (c : ℝ*) → NegUnlimited (⋆f x) := by
  rw [nhdsWithin, tendsto_inf_principal_iff_filterMonad, starSet_diff, starSet_singleton_real]
  simp only [Set.mem_sdiff, mem_singleton_iff, mem_filterMonad_nhds, mem_filterMonad_atBot, and_imp]
  exact ⟨fun h x hA hx hc => h x hA hc hx, fun h x hA hc hx => h x hA hx hc⟩

/-- **Section 7.3, sixth item (limit at plus infinity).** $`\lim_{x \to +\infty} f(x) = L`
if and only if $`{}^*f(x) \simeq L` for all positive unlimited $`x \in {}^*A`. -/
theorem tendsto_atTop_inf_principal_iff_infClose :
    Tendsto f (atTop ⊓ 𝓟 A) (𝓝 L) ↔ ∀ x ∈ ⋆A, PosUnlimited x → ⋆f x ≊ L := by
  rw [tendsto_inf_principal_iff_filterMonad]
  simp only [mem_filterMonad_nhds, mem_filterMonad_atTop]

/-- **Section 7.3, seventh item (limit at minus infinity).** $`\lim_{x \to -\infty} f(x) = L`
if and only if $`{}^*f(x) \simeq L` for all negative unlimited $`x \in {}^*A`. -/
theorem tendsto_atBot_inf_principal_iff_infClose :
    Tendsto f (atBot ⊓ 𝓟 A) (𝓝 L) ↔ ∀ x ∈ ⋆A, NegUnlimited x → ⋆f x ≊ L := by
  rw [tendsto_inf_principal_iff_filterMonad]
  simp only [mem_filterMonad_nhds, mem_filterMonad_atBot]

/-- **Section 7.3, sixth item**, for a function defined on the whole line. -/
theorem tendsto_atTop_nhds_iff_infClose :
    Tendsto f atTop (𝓝 L) ↔ ∀ x : ℝ*, PosUnlimited x → ⋆f x ≊ L := by
  rw [tendsto_iff_starMap_mem_filterMonad (αS := ℝ*) (βS := ℝ*)]
  simp only [mem_filterMonad_nhds, mem_filterMonad_atTop]

/-- **Section 7.3, seventh item**, for a function defined on the whole line. -/
theorem tendsto_atBot_nhds_iff_infClose :
    Tendsto f atBot (𝓝 L) ↔ ∀ x : ℝ*, NegUnlimited x → ⋆f x ≊ L := by
  rw [tendsto_iff_starMap_mem_filterMonad (αS := ℝ*) (βS := ℝ*)]
  simp only [mem_filterMonad_nhds, mem_filterMonad_atBot]

/-- **Section 7.3, sixth item, the proviso.** The enlargement of $`A` has a positive
unlimited member if and only if $`A` is not bounded above. This is the condition under which
the limit at plus infinity along $`A` is meaningful. -/
theorem exists_posUnlimited_mem_starSet_iff :
    (∃ x ∈ ⋆A, PosUnlimited x) ↔ ¬ BddAbove A := by
  constructor
  · rintro ⟨x, hA, hx⟩ ⟨b, hb⟩
    have h1 : x ∈ ⋆(Iic b) := starSet_subset_starSet.2 (fun t ht => hb ht) hA
    rw [starSet_Iic_real] at h1
    exact absurd (hx b) (not_lt.2 h1)
  · intro h
    rw [not_bddAbove_iff] at h
    choose r hrA hr using fun n : ℕ => h n
    refine ⟨Hyperreal.ofSeq r, hyperreal_ofSeq_mem_starSet.2 (Eventually.of_forall hrA), ?_⟩
    exact coe_lt_ofSeq_of_tendsto_atTop
      (tendsto_atTop_mono (fun n => (hr n).le) tendsto_natCast_atTop_atTop)

/-- **Section 7.3, seventh item, the proviso.** The enlargement of $`A` has a negative
unlimited member if and only if $`A` is not bounded below. -/
theorem exists_negUnlimited_mem_starSet_iff :
    (∃ x ∈ ⋆A, NegUnlimited x) ↔ ¬ BddBelow A := by
  constructor
  · rintro ⟨x, hA, hx⟩ ⟨b, hb⟩
    have h1 : x ∈ ⋆(Ici b) := starSet_subset_starSet.2 (fun t ht => hb ht) hA
    rw [starSet_Ici_real] at h1
    exact absurd (hx b) (not_lt.2 h1)
  · intro h
    rw [not_bddBelow_iff] at h
    choose r hrA hr using fun n : ℕ => h (-n)
    refine ⟨Hyperreal.ofSeq r, hyperreal_ofSeq_mem_starSet.2 (Eventually.of_forall hrA), ?_⟩
    intro b
    rw [coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
    obtain ⟨m, hm⟩ := exists_nat_gt (-b)
    refine eventually_hyperfilter_of_forall_ge m fun n hn => ?_
    have : (m : ℝ) ≤ n := by exact_mod_cast hn
    have := hr n
    linarith

end Limits

/-!
## 7.4 Exercises on Limits

Exercise (1) asks for the derivations of the characterisations of Section 7.3; these are the
proofs above. Exercise (2) uses them to obtain three standard facts: a two-sided limit exists
exactly when both one-sided limits exist and agree; limits respect sums, products and
quotients; and continuity at $`c` means that the limit at $`c` is the value at $`c`. Each
becomes a one-line statement about infinite closeness: a hyperreal different from $`c` is
either above or below it, and infinite closeness is compatible with the field operations on
limited numbers (Exercise 5.7(1)).

Exercise (3) asks for a discussion, by infinitesimals, of the continuity of five functions.
The results are:

* $`f_1(x) = \sin(1/x)` (with $`f_1(0) = 0`) is not continuous at $`0`: there are
  infinitesimals at which its extension takes the value $`1`;
* $`f_2(x) = x \sin(1/x)` is continuous at $`0`, because $`|f_2(x)| \le |x|` transfers;
* the indicator function $`f_3` of the rationals is continuous nowhere: every real is
  infinitely close to hyperreals of both kinds;
* $`f_4`, which is $`x` on the rationals and $`-x` on the irrationals, is continuous exactly
  at $`0`;
* $`f_5`, which is $`1/n` at a rational $`m/n` in lowest terms and $`0` at the irrationals,
  is continuous exactly at the irrationals. The interesting half has a purely nonstandard
  proof: if $`x \simeq c` and $`f_5(x)` is not infinitesimal, then $`x` is a hyperrational
  whose denominator is bounded by a standard $`K`, so $`K!\,x` is a limited hyperinteger,
  hence a standard integer, and $`c = \operatorname{sh}(x)` is rational.
-/

section LimitExercises

variable {f g : ℝ → ℝ} {A : Set ℝ} {c L M : ℝ} {x y : ℝ*}

/-- **Exercise 7.4(2), first item.** $`\lim_{x \to c} f(x) = L` if and only if both
$`\lim_{x \to c^+} f(x) = L` and $`\lim_{x \to c^-} f(x) = L`: a hyperreal $`x \ne c` is
either greater or smaller than $`c`. -/
theorem tendsto_diff_singleton_iff_Ioi_and_Iio :
    Tendsto f (𝓝[A \ {c}] c) (𝓝 L) ↔
      Tendsto f (𝓝[A ∩ Ioi c] c) (𝓝 L) ∧ Tendsto f (𝓝[A ∩ Iio c] c) (𝓝 L) := by
  rw [tendsto_nhdsWithin_diff_singleton_iff_infClose, tendsto_nhdsWithin_Ioi_iff_infClose,
    tendsto_nhdsWithin_Iio_iff_infClose]
  constructor
  · intro h
    exact ⟨fun x hA hx hc => h x hA hx hc.ne', fun x hA hx hc => h x hA hx hc.ne⟩
  · rintro ⟨h₁, h₂⟩ x hA hx hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact h₂ x hA hx h
    · exact h₁ x hA hx h

/-- **Exercise 7.4(2), second item, sums.** If $`\lim_{x \to c} f(x) = L` and
$`\lim_{x \to c} g(x) = M`, then $`\lim_{x \to c} (f(x) + g(x)) = L + M`. -/
theorem tendsto_diff_singleton_add (hf : Tendsto f (𝓝[A \ {c}] c) (𝓝 L))
    (hg : Tendsto g (𝓝[A \ {c}] c) (𝓝 M)) :
    Tendsto (fun t => f t + g t) (𝓝[A \ {c}] c) (𝓝 (L + M)) := by
  rw [tendsto_nhdsWithin_diff_singleton_iff_infClose] at *
  intro x hA hx hc
  rw [starMap_add_apply, Hyperreal.coe_add]
  exact (hf x hA hx hc).add (hg x hA hx hc)

/-- **Exercise 7.4(2), second item, products.** If $`\lim_{x \to c} f(x) = L` and
$`\lim_{x \to c} g(x) = M`, then $`\lim_{x \to c} f(x) g(x) = L M`. -/
theorem tendsto_diff_singleton_mul (hf : Tendsto f (𝓝[A \ {c}] c) (𝓝 L))
    (hg : Tendsto g (𝓝[A \ {c}] c) (𝓝 M)) :
    Tendsto (fun t => f t * g t) (𝓝[A \ {c}] c) (𝓝 (L * M)) := by
  rw [tendsto_nhdsWithin_diff_singleton_iff_infClose] at *
  intro x hA hx hc
  rw [starMap_mul_apply, Hyperreal.coe_mul]
  have h1 := hf x hA hx hc
  have h2 := hg x hA hx hc
  exact h1.mul h2 (limited_of_infClose_coe h1) (limited_of_infClose_coe h2)

/-- **Exercise 7.4(2), second item, quotients.** If $`\lim_{x \to c} f(x) = L` and
$`\lim_{x \to c} g(x) = M \ne 0`, then $`\lim_{x \to c} f(x) / g(x) = L / M`. -/
theorem tendsto_diff_singleton_div (hf : Tendsto f (𝓝[A \ {c}] c) (𝓝 L))
    (hg : Tendsto g (𝓝[A \ {c}] c) (𝓝 M)) (hM : M ≠ 0) :
    Tendsto (fun t => f t / g t) (𝓝[A \ {c}] c) (𝓝 (L / M)) := by
  rw [tendsto_nhdsWithin_diff_singleton_iff_infClose] at *
  intro x hA hx hc
  rw [starMap_div_apply, Hyperreal.coe_div]
  have h1 := hf x hA hx hc
  have h2 := hg x hA hx hc
  refine h1.div h2 (limited_of_infClose_coe h1) (limited_of_infClose_coe h2) fun h0 => ?_
  have : (M : ℝ*) ≊ ((0 : ℝ) : ℝ*) := h2.symm.trans h0
  exact hM (infClose_coe_iff.1 this)

/-- **Exercise 7.4(2), third item.** $`f` is continuous at $`c` (relative to $`A`) if and
only if $`\lim_{x \to c} f(x) = f(c)`: the only point of the halo of $`c` not covered by the
limit is $`c` itself, where the extension takes the value $`f(c)`. -/
theorem continuousWithinAt_iff_tendsto_diff_singleton :
    ContinuousWithinAt f A c ↔ Tendsto f (𝓝[A \ {c}] c) (𝓝 (f c)) := by
  rw [continuousWithinAt_iff_infClose, tendsto_nhdsWithin_diff_singleton_iff_infClose]
  constructor
  · intro h x hA hx _
    exact h x hA hx
  · intro h x hA hx
    by_cases hc : x = (c : ℝ*)
    · rw [hc, starMap_coe]
    · exact h x hA hx hc

/-- **Exercise 7.4(2), third item**, for a function defined near $`c`. -/
theorem continuousAt_iff_tendsto_punctured :
    ContinuousAt f c ↔ Tendsto f (𝓝[≠] c) (𝓝 (f c)) := by
  rw [← continuousWithinAt_univ, continuousWithinAt_iff_tendsto_diff_singleton,
    ← compl_eq_univ_sdiff]

end LimitExercises

section TestFunctions

variable {f g : ℝ → ℝ} {A : Set ℝ} {c : ℝ} {x : ℝ*}

/-- **Exercise 7.4(3), tool (universal transfer of an equation on a set).** If $`f` and $`g`
agree on $`A`, their extensions agree on the enlargement of $`A`. -/
theorem starMap_congr_of_mem (h : ∀ t ∈ A, f t = g t) (hx : x ∈ ⋆A) : ⋆f x = ⋆g x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [starMap_hyperreal_ofSeq, starMap_hyperreal_ofSeq, ofSeq_eq_ofSeq_iff]
  exact (hyperreal_ofSeq_mem_starSet.1 hx).mono fun n hn => h _ hn

/-- **Exercise 7.4(3), tool.** If $`f` takes the constant value $`b` on $`A`, its extension
takes the value $`b` on the enlargement of $`A`. -/
theorem starMap_eq_coe_of_mem {b : ℝ} (h : ∀ t ∈ A, f t = b) (hx : x ∈ ⋆A) : ⋆f x = b := by
  rw [starMap_congr_of_mem h hx, starMap_const_apply]

/-- **Exercise 7.4(3), tool.** Every real number is infinitely close to a hyperrational
number: the class of a sequence of rationals converging to it. -/
theorem exists_hyperRat_infClose_coe (c : ℝ) : ∃ x ∈ ℚ*, x ≊ c := by
  obtain ⟨q, hq, hx⟩ := exists_hyperRat_infClose (c : ℝ*)
  exact ⟨q, hq, hx.symm⟩

/-- **Exercise 7.4(3), tool.** Every real number is infinitely close to a member of the
enlargement of the set of irrational numbers. For an irrational number this is the number
itself; a rational number $`c` is the limit of the irrationals $`c + \sqrt2/(n+1)`. -/
theorem exists_irrational_infClose_coe (c : ℝ) : ∃ x ∈ ⋆{t : ℝ | Irrational t}, x ≊ c := by
  obtain ⟨r, hr, hlim⟩ := mem_closure_iff_seq_limit.1 (dense_irrational c)
  exact ⟨Hyperreal.ofSeq r, hyperreal_ofSeq_mem_starSet.2 (Eventually.of_forall hr),
    ofSeq_infClose_coe_iff.2 (hlim.mono_left Nat.hyperfilter_le_atTop)⟩

/-- **Exercise 7.4(3).** The first test function: $`f_1(x) = \sin(1/x)` for $`x \ne 0` and
$`f_1(0) = 0`. -/
def sinInv (x : ℝ) : ℝ := if x = 0 then 0 else Real.sin (1 / x)

/-- **Exercise 7.4(3).** The second test function: $`f_2(x) = x \sin(1/x)` for $`x \ne 0` and
$`f_2(0) = 0`. -/
def mulSinInv (x : ℝ) : ℝ := if x = 0 then 0 else x * Real.sin (1 / x)

open Classical in
/-- **Exercise 7.4(3).** The third test function: $`f_3(x) = 1` for rational $`x` and
$`f_3(x) = 0` for irrational $`x`. -/
def ratIndicator (x : ℝ) : ℝ := if Irrational x then 0 else 1

open Classical in
/-- **Exercise 7.4(3).** The fourth test function: $`f_4(x) = x` for rational $`x` and
$`f_4(x) = -x` for irrational $`x`. -/
def ratSign (x : ℝ) : ℝ := if Irrational x then -x else x

open Classical in
/-- **Exercise 7.4(3).** The fifth test function: $`f_5(x) = 1/n` if $`x` is the rational
$`m/n` in lowest terms with $`n \ge 1`, and $`f_5(x) = 0` if $`x` is irrational. -/
def thomae (x : ℝ) : ℝ := if h : ∃ q : ℚ, (q : ℝ) = x then 1 / (h.choose.den : ℝ) else 0

/-- **Exercise 7.4(3), first function.** There is a nonzero infinitesimal $`x` with
$`{}^*f_1(x) = 1`: the class of the sequence $`1/(\pi/2 + 2\pi n)`. -/
theorem exists_infinitesimal_starMap_sinInv_eq_one :
    ∃ x : ℝ*, Infinitesimal x ∧ ⋆sinInv x = 1 := by
  let r : ℕ → ℝ := fun n => (Real.pi / 2 + n * (2 * Real.pi))⁻¹
  have hpos : ∀ n : ℕ, 0 < Real.pi / 2 + n * (2 * Real.pi) := fun n => by positivity
  refine ⟨Hyperreal.ofSeq r, ?_, ?_⟩
  · rw [infinitesimal_iff_infClose_zero, ← Hyperreal.coe_zero, ofSeq_infClose_coe_iff]
    refine Tendsto.mono_left ?_ Nat.hyperfilter_le_atTop
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _
      (tendsto_natCast_atTop_atTop.atTop_mul_const Real.two_pi_pos))
  · rw [starMap_hyperreal_ofSeq, ← Hyperreal.coe_one, coe_eq_ofSeq_const]
    refine congrArg Hyperreal.ofSeq (funext fun n => ?_)
    have h0 : r n ≠ 0 := inv_ne_zero (hpos n).ne'
    rw [sinInv, ite_eq_right h0]
    simp only [r, one_div, inv_inv]
    rw [Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]

/-- **Exercise 7.4(3), first function.** $`f_1` is not continuous at $`0`: by Theorem 7.1.1
it would have to send every infinitesimal to an infinitesimal, but it sends some
infinitesimal to $`1`. -/
theorem not_continuousAt_sinInv_zero : ¬ ContinuousAt sinInv 0 := by
  intro h
  obtain ⟨x, hx, h1⟩ := exists_infinitesimal_starMap_sinInv_eq_one
  have := continuousAt_iff_infClose.1 h x (by simpa using infinitesimal_iff_infClose_zero.1 hx)
  rw [h1, ← Hyperreal.coe_one, infClose_coe_iff] at this
  simp [sinInv] at this

/-- **Exercise 7.4(3), second function.** $`|f_2(x)| \le |x|` for all real $`x`. -/
theorem abs_mulSinInv_le (t : ℝ) : |mulSinInv t| ≤ |t| := by
  unfold mulSinInv
  split_ifs with h
  · simp
  · rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

/-- **Exercise 7.4(3), tool.** If $`|f(t)| \le |t|` for all real $`t`, then $`{}^*f` maps
infinitesimals to infinitesimals, by transfer of the inequality. -/
theorem infinitesimal_starMap_of_abs_le (h : ∀ t, |f t| ≤ |t|) (hx : Infinitesimal x) :
    Infinitesimal (⋆f x) := by
  refine hx.of_abs_le ?_
  have := starMap_le_starMap_of_mem (A := univ) (f := fun t => |f t|) (g := fun t => |t|)
    (fun t _ => h t) (x := x) (by rw [starSet_univ]; exact mem_univ _)
  rwa [starMap_abs_apply, starMap_abs_apply, starMap_id_apply] at this

/-- **Exercise 7.4(3), second function.** $`f_2` is continuous at $`0`: if $`x` is
infinitesimal then so is $`{}^*f_2(x)`, because $`|{}^*f_2(x)| \le |x|` by transfer. -/
theorem continuousAt_mulSinInv_zero : ContinuousAt mulSinInv 0 := by
  rw [continuousAt_iff_infClose]
  intro x hx
  have h0 : mulSinInv 0 = 0 := by simp [mulSinInv]
  rw [h0]
  rw [Hyperreal.coe_zero, ← infinitesimal_iff_infClose_zero] at *
  exact infinitesimal_starMap_of_abs_le abs_mulSinInv_le hx

/-- **Exercise 7.4(3), third function.** The extension of $`f_3` takes the value $`1` at
every hyperrational. -/
theorem starMap_ratIndicator_of_mem_hyperRat (hx : x ∈ ℚ*) : ⋆ratIndicator x = 1 := by
  have := starMap_eq_coe_of_mem (f := ratIndicator) (b := 1) (A := range ((↑) : ℚ → ℝ))
    (fun t ht => by
      obtain ⟨q, rfl⟩ := ht
      simp [ratIndicator]) hx
  simpa using this

/-- **Exercise 7.4(3), third function.** The extension of $`f_3` takes the value $`0` on the
enlargement of the set of irrationals. -/
theorem starMap_ratIndicator_of_mem_irrational (hx : x ∈ ⋆{t : ℝ | Irrational t}) :
    ⋆ratIndicator x = 0 := by
  have := starMap_eq_coe_of_mem (f := ratIndicator) (b := 0) (A := {t : ℝ | Irrational t})
    (fun t ht => ite_eq_left ht) hx
  simpa using this

/-- **Exercise 7.4(3), third function.** $`f_3` is continuous at no real number $`c`. The
halo of $`c` contains a hyperrational, where the extension is $`1`, and a member of the
enlargement of the irrationals, where it is $`0`; one of the two values is not infinitely
close to $`f_3(c)`. -/
theorem not_continuousAt_ratIndicator (c : ℝ) : ¬ ContinuousAt ratIndicator c := by
  intro h
  rw [continuousAt_iff_infClose] at h
  obtain ⟨x, hxQ, hx⟩ := exists_hyperRat_infClose_coe c
  obtain ⟨y, hyI, hy⟩ := exists_irrational_infClose_coe c
  have h1 := h x hx
  have h2 := h y hy
  rw [starMap_ratIndicator_of_mem_hyperRat hxQ] at h1
  rw [starMap_ratIndicator_of_mem_irrational hyI] at h2
  have : ((1 : ℝ) : ℝ*) ≊ ((0 : ℝ) : ℝ*) := by
    simpa using h1.trans h2.symm
  exact one_ne_zero (infClose_coe_iff.1 this)

/-- **Exercise 7.4(3), fourth function.** $`|f_4(x)| = |x|` for all real $`x`. -/
theorem abs_ratSign (t : ℝ) : |ratSign t| = |t| := by
  unfold ratSign
  split_ifs <;> simp

/-- **Exercise 7.4(3), fourth function.** $`f_4` is continuous at $`c` if and only if
$`c = 0`. At $`0` this follows from $`|f_4(x)| = |x|`. At $`c \ne 0` the halo of $`c`
contains a hyperrational $`x`, where the extension has the value $`x \simeq c`, and a member
$`y` of the enlargement of the irrationals, where it has the value $`-y \simeq -c`; continuity
would give $`c \simeq -c`. -/
theorem continuousAt_ratSign_iff (c : ℝ) : ContinuousAt ratSign c ↔ c = 0 := by
  constructor
  · intro h
    rw [continuousAt_iff_infClose] at h
    obtain ⟨x, hxQ, hx⟩ := exists_hyperRat_infClose_coe c
    obtain ⟨y, hyI, hy⟩ := exists_irrational_infClose_coe c
    have h1 := h x hx
    have h2 := h y hy
    have e1 : ⋆ratSign x = x := by
      rw [starMap_congr_of_mem (g := fun t => t) (A := range ((↑) : ℚ → ℝ)) (fun t ht => by
        obtain ⟨q, rfl⟩ := ht
        simp [ratSign]) hxQ, starMap_id_apply]
    have e2 : ⋆ratSign y = -y := by
      have key : ∀ t ∈ {t : ℝ | Irrational t}, ratSign t = (fun t : ℝ => -t) t :=
        fun t ht => ite_eq_left ht
      rw [starMap_congr_of_mem key hyI, starMap_neg_apply, starMap_id_apply]
    rw [e1] at h1
    rw [e2] at h2
    have h3 : (c : ℝ*) ≊ ((-c : ℝ) : ℝ*) := by
      rw [Hyperreal.coe_neg]
      exact (hx.symm.trans h1).trans (h2.symm.trans hy.neg)
    have := infClose_coe_iff.1 h3
    linarith
  · rintro rfl
    rw [continuousAt_iff_infClose]
    intro x hx
    have h0 : ratSign 0 = 0 := by simp [ratSign]
    rw [h0]
    rw [Hyperreal.coe_zero, ← infinitesimal_iff_infClose_zero] at *
    exact infinitesimal_starMap_of_abs_le (fun t => (abs_ratSign t).le) hx

/-- **Exercise 7.4(3), fifth function.** At a rational number, $`f_5` is the reciprocal of
the denominator. -/
theorem thomae_ratCast (q : ℚ) : thomae (q : ℝ) = 1 / (q.den : ℝ) := by
  have h : ∃ q' : ℚ, (q' : ℝ) = (q : ℝ) := ⟨q, rfl⟩
  rw [thomae, dite_eq_left h]
  have : h.choose = q := Rat.cast_injective h.choose_spec
  rw [this]

/-- **Exercise 7.4(3), fifth function.** At an irrational number, $`f_5` vanishes. -/
theorem thomae_of_irrational {t : ℝ} (ht : Irrational t) : thomae t = 0 := by
  rw [thomae, dite_eq_right]
  rintro ⟨q, rfl⟩
  exact ht ⟨q, rfl⟩

/-- **Exercise 7.4(3), fifth function.** If $`f_5(t) \ge \eta` and $`K` is a natural number
with $`1/\eta < K`, then $`K!\,t` is an integer: $`t` is a rational whose denominator is
below $`K`. -/
theorem factorial_mul_mem_range_of_le_thomae {t η : ℝ} {K : ℕ} (hη : 0 < η)
    (hK : 1 / η < K) (h : η ≤ thomae t) : (K.factorial : ℝ) * t ∈ range ((↑) : ℤ → ℝ) := by
  by_cases hq : ∃ q : ℚ, (q : ℝ) = t
  · obtain ⟨q, rfl⟩ := hq
    rw [thomae_ratCast] at h
    have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have h1 : (q.den : ℝ) ≤ 1 / η := by
      rw [le_div_iff₀ hη]
      have := (le_div_iff₀ hden).1 h
      linarith
    have h2 : q.den ≤ K := by
      have : (q.den : ℝ) < K := lt_of_le_of_lt h1 hK
      exact_mod_cast this.le
    obtain ⟨m, hm⟩ := Nat.dvd_factorial q.den_pos h2
    refine ⟨(m : ℤ) * q.num, ?_⟩
    rw [hm, Rat.cast_def]
    push_cast
    field_simp
  · have : thomae t = 0 := by rw [thomae, dite_eq_right hq]
    rw [this] at h
    exact absurd h (not_le.2 hη)

/-- **Exercise 7.4(3), fifth function.** $`f_5` is continuous at $`c` if and only if $`c` is
irrational.

At a rational $`c` the value is positive, while the halo of $`c` contains members of the
enlargement of the irrationals, where the extension vanishes. Let $`c` be irrational and
$`x \simeq c`, and suppose $`{}^*f_5(x)` were not infinitesimal, say at least a real
$`\eta > 0` in absolute value. Take a standard $`K > 1/\eta`. By transfer $`K!\,x` is a
hyperinteger; it is limited because $`x` is; so it is a standard integer $`z`
(Exercise 5.11(1)). Then $`x = z/K!` is a real number infinitely close to $`c`, hence equal
to $`c`, and $`c` is rational: a contradiction. -/
theorem continuousAt_thomae_iff (c : ℝ) : ContinuousAt thomae c ↔ Irrational c := by
  constructor
  · intro h
    rintro ⟨q, rfl⟩
    rw [continuousAt_iff_infClose] at h
    obtain ⟨y, hyI, hy⟩ := exists_irrational_infClose_coe (q : ℝ)
    have h2 := h y hy
    have e : ⋆thomae y = ((0 : ℝ) : ℝ*) :=
      starMap_eq_coe_of_mem (A := {t : ℝ | Irrational t})
        (fun t ht => thomae_of_irrational ht) hyI
    rw [e, infClose_coe_iff, thomae_ratCast] at h2
    have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have : (0 : ℝ) < 1 / (q.den : ℝ) := by positivity
    linarith
  · intro hc
    rw [continuousAt_iff_infClose]
    intro x hx
    rw [thomae_of_irrational hc, infClose_iff_abs_lt]
    intro η hη
    by_contra hlt
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / η)
    obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
    rw [starMap_hyperreal_ofSeq, coe_eq_ofSeq_const, abs_ofSeq_sub_ofSeq_lt_iff,
      ← almostAll_not] at hlt
    have hint : (K.factorial : ℝ*) * Hyperreal.ofSeq r ∈ ℤ* := by
      have e : (K.factorial : ℝ*) * Hyperreal.ofSeq r =
          Hyperreal.ofSeq fun n => (K.factorial : ℝ) * r n := rfl
      rw [e]
      refine hyperreal_ofSeq_mem_starSet.2 (hlt.mono fun n hn => ?_)
      refine factorial_mul_mem_range_of_le_thomae hη hK ?_
      have := not_lt.1 hn
      rw [sub_zero] at this
      exact this.trans (le_of_eq (abs_of_nonneg (by
        unfold thomae
        split_ifs <;> positivity)))
    have hlim : Limited ((K.factorial : ℝ*) * Hyperreal.ofSeq r) :=
      (limited_natCast _).mul (limited_of_infClose_coe hx)
    obtain ⟨z, hz⟩ := (limited_hyperInt_iff hint).1 hlim
    have hfac : (K.factorial : ℝ*) ≠ 0 := by exact_mod_cast K.factorial_ne_zero
    have hxz : Hyperreal.ofSeq r = (((z : ℝ) / (K.factorial : ℝ) : ℝ) : ℝ*) := by
      rw [Hyperreal.coe_div, ofReal_intCast, ofReal_natCast, eq_div_iff hfac, mul_comm]
      exact hz
    rw [hxz, infClose_coe_iff] at hx
    refine hc ⟨(z : ℚ) / (K.factorial : ℚ), ?_⟩
    rw [← hx]
    push_cast
    rfl

end TestFunctions

end Goldblatt
