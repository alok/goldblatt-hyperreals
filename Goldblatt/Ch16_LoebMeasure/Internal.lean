import Goldblatt.Ch16_LoebMeasure.Loeb

/-!
# 16 (part 4). Internal Measures in the Ultrapower

This is the fourth of five parts of Chapter 16 (the overview is on the chapter page
{lit}`Goldblatt.Ch16_LoebMeasure`). It supplies the nonstandard input for Sections 16.5 to
16.7 in the ultrapower of Chapters 3, 11 and 12, and proves the examples of Sections 16.1 and
16.2 that involve internal sets.

An internal ring of internal sets is given by a sequence of rings of sets, and an internal
finitely additive function on it by a sequence of finitely additive functions; its values are
classes of sequences of extended nonnegative reals. The shadow of such a value is the limit
of the sequence along the index ultrafilter, which always exists in $`[0, \infty]`. Countable
saturation of the ultrapower (Theorem 11.10.1), applied to internal sets of points and to
internal sets of sets, gives the three properties required by part 3, so that every internal
measure has a Loeb measure.
-/

universe u

namespace Goldblatt

open Set Filter MeasureTheory Function Ultrapower
open scoped ENNReal Topology Hyperreal

/-!
## The extended nonnegative hyperreals and their shadows

The book lets an internal measure take values in the enlargement of $`[0, \infty]`. In the
ultrapower that enlargement is the type of classes of sequences of extended nonnegative reals.
Its shadow map sends a class to the limit of any representing sequence along the index
ultrafilter; by compactness of $`[0, \infty]` the limit exists. On the classes that come from
nonnegative hyperreals this is the book's definition: the shadow of a limited number, and
$`\infty` for an unlimited one.
-/

section Shadow

/-- **Section 16.2, example 3.** The enlargement of $`[0, \infty]`: classes of sequences of
extended nonnegative reals. -/
abbrev HyperENNReal : Type := Ultrapower ℝ≥0∞

/-- **Section 16.2, example 4.** The extended shadow of an element of the enlargement of
$`[0, \infty]`: the limit of a representing sequence along the index ultrafilter. -/
noncomputable def loebSh (x : HyperENNReal) : ℝ≥0∞ :=
  Germ.liftOn x (fun f => (Ultrafilter.map f (hyperfilter ℕ)).lim) fun f g h => by
    have : Ultrafilter.map f (hyperfilter ℕ) = Ultrafilter.map g (hyperfilter ℕ) :=
      Ultrafilter.coe_injective (Filter.map_congr h)
    simp only [this]

/-- A sequence of extended nonnegative reals converges along the index ultrafilter to the
extended shadow of its class. -/
theorem tendsto_loebSh (f : ℕ → ℝ≥0∞) :
    Tendsto f (hyperfilter ℕ) (𝓝 (loebSh (Germ.ofFun f))) :=
  (Ultrafilter.map f (hyperfilter ℕ)).le_nhds_lim

/-- The extended shadow of the class of a sequence is its limit along the index ultrafilter,
whenever a limit is known. -/
theorem loebSh_eq_of_tendsto {f : ℕ → ℝ≥0∞} {a : ℝ≥0∞}
    (h : Tendsto f (hyperfilter ℕ) (𝓝 a)) : loebSh (Germ.ofFun f) = a :=
  tendsto_nhds_unique (tendsto_loebSh f) h

/-- The extended shadow of a standard element is that element. -/
theorem loebSh_const (r : ℝ≥0∞) : loebSh (↑r : HyperENNReal) = r :=
  loebSh_eq_of_tendsto (f := fun _ => r) tendsto_const_nhds

/-- The extended shadow is additive. -/
theorem loebSh_add (x y : HyperENNReal) : loebSh (x + y) = loebSh x + loebSh y := by
  induction x, y using Germ.inductionOn₂ with
  | _ f g => exact loebSh_eq_of_tendsto (f := f + g) ((tendsto_loebSh f).add (tendsto_loebSh g))

/-- The extended shadow is monotone. -/
theorem loebSh_mono {x y : HyperENNReal} (h : x ≤ y) : loebSh x ≤ loebSh y := by
  induction x, y using Germ.inductionOn₂ with
  | _ f g => exact le_of_tendsto_of_tendsto (tendsto_loebSh f) (tendsto_loebSh g) (Germ.coe_le.1 h)

/-- If $`x \le r` for a standard $`r`, then the extended shadow of $`x` is at most $`r`. -/
theorem loebSh_le_of_le_const {x : HyperENNReal} {r : ℝ≥0∞} (h : x ≤ (↑r : HyperENNReal)) :
    loebSh x ≤ r := by
  have := loebSh_mono h
  rwa [loebSh_const] at this

/-- If the extended shadow of $`x` is less than a standard $`r`, then $`x < r`. -/
theorem lt_const_of_loebSh_lt {x : HyperENNReal} {r : ℝ≥0∞} (h : loebSh x < r) :
    x < (↑r : HyperENNReal) := by
  induction x using Germ.inductionOn with
  | _ f => exact Germ.coe_lt.2 ((tendsto_loebSh f).eventually (eventually_lt_nhds h))

/-- The inclusion of the nonnegative hyperreals in the enlargement of $`[0, \infty]`
(negative numbers are sent to zero). -/
noncomputable def hyperENNRealOfHyperreal (h : ℝ*) : HyperENNReal := Germ.map ENNReal.ofReal h

/-- A real sequence whose class is limited converges along the index ultrafilter to the
shadow of the class. -/
theorem tendsto_sh_ofSeq {f : ℕ → ℝ} (hl : Limited (Hyperreal.ofSeq f)) :
    Tendsto f (hyperfilter ℕ) (𝓝 (sh (Hyperreal.ofSeq f))) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have h1 := infClose_iff_abs_lt.1 hl.infClose_sh η hη
  have h2 : |Hyperreal.ofSeq f - (sh (Hyperreal.ofSeq f) : ℝ*)| =
      Hyperreal.ofSeq fun n => |f n - sh (Hyperreal.ofSeq f)| := rfl
  rw [h2] at h1
  exact (ofSeq_lt_ofSeq_iff (s := fun _ => η)).1 h1

/-- **Section 16.2, example 4**, the definition of $`\mu_L` in the book's terms: on a limited
nonnegative hyperreal the extended shadow is the shadow of Chapter 5. -/
theorem loebSh_of_limited {h : ℝ*} (hl : Limited h) :
    loebSh (hyperENNRealOfHyperreal h) = ENNReal.ofReal (sh h) := by
  obtain ⟨f, rfl⟩ := hyperreal_exists_rep h
  exact loebSh_eq_of_tendsto (f := fun n => ENNReal.ofReal (f n))
    ((ENNReal.continuous_ofReal.tendsto _).comp (tendsto_sh_ofSeq hl))

/-- **Section 16.2, example 4**, the definition of $`\mu_L` in the book's terms: on a positive
unlimited hyperreal the extended shadow is $`\infty`. -/
theorem loebSh_of_posUnlimited {h : ℝ*} (hu : PosUnlimited h) :
    loebSh (hyperENNRealOfHyperreal h) = ∞ := by
  obtain ⟨f, rfl⟩ := hyperreal_exists_rep h
  refine loebSh_eq_of_tendsto (f := fun n => ENNReal.ofReal (f n)) ?_
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro x
  have := (ofSeq_lt_ofSeq_iff (r := fun _ => (x : ℝ))).1 (hu x)
  filter_upwards [this] with n hn
  rw [← ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt x.coe_nonneg hn)).2 hn

/-- **Section 16.2, example 4.** Every element of the enlargement of $`[0, \infty]` is either
the standard element $`\infty` or the image of a nonnegative hyperreal. In the ultrapower: a
sequence in $`[0, \infty]` is either equal to $`\infty` at almost all indices or finite at
almost all indices, because the index filter is an ultrafilter. -/
theorem hyperENNReal_eq_top_or_exists (x : HyperENNReal) :
    x = (↑(∞ : ℝ≥0∞) : HyperENNReal) ∨ ∃ h : ℝ*, 0 ≤ h ∧ x = hyperENNRealOfHyperreal h := by
  induction x using Germ.inductionOn with
  | _ f =>
    rcases (hyperfilter ℕ).em (fun n => f n = ∞) with h | h
    · exact Or.inl (Germ.coe_eq.2 h)
    · refine Or.inr ⟨Hyperreal.ofSeq fun n => (f n).toReal, ?_, ?_⟩
      · change Hyperreal.ofSeq (fun _ => 0) ≤ _
        rw [ofSeq_le_ofSeq_iff]
        exact Eventually.of_forall fun n => ENNReal.toReal_nonneg
      · exact Germ.coe_eq.2 (h.mono fun n hn => (ENNReal.ofReal_toReal hn).symm)

open Classical in
/-- **Section 16.2, example 4**, the case definition of the extended shadow on the whole
enlargement of $`[0, \infty]`. An element $`x` is either $`\infty`, with shadow $`\infty`, or
a nonnegative hyperreal $`h`, and then its extended shadow is $`\operatorname{sh}(h)` if $`h`
is limited and $`\infty` if $`h` is unlimited. So {name}`Goldblatt.loebSh` is the function the
book defines by cases. -/
theorem loebSh_eq_top_or_exists (x : HyperENNReal) :
    x = (↑(∞ : ℝ≥0∞) : HyperENNReal) ∧ loebSh x = ∞ ∨
      ∃ h : ℝ*, 0 ≤ h ∧ x = hyperENNRealOfHyperreal h ∧
        loebSh x = if Limited h then ENNReal.ofReal (sh h) else ∞ := by
  rcases hyperENNReal_eq_top_or_exists x with rfl | ⟨h, h0, rfl⟩
  · exact Or.inl ⟨rfl, loebSh_const _⟩
  · refine Or.inr ⟨h, h0, rfl, ?_⟩
    split_ifs with hl
    · exact loebSh_of_limited hl
    · exact loebSh_of_posUnlimited (posUnlimited_of_not_limited_of_nonneg hl h0)

end Shadow

/-!
## Internal measures and their Loeb measures

The data of Section 16.5 in the ultrapower: a sequence of rings of subsets of $`\beta` and a
sequence of finitely additive functions on them. The members of the internal ring are the
internal sets $`[B_n]` with $`B_n` in the $`n`-th ring for almost all $`n`, and the internal
measure of $`[B_n]` is the class of the sequence of the measures of the $`B_n`.
-/

section InternalCollection

variable {β βS : Type u} [StarType β βS]

/-- **Section 16.5.** The internal collection of internal sets presented by a sequence
$`(\mathcal A_n)` of collections of subsets of $`\beta`: its members are the internal sets
$`[B_n]` with $`B_n \in \mathcal A_n` for almost all $`n`. -/
def internalCollection (𝔄 : ℕ → Set (Set β)) : Set (Set βS) :=
  {X | ∃ B : ℕ → Set β, X = internalSet B ∧ ∀ᶠ n in hyperfilter ℕ, B n ∈ 𝔄 n}

/-- Membership of $`[B_n]` in the internal collection $`[\mathcal A_n]` does not depend on the
sequence that defines the set. -/
theorem internalSet_mem_internalCollection {𝔄 : ℕ → Set (Set β)} {B : ℕ → Set β} :
    (internalSet B : Set βS) ∈ internalCollection 𝔄 ↔ ∀ᶠ n in hyperfilter ℕ, B n ∈ 𝔄 n := by
  constructor
  · rintro ⟨B', hBB', hB'⟩
    filter_upwards [internalSet_eq_iff.1 hBB', hB'] with n h1 h2
    rwa [h1]
  · exact fun h => ⟨B, rfl, h⟩

/-- **Section 16.5.** If the internal collection $`[\mathcal A_n]` is a ring of sets, then
$`\mathcal A_n` is a ring for almost all $`n`. Otherwise almost every $`\mathcal A_n` would
contain a pair of sets whose difference or union is missing, and the classes of these sets
would witness that the internal collection is not a ring. -/
theorem eventually_isRingOfSets_of_internalCollection {𝔄 : ℕ → Set (Set β)}
    (h : IsRingOfSets (internalCollection 𝔄 : Set (Set βS))) :
    ∀ᶠ n in hyperfilter ℕ, IsRingOfSets (𝔄 n) := by
  by_contra hcon
  rw [← Ultrafilter.eventually_not] at hcon
  have h0 : ∀ᶠ n in hyperfilter ℕ, ∅ ∈ 𝔄 n := by
    obtain ⟨B, hB, hB'⟩ := h.empty_mem
    filter_upwards [internalSet_eq_empty_iff.1 hB.symm, hB'] with n h1 h2
    rwa [h1] at h2
  have hex : ∀ n, ∃ A B : Set β, ¬ IsRingOfSets (𝔄 n) → ∅ ∈ 𝔄 n →
      A ∈ 𝔄 n ∧ B ∈ 𝔄 n ∧ (A \ B ∉ 𝔄 n ∨ A ∪ B ∉ 𝔄 n) := by
    intro n
    by_cases hn : ∃ A B : Set β, A ∈ 𝔄 n ∧ B ∈ 𝔄 n ∧ (A \ B ∉ 𝔄 n ∨ A ∪ B ∉ 𝔄 n)
    · obtain ⟨A, B, hAB⟩ := hn
      exact ⟨A, B, fun _ _ => hAB⟩
    · refine ⟨∅, ∅, fun hnr hne => (hnr ⟨⟨∅, hne⟩, fun A B hA hB => ?_, fun A B hA hB => ?_⟩).elim⟩
      · by_contra hd
        exact hn ⟨A, B, hA, hB, Or.inl hd⟩
      · by_contra hd
        exact hn ⟨A, B, hA, hB, Or.inr hd⟩
  choose a b hab using hex
  have hA : (internalSet a : Set βS) ∈ internalCollection 𝔄 :=
    ⟨a, rfl, by filter_upwards [hcon, h0] with n h1 h2 using (hab n h1 h2).1⟩
  have hB : (internalSet b : Set βS) ∈ internalCollection 𝔄 :=
    ⟨b, rfl, by filter_upwards [hcon, h0] with n h1 h2 using (hab n h1 h2).2.1⟩
  have hd := h.diff_mem hA hB
  have hu := h.union_mem hA hB
  rw [internalSet_diff, internalSet_mem_internalCollection] at hd
  rw [internalSet_union, internalSet_mem_internalCollection] at hu
  obtain ⟨n, h1, h2, h3, h4⟩ := (hcon.and (h0.and (hd.and hu))).exists
  rcases (hab n h1 h2).2.2 with h | h
  · exact h h3
  · exact h h4

/-- **Section 16.5.** If the internal function $`[\mu_n]`, which sends $`[B_n]` to the class
of $`(\mu_n(B_n))`, is finitely additive on the internal collection $`[\mathcal A_n]` (it
vanishes at the empty set and is additive on disjoint pairs of members), then $`\mu_n` is
finitely additive on $`\mathcal A_n` for almost all $`n`. -/
theorem eventually_isFinitelyAdditive_of_internalCollection {𝔄 : ℕ → Set (Set β)}
    {m : ℕ → Set β → ℝ≥0∞} (h0 : (Germ.ofFun (fun n => m n ∅) : HyperENNReal) = 0)
    (hadd : ∀ A B : ℕ → Set β, (internalSet A : Set βS) ∈ internalCollection 𝔄 →
      (internalSet B : Set βS) ∈ internalCollection 𝔄 →
      Disjoint (internalSet A : Set βS) (internalSet B) →
      (Germ.ofFun (fun n => m n (A n ∪ B n)) : HyperENNReal) =
        Germ.ofFun (fun n => m n (A n)) + Germ.ofFun fun n => m n (B n)) :
    ∀ᶠ n in hyperfilter ℕ, IsFinitelyAdditive (𝔄 n) (m n) := by
  by_contra hcon
  rw [← Ultrafilter.eventually_not] at hcon
  have h0' : ∀ᶠ n in hyperfilter ℕ, m n ∅ = 0 := Germ.coe_eq.1 h0
  have hex : ∀ n, ∃ A B : Set β, ¬ IsFinitelyAdditive (𝔄 n) (m n) → m n ∅ = 0 →
      A ∈ 𝔄 n ∧ B ∈ 𝔄 n ∧ Disjoint A B ∧ m n (A ∪ B) ≠ m n A + m n B := by
    intro n
    by_cases hn : ∃ A B : Set β, A ∈ 𝔄 n ∧ B ∈ 𝔄 n ∧ Disjoint A B ∧ m n (A ∪ B) ≠ m n A + m n B
    · obtain ⟨A, B, hAB⟩ := hn
      exact ⟨A, B, fun _ _ => hAB⟩
    · refine ⟨∅, ∅, fun hnf hne => (hnf ⟨hne, fun A B hA hB hAB => ?_⟩).elim⟩
      by_contra hd
      exact hn ⟨A, B, hA, hB, hAB, hd⟩
  choose a b hab using hex
  have hA : (internalSet a : Set βS) ∈ internalCollection 𝔄 :=
    ⟨a, rfl, by filter_upwards [hcon, h0'] with n h1 h2 using (hab n h1 h2).1⟩
  have hB : (internalSet b : Set βS) ∈ internalCollection 𝔄 :=
    ⟨b, rfl, by filter_upwards [hcon, h0'] with n h1 h2 using (hab n h1 h2).2.1⟩
  have hdis : Disjoint (internalSet a : Set βS) (internalSet b) := by
    rw [Set.disjoint_iff_inter_eq_empty, internalSet_inter, internalSet_eq_empty_iff]
    filter_upwards [hcon, h0'] with n h1 h2
    exact Set.disjoint_iff_inter_eq_empty.1 (hab n h1 h2).2.2.1
  have heq : ∀ᶠ n in hyperfilter ℕ, m n (a n ∪ b n) = m n (a n) + m n (b n) :=
    Germ.coe_eq.1 (hadd a b hA hB hdis)
  obtain ⟨n, h1, h2, h3⟩ := (hcon.and (h0'.and heq)).exists
  exact (hab n h1 h2).2.2.2 h3

end InternalCollection

/-- **Section 16.5.** An internal ring of internal subsets of the star type of $`\beta`
together with an internal finitely additive function on it, presented by sequences: the
$`n`-th ring $`\mathcal A_n` and the $`n`-th finitely additive function $`\mu_n`.

Requiring every term to be a ring and every $`\mu_n` to be finitely additive loses nothing.
An internal collection that is a ring has almost all of its terms rings
({name}`Goldblatt.eventually_isRingOfSets_of_internalCollection`), an internal function that
is finitely additive on it has almost all of its terms finitely additive
({name}`Goldblatt.eventually_isFinitelyAdditive_of_internalCollection`), and a pair of
sequences with these properties at almost all indices can be corrected on the remaining
indices without changing the internal ring or the internal function
({lit}`Goldblatt.InternalMeasure.ofEventually`,
{lit}`Goldblatt.InternalMeasure.sets_ofEventually`,
{lit}`Goldblatt.InternalMeasure.μ_ofEventually`). -/
structure InternalMeasure (β : Type u) where
  /-- The sequence of rings. -/
  𝔄 : ℕ → Set (Set β)
  /-- The sequence of finitely additive functions. -/
  m : ℕ → Set β → ℝ≥0∞
  /-- Each term of the first sequence is a ring. -/
  isRing : ∀ n, IsRingOfSets (𝔄 n)
  /-- Each term of the second sequence is finitely additive. -/
  isFinitelyAdditive : ∀ n, IsFinitelyAdditive (𝔄 n) (m n)

namespace InternalMeasure

variable {β βS : Type u} [StarType β βS] (I : InternalMeasure β)

/-- **Section 16.5.** The internal ring $`\mathcal A`: the internal sets $`[B_n]` such that
$`B_n \in \mathcal A_n` for almost all $`n`. -/
def sets : Set (Set βS) :=
  {X | ∃ B : ℕ → Set β, X = internalSet B ∧ ∀ᶠ n in hyperfilter ℕ, B n ∈ I.𝔄 n}

/-- The internal ring is the internal collection of the sequence of rings. -/
theorem sets_eq_internalCollection : (I.sets : Set (Set βS)) = internalCollection I.𝔄 := rfl

/-- Membership of $`[B_n]` in the internal ring does not depend on the defining sequence. -/
theorem internalSet_mem_sets {B : ℕ → Set β} :
    (internalSet B : Set βS) ∈ I.sets ↔ ∀ᶠ n in hyperfilter ℕ, B n ∈ I.𝔄 n := by
  constructor
  · rintro ⟨B', hBB', hB'⟩
    filter_upwards [internalSet_eq_iff.1 hBB', hB'] with n h1 h2
    rwa [h1]
  · exact fun h => ⟨B, rfl, h⟩

/-- Every member of the internal ring is an internal set. -/
theorem isInternalSet_of_mem_sets {X : Set βS} (hX : X ∈ I.sets) : IsInternalSet β X := by
  obtain ⟨B, rfl, -⟩ := hX
  exact ⟨B, rfl⟩

open Classical in
/-- **Section 16.5.** The internal measure $`\mu`: its value at $`[B_n]` is the class of the
sequence $`(\mu_n(B_n))`. (At a set that is not internal the value is zero.) -/
noncomputable def μ (X : Set βS) : HyperENNReal :=
  if h : IsInternalSet β X then Germ.ofFun fun n => I.m n (h.choose n) else 0

/-- **Section 16.5.** The internal measure of $`[B_n]` is the class of the sequence
$`(\mu_n(B_n))`, whatever sequence defines the set. -/
theorem μ_internalSet (B : ℕ → Set β) :
    I.μ (internalSet B : Set βS) = Germ.ofFun fun n => I.m n (B n) := by
  have h : IsInternalSet β (internalSet B : Set βS) := ⟨B, rfl⟩
  rw [μ, dite_eq_left_of_eq_true (eq_true h)]
  refine Germ.coe_eq.2 ?_
  filter_upwards [internalSet_eq_iff.1 h.choose_spec] with n hn
  rw [hn]

open Classical in
/-- **Section 16.5.** The internal measure presented by sequences $`(\mathcal A_n)` and
$`(\mu_n)` of which only almost all terms are known to be a ring with a finitely additive
function: at an index where this fails, the collection is replaced by $`\{\emptyset\}` and
the function by zero. -/
noncomputable def ofEventually (𝔄 : ℕ → Set (Set β)) (m : ℕ → Set β → ℝ≥0∞) :
    InternalMeasure β where
  𝔄 n := if IsRingOfSets (𝔄 n) ∧ IsFinitelyAdditive (𝔄 n) (m n) then 𝔄 n else {∅}
  m n := if IsRingOfSets (𝔄 n) ∧ IsFinitelyAdditive (𝔄 n) (m n) then m n else 0
  isRing n := by
    split_ifs with h
    · exact h.1
    · exact ⟨⟨∅, rfl⟩, by rintro _ _ rfl rfl; simp, by rintro _ _ rfl rfl; simp⟩
  isFinitelyAdditive n := by
    split_ifs with h
    · exact h.2
    · exact ⟨rfl, fun _ _ _ _ _ => by simp⟩

/-- **Section 16.5.** Correcting the sequences on a negligible set of indices does not change
the internal ring. -/
theorem sets_ofEventually {𝔄 : ℕ → Set (Set β)} {m : ℕ → Set β → ℝ≥0∞}
    (h : ∀ᶠ n in hyperfilter ℕ, IsRingOfSets (𝔄 n) ∧ IsFinitelyAdditive (𝔄 n) (m n)) :
    ((ofEventually 𝔄 m).sets : Set (Set βS)) = internalCollection 𝔄 := by
  ext X
  constructor
  · rintro ⟨B, rfl, hB⟩
    refine ⟨B, rfl, ?_⟩
    filter_upwards [h, hB] with n hn hBn
    simpa only [ofEventually, hn, and_self, ite_true] using hBn
  · rintro ⟨B, rfl, hB⟩
    refine ⟨B, rfl, ?_⟩
    filter_upwards [h, hB] with n hn hBn
    simpa only [ofEventually, hn, and_self, ite_true] using hBn

/-- **Section 16.5.** Correcting the sequences on a negligible set of indices does not change
the internal function: its value at $`[B_n]` is still the class of $`(\mu_n(B_n))`. -/
theorem μ_ofEventually {𝔄 : ℕ → Set (Set β)} {m : ℕ → Set β → ℝ≥0∞}
    (h : ∀ᶠ n in hyperfilter ℕ, IsRingOfSets (𝔄 n) ∧ IsFinitelyAdditive (𝔄 n) (m n))
    (B : ℕ → Set β) :
    (ofEventually 𝔄 m).μ (internalSet B : Set βS) = Germ.ofFun fun n => m n (B n) := by
  rw [μ_internalSet]
  refine Germ.coe_eq.2 ?_
  filter_upwards [h] with n hn
  simp only [ofEventually, hn, and_self, ite_true]

/-- **Section 16.2, example 4.** The function $`\mu_L`: the extended shadow of the internal
measure, $`\mu_L(A) = \operatorname{sh}(\mu(A))` if $`\mu(A)` is limited and
$`\mu_L(A) = \infty` otherwise. -/
noncomputable def μL (X : Set βS) : ℝ≥0∞ := loebSh (I.μ X)

/-- $`\mu_L([B_n])` is the limit of $`\mu_n(B_n)` along the index ultrafilter. -/
theorem tendsto_μL (B : ℕ → Set β) :
    Tendsto (fun n => I.m n (B n)) (hyperfilter ℕ) (𝓝 (I.μL (internalSet B : Set βS))) := by
  rw [μL, μ_internalSet]
  exact tendsto_loebSh _

/-- **Section 16.5.** The internal ring is a ring of sets. -/
theorem isRingOfSets_sets : IsRingOfSets (I.sets : Set (Set βS)) := by
  refine ⟨⟨∅, fun _ => ∅, ?_, Eventually.of_forall fun n => (I.isRing n).empty_mem⟩, ?_, ?_⟩
  · rw [← starSet_eq_internalSet, starSet_empty]
  · rintro _ _ ⟨A, rfl, hA⟩ ⟨B, rfl, hB⟩
    rw [internalSet_diff]
    exact ⟨_, rfl, by filter_upwards [hA, hB] with n h1 h2 using (I.isRing n).diff_mem h1 h2⟩
  · rintro _ _ ⟨A, rfl, hA⟩ ⟨B, rfl, hB⟩
    rw [internalSet_union]
    exact ⟨_, rfl, by filter_upwards [hA, hB] with n h1 h2 using (I.isRing n).union_mem h1 h2⟩

/-- **Section 16.1, example 6.** If almost every $`\mathcal A_n` is an algebra, then so is the
internal ring: the whole space is the internal set of the constant sequence of whole spaces.
This is the transfer argument by which the enlargement of an algebra is an algebra. -/
theorem isAlgebraOfSets_sets (h : ∀ᶠ n in hyperfilter ℕ, univ ∈ I.𝔄 n) :
    IsAlgebraOfSets (I.sets : Set (Set βS)) :=
  { I.isRingOfSets_sets with
    univ_mem := ⟨fun _ => univ, by rw [← starSet_eq_internalSet, starSet_univ], h⟩ }

/-- **Section 16.2, example 4.** $`\mu_L` is finitely additive on the internal ring. -/
theorem isFinitelyAdditive_μL : IsFinitelyAdditive (I.sets : Set (Set βS)) I.μL := by
  constructor
  · have h : (∅ : Set βS) = internalSet fun _ => (∅ : Set β) := by
      rw [← starSet_eq_internalSet, starSet_empty]
    rw [h]
    refine tendsto_nhds_unique (I.tendsto_μL _) ?_
    simp only [(I.isFinitelyAdditive _).empty]
    exact tendsto_const_nhds
  · rintro _ _ ⟨A, rfl, hA⟩ ⟨B, rfl, hB⟩ hAB
    have hd : ∀ᶠ n in hyperfilter ℕ, Disjoint (A n) (B n) := by
      have := internalSet_eq_empty_iff.1
        ((internalSet_inter A B).symm.trans (Set.disjoint_iff_inter_eq_empty.1 hAB))
      exact this.mono fun n hn => Set.disjoint_iff_inter_eq_empty.2 hn
    have h1 := (I.tendsto_μL (βS := βS) A).add (I.tendsto_μL (βS := βS) B)
    have h2 := I.tendsto_μL (βS := βS) fun n => A n ∪ B n
    rw [← internalSet_union A B] at h2
    refine tendsto_nhds_unique h2 (h1.congr' ?_)
    filter_upwards [hA, hB, hd] with n hA hB hd
    exact ((I.isFinitelyAdditive n).union hA hB hd).symm

/-- **Lemma 16.5.1, the saturation step.** An increasing sequence of members of the internal
ring whose $`\mu_L`-measures are at most $`r` is included in a single member of
$`\mu_L`-measure at most $`r`. The book extends the sequence to an internal hypersequence and
applies overflow; here countable saturation is applied to the internal sets of sets
$`\{D \in \mathcal A : A_k \subseteq D,\ \mu(D) \le r + \tfrac1{k+1}\}`, which decrease and
are nonempty. -/
theorem exists_upper {A : ℕ → Set βS} (r : ℝ≥0∞) (hA : ∀ k, A k ∈ I.sets) (hmono : Monotone A)
    (hr : ∀ k, I.μL (A k) ≤ r) : ∃ D ∈ I.sets, (∀ k, A k ⊆ D) ∧ I.μL D ≤ r := by
  choose a ha ha' using hA
  let η : ℕ → ℝ≥0∞ := fun k => ((k + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hη : ∀ k, η (k + 1) ≤ η k := fun k =>
    ENNReal.inv_le_inv.2 (by exact_mod_cast Nat.le_succ (k + 1))
  let X : ℕ → Set (Ultrapower (Set β)) := fun k =>
    internalSet fun n => {K | K ∈ I.𝔄 n ∧ a k n ⊆ K ∧ I.m n K ≤ r + η k}
  have hsub : ∀ k, ∀ᶠ n in hyperfilter ℕ, a k n ⊆ a (k + 1) n := fun k =>
    internalSet_subset_iff.1 (by
      rw [← ha k, ← ha (k + 1)]; exact hmono (Nat.le_succ k) : (internalSet (a k) : Set βS) ⊆ _)
  have hne : ∀ k, (X k).Nonempty := by
    intro k
    refine ⟨ofSeq (a k), ofSeq_mem_internalSet.2 ?_⟩
    have hle : ∀ᶠ n in hyperfilter ℕ, I.m n (a k n) ≤ r + η k := by
      by_cases hrt : r = ∞
      · exact Eventually.of_forall fun n => by rw [hrt, top_add]; exact le_top
      · have hlt : I.μL (A k) < r + η k :=
          lt_of_le_of_lt (hr k) (ENNReal.lt_add_right hrt (by simp [η]))
        have := I.tendsto_μL (βS := βS) (a k)
        rw [← ha k] at this
        exact (this.eventually (eventually_lt_nhds hlt)).mono fun n hn => hn.le
    filter_upwards [ha' k, hle] with n h1 h2
    exact ⟨h1, Subset.rfl, h2⟩
  have hdec : ∀ k, X (k + 1) ⊆ X k := by
    intro k
    refine internalSet_subset_iff.2 ?_
    filter_upwards [hsub k] with n hn K hK
    exact ⟨hK.1, hn.trans hK.2.1, hK.2.2.trans (by gcongr; exact hη k)⟩
  obtain ⟨G, hG⟩ := iInter_nonempty_of_isInternalSet (α := Set β)
    (fun k => isInternalSet_internalSet _) hne hdec
  obtain ⟨κ, rfl⟩ := ofSeq_surjective (α := Set β) G
  have hκ : ∀ k, ∀ᶠ n in hyperfilter ℕ,
      κ n ∈ I.𝔄 n ∧ a k n ⊆ κ n ∧ I.m n (κ n) ≤ r + η k := fun k =>
    ofSeq_mem_internalSet.1 (mem_iInter.1 hG k)
  refine ⟨internalSet κ, ⟨κ, rfl, (hκ 0).mono fun n h => h.1⟩, fun k => ?_, ?_⟩
  · rw [ha k]
    exact internalSet_subset_iff.2 ((hκ k).mono fun n h => h.2.1)
  · have hk : ∀ k, I.μL (internalSet κ : Set βS) ≤ r + η k := fun k =>
      le_of_tendsto (I.tendsto_μL κ) ((hκ k).mono fun n h => h.2.2)
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    obtain ⟨k, hk'⟩ := ENNReal.exists_inv_nat_lt (a := (δ : ℝ≥0∞)) (by exact_mod_cast hδ.ne')
    refine (hk k).trans ?_
    gcongr
    exact (ENNReal.inv_le_inv.2 (by exact_mod_cast Nat.le_succ k)).trans hk'.le

/-- **Lemma 16.6.2, the saturation step.** If $`(C_k)` is an increasing and $`(D_k)` a
decreasing sequence of members of the internal ring with every $`C_j` included in every
$`D_k`, then some member $`K` of the ring has $`C_k \subseteq K \subseteq D_k` for all $`k`.
The book extends the sequences to internal hypersequences and takes $`D_K` for an unlimited
$`K` given by overflow; here countable saturation is applied to the internal sets of sets
$`\{K \in \mathcal A : C_k \subseteq K \subseteq D_k\}`. -/
theorem exists_between {C D : ℕ → Set βS} (hC : ∀ k, C k ∈ I.sets) (hD : ∀ k, D k ∈ I.sets)
    (hCmono : Monotone C) (hDanti : Antitone D) (hCD : ∀ j k, C j ⊆ D k) :
    ∃ K ∈ I.sets, ∀ k, C k ⊆ K ∧ K ⊆ D k := by
  choose c hc hc' using hC
  choose d hd hd' using hD
  let X : ℕ → Set (Ultrapower (Set β)) := fun k =>
    internalSet fun n => {K | K ∈ I.𝔄 n ∧ c k n ⊆ K ∧ K ⊆ d k n}
  have hcsub : ∀ k, ∀ᶠ n in hyperfilter ℕ, c k n ⊆ c (k + 1) n := fun k =>
    internalSet_subset_iff.1 (by
      rw [← hc k, ← hc (k + 1)]; exact hCmono (Nat.le_succ k) : (internalSet (c k) : Set βS) ⊆ _)
  have hdsub : ∀ k, ∀ᶠ n in hyperfilter ℕ, d (k + 1) n ⊆ d k n := fun k =>
    internalSet_subset_iff.1 (by
      rw [← hd k, ← hd (k + 1)]; exact hDanti (Nat.le_succ k) :
        (internalSet (d (k + 1)) : Set βS) ⊆ _)
  have hcd : ∀ k, ∀ᶠ n in hyperfilter ℕ, c k n ⊆ d k n := fun k =>
    internalSet_subset_iff.1 (by
      rw [← hc k, ← hd k]; exact hCD k k : (internalSet (c k) : Set βS) ⊆ _)
  have hne : ∀ k, (X k).Nonempty := fun k =>
    ⟨ofSeq (c k), ofSeq_mem_internalSet.2 (by
      filter_upwards [hc' k, hcd k] with n h1 h2 using ⟨h1, Subset.rfl, h2⟩)⟩
  have hdec : ∀ k, X (k + 1) ⊆ X k := by
    intro k
    refine internalSet_subset_iff.2 ?_
    filter_upwards [hcsub k, hdsub k] with n h1 h2 K hK
    exact ⟨hK.1, h1.trans hK.2.1, hK.2.2.trans h2⟩
  obtain ⟨G, hG⟩ := iInter_nonempty_of_isInternalSet (α := Set β)
    (fun k => isInternalSet_internalSet _) hne hdec
  obtain ⟨κ, rfl⟩ := ofSeq_surjective (α := Set β) G
  have hκ : ∀ k, ∀ᶠ n in hyperfilter ℕ, κ n ∈ I.𝔄 n ∧ c k n ⊆ κ n ∧ κ n ⊆ d k n := fun k =>
    ofSeq_mem_internalSet.1 (mem_iInter.1 hG k)
  refine ⟨internalSet κ, ⟨κ, rfl, (hκ 0).mono fun n h => h.1⟩, fun k => ⟨?_, ?_⟩⟩
  · rw [hc k]
    exact internalSet_subset_iff.2 ((hκ k).mono fun n h => h.2.1)
  · rw [hd k]
    exact internalSet_subset_iff.2 ((hκ k).mono fun n h => h.2.2)

/-- **Section 16.1, example 6.** If a sequence of members of an internal ring has its union
in the ring, then some finite initial segment of the sequence already has that union
(Corollary 11.10.2 of countable saturation). Countable additivity of $`\mu_L` on the ring
rests on this. -/
theorem exists_iUnion_eq_biUnion_le_of_mem_sets {A : ℕ → Set βS} (hA : ∀ n, A n ∈ I.sets)
    (hU : ⋃ n, A n ∈ I.sets) : ∃ k, ⋃ n, A n = ⋃ n ≤ k, A n :=
  exists_iUnion_eq_biUnion_le (fun n => I.isInternalSet_of_mem_sets (hA n))
    (I.isInternalSet_of_mem_sets hU)

/-- **Section 16.1, example 6.** The union of a strictly increasing sequence of members of an
internal ring is not in the ring; so an internal ring with such a sequence is not a
sigma-ring. -/
theorem iUnion_notMem_sets_of_ssubset {A : ℕ → Set βS} (hA : ∀ n, A n ∈ I.sets)
    (hinc : ∀ n, A n ⊂ A (n + 1)) : ⋃ n, A n ∉ I.sets := fun hU =>
  not_isInternalSet_iUnion_of_ssubset_succ (fun n => I.isInternalSet_of_mem_sets (hA n)) hinc
    (I.isInternalSet_of_mem_sets hU)

/-- **Section 16.1, example 6.** The union of a pairwise disjoint sequence of members of an
internal ring, infinitely many of which are nonempty, is not in the ring: a finite initial
segment with the same union would have to meet a later nonempty term. -/
theorem iUnion_notMem_sets_of_pairwise_disjoint {A : ℕ → Set βS} (hA : ∀ n, A n ∈ I.sets)
    (hd : Pairwise (Disjoint on A)) (hne : ∀ k, ∃ n > k, (A n).Nonempty) :
    ⋃ n, A n ∉ I.sets := by
  intro hU
  obtain ⟨k, hk⟩ := I.exists_iUnion_eq_biUnion_le_of_mem_sets hA hU
  obtain ⟨n, hn, x, hx⟩ := hne k
  have hx' : x ∈ ⋃ i ≤ k, A i := hk ▸ mem_iUnion.2 ⟨n, hx⟩
  simp only [mem_iUnion, exists_prop] at hx'
  obtain ⟨i, hi, hxi⟩ := hx'
  exact (hd (show i ≠ n by omega)).le_bot ⟨hxi, hx⟩

/-- **Section 16.5.** Every internal finitely additive measure on an internal ring has the
three saturation properties of part 3, and therefore a Loeb measure. -/
noncomputable def toLoebPremeasure : LoebPremeasure βS where
  ring := I.sets
  μL := I.μL
  isRing := I.isRingOfSets_sets
  isFinitelyAdditive := I.isFinitelyAdditive_μL
  finite_union _ hA hU := I.exists_iUnion_eq_biUnion_le_of_mem_sets hA hU
  exists_upper _ r hA hmono hr := I.exists_upper r hA hmono hr
  exists_between _ _ hC hD hCmono hDanti hCD := I.exists_between hC hD hCmono hDanti hCD

/-- The ring of the Loeb premeasure of an internal measure is its internal ring. -/
@[simp] theorem toLoebPremeasure_ring : (I.toLoebPremeasure (βS := βS)).ring = I.sets := rfl

/-- The function of the Loeb premeasure of an internal measure is $`\mu_L`. -/
@[simp] theorem toLoebPremeasure_μL : (I.toLoebPremeasure (βS := βS)).μL = I.μL := rfl

/-- **Section 16.2, example 4.** $`\mu_L` is countably additive on the internal ring: it is a
measure there. -/
theorem isMeasureOnRing_μL : IsMeasureOnRing (I.sets : Set (Set βS)) I.μL :=
  (I.toLoebPremeasure (βS := βS)).isMeasureOnRing

/-- **Section 16.6**, the definition of approximability in terms of the internal measure
itself: $`B` is approximable if and only if for every real $`\varepsilon > 0` there are
$`C, D` in the internal ring with $`C \subseteq B \subseteq D` and
$`\mu(D - C) < \varepsilon`, the inequality being between elements of the enlargement of
$`[0, \infty]`. This is equivalent to the formulation with $`\mu_L` because
$`\mu(A) \simeq \mu_L(A)`. -/
theorem approximable_iff {B : Set βS} :
    (I.toLoebPremeasure (βS := βS)).Approximable B ↔
      ∀ η : ℝ, 0 < η → ∃ C ∈ I.sets, ∃ D ∈ I.sets, C ⊆ B ∧ B ⊆ D ∧
        I.μ (D \ C) < (↑(ENNReal.ofReal η) : HyperENNReal) := by
  constructor
  · intro h η hη
    obtain ⟨C, hC, D, hD, hCB, hBD, hlt⟩ := h η hη
    exact ⟨C, hC, D, hD, hCB, hBD, lt_const_of_loebSh_lt hlt⟩
  · intro h η hη
    obtain ⟨C, hC, D, hD, hCB, hBD, hlt⟩ := h (η / 2) (by positivity)
    refine ⟨C, hC, D, hD, hCB, hBD, lt_of_le_of_lt (loebSh_le_of_le_const hlt.le) ?_⟩
    rw [ENNReal.ofReal_lt_ofReal_iff hη]
    linarith

end InternalMeasure

/-!
## The star-Borel sets

Example 6 of Section 16.1 for the Borel algebra of the real line: its enlargement is an
internal algebra of internal sets of hyperreals that contains the enlargement of every
interval $`(-n, n)` but not their union, the external set of limited hyperreals. So it is not
a sigma-algebra.
-/

namespace InternalMeasure

/-- **Section 16.1, example 6.** The enlargement of the Borel algebra of the real line,
presented by the constant sequence of Borel algebras; as an internal measure it carries the
enlargement of Lebesgue measure. -/
noncomputable def starBorel : InternalMeasure ℝ where
  𝔄 _ := {B | MeasurableSet B}
  m _ := volume
  isRing _ := ⟨⟨∅, mem_ofPred.2 MeasurableSet.empty⟩,
    fun _ _ hA hB => mem_ofPred.2 ((mem_ofPred.1 hA).diff (mem_ofPred.1 hB)),
    fun _ _ hA hB => mem_ofPred.2 ((mem_ofPred.1 hA).union (mem_ofPred.1 hB))⟩
  isFinitelyAdditive _ := ⟨measure_empty, fun _ _ _ hB hAB => measure_union hAB (mem_ofPred.1 hB)⟩

/-- **Section 16.1, example 6.** The star-Borel sets form an algebra. -/
theorem isAlgebraOfSets_sets_starBorel : IsAlgebraOfSets (starBorel.sets : Set (Set ℝ*)) :=
  starBorel.isAlgebraOfSets_sets (Eventually.of_forall fun _ =>
    (mem_ofPred.2 MeasurableSet.univ : univ ∈ {B : Set ℝ | MeasurableSet B}))

/-- **Section 16.1, example 6.** The enlargement of a Borel set is a star-Borel set. -/
theorem starSet_mem_sets_starBorel {B : Set ℝ} (hB : MeasurableSet B) :
    (⋆B : Set ℝ*) ∈ starBorel.sets :=
  ⟨fun _ => B, starSet_eq_internalSet B, Eventually.of_forall fun _ => mem_ofPred.2 hB⟩

/-- **Section 16.1, example 6.** The hyperreal interval $`(-n, n)`, the enlargement of the
real interval, is a star-Borel set. -/
theorem Ioo_neg_natCast_mem_sets_starBorel (n : ℕ) :
    Ioo (-(n : ℝ*)) n ∈ (starBorel.sets : Set (Set ℝ*)) :=
  ⟨fun _ => Ioo (-(n : ℝ)) n, (internalSet_Ioo (fun _ => -(n : ℝ)) fun _ => (n : ℝ)).symm,
    Eventually.of_forall fun _ =>
      (mem_ofPred.2 measurableSet_Ioo : Ioo (-(n : ℝ)) n ∈ {B : Set ℝ | MeasurableSet B})⟩

/-- **Section 16.1, example 6.** The set of limited hyperreals is not a star-Borel set,
because it is external. -/
theorem limitedSet_notMem_sets_starBorel : 𝕃 ∉ (starBorel.sets : Set (Set ℝ*)) := fun h =>
  isExternal_limitedSet (starBorel.isInternalSet_of_mem_sets h)

/-- **Section 16.1, example 6.** The algebra of star-Borel sets is not a sigma-algebra: it
contains every interval $`(-n, n)` but not their union, the set of limited hyperreals. -/
theorem not_isSigmaRing_sets_starBorel : ¬ IsSigmaRing (starBorel.sets : Set (Set ℝ*)) := fun h =>
  limitedSet_notMem_sets_starBorel
    (limitedSet_eq_iUnion_Ioo ▸ h.iUnion_mem Ioo_neg_natCast_mem_sets_starBorel)

end InternalMeasure

/-!
## Weighted counting measures on hyperfinite sets

The examples of Section 16.2: on a hyperfinite set $`S = [S_n]`, an internal weighting
$`w = [w_n]` defines the internal measure that sends an internal subset $`A = [A_n]` of
$`S` to the hyperfinite sum of the weights of its points, the class of the sums
$`\sum_{x \in A_n} w_n(x)`. Its ring is the algebra of all internal subsets of $`S`. The
uniform weighting $`1/|S|` gives the normalised counting measure $`|A|/|S|`.
-/

section Weighted

variable {β βS : Type u} [StarType β βS]

/-- A sum of a constant over the points of a finite set that lie in $`B` is the number of
those points times the constant. -/
theorem sum_indicator_const (s : Finset β) (B : Set β) (c : ℝ≥0∞) :
    ∑ x ∈ s, B.indicator (fun _ => c) x = ((↑s ∩ B : Set β).ncard : ℝ≥0∞) * c := by
  classical
  have hfin : (↑s ∩ B : Set β).Finite := s.finite_toSet.subset inter_subset_left
  have h1 : ∑ x ∈ s, B.indicator (fun _ => c) x = ∑ _x ∈ hfin.toFinset, c := by
    rw [← Finset.sum_subset (s₁ := hfin.toFinset) (fun x hx => (hfin.mem_toFinset.1 hx).1)
      (fun x hx hx' => Set.indicator_of_notMem
        (fun hxB => hx' (hfin.mem_toFinset.2 ⟨hx, hxB⟩)) _)]
    exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (hfin.mem_toFinset.1 hx).2 _
  rw [h1, Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card _ hfin]

/-- **Section 16.2, example 5.** The _weighted counting function_ $`\mu_w` on the internal
subsets of the hyperfinite set $`S = [S_n]`, for the internal weighting $`w = [w_n]`:
$`\mu_w(A) = \sum_{s \in A} w(s)`. -/
noncomputable def InternalMeasure.weighted (s : ℕ → Finset β) (w : ℕ → β → ℝ≥0∞) :
    InternalMeasure β where
  𝔄 n := {B | B ⊆ ↑(s n)}
  m n B := ∑ x ∈ s n, B.indicator (w n) x
  isRing n := ⟨⟨∅, empty_subset _⟩, fun _ _ hA _ => sdiff_subset.trans hA,
    fun _ _ hA hB => union_subset hA hB⟩
  isFinitelyAdditive n := ⟨by simp, fun A B _ _ hAB => by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ =>
      congrFun (Set.indicator_union_of_disjoint hAB (w n)) x⟩

/-- **Section 16.2, example 5.** The ring of the weighted counting function is the algebra
$`\mathcal P_I(S)` of all internal subsets of $`S`. -/
theorem InternalMeasure.mem_sets_weighted_iff {s : ℕ → Finset β} {w : ℕ → β → ℝ≥0∞}
    {X : Set βS} :
    X ∈ (InternalMeasure.weighted s w).sets ↔
      IsInternalSet β X ∧ X ⊆ internalSet fun n => (s n : Set β) := by
  constructor
  · rintro ⟨B, rfl, hB⟩
    exact ⟨⟨B, rfl⟩, internalSet_subset_iff.2 hB⟩
  · rintro ⟨⟨B, rfl⟩, hsub⟩
    exact ⟨B, rfl, internalSet_subset_iff.1 hsub⟩

/-- **Section 16.2, example 5.** The hyperfinite set $`S` itself belongs to the ring: the
internal subsets of $`S` form an algebra of subsets of $`S`. -/
theorem InternalMeasure.internalSet_mem_sets_weighted (s : ℕ → Finset β) (w : ℕ → β → ℝ≥0∞) :
    (internalSet (fun n => (s n : Set β)) : Set βS) ∈ (InternalMeasure.weighted s w).sets :=
  ⟨_, rfl, Eventually.of_forall fun _ => Subset.rfl⟩

/-- **Section 16.2, example 5**, at one index: if the $`n`-th ring consists of all subsets of
the finite set $`S_n`, then the $`n`-th measure of a subset of $`S_n` is the sum of the
measures of its singletons. -/
theorem InternalMeasure.m_eq_sum_singleton (I : InternalMeasure β) (s : ℕ → Finset β) (n : ℕ)
    (h𝔄 : I.𝔄 n = {B | B ⊆ ↑(s n)}) {B : Set β} (hB : B ⊆ ↑(s n)) :
    I.m n B = ∑ x ∈ s n, B.indicator (fun x => I.m n {x}) x := by
  classical
  have hfin : B.Finite := (s n).finite_toSet.subset hB
  have hB' : B = ⋃ x ∈ hfin.toFinset, ({x} : Set β) := by
    ext x; simp
  have hsing : ∀ x ∈ hfin.toFinset, ({x} : Set β) ∈ I.𝔄 n := fun x hx => by
    rw [h𝔄]
    exact singleton_subset_iff.2 (hB (hfin.mem_toFinset.1 hx))
  have h1 : I.m n B = ∑ x ∈ hfin.toFinset, I.m n {x} := by
    conv_lhs => rw [hB']
    exact (I.isFinitelyAdditive n).biUnion_finset (I.isRing n) _ hsing
      (fun x _ y _ hxy => disjoint_singleton.2 hxy)
  rw [h1, ← Finset.sum_subset (s₁ := hfin.toFinset) (fun x hx => hB (hfin.mem_toFinset.1 hx))
    (fun x _ hx' => Set.indicator_of_notMem (fun hxB => hx' (hfin.mem_toFinset.2 hxB)) _)]
  exact Finset.sum_congr rfl fun x hx =>
    (Set.indicator_of_mem (hfin.mem_toFinset.1 hx) (fun x => I.m n {x})).symm

/-- **Section 16.2, example 5.** An internal ring whose terms are, at almost all indices, the
collections of all subsets of the finite sets $`S_n` is the algebra $`\mathcal P_I(S)` of
internal subsets of $`S = [S_n]`, the ring of every weighted counting function on $`S`. -/
theorem InternalMeasure.sets_eq_sets_weighted (I : InternalMeasure β) (s : ℕ → Finset β)
    (w : ℕ → β → ℝ≥0∞) (h𝔄 : ∀ᶠ n in hyperfilter ℕ, I.𝔄 n = {B | B ⊆ ↑(s n)}) :
    (I.sets : Set (Set βS)) = (InternalMeasure.weighted s w).sets := by
  ext X
  constructor
  · rintro ⟨B, rfl, hB⟩
    exact ⟨B, rfl, by filter_upwards [hB, h𝔄] with n hn h; rw [h] at hn; exact hn⟩
  · rintro ⟨B, rfl, hB⟩
    exact ⟨B, rfl, by filter_upwards [hB, h𝔄] with n hn h; rw [h]; exact hn⟩

/-- **Section 16.2, example 5.** Every internal finitely additive function $`\mu` on the
algebra $`\mathcal P_I(S)` of internal subsets of a hyperfinite set $`S` is a weighted
counting function: $`\mu = \mu_w` on $`\mathcal P_I(S)` for the internal weighting
$`w(s) = \mu(\{s\})`. -/
theorem InternalMeasure.μ_eq_μ_weighted_singleton (I : InternalMeasure β) (s : ℕ → Finset β)
    (h𝔄 : ∀ᶠ n in hyperfilter ℕ, I.𝔄 n = {B | B ⊆ ↑(s n)}) {X : Set βS} (hX : X ∈ I.sets) :
    I.μ X = (InternalMeasure.weighted s fun n x => I.m n {x}).μ X := by
  obtain ⟨B, rfl, hB⟩ := hX
  rw [μ_internalSet, μ_internalSet]
  refine Germ.coe_eq.2 ?_
  filter_upwards [hB, h𝔄] with n hn h𝔄n
  exact I.m_eq_sum_singleton s n h𝔄n (by rw [h𝔄n] at hn; exact hn)

/-- **Section 16.2, example 5.** For an internal weighting $`w = [w_n]` with nonnegative real
values, the weighted counting function is the hyperfinite sum of Section 12.7:
$`\mu_w(A) = \sum_{s \in A} w(s)` for every internal subset $`A` of $`S`, the sum being
{name}`Goldblatt.internalSum` of the internal function $`[w_n]` over $`A`. -/
theorem InternalMeasure.μ_weighted_eq_internalSum (s : ℕ → Finset β) (w : ℕ → β → ℝ)
    (hw : ∀ n x, 0 ≤ w n x) {X : Set βS}
    (hX : X ∈ (InternalMeasure.weighted s fun n x => ENNReal.ofReal (w n x)).sets) :
    (InternalMeasure.weighted s fun n x => ENNReal.ofReal (w n x)).μ X =
      hyperENNRealOfHyperreal (internalSum β ((internalMap w : βS → ℝ*) : βS →. ℝ*) X) := by
  obtain ⟨B, rfl, hB⟩ := hX
  rw [μ_internalSet, internalSum_internalMap]
  change _ = Germ.ofFun fun n => ENNReal.ofReal (∑ᶠ x ∈ B n, w n x)
  refine Germ.coe_eq.2 ?_
  filter_upwards [hB] with n hn
  change ∑ x ∈ s n, (B n).indicator (fun x => ENNReal.ofReal (w n x)) x = _
  have h1 : ∑ᶠ x ∈ B n, w n x = ∑ x ∈ s n, (B n).indicator (w n) x := by
    rw [finsum_mem_def]
    exact finsum_eq_sum_of_support_subset _
      (fun x hx => hn (Set.indicator_apply_ne_zero.1 hx).1)
  rw [h1, ENNReal.ofReal_sum_of_nonneg (fun x _ => Set.indicator_nonneg (fun x _ => hw n x) x)]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ B n <;> simp [hx]

/-- **Section 16.2, example 3.** The normalised counting measure on the internal subsets of a
hyperfinite set $`S = [S_n]`: the weighted counting function with the uniform weight
$`1/|S|`. That its value at $`A` is $`|A|/|S|`, with the internal cardinalities of Chapter 12,
is {lit}`Goldblatt.InternalMeasure.μ_counting_eq_internalCard`. -/
noncomputable def InternalMeasure.counting (s : ℕ → Finset β) : InternalMeasure β :=
  InternalMeasure.weighted s fun n _ => ((s n).card : ℝ≥0∞)⁻¹

/-- **Section 16.2, example 3.** For a nonempty hyperfinite set $`S` and an internal subset
$`A` of $`S`, the normalised counting measure is $`\mu(A) = |A|/|S|`, the quotient of the
internal cardinalities ({name}`Goldblatt.internalCard`; for sets of hyperreals this is
{name}`Goldblatt.hcard`). -/
theorem InternalMeasure.μ_counting_eq_internalCard {s : ℕ → Finset β}
    (hs : ∀ᶠ n in hyperfilter ℕ, (s n).Nonempty) {X : Set βS}
    (hX : X ∈ (InternalMeasure.counting s).sets) :
    (InternalMeasure.counting s).μ X = hyperENNRealOfHyperreal
      (internalCard β X / internalCard β (internalSet (fun n => (s n : Set β)) : Set βS)) := by
  obtain ⟨B, rfl, hB⟩ := hX
  rw [μ_internalSet, internalCard_internalSet, internalCard_internalSet_finset]
  change _ = Germ.ofFun fun n => ENNReal.ofReal (((B n).ncard : ℝ) / ((s n).card : ℝ))
  refine Germ.coe_eq.2 ?_
  filter_upwards [hB, hs] with n hn hpos
  have hpos' : (0 : ℝ) < (s n).card := by exact_mod_cast hpos.card_pos
  change ∑ x ∈ s n, (B n).indicator (fun _ => ((s n).card : ℝ≥0∞)⁻¹) x = _
  rw [sum_indicator_const, inter_eq_right.2 hn, ENNReal.ofReal_div_of_pos hpos',
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, div_eq_mul_inv]

/-- **Section 16.2, example 3.** For the normalised counting measure on a nonempty hyperfinite
set $`S`, $`\mu_L(S) = 1`. -/
theorem InternalMeasure.μL_counting_univ {s : ℕ → Finset β}
    (hs : ∀ᶠ n in hyperfilter ℕ, (s n).Nonempty) :
    (InternalMeasure.counting s).μL (internalSet (fun n => (s n : Set β)) : Set βS) = 1 := by
  refine tendsto_nhds_unique ((InternalMeasure.counting s).tendsto_μL _)
    (tendsto_const_nhds.congr' ?_)
  filter_upwards [hs] with n hn
  change (1 : ℝ≥0∞) = ∑ x ∈ s n, (s n : Set β).indicator (fun _ => ((s n).card : ℝ≥0∞)⁻¹) x
  rw [sum_indicator_const, inter_self, Set.ncard_coe_finset,
    ENNReal.mul_inv_cancel (by exact_mod_cast hn.card_ne_zero) (ENNReal.natCast_ne_top _)]

/-- **Section 16.2, example 3.** The normalised counting measure takes values between $`0` and
$`1`: $`\mu_L(A) \le 1` for every internal subset $`A` of $`S`. -/
theorem InternalMeasure.μL_counting_le_one {s : ℕ → Finset β} (B : ℕ → Set β) :
    (InternalMeasure.counting s).μL (internalSet B : Set βS) ≤ 1 := by
  refine le_of_tendsto ((InternalMeasure.counting s).tendsto_μL B) (Eventually.of_forall fun n => ?_)
  change ∑ x ∈ s n, (B n).indicator (fun _ => ((s n).card : ℝ≥0∞)⁻¹) x ≤ 1
  rw [sum_indicator_const]
  rcases (s n).eq_empty_or_nonempty with h | h
  · simp [h]
  · calc ((↑(s n) ∩ B n : Set β).ncard : ℝ≥0∞) * ((s n).card : ℝ≥0∞)⁻¹
        ≤ ((s n).card : ℝ≥0∞) * ((s n).card : ℝ≥0∞)⁻¹ := by
          gcongr
          rw [← Set.ncard_coe_finset (s n)]
          exact Set.ncard_le_ncard inter_subset_left (s n).finite_toSet
      _ = 1 := ENNReal.mul_inv_cancel (by exact_mod_cast h.card_ne_zero)
          (ENNReal.natCast_ne_top _)

end Weighted

/-!
## The algebra of internal subsets of a hyperfinite set is not a sigma-algebra

Example 5 of Section 16.1: the internal subsets of $`S = \{1, \dots, N\}`, for an unlimited
hypernatural $`N`, form an algebra of subsets of $`S` that is not closed under countable
unions, because it contains every singleton $`\{n\}` of a standard positive integer but not
their union, the external set of standard positive integers.
-/

/-- **Section 16.1, example 5.** For any set $`S` of hyperreals, internal or not, the
collection $`\mathcal P_I(S)` of internal subsets of $`S` is a ring of sets. (The book's
$`S` is $`\{1, \dots, N\}`; that this $`S` is itself a member is
{lit}`Goldblatt.setOf_hyperNat_one_le_le_mem_internal_subsets`.) -/
theorem isRingOfSets_internal_subsets (S : Set ℝ*) :
    IsRingOfSets {X : Set ℝ* | IsInternal X ∧ X ⊆ S} :=
  ⟨⟨∅, isInternal_empty, empty_subset _⟩,
    fun _ _ hA hB => ⟨hA.1.diff hB.1, sdiff_subset.trans hA.2⟩,
    fun _ _ hA hB => ⟨hA.1.union hB.1, union_subset hA.2 hB.2⟩⟩

/-- **Section 16.1, example 5.** For a hypernatural $`N`, the set $`S = \{1, \dots, N\}` is
internal (it is hyperfinite, Section 12.3), so it is the largest member of
$`\mathcal P_I(S)`: the ring of internal subsets of $`S` is an algebra of subsets of
$`S`. -/
theorem setOf_hyperNat_one_le_le_mem_internal_subsets {N : ℝ*} (hN : N ∈ ℕ*) :
    {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ N} ∈
      {X : Set ℝ* | IsInternal X ∧ X ⊆ {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ N}} :=
  ⟨(isHyperfinite_setOf_hyperNat_one_le_le hN).isInternalSet, Subset.rfl⟩

/-- **Section 16.1, example 5.** For an unlimited hypernatural $`N`, the algebra of internal
subsets of $`S = \{1, \dots, N\}` is not a sigma-ring: the union of the singletons of the
standard positive integers is countably infinite, so it is not internal. -/
theorem not_isSigmaRing_internal_subsets {N : ℝ*} (hN : N ∈ ℕ*) (hU : Unlimited N) :
    ¬ IsSigmaRing {X : Set ℝ* | IsInternal X ∧ X ⊆ {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ N}} := by
  intro h
  have hmem := h.iUnion_mem (A := fun n : ℕ => {((n + 1 : ℕ) : ℝ*)}) fun n =>
    ⟨isInternal_singleton _, singleton_subset_iff.2
      (natCast_mem_setOf_hyperNat_one_le_le hN hU (Nat.succ_le_succ (Nat.zero_le n)))⟩
  have hc : (⋃ n : ℕ, ({((n + 1 : ℕ) : ℝ*)} : Set ℝ*)).Countable :=
    countable_iUnion fun _ => countable_singleton _
  have hfin := IsInternalSet.finite_of_countable hmem.1 hc
  have hinf : (⋃ n : ℕ, ({((n + 1 : ℕ) : ℝ*)} : Set ℝ*)).Infinite := by
    have : ⋃ n : ℕ, ({((n + 1 : ℕ) : ℝ*)} : Set ℝ*) = range fun n : ℕ => ((n + 1 : ℕ) : ℝ*) := by
      ext x; simp [eq_comm]
    rw [this]
    exact infinite_range_of_injective fun m n hmn => by
      have : (m + 1 : ℕ) = n + 1 := Nat.cast_injective hmn
      omega
  exact hinf hfin

end Goldblatt
