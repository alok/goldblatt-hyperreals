import Mathlib
import Goldblatt.Ch02_LargeSets
import Goldblatt.Ch03_Ultrapower

/-!
# 5 (part 1). Sizes of Hyperreals and Their Arithmetic: Sections 5.1 to 5.3

This is the first of three parts of Chapter 5 (the overview is on the chapter page
{lit}`Goldblatt.Ch05_GreatAndSmall`). It classifies hyperreal numbers by size, as limited,
unlimited, infinitesimal or appreciable, proves every rule of the arithmetic of these classes,
and shows that the limited numbers form a ring in which the infinitesimals are an ideal.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## Hyperrationals as quotients of hyperintegers

The chapter opens with a remark on the enlarged number systems of Chapter 3: a hyperreal is
hyperrational exactly when it is a quotient of two hyperintegers. The book obtains this by
transfer of the corresponding statement about the rationals; here it is proved from
representing sequences, which is what that transfer amounts to in the ultrapower.
-/

section Preliminaries

/-- The inclusion of the reals in the hyperreals agrees with the canonical map from the
natural numbers. -/
@[simp, norm_cast]
theorem ofReal_natCast (n : ℕ) : ((n : ℝ) : ℝ*) = n := rfl

/-- The inclusion of the reals in the hyperreals agrees with the canonical map from the
integers. -/
@[simp, norm_cast]
theorem ofReal_intCast (n : ℤ) : ((n : ℝ) : ℝ*) = n := rfl

/-- **Chapter 5, opening remark.** The hyperrationals are precisely the quotients
$`m/n` of hyperintegers $`m, n` with $`n \ne 0`. -/
theorem mem_hyperRat_iff_exists_div {x : ℝ*} :
    x ∈ ℚ* ↔ ∃ m ∈ ℤ*, ∃ n ∈ ℤ*, n ≠ 0 ∧ x = m / n := by
  constructor
  · intro hx
    obtain ⟨q, rfl⟩ := mem_hyperRat_iff.1 hx
    refine ⟨Hyperreal.ofSeq fun n => (((q n).num : ℤ) : ℝ),
      mem_hyperInt_iff.2 ⟨fun n => (q n).num, rfl⟩,
      Hyperreal.ofSeq fun n => ((((q n).den : ℕ) : ℤ) : ℝ),
      mem_hyperInt_iff.2 ⟨fun n => (q n).den, rfl⟩, ?_, ?_⟩
    · change Hyperreal.ofSeq _ ≠ Hyperreal.ofSeq fun _ => 0
      rw [ofSeq_ne_ofSeq_iff]
      exact Eventually.of_forall fun n => by simp
    · change _ = Hyperreal.ofSeq fun n => (((q n).num : ℤ) : ℝ) / ((((q n).den : ℕ) : ℤ) : ℝ)
      rw [ofSeq_eq_ofSeq_iff]
      exact Eventually.of_forall fun n => by simp [Rat.cast_def]
  · rintro ⟨m, hm, n, hn, -, rfl⟩
    exact hyperRatSubfield.div_mem (hyperInt_subset_hyperRat hm) (hyperInt_subset_hyperRat hn)

/-- Hypernatural numbers are nonnegative. -/
theorem hyperNat_nonneg {x : ℝ*} (hx : x ∈ ℕ*) : 0 ≤ x := by
  obtain ⟨k, rfl⟩ := mem_hyperNat_iff.1 hx
  change Hyperreal.ofSeq (fun _ => 0) ≤ _
  rw [ofSeq_le_ofSeq_iff]
  exact Eventually.of_forall fun n => Nat.cast_nonneg _

end Preliminaries

/-!
## 5.1 (Un)limited, Infinitesimal, and Appreciable Numbers

A hyperreal is classified by comparing it with the real numbers. It is _limited_ if it lies
between two reals, _unlimited_ if it lies beyond all of them, _infinitesimal_ if it is zero or
lies between zero and all reals of its own sign, and _appreciable_ if it is limited without
being infinitesimal. The definitions below are the book's, word for word; each is then shown
equivalent to a condition on the absolute value, which is the form used in proofs, and to the
book's reformulation with natural numbers as bounds.

Mathlib measures the size of an element of an ordered field by its Archimedean class
{name}`ArchimedeanClass.mk`. The last results of the section identify the book's four notions
with the conditions that this class be nonnegative, negative, positive, or zero.
-/

section Sizes

variable {b c : ℝ*}

/-- **Section 5.1.** A hyperreal $`b` is _limited_ if $`r < b < s` for some real numbers
$`r, s`. -/
def Limited (b : ℝ*) : Prop := ∃ r s : ℝ, (r : ℝ*) < b ∧ b < s

/-- **Section 5.1.** A hyperreal $`b` is _positive unlimited_ if $`r < b` for every real
$`r`. -/
def PosUnlimited (b : ℝ*) : Prop := ∀ r : ℝ, (r : ℝ*) < b

/-- **Section 5.1.** A hyperreal $`b` is _negative unlimited_ if $`b < r` for every real
$`r`. -/
def NegUnlimited (b : ℝ*) : Prop := ∀ r : ℝ, b < r

/-- **Section 5.1.** A hyperreal is _unlimited_ if it is positive unlimited or negative
unlimited. -/
def Unlimited (b : ℝ*) : Prop := PosUnlimited b ∨ NegUnlimited b

/-- **Section 5.1.** A hyperreal $`b` is _positive infinitesimal_ if $`0 < b < r` for every
positive real $`r`. -/
def PosInfinitesimal (b : ℝ*) : Prop := 0 < b ∧ ∀ r : ℝ, 0 < r → b < r

/-- **Section 5.1.** A hyperreal $`b` is _negative infinitesimal_ if $`r < b < 0` for every
negative real $`r`. -/
def NegInfinitesimal (b : ℝ*) : Prop := b < 0 ∧ ∀ r : ℝ, r < 0 → (r : ℝ*) < b

/-- **Section 5.1.** A hyperreal is _infinitesimal_ if it is positive infinitesimal, negative
infinitesimal, or zero. -/
def Infinitesimal (b : ℝ*) : Prop := PosInfinitesimal b ∨ NegInfinitesimal b ∨ b = 0

/-- **Section 5.1.** A hyperreal is _appreciable_ if it is limited but not infinitesimal. -/
def Appreciable (b : ℝ*) : Prop := Limited b ∧ ¬ Infinitesimal b

/-- **Section 5.1.** $`b` is infinitesimal if and only if $`|b| < r` for every positive real
$`r`. This is the working form of the definition. -/
theorem infinitesimal_iff_abs_lt : Infinitesimal b ↔ ∀ r : ℝ, 0 < r → |b| < r := by
  constructor
  · rintro (⟨h0, h⟩ | ⟨h0, h⟩ | rfl) r hr
    · rw [abs_of_pos h0]
      exact h r hr
    · rw [abs_of_neg h0]
      have := h (-r) (by linarith)
      rw [Hyperreal.coe_neg] at this
      linarith
    · rw [abs_zero]
      exact Hyperreal.coe_pos.2 hr
  · intro h
    rcases lt_trichotomy b 0 with hb | rfl | hb
    · refine Or.inr (Or.inl ⟨hb, fun r hr => ?_⟩)
      have := h (-r) (by linarith)
      rw [abs_of_neg hb, Hyperreal.coe_neg] at this
      linarith
    · exact Or.inr (Or.inr rfl)
    · refine Or.inl ⟨hb, fun r hr => ?_⟩
      have := h r hr
      rwa [abs_of_pos hb] at this

/-- **Section 5.1.** $`b` is limited if and only if $`|b| < r` for some real $`r`. This is
the working form of the definition. -/
theorem limited_iff_abs_lt : Limited b ↔ ∃ r : ℝ, |b| < r := by
  constructor
  · rintro ⟨r, s, hr, hs⟩
    refine ⟨|r| + |s|, abs_lt.2 ⟨?_, ?_⟩⟩
    · have h : ((-(|r| + |s|) : ℝ) : ℝ*) ≤ r :=
        Hyperreal.coe_le_coe.2 (by linarith [neg_abs_le r, abs_nonneg s])
      rw [Hyperreal.coe_neg] at h
      exact h.trans_lt hr
    · have h : (s : ℝ*) ≤ ((|r| + |s| : ℝ) : ℝ*) :=
        Hyperreal.coe_le_coe.2 (by linarith [le_abs_self s, abs_nonneg r])
      exact hs.trans_le h
  · rintro ⟨r, h⟩
    rw [abs_lt] at h
    exact ⟨-r, r, by rw [Hyperreal.coe_neg]; exact h.1, h.2⟩

/-- **Section 5.1.** $`b` is unlimited if and only if $`|b| > r` for every real $`r`. This
is the working form of the definition. -/
theorem unlimited_iff_abs_gt : Unlimited b ↔ ∀ r : ℝ, (r : ℝ*) < |b| := by
  constructor
  · rintro (h | h) r
    · exact (h r).trans_le (le_abs_self b)
    · have := h (-r)
      rw [Hyperreal.coe_neg] at this
      exact (lt_neg_of_lt_neg this).trans_le (neg_le_abs b)
  · intro h
    rcases le_or_gt 0 b with hb | hb
    · exact Or.inl fun r => by simpa [abs_of_nonneg hb] using h r
    · refine Or.inr fun r => ?_
      have := h (-r)
      rw [abs_of_neg hb, Hyperreal.coe_neg] at this
      linarith

/-- **Section 5.1.** A hyperreal is unlimited exactly when it is not limited. -/
theorem not_limited_iff_unlimited : ¬ Limited b ↔ Unlimited b := by
  rw [limited_iff_abs_lt, unlimited_iff_abs_gt]
  constructor
  · intro h r
    have h' : ((r + 1 : ℝ) : ℝ*) ≤ |b| := not_lt.1 fun hlt => h ⟨_, hlt⟩
    exact (Hyperreal.coe_lt_coe.2 (lt_add_one r)).trans_le h'
  · rintro h ⟨r, hr⟩
    exact lt_asymm hr (h r)

/-- **Section 5.1.** A hyperreal is limited exactly when it is not unlimited. -/
theorem not_unlimited_iff_limited : ¬ Unlimited b ↔ Limited b := by
  rw [← not_limited_iff_unlimited, not_not]

/-- **Section 5.1.** Every hyperreal is limited or unlimited. -/
theorem limited_or_unlimited (b : ℝ*) : Limited b ∨ Unlimited b := by
  rw [← not_limited_iff_unlimited]
  exact em _

theorem Unlimited.not_limited (h : Unlimited b) : ¬ Limited b :=
  not_limited_iff_unlimited.2 h

theorem Limited.not_unlimited (h : Limited b) : ¬ Unlimited b :=
  not_unlimited_iff_limited.2 h

/-- **Section 5.1.** Every real number is limited. -/
theorem limited_coe (r : ℝ) : Limited (r : ℝ*) :=
  ⟨r - 1, r + 1, Hyperreal.coe_lt_coe.2 (by linarith), Hyperreal.coe_lt_coe.2 (by linarith)⟩

/-- **Section 5.1.** Every infinitesimal is limited. -/
theorem Infinitesimal.limited (h : Infinitesimal b) : Limited b :=
  limited_iff_abs_lt.2 ⟨1, infinitesimal_iff_abs_lt.1 h 1 one_pos⟩

/-- Zero is infinitesimal. -/
@[simp]
theorem infinitesimal_zero : Infinitesimal 0 := Or.inr (Or.inr rfl)

/-- Zero is limited. -/
@[simp]
theorem limited_zero : Limited 0 := infinitesimal_zero.limited

/-- **Section 5.1.** The only infinitesimal real number is $`0`. -/
@[simp]
theorem infinitesimal_coe_iff {r : ℝ} : Infinitesimal (r : ℝ*) ↔ r = 0 := by
  refine ⟨fun h => by_contra fun hr => ?_, fun h => by rw [h]; exact infinitesimal_zero⟩
  have := infinitesimal_iff_abs_lt.1 h |r| (abs_pos.2 hr)
  rw [Hyperreal.coe_abs] at this
  exact lt_irrefl _ this

/-- **Section 5.1.** Every nonzero real number is appreciable. -/
theorem appreciable_coe {r : ℝ} (hr : r ≠ 0) : Appreciable (r : ℝ*) :=
  ⟨limited_coe r, fun h => hr (infinitesimal_coe_iff.1 h)⟩

/-- A real number is appreciable exactly when it is not zero. -/
@[simp]
theorem appreciable_coe_iff {r : ℝ} : Appreciable (r : ℝ*) ↔ r ≠ 0 :=
  ⟨fun h hr => h.2 (infinitesimal_coe_iff.2 hr), appreciable_coe⟩

/-- Natural numbers are limited. -/
@[simp]
theorem limited_natCast (n : ℕ) : Limited (n : ℝ*) := limited_coe n

/-- Integers are limited. -/
@[simp]
theorem limited_intCast (n : ℤ) : Limited (n : ℝ*) := limited_coe n

/-- One is limited. -/
@[simp]
theorem limited_one : Limited 1 := by
  simpa using limited_coe 1

/-- One is appreciable. -/
@[simp]
theorem appreciable_one : Appreciable 1 := by
  simpa using appreciable_coe (one_ne_zero (α := ℝ))

theorem Appreciable.limited (h : Appreciable b) : Limited b := h.1

theorem Appreciable.not_infinitesimal (h : Appreciable b) : ¬ Infinitesimal b := h.2

theorem Appreciable.ne_zero (h : Appreciable b) : b ≠ 0 := fun h0 =>
  h.2 (h0 ▸ infinitesimal_zero)

theorem Unlimited.not_infinitesimal (h : Unlimited b) : ¬ Infinitesimal b := fun hi =>
  h.not_limited hi.limited

theorem Unlimited.ne_zero (h : Unlimited b) : b ≠ 0 := fun h0 =>
  h.not_infinitesimal (h0 ▸ infinitesimal_zero)

theorem Infinitesimal.not_unlimited (h : Infinitesimal b) : ¬ Unlimited b :=
  h.limited.not_unlimited

/-- **Section 5.1.** An appreciable number is one that is neither infinitely small nor
infinitely big. -/
theorem appreciable_iff_not_infinitesimal_and_not_unlimited :
    Appreciable b ↔ ¬ Infinitesimal b ∧ ¬ Unlimited b := by
  rw [not_unlimited_iff_limited, Appreciable, and_comm]

/-- **Section 5.1.** Every hyperreal is infinitesimal, appreciable or unlimited (and the three
cases exclude one another, by {name}`Appreciable.not_infinitesimal`,
{name}`Unlimited.not_infinitesimal` and {name}`Unlimited.not_limited`). -/
theorem infinitesimal_or_appreciable_or_unlimited (b : ℝ*) :
    Infinitesimal b ∨ Appreciable b ∨ Unlimited b := by
  rcases limited_or_unlimited b with h | h
  · by_cases hi : Infinitesimal b
    · exact Or.inl hi
    · exact Or.inr (Or.inl ⟨h, hi⟩)
  · exact Or.inr (Or.inr h)

/-- **Section 5.1.** $`b` is appreciable if and only if $`r < |b| < s` for some positive
reals $`r, s`. -/
theorem appreciable_iff_abs : Appreciable b ↔ ∃ r s : ℝ, 0 < r ∧ (r : ℝ*) < |b| ∧ |b| < s := by
  constructor
  · rintro ⟨hl, hi⟩
    obtain ⟨s, hs⟩ := limited_iff_abs_lt.1 hl
    rw [infinitesimal_iff_abs_lt] at hi
    push Not at hi
    obtain ⟨r, hr, hrb⟩ := hi
    exact ⟨r / 2, s, half_pos hr,
      (Hyperreal.coe_lt_coe.2 (half_lt_self hr)).trans_le hrb, hs⟩
  · rintro ⟨r, s, hr, hrb, hs⟩
    exact ⟨limited_iff_abs_lt.2 ⟨s, hs⟩,
      fun hi => lt_asymm hrb (infinitesimal_iff_abs_lt.1 hi r hr)⟩

/-- **Section 5.1, natural-number bounds.** $`b` is limited if and only if $`|b| < n` for some
natural number $`n`. -/
theorem limited_iff_exists_nat : Limited b ↔ ∃ n : ℕ, |b| < n := by
  rw [limited_iff_abs_lt]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨n, hn⟩ := exists_nat_gt r
    exact ⟨n, hr.trans (by exact_mod_cast Hyperreal.coe_lt_coe.2 hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hn⟩

/-- **Section 5.1, natural-number bounds.** $`b` is unlimited if and only if $`|b| > n` for
every natural number $`n`. -/
theorem unlimited_iff_forall_nat : Unlimited b ↔ ∀ n : ℕ, (n : ℝ*) < |b| := by
  rw [unlimited_iff_abs_gt]
  constructor
  · intro h n
    exact h n
  · intro h r
    obtain ⟨n, hn⟩ := exists_nat_gt r
    exact lt_trans (by exact_mod_cast Hyperreal.coe_lt_coe.2 hn) (h n)

/-- **Section 5.1, natural-number bounds.** $`b` is infinitesimal if and only if
$`|b| < 1/n` for every positive natural number $`n`. -/
theorem infinitesimal_iff_forall_nat :
    Infinitesimal b ↔ ∀ n : ℕ, 0 < n → |b| < 1 / (n : ℝ*) := by
  rw [infinitesimal_iff_abs_lt]
  constructor
  · intro h n hn
    have := h (1 / (n : ℝ)) (by positivity)
    rwa [Hyperreal.coe_div, Hyperreal.coe_one, ofReal_natCast] at this
  · intro h r hr
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
    have h1 := h (n + 1) n.succ_pos
    have h2 : ((1 / ((n : ℝ) + 1) : ℝ) : ℝ*) < r := Hyperreal.coe_lt_coe.2 hn
    rw [Hyperreal.coe_div, Hyperreal.coe_one, Hyperreal.coe_add, Hyperreal.coe_one,
      ofReal_natCast] at h2
    push_cast at h1
    exact h1.trans h2

/-- **Section 5.1, natural-number bounds.** $`b` is appreciable if and only if
$`1/n < |b| < n` for some positive natural number $`n`. -/
theorem appreciable_iff_exists_nat :
    Appreciable b ↔ ∃ n : ℕ, 0 < n ∧ 1 / (n : ℝ*) < |b| ∧ |b| < n := by
  rw [appreciable_iff_abs]
  constructor
  · rintro ⟨r, s, hr, hrb, hs⟩
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr
    obtain ⟨k, hk⟩ := exists_nat_gt s
    refine ⟨max (m + 1) k, lt_of_lt_of_le m.succ_pos (le_max_left _ _), ?_, ?_⟩
    · have h1 : (1 / ((max (m + 1) k : ℕ) : ℝ)) < r := by
        refine lt_of_le_of_lt ?_ hm
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast le_max_left (m + 1) k
      have h2 : ((1 / ((max (m + 1) k : ℕ) : ℝ) : ℝ) : ℝ*) < r := Hyperreal.coe_lt_coe.2 h1
      rw [Hyperreal.coe_div, Hyperreal.coe_one, ofReal_natCast] at h2
      exact h2.trans hrb
    · have h1 : s < ((max (m + 1) k : ℕ) : ℝ) :=
        hk.trans_le (by exact_mod_cast le_max_right (m + 1) k)
      have h2 : (s : ℝ*) < (((max (m + 1) k : ℕ) : ℝ) : ℝ*) := Hyperreal.coe_lt_coe.2 h1
      rw [ofReal_natCast] at h2
      exact hs.trans h2
  · rintro ⟨n, hn, h1, h2⟩
    refine ⟨1 / (n : ℝ), n, by positivity, ?_, h2⟩
    rwa [Hyperreal.coe_div, Hyperreal.coe_one, ofReal_natCast]

/-- **Section 5.1.** A positive unlimited number is unlimited and positive, and conversely. -/
theorem posUnlimited_iff : PosUnlimited b ↔ Unlimited b ∧ 0 < b := by
  constructor
  · intro h
    exact ⟨Or.inl h, by simpa using h 0⟩
  · rintro ⟨h, h0⟩ r
    have := unlimited_iff_abs_gt.1 h r
    rwa [abs_of_pos h0] at this

/-- **Section 5.1.** A negative unlimited number is unlimited and negative, and conversely. -/
theorem negUnlimited_iff : NegUnlimited b ↔ Unlimited b ∧ b < 0 := by
  constructor
  · intro h
    exact ⟨Or.inr h, by simpa using h 0⟩
  · rintro ⟨h, h0⟩ r
    have := unlimited_iff_abs_gt.1 h (-r)
    rw [abs_of_neg h0, Hyperreal.coe_neg] at this
    linarith

theorem PosUnlimited.unlimited (h : PosUnlimited b) : Unlimited b := Or.inl h

theorem NegUnlimited.unlimited (h : NegUnlimited b) : Unlimited b := Or.inr h

theorem PosUnlimited.pos (h : PosUnlimited b) : 0 < b := (posUnlimited_iff.1 h).2

theorem NegUnlimited.neg (h : NegUnlimited b) : b < 0 := (negUnlimited_iff.1 h).2

/-- **Section 5.1, non-vacuity.** The hyperreal $`\varepsilon` of Chapter 3 is a nonzero
infinitesimal. -/
theorem infinitesimal_epsilon : Infinitesimal (ε : ℝ*) :=
  Or.inl epsilon_pos_infinitesimal

/-- **Section 5.1, non-vacuity.** There is a nonzero infinitesimal. -/
theorem exists_infinitesimal_ne_zero : ∃ e : ℝ*, Infinitesimal e ∧ e ≠ 0 :=
  ⟨ε, infinitesimal_epsilon, Hyperreal.epsilon_ne_zero⟩

/-- **Section 5.1, non-vacuity.** The hyperreal $`\omega` of Chapter 3 is positive
unlimited. -/
theorem posUnlimited_omega : PosUnlimited (ω : ℝ*) := real_lt_omega

/-- **Section 5.1, non-vacuity.** The hyperreal $`\omega` is unlimited. -/
theorem unlimited_omega : Unlimited (ω : ℝ*) := Or.inl posUnlimited_omega

/-- **Section 5.1, Mathlib's formulation.** A hyperreal is limited exactly when its
Archimedean class is nonnegative. -/
theorem limited_iff_mk_nonneg : Limited b ↔ 0 ≤ ArchimedeanClass.mk b := by
  rw [limited_iff_exists_nat, ← ArchimedeanClass.mk_one, ArchimedeanClass.mk_le_mk]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using hn.le⟩
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, lt_of_le_of_lt (by simpa using hn) ?_⟩
    push_cast
    exact lt_add_one _

/-- **Section 5.1, Mathlib's formulation.** A hyperreal is unlimited exactly when its
Archimedean class is negative. -/
theorem unlimited_iff_mk_neg : Unlimited b ↔ ArchimedeanClass.mk b < 0 := by
  rw [← not_limited_iff_unlimited, limited_iff_mk_nonneg, not_le]

/-- **Section 5.1, Mathlib's formulation.** A hyperreal is infinitesimal exactly when its
Archimedean class is positive. -/
theorem infinitesimal_iff_mk_pos : Infinitesimal b ↔ 0 < ArchimedeanClass.mk b := by
  rw [infinitesimal_iff_forall_nat, ← ArchimedeanClass.mk_one, ArchimedeanClass.mk_lt_mk]
  constructor
  · intro h n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := h n hn
      rw [lt_div_iff₀ (by exact_mod_cast hn)] at this
      simpa [mul_comm] using this
  · intro h n hn
    have := h n
    rw [lt_div_iff₀ (by exact_mod_cast hn)]
    simpa [mul_comm] using this

/-- **Section 5.1, Mathlib's formulation.** A hyperreal is appreciable exactly when its
Archimedean class is zero. -/
theorem appreciable_iff_mk_eq_zero : Appreciable b ↔ ArchimedeanClass.mk b = 0 := by
  rw [Appreciable, limited_iff_mk_nonneg, infinitesimal_iff_mk_pos, not_lt]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/-- **Section 5.1.** The set $`\mathbb L` of limited hyperreals. -/
def limitedSet : Set ℝ* := {b | Limited b}

/-- **Section 5.1.** The set $`\mathbb I` of infinitesimal hyperreals. -/
def infinitesimalSet : Set ℝ* := {b | Infinitesimal b}

@[inherit_doc] scoped notation "𝕃" => limitedSet
@[inherit_doc] scoped notation "𝕀" => infinitesimalSet

@[simp] theorem mem_limitedSet : b ∈ 𝕃 ↔ Limited b := Iff.rfl

@[simp] theorem mem_infinitesimalSet : b ∈ 𝕀 ↔ Infinitesimal b := Iff.rfl

/-- **Section 5.1.** For a set $`X` of hyperreals, $`X_\infty` is the set of its unlimited
members. -/
def unlimitedPart (X : Set ℝ*) : Set ℝ* := {x ∈ X | Unlimited x}

/-- **Section 5.1.** For a set $`X` of hyperreals, $`X^+` is the set of its positive
members. -/
def positivePart (X : Set ℝ*) : Set ℝ* := {x ∈ X | 0 < x}

/-- **Section 5.1.** For a set $`X` of hyperreals, $`X^-` is the set of its negative
members. -/
def negativePart (X : Set ℝ*) : Set ℝ* := {x ∈ X | x < 0}

/-- **Section 5.1.** The set of positive unlimited hyperreals is obtained from the set of all
hyperreals by taking the positive part of the unlimited part. -/
theorem positivePart_unlimitedPart_univ :
    positivePart (unlimitedPart univ) = {b : ℝ* | PosUnlimited b} := by
  ext b
  simp [positivePart, unlimitedPart, posUnlimited_iff]

/-- **Section 5.1.** The set of negative unlimited hyperreals is obtained from the set of all
hyperreals by taking the negative part of the unlimited part. -/
theorem negativePart_unlimitedPart_univ :
    negativePart (unlimitedPart univ) = {b : ℝ* | NegUnlimited b} := by
  ext b
  simp [negativePart, unlimitedPart, negUnlimited_iff]

end Sizes

/-!
## 5.2 Arithmetic of Hyperreals

The book tabulates how the four size classes behave under the field operations and roots.
Every row of the table is a lemma below, in the book's order: sums, opposites, products,
reciprocals, quotients, roots. Throughout, following the book, $`\varepsilon, \delta` stand
for infinitesimals, $`b, c` for appreciable numbers and $`H, K` for unlimited ones. Where a
rule holds under a weaker hypothesis (for instance a limited factor in place of an appreciable
one) the lemma is stated in that generality.

The last row of the table lists the _indeterminate forms_: combinations whose size is not
determined by the sizes of the parts. For each of them we exhibit instances that are
infinitesimal, appreciable and unlimited.

The rules show that the limited numbers form a subring of the hyperreals and that the
infinitesimals form an ideal in it. The section closes with the hyperreal exponential
$`a^x` of Exercise 5.2.1 and with roots of hypernatural order.
-/

section Arithmetic

variable {b c e d H K : ℝ*}

/-! ### Sums -/

/-- **Section 5.2, sums.** If $`\varepsilon` and $`\delta` are infinitesimal then so is
$`\varepsilon + \delta`. -/
theorem Infinitesimal.add (he : Infinitesimal e) (hd : Infinitesimal d) :
    Infinitesimal (e + d) := by
  rw [infinitesimal_iff_abs_lt] at *
  intro r hr
  calc |e + d| ≤ |e| + |d| := abs_add_le _ _
    _ < ((r / 2 : ℝ) : ℝ*) + ((r / 2 : ℝ) : ℝ*) :=
        add_lt_add (he _ (half_pos hr)) (hd _ (half_pos hr))
    _ = r := by rw [← Hyperreal.coe_add, add_halves]

/-- **Section 5.2, sums.** The sum of two limited numbers is limited. In particular the sum
$`b + c` of two appreciable numbers is limited; it may be infinitesimal, see
{lit}`exists_appreciable_add_infinitesimal`. -/
theorem Limited.add (hb : Limited b) (hc : Limited c) : Limited (b + c) := by
  rw [limited_iff_abs_lt] at *
  obtain ⟨r, hr⟩ := hb
  obtain ⟨s, hs⟩ := hc
  exact ⟨r + s, (abs_add_le _ _).trans_lt (by rw [Hyperreal.coe_add]; exact add_lt_add hr hs)⟩

/-- **Section 5.2, sums.** If $`b` and $`c` are appreciable then $`b + c` is limited. -/
theorem Appreciable.add_limited (hb : Appreciable b) (hc : Appreciable c) : Limited (b + c) :=
  hb.limited.add hc.limited

/-- **Section 5.2, opposites.** If $`\varepsilon` is infinitesimal then so is
$`-\varepsilon`. -/
theorem Infinitesimal.neg (he : Infinitesimal e) : Infinitesimal (-e) := by
  rw [infinitesimal_iff_abs_lt] at *
  simpa using he

/-- The negative of a limited number is limited. -/
theorem Limited.neg (hb : Limited b) : Limited (-b) := by
  rw [limited_iff_abs_lt] at *
  simpa using hb

@[simp] theorem infinitesimal_neg_iff : Infinitesimal (-e) ↔ Infinitesimal e :=
  ⟨fun h => by simpa using h.neg, Infinitesimal.neg⟩

@[simp] theorem limited_neg_iff : Limited (-b) ↔ Limited b :=
  ⟨fun h => by simpa using h.neg, Limited.neg⟩

@[simp] theorem unlimited_neg_iff : Unlimited (-H) ↔ Unlimited H := by
  rw [← not_limited_iff_unlimited, ← not_limited_iff_unlimited, limited_neg_iff]

@[simp] theorem appreciable_neg_iff : Appreciable (-b) ↔ Appreciable b := by
  rw [Appreciable, Appreciable, limited_neg_iff, infinitesimal_neg_iff]

/-- The difference of two infinitesimals is infinitesimal. -/
theorem Infinitesimal.sub (he : Infinitesimal e) (hd : Infinitesimal d) :
    Infinitesimal (e - d) := by
  rw [sub_eq_add_neg]
  exact he.add hd.neg

/-- The difference of two limited numbers is limited. -/
theorem Limited.sub (hb : Limited b) (hc : Limited c) : Limited (b - c) := by
  rw [sub_eq_add_neg]
  exact hb.add hc.neg

/-- **Section 5.2, sums.** If $`b` is appreciable and $`\varepsilon` infinitesimal then
$`b + \varepsilon` is appreciable. -/
theorem Appreciable.add_infinitesimal (hb : Appreciable b) (he : Infinitesimal e) :
    Appreciable (b + e) :=
  ⟨hb.limited.add he.limited, fun h => hb.2 (by simpa using h.sub he)⟩

/-- **Section 5.2, sums.** If $`H` is unlimited and $`b` is limited then $`H + b` is
unlimited. This covers both $`H + \varepsilon` and $`H + b` of the book's table. -/
theorem Unlimited.add_limited (hH : Unlimited H) (hb : Limited b) : Unlimited (H + b) :=
  not_limited_iff_unlimited.1 fun h => hH.not_limited (by simpa using h.sub hb)

/-- **Section 5.2, sums.** If $`H` is unlimited and $`\varepsilon` infinitesimal then
$`H + \varepsilon` is unlimited. -/
theorem Unlimited.add_infinitesimal (hH : Unlimited H) (he : Infinitesimal e) :
    Unlimited (H + e) :=
  hH.add_limited he.limited

/-- **Section 5.2, sums.** If $`H` is unlimited and $`b` appreciable then $`H + b` is
unlimited. -/
theorem Unlimited.add_appreciable (hH : Unlimited H) (hb : Appreciable b) :
    Unlimited (H + b) :=
  hH.add_limited hb.limited

/-- **Section 5.2, sums.** The sum of two appreciable numbers can be infinitesimal:
$`1 + (-1) = 0`. So "limited" cannot be improved to "appreciable" in
{name}`Appreciable.add_limited`. -/
theorem exists_appreciable_add_infinitesimal :
    ∃ b c : ℝ*, Appreciable b ∧ Appreciable c ∧ Infinitesimal (b + c) :=
  ⟨1, -1, appreciable_one, appreciable_neg_iff.2 appreciable_one, by simp⟩

/-! ### Opposites -/

/-- **Section 5.2, opposites.** If $`b` is appreciable then so is $`-b`. -/
theorem Appreciable.neg (hb : Appreciable b) : Appreciable (-b) := appreciable_neg_iff.2 hb

/-- **Section 5.2, opposites.** If $`H` is unlimited then so is $`-H`. -/
theorem Unlimited.neg (hH : Unlimited H) : Unlimited (-H) := unlimited_neg_iff.2 hH

/-! ### Products -/

/-- The product of two limited numbers is limited. -/
theorem Limited.mul (hb : Limited b) (hc : Limited c) : Limited (b * c) := by
  rw [limited_iff_abs_lt] at *
  obtain ⟨r, hr⟩ := hb
  obtain ⟨s, hs⟩ := hc
  refine ⟨r * s, ?_⟩
  rw [abs_mul, Hyperreal.coe_mul]
  exact mul_lt_mul'' hr hs (abs_nonneg _) (abs_nonneg _)

/-- **Section 5.2, products.** If $`\varepsilon` is infinitesimal and $`b` is limited then
$`\varepsilon \cdot b` is infinitesimal. This covers $`\varepsilon \cdot b` for appreciable
$`b` in the book's table. -/
theorem Infinitesimal.mul_limited (he : Infinitesimal e) (hb : Limited b) :
    Infinitesimal (e * b) := by
  rw [infinitesimal_iff_abs_lt] at *
  obtain ⟨s, hs⟩ := limited_iff_abs_lt.1 hb
  have hs0 : 0 < s := Hyperreal.coe_pos.1 ((abs_nonneg b).trans_lt hs)
  intro r hr
  have h1 := he (r / s) (div_pos hr hs0)
  rw [abs_mul]
  calc |e| * |b| ≤ |e| * s := mul_le_mul_of_nonneg_left hs.le (abs_nonneg _)
    _ < ((r / s : ℝ) : ℝ*) * s := mul_lt_mul_of_pos_right h1 (Hyperreal.coe_pos.2 hs0)
    _ = r := by rw [← Hyperreal.coe_mul, div_mul_cancel₀ r hs0.ne']

/-- A limited number times an infinitesimal is infinitesimal. -/
theorem Limited.mul_infinitesimal (hb : Limited b) (he : Infinitesimal e) :
    Infinitesimal (b * e) := by
  rw [mul_comm]
  exact he.mul_limited hb

/-- **Section 5.2, products.** If $`\varepsilon` and $`\delta` are infinitesimal then so is
$`\varepsilon \cdot \delta`. -/
theorem Infinitesimal.mul (he : Infinitesimal e) (hd : Infinitesimal d) :
    Infinitesimal (e * d) :=
  he.mul_limited hd.limited

/-- **Section 5.2, products.** If $`\varepsilon` is infinitesimal and $`b` appreciable then
$`\varepsilon \cdot b` is infinitesimal. -/
theorem Infinitesimal.mul_appreciable (he : Infinitesimal e) (hb : Appreciable b) :
    Infinitesimal (e * b) :=
  he.mul_limited hb.limited

/-! ### Reciprocals -/

/-- **Section 5.2, reciprocals.** If $`\varepsilon \ne 0` is infinitesimal then
$`1/\varepsilon` is unlimited. The proof is Exercise 3.8.1. -/
theorem Infinitesimal.inv_unlimited (he : Infinitesimal e) (h0 : e ≠ 0) : Unlimited e⁻¹ := by
  rw [unlimited_iff_abs_gt, abs_inv]
  exact lt_inv_of_pos_infinitesimal (Hyperreal.coeRingHom : ℝ →+* ℝ*)
    (fun _ _ h => Hyperreal.coe_lt_coe.2 h) (abs_pos.2 h0) (infinitesimal_iff_abs_lt.1 he)

/-- **Section 5.2, reciprocals.** If $`H` is unlimited then $`1/H` is infinitesimal. -/
theorem Unlimited.inv_infinitesimal (hH : Unlimited H) : Infinitesimal H⁻¹ := by
  rw [infinitesimal_iff_abs_lt, abs_inv]
  intro r hr
  have h := unlimited_iff_abs_gt.1 hH r⁻¹
  rw [Hyperreal.coe_inv] at h
  exact (inv_lt_comm₀ (abs_pos.2 hH.ne_zero) (Hyperreal.coe_pos.2 hr)).2 h

/-- **Section 5.2, reciprocals.** If $`b` is appreciable then so is $`1/b`. -/
theorem Appreciable.inv (hb : Appreciable b) : Appreciable b⁻¹ := by
  rw [appreciable_iff_abs] at *
  obtain ⟨r, s, hr, hrb, hs⟩ := hb
  have hr' : (0 : ℝ*) < r := Hyperreal.coe_pos.2 hr
  have hb0 : 0 < |b| := hr'.trans hrb
  have hs0 : 0 < s := Hyperreal.coe_pos.1 (hb0.trans hs)
  refine ⟨s⁻¹, r⁻¹, inv_pos.2 hs0, ?_, ?_⟩
  · rw [abs_inv, Hyperreal.coe_inv]
    exact (inv_lt_inv₀ (Hyperreal.coe_pos.2 hs0) hb0).2 hs
  · rw [abs_inv, Hyperreal.coe_inv]
    exact (inv_lt_inv₀ hb0 hr').2 hrb

/-- A nonzero hyperreal is unlimited exactly when its reciprocal is infinitesimal. -/
theorem unlimited_iff_inv_infinitesimal (h0 : H ≠ 0) : Unlimited H ↔ Infinitesimal H⁻¹ :=
  ⟨Unlimited.inv_infinitesimal, fun h => by
    simpa using h.inv_unlimited (inv_ne_zero h0)⟩

@[simp] theorem appreciable_inv_iff : Appreciable b⁻¹ ↔ Appreciable b :=
  ⟨fun h => by simpa using h.inv, Appreciable.inv⟩

/-! ### Products, continued -/

/-- **Section 5.2, products.** If $`b` and $`c` are appreciable then so is $`b \cdot c`. -/
theorem Appreciable.mul (hb : Appreciable b) (hc : Appreciable c) : Appreciable (b * c) :=
  ⟨hb.limited.mul hc.limited, fun h => hb.2 (by
    simpa [mul_assoc, hc.ne_zero] using h.mul_limited hc.inv.limited)⟩

/-- **Section 5.2, products.** If $`b` is appreciable and $`H` unlimited then $`b \cdot H` is
unlimited. -/
theorem Appreciable.mul_unlimited (hb : Appreciable b) (hH : Unlimited H) :
    Unlimited (b * H) :=
  not_limited_iff_unlimited.1 fun h => hH.not_limited (by
    simpa [← mul_assoc, hb.ne_zero] using hb.inv.limited.mul h)

/-- An unlimited number times an appreciable one is unlimited. -/
theorem Unlimited.mul_appreciable (hH : Unlimited H) (hb : Appreciable b) :
    Unlimited (H * b) := by
  rw [mul_comm]
  exact hb.mul_unlimited hH

/-- **Section 5.2, products.** If $`H` and $`K` are unlimited then so is $`H \cdot K`. -/
theorem Unlimited.mul (hH : Unlimited H) (hK : Unlimited K) : Unlimited (H * K) := by
  rw [unlimited_iff_abs_gt] at *
  intro r
  have h1 : (1 : ℝ*) < |H| := by simpa using hH 1
  calc (r : ℝ*) < |K| := hK r
    _ ≤ |H| * |K| := le_mul_of_one_le_left (abs_nonneg _) h1.le
    _ = |H * K| := (abs_mul _ _).symm

/-! ### Quotients -/

/-- **Section 5.2, quotients.** If $`\varepsilon` is infinitesimal and $`b` appreciable then
$`\varepsilon / b` is infinitesimal. -/
theorem Infinitesimal.div_appreciable (he : Infinitesimal e) (hb : Appreciable b) :
    Infinitesimal (e / b) := by
  rw [div_eq_mul_inv]
  exact he.mul_appreciable hb.inv

/-- **Section 5.2, quotients.** If $`b` is limited and $`H` unlimited then $`b / H` is
infinitesimal. This covers both $`\varepsilon / H` and $`b / H` of the book's table. -/
theorem Limited.div_unlimited (hb : Limited b) (hH : Unlimited H) : Infinitesimal (b / H) := by
  rw [div_eq_mul_inv]
  exact hb.mul_infinitesimal hH.inv_infinitesimal

/-- **Section 5.2, quotients.** If $`\varepsilon` is infinitesimal and $`H` unlimited then
$`\varepsilon / H` is infinitesimal. -/
theorem Infinitesimal.div_unlimited (he : Infinitesimal e) (hH : Unlimited H) :
    Infinitesimal (e / H) :=
  he.limited.div_unlimited hH

/-- **Section 5.2, quotients.** If $`b` is appreciable and $`H` unlimited then $`b / H` is
infinitesimal. -/
theorem Appreciable.div_unlimited (hb : Appreciable b) (hH : Unlimited H) :
    Infinitesimal (b / H) :=
  hb.limited.div_unlimited hH

/-- **Section 5.2, quotients.** If $`b` and $`c` are appreciable then so is $`b / c`. -/
theorem Appreciable.div (hb : Appreciable b) (hc : Appreciable c) : Appreciable (b / c) := by
  rw [div_eq_mul_inv]
  exact hb.mul hc.inv

/-- **Section 5.2, quotients.** If $`b` is appreciable and $`\varepsilon \ne 0` infinitesimal
then $`b / \varepsilon` is unlimited. -/
theorem Appreciable.div_infinitesimal (hb : Appreciable b) (he : Infinitesimal e)
    (h0 : e ≠ 0) : Unlimited (b / e) := by
  rw [div_eq_mul_inv]
  exact hb.mul_unlimited (he.inv_unlimited h0)

/-- **Section 5.2, quotients.** If $`H` is unlimited and $`\varepsilon \ne 0` infinitesimal
then $`H / \varepsilon` is unlimited. -/
theorem Unlimited.div_infinitesimal (hH : Unlimited H) (he : Infinitesimal e) (h0 : e ≠ 0) :
    Unlimited (H / e) := by
  rw [div_eq_mul_inv]
  exact hH.mul (he.inv_unlimited h0)

/-- **Section 5.2, quotients.** If $`H` is unlimited and $`b` appreciable then $`H / b` is
unlimited. -/
theorem Unlimited.div_appreciable (hH : Unlimited H) (hb : Appreciable b) :
    Unlimited (H / b) := by
  rw [div_eq_mul_inv]
  exact hH.mul_appreciable hb.inv

/-- A limited number divided by an appreciable one is limited. -/
theorem Limited.div_appreciable (hb : Limited b) (hc : Appreciable c) : Limited (b / c) := by
  rw [div_eq_mul_inv]
  exact hb.mul hc.inv.limited

/-! ### Powers and roots -/

/-- A positive power of an infinitesimal is infinitesimal. -/
theorem Infinitesimal.pow (he : Infinitesimal e) {n : ℕ} (hn : n ≠ 0) :
    Infinitesimal (e ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  clear hn
  induction m with
  | zero => simpa using he
  | succ m ih =>
    rw [pow_succ]
    exact ih.mul he

/-- A power of a limited number is limited. -/
theorem Limited.pow (hb : Limited b) (n : ℕ) : Limited (b ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hb

/-- A power of an appreciable number is appreciable. -/
theorem Appreciable.pow (hb : Appreciable b) (n : ℕ) : Appreciable (b ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hb

/-- A positive power of an unlimited number is unlimited. -/
theorem Unlimited.pow (hH : Unlimited H) {n : ℕ} (hn : n ≠ 0) : Unlimited (H ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  clear hn
  induction m with
  | zero => simpa using hH
  | succ m ih =>
    rw [pow_succ]
    exact ih.mul hH

/-- **Section 5.2, roots, algebraic form.** If a positive power $`y^n` is infinitesimal then
$`y` is infinitesimal. -/
theorem infinitesimal_of_pow {y : ℝ*} {n : ℕ} (h : Infinitesimal (y ^ n)) (hn : n ≠ 0) :
    Infinitesimal y := by
  rcases infinitesimal_or_appreciable_or_unlimited y with hy | hy | hy
  · exact hy
  · exact absurd h (hy.pow n).2
  · exact absurd h (hy.pow hn).not_infinitesimal

/-- **Section 5.2, roots, algebraic form.** If a positive power $`y^n` is appreciable then
$`y` is appreciable. -/
theorem appreciable_of_pow {y : ℝ*} {n : ℕ} (h : Appreciable (y ^ n)) (hn : n ≠ 0) :
    Appreciable y := by
  rcases infinitesimal_or_appreciable_or_unlimited y with hy | hy | hy
  · exact absurd (hy.pow hn) h.2
  · exact hy
  · exact absurd h.1 (hy.pow hn).not_limited

/-- **Section 5.2, roots, algebraic form.** If a power $`y^n` is unlimited then $`y` is
unlimited. -/
theorem unlimited_of_pow {y : ℝ*} {n : ℕ} (h : Unlimited (y ^ n)) : Unlimited y :=
  not_limited_iff_unlimited.1 fun hy => h.not_limited (hy.pow n)

/-- **Section 5.2, roots.** The $`n`-th root function on the hyperreals: the extension of the
real function $`x \mapsto \sqrt[n]{x}`. It is meaningful for $`x \ge 0` and $`n \ge 1`. -/
def hroot (n : ℕ) : ℝ* → ℝ* := ⋆(fun x : ℝ => x ^ ((n : ℝ)⁻¹))

/-- The $`n`-th root of the class of a sequence is the class of the sequence of $`n`-th
roots. -/
theorem hroot_ofSeq (n : ℕ) (r : ℕ → ℝ) :
    hroot n (Hyperreal.ofSeq r) = Hyperreal.ofSeq fun k => r k ^ ((n : ℝ)⁻¹) := rfl

/-- On real numbers the hyperreal $`n`-th root is the real one. -/
theorem hroot_coe (n : ℕ) (r : ℝ) : hroot n (r : ℝ*) = ((r ^ ((n : ℝ)⁻¹) : ℝ) : ℝ*) := rfl

/-- **Section 5.2, roots.** The $`n`-th root of a nonnegative hyperreal is nonnegative. -/
theorem hroot_nonneg (n : ℕ) {x : ℝ*} (hx : 0 ≤ x) : 0 ≤ hroot n x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  have hx' : ∀ᶠ k in hyperfilter ℕ, 0 ≤ r k := ofSeq_le_ofSeq_iff.1 hx
  rw [hroot_ofSeq]
  change Hyperreal.ofSeq (fun _ => 0) ≤ _
  rw [ofSeq_le_ofSeq_iff]
  exact hx'.mono fun k hk => Real.rpow_nonneg hk _

/-- **Section 5.2, roots.** The $`n`-th root really is one: $`(\sqrt[n]{x})^n = x` for
$`x \ge 0` and $`n \ge 1`. This is the transfer of the corresponding real statement. -/
theorem hroot_pow {n : ℕ} (hn : n ≠ 0) {x : ℝ*} (hx : 0 ≤ x) : hroot n x ^ n = x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  have hx' : ∀ᶠ k in hyperfilter ℕ, 0 ≤ r k := ofSeq_le_ofSeq_iff.1 hx
  rw [hroot_ofSeq]
  change Hyperreal.ofSeq (fun k => (r k ^ ((n : ℝ)⁻¹)) ^ n) = _
  rw [ofSeq_eq_ofSeq_iff]
  exact hx'.mono fun k hk => Real.rpow_inv_natCast_pow hk hn

/-- **Section 5.2, roots.** The $`n`-th root of a positive hyperreal is positive. -/
theorem hroot_pos {n : ℕ} (hn : n ≠ 0) {x : ℝ*} (hx : 0 < x) : 0 < hroot n x := by
  refine lt_of_le_of_ne (hroot_nonneg n hx.le) fun h => ?_
  have := hroot_pow hn hx.le
  rw [← h, zero_pow hn] at this
  exact hx.ne this

/-- **Section 5.2, roots.** If $`\varepsilon > 0` is infinitesimal then $`\sqrt[n]{\varepsilon}`
is infinitesimal. -/
theorem Infinitesimal.hroot (he : Infinitesimal e) (h0 : 0 < e) {n : ℕ} (hn : n ≠ 0) :
    Infinitesimal (hroot n e) :=
  infinitesimal_of_pow (by rwa [hroot_pow hn h0.le]) hn

/-- **Section 5.2, roots.** If $`b > 0` is appreciable then $`\sqrt[n]{b}` is appreciable. -/
theorem Appreciable.hroot (hb : Appreciable b) (h0 : 0 < b) {n : ℕ} (hn : n ≠ 0) :
    Appreciable (hroot n b) :=
  appreciable_of_pow (n := n) (by rwa [hroot_pow hn h0.le]) hn

/-- **Section 5.2, roots.** If $`H > 0` is unlimited then $`\sqrt[n]{H}` is unlimited. -/
theorem Unlimited.hroot (hH : Unlimited H) (h0 : 0 < H) {n : ℕ} (hn : n ≠ 0) :
    Unlimited (hroot n H) :=
  unlimited_of_pow (n := n) (by rwa [hroot_pow hn h0.le])

/-! ### Indeterminate forms -/

/-- The square of $`\varepsilon` is infinitesimal. -/
theorem infinitesimal_epsilon_sq : Infinitesimal ((ε : ℝ*) ^ 2) :=
  infinitesimal_epsilon.pow two_ne_zero

/-- The square of $`\omega` is unlimited. -/
theorem unlimited_omega_sq : Unlimited ((ω : ℝ*) ^ 2) :=
  unlimited_omega.pow two_ne_zero

/-- **Section 5.2, indeterminate forms.** A quotient $`\varepsilon/\delta` of infinitesimals
can be infinitesimal, appreciable or unlimited: witnesses are $`\varepsilon^2/\varepsilon`,
$`\varepsilon/\varepsilon` and $`\varepsilon/\varepsilon^2`. -/
theorem indeterminate_infinitesimal_div_infinitesimal :
    (∃ e d : ℝ*, Infinitesimal e ∧ Infinitesimal d ∧ d ≠ 0 ∧ Infinitesimal (e / d)) ∧
    (∃ e d : ℝ*, Infinitesimal e ∧ Infinitesimal d ∧ d ≠ 0 ∧ Appreciable (e / d)) ∧
    (∃ e d : ℝ*, Infinitesimal e ∧ Infinitesimal d ∧ d ≠ 0 ∧ Unlimited (e / d)) := by
  have h0 : (ε : ℝ*) ≠ 0 := Hyperreal.epsilon_ne_zero
  refine ⟨⟨ε ^ 2, ε, infinitesimal_epsilon_sq, infinitesimal_epsilon, h0, ?_⟩,
    ⟨ε, ε, infinitesimal_epsilon, infinitesimal_epsilon, h0, ?_⟩,
    ⟨ε, ε ^ 2, infinitesimal_epsilon, infinitesimal_epsilon_sq, pow_ne_zero 2 h0, ?_⟩⟩
  · have : (ε : ℝ*) ^ 2 / ε = ε := by field_simp
    rw [this]
    exact infinitesimal_epsilon
  · rw [div_self h0]
    exact appreciable_one
  · have : (ε : ℝ*) / ε ^ 2 = ω := by
      rw [← Hyperreal.inv_epsilon]
      field_simp
    rw [this]
    exact unlimited_omega

/-- **Section 5.2, indeterminate forms.** A quotient $`H/K` of unlimited numbers can be
infinitesimal, appreciable or unlimited: witnesses are $`\omega/\omega^2`, $`\omega/\omega`
and $`\omega^2/\omega`. -/
theorem indeterminate_unlimited_div_unlimited :
    (∃ H K : ℝ*, Unlimited H ∧ Unlimited K ∧ Infinitesimal (H / K)) ∧
    (∃ H K : ℝ*, Unlimited H ∧ Unlimited K ∧ Appreciable (H / K)) ∧
    (∃ H K : ℝ*, Unlimited H ∧ Unlimited K ∧ Unlimited (H / K)) := by
  have h0 : (ω : ℝ*) ≠ 0 := Hyperreal.omega_ne_zero
  refine ⟨⟨ω, ω ^ 2, unlimited_omega, unlimited_omega_sq, ?_⟩,
    ⟨ω, ω, unlimited_omega, unlimited_omega, ?_⟩,
    ⟨ω ^ 2, ω, unlimited_omega_sq, unlimited_omega, ?_⟩⟩
  · have : (ω : ℝ*) / ω ^ 2 = ε := by
      rw [← Hyperreal.inv_omega]
      field_simp
    rw [this]
    exact infinitesimal_epsilon
  · rw [div_self h0]
    exact appreciable_one
  · have : (ω : ℝ*) ^ 2 / ω = ω := by field_simp
    rw [this]
    exact unlimited_omega

/-- **Section 5.2, indeterminate forms.** A product $`\varepsilon \cdot H` of an infinitesimal
and an unlimited number can be infinitesimal, appreciable or unlimited: witnesses are
$`\varepsilon^2 \cdot \omega`, $`\varepsilon \cdot \omega` and
$`\varepsilon \cdot \omega^2`. -/
theorem indeterminate_infinitesimal_mul_unlimited :
    (∃ e H : ℝ*, Infinitesimal e ∧ Unlimited H ∧ Infinitesimal (e * H)) ∧
    (∃ e H : ℝ*, Infinitesimal e ∧ Unlimited H ∧ Appreciable (e * H)) ∧
    (∃ e H : ℝ*, Infinitesimal e ∧ Unlimited H ∧ Unlimited (e * H)) := by
  have h0 : (ε : ℝ*) ≠ 0 := Hyperreal.epsilon_ne_zero
  have h1 : (ω : ℝ*) ≠ 0 := Hyperreal.omega_ne_zero
  refine ⟨⟨ε ^ 2, ω, infinitesimal_epsilon_sq, unlimited_omega, ?_⟩,
    ⟨ε, ω, infinitesimal_epsilon, unlimited_omega, ?_⟩,
    ⟨ε, ω ^ 2, infinitesimal_epsilon, unlimited_omega_sq, ?_⟩⟩
  · have : (ε : ℝ*) ^ 2 * ω = ε := by
      rw [pow_two, mul_assoc, Hyperreal.epsilon_mul_omega, mul_one]
    rw [this]
    exact infinitesimal_epsilon
  · rw [Hyperreal.epsilon_mul_omega]
    exact appreciable_one
  · have : (ε : ℝ*) * ω ^ 2 = ω := by
      rw [pow_two, ← mul_assoc, Hyperreal.epsilon_mul_omega, one_mul]
    rw [this]
    exact unlimited_omega

/-- **Section 5.2, indeterminate forms.** A sum $`H + K` of unlimited numbers can be
infinitesimal, appreciable or unlimited: witnesses are $`\omega + (-\omega)`,
$`\omega + (1 - \omega)` and $`\omega + \omega`. -/
theorem indeterminate_unlimited_add_unlimited :
    (∃ H K : ℝ*, Unlimited H ∧ Unlimited K ∧ Infinitesimal (H + K)) ∧
    (∃ H K : ℝ*, Unlimited H ∧ Unlimited K ∧ Appreciable (H + K)) ∧
    (∃ H K : ℝ*, Unlimited H ∧ Unlimited K ∧ Unlimited (H + K)) := by
  refine ⟨⟨ω, -ω, unlimited_omega, unlimited_omega.neg, by simp⟩,
    ⟨ω, 1 - ω, unlimited_omega, ?_, by simp⟩,
    ⟨ω, ω, unlimited_omega, unlimited_omega, ?_⟩⟩
  · have : (1 : ℝ*) - ω = -ω + 1 := by ring
    rw [this]
    exact unlimited_omega.neg.add_limited limited_one
  · have : (ω : ℝ*) + ω = ω * 2 := by ring
    rw [this]
    exact unlimited_omega.mul_appreciable (by simpa using appreciable_coe (two_ne_zero (α := ℝ)))

/-! ### The ring of limited numbers and its ideal of infinitesimals -/

/-- **Section 5.2.** The limited hyperreals form a subring of the hyperreals. Its underlying
set is $`\mathbb L`. -/
def limitedSubring : Subring ℝ* where
  carrier := 𝕃
  zero_mem' := limited_zero
  one_mem' := limited_one
  add_mem' := Limited.add
  mul_mem' := Limited.mul
  neg_mem' := Limited.neg

@[simp] theorem mem_limitedSubring {b : ℝ*} : b ∈ limitedSubring ↔ Limited b := Iff.rfl

@[simp] theorem coe_limitedSubring : (limitedSubring : Set ℝ*) = 𝕃 := rfl

/-- Every member of the ring of limited numbers is limited. -/
theorem limitedSubring.limited (x : limitedSubring) : Limited (x : ℝ*) := x.2

/-- **Section 5.2.** The infinitesimals form a subring of the hyperreals in the sense that
they contain zero and are closed under addition, negation and multiplication. They do not
contain $`1`, so in Mathlib's terminology this is a non-unital subring. Its underlying set is
$`\mathbb I`. -/
def infinitesimalNonUnitalSubring : NonUnitalSubring ℝ* where
  carrier := 𝕀
  zero_mem' := infinitesimal_zero
  add_mem' := Infinitesimal.add
  mul_mem' := Infinitesimal.mul
  neg_mem' := Infinitesimal.neg

@[simp] theorem mem_infinitesimalNonUnitalSubring {b : ℝ*} :
    b ∈ infinitesimalNonUnitalSubring ↔ Infinitesimal b := Iff.rfl

/-- **Section 5.2.** The infinitesimals form an ideal in the ring of limited numbers: they are
closed under addition, and the product of a limited number and an infinitesimal is
infinitesimal. -/
def infinitesimalIdeal : Ideal limitedSubring where
  carrier := {x | Infinitesimal (x : ℝ*)}
  zero_mem' := infinitesimal_zero
  add_mem' := fun ha hb => Infinitesimal.add ha hb
  smul_mem' := fun c _ hx => c.2.mul_infinitesimal hx

@[simp] theorem mem_infinitesimalIdeal {x : limitedSubring} :
    x ∈ infinitesimalIdeal ↔ Infinitesimal (x : ℝ*) := Iff.rfl

/-- **Section 5.2.** The ideal of infinitesimals is proper: $`1` is not infinitesimal. -/
theorem infinitesimalIdeal_ne_top : infinitesimalIdeal ≠ ⊤ := fun h => by
  have : (1 : limitedSubring) ∈ infinitesimalIdeal := h ▸ Submodule.mem_top
  exact appreciable_one.2 this

/-! ### Exercise 5.2.1 and roots of hypernatural order -/

/-- **Exercise 5.2.1.** The hyperreal power $`a^x`: the extension of the two-place real
function $`(a, x) \mapsto a^x`. It is defined for all hyperreal $`a` and $`x`, and is
meaningful for $`a > 0`, where the real function is the usual exponential with base $`a`. -/
def hpow : ℝ* → ℝ* → ℝ* := ⋆(fun a x : ℝ => a ^ x)

/-- The hyperreal power of classes of sequences is the class of the termwise powers. -/
theorem hpow_ofSeq (r s : ℕ → ℝ) :
    hpow (Hyperreal.ofSeq r) (Hyperreal.ofSeq s) = Hyperreal.ofSeq fun n => r n ^ s n := rfl

/-- **Exercise 5.2.1.** On real arguments the hyperreal power is the real power. -/
theorem hpow_coe (a x : ℝ) : hpow (a : ℝ*) (x : ℝ*) = ((a ^ x : ℝ) : ℝ*) := rfl

/-- **Exercise 5.2.1.** $`a^x > 0` for every positive hyperreal $`a` and every hyperreal
$`x`. -/
theorem hpow_pos {a : ℝ*} (ha : 0 < a) (x : ℝ*) : 0 < hpow a x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep x
  have ha' : ∀ᶠ n in hyperfilter ℕ, 0 < r n := ofSeq_lt_ofSeq_iff.1 ha
  rw [hpow_ofSeq]
  change Hyperreal.ofSeq (fun _ => 0) < _
  rw [ofSeq_lt_ofSeq_iff]
  exact ha'.mono fun n hn => Real.rpow_pos_of_pos hn _

/-- **Exercise 5.2.1.** $`a^{x+y} = a^x \cdot a^y` for positive hyperreal $`a`. -/
theorem hpow_add {a : ℝ*} (ha : 0 < a) (x y : ℝ*) : hpow a (x + y) = hpow a x * hpow a y := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep x
  obtain ⟨t, rfl⟩ := hyperreal_exists_rep y
  have ha' : ∀ᶠ n in hyperfilter ℕ, 0 < r n := ofSeq_lt_ofSeq_iff.1 ha
  change Hyperreal.ofSeq (fun n => r n ^ (s n + t n)) =
    Hyperreal.ofSeq (fun n => r n ^ s n * r n ^ t n)
  rw [ofSeq_eq_ofSeq_iff]
  exact ha'.mono fun n hn => Real.rpow_add hn _ _

/-- **Exercise 5.2.1.** $`a^0 = 1`. -/
@[simp]
theorem hpow_zero (a : ℝ*) : hpow a 0 = 1 := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep a
  change Hyperreal.ofSeq (fun n => r n ^ (0 : ℝ)) = Hyperreal.ofSeq (fun _ => 1)
  rw [ofSeq_eq_ofSeq_iff]
  exact Eventually.of_forall fun n => Real.rpow_zero _

/-- **Exercise 5.2.1.** $`a^1 = a`. -/
@[simp]
theorem hpow_one (a : ℝ*) : hpow a 1 = a := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep a
  change Hyperreal.ofSeq (fun n => r n ^ (1 : ℝ)) = Hyperreal.ofSeq r
  rw [ofSeq_eq_ofSeq_iff]
  exact Eventually.of_forall fun n => Real.rpow_one _

/-- **Exercise 5.2.1.** $`a^{-x} = 1/a^x` for nonnegative hyperreal $`a`. -/
theorem hpow_neg {a : ℝ*} (ha : 0 ≤ a) (x : ℝ*) : hpow a (-x) = (hpow a x)⁻¹ := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep x
  have ha' : ∀ᶠ n in hyperfilter ℕ, 0 ≤ r n := ofSeq_le_ofSeq_iff.1 ha
  change Hyperreal.ofSeq (fun n => r n ^ (-s n)) = Hyperreal.ofSeq (fun n => (r n ^ s n)⁻¹)
  rw [ofSeq_eq_ofSeq_iff]
  exact ha'.mono fun n hn => Real.rpow_neg hn _

/-- **Exercise 5.2.1.** $`a^{xy} = (a^x)^y` for nonnegative hyperreal $`a`. -/
theorem hpow_mul {a : ℝ*} (ha : 0 ≤ a) (x y : ℝ*) : hpow a (x * y) = hpow (hpow a x) y := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep x
  obtain ⟨t, rfl⟩ := hyperreal_exists_rep y
  have ha' : ∀ᶠ n in hyperfilter ℕ, 0 ≤ r n := ofSeq_le_ofSeq_iff.1 ha
  change Hyperreal.ofSeq (fun n => r n ^ (s n * t n)) =
    Hyperreal.ofSeq (fun n => (r n ^ s n) ^ t n)
  rw [ofSeq_eq_ofSeq_iff]
  exact ha'.mono fun n hn => Real.rpow_mul hn _ _

/-- **Exercise 5.2.1.** $`(ab)^x = a^x b^x` for nonnegative hyperreals $`a, b`. -/
theorem mul_hpow {a b : ℝ*} (ha : 0 ≤ a) (hb : 0 ≤ b) (x : ℝ*) :
    hpow (a * b) x = hpow a x * hpow b x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep b
  obtain ⟨t, rfl⟩ := hyperreal_exists_rep x
  have ha' : ∀ᶠ n in hyperfilter ℕ, 0 ≤ r n := ofSeq_le_ofSeq_iff.1 ha
  have hb' : ∀ᶠ n in hyperfilter ℕ, 0 ≤ s n := ofSeq_le_ofSeq_iff.1 hb
  change Hyperreal.ofSeq (fun n => (r n * s n) ^ t n) =
    Hyperreal.ofSeq (fun n => r n ^ t n * s n ^ t n)
  rw [ofSeq_eq_ofSeq_iff]
  filter_upwards [ha', hb'] with n h1 h2 using Real.mul_rpow h1 h2

/-- **Exercise 5.2.1.** For a base $`a > 1` the function $`x \mapsto a^x` is strictly
increasing on the hyperreals. -/
theorem hpow_lt_hpow {a : ℝ*} (ha : 1 < a) {x y : ℝ*} (h : x < y) : hpow a x < hpow a y := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep x
  obtain ⟨t, rfl⟩ := hyperreal_exists_rep y
  have ha' : ∀ᶠ n in hyperfilter ℕ, 1 < r n := by
    have ha1 : Hyperreal.ofSeq (fun _ => 1) < Hyperreal.ofSeq r := ha
    exact ofSeq_lt_ofSeq_iff.1 ha1
  have h' : ∀ᶠ n in hyperfilter ℕ, s n < t n := ofSeq_lt_ofSeq_iff.1 h
  rw [hpow_ofSeq, hpow_ofSeq, ofSeq_lt_ofSeq_iff]
  filter_upwards [ha', h'] with n h1 h2 using Real.rpow_lt_rpow_of_exponent_lt h1 h2

/-- **Exercise 5.2.1.** For a base $`0 < a < 1` the function $`x \mapsto a^x` is strictly
decreasing on the hyperreals. -/
theorem hpow_lt_hpow_of_base_lt_one {a : ℝ*} (h0 : 0 < a) (h1 : a < 1) {x y : ℝ*}
    (h : x < y) : hpow a y < hpow a x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep x
  obtain ⟨t, rfl⟩ := hyperreal_exists_rep y
  have h0' : ∀ᶠ n in hyperfilter ℕ, 0 < r n := ofSeq_lt_ofSeq_iff.1 h0
  have h1' : ∀ᶠ n in hyperfilter ℕ, r n < 1 := by
    have : Hyperreal.ofSeq r < Hyperreal.ofSeq (fun _ => 1) := h1
    exact ofSeq_lt_ofSeq_iff.1 this
  have h' : ∀ᶠ n in hyperfilter ℕ, s n < t n := ofSeq_lt_ofSeq_iff.1 h
  rw [hpow_ofSeq, hpow_ofSeq, ofSeq_lt_ofSeq_iff]
  filter_upwards [h0', h1', h'] with n k0 k1 k2
    using Real.rpow_lt_rpow_of_exponent_gt k0 k1 k2

/-- **Exercise 5.2.1.** With a hypernatural exponent given by a sequence of natural numbers,
the hyperreal power is the class of the termwise natural powers. -/
theorem hpow_ofSeq_natCast (r : ℕ → ℝ) (k : ℕ → ℕ) :
    hpow (Hyperreal.ofSeq r) (Hyperreal.ofSeq fun n => (k n : ℝ)) =
      Hyperreal.ofSeq fun n => r n ^ k n := by
  rw [hpow_ofSeq, ofSeq_eq_ofSeq_iff]
  exact Eventually.of_forall fun n => Real.rpow_natCast _ _

/-- **Exercise 5.2.1.** For a standard natural exponent the hyperreal power is the ordinary
power of the field of hyperreals. -/
theorem hpow_natCast (a : ℝ*) (n : ℕ) : hpow a (n : ℝ*) = a ^ n := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep a
  exact hpow_ofSeq_natCast r fun _ => n

/-- **Section 5.2, roots of hypernatural order.** The transfer of the statement that every
positive real has an $`n`-th root for every positive natural $`n`: every positive hyperreal
$`x` has a positive $`N`-th root for every nonzero hypernatural $`N`, that is, a $`y > 0` with
$`y^N = x`. -/
theorem exists_hpow_eq {x : ℝ*} (hx : 0 < x) {N : ℝ*} (_hN : N ∈ ℕ*) (hN0 : N ≠ 0) :
    ∃ y : ℝ*, 0 < y ∧ hpow y N = x :=
  ⟨hpow x N⁻¹, hpow_pos hx _, by rw [← hpow_mul hx.le, inv_mul_cancel₀ hN0, hpow_one]⟩

end Arithmetic

/-!
## 5.3 On the Use of "Finite" and "Infinite"

The book explains why it says "limited" and "unlimited" and not "finite" and "infinite": the
latter words are kept for their set-theoretic meaning. The point is illustrated by the
initial segment of the hypernaturals below an unlimited hypernatural $`N`. As a set it is
infinite, although by transfer it behaves like a finite set in many ways; such _hyperfinite_
sets are studied in Chapter 12. The one formal claim of the section is recorded here.
-/

section FiniteInfinite

/-- **Section 5.3.** If $`N` is an unlimited hypernatural, the set
$`\{k \in {}^*\mathbb N : k \le N\}` is infinite as a set: it contains every standard natural
number. -/
theorem infinite_setOf_hyperNat_le {N : ℝ*} (hN : N ∈ ℕ*) (hU : Unlimited N) :
    {k : ℝ* | k ∈ ℕ* ∧ k ≤ N}.Infinite := by
  have hpos : PosUnlimited N := by
    rcases hU with h | h
    · exact h
    · exact absurd (h 0) (not_lt.2 (by simpa using hyperNat_nonneg hN))
  refine infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℝ*)) Nat.cast_injective
    fun n => ⟨natCast_mem_hyperNat n, ?_⟩
  have := hpos n
  rw [ofReal_natCast] at this
  exact this.le

end FiniteInfinite

end Goldblatt
