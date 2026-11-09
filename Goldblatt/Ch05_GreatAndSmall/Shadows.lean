import Goldblatt.Ch05_GreatAndSmall.Arithmetic

/-!
# 5 (part 2). Halos, Galaxies and Shadows: Sections 5.4 to 5.9

This is the second of three parts of Chapter 5 (the overview is on the chapter page
{lit}`Goldblatt.Ch05_GreatAndSmall`). It introduces infinite closeness and limited distance,
with their equivalence classes the halos and the galaxies, proves that every limited hyperreal
has a unique shadow, shows that taking shadows is a ring homomorphism from the limited numbers
onto the reals whose kernel is the ideal of infinitesimals, and establishes that the existence
of shadows is equivalent to the completeness of the real numbers.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## 5.4 Halos, Galaxies, and Real Comparisons

Two hyperreals are _infinitely close_ when their difference is infinitesimal, and _of limited
distance apart_ when their difference is limited. Both are equivalence relations. The class of
$`b` under the first is its _halo_, under the second its _galaxy_. The halo of zero is the set
of infinitesimals and the galaxy of zero is the set of limited numbers.

The book writes $`b \simeq c` for infinite closeness. In Lean that symbol is the notation for
an equivalence of types, with a binding power that makes it unusable between numbers, so
infinite closeness is written {lit}`b ≊ c` here. Limited distance is written {lit}`b ∼ c`, as
in the book.
-/

section HalosGalaxies

variable {b c d x y : ℝ*}

/-- **Section 5.4.** The hyperreal $`b` is _infinitely close_ to $`c`, written
$`b \simeq c` in the book and {lit}`b ≊ c` here, if $`b - c` is infinitesimal. -/
def InfClose (b c : ℝ*) : Prop := Infinitesimal (b - c)

@[inherit_doc] scoped infix:50 " ≊ " => InfClose

/-- **Section 5.4.** The hyperreals $`b` and $`c` are _of limited distance apart_, written
$`b \sim c`, if $`b - c` is limited. -/
def LimClose (b c : ℝ*) : Prop := Limited (b - c)

@[inherit_doc] scoped infix:50 " ∼ " => LimClose

/-- **Section 5.4.** The _halo_ of $`b`: the set of hyperreals infinitely close to $`b`. -/
def hal (b : ℝ*) : Set ℝ* := {c | b ≊ c}

/-- **Section 5.4.** The _galaxy_ of $`b`: the set of hyperreals at limited distance from
$`b`. -/
def gal (b : ℝ*) : Set ℝ* := {c | b ∼ c}

@[simp] theorem mem_hal : c ∈ hal b ↔ b ≊ c := Iff.rfl

@[simp] theorem mem_gal : c ∈ gal b ↔ b ∼ c := Iff.rfl

theorem infClose_iff : b ≊ c ↔ Infinitesimal (b - c) := Iff.rfl

theorem limClose_iff : b ∼ c ↔ Limited (b - c) := Iff.rfl

/-- $`b \simeq c` if and only if $`|b - c| < r` for every positive real $`r`. -/
theorem infClose_iff_abs_lt : b ≊ c ↔ ∀ r : ℝ, 0 < r → |b - c| < r :=
  infinitesimal_iff_abs_lt

/-- **Section 5.4.** $`b` is infinitesimal if and only if $`b \simeq 0`. -/
theorem infinitesimal_iff_infClose_zero : Infinitesimal b ↔ b ≊ 0 := by
  rw [infClose_iff, sub_zero]

/-- **Section 5.4.** $`b` is limited if and only if $`b \sim 0`. -/
theorem limited_iff_limClose_zero : Limited b ↔ b ∼ 0 := by
  rw [limClose_iff, sub_zero]

/-- **Exercise 5.5(1).** Infinite closeness is reflexive. -/
@[refl, simp]
theorem InfClose.refl (b : ℝ*) : b ≊ b := by
  rw [infClose_iff, sub_self]
  exact infinitesimal_zero

/-- **Exercise 5.5(1).** Infinite closeness is symmetric. -/
@[symm]
theorem InfClose.symm (h : b ≊ c) : c ≊ b := by
  rw [infClose_iff] at *
  simpa using h.neg

/-- **Exercise 5.5(1).** Infinite closeness is transitive. -/
theorem InfClose.trans (h₁ : b ≊ c) (h₂ : c ≊ d) : b ≊ d := by
  rw [infClose_iff] at *
  simpa using h₁.add h₂

instance : Trans InfClose InfClose InfClose := ⟨InfClose.trans⟩

theorem infClose_comm : b ≊ c ↔ c ≊ b := ⟨InfClose.symm, InfClose.symm⟩

/-- **Exercise 5.5(1).** Infinite closeness is an equivalence relation on the hyperreals. -/
theorem infClose_equivalence : Equivalence InfClose :=
  ⟨InfClose.refl, InfClose.symm, InfClose.trans⟩

/-- **Exercise 5.5(1).** Limited distance is reflexive. -/
@[refl, simp]
theorem LimClose.refl (b : ℝ*) : b ∼ b := by
  rw [limClose_iff, sub_self]
  exact limited_zero

/-- **Exercise 5.5(1).** Limited distance is symmetric. -/
@[symm]
theorem LimClose.symm (h : b ∼ c) : c ∼ b := by
  rw [limClose_iff] at *
  simpa using h.neg

/-- **Exercise 5.5(1).** Limited distance is transitive. -/
theorem LimClose.trans (h₁ : b ∼ c) (h₂ : c ∼ d) : b ∼ d := by
  rw [limClose_iff] at *
  simpa using h₁.add h₂

instance : Trans LimClose LimClose LimClose := ⟨LimClose.trans⟩

theorem limClose_comm : b ∼ c ↔ c ∼ b := ⟨LimClose.symm, LimClose.symm⟩

/-- **Exercise 5.5(1).** Limited distance is an equivalence relation on the hyperreals. -/
theorem limClose_equivalence : Equivalence LimClose :=
  ⟨LimClose.refl, LimClose.symm, LimClose.trans⟩

/-- Infinitely close numbers are at limited distance. -/
theorem InfClose.limClose (h : b ≊ c) : b ∼ c := Infinitesimal.limited h

/-- **Section 5.4.** The halo of $`0` is the set $`\mathbb I` of infinitesimals. -/
theorem hal_zero : hal 0 = 𝕀 := by
  ext c
  rw [mem_hal, infClose_comm, ← infinitesimal_iff_infClose_zero, mem_infinitesimalSet]

/-- **Section 5.4.** The galaxy of $`0` is the set $`\mathbb L` of limited hyperreals. -/
theorem gal_zero : gal 0 = 𝕃 := by
  ext c
  rw [mem_gal, limClose_comm, ← limited_iff_limClose_zero, mem_limitedSet]

/-- A halo is the equivalence class of any of its members. -/
theorem hal_eq_hal_iff : hal b = hal c ↔ b ≊ c := by
  constructor
  · intro h
    have : c ∈ hal b := h ▸ InfClose.refl c
    exact this
  · intro h
    ext z
    exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

/-- A galaxy is the equivalence class of any of its members. -/
theorem gal_eq_gal_iff : gal b = gal c ↔ b ∼ c := by
  constructor
  · intro h
    have : c ∈ gal b := h ▸ LimClose.refl c
    exact this
  · intro h
    ext z
    exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

/-- A number that is infinitely close to a limited number is limited. -/
theorem Limited.of_infClose (hb : Limited b) (h : b ≊ c) : Limited c := by
  have := hb.sub h.limited
  simpa using this

/-- A number at limited distance from a limited number is limited. -/
theorem Limited.of_limClose (hb : Limited b) (h : b ∼ c) : Limited c := by
  have := hb.sub h
  simpa using this

/-- A hyperreal whose absolute value is bounded by that of an infinitesimal is
infinitesimal. -/
theorem Infinitesimal.of_abs_le {e : ℝ*} (he : Infinitesimal e) (h : |x| ≤ |e|) :
    Infinitesimal x := by
  rw [infinitesimal_iff_abs_lt] at *
  exact fun r hr => h.trans_lt (he r hr)

/-- A hyperreal whose absolute value is bounded by that of a limited number is limited. -/
theorem Limited.of_abs_le (hb : Limited b) (h : |x| ≤ |b|) : Limited x := by
  rw [limited_iff_abs_lt] at *
  obtain ⟨r, hr⟩ := hb
  exact ⟨r, h.trans_lt hr⟩

/-- Two real numbers are infinitely close only if they are equal. -/
@[simp]
theorem infClose_coe_iff {r s : ℝ} : (r : ℝ*) ≊ s ↔ r = s := by
  rw [infClose_iff, ← Hyperreal.coe_sub, infinitesimal_coe_iff, sub_eq_zero]

end HalosGalaxies

/-!
## 5.5 Exercises on Halos and Galaxies

The exercises verify that the two relations are equivalence relations (done above, where the
relations are introduced), describe halos and galaxies as translates of the halo and the
galaxy of zero, and examine how infinite closeness interacts with the order and with
multiplication. Exercise (6) needs the integer part of a hyperreal, which is introduced here
as the extension of the real floor function.

The discussion of _real comparisons_ that follows the exercises is the principle used
throughout the later chapters to compare two real numbers by looking at hyperreals in their
halos.
-/

section HaloExercises

variable {b c d x y : ℝ*}

/-- **Exercise 5.5(2).** If $`b \simeq x \le y \simeq c` with $`b` and $`c` real, then
$`b \le c`. -/
theorem coe_le_coe_of_infClose_le_infClose {b c : ℝ} (h₁ : (b : ℝ*) ≊ x) (h₂ : x ≤ y)
    (h₃ : y ≊ c) : b ≤ c := by
  by_contra hlt
  rw [not_le] at hlt
  have hd : 0 < (b - c) / 2 := by linarith
  have e₁ := (abs_lt.1 (infClose_iff_abs_lt.1 h₁ _ hd)).2
  have e₂ := (abs_lt.1 (infClose_iff_abs_lt.1 h₃ _ hd)).2
  have e₃ : ((b - c : ℝ) : ℝ*) < ((b - c) / 2 : ℝ) + ((b - c) / 2 : ℝ) := by
    rw [Hyperreal.coe_sub]
    linarith
  rw [← Hyperreal.coe_add, add_halves] at e₃
  exact lt_irrefl _ e₃

/-- **Exercise 5.5(2), the general case.** If $`b \simeq x \le y \simeq c` and $`b, c` are
arbitrary hyperreals, then either $`b \le c` or $`b \simeq c`. -/
theorem le_or_infClose_of_infClose_le_infClose (h₁ : b ≊ x) (h₂ : x ≤ y) (h₃ : y ≊ c) :
    b ≤ c ∨ b ≊ c := by
  rcases le_or_gt b c with h | h
  · exact Or.inl h
  · refine Or.inr (Infinitesimal.of_abs_le (Infinitesimal.add h₁ h₃) ?_)
    rw [abs_of_pos (sub_pos.2 h)]
    refine le_trans ?_ (le_abs_self _)
    linarith

/-- **Exercise 5.5(2), what can go wrong.** If $`b` and $`c` are not real, the conclusion
$`b \le c` can fail: $`\varepsilon \simeq 0 \le 0 \simeq 0` but $`\varepsilon > 0`. -/
theorem exists_infClose_le_infClose_not_le :
    ∃ b x y c : ℝ*, b ≊ x ∧ x ≤ y ∧ y ≊ c ∧ ¬ b ≤ c :=
  ⟨ε, 0, 0, 0, infinitesimal_iff_infClose_zero.1 infinitesimal_epsilon, le_rfl,
    InfClose.refl 0, not_le.2 Hyperreal.epsilon_pos⟩

/-- **Exercise 5.5(3).** $`\operatorname{hal}(b) = \{b + c : c \in \operatorname{hal}(0)\}`. -/
theorem hal_eq_image_add (b : ℝ*) : hal b = (fun c => b + c) '' hal 0 := by
  ext z
  simp only [mem_hal, mem_image]
  constructor
  · intro h
    refine ⟨z - b, ?_, by ring⟩
    rw [infClose_iff] at *
    simpa using h
  · rintro ⟨c, hc, rfl⟩
    rw [infClose_iff] at *
    simpa using hc

/-- **Exercise 5.5(4).** $`\operatorname{gal}(b) = \{b + c : c \in \operatorname{gal}(0)\}`. -/
theorem gal_eq_image_add (b : ℝ*) : gal b = (fun c => b + c) '' gal 0 := by
  ext z
  simp only [mem_gal, mem_image]
  constructor
  · intro h
    refine ⟨z - b, ?_, by ring⟩
    rw [limClose_iff] at *
    simpa using h
  · rintro ⟨c, hc, rfl⟩
    rw [limClose_iff] at *
    simpa using hc

/-- **Exercise 5.5(5).** If $`x \simeq y` and $`b` is limited then $`b \cdot x \simeq b \cdot y`. -/
theorem InfClose.mul_left (h : x ≊ y) (hb : Limited b) : b * x ≊ b * y := by
  rw [infClose_iff, ← mul_sub]
  exact hb.mul_infinitesimal h

/-- If $`x \simeq y` and $`b` is limited then $`x \cdot b \simeq y \cdot b`. -/
theorem InfClose.mul_right (h : x ≊ y) (hb : Limited b) : x * b ≊ y * b := by
  rw [mul_comm x, mul_comm y]
  exact h.mul_left hb

/-- **Exercise 5.5(5), failure for unlimited factors.** With $`b = \omega`,
$`x = \varepsilon` and $`y = 0` we have $`x \simeq y` but $`b x = 1` and $`b y = 0` are not
infinitely close. -/
theorem exists_infClose_mul_unlimited_not_infClose :
    ∃ b x y : ℝ*, Unlimited b ∧ x ≊ y ∧ ¬ b * x ≊ b * y := by
  refine ⟨ω, ε, 0, unlimited_omega, infinitesimal_iff_infClose_zero.1 infinitesimal_epsilon, ?_⟩
  rw [infClose_iff, mul_zero, sub_zero, mul_comm, Hyperreal.epsilon_mul_omega]
  exact appreciable_one.2

/-- **Section 5.5.** The integer part of a hyperreal: the extension of the real floor
function, with values regarded as hyperreals. -/
def hfloor : ℝ* → ℝ* := ⋆(fun x : ℝ => (⌊x⌋ : ℝ))

/-- The integer part of the class of a sequence is the class of the integer parts. -/
theorem hfloor_ofSeq (r : ℕ → ℝ) :
    hfloor (Hyperreal.ofSeq r) = Hyperreal.ofSeq fun n => (⌊r n⌋ : ℝ) := rfl

/-- The integer part of a hyperreal is a hyperinteger. -/
theorem hfloor_mem_hyperInt (x : ℝ*) : hfloor x ∈ ℤ* := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  exact mem_hyperInt_iff.2 ⟨fun n => ⌊r n⌋, rfl⟩

/-- The integer part of a nonnegative hyperreal is a hypernatural. -/
theorem hfloor_mem_hyperNat (hx : 0 ≤ x) : hfloor x ∈ ℕ* := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  have hx' : ∀ᶠ n in hyperfilter ℕ, 0 ≤ r n := ofSeq_le_ofSeq_iff.1 hx
  rw [hfloor_ofSeq]
  refine mem_hyperNat_iff.2 ⟨fun n => ⌊r n⌋₊, ?_⟩
  rw [ofSeq_eq_ofSeq_iff]
  exact hx'.mono fun n hn => by
    rw [← Int.cast_natCast, Int.natCast_floor_eq_floor hn]

/-- The integer part of $`x` is at most $`x`. -/
theorem hfloor_le (x : ℝ*) : hfloor x ≤ x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [hfloor_ofSeq, ofSeq_le_ofSeq_iff]
  exact Eventually.of_forall fun n => Int.floor_le _

/-- $`x` is less than its integer part plus one. -/
theorem lt_hfloor_add_one (x : ℝ*) : x < hfloor x + 1 := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  change _ < Hyperreal.ofSeq fun n => (⌊r n⌋ : ℝ) + 1
  rw [ofSeq_lt_ofSeq_iff]
  exact Eventually.of_forall fun n => Int.lt_floor_add_one _

/-- A hyperreal is at limited distance from its integer part. -/
theorem limClose_hfloor (x : ℝ*) : x ∼ hfloor x := by
  rw [limClose_iff, limited_iff_abs_lt]
  refine ⟨2, ?_⟩
  have h1 := hfloor_le x
  have h2 := lt_hfloor_add_one x
  rw [abs_lt]
  constructor
  · have : (-((2 : ℝ) : ℝ*)) < 0 := by simp
    linarith
  · have : (1 : ℝ*) < ((2 : ℝ) : ℝ*) := by simp
    linarith

/-- **Exercise 5.5(6), hyperintegers.** Every galaxy contains a hyperinteger. -/
theorem exists_hyperInt_mem_gal (b : ℝ*) : ∃ z ∈ ℤ*, z ∈ gal b :=
  ⟨hfloor b, hfloor_mem_hyperInt b, limClose_hfloor b⟩

/-- **Exercise 5.5(6), hyperrationals.** Every galaxy contains a hyperrational that is not a
hyperinteger. -/
theorem exists_hyperRat_not_hyperInt_mem_gal (b : ℝ*) : ∃ q ∈ ℚ* \ ℤ*, q ∈ gal b := by
  have hhalf : (((1 / 2 : ℝ) : ℝ*)) ∈ ℚ* := coe_mem_starSet.2 ⟨1 / 2, by simp⟩
  have hhalf' : (((1 / 2 : ℝ) : ℝ*)) ∉ ℤ* := by
    intro h
    obtain ⟨n, hn⟩ := coe_mem_starSet.1 h
    have h2 : (2 * n : ℤ) = 1 := by
      have : (2 : ℝ) * n = 1 := by rw [hn]; norm_num
      exact_mod_cast this
    omega
  refine ⟨hfloor b + ((1 / 2 : ℝ) : ℝ*), ⟨?_, fun h => hhalf' ?_⟩, ?_⟩
  · exact hyperRatSubfield.add_mem (hyperInt_subset_hyperRat (hfloor_mem_hyperInt b)) hhalf
  · have h' : hfloor b + ((1 / 2 : ℝ) : ℝ*) - hfloor b ∈ ℤ* :=
      hyperIntSubring.sub_mem h (hfloor_mem_hyperInt b)
    rwa [add_sub_cancel_left] at h'
  · refine (limClose_hfloor b).trans ?_
    rw [limClose_iff]
    have : hfloor b - (hfloor b + ((1 / 2 : ℝ) : ℝ*)) = ((-(1 / 2) : ℝ) : ℝ*) := by
      rw [Hyperreal.coe_neg]
      ring
    rw [this]
    exact limited_coe _

/-- **Exercise 5.5(6), hyperirrationals.** Every galaxy contains a hyperreal that is not
hyperrational. -/
theorem exists_not_hyperRat_mem_gal (b : ℝ*) : ∃ x ∉ ℚ*, x ∈ gal b := by
  have hirr : (((√2 : ℝ)) : ℝ*) ∉ ℚ* := by
    intro h
    obtain ⟨q, hq⟩ := coe_mem_starSet.1 h
    exact irrational_sqrt_two ⟨q, hq⟩
  refine ⟨hfloor b + ((√2 : ℝ) : ℝ*), fun h => hirr ?_, ?_⟩
  · have h' : hfloor b + ((√2 : ℝ) : ℝ*) - hfloor b ∈ ℚ* :=
      hyperRatSubfield.sub_mem h (hyperInt_subset_hyperRat (hfloor_mem_hyperInt b))
    rwa [add_sub_cancel_left] at h'
  · refine (limClose_hfloor b).trans ?_
    rw [limClose_iff]
    have : hfloor b - (hfloor b + ((√2 : ℝ) : ℝ*)) = ((-√2 : ℝ) : ℝ*) := by
      rw [Hyperreal.coe_neg]
      ring
    rw [this]
    exact limited_coe _

/-- **Section 5.5, real comparisons.** If $`b > c` are real numbers, everything in the halo of
$`b` is greater than everything in the halo of $`c`. -/
theorem lt_of_mem_hal_of_coe_lt {b c : ℝ} (h : c < b) (hx : x ∈ hal (b : ℝ*))
    (hy : y ∈ hal (c : ℝ*)) : y < x := by
  by_contra hle
  rw [not_lt] at hle
  exact absurd (coe_le_coe_of_infClose_le_infClose hx hle (InfClose.symm hy)) (not_le.2 h)

/-- **Section 5.5, real comparisons.** The halos of two distinct real numbers are disjoint. -/
theorem disjoint_hal_coe {b c : ℝ} (h : b ≠ c) : Disjoint (hal (b : ℝ*)) (hal (c : ℝ*)) := by
  rw [Set.disjoint_left]
  intro z hb hc
  exact h (infClose_coe_iff.1 (InfClose.trans hb (InfClose.symm hc)))

/-- **Section 5.5, real comparisons.** To prove $`b \le c` for real numbers it is enough to
find an $`x` with $`b \simeq x \le c`. -/
theorem coe_le_coe_of_infClose_le {b c : ℝ} (h₁ : (b : ℝ*) ≊ x) (h₂ : x ≤ c) : b ≤ c :=
  coe_le_coe_of_infClose_le_infClose h₁ h₂ (InfClose.refl _)

/-- **Section 5.5, real comparisons.** To prove $`b \le c` for real numbers it is enough to
find an $`x` with $`b \le x \simeq c`. -/
theorem coe_le_coe_of_le_infClose {b c : ℝ} (h₁ : (b : ℝ*) ≤ x) (h₂ : x ≊ c) : b ≤ c :=
  coe_le_coe_of_infClose_le_infClose (InfClose.refl _) h₁ h₂

end HaloExercises

/-!
## 5.6 Shadows

Every limited hyperreal is infinitely close to exactly one real number, its _shadow_ (also
called its standard part). The proof uses the Dedekind completeness of the reals: the shadow of
$`b` is the least upper bound of the set of reals below $`b`. We take this least upper bound
as the definition of the shadow, so that the definition is the book's proof; for an unlimited
$`b` the set of reals below it is empty or unbounded and the least upper bound is by
convention $`0`.

Taking shadows respects the field operations, the absolute value, square roots and the order.
Consequently it is an order-preserving ring homomorphism from the limited numbers onto the
reals with kernel the infinitesimals, and the quotient of the ring of limited numbers by the
ideal of infinitesimals is the field of real numbers.

Mathlib's standard part function {name}`ArchimedeanClass.stdPart` is defined for any ordered
field through the residue field of the ring of finite elements. On the hyperreals it agrees
with the shadow, including at the unlimited numbers.
-/

section Shadows

variable {b c d x y : ℝ*}

/-- **Theorem 5.6.1, definition of the shadow.** The _shadow_ $`\operatorname{sh}(b)` of a
hyperreal $`b`: the least upper bound of the set of real numbers below $`b`. For limited
$`b` it is the unique real infinitely close to $`b`; for unlimited $`b` it is $`0`. -/
def sh (b : ℝ*) : ℝ := sSup {r : ℝ | (r : ℝ*) < b}

/-- **Theorem 5.6.1, existence.** Every limited hyperreal is infinitely close to its shadow.
The proof is the book's: the set of reals below $`b` is nonempty and bounded above, and its
least upper bound $`c` satisfies $`c - e < b \le c + e` for every positive real $`e`. -/
theorem Limited.infClose_sh (hb : Limited b) : b ≊ sh b := by
  obtain ⟨r, s, hr, hs⟩ := hb
  have hne : {t : ℝ | (t : ℝ*) < b}.Nonempty := ⟨r, hr⟩
  have hbdd : BddAbove {t : ℝ | (t : ℝ*) < b} :=
    ⟨s, fun t ht => (Hyperreal.coe_lt_coe.1 (lt_trans ht hs)).le⟩
  have hlub : IsLUB {t : ℝ | (t : ℝ*) < b} (sh b) := Real.isLUB_sSup hne hbdd
  have key : ∀ e : ℝ, 0 < e → |b - sh b| ≤ e := by
    intro e he
    have h1 : b ≤ ((sh b + e : ℝ) : ℝ*) := by
      by_contra hlt
      have := hlub.1 (show sh b + e ∈ {t : ℝ | (t : ℝ*) < b} from not_le.1 hlt)
      linarith
    have h2 : ((sh b - e : ℝ) : ℝ*) < b := by
      by_contra hle
      have hub : sh b - e ∈ upperBounds {t : ℝ | (t : ℝ*) < b} := fun t ht =>
        (Hyperreal.coe_lt_coe.1 (lt_of_lt_of_le ht (not_lt.1 hle))).le
      have := hlub.2 hub
      linarith
    rw [Hyperreal.coe_add] at h1
    rw [Hyperreal.coe_sub] at h2
    rw [abs_le]
    constructor <;> linarith
  rw [infClose_iff_abs_lt]
  intro e he
  exact (key (e / 2) (half_pos he)).trans_lt (Hyperreal.coe_lt_coe.2 (half_lt_self he))

/-- A hyperreal that is infinitely close to a real number is limited. -/
theorem limited_of_infClose_coe {c : ℝ} (h : b ≊ c) : Limited b :=
  (limited_coe c).of_infClose h.symm

/-- **Theorem 5.6.1, uniqueness.** If $`b` is infinitely close to the real number $`c` then
$`c` is the shadow of $`b`. -/
theorem sh_eq_of_infClose {c : ℝ} (h : b ≊ c) : sh b = c :=
  infClose_coe_iff.1 ((limited_of_infClose_coe h).infClose_sh.symm.trans h)

/-- **Theorem 5.6.1.** Every limited hyperreal is infinitely close to exactly one real
number. -/
theorem Limited.existsUnique_infClose (hb : Limited b) : ∃! c : ℝ, b ≊ c :=
  ⟨sh b, hb.infClose_sh, fun _ hc => (sh_eq_of_infClose hc).symm⟩

/-- **Theorem 5.6.1, converse.** A hyperreal is limited exactly when it is infinitely close to
some real number. -/
theorem limited_iff_exists_infClose_coe : Limited b ↔ ∃ c : ℝ, b ≊ c :=
  ⟨fun h => ⟨sh b, h.infClose_sh⟩, fun ⟨_, h⟩ => limited_of_infClose_coe h⟩

/-- For limited $`b`, a real number is the shadow of $`b` exactly when it is infinitely close
to $`b`. -/
theorem Limited.sh_eq_iff (hb : Limited b) {c : ℝ} : sh b = c ↔ b ≊ c :=
  ⟨fun h => h ▸ hb.infClose_sh, sh_eq_of_infClose⟩

/-- The shadow of a real number is itself. -/
@[simp]
theorem sh_coe (r : ℝ) : sh (r : ℝ*) = r := sh_eq_of_infClose (InfClose.refl _)

@[simp] theorem sh_zero : sh 0 = 0 := sh_coe 0

@[simp] theorem sh_one : sh 1 = 1 := by
  simpa using sh_coe 1

@[simp] theorem sh_natCast (n : ℕ) : sh (n : ℝ*) = n := sh_coe n

@[simp] theorem sh_intCast (n : ℤ) : sh (n : ℝ*) = n := sh_coe n

/-- The shadow of an infinitesimal is $`0`. -/
theorem Infinitesimal.sh_eq_zero (h : Infinitesimal b) : sh b = 0 :=
  sh_eq_of_infClose (by simpa using infinitesimal_iff_infClose_zero.1 h)

/-- **Section 5.6.** A limited hyperreal is infinitesimal exactly when its shadow is $`0`. -/
theorem Limited.sh_eq_zero_iff (hb : Limited b) : sh b = 0 ↔ Infinitesimal b := by
  rw [hb.sh_eq_iff, Hyperreal.coe_zero, ← infinitesimal_iff_infClose_zero]

/-- **Section 5.6.** A limited hyperreal is appreciable exactly when its shadow is not
$`0`. -/
theorem Limited.appreciable_iff_sh_ne_zero (hb : Limited b) : Appreciable b ↔ sh b ≠ 0 := by
  rw [Ne, hb.sh_eq_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩

/-- By convention the shadow of an unlimited hyperreal is $`0`. -/
theorem sh_of_unlimited (h : Unlimited b) : sh b = 0 := by
  rcases h with h | h
  · have : {r : ℝ | (r : ℝ*) < b} = univ := eq_univ_of_forall h
    rw [sh, this, Real.sSup_univ]
  · have : {r : ℝ | (r : ℝ*) < b} = ∅ := eq_empty_of_forall_notMem fun r hr => lt_asymm hr (h r)
    rw [sh, this, Real.sSup_empty]

/-- **Section 5.6, Mathlib's formulation.** The shadow is Mathlib's standard part function on
the hyperreals. -/
theorem sh_eq_stdPart (b : ℝ*) : sh b = ArchimedeanClass.stdPart b := by
  rcases limited_or_unlimited b with hb | hb
  · symm
    rw [← ArchimedeanClass.mk_sub_pos_iff Hyperreal.coeRingHom (limited_iff_mk_nonneg.1 hb)]
    exact infinitesimal_iff_mk_pos.1 hb.infClose_sh
  · rw [sh_of_unlimited hb]
    symm
    rw [ArchimedeanClass.stdPart_eq_zero]
    exact (unlimited_iff_mk_neg.1 hb).ne

/-- Two limited hyperreals are infinitely close exactly when they have the same shadow. -/
theorem infClose_iff_sh_eq (hb : Limited b) (hc : Limited c) : b ≊ c ↔ sh b = sh c :=
  ⟨fun h => sh_eq_of_infClose (h.trans hc.infClose_sh),
    fun h => hb.infClose_sh.trans (h ▸ hc.infClose_sh.symm)⟩

/-- Infinitely close limited hyperreals have the same shadow. -/
theorem InfClose.sh_eq (h : b ≊ c) (hb : Limited b) : sh b = sh c :=
  (infClose_iff_sh_eq hb (hb.of_infClose h)).1 h

/-- Adding an infinitesimal gives an infinitely close number. -/
theorem Infinitesimal.add_infClose {e : ℝ*} (he : Infinitesimal e) (b : ℝ*) : b + e ≊ b := by
  rw [infClose_iff, add_sub_cancel_left]
  exact he

/-- Adding an infinitesimal to a limited number does not change the shadow. -/
theorem sh_add_infinitesimal {e : ℝ*} (hb : Limited b) (he : Infinitesimal e) :
    sh (b + e) = sh b :=
  (he.add_infClose b).sh_eq (hb.add he.limited)

/-- **Theorem 5.6.2(1), sums.** $`\operatorname{sh}(b + c) = \operatorname{sh}(b) +
\operatorname{sh}(c)` for limited $`b, c`. -/
theorem sh_add (hb : Limited b) (hc : Limited c) : sh (b + c) = sh b + sh c := by
  apply sh_eq_of_infClose
  rw [infClose_iff, Hyperreal.coe_add]
  have := Infinitesimal.add hb.infClose_sh hc.infClose_sh
  convert this using 1
  ring

/-- **Theorem 5.6.2(1), negatives.** $`\operatorname{sh}(-b) = -\operatorname{sh}(b)`; this
holds for every hyperreal. -/
theorem sh_neg (b : ℝ*) : sh (-b) = -sh b := by
  rcases limited_or_unlimited b with hb | hb
  · apply sh_eq_of_infClose
    rw [infClose_iff, Hyperreal.coe_neg]
    have := Infinitesimal.neg hb.infClose_sh
    convert this using 1
    ring
  · rw [sh_of_unlimited hb, sh_of_unlimited hb.neg, neg_zero]

/-- **Theorem 5.6.2(1), differences.** $`\operatorname{sh}(b - c) = \operatorname{sh}(b) -
\operatorname{sh}(c)` for limited $`b, c`. -/
theorem sh_sub (hb : Limited b) (hc : Limited c) : sh (b - c) = sh b - sh c := by
  rw [sub_eq_add_neg, sh_add hb hc.neg, sh_neg, sub_eq_add_neg]

/-- **Theorem 5.6.2(2), products.** $`\operatorname{sh}(b \cdot c) = \operatorname{sh}(b)
\cdot \operatorname{sh}(c)` for limited $`b, c`. -/
theorem sh_mul (hb : Limited b) (hc : Limited c) : sh (b * c) = sh b * sh c := by
  apply sh_eq_of_infClose
  rw [infClose_iff, Hyperreal.coe_mul]
  have h1 : Infinitesimal (b * (c - sh c)) := hb.mul_infinitesimal hc.infClose_sh
  have h2 : Infinitesimal ((b - sh b) * (sh c : ℝ*)) :=
    Infinitesimal.mul_limited hb.infClose_sh (limited_coe _)
  convert h1.add h2 using 1
  ring

/-- Shadows of reciprocals: $`\operatorname{sh}(1/c) = 1/\operatorname{sh}(c)` for appreciable
$`c`. -/
theorem Appreciable.sh_inv (hc : Appreciable c) : sh c⁻¹ = (sh c)⁻¹ := by
  have hs : sh c ≠ 0 := hc.1.appreciable_iff_sh_ne_zero.1 hc
  have hs' : Appreciable ((sh c : ℝ) : ℝ*) := appreciable_coe hs
  apply sh_eq_of_infClose
  rw [infClose_iff, Hyperreal.coe_inv]
  have h1 : Infinitesimal (((sh c : ℝ) : ℝ*) - c) := (InfClose.symm hc.1.infClose_sh)
  have h2 := h1.div_appreciable (hc.mul hs')
  convert h2 using 1
  have hc0 := hc.ne_zero
  have hs0 := hs'.ne_zero
  field_simp

/-- **Theorem 5.6.2(3), quotients.** $`\operatorname{sh}(b / c) = \operatorname{sh}(b) /
\operatorname{sh}(c)` for limited $`b, c` with $`\operatorname{sh}(c) \ne 0`, that is, with
$`c` appreciable. -/
theorem sh_div (hb : Limited b) (hc : Limited c) (h : sh c ≠ 0) : sh (b / c) = sh b / sh c := by
  have hc' : Appreciable c := hc.appreciable_iff_sh_ne_zero.2 h
  rw [div_eq_mul_inv, sh_mul hb hc'.inv.limited, hc'.sh_inv, div_eq_mul_inv]

/-- **Theorem 5.6.2(4), powers.** $`\operatorname{sh}(b^n) = \operatorname{sh}(b)^n` for
limited $`b`. -/
theorem sh_pow (hb : Limited b) (n : ℕ) : sh (b ^ n) = sh b ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, sh_mul (hb.pow n) hb, ih, pow_succ]

/-- **Theorem 5.6.2(5), absolute values.** $`\operatorname{sh}(|b|) = |\operatorname{sh}(b)|`
for limited $`b`. -/
theorem sh_abs (hb : Limited b) : sh |b| = |sh b| := by
  apply sh_eq_of_infClose
  rw [infClose_iff, Hyperreal.coe_abs]
  exact Infinitesimal.of_abs_le hb.infClose_sh (abs_abs_sub_abs_le_abs_sub _ _)

/-- **Theorem 5.6.2(7), order.** If $`b \le c` are limited then
$`\operatorname{sh}(b) \le \operatorname{sh}(c)`. -/
theorem sh_le_sh (hb : Limited b) (hc : Limited c) (h : b ≤ c) : sh b ≤ sh c :=
  coe_le_coe_of_infClose_le_infClose (InfClose.symm hb.infClose_sh) h hc.infClose_sh

/-- The shadow of a nonnegative limited hyperreal is nonnegative. -/
theorem sh_nonneg (hb : Limited b) (h : 0 ≤ b) : 0 ≤ sh b := by
  simpa using sh_le_sh limited_zero hb h

/-- If a limited $`b` is at most the real $`r` then so is its shadow. -/
theorem Limited.sh_le {r : ℝ} (hb : Limited b) (h : b ≤ r) : sh b ≤ r := by
  simpa using sh_le_sh hb (limited_coe r) h

/-- If a limited $`b` is at least the real $`r` then so is its shadow. -/
theorem Limited.le_sh {r : ℝ} (hb : Limited b) (h : (r : ℝ*) ≤ b) : r ≤ sh b := by
  simpa using sh_le_sh (limited_coe r) hb h

/-- If the shadow of a limited $`b` is less than the real $`r` then $`b < r`. -/
theorem Limited.lt_of_sh_lt {r : ℝ} (hb : Limited b) (h : sh b < r) : b < r :=
  lt_of_not_ge fun hle => absurd (hb.le_sh hle) (not_le.2 h)

/-- If the real $`r` is less than the shadow of a limited $`b` then $`r < b`. -/
theorem Limited.lt_of_lt_sh {r : ℝ} (hb : Limited b) (h : r < sh b) : (r : ℝ*) < b :=
  lt_of_not_ge fun hle => absurd (hb.sh_le hle) (not_le.2 h)

/-- If the shadows of two limited hyperreals are strictly ordered then so are the numbers. -/
theorem lt_of_sh_lt_sh (hb : Limited b) (hc : Limited c) (h : sh b < sh c) : b < c :=
  lt_of_not_ge fun hle => absurd (sh_le_sh hc hb hle) (not_le.2 h)

/-- **Section 5.6.** The square root function on the hyperreals: the extension of the real
square root. -/
def hsqrt : ℝ* → ℝ* := ⋆Real.sqrt

/-- The square root of the class of a sequence is the class of the square roots. -/
theorem hsqrt_ofSeq (r : ℕ → ℝ) :
    hsqrt (Hyperreal.ofSeq r) = Hyperreal.ofSeq fun n => √(r n) := rfl

/-- On real numbers the hyperreal square root is the real one. -/
theorem hsqrt_coe (r : ℝ) : hsqrt (r : ℝ*) = ((√r : ℝ) : ℝ*) := rfl

/-- The hyperreal square root is nonnegative. -/
theorem hsqrt_nonneg (x : ℝ*) : 0 ≤ hsqrt x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  change Hyperreal.ofSeq (fun _ => 0) ≤ _
  rw [hsqrt_ofSeq, ofSeq_le_ofSeq_iff]
  exact Eventually.of_forall fun n => Real.sqrt_nonneg _

/-- The hyperreal square root of a nonnegative number squares to that number. -/
theorem hsqrt_sq (hx : 0 ≤ x) : hsqrt x ^ 2 = x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  have hx' : ∀ᶠ n in hyperfilter ℕ, 0 ≤ r n := ofSeq_le_ofSeq_iff.1 hx
  change Hyperreal.ofSeq (fun n => √(r n) ^ 2) = _
  rw [ofSeq_eq_ofSeq_iff]
  exact hx'.mono fun n hn => Real.sq_sqrt hn

/-- **Theorem 5.6.2(6), square roots.** $`\operatorname{sh}(\sqrt b) =
\sqrt{\operatorname{sh}(b)}` for limited $`b \ge 0`. -/
theorem sh_hsqrt (hb : Limited b) (h0 : 0 ≤ b) : sh (hsqrt b) = √(sh b) := by
  have hsq := hsqrt_sq h0
  have hl : Limited (hsqrt b) :=
    not_unlimited_iff_limited.1 fun hu => (hu.pow two_ne_zero).not_limited (by rwa [hsq])
  have h1 : 0 ≤ sh (hsqrt b) := sh_nonneg hl (hsqrt_nonneg b)
  have h2 : sh (hsqrt b) ^ 2 = sh b := by rw [← sh_pow hl, hsq]
  rw [← h2, Real.sqrt_sq h1]

/-- **Section 5.6.** The shadow map as a ring homomorphism from the ring $`\mathbb L` of
limited hyperreals to the reals. -/
def shadowHom : limitedSubring →+* ℝ where
  toFun x := sh (x : ℝ*)
  map_zero' := sh_zero
  map_one' := sh_one
  map_add' x y := sh_add (limitedSubring.limited x) (limitedSubring.limited y)
  map_mul' x y := sh_mul (limitedSubring.limited x) (limitedSubring.limited y)

@[simp] theorem shadowHom_apply (x : limitedSubring) : shadowHom x = sh (x : ℝ*) := rfl

/-- **Section 5.6.** The shadow map is order-preserving on the limited numbers. -/
theorem shadowHom_monotone : Monotone shadowHom := fun x y h =>
  sh_le_sh (limitedSubring.limited x) (limitedSubring.limited y) h

/-- **Section 5.6.** The shadow map sends the limited numbers onto the reals. -/
theorem shadowHom_surjective : Function.Surjective shadowHom := fun r =>
  ⟨⟨r, limited_coe r⟩, sh_coe r⟩

/-- **Section 5.6.** The kernel of the shadow map is the ideal of infinitesimals. -/
theorem ker_shadowHom : RingHom.ker shadowHom = infinitesimalIdeal := by
  ext x
  rw [RingHom.mem_ker, shadowHom_apply, (limitedSubring.limited x).sh_eq_zero_iff,
    mem_infinitesimalIdeal]

/-- **Section 5.6.** The cosets of the ideal of infinitesimals are the halos: two limited
numbers have the same class modulo the infinitesimals exactly when one lies in the halo of the
other. -/
theorem quotient_mk_eq_iff_mem_hal {x y : limitedSubring} :
    Ideal.Quotient.mk infinitesimalIdeal x = Ideal.Quotient.mk infinitesimalIdeal y ↔
      (y : ℝ*) ∈ hal (x : ℝ*) := by
  rw [Ideal.Quotient.eq, mem_infinitesimalIdeal, mem_hal]
  rfl

/-- **Theorem 5.6.3.** The quotient ring $`\mathbb L / \mathbb I` of the limited hyperreals by
the infinitesimals is isomorphic to the field of real numbers; the isomorphism sends the
class of $`b`, which is the halo of $`b`, to the shadow of $`b`. -/
def limitedQuotientEquiv : limitedSubring ⧸ infinitesimalIdeal ≃+* ℝ :=
  RingEquiv.ofBijective
    (Ideal.Quotient.lift infinitesimalIdeal shadowHom fun x hx =>
      ((limitedSubring.limited x).sh_eq_zero_iff).2 hx)
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro q
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
      intro hx
      change sh (x : ℝ*) = 0 at hx
      exact Ideal.Quotient.eq_zero_iff_mem.2 (((limitedSubring.limited x).sh_eq_zero_iff).1 hx),
    fun r => ⟨Ideal.Quotient.mk _ ⟨r, limited_coe r⟩, sh_coe r⟩⟩

/-- **Theorem 5.6.3.** The isomorphism $`\mathbb L / \mathbb I \cong \mathbb R` sends the
class of $`b` to $`\operatorname{sh}(b)`. -/
@[simp]
theorem limitedQuotientEquiv_mk (x : limitedSubring) :
    limitedQuotientEquiv (Ideal.Quotient.mk infinitesimalIdeal x) = sh (x : ℝ*) := rfl

/-- **Theorem 5.6.3.** The infinitesimals are a maximal ideal of the ring of limited
hyperreals. -/
theorem infinitesimalIdeal_isMaximal : infinitesimalIdeal.IsMaximal := by
  rw [← ker_shadowHom]
  exact RingHom.ker_isMaximal_of_surjective shadowHom shadowHom_surjective

end Shadows

/-!
## 5.7 Exercises on Infinite Closeness

Infinite closeness is preserved by sums, differences, products and, away from the
infinitesimals, quotients of limited numbers. The extensions of the trigonometric functions
take infinitesimals to the values the calculus leads one to expect; the proofs transfer
elementary inequalities of real trigonometry. Every hyperreal is infinitely close to a
hyperrational, and so the real field is also the quotient of the limited hyperrationals by the
infinitesimal hyperrationals.
-/

section InfCloseExercises

variable {b b' c c' x y e : ℝ*}

/-- **Exercise 5.7(1), sums.** If $`b \simeq b'` and $`c \simeq c'` then
$`b + c \simeq b' + c'`. (Limitedness is not needed for this part.) -/
theorem InfClose.add (hb : b ≊ b') (hc : c ≊ c') : b + c ≊ b' + c' := by
  rw [infClose_iff] at *
  convert Infinitesimal.add hb hc using 1
  ring

/-- If $`b \simeq b'` then $`-b \simeq -b'`. -/
theorem InfClose.neg (hb : b ≊ b') : -b ≊ -b' := by
  rw [infClose_iff] at *
  convert Infinitesimal.neg hb using 1
  ring

/-- **Exercise 5.7(1), differences.** If $`b \simeq b'` and $`c \simeq c'` then
$`b - c \simeq b' - c'`. -/
theorem InfClose.sub (hb : b ≊ b') (hc : c ≊ c') : b - c ≊ b' - c' := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact hb.add hc.neg

/-- **Exercise 5.7(1), products.** If $`b, c` are limited, $`b \simeq b'` and
$`c \simeq c'`, then $`b \cdot c \simeq b' \cdot c'`. -/
theorem InfClose.mul (hb : b ≊ b') (hc : c ≊ c') (hbl : Limited b) (hcl : Limited c) :
    b * c ≊ b' * c' := by
  have hc'l : Limited c' := hcl.of_infClose hc
  rw [infClose_iff] at *
  convert (hbl.mul_infinitesimal hc).add (hb.mul_limited hc'l) using 1
  ring

/-- If $`c \simeq c'` and $`c` is appreciable then $`c'` is appreciable. -/
theorem Appreciable.of_infClose (hc : Appreciable c) (h : c ≊ c') : Appreciable c' := by
  have := hc.add_infinitesimal (InfClose.symm h)
  simpa using this

/-- If $`c` is appreciable and $`c \simeq c'` then $`1/c \simeq 1/c'`. -/
theorem InfClose.inv (hc : c ≊ c') (hca : Appreciable c) : c⁻¹ ≊ c'⁻¹ := by
  have hc'a : Appreciable c' := hca.of_infClose hc
  have h := (InfClose.symm hc).div_appreciable (hca.mul hc'a)
  rw [infClose_iff] at *
  convert h using 1
  have h1 := hca.ne_zero
  have h2 := hc'a.ne_zero
  field_simp

/-- **Exercise 5.7(1), quotients.** If $`b, c` are limited, $`b \simeq b'`,
$`c \simeq c'` and $`c \not\simeq 0`, then $`b / c \simeq b' / c'`. -/
theorem InfClose.div (hb : b ≊ b') (hc : c ≊ c') (hbl : Limited b) (hcl : Limited c)
    (hc0 : ¬ c ≊ 0) : b / c ≊ b' / c' := by
  have hca : Appreciable c := ⟨hcl, fun h => hc0 (infinitesimal_iff_infClose_zero.1 h)⟩
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact hb.mul (hc.inv hca) hbl hca.inv.limited

/-- **Exercise 5.7(1), failure when the denominator is infinitesimal.** With $`b = b' = 1`,
$`c = \varepsilon` and $`c' = 2\varepsilon` all hypotheses of the quotient rule hold except
$`c \not\simeq 0`, and $`b/c - b'/c' = \omega/2` is unlimited. -/
theorem exists_infClose_div_not_infClose :
    ∃ b b' c c' : ℝ*, Limited b ∧ Limited c ∧ b ≊ b' ∧ c ≊ c' ∧ c ≠ 0 ∧ c' ≠ 0 ∧
      ¬ b / c ≊ b' / c' := by
  have h0 : (ε : ℝ*) ≠ 0 := Hyperreal.epsilon_ne_zero
  have h2 : Infinitesimal ((2 : ℝ*) * ε) :=
    (limited_coe 2).mul_infinitesimal infinitesimal_epsilon
  refine ⟨1, 1, ε, 2 * ε, limited_one, infinitesimal_epsilon.limited, InfClose.refl 1, ?_, h0,
    mul_ne_zero two_ne_zero h0, ?_⟩
  · rw [infClose_iff]
    exact infinitesimal_epsilon.sub h2
  · rw [infClose_iff]
    have : (1 : ℝ*) / ε - 1 / (2 * ε) = ω * ((1 / 2 : ℝ) : ℝ*) := by
      rw [← Hyperreal.inv_epsilon, Hyperreal.coe_div, Hyperreal.coe_one, Hyperreal.coe_ofNat]
      field_simp
      ring
    rw [this]
    exact (unlimited_omega.mul_appreciable (appreciable_coe (by norm_num))).not_infinitesimal

/-- **Exercise 5.7(2).** The extension of the sine function to the hyperreals. -/
def hsin : ℝ* → ℝ* := ⋆Real.sin

/-- **Exercise 5.7(2).** The extension of the cosine function to the hyperreals. -/
def hcos : ℝ* → ℝ* := ⋆Real.cos

/-- **Exercise 5.7(2).** The extension of the tangent function to the hyperreals. -/
def htan : ℝ* → ℝ* := ⋆Real.tan

theorem hsin_ofSeq (r : ℕ → ℝ) :
    hsin (Hyperreal.ofSeq r) = Hyperreal.ofSeq fun n => Real.sin (r n) := rfl

theorem hcos_ofSeq (r : ℕ → ℝ) :
    hcos (Hyperreal.ofSeq r) = Hyperreal.ofSeq fun n => Real.cos (r n) := rfl

theorem htan_ofSeq (r : ℕ → ℝ) :
    htan (Hyperreal.ofSeq r) = Hyperreal.ofSeq fun n => Real.tan (r n) := rfl

@[simp] theorem hsin_coe (r : ℝ) : hsin (r : ℝ*) = ((Real.sin r : ℝ) : ℝ*) := rfl

@[simp] theorem hcos_coe (r : ℝ) : hcos (r : ℝ*) = ((Real.cos r : ℝ) : ℝ*) := rfl

@[simp] theorem htan_coe (r : ℝ) : htan (r : ℝ*) = ((Real.tan r : ℝ) : ℝ*) := rfl

/-- **Exercise 5.7(2), transferred inequality.** $`|\sin x| \le |x|` for every hyperreal
$`x`. -/
theorem abs_hsin_le (x : ℝ*) : |hsin x| ≤ |x| := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  change Hyperreal.ofSeq (fun n => |Real.sin (r n)|) ≤ Hyperreal.ofSeq (fun n => |r n|)
  rw [ofSeq_le_ofSeq_iff]
  exact Eventually.of_forall fun n => by
    simpa using Real.abs_sin_sub_sin_le (r n) 0

/-- **Exercise 5.7(2), transferred inequality.** $`|\cos x - 1| \le x^2/2` for every
hyperreal $`x`. -/
theorem abs_hcos_sub_one_le (x : ℝ*) : |hcos x - 1| ≤ x ^ 2 / 2 := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  change Hyperreal.ofSeq (fun n => |Real.cos (r n) - 1|) ≤
    Hyperreal.ofSeq (fun n => r n ^ 2 / 2)
  rw [ofSeq_le_ofSeq_iff]
  exact Eventually.of_forall fun n => by
    rw [abs_le]
    constructor <;> linarith [Real.one_sub_sq_div_two_le_cos (x := r n), Real.cos_le_one (r n),
      sq_nonneg (r n)]

/-- **Exercise 5.7(2), transferred identity.** $`\tan x = \sin x / \cos x` for every
hyperreal $`x`. -/
theorem htan_eq_hsin_div_hcos (x : ℝ*) : htan x = hsin x / hcos x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  change Hyperreal.ofSeq (fun n => Real.tan (r n)) =
    Hyperreal.ofSeq (fun n => Real.sin (r n) / Real.cos (r n))
  rw [ofSeq_eq_ofSeq_iff]
  exact Eventually.of_forall fun n => Real.tan_eq_sin_div_cos _

/-- **Exercise 5.7(2), transferred inequality.** $`|x - \sin x| \le |x|^3/6` for every
hyperreal $`x`. -/
theorem abs_sub_hsin_le (x : ℝ*) : |x - hsin x| ≤ |x| ^ 3 / 6 := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  change Hyperreal.ofSeq (fun n => |r n - Real.sin (r n)|) ≤
    Hyperreal.ofSeq (fun n => |r n| ^ 3 / 6)
  rw [ofSeq_le_ofSeq_iff]
  exact Eventually.of_forall fun n => Real.abs_sub_sin_le _

/-- **Exercise 5.7(2).** If $`\varepsilon` is infinitesimal then
$`\sin \varepsilon \simeq 0`. -/
theorem Infinitesimal.hsin_infClose (he : Infinitesimal e) : hsin e ≊ 0 :=
  infinitesimal_iff_infClose_zero.1 (he.of_abs_le (abs_hsin_le e))

/-- **Exercise 5.7(2).** If $`\varepsilon` is infinitesimal then
$`\cos \varepsilon \simeq 1`. -/
theorem Infinitesimal.hcos_infClose (he : Infinitesimal e) : hcos e ≊ 1 := by
  have h : Infinitesimal (e ^ 2 / 2) := by
    have := (he.pow two_ne_zero).mul_limited (limited_coe (1 / 2))
    convert this using 1
    rw [Hyperreal.coe_div, Hyperreal.coe_one, Hyperreal.coe_ofNat]
    ring
  refine h.of_abs_le ((abs_hcos_sub_one_le e).trans (le_abs_self _))

/-- **Exercise 5.7(2).** If $`\varepsilon` is infinitesimal then
$`\tan \varepsilon \simeq 0`. -/
theorem Infinitesimal.htan_infClose (he : Infinitesimal e) : htan e ≊ 0 := by
  rw [htan_eq_hsin_div_hcos, ← infinitesimal_iff_infClose_zero]
  have hcos : Appreciable (hcos e) :=
    appreciable_one.of_infClose (InfClose.symm he.hcos_infClose)
  exact (infinitesimal_iff_infClose_zero.2 he.hsin_infClose).div_appreciable hcos

/-- **Exercise 5.7(2).** If $`\varepsilon \ne 0` is infinitesimal then
$`\sin \varepsilon / \varepsilon \simeq 1`. -/
theorem Infinitesimal.hsin_div_infClose (he : Infinitesimal e) (h0 : e ≠ 0) :
    hsin e / e ≊ 1 := by
  rw [infClose_iff]
  have h : Infinitesimal (e ^ 2 / 6) := by
    have := (he.pow two_ne_zero).mul_limited (limited_coe (1 / 6))
    convert this using 1
    rw [Hyperreal.coe_div, Hyperreal.coe_one, Hyperreal.coe_ofNat]
    ring
  refine h.of_abs_le ?_
  have h1 : hsin e / e - 1 = -((e - hsin e) / e) := by
    field_simp
    ring
  have he0 : 0 < |e| := abs_pos.2 h0
  rw [h1, abs_neg, abs_div, div_le_iff₀ he0]
  refine (abs_sub_hsin_le e).trans (le_of_eq ?_)
  rw [abs_of_nonneg (by positivity : (0 : ℝ*) ≤ e ^ 2 / 6), ← sq_abs e]
  ring

/-- **Exercise 5.7(2).** If $`\varepsilon` is infinitesimal then
$`(\cos \varepsilon - 1)/\varepsilon \simeq 0`. (For $`\varepsilon = 0` the quotient is
$`0` by Lean's convention on division by zero.) -/
theorem Infinitesimal.hcos_sub_one_div_infClose (he : Infinitesimal e) :
    (hcos e - 1) / e ≊ 0 := by
  rw [← infinitesimal_iff_infClose_zero]
  rcases eq_or_ne e 0 with rfl | h0
  · simp
  have h : Infinitesimal (e / 2) := by
    have := he.mul_limited (limited_coe (1 / 2))
    convert this using 1
    rw [Hyperreal.coe_div, Hyperreal.coe_one, Hyperreal.coe_ofNat]
    ring
  refine h.of_abs_le ?_
  have he0 : 0 < |e| := abs_pos.2 h0
  rw [abs_div, div_le_iff₀ he0]
  refine (abs_hcos_sub_one_le e).trans (le_of_eq ?_)
  rw [abs_div, ← sq_abs e, abs_of_pos (two_pos : (0 : ℝ*) < 2)]
  ring

/-- **Exercise 5.7(3).** Every hyperreal is infinitely close to some hyperrational number. -/
theorem exists_hyperRat_infClose (x : ℝ*) : ∃ q ∈ ℚ*, x ≊ q := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  have hq : ∀ n : ℕ, ∃ q : ℚ, |r n - q| < 1 / ((n : ℝ) + 1) := fun n => by
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show r n < r n + 1 / ((n : ℝ) + 1) by linarith)
    exact ⟨q, by rw [abs_lt]; constructor <;> linarith⟩
  choose q hq using hq
  refine ⟨Hyperreal.ofSeq fun n => (q n : ℝ), mem_hyperRat_iff.2 ⟨q, rfl⟩, ?_⟩
  rw [infClose_iff_abs_lt]
  intro e he
  have ht : Tendsto (fun n => r n - q n) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact (hq n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact abs_ofSeq_lt_of_tendsto_zero (s := fun n => r n - q n) ht he

/-- **Exercise 5.7(4).** The ring $`{}^*\mathbb Q \cap \mathbb L` of limited
hyperrationals. -/
def limitedHyperRat : Subring ℝ* := hyperRatSubfield.toSubring ⊓ limitedSubring

theorem mem_limitedHyperRat {x : ℝ*} : x ∈ limitedHyperRat ↔ x ∈ ℚ* ∧ Limited x := Iff.rfl

/-- **Exercise 5.7(4).** The underlying set of the ring of limited hyperrationals is
$`{}^*\mathbb Q \cap \mathbb L`. -/
theorem coe_limitedHyperRat : (limitedHyperRat : Set ℝ*) = ℚ* ∩ 𝕃 := rfl

/-- Every member of the ring of limited hyperrationals is limited. -/
theorem limitedHyperRat.limited (x : limitedHyperRat) : Limited (x : ℝ*) := x.2.2

/-- Every member of the ring of limited hyperrationals is hyperrational. -/
theorem limitedHyperRat.mem_hyperRat (x : limitedHyperRat) : (x : ℝ*) ∈ ℚ* := x.2.1

/-- **Exercise 5.7(4).** The ideal $`{}^*\mathbb Q \cap \mathbb I` of infinitesimal
hyperrationals in the ring of limited hyperrationals. -/
def infinitesimalHyperRat : Ideal limitedHyperRat where
  carrier := {x | Infinitesimal (x : ℝ*)}
  zero_mem' := infinitesimal_zero
  add_mem' := fun ha hb => Infinitesimal.add ha hb
  smul_mem' := fun c _ hx => (limitedHyperRat.limited c).mul_infinitesimal hx

@[simp] theorem mem_infinitesimalHyperRat {x : limitedHyperRat} :
    x ∈ infinitesimalHyperRat ↔ Infinitesimal (x : ℝ*) := Iff.rfl

/-- **Exercise 5.7(4).** The members of the ideal of infinitesimal hyperrationals are exactly
the members of $`{}^*\mathbb Q \cap \mathbb I`. -/
theorem image_infinitesimalHyperRat :
    (fun x : limitedHyperRat => (x : ℝ*)) '' (infinitesimalHyperRat : Set limitedHyperRat) =
      ℚ* ∩ 𝕀 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨limitedHyperRat.mem_hyperRat y, hy⟩
  · rintro ⟨hq, hi⟩
    exact ⟨⟨x, hq, Infinitesimal.limited hi⟩, hi, rfl⟩

/-- **Exercise 5.7(4).** The shadow map restricted to the limited hyperrationals. -/
def shadowHomRat : limitedHyperRat →+* ℝ where
  toFun x := sh (x : ℝ*)
  map_zero' := sh_zero
  map_one' := sh_one
  map_add' x y := sh_add (limitedHyperRat.limited x) (limitedHyperRat.limited y)
  map_mul' x y := sh_mul (limitedHyperRat.limited x) (limitedHyperRat.limited y)

/-- **Exercise 5.7(4).** Every real number is the shadow of a limited hyperrational. -/
theorem shadowHomRat_surjective : Function.Surjective shadowHomRat := fun r => by
  obtain ⟨q, hq, h⟩ := exists_hyperRat_infClose (r : ℝ*)
  exact ⟨⟨q, hq, (limited_coe r).of_infClose h⟩, sh_eq_of_infClose (InfClose.symm h)⟩

/-- **Exercise 5.7(4).** The real field is isomorphic to the ring
$`{}^*\mathbb Q \cap \mathbb L` of limited hyperrationals factored by its ideal
$`{}^*\mathbb Q \cap \mathbb I` of hyperrational infinitesimals; the isomorphism sends the
class of $`q` to its shadow. -/
def limitedHyperRatQuotientEquiv : limitedHyperRat ⧸ infinitesimalHyperRat ≃+* ℝ :=
  RingEquiv.ofBijective
    (Ideal.Quotient.lift infinitesimalHyperRat shadowHomRat fun x hx =>
      ((limitedHyperRat.limited x).sh_eq_zero_iff).2 hx)
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro q
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
      intro hx
      change sh (x : ℝ*) = 0 at hx
      exact Ideal.Quotient.eq_zero_iff_mem.2
        (((limitedHyperRat.limited x).sh_eq_zero_iff).1 hx),
    fun r => by
      obtain ⟨x, hx⟩ := shadowHomRat_surjective r
      exact ⟨Ideal.Quotient.mk _ x, hx⟩⟩

/-- **Exercise 5.7(4).** The isomorphism sends the class of a limited hyperrational to its
shadow. -/
@[simp]
theorem limitedHyperRatQuotientEquiv_mk (x : limitedHyperRat) :
    limitedHyperRatQuotientEquiv (Ideal.Quotient.mk infinitesimalHyperRat x) = sh (x : ℝ*) :=
  rfl

end InfCloseExercises

/-!
## 5.8 Shadows and Completeness

The existence of shadows was derived from the completeness of the reals. The book now shows
the converse: completeness follows from the assertion that every limited hyperreal is
infinitely close to a real number.

Stated for the real numbers of Lean, which are complete, such an implication would have no
content. To make the theorem say something we state it for an arbitrary ordered field $`F`.
The ultrapower of $`F` over the index ultrafilter is again an ordered field containing $`F`,
and the _shadow property_ of $`F` is the assertion that every element of this ultrapower lying
between two elements of $`F` is infinitely close to an element of $`F`. Theorem 5.8.1 then
says: an ordered field with the shadow property is Cauchy complete. The proof is the book's
nonstandard argument, word for word; the value of the extended sequence at the unlimited
hypernatural represented by the identity sequence is simply the class of the sequence itself.
For the field of real numbers the statement specializes to the book's.
-/

section Completeness

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- **Section 5.8.** The _shadow property_ of an ordered field $`F`: every element of the
ultrapower of $`F` that lies between two elements of $`F` (a limited element) is infinitely
close to an element $`c` of $`F`, in the sense that its distance from $`c` is smaller than
every positive element of $`F`. For the reals this is the assertion "every limited hyperreal
is infinitely close to a real number". -/
def ShadowProperty (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] : Prop :=
  ∀ b : Ultrapower F, (∃ r s : F, (r : Ultrapower F) < b ∧ b < (s : Ultrapower F)) →
    ∃ c : F, ∀ e : F, 0 < e → |b - (c : Ultrapower F)| < (e : Ultrapower F)

omit [Field F] [IsStrictOrderedRing F] in
/-- A constant is below the class of a sequence exactly when it is below almost all terms. -/
theorem Ultrapower.const_lt_coe {a : F} {s : ℕ → F} :
    ((a : F) : Ultrapower F) < (s : Ultrapower F) ↔ ∀ᶠ n in hyperfilter ℕ, a < s n :=
  Germ.coe_lt (f := fun _ => a)

omit [Field F] [IsStrictOrderedRing F] in
/-- The class of a sequence is below a constant exactly when almost all terms are. -/
theorem Ultrapower.coe_lt_const {a : F} {s : ℕ → F} :
    (s : Ultrapower F) < ((a : F) : Ultrapower F) ↔ ∀ᶠ n in hyperfilter ℕ, s n < a :=
  Germ.coe_lt (g := fun _ => a)

omit [IsStrictOrderedRing F] in
/-- The distance from the class of a sequence to a constant is below a constant exactly when
this holds for almost all terms. -/
theorem Ultrapower.abs_coe_sub_const_lt {a e : F} {s : ℕ → F} :
    |(s : Ultrapower F) - (a : Ultrapower F)| < (e : Ultrapower F) ↔
      ∀ᶠ n in hyperfilter ℕ, |s n - a| < e :=
  Germ.coe_lt (f := fun n => |s n - a|) (g := fun _ => e)

/-- **Theorem 5.8.1.** In an ordered field with the shadow property every Cauchy sequence
converges. The proof follows the book: the class $`[s]` of a Cauchy sequence $`s` (the value
$`s_N` of the extended sequence at the unlimited hypernatural $`N = [1, 2, 3, \dots]`) is
limited, hence infinitely close to some $`L` in the field, and $`s` converges to $`L`. -/
theorem cauchy_converges_of_shadowProperty (h : ShadowProperty F) {s : ℕ → F}
    (hs : IsCauSeq abs s) : ∃ L : F, ∀ e > 0, ∃ j, ∀ m ≥ j, |s m - L| < e := by
  -- the class of `s` is limited
  obtain ⟨k, hk⟩ := hs.cauchy₂ one_pos
  have hlim : ∃ r t : F, (r : Ultrapower F) < (s : Ultrapower F) ∧
      (s : Ultrapower F) < (t : Ultrapower F) := by
    refine ⟨s k - 1, s k + 1, Ultrapower.const_lt_coe.2 ?_, Ultrapower.coe_lt_const.2 ?_⟩
    · refine eventually_hyperfilter_of_eventually_atTop ?_
      filter_upwards [eventually_ge_atTop k] with n hn
      have := (abs_lt.1 (hk n hn k le_rfl)).1
      linarith
    · refine eventually_hyperfilter_of_eventually_atTop ?_
      filter_upwards [eventually_ge_atTop k] with n hn
      have := (abs_lt.1 (hk n hn k le_rfl)).2
      linarith
  -- so it has a shadow `L`
  obtain ⟨L, hL⟩ := h _ hlim
  refine ⟨L, fun e he => ?_⟩
  -- beyond `j` all terms are within `e / 2` of each other, hence within `e` of `L`
  obtain ⟨j, hj⟩ := hs.cauchy₂ (half_pos he)
  refine ⟨j, fun m hm => ?_⟩
  have h1 : ∀ᶠ n in hyperfilter ℕ, |s n - L| < e / 2 :=
    Ultrapower.abs_coe_sub_const_lt.1 (hL _ (half_pos he))
  have h2 : ∀ᶠ n in hyperfilter ℕ, j ≤ n :=
    eventually_hyperfilter_of_eventually_atTop (eventually_ge_atTop j)
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  have h3 := hj m hm n hn2
  calc |s m - L| = |(s m - s n) + (s n - L)| := by ring_nf
    _ ≤ |s m - s n| + |s n - L| := abs_add_le _ _
    _ < e / 2 + e / 2 := add_lt_add h3 hn1
    _ = e := add_halves e

/-- **Theorem 5.8.1, in Mathlib's vocabulary.** An ordered field with the shadow property is
complete as a field with absolute value: every Cauchy sequence has a limit. -/
theorem cauSeq_isComplete_of_shadowProperty (h : ShadowProperty F) :
    CauSeq.IsComplete F abs :=
  ⟨fun s => by
    obtain ⟨L, hL⟩ := cauchy_converges_of_shadowProperty h s.2
    exact ⟨L, hL⟩⟩

/-- **Theorem 5.6.1, for an ordered field.** The book's proof of the existence of shadows
uses only the least upper bound property, so it shows that every Dedekind complete ordered
field has the shadow property. -/
theorem shadowProperty_of_exists_isLUB
    (hF : ∀ A : Set F, A.Nonempty → BddAbove A → ∃ c, IsLUB A c) : ShadowProperty F := by
  rintro b ⟨r, s, hr, hs⟩
  obtain ⟨c, hlub⟩ := hF {t : F | (t : Ultrapower F) < b} ⟨r, hr⟩
    ⟨s, fun t ht => (Germ.const_lt_iff.1 (lt_trans ht hs)).le⟩
  refine ⟨c, fun e he => ?_⟩
  have h1 : b ≤ ((c + e / 2 : F) : Ultrapower F) := by
    by_contra hlt
    have := hlub.1 (show c + e / 2 ∈ {t : F | (t : Ultrapower F) < b} from not_le.1 hlt)
    linarith [half_pos he]
  have h2 : ((c - e / 2 : F) : Ultrapower F) < b := by
    by_contra hle
    have hub : c - e / 2 ∈ upperBounds {t : F | (t : Ultrapower F) < b} := fun t ht =>
      (Germ.const_lt_iff.1 (lt_of_lt_of_le ht (not_lt.1 hle))).le
    have := hlub.2 hub
    linarith [half_pos he]
  have h3 : ((e / 2 : F) : Ultrapower F) < (e : Ultrapower F) :=
    Germ.const_lt_iff.2 (half_lt_self he)
  have e1 : ((c + e / 2 : F) : Ultrapower F) = (c : Ultrapower F) + ((e / 2 : F) : Ultrapower F) :=
    rfl
  have e2 : ((c - e / 2 : F) : Ultrapower F) = (c : Ultrapower F) - ((e / 2 : F) : Ultrapower F) :=
    rfl
  rw [e1] at h1
  rw [e2] at h2
  rw [abs_lt]
  constructor <;> linarith

/-- **Theorem 5.6.1, in the language of Section 5.8.** The real numbers have the shadow
property. -/
theorem shadowProperty_real : ShadowProperty ℝ := fun b hb =>
  ⟨sh b, infClose_iff_abs_lt.1 (Limited.infClose_sh hb)⟩

/-- **Theorem 5.8.1, the book's statement.** The assertion "every limited hyperreal is
infinitely close to a real number" implies that every Cauchy sequence of real numbers
converges. The proof goes through the nonstandard argument of
{name}`cauchy_converges_of_shadowProperty` and uses the hypothesis, not the completeness of
the real numbers built into Mathlib. -/
theorem real_cauchy_converges_of_shadows
    (h : ∀ b : ℝ*, Limited b → ∃ c : ℝ, b ≊ c) {s : ℕ → ℝ} (hs : IsCauSeq abs s) :
    ∃ L : ℝ, Tendsto s atTop (𝓝 L) := by
  have hF : ShadowProperty ℝ := fun b hb => by
    obtain ⟨c, hc⟩ := h b hb
    exact ⟨c, infClose_iff_abs_lt.1 hc⟩
  obtain ⟨L, hL⟩ := cauchy_converges_of_shadowProperty hF hs
  refine ⟨L, Metric.tendsto_atTop.2 fun e he => ?_⟩
  obtain ⟨j, hj⟩ := hL e he
  exact ⟨j, fun m hm => by rw [Real.dist_eq]; exact hj m hm⟩

end Completeness

/-!
## 5.9 Exercise on Dedekind Completeness

The exercise replaces Cauchy sequences by a direct proof of the least upper bound property
from the shadow property. Given a nonempty set $`A` that is bounded above, let $`s_n` be the
least integer $`k` such that $`k/n` is an upper bound of $`A`; then the shadow of
$`s_N / N` for an unlimited $`N` is the least upper bound of $`A`. The existence of $`s_n`
uses the Archimedean property, which holds for the reals and is assumed of the field here.
Together with the previous section this shows that for an Archimedean ordered field the shadow
property is equivalent to Dedekind completeness.
-/

section Dedekind

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- **Exercise 5.9(a).** In an Archimedean ordered field, if $`A` is nonempty and bounded
above then for each positive natural $`n` there is a least integer $`k` such that $`k/n` is an
upper bound of $`A`. -/
theorem exists_least_int_div_mem_upperBounds [Archimedean F] {A : Set F} (hne : A.Nonempty)
    (hbdd : BddAbove A) {n : ℕ} (hn : 0 < n) :
    ∃ k : ℤ, (k : F) / n ∈ upperBounds A ∧ ∀ j : ℤ, (j : F) / n ∈ upperBounds A → k ≤ j := by
  have hn' : (0 : F) < n := by exact_mod_cast hn
  obtain ⟨a, ha⟩ := hne
  obtain ⟨u, hu⟩ := hbdd
  refine Int.exists_least_of_bdd ?_ ?_
  · obtain ⟨m, hm⟩ := exists_int_le (a * n)
    refine ⟨m, fun z hz => ?_⟩
    have h1 : a ≤ (z : F) / n := hz ha
    rw [le_div_iff₀ hn'] at h1
    exact_mod_cast hm.trans h1
  · obtain ⟨k, hk⟩ := exists_int_ge (u * n)
    refine ⟨k, fun x hx => ?_⟩
    rw [le_div_iff₀ hn']
    exact (mul_le_mul_of_nonneg_right (hu hx) hn'.le).trans hk

/-- **Exercise 5.9(b), (c).** An Archimedean ordered field with the shadow property has the
least upper bound property: every nonempty subset that is bounded above has a least upper
bound. With $`s_n` the least integer such that $`s_n/n` bounds $`A` above, the class of the
sequence $`s_n/n` is limited, and the element of the field infinitely close to it is the least
upper bound. -/
theorem exists_isLUB_of_shadowProperty [Archimedean F] (h : ShadowProperty F) {A : Set F}
    (hne : A.Nonempty) (hbdd : BddAbove A) : ∃ c, IsLUB A c := by
  -- the sequence `s`, indexed so that the `n`-th term uses the denominator `n + 1`
  have hex : ∀ n : ℕ, ∃ k : ℤ, (k : F) / ((n + 1 : ℕ) : F) ∈ upperBounds A ∧
      ∀ j : ℤ, (j : F) / ((n + 1 : ℕ) : F) ∈ upperBounds A → k ≤ j :=
    fun n => exists_least_int_div_mem_upperBounds hne hbdd n.succ_pos
  choose s hs hmin using hex
  have hpos : ∀ n : ℕ, (0 : F) < ((n + 1 : ℕ) : F) := fun n => by exact_mod_cast n.succ_pos
  -- `(s n - 1) / (n + 1)` is not an upper bound, so it lies below some member of `A`
  have hbelow : ∀ n : ℕ, ∃ a ∈ A, ((s n : F) - 1) / ((n + 1 : ℕ) : F) < a := by
    intro n
    by_contra hcon
    push Not at hcon
    have hub : (((s n - 1 : ℤ) : F)) / ((n + 1 : ℕ) : F) ∈ upperBounds A := fun a ha => by
      have := hcon a ha
      rw [Int.cast_sub, Int.cast_one]
      exact this
    have := hmin n _ hub
    omega
  obtain ⟨a, ha⟩ := hne
  obtain ⟨u, hu⟩ := hbdd
  let x : ℕ → F := fun n => (s n : F) / ((n + 1 : ℕ) : F)
  have hxlt : ∀ n, x n - 1 / ((n + 1 : ℕ) : F) < u := fun n => by
    obtain ⟨a', ha', hlt⟩ := hbelow n
    have : x n - 1 / ((n + 1 : ℕ) : F) = ((s n : F) - 1) / ((n + 1 : ℕ) : F) := by
      simp only [x]
      ring
    rw [this]
    exact hlt.trans_le (hu ha')
  have hone : ∀ n : ℕ, 1 / ((n + 1 : ℕ) : F) ≤ 1 := fun n => by
    rw [div_le_one (hpos n)]
    exact_mod_cast n.succ_pos
  -- (b) the class of `x` is limited
  have hlim : ∃ r t : F, (r : Ultrapower F) < (x : Ultrapower F) ∧
      (x : Ultrapower F) < (t : Ultrapower F) := by
    refine ⟨a - 1, u + 1, Ultrapower.const_lt_coe.2 (Eventually.of_forall fun n => ?_),
      Ultrapower.coe_lt_const.2 (Eventually.of_forall fun n => ?_)⟩
    · have : a ≤ x n := hs n ha
      linarith
    · have := hxlt n
      have := hone n
      linarith
  obtain ⟨L, hL⟩ := h _ hlim
  -- (c) `L` is the least upper bound
  refine ⟨L, fun a' ha' => ?_, fun u' hu' => ?_⟩
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := (Ultrapower.abs_coe_sub_const_lt.1 (hL (a' - L) (sub_pos.2 hlt))).exists
    have h1 : a' ≤ x n := hs n ha'
    have h2 := (abs_lt.1 hn).2
    linarith
  · by_contra hlt
    rw [not_le] at hlt
    have he : 0 < (L - u') / 2 := half_pos (sub_pos.2 hlt)
    have h1 : ∀ᶠ n in hyperfilter ℕ, |x n - L| < (L - u') / 2 :=
      Ultrapower.abs_coe_sub_const_lt.1 (hL _ he)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt he
    have h2 : ∀ᶠ n in hyperfilter ℕ, N ≤ n :=
      eventually_hyperfilter_of_eventually_atTop (eventually_ge_atTop N)
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    have h3 : 1 / ((n + 1 : ℕ) : F) < (L - u') / 2 := by
      refine lt_of_le_of_lt ?_ hN
      push_cast
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : F) ≤ n := by exact_mod_cast hn2
      linarith
    have h4 : x n - 1 / ((n + 1 : ℕ) : F) < u' := by
      obtain ⟨a', ha', hlt'⟩ := hbelow n
      have : x n - 1 / ((n + 1 : ℕ) : F) = ((s n : F) - 1) / ((n + 1 : ℕ) : F) := by
        simp only [x]
        ring
      rw [this]
      exact hlt'.trans_le (hu' ha')
    have h5 := (abs_lt.1 hn1).1
    linarith

/-- **Sections 5.8 and 5.9, summary.** For an Archimedean ordered field, the shadow property
is equivalent to Dedekind completeness. -/
theorem shadowProperty_iff_exists_isLUB [Archimedean F] :
    ShadowProperty F ↔ ∀ A : Set F, A.Nonempty → BddAbove A → ∃ c, IsLUB A c :=
  ⟨fun h _ hne hbdd => exists_isLUB_of_shadowProperty h hne hbdd,
    shadowProperty_of_exists_isLUB⟩

/-- **Exercise 5.9, the book's statement.** The assertion "every limited hyperreal is
infinitely close to a real number" implies that every nonempty set of real numbers with an
upper bound has a least upper bound. The proof goes through
{name}`exists_isLUB_of_shadowProperty` and uses the hypothesis, not the completeness of the
real numbers built into Mathlib. -/
theorem real_exists_isLUB_of_shadows (h : ∀ b : ℝ*, Limited b → ∃ c : ℝ, b ≊ c) {A : Set ℝ}
    (hne : A.Nonempty) (hbdd : BddAbove A) : ∃ c, IsLUB A c :=
  exists_isLUB_of_shadowProperty (fun b hb => by
    obtain ⟨c, hc⟩ := h b hb
    exact ⟨c, infClose_iff_abs_lt.1 hc⟩) hne hbdd

end Dedekind

end Goldblatt
