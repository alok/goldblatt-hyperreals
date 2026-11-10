import Mathlib
import Goldblatt.Ch02_LargeSets

/-!
# 18 (part 1). The ultrapower toolkit, the rationals, and completions

This is the first of six parts of Chapter 18 (the overview is on the chapter page
{lit}`Goldblatt.Ch18_Completion`). It fixes the nonstandard model used throughout the
chapter, proves the two principles of Part IV of the book that the chapter relies on
(countable saturation, and the fact that a finite set is not enlarged), and then covers
Sections 18.1 and 18.2.

The model is the ultrapower of Chapter 14 over the index set $`\mathbb N`, seen at the level
of types: the enlargement of a type $`\alpha` is the type {lit}`Star α` of germs of
sequences in $`\alpha` along a fixed nonprincipal ultrafilter. The transform of a function
is {name}`Filter.Germ.map`, and a transferred statement about elements $`[f]`, $`[g]` is a
statement that holds for $`f(i)`, $`g(i)` at almost all indices $`i`.
-/

noncomputable section

namespace Goldblatt.Completion

open Filter

open scoped Hyperreal

/-!
## The model

Chapter 14 builds enlargements as ultrapowers of a superstructure. Here the same
ultrapower is taken one type at a time, which lets a metric space, the ring of integers or a
ring of polynomials be used directly as Lean types.
-/

/-- **Chapter 14, ultrapower model.** The enlargement $`{}^*\alpha` of a type $`\alpha`: the
ultrapower $`\alpha^{\mathbb N}/\mathcal F` for the nonprincipal ultrafilter
{name}`Filter.hyperfilter` on $`\mathbb N`. For $`\alpha = \mathbb R` this is Mathlib's
{name}`Hyperreal`. -/
abbrev Star (α : Type*) : Type _ := (hyperfilter ℕ : Filter ℕ).Germ α

variable {α β : Type*}

/-- Every member of the enlargement is the class of a sequence. -/
theorem Star.exists_rep (x : Star α) : ∃ f : ℕ → α, (↑f : Star α) = x := Quot.exists_rep x

/-- A property that holds from some index on holds at almost all indices. -/
theorem eventually_ge_hyperfilter (n : ℕ) : ∀ᶠ i in hyperfilter ℕ, n ≤ i :=
  (eventually_ge_atTop n).filter_mono (by
    rw [← Nat.cofinite_eq_atTop]; exact hyperfilter_le_cofinite)

/-- **Section 15.4, countable saturation of the ultrapower.** Let $`A_0, A_1, \dots` be
internal subsets of $`{}^*\alpha`, each given by a sequence of subsets $`A_n(i)` of
$`\alpha`. If for every $`n` the intersection $`A_0 \cap \dots \cap A_n` is nonempty (that
is, $`A_0(i) \cap \dots \cap A_n(i)` is nonempty for almost all $`i`), then one element of
$`{}^*\alpha` lies in all the $`A_n`. In the book this is a hypothesis on the framework;
in the ultrapower over $`\mathbb N` it is a theorem. -/
theorem countable_saturation (A : ℕ → ℕ → Set α)
    (h : ∀ n, ∀ᶠ i in hyperfilter ℕ, ∃ a, ∀ m ≤ n, a ∈ A m i) :
    ∃ f : ℕ → α, ∀ n, ∀ᶠ i in hyperfilter ℕ, f i ∈ A n i := by
  classical
  obtain ⟨i₀, a₀, -⟩ := (h 0).exists
  let P : ℕ → ℕ → Prop := fun i n => ∃ a, ∀ m ≤ n, a ∈ A m i
  let f : ℕ → α := fun i =>
    if hi : P i (Nat.findGreatest (P i) i) then hi.choose else a₀
  refine ⟨f, fun n => ?_⟩
  filter_upwards [h n, eventually_ge_hyperfilter n] with i hi hn
  have hP : P i (Nat.findGreatest (P i) i) := Nat.findGreatest_spec hn hi
  have hle : n ≤ Nat.findGreatest (P i) i := Nat.le_findGreatest hn hi
  have hf : f i = hP.choose := dite_eq_left hP
  rw [hf]
  exact hP.choose_spec n hle

/-- **Finite sets are not enlarged.** If $`\beta` is finite then every member of
$`{}^*\beta` is standard. This is the fact $`{}^*(\mathbb Z/m) = \mathbb Z/m` used in
Section 18.4. -/
theorem Star.exists_eq_const_of_finite [Finite β] (x : Star β) : ∃ b : β, x = ↑b := by
  obtain ⟨f, rfl⟩ := x.exists_rep
  by_contra h
  push Not at h
  have h' : ∀ b : β, ∀ᶠ i in hyperfilter ℕ, f i ≠ b := fun b =>
    Ultrafilter.eventually_not.2 fun hb => h b (Germ.coe_eq.2 hb)
  obtain ⟨i, hi⟩ := (eventually_all.2 h').exists
  exact hi (f i) rfl

/-- The standard member of a finite type that a member of its enlargement is equal to. -/
def Star.std [Finite β] (x : Star β) : β := (Star.exists_eq_const_of_finite x).choose

theorem Star.coe_std [Finite β] (x : Star β) : (↑(Star.std x) : Star β) = x :=
  (Star.exists_eq_const_of_finite x).choose_spec.symm

theorem Star.std_eq_iff [Finite β] {f : ℕ → β} {b : β} :
    Star.std (↑f : Star β) = b ↔ ∀ᶠ i in hyperfilter ℕ, f i = b := by
  constructor
  · rintro rfl
    exact Germ.coe_eq.1 (Star.coe_std (↑f : Star β)).symm
  · intro h
    have h1 : (↑(Star.std (↑f : Star β)) : Star β) = ↑b :=
      (Star.coe_std _).trans (Germ.coe_eq.2 h)
    exact Germ.const_inj.1 h1

@[simp]
theorem Star.std_const [Finite β] (b : β) : Star.std (↑b : Star β) = b :=
  Germ.const_inj.1 (Star.coe_std _)

/-- The transform of a ring homomorphism is a ring homomorphism between the enlargements. -/
def mapRingHom {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) : Star R →+* Star S where
  toFun := Germ.map φ
  map_one' := congrArg _ (funext fun _ => map_one φ)
  map_zero' := congrArg _ (funext fun _ => map_zero φ)
  map_mul' x y := Germ.inductionOn₂ x y fun f g =>
    congrArg (Germ.ofFun (l := (hyperfilter ℕ : Filter ℕ))) (funext fun i => map_mul φ (f i) (g i))
  map_add' x y := Germ.inductionOn₂ x y fun f g =>
    congrArg (Germ.ofFun (l := (hyperfilter ℕ : Filter ℕ))) (funext fun i => map_add φ (f i) (g i))

@[simp]
theorem mapRingHom_coe {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) (f : ℕ → R) :
    mapRingHom φ (↑f : Star R) = ↑(fun i => φ (f i)) := rfl

@[simp]
theorem mapRingHom_const {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) (r : R) :
    mapRingHom φ (↑r : Star R) = ↑(φ r) := rfl

/-- The inclusion of a ring in its enlargement, as a ring homomorphism. -/
def constRingHom (R : Type*) [Semiring R] : R →+* Star R :=
  (Germ.coeRingHom (hyperfilter ℕ : Filter ℕ)).comp (Pi.constRingHom ℕ R)

@[simp]
theorem constRingHom_apply {R : Type*} [Semiring R] (r : R) : constRingHom R r = ↑r := rfl

/-- Divisibility in the enlargement of a commutative ring is the transform of divisibility:
$`[f]` divides $`[g]` exactly when $`f(i)` divides $`g(i)` for almost all $`i`. -/
theorem Star.coe_dvd_coe {R : Type*} [CommSemiring R] {f g : ℕ → R} :
    (↑f : Star R) ∣ ↑g ↔ ∀ᶠ i in hyperfilter ℕ, f i ∣ g i := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨c, rfl⟩ := c.exists_rep
    exact (Germ.coe_eq.1 hc).mono fun i hi => ⟨c i, hi⟩
  · intro h
    classical
    refine ⟨↑(fun i => if hi : f i ∣ g i then hi.choose else 0), Germ.coe_eq.2 ?_⟩
    filter_upwards [h] with i hi
    have : (if hi : f i ∣ g i then hi.choose else 0) = hi.choose := dite_eq_left hi
    simp only [this]
    exact hi.choose_spec

/-!
## Unlimited hypernaturals

A hypernatural number is unlimited when it exceeds every standard natural number. The
members of $`{}^*\mathbb N` that are not unlimited are exactly the standard ones.
-/

/-- A hypernatural number $`K` is unlimited if $`n < K` for every standard $`n`. -/
def Unlimited (K : Star ℕ) : Prop := ∀ n : ℕ, (n : Star ℕ) < K

theorem unlimited_coe_iff {k : ℕ → ℕ} :
    Unlimited (↑k : Star ℕ) ↔ ∀ n : ℕ, ∀ᶠ i in hyperfilter ℕ, n < k i :=
  forall_congr' fun _ => Germ.coe_lt

/-- The hypernatural number $`\omega = [0, 1, 2, \dots]`. -/
def omegaNat : Star ℕ := ↑(id : ℕ → ℕ)

/-- **Non-vacuity.** Unlimited hypernaturals exist. -/
theorem unlimited_omegaNat : Unlimited omegaNat :=
  unlimited_coe_iff.2 fun n => (eventually_ge_hyperfilter (n + 1)).mono fun _ hi => hi

/-- A hypernatural that is bounded by a standard natural number is standard. -/
theorem Star.eq_const_of_le_nat {K : Star ℕ} {n : ℕ} (h : K ≤ (n : Star ℕ)) :
    ∃ m : ℕ, m ≤ n ∧ K = (m : Star ℕ) := by
  obtain ⟨k, rfl⟩ := K.exists_rep
  have hk : ∀ᶠ i in hyperfilter ℕ, k i ≤ n := Germ.coe_le.1 h
  by_contra hne
  push Not at hne
  have h' : ∀ m ∈ Finset.range (n + 1), ∀ᶠ i in hyperfilter ℕ, k i ≠ m := fun m hm =>
    Ultrafilter.eventually_not.2 fun hb =>
      hne m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) (Germ.coe_eq.2 hb)
  obtain ⟨i, hi, hi'⟩ := (((Finset.range (n + 1)).eventually_all).2 h' |>.and hk).exists
  exact hi (k i) (Finset.mem_range.2 (Nat.lt_succ_of_le hi')) rfl

/-- A hypernatural number is either unlimited or standard, and not both. -/
theorem not_unlimited_iff {K : Star ℕ} : ¬Unlimited K ↔ ∃ n : ℕ, K = (n : Star ℕ) := by
  constructor
  · intro h
    simp only [Unlimited, not_forall, not_lt] at h
    obtain ⟨n, hn⟩ := h
    obtain ⟨m, -, hm⟩ := Star.eq_const_of_le_nat hn
    exact ⟨m, hm⟩
  · rintro ⟨n, rfl⟩ h
    exact lt_irrefl _ (h n)

theorem Unlimited.of_le {K L : Star ℕ} (hK : Unlimited K) (h : K ≤ L) : Unlimited L :=
  fun n => (hK n).trans_le h

/-!
## Infinitesimal and limited hyperreals, and the shadow

Chapter 5 of the book is formalized on its own page; the few facts about the hyperreals
that this chapter needs are restated here so that the chapter depends only on Part IV. The
shadow is Mathlib's {name}`ArchimedeanClass.stdPart`.
-/

/-- **Section 5.1.** A hyperreal $`x` is infinitesimal if $`|x| < r` for every positive
real $`r`. -/
def Infinitesimal (x : ℝ*) : Prop := ∀ r : ℝ, 0 < r → |x| < (r : ℝ*)

/-- **Section 5.1.** A hyperreal $`x` is limited if $`|x| \le r` for some real $`r`. -/
def Limited (x : ℝ*) : Prop := ∃ r : ℝ, |x| ≤ (r : ℝ*)

/-- **Section 5.6.** The shadow (standard part) of a hyperreal. It is the real number
infinitely close to $`x` when $`x` is limited. -/
def sh (x : ℝ*) : ℝ := ArchimedeanClass.stdPart x

theorem infinitesimal_zero : Infinitesimal 0 := fun r hr => by
  simpa using Hyperreal.coe_pos.2 hr

theorem Infinitesimal.limited {x : ℝ*} (h : Infinitesimal x) : Limited x :=
  ⟨1, (h 1 one_pos).le⟩

theorem limited_coe (r : ℝ) : Limited (r : ℝ*) := ⟨|r|, by rw [Hyperreal.coe_abs]⟩

theorem Limited.of_abs_le {x y : ℝ*} (hy : Limited y) (h : |x| ≤ |y|) : Limited x := by
  obtain ⟨r, hr⟩ := hy
  exact ⟨r, h.trans hr⟩

theorem Infinitesimal.of_abs_le {x y : ℝ*} (hy : Infinitesimal y) (h : |x| ≤ |y|) :
    Infinitesimal x := fun r hr => h.trans_lt (hy r hr)

theorem Infinitesimal.neg {x : ℝ*} (h : Infinitesimal x) : Infinitesimal (-x) :=
  h.of_abs_le (by rw [abs_neg])

theorem Limited.neg {x : ℝ*} (h : Limited x) : Limited (-x) :=
  h.of_abs_le (by rw [abs_neg])

theorem Infinitesimal.add {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) := fun r hr => by
  have h1 := hx (r / 2) (half_pos hr)
  have h2 := hy (r / 2) (half_pos hr)
  calc |x + y| ≤ |x| + |y| := abs_add_le x y
    _ < ((r / 2 : ℝ) : ℝ*) + ((r / 2 : ℝ) : ℝ*) := add_lt_add h1 h2
    _ = (r : ℝ*) := by rw [← Hyperreal.coe_add, add_halves]

theorem Infinitesimal.sub {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem Limited.add {x y : ℝ*} (hx : Limited x) (hy : Limited y) : Limited (x + y) := by
  obtain ⟨r, hr⟩ := hx
  obtain ⟨s, hs⟩ := hy
  exact ⟨r + s, (abs_add_le x y).trans (by rw [Hyperreal.coe_add]; exact add_le_add hr hs)⟩

theorem Limited.sub {x y : ℝ*} (hx : Limited x) (hy : Limited y) : Limited (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem Limited.mul {x y : ℝ*} (hx : Limited x) (hy : Limited y) : Limited (x * y) := by
  obtain ⟨r, hr⟩ := hx
  obtain ⟨s, hs⟩ := hy
  refine ⟨r * s, ?_⟩
  rw [abs_mul, Hyperreal.coe_mul]
  exact mul_le_mul hr hs (abs_nonneg y) ((abs_nonneg x).trans hr)

theorem Infinitesimal.mul_limited {x y : ℝ*} (hx : Infinitesimal x) (hy : Limited y) :
    Infinitesimal (x * y) := fun r hr => by
  obtain ⟨s, hs⟩ := hy
  have hs' : |y| ≤ ((max s 1 : ℝ) : ℝ*) :=
    hs.trans (Hyperreal.coe_le_coe.2 (le_max_left s 1))
  have hpos : (0 : ℝ) < max s 1 := lt_max_of_lt_right one_pos
  have h1 := hx (r / max s 1) (div_pos hr hpos)
  rw [abs_mul]
  calc |x| * |y| ≤ |x| * ((max s 1 : ℝ) : ℝ*) :=
        mul_le_mul_of_nonneg_left hs' (abs_nonneg x)
    _ < ((r / max s 1 : ℝ) : ℝ*) * ((max s 1 : ℝ) : ℝ*) :=
        mul_lt_mul_of_pos_right h1 (Hyperreal.coe_pos.2 hpos)
    _ = (r : ℝ*) := by rw [← Hyperreal.coe_mul, div_mul_cancel₀ r hpos.ne']

theorem infinitesimal_coe_iff {r : ℝ} : Infinitesimal (r : ℝ*) ↔ r = 0 := by
  constructor
  · intro h
    by_contra hr
    have := h |r| (abs_pos.2 hr)
    rw [← Hyperreal.coe_abs] at this
    exact lt_irrefl _ this
  · rintro rfl
    exact infinitesimal_zero

/-- Infinitesimality of a germ, read off a representing sequence. -/
theorem infinitesimal_ofSeq_iff {f : ℕ → ℝ} :
    Infinitesimal (Hyperreal.ofSeq f) ↔ ∀ r : ℝ, 0 < r → ∀ᶠ i in hyperfilter ℕ, |f i| < r :=
  forall₂_congr fun _ _ => Germ.coe_lt

theorem limited_iff_mk {x : ℝ*} : Limited x ↔ 0 ≤ ArchimedeanClass.mk x := by
  constructor
  · rintro ⟨r, hr⟩
    rw [abs_le] at hr
    exact ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean Hyperreal.coeRingHom
      (r := -r) (s := r) (by simpa using hr.1) hr.2
  · intro h
    rw [← ArchimedeanClass.mk_one, ArchimedeanClass.mk_le_mk] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    have : ((n : ℝ) : ℝ*) = (n : ℝ*) := rfl
    rw [this]
    simpa using hn

theorem infinitesimal_iff_mk {x : ℝ*} : Infinitesimal x ↔ 0 < ArchimedeanClass.mk x := by
  rw [← ArchimedeanClass.mk_one, ArchimedeanClass.mk_lt_mk]
  constructor
  · intro h n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have h1 := h (1 / n) (by positivity)
    have hn' : (0 : ℝ*) < n := by exact_mod_cast hn
    have h2 : ((1 / n : ℝ) : ℝ*) = 1 / (n : ℝ*) := by
      rw [Hyperreal.coe_div, Hyperreal.coe_one]; rfl
    rw [h2] at h1
    simp only [nsmul_eq_mul, abs_one]
    calc (n : ℝ*) * |x| < n * (1 / (n : ℝ*)) := mul_lt_mul_of_pos_left h1 hn'
      _ = 1 := by field_simp
  · intro h r hr
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / r)
    have h1 := h n
    simp only [nsmul_eq_mul, abs_one] at h1
    have hn0 : (0 : ℝ) < n := lt_trans (by positivity) hn
    have hn' : (0 : ℝ*) < n := by exact_mod_cast hn0
    have h2 : (1 : ℝ*) < n * (r : ℝ*) := by
      have h3 : (1 : ℝ) < n * r := by rwa [div_lt_iff₀ hr] at hn
      have h4 := Hyperreal.coe_lt_coe.2 h3
      rw [Hyperreal.coe_mul, Hyperreal.coe_one] at h4
      exact h4
    by_contra hcon
    rw [not_lt] at hcon
    have h5 : (n : ℝ*) * (r : ℝ*) ≤ n * |x| := mul_le_mul_of_nonneg_left hcon hn'.le
    exact lt_irrefl _ (h2.trans (h5.trans_lt h1))

@[simp]
theorem sh_coe (r : ℝ) : sh (r : ℝ*) = r := Hyperreal.stdPart_coe r

/-- **Theorem 5.6.1.** A limited hyperreal is infinitely close to its shadow. -/
theorem infinitesimal_sub_sh {x : ℝ*} (hx : Limited x) : Infinitesimal (x - (sh x : ℝ*)) :=
  infinitesimal_iff_mk.2
    (ArchimedeanClass.mk_sub_stdPart_pos Hyperreal.coeRingHom (limited_iff_mk.1 hx))

/-- **Theorem 5.6.1, uniqueness.** A real number infinitely close to $`x` is the shadow of
$`x`. -/
theorem sh_eq_of_infinitesimal_sub {x : ℝ*} {r : ℝ} (h : Infinitesimal (x - (r : ℝ*))) :
    sh x = r := by
  have hx : Limited x := by
    have := h.limited.add (limited_coe r)
    rwa [sub_add_cancel] at this
  exact (ArchimedeanClass.mk_sub_pos_iff Hyperreal.coeRingHom (limited_iff_mk.1 hx)).1
    (infinitesimal_iff_mk.1 h)

theorem limited_of_infinitesimal_sub {x y : ℝ*} (h : Infinitesimal (x - y)) (hy : Limited y) :
    Limited x := by
  have := h.limited.add hy
  rwa [sub_add_cancel] at this

theorem sh_eq_zero_iff {x : ℝ*} (hx : Limited x) : sh x = 0 ↔ Infinitesimal x := by
  constructor
  · intro h
    have := infinitesimal_sub_sh hx
    rwa [h, Hyperreal.coe_zero, sub_zero] at this
  · intro h
    exact sh_eq_of_infinitesimal_sub (by rwa [Hyperreal.coe_zero, sub_zero])

theorem Infinitesimal.sh_eq {x : ℝ*} (h : Infinitesimal x) : sh x = 0 :=
  (sh_eq_zero_iff h.limited).2 h

/-- **Theorem 5.6.2.** The shadow preserves sums of limited numbers. -/
theorem sh_add {x y : ℝ*} (hx : Limited x) (hy : Limited y) : sh (x + y) = sh x + sh y :=
  ArchimedeanClass.stdPart_add (limited_iff_mk.1 hx) (limited_iff_mk.1 hy)

theorem sh_neg (x : ℝ*) : sh (-x) = -sh x := ArchimedeanClass.stdPart_neg x

theorem sh_sub {x y : ℝ*} (hx : Limited x) (hy : Limited y) : sh (x - y) = sh x - sh y :=
  ArchimedeanClass.stdPart_sub (limited_iff_mk.1 hx) (limited_iff_mk.1 hy)

/-- **Theorem 5.6.2.** The shadow preserves products of limited numbers. -/
theorem sh_mul {x y : ℝ*} (hx : Limited x) (hy : Limited y) : sh (x * y) = sh x * sh y :=
  ArchimedeanClass.stdPart_mul (limited_iff_mk.1 hx) (limited_iff_mk.1 hy)

theorem sh_eq_sh_iff {x y : ℝ*} (hx : Limited x) (hy : Limited y) :
    sh x = sh y ↔ Infinitesimal (x - y) := by
  rw [← sh_eq_zero_iff (hx.sub hy), sh_sub hx hy, sub_eq_zero]

theorem sh_nonneg {x : ℝ*} (h : 0 ≤ x) : 0 ≤ sh x := ArchimedeanClass.stdPart_nonneg h

theorem sh_le_of_le {x : ℝ*} {r : ℝ} (hx : Limited x) (h : x ≤ (r : ℝ*)) : sh x ≤ r :=
  ArchimedeanClass.stdPart_le_of_le Hyperreal.coeRingHom (limited_iff_mk.1 hx) h

theorem le_sh_of_le {x : ℝ*} {r : ℝ} (hx : Limited x) (h : (r : ℝ*) ≤ x) : r ≤ sh x :=
  ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom (limited_iff_mk.1 hx) h

theorem lt_of_sh_lt {x : ℝ*} {r : ℝ} (hx : Limited x) (h : sh x < r) : x < (r : ℝ*) :=
  ArchimedeanClass.lt_of_stdPart_lt Hyperreal.coeRingHom (limited_iff_mk.1 hx) h

theorem lt_of_lt_sh {x : ℝ*} {r : ℝ} (hx : Limited x) (h : r < sh x) : (r : ℝ*) < x :=
  ArchimedeanClass.lt_of_lt_stdPart Hyperreal.coeRingHom (limited_iff_mk.1 hx) h

theorem sh_le_sh {x y : ℝ*} (hx : Limited x) (hy : Limited y) (h : x ≤ y) : sh x ≤ sh y :=
  ArchimedeanClass.stdPart_monotoneOn (limited_iff_mk.1 hx) (limited_iff_mk.1 hy) h

theorem Limited.abs {x : ℝ*} (h : Limited x) : Limited |x| := h.of_abs_le (by rw [abs_abs])

theorem sh_abs (x : ℝ*) : sh |x| = |sh x| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (sh_nonneg h)]
  · have h' : sh x ≤ 0 := ArchimedeanClass.stdPart_nonpos h
    rw [abs_of_nonpos h, abs_of_nonpos h', sh_neg]

/-- A nonnegative hyperreal that is smaller than every positive real is infinitesimal. -/
theorem infinitesimal_of_forall_lt {x : ℝ*} (h0 : 0 ≤ x) (h : ∀ r : ℝ, 0 < r → x < (r : ℝ*)) :
    Infinitesimal x := fun r hr => by rw [abs_of_nonneg h0]; exact h r hr

/-- **Non-vacuity.** There is a nonzero infinitesimal hyperreal. -/
theorem exists_infinitesimal_ne_zero : ∃ x : ℝ*, Infinitesimal x ∧ x ≠ 0 :=
  ⟨Hyperreal.epsilon, fun r hr => by
    rw [abs_of_pos Hyperreal.epsilon_pos]; exact Hyperreal.epsilon_lt_of_pos hr,
    Hyperreal.epsilon_ne_zero⟩

/-!
## 18.1 Completing the Rationals

Every real number is the shadow of a hyperrational number. The limited hyperrationals
form a ring, the shadow map is a ring homomorphism from it onto $`\mathbb R`, and its kernel
is the ideal of infinitesimal hyperrationals. So the real field is the quotient of the
limited hyperrationals by the infinitesimal ones. This is the pattern for the rest of the
chapter: take the limited points of an enlargement and identify points that are infinitely
close.
-/

/-- **Section 18.1.** The inclusion of the hyperrationals $`{}^*\mathbb Q` in the
hyperreals, the transform of the inclusion of $`\mathbb Q` in $`\mathbb R`. -/
def hratCast : Star ℚ →+* ℝ* := mapRingHom (Rat.castHom ℝ)

@[simp]
theorem hratCast_coe (f : ℕ → ℚ) :
    hratCast (↑f : Star ℚ) = Hyperreal.ofSeq (fun i => (f i : ℝ)) := rfl

@[simp]
theorem hratCast_const (q : ℚ) : hratCast (Germ.const q : Star ℚ) = ((q : ℝ) : ℝ*) := rfl

theorem hratCast_injective : Function.Injective hratCast := by
  intro x y
  obtain ⟨f, rfl⟩ := x.exists_rep
  obtain ⟨g, rfl⟩ := y.exists_rep
  intro h
  exact Germ.coe_eq.2 ((Germ.coe_eq.1 h).mono fun i hi => Rat.cast_injective hi)

/-- **Section 18.1, the transferred density of the rationals.** If $`r < x` with $`r`
real and $`x` hyperreal, some hyperrational lies strictly between them. -/
theorem exists_hrat_between {r : ℝ} {x : ℝ*} (h : (r : ℝ*) < x) :
    ∃ q : Star ℚ, (r : ℝ*) < hratCast q ∧ hratCast q < x := by
  obtain ⟨f, rfl⟩ := Star.exists_rep (α := ℝ) x
  have hf : ∀ᶠ i in hyperfilter ℕ, r < f i := Germ.coe_lt.1 h
  classical
  let q : ℕ → ℚ := fun i => if hi : r < f i then (exists_rat_btwn hi).choose else 0
  have hq : ∀ i, r < f i → r < (q i : ℝ) ∧ (q i : ℝ) < f i := fun i hi => by
    have : q i = (exists_rat_btwn hi).choose := dite_eq_left hi
    rw [this]; exact (exists_rat_btwn hi).choose_spec
  exact ⟨↑q, Germ.coe_lt.2 (hf.mono fun i hi => (hq i hi).1),
    Germ.coe_lt.2 (hf.mono fun i hi => (hq i hi).2)⟩

/-- **Section 18.1.** Every real number is the shadow of a limited hyperrational: there is
$`q \in {}^*\mathbb Q` with $`q \simeq r`, and $`q` can be taken different from $`r`. -/
theorem exists_hrat_infinitesimal_sub (r : ℝ) :
    ∃ q : Star ℚ, (r : ℝ*) < hratCast q ∧ Infinitesimal (hratCast q - (r : ℝ*)) := by
  have hpos : (r : ℝ*) < r + Hyperreal.epsilon := lt_add_of_pos_right _ Hyperreal.epsilon_pos
  obtain ⟨q, h1, h2⟩ := exists_hrat_between hpos
  refine ⟨q, h1, fun s hs => ?_⟩
  rw [abs_of_pos (sub_pos.2 h1)]
  calc hratCast q - (r : ℝ*) < Hyperreal.epsilon := by rw [sub_lt_iff_lt_add']; exact h2
    _ < s := Hyperreal.epsilon_lt_of_pos hs

/-- **Section 18.1.** The ring $`{}^*\mathbb Q^{\lim}` of limited hyperrationals. -/
def limitedHRat : Subring (Star ℚ) where
  carrier := {q | Limited (hratCast q)}
  mul_mem' {a b} ha hb := by
    change Limited (hratCast (a * b)); rw [map_mul]; exact Limited.mul ha hb
  one_mem' := by
    change Limited (hratCast 1); rw [map_one]; exact limited_coe 1
  add_mem' {a b} ha hb := by
    change Limited (hratCast (a + b)); rw [map_add]; exact Limited.add ha hb
  zero_mem' := by
    change Limited (hratCast 0); rw [map_zero]; exact limited_coe 0
  neg_mem' {a} ha := by
    change Limited (hratCast (-a)); rw [map_neg]; exact Limited.neg ha

theorem mem_limitedHRat {q : Star ℚ} : q ∈ limitedHRat ↔ Limited (hratCast q) := Iff.rfl

/-- **Section 18.1.** The shadow map $`\operatorname{sh} : {}^*\mathbb Q^{\lim} \to \mathbb R`,
a ring homomorphism by Theorem 5.6.2. -/
def shRat : limitedHRat →+* ℝ where
  toFun q := sh (hratCast q)
  map_one' := by simp only [OneMemClass.coe_one, map_one]; exact sh_coe 1
  map_zero' := by simp only [ZeroMemClass.coe_zero, map_zero]; exact sh_coe 0
  map_mul' x y := by
    simp only [MulMemClass.coe_mul, map_mul]; exact sh_mul x.2 y.2
  map_add' x y := by
    simp only [AddMemClass.coe_add, map_add]; exact sh_add x.2 y.2

theorem shRat_apply (q : limitedHRat) : shRat q = sh (hratCast q) := rfl

/-- **Section 18.1.** The shadow map on the limited hyperrationals is onto $`\mathbb R`. -/
theorem shRat_surjective : Function.Surjective shRat := fun r => by
  obtain ⟨q, -, hq⟩ := exists_hrat_infinitesimal_sub r
  exact ⟨⟨q, limited_of_infinitesimal_sub hq (limited_coe r)⟩, sh_eq_of_infinitesimal_sub hq⟩

/-- **Section 18.1.** The kernel of the shadow map is the set $`{}^*\mathbb Q^{\inf}` of
infinitesimal hyperrationals. -/
theorem mem_ker_shRat {q : limitedHRat} :
    q ∈ RingHom.ker shRat ↔ Infinitesimal (hratCast q) := by
  rw [RingHom.mem_ker, shRat_apply, sh_eq_zero_iff q.2]

/-- **Section 18.1.** The isomorphism
$`{}^*\mathbb Q^{\lim} / {}^*\mathbb Q^{\inf} \cong \mathbb R` induced by the shadow map
(compare Exercise 5.7(4)). -/
def limitedHRatQuotEquiv : (limitedHRat ⧸ RingHom.ker shRat) ≃+* ℝ :=
  RingHom.quotientKerEquivOfSurjective shRat_surjective

@[simp]
theorem limitedHRatQuotEquiv_mk (q : limitedHRat) :
    limitedHRatQuotEquiv (Ideal.Quotient.mk _ q) = sh (hratCast q) := rfl

/-- **Section 18.1.** For limited hyperrationals $`x`, $`y` the following are equivalent:
$`x \simeq y`; the shadows agree; the shadow of $`x - y` is zero; $`x - y` is infinitesimal
(lies in the kernel of the shadow map); the cosets of $`x` and $`y` modulo the infinitesimal
hyperrationals agree. So the cosets are the classes of the relation of infinite closeness. -/
theorem hrat_infinitelyClose_tfae (x y : limitedHRat) :
    List.TFAE [Infinitesimal (hratCast x - hratCast y),
      shRat x = shRat y,
      shRat (x - y) = 0,
      x - y ∈ RingHom.ker shRat,
      Ideal.Quotient.mk (RingHom.ker shRat) x = Ideal.Quotient.mk (RingHom.ker shRat) y] := by
  tfae_have 1 ↔ 2 := (sh_eq_sh_iff x.2 y.2).symm
  tfae_have 2 ↔ 3 := by rw [map_sub, sub_eq_zero]
  tfae_have 3 ↔ 4 := Iff.rfl
  tfae_have 4 ↔ 5 := Ideal.Quotient.eq.symm
  tfae_finish

/-!
## 18.2 Metric Space Completion

Metric spaces, Cauchy sequences, convergence and completeness are Mathlib's
({name}`MetricSpace`, {name}`CauchySeq`, {name}`CompleteSpace`). A completion of a metric
space $`X` is a complete metric space containing an isometric copy of $`X` as a dense
subset. The book takes $`X` to be a subset of its completion; here the inclusion is an
explicit isometry. Any two completions are isometric by an isometry that fixes $`X`, which
is proved by comparing each with Mathlib's {name}`UniformSpace.Completion`.
-/

section Completions

variable {X Y Z : Type*} [MetricSpace Y]

/-- **Section 18.2.** Density can be tested with real tolerances: $`X` is dense in $`Y` if
and only if every point of $`Y` is within every positive real distance of a point of $`X`. -/
theorem denseRange_iff_forall_exists_dist_lt {ι : X → Y} :
    DenseRange ι ↔ ∀ y : Y, ∀ r : ℝ, 0 < r → ∃ x : X, dist y (ι x) < r :=
  Metric.denseRange_iff

/-- **Section 18.2.** Density in terms of sequences: $`X` is dense in $`Y` if and only if
every point of $`Y` is the limit of a sequence of points of $`X`. -/
theorem denseRange_iff_forall_exists_seq {ι : X → Y} :
    DenseRange ι ↔ ∀ y : Y, ∃ u : ℕ → X, Tendsto (fun n => ι (u n)) atTop (nhds y) := by
  constructor
  · intro h y
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 (h y)
    choose u hu using hv
    exact ⟨u, by simpa only [hu] using hlim⟩
  · intro h y
    obtain ⟨u, hu⟩ := h y
    exact mem_closure_of_tendsto hu (Eventually.of_forall fun n => Set.mem_range_self _)

variable [MetricSpace X] [MetricSpace Z]

/-- **Section 18.2.** The map $`\iota : X \to Y` exhibits $`Y` as a completion of the metric
space $`X`: it preserves distances, $`Y` is complete, and the image of $`X` is dense in
$`Y`. -/
structure IsCompletion (ι : X → Y) : Prop where
  /-- The original space is a subspace: the map preserves distances. -/
  isometry : Isometry ι
  /-- The larger space is complete. -/
  complete : CompleteSpace Y
  /-- The original space is dense in the larger one. -/
  denseRange : DenseRange ι

/-- Mathlib's completion is a completion in the sense of Section 18.2. -/
theorem isCompletion_coe :
    IsCompletion ((↑) : X → UniformSpace.Completion X) :=
  ⟨UniformSpace.Completion.coe_isometry, inferInstance, UniformSpace.Completion.denseRange_coe⟩

theorem IsCompletion.isometry_extension {ι : X → Y} (h : IsCompletion ι) :
    Isometry (UniformSpace.Completion.extension ι) :=
  haveI := h.complete
  h.isometry.completion_extension

theorem IsCompletion.extension_coe {ι : X → Y} (h : IsCompletion ι) (x : X) :
    UniformSpace.Completion.extension ι (x : UniformSpace.Completion X) = ι x :=
  haveI := h.complete
  UniformSpace.Completion.extension_coe h.isometry.uniformContinuous x

theorem IsCompletion.surjective_extension {ι : X → Y} (h : IsCompletion ι) :
    Function.Surjective (UniformSpace.Completion.extension ι) := by
  have hcl : IsClosed (Set.range (UniformSpace.Completion.extension ι)) :=
    h.isometry_extension.isUniformInducing.isComplete_range.isClosed
  have hsub : Set.range ι ⊆ Set.range (UniformSpace.Completion.extension ι) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, h.extension_coe x⟩
  have : Set.range (UniformSpace.Completion.extension ι) = Set.univ :=
    Set.eq_univ_of_univ_subset (h.denseRange.closure_eq ▸ hcl.closure_subset_iff.2 hsub)
  exact Set.range_eq_univ.1 this

/-- **Section 18.2, uniqueness of completions.** A completion of $`X` is isometric to
Mathlib's completion of $`X`. -/
def IsCompletion.equiv {ι : X → Y} (h : IsCompletion ι) : UniformSpace.Completion X ≃ᵢ Y where
  toEquiv := Equiv.ofBijective _ ⟨h.isometry_extension.injective, h.surjective_extension⟩
  isometry_toFun := h.isometry_extension

theorem IsCompletion.equiv_coe {ι : X → Y} (h : IsCompletion ι) (x : X) :
    h.equiv (x : UniformSpace.Completion X) = ι x :=
  h.extension_coe x

/-- **Section 18.2, uniqueness of completions.** Any two completions of a metric space are
isometric by a bijection that leaves the points of the original space fixed. -/
theorem IsCompletion.unique {ι : X → Y} {κ : X → Z} (h₁ : IsCompletion ι)
    (h₂ : IsCompletion κ) : ∃ e : Y ≃ᵢ Z, ∀ x, e (ι x) = κ x :=
  ⟨h₁.equiv.symm.trans h₂.equiv, fun x => by
    rw [IsometryEquiv.trans_apply, ← h₁.equiv_coe x, IsometryEquiv.symm_apply_apply,
      h₂.equiv_coe]⟩

/-- **Section 18.2.** The real line is a completion of the rationals under the Euclidean
metric. -/
theorem isCompletion_ratCast : IsCompletion ((↑) : ℚ → ℝ) :=
  ⟨Isometry.of_dist_eq fun x y => (Rat.dist_cast x y), inferInstance, Rat.denseRange_cast⟩

end Completions

end Goldblatt.Completion
