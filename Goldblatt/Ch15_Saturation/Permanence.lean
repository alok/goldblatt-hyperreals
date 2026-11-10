import Goldblatt.Ch15_Saturation.Hyperreals

/-!
# 15 (part 3). Permanence and Robinson's sequential lemma: Sections 15.1 to 15.3

This is the third of five parts of Chapter 15 (the overview is on the chapter page
{lit}`Goldblatt.Ch15_Saturation`). It proves the permanence principles of Section 15.1 for
internal properties in an arbitrary framework over the real numbers, derives Robinson's
sequential lemma and its variants (Section 15.2), and uses the lemma to show that a uniform
limit of continuous functions is continuous (Section 15.3).

Throughout, the framework is assumed to have a nonstandard hypernatural number, the standing
assumption of the chapter; it appears as the hypothesis {lit}`hω`.
-/

noncomputable section

namespace Goldblatt

open ZFSet NonstandardFramework

universe u

namespace NonstandardFramework

variable (F : NonstandardFramework.{u}) {A : ZFSet.{u}} {φ : Formula.{u}} {x : ℕ}

/-!
## 15.1 Permanence Principles

A permanence principle says that an internal property which holds throughout a set of a
certain kind (the standard natural numbers from some point on, the unlimited hypernaturals up
to some point, a halo, the real numbers beyond some point) holds on a strictly larger set.
The reason is always the same: the property defines an internal set, and the sets in
question are external.

The book states the principles for an internal formula $`\varphi(x)` of the language of
$`\mathbb U'` with one free variable. Each is proved here in two forms. The form for sets
speaks of an internal entity $`A` and membership in it; it is the one used in applications.
The form for formulas is the book's statement, and follows from the first by the internal set
definition principle of Section 13.15, since $`\{a \in {}^*\mathbb N : \varphi(a)\}` and
$`\{a \in {}^*\mathbb R : \varphi(a)\}` are internal.
-/

/-- **Section 15.1, internal formulas.** $`\varphi` is an internal formula of the language
of $`\mathbb U'` in which only the variable $`x` is free: its constants are internal
entities. -/
structure IsInternalFormula (φ : Formula.{u}) (x : ℕ) : Prop where
  /-- The formula belongs to the language of the universe and only the variable is free. -/
  admissible : φ.Admissible F.U' {x}
  /-- Every constant of the formula is internal. -/
  consts : φ.ConstsSat F.Internal

/-- **Section 15.1.** The statement "$`\varphi(a)` is true": the formula is satisfied in
$`\mathbb U'` when its free variable $`x` is given the value $`a`. -/
def TrueAt (φ : Formula.{u}) (x : ℕ) (a : ZFSet.{u}) : Prop :=
  Sat F.U' (Function.update (fun _ => ∅) x a) φ

variable {F}

/-- **Section 13.15, internal set definition principle.** The members of an internal set
that satisfy an internal formula form an internal set. -/
theorem internal_sep_trueAt (h : F.IsInternalFormula φ x) (hA : F.Internal A)
    (hAset : IsSetOf F.U' A) : F.Internal (A.sep (F.TrueAt φ x)) :=
  F.internal_sep_of_internal_consts φ x h.admissible h.consts _ hA hAset

end NonstandardFramework

namespace RealFramework

variable {F : RealFramework.{u}} {A B V X a b c f n s x y K : ZFSet.{u}} {φ : Formula.{u}}
  {v : ℕ}

/-- $`{}^*\mathbb N` is an internal set. -/
theorem star_N_spec (F : RealFramework.{u}) :
    F.Internal (F.star F.N) ∧ IsSetOf F.U' (F.star F.N) :=
  ⟨F.internal_star F.isSetOf_N.1, F.isSetOf_star F.isSetOf_N⟩

/-- $`{}^*\mathbb R` is an internal set. -/
theorem star_R_spec (F : RealFramework.{u}) :
    F.Internal (F.star F.R) ∧ IsSetOf F.U' (F.star F.R) :=
  ⟨F.internal_star F.isSetOf_R.1, F.isSetOf_star F.isSetOf_R⟩

/-- Hyperreals are internal. -/
theorem internal_of_mem_star_R (ha : a ∈ F.star F.R) : F.Internal a :=
  F.internal_of_mem_star F.isSetOf_R ha

/-- **Section 15.1, the principle behind overflow.** An internal set that contains every
standard natural number contains a nonstandard hypernatural number, because $`\mathbb N` is
not internal. -/
theorem exists_nonstandard_mem (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hB : F.Internal B)
    (hNB : F.N ⊆ B) : ∃ K ∈ F.star F.N, K ∉ F.N ∧ K ∈ B := by
  have hint : F.Internal (F.star F.N ∩ B) := F.internal_inter F.star_N_spec.1 F.star_N_spec.2 hB
  have hsub : F.N ⊆ F.star F.N ∩ B := fun n hn => mem_inter.2 ⟨F.N_subset_star hn, hNB hn⟩
  by_contra hcon
  push Not at hcon
  have : F.star F.N ∩ B = F.N := _root_.le_antisymm (fun K hK => by
    by_contra hKN
    exact hcon K (mem_inter.1 hK).1 hKN (mem_inter.1 hK).2) hsub
  exact F.not_internal_N hω (this ▸ hint)

/-- **Theorem 15.1.1 (1), overflow, for internal sets.** If an internal entity $`A`
contains every standard natural number $`n \ge k`, then for some unlimited hypernatural $`K`
it contains every hypernatural $`n` with $`k \le n \le K`. The proof considers the internal
set of all $`K` with this property; it contains $`\mathbb N`, which is external, so it has a
nonstandard member. (The book takes the predecessor of the least hypernatural above $`k`
outside $`A`.) -/
theorem overflow_set (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hA : F.Internal A) (k : ℕ)
    (h : ∀ n : ℕ, k ≤ n → F.nat n ∈ A) :
    ∃ K, K ∈ F.star F.N ∧ K ∉ F.N ∧
      ∀ n ∈ F.star F.N, pair (F.nat k) n ∈ F.star F.Le → pair n K ∈ F.star F.Le → n ∈ A := by
  obtain ⟨hNint, hNset⟩ := F.star_N_spec
  have hkint : F.Internal (F.nat k) := F.star_nat k ▸ F.internal_star (F.nat_mem_U k)
  set C := (F.star F.N ∩ relImage (F.star F.Le) {F.nat k}) \ A with hC
  set B := F.star F.N \ relImage (F.star F.Le) C with hB
  have hCint : F.Internal C :=
    F.internal_sdiff (F.internal_inter hNint hNset
      (internal_relImage_star F.isSetOf_Le F.relIn_Le (F.internal_singleton hkint)))
      (F.isUniverse'.isSetOf_inter hNset) hA
  have hBint : F.Internal B :=
    F.internal_sdiff hNint hNset (internal_relImage_star F.isSetOf_Le F.relIn_Le hCint)
  have hNB : F.N ⊆ B := by
    intro m hm
    obtain ⟨j, rfl⟩ := F.mem_N.1 hm
    refine mem_sdiff.2 ⟨F.N_subset_star hm, fun hj => ?_⟩
    obtain ⟨n, hnC, hnj⟩ := mem_relImage.1 hj
    obtain ⟨hn, hnA⟩ := mem_sdiff.1 hnC
    obtain ⟨hnN, hkn⟩ := mem_inter.1 hn
    obtain ⟨_, hk', hkn⟩ := mem_relImage.1 hkn
    rw [mem_singleton] at hk'
    subst hk'
    obtain ⟨i, rfl⟩ := F.mem_N.1 (mem_N_of_le_nat hnN hnj)
    exact hnA (h i (F.pair_nat_mem_star_Le.1 hkn))
  obtain ⟨K, hK, hKN, hKB⟩ := exists_nonstandard_mem hω hBint hNB
  refine ⟨K, hK, hKN, fun n hn hkn hnK => ?_⟩
  by_contra hnA
  exact (mem_sdiff.1 hKB).2 (mem_relImage.2 ⟨n, mem_sdiff.2
    ⟨mem_inter.2 ⟨hn, mem_relImage.2 ⟨_, mem_singleton.2 rfl, hkn⟩⟩, hnA⟩, hnK⟩)

/-- **Theorem 15.1.1 (1), overflow.** Let $`\varphi(x)` be an internal formula. If
$`\varphi(n)` is true for all standard $`n \ge k`, then there is an unlimited hypernatural
$`K` such that $`\varphi(n)` is true for all hypernatural $`n` with $`k \le n \le K`. -/
theorem overflow (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hφ : F.IsInternalFormula φ v) (k : ℕ)
    (h : ∀ n : ℕ, k ≤ n → F.TrueAt φ v (F.nat n)) :
    ∃ K, K ∈ F.star F.N ∧ K ∉ F.N ∧
      ∀ n ∈ F.star F.N, pair (F.nat k) n ∈ F.star F.Le → pair n K ∈ F.star F.Le →
        F.TrueAt φ v n := by
  obtain ⟨K, hK, hKN, hall⟩ := overflow_set hω
    (internal_sep_trueAt hφ F.star_N_spec.1 F.star_N_spec.2) k
    fun n hn => mem_sep.2 ⟨F.N_subset_star (F.mem_N.2 ⟨n, rfl⟩), h n hn⟩
  exact ⟨K, hK, hKN, fun n hn hkn hnK => (mem_sep.1 (hall n hn hkn hnK)).2⟩

/-- **Theorem 15.1.1 (2), underflow, for internal sets.** If an internal entity $`A`
contains every unlimited hypernatural $`n \le K`, for some unlimited $`K`, then it contains
every standard natural number from some $`k` on. Otherwise the internal set of the
hypernaturals $`y` such that some $`x \notin A` has $`y \le x \le K` would contain
$`\mathbb N`, hence an unlimited $`y`, and then an unlimited $`x \le K` outside $`A`. -/
theorem underflow_set (hA : F.Internal A) (hK : K ∈ F.star F.N) (hKN : K ∉ F.N)
    (h : ∀ n ∈ F.star F.N, n ∉ F.N → pair n K ∈ F.star F.Le → n ∈ A) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → F.nat n ∈ A := by
  obtain ⟨hNint, hNset⟩ := F.star_N_spec
  have hKint : F.Internal K := F.internal_of_mem_star F.isSetOf_N hK
  by_contra hcon
  push Not at hcon
  set D := (F.star F.N ∩ relPreimage (F.star F.Le) {K}) \ A with hD
  set B := relPreimage (F.star F.Le) D with hB
  have hDint : F.Internal D :=
    F.internal_sdiff (F.internal_inter hNint hNset
      (internal_relPreimage_star F.isSetOf_Le F.relIn_Le (F.internal_singleton hKint)))
      (F.isUniverse'.isSetOf_inter hNset) hA
  have hBint : F.Internal B := internal_relPreimage_star F.isSetOf_Le F.relIn_Le hDint
  have hNB : F.N ⊆ B := by
    intro m hm
    obtain ⟨k, rfl⟩ := F.mem_N.1 hm
    obtain ⟨n, hkn, hnA⟩ := hcon k
    have hnN : F.nat n ∈ F.star F.N := F.N_subset_star (F.mem_N.2 ⟨n, rfl⟩)
    exact mem_relPreimage.2 ⟨F.nat n, mem_sdiff.2 ⟨mem_inter.2 ⟨hnN, mem_relPreimage.2
      ⟨K, mem_singleton.2 rfl, F.nat_le_of_nonstandard hK hKN n⟩⟩, hnA⟩,
      F.pair_nat_mem_star_Le.2 hkn⟩
  obtain ⟨K', hK', hK'N, hK'B⟩ := exists_nonstandard_mem ⟨K, hK, hKN⟩ hBint hNB
  obtain ⟨x, hxD, hK'x⟩ := mem_relPreimage.1 hK'B
  obtain ⟨hx, hxA⟩ := mem_sdiff.1 hxD
  obtain ⟨hxN, hxK⟩ := mem_inter.1 hx
  obtain ⟨K₂, hK₂, hxK₂⟩ := mem_relPreimage.1 hxK
  obtain rfl := mem_singleton.1 hK₂
  exact hxA (h x hxN (notMem_N_of_le hK' hK'N hK'x) hxK₂)

/-- **Theorem 15.1.1 (2), underflow.** Let $`\varphi(x)` be an internal formula. If
there is an unlimited hypernatural $`K` such that $`\varphi(n)` is true for all unlimited
hypernaturals $`n \le K`, then there is a standard $`k` such that $`\varphi(n)` is true for
all standard $`n \ge k`. -/
theorem underflow (hφ : F.IsInternalFormula φ v) (hK : K ∈ F.star F.N) (hKN : K ∉ F.N)
    (h : ∀ n ∈ F.star F.N, n ∉ F.N → pair n K ∈ F.star F.Le → F.TrueAt φ v n) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → F.TrueAt φ v (F.nat n) := by
  obtain ⟨k, hk⟩ := underflow_set (internal_sep_trueAt hφ F.star_N_spec.1 F.star_N_spec.2)
    hK hKN fun n hn hnN hnK => mem_sep.2 ⟨hn, h n hn hnN hnK⟩
  exact ⟨k, fun n hn => (mem_sep.1 (hk n hn)).2⟩

/-- **Theorem 15.1.1 (3), for internal sets.** If an internal entity $`A` contains every
hyperreal infinitely close to a hyperreal $`b`, then it contains every hyperreal within some
positive real distance of $`b`. The internal set of the hypernaturals $`n` such that every
hyperreal within $`1/(n+1)` of $`b` is in $`A` contains all unlimited $`n`, so by underflow
it contains a standard one. -/
theorem near_permanence_set (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hA : F.Internal A)
    (hb : b ∈ F.star F.R) (h : ∀ a, F.Near a b → a ∈ A) :
    ∃ r : ℝ, 0 < r ∧ ∀ a, F.Within r a b → a ∈ A := by
  obtain ⟨hNint, hNset⟩ := F.star_N_spec
  obtain ⟨hRint, hRset⟩ := F.star_R_spec
  have hbint := internal_of_mem_star_R hb
  set cRR := F.cR.prod F.cR with hcRR
  set Close := Code.rel cRR F.cR (fun q m => |q.1 - q.2| * (m + 1) < 1) with hClose
  set P := ZFSet.prod (F.star F.R \ A) {b} with hP
  set Y := F.star F.N \ relImage (F.star Close) P with hY
  have hPint : F.Internal P :=
    F.internal_prod (F.internal_sdiff hRint hRset hA) (F.isUniverse'.isSetOf_sdiff hRset)
      (F.internal_singleton hbint) (F.isUniverse'.isSetOf_singleton hbint.mem_U')
  have hYint : F.Internal Y :=
    F.internal_sdiff hNint hNset
      (internal_relImage_star (Code.isSetOf_rel _ _ _) (Code.relIn_rel _ _ _) hPint)
  obtain ⟨K, hK, hKN⟩ := hω
  obtain ⟨k, hk⟩ := underflow_set hYint hK hKN (by
    intro n hn hnN _
    refine mem_sdiff.2 ⟨hn, fun hmem => ?_⟩
    obtain ⟨p, hp, hpn⟩ := mem_relImage.1 hmem
    obtain ⟨a, ha, b', hb', rfl⟩ := mem_prod.1 hp
    rw [mem_singleton] at hb'
    subst hb'
    refine (mem_sdiff.1 ha).2 (h a fun r hr => ?_)
    have hlt : F.Lt (F.real (1 / r)) n := posUnlimited_of_nonstandard hn hnN (1 / r)
    have h1 := Code.rel_comp cRR F.cR F.cR
      (P := fun q m => |q.1 - q.2| * (m + 1) < 1) (Q := fun m t => t < m)
      (R := fun q t => 0 < t → |q.1 - q.2| < 1 / t)
      (fun q m t h1 h2 ht => by
        rw [lt_div_iff₀ ht]
        nlinarith [abs_nonneg (q.1 - q.2)])
      hpn ((Code.rel_swap F.cR F.cR).1 hlt)
    have h2 := (Code.pair_enc_right_mem_star_rel cRR F.cR (b := 1 / r)).1 h1
    exact cRR.star_set_mono (fun q (hq : 0 < 1 / r → |q.1 - q.2| < 1 / (1 / r)) => by
      have := hq (one_div_pos.2 hr)
      rwa [one_div_one_div] at this) h2)
  refine ⟨1 / ((k : ℝ) + 1), by positivity, fun a ha => ?_⟩
  by_contra haA
  have hkY := hk k le_rfl
  refine (mem_sdiff.1 hkY).2 (mem_relImage.2 ⟨pair a b,
    pair_mem_prod.2 ⟨mem_sdiff.2 ⟨ha.mem.1, haA⟩, mem_singleton.2 rfl⟩, ?_⟩)
  refine (Code.pair_enc_right_mem_star_rel cRR F.cR (b := (k : ℝ))).2 ?_
  exact cRR.star_set_mono (fun q (hq : |q.1 - q.2| < 1 / ((k : ℝ) + 1)) => by
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    exact (lt_div_iff₀ hpos).1 hq) ha

/-- **Theorem 15.1.1 (3).** Let $`\varphi(x)` be an internal formula. If $`\varphi(a)` is
true for all hyperreals $`a` infinitely close to a hyperreal $`b`, then $`\varphi(a)` is
true for all hyperreals $`a` within some positive real distance of $`b`. -/
theorem near_permanence (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hφ : F.IsInternalFormula φ v)
    (hb : b ∈ F.star F.R) (h : ∀ a, F.Near a b → F.TrueAt φ v a) :
    ∃ r : ℝ, 0 < r ∧ ∀ a, F.Within r a b → F.TrueAt φ v a := by
  obtain ⟨r, hr, hall⟩ := near_permanence_set hω
    (internal_sep_trueAt hφ F.star_R_spec.1 F.star_R_spec.2) hb
    fun a ha => mem_sep.2 ⟨ha.mem.1, h a ha⟩
  exact ⟨r, hr, fun a ha => (mem_sep.1 (hall a ha)).2⟩

/-- **Theorem 15.1.1 (4), for internal sets, large numbers.** An internal entity that
contains arbitrarily large real numbers contains a positive unlimited hyperreal. The book
suggests internal order-completeness; the proof here applies the overflow argument to the
internal set of the hypernaturals that lie below some member of $`A`. -/
theorem exists_posUnlimited_mem (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hA : F.Internal A)
    (h : ∀ r : ℝ, ∃ a : ℝ, r < a ∧ F.real a ∈ A) : ∃ a, F.PosUnlimited a ∧ a ∈ A := by
  have hBint : F.Internal (relPreimage (F.star F.Le) A) :=
    internal_relPreimage_star F.isSetOf_Le F.relIn_Le hA
  obtain ⟨K, hK, hKN, hKB⟩ := exists_nonstandard_mem hω hBint (by
    intro m hm
    obtain ⟨k, rfl⟩ := F.mem_N.1 hm
    obtain ⟨a, hka, haA⟩ := h k
    exact mem_relPreimage.2 ⟨F.real a, haA, F.pair_real_mem_star_Le.2 hka.le⟩)
  obtain ⟨a, haA, hKa⟩ := mem_relPreimage.1 hKB
  exact ⟨a, (posUnlimited_of_nonstandard hK hKN).of_le hKa, haA⟩

/-- **Theorem 15.1.1 (4), for internal sets, small numbers.** An internal entity that
contains arbitrarily small real numbers (real numbers below any given real number) contains
a negative unlimited hyperreal. -/
theorem exists_negUnlimited_mem (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hA : F.Internal A)
    (h : ∀ r : ℝ, ∃ a : ℝ, a < r ∧ F.real a ∈ A) : ∃ a, F.NegUnlimited a ∧ a ∈ A := by
  set Q := F.rr (fun m x => x ≤ -m) with hQ
  have hBint : F.Internal (relPreimage (F.star Q) A) :=
    internal_relPreimage_star (Code.isSetOf_rel _ _ _) (Code.relIn_rel _ _ _) hA
  obtain ⟨K, hK, hKN, hKB⟩ := exists_nonstandard_mem hω hBint (by
    intro m hm
    obtain ⟨k, rfl⟩ := F.mem_N.1 hm
    obtain ⟨a, hka, haA⟩ := h (-k)
    exact mem_relPreimage.2 ⟨F.real a, haA,
      (Code.pair_enc_mem_star_rel F.cR F.cR (a := (k : ℝ)) (b := a)).2 hka.le⟩)
  obtain ⟨a, haA, hKa⟩ := mem_relPreimage.1 hKB
  refine ⟨a, fun r => ?_, haA⟩
  have hlt : F.Lt (F.real (-r)) K := posUnlimited_of_nonstandard hK hKN (-r)
  have h1 := Code.rel_comp F.cR F.cR F.cR (P := (· < ·)) (Q := fun m x => x ≤ -m)
    (R := fun t x => x < -t) (fun t m x h1 h2 => by linarith) hlt hKa
  have h2 := (Code.pair_enc_left_mem_star_rel F.cR F.cR (a := -r)).1 h1
  exact lt_real_iff.2 (F.cR.star_set_mono (fun x (hx : x < - -r) => by
    simpa using hx) h2)

/-- **Theorem 15.1.1 (4).** Let $`\varphi(x)` be an internal formula. If $`\varphi(a)` is
true for arbitrarily large real numbers $`a`, then it is true for some positive unlimited
hyperreal; if it is true for arbitrarily small real numbers, then it is true for some
negative unlimited hyperreal. -/
theorem exists_unlimited_trueAt (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N)
    (hφ : F.IsInternalFormula φ v) :
    ((∀ r : ℝ, ∃ a : ℝ, r < a ∧ F.TrueAt φ v (F.real a)) →
      ∃ a, F.PosUnlimited a ∧ F.TrueAt φ v a) ∧
    ((∀ r : ℝ, ∃ a : ℝ, a < r ∧ F.TrueAt φ v (F.real a)) →
      ∃ a, F.NegUnlimited a ∧ F.TrueAt φ v a) := by
  have hint := internal_sep_trueAt hφ F.star_R_spec.1 F.star_R_spec.2
  constructor
  · intro h
    obtain ⟨a, ha, haA⟩ := exists_posUnlimited_mem hω hint fun r =>
      let ⟨a, hra, ha⟩ := h r
      ⟨a, hra, mem_sep.2 ⟨F.real_mem_star a, ha⟩⟩
    exact ⟨a, ha, (mem_sep.1 haA).2⟩
  · intro h
    obtain ⟨a, ha, haA⟩ := exists_negUnlimited_mem hω hint fun r =>
      let ⟨a, hra, ha⟩ := h r
      ⟨a, hra, mem_sep.2 ⟨F.real_mem_star a, ha⟩⟩
    exact ⟨a, ha, (mem_sep.1 haA).2⟩

/-- **Theorem 15.1.1 (5), for internal sets, corrected.** If an internal entity $`A`
contains every _limited_ hyperreal $`a \ge r`, for some real $`r`, then for some positive
unlimited $`b` it contains every hyperreal $`a` with $`r \le a \le b`.

The book's hypothesis is only that $`A` contains every _real_ number $`a \ge r`. With that
hypothesis the conclusion fails: for a positive infinitesimal $`\varepsilon` the internal
set of the hyperreals $`a` with $`a \le r` or $`a \ge r + \varepsilon` contains every real
number $`a \ge r` but not $`r + \varepsilon/2`
({lit}`not_theorem_15_1_1_5_as_printed`). The hypothesis used here is the one of the
analogous statement of Section 11.6, that an internal set including all limited numbers
includes an interval with unlimited end points. -/
theorem exists_posUnlimited_forall_mem (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N)
    (hA : F.Internal A) (r : ℝ)
    (h : ∀ a, F.Limited a → pair (F.real r) a ∈ F.star F.Le → a ∈ A) :
    ∃ b, F.PosUnlimited b ∧
      ∀ a, pair (F.real r) a ∈ F.star F.Le → pair a b ∈ F.star F.Le → a ∈ A := by
  obtain ⟨hNint, hNset⟩ := F.star_N_spec
  obtain ⟨hLint, hLset, hLrel⟩ := star_rel_spec F.isSetOf_Le F.relIn_Le
  have hrint : F.Internal (F.real r) := internal_of_mem_star_R (F.real_mem_star r)
  set C := relImage (F.star F.Le) {F.real r} \ A with hC
  set B := F.star F.N \ relImage (F.star F.Le) C with hB
  have hCint : F.Internal C :=
    F.internal_sdiff (internal_relImage_star F.isSetOf_Le F.relIn_Le
      (F.internal_singleton hrint)) (F.isUniverse'.isSetOf_relImage hLset hLrel _) hA
  have hBint : F.Internal B :=
    F.internal_sdiff hNint hNset (internal_relImage_star F.isSetOf_Le F.relIn_Le hCint)
  obtain ⟨K, hK, hKN, hKB⟩ := exists_nonstandard_mem hω hBint (by
    intro m hm
    obtain ⟨j, rfl⟩ := F.mem_N.1 hm
    refine mem_sdiff.2 ⟨F.N_subset_star hm, fun hj => ?_⟩
    obtain ⟨a, haC, haj⟩ := mem_relImage.1 hj
    obtain ⟨hra, haA⟩ := mem_sdiff.1 haC
    obtain ⟨_, hr', hra⟩ := mem_relImage.1 hra
    rw [mem_singleton] at hr'
    subst hr'
    exact haA (h a (limited_of_le_of_le hra haj) hra))
  refine ⟨K, posUnlimited_of_nonstandard hK hKN, fun a hra haK => ?_⟩
  by_contra haA
  exact (mem_sdiff.1 hKB).2 (mem_relImage.2 ⟨a, mem_sdiff.2
    ⟨mem_relImage.2 ⟨_, mem_singleton.2 rfl, hra⟩, haA⟩, haK⟩)

/-- **Theorem 15.1.1 (5) as printed is false.** For every real $`r` there is an internal
set that contains every real number $`a \ge r` but, for every positive unlimited $`b`, omits
some hyperreal $`a` with $`r \le a \le b`. With an unlimited hypernatural $`K`, the set
consists of the hyperreals $`a` for which it is not the case that $`r < a` and
$`(a - r) K < 1`; the omitted point is $`r + 1/(2K + 2)`. -/
theorem not_theorem_15_1_1_5_as_printed (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (r : ℝ) :
    ∃ A, F.Internal A ∧ (∀ a : ℝ, r ≤ a → F.real a ∈ A) ∧
      ∀ b, F.PosUnlimited b →
        ∃ a, pair (F.real r) a ∈ F.star F.Le ∧ pair a b ∈ F.star F.Le ∧ a ∉ A := by
  obtain ⟨hRint, hRset⟩ := F.star_R_spec
  obtain ⟨K, hK, hKN⟩ := hω
  have hKR : K ∈ F.star F.R := F.star_N_subset_star_R hK
  have hKun := posUnlimited_of_nonstandard hK hKN
  set Q := F.rr (fun x m => r < x ∧ (x - r) * m < 1) with hQ
  refine ⟨F.star F.R \ relPreimage (F.star Q) {K},
    F.internal_sdiff hRint hRset (internal_relPreimage_star (Code.isSetOf_rel _ _ _)
      (Code.relIn_rel _ _ _) (F.internal_singleton (internal_of_mem_star_R hKR))), ?_, ?_⟩
  · intro a hra
    refine mem_sdiff.2 ⟨F.real_mem_star a, fun hmem => ?_⟩
    obtain ⟨K₂, hK₂, haK⟩ := mem_relPreimage.1 hmem
    obtain rfl := mem_singleton.1 hK₂
    have h1 := (Code.pair_enc_left_mem_star_rel F.cR F.cR (a := a)).1 haK
    have h2 : K₂ ∈ F.star (F.cR.set (Set.Iio (1 / (a - r)))) :=
      F.cR.star_set_mono (fun m (hm : r < a ∧ (a - r) * m < 1) => by
        show m < 1 / (a - r)
        rw [lt_div_iff₀ (sub_pos.2 hm.1)]
        linarith [hm.2, mul_comm (a - r) m]) h1
    exact lt_irrefl' ((lt_real_iff.2 h2).trans (hKun _))
  · intro b hb
    obtain ⟨a₀, ha₀⟩ := Code.exists_pair_mem_star_graph F.cR F.cR
      (fun m : ℝ => r + 1 / (2 * |m| + 2)) (F.mem_star_R_iff.1 hKR)
    have hpos : ∀ m : ℝ, (0 : ℝ) < 2 * |m| + 2 := fun m => by positivity
    have h1 : a₀ ∈ F.star (F.cR.set (Set.Ici r)) :=
      Code.mem_right_of_rel F.cR F.cR (P := fun m x => x = r + 1 / (2 * |m| + 2))
        (fun m x hx => by
          show r ≤ x
          rw [hx]
          have := one_div_pos.2 (hpos m)
          linarith) ha₀
    have h2 : a₀ ∈ F.star (F.cR.set (Set.Iic (r + 1))) :=
      Code.mem_right_of_rel F.cR F.cR (P := fun m x => x = r + 1 / (2 * |m| + 2))
        (fun m x hx => by
          show x ≤ r + 1
          rw [hx]
          have : 1 / (2 * |m| + 2) ≤ 1 := by
            rw [div_le_one (hpos m)]
            linarith [abs_nonneg m]
          linarith) ha₀
    refine ⟨a₀, real_le_iff.2 h1, F.le_trans (le_real_iff.2 h2) (hb (r + 1)).le, fun hmem => ?_⟩
    refine (mem_sdiff.1 hmem).2 (mem_relPreimage.2 ⟨K, mem_singleton.2 rfl, ?_⟩)
    refine Code.rel_mono F.cR F.cR (P := fun x m => x = r + 1 / (2 * |m| + 2)) ?_
      ((Code.rel_swap F.cR F.cR).1 ha₀)
    intro x m hx
    have h3 := one_div_pos.2 (hpos m)
    refine ⟨by rw [hx]; linarith, ?_⟩
    rw [hx, add_sub_cancel_left, div_mul_eq_mul_div, one_mul, div_lt_one (hpos m)]
    linarith [le_abs_self m, abs_nonneg m]

/-- **Theorem 15.1.1 (5), corrected.** Let $`\varphi(x)` be an internal formula and $`r`
a real number. If $`\varphi(a)` is true for all limited hyperreals $`a \ge r`, then there is
a positive unlimited $`b` such that $`\varphi(a)` is true for all hyperreals $`a` with
$`r \le a \le b`. See {lit}`exists_posUnlimited_forall_mem` for the reason why "limited
hyperreals" replaces the book's "real numbers". -/
theorem exists_posUnlimited_forall_trueAt (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N)
    (hφ : F.IsInternalFormula φ v) (r : ℝ)
    (h : ∀ a, F.Limited a → pair (F.real r) a ∈ F.star F.Le → F.TrueAt φ v a) :
    ∃ b, F.PosUnlimited b ∧
      ∀ a, pair (F.real r) a ∈ F.star F.Le → pair a b ∈ F.star F.Le → F.TrueAt φ v a := by
  obtain ⟨b, hb, hall⟩ := exists_posUnlimited_forall_mem hω
    (internal_sep_trueAt hφ F.star_R_spec.1 F.star_R_spec.2) r
    fun a ha hra => mem_sep.2 ⟨ha.mem, h a ha hra⟩
  exact ⟨b, hb, fun a hra hab => (mem_sep.1 (hall a hra hab)).2⟩

/-!
### Further permanence results

After Theorem 15.1.1 the book remarks that there are further results of the same kind,
analogous to Exercise 11.5.2 and to the observations of Section 11.6, and leaves their
formulation to the reader. Two of them are needed below and are proved here: an internal set
of limited numbers is bounded by a standard natural number, and an internal set that
contains all limited numbers contains all hyperreals of absolute value at most some
unlimited number.
-/

/-- **Section 15.1 (cf. Exercise 11.5.2 (ii)).** If every member of an internal entity
$`V` is a limited hyperreal, then there is a standard natural number $`n` with
$`-n < v < n` for all $`v \in V`. -/
theorem exists_nat_bound_of_forall_limited (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N)
    (hV : F.Internal V) (h : ∀ v ∈ V, F.Limited v) :
    ∃ n : ℕ, ∀ v ∈ V, F.Lt (F.real (-n)) v ∧ F.Lt v (F.real n) := by
  obtain ⟨hNint, hNset⟩ := F.star_N_spec
  set Q := F.rr (fun v m => m ≤ |v|) with hQ
  set B := F.star F.N \ relImage (F.star Q) V with hB
  have hBint : F.Internal B :=
    F.internal_sdiff hNint hNset
      (internal_relImage_star (Code.isSetOf_rel _ _ _) (Code.relIn_rel _ _ _) hV)
  obtain ⟨K, hK, hKN⟩ := hω
  obtain ⟨k, hk⟩ := underflow_set hBint hK hKN (by
    intro n hn hnN _
    refine mem_sdiff.2 ⟨hn, fun hmem => ?_⟩
    obtain ⟨w, hw, hwn⟩ := mem_relImage.1 hmem
    obtain ⟨r, hr⟩ := limited_iff.1 (h w hw)
    have h1 := Code.rel_of_mem_left F.cR F.cR hr hwn
    have h2 : n ∈ F.star (F.cR.set (Set.Iio r)) :=
      Code.mem_right_of_rel F.cR F.cR (P := fun v m => v ∈ {x : ℝ | |x| < r} ∧ m ≤ |v|)
        (fun v m hvm => _root_.lt_of_le_of_lt hvm.2 hvm.1) h1
    exact lt_irrefl' ((lt_real_iff.2 h2).trans (posUnlimited_of_nonstandard hn hnN r)))
  refine ⟨k, fun w hw => ?_⟩
  have hkB := hk k le_rfl
  have hwR : w ∈ F.star (F.cR.set Set.univ) := F.mem_star_R_iff.1 (h w hw).mem
  have hkR : F.nat k ∈ F.star (F.cR.set Set.univ) :=
    F.mem_star_R_iff.1 (F.real_mem_star k)
  rcases Code.rel_total F.cR F.cR (P := fun v m => |v| < m) (Q := fun v m => m ≤ |v|)
    (fun v m => lt_or_ge |v| m) hwR hkR with h1 | h1
  · exact lt_and_lt_iff.2
      ((Code.pair_enc_right_mem_star_rel F.cR F.cR (b := (k : ℝ))).1 h1)
  · exact absurd (mem_relImage.2 ⟨w, hw, h1⟩) (mem_sdiff.1 hkB).2

/-- **Exercise 15.1.2.** Let $`f` be an internal function with values in
$`{}^*\mathbb R` such that $`f(x)` is limited for all $`x` in an internal set
$`A \subseteq \operatorname{dom} f`. Then there is a standard $`n \in \mathbb N` with
$`|f(x)| < n`, that is $`-n < f(x) < n`, for all $`x \in A`. -/
theorem exists_nat_bound_of_limited_values (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N)
    (hf : F.Internal f) (hfset : IsSetOf F.U' f) (hrel : RelIn F.U' f) (hfun : IsFunction f)
    (hA : F.Internal A) (hAf : A ⊆ dom f) (h : ∀ x ∈ A, F.Limited (app f x)) :
    ∃ n : ℕ, ∀ x ∈ A, F.Lt (F.real (-n)) (app f x) ∧ F.Lt (app f x) (F.real n) := by
  obtain ⟨n, hn⟩ := exists_nat_bound_of_forall_limited hω
    (F.internal_relImage hf hfset hrel hA) (by
      intro w hw
      obtain ⟨x, hx, hxw⟩ := mem_relImage.1 hw
      rw [← hfun.app_eq hxw]
      exact h x hx)
  exact ⟨n, fun x hx => hn _ (mem_relImage.2 ⟨x, hx, hfun.pair_app_mem (hAf hx)⟩)⟩

/-- **Section 15.1 (cf. Section 11.6).** If an internal entity $`X` contains every
limited hyperreal, then there is a positive unlimited $`b` such that $`X` contains every
hyperreal $`a` with $`|a| \le b`, that is, the whole interval $`[-b, b]`. The condition
$`|a| \le b` is expressed by the transform of the relation $`|x| \le y` on the reals. -/
theorem exists_posUnlimited_interval_subset (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N)
    (hX : F.Internal X) (h : ∀ a, F.Limited a → a ∈ X) :
    ∃ b, F.PosUnlimited b ∧ ∀ a, pair a b ∈ F.star (F.rr fun x y => |x| ≤ y) → a ∈ X := by
  obtain ⟨hNint, hNset⟩ := F.star_N_spec
  obtain ⟨hRint, hRset⟩ := F.star_R_spec
  set Q := F.rr (fun x y => |x| ≤ y) with hQ
  set B := F.star F.N \ relImage (F.star Q) (F.star F.R \ X) with hB
  have hBint : F.Internal B :=
    F.internal_sdiff hNint hNset
      (internal_relImage_star (Code.isSetOf_rel _ _ _) (Code.relIn_rel _ _ _)
        (F.internal_sdiff hRint hRset hX))
  obtain ⟨K, hK, hKN, hKB⟩ := exists_nonstandard_mem hω hBint (by
    intro m hm
    obtain ⟨j, rfl⟩ := F.mem_N.1 hm
    refine mem_sdiff.2 ⟨F.N_subset_star hm, fun hj => ?_⟩
    obtain ⟨a, ha, haj⟩ := mem_relImage.1 hj
    refine (mem_sdiff.1 ha).2 (h a (limited_iff.2 ⟨(j : ℝ) + 1, ?_⟩))
    have := (Code.pair_enc_right_mem_star_rel F.cR F.cR (b := (j : ℝ))).1 haj
    exact F.cR.star_set_mono (fun x (hx : |x| ≤ (j : ℝ)) => by
      show |x| < (j : ℝ) + 1
      linarith) this)
  refine ⟨K, posUnlimited_of_nonstandard hK hKN, fun a haK => ?_⟩
  by_contra haX
  have haR : a ∈ F.star F.R :=
    F.mem_star_R_iff.2 (Code.mem_of_pair_mem_star_rel F.cR F.cR haK).1
  exact (mem_sdiff.1 hKB).2 (mem_relImage.2 ⟨a, mem_sdiff.2 ⟨haR, haX⟩, haK⟩)

/-!
## 15.2 Robinson's Sequential Lemma

An internal hypersequence whose terms at the standard natural numbers are all infinitesimal
keeps infinitesimal terms up to some unlimited index. Overflow cannot be applied to the
property "the term is infinitesimal", which is not internal. It is applied to the internal
property $`|n \cdot s_n| < 1`, which holds at standard $`n` and, at an unlimited $`n`,
forces $`s_n` to be infinitesimal.

The lemma is proved first in a general form, for the terms being infinitely close to a fixed
hyperreal $`c` and for an internal function whose domain need not be all of
$`{}^*\mathbb N`. This covers Lemma 15.2.1, the remark after it on hypersequences defined
only up to an unlimited index, and Exercise 15.2.2.
-/

/-- **Exercise 15.2.2, general form.** Let $`s` be an internal function with
$`\mathbb N \subseteq \operatorname{dom} s` and $`c` a hyperreal. If $`s_n \simeq c` for all
standard $`n`, then there is an unlimited hypernatural $`K` such that every hypernatural
$`n \le K` is in the domain of $`s` and has $`s_n \simeq c`. The internal property used for
overflow is $`|n (s_n - c)| < 1`. -/
theorem robinson_near (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hs : F.Internal s)
    (hsset : IsSetOf F.U' s) (hrel : RelIn F.U' s) (hfun : IsFunction s) (hc : c ∈ F.star F.R)
    (h : ∀ n : ℕ, F.nat n ∈ dom s ∧ F.Near (app s (F.nat n)) c) :
    ∃ K, K ∈ F.star F.N ∧ K ∉ F.N ∧
      ∀ n ∈ F.star F.N, pair n K ∈ F.star F.Le → n ∈ dom s ∧ F.Near (app s n) c := by
  set cRR := F.cR.prod F.cR with hcRR
  set Rob := Code.rel cRR F.cR (fun q y => |q.1 * (y - q.2)| < 1) with hRob
  have hcR := F.mem_star_R_iff.1 hc
  obtain ⟨hRobint, hRobset, hRobrel⟩ :=
    star_rel_spec (F := F.toNonstandardFramework) (Code.isSetOf_rel cRR F.cR _)
      (Code.relIn_rel cRR F.cR fun q y => |q.1 * (y - q.2)| < 1)
  set W := Code.sect F.cR F.cR (F.star Rob) c with hW
  obtain ⟨hWint, hWset, hWrel⟩ := Code.sect_spec F.cR F.cR hRobint hRobset hRobrel hcR
  have hAint : F.Internal (dom (s ∩ W)) :=
    F.internal_dom (F.internal_inter hs hsset hWint) (F.isUniverse'.isSetOf_inter hsset)
      fun p hp => hrel p (mem_inter.1 hp).1
  have hsnd : ∀ {m : ZFSet.{u}}, m ∈ F.star F.R →
      pair (pair m c) c ∈ F.star (Code.rel cRR F.cR fun q b => b = q.2) := fun hm =>
    (Code.pair_pair_mem_star_snd F.cR F.cR).2 ⟨F.mem_star_R_iff.1 hm, hcR, rfl⟩
  have hfst : ∀ {m : ZFSet.{u}}, m ∈ F.star F.R →
      pair (pair m c) m ∈ F.star (Code.rel cRR F.cR fun q b => b = q.1) := fun hm =>
    (Code.pair_pair_mem_star_fst F.cR F.cR).2 ⟨F.mem_star_R_iff.1 hm, hcR, rfl⟩
  obtain ⟨K, hK, hKN, hall⟩ := overflow_set hω hAint 0 (by
    intro n _
    obtain ⟨hdom, hnear⟩ := h n
    refine mem_dom.2 ⟨app s (F.nat n), mem_inter.2 ⟨hfun.pair_app_mem hdom, ?_⟩⟩
    have hnR : F.nat n ∈ F.star F.R := F.real_mem_star n
    refine (Code.pair_mem_sect F.cR F.cR hcR).2 ⟨F.mem_star_R_iff.1 hnR, ?_⟩
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hw : F.Within (1 / ((n : ℝ) + 1)) c (app s (F.nat n)) :=
      (hnear _ (one_div_pos.2 hpos)).symm
    have h1 := Code.rel_comp cRR F.cR F.cR (P := fun q b => b = q.2)
      (Q := fun x y => |x - y| < 1 / ((n : ℝ) + 1))
      (R := fun q y => |q.2 - y| < 1 / ((n : ℝ) + 1))
      (fun q b y hb hby => by subst hb; exact hby) (hsnd hnR) hw
    have h2 : pair (F.nat n) c ∈ F.star (cRR.set {q | q.1 = (n : ℝ)}) :=
      (Code.pair_enc_right_mem_star_rel cRR F.cR (b := (n : ℝ))).1
        (Code.rel_mono cRR F.cR (fun q b (hb : b = q.1) => hb.symm) (hfst hnR))
    refine Code.rel_mono cRR F.cR ?_ (Code.rel_of_mem_left cRR F.cR h2 h1)
    rintro q y ⟨hq, hy⟩
    show |q.1 * (y - q.2)| < 1
    rw [Set.mem_ofPred_eq] at hq
    rw [hq, abs_mul, abs_sub_comm, abs_of_nonneg (Nat.cast_nonneg n)]
    rw [lt_div_iff₀ hpos] at hy
    nlinarith [abs_nonneg (q.2 - y)])
  refine ⟨K, hK, hKN, fun n hn hnK => ?_⟩
  by_cases hnN : n ∈ F.N
  · obtain ⟨j, rfl⟩ := F.mem_N.1 hnN
    exact h j
  obtain ⟨y, hy⟩ := mem_dom.1 (hall n hn (nat_zero_le hn) hnK)
  obtain ⟨hys, hyW⟩ := mem_inter.1 hy
  refine ⟨mem_dom.2 ⟨y, hys⟩, ?_⟩
  rw [hfun.app_eq hys]
  have hnR : n ∈ F.star F.R := F.star_N_subset_star_R hn
  have hRobn := ((Code.pair_mem_sect F.cR F.cR hcR).1 hyW).2
  intro r hr
  have hlt : F.Lt (F.real (1 / r)) n := posUnlimited_of_nonstandard hn hnN (1 / r)
  have h1 : pair (pair n c) n ∈
      F.star (Code.rel cRR F.cR fun q b => b ∈ Set.Ioi (1 / r) ∧ b = q.1) :=
    Code.rel_of_mem_right cRR F.cR (real_lt_iff.1 hlt) (hfst hnR)
  have h2 : pair n c ∈ F.star (cRR.set {q | 1 / r < q.1}) :=
    Code.mem_left_of_rel cRR F.cR (P := fun q b => b ∈ Set.Ioi (1 / r) ∧ b = q.1)
      (fun q b hb => by
        show 1 / r < q.1
        rw [← hb.2]
        exact hb.1) h1
  have h3 := Code.rel_of_mem_left cRR F.cR h2 hRobn
  have h4 := Code.rel_comp F.cR cRR F.cR (P := fun b q => b = q.2)
    (Q := fun q y => q ∈ {q : ℝ × ℝ | 1 / r < q.1} ∧ |q.1 * (y - q.2)| < 1)
    (R := fun b y => |b - y| < r)
    (fun b q y hb hq => by
      subst hb
      obtain ⟨hq1, hq2⟩ := hq
      rw [Set.mem_ofPred_eq] at hq1
      have hpos : 0 < q.1 := _root_.lt_trans (one_div_pos.2 hr) hq1
      rw [abs_mul, abs_of_pos hpos] at hq2
      rw [abs_sub_comm]
      have h5 : 1 < r * q.1 := by
        have := (div_lt_iff₀ hr).1 hq1
        linarith [mul_comm q.1 r]
      nlinarith [abs_nonneg (y - q.2)])
    ((Code.rel_swap cRR F.cR).1 (hsnd hnR)) h3
  exact Within.symm h4

/-- **Lemma 15.2.1, for internal functions.** Let $`s` be an internal function with
$`\mathbb N \subseteq \operatorname{dom} s` such that $`s_n` is infinitesimal for all
standard $`n`. Then there is an unlimited $`K` such that every hypernatural $`n \le K` is in
the domain of $`s` and $`s_n` is infinitesimal. This is the form the book describes after
the proof of the lemma, for hypersequences defined on $`\{n \in {}^*\mathbb N : n \le N\}`
with $`N` unlimited; no assumption on the domain beyond containing the standard numbers is
needed. -/
theorem robinson_function (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hs : F.Internal s)
    (hsset : IsSetOf F.U' s) (hrel : RelIn F.U' s) (hfun : IsFunction s)
    (h : ∀ n : ℕ, F.nat n ∈ dom s ∧ F.Infinitesimal (app s (F.nat n))) :
    ∃ K, K ∈ F.star F.N ∧ K ∉ F.N ∧
      ∀ n ∈ F.star F.N, pair n K ∈ F.star F.Le → n ∈ dom s ∧ F.Infinitesimal (app s n) := by
  obtain ⟨K, hK, hKN, hall⟩ := robinson_near hω hs hsset hrel hfun (F.real_mem_star 0)
    fun n => ⟨(h n).1, near_zero_iff.2 (h n).2⟩
  exact ⟨K, hK, hKN, fun n hn hnK =>
    ⟨(hall n hn hnK).1, near_zero_iff.1 (hall n hn hnK).2⟩⟩

/-- An internal function between sets of the nonstandard universe is a set of pairs of that
universe. -/
theorem isFunc_spec {D E : ZFSet.{u}} (hD : IsSetOf F.U' D) (hE : IsSetOf F.U' E)
    (hs : IsFunc D E s) : IsSetOf F.U' s ∧ RelIn F.U' s ∧ IsFunction s ∧ dom s = D :=
  ⟨F.isUniverse'.isSetOf_of_subset_prod hD hE hs.1,
    F.isUniverse'.relIn_of_subset_prod hD hE hs.1, hs.isFunction, hs.dom_eq⟩

/-- **Lemma 15.2.1 (Robinson's sequential lemma).** If
$`s : {}^*\mathbb N \to {}^*\mathbb R` is an internal hypersequence such that $`s_n` is
infinitesimal for all standard $`n`, then there is an unlimited $`K \in {}^*\mathbb N` such
that $`s_n` is infinitesimal for all hypernatural $`n \le K`. -/
theorem robinson_sequential_lemma (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hs : F.Internal s)
    (hsf : IsFunc (F.star F.N) (F.star F.R) s)
    (h : ∀ n : ℕ, F.Infinitesimal (app s (F.nat n))) :
    ∃ K, K ∈ F.star F.N ∧ K ∉ F.N ∧
      ∀ n ∈ F.star F.N, pair n K ∈ F.star F.Le → F.Infinitesimal (app s n) := by
  obtain ⟨hsset, hrel, hfun, hdom⟩ := isFunc_spec F.star_N_spec.2 F.star_R_spec.2 hsf
  obtain ⟨K, hK, hKN, hall⟩ := robinson_function hω hs hsset hrel hfun fun n =>
    ⟨hdom ▸ F.N_subset_star (F.mem_N.2 ⟨n, rfl⟩), h n⟩
  exact ⟨K, hK, hKN, fun n hn hnK => (hall n hn hnK).2⟩

/-- **Exercise 15.2.2.** If $`c \in {}^*\mathbb R` and
$`s : {}^*\mathbb N \to {}^*\mathbb R` is an internal hypersequence such that
$`s_n \simeq c` for all standard $`n`, then there is an unlimited $`K \in {}^*\mathbb N` such
that $`s_n \simeq c` for all hypernatural $`n \le K`. The version for a hypersequence
defined up to an unlimited index is {lit}`robinson_near`. -/
theorem robinson_near_sequence (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hs : F.Internal s)
    (hsf : IsFunc (F.star F.N) (F.star F.R) s) (hc : c ∈ F.star F.R)
    (h : ∀ n : ℕ, F.Near (app s (F.nat n)) c) :
    ∃ K, K ∈ F.star F.N ∧ K ∉ F.N ∧
      ∀ n ∈ F.star F.N, pair n K ∈ F.star F.Le → F.Near (app s n) c := by
  obtain ⟨hsset, hrel, hfun, hdom⟩ := isFunc_spec F.star_N_spec.2 F.star_R_spec.2 hsf
  obtain ⟨K, hK, hKN, hall⟩ := robinson_near hω hs hsset hrel hfun hc fun n =>
    ⟨hdom ▸ F.N_subset_star (F.mem_N.2 ⟨n, rfl⟩), h n⟩
  exact ⟨K, hK, hKN, fun n hn hnK => (hall n hn hnK).2⟩

/-- **Theorem 15.2.3.** If $`f` is an internal function with values in
$`{}^*\mathbb R` and $`f(x)` is infinitesimal for all limited hyperreals $`x`, then there is
a positive unlimited $`b` such that $`f(x)` is infinitesimal for all $`x \in [-b, b]`, that
is, for all hyperreals with $`|x| \le b`. The internal set of the $`x` with
$`|x \cdot f(x)| < 1` includes the limited numbers, hence an interval $`[-b, b]` with $`b`
unlimited. -/
theorem infinitesimal_on_unlimited_interval (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N)
    (hf : F.Internal f) (hfset : IsSetOf F.U' f) (hrel : RelIn F.U' f) (hfun : IsFunction f)
    (h : ∀ x, F.Limited x → x ∈ dom f ∧ F.Infinitesimal (app f x)) :
    ∃ b, F.PosUnlimited b ∧
      ∀ x, pair x b ∈ F.star (F.rr fun x y => |x| ≤ y) →
        x ∈ dom f ∧ F.Infinitesimal (app f x) := by
  set Rob := F.rr (fun x y => |x * y| < 1) with hRob
  obtain ⟨hRobint, hRobset, hRobrel⟩ :=
    star_rel_spec (F := F.toNonstandardFramework) (Code.isSetOf_rel F.cR F.cR _)
      (Code.relIn_rel F.cR F.cR fun x y => |x * y| < 1)
  have hXint : F.Internal (dom (f ∩ F.star Rob)) :=
    F.internal_dom (F.internal_inter hf hfset hRobint) (F.isUniverse'.isSetOf_inter hfset)
      fun p hp => hrel p (mem_inter.1 hp).1
  obtain ⟨b, hb, hall⟩ := exists_posUnlimited_interval_subset hω hXint (by
    intro x hx
    obtain ⟨hdom, hinf⟩ := h x hx
    refine mem_dom.2 ⟨app f x, mem_inter.2 ⟨hfun.pair_app_mem hdom, ?_⟩⟩
    obtain ⟨r, hr⟩ := limited_iff.1 hx
    have hy := infinitesimal_iff.1 hinf (1 / (|r| + 1)) (by positivity)
    have h0 := (Code.pair_mem_star_rel_true F.cR F.cR).2
      ⟨F.mem_star_R_iff.1 hx.mem, F.mem_star_R_iff.1 hinf.mem⟩
    refine Code.rel_mono F.cR F.cR ?_
      (Code.rel_of_mem_left F.cR F.cR hr (Code.rel_of_mem_right F.cR F.cR hy h0))
    rintro u w ⟨hu, hw, -⟩
    show |u * w| < 1
    rw [Set.mem_ofPred_eq] at hu hw
    have hpos : (0 : ℝ) < |r| + 1 := by positivity
    rw [lt_div_iff₀ hpos] at hw
    rw [abs_mul]
    have hur : |u| < |r| + 1 := by linarith [le_abs_self r]
    nlinarith [abs_nonneg u, abs_nonneg w])
  refine ⟨b, hb, fun x hxb => ?_⟩
  obtain ⟨y, hy⟩ := mem_dom.1 (hall x hxb)
  obtain ⟨hyf, hyR⟩ := mem_inter.1 hy
  refine ⟨mem_dom.2 ⟨y, hyf⟩, ?_⟩
  by_cases hlim : F.Limited x
  · exact (h x hlim).2
  rw [hfun.app_eq hyf, infinitesimal_iff]
  intro r hr
  have hxR := (Code.mem_of_pair_mem_star_rel F.cR F.cR hyR).1
  have hx' : x ∈ F.star (F.cR.set {u : ℝ | |u| < 1 / r}ᶜ) :=
    (F.cR.mem_star_set_or_compl _ hxR).resolve_left fun hx => hlim (limited_iff.2 ⟨_, hx⟩)
  refine Code.mem_right_of_rel F.cR F.cR ?_ (Code.rel_of_mem_left F.cR F.cR hx' hyR)
  rintro u w ⟨hu, hw⟩
  show |w| < r
  rw [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hu
  rw [abs_mul] at hw
  have hupos : 0 < |u| := _root_.lt_of_lt_of_le (one_div_pos.2 hr) hu
  have h5 : 1 ≤ r * |u| := by
    have := (div_le_iff₀ hr).1 hu
    linarith [mul_comm |u| r]
  nlinarith [abs_nonneg w]

end RealFramework

end Goldblatt
