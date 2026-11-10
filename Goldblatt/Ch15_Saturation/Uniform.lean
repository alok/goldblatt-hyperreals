import Goldblatt.Ch15_Saturation.Permanence

/-!
# 15 (part 4). Uniformly converging sequences of functions: Section 15.3

This is the fourth of seven parts of Chapter 15 (the overview is on the chapter page
{lit}`Goldblatt.Ch15_Saturation`). It carries out, in an arbitrary framework over the real
numbers with a nonstandard hypernatural number, the proof by Robinson's sequential lemma that
a uniform limit of continuous functions is continuous, and proves the characterization of
uniform convergence that the argument rests on, together with its converse (Exercise
15.3.1).
-/

noncomputable section

namespace Goldblatt

open ZFSet NonstandardFramework

universe u

namespace RealFramework

variable {F : RealFramework.{u}} {n x K : ZFSet.{u}} {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {S : Set ℝ}
  {c : ℝ}

/-!
## 15.3 Uniformly Converging Sequences of Functions

A sequence $`(f_n)` of real functions is a function of two variables, and its transform
assigns a hyperreal $`{}^*f_n(x)` to every hypernatural $`n` and hyperreal $`x`; for fixed
$`n` this is the internal function $`{}^*f_n` of the book. Uniform convergence of $`f_n` to
$`g` on a set $`S` is equivalent to the condition, called (i) in the book, that
$`{}^*f_n(x) \simeq {}^*g(x)` for all unlimited $`n` and all $`x \in {}^*S`.

Given this, continuity of the limit is proved as follows. Let $`c \in S` and $`x \simeq c`
in $`{}^*S`. For standard $`n` the number $`|{}^*f_n(x) - {}^*f_n(c)|` is infinitesimal
because $`f_n` is continuous. These numbers form an internal hypersequence, so by Robinson's
lemma the same holds for some unlimited $`K`. By (i), $`{}^*f_K(x) \simeq {}^*g(x)` and
$`{}^*f_K(c) \simeq g(c)`, and therefore $`{}^*g(x) \simeq g(c)`.

In the formalization a sequence of functions is a function
{lit}`f : ℕ → ℝ → ℝ`, the set $`S` is arbitrary (the book takes a closed interval), and the
function of two variables is coded on pairs of real numbers, the first component being
rounded down to a natural number.
-/

/-- **Section 15.3.** A sequence of real functions as a function on pairs of real numbers:
the pair $`(t, x)` is sent to $`f_{\lfloor t \rfloor}(x)`. -/
def seqFn (f : ℕ → ℝ → ℝ) (q : ℝ × ℝ) : ℝ := f ⌊q.1⌋₊ q.2

variable (F) in
/-- **Section 13.8.** The value $`{}^*g(x)` of the transform of a real function at a
hyperreal. -/
def ext (g : ℝ → ℝ) (x : ZFSet.{u}) : ZFSet.{u} := Code.ap F.cR F.cR g x

variable (F) in
/-- **Section 15.3, the extended sequence.** The value $`{}^*f_n(x)` of the transform of a
sequence of real functions at a hypernatural $`n` and a hyperreal $`x`. -/
def hseq (f : ℕ → ℝ → ℝ) (n x : ZFSet.{u}) : ZFSet.{u} :=
  Code.ap (F.cR.prod F.cR) F.cR (seqFn f) (pair n x)

/-- The extended function takes hyperreals to hyperreals. -/
theorem ext_mem (hx : x ∈ F.star F.R) : F.ext g x ∈ F.star F.R :=
  F.mem_star_R_iff.2 (Code.ap_mem F.cR F.cR (F.mem_star_R_iff.1 hx))

/-- **Section 13.8.** The extended function agrees with the original one on real
numbers. -/
@[simp]
theorem ext_real (r : ℝ) : F.ext g (F.real r) = F.real (g r) := Code.ap_enc F.cR F.cR r

/-- The extended sequence takes hyperreal values. -/
theorem hseq_mem (hn : n ∈ F.star F.R) (hx : x ∈ F.star F.R) : F.hseq f n x ∈ F.star F.R :=
  F.mem_star_R_iff.2 (Code.ap_mem (F.cR.prod F.cR) F.cR
    (Code.pair_mem_star_prod_univ F.cR F.cR (F.mem_star_R_iff.1 hn) (F.mem_star_R_iff.1 hx)))

/-- **Section 15.3.** For standard $`n` and $`x`, $`{}^*f_n(x) = f_n(x)`. -/
theorem hseq_nat_real (m : ℕ) (r : ℝ) : F.hseq f (F.nat m) (F.real r) = F.real (f m r) := by
  have := Code.ap_enc (F.cR.prod F.cR) F.cR (g := seqFn f) ((m : ℝ), r)
  simpa [seqFn, hseq, RealFramework.nat] using this

/-- The basic transfer step of this section: a condition on the pair $`(n, x)` yields the
corresponding relation between $`{}^*f_n(x)` and $`{}^*g(x)`. -/
theorem hseq_ext_rel (hn : n ∈ F.star F.R) (hx : x ∈ F.star F.R) {S₂ : Set (ℝ × ℝ)}
    (hp : pair n x ∈ F.star ((F.cR.prod F.cR).set S₂)) :
    pair (F.hseq f n x) (F.ext g x) ∈
      F.star (F.rr fun u w => ∃ q ∈ S₂, u = seqFn f q ∧ w = g q.2) := by
  have hnR := F.mem_star_R_iff.1 hn
  have hxR := F.mem_star_R_iff.1 hx
  have h1 := Code.pair_ap_mem (F.cR.prod F.cR) F.cR (g := seqFn f)
    (Code.pair_mem_star_prod_univ F.cR F.cR hnR hxR)
  have h1' := Code.rel_of_mem_left (F.cR.prod F.cR) F.cR hp h1
  have hsnd := (Code.pair_pair_mem_star_snd F.cR F.cR).2 ⟨hnR, hxR, rfl⟩
  have h2 := Code.pair_ap_mem F.cR F.cR (g := g) hxR
  have h3 := Code.rel_comp (F.cR.prod F.cR) F.cR F.cR (P := fun q b => b = q.2)
    (Q := fun a b => b = g a) (R := fun q w => w = g q.2)
    (fun q b w hb hw => by rw [hw, hb]) hsnd h2
  exact Code.rel_comp F.cR (F.cR.prod F.cR) F.cR
    (P := fun u q => q ∈ S₂ ∧ u = seqFn f q) (Q := fun q w => w = g q.2)
    (R := fun u w => ∃ q ∈ S₂, u = seqFn f q ∧ w = g q.2)
    (fun u q w hu hw => ⟨q, hu.1, hu.2, hw⟩)
    ((Code.rel_swap (F.cR.prod F.cR) F.cR).1 h1') h3

/-- **Section 15.3.** For standard $`n`, the function $`x \mapsto {}^*f_n(x)` is the
transform of $`f_n`. -/
theorem hseq_nat (m : ℕ) (hx : x ∈ F.star F.R) : F.hseq f (F.nat m) x = F.ext (f m) x := by
  have hnR : F.nat m ∈ F.star F.R := F.real_mem_star m
  have hp : pair (F.nat m) x ∈
      F.star ((F.cR.prod F.cR).set (({(m : ℝ)} : Set ℝ) ×ˢ (Set.univ : Set ℝ))) :=
    (Code.pair_mem_star_prod_set F.cR F.cR).2
      ⟨(F.cR.enc_mem_star_set (a := (m : ℝ))).2 rfl, F.mem_star_R_iff.1 hx⟩
  have h := hseq_ext_rel (f := f) (g := f m) hnR hx hp
  have h' : pair (F.hseq f (F.nat m) x) (F.ext (f m) x) ∈ F.star (F.rr fun u w => u = w) := by
    refine Code.rel_mono F.cR F.cR ?_ h
    rintro u w ⟨q, hq, hu, hw⟩
    have hq1 : q.1 = (m : ℝ) := hq.1
    rw [hu, hw, seqFn, hq1, Nat.floor_natCast]
  exact ((Code.pair_mem_star_rel_eq F.cR).1 h').2

/-- A nonstandard hypernatural number belongs to the transform of every final segment of the
natural numbers. -/
theorem mem_star_nat_ge (hn : n ∈ F.star F.N) (hnN : n ∉ F.N) (k : ℕ) :
    n ∈ F.star (F.cR.set {t : ℝ | ∃ m : ℕ, t = m ∧ k ≤ m}) := by
  have h1 := F.mem_star_N_iff.1 hn
  have h2 := real_lt_iff.1 (posUnlimited_of_nonstandard hn hnN k)
  have : n ∈ F.star (F.cR.set (Set.range ((↑) : ℕ → ℝ) ∩ Set.Ioi (k : ℝ))) := by
    rw [F.cR.star_set_inter]
    exact mem_inter.2 ⟨h1, h2⟩
  refine F.cR.star_set_mono ?_ this
  rintro t ⟨⟨m, rfl⟩, hm⟩
  exact ⟨m, rfl, by exact_mod_cast le_of_lt (Set.mem_Ioi.1 hm)⟩

/-- **Section 15.3, condition (i).** If $`f_n` converges to $`g` uniformly on $`S`, then
$`{}^*f_n(x) \simeq {}^*g(x)` for every unlimited hypernatural $`n` and every
$`x \in {}^*S`. -/
theorem near_hseq_of_tendstoUniformlyOn (hu : TendstoUniformlyOn f g Filter.atTop S)
    (hn : n ∈ F.star F.N) (hnN : n ∉ F.N) (hx : x ∈ F.star (F.cR.set S)) :
    F.Near (F.hseq f n x) (F.ext g x) := by
  intro ε hε
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hu ε hε)
  have hp := (Code.pair_mem_star_prod_set F.cR F.cR).2 ⟨mem_star_nat_ge hn hnN k, hx⟩
  have h := hseq_ext_rel (f := f) (g := g) (F.star_N_subset_star_R hn)
    (mem_star_R_of_mem_star_set hx) hp
  show pair _ _ ∈ F.star (F.rr fun x y => |x - y| < ε)
  refine Code.rel_mono F.cR F.cR ?_ h
  rintro u w ⟨q, hq, hu, hw⟩
  obtain ⟨m, hm, hkm⟩ := hq.1
  have := hk m hkm q.2 hq.2
  rw [Real.dist_eq, abs_sub_comm] at this
  rw [hu, hw, seqFn, hm, Nat.floor_natCast]
  exact this

/-- **Exercise 15.3.1.** Condition (i) is sufficient for uniform convergence: if
$`{}^*f_n(x) \simeq {}^*g(x)` for every unlimited hypernatural $`n` and every
$`x \in {}^*S`, then $`f_n` converges to $`g` uniformly on $`S`. Continuity of the functions
is not needed. -/
theorem tendstoUniformlyOn_of_near (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N)
    (h : ∀ n ∈ F.star F.N, n ∉ F.N → ∀ x ∈ F.star (F.cR.set S),
      F.Near (F.hseq f n x) (F.ext g x)) :
    TendstoUniformlyOn f g Filter.atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rw [Filter.eventually_atTop]
  by_contra hcon
  push Not at hcon
  obtain ⟨K, hK, hKN⟩ := hω
  set P : ℝ → ℝ × ℝ → Prop := fun t q =>
    (∃ m : ℕ, q.1 = m ∧ t ≤ m) ∧ q.2 ∈ S ∧ ε ≤ |seqFn f q - g q.2| with hP
  have hKS : K ∈ F.star (F.cR.set {t | ∃ q, P t q}) := by
    refine F.cR.star_set_mono ?_ (F.mem_star_N_iff.1 hK)
    rintro t ⟨k, rfl⟩
    obtain ⟨m, hm, y, hy, hd⟩ := hcon k
    refine ⟨((m : ℝ), y), ⟨m, rfl, by exact_mod_cast hm⟩, hy, ?_⟩
    rw [Real.dist_eq, abs_sub_comm] at hd
    simpa [seqFn] using hd
  obtain ⟨p, hp⟩ := (Code.mem_star_set_exists F.cR (F.cR.prod F.cR)).1 hKS
  obtain ⟨n, hn, x, hx, rfl⟩ := Code.exists_pair_of_mem_star_prod_univ F.cR F.cR
    (Code.mem_of_pair_mem_star_rel F.cR (F.cR.prod F.cR) hp).2
  have hfst := (Code.pair_pair_mem_star_fst F.cR F.cR).2 ⟨hn, hx, rfl⟩
  have hsnd := (Code.pair_pair_mem_star_snd F.cR F.cR).2 ⟨hn, hx, rfl⟩
  have hKn : pair K n ∈ F.star F.Le := by
    rw [F.Le_eq]
    exact Code.rel_comp F.cR (F.cR.prod F.cR) F.cR (P := P) (Q := fun q a => a = q.1)
      (R := (· ≤ ·)) (fun t q a hq ha => by
        obtain ⟨m, hm, htm⟩ := hq.1
        rw [ha, hm]
        exact htm) hp hfst
  have hnN : n ∈ F.star F.N := by
    rw [F.mem_star_N_iff]
    exact Code.mem_right_of_rel F.cR F.cR
      (P := fun t a => ∃ q, P t q ∧ a = q.1)
      (fun t a ⟨q, hq, ha⟩ => by
        obtain ⟨m, hm, -⟩ := hq.1
        exact ⟨m, by rw [ha, hm]⟩)
      (Code.rel_comp F.cR (F.cR.prod F.cR) F.cR (P := P) (Q := fun q a => a = q.1)
        (R := fun t a => ∃ q, P t q ∧ a = q.1) (fun t q a hq ha => ⟨q, hq, ha⟩) hp hfst)
  have hxS : x ∈ F.star (F.cR.set S) :=
    Code.mem_right_of_rel F.cR F.cR
      (P := fun t a => ∃ q, P t q ∧ a = q.2)
      (fun t a ⟨q, hq, ha⟩ => by rw [ha]; exact hq.2.1)
      (Code.rel_comp F.cR (F.cR.prod F.cR) F.cR (P := P) (Q := fun q a => a = q.2)
        (R := fun t a => ∃ q, P t q ∧ a = q.2) (fun t q a hq ha => ⟨q, hq, ha⟩) hp hsnd)
  have hW := h n hnN (notMem_N_of_le hK hKN hKn) x hxS ε hε
  have hp2 : pair n x ∈ F.star ((F.cR.prod F.cR).set {q | ε ≤ |seqFn f q - g q.2|}) :=
    Code.mem_right_of_rel F.cR (F.cR.prod F.cR) (fun t q (hq : P t q) => hq.2.2) hp
  have hrel := hseq_ext_rel (f := f) (g := g) (F.mem_star_R_iff.2 hn) (F.mem_star_R_iff.2 hx)
    hp2
  exact Code.notMem_star_rel F.cR F.cR
    (P := fun u w => |u - w| < ε ∧ ∃ q ∈ {q | ε ≤ |seqFn f q - g q.2|},
      u = seqFn f q ∧ w = g q.2)
    (fun u w ⟨h1, q, hq, hu, hw⟩ => by
      rw [hu, hw] at h1
      exact absurd h1 (not_lt.2 hq))
    ((Code.rel_and F.cR F.cR).2 ⟨hW, hrel⟩)

/-- **Section 15.3 and Exercise 15.3.1.** A sequence $`f_n` of real functions converges
to $`g` uniformly on $`S` if and only if $`{}^*f_n(x) \simeq {}^*g(x)` for all unlimited
hypernaturals $`n` and all $`x \in {}^*S`. -/
theorem tendstoUniformlyOn_iff_near (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) :
    TendstoUniformlyOn f g Filter.atTop S ↔
      ∀ n ∈ F.star F.N, n ∉ F.N → ∀ x ∈ F.star (F.cR.set S),
        F.Near (F.hseq f n x) (F.ext g x) :=
  ⟨fun hu _ hn hnN _ hx => near_hseq_of_tendstoUniformlyOn hu hn hnN hx,
    tendstoUniformlyOn_of_near hω⟩

/-- **Section 15.3 (the theory of Section 7.1 in a framework).** If $`g` is continuous at
$`c` relative to $`S`, then $`{}^*g(x) \simeq g(c)` for every $`x \in {}^*S` with
$`x \simeq c`. -/
theorem near_ext_of_continuousWithinAt (hc : ContinuousWithinAt g S c)
    (hx : x ∈ F.star (F.cR.set S)) (hxc : F.Near x (F.real c)) :
    F.Near (F.ext g x) (F.real (g c)) := by
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.1 hc ε hε
  have h1 := within_real_iff.1 (hxc δ hδ)
  have h2 : x ∈ F.star (F.cR.set (S ∩ {y | |y - c| < δ})) := by
    rw [F.cR.star_set_inter]
    exact mem_inter.2 ⟨hx, h1⟩
  have hg := Code.pair_ap_mem F.cR F.cR (g := g) (F.cR.star_set_subset_univ _ hx)
  rw [within_real_iff]
  refine Code.mem_right_of_rel F.cR F.cR ?_ (Code.rel_of_mem_left F.cR F.cR h2 hg)
  rintro a b ⟨ha, hb⟩
  have := hd ha.1 (by rw [Real.dist_eq]; exact ha.2)
  rw [Real.dist_eq] at this
  show |b - g c| < ε
  rw [hb]
  exact this

/-- **Section 15.3 (the theory of Section 7.1 in a framework).** If
$`{}^*g(x) \simeq g(c)` for every $`x \in {}^*S` with $`x \simeq c`, then $`g` is continuous
at $`c` relative to $`S`. -/
theorem continuousWithinAt_of_near (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N)
    (h : ∀ x ∈ F.star (F.cR.set S), F.Near x (F.real c) → F.Near (F.ext g x) (F.real (g c))) :
    ContinuousWithinAt g S c := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  by_contra hcon
  push Not at hcon
  obtain ⟨K, hK, hKN⟩ := hω
  set P : ℝ → ℝ → Prop := fun t y => y ∈ S ∧ |y - c| * (t + 1) < 1 ∧ ε ≤ |g y - g c| with hP
  have hKS : K ∈ F.star (F.cR.set {t | ∃ y, P t y}) := by
    refine F.cR.star_set_mono ?_ (F.mem_star_N_iff.1 hK)
    rintro t ⟨k, rfl⟩
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    obtain ⟨y, hyS, hyd, hgd⟩ := hcon (1 / ((k : ℝ) + 1)) (one_div_pos.2 hpos)
    refine ⟨y, hyS, ?_, ?_⟩
    · rw [Real.dist_eq, lt_div_iff₀ hpos] at hyd
      exact hyd
    · rwa [Real.dist_eq] at hgd
  obtain ⟨x, hx⟩ := (Code.mem_star_set_exists F.cR F.cR).1 hKS
  have hxS : x ∈ F.star (F.cR.set S) :=
    Code.mem_right_of_rel F.cR F.cR (fun t y (hy : P t y) => hy.1) hx
  have hxc : F.Near x (F.real c) := by
    intro r hr
    have hlt : F.Lt (F.real (1 / r)) K := posUnlimited_of_nonstandard hK hKN _
    have h1 := Code.rel_comp F.cR F.cR F.cR (P := (· < ·)) (Q := P)
      (R := fun t y => 0 < t → |y - c| < 1 / t)
      (fun t m y htm hy ht => by
        rw [lt_div_iff₀ ht]
        have h5 := hy.2.1
        nlinarith [mul_nonneg (abs_nonneg (y - c)) (by linarith : (0 : ℝ) ≤ m + 1 - t)])
      hlt hx
    have h2 := (Code.pair_enc_left_mem_star_rel F.cR F.cR (a := 1 / r)).1 h1
    rw [within_real_iff]
    exact F.cR.star_set_mono (fun y (hy : 0 < 1 / r → |y - c| < 1 / (1 / r)) => by
      have := hy (one_div_pos.2 hr)
      rwa [one_div_one_div] at this) h2
  have hW := within_real_iff.1 (h x hxS hxc ε hε)
  have hg := Code.pair_ap_mem F.cR F.cR (g := g) (F.cR.star_set_subset_univ _ hxS)
  have hbad : x ∈ F.star (F.cR.set {y | ε ≤ |g y - g c|}) :=
    Code.mem_right_of_rel F.cR F.cR (fun t y (hy : P t y) => hy.2.2) hx
  have h3 : F.ext g x ∈ F.star (F.cR.set {w | ε ≤ |w - g c|}) :=
    Code.mem_right_of_rel F.cR F.cR
      (P := fun a b => a ∈ {y | ε ≤ |g y - g c|} ∧ b = g a)
      (fun a b hab => by
        show ε ≤ |b - g c|
        rw [hab.2]
        exact hab.1) (Code.rel_of_mem_left F.cR F.cR hbad hg)
  have hempty : ∀ w : ℝ, w ∉ ({w | |w - g c| < ε} ∩ {w | ε ≤ |w - g c|} : Set ℝ) := by
    rintro w ⟨h1, h2⟩
    exact absurd (show |w - g c| < ε from h1) (not_lt.2 h2)
  exact F.cR.notMem_star_set hempty (by
    rw [F.cR.star_set_inter]
    exact mem_inter.2 ⟨hW, h3⟩)

/-- **Section 15.3, continuity of a uniform limit, in a framework.** Let $`f_n`
converge to $`g` uniformly on $`S`, and let every $`f_n` be continuous at $`c \in S`
relative to $`S`. Then $`g` is continuous at $`c` relative to $`S`. The proof is the one of
the book: for $`x \simeq c` in $`{}^*S` the internal hypersequence
$`(|{}^*f_n(x) - {}^*f_n(c)| : n \in {}^*\mathbb N)` has infinitesimal terms at all standard
$`n`, so by Robinson's sequential lemma it has an infinitesimal term at some unlimited
$`K`; uniform convergence makes $`{}^*f_K` infinitely close to $`{}^*g` at $`x` and at
$`c`, and the three estimates combine. -/
theorem continuousWithinAt_of_tendstoUniformlyOn (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N)
    (hf : ∀ n, ContinuousWithinAt (f n) S c) (hu : TendstoUniformlyOn f g Filter.atTop S)
    (hcS : c ∈ S) : ContinuousWithinAt g S c := by
  refine continuousWithinAt_of_near hω fun x hxS hxc => ?_
  set cRR := F.cR.prod F.cR with hcRR
  set c3 := F.cR.prod cRR with hc3
  set D : ℝ × (ℝ × ℝ) → ℝ := fun T => |f ⌊T.1⌋₊ T.2.1 - f ⌊T.1⌋₊ T.2.2| with hD
  have hxR : x ∈ F.star (F.cR.set Set.univ) := F.cR.star_set_subset_univ _ hxS
  have hcR : F.real c ∈ F.star (F.cR.set Set.univ) := F.mem_star_R_iff.1 (F.real_mem_star c)
  set y₀ := pair x (F.real c) with hy₀def
  have hy₀ : y₀ ∈ F.star (cRR.set Set.univ) := Code.pair_mem_star_prod_univ F.cR F.cR hxR hcR
  obtain ⟨hGint, hGset, hGrel⟩ :=
    star_rel_spec (F := F.toNonstandardFramework) (Code.isSetOf_rel c3 F.cR _)
      (Code.relIn_rel c3 F.cR fun T b => b = D T)
  set s := Code.sect F.cR cRR (F.star (Code.graph c3 F.cR D)) y₀ with hs
  obtain ⟨hsint, hsset, hsrel⟩ := Code.sect_spec F.cR cRR hGint hGset hGrel hy₀
  have hsfun : IsFunction s := ⟨hsrel.isRel, fun a b b' hab hab' => by
    have h1 := ((Code.pair_mem_sect F.cR cRR hy₀).1 hab).2
    have h2 := ((Code.pair_mem_sect F.cR cRR hy₀).1 hab').2
    exact (Code.ap_eq_of_pair_mem c3 F.cR h1).symm.trans (Code.ap_eq_of_pair_mem c3 F.cR h2)⟩
  have hgr : ∀ m ∈ F.star (F.cR.set Set.univ),
      pair (pair m y₀) (Code.ap c3 F.cR D (pair m y₀)) ∈ F.star (Code.graph c3 F.cR D) :=
    fun m hm => Code.pair_ap_mem c3 F.cR (Code.pair_mem_star_prod_univ F.cR cRR hm hy₀)
  have hsmem : ∀ m ∈ F.star (F.cR.set Set.univ),
      pair m (Code.ap c3 F.cR D (pair m y₀)) ∈ s :=
    fun m hm => (Code.pair_mem_sect F.cR cRR hy₀).2 ⟨hm, hgr m hm⟩
  have hstd : ∀ m : ℕ, F.nat m ∈ dom s ∧ F.Infinitesimal (app s (F.nat m)) := by
    intro m
    have hmR : F.nat m ∈ F.star (F.cR.set Set.univ) :=
      F.mem_star_R_iff.1 (F.real_mem_star m)
    have hmem := hsmem (F.nat m) hmR
    refine ⟨mem_dom.2 ⟨_, hmem⟩, ?_⟩
    rw [hsfun.app_eq hmem, infinitesimal_iff]
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.1 (hf m) ε hε
    have hxδ : x ∈ F.star (F.cR.set (S ∩ {y | |y - c| < δ})) := by
      rw [F.cR.star_set_inter]
      exact mem_inter.2 ⟨hxS, within_real_iff.1 (hxc δ hδ)⟩
    have hT : pair (F.nat m) y₀ ∈ F.star (c3.set (({(m : ℝ)} : Set ℝ) ×ˢ
        ((S ∩ {y | |y - c| < δ}) ×ˢ ({c} : Set ℝ)))) :=
      (Code.pair_mem_star_prod_set F.cR cRR).2
        ⟨(F.cR.enc_mem_star_set (a := (m : ℝ))).2 rfl,
          (Code.pair_mem_star_prod_set F.cR F.cR).2
            ⟨hxδ, (F.cR.enc_mem_star_set (a := c)).2 rfl⟩⟩
    refine Code.mem_right_of_rel c3 F.cR ?_ (Code.rel_of_mem_left c3 F.cR hT (hgr _ hmR))
    rintro T w ⟨hT, hw⟩
    obtain ⟨h1, h2, h3⟩ := hT
    have h1' : T.1 = (m : ℝ) := h1
    have h3' : T.2.2 = c := h3
    have := hd h2.1 (by rw [Real.dist_eq]; exact h2.2)
    rw [Real.dist_eq] at this
    show |w| < ε
    rw [hw, hD]
    simp only [abs_abs, h1', Nat.floor_natCast, h3']
    exact this
  obtain ⟨K, hK, hKN, hall⟩ := robinson_function hω hsint hsset hsrel hsfun hstd
  have hKR : K ∈ F.star F.R := F.star_N_subset_star_R hK
  have hKR' := F.mem_star_R_iff.1 hKR
  have hinf : F.Infinitesimal (app s K) := (hall K hK (F.le_refl hKR)).2
  rw [hsfun.app_eq (hsmem K hKR')] at hinf
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hu (ε / 3) hε3)
  have hT : pair K y₀ ∈ F.star (c3.set ({t : ℝ | ∃ m : ℕ, t = m ∧ k ≤ m} ×ˢ
      (S ×ˢ ({c} : Set ℝ)))) :=
    (Code.pair_mem_star_prod_set F.cR cRR).2 ⟨mem_star_nat_ge hK hKN k,
      (Code.pair_mem_star_prod_set F.cR F.cR).2 ⟨hxS, (F.cR.enc_mem_star_set (a := c)).2 rfl⟩⟩
  have hd := infinitesimal_iff.1 hinf (ε / 3) hε3
  have h1 := Code.rel_of_mem_left c3 F.cR hT (Code.rel_of_mem_right c3 F.cR hd (hgr K hKR'))
  have hT1 : pair K y₀ ∈ F.star (c3.set {T | |g T.2.1 - g c| < ε}) := by
    refine Code.mem_left_of_rel c3 F.cR ?_ h1
    rintro T w ⟨hT, hw, hwD⟩
    obtain ⟨⟨m, hm, hkm⟩, h2, h3⟩ := hT
    have h3' : T.2.2 = c := h3
    have hw' : |w| < ε / 3 := hw
    rw [hwD, hD] at hw'
    simp only [abs_abs, hm, Nat.floor_natCast, h3'] at hw'
    have e1 := hk m hkm T.2.1 h2
    have e2 := hk m hkm c hcS
    rw [Real.dist_eq] at e1 e2
    show |g T.2.1 - g c| < ε
    have e3 : g T.2.1 - g c = (g T.2.1 - f m T.2.1) + (f m T.2.1 - f m c) - (g c - f m c) := by
      ring
    rw [e3]
    have := abs_sub (g T.2.1 - f m T.2.1 + (f m T.2.1 - f m c)) (g c - f m c)
    have := abs_add_le (g T.2.1 - f m T.2.1) (f m T.2.1 - f m c)
    linarith
  have hsnd : pair (pair K y₀) y₀ ∈ F.star (Code.rel c3 cRR fun T q => q = T.2) :=
    (Code.pair_pair_mem_star_snd F.cR cRR).2 ⟨hKR', hy₀, rfl⟩
  have hfst : pair y₀ x ∈ F.star (Code.rel cRR F.cR fun q a => a = q.1) :=
    (Code.pair_pair_mem_star_fst F.cR F.cR).2 ⟨hxR, hcR, rfl⟩
  have h2 := Code.rel_comp c3 cRR F.cR (P := fun T q => q = T.2) (Q := fun q a => a = q.1)
    (R := fun T a => a = T.2.1) (fun T q a hq ha => by rw [ha, hq]) hsnd hfst
  have h3 := Code.rel_of_mem_left c3 F.cR hT1 h2
  have hg := Code.pair_ap_mem F.cR F.cR (g := g) hxR
  have h4 := Code.rel_comp c3 F.cR F.cR
    (P := fun T a => T ∈ {T : ℝ × (ℝ × ℝ) | |g T.2.1 - g c| < ε} ∧ a = T.2.1)
    (Q := fun a b => b = g a) (R := fun _ b => |b - g c| < ε)
    (fun T a b hTa hb => by
      rw [hb, hTa.2]
      exact hTa.1) h3 hg
  rw [within_real_iff]
  exact Code.mem_right_of_rel c3 F.cR (P := fun _ b => |b - g c| < ε) (fun _ _ h => h) h4

end RealFramework

/-- **Section 15.3, the classical result.** If a sequence $`(f_n)` of continuous
real-valued functions on the closed interval $`[a, b]` converges uniformly to a function
$`g`, then $`g` is continuous. It is proved by the nonstandard argument of this section,
inside a framework over the real numbers that has a nonstandard hypernatural number; such a
framework exists by Chapter 14. -/
theorem continuousOn_of_tendstoUniformlyOn_Icc {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ n, ContinuousOn (f n) (Set.Icc a b))
    (hu : TendstoUniformlyOn f g Filter.atTop (Set.Icc a b)) : ContinuousOn g (Set.Icc a b) := by
  obtain ⟨F, hω⟩ := exists_realFramework_nonstandard.{0}
  exact fun c hc =>
    RealFramework.continuousWithinAt_of_tendstoUniformlyOn hω (fun n => hf n c hc) hu hc

end Goldblatt
