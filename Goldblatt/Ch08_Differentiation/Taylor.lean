import Goldblatt.Ch08_Differentiation.Derivative

/-!
# 8 (part 3). Taylor Series and Taylor's Formula: Sections 8.9 and 8.10

This is the third of four parts of Chapter 8 (the overview is on the chapter page
{lit}`Goldblatt.Ch08_Differentiation`). It defines Taylor polynomials and remainders,
expresses convergence of a Taylor series by the behaviour of the polynomials and remainders
of unlimited order, proves Taylor's formula with two forms of the remainder from Rolle's
theorem, transfers the formula to hypernatural orders and hyperreal points, and uses it to
show that the Maclaurin series of the cosine and of the exponential function converge to
those functions. Section 8.10 then reads Taylor's formula at an infinitesimal distance from
the centre: the Taylor polynomial of degree $`n` approximates the function with an error that
is infinitesimal compared to the $`n`-th power of the increment.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## Transfer tools for points between two others

Taylor's formula and the mean value theorem assert the existence of a point $`c` between two
given points. This preliminary section, which is not a numbered section of the book, contains
the existential transfer of such statements in the ultrapower: a point between $`a` and each
term of a sequence is chosen termwise, and the class of the chosen sequence lies between
$`a` and the class of the sequence. "Between" is expressed with the unordered closed interval
{name}`Set.uIcc`, in the reals and in the hyperreals alike.
-/

section Between

variable {J : Set ℝ} {a x : ℝ} {y : ℝ*}

/-- **Chapter 8, transfer tool.** The class of a sequence lies between the classes of two
others if and only if this holds termwise for almost all indices. -/
theorem ofSeq_mem_uIcc {c p q : ℕ → ℝ} :
    Hyperreal.ofSeq c ∈ uIcc (Hyperreal.ofSeq p) (Hyperreal.ofSeq q) ↔
      ∀ᶠ n in hyperfilter ℕ, c n ∈ uIcc (p n) (q n) := by
  simp only [Set.mem_uIcc, ofSeq_le_ofSeq_iff, ← almostAll_and, ← almostAll_or]

/-- **Chapter 8, tool.** A hyperreal between two hyperreals that are infinitely close to
$`r` is infinitely close to $`r`. -/
theorem infClose_of_mem_uIcc {c p q r : ℝ*} (hc : c ∈ uIcc p q) (hp : p ≊ r) (hq : q ≊ r) :
    c ≊ r := by
  rcases Set.mem_uIcc.1 hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact infClose_of_le_of_le h1 h2 hp hq
  · exact infClose_of_le_of_le h1 h2 hq hp

/-- **Chapter 8, transfer tool.** If an interval $`J` of reals contains $`a` and $`x`, then
every hyperreal between $`a` and $`x` belongs to the enlargement of $`J`. -/
theorem uIcc_coe_subset_starSet (hJ : J.OrdConnected) (ha : a ∈ J) (hx : x ∈ J) :
    uIcc (a : ℝ*) x ⊆ ⋆J := by
  intro c hc
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep c
  rw [coe_eq_ofSeq_const, coe_eq_ofSeq_const, ofSeq_mem_uIcc] at hc
  exact hyperreal_ofSeq_mem_starSet.2 (hc.mono fun n hn => hJ.uIcc_subset ha hx hn)

/-- **Chapter 8, transfer tool.** The extension of $`t \mapsto c\,(t - a)^k` is given by the
same formula. -/
theorem starMap_const_mul_sub_pow (c a : ℝ) (k : ℕ) (y : ℝ*) :
    ⋆(fun t : ℝ => c * (t - a) ^ k) y = (c : ℝ*) * (y - a) ^ k := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep y
  rfl

/-- **Chapter 8, transfer tool.** The extension of a finite sum of functions is the sum of
the extensions. -/
theorem starMap_sum_range (g : ℕ → ℝ → ℝ) (m : ℕ) (y : ℝ*) :
    ⋆(fun t : ℝ => ∑ k ∈ Finset.range m, g k t) y = ∑ k ∈ Finset.range m, ⋆(g k) y := by
  induction m with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    rw [starMap_const_apply, Hyperreal.coe_zero]
  | succ m ih =>
    simp only [Finset.sum_range_succ]
    rw [starMap_add_apply, ih]

/-- **Chapter 8, transfer tool (existential transfer of a point in between).** Suppose that
for every real $`t` in $`J` there is a real $`c` between $`x` and $`t`, different from $`x`
if $`t` is, such that $`P(t) = Q(c)\,R(t)`. Then for every hyperreal $`y` in the enlargement
of $`J` there is a hyperreal $`c` between $`x` and $`y`, different from $`x` if $`y` is,
such that $`{}^*P(y) = {}^*Q(c)\,{}^*R(y)`. -/
theorem exists_mem_uIcc_starMap_eq_mul {P Q R : ℝ → ℝ}
    (h : ∀ t ∈ J, ∃ c ∈ uIcc x t, (t ≠ x → c ≠ x) ∧ P t = Q c * R t) (hy : y ∈ ⋆J) :
    ∃ c ∈ uIcc (x : ℝ*) y, (y ≠ x → c ≠ x) ∧ ⋆P y = ⋆Q c * ⋆R y := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep y
  have hr := hyperreal_ofSeq_mem_starSet.1 hy
  have hstd : ∀ n, ∃ c : ℝ, r n ∈ J →
      c ∈ uIcc x (r n) ∧ (r n ≠ x → c ≠ x) ∧ P (r n) = Q c * R (r n) := by
    intro n
    by_cases hn : r n ∈ J
    · obtain ⟨c, h1, h2, h3⟩ := h _ hn
      exact ⟨c, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨x, fun h' => absurd h' hn⟩
  choose c hc using hstd
  refine ⟨Hyperreal.ofSeq c, ?_, ?_, ?_⟩
  · rw [coe_eq_ofSeq_const, ofSeq_mem_uIcc]
    exact hr.mono fun n hn => (hc n hn).1
  · intro hne
    rw [coe_eq_ofSeq_const, ofSeq_ne_ofSeq_iff] at hne ⊢
    filter_upwards [hr, hne] with n h1 h2 using (hc n h1).2.1 h2
  · have key : (Hyperreal.ofSeq fun n => P (r n)) =
        Hyperreal.ofSeq fun n => Q (c n) * R (r n) := by
      rw [ofSeq_eq_ofSeq_iff]
      exact hr.mono fun n hn => (hc n hn).2.2
    exact key

/-- **Chapter 8, transfer tool (existential transfer of a point in between, for a sequence
of statements).** Suppose that for every natural number $`n` and every real $`t` in $`J`
there is a real $`c` between $`a` and $`t` such that $`P_n(t) = Q_n(c)\,R_n(t)`. Then for
every hypernatural $`N` and every hyperreal $`y` in the enlargement of $`J` there is a
hyperreal $`c` between $`a` and $`y` such that $`P_N(y) = Q_N(c)\,R_N(y)`, where the
functions with hypernatural index are those of the hypersequences of Section 7.12. -/
theorem exists_mem_uIcc_hyperFunSeq_eq_mul {P Q R : ℕ → ℝ → ℝ}
    (h : ∀ n, ∀ t ∈ J, ∃ c ∈ uIcc a t, P n t = Q n c * R n t) {N : ℝ*} (hN : N ∈ ℕ*)
    (hy : y ∈ ⋆J) :
    ∃ c ∈ uIcc (a : ℝ*) y, hyperFunSeq P N y = hyperFunSeq Q N c * hyperFunSeq R N y := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep y
  obtain ⟨k, rfl⟩ := exists_hnat_eq hN
  have hr := hyperreal_ofSeq_mem_starSet.1 hy
  have hstd : ∀ n, ∃ c : ℝ, r n ∈ J →
      c ∈ uIcc a (r n) ∧ P (k n) (r n) = Q (k n) c * R (k n) (r n) := by
    intro n
    by_cases hn : r n ∈ J
    · obtain ⟨c, h1, h2⟩ := h (k n) _ hn
      exact ⟨c, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨a, fun h' => absurd h' hn⟩
  choose c hc using hstd
  refine ⟨Hyperreal.ofSeq c, ?_, ?_⟩
  · rw [coe_eq_ofSeq_const, ofSeq_mem_uIcc]
    exact hr.mono fun n hn => (hc n hn).1
  · rw [hyperFunSeq_hnat, hyperFunSeq_hnat, hyperFunSeq_hnat]
    have key : (Hyperreal.ofSeq fun n => P (k n) (r n)) =
        Hyperreal.ofSeq fun n => Q (k n) (c n) * R (k n) (r n) := by
      rw [ofSeq_eq_ofSeq_iff]
      exact hr.mono fun n hn => (hc n hn).2
    exact key

/-- **Chapter 8, transfer tool.** A bound that holds for all terms of a sequence of functions
on $`J` holds for the functions with hypernatural index on the enlargement of $`J`. -/
theorem abs_hyperFunSeq_le {G : ℕ → ℝ → ℝ} {M : ℝ} (h : ∀ n, ∀ t ∈ J, |G n t| ≤ M) {N c : ℝ*}
    (hN : N ∈ ℕ*) (hc : c ∈ ⋆J) : |hyperFunSeq G N c| ≤ M := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep c
  obtain ⟨k, rfl⟩ := exists_hnat_eq hN
  rw [hyperFunSeq_hnat, abs_ofSeq, coe_eq_ofSeq_const, ofSeq_le_ofSeq_iff]
  exact (hyperreal_ofSeq_mem_starSet.1 hc).mono fun n hn => h _ _ hn

end Between

/-!
## 8.9 Taylor Series

Let $`f` be a real function and $`a` a real number at which $`f` has derivatives of all
orders. The _Taylor series_ of $`f` at $`x`, centred on $`a`, is the series with terms
$`f^{(k)}(a)\,(x - a)^k / k!`. Its partial sums are the _Taylor polynomials_
$`P_n(x)`, and $`R_n(x) = f(x) - P_n(x)` is the $`n`-th _remainder_. The series need not
converge, and if it converges its sum need not be $`f(x)`. By Chapter 6, applied to the
sequence of partial sums:

* the Taylor series at $`x` converges to $`L` if and only if $`P_N(x) \simeq L` for all
  unlimited $`N`;
* it converges to $`f(x)` if and only if $`R_N(x)` is infinitesimal for all unlimited $`N`.

Derivatives of higher order are Mathlib's {name}`iteratedDeriv`. The sequence of functions
$`(f^{(n)})` extends, as in Section 7.12, to a hypersequence of functions indexed by the
hypernaturals and defined at all hyperreals; in the formalization this is
{name}`hyperFunSeq` applied to the sequence of iterated derivatives, and similarly for the
polynomials and remainders. Identities between these sequences persist at unlimited indices.

Taylor's formula with Lagrange's form of the remainder says that if $`f` has $`n + 1`
derivatives on an open interval containing $`a` and $`x`, then
$`R_n(x) = f^{(n+1)}(c)\,(x - a)^{n+1}/(n+1)!` for some $`c` between $`a` and $`x`. The
book quotes it as known. It is proved here, together with the second form of the remainder
used in Exercise 8.10.2, by repeated application of Rolle's theorem of Section 8.5 to the
difference between $`f` and a suitable polynomial. By transfer the formula holds for every
hypernatural order and every hyperreal point of the enlarged interval, with a hyperreal
$`c`. If the derivatives of $`f` are bounded on the interval uniformly in the order, the
right side is a limited number times $`(x - a)^{N+1}/(N+1)!`, which for real $`x` and
unlimited $`N` is infinitesimal by Exercise 6.11(10). Hence the Taylor series converges to
the function. This applies to the cosine function, whose derivatives are bounded by $`1`,
and (Exercise 8.9.1) to the exponential function on any bounded interval.

The book illustrates the possible failure of convergence to the function with the function
that is $`e^{-1/x^2}` away from $`0` and $`0` at $`0`, all of whose derivatives vanish at
$`0`; that example is quoted there as well known and is not formalized.
-/

section TaylorSeries

variable {f : ℝ → ℝ} {J : Set ℝ} {a x L : ℝ} {N : ℝ*}

/-- **Section 8.9, Taylor series.** The $`k`-th term
$`\dfrac{f^{(k)}(a)}{k!}(x - a)^k` of the Taylor series of $`f` at $`x`, centred on
$`a`. -/
def taylorTerm (f : ℝ → ℝ) (a x : ℝ) (k : ℕ) : ℝ :=
  iteratedDeriv k f a / k.factorial * (x - a) ^ k

/-- **Section 8.9, Taylor polynomials.** The $`n`-th Taylor polynomial
$`P_n(x) = \sum_{k=0}^{n} \dfrac{f^{(k)}(a)}{k!}(x - a)^k` of $`f` centred on $`a`. -/
def taylorPoly (f : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), taylorTerm f a x k

/-- **Section 8.9, equation (vii).** The $`n`-th remainder $`R_n(x) = f(x) - P_n(x)`. -/
def taylorRem (f : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ) : ℝ := f x - taylorPoly f a n x

/-- **Section 8.9.** The Taylor polynomials are the partial sums of the Taylor series: the
$`n`-th polynomial is the sum of the first $`n + 1` terms. -/
theorem taylorPoly_eq_partialSum (f : ℝ → ℝ) (a x : ℝ) (n : ℕ) :
    taylorPoly f a n x = partialSum (taylorTerm f a x) (n + 1) := rfl

/-- **Section 8.9.** Consecutive Taylor polynomials differ by one term:
$`P_{n+1}(x) - P_n(x) = \dfrac{f^{(n+1)}(a)}{(n+1)!}(x - a)^{n+1}`. -/
theorem taylorPoly_succ (f : ℝ → ℝ) (a x : ℝ) (n : ℕ) :
    taylorPoly f a (n + 1) x = taylorPoly f a n x + taylorTerm f a x (n + 1) :=
  Finset.sum_range_succ _ _

/-- **Section 8.9.** At the centre every Taylor polynomial takes the value $`f(a)`. -/
theorem taylorPoly_self (f : ℝ → ℝ) (a : ℝ) (n : ℕ) : taylorPoly f a n a = f a := by
  rw [taylorPoly, Finset.sum_eq_single 0]
  · simp [taylorTerm]
  · intro i _ hi
    simp [taylorTerm, hi]
  · intro h
    exact absurd (Finset.mem_range.2 n.succ_pos) h

/-- **Section 8.9.** At the centre every remainder vanishes. -/
theorem taylorRem_self (f : ℝ → ℝ) (a : ℝ) (n : ℕ) : taylorRem f a n a = 0 := by
  rw [taylorRem, taylorPoly_self, sub_self]

/-- **Section 8.9, first statement.** The Taylor series of $`f` at $`x` converges to the
real number $`L` if and only if $`P_N(x) \simeq L` for all unlimited $`N`. -/
theorem seriesSum_taylorTerm_iff :
    SeriesSum (taylorTerm f a x) L ↔
      ∀ N ∈ unlimitedHyperNat, hyperSeq (fun n => taylorPoly f a n x) N ≊ L := by
  rw [← tendsto_iff_forall_unlimited_infClose]
  exact (tendsto_add_atTop_iff_nat (f := partialSum (taylorTerm f a x)) 1).symm

/-- **Section 8.9, equation (vii) for hypernatural orders.** By transfer,
$`R_N(x) = f(x) - P_N(x)` for the extended sequences of remainders and polynomials. -/
theorem hyperSeq_taylorRem (f : ℝ → ℝ) (a x : ℝ) (N : ℝ*) :
    hyperSeq (fun n => taylorRem f a n x) N =
      f x - hyperSeq (fun n => taylorPoly f a n x) N := by
  have := hyperSeq_sub (fun _ => f x) (fun n => taylorPoly f a n x) N
  rwa [hyperSeq_const] at this

/-- **Section 8.9, second statement.** The Taylor series of $`f` at $`x` converges to
$`f(x)` if and only if the remainder $`R_N(x)` is infinitesimal for all unlimited $`N`. -/
theorem seriesSum_taylorTerm_self_iff :
    SeriesSum (taylorTerm f a x) (f x) ↔
      ∀ N ∈ unlimitedHyperNat, Infinitesimal (hyperSeq (fun n => taylorRem f a n x) N) := by
  rw [seriesSum_taylorTerm_iff]
  refine forall₂_congr fun N _ => ?_
  rw [hyperSeq_taylorRem, infClose_comm]
  rfl

/-- **Section 8.9, the identity for consecutive polynomials at hypernatural orders.** For
every hypernatural $`N` and every hyperreal $`y`, the extended polynomials satisfy
$`P_{N+1}(y) - P_N(y) = T_{N+1}(y)`, where $`T_n(t)` is the $`n`-th term of the Taylor
series at $`t`. This is the book's example of a result that continues to hold for unlimited
$`n` by transfer. -/
theorem hyperFunSeq_taylorPoly_add_one (f : ℝ → ℝ) (a : ℝ) (hN : N ∈ ℕ*) (y : ℝ*) :
    hyperFunSeq (fun n t => taylorPoly f a n t) (N + 1) y -
        hyperFunSeq (fun n t => taylorPoly f a n t) N y =
      hyperFunSeq (fun n t => taylorTerm f a t (n + 1)) N y := by
  obtain ⟨k, rfl⟩ := exists_hnat_eq hN
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep y
  rw [← hnat_const_one, hnat_add, hyperFunSeq_hnat, hyperFunSeq_hnat, hyperFunSeq_hnat]
  have key : (Hyperreal.ofSeq fun n => taylorPoly f a (k n + 1) (r n) -
      taylorPoly f a (k n) (r n)) = Hyperreal.ofSeq fun n => taylorTerm f a (r n) (k n + 1) :=
    congrArg Hyperreal.ofSeq (funext fun n => by rw [taylorPoly_succ, add_sub_cancel_left])
  exact key

/-- **Section 8.9, tool.** The derivative of a polynomial written in powers of $`t - a`
with coefficients $`C_i / i!`: differentiating shifts the coefficient sequence by one. -/
theorem hasDerivAt_sum_div_factorial_mul_pow (C : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ i ∈ Finset.range (m + 1), C i / i.factorial * (s - a) ^ i)
      (∑ i ∈ Finset.range m, C (i + 1) / i.factorial * (t - a) ^ i) t := by
  have h : ∀ i ∈ Finset.range m,
      HasDerivAt (fun s : ℝ => C (i + 1) / (i + 1).factorial * (s - a) ^ (i + 1))
        (C (i + 1) / i.factorial * (t - a) ^ i) t := by
    intro i _
    have h1 : HasDerivAt (fun s : ℝ => (s - a) ^ (i + 1)) ((i + 1 : ℕ) * (t - a) ^ i) t := by
      simpa using ((hasDerivAt_id t).sub_const a).fun_pow (i + 1)
    have h2 := h1.const_mul (C (i + 1) / (i + 1).factorial)
    convert h2 using 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  have h2 := (HasDerivAt.fun_sum h).add_const (C 0)
  convert h2 using 1
  funext s
  rw [Finset.sum_range_succ']
  simp

/-- **Section 8.5 (Rolle's Theorem)**, for end points in either order: if $`f` is
differentiable at every point between the distinct numbers $`p` and $`q` inclusive and
$`f(p) = f(q)`, then $`f'` vanishes at some point strictly between them. -/
theorem exists_deriv_eq_zero_between {g g' : ℝ → ℝ} {p q : ℝ} (hpq : p ≠ q)
    (hd : ∀ t ∈ uIcc p q, HasDerivAt g (g' t) t) (h : g p = g q) :
    ∃ c, min p q < c ∧ c < max p q ∧ g' c = 0 := by
  have hcont : ContinuousOn g (uIcc p q) := fun t ht =>
    (continuousAt_of_hasDerivAt (hd t ht)).continuousWithinAt
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · rw [uIcc_of_le hlt.le] at hd hcont
    obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero_of_eq hlt hcont
      (fun t ht => hd t (Ioo_subset_Icc_self ht)) h
    exact ⟨c, by rw [min_eq_left hlt.le]; exact hc.1, by rw [max_eq_right hlt.le]; exact hc.2,
      hc0⟩
  · rw [uIcc_of_ge hgt.le] at hd hcont
    obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero_of_eq hgt hcont
      (fun t ht => hd t (Ioo_subset_Icc_self ht)) h.symm
    exact ⟨c, by rw [min_eq_right hgt.le]; exact hc.1, by rw [max_eq_left hgt.le]; exact hc.2,
      hc0⟩

/-- **Section 8.9, tool (iterated Rolle).** Let $`F_0, F_1, \dots, F_{n+1}` be functions on
an interval $`J` with $`F_k' = F_{k+1}` on $`J` for $`k \le n`. If $`F_k(a) = 0` for all
$`k \le n` and $`F_0(x) = 0` at some $`x \ne a`, then $`F_{n+1}` vanishes at a point strictly
between $`a` and $`x`. Rolle's theorem gives a zero of $`F_1` between $`a` and $`x`, then a
zero of $`F_2` between $`a` and that point, and so on. -/
theorem exists_eq_zero_of_iterated_rolle {F : ℕ → ℝ → ℝ} (hJ : J.OrdConnected) (ha : a ∈ J)
    (n : ℕ) : ∀ {x : ℝ}, x ∈ J → x ≠ a →
      (∀ k ≤ n, ∀ t ∈ J, HasDerivAt (F k) (F (k + 1) t) t) → (∀ k ≤ n, F k a = 0) →
      F 0 x = 0 → ∃ c, min a x < c ∧ c < max a x ∧ F (n + 1) c = 0 := by
  induction n with
  | zero =>
    intro x hx hxa hD h0 hx0
    exact exists_deriv_eq_zero_between (g' := F 1) hxa.symm
      (fun t ht => hD 0 le_rfl t (hJ.uIcc_subset ha hx ht)) ((h0 0 le_rfl).trans hx0.symm)
  | succ n ih =>
    intro x hx hxa hD h0 hx0
    obtain ⟨c, hc1, hc2, hc0⟩ := ih hx hxa (fun k hk => hD k (hk.trans n.le_succ))
      (fun k hk => h0 k (hk.trans n.le_succ)) hx0
    have hcJ : c ∈ J := hJ.uIcc_subset ha hx (Set.mem_uIcc.2 (by
      rcases le_total a x with h | h
      · rw [min_eq_left h] at hc1
        rw [max_eq_right h] at hc2
        exact Or.inl ⟨hc1.le, hc2.le⟩
      · rw [min_eq_right h] at hc1
        rw [max_eq_left h] at hc2
        exact Or.inr ⟨hc1.le, hc2.le⟩))
    have hca : c ≠ a := by
      rintro rfl
      rcases le_total c x with h | h
      · rw [min_eq_left h] at hc1
        exact lt_irrefl _ hc1
      · rw [max_eq_left h] at hc2
        exact lt_irrefl _ hc2
    obtain ⟨c', h1, h2, h3⟩ := exists_deriv_eq_zero_between (g := F (n + 1))
      (g' := F (n + 1 + 1)) hca.symm
      (fun t ht => hD (n + 1) le_rfl t (hJ.uIcc_subset ha hcJ ht))
      ((h0 (n + 1) le_rfl).trans hc0.symm)
    exact ⟨c', lt_of_le_of_lt (le_min (min_le_left _ _) hc1.le) h1,
      lt_of_lt_of_le h2 (max_le (le_max_left _ _) hc2.le), h3⟩

/-- **Section 8.9, auxiliary functions of the proof of Taylor's formula.** Given functions
$`D_0, D_1, \dots` (the successive derivatives of $`f`) and numbers $`C_0, \dots, C_d`, the
$`k`-th auxiliary function is $`D_k` minus the $`k`-th derivative of the polynomial
$`\sum_{i \le d} C_i\,(t - a)^i / i!`. -/
def taylorAux (D : ℕ → ℝ → ℝ) (C : ℕ → ℝ) (a : ℝ) (d k : ℕ) (t : ℝ) : ℝ :=
  D k t - ∑ i ∈ Finset.range (d + 1 - k), C (k + i) / i.factorial * (t - a) ^ i

/-- **Section 8.9, tool.** Each auxiliary function is the derivative of the preceding
one. -/
theorem hasDerivAt_taylorAux {D : ℕ → ℝ → ℝ} {C : ℕ → ℝ} {d k : ℕ} {t : ℝ} (hk : k < d)
    (h : HasDerivAt (D k) (D (k + 1) t) t) :
    HasDerivAt (taylorAux D C a d k) (taylorAux D C a d (k + 1) t) t := by
  have e1 : d + 1 - k = d - k + 1 := by omega
  have e2 : d + 1 - (k + 1) = d - k := by omega
  have hp := hasDerivAt_sum_div_factorial_mul_pow (fun i => C (k + i)) a (d - k) t
  have hfun : taylorAux D C a d k =
      fun s => D k s - ∑ i ∈ Finset.range (d - k + 1), C (k + i) / i.factorial * (s - a) ^ i := by
    funext s
    rw [taylorAux, e1]
  have hval : taylorAux D C a d (k + 1) t =
      D (k + 1) t - ∑ i ∈ Finset.range (d - k), C (k + (i + 1)) / i.factorial * (t - a) ^ i := by
    rw [taylorAux, e2]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    rw [show k + 1 + i = k + (i + 1) by omega]
  rw [hfun, hval]
  exact h.fun_sub hp

/-- **Section 8.9, tool.** At the centre the $`k`-th auxiliary function has the value
$`D_k(a) - C_k`. -/
theorem taylorAux_self (D : ℕ → ℝ → ℝ) (C : ℕ → ℝ) (a : ℝ) {d k : ℕ} (hk : k ≤ d) :
    taylorAux D C a d k a = D k a - C k := by
  rw [taylorAux, Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- **Section 8.9, tool (Rolle's theorem for a function minus a polynomial).** Let
$`D_{k}' = D_{k+1}` on the interval $`J` for $`k \le m`, and let $`C_0, \dots, C_d` be
numbers with $`m < d` and $`C_k = D_k(a)` for $`k \le m`. If
$`D_0(x) = \sum_{i \le d} C_i\,(x - a)^i/i!` at some $`x \ne a` in $`J`, then there is a
point $`c` strictly between $`a` and $`x` with
$`D_{m+1}(c) = \sum_{i < d - m} C_{m+1+i}\,(c - a)^i/i!`. Both forms of Taylor's formula
are instances. -/
theorem exists_iterated_rolle_sub_poly {D : ℕ → ℝ → ℝ} (hJ : J.OrdConnected) (ha : a ∈ J)
    (hx : x ∈ J) (hxa : x ≠ a) {m d : ℕ} (hmd : m < d)
    (hD : ∀ k ≤ m, ∀ t ∈ J, HasDerivAt (D k) (D (k + 1) t) t) (C : ℕ → ℝ)
    (hC : ∀ k ≤ m, C k = D k a)
    (hx0 : D 0 x = ∑ i ∈ Finset.range (d + 1), C i / i.factorial * (x - a) ^ i) :
    ∃ c, min a x < c ∧ c < max a x ∧
      D (m + 1) c = ∑ i ∈ Finset.range (d - m), C (m + 1 + i) / i.factorial * (c - a) ^ i := by
  obtain ⟨c, h1, h2, h3⟩ := exists_eq_zero_of_iterated_rolle (F := taylorAux D C a d) hJ ha m
    hx hxa (fun k hk t ht => hasDerivAt_taylorAux (by omega) (hD k hk t ht))
    (fun k hk => by rw [taylorAux_self D C a (by omega), hC k hk, sub_self])
    (by
      rw [taylorAux, Nat.sub_zero]
      simp only [zero_add]
      rw [hx0, sub_self])
  refine ⟨c, h1, h2, ?_⟩
  rw [taylorAux, sub_eq_zero] at h3
  rw [h3, show d + 1 - (m + 1) = d - m by omega]

/-- **Section 8.9, Taylor's formula with Lagrange's form of the remainder.** Let $`J` be an
interval containing $`a` and $`x`, with $`x \ne a`, on which $`f` can be differentiated
$`n + 1` times. Then there is a real number $`c` strictly between $`a` and $`x` such that
$$`R_n(x) = \frac{f^{(n+1)}(c)}{(n+1)!}(x - a)^{n+1}.`
The hypothesis is stated as differentiability on $`J` of the derivatives of order at most
$`n`. The book quotes this theorem; here it is derived from Rolle's theorem. -/
theorem exists_taylorRem_eq_lagrange (hJ : J.OrdConnected) (ha : a ∈ J) (hx : x ∈ J)
    (hxa : x ≠ a) (n : ℕ)
    (hD : ∀ k ≤ n, ∀ t ∈ J, DifferentiableAt ℝ (iteratedDeriv k f) t) :
    ∃ c, min a x < c ∧ c < max a x ∧
      taylorRem f a n x = iteratedDeriv (n + 1) f c / (n + 1).factorial * (x - a) ^ (n + 1) := by
  set M : ℝ := taylorRem f a n x * (n + 1).factorial / (x - a) ^ (n + 1) with hM
  have hpow : (x - a) ^ (n + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hxa)
  have hfac : ((n + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  obtain ⟨c, h1, h2, h3⟩ := exists_iterated_rolle_sub_poly (D := fun k => iteratedDeriv k f)
    hJ ha hx hxa (m := n) (d := n + 1) (Nat.lt_succ_self n)
    (fun k hk t ht => by
      rw [iteratedDeriv_succ]
      exact (hD k hk t ht).hasDerivAt)
    (fun k => if k ≤ n then iteratedDeriv k f a else M) (fun k hk => ite_eq_left hk)
    (by
      rw [iteratedDeriv_zero, Finset.sum_range_succ, ite_eq_right (by omega)]
      have hsum : ∑ i ∈ Finset.range (n + 1),
          (if i ≤ n then iteratedDeriv i f a else M) / i.factorial * (x - a) ^ i =
            taylorPoly f a n x :=
        Finset.sum_congr rfl fun i hi => by
          rw [ite_eq_left (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
          rfl
      rw [hsum, hM, taylorRem]
      field_simp
      ring)
  refine ⟨c, h1, h2, ?_⟩
  have h4 : iteratedDeriv (n + 1) f c = M := by
    rw [show n + 1 - n = 1 by omega] at h3
    simpa using h3
  rw [h4, hM]
  field_simp

/-- **Section 8.9, equation (viii).** Taylor's formula with Lagrange's remainder, for every
point $`x` of the interval: there is $`c` between $`a` and $`x` (possibly an end point, to
include the case $`x = a`, but different from $`a` when $`x` is) with
$`f(x) - P_n(x) = f^{(n+1)}(c)\,(x - a)^{n+1}/(n+1)!`. -/
theorem exists_mem_uIcc_taylorRem_eq_lagrange (hJ : J.OrdConnected) (ha : a ∈ J)
    (hx : x ∈ J) (n : ℕ) (hD : ∀ k ≤ n, ∀ t ∈ J, DifferentiableAt ℝ (iteratedDeriv k f) t) :
    ∃ c ∈ uIcc a x, (x ≠ a → c ≠ a) ∧
      taylorRem f a n x = iteratedDeriv (n + 1) f c / (n + 1).factorial * (x - a) ^ (n + 1) := by
  rcases eq_or_ne x a with rfl | hxa
  · exact ⟨x, left_mem_uIcc, fun h => absurd rfl h, by simp [taylorRem_self]⟩
  · obtain ⟨c, h1, h2, h3⟩ := exists_taylorRem_eq_lagrange hJ ha hx hxa n hD
    refine ⟨c, ⟨h1.le, h2.le⟩, fun _ => ?_, h3⟩
    rintro rfl
    rcases le_total c x with h | h
    · rw [min_eq_left h] at h1
      exact lt_irrefl _ h1
    · rw [max_eq_left h] at h2
      exact lt_irrefl _ h2

/-- **Exercise 8.10.2, the second form of the remainder.** Let $`J` be an interval
containing $`a` and $`x`, with $`x \ne a`, on which $`f` can be differentiated $`n` times.
Then there is a real number $`c` between $`a` and $`x`, different from $`a`, such that
$$`R_n(x) = \frac{f^{(n)}(c) - f^{(n)}(a)}{(c - a)\,(n+1)!}(x - a)^{n+1}.`
The book assumes that $`f^{(n+1)}` exists between $`a` and $`x`; the proof by Rolle's
theorem needs only $`n` derivatives, and the statement is given in that stronger form. For
$`n \ge 1` the point $`c` is strictly between $`a` and $`x`; for $`n = 0` the formula holds
with $`c = x`. -/
theorem exists_taylorRem_eq_slope (hJ : J.OrdConnected) (ha : a ∈ J) (hx : x ∈ J)
    (hxa : x ≠ a) (n : ℕ)
    (hD : ∀ k < n, ∀ t ∈ J, DifferentiableAt ℝ (iteratedDeriv k f) t) :
    ∃ c ∈ uIcc a x, c ≠ a ∧
      taylorRem f a n x = (iteratedDeriv n f c - iteratedDeriv n f a) /
        ((c - a) * (n + 1).factorial) * (x - a) ^ (n + 1) := by
  have hxa' : x - a ≠ 0 := sub_ne_zero.2 hxa
  rcases n with _ | m
  · refine ⟨x, right_mem_uIcc, hxa, ?_⟩
    simp only [taylorRem, taylorPoly, taylorTerm, zero_add, Finset.range_one,
      Finset.sum_singleton, iteratedDeriv_zero, Nat.factorial, Nat.cast_one, pow_zero, pow_one,
      div_one, mul_one]
    field_simp
  set M : ℝ := taylorRem f a (m + 1) x * (m + 2).factorial / (x - a) ^ (m + 2) with hM
  have hpow : (x - a) ^ (m + 2) ≠ 0 := pow_ne_zero _ hxa'
  have hfac : ((m + 2).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  obtain ⟨c, h1, h2, h3⟩ := exists_iterated_rolle_sub_poly (D := fun k => iteratedDeriv k f)
    hJ ha hx hxa (m := m) (d := m + 2) (by omega)
    (fun k hk t ht => by
      rw [iteratedDeriv_succ]
      exact (hD k (by omega) t ht).hasDerivAt)
    (fun k => if k ≤ m + 1 then iteratedDeriv k f a else M) (fun k hk => ite_eq_left (by omega))
    (by
      rw [iteratedDeriv_zero, Finset.sum_range_succ, ite_eq_right (by omega)]
      have hsum : ∑ i ∈ Finset.range (m + 2),
          (if i ≤ m + 1 then iteratedDeriv i f a else M) / i.factorial * (x - a) ^ i =
            taylorPoly f a (m + 1) x :=
        Finset.sum_congr rfl fun i hi => by
          rw [ite_eq_left (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
          rfl
      rw [hsum, hM, taylorRem]
      field_simp
      ring)
  have hca : c ≠ a := by
    rintro rfl
    rcases le_total c x with h | h
    · rw [min_eq_left h] at h1
      exact lt_irrefl _ h1
    · rw [max_eq_left h] at h2
      exact lt_irrefl _ h2
  have hca' : c - a ≠ 0 := sub_ne_zero.2 hca
  refine ⟨c, ⟨h1.le, h2.le⟩, hca, ?_⟩
  have h4 : iteratedDeriv (m + 1) f c - iteratedDeriv (m + 1) f a = M * (c - a) := by
    rw [show m + 2 - m = 2 by omega, Finset.sum_range_succ, Finset.sum_range_one] at h3
    rw [h3]
    simp
  rw [h4, hM]
  field_simp

/-- **Section 8.9, the hypersequence of derivatives.** The derivative $`f^{(N)}` of
hypernatural order $`N`, as a function on the hyperreals: the value at $`(N, x)` of the
extension of $`F(n, x) = f^{(n)}(x)`. -/
def hyperIteratedDeriv (f : ℝ → ℝ) : ℝ* → ℝ* → ℝ* := hyperFunSeq fun n => iteratedDeriv n f

/-- **Section 8.9.** For a standard order $`n` the derivative of the hypersequence is the
extension of the $`n`-th derivative. -/
theorem hyperIteratedDeriv_natCast (f : ℝ → ℝ) (n : ℕ) (x : ℝ*) :
    hyperIteratedDeriv f n x = ⋆(iteratedDeriv n f) x :=
  hyperFunSeq_natCast _ n x

/-- **Section 8.9, Taylor's formula (viii) by transfer.** Let $`f` be infinitely
differentiable on an interval $`J` containing $`a`. Then for every hypernatural $`N` and
every hyperreal $`y` in the enlargement of $`J` there is a hyperreal $`c` between $`a` and
$`y` such that
$$`R_N(y) = f^{(N+1)}(c)\,\frac{(y - a)^{N+1}}{(N+1)!},`
where all three factors are values of the hypersequences that extend the corresponding
sequences of real functions. The point $`c` need not be real. -/
theorem exists_hyper_taylorRem_eq_lagrange (hJ : J.OrdConnected) (ha : a ∈ J)
    (hD : ∀ k, ∀ t ∈ J, DifferentiableAt ℝ (iteratedDeriv k f) t) (hN : N ∈ ℕ*) {y : ℝ*}
    (hy : y ∈ ⋆J) :
    ∃ c ∈ uIcc (a : ℝ*) y,
      hyperFunSeq (fun n t => taylorRem f a n t) N y =
        hyperFunSeq (fun n t => iteratedDeriv (n + 1) f t) N c *
          hyperFunSeq (fun n t => (t - a) ^ (n + 1) / (n + 1).factorial) N y := by
  refine exists_mem_uIcc_hyperFunSeq_eq_mul (fun n t ht => ?_) hN hy
  obtain ⟨c, hc, -, heq⟩ :=
    exists_mem_uIcc_taylorRem_eq_lagrange hJ ha ht n fun k _ => hD k
  exact ⟨c, hc, by rw [heq]; ring⟩

/-- **Section 8.9, convergence of the Taylor series from a bound on the derivatives.** Let
$`f` be infinitely differentiable on an interval $`J` containing $`a` and the real number
$`x`, and suppose that all derivatives of $`f` are bounded on $`J` by one real number $`M`.
Then the remainder $`R_N(x)` is infinitesimal for every unlimited $`N`. By the transferred
Taylor formula, $`R_N(x)` is the product of $`f^{(N+1)}(c)`, which is limited because the
bound transfers, and $`(x - a)^{N+1}/(N+1)!`, which is infinitesimal by
Exercise 6.11(10). -/
theorem infinitesimal_taylorRem_of_bounded (hJ : J.OrdConnected) (ha : a ∈ J) (hx : x ∈ J)
    (hD : ∀ k, ∀ t ∈ J, DifferentiableAt ℝ (iteratedDeriv k f) t) {M : ℝ}
    (hM : ∀ k, ∀ t ∈ J, |iteratedDeriv k f t| ≤ M) (hN : N ∈ unlimitedHyperNat) :
    Infinitesimal (hyperSeq (fun n => taylorRem f a n x) N) := by
  have hxJ : (x : ℝ*) ∈ ⋆J := uIcc_coe_subset_starSet hJ ha hx right_mem_uIcc
  obtain ⟨c, hc, heq⟩ := exists_hyper_taylorRem_eq_lagrange hJ ha hD hN.1 hxJ
  rw [hyperFunSeq_coe _ _ hN.1, hyperFunSeq_coe _ _ hN.1] at heq
  rw [heq]
  -- the derivative of unlimited order is limited at `c`
  have hcJ : c ∈ ⋆J := uIcc_coe_subset_starSet hJ ha hx hc
  have hb := abs_hyperFunSeq_le (G := fun n t => iteratedDeriv (n + 1) f t)
    (fun n t ht => hM (n + 1) t ht) hN.1 hcJ
  have hlim : Limited (hyperFunSeq (fun n t => iteratedDeriv (n + 1) f t) N c) :=
    limited_iff_abs_lt.2 ⟨M + 1, lt_of_le_of_lt hb (Hyperreal.coe_lt_coe.2 (by linarith))⟩
  -- the power divided by the factorial is infinitesimal
  have hinf := infinitesimal_pow_div_factorial (x - a) (add_one_mem_unlimitedHyperNat hN)
  rw [hyperSeq_add_one _ hN.1] at hinf
  exact hlim.mul_infinitesimal hinf

/-- **Section 8.9, convergence of the Taylor series from a bound on the derivatives.** Under
the hypotheses of the preceding theorem, the Taylor series of $`f` at $`x` centred on $`a`
converges to $`f(x)`. -/
theorem seriesSum_taylorTerm_of_bounded (hJ : J.OrdConnected) (ha : a ∈ J) (hx : x ∈ J)
    (hD : ∀ k, ∀ t ∈ J, DifferentiableAt ℝ (iteratedDeriv k f) t) {M : ℝ}
    (hM : ∀ k, ∀ t ∈ J, |iteratedDeriv k f t| ≤ M) :
    SeriesSum (taylorTerm f a x) (f x) :=
  seriesSum_taylorTerm_self_iff.2 fun _ hN =>
    infinitesimal_taylorRem_of_bounded hJ ha hx hD hM hN

/-- **Section 8.9, the cosine function.** For every real $`x` and every unlimited $`N`, the
remainder $`R_N(x)` of the Maclaurin series of the cosine is infinitesimal: all derivatives
of the cosine are plus or minus the sine or the cosine, and so are bounded by $`1`. -/
theorem infinitesimal_taylorRem_cos (x : ℝ) (hN : N ∈ unlimitedHyperNat) :
    Infinitesimal (hyperSeq (fun n => taylorRem Real.cos 0 n x) N) :=
  infinitesimal_taylorRem_of_bounded (J := univ) ordConnected_univ (mem_univ _) (mem_univ _)
    (fun k _ _ => (Real.differentiable_iteratedDeriv_cos k).differentiableAt)
    (fun k t _ => Real.abs_iteratedDeriv_cos_le_one k t) hN

/-- **Section 8.9, the cosine function.** The Maclaurin series of the cosine function
converges to $`\cos x` at every real $`x`. -/
theorem seriesSum_maclaurin_cos (x : ℝ) : SeriesSum (taylorTerm Real.cos 0 x) (Real.cos x) :=
  seriesSum_taylorTerm_self_iff.2 fun _ hN => infinitesimal_taylorRem_cos x hN

/-- **Exercise 8.9.1.** For every real $`x` and every unlimited $`N`, the remainder
$`R_N(x)` of the Maclaurin series of the exponential function is infinitesimal. Every
derivative of the exponential function is the exponential function, which on the interval
$`(-|x| - 1, |x| + 1)` is bounded by $`e^{|x| + 1}`. -/
theorem infinitesimal_taylorRem_exp (x : ℝ) (hN : N ∈ unlimitedHyperNat) :
    Infinitesimal (hyperSeq (fun n => taylorRem Real.exp 0 n x) N) := by
  have hiter : ∀ k, iteratedDeriv k Real.exp = Real.exp := fun k => by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  have hx : |x| < |x| + 1 := by linarith
  refine infinitesimal_taylorRem_of_bounded (J := Ioo (-(|x| + 1)) (|x| + 1))
    (M := Real.exp (|x| + 1)) ordConnected_Ioo
    ⟨by linarith [abs_nonneg x], by linarith [abs_nonneg x]⟩ (abs_lt.1 hx)
    (fun k t _ => by rw [hiter]; exact Real.differentiable_exp.differentiableAt)
    (fun k t ht => by
      rw [hiter, abs_of_pos (Real.exp_pos t)]
      exact Real.exp_le_exp.2 ht.2.le) hN

/-- **Exercise 8.9.1.** The Maclaurin series of the exponential function converges to
$`e^x` at every real $`x`. -/
theorem seriesSum_maclaurin_exp (x : ℝ) : SeriesSum (taylorTerm Real.exp 0 x) (Real.exp x) :=
  seriesSum_taylorTerm_self_iff.2 fun _ hN => infinitesimal_taylorRem_exp x hN

/-- **Section 8.9, non-vacuity.** The terms of the Maclaurin series of the exponential
function are $`x^k/k!`, so the series in the preceding theorem is the familiar one. -/
theorem taylorTerm_exp_zero (x : ℝ) (k : ℕ) :
    taylorTerm Real.exp 0 x k = x ^ k / k.factorial := by
  rw [taylorTerm, iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.exp_zero, sub_zero]
  ring

end TaylorSeries

/-!
## 8.10 Incremental Approximation by Taylor's Formula

The incremental equation of Theorem 8.2.2 approximates $`f(x + \Delta x)` by a linear
function of the increment with an error $`\varepsilon\,\Delta x` that is infinitely smaller
than $`\Delta x`. Taylor's formula gives approximations of higher order. Fix a real number
$`x` and a positive integer $`n`, and consider Taylor polynomials centred on $`x` itself. If
$`f^{(n)}` exists on an open interval containing $`x`, Taylor's formula with Lagrange's
remainder of order $`n - 1` holds at the real points $`x + \Delta x` of the interval, and
by transfer at $`x + \Delta x` for every infinitesimal $`\Delta x`, with a point $`c`
between $`x` and $`x + \Delta x`, so that $`c \simeq x`. If $`f^{(n)}` is continuous at
$`x`, then $`f^{(n)}(c) \simeq f^{(n)}(x)`, and replacing one by the other changes the last
term by $`\varepsilon\,\Delta x^n` with $`\varepsilon` infinitesimal. This is Theorem
8.10.1. Exercise 8.10.2 removes the hypothesis of continuity by using the second form of
the remainder, in which the last coefficient is a Newton quotient of $`f^{(n-1)}` at $`x`,
infinitely close to $`f^{(n)}(x)` by Theorem 8.1.1.
-/

section TaylorIncrement

variable {f : ℝ → ℝ} {J : Set ℝ} {x : ℝ} {Δ : ℝ*}

/-- **Section 8.10, tool.** The extension of a Taylor polynomial centred on $`a` is the
polynomial with the same coefficients in the hyperreal variable. -/
theorem starMap_taylorPoly (f : ℝ → ℝ) (a : ℝ) (n : ℕ) (y : ℝ*) :
    ⋆(fun t => taylorPoly f a n t) y =
      ∑ k ∈ Finset.range (n + 1),
        ((iteratedDeriv k f a / k.factorial : ℝ) : ℝ*) * (y - a) ^ k := by
  unfold taylorPoly taylorTerm
  rw [starMap_sum_range]
  exact Finset.sum_congr rfl fun k _ => starMap_const_mul_sub_pow _ a k y

/-- **Section 8.10, equation (ix) by transfer.** Suppose that for every real $`t` in a
neighbourhood $`J` of $`x` the remainder of order $`m` centred on $`x` has the form
$`R_m(t) = Q(c)\,(t - x)^{m+1}/(m+1)!` with $`c` between $`x` and $`t`, different from
$`x` if $`t` is. Then for every infinitesimal $`\Delta x` there is a hyperreal
$`c \simeq x`, different from $`x` if $`\Delta x \ne 0`, such that
$$`{}^*f(x + \Delta x) = \sum_{k \le m} \frac{f^{(k)}(x)}{k!}\Delta x^k +
  {}^*Q(c)\,\frac{\Delta x^{m+1}}{(m+1)!}.` -/
theorem exists_taylor_increment_of_remainder {Q : ℝ → ℝ} {m : ℕ}
    (h : ∀ t ∈ J, ∃ c ∈ uIcc x t, (t ≠ x → c ≠ x) ∧
      taylorRem f x m t = Q c * (1 / (m + 1).factorial * (t - x) ^ (m + 1)))
    (hJx : J ∈ 𝓝 x) (hΔ : Infinitesimal Δ) :
    ∃ c : ℝ*, c ≊ x ∧ (Δ ≠ 0 → c ≠ x) ∧
      ⋆f (x + Δ) = ∑ k ∈ Finset.range (m + 1),
          ((iteratedDeriv k f x / k.factorial : ℝ) : ℝ*) * Δ ^ k +
        ⋆Q c * (((1 / (m + 1).factorial : ℝ) : ℝ*) * Δ ^ (m + 1)) := by
  have hy : (x : ℝ*) + Δ ∈ ⋆J := coe_add_infinitesimal_mem_starSet_of_mem_nhds hJx hΔ
  obtain ⟨c, hc, hne, heq⟩ := exists_mem_uIcc_starMap_eq_mul h hy
  have hyx : (x : ℝ*) + Δ ≊ x := by rw [infClose_iff]; simpa using hΔ
  refine ⟨c, infClose_of_mem_uIcc hc (InfClose.refl _) hyx, fun h0 => hne (by simpa using h0), ?_⟩
  have hP : ⋆(fun t => taylorRem f x m t) ((x : ℝ*) + Δ) =
      ⋆f (x + Δ) - ⋆(fun t => taylorPoly f x m t) (x + Δ) :=
    starMap_sub_apply f (fun t => taylorPoly f x m t) _
  rw [hP, starMap_taylorPoly, starMap_const_mul_sub_pow, add_sub_cancel_left] at heq
  linear_combination heq

/-- **Theorem 8.10.1.** Let $`n \ge 1`. If the $`n`-th derivative $`f^{(n)}` exists on an
open interval $`J` containing the real number $`x`, and $`f^{(n)}` is continuous at $`x`,
then for any infinitesimal $`\Delta x`,
$$`{}^*f(x + \Delta x) = f(x) + f'(x)\,\Delta x + \frac{f''(x)}{2!}\Delta x^2 + \cdots +
  \frac{f^{(n)}(x)}{n!}\Delta x^n + \varepsilon\,\Delta x^n`
for some infinitesimal $`\varepsilon`. The existence of $`f^{(n)}` on $`J` is stated as
differentiability on $`J` of the derivatives of order less than $`n`. -/
theorem exists_infinitesimal_taylor_increment (hJ : J.OrdConnected) (hJx : J ∈ 𝓝 x) {n : ℕ}
    (hn : n ≠ 0) (hD : ∀ k < n, ∀ t ∈ J, DifferentiableAt ℝ (iteratedDeriv k f) t)
    (hcont : ContinuousAt (iteratedDeriv n f) x) (hΔ : Infinitesimal Δ) :
    ∃ η : ℝ*, Infinitesimal η ∧
      ⋆f (x + Δ) = ∑ k ∈ Finset.range (n + 1),
        ((iteratedDeriv k f x / k.factorial : ℝ) : ℝ*) * Δ ^ k + η * Δ ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hxJ : x ∈ J := mem_of_mem_nhds hJx
  -- Taylor's formula with Lagrange's remainder of order `m`, at the real points of `J`
  have hstd : ∀ t ∈ J, ∃ c ∈ uIcc x t, (t ≠ x → c ≠ x) ∧
      taylorRem f x m t =
        iteratedDeriv (m + 1) f c * (1 / (m + 1).factorial * (t - x) ^ (m + 1)) := by
    intro t ht
    obtain ⟨c, hc, hne, heq⟩ := exists_mem_uIcc_taylorRem_eq_lagrange hJ hxJ ht m
      fun k hk => hD k (by omega)
    exact ⟨c, hc, hne, by rw [heq]; ring⟩
  obtain ⟨c, hcx, -, heq⟩ := exists_taylor_increment_of_remainder hstd hJx hΔ
  -- continuity of the `n`-th derivative at `x`
  have hclose : ⋆(iteratedDeriv (m + 1) f) c ≊ ((iteratedDeriv (m + 1) f x : ℝ) : ℝ*) :=
    hcont.starMap_infClose hcx
  refine ⟨(⋆(iteratedDeriv (m + 1) f) c - ((iteratedDeriv (m + 1) f x : ℝ) : ℝ*)) *
    ((1 / (m + 1).factorial : ℝ) : ℝ*), Infinitesimal.mul_limited hclose (limited_coe _), ?_⟩
  have hcoef : ((iteratedDeriv (m + 1) f x / (m + 1).factorial : ℝ) : ℝ*) =
      ((iteratedDeriv (m + 1) f x : ℝ) : ℝ*) * ((1 / (m + 1).factorial : ℝ) : ℝ*) := by
    rw [← Hyperreal.coe_mul]
    congr 1
    ring
  rw [heq, Finset.sum_range_succ _ (m + 1), hcoef]
  ring

/-- **Exercise 8.10.2.** Theorem 8.10.1 holds without the hypothesis of continuity of
$`f^{(n)}`: if $`n \ge 1` and $`f^{(n)}` exists on an open interval $`J` containing the real
number $`x`, then for any infinitesimal $`\Delta x`,
$$`{}^*f(x + \Delta x) = \sum_{k \le n} \frac{f^{(k)}(x)}{k!}\Delta x^k +
  \varepsilon\,\Delta x^n`
for some infinitesimal $`\varepsilon`. The second form of the remainder of order $`n - 1`
gives, by transfer, a hyperreal $`c \simeq x` with $`c \ne x` such that the coefficient of
$`\Delta x^n / n!` is the Newton quotient
$`({}^*f^{(n-1)}(c) - f^{(n-1)}(x))/(c - x)`, and this is infinitely close to
$`f^{(n)}(x)` by Theorem 8.1.1 because $`f^{(n-1)}` is differentiable at $`x`. -/
theorem exists_infinitesimal_taylor_increment_of_differentiable (hJ : J.OrdConnected)
    (hJx : J ∈ 𝓝 x) {n : ℕ} (hn : n ≠ 0)
    (hD : ∀ k < n, ∀ t ∈ J, DifferentiableAt ℝ (iteratedDeriv k f) t)
    (hΔ : Infinitesimal Δ) :
    ∃ η : ℝ*, Infinitesimal η ∧
      ⋆f (x + Δ) = ∑ k ∈ Finset.range (n + 1),
        ((iteratedDeriv k f x / k.factorial : ℝ) : ℝ*) * Δ ^ k + η * Δ ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hxJ : x ∈ J := mem_of_mem_nhds hJx
  -- the second form of the remainder of order `m`, at the real points of `J`
  have hstd : ∀ t ∈ J, ∃ c ∈ uIcc x t, (t ≠ x → c ≠ x) ∧
      taylorRem f x m t =
        slope (iteratedDeriv m f) x c * (1 / (m + 1).factorial * (t - x) ^ (m + 1)) := by
    intro t ht
    rcases eq_or_ne t x with rfl | htx
    · exact ⟨t, left_mem_uIcc, fun h => absurd rfl h, by simp [taylorRem_self]⟩
    · obtain ⟨c, hc, hne, heq⟩ := exists_taylorRem_eq_slope hJ hxJ ht htx m
        fun k hk => hD k (by omega)
      refine ⟨c, hc, fun _ => hne, ?_⟩
      rw [heq, slope_def_field]
      have h1 : c - x ≠ 0 := sub_ne_zero.2 hne
      field_simp
  obtain ⟨c, hcx, hne, heq⟩ := exists_taylor_increment_of_remainder hstd hJx hΔ
  have hcoef : ((iteratedDeriv (m + 1) f x / (m + 1).factorial : ℝ) : ℝ*) =
      ((iteratedDeriv (m + 1) f x : ℝ) : ℝ*) * ((1 / (m + 1).factorial : ℝ) : ℝ*) := by
    rw [← Hyperreal.coe_mul]
    congr 1
    ring
  rcases eq_or_ne Δ 0 with rfl | h0
  · refine ⟨0, infinitesimal_zero, ?_⟩
    rw [heq, Finset.sum_range_succ _ (m + 1)]
    simp
  -- the Newton quotient of the derivative of order `m` at the point `c ≠ x`
  have hder : HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m + 1) f x) x := by
    rw [iteratedDeriv_succ]
    exact (hD m (Nat.lt_succ_self m) x hxJ).hasDerivAt
  have hclose : ⋆(slope (iteratedDeriv m f) x) c ≊ ((iteratedDeriv (m + 1) f x : ℝ) : ℝ*) := by
    rw [starMap_slope_apply]
    exact hasDerivWithinAt_iff_infClose.1 hder.hasDerivWithinAt c
      (by rw [starSet_univ]; exact mem_univ _) hcx (hne h0)
  refine ⟨(⋆(slope (iteratedDeriv m f) x) c - ((iteratedDeriv (m + 1) f x : ℝ) : ℝ*)) *
    ((1 / (m + 1).factorial : ℝ) : ℝ*), Infinitesimal.mul_limited hclose (limited_coe _), ?_⟩
  rw [heq, Finset.sum_range_succ _ (m + 1), hcoef]
  ring

/-- **Section 8.10, the case of order one.** For $`n = 1` the expansion of Exercise 8.10.2
is the incremental equation of Theorem 8.2.2:
$`{}^*f(x + \Delta x) = f(x) + f'(x)\,\Delta x + \varepsilon\,\Delta x`. -/
theorem exists_infinitesimal_taylor_increment_one (hf : DifferentiableAt ℝ f x)
    (hΔ : Infinitesimal Δ) :
    ∃ η : ℝ*, Infinitesimal η ∧ ⋆f (x + Δ) = f x + (deriv f x : ℝ) * Δ + η * Δ :=
  hf.hasDerivAt.incremental_equation hΔ

end TaylorIncrement

end Goldblatt
