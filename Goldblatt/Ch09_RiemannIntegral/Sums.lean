import Mathlib
import Goldblatt.Ch02_LargeSets
import Goldblatt.Ch03_Ultrapower
import Goldblatt.Ch05_GreatAndSmall
import Goldblatt.Ch06_Sequences
import Goldblatt.Ch07_Continuity
import Goldblatt.Ch08_Differentiation

/-!
# 9 (part 1). Riemann Sums: Section 9.1

This is the first of three parts of Chapter 9 (the overview is on the chapter page
{lit}`Goldblatt.Ch09_RiemannIntegral`). It sets up the standard theory of upper, lower and
ordinary Riemann sums over a partition of a closed interval, specialises it to the partition
determined by a single positive width, regards the three sums as functions of that width, and
extends them to positive hyperreal widths. It ends with Theorem 9.1.1 and Exercise 9.1.2: for
a continuous or a monotonic function, the upper and the lower sum of an infinitesimal width
are infinitely close.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## 9.1 Riemann Sums

Throughout, $`f` is a real function that is bounded on the interval $`[a, b]`. A partition
cuts the interval into finitely many subintervals, and to each subinterval $`[x, y]` three
rectangles of width $`y - x` are attached: one whose height is the least upper bound of $`f`
on the subinterval, one whose height is the greatest lower bound, and one whose height is
the value $`f(x)` at the left end. Adding the areas over the subintervals of the partition
gives the upper, the lower and the ordinary Riemann sum.

The section has a standard half and a hyperreal half. The standard half proves the facts
the book quotes from the standard theory: the chain of inequalities between the three sums,
the fact that every lower sum is below every upper sum, the effect of refining a partition,
and an estimate (used in Section 9.2) that compares the sums of the partition of width
$`\Delta x` with those of an arbitrary partition. The hyperreal half extends the sums, as
functions of the width, to the positive hyperreals, transfers the inequalities, and proves
that for a continuous or monotonic function the extended upper and lower sums at an
infinitesimal width differ by an infinitesimal.

### Bounded functions, suprema and infima on an interval
-/

section IntervalFunctions

variable {f g : ℝ → ℝ} {A A' : Set ℝ} {a b x y x' y' : ℝ}

/-- **Section 9.1.** The function $`f` is _bounded_ on the set $`A`: there is a real number
$`B` with $`|f(x)| \le B` for all $`x \in A`. This is the standing hypothesis of the
chapter, with $`A = [a, b]`. -/
def BoundedOn (f : ℝ → ℝ) (A : Set ℝ) : Prop := ∃ B : ℝ, ∀ x ∈ A, |f x| ≤ B

/-- A function bounded on a set is bounded on every subset. -/
theorem BoundedOn.mono (h : BoundedOn f A) (hA : A' ⊆ A) : BoundedOn f A' :=
  let ⟨B, hB⟩ := h
  ⟨B, fun x hx => hB x (hA hx)⟩

/-- The set of values on $`A` of a function bounded on $`A` is bounded above. -/
theorem BoundedOn.bddAbove (h : BoundedOn f A) : BddAbove (f '' A) := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B, by rintro _ ⟨x, hx, rfl⟩; exact (le_abs_self _).trans (hB x hx)⟩

/-- The set of values on $`A` of a function bounded on $`A` is bounded below. -/
theorem BoundedOn.bddBelow (h : BoundedOn f A) : BddBelow (f '' A) := by
  obtain ⟨B, hB⟩ := h
  exact ⟨-B, by rintro _ ⟨x, hx, rfl⟩; exact neg_le_of_abs_le (hB x hx)⟩

/-- The negative of a bounded function is bounded. -/
theorem BoundedOn.neg (h : BoundedOn f A) : BoundedOn (fun t => -f t) A :=
  let ⟨B, hB⟩ := h
  ⟨B, fun x hx => by simpa using hB x hx⟩

/-- **Section 9.2, remark.** A function continuous on $`[a, b]` is bounded there, by the
extreme value theorem of Section 7.6. -/
theorem boundedOn_Icc_of_continuousOn (hf : ContinuousOn f (Icc a b)) :
    BoundedOn f (Icc a b) := by
  rcases le_or_gt a b with hab | hab
  · obtain ⟨c, _, d, _, h⟩ := extreme_value_Icc hab hf
    exact ⟨max |f c| |f d|, fun t ht => abs_le_max_abs_abs (h t ht).1 (h t ht).2⟩
  · exact ⟨0, fun t ht => absurd (ht.1.trans ht.2) (not_le.2 hab)⟩

/-- **Section 9.2, remark.** A function that is nondecreasing on $`[a, b]` is bounded there:
its values lie between $`f(a)` and $`f(b)`. -/
theorem boundedOn_Icc_of_monotoneOn (hf : MonotoneOn f (Icc a b)) : BoundedOn f (Icc a b) :=
  ⟨max |f a| |f b|, fun _ ht => abs_le_max_abs_abs
    (hf (left_mem_Icc.2 (ht.1.trans ht.2)) ht ht.1)
    (hf ht (right_mem_Icc.2 (ht.1.trans ht.2)) ht.2)⟩

/-- **Section 9.2, remark.** A function that is nonincreasing on $`[a, b]` is bounded
there. -/
theorem boundedOn_Icc_of_antitoneOn (hf : AntitoneOn f (Icc a b)) : BoundedOn f (Icc a b) :=
  ⟨max |f b| |f a|, fun _ ht => abs_le_max_abs_abs
    (hf ht (right_mem_Icc.2 (ht.1.trans ht.2)) ht.2)
    (hf (left_mem_Icc.2 (ht.1.trans ht.2)) ht ht.1)⟩

/-- **Section 9.1.** The least upper bound $`M` of the values of $`f` on the interval
$`[x, y]`. For a subinterval $`[x_{i-1}, x_i]` of a partition this is the number the book
calls $`M_i`. -/
def supOn (f : ℝ → ℝ) (x y : ℝ) : ℝ := sSup (f '' Icc x y)

/-- **Section 9.1.** The greatest lower bound $`m` of the values of $`f` on the interval
$`[x, y]`. For a subinterval of a partition this is the book's $`m_i`. -/
def infOn (f : ℝ → ℝ) (x y : ℝ) : ℝ := sInf (f '' Icc x y)

/-- Every value of $`f` on $`[x, y]` is at most the supremum. -/
theorem le_supOn (h : BoundedOn f (Icc x y)) {t : ℝ} (ht : t ∈ Icc x y) : f t ≤ supOn f x y :=
  le_csSup h.bddAbove (mem_image_of_mem f ht)

/-- Every value of $`f` on $`[x, y]` is at least the infimum. -/
theorem infOn_le (h : BoundedOn f (Icc x y)) {t : ℝ} (ht : t ∈ Icc x y) : infOn f x y ≤ f t :=
  csInf_le h.bddBelow (mem_image_of_mem f ht)

/-- An upper bound of the values of $`f` on a nonempty interval bounds the supremum. -/
theorem supOn_le (hxy : x ≤ y) {M : ℝ} (h : ∀ t ∈ Icc x y, f t ≤ M) : supOn f x y ≤ M :=
  csSup_le ((nonempty_Icc.2 hxy).image f) (by rintro _ ⟨t, ht, rfl⟩; exact h t ht)

/-- A lower bound of the values of $`f` on a nonempty interval is below the infimum. -/
theorem le_infOn (hxy : x ≤ y) {m : ℝ} (h : ∀ t ∈ Icc x y, m ≤ f t) : m ≤ infOn f x y :=
  le_csInf ((nonempty_Icc.2 hxy).image f) (by rintro _ ⟨t, ht, rfl⟩; exact h t ht)

/-- On a nonempty interval the infimum is at most the supremum. -/
theorem infOn_le_supOn (h : BoundedOn f (Icc x y)) (hxy : x ≤ y) : infOn f x y ≤ supOn f x y :=
  (infOn_le h (left_mem_Icc.2 hxy)).trans (le_supOn h (left_mem_Icc.2 hxy))

/-- The supremum over a subinterval is at most the supremum over the interval. -/
theorem supOn_mono (h : BoundedOn f (Icc x' y')) (hxy : x ≤ y) (hx : x' ≤ x) (hy : y ≤ y') :
    supOn f x y ≤ supOn f x' y' :=
  supOn_le hxy fun _ ht => le_supOn h ⟨hx.trans ht.1, ht.2.trans hy⟩

/-- The infimum over a subinterval is at least the infimum over the interval. -/
theorem infOn_mono (h : BoundedOn f (Icc x' y')) (hxy : x ≤ y) (hx : x' ≤ x) (hy : y ≤ y') :
    infOn f x' y' ≤ infOn f x y :=
  le_infOn hxy fun _ ht => infOn_le h ⟨hx.trans ht.1, ht.2.trans hy⟩

/-- The infimum of $`f` is the negative of the supremum of $`-f`. This identity lets every
statement about lower sums be read off from the corresponding statement about upper sums. -/
theorem infOn_eq_neg_supOn_neg (f : ℝ → ℝ) (x y : ℝ) :
    infOn f x y = -supOn (fun t => -f t) x y := by
  rw [infOn, supOn, Real.sInf_def, ← Set.image_neg_eq_neg, Set.image_image]

/-- If the supremum of $`f` on a nonempty interval is bounded by $`B` in absolute value when
$`f` is. -/
theorem abs_supOn_le (hxy : x ≤ y) {B : ℝ} (hB : ∀ t ∈ Icc x y, |f t| ≤ B) :
    |supOn f x y| ≤ B :=
  abs_le.2 ⟨(neg_le_of_abs_le (hB x (left_mem_Icc.2 hxy))).trans
    (le_supOn ⟨B, hB⟩ (left_mem_Icc.2 hxy)),
    supOn_le hxy fun t ht => (le_abs_self _).trans (hB t ht)⟩

/-- **Section 9.1, oscillation.** If the values of $`g` at any two points of a nonempty
interval differ by at most $`K`, then the supremum and the infimum of $`g` on the interval
differ by at most $`K`. The difference $`M - m` is the _oscillation_ of the function on the
interval. -/
theorem supOn_sub_infOn_le (hxy : x ≤ y) {K : ℝ}
    (h : ∀ s ∈ Icc x y, ∀ t ∈ Icc x y, g t - g s ≤ K) : supOn g x y - infOn g x y ≤ K := by
  have h1 : supOn g x y ≤ infOn g x y + K := by
    refine supOn_le hxy fun t ht => ?_
    have : g t - K ≤ infOn g x y := le_infOn hxy fun s hs => by linarith [h s hs t ht]
    linarith
  linarith

end IntervalFunctions

/-!
### Partitions and their Riemann sums
-/

section Partitions

variable {f g : ℝ → ℝ} {a b : ℝ}

/-- **Section 9.1.** A _partition_ of $`[a, b]`: a finite list of points
$`a = x_0 < x_1 < \cdots < x_n = b`. The points are given by a function on the natural
numbers of which only the values at $`0, \dots, n` matter. A partition with $`n = 0` exists
exactly when $`a = b`. -/
structure IntervalPartition (a b : ℝ) where
  /-- The number $`n` of subintervals. -/
  n : ℕ
  /-- The points $`x_0, \dots, x_n` of the partition. -/
  pt : ℕ → ℝ
  /-- The first point is $`a`. -/
  pt_zero : pt 0 = a
  /-- The last point is $`b`. -/
  pt_n : pt n = b
  /-- The points are strictly increasing. -/
  lt_succ : ∀ i < n, pt i < pt (i + 1)

namespace IntervalPartition

variable (P Q : IntervalPartition a b)

/-- The points of a partition are nondecreasing in the index. -/
theorem pt_le_pt {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.n) : P.pt i ≤ P.pt j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (ih (by omega)).trans (P.lt_succ k (by omega)).le

/-- The points of a partition are strictly increasing in the index. -/
theorem pt_lt_pt {i j : ℕ} (hij : i < j) (hj : j ≤ P.n) : P.pt i < P.pt j :=
  (P.lt_succ i (by omega)).trans_le (P.pt_le_pt (by omega) hj)

/-- A smaller point has a smaller index. -/
theorem lt_of_pt_lt {i j : ℕ} (hi : i ≤ P.n) (h : P.pt i < P.pt j) : i < j := by
  by_contra hc
  exact absurd (P.pt_le_pt (not_lt.1 hc) hi) (not_le.2 h)

/-- Every point of a partition of $`[a, b]` is at least $`a`. -/
theorem le_pt {i : ℕ} (hi : i ≤ P.n) : a ≤ P.pt i := by
  simpa [P.pt_zero] using P.pt_le_pt (Nat.zero_le i) hi

/-- Every point of a partition of $`[a, b]` is at most $`b`. -/
theorem pt_le {i : ℕ} (hi : i ≤ P.n) : P.pt i ≤ b := by
  simpa [P.pt_n] using P.pt_le_pt hi le_rfl

include P in
/-- An interval that has a partition is not reversed. -/
theorem le : a ≤ b := by
  simpa [P.pt_zero, P.pt_n] using P.pt_le_pt (Nat.zero_le _) le_rfl

/-- Each subinterval of a partition of $`[a, b]` is included in $`[a, b]`. -/
theorem Icc_subset {i : ℕ} (hi : i < P.n) : Icc (P.pt i) (P.pt (i + 1)) ⊆ Icc a b :=
  Icc_subset_Icc (P.le_pt hi.le) (P.pt_le hi)

/-- **Section 9.1.** The sum over the subintervals $`[x_i, x_{i+1}]` of a partition of the
values $`g(x_i, x_{i+1})` of a function $`g` of intervals. The three Riemann sums are the
cases in which $`g(x, y)` is the area of a rectangle on $`[x, y]`. -/
def sum (g : ℝ → ℝ → ℝ) : ℝ := ∑ i ∈ Finset.range P.n, g (P.pt i) (P.pt (i + 1))

/-- A sum over a partition is monotone in the function of intervals. -/
theorem sum_le_sum {g g' : ℝ → ℝ → ℝ}
    (h : ∀ i < P.n, g (P.pt i) (P.pt (i + 1)) ≤ g' (P.pt i) (P.pt (i + 1))) :
    P.sum g ≤ P.sum g' :=
  Finset.sum_le_sum fun i hi => h i (Finset.mem_range.1 hi)

/-- **Section 9.1.** The widths of the subintervals of a partition of $`[a, b]` add up to
$`b - a`; more generally $`\sum_i c\,\Delta x_i = c(b - a)`. -/
theorem sum_const_mul (c : ℝ) : P.sum (fun x y => c * (y - x)) = c * (b - a) := by
  rw [sum, ← Finset.mul_sum, Finset.sum_range_sub (fun i => P.pt i), P.pt_n, P.pt_zero]

/-- A sum over a partition is additive in the function of intervals. -/
theorem sum_sub (g g' : ℝ → ℝ → ℝ) : P.sum (fun x y => g x y - g' x y) = P.sum g - P.sum g' := by
  simp [sum, Finset.sum_sub_distrib]

/-- **Section 9.1.** The _upper Riemann sum_ $`U_a^b(f, P) = \sum_i M_i\,\Delta x_i`. -/
def upperSum (f : ℝ → ℝ) : ℝ := P.sum fun x y => supOn f x y * (y - x)

/-- **Section 9.1.** The _lower Riemann sum_ $`L_a^b(f, P) = \sum_i m_i\,\Delta x_i`. -/
def lowerSum (f : ℝ → ℝ) : ℝ := P.sum fun x y => infOn f x y * (y - x)

/-- **Section 9.1.** The _ordinary Riemann sum_
$`S_a^b(f, P) = \sum_i f(x_{i-1})\,\Delta x_i`, in which each rectangle has the height of the
function at the left end of its base. -/
def ordSum (f : ℝ → ℝ) : ℝ := P.sum fun x y => f x * (y - x)

/-- The lower sum of $`f` is the negative of the upper sum of $`-f`. -/
theorem lowerSum_eq_neg_upperSum_neg (f : ℝ → ℝ) :
    P.lowerSum f = -P.upperSum fun t => -f t := by
  simp only [lowerSum, upperSum, sum, infOn_eq_neg_supOn_neg, neg_mul, Finset.sum_neg_distrib]

/-- **Section 9.1.** $`L_a^b(f, P) \le S_a^b(f, P)`. -/
theorem lowerSum_le_ordSum (hf : BoundedOn f (Icc a b)) : P.lowerSum f ≤ P.ordSum f :=
  P.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
    (infOn_le (hf.mono (P.Icc_subset hi)) (left_mem_Icc.2 (P.lt_succ i hi).le))
    (sub_nonneg.2 (P.lt_succ i hi).le)

/-- **Section 9.1.** $`S_a^b(f, P) \le U_a^b(f, P)`. -/
theorem ordSum_le_upperSum (hf : BoundedOn f (Icc a b)) : P.ordSum f ≤ P.upperSum f :=
  P.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
    (le_supOn (hf.mono (P.Icc_subset hi)) (left_mem_Icc.2 (P.lt_succ i hi).le))
    (sub_nonneg.2 (P.lt_succ i hi).le)

/-- **Section 9.1.** $`U_a^b(f, P) \le M(b - a)`, where $`M` is the least upper bound of
$`f` on $`[a, b]`. -/
theorem upperSum_le (hf : BoundedOn f (Icc a b)) : P.upperSum f ≤ supOn f a b * (b - a) := by
  rw [← P.sum_const_mul]
  exact P.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
    (supOn_mono hf (P.lt_succ i hi).le (P.le_pt hi.le) (P.pt_le hi))
    (sub_nonneg.2 (P.lt_succ i hi).le)

/-- **Section 9.1.** $`m(b - a) \le L_a^b(f, P)`, where $`m` is the greatest lower bound of
$`f` on $`[a, b]`. -/
theorem le_lowerSum (hf : BoundedOn f (Icc a b)) : infOn f a b * (b - a) ≤ P.lowerSum f := by
  rw [← P.sum_const_mul]
  exact P.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
    (infOn_mono hf (P.lt_succ i hi).le (P.le_pt hi.le) (P.pt_le hi))
    (sub_nonneg.2 (P.lt_succ i hi).le)

/-- **Section 9.1.** The chain of inequalities
$$`m(b - a) \le L_a^b(f, P) \le S_a^b(f, P) \le U_a^b(f, P) \le M(b - a)`
for a function bounded on $`[a, b]` with least upper bound $`M` and greatest lower bound
$`m` there. -/
theorem lowerSum_ordSum_upperSum_chain (hf : BoundedOn f (Icc a b)) :
    infOn f a b * (b - a) ≤ P.lowerSum f ∧ P.lowerSum f ≤ P.ordSum f ∧
      P.ordSum f ≤ P.upperSum f ∧ P.upperSum f ≤ supOn f a b * (b - a) :=
  ⟨P.le_lowerSum hf, P.lowerSum_le_ordSum hf, P.ordSum_le_upperSum hf, P.upperSum_le hf⟩

end IntervalPartition

end Partitions

/-!
### Comparing two partitions

The book obtains the inequality $`L_a^b(f, P_1) \le U_a^b(f, P_2)` by passing to a common
refinement of the two partitions. The same double counting is organised here without building
the refinement. For subintervals $`I` of the first partition and $`J` of the second, let
$`\ell(I, J)` be the length of $`I \cap J`. The lengths $`\ell(I, J)` over all $`J` add up to
the length of $`I`, and over all $`I` to the length of $`J`, so each Riemann sum is a double
sum over the pairs $`(I, J)`; and two heights need only be compared for pairs with
$`\ell(I, J) > 0`, that is, for subintervals that share a point. The pairs with
$`\ell(I, J) > 0` are exactly the subintervals of the common refinement.
-/

section Overlap

variable {f : ℝ → ℝ} {a b u v x y : ℝ}

/-- The point of $`[u, v]` nearest to $`t`. -/
def intervalClamp (u v t : ℝ) : ℝ := max u (min v t)

/-- **Section 9.1, tool.** The length of the intersection of $`[u, v]` and $`[x, y]`,
written as a difference so that it telescopes along a partition. -/
def intervalOverlap (u v x y : ℝ) : ℝ := intervalClamp u v y - intervalClamp u v x

/-- The length of an intersection is not negative. -/
theorem intervalOverlap_nonneg (u v : ℝ) (hxy : x ≤ y) : 0 ≤ intervalOverlap u v x y :=
  sub_nonneg.2 (max_le_max le_rfl (min_le_min le_rfl hxy))

/-- The length of $`[u, v] \cap [x, y]` does not depend on the order of the two intervals. -/
theorem intervalOverlap_comm (huv : u ≤ v) (hxy : x ≤ y) :
    intervalOverlap u v x y = intervalOverlap x y u v := by
  simp only [intervalOverlap, intervalClamp, max_def, min_def]
  split_ifs <;> linarith

/-- The intersection is no longer than the second interval. -/
theorem intervalOverlap_le_sub (u v : ℝ) (hxy : x ≤ y) : intervalOverlap u v x y ≤ y - x := by
  simp only [intervalOverlap, intervalClamp, max_def, min_def]
  split_ifs <;> linarith

/-- If two intervals intersect in positive length, the larger of the left ends is below the
smaller of the right ends, so the intervals share a point. -/
theorem lt_of_intervalOverlap_pos (h : 0 < intervalOverlap u v x y) : max u x < min v y := by
  simp only [intervalOverlap, intervalClamp, max_def, min_def] at h ⊢
  split_ifs at h ⊢ <;> linarith

/-- **Section 9.1, tool.** An interval $`[x, y]` of width at most $`\Delta` that has $`p` in
its interior lies in $`[p - \Delta, p + \Delta]`, so its intersection with any interval
having $`p` as an end point is no longer than its intersection with
$`[p - \Delta, p + \Delta]`. -/
theorem intervalOverlap_le_of_lt_left {Δ : ℝ} (hxy : x ≤ y) (hΔ : y - x ≤ Δ) (hx : x < u) :
    intervalOverlap x y u v ≤ intervalOverlap (u - Δ) (u + Δ) x y := by
  simp only [intervalOverlap, intervalClamp, max_def, min_def]
  split_ifs <;> linarith

/-- The companion of {name}`intervalOverlap_le_of_lt_left` for the right end point. -/
theorem intervalOverlap_le_of_lt_right {Δ : ℝ} (hxy : x ≤ y) (hΔ : y - x ≤ Δ) (huv : u ≤ v)
    (hy : v < y) : intervalOverlap x y u v ≤ intervalOverlap (v - Δ) (v + Δ) x y := by
  simp only [intervalOverlap, intervalClamp, max_def, min_def]
  split_ifs <;> linarith

namespace IntervalPartition

variable (P Q : IntervalPartition a b)

/-- **Section 9.1, tool.** The intersections of a subinterval $`[u, v]` of $`[a, b]` with
the subintervals of a partition of $`[a, b]` have total length $`v - u`. -/
theorem sum_intervalOverlap (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    ∑ j ∈ Finset.range P.n, intervalOverlap u v (P.pt j) (P.pt (j + 1)) = v - u := by
  simp only [intervalOverlap]
  rw [Finset.sum_range_sub (fun j => intervalClamp u v (P.pt j)), P.pt_n, P.pt_zero,
    intervalClamp, intervalClamp, min_eq_left hvb, max_eq_right huv,
    max_eq_left ((min_le_right _ _).trans hau)]

/-- The intersections of any interval $`[u, v]` with the subintervals of a partition have
total length at most $`v - u`. -/
theorem sum_intervalOverlap_le (huv : u ≤ v) :
    ∑ j ∈ Finset.range P.n, intervalOverlap u v (P.pt j) (P.pt (j + 1)) ≤ v - u := by
  simp only [intervalOverlap]
  rw [Finset.sum_range_sub (fun j => intervalClamp u v (P.pt j))]
  have h1 : intervalClamp u v (P.pt P.n) ≤ v := max_le huv (min_le_left _ _)
  have h2 : u ≤ intervalClamp u v (P.pt 0) := le_max_left _ _
  linarith

/-- **Section 9.1, tool (double counting).** A sum $`\sum_I c(I)\,|I|` over the subintervals
of a partition $`P` is the double sum of $`c(I)\,\ell(I, J)` over the subintervals $`I` of
$`P` and $`J` of a second partition $`Q`. -/
theorem sum_mul_eq_sum_sum (c : ℝ → ℝ → ℝ) :
    P.sum (fun x y => c x y * (y - x)) =
      ∑ i ∈ Finset.range P.n, ∑ j ∈ Finset.range Q.n,
        c (P.pt i) (P.pt (i + 1)) *
          intervalOverlap (P.pt i) (P.pt (i + 1)) (Q.pt j) (Q.pt (j + 1)) := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [← Finset.mul_sum, Q.sum_intervalOverlap (P.le_pt hi'.le) (P.lt_succ i hi').le (P.pt_le hi')]

/-- **Section 9.1, tool (comparison through the common refinement).** Let $`c` and $`d`
assign heights to intervals. If $`c(I) \le d(J)` whenever a subinterval $`I` of $`P` and a
subinterval $`J` of $`Q` overlap in more than a point, then
$`\sum_I c(I)\,|I| \le \sum_J d(J)\,|J|`. -/
theorem sum_mul_le_sum_mul (c d : ℝ → ℝ → ℝ)
    (h : ∀ i < P.n, ∀ j < Q.n, max (P.pt i) (Q.pt j) < min (P.pt (i + 1)) (Q.pt (j + 1)) →
      c (P.pt i) (P.pt (i + 1)) ≤ d (Q.pt j) (Q.pt (j + 1))) :
    P.sum (fun x y => c x y * (y - x)) ≤ Q.sum (fun x y => d x y * (y - x)) := by
  rw [P.sum_mul_eq_sum_sum Q, Q.sum_mul_eq_sum_sum P, Finset.sum_comm]
  refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have hj' := Finset.mem_range.1 hj
  rw [intervalOverlap_comm (Q.lt_succ j hj').le (P.lt_succ i hi').le]
  rcases (intervalOverlap_nonneg (P.pt i) (P.pt (i + 1)) (Q.lt_succ j hj').le).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right (h i hi' j hj' (lt_of_intervalOverlap_pos h0)) h0.le

/-- **Section 9.1.** Any lower sum is less than or equal to any upper sum:
$`L_a^b(f, P_1) \le U_a^b(f, P_2)` for all partitions $`P_1`, $`P_2` of $`[a, b]`. The book
refers to the standard argument by refinement; here it is the comparison
{name}`IntervalPartition.sum_mul_le_sum_mul`, applied to the infimum on a subinterval of the
first partition and the supremum on an overlapping subinterval of the second, which are
separated by the value of $`f` at a common point. -/
theorem lowerSum_le_upperSum (hf : BoundedOn f (Icc a b)) : P.lowerSum f ≤ Q.upperSum f := by
  refine P.sum_mul_le_sum_mul Q (infOn f) (supOn f) fun i hi j hj hlt => ?_
  have h1 : max (P.pt i) (Q.pt j) ∈ Icc (P.pt i) (P.pt (i + 1)) :=
    ⟨le_max_left _ _, hlt.le.trans (min_le_left _ _)⟩
  have h2 : max (P.pt i) (Q.pt j) ∈ Icc (Q.pt j) (Q.pt (j + 1)) :=
    ⟨le_max_right _ _, hlt.le.trans (min_le_right _ _)⟩
  exact (infOn_le (hf.mono (P.Icc_subset hi)) h1).trans (le_supOn (hf.mono (Q.Icc_subset hj)) h2)

/-- **Section 9.1.** The partition $`Q` _refines_ $`P`: every point of $`P` is a point of
$`Q`. -/
def Refines (Q P : IntervalPartition a b) : Prop := ∀ i ≤ P.n, ∃ j ≤ Q.n, Q.pt j = P.pt i

/-- If $`Q` refines $`P`, every subinterval of $`Q` that overlaps a subinterval of $`P` in
more than a point is included in it. -/
theorem Refines.subinterval {P Q : IntervalPartition a b} (h : Q.Refines P) {i j : ℕ}
    (hi : i < P.n) (hj : j < Q.n)
    (hlt : max (Q.pt j) (P.pt i) < min (Q.pt (j + 1)) (P.pt (i + 1))) :
    P.pt i ≤ Q.pt j ∧ Q.pt (j + 1) ≤ P.pt (i + 1) := by
  obtain ⟨k, hk, hk'⟩ := h i hi.le
  obtain ⟨l, hl, hl'⟩ := h (i + 1) hi
  have h1 : Q.pt k < Q.pt (j + 1) := by
    rw [hk']; exact (le_max_right _ _).trans_lt (hlt.trans_le (min_le_left _ _))
  have h2 : Q.pt j < Q.pt l := by
    rw [hl']; exact (le_max_left _ _).trans_lt (hlt.trans_le (min_le_right _ _))
  have h3 := Q.lt_of_pt_lt hk h1
  have h4 := Q.lt_of_pt_lt hj.le h2
  exact ⟨hk' ▸ Q.pt_le_pt (by omega) hj.le, hl' ▸ Q.pt_le_pt (by omega) hl⟩

/-- **Section 9.1 (refinement).** Refining a partition does not increase the upper sum. -/
theorem Refines.upperSum_le {P Q : IntervalPartition a b} (h : Q.Refines P)
    (hf : BoundedOn f (Icc a b)) : Q.upperSum f ≤ P.upperSum f := by
  refine Q.sum_mul_le_sum_mul P (supOn f) (supOn f) fun j hj i hi hlt => ?_
  obtain ⟨h1, h2⟩ := h.subinterval hi hj hlt
  exact supOn_mono (hf.mono (P.Icc_subset hi)) (Q.lt_succ j hj).le h1 h2

/-- **Section 9.1 (refinement).** Refining a partition does not decrease the lower sum. -/
theorem Refines.lowerSum_le {P Q : IntervalPartition a b} (h : Q.Refines P)
    (hf : BoundedOn f (Icc a b)) : P.lowerSum f ≤ Q.lowerSum f := by
  rw [P.lowerSum_eq_neg_upperSum_neg, Q.lowerSum_eq_neg_upperSum_neg]
  exact neg_le_neg (h.upperSum_le hf.neg)

end IntervalPartition

end Overlap

/-!
### The partition determined by a width

A positive real number $`\Delta x` determines a partition of $`[a, b]`: the points
$`a, a + \Delta x, a + 2\Delta x, \dots` as long as they stay below $`b`, and then $`b`. All
subintervals have width $`\Delta x` except possibly the last, which may be shorter. The
number of subintervals is the least $`n` with $`a + n\,\Delta x \ge b`.
-/

section Mesh

variable {f g : ℝ → ℝ} {a b Δ Δ' : ℝ}

/-- **Section 9.1.** The number of subintervals of the partition of $`[a, b]` of width
$`\Delta x`: the least natural number $`n` with $`a + n\,\Delta x \ge b`. -/
def meshCard (a b Δ : ℝ) : ℕ := ⌈(b - a) / Δ⌉₊

/-- **Section 9.1.** The $`k`-th point of the partition of $`[a, b]` of width $`\Delta x`:
the point $`a + k\,\Delta x`, cut off at $`b`. -/
def meshPoint (a b Δ : ℝ) (k : ℕ) : ℝ := min (a + k * Δ) b

/-- For a positive width, $`k` is less than the number of subintervals exactly when
$`a + k\,\Delta x < b`. -/
theorem lt_meshCard_iff (hΔ : 0 < Δ) {k : ℕ} : k < meshCard a b Δ ↔ a + k * Δ < b := by
  rw [meshCard, Nat.lt_ceil, lt_div_iff₀ hΔ]
  constructor <;> intro h <;> linarith

/-- The first point of the partition of width $`\Delta x` is $`a`. -/
theorem meshPoint_zero (hab : a ≤ b) : meshPoint a b Δ 0 = a := by simp [meshPoint, hab]

/-- Before the last point, the $`k`-th point is $`a + k\,\Delta x`. -/
theorem meshPoint_of_lt (hΔ : 0 < Δ) {k : ℕ} (hk : k < meshCard a b Δ) :
    meshPoint a b Δ k = a + k * Δ :=
  min_eq_left ((lt_meshCard_iff hΔ).1 hk).le

/-- The last point of the partition of width $`\Delta x` is $`b`. -/
theorem meshPoint_meshCard (hΔ : 0 < Δ) : meshPoint a b Δ (meshCard a b Δ) = b := by
  refine min_eq_right ?_
  by_contra h
  exact lt_irrefl _ ((lt_meshCard_iff hΔ).2 (not_le.1 h))

/-- The points of the partition of width $`\Delta x` increase strictly up to the last. -/
theorem meshPoint_lt_succ (hΔ : 0 < Δ) {k : ℕ} (hk : k < meshCard a b Δ) :
    meshPoint a b Δ k < meshPoint a b Δ (k + 1) := by
  have h := (lt_meshCard_iff hΔ).1 hk
  rw [meshPoint_of_lt hΔ hk, meshPoint, lt_min_iff]
  exact ⟨by push_cast; linarith, h⟩

/-- **Section 9.1.** Every subinterval of the partition of width $`\Delta x` has width at
most $`\Delta x`. -/
theorem meshPoint_succ_sub_le (hΔ : 0 < Δ) (k : ℕ) :
    meshPoint a b Δ (k + 1) - meshPoint a b Δ k ≤ Δ := by
  simp only [meshPoint, min_def]
  push_cast
  split_ifs <;> linarith

/-- **Section 9.1.** If $`\Delta x \ge b - a > 0`, the partition of width $`\Delta x` has a
single subinterval: it is the partition with the two points $`a` and $`b`. -/
theorem meshCard_eq_one (hab : a < b) (h : b - a ≤ Δ) : meshCard a b Δ = 1 := by
  have hΔ : 0 < Δ := (sub_pos.2 hab).trans_le h
  rw [meshCard, Nat.ceil_eq_iff one_ne_zero]
  exact ⟨by simpa using div_pos (sub_pos.2 hab) hΔ, by simpa using (div_le_one hΔ).2 h⟩

/-- **Section 9.1.** The partition $`P_{\Delta x}` of $`[a, b]` into subintervals of equal
width $`\Delta x`, with a possibly smaller last subinterval. If $`\Delta x \ge b - a > 0` it
is the partition with the two points $`a` and $`b`. -/
def meshPartition (hab : a ≤ b) (hΔ : 0 < Δ) : IntervalPartition a b where
  n := meshCard a b Δ
  pt := meshPoint a b Δ
  pt_zero := meshPoint_zero hab
  pt_n := meshPoint_meshCard hΔ
  lt_succ := fun _ hi => meshPoint_lt_succ hΔ hi

/-- **Section 9.1.** The sum of the values of a function of intervals over the subintervals
of the partition of width $`\Delta x`, as a function of the width that is defined for every
real number (it is only meaningful for $`a \le b` and $`\Delta x > 0`). -/
def meshSumOf (g : ℝ → ℝ → ℝ) (a b Δ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (meshCard a b Δ), g (meshPoint a b Δ k) (meshPoint a b Δ (k + 1))

/-- For $`a \le b` and a positive width, {name}`meshSumOf` is the sum over the partition
{name}`meshPartition`. -/
theorem meshPartition_sum (hab : a ≤ b) (hΔ : 0 < Δ) (g : ℝ → ℝ → ℝ) :
    (meshPartition hab hΔ).sum g = meshSumOf g a b Δ := rfl

/-- **Section 9.1.** The upper Riemann sum $`U_a^b(f, \Delta x)` of the partition of width
$`\Delta x`, as a function of the real variable $`\Delta x`. -/
def upperSum (f : ℝ → ℝ) (a b Δ : ℝ) : ℝ := meshSumOf (fun x y => supOn f x y * (y - x)) a b Δ

/-- **Section 9.1.** The lower Riemann sum $`L_a^b(f, \Delta x)` of the partition of width
$`\Delta x`, as a function of the real variable $`\Delta x`. -/
def lowerSum (f : ℝ → ℝ) (a b Δ : ℝ) : ℝ := meshSumOf (fun x y => infOn f x y * (y - x)) a b Δ

/-- **Section 9.1.** The ordinary Riemann sum $`S_a^b(f, \Delta x)` of the partition of width
$`\Delta x`, as a function of the real variable $`\Delta x`: the sum
$`f(x_0)\Delta x + \cdots + f(x_{n-2})\Delta x + f(x_{n-1})(b - x_{n-1})`. -/
def ordSum (f : ℝ → ℝ) (a b Δ : ℝ) : ℝ := meshSumOf (fun x y => f x * (y - x)) a b Δ

/-- The upper sum of width $`\Delta x` is the upper sum of the partition $`P_{\Delta x}`. -/
theorem meshPartition_upperSum (hab : a ≤ b) (hΔ : 0 < Δ) (f : ℝ → ℝ) :
    (meshPartition hab hΔ).upperSum f = upperSum f a b Δ := rfl

/-- The lower sum of width $`\Delta x` is the lower sum of the partition $`P_{\Delta x}`. -/
theorem meshPartition_lowerSum (hab : a ≤ b) (hΔ : 0 < Δ) (f : ℝ → ℝ) :
    (meshPartition hab hΔ).lowerSum f = lowerSum f a b Δ := rfl

/-- The ordinary sum of width $`\Delta x` is the ordinary sum of the partition
$`P_{\Delta x}`. -/
theorem meshPartition_ordSum (hab : a ≤ b) (hΔ : 0 < Δ) (f : ℝ → ℝ) :
    (meshPartition hab hΔ).ordSum f = ordSum f a b Δ := rfl

/-- The lower sum of width $`\Delta x` of $`f` is the negative of the upper sum of $`-f`. -/
theorem lowerSum_eq_neg_upperSum_neg (f : ℝ → ℝ) (a b Δ : ℝ) :
    lowerSum f a b Δ = -upperSum (fun t => -f t) a b Δ := by
  simp only [lowerSum, upperSum, meshSumOf, infOn_eq_neg_supOn_neg, neg_mul,
    Finset.sum_neg_distrib]

/-- **Section 9.1.** $`L_a^b(f, \Delta x) \le S_a^b(f, \Delta x)` for real $`\Delta x > 0`. -/
theorem lowerSum_le_ordSum (hf : BoundedOn f (Icc a b)) (hab : a ≤ b) (hΔ : 0 < Δ) :
    lowerSum f a b Δ ≤ ordSum f a b Δ :=
  (meshPartition hab hΔ).lowerSum_le_ordSum hf

/-- **Section 9.1.** $`S_a^b(f, \Delta x) \le U_a^b(f, \Delta x)` for real $`\Delta x > 0`. -/
theorem ordSum_le_upperSum (hf : BoundedOn f (Icc a b)) (hab : a ≤ b) (hΔ : 0 < Δ) :
    ordSum f a b Δ ≤ upperSum f a b Δ :=
  (meshPartition hab hΔ).ordSum_le_upperSum hf

/-- **Section 9.1.** $`U_a^b(f, \Delta x) \le M(b - a)` for real $`\Delta x > 0`. -/
theorem upperSum_le_supOn_mul (hf : BoundedOn f (Icc a b)) (hab : a ≤ b) (hΔ : 0 < Δ) :
    upperSum f a b Δ ≤ supOn f a b * (b - a) :=
  (meshPartition hab hΔ).upperSum_le hf

/-- **Section 9.1.** $`m(b - a) \le L_a^b(f, \Delta x)` for real $`\Delta x > 0`. -/
theorem infOn_mul_le_lowerSum (hf : BoundedOn f (Icc a b)) (hab : a ≤ b) (hΔ : 0 < Δ) :
    infOn f a b * (b - a) ≤ lowerSum f a b Δ :=
  (meshPartition hab hΔ).le_lowerSum hf

/-- **Section 9.1.** $`L_a^b(f, \Delta x) \le U_a^b(f, \Delta y)` for all real
$`\Delta x, \Delta y > 0`. -/
theorem lowerSum_le_upperSum (hf : BoundedOn f (Icc a b)) (hab : a ≤ b) (hΔ : 0 < Δ)
    (hΔ' : 0 < Δ') : lowerSum f a b Δ ≤ upperSum f a b Δ' :=
  (meshPartition hab hΔ).lowerSum_le_upperSum (meshPartition hab hΔ') hf

/-- The difference of the upper and the lower sum is the sum of the oscillations times the
widths. -/
theorem IntervalPartition.upperSum_sub_lowerSum (P : IntervalPartition a b) (f : ℝ → ℝ) :
    P.upperSum f - P.lowerSum f = P.sum fun x y => (supOn f x y - infOn f x y) * (y - x) := by
  rw [IntervalPartition.upperSum, IntervalPartition.lowerSum, ← P.sum_sub]
  simp only [sub_mul]

/-- **Section 9.2, standard estimate (upper sums).** Let $`|f| \le B` on $`[a, b]` and let
$`P` be a partition of $`[a, b]` with $`n` subintervals. Then for every real
$`\Delta x > 0`,
$$`U_a^b(f, \Delta x) \le U_a^b(f, P) + 8Bn\,\Delta x.`
A subinterval of the partition of width $`\Delta x` either lies inside a subinterval of
$`P`, where its supremum is no larger, or has a point of $`P` in its interior; the
subintervals of the second kind lie within $`\Delta x` of the points of $`P` and so have
total length at most $`4n\,\Delta x`. This is the standard fact behind the statement, quoted
in Section 9.2 of the book, that the upper and lower sums of an integrable function
approximate each other as the width tends to zero. -/
theorem upperSum_le_add_mul (P : IntervalPartition a b) {B : ℝ}
    (hB : ∀ x ∈ Icc a b, |f x| ≤ B) (hΔ : 0 < Δ) :
    upperSum f a b Δ ≤ P.upperSum f + 8 * B * P.n * Δ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB a (left_mem_Icc.2 P.le))
  have hf : BoundedOn f (Icc a b) := ⟨B, hB⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : IntervalPartition a b, Q = meshPartition P.le hΔ := ⟨_, rfl⟩
  have hw : ∀ j, Q.pt (j + 1) - Q.pt j ≤ Δ := fun j => by
    rw [hQ]; exact meshPoint_succ_sub_le hΔ j
  have hUQ : upperSum f a b Δ = Q.upperSum f := by rw [hQ]; rfl
  rw [hUQ, IntervalPartition.upperSum, Q.sum_mul_eq_sum_sum P, Finset.sum_comm]
  have key : ∀ i ∈ Finset.range P.n,
      ∑ j ∈ Finset.range Q.n, supOn f (Q.pt j) (Q.pt (j + 1)) *
          intervalOverlap (Q.pt j) (Q.pt (j + 1)) (P.pt i) (P.pt (i + 1)) ≤
        supOn f (P.pt i) (P.pt (i + 1)) * (P.pt (i + 1) - P.pt i) + 8 * B * Δ := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hxi := (P.lt_succ i hi').le
    have hMP : |supOn f (P.pt i) (P.pt (i + 1))| ≤ B :=
      abs_supOn_le hxi fun t ht => hB t (P.Icc_subset hi' ht)
    calc ∑ j ∈ Finset.range Q.n, supOn f (Q.pt j) (Q.pt (j + 1)) *
          intervalOverlap (Q.pt j) (Q.pt (j + 1)) (P.pt i) (P.pt (i + 1))
        ≤ ∑ j ∈ Finset.range Q.n, (supOn f (P.pt i) (P.pt (i + 1)) *
            intervalOverlap (P.pt i) (P.pt (i + 1)) (Q.pt j) (Q.pt (j + 1)) +
            2 * B * (intervalOverlap (P.pt i - Δ) (P.pt i + Δ) (Q.pt j) (Q.pt (j + 1)) +
              intervalOverlap (P.pt (i + 1) - Δ) (P.pt (i + 1) + Δ) (Q.pt j) (Q.pt (j + 1)))) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := Finset.mem_range.1 hj
          have hyj := (Q.lt_succ j hj').le
          rw [intervalOverlap_comm hxi hyj]
          have ho := intervalOverlap_nonneg (Q.pt j) (Q.pt (j + 1)) hxi
          have e1 := intervalOverlap_nonneg (P.pt i - Δ) (P.pt i + Δ) hyj
          have e2 := intervalOverlap_nonneg (P.pt (i + 1) - Δ) (P.pt (i + 1) + Δ) hyj
          have hMQ : |supOn f (Q.pt j) (Q.pt (j + 1))| ≤ B :=
            abs_supOn_le hyj fun t ht => hB t (Q.Icc_subset hj' ht)
          by_cases hsub : P.pt i ≤ Q.pt j ∧ Q.pt (j + 1) ≤ P.pt (i + 1)
          · have := supOn_mono (hf.mono (P.Icc_subset hi')) hyj hsub.1 hsub.2
            nlinarith [mul_le_mul_of_nonneg_right this ho, mul_nonneg hB0 (add_nonneg e1 e2)]
          · rw [not_and_or, not_le, not_le] at hsub
            have hoe : intervalOverlap (Q.pt j) (Q.pt (j + 1)) (P.pt i) (P.pt (i + 1)) ≤
                intervalOverlap (P.pt i - Δ) (P.pt i + Δ) (Q.pt j) (Q.pt (j + 1)) +
                intervalOverlap (P.pt (i + 1) - Δ) (P.pt (i + 1) + Δ) (Q.pt j) (Q.pt (j + 1)) := by
              rcases hsub with h | h
              · linarith [intervalOverlap_le_of_lt_left (v := P.pt (i + 1)) hyj (hw j) h]
              · linarith [intervalOverlap_le_of_lt_right hyj (hw j) hxi h]
            nlinarith [mul_le_mul_of_nonneg_right (abs_le.1 hMQ).2 ho,
              mul_le_mul_of_nonneg_right (abs_le.1 hMP).1 ho, mul_le_mul_of_nonneg_left hoe hB0]
      _ = supOn f (P.pt i) (P.pt (i + 1)) *
            ∑ j ∈ Finset.range Q.n,
              intervalOverlap (P.pt i) (P.pt (i + 1)) (Q.pt j) (Q.pt (j + 1)) +
            2 * B * (∑ j ∈ Finset.range Q.n,
                intervalOverlap (P.pt i - Δ) (P.pt i + Δ) (Q.pt j) (Q.pt (j + 1)) +
              ∑ j ∈ Finset.range Q.n,
                intervalOverlap (P.pt (i + 1) - Δ) (P.pt (i + 1) + Δ) (Q.pt j) (Q.pt (j + 1))) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ supOn f (P.pt i) (P.pt (i + 1)) * (P.pt (i + 1) - P.pt i) + 8 * B * Δ := by
          rw [Q.sum_intervalOverlap (P.le_pt hi'.le) hxi (P.pt_le hi')]
          have h1 := Q.sum_intervalOverlap_le (u := P.pt i - Δ) (v := P.pt i + Δ) (by linarith)
          have h2 := Q.sum_intervalOverlap_le (u := P.pt (i + 1) - Δ) (v := P.pt (i + 1) + Δ)
            (by linarith)
          nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 h2) hB0]
  calc _ ≤ ∑ i ∈ Finset.range P.n,
        (supOn f (P.pt i) (P.pt (i + 1)) * (P.pt (i + 1) - P.pt i) + 8 * B * Δ) :=
        Finset.sum_le_sum key
    _ = P.upperSum f + 8 * B * P.n * Δ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          IntervalPartition.upperSum, IntervalPartition.sum]
        ring

/-- **Section 9.2, standard estimate (lower sums).** With $`|f| \le B` on $`[a, b]` and a
partition $`P` with $`n` subintervals,
$`L_a^b(f, P) - 8Bn\,\Delta x \le L_a^b(f, \Delta x)` for every real $`\Delta x > 0`. -/
theorem sub_mul_le_lowerSum (P : IntervalPartition a b) {B : ℝ}
    (hB : ∀ x ∈ Icc a b, |f x| ≤ B) (hΔ : 0 < Δ) :
    P.lowerSum f - 8 * B * P.n * Δ ≤ lowerSum f a b Δ := by
  have h := upperSum_le_add_mul (f := fun t => -f t) P (B := B)
    (fun x hx => by simpa using hB x hx) hΔ
  rw [lowerSum_eq_neg_upperSum_neg, P.lowerSum_eq_neg_upperSum_neg]
  linarith

/-- **Theorem 9.1.1, real form.** Let $`f` be continuous on $`[a, b]`. For every real
$`\Delta x > 0` there are points $`c, d \in [a, b]` with $`|c - d| \le \Delta x` and
$$`U_a^b(f, \Delta x) - L_a^b(f, \Delta x) \le \bigl(f(c) - f(d)\bigr)(b - a).`
These are the points at which the largest oscillation $`M_i - m_i` on a subinterval of the
partition is attained, which exist by the extreme value theorem. -/
theorem exists_points_upperSum_sub_lowerSum_le (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hΔ : 0 < Δ) :
    ∃ c ∈ Icc a b, ∃ d ∈ Icc a b, |c - d| ≤ Δ ∧
      upperSum f a b Δ - lowerSum f a b Δ ≤ (f c - f d) * (b - a) := by
  obtain ⟨P, hP⟩ : ∃ P : IntervalPartition a b, P = meshPartition hab hΔ := ⟨_, rfl⟩
  have hw : ∀ j, P.pt (j + 1) - P.pt j ≤ Δ := fun j => by
    rw [hP]; exact meshPoint_succ_sub_le hΔ j
  have hUL : upperSum f a b Δ - lowerSum f a b Δ = P.upperSum f - P.lowerSum f := by
    rw [hP]; rfl
  rw [hUL, P.upperSum_sub_lowerSum]
  rcases Nat.eq_zero_or_pos P.n with h0 | h0
  · refine ⟨a, left_mem_Icc.2 hab, a, left_mem_Icc.2 hab, by simpa using hΔ.le, ?_⟩
    simp [IntervalPartition.sum, h0]
  · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.range P.n)
      (fun i => supOn f (P.pt i) (P.pt (i + 1)) - infOn f (P.pt i) (P.pt (i + 1)))
      ⟨0, Finset.mem_range.2 h0⟩
    have hi' := Finset.mem_range.1 hi
    have hlt := P.lt_succ i hi'
    obtain ⟨d, hd, c, hc, hcd⟩ := extreme_value_Icc hlt.le (hf.mono (P.Icc_subset hi'))
    refine ⟨c, P.Icc_subset hi' hc, d, P.Icc_subset hi' hd, ?_, ?_⟩
    · rw [abs_le]
      constructor <;> linarith [hc.1, hc.2, hd.1, hd.2, hw i]
    · have h1 : supOn f (P.pt i) (P.pt (i + 1)) ≤ f c := supOn_le hlt.le fun t ht => (hcd t ht).2
      have h2 : f d ≤ infOn f (P.pt i) (P.pt (i + 1)) := le_infOn hlt.le fun t ht => (hcd t ht).1
      calc P.sum (fun x y => (supOn f x y - infOn f x y) * (y - x))
          ≤ P.sum (fun x y => (f c - f d) * (y - x)) :=
            P.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right
              ((hmax j (Finset.mem_range.2 hj)).trans (by linarith))
              (sub_nonneg.2 (P.lt_succ j hj).le)
        _ = (f c - f d) * (b - a) := P.sum_const_mul _

/-- **Exercise 9.1.2, first part.** If $`f` is nondecreasing on $`[a, b]`, then for every
real $`\Delta x > 0`,
$$`U_a^b(f, \Delta x) - L_a^b(f, \Delta x) \le \Delta x\,\bigl(f(b) - f(a)\bigr).`
On each subinterval the supremum is the value at the right end and the infimum the value at
the left end, each width is at most $`\Delta x`, and the differences of the values
telescope. -/
theorem upperSum_sub_lowerSum_le_of_monotoneOn (hab : a ≤ b) (hf : MonotoneOn f (Icc a b))
    (hΔ : 0 < Δ) : upperSum f a b Δ - lowerSum f a b Δ ≤ Δ * (f b - f a) := by
  obtain ⟨P, hP⟩ : ∃ P : IntervalPartition a b, P = meshPartition hab hΔ := ⟨_, rfl⟩
  have hw : ∀ j, P.pt (j + 1) - P.pt j ≤ Δ := fun j => by
    rw [hP]; exact meshPoint_succ_sub_le hΔ j
  have hUL : upperSum f a b Δ - lowerSum f a b Δ = P.upperSum f - P.lowerSum f := by
    rw [hP]; rfl
  rw [hUL, P.upperSum_sub_lowerSum]
  calc P.sum (fun x y => (supOn f x y - infOn f x y) * (y - x))
      ≤ P.sum (fun x y => Δ * (f y - f x)) := P.sum_le_sum fun j hj => by
        have hlt := P.lt_succ j hj
        have hx : P.pt j ∈ Icc a b := P.Icc_subset hj (left_mem_Icc.2 hlt.le)
        have hy : P.pt (j + 1) ∈ Icc a b := P.Icc_subset hj (right_mem_Icc.2 hlt.le)
        have h1 : supOn f (P.pt j) (P.pt (j + 1)) ≤ f (P.pt (j + 1)) :=
          supOn_le hlt.le fun t ht => hf (P.Icc_subset hj ht) hy ht.2
        have h2 : f (P.pt j) ≤ infOn f (P.pt j) (P.pt (j + 1)) :=
          le_infOn hlt.le fun t ht => hf hx (P.Icc_subset hj ht) ht.1
        have h3 : 0 ≤ f (P.pt (j + 1)) - f (P.pt j) := sub_nonneg.2 (hf hx hy hlt.le)
        calc (supOn f (P.pt j) (P.pt (j + 1)) - infOn f (P.pt j) (P.pt (j + 1))) *
              (P.pt (j + 1) - P.pt j)
            ≤ (f (P.pt (j + 1)) - f (P.pt j)) * (P.pt (j + 1) - P.pt j) :=
              mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.2 hlt.le)
          _ ≤ (f (P.pt (j + 1)) - f (P.pt j)) * Δ := mul_le_mul_of_nonneg_left (hw j) h3
          _ = Δ * (f (P.pt (j + 1)) - f (P.pt j)) := mul_comm _ _
    _ = Δ * (f b - f a) := by
        rw [IntervalPartition.sum, ← Finset.mul_sum, Finset.sum_range_sub (fun i => f (P.pt i)),
          P.pt_n, P.pt_zero]

/-- **Exercise 9.1.2, second part.** If $`f` is nonincreasing on $`[a, b]`, then for every
real $`\Delta x > 0`,
$$`U_a^b(f, \Delta x) - L_a^b(f, \Delta x) \le \Delta x\,\bigl(f(a) - f(b)\bigr).` -/
theorem upperSum_sub_lowerSum_le_of_antitoneOn (hab : a ≤ b) (hf : AntitoneOn f (Icc a b))
    (hΔ : 0 < Δ) : upperSum f a b Δ - lowerSum f a b Δ ≤ Δ * (f a - f b) := by
  obtain ⟨P, hP⟩ : ∃ P : IntervalPartition a b, P = meshPartition hab hΔ := ⟨_, rfl⟩
  have hw : ∀ j, P.pt (j + 1) - P.pt j ≤ Δ := fun j => by
    rw [hP]; exact meshPoint_succ_sub_le hΔ j
  have hUL : upperSum f a b Δ - lowerSum f a b Δ = P.upperSum f - P.lowerSum f := by
    rw [hP]; rfl
  rw [hUL, P.upperSum_sub_lowerSum]
  calc P.sum (fun x y => (supOn f x y - infOn f x y) * (y - x))
      ≤ P.sum (fun x y => Δ * (-f y - -f x)) := P.sum_le_sum fun j hj => by
        have hlt := P.lt_succ j hj
        have hx : P.pt j ∈ Icc a b := P.Icc_subset hj (left_mem_Icc.2 hlt.le)
        have hy : P.pt (j + 1) ∈ Icc a b := P.Icc_subset hj (right_mem_Icc.2 hlt.le)
        have h1 : supOn f (P.pt j) (P.pt (j + 1)) ≤ f (P.pt j) :=
          supOn_le hlt.le fun t ht => hf hx (P.Icc_subset hj ht) ht.1
        have h2 : f (P.pt (j + 1)) ≤ infOn f (P.pt j) (P.pt (j + 1)) :=
          le_infOn hlt.le fun t ht => hf (P.Icc_subset hj ht) hy ht.2
        have h3 : 0 ≤ f (P.pt j) - f (P.pt (j + 1)) := sub_nonneg.2 (hf hx hy hlt.le)
        calc (supOn f (P.pt j) (P.pt (j + 1)) - infOn f (P.pt j) (P.pt (j + 1))) *
              (P.pt (j + 1) - P.pt j)
            ≤ (f (P.pt j) - f (P.pt (j + 1))) * (P.pt (j + 1) - P.pt j) :=
              mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.2 hlt.le)
          _ ≤ (f (P.pt j) - f (P.pt (j + 1))) * Δ := mul_le_mul_of_nonneg_left (hw j) h3
          _ = Δ * (-f (P.pt (j + 1)) - -f (P.pt j)) := by ring
    _ = Δ * (f a - f b) := by
        rw [IntervalPartition.sum, ← Finset.mul_sum, Finset.sum_range_sub (fun i => -f (P.pt i)),
          P.pt_n, P.pt_zero]
        ring

end Mesh

/-!
### Riemann sums of hyperreal width

For fixed $`f`, $`a` and $`b`, the three sums $`U_a^b(f, \Delta x)`, $`L_a^b(f, \Delta x)`
and $`S_a^b(f, \Delta x)` are real functions of the real variable $`\Delta x`. Like every
real function they extend to the hyperreals, and in particular acquire values at positive
infinitesimal widths. No hyperfinite summation is needed for this: the extended ordinary sum
at $`\Delta x = [r_n]` is simply the class of the sequence of real sums
$`S_a^b(f, r_n)`. (Section 12.7 of the book returns to the informal picture of a sum of
unlimited length.) The inequalities of the standard theory hold for all positive real
widths, so by transfer they hold for all positive hyperreal widths.
-/

section HyperSums

variable {f : ℝ → ℝ} {a b : ℝ} {Δ Δ' : ℝ*}

/-- **Section 9.1.** The extension of the upper Riemann sum $`U_a^b(f, \Delta x)` to
hyperreal widths $`\Delta x`. -/
def hyperUpperSum (f : ℝ → ℝ) (a b : ℝ) : ℝ* → ℝ* := ⋆(upperSum f a b)

/-- **Section 9.1.** The extension of the lower Riemann sum $`L_a^b(f, \Delta x)` to
hyperreal widths $`\Delta x`. -/
def hyperLowerSum (f : ℝ → ℝ) (a b : ℝ) : ℝ* → ℝ* := ⋆(lowerSum f a b)

/-- **Section 9.1.** The extension of the ordinary Riemann sum $`S_a^b(f, \Delta x)` to
hyperreal widths $`\Delta x`. -/
def hyperOrdSum (f : ℝ → ℝ) (a b : ℝ) : ℝ* → ℝ* := ⋆(ordSum f a b)

/-- At the class of a sequence of widths, the extended upper sum is the class of the
sequence of upper sums. -/
theorem hyperUpperSum_ofSeq (f : ℝ → ℝ) (a b : ℝ) (r : ℕ → ℝ) :
    hyperUpperSum f a b (Hyperreal.ofSeq r) = Hyperreal.ofSeq fun n => upperSum f a b (r n) :=
  rfl

/-- At the class of a sequence of widths, the extended lower sum is the class of the
sequence of lower sums. -/
theorem hyperLowerSum_ofSeq (f : ℝ → ℝ) (a b : ℝ) (r : ℕ → ℝ) :
    hyperLowerSum f a b (Hyperreal.ofSeq r) = Hyperreal.ofSeq fun n => lowerSum f a b (r n) :=
  rfl

/-- At the class of a sequence of widths, the extended ordinary sum is the class of the
sequence of ordinary sums. -/
theorem hyperOrdSum_ofSeq (f : ℝ → ℝ) (a b : ℝ) (r : ℕ → ℝ) :
    hyperOrdSum f a b (Hyperreal.ofSeq r) = Hyperreal.ofSeq fun n => ordSum f a b (r n) :=
  rfl

/-- At a real width the extended upper sum is the real upper sum. -/
theorem hyperUpperSum_coe (f : ℝ → ℝ) (a b t : ℝ) :
    hyperUpperSum f a b (t : ℝ*) = (upperSum f a b t : ℝ) := rfl

/-- At a real width the extended lower sum is the real lower sum. -/
theorem hyperLowerSum_coe (f : ℝ → ℝ) (a b t : ℝ) :
    hyperLowerSum f a b (t : ℝ*) = (lowerSum f a b t : ℝ) := rfl

/-- At a real width the extended ordinary sum is the real ordinary sum. -/
theorem hyperOrdSum_coe (f : ℝ → ℝ) (a b t : ℝ) :
    hyperOrdSum f a b (t : ℝ*) = (ordSum f a b t : ℝ) := rfl

/-- **Chapter 9, transfer tool.** The class of a sequence is positive if and only if almost
all of its terms are positive. -/
theorem zero_lt_ofSeq_iff {r : ℕ → ℝ} :
    0 < Hyperreal.ofSeq r ↔ ∀ᶠ n in hyperfilter ℕ, 0 < r n := by
  rw [← Hyperreal.coe_zero, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]

/-- **Chapter 9, transfer tool.** The enlargement of the set of positive reals is the set of
positive hyperreals. -/
theorem mem_starSet_Ioi_zero : Δ ∈ ⋆(Ioi (0 : ℝ)) ↔ 0 < Δ := by
  rw [starSet_Ioi_real, mem_Ioi, Hyperreal.coe_zero]

/-- **Chapter 9, transfer tool (universal transfer over the positive reals).** If
$`F(t) \le G(t)` for all real $`t > 0`, then the extensions satisfy the same inequality at
every positive hyperreal. -/
theorem starMap_le_starMap_of_pos {F G : ℝ → ℝ} (h : ∀ t : ℝ, 0 < t → F t ≤ G t) (hΔ : 0 < Δ) :
    ⋆F Δ ≤ ⋆G Δ :=
  starMap_le_starMap_of_mem (A := Ioi 0) h (mem_starSet_Ioi_zero.2 hΔ)

/-- **Chapter 9, transfer tool (existential transfer over the positive reals).** If the
extensions satisfy $`{}^*F(\Delta) < {}^*G(\Delta)` at some positive hyperreal, then
$`F(t) < G(t)` for some positive real $`t`. -/
theorem exists_pos_lt_of_starMap_lt {F G : ℝ → ℝ} (hΔ : 0 < Δ) (h : ⋆F Δ < ⋆G Δ) :
    ∃ t : ℝ, 0 < t ∧ F t < G t := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep Δ
  rw [starMap_hyperreal_ofSeq, starMap_hyperreal_ofSeq, ofSeq_lt_ofSeq_iff] at h
  obtain ⟨n, h1, h2⟩ := ((zero_lt_ofSeq_iff.1 hΔ).and h).exists
  exact ⟨r n, h1, h2⟩

/-- **Section 9.1, by transfer.** $`L_a^b(f, \Delta x) \le S_a^b(f, \Delta x)` for every
positive hyperreal $`\Delta x`. -/
theorem hyperLowerSum_le_hyperOrdSum (hf : BoundedOn f (Icc a b)) (hab : a ≤ b) (hΔ : 0 < Δ) :
    hyperLowerSum f a b Δ ≤ hyperOrdSum f a b Δ :=
  starMap_le_starMap_of_pos (fun _ ht => lowerSum_le_ordSum hf hab ht) hΔ

/-- **Section 9.1, by transfer.** $`S_a^b(f, \Delta x) \le U_a^b(f, \Delta x)` for every
positive hyperreal $`\Delta x`. -/
theorem hyperOrdSum_le_hyperUpperSum (hf : BoundedOn f (Icc a b)) (hab : a ≤ b) (hΔ : 0 < Δ) :
    hyperOrdSum f a b Δ ≤ hyperUpperSum f a b Δ :=
  starMap_le_starMap_of_pos (fun _ ht => ordSum_le_upperSum hf hab ht) hΔ

/-- **Section 9.1, by transfer.** $`U_a^b(f, \Delta x) \le M(b - a)` for every positive
hyperreal $`\Delta x`. -/
theorem hyperUpperSum_le (hf : BoundedOn f (Icc a b)) (hab : a ≤ b) (hΔ : 0 < Δ) :
    hyperUpperSum f a b Δ ≤ ((supOn f a b * (b - a) : ℝ) : ℝ*) := by
  have h := starMap_le_starMap_of_pos (G := fun _ => supOn f a b * (b - a))
    (fun _ ht => upperSum_le_supOn_mul hf hab ht) hΔ
  rwa [starMap_const_apply] at h

/-- **Section 9.1, by transfer.** $`m(b - a) \le L_a^b(f, \Delta x)` for every positive
hyperreal $`\Delta x`. -/
theorem le_hyperLowerSum (hf : BoundedOn f (Icc a b)) (hab : a ≤ b) (hΔ : 0 < Δ) :
    ((infOn f a b * (b - a) : ℝ) : ℝ*) ≤ hyperLowerSum f a b Δ := by
  have h := starMap_le_starMap_of_pos (F := fun _ => infOn f a b * (b - a))
    (fun _ ht => infOn_mul_le_lowerSum hf hab ht) hΔ
  rwa [starMap_const_apply] at h

/-- **Section 9.1, by transfer.** For every positive hyperreal $`\Delta x`, including every
positive infinitesimal,
$$`m(b - a) \le L_a^b(f, \Delta x) \le S_a^b(f, \Delta x) \le U_a^b(f, \Delta x) \le M(b - a).` -/
theorem hyperLowerSum_hyperOrdSum_hyperUpperSum_chain (hf : BoundedOn f (Icc a b)) (hab : a ≤ b)
    (hΔ : 0 < Δ) :
    ((infOn f a b * (b - a) : ℝ) : ℝ*) ≤ hyperLowerSum f a b Δ ∧
      hyperLowerSum f a b Δ ≤ hyperOrdSum f a b Δ ∧
      hyperOrdSum f a b Δ ≤ hyperUpperSum f a b Δ ∧
      hyperUpperSum f a b Δ ≤ ((supOn f a b * (b - a) : ℝ) : ℝ*) :=
  ⟨le_hyperLowerSum hf hab hΔ, hyperLowerSum_le_hyperOrdSum hf hab hΔ,
    hyperOrdSum_le_hyperUpperSum hf hab hΔ, hyperUpperSum_le hf hab hΔ⟩

/-- **Section 9.1, by transfer.** $`L_a^b(f, \Delta x) \le U_a^b(f, \Delta y)` for all
positive hyperreals $`\Delta x` and $`\Delta y`. -/
theorem hyperLowerSum_le_hyperUpperSum (hf : BoundedOn f (Icc a b)) (hab : a ≤ b) (hΔ : 0 < Δ)
    (hΔ' : 0 < Δ') : hyperLowerSum f a b Δ ≤ hyperUpperSum f a b Δ' := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep Δ
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep Δ'
  rw [hyperLowerSum_ofSeq, hyperUpperSum_ofSeq, ofSeq_le_ofSeq_iff]
  filter_upwards [zero_lt_ofSeq_iff.1 hΔ, zero_lt_ofSeq_iff.1 hΔ'] with n h1 h2
  exact lowerSum_le_upperSum hf hab h1 h2

/-- **Section 9.1, by transfer.** A standard lower sum is at most the upper sum of any
positive hyperreal width. -/
theorem IntervalPartition.lowerSum_le_hyperUpperSum (P : IntervalPartition a b)
    (hf : BoundedOn f (Icc a b)) (hΔ : 0 < Δ) :
    ((P.lowerSum f : ℝ) : ℝ*) ≤ hyperUpperSum f a b Δ := by
  have h := starMap_le_starMap_of_pos (F := fun _ => P.lowerSum f) (G := Goldblatt.upperSum f a b)
    (fun _ ht => P.lowerSum_le_upperSum (meshPartition P.le ht) hf) hΔ
  rwa [starMap_const_apply] at h

/-- **Section 9.1, by transfer.** The lower sum of any positive hyperreal width is at most a
standard upper sum. -/
theorem IntervalPartition.hyperLowerSum_le_upperSum (P : IntervalPartition a b)
    (hf : BoundedOn f (Icc a b)) (hΔ : 0 < Δ) :
    hyperLowerSum f a b Δ ≤ ((P.upperSum f : ℝ) : ℝ*) := by
  have h := starMap_le_starMap_of_pos (F := Goldblatt.lowerSum f a b) (G := fun _ => P.upperSum f)
    (fun _ ht => (meshPartition P.le ht).lowerSum_le_upperSum P hf) hΔ
  rwa [starMap_const_apply] at h

/-- **Section 9.2.** The upper sum of a positive hyperreal width is limited, being bounded
by the real numbers $`m(b - a)` and $`M(b - a)`. -/
theorem limited_hyperUpperSum (hf : BoundedOn f (Icc a b)) (hab : a ≤ b) (hΔ : 0 < Δ) :
    Limited (hyperUpperSum f a b Δ) :=
  limited_of_mem_Icc ⟨(le_hyperLowerSum hf hab hΔ).trans
    ((hyperLowerSum_le_hyperOrdSum hf hab hΔ).trans (hyperOrdSum_le_hyperUpperSum hf hab hΔ)),
    hyperUpperSum_le hf hab hΔ⟩

/-- **Section 9.2.** The lower sum of a positive hyperreal width is limited. -/
theorem limited_hyperLowerSum (hf : BoundedOn f (Icc a b)) (hab : a ≤ b) (hΔ : 0 < Δ) :
    Limited (hyperLowerSum f a b Δ) :=
  limited_of_mem_Icc ⟨le_hyperLowerSum hf hab hΔ,
    (hyperLowerSum_le_hyperOrdSum hf hab hΔ).trans
      ((hyperOrdSum_le_hyperUpperSum hf hab hΔ).trans (hyperUpperSum_le hf hab hΔ))⟩

/-- **Section 9.2.** The ordinary Riemann sum of a positive hyperreal width is limited. -/
theorem limited_hyperOrdSum (hf : BoundedOn f (Icc a b)) (hab : a ≤ b) (hΔ : 0 < Δ) :
    Limited (hyperOrdSum f a b Δ) :=
  limited_of_mem_Icc ⟨(le_hyperLowerSum hf hab hΔ).trans (hyperLowerSum_le_hyperOrdSum hf hab hΔ),
    (hyperOrdSum_le_hyperUpperSum hf hab hΔ).trans (hyperUpperSum_le hf hab hΔ)⟩

/-- A real multiple of a positive infinitesimal is less than every positive real. -/
theorem coe_mul_posInfinitesimal_lt (c : ℝ) (hΔ : PosInfinitesimal Δ) {δ : ℝ} (hδ : 0 < δ) :
    (c : ℝ*) * Δ < δ := by
  have : Infinitesimal ((c : ℝ*) * Δ) := (limited_coe c).mul_infinitesimal (Or.inl hΔ)
  exact (le_abs_self _).trans_lt (infinitesimal_iff_abs_lt.1 this δ hδ)

/-- **Section 9.1.** The number $`n` of subintervals of the partition of $`[a, b]` of width
$`\Delta x`, extended to hyperreal widths: the least hyperinteger $`n` with
$`a + n\,\Delta x \ge b`. -/
def hyperMeshCard (a b : ℝ) : ℝ* → ℝ* := ⋆(fun t : ℝ => (meshCard a b t : ℝ))

/-- The number of subintervals of a partition of hyperreal width is a hypernatural. -/
theorem hyperMeshCard_mem_hyperNat (a b : ℝ) (Δ : ℝ*) : hyperMeshCard a b Δ ∈ ℕ* := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep Δ
  exact mem_hyperNat_iff.2 ⟨fun n => meshCard a b (r n), rfl⟩

/-- **Section 9.1.** When $`\Delta x` is a positive infinitesimal and $`a < b`, the number
$`n` of subintervals of the partition of width $`\Delta x` is unlimited: by transfer
$`n \ge (b - a)/\Delta x`, and the quotient of a positive real by a positive infinitesimal
exceeds every real. -/
theorem hyperMeshCard_mem_unlimitedHyperNat (hab : a < b) (hΔ : PosInfinitesimal Δ) :
    hyperMeshCard a b Δ ∈ unlimitedHyperNat := by
  refine mem_unlimitedHyperNat.2 ⟨hyperMeshCard_mem_hyperNat a b Δ, Or.inl fun r => ?_⟩
  have hle : ((b - a : ℝ) : ℝ*) / Δ ≤ hyperMeshCard a b Δ := by
    obtain ⟨s, rfl⟩ := hyperreal_exists_rep Δ
    change Hyperreal.ofSeq (fun n => (b - a) / s n) ≤
      Hyperreal.ofSeq (fun n => (meshCard a b (s n) : ℝ))
    exact ofSeq_le_ofSeq_iff.2 (Eventually.of_forall fun n => Nat.le_ceil _)
  refine lt_of_lt_of_le ?_ hle
  rw [lt_div_iff₀ hΔ.1]
  exact coe_mul_posInfinitesimal_lt r hΔ (sub_pos.2 hab)

/-- **Chapter 9, tool.** If $`L \le U` and $`U - L` is at most an infinitesimal, then
$`L \simeq U`. -/
theorem infClose_of_le_of_sub_le {L U e : ℝ*} (h : L ≤ U) (hle : U - L ≤ e)
    (he : Infinitesimal e) : L ≊ U := by
  have h0 : 0 ≤ U - L := sub_nonneg.2 h
  have : Infinitesimal (U - L) :=
    he.of_abs_le (by rw [abs_of_nonneg h0]; exact hle.trans (le_abs_self _))
  exact InfClose.symm this

/-- **Chapter 9, tool.** A hyperreal between two hyperreals that are infinitely close to
each other is infinitely close to both. -/
theorem infClose_between {L S U : ℝ*} (h1 : L ≤ S) (h2 : S ≤ U) (h : L ≊ U) :
    L ≊ S ∧ S ≊ U := by
  have hUL : Infinitesimal (U - L) := h.symm
  have hLS : L ≊ S := infClose_of_le_of_sub_le h1 (by linarith) hUL
  exact ⟨hLS, hLS.symm.trans h⟩

/-- **Theorem 9.1.1.** If $`f` is continuous on the real interval $`[a, b]`, then for every
positive infinitesimal $`\Delta x`,
$$`L_a^b(f, \Delta x) \simeq U_a^b(f, \Delta x).`
The proof is the book's. For real $`\Delta x > 0` there are points $`c, d \in [a, b]`, no
further apart than $`\Delta x`, with
$`U - L \le (f(c) - f(d))(b - a)` ({name}`exists_points_upperSum_sub_lowerSum_le`). By
transfer the same holds for the infinitesimal $`\Delta x`, with points
$`c \simeq d` of the enlargement of $`[a, b]`. By the uniform continuity of $`f` on
$`[a, b]` (Theorem 7.7.2) the values of the extension at $`c` and $`d` are infinitely close,
so $`U - L` is at most an infinitesimal multiple of the real number $`b - a`. -/
theorem hyperLowerSum_infClose_hyperUpperSum_of_continuousOn (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hΔ : PosInfinitesimal Δ) :
    hyperLowerSum f a b Δ ≊ hyperUpperSum f a b Δ := by
  have hfb := boundedOn_Icc_of_continuousOn hf
  have hLU : hyperLowerSum f a b Δ ≤ hyperUpperSum f a b Δ :=
    hyperLowerSum_le_hyperUpperSum hfb hab hΔ.1 hΔ.1
  have hΔi : Infinitesimal Δ := Or.inl hΔ
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep Δ
  have hr := zero_lt_ofSeq_iff.1 hΔ.1
  -- the points c(Δx), d(Δx) of the book, chosen for each index
  have hex : ∀ n, ∃ c d : ℝ, 0 < r n → c ∈ Icc a b ∧ d ∈ Icc a b ∧ |c - d| ≤ r n ∧
      upperSum f a b (r n) - lowerSum f a b (r n) ≤ (f c - f d) * (b - a) := by
    intro n
    by_cases h : 0 < r n
    · obtain ⟨c, hc, d, hd, h1, h2⟩ := exists_points_upperSum_sub_lowerSum_le hab hf h
      exact ⟨c, d, fun _ => ⟨hc, hd, h1, h2⟩⟩
    · exact ⟨a, a, fun h' => absurd h' h⟩
  choose c d hcd using hex
  have hC : Hyperreal.ofSeq c ∈ ⋆(Icc a b) :=
    hyperreal_ofSeq_mem_starSet.2 (hr.mono fun n hn => (hcd n hn).1)
  have hD : Hyperreal.ofSeq d ∈ ⋆(Icc a b) :=
    hyperreal_ofSeq_mem_starSet.2 (hr.mono fun n hn => (hcd n hn).2.1)
  -- (i): c ≃ d
  have hCD : Hyperreal.ofSeq c ≊ Hyperreal.ofSeq d := by
    refine hΔi.of_abs_le ?_
    rw [abs_of_pos hΔ.1, ofSeq_sub, abs_ofSeq, ofSeq_le_ofSeq_iff]
    exact hr.mono fun n hn => (hcd n hn).2.2.1
  have hfcd : ⋆f (Hyperreal.ofSeq c) ≊ ⋆f (Hyperreal.ofSeq d) :=
    uniformContinuousOn_iff_infClose.1 (uniformContinuousOn_Icc_of_continuousOn hf) _ hC _ hD hCD
  -- (ii): U - L ≤ (f(c) - f(d))(b - a)
  have hle : hyperUpperSum f a b (Hyperreal.ofSeq r) - hyperLowerSum f a b (Hyperreal.ofSeq r) ≤
      (⋆f (Hyperreal.ofSeq c) - ⋆f (Hyperreal.ofSeq d)) * ((b - a : ℝ) : ℝ*) := by
    change Hyperreal.ofSeq (fun n => upperSum f a b (r n) - lowerSum f a b (r n)) ≤
      Hyperreal.ofSeq (fun n => (f (c n) - f (d n)) * (b - a))
    exact ofSeq_le_ofSeq_iff.2 (hr.mono fun n hn => (hcd n hn).2.2.2)
  exact infClose_of_le_of_sub_le hLU hle (Infinitesimal.mul_limited hfcd (limited_coe _))

/-- **Exercise 9.1.2, by transfer.** If $`f` is nondecreasing on $`[a, b]`, then
$`U_a^b(f, \Delta x) - L_a^b(f, \Delta x) \le \Delta x\,(f(b) - f(a))` for every positive
hyperreal $`\Delta x`. -/
theorem hyperUpperSum_sub_hyperLowerSum_le_of_monotoneOn (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b)) (hΔ : 0 < Δ) :
    hyperUpperSum f a b Δ - hyperLowerSum f a b Δ ≤ Δ * ((f b - f a : ℝ) : ℝ*) := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep Δ
  change Hyperreal.ofSeq (fun n => upperSum f a b (r n) - lowerSum f a b (r n)) ≤
    Hyperreal.ofSeq (fun n => r n * (f b - f a))
  exact ofSeq_le_ofSeq_iff.2 ((zero_lt_ofSeq_iff.1 hΔ).mono fun n hn =>
    upperSum_sub_lowerSum_le_of_monotoneOn hab hf hn)

/-- **Exercise 9.1.2, by transfer.** If $`f` is nonincreasing on $`[a, b]`, then
$`U_a^b(f, \Delta x) - L_a^b(f, \Delta x) \le \Delta x\,(f(a) - f(b))` for every positive
hyperreal $`\Delta x`. -/
theorem hyperUpperSum_sub_hyperLowerSum_le_of_antitoneOn (hab : a ≤ b)
    (hf : AntitoneOn f (Icc a b)) (hΔ : 0 < Δ) :
    hyperUpperSum f a b Δ - hyperLowerSum f a b Δ ≤ Δ * ((f a - f b : ℝ) : ℝ*) := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep Δ
  change Hyperreal.ofSeq (fun n => upperSum f a b (r n) - lowerSum f a b (r n)) ≤
    Hyperreal.ofSeq (fun n => r n * (f a - f b))
  exact ofSeq_le_ofSeq_iff.2 ((zero_lt_ofSeq_iff.1 hΔ).mono fun n hn =>
    upperSum_sub_lowerSum_le_of_antitoneOn hab hf hn)

/-- **Exercise 9.1.2, third part.** Theorem 9.1.1 holds for functions that are nondecreasing
on $`[a, b]`: for a positive infinitesimal $`\Delta x` the difference of the upper and the
lower sum is at most the infinitesimal $`\Delta x\,(f(b) - f(a))`. -/
theorem hyperLowerSum_infClose_hyperUpperSum_of_monotoneOn (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b)) (hΔ : PosInfinitesimal Δ) :
    hyperLowerSum f a b Δ ≊ hyperUpperSum f a b Δ :=
  infClose_of_le_of_sub_le
    (hyperLowerSum_le_hyperUpperSum (boundedOn_Icc_of_monotoneOn hf) hab hΔ.1 hΔ.1)
    (hyperUpperSum_sub_hyperLowerSum_le_of_monotoneOn hab hf hΔ.1)
    (Infinitesimal.mul_limited (Or.inl hΔ) (limited_coe _))

/-- **Exercise 9.1.2, third part.** Theorem 9.1.1 holds for functions that are nonincreasing
on $`[a, b]`. -/
theorem hyperLowerSum_infClose_hyperUpperSum_of_antitoneOn (hab : a ≤ b)
    (hf : AntitoneOn f (Icc a b)) (hΔ : PosInfinitesimal Δ) :
    hyperLowerSum f a b Δ ≊ hyperUpperSum f a b Δ :=
  infClose_of_le_of_sub_le
    (hyperLowerSum_le_hyperUpperSum (boundedOn_Icc_of_antitoneOn hf) hab hΔ.1 hΔ.1)
    (hyperUpperSum_sub_hyperLowerSum_le_of_antitoneOn hab hf hΔ.1)
    (Infinitesimal.mul_limited (Or.inl hΔ) (limited_coe _))

/-- **Exercise 9.1.2.** A function is _monotonic_ on $`[a, b]` if it is nondecreasing or
nonincreasing there. Theorem 9.1.1 holds for monotonic functions: for every positive
infinitesimal $`\Delta x`, $`L_a^b(f, \Delta x) \simeq U_a^b(f, \Delta x)`. -/
theorem hyperLowerSum_infClose_hyperUpperSum_of_monotonic (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b)) (hΔ : PosInfinitesimal Δ) :
    hyperLowerSum f a b Δ ≊ hyperUpperSum f a b Δ :=
  hf.elim (fun h => hyperLowerSum_infClose_hyperUpperSum_of_monotoneOn hab h hΔ)
    (fun h => hyperLowerSum_infClose_hyperUpperSum_of_antitoneOn hab h hΔ)

end HyperSums

end Goldblatt
