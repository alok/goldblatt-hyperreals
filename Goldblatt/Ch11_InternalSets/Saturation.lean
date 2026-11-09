import Goldblatt.Ch11_InternalSets.Definability

/-!
# 11 (part 3). Saturation and Topology: Sections 11.10 to 11.14

This is the third of three parts of Chapter 11 (the overview is on the chapter page
{lit}`Goldblatt.Ch11_InternalSets`). It proves countable saturation for the ultrapower, draws
its consequences for countable unions and intersections of internal sets and for the size of
internal sets, proves that the shadow of an internal set is closed, and compares the
hyper-open sets with the topologies on the hyperreals introduced in Chapter 10.
-/

universe u

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Pointwise

/-!
## 11.10 Saturation of Internal Sets

A decreasing sequence of nonempty internal sets has a common point. This property,
_countable saturation_, is a fact about the ultrapower and not a consequence of transfer. Its
proof is a diagonal construction on the defining sequences: at index $`n` one looks at the
first $`n` sets of the sequence, finds the largest $`k \le n` for which the $`n`-th terms of
the first $`k` defining sequences form a decreasing chain of nonempty sets, and picks a point
in the last set of that chain. The class of the sequence of points picked lies in every set.

Saturation limits the ways in which countably many internal sets can combine to an internal
set: a countable union or intersection of internal sets is internal only if it is already a
finite union or intersection.
-/

section Saturation

variable {α αS : Type u} [StarType α αS]

/-- A sequence of sets whose first $`m` steps are decreasing is decreasing up to $`m`. -/
theorem subset_of_forall_succ_subset {A : ℕ → Set α} {m : ℕ} (h : ∀ i < m, A (i + 1) ⊆ A i)
    {k : ℕ} (hk : k ≤ m) : A m ⊆ A k := by
  induction m, hk using Nat.le_induction with
  | base => exact Subset.rfl
  | succ m _ ih =>
    exact (h m (Nat.lt_succ_self m)).trans (ih fun i hi => h i (Nat.lt_succ_of_lt hi))

/-- **Theorem 11.10.1** (countable saturation), in terms of defining sequences. If the
internal sets $`X^k = [A^k_n]` are nonempty and decreasing in $`k`, then their intersection
is nonempty. This is the diagonal argument of the book: with $`J^k` the large set of indices
$`n` at which $`A^0_n \supseteq \dots \supseteq A^k_n \ne \emptyset`, one chooses
$`s_n \in A^{k_n}_n` where $`k_n` is the largest $`k \le n` with $`n \in J^k`, and then
$`s_n \in A^k_n` whenever $`k \le n` and $`n \in J^k`. -/
theorem iInter_internalSet_nonempty (A : ℕ → ℕ → Set α)
    (hne : ∀ k, (internalSet (A k) : Set αS).Nonempty)
    (hdec : ∀ k, (internalSet (A (k + 1)) : Set αS) ⊆ internalSet (A k)) :
    (⋂ k, (internalSet (A k) : Set αS)).Nonempty := by
  classical
  let J : ℕ → Set ℕ := fun k => {n | (∀ i < k, A (i + 1) n ⊆ A i n) ∧ (A k n).Nonempty}
  have hJ : ∀ k, ∀ᶠ n in hyperfilter ℕ, n ∈ J k := fun k => by
    have h1 : ∀ᶠ n in hyperfilter ℕ, ∀ i ∈ Iio k, A (i + 1) n ⊆ A i n :=
      (eventually_all_finite (finite_Iio k)).2 fun i _ => internalSet_subset_iff.1 (hdec i)
    exact (h1.and (internalSet_nonempty_iff.1 (hne k))).mono fun n hn =>
      ⟨fun i hi => hn.1 i hi, hn.2⟩
  obtain ⟨a₀⟩ : Nonempty α := by
    obtain ⟨x, hx⟩ := hne 0
    obtain ⟨r, -, -⟩ := mem_internalSet_iff.1 hx
    exact ⟨r 0⟩
  let κ : ℕ → ℕ := fun n => Nat.findGreatest (fun k => n ∈ J k) n
  let s : ℕ → α := fun n => if h : (A (κ n) n).Nonempty then h.some else a₀
  refine ⟨ofSeq s, mem_iInter.2 fun k => ofSeq_mem_internalSet.2 ?_⟩
  have hk : ∀ᶠ n in hyperfilter ℕ, k ≤ n := setOf_le_mem_hyperfilter k
  refine (hk.and (hJ k)).mono fun n hn => ?_
  have hkκ : k ≤ κ n := Nat.le_findGreatest hn.1 hn.2
  have hκJ : n ∈ J (κ n) := Nat.findGreatest_spec (P := fun k => n ∈ J k) hn.1 hn.2
  have hs : s n ∈ A (κ n) n := by
    simp only [s, hκJ.2, ↓reduceDIte]
    exact hκJ.2.some_mem
  exact subset_of_forall_succ_subset (A := fun i => A i n) hκJ.1 hkκ hs

/-- **Theorem 11.10.1** (countable saturation). The intersection of a decreasing sequence
$`X^0 \supseteq X^1 \supseteq \cdots` of nonempty internal sets is nonempty. -/
theorem iInter_nonempty_of_isInternalSet {X : ℕ → Set αS} (hX : ∀ k, IsInternalSet α (X k))
    (hne : ∀ k, (X k).Nonempty) (hdec : ∀ k, X (k + 1) ⊆ X k) : (⋂ k, X k).Nonempty := by
  choose A hA using hX
  obtain rfl : X = fun k => internalSet (A k) := funext hA
  exact iInter_internalSet_nonempty A hne hdec

/-- **Theorem 11.10.1** (countable saturation), for the hyperreals: a decreasing sequence of
nonempty internal sets of hyperreals has nonempty intersection. -/
theorem iInter_nonempty_of_isInternal {X : ℕ → Set ℝ*} (hX : ∀ k, IsInternal (X k))
    (hne : ∀ k, (X k).Nonempty) (hdec : ∀ k, X (k + 1) ⊆ X k) : (⋂ k, X k).Nonempty :=
  iInter_nonempty_of_isInternalSet hX hne hdec

/-- A union of internal sets over an initial segment of the natural numbers is internal. -/
theorem isInternalSet_biUnion_le {X : ℕ → Set αS} (hX : ∀ n, IsInternalSet α (X n)) (k : ℕ) :
    IsInternalSet α (⋃ n ≤ k, X n) := by
  have e : (⋃ n ≤ k, X n) = ⋃ n ∈ Finset.range (k + 1), X n := by
    ext x
    simp only [mem_iUnion, Finset.mem_range, Nat.lt_succ_iff, exists_prop]
  rw [e]
  exact isInternalSet_biUnion_finset _ fun n _ => hX n

/-- An intersection of internal sets over an initial segment of the natural numbers is
internal. -/
theorem isInternalSet_biInter_le {X : ℕ → Set αS} (hX : ∀ n, IsInternalSet α (X n)) (k : ℕ) :
    IsInternalSet α (⋂ n ≤ k, X n) := by
  have e : (⋂ n ≤ k, X n) = ⋂ n ∈ Finset.range (k + 1), X n := by
    ext x
    simp only [mem_iInter, Finset.mem_range, Nat.lt_succ_iff]
  rw [e]
  exact isInternalSet_biInter_finset _ fun n _ => hX n

/-- **Corollary 11.10.2(1).** A countable family of internal sets with the finite
intersection property has nonempty intersection. -/
theorem iInter_nonempty_of_fip {X : ℕ → Set αS} (hX : ∀ n, IsInternalSet α (X n))
    (hfip : ∀ s : Finset ℕ, (⋂ n ∈ s, X n).Nonempty) : (⋂ n, X n).Nonempty := by
  have hY : ∀ k, IsInternalSet α (⋂ n ≤ k, X n) := isInternalSet_biInter_le hX
  have hne : ∀ k, (⋂ n ≤ k, X n).Nonempty := fun k => by
    obtain ⟨x, hx⟩ := hfip (Finset.range (k + 1))
    refine ⟨x, mem_iInter₂.2 fun n hn => ?_⟩
    exact mem_iInter₂.1 hx n (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
  obtain ⟨x, hx⟩ := iInter_nonempty_of_isInternalSet hY hne fun k y hy =>
    mem_iInter₂.2 fun n hn => mem_iInter₂.1 hy n (Nat.le_succ_of_le hn)
  exact ⟨x, mem_iInter.2 fun n => mem_iInter₂.1 (mem_iInter.1 hx n) n le_rfl⟩

/-- **Corollary 11.10.2(2).** If an internal set is covered by countably many internal sets,
it is covered by finitely many of them. -/
theorem IsInternalSet.exists_subset_biUnion_le {X : Set αS} (hX : IsInternalSet α X)
    {Y : ℕ → Set αS} (hY : ∀ n, IsInternalSet α (Y n)) (h : X ⊆ ⋃ n, Y n) :
    ∃ k, X ⊆ ⋃ n ≤ k, Y n := by
  by_contra hno
  push Not at hno
  obtain ⟨x, hx⟩ := iInter_nonempty_of_isInternalSet
    (X := fun k => X \ ⋃ n ≤ k, Y n) (fun k => hX.diff (isInternalSet_biUnion_le hY k))
    (fun k => by
      obtain ⟨x, hx, hx'⟩ := not_subset.1 (hno k)
      exact ⟨x, hx, hx'⟩)
    (fun k x hx => ⟨hx.1, fun hx' => hx.2 (by
      obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.1 hx'
      exact mem_iUnion₂.2 ⟨n, Nat.le_succ_of_le hn, hxn⟩)⟩)
  obtain ⟨n, hn⟩ := mem_iUnion.1 (h (mem_iInter.1 hx 0).1)
  exact (mem_iInter.1 hx n).2 (mem_iUnion₂.2 ⟨n, le_rfl, hn⟩)

/-- **Corollary 11.10.2(3).** If the intersection of countably many internal sets is included
in an internal set, so is the intersection of finitely many of them. -/
theorem IsInternalSet.exists_biInter_le_subset {X : Set αS} (hX : IsInternalSet α X)
    {Y : ℕ → Set αS} (hY : ∀ n, IsInternalSet α (Y n)) (h : ⋂ n, Y n ⊆ X) :
    ∃ k, ⋂ n ≤ k, Y n ⊆ X := by
  by_contra hno
  push Not at hno
  obtain ⟨x, hx⟩ := iInter_nonempty_of_isInternalSet
    (X := fun k => (⋂ n ≤ k, Y n) \ X) (fun k => (isInternalSet_biInter_le hY k).diff hX)
    (fun k => by
      obtain ⟨x, hx, hx'⟩ := not_subset.1 (hno k)
      exact ⟨x, hx, hx'⟩)
    (fun k x hx => ⟨mem_iInter₂.2 fun n hn => mem_iInter₂.1 hx.1 n (Nat.le_succ_of_le hn),
      hx.2⟩)
  refine (mem_iInter.1 hx 0).2 (h (mem_iInter.2 fun n => ?_))
  exact mem_iInter₂.1 (mem_iInter.1 hx n).1 n le_rfl

/-- **Corollary 11.10.2(4).** If the union of countably many internal sets is internal, it is
the union of finitely many of them. -/
theorem exists_iUnion_eq_biUnion_le {Y : ℕ → Set αS} (hY : ∀ n, IsInternalSet α (Y n))
    (h : IsInternalSet α (⋃ n, Y n)) : ∃ k, ⋃ n, Y n = ⋃ n ≤ k, Y n := by
  obtain ⟨k, hk⟩ := h.exists_subset_biUnion_le hY Subset.rfl
  exact ⟨k, Subset.antisymm hk (iUnion₂_subset fun n _ => subset_iUnion Y n)⟩

/-- **Corollary 11.10.2(5).** If the intersection of countably many internal sets is
internal, it is the intersection of finitely many of them. -/
theorem exists_iInter_eq_biInter_le {Y : ℕ → Set αS} (hY : ∀ n, IsInternalSet α (Y n))
    (h : IsInternalSet α (⋂ n, Y n)) : ∃ k, ⋂ n, Y n = ⋂ n ≤ k, Y n := by
  obtain ⟨k, hk⟩ := h.exists_biInter_le_subset hY Subset.rfl
  exact ⟨k, Subset.antisymm (subset_iInter₂ fun n _ => iInter_subset Y n) hk⟩

/-- **Exercise 11.10.3.** The union of a strictly increasing sequence of internal sets is not
internal. -/
theorem not_isInternalSet_iUnion_of_ssubset_succ {Y : ℕ → Set αS}
    (hY : ∀ n, IsInternalSet α (Y n)) (hinc : ∀ n, Y n ⊂ Y (n + 1)) :
    ¬ IsInternalSet α (⋃ n, Y n) := by
  intro h
  obtain ⟨k, hk⟩ := exists_iUnion_eq_biUnion_le hY h
  have hmono : Monotone Y := monotone_nat_of_le_succ fun n => (hinc n).subset
  have h1 : Y (k + 1) ⊆ Y k := by
    refine (subset_iUnion Y (k + 1)).trans ?_
    rw [hk]
    exact iUnion₂_subset fun n hn => hmono hn
  exact (hinc k).not_subset h1

/-- **Exercise 11.10.3, the corresponding result for intersections.** The intersection of a
strictly decreasing sequence of internal sets is not internal. -/
theorem not_isInternalSet_iInter_of_ssubset_succ {Y : ℕ → Set αS}
    (hY : ∀ n, IsInternalSet α (Y n)) (hdec : ∀ n, Y (n + 1) ⊂ Y n) :
    ¬ IsInternalSet α (⋂ n, Y n) := by
  intro h
  obtain ⟨k, hk⟩ := exists_iInter_eq_biInter_le hY h
  have hanti : Antitone Y := antitone_nat_of_succ_le fun n => (hdec n).subset
  have h1 : Y k ⊆ Y (k + 1) := by
    refine Subset.trans ?_ (iInter_subset Y (k + 1))
    rw [hk]
    exact subset_iInter₂ fun n hn => hanti hn
  exact (hdec k).not_subset h1

/-- **Exercise 11.10.3, a correction.** The exercise also asserts that the union of a
strictly _decreasing_ sequence of internal sets is external. That is false as stated: the
union of a decreasing sequence is its first term, which is internal. The true statements are
the two preceding theorems. -/
theorem isInternalSet_iUnion_of_antitone {Y : ℕ → Set αS} (hY : ∀ n, IsInternalSet α (Y n))
    (hdec : ∀ n, Y (n + 1) ⊆ Y n) : IsInternalSet α (⋃ n, Y n) := by
  have hanti : Antitone Y := antitone_nat_of_succ_le hdec
  have e : ⋃ n, Y n = Y 0 :=
    Subset.antisymm (iUnion_subset fun n => hanti (Nat.zero_le n)) (subset_iUnion Y 0)
  rw [e]
  exact hY 0

end Saturation

/-!
## 11.11 Saturation Creates Nonstandard Entities

Saturation is an existence principle: whenever an element can be described as a common point
of a decreasing sequence of nonempty internal sets, such an element exists. The positive
infinitesimals are the common points of the intervals $`(0, \tfrac1n)`, and positive
unlimited numbers are the common points of the rays beyond $`n`. Less obviously, every
sequence of infinitesimals is bounded above by a single infinitesimal, and every sequence of
unlimited hypernaturals is bounded below by a single unlimited hypernatural.

The book numbers sequences from $`1`; here the $`n`-th interval is $`(0, \tfrac1{n+1})`.
-/

section Entities

/-- The real number $`\tfrac1{n+1}`, as a hyperreal. -/
theorem coe_one_div_natCast_add_one (n : ℕ) :
    ((1 / ((n : ℝ) + 1) : ℝ) : ℝ*) = 1 / ((n : ℝ*) + 1) := rfl

/-- A hyperreal that is less than $`\tfrac1{n+1}` in absolute value for every natural number
$`n` is infinitesimal. -/
theorem infinitesimal_of_forall_abs_lt_one_div {x : ℝ*}
    (h : ∀ n : ℕ, |x| < 1 / ((n : ℝ*) + 1)) : Infinitesimal x := by
  rw [infinitesimal_iff_abs_lt]
  intro r hr
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
  exact (h n).trans (by rw [← coe_one_div_natCast_add_one]; exact Hyperreal.coe_lt_coe.2 hn)

/-- An infinitesimal is less than $`\tfrac1{n+1}` in absolute value for every natural number
$`n`. -/
theorem Infinitesimal.abs_lt_one_div {x : ℝ*} (hx : Infinitesimal x) (n : ℕ) :
    |x| < 1 / ((n : ℝ*) + 1) := by
  rw [← coe_one_div_natCast_add_one]
  exact infinitesimal_iff_abs_lt.1 hx _ (by positivity)

/-- **Section 11.11.** The intersection of the decreasing sequence of internal intervals
$`(0, \tfrac1{n+1})` is precisely the set of positive infinitesimals. -/
theorem iInter_Ioo_zero_one_div :
    ⋂ n : ℕ, Ioo (0 : ℝ*) (1 / ((n : ℝ*) + 1)) = {x | PosInfinitesimal x} := by
  ext x
  simp only [mem_iInter, mem_Ioo, mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨(h 0).1, fun r hr => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
    exact (h n).2.trans (by rw [← coe_one_div_natCast_add_one]; exact Hyperreal.coe_lt_coe.2 hn)
  · rintro ⟨h0, h⟩ n
    refine ⟨h0, ?_⟩
    rw [← coe_one_div_natCast_add_one]
    exact h _ (by positivity)

/-- **Section 11.11.** Countable saturation implies that there are positive infinitesimals:
the intervals $`(0, \tfrac1{n+1})` are nonempty, internal and decreasing. -/
theorem exists_posInfinitesimal_of_saturation : ∃ x : ℝ*, PosInfinitesimal x := by
  have hpos : ∀ n : ℕ, (0 : ℝ*) < 1 / ((n : ℝ*) + 1) := fun n => by positivity
  obtain ⟨x, hx⟩ := iInter_nonempty_of_isInternal
    (X := fun n : ℕ => Ioo (0 : ℝ*) (1 / ((n : ℝ*) + 1))) (fun n => isInternal_Ioo _ _)
    (fun n => nonempty_Ioo.2 (hpos n))
    (fun n => Ioo_subset_Ioo_right (by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith))
  rw [iInter_Ioo_zero_one_div] at hx
  exact ⟨x, hx⟩

/-- A hyperreal greater than every natural number is positive unlimited. -/
theorem posUnlimited_of_forall_natCast_lt {x : ℝ*} (h : ∀ n : ℕ, (n : ℝ*) < x) :
    PosUnlimited x := by
  intro r
  obtain ⟨n, hn⟩ := exists_nat_gt r
  exact lt_trans (Hyperreal.coe_lt_coe.2 hn) (h n)

/-- **Exercise 11.11.1.** Countable saturation implies that there are positive unlimited
hyperreals: the rays $`\{x : n < x\}` are nonempty, internal and decreasing. -/
theorem exists_posUnlimited_of_saturation : ∃ x : ℝ*, PosUnlimited x := by
  obtain ⟨x, hx⟩ := iInter_nonempty_of_isInternal
    (X := fun n : ℕ => Ioi (n : ℝ*)) (fun n => isInternal_Ioi _)
    (fun n => ⟨(n : ℝ*) + 1, by simp⟩)
    (fun n => Ioi_subset_Ioi (by push_cast; linarith))
  exact ⟨x, posUnlimited_of_forall_natCast_lt fun n => mem_iInter.1 hx n⟩

/-- **Exercise 11.11.1.** Countable saturation implies that there are negative unlimited
hyperreals: the rays $`\{x : x < -n\}` are nonempty, internal and decreasing. -/
theorem exists_negUnlimited_of_saturation : ∃ x : ℝ*, NegUnlimited x := by
  obtain ⟨x, hx⟩ := iInter_nonempty_of_isInternal
    (X := fun n : ℕ => Iio (-(n : ℝ*))) (fun n => isInternal_Iio _)
    (fun n => ⟨-(n : ℝ*) - 1, by simp⟩)
    (fun n => Iio_subset_Iio (by push_cast; linarith))
  refine ⟨x, ?_⟩
  rw [← neg_neg x, negUnlimited_neg_iff]
  refine posUnlimited_of_forall_natCast_lt fun n => ?_
  have := mem_Iio.1 (mem_iInter.1 hx n)
  linarith

/-- **Section 11.11.** Every sequence of infinitesimals has an infinitesimal upper bound. The
internal intervals $`[\varepsilon_n, \tfrac1{n+1})` have the finite intersection property,
because the largest of finitely many $`\varepsilon_n` belongs to each of the corresponding
intervals, and any common point of all of them is an infinitesimal upper bound. -/
theorem exists_infinitesimal_upper_bound (e : ℕ → ℝ*) (he : ∀ n, Infinitesimal (e n)) :
    ∃ d, Infinitesimal d ∧ ∀ n, e n ≤ d := by
  have hlt : ∀ m n : ℕ, e m < 1 / ((n : ℝ*) + 1) := fun m n =>
    (le_abs_self _).trans_lt ((he m).abs_lt_one_div n)
  obtain ⟨x, hx⟩ := iInter_nonempty_of_fip (α := ℝ)
    (X := fun n : ℕ => Ico (e n) (1 / ((n : ℝ*) + 1))) (fun n => isInternal_Ico _ _)
    (fun s => by
      rcases s.eq_empty_or_nonempty with rfl | hs
      · exact ⟨0, by simp⟩
      · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' hs e
        refine ⟨s.sup' hs e, mem_iInter₂.2 fun n hn => ⟨Finset.le_sup' e hn, ?_⟩⟩
        rw [hj]
        exact hlt j n)
  have hx' : ∀ n, e n ≤ x ∧ x < 1 / ((n : ℝ*) + 1) := fun n => mem_iInter.1 hx n
  refine ⟨x, infinitesimal_of_forall_abs_lt_one_div fun n => abs_lt.2 ⟨?_, (hx' n).2⟩,
    fun n => (hx' n).1⟩
  have h1 := (abs_lt.1 ((he 0).abs_lt_one_div n)).1
  exact lt_of_lt_of_le h1 (hx' 0).1

/-- **Section 11.11.** Every sequence of unlimited hypernaturals has an unlimited
hypernatural lower bound. The internal sets $`(n, s_n] \cap {}^*\mathbb N` have the finite
intersection property, because the least of finitely many $`s_n` belongs to each of the
corresponding sets, and any common point of all of them is an unlimited lower bound. -/
theorem exists_unlimited_hyperNat_lower_bound (s : ℕ → ℝ*) (hs : ∀ n, s n ∈ ℕ*)
    (hU : ∀ n, Unlimited (s n)) : ∃ K ∈ ℕ*, Unlimited K ∧ ∀ n, K ≤ s n := by
  obtain ⟨x, hx⟩ := iInter_nonempty_of_fip (α := ℝ)
    (X := fun n : ℕ => Ioc (n : ℝ*) (s n) ∩ ℕ*)
    (fun n => (isInternal_Ioc _ _).inter isInternal_hyperNat)
    (fun t => by
      rcases t.eq_empty_or_nonempty with rfl | ht
      · exact ⟨0, by simp⟩
      · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' ht s
        refine ⟨t.inf' ht s, mem_iInter₂.2 fun n hn => ⟨⟨?_, Finset.inf'_le s hn⟩, ?_⟩⟩
        · rw [hj]
          exact posUnlimited_of_mem_hyperNat (hs j) (hU j) n
        · rw [hj]
          exact hs j)
  have hx' : ∀ n : ℕ, ((n : ℝ*) < x ∧ x ≤ s n) ∧ x ∈ ℕ* := fun n => mem_iInter.1 hx n
  exact ⟨x, (hx' 0).2, (posUnlimited_of_forall_natCast_lt fun n => (hx' n).1.1).unlimited,
    fun n => (hx' n).1.2⟩

/-- The integer part of a positive unlimited hyperreal is a positive unlimited
hypernatural. -/
theorem PosUnlimited.hfloor {x : ℝ*} (hx : PosUnlimited x) :
    hfloor x ∈ ℕ* ∧ PosUnlimited (hfloor x) := by
  refine ⟨hfloor_mem_hyperNat hx.pos.le, fun r => ?_⟩
  have h1 := hx.sub_one r
  have h2 := lt_hfloor_add_one x
  linarith

/-- **Exercise 11.11.2, first half, the construction.** Let $`(s_n)` be a sequence of
unlimited hypernaturals and let $`\delta` be an infinitesimal with $`1/s_n \le \delta` for
all $`n`. Then the integer part of $`1/\delta` is an unlimited hypernatural lower bound of
the $`s_n`. No saturation and no global hypothesis is involved: the bound is computed from
$`\delta`. -/
theorem hfloor_inv_unlimited_lower_bound {s : ℕ → ℝ*} {d : ℝ*} (hs : ∀ n, s n ∈ ℕ*)
    (hU : ∀ n, Unlimited (s n)) (hd : Infinitesimal d) (hle : ∀ n, (s n)⁻¹ ≤ d) :
    hfloor d⁻¹ ∈ ℕ* ∧ Unlimited (hfloor d⁻¹) ∧ ∀ n, hfloor d⁻¹ ≤ s n := by
  have hs0 : ∀ n, 0 < s n := fun n => (posUnlimited_of_mem_hyperNat (hs n) (hU n)).pos
  have hd0 : 0 < d := lt_of_lt_of_le (inv_pos.2 (hs0 0)) (hle 0)
  have hdU : PosUnlimited d⁻¹ :=
    posUnlimited_iff.2 ⟨hd.inv_unlimited hd0.ne', inv_pos.2 hd0⟩
  refine ⟨hdU.hfloor.1, hdU.hfloor.2.unlimited, fun n => (hfloor_le _).trans ?_⟩
  exact (inv_le_comm₀ (hs0 n) hd0).1 (hle n)

/-- **Exercise 11.11.2, second half, the construction.** Let $`(\varepsilon_n)` be any
sequence of hyperreals and let $`K` be an unlimited hypernatural that is at most the integer
part of $`1/|\varepsilon_n|` for every $`n` with $`\varepsilon_n \ne 0`. Then $`1/K` is an
infinitesimal upper bound of the $`\varepsilon_n`. Again the bound is computed from $`K`,
with no saturation and no global hypothesis. -/
theorem inv_infinitesimal_upper_bound {e : ℕ → ℝ*} {K : ℝ*} (hK : K ∈ ℕ*) (hKU : Unlimited K)
    (hKle : ∀ n, e n ≠ 0 → K ≤ hfloor |e n|⁻¹) :
    Infinitesimal K⁻¹ ∧ ∀ n, e n ≤ K⁻¹ := by
  have hK0 : 0 < K := (posUnlimited_of_mem_hyperNat hK hKU).pos
  refine ⟨hKU.inv_infinitesimal, fun n => ?_⟩
  by_cases hn : e n = 0
  · rw [hn]
    exact (inv_pos.2 hK0).le
  · have h2 : K ≤ |e n|⁻¹ := (hKle n hn).trans (hfloor_le _)
    exact (le_abs_self _).trans ((le_inv_comm₀ (abs_pos.2 hn) hK0).2 h2)

/-- **Exercise 11.11.2, first half.** The existence of infinitesimal upper bounds for
sequences of infinitesimals implies the existence of unlimited hypernatural lower bounds for
sequences of unlimited hypernaturals, without saturation: if $`\delta` is an infinitesimal
upper bound of the reciprocals $`1/s_n`, then the integer part of $`1/\delta` is an unlimited
hypernatural lower bound of the $`s_n`. Both properties are in fact true (by the two theorems
before these), so as a statement this implication is trivially true; its content is the
construction, which is stated on its own, free of any hypothesis that could make it vacuous,
as {name}`Goldblatt.hfloor_inv_unlimited_lower_bound`. -/
theorem unlimited_lower_bound_of_infinitesimal_upper_bound
    (H : ∀ e : ℕ → ℝ*, (∀ n, Infinitesimal (e n)) → ∃ d, Infinitesimal d ∧ ∀ n, e n ≤ d)
    (s : ℕ → ℝ*) (hs : ∀ n, s n ∈ ℕ*) (hU : ∀ n, Unlimited (s n)) :
    ∃ K ∈ ℕ*, Unlimited K ∧ ∀ n, K ≤ s n := by
  obtain ⟨d, hd, hle⟩ := H (fun n => (s n)⁻¹) fun n => (hU n).inv_infinitesimal
  obtain ⟨h1, h2, h3⟩ := hfloor_inv_unlimited_lower_bound hs hU hd hle
  exact ⟨hfloor d⁻¹, h1, h2, h3⟩

/-- **Exercise 11.11.2, second half.** The existence of unlimited hypernatural lower bounds
implies the existence of infinitesimal upper bounds, without saturation: replace each nonzero
$`\varepsilon_n` by the integer part of $`1/|\varepsilon_n|`, an unlimited hypernatural; if
$`K` is an unlimited lower bound of these numbers then $`1/K` is an infinitesimal upper bound
of the $`\varepsilon_n`. The construction on its own is
{name}`Goldblatt.inv_infinitesimal_upper_bound`. -/
theorem infinitesimal_upper_bound_of_unlimited_lower_bound
    (H : ∀ s : ℕ → ℝ*, (∀ n, s n ∈ ℕ*) → (∀ n, Unlimited (s n)) →
      ∃ K ∈ ℕ*, Unlimited K ∧ ∀ n, K ≤ s n)
    (e : ℕ → ℝ*) (he : ∀ n, Infinitesimal (e n)) : ∃ d, Infinitesimal d ∧ ∀ n, e n ≤ d := by
  classical
  have hinv : ∀ n, e n ≠ 0 → PosUnlimited |e n|⁻¹ := fun n hn =>
    posUnlimited_iff.2 ⟨((he n).of_abs_le (abs_abs _).le).inv_unlimited (abs_ne_zero.2 hn),
      inv_pos.2 (abs_pos.2 hn)⟩
  obtain ⟨K, hK, hKU, hKle⟩ := H (fun n => if e n = 0 then ω else hfloor |e n|⁻¹)
    (fun n => by
      by_cases hn : e n = 0
      · simp only [hn, ↓reduceIte]
        exact omega_mem_hyperNat
      · simp only [hn, ↓reduceIte]
        exact (hinv n hn).hfloor.1)
    (fun n => by
      by_cases hn : e n = 0
      · simp only [hn, ↓reduceIte]
        exact unlimited_omega
      · simp only [hn, ↓reduceIte]
        exact (hinv n hn).hfloor.2.unlimited)
  obtain ⟨h1, h2⟩ := inv_infinitesimal_upper_bound (e := e) hK hKU fun n hn => by
    simpa only [hn, ↓reduceIte] using hKle n
  exact ⟨K⁻¹, h1, h2⟩

end Entities

/-!
## 11.12 The Size of an Internal Set

Countable saturation forces infinite internal sets to be large: an internal set cannot be
countably infinite. Given an enumeration of a countable internal set, remove its points one
at a time; this produces a decreasing sequence of internal sets with empty intersection, so
one of them must already be empty. In particular the hypernaturals up to an unlimited $`N`
form an uncountable set, and there are uncountably many galaxies of hypernaturals below
$`N`.
-/

section Size

variable {α αS : Type u} [StarType α αS]

/-- **Section 11.12.** A countable internal set is finite. -/
theorem IsInternalSet.finite_of_countable {X : Set αS} (hX : IsInternalSet α X)
    (hc : X.Countable) : X.Finite := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · exact finite_empty
  obtain ⟨f, rfl⟩ := hc.exists_eq_range hne
  by_contra hinf
  obtain ⟨x, hx⟩ := iInter_nonempty_of_isInternalSet (X := fun n => range f \ f '' Iic n)
    (fun n => hX.diff (isInternalSet_of_finite ((finite_Iic n).image f)))
    (fun n => by
      by_contra hE
      exact hinf (((finite_Iic n).image f).subset
        (sdiff_eq_empty.1 (not_nonempty_iff_eq_empty.1 hE))))
    (fun n x hx => ⟨hx.1, fun h => hx.2 (image_mono (Iic_subset_Iic.2 (Nat.le_succ n)) h)⟩)
  obtain ⟨m, hm⟩ := (mem_iInter.1 hx 0).1
  exact (mem_iInter.1 hx m).2 ⟨m, mem_Iic.2 le_rfl, hm⟩

/-- **Section 11.12.** Every internal set is either finite or uncountable. -/
theorem IsInternalSet.finite_or_not_countable {X : Set αS} (hX : IsInternalSet α X) :
    X.Finite ∨ ¬ X.Countable :=
  (em X.Countable).imp hX.finite_of_countable id

/-- **Section 11.12.** An infinite internal set is uncountable. -/
theorem IsInternalSet.not_countable_of_infinite {X : Set αS} (hX : IsInternalSet α X)
    (hinf : X.Infinite) : ¬ X.Countable :=
  fun hc => hinf (hX.finite_of_countable hc)

/-- **Section 11.12, the remark on Section 11.7.** A set of standard elements that is
internal, as a set of elements of the star type, is finite. This is the result of Section
11.7 for an arbitrary type, now as a consequence of saturation: an infinite set contains a
countably infinite subset, which would be a countably infinite internal set. -/
theorem finite_of_isInternalSet_image_of {A : Set α}
    (hA : IsInternalSet α (of '' A : Set αS)) : A.Finite := by
  by_contra hinf
  have : Infinite A := infinite_coe_iff.2 hinf
  have hg : Function.Injective fun n => (Infinite.natEmbedding A n : α) :=
    fun m n h => (Infinite.natEmbedding A).injective (Subtype.ext h)
  have hB : IsInternalSet α (of '' range (fun n => (Infinite.natEmbedding A n : α)) : Set αS) :=
    hA.image_of_subset (by rintro _ ⟨n, rfl⟩; exact (Infinite.natEmbedding A n).2)
  have hfin := hB.finite_of_countable ((countable_range _).image _)
  exact infinite_range_of_injective hg (hfin.of_finite_image of_injective.injOn)

/-- **Section 11.12.** If $`N` is an unlimited hypernatural then the internal set
$`\{k \in {}^*\mathbb N : k \le N\}` is uncountable. -/
theorem not_countable_setOf_hyperNat_le {N : ℝ*} (hN : N ∈ ℕ*) (hU : Unlimited N) :
    ¬ {k : ℝ* | k ∈ ℕ* ∧ k ≤ N}.Countable := fun hc =>
  infinite_setOf_hyperNat_le hN hU
    (IsInternalSet.finite_of_countable (isInternal_setOf_hyperNat_le hN) hc)

/-- **Section 11.12.** If $`N` is an unlimited hypernatural then there are uncountably many
unlimited hypernaturals below $`N`. -/
theorem not_countable_setOf_unlimited_hyperNat_le {N : ℝ*} (hN : N ∈ ℕ*) (hU : Unlimited N) :
    ¬ {k : ℝ* | k ∈ ℕ* ∧ Unlimited k ∧ k ≤ N}.Countable := fun hc =>
  not_countable_setOf_hyperNat_le hN hU
    ((hc.union (countable_range ((↑) : ℕ → ℝ*))).mono fun k hk => by
      by_cases hl : Limited k
      · exact Or.inr (((limited_hyperNat_iff hk.1).1 hl).imp fun n hn => hn.symm)
      · exact Or.inl ⟨hk.1, not_limited_iff_unlimited.1 hl, hk.2⟩)

/-- **Section 11.12.** If $`N` is an unlimited hypernatural then there are uncountably many
galaxies of unlimited hypernaturals strictly below the galaxy of $`N`, that is, between the
standard natural numbers and $`N`. -/
theorem not_countable_image_natGalaxy {N : ℝ*} (hN : N ∈ ℕ*) (hU : Unlimited N) :
    ¬ (natGalaxy '' {H : ℝ* | H ∈ ℕ* ∧ Unlimited H ∧ GalLT H N}).Countable := by
  intro hc
  have hgal : ∀ H ∈ ℕ*, Unlimited H → (natGalaxy H).Countable := fun H hH hHU => by
    rw [natGalaxy_eq_of_unlimited hH hHU]
    exact (countable_range fun n : ℤ => H + n).mono fun x hx => hx.imp fun n hn => hn.symm
  have hT : {H : ℝ* | H ∈ ℕ* ∧ Unlimited H ∧ GalLT H N}.Countable := by
    refine (hc.sUnion ?_).mono fun H hH => ?_
    · rintro _ ⟨H, hH, rfl⟩
      exact hgal H hH.1 hH.2.1
    · exact ⟨natGalaxy H, ⟨H, hH, rfl⟩, LimClose.refl H, hH.1⟩
  refine not_countable_setOf_unlimited_hyperNat_le hN hU
    ((hT.union (hgal N hN hU)).mono fun k hk => ?_)
  by_cases hkN : k ∼ N
  · exact Or.inr ⟨hkN.symm, hk.1⟩
  · exact Or.inl ⟨hk.1, hk.2.1,
      lt_of_le_of_ne hk.2.2 fun e => hkN (e ▸ LimClose.refl k), hkN⟩

end Size

/-!
## 11.13 Closure of the Shadow of an Internal Set

The _shadow_ of a set of hyperreals is the set of shadows of its limited members. The shadow
of an internal set is always a closed set of reals. The book proves this from countable
saturation, and an exercise asks for a second proof from overflow; both are given.
-/

section Shadow

/-- **Section 11.13.** The shadow $`\operatorname{sh}(X)` of a set $`X` of hyperreals: the
set of shadows of the limited members of $`X`. This is the definition that later chapters
should reuse for shadows of sets. -/
def shSet (X : Set ℝ*) : Set ℝ := {r | ∃ x ∈ X, Limited x ∧ sh x = r}

/-- **Section 11.13.** A real number belongs to the shadow of $`X` if and only if it is
infinitely close to a member of $`X`. -/
theorem mem_shSet_iff {X : Set ℝ*} {r : ℝ} : r ∈ shSet X ↔ ∃ x ∈ X, x ≊ (r : ℝ*) := by
  constructor
  · rintro ⟨x, hx, hl, rfl⟩
    exact ⟨x, hx, hl.infClose_sh⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, limited_of_infClose_coe h, sh_eq_of_infClose h⟩

/-- **Section 11.13, first example.** If $`a < b` are limited, the shadow of the interval
$`(a, b)` is the closed real interval from the shadow of $`a` to the shadow of $`b`. -/
theorem shSet_Ioo_of_limited {a b : ℝ*} (ha : Limited a) (hb : Limited b) (hab : a < b) :
    shSet (Ioo a b) = Icc (sh a) (sh b) := by
  have hε := epsilon_pos_infinitesimal.1
  have hδ0 : 0 < min (ε : ℝ*) ((b - a) / 2) := lt_min hε (half_pos (sub_pos.2 hab))
  have hδ : Infinitesimal (min (ε : ℝ*) ((b - a) / 2)) :=
    infinitesimal_epsilon.of_abs_le (by
      rw [abs_of_pos hδ0, abs_of_pos hε]
      exact min_le_left _ _)
  have hδ2 : min (ε : ℝ*) ((b - a) / 2) ≤ (b - a) / 2 := min_le_right _ _
  ext r
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, hx, rfl⟩
    exact ⟨sh_le_sh ha hx h1.le, sh_le_sh hx hb h2.le⟩
  · rintro ⟨h1, h2⟩
    rcases h1.eq_or_lt with e | h1
    · refine ⟨a + min (ε : ℝ*) ((b - a) / 2), ⟨by linarith, by linarith⟩, ha.add hδ.limited, ?_⟩
      rw [sh_add_infinitesimal ha hδ, e]
    · rcases h2.eq_or_lt with e | h2
      · refine ⟨b + -min (ε : ℝ*) ((b - a) / 2), ⟨by linarith, by linarith⟩,
          hb.add hδ.neg.limited, ?_⟩
        rw [sh_add_infinitesimal hb hδ.neg, e]
      · exact ⟨r, ⟨ha.lt_of_sh_lt h1, hb.lt_of_lt_sh h2⟩, limited_coe r, sh_coe r⟩

/-- **Section 11.13, second example.** If $`a` is limited and $`b` is positive unlimited,
the shadow of the interval $`(a, b)` is the closed ray of reals from the shadow of $`a`. -/
theorem shSet_Ioo_of_posUnlimited {a b : ℝ*} (ha : Limited a) (hb : PosUnlimited b) :
    shSet (Ioo a b) = Ici (sh a) := by
  ext r
  constructor
  · rintro ⟨x, ⟨h1, -⟩, hx, rfl⟩
    exact sh_le_sh ha hx h1.le
  · intro h1
    rcases (mem_Ici.1 h1).eq_or_lt with e | h1
    · refine ⟨a + ε, ⟨by linarith [epsilon_pos_infinitesimal.1], ?_⟩,
        ha.add infinitesimal_epsilon.limited, ?_⟩
      · exact (ha.add infinitesimal_epsilon.limited).lt_posUnlimited hb
      · rw [sh_add_infinitesimal ha infinitesimal_epsilon, e]
    · exact ⟨r, ⟨ha.lt_of_sh_lt h1, hb r⟩, limited_coe r, sh_coe r⟩

/-- **Theorem 11.13.1, first step.** If the real number $`r` is a closure point of the shadow
of $`X`, then every interval of positive real radius around $`r` contains a member of
$`X`. -/
theorem exists_mem_Ioo_of_mem_closure_shSet {X : Set ℝ*} {r : ℝ} (hr : r ∈ closure (shSet X))
    {c : ℝ} (hc : 0 < c) : ∃ x ∈ X, (r : ℝ*) - (c : ℝ*) < x ∧ x < (r : ℝ*) + (c : ℝ*) := by
  obtain ⟨_, ⟨x, hx, hl, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 hr c hc
  rw [Real.dist_eq] at hd
  obtain ⟨h1, h2⟩ := abs_lt.1 hd
  have h3 : ((r - c : ℝ) : ℝ*) < x := hl.lt_of_lt_sh (by linarith)
  have h4 : x < ((r + c : ℝ) : ℝ*) := hl.lt_of_sh_lt (by linarith)
  exact ⟨x, hx, h3, h4⟩

/-- **Theorem 11.13.1.** The shadow of an internal set is a closed set of real numbers. If
$`r` is a closure point of the shadow of $`X`, the internal sets
$`X \cap (r - \tfrac1{n+1}, r + \tfrac1{n+1})` are nonempty and decreasing, so by countable
saturation they have a common point, which belongs to $`X` and is infinitely close to
$`r`. -/
theorem IsInternal.isClosed_shSet {X : Set ℝ*} (hX : IsInternal X) : IsClosed (shSet X) := by
  refine isClosed_of_closure_subset fun r hr => ?_
  obtain ⟨y, hy⟩ := iInter_nonempty_of_isInternal
    (X := fun n : ℕ => X ∩ Ioo ((r : ℝ*) - 1 / ((n : ℝ*) + 1)) (r + 1 / ((n : ℝ*) + 1)))
    (fun n => hX.inter (isInternal_Ioo _ _))
    (fun n => by
      obtain ⟨x, hx, h1, h2⟩ := exists_mem_Ioo_of_mem_closure_shSet hr
        (c := 1 / ((n : ℝ) + 1)) (by positivity)
      exact ⟨x, hx, h1, h2⟩)
    (fun n x hx => by
      have hle : (1 : ℝ*) / (((n + 1 : ℕ) : ℝ*) + 1) ≤ 1 / ((n : ℝ*) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith
      exact ⟨hx.1, by linarith [hx.2.1], by linarith [hx.2.2]⟩)
  have hy' : ∀ n : ℕ, y ∈ X ∧ (r : ℝ*) - 1 / ((n : ℝ*) + 1) < y ∧ y < r + 1 / ((n : ℝ*) + 1) :=
    fun n => mem_iInter.1 hy n
  refine mem_shSet_iff.2 ⟨y, (hy' 0).1, infinitesimal_of_forall_abs_lt_one_div fun n => ?_⟩
  exact abs_lt.2 ⟨by linarith [(hy' n).2.1], by linarith [(hy' n).2.2]⟩

/-- **Exercise 11.13.2, the atomic formula.** In the ultrapower the atomic formula
$`x_2 - 1/x_1 < x_0 \wedge x_0 < x_2 + 1/x_1` says what it should. -/
theorem starRealize_mem_Ioo_sub_add_one_div (y k r : ℝ*) :
    (IFormula.rel fun _ (v : Fin 3 → ℝ) =>
        v 2 - 1 / v 1 < v 0 ∧ v 0 < v 2 + 1 / v 1).starRealize (Fin.cons y ![k, r]) ↔
      y ∈ Ioo (r - 1 / k) (r + 1 / k) := by
  obtain ⟨η, rfl⟩ := hyperreal_exists_rep y
  obtain ⟨κ, rfl⟩ := hyperreal_exists_rep k
  obtain ⟨ρ, rfl⟩ := hyperreal_exists_rep r
  have e1 : Hyperreal.ofSeq ρ - 1 / Hyperreal.ofSeq κ =
      Hyperreal.ofSeq fun n => ρ n - 1 / κ n := rfl
  have e2 : Hyperreal.ofSeq ρ + 1 / Hyperreal.ofSeq κ =
      Hyperreal.ofSeq fun n => ρ n + 1 / κ n := rfl
  rw [mem_Ioo, e1, e2, ofSeq_lt_ofSeq_iff, ofSeq_lt_ofSeq_iff, ← almostAll_and]
  exact hyperreal_internalRelN_vec₃

/-- **Exercise 11.13.2, the definable set.** For an internal set $`X` and a hyperreal $`r`,
the set of hypernaturals $`n` for which $`X` meets the interval
$`(r - \tfrac1n, r + \tfrac1n)` is internal, by the internal set definition principle: it is
defined by the formula
$`x \in \mathbb N \wedge \exists z\,(z \in A \wedge y - \tfrac1x < z < y + \tfrac1x)` with
the parameter $`r` for $`y` and the internal set $`X` for $`A`. -/
theorem IsInternal.isInternal_setOf_ball_inter_nonempty {X : Set ℝ*} (hX : IsInternal X)
    (r : ℝ*) :
    IsInternal {k : ℝ* | k ∈ ℕ* ∧ (X ∩ Ioo (r - 1 / k) (r + 1 / k)).Nonempty} := by
  obtain ⟨A, rfl⟩ := hX
  refine IFormula.isInternalSet_of_forall_iff (α := ℝ)
    ((IFormula.mem 0 fun _ => range ((↑) : ℕ → ℝ)).and
      (IFormula.ex ((IFormula.mem 0 A).and
        (IFormula.rel fun _ v => v 2 - 1 / v 1 < v 0 ∧ v 0 < v 2 + 1 / v 1))))
    ![r] fun x => ?_
  simp only [IFormula.starRealize_ex, IFormula.starRealize_and, IFormula.starRealize_mem,
    internalSet_const_range_natCast, mem_ofPred_eq]
  refine and_congr Iff.rfl (exists_congr fun y => and_congr Iff.rfl ?_)
  exact (starRealize_mem_Ioo_sub_add_one_div y x r).symm

/-- **Exercise 11.13.2.** The shadow of an internal set is closed, proved by overflow instead
of countable saturation. If $`r` is a closure point of the shadow of $`X`, then $`X` meets
$`(r - \tfrac1n, r + \tfrac1n)` for every standard $`n \ge 1`; the set of such $`n` is
internal, so by overflow it contains an unlimited $`K`, and a point of $`X` within
$`\tfrac1K` of $`r` is infinitely close to $`r`. -/
theorem IsInternal.isClosed_shSet_of_overflow {X : Set ℝ*} (hX : IsInternal X) :
    IsClosed (shSet X) := by
  refine isClosed_of_closure_subset fun r hr => ?_
  obtain ⟨K, hK, hKU, hKX⟩ := (hX.isInternal_setOf_ball_inter_nonempty r).overflow 1
    (fun n hn => ⟨natCast_mem_hyperNat n, by
      obtain ⟨x, hx, h1, h2⟩ := exists_mem_Ioo_of_mem_closure_shSet hr
        (c := 1 / (n : ℝ)) (by
          have : (0 : ℝ) < n := by exact_mod_cast hn
          positivity)
      exact ⟨x, hx, h1, h2⟩⟩)
  obtain ⟨-, y, hyX, hy1, hy2⟩ := hKX K hK
    (posUnlimited_of_mem_hyperNat hK hKU ((1 : ℕ) : ℝ)).le le_rfl
  refine mem_shSet_iff.2 ⟨y, hyX, ?_⟩
  have hI : Infinitesimal (1 / K) := by
    rw [one_div]
    exact hKU.inv_infinitesimal
  have h0 : (0 : ℝ*) < 1 / K := by
    have := (posUnlimited_of_mem_hyperNat hK hKU).pos
    positivity
  refine hI.of_abs_le ?_
  rw [abs_of_pos h0]
  exact (abs_lt.2 ⟨by linarith, by linarith⟩).le

end Shadow

/-!
## 11.14 Interval Topology and Hyper-Open Sets

Section 10.5 introduced three notions of open subset of the hyperreal line: _interval-open_
sets (unions of open intervals with hyperreal end points), _real-open_ sets (unions of open
intervals of real radius) and _S-open_ sets (unions of S-neighbourhoods). This section adds a
fourth, which only makes sense for internal sets: $`[A_n]` is _hyper-open_ when almost all
the $`A_n` are open sets of reals. Hyper-open sets are interval-open, and for internal sets
the two notions coincide; the hyper-open sets are a base of the interval topology but not a
topology. The section ends with a characterization of the internal S-open sets as those that
contain the halo of each of their points.

The notions of Section 10.5 are restated here, in the namespace {lit}`HyperTopology`, in
their pointwise form: a set is a union of sets from a family exactly when each of its points
lies in a member of the family that is included in the set. They are restated rather than
imported because this chapter does not depend on Chapter 10; when the Chapter 10 page defines
them, these local copies are meant to be replaced by, or proved equivalent to, the
definitions made there.
-/

section HyperOpen

namespace HyperTopology

/-- **Section 10.5, recalled.** A set of hyperreals is _interval-open_ if each of its points
lies in a hyperreal open interval included in the set. -/
def IntervalOpen (A : Set ℝ*) : Prop := ∀ x ∈ A, ∃ a b : ℝ*, x ∈ Ioo a b ∧ Ioo a b ⊆ A

/-- **Section 10.5, recalled.** A set of hyperreals is _real-open_ if each of its points lies
in an interval $`(r - \varepsilon, r + \varepsilon)` of positive real radius $`\varepsilon`,
around a hyperreal $`r`, that is included in the set. -/
def RealOpen (A : Set ℝ*) : Prop :=
  ∀ x ∈ A, ∃ (r : ℝ*) (e : ℝ), 0 < e ∧ x ∈ Ioo (r - e) (r + e) ∧ Ioo (r - (e : ℝ*)) (r + e) ⊆ A

/-- **Section 10.5, recalled.** The S-neighbourhood $`((r - \varepsilon, r + \varepsilon))`:
the set of points whose whole halo lies in the interval. -/
def sNhd (r : ℝ*) (e : ℝ) : Set ℝ* := {x | hal x ⊆ Ioo (r - (e : ℝ*)) (r + e)}

/-- **Section 10.5, recalled.** A set of hyperreals is _S-open_ if each of its points lies in
an S-neighbourhood of positive real radius that is included in the set. -/
def SOpen (A : Set ℝ*) : Prop :=
  ∀ x ∈ A, ∃ (r : ℝ*) (e : ℝ), 0 < e ∧ x ∈ sNhd r e ∧ sNhd r e ⊆ A

/-- **Section 10.5, recalled.** A set is interval-open if and only if it is a union of
hyperreal open intervals. -/
theorem intervalOpen_iff_exists_sUnion {A : Set ℝ*} :
    IntervalOpen A ↔ ∃ 𝒮 : Set (Set ℝ*), (∀ S ∈ 𝒮, ∃ a b : ℝ*, S = Ioo a b) ∧ A = ⋃₀ 𝒮 := by
  constructor
  · intro h
    refine ⟨{S | (∃ a b : ℝ*, S = Ioo a b) ∧ S ⊆ A}, fun S hS => hS.1, ?_⟩
    refine Subset.antisymm (fun x hx => ?_) (sUnion_subset fun S hS => hS.2)
    obtain ⟨a, b, hx', hsub⟩ := h x hx
    exact ⟨Ioo a b, ⟨⟨a, b, rfl⟩, hsub⟩, hx'⟩
  · rintro ⟨𝒮, h𝒮, rfl⟩ x ⟨S, hS, hx⟩
    obtain ⟨a, b, rfl⟩ := h𝒮 S hS
    exact ⟨a, b, hx, subset_sUnion_of_mem hS⟩

end HyperTopology

open HyperTopology

/-- **Section 11.14.** An internal set $`[A_n]` is _hyper-open_ if $`A_n` is an open set of
reals for almost all $`n`. By Theorem 11.2(3) this does not depend on the defining sequence
({lit}`Goldblatt.hyperOpen_internalSet_iff`). -/
def HyperOpen (X : Set ℝ*) : Prop :=
  ∃ A : ℕ → Set ℝ, X = internalSet A ∧ ∀ᶠ n in hyperfilter ℕ, IsOpen (A n)

/-- **Section 11.14.** $`[A_n]` is hyper-open if and only if almost all $`A_n` are open,
whatever sequence defines the set. -/
theorem hyperOpen_internalSet_iff {A : ℕ → Set ℝ} :
    HyperOpen (internalSet A) ↔ ∀ᶠ n in hyperfilter ℕ, IsOpen (A n) := by
  constructor
  · rintro ⟨A', hA', h⟩
    exact ((internalSet_eq_iff.1 hA').and h).mono fun n hn => hn.1 ▸ hn.2
  · exact fun h => ⟨A, rfl, h⟩

/-- **Section 11.14.** A hyper-open set is internal. -/
theorem HyperOpen.isInternal {X : Set ℝ*} (hX : HyperOpen X) : IsInternal X := by
  obtain ⟨A, rfl, -⟩ := hX
  exact ⟨A, rfl⟩

/-- **Section 11.14.** Every hyperreal open interval is hyper-open. -/
theorem hyperOpen_Ioo (a b : ℝ*) : HyperOpen (Ioo a b) := by
  obtain ⟨a, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨b, rfl⟩ := hyperreal_exists_rep b
  exact ⟨_, (internalSet_Ioo a b).symm, Eventually.of_forall fun _ => isOpen_Ioo⟩

/-- **Lemma 11.14.1.** Every hyper-open set is a union of hyperreal open intervals: each
point $`[r_n]` of $`[A_n]` lies in an interval $`([a_n], [b_n])` included in the set, where
$`(a_n, b_n)` is an interval around $`r_n` inside the open set $`A_n`. -/
theorem HyperOpen.intervalOpen {X : Set ℝ*} (hX : HyperOpen X) : IntervalOpen X := by
  obtain ⟨A, rfl, hA⟩ := hX
  intro x hx
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  have h1 : ∀ᶠ n in hyperfilter ℕ, ∃ e : ℝ, 0 < e ∧ Ioo (r n - e) (r n + e) ⊆ A n :=
    (hA.and (hyperreal_ofSeq_mem_internalSet.1 hx)).mono fun n hn => by
      obtain ⟨e, he, hsub⟩ := Metric.isOpen_iff.1 hn.1 (r n) hn.2
      exact ⟨e, he, by rwa [Real.ball_eq_Ioo] at hsub⟩
  obtain ⟨e, he⟩ := exists_seq_of_almostAll_exists h1
  refine ⟨Hyperreal.ofSeq fun n => r n - e n, Hyperreal.ofSeq fun n => r n + e n, ⟨?_, ?_⟩, ?_⟩
  · exact ofSeq_lt_ofSeq_iff.2 (he.mono fun n hn => by linarith [hn.1])
  · exact ofSeq_lt_ofSeq_iff.2 (he.mono fun n hn => by linarith [hn.1])
  · rw [← internalSet_Ioo]
    exact internalSet_subset_iff.2 (he.mono fun n hn => hn.2)

/-- **Section 11.14.** The set of limited numbers is the union of the hyper-open intervals
$`(-n, n)` over the natural numbers $`n`. -/
theorem limitedSet_eq_iUnion_Ioo : 𝕃 = ⋃ n : ℕ, Ioo (-(n : ℝ*)) n := by
  ext x
  simp only [mem_limitedSet, mem_iUnion, mem_Ioo, limited_iff_exists_nat, abs_lt]

/-- **Section 11.14.** The set of limited numbers is interval-open. -/
theorem intervalOpen_limitedSet : IntervalOpen 𝕃 := by
  intro x hx
  obtain ⟨n, hn⟩ := limited_iff_exists_nat.1 hx
  refine ⟨-(n : ℝ*), n, abs_lt.1 hn, fun y hy => ?_⟩
  exact limited_iff_exists_nat.2 ⟨n, abs_lt.2 hy⟩

/-- **Section 11.14.** The set of limited numbers is not hyper-open, because it is external.
So the class of hyper-open sets is not closed under countable unions, and is not a topology;
it is a base for the interval topology
({lit}`Goldblatt.intervalOpen_iff_sUnion_hyperOpen`). -/
theorem not_hyperOpen_limitedSet : ¬ HyperOpen 𝕃 :=
  fun h => isExternal_limitedSet h.isInternal

/-- **Section 11.14.** The hyper-open sets form a base of the interval topology: a set of
hyperreals is interval-open if and only if it is a union of hyper-open sets. One direction
holds because open intervals are hyper-open, the other by Lemma 11.14.1. -/
theorem intervalOpen_iff_sUnion_hyperOpen {A : Set ℝ*} :
    IntervalOpen A ↔ ∃ 𝒮 : Set (Set ℝ*), (∀ S ∈ 𝒮, HyperOpen S) ∧ A = ⋃₀ 𝒮 := by
  constructor
  · intro h
    obtain ⟨𝒮, h𝒮, rfl⟩ := intervalOpen_iff_exists_sUnion.1 h
    exact ⟨𝒮, fun S hS => by obtain ⟨a, b, rfl⟩ := h𝒮 S hS; exact hyperOpen_Ioo a b, rfl⟩
  · rintro ⟨𝒮, h𝒮, rfl⟩ x ⟨S, hS, hx⟩
    obtain ⟨a, b, hx', hsub⟩ := (h𝒮 S hS).intervalOpen x hx
    exact ⟨a, b, hx', hsub.trans (subset_sUnion_of_mem hS)⟩

/-- **Exercise 11.14.2.** The union of two hyper-open sets is hyper-open. -/
theorem HyperOpen.union {X Y : Set ℝ*} (hX : HyperOpen X) (hY : HyperOpen Y) :
    HyperOpen (X ∪ Y) := by
  obtain ⟨A, rfl, hA⟩ := hX
  obtain ⟨B, rfl, hB⟩ := hY
  exact ⟨_, internalSet_union A B, (hA.and hB).mono fun n hn => hn.1.union hn.2⟩

/-- **Exercise 11.14.2.** The empty set is hyper-open. -/
theorem hyperOpen_empty : HyperOpen (∅ : Set ℝ*) :=
  ⟨fun _ => ∅, by rw [← starSet_eq_internalSet, starSet_empty],
    Eventually.of_forall fun _ => isOpen_empty⟩

/-- **Exercise 11.14.2.** The class of hyper-open sets is closed under finite unions. -/
theorem hyperOpen_biUnion_finset {ι : Type*} (s : Finset ι) {X : ι → Set ℝ*}
    (hX : ∀ i ∈ s, HyperOpen (X i)) : HyperOpen (⋃ i ∈ s, X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hyperOpen_empty
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    exact (hX a (Finset.mem_insert_self a s)).union
      (ih fun i hi => hX i (Finset.mem_insert_of_mem hi))

/-- **Exercise 11.14.3.** For an internal set $`A = [A_n]`, the set $`B = [B_n]` with $`B_n`
the interior of $`A_n` is hyper-open, hence interval-open, and is included in $`A`. -/
theorem hyperOpen_internalSet_interior (A : ℕ → Set ℝ) :
    HyperOpen (internalSet fun n => interior (A n)) :=
  ⟨_, rfl, Eventually.of_forall fun _ => isOpen_interior⟩

/-- **Exercise 11.14.3.** $`[\operatorname{int} A_n] \subseteq [A_n]`. -/
theorem internalSet_interior_subset (A : ℕ → Set ℝ) :
    (internalSet fun n => interior (A n)) ⊆ internalSet A :=
  internalSet_subset_iff.2 (Eventually.of_forall fun _ => interior_subset)

/-- **Exercise 11.14.3.** Every interval-open subset of $`[A_n]` is included in
$`[\operatorname{int} A_n]`. -/
theorem HyperTopology.IntervalOpen.subset_internalSet_interior {U : Set ℝ*} (hU : IntervalOpen U)
    {A : ℕ → Set ℝ} (hUA : U ⊆ internalSet A) : U ⊆ internalSet fun n => interior (A n) := by
  intro x hx
  obtain ⟨a, b, hxab, hab⟩ := hU x hx
  obtain ⟨a, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨b, rfl⟩ := hyperreal_exists_rep b
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  have h1 : ∀ᶠ n in hyperfilter ℕ, Ioo (a n) (b n) ⊆ A n := by
    have := hab.trans hUA
    rwa [← internalSet_Ioo, internalSet_subset_iff] at this
  have h2 : ∀ᶠ n in hyperfilter ℕ, r n ∈ Ioo (a n) (b n) := by
    rwa [← internalSet_Ioo, hyperreal_ofSeq_mem_internalSet] at hxab
  exact hyperreal_ofSeq_mem_internalSet.2 ((h1.and h2).mono fun n hn =>
    mem_interior.2 ⟨_, hn.1, isOpen_Ioo, hn.2⟩)

/-- **Exercise 11.14.3.** $`[\operatorname{int} A_n]` is the interior of $`[A_n]` in the
interval topology: it is the union of all interval-open subsets of $`[A_n]`. -/
theorem internalSet_interior_eq_sUnion (A : ℕ → Set ℝ) :
    (internalSet fun n => interior (A n)) = ⋃₀ {U | IntervalOpen U ∧ U ⊆ internalSet A} :=
  Subset.antisymm
    (subset_sUnion_of_mem ⟨(hyperOpen_internalSet_interior A).intervalOpen,
      internalSet_interior_subset A⟩)
    (sUnion_subset fun _ hU => hU.1.subset_internalSet_interior hU.2)

/-- **Exercise 11.14.3, the deduction.** An internal set is interval-open if and only if it
is hyper-open. -/
theorem IsInternal.intervalOpen_iff_hyperOpen {X : Set ℝ*} (hX : IsInternal X) :
    IntervalOpen X ↔ HyperOpen X := by
  refine ⟨fun h => ?_, HyperOpen.intervalOpen⟩
  obtain ⟨A, rfl⟩ := hX
  have e : internalSet A = internalSet fun n => interior (A n) :=
    Subset.antisymm (h.subset_internalSet_interior Subset.rfl) (internalSet_interior_subset A)
  rw [e]
  exact hyperOpen_internalSet_interior A

/-- **Section 11.14.** The set of limited numbers is S-open. -/
theorem sOpen_limitedSet : SOpen 𝕃 := by
  intro x hx
  refine ⟨x, 1, one_pos, fun y hy => ?_, fun y hy => ?_⟩
  · have := abs_lt.1 (infClose_iff_abs_lt.1 hy 1 one_pos)
    rw [Hyperreal.coe_one] at this ⊢
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  · have hy' : y ∈ Ioo (x - ((1 : ℝ) : ℝ*)) (x + ((1 : ℝ) : ℝ*)) := hy (InfClose.refl y)
    rw [Hyperreal.coe_one] at hy'
    have h1 : Limited (y - x) := limited_one.of_abs_le (by
      rw [abs_one]
      exact (abs_lt.2 ⟨by linarith [hy'.1], by linarith [hy'.2]⟩).le)
    simpa using hx.add h1

/-- **Section 11.14.** The set of limited numbers is real-open. -/
theorem realOpen_limitedSet : RealOpen 𝕃 := by
  intro x hx
  refine ⟨x, 1, one_pos, ?_, fun y hy => ?_⟩
  · rw [Hyperreal.coe_one]
    exact ⟨by linarith, by linarith⟩
  · rw [Hyperreal.coe_one] at hy
    have h1 : Limited (y - x) := limited_one.of_abs_le (by
      rw [abs_one]
      exact (abs_lt.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩).le)
    simpa using hx.add h1

/-- **Section 11.14.** An open interval of infinitesimal length is hyper-open but not
real-open. Together with the set of limited numbers, which is real-open (indeed S-open) but
not hyper-open, this shows that the two classes are incomparable, even among internal
sets. -/
theorem not_realOpen_Ioo_of_infinitesimal {a d : ℝ*} (hd0 : 0 < d) (hd : Infinitesimal d) :
    ¬ RealOpen (Ioo a (a + d)) := by
  intro h
  obtain ⟨r, e, he, -, hsub⟩ := h (a + d / 2) ⟨by linarith, by linarith⟩
  have he' : (0 : ℝ*) < (e : ℝ*) := by exact_mod_cast he
  have h1 := @hsub r ⟨by linarith, by linarith⟩
  have h2 := @hsub (r + e / 2) ⟨by linarith, by linarith⟩
  have h3 : (e : ℝ*) / 2 < d := by linarith [h1.1, h2.2]
  have h4 := infinitesimal_iff_abs_lt.1 hd (e / 2) (by positivity)
  rw [abs_of_pos hd0, Hyperreal.coe_div] at h4
  have h5 : ((2 : ℝ) : ℝ*) = 2 := rfl
  rw [h5] at h4
  linarith

/-- **Theorem 11.14.4, the easy direction.** An S-open set contains the halo of each of its
points. This does not need the set to be internal. -/
theorem HyperTopology.SOpen.hal_subset {B : Set ℝ*} (hB : SOpen B) {r : ℝ*} (hr : r ∈ B) :
    hal r ⊆ B := by
  obtain ⟨c, e, -, hrc, hsub⟩ := hB r hr
  intro y hy
  refine hsub ?_
  change hal y ⊆ _
  rw [← hal_eq_hal_iff.2 (mem_hal.1 hy)]
  exact hrc

/-- **Theorem 11.14.4.** An internal set is S-open if and only if it contains the halo of
each of its points. If the internal set $`B` contains the halo of $`r`, then by the
permanence theorem 11.9.1 (an application of underflow) it contains an interval of positive
real radius $`\varepsilon` around $`r`, and so it includes the S-neighbourhood
$`((r - \varepsilon, r + \varepsilon))`, to which $`r` belongs. -/
theorem IsInternal.sOpen_iff_forall_hal_subset {B : Set ℝ*} (hB : IsInternal B) :
    SOpen B ↔ ∀ r ∈ B, hal r ⊆ B := by
  refine ⟨fun h r hr => h.hal_subset hr, fun h r hr => ?_⟩
  obtain ⟨e, he, hball⟩ := hB.exists_real_ball_subset (h r hr)
  refine ⟨r, e, he, fun y hy => ?_, fun y hy => ?_⟩
  · have := abs_lt.1 (infClose_iff_abs_lt.1 hy e he)
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  · have hy' : y ∈ Ioo (r - (e : ℝ*)) (r + e) := hy (InfClose.refl y)
    exact hball y (abs_lt.2 ⟨by linarith [hy'.1], by linarith [hy'.2]⟩)

end HyperOpen

end Goldblatt
