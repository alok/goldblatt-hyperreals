import Goldblatt.Ch13_Universes.Internal

/-!
# 13 (part 5). Numbers in a Framework, External Images and Hyperfinite Sets

This is the last of five parts of Chapter 13 (the overview is on the chapter page
{lit}`Goldblatt.Ch13_Universes`). From Section 13.9 on the book assumes that the real numbers
are among the individuals of the framework. This part makes that assumption explicit, and
covers what depends on it: the examples of Section 13.9, the internal least number principle
and internal induction of Section 13.12, the exercises of Section 13.13, the theorem of
Section 13.14 that the image of an infinite set is external, and the theory of hyperfinite
sets and hyperfinite sums of Sections 13.17 to 13.20.
-/

noncomputable section

namespace Goldblatt

open ZFSet

universe u

/-!
## Frameworks over the real numbers

A real framework is a nonstandard framework together with a copy of the real numbers among
its individuals. The natural numbers are the images of the natural numbers of Lean, starting
from $`0`; the book's set $`\mathbb N` starts from $`1`, and where this matters (initial
segments $`\{1, \dots, n\}`) the lower bound is written out.
-/

/-- **Section 13.9, standing assumption.** A nonstandard framework for a set $`X` that
includes the real numbers: an injection of $`\mathbb R` into the set of individuals. -/
structure RealFramework extends NonstandardFramework.{u} where
  /-- The individual representing a real number. -/
  real : ℝ → ZFSet.{u}
  /-- Distinct real numbers are represented by distinct individuals. -/
  real_injective : Function.Injective real
  /-- Real numbers are individuals. -/
  real_mem : ∀ r, real r ∈ X

namespace RealFramework

open Formula Term NonstandardFramework

variable (F : RealFramework.{u}) {A B C D f a b c n x : ZFSet.{u}}

/-- The individual representing a natural number. -/
def nat (k : ℕ) : ZFSet.{u} := F.real k

/-- The set $`\mathbb R` of real numbers of the framework. -/
def R : ZFSet.{u} := ZFSet.range F.real

/-- The set $`\mathbb N` of natural numbers of the framework (starting from $`0`). -/
def N : ZFSet.{u} := ZFSet.range F.nat

/-- The order relation $`\le` on the real numbers, as a set of pairs in the universe. -/
def Le : ZFSet.{u} :=
  (prod F.R F.R).sep fun p => ∃ r s : ℝ, r ≤ s ∧ p = pair (F.real r) (F.real s)

/-- The successor relation $`\{(k, k + 1)\}` on the natural numbers. -/
def Succ : ZFSet.{u} := ZFSet.range fun k : ℕ => pair (F.nat k) (F.nat (k + 1))

theorem nat_injective : Function.Injective F.nat := fun _ _ h =>
  Nat.cast_injective (F.real_injective h)

theorem real_mem_U (r : ℝ) : F.real r ∈ F.U :=
  F.hU.subset F.isUniverseOver.base_isSetOf (F.real_mem r)

theorem nat_mem_U (k : ℕ) : F.nat k ∈ F.U := F.real_mem_U k

@[simp]
theorem star_real (r : ℝ) : F.star (F.real r) = F.real r := F.star_individual _ (F.real_mem r)

@[simp]
theorem star_nat (k : ℕ) : F.star (F.nat k) = F.nat k := F.star_real k

theorem mem_R : a ∈ F.R ↔ ∃ r, a = F.real r := by
  rw [R, mem_range]
  exact ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩

theorem mem_N : a ∈ F.N ↔ ∃ k, a = F.nat k := by
  rw [N, mem_range]
  exact ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩

theorem R_subset_base : F.R ⊆ F.X := fun a ha => by
  obtain ⟨r, rfl⟩ := F.mem_R.1 ha
  exact F.real_mem r

theorem N_subset_base : F.N ⊆ F.X := fun a ha => by
  obtain ⟨k, rfl⟩ := F.mem_N.1 ha
  exact F.real_mem k

theorem isSetOf_R : IsSetOf F.U F.R :=
  F.hU.isSetOf_of_subset F.isUniverseOver.base_isSetOf F.R_subset_base

theorem isSetOf_N : IsSetOf F.U F.N :=
  F.hU.isSetOf_of_subset F.isUniverseOver.base_isSetOf F.N_subset_base

/-- **Section 13.8/13.9.** $`\mathbb N \subseteq {}^*\mathbb N`. -/
theorem N_subset_star : F.N ⊆ F.star F.N := (F.subset_star_of_subset_base F.N_subset_base).1

/-- **Section 13.9.** $`\operatorname{im} \mathbb N = \mathbb N` and
$`\operatorname{im} \mathbb R = \mathbb R`. -/
theorem im_N_im_R : F.im F.N = F.N ∧ F.im F.R = F.R :=
  ⟨F.im_eq_of_subset_base F.N_subset_base, F.im_eq_of_subset_base F.R_subset_base⟩

/-- **Section 13.9.** All standard members of $`{}^*\mathbb N` belong to $`\mathbb N`; thus
any member of $`{}^*\mathbb N - \mathbb N` is nonstandard. -/
theorem mem_N_of_standard (hs : F.Standard a) (ha : a ∈ F.star F.N) : a ∈ F.N :=
  F.mem_of_standard_of_mem_star F.N_subset_base hs ha

theorem pair_mem_Le {r s : ℝ} : pair (F.real r) (F.real s) ∈ F.Le ↔ r ≤ s := by
  rw [Le, mem_sep]
  constructor
  · rintro ⟨-, r', s', h, he⟩
    obtain ⟨h1, h2⟩ := pair_inj.1 he
    rwa [F.real_injective h1, F.real_injective h2]
  · exact fun h => ⟨pair_mem_prod.2 ⟨F.mem_R.2 ⟨r, rfl⟩, F.mem_R.2 ⟨s, rfl⟩⟩, r, s, h, rfl⟩

theorem pair_nat_mem_Le {j k : ℕ} : pair (F.nat j) (F.nat k) ∈ F.Le ↔ j ≤ k := by
  rw [nat, nat, pair_mem_Le, Nat.cast_le]

theorem isSetOf_Le : IsSetOf F.U F.Le :=
  F.hU.isSetOf_of_subset_prod F.isSetOf_R F.isSetOf_R sep_subset

theorem mem_Succ : a ∈ F.Succ ↔ ∃ k, a = pair (F.nat k) (F.nat (k + 1)) := by
  rw [Succ, mem_range]
  exact ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩

theorem pair_mem_Succ {k : ℕ} : pair (F.nat k) b ∈ F.Succ ↔ b = F.nat (k + 1) := by
  rw [mem_Succ]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨h1, h2⟩ := pair_inj.1 hj
    rw [h2, F.nat_injective h1]
  · exact fun h => ⟨k, by rw [h]⟩

theorem isSetOf_Succ : IsSetOf F.U F.Succ :=
  F.hU.isSetOf_of_subset_prod F.isSetOf_N F.isSetOf_N fun p hp => by
    obtain ⟨k, rfl⟩ := F.mem_Succ.1 hp
    exact pair_mem_prod.2 ⟨F.mem_N.2 ⟨k, rfl⟩, F.mem_N.2 ⟨k + 1, rfl⟩⟩

/-!
## 13.12 and 13.13: internal least number principle and internal induction

A statement about all subsets of $`\mathbb N` transfers to a statement about all internal
subsets of $`{}^*\mathbb N`, by Theorem 13.12.1. Applied to the least number principle and to
induction this gives the internal versions of both, and from internal induction it follows
that $`\mathbb N` is external as soon as there is a nonstandard hypernatural.
-/

/-- **Section 13.12, internal least number principle.** Every nonempty internal subset of
$`{}^*\mathbb N` has a least element. -/
theorem internal_least (hB : F.Internal B) (hBN : B ⊆ F.star F.N) (hne : B ≠ ∅) :
    ∃ y ∈ B, ∀ z ∈ B, pair y z ∈ F.star F.Le := by
  have hBP := (F.mem_star_powerset_iff F.isSetOf_N).2 ⟨hBN, hB⟩
  have h := F.transfer
    (.all 0 (.const (powerset F.N)) (.imp (.neg (.equal (.var 0) (.const ∅)))
      (.ex 1 (.var 0) (.all 2 (.var 0) (.elem (.opair (.var 1) (.var 2)) (.const F.Le))))))
    (by simp [IsSentence, (F.hU.isSetOf_powerset F.isSetOf_N).1, F.hU.empty_mem, F.isSetOf_Le.1])
  sat_simp at h
  rw [F.star_empty] at h
  have h' := h.1 (by
    intro x _ hx hne
    rw [mem_powerset] at hx
    have hS : ∃ k, F.nat k ∈ x := by
      obtain ⟨y, hy⟩ := (eq_empty_or_nonempty x).resolve_left hne
      obtain ⟨k, rfl⟩ := F.mem_N.1 (hx hy)
      exact ⟨k, hy⟩
    classical
    refine ⟨F.nat (Nat.find hS), F.nat_mem_U _, Nat.find_spec hS, fun z _ hz => ?_⟩
    obtain ⟨k, rfl⟩ := F.mem_N.1 (hx hz)
    exact F.pair_nat_mem_Le.2 (Nat.find_min' hS hz))
  have hBU : B ⊆ F.U' := fun z hz => F.star_subset_U' F.isSetOf_N (hBN hz)
  obtain ⟨y, -, hy, hmin⟩ := h' B hB.mem_U' hBP hne
  exact ⟨y, hy, fun z hz => hmin z (hBU hz) hz⟩

/-- **Exercise 13.13 (1), internal induction (Theorem 11.3.2).** An internal subset of
$`{}^*\mathbb N` that contains the first number and is closed under successor is all of
$`{}^*\mathbb N`. -/
theorem internal_induction (hB : F.Internal B) (hBN : B ⊆ F.star F.N) (h0 : F.nat 0 ∈ B)
    (hs : ∀ y ∈ B, ∀ z ∈ F.star F.N, pair y z ∈ F.star F.Succ → z ∈ B) : B = F.star F.N := by
  have hBP := (F.mem_star_powerset_iff F.isSetOf_N).2 ⟨hBN, hB⟩
  have h := F.transfer
    (.all 0 (.const (powerset F.N)) (.imp
      (.conj (.elem (.const (F.nat 0)) (.var 0))
        (.all 1 (.var 0) (.all 2 (.const F.N)
          (.imp (.elem (.opair (.var 1) (.var 2)) (.const F.Succ)) (.elem (.var 2) (.var 0))))))
      (.all 1 (.const F.N) (.elem (.var 1) (.var 0)))))
    (by simp [IsSentence, (F.hU.isSetOf_powerset F.isSetOf_N).1, F.isSetOf_N.1, F.isSetOf_Succ.1,
      F.nat_mem_U])
  sat_simp at h
  rw [F.star_nat] at h
  have h' := h.1 (by
    rintro x - hx ⟨hx0, hxs⟩ y - hy
    rw [mem_powerset] at hx
    obtain ⟨k, rfl⟩ := F.mem_N.1 hy
    induction k with
    | zero => exact hx0
    | succ k ih =>
      exact hxs _ (F.nat_mem_U k) (ih (F.mem_N.2 ⟨k, rfl⟩)) _ (F.nat_mem_U (k + 1))
        (F.mem_N.2 ⟨k + 1, rfl⟩) (F.pair_mem_Succ.2 rfl))
  have hNU := F.star_subset_U' F.isSetOf_N
  refine le_antisymm hBN fun y hy => ?_
  exact h' B hB.mem_U' hBP ⟨h0, fun y _ hy z hz hzN hyz => hs y hy z hzN hyz⟩ y (hNU hy) hy

/-- **Section 13.12.** If $`{}^*\mathbb N - \mathbb N` is nonempty, then $`\mathbb N` is
external: it is not an internal set. -/
theorem not_internal_N (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) : ¬ F.Internal F.N := by
  intro hN
  have := F.internal_induction hN F.N_subset_star (F.mem_N.2 ⟨0, rfl⟩) (by
    intro y hy z hz hyz
    obtain ⟨k, rfl⟩ := F.mem_N.1 hy
    have h := F.transfer
      (.all 0 (.const F.N) (.imp (.elem (.opair (.const (F.nat k)) (.var 0)) (.const F.Succ))
        (.equal (.var 0) (.const (F.nat (k + 1))))))
      (by simp [IsSentence, F.isSetOf_N.1, F.isSetOf_Succ.1, F.nat_mem_U])
    sat_simp at h
    rw [F.star_nat, F.star_nat] at h
    have := h.1 (fun z _ _ hz => F.pair_mem_Succ.1 hz) z (F.star_subset_U' F.isSetOf_N hz) hz hyz
    rw [this]
    exact F.mem_N.2 ⟨k + 1, rfl⟩)
  obtain ⟨n, hn, hn'⟩ := hω
  rw [← this] at hn
  exact hn' hn

/-- **Section 13.12.** If $`{}^*\mathbb N - \mathbb N` is nonempty, then $`\mathbb N` is an
external entity, and so the internal entities are not closed under power sets:
$`\mathcal P({}^*\mathbb N)` has a member that is not internal. -/
theorem external_N (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) :
    F.External F.N ∧ F.N ∈ powerset (F.star F.N) :=
  ⟨⟨(F.isSetOf_star F.isSetOf_N).1 |> fun _ =>
      (F.isUniverse'.isSetOf_of_subset (F.isSetOf_star F.isSetOf_N) F.N_subset_star).1,
    F.not_internal_N hω⟩, mem_powerset.2 F.N_subset_star⟩

/-!
## 13.9 Initial segments of the hypernaturals

For a hypernatural $`n`, the initial segment $`\{1, \dots, n\}` of $`{}^*\mathbb N` is an
internal set: it belongs to the standard set $`{}^*\mathcal P(\mathbb N)`.
-/

/-- **Section 13.9, initial segments.** The subset
$`\{1, \dots, n\} = \{x \in {}^*\mathbb N : 1 \le x \le n\}` of $`{}^*\mathbb N`. -/
def seg (n : ZFSet.{u}) : ZFSet.{u} :=
  (F.star F.N).sep fun x => pair (F.nat 1) x ∈ F.star F.Le ∧ pair x n ∈ F.star F.Le

/-- **Section 13.9/13.10.** Every initial segment $`\{1, \dots, n\}` of the hypernaturals is
internal. -/
theorem internal_seg (hn : n ∈ F.star F.N) : F.Internal (F.seg n) := by
  have := F.internal_sep
    (.conj (.elem (.opair (.const (F.nat 1)) (.var 0)) (.const F.Le))
      (.elem (.opair (.var 0) (.var 1)) (.const F.Le))) [1] 0
    (by simp [F.nat_mem_U, F.isSetOf_Le.1]) (fun _ => n)
    (by simpa using F.internal_of_mem_star F.isSetOf_N hn) (F.internal_star F.isSetOf_N.1)
    (F.isSetOf_star F.isSetOf_N)
  sat_simp at this
  rw [F.star_nat] at this
  exact this

/-- **Section 13.9.** For every hypernatural $`n`, the set $`\{1, \dots, n\}` belongs to the
standard set $`{}^*\mathcal P(\mathbb N)`. -/
theorem seg_mem_star_powerset (hn : n ∈ F.star F.N) : F.seg n ∈ F.star (powerset F.N) :=
  (F.mem_star_powerset_iff F.isSetOf_N).2 ⟨sep_subset, F.internal_seg hn⟩

/-!
## 13.14 External Images Are External

If there is a nonstandard hypernatural, then the image of every infinite set of the universe
is external. Hence every infinite standard set has nonstandard members, and the transform of
its power set is a proper subset of the power set of its transform.
-/

/-- **Theorem 13.14.1.** If $`{}^*\mathbb N` has a nonstandard element, then the image
$`\operatorname{im} A` of any infinite set $`A \in \mathbb U` is not internal. The proof
includes **Exercise 13.14.2**: the inverse image of $`\operatorname{im} X` under
$`{}^*f`, for an injection $`f` of $`\mathbb N` into $`A` with range $`X`, is
$`\mathbb N`. -/
theorem not_internal_im (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hA : IsSetOf F.U A)
    (hinf : (A : Set ZFSet.{u}).Infinite) : ¬ F.Internal (F.im A) := by
  intro him
  let g := hinf.natEmbedding
  set fz : ZFSet.{u} := ZFSet.range fun k : ℕ => pair (F.nat k) (g k : ZFSet.{u}) with hfz
  have hmem : ∀ p, p ∈ fz ↔ ∃ k, p = pair (F.nat k) (g k) := by
    intro p
    rw [hfz, mem_range]
    exact ⟨fun ⟨k, h⟩ => ⟨k, h.symm⟩, fun ⟨k, h⟩ => ⟨k, h.symm⟩⟩
  have hgA : ∀ k, (g k : ZFSet.{u}) ∈ A := fun k => (g k).2
  have hfunc : IsFunc F.N A fz := by
    refine ⟨fun p hp => ?_, fun z hz => ?_⟩
    · obtain ⟨k, rfl⟩ := (hmem p).1 hp
      exact pair_mem_prod.2 ⟨F.mem_N.2 ⟨k, rfl⟩, hgA k⟩
    · obtain ⟨k, rfl⟩ := F.mem_N.1 hz
      refine ⟨g k, (hmem _).2 ⟨k, rfl⟩, fun w hw => ?_⟩
      obtain ⟨m, hm⟩ := (hmem _).1 hw
      obtain ⟨h1, h2⟩ := pair_inj.1 hm
      rw [h2, F.nat_injective h1]
  have hinj : IsInjective fz := by
    intro a a' b hab hab'
    obtain ⟨k, hk⟩ := (hmem _).1 hab
    obtain ⟨m, hm⟩ := (hmem _).1 hab'
    obtain ⟨rfl, h2⟩ := pair_inj.1 hk
    obtain ⟨rfl, h2'⟩ := pair_inj.1 hm
    have : g k = g m := Subtype.ext (h2.symm.trans h2')
    rw [g.injective this]
  have hfset := F.hU.isSetOf_of_isFunc F.isSetOf_N hA hfunc
  have hrel := F.hU.relIn_of_subset_prod F.isSetOf_N hA hfunc.1
  have hX₀ := F.hU.isSetOf_ran hfset hrel
  have him_set : IsSetOf F.U' (F.im A) := isSetOf_of_subset him.mem_U' fun b hb =>
    F.star_subset_U' hA (F.im_subset_star hA hb)
  have hint : F.Internal (F.im A ∩ F.star (ran fz)) :=
    F.internal_inter him him_set (F.internal_star hX₀.1)
  have hpre := F.internal_relPreimage (F.internal_star hfset.1) (F.isSetOf_star hfset)
    (F.relIn_star hfset hrel) hint
  have hstar : ∀ k, pair (F.nat k) (F.star (g k)) ∈ F.star fz := fun k => by
    have := (F.star_mem_star_iff (F.hU.isSetOf_opair (F.nat_mem_U k)
      (F.hU.subset hA (hgA k))).1 hfset.1).2 ((hmem _).2 ⟨k, rfl⟩)
    rwa [F.star_opair (F.nat_mem_U k) (F.hU.subset hA (hgA k)), F.star_nat] at this
  have hN : relPreimage (F.star fz) (F.im A ∩ F.star (ran fz)) = F.N := by
    ext x
    rw [mem_relPreimage, F.mem_N]
    constructor
    · rintro ⟨b, hb, hxb⟩
      obtain ⟨hbim, hbX⟩ := mem_inter.1 hb
      obtain ⟨a, haA, rfl⟩ := F.mem_im.1 hbim
      have haX : a ∈ ran fz := (F.star_mem_star_iff (F.hU.subset hA haA) hX₀.1).1 hbX
      obtain ⟨c, hc⟩ := mem_ran.1 haX
      obtain ⟨k, hk⟩ := (hmem _).1 hc
      obtain ⟨rfl, rfl⟩ := pair_inj.1 hk
      exact ⟨k, (F.isInjective_star_iff F.isSetOf_N hA hfunc).2 hinj _ _ _ hxb (hstar k)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨F.star (g k), mem_inter.2 ⟨F.mem_im.2 ⟨g k, hgA k, rfl⟩,
        (F.star_mem_star_iff (F.hU.subset hA (hgA k)) hX₀.1).2
          (mem_ran.2 ⟨F.nat k, (hmem _).2 ⟨k, rfl⟩⟩)⟩, hstar k⟩
  rw [hN] at hpre
  exact F.not_internal_N hω hpre

/-- **Theorem 13.14.1.** The image of an infinite set is an external entity of
$`\mathbb U'`. -/
theorem external_im (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hA : IsSetOf F.U A)
    (hinf : (A : Set ZFSet.{u}).Infinite) : F.External (F.im A) :=
  ⟨(F.isUniverse'.isSetOf_of_subset (F.isSetOf_star hA) (F.im_subset_star hA)).1,
    F.not_internal_im hω hA hinf⟩

/-- **Section 13.14.** If $`{}^*\mathbb N` has nonstandard elements, then so does $`{}^*A`
for every infinite set $`A \in \mathbb U`. -/
theorem exists_nonstandard_mem_star (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hA : IsSetOf F.U A)
    (hinf : (A : Set ZFSet.{u}).Infinite) : ∃ b, b ∈ F.star A ∧ F.Nonstandard b := by
  by_contra hcon
  push Not at hcon
  have : F.im A = F.star A := le_antisymm (F.im_subset_star hA) fun b hb =>
    (F.mem_im_iff hA).2 ⟨hb, by_contra fun hs => hcon b hb ⟨F.star_subset_U' hA hb, hs⟩⟩
  exact F.not_internal_im hω hA hinf (this ▸ F.internal_star hA.1)

/-- **Section 13.14.** If $`{}^*\mathbb N` has nonstandard elements and $`A` is infinite,
then $`{}^*\mathcal P(A)` is a proper subset of $`\mathcal P({}^*A)`: the image of $`A` is a
subset of $`{}^*A` that is not in $`{}^*\mathcal P(A)`. -/
theorem im_mem_powerset_star_sdiff (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (hA : IsSetOf F.U A)
    (hinf : (A : Set ZFSet.{u}).Infinite) :
    F.im A ∈ powerset (F.star A) ∧ F.im A ∉ F.star (powerset A) :=
  ⟨mem_powerset.2 (F.im_subset_star hA), fun h =>
    F.not_internal_im hω hA hinf ((F.mem_star_powerset_iff hA).1 h).2⟩

end RealFramework

end Goldblatt
