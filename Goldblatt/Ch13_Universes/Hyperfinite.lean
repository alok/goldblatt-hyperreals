import Goldblatt.Ch13_Universes.Internal

/-!
# 13 (part 5). Numbers in a Framework, External Images and Hyperfinite Sets

This is the fifth of six parts of Chapter 13 (the overview is on the chapter page
{lit}`Goldblatt.Ch13_Universes`). From Section 13.9 on the book assumes that the real numbers
are among the individuals of the framework. This part makes that assumption explicit, and
covers what depends on it: the examples of Section 13.9, the internal least number principle
and internal induction of Section 13.12, the exercises of Section 13.13, the theorem of
Section 13.14 that the image of an infinite set is external, and the theory of hyperfinite
sets of Sections 13.17 and 13.18. Arithmetic and hyperfinite sums (Sections 13.19 and 13.20)
are in part 6.

The sections follow the book's order with two exceptions, both forced by the order of the
proofs. Internal induction, an exercise of Section 13.13, is proved in Section 13.12 because
the proof that $`\mathbb N` is external uses it; and two exercises of Section 13.18 that do
not involve numbers are proved in Section 13.17, where later proofs of that section use them.
The parts of Sections 13.9, 13.12 and 13.13 found here, and not in parts 3 and 4, are those
that mention numbers.
-/

noncomputable section

namespace Goldblatt

open ZFSet

universe u

/-!
## 13.9 Standard Entities: the examples with numbers

From here on the book assumes that the real numbers are among the individuals. This section
makes the assumption explicit and then treats the two examples of Section 13.9, initial
segments of the hypernaturals and intervals of hyperreals.

### Frameworks over the real numbers

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

/-- **Section 13.9, consistency of the standing assumption.** There are frameworks in which
the real numbers are individuals: the trivial framework on the superstructure over a copy of
the real numbers. -/
instance : Nonempty RealFramework.{u} :=
  let ⟨ι, _, hι, h⟩ := exists_isUniverseOver (ULift.{u} ℝ)
  ⟨{ NonstandardFramework.trivial h with
      real := fun r => ι ⟨r⟩
      real_injective := fun _ _ hrs => congrArg ULift.down (hι hrs)
      real_mem := fun r => mem_range.2 ⟨⟨r⟩, rfl⟩ }⟩

theorem pair_real_mem_star_Le {r s : ℝ} :
    pair (F.real r) (F.real s) ∈ F.star F.Le ↔ r ≤ s := by
  have := F.star_mem_star_iff (F.hU.isSetOf_opair (F.real_mem_U r) (F.real_mem_U s)).1
    F.isSetOf_Le.1
  rw [F.star_opair (F.real_mem_U r) (F.real_mem_U s), F.star_real, F.star_real] at this
  rw [this, F.pair_mem_Le]

theorem pair_nat_mem_star_Le {j k : ℕ} :
    pair (F.nat j) (F.nat k) ∈ F.star F.Le ↔ j ≤ k := by
  rw [nat, nat, pair_real_mem_star_Le, Nat.cast_le]

/-- **Section 13.9.** A nonstandard hypernatural is greater than every natural number. -/
theorem nat_le_of_nonstandard (hn : n ∈ F.star F.N) (hnN : n ∉ F.N) (k : ℕ) :
    pair (F.nat k) n ∈ F.star F.Le := by
  set C := F.N.sep fun x => pair x (F.nat k) ∈ F.Le with hC
  have hCN : C ⊆ F.N := sep_subset
  have hCset := F.hU.isSetOf_of_subset F.isSetOf_N hCN
  have hCfin : (C : Set ZFSet.{u}).Finite := by
    refine ((Set.finite_Iic k).image F.nat).subset fun x hx => ?_
    obtain ⟨hxN, hxk⟩ := mem_sep.1 hx
    obtain ⟨j, rfl⟩ := F.mem_N.1 hxN
    exact ⟨j, F.pair_nat_mem_Le.1 hxk, rfl⟩
  have hCstar : F.star C = C :=
    F.star_eq_self_of_finite_subset_base (fun x hx => F.N_subset_base (hCN hx)) hCfin
  have h := F.transfer
    (.conj (.all 0 (.const F.N) (.imp
        (.elem (.opair (.var 0) (.const (F.nat k))) (.const F.Le)) (.elem (.var 0) (.const C))))
      (.all 0 (.const F.N) (.all 1 (.const F.N) (.disj
        (.elem (.opair (.var 0) (.var 1)) (.const F.Le))
        (.elem (.opair (.var 1) (.var 0)) (.const F.Le))))))
    (by simp [IsSentence, F.isSetOf_N.1, F.isSetOf_Le.1, F.nat_mem_U, hCset.1])
  sat_simp at h
  rw [F.star_nat, hCstar] at h
  obtain ⟨h1, h2⟩ := h.1 ⟨fun x _ hx hxk => mem_sep.2 ⟨hx, hxk⟩, fun x _ hx y _ hy => by
    obtain ⟨i, rfl⟩ := F.mem_N.1 hx
    obtain ⟨j, rfl⟩ := F.mem_N.1 hy
    rcases le_total i j with h | h
    · exact Or.inl (F.pair_nat_mem_Le.2 h)
    · exact Or.inr (F.pair_nat_mem_Le.2 h)⟩
  have hnU := F.star_subset_U' F.isSetOf_N hn
  have hk := F.N_subset_star (F.mem_N.2 ⟨k, rfl⟩)
  rcases h2 (F.nat k) (F.star_subset_U' F.isSetOf_N hk) hk n hnU hn with h | h
  · exact h
  · exact absurd (hCN (h1 n hnU hn h)) hnN

/-!
### Initial segments of the hypernaturals

For a hypernatural $`n`, the initial segment $`\{1, \dots, n\}` of $`{}^*\mathbb N` is an
internal set: it belongs to the standard set $`{}^*\mathcal P(\mathbb N)`. It is not a
standard set when $`n` is unlimited.
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

/-- **Section 13.9.** If $`n \in {}^*\mathbb N - \mathbb N`, then the internal set
$`\{1, \dots, n\}` is not a standard set: a set $`A` whose transform contains every positive
natural number is unbounded in $`\mathbb N`, so by transfer $`{}^*A` is unbounded in
$`{}^*\mathbb N`, while $`\{1, \dots, n\}` is bounded by $`n`. -/
theorem not_standard_seg (hn : n ∈ F.star F.N) (hnN : n ∉ F.N) : ¬ F.Standard (F.seg n) := by
  rintro ⟨A, hA, hseg⟩
  have hmemA : ∀ k : ℕ, F.nat (k + 1) ∈ A := fun k => by
    have h1 : F.nat (k + 1) ∈ F.seg n := mem_sep.2 ⟨F.N_subset_star (F.mem_N.2 ⟨k + 1, rfl⟩),
      F.pair_nat_mem_star_Le.2 (Nat.le_add_left 1 k), F.nat_le_of_nonstandard hn hnN (k + 1)⟩
    rw [hseg, ← F.star_nat (k + 1)] at h1
    exact (F.star_mem_star_iff (F.nat_mem_U _) hA).1 h1
  have h := F.transfer
    (.conj (.all 0 (.const F.N) (.ex 1 (.const A) (.conj
        (.elem (.opair (.var 0) (.var 1)) (.const F.Le)) (.neg (.equal (.var 0) (.var 1))))))
      (.all 0 (.const F.N) (.all 1 (.const F.N) (.imp
        (.conj (.elem (.opair (.var 0) (.var 1)) (.const F.Le))
          (.elem (.opair (.var 1) (.var 0)) (.const F.Le))) (.equal (.var 0) (.var 1))))))
    (by simp [IsSentence, F.isSetOf_N.1, hA, F.isSetOf_Le.1])
  sat_simp at h
  obtain ⟨h1, h2⟩ := h.1 ⟨fun x _ hx => by
      obtain ⟨k, rfl⟩ := F.mem_N.1 hx
      exact ⟨F.nat (k + 1), F.nat_mem_U _, hmemA k, F.pair_nat_mem_Le.2 (Nat.le_succ k),
        fun h => by have := F.nat_injective h; omega⟩,
    fun x _ hx y _ hy hxy => by
      obtain ⟨i, rfl⟩ := F.mem_N.1 hx
      obtain ⟨j, rfl⟩ := F.mem_N.1 hy
      rw [le_antisymm (F.pair_nat_mem_Le.1 hxy.1) (F.pair_nat_mem_Le.1 hxy.2)]⟩
  have hnU := F.star_subset_U' F.isSetOf_N hn
  obtain ⟨y, hyU, hyA, hny, hne⟩ := h1 n hnU hn
  rw [← hseg] at hyA
  obtain ⟨hyN, -, hyn⟩ := mem_sep.1 hyA
  exact hne (h2 n hnU hn y hyU hyN ⟨hny, hyn⟩)

/-!
### Intervals of hyperreals

The set of open intervals of the real line is a member of the universe. Its transform
consists exactly of the open intervals of the hyperreal line with hyperreal end points; the
standard ones among them are those with real end points.
-/

/-- The open interval $`(a, b)` of a set $`S` of numbers ordered by the relation $`L`:
$`\{x \in S : a < x < b\}`, where $`a < x` means $`a \le x` and $`x \ne a`. -/
def _root_.Goldblatt.ooIn (S L a b : ZFSet.{u}) : ZFSet.{u} :=
  S.sep fun x => (pair a x ∈ L ∧ x ≠ a) ∧ (pair x b ∈ L ∧ x ≠ b)

/-- **Section 13.9.** The set $`\mathrm{Int}` of all open intervals $`(a, b)` of the real
line with real end points. -/
def Int : ZFSet.{u} :=
  ZFSet.range fun p : ℝ × ℝ => ooIn F.R F.Le (F.real p.1) (F.real p.2)

theorem mem_Int : A ∈ F.Int ↔ ∃ r s : ℝ, A = ooIn F.R F.Le (F.real r) (F.real s) := by
  rw [Int, mem_range]
  exact ⟨fun ⟨p, h⟩ => ⟨p.1, p.2, h.symm⟩, fun ⟨r, s, h⟩ => ⟨(r, s), h.symm⟩⟩

theorem isSetOf_Int : IsSetOf F.U F.Int :=
  F.hU.isSetOf_of_subset (F.hU.isSetOf_powerset F.isSetOf_R) fun A hA => by
    obtain ⟨r, s, rfl⟩ := F.mem_Int.1 hA
    exact mem_powerset.2 sep_subset

/-- **Section 13.9.** The transform of the real interval $`(a, b)` is the hyperreal interval
with the same end points: $`{}^*(a, b) = \{x \in {}^*\mathbb R : a < x < b\}`. So it has
nonstandard elements as soon as $`{}^*\mathbb R` has elements infinitely close to a point of
it. -/
theorem star_ooIn (r s : ℝ) :
    F.star (ooIn F.R F.Le (F.real r) (F.real s)) =
      ooIn (F.star F.R) (F.star F.Le) (F.real r) (F.real s) := by
  ext x
  have := F.mem_star_sep F.isSetOf_R
    (.conj (.conj (.elem (.opair (.const (F.real r)) (.var 0)) (.const F.Le))
        (.neg (.equal (.var 0) (.const (F.real r)))))
      (.conj (.elem (.opair (.var 0) (.const (F.real s))) (.const F.Le))
        (.neg (.equal (.var 0) (.const (F.real s))))))
    (by simp [F.real_mem_U, F.isSetOf_Le.1]) (C := ooIn F.R F.Le (F.real r) (F.real s))
    (by intro a; sat_simp; rw [ooIn, mem_sep]) x
  sat_simp at this
  rw [F.star_real, F.star_real] at this
  rw [this, ooIn, mem_sep]

/-- **Section 13.9.** The standard set $`{}^*\mathrm{Int}` consists precisely of the
hyperreal intervals $`(a, b) \subseteq {}^*\mathbb R` for all $`a, b \in {}^*\mathbb R`. -/
theorem mem_star_Int :
    A ∈ F.star F.Int ↔
      ∃ a ∈ F.star F.R, ∃ b ∈ F.star F.R, A = ooIn (F.star F.R) (F.star F.Le) a b := by
  have hI := F.isSetOf_Int
  have hRU := F.star_subset_U' F.isSetOf_R
  have h := F.transfer
    (.conj
      (.all 0 (.const F.Int) (.ex 1 (.const F.R) (.ex 2 (.const F.R) (.all 3 (.const F.R)
        (.biimp (.elem (.var 3) (.var 0))
          (.conj (.conj (.elem (.opair (.var 1) (.var 3)) (.const F.Le))
              (.neg (.equal (.var 3) (.var 1))))
            (.conj (.elem (.opair (.var 3) (.var 2)) (.const F.Le))
              (.neg (.equal (.var 3) (.var 2))))))))))
      (.all 1 (.const F.R) (.all 2 (.const F.R) (.ex 0 (.const F.Int) (.all 3 (.const F.R)
        (.biimp (.elem (.var 3) (.var 0))
          (.conj (.conj (.elem (.opair (.var 1) (.var 3)) (.const F.Le))
              (.neg (.equal (.var 3) (.var 1))))
            (.conj (.elem (.opair (.var 3) (.var 2)) (.const F.Le))
              (.neg (.equal (.var 3) (.var 2)))))))))))
    (by simp [IsSentence, hI.1, F.isSetOf_R.1, F.isSetOf_Le.1])
  sat_simp at h
  obtain ⟨h1, h2⟩ := h.1 ⟨fun A _ hA => by
      obtain ⟨r, s, rfl⟩ := F.mem_Int.1 hA
      refine ⟨F.real r, F.real_mem_U r, F.mem_R.2 ⟨r, rfl⟩, F.real s, F.real_mem_U s,
        F.mem_R.2 ⟨s, rfl⟩, fun x _ hx => ?_⟩
      rw [ooIn, mem_sep]
      exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩,
    fun a _ ha b _ hb => by
      obtain ⟨r, rfl⟩ := F.mem_R.1 ha
      obtain ⟨s, rfl⟩ := F.mem_R.1 hb
      refine ⟨ooIn F.R F.Le (F.real r) (F.real s),
        F.hU.subset hI (F.mem_Int.2 ⟨r, s, rfl⟩), F.mem_Int.2 ⟨r, s, rfl⟩, fun x _ hx => ?_⟩
      rw [ooIn, mem_sep]
      exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩⟩
  have hsub : ∀ A, A ∈ F.star F.Int → A ⊆ F.star F.R := fun A hA =>
    mem_powerset.1 (F.star_powerset_subset F.isSetOf_R
      ((F.star_subset_star_iff hI (F.hU.isSetOf_powerset F.isSetOf_R)).2 (fun B hB => by
        obtain ⟨r, s, rfl⟩ := F.mem_Int.1 hB
        exact mem_powerset.2 sep_subset) hA))
  have hext : ∀ A a b, A ⊆ F.star F.R → (∀ x ∈ F.U', x ∈ F.star F.R → (x ∈ A ↔
      (pair a x ∈ F.star F.Le ∧ ¬x = a) ∧ pair x b ∈ F.star F.Le ∧ ¬x = b)) →
      A = ooIn (F.star F.R) (F.star F.Le) a b := fun A a b hA hx => by
    ext x
    rw [ooIn, mem_sep]
    exact ⟨fun h => ⟨hA h, (hx x (hRU (hA h)) (hA h)).1 h⟩, fun h => (hx x (hRU h.1) h.1).2 h.2⟩
  constructor
  · intro hA
    obtain ⟨a, -, ha, b, -, hb, hx⟩ := h1 A (F.star_subset_U' hI hA) hA
    exact ⟨a, ha, b, hb, hext A a b (hsub A hA) hx⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨A, -, hA, hx⟩ := h2 a (hRU ha) ha b (hRU hb) hb
    rw [← hext A a b (hsub A hA) hx]
    exact hA

/-- **Exercise 13.9.1.** The standard elements of $`{}^*\mathrm{Int}` are exactly the
hyperreal intervals $`\{x \in {}^*\mathbb R : r < x < s\}` with real end points
$`r, s`. -/
theorem standard_mem_star_Int_iff :
    (A ∈ F.star F.Int ∧ F.Standard A) ↔
      ∃ r s : ℝ, A = ooIn (F.star F.R) (F.star F.Le) (F.real r) (F.real s) := by
  rw [← F.mem_im_iff F.isSetOf_Int, mem_im]
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨r, s, rfl⟩ := F.mem_Int.1 hB
    exact ⟨r, s, F.star_ooIn r s⟩
  · rintro ⟨r, s, rfl⟩
    exact ⟨_, F.mem_Int.2 ⟨r, s, rfl⟩, (F.star_ooIn r s).symm⟩

/-!
## 13.10 Internal Entities: the examples

Section 13.10 returns to the two examples: initial segments and hyperreal intervals are
internal because they belong to the standard sets $`{}^*\mathcal P(\mathbb N)` and
$`{}^*\mathrm{Int}`. For initial segments this is {lit}`RealFramework.internal_seg` above. The
third example of that section, the uniform partitions, needs arithmetic and is in part 6.
-/

/-- **Section 13.10.** Every open hyperreal interval $`\{x \in {}^*\mathbb R : a < x < b\}`
with hyperreal end points $`a, b` is internal, since it belongs to
$`{}^*\mathrm{Int}`. -/
theorem internal_ooIn (ha : a ∈ F.star F.R) (hb : b ∈ F.star F.R) :
    F.Internal (ooIn (F.star F.R) (F.star F.Le) a b) :=
  F.internal_of_mem_star F.isSetOf_Int (F.mem_star_Int.2 ⟨a, ha, b, hb, rfl⟩)

/-!
## 13.12 Transformed Power Sets: the natural numbers

A statement about all subsets of $`\mathbb N` transfers to a statement about all internal
subsets of $`{}^*\mathbb N`, by Theorem 13.12.1. Applied to the least number principle this
gives the internal least number principle of Section 13.12. The same section observes that
$`\mathbb N` is external as soon as there is a nonstandard hypernatural; the proof given
here goes through internal induction, the first exercise of Section 13.13, which is therefore
proved in this section.
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
## 13.13 Exercises on Internal Sets and Functions

The first exercise asks for internal induction (proved above, because the externality of
$`\mathbb N` uses it) and internal order-completeness. The second and third describe the
transforms of a power set and of a set of functions.
-/

/-- **Exercise 13.13 (1), internal order-completeness (Theorem 11.5.1).** Every nonempty
internal subset of $`{}^*\mathbb R` that has an upper bound in $`{}^*\mathbb R` has a least
upper bound in $`{}^*\mathbb R`. -/
theorem internal_order_complete (hB : F.Internal B) (hBR : B ⊆ F.star F.R) (hne : B ≠ ∅)
    (hbdd : ∃ b ∈ F.star F.R, ∀ y ∈ B, pair y b ∈ F.star F.Le) :
    ∃ s ∈ F.star F.R, (∀ y ∈ B, pair y s ∈ F.star F.Le) ∧
      ∀ b ∈ F.star F.R, (∀ y ∈ B, pair y b ∈ F.star F.Le) → pair s b ∈ F.star F.Le := by
  have hBP := (F.mem_star_powerset_iff F.isSetOf_R).2 ⟨hBR, hB⟩
  have h := F.transfer
    (.all 0 (.const (powerset F.R)) (.imp
      (.conj (.neg (.equal (.var 0) (.const ∅)))
        (.ex 1 (.const F.R) (.all 2 (.var 0) (.elem (.opair (.var 2) (.var 1)) (.const F.Le)))))
      (.ex 1 (.const F.R) (.conj
        (.all 2 (.var 0) (.elem (.opair (.var 2) (.var 1)) (.const F.Le)))
        (.all 3 (.const F.R) (.imp
          (.all 2 (.var 0) (.elem (.opair (.var 2) (.var 3)) (.const F.Le)))
          (.elem (.opair (.var 1) (.var 3)) (.const F.Le))))))))
    (by simp [IsSentence, (F.hU.isSetOf_powerset F.isSetOf_R).1, F.hU.empty_mem, F.isSetOf_Le.1,
      F.isSetOf_R.1])
  sat_simp at h
  rw [F.star_empty] at h
  have h' := h.1 (by
    rintro x - hx ⟨hne, b', -, hb', hub⟩
    rw [mem_powerset] at hx
    obtain ⟨b, rfl⟩ := F.mem_R.1 hb'
    have hxU : x ⊆ F.U := fun y hy => F.hU.subset F.isSetOf_R (hx hy)
    have hSne : {r : ℝ | F.real r ∈ x}.Nonempty := by
      obtain ⟨y, hy⟩ := (eq_empty_or_nonempty x).resolve_left hne
      obtain ⟨r, rfl⟩ := F.mem_R.1 (hx hy)
      exact ⟨r, hy⟩
    have hSbdd : BddAbove {r : ℝ | F.real r ∈ x} :=
      ⟨b, fun r hr => F.pair_mem_Le.1 (hub _ (hxU hr) hr)⟩
    have hlub := isLUB_csSup hSne hSbdd
    refine ⟨F.real (sSup {r : ℝ | F.real r ∈ x}), F.real_mem_U _, F.mem_R.2 ⟨_, rfl⟩,
      fun y _ hy => ?_, fun c' _ hc' hc => ?_⟩
    · obtain ⟨r, rfl⟩ := F.mem_R.1 (hx hy)
      exact F.pair_mem_Le.2 (hlub.1 hy)
    · obtain ⟨c, rfl⟩ := F.mem_R.1 hc'
      exact F.pair_mem_Le.2 (hlub.2 fun r hr => F.pair_mem_Le.1 (hc _ (hxU hr) hr)))
  have hRU := F.star_subset_U' F.isSetOf_R
  have hBU : B ⊆ F.U' := fun y hy => hRU (hBR hy)
  obtain ⟨b, hb, hub⟩ := hbdd
  obtain ⟨s, -, hs, h1, h2⟩ := h' B hB.mem_U' hBP
    ⟨hne, b, hRU hb, hb, fun y _ hy => hub y hy⟩
  exact ⟨s, hs, fun y hy => h1 y (hBU hy) hy,
    fun c hc hcub => h2 c (hRU hc) hc fun y _ hy => hcub y hy⟩

end RealFramework

/-!
### Power sets and function spaces

The second and third exercises of Section 13.13 do not involve numbers and are proved for
arbitrary frameworks. Subsets of $`A` correspond to functions from $`A` to a two-element set,
and under this correspondence the members of $`{}^*\mathcal P(A)` are the internal functions
from $`{}^*A` to that set. More generally, the transform of the set of all functions from
$`A` to $`B` is the set of all internal functions from $`{}^*A` to $`{}^*B`.
-/

/-- **Exercise 13.13 (2), the two-element set.** The set $`\{0, 1\}`, with the numerals
$`0 = \emptyset` and $`1 = \{\emptyset\}`. -/
def two : ZFSet.{u} := {num 0, num 1}

/-- **Exercise 13.13 (2), characteristic functions.** The characteristic function of
$`B` on $`A`: the set of pairs $`(a, 1)` with $`a \in B` and $`(a, 0)` with
$`a \in A - B`. -/
def chi (A B : ZFSet.{u}) : ZFSet.{u} := prod B {num 1} ∪ prod (A \ B) {num 0}

theorem num_zero_ne_one : (num 0 : ZFSet.{u}) ≠ num 1 := fun h => by
  have := num_injective h
  omega

theorem pair_mem_chi {A B a c : ZFSet.{u}} :
    pair a c ∈ chi A B ↔ (a ∈ B ∧ c = num 1) ∨ (a ∈ A ∧ a ∉ B ∧ c = num 0) := by
  simp [chi, and_assoc]

theorem chi_subset {A B : ZFSet.{u}} (hBA : B ⊆ A) : chi A B ⊆ prod A two := by
  intro p hp
  rcases mem_union.1 hp with hp | hp
  · obtain ⟨a, ha, c, hc, rfl⟩ := mem_prod.1 hp
    exact pair_mem_prod.2 ⟨hBA ha, by rw [mem_singleton.1 hc]; simp [two]⟩
  · obtain ⟨a, ha, c, hc, rfl⟩ := mem_prod.1 hp
    exact pair_mem_prod.2 ⟨(mem_sdiff.1 ha).1, by rw [mem_singleton.1 hc]; simp [two]⟩

/-- **Exercise 13.13 (2).** The characteristic function of a subset of $`A` is a function
from $`A` to $`\{0, 1\}`. -/
theorem isFunc_chi {A B : ZFSet.{u}} (hBA : B ⊆ A) : IsFunc A two (chi A B) := by
  refine ⟨chi_subset hBA, fun z hz => ?_⟩
  by_cases hzB : z ∈ B
  · refine ⟨num 1, pair_mem_chi.2 (Or.inl ⟨hzB, rfl⟩), fun w hw => ?_⟩
    rcases pair_mem_chi.1 hw with h | h
    · exact h.2
    · exact absurd hzB h.2.1
  · refine ⟨num 0, pair_mem_chi.2 (Or.inr ⟨hz, hzB, rfl⟩), fun w hw => ?_⟩
    rcases pair_mem_chi.1 hw with h | h
    · exact absurd h.1 hzB
    · exact h.2.2

/-- **Exercise 13.13 (2).** A subset is recovered from its characteristic function as the
inverse image of $`\{1\}`. -/
theorem relPreimage_chi {A B : ZFSet.{u}} : relPreimage (chi A B) {num 1} = B := by
  ext a
  rw [mem_relPreimage]
  constructor
  · rintro ⟨c, hc, hac⟩
    rw [mem_singleton.1 hc] at hac
    rcases pair_mem_chi.1 hac with h | h
    · exact h.1
    · exact absurd h.2.2.symm num_zero_ne_one
  · exact fun ha => ⟨num 1, mem_singleton.2 rfl, pair_mem_chi.2 (Or.inl ⟨ha, rfl⟩)⟩

/-- **Exercise 13.13 (2).** Every function from $`A` to $`\{0, 1\}` is the characteristic
function of the inverse image of $`\{1\}`. -/
theorem chi_relPreimage {A g : ZFSet.{u}} (hg : IsFunc A two g) :
    chi A (relPreimage g {num 1}) = g := by
  have hpre : ∀ a, a ∈ relPreimage g {num 1} ↔ pair a (num 1) ∈ g := fun a => by
    rw [mem_relPreimage]
    exact ⟨fun ⟨c, hc, h⟩ => mem_singleton.1 hc ▸ h, fun h => ⟨_, mem_singleton.2 rfl, h⟩⟩
  have htwo : ∀ w, w ∈ (two : ZFSet.{u}) → w = num 0 ∨ w = num 1 := fun w hw => by
    simpa [two] using hw
  ext p
  constructor
  · intro hp
    obtain ⟨a, -, c, -, rfl⟩ := mem_prod.1 (chi_subset (A := A) (fun a ha => by
      obtain ⟨c, -, hac⟩ := mem_relPreimage.1 ha
      exact (pair_mem_prod.1 (hg.1 hac)).1) hp)
    rcases pair_mem_chi.1 hp with ⟨ha, rfl⟩ | ⟨haA, ha, rfl⟩
    · exact (hpre a).1 ha
    · obtain ⟨w, hw, -⟩ := hg.2 a haA
      rcases htwo w (pair_mem_prod.1 (hg.1 hw)).2 with rfl | rfl
      · exact hw
      · exact absurd ((hpre a).2 hw) ha
  · intro hp
    obtain ⟨a, haA, w, hw, rfl⟩ := mem_prod.1 (hg.1 hp)
    rcases htwo w hw with rfl | rfl
    · refine pair_mem_chi.2 (Or.inr ⟨haA, fun ha => ?_, rfl⟩)
      exact num_zero_ne_one (hg.isFunction.2 a _ _ hp ((hpre a).1 ha))
    · exact pair_mem_chi.2 (Or.inl ⟨(hpre a).2 hp, rfl⟩)

/-- **Exercise 13.13 (2), standard part.** $`\mathcal P(A)` is in bijective correspondence
with the set of all functions $`f : A \to \{0, 1\}`, by taking characteristic functions. -/
theorem bijOn_chi (A : ZFSet.{u}) :
    Set.BijOn (chi A) (powerset A : Set ZFSet.{u}) (funs A two : Set ZFSet.{u}) := by
  refine ⟨fun B hB => mem_funs.2 (isFunc_chi (mem_powerset.1 hB)), fun B _ B' _ h => ?_,
    fun g hg => ?_⟩
  · rw [← relPreimage_chi (A := A) (B := B), ← relPreimage_chi (A := A) (B := B'), h]
  · have hg' := mem_funs.1 hg
    refine ⟨relPreimage g {num 1}, mem_powerset.2 fun a ha => ?_, chi_relPreimage hg'⟩
    obtain ⟨c, -, hac⟩ := mem_relPreimage.1 ha
    exact (pair_mem_prod.1 (hg'.1 hac)).1

namespace NonstandardFramework

variable (F : NonstandardFramework.{u}) {A B : ZFSet.{u}}

/-- **Exercise 13.13 (2).** $`{}^*\mathcal P(A)` is in bijective correspondence with the set
of all internal functions $`f : {}^*A \to \{0, 1\}`, again by taking characteristic
functions. -/
theorem bijOn_chi_star (hA : IsSetOf F.U A) :
    Set.BijOn (chi (F.star A)) (F.star (powerset A) : Set ZFSet.{u})
      {g | IsFunc (F.star A) two g ∧ F.Internal g} := by
  have hone : F.Internal ({num 1} : ZFSet.{u}) := by
    have := F.internal_singleton (F.internal_star (F.hU.isSetOf_num 1).1)
    rwa [F.star_num] at this
  have hzero : F.Internal ({num 0} : ZFSet.{u}) := by
    have := F.internal_singleton (F.internal_star (F.hU.isSetOf_num 0).1)
    rwa [F.star_num] at this
  have hnumU : ∀ k, (num k : ZFSet.{u}) ∈ F.U' := fun k => (F.isUniverse'.isSetOf_num k).1
  have hAU := F.star_subset_U' hA
  refine ⟨fun B hB => ?_, fun B _ B' _ h => ?_, fun g hg => ?_⟩
  · obtain ⟨hBA, hBint⟩ := (F.mem_star_powerset_iff hA).1 hB
    have hBset : IsSetOf F.U' B := isSetOf_of_subset hBint.mem_U' fun y hy => hAU (hBA hy)
    have hD := F.internal_sdiff (F.internal_star hA.1) (F.isSetOf_star hA) hBint
    have hDset : IsSetOf F.U' (F.star A \ B) :=
      F.isUniverse'.isSetOf_sdiff (F.isSetOf_star hA)
    have h1 := F.internal_prod hBint hBset hone (F.isUniverse'.isSetOf_singleton (hnumU 1))
    have h2 := F.internal_prod hD hDset hzero (F.isUniverse'.isSetOf_singleton (hnumU 0))
    have hsub : ∀ {S c : ZFSet.{u}}, S ⊆ F.U' → c ∈ F.U' → prod S {c} ⊆ F.U' :=
      fun hS hc p hp => by
        obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 hp
        rw [mem_singleton.1 hb]
        exact (F.isUniverse'.isSetOf_opair (hS ha) hc).1
    exact ⟨isFunc_chi hBA, F.internal_union h1
      (isSetOf_of_subset h1.mem_U' (hsub (F.isUniverse'.subset hBset) (hnumU 1))) h2
      (isSetOf_of_subset h2.mem_U' (hsub (F.isUniverse'.subset hDset) (hnumU 0)))⟩
  · rw [← relPreimage_chi (A := F.star A) (B := B), ← relPreimage_chi (A := F.star A) (B := B'),
      h]
  · obtain ⟨hfunc, hint⟩ := hg
    have hrel : RelIn F.U' g := fun p hp => by
      obtain ⟨a, ha, w, hw, rfl⟩ := mem_prod.1 (hfunc.1 hp)
      refine ⟨a, hAU ha, w, ?_, rfl⟩
      have : w = num 0 ∨ w = num 1 := by simpa [two] using hw
      rcases this with rfl | rfl
      · exact hnumU 0
      · exact hnumU 1
    have hgset : IsSetOf F.U' g := isSetOf_of_subset hint.mem_U' fun p hp => by
      obtain ⟨a, ha, b, hb, rfl⟩ := hrel p hp
      exact (F.isUniverse'.isSetOf_opair ha hb).1
    refine ⟨relPreimage g {num 1}, ?_, chi_relPreimage hfunc⟩
    refine (F.mem_star_powerset_iff hA).2 ⟨fun a ha => ?_,
      F.internal_relPreimage hint hgset hrel hone⟩
    obtain ⟨c, -, hac⟩ := mem_relPreimage.1 ha
    exact (pair_mem_prod.1 (hfunc.1 hac)).1

/-- A function between two sets, written with quantifiers bounded by those sets. -/
theorem _root_.Goldblatt.isFunc_iff_bounded {V g : ZFSet.{u}} (hA : A ⊆ V) (hB : B ⊆ V)
    (hg : g ⊆ prod A B) :
    IsFunc A B g ↔ (∀ a ∈ V, a ∈ A → ∃ b ∈ V, b ∈ B ∧ pair a b ∈ g) ∧
      ∀ a ∈ V, a ∈ A → ∀ b ∈ V, b ∈ B → ∀ c ∈ V, c ∈ B →
        pair a b ∈ g ∧ pair a c ∈ g → b = c := by
  constructor
  · intro h
    obtain ⟨-, -, h2, h3⟩ := isFunc_iff.1 h
    exact ⟨fun a _ ha => let ⟨b, hb, hab⟩ := h3 a ha; ⟨b, hB hb, hb, hab⟩,
      fun a _ _ b _ _ c _ _ hbc => h2 a b c hbc.1 hbc.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨hg, fun a ha => ?_⟩
    obtain ⟨b, -, hb, hab⟩ := h1 a (hA ha) ha
    refine ⟨b, hab, fun c hc => ?_⟩
    have hc' := (pair_mem_prod.1 (hg hc)).2
    exact h2 a (hA ha) ha c (hB hc') hc' b (hB hb) hb ⟨hc, hab⟩

/-- **Exercise 13.13 (3).** If $`A, B \in \mathbb U`, then $`{}^*(B^A)` is the set of all
internal functions from $`{}^*A` to $`{}^*B`. -/
theorem mem_star_funs_iff {g : ZFSet.{u}} (hA : IsSetOf F.U A) (hB : IsSetOf F.U B) :
    g ∈ F.star (funs A B) ↔ IsFunc (F.star A) (F.star B) g ∧ F.Internal g := by
  have hP := F.hU.isSetOf_prod hA hB
  have hPP := F.hU.isSetOf_powerset hP
  have hfuns := F.hU.isSetOf_funs hA hB
  have h := F.transfer
    (.all 0 (.const (powerset (prod A B))) (.biimp (.elem (.var 0) (.const (funs A B)))
      (.conj (.all 1 (.const A) (.ex 2 (.const B) (.elem (.opair (.var 1) (.var 2)) (.var 0))))
        (.all 1 (.const A) (.all 2 (.const B) (.all 3 (.const B) (.imp
          (.conj (.elem (.opair (.var 1) (.var 2)) (.var 0))
            (.elem (.opair (.var 1) (.var 3)) (.var 0)))
          (.equal (.var 2) (.var 3)))))))))
    (by simp [Formula.IsSentence, hPP.1, hfuns.1, hA.1, hB.1])
  sat_simp at h
  have h' := h.1 fun g _ hg => by
    rw [mem_funs, isFunc_iff_bounded (F.hU.subset hA) (F.hU.subset hB) (mem_powerset.1 hg)]
  have key : ∀ g, g ∈ F.star (powerset (prod A B)) →
      (g ∈ F.star (funs A B) ↔ IsFunc (F.star A) (F.star B) g) := fun g hg => by
    have hsub : g ⊆ prod (F.star A) (F.star B) := by
      rw [← F.star_prod hA hB]
      exact mem_powerset.1 (F.star_powerset_subset hP hg)
    rw [isFunc_iff_bounded (F.star_subset_U' hA) (F.star_subset_U' hB) hsub]
    exact h' g (F.star_subset_U' hPP hg) hg
  constructor
  · intro hg
    have hgP := (F.star_subset_star_iff hfuns hPP).2 (fun x hx => (mem_sep.1 hx).1) hg
    exact ⟨(key g hgP).1 hg, F.internal_of_mem_star hfuns hg⟩
  · rintro ⟨hfunc, hint⟩
    have hgP : g ∈ F.star (powerset (prod A B)) :=
      (F.mem_star_powerset_iff hP).2 ⟨by rw [F.star_prod hA hB]; exact hfunc.1, hint⟩
    exact (key g hgP).2 hfunc

end NonstandardFramework

namespace RealFramework

open Formula Term NonstandardFramework

variable (F : RealFramework.{u}) {A B C D f a b c n x : ZFSet.{u}}

/-!
## 13.14 External Images Are External

If there is a nonstandard hypernatural, then the image of every infinite set of the universe
is external. Hence every infinite standard set has nonstandard members, and the transform of
its power set is a proper subset of the power set of its transform.
-/

/-- **Section 13.14.** For sets $`C \subseteq A` of the universe, the standard members of
$`{}^*C` among the images of members of $`A` are the images of members of $`C`:
$`\operatorname{im} A \cap {}^*C = \operatorname{im} C`. -/
theorem im_inter_star (hA : IsSetOf F.U A) (hCA : C ⊆ A) :
    F.im A ∩ F.star C = F.im C := by
  have hC := F.hU.isSetOf_of_subset hA hCA
  ext b
  rw [mem_inter, F.mem_im, F.mem_im]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hb⟩
    exact ⟨a, (F.star_mem_star_iff (F.hU.subset hA ha) hC.1).1 hb, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, hCA ha, rfl⟩, (F.star_mem_star_iff (F.hU.subset hC ha) hC.1).2 ha⟩

/-- **Exercise 13.14.2.** Let $`f` be an injection of $`\mathbb N` into a set $`A` of the
universe, with range $`X`. Then the inverse image of $`\operatorname{im} X` under the
transform of $`f` is $`\mathbb N`: $`({}^*f)^{-1}(\operatorname{im} X) = \mathbb N`. -/
theorem relPreimage_star_im_ran (hA : IsSetOf F.U A) (hfunc : IsFunc F.N A f)
    (hinj : IsInjective f) : relPreimage (F.star f) (F.im (ran f)) = F.N := by
  have hfset := F.hU.isSetOf_of_isFunc F.isSetOf_N hA hfunc
  have hstar : ∀ k, pair (F.nat k) (F.star (app f (F.nat k))) ∈ F.star f := fun k => by
    have hmem := hfunc.isFunction.pair_app_mem (hfunc.dom_eq ▸ F.mem_N.2 ⟨k, rfl⟩)
    have hb := F.hU.subset hA (pair_mem_prod.1 (hfunc.1 hmem)).2
    have := (F.star_mem_star_iff (F.hU.isSetOf_opair (F.nat_mem_U k) hb).1 hfset.1).2 hmem
    rwa [F.star_opair (F.nat_mem_U k) hb, F.star_nat] at this
  ext x
  rw [mem_relPreimage, F.mem_N]
  constructor
  · rintro ⟨b, hb, hxb⟩
    obtain ⟨a, ha, rfl⟩ := F.mem_im.1 hb
    obtain ⟨c, hc⟩ := mem_ran.1 ha
    obtain ⟨k, rfl⟩ := F.mem_N.1 (pair_mem_prod.1 (hfunc.1 hc)).1
    have hk := hstar k
    rw [hfunc.isFunction.app_eq hc] at hk
    exact ⟨k, (F.isInjective_star_iff F.isSetOf_N hA hfunc).2 hinj _ _ _ hxb hk⟩
  · rintro ⟨k, rfl⟩
    have hmem := hfunc.isFunction.pair_app_mem (hfunc.dom_eq ▸ F.mem_N.2 ⟨k, rfl⟩)
    exact ⟨_, F.mem_im.2 ⟨_, mem_ran.2 ⟨_, hmem⟩, rfl⟩, hstar k⟩

/-- **Theorem 13.14.1.** If $`{}^*\mathbb N` has a nonstandard element, then the image
$`\operatorname{im} A` of any infinite set $`A \in \mathbb U` is not internal. As in the
book, an injection $`f` of $`\mathbb N` into $`A` with range $`X` is chosen; if
$`\operatorname{im} A` were internal, so would be
$`\operatorname{im} X = \operatorname{im} A \cap {}^*X` and its inverse image under
$`{}^*f`, which is $`\mathbb N` by Exercise 13.14.2. -/
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
  rw [F.im_inter_star hA hfunc.ran_subset, F.relPreimage_star_im_ran hA hfunc hinj] at hpre
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

/-!
## 13.17 Hyperfiniteness

For a set $`A` of the universe, $`\mathcal P_F(A)` is the set of its finite subsets. The
members of $`{}^*\mathcal P_F(A)` are the hyperfinite subsets of $`{}^*A`; each is an internal
subset of $`{}^*A`, but in general not a finite one. Theorem 13.17.1 characterizes the
hyperfinite sets as those in internal bijection with an initial segment
$`\{1, \dots, n\}` of the hypernaturals.
-/

/-- **Section 13.17.** The set $`\mathcal P_F(A) = \{B \subseteq A : B \text{ is finite}\}`
of all finite subsets of $`A`. -/
def finPow (A : ZFSet.{u}) : ZFSet.{u} :=
  (powerset A).sep fun B => (B : Set ZFSet.{u}).Finite

theorem mem_finPow {A B : ZFSet.{u}} : B ∈ finPow A ↔ B ⊆ A ∧ (B : Set ZFSet.{u}).Finite := by
  rw [finPow, mem_sep, mem_powerset]

/-- **Section 13.17.** If $`A \in \mathbb U` then $`\mathcal P_F(A) \in \mathbb U`. -/
theorem IsUniverse.isSetOf_finPow {U A : ZFSet.{u}} (hU : IsUniverse U) (hA : IsSetOf U A) :
    IsSetOf U (finPow A) :=
  hU.isSetOf_sep (hU.isSetOf_powerset hA) _

namespace NonstandardFramework

variable (F : NonstandardFramework.{u}) {A B : ZFSet.{u}}

/-- **Section 13.17, hyperfinite sets.** A set is hyperfinite when it belongs to
$`{}^*\mathcal P_F(A)` for some set $`A \in \mathbb U`. -/
def Hyperfinite (B : ZFSet.{u}) : Prop := ∃ A, IsSetOf F.U A ∧ B ∈ F.star (finPow A)

/-- **Section 13.17.** $`{}^*\mathcal P_F(A) \subseteq {}^*\mathcal P(A) \subseteq
\mathcal P({}^*A)`. -/
theorem star_finPow_subset (hA : IsSetOf F.U A) :
    F.star (finPow A) ⊆ F.star (powerset A) ∧ F.star (powerset A) ⊆ powerset (F.star A) :=
  ⟨(F.star_subset_star_iff (F.hU.isSetOf_finPow hA) (F.hU.isSetOf_powerset hA)).2 sep_subset,
    F.star_powerset_subset hA⟩

/-- **Section 13.17.** Each member of $`{}^*\mathcal P_F(A)` is an internal subset of
$`{}^*A`. -/
theorem internal_subset_of_mem_star_finPow (hA : IsSetOf F.U A) (hB : B ∈ F.star (finPow A)) :
    B ⊆ F.star A ∧ F.Internal B :=
  (F.mem_star_powerset_iff hA).1 ((F.star_finPow_subset hA).1 hB)

variable {F} in
/-- A hyperfinite set is internal. -/
theorem Hyperfinite.internal (h : F.Hyperfinite B) : F.Internal B :=
  let ⟨_, hA, hB⟩ := h
  (F.internal_subset_of_mem_star_finPow hA hB).2

variable {F} in
/-- A hyperfinite set is a set of $`\mathbb U'`. -/
theorem Hyperfinite.isSetOf (h : F.Hyperfinite B) : IsSetOf F.U' B :=
  let ⟨_, hA, hB⟩ := h
  F.isSetOf_of_mem_star_powerset hA ((F.star_finPow_subset hA).1 hB)

variable {F} in
/-- A hyperfinite subset of a standard set $`{}^*C` belongs to $`{}^*\mathcal P_F(C)`. -/
theorem Hyperfinite.mem_star_finPow {C : ZFSet.{u}} (h : F.Hyperfinite B) (hC : IsSetOf F.U C)
    (hBC : B ⊆ F.star C) : B ∈ F.star (finPow C) := by
  obtain ⟨A, hA, hB⟩ := h
  have hFA := F.hU.isSetOf_finPow hA
  have hFC := F.hU.isSetOf_finPow hC
  have h := F.transfer
    (.all 0 (.const (finPow A)) (.imp (.all 1 (.var 0) (.elem (.var 1) (.const C)))
      (.elem (.var 0) (.const (finPow C)))))
    (by simp [Formula.IsSentence, hFA.1, hFC.1, hC.1])
  sat_simp at h
  exact h.1 (fun x _ hx hxC => mem_finPow.2
    ⟨fun y hy => hxC y (F.hU.subset hA ((mem_finPow.1 hx).1 hy)) hy, (mem_finPow.1 hx).2⟩)
    B (F.star_subset_U' hFA hB) hB fun y _ hy => hBC hy

variable {F} in
/-- **Exercise 13.18 (2), first part.** Any internal subset of a hyperfinite set is
hyperfinite. -/
theorem Hyperfinite.of_internal_subset (hA : F.Hyperfinite A) (hB : F.Internal B)
    (hBA : B ⊆ A) : F.Hyperfinite B := by
  obtain ⟨T, hT, hAT⟩ := hA
  have hFT := F.hU.isSetOf_finPow hT
  have hPT := F.hU.isSetOf_powerset hT
  have hAsub := (F.internal_subset_of_mem_star_finPow hT hAT).1
  have hBP := (F.mem_star_powerset_iff hT).2 ⟨fun x hx => hAsub (hBA hx), hB⟩
  have h := F.transfer
    (.all 0 (.const (finPow T)) (.all 1 (.const (powerset T))
      (.imp (.all 2 (.var 1) (.elem (.var 2) (.var 0))) (.elem (.var 1) (.const (finPow T))))))
    (by simp [Formula.IsSentence, hFT.1, hPT.1])
  sat_simp at h
  refine ⟨T, hT, h.1 ?_ A (F.star_subset_U' hFT hAT) hAT B hB.mem_U' hBP fun z _ hz => hBA hz⟩
  intro x _ hx y _ hy hyx
  rw [mem_powerset] at hy
  have hsub : y ⊆ x := fun z hz => hyx z (F.hU.subset hT (hy hz)) hz
  exact mem_finPow.2 ⟨hy, (mem_finPow.1 hx).2.subset fun z hz => hsub hz⟩

variable {F} in
/-- **Exercise 13.18 (6).** Internal images of hyperfinite sets are hyperfinite: if $`f` is
an internal function and $`B` is hyperfinite, then $`f(B)` is hyperfinite. -/
theorem Hyperfinite.relImage {f : ZFSet.{u}} (hB : F.Hyperfinite B) (hf : F.Internal f)
    (hrel : RelIn F.U' f) (hfun : IsFunction f) : F.Hyperfinite (relImage f B) := by
  have hfU' : f ⊆ F.U' := fun p hp => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hrel p hp
    exact (F.isUniverse'.isSetOf_opair ha hb).1
  have hfset : IsSetOf F.U' f := isSetOf_of_subset hf.mem_U' hfU'
  obtain ⟨T, hT, -, hsubT, hrelT⟩ := F.exists_ambient [f, B] (by simp [hf, hB.internal])
  have hfT := hrelT f (by simp) hfset hrel
  have hBT := hsubT B (by simp) hB.isSetOf
  have hTT := F.hU.isSetOf_prod hT hT
  have hPTT := F.hU.isSetOf_powerset hTT
  have hPT := F.hU.isSetOf_powerset hT
  have hFT := F.hU.isSetOf_finPow hT
  have hfP : f ∈ F.star (powerset (prod T T)) :=
    (F.mem_star_powerset_iff hTT).2 ⟨by rw [F.star_prod hT hT]; exact hfT, hf⟩
  have hBF := hB.mem_star_finPow hT hBT
  have himg := F.internal_relImage hf hfset hrel hB.internal
  have himgT : Goldblatt.relImage f B ⊆ F.star T := fun b hb => by
    obtain ⟨a, -, hab⟩ := mem_relImage.1 hb
    exact (pair_mem_prod.1 (hfT hab)).2
  have hyP := (F.mem_star_powerset_iff hT).2 ⟨himgT, himg⟩
  have h := F.transfer
    (.all 0 (.const (powerset (prod T T))) (.all 1 (.const (finPow T))
      (.all 2 (.const (powerset T)) (.imp (.conj
        (.all 3 (.const T) (.all 4 (.const T) (.all 5 (.const T) (.imp
          (.conj (.elem (.opair (.var 3) (.var 4)) (.var 0))
            (.elem (.opair (.var 3) (.var 5)) (.var 0)))
          (.equal (.var 4) (.var 5))))))
        (.all 4 (.var 2) (.ex 3 (.var 1) (.elem (.opair (.var 3) (.var 4)) (.var 0)))))
      (.elem (.var 2) (.const (finPow T)))))))
    (by simp [Formula.IsSentence, hPTT.1, hFT.1, hPT.1, hT.1])
  sat_simp at h
  refine ⟨T, hT, h.1 ?_ f hf.mem_U' hfP B hB.internal.mem_U' hBF _ himg.mem_U' hyP ⟨?_, ?_⟩⟩
  · rintro g - hg x - hx y - hy ⟨hfunc, himg⟩
    rw [mem_powerset] at hg hy
    have hg' : IsFunction g := ⟨fun p hp => let ⟨a, _, b, _, h⟩ := mem_prod.1 (hg hp); ⟨a, b, h⟩,
      fun a b c hab hac => by
        have h1 := pair_mem_prod.1 (hg hab)
        have h2 := pair_mem_prod.1 (hg hac)
        exact hfunc a (F.hU.subset hT h1.1) h1.1 b (F.hU.subset hT h1.2) h1.2 c
          (F.hU.subset hT h2.2) h2.2 ⟨hab, hac⟩⟩
    refine mem_finPow.2 ⟨hy, ((mem_finPow.1 hx).2.image (app g)).subset fun b hb => ?_⟩
    obtain ⟨a, -, hax, hab⟩ := himg b (F.hU.subset hT (hy hb)) hb
    exact ⟨a, hax, hg'.app_eq hab⟩
  · exact fun a _ _ b _ _ c _ _ h => hfun.2 a b c h.1 h.2
  · intro b _ hb
    obtain ⟨a, ha, hab⟩ := mem_relImage.1 hb
    exact ⟨a, F.star_subset_U' hT (hBT ha), ha, hab⟩

end NonstandardFramework

/-!
### The characterization by internal bijections

The proof of Theorem 13.17.1 transfers two sentences built on one formula, which says that
$`f` is a bijection from the initial segment determined by $`n` onto $`Z`. The formula and its
meaning are set up first.
-/

/-- The statement, with all quantifiers bounded and ranging over a universe $`W`, that $`V` is
the initial segment $`\{x \in N : 1 \le x \le n\}` and that $`f` is a bijection from $`V` onto
$`Z`. Its seven clauses are the seven formulas in the book's proof of Theorem 13.17.1. -/
def BijSpec (W N' Le' one V Z n f : ZFSet.{u}) : Prop :=
  (∀ x ∈ W, x ∈ V → x ∈ N' ∧ pair one x ∈ Le' ∧ pair x n ∈ Le') ∧
  (∀ x ∈ W, x ∈ N' → pair one x ∈ Le' ∧ pair x n ∈ Le' → x ∈ V) ∧
  (∀ b ∈ W, b ∈ f → ∃ x ∈ W, x ∈ V ∧ ∃ y ∈ W, y ∈ Z ∧ b = pair x y) ∧
  (∀ x ∈ W, x ∈ V → ∀ y ∈ W, y ∈ Z → ∀ z ∈ W, z ∈ Z →
    pair x y ∈ f ∧ pair x z ∈ f → y = z) ∧
  (∀ x ∈ W, x ∈ V → ∃ y ∈ W, y ∈ Z ∧ pair x y ∈ f) ∧
  (∀ y ∈ W, y ∈ Z → ∃ x ∈ W, x ∈ V ∧ pair x y ∈ f) ∧
  (∀ x ∈ W, x ∈ V → ∀ y ∈ W, y ∈ V → ∀ z ∈ W, z ∈ Z →
    pair x z ∈ f ∧ pair y z ∈ f → x = y)

/-- The formula $`\varphi(n, f, Z)` of the proof of Theorem 13.17.1: there is
$`V \in \mathcal P(\mathbb N)` such that $`V = \{1, \dots, n\}` and $`f` is a bijection from
$`V` onto $`Z`. The variables $`0, 1, 2` stand for $`Z, n, f`. -/
def bijFormula (PN N' Le' one : ZFSet.{u}) : Formula.{u} :=
  .ex 3 (.const PN) (.conj
    (.all 4 (.var 3) (.conj (.elem (.var 4) (.const N'))
      (.conj (.elem (.opair (.const one) (.var 4)) (.const Le'))
        (.elem (.opair (.var 4) (.var 1)) (.const Le')))))
    (.conj (.all 4 (.const N') (.imp
        (.conj (.elem (.opair (.const one) (.var 4)) (.const Le'))
          (.elem (.opair (.var 4) (.var 1)) (.const Le')))
        (.elem (.var 4) (.var 3))))
    (.conj (.all 4 (.var 2) (.ex 5 (.var 3) (.ex 6 (.var 0)
        (.equal (.var 4) (.opair (.var 5) (.var 6))))))
    (.conj (.all 4 (.var 3) (.all 5 (.var 0) (.all 6 (.var 0) (.imp
        (.conj (.elem (.opair (.var 4) (.var 5)) (.var 2))
          (.elem (.opair (.var 4) (.var 6)) (.var 2)))
        (.equal (.var 5) (.var 6))))))
    (.conj (.all 4 (.var 3) (.ex 5 (.var 0) (.elem (.opair (.var 4) (.var 5)) (.var 2))))
    (.conj (.all 5 (.var 0) (.ex 4 (.var 3) (.elem (.opair (.var 4) (.var 5)) (.var 2))))
      (.all 4 (.var 3) (.all 5 (.var 3) (.all 6 (.var 0) (.imp
        (.conj (.elem (.opair (.var 4) (.var 6)) (.var 2))
          (.elem (.opair (.var 5) (.var 6)) (.var 2)))
        (.equal (.var 4) (.var 5))))))))))))

theorem star_bijFormula (s : ZFSet.{u} → ZFSet.{u}) (PN N' Le' one : ZFSet.{u}) :
    (bijFormula PN N' Le' one).star s = bijFormula (s PN) (s N') (s Le') (s one) := by
  simp [bijFormula]

theorem sat_bijFormula (W PN N' Le' one : ZFSet.{u}) (v : ℕ → ZFSet.{u}) :
    Sat W v (bijFormula PN N' Le' one) ↔
      ∃ V ∈ W, V ∈ PN ∧ BijSpec W N' Le' one V (v 0) (v 1) (v 2) := by
  simp only [bijFormula, BijSpec]
  sat_simp

theorem admissible_bijFormula {U PN N' Le' one : ZFSet.{u}} (hPN : PN ∈ U) (hN : N' ∈ U)
    (hLe : Le' ∈ U) (hone : one ∈ U) :
    (bijFormula PN N' Le' one).Admissible U (insert 2 (insert 1 (insert 0 ∅))) := by
  simp [bijFormula, hPN, hN, hLe, hone]

/-- The bounded statement {lit}`BijSpec` says what it is meant to say. -/
theorem bijSpec_iff {W N' Le' one V Z n f : ZFSet.{u}} (hV : V ⊆ W) (hZ : Z ⊆ W) (hN : N' ⊆ W)
    (hf : f ⊆ W) :
    BijSpec W N' Le' one V Z n f ↔
      V = (N'.sep fun x => pair one x ∈ Le' ∧ pair x n ∈ Le') ∧ IsFunc V Z f ∧
        IsInjective f ∧ ran f = Z := by
  constructor
  · rintro ⟨e1, e2, e3, e4, e5, e6, e7⟩
    have hsub : f ⊆ prod V Z := fun b hb => by
      obtain ⟨x, -, hx, y, -, hy, rfl⟩ := e3 b (hf hb) hb
      exact pair_mem_prod.2 ⟨hx, hy⟩
    refine ⟨?_, ⟨hsub, fun x hx => ?_⟩, fun a a' b hab hab' => ?_, ?_⟩
    · ext x
      rw [mem_sep]
      exact ⟨fun hx => e1 x (hV hx) hx, fun hx => e2 x (hN hx.1) hx.1 hx.2⟩
    · obtain ⟨y, -, hy, hxy⟩ := e5 x (hV hx) hx
      refine ⟨y, hxy, fun w hw => ?_⟩
      have hwZ := (pair_mem_prod.1 (hsub hw)).2
      exact e4 x (hV hx) hx w (hZ hwZ) hwZ y (hZ hy) hy ⟨hw, hxy⟩
    · have h1 := pair_mem_prod.1 (hsub hab)
      have h2 := pair_mem_prod.1 (hsub hab')
      exact e7 a (hV h1.1) h1.1 a' (hV h2.1) h2.1 b (hZ h1.2) h1.2 ⟨hab, hab'⟩
    · ext y
      rw [mem_ran]
      constructor
      · rintro ⟨x, hxy⟩
        exact (pair_mem_prod.1 (hsub hxy)).2
      · intro hy
        obtain ⟨x, -, -, hxy⟩ := e6 y (hZ hy) hy
        exact ⟨x, hxy⟩
  · rintro ⟨rfl, hfunc, hinj, hran⟩
    refine ⟨fun x _ hx => mem_sep.1 hx, fun x _ hx h => mem_sep.2 ⟨hx, h⟩, fun b _ hb => ?_,
      fun x _ hx y _ _ z _ _ h => ?_, fun x _ hx => ?_, fun y _ hy => ?_,
      fun x _ _ y _ _ z _ _ h => hinj x y z h.1 h.2⟩
    · obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod.1 (hfunc.1 hb)
      exact ⟨x, hV hx, hx, y, hZ hy, hy, rfl⟩
    · exact hfunc.isFunction.2 x y z h.1 h.2
    · obtain ⟨y, hy, -⟩ := hfunc.2 x hx
      have hyZ := (pair_mem_prod.1 (hfunc.1 hy)).2
      exact ⟨y, hZ hyZ, hyZ, hy⟩
    · rw [← hran, mem_ran] at hy
      obtain ⟨x, hxy⟩ := hy
      have hxV := (pair_mem_prod.1 (hfunc.1 hxy)).1
      exact ⟨x, hV hxV, hxV, hxy⟩

/-- Unfold the truth definition of a formula built from {lit}`bijFormula`. -/
macro "bij_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Formula.Holds, Formula.star, Term.star, star_bijFormula, Sat,
    sat_bijFormula, Term.Defined, Term.val, Term.val_opair, Term.defined_opair,
    Term.star_opair, forall_true_left, true_and, and_true, and_self,
    Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, zero_ne_one,
    one_ne_zero, OfNat.ofNat_ne_zero, OfNat.zero_ne_ofNat, OfNat.ofNat_ne_one,
    OfNat.one_ne_ofNat, Nat.reduceEqDiff] $[$loc]?)

namespace RealFramework

open Formula Term NonstandardFramework

variable (F : RealFramework.{u}) {A B C D f a b c n x : ZFSet.{u}}

/-- In the standard universe, the initial segment determined by the natural number $`m`
consists of the numbers $`1, \dots, m`. -/
theorem mem_sep_seg_iff {m : ℕ} :
    x ∈ (F.N.sep fun x => pair (F.nat 1) x ∈ F.Le ∧ pair x (F.nat m) ∈ F.Le) ↔
      ∃ k, 1 ≤ k ∧ k ≤ m ∧ x = F.nat k := by
  rw [mem_sep, F.mem_N]
  constructor
  · rintro ⟨⟨k, rfl⟩, h1, h2⟩
    exact ⟨k, F.pair_nat_mem_Le.1 h1, F.pair_nat_mem_Le.1 h2, rfl⟩
  · rintro ⟨k, h1, h2, rfl⟩
    exact ⟨⟨k, rfl⟩, F.pair_nat_mem_Le.2 h1, F.pair_nat_mem_Le.2 h2⟩

/-- **Theorem 13.17.1.** A set $`B` is hyperfinite if and only if there is an internal
bijection $`f : \{1, \dots, n\} \to B` for some $`n \in {}^*\mathbb N`. An internal function
is an internal set of pairs of members of $`\mathbb U'`; in the second sentence transferred
in the proof, the clause that $`Z` is a set is added to the book's hypothesis (it is
automatic there because the book's $`\mathbb N` does not contain $`0`). -/
theorem hyperfinite_iff :
    F.Hyperfinite B ↔ ∃ n ∈ F.star F.N, ∃ f, F.Internal f ∧ RelIn F.U' f ∧
      IsFunc (F.seg n) B f ∧ IsInjective f ∧ ran f = B := by
  have hPN := F.hU.isSetOf_powerset F.isSetOf_N
  have hNU' := F.star_subset_U' F.isSetOf_N
  constructor
  · rintro ⟨A, hA, hB⟩
    have hFP := F.hU.isSetOf_finPow hA
    have hNA := F.hU.isSetOf_prod F.isSetOf_N hA
    have hPNA := F.hU.isSetOf_powerset hNA
    have hsent : (Formula.all 0 (.const (finPow A)) (.ex 1 (.const F.N)
        (.ex 2 (.const (powerset (prod F.N A)))
          (bijFormula (powerset F.N) F.N F.Le (F.nat 1))))).IsSentence F.U :=
      ⟨hFP.1, F.isSetOf_N.1, hPNA.1,
        admissible_bijFormula hPN.1 F.isSetOf_N.1 F.isSetOf_Le.1 (F.nat_mem_U 1)⟩
    have h := F.transfer _ hsent
    bij_simp at h
    rw [F.star_nat] at h
    have hBsub := (F.internal_subset_of_mem_star_finPow hA hB).1
    have hBU : B ⊆ F.U' := fun y hy => F.star_subset_U' hA (hBsub hy)
    obtain ⟨n, -, hn, f, -, hf, V, -, hV, hspec⟩ := h.1 (by
      intro Z _ hZ
      obtain ⟨hZA, hZfin⟩ := mem_finPow.1 hZ
      have := hZfin.to_subtype
      let e := (Finite.equivFin (Z : Set ZFSet.{u})).symm
      set m := Nat.card (Z : Set ZFSet.{u}) with hm
      set V : ZFSet.{u} := F.N.sep fun x => pair (F.nat 1) x ∈ F.Le ∧ pair x (F.nat m) ∈ F.Le
        with hVdef
      set f : ZFSet.{u} := ZFSet.range fun i : Fin m => pair (F.nat (i + 1)) (e i : ZFSet.{u})
        with hfdef
      have hfmem : ∀ p, p ∈ f ↔ ∃ i : Fin m, p = pair (F.nat (i + 1)) (e i) := by
        intro p
        rw [hfdef, mem_range]
        exact ⟨fun ⟨k, h⟩ => ⟨k, h.symm⟩, fun ⟨k, h⟩ => ⟨k, h.symm⟩⟩
      have hVmem : ∀ x, x ∈ V ↔ ∃ i : Fin m, x = F.nat (i + 1) := by
        intro x
        rw [hVdef, F.mem_sep_seg_iff]
        constructor
        · rintro ⟨k, h1, h2, rfl⟩
          exact ⟨⟨k - 1, by omega⟩, by congr 1; simp; omega⟩
        · rintro ⟨i, rfl⟩
          exact ⟨i + 1, by omega, by omega, rfl⟩
      have heZ : ∀ i, (e i : ZFSet.{u}) ∈ Z := fun i => (e i).2
      have hfunc : IsFunc V Z f := by
        refine ⟨fun p hp => ?_, fun z hz => ?_⟩
        · obtain ⟨i, rfl⟩ := (hfmem p).1 hp
          exact pair_mem_prod.2 ⟨(hVmem _).2 ⟨i, rfl⟩, heZ i⟩
        · obtain ⟨i, rfl⟩ := (hVmem z).1 hz
          refine ⟨e i, (hfmem _).2 ⟨i, rfl⟩, fun w hw => ?_⟩
          obtain ⟨j, hj⟩ := (hfmem _).1 hw
          obtain ⟨h1, h2⟩ := pair_inj.1 hj
          have : i = j := Fin.ext (by simpa using F.nat_injective h1)
          rw [h2, this]
      have hinj : IsInjective f := by
        intro a a' b hab hab'
        obtain ⟨i, hi⟩ := (hfmem _).1 hab
        obtain ⟨j, hj⟩ := (hfmem _).1 hab'
        obtain ⟨rfl, h2⟩ := pair_inj.1 hi
        obtain ⟨rfl, h2'⟩ := pair_inj.1 hj
        have : e i = e j := Subtype.ext (h2.symm.trans h2')
        rw [e.injective this]
      have hran : ran f = Z := by
        ext z
        rw [mem_ran]
        constructor
        · rintro ⟨x, hx⟩
          exact (pair_mem_prod.1 (hfunc.1 hx)).2
        · intro hz
          refine ⟨F.nat ((e.symm ⟨z, hz⟩ : ℕ) + 1), (hfmem _).2 ⟨e.symm ⟨z, hz⟩, ?_⟩⟩
          rw [Equiv.apply_symm_apply]
      have hVN : V ⊆ F.N := sep_subset
      have hZU : Z ⊆ F.U := fun y hy => F.hU.subset hA (hZA hy)
      have hfNA : f ⊆ prod F.N A := fun p hp => by
        obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 (hfunc.1 hp)
        exact pair_mem_prod.2 ⟨hVN ha, hZA hb⟩
      have hfU : f ⊆ F.U := fun p hp => F.hU.subset hNA (hfNA hp)
      refine ⟨F.nat m, F.nat_mem_U m, F.mem_N.2 ⟨m, rfl⟩, f,
        (F.hU.isSetOf_of_subset hNA hfNA).1, mem_powerset.2 hfNA, V,
        (F.hU.isSetOf_of_subset F.isSetOf_N hVN).1, mem_powerset.2 hVN, ?_⟩
      exact (bijSpec_iff (fun x hx => F.hU.subset F.isSetOf_N (hVN hx)) hZU
        (F.hU.subset F.isSetOf_N) hfU).2 ⟨rfl, hfunc, hinj, hran⟩) B
      (F.internal_subset_of_mem_star_finPow hA hB).2.mem_U' hB
    have hVN := mem_powerset.1 (F.star_powerset_subset F.isSetOf_N hV)
    have hfsub := mem_powerset.1 (F.star_powerset_subset hNA hf)
    have hfU' : f ⊆ F.U' := fun p hp => F.star_subset_U' hNA (hfsub hp)
    obtain ⟨rfl, hfunc, hinj, hran⟩ :=
      (bijSpec_iff (fun x hx => hNU' (hVN hx)) hBU hNU' hfU').1 hspec
    refine ⟨n, hn, f, F.internal_of_mem_star hPNA hf, fun p hp => ?_, hfunc, hinj, hran⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 (hfunc.1 hp)
    exact ⟨a, hNU' (hVN ha), b, hBU hb, rfl⟩
  · rintro ⟨n, hn, f, hfint, hfrel, hfunc, hinj, hran⟩
    have hfU' : f ⊆ F.U' := fun p hp => by
      obtain ⟨a, ha, b, hb, rfl⟩ := hfrel p hp
      exact (F.isUniverse'.isSetOf_opair ha hb).1
    have hfset : IsSetOf F.U' f := isSetOf_of_subset hfint.mem_U' hfU'
    have hBint : F.Internal B := hran ▸ F.internal_ran hfint hfset hfrel
    have hBU : B ⊆ F.U' := fun y hy => by
      rw [← hran, mem_ran] at hy
      obtain ⟨x, hxy⟩ := hy
      obtain ⟨a, -, b, hb, h⟩ := hfrel _ hxy
      rw [(pair_inj.1 h).2]
      exact hb
    obtain ⟨T, hT, hTt, hTt', hBT⟩ := F.exists_transitive_of_internal hBint
    have hBsubT : B ⊆ F.star T := fun y hy => hTt' B hBT y hy (hBU hy)
    have hNT := F.hU.isSetOf_prod F.isSetOf_N hT
    have hPNT := F.hU.isSetOf_powerset hNT
    have hFP := F.hU.isSetOf_finPow hT
    have hfmem : f ∈ F.star (powerset (prod F.N T)) := by
      refine (F.mem_star_powerset_iff hNT).2 ⟨fun p hp => ?_, hfint⟩
      rw [F.star_prod F.isSetOf_N hT]
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 (hfunc.1 hp)
      exact pair_mem_prod.2 ⟨(mem_sep.1 ha).1, hBsubT hb⟩
    have hS : (Formula.disj (.equal (.var 0) (.const ∅))
        (.ex 1 (.var 0) (.equal (.var 1) (.var 1)))).Admissible F.U (insert 0 ∅) := by
      simp [F.hU.empty_mem]
    have hsent : (Formula.all 0 (.const T) (.imp (.conj
          (.disj (.equal (.var 0) (.const ∅)) (.ex 1 (.var 0) (.equal (.var 1) (.var 1))))
          (.ex 1 (.const F.N) (.ex 2 (.const (powerset (prod F.N T)))
            (bijFormula (powerset F.N) F.N F.Le (F.nat 1)))))
        (.elem (.var 0) (.const (finPow T))))).IsSentence F.U :=
      ⟨hT.1, ⟨hS, F.isSetOf_N.1, hPNT.1,
        admissible_bijFormula hPN.1 F.isSetOf_N.1 F.isSetOf_Le.1 (F.nat_mem_U 1)⟩,
        Set.mem_insert _ _, hFP.1⟩
    have h := F.transfer _ hsent
    bij_simp at h
    rw [F.star_empty, F.star_nat] at h
    refine ⟨T, hT, h.1 ?_ B hBint.mem_U' hBT ⟨?_, n, hNU' hn, hn, f, hfint.mem_U', hfmem,
      F.seg n, (F.internal_seg hn).mem_U', F.seg_mem_star_powerset hn, ?_⟩⟩
    · rintro Z hZU hZT ⟨hZset, m', -, hm', f', -, hf', V', -, hV', hspec⟩
      have hZs : IsSetOf F.U Z := ⟨hZU, fun hi => by
        rcases hZset with rfl | ⟨y, hy, hyZ⟩
        · exact hi.1 rfl
        · exact hi.2 y hy hyZ⟩
      have hZsubU := F.hU.subset hZs
      have hZsubT : Z ⊆ T := fun y hy => hTt Z hZT y hy (hZsubU hy)
      rw [mem_powerset] at hf' hV'
      obtain ⟨rfl, hfunc', -, hran'⟩ := (bijSpec_iff
        (fun x hx => F.hU.subset F.isSetOf_N (hV' hx)) hZsubU (F.hU.subset F.isSetOf_N)
        (fun p hp => F.hU.subset hNT (hf' hp))).1 hspec
      obtain ⟨m, rfl⟩ := F.mem_N.1 hm'
      refine mem_finPow.2 ⟨hZsubT, ?_⟩
      refine ((Set.finite_Iic m).image fun k => app f' (F.nat k)).subset fun z hz => ?_
      have hz' : z ∈ ran f' := by
        rw [hran']
        exact hz
      obtain ⟨x, hxz⟩ := mem_ran.1 hz'
      obtain ⟨k, -, hk, rfl⟩ := F.mem_sep_seg_iff.1 (pair_mem_prod.1 (hfunc'.1 hxz)).1
      exact ⟨k, hk, hfunc'.isFunction.app_eq hxz⟩
    · rcases eq_empty_or_nonempty B with rfl | ⟨y, hy⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨y, hBU hy, hy⟩
    · exact (bijSpec_iff (fun x hx => hNU' (mem_sep.1 hx).1) hBU hNU' hfU').2
        ⟨rfl, hfunc, hinj, hran⟩

/-!
### Initial segments are hyperfinite

Initial segments are hyperfinite, and infinite when their end point is unlimited.
-/

/-- **Section 13.17.** For each $`n \in {}^*\mathbb N`, the initial segment
$`\{1, \dots, n\}` of $`{}^*\mathbb N` belongs to $`{}^*\mathcal P_F(\mathbb N)`: it is
hyperfinite. -/
theorem hyperfinite_seg (hn : n ∈ F.star F.N) : F.Hyperfinite (F.seg n) := by
  have hFP := F.hU.isSetOf_finPow F.isSetOf_N
  have h := F.transfer
    (.all 1 (.const F.N) (.ex 2 (.const (finPow F.N)) (.all 0 (.const F.N)
      (.biimp (.elem (.var 0) (.var 2))
        (.conj (.elem (.opair (.const (F.nat 1)) (.var 0)) (.const F.Le))
          (.elem (.opair (.var 0) (.var 1)) (.const F.Le)))))))
    (by simp [IsSentence, F.isSetOf_N.1, hFP.1, F.isSetOf_Le.1, F.nat_mem_U])
  sat_simp at h
  rw [F.star_nat] at h
  obtain ⟨V, -, hV, hVmem⟩ := h.1 (by
    intro m' _ hm'
    obtain ⟨m, rfl⟩ := F.mem_N.1 hm'
    refine ⟨F.N.sep fun x => pair (F.nat 1) x ∈ F.Le ∧ pair x (F.nat m) ∈ F.Le,
      (F.hU.isSetOf_sep F.isSetOf_N _).1, mem_finPow.2 ⟨sep_subset, ?_⟩, fun x _ hx => by
        rw [mem_sep]
        exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩⟩
    refine ((Set.finite_Iic m).image F.nat).subset fun x hx => ?_
    obtain ⟨k, -, hk, rfl⟩ := F.mem_sep_seg_iff.1 hx
    exact ⟨k, hk, rfl⟩) n (F.star_subset_U' F.isSetOf_N hn) hn
  have hVsub := (F.internal_subset_of_mem_star_finPow F.isSetOf_N hV).1
  have : F.seg n = V := by
    ext x
    rw [seg, mem_sep]
    constructor
    · rintro ⟨hx, h⟩
      exact (hVmem x (F.star_subset_U' F.isSetOf_N hx) hx).2 h
    · intro hx
      exact ⟨hVsub hx, (hVmem x (F.star_subset_U' F.isSetOf_N (hVsub hx)) (hVsub hx)).1 hx⟩
  rw [this]
  exact ⟨F.N, F.isSetOf_N, hV⟩

/-- **Section 13.17.** When $`n` is an unlimited hypernatural, the hyperfinite set
$`\{1, \dots, n\}` contains every positive natural number and is infinite. So
$`{}^*\mathcal P_F(\mathbb N)` is not included in $`\mathcal P_F({}^*\mathbb N)`. -/
theorem infinite_seg (hn : n ∈ F.star F.N) (hnN : n ∉ F.N) :
    (F.seg n : Set ZFSet.{u}).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => F.nat (k + 1))
    (fun i j h => by simpa using F.nat_injective h) fun k => ?_
  exact mem_sep.2 ⟨F.N_subset_star (F.mem_N.2 ⟨k + 1, rfl⟩),
    F.pair_nat_mem_star_Le.2 (Nat.le_add_left 1 k), F.nat_le_of_nonstandard hn hnN (k + 1)⟩

/-!
### Internal cardinality

The number of elements of a finite subset of $`A` is a function from $`\mathcal P_F(A)` to
$`\mathbb N` in the universe. Its transform assigns to every hyperfinite subset of
$`{}^*A` a hypernatural number, its internal cardinality, and this is the number $`n` of
Theorem 13.17.1.
-/

end RealFramework

/-- The graph of a map defined on the members of a set is a function on that set. -/
theorem isFunc_graph (A B : ZFSet.{u}) (h : A → ZFSet.{u}) (hB : ∀ a, h a ∈ B) :
    IsFunc A B (ZFSet.range fun a : A => pair (a : ZFSet.{u}) (h a)) := by
  refine ⟨fun p hp => ?_, fun z hz => ?_⟩
  · obtain ⟨a, rfl⟩ := mem_range.1 hp
    exact pair_mem_prod.2 ⟨a.2, hB a⟩
  · refine ⟨h ⟨z, hz⟩, mem_range.2 ⟨⟨z, hz⟩, rfl⟩, fun w hw => ?_⟩
    obtain ⟨a, ha⟩ := mem_range.1 hw
    obtain ⟨h1, h2⟩ := pair_inj.1 ha
    have : a = ⟨z, hz⟩ := Subtype.ext h1
    rw [← h2, this]

theorem app_graph (A B : ZFSet.{u}) (h : A → ZFSet.{u}) (hB : ∀ a, h a ∈ B) (a : A) :
    app (ZFSet.range fun a : A => pair (a : ZFSet.{u}) (h a)) a = h a :=
  (isFunc_graph A B h hB).isFunction.app_eq (mem_range.2 ⟨a, rfl⟩)

namespace RealFramework

open Formula Term NonstandardFramework

variable (F : RealFramework.{u}) {A B C D T f a b c n x : ZFSet.{u}}

/-- **Section 13.17, cardinality of finite sets.** The function $`\mathcal P_F(A) \to
\mathbb N` assigning to each finite subset of $`A` its number of elements, as a set of pairs
in the universe. -/
def cardFn (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun Z : (finPow A : ZFSet.{u}) =>
    pair (Z : ZFSet.{u}) (F.nat (Nat.card ((Z : ZFSet.{u}) : Set ZFSet.{u})))

theorem isFunc_cardFn (A : ZFSet.{u}) : IsFunc (finPow A) F.N (F.cardFn A) :=
  isFunc_graph _ _ _ fun _ => F.mem_N.2 ⟨_, rfl⟩

/-- **Section 13.17, internal cardinality.** The internal cardinality $`|B|` of a hyperfinite
set $`B \in {}^*\mathcal P_F(A)`: the value at $`B` of the transform of the cardinality
function $`\mathcal P_F(A) \to \mathbb N`. -/
def icard (A B : ZFSet.{u}) : ZFSet.{u} := app (F.star (F.cardFn A)) B

/-- **Section 13.17.** The map $`B \mapsto |B|` is an internal function from
$`{}^*\mathcal P_F(A)` to $`{}^*\mathbb N`: it is the transform of the cardinality
function. -/
theorem isFunc_star_cardFn (hA : IsSetOf F.U A) :
    IsFunc (F.star (finPow A)) (F.star F.N) (F.star (F.cardFn A)) ∧
      F.Internal (F.star (F.cardFn A)) :=
  ⟨F.isFunc_star (F.hU.isSetOf_finPow hA) F.isSetOf_N (F.isFunc_cardFn A),
    F.internal_star (F.hU.isSetOf_of_isFunc (F.hU.isSetOf_finPow hA) F.isSetOf_N
      (F.isFunc_cardFn A)).1⟩

/-- The internal cardinality of a hyperfinite subset of $`{}^*A` is a hypernatural number. -/
theorem icard_mem (hA : IsSetOf F.U A) (hB : B ∈ F.star (finPow A)) :
    F.icard A B ∈ F.star F.N := by
  have hf := (F.isFunc_star_cardFn hA).1
  exact (pair_mem_prod.1 (hf.1 (hf.isFunction.pair_app_mem (hf.dom_eq ▸ hB)))).2

/-- **Section 13.17.** On (the transform of) a finite set the internal cardinality is the
ordinary number of elements. -/
theorem icard_star {Z : ZFSet.{u}} (hA : IsSetOf F.U A) (hZ : Z ∈ finPow A) :
    F.icard A (F.star Z) = F.nat (Nat.card (Z : Set ZFSet.{u})) := by
  rw [icard, ← F.star_app (F.hU.isSetOf_finPow hA) F.isSetOf_N (F.isFunc_cardFn A) hZ]
  have : app (F.cardFn A) Z = F.nat (Nat.card (Z : Set ZFSet.{u})) :=
    app_graph (finPow A) F.N _ (fun _ => F.mem_N.2 ⟨_, rfl⟩) ⟨Z, hZ⟩
  rw [this, F.star_nat]

/-- In the standard universe, a set in bijection with $`\{1, \dots, m\}` has $`m`
elements. -/
theorem card_eq_of_bijection {m : ℕ} {Z g : ZFSet.{u}}
    (hfunc : IsFunc (F.N.sep fun x => pair (F.nat 1) x ∈ F.Le ∧ pair x (F.nat m) ∈ F.Le) Z g)
    (hinj : IsInjective g) (hran : ran g = Z) : Nat.card (Z : Set ZFSet.{u}) = m := by
  have hV : ∀ i : Fin m, F.nat (i + 1) ∈
      (F.N.sep fun x => pair (F.nat 1) x ∈ F.Le ∧ pair x (F.nat m) ∈ F.Le) := fun i =>
    F.mem_sep_seg_iff.2 ⟨i + 1, by omega, by omega, rfl⟩
  have hpair : ∀ i : Fin m, pair (F.nat (i + 1)) (app g (F.nat (i + 1))) ∈ g := fun i =>
    hfunc.isFunction.pair_app_mem (hfunc.dom_eq ▸ hV i)
  let φ : Fin m → (Z : Set ZFSet.{u}) := fun i =>
    ⟨app g (F.nat (i + 1)), (pair_mem_prod.1 (hfunc.1 (hpair i))).2⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro i j hij
      have h1 : app g (F.nat (i + 1)) = app g (F.nat (j + 1)) := congrArg Subtype.val hij
      have h2 := hpair j
      rw [← h1] at h2
      exact Fin.ext (by simpa using F.nat_injective (hinj _ _ _ (hpair i) h2))
    · rintro ⟨z, hz⟩
      have hz' : z ∈ ran g := by
        rw [hran]
        exact hz
      obtain ⟨x, hxz⟩ := mem_ran.1 hz'
      obtain ⟨k, hk1, hk2, rfl⟩ := F.mem_sep_seg_iff.1 (pair_mem_prod.1 (hfunc.1 hxz)).1
      refine ⟨⟨k - 1, by omega⟩, Subtype.ext ?_⟩
      have hk : k - 1 + 1 = k := by omega
      show app g (F.nat (k - 1 + 1)) = z
      rw [hk]
      exact hfunc.isFunction.app_eq hxz
  simpa using (Nat.card_eq_of_bijective φ hφ).symm

/-- **Section 13.17.** The number $`n` in Theorem 13.17.1 is the internal cardinality of
$`B`: if there is an internal bijection from $`\{1, \dots, n\}` onto a hyperfinite subset
$`B` of $`{}^*A`, then $`|B| = n`. -/
theorem icard_eq_of_bijection (hA : IsSetOf F.U A) (hB : B ∈ F.star (finPow A))
    (hn : n ∈ F.star F.N) (hf : F.Internal f) (hfunc : IsFunc (F.seg n) B f)
    (hinj : IsInjective f) (hran : ran f = B) : F.icard A B = n := by
  have hPN := F.hU.isSetOf_powerset F.isSetOf_N
  have hNU' := F.star_subset_U' F.isSetOf_N
  have hFP := F.hU.isSetOf_finPow hA
  have hNA := F.hU.isSetOf_prod F.isSetOf_N hA
  have hPNA := F.hU.isSetOf_powerset hNA
  have hC := F.hU.isSetOf_of_isFunc hFP F.isSetOf_N (F.isFunc_cardFn A)
  have hBsub := (F.internal_subset_of_mem_star_finPow hA hB).1
  have hBU : B ⊆ F.U' := fun y hy => F.star_subset_U' hA (hBsub hy)
  have hfsub : f ⊆ prod (F.star F.N) (F.star A) := fun p hp => by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 (hfunc.1 hp)
    exact pair_mem_prod.2 ⟨(mem_sep.1 ha).1, hBsub hb⟩
  have hfmem : f ∈ F.star (powerset (prod F.N A)) :=
    (F.mem_star_powerset_iff hNA).2 ⟨by rw [F.star_prod F.isSetOf_N hA]; exact hfsub, hf⟩
  have hfU' : f ⊆ F.U' := fun p hp => by
    have := hfsub hp
    rw [← F.star_prod F.isSetOf_N hA] at this
    exact F.star_subset_U' hNA this
  have hsent : (Formula.all 0 (.const (finPow A)) (.all 1 (.const F.N)
      (.all 2 (.const (powerset (prod F.N A))) (.imp
        (bijFormula (powerset F.N) F.N F.Le (F.nat 1))
        (.elem (.opair (.var 0) (.var 1)) (.const (F.cardFn A))))))).IsSentence F.U :=
    ⟨hFP.1, F.isSetOf_N.1, hPNA.1,
      admissible_bijFormula hPN.1 F.isSetOf_N.1 F.isSetOf_Le.1 (F.nat_mem_U 1),
      by simp [hC.1]⟩
  have h := F.transfer _ hsent
  bij_simp at h
  rw [F.star_nat] at h
  have h' := h.1 (by
    rintro Z - hZ m' - hm' g - hg ⟨V, -, hV, hspec⟩
    obtain ⟨m, rfl⟩ := F.mem_N.1 hm'
    rw [mem_powerset] at hg hV
    have hZU : Z ⊆ F.U := fun y hy => F.hU.subset hA ((mem_finPow.1 hZ).1 hy)
    obtain ⟨rfl, hfunc', hinj', hran'⟩ := (bijSpec_iff
      (fun x hx => F.hU.subset F.isSetOf_N (hV hx)) hZU (F.hU.subset F.isSetOf_N)
      (fun p hp => F.hU.subset hNA (hg hp))).1 hspec
    refine mem_range.2 ⟨⟨Z, hZ⟩, ?_⟩
    show pair Z (F.nat (Nat.card (Z : Set ZFSet.{u}))) = pair Z (F.nat m)
    rw [F.card_eq_of_bijection hfunc' hinj' hran'])
  have hmem := h' B (F.star_subset_U' hFP hB) hB n (hNU' hn) hn f hf.mem_U' hfmem
    ⟨F.seg n, (F.internal_seg hn).mem_U', F.seg_mem_star_powerset hn,
      (bijSpec_iff (fun x hx => hNU' (mem_sep.1 hx).1) hBU hNU' hfU').2
        ⟨rfl, hfunc, hinj, hran⟩⟩
  exact (F.isFunc_star_cardFn hA).1.isFunction.app_eq hmem

/-- The identity function on a set, as a set of pairs. -/
def _root_.Goldblatt.idOn (S : ZFSet.{u}) : ZFSet.{u} :=
  (prod S S).sep fun p => ∃ a, p = pair a a

theorem _root_.Goldblatt.pair_mem_idOn {S : ZFSet.{u}} : pair a b ∈ idOn S ↔ a ∈ S ∧ a = b := by
  rw [idOn, mem_sep, pair_mem_prod]
  constructor
  · rintro ⟨⟨ha, -⟩, c, hc⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.1 hc
    exact ⟨ha, rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨⟨ha, ha⟩, a, rfl⟩

theorem _root_.Goldblatt.isFunc_idOn (S : ZFSet.{u}) :
    IsFunc S S (idOn S) ∧ IsInjective (idOn S) ∧ ran (idOn S) = S := by
  refine ⟨⟨sep_subset, fun z hz => ⟨z, pair_mem_idOn.2 ⟨hz, rfl⟩, fun w hw =>
    (pair_mem_idOn.1 hw).2.symm⟩⟩, fun a a' b h h' => ?_, ?_⟩
  · rw [(pair_mem_idOn.1 h).2, (pair_mem_idOn.1 h').2]
  · ext b
    rw [mem_ran]
    exact ⟨fun ⟨a, h⟩ => (pair_mem_idOn.1 h).2 ▸ (pair_mem_idOn.1 h).1,
      fun hb => ⟨b, pair_mem_idOn.2 ⟨hb, rfl⟩⟩⟩

/-- The identity function on an internal set is internal. -/
theorem internal_idOn {S : ZFSet.{u}} (hS : F.Internal S) (hSset : IsSetOf F.U' S) :
    F.Internal (idOn S) := by
  have hP := F.internal_prod hS hSset hS hSset
  have hSU := F.isUniverse'.subset hSset
  have hPset : IsSetOf F.U' (prod S S) := isSetOf_of_subset hP.mem_U' fun p hp => by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 hp
    exact (F.isUniverse'.isSetOf_opair (hSU ha) (hSU hb)).1
  have := F.internal_sep (.ex 1 (.var 2) (.equal (.var 0) (.opair (.var 1) (.var 1)))) [2] 0
    (by simp) (fun _ => S) (by simp [hS]) hP hPset
  sat_simp at this
  have e : idOn S = (prod S S).sep fun p => ∃ a ∈ F.U', a ∈ S ∧ p = pair a a := by
    ext p
    rw [idOn, mem_sep, mem_sep]
    constructor
    · rintro ⟨hp, a, rfl⟩
      have ha := (pair_mem_prod.1 hp).1
      exact ⟨hp, a, hSU ha, ha, rfl⟩
    · rintro ⟨hp, a, -, -, rfl⟩
      exact ⟨hp, a, rfl⟩
  rw [e]
  exact this

/-- **Section 13.17.** The internal cardinality of the initial segment
$`\{1, \dots, n\}` is $`n`. -/
theorem icard_seg (hn : n ∈ F.star F.N) : F.icard F.N (F.seg n) = n := by
  have hseg := F.hyperfinite_seg hn
  obtain ⟨h1, h2, h3⟩ := isFunc_idOn (F.seg n)
  exact F.icard_eq_of_bijection F.isSetOf_N (hseg.mem_star_finPow F.isSetOf_N sep_subset) hn
    (F.internal_idOn hseg.internal hseg.isSetOf) h1 h2 h3

/-!
## 13.18 Exercises on Hyperfinite Sets and Sizes

The exercises of Section 13.18: bounds for internal injections between initial segments,
hyperfiniteness and size of internal subsets and of the internal power set, greatest and
least elements, and the characterization of hyperfinite sets by internal surjections. Two
parts that do not involve numbers, that internal subsets and internal images of hyperfinite
sets are hyperfinite (Exercises 13.18 (2) and (6)), are proved in Section 13.17 above for
arbitrary frameworks, where the later proofs of that section use them. The exercises appear
here in the order (2), (1), (4), (3), (5), because the first uses the second.
-/

/-- **Exercise 13.18 (2), second part.** If $`B \subseteq A` are hyperfinite subsets of
$`{}^*T`, then $`|B| \le |A|`. -/
theorem icard_le_of_subset (hT : IsSetOf F.U T) (hA : A ∈ F.star (finPow T))
    (hB : B ∈ F.star (finPow T)) (hBA : B ⊆ A) :
    pair (F.icard T B) (F.icard T A) ∈ F.star F.Le := by
  have hFP := F.hU.isSetOf_finPow hT
  have hC := F.hU.isSetOf_of_isFunc hFP F.isSetOf_N (F.isFunc_cardFn T)
  have h := F.transfer
    (.all 0 (.const (finPow T)) (.all 1 (.const (finPow T)) (.imp
      (.all 2 (.var 1) (.elem (.var 2) (.var 0)))
      (.ex 3 (.const F.N) (.ex 4 (.const F.N) (.conj
        (.elem (.opair (.var 1) (.var 3)) (.const (F.cardFn T)))
        (.conj (.elem (.opair (.var 0) (.var 4)) (.const (F.cardFn T)))
          (.elem (.opair (.var 3) (.var 4)) (.const F.Le)))))))))
    (by simp [IsSentence, hFP.1, hC.1, F.isSetOf_N.1, F.isSetOf_Le.1])
  sat_simp at h
  obtain ⟨c, -, -, d, -, -, hc, hd, hcd⟩ := h.1 (by
    intro x _ hx y _ hy hyx
    have hxT := mem_finPow.1 hx
    have hsub : (y : Set ZFSet.{u}) ⊆ x := fun z hz =>
      hyx z (F.hU.subset hT ((mem_finPow.1 hy).1 hz)) hz
    exact ⟨_, F.nat_mem_U _, F.mem_N.2 ⟨_, rfl⟩, _, F.nat_mem_U _, F.mem_N.2 ⟨_, rfl⟩,
      mem_range.2 ⟨⟨y, hy⟩, rfl⟩, mem_range.2 ⟨⟨x, hx⟩, rfl⟩,
      F.pair_nat_mem_Le.2 (Nat.card_mono hxT.2 hsub)⟩)
    A (F.star_subset_U' hFP hA) hA B (F.star_subset_U' hFP hB) hB fun z _ hz => hBA hz
  have hfun := (F.isFunc_star_cardFn hT).1.isFunction
  rw [icard, icard, hfun.app_eq hc, hfun.app_eq hd]
  exact hcd

/-- **Exercise 13.18 (1), first part.** If there is an internal injection
$`\{1, \dots, n\} \to \{1, \dots, m\}`, then $`n \le m`. -/
theorem le_of_internal_injection {m : ZFSet.{u}} (hn : n ∈ F.star F.N) (hm : m ∈ F.star F.N)
    (hf : F.Internal f) (hrel : RelIn F.U' f) (hfunc : IsFunc (F.seg n) (F.seg m) f)
    (hinj : IsInjective f) : pair n m ∈ F.star F.Le := by
  have hfU' : f ⊆ F.U' := fun p hp => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hrel p hp
    exact (F.isUniverse'.isSetOf_opair ha hb).1
  have hfset : IsSetOf F.U' f := isSetOf_of_subset hf.mem_U' hfU'
  have hran := F.internal_ran hf hfset hrel
  have hsub : ran f ⊆ F.seg m := hfunc.ran_subset
  have hsegm := F.hyperfinite_seg hm
  have hB := (hsegm.of_internal_subset hran hsub).mem_star_finPow F.isSetOf_N
    fun y hy => (mem_sep.1 (hsub hy)).1
  have hfunc' : IsFunc (F.seg n) (ran f) f := by
    refine ⟨fun p hp => ?_, hfunc.2⟩
    obtain ⟨a, ha, b, -, rfl⟩ := mem_prod.1 (hfunc.1 hp)
    exact pair_mem_prod.2 ⟨ha, mem_ran.2 ⟨a, hp⟩⟩
  have h1 := F.icard_eq_of_bijection F.isSetOf_N hB hn hf hfunc' hinj rfl
  have h2 := F.icard_seg hm
  have := F.icard_le_of_subset F.isSetOf_N (hsegm.mem_star_finPow F.isSetOf_N sep_subset) hB hsub
  rwa [h1, h2] at this

/-- **Exercise 13.18 (1), second part.** If there is an internal bijection
$`\{1, \dots, n\} \to \{1, \dots, m\}`, then $`n = m`. Hence the number $`n` in Theorem
13.17.1 is uniquely determined by the hyperfinite set. -/
theorem eq_of_internal_bijection {m : ZFSet.{u}} (hn : n ∈ F.star F.N) (hm : m ∈ F.star F.N)
    (hf : F.Internal f) (hfunc : IsFunc (F.seg n) (F.seg m) f) (hinj : IsInjective f)
    (hran : ran f = F.seg m) : n = m := by
  have hsegm := F.hyperfinite_seg hm
  rw [← F.icard_eq_of_bijection F.isSetOf_N (hsegm.mem_star_finPow F.isSetOf_N sep_subset) hn hf
    hfunc hinj hran, F.icard_seg hm]

/-- The power set of a finite set is finite. -/
theorem _root_.Goldblatt.finite_coe_powerset {x : ZFSet.{u}} (h : (x : Set ZFSet.{u}).Finite) :
    ((powerset x : ZFSet.{u}) : Set ZFSet.{u}).Finite := by
  have : Finite (𝒫 (x : Set ZFSet.{u})) := h.powerset.to_subtype
  have : Finite (powerset x) := Finite.of_equiv _ (powersetEquiv x).symm
  exact Set.toFinite _

theorem _root_.Goldblatt.card_coe_powerset {x : ZFSet.{u}} (h : (x : Set ZFSet.{u}).Finite) :
    Nat.card ((powerset x : ZFSet.{u}) : Set ZFSet.{u}) = 2 ^ Nat.card (x : Set ZFSet.{u}) := by
  have e : Nat.card ((powerset x : ZFSet.{u}) : Set ZFSet.{u}) =
      Nat.card (𝒫 (x : Set ZFSet.{u})) := Nat.card_congr (powersetEquiv x)
  rw [e, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_powerset _ h]

/-- **Exercise 13.18 (4).** The internal power set
$`\mathcal P_I(A) = \mathcal P(A) \cap {}^*\mathbb U = \{B \subseteq A : B \text{ is
internal}\}`. -/
def internalPowerset (A : ZFSet.{u}) : ZFSet.{u} := (powerset A).sep F.Internal

/-- The function $`k \mapsto 2^k` on the natural numbers, as a set of pairs in the
universe. -/
def powFn : ZFSet.{u} := ZFSet.range fun k : ℕ => pair (F.nat k) (F.nat (2 ^ k))

theorem isFunc_powFn : IsFunc F.N F.N F.powFn := by
  refine ⟨fun p hp => ?_, fun z hz => ?_⟩
  · obtain ⟨k, rfl⟩ := mem_range.1 hp
    exact pair_mem_prod.2 ⟨F.mem_N.2 ⟨k, rfl⟩, F.mem_N.2 ⟨_, rfl⟩⟩
  · obtain ⟨k, rfl⟩ := F.mem_N.1 hz
    refine ⟨F.nat (2 ^ k), mem_range.2 ⟨k, rfl⟩, fun w hw => ?_⟩
    obtain ⟨j, hj⟩ := mem_range.1 hw
    obtain ⟨h1, h2⟩ := pair_inj.1 hj
    rw [← h2, F.nat_injective h1]

/-- **Exercise 13.18 (4).** If $`A` is hyperfinite, then so is its internal power set
$`\mathcal P_I(A)`. Moreover, if $`|A| = n` then $`|\mathcal P_I(A)| = 2^n`, where
$`n \mapsto 2^n` is the transform of the exponential function on $`\mathbb N`. -/
theorem hyperfinite_internalPowerset (hT : IsSetOf F.U T) (hA : A ∈ F.star (finPow T)) :
    F.internalPowerset A ∈ F.star (finPow (powerset T)) ∧
      F.icard (powerset T) (F.internalPowerset A) = app (F.star F.powFn) (F.icard T A) := by
  have hPT := F.hU.isSetOf_powerset hT
  have hFT := F.hU.isSetOf_finPow hT
  have hFPT := F.hU.isSetOf_finPow hPT
  have hC := F.hU.isSetOf_of_isFunc hFT F.isSetOf_N (F.isFunc_cardFn T)
  have hC' := F.hU.isSetOf_of_isFunc hFPT F.isSetOf_N (F.isFunc_cardFn (powerset T))
  have hpow := F.hU.isSetOf_of_isFunc F.isSetOf_N F.isSetOf_N F.isFunc_powFn
  have h := F.transfer
    (.all 0 (.const (finPow T)) (.ex 1 (.const (finPow (powerset T))) (.conj
      (.all 2 (.const (powerset T)) (.biimp (.elem (.var 2) (.var 1))
        (.all 3 (.var 2) (.elem (.var 3) (.var 0)))))
      (.ex 4 (.const F.N) (.ex 5 (.const F.N) (.conj
        (.elem (.opair (.var 0) (.var 4)) (.const (F.cardFn T)))
        (.conj (.elem (.opair (.var 1) (.var 5)) (.const (F.cardFn (powerset T))))
          (.elem (.opair (.var 4) (.var 5)) (.const F.powFn)))))))))
    (by simp [IsSentence, hFT.1, hFPT.1, hPT.1, hC.1, hC'.1, hpow.1, F.isSetOf_N.1])
  sat_simp at h
  obtain ⟨y, -, hy, hymem, c, -, -, d, -, -, hc, hd, hcd⟩ := h.1 (by
    intro x _ hx
    obtain ⟨hxT, hxfin⟩ := mem_finPow.1 hx
    have hPx : powerset x ∈ finPow (powerset T) := mem_finPow.2
      ⟨fun z hz => mem_powerset.2 fun w hw => hxT (mem_powerset.1 hz hw), finite_coe_powerset hxfin⟩
    refine ⟨powerset x, (F.hU.subset hFPT hPx), hPx, fun z _ hz => ?_, _, F.nat_mem_U _,
      F.mem_N.2 ⟨_, rfl⟩, _, F.nat_mem_U _, F.mem_N.2 ⟨_, rfl⟩, mem_range.2 ⟨⟨x, hx⟩, rfl⟩,
      mem_range.2 ⟨⟨powerset x, hPx⟩, rfl⟩, ?_⟩
    · rw [mem_powerset]
      exact ⟨fun h w _ hw => h hw,
        fun h w hw => h w (F.hU.subset hT (mem_powerset.1 hz hw)) hw⟩
    · rw [card_coe_powerset hxfin]
      exact mem_range.2 ⟨_, rfl⟩) A (F.star_subset_U' hFT hA) hA
  have hysub := (F.internal_subset_of_mem_star_finPow hPT hy).1
  have hAsub := (F.internal_subset_of_mem_star_finPow hT hA).1
  have hPI : F.internalPowerset A = y := by
    ext z
    rw [internalPowerset, mem_sep, mem_powerset]
    constructor
    · rintro ⟨hzA, hzint⟩
      have hzP := (F.mem_star_powerset_iff hT).2 ⟨fun w hw => hAsub (hzA hw), hzint⟩
      exact (hymem z (F.star_subset_U' hPT hzP) hzP).2 fun w _ hw => hzA hw
    · intro hzy
      have hzP := hysub hzy
      obtain ⟨hzT, hzint⟩ := (F.mem_star_powerset_iff hT).1 hzP
      exact ⟨fun w hw => (hymem z (F.star_subset_U' hPT hzP) hzP).1 hzy w
        (F.star_subset_U' hT (hzT hw)) hw, hzint⟩
  rw [hPI]
  refine ⟨hy, ?_⟩
  rw [icard, icard, (F.isFunc_star_cardFn hPT).1.isFunction.app_eq hd,
    (F.isFunc_star_cardFn hT).1.isFunction.app_eq hc]
  exact ((F.isFunc_star F.isSetOf_N F.isSetOf_N F.isFunc_powFn).isFunction.app_eq hcd).symm

/-- **Exercise 13.18 (4).** If $`A` is hyperfinite, then so is its internal power set. -/
theorem hyperfinite_internalPowerset' (hA : F.Hyperfinite A) :
    F.Hyperfinite (F.internalPowerset A) :=
  let ⟨T, hT, hAT⟩ := hA
  ⟨powerset T, F.hU.isSetOf_powerset hT, (F.hyperfinite_internalPowerset hT hAT).1⟩

/-- **Exercise 13.18 (3).** Any nonempty hyperfinite subset of $`{}^*\mathbb R` has a
greatest and a least element. The book omits the word nonempty. -/
theorem exists_greatest_least (hB : F.Hyperfinite B) (hBR : B ⊆ F.star F.R) (hne : B ≠ ∅) :
    (∃ y ∈ B, ∀ z ∈ B, pair z y ∈ F.star F.Le) ∧ ∃ y ∈ B, ∀ z ∈ B, pair y z ∈ F.star F.Le := by
  have hFP := F.hU.isSetOf_finPow F.isSetOf_R
  have hBF := hB.mem_star_finPow F.isSetOf_R hBR
  have h := F.transfer
    (.all 0 (.const (finPow F.R)) (.imp (.neg (.equal (.var 0) (.const ∅))) (.conj
      (.ex 1 (.var 0) (.all 2 (.var 0) (.elem (.opair (.var 2) (.var 1)) (.const F.Le))))
      (.ex 1 (.var 0) (.all 2 (.var 0) (.elem (.opair (.var 1) (.var 2)) (.const F.Le)))))))
    (by simp [IsSentence, hFP.1, F.hU.empty_mem, F.isSetOf_Le.1])
  sat_simp at h
  rw [F.star_empty] at h
  have hBU : B ⊆ F.U' := fun y hy => F.star_subset_U' F.isSetOf_R (hBR hy)
  obtain ⟨⟨y, -, hy, hmax⟩, ⟨w, -, hw, hmin⟩⟩ := h.1 (by
    intro x _ hx hne
    obtain ⟨hxR, hxfin⟩ := mem_finPow.1 hx
    have hSfin : {r : ℝ | F.real r ∈ x}.Finite :=
      hxfin.preimage (F.real_injective.injOn (s := {r : ℝ | F.real r ∈ x}))
    have hSne : {r : ℝ | F.real r ∈ x}.Nonempty := by
      obtain ⟨y, hy⟩ := (eq_empty_or_nonempty x).resolve_left hne
      obtain ⟨r, rfl⟩ := F.mem_R.1 (hxR hy)
      exact ⟨r, hy⟩
    obtain ⟨M, hM, hMmax⟩ := Set.exists_max_image _ id hSfin hSne
    obtain ⟨m, hm, hmmin⟩ := Set.exists_min_image _ id hSfin hSne
    refine ⟨⟨F.real M, F.real_mem_U M, hM, fun z _ hz => ?_⟩,
      ⟨F.real m, F.real_mem_U m, hm, fun z _ hz => ?_⟩⟩
    · obtain ⟨r, rfl⟩ := F.mem_R.1 (hxR hz)
      exact F.pair_mem_Le.2 (hMmax r hz)
    · obtain ⟨r, rfl⟩ := F.mem_R.1 (hxR hz)
      exact F.pair_mem_Le.2 (hmmin r hz)) B hB.internal.mem_U' hBF hne
  exact ⟨⟨y, hy, fun z hz => hmax z (hBU hz) hz⟩, ⟨w, hw, fun z hz => hmin z (hBU hz) hz⟩⟩

/-- **Exercise 13.18 (5).** A set $`B` is hyperfinite if and only if there is an internal
surjection $`f : \{1, \dots, n\} \to B` for some $`n \in {}^*\mathbb N`. -/
theorem hyperfinite_iff_surjection :
    F.Hyperfinite B ↔ ∃ n ∈ F.star F.N, ∃ f, F.Internal f ∧ RelIn F.U' f ∧
      IsFunc (F.seg n) B f ∧ ran f = B := by
  constructor
  · intro h
    obtain ⟨n, hn, f, h1, h2, h3, -, h5⟩ := F.hyperfinite_iff.1 h
    exact ⟨n, hn, f, h1, h2, h3, h5⟩
  · rintro ⟨n, hn, f, hfint, hfrel, hfunc, hran⟩
    have : B = relImage f (F.seg n) := by
      ext b
      rw [← hran, mem_ran, mem_relImage]
      exact ⟨fun ⟨a, hab⟩ => ⟨a, (pair_mem_prod.1 (hfunc.1 hab)).1, hab⟩,
        fun ⟨a, _, hab⟩ => ⟨a, hab⟩⟩
    rw [this]
    exact (F.hyperfinite_seg hn).relImage hfint hfrel hfunc.isFunction

end RealFramework

end Goldblatt
