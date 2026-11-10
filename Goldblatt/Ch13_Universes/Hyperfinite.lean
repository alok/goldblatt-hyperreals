import Goldblatt.Ch13_Universes.Internal

/-!
# 13 (part 5). Numbers in a Framework and External Images

This is the fifth of seven parts of Chapter 13 (the overview is on the chapter page
{lit}`Goldblatt.Ch13_Universes`). From Section 13.9 on the book assumes that the real numbers
are among the individuals of the framework. This part makes that assumption explicit, and
covers what depends on it: the examples of Section 13.9, the internal least number principle
and internal induction of Section 13.12, the exercises of Section 13.13, and the theorem of
Section 13.14 that the image of an infinite set is external. Hyperfinite sets (Sections 13.17
and 13.18) are in part 6; arithmetic and hyperfinite sums (Sections 13.19 and 13.20) are in
part 7.

The sections follow the book's order with one exception, forced by the order of the
proofs: internal induction, an exercise of Section 13.13, is proved in Section 13.12 because
the proof that $`\mathbb N` is external uses it.
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

/-- **Section 13.9.** The individual representing a natural number. -/
def nat (k : ℕ) : ZFSet.{u} := F.real k

/-- **Section 13.9.** The set $`\mathbb R` of real numbers of the framework. -/
def R : ZFSet.{u} := ZFSet.range F.real

/-- **Section 13.9.** The set $`\mathbb N` of natural numbers of the framework. It is the
image of Lean's natural numbers and so starts from $`0`, whereas the book's $`\mathbb N` is
$`\{1, 2, \dots\}`. Later chapters that reuse this set should keep this in mind: initial
segments $`\{1, \dots, n\}` write their lower bound explicitly, and induction starts at
$`0`. -/
def N : ZFSet.{u} := ZFSet.range F.nat

/-- **Section 13.8.** The order relation $`\le` on the real numbers, as a set of pairs in the
universe. -/
def Le : ZFSet.{u} :=
  (prod F.R F.R).sep fun p => ∃ r s : ℝ, r ≤ s ∧ p = pair (F.real r) (F.real s)

/-- **Section 13.8.** The successor relation $`\{(k, k + 1)\}` on the natural numbers, as a set
of pairs in the universe. -/
def Succ : ZFSet.{u} := ZFSet.range fun k : ℕ => pair (F.nat k) (F.nat (k + 1))

/-- Distinct natural numbers are represented by distinct individuals. -/
theorem nat_injective : Function.Injective F.nat := fun _ _ h =>
  Nat.cast_injective (F.real_injective h)

/-- Real numbers are members of the universe. -/
theorem real_mem_U (r : ℝ) : F.real r ∈ F.U :=
  F.hU.subset F.isUniverseOver.base_isSetOf (F.real_mem r)

/-- Natural numbers are members of the universe. -/
theorem nat_mem_U (k : ℕ) : F.nat k ∈ F.U := F.real_mem_U k

/-- **Section 13.8.** A real number is its own transform, being an individual. -/
@[simp]
theorem star_real (r : ℝ) : F.star (F.real r) = F.real r := F.star_individual _ (F.real_mem r)

/-- **Section 13.8.** A natural number is its own transform. -/
@[simp]
theorem star_nat (k : ℕ) : F.star (F.nat k) = F.nat k := F.star_real k

/-- The members of $`\mathbb R` are the individuals representing real numbers. -/
theorem mem_R : a ∈ F.R ↔ ∃ r, a = F.real r := by
  rw [R, mem_range]
  exact ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩

/-- The members of $`\mathbb N` are the individuals representing natural numbers. -/
theorem mem_N : a ∈ F.N ↔ ∃ k, a = F.nat k := by
  rw [N, mem_range]
  exact ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩

/-- $`\mathbb R` is a set of individuals. -/
theorem R_subset_base : F.R ⊆ F.X := fun a ha => by
  obtain ⟨r, rfl⟩ := F.mem_R.1 ha
  exact F.real_mem r

/-- $`\mathbb N` is a set of individuals. -/
theorem N_subset_base : F.N ⊆ F.X := fun a ha => by
  obtain ⟨k, rfl⟩ := F.mem_N.1 ha
  exact F.real_mem k

/-- $`\mathbb R` is a set of the universe. -/
theorem isSetOf_R : IsSetOf F.U F.R :=
  F.hU.isSetOf_of_subset F.isUniverseOver.base_isSetOf F.R_subset_base

/-- $`\mathbb N` is a set of the universe. -/
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

/-- The relation {lit}`Le` holds between two real numbers exactly when $`r \le s`. -/
theorem pair_mem_Le {r s : ℝ} : pair (F.real r) (F.real s) ∈ F.Le ↔ r ≤ s := by
  rw [Le, mem_sep]
  constructor
  · rintro ⟨-, r', s', h, he⟩
    obtain ⟨h1, h2⟩ := pair_inj.1 he
    rwa [F.real_injective h1, F.real_injective h2]
  · exact fun h => ⟨pair_mem_prod.2 ⟨F.mem_R.2 ⟨r, rfl⟩, F.mem_R.2 ⟨s, rfl⟩⟩, r, s, h, rfl⟩

/-- The relation {lit}`Le` holds between two natural numbers exactly when $`j \le k`. -/
theorem pair_nat_mem_Le {j k : ℕ} : pair (F.nat j) (F.nat k) ∈ F.Le ↔ j ≤ k := by
  rw [nat, nat, pair_mem_Le, Nat.cast_le]

/-- The order relation on $`\mathbb R` is a set of the universe. -/
theorem isSetOf_Le : IsSetOf F.U F.Le :=
  F.hU.isSetOf_of_subset_prod F.isSetOf_R F.isSetOf_R sep_subset

/-- The members of the successor relation are the pairs $`(k, k + 1)`. -/
theorem mem_Succ : a ∈ F.Succ ↔ ∃ k, a = pair (F.nat k) (F.nat (k + 1)) := by
  rw [Succ, mem_range]
  exact ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩

/-- The successor of the natural number $`k` is $`k + 1`. -/
theorem pair_mem_Succ {k : ℕ} : pair (F.nat k) b ∈ F.Succ ↔ b = F.nat (k + 1) := by
  rw [mem_Succ]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨h1, h2⟩ := pair_inj.1 hj
    rw [h2, F.nat_injective h1]
  · exact fun h => ⟨k, by rw [h]⟩

/-- The successor relation is a set of the universe. -/
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

/-- **Section 13.8.** On real numbers the transformed order $`{}^*{\le}` agrees with $`\le`. -/
theorem pair_real_mem_star_Le {r s : ℝ} :
    pair (F.real r) (F.real s) ∈ F.star F.Le ↔ r ≤ s := by
  have := F.star_mem_star_iff (F.hU.isSetOf_opair (F.real_mem_U r) (F.real_mem_U s)).1
    F.isSetOf_Le.1
  rw [F.star_opair (F.real_mem_U r) (F.real_mem_U s), F.star_real, F.star_real] at this
  rw [this, F.pair_mem_Le]

/-- **Section 13.8.** On natural numbers the transformed order agrees with $`\le`. -/
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

/-- **Section 13.9, open intervals.** The open interval $`(a, b)` of a set $`S` of numbers ordered by the relation $`L`:
$`\{x \in S : a < x < b\}`, where $`a < x` means $`a \le x` and $`x \ne a`. -/
def _root_.Goldblatt.ooIn (S L a b : ZFSet.{u}) : ZFSet.{u} :=
  S.sep fun x => (pair a x ∈ L ∧ x ≠ a) ∧ (pair x b ∈ L ∧ x ≠ b)

/-- **Section 13.9.** The set $`\mathrm{Int}` of all open intervals $`(a, b)` of the real
line with real end points. -/
def Int : ZFSet.{u} :=
  ZFSet.range fun p : ℝ × ℝ => ooIn F.R F.Le (F.real p.1) (F.real p.2)

/-- **Section 13.9.** The members of $`\mathrm{Int}` are the real intervals $`(r, s)`. -/
theorem mem_Int : A ∈ F.Int ↔ ∃ r s : ℝ, A = ooIn F.R F.Le (F.real r) (F.real s) := by
  rw [Int, mem_range]
  exact ⟨fun ⟨p, h⟩ => ⟨p.1, p.2, h.symm⟩, fun ⟨r, s, h⟩ => ⟨(r, s), h.symm⟩⟩

/-- **Section 13.9.** $`\mathrm{Int}` is a set of the universe. -/
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
third example of that section, the uniform partitions, needs arithmetic and is in part 7.
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
$`{}^*\mathbb N`. The base case is $`0` because the formalization's $`\mathbb N` starts at
$`0`; the book's $`\mathbb N` starts at $`1` and its base case is $`1 \in B`. -/
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

/-- The numerals $`0` and $`1` are different. -/
theorem num_zero_ne_one : (num 0 : ZFSet.{u}) ≠ num 1 := fun h => by
  have := num_injective h
  omega

/-- The pairs of a characteristic function: $`(a, 1)` for $`a \in B` and $`(a, 0)` for $`a \in A -
B`. -/
theorem pair_mem_chi {A B a c : ZFSet.{u}} :
    pair a c ∈ chi A B ↔ (a ∈ B ∧ c = num 1) ∨ (a ∈ A ∧ a ∉ B ∧ c = num 0) := by
  simp [chi, and_assoc]

/-- The characteristic function of a subset of $`A` is a set of pairs from $`A \times \{0, 1\}`.
-/
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

end Goldblatt
