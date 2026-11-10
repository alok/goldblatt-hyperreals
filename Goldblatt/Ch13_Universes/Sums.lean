import Goldblatt.Ch13_Universes.Hyperfinite

/-!
# 13 (part 6). Arithmetic in a Framework and Hyperfinite Sums

This is the last of six parts of Chapter 13 (the overview is on the chapter page
{lit}`Goldblatt.Ch13_Universes`). It covers the places where the book uses the arithmetic of
the real numbers inside a framework: the example at the end of Section 13.8 of a function
whose transform does not extend it, the uniform partitions that illustrate Sections 13.10,
13.15 and 13.16, hyperfinite summation (Section 13.19) and the exercises on hyperfinite sums
(Section 13.20).

The sections of this page follow the book's order. The page as a whole comes after part 5
because every item here needs the real numbers introduced there, and the sums need the
hyperfinite sets of Section 13.17.
-/

noncomputable section

namespace Goldblatt

open ZFSet

universe u

namespace RealFramework

open Formula Term NonstandardFramework

variable (F : RealFramework.{u}) {A B C D T f g h a b c n x y p : ZFSet.{u}}

/-!
## 13.8 Nonstandard Frameworks: operations on the real numbers

Section 13.8 observes that when the real numbers are individuals, the operations and
relations on them are entities of $`\mathbb U`, so each has a transform. A binary operation
is the set of pairs $`((r, s), t)` with $`t` the value at $`(r, s)`; its transform is a
function from $`{}^*\mathbb R \times {}^*\mathbb R` to $`{}^*\mathbb R` which agrees with the
operation on real arguments.
-/

/-- **Section 13.8.** The real number represented by an individual of the framework (and an
arbitrary real number for a set that represents none). -/
def toReal (a : ZFSet.{u}) : ℝ := Function.invFun F.real a

/-- **Section 13.8.** The individual representing $`r` represents $`r`. -/
@[simp]
theorem toReal_real (r : ℝ) : F.toReal (F.real r) = r :=
  Function.leftInverse_invFun F.real_injective r

/-- **Section 13.8, operations as entities.** A binary operation on the real numbers, as the
set of all pairs $`((r, s), r \circ s)` in the universe. -/
def binFn (op : ℝ → ℝ → ℝ) : ZFSet.{u} :=
  ZFSet.range fun q : ℝ × ℝ => pair (pair (F.real q.1) (F.real q.2)) (F.real (op q.1 q.2))

variable {op : ℝ → ℝ → ℝ}

/-- **Section 13.8.** The members of a binary operation are the pairs
$`((r, s), r \circ s)`. -/
theorem mem_binFn :
    p ∈ F.binFn op ↔ ∃ r s : ℝ, p = pair (pair (F.real r) (F.real s)) (F.real (op r s)) := by
  rw [binFn, mem_range]
  exact ⟨fun ⟨q, h⟩ => ⟨q.1, q.2, h.symm⟩, fun ⟨r, s, h⟩ => ⟨(r, s), h.symm⟩⟩

/-- **Section 13.8.** The value of a binary operation at a pair of real numbers. -/
theorem pair_mem_binFn {r s : ℝ} :
    pair (pair (F.real r) (F.real s)) c ∈ F.binFn op ↔ c = F.real (op r s) := by
  rw [mem_binFn]
  constructor
  · rintro ⟨r', s', h⟩
    obtain ⟨h1, h2⟩ := pair_inj.1 h
    obtain ⟨h3, h4⟩ := pair_inj.1 h1
    rw [h2, F.real_injective h3, F.real_injective h4]
  · exact fun h => ⟨r, s, by rw [h]⟩

/-- **Section 13.8.** A binary operation on the real numbers is a function from
$`\mathbb R \times \mathbb R` to $`\mathbb R`. -/
theorem isFunc_binFn (op : ℝ → ℝ → ℝ) : IsFunc (prod F.R F.R) F.R (F.binFn op) := by
  refine ⟨fun p hp => ?_, fun z hz => ?_⟩
  · obtain ⟨r, s, rfl⟩ := F.mem_binFn.1 hp
    exact pair_mem_prod.2 ⟨pair_mem_prod.2 ⟨F.mem_R.2 ⟨r, rfl⟩, F.mem_R.2 ⟨s, rfl⟩⟩,
      F.mem_R.2 ⟨_, rfl⟩⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 hz
    obtain ⟨r, rfl⟩ := F.mem_R.1 ha
    obtain ⟨s, rfl⟩ := F.mem_R.1 hb
    exact ⟨F.real (op r s), F.pair_mem_binFn.2 rfl, fun w hw => F.pair_mem_binFn.1 hw⟩

/-- **Section 13.8.** Every binary operation on the real numbers is an entity of the
universe. -/
theorem isSetOf_binFn (op : ℝ → ℝ → ℝ) : IsSetOf F.U (F.binFn op) :=
  F.hU.isSetOf_of_isFunc (F.hU.isSetOf_prod F.isSetOf_R F.isSetOf_R) F.isSetOf_R
    (F.isFunc_binFn op)

/-- **Section 13.8.** The transform of a binary operation on $`\mathbb R` is a function from
$`{}^*\mathbb R \times {}^*\mathbb R` to $`{}^*\mathbb R`. -/
theorem isFunc_star_binFn (op : ℝ → ℝ → ℝ) :
    IsFunc (prod (F.star F.R) (F.star F.R)) (F.star F.R) (F.star (F.binFn op)) := by
  have := F.isFunc_star (F.hU.isSetOf_prod F.isSetOf_R F.isSetOf_R) F.isSetOf_R
    (F.isFunc_binFn op)
  rwa [F.star_prod F.isSetOf_R F.isSetOf_R] at this

/-- **Section 13.8, transformed operations.** The value $`a \mathbin{{}^*\!\circ} b` of the
transform of a binary operation at two hyperreal numbers. -/
def hop (op : ℝ → ℝ → ℝ) (a b : ZFSet.{u}) : ZFSet.{u} := app (F.star (F.binFn op)) (pair a b)

/-- **Section 13.8.** The sum $`a + b` of two hyperreal numbers: the value of the transform
of addition. As in the book, the star is dropped from the name. -/
def hadd (a b : ZFSet.{u}) : ZFSet.{u} := F.hop (· + ·) a b

/-- **Section 13.8.** The product $`a b` of two hyperreal numbers: the value of the transform
of multiplication. -/
def hmul (a b : ZFSet.{u}) : ZFSet.{u} := F.hop (· * ·) a b

/-- **Section 13.8.** The pair $`((a, b), a \circ b)` belongs to the transformed
operation. -/
theorem pair_hop_mem (ha : a ∈ F.star F.R) (hb : b ∈ F.star F.R) :
    pair (pair a b) (F.hop op a b) ∈ F.star (F.binFn op) := by
  have hf := F.isFunc_star_binFn op
  exact hf.isFunction.pair_app_mem (hf.dom_eq ▸ pair_mem_prod.2 ⟨ha, hb⟩)

/-- **Section 13.8.** A transformed operation takes hyperreal numbers to hyperreal
numbers. -/
theorem hop_mem (ha : a ∈ F.star F.R) (hb : b ∈ F.star F.R) : F.hop op a b ∈ F.star F.R :=
  (pair_mem_prod.1 ((F.isFunc_star_binFn op).1 (F.pair_hop_mem ha hb))).2

/-- **Section 13.8.** The value of a transformed operation is determined by membership in
the transformed set of pairs. -/
theorem hop_eq_of_mem (hmem : pair (pair a b) c ∈ F.star (F.binFn op)) : F.hop op a b = c :=
  (F.isFunc_star_binFn op).isFunction.app_eq hmem

/-- **Section 13.8.** On real numbers a transformed operation agrees with the operation:
dropping the star is harmless for functions between individuals. -/
theorem hop_real (r s : ℝ) : F.hop op (F.real r) (F.real s) = F.real (op r s) := by
  refine F.hop_eq_of_mem ?_
  have hp := (F.hU.isSetOf_opair (F.real_mem_U r) (F.real_mem_U s)).1
  have := (F.star_mem_star_iff (F.hU.isSetOf_opair hp (F.real_mem_U (op r s))).1
    (F.isSetOf_binFn op).1).2 (F.pair_mem_binFn.2 rfl)
  rwa [F.star_opair hp (F.real_mem_U _), F.star_opair (F.real_mem_U r) (F.real_mem_U s),
    F.star_real, F.star_real, F.star_real] at this

/-- **Section 13.8.** The real numbers are hyperreal numbers. -/
theorem R_subset_star : F.R ⊆ F.star F.R := (F.subset_star_of_subset_base F.R_subset_base).1

/-- **Section 13.8.** Every real number is a hyperreal number. -/
theorem real_mem_star (r : ℝ) : F.real r ∈ F.star F.R := F.R_subset_star (F.mem_R.2 ⟨r, rfl⟩)

/-- **Section 13.8.** The hypernatural numbers are hyperreal numbers. -/
theorem star_N_subset_star_R : F.star F.N ⊆ F.star F.R :=
  (F.star_subset_star_iff F.isSetOf_N F.isSetOf_R).2 fun a ha => by
    obtain ⟨k, rfl⟩ := F.mem_N.1 ha
    exact F.mem_R.2 ⟨k, rfl⟩

/-!
### A function whose transform does not extend it

For functions and relations between individuals the star may be dropped, because the
transform agrees with the original on standard arguments. For a function whose values are
sets this fails. The book's example is the function $`f` taking a real number $`r` to the
ray $`\{x \in \mathbb R : x > r\}`: the value of $`{}^*f` at $`r` is the ray of hyperreals
above $`r`, which is larger than $`f(r)` as soon as there are nonstandard hyperreals.
-/

/-- **Section 13.8, example.** The ray $`f(r) = \{x \in \mathbb R : x > r\}`, where
$`x > r` is written as $`r \le x` and $`x \ne r`. -/
def upperRay (r : ℝ) : ZFSet.{u} := F.R.sep fun x => pair (F.real r) x ∈ F.Le ∧ x ≠ F.real r

/-- **Section 13.8, example.** The function $`f : \mathbb R \to \mathcal P(\mathbb R)`,
$`f(r) = \{x \in \mathbb R : x > r\}`, as a set of pairs in the universe. -/
def rayFn : ZFSet.{u} := ZFSet.range fun r : ℝ => pair (F.real r) (F.upperRay r)

/-- **Section 13.8, example.** The ray function is a function from $`\mathbb R` to
$`\mathcal P(\mathbb R)`. -/
theorem isFunc_rayFn : IsFunc F.R (powerset F.R) F.rayFn := by
  refine ⟨fun p hp => ?_, fun z hz => ?_⟩
  · obtain ⟨r, rfl⟩ := mem_range.1 hp
    exact pair_mem_prod.2 ⟨F.mem_R.2 ⟨r, rfl⟩, mem_powerset.2 sep_subset⟩
  · obtain ⟨r, rfl⟩ := F.mem_R.1 hz
    refine ⟨F.upperRay r, mem_range.2 ⟨r, rfl⟩, fun w hw => ?_⟩
    obtain ⟨s, hs⟩ := mem_range.1 hw
    obtain ⟨h1, h2⟩ := pair_inj.1 hs
    rw [← h2, F.real_injective h1]

/-- **Section 13.8, example.** The value of the ray function at $`r` is the ray above
$`r`. -/
theorem app_rayFn (r : ℝ) : app F.rayFn (F.real r) = F.upperRay r :=
  F.isFunc_rayFn.isFunction.app_eq (mem_range.2 ⟨r, rfl⟩)

/-- **Section 13.8, example.** The transform of the ray $`\{x \in \mathbb R : x > r\}` is the
ray $`\{x \in {}^*\mathbb R : x > r\}` of hyperreal numbers. -/
theorem star_upperRay (r : ℝ) :
    F.star (F.upperRay r) =
      (F.star F.R).sep fun x => pair (F.real r) x ∈ F.star F.Le ∧ x ≠ F.real r := by
  ext x
  have := F.mem_star_sep F.isSetOf_R
    (.conj (.elem (.opair (.const (F.real r)) (.var 0)) (.const F.Le))
      (.neg (.equal (.var 0) (.const (F.real r)))))
    (by simp [F.real_mem_U, F.isSetOf_Le.1]) (C := F.upperRay r)
    (by intro a; sat_simp; rw [upperRay, mem_sep]) x
  sat_simp at this
  rw [F.star_real] at this
  rw [this, mem_sep]

/-- **Section 13.8, example.** For a real number $`r`,
$`{}^*f(r) = {}^*(f(r)) = \{x \in {}^*\mathbb R : x > r\}`. -/
theorem app_star_rayFn (r : ℝ) :
    app (F.star F.rayFn) (F.real r) = F.star (app F.rayFn (F.real r)) ∧
      app (F.star F.rayFn) (F.real r) =
        (F.star F.R).sep fun x => pair (F.real r) x ∈ F.star F.Le ∧ x ≠ F.real r := by
  have h := F.star_app F.isSetOf_R (F.hU.isSetOf_powerset F.isSetOf_R) F.isFunc_rayFn
    (F.mem_R.2 ⟨r, rfl⟩)
  rw [F.star_real] at h
  refine ⟨h.symm, ?_⟩
  rw [← h, F.app_rayFn, F.star_upperRay]

/-- **Section 13.8, example.** If there is a nonstandard hypernatural number, then
$`{}^*f(0) \ne f(0)`: the value of the transform at $`0` is the set of positive hyperreals,
which contains that hypernatural, while $`f(0)` is the set of positive reals. So the
transform of $`f` does not agree with $`f` on $`\mathbb R`. -/
theorem app_star_rayFn_ne (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) :
    app (F.star F.rayFn) (F.real 0) ≠ app F.rayFn (F.real 0) := by
  obtain ⟨n, hn, hnN⟩ := hω
  intro heq
  have h0 : F.nat 0 = F.real 0 := by simp [nat]
  have hmem : n ∈ app (F.star F.rayFn) (F.real 0) := by
    rw [(F.app_star_rayFn 0).2, mem_sep]
    refine ⟨F.star_N_subset_star_R hn, ?_, fun h => hnN (F.mem_N.2 ⟨0, h.trans h0.symm⟩)⟩
    rw [← h0]
    exact F.nat_le_of_nonstandard hn hnN 0
  rw [heq, F.app_rayFn] at hmem
  obtain ⟨r, rfl⟩ := F.mem_R.1 (mem_sep.1 hmem).1
  exact hnN (F.mem_N_of_standard (F.standard_of_mem_base (F.real_mem r)) hn)

/-!
## 13.10 Internal Entities: uniform partitions (also Sections 13.15 and 13.16)

The book illustrates internal sets three times with the same example, the uniform partition
$`P_n^{[a, b]} = \{a + k(b - a)/n : k \in {}^*\mathbb Z,\ 0 \le k \le n\}` of a hyperreal
interval into $`n` parts, for hyperreal $`a, b` and a hypernatural $`n`. It is internal
because it belongs to $`{}^*\mathcal P(\mathbb R)` (Section 13.10), because it is defined by
an internal formula (Section 13.15), and because it is the image of an internal function
(Section 13.16). All three arguments are carried out here. The partition points
$`a + k(b - a)/n` are formed with a single function of the universe, taking
$`((a, b), (n, k))` to that real number, in place of the composite of addition,
multiplication and division; the index $`k` ranges over the hypernaturals up to $`n`, which
are the hyperintegers between $`0` and $`n`, since the natural numbers of the formalization
start at $`0`.
-/

/-- **Section 13.10, partition points.** The function taking $`((a, b), (n, k))` to the
partition point $`a + k(b - a)/n`, as a set of pairs in the universe. -/
def partFn : ZFSet.{u} :=
  ZFSet.range fun q : (ℝ × ℝ) × (ℕ × ℕ) =>
    pair (pair (pair (F.real q.1.1) (F.real q.1.2)) (pair (F.nat q.2.1) (F.nat q.2.2)))
      (F.real (q.1.1 + q.2.2 * (q.1.2 - q.1.1) / q.2.1))

/-- **Section 13.10.** The value of the partition point function. -/
theorem pair_mem_partFn {r s : ℝ} {i j : ℕ} :
    pair (pair (pair (F.real r) (F.real s)) (pair (F.nat i) (F.nat j))) c ∈ F.partFn ↔
      c = F.real (r + j * (s - r) / i) := by
  rw [partFn, mem_range]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨h1, h2⟩ := pair_inj.1 hq
    obtain ⟨h3, h4⟩ := pair_inj.1 h1
    obtain ⟨h5, h6⟩ := pair_inj.1 h3
    obtain ⟨h7, h8⟩ := pair_inj.1 h4
    rw [← h2, F.real_injective h5, F.real_injective h6, F.nat_injective h7, F.nat_injective h8]
  · rintro rfl
    exact ⟨((r, s), (i, j)), rfl⟩

/-- **Section 13.10.** The partition point function is a function from
$`(\mathbb R \times \mathbb R) \times (\mathbb N \times \mathbb N)` to $`\mathbb R`. -/
theorem isFunc_partFn :
    IsFunc (prod (prod F.R F.R) (prod F.N F.N)) F.R F.partFn := by
  refine ⟨fun p hp => ?_, fun z hz => ?_⟩
  · obtain ⟨q, rfl⟩ := mem_range.1 hp
    exact pair_mem_prod.2 ⟨pair_mem_prod.2 ⟨pair_mem_prod.2 ⟨F.mem_R.2 ⟨_, rfl⟩,
      F.mem_R.2 ⟨_, rfl⟩⟩, pair_mem_prod.2 ⟨F.mem_N.2 ⟨_, rfl⟩, F.mem_N.2 ⟨_, rfl⟩⟩⟩,
      F.mem_R.2 ⟨_, rfl⟩⟩
  · obtain ⟨ab, hab, nk, hnk, rfl⟩ := mem_prod.1 hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 hab
    obtain ⟨n, hn, k, hk, rfl⟩ := mem_prod.1 hnk
    obtain ⟨r, rfl⟩ := F.mem_R.1 ha
    obtain ⟨s, rfl⟩ := F.mem_R.1 hb
    obtain ⟨i, rfl⟩ := F.mem_N.1 hn
    obtain ⟨j, rfl⟩ := F.mem_N.1 hk
    exact ⟨_, F.pair_mem_partFn.2 rfl, fun w hw => F.pair_mem_partFn.1 hw⟩

/-- The domain of the partition point function is a set of the universe. -/
theorem isSetOf_partDom : IsSetOf F.U (prod (prod F.R F.R) (prod F.N F.N)) :=
  F.hU.isSetOf_prod (F.hU.isSetOf_prod F.isSetOf_R F.isSetOf_R)
    (F.hU.isSetOf_prod F.isSetOf_N F.isSetOf_N)

/-- **Section 13.10.** The partition point function is an entity of the universe. -/
theorem isSetOf_partFn : IsSetOf F.U F.partFn :=
  F.hU.isSetOf_of_isFunc F.isSetOf_partDom F.isSetOf_R F.isFunc_partFn

/-- **Section 13.10.** The transform of the partition point function is a function from
$`({}^*\mathbb R \times {}^*\mathbb R) \times ({}^*\mathbb N \times {}^*\mathbb N)` to
$`{}^*\mathbb R`. -/
theorem isFunc_star_partFn :
    IsFunc (prod (prod (F.star F.R) (F.star F.R)) (prod (F.star F.N) (F.star F.N)))
      (F.star F.R) (F.star F.partFn) := by
  have := F.isFunc_star F.isSetOf_partDom F.isSetOf_R F.isFunc_partFn
  rwa [F.star_prod (F.hU.isSetOf_prod F.isSetOf_R F.isSetOf_R)
    (F.hU.isSetOf_prod F.isSetOf_N F.isSetOf_N), F.star_prod F.isSetOf_R F.isSetOf_R,
    F.star_prod F.isSetOf_N F.isSetOf_N] at this

/-- **Section 13.10, uniform partitions.** The uniform partition
$`P_n^{[a, b]} = \{a + k(b - a)/n : 0 \le k \le n\}` determined by hyperreals $`a, b` and a
hypernatural $`n`: the set of hyperreals $`x` such that $`x` is the partition point of some
hypernatural $`k \le n`. -/
def partition (a b n : ZFSet.{u}) : ZFSet.{u} :=
  (F.star F.R).sep fun x => ∃ k ∈ F.star F.N, pair k n ∈ F.star F.Le ∧
    pair (pair (pair a b) (pair n k)) x ∈ F.star F.partFn

/-- **Section 13.10.** Every uniform partition belongs to $`{}^*\mathcal P(\mathbb R)`, by
transfer of the statement that for all real $`a, b` and natural $`n` there is a set of real
numbers consisting of the partition points. -/
theorem partition_mem_star_powerset (ha : a ∈ F.star F.R) (hb : b ∈ F.star F.R)
    (hn : n ∈ F.star F.N) : F.partition a b n ∈ F.star (powerset F.R) := by
  have hPR := F.hU.isSetOf_powerset F.isSetOf_R
  have htr := F.transfer
    (.all 1 (.const F.R) (.all 2 (.const F.R) (.all 3 (.const F.N) (.ex 0 (.const (powerset F.R))
      (.all 4 (.const F.R) (.biimp (.elem (.var 4) (.var 0))
        (.ex 5 (.const F.N) (.conj (.elem (.opair (.var 5) (.var 3)) (.const F.Le))
          (.elem (.opair (.opair (.opair (.var 1) (.var 2)) (.opair (.var 3) (.var 5)))
            (.var 4)) (.const F.partFn))))))))))
    (by simp [IsSentence, hPR.1, F.isSetOf_R.1, F.isSetOf_N.1, F.isSetOf_Le.1,
      F.isSetOf_partFn.1])
  sat_simp at htr
  have hRU' := F.star_subset_U' F.isSetOf_R
  have hNU' := F.star_subset_U' F.isSetOf_N
  obtain ⟨P, -, hP, hPmem⟩ := htr.1 (by
    intro a' _ _ b' _ _ n' _ _
    refine ⟨F.R.sep fun x => ∃ k ∈ F.U, k ∈ F.N ∧ pair k n' ∈ F.Le ∧
      pair (pair (pair a' b') (pair n' k)) x ∈ F.partFn, (F.hU.isSetOf_sep F.isSetOf_R _).1,
      mem_powerset.2 sep_subset, fun x _ hx => ?_⟩
    rw [mem_sep]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩) a (hRU' ha) ha b (hRU' hb) hb n (hNU' hn) hn
  have hPsub := mem_powerset.1 (F.star_powerset_subset F.isSetOf_R hP)
  have : F.partition a b n = P := by
    ext x
    rw [partition, mem_sep]
    constructor
    · rintro ⟨hx, k, hk, h⟩
      exact (hPmem x (hRU' hx) hx).2 ⟨k, hNU' hk, hk, h⟩
    · intro hx
      obtain ⟨k, -, hk, h⟩ := (hPmem x (hRU' (hPsub hx)) (hPsub hx)).1 hx
      exact ⟨hPsub hx, k, hk, h⟩
  rw [this]
  exact hP

/-- **Section 13.10.** Every uniform partition is an internal subset of
$`{}^*\mathbb R`. -/
theorem internal_partition (ha : a ∈ F.star F.R) (hb : b ∈ F.star F.R) (hn : n ∈ F.star F.N) :
    F.partition a b n ⊆ F.star F.R ∧ F.Internal (F.partition a b n) :=
  (F.mem_star_powerset_iff F.isSetOf_R).1 (F.partition_mem_star_powerset ha hb hn)

/-- **Section 13.15, illustration.** The uniform partition is internal by the internal set
definition principle: it is the subset of the internal set $`{}^*\mathbb R` defined by the
internal formula "$`x` is the partition point of some $`k \le n`", whose parameters
$`a, b, n` are internal. -/
theorem internal_partition_of_definition (ha : a ∈ F.star F.R) (hb : b ∈ F.star F.R)
    (hn : n ∈ F.star F.N) : F.Internal (F.partition a b n) := by
  have hv : ∀ y ∈ [1, 2, 3], F.Internal (Function.update (Function.update
      (Function.update (fun _ => (∅ : ZFSet.{u})) 1 a) 2 b) 3 n y) := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · simpa using F.internal_of_mem_star F.isSetOf_R ha
    · simpa using F.internal_of_mem_star F.isSetOf_R hb
    · simpa using F.internal_of_mem_star F.isSetOf_N hn
  have := F.internal_sep
    (.ex 5 (.const F.N) (.conj (.elem (.opair (.var 5) (.var 3)) (.const F.Le))
      (.elem (.opair (.opair (.opair (.var 1) (.var 2)) (.opair (.var 3) (.var 5)))
        (.var 0)) (.const F.partFn)))) [1, 2, 3] 0
    (by simp [F.isSetOf_N.1, F.isSetOf_Le.1, F.isSetOf_partFn.1]) _ hv
    (F.internal_star F.isSetOf_R.1) (F.isSetOf_star F.isSetOf_R)
  sat_simp at this
  have e : F.partition a b n = (F.star F.R).sep fun x => ∃ k ∈ F.U', k ∈ F.star F.N ∧
      pair k n ∈ F.star F.Le ∧ pair (pair (pair a b) (pair n k)) x ∈ F.star F.partFn := by
    ext x
    rw [partition, mem_sep, mem_sep]
    exact ⟨fun ⟨hx, k, hk, h⟩ => ⟨hx, k, F.star_subset_U' F.isSetOf_N hk, hk, h⟩,
      fun ⟨hx, k, _, hk, h⟩ => ⟨hx, k, hk, h⟩⟩
  rw [e]
  exact this

/-- **Section 13.16, illustration.** The uniform partition is the image of an internal
function: the function on $`\{k \in {}^*\mathbb N : k \le n\}` defined by the internal term
$`a + x(b - a)/n` is internal by the internal function definition principle, and its range is
the partition. -/
theorem partition_eq_ran_internal (ha : a ∈ F.star F.R) (hb : b ∈ F.star F.R)
    (hn : n ∈ F.star F.N) :
    ∃ f, F.Internal f ∧
      IsFunc ((F.star F.N).sep fun k => pair k n ∈ F.star F.Le) (F.star F.R) f ∧
      (∀ k ∈ dom f, app f k = app (F.star F.partFn) (pair (pair a b) (pair n k))) ∧
      ran f = F.partition a b n := by
  set A : ZFSet.{u} := (F.star F.N).sep fun k => pair k n ∈ F.star F.Le with hAdef
  set f : ZFSet.{u} := (prod A (F.star F.R)).sep fun p => ∃ k y, p = pair k y ∧
    pair (pair (pair a b) (pair n k)) y ∈ F.star F.partFn with hfdef
  have hpf := F.isFunc_star_partFn
  have hmem : ∀ k y, pair k y ∈ f ↔ k ∈ A ∧ y ∈ F.star F.R ∧
      pair (pair (pair a b) (pair n k)) y ∈ F.star F.partFn := fun k y => by
    rw [hfdef, mem_sep, pair_mem_prod]
    constructor
    · rintro ⟨⟨hk, hy⟩, k', y', hp, h⟩
      obtain ⟨rfl, rfl⟩ := pair_inj.1 hp
      exact ⟨hk, hy, h⟩
    · rintro ⟨hk, hy, h⟩
      exact ⟨⟨hk, hy⟩, k, y, rfl, h⟩
  have harg : ∀ k ∈ A, pair (pair a b) (pair n k) ∈ dom (F.star F.partFn) := fun k hk => by
    rw [hpf.dom_eq]
    exact pair_mem_prod.2 ⟨pair_mem_prod.2 ⟨ha, hb⟩, pair_mem_prod.2 ⟨hn, (mem_sep.1 hk).1⟩⟩
  have hpt : ∀ k ∈ A, pair k (app (F.star F.partFn) (pair (pair a b) (pair n k))) ∈ f :=
    fun k hk => by
      have h := hpf.isFunction.pair_app_mem (harg k hk)
      exact (hmem _ _).2 ⟨hk, (pair_mem_prod.1 (hpf.1 h)).2, h⟩
  have hfunc : IsFunc A (F.star F.R) f :=
    ⟨sep_subset, fun k hk => ⟨_, hpt k hk, fun w hw =>
      hpf.isFunction.2 _ _ _ ((hmem _ _).1 hw).2.2 ((hmem _ _).1 (hpt k hk)).2.2⟩⟩
  have happ : ∀ k ∈ A, app f k = app (F.star F.partFn) (pair (pair a b) (pair n k)) :=
    fun k hk => hfunc.isFunction.app_eq (hpt k hk)
  have hAint : F.Internal A := by
    have := F.internal_sep (.elem (.opair (.var 0) (.var 1)) (.const F.Le)) [1] 0
      (by simp [F.isSetOf_Le.1]) (fun _ => n)
      (by simpa using F.internal_of_mem_star F.isSetOf_N hn) (F.internal_star F.isSetOf_N.1)
      (F.isSetOf_star F.isSetOf_N)
    sat_simp at this
    exact this
  have hAset : IsSetOf F.U' A := isSetOf_of_subset hAint.mem_U' fun k hk =>
    F.star_subset_U' F.isSetOf_N (mem_sep.1 hk).1
  have hv : ∀ y ∈ [1, 2, 3], F.Internal (Function.update (Function.update
      (Function.update (fun _ => (∅ : ZFSet.{u})) 1 a) 2 b) 3 n y) := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · simpa using F.internal_of_mem_star F.isSetOf_R ha
    · simpa using F.internal_of_mem_star F.isSetOf_R hb
    · simpa using F.internal_of_mem_star F.isSetOf_N hn
  have hfint : F.Internal f := F.internal_of_term
    (.app (.const F.partFn) (.opair (.opair (.var 1) (.var 2)) (.opair (.var 3) (.var 0))))
    [1, 2, 3] 0 (by simp [F.isSetOf_partFn.1]) _ hv hAint hAset
    (F.internal_star F.isSetOf_R.1) (F.isSetOf_star F.isSetOf_R) hfunc fun k hk => by
      sat_simp
      exact ⟨⟨hpf.isFunction, F.relIn_star F.isSetOf_partFn
        (F.hU.relIn_of_subset_prod F.isSetOf_partDom F.isSetOf_R F.isFunc_partFn.1),
        harg k hk⟩, happ k hk⟩
  refine ⟨f, hfint, hfunc, fun k hk => happ k (hfunc.dom_eq ▸ hk), ?_⟩
  ext y
  rw [mem_ran, partition, mem_sep]
  constructor
  · rintro ⟨k, hky⟩
    obtain ⟨hk, hy, h⟩ := (hmem k y).1 hky
    exact ⟨hy, k, (mem_sep.1 hk).1, (mem_sep.1 hk).2, h⟩
  · rintro ⟨hy, k, hk, hkn, h⟩
    exact ⟨k, (hmem k y).2 ⟨mem_sep.2 ⟨hk, hkn⟩, hy, h⟩⟩

/-!
## 13.19 Hyperfinite Summation

Summation of finite sets of real numbers is a function from $`\mathcal P_F(\mathbb R)` to
$`\mathbb R` in the universe. Its transform is an internal function from
$`{}^*\mathcal P_F(\mathbb R)` to $`{}^*\mathbb R`, and this gives a meaning to the sum of
every hyperfinite set of hyperreals ({lit}`RealFramework.hsum`).

The book then defines the sum of an internal function $`f` over a hyperfinite set $`B` as
the sum of the hyperfinite set $`f(B)`. Read literally, that is the sum of the _set_ of
values, which counts a value taken several times only once, so it is the intended sum only
when $`f` is injective on $`B`; the properties listed in Section 13.20 fail for it otherwise
(additivity already fails for two constant functions). The formalization therefore follows
the corrected definition: the operator that sums a real-valued function over a finite set is
itself a function of the universe, defined on pairs of a set of pairs and a finite set, and
the sum of an internal function over a hyperfinite set is the value of its transform
({lit}`RealFramework.hfsum`). For a function that is injective on $`B` this is the book's
$`\sum f(B)` ({lit}`RealFramework.hfsum_eq_hsum_relImage`).

The functions summed are subsets of $`T \times \mathbb R` for a set $`T` of the universe, and
the hyperfinite sets are members of $`{}^*\mathcal P_F(T)`. Every internal function with
hyperreal values and every hyperfinite subset of its domain arise in this way for a suitable
$`T` ({lit}`RealFramework.exists_ambient_sum`).
-/

/-- **Section 13.19.** The summation function $`\mathcal P_F(\mathbb R) \to \mathbb R`,
$`B \mapsto \sum B`, as a set of pairs in the universe. -/
def sumFn : ZFSet.{u} :=
  ZFSet.range fun Z : (finPow F.R : ZFSet.{u}) =>
    pair (Z : ZFSet.{u}) (F.real (∑ᶠ r ∈ {r : ℝ | F.real r ∈ (Z : ZFSet.{u})}, r))

/-- **Section 13.19.** Summation of finite sets of real numbers is a function from
$`\mathcal P_F(\mathbb R)` to $`\mathbb R`. -/
theorem isFunc_sumFn : IsFunc (finPow F.R) F.R F.sumFn :=
  isFunc_graph _ _ _ fun _ => F.mem_R.2 ⟨_, rfl⟩

/-- **Section 13.19, hyperfinite sums.** The sum $`\sum B` of a hyperfinite set
$`B \subseteq {}^*\mathbb R`: the value at $`B` of the transform of the summation
function. -/
def hsum (B : ZFSet.{u}) : ZFSet.{u} := app (F.star F.sumFn) B

/-- **Section 13.19.** Summation transforms to an internal function from
$`{}^*\mathcal P_F(\mathbb R)` to $`{}^*\mathbb R`. -/
theorem isFunc_star_sumFn :
    IsFunc (F.star (finPow F.R)) (F.star F.R) (F.star F.sumFn) ∧ F.Internal (F.star F.sumFn) :=
  ⟨F.isFunc_star (F.hU.isSetOf_finPow F.isSetOf_R) F.isSetOf_R F.isFunc_sumFn,
    F.internal_star (F.hU.isSetOf_of_isFunc (F.hU.isSetOf_finPow F.isSetOf_R) F.isSetOf_R
      F.isFunc_sumFn).1⟩

/-- **Section 13.19.** The sum of a hyperfinite set of hyperreals is a hyperreal. -/
theorem hsum_mem (hB : F.Hyperfinite B) (hBR : B ⊆ F.star F.R) : F.hsum B ∈ F.star F.R := by
  have hf := F.isFunc_star_sumFn.1
  have hBF := hB.mem_star_finPow F.isSetOf_R hBR
  exact (pair_mem_prod.1 (hf.1 (hf.isFunction.pair_app_mem (hf.dom_eq ▸ hBF)))).2

/-- **Section 13.19.** On a finite set of real numbers the hyperfinite sum is the ordinary
sum. -/
theorem hsum_of_finite {Z : ZFSet.{u}} (hZ : Z ∈ finPow F.R) :
    F.hsum Z = F.real (∑ᶠ r ∈ {r : ℝ | F.real r ∈ Z}, r) := by
  have hZX : Z ⊆ F.X := fun y hy => F.R_subset_base ((mem_finPow.1 hZ).1 hy)
  have hstar : F.star Z = Z := F.star_eq_self_of_finite_subset_base hZX (mem_finPow.1 hZ).2
  have h := F.star_app (F.hU.isSetOf_finPow F.isSetOf_R) F.isSetOf_R F.isFunc_sumFn hZ
  rw [hstar] at h
  rw [hsum, ← h]
  have : app F.sumFn Z = F.real (∑ᶠ r ∈ {r : ℝ | F.real r ∈ Z}, r) :=
    app_graph (finPow F.R) F.R _ (fun _ => F.mem_R.2 ⟨_, rfl⟩) ⟨Z, hZ⟩
  rw [this, F.star_real]

/-- **Section 13.19, sums of functions over finite sets.** The real number
$`\sum_{a \in B} g(a)` for a set of pairs $`g` with real values and a finite set $`B`; each
value $`g(a)` is read as a real number by {lit}`RealFramework.toReal`. -/
def fsum (g B : ZFSet.{u}) : ℝ := ∑ᶠ a ∈ (B : Set ZFSet.{u}), F.toReal (app g a)

/-- **Section 13.19, the summation operator.** The function taking a pair $`(g, B)`, with
$`g \subseteq T \times \mathbb R` and $`B` a finite subset of $`T`, to the sum
$`\sum_{a \in B} g(a)`, as a set of pairs in the universe. -/
def fsumFn (T : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun q : (powerset (prod T F.R) : ZFSet.{u}) × (finPow T : ZFSet.{u}) =>
    pair (pair (q.1 : ZFSet.{u}) (q.2 : ZFSet.{u})) (F.real (F.fsum q.1 q.2))

/-- **Section 13.19.** The members of the summation operator are the pairs
$`((g, B), \sum_{a \in B} g(a))`. -/
theorem pair_mem_fsumFn {s : ZFSet.{u}} :
    pair (pair g B) s ∈ F.fsumFn T ↔
      g ∈ powerset (prod T F.R) ∧ B ∈ finPow T ∧ s = F.real (F.fsum g B) := by
  rw [fsumFn, mem_range]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨h1, h2⟩ := pair_inj.1 hq
    obtain ⟨h3, h4⟩ := pair_inj.1 h1
    subst h3 h4
    exact ⟨q.1.2, q.2.2, h2.symm⟩
  · rintro ⟨hg, hB, rfl⟩
    exact ⟨(⟨g, hg⟩, ⟨B, hB⟩), rfl⟩

/-- **Section 13.19.** The summation operator is a function from
$`\mathcal P(T \times \mathbb R) \times \mathcal P_F(T)` to $`\mathbb R`. -/
theorem isFunc_fsumFn (T : ZFSet.{u}) :
    IsFunc (prod (powerset (prod T F.R)) (finPow T)) F.R (F.fsumFn T) := by
  refine ⟨fun p hp => ?_, fun z hz => ?_⟩
  · obtain ⟨q, rfl⟩ := mem_range.1 hp
    exact pair_mem_prod.2 ⟨pair_mem_prod.2 ⟨q.1.2, q.2.2⟩, F.mem_R.2 ⟨_, rfl⟩⟩
  · obtain ⟨g, hg, B, hB, rfl⟩ := mem_prod.1 hz
    exact ⟨_, F.pair_mem_fsumFn.2 ⟨hg, hB, rfl⟩, fun w hw => (F.pair_mem_fsumFn.1 hw).2.2⟩

variable {F} in
/-- The domain of the summation operator is a set of the universe. -/
theorem isSetOf_sumDom (hT : IsSetOf F.U T) :
    IsSetOf F.U (prod (powerset (prod T F.R)) (finPow T)) :=
  F.hU.isSetOf_prod (F.hU.isSetOf_powerset (F.hU.isSetOf_prod hT F.isSetOf_R))
    (F.hU.isSetOf_finPow hT)

/-- **Section 13.19.** The summation operator is an entity of the universe. -/
theorem isSetOf_fsumFn (hT : IsSetOf F.U T) : IsSetOf F.U (F.fsumFn T) :=
  F.hU.isSetOf_of_isFunc (isSetOf_sumDom hT) F.isSetOf_R (F.isFunc_fsumFn T)

/-- **Section 13.19, sums of internal functions.** The sum $`\sum_{x \in B} f(x)` of an
internal function $`f \subseteq {}^*T \times {}^*\mathbb R` over a hyperfinite set
$`B \in {}^*\mathcal P_F(T)`: the value at $`(f, B)` of the transform of the summation
operator. The book's definition as $`\sum f(B)` is correct only for $`f` injective on $`B`;
see {lit}`RealFramework.hfsum_eq_hsum_relImage`. -/
def hfsum (T f B : ZFSet.{u}) : ZFSet.{u} := app (F.star (F.fsumFn T)) (pair f B)

/-- **Section 13.19.** The transform of the summation operator is an internal function from
$`{}^*\mathcal P(T \times \mathbb R) \times {}^*\mathcal P_F(T)` to $`{}^*\mathbb R`. -/
theorem isFunc_star_fsumFn (hT : IsSetOf F.U T) :
    IsFunc (prod (F.star (powerset (prod T F.R))) (F.star (finPow T))) (F.star F.R)
      (F.star (F.fsumFn T)) ∧ F.Internal (F.star (F.fsumFn T)) := by
  have hP := F.hU.isSetOf_powerset (F.hU.isSetOf_prod hT F.isSetOf_R)
  have := F.isFunc_star (isSetOf_sumDom hT) F.isSetOf_R (F.isFunc_fsumFn T)
  rw [F.star_prod hP (F.hU.isSetOf_finPow hT)] at this
  exact ⟨this, F.internal_star (F.isSetOf_fsumFn hT).1⟩

/-- **Section 13.19.** The pair $`((f, B), \sum_{x \in B} f(x))` belongs to the transformed
summation operator. -/
theorem pair_hfsum_mem (hT : IsSetOf F.U T) (hf : f ∈ F.star (powerset (prod T F.R)))
    (hB : B ∈ F.star (finPow T)) : pair (pair f B) (F.hfsum T f B) ∈ F.star (F.fsumFn T) := by
  have h := (F.isFunc_star_fsumFn hT).1
  exact h.isFunction.pair_app_mem (h.dom_eq ▸ pair_mem_prod.2 ⟨hf, hB⟩)

/-- **Section 13.19.** The sum of an internal function with hyperreal values over a
hyperfinite set is a hyperreal number. -/
theorem hfsum_mem (hT : IsSetOf F.U T) (hf : f ∈ F.star (powerset (prod T F.R)))
    (hB : B ∈ F.star (finPow T)) : F.hfsum T f B ∈ F.star F.R :=
  (pair_mem_prod.1 ((F.isFunc_star_fsumFn hT).1.1 (F.pair_hfsum_mem hT hf hB))).2

/-- **Section 13.19.** The sum is determined by membership in the transformed summation
operator. -/
theorem hfsum_eq_of_mem {s : ZFSet.{u}} (hT : IsSetOf F.U T)
    (hmem : pair (pair f B) s ∈ F.star (F.fsumFn T)) : F.hfsum T f B = s :=
  (F.isFunc_star_fsumFn hT).1.isFunction.app_eq hmem

/-- **Section 13.19.** On (the transforms of) a function and a finite set of the universe the
hyperfinite sum is the ordinary finite sum. -/
theorem hfsum_star (hT : IsSetOf F.U T) (hg : g ∈ powerset (prod T F.R))
    (hB : B ∈ finPow T) : F.hfsum T (F.star g) (F.star B) = F.real (F.fsum g B) := by
  have hP := F.hU.isSetOf_powerset (F.hU.isSetOf_prod hT F.isSetOf_R)
  have hgU := F.hU.subset hP hg
  have hBU := F.hU.subset (F.hU.isSetOf_finPow hT) hB
  have h := F.star_app (isSetOf_sumDom hT) F.isSetOf_R (F.isFunc_fsumFn T)
    (pair_mem_prod.2 ⟨hg, hB⟩)
  rw [F.star_opair hgU hBU] at h
  rw [hfsum, ← h, (F.isFunc_fsumFn T).isFunction.app_eq (F.pair_mem_fsumFn.2 ⟨hg, hB, rfl⟩),
    F.star_real]

/-- **Section 13.19.** A member of $`{}^*\mathcal P(T \times \mathbb R)` is an internal set
of pairs from $`{}^*T \times {}^*\mathbb R`, and conversely. -/
theorem mem_star_powerset_prod_iff (hT : IsSetOf F.U T) :
    f ∈ F.star (powerset (prod T F.R)) ↔
      f ⊆ prod (F.star T) (F.star F.R) ∧ F.Internal f := by
  rw [F.mem_star_powerset_iff (F.hU.isSetOf_prod hT F.isSetOf_R), F.star_prod hT F.isSetOf_R]

/-- **Section 13.19.** Every internal function $`f` with hyperreal values, together with a
hyperfinite subset $`B` of its domain, lies in the domain of the transformed summation
operator of some set $`T` of the universe. So $`\sum_{x \in B} f(x)` is defined in the
situation described by the book. -/
theorem exists_ambient_sum (hf : F.Internal f) (hrel : RelIn F.U' f)
    (hran : ran f ⊆ F.star F.R) (hB : F.Hyperfinite B) (hBf : B ⊆ dom f) :
    ∃ T, IsSetOf F.U T ∧ f ∈ F.star (powerset (prod T F.R)) ∧ B ∈ F.star (finPow T) := by
  have hfset : IsSetOf F.U' f := isSetOf_of_subset hf.mem_U' fun p hp => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hrel p hp
    exact (F.isUniverse'.isSetOf_opair ha hb).1
  obtain ⟨T, hT, -, -, hrelT⟩ := F.exists_ambient [f] (by simp [hf])
  have hfT := hrelT f (by simp) hfset hrel
  refine ⟨T, hT, (F.mem_star_powerset_prod_iff hT).2 ⟨fun p hp => ?_, hf⟩,
    hB.mem_star_finPow hT fun x hx => ?_⟩
  · obtain ⟨a, ha, b, -, rfl⟩ := mem_prod.1 (hfT hp)
    exact pair_mem_prod.2 ⟨ha, hran (mem_ran.2 ⟨a, hp⟩)⟩
  · obtain ⟨b, hb⟩ := mem_dom.1 (hBf hx)
    exact (pair_mem_prod.1 (hfT hb)).1

/-- **Section 13.19.** Enlarging the set $`T` does not change the sum: if $`T \subseteq T'`,
then the sum of $`f` over $`B` computed with the summation operator of $`T'` is the one
computed with that of $`T`. -/
theorem hfsum_mono_ambient {T' : ZFSet.{u}} (hT : IsSetOf F.U T) (hT' : IsSetOf F.U T')
    (hTT' : T ⊆ T') (hf : f ∈ F.star (powerset (prod T F.R))) (hB : B ∈ F.star (finPow T)) :
    F.hfsum T' f B = F.hfsum T f B := by
  have hP := F.hU.isSetOf_powerset (F.hU.isSetOf_prod hT F.isSetOf_R)
  have hFT := F.hU.isSetOf_finPow hT
  have htr := F.transfer
    (.all 0 (.const (powerset (prod T F.R))) (.all 1 (.const (finPow T)) (.all 2 (.const F.R)
      (.imp (.elem (.opair (.opair (.var 0) (.var 1)) (.var 2)) (.const (F.fsumFn T)))
        (.elem (.opair (.opair (.var 0) (.var 1)) (.var 2)) (.const (F.fsumFn T')))))))
    (by simp [IsSentence, hP.1, hFT.1, F.isSetOf_R.1, (F.isSetOf_fsumFn hT).1,
      (F.isSetOf_fsumFn hT').1])
  sat_simp at htr
  refine F.hfsum_eq_of_mem hT' (htr.1 ?_ f (F.star_subset_U' hP hf) hf B
    (F.star_subset_U' hFT hB) hB _ (F.star_subset_U' F.isSetOf_R (F.hfsum_mem hT hf hB))
    (F.hfsum_mem hT hf hB) (F.pair_hfsum_mem hT hf hB))
  intro g' _ hg' B' _ hB' s _ _ hs
  obtain ⟨-, -, rfl⟩ := F.pair_mem_fsumFn.1 hs
  refine F.pair_mem_fsumFn.2 ⟨mem_powerset.2 fun q hq => ?_, mem_finPow.2
    ⟨fun z hz => hTT' ((mem_finPow.1 hB').1 hz), (mem_finPow.1 hB').2⟩, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 (mem_powerset.1 hg' hq)
  exact pair_mem_prod.2 ⟨hTT' ha, hb⟩

/-- **Section 13.19.** The sum of an internal function over a hyperfinite set does not
depend on the set $`T` of the universe used to form the summation operator. -/
theorem hfsum_ambient_irrel {T' : ZFSet.{u}} (hT : IsSetOf F.U T) (hT' : IsSetOf F.U T')
    (hf : f ∈ F.star (powerset (prod T F.R))) (hB : B ∈ F.star (finPow T))
    (hf' : f ∈ F.star (powerset (prod T' F.R))) (hB' : B ∈ F.star (finPow T')) :
    F.hfsum T f B = F.hfsum T' f B := by
  have hU := F.hU.isSetOf_union hT hT'
  rw [← F.hfsum_mono_ambient hT hU (fun z hz => mem_union.2 (Or.inl hz)) hf hB,
    ← F.hfsum_mono_ambient hT' hU (fun z hz => mem_union.2 (Or.inr hz)) hf' hB']

/-!
## 13.20 Exercises on Hyperfinite Sums

The first exercise lists four properties of hyperfinite summation: homogeneity, additivity,
additivity over disjoint sets, and monotonicity. Each is the transfer of the corresponding
property of the summation operator on finite sets. The functions $`c f` and $`f + g` of the
book are represented by any internal function with the stated values on $`B`, since a sum
over $`B` depends only on the values on $`B`. The second exercise asks for indexed sums
$`\sum_{i=1}^n x_i` with $`n` unlimited: they are the sums of an internal sequence $`x` over
the hyperfinite initial segment $`\{1, \dots, n\}`.
-/

/-- The single-valuedness of the relation named by the variable $`g` between $`T` and $`R`,
as a bounded formula: $`(\forall a \in T)(\forall b, c \in R)\,((a, b) \in g \land
(a, c) \in g \to b = c)`. It uses the variables $`10, 11, 12`. -/
def _root_.Goldblatt.svF (T R : ZFSet.{u}) (g : ℕ) : Formula.{u} :=
  .all 10 (.const T) (.all 11 (.const R) (.all 12 (.const R) (.imp
    (.conj (.elem (.opair (.var 10) (.var 11)) (.var g))
      (.elem (.opair (.var 10) (.var 12)) (.var g)))
    (.equal (.var 11) (.var 12)))))

/-- A subset of $`A \times B` that is single-valued, in the bounded form produced by
{lit}`svF`, is a function. -/
theorem _root_.Goldblatt.isFunction_of_bounded {V : ZFSet.{u}} (hg : g ⊆ prod A B) (hA : A ⊆ V)
    (hB : B ⊆ V)
    (hsv : ∀ a ∈ V, a ∈ A → ∀ b ∈ V, b ∈ B → ∀ c ∈ V, c ∈ B →
      pair a b ∈ g ∧ pair a c ∈ g → b = c) : IsFunction g := by
  refine ⟨fun p hp => let ⟨a, _, b, _, h⟩ := mem_prod.1 (hg hp); ⟨a, b, h⟩, fun a b c hab hac => ?_⟩
  have h1 := pair_mem_prod.1 (hg hab)
  have h2 := pair_mem_prod.1 (hg hac)
  exact hsv a (hA h1.1) h1.1 b (hB h1.2) h1.2 c (hB h2.2) h2.2 ⟨hab, hac⟩

/-- The real number named by the value of a function at a point. -/
theorem toReal_app {r : ℝ} (hg : IsFunction g) (hmem : pair a (F.real r) ∈ g) :
    F.toReal (app g a) = r := by
  rw [hg.app_eq hmem, F.toReal_real]

/-- A member of $`{}^*\mathcal P(T \times \mathbb R)` that is a function takes each point of
its domain to a hyperreal number. -/
theorem pair_app_mem_of_mem_star (hT : IsSetOf F.U T) (hf : f ∈ F.star (powerset (prod T F.R)))
    (hfun : IsFunction f) (hx : x ∈ dom f) :
    pair x (app f x) ∈ f ∧ x ∈ F.U' ∧ app f x ∈ F.U' ∧ app f x ∈ F.star F.R := by
  have hmem := hfun.pair_app_mem hx
  have := pair_mem_prod.1 (((F.mem_star_powerset_prod_iff hT).1 hf).1 hmem)
  exact ⟨hmem, F.star_subset_U' hT this.1, F.star_subset_U' F.isSetOf_R this.2, this.2⟩

/-- **Exercise 13.20 (1), homogeneity.** $`\sum_{x \in B} c f(x) = c \sum_{x \in B} f(x)`
for an internal function $`f`, a hyperfinite set $`B` and a hyperreal number $`c`. Here
$`k` is any internal function with $`k(x) = c f(x)` on $`B`. -/
theorem hfsum_smul {k : ZFSet.{u}} (hT : IsSetOf F.U T)
    (hf : f ∈ F.star (powerset (prod T F.R))) (hk : k ∈ F.star (powerset (prod T F.R)))
    (hB : B ∈ F.star (finPow T)) (hc : c ∈ F.star F.R) (hffun : IsFunction f)
    (hkfun : IsFunction k) (hBf : B ⊆ dom f) (hBk : B ⊆ dom k)
    (hval : ∀ x ∈ B, app k x = F.hmul c (app f x)) :
    F.hfsum T k B = F.hmul c (F.hfsum T f B) := by
  have hP := F.hU.isSetOf_powerset (F.hU.isSetOf_prod hT F.isSetOf_R)
  have hFT := F.hU.isSetOf_finPow hT
  have htr := F.transfer
    (.all 0 (.const (powerset (prod T F.R))) (.all 1 (.const (powerset (prod T F.R))) (.all 2 (.const (finPow T)) (.all 3 (.const F.R) (.imp
      (.conj (svF T F.R 0) (.conj (svF T F.R 1)
        (.all 4 (.var 2) (.ex 5 (.const F.R) (.ex 6 (.const F.R) (.conj (.elem (.opair (.var 4) (.var 5)) (.var 0))
          (.conj (.elem (.opair (.var 4) (.var 6)) (.var 1)) (.elem (.opair (.opair (.var 3) (.var 5)) (.var 6)) (.const (F.binFn (· * ·)))))))))))
      (.ex 7 (.const F.R) (.ex 8 (.const F.R) (.conj (.elem (.opair (.opair (.var 0) (.var 2)) (.var 7)) (.const (F.fsumFn T))) (.conj (.elem (.opair (.opair (.var 1) (.var 2)) (.var 8)) (.const (F.fsumFn T))) (.elem (.opair (.opair (.var 3) (.var 7)) (.var 8)) (.const (F.binFn (· * ·)))))))))))))
    (by simp [IsSentence, svF, hP.1, hFT.1, hT.1, F.isSetOf_R.1, (F.isSetOf_fsumFn hT).1,
      (F.isSetOf_binFn _).1])
  simp only [svF] at htr
  sat_simp at htr
  have h' := htr.1 (by
    rintro g - hg k' - hk' B' - hB' c' - hc' ⟨hgs, hks, hpt⟩
    obtain ⟨c0, rfl⟩ := F.mem_R.1 hc'
    have hgf := isFunction_of_bounded (mem_powerset.1 hg) (F.hU.subset hT)
      (F.hU.subset F.isSetOf_R) hgs
    have hkf := isFunction_of_bounded (mem_powerset.1 hk') (F.hU.subset hT)
      (F.hU.subset F.isSetOf_R) hks
    refine ⟨_, F.real_mem_U _, F.mem_R.2 ⟨_, rfl⟩, _, F.real_mem_U _, F.mem_R.2 ⟨_, rfl⟩,
      F.pair_mem_fsumFn.2 ⟨hg, hB', rfl⟩, F.pair_mem_fsumFn.2 ⟨hk', hB', rfl⟩,
      F.pair_mem_binFn.2 ?_⟩
    congr 1
    rw [fsum, fsum, mul_finsum_mem]
    refine finsum_mem_congr rfl fun a ha => ?_
    obtain ⟨y, -, hy, z, -, hz, hay, haz, hmul⟩ :=
      hpt a (F.hU.subset hT ((mem_finPow.1 hB').1 ha)) ha
    obtain ⟨r, rfl⟩ := F.mem_R.1 hy
    rw [F.pair_mem_binFn.1 hmul] at haz
    rw [F.toReal_app hgf hay, F.toReal_app hkf haz])
  obtain ⟨s, -, -, t, -, -, h1, h2, h3⟩ := h' f (F.star_subset_U' hP hf) hf k
    (F.star_subset_U' hP hk) hk B (F.star_subset_U' hFT hB) hB c
    (F.star_subset_U' F.isSetOf_R hc) hc
    ⟨fun a _ _ b _ _ c _ _ hbc => hffun.2 a b c hbc.1 hbc.2,
      fun a _ _ b _ _ c _ _ hbc => hkfun.2 a b c hbc.1 hbc.2, fun x _ hx => by
        obtain ⟨hxy, -, hyU, hy⟩ := F.pair_app_mem_of_mem_star hT hf hffun (hBf hx)
        obtain ⟨hxz, -, hzU, hz⟩ := F.pair_app_mem_of_mem_star hT hk hkfun (hBk hx)
        refine ⟨_, hyU, hy, _, hzU, hz, hxy, hxz, ?_⟩
        rw [hval x hx]
        exact F.pair_hop_mem hc hy⟩
  rw [F.hfsum_eq_of_mem hT h1, F.hfsum_eq_of_mem hT h2]
  exact (F.hop_eq_of_mem h3).symm

/-- **Exercise 13.20 (1), additivity.**
$`\sum_{x \in B} (f(x) + g(x)) = \sum_{x \in B} f(x) + \sum_{x \in B} g(x)` for internal
functions $`f, g` and a hyperfinite set $`B`. Here $`k` is any internal function with
$`k(x) = f(x) + g(x)` on $`B`. -/
theorem hfsum_add {k : ZFSet.{u}} (hT : IsSetOf F.U T)
    (hf : f ∈ F.star (powerset (prod T F.R))) (hg : g ∈ F.star (powerset (prod T F.R)))
    (hk : k ∈ F.star (powerset (prod T F.R))) (hB : B ∈ F.star (finPow T))
    (hffun : IsFunction f) (hgfun : IsFunction g) (hkfun : IsFunction k)
    (hBf : B ⊆ dom f) (hBg : B ⊆ dom g) (hBk : B ⊆ dom k)
    (hval : ∀ x ∈ B, app k x = F.hadd (app f x) (app g x)) :
    F.hfsum T k B = F.hadd (F.hfsum T f B) (F.hfsum T g B) := by
  have hP := F.hU.isSetOf_powerset (F.hU.isSetOf_prod hT F.isSetOf_R)
  have hFT := F.hU.isSetOf_finPow hT
  have htr := F.transfer
    (.all 0 (.const (powerset (prod T F.R))) (.all 1 (.const (powerset (prod T F.R))) (.all 2 (.const (powerset (prod T F.R))) (.all 3 (.const (finPow T)) (.imp
      (.conj (svF T F.R 0) (.conj (svF T F.R 1) (.conj (svF T F.R 2)
        (.all 4 (.var 3) (.ex 5 (.const F.R) (.ex 6 (.const F.R) (.ex 7 (.const F.R) (.conj (.elem (.opair (.var 4) (.var 5)) (.var 0))
          (.conj (.elem (.opair (.var 4) (.var 6)) (.var 1)) (.conj (.elem (.opair (.var 4) (.var 7)) (.var 2)) (.elem (.opair (.opair (.var 5) (.var 6)) (.var 7)) (.const (F.binFn (· + ·))))))))))))))
      (.ex 7 (.const F.R) (.ex 8 (.const F.R) (.ex 9 (.const F.R) (.conj (.elem (.opair (.opair (.var 0) (.var 3)) (.var 7)) (.const (F.fsumFn T)))
        (.conj (.elem (.opair (.opair (.var 1) (.var 3)) (.var 8)) (.const (F.fsumFn T))) (.conj (.elem (.opair (.opair (.var 2) (.var 3)) (.var 9)) (.const (F.fsumFn T))) (.elem (.opair (.opair (.var 7) (.var 8)) (.var 9)) (.const (F.binFn (· + ·)))))))))))))))
    (by simp [IsSentence, svF, hP.1, hFT.1, hT.1, F.isSetOf_R.1, (F.isSetOf_fsumFn hT).1,
      (F.isSetOf_binFn _).1])
  simp only [svF] at htr
  sat_simp at htr
  have h' := htr.1 (by
    rintro f' - hf' g' - hg' k' - hk' B' - hB' ⟨hfs, hgs, hks, hpt⟩
    have hff := isFunction_of_bounded (mem_powerset.1 hf') (F.hU.subset hT)
      (F.hU.subset F.isSetOf_R) hfs
    have hgf := isFunction_of_bounded (mem_powerset.1 hg') (F.hU.subset hT)
      (F.hU.subset F.isSetOf_R) hgs
    have hkf := isFunction_of_bounded (mem_powerset.1 hk') (F.hU.subset hT)
      (F.hU.subset F.isSetOf_R) hks
    refine ⟨_, F.real_mem_U _, F.mem_R.2 ⟨_, rfl⟩, _, F.real_mem_U _, F.mem_R.2 ⟨_, rfl⟩,
      _, F.real_mem_U _, F.mem_R.2 ⟨_, rfl⟩, F.pair_mem_fsumFn.2 ⟨hf', hB', rfl⟩,
      F.pair_mem_fsumFn.2 ⟨hg', hB', rfl⟩, F.pair_mem_fsumFn.2 ⟨hk', hB', rfl⟩,
      F.pair_mem_binFn.2 ?_⟩
    congr 1
    have hfin := (mem_finPow.1 hB').2
    rw [fsum, fsum, fsum, ← finsum_mem_add_distrib hfin]
    refine finsum_mem_congr rfl fun a ha => ?_
    obtain ⟨y, -, hy, z, -, hz, w, -, hw, hay, haz, haw, hadd⟩ :=
      hpt a (F.hU.subset hT ((mem_finPow.1 hB').1 ha)) ha
    obtain ⟨r, rfl⟩ := F.mem_R.1 hy
    obtain ⟨r', rfl⟩ := F.mem_R.1 hz
    rw [F.pair_mem_binFn.1 hadd] at haw
    rw [F.toReal_app hff hay, F.toReal_app hgf haz, F.toReal_app hkf haw])
  obtain ⟨s, -, -, t, -, -, w, -, -, h1, h2, h3, h4⟩ := h' f (F.star_subset_U' hP hf) hf g
    (F.star_subset_U' hP hg) hg k (F.star_subset_U' hP hk) hk B (F.star_subset_U' hFT hB) hB
    ⟨fun a _ _ b _ _ c _ _ hbc => hffun.2 a b c hbc.1 hbc.2,
      fun a _ _ b _ _ c _ _ hbc => hgfun.2 a b c hbc.1 hbc.2,
      fun a _ _ b _ _ c _ _ hbc => hkfun.2 a b c hbc.1 hbc.2, fun x _ hx => by
        obtain ⟨hxy, -, hyU, hy⟩ := F.pair_app_mem_of_mem_star hT hf hffun (hBf hx)
        obtain ⟨hxz, -, hzU, hz⟩ := F.pair_app_mem_of_mem_star hT hg hgfun (hBg hx)
        obtain ⟨hxw, -, hwU, hw⟩ := F.pair_app_mem_of_mem_star hT hk hkfun (hBk hx)
        refine ⟨_, hyU, hy, _, hzU, hz, _, hwU, hw, hxy, hxz, hxw, ?_⟩
        rw [hval x hx]
        exact F.pair_hop_mem hy hz⟩
  rw [F.hfsum_eq_of_mem hT h1, F.hfsum_eq_of_mem hT h2, F.hfsum_eq_of_mem hT h3]
  exact (F.hop_eq_of_mem h4).symm

/-- **Exercise 13.20 (1), additivity over disjoint sets.** If $`B` and $`C` are disjoint
hyperfinite sets, then $`B \cup C` is hyperfinite and
$`\sum_{x \in B \cup C} f(x) = \sum_{x \in B} f(x) + \sum_{x \in C} f(x)`. -/
theorem hfsum_union (hT : IsSetOf F.U T) (hf : f ∈ F.star (powerset (prod T F.R)))
    (hB : B ∈ F.star (finPow T)) (hC : C ∈ F.star (finPow T)) (hdisj : B ∩ C = ∅) :
    B ∪ C ∈ F.star (finPow T) ∧
      F.hfsum T f (B ∪ C) = F.hadd (F.hfsum T f B) (F.hfsum T f C) := by
  have hP := F.hU.isSetOf_powerset (F.hU.isSetOf_prod hT F.isSetOf_R)
  have hFT := F.hU.isSetOf_finPow hT
  have htr := F.transfer
    (.all 0 (.const (powerset (prod T F.R))) (.all 1 (.const (finPow T)) (.all 2 (.const (finPow T)) (.imp
      (.all 4 (.var 1) (.neg (.elem (.var 4) (.var 2))))
      (.ex 3 (.const (finPow T)) (.conj
        (.all 4 (.const T) (.biimp (.elem (.var 4) (.var 3))
          (.disj (.elem (.var 4) (.var 1)) (.elem (.var 4) (.var 2)))))
        (.ex 5 (.const F.R) (.ex 6 (.const F.R) (.ex 7 (.const F.R) (.conj (.elem (.opair (.opair (.var 0) (.var 1)) (.var 5)) (.const (F.fsumFn T)))
          (.conj (.elem (.opair (.opair (.var 0) (.var 2)) (.var 6)) (.const (F.fsumFn T))) (.conj (.elem (.opair (.opair (.var 0) (.var 3)) (.var 7)) (.const (F.fsumFn T))) (.elem (.opair (.opair (.var 5) (.var 6)) (.var 7)) (.const (F.binFn (· + ·))))))))))))))))
    (by simp [IsSentence, hP.1, hFT.1, hT.1, F.isSetOf_R.1, (F.isSetOf_fsumFn hT).1,
      (F.isSetOf_binFn _).1])
  sat_simp at htr
  have h' := htr.1 (by
    rintro g' - hg' B' - hB' C' - hC' hdis
    obtain ⟨hBT, hBfin⟩ := mem_finPow.1 hB'
    obtain ⟨hCT, hCfin⟩ := mem_finPow.1 hC'
    have hcoe : ((B' ∪ C' : ZFSet.{u}) : Set ZFSet.{u}) =
        (B' : Set ZFSet.{u}) ∪ (C' : Set ZFSet.{u}) := Set.ext fun z => mem_union
    have hD : B' ∪ C' ∈ finPow T := mem_finPow.2 ⟨fun z hz => (mem_union.1 hz).elim
      (fun h => hBT h) (fun h => hCT h), by rw [hcoe]; exact hBfin.union hCfin⟩
    refine ⟨B' ∪ C', F.hU.subset hFT hD, hD, fun z _ _ => mem_union,
      _, F.real_mem_U _, F.mem_R.2 ⟨_, rfl⟩, _, F.real_mem_U _, F.mem_R.2 ⟨_, rfl⟩,
      _, F.real_mem_U _, F.mem_R.2 ⟨_, rfl⟩, F.pair_mem_fsumFn.2 ⟨hg', hB', rfl⟩,
      F.pair_mem_fsumFn.2 ⟨hg', hC', rfl⟩, F.pair_mem_fsumFn.2 ⟨hg', hD, rfl⟩,
      F.pair_mem_binFn.2 ?_⟩
    congr 1
    rw [fsum, fsum, fsum, hcoe]
    exact finsum_mem_union (Set.disjoint_left.2 fun z hzB hzC =>
      hdis z (F.hU.subset hT (hBT hzB)) hzB hzC) hBfin hCfin)
  have hBsub := (F.internal_subset_of_mem_star_finPow hT hB).1
  have hCsub := (F.internal_subset_of_mem_star_finPow hT hC).1
  obtain ⟨D, -, hD, hDmem, s, -, -, t, -, -, w, -, -, h1, h2, h3, h4⟩ := h' f
    (F.star_subset_U' hP hf) hf B (F.star_subset_U' hFT hB) hB C (F.star_subset_U' hFT hC) hC
    fun x _ hxB hxC => by
      have : x ∈ B ∩ C := mem_inter.2 ⟨hxB, hxC⟩
      rw [hdisj] at this
      exact notMem_empty x this
  have hDsub := (F.internal_subset_of_mem_star_finPow hT hD).1
  have hDeq : B ∪ C = D := by
    ext z
    rw [mem_union]
    constructor
    · intro hz
      have hzT : z ∈ F.star T := hz.elim (fun h => hBsub h) (fun h => hCsub h)
      exact (hDmem z (F.star_subset_U' hT hzT) hzT).2 hz
    · intro hz
      exact (hDmem z (F.star_subset_U' hT (hDsub hz)) (hDsub hz)).1 hz
  rw [hDeq]
  refine ⟨hD, ?_⟩
  rw [F.hfsum_eq_of_mem hT h1, F.hfsum_eq_of_mem hT h2, F.hfsum_eq_of_mem hT h3]
  exact (F.hop_eq_of_mem h4).symm

/-- **Exercise 13.20 (1), monotonicity.** If $`f(x) \le g(x)` for all $`x \in B`, then
$`\sum_{x \in B} f(x) \le \sum_{x \in B} g(x)`. -/
theorem hfsum_le (hT : IsSetOf F.U T) (hf : f ∈ F.star (powerset (prod T F.R)))
    (hg : g ∈ F.star (powerset (prod T F.R))) (hB : B ∈ F.star (finPow T))
    (hffun : IsFunction f) (hgfun : IsFunction g) (hBf : B ⊆ dom f) (hBg : B ⊆ dom g)
    (hval : ∀ x ∈ B, pair (app f x) (app g x) ∈ F.star F.Le) :
    pair (F.hfsum T f B) (F.hfsum T g B) ∈ F.star F.Le := by
  have hP := F.hU.isSetOf_powerset (F.hU.isSetOf_prod hT F.isSetOf_R)
  have hFT := F.hU.isSetOf_finPow hT
  have htr := F.transfer
    (.all 0 (.const (powerset (prod T F.R))) (.all 1 (.const (powerset (prod T F.R))) (.all 2 (.const (finPow T)) (.imp
      (.conj (svF T F.R 0) (.conj (svF T F.R 1)
        (.all 4 (.var 2) (.ex 5 (.const F.R) (.ex 6 (.const F.R) (.conj (.elem (.opair (.var 4) (.var 5)) (.var 0))
          (.conj (.elem (.opair (.var 4) (.var 6)) (.var 1)) (.elem (.opair (.var 5) (.var 6)) (.const F.Le)))))))))
      (.ex 7 (.const F.R) (.ex 8 (.const F.R) (.conj (.elem (.opair (.opair (.var 0) (.var 2)) (.var 7)) (.const (F.fsumFn T))) (.conj (.elem (.opair (.opair (.var 1) (.var 2)) (.var 8)) (.const (F.fsumFn T)))
        (.elem (.opair (.var 7) (.var 8)) (.const F.Le))))))))))
    (by simp [IsSentence, svF, hP.1, hFT.1, hT.1, F.isSetOf_R.1, (F.isSetOf_fsumFn hT).1,
      F.isSetOf_Le.1])
  simp only [svF] at htr
  sat_simp at htr
  have h' := htr.1 (by
    rintro f' - hf' g' - hg' B' - hB' ⟨hfs, hgs, hpt⟩
    have hff := isFunction_of_bounded (mem_powerset.1 hf') (F.hU.subset hT)
      (F.hU.subset F.isSetOf_R) hfs
    have hgf := isFunction_of_bounded (mem_powerset.1 hg') (F.hU.subset hT)
      (F.hU.subset F.isSetOf_R) hgs
    refine ⟨_, F.real_mem_U _, F.mem_R.2 ⟨_, rfl⟩, _, F.real_mem_U _, F.mem_R.2 ⟨_, rfl⟩,
      F.pair_mem_fsumFn.2 ⟨hf', hB', rfl⟩, F.pair_mem_fsumFn.2 ⟨hg', hB', rfl⟩,
      F.pair_mem_Le.2 ?_⟩
    have hfin := (mem_finPow.1 hB').2
    rw [fsum, fsum, finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine Finset.sum_le_sum fun a ha => ?_
    rw [Set.Finite.mem_toFinset] at ha
    obtain ⟨y, -, hy, z, -, hz, hay, haz, hle⟩ :=
      hpt a (F.hU.subset hT ((mem_finPow.1 hB').1 ha)) ha
    obtain ⟨r, rfl⟩ := F.mem_R.1 hy
    obtain ⟨r', rfl⟩ := F.mem_R.1 hz
    rw [F.toReal_app hff hay, F.toReal_app hgf haz]
    exact F.pair_mem_Le.1 hle)
  obtain ⟨s, -, -, t, -, -, h1, h2, h3⟩ := h' f (F.star_subset_U' hP hf) hf g
    (F.star_subset_U' hP hg) hg B (F.star_subset_U' hFT hB) hB
    ⟨fun a _ _ b _ _ c _ _ hbc => hffun.2 a b c hbc.1 hbc.2,
      fun a _ _ b _ _ c _ _ hbc => hgfun.2 a b c hbc.1 hbc.2, fun x _ hx => by
        obtain ⟨hxy, -, hyU, hy⟩ := F.pair_app_mem_of_mem_star hT hf hffun (hBf hx)
        obtain ⟨hxz, -, hzU, hz⟩ := F.pair_app_mem_of_mem_star hT hg hgfun (hBg hx)
        exact ⟨_, hyU, hy, _, hzU, hz, hxy, hxz, hval x hx⟩⟩
  rw [F.hfsum_eq_of_mem hT h1, F.hfsum_eq_of_mem hT h2]
  exact h3

/-- **Section 13.19, the book's definition.** If the internal function $`f` is injective on
the hyperfinite set $`B`, then $`f(B)` is a hyperfinite set of hyperreals and
$`\sum_{x \in B} f(x) = \sum f(B)`, the sum of the set of values. This is the book's
definition of the left-hand side; without injectivity the two sides differ. -/
theorem hfsum_eq_hsum_relImage (hT : IsSetOf F.U T) (hf : f ∈ F.star (powerset (prod T F.R)))
    (hB : B ∈ F.star (finPow T)) (hffun : IsFunction f) (hBf : B ⊆ dom f)
    (hinj : ∀ x ∈ B, ∀ x' ∈ B, app f x = app f x' → x = x') :
    relImage f B ∈ F.star (finPow F.R) ∧ F.hfsum T f B = F.hsum (relImage f B) := by
  have hP := F.hU.isSetOf_powerset (F.hU.isSetOf_prod hT F.isSetOf_R)
  have hFT := F.hU.isSetOf_finPow hT
  have hFR := F.hU.isSetOf_finPow F.isSetOf_R
  have hsum := F.hU.isSetOf_of_isFunc hFR F.isSetOf_R F.isFunc_sumFn
  have htr := F.transfer
    (.all 0 (.const (powerset (prod T F.R))) (.all 1 (.const (finPow T)) (.imp
      (.conj (svF T F.R 0) (.conj
        (.all 4 (.var 1) (.ex 5 (.const F.R) (.elem (.opair (.var 4) (.var 5)) (.var 0))))
        (.all 4 (.var 1) (.all 6 (.var 1) (.all 5 (.const F.R) (.imp
          (.conj (.elem (.opair (.var 4) (.var 5)) (.var 0)) (.elem (.opair (.var 6) (.var 5)) (.var 0))) (.equal (.var 4) (.var 6))))))))
      (.ex 2 (.const (finPow F.R)) (.conj
        (.all 5 (.const F.R) (.biimp (.elem (.var 5) (.var 2)) (.ex 4 (.var 1) (.elem (.opair (.var 4) (.var 5)) (.var 0)))))
        (.ex 7 (.const F.R) (.conj (.elem (.opair (.opair (.var 0) (.var 1)) (.var 7)) (.const (F.fsumFn T)))
          (.elem (.opair (.var 2) (.var 7)) (.const F.sumFn)))))))))
    (by simp [IsSentence, svF, hP.1, hFT.1, hFR.1, hT.1, F.isSetOf_R.1,
      (F.isSetOf_fsumFn hT).1, hsum.1])
  simp only [svF] at htr
  sat_simp at htr
  have h' := htr.1 (by
    rintro g' - hg' B' - hB' ⟨hgs, hdom, hin⟩
    have hgsub := mem_powerset.1 hg'
    have hgf := isFunction_of_bounded hgsub (F.hU.subset hT) (F.hU.subset F.isSetOf_R) hgs
    obtain ⟨hBT, hBfin⟩ := mem_finPow.1 hB'
    have hBU : B' ⊆ F.U := fun a ha => F.hU.subset hT (hBT ha)
    have hZ : relImage g' B' ∈ finPow F.R := mem_finPow.2 ⟨fun y hy => by
        obtain ⟨a, -, hay⟩ := mem_relImage.1 hy
        exact (pair_mem_prod.1 (hgsub hay)).2,
      (hBfin.image (app g')).subset fun y hy => by
        obtain ⟨a, ha, hay⟩ := mem_relImage.1 hy
        exact ⟨a, ha, hgf.app_eq hay⟩⟩
    refine ⟨relImage g' B', F.hU.subset hFR hZ, hZ, fun y _ _ => ?_, _, F.real_mem_U _,
      F.mem_R.2 ⟨_, rfl⟩, F.pair_mem_fsumFn.2 ⟨hg', hB', rfl⟩, ?_⟩
    · rw [mem_relImage]
      exact ⟨fun ⟨a, ha, hay⟩ => ⟨a, hBU ha, ha, hay⟩, fun ⟨a, _, ha, hay⟩ => ⟨a, ha, hay⟩⟩
    · have hval : ∀ a ∈ B', ∃ r : ℝ, pair a (F.real r) ∈ g' := fun a ha => by
        obtain ⟨y, -, hy, hay⟩ := hdom a (hBU ha) ha
        obtain ⟨r, rfl⟩ := F.mem_R.1 hy
        exact ⟨r, hay⟩
      have himg : {r : ℝ | F.real r ∈ relImage g' B'} =
          (fun a => F.toReal (app g' a)) '' (B' : Set ZFSet.{u}) := by
        ext r
        constructor
        · intro hr
          obtain ⟨a, ha, har⟩ := mem_relImage.1 hr
          exact ⟨a, ha, F.toReal_app hgf har⟩
        · rintro ⟨a, ha, rfl⟩
          obtain ⟨r, har⟩ := hval a ha
          show F.real (F.toReal (app g' a)) ∈ relImage g' B'
          rw [F.toReal_app hgf har]
          exact mem_relImage.2 ⟨a, ha, har⟩
      have hinjOn : Set.InjOn (fun a => F.toReal (app g' a)) (B' : Set ZFSet.{u}) := by
        intro a ha a' ha' heq
        obtain ⟨r, har⟩ := hval a ha
        obtain ⟨r', har'⟩ := hval a' ha'
        simp only [F.toReal_app hgf har, F.toReal_app hgf har'] at heq
        subst heq
        exact hin a (hBU ha) ha a' (hBU ha') ha' _ (F.real_mem_U r) (F.mem_R.2 ⟨r, rfl⟩)
          ⟨har, har'⟩
      have hsumeq : F.fsum g' B' = ∑ᶠ r ∈ {r : ℝ | F.real r ∈ relImage g' B'}, r := by
        rw [himg, finsum_mem_image hinjOn, fsum]
      rw [hsumeq]
      exact mem_range.2 ⟨⟨relImage g' B', hZ⟩, rfl⟩)
  have hfsub := ((F.mem_star_powerset_prod_iff hT).1 hf).1
  have hBsub := (F.internal_subset_of_mem_star_finPow hT hB).1
  obtain ⟨Z, -, hZ, hZmem, s, -, -, h1, h2⟩ := h' f (F.star_subset_U' hP hf) hf B
    (F.star_subset_U' hFT hB) hB
    ⟨fun a _ _ b _ _ c _ _ hbc => hffun.2 a b c hbc.1 hbc.2, fun x _ hx => by
        obtain ⟨hxy, -, hyU, hy⟩ := F.pair_app_mem_of_mem_star hT hf hffun (hBf hx)
        exact ⟨_, hyU, hy, hxy⟩,
      fun x _ hx x' _ hx' y _ _ hxy =>
        hinj x hx x' hx' ((hffun.app_eq hxy.1).trans (hffun.app_eq hxy.2).symm)⟩
  have hZsub := (F.internal_subset_of_mem_star_finPow F.isSetOf_R hZ).1
  have hZeq : relImage f B = Z := by
    ext y
    rw [mem_relImage]
    constructor
    · rintro ⟨a, ha, hay⟩
      have hy := (pair_mem_prod.1 (hfsub hay)).2
      exact (hZmem y (F.star_subset_U' F.isSetOf_R hy) hy).2
        ⟨a, F.star_subset_U' hT (hBsub ha), ha, hay⟩
    · intro hy
      obtain ⟨a, -, ha, hay⟩ :=
        (hZmem y (F.star_subset_U' F.isSetOf_R (hZsub hy)) (hZsub hy)).1 hy
      exact ⟨a, ha, hay⟩
  rw [hZeq]
  exact ⟨hZ, (F.hfsum_eq_of_mem hT h1).trans (F.isFunc_star_sumFn.1.isFunction.app_eq h2).symm⟩

/-- **Exercise 13.20 (2), indexed sums.** The sum $`\sum_{i=1}^n x_i` of an internal sequence
$`x` of hyperreals up to a hypernatural $`n`, possibly unlimited: the sum of the internal
function $`x` over the hyperfinite initial segment $`\{1, \dots, n\}`. It is defined when
$`x` is an internal function with hyperreal values whose domain is a subset of
$`{}^*\mathbb N` that includes $`\{1, \dots, n\}`. -/
def isum (x n : ZFSet.{u}) : ZFSet.{u} := F.hfsum F.N x (F.seg n)

/-- **Section 13.17.** An initial segment $`\{1, \dots, n\}` of the hypernaturals belongs to
$`{}^*\mathcal P_F(\mathbb N)`. -/
theorem seg_mem_star_finPow (hn : n ∈ F.star F.N) : F.seg n ∈ F.star (finPow F.N) :=
  (F.hyperfinite_seg hn).mem_star_finPow F.isSetOf_N sep_subset

/-- **Exercise 13.20 (2).** An indexed sum of hyperreals is a hyperreal. -/
theorem isum_mem (hx : x ∈ F.star (powerset (prod F.N F.R))) (hn : n ∈ F.star F.N) :
    F.isum x n ∈ F.star F.R :=
  F.hfsum_mem F.isSetOf_N hx (F.seg_mem_star_finPow hn)

/-- **Exercise 13.20 (2).** The empty indexed sum: $`\sum_{i=1}^0 x_i = 0`. -/
theorem isum_zero (hx : x ∈ F.star (powerset (prod F.N F.R))) :
    F.isum x (F.nat 0) = F.real 0 := by
  have hT := F.isSetOf_N
  have hP := F.hU.isSetOf_powerset (F.hU.isSetOf_prod hT F.isSetOf_R)
  have hFT := F.hU.isSetOf_finPow hT
  have htr := F.transfer
    (.all 0 (.const (powerset (prod F.N F.R))) (.all 1 (.const (finPow F.N)) (.imp
      (.all 4 (.var 1) (.conj (.elem (.opair (.const (F.nat 1)) (.var 4)) (.const F.Le))
        (.elem (.opair (.var 4) (.const (F.nat 0))) (.const F.Le))))
      (.elem (.opair (.opair (.var 0) (.var 1)) (.const (F.real 0))) (.const (F.fsumFn F.N))))))
    (by simp [IsSentence, hP.1, hFT.1, F.isSetOf_Le.1, (F.isSetOf_fsumFn hT).1, F.nat_mem_U,
      F.real_mem_U])
  sat_simp at htr
  rw [F.star_nat, F.star_nat, F.star_real] at htr
  have h0 : F.nat 0 ∈ F.star F.N := F.N_subset_star (F.mem_N.2 ⟨0, rfl⟩)
  have hseg := F.seg_mem_star_finPow h0
  refine F.hfsum_eq_of_mem hT (htr.1 ?_ x (F.star_subset_U' hP hx) hx _
    (F.star_subset_U' hFT hseg) hseg fun k _ hk => (mem_sep.1 hk).2)
  intro g' _ hg' V _ hV hVmem
  refine F.pair_mem_fsumFn.2 ⟨hg', hV, ?_⟩
  have hempty : (V : Set ZFSet.{u}) = ∅ := Set.eq_empty_of_forall_notMem fun a ha => by
    have haN := (mem_finPow.1 hV).1 ha
    obtain ⟨k, rfl⟩ := F.mem_N.1 haN
    obtain ⟨h1, h2⟩ := hVmem _ (F.nat_mem_U k) ha
    have := F.pair_nat_mem_Le.1 h1
    have := F.pair_nat_mem_Le.1 h2
    omega
  rw [fsum, hempty, finsum_mem_empty]

/-- **Exercise 13.20 (2).** The recursion for indexed sums: if $`m` is the successor of the
hypernatural $`n`, then $`\sum_{i=1}^{m} x_i = \sum_{i=1}^{n} x_i + x_m`. Together with
{lit}`RealFramework.isum_zero` this determines the indexed sums of an internal sequence. -/
theorem isum_succ {m : ZFSet.{u}} (hx : x ∈ F.star (powerset (prod F.N F.R)))
    (hxfun : IsFunction x) (hn : n ∈ F.star F.N) (hm : m ∈ F.star F.N)
    (hnm : pair n m ∈ F.star F.Succ) (hmx : m ∈ dom x) :
    F.isum x m = F.hadd (F.isum x n) (app x m) := by
  have hT := F.isSetOf_N
  have hP := F.hU.isSetOf_powerset (F.hU.isSetOf_prod hT F.isSetOf_R)
  have hFT := F.hU.isSetOf_finPow hT
  have htr := F.transfer
    (.all 0 (.const (powerset (prod F.N F.R))) (.all 1 (.const F.N) (.all 2 (.const F.N)
      (.all 3 (.const (finPow F.N)) (.all 4 (.const (finPow F.N)) (.all 5 (.const F.R) (.imp
        (.conj (svF F.N F.R 0) (.conj (.elem (.opair (.var 1) (.var 2)) (.const F.Succ))
          (.conj (.elem (.opair (.var 2) (.var 5)) (.var 0)) (.conj
            (.all 8 (.const F.N) (.biimp (.elem (.var 8) (.var 3)) (.conj
              (.elem (.opair (.const (F.nat 1)) (.var 8)) (.const F.Le))
              (.elem (.opair (.var 8) (.var 1)) (.const F.Le)))))
            (.all 8 (.const F.N) (.biimp (.elem (.var 8) (.var 4)) (.conj
              (.elem (.opair (.const (F.nat 1)) (.var 8)) (.const F.Le))
              (.elem (.opair (.var 8) (.var 2)) (.const F.Le)))))))))
        (.ex 6 (.const F.R) (.ex 7 (.const F.R) (.conj
          (.elem (.opair (.opair (.var 0) (.var 3)) (.var 6)) (.const (F.fsumFn F.N))) (.conj
          (.elem (.opair (.opair (.var 0) (.var 4)) (.var 7)) (.const (F.fsumFn F.N)))
          (.elem (.opair (.opair (.var 6) (.var 5)) (.var 7))
            (.const (F.binFn (· + ·)))))))))))))))
    (by simp [IsSentence, svF, hP.1, hFT.1, hT.1, F.isSetOf_R.1, F.isSetOf_Le.1,
      F.isSetOf_Succ.1, (F.isSetOf_fsumFn hT).1, (F.isSetOf_binFn _).1, F.nat_mem_U])
  simp only [svF] at htr
  sat_simp at htr
  rw [F.star_nat] at htr
  have h' := htr.1 (by
    rintro g' - hg' n' - hn' m' - hm' V - hV V' - hV' y - hy ⟨hgs, hsucc, hmy, hVmem, hVmem'⟩
    have hgf := isFunction_of_bounded (mem_powerset.1 hg') (F.hU.subset hT)
      (F.hU.subset F.isSetOf_R) hgs
    obtain ⟨j, rfl⟩ := F.mem_N.1 hn'
    rw [F.pair_mem_Succ.1 hsucc] at hmy hVmem'
    obtain ⟨r, rfl⟩ := F.mem_R.1 hy
    obtain ⟨hVN, hVfin⟩ := mem_finPow.1 hV
    obtain ⟨hVN', -⟩ := mem_finPow.1 hV'
    have hV1 : ∀ i : ℕ, F.nat i ∈ V ↔ 1 ≤ i ∧ i ≤ j := fun i => by
      rw [hVmem _ (F.nat_mem_U i) (F.mem_N.2 ⟨i, rfl⟩), F.pair_nat_mem_Le, F.pair_nat_mem_Le]
    have hV2 : ∀ i : ℕ, F.nat i ∈ V' ↔ 1 ≤ i ∧ i ≤ j + 1 := fun i => by
      rw [hVmem' _ (F.nat_mem_U i) (F.mem_N.2 ⟨i, rfl⟩), F.pair_nat_mem_Le, F.pair_nat_mem_Le]
    have hcoe : (V' : Set ZFSet.{u}) = insert (F.nat (j + 1)) (V : Set ZFSet.{u}) := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, rfl⟩ := F.mem_N.1 (hVN' ha)
        obtain ⟨h1, h2⟩ := (hV2 i).1 ha
        rcases Nat.eq_or_lt_of_le h2 with rfl | h3
        · exact Or.inl rfl
        · exact Or.inr ((hV1 i).2 ⟨h1, by omega⟩)
      · rintro (rfl | ha)
        · exact (hV2 _).2 ⟨by omega, le_rfl⟩
        · obtain ⟨i, rfl⟩ := F.mem_N.1 (hVN ha)
          obtain ⟨h1, h2⟩ := (hV1 i).1 ha
          exact (hV2 i).2 ⟨h1, by omega⟩
    have hnot : F.nat (j + 1) ∉ (V : Set ZFSet.{u}) := fun h => by
      have := ((hV1 _).1 h).2
      omega
    refine ⟨_, F.real_mem_U _, F.mem_R.2 ⟨_, rfl⟩, _, F.real_mem_U _, F.mem_R.2 ⟨_, rfl⟩,
      F.pair_mem_fsumFn.2 ⟨hg', hV, rfl⟩, F.pair_mem_fsumFn.2 ⟨hg', hV', rfl⟩,
      F.pair_mem_binFn.2 ?_⟩
    congr 1
    rw [fsum, fsum, hcoe, finsum_mem_insert _ hnot hVfin, F.toReal_app hgf hmy, add_comm])
  have hsn := F.seg_mem_star_finPow hn
  have hsm := F.seg_mem_star_finPow hm
  obtain ⟨hmy, -, hyU, hy⟩ := F.pair_app_mem_of_mem_star hT hx hxfun hmx
  have hNU' := F.star_subset_U' hT
  obtain ⟨s, -, -, t, -, -, h1, h2, h3⟩ := h' x (F.star_subset_U' hP hx) hx n (hNU' hn) hn m
    (hNU' hm) hm _ (F.star_subset_U' hFT hsn) hsn _ (F.star_subset_U' hFT hsm) hsm _ hyU hy
    ⟨fun a _ _ b _ _ c _ _ hbc => hxfun.2 a b c hbc.1 hbc.2, hnm, hmy,
      fun k _ hk => by rw [seg, mem_sep]; exact ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩,
      fun k _ hk => by rw [seg, mem_sep]; exact ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩⟩
  rw [isum, isum, F.hfsum_eq_of_mem hT h1, F.hfsum_eq_of_mem hT h2]
  exact (F.hop_eq_of_mem h3).symm

/-- **Exercise 13.20 (2).** For a standard $`m` the indexed sum is the ordinary finite sum:
if $`x_k` is the real number $`r_k` for $`k = 1, \dots, m`, then
$`\sum_{i=1}^m x_i = r_1 + \dots + r_m`. -/
theorem isum_nat (hx : x ∈ F.star (powerset (prod F.N F.R))) (hxfun : IsFunction x)
    (r : ℕ → ℝ) (m : ℕ) (hval : ∀ k, 1 ≤ k → k ≤ m → pair (F.nat k) (F.real (r k)) ∈ x) :
    F.isum x (F.nat m) = F.real (∑ k ∈ Finset.Icc 1 m, r k) := by
  induction m with
  | zero => simpa using F.isum_zero hx
  | succ m ih =>
    have hN : ∀ k : ℕ, F.nat k ∈ F.star F.N := fun k => F.N_subset_star (F.mem_N.2 ⟨k, rfl⟩)
    have hmem := hval (m + 1) (by omega) le_rfl
    have hsucc : pair (F.nat m) (F.nat (m + 1)) ∈ F.star F.Succ := by
      have := (F.star_mem_star_iff (F.hU.isSetOf_opair (F.nat_mem_U m) (F.nat_mem_U (m + 1))).1
        F.isSetOf_Succ.1).2 (F.pair_mem_Succ.2 rfl)
      rwa [F.star_opair (F.nat_mem_U m) (F.nat_mem_U (m + 1)), F.star_nat, F.star_nat] at this
    rw [F.isum_succ hx hxfun (hN m) (hN (m + 1)) hsucc (mem_dom.2 ⟨_, hmem⟩),
      ih fun k h1 h2 => hval k h1 (by omega), hxfun.app_eq hmem, hadd, F.hop_real,
      Finset.sum_Icc_succ_top (by omega)]

end RealFramework

end Goldblatt
