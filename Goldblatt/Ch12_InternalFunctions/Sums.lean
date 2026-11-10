import Goldblatt.Ch12_InternalFunctions.Hyperfinite

/-!
# 12 (part 3). Integrals as Hyperfinite Sums: Section 12.7

This is the third of three parts of Chapter 12 (the overview is on the chapter page
{lit}`Goldblatt.Ch12_InternalFunctions`). It defines the sum of an internal function over a
hyperfinite set, proves the algebraic properties of hyperfinite sums, and shows that an integral
over a closed interval is the shadow of a hyperfinite Riemann sum over a partition of
infinitesimal width. This is proved for every bounded function whose Riemann sums of
Section 9.1 converge ({lit}`Goldblatt.RiemannSumsConverge.eq_sh_hsum_hpartition`), and hence
for continuous functions with Mathlib's interval integral
({lit}`Goldblatt.integral_eq_sh_hsum_hpartition`). The book states the result for Riemann
integrable functions; that case needs the two hypotheses to be derived from integrability,
which is the business of Chapter 9 and is not done here.
-/

universe u

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal

/-!
## 12.7 Integrals as Hyperfinite Sums

A finite sum $`\sum_{x \in X} g(x)` makes sense for a finite set $`X` and a function $`g`
defined on it. If $`A = [A_n]` is hyperfinite and $`f = [f_n]` is an internal function defined
on $`A`, then $`\sum_{x \in A_n} f_n(x)` is a finite sum of reals for almost all $`n`, and the
class of this sequence of sums is the _hyperfinite sum_ $`\sum_{x \in A} f(x)`. Hyperfinite
sums are linear, additive over disjoint unions, and monotone, by the corresponding facts for
finite sums.

The second half of the section applies this to integration. For a positive infinitesimal
$`\Delta x`, the points $`a + k\,\Delta x` below $`b` form a hyperfinite set $`P`, and the
extended Riemann sum of Section 9.1 is, up to an infinitesimal, a hyperfinite sum over $`P`.
Its shadow is the integral: this is proved for every function that is bounded on the interval
and whose Section 9.1 Riemann sums converge
({lit}`Goldblatt.RiemannSumsConverge.eq_sh_hsum_hpartition`), in particular for continuous
functions ({lit}`Goldblatt.integral_eq_sh_hsum_hpartition`). The Riemann integrable case of
the book is the same theorem once Chapter 9 supplies boundedness and convergence of the
Riemann sums for integrable functions; it is not yet proved unconditionally.

The partition here is the one of Section 9.1, determined by a width; its objects are named
{lit}`Goldblatt.widthPartitionCard` and {lit}`Goldblatt.widthPartitionPoint` to keep them
apart from the partition into $`n` equal parts used in Chapter 7.

In the formalization the hyperfinite sum is {lit}`Goldblatt.internalSum` (for hyperreal
functions, {lit}`Goldblatt.hsum`). A partial function is given the value $`0` outside its
domain ({lit}`Goldblatt.pval`), so that the sum is defined for every internal function and
every internal set; the theorems state the hypotheses under which it has the expected
meaning.
-/

section PartialValues

open Classical in
/-- **Section 12.7.** The value of a partial function at a point, with the value $`0` outside
the domain. -/
noncomputable def pval {X : Type*} {M : Type*} [Zero M] (g : X →. M) (x : X) : M :=
  if h : (g x).Dom then (g x).get h else 0

/-- If $`g(x) = y` then the value of $`g` at $`x` is $`y`. -/
theorem pval_of_mem {X : Type*} {M : Type*} [Zero M] {g : X →. M} {x : X} {y : M}
    (h : y ∈ g x) : pval g x = y := by
  have hd : (g x).Dom := Part.dom_iff_mem.2 ⟨y, h⟩
  simp only [pval, hd, ↓reduceDIte]
  exact Part.get_eq_of_mem h hd

/-- Outside the domain the value is $`0`. -/
theorem pval_of_notMem_dom {X : Type*} {M : Type*} [Zero M] {g : X →. M} {x : X}
    (h : x ∉ g.Dom) : pval g x = 0 := by
  have hd : ¬ (g x).Dom := h
  simp only [pval, hd, ↓reduceDIte]

/-- On the domain, the value is the value of the partial function. -/
theorem pval_mem {X : Type*} {M : Type*} [Zero M] {g : X →. M} {x : X} (h : x ∈ g.Dom) :
    pval g x ∈ g x := by
  obtain ⟨y, hy⟩ := (PFun.mem_dom _ _).1 h
  rw [pval_of_mem hy]
  exact hy

/-- The value of a total function, regarded as a partial function, is its value. -/
theorem pval_coe {X : Type*} {M : Type*} [Zero M] (f : X → M) (x : X) :
    pval (f : X →. M) x = f x :=
  pval_of_mem (by rw [PFun.coe_val]; exact Part.mem_some _)

/-- The value of a multiple of a partial real function is the multiple of the value. -/
theorem pval_map_mul_left {X : Type*} (g : X →. ℝ) (c : ℝ) (x : X) :
    pval (g.map fun y => c * y) x = c * pval g x := by
  by_cases hx : x ∈ g.Dom
  · exact pval_of_mem ((PFun.mem_map _ _ _ _).2 ⟨_, pval_mem hx, rfl⟩)
  · rw [pval_of_notMem_dom (by rwa [PFun.dom_map]), pval_of_notMem_dom hx, mul_zero]

end PartialValues

section HyperfiniteSums

variable {α αS : Type u} [StarType α αS]

open Classical in
/-- **Section 12.7.** The _hyperfinite sum_ $`\sum_{x \in A} f(x)` of an internal
hyperreal-valued function $`f = [f_n]` over an internal set $`A = [A_n]`: the class of the
sequence of sums $`\sum_{x \in A_n} f_n(x)` ({lit}`Goldblatt.internalSum_internalPFun`). The
book's definition is the case of a hyperfinite $`A` included in the domain of $`f`. Outside
that case the definition still returns a hyperreal: a function counts as $`0` where it is not
defined, a sum over an infinite set with infinitely many nonzero terms is $`0`, and the sum is
$`0` if $`f` or $`A` is not internal. -/
noncomputable def internalSum (α : Type u) {αS : Type u} [StarType α αS] (f : αS →. ℝ*)
    (X : Set αS) : ℝ* :=
  if h : IsInternalPFun α ℝ f ∧ IsInternalSet α X then
    Hyperreal.ofSeq fun n => ∑ᶠ x ∈ h.2.choose n, pval (h.1.choose n) x
  else 0

/-- **Section 12.7.** The hyperfinite sum of a hyperreal function over a set of hyperreals. -/
noncomputable abbrev hsum (f : ℝ* →. ℝ*) (X : Set ℝ*) : ℝ* := internalSum ℝ f X

/-- **Section 12.7.** $`\sum_{x \in [A_n]} [f_n](x) = \bigl[\sum_{x \in A_n} f_n(x)\bigr]`,
whichever sequences define the function and the set. -/
theorem internalSum_internalPFun (F : ℕ → α →. ℝ) (A : ℕ → Set α) :
    internalSum α (internalPFun F : αS →. ℝ*) (internalSet A) =
      Hyperreal.ofSeq fun n => ∑ᶠ x ∈ A n, pval (F n) x := by
  have h : IsInternalPFun α ℝ (internalPFun F : αS →. ℝ*) ∧
      IsInternalSet α (internalSet A : Set αS) := ⟨⟨F, rfl⟩, ⟨A, rfl⟩⟩
  rw [internalSum]
  split_ifs
  refine ofSeq_eq_ofSeq_iff.2 ?_
  filter_upwards [internalPFun_eq_iff.1 h.1.choose_spec, internalSet_eq_iff.1 h.2.choose_spec]
    with n h1 h2
  rw [← h1, ← h2]

/-- **Section 12.7.** For a sequence of finite sets given as {name}`Finset`s, the hyperfinite
sum is the class of the sequence of finite sums. -/
theorem internalSum_internalPFun_finset (F : ℕ → α →. ℝ) (A : ℕ → Finset α) :
    internalSum α (internalPFun F : αS →. ℝ*) (internalSet fun n => (A n : Set α)) =
      Hyperreal.ofSeq fun n => ∑ x ∈ A n, pval (F n) x := by
  rw [internalSum_internalPFun]
  simp only [finsum_mem_coe_finset]

/-- **Section 12.7.** The hyperfinite sum of the internal function of a sequence of total
functions: $`\sum_{x \in [A_n]} [f_n](x) = \bigl[\sum_{x \in A_n} f_n(x)\bigr]`. -/
theorem internalSum_internalMap (f : ℕ → α → ℝ) (A : ℕ → Set α) :
    internalSum α ((internalMap f : αS → ℝ*) : αS →. ℝ*) (internalSet A) =
      Hyperreal.ofSeq fun n => ∑ᶠ x ∈ A n, f n x := by
  rw [← internalPFun_coe, internalSum_internalPFun]
  simp only [pval_coe]

/-- **Section 12.7.** The hyperfinite sum over $`[A_n]`, for finite sets $`A_n`, of the
internal function of a sequence of total functions. -/
theorem internalSum_internalMap_finset (f : ℕ → α → ℝ) (A : ℕ → Finset α) :
    internalSum α ((internalMap f : αS → ℝ*) : αS →. ℝ*) (internalSet fun n => (A n : Set α)) =
      Hyperreal.ofSeq fun n => ∑ x ∈ A n, f n x := by
  rw [internalSum_internalMap]
  simp only [finsum_mem_coe_finset]

/-- **Section 12.7.** A sum over the empty set is $`0`. -/
theorem internalSum_empty (f : αS →. ℝ*) : internalSum α f (∅ : Set αS) = 0 := by
  by_cases hf : IsInternalPFun α ℝ f
  · obtain ⟨F, rfl⟩ := hf
    have h : (∅ : Set αS) = internalSet fun _ : ℕ => (∅ : Set α) := by
      rw [← starSet_eq_internalSet, starSet_empty]
    rw [h, internalSum_internalPFun]
    simp only [mem_empty_iff_false, finsum_false, finsum_zero]
    rfl
  · rw [internalSum]
    split_ifs with h
    · exact absurd h.1 hf
    · rfl

/-- **Section 12.7, first property.** A constant factor may be taken out of a hyperfinite
sum: $`\sum_{x \in A} c f(x) = c \sum_{x \in A} f(x)`. -/
theorem internalSum_map_mul_left {f : αS →. ℝ*} (hf : IsInternalPFun α ℝ f) {X : Set αS}
    (hX : IsHyperfiniteSet α X) (c : ℝ*) :
    internalSum α (f.map fun y => c * y) X = c * internalSum α f X := by
  obtain ⟨F, rfl⟩ := hf
  obtain ⟨A, rfl⟩ := isHyperfiniteSet_iff_exists_finset.1 hX
  obtain ⟨c, rfl⟩ := hyperreal_exists_rep c
  rw [map_mul_left_internalPFun, internalSum_internalPFun_finset,
    internalSum_internalPFun_finset]
  change _ = Hyperreal.ofSeq fun n => c n * ∑ x ∈ A n, pval (F n) x
  refine ofSeq_eq_ofSeq_iff.2 (Eventually.of_forall fun n => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => pval_map_mul_left _ _ _

/-- **Section 12.7, first property**, with the factor on the right:
$`\sum_{x \in A} f(x)\,c = \bigl(\sum_{x \in A} f(x)\bigr) c`. -/
theorem internalSum_map_mul_right {f : αS →. ℝ*} (hf : IsInternalPFun α ℝ f) {X : Set αS}
    (hX : IsHyperfiniteSet α X) (c : ℝ*) :
    internalSum α (f.map fun y => y * c) X = internalSum α f X * c := by
  have h : (fun y : ℝ* => y * c) = fun y => c * y := funext fun y => mul_comm y c
  rw [h, internalSum_map_mul_left hf hX, mul_comm]

/-- **Section 12.7, second property.** A hyperfinite sum of a sum of two internal functions,
over a hyperfinite set on which both are defined, is the sum of the hyperfinite sums:
$`\sum_{x \in A} (f(x) + g(x)) = \sum_{x \in A} f(x) + \sum_{x \in A} g(x)`. -/
theorem internalSum_padd {f g : αS →. ℝ*} (hf : IsInternalPFun α ℝ f)
    (hg : IsInternalPFun α ℝ g) {X : Set αS} (hX : IsHyperfiniteSet α X) (hXf : X ⊆ f.Dom)
    (hXg : X ⊆ g.Dom) :
    internalSum α (padd f g) X = internalSum α f X + internalSum α g X := by
  obtain ⟨F, rfl⟩ := hf
  obtain ⟨G, rfl⟩ := hg
  obtain ⟨A, rfl⟩ := isHyperfiniteSet_iff_exists_finset.1 hX
  rw [dom_internalPFun, internalSet_subset_iff] at hXf hXg
  rw [padd_internalPFun, internalSum_internalPFun_finset, internalSum_internalPFun_finset,
    internalSum_internalPFun_finset, ofSeq_add]
  refine ofSeq_eq_ofSeq_iff.2 ?_
  filter_upwards [hXf, hXg] with n h1 h2
  rw [Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x hx =>
    pval_of_mem (mem_padd.2 ⟨_, pval_mem (h1 hx), _, pval_mem (h2 hx), rfl⟩)

/-- **Section 12.7, third property.** A hyperfinite sum over the union of two disjoint
hyperfinite sets is the sum of the two hyperfinite sums:
$`\sum_{x \in A \cup B} f(x) = \sum_{x \in A} f(x) + \sum_{x \in B} f(x)`. -/
theorem internalSum_union {f : αS →. ℝ*} (hf : IsInternalPFun α ℝ f) {X Y : Set αS}
    (hX : IsHyperfiniteSet α X) (hY : IsHyperfiniteSet α Y) (hXY : Disjoint X Y) :
    internalSum α f (X ∪ Y) = internalSum α f X + internalSum α f Y := by
  classical
  obtain ⟨F, rfl⟩ := hf
  obtain ⟨A, rfl⟩ := isHyperfiniteSet_iff_exists_finset.1 hX
  obtain ⟨B, rfl⟩ := isHyperfiniteSet_iff_exists_finset.1 hY
  have hdisj : ∀ᶠ n in hyperfilter ℕ, Disjoint (A n) (B n) := by
    have h1 := disjoint_iff_inter_eq_empty.1 hXY
    rw [internalSet_inter, internalSet_eq_empty_iff] at h1
    exact h1.mono fun n hn => Finset.disjoint_coe.1 (disjoint_iff_inter_eq_empty.2 hn)
  have hU : (internalSet (fun n => (A n : Set α)) ∪ internalSet (fun n => (B n : Set α)) :
      Set αS) = internalSet fun n => ((A n ∪ B n : Finset α) : Set α) := by
    rw [internalSet_union]
    simp only [Finset.coe_union]
  rw [hU, internalSum_internalPFun_finset, internalSum_internalPFun_finset,
    internalSum_internalPFun_finset, ofSeq_add]
  refine ofSeq_eq_ofSeq_iff.2 (hdisj.mono fun n hn => ?_)
  rw [Pi.add_apply, Finset.sum_union hn]

/-- **Section 12.7, fourth property.** Hyperfinite sums are monotone: if $`f(x) \le g(x)` for
all $`x` in the hyperfinite set $`A`, on which both functions are defined, then
$`\sum_{x \in A} f(x) \le \sum_{x \in A} g(x)`. The pointwise hypothesis on the internal
functions transfers to almost all terms of the sequences, since a sequence of points where it
failed would define a point of $`A` where $`f` exceeded $`g`. -/
theorem internalSum_le_internalSum {f g : αS →. ℝ*} (hf : IsInternalPFun α ℝ f)
    (hg : IsInternalPFun α ℝ g) {X : Set αS} (hX : IsHyperfiniteSet α X) (hXf : X ⊆ f.Dom)
    (hXg : X ⊆ g.Dom) (hle : ∀ x ∈ X, ∀ y ∈ f x, ∀ z ∈ g x, y ≤ z) :
    internalSum α f X ≤ internalSum α g X := by
  obtain ⟨F, rfl⟩ := hf
  obtain ⟨G, rfl⟩ := hg
  obtain ⟨A, rfl⟩ := isHyperfiniteSet_iff_exists_finset.1 hX
  rw [dom_internalPFun, internalSet_subset_iff] at hXf hXg
  have key : ∀ᶠ n in hyperfilter ℕ, ∀ x ∈ A n, pval (F n) x ≤ pval (G n) x := by
    by_contra hnot
    rw [← almostAll_not] at hnot
    have hex : ∀ᶠ n in hyperfilter ℕ, ∃ x, x ∈ A n ∧ pval (G n) x < pval (F n) x :=
      hnot.mono fun n hn => by
        push Not at hn
        exact hn
    obtain ⟨r, hr⟩ := exists_seq_of_almostAll_exists hex
    have hmem : (ofSeq r : αS) ∈ internalSet fun n => (A n : Set α) :=
      ofSeq_mem_internalSet.2 (hr.mono fun n hn => hn.1)
    have h1 : (ofSeq (fun n => pval (F n) (r n)) : ℝ*) ∈ internalPFun F (ofSeq r : αS) :=
      ofSeq_mem_internalPFun.2 (by
        filter_upwards [hr, hXf] with n hn h using pval_mem (h hn.1))
    have h2 : (ofSeq (fun n => pval (G n) (r n)) : ℝ*) ∈ internalPFun G (ofSeq r : αS) :=
      ofSeq_mem_internalPFun.2 (by
        filter_upwards [hr, hXg] with n hn h using pval_mem (h hn.1))
    have h3 : Hyperreal.ofSeq (fun n => pval (F n) (r n)) ≤
        Hyperreal.ofSeq fun n => pval (G n) (r n) := hle _ hmem _ h1 _ h2
    exact almostAll_not.1 (hr.mono fun n hn => not_le.2 hn.2) (ofSeq_le_ofSeq_iff.1 h3)
  rw [internalSum_internalPFun_finset, internalSum_internalPFun_finset, ofSeq_le_ofSeq_iff]
  exact key.mono fun n hn => Finset.sum_le_sum hn

/-- **Section 12.7.** The hyperfinite sum of the constant function $`1` over a hyperfinite set
is the internal cardinality of the set. -/
theorem internalSum_one {X : Set αS} (hX : IsHyperfiniteSet α X) :
    internalSum α ((fun _ => (1 : ℝ*) : αS → ℝ*) : αS →. ℝ*) X = internalCard α X := by
  obtain ⟨A, rfl⟩ := isHyperfiniteSet_iff_exists_finset.1 hX
  have h1 : (fun _ => (1 : ℝ*) : αS → ℝ*) = internalMap (α := α) fun _ _ => (1 : ℝ) := by
    funext x
    obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
    rw [internalMap_ofSeq]
    rfl
  rw [h1, internalSum_internalMap_finset, internalCard_internalSet_finset]
  refine ofSeq_eq_ofSeq_iff.2 (Eventually.of_forall fun n => ?_)
  simp

end HyperfiniteSums

section RealRiemannSums

/-- **Section 12.7 (and 9.1).** The number $`N` of points $`a + k\varepsilon` below $`b`: the
least natural number with $`a + N\varepsilon \ge b`.

This is a definition of Section 9.1, placed here provisionally because the chapter on the
Riemann integral is not among the modules this chapter may import. Once that chapter exists,
either it should reuse this name or the present section should be rebased on its definition
through a bridging lemma. -/
noncomputable def widthPartitionCard (a b e : ℝ) : ℕ := ⌈(b - a) / e⌉₊

/-- **Section 12.7 (and 9.1).** The $`k`-th point of the partition of $`[a, b]` into
subintervals of width $`\varepsilon` with a possibly smaller last subinterval: $`a +
k\varepsilon`, cut off at $`b`.

Like {name}`Goldblatt.widthPartitionCard`, this is a Section 9.1 definition placed here
provisionally. -/
noncomputable def widthPartitionPoint (a b e : ℝ) (k : ℕ) : ℝ := min (a + k * e) b

/-- **Section 12.7 (and 9.1).** The ordinary Riemann sum $`S_a^b(f, \varepsilon)` of the
partition of $`[a, b]` into subintervals of width $`\varepsilon`, with a possibly smaller last
subinterval: the sum of the terms $`f(x_k)(x_{k+1} - x_k)`.

Like {name}`Goldblatt.widthPartitionCard`, this is a Section 9.1 definition placed here
provisionally; a later formalization of Chapter 9 should reuse it or be linked to it by a
bridging lemma, so that the two chapters do not carry divergent copies. -/
noncomputable def riemannSum (f : ℝ → ℝ) (a b e : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (widthPartitionCard a b e),
    f (widthPartitionPoint a b e k) *
      (widthPartitionPoint a b e (k + 1) - widthPartitionPoint a b e k)

/-- **Section 12.7.** The sum $`\bigl(\sum_{x \in P_\varepsilon} f(x)\bigr)\varepsilon` over
the points $`a + k\varepsilon` below $`b`, in which every term has the full width
$`\varepsilon`. -/
noncomputable def uniformSum (f : ℝ → ℝ) (a b e : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (widthPartitionCard a b e), f (a + k * e) * e

/-- **Section 12.7.** The finite set $`P_\varepsilon` of the points $`a + k\varepsilon` below
$`b`. -/
noncomputable def partitionFinset (a b e : ℝ) : Finset ℝ :=
  (Finset.range (widthPartitionCard a b e)).image fun k : ℕ => a + k * e

/-- For $`\varepsilon > 0`, $`k < N` if and only if $`a + k\varepsilon < b`. -/
theorem lt_widthPartitionCard_iff {a b e : ℝ} (he : 0 < e) {k : ℕ} :
    k < widthPartitionCard a b e ↔ a + k * e < b := by
  rw [widthPartitionCard, Nat.lt_ceil, lt_div_iff₀ he]
  constructor <;> intro h <;> linarith

/-- For $`\varepsilon > 0`, the finite set $`P_\varepsilon` consists of the points $`a +
k\varepsilon` that lie below $`b`. -/
theorem coe_partitionFinset {a b e : ℝ} (he : 0 < e) :
    (partitionFinset a b e : Set ℝ) = {x : ℝ | ∃ k : ℕ, x = a + k * e ∧ x < b} := by
  ext x
  simp only [partitionFinset, Finset.coe_image, Finset.coe_range, mem_image, mem_Iio,
    mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, rfl, (lt_widthPartitionCard_iff he).1 hk⟩
  · rintro ⟨k, rfl, hk⟩
    exact ⟨k, (lt_widthPartitionCard_iff he).2 hk, rfl⟩

/-- For $`\varepsilon > 0`, the points $`a + k\varepsilon` are distinct. -/
theorem injective_partition {a e : ℝ} (he : 0 < e) :
    Function.Injective fun k : ℕ => a + k * e := fun _ _ hij =>
  Nat.cast_injective (mul_right_cancel₀ he.ne' (add_left_cancel hij))

/-- For $`\varepsilon > 0`, the set $`P_\varepsilon` has $`N` elements. -/
theorem card_partitionFinset {a b e : ℝ} (he : 0 < e) :
    (partitionFinset a b e).card = widthPartitionCard a b e := by
  rw [partitionFinset, Finset.card_image_of_injective _ (injective_partition he),
    Finset.card_range]

/-- For $`\varepsilon > 0`, a sum over $`P_\varepsilon` is a sum over the indices
$`k < N`. -/
theorem sum_partitionFinset {a b e : ℝ} (he : 0 < e) (g : ℝ → ℝ) :
    ∑ x ∈ partitionFinset a b e, g x =
      ∑ k ∈ Finset.range (widthPartitionCard a b e), g (a + k * e) := by
  rw [partitionFinset, Finset.sum_image fun _ _ _ _ h => injective_partition he h]

/-- The first point of the partition is $`a`. -/
theorem widthPartitionPoint_zero {a b e : ℝ} (hab : a ≤ b) :
    widthPartitionPoint a b e 0 = a := by
  simp [widthPartitionPoint, hab]

/-- For $`k < N` the $`k`-th point of the partition is $`a + k\varepsilon`. -/
theorem widthPartitionPoint_of_lt {a b e : ℝ} (he : 0 < e) {k : ℕ}
    (hk : k < widthPartitionCard a b e) :
    widthPartitionPoint a b e k = a + k * e :=
  min_eq_left ((lt_widthPartitionCard_iff he).1 hk).le

/-- The last point of the partition is $`b`. -/
theorem widthPartitionPoint_widthPartitionCard {a b e : ℝ} (he : 0 < e) :
    widthPartitionPoint a b e (widthPartitionCard a b e) = b := by
  have h : ¬ widthPartitionCard a b e < widthPartitionCard a b e := lt_irrefl _
  rw [lt_widthPartitionCard_iff he] at h
  exact min_eq_right (not_lt.1 h)

/-- The points of the partition increase. -/
theorem widthPartitionPoint_le_succ {a b e : ℝ} (he : 0 < e) (k : ℕ) :
    widthPartitionPoint a b e k ≤ widthPartitionPoint a b e (k + 1) := by
  refine min_le_min ?_ le_rfl
  push_cast
  nlinarith

/-- The points of the partition are at least $`a`. -/
theorem le_widthPartitionPoint {a b e : ℝ} (hab : a ≤ b) (he : 0 < e) (k : ℕ) :
    a ≤ widthPartitionPoint a b e k := by
  have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) he.le
  exact le_min (by linarith) hab

/-- The points of the partition are at most $`b`. -/
theorem widthPartitionPoint_le (a b e : ℝ) (k : ℕ) : widthPartitionPoint a b e k ≤ b :=
  min_le_right _ _

/-- Consecutive points of the partition are at most $`\varepsilon` apart. -/
theorem widthPartitionPoint_succ_sub_le {a b e : ℝ} (he : 0 < e) (k : ℕ) :
    widthPartitionPoint a b e (k + 1) - widthPartitionPoint a b e k ≤ e := by
  unfold widthPartitionPoint
  push_cast
  rcases le_total (a + k * e) b with h | h
  · rw [min_eq_left h]
    have := min_le_left (a + (k + 1) * e) b
    linarith
  · rw [min_eq_right h, min_eq_right (by nlinarith)]
    linarith

/-- **Section 12.7 (and 9.2), the standard fact.** For a continuous function on $`[a, b]`, the
ordinary Riemann sums $`S_a^b(f, \varepsilon)` converge to the integral as the width
$`\varepsilon` tends to $`0`. By uniform continuity, on each subinterval the function stays
within a small constant of its value at the left end point, so each term of the sum is close to
the integral over its subinterval. -/
theorem abs_riemannSum_sub_integral_lt {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ e, 0 < e → e < η → |riemannSum f a b e - ∫ x in a..b, f x| < δ := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at huc
  have hba : 0 < b - a := sub_pos.2 hab
  have hc : 0 < δ / (2 * (b - a)) := div_pos hδ (by linarith)
  obtain ⟨η, hη, H⟩ := huc _ hc
  refine ⟨η, hη, fun e he heη => ?_⟩
  set n := widthPartitionCard a b e with hn
  set y : ℕ → ℝ := widthPartitionPoint a b e with hy
  have hy0 : y 0 = a := widthPartitionPoint_zero hab.le
  have hyn : y n = b := widthPartitionPoint_widthPartitionCard he
  have hymono : ∀ k, y k ≤ y (k + 1) := widthPartitionPoint_le_succ he
  have hya : ∀ k, a ≤ y k := le_widthPartitionPoint hab.le he
  have hyb : ∀ k, y k ≤ b := widthPartitionPoint_le a b e
  have hstep : ∀ k, y (k + 1) - y k ≤ e := widthPartitionPoint_succ_sub_le he
  have hint : ∀ k < n, IntervalIntegrable f MeasureTheory.volume (y k) (y (k + 1)) :=
    fun k _ => (hf.mono (by
      rw [uIcc_of_le (hymono k)]
      exact Icc_subset_Icc (hya k) (hyb _))).intervalIntegrable
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [hy0, hyn] at hsum
  rw [riemannSum, ← hsum, ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.range n,
      |f (y k) * (y (k + 1) - y k) - ∫ x in y k..y (k + 1), f x| ≤
        δ / (2 * (b - a)) * (y (k + 1) - y k) := by
    intro k hk
    have hk' := hint k (Finset.mem_range.1 hk)
    have e1 : f (y k) * (y (k + 1) - y k) - ∫ x in y k..y (k + 1), f x =
        ∫ x in y k..y (k + 1), (f (y k) - f x) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hk',
        intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    rw [e1]
    have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := y k) (b := y (k + 1))
      (f := fun x => f (y k) - f x) (C := δ / (2 * (b - a))) (by
        intro x hx
        rw [uIoc_of_le (hymono k)] at hx
        rw [Real.norm_eq_abs, ← Real.dist_eq]
        refine (H (y k) ⟨hya k, hyb k⟩ x ⟨(hya k).trans hx.1.le, hx.2.trans (hyb _)⟩ ?_).le
        rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 hx.1)]
        linarith [hx.2, hstep k])
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (hymono k))] at h2
  calc |∑ k ∈ Finset.range n, (f (y k) * (y (k + 1) - y k) - ∫ x in y k..y (k + 1), f x)|
      ≤ ∑ k ∈ Finset.range n,
          |f (y k) * (y (k + 1) - y k) - ∫ x in y k..y (k + 1), f x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, δ / (2 * (b - a)) * (y (k + 1) - y k) := Finset.sum_le_sum hterm
    _ = δ / (2 * (b - a)) * (b - a) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub, hyn, hy0]
    _ = δ / 2 := by field_simp
    _ < δ := by linarith

/-- **Section 12.7 (and 9.2).** The ordinary Riemann sums $`S_a^b(f, \varepsilon)` of $`f`
_converge_ to the real number $`I` as the width $`\varepsilon` tends to $`0` through positive
values. This is the conclusion of the analysis of Section 9.2 for a function that is Riemann
integrable on $`[a, b]` with integral $`I`, and it is the only fact about integrability that
Section 12.7 uses. It is stated here as a predicate, to be discharged by Chapter 9 for
integrable functions; the theorem {lit}`riemannSumsConverge_integral_of_continuousOn` below
discharges it for continuous functions. -/
def RiemannSumsConverge (f : ℝ → ℝ) (a b I : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ η > 0, ∀ e, 0 < e → e < η → |riemannSum f a b e - I| < δ

/-- **Section 12.7 (and 9.2).** The Riemann sums of a function continuous on $`[a, b]` converge
to its integral. -/
theorem riemannSumsConverge_integral_of_continuousOn {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) : RiemannSumsConverge f a b (∫ x in a..b, f x) :=
  fun _ hδ => abs_riemannSum_sub_integral_lt hab hf hδ

/-- The limit of the Riemann sums is unique. -/
theorem RiemannSumsConverge.unique {f : ℝ → ℝ} {a b I J : ℝ} (hI : RiemannSumsConverge f a b I)
    (hJ : RiemannSumsConverge f a b J) : I = J := by
  by_contra hne
  have hpos : 0 < |I - J| / 2 := half_pos (abs_pos.2 (sub_ne_zero.2 hne))
  obtain ⟨η₁, hη₁, H₁⟩ := hI _ hpos
  obtain ⟨η₂, hη₂, H₂⟩ := hJ _ hpos
  have he : 0 < min η₁ η₂ / 2 := half_pos (lt_min hη₁ hη₂)
  have h1 := H₁ _ he (by linarith [min_le_left η₁ η₂])
  have h2 := H₂ _ he (by linarith [min_le_right η₁ η₂])
  have h3 : |I - J| ≤ |riemannSum f a b (min η₁ η₂ / 2) - I| +
      |riemannSum f a b (min η₁ η₂ / 2) - J| := by
    rw [abs_sub_comm (riemannSum f a b (min η₁ η₂ / 2)) I]
    exact abs_sub_le _ _ _
  linarith

/-- **Section 12.7, the standard fact.** For a function that is bounded on $`[a, b]`, the sum
$`\bigl(\sum_{x \in P_\varepsilon} f(x)\bigr)\varepsilon` differs from the ordinary Riemann
sum $`S_a^b(f, \varepsilon)` by at most a constant multiple of $`\varepsilon`: the two sums
differ only in the width given to the last subinterval. -/
theorem abs_uniformSum_sub_riemannSum_le {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M) :
    ∃ M : ℝ, ∀ e, 0 < e → |uniformSum f a b e - riemannSum f a b e| ≤ M * e := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨|M|, fun e he => ?_⟩
  set n := widthPartitionCard a b e with hn
  set y : ℕ → ℝ := widthPartitionPoint a b e with hy
  have hyk : ∀ k ∈ Finset.range n, y k = a + k * e := fun k hk =>
    widthPartitionPoint_of_lt he (Finset.mem_range.1 hk)
  have hU : uniformSum f a b e = ∑ k ∈ Finset.range n, f (y k) * e :=
    Finset.sum_congr rfl fun k hk => by rw [hyk k hk]
  rw [hU, riemannSum, ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.range n,
      |f (y k) * e - f (y k) * (y (k + 1) - y k)| ≤ |M| * (e - (y (k + 1) - y k)) := by
    intro k hk
    have hmem : y k ∈ Icc a b :=
      ⟨le_widthPartitionPoint hab.le he k, widthPartitionPoint_le a b e k⟩
    have h1 : 0 ≤ e - (y (k + 1) - y k) := sub_nonneg.2 (widthPartitionPoint_succ_sub_le he k)
    rw [← mul_sub, abs_mul, abs_of_nonneg h1]
    exact mul_le_mul_of_nonneg_right
      ((hM _ hmem).trans (le_abs_self M)) h1
  have hy0 : y 0 = a := widthPartitionPoint_zero hab.le
  have hyn : y n = b := widthPartitionPoint_widthPartitionCard he
  have hceil : (n : ℝ) * e - (b - a) ≤ e := by
    have h1 : (n : ℝ) < (b - a) / e + 1 := Nat.ceil_lt_add_one (div_nonneg (by linarith) he.le)
    have h2 : (n : ℝ) * e < ((b - a) / e + 1) * e := mul_lt_mul_of_pos_right h1 he
    have h3 : ((b - a) / e + 1) * e = (b - a) + e := by field_simp
    linarith
  calc |∑ k ∈ Finset.range n, (f (y k) * e - f (y k) * (y (k + 1) - y k))|
      ≤ ∑ k ∈ Finset.range n, |f (y k) * e - f (y k) * (y (k + 1) - y k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, |M| * (e - (y (k + 1) - y k)) := Finset.sum_le_sum hterm
    _ = |M| * (n * e - (b - a)) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_range_sub, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, hyn, hy0]
    _ ≤ |M| * e := mul_le_mul_of_nonneg_left hceil (abs_nonneg M)

end RealRiemannSums

section HyperfinitePartition

/-- **Section 12.7.** The hyperfinite partition determined by a width $`\Delta x`: the set
$`P` of the points $`a + k\,\Delta x`, for $`k` a hypernatural, that lie below $`b`. Together
with $`b` it divides $`[a, b]` into subintervals of width $`\Delta x`, with a possibly smaller
last one. -/
def hpartition (a b Δ : ℝ*) : Set ℝ* := {x : ℝ* | ∃ k ∈ ℕ*, x = a + k * Δ ∧ x < b}

/-- **Section 12.7.** For real $`a`, $`b` and $`\Delta x = [\varepsilon_n]`, the set $`P` is
the internal set $`[P_n]` of the sets of points $`a + k\varepsilon_n` below $`b`. -/
theorem hpartition_eq_internalSet (a b : ℝ) (e : ℕ → ℝ) :
    hpartition a b (Hyperreal.ofSeq e) =
      internalSet fun n => {x : ℝ | ∃ k : ℕ, x = a + k * e n ∧ x < b} := by
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [hyperreal_ofSeq_mem_internalSet]
  constructor
  · rintro ⟨k, hk, hx, hxb⟩
    obtain ⟨κ, rfl⟩ := exists_hnat_eq hk
    have hx' : Hyperreal.ofSeq r = Hyperreal.ofSeq fun n => a + (κ n : ℝ) * e n := hx
    have hxb' : Hyperreal.ofSeq r < Hyperreal.ofSeq fun _ => b := hxb
    exact ((ofSeq_eq_ofSeq_iff.1 hx').and (ofSeq_lt_ofSeq_iff.1 hxb')).mono fun n hn =>
      ⟨κ n, hn.1, hn.2⟩
  · intro h
    obtain ⟨κ, hκ⟩ := exists_seq_of_almostAll_exists h
    refine ⟨hnat κ, hnat_mem_hyperNat κ, ?_, ?_⟩
    · change Hyperreal.ofSeq r = Hyperreal.ofSeq fun n => a + (κ n : ℝ) * e n
      exact ofSeq_eq_ofSeq_iff.2 (hκ.mono fun n hn => hn.1)
    · change Hyperreal.ofSeq r < Hyperreal.ofSeq fun _ => b
      exact ofSeq_lt_ofSeq_iff.2 (hκ.mono fun n hn => hn.2)

/-- A hyperreal $`[\varepsilon_n]` is positive if and only if almost all $`\varepsilon_n`
are. -/
theorem ofSeq_pos_iff {e : ℕ → ℝ} :
    0 < Hyperreal.ofSeq e ↔ ∀ᶠ n in hyperfilter ℕ, 0 < e n := by
  change Hyperreal.ofSeq (fun _ => (0 : ℝ)) < _ ↔ _
  rw [ofSeq_lt_ofSeq_iff]

/-- **Section 12.7.** For a positive $`\Delta x = [\varepsilon_n]`, the set $`P` is the
internal set of the finite sets $`P_{\varepsilon_n}`. -/
theorem hpartition_eq_internalSet_finset (a b : ℝ) {e : ℕ → ℝ} (he : 0 < Hyperreal.ofSeq e) :
    hpartition a b (Hyperreal.ofSeq e) =
      internalSet fun n => (partitionFinset a b (e n) : Set ℝ) := by
  rw [hpartition_eq_internalSet]
  exact internalSet_congr ((ofSeq_pos_iff.1 he).mono fun n hn => (coe_partitionFinset hn).symm)

/-- **Section 12.7.** For real $`a`, $`b` and a positive hyperreal $`\Delta x`, the partition
$`P` is hyperfinite. -/
theorem isHyperfinite_hpartition (a b : ℝ) {Δ : ℝ*} (hΔ : 0 < Δ) :
    IsHyperfinite (hpartition a b Δ) := by
  obtain ⟨e, rfl⟩ := hyperreal_exists_rep Δ
  rw [hpartition_eq_internalSet_finset a b hΔ]
  exact isHyperfiniteSet_internalSet_finset _

/-- **Section 12.7.** The internal size $`N = [N_n]` of the hyperfinite partition $`P` is the
value at $`\Delta x` of the extension of the function that counts the points of
$`P_\varepsilon`. -/
theorem hcard_hpartition (a b : ℝ) {Δ : ℝ*} (hΔ : 0 < Δ) :
    hcard (hpartition a b Δ) =
      (⋆(fun e : ℝ => (widthPartitionCard a b e : ℝ)) : ℝ* → ℝ*) Δ := by
  obtain ⟨e, rfl⟩ := hyperreal_exists_rep Δ
  rw [hpartition_eq_internalSet_finset a b hΔ]
  unfold hcard
  rw [internalCard_internalSet_finset, starMap_hyperreal_ofSeq]
  exact ofSeq_eq_ofSeq_iff.2 ((ofSeq_pos_iff.1 hΔ).mono fun n hn =>
    congrArg Nat.cast (card_partitionFinset hn))

/-- **Exercise 12.7.1.** For a positive $`\Delta x`, the hyperfinite partition $`P` of
internal size $`N` is the set of the points $`a + k\,\Delta x` with $`k` a hypernatural below
$`N`. In particular each member of $`P` has this form. -/
theorem hpartition_eq_setOf_lt_hcard (a b : ℝ) {Δ : ℝ*} (hΔ : 0 < Δ) :
    hpartition a b Δ =
      {x : ℝ* | ∃ k ∈ ℕ*, k < hcard (hpartition a b Δ) ∧ x = a + k * Δ} := by
  obtain ⟨e, rfl⟩ := hyperreal_exists_rep Δ
  have hN : hcard (hpartition a b (Hyperreal.ofSeq e)) =
      hnat fun n => widthPartitionCard a b (e n) := by
    rw [hcard_hpartition a b hΔ]
    rfl
  have hpos := ofSeq_pos_iff.1 hΔ
  rw [hN]
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [hpartition_eq_internalSet, hyperreal_ofSeq_mem_internalSet]
  constructor
  · intro h
    obtain ⟨κ, hκ⟩ := exists_seq_of_almostAll_exists h
    refine ⟨hnat κ, hnat_mem_hyperNat κ, hnat_lt_hnat_iff.2 ?_, ?_⟩
    · filter_upwards [hκ, hpos] with n h1 h2
      exact (lt_widthPartitionCard_iff h2).2 (h1.1 ▸ h1.2)
    · change Hyperreal.ofSeq r = Hyperreal.ofSeq fun n => a + (κ n : ℝ) * e n
      exact ofSeq_eq_ofSeq_iff.2 (hκ.mono fun n hn => hn.1)
  · rintro ⟨k, hk, hkN, hx⟩
    obtain ⟨κ, rfl⟩ := exists_hnat_eq hk
    have hx' : Hyperreal.ofSeq r = Hyperreal.ofSeq fun n => a + (κ n : ℝ) * e n := hx
    filter_upwards [ofSeq_eq_ofSeq_iff.1 hx', hnat_lt_hnat_iff.1 hkN, hpos] with n h1 h2 h3
    exact ⟨κ n, h1, h1 ▸ (lt_widthPartitionCard_iff h3).1 h2⟩

/-- **Exercise 12.7.1.** Each member of the hyperfinite partition $`P` has the form
$`a + k\,\Delta x` for a hypernatural $`k` below the internal size $`N` of $`P`. -/
theorem exists_lt_hcard_of_mem_hpartition (a b : ℝ) {Δ : ℝ*} (hΔ : 0 < Δ) {x : ℝ*}
    (hx : x ∈ hpartition a b Δ) :
    ∃ k ∈ ℕ*, k < hcard (hpartition a b Δ) ∧ x = a + k * Δ := by
  rw [hpartition_eq_setOf_lt_hcard a b hΔ] at hx
  exact hx

/-- **Section 12.7.** For $`a < b` and a positive infinitesimal $`\Delta x`, the internal size
of the hyperfinite partition is unlimited: the partition is hyperfinite but not finite. -/
theorem unlimited_hcard_hpartition {a b : ℝ} (hab : a < b) {Δ : ℝ*} (hΔ : PosInfinitesimal Δ) :
    Unlimited (hcard (hpartition a b Δ)) := by
  obtain ⟨e, rfl⟩ := hyperreal_exists_rep Δ
  refine Or.inl fun r => ?_
  rw [hcard_hpartition a b hΔ.1, starMap_hyperreal_ofSeq, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
  have hba : 0 < b - a := sub_pos.2 hab
  have hr1 : (0 : ℝ) < |r| + 1 := by positivity
  have h1 : Hyperreal.ofSeq e < Hyperreal.ofSeq fun _ => (b - a) / (|r| + 1) :=
    hΔ.2 _ (div_pos hba hr1)
  filter_upwards [ofSeq_pos_iff.1 hΔ.1, ofSeq_lt_ofSeq_iff.1 h1] with n h2 h3
  have h4 : |r| + 1 < (b - a) / e n := by
    rw [lt_div_iff₀ h2]
    rw [lt_div_iff₀ hr1] at h3
    linarith [mul_comm (e n) (|r| + 1)]
  calc r ≤ |r| := le_abs_self r
    _ < (b - a) / e n := by linarith
    _ ≤ (widthPartitionCard a b (e n) : ℝ) := Nat.le_ceil _

/-- **Section 12.7.** The hyperfinite sum of the extension $`{}^*f` of a real function over
the hyperfinite partition $`P` is the class of the sequence of the finite sums over
$`P_{\varepsilon_n}`: $`\sum_{x \in P} f(x) = \bigl[\sum_{x \in P_n} f(x)\bigr]`. -/
theorem hsum_starMap_hpartition (f : ℝ → ℝ) (a b : ℝ) {e : ℕ → ℝ}
    (he : 0 < Hyperreal.ofSeq e) :
    hsum ((⋆f : ℝ* → ℝ*) : ℝ* →. ℝ*) (hpartition a b (Hyperreal.ofSeq e)) =
      Hyperreal.ofSeq fun n => ∑ x ∈ partitionFinset a b (e n), f x := by
  rw [hpartition_eq_internalSet_finset a b he, ← internalMap_const]
  exact internalSum_internalMap_finset (fun _ => f) _

/-- **Section 12.7.** The width may be taken out of the hyperfinite Riemann sum:
$`\sum_{x \in P} f(x)\,\Delta x = \bigl(\sum_{x \in P} f(x)\bigr)\Delta x`. -/
theorem hsum_starMap_mul_hpartition (f : ℝ → ℝ) (a b : ℝ) {Δ : ℝ*} (hΔ : 0 < Δ) :
    hsum ((fun x => (⋆f : ℝ* → ℝ*) x * Δ : ℝ* → ℝ*) : ℝ* →. ℝ*) (hpartition a b Δ) =
      hsum ((⋆f : ℝ* → ℝ*) : ℝ* →. ℝ*) (hpartition a b Δ) * Δ := by
  have h := internalSum_map_mul_right (isInternalPFun_starMap f)
    (isHyperfinite_hpartition a b hΔ) Δ
  rw [← h]
  congr 1

/-- **Section 12.7.** The hyperfinite Riemann sum over $`P` with all widths equal to
$`\Delta x` is the value at $`\Delta x` of the extension of the real function
$`\varepsilon \mapsto \bigl(\sum_{x \in P_\varepsilon} f(x)\bigr)\varepsilon`:
$`\bigl[(\sum_{x \in P_n} f(x))\,\varepsilon_n\bigr] = \bigl(\sum_{x \in P} f(x)\bigr)
\Delta x`. -/
theorem starMap_uniformSum_eq_hsum_mul (f : ℝ → ℝ) (a b : ℝ) {Δ : ℝ*} (hΔ : 0 < Δ) :
    (⋆(uniformSum f a b) : ℝ* → ℝ*) Δ =
      hsum ((⋆f : ℝ* → ℝ*) : ℝ* →. ℝ*) (hpartition a b Δ) * Δ := by
  obtain ⟨e, rfl⟩ := hyperreal_exists_rep Δ
  rw [hsum_starMap_hpartition f a b hΔ, starMap_hyperreal_ofSeq, ofSeq_mul]
  refine ofSeq_eq_ofSeq_iff.2 ((ofSeq_pos_iff.1 hΔ).mono fun n hn => ?_)
  rw [Pi.mul_apply, sum_partitionFinset hn, uniformSum, Finset.sum_mul]

/-- A hyperreal $`[s_n]` is within a real $`\delta` of a real $`c` if and only if almost all
$`s_n` are. -/
theorem abs_ofSeq_sub_coe_lt_iff {s : ℕ → ℝ} {c δ : ℝ} :
    |Hyperreal.ofSeq s - (c : ℝ*)| < (δ : ℝ*) ↔ ∀ᶠ n in hyperfilter ℕ, |s n - c| < δ := by
  change |Hyperreal.ofSeq s - Hyperreal.ofSeq fun _ => c| < Hyperreal.ofSeq (fun _ => δ) ↔ _
  rw [ofSeq_sub, abs_ofSeq, ofSeq_lt_ofSeq_iff]
  rfl

/-- **Section 12.7 (and 9.2), the nonstandard step.** If the Riemann sums of $`f` over
$`[a, b]` converge to $`I`, then for every positive infinitesimal $`\Delta x` the extended
ordinary Riemann sum $`S_a^b(f, \Delta x)` is infinitely close to $`I`. Given a real tolerance,
the real Riemann sums are within it of $`I` for all small enough real widths, and almost all
terms of a sequence representing $`\Delta x` are that small. -/
theorem RiemannSumsConverge.infClose_starMap_riemannSum {f : ℝ → ℝ} {a b I : ℝ}
    (hI : RiemannSumsConverge f a b I) {Δ : ℝ*} (hΔ : PosInfinitesimal Δ) :
    (⋆(riemannSum f a b) : ℝ* → ℝ*) Δ ≊ (I : ℝ*) := by
  obtain ⟨e, rfl⟩ := hyperreal_exists_rep Δ
  rw [infClose_iff_abs_lt]
  intro δ hδ
  obtain ⟨η, hη, H⟩ := hI δ hδ
  rw [starMap_hyperreal_ofSeq, abs_ofSeq_sub_coe_lt_iff]
  have h1 : Hyperreal.ofSeq e < Hyperreal.ofSeq fun _ => η := hΔ.2 η hη
  filter_upwards [ofSeq_pos_iff.1 hΔ.1, ofSeq_lt_ofSeq_iff.1 h1] with n h2 h3 using H _ h2 h3

/-- **Section 12.7 (and 9.2), nonstandard characterization.** The Riemann sums of $`f` over
$`[a, b]` converge to $`I` if and only if the extended Riemann sum $`S_a^b(f, \Delta x)` is
infinitely close to $`I` for every positive infinitesimal $`\Delta x`. For the converse, if the
real sums did not converge there would be a tolerance $`\delta` and widths $`\varepsilon_n <
1/(n+1)` whose sums stay $`\delta` away from $`I`; the class of $`(\varepsilon_n)` is then a
positive infinitesimal at which the extended sum is not infinitely close to $`I`. -/
theorem riemannSumsConverge_iff_forall_infClose {f : ℝ → ℝ} {a b I : ℝ} :
    RiemannSumsConverge f a b I ↔
      ∀ Δ : ℝ*, PosInfinitesimal Δ → (⋆(riemannSum f a b) : ℝ* → ℝ*) Δ ≊ (I : ℝ*) := by
  refine ⟨fun hI Δ hΔ => hI.infClose_starMap_riemannSum hΔ, fun H => ?_⟩
  by_contra hcon
  unfold RiemannSumsConverge at hcon
  push Not at hcon
  obtain ⟨δ, hδ, hbad⟩ := hcon
  have hch : ∀ n : ℕ, ∃ e : ℝ, 0 < e ∧ e < 1 / ((n : ℝ) + 1) ∧ δ ≤ |riemannSum f a b e - I| :=
    fun n => hbad _ (by positivity)
  choose e he0 he1 he2 using hch
  have hΔ : PosInfinitesimal (Hyperreal.ofSeq e) := by
    refine ⟨ofSeq_pos_iff.2 (Eventually.of_forall he0), fun r hr => ?_⟩
    change Hyperreal.ofSeq e < Hyperreal.ofSeq fun _ => r
    rw [ofSeq_lt_ofSeq_iff]
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr
    refine eventually_hyperfilter_of_forall_ge m fun n hn => (he1 n).trans_le (le_trans ?_ hm.le)
    have hmn : (m : ℝ) ≤ n := Nat.cast_le.2 hn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have h := H _ hΔ
  rw [infClose_iff_abs_lt] at h
  have h' := h δ hδ
  rw [starMap_hyperreal_ofSeq, abs_ofSeq_sub_coe_lt_iff] at h'
  obtain ⟨n, hn⟩ := h'.exists
  exact absurd hn (not_lt.2 (he2 n))

/-- **Section 12.7.** For a function $`f` bounded on $`[a, b]` and a positive infinitesimal
$`\Delta x`, the extended ordinary Riemann sum $`S_a^b(f, \Delta x)` is infinitely close to the
hyperfinite sum $`\bigl(\sum_{x \in P} f(x)\bigr)\Delta x`. The book writes an equality here;
the two differ in the width of the last subinterval, which is $`\Delta x` in the hyperfinite
sum and $`b - x_{N-1}` in the Riemann sum of Section 9.1, so in general they are only
infinitely close. Boundedness, which every Riemann integrable function has, is what makes the
difference infinitesimal. -/
theorem infClose_starMap_riemannSum_hsum_mul {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M) {Δ : ℝ*} (hΔ : PosInfinitesimal Δ) :
    (⋆(riemannSum f a b) : ℝ* → ℝ*) Δ ≊
      hsum ((⋆f : ℝ* → ℝ*) : ℝ* →. ℝ*) (hpartition a b Δ) * Δ := by
  rw [← starMap_uniformSum_eq_hsum_mul f a b hΔ.1]
  obtain ⟨e, rfl⟩ := hyperreal_exists_rep Δ
  obtain ⟨M, hM⟩ := abs_uniformSum_sub_riemannSum_le hab hf
  refine InfClose.symm ?_
  rw [infClose_iff_abs_lt]
  intro δ hδ
  rw [starMap_hyperreal_ofSeq, starMap_hyperreal_ofSeq, ofSeq_sub, abs_ofSeq, coe_eq_ofSeq_const,
    ofSeq_lt_ofSeq_iff]
  have hM1 : (0 : ℝ) < |M| + 1 := by positivity
  have h1 : Hyperreal.ofSeq e < Hyperreal.ofSeq fun _ => δ / (|M| + 1) :=
    hΔ.2 _ (div_pos hδ hM1)
  filter_upwards [ofSeq_pos_iff.1 hΔ.1, ofSeq_lt_ofSeq_iff.1 h1] with n h2 h3
  rw [lt_div_iff₀ hM1] at h3
  calc |uniformSum f a b (e n) - riemannSum f a b (e n)| ≤ M * e n := hM _ h2
    _ ≤ |M| * e n := mul_le_mul_of_nonneg_right (le_abs_self M) h2.le
    _ < δ := by nlinarith

/-- **Section 12.7, the integral as a hyperfinite sum.** Let $`f` be bounded on $`[a, b]` with
Riemann sums converging to $`I`. Then for every positive infinitesimal $`\Delta x` the
hyperfinite Riemann sum $`\sum_{x \in P} f(x)\,\Delta x` over the hyperfinite partition $`P` is
infinitely close to $`I`. -/
theorem RiemannSumsConverge.infClose_hsum_hpartition {f : ℝ → ℝ} {a b I : ℝ} (hab : a < b)
    (hf : ∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M) (hI : RiemannSumsConverge f a b I) {Δ : ℝ*}
    (hΔ : PosInfinitesimal Δ) :
    hsum ((fun x => (⋆f : ℝ* → ℝ*) x * Δ : ℝ* → ℝ*) : ℝ* →. ℝ*) (hpartition a b Δ) ≊
      (I : ℝ*) := by
  rw [hsum_starMap_mul_hpartition f a b hΔ.1]
  exact (infClose_starMap_riemannSum_hsum_mul hab hf hΔ).symm.trans
    (hI.infClose_starMap_riemannSum hΔ)

/-- **Section 12.7, the integral as a hyperfinite sum, general form.** Let $`f` be bounded on
$`[a, b]`, $`a < b`, with Riemann sums $`S_a^b(f, \varepsilon)` converging to the real number
$`I` as $`\varepsilon \to 0^+`. Then for any positive infinitesimal $`\Delta x`,
$$`I = \operatorname{sh}\bigl(S_a^b(f, \Delta x)\bigr)
  = \operatorname{sh}\Bigl(\sum_{x \in P} f(x)\,\Delta x\Bigr).`
The book states this for a function Riemann integrable on $`[a, b]`, with $`I` its integral.
Such a function is bounded, and Section 9.2 shows that its Riemann sums converge to the
integral; those two facts are the hypotheses here, since Chapter 9 is not available to this
chapter. Everything the present section adds to them is proved. -/
theorem RiemannSumsConverge.eq_sh_hsum_hpartition {f : ℝ → ℝ} {a b I : ℝ} (hab : a < b)
    (hf : ∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M) (hI : RiemannSumsConverge f a b I) {Δ : ℝ*}
    (hΔ : PosInfinitesimal Δ) :
    I = sh ((⋆(riemannSum f a b) : ℝ* → ℝ*) Δ) ∧
      I = sh (hsum ((fun x => (⋆f : ℝ* → ℝ*) x * Δ : ℝ* → ℝ*) : ℝ* →. ℝ*)
        (hpartition a b Δ)) :=
  ⟨(sh_eq_of_infClose (hI.infClose_starMap_riemannSum hΔ)).symm,
    (sh_eq_of_infClose (hI.infClose_hsum_hpartition hab hf hΔ)).symm⟩

/-- A function continuous on $`[a, b]` is bounded there. -/
theorem exists_abs_le_of_continuousOn_Icc {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) : ∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact ⟨M, fun x hx => (Real.norm_eq_abs _).symm.le.trans (hM x hx)⟩

/-- **Section 12.7 (and 9.2).** For a continuous function $`f` on $`[a, b]` and a positive
infinitesimal $`\Delta x`, the extended ordinary Riemann sum $`S_a^b(f, \Delta x)` is
infinitely close to the integral of $`f`. A special case of
{name}`Goldblatt.RiemannSumsConverge.infClose_starMap_riemannSum`. -/
theorem infClose_starMap_riemannSum_integral {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) {Δ : ℝ*} (hΔ : PosInfinitesimal Δ) :
    (⋆(riemannSum f a b) : ℝ* → ℝ*) Δ ≊ ((∫ x in a..b, f x : ℝ) : ℝ*) :=
  (riemannSumsConverge_integral_of_continuousOn hab hf).infClose_starMap_riemannSum hΔ

/-- **Section 12.7, the integral as a hyperfinite sum, continuous case.** For a continuous
function $`f` on $`[a, b]` and a positive infinitesimal $`\Delta x`, the hyperfinite Riemann sum
$`\sum_{x \in P} f(x)\,\Delta x` over the hyperfinite partition $`P` is infinitely close to the
integral of $`f` over $`[a, b]`. A special case of
{name}`Goldblatt.RiemannSumsConverge.infClose_hsum_hpartition`. -/
theorem infClose_hsum_hpartition_integral {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) {Δ : ℝ*} (hΔ : PosInfinitesimal Δ) :
    hsum ((fun x => (⋆f : ℝ* → ℝ*) x * Δ : ℝ* → ℝ*) : ℝ* →. ℝ*) (hpartition a b Δ) ≊
      ((∫ x in a..b, f x : ℝ) : ℝ*) :=
  (riemannSumsConverge_integral_of_continuousOn hab hf).infClose_hsum_hpartition hab
    (exists_abs_le_of_continuousOn_Icc hf) hΔ

/-- **Section 12.7, the integral as a hyperfinite sum, continuous case.** For a continuous
function $`f` on $`[a, b]` and any positive infinitesimal $`\Delta x`,
$$`\int_a^b f(x)\,dx = \operatorname{sh}\bigl(S_a^b(f, \Delta x)\bigr)
  = \operatorname{sh}\Bigl(\sum_{x \in P} f(x)\,\Delta x\Bigr),`
with Mathlib's interval integral on the left. This is the corollary of the general form
{name}`Goldblatt.RiemannSumsConverge.eq_sh_hsum_hpartition` in the one case where the
convergence of the Riemann sums is proved in this chapter
({name}`Goldblatt.abs_riemannSum_sub_integral_lt`); the book's statement for all Riemann
integrable functions is the general form together with Section 9.2. -/
theorem integral_eq_sh_hsum_hpartition {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) {Δ : ℝ*} (hΔ : PosInfinitesimal Δ) :
    ∫ x in a..b, f x = sh ((⋆(riemannSum f a b) : ℝ* → ℝ*) Δ) ∧
      ∫ x in a..b, f x =
        sh (hsum ((fun x => (⋆f : ℝ* → ℝ*) x * Δ : ℝ* → ℝ*) : ℝ* →. ℝ*) (hpartition a b Δ)) :=
  (riemannSumsConverge_integral_of_continuousOn hab hf).eq_sh_hsum_hpartition hab
    (exists_abs_le_of_continuousOn_Icc hf) hΔ

/-- **Section 12.7, non-vacuity.** The integral of the identity function over $`[0, 1]` is the
shadow of the hyperfinite sum $`\sum_{x \in P} x\,\varepsilon` over the partition of width the
infinitesimal $`\varepsilon`, so that shadow is $`\tfrac12`. -/
theorem sh_hsum_id_epsilon :
    sh (hsum ((fun x => (⋆(fun t : ℝ => t) : ℝ* → ℝ*) x * ε : ℝ* → ℝ*) : ℝ* →. ℝ*)
      (hpartition (0 : ℝ) (1 : ℝ) ε)) = 1 / 2 := by
  have hε : PosInfinitesimal (ε : ℝ*) := epsilon_pos_infinitesimal
  rw [← (integral_eq_sh_hsum_hpartition (f := fun t : ℝ => t) zero_lt_one
    continuous_id.continuousOn hε).2]
  simp

end HyperfinitePartition

end Goldblatt
