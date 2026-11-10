import Goldblatt.Ch12_InternalFunctions.Functions

/-!
# 12 (part 2). Hyperfinite Sets: Sections 12.3 to 12.6

This is the second of three parts of Chapter 12 (the overview is on the chapter page
{lit}`Goldblatt.Ch12_InternalFunctions`). It defines hyperfinite sets and their internal
cardinality, proves the exercises on hyperfiniteness, characterizes hyperfinite sets by internal
bijections with initial segments of the hypernaturals, and proves the hyperfinite pigeonhole
principle.
-/

universe u v

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal

/-!
## 12.3 Hyperfinite Sets

An internal set $`[A_n]` is _hyperfinite_ when almost all of the sets $`A_n` are finite. Such a
set need not be finite, and when it is infinite it is uncountable, but it has a size: the
hypernatural number $`[|A_n|]`, its _internal cardinality_. The examples of the section are the
initial segments $`\{1, \dots, N\}` of the hypernaturals, hyperfinite grids, finite sets, and
the hyperfinite sets squeezed between a countable set and its enlargement.

In the formalization hyperfiniteness is a predicate on sets of elements of a star type,
{lit}`Goldblatt.IsHyperfiniteSet`, with the abbreviation {lit}`Goldblatt.IsHyperfinite` for sets
of hyperreals. The internal cardinality {lit}`Goldblatt.internalCard` (for hyperreals,
{lit}`Goldblatt.hcard`) is a hyperreal that lies in the set of hypernaturals. It is defined for
every set, with the value $`0` for sets that are not internal, and for an internal set
$`[A_n]` it is the class of the sequence of cardinalities, where the cardinality of an infinite
set is taken to be $`0`.
-/

section Hyperfinite

variable {α αS : Type u} [StarType α αS]

/-- **Section 12.3.** A set of elements of the star type of $`\alpha` is _hyperfinite_ if it is
the internal set $`[A_n]` of a sequence of sets almost all of which are finite. -/
def IsHyperfiniteSet (α : Type u) {αS : Type u} [StarType α αS] (X : Set αS) : Prop :=
  ∃ A : ℕ → Set α, X = internalSet A ∧ ∀ᶠ n in hyperfilter ℕ, (A n).Finite

/-- **Section 12.3.** A set of hyperreals is _hyperfinite_ if it is $`[A_n]` for a sequence of
sets of reals almost all of which are finite. -/
abbrev IsHyperfinite (X : Set ℝ*) : Prop := IsHyperfiniteSet ℝ X

/-- **Section 12.3.** A hyperfinite set is internal. -/
theorem IsHyperfiniteSet.isInternalSet {X : Set αS} (h : IsHyperfiniteSet α X) :
    IsInternalSet α X := by
  obtain ⟨A, hA, -⟩ := h
  exact ⟨A, hA⟩

/-- **Section 12.3.** The internal set $`[A_n]` is hyperfinite if and only if $`A_n` is finite
for almost all $`n`: hyperfiniteness does not depend on the defining sequence. -/
theorem isHyperfiniteSet_internalSet_iff {A : ℕ → Set α} :
    IsHyperfiniteSet α (internalSet A : Set αS) ↔ ∀ᶠ n in hyperfilter ℕ, (A n).Finite := by
  constructor
  · rintro ⟨B, hAB, hB⟩
    filter_upwards [internalSet_eq_iff.1 hAB, hB] with n h1 h2
    rw [h1]
    exact h2
  · exact fun h => ⟨A, rfl, h⟩

/-- **Section 12.3.** The internal set $`[A_n]` fails to be hyperfinite if and only if $`A_n`
is infinite for almost all $`n`. -/
theorem not_isHyperfiniteSet_internalSet_iff {A : ℕ → Set α} :
    ¬ IsHyperfiniteSet α (internalSet A : Set αS) ↔ ∀ᶠ n in hyperfilter ℕ, (A n).Infinite := by
  rw [isHyperfiniteSet_internalSet_iff, ← almostAll_not]
  rfl

/-- **Section 12.3.** A hyperfinite set is defined by a sequence _all_ of whose terms are
finite: the defining sequence can always be changed on a negligible set of indices so that
every term is finite. -/
theorem IsHyperfiniteSet.exists_rep_finite {X : Set αS} (h : IsHyperfiniteSet α X) :
    ∃ A : ℕ → Set α, X = internalSet A ∧ ∀ n, (A n).Finite := by
  obtain ⟨A, rfl, hA⟩ := h
  obtain ⟨A', h1, h2⟩ := internalSet_exists_rep_forall (αS := αS) (P := fun _ S => S.Finite) hA
    (fun _ => ∅) (fun _ => finite_empty)
  exact ⟨A', h1.symm, h2⟩

/-- **Section 12.3.** A set is hyperfinite if and only if it is the internal set of a sequence
of finite sets, given as {name}`Finset`s. -/
theorem isHyperfiniteSet_iff_exists_finset {X : Set αS} :
    IsHyperfiniteSet α X ↔ ∃ A : ℕ → Finset α, X = internalSet fun n => (A n : Set α) := by
  constructor
  · intro h
    obtain ⟨A, rfl, hA⟩ := h.exists_rep_finite
    exact ⟨fun n => (hA n).toFinset, by simp only [Finite.coe_toFinset]⟩
  · rintro ⟨A, rfl⟩
    exact ⟨_, rfl, Eventually.of_forall fun n => (A n).finite_toSet⟩

/-- **Section 12.3.** The internal set of a sequence of finite sets is hyperfinite. -/
theorem isHyperfiniteSet_internalSet_finset (A : ℕ → Finset α) :
    IsHyperfiniteSet α (internalSet (fun n => (A n : Set α)) : Set αS) :=
  isHyperfiniteSet_iff_exists_finset.2 ⟨A, rfl⟩

open Classical in
/-- **Section 12.3.** The _internal cardinality_ of a set of elements of a star type: for an
internal set $`[A_n]` it is the hypernatural $`[|A_n|]`
({lit}`Goldblatt.internalCard_internalSet`), where an infinite $`A_n` counts as $`0`; for a set
that is not internal it is $`0`. It is the size of the set when the set is hyperfinite. -/
noncomputable def internalCard (α : Type u) {αS : Type u} [StarType α αS] (X : Set αS) : ℝ* :=
  if h : IsInternalSet α X then hnat fun n => (h.choose n).ncard else 0

/-- **Section 12.3.** The internal cardinality of a set of hyperreals. -/
noncomputable abbrev hcard (X : Set ℝ*) : ℝ* := internalCard ℝ X

/-- **Section 12.3.** $`|[A_n]| = [|A_n|]`: the internal cardinality of $`[A_n]` is the class
of the sequence of cardinalities, whichever sequence defines the set. -/
theorem internalCard_internalSet (A : ℕ → Set α) :
    internalCard α (internalSet A : Set αS) = hnat fun n => (A n).ncard := by
  have h : IsInternalSet α (internalSet A : Set αS) := isInternalSet_internalSet A
  rw [internalCard]
  split_ifs
  exact hnat_eq_hnat_iff.2 ((internalSet_eq_iff.1 h.choose_spec).mono fun n hn => by rw [hn])

/-- **Section 12.3.** For a sequence of {name}`Finset`s, $`|[A_n]| = [|A_n|]`. -/
theorem internalCard_internalSet_finset (A : ℕ → Finset α) :
    internalCard α (internalSet (fun n => (A n : Set α)) : Set αS) = hnat fun n => (A n).card := by
  rw [internalCard_internalSet]
  simp only [ncard_coe_finset]

/-- **Section 12.3.** The internal cardinality is a hypernatural number. -/
theorem internalCard_mem_hyperNat (X : Set αS) : internalCard α X ∈ ℕ* := by
  rw [internalCard]
  split_ifs with h
  · exact hnat_mem_hyperNat _
  · simpa using natCast_mem_hyperNat 0

/-- **Section 12.3.** The internal cardinality is nonnegative. -/
theorem internalCard_nonneg (X : Set αS) : 0 ≤ internalCard α X :=
  hyperNat_nonneg (internalCard_mem_hyperNat X)

/-- **Section 12.3.** The empty set is hyperfinite. -/
theorem isHyperfiniteSet_empty : IsHyperfiniteSet α (∅ : Set αS) :=
  ⟨fun _ => ∅, by rw [← starSet_eq_internalSet, starSet_empty],
    Eventually.of_forall fun _ => finite_empty⟩

/-- **Section 12.3.** The internal cardinality of the empty set is $`0`. -/
theorem internalCard_empty : internalCard α (∅ : Set αS) = 0 := by
  have h : (∅ : Set αS) = internalSet fun _ : ℕ => (∅ : Set α) := by
    rw [← starSet_eq_internalSet, starSet_empty]
  rw [h, internalCard_internalSet]
  simp only [ncard_empty, hnat_const_zero]

/-- **Section 12.3.** A hyperfinite set of internal cardinality $`0` is empty. -/
theorem IsHyperfiniteSet.eq_empty_of_internalCard_eq_zero {X : Set αS}
    (h : IsHyperfiniteSet α X) (h0 : internalCard α X = 0) : X = ∅ := by
  obtain ⟨A, rfl, hA⟩ := h
  rw [internalCard_internalSet, ← hnat_const_zero, hnat_eq_hnat_iff] at h0
  rw [internalSet_eq_empty_iff]
  filter_upwards [hA, h0] with n h1 h2 using (ncard_eq_zero h1).1 h2

/-- **Section 12.3, third example.** Every finite set of elements of a star type is
hyperfinite: if the elements are the classes of the sequences $`r^1, \dots, r^k`, the set is
$`[A_n]` with $`A_n = \{r^1_n, \dots, r^k_n\}`. Its internal cardinality is its number of
elements, because distinct classes have representatives that differ at almost all indices. -/
theorem isHyperfiniteSet_and_internalCard_of_finite {X : Set αS} (hX : X.Finite) :
    IsHyperfiniteSet α X ∧ internalCard α X = X.ncard := by
  have hfin : Finite X := hX
  choose r hr using fun x : X => ofSeq_surjective (α := α) (x : αS)
  have hXr : X = internalSet fun n => range fun i : X => r i n := by
    rw [internalSet_range_finite]
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, hr ⟨x, hx⟩⟩
    · rintro ⟨i, rfl⟩
      change ofSeq (r i) ∈ X
      rw [hr i]
      exact i.2
  refine ⟨⟨_, hXr, Eventually.of_forall fun n => finite_range _⟩, ?_⟩
  have hinj : ∀ᶠ n in hyperfilter ℕ, Function.Injective fun i : X => r i n := by
    have h1 : ∀ p : X × X, ∀ᶠ n in hyperfilter ℕ, r p.1 n = r p.2 n → p.1 = p.2 := by
      intro p
      by_cases hp : p.1 = p.2
      · exact Eventually.of_forall fun _ _ => hp
      · have hne : (ofSeq (r p.1) : αS) ≠ ofSeq (r p.2) := by
          rw [hr, hr]
          exact fun h => hp (Subtype.ext h)
        exact (Ultrapower.ofSeq_ne_ofSeq.1 hne).mono fun n hn h => absurd h hn
    exact (almostAll_forall_finite.2 h1).mono fun n hn i j hij => hn (i, j) hij
  conv_lhs => rw [hXr]
  rw [internalCard_internalSet, natCast_eq_hnat, hnat_eq_hnat_iff]
  refine hinj.mono fun n hn => ?_
  rw [← image_univ, ncard_image_of_injective _ hn, ncard_univ, Nat.card_coe_set_eq]

/-- **Section 12.3, third example.** Every finite set of elements of a star type is
hyperfinite. -/
theorem isHyperfiniteSet_of_finite {X : Set αS} (hX : X.Finite) : IsHyperfiniteSet α X :=
  (isHyperfiniteSet_and_internalCard_of_finite hX).1

/-- **Section 12.3, third example.** The internal cardinality of a finite set is its number of
elements. -/
theorem internalCard_of_finite {X : Set αS} (hX : X.Finite) : internalCard α X = X.ncard :=
  (isHyperfiniteSet_and_internalCard_of_finite hX).2

/-- **Section 12.3.** The internal cardinality of a singleton is $`1`. -/
theorem internalCard_singleton (x : αS) : internalCard α ({x} : Set αS) = 1 := by
  rw [internalCard_of_finite (finite_singleton x), ncard_singleton, Nat.cast_one]

/-- **Section 12.3.** A hyperfinite set is finite or uncountable: by Section 11.12 this is true
of every internal set. -/
theorem IsHyperfiniteSet.finite_or_not_countable {X : Set αS} (h : IsHyperfiniteSet α X) :
    X.Finite ∨ ¬ X.Countable :=
  h.isInternalSet.finite_or_not_countable

/-- **Section 12.3.** A hyperfinite set is finite if and only if its internal cardinality is a
standard natural number, that is, a limited hypernatural. If $`|A_n| = m` for almost all $`n`
then $`[A_n]` consists of the classes of $`m` sequences that enumerate the sets $`A_n`. -/
theorem IsHyperfiniteSet.finite_iff_limited_internalCard {X : Set αS}
    (h : IsHyperfiniteSet α X) : X.Finite ↔ Limited (internalCard α X) := by
  constructor
  · intro hX
    rw [internalCard_of_finite hX]
    exact (limited_hyperNat_iff (natCast_mem_hyperNat _)).2 ⟨_, rfl⟩
  · intro hl
    obtain ⟨m, hm⟩ := (limited_hyperNat_iff (internalCard_mem_hyperNat X)).1 hl
    obtain ⟨A, rfl, hA⟩ := h
    rw [internalCard_internalSet, natCast_eq_hnat, hnat_eq_hnat_iff] at hm
    have hex : ∀ᶠ n in hyperfilter ℕ, ∃ e : Fin m → α, range e = A n := by
      filter_upwards [hA, hm] with n h1 h2
      have : Finite (A n) := h1
      let e : A n ≃ Fin m := Finite.equivFinOfCardEq ((Nat.card_coe_set_eq (A n)).trans h2)
      refine ⟨fun i => (e.symm i : α), ?_⟩
      ext a
      constructor
      · rintro ⟨i, rfl⟩
        exact (e.symm i).2
      · intro ha
        exact ⟨e ⟨a, ha⟩, by simp only [Equiv.symm_apply_apply]⟩
    obtain ⟨e, he⟩ := exists_seq_of_almostAll_exists hex
    have h2 : (internalSet A : Set αS) = internalSet fun n => range fun i : Fin m => e n i :=
      internalSet_congr (he.mono fun n hn => hn.symm)
    rw [h2, internalSet_range_finite (fun (i : Fin m) n => e n i)]
    exact finite_range _

end Hyperfinite

section Examples

/-- **Section 12.3, fourth example.** For a hypernatural $`N`, the set $`\{1, 2, \dots, N\}`
of hypernaturals is hyperfinite. -/
theorem isHyperfinite_setOf_hyperNat_one_le_le {N : ℝ*} (hN : N ∈ ℕ*) :
    IsHyperfinite {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ N} := by
  obtain ⟨N, rfl⟩ := exists_hnat_eq hN
  rw [setOf_hyperNat_one_le_le_eq_internalSet]
  exact isHyperfiniteSet_internalSet_iff.2
    (Eventually.of_forall fun n => (finite_Icc 1 (N n)).image _)

/-- **Section 12.3, fourth example.** For a hypernatural $`N`, the set $`\{1, 2, \dots, N\}`
has internal cardinality $`N`. -/
theorem hcard_setOf_hyperNat_one_le_le {N : ℝ*} (hN : N ∈ ℕ*) :
    hcard {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ N} = N := by
  obtain ⟨N, rfl⟩ := exists_hnat_eq hN
  rw [setOf_hyperNat_one_le_le_eq_internalSet]
  unfold hcard
  rw [internalCard_internalSet]
  refine hnat_eq_hnat_iff.2 (Eventually.of_forall fun n => ?_)
  rw [ncard_image_of_injective _ Nat.cast_injective, ← Nat.card_coe_set_eq]
  simp

/-- **Section 12.3, fourth example**, from $`0`: for a hypernatural $`N`, the initial segment
$`\{0, 1, \dots, N\}` of the hypernaturals is hyperfinite. -/
theorem isHyperfinite_setOf_hyperNat_le {N : ℝ*} (hN : N ∈ ℕ*) :
    IsHyperfinite {k : ℝ* | k ∈ ℕ* ∧ k ≤ N} := by
  obtain ⟨N, rfl⟩ := exists_hnat_eq hN
  rw [setOf_hyperNat_le_eq_internalSet]
  exact isHyperfiniteSet_internalSet_iff.2
    (Eventually.of_forall fun n => (finite_Iic (N n)).image _)

/-- **Section 12.3, fourth example**, from $`0`: the initial segment $`\{0, 1, \dots, N\}` has
internal cardinality $`N + 1`. -/
theorem hcard_setOf_hyperNat_le {N : ℝ*} (hN : N ∈ ℕ*) :
    hcard {k : ℝ* | k ∈ ℕ* ∧ k ≤ N} = N + 1 := by
  obtain ⟨N, rfl⟩ := exists_hnat_eq hN
  rw [setOf_hyperNat_le_eq_internalSet]
  unfold hcard
  rw [internalCard_internalSet, ← hnat_const_one, hnat_add]
  refine hnat_eq_hnat_iff.2 (Eventually.of_forall fun n => ?_)
  rw [ncard_image_of_injective _ Nat.cast_injective, ← Nat.card_coe_set_eq]
  simp

/-- **Section 12.3, first example.** For an unlimited hypernatural $`N` (for instance
$`N = \omega`, where the set is $`[\{1, \dots, n\}]`), the hyperfinite set
$`\{1, \dots, N\}` contains every positive standard natural number. -/
theorem natCast_mem_setOf_hyperNat_one_le_le {N : ℝ*} (hN : N ∈ ℕ*) (hU : Unlimited N) {m : ℕ}
    (hm : 1 ≤ m) : (m : ℝ*) ∈ {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ N} :=
  ⟨natCast_mem_hyperNat m, by exact_mod_cast hm, (posUnlimited_of_mem_hyperNat hN hU m).le⟩

/-- **Section 12.3, first example.** For an unlimited hypernatural $`N`, the hyperfinite set
$`\{1, \dots, N\}` is uncountable. -/
theorem not_countable_setOf_hyperNat_one_le_le {N : ℝ*} (hN : N ∈ ℕ*) (hU : Unlimited N) :
    ¬ {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ N}.Countable := by
  intro hc
  refine not_countable_setOf_hyperNat_le hN hU ((hc.union (countable_singleton 0)).mono ?_)
  rintro k ⟨hk, hkN⟩
  by_cases h0 : k = 0
  · exact Or.inr h0
  · refine Or.inl ⟨hk, ?_, hkN⟩
    have h1 : (0 : ℝ*) < k := lt_of_le_of_ne (hyperNat_nonneg hk) (Ne.symm h0)
    have h2 := add_one_le_of_lt_of_mem_hyperInt (by simpa using intCast_mem_hyperInt 0)
      (hyperNat_subset_hyperInt hk) h1
    simpa using h2

/-- **Section 12.3, first example.** The hyperfinite set $`[\{1, \dots, n\}] = \{1, \dots,
\omega\}` is uncountable, and its internal cardinality is $`\omega`. -/
theorem hcard_setOf_hyperNat_one_le_le_omega :
    IsHyperfinite {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ ω} ∧
      hcard {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ ω} = ω ∧
      ¬ {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ ω}.Countable :=
  ⟨isHyperfinite_setOf_hyperNat_one_le_le omega_mem_hyperNat,
    hcard_setOf_hyperNat_one_le_le omega_mem_hyperNat,
    not_countable_setOf_hyperNat_one_le_le omega_mem_hyperNat unlimited_omega⟩

/-- **Section 12.3, fifth example.** For a hypernatural $`N`, the grid
$`\{0, \tfrac1N, \tfrac2N, \dots, \tfrac{N-1}N, 1\}` is hyperfinite. -/
theorem isHyperfinite_setOf_div_hyperNat {N : ℝ*} (hN : N ∈ ℕ*) :
    IsHyperfinite {x : ℝ* | ∃ k ∈ ℕ*, k ≤ N ∧ x = k / N} := by
  obtain ⟨N, rfl⟩ := exists_hnat_eq hN
  rw [setOf_div_hyperNat_eq_internalSet]
  exact isHyperfiniteSet_internalSet_iff.2
    (Eventually.of_forall fun n => (finite_Iic (N n)).image _)

/-- **Section 12.3, fifth example.** For a hypernatural $`N`, the grid
$`\{0, \tfrac1N, \tfrac2N, \dots, \tfrac{N-1}N, 1\}` has internal cardinality $`N + 1`. (For
$`N = 0` the grid is $`\{0\}`, by the convention on division by zero, and the formula still
holds.) -/
theorem hcard_setOf_div_hyperNat {N : ℝ*} (hN : N ∈ ℕ*) :
    hcard {x : ℝ* | ∃ k ∈ ℕ*, k ≤ N ∧ x = k / N} = N + 1 := by
  obtain ⟨N, rfl⟩ := exists_hnat_eq hN
  rw [setOf_div_hyperNat_eq_internalSet]
  unfold hcard
  rw [internalCard_internalSet, ← hnat_const_one, hnat_add]
  refine hnat_eq_hnat_iff.2 (Eventually.of_forall fun n => ?_)
  have hinj : InjOn (fun k : ℕ => (k : ℝ) / N n) (Iic (N n)) := by
    intro i hi j hj hij
    rcases Nat.eq_zero_or_pos (N n) with h0 | hpos
    · rw [mem_Iic, h0, Nat.le_zero] at hi hj
      rw [hi, hj]
    · have hN0 : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
      exact Nat.cast_injective ((div_left_inj' hN0).1 hij)
  rw [hinj.ncard_image, ← Nat.card_coe_set_eq]
  simp

/-- **Section 12.3, sixth example.** For hyperreals $`a`, $`b` and a hypernatural $`N`, the
uniform partition $`\{a + k\,\tfrac{b - a}{N} : k \in {}^*\mathbb N,\ k \le N\}` is the
internal set defined by the finite partitions
$`\{a_n + k\,\tfrac{b_n - a_n}{N_n} : k \le N_n\}`. -/
theorem setOf_uniform_partition_eq_internalSet (a b : ℕ → ℝ) (N : ℕ → ℕ) :
    {x : ℝ* | ∃ k ∈ ℕ*, k ≤ hnat N ∧
        x = Hyperreal.ofSeq a + k * ((Hyperreal.ofSeq b - Hyperreal.ofSeq a) / hnat N)} =
      internalSet fun n =>
        ((fun k : ℕ => a n + (k : ℝ) * ((b n - a n) / N n)) '' Iic (N n) : Set ℝ) := by
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [hyperreal_ofSeq_mem_internalSet]
  constructor
  · rintro ⟨k, hk, hkN, hx⟩
    obtain ⟨κ, rfl⟩ := exists_hnat_eq hk
    have hx' : Hyperreal.ofSeq r =
        Hyperreal.ofSeq fun n => a n + (κ n : ℝ) * ((b n - a n) / N n) := hx
    exact ((hnat_le_hnat_iff.1 hkN).and (ofSeq_eq_ofSeq_iff.1 hx')).mono fun n hn =>
      ⟨κ n, hn.1, hn.2.symm⟩
  · intro h
    obtain ⟨κ, hκ⟩ := exists_seq_of_almostAll_exists h
    refine ⟨hnat κ, hnat_mem_hyperNat κ, hnat_le_hnat_iff.2 (hκ.mono fun n hn => hn.1), ?_⟩
    change Hyperreal.ofSeq r = Hyperreal.ofSeq fun n => a n + (κ n : ℝ) * ((b n - a n) / N n)
    exact ofSeq_eq_ofSeq_iff.2 (hκ.mono fun n hn => hn.2.symm)

/-- **Section 12.3, sixth example.** The index $`k` of a point of the uniform partition may
equivalently be taken to be a hyperinteger with $`0 \le k \le N`, as in the book. -/
theorem setOf_uniform_partition_hyperInt (a b N : ℝ*) :
    {x : ℝ* | ∃ k ∈ ℤ*, 0 ≤ k ∧ k ≤ N ∧ x = a + k * ((b - a) / N)} =
      {x : ℝ* | ∃ k ∈ ℕ*, k ≤ N ∧ x = a + k * ((b - a) / N)} := by
  ext x
  constructor
  · rintro ⟨k, hk, h0, hkN, hx⟩
    exact ⟨k, mem_hyperNat_iff_hyperInt_nonneg.2 ⟨hk, h0⟩, hkN, hx⟩
  · rintro ⟨k, hk, hkN, hx⟩
    exact ⟨k, (mem_hyperNat_iff_hyperInt_nonneg.1 hk).1, (mem_hyperNat_iff_hyperInt_nonneg.1 hk).2,
      hkN, hx⟩

/-- **Section 12.3, sixth example.** For any hyperreals $`a`, $`b` and any hypernatural $`N`,
the uniform partition $`\{a + k\,\tfrac{b - a}{N} : k \in {}^*\mathbb Z,\ 0 \le k \le N\}` is
hyperfinite. -/
theorem isHyperfinite_setOf_uniform_partition (a b : ℝ*) {N : ℝ*} (hN : N ∈ ℕ*) :
    IsHyperfinite {x : ℝ* | ∃ k ∈ ℤ*, 0 ≤ k ∧ k ≤ N ∧ x = a + k * ((b - a) / N)} := by
  obtain ⟨N, rfl⟩ := exists_hnat_eq hN
  obtain ⟨a, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨b, rfl⟩ := hyperreal_exists_rep b
  rw [setOf_uniform_partition_hyperInt, setOf_uniform_partition_eq_internalSet]
  exact isHyperfiniteSet_internalSet_iff.2
    (Eventually.of_forall fun n => (finite_Iic (N n)).image _)

/-- **Section 12.3, sixth example.** For hyperreals $`a \ne b` and a hypernatural $`N`, the
uniform partition $`\{a + k\,\tfrac{b - a}{N} : k \in {}^*\mathbb Z,\ 0 \le k \le N\}` has
internal cardinality $`N + 1`. The book states this for all $`a` and $`b`; when $`a = b` and
$`N \ne 0` the partition is the single point $`a` and the count is wrong, so the hypothesis
$`a \ne b` is added. -/
theorem hcard_setOf_uniform_partition {a b : ℝ*} (hab : a ≠ b) {N : ℝ*} (hN : N ∈ ℕ*) :
    hcard {x : ℝ* | ∃ k ∈ ℤ*, 0 ≤ k ∧ k ≤ N ∧ x = a + k * ((b - a) / N)} = N + 1 := by
  obtain ⟨N, rfl⟩ := exists_hnat_eq hN
  obtain ⟨a, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨b, rfl⟩ := hyperreal_exists_rep b
  rw [setOf_uniform_partition_hyperInt, setOf_uniform_partition_eq_internalSet]
  unfold hcard
  rw [internalCard_internalSet, ← hnat_const_one, hnat_add]
  refine hnat_eq_hnat_iff.2 ((ofSeq_ne_ofSeq_iff.1 hab).mono fun n hn => ?_)
  have hinj : InjOn (fun k : ℕ => a n + (k : ℝ) * ((b n - a n) / N n)) (Iic (N n)) := by
    intro i hi j hj hij
    rcases Nat.eq_zero_or_pos (N n) with h0 | hpos
    · rw [mem_Iic, h0, Nat.le_zero] at hi hj
      rw [hi, hj]
    · have hN0 : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
      have hd : (b n - a n) / N n ≠ 0 := div_ne_zero (sub_ne_zero.2 (Ne.symm hn)) hN0
      exact Nat.cast_injective (mul_right_cancel₀ hd (add_left_cancel hij))
  rw [hinj.ncard_image, ← Nat.card_coe_set_eq]
  simp

end Examples

section Countable

variable {α αS : Type u} [StarType α αS]

/-- **Section 12.3, second example.** For a sequence $`(x_n)`, the internal set $`[A_n]` with
$`A_n = \{x_0, \dots, x_{n-1}\}` is hyperfinite. -/
theorem isHyperfiniteSet_internalSet_image_Iio (x : ℕ → α) :
    IsHyperfiniteSet α (internalSet (fun n => x '' Iio n) : Set αS) :=
  isHyperfiniteSet_internalSet_iff.2 (Eventually.of_forall fun n => (finite_Iio n).image x)

/-- **Section 12.3, second example.** The hyperfinite set $`[\{x_0, \dots, x_{n-1}\}]`
contains every term $`x_m` of the sequence, because $`x_m \in A_n` for all $`n > m`. -/
theorem image_of_range_subset_internalSet_image_Iio (x : ℕ → α) :
    (of '' range x : Set αS) ⊆ internalSet fun n => x '' Iio n := by
  rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
  rw [of_eq_ofSeq, ofSeq_mem_internalSet]
  exact eventually_hyperfilter_of_forall_ge (m + 1) fun n hn => ⟨m, hn, rfl⟩

/-- **Section 12.3, second example.** The hyperfinite set $`[\{x_0, \dots, x_{n-1}\}]` is
included in the enlargement of the set of terms of the sequence. -/
theorem internalSet_image_Iio_subset_starSet (x : ℕ → α) :
    (internalSet (fun n => x '' Iio n) : Set αS) ⊆ ⋆(range x) :=
  internalSet_subset_starSet_iff.2 (Eventually.of_forall fun _ => image_subset_range _ _)

/-- **Section 12.3, second example.** If the sequence $`(x_n)` has no repetitions, the
hyperfinite set $`[\{x_0, \dots, x_{n-1}\}]` has internal cardinality $`\omega`.

The book asserts internal size $`\omega` for the approximating set without assuming that the
enumeration has no repetitions. That is a correction: the claim needs the extra hypothesis and
fails without it, for instance when $`B` is finite, where the approximating set is $`B` itself
and has finite size. -/
theorem internalCard_internalSet_image_Iio {x : ℕ → α} (hx : Function.Injective x) :
    internalCard α (internalSet (fun n => x '' Iio n) : Set αS) = ω := by
  rw [internalCard_internalSet]
  change _ = hnat fun n => n
  refine hnat_eq_hnat_iff.2 (Eventually.of_forall fun n => ?_)
  rw [ncard_image_of_injective _ hx, ← Nat.card_coe_set_eq]
  simp

/-- **Section 12.3, second example.** Every countable set $`B` has a hyperfinite
approximation: a hyperfinite set $`A` with $`B \subseteq A \subseteq {}^*B`. No claim is
made about the internal size of $`A`; the book's value $`\omega` holds only for an enumeration
without repetitions, see {name}`Goldblatt.internalCard_internalSet_image_Iio`. -/
theorem exists_isHyperfiniteSet_between {B : Set α} (hB : B.Countable) :
    ∃ A : Set αS, IsHyperfiniteSet α A ∧ of '' B ⊆ A ∧ A ⊆ ⋆B := by
  rcases B.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, isHyperfiniteSet_empty, by rw [image_empty], empty_subset _⟩
  · obtain ⟨x, rfl⟩ := hB.exists_eq_range hne
    exact ⟨_, isHyperfiniteSet_internalSet_image_Iio x,
      image_of_range_subset_internalSet_image_Iio x, internalSet_image_Iio_subset_starSet x⟩

/-- **Section 12.3, second example**, for sets of reals: every countable set $`B` of reals has
a hyperfinite approximation $`A` with $`B \subseteq A \subseteq {}^*B`. -/
theorem exists_isHyperfinite_between {B : Set ℝ} (hB : B.Countable) :
    ∃ A : Set ℝ*, IsHyperfinite A ∧ ((↑) : ℝ → ℝ*) '' B ⊆ A ∧ A ⊆ ⋆B :=
  exists_isHyperfiniteSet_between hB

end Countable

/-!
## 12.4 Exercises on Hyperfiniteness

Hyperfinite sets behave like finite sets as long as only internal objects are involved. A
nonempty hyperfinite set of hyperreals has a greatest and a least member; unions and
intersections of hyperfinite sets are hyperfinite, and the internal cardinalities satisfy the
inclusion-exclusion formula; an internal subset of a hyperfinite set is hyperfinite, and its
internal cardinality is no larger. In each case the finite statement holds for almost all terms
of the defining sequences.
-/

section HyperfiniteExercises

variable {α αS : Type u} [StarType α αS]

/-- **Exercise 12.4(1).** A nonempty hyperfinite set of hyperreals has a greatest element: the
class of the sequence of the greatest elements of the finite sets $`A_n`. The exercise does not
say so, but the set has to be nonempty. -/
theorem IsHyperfinite.exists_isGreatest {X : Set ℝ*} (h : IsHyperfinite X) (hne : X.Nonempty) :
    ∃ m, IsGreatest X m := by
  obtain ⟨A, rfl, hA⟩ := h
  have h1 := internalSet_nonempty_iff.1 hne
  have h2 : ∀ᶠ n in hyperfilter ℕ, ∃ m, IsGreatest (A n) m := by
    filter_upwards [hA, h1] with n hf hn
    obtain ⟨m, hm, hmax⟩ := Set.exists_max_image (A n) id hf hn
    exact ⟨m, hm, fun b hb => hmax b hb⟩
  obtain ⟨m, hm⟩ := exists_seq_of_almostAll_exists h2
  exact ⟨Hyperreal.ofSeq m, hyperreal_ofSeq_mem_internalSet.2 (hm.mono fun n hn => hn.1),
    ofSeq_mem_upperBounds_internalSet_iff.2 (hm.mono fun n hn => hn.2)⟩

/-- **Exercise 12.4(1).** A nonempty hyperfinite set of hyperreals has a least element. -/
theorem IsHyperfinite.exists_isLeast {X : Set ℝ*} (h : IsHyperfinite X) (hne : X.Nonempty) :
    ∃ m, IsLeast X m := by
  obtain ⟨A, rfl, hA⟩ := h
  have h1 := internalSet_nonempty_iff.1 hne
  have h2 : ∀ᶠ n in hyperfilter ℕ, ∃ m, IsLeast (A n) m := by
    filter_upwards [hA, h1] with n hf hn
    obtain ⟨m, hm, hmin⟩ := Set.exists_min_image (A n) id hf hn
    exact ⟨m, hm, fun b hb => hmin b hb⟩
  obtain ⟨m, hm⟩ := exists_seq_of_almostAll_exists h2
  exact ⟨Hyperreal.ofSeq m, isLeast_internalSet_ofSeq hm⟩

/-- **Exercise 12.4(2).** The union of two hyperfinite sets is hyperfinite. -/
theorem IsHyperfiniteSet.union {X Y : Set αS} (hX : IsHyperfiniteSet α X)
    (hY : IsHyperfiniteSet α Y) : IsHyperfiniteSet α (X ∪ Y) := by
  obtain ⟨A, rfl, hA⟩ := hX
  obtain ⟨B, rfl, hB⟩ := hY
  rw [internalSet_union]
  exact isHyperfiniteSet_internalSet_iff.2 (by
    filter_upwards [hA, hB] with n h1 h2 using h1.union h2)

/-- **Exercise 12.4(2) and (3).** The intersection of a hyperfinite set with an internal set is
hyperfinite. -/
theorem IsHyperfiniteSet.inter_of_isInternalSet {X Y : Set αS} (hX : IsHyperfiniteSet α X)
    (hY : IsInternalSet α Y) : IsHyperfiniteSet α (X ∩ Y) := by
  obtain ⟨A, rfl, hA⟩ := hX
  obtain ⟨B, rfl⟩ := hY
  rw [internalSet_inter]
  exact isHyperfiniteSet_internalSet_iff.2 (hA.mono fun n h1 => h1.subset inter_subset_left)

/-- **Exercise 12.4(2).** The intersection of two hyperfinite sets is hyperfinite. -/
theorem IsHyperfiniteSet.inter {X Y : Set αS} (hX : IsHyperfiniteSet α X)
    (hY : IsHyperfiniteSet α Y) : IsHyperfiniteSet α (X ∩ Y) :=
  hX.inter_of_isInternalSet hY.isInternalSet

/-- **Exercise 12.4(2).** For hyperfinite sets $`X` and $`Y`,
$`|X \cup Y| + |X \cap Y| = |X| + |Y|`. -/
theorem internalCard_union_add_internalCard_inter {X Y : Set αS} (hX : IsHyperfiniteSet α X)
    (hY : IsHyperfiniteSet α Y) :
    internalCard α (X ∪ Y) + internalCard α (X ∩ Y) = internalCard α X + internalCard α Y := by
  obtain ⟨A, rfl, hA⟩ := hX
  obtain ⟨B, rfl, hB⟩ := hY
  rw [internalSet_union, internalSet_inter]
  simp only [internalCard_internalSet, hnat_add]
  refine hnat_eq_hnat_iff.2 ?_
  filter_upwards [hA, hB] with n h1 h2 using ncard_union_add_ncard_inter (A n) (B n) h1 h2

/-- **Exercise 12.4(2).** For hyperfinite sets $`X` and $`Y`,
$`|X \cup Y| = |X| + |Y| - |X \cap Y|`. -/
theorem internalCard_union {X Y : Set αS} (hX : IsHyperfiniteSet α X)
    (hY : IsHyperfiniteSet α Y) :
    internalCard α (X ∪ Y) = internalCard α X + internalCard α Y - internalCard α (X ∩ Y) :=
  eq_sub_of_add_eq (internalCard_union_add_internalCard_inter hX hY)

/-- **Exercise 12.4(2)**, additivity: the internal cardinality of the union of two disjoint
hyperfinite sets is the sum of the internal cardinalities. -/
theorem internalCard_union_of_disjoint {X Y : Set αS} (hX : IsHyperfiniteSet α X)
    (hY : IsHyperfiniteSet α Y) (hXY : Disjoint X Y) :
    internalCard α (X ∪ Y) = internalCard α X + internalCard α Y := by
  rw [internalCard_union hX hY, disjoint_iff_inter_eq_empty.1 hXY, internalCard_empty, sub_zero]

/-- **Exercise 12.4(3).** An internal subset of a hyperfinite set is hyperfinite. -/
theorem IsHyperfiniteSet.subset {X Y : Set αS} (hY : IsHyperfiniteSet α Y)
    (hX : IsInternalSet α X) (h : X ⊆ Y) : IsHyperfiniteSet α X := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨B, rfl, hB⟩ := hY
  exact isHyperfiniteSet_internalSet_iff.2 (by
    filter_upwards [internalSet_subset_iff.1 h, hB] with n h1 h2 using h2.subset h1)

/-- **Exercise 12.4(3)**, monotonicity: an internal subset of a hyperfinite set has internal
cardinality at most that of the set. -/
theorem internalCard_le_of_subset {X Y : Set αS} (hY : IsHyperfiniteSet α Y)
    (hX : IsInternalSet α X) (h : X ⊆ Y) : internalCard α X ≤ internalCard α Y := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨B, rfl, hB⟩ := hY
  rw [internalCard_internalSet, internalCard_internalSet]
  refine hnat_le_hnat_iff.2 ?_
  filter_upwards [internalSet_subset_iff.1 h, hB] with n h1 h2 using ncard_le_ncard h1 h2

/-- **Exercise 12.4(3).** The difference of a hyperfinite set and an internal set is
hyperfinite. -/
theorem IsHyperfiniteSet.diff {X Y : Set αS} (hX : IsHyperfiniteSet α X)
    (hY : IsInternalSet α Y) : IsHyperfiniteSet α (X \ Y) :=
  hX.subset (hX.isInternalSet.diff hY) sdiff_subset

/-- **Exercise 12.4(2) and (3).** For an internal subset $`X` of a hyperfinite set $`Y`,
$`|Y \setminus X| = |Y| - |X|`. -/
theorem internalCard_diff {X Y : Set αS} (hY : IsHyperfiniteSet α Y) (hX : IsInternalSet α X)
    (h : X ⊆ Y) : internalCard α (Y \ X) = internalCard α Y - internalCard α X := by
  have h1 := internalCard_union_of_disjoint (hY.diff hX) (hY.subset hX h) disjoint_sdiff_left
  rw [sdiff_union_of_subset h] at h1
  rw [h1, add_sub_cancel_right]

/-- **Exercise 12.4(3)**, strict monotonicity: a proper internal subset of a hyperfinite set
has strictly smaller internal cardinality. -/
theorem internalCard_lt_of_ssubset {X Y : Set αS} (hY : IsHyperfiniteSet α Y)
    (hX : IsInternalSet α X) (h : X ⊂ Y) : internalCard α X < internalCard α Y := by
  have h1 := internalCard_diff hY hX h.subset
  have h2 : internalCard α (Y \ X) ≠ 0 := fun h0 =>
    h.not_subset (sdiff_eq_empty.1 ((hY.diff hX).eq_empty_of_internalCard_eq_zero h0))
  have h3 := lt_of_le_of_ne (internalCard_nonneg (α := α) (Y \ X)) (Ne.symm h2)
  rw [h1] at h3
  exact sub_pos.1 h3

end HyperfiniteExercises

/-!
## 12.5 Counting a Hyperfinite Set

A finite set is one that can be counted: it is in bijection with $`\{1, \dots, n\}` for some
natural number $`n`. Theorem 12.5.1 is the hyperfinite version, with an internal bijection and
a hypernatural $`N`. Its interest is that it describes hyperfinite sets and their sizes in
terms of hypernaturals and internal functions alone, with no mention of the ultrafilter.
-/

section Counting

variable {α αS : Type u} [StarType α αS]

/-- The image of a finite set under a partial function is finite. -/
theorem finite_pfun_image {X : Type*} {Y : Type*} (g : X →. Y) {S : Set X} (hS : S.Finite) :
    (g.image S).Finite := by
  refine (hS.biUnion fun a _ => (Set.Subsingleton.finite (s := {b | b ∈ g a})
    fun b hb b' hb' => Part.mem_unique hb hb')).subset fun y hy => ?_
  obtain ⟨a, ha, hy⟩ := (PFun.mem_image _ _ _).1 hy
  exact mem_biUnion ha hy

/-- An injective partial function preserves the number of elements of a subset of its
domain. -/
theorem PInjective.ncard_image {X : Type*} {Y : Type*} {g : X →. Y} (hg : PInjective g)
    {S : Set X} (hS : S ⊆ g.Dom) : (g.image S).ncard = S.ncard := by
  symm
  refine Set.ncard_congr (fun a ha => (g a).get (hS ha)) ?_ ?_ ?_
  · intro a ha
    exact (PFun.mem_image _ _ _).2 ⟨a, ha, Part.get_mem _⟩
  · intro a b ha hb hab
    exact hg (Part.get_mem (hS ha)) (hab ▸ Part.get_mem (hS hb))
  · intro b hb
    obtain ⟨a, ha, hab⟩ := (PFun.mem_image _ _ _).1 hb
    exact ⟨a, ha, Part.get_eq_of_mem hab _⟩

/-- The range of a partial function is the image of its domain. -/
theorem pfun_ran_eq_image_dom {X : Type*} {Y : Type*} (g : X →. Y) : g.ran = g.image g.Dom := by
  ext y
  rw [PFun.mem_image]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (PFun.mem_dom _ _).2 ⟨y, ha⟩, ha⟩
  · rintro ⟨a, -, ha⟩
    exact ⟨a, ha⟩

/-- **Section 12.5, the standard fact.** A finite set with $`m` elements is the range of an
injective function defined on $`\{1, \dots, m\}`. -/
theorem exists_pfun_enumeration {Y : Type*} {S : Set Y} (hS : S.Finite) :
    ∃ g : ℝ →. Y, g.Dom = ((↑) : ℕ → ℝ) '' Icc 1 S.ncard ∧ PInjective g ∧ g.ran = S := by
  have hfin : Finite S := hS
  let e : S ≃ Fin S.ncard := Finite.equivFinOfCardEq (Nat.card_coe_set_eq S)
  let g : ℝ →. Y := fun x =>
    ⟨∃ k : Fin S.ncard, ((k : ℕ) : ℝ) + 1 = x, fun h => (e.symm h.choose : Y)⟩
  have hmem : ∀ x y, y ∈ g x ↔ ∃ k : Fin S.ncard, ((k : ℕ) : ℝ) + 1 = x ∧ (e.symm k : Y) = y := by
    intro x y
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h.choose, h.choose_spec, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have h : ∃ k : Fin S.ncard, ((k : ℕ) : ℝ) + 1 = x := ⟨k, hk⟩
      refine ⟨h, ?_⟩
      have hk' : h.choose = k := by
        have h1 := h.choose_spec
        exact Fin.ext (Nat.cast_injective (add_right_cancel (h1.trans hk.symm)))
      change (e.symm h.choose : Y) = _
      rw [hk']
  refine ⟨g, ?_, ?_, ?_⟩
  · ext x
    rw [PFun.mem_dom]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨k, hk, -⟩ := (hmem x y).1 hy
      exact ⟨k + 1, ⟨Nat.le_add_left 1 k, k.2⟩, by rw [← hk]; push_cast; ring⟩
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      refine ⟨_, (hmem _ _).2 ⟨⟨j - 1, by omega⟩, ?_, rfl⟩⟩
      change ((j - 1 : ℕ) : ℝ) + 1 = j
      rw [Nat.cast_sub h1]
      push_cast
      ring
  · intro x x' y hy hy'
    obtain ⟨k, hk, hky⟩ := (hmem x y).1 hy
    obtain ⟨k', hk', hky'⟩ := (hmem x' y).1 hy'
    have : k = k' := e.symm.injective (Subtype.ext (hky.trans hky'.symm))
    rw [← hk, ← hk', this]
  · ext y
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨k, -, rfl⟩ := (hmem x y).1 hx
      exact (e.symm k).2
    · intro hy
      exact ⟨_, (hmem _ _).2 ⟨e ⟨y, hy⟩, rfl, by rw [Equiv.symm_apply_apply]⟩⟩

/-- **Theorem 12.5.1.** A set $`A` is hyperfinite with internal cardinality $`N` if and only if
there is an internal bijection from $`\{1, \dots, N\}` onto $`A`: an injective internal
function with domain $`\{1, \dots, N\}` and range $`A`.

From left to right, enumerate almost every $`A_n` by $`\{1, \dots, N_n\}` and take the internal
function of the enumerations; it is injective by Exercise 12.2(4) and has range $`A` by
Exercise 12.2(1). From right to left, almost every $`f_n` is an injection defined on
$`\{1, \dots, N_n\}`, and its range, which is almost always $`A_n`, has $`N_n` elements. The
book assumes that $`A` is internal; this follows from either side, so the hypothesis is
dropped. -/
theorem isHyperfiniteSet_and_internalCard_eq_iff {X : Set αS} {N : ℝ*} (hN : N ∈ ℕ*) :
    IsHyperfiniteSet α X ∧ internalCard α X = N ↔
      ∃ f : ℝ* →. αS, IsInternalPFun ℝ α f ∧ f.Dom = {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ N} ∧
        PInjective f ∧ f.ran = X := by
  obtain ⟨N, rfl⟩ := exists_hnat_eq hN
  constructor
  · rintro ⟨⟨A, rfl, hA⟩, hcard⟩
    rw [internalCard_internalSet, hnat_eq_hnat_iff] at hcard
    have hex : ∀ᶠ n in hyperfilter ℕ, ∃ g : ℝ →. α,
        g.Dom = ((↑) : ℕ → ℝ) '' Icc 1 (N n) ∧ PInjective g ∧ g.ran = A n := by
      filter_upwards [hA, hcard] with n h1 h2
      rw [← h2]
      exact exists_pfun_enumeration h1
    obtain ⟨F, hF⟩ := exists_seq_of_almostAll_exists hex
    refine ⟨internalPFun F, isInternalPFun_internalPFun F, ?_, ?_, ?_⟩
    · rw [dom_internalPFun, setOf_hyperNat_one_le_le_eq_internalSet]
      exact internalSet_congr (hF.mono fun n hn => hn.1)
    · exact pinjective_internalPFun_iff.2 (hF.mono fun n hn => hn.2.1)
    · rw [ran_internalPFun]
      exact internalSet_congr (hF.mono fun n hn => hn.2.2)
  · rintro ⟨f, ⟨F, rfl⟩, hdom, hinj, rfl⟩
    rw [dom_internalPFun, setOf_hyperNat_one_le_le_eq_internalSet, internalSet_eq_iff] at hdom
    have hinj' := pinjective_internalPFun_iff.1 hinj
    rw [ran_internalPFun]
    have key : ∀ᶠ n in hyperfilter ℕ, (F n).ran.Finite ∧ (F n).ran.ncard = N n := by
      filter_upwards [hdom, hinj'] with n h1 h2
      rw [pfun_ran_eq_image_dom, h2.ncard_image subset_rfl, h1]
      refine ⟨finite_pfun_image _ ((finite_Icc 1 (N n)).image _), ?_⟩
      rw [ncard_image_of_injective _ Nat.cast_injective, ← Nat.card_coe_set_eq]
      simp
    refine ⟨isHyperfiniteSet_internalSet_iff.2 (key.mono fun n hn => hn.1), ?_⟩
    rw [internalCard_internalSet]
    exact hnat_eq_hnat_iff.2 (key.mono fun n hn => hn.2)

/-- **Theorem 12.5.1**, existential form: a set is hyperfinite if and only if it is the range
of an injective internal function defined on $`\{1, \dots, N\}` for some hypernatural
$`N`. -/
theorem isHyperfiniteSet_iff_exists_internal_bijection {X : Set αS} :
    IsHyperfiniteSet α X ↔
      ∃ N ∈ ℕ*, ∃ f : ℝ* →. αS, IsInternalPFun ℝ α f ∧
        f.Dom = {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ N} ∧ PInjective f ∧ f.ran = X := by
  constructor
  · intro h
    exact ⟨_, internalCard_mem_hyperNat X,
      (isHyperfiniteSet_and_internalCard_eq_iff (internalCard_mem_hyperNat X)).1 ⟨h, rfl⟩⟩
  · rintro ⟨N, hN, h⟩
    exact ((isHyperfiniteSet_and_internalCard_eq_iff hN).2 h).1

end Counting

/-!
## 12.6 Hyperfinite Pigeonhole Principle

A set is finite exactly when every injection of the set into itself is onto. Among internal
sets, and with internal injections, the same property characterizes the hyperfinite sets. As an
application, a function that shifts the standard natural numbers but fixes the nonstandard
hypernaturals cannot be internal.
-/

section Pigeonhole

variable {α αS : Type u} [StarType α αS]

/-- **Section 12.6, the standard pigeonhole principle.** An injective partial function that
maps a finite subset of its domain into itself maps it onto itself. -/
theorem PInjective.image_eq_of_finite {X : Type*} {g : X →. X} (hg : PInjective g) {S : Set X}
    (hS : S.Finite) (hdom : S ⊆ g.Dom) (himg : g.image S ⊆ S) : g.image S = S :=
  eq_of_subset_of_ncard_le himg (hg.ncard_image hdom).ge hS

/-- **Section 12.6, the standard fact.** An infinite set admits an injection into itself that
is not onto. -/
theorem exists_pfun_injective_not_surjective {Y : Type*} {S : Set Y} (hS : S.Infinite) :
    ∃ g : Y →. Y, g.Dom = S ∧ PInjective g ∧ g.image S ⊆ S ∧ ∃ a ∈ S, a ∉ g.image S := by
  classical
  have hinf : Infinite S := infinite_coe_iff.2 hS
  let e := Infinite.natEmbedding S
  let h : S → S := fun x => if x ∈ range e then e (Function.invFun e x + 1) else x
  have he : ∀ k, h (e k) = e (k + 1) := fun k => by
    simp only [h, mem_range_self, ite_true, Function.leftInverse_invFun e.injective k]
  have hne : ∀ x, x ∉ range e → h x = x := fun x hx => by simp only [h, hx, ite_false]
  have hinj : Function.Injective h := by
    intro x y hxy
    by_cases hx : x ∈ range e <;> by_cases hy : y ∈ range e
    · obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      rw [he, he] at hxy
      rw [Nat.succ_injective (e.injective hxy)]
    · obtain ⟨i, rfl⟩ := hx
      rw [he, hne y hy] at hxy
      exact absurd ⟨i + 1, hxy⟩ hy
    · obtain ⟨j, rfl⟩ := hy
      rw [hne x hx, he] at hxy
      exact absurd ⟨j + 1, hxy.symm⟩ hx
    · rwa [hne x hx, hne y hy] at hxy
  have h0 : ∀ x, h x ≠ e 0 := by
    intro x hx
    by_cases hxr : x ∈ range e
    · obtain ⟨i, rfl⟩ := hxr
      rw [he] at hx
      exact Nat.succ_ne_zero i (e.injective hx)
    · rw [hne x hxr] at hx
      exact hxr ⟨0, hx.symm⟩
  refine ⟨pfunOn S (fun x => (h x : Y)), dom_pfunOn _ _, ?_, ?_, e 0, (e 0).2, ?_⟩
  · intro a a' b hb hb'
    obtain ⟨ha, rfl⟩ := mem_pfunOn.1 hb
    obtain ⟨ha', hb'⟩ := mem_pfunOn.1 hb'
    exact congrArg Subtype.val (hinj (Subtype.ext hb'.symm))
  · intro b hb
    obtain ⟨a, -, hab⟩ := (PFun.mem_image _ _ _).1 hb
    obtain ⟨ha, rfl⟩ := mem_pfunOn.1 hab
    exact (h _).2
  · intro hb
    obtain ⟨a, -, hab⟩ := (PFun.mem_image _ _ _).1 hb
    obtain ⟨ha, hh⟩ := mem_pfunOn.1 hab
    exact h0 _ (Subtype.ext hh)

/-- **Theorem 12.6.1**, the forward direction: an injective internal function that maps a
hyperfinite subset of its domain into itself maps it onto itself. Almost all terms of the
defining sequences satisfy the hypotheses of the standard pigeonhole principle. -/
theorem IsHyperfiniteSet.image_eq_of_pinjective {X : Set αS} (hX : IsHyperfiniteSet α X)
    {f : αS →. αS} (hf : IsInternalPFun α α f) (hinj : PInjective f) (hdom : X ⊆ f.Dom)
    (himg : f.image X ⊆ X) : f.image X = X := by
  obtain ⟨A, rfl, hA⟩ := hX
  obtain ⟨F, rfl⟩ := hf
  rw [dom_internalPFun, internalSet_subset_iff] at hdom
  rw [image_internalPFun, internalSet_subset_iff] at himg
  rw [image_internalPFun]
  refine internalSet_congr ?_
  filter_upwards [hA, hdom, himg, pinjective_internalPFun_iff.1 hinj] with n h1 h2 h3 h4
    using h4.image_eq_of_finite h1 h2 h3

/-- **Theorem 12.6.1** (hyperfinite pigeonhole principle). An internal set $`A` is hyperfinite
if and only if every injective internal function whose domain includes $`A` and which maps
$`A` into $`A` maps $`A` onto $`A`.

For the converse, if $`A = [A_n]` is not hyperfinite then almost every $`A_n` is infinite and
so has an injection $`f_n` into itself that misses a point $`r_n`; the internal function
$`[f_n]` is then an injection of $`A` into itself that misses $`[r_n]`. -/
theorem isHyperfiniteSet_iff_pigeonhole {X : Set αS} (hX : IsInternalSet α X) :
    IsHyperfiniteSet α X ↔
      ∀ f : αS →. αS, IsInternalPFun α α f → PInjective f → X ⊆ f.Dom → f.image X ⊆ X →
        f.image X = X := by
  constructor
  · exact fun h f hf hinj hdom himg => h.image_eq_of_pinjective hf hinj hdom himg
  · intro h
    by_contra hnot
    obtain ⟨A, rfl⟩ := hX
    have hinf := not_isHyperfiniteSet_internalSet_iff.1 hnot
    have hex : ∀ᶠ n in hyperfilter ℕ, ∃ p : (α →. α) × α, p.1.Dom = A n ∧ PInjective p.1 ∧
        p.1.image (A n) ⊆ A n ∧ p.2 ∈ A n ∧ p.2 ∉ p.1.image (A n) := by
      refine hinf.mono fun n hn => ?_
      obtain ⟨g, h1, h2, h3, a, h4, h5⟩ := exists_pfun_injective_not_surjective hn
      exact ⟨(g, a), h1, h2, h3, h4, h5⟩
    obtain ⟨p, hp⟩ := exists_seq_of_almostAll_exists hex
    have himg : (internalPFun (fun n => (p n).1) : αS →. αS).image (internalSet A) =
        internalSet fun n => (p n).1.image (A n) := image_internalPFun _ _
    have key := h (internalPFun fun n => (p n).1) (isInternalPFun_internalPFun _)
      (pinjective_internalPFun_iff.2 (hp.mono fun n hn => hn.2.1))
      (by
        rw [dom_internalPFun]
        exact internalSet_subset_iff.2 (hp.mono fun n hn => hn.1.ge))
      (by
        rw [himg]
        exact internalSet_subset_iff.2 (hp.mono fun n hn => hn.2.2.1))
    have hmem : (ofSeq (fun n => (p n).2) : αS) ∈ internalSet A :=
      ofSeq_mem_internalSet.2 (hp.mono fun n hn => hn.2.2.2.1)
    rw [← key, himg, ofSeq_mem_internalSet] at hmem
    exact almostAll_not.1 (hp.mono fun n hn => hn.2.2.2.2) hmem

open Classical in
/-- **Section 12.6, example.** The function on the hypernaturals that doubles the standard
natural numbers and fixes the nonstandard hypernaturals. -/
noncomputable def doubleStandard : ℝ* →. ℝ* :=
  pfunOn ℕ* fun k => if (k : ℝ*) ∈ range ((↑) : ℕ → ℝ*) then 2 * (k : ℝ*) else k

/-- **Section 12.6, example.** The function that doubles the standard natural numbers and
fixes the nonstandard hypernaturals is not internal. The book argues from the fact that it
maps the set of all hypernaturals injectively into, but not onto, itself; that set is not
hyperfinite, so the pigeonhole principle does not apply to it as it stands. The argument is
correct for the hyperfinite set $`\{0, 1, \dots, \omega\}`, which the function also maps
injectively into itself, missing the point $`1`. -/
theorem not_isInternalFun_doubleStandard : ¬ IsInternalFun doubleStandard := by
  classical
  intro hint
  have hval : ∀ {k y : ℝ*}, y ∈ doubleStandard k ↔
      k ∈ ℕ* ∧ ((k ∈ range ((↑) : ℕ → ℝ*) ∧ y = 2 * k) ∨ (k ∉ range ((↑) : ℕ → ℝ*) ∧ y = k)) := by
    intro k y
    rw [doubleStandard, mem_pfunOn]
    constructor
    · rintro ⟨hk, rfl⟩
      refine ⟨hk, ?_⟩
      by_cases hs : k ∈ range ((↑) : ℕ → ℝ*)
      · exact Or.inl ⟨hs, by simp only [hs, ite_true]⟩
      · exact Or.inr ⟨hs, by simp only [hs, ite_false]⟩
    · rintro ⟨hk, ⟨hs, rfl⟩ | ⟨hs, rfl⟩⟩
      · exact ⟨hk, by simp only [hs, ite_true]⟩
      · exact ⟨hk, by simp only [hs, ite_false]⟩
  have hinj : PInjective doubleStandard := by
    intro k k' y hy hy'
    obtain ⟨-, ⟨hs, rfl⟩ | ⟨hs, rfl⟩⟩ := hval.1 hy <;>
      obtain ⟨-, ⟨hs', h⟩ | ⟨hs', h⟩⟩ := hval.1 hy'
    · exact mul_left_cancel₀ two_ne_zero h
    · obtain ⟨m, rfl⟩ := hs
      exact absurd ⟨2 * m, by rw [← h]; push_cast; ring⟩ hs'
    · obtain ⟨m, rfl⟩ := hs'
      exact absurd ⟨2 * m, by rw [h]; push_cast; ring⟩ hs
    · exact h
  have hX := isHyperfinite_setOf_hyperNat_le omega_mem_hyperNat
  have hdom : {k : ℝ* | k ∈ ℕ* ∧ k ≤ ω} ⊆ doubleStandard.Dom := fun k hk => hk.1
  have himg : doubleStandard.image {k : ℝ* | k ∈ ℕ* ∧ k ≤ ω} ⊆ {k : ℝ* | k ∈ ℕ* ∧ k ≤ ω} := by
    intro y hy
    obtain ⟨k, hk, hky⟩ := (PFun.mem_image _ _ _).1 hy
    obtain ⟨-, ⟨⟨m, rfl⟩, rfl⟩ | ⟨-, rfl⟩⟩ := hval.1 hky
    · have h2 : (2 * (m : ℝ*)) = ((2 * m : ℕ) : ℝ*) := by push_cast; ring
      rw [h2]
      exact ⟨natCast_mem_hyperNat _, (posUnlimited_omega ((2 * m : ℕ) : ℝ)).le⟩
    · exact hk
  have key := hX.image_eq_of_pinjective hint hinj hdom himg
  have h1 : (1 : ℝ*) ∈ {k : ℝ* | k ∈ ℕ* ∧ k ≤ ω} :=
    ⟨by simpa using natCast_mem_hyperNat 1, (posUnlimited_omega 1).le⟩
  rw [← key] at h1
  obtain ⟨k, -, hk⟩ := (PFun.mem_image _ _ _).1 h1
  obtain ⟨-, ⟨⟨m, rfl⟩, h⟩ | ⟨hs, h⟩⟩ := hval.1 hk
  · have h3 : ((1 : ℕ) : ℝ*) = ((2 * m : ℕ) : ℝ*) := by rw [Nat.cast_one, h]; push_cast; ring
    have := Nat.cast_injective h3
    omega
  · exact hs ⟨1, by rw [← h, Nat.cast_one]⟩

end Pigeonhole

end Goldblatt
