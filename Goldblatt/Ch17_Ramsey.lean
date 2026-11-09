import Mathlib
import Goldblatt.Ch02_LargeSets
import Goldblatt.Ch03_Ultrapower
import Goldblatt.Ch05_GreatAndSmall

/-!
# 17. Ramsey Theory

Nonstandard methods are not confined to analysis. This chapter applies them to the
combinatorics of infinite sets. The subject is Ramsey's theorem: however the $`k`-element
subsets of an infinite set are painted with finitely many colours, some infinite subset has all
of its $`k`-element subsets painted alike.

The proofs all have the same shape. A nonstandard element $`\pi` of the enlargement of an
infinite set is fixed once and for all, and a sequence of standard elements is then built one
term at a time, each new term being chosen to _behave like_ $`\pi` with respect to the finitely
many terms chosen before it. Such a term exists because $`\pi` itself has the required
behaviour, and a statement with finitely many standard parameters that is true of some element
of an enlargement is true of some standard element.

Everything is carried out in the concrete ultrapower of Chapter 3 with index set the natural
numbers. There a nonstandard element is the class of a sequence $`(p_n)` that is not almost
everywhere constant, a statement about it holds exactly when the corresponding statement about
$`p_n` holds for almost all $`n`, and "existential transfer" is the remark that a property
holding for almost all $`n` holds for at least one $`n`. The book works in an enlargement of a
universe; the ultrapower is one, and the arguments use nothing beyond the existence of a
nonstandard member of the enlargement of an infinite set (Theorem 3.9.1).

Colourings are formalized as functions from finite sets to a type of colours, which is the same
thing as a partition into colour classes; the book's formulation by a finite cover is derived as
a corollary. Mathlib (at the version used here) has no Ramsey theorem for $`k`-element subsets,
so nothing in this chapter is imported from it; the nearest relative there is
{name}`exists_increasing_or_nonincreasing_subseq`, a statement about pairs in the spirit of
Theorem 17.1.1.

## 17.1 Colourings and Monochromatic Sets

The starting point is the pigeonhole principle for infinite sets: if an infinite set is covered
by finitely many sets, one of them meets it in an infinite set. Ramsey's theorem is the same
statement one level up, with the points of the set replaced by its $`k`-element subsets, and the
conclusion "some colour is used infinitely often" replaced by the much stronger "some infinite
set sees only one colour". This section sets up the vocabulary.

Two items of Section 17.1 are found further down the page, because they need the proof given
in Section 17.3. The statement of Ramsey's theorem is {lit}`Goldblatt.infinite_ramsey` (with
the variants {lit}`Goldblatt.infinite_ramsey'` and {lit}`Goldblatt.infinite_ramsey_cover`), at
the end of Section 17.3. Its first application, Theorem 17.1.1 on infinite partially ordered
sets, is {lit}`Goldblatt.exists_strictMono_or_strictAnti_or_antichain`, in the section
"17.1 revisited" that follows Section 17.3; the nonstandard proof of the same theorem, from
Section 17.2, is {lit}`Goldblatt.exists_strictMono_or_strictAnti_or_antichain_nonstandard`.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal

universe u

section Colourings

variable {α : Type u} {κ : Type*} {ι : Type*}

/-- **Section 17.1, definition.** The set $`[A]^k` of all $`k`-element subsets of $`A`. Its
members are finite sets, so they are represented by Mathlib's finite sets. -/
def kSubsets (A : Set α) (k : ℕ) : Set (Finset α) := {t | (t : Set α) ⊆ A ∧ t.card = k}

/-- **Section 17.1.** Membership of $`[A]^k`, unfolded. -/
@[simp]
theorem mem_kSubsets {A : Set α} {k : ℕ} {t : Finset α} :
    t ∈ kSubsets A k ↔ (t : Set α) ⊆ A ∧ t.card = k :=
  Iff.rfl

/-- **Section 17.1.** If $`B \subseteq A` then $`[B]^k \subseteq [A]^k`. -/
theorem kSubsets_mono {A B : Set α} (h : B ⊆ A) (k : ℕ) : kSubsets B k ⊆ kSubsets A k :=
  fun _ ht => ⟨ht.1.trans h, ht.2⟩

/-- **Section 17.1**, relation to Mathlib. For a finite set $`s`, the set $`[s]^k` is Mathlib's
{name}`Finset.powersetCard`. -/
theorem kSubsets_coe (s : Finset α) (k : ℕ) :
    kSubsets (s : Set α) k = ↑(s.powersetCard k) := by
  ext t
  simp [Finset.mem_powersetCard]

/-- **Section 17.1.** The only $`0`-element subset is the empty set. -/
theorem kSubsets_zero (A : Set α) : kSubsets A 0 = {∅} := by
  ext t
  constructor
  · rintro ⟨-, h⟩
    exact Finset.card_eq_zero.1 h
  · rintro rfl
    exact ⟨by simp, rfl⟩

/-- **Section 17.3.** The set $`[A]^1` is identified with $`A` by the correspondence
$`\{a\} \leftrightarrow a`. -/
theorem kSubsets_one (A : Set α) : kSubsets A 1 = (fun a => ({a} : Finset α)) '' A := by
  ext t
  constructor
  · rintro ⟨h, hc⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hc
    exact ⟨a, h (by simp), rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨by simpa using ha, Finset.card_singleton a⟩

/-- **Section 17.1**, non-vacuity. An infinite set has $`k`-element subsets for every $`k`. -/
theorem kSubsets_nonempty {A : Set α} (hA : A.Infinite) (k : ℕ) : (kSubsets A k).Nonempty :=
  hA.exists_subset_card_eq k

/-- **Section 17.1, definition.** Given colour classes $`C_i` of $`k`-element sets, a set $`B`
is _monochromatic_ if all of its $`k`-element subsets get the same colour:
$`[B]^k \subseteq C_i` for some $`i`. -/
def IsMonochromatic (C : ι → Set (Finset α)) (k : ℕ) (B : Set α) : Prop :=
  ∃ i, kSubsets B k ⊆ C i

/-- **Section 17.1.** For a colouring given as a function $`c`, with colour classes the fibres
of $`c`, a set is monochromatic exactly when $`c` is constant on its $`k`-element subsets. -/
theorem isMonochromatic_fibres_iff {c : Finset α → κ} {k : ℕ} {B : Set α} :
    IsMonochromatic (fun i => c ⁻¹' {i}) k B ↔ ∃ i, ∀ t ∈ kSubsets B k, c t = i :=
  Iff.rfl

/-- **Section 17.1**, the opening observation (pigeonhole principle for infinite sets). If an
infinite set $`A` is contained in a finite union $`C_1 \cup \dots \cup C_r`, then one of the
sets $`A \cap C_i` is infinite. The book treats this as evident; it is Mathlib's fact that a
finite union of finite sets is finite. -/
theorem exists_infinite_inter_of_subset_iUnion [Finite ι] {A : Set α} (hA : A.Infinite)
    (C : ι → Set α) (h : A ⊆ ⋃ i, C i) : ∃ i, (A ∩ C i).Infinite := by
  by_contra hcon
  refine hA ((Set.finite_iUnion fun i => not_infinite.1 (not_exists.1 hcon i)).subset
    fun a ha => ?_)
  obtain ⟨i, hi⟩ := mem_iUnion.1 (h ha)
  exact mem_iUnion.2 ⟨i, ha, hi⟩

/-- **Section 17.1**, the opening observation in the language of colourings. Whenever the
points of an infinite set $`A` are coloured with finitely many colours, some infinite subset of
$`A` is monochromatic. -/
theorem exists_infinite_monochromatic_points [Finite κ] {A : Set α} (hA : A.Infinite)
    (c : α → κ) : ∃ B ⊆ A, B.Infinite ∧ ∃ i, ∀ a ∈ B, c a = i := by
  obtain ⟨i, hi⟩ := exists_infinite_inter_of_subset_iUnion hA (fun i => c ⁻¹' {i})
    fun a _ => mem_iUnion.2 ⟨c a, rfl⟩
  exact ⟨_, inter_subset_left, hi, i, fun a ha => ha.2⟩

end Colourings

/-!
## 17.2 A Nonstandard Approach

Before Ramsey's theorem itself, the book analyses an infinite partially ordered set $`P`
directly. Fix a nonstandard $`\pi` in the enlargement of $`P` and split the standard elements
into the set $`L` of those below $`\pi`, the set $`U` of those above it, and the rest. If $`L`
has no maximal element it contains an increasing sequence; if $`U` has no minimal element it
contains a decreasing one. Otherwise the region $`M` strictly between a maximal element of $`L`
and a minimal element of $`U` contains $`\pi` in its enlargement, and no standard element of
$`M` is comparable with $`\pi`. An antichain in $`M` is then built by repeatedly choosing a
standard element that is, like $`\pi`, incomparable with everything chosen so far.

The book first adjoins a least and a greatest element to $`P`, so that $`L` and $`U` are
nonempty, and removes them at the end. The formalization avoids this by letting the lower
bound of $`M` be absent when $`L` is empty, and the upper bound be absent when $`U` is empty.

Two small tools for building sequences by recursion come first; they are the only place where
the recursion is carried out, and every inductive construction of the chapter is an instance of
one of them.
-/

section Sequences

/-- **Section 17.2**, tool (not a numbered item). A sequence can be built step by step: if
$`x_0` satisfies an invariant, and every $`x` satisfying the invariant has a successor $`y`
that satisfies it and is related to $`x`, then there is a sequence starting at $`x_0`, all of
whose terms satisfy the invariant, with consecutive terms related. -/
theorem exists_seq_of_step {X : Type*} (Inv : X → Prop) (R : X → X → Prop) {x₀ : X}
    (h₀ : Inv x₀) (step : ∀ x, Inv x → ∃ y, Inv y ∧ R x y) :
    ∃ s : ℕ → X, s 0 = x₀ ∧ ∀ n, Inv (s n) ∧ R (s n) (s (n + 1)) := by
  choose! f hf using step
  let g : ℕ → {x // Inv x} := fun n =>
    Nat.rec ⟨x₀, h₀⟩ (fun _ x => ⟨f x.1, (hf x.1 x.2).1⟩) n
  exact ⟨fun n => (g n).1, rfl, fun n => ⟨(g n).2, (hf _ (g n).2).2⟩⟩

/-- **Sections 17.2 and 17.3**, tool (not a numbered item). A sequence can be built by choosing
each term in terms of the finite set of its predecessors: if for every finite set $`F` there is
some $`x` with $`R(F, x)`, then there is a sequence $`s` with
$`R(\{s_0, \dots, s_{n-1}\}, s_n)` for every $`n`. -/
theorem exists_seq_of_forall_finset_exists {α : Type*} [DecidableEq α]
    (R : Finset α → α → Prop) (h : ∀ F, ∃ x, R F x) :
    ∃ s : ℕ → α, ∀ n, R ((Finset.range n).image s) (s n) := by
  choose next hnext using h
  let G : ℕ → Finset α := fun n => Nat.rec ∅ (fun _ F => insert (next F) F) n
  have hG : ∀ n, G n = (Finset.range n).image fun m => next (G m) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change insert (next (G n)) (G n) = _
      rw [Finset.range_add_one, Finset.image_insert, ← ih]
  refine ⟨fun n => next (G n), fun n => ?_⟩
  rw [← hG]
  exact hnext _

end Sequences

section StarRelations

variable {α : Type u}

/-- **Section 3.14**, restated for use here. A standard element $`a` is related to the class of
a sequence $`s` by the enlarged relation exactly when $`a` is related to $`s_n` for almost all
$`n`. -/
theorem starRel₂_of_ofSeq {β : Type u} {P : α → β → Prop} {a : α} {s : ℕ → β} :
    starRel₂ P (of a : Ultrapower α) (ofSeq s : Ultrapower β) ↔
      ∀ᶠ n in hyperfilter ℕ, P a (s n) :=
  starRel₂_ofSeq (r := fun _ => a)

/-- **Section 3.14**, restated for use here. The class of a sequence $`r` is related to a
standard element $`b` by the enlarged relation exactly when $`r_n` is related to $`b` for
almost all $`n`. -/
theorem starRel₂_ofSeq_of {β : Type u} {P : α → β → Prop} {r : ℕ → α} {b : β} :
    starRel₂ P (ofSeq r : Ultrapower α) (of b : Ultrapower β) ↔
      ∀ᶠ n in hyperfilter ℕ, P (r n) b :=
  starRel₂_ofSeq (s := fun _ => b)

end StarRelations

section Posets

variable {P : Type u} [PartialOrder P]

/-- **Section 17.2.** A nonempty set $`L` without maximal elements (every member has a strictly
larger member) contains a strictly increasing sequence. -/
theorem exists_strictMono_of_forall_exists_gt {L : Set P} (hne : L.Nonempty)
    (h : ∀ x ∈ L, ∃ y ∈ L, x < y) : ∃ s : ℕ → P, StrictMono s ∧ ∀ n, s n ∈ L := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨s, -, hs⟩ := exists_seq_of_step (· ∈ L) (· < ·) hx₀ h
  exact ⟨s, strictMono_nat_of_lt_succ fun n => (hs n).2, fun n => (hs n).1⟩

/-- **Section 17.2.** A nonempty set $`U` without minimal elements (every member has a strictly
smaller member) contains a strictly decreasing sequence. -/
theorem exists_strictAnti_of_forall_exists_lt {U : Set P} (hne : U.Nonempty)
    (h : ∀ x ∈ U, ∃ y ∈ U, y < x) : ∃ s : ℕ → P, StrictAnti s ∧ ∀ n, s n ∈ U := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨s, -, hs⟩ := exists_seq_of_step (· ∈ U) (fun x y => y < x) hx₀ h
  exact ⟨s, strictAnti_nat_of_succ_lt fun n => (hs n).2, fun n => (hs n).1⟩

/-- **Section 17.2**, the inductive construction of the antichain. Let $`\pi` belong to the
enlargement of a set $`M` and be incomparable, under the enlarged order, with every standard
member of $`M`. Then $`M` contains an antichain $`(p_n)`: distinct indices give incomparable
elements. At each stage the statement "there is a member of the enlargement of $`M`
incomparable with $`p_1, \dots, p_n`" is true, with witness $`\pi`, so a standard such member
exists. -/
theorem exists_antichain_of_incomparable_nonstandard {M : Set P} {π : Ultrapower P}
    (hM : π ∈ (starSet M : Set (Ultrapower P)))
    (hinc : ∀ m ∈ M, ¬ starRel₂ (fun a b : P => a ≤ b) (of m : Ultrapower P) π ∧
      ¬ starRel₂ (fun a b : P => a ≤ b) π (of m : Ultrapower P)) :
    ∃ s : ℕ → P, (∀ n, s n ∈ M) ∧ ∀ m n, m ≠ n → ¬ s m ≤ s n := by
  classical
  obtain ⟨p, rfl⟩ := ofSeq_surjective (α := P) π
  have hM' : ∀ᶠ n in hyperfilter ℕ, p n ∈ M := ofSeq_mem_starSet.1 hM
  have hinc' : ∀ m ∈ M, ∀ᶠ n in hyperfilter ℕ, ¬ m ≤ p n ∧ ¬ p n ≤ m := fun m hm =>
    (almostAll_not.2 (mt starRel₂_of_ofSeq.2 (hinc m hm).1)).and
      (almostAll_not.2 (mt starRel₂_ofSeq_of.2 (hinc m hm).2))
  obtain ⟨s, hs⟩ := exists_seq_of_forall_finset_exists
    (fun F x => x ∈ M ∧ ∀ y ∈ F, y ∈ M → ¬ y ≤ x ∧ ¬ x ≤ y) (fun F => by
      have h : ∀ᶠ n in hyperfilter ℕ, ∀ y ∈ F, y ∈ M → ¬ y ≤ p n ∧ ¬ p n ≤ y := by
        rw [eventually_all_finset]
        intro y _
        by_cases hy : y ∈ M
        · exact (hinc' y hy).mono fun n hn _ => hn
        · exact Eventually.of_forall fun n h => absurd h hy
      obtain ⟨n, hn1, hn2⟩ := (hM'.and h).exists
      exact ⟨p n, hn1, hn2⟩)
  refine ⟨s, fun n => (hs n).1, ?_⟩
  have key : ∀ m n, m < n → ¬ s m ≤ s n ∧ ¬ s n ≤ s m := fun m n hmn =>
    (hs n).2 (s m) (Finset.mem_image.2 ⟨m, Finset.mem_range.2 hmn, rfl⟩) (hs m).1
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact (key m n h).1
  · exact (key n m h).2

/-- **Theorem 17.1.1**, by the nonstandard analysis of Section 17.2. An infinite partially
ordered set contains a strictly increasing sequence, or a strictly decreasing sequence, or an
infinite antichain (a sequence whose terms with distinct indices are pairwise incomparable).

With $`\pi` nonstandard, $`L` the set of standard elements below $`\pi` and $`U` the set of
those above, the proof finds an increasing sequence in $`L` if $`L` is nonempty without maximal
elements, a decreasing sequence in $`U` if $`U` is nonempty without minimal elements, and
otherwise an antichain in the region between a maximal element of $`L` and a minimal element of
$`U`. Unlike the book, no least and greatest elements are adjoined: an empty $`L` or $`U`
simply imposes no bound. -/
theorem exists_strictMono_or_strictAnti_or_antichain_nonstandard [Infinite P] :
    ∃ s : ℕ → P, StrictMono s ∨ StrictAnti s ∨ ∀ m n, m ≠ n → ¬ s m ≤ s n := by
  obtain ⟨π, -, hπ⟩ := exists_nonstandard_mem_starSet (αS := Ultrapower P)
    (infinite_univ (α := P))
  obtain ⟨p, rfl⟩ := ofSeq_surjective (α := P) π
  have hns : ∀ a : P, ∀ᶠ n in hyperfilter ℕ, p n ≠ a := fun a =>
    ofSeq_ne_ofSeq.1 fun h => hπ ⟨a, h.symm⟩
  let L : Set P := {q | starRel₂ (fun a b : P => a < b) (of q : Ultrapower P) (ofSeq p : Ultrapower P)}
  let U : Set P := {q | starRel₂ (fun a b : P => a < b) (ofSeq p : Ultrapower P) (of q : Ultrapower P)}
  have hL_iff : ∀ q, q ∈ L ↔ ∀ᶠ n in hyperfilter ℕ, q < p n := fun q => starRel₂_of_ofSeq
  have hU_iff : ∀ q, q ∈ U ↔ ∀ᶠ n in hyperfilter ℕ, p n < q := fun q => starRel₂_ofSeq_of
  -- First case: `L` is nonempty and has no maximal element.
  by_cases hL : L.Nonempty ∧ ∀ x ∈ L, ∃ y ∈ L, x < y
  · obtain ⟨s, hs, -⟩ := exists_strictMono_of_forall_exists_gt hL.1 hL.2
    exact ⟨s, Or.inl hs⟩
  -- Second case: `U` is nonempty and has no minimal element.
  by_cases hU : U.Nonempty ∧ ∀ x ∈ U, ∃ y ∈ U, y < x
  · obtain ⟨s, hs, -⟩ := exists_strictAnti_of_forall_exists_lt hU.1 hU.2
    exact ⟨s, Or.inr (Or.inl hs)⟩
  -- The lower bound: everything, or the elements above a maximal element of `L`.
  obtain ⟨Lo, hπLo, hLo⟩ : ∃ Lo : Set P,
      (ofSeq p : Ultrapower P) ∈ (starSet Lo : Set (Ultrapower P)) ∧ ∀ m ∈ Lo, m ∉ L := by
    by_cases hne : L.Nonempty
    · obtain ⟨x, hx, hmax⟩ : ∃ x ∈ L, ∀ y ∈ L, ¬ x < y := by
        by_contra h
        push Not at h
        exact hL ⟨hne, h⟩
      exact ⟨Ioi x, ofSeq_mem_starSet.2 ((hL_iff x).1 hx), fun m hm hmL => hmax m hmL hm⟩
    · exact ⟨univ, by rw [starSet_univ]; trivial, fun m _ hm => hne ⟨m, hm⟩⟩
  -- The upper bound: everything, or the elements below a minimal element of `U`.
  obtain ⟨Hi, hπHi, hHi⟩ : ∃ Hi : Set P,
      (ofSeq p : Ultrapower P) ∈ (starSet Hi : Set (Ultrapower P)) ∧ ∀ m ∈ Hi, m ∉ U := by
    by_cases hne : U.Nonempty
    · obtain ⟨x, hx, hmin⟩ : ∃ x ∈ U, ∀ y ∈ U, ¬ y < x := by
        by_contra h
        push Not at h
        exact hU ⟨hne, h⟩
      exact ⟨Iio x, ofSeq_mem_starSet.2 ((hU_iff x).1 hx), fun m hm hmU => hmin m hmU hm⟩
    · exact ⟨univ, by rw [starSet_univ]; trivial, fun m _ hm => hne ⟨m, hm⟩⟩
  -- The middle region contains `π` in its enlargement, and nothing in it is comparable with `π`.
  have hπM : (ofSeq p : Ultrapower P) ∈ (starSet (Lo ∩ Hi) : Set (Ultrapower P)) := by
    rw [starSet_inter]
    exact ⟨hπLo, hπHi⟩
  obtain ⟨s, -, hs⟩ := exists_antichain_of_incomparable_nonstandard hπM (fun m hm => by
    constructor
    · intro h
      refine hLo m hm.1 ((hL_iff m).2 ?_)
      exact ((starRel₂_of_ofSeq.1 h).and (hns m)).mono fun n hn => lt_of_le_of_ne hn.1 hn.2.symm
    · intro h
      refine hHi m hm.2 ((hU_iff m).2 ?_)
      exact ((starRel₂_ofSeq_of.1 h).and (hns m)).mono fun n hn => lt_of_le_of_ne hn.1 hn.2)
  exact ⟨s, Or.inr (Or.inr hs)⟩

end Posets

/-!
## 17.3 Proving Ramsey's Theorem

Ramsey's theorem is proved in three moves, as in the book.

First, two colours suffice: an $`(r+1)`-colouring is turned into a $`2`-colouring by merging
the first $`r` colours, and an induction on the number of colours does the rest.

Second, for two colours ("black" and "white") the theorem is proved by induction on $`k`. Given
a colouring of the $`(k+1)`-element subsets of an infinite set $`A`, fix a nonstandard $`\pi`
in the enlargement of $`A`. The enlarged colouring assigns a colour to each set
$`t \cup \{\pi\}` with $`t` a standard finite set. A sequence $`s_0, s_1, \dots` of distinct
elements of $`A` is constructed in which every term behaves, towards the sets of its
predecessors, exactly as $`\pi` does: $`t \cup \{s_n\}` is black if and only if
$`t \cup \{\pi\}` is black, for every set $`t` of earlier terms. Colouring a $`k`-element set
$`t` of terms by the colour of $`t \cup \{\pi\}` and applying the induction hypothesis gives an
infinite set $`B` of terms on which this derived colouring is constant; and then the original
colouring is constant on the $`(k+1)`-element subsets of $`B`, because such a subset is
$`t \cup \{s_n\}` with $`s_n` its latest term.

Third, the next term of the sequence exists by existential transfer: finitely many conditions
are imposed on it, and $`\pi` satisfies them all.

The book assumes that $`A` contains the natural numbers and takes $`\pi` to be an unlimited
hypernatural, so that "latest term" can be read as "largest term". Here $`A` is an arbitrary
infinite set in an arbitrary type and $`\pi` any nonstandard member of its enlargement; only
the order of the indices is used. The induction on $`k` is started at $`k = 0`, where the
statement is trivial; the book's base case $`k = 1`, the pigeonhole principle, is also proved
directly.
-/

section Ramsey

variable {α : Type u} {κ : Type*} {ι : Type*}

/-- **Section 17.3**, reduction to two colours. Fix $`k` and suppose that every $`2`-colouring
of the $`k`-element subsets of an infinite set has an infinite monochromatic subset. Then the
same holds for colourings by any finite set $`S` of colours: if $`c` takes values in $`S` on
$`[A]^k`, there is an infinite $`B \subseteq A` on whose $`k`-element subsets $`c` is constant.
The proof is the book's induction on the number of colours, in the form of an induction on the
finite set $`S`: single out one colour, treat the others as one, and recolour. -/
theorem ramsey_of_two_colours (k : ℕ)
    (h2 : ∀ A : Set α, A.Infinite → ∀ c : Finset α → Bool,
      ∃ B ⊆ A, B.Infinite ∧ ∃ i, ∀ t ∈ kSubsets B k, c t = i)
    (S : Finset κ) : ∀ A : Set α, A.Infinite → ∀ c : Finset α → κ,
      (∀ t ∈ kSubsets A k, c t ∈ S) →
      ∃ B ⊆ A, B.Infinite ∧ ∃ i ∈ S, ∀ t ∈ kSubsets B k, c t = i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro A hA c h
    obtain ⟨t, ht⟩ := hA.exists_subset_card_eq k
    exact absurd (h t ht) (Finset.notMem_empty _)
  | insert a S _ ih =>
    intro A hA c h
    obtain ⟨B, hBA, hB, i, hi⟩ := h2 A hA fun t => decide (c t = a)
    cases i with
    | true =>
      exact ⟨B, hBA, hB, a, Finset.mem_insert_self a S, fun t ht => of_decide_eq_true (hi t ht)⟩
    | false =>
      obtain ⟨B', hB'B, hB', j, hj, hj'⟩ := ih B hB c fun t ht =>
        (Finset.mem_insert.1 (h t (kSubsets_mono hBA k ht))).resolve_left
          (of_decide_eq_false (hi t ht))
      exact ⟨B', hB'B.trans hBA, hB', j, Finset.mem_insert_of_mem hj, hj'⟩

/-- **Section 17.3, definition.** The colour that the enlarged $`2`-colouring gives to
$`t \cup \{\pi\}`, for a standard finite set $`t` and an element $`\pi` of the ultrapower: the
set $`t \cup \{\pi\}` is _black_ when it belongs to the enlargement $`{}^*C_b` of the class of
black sets. Here $`t \cup \{\pi\}` is the value at $`\pi` of the extension of the function
$`x \mapsto t \cup \{x\}`. -/
def StarBlack [DecidableEq α] (c : Finset α → Bool) (π : Ultrapower α) (t : Finset α) : Prop :=
  (starMap (fun x => insert x t) π : Ultrapower (Finset α)) ∈
    (starSet {u : Finset α | c u = true} : Set (Ultrapower (Finset α)))

/-- **Section 17.3.** If $`\pi` is the class of the sequence $`(p_n)`, then $`t \cup \{\pi\}`
is black exactly when $`t \cup \{p_n\}` is black for almost all $`n`. -/
theorem starBlack_ofSeq [DecidableEq α] {c : Finset α → Bool} {p : ℕ → α} {t : Finset α} :
    StarBlack c (ofSeq p) t ↔ ∀ᶠ n in hyperfilter ℕ, c (insert (p n) t) = true := by
  rw [StarBlack, starMap_ofSeq, ofSeq_mem_starSet]
  rfl

/-- **Section 17.3**, the enlarged classes still form a $`2`-colouring: a set
$`t \cup \{\pi\}` that is not in the enlargement of the black sets is in the enlargement of
the white sets. -/
theorem not_starBlack_iff [DecidableEq α] {c : Finset α → Bool} {π : Ultrapower α}
    {t : Finset α} :
    ¬ StarBlack c π t ↔ (starMap (fun x => insert x t) π : Ultrapower (Finset α)) ∈
      (starSet {u : Finset α | c u = false} : Set (Ultrapower (Finset α))) := by
  have h : {u : Finset α | c u = false} = {u : Finset α | c u = true}ᶜ := by
    ext u
    simp
  rw [h, starSet_compl]
  rfl

/-- **Section 17.3**, the extension of the $`2`-colouring. The enlargements $`{}^*C_b` and
$`{}^*C_w` of the two colour classes are disjoint and together contain all of
$`{}^*([A]^{k})`, so they $`2`-colour it. By Exercise 17.3.1
({lit}`Goldblatt.bijOn_internalElems_starSet_kSubsets`, proved below) the members of
$`{}^*([A]^{k})` are the $`k`-element subsets of the enlargement of $`A`, so this is the
book's colouring of $`[{}^*A]^{k}`. In fact the two enlarged classes partition the whole ultrapower of the type of
finite sets, because here a colouring is a total function. -/
theorem starSet_black_white (c : Finset α → Bool) (A : Set α) (k : ℕ) :
    (starSet (kSubsets A k) : Set (Ultrapower (Finset α))) ⊆
        starSet {u : Finset α | c u = true} ∪ starSet {u : Finset α | c u = false} ∧
      Disjoint (starSet {u : Finset α | c u = true} : Set (Ultrapower (Finset α)))
        (starSet {u : Finset α | c u = false}) := by
  have h : {u : Finset α | c u = false} = {u : Finset α | c u = true}ᶜ := by
    ext u
    simp
  rw [h, starSet_compl]
  exact ⟨fun S _ => by rw [union_compl_self]; trivial, disjoint_compl_right⟩

/-- **Section 17.3**, the existential transfer step. Let $`\pi` be a nonstandard member of the
enlargement of $`A`, and let $`F` be a finite set of standard elements. Then there is a
standard $`x \in A`, outside $`F`, that behaves towards $`F` just like $`\pi`: for every
$`t \subseteq F`, the set $`t \cup \{x\}` is black if and only if $`t \cup \{\pi\}` is black.

These are finitely many conditions on $`x`, each true of $`\pi`; in the ultrapower each holds
of $`p_n` for almost all $`n`, where $`\pi = [p_n]`, hence all hold together for almost all
$`n`, and in particular for some $`n`. -/
theorem exists_standard_like_nonstandard [DecidableEq α] (c : Finset α → Bool) {A : Set α}
    {π : Ultrapower α} (hπA : π ∈ (starSet A : Set (Ultrapower α)))
    (hπ : π ∉ range (of : α → Ultrapower α)) (F : Finset α) :
    ∃ x ∈ A, x ∉ F ∧ ∀ t ⊆ F, (c (insert x t) = true ↔ StarBlack c π t) := by
  obtain ⟨p, rfl⟩ := ofSeq_surjective (α := α) π
  have h1 : ∀ᶠ n in hyperfilter ℕ, p n ∈ A := ofSeq_mem_starSet.1 hπA
  have h2 : ∀ᶠ n in hyperfilter ℕ, ∀ a ∈ F, p n ≠ a := by
    rw [eventually_all_finset]
    intro a _
    exact ofSeq_ne_ofSeq.1 fun h => hπ ⟨a, h.symm⟩
  have h3 : ∀ᶠ n in hyperfilter ℕ, ∀ t ∈ F.powerset,
      (c (insert (p n) t) = true ↔ StarBlack c (ofSeq p) t) := by
    rw [eventually_all_finset]
    intro t _
    by_cases ht : StarBlack c (ofSeq p) t
    · exact (starBlack_ofSeq.1 ht).mono fun n hn => iff_of_true hn ht
    · exact (almostAll_not.2 (mt starBlack_ofSeq.2 ht)).mono fun n hn => iff_of_false hn ht
  obtain ⟨n, hn1, hn2, hn3⟩ := (h1.and (h2.and h3)).exists
  exact ⟨p n, hn1, fun hmem => hn2 _ hmem rfl, fun t ht => hn3 t (Finset.mem_powerset.2 ht)⟩

/-- **Section 17.3**, the sequence guided by $`\pi`. For a nonstandard $`\pi` in the
enlargement of $`A` there is a sequence $`s` of distinct elements of $`A` each of whose terms
relates to its predecessors as $`\pi` does: whenever $`t` is a set of terms of index below
$`n`, the set $`t \cup \{s_n\}` is black if and only if $`t \cup \{\pi\}` is black. This is
the book's property (iii), for sets $`t` of any size. -/
theorem exists_seq_like_nonstandard [DecidableEq α] (c : Finset α → Bool) {A : Set α}
    {π : Ultrapower α} (hπA : π ∈ (starSet A : Set (Ultrapower α)))
    (hπ : π ∉ range (of : α → Ultrapower α)) :
    ∃ s : ℕ → α, Function.Injective s ∧ (∀ n, s n ∈ A) ∧
      ∀ n, ∀ t ⊆ (Finset.range n).image s, (c (insert (s n) t) = true ↔ StarBlack c π t) := by
  obtain ⟨s, hs⟩ := exists_seq_of_forall_finset_exists
    (fun F x => x ∈ A ∧ x ∉ F ∧ ∀ t ⊆ F, (c (insert x t) = true ↔ StarBlack c π t))
    (exists_standard_like_nonstandard c hπA hπ)
  refine ⟨s, Function.Injective.of_lt_imp_ne fun m n hmn h => ?_, fun n => (hs n).1, fun n => (hs n).2.2⟩
  exact (hs n).2.1 (Finset.mem_image.2 ⟨m, Finset.mem_range.2 hmn, h⟩)

/-- **Section 17.3**, the inductive step in $`k`. If Ramsey's theorem holds for
$`2`-colourings of $`k`-element subsets (of every infinite set), then it holds for
$`2`-colourings of $`(k+1)`-element subsets.

Take the sequence $`s` guided by a nonstandard $`\pi`, let $`D` be its set of terms, colour a
$`k`-element subset $`t` of $`D` black when $`t \cup \{\pi\}` is black, and let
$`B \subseteq D` be infinite and monochromatic for this colouring. A $`(k+1)`-element subset
$`u` of $`B` is $`t \cup \{s_m\}`, where $`s_m` is its term of largest index and $`t` consists
of earlier terms; so $`u` has the colour of $`t \cup \{\pi\}`, which is the colour of $`B`. -/
theorem ramsey_two_colours_succ (k : ℕ)
    (ih : ∀ D : Set α, D.Infinite → ∀ c : Finset α → Bool,
      ∃ B ⊆ D, B.Infinite ∧ ∃ i, ∀ t ∈ kSubsets B k, c t = i)
    {A : Set α} (hA : A.Infinite) (c : Finset α → Bool) :
    ∃ B ⊆ A, B.Infinite ∧ ∃ i, ∀ t ∈ kSubsets B (k + 1), c t = i := by
  classical
  obtain ⟨π, hπA, hπ⟩ := exists_nonstandard_mem_starSet (αS := Ultrapower α) hA
  obtain ⟨s, hinj, hsA, hs⟩ := exists_seq_like_nonstandard c hπA hπ
  obtain ⟨B, hBD, hB, i, hi⟩ := ih (range s) (infinite_range_of_injective hinj)
    fun t => decide (StarBlack c π t)
  refine ⟨B, hBD.trans (range_subset_iff.2 hsA), hB, i, ?_⟩
  rintro u ⟨huB, hcard⟩
  -- Write `u` as the image of a set `J` of indices, with largest index `m`.
  obtain ⟨J, -, rfl⟩ : ∃ J : Finset ℕ, (J : Set ℕ) ⊆ univ ∧ J.image s = u :=
    Finset.subset_set_image_iff.1 (by rw [image_univ]; exact huB.trans hBD)
  rw [Finset.card_image_of_injective _ hinj] at hcard
  have hJ : J.Nonempty := Finset.card_pos.1 (by omega)
  set m := J.max' hJ with hm
  have hmJ : m ∈ J := J.max'_mem hJ
  -- The remaining terms form a `k`-element subset `t` of `B`, all of index below `m`.
  have hu : J.image s = insert (s m) ((J.erase m).image s) := by
    rw [← Finset.image_insert, Finset.insert_erase hmJ]
  have htB : (J.erase m).image s ∈ kSubsets B k := by
    refine ⟨fun x hx => huB ?_, ?_⟩
    · rw [hu]
      exact Finset.mem_insert_of_mem hx
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem hmJ, hcard]
      rfl
  have hprev : (J.erase m).image s ⊆ (Finset.range m).image s :=
    Finset.image_subset_image fun j hj => Finset.mem_range.2
      (lt_of_le_of_ne (J.le_max' j (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj))
  have h1 := hs m _ hprev
  have h2 := hi _ htB
  rw [hu]
  cases i with
  | true => exact h1.2 (of_decide_eq_true h2)
  | false =>
    have h3 : ¬ c (insert (s m) ((J.erase m).image s)) = true :=
      fun h => of_decide_eq_false h2 (h1.1 h)
    simpa using h3

/-- **Ramsey's Theorem for two colours** (Section 17.3). For every $`k`, every infinite set
$`A` and every colouring of the $`k`-element subsets of $`A` in black and white, there is an
infinite subset of $`A` all of whose $`k`-element subsets have the same colour. Induction on
$`k`, with {name}`Goldblatt.ramsey_two_colours_succ` as the inductive step. -/
theorem ramsey_two_colours (k : ℕ) {A : Set α} (hA : A.Infinite) (c : Finset α → Bool) :
    ∃ B ⊆ A, B.Infinite ∧ ∃ i, ∀ t ∈ kSubsets B k, c t = i := by
  induction k generalizing A c with
  | zero =>
    refine ⟨A, Subset.rfl, hA, c ∅, fun t ht => ?_⟩
    rw [kSubsets_zero] at ht
    rw [mem_singleton_iff.1 ht]
  | succ k ih => exact ramsey_two_colours_succ k (fun D hD c' => ih hD c') hA c

/-- **Ramsey's Theorem** (Section 17.1; proved in Section 17.3). Let $`A` be an infinite set
and let the $`k`-element subsets of $`A` be coloured with finitely many colours. Then $`A` has
an infinite subset $`B` that is monochromatic: all $`k`-element subsets of $`B` receive the
same colour.

The colouring is a function $`c` from finite sets to a finite type of colours; only its values
on $`[A]^k` matter. The proof combines the reduction to two colours with the two-colour
theorem, whose inductive step is the nonstandard construction. -/
theorem infinite_ramsey [Finite κ] (k : ℕ) {A : Set α} (hA : A.Infinite) (c : Finset α → κ) :
    ∃ B ⊆ A, B.Infinite ∧ ∃ i, ∀ t ∈ kSubsets B k, c t = i := by
  have := Fintype.ofFinite κ
  obtain ⟨B, hBA, hB, i, -, hi⟩ := ramsey_of_two_colours k
    (fun A hA c => ramsey_two_colours k hA c) Finset.univ A hA c fun _ _ => Finset.mem_univ _
  exact ⟨B, hBA, hB, i, hi⟩

/-- **Ramsey's Theorem**, written out without the notation $`[B]^k`: for every colouring $`c`
of finite subsets of a type by finitely many colours, every $`k` and every infinite set $`A`,
there are an infinite $`B \subseteq A` and a colour $`i` such that $`c(t) = i` for every
$`k`-element set $`t \subseteq B`. -/
theorem infinite_ramsey' [Finite κ] (k : ℕ) {A : Set α} (hA : A.Infinite) (c : Finset α → κ) :
    ∃ B : Set α, B ⊆ A ∧ B.Infinite ∧
      ∃ i : κ, ∀ t : Finset α, (t : Set α) ⊆ B → t.card = k → c t = i := by
  obtain ⟨B, hBA, hB, i, hi⟩ := infinite_ramsey k hA c
  exact ⟨B, hBA, hB, i, fun t ht hk => hi t ⟨ht, hk⟩⟩

/-- **Section 17.1**, non-vacuity. Colour a finite set of natural numbers by the parity of the
sum of its elements. The set of even numbers is infinite and monochromatic for this colouring
of pairs, so the conclusion of Ramsey's theorem is witnessed concretely here. -/
example : ∃ B : Set ℕ, B.Infinite ∧
    ∃ i, ∀ t ∈ kSubsets B 2, decide (Even (t.sum id)) = i := by
  refine ⟨{n | Even n}, ?_, true, fun t ht => decide_eq_true (Finset.even_sum _ fun a ha => ?_)⟩
  · refine infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n)
      (fun a b h => by simpa using h) fun n => even_two_mul n
  · exact ht.1 ha

/-- **Ramsey's Theorem**, in the book's formulation by a finite cover (Section 17.1). If $`A`
is infinite and $`[A]^k \subseteq C_1 \cup \dots \cup C_r`, then $`A` has an infinite
monochromatic subset $`B`, that is, $`[B]^k \subseteq C_i` for some $`i`. The classes need not
be disjoint. -/
theorem infinite_ramsey_cover [Finite ι] (k : ℕ) {A : Set α} (hA : A.Infinite)
    (C : ι → Set (Finset α)) (hC : kSubsets A k ⊆ ⋃ i, C i) :
    ∃ B ⊆ A, B.Infinite ∧ IsMonochromatic C k B := by
  classical
  let c : Finset α → Option ι := fun t => if h : ∃ i, t ∈ C i then some h.choose else none
  have hc : ∀ t ∈ kSubsets A k, ∀ o, c t = o → ∃ i, o = some i ∧ t ∈ C i := by
    intro t ht o ho
    have h : ∃ i, t ∈ C i := mem_iUnion.1 (hC ht)
    refine ⟨h.choose, ?_, h.choose_spec⟩
    rw [← ho]
    exact dite_eq_left h
  obtain ⟨B, hBA, hB, o, ho⟩ := infinite_ramsey k hA c
  obtain ⟨t₀, ht₀⟩ := kSubsets_nonempty hB k
  obtain ⟨i, rfl, -⟩ := hc t₀ (kSubsets_mono hBA k ht₀) o (ho t₀ ht₀)
  refine ⟨B, hBA, hB, i, fun t ht => ?_⟩
  obtain ⟨j, hj, hjt⟩ := hc t (kSubsets_mono hBA k ht) _ (ho t ht)
  rw [Option.some.inj hj]
  exact hjt

/-- **Section 17.3**, the base case $`k = 1` as the book proves it. A finite colouring of the
one-element subsets of an infinite set $`A` is a colouring of the points of $`A`, so the
pigeonhole principle gives an infinite monochromatic subset. (The main induction starts at
$`k = 0` and does not use this.) -/
theorem ramsey_one [Finite κ] {A : Set α} (hA : A.Infinite) (c : Finset α → κ) :
    ∃ B ⊆ A, B.Infinite ∧ ∃ i, ∀ t ∈ kSubsets B 1, c t = i := by
  obtain ⟨B, hBA, hB, i, hi⟩ := exists_infinite_monochromatic_points hA fun a => c {a}
  refine ⟨B, hBA, hB, i, ?_⟩
  rintro t ⟨ht, hc⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hc
  exact hi a (ht (by simp))

end Ramsey

/-!
### Exercise 17.3.1

In the book the $`2`-colouring of $`[A]^{k+1}` is extended to the $`(k+1)`-element subsets of
the enlargement of $`A`, using the inclusion of $`[{}^*A]^{k+1}` in $`{}^*([A]^{k+1})`; the
exercise asks for equality. In the ultrapower the two sides live in different types: a member
of $`{}^*([A]^k)` is the class of a sequence of finite sets, while a member of $`[{}^*A]^k` is
a finite set of classes. They are compared through the set of elements of an internal finite
set. Taking elements is injective (extensionality, transferred), and the exercise becomes the
statement that it is a bijection from $`{}^*([A]^k)` onto $`[{}^*A]^k`.
-/

section InternalFiniteSets

variable {α : Type u}

/-- **Exercise 17.3.1**, vocabulary. The set of elements of an internal finite set $`S`, a
member of the ultrapower of the type of finite sets: $`x` is an element of $`S` when the
enlarged membership relation holds. If $`S = [S_n]` and $`x = [x_n]` this says
$`x_n \in S_n` for almost all $`n`. -/
def internalElems (S : Ultrapower (Finset α)) : Set (Ultrapower α) :=
  {x | starRel₂ (fun (a : α) (s : Finset α) => a ∈ s) x S}

/-- **Exercise 17.3.1**, the almost-all criterion for the elements of an internal finite
set. -/
theorem ofSeq_mem_internalElems {g : ℕ → α} {σ : ℕ → Finset α} :
    (ofSeq g : Ultrapower α) ∈ internalElems (ofSeq σ) ↔
      ∀ᶠ n in hyperfilter ℕ, g n ∈ σ n := by
  rw [internalElems, mem_ofPred_eq, starRel₂_ofSeq]

/-- **Exercise 17.3.1**, key computation. If almost every $`S_n` is enumerated as
$`\{E_n(1), \dots, E_n(k)\}`, then the elements of the internal set $`[S_n]` are exactly the
$`k` classes $`[E_n(i)]`. This is where finiteness of $`k` is used: a sequence that almost
everywhere takes one of $`k` values almost everywhere takes a fixed one of them. -/
theorem internalElems_ofSeq_eq_range [DecidableEq α] {k : ℕ} {σ : ℕ → Finset α}
    {E : ℕ → Fin k → α} (h : ∀ᶠ n in hyperfilter ℕ, Finset.univ.image (E n) = σ n) :
    internalElems (ofSeq σ) = range fun i => (ofSeq fun n => E n i : Ultrapower α) := by
  ext y
  obtain ⟨g, rfl⟩ := ofSeq_surjective (α := α) y
  rw [ofSeq_mem_internalElems, mem_range]
  have h1 : (∀ᶠ n in hyperfilter ℕ, g n ∈ σ n) ↔ ∀ᶠ n in hyperfilter ℕ, ∃ i, E n i = g n :=
    eventually_congr (h.mono fun n hn => by rw [← hn]; simp)
  rw [h1, almostAll_exists_finite]
  exact exists_congr fun i => Ultrapower.ofSeq_eq_ofSeq.symm

/-- **Exercise 17.3.1**, transferred extensionality. An internal finite set is determined by
its elements: two members of the ultrapower of the type of finite sets with the same elements
are equal. If $`[S_n] \ne [S'_n]` then $`S_n \ne S'_n` for almost all $`n`; choose $`x_n` in
exactly one of the two. As the index sets on which $`x_n \in S_n` and on which
$`x_n \in S'_n` are complementary almost everywhere, $`[x_n]` is an element of exactly one of
the two internal sets. -/
theorem internalElems_injective :
    Function.Injective (internalElems : Ultrapower (Finset α) → Set (Ultrapower α)) := by
  intro S S' h
  obtain ⟨σ, rfl⟩ := ofSeq_surjective (α := Finset α) S
  obtain ⟨σ', rfl⟩ := ofSeq_surjective (α := Finset α) S'
  by_contra hne
  have hex : ∀ᶠ n in hyperfilter ℕ, ∃ a, ¬ (a ∈ σ n ↔ a ∈ σ' n) :=
    (Ultrapower.ofSeq_ne_ofSeq.1 hne).mono fun n hn => by
      by_contra hcon
      exact hn (Finset.ext fun a => not_not.1 (not_exists.1 hcon a))
  obtain ⟨g, hg⟩ := exists_seq_of_almostAll_exists hex
  have h1 : (∀ᶠ n in hyperfilter ℕ, g n ∈ σ n) ↔ ∀ᶠ n in hyperfilter ℕ, g n ∈ σ' n := by
    rw [← ofSeq_mem_internalElems, ← ofSeq_mem_internalElems, h]
  by_cases hs : ∀ᶠ n in hyperfilter ℕ, g n ∈ σ n
  · obtain ⟨n, hn, hn1, hn2⟩ := (hg.and (hs.and (h1.1 hs))).exists
    exact hn (iff_of_true hn1 hn2)
  · obtain ⟨n, hn, hn1, hn2⟩ :=
      (hg.and ((almostAll_not.2 hs).and (almostAll_not.2 (mt h1.2 hs)))).exists
    exact hn (iff_of_false hn1 hn2)

/-- **Exercise 17.3.1**, the two inclusions. The sets of elements of the members of the
enlargement of $`[A]^k` are exactly the $`k`-element subsets of the enlargement of $`A`.
Together with {name}`Goldblatt.internalElems_injective` this gives the identification stated as
{lit}`Goldblatt.bijOn_internalElems_starSet_kSubsets`, the next declaration. -/
theorem image_internalElems_starSet_kSubsets (A : Set α) (k : ℕ) :
    internalElems '' (starSet (kSubsets A k) : Set (Ultrapower (Finset α))) =
      (fun T : Finset (Ultrapower α) => (T : Set (Ultrapower α))) ''
        kSubsets (starSet A : Set (Ultrapower α)) k := by
  classical
  ext T
  constructor
  · -- An internal set whose terms are almost all in `[A]^k` has exactly `k` elements.
    rintro ⟨S, hS, rfl⟩
    obtain ⟨σ, rfl⟩ := ofSeq_surjective (α := Finset α) S
    have hσ : ∀ᶠ n in hyperfilter ℕ, σ n ∈ kSubsets A k := ofSeq_mem_starSet.1 hS
    have hex : ∀ᶠ n in hyperfilter ℕ, ∃ e : Fin k → α,
        Function.Injective e ∧ Finset.univ.image e = σ n := hσ.mono fun n hn => by
      let φ := (σ n).equivFinOfCardEq hn.2
      refine ⟨fun i => (φ.symm i : α), fun i j hij => φ.symm.injective (Subtype.ext hij), ?_⟩
      ext a
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact (φ.symm i).2
      · intro ha
        exact ⟨φ ⟨a, ha⟩, by simp⟩
    obtain ⟨E, hE⟩ := exists_seq_of_almostAll_exists hex
    have hinj : Function.Injective fun i => (ofSeq fun n => E n i : Ultrapower α) := by
      intro i j hij
      obtain ⟨n, hn1, hn2⟩ := ((Ultrapower.ofSeq_eq_ofSeq.1 hij).and hE).exists
      exact hn2.1 hn1
    refine ⟨Finset.univ.image fun i => (ofSeq fun n => E n i : Ultrapower α), ⟨?_, ?_⟩, ?_⟩
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      refine ofSeq_mem_starSet.2 ((hσ.and hE).mono fun n hn => hn.1.1 ?_)
      rw [← hn.2.2]
      simp
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · rw [internalElems_ofSeq_eq_range (hE.mono fun n hn => hn.2)]
      simp
  · -- A `k`-element subset of the enlargement of `A` is the set of elements of the class of
    -- the sequence of sets of `n`-th terms of representatives.
    rintro ⟨F, ⟨hFA, hFk⟩, rfl⟩
    let φ : Fin k ≃ F := (F.equivFinOfCardEq hFk).symm
    choose r hr using fun x : Ultrapower α => ofSeq_surjective (α := α) x
    let E : ℕ → Fin k → α := fun n i => r (φ i) n
    have hx : ∀ i, (ofSeq fun n => E n i : Ultrapower α) = φ i := fun i => hr (φ i)
    have hA : ∀ᶠ n in hyperfilter ℕ, ∀ i, E n i ∈ A := by
      rw [almostAll_forall_finite]
      intro i
      refine ofSeq_mem_starSet.1 ?_
      rw [hx i]
      exact hFA (φ i).2
    have hinj : ∀ᶠ n in hyperfilter ℕ, ∀ i j, E n i = E n j → i = j := by
      rw [almostAll_forall_finite]
      intro i
      rw [almostAll_forall_finite]
      intro j
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ _ => hij
      · have hne : (ofSeq fun n => E n i : Ultrapower α) ≠ ofSeq fun n => E n j := by
          rw [hx i, hx j]
          exact fun h => hij (φ.injective (Subtype.ext h))
        exact (Ultrapower.ofSeq_ne_ofSeq.1 hne).mono fun n hn h => absurd h hn
    refine ⟨ofSeq fun n => Finset.univ.image (E n), ofSeq_mem_starSet.2 ?_, ?_⟩
    · refine (hA.and hinj).mono fun n hn => ⟨fun a ha => ?_, ?_⟩
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
        exact hn.1 i
      · rw [Finset.card_image_of_injective _ fun i j h => hn.2 i j h, Finset.card_univ,
          Fintype.card_fin]
    · rw [internalElems_ofSeq_eq_range (E := E) (Eventually.of_forall fun _ => rfl)]
      ext y
      simp only [mem_range, hx, Finset.mem_coe]
      constructor
      · rintro ⟨i, rfl⟩
        exact (φ i).2
      · intro hy
        exact ⟨φ.symm ⟨y, hy⟩, by simp⟩

/-- **Exercise 17.3.1.** $`{}^*([A]^k) = [{}^*A]^k`. In the ultrapower the two sides have
different types, and the equality is the statement that passing from an internal finite set to
its set of elements is a bijection from the enlargement of $`[A]^k` onto the family of
$`k`-element subsets of the enlargement of $`A`: it maps into that family, it is injective, and
every $`k`-element subset of the enlargement of $`A` arises. The book states it with $`k + 1`
in place of $`k`. -/
theorem bijOn_internalElems_starSet_kSubsets (A : Set α) (k : ℕ) :
    Set.BijOn internalElems (starSet (kSubsets A k) : Set (Ultrapower (Finset α)))
      ((fun T : Finset (Ultrapower α) => (T : Set (Ultrapower α))) ''
        kSubsets (starSet A : Set (Ultrapower α)) k) :=
  ⟨fun _ hS => (image_internalElems_starSet_kSubsets A k).le (mem_image_of_mem _ hS),
    internalElems_injective.injOn, (image_internalElems_starSet_kSubsets A k).ge⟩

end InternalFiniteSets

/-!
## 17.1 revisited: Theorem 17.1.1 from Ramsey's theorem

This section returns to Section 17.1. With Ramsey's theorem available, Theorem 17.1.1 has the
short proof given there:
colour a pair black if its two elements are comparable and white otherwise. An infinite white
set is an antichain. An infinite black set is an infinite chain, and an infinite chain contains
an increasing or a decreasing sequence, according to whether it is well-ordered or not.
-/

section PosetsViaRamsey

variable {P : Type u} [PartialOrder P]

/-- **Theorem 17.1.1**, the last step of the proof. An infinite chain $`Q` contains a strictly
increasing or a strictly decreasing sequence. If some nonempty subset of $`Q` has no least
element, descend inside it. Otherwise $`Q` is well-ordered, and an increasing sequence is built
by starting at the least element and passing each time to the least element above the current
one; this never stops because each term has only finitely many elements of $`Q` below it. -/
theorem exists_strictMono_or_strictAnti_of_chain {Q : Set P} (hQ : Q.Infinite)
    (hch : ∀ x ∈ Q, ∀ y ∈ Q, x ≤ y ∨ y ≤ x) :
    ∃ s : ℕ → P, (∀ n, s n ∈ Q) ∧ (StrictMono s ∨ StrictAnti s) := by
  by_cases hwf : ∃ T ⊆ Q, T.Nonempty ∧ ∀ x ∈ T, ∃ y ∈ T, y < x
  · obtain ⟨T, hTQ, hne, hT⟩ := hwf
    obtain ⟨s, hs, hsT⟩ := exists_strictAnti_of_forall_exists_lt hne hT
    exact ⟨s, fun n => hTQ (hsT n), Or.inr hs⟩
  · have least : ∀ T ⊆ Q, T.Nonempty → ∃ x ∈ T, ∀ y ∈ T, x ≤ y := by
      intro T hTQ hne
      by_contra hcon
      refine hwf ⟨T, hTQ, hne, fun x hx => ?_⟩
      by_contra hx'
      refine hcon ⟨x, hx, fun y hy => ?_⟩
      rcases hch x (hTQ hx) y (hTQ hy) with h | h
      · exact h
      · exact (eq_or_lt_of_le h).elim (fun e => e.ge) fun hlt => absurd ⟨y, hy, hlt⟩ hx'
    obtain ⟨x₀, hx₀Q, hx₀⟩ := least Q Subset.rfl hQ.nonempty
    have h₀ : x₀ ∈ Q ∧ {q | q ∈ Q ∧ q ≤ x₀}.Finite :=
      ⟨hx₀Q, (finite_singleton x₀).subset fun q hq => le_antisymm hq.2 (hx₀ q hq.1)⟩
    obtain ⟨s, -, hs⟩ := exists_seq_of_step (fun x => x ∈ Q ∧ {q | q ∈ Q ∧ q ≤ x}.Finite)
      (· < ·) h₀ (by
        rintro x ⟨hxQ, hfin⟩
        have hne : {q | q ∈ Q ∧ x < q}.Nonempty := by
          by_contra hempty
          refine hQ (hfin.subset fun q hq => ⟨hq, ?_⟩)
          rcases hch x hxQ q hq with h | h
          · by_contra hqx
            exact hempty ⟨q, hq, lt_of_le_not_ge h hqx⟩
          · exact h
        obtain ⟨y, ⟨hyQ, hxy⟩, hy⟩ := least _ (fun q hq => hq.1) hne
        refine ⟨y, ⟨hyQ, (hfin.union (finite_singleton y)).subset fun q hq => ?_⟩, hxy⟩
        by_cases hqx : q ≤ x
        · exact Or.inl ⟨hq.1, hqx⟩
        · rcases hch x hxQ q hq.1 with h | h
          · exact Or.inr (le_antisymm hq.2 (hy q ⟨hq.1, lt_of_le_not_ge h hqx⟩))
          · exact absurd h hqx)
    exact ⟨s, fun n => (hs n).1.1, Or.inl (strictMono_nat_of_lt_succ fun n => (hs n).2)⟩

/-- **Theorem 17.1.1.** An infinite partially ordered set $`(P, \le)` contains a sequence
$`(p_n)` that is strictly increasing, or strictly decreasing, or an antichain: $`p_n` and
$`p_m` are incomparable whenever $`n \ne m`.

This is the proof of Section 17.1, by Ramsey's theorem for pairs applied to the colouring
"comparable or incomparable". The nonstandard proof of Section 17.2 is
{name}`Goldblatt.exists_strictMono_or_strictAnti_or_antichain_nonstandard`. -/
theorem exists_strictMono_or_strictAnti_or_antichain [Infinite P] :
    ∃ s : ℕ → P, StrictMono s ∨ StrictAnti s ∨ ∀ m n, m ≠ n → ¬ s m ≤ s n := by
  classical
  let c : Finset P → Bool := fun t => decide (∀ x ∈ t, ∀ y ∈ t, x ≤ y ∨ y ≤ x)
  obtain ⟨Q, -, hQ, i, hi⟩ := infinite_ramsey 2 (infinite_univ (α := P)) c
  have pair : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → c {x, y} = i := fun x hx y hy hxy =>
    hi _ ⟨by simp [insert_subset_iff, hx, hy], Finset.card_pair hxy⟩
  cases i with
  | true =>
    have hch : ∀ x ∈ Q, ∀ y ∈ Q, x ≤ y ∨ y ≤ x := by
      intro x hx y hy
      by_cases hxy : x = y
      · exact Or.inl hxy.le
      · exact of_decide_eq_true (pair x hx y hy hxy) x (by simp) y (by simp)
    obtain ⟨s, -, hs⟩ := exists_strictMono_or_strictAnti_of_chain hQ hch
    exact ⟨s, hs.elim Or.inl fun h => Or.inr (Or.inl h)⟩
  | false =>
    let f := hQ.natEmbedding Q
    refine ⟨fun n => f n, Or.inr (Or.inr fun m n hmn hle => ?_)⟩
    have hne : (f m : P) ≠ f n := fun h => hmn (f.injective (Subtype.ext h))
    refine of_decide_eq_false (pair _ (f m).2 _ (f n).2 hne) fun x hx y hy => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Or.inl le_rfl
    · exact Or.inl hle
    · exact Or.inr hle
    · exact Or.inl le_rfl

end PosetsViaRamsey

/-!
## 17.4 The Finite Ramsey Theorem

For a finite set there can be no infinite monochromatic subset, but one can ask for a
monochromatic subset of a prescribed size $`m`. The finite Ramsey theorem says that this is
always possible inside $`\{1, \dots, n\}` once $`n` is large enough, the bound depending only
on $`k`, on the number of colours and on $`m`.

The book derives it from the infinite theorem. Write $`\psi(n)` for "every colouring of the
$`k`-element subsets of $`\{1, \dots, n\}` has a monochromatic subset with at least $`m`
elements". For an unlimited hypernatural $`N` the transferred statement holds: an internal
colouring of the $`k`-element subsets of $`\{1, \dots, N\}` colours in particular all standard
finite sets of positive integers, the infinite theorem gives an infinite standard set $`D`
monochromatic for it, and any $`m`-element subset of $`D` is a witness. So the enlarged
statement "there is $`n` with $`\psi(n)`" is true, and by transfer so is the standard one.

In the ultrapower an internal colouring is the class of a sequence $`(c_n)` of colourings, the
colour it gives to a standard set $`t` is the colour $`c_n(t)` taken for almost all $`n`, and
the transferred $`\psi` holds at $`N = [\nu_n]` exactly when $`\psi(\nu_n)` holds for almost
all $`n`.
-/

section FiniteRamsey

variable {κ : Type*}

/-- **Section 17.4.** An internal colouring induces a colouring of the standard finite sets
that has an infinite monochromatic set. Precisely: for any sequence $`(c_n)` of colourings by
finitely many colours there are an infinite set $`D` of positive integers and a colour $`i`
such that every $`k`-element subset $`t` of $`D` has $`c_n(t) = i` for almost all $`n`; that
is, the internal colouring $`[c_n]` gives colour $`i` to $`t`. This is the infinite Ramsey
theorem applied to the induced colouring. -/
theorem exists_infinite_homogeneous_internal [Finite κ] (k : ℕ) (c : ℕ → Finset ℕ → κ) :
    ∃ D : Set ℕ, D ⊆ Ici 1 ∧ D.Infinite ∧
      ∃ i, ∀ t ∈ kSubsets D k, ∀ᶠ n in hyperfilter ℕ, c n t = i := by
  have h : ∀ t : Finset ℕ, ∃ i, ∀ᶠ n in hyperfilter ℕ, c n t = i := fun t =>
    almostAll_exists_finite.1 (Eventually.of_forall fun n => ⟨c n t, rfl⟩)
  choose χ hχ using h
  obtain ⟨D, hD1, hD, i, hi⟩ := infinite_ramsey k (Ici_infinite 1) χ
  exact ⟨D, hD1, hD, i, fun t ht => hi t ht ▸ hχ t⟩

/-- **Section 17.4**, the statement $`{}^*\psi(N)` for unlimited $`N`. Let $`Q` be a property
of finite sets of natural numbers that can be realised inside every infinite set of positive
integers, and let $`(\nu_n)` represent an unlimited hypernatural, in the sense that for each
standard $`b` almost all $`\nu_n` are at least $`b`. Then for almost all $`n`, every colouring
of the $`k`-element subsets of $`\{1, \dots, \nu_n\}` has a monochromatic subset with property
$`Q`.

The property $`Q` is "at least $`m` elements" for the finite Ramsey theorem and "at least
$`m` elements and relatively large" for the Paris–Harrington version; this single statement
serves both. The proof argues by contradiction, choosing a bad colouring $`c_n` at almost
every index and applying {name}`Goldblatt.exists_infinite_homogeneous_internal` to the internal colouring
they form. -/
theorem eventually_forall_exists_monochromatic [Finite κ] (k : ℕ) (Q : Finset ℕ → Prop)
    (hQ : ∀ D : Set ℕ, D ⊆ Ici 1 → D.Infinite → ∃ B : Finset ℕ, (B : Set ℕ) ⊆ D ∧ Q B)
    (ν : ℕ → ℕ) (hν : ∀ b : ℕ, ∀ᶠ n in hyperfilter ℕ, b ≤ ν n) :
    ∀ᶠ n in hyperfilter ℕ, ∀ c : Finset ℕ → κ, ∃ B ⊆ Finset.Icc 1 (ν n),
      Q B ∧ ∃ i, ∀ t ∈ kSubsets (B : Set ℕ) k, c t = i := by
  by_contra h
  rw [← almostAll_not] at h
  have h' : ∀ᶠ n in hyperfilter ℕ, ∃ c : Finset ℕ → κ, ¬ ∃ B ⊆ Finset.Icc 1 (ν n),
      Q B ∧ ∃ i, ∀ t ∈ kSubsets (B : Set ℕ) k, c t = i := h.mono fun n hn => not_forall.1 hn
  obtain ⟨c, hc⟩ := exists_seq_of_almostAll_exists h'
  obtain ⟨D, hD1, hD, i, hi⟩ := exists_infinite_homogeneous_internal k c
  obtain ⟨B, hBD, hQB⟩ := hQ D hD1 hD
  have h1 : ∀ᶠ n in hyperfilter ℕ, B ⊆ Finset.Icc 1 (ν n) :=
    (hν (B.sup id)).mono fun n hn b hb =>
      Finset.mem_Icc.2 ⟨hD1 (hBD hb), le_trans (Finset.le_sup (f := id) hb) hn⟩
  have h2 : ∀ᶠ n in hyperfilter ℕ, ∀ t ∈ B.powersetCard k, c n t = i := by
    rw [eventually_all_finset]
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    exact hi t ⟨(Finset.coe_subset.2 ht.1).trans hBD, ht.2⟩
  obtain ⟨n, hn, hn1, hn2⟩ := (hc.and (h1.and h2)).exists
  exact hn ⟨B, hn1, hQB, i, fun t ht =>
    hn2 t (Finset.mem_powersetCard.2 ⟨Finset.coe_subset.1 ht.1, ht.2⟩)⟩

/-- **Section 17.4.** A sequence of natural numbers that represents an unlimited hypernatural
(a member of $`{}^*\mathbb N - \mathbb N`, in the sense of Chapter 5) eventually exceeds every
standard bound at almost all indices. This connects the hypothesis of
{name}`Goldblatt.eventually_forall_exists_monochromatic` with the book's "unlimited hypernatural". -/
theorem eventually_le_of_hnat_mem_unlimitedHyperNat {ν : ℕ → ℕ}
    (h : hnat ν ∈ unlimitedHyperNat) (b : ℕ) : ∀ᶠ n in hyperfilter ℕ, b ≤ ν n := by
  have hu : Unlimited (hnat ν) := (mem_unlimitedHyperNat.1 h).2
  have hlt : (b : ℝ*) < hnat ν := by
    have := unlimited_iff_forall_nat.1 hu b
    rwa [abs_of_nonneg (hyperNat_nonneg (hnat_mem_hyperNat ν))] at this
  rw [natCast_eq_hnat, hnat_lt_hnat_iff] at hlt
  exact hlt.mono fun n hn => hn.le

/-- **Section 17.4**, the transfer step, for a general selection property $`Q` (see
{name}`Goldblatt.eventually_forall_exists_monochromatic`). There is a standard $`n` such that every
colouring of the $`k`-element subsets of $`\{1, \dots, n\}` has a monochromatic subset with
property $`Q`: the statement holds at almost every index of the unlimited hypernatural
$`\omega = [1, 2, 3, \dots]`, hence at some index. -/
theorem finite_ramsey_with [Finite κ] (k : ℕ) (Q : Finset ℕ → Prop)
    (hQ : ∀ D : Set ℕ, D ⊆ Ici 1 → D.Infinite → ∃ B : Finset ℕ, (B : Set ℕ) ⊆ D ∧ Q B) :
    ∃ n, ∀ c : Finset ℕ → κ, ∃ B ⊆ Finset.Icc 1 n,
      Q B ∧ ∃ i, ∀ t ∈ kSubsets (B : Set ℕ) k, c t = i :=
  (eventually_forall_exists_monochromatic k Q hQ id fun b =>
    eventually_hyperfilter_of_forall_ge b fun _ hn => hn).exists

/-- **Finite Ramsey Theorem** (Section 17.4). For all natural numbers $`k`, $`r`, $`m` there is
a natural number $`n` such that for every $`r`-colouring of the $`k`-element subsets of
$`\{1, \dots, n\}` there is a monochromatic set $`B \subseteq \{1, \dots, n\}` with at least
$`m` elements.

An $`r`-colouring is a function into a type with $`r` elements; its values outside
$`[\{1, \dots, n\}]^k` are irrelevant, since $`B` lies inside $`\{1, \dots, n\}`. -/
theorem finite_ramsey (k r m : ℕ) :
    ∃ n, ∀ c : Finset ℕ → Fin r, ∃ B ⊆ Finset.Icc 1 n,
      m ≤ B.card ∧ ∃ i, ∀ t ∈ kSubsets (B : Set ℕ) k, c t = i :=
  finite_ramsey_with k (fun B => m ≤ B.card) fun D _ hD => by
    obtain ⟨B, hB, hc⟩ := hD.exists_subset_card_eq m
    exact ⟨B, hB, hc.ge⟩

/-- **Section 17.4**, the book's intermediate claim in its own terms. If $`N` is an unlimited
hypernatural, represented by the sequence $`(\nu_n)`, then the transferred statement
$`{}^*\psi(N)` holds: for almost all $`n`, every $`r`-colouring of the $`k`-element subsets of
$`\{1, \dots, \nu_n\}` has a monochromatic subset with at least $`m` elements. -/
theorem eventually_finite_ramsey_of_unlimited (k r m : ℕ) {ν : ℕ → ℕ}
    (hν : hnat ν ∈ unlimitedHyperNat) :
    ∀ᶠ n in hyperfilter ℕ, ∀ c : Finset ℕ → Fin r, ∃ B ⊆ Finset.Icc 1 (ν n),
      m ≤ B.card ∧ ∃ i, ∀ t ∈ kSubsets (B : Set ℕ) k, c t = i :=
  eventually_forall_exists_monochromatic k (fun B => m ≤ B.card)
    (fun D _ hD => by
      obtain ⟨B, hB, hc⟩ := hD.exists_subset_card_eq m
      exact ⟨B, hB, hc.ge⟩)
    ν (eventually_le_of_hnat_mem_unlimitedHyperNat hν)

/-- **Finite Ramsey Theorem**, in Mathlib's vocabulary: the $`k`-element subsets of a finite
set are its {name}`Finset.powersetCard`, and the colours form an arbitrary finite type. -/
theorem finite_ramsey_powersetCard (κ : Type*) [Finite κ] (k m : ℕ) :
    ∃ n, ∀ c : Finset ℕ → κ, ∃ B ⊆ Finset.Icc 1 n,
      m ≤ B.card ∧ ∃ i, ∀ t ∈ B.powersetCard k, c t = i := by
  obtain ⟨n, hn⟩ := finite_ramsey_with (κ := κ) k (fun B => m ≤ B.card) fun D _ hD => by
    obtain ⟨B, hB, hc⟩ := hD.exists_subset_card_eq m
    exact ⟨B, hB, hc.ge⟩
  refine ⟨n, fun c => ?_⟩
  obtain ⟨B, hB, hm, i, hi⟩ := hn c
  refine ⟨B, hB, hm, i, fun t ht => hi t ?_⟩
  rw [kSubsets_coe]
  exact ht

/-- **Finite Ramsey Theorem**, in the book's formulation by a cover. For all $`k`, $`m` and
every finite index set there is $`n` such that whenever
$`[\{1, \dots, n\}]^k \subseteq C_1 \cup \dots \cup C_r`, some
$`B \subseteq \{1, \dots, n\}` with at least $`m` elements is monochromatic. With no colour
classes at all ($`r = 0`) the statement holds for $`n = k`, since the $`k`-element set
$`\{1, \dots, k\}` is then not covered. -/
theorem finite_ramsey_cover (ι : Type*) [Finite ι] (k m : ℕ) :
    ∃ n, ∀ C : ι → Set (Finset ℕ), kSubsets (Finset.Icc 1 n : Set ℕ) k ⊆ ⋃ i, C i →
      ∃ B ⊆ Finset.Icc 1 n, m ≤ B.card ∧ IsMonochromatic C k (B : Set ℕ) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨k, fun C hC => ?_⟩
    have hmem : Finset.Icc 1 k ∈ kSubsets (Finset.Icc 1 k : Set ℕ) k :=
      ⟨Subset.rfl, by simp⟩
    have := hC hmem
    rw [iUnion_of_empty] at this
    exact absurd this (notMem_empty _)
  obtain ⟨n, hn⟩ := finite_ramsey_with (κ := ι) k (fun B => m ≤ B.card) fun D _ hD => by
    obtain ⟨B, hB, hc⟩ := hD.exists_subset_card_eq m
    exact ⟨B, hB, hc.ge⟩
  refine ⟨n, fun C hC => ?_⟩
  let c : Finset ℕ → ι := fun t => if h : ∃ i, t ∈ C i then h.choose else Classical.arbitrary ι
  obtain ⟨B, hB, hm, i, hi⟩ := hn c
  refine ⟨B, hB, hm, i, fun t ht => ?_⟩
  have h : ∃ i, t ∈ C i := mem_iUnion.1 (hC (kSubsets_mono (Finset.coe_subset.2 hB) k ht))
  have hct : c t = h.choose := dite_eq_left h
  rw [← hi t ht, hct]
  exact h.choose_spec

end FiniteRamsey

/-!
### Exercise 17.4.1

The exercise asks the reader to check that $`\psi(n)` can be written as a formula of the formal
language of the universe, so that the transfer principle applies to it. It has no mathematical
content beyond that verification. In this formalization no formal language is involved: the
transferred statement at the class of a sequence $`(\nu_n)` is by definition "$`\psi(\nu_n)` for
almost all $`n`", and the two uses of transfer in the book's proof are the two halves of
{name}`Goldblatt.eventually_forall_exists_monochromatic` and {name}`Goldblatt.finite_ramsey_with`: the choice of a
sequence of colourings from an almost-everywhere existence statement (the quantifier over
internal colourings), and the passage from "almost all $`n`" to "some $`n`".

## 17.5 The Paris–Harrington Version

The monochromatic set in the finite theorem was an arbitrary $`m`-element subset of an infinite
monochromatic set $`D`, so there is room to ask for more. Call a finite set of positive
integers _relatively large_ if it has at least as many elements as its least element. Every
infinite set of positive integers has relatively large finite subsets of any prescribed minimum
size, so the same nonstandard argument yields a monochromatic set that is, in addition,
relatively large. This innocent-looking strengthening is the Paris–Harrington statement,
famous for being true but unprovable in first-order Peano arithmetic; the unprovability is
metamathematics outside the scope of this chapter, and only the truth of the statement is
formalized.
-/

section ParisHarrington

/-- **Section 17.5, definition.** A finite set $`B` of natural numbers is _relatively large_ if
$`|B| \ge \min B`: it has a least element $`b`, and $`b \le |B|`. In particular a relatively
large set is nonempty. -/
def RelativelyLarge (B : Finset ℕ) : Prop := ∃ b, IsLeast (B : Set ℕ) b ∧ b ≤ B.card

/-- **Section 17.5.** Relative largeness in terms of Mathlib's minimum of a nonempty finite
set. -/
theorem relativelyLarge_iff {B : Finset ℕ} :
    RelativelyLarge B ↔ ∃ h : B.Nonempty, B.min' h ≤ B.card := by
  constructor
  · rintro ⟨b, hb, hle⟩
    have hne : B.Nonempty := ⟨b, hb.1⟩
    exact ⟨hne, by rwa [(B.isLeast_min' hne).unique hb]⟩
  · rintro ⟨h, hle⟩
    exact ⟨B.min' h, B.isLeast_min' h, hle⟩

/-- **Section 17.5**, non-vacuity. The set $`\{2, 5\}` is relatively large, and $`\{3, 5\}` is
not. -/
example : RelativelyLarge {2, 5} ∧ ¬ RelativelyLarge {3, 5} := by
  constructor
  · exact ⟨2, ⟨by simp, by simp [lowerBounds]⟩, by simp⟩
  · rintro ⟨b, ⟨hb, hlb⟩, hle⟩
    have h3 : b ≤ 3 := hlb (by simp)
    have hb' : b = 3 ∨ b = 5 := by simpa using hb
    have hcard : ({3, 5} : Finset ℕ).card = 2 := by decide
    omega

/-- **Section 17.5.** Every infinite set $`D` of natural numbers contains, for each $`m`, a
finite relatively large subset with at least $`m` elements. The construction is the book's:
take $`j \in D` above $`m` together with $`j - 1` larger elements of $`D`, so that
$`|B| = \min B = j`. -/
theorem exists_relativelyLarge_subset {D : Set ℕ} (hD : D.Infinite) (m : ℕ) :
    ∃ B : Finset ℕ, (B : Set ℕ) ⊆ D ∧ m ≤ B.card ∧ RelativelyLarge B := by
  obtain ⟨j, hjD, hmj⟩ := hD.exists_gt m
  have hinf : {x | x ∈ D ∧ j < x}.Infinite :=
    (hD.sdiff (finite_Iic j)).mono fun x hx => ⟨hx.1, not_le.1 hx.2⟩
  obtain ⟨E, hE, hEcard⟩ := hinf.exists_subset_card_eq (j - 1)
  have hjE : j ∉ E := fun h => lt_irrefl j (hE h).2
  have hcard : (insert j E).card = j := by
    rw [Finset.card_insert_of_notMem hjE, hEcard]
    omega
  refine ⟨insert j E, ?_, by omega, j, ⟨Finset.mem_insert_self j E, ?_⟩, hcard.ge⟩
  · intro x hx
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with rfl | hx
    · exact hjD
    · exact (hE hx).1
  · intro x hx
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with rfl | hx
    · exact le_rfl
    · exact (hE hx).2.le

/-- **Paris–Harrington version of the finite Ramsey theorem** (Section 17.5). For all natural
numbers $`k`, $`r`, $`m` there is a natural number $`n` such that for every $`r`-colouring of
the $`k`-element subsets of $`\{1, \dots, n\}` there is a relatively large monochromatic set
$`B \subseteq \{1, \dots, n\}` with at least $`m` elements.

Only the truth of the statement is proved, by the nonstandard argument of Section 17.4 with a
relatively large subset selected from the infinite monochromatic set. -/
theorem paris_harrington (k r m : ℕ) :
    ∃ n, ∀ c : Finset ℕ → Fin r, ∃ B ⊆ Finset.Icc 1 n,
      (m ≤ B.card ∧ RelativelyLarge B) ∧ ∃ i, ∀ t ∈ kSubsets (B : Set ℕ) k, c t = i :=
  finite_ramsey_with k (fun B => m ≤ B.card ∧ RelativelyLarge B) fun _ _ hD =>
    exists_relativelyLarge_subset hD m

/-- **Section 17.5.** The Paris–Harrington version implies the finite Ramsey theorem: the
bound it provides for $`k`, $`r`, $`m` also serves there. -/
theorem finite_ramsey_of_paris_harrington (k r m : ℕ) :
    ∃ n, ∀ c : Finset ℕ → Fin r, ∃ B ⊆ Finset.Icc 1 n,
      m ≤ B.card ∧ ∃ i, ∀ t ∈ kSubsets (B : Set ℕ) k, c t = i := by
  obtain ⟨n, hn⟩ := paris_harrington k r m
  refine ⟨n, fun c => ?_⟩
  obtain ⟨B, hB, ⟨hm, -⟩, h⟩ := hn c
  exact ⟨B, hB, hm, h⟩

end ParisHarrington

/-!
## 17.6 Reference

The nonstandard treatment of Ramsey theory followed in this chapter is due to Joram Hirshfeld
(_Nonstandard combinatorics_, Studia Logica 47), as the book records.
-/

end Goldblatt
