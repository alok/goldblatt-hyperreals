import Goldblatt.Ch05_GreatAndSmall

/-!
# 11 (part 1). Internal Sets and Their Principles: Sections 11.1 to 11.6

This is the first of three parts of Chapter 11 (the overview is on the chapter page
{lit}`Goldblatt.Ch11_InternalSets`). It defines internal sets, works out their Boolean algebra,
proves the internal least number principle, internal induction, overflow and internal
order-completeness, and uses these to show that the familiar sets of nonstandard analysis (the
standard natural numbers, the reals, the limited numbers, the infinitesimals, the halos) are
external.
-/

universe u v

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Pointwise

/-!
## 11.1 Internal Sets

A point of the ultrapower is the class of a sequence of points. In the same way a sequence
$`(A_n)` of sets of standard elements determines one set $`[A_n]` of elements of the
ultrapower, by the almost-all criterion: the class of $`(r_n)` belongs to $`[A_n]` when
$`r_n \in A_n` for almost all $`n`. The sets that arise in this way are the _internal_ sets.
Enlargements are the internal sets given by constant sequences, and intervals with hyperreal
end points and initial segments of the hypernaturals are internal sets that are usually not
enlargements.

As in Chapter 3 the construction is carried out over an arbitrary type $`\alpha` with its star
type; the book's case is that of the reals and the hyperreals. A sequence of sets is the same
thing as a function into the type of sets, so it has a germ along the index ultrafilter, and
an internal set depends only on that germ: this is the type-level view of internal sets,
{lit}`Goldblatt.internalSetEquiv` in Section 11.2.
-/

section InternalSets

variable {α αS : Type u} [StarType α αS]

/-- **Section 11.1, type-level view.** The set of elements of the star type determined by a
germ of set-valued sequences: $`x` belongs to it when the germ of $`x` is related to the given
germ by termwise membership. -/
def internalSetOfGerm (g : Germ (hyperfilter ℕ : Filter ℕ) (Set α)) : Set αS :=
  {x | Germ.LiftRel (fun a A => a ∈ A) (StarType.equiv x) g}

/-- **Section 11.1.** The _internal set_ $`[A_n]` determined by a sequence $`(A_n)` of sets:
the class of a sequence $`(r_n)` belongs to it when $`r_n \in A_n` for almost all $`n`
(see {lit}`Goldblatt.ofSeq_mem_internalSet`). -/
def internalSet (A : ℕ → Set α) : Set αS :=
  internalSetOfGerm (A : Germ (hyperfilter ℕ : Filter ℕ) (Set α))

/-- **Section 11.1, well-definedness.** If $`[r_n] = [s_n]` then $`r_n \in A_n` for almost
all $`n` if and only if $`s_n \in A_n` for almost all $`n`. -/
theorem almostAll_mem_congr {r s : ℕ → α} {A : ℕ → Set α} (h : (ofSeq r : αS) = ofSeq s) :
    (∀ᶠ n in hyperfilter ℕ, r n ∈ A n) ↔ ∀ᶠ n in hyperfilter ℕ, s n ∈ A n := by
  have h' : ∀ᶠ n in hyperfilter ℕ, r n = s n := Ultrapower.ofSeq_eq_ofSeq.1 h
  exact ⟨fun H => (h'.and H).mono fun n hn => hn.1 ▸ hn.2,
    fun H => (h'.and H).mono fun n hn => hn.1.symm ▸ hn.2⟩

/-- **Section 11.1, the almost-all criterion for membership.** $`[r_n] \in [A_n]` if and only
if $`r_n \in A_n` for almost all $`n`. -/
theorem ofSeq_mem_internalSet {r : ℕ → α} {A : ℕ → Set α} :
    (ofSeq r : αS) ∈ internalSet A ↔ ∀ᶠ n in hyperfilter ℕ, r n ∈ A n := by
  change Germ.LiftRel (fun a A => a ∈ A) (StarType.equiv (ofSeq r : αS))
    (A : Germ (hyperfilter ℕ : Filter ℕ) (Set α)) ↔ _
  rw [equiv_ofSeq]
  exact Germ.liftRel_coe

/-- **Section 11.1**, for the hyperreals: $`[r_n] \in [A_n]` if and only if $`r_n \in A_n`
for almost all $`n`. -/
theorem hyperreal_ofSeq_mem_internalSet {r : ℕ → ℝ} {A : ℕ → Set ℝ} :
    Hyperreal.ofSeq r ∈ internalSet A ↔ ∀ᶠ n in hyperfilter ℕ, r n ∈ A n :=
  ofSeq_mem_internalSet

/-- **Section 11.1.** An element belongs to $`[A_n]` if and only if it is the class of some
sequence $`(r_n)` with $`r_n \in A_n` for almost all $`n`. -/
theorem mem_internalSet_iff {x : αS} {A : ℕ → Set α} :
    x ∈ internalSet A ↔ ∃ r : ℕ → α, x = ofSeq r ∧ ∀ᶠ n in hyperfilter ℕ, r n ∈ A n := by
  constructor
  · intro h
    obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
    exact ⟨r, rfl, ofSeq_mem_internalSet.1 h⟩
  · rintro ⟨r, rfl, h⟩
    exact ofSeq_mem_internalSet.2 h

/-- **Section 11.1.** An element of $`[A_n]` can be represented by a sequence $`(r_n)` with
$`r_n \in A_n` for _every_ $`n`, provided every $`A_n` is nonempty. -/
theorem exists_rep_forall_mem {x : αS} {A : ℕ → Set α} (hx : x ∈ internalSet A)
    (hA : ∀ n, (A n).Nonempty) : ∃ r : ℕ → α, x = ofSeq r ∧ ∀ n, r n ∈ A n := by
  classical
  obtain ⟨r, rfl, h⟩ := mem_internalSet_iff.1 hx
  refine ⟨fun n => if r n ∈ A n then r n else (hA n).some, ?_, fun n => ?_⟩
  · exact Ultrapower.ofSeq_eq_ofSeq.2 (h.mono fun n hn => by simp only [hn, ↓reduceIte])
  · dsimp only
    split_ifs with hn
    exacts [hn, (hA n).some_mem]

/-- **Section 11.1.** A set of elements of the star type of $`\alpha` is _internal_ if it is
$`[A_n]` for some sequence $`(A_n)` of subsets of $`\alpha`. The type $`\alpha` is an
explicit argument because it cannot be recovered from the star type; for sets of hyperreals
use {lit}`Goldblatt.IsInternal`. -/
def IsInternalSet (α : Type u) {αS : Type u} [StarType α αS] (X : Set αS) : Prop :=
  ∃ A : ℕ → Set α, X = internalSet A

/-- **Section 11.1.** A set of hyperreals is _internal_ if it is $`[A_n]` for some sequence
$`(A_n)` of sets of real numbers. -/
abbrev IsInternal (X : Set ℝ*) : Prop := IsInternalSet ℝ X

/-- **Section 11.6.** A set of hyperreals is _external_ if it is not internal. -/
def IsExternal (X : Set ℝ*) : Prop := ¬ IsInternal X

/-- The set $`[A_n]` is internal. -/
theorem isInternalSet_internalSet (A : ℕ → Set α) : IsInternalSet α (internalSet A : Set αS) :=
  ⟨A, rfl⟩

/-- A set of hyperreals is internal if and only if it is $`[A_n]` for a sequence of sets of
reals. -/
theorem isInternal_iff {X : Set ℝ*} : IsInternal X ↔ ∃ A : ℕ → Set ℝ, X = internalSet A :=
  Iff.rfl

/-- **Section 11.1, first example.** The internal set of a constant sequence is the
enlargement: $`[A] = {}^*A`. -/
theorem starSet_eq_internalSet (A : Set α) : (⋆A : Set αS) = internalSet fun _ => A := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [ofSeq_mem_starSet, ofSeq_mem_internalSet]

/-- **Section 11.1, first example.** The enlargement of any set is internal. -/
theorem isInternalSet_starSet (A : Set α) : IsInternalSet α (⋆A : Set αS) :=
  ⟨_, starSet_eq_internalSet A⟩

/-- **Section 11.1, first example.** The whole star type is internal. -/
theorem isInternalSet_univ : IsInternalSet α (univ : Set αS) := by
  rw [← starSet_univ (α := α)]
  exact isInternalSet_starSet univ

/-- **Section 11.1, first example.** The empty set is internal. -/
theorem isInternalSet_empty : IsInternalSet α (∅ : Set αS) := by
  rw [← starSet_empty (α := α)]
  exact isInternalSet_starSet ∅

/-- **Section 11.1, first example.** The set of copies of the members of a finite set of
standard elements is internal, because it is the enlargement of that set. -/
theorem isInternalSet_image_of_of_finite {A : Set α} (hA : A.Finite) :
    IsInternalSet α (of '' A : Set αS) := by
  rw [← starSet_of_finite hA]
  exact isInternalSet_starSet A

/-- **Section 11.1, first example.** The set of hypernatural numbers is internal. -/
theorem isInternal_hyperNat : IsInternal ℕ* := isInternalSet_starSet _

/-- **Section 11.1, first example.** The set of hyperintegers is internal. -/
theorem isInternal_hyperInt : IsInternal ℤ* := isInternalSet_starSet _

/-- **Section 11.1, first example.** The set of hyperrationals is internal. -/
theorem isInternal_hyperRat : IsInternal ℚ* := isInternalSet_starSet _

/-- **Section 11.1, first example.** The set of all hyperreals is internal. -/
theorem isInternal_univ : IsInternal (univ : Set ℝ*) := isInternalSet_univ

/-- **Section 11.1, first example.** A finite set of real numbers, viewed as a set of
hyperreals, is internal. -/
theorem isInternal_image_coe_of_finite {A : Set ℝ} (hA : A.Finite) :
    IsInternal (((↑) : ℝ → ℝ*) '' A) :=
  isInternalSet_image_of_of_finite hA

end InternalSets

/-!
## 11.2 Algebra of Internal Sets

Intersections, unions, differences and complements of internal sets are computed termwise on
the defining sequences, so the internal sets form a Boolean algebra of sets. Inclusion and
equality of internal sets are again decided by the almost-all criterion: $`[A_n] \subseteq
[B_n]` exactly when $`A_n \subseteq B_n` for almost all $`n`. In particular the defining
sequence of an internal set may be changed at will outside a large set of indices, and the
internal sets are in bijection with the germs of set-valued sequences.
-/

section Algebra

variable {α αS : Type u} [StarType α αS]

/-- **Theorem 11.2(1).** $`[A_n] \cap [B_n] = [A_n \cap B_n]`. -/
theorem internalSet_inter (A B : ℕ → Set α) :
    (internalSet A ∩ internalSet B : Set αS) = internalSet fun n => A n ∩ B n := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_inter_iff, ofSeq_mem_internalSet, almostAll_and]

/-- **Theorem 11.2(1).** $`[A_n] \cup [B_n] = [A_n \cup B_n]`. -/
theorem internalSet_union (A B : ℕ → Set α) :
    (internalSet A ∪ internalSet B : Set αS) = internalSet fun n => A n ∪ B n := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_union, ofSeq_mem_internalSet, almostAll_or]

/-- **Theorem 11.2(1).** $`[A_n] - [B_n] = [A_n - B_n]`. -/
theorem internalSet_diff (A B : ℕ → Set α) :
    (internalSet A \ internalSet B : Set αS) = internalSet fun n => A n \ B n := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [Set.mem_sdiff, ofSeq_mem_internalSet, almostAll_and, almostAll_not]

/-- **Theorem 11.2(1).** The complement of $`[A_n]` is $`[A_n^c]`. -/
theorem internalSet_compl (A : ℕ → Set α) :
    ((internalSet A)ᶜ : Set αS) = internalSet fun n => (A n)ᶜ := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_compl_iff, ofSeq_mem_internalSet, almostAll_not]

/-- **Theorem 11.2(1).** The intersection of two internal sets is internal. -/
theorem IsInternalSet.inter {X Y : Set αS} (hX : IsInternalSet α X) (hY : IsInternalSet α Y) :
    IsInternalSet α (X ∩ Y) := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨B, rfl⟩ := hY
  exact ⟨_, internalSet_inter A B⟩

/-- **Theorem 11.2(1).** The union of two internal sets is internal. -/
theorem IsInternalSet.union {X Y : Set αS} (hX : IsInternalSet α X) (hY : IsInternalSet α Y) :
    IsInternalSet α (X ∪ Y) := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨B, rfl⟩ := hY
  exact ⟨_, internalSet_union A B⟩

/-- **Theorem 11.2(1).** The difference of two internal sets is internal. -/
theorem IsInternalSet.diff {X Y : Set αS} (hX : IsInternalSet α X) (hY : IsInternalSet α Y) :
    IsInternalSet α (X \ Y) := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨B, rfl⟩ := hY
  exact ⟨_, internalSet_diff A B⟩

/-- **Theorem 11.2(1).** The complement of an internal set is internal. -/
theorem IsInternalSet.compl {X : Set αS} (hX : IsInternalSet α X) : IsInternalSet α Xᶜ := by
  obtain ⟨A, rfl⟩ := hX
  exact ⟨_, internalSet_compl A⟩

/-- **Theorem 11.2(1).** A set is internal if and only if its complement is. -/
theorem isInternalSet_compl_iff {X : Set αS} : IsInternalSet α Xᶜ ↔ IsInternalSet α X :=
  ⟨fun h => by simpa using h.compl, IsInternalSet.compl⟩

/-- **Theorem 11.2(1).** A finite intersection of internal sets is internal. -/
theorem isInternalSet_biInter_finset {ι : Type*} (s : Finset ι) {X : ι → Set αS}
    (hX : ∀ i ∈ s, IsInternalSet α (X i)) : IsInternalSet α (⋂ i ∈ s, X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isInternalSet_univ (α := α)
  | insert a s _ ih =>
    rw [Finset.set_biInter_insert]
    exact (hX a (Finset.mem_insert_self a s)).inter
      (ih fun i hi => hX i (Finset.mem_insert_of_mem hi))

/-- **Theorem 11.2(1).** A finite union of internal sets is internal. -/
theorem isInternalSet_biUnion_finset {ι : Type*} (s : Finset ι) {X : ι → Set αS}
    (hX : ∀ i ∈ s, IsInternalSet α (X i)) : IsInternalSet α (⋃ i ∈ s, X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isInternalSet_empty (α := α)
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    exact (hX a (Finset.mem_insert_self a s)).union
      (ih fun i hi => hX i (Finset.mem_insert_of_mem hi))

/-- **Theorem 11.2(2).** $`[A_n] \subseteq [B_n]` if and only if $`A_n \subseteq B_n` for
almost all $`n`. If the inclusion of the sequences fails almost everywhere, choosing a point
of $`A_n - B_n` at each such index produces a point of $`[A_n] - [B_n]`. -/
theorem internalSet_subset_iff {A B : ℕ → Set α} :
    (internalSet A : Set αS) ⊆ internalSet B ↔ ∀ᶠ n in hyperfilter ℕ, A n ⊆ B n := by
  constructor
  · intro h
    by_contra hJ
    rw [← almostAll_not] at hJ
    have hex : ∀ᶠ n in hyperfilter ℕ, ∃ a, a ∈ A n ∧ a ∉ B n :=
      hJ.mono fun n hn => not_subset.1 hn
    obtain ⟨r, hr⟩ := exists_seq_of_almostAll_exists hex
    have h1 : (ofSeq r : αS) ∈ internalSet A :=
      ofSeq_mem_internalSet.2 (hr.mono fun n hn => hn.1)
    exact almostAll_not.1 (hr.mono fun n hn => hn.2) (ofSeq_mem_internalSet.1 (h h1))
  · intro h x hx
    obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
    exact ofSeq_mem_internalSet.2
      ((h.and (ofSeq_mem_internalSet.1 hx)).mono fun n hn => hn.1 hn.2)

/-- **Theorem 11.2(3).** $`[A_n] = [B_n]` if and only if $`A_n = B_n` for almost all $`n`.
Equality of the two sets means having the same members; that it is decided by the ultrafilter
is a theorem and not a definition. -/
theorem internalSet_eq_iff {A B : ℕ → Set α} :
    (internalSet A : Set αS) = internalSet B ↔ ∀ᶠ n in hyperfilter ℕ, A n = B n := by
  simp only [Subset.antisymm_iff, internalSet_subset_iff, almostAll_and]

/-- **Theorem 11.2(4).** $`[A_n] \ne [B_n]` if and only if $`A_n \ne B_n` for almost all
$`n`. -/
theorem internalSet_ne_iff {A B : ℕ → Set α} :
    (internalSet A : Set αS) ≠ internalSet B ↔ ∀ᶠ n in hyperfilter ℕ, A n ≠ B n := by
  rw [Ne, internalSet_eq_iff, ← almostAll_not]

/-- **Section 11.2.** Sequences of sets that agree almost everywhere define the same internal
set. -/
theorem internalSet_congr {A B : ℕ → Set α} (h : ∀ᶠ n in hyperfilter ℕ, A n = B n) :
    (internalSet A : Set αS) = internalSet B :=
  internalSet_eq_iff.2 h

/-- **Section 11.2.** $`[A_n]` is empty if and only if $`A_n` is empty for almost all
$`n`. -/
theorem internalSet_eq_empty_iff {A : ℕ → Set α} :
    (internalSet A : Set αS) = ∅ ↔ ∀ᶠ n in hyperfilter ℕ, A n = ∅ := by
  rw [← starSet_empty (α := α), starSet_eq_internalSet, internalSet_eq_iff]

/-- **Section 11.2.** $`[A_n]` is nonempty if and only if $`A_n` is nonempty for almost all
$`n`. -/
theorem internalSet_nonempty_iff {A : ℕ → Set α} :
    (internalSet A : Set αS).Nonempty ↔ ∀ᶠ n in hyperfilter ℕ, (A n).Nonempty := by
  simp only [nonempty_iff_ne_empty, Ne, internalSet_eq_empty_iff, almostAll_not]

/-- **Section 11.2.** $`[A_n] \subseteq {}^*B` if and only if $`A_n \subseteq B` for almost
all $`n`. -/
theorem internalSet_subset_starSet_iff {A : ℕ → Set α} {B : Set α} :
    (internalSet A : Set αS) ⊆ ⋆B ↔ ∀ᶠ n in hyperfilter ℕ, A n ⊆ B := by
  rw [starSet_eq_internalSet, internalSet_subset_iff]

/-- **Section 11.2, changing the defining sequence.** If almost all terms of the sequence
$`(A_n)` have a property $`P_n`, and the property can be satisfied at every index, then
$`[A_n]` is also defined by a sequence all of whose terms have the property. This is the
formal content of the phrase "we may as well assume that every $`A_n` ...". -/
theorem internalSet_exists_rep_forall {A : ℕ → Set α} {P : ℕ → Set α → Prop}
    (h : ∀ᶠ n in hyperfilter ℕ, P n (A n)) (D : ℕ → Set α) (hD : ∀ n, P n (D n)) :
    ∃ A' : ℕ → Set α, (internalSet A' : Set αS) = internalSet A ∧ ∀ n, P n (A' n) := by
  classical
  refine ⟨fun n => if P n (A n) then A n else D n,
    internalSet_eq_iff.2 (h.mono fun n hn => by simp only [hn, ↓reduceIte]), fun n => ?_⟩
  dsimp only
  split_ifs with hn
  exacts [hn, hD n]

/-- **Section 11.2, remark after the theorem.** A nonempty internal set is defined by a
sequence of nonempty sets. -/
theorem IsInternalSet.exists_rep_nonempty {X : Set αS} (hX : IsInternalSet α X)
    (hne : X.Nonempty) : ∃ A : ℕ → Set α, X = internalSet A ∧ ∀ n, (A n).Nonempty := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, -, -⟩ := mem_internalSet_iff.1 hx
  obtain ⟨A', h1, h2⟩ := internalSet_exists_rep_forall (αS := αS) (P := fun _ S => S.Nonempty)
    (internalSet_nonempty_iff.1 ⟨x, hx⟩) (fun n => {r n}) (fun n => singleton_nonempty _)
  exact ⟨A', h1.symm, h2⟩

/-- **Section 11.2, remark after the theorem.** An internal subset of an enlargement
$`{}^*B` is defined by a sequence of subsets of $`B`. -/
theorem IsInternalSet.exists_rep_subset {X : Set αS} (hX : IsInternalSet α X) {B : Set α}
    (hB : X ⊆ ⋆B) : ∃ A : ℕ → Set α, X = internalSet A ∧ ∀ n, A n ⊆ B := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨A', h1, h2⟩ := internalSet_exists_rep_forall (αS := αS) (P := fun _ S => S ⊆ B)
    (internalSet_subset_starSet_iff.1 hB) (fun _ => ∅) (fun _ => empty_subset _)
  exact ⟨A', h1.symm, h2⟩

/-- **Section 11.2, remark after the theorem.** Finitely many such conditions can be
combined: a nonempty internal subset of $`{}^*B` is defined by a sequence of nonempty subsets
of $`B`. -/
theorem IsInternalSet.exists_rep_nonempty_subset {X : Set αS} (hX : IsInternalSet α X)
    (hne : X.Nonempty) {B : Set α} (hB : X ⊆ ⋆B) :
    ∃ A : ℕ → Set α, X = internalSet A ∧ ∀ n, (A n).Nonempty ∧ A n ⊆ B := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, rfl, hr⟩ := mem_internalSet_iff.1 hx
  have hrB : ∀ᶠ n in hyperfilter ℕ, r n ∈ B := ofSeq_mem_starSet.1 (hB hx)
  obtain ⟨b, hb⟩ : B.Nonempty := by
    obtain ⟨n, hn⟩ := hrB.exists
    exact ⟨_, hn⟩
  obtain ⟨A', h1, h2⟩ := internalSet_exists_rep_forall (αS := αS)
    (P := fun _ S => S.Nonempty ∧ S ⊆ B)
    ((internalSet_nonempty_iff.1 ⟨_, hx⟩).and (internalSet_subset_starSet_iff.1 hB))
    (fun _ => {b}) (fun _ => ⟨singleton_nonempty _, singleton_subset_iff.2 hb⟩)
  exact ⟨A', h1.symm, h2⟩

/-- **Section 11.2, type-level view.** The set determined by the germ of a sequence of sets is
the internal set of that sequence. -/
theorem internalSetOfGerm_coe (A : ℕ → Set α) :
    (internalSetOfGerm (A : Germ (hyperfilter ℕ : Filter ℕ) (Set α)) : Set αS) = internalSet A :=
  rfl

/-- **Section 11.2, type-level view.** By Theorem 11.2(3), different germs of set-valued
sequences determine different sets. -/
theorem internalSetOfGerm_injective :
    Function.Injective (internalSetOfGerm : Germ (hyperfilter ℕ : Filter ℕ) (Set α) → Set αS) := by
  intro g h
  induction g using Germ.inductionOn with | _ A => ?_
  induction h using Germ.inductionOn with | _ B => ?_
  intro hAB
  exact Germ.coe_eq.2 (internalSet_eq_iff.1 hAB)

/-- **Section 11.2, type-level view.** A set is internal if and only if it is determined by a
germ of set-valued sequences. -/
theorem isInternalSet_iff_exists_germ {X : Set αS} :
    IsInternalSet α X ↔ ∃ g : Germ (hyperfilter ℕ : Filter ℕ) (Set α), internalSetOfGerm g = X := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A, rfl⟩
  · rintro ⟨g, rfl⟩
    induction g using Germ.inductionOn with | _ A => ?_
    exact ⟨A, rfl⟩

/-- **Section 11.2, type-level view.** Internal sets are the same thing as germs of
set-valued sequences along the index ultrafilter: an internal subset of the ultrapower of
$`\alpha` is an element of the ultrapower of the type of subsets of $`\alpha`. -/
noncomputable def internalSetEquiv :
    Germ (hyperfilter ℕ : Filter ℕ) (Set α) ≃ {X : Set αS // IsInternalSet α X} :=
  Equiv.ofBijective (fun g => ⟨internalSetOfGerm g, isInternalSet_iff_exists_germ.2 ⟨g, rfl⟩⟩)
    ⟨fun _ _ h => internalSetOfGerm_injective (Subtype.ext_iff.1 h), fun X => by
      obtain ⟨g, hg⟩ := isInternalSet_iff_exists_germ.1 X.2
      exact ⟨g, Subtype.ext hg⟩⟩

/-- **Section 11.2, type-level view.** The internal set attached to the germ of $`(A_n)` is
$`[A_n]`. -/
theorem internalSetEquiv_coe (A : ℕ → Set α) :
    ((internalSetEquiv (A : Germ (hyperfilter ℕ : Filter ℕ) (Set α)) :
      {X : Set αS // IsInternalSet α X}) : Set αS) = internalSet A :=
  rfl

/-- **Section 11.1, second example.** The internal set of the sequence of singletons
$`\{r_n\}` is the singleton of $`[r_n]`. -/
theorem internalSet_singleton (r : ℕ → α) :
    (internalSet (fun n => {r n}) : Set αS) = {ofSeq r} := by
  ext x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [ofSeq_mem_internalSet, mem_singleton_iff, Ultrapower.ofSeq_eq_ofSeq]

/-- **Section 11.1, second example.** Every singleton is internal. -/
theorem isInternalSet_singleton (x : αS) : IsInternalSet α ({x} : Set αS) := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  exact ⟨_, (internalSet_singleton r).symm⟩

/-- **Section 11.1, second example.** The finite set $`\{[r^1_n], \dots, [r^k_n]\}` is the
internal set $`[A_n]` with $`A_n = \{r^1_n, \dots, r^k_n\}`. -/
theorem internalSet_range_finite {ι : Type*} [Finite ι] (r : ι → ℕ → α) :
    (internalSet (fun n => range fun i => r i n) : Set αS) = range fun i => ofSeq (r i) := by
  ext x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [ofSeq_mem_internalSet, mem_range, Ultrapower.ofSeq_eq_ofSeq]
  exact almostAll_exists_finite

/-- **Section 11.1, second example.** Every finite set of elements of the star type is
internal. -/
theorem isInternalSet_of_finite {X : Set αS} (hX : X.Finite) : IsInternalSet α X := by
  induction X, hX using Set.Finite.induction_on with
  | empty => exact isInternalSet_empty
  | insert _ _ ih =>
    rw [insert_eq]
    exact (isInternalSet_singleton _).union ih

/-- **Section 11.2, subsets of internal sets.** If a set $`A` of standard elements is
internal (as a set of elements of the star type), then so is every subset $`X` of $`A`,
because $`X = A \cap {}^*X`. -/
theorem IsInternalSet.image_of_subset {A X : Set α} (hA : IsInternalSet α (of '' A : Set αS))
    (hX : X ⊆ A) : IsInternalSet α (of '' X : Set αS) := by
  have h : (of '' X : Set αS) = of '' A ∩ ⋆X := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, hX ha, rfl⟩, of_mem_starSet.2 ha⟩
    · rintro ⟨⟨a, -, rfl⟩, h⟩
      exact ⟨a, of_mem_starSet.1 h, rfl⟩
  rw [h]
  exact hA.inter (isInternalSet_starSet X)

/-- **Section 11.2, subsets of internal sets**, for the reals: if a set of real numbers is
internal then so is each of its subsets. (Section 11.7 shows that such a set must be
finite.) -/
theorem IsInternal.image_coe_subset {A X : Set ℝ} (hA : IsInternal (((↑) : ℝ → ℝ*) '' A))
    (hX : X ⊆ A) : IsInternal (((↑) : ℝ → ℝ*) '' X) :=
  IsInternalSet.image_of_subset (αS := ℝ*) hA hX

/-- **Theorem 11.2(1)**, for the hyperreals: the intersection of two internal sets is
internal. -/
theorem IsInternal.inter {X Y : Set ℝ*} (hX : IsInternal X) (hY : IsInternal Y) :
    IsInternal (X ∩ Y) :=
  IsInternalSet.inter hX hY

/-- **Theorem 11.2(1)**, for the hyperreals: the union of two internal sets is internal. -/
theorem IsInternal.union {X Y : Set ℝ*} (hX : IsInternal X) (hY : IsInternal Y) :
    IsInternal (X ∪ Y) :=
  IsInternalSet.union hX hY

/-- **Theorem 11.2(1)**, for the hyperreals: the difference of two internal sets is
internal. -/
theorem IsInternal.diff {X Y : Set ℝ*} (hX : IsInternal X) (hY : IsInternal Y) :
    IsInternal (X \ Y) :=
  IsInternalSet.diff hX hY

/-- **Theorem 11.2(1)**, for the hyperreals: the complement of an internal set is
internal. -/
theorem IsInternal.compl {X : Set ℝ*} (hX : IsInternal X) : IsInternal Xᶜ :=
  IsInternalSet.compl hX

/-- **Section 11.1, second example**, for the hyperreals: the empty set is internal. -/
theorem isInternal_empty : IsInternal (∅ : Set ℝ*) := isInternalSet_empty

/-- **Section 11.1, second example**, for the hyperreals: every singleton is internal. -/
theorem isInternal_singleton (x : ℝ*) : IsInternal ({x} : Set ℝ*) := isInternalSet_singleton x

/-- **Section 11.1, second example**, for the hyperreals: every finite set of hyperreals is
internal. -/
theorem isInternal_of_finite {X : Set ℝ*} (hX : X.Finite) : IsInternal X :=
  isInternalSet_of_finite hX

end Algebra


/-!
### Intervals and initial segments

The remaining examples of Section 11.1 are specific to the hyperreals: intervals with
arbitrary hyperreal end points, and the initial segments of the hypernaturals that will
become the model of a hyperfinite set in Chapter 12. They are placed after the Boolean algebra
because several of them are most easily obtained from it.
-/

section Intervals

/-- **Section 11.1, third example.** The open interval $`(a, b)` with $`a = [a_n]` and
$`b = [b_n]` is the internal set defined by the real intervals $`(a_n, b_n)`. -/
theorem internalSet_Ioo (a b : ℕ → ℝ) :
    internalSet (fun n => Ioo (a n) (b n)) = Ioo (Hyperreal.ofSeq a) (Hyperreal.ofSeq b) := by
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  simp only [hyperreal_ofSeq_mem_internalSet, mem_Ioo, ofSeq_lt_ofSeq_iff, almostAll_and]

/-- **Section 11.1, third example.** $`(a, b] = [(a_n, b_n]]`. -/
theorem internalSet_Ioc (a b : ℕ → ℝ) :
    internalSet (fun n => Ioc (a n) (b n)) = Ioc (Hyperreal.ofSeq a) (Hyperreal.ofSeq b) := by
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  simp only [hyperreal_ofSeq_mem_internalSet, mem_Ioc, ofSeq_lt_ofSeq_iff, ofSeq_le_ofSeq_iff,
    almostAll_and]

/-- **Section 11.1, third example.** $`[a, b) = [[a_n, b_n)]`. -/
theorem internalSet_Ico (a b : ℕ → ℝ) :
    internalSet (fun n => Ico (a n) (b n)) = Ico (Hyperreal.ofSeq a) (Hyperreal.ofSeq b) := by
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  simp only [hyperreal_ofSeq_mem_internalSet, mem_Ico, ofSeq_lt_ofSeq_iff, ofSeq_le_ofSeq_iff,
    almostAll_and]

/-- **Section 11.1, third example.** The closed interval $`[a, b]` is the internal set
defined by the real intervals $`[a_n, b_n]`. -/
theorem internalSet_Icc (a b : ℕ → ℝ) :
    internalSet (fun n => Icc (a n) (b n)) = Icc (Hyperreal.ofSeq a) (Hyperreal.ofSeq b) := by
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  simp only [hyperreal_ofSeq_mem_internalSet, mem_Icc, ofSeq_le_ofSeq_iff, almostAll_and]

/-- **Section 11.1, third example.** $`\{x : a < x\} = [(a_n, \infty)]`. -/
theorem internalSet_Ioi (a : ℕ → ℝ) :
    internalSet (fun n => Ioi (a n)) = Ioi (Hyperreal.ofSeq a) := by
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  simp only [hyperreal_ofSeq_mem_internalSet, mem_Ioi, ofSeq_lt_ofSeq_iff]

/-- **Section 11.1, third example.** $`\{x : a \le x\} = [[a_n, \infty)]`. -/
theorem internalSet_Ici (a : ℕ → ℝ) :
    internalSet (fun n => Ici (a n)) = Ici (Hyperreal.ofSeq a) := by
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  simp only [hyperreal_ofSeq_mem_internalSet, mem_Ici, ofSeq_le_ofSeq_iff]

/-- **Section 11.1, third example.** $`\{x : x < a\} = [(-\infty, a_n)]`. -/
theorem internalSet_Iio (a : ℕ → ℝ) :
    internalSet (fun n => Iio (a n)) = Iio (Hyperreal.ofSeq a) := by
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  simp only [hyperreal_ofSeq_mem_internalSet, mem_Iio, ofSeq_lt_ofSeq_iff]

/-- **Section 11.1, third example.** $`\{x : x \le a\} = [(-\infty, a_n]]`. -/
theorem internalSet_Iic (a : ℕ → ℝ) :
    internalSet (fun n => Iic (a n)) = Iic (Hyperreal.ofSeq a) := by
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  simp only [hyperreal_ofSeq_mem_internalSet, mem_Iic, ofSeq_le_ofSeq_iff]

/-- **Section 11.1, third example.** Every open hyperreal interval is internal. -/
theorem isInternal_Ioo (a b : ℝ*) : IsInternal (Ioo a b) := by
  obtain ⟨a, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨b, rfl⟩ := hyperreal_exists_rep b
  exact ⟨_, (internalSet_Ioo a b).symm⟩

/-- **Section 11.1, third example.** Every interval $`(a, b]` is internal. -/
theorem isInternal_Ioc (a b : ℝ*) : IsInternal (Ioc a b) := by
  obtain ⟨a, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨b, rfl⟩ := hyperreal_exists_rep b
  exact ⟨_, (internalSet_Ioc a b).symm⟩

/-- **Section 11.1, third example.** Every interval $`[a, b)` is internal. -/
theorem isInternal_Ico (a b : ℝ*) : IsInternal (Ico a b) := by
  obtain ⟨a, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨b, rfl⟩ := hyperreal_exists_rep b
  exact ⟨_, (internalSet_Ico a b).symm⟩

/-- **Section 11.1, third example.** Every closed hyperreal interval is internal. -/
theorem isInternal_Icc (a b : ℝ*) : IsInternal (Icc a b) := by
  obtain ⟨a, rfl⟩ := hyperreal_exists_rep a
  obtain ⟨b, rfl⟩ := hyperreal_exists_rep b
  exact ⟨_, (internalSet_Icc a b).symm⟩

/-- **Section 11.1, third example.** Every open upper ray is internal. -/
theorem isInternal_Ioi (a : ℝ*) : IsInternal (Ioi a) := by
  obtain ⟨a, rfl⟩ := hyperreal_exists_rep a
  exact ⟨_, (internalSet_Ioi a).symm⟩

/-- **Section 11.1, third example.** Every closed upper ray is internal. -/
theorem isInternal_Ici (a : ℝ*) : IsInternal (Ici a) := by
  obtain ⟨a, rfl⟩ := hyperreal_exists_rep a
  exact ⟨_, (internalSet_Ici a).symm⟩

/-- **Section 11.1, third example.** Every open lower ray is internal. -/
theorem isInternal_Iio (a : ℝ*) : IsInternal (Iio a) := by
  obtain ⟨a, rfl⟩ := hyperreal_exists_rep a
  exact ⟨_, (internalSet_Iio a).symm⟩

/-- **Section 11.1, third example.** Every closed lower ray is internal. -/
theorem isInternal_Iic (a : ℝ*) : IsInternal (Iic a) := by
  obtain ⟨a, rfl⟩ := hyperreal_exists_rep a
  exact ⟨_, (internalSet_Iic a).symm⟩

/-- **Section 11.1, third example.** A nonempty set of hyperreals that contains no real number
is not the enlargement of any set of reals, since an enlargement contains the members of the
set it enlarges. -/
theorem ne_starSet_of_nonempty_of_forall_coe_notMem {X : Set ℝ*} (hne : X.Nonempty)
    (hX : ∀ r : ℝ, (r : ℝ*) ∉ X) (A : Set ℝ) : X ≠ ⋆A := by
  rintro rfl
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · rw [starSet_empty] at hne
    exact hne.ne_empty rfl
  · exact hX a (coe_mem_starSet.2 ha)

/-- **Section 11.1, third example.** If $`a` is positive unlimited then every nonempty set of
hyperreals bounded below by $`a` is disjoint from the reals, and so is not an enlargement.
This applies to each of the internal intervals with left end point $`a` (the book says only
"unlimited", but for a negative unlimited left end point the interval may well contain
reals). -/
theorem ne_starSet_of_subset_Ici_posUnlimited {X : Set ℝ*} {a : ℝ*} (ha : PosUnlimited a)
    (hne : X.Nonempty) (hX : X ⊆ Ici a) (A : Set ℝ) : X ≠ ⋆A :=
  ne_starSet_of_nonempty_of_forall_coe_notMem hne
    (fun r hr => absurd (hX hr) (not_le.2 (ha r))) A

/-- **Section 11.1, third example.** The internal interval $`(a, b)` with $`a < b` and $`a`
positive unlimited is not the enlargement of any set of reals. -/
theorem Ioo_ne_starSet_of_posUnlimited {a b : ℝ*} (ha : PosUnlimited a) (hab : a < b)
    (A : Set ℝ) : Ioo a b ≠ ⋆A :=
  ne_starSet_of_subset_Ici_posUnlimited ha (nonempty_Ioo.2 hab) (fun _ hx => hx.1.le) A

/-- **Section 11.1, fourth example.** For a hypernatural $`N = [N_n]`, the initial segment
$`\{k \in {}^*\mathbb N : k \le N\}` is the internal set defined by the finite sets
$`\{0, 1, \dots, N_n\}`. (Lean's natural numbers start at $`0`; the book's segment
$`\{1, \dots, N\}` is {lit}`Goldblatt.setOf_hyperNat_one_le_le_eq_internalSet`.) -/
theorem setOf_hyperNat_le_eq_internalSet (N : ℕ → ℕ) :
    {k : ℝ* | k ∈ ℕ* ∧ k ≤ hnat N} =
      internalSet fun n => (((↑) : ℕ → ℝ) '' Iic (N n) : Set ℝ) := by
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [mem_ofPred_eq, hyperNat, hyperreal_ofSeq_mem_starSet, hnat, ofSeq_le_ofSeq_iff,
    hyperreal_ofSeq_mem_internalSet, ← almostAll_and]
  refine eventually_congr (Eventually.of_forall fun n => ?_)
  constructor
  · rintro ⟨⟨k, hk⟩, h⟩
    exact ⟨k, Nat.cast_le.1 (hk ▸ h), hk⟩
  · rintro ⟨k, hk, hk'⟩
    exact ⟨⟨k, hk'⟩, hk' ▸ Nat.cast_le.2 hk⟩

/-- **Section 11.1, fourth example**, in the book's numbering from $`1`: for a hypernatural
$`N = [N_n]`, the set $`\{1, 2, \dots, N\}` of hypernaturals is the internal set defined by
the finite sets $`\{1, 2, \dots, N_n\}`. -/
theorem setOf_hyperNat_one_le_le_eq_internalSet (N : ℕ → ℕ) :
    {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ hnat N} =
      internalSet fun n => (((↑) : ℕ → ℝ) '' Icc 1 (N n) : Set ℝ) := by
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  have h1 : (1 : ℝ*) = Hyperreal.ofSeq fun _ => (1 : ℝ) := rfl
  rw [mem_ofPred_eq, hyperNat, hyperreal_ofSeq_mem_starSet, hnat, ofSeq_le_ofSeq_iff, h1,
    ofSeq_le_ofSeq_iff, hyperreal_ofSeq_mem_internalSet, ← almostAll_and, ← almostAll_and]
  refine eventually_congr (Eventually.of_forall fun n => ?_)
  constructor
  · rintro ⟨⟨k, hk⟩, h, h'⟩
    refine ⟨k, ⟨?_, ?_⟩, hk⟩
    · exact_mod_cast (hk ▸ h : (1 : ℝ) ≤ k)
    · exact Nat.cast_le.1 (hk ▸ h')
  · rintro ⟨k, ⟨hk1, hk2⟩, hk'⟩
    refine ⟨⟨k, hk'⟩, ?_, hk' ▸ Nat.cast_le.2 hk2⟩
    rw [← hk']
    exact_mod_cast hk1

/-- **Section 11.1, fourth example.** For a hypernatural $`N`, the initial segment
$`\{k \in {}^*\mathbb N : k \le N\}` is internal. -/
theorem isInternal_setOf_hyperNat_le {N : ℝ*} (hN : N ∈ ℕ*) :
    IsInternal {k : ℝ* | k ∈ ℕ* ∧ k ≤ N} := by
  obtain ⟨N, rfl⟩ := exists_hnat_eq hN
  exact ⟨_, setOf_hyperNat_le_eq_internalSet N⟩

/-- **Section 11.1, fourth example.** For a hypernatural $`N`, the set $`\{1, 2, \dots, N\}`
of hypernaturals is internal. -/
theorem isInternal_setOf_hyperNat_one_le_le {N : ℝ*} (hN : N ∈ ℕ*) :
    IsInternal {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ N} := by
  obtain ⟨N, rfl⟩ := exists_hnat_eq hN
  exact ⟨_, setOf_hyperNat_one_le_le_eq_internalSet N⟩

/-- **Section 11.1, fifth example.** For a hypernatural $`N = [N_n]`, the set
$`\{k/N : k \in {}^*\mathbb N,\ k \le N\} = \{0, \tfrac1N, \tfrac2N, \dots, 1\}` is the
internal set defined by the finite sets $`\{0, \tfrac1{N_n}, \dots, 1\}`. -/
theorem setOf_div_hyperNat_eq_internalSet (N : ℕ → ℕ) :
    {x : ℝ* | ∃ k ∈ ℕ*, k ≤ hnat N ∧ x = k / hnat N} =
      internalSet fun n => ((fun k : ℕ => (k : ℝ) / N n) '' Iic (N n) : Set ℝ) := by
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [hyperreal_ofSeq_mem_internalSet]
  constructor
  · rintro ⟨k, hk, hkN, hx⟩
    obtain ⟨κ, rfl⟩ := exists_hnat_eq hk
    have hx' : Hyperreal.ofSeq r = Hyperreal.ofSeq fun n => (κ n : ℝ) / N n := hx
    exact ((hnat_le_hnat_iff.1 hkN).and (ofSeq_eq_ofSeq_iff.1 hx')).mono fun n hn =>
      ⟨κ n, hn.1, hn.2.symm⟩
  · intro h
    obtain ⟨κ, hκ⟩ := exists_seq_of_almostAll_exists h
    refine ⟨hnat κ, hnat_mem_hyperNat κ, hnat_le_hnat_iff.2 (hκ.mono fun n hn => hn.1), ?_⟩
    change Hyperreal.ofSeq r = Hyperreal.ofSeq fun n => (κ n : ℝ) / N n
    exact ofSeq_eq_ofSeq_iff.2 (hκ.mono fun n hn => hn.2.symm)

/-- **Section 11.1, fifth example.** For a hypernatural $`N`, the set
$`\{0, \tfrac1N, \tfrac2N, \dots, \tfrac{N-1}N, 1\}` is internal. -/
theorem isInternal_setOf_div_hyperNat {N : ℝ*} (hN : N ∈ ℕ*) :
    IsInternal {x : ℝ* | ∃ k ∈ ℕ*, k ≤ N ∧ x = k / N} := by
  obtain ⟨N, rfl⟩ := exists_hnat_eq hN
  exact ⟨_, setOf_div_hyperNat_eq_internalSet N⟩

/-- **Section 11.2.** The set of negatives of the members of $`[A_n]` is $`[-A_n]`. -/
theorem internalSet_neg (A : ℕ → Set ℝ) : internalSet (fun n => -A n) = -internalSet A := by
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  have h : -Hyperreal.ofSeq r = Hyperreal.ofSeq fun n => -r n := rfl
  simp only [Set.mem_neg, h, hyperreal_ofSeq_mem_internalSet]

/-- **Section 11.2.** The set of negatives of the members of an internal set is internal. -/
theorem IsInternal.neg {X : Set ℝ*} (hX : IsInternal X) : IsInternal (-X) := by
  obtain ⟨A, rfl⟩ := hX
  exact ⟨_, (internalSet_neg A).symm⟩

/-- **Section 11.2.** A translate of an internal set is internal: if $`X = [A_n]` and
$`c = [c_n]` then $`\{x : x + c \in X\}` is defined by the translates of the $`A_n`. -/
theorem IsInternal.preimage_add_right {X : Set ℝ*} (hX : IsInternal X) (c : ℝ*) :
    IsInternal {x | x + c ∈ X} := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨c, rfl⟩ := hyperreal_exists_rep c
  refine ⟨fun n => {a | a + c n ∈ A n}, ?_⟩
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  have h : Hyperreal.ofSeq r + Hyperreal.ofSeq c = Hyperreal.ofSeq fun n => r n + c n := rfl
  simp only [mem_ofPred_eq, h, hyperreal_ofSeq_mem_internalSet]

end Intervals

/-!
## 11.3 Internal Least Number Principle and Induction

Every nonempty set of natural numbers has a least member. The hypernaturals do not inherit
this property for arbitrary subsets: the unlimited hypernaturals have no least member
({name}`Goldblatt.not_exists_isLeast_unlimitedHyperNat`). They do inherit it for internal
subsets, and the least member of $`[A_n]` is the class of the sequence of least members of
the $`A_n`. The principle of induction, which for the natural numbers is equivalent to the
least number principle, survives in the same way: it holds for internal sets of
hypernaturals.
-/

section LeastNumber

/-- Every nonempty set of reals consisting of natural numbers has a least member. -/
theorem exists_isLeast_of_subset_range_natCast {S : Set ℝ} (hne : S.Nonempty)
    (hS : S ⊆ range ((↑) : ℕ → ℝ)) : ∃ m, IsLeast S m := by
  classical
  have hex : ∃ k : ℕ, (k : ℝ) ∈ S := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨k, rfl⟩ := hS hx
    exact ⟨k, hx⟩
  refine ⟨(Nat.find hex : ℕ), Nat.find_spec hex, fun x hx => ?_⟩
  obtain ⟨k, rfl⟩ := hS hx
  exact Nat.cast_le.2 (Nat.find_min' hex hx)

/-- **Theorem 11.3.1, the formula $`\min [A_n] = [\min A_n]`.** If $`r_n` is the least member
of $`A_n` for almost all $`n`, then $`[r_n]` is the least member of $`[A_n]`. -/
theorem isLeast_internalSet_ofSeq {A : ℕ → Set ℝ} {r : ℕ → ℝ}
    (h : ∀ᶠ n in hyperfilter ℕ, IsLeast (A n) (r n)) :
    IsLeast (internalSet A) (Hyperreal.ofSeq r) := by
  refine ⟨hyperreal_ofSeq_mem_internalSet.2 (h.mono fun n hn => hn.1), fun x hx => ?_⟩
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep x
  exact ofSeq_le_ofSeq_iff.2
    ((h.and (hyperreal_ofSeq_mem_internalSet.1 hx)).mono fun n hn => hn.1.2 hn.2)

/-- **Theorem 11.3.1** (internal least number principle). Every nonempty internal set of
hypernatural numbers has a least member. -/
theorem IsInternal.exists_isLeast {X : Set ℝ*} (hX : IsInternal X) (hN : X ⊆ ℕ*)
    (hne : X.Nonempty) : ∃ m, IsLeast X m := by
  obtain ⟨A, rfl⟩ := hX
  have h1 := internalSet_nonempty_iff.1 hne
  have h2 : ∀ᶠ n in hyperfilter ℕ, A n ⊆ range ((↑) : ℕ → ℝ) :=
    internalSet_subset_starSet_iff.1 hN
  have h3 : ∀ᶠ n in hyperfilter ℕ, ∃ m, IsLeast (A n) m :=
    (h1.and h2).mono fun n hn => exists_isLeast_of_subset_range_natCast hn.1 hn.2
  obtain ⟨r, hr⟩ := exists_seq_of_almostAll_exists h3
  exact ⟨_, isLeast_internalSet_ofSeq hr⟩

/-- **Theorem 11.3.2** (internal induction). An internal set of hypernaturals that contains
$`0` and is closed under the successor function is the set of all hypernaturals. Lean's
natural numbers start at $`0`, so the induction starts there; the book's form, starting at
$`1`, is {lit}`Goldblatt.IsInternal.induction_from_one`. -/
theorem IsInternal.induction {X : Set ℝ*} (hX : IsInternal X) (hN : X ⊆ ℕ*)
    (h0 : (0 : ℝ*) ∈ X) (hs : ∀ n ∈ X, n + 1 ∈ X) : X = ℕ* := by
  refine Subset.antisymm hN fun x hx => ?_
  by_contra hxX
  have hY : IsInternal (ℕ* \ X) := isInternal_hyperNat.diff hX
  obtain ⟨m, ⟨hm, hmX⟩, hmin⟩ := hY.exists_isLeast sdiff_subset ⟨x, hx, hxX⟩
  have hm0 : m ≠ 0 := fun h => hmX (h ▸ h0)
  have hm1 := sub_one_mem_hyperNat hm hm0
  have hmem : m - 1 ∈ X := by
    by_contra h
    have := hmin ⟨hm1, h⟩
    linarith
  exact hmX (by simpa using hs _ hmem)

/-- **Theorem 11.3.2** (internal induction, in the book's numbering). An internal set of
hypernaturals that contains $`1` and is closed under the successor function contains every
positive hypernatural. -/
theorem IsInternal.induction_from_one {X : Set ℝ*} (hX : IsInternal X) (hN : X ⊆ ℕ*)
    (h1 : (1 : ℝ*) ∈ X) (hs : ∀ n ∈ X, n + 1 ∈ X) {n : ℝ*} (hn : n ∈ ℕ*) (hn1 : 1 ≤ n) :
    n ∈ X := by
  have h0N : (0 : ℝ*) ∈ ℕ* := by simpa using natCast_mem_hyperNat 0
  have hX' : IsInternal (X ∪ {0}) := hX.union (isInternal_singleton 0)
  have h := hX'.induction (union_subset hN (singleton_subset_iff.2 h0N)) (Or.inr rfl)
    (by
      rintro m (hm | hm)
      · exact Or.inl (hs m hm)
      · rw [mem_singleton_iff.1 hm, zero_add]
        exact Or.inl h1)
  rw [← h] at hn
  rcases hn with hn | hn
  · exact hn
  · rw [mem_singleton_iff.1 hn] at hn1
    exact absurd hn1 (by norm_num)

end LeastNumber

/-!
## 11.4 The Overflow Principle

The set of standard natural numbers is not internal: by internal induction it would be the
set of all hypernaturals. Consequently an internal set that contains all standard natural
numbers from some point on cannot stop exactly where the standard numbers stop. The overflow
principle makes this precise: such a set contains a whole initial segment of the
hypernaturals reaching up to an unlimited number.
-/

section Overflow

/-- **Section 11.4.** The set of standard natural numbers is external: if it were internal,
internal induction would make it equal to the set of all hypernaturals, which contains the
nonstandard number $`\omega`. -/
theorem isExternal_range_natCast : IsExternal (range ((↑) : ℕ → ℝ*)) := by
  intro hX
  have h := hX.induction (by rintro _ ⟨n, rfl⟩; exact natCast_mem_hyperNat n)
    ⟨0, Nat.cast_zero⟩ (by rintro _ ⟨n, rfl⟩; exact ⟨n + 1, by push_cast; rfl⟩)
  have hω : (ω : ℝ*) ∈ range ((↑) : ℕ → ℝ*) := h ▸ omega_mem_hyperNat
  obtain ⟨n, hn⟩ := hω
  exact omega_nonstandard_nat.2 n hn.symm

/-- **Theorem 11.4.1** (overflow). Let $`X` be an internal set and $`k` a natural number. If
every standard natural number $`n \ge k` belongs to $`X`, then there is an unlimited
hypernatural $`K` such that every hypernatural $`n` with $`k \le n \le K` belongs to $`X`.
The book assumes in addition that $`X` consists of hypernaturals; the hypothesis is not
needed. -/
theorem IsInternal.overflow {X : Set ℝ*} (hX : IsInternal X) (k : ℕ)
    (h : ∀ n : ℕ, k ≤ n → (n : ℝ*) ∈ X) :
    ∃ K ∈ ℕ*, Unlimited K ∧ ∀ n ∈ ℕ*, (k : ℝ*) ≤ n → n ≤ K → n ∈ X := by
  have hY : IsInternal ((ℕ* ∩ Ioi (k : ℝ*)) \ X) :=
    (isInternal_hyperNat.inter (isInternal_Ioi _)).diff hX
  rcases ((ℕ* ∩ Ioi (k : ℝ*)) \ X).eq_empty_or_nonempty with hE | hne
  · refine ⟨ω, omega_mem_hyperNat, unlimited_omega, fun n hn hkn _ => ?_⟩
    rcases hkn.eq_or_lt with e | lt
    · rw [← e]
      exact h k le_rfl
    · by_contra hnX
      exact eq_empty_iff_forall_notMem.1 hE n ⟨⟨hn, lt⟩, hnX⟩
  · obtain ⟨H, ⟨⟨hH, hkH⟩, hHX⟩, hmin⟩ := hY.exists_isLeast (fun x hx => hx.1.1) hne
    have hHU : Unlimited H := by
      refine not_limited_iff_unlimited.1 fun hl => ?_
      obtain ⟨m, rfl⟩ := (limited_hyperNat_iff hH).1 hl
      exact hHX (h m (by exact_mod_cast (mem_Ioi.1 hkH).le))
    refine ⟨H - 1, sub_one_mem_hyperNat hH hHU.ne_zero, ?_, fun n hn hkn hnH => ?_⟩
    · rw [sub_eq_add_neg]
      exact hHU.add_limited limited_one.neg
    · rcases hkn.eq_or_lt with e | lt
      · rw [← e]
        exact h k le_rfl
      · by_contra hnX
        have := hmin ⟨⟨hn, lt⟩, hnX⟩
        linarith

/-- **Exercise 11.4.2.** The overflow principle, as a property of a class $`\mathcal C` of
sets of hyperreals: whenever a member of the class contains all standard natural numbers from
some $`k` on, it contains all hypernaturals between $`k` and some unlimited hypernatural. -/
def OverflowPrinciple (𝒞 : Set (Set ℝ*)) : Prop :=
  ∀ X ∈ 𝒞, ∀ k : ℕ, (∀ n : ℕ, k ≤ n → (n : ℝ*) ∈ X) →
    ∃ K ∈ ℕ*, Unlimited K ∧ ∀ n ∈ ℕ*, (k : ℝ*) ≤ n → n ≤ K → n ∈ X

/-- **Exercise 11.4.2.** The second statement of the exercise, as a property of a class of
sets: a member of the class that contains arbitrarily small unlimited hypernaturals contains
arbitrarily large standard natural numbers. -/
def UnboundedPrinciple (𝒞 : Set (Set ℝ*)) : Prop :=
  ∀ X ∈ 𝒞, (∀ K ∈ ℕ*, Unlimited K → ∃ H ∈ X, H ∈ ℕ* ∧ Unlimited H ∧ H ≤ K) →
    ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ (n : ℝ*) ∈ X

/-- **Exercise 11.4.2.** Overflow is equivalent to the statement that a set with arbitrarily
small unlimited members has arbitrarily large limited members. Both statements are true of
the internal sets, so to give the equivalence content it is proved for an arbitrary class of
sets closed under complementation relative to the hypernaturals, which is the only property
of the internal sets that the argument (the book's hint) uses. -/
theorem overflowPrinciple_iff_unboundedPrinciple {𝒞 : Set (Set ℝ*)}
    (h𝒞 : ∀ X ∈ 𝒞, ℕ* \ X ∈ 𝒞) : OverflowPrinciple 𝒞 ↔ UnboundedPrinciple 𝒞 := by
  constructor
  · intro hO X hX hsmall k
    by_contra hk
    push Not at hk
    obtain ⟨K, hK, hKU, hKX⟩ := hO _ (h𝒞 X hX) k
      (fun n hn => ⟨natCast_mem_hyperNat n, hk n hn⟩)
    obtain ⟨H, hHX, hH, hHU, hHK⟩ := hsmall K hK hKU
    exact (hKX H hH (posUnlimited_of_mem_hyperNat hH hHU k).le hHK).2 hHX
  · intro hU X hX k hk
    by_contra hno
    push Not at hno
    have hsmall : ∀ K ∈ ℕ*, Unlimited K → ∃ H ∈ ℕ* \ X, H ∈ ℕ* ∧ Unlimited H ∧ H ≤ K := by
      intro K hK hKU
      obtain ⟨n, hn, hkn, hnK, hnX⟩ := hno K hK hKU
      refine ⟨n, ⟨hn, hnX⟩, hn, ?_, hnK⟩
      refine not_limited_iff_unlimited.1 fun hl => ?_
      obtain ⟨m, rfl⟩ := (limited_hyperNat_iff hn).1 hl
      exact hnX (hk m (by exact_mod_cast hkn))
    obtain ⟨n, hn, hnX⟩ := hU _ (h𝒞 X hX) hsmall k
    exact hnX.2 (hk n hn)

/-- **Theorem 11.4.1**, restated: the class of internal sets has the overflow property. -/
theorem overflowPrinciple_isInternal : OverflowPrinciple {X | IsInternal X} :=
  fun _ hX k h => IsInternal.overflow hX k h

/-- **Exercise 11.4.2.** An internal set that contains arbitrarily small unlimited
hypernaturals contains arbitrarily large standard natural numbers. -/
theorem IsInternal.exists_natCast_mem_of_forall_exists_unlimited_le {X : Set ℝ*}
    (hX : IsInternal X)
    (h : ∀ K ∈ ℕ*, Unlimited K → ∃ H ∈ X, H ∈ ℕ* ∧ Unlimited H ∧ H ≤ K) (k : ℕ) :
    ∃ n : ℕ, k ≤ n ∧ (n : ℝ*) ∈ X :=
  (overflowPrinciple_iff_unboundedPrinciple (𝒞 := {X | IsInternal X})
    (fun _ hX => isInternal_hyperNat.diff hX)).1 overflowPrinciple_isInternal X hX h k

/-- **Section 11.4.** Every cofinite set of standard natural numbers is external: by overflow
an internal set containing all natural numbers from some point on has an unlimited member. -/
theorem isExternal_image_natCast_of_finite_compl {A : Set ℕ} (hA : Aᶜ.Finite) :
    IsExternal (((↑) : ℕ → ℝ*) '' A) := by
  intro hX
  obtain ⟨M, hM⟩ := hA.bddAbove
  obtain ⟨K, hKN, hKU, hK⟩ := hX.overflow (M + 1) (fun n hn => by
    refine ⟨n, ?_, rfl⟩
    by_contra hnA
    have := hM hnA
    omega)
  obtain ⟨m, -, rfl⟩ := hK K hKN (posUnlimited_of_mem_hyperNat hKN hKU _).le le_rfl
  exact hKU.not_limited (limited_natCast m)

end Overflow

/-!
## 11.5 Internal Order-Completeness

The hyperreal line is not order-complete: the set of real numbers is bounded above in it, by
any positive unlimited number, but has no least upper bound, since there is no least positive
unlimited number. Completeness does hold for internal sets, and the least upper bound of
$`[A_n]` is the class of the sequence of least upper bounds of the $`A_n`. The exercises
draw the first "spillover" consequences: an internal set cannot contain arbitrarily large
limited numbers without containing an unlimited one, and so on.
-/

section OrderCompleteness

/-- **Section 11.5.** The upper bounds of the set of real numbers in the hyperreals are
precisely the positive unlimited numbers. -/
theorem upperBounds_range_coe :
    upperBounds (range ((↑) : ℝ → ℝ*)) = {b | PosUnlimited b} := by
  ext b
  constructor
  · intro hb r
    have h1 : ((r + 1 : ℝ) : ℝ*) ≤ b := hb ⟨r + 1, rfl⟩
    exact lt_of_lt_of_le (Hyperreal.coe_lt_coe.2 (by linarith)) h1
  · rintro hb _ ⟨r, rfl⟩
    exact (hb r).le

/-- If $`b` is positive unlimited then so is $`b - 1`. -/
theorem PosUnlimited.sub_one {b : ℝ*} (hb : PosUnlimited b) : PosUnlimited (b - 1) := by
  intro r
  have h := hb (r + 1)
  rw [Hyperreal.coe_add, Hyperreal.coe_one] at h
  linarith

/-- A number that is at least a positive unlimited number is positive unlimited. -/
theorem PosUnlimited.of_le {b c : ℝ*} (hb : PosUnlimited b) (h : b ≤ c) : PosUnlimited c :=
  fun r => lt_of_lt_of_le (hb r) h

/-- A nonnegative hyperreal that is not limited is positive unlimited. -/
theorem posUnlimited_of_not_limited_of_nonneg {x : ℝ*} (hx : ¬ Limited x) (h0 : 0 ≤ x) :
    PosUnlimited x := by
  rcases not_limited_iff_unlimited.1 hx with h | h
  · exact h
  · exact absurd (by simpa using h 0) (not_lt.2 h0)

/-- A limited hyperreal is less than every positive unlimited one. -/
theorem Limited.lt_posUnlimited {x b : ℝ*} (hx : Limited x) (hb : PosUnlimited b) : x < b := by
  obtain ⟨_, s, -, hs⟩ := hx
  exact hs.trans (hb s)

/-- $`-x` is negative unlimited if and only if $`x` is positive unlimited. -/
theorem negUnlimited_neg_iff {x : ℝ*} : NegUnlimited (-x) ↔ PosUnlimited x := by
  constructor
  · intro h r
    have := h (-r)
    rw [Hyperreal.coe_neg] at this
    linarith
  · intro h r
    have := h (-r)
    rw [Hyperreal.coe_neg] at this
    linarith

/-- **Section 11.5.** The set of real numbers is a nonempty subset of the hyperreals that is
bounded above but has no least upper bound: there is no least positive unlimited number. -/
theorem not_exists_isLUB_range_coe : ¬ ∃ b, IsLUB (range ((↑) : ℝ → ℝ*)) b := by
  rintro ⟨b, hb, hmin⟩
  rw [upperBounds_range_coe] at hb hmin
  have := hmin (PosUnlimited.sub_one hb)
  linarith

/-- **Theorem 11.5.1, the key step.** $`[t_n]` is an upper bound of $`[A_n]` if and only if
$`t_n` is an upper bound of $`A_n` for almost all $`n`. -/
theorem ofSeq_mem_upperBounds_internalSet_iff {A : ℕ → Set ℝ} {t : ℕ → ℝ} :
    Hyperreal.ofSeq t ∈ upperBounds (internalSet A) ↔
      ∀ᶠ n in hyperfilter ℕ, t n ∈ upperBounds (A n) := by
  constructor
  · intro h
    by_contra hJ
    rw [← almostAll_not] at hJ
    have hex : ∀ᶠ n in hyperfilter ℕ, ∃ a, a ∈ A n ∧ t n < a :=
      hJ.mono fun n hn => by
        simp only [upperBounds, mem_ofPred_eq, not_forall, not_le] at hn
        obtain ⟨a, ha, hlt⟩ := hn
        exact ⟨a, ha, hlt⟩
    obtain ⟨a, ha⟩ := exists_seq_of_almostAll_exists hex
    have h1 : Hyperreal.ofSeq a ∈ internalSet A :=
      hyperreal_ofSeq_mem_internalSet.2 (ha.mono fun n hn => hn.1)
    have h2 : Hyperreal.ofSeq t < Hyperreal.ofSeq a :=
      ofSeq_lt_ofSeq_iff.2 (ha.mono fun n hn => hn.2)
    exact absurd (h h1) (not_le.2 h2)
  · intro h x hx
    obtain ⟨b, rfl⟩ := hyperreal_exists_rep x
    exact ofSeq_le_ofSeq_iff.2
      ((h.and (hyperreal_ofSeq_mem_internalSet.1 hx)).mono fun n hn => hn.1 hn.2)

/-- **Theorem 11.5.1, the formula $`\operatorname{lub} [A_n] = [\operatorname{lub} A_n]`.** If
$`s_n` is the least upper bound of $`A_n` for almost all $`n`, then $`[s_n]` is the least
upper bound of $`[A_n]`. -/
theorem isLUB_internalSet_ofSeq {A : ℕ → Set ℝ} {s : ℕ → ℝ}
    (h : ∀ᶠ n in hyperfilter ℕ, IsLUB (A n) (s n)) :
    IsLUB (internalSet A) (Hyperreal.ofSeq s) := by
  refine ⟨ofSeq_mem_upperBounds_internalSet_iff.2 (h.mono fun n hn => hn.1), fun x hx => ?_⟩
  obtain ⟨t, rfl⟩ := hyperreal_exists_rep x
  exact ofSeq_le_ofSeq_iff.2
    ((h.and (ofSeq_mem_upperBounds_internalSet_iff.1 hx)).mono fun n hn => hn.1.2 hn.2)

/-- **Theorem 11.5.1** (internal order-completeness, upper bounds). A nonempty internal set
of hyperreals that is bounded above has a least upper bound. The least upper bound is the
class of the sequence of suprema of the defining sets, almost all of which are nonempty and
bounded above; this is where the order-completeness of the reals is used. -/
theorem IsInternal.exists_isLUB {X : Set ℝ*} (hX : IsInternal X) (hne : X.Nonempty)
    (hb : BddAbove X) : ∃ b, IsLUB X b := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨u, hu⟩ := hb
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep u
  have h1 := internalSet_nonempty_iff.1 hne
  have h2 := ofSeq_mem_upperBounds_internalSet_iff.1 hu
  exact ⟨Hyperreal.ofSeq fun n => sSup (A n), isLUB_internalSet_ofSeq
    ((h1.and h2).mono fun n hn => isLUB_csSup hn.1 ⟨r n, hn.2⟩)⟩

/-- **Theorem 11.5.1** (internal order-completeness, lower bounds). A nonempty internal set
of hyperreals that is bounded below has a greatest lower bound. -/
theorem IsInternal.exists_isGLB {X : Set ℝ*} (hX : IsInternal X) (hne : X.Nonempty)
    (hb : BddBelow X) : ∃ b, IsGLB X b := by
  obtain ⟨b, hb'⟩ := hX.neg.exists_isLUB hne.neg (bddAbove_neg.2 hb)
  have h := (isGLB_neg (s := -X) (a := -b)).2 (by rwa [neg_neg])
  rw [neg_neg] at h
  exact ⟨-b, h⟩

/-- **Section 11.5.** A nonempty set of hyperreals that is bounded above but has no least
upper bound is external. -/
theorem isExternal_of_not_exists_isLUB {X : Set ℝ*} (hne : X.Nonempty) (hb : BddAbove X)
    (h : ¬ ∃ b, IsLUB X b) : IsExternal X :=
  fun hX => h (hX.exists_isLUB hne hb)

/-- **Exercise 11.5.2(i).** An internal set with arbitrarily large limited members has a
positive unlimited member. -/
theorem IsInternal.exists_posUnlimited_mem {X : Set ℝ*} (hX : IsInternal X)
    (h : ∀ r : ℝ, ∃ x ∈ X, Limited x ∧ (r : ℝ*) < x) : ∃ x ∈ X, PosUnlimited x := by
  by_contra hno
  push Not at hno
  have hY : IsInternal (X ∩ Ici 0) := hX.inter (isInternal_Ici 0)
  have hne : (X ∩ Ici 0).Nonempty := by
    obtain ⟨x, hx, -, h0⟩ := h 0
    exact ⟨x, hx, le_of_lt (by simpa using h0)⟩
  have hbdd : BddAbove (X ∩ Ici 0) := by
    refine ⟨ω, fun x hx => ?_⟩
    by_contra hlt
    exact hno x hx.1 (posUnlimited_omega.of_le (not_le.1 hlt).le)
  obtain ⟨b, hb⟩ := hY.exists_isLUB hne hbdd
  have hbU : PosUnlimited b := by
    intro r
    obtain ⟨x, hx, -, hrx⟩ := h (max r 0)
    have h0 : (0 : ℝ*) ≤ x := by
      have : ((0 : ℝ) : ℝ*) ≤ ((max r 0 : ℝ) : ℝ*) := Hyperreal.coe_le_coe.2 (le_max_right _ _)
      exact (this.trans hrx.le)
    have hr : (r : ℝ*) ≤ ((max r 0 : ℝ) : ℝ*) := Hyperreal.coe_le_coe.2 (le_max_left _ _)
    exact lt_of_le_of_lt hr (lt_of_lt_of_le hrx (hb.1 ⟨hx, h0⟩))
  obtain ⟨x, hx, hlt⟩ := (lt_isLUB_iff hb).1 (sub_one_lt b)
  exact hno x hx.1 (hbU.sub_one.of_le hlt.le)

/-- **Exercise 11.5.2(ii).** An internal set all of whose members are limited is contained in
an interval $`[-r, r]` with $`r` real. -/
theorem IsInternal.subset_Icc_of_forall_limited {X : Set ℝ*} (hX : IsInternal X)
    (h : ∀ x ∈ X, Limited x) : ∃ r : ℝ, X ⊆ Icc (-(r : ℝ*)) r := by
  have key : ∀ Y : Set ℝ*, IsInternal Y → (∀ x ∈ Y, Limited x) →
      ∃ r : ℝ, ∀ x ∈ Y, x ≤ (r : ℝ*) := by
    intro Y hY hlim
    by_contra hno
    push Not at hno
    obtain ⟨x, hx, hxU⟩ := hY.exists_posUnlimited_mem fun r => by
      obtain ⟨x, hx, hrx⟩ := hno r
      exact ⟨x, hx, hlim x hx, hrx⟩
    exact (hxU.unlimited).not_limited (hlim x hx)
  obtain ⟨r₁, h₁⟩ := key X hX h
  obtain ⟨r₂, h₂⟩ := key (-X) hX.neg fun x hx => by simpa using (h (-x) hx).neg
  refine ⟨max r₁ r₂, fun x hx => ⟨?_, ?_⟩⟩
  · have := h₂ (-x) (by simpa using hx)
    have hm : (r₂ : ℝ*) ≤ ((max r₁ r₂ : ℝ) : ℝ*) := Hyperreal.coe_le_coe.2 (le_max_right _ _)
    linarith
  · exact (h₁ x hx).trans (Hyperreal.coe_le_coe.2 (le_max_left _ _))

/-- **Exercises 11.5.2(iii), 11.5.2(iv) and Section 11.6, the common core.** An internal set
all of whose members are positive unlimited lies entirely above some positive unlimited
number. The greatest lower bound of the set is positive unlimited, and half of it will do. -/
theorem IsInternal.exists_posUnlimited_lt {X : Set ℝ*} (hX : IsInternal X)
    (h : ∀ x ∈ X, PosUnlimited x) : ∃ b, PosUnlimited b ∧ ∀ x ∈ X, b < x := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · exact ⟨ω, posUnlimited_omega, fun x hx => absurd hx (notMem_empty x)⟩
  · obtain ⟨c, hc⟩ := hX.exists_isGLB hne ⟨0, fun x hx => by simpa using (h x hx 0).le⟩
    have hcU : PosUnlimited c := by
      intro r
      have h1 : ((r + 1 : ℝ) : ℝ*) ≤ c := hc.2 fun x hx => (h x hx _).le
      exact lt_of_lt_of_le (Hyperreal.coe_lt_coe.2 (by linarith)) h1
    refine ⟨c / 2, hcU.div_two, fun x hx => lt_of_lt_of_le ?_ (hc.1 hx)⟩
    have : (0 : ℝ*) < c := hcU.pos
    linarith

/-- **Exercise 11.5.2(iii).** An internal set with arbitrarily small positive unlimited
members has a positive limited member. -/
theorem IsInternal.exists_pos_limited_mem {X : Set ℝ*} (hX : IsInternal X)
    (h : ∀ K, PosUnlimited K → ∃ x ∈ X, PosUnlimited x ∧ x ≤ K) :
    ∃ x ∈ X, 0 < x ∧ Limited x := by
  by_contra hno
  push Not at hno
  obtain ⟨b, hb, hlt⟩ := (hX.inter (isInternal_Ioi 0)).exists_posUnlimited_lt fun x hx =>
    posUnlimited_of_not_limited_of_nonneg (hno x hx.1 hx.2) (le_of_lt hx.2)
  obtain ⟨x, hx, hxU, hxb⟩ := h b hb
  exact absurd (hlt x ⟨hx, hxU.pos⟩) (not_lt.2 hxb)

/-- The minimum of two positive unlimited numbers is positive unlimited. -/
theorem PosUnlimited.min {b c : ℝ*} (hb : PosUnlimited b) (hc : PosUnlimited c) :
    PosUnlimited (min b c) :=
  fun r => lt_min (hb r) (hc r)

/-- **Exercise 11.5.2(iv).** An internal set with no limited members is contained in
$`\{x : x < -b \text{ or } b < x\}` for some (positive) unlimited $`b`. -/
theorem IsInternal.exists_posUnlimited_of_forall_not_limited {X : Set ℝ*} (hX : IsInternal X)
    (h : ∀ x ∈ X, ¬ Limited x) : ∃ b, PosUnlimited b ∧ X ⊆ {x | x < -b ∨ b < x} := by
  obtain ⟨b₁, hb₁, h₁⟩ := (hX.inter (isInternal_Ici 0)).exists_posUnlimited_lt fun x hx =>
    posUnlimited_of_not_limited_of_nonneg (h x hx.1) hx.2
  obtain ⟨b₂, hb₂, h₂⟩ := (hX.neg.inter (isInternal_Ici 0)).exists_posUnlimited_lt fun x hx =>
    posUnlimited_of_not_limited_of_nonneg (fun hl => h (-x) hx.1 hl.neg) hx.2
  refine ⟨min b₁ b₂, hb₁.min hb₂, fun x hx => ?_⟩
  rcases le_total 0 x with h0 | h0
  · exact Or.inr (lt_of_le_of_lt (min_le_left _ _) (h₁ x ⟨hx, h0⟩))
  · left
    have := h₂ (-x) ⟨by simpa using hx, by simpa using h0⟩
    have := min_le_right b₁ b₂
    linarith

end OrderCompleteness

/-!
## 11.6 External Sets

A set of hyperreals that is not internal is _external_. The principles of the preceding
sections are tests for externality: a nonempty set of hypernaturals without a least member, or
a nonempty bounded set of hyperreals without a least upper bound, cannot be internal. By these
tests almost every set that is defined by mentioning the standard world is external: the
standard natural numbers, the real numbers, the limited numbers, the infinitesimals, every
halo. The same arguments give sharper "spillover" statements: an internal set that contains
all limited numbers contains an interval with unlimited end points, and an internal set of
infinitesimals is contained in an interval with infinitesimal end points.
-/

section External

/-- **Section 11.6, unlimited hypernaturals.** The set of unlimited hypernaturals is
external, because it is nonempty and has no least member. -/
theorem isExternal_unlimitedHyperNat : IsExternal unlimitedHyperNat := fun hX =>
  not_exists_isLeast_unlimitedHyperNat
    (hX.exists_isLeast (fun _ hx => hx.1) ⟨ω, omega_mem_unlimitedHyperNat⟩)

/-- **Section 11.6, limited hypernaturals.** The set of standard natural numbers is external:
otherwise its complement in the hypernaturals, the set of unlimited hypernaturals, would be
internal. (The alternative proof by internal induction is
{name}`Goldblatt.isExternal_range_natCast`.) -/
theorem isExternal_range_natCast' : IsExternal (range ((↑) : ℕ → ℝ*)) := fun hX =>
  isExternal_unlimitedHyperNat (isInternal_hyperNat.diff hX)

/-- **Section 11.6.** A set of hyperreals whose hypernatural members are exactly the standard
natural numbers is external. -/
theorem isExternal_of_inter_hyperNat_eq {S : Set ℝ*} (h : S ∩ ℕ* = range ((↑) : ℕ → ℝ*)) :
    IsExternal S := fun hS =>
  isExternal_range_natCast (h ▸ hS.inter isInternal_hyperNat)

/-- **Section 11.6.** A set of hyperreals whose hypernatural members are exactly the nonzero
standard natural numbers is external. -/
theorem isExternal_of_inter_hyperNat_union_zero_eq {S : Set ℝ*}
    (h : S ∩ ℕ* ∪ {0} = range ((↑) : ℕ → ℝ*)) : IsExternal S := fun hS =>
  isExternal_range_natCast (h ▸ (hS.inter isInternal_hyperNat).union (isInternal_singleton 0))

/-- **Section 11.6, real numbers.** The set of real numbers is external: its intersection
with the hypernaturals is the set of standard natural numbers. -/
theorem isExternal_range_coe : IsExternal (range ((↑) : ℝ → ℝ*)) := by
  refine isExternal_of_inter_hyperNat_eq ?_
  ext x
  constructor
  · rintro ⟨⟨r, rfl⟩, h⟩
    obtain ⟨n, rfl⟩ := coe_mem_hyperNat_iff.1 h
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨⟨(n : ℝ), rfl⟩, natCast_mem_hyperNat n⟩

/-- **Section 11.6, real numbers, alternative proof.** The set of real numbers is external
because it is nonempty and bounded above but has no least upper bound. -/
theorem isExternal_range_coe' : IsExternal (range ((↑) : ℝ → ℝ*)) :=
  isExternal_of_not_exists_isLUB ⟨_, ⟨0, rfl⟩⟩
    ⟨ω, by rw [upperBounds_range_coe]; exact posUnlimited_omega⟩ not_exists_isLUB_range_coe

/-- **Section 11.6, limited hyperreals.** The set of limited numbers is external: it is
bounded above by every positive unlimited number but has no least upper bound. -/
theorem isExternal_limitedSet : IsExternal 𝕃 := by
  refine isExternal_of_not_exists_isLUB ⟨0, limited_zero⟩
    ⟨ω, fun x hx => (Limited.lt_posUnlimited hx posUnlimited_omega).le⟩ ?_
  rintro ⟨b, hb, hmin⟩
  have hbU : PosUnlimited b := fun r =>
    lt_of_lt_of_le (Hyperreal.coe_lt_coe.2 (lt_add_one r)) (hb (limited_coe (r + 1)))
  have := hmin fun x hx => (Limited.lt_posUnlimited hx hbU.sub_one).le
  linarith

/-- **Section 11.6, limited hyperreals.** The set of limited numbers is the intersection of
the internal intervals $`(-b, b)` over all positive unlimited $`b`. (The book writes "$`b`
unlimited"; for negative $`b` the interval is empty, so positivity is intended.) -/
theorem limitedSet_eq_iInter_Ioo : 𝕃 = ⋂ b ∈ {b : ℝ* | PosUnlimited b}, Ioo (-b) b := by
  ext x
  simp only [mem_iInter, mem_Ioo, mem_limitedSet, mem_ofPred_eq]
  constructor
  · intro hx b hb
    have h1 := hx.lt_posUnlimited hb
    have h2 := hx.neg.lt_posUnlimited hb
    exact ⟨by linarith, h1⟩
  · intro h
    by_contra hx
    have hU : PosUnlimited |x| := posUnlimited_of_not_limited_of_nonneg
      (fun hl => hx (hl.of_abs_le (abs_abs x).ge)) (abs_nonneg x)
    obtain ⟨h1, h2⟩ := h |x| hU
    rcases le_total 0 x with h0 | h0
    · rw [abs_of_nonneg h0] at h2
      exact lt_irrefl _ h2
    · rw [abs_of_nonpos h0, neg_neg] at h1
      exact lt_irrefl _ h1

/-- **Section 11.6, limited hyperreals.** The intersection of an infinite family of internal
sets can fail to be internal. -/
theorem exists_iInter_isInternal_isExternal :
    ∃ (ι : Type) (X : ι → Set ℝ*), (∀ i, IsInternal (X i)) ∧ IsExternal (⋂ i, X i) := by
  refine ⟨{b : ℝ* // PosUnlimited b}, fun b => Ioo (-(b : ℝ*)) b, fun b => isInternal_Ioo _ _, ?_⟩
  have h := isExternal_limitedSet
  rw [limitedSet_eq_iInter_Ioo, biInter_eq_iInter] at h
  exact h

/-- **Section 11.6, limited hyperreals.** An internal set that contains every limited number
contains an interval $`[-b, b]` with $`b` unlimited. -/
theorem IsInternal.exists_posUnlimited_Icc_subset {X : Set ℝ*} (hX : IsInternal X)
    (h : 𝕃 ⊆ X) : ∃ b, PosUnlimited b ∧ Icc (-b) b ⊆ X := by
  obtain ⟨b₁, hb₁, h₁⟩ := ((isInternal_Ici 0).diff hX).exists_posUnlimited_lt fun x hx =>
    posUnlimited_of_not_limited_of_nonneg (fun hl => hx.2 (h hl)) hx.1
  obtain ⟨b₂, hb₂, h₂⟩ := ((isInternal_Ici 0).diff hX.neg).exists_posUnlimited_lt fun x hx =>
    posUnlimited_of_not_limited_of_nonneg (fun hl => hx.2 (h hl.neg)) hx.1
  refine ⟨min b₁ b₂, hb₁.min hb₂, fun x hx => ?_⟩
  rcases le_total 0 x with h0 | h0
  · by_contra hxX
    have := h₁ x ⟨h0, hxX⟩
    have := min_le_left b₁ b₂
    linarith [hx.2]
  · by_contra hxX
    have := h₂ (-x) ⟨by simpa using h0, by simpa using hxX⟩
    have := min_le_right b₁ b₂
    linarith [hx.1]

/-- **Section 11.6, limited hyperreals.** An internal set that contains every limited number
is not the set of limited numbers: it has unlimited members. -/
theorem IsInternal.exists_unlimited_mem_of_limitedSet_subset {X : Set ℝ*} (hX : IsInternal X)
    (h : 𝕃 ⊆ X) : ∃ x ∈ X, Unlimited x := by
  obtain ⟨b, hb, hsub⟩ := hX.exists_posUnlimited_Icc_subset h
  exact ⟨b, hsub ⟨by linarith [hb.pos], le_rfl⟩, hb.unlimited⟩

/-- **Section 11.6, infinitesimals.** The least upper bound of a nonempty internal set of
infinitesimals is infinitesimal. -/
theorem infinitesimal_of_isLUB {X : Set ℝ*} (h : ∀ x ∈ X, Infinitesimal x) (hne : X.Nonempty)
    {b : ℝ*} (hb : IsLUB X b) : Infinitesimal b := by
  rw [infinitesimal_iff_abs_lt]
  intro r hr
  obtain ⟨x₀, hx₀⟩ := hne
  have h1 := abs_lt.1 (infinitesimal_iff_abs_lt.1 (h x₀ hx₀) r hr)
  have h2 : b ≤ ((r / 2 : ℝ) : ℝ*) := hb.2 fun x hx =>
    (abs_lt.1 (infinitesimal_iff_abs_lt.1 (h x hx) (r / 2) (by linarith))).2.le
  have h3 : ((r / 2 : ℝ) : ℝ*) < (r : ℝ*) := Hyperreal.coe_lt_coe.2 (by linarith)
  exact abs_lt.2 ⟨lt_of_lt_of_le h1.1 (hb.1 hx₀), lt_of_le_of_lt h2 h3⟩

/-- **Section 11.6, infinitesimals.** The greatest lower bound of a nonempty internal set of
infinitesimals is infinitesimal. -/
theorem infinitesimal_of_isGLB {X : Set ℝ*} (h : ∀ x ∈ X, Infinitesimal x) (hne : X.Nonempty)
    {a : ℝ*} (ha : IsGLB X a) : Infinitesimal a := by
  rw [infinitesimal_iff_abs_lt]
  intro r hr
  obtain ⟨x₀, hx₀⟩ := hne
  have h1 := abs_lt.1 (infinitesimal_iff_abs_lt.1 (h x₀ hx₀) r hr)
  have h2 : ((-(r / 2) : ℝ) : ℝ*) ≤ a := ha.2 fun x hx => by
    have := (abs_lt.1 (infinitesimal_iff_abs_lt.1 (h x hx) (r / 2) (by linarith))).1
    rw [Hyperreal.coe_neg]
    exact this.le
  have h3 : ((-r : ℝ) : ℝ*) < ((-(r / 2) : ℝ) : ℝ*) := Hyperreal.coe_lt_coe.2 (by linarith)
  rw [Hyperreal.coe_neg] at h3
  exact abs_lt.2 ⟨lt_of_lt_of_le h3 h2, lt_of_le_of_lt (ha.1 hx₀) h1.2⟩

/-- **Section 11.6, infinitesimals.** An internal set of infinitesimals is contained in an
interval $`[-c, c]` with $`c` infinitesimal. -/
theorem IsInternal.subset_Icc_of_forall_infinitesimal {X : Set ℝ*} (hX : IsInternal X)
    (h : ∀ x ∈ X, Infinitesimal x) : ∃ c, Infinitesimal c ∧ 0 ≤ c ∧ X ⊆ Icc (-c) c := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, infinitesimal_zero, le_rfl, empty_subset _⟩
  · have hlt : ∀ x ∈ X, -1 < x ∧ x < 1 := fun x hx => by
      have := abs_lt.1 (infinitesimal_iff_abs_lt.1 (h x hx) 1 one_pos)
      simpa using this
    obtain ⟨b, hb⟩ := hX.exists_isLUB hne ⟨1, fun x hx => (hlt x hx).2.le⟩
    obtain ⟨a, ha⟩ := hX.exists_isGLB hne ⟨-1, fun x hx => (hlt x hx).1.le⟩
    have hbI := infinitesimal_of_isLUB h hne hb
    have haI := infinitesimal_of_isGLB h hne ha
    refine ⟨|a| + |b|, (haI.of_abs_le (abs_abs a).le).add (hbI.of_abs_le (abs_abs b).le),
      add_nonneg (abs_nonneg a) (abs_nonneg b), fun x hx => ⟨?_, ?_⟩⟩
    · have := ha.1 hx
      have := neg_abs_le a
      have := abs_nonneg b
      linarith
    · have := hb.1 hx
      have := le_abs_self b
      have := abs_nonneg a
      linarith

/-- **Section 11.6, infinitesimals.** The set of infinitesimals is external. If it were
internal it would lie in an interval $`[-c, c]` with $`c` infinitesimal, but $`c +
\varepsilon` is an infinitesimal outside that interval. -/
theorem isExternal_infinitesimalSet : IsExternal 𝕀 := by
  intro hX
  obtain ⟨c, hc, -, hsub⟩ := hX.subset_Icc_of_forall_infinitesimal fun _ hx => hx
  have := (hsub (hc.add infinitesimal_epsilon : c + ε ∈ 𝕀)).2
  linarith [epsilon_pos_infinitesimal.1]

/-- **Section 11.6, infinitesimals.** The set of positive infinitesimals is external. -/
theorem isExternal_setOf_pos_infinitesimal : IsExternal {x : ℝ* | 0 < x ∧ Infinitesimal x} := by
  intro hX
  obtain ⟨c, hc, hc0, hsub⟩ := hX.subset_Icc_of_forall_infinitesimal fun _ hx => hx.2
  have h0 := epsilon_pos_infinitesimal.1
  have := (hsub ⟨by linarith, hc.add infinitesimal_epsilon⟩ : c + ε ∈ Icc (-c) c).2
  linarith

/-- **Section 11.6, infinitesimals.** The set of negative infinitesimals is external. -/
theorem isExternal_setOf_neg_infinitesimal : IsExternal {x : ℝ* | x < 0 ∧ Infinitesimal x} := by
  intro hX
  obtain ⟨c, hc, hc0, hsub⟩ := hX.subset_Icc_of_forall_infinitesimal fun _ hx => hx.2
  have h0 := epsilon_pos_infinitesimal.1
  have := (hsub ⟨by linarith, (hc.add infinitesimal_epsilon).neg⟩ : -(c + ε) ∈ Icc (-c) c).1
  linarith

/-- $`x + b` lies in the halo of $`b` if and only if $`x` is infinitesimal. -/
theorem add_mem_hal_iff {x b : ℝ*} : x + b ∈ hal b ↔ Infinitesimal x := by
  rw [mem_hal, infClose_iff, show b - (x + b) = -x by ring, infinitesimal_neg_iff]

/-- **Section 11.6, infinitesimals.** Every halo is external. The halo of $`b` is a translate
of the set of infinitesimals, and translates of internal sets are internal. -/
theorem isExternal_hal (b : ℝ*) : IsExternal (hal b) := by
  intro hX
  refine isExternal_infinitesimalSet ?_
  have h := hX.preimage_add_right b
  have e : {x | x + b ∈ hal b} = 𝕀 := by
    ext x
    exact add_mem_hal_iff
  rwa [e] at h

/-- **Section 11.6, infinitesimals.** The right half $`\{x > b : x \simeq b\}` of a halo is
external. -/
theorem isExternal_hal_inter_Ioi (b : ℝ*) : IsExternal (hal b ∩ Ioi b) := by
  intro hX
  refine isExternal_setOf_pos_infinitesimal ?_
  have h := hX.preimage_add_right b
  have e : {x | x + b ∈ hal b ∩ Ioi b} = {x : ℝ* | 0 < x ∧ Infinitesimal x} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, add_mem_hal_iff, mem_Ioi, lt_add_iff_pos_left]
    exact and_comm
  rwa [e] at h

/-- **Section 11.6, infinitesimals.** The left half $`\{x < b : x \simeq b\}` of a halo is
external. -/
theorem isExternal_hal_inter_Iio (b : ℝ*) : IsExternal (hal b ∩ Iio b) := by
  intro hX
  refine isExternal_setOf_neg_infinitesimal ?_
  have h := hX.preimage_add_right b
  have e : {x | x + b ∈ hal b ∩ Iio b} = {x : ℝ* | x < 0 ∧ Infinitesimal x} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, add_mem_hal_iff, mem_Iio, add_lt_iff_neg_right]
    exact and_comm
  rwa [e] at h

/-- **Exercise 11.6.1.** The set of positive real numbers is external. -/
theorem isExternal_image_coe_Ioi_zero : IsExternal (((↑) : ℝ → ℝ*) '' Ioi 0) := by
  refine isExternal_of_inter_hyperNat_union_zero_eq ?_
  ext x
  constructor
  · rintro (⟨⟨r, -, rfl⟩, h⟩ | h)
    · obtain ⟨n, rfl⟩ := coe_mem_hyperNat_iff.1 h
      exact ⟨n, rfl⟩
    · exact ⟨0, by rw [mem_singleton_iff.1 h, Nat.cast_zero]⟩
  · rintro ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inr (by simp)
    · exact Or.inl ⟨⟨(n : ℝ), by simpa using hn, rfl⟩, natCast_mem_hyperNat n⟩

/-- **Exercise 11.6.1.** The set of integers is external. -/
theorem isExternal_range_intCast : IsExternal (range ((↑) : ℤ → ℝ*)) := by
  refine isExternal_of_inter_hyperNat_eq ?_
  ext x
  constructor
  · rintro ⟨⟨z, rfl⟩, h⟩
    have hz : (0 : ℤ) ≤ z := by exact_mod_cast hyperNat_nonneg h
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    exact ⟨n, by simp⟩
  · rintro ⟨n, rfl⟩
    exact ⟨⟨(n : ℤ), by simp⟩, natCast_mem_hyperNat n⟩

/-- **Exercise 11.6.1.** The set of rational numbers is external. -/
theorem isExternal_range_ratCast : IsExternal (range fun q : ℚ => ((q : ℝ) : ℝ*)) := by
  refine isExternal_of_inter_hyperNat_eq ?_
  ext x
  constructor
  · rintro ⟨⟨q, rfl⟩, h⟩
    obtain ⟨n, hn⟩ := coe_mem_hyperNat_iff.1 h
    exact ⟨n, by change (n : ℝ*) = ((q : ℝ) : ℝ*); rw [← hn]; rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨⟨(n : ℚ), by change (((n : ℚ) : ℝ) : ℝ*) = (n : ℝ*); rw [Rat.cast_natCast]; rfl⟩,
      natCast_mem_hyperNat n⟩

/-- **Exercise 11.6.1.** The set of unlimited hyperreals is external: it is the complement of
the set of limited numbers. -/
theorem isExternal_setOf_unlimited : IsExternal {x : ℝ* | Unlimited x} := by
  intro hX
  refine isExternal_limitedSet ?_
  have h := hX.compl
  have e : {x : ℝ* | Unlimited x}ᶜ = 𝕃 := by
    ext x
    simp only [mem_compl_iff, mem_ofPred_eq, mem_limitedSet, ← not_limited_iff_unlimited,
      not_not]
  rwa [e] at h

/-- **Exercise 11.6.1.** The set of positive unlimited hyperreals is external: its
hypernatural members are the unlimited hypernaturals. -/
theorem isExternal_setOf_posUnlimited : IsExternal {x : ℝ* | PosUnlimited x} := by
  intro hX
  refine isExternal_unlimitedHyperNat ?_
  have h := hX.inter isInternal_hyperNat
  have e : {x : ℝ* | PosUnlimited x} ∩ ℕ* = unlimitedHyperNat := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact mem_unlimitedHyperNat.2 ⟨h2, Or.inl h1⟩
    · intro hx
      obtain ⟨hN, hU⟩ := mem_unlimitedHyperNat.1 hx
      exact ⟨posUnlimited_of_mem_hyperNat hN hU, hN⟩
  rwa [e] at h

/-- **Exercise 11.6.1.** The set of negative unlimited hyperreals is external. -/
theorem isExternal_setOf_negUnlimited : IsExternal {x : ℝ* | NegUnlimited x} := by
  intro hX
  refine isExternal_setOf_posUnlimited ?_
  have h := hX.neg
  have e : -{x : ℝ* | NegUnlimited x} = {x : ℝ* | PosUnlimited x} := by
    ext x
    simp only [Set.mem_neg, mem_ofPred_eq, negUnlimited_neg_iff]
  rwa [e] at h

/-- **Exercise 11.6.1.** The set of appreciable hyperreals is external: its hypernatural
members are the nonzero standard natural numbers. -/
theorem isExternal_setOf_appreciable : IsExternal {x : ℝ* | Appreciable x} := by
  refine isExternal_of_inter_hyperNat_union_zero_eq ?_
  ext x
  constructor
  · rintro (⟨h1, h2⟩ | h)
    · obtain ⟨n, rfl⟩ := (limited_hyperNat_iff h2).1 h1.limited
      exact ⟨n, rfl⟩
    · exact ⟨0, by rw [mem_singleton_iff.1 h, Nat.cast_zero]⟩
  · rintro ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inr (by simp)
    · exact Or.inl ⟨appreciable_coe (r := (n : ℝ)) (Nat.cast_ne_zero.2 hn.ne'),
        natCast_mem_hyperNat n⟩

end External

end Goldblatt
