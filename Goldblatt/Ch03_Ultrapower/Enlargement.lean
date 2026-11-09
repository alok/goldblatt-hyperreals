import Goldblatt.Ch03_Ultrapower.Construction

/-!
# 3 (part 2). Enlargement of Sets: Sections 3.9 and 3.10

This is the second of three parts of Chapter 3 (the overview is on the chapter page
{lit}`Goldblatt.Ch03_Ultrapower`). It defines the enlargement of a set, introduces the star
notation, proves that exactly the infinite sets acquire nonstandard members, and works through
the exercises on enlargements, including the enlarged number systems.
-/

universe u v w

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## 3.9 Enlarging Sets

A set $`A` of standard elements is enlarged to a set $`{}^*A` of elements of the ultrapower by
the almost-all criterion: the class of a sequence belongs to $`{}^*A` when almost all of its
terms belong to $`A`. The enlargement contains (the copies of) the members of $`A`, and its
other members are the _nonstandard_ members of $`A`. Theorem 3.9.1 says that an infinite set
always has nonstandard members; with Exercise 3.10(1) this characterizes the infinite sets.

Everything is done for subsets of an arbitrary type $`\alpha`; the book's case is
$`\alpha = \mathbb R`, where the ultrapower is the type of hyperreals.
-/

section Enlargement

variable {α αS : Type u} {β βS : Type v} {γ γS : Type w}
  [StarType α αS] [StarType β βS] [StarType γ γS]

/-- **Section 3.9.** The statement value $`[\![ r \in A ]\!] = \{n : r_n \in A\}`. -/
def memSet (r : ℕ → α) (A : Set α) : Set ℕ := {n | r n ∈ A}

/-- **Section 3.9, well-definedness of enlargement.**
$`[\![ r = r' ]\!] \cap [\![ r \in A ]\!] \subseteq [\![ r' \in A ]\!]`. -/
theorem agreementSet_inter_memSet_subset (r r' : ℕ → α) (A : Set α) :
    agreementSet r r' ∩ memSet r A ⊆ memSet r' A := by
  rintro n ⟨h₁, h₂⟩
  simp only [agreementSet, memSet, mem_ofPred_eq] at h₁ h₂ ⊢
  rwa [← h₁]

/-- **Section 3.9, well-definedness of enlargement.** If $`r \equiv r'` and
$`[\![ r \in A ]\!]` is large, then $`[\![ r' \in A ]\!]` is large. -/
theorem memSet_mem_hyperfilter_of_seqEquiv {r r' : ℕ → α} {A : Set α} (h : r ≡ᵤ r')
    (hA : memSet r A ∈ hyperfilter ℕ) : memSet r' A ∈ hyperfilter ℕ :=
  mem_hyperfilter_of_superset (inter_mem_hyperfilter_iff.2 ⟨h, hA⟩)
    (agreementSet_inter_memSet_subset r r' A)

/-- **Section 3.9.** The _enlargement_ $`{}^*A` of a set $`A`: the class of a sequence $`r`
belongs to it when $`r_n \in A` for almost all $`n`. Written {lit}`⋆A`. -/
def starSet (A : Set α) : Set αS := {x | Germ.LiftPred (· ∈ A) (StarType.equiv x)}

/-- **Section 3.11.** The _extension_ $`{}^*f` of a function $`f`, acting on classes of
sequences termwise: $`{}^*f([r]) = [f \circ r]`. Written {lit}`⋆f`. -/
noncomputable def starMap (f : α → β) : αS → βS :=
  fun x => StarType.equiv.symm (Germ.map f (StarType.equiv x))

/-- **Exercise 3.12(5).** The extension of a function of two arguments, acting termwise:
$`{}^*f([r], [s]) = [f(r_n, s_n)]`. Written {lit}`⋆f`. -/
noncomputable def starMap₂ (f : α → β → γ) : αS → βS → γS :=
  fun x y => StarType.equiv.symm (Germ.map₂ f (StarType.equiv x) (StarType.equiv y))

/-- **Section 3.14.** The enlargement $`{}^*P` of a binary relation $`P`: it holds of
$`[r], [s]` when $`P(r_n, s_n)` for almost all $`n`. Written {lit}`⋆P`. -/
def starRel₂ (P : α → β → Prop) : αS → βS → Prop :=
  fun x y => Germ.LiftRel P (StarType.equiv x) (StarType.equiv y)

/-- The book's prefix star. Applied to a set it is the enlargement {lit}`starSet`; applied to a
function of one argument it is the extension {lit}`starMap`; applied to a function of two
arguments it is {lit}`starMap₂`; applied to a binary relation it is {lit}`starRel₂`. -/
scoped syntax:max "⋆" term:max : term

open Lean Elab Term Meta in
elab_rules : term
  | `(⋆ $x) => do
    let e ← withSynthesize (postpone := .partial) (elabTerm x none)
    let t ← whnfR (← instantiateMVars (← inferType e))
    let stx ← exprToSyntax e
    if t.isAppOf ``Set then
      elabTerm (← `(Goldblatt.starSet $stx)) none
    else
      let (n, isProp) ← withReducible <| forallTelescopeReducing t fun xs body =>
        return (xs.size, body.isProp)
      match n, isProp with
      | 1, false => elabTerm (← `(Goldblatt.starMap $stx)) none
      | 2, false => elabTerm (← `(Goldblatt.starMap₂ $stx)) none
      | 2, true => elabTerm (← `(Goldblatt.starRel₂ $stx)) none
      | _, _ => throwError "⋆: expected a set, a function of one or two arguments, or a \
          binary relation, but{indentExpr e}\nhas type{indentExpr t}"

/-- Display {lit}`starSet A` as {lit}`⋆A`. -/
@[app_unexpander Goldblatt.starSet]
def unexpandStarSet : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `(⋆ $A)
  | _ => throw ()

/-- Display {lit}`starMap f` as {lit}`⋆f`. -/
@[app_unexpander Goldblatt.starMap]
def unexpandStarMap : Lean.PrettyPrinter.Unexpander
  | `($_ $f) => `(⋆ $f)
  | `($_ $f $x) => `(⋆ $f $x)
  | _ => throw ()

/-- Display {lit}`starMap₂ f` as {lit}`⋆f`. -/
@[app_unexpander Goldblatt.starMap₂]
def unexpandStarMap₂ : Lean.PrettyPrinter.Unexpander
  | `($_ $f) => `(⋆ $f)
  | `($_ $f $x) => `(⋆ $f $x)
  | `($_ $f $x $y) => `(⋆ $f $x $y)
  | _ => throw ()

/-- Display {lit}`starRel₂ P` as {lit}`⋆P`. -/
@[app_unexpander Goldblatt.starRel₂]
def unexpandStarRel₂ : Lean.PrettyPrinter.Unexpander
  | `($_ $f) => `(⋆ $f)
  | `($_ $f $x) => `(⋆ $f $x)
  | `($_ $f $x $y) => `(⋆ $f $x $y)
  | _ => throw ()

/-- **Section 3.9, almost-all criterion for membership.** $`[r] \in {}^*A` if and only if
$`r_n \in A` for almost all $`n`. -/
theorem ofSeq_mem_starSet {r : ℕ → α} {A : Set α} :
    (ofSeq r : αS) ∈ ⋆A ↔ ∀ᶠ n in hyperfilter ℕ, r n ∈ A := by
  change Germ.LiftPred (· ∈ A) (StarType.equiv (ofSeq r : αS)) ↔ _
  rw [equiv_ofSeq]
  exact Germ.liftPred_coe

/-- **Section 3.9.** $`[r] \in {}^*A` if and only if the statement value $`[\![ r \in A ]\!]`
is large. -/
theorem ofSeq_mem_starSet_iff_memSet {r : ℕ → α} {A : Set α} :
    (ofSeq r : αS) ∈ ⋆A ↔ memSet r A ∈ hyperfilter ℕ :=
  ofSeq_mem_starSet

/-- **Section 3.9**, for the reals: a hyperreal $`[r]` belongs to $`{}^*A` if and only if
$`r_n \in A` for almost all $`n`. -/
theorem hyperreal_ofSeq_mem_starSet {r : ℕ → ℝ} {A : Set ℝ} :
    Hyperreal.ofSeq r ∈ ⋆A ↔ ∀ᶠ n in hyperfilter ℕ, r n ∈ A :=
  ofSeq_mem_starSet

/-- **Section 3.9.** A class does not belong to $`{}^*A` if and only if almost all terms of the
sequence lie outside $`A`. -/
theorem ofSeq_notMem_starSet {r : ℕ → α} {A : Set α} :
    (ofSeq r : αS) ∉ ⋆A ↔ ∀ᶠ n in hyperfilter ℕ, r n ∉ A := by
  rw [ofSeq_mem_starSet, almostAll_not]

/-- **Section 3.9, and Exercise 3.10(5).** For a standard element $`a`, $`{}^*a \in {}^*A` if
and only if $`a \in A`. So the enlargement contains $`A` and adds no new standard
elements. -/
theorem of_mem_starSet {a : α} {A : Set α} : (of a : αS) ∈ ⋆A ↔ a ∈ A := by
  rw [of_eq_ofSeq, ofSeq_mem_starSet, almostAll_const]

/-- **Section 3.9**, for the reals: a real number belongs to $`{}^*A` if and only if it
belongs to $`A`. -/
theorem coe_mem_starSet {a : ℝ} {A : Set ℝ} : (a : ℝ*) ∈ ⋆A ↔ a ∈ A :=
  of_mem_starSet

/-- **Section 3.9.** $`A \subseteq {}^*A`, after identifying a standard element with its
copy. -/
theorem image_of_subset_starSet (A : Set α) : (of '' A : Set αS) ⊆ ⋆A := by
  rintro _ ⟨a, ha, rfl⟩
  exact of_mem_starSet.2 ha

/-- **Theorem 3.9.1.** Any infinite set has nonstandard members: if $`A` is infinite there is
an element of $`{}^*A` that is not the copy of any standard element. The witness is the class
of a sequence of distinct elements of $`A`. -/
theorem exists_nonstandard_mem_starSet {A : Set α} (hA : A.Infinite) :
    ∃ x ∈ ⋆A, x ∉ range (of : α → αS) := by
  have : Infinite A := hA.to_subtype
  let e : ℕ ↪ A := Infinite.natEmbedding A
  refine ⟨ofSeq fun n => (e n : α), ofSeq_mem_starSet.2 (Eventually.of_forall fun n => (e n).2),
    ?_⟩
  rintro ⟨a, ha⟩
  have h : ∀ᶠ n in hyperfilter ℕ, (e n : α) = a := ofSeq_eq_of.1 ha.symm
  refine notMem_hyperfilter_of_finite (Set.Subsingleton.finite ?_) h
  intro m hm n hn
  exact e.injective (Subtype.ext (hm.trans hn.symm))

/-- **Theorem 3.9.1**, for the reals: an infinite set of real numbers has a nonstandard member,
a hyperreal in its enlargement that is not a real number. -/
theorem exists_nonstandard_mem_starSet_real {A : Set ℝ} (hA : A.Infinite) :
    ∃ x : ℝ*, x ∈ ⋆A ∧ x ∉ range ((↑) : ℝ → ℝ*) :=
  exists_nonstandard_mem_starSet hA

/-!
## 3.10 Exercises on Enlargement

Enlargement commutes with the finite Boolean operations, is injective and monotone, fixes
finite sets, and turns real intervals into the hyperreal intervals with the same endpoints.
It does not commute with countable unions: the union of the enlargements of the singletons of
natural numbers is just the set of standard naturals, while the enlargement of their union
contains $`\omega`.
-/

/-- **Exercise 3.10(1).** If $`A` is finite then $`{}^*A = A`: an almost-everywhere member of a
finite set is almost everywhere equal to one of its elements, since an ultrafilter that contains
a finite union contains one of its members. -/
theorem starSet_of_finite {A : Set α} (hA : A.Finite) : (⋆A : Set αS) = of '' A := by
  refine Subset.antisymm (fun x hx => ?_) (image_of_subset_starSet A)
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  have h : (⋃ a ∈ A, {n | r n = a}) ∈ hyperfilter ℕ :=
    mem_hyperfilter_of_superset (ofSeq_mem_starSet.1 hx) fun n hn => mem_biUnion hn rfl
  obtain ⟨a, ha, h'⟩ := (Ultrafilter.finite_biUnion_mem_iff hA).1 h
  exact ⟨a, ha, (ofSeq_eq_of.2 h').symm⟩

/-- **Exercise 3.10(1).** A finite set has no nonstandard members. -/
theorem mem_range_of_of_mem_starSet_of_finite {A : Set α} (hA : A.Finite) {x : αS}
    (hx : x ∈ ⋆A) : x ∈ range (of : α → αS) := by
  rw [starSet_of_finite hA] at hx
  exact image_subset_range _ _ hx

/-- **Theorem 3.9.1 and its converse.** A set is infinite if and only if it has a nonstandard
member. -/
theorem infinite_iff_exists_nonstandard_mem {A : Set α} :
    A.Infinite ↔ ∃ x ∈ ⋆A, x ∉ range (of : α → αS) :=
  ⟨exists_nonstandard_mem_starSet, fun ⟨_, hx, hx'⟩ hfin =>
    hx' (mem_range_of_of_mem_starSet_of_finite hfin hx)⟩

/-- **Exercise 3.10(1) and its converse.** A set is finite if and only if its enlargement
consists of the copies of its elements. -/
theorem finite_iff_starSet_eq_image {A : Set α} : A.Finite ↔ (⋆A : Set αS) = of '' A := by
  refine ⟨starSet_of_finite, fun h => by_contra fun hinf => ?_⟩
  obtain ⟨x, hx, hx'⟩ := exists_nonstandard_mem_starSet hinf
  rw [h] at hx
  exact hx' (image_subset_range _ _ hx)

/-- **Exercise 3.10(1).** The enlargement of a singleton is the singleton of the copy. -/
theorem starSet_singleton (a : α) : (⋆({a} : Set α) : Set αS) = {of a} := by
  rw [starSet_of_finite (finite_singleton a), image_singleton]

/-- **Exercise 3.10(1)**, for the reals: the enlargement of a finite set of real numbers is the
same set, regarded as a set of hyperreals. -/
theorem starSet_of_finite_real {A : Set ℝ} (hA : A.Finite) : ⋆A = ((↑) : ℝ → ℝ*) '' A :=
  starSet_of_finite hA

/-- **Exercise 3.10(1)**, for the reals: the enlargement of a singleton is the same
singleton. -/
theorem starSet_singleton_real (a : ℝ) : ⋆({a} : Set ℝ) = {(a : ℝ*)} :=
  starSet_singleton a

/-- **Exercise 3.10(2).** $`A \subseteq B` if and only if $`{}^*A \subseteq {}^*B`. -/
theorem starSet_subset_starSet {A B : Set α} : (⋆A : Set αS) ⊆ ⋆B ↔ A ⊆ B := by
  refine ⟨fun h a ha => of_mem_starSet.1 (h (of_mem_starSet.2 ha)), fun h x hx => ?_⟩
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  exact ofSeq_mem_starSet.2 ((ofSeq_mem_starSet.1 hx).mono fun n hn => h hn)

/-- **Exercise 3.10(2).** Enlargement is monotone. -/
theorem starSet_mono {A B : Set α} (h : A ⊆ B) : (⋆A : Set αS) ⊆ ⋆B :=
  starSet_subset_starSet.2 h

/-- **Exercise 3.10(2).** $`A = B` if and only if $`{}^*A = {}^*B`. -/
theorem starSet_inj {A B : Set α} : (⋆A : Set αS) = ⋆B ↔ A = B := by
  simp only [Subset.antisymm_iff, starSet_subset_starSet]

/-- **Exercise 3.10(3).** $`{}^*(A \cup B) = {}^*A \cup {}^*B`. This uses the ultrafilter
property. -/
theorem starSet_union (A B : Set α) : (⋆(A ∪ B) : Set αS) = ⋆A ∪ ⋆B := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_union, ofSeq_mem_starSet, almostAll_or]

/-- **Exercise 3.10(3).** $`{}^*(A \cap B) = {}^*A \cap {}^*B`. -/
theorem starSet_inter (A B : Set α) : (⋆(A ∩ B) : Set αS) = ⋆A ∩ ⋆B := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_inter_iff, ofSeq_mem_starSet, almostAll_and]

/-- **Exercise 3.10(3).** The enlargement of a complement is the complement of the
enlargement. -/
theorem starSet_compl (A : Set α) : (⋆(Aᶜ) : Set αS) = (⋆A)ᶜ := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_compl_iff, ofSeq_mem_starSet, almostAll_not]

/-- **Exercise 3.10(3).** $`{}^*(A - B) = {}^*A - {}^*B`. -/
theorem starSet_diff (A B : Set α) : (⋆(A \ B) : Set αS) = ⋆A \ ⋆B := by
  rw [sdiff_eq, starSet_inter, starSet_compl, sdiff_eq]

/-- **Exercise 3.10(3).** $`{}^*\emptyset = \emptyset`. -/
theorem starSet_empty : (⋆(∅ : Set α) : Set αS) = ∅ := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [ofSeq_mem_starSet, mem_empty_iff_false, eventually_false_iff_eq_bot,
    iff_false]
  exact (hyperfilter ℕ).neBot.ne

/-- **Exercise 3.10(3).** The enlargement of the whole type is the whole ultrapower. -/
theorem starSet_univ : (⋆(univ : Set α) : Set αS) = univ := by
  rw [← compl_empty, starSet_compl, starSet_empty, compl_empty]

/-- **Exercise 3.10(4), the positive half.** The union of the enlargements is always contained
in the enlargement of the union. -/
theorem iUnion_starSet_subset {ι : Sort*} (A : ι → Set α) :
    ⋃ i, (⋆(A i) : Set αS) ⊆ ⋆(⋃ i, A i) :=
  iUnion_subset fun i => starSet_mono (subset_iUnion A i)

/-- **Exercise 3.10(4), finite unions.** Enlargement commutes with unions over a finite index
set. -/
theorem starSet_iUnion_of_finite {ι : Type*} [Finite ι] (A : ι → Set α) :
    (⋆(⋃ i, A i) : Set αS) = ⋃ i, ⋆(A i) := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_iUnion, ofSeq_mem_starSet, almostAll_exists_finite]

/-- **Exercise 3.10(4), finite intersections.** Enlargement commutes with intersections over a
finite index set. -/
theorem starSet_iInter_of_finite {ι : Type*} [Finite ι] (A : ι → Set α) :
    (⋆(⋂ i, A i) : Set αS) = ⋂ i, ⋆(A i) := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_iInter, ofSeq_mem_starSet, almostAll_forall_finite]

/-- **Exercise 3.10(4), infinite intersections.** The enlargement of an intersection is always
contained in the intersection of the enlargements. -/
theorem starSet_iInter_subset {ι : Sort*} (A : ι → Set α) :
    (⋆(⋂ i, A i) : Set αS) ⊆ ⋂ i, ⋆(A i) :=
  subset_iInter fun i => starSet_mono (iInter_subset A i)

/-- **Exercise 3.10(5).** $`{}^*A \cap \mathbb R = A`: the standard elements of the enlargement
are the elements of $`A`. -/
theorem preimage_of_starSet (A : Set α) : of ⁻¹' (⋆A : Set αS) = A := by
  ext a
  exact of_mem_starSet

/-- **Exercise 3.10(5).** The members of $`{}^*A` that are copies of standard elements are
exactly the copies of members of $`A`. -/
theorem starSet_inter_range_of (A : Set α) :
    (⋆A : Set αS) ∩ range (of : α → αS) = of '' A := by
  ext x
  constructor
  · rintro ⟨hx, a, rfl⟩
    exact ⟨a, of_mem_starSet.1 hx, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨of_mem_starSet.2 ha, a, rfl⟩

/-- **Exercise 3.10(5)**, for the reals: $`{}^*A \cap \mathbb R = A`. -/
theorem starSet_inter_range_coe (A : Set ℝ) :
    ⋆A ∩ range ((↑) : ℝ → ℝ*) = ((↑) : ℝ → ℝ*) '' A :=
  starSet_inter_range_of A

end Enlargement

namespace Ultrapower

variable {α : Type*} [Preorder α]

/-- **Section 3.6, almost-all criterion for the order**, in any ultrapower of an ordered
type. -/
theorem ofSeq_le_iff {r s : ℕ → α} :
    (ofSeq r : Ultrapower α) ≤ ofSeq s ↔ ∀ᶠ n in hyperfilter ℕ, r n ≤ s n :=
  Germ.coe_le

/-- **Section 3.6, almost-all criterion for the strict order**, in any ultrapower of an ordered
type. -/
theorem ofSeq_lt_iff {r s : ℕ → α} :
    (ofSeq r : Ultrapower α) < ofSeq s ↔ ∀ᶠ n in hyperfilter ℕ, r n < s n :=
  Germ.coe_lt

end Ultrapower

section Intervals

variable {α : Type*} [Preorder α]

/-- **Exercise 3.10(6).** The enlargement of a closed interval is the closed interval of the
ultrapower with the same endpoints. -/
theorem starSet_Icc (a b : α) : (⋆(Icc a b) : Set (Ultrapower α)) = Icc (of a) (of b) := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_Icc, ofSeq_mem_starSet, almostAll_and, of_eq_ofSeq, Ultrapower.ofSeq_le_iff]

/-- **Exercise 3.10(6), open intervals.** -/
theorem starSet_Ioo (a b : α) : (⋆(Ioo a b) : Set (Ultrapower α)) = Ioo (of a) (of b) := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_Ioo, ofSeq_mem_starSet, almostAll_and, of_eq_ofSeq, Ultrapower.ofSeq_lt_iff]

/-- **Exercise 3.10(6), half-open intervals.** -/
theorem starSet_Ico (a b : α) : (⋆(Ico a b) : Set (Ultrapower α)) = Ico (of a) (of b) := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_Ico, ofSeq_mem_starSet, almostAll_and, of_eq_ofSeq, Ultrapower.ofSeq_lt_iff,
    Ultrapower.ofSeq_le_iff]

/-- **Exercise 3.10(6), half-open intervals.** -/
theorem starSet_Ioc (a b : α) : (⋆(Ioc a b) : Set (Ultrapower α)) = Ioc (of a) (of b) := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_Ioc, ofSeq_mem_starSet, almostAll_and, of_eq_ofSeq, Ultrapower.ofSeq_lt_iff,
    Ultrapower.ofSeq_le_iff]

/-- **Exercise 3.10(6), closed rays.** -/
theorem starSet_Ici (a : α) : (⋆(Ici a) : Set (Ultrapower α)) = Ici (of a) := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_Ici, ofSeq_mem_starSet, of_eq_ofSeq, Ultrapower.ofSeq_le_iff]

/-- **Exercise 3.10(6), closed rays.** -/
theorem starSet_Iic (a : α) : (⋆(Iic a) : Set (Ultrapower α)) = Iic (of a) := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_Iic, ofSeq_mem_starSet, of_eq_ofSeq, Ultrapower.ofSeq_le_iff]

/-- **Exercise 3.10(8), open rays.** -/
theorem starSet_Ioi (a : α) : (⋆(Ioi a) : Set (Ultrapower α)) = Ioi (of a) := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_Ioi, ofSeq_mem_starSet, of_eq_ofSeq, Ultrapower.ofSeq_lt_iff]

/-- **Exercise 3.10(8), open rays.** -/
theorem starSet_Iio (a : α) : (⋆(Iio a) : Set (Ultrapower α)) = Iio (of a) := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  simp only [mem_Iio, ofSeq_mem_starSet, of_eq_ofSeq, Ultrapower.ofSeq_lt_iff]

/-- **Exercise 3.10(6).** For real numbers $`a, b`, the enlargement of the closed interval
$`[a, b]` is the set of hyperreals $`x` with $`a \le x \le b`. -/
theorem starSet_Icc_real (a b : ℝ) : ⋆(Icc a b) = Icc (a : ℝ*) b := starSet_Icc a b

/-- **Exercise 3.10(6)**, open real intervals. -/
theorem starSet_Ioo_real (a b : ℝ) : ⋆(Ioo a b) = Ioo (a : ℝ*) b := starSet_Ioo a b

/-- **Exercise 3.10(6)**, half-open real intervals. -/
theorem starSet_Ico_real (a b : ℝ) : ⋆(Ico a b) = Ico (a : ℝ*) b := starSet_Ico a b

/-- **Exercise 3.10(6)**, half-open real intervals. -/
theorem starSet_Ioc_real (a b : ℝ) : ⋆(Ioc a b) = Ioc (a : ℝ*) b := starSet_Ioc a b

/-- **Exercise 3.10(6)**, closed real rays. -/
theorem starSet_Ici_real (a : ℝ) : ⋆(Ici a) = Ici (a : ℝ*) := starSet_Ici a

/-- **Exercise 3.10(6)**, closed real rays. -/
theorem starSet_Iic_real (a : ℝ) : ⋆(Iic a) = Iic (a : ℝ*) := starSet_Iic a

/-- **Exercise 3.10(6)**, open real rays. -/
theorem starSet_Ioi_real (a : ℝ) : ⋆(Ioi a) = Ioi (a : ℝ*) := starSet_Ioi a

/-- **Exercise 3.10(6)**, open real rays. -/
theorem starSet_Iio_real (a : ℝ) : ⋆(Iio a) = Iio (a : ℝ*) := starSet_Iio a

/-- **Exercise 3.10(8).** The enlargement of the set of positive reals is the set of positive
hyperreals. -/
theorem starSet_pos_real : ⋆{x : ℝ | 0 < x} = {x : ℝ* | 0 < x} := starSet_Ioi_real 0

end Intervals

section NumberSystems

/-- **Section 3.9.** The set $`{}^*\mathbb N` of _hypernatural numbers_: the enlargement of the
set of natural numbers, as a subset of the hyperreals. Written {lit}`ℕ*`. -/
def hyperNat : Set ℝ* := ⋆(range ((↑) : ℕ → ℝ))

/-- **Exercise 3.10(7).** The set $`{}^*\mathbb Z` of _hyperintegers_: the enlargement of the
set of integers, as a subset of the hyperreals. Written {lit}`ℤ*`. -/
def hyperInt : Set ℝ* := ⋆(range ((↑) : ℤ → ℝ))

/-- **Section 3.9.** The set $`{}^*\mathbb Q` of _hyperrational numbers_: the enlargement of
the set of rationals, as a subset of the hyperreals. Written {lit}`ℚ*`. -/
def hyperRat : Set ℝ* := ⋆(range ((↑) : ℚ → ℝ))

@[inherit_doc] scoped notation "ℕ*" => hyperNat
@[inherit_doc] scoped notation "ℤ*" => hyperInt
@[inherit_doc] scoped notation "ℚ*" => hyperRat

/-- **Section 3.9.** A member of the enlargement of the range of a map $`f` is the class of a
sequence of values of $`f`. -/
theorem mem_starSet_range_iff {α αS : Type u} [StarType α αS] {β : Type v} {f : β → α}
    {x : αS} : x ∈ ⋆(range f) ↔ ∃ k : ℕ → β, x = ofSeq fun n => f (k n) := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [ofSeq_mem_starSet]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_seq_of_almostAll_exists h
    exact ⟨k, Ultrapower.ofSeq_eq_ofSeq.2 (hk.mono fun n hn => hn.symm)⟩
  · rintro ⟨k, hk⟩
    exact (Ultrapower.ofSeq_eq_ofSeq.1 hk).mono fun n hn => ⟨k n, hn.symm⟩

/-- **Section 3.9.** A hyperreal is a hypernatural number if and only if it is the class of a
sequence of natural numbers. -/
theorem mem_hyperNat_iff {x : ℝ*} :
    x ∈ ℕ* ↔ ∃ k : ℕ → ℕ, x = Hyperreal.ofSeq fun n => (k n : ℝ) :=
  mem_starSet_range_iff

/-- **Section 3.9.** A hyperreal is a hyperinteger if and only if it is the class of a sequence
of integers. -/
theorem mem_hyperInt_iff {x : ℝ*} :
    x ∈ ℤ* ↔ ∃ k : ℕ → ℤ, x = Hyperreal.ofSeq fun n => (k n : ℝ) :=
  mem_starSet_range_iff

/-- **Section 3.9.** A hyperreal is hyperrational if and only if it is the class of a sequence
of rational numbers. -/
theorem mem_hyperRat_iff {x : ℝ*} :
    x ∈ ℚ* ↔ ∃ k : ℕ → ℚ, x = Hyperreal.ofSeq fun n => (k n : ℝ) :=
  mem_starSet_range_iff

/-- **Section 3.9.** Every natural number is a hypernatural number. -/
theorem natCast_mem_hyperNat (n : ℕ) : (n : ℝ*) ∈ ℕ* :=
  coe_mem_starSet (a := (n : ℝ)).2 ⟨n, rfl⟩

/-- **Section 3.9.** Every integer is a hyperinteger. -/
theorem intCast_mem_hyperInt (n : ℤ) : (n : ℝ*) ∈ ℤ* :=
  coe_mem_starSet (a := (n : ℝ)).2 ⟨n, rfl⟩

/-- **Section 3.9.** A real number is a hypernatural number only if it is a natural number. -/
theorem coe_mem_hyperNat_iff {r : ℝ} : (r : ℝ*) ∈ ℕ* ↔ ∃ n : ℕ, (n : ℝ) = r :=
  coe_mem_starSet

/-- **Section 3.9.** $`{}^*\mathbb N \subseteq {}^*\mathbb Z`. -/
theorem hyperNat_subset_hyperInt : ℕ* ⊆ ℤ* :=
  starSet_mono (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩)

/-- **Section 3.9.** $`{}^*\mathbb Z \subseteq {}^*\mathbb Q`. -/
theorem hyperInt_subset_hyperRat : ℤ* ⊆ ℚ* :=
  starSet_mono (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩)

/-- **Section 3.9.** $`\omega` is a hypernatural number. -/
theorem omega_mem_hyperNat : (ω : ℝ*) ∈ ℕ* :=
  mem_hyperNat_iff.2 ⟨id, rfl⟩

/-- **Section 3.9.** $`\omega` is a _nonstandard_ natural number: it belongs to
$`{}^*\mathbb N` but is not a natural number (indeed not a real number). -/
theorem omega_nonstandard_nat : (ω : ℝ*) ∈ ℕ* ∧ ∀ n : ℕ, (ω : ℝ*) ≠ n :=
  ⟨omega_mem_hyperNat, fun n => omega_ne_coe n⟩

/-- **Exercise 3.10(4).** Enlargement does not commute with countable unions. The union of the
enlargements of the singletons $`\{n\}` is the set of standard natural numbers, whereas the
enlargement of the union is $`{}^*\mathbb N`, which contains $`\omega`. -/
theorem starSet_iUnion_ne_iUnion_starSet :
    ⋆(⋃ n : ℕ, ({(n : ℝ)} : Set ℝ)) ≠ ⋃ n : ℕ, ⋆({(n : ℝ)} : Set ℝ) := by
  intro h
  have hω : (ω : ℝ*) ∈ ⋆(⋃ n : ℕ, ({(n : ℝ)} : Set ℝ)) := by
    have : (⋃ n : ℕ, ({(n : ℝ)} : Set ℝ)) = range ((↑) : ℕ → ℝ) := by
      ext x
      simp [eq_comm]
    rw [this]
    exact omega_mem_hyperNat
  rw [h, mem_iUnion] at hω
  obtain ⟨n, hn⟩ := hω
  rw [starSet_singleton] at hn
  exact omega_ne_coe n hn

/-- **Exercise 3.10(7), general form.** If a set of reals is closed under a binary operation
$`f`, its enlargement is closed under the termwise extension of $`f`. -/
theorem ofSeq_binop_mem_starSet {A : Set ℝ} {f : ℝ → ℝ → ℝ} (hf : ∀ a ∈ A, ∀ b ∈ A, f a b ∈ A)
    {F : ℝ* → ℝ* → ℝ*}
    (hF : ∀ r s : ℕ → ℝ, F (Hyperreal.ofSeq r) (Hyperreal.ofSeq s) =
      Hyperreal.ofSeq fun n => f (r n) (s n))
    {x y : ℝ*} (hx : x ∈ ⋆A) (hy : y ∈ ⋆A) : F x y ∈ ⋆A := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
  rw [hF, hyperreal_ofSeq_mem_starSet]
  filter_upwards [hyperreal_ofSeq_mem_starSet.1 hx, hyperreal_ofSeq_mem_starSet.1 hy] with n h₁ h₂
  exact hf _ h₁ _ h₂

/-- **Exercise 3.10(7).** If a set of reals is closed under addition, so is its
enlargement. -/
theorem add_mem_starSet {A : Set ℝ} (hA : ∀ a ∈ A, ∀ b ∈ A, a + b ∈ A) {x y : ℝ*}
    (hx : x ∈ ⋆A) (hy : y ∈ ⋆A) : x + y ∈ ⋆A :=
  ofSeq_binop_mem_starSet hA (F := (· + ·)) (fun _ _ => rfl) hx hy

/-- **Exercise 3.10(7).** If a set of reals is closed under multiplication, so is its
enlargement. -/
theorem mul_mem_starSet {A : Set ℝ} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) {x y : ℝ*}
    (hx : x ∈ ⋆A) (hy : y ∈ ⋆A) : x * y ∈ ⋆A :=
  ofSeq_binop_mem_starSet hA (F := (· * ·)) (fun _ _ => rfl) hx hy

/-- **Exercise 3.10(7).** If a set of reals is closed under negation, so is its
enlargement. -/
theorem neg_mem_starSet {A : Set ℝ} (hA : ∀ a ∈ A, -a ∈ A) {x : ℝ*} (hx : x ∈ ⋆A) :
    -x ∈ ⋆A := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [ofSeq_neg, hyperreal_ofSeq_mem_starSet]
  exact (hyperreal_ofSeq_mem_starSet.1 hx).mono fun n hn => hA _ hn

/-- **Exercise 3.10(7).** If a set of reals is closed under inversion, so is its
enlargement. -/
theorem inv_mem_starSet {A : Set ℝ} (hA : ∀ a ∈ A, a⁻¹ ∈ A) {x : ℝ*} (hx : x ∈ ⋆A) :
    x⁻¹ ∈ ⋆A := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [inv_ofSeq, hyperreal_ofSeq_mem_starSet]
  refine (hyperreal_ofSeq_mem_starSet.1 hx).mono fun n hn => ?_
  have h : invSeq r n = (r n)⁻¹ := by
    by_cases h0 : r n = 0 <;> simp [invSeq, h0]
  rw [h]
  exact hA _ hn

/-- **Exercise 3.10(7).** The hypernatural numbers are closed under addition. -/
theorem add_mem_hyperNat {x y : ℝ*} (hx : x ∈ ℕ*) (hy : y ∈ ℕ*) : x + y ∈ ℕ* :=
  add_mem_starSet (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a + b, by push_cast; rfl⟩) hx hy

/-- **Exercise 3.10(7).** The hypernatural numbers are closed under multiplication. -/
theorem mul_mem_hyperNat {x y : ℝ*} (hx : x ∈ ℕ*) (hy : y ∈ ℕ*) : x * y ∈ ℕ* :=
  mul_mem_starSet (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, by push_cast; rfl⟩) hx hy

/-- **Exercise 3.10(7).** $`{}^*\mathbb Z` is a subring of the hyperreals: it contains $`0` and
$`1` and is closed under addition, negation and multiplication. -/
def hyperIntSubring : Subring ℝ* where
  carrier := ℤ*
  zero_mem' := by simpa using intCast_mem_hyperInt 0
  one_mem' := by simpa using intCast_mem_hyperInt 1
  add_mem' := add_mem_starSet
    (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a + b, by push_cast; rfl⟩)
  mul_mem' := mul_mem_starSet
    (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, by push_cast; rfl⟩)
  neg_mem' := neg_mem_starSet (by rintro _ ⟨a, rfl⟩; exact ⟨-a, by push_cast; rfl⟩)

/-- **Exercise 3.10(7).** The underlying set of the subring of hyperintegers is
$`{}^*\mathbb Z`. -/
theorem coe_hyperIntSubring : (hyperIntSubring : Set ℝ*) = ℤ* := rfl

/-- **Exercise 3.10(7), companion.** $`{}^*\mathbb Q` is a subfield of the hyperreals. -/
def hyperRatSubfield : Subfield ℝ* where
  carrier := ℚ*
  zero_mem' := by
    have h : ((0 : ℝ) : ℝ*) ∈ ℚ* := coe_mem_starSet.2 ⟨0, by simp⟩
    simpa using h
  one_mem' := by
    have h : ((1 : ℝ) : ℝ*) ∈ ℚ* := coe_mem_starSet.2 ⟨1, by simp⟩
    simpa using h
  add_mem' := add_mem_starSet
    (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a + b, by push_cast; rfl⟩)
  mul_mem' := mul_mem_starSet
    (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, by push_cast; rfl⟩)
  neg_mem' := neg_mem_starSet (by rintro _ ⟨a, rfl⟩; exact ⟨-a, by push_cast; rfl⟩)
  inv_mem' := fun _ => inv_mem_starSet (by rintro _ ⟨a, rfl⟩; exact ⟨a⁻¹, by push_cast; rfl⟩)

end NumberSystems

end Goldblatt
