import Mathlib
import Goldblatt.Ch02_LargeSets

/-!
# 3 (part 1). The Ultrapower: Sections 3.1 to 3.8

This is the first of three parts of Chapter 3 (the overview is on the chapter page
{lit}`Goldblatt.Ch03_Ultrapower`). It covers the ring of real sequences, agreement almost
everywhere, the logical notation of statement values, the ultrapower as an ordered field, the
inclusion of the reals, and the first infinitesimal and unlimited hyperreals.
-/

noncomputable section

universe u

namespace Goldblatt

open Set Filter
open scoped Hyperreal Topology

/-!
## 3.1 The Ring of Real-Valued Sequences

Real sequences form a commutative ring under termwise addition and multiplication. Mathlib
provides this ring structure on the function type from the naturals to the reals, so there is
nothing to construct; we record that the operations are termwise and that the ring is not a
field, because it has zero divisors: the two alternating sequences of Chapter 2 multiply to
zero. More precisely a sequence is invertible exactly when none of its terms vanishes.
-/

section Sequences

/-- **Section 3.1.** Real sequences form a commutative ring; this is Mathlib's pointwise ring
structure on functions. -/
example : CommRing (ℕ → ℝ) := inferInstance

/-- **Section 3.1.** Addition of sequences is termwise. -/
theorem seq_add_apply (r s : ℕ → ℝ) (n : ℕ) : (r + s) n = r n + s n := rfl

/-- **Section 3.1.** Multiplication of sequences is termwise. -/
theorem seq_mul_apply (r s : ℕ → ℝ) (n : ℕ) : (r * s) n = r n * s n := rfl

/-- **Section 3.1.** The additive inverse of a sequence is taken termwise. -/
theorem seq_neg_apply (r : ℕ → ℝ) (n : ℕ) : (-r) n = -r n := rfl

/-- **Section 3.1.** The zero of the ring of sequences is the constant sequence $`0`. -/
theorem seq_zero_apply (n : ℕ) : (0 : ℕ → ℝ) n = 0 := rfl

/-- **Section 3.1.** The unity of the ring of sequences is the constant sequence $`1`. -/
theorem seq_one_apply (n : ℕ) : (1 : ℕ → ℝ) n = 1 := rfl

/-- **Section 3.1.** The two alternating sequences $`(1,0,1,0,\dots)` and $`(0,1,0,1,\dots)`
have product zero. -/
theorem alternating_mul_eq_zero : alternatingOneZero * alternatingZeroOne = 0 := by
  funext n
  by_cases h : Odd n <;> simp [alternatingOneZero, alternatingZeroOne, h]

/-- **Section 3.1.** The sequence $`(1,0,1,0,\dots)` is not the zero sequence. -/
theorem alternatingOneZero_ne_zero : alternatingOneZero ≠ 0 := fun h => by
  have := congrFun h 1
  simp [alternatingOneZero] at this

/-- **Section 3.1.** The sequence $`(0,1,0,1,\dots)` is not the zero sequence. -/
theorem alternatingZeroOne_ne_zero : alternatingZeroOne ≠ 0 := fun h => by
  have := congrFun h 0
  simp [alternatingZeroOne] at this

/-- **Section 3.1.** The ring of real sequences has zero divisors. -/
theorem exists_seq_zero_divisors : ∃ r s : ℕ → ℝ, r ≠ 0 ∧ s ≠ 0 ∧ r * s = 0 :=
  ⟨_, _, alternatingOneZero_ne_zero, alternatingZeroOne_ne_zero, alternating_mul_eq_zero⟩

/-- **Section 3.1.** A sequence has a multiplicative inverse in the ring of sequences if and
only if all of its terms are nonzero. -/
theorem isUnit_seq_iff (r : ℕ → ℝ) : IsUnit r ↔ ∀ n, r n ≠ 0 := by
  simp [Pi.isUnit_iff]

/-- **Section 3.1.** A sequence with at least one zero term has no multiplicative inverse. -/
theorem not_isUnit_seq_of_zero_term {r : ℕ → ℝ} {n : ℕ} (h : r n = 0) : ¬ IsUnit r :=
  fun hu => (isUnit_seq_iff r).1 hu n h

/-- **Section 3.1.** The ring of real sequences is not a field. -/
theorem not_isField_seq : ¬ IsField (ℕ → ℝ) := fun hF => by
  obtain ⟨s, hs⟩ := hF.mul_inv_cancel alternatingOneZero_ne_zero
  have h := congrFun hs 0
  simp [alternatingOneZero] at h

end Sequences

/-!
## 3.2 Equivalence Modulo an Ultrafilter

Two sequences are declared equivalent when the set of indices at which they agree is large,
that is, belongs to the hyperfilter. The definition makes sense for sequences of any kind, and
it is the relation Mathlib calls eventual equality along the hyperfilter.
-/

section SeqEquiv

variable {α : Type*}

/-- **Section 3.2.** Two sequences are _equivalent modulo the ultrafilter_ (they agree almost
everywhere) when their agreement set $`\{n : r_n = s_n\}` is large. -/
def SeqEquiv (r s : ℕ → α) : Prop := agreementSet r s ∈ hyperfilter ℕ

@[inherit_doc] scoped infix:50 " ≡ᵤ " => SeqEquiv

/-- **Section 3.2.** Agreement almost everywhere, phrased with Mathlib's "eventually"
quantifier. -/
theorem seqEquiv_iff_eventually {r s : ℕ → α} :
    r ≡ᵤ s ↔ ∀ᶠ n in hyperfilter ℕ, r n = s n := Iff.rfl

/-- **Section 3.2.** Agreement almost everywhere is Mathlib's eventual equality along the
hyperfilter. -/
theorem seqEquiv_iff_eventuallyEq {r s : ℕ → α} :
    r ≡ᵤ s ↔ r =ᶠ[(hyperfilter ℕ : Filter ℕ)] s := Iff.rfl

end SeqEquiv

/-!
## 3.3 Exercises on Almost-Everywhere Agreement

Agreement almost everywhere is an equivalence relation and is compatible with the ring
operations, so it is a congruence on the ring of sequences. Each proof exhibits a large set on
which the required agreement holds (Section 3.5 isolates these inclusions). The third exercise
is the first sign that the quotient will contain something new: the sequence
$`(1, \tfrac12, \tfrac13, \dots)` is not identified with zero.
-/

section SeqEquivExercises

variable {α : Type*}

/-- **Exercise 3.3(1), reflexivity.** -/
theorem SeqEquiv.refl (r : ℕ → α) : r ≡ᵤ r := by
  rw [SeqEquiv, agreementSet_self]
  exact univ_mem_hyperfilter ℕ

/-- **Exercise 3.3(1), symmetry.** -/
theorem SeqEquiv.symm {r s : ℕ → α} (h : r ≡ᵤ s) : s ≡ᵤ r := by
  rwa [SeqEquiv, agreementSet_comm]

/-- **Exercise 3.3(1), transitivity.** -/
theorem SeqEquiv.trans {r s t : ℕ → α} (h₁ : r ≡ᵤ s) (h₂ : s ≡ᵤ t) : r ≡ᵤ t :=
  mem_hyperfilter_of_superset (inter_mem_hyperfilter_iff.2 ⟨h₁, h₂⟩)
    (agreementSet_inter_subset r s t)

/-- **Exercise 3.3(1).** Agreement almost everywhere is an equivalence relation on sequences. -/
theorem seqEquiv_equivalence : Equivalence (SeqEquiv (α := α)) :=
  ⟨SeqEquiv.refl, SeqEquiv.symm, SeqEquiv.trans⟩

/-- **Exercise 3.3(2), addition.** If $`r \equiv r'` and $`s \equiv s'` then
$`r + s \equiv r' + s'`. -/
theorem SeqEquiv.add {r r' s s' : ℕ → ℝ} (hr : r ≡ᵤ r') (hs : s ≡ᵤ s') : r + s ≡ᵤ r' + s' :=
  mem_hyperfilter_of_superset (inter_mem_hyperfilter_iff.2 ⟨hr, hs⟩)
    fun n hn => by
      have h₁ : r n = r' n := hn.1
      have h₂ : s n = s' n := hn.2
      simp [agreementSet, h₁, h₂]

/-- **Exercise 3.3(2), multiplication.** If $`r \equiv r'` and $`s \equiv s'` then
$`r \cdot s \equiv r' \cdot s'`. -/
theorem SeqEquiv.mul {r r' s s' : ℕ → ℝ} (hr : r ≡ᵤ r') (hs : s ≡ᵤ s') : r * s ≡ᵤ r' * s' :=
  mem_hyperfilter_of_superset (inter_mem_hyperfilter_iff.2 ⟨hr, hs⟩)
    fun n hn => by
      have h₁ : r n = r' n := hn.1
      have h₂ : s n = s' n := hn.2
      simp [agreementSet, h₁, h₂]

/-- **Exercise 3.3(2), negation.** If $`r \equiv r'` then $`-r \equiv -r'`. -/
theorem SeqEquiv.neg {r r' : ℕ → ℝ} (hr : r ≡ᵤ r') : -r ≡ᵤ -r' :=
  mem_hyperfilter_of_superset hr fun n hn => by
    simp only [agreementSet, mem_ofPred_eq] at hn
    simp [agreementSet, hn]

/-- **Exercise 3.3(2).** Agreement almost everywhere is a congruence on the ring of real
sequences. -/
theorem seqEquiv_congruence {r r' s s' : ℕ → ℝ} (hr : r ≡ᵤ r') (hs : s ≡ᵤ s') :
    r + s ≡ᵤ r' + s' ∧ r * s ≡ᵤ r' * s' :=
  ⟨hr.add hs, hr.mul hs⟩

/-- **Exercise 3.3(3).** The sequence $`(1, \tfrac12, \tfrac13, \dots)` is not equivalent to
the zero sequence: the two agree nowhere, and the empty set is not large. -/
theorem not_seqEquiv_one_div_zero : ¬ (fun n : ℕ => 1 / ((n : ℝ) + 1)) ≡ᵤ (0 : ℕ → ℝ) := by
  intro h
  have hempty : agreementSet (fun n : ℕ => 1 / ((n : ℝ) + 1)) (0 : ℕ → ℝ) = ∅ := by
    ext n
    simp only [agreementSet, mem_ofPred_eq, Pi.zero_apply, mem_empty_iff_false, iff_false]
    positivity
  rw [SeqEquiv, hempty] at h
  exact empty_notMem_hyperfilter ℕ h

end SeqEquivExercises

/-!
## 3.4 A Suggestive Logical Notation

The book writes $`[\![ r = s ]\!]` for the agreement set of two sequences, and similarly
$`[\![ r < s ]\!]`, $`[\![ r \le s ]\!]` and so on for the set of indices at which the stated
relation holds between the terms: the "value" of a statement is a set of indices instead of a
truth value, and the statement holds almost everywhere when its value is large. In Lean the
value of a statement $`\varphi(n)` is the set-builder {lit}`{n | φ n}` and "the value is large"
is {lit}`∀ᶠ n in hyperfilter ℕ, φ n`. Chapter 2 already named $`[\![ r = s ]\!]`
({lit}`agreementSet`) and $`[\![ r < s ]\!]` ({lit}`lessSet`); we add $`[\![ r \le s ]\!]`.
-/

section StatementValues

variable {α : Type*}

/-- **Section 3.4.** The statement value $`[\![ r \le s ]\!] = \{n : r_n \le s_n\}`. -/
def leSet (r s : ℕ → ℝ) : Set ℕ := {n | r n ≤ s n}

/-- **Section 3.4.** The statement value $`[\![ r > s ]\!]` is $`[\![ s < r ]\!]`. -/
theorem setOf_gt_eq_lessSet (r s : ℕ → ℝ) : {n | r n > s n} = lessSet s r := rfl

/-- **Section 3.4.** The value of $`r \le s` is the union of the values of $`r < s` and
$`r = s`. -/
theorem leSet_eq_union (r s : ℕ → ℝ) : leSet r s = lessSet r s ∪ agreementSet r s := by
  ext n
  simp only [leSet, lessSet, agreementSet, mem_ofPred_eq, mem_union]
  exact le_iff_lt_or_eq

/-!
## 3.5 Exercises on Statement Values

The inclusions between statement values that make the quotient construction work. Each is a
pointwise triviality; the content is that largeness then propagates, because large sets are
closed under intersection and supersets. We also record how largeness of a statement value
interacts with the propositional connectives. For conjunction this holds for any filter; for
negation, disjunction and implication it is exactly the ultrafilter property.
-/

/-- **Exercise 3.5(1).** $`[\![ r = s ]\!] \cap [\![ s = t ]\!] \subseteq [\![ r = t ]\!]`. -/
theorem agreementSet_inter_agreementSet_subset (r s t : ℕ → α) :
    agreementSet r s ∩ agreementSet s t ⊆ agreementSet r t :=
  agreementSet_inter_subset r s t

/-- **Exercise 3.5(2).** Where $`r = r'` and $`s = s'` hold, so do $`r + s = r' + s'` and
$`r \cdot s = r' \cdot s'`. -/
theorem agreementSet_inter_subset_add_mul (r r' s s' : ℕ → ℝ) :
    agreementSet r r' ∩ agreementSet s s' ⊆
      agreementSet (r + s) (r' + s') ∩ agreementSet (r * s) (r' * s') := by
  rintro n ⟨h₁, h₂⟩
  simp only [agreementSet, mem_ofPred_eq] at h₁ h₂
  simp [agreementSet, h₁, h₂]

/-- **Exercise 3.5(3).**
$`[\![ r = r' ]\!] \cap [\![ s = s' ]\!] \cap [\![ r < s ]\!] \subseteq [\![ r' < s' ]\!]`. -/
theorem agreementSet_inter_lessSet_subset (r r' s s' : ℕ → ℝ) :
    agreementSet r r' ∩ agreementSet s s' ∩ lessSet r s ⊆ lessSet r' s' := by
  rintro n ⟨⟨h₁, h₂⟩, h₃⟩
  simp only [agreementSet, lessSet, mem_ofPred_eq] at h₁ h₂ h₃ ⊢
  rwa [← h₁, ← h₂]

/-- **Exercise 3.5(4).** If $`r \equiv r'` and $`s \equiv s'`, then $`[\![ r < s ]\!]` is large
if and only if $`[\![ r' < s' ]\!]` is. -/
theorem lessSet_mem_hyperfilter_congr {r r' s s' : ℕ → ℝ} (hr : r ≡ᵤ r') (hs : s ≡ᵤ s') :
    lessSet r s ∈ hyperfilter ℕ ↔ lessSet r' s' ∈ hyperfilter ℕ := by
  constructor
  · intro h
    exact mem_of_superset (inter_mem (inter_mem hr hs) h)
      (agreementSet_inter_lessSet_subset r r' s s')
  · intro h
    have hr' : agreementSet r' r ∈ hyperfilter ℕ := by rwa [agreementSet_comm]
    have hs' : agreementSet s' s ∈ hyperfilter ℕ := by rwa [agreementSet_comm]
    exact mem_of_superset (inter_mem (inter_mem hr' hs') h)
      (agreementSet_inter_lessSet_subset r' r s' s)

/-- **Section 3.5, Boolean laws.** A conjunction holds almost everywhere if and only if both
conjuncts do. -/
theorem almostAll_and {p q : ℕ → Prop} :
    (∀ᶠ n in hyperfilter ℕ, p n ∧ q n) ↔
      (∀ᶠ n in hyperfilter ℕ, p n) ∧ ∀ᶠ n in hyperfilter ℕ, q n :=
  eventually_and

/-- **Section 3.5, Boolean laws.** A disjunction holds almost everywhere if and only if one of
the disjuncts does. This uses that the index filter is an ultrafilter. -/
theorem almostAll_or {p q : ℕ → Prop} :
    (∀ᶠ n in hyperfilter ℕ, p n ∨ q n) ↔
      (∀ᶠ n in hyperfilter ℕ, p n) ∨ ∀ᶠ n in hyperfilter ℕ, q n :=
  Ultrafilter.eventually_or

/-- **Section 3.5, Boolean laws.** A negation holds almost everywhere if and only if the
negated statement does not. This uses that the index filter is an ultrafilter. -/
theorem almostAll_not {p : ℕ → Prop} :
    (∀ᶠ n in hyperfilter ℕ, ¬ p n) ↔ ¬ ∀ᶠ n in hyperfilter ℕ, p n :=
  Ultrafilter.eventually_not

/-- **Section 3.5, Boolean laws.** An implication holds almost everywhere if and only if the
almost-everywhere statements imply one another. -/
theorem almostAll_imp {p q : ℕ → Prop} :
    (∀ᶠ n in hyperfilter ℕ, p n → q n) ↔
      ((∀ᶠ n in hyperfilter ℕ, p n) → ∀ᶠ n in hyperfilter ℕ, q n) :=
  Ultrafilter.eventually_imp

/-- **Section 3.5, Boolean laws.** A biconditional holds almost everywhere if and only if the
two almost-everywhere statements are equivalent. -/
theorem almostAll_iff {p q : ℕ → Prop} :
    (∀ᶠ n in hyperfilter ℕ, (p n ↔ q n)) ↔
      ((∀ᶠ n in hyperfilter ℕ, p n) ↔ ∀ᶠ n in hyperfilter ℕ, q n) := by
  simp only [iff_iff_implies_and_implies, almostAll_and, almostAll_imp]

/-- **Section 3.5, Boolean laws.** A statement that does not mention the index holds almost
everywhere if and only if it holds. -/
theorem almostAll_const {p : Prop} : (∀ᶠ _n : ℕ in hyperfilter ℕ, p) ↔ p :=
  eventually_const

/-- **Section 3.5, Boolean laws.** A finite conjunction holds almost everywhere if and only if
each conjunct does. -/
theorem almostAll_forall_finite {ι : Type*} [Finite ι] {p : ι → ℕ → Prop} :
    (∀ᶠ n in hyperfilter ℕ, ∀ i, p i n) ↔ ∀ i, ∀ᶠ n in hyperfilter ℕ, p i n :=
  eventually_all

/-- **Section 3.5, Boolean laws.** A finite disjunction holds almost everywhere if and only if
one of the disjuncts does. -/
theorem almostAll_exists_finite {ι : Type*} [Finite ι] {p : ι → ℕ → Prop} :
    (∀ᶠ n in hyperfilter ℕ, ∃ i, p i n) ↔ ∃ i, ∀ᶠ n in hyperfilter ℕ, p i n := by
  rw [← not_iff_not]
  simp only [← almostAll_not, not_exists, almostAll_forall_finite]

/-- **Section 3.5, choice of witnesses.** If for almost all $`n` there is some $`b` with
$`p(n, b)`, then there is a single sequence $`s` with $`p(n, s_n)` for almost all $`n`. This is
the step behind every existential statement about the ultrapower. -/
theorem exists_seq_of_almostAll_exists {β : Type*} {p : ℕ → β → Prop}
    (h : ∀ᶠ n in hyperfilter ℕ, ∃ b, p n b) :
    ∃ s : ℕ → β, ∀ᶠ n in hyperfilter ℕ, p n (s n) := by
  classical
  obtain ⟨_, b₀, _⟩ := h.exists
  refine ⟨fun n => if hn : ∃ b, p n b then hn.choose else b₀, h.mono fun n hn => ?_⟩
  simp only [hn, ↓reduceDIte]
  exact hn.choose_spec

/-- **Section 3.5, choice of witnesses.** An existential statement holds at almost all indices
if and only if a single sequence of witnesses works at almost all indices. -/
theorem almostAll_exists_iff {β : Type*} {p : ℕ → β → Prop} :
    (∀ᶠ n in hyperfilter ℕ, ∃ b, p n b) ↔ ∃ s : ℕ → β, ∀ᶠ n in hyperfilter ℕ, p n (s n) :=
  ⟨exists_seq_of_almostAll_exists, fun ⟨s, hs⟩ => hs.mono fun n hn => ⟨s n, hn⟩⟩

/-- **Section 3.5, choice of witnesses.** A universal statement holds at almost all indices if
and only if it holds almost everywhere along every sequence. -/
theorem almostAll_forall_iff {β : Type*} {p : ℕ → β → Prop} :
    (∀ᶠ n in hyperfilter ℕ, ∀ b, p n b) ↔ ∀ s : ℕ → β, ∀ᶠ n in hyperfilter ℕ, p n (s n) := by
  rw [← not_iff_not]
  simp only [← almostAll_not, not_forall, almostAll_exists_iff]

end StatementValues

/-!
## 3.6 The Ultrapower

The hyperreals are the set of equivalence classes of real sequences. Mathlib's
{name}`Hyperreal` is this quotient: a germ along the hyperfilter is a class of functions under
eventual equality, which we saw is the relation of Section 3.2. We make the identification
explicit ({lit}`ultrapowerEquiv`), then state the definitions of the operations and the order on
classes, and the almost-all criterion for each of them.

Theorem 3.6.1 says that the result is an ordered field. The field and order structures come
from Mathlib's instances, but the three points the book singles out as needing the ultrafilter
property are proved here by the book's arguments: a nonzero class has an inverse given by
inverting the nonzero terms; exactly one of $`x < y`, $`x = y`, $`y < x` holds, because exactly
one of the three statement values is large; and the positive classes are closed under sum and
product.

The same construction applied to an arbitrary type $`\alpha` in place of the reals gives the
ultrapower {lit}`Ultrapower α`. Its basic interface is set up first, since the rest of the
chapter is phrased with it. So that statements about the reals are typed with Mathlib's
hyperreals and not with the definitionally equal ultrapower of the reals, the interface is
phrased through a small class {lit}`StarType α αS` that names the _star type_ of a type: the
hyperreals for the reals, and the ultrapower for everything else.
-/

/-- **Section 3.6.** The ultrapower of a type $`\alpha` modulo the hyperfilter: sequences in
$`\alpha` up to agreement almost everywhere. For the reals this is the type of hyperreals,
definitionally. -/
abbrev Ultrapower (α : Type*) : Type _ := Germ (hyperfilter ℕ : Filter ℕ) α

/-- **Section 3.6.** The _star type_ of a type $`\alpha`: the type that plays the role of
$`{}^*\alpha`, together with its identification with the ultrapower of $`\alpha`. For the reals
the star type is the type of hyperreals; for every other type it is the ultrapower itself. The
class exists only so that enlargements of sets of reals and extensions of real functions are
typed with Mathlib's hyperreals on the nose, while the same definitions and theorems serve
every other type. -/
class StarType (α : Type u) (αS : outParam (Type u)) where
  /-- The identification of the star type with the ultrapower. -/
  equiv : αS ≃ Ultrapower α

/-- **Section 3.6, convention.** The star type of a general type is its ultrapower. -/
instance (priority := low) instStarTypeUltrapower (α : Type u) : StarType α (Ultrapower α) :=
  ⟨Equiv.refl _⟩

/-- **Section 3.6, convention.** The star type of the reals is the type of hyperreals. -/
instance instStarTypeReal : StarType ℝ ℝ* := ⟨Equiv.refl _⟩

namespace Ultrapower

variable {α αS : Type u} [StarType α αS]

/-- **Section 3.6.** The class $`[r]` of a sequence $`r`, as an element of the star type. For
real sequences this is {name}`Hyperreal.ofSeq`. -/
def ofSeq (r : ℕ → α) : αS := StarType.equiv.symm (Germ.ofFun r)

/-- **Section 3.7.** The class $`{}^*a` of the constant sequence with value $`a`: the copy of a
standard element inside the star type. For a real number this is the coercion into the
hyperreals. -/
def of (a : α) : αS := StarType.equiv.symm (Germ.const a)

/-- **Section 3.6.** The identification of the star type with the ultrapower sends the class of a sequence to
its germ. -/
theorem equiv_ofSeq (r : ℕ → α) : StarType.equiv (ofSeq r : αS) = Germ.ofFun r :=
  Equiv.apply_symm_apply _ _

/-- **Section 3.6.** Every element of the star type is the class of some sequence. -/
theorem ofSeq_surjective : Function.Surjective (ofSeq : (ℕ → α) → αS) := fun x => by
  obtain ⟨r, hr⟩ := Quot.exists_rep (StarType.equiv (α := α) x)
  exact ⟨r, (Equiv.symm_apply_eq _).2 hr⟩

/-- **Section 3.6, almost-all criterion for equality.** Two classes are equal if and only if
the sequences agree at almost all indices. -/
theorem ofSeq_eq_ofSeq {r s : ℕ → α} :
    (ofSeq r : αS) = ofSeq s ↔ ∀ᶠ n in hyperfilter ℕ, r n = s n := by
  rw [ofSeq, ofSeq, Equiv.apply_eq_iff_eq]
  exact Germ.coe_eq

/-- **Section 3.6.** Two classes are equal if and only if the sequences are equivalent modulo
the ultrafilter. -/
theorem ofSeq_eq_ofSeq_iff_seqEquiv {r s : ℕ → α} : (ofSeq r : αS) = ofSeq s ↔ r ≡ᵤ s :=
  ofSeq_eq_ofSeq

/-- **Section 3.6.** Two classes differ if and only if the sequences differ at almost all
indices. -/
theorem ofSeq_ne_ofSeq {r s : ℕ → α} :
    (ofSeq r : αS) ≠ ofSeq s ↔ ∀ᶠ n in hyperfilter ℕ, r n ≠ s n := by
  rw [Ne, ofSeq_eq_ofSeq, ← almostAll_not]

/-- **Section 3.7.** The standard copy of $`a` is the class of the constant sequence. -/
theorem of_eq_ofSeq (a : α) : (of a : αS) = ofSeq fun _ => a := rfl

/-- **Section 3.7.** A class equals a standard element if and only if almost all terms of the
sequence equal it. -/
theorem ofSeq_eq_of {r : ℕ → α} {a : α} :
    (ofSeq r : αS) = of a ↔ ∀ᶠ n in hyperfilter ℕ, r n = a :=
  ofSeq_eq_ofSeq

/-- **Section 3.7.** Two standard copies are equal if and only if the elements are. -/
theorem of_inj {a b : α} : (of a : αS) = of b ↔ a = b := by
  rw [of_eq_ofSeq, of_eq_ofSeq, ofSeq_eq_ofSeq, almostAll_const]

/-- **Section 3.7.** The map sending a standard element to its copy in the star type is
injective. -/
theorem of_injective : Function.Injective (of : α → αS) := fun _ _ h => of_inj.1 h

end Ultrapower

/-- **Section 3.6.** In the ultrapower itself, the class of a sequence is its germ. -/
theorem Ultrapower.ofSeq_ultrapower {α : Type*} (r : ℕ → α) :
    (Ultrapower.ofSeq r : Ultrapower α) = Germ.ofFun r := rfl

/-- **Section 3.7.** In the ultrapower itself, the copy of a standard element is the constant
germ. -/
theorem Ultrapower.of_ultrapower {α : Type*} (a : α) :
    (Ultrapower.of a : Ultrapower α) = Germ.const a := rfl

open Ultrapower

/-- **Section 3.6.** The hyperreals are the ultrapower of the reals. -/
theorem hyperreal_eq_ultrapower : ℝ* = Ultrapower ℝ := rfl

/-- **Section 3.6.** For real sequences, the class in the star type is Mathlib's
{name}`Hyperreal.ofSeq`. -/
@[simp]
theorem Ultrapower.ofSeq_real (r : ℕ → ℝ) : (ofSeq r : ℝ*) = Hyperreal.ofSeq r := rfl

/-- **Section 3.7.** For a real number, the standard copy is the coercion into the
hyperreals. -/
@[simp]
theorem Ultrapower.of_real (a : ℝ) : (of a : ℝ*) = (a : ℝ*) := rfl

section Hyperreals

/-- **Section 3.6.** The setoid of agreement almost everywhere on real sequences. -/
def seqSetoid : Setoid (ℕ → ℝ) := ⟨SeqEquiv, seqEquiv_equivalence⟩

/-- **Section 3.6.** The book's hyperreals, the quotient set of real sequences by agreement
almost everywhere, are Mathlib's hyperreals. The identification sends the class of a sequence
to the class of the same sequence. -/
def ultrapowerEquiv : Quotient seqSetoid ≃ ℝ* :=
  Quotient.congr (Equiv.refl _) fun _ _ => Iff.rfl

/-- **Section 3.6.** The identification of the two quotients sends $`[r]` to $`[r]`. -/
theorem ultrapowerEquiv_mk (r : ℕ → ℝ) :
    ultrapowerEquiv (Quotient.mk seqSetoid r) = Hyperreal.ofSeq r := rfl

/-- **Section 3.6.** Every hyperreal is the class of a real sequence. -/
theorem hyperreal_exists_rep (x : ℝ*) : ∃ r : ℕ → ℝ, x = Hyperreal.ofSeq r := by
  obtain ⟨r, rfl⟩ := Hyperreal.ofSeq_surjective x
  exact ⟨r, rfl⟩

/-- **Section 3.6, almost-all criterion for equality.** $`[r] = [s]` if and only if
$`r_n = s_n` for almost all $`n`. -/
theorem ofSeq_eq_ofSeq_iff {r s : ℕ → ℝ} :
    Hyperreal.ofSeq r = Hyperreal.ofSeq s ↔ ∀ᶠ n in hyperfilter ℕ, r n = s n :=
  Germ.coe_eq

/-- **Section 3.6.** $`[r] = [s]` if and only if $`r \equiv s`. -/
theorem hyperreal_ofSeq_eq_iff_seqEquiv {r s : ℕ → ℝ} :
    Hyperreal.ofSeq r = Hyperreal.ofSeq s ↔ r ≡ᵤ s :=
  ofSeq_eq_ofSeq_iff

/-- **Section 3.6.** $`[r] \ne [s]` if and only if $`r_n \ne s_n` for almost all $`n`. -/
theorem ofSeq_ne_ofSeq_iff {r s : ℕ → ℝ} :
    Hyperreal.ofSeq r ≠ Hyperreal.ofSeq s ↔ ∀ᶠ n in hyperfilter ℕ, r n ≠ s n := by
  rw [Ne, ofSeq_eq_ofSeq_iff, ← almostAll_not]

/-- **Section 3.6, definition of addition.** $`[r] + [s] = [r + s]`. -/
theorem ofSeq_add (r s : ℕ → ℝ) :
    Hyperreal.ofSeq r + Hyperreal.ofSeq s = Hyperreal.ofSeq (r + s) := rfl

/-- **Section 3.6, definition of multiplication.** $`[r] \cdot [s] = [r \cdot s]`. -/
theorem ofSeq_mul (r s : ℕ → ℝ) :
    Hyperreal.ofSeq r * Hyperreal.ofSeq s = Hyperreal.ofSeq (r * s) := rfl

/-- **Section 3.6, additive inverses.** $`-[r] = [-r]`. -/
theorem ofSeq_neg (r : ℕ → ℝ) : -Hyperreal.ofSeq r = Hyperreal.ofSeq (-r) := rfl

/-- **Section 3.6.** $`[r] - [s] = [r - s]`. -/
theorem ofSeq_sub (r s : ℕ → ℝ) :
    Hyperreal.ofSeq r - Hyperreal.ofSeq s = Hyperreal.ofSeq (r - s) := rfl

/-- **Section 3.6.** The zero of the hyperreals is the class of the zero sequence. -/
theorem ofSeq_zero : Hyperreal.ofSeq 0 = 0 := rfl

/-- **Section 3.6.** The unity of the hyperreals is the class of the constant sequence
$`1`. -/
theorem ofSeq_one : Hyperreal.ofSeq 1 = 1 := rfl

/-- **Section 3.6, definition of the order.** $`[r] < [s]` if and only if the statement value
$`[\![ r < s ]\!]` is large. -/
theorem ofSeq_lt_ofSeq_iff_lessSet {r s : ℕ → ℝ} :
    Hyperreal.ofSeq r < Hyperreal.ofSeq s ↔ lessSet r s ∈ hyperfilter ℕ :=
  Hyperreal.ofSeq_lt_ofSeq

/-- **Section 3.6, almost-all criterion for the order.** $`[r] < [s]` if and only if
$`r_n < s_n` for almost all $`n`. -/
theorem ofSeq_lt_ofSeq_iff {r s : ℕ → ℝ} :
    Hyperreal.ofSeq r < Hyperreal.ofSeq s ↔ ∀ᶠ n in hyperfilter ℕ, r n < s n :=
  Hyperreal.ofSeq_lt_ofSeq

/-- **Section 3.6, almost-all criterion for the weak order.** $`[r] \le [s]` if and only if
$`r_n \le s_n` for almost all $`n`. -/
theorem ofSeq_le_ofSeq_iff {r s : ℕ → ℝ} :
    Hyperreal.ofSeq r ≤ Hyperreal.ofSeq s ↔ ∀ᶠ n in hyperfilter ℕ, r n ≤ s n :=
  Hyperreal.ofSeq_le_ofSeq

/-- **Section 3.6.** $`[r] \le [s]` if and only if the statement value $`[\![ r \le s ]\!]` is
large. -/
theorem ofSeq_le_ofSeq_iff_leSet {r s : ℕ → ℝ} :
    Hyperreal.ofSeq r ≤ Hyperreal.ofSeq s ↔ leSet r s ∈ hyperfilter ℕ :=
  Hyperreal.ofSeq_le_ofSeq

/-- **Section 3.6, almost-all criterion for sums.** $`[r] + [s] = [t]` if and only if
$`r_n + s_n = t_n` for almost all $`n`. -/
theorem ofSeq_add_eq_ofSeq {r s t : ℕ → ℝ} :
    Hyperreal.ofSeq r + Hyperreal.ofSeq s = Hyperreal.ofSeq t ↔
      ∀ᶠ n in hyperfilter ℕ, r n + s n = t n := by
  rw [ofSeq_add, ofSeq_eq_ofSeq_iff]
  rfl

/-- **Section 3.6, almost-all criterion for products.** $`[r] \cdot [s] = [t]` if and only if
$`r_n \cdot s_n = t_n` for almost all $`n`. -/
theorem ofSeq_mul_eq_ofSeq {r s t : ℕ → ℝ} :
    Hyperreal.ofSeq r * Hyperreal.ofSeq s = Hyperreal.ofSeq t ↔
      ∀ᶠ n in hyperfilter ℕ, r n * s n = t n := by
  rw [ofSeq_mul, ofSeq_eq_ofSeq_iff]
  rfl

/-- **Theorem 3.6.1, the inverse sequence.** The sequence used in the book's proof to invert
$`[r]`: invert the nonzero terms and put $`0` elsewhere. -/
def invSeq (r : ℕ → ℝ) : ℕ → ℝ := fun n => if r n ≠ 0 then (r n)⁻¹ else 0

/-- **Theorem 3.6.1, existence of inverses.** If $`[r] \ne 0` then the set $`J` of indices
with $`r_n \ne 0` is large, and on $`J` the product of $`r` with its inverse sequence is $`1`;
hence $`[r]` has a multiplicative inverse. -/
theorem ofSeq_mul_ofSeq_invSeq {r : ℕ → ℝ} (h : Hyperreal.ofSeq r ≠ 0) :
    Hyperreal.ofSeq r * Hyperreal.ofSeq (invSeq r) = 1 := by
  have hJ : ∀ᶠ n in hyperfilter ℕ, r n ≠ 0 := by
    rw [← ofSeq_zero, ofSeq_ne_ofSeq_iff] at h
    exact h
  rw [← ofSeq_one, ofSeq_mul_eq_ofSeq]
  filter_upwards [hJ] with n hn
  simp [invSeq, hn]

/-- **Theorem 3.6.1, formula for the inverse.** The inverse of a class is the class of the
inverse sequence, $`[r]^{-1} = [r_n^{-1}]`, with the convention $`0^{-1} = 0`. -/
theorem inv_ofSeq (r : ℕ → ℝ) : (Hyperreal.ofSeq r)⁻¹ = Hyperreal.ofSeq (invSeq r) := by
  by_cases h : Hyperreal.ofSeq r = 0
  · rw [h, inv_zero, ← ofSeq_zero, ofSeq_eq_ofSeq_iff]
    rw [← ofSeq_zero, ofSeq_eq_ofSeq_iff] at h
    filter_upwards [h] with n hn
    simp [invSeq, hn]
  · exact inv_eq_of_mul_eq_one_right (ofSeq_mul_ofSeq_invSeq h)

/-- **Theorem 3.6.1, trichotomy of statement values.** For real sequences $`r, s`, exactly one
of the three sets $`[\![ r < s ]\!]`, $`[\![ r = s ]\!]`, $`[\![ s < r ]\!]` is large: they
partition the index set, and an ultrafilter contains exactly one block of a finite
partition. -/
theorem trichotomy_statement_values (r s : ℕ → ℝ) :
    (lessSet r s ∈ hyperfilter ℕ ∧ agreementSet r s ∉ hyperfilter ℕ ∧
        lessSet s r ∉ hyperfilter ℕ) ∨
      (lessSet r s ∉ hyperfilter ℕ ∧ agreementSet r s ∈ hyperfilter ℕ ∧
        lessSet s r ∉ hyperfilter ℕ) ∨
      (lessSet r s ∉ hyperfilter ℕ ∧ agreementSet r s ∉ hyperfilter ℕ ∧
        lessSet s r ∈ hyperfilter ℕ) := by
  have hcover : lessSet r s ∪ (agreementSet r s ∪ lessSet s r) ∈ hyperfilter ℕ := by
    refine mem_hyperfilter_of_superset (univ_mem_hyperfilter ℕ) fun n _ => ?_
    simp only [lessSet, agreementSet, mem_union, mem_ofPred_eq]
    exact lt_trichotomy (r n) (s n)
  have h₁₂ : lessSet r s ∈ hyperfilter ℕ → agreementSet r s ∈ hyperfilter ℕ → False :=
    fun h h' => by
      obtain ⟨n, hn, hn'⟩ := Filter.nonempty_of_mem (inter_mem h h')
      exact absurd hn' (ne_of_lt hn)
  have h₁₃ : lessSet r s ∈ hyperfilter ℕ → lessSet s r ∈ hyperfilter ℕ → False :=
    fun h h' => by
      obtain ⟨n, hn, hn'⟩ := Filter.nonempty_of_mem (inter_mem h h')
      exact lt_asymm (show r n < s n from hn) hn'
  have h₂₃ : agreementSet r s ∈ hyperfilter ℕ → lessSet s r ∈ hyperfilter ℕ → False :=
    fun h h' => by
      obtain ⟨n, hn, hn'⟩ := Filter.nonempty_of_mem (inter_mem h h')
      exact absurd hn (ne_of_gt hn')
  rw [union_mem_hyperfilter_iff, union_mem_hyperfilter_iff] at hcover
  tauto

/-- **Theorem 3.6.1, linearity of the order.** For hyperreals $`x, y`, exactly one of
$`x < y`, $`x = y`, $`y < x` holds. -/
theorem hyperreal_trichotomy (x y : ℝ*) :
    (x < y ∧ x ≠ y ∧ ¬ y < x) ∨ (¬ x < y ∧ x = y ∧ ¬ y < x) ∨ (¬ x < y ∧ x ≠ y ∧ y < x) := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
  simp only [Ne, hyperreal_ofSeq_eq_iff_seqEquiv, ofSeq_lt_ofSeq_iff_lessSet]
  exact trichotomy_statement_values r s

/-- **Theorem 3.6.1, positive classes are closed under addition** (the part of the proof left
as an exercise). -/
theorem ofSeq_add_pos {r s : ℕ → ℝ} (hr : 0 < Hyperreal.ofSeq r) (hs : 0 < Hyperreal.ofSeq s) :
    0 < Hyperreal.ofSeq r + Hyperreal.ofSeq s := by
  rw [← ofSeq_zero, ofSeq_lt_ofSeq_iff] at hr hs
  rw [ofSeq_add, ← ofSeq_zero, ofSeq_lt_ofSeq_iff]
  filter_upwards [hr, hs] with n h₁ h₂
  exact add_pos h₁ h₂

/-- **Theorem 3.6.1, positive classes are closed under multiplication** (the part of the proof
left as an exercise). -/
theorem ofSeq_mul_pos {r s : ℕ → ℝ} (hr : 0 < Hyperreal.ofSeq r) (hs : 0 < Hyperreal.ofSeq s) :
    0 < Hyperreal.ofSeq r * Hyperreal.ofSeq s := by
  rw [← ofSeq_zero, ofSeq_lt_ofSeq_iff] at hr hs
  rw [ofSeq_mul, ← ofSeq_zero, ofSeq_lt_ofSeq_iff]
  filter_upwards [hr, hs] with n h₁ h₂
  exact mul_pos h₁ h₂

/-- **Theorem 3.6.1.** The hyperreals are a field: Mathlib's instance, whose inverse is the one
computed in {name}`Goldblatt.inv_ofSeq`. -/
example : Field ℝ* := inferInstance

/-- **Theorem 3.6.1.** The hyperreals are linearly ordered: Mathlib's instance, whose
trichotomy is {name}`Goldblatt.hyperreal_trichotomy`. -/
example : LinearOrder ℝ* := inferInstance

/-- **Theorem 3.6.1.** With the operations and order defined on classes of sequences, the
hyperreals form an ordered field with zero $`[0]` and unity $`[1]`. The field and linear order
are Mathlib's instances; the statement records that they are compatible (a strict ordered
ring), names the zero and the unity, and repeats the three facts proved above by the book's
almost-everywhere arguments: nonzero elements are invertible, the order is total, and the
positive elements are closed under addition and multiplication. -/
theorem hyperreal_ordered_field :
    IsStrictOrderedRing ℝ* ∧ (0 : ℝ*) = Hyperreal.ofSeq 0 ∧ (1 : ℝ*) = Hyperreal.ofSeq 1 ∧
      (∀ x : ℝ*, x ≠ 0 → ∃ y, x * y = 1) ∧
      (∀ x y : ℝ*, x < y ∨ x = y ∨ y < x) ∧
      (∀ x y : ℝ*, 0 < x → 0 < y → 0 < x + y ∧ 0 < x * y) := by
  refine ⟨inferInstance, rfl, rfl, fun x hx => ?_, fun x y => ?_, fun x y hx hy => ?_⟩
  · obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
    exact ⟨_, ofSeq_mul_ofSeq_invSeq hx⟩
  · rcases hyperreal_trichotomy x y with h | h | h
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.2.1)
    · exact Or.inr (Or.inr h.2.2)
  · obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
    obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
    exact ⟨ofSeq_add_pos hx hy, ofSeq_mul_pos hx hy⟩

/-!
## 3.7 Including the Reals in the Hyperreals

A real number is sent to the class of the constant sequence with that value. This map
preserves sums, products and the order and is injective, so the reals may be regarded as an
ordered subfield of the hyperreals. In Mathlib the map is the coercion from the reals to the
hyperreals, and bundled as an ordered ring homomorphism it is {name}`Hyperreal.coeRingHom`.
-/

/-- **Section 3.7.** The hyperreal $`{}^*r` attached to a real number $`r` is the class of the
constant sequence $`(r, r, r, \dots)`. -/
theorem coe_eq_ofSeq_const (r : ℝ) : (r : ℝ*) = Hyperreal.ofSeq fun _ => r := rfl

/-- **Section 3.7.** $`{}^*(r + s) = {}^*r + {}^*s`. -/
theorem ofReal_add (r s : ℝ) : ((r + s : ℝ) : ℝ*) = r + s := Hyperreal.coe_add r s

/-- **Section 3.7.** $`{}^*(r \cdot s) = {}^*r \cdot {}^*s`. -/
theorem ofReal_mul (r s : ℝ) : ((r * s : ℝ) : ℝ*) = r * s := Hyperreal.coe_mul r s

/-- **Section 3.7.** $`{}^*r < {}^*s` if and only if $`r < s`: a constant statement holds
almost everywhere exactly when it holds. -/
theorem ofReal_lt_ofReal {r s : ℝ} : (r : ℝ*) < s ↔ r < s := by
  rw [coe_eq_ofSeq_const, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff, almostAll_const]

/-- **Section 3.7.** $`{}^*r = {}^*s` if and only if $`r = s`. -/
theorem ofReal_inj {r s : ℝ} : (r : ℝ*) = s ↔ r = s := by
  rw [coe_eq_ofSeq_const, coe_eq_ofSeq_const, ofSeq_eq_ofSeq_iff, almostAll_const]

/-- **Theorem 3.7.1.** The map $`r \mapsto {}^*r` is an order-preserving field isomorphism of
the reals into the hyperreals: it is a ring homomorphism (Mathlib's
{name}`Hyperreal.coeRingHom`) that is injective and strictly increasing. -/
theorem coe_orderEmbedding :
    (∀ r : ℝ, Hyperreal.coeRingHom r = (r : ℝ*)) ∧
      Function.Injective (Hyperreal.coeRingHom : ℝ → ℝ*) ∧
      StrictMono (Hyperreal.coeRingHom : ℝ → ℝ*) :=
  ⟨fun _ => rfl, fun _ _ h => ofReal_inj.1 h, fun _ _ h => ofReal_lt_ofReal.2 h⟩

/-- **Theorem 3.7.1.** The reals form a subfield of the hyperreals: the range of the inclusion,
as a subfield, is isomorphic to the reals as a ring. -/
def realSubfieldEquiv : ℝ ≃+* (Hyperreal.coeRingHom : ℝ →+* ℝ*).fieldRange :=
  RingEquiv.ofBijective (Hyperreal.coeRingHom : ℝ →+* ℝ*).rangeRestrictField
    ⟨fun _ _ h => ofReal_inj.1 (congrArg Subtype.val h), fun ⟨_, r, hr⟩ => ⟨r, Subtype.ext hr⟩⟩

/-!
## 3.8 Infinitesimals and Unlimited Numbers

The hyperreals are a proper extension of the reals. The class $`\varepsilon` of a sequence
tending to zero through positive values is positive but smaller than every positive real, and
the class $`\omega` of the sequence of natural numbers exceeds every real. Both facts use that
the ultrafilter is nonprincipal, in the form "cofinite sets are large". With a principal
ultrafilter every class would be the class of a constant sequence and nothing new would
appear.

Mathlib's {name}`Hyperreal.epsilon` and {name}`Hyperreal.omega` are the classes of
$`(0, 1, \tfrac12, \tfrac13, \dots)` and $`(0, 1, 2, \dots)`.
-/

/-- **Section 3.8.** $`\varepsilon` is the class of the sequence of reciprocals of the natural
numbers. -/
theorem epsilon_eq_ofSeq : (ε : ℝ*) = Hyperreal.ofSeq fun n => (n : ℝ)⁻¹ := rfl

/-- **Section 3.8.** $`\omega` is the class of the sequence of natural numbers. -/
theorem omega_eq_ofSeq : (ω : ℝ*) = Hyperreal.ofSeq fun n => (n : ℝ) := rfl

/-- **Section 3.8.** $`0 < \varepsilon`: the reciprocal $`1/n` is positive for almost all
$`n`. -/
theorem zero_lt_epsilon : (0 : ℝ*) < ε := by
  rw [epsilon_eq_ofSeq, ← ofSeq_zero, ofSeq_lt_ofSeq_iff]
  exact eventually_hyperfilter_of_forall_ge 1 fun n hn =>
    inv_pos.2 (Nat.cast_pos.2 (Nat.lt_of_lt_of_le Nat.one_pos hn))

/-- **Section 3.8.** $`\varepsilon` is smaller than every positive real number: for a positive
real $`r` the set of $`n` with $`1/n < r` is cofinite, hence large. -/
theorem epsilon_lt_coe {r : ℝ} (hr : 0 < r) : (ε : ℝ*) < r := by
  rw [epsilon_eq_ofSeq, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
  obtain ⟨N, hN⟩ := exists_nat_gt r⁻¹
  refine eventually_hyperfilter_of_forall_ge N fun n hn => ?_
  exact inv_lt_of_inv_lt₀ hr (lt_of_lt_of_le hN (Nat.cast_le.2 hn))

/-- **Section 3.8.** $`\varepsilon` is a positive infinitesimal: it is positive and smaller
than every positive real. In particular it is a nonzero infinitesimal, so the notion is not
vacuous. -/
theorem epsilon_pos_infinitesimal : (0 : ℝ*) < ε ∧ ∀ r : ℝ, 0 < r → (ε : ℝ*) < r :=
  ⟨zero_lt_epsilon, fun _ hr => epsilon_lt_coe hr⟩

/-- **Section 3.8.** $`\omega` is greater than every real number: by the Eudoxus–Archimedes
principle the set of $`n` with $`r < n` is cofinite, hence large. -/
theorem real_lt_omega (r : ℝ) : (r : ℝ*) < ω := by
  rw [omega_eq_ofSeq, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
  obtain ⟨N, hN⟩ := exists_nat_gt r
  exact eventually_hyperfilter_of_forall_ge N fun n hn => lt_of_lt_of_le hN (Nat.cast_le.2 hn)

/-- **Section 3.8.** $`\varepsilon \cdot \omega = 1`, so each is the inverse of the other. -/
theorem epsilon_mul_omega_eq_one : (ε : ℝ*) * ω = 1 := by
  rw [epsilon_eq_ofSeq, omega_eq_ofSeq, ← ofSeq_one, ofSeq_mul_eq_ofSeq]
  exact eventually_hyperfilter_of_forall_ge 1 fun n hn =>
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 hn))

/-- **Section 3.8.** $`\omega = \varepsilon^{-1}`. -/
theorem omega_eq_inv_epsilon : (ω : ℝ*) = ε⁻¹ :=
  (inv_eq_of_mul_eq_one_right epsilon_mul_omega_eq_one).symm

/-- **Section 3.8.** $`\varepsilon = \omega^{-1}`. -/
theorem epsilon_eq_inv_omega : (ε : ℝ*) = ω⁻¹ :=
  (inv_eq_of_mul_eq_one_left epsilon_mul_omega_eq_one).symm

/-- **Section 3.8.** $`\omega` is not a real number: for a real $`r` the set of $`n` with
$`r = n` has at most one element, so it is not large. -/
theorem omega_ne_coe (r : ℝ) : (ω : ℝ*) ≠ r := by
  rw [omega_eq_ofSeq, coe_eq_ofSeq_const, Ne, ofSeq_eq_ofSeq_iff]
  intro h
  refine notMem_hyperfilter_of_finite (Set.Subsingleton.finite ?_) h
  intro m hm n hn
  exact Nat.cast_injective (R := ℝ) (hm.trans hn.symm)

/-- **Section 3.8.** The hyperreals are a proper extension of the reals. -/
theorem omega_notMem_range_coe : (ω : ℝ*) ∉ range ((↑) : ℝ → ℝ*) :=
  fun ⟨r, hr⟩ => omega_ne_coe r hr.symm

/-- **Section 3.8.** The inclusion of the reals in the hyperreals is not surjective. -/
theorem coe_not_surjective : ¬ Function.Surjective ((↑) : ℝ → ℝ*) :=
  fun h => omega_notMem_range_coe (h ω)

/-- **Section 3.8.** The absolute value of a class is the class of the absolute values. (This
is also Exercise 3.12(3).) -/
theorem abs_ofSeq (r : ℕ → ℝ) : |Hyperreal.ofSeq r| = Hyperreal.ofSeq fun n => |r n| :=
  Germ.abs_def _

/-- **Section 3.8.** If a real sequence converges to zero then its class is infinitesimal: its
absolute value is smaller than every positive real. -/
theorem abs_ofSeq_lt_of_tendsto_zero {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0)) {r : ℝ}
    (hr : 0 < r) : |Hyperreal.ofSeq s| < r := by
  rw [abs_ofSeq, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
  refine eventually_hyperfilter_of_eventually_atTop ?_
  have h := hs.abs
  rw [abs_zero] at h
  exact h.eventually (gt_mem_nhds hr)

/-- **Section 3.8.** If a real sequence diverges to infinity then its class is unlimited: it
exceeds every real number. -/
theorem coe_lt_ofSeq_of_tendsto_atTop {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) (r : ℝ) :
    (r : ℝ*) < Hyperreal.ofSeq s := by
  rw [coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
  exact eventually_hyperfilter_of_eventually_atTop (hs.eventually (eventually_gt_atTop r))

/-- **Section 3.8.** The book's own example, the class of $`(1, \tfrac12, \tfrac13, \dots)`,
is a positive infinitesimal. -/
theorem ofSeq_one_div_pos_infinitesimal :
    (0 : ℝ*) < Hyperreal.ofSeq (fun n => 1 / ((n : ℝ) + 1)) ∧
      ∀ r : ℝ, 0 < r → Hyperreal.ofSeq (fun n => 1 / ((n : ℝ) + 1)) < r := by
  have hpos : (0 : ℝ*) < Hyperreal.ofSeq (fun n => 1 / ((n : ℝ) + 1)) := by
    rw [← ofSeq_zero, ofSeq_lt_ofSeq_iff]
    exact Eventually.of_forall fun n => by positivity
  refine ⟨hpos, fun r hr => ?_⟩
  have h := abs_ofSeq_lt_of_tendsto_zero tendsto_one_div_add_atTop_nhds_zero_nat hr
  rwa [abs_of_pos hpos] at h

/-- **Section 3.8, principal ultrafilters give nothing new.** If the ultrapower of the reals is
formed with the principal ultrafilter at an index $`j`, every sequence agrees almost everywhere
with the constant sequence at its $`j`-th term, so the inclusion of the reals is a bijection
onto the ultrapower. -/
theorem const_bijective_of_principal (j : ℕ) :
    Function.Bijective (Germ.const : ℝ → Germ (pure j : Filter ℕ) ℝ) := by
  refine ⟨fun a b h => Germ.const_inj.1 h, fun x => ?_⟩
  induction x using Germ.inductionOn with
  | _ f => exact ⟨f j, Germ.coe_eq.2 (by simp [EventuallyEq])⟩

/-- **Section 3.8, principal ultrafilters give nothing new.** With the principal ultrafilter
at an index $`j`, the inclusion of the reals is an isomorphism of ordered fields from the reals
onto the ultrapower: it is a bijection that preserves sums, products and the order. So a
principal ultrafilter produces only a copy of the reals. -/
noncomputable def constOrderRingIsoOfPrincipal (j : ℕ) : ℝ ≃+*o Germ (pure j : Filter ℕ) ℝ where
  toEquiv := Equiv.ofBijective _ (const_bijective_of_principal j)
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_le_map_iff' := Germ.const_le_iff

/-- **Section 3.8.** The isomorphism {name}`Goldblatt.constOrderRingIsoOfPrincipal` is the
inclusion of the reals as classes of constant sequences. -/
theorem constOrderRingIsoOfPrincipal_apply (j : ℕ) (r : ℝ) :
    constOrderRingIsoOfPrincipal j r = Germ.const r := rfl

/-- **Section 3.8, nonprincipal ultrafilters always give something new.** For any nonprincipal
ultrafilter on the natural numbers, the class of the identity sequence in the corresponding
ultrapower of the reals is not the class of a constant sequence. -/
theorem const_not_surjective_of_nonprincipal (U : Ultrafilter ℕ) (hU : ∀ j, U ≠ pure j) :
    ¬ Function.Surjective (Germ.const : ℝ → Germ (U : Filter ℕ) ℝ) := by
  intro hsurj
  obtain ⟨r, hr⟩ := hsurj (Germ.ofFun fun n : ℕ => (n : ℝ))
  have hmem : {n : ℕ | r = (n : ℝ)} ∈ U := Germ.coe_eq.1 hr
  have hfin : {n : ℕ | r = (n : ℝ)}.Finite :=
    Set.Subsingleton.finite fun m hm n hn => Nat.cast_injective (R := ℝ) (hm.symm.trans hn)
  obtain ⟨j, -, hj⟩ := Ultrafilter.eq_pure_of_finite_mem hfin hmem
  exact hU j hj

/-- **Exercise 3.8.1.** In any ordered field containing the reals, the inverse of a positive
infinitesimal is greater than every real number. Only ordered-field properties are used. The
ordered field is $`K`, and the reals sit inside it through an order-preserving ring
homomorphism $`\varphi`. -/
theorem lt_inv_of_pos_infinitesimal {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (φ : ℝ →+* K) (hφ : StrictMono φ) {e : K} (he : 0 < e)
    (hinf : ∀ r : ℝ, 0 < r → e < φ r) (r : ℝ) : φ r < e⁻¹ := by
  rcases le_or_gt r 0 with hr | hr
  · calc φ r ≤ φ 0 := hφ.monotone hr
      _ = 0 := map_zero φ
      _ < e⁻¹ := inv_pos.2 he
  · have h := hinf r⁻¹ (inv_pos.2 hr)
    rw [map_inv₀] at h
    have hφr : 0 < φ r := by
      have := hφ hr
      rwa [map_zero] at this
    exact (lt_inv_comm₀ hφr he).2 h

/-- **Exercise 3.8.1**, applied to the hyperreals: the inverse of $`\varepsilon` exceeds every
real number. -/
theorem coe_lt_inv_epsilon (r : ℝ) : (r : ℝ*) < ε⁻¹ :=
  lt_inv_of_pos_infinitesimal (Hyperreal.coeRingHom : ℝ →+* ℝ*) (fun _ _ h => ofReal_lt_ofReal.2 h)
    zero_lt_epsilon (fun _ hr => epsilon_lt_coe hr) r

end Hyperreals

end Goldblatt
