import Goldblatt.Ch11_InternalSets.Basic

/-!
# 11 (part 2). Defining Internal Sets: Sections 11.7 to 11.9

This is the second of three parts of Chapter 11 (the overview is on the chapter page
{lit}`Goldblatt.Ch11_InternalSets`). It proves the internal set definition principle: a set
defined by a first-order condition whose parameters are elements of the ultrapower and
internal sets is itself internal. The principle is then used as the book uses it, to show that
infinite sets of reals are external, to prove the underflow principle, and to prove the
permanence theorem for halos.
-/

universe u v

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Pointwise

/-!
## 11.7 Defining Internal Sets

The proofs of the least number principle and of order-completeness for internal sets were
ultrafilter calculations of one and the same shape: a statement about classes of sequences
and internal sets was shown to hold exactly when the corresponding statement about the terms
holds at almost all indices. This is true for every first-order statement, and it has a
consequence for sets. If a condition on $`x` is built from internal sets and elements of the
ultrapower by connectives and quantifiers, then the set of $`x` that satisfy it is the
internal set $`[B_n]`, where $`B_n` is the set defined by the same condition with the $`n`-th
terms of all parameters. This is the _internal set definition principle_.

The formalization has three layers.

* Quantifier lemmas ({lit}`Goldblatt.forall_star_iff`, {lit}`Goldblatt.exists_star_iff`):
  a quantifier over the ultrapower may be moved inside "for almost all $`n`". Together with
  the Boolean laws of Chapter 3 these compute any concrete definable set, and they are what
  the later proofs of this chapter use.
* Binary _internal relations_ ({lit}`Goldblatt.internalRel`), defined by sequences of
  relations exactly as internal sets are defined by sequences of sets, with the closure
  properties of sets defined from them: sections, and existential and universal
  quantification, bounded or not.
* The principle itself for an arbitrary first-order formula, as a theorem about a small
  deeply embedded language ({lit}`Goldblatt.IFormula`): atomic formulas are internal
  relations of any finite arity between the variables, and formulas are closed under
  negation, conjunction and universal quantification. Internal sets, enlargements of
  standard relations and graphs of extended functions are all atomic in this language, so it
  covers the formulas of the book.
-/

section Quantifiers

variable {α αS : Type u} {β βS : Type v} [StarType α αS] [StarType β βS]

/-- **Section 11.7, moving a universal quantifier inside "almost all".** If a property $`Q`
of elements of the ultrapower is decided on classes of sequences by an almost-all criterion,
then $`Q` holds for all elements if and only if, for almost all $`n`, the criterion holds for
all standard elements. -/
theorem forall_star_iff {Q : βS → Prop} {p : ℕ → β → Prop}
    (h : ∀ s : ℕ → β, Q (ofSeq s) ↔ ∀ᶠ n in hyperfilter ℕ, p n (s n)) :
    (∀ y, Q y) ↔ ∀ᶠ n in hyperfilter ℕ, ∀ b, p n b := by
  rw [(ofSeq_surjective (α := β) (αS := βS)).forall]
  simp only [h]
  exact almostAll_forall_iff.symm

/-- **Section 11.7, moving an existential quantifier inside "almost all".** If a property
$`Q` of elements of the ultrapower is decided on classes of sequences by an almost-all
criterion, then $`Q` holds for some element if and only if, for almost all $`n`, the
criterion holds for some standard element. -/
theorem exists_star_iff {Q : βS → Prop} {p : ℕ → β → Prop}
    (h : ∀ s : ℕ → β, Q (ofSeq s) ↔ ∀ᶠ n in hyperfilter ℕ, p n (s n)) :
    (∃ y, Q y) ↔ ∀ᶠ n in hyperfilter ℕ, ∃ b, p n b := by
  rw [(ofSeq_surjective (α := β) (αS := βS)).exists]
  simp only [h]
  exact almostAll_exists_iff.symm

/-- **Section 11.7**, for the hyperreals: a universal quantifier over the hyperreals may be
moved inside "almost all". -/
theorem hyperreal_forall_iff {Q : ℝ* → Prop} {p : ℕ → ℝ → Prop}
    (h : ∀ s : ℕ → ℝ, Q (Hyperreal.ofSeq s) ↔ ∀ᶠ n in hyperfilter ℕ, p n (s n)) :
    (∀ y, Q y) ↔ ∀ᶠ n in hyperfilter ℕ, ∀ b, p n b :=
  forall_star_iff h

/-- **Section 11.7**, for the hyperreals: an existential quantifier over the hyperreals may
be moved inside "almost all". -/
theorem hyperreal_exists_iff {Q : ℝ* → Prop} {p : ℕ → ℝ → Prop}
    (h : ∀ s : ℕ → ℝ, Q (Hyperreal.ofSeq s) ↔ ∀ᶠ n in hyperfilter ℕ, p n (s n)) :
    (∃ y, Q y) ↔ ∀ᶠ n in hyperfilter ℕ, ∃ b, p n b :=
  exists_star_iff h

end Quantifiers

section InternalRelations

variable {α αS : Type u} {β βS : Type v} [StarType α αS] [StarType β βS]

/-- **Section 11.7.** The _internal relation_ determined by a sequence $`(R_n)` of binary
relations: $`[r_n]` and $`[s_n]` are related when $`R_n(r_n, s_n)` for almost all $`n`. The
enlargement of a standard relation is the case of a constant sequence. -/
def internalRel (R : ℕ → α → β → Prop) (x : αS) (y : βS) : Prop :=
  ∃ (r : ℕ → α) (s : ℕ → β), x = ofSeq r ∧ y = ofSeq s ∧ ∀ᶠ n in hyperfilter ℕ, R n (r n) (s n)

/-- **Section 11.7, the almost-all criterion for internal relations.** The definition does
not depend on the representing sequences. -/
theorem internalRel_ofSeq {R : ℕ → α → β → Prop} {r : ℕ → α} {s : ℕ → β} :
    internalRel R (ofSeq r : αS) (ofSeq s : βS) ↔ ∀ᶠ n in hyperfilter ℕ, R n (r n) (s n) := by
  constructor
  · rintro ⟨r', s', hr, hs, h⟩
    have h1 : ∀ᶠ n in hyperfilter ℕ, r n = r' n := Ultrapower.ofSeq_eq_ofSeq.1 hr
    have h2 : ∀ᶠ n in hyperfilter ℕ, s n = s' n := Ultrapower.ofSeq_eq_ofSeq.1 hs
    exact (h1.and (h2.and h)).mono fun n hn => by
      rw [hn.1, hn.2.1]
      exact hn.2.2
  · exact fun h => ⟨r, s, rfl, rfl, h⟩

/-- **Section 11.7.** The enlargement of a standard relation is the internal relation of the
constant sequence. -/
theorem starRel₂_iff_internalRel {P : α → β → Prop} {x : αS} {y : βS} :
    ⋆P x y ↔ internalRel (fun _ => P) x y := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [starRel₂_ofSeq, internalRel_ofSeq]

/-- **Section 11.7.** Membership in an internal set, as an internal relation in which the
second argument is ignored. -/
theorem internalRel_mem {A : ℕ → Set α} {x : αS} {y : βS} :
    internalRel (fun n a (_ : β) => a ∈ A n) x y ↔ x ∈ internalSet A := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [internalRel_ofSeq, ofSeq_mem_internalSet]

/-- **Section 11.7.** The negation of an internal relation is internal. -/
theorem not_internalRel {R : ℕ → α → β → Prop} {x : αS} {y : βS} :
    ¬ internalRel R x y ↔ internalRel (fun n a b => ¬ R n a b) x y := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [internalRel_ofSeq, internalRel_ofSeq, almostAll_not]

/-- **Section 11.7.** The conjunction of two internal relations is internal. -/
theorem internalRel_and {R S : ℕ → α → β → Prop} {x : αS} {y : βS} :
    internalRel R x y ∧ internalRel S x y ↔ internalRel (fun n a b => R n a b ∧ S n a b) x y := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [internalRel_ofSeq, internalRel_ofSeq, internalRel_ofSeq, almostAll_and]

/-- **Section 11.7.** The disjunction of two internal relations is internal. -/
theorem internalRel_or {R S : ℕ → α → β → Prop} {x : αS} {y : βS} :
    internalRel R x y ∨ internalRel S x y ↔ internalRel (fun n a b => R n a b ∨ S n a b) x y := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [internalRel_ofSeq, internalRel_ofSeq, internalRel_ofSeq, almostAll_or]

/-- **Internal set definition, sections.** For an internal relation and a fixed parameter
$`c = [c_n]`, the set $`\{x : R(x, c)\}` is the internal set defined by the sections
$`\{a : R_n(a, c_n)\}`. -/
theorem setOf_internalRel_ofSeq (R : ℕ → α → β → Prop) (c : ℕ → β) :
    {x : αS | internalRel R x (ofSeq c : βS)} = internalSet fun n => {a | R n a (c n)} := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [mem_ofPred_eq, internalRel_ofSeq, ofSeq_mem_internalSet]
  rfl

/-- **Internal set definition, sections.** A section of an internal relation at a parameter
from the ultrapower is an internal set. -/
theorem isInternalSet_setOf_internalRel (R : ℕ → α → β → Prop) (c : βS) :
    IsInternalSet α {x : αS | internalRel R x c} := by
  obtain ⟨c, rfl⟩ := ofSeq_surjective (α := β) c
  exact ⟨_, setOf_internalRel_ofSeq R c⟩

/-- **Internal set definition, existential quantifier.** The set of $`x` that are related to
some $`y` by an internal relation is the internal set defined by the domains
$`\{a : \exists b,\ R_n(a, b)\}`. -/
theorem setOf_exists_internalRel (R : ℕ → α → β → Prop) :
    {x : αS | ∃ y : βS, internalRel R x y} = internalSet fun n => {a | ∃ b, R n a b} := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [mem_ofPred_eq, ofSeq_mem_internalSet]
  exact exists_star_iff fun s => internalRel_ofSeq

/-- **Internal set definition, universal quantifier.** The set of $`x` that are related to
every $`y` by an internal relation is the internal set defined by the sets
$`\{a : \forall b,\ R_n(a, b)\}`. -/
theorem setOf_forall_internalRel (R : ℕ → α → β → Prop) :
    {x : αS | ∀ y : βS, internalRel R x y} = internalSet fun n => {a | ∀ b, R n a b} := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [mem_ofPred_eq, ofSeq_mem_internalSet]
  exact forall_star_iff fun s => internalRel_ofSeq

/-- **Internal set definition, bounded existential quantifier.** The set of $`x` related to
some member of the internal set $`[B_n]` is the internal set defined by
$`\{a : \exists b \in B_n,\ R_n(a, b)\}`. -/
theorem setOf_exists_mem_internalRel (R : ℕ → α → β → Prop) (B : ℕ → Set β) :
    {x : αS | ∃ y ∈ (internalSet B : Set βS), internalRel R x y} =
      internalSet fun n => {a | ∃ b ∈ B n, R n a b} := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [mem_ofPred_eq, ofSeq_mem_internalSet]
  refine exists_star_iff fun s => ?_
  rw [ofSeq_mem_internalSet, internalRel_ofSeq, almostAll_and]

/-- **Internal set definition, bounded universal quantifier.** The set of $`x` related to
every member of the internal set $`[B_n]` is the internal set defined by
$`\{a : \forall b \in B_n,\ R_n(a, b)\}`. -/
theorem setOf_forall_mem_internalRel (R : ℕ → α → β → Prop) (B : ℕ → Set β) :
    {x : αS | ∀ y ∈ (internalSet B : Set βS), internalRel R x y} =
      internalSet fun n => {a | ∀ b ∈ B n, R n a b} := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [mem_ofPred_eq, ofSeq_mem_internalSet]
  refine forall_star_iff fun s => ?_
  rw [ofSeq_mem_internalSet, internalRel_ofSeq, almostAll_imp]

/-- **Internal set definition, quantifiers.** The domain of an internal relation is
internal. -/
theorem isInternalSet_setOf_exists_internalRel (R : ℕ → α → β → Prop) :
    IsInternalSet α {x : αS | ∃ y : βS, internalRel R x y} :=
  ⟨_, setOf_exists_internalRel R⟩

/-- **Internal set definition, quantifiers.** The set of points related to everything by an
internal relation is internal. -/
theorem isInternalSet_setOf_forall_internalRel (R : ℕ → α → β → Prop) :
    IsInternalSet α {x : αS | ∀ y : βS, internalRel R x y} :=
  ⟨_, setOf_forall_internalRel R⟩

/-- **Internal set definition, bounded quantifiers.** The set of points related to some
member of an internal set by an internal relation is internal. -/
theorem isInternalSet_setOf_exists_mem_internalRel (R : ℕ → α → β → Prop) {Y : Set βS}
    (hY : IsInternalSet β Y) : IsInternalSet α {x : αS | ∃ y ∈ Y, internalRel R x y} := by
  obtain ⟨B, rfl⟩ := hY
  exact ⟨_, setOf_exists_mem_internalRel R B⟩

/-- **Internal set definition, bounded quantifiers.** The set of points related to every
member of an internal set by an internal relation is internal. -/
theorem isInternalSet_setOf_forall_mem_internalRel (R : ℕ → α → β → Prop) {Y : Set βS}
    (hY : IsInternalSet β Y) : IsInternalSet α {x : αS | ∀ y ∈ Y, internalRel R x y} := by
  obtain ⟨B, rfl⟩ := hY
  exact ⟨_, setOf_forall_mem_internalRel R B⟩

end InternalRelations

/-!
### The principle for arbitrary formulas

To state the principle for all first-order formulas at once, formulas are made into data. A
formula with $`k` free variables is built from atomic formulas by negation, conjunction and
universal quantification; an atomic formula is given by a sequence of $`k`-ary relations on
the standard type, and is read in the ultrapower as the internal relation that the sequence
defines. A formula therefore has a standard reading at each index $`n` and a reading in the
ultrapower, and the theorem ({lit}`Goldblatt.IFormula.starRealize_ofSeq`) is that the reading
in the ultrapower holds of classes of sequences exactly when the reading at index $`n` holds
of their $`n`-th terms for almost all $`n`.
-/

section Formulas

variable {α αS : Type u} [StarType α αS]

/-- **Section 11.7.** The internal relation determined by a sequence of relations of finite
arity: a tuple of classes of sequences satisfies it when the tuples of $`n`-th terms satisfy
the $`n`-th relation for almost all $`n`. -/
def internalRelN {ι : Type*} [Finite ι] (R : ℕ → (ι → α) → Prop) (x : ι → αS) : Prop :=
  ∃ r : ι → ℕ → α, (∀ i, x i = ofSeq (r i)) ∧ ∀ᶠ n in hyperfilter ℕ, R n fun i => r i n

/-- **Section 11.7, the almost-all criterion for internal relations of finite arity.** -/
theorem internalRelN_ofSeq {ι : Type*} [Finite ι] {R : ℕ → (ι → α) → Prop} {r : ι → ℕ → α} :
    internalRelN R (fun i => (ofSeq (r i) : αS)) ↔
      ∀ᶠ n in hyperfilter ℕ, R n fun i => r i n := by
  constructor
  · rintro ⟨r', hr, h⟩
    have h1 : ∀ᶠ n in hyperfilter ℕ, ∀ i, r i n = r' i n :=
      almostAll_forall_finite.2 fun i => Ultrapower.ofSeq_eq_ofSeq.1 (hr i)
    exact (h1.and h).mono fun n hn => by
      have e : (fun i => r i n) = fun i => r' i n := funext hn.1
      rw [e]
      exact hn.2
  · exact fun h => ⟨r, fun _ => rfl, h⟩

/-- Every tuple of elements of the star type is a tuple of classes of sequences. -/
theorem exists_rep_fun {ι : Type*} (x : ι → αS) :
    ∃ r : ι → ℕ → α, x = fun i => ofSeq (r i) := by
  choose r hr using fun i => ofSeq_surjective (α := α) (x i)
  exact ⟨r, funext fun i => (hr i).symm⟩

/-- **Section 11.7.** First-order formulas with $`k` free variables over internal relations.
The variables are numbered from $`0`, and a quantifier binds variable $`0` and shifts the
others up by one. Disjunction, implication and the existential quantifier are defined from
the constructors. -/
inductive IFormula (α : Type u) : ℕ → Type u
  /-- An atomic formula: a sequence of relations between the free variables. -/
  | rel {k : ℕ} (R : ℕ → (Fin k → α) → Prop) : IFormula α k
  /-- Negation. -/
  | not {k : ℕ} (φ : IFormula α k) : IFormula α k
  /-- Conjunction. -/
  | and {k : ℕ} (φ ψ : IFormula α k) : IFormula α k
  /-- Universal quantification over variable $`0`. -/
  | all {k : ℕ} (φ : IFormula α (k + 1)) : IFormula α k

namespace IFormula

/-- Disjunction of formulas. -/
def or {k : ℕ} (φ ψ : IFormula α k) : IFormula α k := .not (.and (.not φ) (.not ψ))

/-- Implication between formulas. -/
def imp {k : ℕ} (φ ψ : IFormula α k) : IFormula α k := .not (.and φ (.not ψ))

/-- Existential quantification over variable $`0`. -/
def ex {k : ℕ} (φ : IFormula α (k + 1)) : IFormula α k := .not (.all (.not φ))

/-- The atomic formula saying that variable $`i` belongs to the internal set $`[A_n]`. -/
def mem {k : ℕ} (i : Fin k) (A : ℕ → Set α) : IFormula α k := .rel fun n v => v i ∈ A n

/-- The atomic formula saying that variables $`i` and $`j` are related by the binary internal
relation $`[R_n]`. -/
def rel₂ {k : ℕ} (i j : Fin k) (R : ℕ → α → α → Prop) : IFormula α k :=
  .rel fun n v => R n (v i) (v j)

/-- **Section 11.7.** The standard reading of a formula at index $`n`: atomic formulas are
read by their $`n`-th relation, and quantifiers range over the standard type. -/
def realize : {k : ℕ} → IFormula α k → ℕ → (Fin k → α) → Prop
  | _, .rel R, n, v => R n v
  | _, .not φ, n, v => ¬ φ.realize n v
  | _, .and φ ψ, n, v => φ.realize n v ∧ ψ.realize n v
  | _, .all φ, n, v => ∀ a : α, φ.realize n (Fin.cons a v)

/-- **Section 11.7.** The reading of a formula in the ultrapower: atomic formulas are read as
internal relations, and quantifiers range over the star type. -/
def starRealize : {k : ℕ} → IFormula α k → (Fin k → αS) → Prop
  | _, .rel R, v => internalRelN R v
  | _, .not φ, v => ¬ φ.starRealize v
  | _, .and φ ψ, v => φ.starRealize v ∧ ψ.starRealize v
  | _, .all φ, v => ∀ x : αS, φ.starRealize (Fin.cons x v)

/-- Adjoining a class of sequences to a tuple of classes of sequences. -/
theorem cons_ofSeq {k : ℕ} (s : ℕ → α) (r : Fin k → ℕ → α) :
    (Fin.cons (ofSeq s : αS) fun i => (ofSeq (r i) : αS) : Fin (k + 1) → αS) =
      fun i => ofSeq ((Fin.cons s r : Fin (k + 1) → ℕ → α) i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
  · simp only [Fin.cons_succ]

/-- The $`n`-th terms of a tuple of sequences with one sequence adjoined. -/
theorem cons_apply_seq {k : ℕ} (s : ℕ → α) (r : Fin k → ℕ → α) (n : ℕ) :
    (fun i => (Fin.cons s r : Fin (k + 1) → ℕ → α) i n) = Fin.cons (s n) fun i => r i n := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
  · simp only [Fin.cons_succ]

/-- **Section 11.7, the equivalence of (i) and (ii).** A formula holds in the ultrapower of
the classes $`[r^1_n], \dots, [r^k_n]` if and only if, for almost all $`n`, its standard
reading at index $`n` holds of $`r^1_n, \dots, r^k_n`. -/
theorem starRealize_ofSeq {k : ℕ} (φ : IFormula α k) (r : Fin k → ℕ → α) :
    φ.starRealize (fun i => (ofSeq (r i) : αS)) ↔
      ∀ᶠ n in hyperfilter ℕ, φ.realize n fun i => r i n := by
  induction φ with
  | rel R => exact internalRelN_ofSeq
  | not φ ih => simp only [starRealize, realize, ih, almostAll_not]
  | and φ ψ ih1 ih2 => simp only [starRealize, realize, ih1, ih2, almostAll_and]
  | all φ ih =>
    simp only [starRealize, realize]
    rw [(ofSeq_surjective (α := α) (αS := αS)).forall, almostAll_forall_iff]
    refine forall_congr' fun s => ?_
    rw [cons_ofSeq, ih]
    refine eventually_congr (Eventually.of_forall fun n => ?_)
    rw [cons_apply_seq]

/-- **Section 11.7.** The reading of a disjunction in the ultrapower. -/
theorem starRealize_or {k : ℕ} (φ ψ : IFormula α k) (v : Fin k → αS) :
    (φ.or ψ).starRealize v ↔ φ.starRealize v ∨ ψ.starRealize v := by
  simp only [IFormula.or, starRealize, not_and_or, not_not]

/-- **Section 11.7.** The reading of an implication in the ultrapower. -/
theorem starRealize_imp {k : ℕ} (φ ψ : IFormula α k) (v : Fin k → αS) :
    (φ.imp ψ).starRealize v ↔ (φ.starRealize v → ψ.starRealize v) := by
  simp only [IFormula.imp, starRealize, not_and, not_not]

/-- **Section 11.7.** The reading of an existential quantifier in the ultrapower. -/
theorem starRealize_ex {k : ℕ} (φ : IFormula α (k + 1)) (v : Fin k → αS) :
    φ.ex.starRealize v ↔ ∃ x : αS, φ.starRealize (Fin.cons x v) := by
  simp only [IFormula.ex, starRealize, not_forall, not_not]

/-- **Section 11.7.** The reading of a universal quantifier in the ultrapower. -/
theorem starRealize_all {k : ℕ} (φ : IFormula α (k + 1)) (v : Fin k → αS) :
    φ.all.starRealize v ↔ ∀ x : αS, φ.starRealize (Fin.cons x v) :=
  Iff.rfl

/-- **Section 11.7.** The reading of a conjunction in the ultrapower. -/
theorem starRealize_and {k : ℕ} (φ ψ : IFormula α k) (v : Fin k → αS) :
    (φ.and ψ).starRealize v ↔ φ.starRealize v ∧ ψ.starRealize v :=
  Iff.rfl

/-- **Section 11.7.** The reading of a negation in the ultrapower. -/
theorem starRealize_not {k : ℕ} (φ : IFormula α k) (v : Fin k → αS) :
    φ.not.starRealize v ↔ ¬ φ.starRealize v :=
  Iff.rfl

/-- **Section 11.7.** In the ultrapower, the atomic formula for membership of variable $`i`
in $`[A_n]` says that the value of the variable belongs to the internal set. -/
theorem starRealize_mem {k : ℕ} (i : Fin k) (A : ℕ → Set α) (v : Fin k → αS) :
    (mem i A).starRealize v ↔ v i ∈ internalSet A := by
  obtain ⟨r, rfl⟩ := exists_rep_fun (α := α) v
  rw [mem, starRealize, internalRelN_ofSeq, ofSeq_mem_internalSet]

/-- **Section 11.7.** In the ultrapower, the atomic formula for a binary internal relation
between variables $`i` and $`j` says that their values are related by it. -/
theorem starRealize_rel₂ {k : ℕ} (i j : Fin k) (R : ℕ → α → α → Prop) (v : Fin k → αS) :
    (rel₂ i j R).starRealize v ↔ internalRel R (v i) (v j) := by
  obtain ⟨r, rfl⟩ := exists_rep_fun (α := α) v
  rw [rel₂, starRealize, internalRelN_ofSeq, internalRel_ofSeq]

/-- **Section 11.7, the transfer principle (†) for internal sets.** A sentence holds in the
ultrapower if and only if its standard reading holds at almost all indices. In particular a
sentence about a set symbol that is true for every set of standard elements is true for every
internal set. -/
theorem starRealize_sentence (φ : IFormula α 0) (v : Fin 0 → αS) :
    φ.starRealize v ↔ ∀ᶠ n in hyperfilter ℕ, φ.realize n Fin.elim0 := by
  have e : v = fun i => (ofSeq ((Fin.elim0 : Fin 0 → ℕ → α) i) : αS) := Subsingleton.elim _ _
  rw [e, starRealize_ofSeq]
  refine eventually_congr (Eventually.of_forall fun n => ?_)
  rw [show (fun i => (Fin.elim0 : Fin 0 → ℕ → α) i n) = Fin.elim0 from Subsingleton.elim _ _]

/-- **Section 11.7, the transfer principle (†) for internal sets.** A sentence whose standard
reading is true at every index is true in the ultrapower. -/
theorem starRealize_of_forall_realize (φ : IFormula α 0)
    (h : ∀ n, φ.realize n Fin.elim0) (v : Fin 0 → αS) : φ.starRealize v :=
  (starRealize_sentence φ v).2 (Eventually.of_forall h)

/-- **Theorem 11.7.1** (internal set definition principle), with the defining sequence. For a
formula $`\varphi(x_0, x_1, \dots, x_k)` and parameters $`c_1 = [c^1_n], \dots,
c_k = [c^k_n]`, the set of $`b` with $`\varphi(b, c_1, \dots, c_k)` in the ultrapower is the
internal set $`[B_n]`, where $`B_n` is the set of standard $`a` such that the reading of
$`\varphi` at index $`n` holds of $`a, c^1_n, \dots, c^k_n`. -/
theorem setOf_starRealize_eq_internalSet {k : ℕ} (φ : IFormula α (k + 1))
    (c : Fin k → ℕ → α) :
    {b : αS | φ.starRealize (Fin.cons b fun i => (ofSeq (c i) : αS))} =
      internalSet fun n => {a | φ.realize n (Fin.cons a fun i => c i n)} := by
  ext x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := α) x
  rw [mem_ofPred_eq, cons_ofSeq, starRealize_ofSeq, ofSeq_mem_internalSet]
  refine eventually_congr (Eventually.of_forall fun n => ?_)
  rw [cons_apply_seq]
  rfl

/-- **Theorem 11.7.1** (internal set definition principle). Let $`\varphi(x_0, \dots, x_k)`
be a first-order formula over internal relations, in particular one that mentions internal
sets $`X_1, \dots, X_m`, and let $`c_1, \dots, c_k` be elements of the ultrapower. Then
$`\{b : \varphi(b, c_1, \dots, c_k)\}` is an internal set. -/
theorem isInternalSet_setOf_starRealize {k : ℕ} (φ : IFormula α (k + 1)) (c : Fin k → αS) :
    IsInternalSet α {b : αS | φ.starRealize (Fin.cons b c)} := by
  obtain ⟨c, rfl⟩ := exists_rep_fun (α := α) c
  exact ⟨_, setOf_starRealize_eq_internalSet φ c⟩

end IFormula

end Formulas

/-!
### Using the principle

The examples of Section 11.1 can be recovered from the principle, as the book remarks: an
open interval is defined by the formula $`x_1 < x_0 \wedge x_0 < x_2`. The first substantial
application is the proof that an internal set of real numbers must be finite.
-/

section Applications

/-- **Section 11.7.** The order of the hyperreals is the internal relation of the constant
sequence of the order of the reals. -/
theorem internalRel_lt {x y : ℝ*} : internalRel (fun _ (a b : ℝ) => a < b) x y ↔ x < y := by
  rw [← starRel₂_iff_internalRel]
  exact starRel₂_lt

/-- **Section 11.7.** The weak order of the hyperreals is the internal relation of the
constant sequence of the weak order of the reals. -/
theorem internalRel_le {x y : ℝ*} : internalRel (fun _ (a b : ℝ) => a ≤ b) x y ↔ x ≤ y := by
  rw [← starRel₂_iff_internalRel]
  exact starRel₂_le

/-- **Section 11.7, second example after the principle; Exercise 11.7.1.** The open interval
$`(a, b)` is internal because it is defined by the formula $`x_1 < x_0 \wedge x_0 < x_2` with
the parameters $`a, b`. This is {name}`Goldblatt.isInternal_Ioo` again, now obtained from the
internal set definition principle. -/
theorem isInternal_Ioo_of_definition (a b : ℝ*) : IsInternal (Ioo a b) := by
  have h := IFormula.isInternalSet_setOf_starRealize (α := ℝ)
    ((IFormula.rel₂ 1 0 fun _ x y => x < y).and (IFormula.rel₂ 0 2 fun _ x y => x < y)) ![a, b]
  have e : {x : ℝ* | ((IFormula.rel₂ 1 0 fun _ (x y : ℝ) => x < y).and
      (IFormula.rel₂ 0 2 fun _ x y => x < y)).starRealize (Fin.cons x ![a, b])} = Ioo a b := by
    ext x
    simp only [mem_ofPred_eq, IFormula.starRealize_and, IFormula.starRealize_rel₂,
      internalRel_lt, mem_Ioo]
    exact Iff.rfl
  rwa [e] at h

/-- **Section 11.7, the formula discussed before the principle.** For an internal set $`X`
and a hyperreal $`c`, the set of $`b` such that every $`z` strictly between $`b` and $`c`
belongs to $`X` is internal: it is defined by the formula
$`\forall z\,(x_0 < z \wedge z < x_1 \to z \in X)`. -/
theorem IsInternal.isInternal_setOf_Ioo_subset {X : Set ℝ*} (hX : IsInternal X) (c : ℝ*) :
    IsInternal {b : ℝ* | ∀ z, b < z → z < c → z ∈ X} := by
  obtain ⟨A, rfl⟩ := hX
  have h := IFormula.isInternalSet_setOf_starRealize (α := ℝ)
    (IFormula.all (((IFormula.rel₂ 1 0 fun _ x y => x < y).and
      (IFormula.rel₂ 0 2 fun _ x y => x < y)).imp (IFormula.mem 0 A))) ![c]
  have e : {b : ℝ* | (IFormula.all (((IFormula.rel₂ 1 0 fun _ (x y : ℝ) => x < y).and
      (IFormula.rel₂ 0 2 fun _ x y => x < y)).imp (IFormula.mem 0 A))).starRealize
        (Fin.cons b ![c])} = {b : ℝ* | ∀ z, b < z → z < c → z ∈ internalSet A} := by
    ext b
    simp only [mem_ofPred_eq, IFormula.starRealize_all, IFormula.starRealize_imp,
      IFormula.starRealize_and, IFormula.starRealize_rel₂, IFormula.starRealize_mem,
      internalRel_lt, and_imp]
    exact Iff.rfl
  rwa [e] at h

/-- **Section 11.7.** Every internal set of real numbers is finite; equivalently, every
infinite set of reals is external. The proof is the book's. An infinite set $`A` contains the
range $`X` of an injective sequence $`f`, and $`X` is internal with $`A`. The set of
hypernaturals $`n` with $`{}^*f(n) \in X` is then internal by internal set definition, but
since $`f` is injective this set is the external set of standard natural numbers. -/
theorem finite_of_isInternal_image_coe {A : Set ℝ} (hA : IsInternal (((↑) : ℝ → ℝ*) '' A)) :
    A.Finite := by
  by_contra hinf
  obtain ⟨f, hf, hfA⟩ : ∃ f : ℕ → ℝ, Function.Injective f ∧ range f ⊆ A := by
    have : Infinite A := Set.infinite_coe_iff.2 hinf
    exact ⟨fun n => (Infinite.natEmbedding A n : ℝ),
      fun m n h => (Infinite.natEmbedding A).injective (Subtype.ext h),
      by rintro _ ⟨n, rfl⟩; exact (Infinite.natEmbedding A n).2⟩
  obtain ⟨C, hC⟩ := hA.image_coe_subset hfA
  let g : ℝ → ℝ := fun r => f ⌊r⌋₊
  have hB : IsInternal {x : ℝ* | x ∈ ℕ* ∧ ⋆g x ∈ (((↑) : ℝ → ℝ*) '' range f)} := by
    refine ⟨fun n => {a | a ∈ range ((↑) : ℕ → ℝ) ∧ g a ∈ C n}, ?_⟩
    ext x
    obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
    rw [hC]
    simp only [mem_ofPred_eq, hyperNat, hyperreal_ofSeq_mem_starSet, starMap_hyperreal_ofSeq,
      hyperreal_ofSeq_mem_internalSet, almostAll_and]
  refine isExternal_range_natCast ?_
  have e : {x : ℝ* | x ∈ ℕ* ∧ ⋆g x ∈ (((↑) : ℝ → ℝ*) '' range f)} = range ((↑) : ℕ → ℝ*) := by
    ext x
    constructor
    · rintro ⟨hx, _, ⟨m, rfl⟩, hm⟩
      obtain ⟨κ, rfl⟩ := exists_hnat_eq hx
      have h1 : Hyperreal.ofSeq (fun _ => f m) = Hyperreal.ofSeq fun n => g (κ n) := hm
      have h2 : ∀ᶠ n in hyperfilter ℕ, m = κ n := (ofSeq_eq_ofSeq_iff.1 h1).mono fun n hn => by
        have : f m = f ⌊(κ n : ℝ)⌋₊ := hn
        rw [Nat.floor_natCast] at this
        exact hf this
      exact ⟨m, by rw [natCast_eq_hnat, hnat_eq_hnat_iff]; exact h2⟩
    · rintro ⟨n, rfl⟩
      refine ⟨natCast_mem_hyperNat n, f n, ⟨n, rfl⟩, ?_⟩
      change ((f n : ℝ) : ℝ*) = ⋆g ((n : ℝ) : ℝ*)
      rw [starMap_coe]
      simp only [g, Nat.floor_natCast]
  rwa [e] at hB

/-- **Section 11.7.** Every infinite set of real numbers is external. -/
theorem isExternal_image_coe_of_infinite {A : Set ℝ} (hA : A.Infinite) :
    IsExternal (((↑) : ℝ → ℝ*) '' A) :=
  fun h => hA (finite_of_isInternal_image_coe h)

/-- **Section 11.7.** A set of real numbers is internal, as a set of hyperreals, if and only
if it is finite. -/
theorem isInternal_image_coe_iff {A : Set ℝ} : IsInternal (((↑) : ℝ → ℝ*) '' A) ↔ A.Finite :=
  ⟨finite_of_isInternal_image_coe, isInternal_image_coe_of_finite⟩

end Applications

/-!
## 11.8 The Underflow Principle

Underflow is the order-theoretic dual of overflow: an internal set that contains all
unlimited hypernaturals below some unlimited $`K` cannot stop exactly where the unlimited
numbers stop, and so contains all standard natural numbers from some point on. The proof
applies the least number principle to the set of $`k` for which the whole segment from $`k`
to $`K` lies in the given set, and it is the internal set definition principle that shows
this set of $`k` to be internal.
-/

section Underflow

/-- **Theorem 11.8.1, the definable set.** For an internal set $`X` and a hyperreal $`K`,
the set of hypernaturals $`k \le K` such that every hypernatural $`z` with $`k \le z \le K`
belongs to $`X` is internal. It is defined by the formula
$`x \in \mathbb N \wedge x \le y \wedge \forall z \in \mathbb N\,(x \le z \le y \to z \in A)`. -/
theorem IsInternal.isInternal_setOf_segment_subset {X : Set ℝ*} (hX : IsInternal X) (K : ℝ*) :
    IsInternal {k : ℝ* | k ∈ ℕ* ∧ k ≤ K ∧ ∀ z ∈ ℕ*, k ≤ z → z ≤ K → z ∈ X} := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨κ, rfl⟩ := hyperreal_exists_rep K
  refine ⟨fun n => {a | a ∈ range ((↑) : ℕ → ℝ) ∧ a ≤ κ n ∧
    ∀ z ∈ range ((↑) : ℕ → ℝ), a ≤ z → z ≤ κ n → z ∈ A n}, ?_⟩
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [hyperreal_ofSeq_mem_internalSet]
  simp only [mem_ofPred_eq, almostAll_and]
  refine and_congr hyperreal_ofSeq_mem_starSet (and_congr ofSeq_le_ofSeq_iff ?_)
  refine hyperreal_forall_iff fun s => ?_
  simp only [hyperNat, hyperreal_ofSeq_mem_starSet, ofSeq_le_ofSeq_iff,
    hyperreal_ofSeq_mem_internalSet, almostAll_imp]

/-- **Theorem 11.8.1** (underflow). Let $`X` be an internal set and $`K` an unlimited
hypernatural. If every unlimited hypernatural $`H \le K` belongs to $`X`, then there is a
natural number $`k` such that every standard natural number $`n \ge k` belongs to $`X`. As
for overflow, the book's hypothesis that $`X` consists of hypernaturals is not needed. -/
theorem IsInternal.underflow {X : Set ℝ*} (hX : IsInternal X) {K : ℝ*} (hK : K ∈ ℕ*)
    (hKU : Unlimited K) (h : ∀ H ∈ ℕ*, Unlimited H → H ≤ K → H ∈ X) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → (n : ℝ*) ∈ X := by
  obtain ⟨k, ⟨hkN, hkK, hk⟩, hmin⟩ := (hX.isInternal_setOf_segment_subset K).exists_isLeast
    (fun x hx => hx.1) ⟨K, hK, le_rfl, fun z hz h1 h2 => by
      rw [le_antisymm h2 h1]
      exact h K hK hKU le_rfl⟩
  have hkL : Limited k := by
    by_contra hkU
    rw [not_limited_iff_unlimited] at hkU
    have hk1 := sub_one_mem_hyperNat hkN hkU.ne_zero
    have hk1U : Unlimited (k - 1) := by
      rw [sub_eq_add_neg]
      exact hkU.add_limited limited_one.neg
    have hmem : k - 1 ∈ {k : ℝ* | k ∈ ℕ* ∧ k ≤ K ∧ ∀ z ∈ ℕ*, k ≤ z → z ≤ K → z ∈ X} :=
      ⟨hk1, by linarith, fun z hz h1 h2 =>
        h z hz ((posUnlimited_of_mem_hyperNat hk1 hk1U).of_le h1).unlimited h2⟩
    have := hmin hmem
    linarith
  obtain ⟨m, rfl⟩ := (limited_hyperNat_iff hkN).1 hkL
  exact ⟨m, fun n hn => hk n (natCast_mem_hyperNat n) (by exact_mod_cast hn)
    (posUnlimited_of_mem_hyperNat hK hKU n).le⟩

/-- **Exercise 11.8.2.** The underflow principle, as a property of a class of sets of
hyperreals. -/
def UnderflowPrinciple (𝒞 : Set (Set ℝ*)) : Prop :=
  ∀ X ∈ 𝒞, ∀ K ∈ ℕ*, Unlimited K → (∀ H ∈ ℕ*, Unlimited H → H ≤ K → H ∈ X) →
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → (n : ℝ*) ∈ X

/-- **Exercise 11.8.2.** The second statement of the exercise, as a property of a class of
sets: a member of the class that contains arbitrarily large standard natural numbers contains
arbitrarily small unlimited hypernaturals. -/
def SmallUnlimitedPrinciple (𝒞 : Set (Set ℝ*)) : Prop :=
  ∀ X ∈ 𝒞, (∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ (n : ℝ*) ∈ X) →
    ∀ K ∈ ℕ*, Unlimited K → ∃ H ∈ X, H ∈ ℕ* ∧ Unlimited H ∧ H ≤ K

/-- **Exercise 11.8.2.** Underflow is equivalent to the statement that a set with arbitrarily
large limited members has arbitrarily small unlimited members. As in Exercise 11.4.2, the
equivalence is proved for an arbitrary class of sets closed under complementation relative to
the hypernaturals. -/
theorem underflowPrinciple_iff_smallUnlimitedPrinciple {𝒞 : Set (Set ℝ*)}
    (h𝒞 : ∀ X ∈ 𝒞, ℕ* \ X ∈ 𝒞) : UnderflowPrinciple 𝒞 ↔ SmallUnlimitedPrinciple 𝒞 := by
  constructor
  · intro hU X hX hlarge K hK hKU
    by_contra hno
    push Not at hno
    obtain ⟨k, hk⟩ := hU _ (h𝒞 X hX) K hK hKU fun H hH hHU hHK =>
      ⟨hH, fun hHX => absurd hHK (not_le.2 (hno H hHX hH hHU))⟩
    obtain ⟨n, hn, hnX⟩ := hlarge k
    exact (hk n hn).2 hnX
  · intro hS X hX K hK hKU h
    by_contra hno
    push Not at hno
    obtain ⟨H, hHX, hH, hHU, hHK⟩ := hS _ (h𝒞 X hX)
      (fun k => by
        obtain ⟨n, hn, hnX⟩ := hno k
        exact ⟨n, hn, natCast_mem_hyperNat n, hnX⟩) K hK hKU
    exact hHX.2 (h H hH hHU hHK)

/-- **Theorem 11.8.1**, restated: the class of internal sets has the underflow property. -/
theorem underflowPrinciple_isInternal : UnderflowPrinciple {X | IsInternal X} :=
  fun _ hX _ hK hKU h => IsInternal.underflow hX hK hKU h

/-- **Exercise 11.8.2.** An internal set that contains arbitrarily large standard natural
numbers contains arbitrarily small unlimited hypernaturals. -/
theorem IsInternal.exists_unlimited_le_mem {X : Set ℝ*} (hX : IsInternal X)
    (h : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ (n : ℝ*) ∈ X) {K : ℝ*} (hK : K ∈ ℕ*) (hKU : Unlimited K) :
    ∃ H ∈ X, H ∈ ℕ* ∧ Unlimited H ∧ H ≤ K :=
  (underflowPrinciple_iff_smallUnlimitedPrinciple (𝒞 := {X | IsInternal X})
    (fun _ hX => isInternal_hyperNat.diff hX)).1 underflowPrinciple_isInternal X hX h K hK hKU

/-- **Exercise 11.8.2, the deduction.** If $`A` is an infinite set of natural numbers, then
its enlargement contains arbitrarily small unlimited members: below every unlimited
hypernatural there is an unlimited member of $`{}^*A`. -/
theorem exists_unlimited_mem_starSet_le {A : Set ℕ} (hA : A.Infinite) {K : ℝ*} (hK : K ∈ ℕ*)
    (hKU : Unlimited K) : ∃ H ∈ ⋆(((↑) : ℕ → ℝ) '' A), Unlimited H ∧ H ≤ K := by
  obtain ⟨H, hH, -, hHU, hHK⟩ := IsInternal.exists_unlimited_le_mem
    (isInternalSet_starSet (((↑) : ℕ → ℝ) '' A)) (fun k => by
      obtain ⟨n, hn, hkn⟩ := hA.exists_gt k
      exact ⟨n, hkn.le, coe_mem_starSet.2 ⟨n, hn, rfl⟩⟩) hK hKU
  exact ⟨H, hH, hHU, hHK⟩

end Underflow

/-!
## 11.9 Internal Sets and Permanence

A _permanence principle_ says that a property that defines an internal set cannot hold of
exactly the members of an external set: if it holds throughout an external set, it continues
to hold on a strictly larger internal one. Overflow and underflow are of this kind (the
external set is the set of standard natural numbers, or of unlimited hypernaturals), and so
are the spillover results of Exercise 11.5.2 and Section 11.6 (the external set is the set of
limited numbers, or of infinitesimals). So is universal transfer, in which a property passes
from the external set of reals to the internal set of all hyperreals. The theorem of this
section is the permanence principle for halos, around an arbitrary hyperreal point.
-/

section Permanence

/-- **Theorem 11.9.1, the definable set.** For an internal set $`X` and a hyperreal $`b`,
the set of hypernaturals $`k` such that the interval $`(b - \tfrac1k, b + \tfrac1k)` is
included in $`X` is internal. It is defined by the formula
$`x \in \mathbb N \wedge \forall z\,(|z - y| < \tfrac1x \to z \in A)`. -/
theorem IsInternal.isInternal_setOf_ball_subset {X : Set ℝ*} (hX : IsInternal X) (b : ℝ*) :
    IsInternal {k : ℝ* | k ∈ ℕ* ∧ ∀ z : ℝ*, |z - b| < 1 / k → z ∈ X} := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨β, rfl⟩ := hyperreal_exists_rep b
  refine ⟨fun n => {a | a ∈ range ((↑) : ℕ → ℝ) ∧ ∀ z : ℝ, |z - β n| < 1 / a → z ∈ A n}, ?_⟩
  ext x
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [hyperreal_ofSeq_mem_internalSet]
  simp only [mem_ofPred_eq, almostAll_and]
  refine and_congr hyperreal_ofSeq_mem_starSet (hyperreal_forall_iff fun s => ?_)
  have e1 : |Hyperreal.ofSeq s - Hyperreal.ofSeq β| = Hyperreal.ofSeq fun n => |s n - β n| :=
    abs_ofSeq _
  have e2 : (1 : ℝ*) / Hyperreal.ofSeq r = Hyperreal.ofSeq fun n => 1 / r n := rfl
  rw [e1, e2, ofSeq_lt_ofSeq_iff, hyperreal_ofSeq_mem_internalSet, almostAll_imp]

/-- **Theorem 11.9.1** (permanence for halos). If an internal set $`X` contains every point
infinitely close to the hyperreal $`b`, then there is a positive real $`\varepsilon` such
that $`X` contains every point within $`\varepsilon` of $`b`. -/
theorem IsInternal.exists_real_ball_subset {X : Set ℝ*} (hX : IsInternal X) {b : ℝ*}
    (h : hal b ⊆ X) : ∃ e : ℝ, 0 < e ∧ ∀ x : ℝ*, |x - b| < e → x ∈ X := by
  obtain ⟨k, hk⟩ := (hX.isInternal_setOf_ball_subset b).underflow omega_mem_hyperNat
    unlimited_omega fun H hH hHU _ => ⟨hH, fun z hz => h (by
      have hI : Infinitesimal (1 / H) := by
        rw [one_div]
        exact hHU.inv_infinitesimal
      have hz' : Infinitesimal (z - b) :=
        hI.of_abs_le (hz.le.trans (le_abs_self _))
      rw [mem_hal, infClose_iff, ← neg_sub]
      exact hz'.neg)⟩
  have hk1 := (hk (k + 1) (Nat.le_succ k)).2
  refine ⟨1 / ((k : ℝ) + 1), by positivity, fun x hx => hk1 x ?_⟩
  have e : ((1 / ((k : ℝ) + 1) : ℝ) : ℝ*) = 1 / ((k + 1 : ℕ) : ℝ*) := by
    push_cast
    rfl
  rwa [e] at hx

end Permanence

end Goldblatt
