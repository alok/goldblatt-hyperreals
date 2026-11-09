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
  standard relations and conditions on values of extended functions are all atomic in this
  language: the atoms {lit}`Goldblatt.IFormula.mem`, {lit}`Goldblatt.IFormula.star`,
  {lit}`Goldblatt.IFormula.memMap`, {lit}`Goldblatt.IFormula.rel₂Map` and
  {lit}`Goldblatt.IFormula.relTerms` come with lemmas that read them in the ultrapower as
  membership in an internal set, as the enlargement of a standard relation in the sense of
  Chapter 3, and as internal relations between values of extended functions. So the language
  covers the formulas of the book, and the definable sets used later in the chapter are
  obtained from it.
* The transfer principle for sentences with set symbols, marked with a dagger in the book, is
  proved for a second small language {lit}`Goldblatt.SFormula` that has set symbols in
  addition: a formula that holds of all sets of standard elements holds of all internal sets
  ({lit}`Goldblatt.SFormula.starRealize_of_forall_realize`).
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

/-- **Section 11.7.** Equality in the ultrapower is the internal relation of the constant
sequence of the equality of the standard type. -/
theorem internalRel_eq {x y : αS} : internalRel (fun _ (a b : α) => a = b) x y ↔ x = y := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := α) y
  rw [internalRel_ofSeq, Ultrapower.ofSeq_eq_ofSeq]

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

/-- **Section 11.7.** The internal relation of a constant sequence is the enlargement of the
standard relation, in the sense of Chapter 3: for a relation $`P` of finite arity on the
standard type, the internal relation defined by the sequence $`(P, P, P, \dots)` is
$`{}^*P`. -/
theorem internalRelN_const_iff_starRel {ι : Type*} [Finite ι] {P : Set (ι → α)} {x : ι → αS} :
    internalRelN (fun _ v => v ∈ P) x ↔ x ∈ starRel P := by
  obtain ⟨r, rfl⟩ := exists_rep_fun (α := α) x
  rw [internalRelN_ofSeq, starRel_ofSeq]

/-- **Section 11.7.** Substituting standard functions of the variables into an internal
relation: the internal relation defined by the relations
$`R_n(t_1(\vec a), \dots, t_m(\vec a))` holds of a tuple $`\vec x` of the ultrapower if and
only if the internal relation $`[R_n]` holds of the values
$`{}^*t_1(\vec x), \dots, {}^*t_m(\vec x)` of the extended functions. -/
theorem internalRelN_comp_starMapN {ι κ : Type*} [Finite ι] [Finite κ]
    (R : ℕ → (κ → α) → Prop) (t : κ → (ι → α) → α) (x : ι → αS) :
    internalRelN (fun n v => R n fun j => t j v) x ↔
      internalRelN R fun j => (starMapN (t j) x : αS) := by
  obtain ⟨r, rfl⟩ := exists_rep_fun (α := α) x
  have e : (fun j => (starMapN (t j) (fun i => (ofSeq (r i) : αS)) : αS)) =
      fun j => ofSeq fun n => t j fun i => r i n := funext fun j => starMapN_ofSeq (t j) r
  rw [e, internalRelN_ofSeq, internalRelN_ofSeq]

/-- **Section 11.7, the almost-all criterion for ternary internal relations**, for a triple
written out as a vector. -/
theorem internalRelN_vec₃ {R : ℕ → (Fin 3 → α) → Prop} {a b c : ℕ → α} :
    internalRelN R ![(ofSeq a : αS), ofSeq b, ofSeq c] ↔
      ∀ᶠ n in hyperfilter ℕ, R n ![a n, b n, c n] := by
  have e : (![(ofSeq a : αS), ofSeq b, ofSeq c] : Fin 3 → αS) =
      fun i => ofSeq ((![a, b, c] : Fin 3 → ℕ → α) i) := by
    funext i
    fin_cases i <;> rfl
  rw [e, internalRelN_ofSeq]
  refine eventually_congr (Eventually.of_forall fun n => ?_)
  have e' : (fun i => (![a, b, c] : Fin 3 → ℕ → α) i n) = ![a n, b n, c n] := by
    funext i
    fin_cases i <;> rfl
  rw [e']

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

/-- The atomic formula given by a standard relation $`P` between the variables. In the
ultrapower it is read as the enlargement $`{}^*P`. -/
def star {k : ℕ} (P : Set (Fin k → α)) : IFormula α k := .rel fun _ v => v ∈ P

/-- The atomic formula obtained from an internal relation $`[R_n]` of arity $`m` by
substituting the terms $`t_1, \dots, t_m`, which are standard functions of the variables. -/
def relTerms {k m : ℕ} (R : ℕ → (Fin m → α) → Prop) (t : Fin m → (Fin k → α) → α) :
    IFormula α k := .rel fun n v => R n fun j => t j v

/-- The atomic formula saying that the value of the standard function $`f` at variable $`i`
belongs to the internal set $`[A_n]`. -/
def memMap {k : ℕ} (i : Fin k) (f : α → α) (A : ℕ → Set α) : IFormula α k :=
  .rel fun n v => f (v i) ∈ A n

/-- The atomic formula saying that the values of the standard functions $`f` at variable
$`i` and $`g` at variable $`j` are related by the binary internal relation $`[R_n]`. -/
def rel₂Map {k : ℕ} (i j : Fin k) (f g : α → α) (R : ℕ → α → α → Prop) : IFormula α k :=
  .rel fun n v => R n (f (v i)) (g (v j))

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

/-- The formula that is false at every index. -/
def falsum {k : ℕ} : IFormula α k := .rel fun _ _ => False

/-- **Section 11.7.** The false formula is false in the ultrapower. -/
theorem starRealize_falsum {k : ℕ} (v : Fin k → αS) :
    ¬ (falsum : IFormula α k).starRealize v := by
  obtain ⟨r, rfl⟩ := exists_rep_fun (α := α) v
  rw [falsum, starRealize, internalRelN_ofSeq, eventually_const]
  exact id

/-- The disjunction $`\varphi_1 \vee \dots \vee \varphi_n` of a finite list of formulas; the
empty disjunction is the false formula. -/
def disj {k : ℕ} : List (IFormula α k) → IFormula α k
  | [] => falsum
  | φ :: l => φ.or (disj l)

/-- **Section 11.7.** A finite disjunction holds in the ultrapower exactly when one of its
members does. -/
theorem starRealize_disj {k : ℕ} (l : List (IFormula α k)) (v : Fin k → αS) :
    (disj l).starRealize v ↔ ∃ φ ∈ l, φ.starRealize v := by
  induction l with
  | nil => simp only [disj, starRealize_falsum, List.not_mem_nil, false_and, exists_false]
  | cons φ l ih =>
    rw [disj, starRealize_or, ih]
    simp only [List.mem_cons, exists_eq_or_imp]

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

/-- **Section 11.7.** In the ultrapower an atomic formula is read as the internal relation of
its sequence of relations. -/
theorem starRealize_rel {k : ℕ} (R : ℕ → (Fin k → α) → Prop) (v : Fin k → αS) :
    (IFormula.rel R).starRealize v ↔ internalRelN R v :=
  Iff.rfl

/-- **Section 11.7.** In the ultrapower, the atomic formula of a standard relation $`P` says
that the values of the variables are related by the enlargement $`{}^*P` of Chapter 3
({name}`Goldblatt.starRel`). -/
theorem starRealize_star {k : ℕ} (P : Set (Fin k → α)) (v : Fin k → αS) :
    (star P).starRealize v ↔ v ∈ starRel P :=
  internalRelN_const_iff_starRel

/-- **Section 11.7.** In the ultrapower, an atomic formula with terms says that the values of
the extended terms ({name}`Goldblatt.starMapN`) are related by the internal relation. -/
theorem starRealize_relTerms {k m : ℕ} (R : ℕ → (Fin m → α) → Prop)
    (t : Fin m → (Fin k → α) → α) (v : Fin k → αS) :
    (relTerms R t).starRealize v ↔ internalRelN R fun j => (starMapN (t j) v : αS) :=
  internalRelN_comp_starMapN R t v

/-- **Section 11.7.** In the ultrapower, the atomic formula $`f(x_i) \in A` says that the
value of the extended function $`{}^*f` at the variable belongs to the internal set
$`[A_n]`. -/
theorem starRealize_memMap {k : ℕ} (i : Fin k) (f : α → α) (A : ℕ → Set α) (v : Fin k → αS) :
    (memMap i f A).starRealize v ↔ (starMap f (v i) : αS) ∈ internalSet A := by
  obtain ⟨r, rfl⟩ := exists_rep_fun (α := α) v
  rw [memMap, starRealize, internalRelN_ofSeq, starMap_ofSeq, ofSeq_mem_internalSet]
  rfl

/-- **Section 11.7.** In the ultrapower, the atomic formula $`R(f(x_i), g(x_j))` says that
the values of the extended functions $`{}^*f` and $`{}^*g` at the variables are related by
the internal relation $`[R_n]`. -/
theorem starRealize_rel₂Map {k : ℕ} (i j : Fin k) (f g : α → α) (R : ℕ → α → α → Prop)
    (v : Fin k → αS) :
    (rel₂Map i j f g R).starRealize v ↔
      internalRel R (starMap f (v i) : αS) (starMap g (v j) : αS) := by
  obtain ⟨r, rfl⟩ := exists_rep_fun (α := α) v
  rw [rel₂Map, starRealize, internalRelN_ofSeq, starMap_ofSeq, starMap_ofSeq, internalRel_ofSeq]
  rfl

/-- **Section 11.7, the equivalence of (i) and (ii) for sentences.** A sentence over internal
relations holds in the ultrapower if and only if its standard reading holds at almost all
indices. Here the internal sets that the sentence mentions are part of the sentence; the
transfer principle marked with a dagger in the book, in which a set symbol ranges over all
sets on one side and over all internal sets on the other, is
{lit}`Goldblatt.SFormula.starRealize_of_forall_realize` below. -/
theorem starRealize_sentence (φ : IFormula α 0) (v : Fin 0 → αS) :
    φ.starRealize v ↔ ∀ᶠ n in hyperfilter ℕ, φ.realize n Fin.elim0 := by
  have e : v = fun i => (ofSeq ((Fin.elim0 : Fin 0 → ℕ → α) i) : αS) := Subsingleton.elim _ _
  rw [e, starRealize_ofSeq]
  refine eventually_congr (Eventually.of_forall fun n => ?_)
  rw [show (fun i => (Fin.elim0 : Fin 0 → ℕ → α) i n) = Fin.elim0 from Subsingleton.elim _ _]

/-- **Section 11.7, the equivalence of (i) and (ii) for sentences.** A sentence whose
standard reading is true at every index is true in the ultrapower. -/
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

/-- **Theorem 11.7.1** (internal set definition principle), in the form in which it is
applied: a set whose membership condition is the reading in the ultrapower of a formula, with
parameters from the ultrapower, is internal. -/
theorem isInternalSet_of_forall_iff {k : ℕ} (φ : IFormula α (k + 1)) (c : Fin k → αS)
    {X : Set αS} (h : ∀ x, x ∈ X ↔ φ.starRealize (Fin.cons x c)) : IsInternalSet α X := by
  have e : X = {b : αS | φ.starRealize (Fin.cons b c)} := Set.ext h
  rw [e]
  exact isInternalSet_setOf_starRealize φ c

end IFormula

/-!
### Formulas with set symbols and the transfer principle for internal sets

In a formula of the previous kind the internal sets are fixed parameters. The transfer
principle that the book marks with a dagger speaks instead of a sentence $`\varphi(A)` in
which $`A` is a _set symbol_: if $`\varphi(A)` is true for every set $`A` of standard
elements, then its transform is true when the symbol is read as any internal set. To state
this, the language is extended by $`m` set symbols. A formula of the extended language has a
standard reading for each choice of $`m` sets of standard elements, and a reading in the
ultrapower for each choice of $`m` sets of elements of the ultrapower. When the latter are
internal sets $`[A^1_n], \dots, [A^m_n]`, the reading in the ultrapower is that of the
formula of the previous kind obtained by substituting the defining sequences for the set
symbols, and so it holds exactly when the standard reading with the sets
$`A^1_n, \dots, A^m_n` holds for almost all $`n`.
-/

/-- **Section 11.7.** First-order formulas with $`k` free variables and $`m` set symbols.
The atomic formulas are internal relations between the variables, as for
{name}`Goldblatt.IFormula`, and membership of a variable in a set symbol. -/
inductive SFormula (α : Type u) (m : ℕ) : ℕ → Type u
  /-- An atomic formula: a sequence of relations between the free variables. -/
  | rel {k : ℕ} (R : ℕ → (Fin k → α) → Prop) : SFormula α m k
  /-- The atomic formula saying that variable $`i` belongs to the set symbol $`j`. -/
  | mem {k : ℕ} (i : Fin k) (j : Fin m) : SFormula α m k
  /-- Negation. -/
  | not {k : ℕ} (φ : SFormula α m k) : SFormula α m k
  /-- Conjunction. -/
  | and {k : ℕ} (φ ψ : SFormula α m k) : SFormula α m k
  /-- Universal quantification over variable $`0`. -/
  | all {k : ℕ} (φ : SFormula α m (k + 1)) : SFormula α m k

namespace SFormula

variable {m : ℕ}

/-- Disjunction of formulas with set symbols. -/
def or {k : ℕ} (φ ψ : SFormula α m k) : SFormula α m k := .not (.and (.not φ) (.not ψ))

/-- Implication between formulas with set symbols. -/
def imp {k : ℕ} (φ ψ : SFormula α m k) : SFormula α m k := .not (.and φ (.not ψ))

/-- Existential quantification over variable $`0`. -/
def ex {k : ℕ} (φ : SFormula α m (k + 1)) : SFormula α m k := .not (.all (.not φ))

/-- The atomic formula saying that variable $`i` belongs to the fixed internal set
$`[A_n]`. -/
def memI {k : ℕ} (i : Fin k) (A : ℕ → Set α) : SFormula α m k := .rel fun n v => v i ∈ A n

/-- The atomic formula saying that variables $`i` and $`j` are related by the binary internal
relation $`[R_n]`. -/
def rel₂ {k : ℕ} (i j : Fin k) (R : ℕ → α → α → Prop) : SFormula α m k :=
  .rel fun n v => R n (v i) (v j)

/-- **Section 11.7.** Substitution of sequences of sets for the set symbols: the result is a
formula over internal relations, in which the set symbol $`j` has become the internal set
$`[A^j_n]`. -/
def subst : {k : ℕ} → SFormula α m k → (Fin m → ℕ → Set α) → IFormula α k
  | _, .rel R, _ => .rel R
  | _, .mem i j, A => IFormula.mem i (A j)
  | _, .not φ, A => (φ.subst A).not
  | _, .and φ ψ, A => (φ.subst A).and (ψ.subst A)
  | _, .all φ, A => (φ.subst A).all

/-- **Section 11.7.** The standard reading $`\varphi(S_1, \dots, S_m)` of a formula with set
symbols at index $`n`, for sets $`S_1, \dots, S_m` of standard elements. -/
def realize : {k : ℕ} → SFormula α m k → (Fin m → Set α) → ℕ → (Fin k → α) → Prop
  | _, .rel R, _, n, v => R n v
  | _, .mem i j, S, _, v => v i ∈ S j
  | _, .not φ, S, n, v => ¬ φ.realize S n v
  | _, .and φ ψ, S, n, v => φ.realize S n v ∧ ψ.realize S n v
  | _, .all φ, S, n, v => ∀ a : α, φ.realize S n (Fin.cons a v)

/-- **Section 11.7.** The reading $`{}^*\varphi(X_1, \dots, X_m)` of a formula with set
symbols in the ultrapower, for arbitrary sets $`X_1, \dots, X_m` of elements of the
ultrapower. -/
def starRealize : {k : ℕ} → SFormula α m k → (Fin m → Set αS) → (Fin k → αS) → Prop
  | _, .rel R, _, v => internalRelN R v
  | _, .mem i j, X, v => v i ∈ X j
  | _, .not φ, X, v => ¬ φ.starRealize X v
  | _, .and φ ψ, X, v => φ.starRealize X v ∧ ψ.starRealize X v
  | _, .all φ, X, v => ∀ x : αS, φ.starRealize X (Fin.cons x v)

/-- **Section 11.7.** The standard reading at index $`n` of a formula in which sequences of
sets have been substituted for the set symbols is the standard reading of the original
formula with the $`n`-th sets. -/
theorem realize_subst {k : ℕ} (Φ : SFormula α m k) (A : Fin m → ℕ → Set α) (n : ℕ)
    (v : Fin k → α) : (Φ.subst A).realize n v ↔ Φ.realize (fun j => A j n) n v := by
  induction Φ with
  | rel R => exact Iff.rfl
  | mem i j => exact Iff.rfl
  | not φ ih => simp only [subst, IFormula.realize, realize, ih]
  | and φ ψ ih1 ih2 => simp only [subst, IFormula.realize, realize, ih1, ih2]
  | all φ ih => simp only [subst, IFormula.realize, realize, ih]

/-- **Section 11.7.** Reading the set symbols as the internal sets $`[A^j_n]` is the same as
substituting the defining sequences. -/
theorem starRealize_internalSet {k : ℕ} (Φ : SFormula α m k) (A : Fin m → ℕ → Set α)
    (v : Fin k → αS) :
    Φ.starRealize (fun j => (internalSet (A j) : Set αS)) v ↔ (Φ.subst A).starRealize v := by
  induction Φ with
  | rel R => exact Iff.rfl
  | mem i j => exact (IFormula.starRealize_mem i (A j) v).symm
  | not φ ih => simp only [subst, IFormula.starRealize, starRealize, ih]
  | and φ ψ ih1 ih2 => simp only [subst, IFormula.starRealize, starRealize, ih1, ih2]
  | all φ ih => simp only [subst, IFormula.starRealize, starRealize, ih]

/-- **Section 11.7, the equivalence of (i) and (ii), with set symbols.** The sentence
$`{}^*\varphi([r^1_n], \dots, [r^k_n], [A^1_n], \dots, [A^m_n])` is true if and only if
$`\varphi(r^1_n, \dots, r^k_n, A^1_n, \dots, A^m_n)` is true for almost all $`n`. -/
theorem starRealize_internalSet_ofSeq {k : ℕ} (Φ : SFormula α m k) (A : Fin m → ℕ → Set α)
    (r : Fin k → ℕ → α) :
    Φ.starRealize (fun j => (internalSet (A j) : Set αS)) (fun i => (ofSeq (r i) : αS)) ↔
      ∀ᶠ n in hyperfilter ℕ, Φ.realize (fun j => A j n) n fun i => r i n := by
  rw [starRealize_internalSet, IFormula.starRealize_ofSeq]
  exact eventually_congr (Eventually.of_forall fun n => realize_subst Φ A n _)

/-- **Section 11.7, the transfer principle marked with a dagger.** If $`\varphi(A)` is true
whenever the set symbol $`A` is read as an arbitrary set of standard elements, then
$`{}^*\varphi(X)` is true whenever it is read as an arbitrary internal set. The statement is
proved for any number of set symbols and for formulas with free variables (a formula true of
all standard elements is true of all elements of the ultrapower), of which the book's
statement about sentences with one set symbol is the case $`m = 1`, $`k = 0`. Atomic formulas
may be sequences of relations, so the hypothesis asks for truth at every index; for a formula
whose atoms are standard relations, that is, constant sequences, the index plays no role and
the hypothesis is literally that $`\varphi(A)` is true for all $`A`. -/
theorem starRealize_of_forall_realize {k : ℕ} (Φ : SFormula α m k)
    (h : ∀ (S : Fin m → Set α) (n : ℕ) (a : Fin k → α), Φ.realize S n a)
    {X : Fin m → Set αS} (hX : ∀ j, IsInternalSet α (X j)) (v : Fin k → αS) :
    Φ.starRealize X v := by
  choose A hA using hX
  obtain ⟨r, rfl⟩ := exists_rep_fun (α := α) v
  have e : X = fun j => (internalSet (A j) : Set αS) := funext hA
  rw [e, starRealize_internalSet_ofSeq]
  exact Eventually.of_forall fun n => h _ n _

/-- **Theorem 11.7.1** (internal set definition principle), with set symbols. This is the
statement in the shape the book gives it: for a formula
$`\varphi(x_0, \dots, x_k, A_1, \dots, A_m)` with set symbols, hyperreals (here, elements
of the ultrapower) $`c_1, \dots, c_k` and _arbitrary_ internal sets $`X_1, \dots, X_m`, the
set $`\{b : {}^*\varphi(b, c_1, \dots, c_k, X_1, \dots, X_m)\}` is internal. It follows from
the version for formulas over internal relations
({name}`Goldblatt.IFormula.isInternalSet_setOf_starRealize`) by substituting defining
sequences of the $`X_j` for the set symbols. -/
theorem isInternalSet_setOf_starRealize {k : ℕ} (Φ : SFormula α m (k + 1))
    {X : Fin m → Set αS} (hX : ∀ j, IsInternalSet α (X j)) (c : Fin k → αS) :
    IsInternalSet α {b : αS | Φ.starRealize X (Fin.cons b c)} := by
  choose A hA using hX
  have e : X = fun j => (internalSet (A j) : Set αS) := funext hA
  subst e
  simp only [starRealize_internalSet]
  exact IFormula.isInternalSet_setOf_starRealize _ c

/-- **Theorem 11.7.1** (internal set definition principle), with set symbols, in the form in
which it is applied: a set whose membership condition is the reading in the ultrapower of a
formula with set symbols, the symbols being read as internal sets, is internal. -/
theorem isInternalSet_of_forall_iff {k : ℕ} (Φ : SFormula α m (k + 1))
    {X : Fin m → Set αS} (hX : ∀ j, IsInternalSet α (X j)) (c : Fin k → αS) {Y : Set αS}
    (h : ∀ x, x ∈ Y ↔ Φ.starRealize X (Fin.cons x c)) : IsInternalSet α Y := by
  have e : Y = {b : αS | Φ.starRealize X (Fin.cons b c)} := Set.ext h
  rw [e]
  exact isInternalSet_setOf_starRealize Φ hX c

/-- The reading of a negation in the ultrapower. -/
theorem starRealize_not {k : ℕ} (φ : SFormula α m k) (X : Fin m → Set αS) (v : Fin k → αS) :
    φ.not.starRealize X v ↔ ¬ φ.starRealize X v :=
  Iff.rfl

/-- The reading of a conjunction in the ultrapower. -/
theorem starRealize_and {k : ℕ} (φ ψ : SFormula α m k) (X : Fin m → Set αS) (v : Fin k → αS) :
    (φ.and ψ).starRealize X v ↔ φ.starRealize X v ∧ ψ.starRealize X v :=
  Iff.rfl

/-- The reading of a universal quantifier in the ultrapower. -/
theorem starRealize_all {k : ℕ} (φ : SFormula α m (k + 1)) (X : Fin m → Set αS)
    (v : Fin k → αS) :
    φ.all.starRealize X v ↔ ∀ x : αS, φ.starRealize X (Fin.cons x v) :=
  Iff.rfl

/-- The reading of a disjunction in the ultrapower. -/
theorem starRealize_or {k : ℕ} (φ ψ : SFormula α m k) (X : Fin m → Set αS) (v : Fin k → αS) :
    (φ.or ψ).starRealize X v ↔ φ.starRealize X v ∨ ψ.starRealize X v := by
  simp only [SFormula.or, starRealize, not_and_or, not_not]

/-- The reading of an implication in the ultrapower. -/
theorem starRealize_imp {k : ℕ} (φ ψ : SFormula α m k) (X : Fin m → Set αS) (v : Fin k → αS) :
    (φ.imp ψ).starRealize X v ↔ (φ.starRealize X v → ψ.starRealize X v) := by
  simp only [SFormula.imp, starRealize, not_and, not_not]

/-- The reading of an existential quantifier in the ultrapower. -/
theorem starRealize_ex {k : ℕ} (φ : SFormula α m (k + 1)) (X : Fin m → Set αS)
    (v : Fin k → αS) :
    φ.ex.starRealize X v ↔ ∃ x : αS, φ.starRealize X (Fin.cons x v) := by
  simp only [SFormula.ex, starRealize, not_forall, not_not]

/-- In the ultrapower, membership of a variable in a set symbol is membership of its value in
the set that the symbol is read as. -/
theorem starRealize_mem {k : ℕ} (i : Fin k) (j : Fin m) (X : Fin m → Set αS) (v : Fin k → αS) :
    (mem i j : SFormula α m k).starRealize X v ↔ v i ∈ X j :=
  Iff.rfl

/-- In the ultrapower, the atomic formula for membership of variable $`i` in $`[A_n]` says
that the value of the variable belongs to the internal set. -/
theorem starRealize_memI {k : ℕ} (i : Fin k) (A : ℕ → Set α) (X : Fin m → Set αS)
    (v : Fin k → αS) :
    (memI i A : SFormula α m k).starRealize X v ↔ v i ∈ internalSet A :=
  IFormula.starRealize_mem i A v

/-- In the ultrapower, the atomic formula for a binary internal relation between two
variables says that their values are related by it. -/
theorem starRealize_rel₂ {k : ℕ} (i j : Fin k) (R : ℕ → α → α → Prop) (X : Fin m → Set αS)
    (v : Fin k → αS) :
    (rel₂ i j R : SFormula α m k).starRealize X v ↔ internalRel R (v i) (v j) :=
  IFormula.starRealize_rel₂ i j R v

/-- The standard reading of a negation. -/
theorem realize_not {k : ℕ} (φ : SFormula α m k) (S : Fin m → Set α) (n : ℕ) (v : Fin k → α) :
    φ.not.realize S n v ↔ ¬ φ.realize S n v :=
  Iff.rfl

/-- The standard reading of a conjunction. -/
theorem realize_and {k : ℕ} (φ ψ : SFormula α m k) (S : Fin m → Set α) (n : ℕ) (v : Fin k → α) :
    (φ.and ψ).realize S n v ↔ φ.realize S n v ∧ ψ.realize S n v :=
  Iff.rfl

/-- The standard reading of a universal quantifier. -/
theorem realize_all {k : ℕ} (φ : SFormula α m (k + 1)) (S : Fin m → Set α) (n : ℕ)
    (v : Fin k → α) :
    φ.all.realize S n v ↔ ∀ a : α, φ.realize S n (Fin.cons a v) :=
  Iff.rfl

/-- The standard reading of a disjunction. -/
theorem realize_or {k : ℕ} (φ ψ : SFormula α m k) (S : Fin m → Set α) (n : ℕ) (v : Fin k → α) :
    (φ.or ψ).realize S n v ↔ φ.realize S n v ∨ ψ.realize S n v := by
  simp only [SFormula.or, realize, not_and_or, not_not]

/-- The standard reading of an implication. -/
theorem realize_imp {k : ℕ} (φ ψ : SFormula α m k) (S : Fin m → Set α) (n : ℕ) (v : Fin k → α) :
    (φ.imp ψ).realize S n v ↔ (φ.realize S n v → ψ.realize S n v) := by
  simp only [SFormula.imp, realize, not_and, not_not]

/-- The standard reading of an existential quantifier. -/
theorem realize_ex {k : ℕ} (φ : SFormula α m (k + 1)) (S : Fin m → Set α) (n : ℕ)
    (v : Fin k → α) :
    φ.ex.realize S n v ↔ ∃ a : α, φ.realize S n (Fin.cons a v) := by
  simp only [SFormula.ex, realize, not_forall, not_not]

/-- The standard reading of membership of a variable in a set symbol. -/
theorem realize_mem {k : ℕ} (i : Fin k) (j : Fin m) (S : Fin m → Set α) (n : ℕ)
    (v : Fin k → α) :
    (mem i j : SFormula α m k).realize S n v ↔ v i ∈ S j :=
  Iff.rfl

/-- The standard reading at index $`n` of membership of a variable in $`[A_n]`. -/
theorem realize_memI {k : ℕ} (i : Fin k) (A : ℕ → Set α) (S : Fin m → Set α) (n : ℕ)
    (v : Fin k → α) :
    (memI i A : SFormula α m k).realize S n v ↔ v i ∈ A n :=
  Iff.rfl

/-- The standard reading at index $`n` of a binary internal relation between two
variables. -/
theorem realize_rel₂ {k : ℕ} (i j : Fin k) (R : ℕ → α → α → Prop) (S : Fin m → Set α) (n : ℕ)
    (v : Fin k → α) :
    (rel₂ i j R : SFormula α m k).realize S n v ↔ R n (v i) (v j) :=
  Iff.rfl

end SFormula

end Formulas

/-!
### Using the principle

The examples of Section 11.1 can be recovered from the principle, as the book remarks: a
finite set is defined by a disjunction of equations $`x_0 = x_i`
({lit}`Goldblatt.isInternalSet_range_of_definition`), and an open interval by the formula
$`x_1 < x_0 \wedge x_0 < x_2`. Exercise 11.7.1 asks
for the same to be done for the other intervals, for an initial segment of the hypernaturals
and for a hyperfinite grid; these are the theorems below whose names end in
{lit}`_of_definition`, each obtained from {lit}`Goldblatt.IFormula.isInternalSet_of_forall_iff`
by writing down the defining formula. The least number principle of Section 11.3 and the
order-completeness of Section 11.5 are derived once more, from the transfer principle for
sentences with a set symbol. The first substantial
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

/-- The internal set of the constant sequence of the set of natural numbers is the set of
hypernaturals. -/
theorem internalSet_const_range_natCast :
    (internalSet fun _ : ℕ => range ((↑) : ℕ → ℝ) : Set ℝ*) = ℕ* :=
  (starSet_eq_internalSet _).symm

/-- **Section 11.7, the almost-all criterion for ternary internal relations** on the
hyperreals. -/
theorem hyperreal_internalRelN_vec₃ {R : ℕ → (Fin 3 → ℝ) → Prop} {a b c : ℕ → ℝ} :
    internalRelN R ![Hyperreal.ofSeq a, Hyperreal.ofSeq b, Hyperreal.ofSeq c] ↔
      ∀ᶠ n in hyperfilter ℕ, R n ![a n, b n, c n] :=
  internalRelN_vec₃

/-- **Section 11.7, first example after the principle.** A finite set
$`\{c_1, \dots, c_n\}` of elements of the ultrapower is internal because it is defined by
the formula $`x_0 = x_1 \vee \dots \vee x_0 = x_n` with the parameters $`c_1, \dots, c_n`.
The disjunction is built by {name}`Goldblatt.IFormula.disj` from the atomic formulas
$`x_0 = x_i`; for $`n = 0` it is the false formula, which defines the empty set. -/
theorem isInternalSet_range_of_definition {α αS : Type u} [StarType α αS] {n : ℕ}
    (c : Fin n → αS) : IsInternalSet α (range c) :=
  IFormula.isInternalSet_of_forall_iff
    (IFormula.disj (List.ofFn fun i : Fin n => IFormula.rel₂ 0 i.succ fun _ a b => a = b)) c
    fun x => by
      rw [IFormula.starRealize_disj]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩,
          (IFormula.starRealize_rel₂ _ _ _ _).2 (internalRel_eq.2 (by simp))⟩
      · rintro ⟨φ, hφ, h⟩
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
        have h' := internalRel_eq.1 ((IFormula.starRealize_rel₂ _ _ _ _).1 h)
        exact ⟨i, by simpa using h'.symm⟩

/-- **Section 11.7, first example after the principle.** Every finite set of elements of the
ultrapower is internal, by the internal set definition principle. This is
{name}`Goldblatt.isInternalSet_of_finite` again, now obtained from the principle. -/
theorem isInternalSet_of_finite_of_definition {α αS : Type u} [StarType α αS] {X : Set αS}
    (hX : X.Finite) : IsInternalSet α X := by
  obtain ⟨n, f, rfl⟩ := hX.fin_embedding
  exact isInternalSet_range_of_definition f

/-- **Section 11.7, first example after the principle.** Every finite set of hyperreals is
internal, by the internal set definition principle. -/
theorem isInternal_of_finite_of_definition {X : Set ℝ*} (hX : X.Finite) : IsInternal X :=
  isInternalSet_of_finite_of_definition hX

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

/-- **Exercise 11.7.1.** The interval $`(a, b]` is internal by the internal set definition
principle: it is defined by the formula $`x_1 < x_0 \wedge x_0 \le x_2` with the parameters
$`a, b`. -/
theorem isInternal_Ioc_of_definition (a b : ℝ*) : IsInternal (Ioc a b) :=
  IFormula.isInternalSet_of_forall_iff (α := ℝ)
    ((IFormula.rel₂ 1 0 fun _ x y => x < y).and (IFormula.rel₂ 0 2 fun _ x y => x ≤ y)) ![a, b]
    fun x => by
      simp only [IFormula.starRealize_and, IFormula.starRealize_rel₂, internalRel_lt,
        internalRel_le, mem_Ioc]
      exact Iff.rfl

/-- **Exercise 11.7.1.** The interval $`[a, b)` is internal by the internal set definition
principle: it is defined by the formula $`x_1 \le x_0 \wedge x_0 < x_2`. -/
theorem isInternal_Ico_of_definition (a b : ℝ*) : IsInternal (Ico a b) :=
  IFormula.isInternalSet_of_forall_iff (α := ℝ)
    ((IFormula.rel₂ 1 0 fun _ x y => x ≤ y).and (IFormula.rel₂ 0 2 fun _ x y => x < y)) ![a, b]
    fun x => by
      simp only [IFormula.starRealize_and, IFormula.starRealize_rel₂, internalRel_lt,
        internalRel_le, mem_Ico]
      exact Iff.rfl

/-- **Exercise 11.7.1.** The interval $`[a, b]` is internal by the internal set definition
principle: it is defined by the formula $`x_1 \le x_0 \wedge x_0 \le x_2`. -/
theorem isInternal_Icc_of_definition (a b : ℝ*) : IsInternal (Icc a b) :=
  IFormula.isInternalSet_of_forall_iff (α := ℝ)
    ((IFormula.rel₂ 1 0 fun _ x y => x ≤ y).and (IFormula.rel₂ 0 2 fun _ x y => x ≤ y)) ![a, b]
    fun x => by
      simp only [IFormula.starRealize_and, IFormula.starRealize_rel₂, internalRel_le, mem_Icc]
      exact Iff.rfl

/-- **Exercise 11.7.1.** The ray $`\{x : a < x\}` is internal by the internal set definition
principle: it is defined by the formula $`x_1 < x_0`. -/
theorem isInternal_Ioi_of_definition (a : ℝ*) : IsInternal (Ioi a) :=
  IFormula.isInternalSet_of_forall_iff (α := ℝ) (IFormula.rel₂ 1 0 fun _ x y => x < y) ![a]
    fun x => by
      simp only [IFormula.starRealize_rel₂, internalRel_lt, mem_Ioi]
      exact Iff.rfl

/-- **Exercise 11.7.1.** The ray $`\{x : a \le x\}` is internal by the internal set
definition principle: it is defined by the formula $`x_1 \le x_0`. -/
theorem isInternal_Ici_of_definition (a : ℝ*) : IsInternal (Ici a) :=
  IFormula.isInternalSet_of_forall_iff (α := ℝ) (IFormula.rel₂ 1 0 fun _ x y => x ≤ y) ![a]
    fun x => by
      simp only [IFormula.starRealize_rel₂, internalRel_le, mem_Ici]
      exact Iff.rfl

/-- **Exercise 11.7.1.** The ray $`\{x : x < a\}` is internal by the internal set definition
principle: it is defined by the formula $`x_0 < x_1`. -/
theorem isInternal_Iio_of_definition (a : ℝ*) : IsInternal (Iio a) :=
  IFormula.isInternalSet_of_forall_iff (α := ℝ) (IFormula.rel₂ 0 1 fun _ x y => x < y) ![a]
    fun x => by
      simp only [IFormula.starRealize_rel₂, internalRel_lt, mem_Iio]
      exact Iff.rfl

/-- **Exercise 11.7.1.** The ray $`\{x : x \le a\}` is internal by the internal set
definition principle: it is defined by the formula $`x_0 \le x_1`. -/
theorem isInternal_Iic_of_definition (a : ℝ*) : IsInternal (Iic a) :=
  IFormula.isInternalSet_of_forall_iff (α := ℝ) (IFormula.rel₂ 0 1 fun _ x y => x ≤ y) ![a]
    fun x => by
      simp only [IFormula.starRealize_rel₂, internalRel_le, mem_Iic]
      exact Iff.rfl

/-- **Exercise 11.7.1.** The set $`\{k \in {}^*\mathbb N : 1 \le k \le N\}` is internal by
the internal set definition principle: it is defined by the formula
$`x_0 \in \mathbb N \wedge x_1 \le x_0 \wedge x_0 \le x_2` with the parameters $`1, N`.
Derived in this way the statement needs no hypothesis on $`N`. -/
theorem isInternal_setOf_hyperNat_one_le_le_of_definition (N : ℝ*) :
    IsInternal {k : ℝ* | k ∈ ℕ* ∧ 1 ≤ k ∧ k ≤ N} :=
  IFormula.isInternalSet_of_forall_iff (α := ℝ)
    ((IFormula.mem 0 fun _ => range ((↑) : ℕ → ℝ)).and
      ((IFormula.rel₂ 1 0 fun _ x y => x ≤ y).and (IFormula.rel₂ 0 2 fun _ x y => x ≤ y)))
    ![1, N] fun x => by
      simp only [IFormula.starRealize_and, IFormula.starRealize_rel₂, IFormula.starRealize_mem,
        internalRel_le, internalSet_const_range_natCast, mem_ofPred_eq]
      exact Iff.rfl

/-- **Exercise 11.7.1, an atomic formula with a function symbol.** In the ultrapower the
atomic formula $`x_1 = x_0 / x_2` says what it should. -/
theorem starRealize_eq_div (k x N : ℝ*) :
    (IFormula.rel fun _ (v : Fin 3 → ℝ) => v 1 = v 0 / v 2).starRealize (Fin.cons k ![x, N]) ↔
      x = k / N := by
  obtain ⟨a, rfl⟩ := hyperreal_exists_rep k
  obtain ⟨b, rfl⟩ := hyperreal_exists_rep x
  obtain ⟨c, rfl⟩ := hyperreal_exists_rep N
  have e : Hyperreal.ofSeq a / Hyperreal.ofSeq c = Hyperreal.ofSeq fun n => a n / c n := rfl
  rw [e, ofSeq_eq_ofSeq_iff]
  exact hyperreal_internalRelN_vec₃

/-- **Exercise 11.7.1.** The set $`\{k/N : k \in {}^*\mathbb N,\ k \le N\} =
\{0, \tfrac1N, \tfrac2N, \dots, 1\}` is internal by the internal set definition principle:
it is defined by the formula
$`\exists z\,(z \in \mathbb N \wedge z \le x_1 \wedge x_0 = z / x_1)` with the parameter
$`N`. -/
theorem isInternal_setOf_div_hyperNat_of_definition (N : ℝ*) :
    IsInternal {x : ℝ* | ∃ k ∈ ℕ*, k ≤ N ∧ x = k / N} :=
  IFormula.isInternalSet_of_forall_iff (α := ℝ)
    (IFormula.ex ((IFormula.mem 0 fun _ => range ((↑) : ℕ → ℝ)).and
      ((IFormula.rel₂ 0 2 fun _ x y => x ≤ y).and
        (IFormula.rel fun _ v => v 1 = v 0 / v 2))))
    ![N] fun x => by
      simp only [IFormula.starRealize_ex, IFormula.starRealize_and, IFormula.starRealize_rel₂,
        IFormula.starRealize_mem, internalRel_le, internalSet_const_range_natCast,
        mem_ofPred_eq]
      refine exists_congr fun k => and_congr Iff.rfl (and_congr Iff.rfl ?_)
      exact (starRealize_eq_div k x N).symm

/-- **Section 11.7, the first sentence discussed in the section; Theorem 11.3.1 by
transfer.** The sentence
$$`\bigl[\exists x\,(x \in A) \wedge \forall x\,(x \in A \to x \in \mathbb N)\bigr] \to
\exists x\,\bigl(x \in A \wedge \forall y\,(y \in A \to x \le y)\bigr)`
is true for every set $`A` of real numbers, because the natural numbers are well ordered. By
the transfer principle for sentences with a set symbol
({name}`Goldblatt.SFormula.starRealize_of_forall_realize`) its transform is true of every
internal set, and this is the internal least number principle
({name}`Goldblatt.IsInternal.exists_isLeast`), obtained here without an ultrafilter
calculation. -/
theorem IsInternal.exists_isLeast_of_transfer {X : Set ℝ*} (hX : IsInternal X) (hsub : X ⊆ ℕ*)
    (hne : X.Nonempty) : ∃ a, IsLeast X a := by
  have h := SFormula.starRealize_of_forall_realize (α := ℝ) (m := 1)
    (((SFormula.ex (SFormula.mem 0 0)).and
      (SFormula.all ((SFormula.mem 0 0).imp (SFormula.memI 0 fun _ => range ((↑) : ℕ → ℝ))))).imp
      (SFormula.ex ((SFormula.mem 0 0).and
        (SFormula.all ((SFormula.mem 0 0).imp (SFormula.rel₂ 1 0 fun _ x y => x ≤ y))))))
    (fun S n a => by
      simp only [SFormula.realize_imp, SFormula.realize_and, SFormula.realize_ex,
        SFormula.realize_all, SFormula.realize_mem, SFormula.realize_memI,
        SFormula.realize_rel₂]
      rintro ⟨⟨x, hx⟩, hN⟩
      have hT : {k : ℕ | (k : ℝ) ∈ S 0}.Nonempty := by
        obtain ⟨k, hk⟩ := hN x hx
        exact ⟨k, by rw [mem_ofPred_eq, hk]; exact hx⟩
      refine ⟨((sInf {k : ℕ | (k : ℝ) ∈ S 0} : ℕ) : ℝ), Nat.sInf_mem hT, fun y hy => ?_⟩
      obtain ⟨k, rfl⟩ := hN y hy
      exact Nat.cast_le.2 (Nat.sInf_le hy))
    (X := fun _ => X) (fun _ => hX) Fin.elim0
  simp only [SFormula.starRealize_imp, SFormula.starRealize_and, SFormula.starRealize_ex,
    SFormula.starRealize_all, SFormula.starRealize_mem, SFormula.starRealize_memI,
    SFormula.starRealize_rel₂, internalRel_le, internalSet_const_range_natCast] at h
  obtain ⟨a, ha, hmin⟩ := h ⟨hne, hsub⟩
  exact ⟨a, ha, hmin⟩

/-- **Section 11.7, the second sentence discussed in the section; Theorem 11.5.1 by
transfer.** The sentence
$$`\bigl[\exists x\,(x \in A) \wedge \exists x\,\forall y\,(y \in A \to y \le x)\bigr] \to
\exists x\,\bigl[\forall y\,(y \in A \to y \le x) \wedge
\forall z\,\bigl(\forall y\,(y \in A \to y \le z) \to x \le z\bigr)\bigr]`
is true for every set $`A` of real numbers, because the real line is order-complete. By the
transfer principle for sentences with a set symbol
({name}`Goldblatt.SFormula.starRealize_of_forall_realize`) its transform is true of every
internal set, and this is internal order-completeness
({name}`Goldblatt.IsInternal.exists_isLUB`), obtained here without an ultrafilter
calculation. The sentence displayed in the book has no first conjunct in its antecedent, and
is then false for the empty set, so that the dagger principle does not apply to it as
printed (the book restricts to nonempty internal sets afterwards); the conjunct
$`\exists x\,(x \in A)` is the correction. -/
theorem IsInternal.exists_isLUB_of_transfer {X : Set ℝ*} (hX : IsInternal X)
    (hne : X.Nonempty) (hb : BddAbove X) : ∃ b, IsLUB X b := by
  have h := SFormula.starRealize_of_forall_realize (α := ℝ) (m := 1)
    (((SFormula.ex (SFormula.mem 0 0)).and
      (SFormula.ex (SFormula.all ((SFormula.mem 0 0).imp
        (SFormula.rel₂ 0 1 fun _ x y => x ≤ y))))).imp
      (SFormula.ex ((SFormula.all ((SFormula.mem 0 0).imp
          (SFormula.rel₂ 0 1 fun _ x y => x ≤ y))).and
        (SFormula.all ((SFormula.all ((SFormula.mem 0 0).imp
          (SFormula.rel₂ 0 1 fun _ x y => x ≤ y))).imp
            (SFormula.rel₂ 1 0 fun _ x y => x ≤ y))))))
    (fun S n a => by
      simp only [SFormula.realize_imp, SFormula.realize_and, SFormula.realize_ex,
        SFormula.realize_all, SFormula.realize_mem, SFormula.realize_rel₂]
      rintro ⟨⟨x, hx⟩, ⟨u, hu⟩⟩
      exact ⟨sSup (S 0), fun y hy => le_csSup ⟨u, hu⟩ hy, fun z hz => csSup_le ⟨x, hx⟩ hz⟩)
    (X := fun _ => X) (fun _ => hX) Fin.elim0
  simp only [SFormula.starRealize_imp, SFormula.starRealize_and, SFormula.starRealize_ex,
    SFormula.starRealize_all, SFormula.starRealize_mem,
    SFormula.starRealize_rel₂, internalRel_le] at h
  obtain ⟨u, hu⟩ := hb
  obtain ⟨b, hb1, hb2⟩ := h ⟨hne, u, fun y hy => hu hy⟩
  exact ⟨b, fun y hy => hb1 y hy, fun z hz => hb2 z fun y hy => hz hy⟩

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
hypernaturals $`n` with $`{}^*f(n) \in X` is then internal by internal set definition (it is
defined by the formula $`x \in \mathbb N \wedge f(x) \in X`, whose second conjunct is the
atom {name}`Goldblatt.IFormula.memMap`), but since $`f` is injective this set is the external
set of standard natural numbers. -/
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
    rw [hC]
    refine IFormula.isInternalSet_of_forall_iff (α := ℝ)
      ((IFormula.mem 0 fun _ => range ((↑) : ℕ → ℝ)).and (IFormula.memMap 0 g C)) Fin.elim0
      fun x => ?_
    simp only [IFormula.starRealize_and, IFormula.starRealize_mem, IFormula.starRealize_memMap,
      internalSet_const_range_natCast, mem_ofPred_eq]
    exact Iff.rfl
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
belongs to $`X` is internal, by the internal set definition principle: it is defined by the
formula
$`x \in \mathbb N \wedge x \le y \wedge \forall z \in \mathbb N\,(x \le z \le y \to z \in A)`
with the parameter $`K` for $`y` and the internal set $`X` for $`A`. -/
theorem IsInternal.isInternal_setOf_segment_subset {X : Set ℝ*} (hX : IsInternal X) (K : ℝ*) :
    IsInternal {k : ℝ* | k ∈ ℕ* ∧ k ≤ K ∧ ∀ z ∈ ℕ*, k ≤ z → z ≤ K → z ∈ X} := by
  obtain ⟨A, rfl⟩ := hX
  refine IFormula.isInternalSet_of_forall_iff (α := ℝ)
    ((IFormula.mem 0 fun _ => range ((↑) : ℕ → ℝ)).and
      ((IFormula.rel₂ 0 1 fun _ x y => x ≤ y).and
        (IFormula.all ((IFormula.mem 0 fun _ => range ((↑) : ℕ → ℝ)).imp
          ((IFormula.rel₂ 1 0 fun _ x y => x ≤ y).imp
            ((IFormula.rel₂ 0 2 fun _ x y => x ≤ y).imp (IFormula.mem 0 A)))))))
    ![K] fun x => ?_
  simp only [IFormula.starRealize_all, IFormula.starRealize_imp, IFormula.starRealize_and,
    IFormula.starRealize_rel₂, IFormula.starRealize_mem, internalRel_le,
    internalSet_const_range_natCast, mem_ofPred_eq]
  exact Iff.rfl

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

/-- **Section 11.9.** A set defined by the transform of a formula, with parameters from
$`{}^*\mathbb R`, is never a halo: it is internal by the internal set definition principle,
and a halo is external ({name}`Goldblatt.isExternal_hal`). So a property expressed by such a
formula cannot hold of exactly the points infinitely close to $`b`. The book states this for
a formula with one free variable and no parameters, which is the case $`k = 0`. -/
theorem IFormula.setOf_starRealize_ne_hal {k : ℕ} (φ : IFormula ℝ (k + 1)) (c : Fin k → ℝ*)
    (b : ℝ*) : {x : ℝ* | φ.starRealize (Fin.cons x c)} ≠ hal b := fun h =>
  isExternal_hal b (h ▸ IFormula.isInternalSet_setOf_starRealize φ c)

/-- **Section 11.9.** The same for formulas with set symbols read as internal sets: the set
they define is never a halo. -/
theorem SFormula.setOf_starRealize_ne_hal {m k : ℕ} (Φ : SFormula ℝ m (k + 1))
    {X : Fin m → Set ℝ*} (hX : ∀ j, IsInternal (X j)) (c : Fin k → ℝ*) (b : ℝ*) :
    {x : ℝ* | Φ.starRealize X (Fin.cons x c)} ≠ hal b := fun h =>
  isExternal_hal b (h ▸ SFormula.isInternalSet_setOf_starRealize Φ hX c)

/-- **Section 11.9.** In particular, if the transform of a formula holds at every point of a
halo, then it holds at some point outside the halo: the property is permanent. -/
theorem IFormula.exists_starRealize_not_mem_hal {k : ℕ} (φ : IFormula ℝ (k + 1))
    (c : Fin k → ℝ*) (b : ℝ*) (h : ∀ x ∈ hal b, φ.starRealize (Fin.cons x c)) :
    ∃ x, x ∉ hal b ∧ φ.starRealize (Fin.cons x c) := by
  by_contra hcon
  refine IFormula.setOf_starRealize_ne_hal φ c b (Subset.antisymm (fun x hx => ?_) h)
  by_contra hx'
  exact hcon ⟨x, hx', hx⟩

/-- **Theorem 11.9.1, the atomic formula.** In the ultrapower the atomic formula
$`|x_0 - x_2| < 1/x_1`, which is the standard ternary relation with these function symbols,
says what it should. -/
theorem starRealize_abs_sub_lt_one_div (z k b : ℝ*) :
    (IFormula.rel fun _ (v : Fin 3 → ℝ) => |v 0 - v 2| < 1 / v 1).starRealize
      (Fin.cons z ![k, b]) ↔ |z - b| < 1 / k := by
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep z
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep k
  obtain ⟨β, rfl⟩ := hyperreal_exists_rep b
  have e1 : |Hyperreal.ofSeq s - Hyperreal.ofSeq β| = Hyperreal.ofSeq fun n => |s n - β n| :=
    abs_ofSeq _
  have e2 : (1 : ℝ*) / Hyperreal.ofSeq r = Hyperreal.ofSeq fun n => 1 / r n := rfl
  rw [e1, e2, ofSeq_lt_ofSeq_iff]
  exact hyperreal_internalRelN_vec₃

/-- **Theorem 11.9.1, the definable set.** For an internal set $`X` and a hyperreal $`b`,
the set of hypernaturals $`k` such that the interval $`(b - \tfrac1k, b + \tfrac1k)` is
included in $`X` is internal, by the internal set definition principle: it is defined by the
formula $`x \in \mathbb N \wedge \forall z\,(|z - y| < \tfrac1x \to z \in A)` with the
parameter $`b` for $`y` and the internal set $`X` for $`A`. -/
theorem IsInternal.isInternal_setOf_ball_subset {X : Set ℝ*} (hX : IsInternal X) (b : ℝ*) :
    IsInternal {k : ℝ* | k ∈ ℕ* ∧ ∀ z : ℝ*, |z - b| < 1 / k → z ∈ X} := by
  obtain ⟨A, rfl⟩ := hX
  refine IFormula.isInternalSet_of_forall_iff (α := ℝ)
    ((IFormula.mem 0 fun _ => range ((↑) : ℕ → ℝ)).and
      (IFormula.all ((IFormula.rel fun _ v => |v 0 - v 2| < 1 / v 1).imp (IFormula.mem 0 A))))
    ![b] fun x => ?_
  simp only [IFormula.starRealize_all, IFormula.starRealize_imp, IFormula.starRealize_and,
    IFormula.starRealize_mem, internalSet_const_range_natCast, mem_ofPred_eq]
  refine and_congr Iff.rfl (forall_congr' fun z => imp_congr ?_ Iff.rfl)
  exact (starRealize_abs_sub_lt_one_div z x b).symm

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
