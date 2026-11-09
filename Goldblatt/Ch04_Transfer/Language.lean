import Goldblatt.Ch02_LargeSets
import Goldblatt.Ch03_Ultrapower

/-!
# 4 (part 1). The Language of a Relational Structure: Sections 4.2 to 4.4

This is the first of three parts of Chapter 4 (the overview is on the chapter page
{lit}`Goldblatt.Ch04_Transfer`). It sets up the formal language in which transferable
statements are written: relational structures, terms that may fail to name anything, formulas
with bounded quantifiers, the truth conditions of the book including its treatment of
undefined terms, and the star-transform that turns a formula about a structure into a formula
about its enlargement.

Everything is done over an arbitrary type in place of the reals. The book's case is the type of
real numbers, whose star type is the type of hyperreals; Section 4.7 of the book points out
that nothing depends on that choice.
-/

universe u

namespace Goldblatt

open Set Filter Function Ultrapower
open scoped Hyperreal

/-!
## 4.2 Relational Structures

A relational structure is a set together with a stock of relations and of functions on it, each
of some finite arity, where a function is allowed to be defined on only part of the set of
tuples. A $`k`-ary relation is a set of $`k`-tuples, and tuples are functions on the finite type
with $`k` elements, as in Section 3.14. A partial $`m`-ary function is a pair: its domain, a set
of $`m`-tuples, and a function on that domain.

The _full_ structure on a set has all relations and all partial functions. The structure that
matters for transfer is the enlargement of the full structure: its relations are the
enlargements of the standard relations and its functions the extensions of the standard partial
functions. It is far from full, and Exercise 4.2.1 makes that precise.
-/

/-- **Section 4.2.** A _relational structure_ on a set $`S`: a collection of finitary relations
on $`S` and a collection of finitary, possibly partial, functions on $`S`. A $`k`-ary relation
is a set of $`k`-tuples; a partial $`m`-ary function is a domain of $`m`-tuples together with a
function defined on it. (The book also asks $`S` to be nonempty; nothing here needs that.) -/
structure RelStructure (S : Type u) where
  /-- The $`k`-ary relations of the structure. -/
  Rel : (k : ℕ) → Set (Set (Fin k → S))
  /-- The partial $`m`-ary functions of the structure, each given with its domain. -/
  Fun : (m : ℕ) → Set (Σ A : Set (Fin m → S), A → S)

/-- **Section 4.2.** The _full structure_ based on $`S`: all finitary relations and all
finitary partial functions on $`S`. For the reals this is the structure the book calls
$`\mathfrak R`. -/
def RelStructure.full (S : Type u) : RelStructure S where
  Rel _ := univ
  Fun _ := univ

/-- **Section 4.2.** The structure $`{}^*\mathfrak S` associated with the full structure on a
set: its universe is the star type, its relations are the enlargements $`{}^*P` of the
relations on the set (Section 3.14) and its functions are the extensions $`{}^*f` of the partial
functions on the set (Sections 3.11 and 3.13). For the reals this is the book's
$`{}^*\mathfrak R`. -/
def RelStructure.star (α : Type u) {αS : Type u} [StarType α αS] : RelStructure αS where
  Rel k := range fun P : Set (Fin k → α) => (starRel P : Set (Fin k → αS))
  Fun m := range fun p : (Σ A : Set (Fin m → α), A → α) =>
    (⟨starRel p.1, starMapOnN p.1 p.2⟩ : Σ A : Set (Fin m → αS), A → αS)

/-- **Section 4.2.** The unary relation that corresponds to a subset: the set of one-tuples
whose entry lies in the subset. -/
def unaryRel {S : Type u} (A : Set S) : Set (Fin 1 → S) := {a | a 0 ∈ A}

section StarStructure

variable {α αS : Type u} [StarType α αS]

/-- **Section 4.2.** A relation belongs to $`{}^*\mathfrak S` when it is the enlargement of a
standard relation. -/
theorem RelStructure.mem_star_rel {k : ℕ} {R : Set (Fin k → αS)} :
    R ∈ (RelStructure.star α).Rel k ↔ ∃ P : Set (Fin k → α), starRel P = R := Iff.rfl

/-- **Section 4.2.** A partial function belongs to $`{}^*\mathfrak S` when it is the extension
of a standard partial function. -/
theorem RelStructure.mem_star_fun {m : ℕ} {F : Σ A : Set (Fin m → αS), A → αS} :
    F ∈ (RelStructure.star α).Fun m ↔
      ∃ p : (Σ A : Set (Fin m → α), A → α), ⟨starRel p.1, starMapOnN p.1 p.2⟩ = F := Iff.rfl

/-- **Section 4.2.** The enlargement of the unary relation of a set is the unary relation of the
enlargement of the set. -/
theorem starRel_unaryRel (A : Set α) :
    (starRel (unaryRel A) : Set (Fin 1 → αS)) = unaryRel (⋆A) := by
  ext x
  rw [starRel_unary]
  rfl

/-- **Section 4.2.** The subsets of the star type that belong to the structure
$`{}^*\mathfrak S`, as unary relations, are exactly the enlargements of standard sets. -/
theorem unaryRel_mem_star_iff {B : Set αS} :
    unaryRel B ∈ (RelStructure.star α).Rel 1 ↔ ∃ A : Set α, (⋆A : Set αS) = B := by
  rw [RelStructure.mem_star_rel]
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨{a | (fun _ => a) ∈ P}, ?_⟩
    ext x
    have h : (fun _ : Fin 1 => x) ∈ starRel P ↔ (fun _ : Fin 1 => x) ∈ unaryRel B := by
      have hP' : starRel P = unaryRel B := hP
      rw [hP']
    rw [starRel_unary] at h
    exact h
  · rintro ⟨A, rfl⟩
    exact ⟨unaryRel A, starRel_unaryRel A⟩

/-- **Exercise 4.2.1.** The standard copy of an infinite set is not the enlargement of any set:
if $`A` is infinite, there is no $`B` with $`{}^*B = \{{}^*a : a \in A\}`. The reason is that
such a $`B` would have to be $`A` itself, and the enlargement of an infinite set has nonstandard
members (Theorem 3.9.1). -/
theorem image_of_ne_starSet {A : Set α} (hA : A.Infinite) (B : Set α) :
    (⋆B : Set αS) ≠ of '' A := by
  intro h
  have hBA : B = A := by
    ext a
    rw [← of_mem_starSet (αS := αS), h]
    exact ⟨fun ⟨b, hb, hba⟩ => of_injective hba ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩
  subst hBA
  obtain ⟨x, hx, hne⟩ := infinite_iff_exists_nonstandard_mem.1 hA
  rw [h] at hx
  obtain ⟨a, -, rfl⟩ := hx
  exact hne ⟨a, rfl⟩

/-- **Exercise 4.2.1.** No infinite set of standard elements belongs to the relations of
$`{}^*\mathfrak S`: for infinite $`A`, the standard copy of $`A`, regarded as a unary relation
on the star type, is not one of the relations $`{}^*P`. -/
theorem unaryRel_image_of_notMem_star {A : Set α} (hA : A.Infinite) :
    unaryRel (of '' A : Set αS) ∉ (RelStructure.star α).Rel 1 := fun h => by
  obtain ⟨B, hB⟩ := unaryRel_mem_star_iff.1 h
  exact image_of_ne_starSet hA B hB

/-- **Exercise 4.2.1, the reals.** No infinite set of real numbers, regarded as a set of
hyperreals, is the enlargement of a set of reals. -/
theorem image_coe_ne_starSet_real {A : Set ℝ} (hA : A.Infinite) (B : Set ℝ) :
    ⋆B ≠ ((↑) : ℝ → ℝ*) '' A :=
  image_of_ne_starSet hA B

/-- **Exercise 4.2.1, the reals.** None of the sets $`\mathbb N`, $`\mathbb Z`, $`\mathbb Q`,
$`\mathbb R`, as sets of hyperreals, is the enlargement of a set of reals; so none of them
belongs to the relations of $`{}^*\mathfrak R`. -/
theorem number_systems_ne_starSet (B : Set ℝ) :
    ⋆B ≠ range (fun n : ℕ => ((n : ℝ) : ℝ*)) ∧ ⋆B ≠ range (fun n : ℤ => ((n : ℝ) : ℝ*)) ∧
      ⋆B ≠ range (fun q : ℚ => ((q : ℝ) : ℝ*)) ∧ ⋆B ≠ range ((↑) : ℝ → ℝ*) := by
  have key : ∀ {ι : Type} (f : ι → ℝ), (range f).Infinite →
      ⋆B ≠ range (fun i : ι => ((f i : ℝ) : ℝ*)) := fun f hf => by
    have h := image_coe_ne_starSet_real hf B
    rwa [← range_comp] at h
  refine ⟨key _ ?_, key _ ?_, key _ ?_, ?_⟩
  · exact infinite_range_of_injective Nat.cast_injective
  · exact infinite_range_of_injective Int.cast_injective
  · exact infinite_range_of_injective Rat.cast_injective
  · have h := image_coe_ne_starSet_real infinite_univ B
    rwa [image_univ] at h

/-- **Section 4.2.** The structure $`{}^*\mathfrak R` is not full: there is a set of hyperreals
that is not among its relations. -/
theorem star_ne_full_real : RelStructure.star ℝ ≠ RelStructure.full ℝ* := fun h => by
  have h1 := unaryRel_image_of_notMem_star (α := ℝ) (A := univ) infinite_univ
  rw [h] at h1
  exact h1 (mem_univ _)

end StarStructure

/-!
## 4.3 The Language of a Relational Structure

The language of a structure has variables, a constant for each element, a function symbol for
each function of the structure and a relation symbol for each of its relations. Terms are built
from variables and constants by function symbols; atomic formulas apply a relation symbol to
terms; formulas are built from atomic ones by the five connectives and by quantifiers, and every
quantifier is _bounded_: it carries a set over which its variable ranges.

In Lean the symbols are the relations and functions themselves, so the type of terms and the
type of formulas below are those of the language of the full structure, and the language of a
smaller structure is cut out by the predicates {lit}`Term.Over` and {lit}`Formula.Over`.
Variables are natural numbers, used as names exactly as the book uses letters: a quantifier
names the variable it binds, and the same name may be bound again further in.

Because functions may be partial, a term without variables may fail to name anything. The book's
truth conditions take this into account, and are reproduced faithfully:

* a closed term names an element, or is undefined;
* a formula is _defined_ when all the closed terms occurring in it are;
* an atomic sentence is true when its terms are defined and the tuple they name belongs to the
  relation;
* a universally quantified sentence is true when every instance that is defined is true, and an
  existentially quantified one when some instance is defined and true.

To state these conditions for formulas with free variables, the book substitutes constants for
variables. We use _valuations_ instead: assignments of values to some of the variables. A
variable without a value is still a variable; a term is _closed_ under a valuation when all its
variables have values. Substituting a constant for a variable and giving the variable that value
come to the same thing ({lit}`Formula.holds_subst`).
-/

/-- **Section 4.3, terms.** The terms of the language of the full structure on $`S`: a variable,
a constant naming an element of $`S`, or a function symbol applied to terms. A function symbol
is a partial $`m`-ary function on $`S`, given by its domain $`A`, a set of $`m`-tuples, and a
function on $`A`. Variables are named by natural numbers. -/
inductive Term (S : Type u) : Type u
  /-- The variable with a given name. -/
  | var (x : ℕ) : Term S
  /-- The constant naming an element. -/
  | const (s : S) : Term S
  /-- A partial function with domain {lit}`A` applied to a tuple of terms. -/
  | func {m : ℕ} (A : Set (Fin m → S)) (f : A → S) (ts : Fin m → Term S) : Term S

/-- **Section 4.3, formulas.** The formulas of the language of the full structure on $`S`: an
atomic formula $`P(\tau_1, \dots, \tau_k)` for a $`k`-ary relation $`P`; conjunction,
disjunction, negation, implication and biconditional; and the bounded quantifiers
$`(\forall x \in P)\varphi` and $`(\exists x \in P)\varphi`, where the bound $`P` is a subset
of $`S`. -/
inductive Formula (S : Type u) : Type u
  /-- The atomic formula applying a relation to a tuple of terms. -/
  | rel {k : ℕ} (P : Set (Fin k → S)) (ts : Fin k → Term S) : Formula S
  /-- Conjunction. -/
  | and (φ ψ : Formula S) : Formula S
  /-- Disjunction. -/
  | or (φ ψ : Formula S) : Formula S
  /-- Negation. -/
  | not (φ : Formula S) : Formula S
  /-- Implication. -/
  | imp (φ ψ : Formula S) : Formula S
  /-- Biconditional. -/
  | iff (φ ψ : Formula S) : Formula S
  /-- The bounded universal quantifier binding the variable {lit}`x` with bound {lit}`P`. -/
  | all (x : ℕ) (P : Set S) (φ : Formula S) : Formula S
  /-- The bounded existential quantifier binding the variable {lit}`x` with bound {lit}`P`. -/
  | ex (x : ℕ) (P : Set S) (φ : Formula S) : Formula S

/-- **Section 4.3, valuations.** An assignment of values to some of the variables. The variables
that receive no value remain variables. Assigning the value $`s` to $`x` plays the role of
substituting the constant $`s` for $`x`. -/
abbrev Valuation (S : Type u) : Type u := ℕ → Option S

/-- **Section 4.3.** The empty valuation, which assigns no values. Sentences are evaluated under
it. -/
def Valuation.empty {S : Type u} : Valuation S := fun _ => none

@[simp]
theorem Valuation.empty_apply {S : Type u} (x : ℕ) : (Valuation.empty : Valuation S) x = none :=
  rfl

namespace Term

variable {S : Type u}

/-- **Section 4.3, what a term names.** The relation "the term $`\tau` names the element $`a`"
under a valuation. A variable names its value, if it has one; a constant names itself;
$`f(\tau_1, \dots, \tau_m)` names $`f(s_1, \dots, s_m)` when each $`\tau_i` names $`s_i` and the
tuple $`(s_1, \dots, s_m)` lies in the domain of $`f`. -/
def Names : Term S → Valuation S → S → Prop
  | var x, v, a => v x = some a
  | const s, _, a => s = a
  | func A f ts, v, a =>
      ∃ args, (∀ i, (ts i).Names v (args i)) ∧ ∃ h : args ∈ A, f ⟨args, h⟩ = a

@[simp] theorem names_var {x : ℕ} {v : Valuation S} {a : S} :
    (var x).Names v a ↔ v x = some a := Iff.rfl

@[simp] theorem names_const {s : S} {v : Valuation S} {a : S} :
    (const s).Names v a ↔ s = a := Iff.rfl

theorem names_func {m : ℕ} {A : Set (Fin m → S)} {f : A → S} {ts : Fin m → Term S}
    {v : Valuation S} {a : S} :
    (func A f ts).Names v a ↔
      ∃ args, (∀ i, (ts i).Names v (args i)) ∧ ∃ h : args ∈ A, f ⟨args, h⟩ = a := Iff.rfl

/-- **Section 4.3, closed terms.** A term is _closed_ under a valuation when each of its
variables has been given a value. With the empty valuation this is the book's notion: a term
with no variables. -/
def Closed : Term S → Valuation S → Prop
  | var x, v => v x ≠ none
  | const _, _ => True
  | func _ _ ts, v => ∀ i, (ts i).Closed v

@[simp] theorem closed_var {x : ℕ} {v : Valuation S} : (var x : Term S).Closed v ↔ v x ≠ none :=
  Iff.rfl

@[simp] theorem closed_const {s : S} {v : Valuation S} : (const s).Closed v := trivial

theorem closed_func {m : ℕ} {A : Set (Fin m → S)} {f : A → S} {ts : Fin m → Term S}
    {v : Valuation S} : (func A f ts).Closed v ↔ ∀ i, (ts i).Closed v := Iff.rfl

/-- **Section 4.3.** A term _denotes_ under a valuation when it names some element. -/
def Denotes (t : Term S) (v : Valuation S) : Prop := ∃ a, t.Names v a

/-- **Section 4.3, defined terms.** A term is _defined_ under a valuation when every closed term
occurring in it names something: every subterm all of whose variables have values denotes. A
term that still has variables without values is defined as long as its closed subterms are. -/
def Defined : Term S → Valuation S → Prop
  | var _, _ => True
  | const _, _ => True
  | func A f ts, v =>
      (∀ i, (ts i).Defined v) ∧ ((∀ i, (ts i).Closed v) → (func A f ts).Denotes v)

@[simp] theorem defined_var {x : ℕ} {v : Valuation S} : (var x : Term S).Defined v := trivial

@[simp] theorem defined_const {s : S} {v : Valuation S} : (const s).Defined v := trivial

theorem defined_func {m : ℕ} {A : Set (Fin m → S)} {f : A → S} {ts : Fin m → Term S}
    {v : Valuation S} :
    (func A f ts).Defined v ↔
      (∀ i, (ts i).Defined v) ∧ ((∀ i, (ts i).Closed v) → (func A f ts).Denotes v) := Iff.rfl

/-- **Section 4.3.** The variables that occur in a term. -/
def vars : Term S → Set ℕ
  | var x => {x}
  | const _ => ∅
  | func _ _ ts => ⋃ i, (ts i).vars

/-- **Section 4.3.** A term names at most one element. -/
theorem Names.unique {t : Term S} {v : Valuation S} {a b : S} (ha : t.Names v a)
    (hb : t.Names v b) : a = b := by
  induction t generalizing a b with
  | var x => exact Option.some.inj (ha.symm.trans hb)
  | const s => exact ha.symm.trans hb
  | func A f ts ih =>
    obtain ⟨args, h1, h2, rfl⟩ := ha
    obtain ⟨args', h1', h2', rfl⟩ := hb
    have : args = args' := funext fun i => ih i (h1 i) (h1' i)
    subst this
    rfl

/-- **Section 4.3.** A term that names something is closed. -/
theorem Names.closed {t : Term S} {v : Valuation S} {a : S} (ha : t.Names v a) :
    t.Closed v := by
  induction t generalizing a with
  | var x => exact fun h => by simp [h] at ha
  | const s => trivial
  | func A f ts ih =>
    obtain ⟨args, h1, -⟩ := ha
    exact fun i => ih i (h1 i)

/-- **Section 4.3.** A term that names something is defined: all its subterms name
something. -/
theorem Names.defined {t : Term S} {v : Valuation S} {a : S} (ha : t.Names v a) :
    t.Defined v := by
  induction t generalizing a with
  | var x => trivial
  | const s => trivial
  | func A f ts ih =>
    have ha' := ha
    obtain ⟨args, h1, -⟩ := ha
    exact ⟨fun i => ih i (h1 i), fun _ => ⟨a, ha'⟩⟩

/-- **Section 4.3.** A closed term that is defined names an element. -/
theorem Defined.denotes {t : Term S} {v : Valuation S} (hd : t.Defined v) (hc : t.Closed v) :
    t.Denotes v := by
  cases t with
  | var x =>
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hc
    exact ⟨a, ha⟩
  | const s => exact ⟨s, rfl⟩
  | func A f ts => exact hd.2 hc

/-- **Section 4.3.** For a closed term, being defined is the same as naming an element. This is
the book's notion of a defined closed term. -/
theorem defined_iff_denotes {t : Term S} {v : Valuation S} (hc : t.Closed v) :
    t.Defined v ↔ t.Denotes v :=
  ⟨fun hd => hd.denotes hc, fun ⟨_, ha⟩ => ha.defined⟩

/-- **Section 4.3.** What a term names depends only on the values of its variables. -/
theorem names_congr {t : Term S} {v w : Valuation S} (h : ∀ x ∈ t.vars, v x = w x) {a : S} :
    t.Names v a ↔ t.Names w a := by
  induction t generalizing a with
  | var x => rw [names_var, names_var, h x rfl]
  | const s => rfl
  | func A f ts ih =>
    have ih' : ∀ i (b : S), (ts i).Names v b ↔ (ts i).Names w b := fun i b =>
      ih i fun x hx => h x (mem_iUnion.2 ⟨i, hx⟩)
    simp only [names_func, ih']

/-- **Section 4.3.** A term is closed exactly when all its variables have values. -/
theorem closed_iff {t : Term S} {v : Valuation S} : t.Closed v ↔ ∀ x ∈ t.vars, v x ≠ none := by
  induction t with
  | var x => simp [vars]
  | const s => simp [vars]
  | func A f ts ih =>
    simp only [closed_func, ih, vars, mem_iUnion]
    exact ⟨fun h x ⟨i, hi⟩ => h i x hi, fun h i x hi => h x ⟨i, hi⟩⟩

/-- **Section 4.3.** Whether a term is defined depends only on the values of its variables. -/
theorem defined_congr {t : Term S} {v w : Valuation S} (h : ∀ x ∈ t.vars, v x = w x) :
    t.Defined v ↔ t.Defined w := by
  induction t with
  | var x => rfl
  | const s => rfl
  | func A f ts ih =>
    have ih' : ∀ i, (ts i).Defined v ↔ (ts i).Defined w := fun i =>
      ih i fun x hx => h x (mem_iUnion.2 ⟨i, hx⟩)
    have hc : ∀ i, (ts i).Closed v ↔ (ts i).Closed w := fun i => by
      rw [closed_iff, closed_iff]
      exact forall₂_congr fun x hx => by rw [h x (mem_iUnion.2 ⟨i, hx⟩)]
    have hn : (func A f ts).Denotes v ↔ (func A f ts).Denotes w :=
      exists_congr fun a => names_congr h
    simp only [defined_func, ih', hc, hn]

end Term

namespace Formula

variable {S : Type u}

/-- **Section 4.3, defined formulas.** A formula is _defined_ under a valuation when all the
closed terms occurring in it are defined, that is, name something. A quantifier takes the
value away from the variable it binds, so a term in its scope that mentions the bound variable
is not closed and imposes no condition. For a sentence and the empty valuation this is the
book's notion of a defined sentence. -/
def Defined : Formula S → Valuation S → Prop
  | rel _ ts, v => ∀ i, (ts i).Defined v
  | and φ ψ, v => φ.Defined v ∧ ψ.Defined v
  | or φ ψ, v => φ.Defined v ∧ ψ.Defined v
  | not φ, v => φ.Defined v
  | imp φ ψ, v => φ.Defined v ∧ ψ.Defined v
  | iff φ ψ, v => φ.Defined v ∧ ψ.Defined v
  | all x _ φ, v => φ.Defined (update v x none)
  | ex x _ φ, v => φ.Defined (update v x none)

/-- **Section 4.3, truth.** The truth of a formula under a valuation, by the book's rules.

* $`P(\tau_1, \dots, \tau_k)` is true when the terms all name elements and the tuple of those
  elements belongs to $`P`.
* The connectives have their usual meaning.
* $`(\forall x \in P)\varphi` is true when, for every $`s \in P`, if $`\varphi(s)` is defined
  then it is true.
* $`(\exists x \in P)\varphi` is true when there is some $`s \in P` for which $`\varphi(s)` is
  defined and true.

Here $`\varphi(s)` is $`\varphi` with the value $`s` given to $`x`. The book intends these rules
for defined sentences, where they give the truth value; the recursion makes sense for every
formula and valuation, and the transfer theorems hold in that generality. -/
def Holds : Formula S → Valuation S → Prop
  | rel P ts, v => ∃ args, (∀ i, (ts i).Names v (args i)) ∧ args ∈ P
  | and φ ψ, v => φ.Holds v ∧ ψ.Holds v
  | or φ ψ, v => φ.Holds v ∨ ψ.Holds v
  | not φ, v => ¬φ.Holds v
  | imp φ ψ, v => φ.Holds v → ψ.Holds v
  | iff φ ψ, v => (φ.Holds v ↔ ψ.Holds v)
  | all x P φ, v =>
      ∀ a ∈ P, φ.Defined (update v x (some a)) → φ.Holds (update v x (some a))
  | ex x P φ, v =>
      ∃ a ∈ P, φ.Defined (update v x (some a)) ∧ φ.Holds (update v x (some a))

section simp

variable {k : ℕ} {P : Set (Fin k → S)} {ts : Fin k → Term S} {φ ψ : Formula S}
  {v : Valuation S} {x : ℕ} {B : Set S}

theorem defined_rel : (rel P ts).Defined v ↔ ∀ i, (ts i).Defined v := Iff.rfl
@[simp] theorem defined_and : (and φ ψ).Defined v ↔ φ.Defined v ∧ ψ.Defined v := Iff.rfl
@[simp] theorem defined_or : (or φ ψ).Defined v ↔ φ.Defined v ∧ ψ.Defined v := Iff.rfl
@[simp] theorem defined_not : (not φ).Defined v ↔ φ.Defined v := Iff.rfl
@[simp] theorem defined_imp : (imp φ ψ).Defined v ↔ φ.Defined v ∧ ψ.Defined v := Iff.rfl
@[simp] theorem defined_iff : (iff φ ψ).Defined v ↔ φ.Defined v ∧ ψ.Defined v := Iff.rfl
@[simp] theorem defined_all : (all x B φ).Defined v ↔ φ.Defined (update v x none) := Iff.rfl
@[simp] theorem defined_ex : (ex x B φ).Defined v ↔ φ.Defined (update v x none) := Iff.rfl

theorem holds_rel :
    (rel P ts).Holds v ↔ ∃ args, (∀ i, (ts i).Names v (args i)) ∧ args ∈ P := Iff.rfl
@[simp] theorem holds_and : (and φ ψ).Holds v ↔ φ.Holds v ∧ ψ.Holds v := Iff.rfl
@[simp] theorem holds_or : (or φ ψ).Holds v ↔ φ.Holds v ∨ ψ.Holds v := Iff.rfl
@[simp] theorem holds_not : (not φ).Holds v ↔ ¬φ.Holds v := Iff.rfl
@[simp] theorem holds_imp : (imp φ ψ).Holds v ↔ (φ.Holds v → ψ.Holds v) := Iff.rfl
@[simp] theorem holds_iff : (iff φ ψ).Holds v ↔ (φ.Holds v ↔ ψ.Holds v) := Iff.rfl
@[simp] theorem holds_all : (all x B φ).Holds v ↔
    ∀ a ∈ B, φ.Defined (update v x (some a)) → φ.Holds (update v x (some a)) := Iff.rfl
@[simp] theorem holds_ex : (ex x B φ).Holds v ↔
    ∃ a ∈ B, φ.Defined (update v x (some a)) ∧ φ.Holds (update v x (some a)) := Iff.rfl

end simp

/-- **Section 4.3, sentences.** The variables with a free occurrence in a formula: those of its
terms that are not bound by a quantifier above them. -/
def freeVars : Formula S → Set ℕ
  | rel _ ts => ⋃ i, (ts i).vars
  | and φ ψ => φ.freeVars ∪ ψ.freeVars
  | or φ ψ => φ.freeVars ∪ ψ.freeVars
  | not φ => φ.freeVars
  | imp φ ψ => φ.freeVars ∪ ψ.freeVars
  | iff φ ψ => φ.freeVars ∪ ψ.freeVars
  | all x _ φ => φ.freeVars \ {x}
  | ex x _ φ => φ.freeVars \ {x}

/-- **Section 4.3, sentences.** A _sentence_ is a formula in which no variable occurs free. -/
def IsSentence (φ : Formula S) : Prop := φ.freeVars = ∅

/-- **Section 4.3, sentences.** A sentence is _defined_ when all its closed terms are: it is
defined under the empty valuation. -/
def IsDefined (φ : Formula S) : Prop := φ.Defined Valuation.empty

/-- **Section 4.3, sentences.** A sentence is _true_ when it holds under the empty
valuation. -/
def IsTrue (φ : Formula S) : Prop := φ.Holds Valuation.empty

theorem update_congr_of_diff {v w : Valuation S} {F : Set ℕ} {x : ℕ}
    (h : ∀ y ∈ F \ {x}, v y = w y) (o : Option S) : ∀ y ∈ F, update v x o y = update w x o y := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx
    simp
  · rw [update_of_ne hyx, update_of_ne hyx]
    exact h y ⟨hy, hyx⟩

/-- **Section 4.3.** Whether a formula is defined depends only on the values of its free
variables. -/
theorem defined_congr {φ : Formula S} {v w : Valuation S} (h : ∀ x ∈ φ.freeVars, v x = w x) :
    φ.Defined v ↔ φ.Defined w := by
  induction φ generalizing v w with
  | rel P ts =>
    exact forall_congr' fun i => Term.defined_congr fun x hx => h x (mem_iUnion.2 ⟨i, hx⟩)
  | and φ ψ ih₁ ih₂ | or φ ψ ih₁ ih₂ | imp φ ψ ih₁ ih₂ | iff φ ψ ih₁ ih₂ =>
    exact and_congr (ih₁ fun x hx => h x (Or.inl hx)) (ih₂ fun x hx => h x (Or.inr hx))
  | not φ ih => exact ih h
  | all x P φ ih | ex x P φ ih => exact ih (update_congr_of_diff h none)

/-- **Section 4.3.** The truth of a formula depends only on the values of its free variables:
"a formula has no particular meaning until values are assigned to its free variables", and once
they are, nothing else matters. -/
theorem holds_congr {φ : Formula S} {v w : Valuation S} (h : ∀ x ∈ φ.freeVars, v x = w x) :
    φ.Holds v ↔ φ.Holds w := by
  induction φ generalizing v w with
  | rel P ts =>
    have h' : ∀ i (b : S), (ts i).Names v b ↔ (ts i).Names w b := fun i b =>
      Term.names_congr fun x hx => h x (mem_iUnion.2 ⟨i, hx⟩)
    simp only [holds_rel, h']
  | and φ ψ ih₁ ih₂ =>
    exact and_congr (ih₁ fun x hx => h x (Or.inl hx)) (ih₂ fun x hx => h x (Or.inr hx))
  | or φ ψ ih₁ ih₂ =>
    exact or_congr (ih₁ fun x hx => h x (Or.inl hx)) (ih₂ fun x hx => h x (Or.inr hx))
  | not φ ih => exact not_congr (ih h)
  | imp φ ψ ih₁ ih₂ =>
    exact imp_congr (ih₁ fun x hx => h x (Or.inl hx)) (ih₂ fun x hx => h x (Or.inr hx))
  | iff φ ψ ih₁ ih₂ =>
    exact iff_congr (ih₁ fun x hx => h x (Or.inl hx)) (ih₂ fun x hx => h x (Or.inr hx))
  | all x P φ ih =>
    refine forall₂_congr fun a _ => ?_
    exact imp_congr (defined_congr (update_congr_of_diff h _)) (ih (update_congr_of_diff h _))
  | ex x P φ ih =>
    refine exists_congr fun a => and_congr_right fun _ => ?_
    exact and_congr (defined_congr (update_congr_of_diff h _)) (ih (update_congr_of_diff h _))

/-- **Section 4.3, sentences.** A sentence has a fixed meaning: its truth does not depend on
the valuation. In particular it is true under some valuation if and only if it is true. -/
theorem IsSentence.holds_iff {φ : Formula S} (hφ : φ.IsSentence) (v : Valuation S) :
    φ.Holds v ↔ φ.IsTrue :=
  holds_congr fun x hx => by rw [IsSentence] at hφ; rw [hφ] at hx; exact hx.elim

/-- **Section 4.3, sentences.** Whether a sentence is defined does not depend on the
valuation. -/
theorem IsSentence.defined_iff {φ : Formula S} (hφ : φ.IsSentence) (v : Valuation S) :
    φ.Defined v ↔ φ.IsDefined :=
  defined_congr fun x hx => by rw [IsSentence] at hφ; rw [hφ] at hx; exact hx.elim

end Formula

/-!
### Substituting constants

The book writes $`\varphi(s)` for the result of replacing the free occurrences of a variable
$`x` in $`\varphi` by the constant $`s`. Substitution is defined here and shown to agree with
giving $`x` the value $`s`, which is how the truth conditions above were phrased.
-/

namespace Term

variable {S : Type u}

/-- **Section 4.3, truth and quantification.** Replace the variable $`x` by the constant $`s`
throughout a term. -/
def subst (x : ℕ) (s : S) : Term S → Term S
  | var y => if y = x then const s else var y
  | const c => const c
  | func A f ts => func A f fun i => (ts i).subst x s

theorem names_subst {x : ℕ} {s : S} {t : Term S} {v : Valuation S} {a : S} :
    (t.subst x s).Names v a ↔ t.Names (update v x (some s)) a := by
  induction t generalizing a with
  | var y =>
    by_cases h : y = x
    · subst h
      simp [subst]
    · simp [subst, h]
  | const c => rfl
  | func A f ts ih => simp only [subst, names_func, ih]

theorem closed_subst {x : ℕ} {s : S} {t : Term S} {v : Valuation S} :
    (t.subst x s).Closed v ↔ t.Closed (update v x (some s)) := by
  induction t with
  | var y =>
    by_cases h : y = x
    · subst h
      simp [subst]
    · simp [subst, h]
  | const c => rfl
  | func A f ts ih => simp only [subst, closed_func, ih]

theorem defined_subst {x : ℕ} {s : S} {t : Term S} {v : Valuation S} :
    (t.subst x s).Defined v ↔ t.Defined (update v x (some s)) := by
  induction t with
  | var y =>
    by_cases h : y = x
    · subst h
      simp [subst]
    · simp [subst, h]
  | const c => rfl
  | func A f ts ih =>
    have hn : (func A f fun i => (ts i).subst x s).Denotes v ↔
        (func A f ts).Denotes (update v x (some s)) :=
      exists_congr fun a => names_subst (t := func A f ts)
    simp only [subst, defined_func, ih, closed_subst, hn]

end Term

namespace Formula

variable {S : Type u}

/-- **Section 4.3, truth and quantification.** The formula $`\varphi(s)`: replace the free
occurrences of the variable $`x` in $`\varphi` by the constant $`s`. Occurrences in the scope of
a quantifier that binds $`x` are bound and are left alone. -/
def subst (x : ℕ) (s : S) : Formula S → Formula S
  | rel P ts => rel P fun i => (ts i).subst x s
  | and φ ψ => and (φ.subst x s) (ψ.subst x s)
  | or φ ψ => or (φ.subst x s) (ψ.subst x s)
  | not φ => not (φ.subst x s)
  | imp φ ψ => imp (φ.subst x s) (ψ.subst x s)
  | iff φ ψ => iff (φ.subst x s) (ψ.subst x s)
  | all y P φ => if y = x then all y P φ else all y P (φ.subst x s)
  | ex y P φ => if y = x then ex y P φ else ex y P (φ.subst x s)

/-- **Section 4.3, truth and quantification.** $`\varphi(s)` is defined under a valuation
exactly when $`\varphi` is defined once $`x` is given the value $`s`. -/
theorem defined_subst {x : ℕ} {s : S} {φ : Formula S} {v : Valuation S} :
    (φ.subst x s).Defined v ↔ φ.Defined (update v x (some s)) := by
  induction φ generalizing v with
  | rel P ts => exact forall_congr' fun i => Term.defined_subst
  | and φ ψ ih₁ ih₂ | or φ ψ ih₁ ih₂ | imp φ ψ ih₁ ih₂ | iff φ ψ ih₁ ih₂ =>
    exact and_congr ih₁ ih₂
  | not φ ih => exact ih
  | all y P φ ih | ex y P φ ih =>
    by_cases h : y = x
    · subst h
      simp [subst]
    · simp only [subst, h, ite_false, defined_all, defined_ex, ih, update_comm h]

/-- **Section 4.3, truth and quantification.** $`\varphi(s)` is true under a valuation exactly
when $`\varphi` is true once $`x` is given the value $`s`. This identifies the book's truth
conditions for quantifiers, stated with substituted constants, with the ones used here. -/
theorem holds_subst {x : ℕ} {s : S} {φ : Formula S} {v : Valuation S} :
    (φ.subst x s).Holds v ↔ φ.Holds (update v x (some s)) := by
  induction φ generalizing v with
  | rel P ts => simp only [subst, holds_rel, Term.names_subst]
  | and φ ψ ih₁ ih₂ => exact and_congr ih₁ ih₂
  | or φ ψ ih₁ ih₂ => exact or_congr ih₁ ih₂
  | not φ ih => exact not_congr ih
  | imp φ ψ ih₁ ih₂ => exact imp_congr ih₁ ih₂
  | iff φ ψ ih₁ ih₂ => exact iff_congr ih₁ ih₂
  | all y P φ ih =>
    by_cases h : y = x
    · subst h
      simp [subst]
    · simp only [subst, h, ite_false, holds_all, ih, defined_subst, update_comm h]
  | ex y P φ ih =>
    by_cases h : y = x
    · subst h
      simp [subst]
    · simp only [subst, h, ite_false, holds_ex, ih, defined_subst, update_comm h]

/-- **Section 4.3, truth of a universal sentence.** $`(\forall x \in P)\varphi` is true if and
only if, for all $`s` in $`P`, if the sentence $`\varphi(s)` is defined then it is true. -/
theorem isTrue_all_iff {x : ℕ} {P : Set S} {φ : Formula S} :
    (all x P φ).IsTrue ↔ ∀ s ∈ P, (φ.subst x s).IsDefined → (φ.subst x s).IsTrue := by
  simp only [IsTrue, IsDefined, holds_all, holds_subst, defined_subst]

/-- **Section 4.3, truth of an existential sentence.** $`(\exists x \in P)\varphi` is true if
and only if there is some $`s` in $`P` for which $`\varphi(s)` is defined and true. -/
theorem isTrue_ex_iff {x : ℕ} {P : Set S} {φ : Formula S} :
    (ex x P φ).IsTrue ↔ ∃ s ∈ P, (φ.subst x s).IsDefined ∧ (φ.subst x s).IsTrue := by
  simp only [IsTrue, IsDefined, holds_ex, holds_subst, defined_subst]

end Formula

/-!
### The language of a structure

The types above are the language of the full structure. A formula belongs to the language of a
structure when its function symbols, relation symbols and quantifier bounds are taken from the
structure.
-/

/-- **Section 4.3.** A term of the language of a structure: every function symbol in it is one
of the functions of the structure. Every element of the universe is allowed as a constant. -/
def Term.Over {S : Type u} (𝔖 : RelStructure S) : Term S → Prop
  | .var _ => True
  | .const _ => True
  | .func (m := m) A f ts => (⟨A, f⟩ : Σ A : Set (Fin m → S), A → S) ∈ 𝔖.Fun m ∧
      ∀ i, (ts i).Over 𝔖

/-- **Section 4.3.** A formula of the language of a structure: its terms are terms of that
language, its relation symbols are relations of the structure, and the bound of each quantifier
is a unary relation of the structure. -/
def Formula.Over {S : Type u} (𝔖 : RelStructure S) : Formula S → Prop
  | .rel (k := k) P ts => P ∈ 𝔖.Rel k ∧ ∀ i, (ts i).Over 𝔖
  | .and φ ψ => φ.Over 𝔖 ∧ ψ.Over 𝔖
  | .or φ ψ => φ.Over 𝔖 ∧ ψ.Over 𝔖
  | .not φ => φ.Over 𝔖
  | .imp φ ψ => φ.Over 𝔖 ∧ ψ.Over 𝔖
  | .iff φ ψ => φ.Over 𝔖 ∧ ψ.Over 𝔖
  | .all _ P φ => unaryRel P ∈ 𝔖.Rel 1 ∧ φ.Over 𝔖
  | .ex _ P φ => unaryRel P ∈ 𝔖.Rel 1 ∧ φ.Over 𝔖

/-- **Section 4.3.** Every term is a term of the language of the full structure. -/
theorem Term.over_full {S : Type u} (t : Term S) : t.Over (RelStructure.full S) := by
  induction t with
  | var x => trivial
  | const s => trivial
  | func A f ts ih => exact ⟨mem_univ _, ih⟩

/-- **Section 4.3.** Every formula is a formula of the language of the full structure. -/
theorem Formula.over_full {S : Type u} (φ : Formula S) : φ.Over (RelStructure.full S) := by
  induction φ with
  | rel P ts => exact ⟨mem_univ _, fun i => (ts i).over_full⟩
  | and φ ψ ih₁ ih₂ | or φ ψ ih₁ ih₂ | imp φ ψ ih₁ ih₂ | iff φ ψ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | not φ ih => exact ih
  | all x P φ ih | ex x P φ ih => exact ⟨mem_univ _, ih⟩

/-!
## 4.4 Star-Transforms

The star-transform of a formula of the language of the full structure on a set is a formula of
the language of the enlarged structure. It is obtained by putting a star on every function
symbol, on every relation symbol and on the bound of every quantifier; variables are left alone,
and a constant $`s` is replaced by its copy $`{}^*s` in the star type, which the book identifies
with $`s`.
-/

section Star

variable {α αS : Type u} [StarType α αS]

/-- **Section 4.4.** The star-transform $`{}^*\tau` of a term: every function symbol $`f` is
replaced by its extension $`{}^*f`, whose domain is the enlargement of the domain of $`f`.
Variables are unchanged and a constant is replaced by its standard copy. -/
noncomputable def Term.star : Term α → Term αS
  | .var x => .var x
  | .const s => .const (of s)
  | .func A f ts => .func (starRel A) (starMapOnN A f) fun i => (ts i).star

/-- **Section 4.4.** The star-transform $`{}^*\varphi` of a formula: terms are replaced by their
star-transforms, the relation symbol $`P` of an atomic formula by $`{}^*P`, and the bound $`P`
of a quantifier by $`{}^*P`. -/
noncomputable def Formula.star : Formula α → Formula αS
  | .rel P ts => .rel (starRel P) fun i => (ts i).star
  | .and φ ψ => .and φ.star ψ.star
  | .or φ ψ => .or φ.star ψ.star
  | .not φ => .not φ.star
  | .imp φ ψ => .imp φ.star ψ.star
  | .iff φ ψ => .iff φ.star ψ.star
  | .all x P φ => .all x (⋆P) φ.star
  | .ex x P φ => .ex x (⋆P) φ.star

/-- **Section 4.4.** The star-transform does not change the variables of a term. -/
theorem Term.vars_star (t : Term α) : (t.star : Term αS).vars = t.vars := by
  induction t with
  | var x => rfl
  | const s => rfl
  | func A f ts ih => simp only [Term.star, Term.vars, ih]

/-- **Section 4.4.** The star-transform does not change the free variables of a formula. -/
theorem Formula.freeVars_star (φ : Formula α) : (φ.star : Formula αS).freeVars = φ.freeVars := by
  induction φ with
  | rel P ts => simp only [Formula.star, Formula.freeVars, Term.vars_star]
  | and φ ψ ih₁ ih₂ | or φ ψ ih₁ ih₂ | imp φ ψ ih₁ ih₂ | iff φ ψ ih₁ ih₂ =>
    simp only [Formula.star, Formula.freeVars, ih₁, ih₂]
  | not φ ih => exact ih
  | all x P φ ih | ex x P φ ih => simp only [Formula.star, Formula.freeVars, ih]

/-- **Section 4.4.** The star-transform of a sentence is a sentence. -/
theorem Formula.IsSentence.star {φ : Formula α} (hφ : φ.IsSentence) :
    (φ.star : Formula αS).IsSentence := by
  rw [Formula.IsSentence, Formula.freeVars_star]
  exact hφ

/-- **Section 4.4.** The star-transform of a term is a term of the language of the enlarged
structure. -/
theorem Term.star_over (t : Term α) : (t.star : Term αS).Over (RelStructure.star α) := by
  induction t with
  | var x => trivial
  | const s => trivial
  | func A f ts ih => exact ⟨RelStructure.mem_star_fun.2 ⟨⟨A, f⟩, rfl⟩, ih⟩

/-- **Section 4.4.** The star-transform of a formula of the language of the full structure on a
set is a formula of the language of the enlarged structure: of $`\mathcal L_{{}^*\mathfrak R}`
when the set is the reals. -/
theorem Formula.star_over (φ : Formula α) :
    (φ.star : Formula αS).Over (RelStructure.star α) := by
  induction φ with
  | rel P ts => exact ⟨RelStructure.mem_star_rel.2 ⟨P, rfl⟩, fun i => (ts i).star_over⟩
  | and φ ψ ih₁ ih₂ | or φ ψ ih₁ ih₂ | imp φ ψ ih₁ ih₂ | iff φ ψ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | not φ ih => exact ih
  | all x P φ ih | ex x P φ ih => exact ⟨unaryRel_mem_star_iff.2 ⟨P, rfl⟩, ih⟩

/-- **Section 4.4.** Substituting a constant commutes with the star-transform: the transform of
$`\tau(s)` is $`{}^*\tau({}^*s)`. -/
theorem Term.star_subst (x : ℕ) (s : α) (t : Term α) :
    ((t.subst x s).star : Term αS) = t.star.subst x (of s) := by
  induction t with
  | var y =>
    by_cases h : y = x
    · simp [Term.subst, Term.star, h]
    · simp [Term.subst, Term.star, h]
  | const c => rfl
  | func A f ts ih => simp only [Term.subst, Term.star, ih]

/-- **Section 4.4.** Substituting a constant commutes with the star-transform: the transform of
$`\varphi(s)` is $`{}^*\varphi({}^*s)`. -/
theorem Formula.star_subst (x : ℕ) (s : α) (φ : Formula α) :
    ((φ.subst x s).star : Formula αS) = φ.star.subst x (of s) := by
  induction φ with
  | rel P ts => simp only [Formula.subst, Formula.star, Term.star_subst]
  | and φ ψ ih₁ ih₂ | or φ ψ ih₁ ih₂ | imp φ ψ ih₁ ih₂ | iff φ ψ ih₁ ih₂ =>
    simp only [Formula.subst, Formula.star, ih₁, ih₂]
  | not φ ih => simp only [Formula.subst, Formula.star, ih]
  | all y P φ ih | ex y P φ ih =>
    by_cases h : y = x
    · simp [Formula.subst, Formula.star, h]
    · simp [Formula.subst, Formula.star, h, ih]

end Star

end Goldblatt
