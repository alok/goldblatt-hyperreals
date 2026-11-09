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

/-- **Section 4.3.** The empty valuation gives no variable a value. -/
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

/-- **Section 4.3.** A variable names its value, if it has one. -/
@[simp] theorem names_var {x : ℕ} {v : Valuation S} {a : S} :
    (var x).Names v a ↔ v x = some a := Iff.rfl

/-- **Section 4.3.** A constant names itself. -/
@[simp] theorem names_const {s : S} {v : Valuation S} {a : S} :
    (const s).Names v a ↔ s = a := Iff.rfl

/-- **Section 4.3.** Unfolding of what a function symbol applied to terms names. -/
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

/-- **Section 4.3.** A variable is closed when it has a value. -/
@[simp] theorem closed_var {x : ℕ} {v : Valuation S} : (var x : Term S).Closed v ↔ v x ≠ none :=
  Iff.rfl

/-- **Section 4.3.** A constant is closed. -/
@[simp] theorem closed_const {s : S} {v : Valuation S} : (const s).Closed v := trivial

/-- **Section 4.3.** A function symbol applied to terms is closed when the terms are. -/
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

/-- **Section 4.3.** A variable is defined: it has no closed subterm unless it has a value. -/
@[simp] theorem defined_var {x : ℕ} {v : Valuation S} : (var x : Term S).Defined v := trivial

/-- **Section 4.3.** A constant is defined. -/
@[simp] theorem defined_const {s : S} {v : Valuation S} : (const s).Defined v := trivial

/-- **Section 4.3.** Unfolding of definedness for a function symbol applied to terms. -/
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

/-- **Section 4.3.** Unfolding of definedness for an atomic formula. -/
theorem defined_rel : (rel P ts).Defined v ↔ ∀ i, (ts i).Defined v := Iff.rfl
/-- **Section 4.3.** Unfolding of definedness for a conjunction. -/
@[simp] theorem defined_and : (and φ ψ).Defined v ↔ φ.Defined v ∧ ψ.Defined v := Iff.rfl
/-- **Section 4.3.** Unfolding of definedness for a disjunction. -/
@[simp] theorem defined_or : (or φ ψ).Defined v ↔ φ.Defined v ∧ ψ.Defined v := Iff.rfl
/-- **Section 4.3.** Unfolding of definedness for a negation. -/
@[simp] theorem defined_not : (not φ).Defined v ↔ φ.Defined v := Iff.rfl
/-- **Section 4.3.** Unfolding of definedness for an implication. -/
@[simp] theorem defined_imp : (imp φ ψ).Defined v ↔ φ.Defined v ∧ ψ.Defined v := Iff.rfl
/-- **Section 4.3.** Unfolding of definedness for a biconditional. -/
@[simp] theorem defined_iff : (iff φ ψ).Defined v ↔ φ.Defined v ∧ ψ.Defined v := Iff.rfl
/-- **Section 4.3.** Unfolding of definedness for a bounded universal quantifier. -/
@[simp] theorem defined_all : (all x B φ).Defined v ↔ φ.Defined (update v x none) := Iff.rfl
/-- **Section 4.3.** Unfolding of definedness for a bounded existential quantifier. -/
@[simp] theorem defined_ex : (ex x B φ).Defined v ↔ φ.Defined (update v x none) := Iff.rfl

/-- **Section 4.3.** Unfolding of the truth condition for an atomic formula. -/
theorem holds_rel :
    (rel P ts).Holds v ↔ ∃ args, (∀ i, (ts i).Names v (args i)) ∧ args ∈ P := Iff.rfl
/-- **Section 4.3.** Unfolding of the truth condition for a conjunction. -/
@[simp] theorem holds_and : (and φ ψ).Holds v ↔ φ.Holds v ∧ ψ.Holds v := Iff.rfl
/-- **Section 4.3.** Unfolding of the truth condition for a disjunction. -/
@[simp] theorem holds_or : (or φ ψ).Holds v ↔ φ.Holds v ∨ ψ.Holds v := Iff.rfl
/-- **Section 4.3.** Unfolding of the truth condition for a negation. -/
@[simp] theorem holds_not : (not φ).Holds v ↔ ¬φ.Holds v := Iff.rfl
/-- **Section 4.3.** Unfolding of the truth condition for an implication. -/
@[simp] theorem holds_imp : (imp φ ψ).Holds v ↔ (φ.Holds v → ψ.Holds v) := Iff.rfl
/-- **Section 4.3.** Unfolding of the truth condition for a biconditional. -/
@[simp] theorem holds_iff : (iff φ ψ).Holds v ↔ (φ.Holds v ↔ ψ.Holds v) := Iff.rfl
/-- **Section 4.3.** Unfolding of the truth condition for a bounded universal quantifier. -/
@[simp] theorem holds_all : (all x B φ).Holds v ↔
    ∀ a ∈ B, φ.Defined (update v x (some a)) → φ.Holds (update v x (some a)) := Iff.rfl
/-- **Section 4.3.** Unfolding of the truth condition for a bounded existential quantifier. -/
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

/-- **Section 4.3.** Two valuations that agree on a set of variables other than $`x` agree on the
whole set once $`x` is treated the same way in both. -/
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

/-- **Section 4.3, sentences.** Truth depends only on the values given to the free variables of
a formula: two valuations that agree on them make the same formulas true. -/
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

/-- **Section 4.3.** What a term names after the constant $`s` is substituted for $`x` is what it
names when $`x` is given the value $`s`. -/
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

/-- **Section 4.3.** Substituting a constant for $`x` and giving $`x` a value have the same effect
on closedness. -/
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

/-- **Section 4.3.** Substituting a constant for $`x` and giving $`x` a value have the same effect
on definedness of a term. -/
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

/-- **Section 4.3, truth of a universal sentence.** A bounded universal sentence
$`(\forall x \in P)\varphi` is true exactly when every instance $`\varphi(s)`, $`s \in P`, that
is a defined sentence is true. Undefined instances are passed over. -/
theorem isTrue_all_iff {x : ℕ} {P : Set S} {φ : Formula S} :
    (all x P φ).IsTrue ↔ ∀ s ∈ P, (φ.subst x s).IsDefined → (φ.subst x s).IsTrue := by
  simp only [IsTrue, IsDefined, holds_all, holds_subst, defined_subst]

/-- **Section 4.3, truth of an existential sentence.** A bounded existential sentence
$`(\exists x \in P)\varphi` is true exactly when some instance $`\varphi(s)` with $`s \in P` is
both defined and true. -/
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

/-- **Section 4.3.** Substituting a constant for a variable keeps a term in the language of a
structure, since every element of the universe is available as a constant. -/
theorem Term.Over.subst {S : Type u} {𝔖 : RelStructure S} {t : Term S} (h : t.Over 𝔖) (x : ℕ)
    (s : S) : (t.subst x s).Over 𝔖 := by
  induction t with
  | var y =>
    by_cases hy : y = x
    · simp [Term.subst, hy, Term.Over]
    · simp [Term.subst, hy, Term.Over]
  | const c => trivial
  | func A f ts ih => exact ⟨h.1, fun i => ih i (h.2 i)⟩

/-- **Section 4.3.** Substituting a constant for a free variable keeps a formula in the language
of a structure: $`\varphi(s)` is a formula of the language whenever $`\varphi` is, for any
element $`s` of the universe. -/
theorem Formula.Over.subst {S : Type u} {𝔖 : RelStructure S} {φ : Formula S} (h : φ.Over 𝔖)
    (x : ℕ) (s : S) : (φ.subst x s).Over 𝔖 := by
  induction φ with
  | rel P ts => exact ⟨h.1, fun i => (h.2 i).subst x s⟩
  | and φ ψ ih₁ ih₂ | or φ ψ ih₁ ih₂ | imp φ ψ ih₁ ih₂ | iff φ ψ ih₁ ih₂ =>
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | not φ ih => exact ih h
  | all y P φ ih | ex y P φ ih =>
    by_cases hy : y = x
    · simpa [Formula.subst, hy] using h
    · simp only [Formula.subst, hy, ite_false]
      exact ⟨h.1, ih h.2⟩

/-!
### Customary notation

The book writes binary operations infix, writes $`\tau \in P` for an atomic formula with a
unary relation, and $`\tau_1 = \tau_2`, $`\tau_1 < \tau_2` for the identity and order relations.
The definitions below provide these shapes of term and formula, with the lemmas that say what
they name and when they hold; each is a special case of the general function and relation
symbols.
-/

/-- **Section 4.3, helper.** A statement about some one-tuple is a statement about some element. -/
theorem exists_fin_one_pi {S : Type u} {P : (Fin 1 → S) → Prop} :
    (∃ a, P a) ↔ ∃ a, P fun _ => a :=
  ⟨fun ⟨a, h⟩ => ⟨a 0, by
    have e : (fun _ => a 0) = a := funext fun i => by rw [Fin.eq_zero i]
    rwa [e]⟩, fun ⟨a, h⟩ => ⟨_, h⟩⟩

/-- **Section 4.3, helper.** A statement about some pair, as a two-tuple, is a statement about some two elements. -/
theorem exists_fin_two_pi {S : Type u} {P : (Fin 2 → S) → Prop} :
    (∃ a, P a) ↔ ∃ a b, P ![a, b] :=
  ⟨fun ⟨a, h⟩ => ⟨a 0, a 1, by
    have e : ![a 0, a 1] = a := by
      funext i
      fin_cases i <;> rfl
    rwa [e]⟩, fun ⟨a, b, h⟩ => ⟨_, h⟩⟩

namespace Term

variable {S : Type u}

/-- **Section 4.3, notation.** The term $`f(\tau)` for a total function $`f` of one argument. -/
def app₁ (f : S → S) (t : Term S) : Term S :=
  func univ (fun a => f (a.1 0)) ![t]

/-- **Section 4.3, notation.** The term $`f(\tau_1, \tau_2)` for a total function $`f` of two
arguments, such as $`\tau_1 + \tau_2`. -/
def app₂ (f : S → S → S) (t u : Term S) : Term S :=
  func univ (fun a => f (a.1 0) (a.1 1)) ![t, u]

/-- **Section 4.3, notation.** The term $`f(\tau)` for a partial function $`f` of one argument
with domain $`A`, such as $`\tan \tau` or $`s_\tau` for a sequence $`s`. -/
def papp₁ (A : Set S) (f : A → S) (t : Term S) : Term S :=
  func (unaryRel A) (fun a => f ⟨a.1 0, a.2⟩) ![t]

section generic

variable {v : Valuation S} {t u : Term S} {c : S}

/-- **Section 4.3.** What a function symbol of one argument applied to a term names. -/
theorem names_func_one {A : Set (Fin 1 → S)} {g : A → S} :
    (func A g ![t]).Names v c ↔
      ∃ a, t.Names v a ∧ ∃ h : (fun _ => a) ∈ A, g ⟨fun _ => a, h⟩ = c := by
  rw [names_func, exists_fin_one_pi]
  simp only [Fin.forall_fin_one, Matrix.cons_val_zero]

/-- **Section 4.3.** What a function symbol of two arguments applied to terms names. -/
theorem names_func_two {A : Set (Fin 2 → S)} {g : A → S} :
    (func A g ![t, u]).Names v c ↔
      ∃ a b, t.Names v a ∧ u.Names v b ∧ ∃ h : ![a, b] ∈ A, g ⟨![a, b], h⟩ = c := by
  rw [names_func, exists_fin_two_pi]
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, and_assoc]

/-- **Section 4.3.** Closedness for a function symbol of one argument. -/
theorem closed_func_one {A : Set (Fin 1 → S)} {g : A → S} :
    (func A g ![t]).Closed v ↔ t.Closed v := by
  simp only [closed_func, Fin.forall_fin_one, Matrix.cons_val_zero]

/-- **Section 4.3.** Closedness for a function symbol of two arguments. -/
theorem closed_func_two {A : Set (Fin 2 → S)} {g : A → S} :
    (func A g ![t, u]).Closed v ↔ t.Closed v ∧ u.Closed v := by
  simp only [closed_func, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Section 4.3.** Definedness for a function symbol of one argument: the argument is defined and,
if it is closed, what it names lies in the domain. -/
theorem defined_func_one {A : Set (Fin 1 → S)} {g : A → S} :
    (func A g ![t]).Defined v ↔
      t.Defined v ∧ (t.Closed v → ∃ a, t.Names v a ∧ (fun _ => a) ∈ A) := by
  rw [defined_func, Denotes]
  simp only [names_func_one, Fin.forall_fin_one, Matrix.cons_val_zero]
  refine and_congr_right fun _ => imp_congr_right fun _ => ?_
  exact ⟨fun ⟨_, a, ha, h, _⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨_, a, ha, h, rfl⟩⟩

/-- **Section 4.3.** Definedness for a function symbol of two arguments: the arguments are defined
and, if they are closed, the pair they name lies in the domain. -/
theorem defined_func_two {A : Set (Fin 2 → S)} {g : A → S} :
    (func A g ![t, u]).Defined v ↔ t.Defined v ∧ u.Defined v ∧
      (t.Closed v → u.Closed v → ∃ a b, t.Names v a ∧ u.Names v b ∧ ![a, b] ∈ A) := by
  rw [defined_func, Denotes]
  simp only [names_func_two, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    and_assoc, and_imp]
  refine and_congr_right fun _ => and_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  exact ⟨fun ⟨_, a, b, ha, hb, h, _⟩ => ⟨a, b, ha, hb, h⟩,
    fun ⟨a, b, ha, hb, h⟩ => ⟨_, a, b, ha, hb, h, rfl⟩⟩

end generic

section helpers

variable {v : Valuation S} {t u : Term S} {c : S}

/-- **Section 4.3.** $`f(\tau)` names $`f(a)` when $`\tau` names $`a`. -/
@[simp] theorem names_app₁ {f : S → S} :
    (app₁ f t).Names v c ↔ ∃ a, t.Names v a ∧ f a = c := by
  simp only [app₁, names_func_one, mem_univ, exists_true_left]

/-- **Section 4.3.** $`f(\tau_1, \tau_2)` names $`f(a, b)` when $`\tau_1` names $`a` and $`\tau_2`
names $`b`. -/
@[simp] theorem names_app₂ {f : S → S → S} :
    (app₂ f t u).Names v c ↔ ∃ a b, t.Names v a ∧ u.Names v b ∧ f a b = c := by
  simp only [app₂, names_func_two, mem_univ, exists_true_left, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- **Section 4.3.** For a partial function $`f`, the term $`f(\tau)` names $`f(a)` when $`\tau`
names an element $`a` of the domain. -/
@[simp] theorem names_papp₁ {A : Set S} {f : A → S} :
    (papp₁ A f t).Names v c ↔ ∃ a, t.Names v a ∧ ∃ h : a ∈ A, f ⟨a, h⟩ = c := by
  simp only [papp₁, names_func_one]
  rfl

/-- **Section 4.3.** $`f(\tau)` is closed when $`\tau` is. -/
@[simp] theorem closed_app₁ {f : S → S} : (app₁ f t).Closed v ↔ t.Closed v := closed_func_one

/-- **Section 4.3.** $`f(\tau_1, \tau_2)` is closed when both arguments are. -/
@[simp] theorem closed_app₂ {f : S → S → S} :
    (app₂ f t u).Closed v ↔ t.Closed v ∧ u.Closed v := closed_func_two

/-- **Section 4.3.** For a partial function $`f`, the term $`f(\tau)` is closed when $`\tau` is. -/
@[simp] theorem closed_papp₁ {A : Set S} {f : A → S} : (papp₁ A f t).Closed v ↔ t.Closed v :=
  closed_func_one

/-- **Section 4.3.** A term built with a total function is defined as soon as its argument
is. -/
@[simp] theorem defined_app₁ {f : S → S} : (app₁ f t).Defined v ↔ t.Defined v := by
  rw [app₁, defined_func_one]
  refine and_iff_left_of_imp fun hd hc => ?_
  obtain ⟨a, ha⟩ := hd.denotes hc
  exact ⟨a, ha, mem_univ _⟩

/-- **Section 4.3.** A term built with a total function of two arguments is defined as soon as its
arguments are. -/
@[simp] theorem defined_app₂ {f : S → S → S} :
    (app₂ f t u).Defined v ↔ t.Defined v ∧ u.Defined v := by
  rw [app₂, defined_func_two, ← and_assoc]
  refine and_iff_left_of_imp fun hd hc hc' => ?_
  obtain ⟨a, ha⟩ := hd.1.denotes hc
  obtain ⟨b, hb⟩ := hd.2.denotes hc'
  exact ⟨a, b, ha, hb, mem_univ _⟩

/-- **Section 4.3.** A term $`f(\tau)` with $`f` partial is defined when $`\tau` is and, if
$`\tau` is closed, the element it names lies in the domain of $`f`. -/
@[simp] theorem defined_papp₁ {A : Set S} {f : A → S} :
    (papp₁ A f t).Defined v ↔ t.Defined v ∧ (t.Closed v → ∃ a, t.Names v a ∧ a ∈ A) := by
  rw [papp₁, defined_func_one]
  rfl

end helpers

end Term

namespace Formula

variable {S : Type u}

/-- **Section 4.3, notation.** The membership formula $`\tau \in A`: the atomic formula of the
unary relation $`A`. -/
def mem (t : Term S) (A : Set S) : Formula S := rel (unaryRel A) ![t]

/-- **Section 4.3, notation.** The atomic formula $`P(\tau_1, \tau_2)` of a binary relation,
written infix for the familiar relations. -/
def rel₂ (P : S → S → Prop) (t u : Term S) : Formula S := rel {a | P (a 0) (a 1)} ![t, u]

/-- **Section 4.3, notation.** The formula $`\tau_1 = \tau_2`, the atomic formula of the identity
relation. -/
def eq (t u : Term S) : Formula S := rel₂ (fun a b => a = b) t u

/-- **Section 4.3, notation.** The formula $`\tau_1 < \tau_2` for terms of the language of the
reals. -/
def lt (t u : Term ℝ) : Formula ℝ := rel₂ (fun a b => a < b) t u

/-- **Section 4.3, notation.** The formula $`\tau_1 \le \tau_2` for terms of the language of the
reals. -/
def le (t u : Term ℝ) : Formula ℝ := rel₂ (fun a b => a ≤ b) t u

section generic

variable {v : Valuation S} {t u : Term S}

/-- **Section 4.3.** Truth of an atomic formula with a unary relation. -/
theorem holds_rel_one {P : Set (Fin 1 → S)} :
    (rel P ![t]).Holds v ↔ ∃ a, t.Names v a ∧ (fun _ => a) ∈ P := by
  rw [holds_rel, exists_fin_one_pi]
  simp only [Fin.forall_fin_one, Matrix.cons_val_zero]

/-- **Section 4.3.** Truth of an atomic formula with a binary relation. -/
theorem holds_rel_two {P : Set (Fin 2 → S)} :
    (rel P ![t, u]).Holds v ↔ ∃ a b, t.Names v a ∧ u.Names v b ∧ ![a, b] ∈ P := by
  rw [holds_rel, exists_fin_two_pi]
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, and_assoc]

/-- **Section 4.3.** An atomic formula with a unary relation is defined when its term is. -/
theorem defined_rel_one {P : Set (Fin 1 → S)} : (rel P ![t]).Defined v ↔ t.Defined v := by
  simp only [defined_rel, Fin.forall_fin_one, Matrix.cons_val_zero]

/-- **Section 4.3.** An atomic formula with a binary relation is defined when its terms are. -/
theorem defined_rel_two {P : Set (Fin 2 → S)} :
    (rel P ![t, u]).Defined v ↔ t.Defined v ∧ u.Defined v := by
  simp only [defined_rel, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]

end generic

section helpers

variable {v : Valuation S} {t u : Term S}

/-- **Section 4.3.** $`\tau \in A` is true when $`\tau` names a member of $`A`. -/
@[simp] theorem holds_mem {A : Set S} : (mem t A).Holds v ↔ ∃ a, t.Names v a ∧ a ∈ A :=
  holds_rel_one

/-- **Section 4.3.** $`P(\tau_1, \tau_2)` is true when the terms name elements related by $`P`. -/
@[simp] theorem holds_rel₂ {P : S → S → Prop} :
    (rel₂ P t u).Holds v ↔ ∃ a b, t.Names v a ∧ u.Names v b ∧ P a b :=
  holds_rel_two

/-- **Section 4.3.** $`\tau_1 = \tau_2` is true when the terms name the same element. -/
@[simp] theorem holds_eq : (eq t u).Holds v ↔ ∃ a b, t.Names v a ∧ u.Names v b ∧ a = b :=
  holds_rel_two

/-- **Section 4.3.** $`\tau_1 < \tau_2` is true when the terms name reals in that order. -/
@[simp] theorem holds_lt {t u : Term ℝ} {v : Valuation ℝ} :
    (lt t u).Holds v ↔ ∃ a b, t.Names v a ∧ u.Names v b ∧ a < b :=
  holds_rel_two

/-- **Section 4.3.** $`\tau_1 \le \tau_2` is true when the terms name reals in that order. -/
@[simp] theorem holds_le {t u : Term ℝ} {v : Valuation ℝ} :
    (le t u).Holds v ↔ ∃ a b, t.Names v a ∧ u.Names v b ∧ a ≤ b :=
  holds_rel_two

/-- **Section 4.3.** $`\tau \in A` is defined when $`\tau` is. -/
@[simp] theorem defined_mem {A : Set S} : (mem t A).Defined v ↔ t.Defined v := defined_rel_one

/-- **Section 4.3.** $`P(\tau_1, \tau_2)` is defined when both terms are. -/
@[simp] theorem defined_rel₂ {P : S → S → Prop} :
    (rel₂ P t u).Defined v ↔ t.Defined v ∧ u.Defined v := defined_rel_two

/-- **Section 4.3.** $`\tau_1 = \tau_2` is defined when both terms are. -/
@[simp] theorem defined_eq : (eq t u).Defined v ↔ t.Defined v ∧ u.Defined v := defined_rel_two

/-- **Section 4.3.** $`\tau_1 < \tau_2` is defined when both terms are. -/
@[simp] theorem defined_lt {t u : Term ℝ} {v : Valuation ℝ} :
    (lt t u).Defined v ↔ t.Defined v ∧ u.Defined v := defined_rel_two

/-- **Section 4.3.** $`\tau_1 \le \tau_2` is defined when both terms are. -/
@[simp] theorem defined_le {t u : Term ℝ} {v : Valuation ℝ} :
    (le t u).Defined v ↔ t.Defined v ∧ u.Defined v := defined_rel_two

end helpers

end Formula

/-!
The notation below is available after {lit}`open scoped Goldblatt.Lang`. It writes formulas
in a shape close to the book's: {lit}`∀' x ∈ P, φ` and {lit}`∃' x ∈ P, φ` for the bounded
quantifiers, {lit}`⋏`, {lit}`⋎`, {lit}`∼'`, {lit}`⟹`, {lit}`⟺` for the connectives, and primed
relation and operation signs between terms.
-/

namespace Lang

@[inherit_doc] scoped notation:50 t:51 " =' " u:51 => Formula.eq t u
@[inherit_doc] scoped notation:50 t:51 " <' " u:51 => Formula.lt t u
@[inherit_doc] scoped notation:50 t:51 " ≤' " u:51 => Formula.le t u
@[inherit_doc] scoped notation:50 t:51 " ∈' " A:51 => Formula.mem t A
@[inherit_doc] scoped infixr:35 " ⋏ " => Formula.and
@[inherit_doc] scoped infixr:30 " ⋎ " => Formula.or
@[inherit_doc] scoped notation:max "∼'" φ:max => Formula.not φ
@[inherit_doc] scoped infixr:25 " ⟹ " => Formula.imp
@[inherit_doc] scoped infix:20 " ⟺ " => Formula.iff
@[inherit_doc] scoped notation:15 "∀' " x:max " ∈ " P:51 ", " φ:15 => Formula.all x P φ
@[inherit_doc] scoped notation:15 "∃' " x:max " ∈ " P:51 ", " φ:15 => Formula.ex x P φ
/-- **Section 4.3, notation.** The sum of two terms of the language of the reals. -/
scoped notation:65 t:65 " +' " u:66 => Term.app₂ (fun a b : ℝ => a + b) t u
/-- **Section 4.3, notation.** The difference of two terms of the language of the reals. -/
scoped notation:65 t:65 " -' " u:66 => Term.app₂ (fun a b : ℝ => a - b) t u
/-- **Section 4.3, notation.** The product of two terms of the language of the reals. -/
scoped notation:70 t:70 " *' " u:71 => Term.app₂ (fun a b : ℝ => a * b) t u

end Lang

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

/-!
### Dropping the stars

The book drops the star from the transforms of familiar symbols: the transform of
$`\tau_1 = \tau_2` is again an equation, the transform of $`\tau_1 < \tau_2` an inequality, and
the transform of $`\tau \in A` is $`\tau \in {}^*A`. The lemmas below justify this for the
notation of Section 4.3: they compute what the star-transforms of those terms name and when
the star-transforms of those formulas hold, in terms of the extensions and enlargements of
Chapter 3.
-/

section StarNotation

variable {α αS : Type u} [StarType α αS]

/-- **Section 4.4.** The star-transform leaves a variable alone. -/
@[simp] theorem Term.star_var (x : ℕ) : ((Term.var x : Term α).star : Term αS) = .var x := rfl

/-- **Section 4.4.** The star-transform replaces a constant by its standard copy. -/
@[simp] theorem Term.star_const (s : α) : ((Term.const s).star : Term αS) = .const (of s) := rfl

/-- **Section 4.4.** The star-transform of a conjunction. -/
@[simp] theorem Formula.star_and (φ ψ : Formula α) :
    ((φ.and ψ).star : Formula αS) = φ.star.and ψ.star := rfl
/-- **Section 4.4.** The star-transform of a disjunction. -/
@[simp] theorem Formula.star_or (φ ψ : Formula α) :
    ((φ.or ψ).star : Formula αS) = φ.star.or ψ.star := rfl
/-- **Section 4.4.** The star-transform of a negation. -/
@[simp] theorem Formula.star_not (φ : Formula α) : (φ.not.star : Formula αS) = φ.star.not := rfl
/-- **Section 4.4.** The star-transform of an implication. -/
@[simp] theorem Formula.star_imp (φ ψ : Formula α) :
    ((φ.imp ψ).star : Formula αS) = φ.star.imp ψ.star := rfl
/-- **Section 4.4.** The star-transform of a biconditional. -/
@[simp] theorem Formula.star_iff (φ ψ : Formula α) :
    ((φ.iff ψ).star : Formula αS) = φ.star.iff ψ.star := rfl
/-- **Section 4.4.** The star-transform of a bounded universal quantifier. -/
@[simp] theorem Formula.star_all (x : ℕ) (P : Set α) (φ : Formula α) :
    ((Formula.all x P φ).star : Formula αS) = .all x (⋆P) φ.star := rfl
/-- **Section 4.4.** The star-transform of a bounded existential quantifier. -/
@[simp] theorem Formula.star_ex (x : ℕ) (P : Set α) (φ : Formula α) :
    ((Formula.ex x P φ).star : Formula αS) = .ex x (⋆P) φ.star := rfl

/-- **Section 4.4.** The star-transform of a one-tuple of terms. -/
theorem Term.star_vec_one (t : Term α) :
    (fun i => ((![t] : Fin 1 → Term α) i).star : Fin 1 → Term αS) = ![t.star] := by
  funext i
  rw [Fin.eq_zero i]
  rfl

/-- **Section 4.4.** The star-transform of a pair of terms. -/
theorem Term.star_vec_two (t u : Term α) :
    (fun i => ((![t, u] : Fin 2 → Term α) i).star : Fin 2 → Term αS) = ![t.star, u.star] := by
  funext i
  fin_cases i <;> rfl

/-- **Section 3.13.** The extension of a total function of one argument, regarded as a partial
function whose domain is everything, is the extension of Section 3.11. -/
theorem starMapOnN_univ_one (f : α → α) (a : αS)
    (h : (fun _ : Fin 1 => a) ∈ starRel (univ : Set (Fin 1 → α))) :
    starMapOnN univ (fun p : (univ : Set (Fin 1 → α)) => f (p.1 0)) ⟨fun _ => a, h⟩ = ⋆f a := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) a
  rw [starMap_ofSeq]
  exact (starMapOnN_ofSeq_eq_ofSeq (r := fun _ => r) h).2
    (Eventually.of_forall fun n => ⟨mem_univ _, rfl⟩)

/-- **Section 3.14.** A pair of classes of sequences, as a two-tuple, is the tuple of the classes of
the pair of sequences. -/
theorem vec_two_ofSeq (r s : ℕ → α) :
    (![ofSeq r, ofSeq s] : Fin 2 → αS) = fun i => ofSeq (![r, s] i) := by
  funext i
  fin_cases i <;> rfl

/-- **Exercise 3.12(5).** The extension of a total function of two arguments, regarded as a
partial function of pairs whose domain is everything, is the two-argument extension of
Chapter 3. -/
theorem starMapOnN_univ_two (f : α → α → α) (a b : αS)
    (h : ![a, b] ∈ starRel (univ : Set (Fin 2 → α))) :
    starMapOnN univ (fun p : (univ : Set (Fin 2 → α)) => f (p.1 0) (p.1 1)) ⟨![a, b], h⟩ =
      ⋆f a b := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) a
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := α) b
  rw [starMap₂_ofSeq]
  have key : ∀ (x : Fin 2 → αS) (hx : x ∈ starRel (univ : Set (Fin 2 → α))),
      x = (fun i => ofSeq (![r, s] i)) →
      starMapOnN univ (fun p : (univ : Set (Fin 2 → α)) => f (p.1 0) (p.1 1)) ⟨x, hx⟩ =
        (ofSeq fun n => f (r n) (s n) : αS) := by
    rintro x hx rfl
    exact (starMapOnN_ofSeq_eq_ofSeq hx).2 (Eventually.of_forall fun n => ⟨mem_univ _, rfl⟩)
  exact key _ h (vec_two_ofSeq r s)

/-- **Section 3.13.** The extension of a partial function of one argument, taken as a function
of one-tuples, is the extension {name}`Goldblatt.starMapOn` of Section 3.13. -/
theorem starMapOnN_unaryRel (A : Set α) (f : A → α) (a : αS)
    (h : (fun _ : Fin 1 => a) ∈ starRel (unaryRel A)) (h' : a ∈ (⋆A : Set αS)) :
    starMapOnN (unaryRel A) (fun p => f ⟨p.1 0, p.2⟩) ⟨fun _ => a, h⟩ =
      starMapOn A f ⟨a, h'⟩ := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) a
  obtain ⟨s, hs⟩ := ofSeq_surjective (α := α) (αS := αS) (starMapOn A f ⟨ofSeq r, h'⟩)
  rw [← hs]
  exact (starMapOnN_ofSeq_eq_ofSeq (r := fun _ => r) h).2
    ((starMapOn_ofSeq_eq_ofSeq h').1 hs.symm)

namespace Term

variable {v : Valuation αS} {t u : Term α} {c : αS}

/-- **Section 4.4.** The transform of $`f(\tau)` names $`{}^*f` of what the transform of $`\tau`
names. -/
@[simp] theorem names_star_app₁ {f : α → α} :
    ((app₁ f t).star : Term αS).Names v c ↔ ∃ a, (t.star : Term αS).Names v a ∧ ⋆f a = c := by
  simp only [app₁, star, star_vec_one, names_func_one]
  refine exists_congr fun a => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨h, rfl⟩
    exact (starMapOnN_univ_one f a h).symm
  · rintro rfl
    have h : (fun _ : Fin 1 => a) ∈ starRel (univ : Set (Fin 1 → α)) := by
      rw [starRel_univ]; exact mem_univ _
    exact ⟨h, starMapOnN_univ_one f a h⟩

/-- **Section 4.4.** The transform of $`f(\tau_1, \tau_2)` names $`{}^*f` of what the transforms
of $`\tau_1` and $`\tau_2` name. -/
@[simp] theorem names_star_app₂ {f : α → α → α} :
    ((app₂ f t u).star : Term αS).Names v c ↔
      ∃ a b, (t.star : Term αS).Names v a ∧ (u.star : Term αS).Names v b ∧ ⋆f a b = c := by
  simp only [app₂, star, star_vec_two, names_func_two]
  refine exists_congr fun a => exists_congr fun b => and_congr_right fun _ =>
    and_congr_right fun _ => ?_
  constructor
  · rintro ⟨h, rfl⟩
    exact (starMapOnN_univ_two f a b h).symm
  · rintro rfl
    have h : ![a, b] ∈ starRel (univ : Set (Fin 2 → α)) := by
      rw [starRel_univ]; exact mem_univ _
    exact ⟨h, starMapOnN_univ_two f a b h⟩

/-- **Section 4.4.** The transform of $`f(\tau)`, for a partial function $`f` with domain $`A`,
names $`{}^*f(a)` when the transform of $`\tau` names an element $`a` of $`{}^*A`. -/
@[simp] theorem names_star_papp₁ {A : Set α} {f : A → α} :
    ((papp₁ A f t).star : Term αS).Names v c ↔
      ∃ a, (t.star : Term αS).Names v a ∧ ∃ h : a ∈ (⋆A : Set αS), starMapOn A f ⟨a, h⟩ = c := by
  simp only [papp₁, star, star_vec_one, names_func_one]
  refine exists_congr fun a => and_congr_right fun _ => ?_
  have hiff : (fun _ : Fin 1 => a) ∈ starRel (unaryRel A) ↔ a ∈ (⋆A : Set αS) := by
    rw [starRel_unaryRel]; rfl
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨hiff.1 h, (starMapOnN_unaryRel A f a h (hiff.1 h)).symm⟩
  · rintro ⟨h, rfl⟩
    exact ⟨hiff.2 h, starMapOnN_unaryRel A f a (hiff.2 h) h⟩

/-- **Section 4.4.** The transform of $`f(\tau)` is closed when the transform of $`\tau` is. -/
@[simp] theorem closed_star_app₁ {f : α → α} :
    ((app₁ f t).star : Term αS).Closed v ↔ (t.star : Term αS).Closed v := by
  simp only [app₁, star, star_vec_one, closed_func_one]

/-- **Section 4.4.** The transform of $`f(\tau_1, \tau_2)` is closed when the transforms of both
arguments are. -/
@[simp] theorem closed_star_app₂ {f : α → α → α} :
    ((app₂ f t u).star : Term αS).Closed v ↔
      (t.star : Term αS).Closed v ∧ (u.star : Term αS).Closed v := by
  simp only [app₂, star, star_vec_two, closed_func_two]

/-- **Section 4.4.** For a partial function $`f`, the transform of $`f(\tau)` is closed when the
transform of $`\tau` is. -/
@[simp] theorem closed_star_papp₁ {A : Set α} {f : A → α} :
    ((papp₁ A f t).star : Term αS).Closed v ↔ (t.star : Term αS).Closed v := by
  simp only [papp₁, star, star_vec_one, closed_func_one]

/-- **Section 4.4.** The transform of $`f(\tau)`, with $`f` total, is defined when the transform of
$`\tau` is. -/
@[simp] theorem defined_star_app₁ {f : α → α} :
    ((app₁ f t).star : Term αS).Defined v ↔ (t.star : Term αS).Defined v := by
  simp only [app₁, star, star_vec_one, defined_func_one, starRel_univ, mem_univ, and_true]
  exact and_iff_left_of_imp fun hd hc => hd.denotes hc

/-- **Section 4.4.** The transform of $`f(\tau_1, \tau_2)`, with $`f` total, is defined when the
transforms of both arguments are. -/
@[simp] theorem defined_star_app₂ {f : α → α → α} :
    ((app₂ f t u).star : Term αS).Defined v ↔
      (t.star : Term αS).Defined v ∧ (u.star : Term αS).Defined v := by
  simp only [app₂, star, star_vec_two, defined_func_two, starRel_univ, mem_univ, and_true]
  rw [← and_assoc]
  refine and_iff_left_of_imp fun hd hc hc' => ?_
  obtain ⟨a, ha⟩ := hd.1.denotes hc
  obtain ⟨b, hb⟩ := hd.2.denotes hc'
  exact ⟨a, b, ha, hb⟩

/-- **Section 4.4.** For a partial function $`f` with domain $`A`, the transform of $`f(\tau)` is
defined when the transform of $`\tau` is and, if that is closed, the element it names lies in
$`{}^*A`. -/
@[simp] theorem defined_star_papp₁ {A : Set α} {f : A → α} :
    ((papp₁ A f t).star : Term αS).Defined v ↔ (t.star : Term αS).Defined v ∧
      ((t.star : Term αS).Closed v → ∃ a, (t.star : Term αS).Names v a ∧ a ∈ (⋆A : Set αS)) := by
  simp only [papp₁, star, star_vec_one, defined_func_one, starRel_unaryRel]
  rfl

end Term

namespace Formula

variable {v : Valuation αS} {t u : Term α}

/-- **Section 4.4.** The transform of $`\tau \in A` is $`{}^*\tau \in {}^*A`. -/
@[simp] theorem holds_star_mem {A : Set α} :
    ((mem t A).star : Formula αS).Holds v ↔
      ∃ a, (t.star : Term αS).Names v a ∧ a ∈ (⋆A : Set αS) := by
  simp only [mem, star, Term.star_vec_one, holds_rel_one, starRel_unaryRel]
  rfl

/-- **Section 4.4.** The transform of $`P(\tau_1, \tau_2)` is $`{}^*P({}^*\tau_1, {}^*\tau_2)`. -/
@[simp] theorem holds_star_rel₂ {P : α → α → Prop} :
    ((rel₂ P t u).star : Formula αS).Holds v ↔
      ∃ a b, (t.star : Term αS).Names v a ∧ (u.star : Term αS).Names v b ∧ ⋆P a b := by
  simp only [rel₂, star, Term.star_vec_two, holds_rel_two, starRel_binary]

/-- **Section 4.4.** The transform of an equation is an equation: the star on the identity
relation may be dropped. -/
@[simp] theorem holds_star_eq :
    ((eq t u).star : Formula αS).Holds v ↔
      ∃ a b, (t.star : Term αS).Names v a ∧ (u.star : Term αS).Names v b ∧ a = b := by
  simp only [eq, holds_star_rel₂, starRel₂_eq]

/-- **Section 4.4.** The transform of an inequality between real terms is the same inequality
between hyperreals: the star on the order relation may be dropped. -/
@[simp] theorem holds_star_lt {t u : Term ℝ} {v : Valuation ℝ*} :
    (lt t u).star.Holds v ↔ ∃ a b, t.star.Names v a ∧ u.star.Names v b ∧ a < b := by
  simp only [lt, holds_star_rel₂, starRel₂_lt]

/-- **Section 4.4.** The transform of a weak inequality between real terms is the same
inequality between hyperreals. -/
@[simp] theorem holds_star_le {t u : Term ℝ} {v : Valuation ℝ*} :
    (le t u).star.Holds v ↔ ∃ a b, t.star.Names v a ∧ u.star.Names v b ∧ a ≤ b := by
  simp only [le, holds_star_rel₂, starRel₂_le]

/-- **Section 4.4.** The transform of $`\tau \in A` is defined when the transform of $`\tau` is. -/
@[simp] theorem defined_star_mem {A : Set α} :
    ((mem t A).star : Formula αS).Defined v ↔ (t.star : Term αS).Defined v := by
  simp only [mem, star, Term.star_vec_one, defined_rel_one]

/-- **Section 4.4.** The transform of $`P(\tau_1, \tau_2)` is defined when the transforms of both
terms are. -/
@[simp] theorem defined_star_rel₂ {P : α → α → Prop} :
    ((rel₂ P t u).star : Formula αS).Defined v ↔
      (t.star : Term αS).Defined v ∧ (u.star : Term αS).Defined v := by
  simp only [rel₂, star, Term.star_vec_two, defined_rel_two]

/-- **Section 4.4.** The transform of $`\tau_1 = \tau_2` is defined when the transforms of both
terms are. -/
@[simp] theorem defined_star_eq :
    ((eq t u).star : Formula αS).Defined v ↔
      (t.star : Term αS).Defined v ∧ (u.star : Term αS).Defined v := defined_star_rel₂

/-- **Section 4.4.** The transform of $`\tau_1 < \tau_2` is defined when the transforms of both
terms are. -/
@[simp] theorem defined_star_lt {t u : Term ℝ} {v : Valuation ℝ*} :
    (lt t u).star.Defined v ↔ t.star.Defined v ∧ u.star.Defined v := defined_star_rel₂

/-- **Section 4.4.** The transform of $`\tau_1 \le \tau_2` is defined when the transforms of both
terms are. -/
@[simp] theorem defined_star_le {t u : Term ℝ} {v : Valuation ℝ*} :
    (le t u).star.Defined v ↔ t.star.Defined v ∧ u.star.Defined v := defined_star_rel₂

end Formula

end StarNotation

end Goldblatt
