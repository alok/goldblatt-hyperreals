import Goldblatt.Ch13_Universes.Sets

/-!
# 13 (part 2). The Language of a Universe: Section 13.7

This is the second of five parts of Chapter 13 (the overview is on the chapter page
{lit}`Goldblatt.Ch13_Universes`). It defines the formal language attached to a universe as a
deep embedding: an inductive type of terms, an inductive type of formulas whose quantifiers
are all bounded, the satisfaction relation, and the syntactic notion of a sentence over a
universe. The transfer principle of the next part is a statement about these objects.
-/

noncomputable section

namespace Goldblatt

open ZFSet

universe u

/-!
## 13.7 The Language of a Universe

Terms are built from variables and from constants, one for each member of the universe, by
forming tuples and function values. Atomic formulas are equations and membership statements
between terms. Formulas are built from atomic ones by the propositional connectives and by
the bounded quantifiers "for all $`x \in \tau`" and "for some $`x \in \tau`", where $`\tau` is
a term in which $`x` does not occur. There is no unbounded quantifier.

Conventions of the formalization.

* Variables are natural numbers, and a formula is evaluated under an assignment of sets to
  all variables. A quantifier changes the assignment at its own variable.
* The type of terms does not depend on the universe: any set may appear as a constant. That
  the constants of a formula come from $`\mathbb U` is part of the predicate
  {lit}`Formula.IsSentence`, together with the book's requirement that a quantified variable
  does not occur in its bound and the requirement that no variable is free.
* Quantified variables range over the members of the bound _that belong to the universe_.
  For a bound that is a set of the universe this is no restriction, by transitivity; for a
  bound that is an individual it means that the quantifier ranges over nothing, as in the
  book, where individuals have no members.
* A closed term can fail to name anything (a function applied outside its domain). The book
  handles this as in its Chapter 4, by speaking only of defined sentences. Here every formula
  has a truth value: an atomic formula with an undefined term is false, and a quantifier
  whose bound is undefined ranges over nothing. The two treatments agree on every formula
  whose terms are always defined, and being defined is itself expressible by a bounded
  formula, so nothing is lost.
-/

/-- **Section 13.7, terms.** The terms of the language of a universe: variables, constants,
tuples $`(\tau_1, \dots, \tau_m)` with $`m \ge 2` (the constructor takes $`m - 2` and a family
of $`m` terms), and function values $`\tau(\sigma)`. -/
inductive Term : Type (u + 1)
  /-- The variable with a given index. -/
  | var : ℕ → Term
  /-- The constant naming a given set. -/
  | const : ZFSet.{u} → Term
  /-- The tuple of a family of at least two terms. -/
  | tuple : (m : ℕ) → (Fin (m + 2) → Term) → Term
  /-- The value of a function term at an argument term. -/
  | app : Term → Term → Term

namespace Term

/-- **Section 13.7, what a term names.** The value of a term under an assignment of sets to
the variables. A tuple of terms names the tuple of their values, and $`\tau(\sigma)` names
the value {lit}`app` of the function named by $`\tau` at the entity named by $`\sigma`. The
value is meaningful only when the term is defined ({lit}`Term.Defined`). -/
def val (v : ℕ → ZFSet.{u}) : Term.{u} → ZFSet.{u}
  | var n => v n
  | const a => a
  | tuple m ts => Goldblatt.tuple (m + 2) fun i => (ts i).val v
  | app f x => Goldblatt.app (f.val v) (x.val v)

/-- **Section 13.7, defined terms.** Variables and constants are always defined; a tuple is
defined when all its components are; $`\tau(\sigma)` is defined when $`\tau` and $`\sigma` are
defined, $`\tau` names a function of the universe (a single-valued set of pairs of members of
$`\mathbb U`) and $`\sigma` names a member of its domain. -/
def Defined (U : ZFSet.{u}) (v : ℕ → ZFSet.{u}) : Term.{u} → Prop
  | var _ => True
  | const _ => True
  | tuple _ ts => ∀ i, (ts i).Defined U v
  | app f x => f.Defined U v ∧ x.Defined U v ∧ IsFunction (f.val v) ∧ RelIn U (f.val v) ∧
      x.val v ∈ dom (f.val v)

/-- **Section 13.8, transform of a term.** Replace every constant $`a` of a term by
$`s(a)`. -/
def star (s : ZFSet.{u} → ZFSet.{u}) : Term.{u} → Term.{u}
  | var n => var n
  | const a => const (s a)
  | tuple m ts => tuple m fun i => (ts i).star s
  | app f x => app (f.star s) (x.star s)

/-- A term is admissible for a universe $`\mathbb U` and a set $`b` of variables when all its
constants belong to $`\mathbb U` and all its variables belong to $`b`. -/
def Admissible (U : ZFSet.{u}) (b : Set ℕ) : Term.{u} → Prop
  | var n => n ∈ b
  | const a => a ∈ U
  | tuple _ ts => ∀ i, (ts i).Admissible U b
  | app f x => f.Admissible U b ∧ x.Admissible U b

attribute [simp] val Defined star Admissible

/-- The pair term $`(\sigma, \tau)`, the tuple of two terms. -/
def opair (s t : Term.{u}) : Term.{u} := tuple 0 ![s, t]

@[simp]
theorem val_opair (v : ℕ → ZFSet.{u}) (s t : Term.{u}) :
    (opair s t).val v = pair (s.val v) (t.val v) := by
  simp [opair]

@[simp]
theorem defined_opair (U : ZFSet.{u}) (v : ℕ → ZFSet.{u}) (s t : Term.{u}) :
    (opair s t).Defined U v ↔ s.Defined U v ∧ t.Defined U v := by
  simp [opair, Fin.forall_fin_two]

@[simp]
theorem star_opair (σ : ZFSet.{u} → ZFSet.{u}) (s t : Term.{u}) :
    (opair s t).star σ = opair (s.star σ) (t.star σ) := by
  simp only [opair, star]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp]
theorem admissible_opair (U : ZFSet.{u}) (b : Set ℕ) (s t : Term.{u}) :
    (opair s t).Admissible U b ↔ s.Admissible U b ∧ t.Admissible U b := by
  simp [opair, Fin.forall_fin_two]

variable {U U' : ZFSet.{u}} {b b' : Set ℕ} {v w : ℕ → ZFSet.{u}}

theorem Admissible.mono {t : Term.{u}} (h : t.Admissible U b) (hb : b ⊆ b') :
    t.Admissible U b' := by
  induction t with
  | var n => exact hb h
  | const a => exact h
  | tuple m ts ih => exact fun i => ih i (h i)
  | app f x ihf ihx => exact ⟨ihf h.1, ihx h.2⟩

/-- The value of a term depends only on the values of its variables. -/
theorem val_congr {t : Term.{u}} (h : t.Admissible U b) (hvw : ∀ x ∈ b, v x = w x) :
    t.val v = t.val w := by
  induction t with
  | var n => exact hvw n h
  | const a => rfl
  | tuple m ts ih =>
    simp only [val]
    congr 1
    funext i
    exact ih i (h i)
  | app f x ihf ihx => simp only [val, ihf h.1, ihx h.2]

/-- Whether a term is defined depends only on the values of its variables. -/
theorem defined_congr {t : Term.{u}} (h : t.Admissible U b) (hvw : ∀ x ∈ b, v x = w x) :
    t.Defined U' v ↔ t.Defined U' w := by
  induction t with
  | var n => rfl
  | const a => rfl
  | tuple m ts ih =>
    simp only [Defined]
    exact forall_congr' fun i => ih i (h i)
  | app f x ihf ihx =>
    simp only [Defined, ihf h.1, ihx h.2, val_congr h.1 hvw, val_congr h.2 hvw]

/-- The transform of an admissible term is admissible for the target universe. -/
theorem Admissible.star {t : Term.{u}} {s : ZFSet.{u} → ZFSet.{u}} (h : t.Admissible U b)
    (hs : ∀ a ∈ U, s a ∈ U') : (t.star s).Admissible U' b := by
  induction t with
  | var n => exact h
  | const a => exact hs a h
  | tuple m ts ih => exact fun i => ih i (h i)
  | app f x ihf ihx => exact ⟨ihf h.1, ihx h.2⟩

/-- In a universe, a defined term whose constants and variable values are in the universe
names a member of the universe. -/
theorem val_mem (hU : IsUniverse U) {t : Term.{u}} (h : t.Admissible U b)
    (hv : ∀ x ∈ b, v x ∈ U) (hd : t.Defined U v) : t.val v ∈ U := by
  induction t with
  | var n => exact hv n h
  | const a => exact h
  | tuple m ts ih => exact (hU.isSetOf_tuple _ _ fun i => ih i (h i) (hd i)).1
  | app f x ihf ihx =>
    obtain ⟨-, -, hfun, hrel, hdom⟩ := hd
    obtain ⟨a, -, c, hc, hp⟩ := hrel _ (hfun.pair_app_mem hdom)
    simp only [val]
    rw [(pair_inj.1 hp).2]
    exact hc

end Term

/-- **Section 13.7, formulas.** The formulas of the language of a universe: equations
$`\tau = \sigma` and membership statements $`\tau \in \sigma` between terms, closed under
conjunction, disjunction, negation, implication, bi-implication, and the bounded quantifiers
$`(\forall x \in \tau)\varphi` and $`(\exists x \in \tau)\varphi`. -/
inductive Formula : Type (u + 1)
  /-- The atomic formula $`\tau = \sigma`. -/
  | equal : Term.{u} → Term.{u} → Formula
  /-- The atomic formula $`\tau \in \sigma`. -/
  | elem : Term.{u} → Term.{u} → Formula
  /-- Conjunction. -/
  | conj : Formula → Formula → Formula
  /-- Disjunction. -/
  | disj : Formula → Formula → Formula
  /-- Negation. -/
  | neg : Formula → Formula
  /-- Implication. -/
  | imp : Formula → Formula → Formula
  /-- Bi-implication. -/
  | biimp : Formula → Formula → Formula
  /-- The bounded universal quantifier $`(\forall x \in \tau)\varphi`. -/
  | all : ℕ → Term.{u} → Formula → Formula
  /-- The bounded existential quantifier $`(\exists x \in \tau)\varphi`. -/
  | ex : ℕ → Term.{u} → Formula → Formula

/-- **Section 13.7, truth.** Satisfaction of a formula in the universe $`\mathbb U` under an
assignment of sets to the variables. Atomic formulas are true when their terms are defined
and the named entities are equal, respectively related by membership; connectives have their
usual meaning; $`(\forall x \in \tau)\varphi` says that $`\varphi` holds for every member of
$`\mathbb U` that belongs to the set named by $`\tau`, and $`(\exists x \in \tau)\varphi` that
it holds for some such member. -/
def Sat (U : ZFSet.{u}) : (ℕ → ZFSet.{u}) → Formula.{u} → Prop
  | v, .equal s t => s.Defined U v ∧ t.Defined U v ∧ s.val v = t.val v
  | v, .elem s t => s.Defined U v ∧ t.Defined U v ∧ s.val v ∈ t.val v
  | v, .conj φ ψ => Sat U v φ ∧ Sat U v ψ
  | v, .disj φ ψ => Sat U v φ ∨ Sat U v ψ
  | v, .neg φ => ¬ Sat U v φ
  | v, .imp φ ψ => Sat U v φ → Sat U v ψ
  | v, .biimp φ ψ => (Sat U v φ ↔ Sat U v ψ)
  | v, .all x τ φ => ∀ a ∈ U, τ.Defined U v → a ∈ τ.val v → Sat U (Function.update v x a) φ
  | v, .ex x τ φ => ∃ a ∈ U, τ.Defined U v ∧ a ∈ τ.val v ∧ Sat U (Function.update v x a) φ

namespace Formula

/-- **Section 13.8, transform of a formula.** Replace every constant $`a` occurring in a
formula, in an atomic subformula or in the bound of a quantifier, by $`s(a)`. -/
def star (s : ZFSet.{u} → ZFSet.{u}) : Formula.{u} → Formula.{u}
  | equal t₁ t₂ => equal (t₁.star s) (t₂.star s)
  | elem t₁ t₂ => elem (t₁.star s) (t₂.star s)
  | conj φ ψ => conj (φ.star s) (ψ.star s)
  | disj φ ψ => disj (φ.star s) (ψ.star s)
  | neg φ => neg (φ.star s)
  | imp φ ψ => imp (φ.star s) (ψ.star s)
  | biimp φ ψ => biimp (φ.star s) (ψ.star s)
  | all x τ φ => all x (τ.star s) (φ.star s)
  | ex x τ φ => ex x (τ.star s) (φ.star s)

/-- A formula is admissible for a universe $`\mathbb U` and a set $`b` of variables when it is
a formula of the language of $`\mathbb U` (all constants belong to $`\mathbb U`, and the
variable of each quantifier does not occur in the bound of that quantifier) whose free
variables all belong to $`b`. -/
def Admissible (U : ZFSet.{u}) : Set ℕ → Formula.{u} → Prop
  | b, equal s t => s.Admissible U b ∧ t.Admissible U b
  | b, elem s t => s.Admissible U b ∧ t.Admissible U b
  | b, conj φ ψ => φ.Admissible U b ∧ ψ.Admissible U b
  | b, disj φ ψ => φ.Admissible U b ∧ ψ.Admissible U b
  | b, neg φ => φ.Admissible U b
  | b, imp φ ψ => φ.Admissible U b ∧ ψ.Admissible U b
  | b, biimp φ ψ => φ.Admissible U b ∧ ψ.Admissible U b
  | b, all x τ φ => τ.Admissible U (b \ {x}) ∧ φ.Admissible U (insert x b)
  | b, ex x τ φ => τ.Admissible U (b \ {x}) ∧ φ.Admissible U (insert x b)

/-- **Section 13.7, sentences.** A sentence of the language of $`\mathbb U`: a formula with
constants from $`\mathbb U`, in which no quantified variable occurs in its own bound, and in
which every occurrence of a variable is within the scope of a quantifier for it. -/
def IsSentence (U : ZFSet.{u}) (φ : Formula.{u}) : Prop := φ.Admissible U ∅

/-- **Section 13.7, truth of a sentence.** A sentence is true in $`\mathbb U` when it is
satisfied under the assignment sending every variable to the empty set; by
{lit}`Formula.holds_iff_sat` the assignment does not matter. -/
def Holds (U : ZFSet.{u}) (φ : Formula.{u}) : Prop := Sat U (fun _ => ∅) φ

attribute [simp] star Admissible

variable {U U' : ZFSet.{u}} {b b' : Set ℕ} {v w : ℕ → ZFSet.{u}}

theorem Admissible.mono {φ : Formula.{u}} (h : φ.Admissible U b) (hb : b ⊆ b') :
    φ.Admissible U b' := by
  induction φ generalizing b b' with
  | equal s t => exact ⟨h.1.mono hb, h.2.mono hb⟩
  | elem s t => exact ⟨h.1.mono hb, h.2.mono hb⟩
  | conj φ ψ ihφ ihψ => exact ⟨ihφ h.1 hb, ihψ h.2 hb⟩
  | disj φ ψ ihφ ihψ => exact ⟨ihφ h.1 hb, ihψ h.2 hb⟩
  | neg φ ih => exact ih h hb
  | imp φ ψ ihφ ihψ => exact ⟨ihφ h.1 hb, ihψ h.2 hb⟩
  | biimp φ ψ ihφ ihψ => exact ⟨ihφ h.1 hb, ihψ h.2 hb⟩
  | all x τ φ ih =>
    exact ⟨h.1.mono (Set.sdiff_subset_sdiff_left hb), ih h.2 (Set.insert_subset_insert hb)⟩
  | ex x τ φ ih =>
    exact ⟨h.1.mono (Set.sdiff_subset_sdiff_left hb), ih h.2 (Set.insert_subset_insert hb)⟩

/-- **Section 13.7.** The truth of a formula depends only on the values of its free
variables. -/
theorem sat_congr {φ : Formula.{u}} (h : φ.Admissible U b) (hvw : ∀ x ∈ b, v x = w x) :
    Sat U' v φ ↔ Sat U' w φ := by
  induction φ generalizing b v w with
  | equal s t =>
    simp only [Sat, Term.defined_congr h.1 hvw, Term.defined_congr h.2 hvw,
      Term.val_congr h.1 hvw, Term.val_congr h.2 hvw]
  | elem s t =>
    simp only [Sat, Term.defined_congr h.1 hvw, Term.defined_congr h.2 hvw,
      Term.val_congr h.1 hvw, Term.val_congr h.2 hvw]
  | conj φ ψ ihφ ihψ => simp only [Sat, ihφ h.1 hvw, ihψ h.2 hvw]
  | disj φ ψ ihφ ihψ => simp only [Sat, ihφ h.1 hvw, ihψ h.2 hvw]
  | neg φ ih => simp only [Sat, ih h hvw]
  | imp φ ψ ihφ ihψ => simp only [Sat, ihφ h.1 hvw, ihψ h.2 hvw]
  | biimp φ ψ ihφ ihψ => simp only [Sat, ihφ h.1 hvw, ihψ h.2 hvw]
  | all x τ φ ih =>
    have hvw' : ∀ y ∈ b \ {x}, v y = w y := fun y hy => hvw y hy.1
    have key : ∀ a, Sat U' (Function.update v x a) φ ↔ Sat U' (Function.update w x a) φ :=
      fun a => ih h.2 fun y hy => by
        by_cases hyx : y = x
        · subst hyx; simp
        · simp [Function.update_of_ne hyx, hvw y (hy.resolve_left hyx)]
    simp only [Sat, Term.defined_congr h.1 hvw', Term.val_congr h.1 hvw', key]
  | ex x τ φ ih =>
    have hvw' : ∀ y ∈ b \ {x}, v y = w y := fun y hy => hvw y hy.1
    have key : ∀ a, Sat U' (Function.update v x a) φ ↔ Sat U' (Function.update w x a) φ :=
      fun a => ih h.2 fun y hy => by
        by_cases hyx : y = x
        · subst hyx; simp
        · simp [Function.update_of_ne hyx, hvw y (hy.resolve_left hyx)]
    simp only [Sat, Term.defined_congr h.1 hvw', Term.val_congr h.1 hvw', key]

/-- **Section 13.7.** A sentence has a truth value that does not depend on the assignment. -/
theorem holds_iff_sat {φ : Formula.{u}} (h : φ.IsSentence U) (v : ℕ → ZFSet.{u}) :
    φ.Holds U' ↔ Sat U' v φ :=
  sat_congr h fun _ hx => absurd hx (Set.notMem_empty _)

/-- **Section 13.8.** The transform of a formula of the language of $`\mathbb U` under a map
into $`\mathbb U'` is a formula of the language of $`\mathbb U'` with the same free
variables. -/
theorem Admissible.star {φ : Formula.{u}} {s : ZFSet.{u} → ZFSet.{u}} (h : φ.Admissible U b)
    (hs : ∀ a ∈ U, s a ∈ U') : (φ.star s).Admissible U' b := by
  induction φ generalizing b with
  | equal t₁ t₂ => exact ⟨h.1.star hs, h.2.star hs⟩
  | elem t₁ t₂ => exact ⟨h.1.star hs, h.2.star hs⟩
  | conj φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | disj φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | neg φ ih => exact ih h
  | imp φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | biimp φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | all x τ φ ih => exact ⟨h.1.star hs, ih h.2⟩
  | ex x τ φ ih => exact ⟨h.1.star hs, ih h.2⟩

/-- **Section 13.8.** If $`\varphi` is a sentence, then so is its transform. -/
theorem IsSentence.star {φ : Formula.{u}} {s : ZFSet.{u} → ZFSet.{u}} (h : φ.IsSentence U)
    (hs : ∀ a ∈ U, s a ∈ U') : (φ.star s).IsSentence U' :=
  Admissible.star h hs

/-- A formula without constants is its own transform. -/
theorem star_id (φ : Formula.{u}) : φ.star id = φ := by
  have ht : ∀ t : Term.{u}, t.star id = t := fun t => by
    induction t with
    | var n => rfl
    | const a => rfl
    | tuple m ts ih => simp only [Term.star, ih]
    | app f x ihf ihx => simp only [Term.star, ihf, ihx]
  induction φ with
  | equal s t => simp only [star, ht]
  | elem s t => simp only [star, ht]
  | conj φ ψ ihφ ihψ => simp only [star, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [star, ihφ, ihψ]
  | neg φ ih => simp only [star, ih]
  | imp φ ψ ihφ ihψ => simp only [star, ihφ, ihψ]
  | biimp φ ψ ihφ ihψ => simp only [star, ihφ, ihψ]
  | all x τ φ ih => simp only [star, ht, ih]
  | ex x τ φ ih => simp only [star, ht, ih]

/-- A block of bounded universal quantifiers $`(\forall x_1 \in T_1) \cdots
(\forall x_k \in T_k)` with constant bounds, given as a list of pairs $`(x_i, T_i)`, in front
of a formula. -/
def alls : List (ℕ × ZFSet.{u}) → Formula.{u} → Formula.{u}
  | [], φ => φ
  | (x, T) :: l, φ => all x (.const T) (alls l φ)

/-- A block of bounded existential quantifiers with constant bounds in front of a formula. -/
def exs : List (ℕ × ZFSet.{u}) → Formula.{u} → Formula.{u}
  | [], φ => φ
  | (x, T) :: l, φ => ex x (.const T) (exs l φ)

/-- The assignments obtained from $`v` by giving the variables of a quantifier block, in
order, values in $`\mathbb U` that belong to the corresponding bounds. -/
def reach (U : ZFSet.{u}) : List (ℕ × ZFSet.{u}) → (ℕ → ZFSet.{u}) → Set (ℕ → ZFSet.{u})
  | [], v => {v}
  | (x, T) :: l, v => {w | ∃ a ∈ U, a ∈ T ∧ w ∈ reach U l (Function.update v x a)}

theorem sat_alls {l : List (ℕ × ZFSet.{u})} {φ : Formula.{u}} :
    Sat U v (alls l φ) ↔ ∀ w ∈ reach U l v, Sat U w φ := by
  induction l generalizing v with
  | nil => simp [alls, reach]
  | cons p l ih =>
    obtain ⟨x, T⟩ := p
    simp only [alls, Sat, Term.Defined, Term.val, forall_true_left, ih, reach, Set.mem_ofPred_eq]
    exact ⟨fun h w ⟨a, ha, haT, hw⟩ => h a ha haT w hw, fun h a ha haT w hw => h w ⟨a, ha, haT, hw⟩⟩

theorem sat_exs {l : List (ℕ × ZFSet.{u})} {φ : Formula.{u}} :
    Sat U v (exs l φ) ↔ ∃ w ∈ reach U l v, Sat U w φ := by
  induction l generalizing v with
  | nil => simp [exs, reach]
  | cons p l ih =>
    obtain ⟨x, T⟩ := p
    simp only [exs, Sat, Term.Defined, Term.val, true_and, ih, reach, Set.mem_ofPred_eq]
    exact ⟨fun ⟨a, ha, haT, w, hw, h⟩ => ⟨w, ⟨a, ha, haT, hw⟩, h⟩,
      fun ⟨w, ⟨a, ha, haT, hw⟩, h⟩ => ⟨a, ha, haT, w, hw, h⟩⟩

/-- Every assignment that gives each variable of a quantifier block a value in $`\mathbb U`
belonging to its bound, and agrees with $`v` elsewhere, is reached. -/
theorem mem_reach_of {l : List (ℕ × ZFSet.{u})} (hw : ∀ p ∈ l, w p.1 ∈ U ∧ w p.1 ∈ p.2)
    (hv : ∀ y, y ∉ l.map Prod.fst → w y = v y) : w ∈ reach U l v := by
  induction l generalizing v with
  | nil =>
    simp only [reach, Set.mem_singleton_iff]
    exact funext fun y => hv y (by simp)
  | cons p l ih =>
    obtain ⟨x, T⟩ := p
    refine ⟨w x, (hw _ (List.mem_cons_self ..)).1, (hw _ (List.mem_cons_self ..)).2, ?_⟩
    refine ih (fun p hp => hw p (List.mem_cons_of_mem _ hp)) fun y hy => ?_
    by_cases hyx : y = x
    · subst hyx; simp
    · rw [Function.update_of_ne hyx]
      exact hv y (by simpa [hyx] using hy)

/-- For a block of distinct variables, every reached assignment gives each variable of the
block a value in $`\mathbb U` belonging to its bound, and agrees with $`v` elsewhere. -/
theorem of_mem_reach {l : List (ℕ × ZFSet.{u})} (hl : (l.map Prod.fst).Nodup)
    (hw : w ∈ reach U l v) :
    (∀ p ∈ l, w p.1 ∈ U ∧ w p.1 ∈ p.2) ∧ ∀ y, y ∉ l.map Prod.fst → w y = v y := by
  induction l generalizing v with
  | nil =>
    simp only [reach, Set.mem_singleton_iff] at hw
    subst hw
    simp
  | cons p l ih =>
    obtain ⟨x, T⟩ := p
    obtain ⟨a, ha, haT, hw⟩ := hw
    rw [List.map_cons, List.nodup_cons] at hl
    obtain ⟨h1, h2⟩ := ih hl.2 hw
    have hwx : w x = a := by rw [h2 x hl.1]; simp
    refine ⟨fun p hp => ?_, fun y hy => ?_⟩
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hwx ▸ ha, hwx ▸ haT⟩
      · exact h1 p hp
    · simp only [List.map_cons, List.mem_cons, not_or] at hy
      rw [h2 y hy.2, Function.update_of_ne hy.1]

/-- The assignments reached through a quantifier block on the variables $`0, \dots, n - 1`
with bounds $`A_0, \dots, A_{n-1}`: those that give each of these variables a value in
$`\mathbb U` belonging to its bound and agree with $`v` on all other variables. -/
theorem mem_reach_ofFn_iff (n : ℕ) (A : Fin n → ZFSet.{u}) :
    w ∈ reach U (List.ofFn fun i : Fin n => ((i : ℕ), A i)) v ↔
      (∀ i : Fin n, w i ∈ U ∧ w i ∈ A i) ∧ ∀ y, n ≤ y → w y = v y := by
  set l := List.ofFn fun i : Fin n => ((i : ℕ), A i) with hl
  have hfst : l.map Prod.fst = List.ofFn fun i : Fin n => (i : ℕ) := by
    rw [hl, List.map_ofFn]
    rfl
  have hnodup : (l.map Prod.fst).Nodup := by
    rw [hfst]
    exact List.nodup_ofFn.2 fun i j h => Fin.ext h
  have hnot : ∀ y, y ∉ l.map Prod.fst ↔ n ≤ y := by
    intro y
    rw [hfst, List.mem_ofFn]
    constructor
    · intro h
      by_contra hlt
      exact h ⟨⟨y, by omega⟩, rfl⟩
    · rintro h ⟨i, rfl⟩
      exact absurd i.2 (by omega)
  constructor
  · intro hw
    obtain ⟨h1, h2⟩ := of_mem_reach hnodup hw
    exact ⟨fun i => h1 _ (by rw [hl, List.mem_ofFn]; exact ⟨i, rfl⟩),
      fun y hy => h2 y ((hnot y).2 hy)⟩
  · rintro ⟨h1, h2⟩
    refine mem_reach_of (fun p hp => ?_) fun y hy => h2 y ((hnot y).1 hy)
    rw [hl, List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    exact h1 i

theorem admissible_alls {l : List (ℕ × ZFSet.{u})} {φ : Formula.{u}} (hl : ∀ p ∈ l, p.2 ∈ U)
    (hφ : φ.Admissible U (b ∪ {y | y ∈ l.map Prod.fst})) : (alls l φ).Admissible U b := by
  induction l generalizing b with
  | nil => simpa [alls] using hφ
  | cons p l ih =>
    obtain ⟨x, T⟩ := p
    refine ⟨hl _ (List.mem_cons_self ..), ih (fun p hp => hl p (List.mem_cons_of_mem _ hp)) ?_⟩
    refine hφ.mono fun y hy => ?_
    simp only [List.map_cons, List.mem_cons, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_insert_iff] at hy ⊢
    tauto

theorem admissible_exs {l : List (ℕ × ZFSet.{u})} {φ : Formula.{u}} (hl : ∀ p ∈ l, p.2 ∈ U)
    (hφ : φ.Admissible U (b ∪ {y | y ∈ l.map Prod.fst})) : (exs l φ).Admissible U b := by
  induction l generalizing b with
  | nil => simpa [exs] using hφ
  | cons p l ih =>
    obtain ⟨x, T⟩ := p
    refine ⟨hl _ (List.mem_cons_self ..), ih (fun p hp => hl p (List.mem_cons_of_mem _ hp)) ?_⟩
    refine hφ.mono fun y hy => ?_
    simp only [List.map_cons, List.mem_cons, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_insert_iff] at hy ⊢
    tauto

theorem star_alls (s : ZFSet.{u} → ZFSet.{u}) (l : List (ℕ × ZFSet.{u})) (φ : Formula.{u}) :
    (alls l φ).star s = alls (l.map fun p => (p.1, s p.2)) (φ.star s) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [alls, star, Term.star, ih, List.map_cons]

theorem star_exs (s : ZFSet.{u} → ZFSet.{u}) (l : List (ℕ × ZFSet.{u})) (φ : Formula.{u}) :
    (exs l φ).star s = exs (l.map fun p => (p.1, s p.2)) (φ.star s) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [exs, star, Term.star, ih, List.map_cons]

end Formula

/-!
### Replacing constants by variables

The proof of the internal set definition principle in Section 13.15 begins by replacing each
constant of a formula by a new variable. The operation and its properties are recorded here.
-/

namespace Term

/-- Replace each constant $`c` of a term by the variable with index $`e(c)`. -/
def abs (e : ZFSet.{u} → ℕ) : Term.{u} → Term.{u}
  | var n => var n
  | const c => var (e c)
  | tuple m ts => tuple m fun i => (ts i).abs e
  | app f x => app (f.abs e) (x.abs e)

/-- All variables of the term have index below $`N` and all its constants satisfy $`K`. -/
def Below (N : ℕ) (K : ZFSet.{u} → Prop) : Term.{u} → Prop
  | var n => n < N
  | const c => K c
  | tuple _ ts => ∀ i, (ts i).Below N K
  | app f x => f.Below N K ∧ x.Below N K

variable {N N' : ℕ} {K K' : ZFSet.{u} → Prop} {e : ZFSet.{u} → ℕ} {t : Term.{u}}
  {U U' : ZFSet.{u}} {b : Set ℕ} {w : ℕ → ZFSet.{u}}

theorem Below.mono (h : t.Below N K) (hN : N ≤ N') (hK : ∀ c, K c → K' c) : t.Below N' K' := by
  induction t with
  | var n => exact lt_of_lt_of_le h hN
  | const c => exact hK c h
  | tuple m ts ih => exact fun i => ih i (h i)
  | app f x ihf ihx => exact ⟨ihf h.1, ihx h.2⟩

theorem exists_below {P : ZFSet.{u} → Prop} (h : t.Below N P) :
    ∃ N', ∃ L : List ZFSet.{u}, (∀ c ∈ L, P c) ∧ t.Below N' (· ∈ L) := by
  induction t with
  | var n => exact ⟨n + 1, [], by simp, Nat.lt_succ_self n⟩
  | const c =>
    exact ⟨0, [c], fun d hd => by rw [List.mem_singleton.1 hd]; exact h,
      List.mem_singleton.2 rfl⟩
  | tuple m ts ih =>
    choose Nf Lf hP hB using fun i => ih i (h i)
    refine ⟨Finset.univ.sup Nf, (List.ofFn Lf).flatten, fun c hc => ?_, fun i =>
      (hB i).mono (Finset.le_sup (Finset.mem_univ i)) fun c hc =>
        List.mem_flatten.2 ⟨Lf i, by rw [List.mem_ofFn]; exact ⟨i, rfl⟩, hc⟩⟩
    obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 hc
    rw [List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    exact hP i c hcl
  | app f x ihf ihx =>
    obtain ⟨N1, L1, hP1, h1⟩ := ihf h.1
    obtain ⟨N2, L2, hP2, h2⟩ := ihx h.2
    refine ⟨max N1 N2, L1 ++ L2, fun c hc => ?_,
      h1.mono (le_max_left _ _) fun c hc => List.mem_append_left _ hc,
      h2.mono (le_max_right _ _) fun c hc => List.mem_append_right _ hc⟩
    rcases List.mem_append.1 hc with hc | hc
    · exact hP1 c hc
    · exact hP2 c hc

theorem val_abs (h : t.Below N K) (hw : ∀ c, K c → w (e c) = c) :
    (t.abs e).val w = t.val w := by
  induction t with
  | var n => rfl
  | const c => exact hw c h
  | tuple m ts ih =>
    simp only [abs, val]
    congr 1
    funext i
    exact ih i (h i)
  | app f x ihf ihx => simp only [abs, val, ihf h.1, ihx h.2]

theorem defined_abs (h : t.Below N K) (hw : ∀ c, K c → w (e c) = c) :
    (t.abs e).Defined U w ↔ t.Defined U w := by
  induction t with
  | var n => rfl
  | const c => simp [abs]
  | tuple m ts ih =>
    simp only [abs, Defined]
    exact forall_congr' fun i => ih i (h i)
  | app f x ihf ihx =>
    simp only [abs, Defined, ihf h.1, ihx h.2, val_abs h.1 hw, val_abs h.2 hw]

theorem star_abs (s : ZFSet.{u} → ZFSet.{u}) (t : Term.{u}) : (t.abs e).star s = t.abs e := by
  induction t with
  | var n => rfl
  | const c => rfl
  | tuple m ts ih => simp only [abs, star, ih]
  | app f x ihf ihx => simp only [abs, star, ihf, ihx]

theorem admissible_abs (h : t.Admissible U' b) (hB : t.Below N K) :
    (t.abs e).Admissible U (b ∪ {n | ∃ c, K c ∧ e c = n}) := by
  induction t with
  | var n => exact Or.inl h
  | const c => exact Or.inr ⟨c, hB, rfl⟩
  | tuple m ts ih => exact fun i => ih i (h i) (hB i)
  | app f x ihf ihx => exact ⟨ihf h.1 hB.1, ihx h.2 hB.2⟩

end Term

namespace Formula

/-- Replace each constant $`c` of a formula by the variable with index $`e(c)`. -/
def abs (e : ZFSet.{u} → ℕ) : Formula.{u} → Formula.{u}
  | equal s t => equal (s.abs e) (t.abs e)
  | elem s t => elem (s.abs e) (t.abs e)
  | conj φ ψ => conj (φ.abs e) (ψ.abs e)
  | disj φ ψ => disj (φ.abs e) (ψ.abs e)
  | neg φ => neg (φ.abs e)
  | imp φ ψ => imp (φ.abs e) (ψ.abs e)
  | biimp φ ψ => biimp (φ.abs e) (ψ.abs e)
  | all x τ φ => all x (τ.abs e) (φ.abs e)
  | ex x τ φ => ex x (τ.abs e) (φ.abs e)

/-- All variables of the formula, free or bound, have index below $`N`, and all its constants
satisfy $`K`. -/
def Below (N : ℕ) (K : ZFSet.{u} → Prop) : Formula.{u} → Prop
  | equal s t => s.Below N K ∧ t.Below N K
  | elem s t => s.Below N K ∧ t.Below N K
  | conj φ ψ => φ.Below N K ∧ ψ.Below N K
  | disj φ ψ => φ.Below N K ∧ ψ.Below N K
  | neg φ => φ.Below N K
  | imp φ ψ => φ.Below N K ∧ ψ.Below N K
  | biimp φ ψ => φ.Below N K ∧ ψ.Below N K
  | all x τ φ => x < N ∧ τ.Below N K ∧ φ.Below N K
  | ex x τ φ => x < N ∧ τ.Below N K ∧ φ.Below N K

/-- **Section 13.15.** Every constant of the formula satisfies $`P`; for instance, every
constant is internal. (A bound on the indices of the variables always exists.) -/
def ConstsSat (P : ZFSet.{u} → Prop) (φ : Formula.{u}) : Prop := ∃ N, φ.Below N P

variable {N N' : ℕ} {K K' : ZFSet.{u} → Prop} {e : ZFSet.{u} → ℕ} {φ : Formula.{u}}
  {U U' : ZFSet.{u}} {b : Set ℕ} {w : ℕ → ZFSet.{u}}

theorem Below.mono (h : φ.Below N K) (hN : N ≤ N') (hK : ∀ c, K c → K' c) : φ.Below N' K' := by
  induction φ with
  | equal s t => exact ⟨h.1.mono hN hK, h.2.mono hN hK⟩
  | elem s t => exact ⟨h.1.mono hN hK, h.2.mono hN hK⟩
  | conj φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | disj φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | neg φ ih => exact ih h
  | imp φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | biimp φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | all x τ φ ih => exact ⟨lt_of_lt_of_le h.1 hN, h.2.1.mono hN hK, ih h.2.2⟩
  | ex x τ φ ih => exact ⟨lt_of_lt_of_le h.1 hN, h.2.1.mono hN hK, ih h.2.2⟩

theorem exists_below {P : ZFSet.{u} → Prop} (h : φ.Below N P) :
    ∃ N', ∃ L : List ZFSet.{u}, (∀ c ∈ L, P c) ∧ φ.Below N' (· ∈ L) := by
  have two : ∀ {N1 N2 : ℕ} {L1 L2 : List ZFSet.{u}}, (∀ c ∈ L1, P c) → (∀ c ∈ L2, P c) →
      ∀ c ∈ L1 ++ L2, P c := fun h1 h2 c hc => by
    rcases List.mem_append.1 hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc
  induction φ with
  | equal s t =>
    obtain ⟨N1, L1, hP1, h1⟩ := Term.exists_below h.1
    obtain ⟨N2, L2, hP2, h2⟩ := Term.exists_below h.2
    exact ⟨max N1 N2, L1 ++ L2, two (N1 := N1) (N2 := N2) hP1 hP2,
      h1.mono (le_max_left _ _) fun c hc => List.mem_append_left _ hc,
      h2.mono (le_max_right _ _) fun c hc => List.mem_append_right _ hc⟩
  | elem s t =>
    obtain ⟨N1, L1, hP1, h1⟩ := Term.exists_below h.1
    obtain ⟨N2, L2, hP2, h2⟩ := Term.exists_below h.2
    exact ⟨max N1 N2, L1 ++ L2, two (N1 := N1) (N2 := N2) hP1 hP2,
      h1.mono (le_max_left _ _) fun c hc => List.mem_append_left _ hc,
      h2.mono (le_max_right _ _) fun c hc => List.mem_append_right _ hc⟩
  | conj φ ψ ihφ ihψ =>
    obtain ⟨N1, L1, hP1, h1⟩ := ihφ h.1
    obtain ⟨N2, L2, hP2, h2⟩ := ihψ h.2
    exact ⟨max N1 N2, L1 ++ L2, two (N1 := N1) (N2 := N2) hP1 hP2,
      h1.mono (le_max_left _ _) fun c hc => List.mem_append_left _ hc,
      h2.mono (le_max_right _ _) fun c hc => List.mem_append_right _ hc⟩
  | disj φ ψ ihφ ihψ =>
    obtain ⟨N1, L1, hP1, h1⟩ := ihφ h.1
    obtain ⟨N2, L2, hP2, h2⟩ := ihψ h.2
    exact ⟨max N1 N2, L1 ++ L2, two (N1 := N1) (N2 := N2) hP1 hP2,
      h1.mono (le_max_left _ _) fun c hc => List.mem_append_left _ hc,
      h2.mono (le_max_right _ _) fun c hc => List.mem_append_right _ hc⟩
  | neg φ ih => exact ih h
  | imp φ ψ ihφ ihψ =>
    obtain ⟨N1, L1, hP1, h1⟩ := ihφ h.1
    obtain ⟨N2, L2, hP2, h2⟩ := ihψ h.2
    exact ⟨max N1 N2, L1 ++ L2, two (N1 := N1) (N2 := N2) hP1 hP2,
      h1.mono (le_max_left _ _) fun c hc => List.mem_append_left _ hc,
      h2.mono (le_max_right _ _) fun c hc => List.mem_append_right _ hc⟩
  | biimp φ ψ ihφ ihψ =>
    obtain ⟨N1, L1, hP1, h1⟩ := ihφ h.1
    obtain ⟨N2, L2, hP2, h2⟩ := ihψ h.2
    exact ⟨max N1 N2, L1 ++ L2, two (N1 := N1) (N2 := N2) hP1 hP2,
      h1.mono (le_max_left _ _) fun c hc => List.mem_append_left _ hc,
      h2.mono (le_max_right _ _) fun c hc => List.mem_append_right _ hc⟩
  | all x τ φ ih =>
    obtain ⟨N1, L1, hP1, h1⟩ := Term.exists_below h.2.1
    obtain ⟨N2, L2, hP2, h2⟩ := ih h.2.2
    exact ⟨max (max N1 N2) (x + 1), L1 ++ L2, two (N1 := N1) (N2 := N2) hP1 hP2,
      lt_of_lt_of_le (Nat.lt_succ_self x) (le_max_right _ _),
      h1.mono (le_trans (le_max_left _ _) (le_max_left _ _)) fun c hc =>
        List.mem_append_left _ hc,
      h2.mono (le_trans (le_max_right _ _) (le_max_left _ _)) fun c hc =>
        List.mem_append_right _ hc⟩
  | ex x τ φ ih =>
    obtain ⟨N1, L1, hP1, h1⟩ := Term.exists_below h.2.1
    obtain ⟨N2, L2, hP2, h2⟩ := ih h.2.2
    exact ⟨max (max N1 N2) (x + 1), L1 ++ L2, two (N1 := N1) (N2 := N2) hP1 hP2,
      lt_of_lt_of_le (Nat.lt_succ_self x) (le_max_right _ _),
      h1.mono (le_trans (le_max_left _ _) (le_max_left _ _)) fun c hc =>
        List.mem_append_left _ hc,
      h2.mono (le_trans (le_max_right _ _) (le_max_left _ _)) fun c hc =>
        List.mem_append_right _ hc⟩

/-- Replacing constants by variables that are assigned those constants, and that are not
among the variables of the formula, does not change its truth. -/
theorem sat_abs (h : φ.Below N K) (hw : ∀ c, K c → N ≤ e c ∧ w (e c) = c) :
    Sat U w (φ.abs e) ↔ Sat U w φ := by
  induction φ generalizing w with
  | equal s t =>
    have hw' : ∀ c, K c → w (e c) = c := fun c hc => (hw c hc).2
    simp only [abs, Sat, Term.val_abs h.1 hw', Term.val_abs h.2 hw', Term.defined_abs h.1 hw',
      Term.defined_abs h.2 hw']
  | elem s t =>
    have hw' : ∀ c, K c → w (e c) = c := fun c hc => (hw c hc).2
    simp only [abs, Sat, Term.val_abs h.1 hw', Term.val_abs h.2 hw', Term.defined_abs h.1 hw',
      Term.defined_abs h.2 hw']
  | conj φ ψ ihφ ihψ => simp only [abs, Sat, ihφ h.1 hw, ihψ h.2 hw]
  | disj φ ψ ihφ ihψ => simp only [abs, Sat, ihφ h.1 hw, ihψ h.2 hw]
  | neg φ ih => simp only [abs, Sat, ih h hw]
  | imp φ ψ ihφ ihψ => simp only [abs, Sat, ihφ h.1 hw, ihψ h.2 hw]
  | biimp φ ψ ihφ ihψ => simp only [abs, Sat, ihφ h.1 hw, ihψ h.2 hw]
  | all x τ φ ih =>
    have hw' : ∀ c, K c → w (e c) = c := fun c hc => (hw c hc).2
    have key : ∀ a, Sat U (Function.update w x a) (φ.abs e) ↔ Sat U (Function.update w x a) φ :=
      fun a => ih h.2.2 fun c hc => ⟨(hw c hc).1, by
        have h1 := (hw c hc).1
        have h2 := h.1
        rw [Function.update_of_ne (by omega)]
        exact (hw c hc).2⟩
    simp only [abs, Sat, Term.val_abs h.2.1 hw', Term.defined_abs h.2.1 hw', key]
  | ex x τ φ ih =>
    have hw' : ∀ c, K c → w (e c) = c := fun c hc => (hw c hc).2
    have key : ∀ a, Sat U (Function.update w x a) (φ.abs e) ↔ Sat U (Function.update w x a) φ :=
      fun a => ih h.2.2 fun c hc => ⟨(hw c hc).1, by
        have h1 := (hw c hc).1
        have h2 := h.1
        rw [Function.update_of_ne (by omega)]
        exact (hw c hc).2⟩
    simp only [abs, Sat, Term.val_abs h.2.1 hw', Term.defined_abs h.2.1 hw', key]

/-- A formula without constants is its own transform. -/
theorem star_abs (s : ZFSet.{u} → ZFSet.{u}) (φ : Formula.{u}) :
    (φ.abs e).star s = φ.abs e := by
  induction φ with
  | equal s t => simp only [abs, star, Term.star_abs]
  | elem s t => simp only [abs, star, Term.star_abs]
  | conj φ ψ ihφ ihψ => simp only [abs, star, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [abs, star, ihφ, ihψ]
  | neg φ ih => simp only [abs, star, ih]
  | imp φ ψ ihφ ihψ => simp only [abs, star, ihφ, ihψ]
  | biimp φ ψ ihφ ihψ => simp only [abs, star, ihφ, ihψ]
  | all x τ φ ih => simp only [abs, star, Term.star_abs, ih]
  | ex x τ φ ih => simp only [abs, star, Term.star_abs, ih]

theorem admissible_abs (h : φ.Admissible U' b) (hB : φ.Below N K) (he : ∀ c, K c → N ≤ e c) :
    (φ.abs e).Admissible U (b ∪ {n | ∃ c, K c ∧ e c = n}) := by
  have hq : ∀ {x : ℕ} {b : Set ℕ}, x < N →
      (b \ {x} ∪ {n | ∃ c, K c ∧ e c = n}) ⊆ (b ∪ {n | ∃ c, K c ∧ e c = n}) \ {x} ∧
      (insert x b ∪ {n | ∃ c, K c ∧ e c = n}) ⊆ insert x (b ∪ {n | ∃ c, K c ∧ e c = n}) := by
    intro x b hx
    constructor
    · rintro n (hn | ⟨c, hc, rfl⟩)
      · exact ⟨Or.inl hn.1, hn.2⟩
      · refine ⟨Or.inr ⟨c, hc, rfl⟩, fun hx' => ?_⟩
        have h1 := he c hc
        have h2 : e c = x := hx'
        omega
    · rintro n (hn | hn)
      · rcases hn with rfl | hn
        · exact Or.inl rfl
        · exact Or.inr (Or.inl hn)
      · exact Or.inr (Or.inr hn)
  induction φ generalizing b with
  | equal s t => exact ⟨Term.admissible_abs h.1 hB.1, Term.admissible_abs h.2 hB.2⟩
  | elem s t => exact ⟨Term.admissible_abs h.1 hB.1, Term.admissible_abs h.2 hB.2⟩
  | conj φ ψ ihφ ihψ => exact ⟨ihφ h.1 hB.1, ihψ h.2 hB.2⟩
  | disj φ ψ ihφ ihψ => exact ⟨ihφ h.1 hB.1, ihψ h.2 hB.2⟩
  | neg φ ih => exact ih h hB
  | imp φ ψ ihφ ihψ => exact ⟨ihφ h.1 hB.1, ihψ h.2 hB.2⟩
  | biimp φ ψ ihφ ihψ => exact ⟨ihφ h.1 hB.1, ihψ h.2 hB.2⟩
  | all x τ φ ih =>
    exact ⟨(Term.admissible_abs h.1 hB.2.1).mono (hq hB.1).1, (ih h.2 hB.2.2).mono (hq hB.1).2⟩
  | ex x τ φ ih =>
    exact ⟨(Term.admissible_abs h.1 hB.2.1).mono (hq hB.1).1, (ih h.2 hB.2.2).mono (hq hB.1).2⟩

end Formula

attribute [simp] Sat

/-- Unfold the truth definition of an explicitly written formula: evaluates satisfaction,
values and definedness of terms, transforms, and the assignment at numbered variables. -/
macro "sat_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Formula.Holds, Formula.star, Term.star, Sat, Term.Defined, Term.val,
    Term.val_opair, Term.defined_opair, Term.star_opair, forall_true_left, true_and, and_true,
    and_self, implies_true, Function.update_self, Function.update_of_ne, ne_eq,
    not_false_eq_true, zero_ne_one, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.zero_ne_ofNat,
    OfNat.ofNat_ne_one, OfNat.one_ne_ofNat, Nat.reduceEqDiff] $[$loc]?)

/-- **Section 13.7, an example.** The sentence $`(\forall x \in \mathcal P(A))
(\forall y \in x)\,(y \in A)`, used in Section 13.8, is true in every universe containing the
set $`A`. -/
example {U A : ZFSet.{u}} (hU : IsUniverse U) (hA : IsSetOf U A) :
    (Formula.all 0 (.const (powerset A)) (.all 1 (.var 0) (.elem (.var 1) (.const A)))).IsSentence U
      ∧ (Formula.all 0 (.const (powerset A)) (.all 1 (.var 0) (.elem (.var 1) (.const A)))).Holds
        U := by
  refine ⟨by simp [Formula.IsSentence, hA.1, (hU.isSetOf_powerset hA).1], ?_⟩
  simp only [Formula.Holds, Sat, Term.Defined, Term.val, forall_true_left, true_and,
    Function.update_self, mem_powerset]
  intro a _ haA b _ hba
  simpa using haA hba

end Goldblatt
