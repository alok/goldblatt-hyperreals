import Goldblatt.Ch04_Transfer.Los

/-!
# 4 (part 3). Transfer at Work: Sections 4.1 and 4.3 to 4.7

This is the third of three parts of Chapter 4 (the overview is on the chapter page
{lit}`Goldblatt.Ch04_Transfer`). The worked examples and exercises of the chapter are written
out as formal sentences of the language of Part 1 and settled with the transfer principle of
Part 2. Each example follows the same pattern:

* a definition gives the sentence, as a formula of the language of the full structure;
* a lemma reads off what it means for the sentence to be true, and another what it means for
  its star-transform to be true (this is the content of Exercise 4.4.1: the informal transforms
  of Section 4.1 are what the formal definition produces);
* the statement about the hyperreals is then obtained from the statement about the reals by
  {name}`Goldblatt.Formula.transfer`, in whichever direction is wanted.

The examples of Section 4.1 open the book's chapter, before the formal language exists; here
they come after it, since they are proved with it.
-/

universe u

namespace Goldblatt

open Set Filter Function Ultrapower Term Formula
open scoped Hyperreal Lang

/-- **Section 4.1, notation.** The set of natural numbers, as a set of reals. Its enlargement is the set
{lit}`ℕ*` of hypernatural numbers, by definition. -/
local notation "ℕᵣ" => (range ((↑) : ℕ → ℝ))

/-- **Section 4.1, notation.** The set of rational numbers, as a set of reals. Its enlargement is {lit}`ℚ*`. -/
local notation "ℚᵣ" => (range ((↑) : ℚ → ℝ))

/-- **Section 4.1, helper.** A natural number, sent to the reals and then to the hyperreals, is that natural number as a
hyperreal. -/
theorem coe_natCast_real (n : ℕ) : ((n : ℝ) : ℝ*) = (n : ℝ*) := rfl

/-!
## 4.3 Examples: free variables and undefined terms

Two small examples from Section 4.3 of the book. The first is its illustration of free and
bound occurrences. The second is its illustration of an undefined term: with the tangent as a
partial function, the instance of an identity at an argument outside the domain is an
undefined sentence, and the universally quantified identity is true all the same, because
undefined instances are passed over.
-/

section FreeVars

variable {S : Type u}

/-- **Section 4.3.** The only variable of a variable is itself. -/
@[simp] theorem Term.vars_var (x : ℕ) : (var x : Term S).vars = {x} := rfl

/-- **Section 4.3.** A constant has no variables. -/
@[simp] theorem Term.vars_const (s : S) : (const s).vars = ∅ := rfl

/-- **Section 4.3.** The variables of $`f(\tau)` are those of $`\tau`. -/
@[simp] theorem Term.vars_app₁ (f : S → S) (t : Term S) : (app₁ f t).vars = t.vars := by
  ext x
  simp [app₁, vars]

/-- **Section 4.3.** The variables of $`f(\tau_1, \tau_2)` are those of the two arguments. -/
@[simp] theorem Term.vars_app₂ (f : S → S → S) (t u : Term S) :
    (app₂ f t u).vars = t.vars ∪ u.vars := by
  ext x
  simp [app₂, vars, Fin.exists_fin_two]

/-- **Section 4.3.** For a partial function $`f`, the variables of $`f(\tau)` are those of $`\tau`.
-/
@[simp] theorem Term.vars_papp₁ (A : Set S) (f : A → S) (t : Term S) :
    (papp₁ A f t).vars = t.vars := by
  ext x
  simp [papp₁, vars]

/-- **Section 4.3.** The free variables of $`\tau \in A` are the variables of $`\tau`. -/
@[simp] theorem Formula.freeVars_mem (t : Term S) (A : Set S) : (mem t A).freeVars = t.vars := by
  ext x
  simp [mem, freeVars]

/-- **Section 4.3.** The free variables of $`P(\tau_1, \tau_2)` are the variables of the two terms.
-/
@[simp] theorem Formula.freeVars_rel₂ (P : S → S → Prop) (t u : Term S) :
    (rel₂ P t u).freeVars = t.vars ∪ u.vars := by
  ext x
  simp [rel₂, freeVars, Fin.exists_fin_two]

/-- **Section 4.3.** The free variables of $`\tau_1 = \tau_2` are the variables of the two terms. -/
@[simp] theorem Formula.freeVars_eq (t u : Term S) : (eq t u).freeVars = t.vars ∪ u.vars :=
  freeVars_rel₂ _ t u

/-- **Section 4.3.** The free variables of $`\tau_1 < \tau_2` are the variables of the two terms. -/
@[simp] theorem Formula.freeVars_lt (t u : Term ℝ) : (lt t u).freeVars = t.vars ∪ u.vars :=
  freeVars_rel₂ _ t u

/-- **Section 4.3.** The free variables of $`\tau_1 \le \tau_2` are the variables of the two terms.
-/
@[simp] theorem Formula.freeVars_le (t u : Term ℝ) : (le t u).freeVars = t.vars ∪ u.vars :=
  freeVars_rel₂ _ t u

end FreeVars

/-- **Section 4.3, free and bound occurrences.** The book's example
$`(x < 1) \land (\forall x \in \mathbb N)(x > y)`, with $`x` the variable $`0` and $`y` the
variable $`1`. Here $`\mathbb N` is Lean's set of natural numbers, which contains $`0`; the
variant {lit}`freeBoundExample'` below uses the book's $`\{1, 2, \dots\}`. -/
def freeBoundExample : Formula ℝ :=
  (var 0 <' const 1) ⋏ (∀' 0 ∈ ℕᵣ, var 1 <' var 0)

/-- **Section 4.3, free and bound occurrences.** In
$`(x < 1) \land (\forall x \in \mathbb N)(x > y)` both $`x` and $`y` occur free: the first
occurrence of $`x` is free although the later ones are bound. So the formula is not a
sentence. -/
theorem freeVars_freeBoundExample : freeBoundExample.freeVars = {0, 1} := by
  ext x
  simp only [freeBoundExample, freeVars, Formula.freeVars_lt, Term.vars_var, Term.vars_const,
    mem_union, Set.mem_sdiff, mem_singleton_iff, mem_insert_iff, mem_empty_iff_false]
  tauto

/-- **Section 4.3.** The formula $`(x < 1) \land (\forall x \in \mathbb N)(x > y)` is true when
$`x = 0` and $`y = -1`. (The book takes $`x = y = 0`, its natural numbers starting at $`1`;
Lean's start at $`0`, so $`y` must be smaller. The book's own values are verified for the
variant with positive naturals in {lit}`holds_freeBoundExample'_zero`.) -/
theorem holds_freeBoundExample_zero :
    freeBoundExample.Holds (update (update Valuation.empty 0 (some 0)) 1 (some (-1))) := by
  simp only [freeBoundExample, holds_and, holds_lt, holds_all, names_var, names_const,
    mem_range, forall_exists_index]
  refine ⟨⟨0, 1, by simp, rfl, one_pos⟩, ?_⟩
  rintro _ n rfl -
  exact ⟨-1, n, by simp, by simp, by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩

/-- **Section 4.3.** The formula $`(x < 1) \land (\forall x \in \mathbb N)(x > y)` is false when
$`x = 2`, whatever the value of $`y`. -/
theorem not_holds_freeBoundExample_two (y : ℝ) :
    ¬freeBoundExample.Holds (update (update Valuation.empty 0 (some 2)) 1 (some y)) := by
  simp only [freeBoundExample, holds_and, holds_lt, names_var, names_const]
  rintro ⟨⟨a, b, ha, rfl, hab⟩, -⟩
  simp at ha
  subst ha
  norm_num at hab

/-- **Section 4.3.** The book's set of natural numbers $`\{1, 2, 3, \dots\}`, as a set of
reals. Lean's natural numbers start at $`0`, so this is the set of their successors. -/
def posNat : Set ℝ := range fun n : ℕ => (n : ℝ) + 1

/-- **Section 4.3.** A real number is a positive natural number exactly when it is a natural
number and at least $`1`. -/
theorem mem_posNat_iff (a : ℝ) : a ∈ posNat ↔ a ∈ ℕᵣ ∧ 1 ≤ a := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨⟨n + 1, by push_cast; rfl⟩, by simp⟩
  · rintro ⟨⟨m, rfl⟩, h⟩
    have hm : 1 ≤ m := by exact_mod_cast h
    exact ⟨m - 1, by
      have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm, Nat.cast_one]
      simp only [this]
      ring⟩

/-- **Section 4.3, free and bound occurrences, literally.** The book's example
$`(x < 1) \land (\forall x \in \mathbb N)(x > y)` with the bound read as the book reads it,
the natural numbers from $`1` on. -/
def freeBoundExample' : Formula ℝ :=
  (var 0 <' const 1) ⋏ (∀' 0 ∈ posNat, var 1 <' var 0)

/-- **Section 4.3.** With the natural numbers starting at $`1`, the formula
$`(x < 1) \land (\forall x \in \mathbb N)(x > y)` is true when $`x = y = 0`, as the book
says. -/
theorem holds_freeBoundExample'_zero :
    freeBoundExample'.Holds (update (update Valuation.empty 0 (some 0)) 1 (some 0)) := by
  simp only [freeBoundExample', holds_and, holds_lt, holds_all, names_var, names_const, posNat,
    mem_range, forall_exists_index]
  refine ⟨⟨0, 1, by simp, rfl, one_pos⟩, ?_⟩
  rintro _ n rfl -
  exact ⟨0, n + 1, by simp, by simp, by positivity⟩

/-- **Section 4.3.** With the natural numbers starting at $`1`, the formula is again false when
$`x = 2`, whatever the value of $`y`. -/
theorem not_holds_freeBoundExample'_two (y : ℝ) :
    ¬freeBoundExample'.Holds (update (update Valuation.empty 0 (some 2)) 1 (some y)) := by
  simp only [freeBoundExample', holds_and, holds_lt, names_var, names_const]
  rintro ⟨⟨a, b, ha, rfl, hab⟩, -⟩
  simp at ha
  subst ha
  norm_num at hab

/-- **Section 4.3.** The domain of the tangent: the reals at which the cosine does not vanish. -/
def tanDomain : Set ℝ := {x | Real.cos x ≠ 0}

/-- **Section 4.3.** The tangent as a partial function, defined where the cosine does not
vanish. -/
noncomputable def partialTan : tanDomain → ℝ := fun x => Real.tan x

/-- **Section 4.3.** The formula $`\tan(-x) = -\tan(x)`, with the tangent partial and $`x` the
variable $`0`. -/
noncomputable def tanOddFormula : Formula ℝ :=
  papp₁ tanDomain partialTan (app₁ (fun a => -a) (var 0)) ='
    app₁ (fun a => -a) (papp₁ tanDomain partialTan (var 0))

/-- **Section 4.3, an undefined sentence.** Substituting $`\pi/2` for $`x` in
$`\tan(-x) = -\tan(x)` gives a sentence that is not defined: its closed term
$`\tan(\pi/2)` names nothing. -/
theorem not_isDefined_tanOddFormula_subst :
    ¬(tanOddFormula.subst 0 (Real.pi / 2)).IsDefined := by
  simp only [tanOddFormula, IsDefined, Formula.defined_subst, defined_eq, defined_app₁,
    defined_papp₁, defined_var, closed_var, names_var, update_self, Option.some.injEq,
    exists_eq_left', true_and, ne_eq, reduceCtorEq, not_false_eq_true, forall_const, not_and]
  intro _ h
  simp [tanDomain] at h

/-- **Section 4.3, a true sentence with undefined instances.** The sentence
$`(\forall x \in \mathbb R)[\tan(-x) = -\tan(x)]`. -/
noncomputable def tanOddSentence : Formula ℝ := ∀' 0 ∈ univ, tanOddFormula

/-- **Section 4.3.** $`(\forall x \in \mathbb R)[\tan(-x) = -\tan(x)]` is a sentence, and it is
defined: it has no closed terms at all. -/
theorem tanOddSentence_isSentence_isDefined :
    tanOddSentence.IsSentence ∧ tanOddSentence.IsDefined := by
  constructor
  · simp [IsSentence, tanOddSentence, tanOddFormula, freeVars]
  · simp [IsDefined, tanOddSentence, tanOddFormula]

/-- **Section 4.3.** $`(\forall x \in \mathbb R)[\tan(-x) = -\tan(x)]` is true: every instance
that is defined is true. -/
theorem isTrue_tanOddSentence : tanOddSentence.IsTrue := by
  simp only [tanOddSentence, tanOddFormula, IsTrue, holds_all, holds_eq, names_papp₁,
    names_app₁, names_var, update_self, Option.some.injEq, mem_univ, forall_const, defined_eq,
    defined_app₁, defined_papp₁, defined_var, closed_var, closed_app₁, exists_eq_left',
    true_and, ne_eq, reduceCtorEq, not_false_eq_true]
  rintro a ⟨h1, h2⟩
  exact ⟨_, _, ⟨h1, rfl⟩, ⟨_, ⟨h2, rfl⟩, rfl⟩, by simp [partialTan, Real.tan_neg]⟩

/-- **Sections 4.3 and 4.5.** By transfer, the extended tangent is odd wherever both sides are
defined: for a hyperreal $`x` such that $`x` and $`-x` lie in the enlarged domain,
$`{}^*\tan(-x) = -{}^*\tan(x)`. -/
theorem starTan_neg (x : ℝ*) (h : x ∈ ⋆tanDomain) (h' : -x ∈ ⋆tanDomain) :
    starMapOn tanDomain partialTan ⟨-x, h'⟩ = -starMapOn tanDomain partialTan ⟨x, h⟩ := by
  have key := (transfer (αS := ℝ*) tanOddSentence).2 isTrue_tanOddSentence
  simp only [tanOddSentence, tanOddFormula, IsTrue, Formula.star_all, holds_all, holds_star_eq,
    names_star_papp₁, names_star_app₁, Term.star_var, names_var, update_self,
    Option.some.injEq, starSet_univ, mem_univ, forall_const, defined_star_eq,
    defined_star_papp₁, defined_star_app₁, defined_var, closed_star_app₁, closed_var, true_and,
    ne_eq, reduceCtorEq, not_false_eq_true] at key
  obtain ⟨_, _, ⟨_, ⟨_, rfl, rfl⟩, ha, rfl⟩, ⟨_, ⟨_, rfl, hb, rfl⟩, rfl⟩, hab⟩ :=
    key x ⟨⟨_, ⟨x, rfl, rfl⟩, h'⟩, ⟨x, rfl, h⟩⟩
  exact hab

/-!
## 4.1 Transforming Statements

The six examples that open the chapter. Each is a sentence about the reals whose star-transform
is a statement about the hyperreals, and each time the second follows from the first, or the
first from the second, by transfer.
-/

/-!
### Example 1: the Eudoxus–Archimedes principle
-/

/-- **Section 4.1, example 1.** The sentence
$`(\forall x \in \mathbb R)(\exists m \in \mathbb N)(x < m)`. -/
def archimedeanSentence : Formula ℝ := ∀' 0 ∈ univ, ∃' 1 ∈ ℕᵣ, var 0 <' var 1

/-- **Section 4.1, example 1.** The sentence says that every real number is less than some
natural number. -/
theorem isTrue_archimedeanSentence :
    archimedeanSentence.IsTrue ↔ ∀ x : ℝ, ∃ m ∈ ℕᵣ, x < m := by
  simp [archimedeanSentence, IsTrue]

/-- **Section 4.1, example 1, and Exercise 4.4.1.** The star-transform of the sentence is
$`(\forall x \in {}^*\mathbb R)(\exists m \in {}^*\mathbb N)(x < m)`. -/
theorem isTrue_star_archimedeanSentence :
    archimedeanSentence.star.IsTrue ↔ ∀ x : ℝ*, ∃ m ∈ ℕ*, x < m := by
  simp [archimedeanSentence, IsTrue, starSet_univ, hyperNat]

/-- **Section 4.1, example 1.** The sentence is indeed a sentence, and it is defined. -/
theorem archimedeanSentence_isSentence_isDefined :
    archimedeanSentence.IsSentence ∧ archimedeanSentence.IsDefined := by
  constructor
  · simp [IsSentence, archimedeanSentence, freeVars]
  · simp [IsDefined, archimedeanSentence]

/-- **Section 4.1, example 1, and Exercise 4.1.1.** By transfer, every hyperreal is less than
some hypernatural number. -/
theorem exists_hyperNat_gt (x : ℝ*) : ∃ m ∈ ℕ*, x < m :=
  isTrue_star_archimedeanSentence.1 ((transfer _).2 (isTrue_archimedeanSentence.2 fun x =>
    let ⟨n, hn⟩ := exists_nat_gt x; ⟨n, ⟨n, rfl⟩, hn⟩)) x

/-- **Section 4.1, example 1.** The same principle with the range of each quantifier displayed
by a conjunct, as in the book's first formulation:
$`(\forall x \in \mathbb R)(\exists m \in \mathbb R)(x < m \land m \in \mathbb N)`. -/
def archimedeanSentence' : Formula ℝ :=
  ∀' 0 ∈ univ, ∃' 1 ∈ univ, (var 0 <' var 1 ⋏ var 1 ∈' ℕᵣ)

/-- **Section 4.1, example 1.** The transform of the first formulation replaces $`\mathbb N` by
$`{}^*\mathbb N`. -/
theorem isTrue_star_archimedeanSentence' :
    archimedeanSentence'.star.IsTrue ↔ ∀ x : ℝ*, ∃ m : ℝ*, x < m ∧ m ∈ ℕ* := by
  simp [archimedeanSentence', IsTrue, starSet_univ, hyperNat]

/-- **Section 4.1, example 1.** The first formulation says that every real number is less than
some real number that is a natural number. -/
theorem isTrue_archimedeanSentence' :
    archimedeanSentence'.IsTrue ↔ ∀ x : ℝ, ∃ m : ℝ, x < m ∧ m ∈ ℕᵣ := by
  simp [archimedeanSentence', IsTrue]

/-- **Section 4.1, example 1.** The first formulation is true of the reals: this is the
Eudoxus–Archimedes principle. -/
theorem archimedeanSentence'_isTrue : archimedeanSentence'.IsTrue :=
  isTrue_archimedeanSentence'.2 fun x =>
    let ⟨n, hn⟩ := exists_nat_gt x; ⟨n, hn, ⟨n, rfl⟩⟩

/-- **Section 4.1, example 1, and Exercise 4.1.1.** By transfer of the first formulation, every
hyperreal is less than some hyperreal that is a hypernatural number. -/
theorem exists_hyperNat_gt' (x : ℝ*) : ∃ m : ℝ*, x < m ∧ m ∈ ℕ* :=
  isTrue_star_archimedeanSentence'.1 ((transfer _).2 archimedeanSentence'_isTrue) x

/-- **Section 4.1, example 1.** The sentence
$`(\forall x \in {}^*\mathbb R)(\exists m \in \mathbb N)(x < m)`, in which the first bound has
been starred and the second has not. It is a sentence of the language of the full structure on
the hyperreals. -/
def mixedArchimedeanSentence : Formula ℝ* :=
  ∀' 0 ∈ univ, ∃' 1 ∈ range ((↑) : ℕ → ℝ*), rel₂ (fun a b => a < b) (var 0) (var 1)

/-- **Section 4.1, example 1.** The mixed sentence says that every hyperreal is less than some
standard natural number. -/
theorem isTrue_mixedArchimedeanSentence :
    mixedArchimedeanSentence.IsTrue ↔ ∀ x : ℝ*, ∃ m : ℕ, x < (m : ℝ*) := by
  simp [mixedArchimedeanSentence, IsTrue]

/-- **Section 4.1, example 1.** The mixed sentence is false: $`\omega` is greater than every
natural number. Replacing $`\mathbb N` by $`{}^*\mathbb N` is what makes the transform true. -/
theorem not_isTrue_mixedArchimedeanSentence : ¬mixedArchimedeanSentence.IsTrue := by
  rw [isTrue_mixedArchimedeanSentence]
  intro h
  obtain ⟨m, hm⟩ := h ω
  exact lt_asymm hm (real_lt_omega m)

/-- **Section 4.1, example 1, and Exercise 4.2.1.** The mixed sentence is not a sentence of the
language of $`{}^*\mathfrak R`: its bound $`\mathbb N` is not a relation of that structure. So
it is no counterexample to transfer. -/
theorem not_over_mixedArchimedeanSentence :
    ¬mixedArchimedeanSentence.Over (RelStructure.star ℝ) := by
  rintro ⟨-, h, -⟩
  obtain ⟨B, hB⟩ := unaryRel_mem_star_iff.1 h
  exact (number_systems_ne_starSet B).1 hB

/-!
### Example 2: density of the rationals
-/

/-- **Section 4.1, example 2.** The sentence
$`(\forall x, y \in \mathbb R)(x < y \to (\exists q \in \mathbb Q)(x < q < y))`. -/
def densitySentence : Formula ℝ :=
  ∀' 0 ∈ univ, ∀' 1 ∈ univ, (var 0 <' var 1 ⟹ (∃' 2 ∈ ℚᵣ, (var 0 <' var 2 ⋏ var 2 <' var 1)))

/-- **Section 4.1, example 2.** The sentence says that the rationals are dense in the reals. -/
theorem isTrue_densitySentence :
    densitySentence.IsTrue ↔ ∀ x y : ℝ, x < y → ∃ q ∈ ℚᵣ, x < q ∧ q < y := by
  simp [densitySentence, IsTrue]

/-- **Section 4.1, example 2, and Exercise 4.4.1.** The star-transform is
$`(\forall x, y \in {}^*\mathbb R)(x < y \to (\exists q \in {}^*\mathbb Q)(x < q < y))`. -/
theorem isTrue_star_densitySentence :
    densitySentence.star.IsTrue ↔ ∀ x y : ℝ*, x < y → ∃ q ∈ ℚ*, x < q ∧ q < y := by
  simp [densitySentence, IsTrue, starSet_univ, hyperRat]

/-- **Section 4.1, example 2, and Exercise 4.1.1.** By transfer, the hyperrationals are dense in
the hyperreals. -/
theorem exists_hyperRat_btwn {x y : ℝ*} (h : x < y) : ∃ q ∈ ℚ*, x < q ∧ q < y :=
  isTrue_star_densitySentence.1 ((transfer _).2 (isTrue_densitySentence.2 fun _ _ hxy =>
    let ⟨q, h1, h2⟩ := exists_rat_btwn hxy; ⟨q, ⟨q, rfl⟩, h1, h2⟩)) x y h

/-!
### Example 3: finiteness
-/

section Finiteness

variable {S : Type u} {α αS : Type u} [StarType α αS]

/-- **Section 4.1, example 3.** The formula $`\tau = r_1 \lor \dots \lor \tau = r_k` for a
nonempty list $`r_1, \dots, r_k` of constants. -/
def Formula.anyEq (t : Term S) : S → List S → Formula S
  | r, [] => eq t (const r)
  | r, r' :: l => or (eq t (const r)) (anyEq t r' l)

/-- **Section 4.1, example 3.** The disjunction $`\tau = r_1 \lor \dots \lor \tau = r_k` is true
when $`\tau` names one of the listed elements. -/
theorem Formula.holds_anyEq {t : Term S} {v : Valuation S} (r : S) (l : List S) :
    (anyEq t r l).Holds v ↔ ∃ a, t.Names v a ∧ a ∈ r :: l := by
  induction l generalizing r with
  | nil => simp [anyEq]
  | cons r' l ih => simp [anyEq, ih r', and_or_left, exists_or]

/-- **Section 4.1, example 3.** The disjunction is defined when $`\tau` is. -/
theorem Formula.defined_anyEq {t : Term S} {v : Valuation S} (r : S) (l : List S) :
    (anyEq t r l).Defined v ↔ t.Defined v := by
  induction l generalizing r with
  | nil => simp [anyEq]
  | cons r' l ih => simp [anyEq, ih r']

/-- **Section 4.1, example 3.** The transform of the disjunction is true when the transform of
$`\tau` names the standard copy of one of the listed elements. -/
theorem Formula.holds_star_anyEq {t : Term α} {v : Valuation αS} (r : α) (l : List α) :
    ((anyEq t r l).star : Formula αS).Holds v ↔
      ∃ a, (t.star : Term αS).Names v a ∧ ∃ b ∈ r :: l, of b = a := by
  induction l generalizing r with
  | nil => simp [anyEq]
  | cons r' l ih => simp [anyEq, ih r', and_or_left, exists_or]

/-- **Section 4.1, example 3.** The transform of the disjunction is defined when the transform of
$`\tau` is. -/
theorem Formula.defined_star_anyEq {t : Term α} {v : Valuation αS} (r : α) (l : List α) :
    ((anyEq t r l).star : Formula αS).Defined v ↔ (t.star : Term αS).Defined v := by
  induction l generalizing r with
  | nil => simp [anyEq]
  | cons r' l ih => simp [anyEq, ih r']

/-- **Section 4.1, example 3.** For $`A = \{r_1, \dots, r_k\}`, the sentence
$`(\forall x \in A)(x = r_1 \lor \dots \lor x = r_k)`. -/
def finiteSentence (r : α) (l : List α) : Formula α :=
  ∀' 0 ∈ {x | x ∈ r :: l}, anyEq (var 0) r l

/-- **Section 4.1, example 3.** The sentence is true. -/
theorem isTrue_finiteSentence (r : α) (l : List α) : (finiteSentence r l).IsTrue := by
  simp [finiteSentence, IsTrue, holds_anyEq, defined_anyEq]

/-- **Section 4.1, example 3, and Exercise 4.4.1.** The star-transform is
$`(\forall x \in {}^*A)(x = {}^*r_1 \lor \dots \lor x = {}^*r_k)`. -/
theorem isTrue_star_finiteSentence (r : α) (l : List α) :
    ((finiteSentence r l).star : Formula αS).IsTrue ↔
      ∀ x ∈ (⋆{x | x ∈ r :: l} : Set αS), ∃ b, x = of b ∧ b ∈ r :: l := by
  simp [finiteSentence, IsTrue, holds_star_anyEq, defined_star_anyEq]

/-- **Exercise 3.10(3) by transfer.** The sentence
$`(\forall x \in \emptyset)\,\lnot(x = x)`, which is true because there is nothing to check. -/
def emptySentence (α : Type u) : Formula α := ∀' 0 ∈ (∅ : Set α), ∼'(var 0 =' var 0)

/-- **Exercises 4.5.1 and 3.10(3).** By transfer, the enlargement of the empty set is empty: the
transform of $`(\forall x \in \emptyset)\,\lnot(x = x)` says that no member of
$`{}^*\emptyset` is equal to itself. -/
theorem starSet_empty_by_transfer : (⋆(∅ : Set α) : Set αS) = ∅ := by
  have key := (transfer (αS := αS) (emptySentence α)).2 (by simp [emptySentence, IsTrue])
  simp [emptySentence, IsTrue] at key
  exact eq_empty_iff_forall_notMem.2 key

/-- **Section 4.1, example 3, and Exercises 4.1.1, 3.10(1).** By transfer, the enlargement of a
finite set is the set itself: a finite set of standard elements has no nonstandard members. The
argument needs the set to be listed by finitely many constants, which is why it says nothing
about infinite sets. -/
theorem starSet_of_finite_by_transfer {A : Set α} (hA : A.Finite) :
    (⋆A : Set αS) = of '' A := by
  refine Subset.antisymm ?_ (image_of_subset_starSet A)
  obtain ⟨L, hL⟩ : ∃ L : List α, A = {x | x ∈ L} :=
    ⟨hA.toFinset.toList, by ext x; simp⟩
  subst hL
  cases L with
  | nil =>
    have : ({x | x ∈ ([] : List α)} : Set α) = ∅ := by ext x; simp
    rw [this, starSet_empty_by_transfer]
    exact empty_subset _
  | cons r l =>
    intro x hx
    obtain ⟨b, rfl, hb⟩ := (isTrue_star_finiteSentence r l).1
      ((transfer _).2 (isTrue_finiteSentence r l)) x hx
    exact ⟨b, hb, rfl⟩

end Finiteness

/-!
### Example 4: finitary set operations
-/

section SetOperations

variable {α αS : Type u} [StarType α αS]

/-- **Section 4.1, example 4.** The sentence
$`(\forall x \in \mathbb R)(x \in A \cup B \leftrightarrow x \in A \lor x \in B)`. -/
def unionSentence (A B : Set α) : Formula α :=
  ∀' 0 ∈ univ, (var 0 ∈' (A ∪ B) ⟺ (var 0 ∈' A ⋎ var 0 ∈' B))

/-- **Section 4.1, example 4, and Exercise 4.4.1.** The star-transform is
$`(\forall x \in {}^*\mathbb R)(x \in {}^*(A \cup B) \leftrightarrow x \in {}^*A \lor
x \in {}^*B)`. -/
theorem isTrue_star_unionSentence (A B : Set α) :
    ((unionSentence A B).star : Formula αS).IsTrue ↔
      ∀ x : αS, x ∈ ⋆(A ∪ B) ↔ x ∈ ⋆A ∨ x ∈ ⋆B := by
  simp [unionSentence, IsTrue, starSet_univ]

/-- **Section 4.1, example 4, and Exercises 4.1.1, 3.10(3).** By transfer,
$`{}^*(A \cup B) = {}^*A \cup {}^*B`. -/
theorem starSet_union_by_transfer (A B : Set α) : (⋆(A ∪ B) : Set αS) = ⋆A ∪ ⋆B := by
  ext x
  refine (isTrue_star_unionSentence A B).1 ((transfer _).2 ?_) x
  simp [unionSentence, IsTrue]

/-- **Section 4.1, example 4.** The sentence
$`(\forall x \in \mathbb R)(x \in A \cap B \leftrightarrow x \in A \land x \in B)`. -/
def interSentence (A B : Set α) : Formula α :=
  ∀' 0 ∈ univ, (var 0 ∈' (A ∩ B) ⟺ (var 0 ∈' A ⋏ var 0 ∈' B))

/-- **Section 4.1, example 4, and Exercise 3.10(3).** By transfer,
$`{}^*(A \cap B) = {}^*A \cap {}^*B`. -/
theorem starSet_inter_by_transfer (A B : Set α) : (⋆(A ∩ B) : Set αS) = ⋆A ∩ ⋆B := by
  ext x
  have key := (transfer (αS := αS) (interSentence A B)).2 (by simp [interSentence, IsTrue])
  simp [interSentence, IsTrue, starSet_univ] at key
  exact key x

/-- **Section 4.1, example 4.** The sentence
$`(\forall x \in \mathbb R)(x \in A - B \leftrightarrow x \in A \land \lnot\, x \in B)`. -/
def diffSentence (A B : Set α) : Formula α :=
  ∀' 0 ∈ univ, (var 0 ∈' (A \ B) ⟺ (var 0 ∈' A ⋏ ∼'(var 0 ∈' B)))

/-- **Section 4.1, example 4, and Exercise 3.10(3).** By transfer,
$`{}^*(A - B) = {}^*A - {}^*B`. -/
theorem starSet_diff_by_transfer (A B : Set α) : (⋆(A \ B) : Set αS) = ⋆A \ ⋆B := by
  ext x
  have key := (transfer (αS := αS) (diffSentence A B)).2 (by simp [diffSentence, IsTrue])
  simp [diffSentence, IsTrue, starSet_univ] at key
  exact key x

/-- **Exercise 3.10(2) by transfer.** The sentence $`(\forall x \in A)(x \in B)`. -/
def subsetSentence (A B : Set α) : Formula α := ∀' 0 ∈ A, var 0 ∈' B

/-- **Exercises 4.5.1 and 3.10(2).** By transfer, $`A \subseteq B` if and only if
$`{}^*A \subseteq {}^*B`: the two inclusions are the truth of a sentence and of its
transform. -/
theorem starSet_subset_starSet_by_transfer {A B : Set α} :
    (⋆A : Set αS) ⊆ ⋆B ↔ A ⊆ B := by
  have key := transfer (αS := αS) (subsetSentence A B)
  simpa [subsetSentence, IsTrue, subset_def] using key

/-- **Exercises 4.5.1 and 3.10(2).** $`A = B` if and only if $`{}^*A = {}^*B`, from the
transferred inclusions in both directions. -/
theorem starSet_eq_starSet_by_transfer {A B : Set α} : (⋆A : Set αS) = ⋆B ↔ A = B := by
  rw [subset_antisymm_iff, subset_antisymm_iff, starSet_subset_starSet_by_transfer,
    starSet_subset_starSet_by_transfer]

/-- **Exercises 4.5.1 and 3.10(5).** By transfer of the atomic sentence $`a \in A`: a standard
element belongs to $`{}^*A` if and only if it belongs to $`A`. -/
theorem of_mem_starSet_by_transfer {a : α} {A : Set α} : (of a : αS) ∈ ⋆A ↔ a ∈ A := by
  have key := transfer (αS := αS) (const a ∈' A)
  simpa [IsTrue] using key

end SetOperations

/-!
### Example 5: discreteness of the natural numbers

The book's natural numbers start at $`1`; Lean's start at $`0`, and the hypernatural numbers
of Chapter 3 are the enlargement of Lean's. So the least-element statement is given twice: as
$`x \ge 0` for the hypernaturals of this project, and as the book's $`x \ge 1` for the
enlargement of the positive naturals {name}`Goldblatt.posNat`.
-/

/-- **Section 4.1, example 5.** For a natural number $`n`, the sentence
$`(\forall x \in \mathbb N)(n \le x \le n + 1 \to x = n \lor x = n + 1)`. -/
def discreteSentence (n : ℕ) : Formula ℝ :=
  ∀' 0 ∈ ℕᵣ, ((const (n : ℝ) ≤' var 0 ⋏ var 0 ≤' const ((n : ℝ) + 1)) ⟹
    (var 0 =' const (n : ℝ) ⋎ var 0 =' const ((n : ℝ) + 1)))

/-- **Section 4.1, example 5.** The sentence is true: there is no natural number strictly
between $`n` and $`n + 1`. -/
theorem isTrue_discreteSentence (n : ℕ) : (discreteSentence n).IsTrue := by
  simp [discreteSentence, IsTrue]
  intro m h1 h2
  have h2' : m ≤ n + 1 := by exact_mod_cast h2
  rcases Nat.lt_or_ge n m with h | h
  · right
    have : m = n + 1 := by omega
    subst this
    push_cast
    rfl
  · left
    omega

/-- **Section 4.1, example 5, and Exercises 4.1.1, 4.4.1.** By transfer, no hypernatural number
lies strictly between $`n` and $`n + 1`:
$`(\forall x \in {}^*\mathbb N)(n \le x \le n + 1 \to x = n \lor x = n + 1)`. -/
theorem hyperNat_eq_or_eq_add_one (n : ℕ) {x : ℝ*} (hx : x ∈ ℕ*) (h1 : (n : ℝ*) ≤ x)
    (h2 : x ≤ n + 1) : x = n ∨ x = n + 1 := by
  have key := (transfer (αS := ℝ*) (discreteSentence n)).2 (isTrue_discreteSentence n)
  simp [discreteSentence, IsTrue] at key
  rcases key x hx h1 h2 with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- **Section 4.1, example 5.** The sentence $`(\forall x \in \mathbb N)(x \ge 0)`. -/
def natNonnegSentence : Formula ℝ := ∀' 0 ∈ ℕᵣ, const 0 ≤' var 0

/-- **Section 4.1, example 5, and Exercise 4.1.1.** By transfer, every hypernatural number is
at least $`0`, the least natural number. -/
theorem hyperNat_nonneg {x : ℝ*} (hx : x ∈ ℕ*) : 0 ≤ x := by
  have key := (transfer (αS := ℝ*) natNonnegSentence).2 (by simp [natNonnegSentence, IsTrue])
  simp [natNonnegSentence, IsTrue] at key
  exact key x hx

/-- **Section 4.1, example 5.** A nonstandard hypernatural number is greater than every natural
number, hence unlimited. The proof is by induction on the natural number, the step being the
discreteness statement obtained by transfer. -/
theorem natCast_lt_of_mem_hyperNat_of_nonstandard {x : ℝ*} (hx : x ∈ ℕ*)
    (hns : ∀ n : ℕ, x ≠ n) (n : ℕ) : (n : ℝ*) < x := by
  induction n with
  | zero =>
    have h0 := hns 0
    rw [Nat.cast_zero] at h0 ⊢
    exact lt_of_le_of_ne (hyperNat_nonneg hx) (Ne.symm h0)
  | succ n ih =>
    rw [Nat.cast_succ]
    by_contra hlt
    rcases hyperNat_eq_or_eq_add_one n hx ih.le (not_lt.1 hlt) with h | h
    · exact hns n h
    · exact hns (n + 1) (by rw [h, Nat.cast_succ])

/-- **Section 4.1, example 5.** The sentence
$`(\forall x \in \mathbb R)(x \in \mathbb N^{\ge 1} \leftrightarrow x \in \mathbb N \land
1 \le x)`, relating the book's natural numbers to Lean's. -/
def posNatSentence : Formula ℝ :=
  ∀' 0 ∈ univ, (var 0 ∈' posNat ⟺ (var 0 ∈' ℕᵣ ⋏ const 1 ≤' var 0))

/-- **Section 4.1, example 5.** By transfer, the enlargement of the book's set of natural numbers
$`\{1, 2, \dots\}` consists of the hypernatural numbers, in the sense of this project, that are
at least $`1`. -/
theorem starSet_posNat_by_transfer : ⋆posNat = {x : ℝ* | x ∈ ℕ* ∧ 1 ≤ x} := by
  ext x
  have key := (transfer (αS := ℝ*) posNatSentence).2 (by
    simpa [posNatSentence, IsTrue] using mem_posNat_iff)
  simp [posNatSentence, IsTrue, starSet_univ] at key
  simpa [hyperNat] using key x

/-- **Section 4.1, example 5.** The sentence $`(\forall x \in \mathbb N)(x \ge 1)`, with
$`\mathbb N` the book's set $`\{1, 2, \dots\}`. -/
def posNatLeastSentence : Formula ℝ := ∀' 0 ∈ posNat, const 1 ≤' var 0

/-- **Section 4.1, example 5, and Exercise 4.1.1.** The book's statement, literally: by transfer,
every member of the enlargement of $`\{1, 2, \dots\}` is at least $`1`, that is,
$`(\forall x \in {}^*\mathbb N)(x \ge 1)`. -/
theorem one_le_of_mem_starSet_posNat {x : ℝ*} (hx : x ∈ ⋆posNat) : 1 ≤ x := by
  have key := (transfer (αS := ℝ*) posNatLeastSentence).2 (by
    simp only [posNatLeastSentence, IsTrue, holds_all, holds_le, names_var, names_const]
    rintro _ ⟨n, rfl⟩ -
    exact ⟨1, (n : ℝ) + 1, rfl, by simp, by simp⟩)
  simp [posNatLeastSentence, IsTrue] at key
  exact key x hx

/-!
### Example 6: unbounded sets of reals
-/

/-- **Section 4.1, example 6.** For a set $`A` of reals and a real $`r`, the sentence
$`(\exists n \in A)(r < n)`. -/
def exceedsSentence (A : Set ℝ) (r : ℝ) : Formula ℝ := ∃' 0 ∈ A, const r <' var 0

/-- **Section 4.1, example 6.** The sentence says that some member of $`A` exceeds $`r`. -/
theorem isTrue_exceedsSentence (A : Set ℝ) (r : ℝ) :
    (exceedsSentence A r).IsTrue ↔ ∃ a ∈ A, r < a := by
  simp [exceedsSentence, IsTrue]

/-- **Section 4.1, example 6, and Exercise 4.4.1.** The star-transform is
$`(\exists n \in {}^*A)(r < n)`. -/
theorem isTrue_star_exceedsSentence (A : Set ℝ) (r : ℝ) :
    (exceedsSentence A r).star.IsTrue ↔ ∃ x ∈ ⋆A, (r : ℝ*) < x := by
  simp [exceedsSentence, IsTrue]

/-- **Section 4.1, example 6.** If the enlargement of a set of reals has an unlimited member,
one greater than every real, then the set is unbounded above: it has members greater than any
given real. Here transfer is used from the hyperreals back to the reals. -/
theorem exists_gt_of_exists_unlimited_mem_starSet {A : Set ℝ} {x : ℝ*} (hx : x ∈ ⋆A)
    (hbig : ∀ r : ℝ, (r : ℝ*) < x) (r : ℝ) : ∃ a ∈ A, r < a :=
  (isTrue_exceedsSentence A r).1 ((transfer _).1
    ((isTrue_star_exceedsSentence A r).2 ⟨x, hx, hbig r⟩))

/-- **Section 4.1, example 6.** The Eudoxus–Archimedes principle deduced from the existence of
an unlimited hypernatural number: since $`\omega \in {}^*\mathbb N` exceeds every real, every
real is exceeded by a natural number. -/
theorem exists_nat_gt_by_transfer (r : ℝ) : ∃ n : ℕ, r < n := by
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ :=
    exists_gt_of_exists_unlimited_mem_starSet (A := ℕᵣ) omega_mem_hyperNat real_lt_omega r
  exact ⟨n, hn⟩

/-!
## 4.4 Star-Transforms: examples

The two transforms displayed in Section 4.4 of the book, computed from the formal definition.
In both the stars on the order relation and on constants disappear, and what remains is a star
on the function symbols and on the set $`\mathbb Q`.
-/

/-- **Section 4.4, first displayed example.** For a function $`f` on the reals, the transform of
the formula $`\pi < f(x + 1)` is $`\pi < {}^*f(x + 1)`: it holds under a valuation exactly when
$`x` has a hyperreal value satisfying that inequality. -/
theorem holds_star_pi_lt_app (f : ℝ → ℝ) (v : Valuation ℝ*) :
    (const Real.pi <' app₁ f (var 0 +' const 1)).star.Holds v ↔
      ∃ x, v 0 = some x ∧ (Real.pi : ℝ*) < ⋆f (x + 1) := by
  simp [starMap₂_add]

/-- **Section 4.4, second displayed example.** The transform of $`\sin e^x \in \mathbb Q` is
$`\sin e^x \in {}^*\mathbb Q`, where the sine and the exponential are now the extended
functions. -/
theorem holds_star_sin_exp_mem_rat (v : Valuation ℝ*) :
    ((app₁ Real.sin (app₁ Real.exp (var 0))) ∈' ℚᵣ).star.Holds v ↔
      ∃ x, v 0 = some x ∧ ⋆Real.sin (⋆Real.exp x) ∈ ℚ* := by
  simp [hyperRat]

/-!
## 4.5 The Transfer Principle: examples

The illustrations of Section 4.5: the ordered-field properties of the hyperreals, the
enlargement of an interval, identities between extended functions, and a use of existential
transfer to bound a sequence.
-/

/-!
### The field axioms
-/

/-- **Section 4.5.** The sentence $`(\forall x, y \in \mathbb R)(x + y = y + x)`. -/
def addCommSentence : Formula ℝ := ∀' 0 ∈ univ, ∀' 1 ∈ univ, var 0 +' var 1 =' var 1 +' var 0

/-- **Section 4.5, and Exercise 4.4.1.** The star-transform of commutativity of addition is
commutativity of addition of hyperreals. -/
theorem isTrue_star_addCommSentence :
    addCommSentence.star.IsTrue ↔ ∀ x y : ℝ*, x + y = y + x := by
  simp [addCommSentence, IsTrue, starSet_univ, starMap₂_add, eq_comm]

/-- **Section 4.5.** By transfer, addition of hyperreals is commutative. -/
theorem hyperreal_add_comm_by_transfer (x y : ℝ*) : x + y = y + x :=
  isTrue_star_addCommSentence.1
    ((transfer _).2 (by simp [addCommSentence, IsTrue, add_comm])) x y

/-- **Section 4.5.** The sentence $`(\forall x \in \mathbb R)(x \cdot 1 = x)`. -/
def mulOneSentence : Formula ℝ := ∀' 0 ∈ univ, var 0 *' const 1 =' var 0

/-- **Section 4.5.** By transfer, $`x \cdot 1 = x` for every hyperreal $`x`. -/
theorem hyperreal_mul_one_by_transfer (x : ℝ*) : x * 1 = x := by
  have key := (transfer (αS := ℝ*) mulOneSentence).2 (by simp [mulOneSentence, IsTrue])
  simp [mulOneSentence, IsTrue, starSet_univ, starMap₂_mul, -mul_one] at key
  exact (key x).symm

/-- **Section 4.5.** The sentence
$`(\forall x, y \in \mathbb R)(x < y \lor x = y \lor y < x)`. -/
def trichotomySentence : Formula ℝ :=
  ∀' 0 ∈ univ, ∀' 1 ∈ univ, (var 0 <' var 1 ⋎ (var 0 =' var 1 ⋎ var 1 <' var 0))

/-- **Section 4.5, and Exercise 4.4.1.** The star-transform of trichotomy is trichotomy for
hyperreals. -/
theorem isTrue_star_trichotomySentence :
    trichotomySentence.star.IsTrue ↔ ∀ x y : ℝ*, x < y ∨ x = y ∨ y < x := by
  simp [trichotomySentence, IsTrue, starSet_univ, eq_comm]

/-- **Section 4.5.** By transfer, the order of the hyperreals is total. -/
theorem hyperreal_trichotomy_by_transfer (x y : ℝ*) : x < y ∨ x = y ∨ y < x :=
  isTrue_star_trichotomySentence.1
    ((transfer _).2 (by
      simpa [trichotomySentence, IsTrue, eq_comm] using fun a b : ℝ => lt_trichotomy a b)) x y

/-- **Section 4.5.** The sentence
$`(\forall x \in \mathbb R)[x \ne 0 \to (\exists y \in \mathbb R)\, x \cdot y = 1]`. -/
def inverseSentence : Formula ℝ :=
  ∀' 0 ∈ univ, (∼'(var 0 =' const 0) ⟹ (∃' 1 ∈ univ, var 0 *' var 1 =' const 1))

/-- **Section 4.5, and Exercise 4.4.1.** The star-transform of the existence of inverses. -/
theorem isTrue_star_inverseSentence :
    inverseSentence.star.IsTrue ↔ ∀ x : ℝ*, x ≠ 0 → ∃ y : ℝ*, x * y = 1 := by
  simp [inverseSentence, IsTrue, starSet_univ, starMap₂_mul, eq_comm]

/-- **Section 4.5.** By transfer, every nonzero hyperreal has a multiplicative inverse: no
ultrapower construction of the inverse is needed. -/
theorem hyperreal_exists_inverse_by_transfer {x : ℝ*} (hx : x ≠ 0) : ∃ y : ℝ*, x * y = 1 :=
  isTrue_star_inverseSentence.1 ((transfer _).2 (by
    simp only [inverseSentence, IsTrue, holds_all, holds_imp, holds_not, holds_eq, holds_ex,
      names_app₂, names_var, names_const, mem_univ, true_and, forall_const]
    intro a _ ha
    have ha0 : a ≠ 0 := fun h => ha ⟨a, 0, by simp, rfl, h⟩
    exact ⟨a⁻¹, by simp, 1, 1, ⟨a, a⁻¹, by simp, by simp, mul_inv_cancel₀ ha0⟩, rfl, rfl⟩)) x hx

/-!
### Intervals
-/

/-- **Section 4.5.** The sentence
$`(\forall x \in \mathbb R)(x \in [a, b] \leftrightarrow a \le x \le b)`. -/
def intervalSentence (a b : ℝ) : Formula ℝ :=
  ∀' 0 ∈ univ, (var 0 ∈' Icc a b ⟺ (const a ≤' var 0 ⋏ var 0 ≤' const b))

/-- **Section 4.5, and Exercises 4.5.1, 3.10(6).** By transfer, the enlargement of the closed
interval $`[a, b]` is the hyperreal interval with the same endpoints:
$`{}^*[a, b] = \{x \in {}^*\mathbb R : a \le x \le b\}`. -/
theorem starSet_Icc_by_transfer (a b : ℝ) : ⋆(Icc a b) = Icc (a : ℝ*) b := by
  ext x
  have key := (transfer (αS := ℝ*) (intervalSentence a b)).2
    (by simp [intervalSentence, IsTrue])
  simp [intervalSentence, IsTrue, starSet_univ] at key
  simpa using key x

/-!
### Identities between extended functions
-/

/-- **Section 4.5.** The sentence $`(\forall x \in \mathbb R)\, \sin(\pi - x) = \sin x`. -/
noncomputable def sinSentence : Formula ℝ :=
  ∀' 0 ∈ univ, app₁ Real.sin (const Real.pi -' var 0) =' app₁ Real.sin (var 0)

/-- **Section 4.5.** By transfer, $`\sin(\pi - x) = \sin x` for every hyperreal $`x`, where
$`\sin` now denotes the extended sine function. -/
theorem starMap_sin_pi_sub (x : ℝ*) :
    ⋆Real.sin ((Real.pi : ℝ*) - x) = ⋆Real.sin x := by
  have key := (transfer (αS := ℝ*) sinSentence).2
    (by simp [sinSentence, IsTrue, Real.sin_pi_sub])
  simp [sinSentence, IsTrue, starSet_univ] at key
  exact (key x).symm

/-- **Section 4.5.** The sentence
$`(\forall x \in \mathbb R)\, \cosh x + \sinh x = e^x`. -/
noncomputable def coshSinhSentence : Formula ℝ :=
  ∀' 0 ∈ univ, app₁ Real.cosh (var 0) +' app₁ Real.sinh (var 0) =' app₁ Real.exp (var 0)

/-- **Section 4.5.** By transfer, $`\cosh x + \sinh x = e^x` for every hyperreal $`x`. -/
theorem starMap_cosh_add_sinh (x : ℝ*) : ⋆Real.cosh x + ⋆Real.sinh x = ⋆Real.exp x := by
  have key := (transfer (αS := ℝ*) coshSinhSentence).2
    (by simp [coshSinhSentence, IsTrue, Real.cosh_add_sinh])
  simp [coshSinhSentence, IsTrue, starSet_univ, starMap₂_add] at key
  exact (key x).symm

/-- **Section 4.5.** The sentence
$`(\forall x, y \in \mathbb R^+)\, \log xy = \log x + \log y`. -/
noncomputable def logMulSentence : Formula ℝ :=
  ∀' 0 ∈ Ioi 0, ∀' 1 ∈ Ioi 0,
    app₁ Real.log (var 0 *' var 1) =' app₁ Real.log (var 0) +' app₁ Real.log (var 1)

/-- **Section 4.5.** By transfer, $`\log xy = \log x + \log y` for all positive hyperreals
$`x` and $`y`. -/
theorem starMap_log_mul {x y : ℝ*} (hx : 0 < x) (hy : 0 < y) :
    ⋆Real.log (x * y) = ⋆Real.log x + ⋆Real.log y := by
  have key := (transfer (αS := ℝ*) logMulSentence).2 (by
    simp only [logMulSentence, IsTrue, holds_all, holds_eq, names_app₁, names_app₂, names_var,
      mem_Ioi]
    intro a ha _ b hb _
    exact ⟨_, _, ⟨_, ⟨a, b, by simp, by simp, rfl⟩, rfl⟩,
      ⟨_, _, ⟨a, by simp, rfl⟩, ⟨b, by simp, rfl⟩, rfl⟩, Real.log_mul ha.ne' hb.ne'⟩)
  simp [logMulSentence, IsTrue, starMap₂_add, starMap₂_mul, starSet_Ioi_real] at key
  exact (key x hx y hy).symm

/-!
### Existential transfer: a bounded sequence

A sequence is a partial function on the reals whose domain is the set of natural numbers, and
its extension is the hypersequence of Section 3.13. If the hypersequence never takes an
unlimited value, the sequence is bounded: the unlimited number $`\omega` is a bound for the
hypersequence, so _some_ hyperreal is, and existential transfer turns that into a real bound.
The first step, replacing the nonstandard constant $`\omega` by an existentially quantified
variable, is essential, because a sentence containing $`\omega` is not the transform of anything
(see Section 4.7 below).
-/

/-- **Section 4.5.** A real sequence $`s`, as a partial function on the reals with domain the
natural numbers. -/
noncomputable def seqFun (s : ℕ → ℝ) : ℕᵣ → ℝ := fun x => s ⌊(x : ℝ)⌋₊

/-- **Section 4.5.** The partial function of a sequence takes the value $`s_n` at the natural number
$`n`. -/
theorem seqFun_natCast (s : ℕ → ℝ) (n : ℕ) : seqFun s ⟨n, n, rfl⟩ = s n := by
  simp [seqFun]

/-- **Section 4.5.** The formula $`(\forall n \in \mathbb N)(|s(n)| < y)`, with $`y` free (the
variable $`0`): "$`y` bounds the sequence". -/
noncomputable def boundedBody (s : ℕ → ℝ) : Formula ℝ :=
  ∀' 1 ∈ ℕᵣ, app₁ (fun a => |a|) (papp₁ ℕᵣ (seqFun s) (var 1)) <' var 0

/-- **Section 4.5.** The sentence
$`(\exists y \in \mathbb R)(\forall n \in \mathbb N)(|s(n)| < y)`. -/
noncomputable def boundedSentence (s : ℕ → ℝ) : Formula ℝ := ∃' 0 ∈ univ, boundedBody s

/-- **Section 4.5.** The sentence says that the sequence is bounded. -/
theorem isTrue_boundedSentence (s : ℕ → ℝ) :
    (boundedSentence s).IsTrue ↔ ∃ y : ℝ, ∀ n : ℕ, |s n| < y := by
  simp [boundedSentence, boundedBody, IsTrue, seqFun]

/-- **Section 4.5, and Exercise 4.4.1.** Substituting a hyperreal constant $`y` for the free
variable of the transform of $`(\forall n \in \mathbb N)(|s(n)| < y)` gives a defined sentence,
which says $`(\forall n \in {}^*\mathbb N)(|{}^*s(n)| < y)`, where $`{}^*s` is the
hypersequence extending $`s`. The constant need not be standard. -/
theorem isTrue_star_boundedBody_subst (s : ℕ → ℝ) (y : ℝ*) :
    ((boundedBody s).star.subst 0 y).IsDefined ∧
      (((boundedBody s).star.subst 0 y).IsTrue ↔ ∀ n ∈ ℕ*, |hyperSeq s n| < y) := by
  have hs : ∀ (n : ℝ*) (h : n ∈ ⋆ℕᵣ), starMapOn ℕᵣ (seqFun s) ⟨n, h⟩ = hyperSeq s n :=
    fun n h => starMapOn_range_natCast_eq_hyperSeq s (seqFun s) (seqFun_natCast s) ⟨n, h⟩
  simp only [boundedBody, IsTrue, IsDefined, Formula.holds_subst, Formula.defined_subst,
    Formula.star_all, holds_all,
    holds_star_lt, names_star_app₁, names_star_papp₁, Term.star_var, names_var,
    defined_all, defined_star_lt, defined_star_app₁, defined_star_papp₁,
    defined_var, closed_var, starMap_abs]
  refine ⟨by simp, ?_⟩
  constructor
  · intro H n hn
    obtain ⟨_, _, ⟨_, ⟨a, ha, ha', rfl⟩, rfl⟩, hb, hlt⟩ :=
      H n hn ⟨⟨trivial, fun _ => ⟨n, by simp, hn⟩⟩, trivial⟩
    simp at ha hb
    subst ha hb
    rw [hs] at hlt
    exact hlt
  · intro H n hn _
    exact ⟨_, y, ⟨_, ⟨n, by simp, hn, rfl⟩, rfl⟩, by simp, by rw [hs]; exact H n hn⟩

/-- **Section 4.5, and Exercise 4.4.1.** The star-transform of the boundedness sentence is
$`(\exists y \in {}^*\mathbb R)(\forall n \in {}^*\mathbb N)(|{}^*s(n)| < y)`, where
$`{}^*s` is the hypersequence extending $`s`. -/
theorem isTrue_star_boundedSentence (s : ℕ → ℝ) :
    (boundedSentence s).star.IsTrue ↔ ∃ y : ℝ*, ∀ n ∈ ℕ*, |hyperSeq s n| < y := by
  rw [boundedSentence, Formula.star_ex, isTrue_ex_iff]
  simp only [starSet_univ, mem_univ, true_and, (isTrue_star_boundedBody_subst s _).1,
    (isTrue_star_boundedBody_subst s _).2]

/-- **Sections 4.5 and 4.7.** The sentence
$`(\forall n \in {}^*\mathbb N)(|{}^*s(n)| < \omega)` of the book's discussion of existential
transfer. It is obtained exactly as the book obtains it: take the transform of the formula
$`(\forall n \in \mathbb N)(|s(n)| < y)` and substitute the constant $`\omega` for its free
variable $`y`. -/
noncomputable def omegaBoundSentence (s : ℕ → ℝ) : Formula ℝ* :=
  (boundedBody s).star.subst 0 ω

/-- **Sections 4.5 and 4.7.** The sentence
$`(\forall n \in {}^*\mathbb N)(|{}^*s(n)| < \omega)` is defined, and it says what it should:
every term of the hypersequence is smaller in absolute value than $`\omega`. -/
theorem isTrue_omegaBoundSentence (s : ℕ → ℝ) :
    (omegaBoundSentence s).IsDefined ∧
      ((omegaBoundSentence s).IsTrue ↔ ∀ n ∈ ℕ*, |hyperSeq s n| < ω) :=
  isTrue_star_boundedBody_subst s ω

/-- **Sections 4.5 and 4.7.** The sentence
$`(\forall n \in {}^*\mathbb N)(|{}^*s(n)| < \omega)` is a sentence of the language of
$`{}^*\mathfrak R`: its symbols are extensions and enlargements of standard ones, and
$`\omega`, like every hyperreal, is available as a constant. -/
theorem omegaBoundSentence_over (s : ℕ → ℝ) :
    (omegaBoundSentence s).Over (RelStructure.star ℝ) :=
  ((boundedBody s).star_over).subst 0 ω

/-- **Sections 4.5 and 4.7.** $`(\forall n \in {}^*\mathbb N)(|{}^*s(n)| < \omega)` is a
sentence: substituting $`\omega` has used up the only free variable. -/
theorem omegaBoundSentence_isSentence (s : ℕ → ℝ) : (omegaBoundSentence s).IsSentence := by
  ext x
  simp [omegaBoundSentence, boundedBody, Formula.subst, Formula.star, Formula.lt, rel₂, freeVars,
    Term.star, Term.subst, Term.vars, app₁, papp₁, Fin.exists_fin_two]

/-- **Section 4.5, removing the constant.** The step of the book's argument that trades the
nonstandard constant for a quantified variable: the sentence
$`(\forall n \in {}^*\mathbb N)(|{}^*s(n)| < \omega)` implies
$`(\exists y \in {}^*\mathbb R)(\forall n \in {}^*\mathbb N)(|{}^*s(n)| < y)`, which is the
star-transform of the boundedness sentence. This is the truth rule for the existential
quantifier, with $`\omega` as the witness. -/
theorem isTrue_star_boundedSentence_of_omegaBoundSentence (s : ℕ → ℝ)
    (h : (omegaBoundSentence s).IsTrue) : (boundedSentence s).star.IsTrue := by
  rw [boundedSentence, Formula.star_ex, isTrue_ex_iff]
  exact ⟨ω, by rw [starSet_univ]; trivial, (isTrue_omegaBoundSentence s).1, h⟩

/-- **Section 4.5, existential transfer.** If the hypersequence extending a real sequence takes
no unlimited value, then the sequence is bounded. The proof is the book's: the hypothesis makes
the sentence with the constant $`\omega` true; that sentence is not a transform, but it implies
the transform of the boundedness sentence, and transfer brings the latter down to the reals. -/
theorem bounded_of_hyperSeq_limited (s : ℕ → ℝ)
    (h : ∀ N ∈ ℕ*, ∃ r : ℝ, |hyperSeq s N| < (r : ℝ*)) : ∃ b : ℝ, ∀ n : ℕ, |s n| < b := by
  refine (isTrue_boundedSentence s).1 ((transfer _).1
    (isTrue_star_boundedSentence_of_omegaBoundSentence s ((isTrue_omegaBoundSentence s).2.2 ?_)))
  intro N hN
  obtain ⟨r, hr⟩ := h N hN
  exact hr.trans (real_lt_omega r)

/-!
### Exercise 4.5.1

Which of Exercises 3.10 can be proved by transfer? Every part that asserts something, that is,
all but part (4), which asks a question whose answer is no. In detail:

* (1), a finite set is its own enlargement: {name}`Goldblatt.starSet_of_finite_by_transfer`.
* (2), inclusion and equality of sets: {name}`Goldblatt.starSet_subset_starSet_by_transfer` and
  {name}`Goldblatt.starSet_eq_starSet_by_transfer`.
* (3), union, intersection, difference and the empty set:
  {name}`Goldblatt.starSet_union_by_transfer`, {name}`Goldblatt.starSet_inter_by_transfer`,
  {name}`Goldblatt.starSet_diff_by_transfer`, {name}`Goldblatt.starSet_empty_by_transfer`.
* (4), countable unions: a union of infinitely many sets is not described by a sentence, which
  would need an infinite disjunction, and the statement is in fact false
  ({name}`Goldblatt.starSet_iUnion_ne_iUnion_starSet`).
* (5), the standard members of an enlargement: {name}`Goldblatt.of_mem_starSet_by_transfer`.
* (6), closed intervals: {name}`Goldblatt.starSet_Icc_by_transfer`.
* (7), the hyperintegers are closed under addition, subtraction and multiplication:
  {lit}`hyperInt_closed_by_transfer` below, a case of the general statement
  {lit}`starMap₂_mem_starSet_by_transfer` that an enlargement is closed under the
  extension of any operation under which the set is closed.
* (8), the enlargement of the positive reals: {lit}`starSet_Ioi_zero_by_transfer`
  below.
-/

section Closure

variable {α αS : Type u} [StarType α αS]

/-- **Exercise 3.10(7) by transfer.** For a binary operation $`f` and a set $`A`, the sentence
$`(\forall x, y \in A)(f(x, y) \in A)`. -/
def closedSentence₂ (f : α → α → α) (A : Set α) : Formula α :=
  ∀' 0 ∈ A, ∀' 1 ∈ A, app₂ f (var 0) (var 1) ∈' A

/-- **Exercises 4.5.1 and 3.10(7).** By transfer, if a set is closed under a binary operation
then its enlargement is closed under the extended operation. -/
theorem starMap₂_mem_starSet_by_transfer {f : α → α → α} {A : Set α}
    (hA : ∀ a ∈ A, ∀ b ∈ A, f a b ∈ A) {x y : αS} (hx : x ∈ (⋆A : Set αS))
    (hy : y ∈ (⋆A : Set αS)) : ⋆f x y ∈ (⋆A : Set αS) := by
  have key := (transfer (αS := αS) (closedSentence₂ f A)).2 (by
    simp only [closedSentence₂, IsTrue, holds_all, holds_mem, names_app₂, names_var]
    intro a ha _ b hb _
    exact ⟨f a b, ⟨a, b, by simp, by simp, rfl⟩, hA a ha b hb⟩)
  simp [closedSentence₂, IsTrue] at key
  exact key x hx y hy

/-- **Exercise 3.10(7) by transfer.** For a unary operation $`f` and a set $`A`, the sentence
$`(\forall x \in A)(f(x) \in A)`. -/
def closedSentence₁ (f : α → α) (A : Set α) : Formula α := ∀' 0 ∈ A, app₁ f (var 0) ∈' A

/-- **Exercises 4.5.1 and 3.10(7).** By transfer, if a set is closed under a unary operation
then its enlargement is closed under the extended operation. -/
theorem starMap_mem_starSet_by_transfer {f : α → α} {A : Set α} (hA : ∀ a ∈ A, f a ∈ A) {x : αS}
    (hx : x ∈ (⋆A : Set αS)) : ⋆f x ∈ (⋆A : Set αS) := by
  have key := (transfer (αS := αS) (closedSentence₁ f A)).2 (by
    simp only [closedSentence₁, IsTrue, holds_all, holds_mem, names_app₁, names_var]
    intro a ha _
    exact ⟨f a, ⟨a, by simp, rfl⟩, hA a ha⟩)
  simp [closedSentence₁, IsTrue] at key
  exact key x hx

end Closure

/-- **Exercise 3.10(7) by transfer.** The sentence
$`(\forall x, y \in A)(x + y \in A)`. -/
def addClosedSentence (A : Set ℝ) : Formula ℝ :=
  ∀' 0 ∈ A, ∀' 1 ∈ A, (var 0 +' var 1) ∈' A

/-- **Exercises 4.5.1 and 3.10(7).** By transfer, if a set of reals is closed under addition
then so is its enlargement. -/
theorem add_mem_starSet_by_transfer {A : Set ℝ} (hA : ∀ a ∈ A, ∀ b ∈ A, a + b ∈ A) {x y : ℝ*}
    (hx : x ∈ ⋆A) (hy : y ∈ ⋆A) : x + y ∈ ⋆A := by
  have key := (transfer (αS := ℝ*) (addClosedSentence A)).2 (by
    simp only [addClosedSentence, IsTrue, holds_all, holds_mem, names_app₂, names_var]
    intro a ha _ b hb _
    exact ⟨a + b, ⟨a, b, by simp, by simp, rfl⟩, hA a ha b hb⟩)
  simp [addClosedSentence, IsTrue, starMap₂_add] at key
  exact key x hx y hy

/-- **Exercises 4.5.1 and 3.10(7).** By transfer, the hyperintegers are closed under addition,
subtraction, multiplication and negation: $`{}^*\mathbb Z` is a subring of the hyperreals. Each
closure property is the transform of the corresponding property of $`\mathbb Z`. -/
theorem hyperInt_closed_by_transfer {x y : ℝ*} (hx : x ∈ ℤ*) (hy : y ∈ ℤ*) :
    x + y ∈ ℤ* ∧ x - y ∈ ℤ* ∧ x * y ∈ ℤ* ∧ -x ∈ ℤ* := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact starMap₂_mem_starSet_by_transfer (f := fun a b : ℝ => a + b)
      (by rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩; exact ⟨m + n, by push_cast; rfl⟩) hx hy
  · exact starMap₂_mem_starSet_by_transfer (f := fun a b : ℝ => a - b)
      (by rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩; exact ⟨m - n, by push_cast; rfl⟩) hx hy
  · exact starMap₂_mem_starSet_by_transfer (f := fun a b : ℝ => a * b)
      (by rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩; exact ⟨m * n, by push_cast; rfl⟩) hx hy
  · exact starMap_mem_starSet_by_transfer (f := fun a : ℝ => -a)
      (by rintro _ ⟨m, rfl⟩; exact ⟨-m, by push_cast; rfl⟩) hx

/-- **Exercise 3.10(8) by transfer.** The sentence
$`(\forall x \in \mathbb R)(x \in \mathbb R^+ \leftrightarrow 0 < x)`. -/
def positiveSentence : Formula ℝ := ∀' 0 ∈ univ, (var 0 ∈' Ioi 0 ⟺ const 0 <' var 0)

/-- **Exercises 4.5.1 and 3.10(8).** By transfer, the enlargement of the set of positive reals
is the set of positive hyperreals: $`{}^*(\mathbb R^+) = ({}^*\mathbb R)^+`. -/
theorem starSet_Ioi_zero_by_transfer : ⋆(Ioi (0 : ℝ)) = Ioi (0 : ℝ*) := by
  ext x
  have key := (transfer (αS := ℝ*) positiveSentence).2 (by simp [positiveSentence, IsTrue])
  simp [positiveSentence, IsTrue, starSet_univ] at key
  simpa using key x

/-!
## 4.6 Justifying Transfer: examples

Section 4.6 of the book introduces the notation $`\varphi(x_1, \dots, x_p)` for a formula with
its free variables displayed, and $`\varphi(s_1, \dots, s_p)` for the result of substituting
constants. Its example is formalized here, and the theorem of Łoś
({name}`Goldblatt.Formula.isTrue_star_subst_ofSeq`) is applied to it: with a hyperreal
$`[r]` in place of the first variable, the transformed sentence is true exactly when its
instances at the terms $`r_n` are true for almost all $`n`.
-/

/-- **Section 4.6, substitution notation.** The book's example of the notation
$`\varphi(x_1, x_2)`: the formula $`(\exists y \in \mathbb Q)(x_1^2 + x_2^2 < y)`, with
$`x_1, x_2, y` the variables $`1, 2, 0`. -/
def sumSquaresFormula : Formula ℝ :=
  ∃' 0 ∈ ℚᵣ, (var 1 *' var 1) +' (var 2 *' var 2) <' var 0

/-- **Section 4.6, substitution notation.** The sentence $`\varphi(\pi, \sqrt 2)` obtained by
substituting constants for the free variables is
$`(\exists y \in \mathbb Q)(\pi^2 + (\sqrt 2)^2 < y)`. -/
theorem isTrue_sumSquaresFormula_subst (a b : ℝ) :
    ((sumSquaresFormula.subst 1 a).subst 2 b).IsTrue ↔ ∃ y ∈ ℚᵣ, a * a + b * b < y := by
  simp [sumSquaresFormula, IsTrue, holds_subst]

/-- **Section 4.6, the theorem of Łoś on the example.** For a sequence $`r` of reals and a real
$`b`, the sentence $`{}^*\varphi([r], b)`, which says
$`(\exists y \in {}^*\mathbb Q)([r]^2 + b^2 < y)`, is true if and only if
$`(\exists y \in \mathbb Q)(r_n^2 + b^2 < y)` for almost all $`n`. This is
{name}`Goldblatt.Formula.isTrue_star_subst_ofSeq` applied to $`\varphi(x_1, b)`. -/
theorem isTrue_star_sumSquaresFormula_subst_ofSeq (r : ℕ → ℝ) (b : ℝ) :
    (((sumSquaresFormula.subst 2 b).star : Formula ℝ*).subst 1 (ofSeq r)).IsTrue ↔
      ∀ᶠ n in hyperfilter ℕ, ∃ y ∈ ℚᵣ, r n * r n + b * b < y := by
  rw [isTrue_star_subst_ofSeq]
  refine eventually_congr (Eventually.of_forall fun n => ?_)
  simp [sumSquaresFormula, IsTrue, holds_subst]

/-- **Section 4.6, the example read in the hyperreals.** The sentence $`{}^*\varphi(c, b)`,
for a hyperreal $`c` and a real $`b`, says that $`c^2 + b^2` is less than some hyperrational
number. -/
theorem isTrue_star_sumSquaresFormula_subst (c : ℝ*) (b : ℝ) :
    (((sumSquaresFormula.subst 2 b).star : Formula ℝ*).subst 1 c).IsTrue ↔
      ∃ y ∈ ⋆ℚᵣ, c * c + (b : ℝ*) * b < y := by
  rw [Formula.star_subst]
  simp [sumSquaresFormula, IsTrue, holds_subst]
  rfl

/-- **Section 4.6, the theorem of Łoś on the example, both sides unfolded.** The square of a
hyperreal $`[r]` plus $`b^2` is below some hyperrational exactly when $`r_n^2 + b^2` is below
some rational for almost all $`n`. (Both sides are in fact always true; the point is that the
equivalence is an instance of the theorem of Łoś.) -/
theorem exists_hyperRat_gt_sumSquares_iff (r : ℕ → ℝ) (b : ℝ) :
    (∃ y ∈ ⋆ℚᵣ, ofSeq r * ofSeq r + (b : ℝ*) * b < y) ↔
      ∀ᶠ n in hyperfilter ℕ, ∃ y ∈ ℚᵣ, r n * r n + b * b < y :=
  (isTrue_star_sumSquaresFormula_subst (ofSeq r) b).symm.trans
    (isTrue_star_sumSquaresFormula_subst_ofSeq r b)

/-!
## 4.7 Extending Transfer

Section 4.7 of the book makes three points, each of which has a precise counterpart here.

_Other structures._ Nothing in the construction is special to the reals. The whole chapter was
carried out for an arbitrary type, and the transfer principle
{name}`Goldblatt.Formula.transfer` holds for the full structure on any type and its ultrapower.
The complex numbers are singled out below.

_Nonstandard constants._ The transfer principle is about star-transforms, and the constants of
a star-transform are standard. A sentence about the hyperreals that mentions a nonstandard
constant, such as $`\omega`, is not a transform. What remains true for such sentences is the
theorem of Łoś: replace each constant by a representing sequence, and the sentence is true
exactly when its instances are true at almost all indices
({name}`Goldblatt.Formula.isTrue_star_subst_ofSeq`). Such a sentence is still a sentence of the
language of the enlarged structure, since substituting a constant does not leave that language
({name}`Goldblatt.Formula.Over.subst`), and it may imply a transform, obtained by quantifying
the constant away; that is how the book uses them, and the example of Section 4.5 is revisited
below.

_Quantifying over sets._ The variables of the language range over elements, not over sets of
elements, so a statement such as Dedekind completeness, which begins "for every set of reals",
is not a sentence and cannot be transferred. What can be transferred is each of its instances:
for a fixed set $`A`, "if $`A` is bounded above then it has a least upper bound" is a sentence
with $`A` as a relation symbol. So every enlargement that is bounded above has a least upper
bound, while some sets of hyperreals that are bounded above have none. Consequently no formula
can say "Dedekind complete" of both structures at once
(the theorem {lit}`Goldblatt.no_formula_expresses_dedekind` below). The sets of the second
kind are therefore not enlargements; Chapter 11 of the book calls them external.
-/

/-- **Section 4.7, other structures.** The transfer principle for the complex numbers: a
sentence of the language of the full structure on $`\mathbb C` is true if and only if its
star-transform is true in the ultrapower of $`\mathbb C`. -/
theorem transfer_complex (φ : Formula ℂ) : (φ.star : Formula (Ultrapower ℂ)).IsTrue ↔ φ.IsTrue :=
  transfer φ

section Constants

variable {S : Type u} {α αS : Type u} [StarType α αS]

/-- **Section 4.7.** The constants that occur in a term. -/
def Term.consts : Term S → Set S
  | .var _ => ∅
  | .const s => {s}
  | .func _ _ ts => ⋃ i, (ts i).consts

/-- **Section 4.7.** The constants that occur in a formula. -/
def Formula.consts : Formula S → Set S
  | .rel _ ts => ⋃ i, (ts i).consts
  | .and φ ψ => φ.consts ∪ ψ.consts
  | .or φ ψ => φ.consts ∪ ψ.consts
  | .not φ => φ.consts
  | .imp φ ψ => φ.consts ∪ ψ.consts
  | .iff φ ψ => φ.consts ∪ ψ.consts
  | .all _ _ φ => φ.consts
  | .ex _ _ φ => φ.consts

/-- **Section 4.7.** Every constant of the star-transform of a term is standard. -/
theorem Term.consts_star_subset (t : Term α) :
    (t.star : Term αS).consts ⊆ range (of : α → αS) := by
  induction t with
  | var x => exact empty_subset _
  | const s => exact singleton_subset_iff.2 ⟨s, rfl⟩
  | func A f ts ih => exact iUnion_subset ih

/-- **Section 4.7, nonstandard constants.** Every constant of the star-transform of a formula is
standard. Hence a formula in which a nonstandard constant occurs is not the star-transform of
any formula, and the transfer principle says nothing about it. -/
theorem Formula.consts_star_subset (φ : Formula α) :
    (φ.star : Formula αS).consts ⊆ range (of : α → αS) := by
  induction φ with
  | rel P ts => exact iUnion_subset fun i => (ts i).consts_star_subset
  | and φ ψ ih₁ ih₂ | or φ ψ ih₁ ih₂ | imp φ ψ ih₁ ih₂ | iff φ ψ ih₁ ih₂ =>
    exact union_subset ih₁ ih₂
  | not φ ih => exact ih
  | all x P φ ih | ex x P φ ih => exact ih

end Constants

/-- **Sections 4.5 and 4.7, nonstandard constants.** The sentence
$`(\forall n \in {}^*\mathbb N)(|{}^*s(n)| < \omega)` belongs to the language of
$`{}^*\mathfrak R` ({name}`Goldblatt.omegaBoundSentence_over`), but it is not the star-transform
of any formula of the language of the reals, because the constant $`\omega` occurs in it. So
the transfer principle does not apply to it directly; one first passes to the existential
sentence it implies
({name}`Goldblatt.isTrue_star_boundedSentence_of_omegaBoundSentence`). -/
theorem omegaBoundSentence_ne_star (s : ℕ → ℝ) (φ : Formula ℝ) :
    φ.star ≠ omegaBoundSentence s := by
  intro h
  have hω : (ω : ℝ*) ∈ (omegaBoundSentence s).consts := by
    simp only [omegaBoundSentence, boundedBody, Formula.star, Formula.subst, Formula.lt, rel₂,
      Formula.consts, mem_iUnion, one_ne_zero, ite_false]
    exact ⟨1, by simp [Term.subst, Term.consts]⟩
  rw [← h] at hω
  obtain ⟨r, hr⟩ := φ.consts_star_subset hω
  exact (real_lt_omega r).ne hr

/-!
### Dedekind completeness
-/

/-- **Section 4.7.** For a set $`A` of reals, the sentence "if $`A` has an upper bound then it
has a least upper bound":
$$`(\exists b \in \mathbb R)(\forall x \in A)(x \le b) \to (\exists l \in \mathbb R)
[(\forall x \in A)(x \le l) \land (\forall b \in \mathbb R)((\forall x \in A)(x \le b) \to
l \le b)].`
The set $`A` enters as the bound of a quantifier, a symbol of the language; there is no
quantification over sets. -/
def lubSentence (A : Set ℝ) : Formula ℝ :=
  (∃' 0 ∈ univ, ∀' 1 ∈ A, var 1 ≤' var 0) ⟹
    (∃' 2 ∈ univ, ((∀' 1 ∈ A, var 1 ≤' var 2) ⋏
      (∀' 3 ∈ univ, ((∀' 1 ∈ A, var 1 ≤' var 3) ⟹ var 2 ≤' var 3))))

/-- **Section 4.7.** The sentence says what it should about $`A`. -/
theorem isTrue_lubSentence (A : Set ℝ) :
    (lubSentence A).IsTrue ↔
      ((∃ b : ℝ, ∀ x ∈ A, x ≤ b) →
        ∃ l : ℝ, (∀ x ∈ A, x ≤ l) ∧ ∀ b : ℝ, (∀ x ∈ A, x ≤ b) → l ≤ b) := by
  simp [lubSentence, IsTrue]

/-- **Section 4.7, and Exercise 4.4.1.** The star-transform says the same about the enlargement
$`{}^*A`, with bounds and least upper bound sought among the hyperreals. -/
theorem isTrue_star_lubSentence (A : Set ℝ) :
    (lubSentence A).star.IsTrue ↔
      ((∃ b : ℝ*, ∀ x ∈ ⋆A, x ≤ b) →
        ∃ l : ℝ*, (∀ x ∈ ⋆A, x ≤ l) ∧ ∀ b : ℝ*, (∀ x ∈ ⋆A, x ≤ b) → l ≤ b) := by
  simp [lubSentence, IsTrue, starSet_univ]

/-- **Section 4.7, completeness instance by instance.** By transfer, the enlargement of a
nonempty set of reals, if it is bounded above in the hyperreals, has a least upper bound in the
hyperreals. Each instance of Dedekind completeness transfers, since each is a sentence. -/
theorem exists_isLUB_starSet {A : Set ℝ} (hne : A.Nonempty) (hb : BddAbove (⋆A)) :
    ∃ l : ℝ*, IsLUB (⋆A) l := by
  have htrue : (lubSentence A).IsTrue := by
    rw [isTrue_lubSentence]
    intro hbdd
    obtain ⟨l, hl⟩ := Real.exists_isLUB hne hbdd
    exact ⟨l, hl.1, hl.2⟩
  obtain ⟨l, h1, h2⟩ := (isTrue_star_lubSentence A).1 ((transfer _).2 htrue) hb
  exact ⟨l, h1, h2⟩

/-- **Section 4.7, the completeness principle is not transferable.** The hyperreals are not
Dedekind complete: the set of standard reals is nonempty and bounded above, by $`\omega`, and
has no least upper bound. So the statement "every nonempty set that is bounded above has a least
upper bound", true of the reals, is false of the hyperreals; it quantifies over sets and is not
a sentence of the language. -/
theorem not_dedekindComplete_hyperreal :
    ∃ S : Set ℝ*, S.Nonempty ∧ BddAbove S ∧ ¬∃ l : ℝ*, IsLUB S l := by
  refine ⟨range ((↑) : ℝ → ℝ*), ⟨_, ⟨0, rfl⟩⟩, ⟨ω, ?_⟩, ?_⟩
  · rintro _ ⟨r, rfl⟩
    exact (real_lt_omega r).le
  · rintro ⟨l, hl⟩
    have hub : l - 1 ∈ upperBounds (range ((↑) : ℝ → ℝ*)) := by
      rintro _ ⟨r, rfl⟩
      have h := hl.1 ⟨r + 1, rfl⟩
      rw [Hyperreal.coe_add, Hyperreal.coe_one] at h
      linarith
    have := hl.2 hub
    linarith

/-- **Section 4.7, Dedekind completeness is not expressible.** No formula of the language of the
reals expresses Dedekind completeness uniformly, that is, in such a way that the formula says
"every nonempty set bounded above has a least upper bound" of the reals and its star-transform
says the same of the hyperreals. By the transfer principle the formula and its transform have
the same truth value, whereas completeness holds of the reals and fails of the hyperreals
({name}`Goldblatt.not_dedekindComplete_hyperreal`). The book's remark is that the completeness
statement, which quantifies over sets, is no sentence of the language; this theorem is the
provable form of that remark: whatever a formula says, it cannot be completeness on both
sides. -/
theorem no_formula_expresses_dedekind :
    ¬∃ φ : Formula ℝ,
      (φ.IsTrue ↔ ∀ S : Set ℝ, S.Nonempty → BddAbove S → ∃ l : ℝ, IsLUB S l) ∧
      ((φ.star : Formula ℝ*).IsTrue ↔
        ∀ S : Set ℝ*, S.Nonempty → BddAbove S → ∃ l : ℝ*, IsLUB S l) := by
  rintro ⟨φ, hR, hS⟩
  obtain ⟨S, hne, hb, hS'⟩ := not_dedekindComplete_hyperreal
  exact hS' (hS.1 ((transfer φ).2 (hR.2 fun _ h h' => Real.exists_isLUB h h')) S hne hb)

/-- **Section 4.7.** A set of hyperreals that is nonempty and bounded above but has no least
upper bound is not the enlargement of any set of reals: transfer would give it a least upper
bound. In particular the set of standard reals is not an enlargement, which is Exercise 4.2.1
again. -/
theorem ne_starSet_of_not_exists_isLUB {S : Set ℝ*} (hne : S.Nonempty) (hb : BddAbove S)
    (hS : ¬∃ l : ℝ*, IsLUB S l) (A : Set ℝ) : ⋆A ≠ S := by
  rintro rfl
  have hA : A.Nonempty := by
    by_contra hA
    rw [not_nonempty_iff_eq_empty.1 hA, starSet_empty] at hne
    exact not_nonempty_empty hne
  exact hS (exists_isLUB_starSet hA hb)

/-!
### What the following chapters use

The book closes the chapter by listing what the next chapters need: the hyperreals form an
ordered field containing the reals, there is an unlimited hypernatural number, whose reciprocal
is then a positive infinitesimal, and the transfer principle holds. The first is Mathlib's field
structure together with Section 3.7; the last is {name}`Goldblatt.Formula.transfer`; the middle
one is recorded here.
-/

/-- **Section 4.7.** There is a hypernatural number $`N` that is not a natural number. It is
greater than every real number, and its reciprocal is a positive infinitesimal: positive and
smaller than every positive real. -/
theorem exists_unlimited_hyperNat :
    ∃ N ∈ ℕ*, (∀ n : ℕ, N ≠ n) ∧ (∀ r : ℝ, (r : ℝ*) < N) ∧
      0 < N⁻¹ ∧ ∀ r : ℝ, 0 < r → N⁻¹ < (r : ℝ*) := by
  have hpos : (0 : ℝ*) < ω := by
    have := real_lt_omega 0
    rwa [Hyperreal.coe_zero] at this
  refine ⟨ω, omega_mem_hyperNat, omega_nonstandard_nat.2, real_lt_omega, inv_pos.2 hpos,
    fun r hr => ?_⟩
  have hr' : (0 : ℝ*) < r := Hyperreal.coe_pos.2 hr
  rw [inv_lt_comm₀ hpos hr', ← Hyperreal.coe_inv]
  exact real_lt_omega _

end Goldblatt
