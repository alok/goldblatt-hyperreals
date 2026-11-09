import Goldblatt.Ch04_Transfer.Language

/-!
# 4 (part 2). Transfer and the Theorem of Łoś: Sections 4.5 and 4.6

This is the second of three parts of Chapter 4 (the overview is on the chapter page
{lit}`Goldblatt.Ch04_Transfer`). It proves the theorem of Łoś for the language of Part 1 and
derives the transfer principle from it, as Section 4.6 of the book indicates. The book states
both results and leaves the proof of the first to the reader's faith; here it is carried out in
full, by induction on terms and formulas, from the almost-all toolkit of Chapter 3.

The order of the two sections is reversed relative to the book, because the transfer principle
of Section 4.5 is deduced from the theorem of Section 4.6.
-/

universe u

namespace Goldblatt

open Set Filter Function Ultrapower
open scoped Hyperreal

variable {α αS : Type u} [StarType α αS]

/-!
## 4.6 Justifying Transfer

The almost-all criterion of Chapter 3, by which equality, order, membership of an enlarged set
and enlarged relations were defined, holds for every formula: the star-transform of a formula is
true of classes of sequences exactly when the formula is true of their terms at almost all
indices. This is the theorem of Łoś.

To state it we assign to some of the variables not values but _sequences_ of values. Such an
assignment yields a valuation in the star type, by taking classes, and for each index $`n` a
valuation in the original type, by taking $`n`-th terms. The theorem has two halves, one for
definedness and one for truth, and they are proved together, since the truth condition of a
quantifier mentions definedness.
-/

/-- **Section 4.6.** An assignment of sequences to some of the variables: the data
$`r^1, \dots, r^p` of the theorem of Łoś, attached to the variables $`x_1, \dots, x_p`. -/
abbrev SeqValuation (α : Type u) : Type u := ℕ → Option (ℕ → α)

namespace SeqValuation

/-- **Section 4.6.** The valuation in the star type that gives each variable the class
$`[r^i]` of its sequence. -/
noncomputable def germ (r : SeqValuation α) : Valuation αS := fun x => (r x).map ofSeq

/-- **Section 4.6.** The valuation at the index $`n`, giving each variable the $`n`-th term
$`r^i_n` of its sequence. -/
def eval (r : SeqValuation α) (n : ℕ) : Valuation α := fun x => (r x).map fun s => s n

/-- **Section 4.6.** The assignment of constant sequences that corresponds to a valuation. -/
def const (v : Valuation α) : SeqValuation α := fun x => (v x).map fun a _ => a

theorem germ_update_some (r : SeqValuation α) (x : ℕ) (s : ℕ → α) :
    update (r.germ : Valuation αS) x (some (ofSeq s)) = germ (update r x (some s)) := by
  funext y
  by_cases h : y = x
  · subst h
    simp [germ]
  · simp [germ, update_of_ne h]

theorem germ_update_none (r : SeqValuation α) (x : ℕ) :
    update (r.germ : Valuation αS) x none = germ (update r x none) := by
  funext y
  by_cases h : y = x
  · subst h
    simp [germ]
  · simp [germ, update_of_ne h]

theorem eval_update_some (r : SeqValuation α) (x : ℕ) (s : ℕ → α) (n : ℕ) :
    update (r.eval n) x (some (s n)) = eval (update r x (some s)) n := by
  funext y
  by_cases h : y = x
  · subst h
    simp [eval]
  · simp [eval, update_of_ne h]

theorem eval_update_none (r : SeqValuation α) (x : ℕ) (n : ℕ) :
    update (r.eval n) x none = eval (update r x none) n := by
  funext y
  by_cases h : y = x
  · subst h
    simp [eval]
  · simp [eval, update_of_ne h]

@[simp]
theorem eval_const (v : Valuation α) (n : ℕ) : (const v).eval n = v := by
  funext x
  simp only [eval, const, Option.map_map]
  exact Option.map_id'

theorem germ_const (v : Valuation α) :
    ((const v).germ : Valuation αS) = fun x => (v x).map of := by
  funext x
  simp only [germ, const, Option.map_map]
  rfl

@[simp]
theorem germ_const_empty :
    ((const (Valuation.empty : Valuation α)).germ : Valuation αS) = Valuation.empty := rfl

/-- **Section 4.6.** Every valuation in the star type arises from an assignment of sequences:
choose a representing sequence for each value. -/
theorem exists_germ_eq (v : Valuation αS) : ∃ r : SeqValuation α, r.germ = v := by
  refine ⟨fun x => (v x).map (surjInv (ofSeq_surjective (α := α) (αS := αS))), ?_⟩
  funext x
  simp only [germ, Option.map_map]
  have : (ofSeq ∘ surjInv (ofSeq_surjective (α := α) (αS := αS))) = id :=
    funext fun y => surjInv_eq _ y
  rw [this]
  exact Option.map_id'

end SeqValuation

/-- **Section 4.6, tuples.** The step that handles a tuple of arguments. Suppose that
predicates $`N_i` on the star type obey the almost-all criterion, and that a predicate $`Q` on
tuples does too. Then so does the statement that some tuple satisfies all the $`N_i` coordinate
by coordinate and satisfies $`Q`. -/
theorem exists_tuple_iff_almostAll {m : ℕ} {N : Fin m → αS → Prop}
    {N' : Fin m → ℕ → α → Prop}
    (hN : ∀ i (s : ℕ → α), N i (ofSeq s) ↔ ∀ᶠ n in hyperfilter ℕ, N' i n (s n))
    {Q : (Fin m → αS) → Prop} {Q' : ℕ → (Fin m → α) → Prop}
    (hQ : ∀ q : Fin m → ℕ → α,
      Q (fun i => ofSeq (q i)) ↔ ∀ᶠ n in hyperfilter ℕ, Q' n fun i => q i n) :
    (∃ args, (∀ i, N i (args i)) ∧ Q args) ↔
      ∀ᶠ n in hyperfilter ℕ, ∃ args, (∀ i, N' i n (args i)) ∧ Q' n args := by
  constructor
  · rintro ⟨args, h1, h2⟩
    obtain ⟨q, rfl⟩ := Ultrapower.exists_rep_tuple (α := α) args
    have a1 := almostAll_forall_finite.2 fun i => (hN i (q i)).1 (h1 i)
    have a2 := (hQ q).1 h2
    filter_upwards [a1, a2] with n h1 h2
    exact ⟨fun i => q i n, h1, h2⟩
  · intro H
    obtain ⟨q, hq⟩ := exists_seq_of_almostAll_exists H
    exact ⟨fun i => ofSeq fun n => q n i, fun i => (hN i _).2 (hq.mono fun n hn => hn.1 i),
      (hQ _).2 (hq.mono fun n hn => hn.2)⟩

namespace Term

/-- **Section 4.6, the theorem of Łoś for terms.** The star-transform of a term, evaluated at
classes of sequences, names the class $`[s]` if and only if for almost all $`n` the term,
evaluated at the $`n`-th terms, names $`s_n`. -/
theorem names_star_germ (t : Term α) (r : SeqValuation α) (s : ℕ → α) :
    (t.star : Term αS).Names r.germ (ofSeq s) ↔
      ∀ᶠ n in hyperfilter ℕ, t.Names (r.eval n) (s n) := by
  induction t generalizing s with
  | var x =>
    simp only [star, names_var, SeqValuation.germ, SeqValuation.eval]
    cases r x with
    | none => simp only [Option.map_none, reduceCtorEq, almostAll_const]
    | some q => simp only [Option.map_some, Option.some.injEq, Ultrapower.ofSeq_eq_ofSeq]
  | const c =>
    simp only [star, names_const]
    exact Ultrapower.ofSeq_eq_ofSeq
  | func A f ts ih =>
    refine exists_tuple_iff_almostAll (fun i s => ih i s) fun q => ?_
    constructor
    · rintro ⟨h, H⟩
      exact (starMapOnN_ofSeq_eq_ofSeq h).1 H
    · intro H
      have h : (fun i => (ofSeq (q i) : αS)) ∈ starRel A :=
        starRel_ofSeq.2 (H.mono fun _ hn => hn.1)
      exact ⟨h, (starMapOnN_ofSeq_eq_ofSeq h).2 H⟩

/-- **Section 4.6.** Whether the star-transform of a term is closed at classes of sequences is
the same as whether the term is closed at any index: it depends only on which variables have
been assigned. -/
theorem closed_star_germ (t : Term α) (r : SeqValuation α) (n : ℕ) :
    (t.star : Term αS).Closed r.germ ↔ t.Closed (r.eval n) := by
  induction t with
  | var x =>
    simp only [star, closed_var, SeqValuation.germ, SeqValuation.eval]
    cases r x <;> simp
  | const c => rfl
  | func A f ts ih => simp only [star, closed_func, ih]

/-- **Section 4.6.** The star-transform of a term names something at classes of sequences if
and only if the term names something at almost all indices. -/
theorem denotes_star_germ (t : Term α) (r : SeqValuation α) :
    (t.star : Term αS).Denotes r.germ ↔ ∀ᶠ n in hyperfilter ℕ, t.Denotes (r.eval n) := by
  unfold Denotes
  rw [(ofSeq_surjective (α := α) (αS := αS)).exists, almostAll_exists_iff]
  exact exists_congr fun s => names_star_germ t r s

/-- **Section 4.6, the theorem of Łoś for definedness of terms.** The star-transform of a term
is defined at classes of sequences if and only if the term is defined at almost all indices. -/
theorem defined_star_germ (t : Term α) (r : SeqValuation α) :
    (t.star : Term αS).Defined r.germ ↔ ∀ᶠ n in hyperfilter ℕ, t.Defined (r.eval n) := by
  induction t with
  | var x => simp [star]
  | const c => simp [star]
  | func A f ts ih =>
    have hc : (∀ i, ((ts i).star : Term αS).Closed r.germ) ↔
        ∀ᶠ n in hyperfilter ℕ, ∀ i, (ts i).Closed (r.eval n) := by
      rw [almostAll_forall_finite]
      refine forall_congr' fun i => ?_
      rw [← almostAll_const (p := ((ts i).star : Term αS).Closed r.germ)]
      exact eventually_congr (Eventually.of_forall fun n => closed_star_germ (ts i) r n)
    have hd := denotes_star_germ (func A f ts) r
    simp only [defined_func, almostAll_and, almostAll_imp, almostAll_forall_finite]
    simp only [star] at hd ⊢
    rw [defined_func, hc, hd]
    simp only [ih, almostAll_forall_finite]

end Term

namespace Formula

/-- **Section 4.6, the theorem of Łoś.** For every formula $`\varphi` and every assignment of
sequences $`r^1, \dots, r^p` to variables, the star-transform $`{}^*\varphi` is defined at the
classes $`[r^1], \dots, [r^p]` if and only if $`\varphi` is defined at
$`r^1_n, \dots, r^p_n` for almost all $`n`, and $`{}^*\varphi([r^1], \dots, [r^p])` is true if
and only if $`\varphi(r^1_n, \dots, r^p_n)` is true for almost all $`n`. The two halves are
proved together by induction on the formula. -/
theorem los (φ : Formula α) (r : SeqValuation α) :
    ((φ.star : Formula αS).Defined r.germ ↔ ∀ᶠ n in hyperfilter ℕ, φ.Defined (r.eval n)) ∧
      ((φ.star : Formula αS).Holds r.germ ↔ ∀ᶠ n in hyperfilter ℕ, φ.Holds (r.eval n)) := by
  induction φ generalizing r with
  | rel P ts =>
    constructor
    · simp only [star, defined_rel, almostAll_forall_finite, Term.defined_star_germ]
    · exact exists_tuple_iff_almostAll (fun i s => Term.names_star_germ (ts i) r s)
        fun q => starRel_ofSeq
  | and φ ψ ih₁ ih₂ =>
    simp only [star, defined_and, holds_and, almostAll_and, ih₁ r, ih₂ r, and_self]
  | or φ ψ ih₁ ih₂ =>
    simp only [star, defined_or, holds_or, almostAll_and, almostAll_or, ih₁ r, ih₂ r, and_self]
  | not φ ih =>
    simp only [star, defined_not, holds_not, almostAll_not, ih r, and_self]
  | imp φ ψ ih₁ ih₂ =>
    simp only [star, defined_imp, holds_imp, almostAll_and, almostAll_imp, ih₁ r, ih₂ r,
      and_self]
  | iff φ ψ ih₁ ih₂ =>
    simp only [star, defined_iff, holds_iff, almostAll_and, almostAll_iff, ih₁ r, ih₂ r,
      and_self]
  | all x P φ ih =>
    constructor
    · simp only [star, defined_all, SeqValuation.germ_update_none, (ih _).1,
        SeqValuation.eval_update_none]
    · simp only [star, holds_all]
      rw [(ofSeq_surjective (α := α) (αS := αS)).forall, almostAll_forall_iff]
      refine forall_congr' fun s => ?_
      rw [SeqValuation.germ_update_some, (ih _).1, (ih _).2, ofSeq_mem_starSet, almostAll_imp,
        almostAll_imp]
      simp only [SeqValuation.eval_update_some]
  | ex x P φ ih =>
    constructor
    · simp only [star, defined_ex, SeqValuation.germ_update_none, (ih _).1,
        SeqValuation.eval_update_none]
    · simp only [star, holds_ex]
      rw [(ofSeq_surjective (α := α) (αS := αS)).exists, almostAll_exists_iff]
      refine exists_congr fun s => ?_
      rw [SeqValuation.germ_update_some, (ih _).1, (ih _).2, ofSeq_mem_starSet, almostAll_and,
        almostAll_and]
      simp only [SeqValuation.eval_update_some]

/-- **Section 4.6, the theorem of Łoś, truth.** $`{}^*\varphi([r^1], \dots, [r^p])` is true if
and only if $`\varphi(r^1_n, \dots, r^p_n)` is true for almost all $`n`. -/
theorem holds_star_germ (φ : Formula α) (r : SeqValuation α) :
    (φ.star : Formula αS).Holds r.germ ↔ ∀ᶠ n in hyperfilter ℕ, φ.Holds (r.eval n) :=
  (los φ r).2

/-- **Section 4.6, the theorem of Łoś, definedness.** $`{}^*\varphi([r^1], \dots, [r^p])` is
defined if and only if $`\varphi(r^1_n, \dots, r^p_n)` is defined for almost all $`n`. -/
theorem defined_star_germ (φ : Formula α) (r : SeqValuation α) :
    (φ.star : Formula αS).Defined r.germ ↔ ∀ᶠ n in hyperfilter ℕ, φ.Defined (r.eval n) :=
  (los φ r).1

/-- **Section 4.6, the theorem of Łoś in the book's notation.** With
$`[\![ \varphi(r^1, \dots, r^p) ]\!] = \{n : \varphi(r^1_n, \dots, r^p_n) \text{ is true}\}`,
the sentence $`{}^*\varphi([r^1], \dots, [r^p])` is true if and only if that set of indices
belongs to the ultrafilter. -/
theorem holds_star_germ_iff_mem (φ : Formula α) (r : SeqValuation α) :
    (φ.star : Formula αS).Holds r.germ ↔ {n | φ.Holds (r.eval n)} ∈ hyperfilter ℕ :=
  holds_star_germ φ r

/-- **Section 4.6, the theorem of Łoś with one free variable.** For a formula $`\varphi(x)`
and a sequence $`r`, the sentence $`{}^*\varphi([r])`, obtained by substituting the constant
$`[r]` for $`x`, is true if and only if the sentence $`\varphi(r_n)` is true for almost all
$`n`. -/
theorem isTrue_star_subst_ofSeq (φ : Formula α) (x : ℕ) (r : ℕ → α) :
    ((φ.star : Formula αS).subst x (ofSeq r)).IsTrue ↔
      ∀ᶠ n in hyperfilter ℕ, (φ.subst x (r n)).IsTrue := by
  simp only [IsTrue, holds_subst]
  have h := holds_star_germ (αS := αS) φ (update (fun _ => none) x (some r))
  rw [← SeqValuation.germ_update_some] at h
  simp only [← SeqValuation.eval_update_some] at h
  exact h

/-- **Section 4.6, the atomic cases.** The almost-all criterion for an enlarged relation
(Section 3.14) is the theorem of Łoś for an atomic formula whose terms are variables. -/
theorem holds_star_rel_var {k : ℕ} (P : Set (Fin k → α)) (r : Fin k → ℕ → α) :
    (fun i => (ofSeq (r i) : αS)) ∈ starRel P ↔
      ∀ᶠ n in hyperfilter ℕ, (fun i => r i n) ∈ P :=
  starRel_ofSeq

end Formula

/-!
## 4.5 The Transfer Principle

A sentence has no free variables, so no sequences need be assigned and the set of indices at
which it is true is everything or nothing. The theorem of Łoś then says that the star-transform
of a sentence is true exactly when the sentence is. That is the transfer principle. The same
argument gives a version with parameters: a formula is true of standard elements exactly when
its star-transform is true of their copies.

The two directions of transfer for a quantified sentence are the forms used in practice.
_Universal transfer_: what holds for all members of a set holds for all members of its
enlargement. _Existential transfer_: if the enlargement of a set has a member with a property,
the set itself has one.
-/

namespace Formula

/-- **Section 4.5, the transfer principle.** A sentence $`\varphi` of the language of the full
structure is true if and only if its star-transform $`{}^*\varphi` is true in the enlarged
structure. The book states this for defined sentences; it holds, with the truth conditions of
Section 4.3, whether or not the sentence is defined. No hypothesis that $`\varphi` is a sentence
is needed either, since truth is evaluated under the empty valuation. -/
theorem transfer (φ : Formula α) : (φ.star : Formula αS).IsTrue ↔ φ.IsTrue := by
  have h := holds_star_germ (αS := αS) φ (SeqValuation.const Valuation.empty)
  simp only [SeqValuation.germ_const_empty, SeqValuation.eval_const, almostAll_const] at h
  exact h

/-- **Section 4.5, the transfer principle, definedness.** A sentence is defined if and only if
its star-transform is: transfer applies to exactly the same sentences on both sides. -/
theorem transfer_defined (φ : Formula α) : (φ.star : Formula αS).IsDefined ↔ φ.IsDefined := by
  have h := defined_star_germ (αS := αS) φ (SeqValuation.const Valuation.empty)
  simp only [SeqValuation.germ_const_empty, SeqValuation.eval_const, almostAll_const] at h
  exact h

/-- **Section 4.5, transfer with parameters.** A formula is true of standard elements
$`a_1, \dots, a_p` if and only if its star-transform is true of their copies
$`{}^*a_1, \dots, {}^*a_p`. -/
theorem holds_star_of (φ : Formula α) (v : Valuation α) :
    (φ.star : Formula αS).Holds (fun x => (v x).map of) ↔ φ.Holds v := by
  have h := holds_star_germ (αS := αS) φ (SeqValuation.const v)
  simp only [SeqValuation.germ_const, SeqValuation.eval_const, almostAll_const] at h
  exact h

/-- **Section 4.5, transfer with parameters, definedness.** A formula is defined at standard
elements if and only if its star-transform is defined at their copies. -/
theorem defined_star_of (φ : Formula α) (v : Valuation α) :
    (φ.star : Formula αS).Defined (fun x => (v x).map of) ↔ φ.Defined v := by
  have h := defined_star_germ (αS := αS) φ (SeqValuation.const v)
  simp only [SeqValuation.germ_const, SeqValuation.eval_const, almostAll_const] at h
  exact h

/-- **Section 4.5, universal transfer.** If $`\varphi(s)` is true for every $`s \in P` for which
it is defined, then $`{}^*\varphi(x)` is true for every $`x \in {}^*P` for which it is defined:
a property that holds for all members of $`P` holds for all members of $`{}^*P`. -/
theorem universal_transfer {x : ℕ} {P : Set α} {φ : Formula α}
    (h : ∀ s ∈ P, (φ.subst x s).IsDefined → (φ.subst x s).IsTrue) :
    ∀ y ∈ (⋆P : Set αS), ((φ.star : Formula αS).subst x y).IsDefined →
      ((φ.star : Formula αS).subst x y).IsTrue :=
  isTrue_all_iff.1 ((transfer (αS := αS) (all x P φ)).2 (isTrue_all_iff.2 h))

/-- **Section 4.5, existential transfer.** If there is some $`y \in {}^*P` for which
$`{}^*\varphi(y)` is defined and true, then there is some $`s \in P` for which $`\varphi(s)` is
defined and true: if a member of the enlargement has a property, so does a member of the
set. -/
theorem existential_transfer {x : ℕ} {P : Set α} {φ : Formula α}
    (h : ∃ y ∈ (⋆P : Set αS), ((φ.star : Formula αS).subst x y).IsDefined ∧
      ((φ.star : Formula αS).subst x y).IsTrue) :
    ∃ s ∈ P, (φ.subst x s).IsDefined ∧ (φ.subst x s).IsTrue :=
  isTrue_ex_iff.1 ((transfer (αS := αS) (ex x P φ)).1 (isTrue_ex_iff.2 h))

/-- **Section 4.5.** Transfer of a standard instance: for a standard element $`s`, the sentence
$`{}^*\varphi({}^*s)` is true if and only if $`\varphi(s)` is. -/
theorem isTrue_star_subst_of (φ : Formula α) (x : ℕ) (s : α) :
    ((φ.star : Formula αS).subst x (of s)).IsTrue ↔ (φ.subst x s).IsTrue := by
  rw [← star_subst]
  exact transfer _

end Formula

end Goldblatt
