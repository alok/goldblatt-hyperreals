import Goldblatt.Ch14_Enlargements.Collapse

/-!
# 14 (part 3). Łoś's Theorem: Section 14.3

This is the third of five parts of Chapter 14 (the overview is on the chapter page
{lit}`Goldblatt.Ch14_Enlargements`). It proves the theorem of Łoś for the bounded ultrapower
by induction on formulas, relative to an assumption about the terms that occur in the formula.
The assumption is discharged in part 4.
-/

noncomputable section

namespace Goldblatt

open ZFSet Filter
open scoped Classical

universe u v

/-!
## 14.3 Enlargements as Ultrapowers: Łoś's theorem for formulas

The transfer map of the ultrapower sends $`a` to $`{}^*a = [a^I]`, the collapse of the
constant function. That this map satisfies the transfer principle is a special case of a
statement about arbitrary functions of bounded rank, the theorem of Łoś: a formula holds of
the classes $`[f_1], \dots, [f_p]` in the new universe if and only if it holds of the values
$`f_1(i), \dots, f_p(i)` in the old one for almost all $`i`.

The proof is an induction on the formula. Atomic formulas are the two properties of the
collapse from part 2. Conjunction commutes with "almost all" for any filter; negation,
disjunction and implication do so because the filter is an ultrafilter. The quantifier step
uses the axiom of choice to select a witness at each index, and the bound of the quantifier to
see that the selected function has bounded rank.

In the language of Chapter 13 terms can be tuples and function values, and a term can be
undefined. To keep the induction on formulas separate from the treatment of terms, the theorem
is proved here for formulas whose terms satisfy the corresponding statement for terms
({lit}`BoundedUltrapower.TermLos`), which is immediate for variables and constants.
-/

namespace Formula

/-- Every term occurring in the formula, in an atomic subformula or as the bound of a
quantifier, satisfies $`P`. -/
def TermsSat (P : Term.{u} → Prop) : Formula.{u} → Prop
  | equal s t => P s ∧ P t
  | elem s t => P s ∧ P t
  | conj φ ψ => φ.TermsSat P ∧ ψ.TermsSat P
  | disj φ ψ => φ.TermsSat P ∧ ψ.TermsSat P
  | neg φ => φ.TermsSat P
  | imp φ ψ => φ.TermsSat P ∧ ψ.TermsSat P
  | biimp φ ψ => φ.TermsSat P ∧ ψ.TermsSat P
  | all _ τ φ => P τ ∧ φ.TermsSat P
  | ex _ τ φ => P τ ∧ φ.TermsSat P

/-- Every term of a formula of the language of $`\mathbb U` has its
constants in $`\mathbb U`. -/
theorem termsSat_of_admissible {U : ZFSet.{u}} {φ : Formula.{u}} {b : Set ℕ}
    (h : φ.Admissible U b) : φ.TermsSat fun t => t.Admissible U Set.univ := by
  induction φ generalizing b with
  | equal s t => exact ⟨h.1.mono (Set.subset_univ _), h.2.mono (Set.subset_univ _)⟩
  | elem s t => exact ⟨h.1.mono (Set.subset_univ _), h.2.mono (Set.subset_univ _)⟩
  | conj φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | disj φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | neg φ ih => exact ih h
  | imp φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | biimp φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | all x τ φ ih => exact ⟨h.1.mono (Set.subset_univ _), ih h.2⟩
  | ex x τ φ ih => exact ⟨h.1.mono (Set.subset_univ _), ih h.2⟩

end Formula

/-- For an ultrafilter, a bi-implication holds almost
everywhere exactly when the two sides hold almost everywhere together. -/
theorem _root_.Ultrafilter.eventually_iff_iff {α : Type*} (f : Ultrafilter α) {p q : α → Prop} :
    (∀ᶠ x in f, (p x ↔ q x)) ↔ ((∀ᶠ x in f, p x) ↔ ∀ᶠ x in f, q x) := by
  simp only [iff_iff_implies_and_implies, eventually_and, Ultrafilter.eventually_imp]

namespace BoundedUltrapower

variable {I : Type v} [Small.{u} I] {𝓕 : Ultrafilter I} {X : ZFSet.{u}}

variable (𝓕) in
/-- **Section 14.3, the transfer map.** $`{}^*a = [a^I]`, the collapse of the constant
function with value $`a`. -/
def star (hX : IsBaseSet X) (a : ZFSet.{u}) : ZFSet.{u} := col 𝓕 hX fun _ => a

variable (𝓕) in
/-- **Section 14.3, the statement of Łoś's theorem for a term.** For every assignment
of functions of bounded rank to the variables: the transformed term is defined at the collapsed
assignment if and only if the term is defined at almost all indices, and in that case its value
is the collapse of a function of bounded rank that almost everywhere equals the pointwise
value. -/
def TermLos (hX : IsBaseSet X) (t : Term.{u}) : Prop :=
  ∀ fs : ℕ → I → ZFSet.{u}, (∀ x, Bdd 𝓕 X (fs x)) →
    ((t.star (star 𝓕 hX)).Defined (superstructure (base 𝓕 X)) (fun x => col 𝓕 hX (fs x)) ↔
        ∀ᶠ i in 𝓕, t.Defined (superstructure X) fun x => fs x i) ∧
    ((∀ᶠ i in 𝓕, t.Defined (superstructure X) fun x => fs x i) →
      ∃ g, Bdd 𝓕 X g ∧ (∀ᶠ i in 𝓕, g i = t.val fun x => fs x i) ∧
        (t.star (star 𝓕 hX)).val (fun x => col 𝓕 hX (fs x)) = col 𝓕 hX g)

/-- Łoś's theorem for a variable. -/
theorem termLos_var (hX : IsBaseSet X) (n : ℕ) : TermLos 𝓕 hX (.var n) := fun fs hfs =>
  ⟨by simp, fun _ => ⟨fs n, hfs n, Eventually.of_forall fun _ => rfl, rfl⟩⟩

/-- Łoś's theorem for a constant from $`\mathbb U(X)`. -/
theorem termLos_const (hX : IsBaseSet X) {a : ZFSet.{u}} (ha : a ∈ superstructure X) :
    TermLos 𝓕 hX (.const a) := fun _ _ =>
  ⟨by simp, fun _ => ⟨fun _ => a, bdd_const ha, Eventually.of_forall fun _ => rfl, rfl⟩⟩

omit [Small.{u} I] in
/-- Changing an assignment of functions at one variable and then evaluating at an
index is the same as evaluating and then changing. -/
theorem update_apply (fs : ℕ → I → ZFSet.{u}) (x : ℕ) (h : I → ZFSet.{u}) (i : I) :
    (fun y => Function.update fs x h y i) = Function.update (fun y => fs y i) x (h i) := by
  funext y
  by_cases hy : y = x
  · subst hy; simp
  · simp [Function.update_of_ne hy]

/-- Changing an assignment of functions at one variable and then collapsing is the
same as collapsing and then changing. -/
theorem col_update (hX : IsBaseSet X) (fs : ℕ → I → ZFSet.{u}) (x : ℕ) (h : I → ZFSet.{u}) :
    (fun y => col 𝓕 hX (Function.update fs x h y)) =
      Function.update (fun y => col 𝓕 hX (fs y)) x (col 𝓕 hX h) := by
  funext y
  by_cases hy : y = x
  · subst hy; simp
  · simp [Function.update_of_ne hy]

omit [Small.{u} I] in
/-- Changing an assignment of functions of bounded rank at one variable, to a
function of bounded rank, gives such an assignment. -/
theorem bdd_update {fs : ℕ → I → ZFSet.{u}} (hfs : ∀ x, Bdd 𝓕 X (fs x)) (x : ℕ)
    {h : I → ZFSet.{u}} (hh : Bdd 𝓕 X h) : ∀ y, Bdd 𝓕 X (Function.update fs x h y) := fun y => by
  by_cases hy : y = x
  · subst hy; simpa using hh
  · simpa [Function.update_of_ne hy] using hfs y

/-- **Section 14.3, Łoś's theorem, the quantifier step.** If the theorem holds for the
bound $`\tau` and for $`\psi` at all assignments that differ at $`x`, then it holds for
$`(\exists x \in \tau)\psi`. From left to right a witness in $`\mathbb U(Y)` is the collapse of
a function; from right to left a witness is chosen at each index, and the resulting function is
of bounded rank because its values are members of the values of the bound. -/
theorem los_ex (hX : IsBaseSet X) {τ : Term.{u}} (hτ : TermLos 𝓕 hX τ) (x : ℕ)
    (ψ : Formula.{u}) {fs : ℕ → I → ZFSet.{u}} (hfs : ∀ x, Bdd 𝓕 X (fs x))
    (ih : ∀ h : I → ZFSet.{u}, Bdd 𝓕 X h →
      (Sat (superstructure (base 𝓕 X)) (fun y => col 𝓕 hX (Function.update fs x h y))
          (ψ.star (star 𝓕 hX)) ↔
        ∀ᶠ i in 𝓕, Sat (superstructure X) (fun y => Function.update fs x h y i) ψ)) :
    Sat (superstructure (base 𝓕 X)) (fun y => col 𝓕 hX (fs y))
        ((Formula.ex x τ ψ).star (star 𝓕 hX)) ↔
      ∀ᶠ i in 𝓕, Sat (superstructure X) (fun y => fs y i) (.ex x τ ψ) := by
  obtain ⟨hd, hv⟩ := hτ fs hfs
  simp only [Formula.star, Sat]
  constructor
  · rintro ⟨a, haW, hdef, hmem, hsat⟩
    have e := hd.1 hdef
    obtain ⟨g, hg, a1, a2⟩ := hv e
    rw [a2] at hmem
    obtain ⟨h, hh, hhg, rfl⟩ := exists_of_mem_col hX haW hmem
    rw [← col_update] at hsat
    have h4 := (ih h hh).1 hsat
    filter_upwards [e, a1, hhg, h4, hh.eventually_mem] with i h1 h2 h3 h4 h5
    exact ⟨h i, h5, h1, h2 ▸ h3, by rwa [update_apply] at h4⟩
  · intro hev
    obtain ⟨h, hh⟩ := Filter.skolem.1 hev
    have e : ∀ᶠ i in 𝓕, τ.Defined (superstructure X) fun y => fs y i :=
      hh.mono fun i hi => hi.2.1
    obtain ⟨g, hg, a1, a2⟩ := hv e
    have hmem : ∀ᶠ i in 𝓕, h i ∈ g i := by
      filter_upwards [hh, a1] with i h1 h2
      exact h2 ▸ h1.2.2.1
    have hbh : Bdd 𝓕 X h := bdd_of_eventually_mem hX hg (by
      filter_upwards [hh, hmem] with i h1 h2
      exact ⟨h1.1, h2⟩)
    refine ⟨col 𝓕 hX h, col_mem hX hbh, hd.2 e, ?_, ?_⟩
    · rw [a2]
      exact (col_mem_col_iff hX hbh hg).2 hmem
    · rw [← col_update]
      exact (ih h hbh).2 (hh.mono fun i hi => by rw [update_apply]; exact hi.2.2.2)

/-- A bounded universal quantifier is the negation of a bounded
existential quantifier of the negation. -/
theorem sat_all_iff_not_ex (V : ZFSet.{u}) (v : ℕ → ZFSet.{u}) (x : ℕ) (τ : Term.{u})
    (φ : Formula.{u}) : Sat V v (.all x τ φ) ↔ ¬ Sat V v (.ex x τ (.neg φ)) := by
  simp only [Sat, not_exists, not_and, not_not]

/-- **Section 14.3, Łoś's theorem relative to its terms.** For a formula all of
whose terms satisfy Łoś's theorem for terms, and functions $`f_1, \dots, f_p \in Z`,
$$`{}^*\varphi([f_1], \dots, [f_p]) \iff
\{i \in I : \varphi(f_1(i), \dots, f_p(i))\} \in \mathcal F.`
The proof is by induction on the formula. It is used twice: for formulas whose terms are
variables, where the hypothesis is immediate, and then, once tuples and function values have
been treated with the help of the first use, for all formulas. -/
theorem los_of_terms (hX : IsBaseSet X) (P : Term.{u} → Prop) (hP : ∀ t, P t → TermLos 𝓕 hX t) :
    ∀ (φ : Formula.{u}), φ.TermsSat P → ∀ fs : ℕ → I → ZFSet.{u}, (∀ x, Bdd 𝓕 X (fs x)) →
      (Sat (superstructure (base 𝓕 X)) (fun y => col 𝓕 hX (fs y)) (φ.star (star 𝓕 hX)) ↔
        ∀ᶠ i in 𝓕, Sat (superstructure X) (fun y => fs y i) φ) := by
  intro φ
  induction φ with
  | equal s t =>
    intro h fs hfs
    obtain ⟨hds, hvs⟩ := hP s h.1 fs hfs
    obtain ⟨hdt, hvt⟩ := hP t h.2 fs hfs
    simp only [Formula.star, Sat]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have e1 := hds.1 h1
      have e2 := hdt.1 h2
      obtain ⟨g1, hg1, a1, a2⟩ := hvs e1
      obtain ⟨g2, hg2, b1, b2⟩ := hvt e2
      rw [a2, b2] at h3
      filter_upwards [e1, e2, a1, b1, (col_eq_iff hX hg1 hg2).1 h3] with i c1 c2 c3 c4 c5
      exact ⟨c1, c2, by rw [← c3, ← c4, c5]⟩
    · intro hev
      have e1 := hev.mono fun i hi => hi.1
      have e2 := hev.mono fun i hi => hi.2.1
      obtain ⟨g1, hg1, a1, a2⟩ := hvs e1
      obtain ⟨g2, hg2, b1, b2⟩ := hvt e2
      refine ⟨hds.2 e1, hdt.2 e2, ?_⟩
      rw [a2, b2]
      refine (col_eq_iff hX hg1 hg2).2 ?_
      filter_upwards [hev, a1, b1] with i c1 c2 c3
      rw [c2, c3]
      exact c1.2.2
  | elem s t =>
    intro h fs hfs
    obtain ⟨hds, hvs⟩ := hP s h.1 fs hfs
    obtain ⟨hdt, hvt⟩ := hP t h.2 fs hfs
    simp only [Formula.star, Sat]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have e1 := hds.1 h1
      have e2 := hdt.1 h2
      obtain ⟨g1, hg1, a1, a2⟩ := hvs e1
      obtain ⟨g2, hg2, b1, b2⟩ := hvt e2
      rw [a2, b2] at h3
      filter_upwards [e1, e2, a1, b1, (col_mem_col_iff hX hg1 hg2).1 h3] with i c1 c2 c3 c4 c5
      exact ⟨c1, c2, by rw [← c3, ← c4]; exact c5⟩
    · intro hev
      have e1 := hev.mono fun i hi => hi.1
      have e2 := hev.mono fun i hi => hi.2.1
      obtain ⟨g1, hg1, a1, a2⟩ := hvs e1
      obtain ⟨g2, hg2, b1, b2⟩ := hvt e2
      refine ⟨hds.2 e1, hdt.2 e2, ?_⟩
      rw [a2, b2]
      refine (col_mem_col_iff hX hg1 hg2).2 ?_
      filter_upwards [hev, a1, b1] with i c1 c2 c3
      rw [c2, c3]
      exact c1.2.2
  | conj φ ψ ihφ ihψ =>
    intro h fs hfs
    simp only [Formula.star, Sat, ihφ h.1 fs hfs, ihψ h.2 fs hfs, eventually_and]
  | disj φ ψ ihφ ihψ =>
    intro h fs hfs
    simp only [Formula.star, Sat, ihφ h.1 fs hfs, ihψ h.2 fs hfs, Ultrafilter.eventually_or]
  | neg φ ih =>
    intro h fs hfs
    simp only [Formula.star, Sat, ih h fs hfs, Ultrafilter.eventually_not]
  | imp φ ψ ihφ ihψ =>
    intro h fs hfs
    simp only [Formula.star, Sat, ihφ h.1 fs hfs, ihψ h.2 fs hfs, Ultrafilter.eventually_imp]
  | biimp φ ψ ihφ ihψ =>
    intro h fs hfs
    simp only [Formula.star, Sat, ihφ h.1 fs hfs, ihψ h.2 fs hfs,
      Ultrafilter.eventually_iff_iff]
  | all x τ φ ih =>
    intro h fs hfs
    have key := los_ex hX (hP τ h.1) x (.neg φ) hfs fun k hk => by
      simp only [Formula.star, Sat, ih h.2 _ (bdd_update hfs x hk), Ultrafilter.eventually_not]
    rw [show (Formula.all x τ φ).star (star 𝓕 hX) =
      .all x (τ.star (star 𝓕 hX)) (φ.star (star 𝓕 hX)) from rfl, sat_all_iff_not_ex]
    simp only [sat_all_iff_not_ex, Ultrafilter.eventually_not]
    exact not_congr key
  | ex x τ φ ih =>
    intro h fs hfs
    exact los_ex hX (hP τ h.1) x φ hfs fun k hk => ih h.2 _ (bdd_update hfs x hk)

end BoundedUltrapower
end Goldblatt
