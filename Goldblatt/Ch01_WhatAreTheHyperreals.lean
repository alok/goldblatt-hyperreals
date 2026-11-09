import Mathlib

/-!
# 1. What Are the Hyperreals?

The first chapter of Goldblatt's book is an invitation rather than a development: it says
what an infinitesimal is supposed to be, recalls how such quantities were used long before
anyone could say what they were, and asks what a real number is, so that the same question
can later be asked about hyperreal numbers.  It contains no numbered theorems or exercises.

This page plays the same role for the formalization.  A _hyperreal_ is an element of an
ordered field $`{}^*\mathbb{R}` that extends the real field $`\mathbb{R}` and contains
numbers that are positive yet smaller than every positive real, together with their
reciprocals, which exceed every real.  Parts I to III of the project work in one concrete
such field, Mathlib's {name}`Hyperreal`, the ultrapower of $`\mathbb{R}` over a
nonprincipal ultrafilter on $`\mathbb{N}`; this is the construction of the book's Chapter 3.
The later chapters build on it the transfer principle, the calculus of limited, unlimited
and infinitesimal numbers, nonstandard treatments of convergence, continuity,
differentiation, integration and topology, internal sets and functions, and then the
general theory of enlargements with its applications.

The few Lean statements below are previews, proved directly from Mathlib, of phenomena that
the following chapters establish systematically.  Everything on this page lives in the
namespace {lit}`Goldblatt.Intro`, a sub-namespace of the project-wide {lit}`Goldblatt`.
This is a deliberate deviation from the project convention of a single namespace: it leaves
the official definitions of later chapters free to use the natural names.  Statements marked
as _illustrations_ are additions of this project and are not taken from the book.

## 1.1 Infinitely Small and Large

Section 1.1 fixes the vocabulary.  A number $`\varepsilon` is _infinitely small_ when
$`|\varepsilon| < 1/n` for every positive integer $`n`, and a number $`\omega` is
_infinitely large_ when $`|\omega| > n` for every positive integer $`n`.  The two notions
are exchanged by taking reciprocals, the real field has no nonzero number of the first kind
and no number of the second kind, and the point of the subject is that a larger ordered
field has both.
-/

namespace Goldblatt.Intro

open Hyperreal
open scoped ConditionallyCompleteLinearOrderedField

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Section 1.1, definition** (infinitely small).  An element $`x` of an ordered field is
infinitely small when $`|x| < 1/n` for every positive integer $`n`.  Zero is allowed here;
the book's _infinitesimals_ of Section 1.1 are the nonzero such elements.  This predicate is
only used on this page.  Mathlib, and with it the later chapters, expresses the same
condition through the Archimedean class of $`x`; the two agree by
{lit}`infinitelySmall_iff_archimedeanClassMk_pos` below. -/
def InfinitelySmall (x : K) : Prop :=
  ∀ n : ℕ, 0 < n → |x| < 1 / (n : K)

/-- **Section 1.1, definition** (infinitely large).  An element $`w` of an ordered field is
infinitely large when $`|w| > n` for every positive integer $`n`.  In Mathlib's language
this says that the Archimedean class of $`w` is negative; see
{lit}`infinitelyLarge_iff_archimedeanClassMk_neg` below. -/
def InfinitelyLarge (w : K) : Prop :=
  ∀ n : ℕ, 0 < n → (n : K) < |w|

/-- **Section 1.1** (reciprocal of an infinitesimal).  If $`\varepsilon \ne 0` is infinitely
small then $`1/\varepsilon` is infinitely large. -/
theorem InfinitelySmall.infinitelyLarge_inv {x : K} (hx : InfinitelySmall x) (h0 : x ≠ 0) :
    InfinitelyLarge x⁻¹ := by
  intro n hn
  have hn' : (0 : K) < n := Nat.cast_pos.mpr hn
  have hpos : 0 < |x| := abs_pos.mpr h0
  rw [abs_inv, lt_inv_comm₀ hn' hpos, ← one_div]
  exact hx n hn

/-- **Section 1.1** (reciprocal of an infinite number).  If $`\omega` is infinitely large
then $`1/\omega` is a nonzero infinitely small number. -/
theorem InfinitelyLarge.infinitelySmall_inv {w : K} (hw : InfinitelyLarge w) :
    w⁻¹ ≠ 0 ∧ InfinitelySmall w⁻¹ := by
  have h1 : (1 : K) < |w| := by simpa using hw 1 one_pos
  have hpos : 0 < |w| := zero_lt_one.trans h1
  refine ⟨inv_ne_zero (abs_pos.mp hpos), fun n hn => ?_⟩
  have hn' : (0 : K) < n := Nat.cast_pos.mpr hn
  rw [abs_inv, one_div, inv_lt_inv₀ hpos hn']
  exact hw n hn

/-- **Section 1.1** (an Archimedean field has no nonzero infinitesimals).  In an Archimedean
ordered field, in particular in $`\mathbb{R}`, the only infinitely small element is
$`0`. -/
theorem InfinitelySmall.eq_zero [Archimedean K] {x : K} (hx : InfinitelySmall x) : x = 0 := by
  by_contra h0
  obtain ⟨n, hn⟩ := exists_nat_gt |x⁻¹|
  have hn0 : 0 < n := by
    have : (0 : K) < n := (abs_nonneg _).trans_lt hn
    exact_mod_cast this
  exact lt_asymm hn (hx.infinitelyLarge_inv h0 n hn0)

/-- **Section 1.1** (an Archimedean field has no infinite elements).  In an Archimedean
ordered field, in particular in $`\mathbb{R}`, no element is infinitely large. -/
theorem not_infinitelyLarge [Archimedean K] (w : K) : ¬ InfinitelyLarge w := fun hw =>
  hw.infinitelySmall_inv.1 hw.infinitelySmall_inv.2.eq_zero

/-- **Section 1.1, definition** (agreement with Mathlib, illustration).  An element $`x` of an
ordered field is infinitely small exactly when its Archimedean class is positive, that is,
when $`n\,|x| < 1` for every natural number $`n`.  This is the form in which Mathlib states
that $`x` is infinitesimal, so the page-local predicate {name}`InfinitelySmall` coincides
with the notion used from Chapter 5 on. -/
theorem infinitelySmall_iff_archimedeanClassMk_pos (x : K) :
    InfinitelySmall x ↔ 0 < ArchimedeanClass.mk x := by
  rw [← ArchimedeanClass.mk_one, ArchimedeanClass.mk_lt_mk]
  simp only [abs_one, nsmul_eq_mul]
  constructor
  · intro h n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : K) < n := Nat.cast_pos.mpr hn
      have := h n hn
      rwa [lt_div_iff₀' hn'] at this
  · intro h n hn
    have hn' : (0 : K) < n := Nat.cast_pos.mpr hn
    rw [lt_div_iff₀' hn']
    exact h n

/-- **Section 1.1, definition** (agreement with Mathlib, illustration).  An element $`w` of an
ordered field is infinitely large exactly when its Archimedean class is negative, that is,
when $`n \cdot 1 < |w|` for every natural number $`n`.  This is the form in which Mathlib
states that $`w` is infinite (unlimited), so {name}`InfinitelyLarge` coincides with the
notion used from Chapter 5 on. -/
theorem infinitelyLarge_iff_archimedeanClassMk_neg (w : K) :
    InfinitelyLarge w ↔ ArchimedeanClass.mk w < 0 := by
  rw [← ArchimedeanClass.mk_one, ArchimedeanClass.mk_lt_mk]
  simp only [abs_one, nsmul_eq_mul, mul_one]
  constructor
  · intro h n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := h 1 one_pos
      simp only [Nat.cast_one, Nat.cast_zero] at this ⊢
      exact zero_lt_one.trans this
    · exact h n hn
  · exact fun h n _ => h n

end OrderedField

/-- The real number $`n`, embedded in the hyperreals, is the hyperreal natural number
$`n`. -/
theorem hyperreal_coe_natCast (n : ℕ) : ((n : ℝ) : ℝ*) = n := rfl

/-- **Section 1.1** (the hyperreals contain a nonzero infinitesimal).  The hyperreal
$`\varepsilon`, the class of the sequence $`(1/n)`, is nonzero and infinitely small. -/
theorem epsilon_infinitelySmall : (ε : ℝ*) ≠ 0 ∧ InfinitelySmall (ε : ℝ*) := by
  refine ⟨epsilon_ne_zero, fun n hn => ?_⟩
  rw [abs_of_pos epsilon_pos]
  have h : (0 : ℝ) < 1 / n := by positivity
  have h' : (ε : ℝ*) < ((1 / n : ℝ) : ℝ*) := epsilon_lt_of_pos h
  rwa [coe_div, coe_one, hyperreal_coe_natCast] at h'

/-- **Section 1.1** (the hyperreals contain an infinite number).  The hyperreal $`\omega`,
the class of the sequence $`(n)`, is infinitely large. -/
theorem omega_infinitelyLarge : InfinitelyLarge (ω : ℝ*) := by
  intro n _
  rw [abs_omega, ← hyperreal_coe_natCast]
  exact coe_lt_omega n

/-- **Section 1.1** (existence of a positive infinitesimal).  There is a hyperreal that is
positive and smaller than every positive real number. -/
theorem exists_pos_infinitesimal : ∃ e : ℝ*, 0 < e ∧ ∀ r : ℝ, 0 < r → e < r :=
  ⟨ε, epsilon_pos, fun _ => epsilon_lt_of_pos⟩

/-- **Section 1.1** (existence of an unlimited number).  There is a hyperreal that is larger
than every real number. -/
theorem exists_unlimited : ∃ w : ℝ*, ∀ r : ℝ, (r : ℝ*) < w :=
  ⟨ω, coe_lt_omega⟩

/-- **Section 1.1** (the reals are an ordered subfield of the hyperreals).  The canonical map
$`\mathbb{R} \to {}^*\mathbb{R}`, which {name}`Hyperreal.coeRingHom` packages as a
homomorphism of ordered rings, is strictly increasing and hence injective. -/
theorem hyperreal_coe_strictMono : StrictMono ((↑) : ℝ → ℝ*) := fun _ _ => coe_lt_coe.mpr

/-- **Section 1.1** (the extension is proper).  Some hyperreal is not a real number: the
embedding of $`\mathbb{R}` in $`{}^*\mathbb{R}` is not surjective. -/
theorem hyperreal_coe_not_surjective : ¬ Function.Surjective ((↑) : ℝ → ℝ*) := fun h => by
  obtain ⟨r, hr⟩ := h ω
  exact lt_irrefl _ (hr ▸ coe_lt_omega r)

/-!
## 1.2 Historical Background

Section 1.2 is a historical essay, and nothing in it is a theorem.  In outline: the Greek
geometers, Archimedes above all, found areas and volumes by imagining figures as made of
indivisible slices, but proved their results by the method of exhaustion, which avoids the
infinite.  In the seventeenth century Newton and Leibniz turned such heuristics into a
calculus; Leibniz in particular computed with differentials, treating a curve as a polygon
with infinitely many infinitely short sides and discarding higher-order infinitesimals at
the end of a calculation.  Euler manipulated infinitely large and small numbers with great
freedom and success.  Cauchy still spoke of infinitely small variable quantities when he
defined continuity, but the nineteenth-century programme that followed, culminating with
Weierstrass, replaced them by the static epsilon-delta definition of limit.  In 1960
Abraham Robinson showed, using tools from mathematical logic, that the older language can
be made fully rigorous: there are ordered fields extending the reals in which infinitesimals
exist and to which the true statements about the reals transfer.

The one computation the section displays is Leibniz's rule for the differential of a
product.  The difference between two successive values of $`xy` is
$`(x + dx)(y + dy) - xy = x\,dy + y\,dx + dx\,dy`, and the rule $`d(xy) = x\,dy + y\,dx`
results from dropping $`dx\,dy` as infinitely small in comparison with the other terms.
In an ordered field with infinitesimals the first step is an algebraic identity, and the
second has a precise meaning: relative to either differential, the dropped term is itself
infinitely small.

As an illustration that is not in the book, the same pattern differentiates $`x^2`: the
quotient of the increments for the infinitesimal increment $`\varepsilon` differs from
$`2x` only by $`\varepsilon`.  "Neglecting" the leftover infinitesimal becomes the operation
of taking the standard part, which is studied in Chapters 5 and 8.

The section ends with Robinson's hyperreal field and the transfer principle, and with a
warning about its scope: transfer applies to properties of a certain logical form, and
Dedekind completeness is not one of them.  The hyperreal field is _not_ Dedekind complete;
the set of reals inside it is bounded above and has no least upper bound.
-/

/-- **Section 1.2** (Newton and Leibniz; the increment of a product).  For any $`x`, $`y`
and increments $`dx`, $`dy`,
$$`(x + dx)(y + dy) - xy = x\,dy + y\,dx + dx\,dy .`
The book quotes this for Leibniz's differentials; as an identity it holds in every
commutative ring, and it is stated here in the hyperreals. -/
theorem leibniz_product_increment (x y dx dy : ℝ*) :
    (x + dx) * (y + dy) - x * y = x * dy + y * dx + dx * dy := by
  ring

/-- **Section 1.2** (Newton and Leibniz; the omitted term is comparatively infinitely small).
If $`dx` and $`dy` are nonzero and infinitely small, then the term $`dx\,dy` omitted from
Leibniz's product rule is infinitely small compared with each differential:
both $`dx\,dy/dx` and $`dx\,dy/dy` are infinitely small.  The book says only that the term
is infinitely small in comparison with the rest; this is the reading made precise here. -/
theorem leibniz_omitted_term_infinitelySmall {dx dy : ℝ*} (hdx : InfinitelySmall dx)
    (hdy : InfinitelySmall dy) (hx0 : dx ≠ 0) (hy0 : dy ≠ 0) :
    InfinitelySmall (dx * dy / dx) ∧ InfinitelySmall (dx * dy / dy) := by
  rw [mul_div_cancel_left₀ dy hx0, mul_div_cancel_right₀ dx hy0]
  exact ⟨hdy, hdx⟩

/-- **Illustration for Section 1.2** (the Leibnizian derivative of the square; an addition
of this project, not a computation from the book).  For a real $`x` and the infinitesimal $`\varepsilon`,
$$`\frac{(x+\varepsilon)^2 - x^2}{\varepsilon} = 2x + \varepsilon ,`
so the increment quotient is infinitely close to $`2x`. -/
theorem sq_increment_quotient (x : ℝ) :
    (((x : ℝ*) + ε) ^ 2 - (x : ℝ*) ^ 2) / ε = 2 * x + ε := by
  have h : (ε : ℝ*) ≠ 0 := epsilon_ne_zero
  field_simp
  ring

/-- **Illustration for Section 1.2** (the neglected term is infinitesimal; an addition of
this project).  The increment quotient of the
square at $`x` differs from the real number $`2x` by an infinitely small amount. -/
theorem sq_increment_quotient_sub_infinitelySmall (x : ℝ) :
    InfinitelySmall ((((x : ℝ*) + ε) ^ 2 - (x : ℝ*) ^ 2) / ε - 2 * x) := by
  rw [sq_increment_quotient, add_sub_cancel_left]
  exact epsilon_infinitelySmall.2

/-- **Section 1.2** (Robinson; the hyperreals are not Dedekind complete).  The book states this
without proof as its example of a property that does not transfer.  The set of real numbers,
viewed inside $`{}^*\mathbb{R}`, is nonempty and bounded above by $`\omega`, but it has no
least upper bound: if $`s` were one, then $`s - 1` would not be an upper bound, so
$`s - 1 < r` for some real $`r`, and then the real $`r + 1` would exceed $`s`. -/
theorem hyperreal_not_dedekind_complete :
    (Set.range ((↑) : ℝ → ℝ*)).Nonempty ∧ BddAbove (Set.range ((↑) : ℝ → ℝ*)) ∧
      ¬ ∃ s : ℝ*, IsLUB (Set.range ((↑) : ℝ → ℝ*)) s := by
  refine ⟨⟨_, 0, rfl⟩, ⟨ω, ?_⟩, ?_⟩
  · rintro _ ⟨r, rfl⟩
    exact (coe_lt_omega r).le
  · rintro ⟨s, hs⟩
    have hlt : s - 1 < s := sub_one_lt s
    obtain ⟨_, ⟨r, rfl⟩, hr⟩ := (lt_isLUB_iff hs).mp hlt
    have hle : ((r + 1 : ℝ) : ℝ*) ≤ s := hs.1 ⟨r + 1, rfl⟩
    rw [coe_add, coe_one] at hle
    linarith

/-!
## 1.3 What Is a Real Number?

Section 1.3 lists the usual answers to its title question: an infinite decimal, an element
of a complete ordered field, a Dedekind cut of rationals, an equivalence class of rational
Cauchy sequences.  The second answer is the axiomatic one, and it is legitimate because the
axioms are categorical: any two complete ordered fields are isomorphic.  The third and
fourth are constructions, which show that the axioms are consistent.  The hyperreals will
be obtained in Chapter 3 by a construction modelled on the fourth answer, with real
sequences in place of rational Cauchy sequences.

The section closes with the Eudoxus–Archimedes principle, that of two magnitudes the
smaller can be multiplied to exceed the larger.  It holds in $`\mathbb{R}` and is exactly
what excludes infinite and infinitesimal reals.  The hyperreal line is an ordered field in
which the principle fails.  That fits with the failure of Dedekind completeness announced in
Section 1.2 and proved above: a Dedekind complete ordered field is always Archimedean.
-/

/-- **Section 1.3, answer (2)** (Dedekind completeness of the reals).  Every nonempty set of
real numbers that is bounded above has a least upper bound. -/
theorem real_exists_isLUB {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddAbove S) :
    ∃ s : ℝ, IsLUB S s :=
  Real.exists_isLUB hne hbdd

/-- **Section 1.3, answer (2)** (complete ordered fields are isomorphic).  Any two complete
ordered fields are isomorphic as ordered fields.  A complete ordered field is rendered as a
field with a {name}`ConditionallyCompleteLinearOrder` that is a strict ordered ring; the
isomorphism is Mathlib's {name}`ConditionallyCompleteLinearOrderedField.inducedOrderRingIso`. -/
theorem completeOrderedField_iso (F G : Type*)
    [Field F] [ConditionallyCompleteLinearOrder F] [IsStrictOrderedRing F]
    [Field G] [ConditionallyCompleteLinearOrder G] [IsStrictOrderedRing G] :
    Nonempty (F ≃+*o G) :=
  ⟨ConditionallyCompleteLinearOrderedField.inducedOrderRingIso F G⟩

/-- **Section 1.3, answer (2)** (the isomorphism is unique).  Between two complete ordered
fields there is exactly one isomorphism of ordered fields, so a complete ordered field has
no symmetries and the identification with $`\mathbb{R}` is canonical. -/
theorem completeOrderedField_iso_unique (F G : Type*)
    [Field F] [ConditionallyCompleteLinearOrder F] [IsStrictOrderedRing F]
    [Field G] [ConditionallyCompleteLinearOrder G] [IsStrictOrderedRing G]
    (e₁ e₂ : F ≃+*o G) : e₁ = e₂ :=
  Subsingleton.elim e₁ e₂

/-- **Section 1.3** (the Eudoxus–Archimedes principle in the reals).  For a positive
real $`a` and any real $`b`, some natural multiple of $`a` exceeds $`b`.  The book's
principle is the case $`b > 0`; the Lean statement drops that hypothesis, which is not
needed. -/
theorem real_eudoxus_archimedes {a b : ℝ} (ha : 0 < a) : ∃ n : ℕ, b < n * a := by
  obtain ⟨n, hn⟩ := exists_nat_gt (b / a)
  exact ⟨n, (div_lt_iff₀ ha).mp hn⟩

/-- **Section 1.3** (every real is exceeded by an integer).  The consequence of the
Eudoxus–Archimedes principle singled out in the text. -/
theorem real_exists_nat_gt (r : ℝ) : ∃ n : ℕ, r < n :=
  exists_nat_gt r

/-- **Section 1.3** (the principle fails for the hyperreal line).  No integer multiple of the
positive hyperreal $`1` exceeds $`\omega`: for every natural number $`n`,
$`n \cdot 1 < \omega`. -/
theorem hyperreal_eudoxus_archimedes_fails : ∀ n : ℕ, (n : ℝ*) * 1 < ω := by
  intro n
  rw [mul_one, ← hyperreal_coe_natCast]
  exact coe_lt_omega n

/-- **Section 1.3** (the hyperreals are not Archimedean).  The ordered field of hyperreals
does not satisfy Mathlib's {name}`Archimedean` property, because $`\omega` exceeds every
natural number. -/
theorem hyperreal_not_archimedean : ¬ Archimedean ℝ* := fun _ =>
  not_infinitelyLarge (ω : ℝ*) omega_infinitelyLarge

/-!
## 1.4 Historical References

Section 1.4 is a reading list on the history sketched in Section 1.2 and has no mathematical
content to formalize.
-/

end Goldblatt.Intro
