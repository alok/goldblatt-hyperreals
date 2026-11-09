import Goldblatt.Ch03_Ultrapower.Enlargement

/-!
# 3 (part 3). Extension of Functions and Relations: Sections 3.11 to 3.16

This is the third of three parts of Chapter 3 (the overview is on the chapter page
{lit}`Goldblatt.Ch03_Ultrapower`). It extends functions, partial functions and sequences to the
ultrapower, enlarges relations of any finite arity, proves the transfer of single quantifiers
that Chapter 4 builds on, and closes with what can be said about the uniqueness of the
hyperreals.
-/

universe u v w

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## 3.11 Extending Functions

A function $`f` between standard types extends to the ultrapowers by acting on sequences
termwise: $`{}^*f([r]) = [f \circ r]`. This is well defined because sequences that agree at an
index have the same image at that index, and it obeys the almost-all criterion. In Lean the
extension is {lit}`starMap f`, written {lit}`⋆f`; it is Mathlib's {name}`Filter.Germ.map`.
-/

section Extension

variable {α αS : Type u} {β βS : Type v} {γ γS : Type w}
  [StarType α αS] [StarType β βS] [StarType γ γS]

/-- **Section 3.11, well-definedness of extension.**
$`[\![ r = r' ]\!] \subseteq [\![ f \circ r = f \circ r' ]\!]`. -/
theorem agreementSet_subset_agreementSet_comp (f : α → β) (r r' : ℕ → α) :
    agreementSet r r' ⊆ agreementSet (f ∘ r) (f ∘ r') :=
  fun _ hn => congrArg f hn

/-- **Section 3.11, well-definedness of extension.** If $`r \equiv r'` then
$`f \circ r \equiv f \circ r'`. -/
theorem SeqEquiv.comp_left {r r' : ℕ → α} (h : r ≡ᵤ r') (f : α → β) : f ∘ r ≡ᵤ f ∘ r' :=
  mem_hyperfilter_of_superset h (agreementSet_subset_agreementSet_comp f r r')

/-- **Section 3.11, definition of the extension.** $`{}^*f([r]) = [f \circ r]`. -/
theorem starMap_ofSeq (f : α → β) (r : ℕ → α) : ⋆f (ofSeq r : αS) = (ofSeq (f ∘ r) : βS) := by
  change StarType.equiv.symm (Germ.map f (StarType.equiv (ofSeq r : αS))) = _
  rw [equiv_ofSeq]
  rfl

/-- **Section 3.11**, for real functions: $`{}^*f([r_n]) = [f(r_n)]`. -/
theorem starMap_hyperreal_ofSeq (f : ℝ → ℝ) (r : ℕ → ℝ) :
    ⋆f (Hyperreal.ofSeq r) = Hyperreal.ofSeq fun n => f (r n) := rfl

/-- **Section 3.11, almost-all criterion for extensions.** $`{}^*f([r]) = [s]` if and only if
$`f(r_n) = s_n` for almost all $`n`. -/
theorem starMap_ofSeq_eq_ofSeq {f : α → β} {r : ℕ → α} {s : ℕ → β} :
    ⋆f (ofSeq r : αS) = (ofSeq s : βS) ↔ ∀ᶠ n in hyperfilter ℕ, f (r n) = s n := by
  rw [starMap_ofSeq]
  exact Ultrapower.ofSeq_eq_ofSeq

/-- **Section 3.11.** The sine function extends to all hyperreals, with
$`{}^*\sin([r_n]) = [\sin(r_n)]`. -/
example (r : ℕ → ℝ) : ⋆Real.sin (Hyperreal.ofSeq r) = Hyperreal.ofSeq fun n => Real.sin (r n) :=
  rfl

/-!
## 3.12 Exercises on Extensions

The extension agrees with the original function on standard elements, preserves injectivity and
surjectivity, and commutes with composition. The extension of the absolute value is the
absolute value of the hyperreals, the extension of a characteristic function is the
characteristic function of the enlargement, and functions of several arguments extend in the
same termwise way.
-/

/-- **Exercise 3.12(1).** $`{}^*f` agrees with $`f` on standard elements:
$`{}^*f({}^*a) = {}^*(f(a))`. -/
theorem starMap_of (f : α → β) (a : α) : ⋆f (of a : αS) = (of (f a) : βS) :=
  starMap_ofSeq f fun _ => a

/-- **Exercise 3.12(1)**, for real functions: $`{}^*f(r) = f(r)` for real $`r`. -/
theorem starMap_coe (f : ℝ → ℝ) (r : ℝ) : ⋆f (r : ℝ*) = ((f r : ℝ) : ℝ*) := rfl

/-- **Exercise 3.12(2).** If $`f` is injective, so is $`{}^*f`. -/
theorem starMap_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (⋆f : αS → βS) := by
  intro x y h
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := α) y
  rw [starMap_ofSeq, starMap_ofSeq, Ultrapower.ofSeq_eq_ofSeq] at h
  exact Ultrapower.ofSeq_eq_ofSeq.2 (h.mono fun n hn => hf hn)

/-- **Exercise 3.12(2).** $`{}^*f` is injective if and only if $`f` is. -/
theorem starMap_injective_iff {f : α → β} :
    Function.Injective (⋆f : αS → βS) ↔ Function.Injective f :=
  ⟨fun h a b hab => of_injective (αS := αS) (h (by rw [starMap_of, starMap_of, hab])),
    starMap_injective⟩

/-- **Exercise 3.12(2).** The answer to the book's question: if $`f` is surjective, so is
$`{}^*f`. Given a class $`[s]`, choose for each $`n` a preimage of $`s_n`. -/
theorem starMap_surjective {f : α → β} (hf : Function.Surjective f) :
    Function.Surjective (⋆f : αS → βS) := by
  intro y
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  obtain ⟨r, hr⟩ := exists_seq_of_almostAll_exists (Eventually.of_forall fun n => hf (s n))
  exact ⟨ofSeq r, starMap_ofSeq_eq_ofSeq.2 hr⟩

/-- **Exercise 3.12(2).** $`{}^*f` is surjective if and only if $`f` is. -/
theorem starMap_surjective_iff {f : α → β} :
    Function.Surjective (⋆f : αS → βS) ↔ Function.Surjective f := by
  refine ⟨fun h b => ?_, starMap_surjective⟩
  obtain ⟨x, hx⟩ := h (of b)
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [starMap_ofSeq] at hx
  obtain ⟨n, hn⟩ := (ofSeq_eq_of.1 hx).exists
  exact ⟨r n, hn⟩

/-- **Exercise 3.12, composition.** The extension of a composite is the composite of the
extensions. -/
theorem starMap_comp (g : β → γ) (f : α → β) :
    (⋆(g ∘ f) : αS → γS) = ⋆g ∘ (⋆f : αS → βS) := by
  funext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [Function.comp_apply, starMap_ofSeq, starMap_ofSeq, starMap_ofSeq]
  rfl

/-- **Exercise 3.12, composition.** $`{}^*(g \circ f)(x) = {}^*g({}^*f(x))`. -/
theorem starMap_starMap (g : β → γ) (f : α → β) (x : αS) :
    (⋆g (⋆f x : βS) : γS) = ⋆(g ∘ f) x := by
  rw [starMap_comp (βS := βS)]
  rfl

/-- **Exercise 3.12, identity.** The extension of the identity is the identity. -/
theorem starMap_id : (⋆(id : α → α) : αS → αS) = id := by
  funext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [starMap_ofSeq]
  rfl

/-- **Exercise 3.12(3), the definition by cases.** The absolute value of a hyperreal $`x` is
$`x` if $`x > 0`, is $`0` if $`x = 0`, and is $`-x` if $`x < 0`. The absolute value of the
hyperreals used in this project is Mathlib's, the supremum of $`x` and $`-x`; this lemma shows
that it is the function the exercise defines. -/
theorem hyperreal_abs_cases (x : ℝ*) : |x| = if 0 < x then x else if x = 0 then 0 else -x := by
  split_ifs with h₁ h₂
  · exact abs_of_pos h₁
  · rw [h₂, abs_zero]
  · exact abs_of_neg (lt_of_le_of_ne (not_lt.1 h₁) h₂)

/-- **Exercise 3.12(3).** The absolute value of the hyperreals, which by
{name}`Goldblatt.hyperreal_abs_cases` is the one defined by cases from the order, satisfies
$`|[r_n]| = [|r_n|]`: it is the extension of the real absolute value. -/
theorem starMap_abs (x : ℝ*) : ⋆(fun a : ℝ => |a|) x = |x| :=
  (Germ.abs_def x).symm

/-- **Exercise 3.12(3).** The absolute value on the hyperreals extends the one on the reals. -/
theorem ofReal_abs (r : ℝ) : ((|r| : ℝ) : ℝ*) = |(r : ℝ*)| := Hyperreal.coe_abs r

/-- **Exercise 3.12(4).** The extension of the characteristic function of $`A` is the
characteristic function of $`{}^*A`. -/
theorem starMap_indicator (A : Set ℝ) (x : ℝ*) :
    ⋆(A.indicator (1 : ℝ → ℝ)) x = (⋆A).indicator (1 : ℝ* → ℝ*) x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  by_cases h : Hyperreal.ofSeq r ∈ ⋆A
  · rw [indicator_of_mem h, Pi.one_apply, ← ofSeq_one, starMap_hyperreal_ofSeq, ofSeq_eq_ofSeq_iff]
    exact (hyperreal_ofSeq_mem_starSet.1 h).mono fun n hn => by simp [indicator_of_mem hn]
  · rw [indicator_of_notMem h, ← ofSeq_zero, starMap_hyperreal_ofSeq, ofSeq_eq_ofSeq_iff]
    exact (ofSeq_notMem_starSet.1 h).mono fun n hn => by simp [indicator_of_notMem hn]

/-- **Section 3.11.** The extension of a function maps the enlargement of a set onto the
enlargement of its image: $`{}^*(f[A]) = {}^*f[{}^*A]`. -/
theorem starSet_image (f : α → β) (A : Set α) :
    (⋆(f '' A) : Set βS) = (⋆f : αS → βS) '' ⋆A := by
  ext y
  constructor
  · intro hy
    obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
    have h : ∀ᶠ n in hyperfilter ℕ, ∃ a, a ∈ A ∧ f a = s n :=
      (ofSeq_mem_starSet (r := s) (A := f '' A)).1 hy
    obtain ⟨r, hr⟩ := exists_seq_of_almostAll_exists h
    exact ⟨ofSeq r, ofSeq_mem_starSet.2 (hr.mono fun n hn => hn.1),
      starMap_ofSeq_eq_ofSeq.2 (hr.mono fun n hn => hn.2)⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
    rw [starMap_ofSeq]
    exact ofSeq_mem_starSet.2 ((ofSeq_mem_starSet.1 hx).mono fun n hn => mem_image_of_mem f hn)

/-- **Section 3.11.** The enlargement of the range of $`f` is the range of $`{}^*f`. -/
theorem starSet_range (f : α → β) : (⋆(range f) : Set βS) = range (⋆f : αS → βS) := by
  rw [← image_univ, starSet_image, starSet_univ, image_univ]

/-- **Section 3.11.** The enlargement of a preimage is the preimage of the enlargement under
the extension. -/
theorem starSet_preimage (f : α → β) (B : Set β) :
    (⋆(f ⁻¹' B) : Set αS) = (⋆f : αS → βS) ⁻¹' ⋆B := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [mem_preimage, starMap_ofSeq, ofSeq_mem_starSet, ofSeq_mem_starSet]
  rfl

/-- **Section 3.11.** The extension of a function maps $`{}^*A` into $`{}^*B` whenever the
function maps $`A` into $`B`. -/
theorem starMap_mem_starSet {f : α → β} {A : Set α} {B : Set β} (h : MapsTo f A B)
    {x : αS} (hx : x ∈ ⋆A) : (⋆f x : βS) ∈ ⋆B := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [starMap_ofSeq]
  exact ofSeq_mem_starSet.2 ((ofSeq_mem_starSet.1 hx).mono fun n hn => h hn)

/-- **Exercise 3.12(5).** The extension of a function of two arguments acts termwise:
$`{}^*f([r], [s]) = [f(r_n, s_n)]`. -/
theorem starMap₂_ofSeq (f : α → β → γ) (r : ℕ → α) (s : ℕ → β) :
    ⋆f (ofSeq r : αS) (ofSeq s : βS) = (ofSeq fun n => f (r n) (s n) : γS) := by
  change StarType.equiv.symm (Germ.map₂ f (StarType.equiv (ofSeq r : αS))
    (StarType.equiv (ofSeq s : βS))) = _
  rw [equiv_ofSeq, equiv_ofSeq]
  rfl

/-- **Exercise 3.12(5).** The extension of a function of two arguments agrees with the function
on standard elements. -/
theorem starMap₂_of (f : α → β → γ) (a : α) (b : β) :
    ⋆f (of a : αS) (of b : βS) = (of (f a b) : γS) :=
  starMap₂_ofSeq f (fun _ => a) fun _ => b

/-- **Exercise 3.12(5), almost-all criterion.** $`{}^*f([r], [s]) = [t]` if and only if
$`f(r_n, s_n) = t_n` for almost all $`n`. -/
theorem starMap₂_ofSeq_eq_ofSeq {f : α → β → γ} {r : ℕ → α} {s : ℕ → β} {t : ℕ → γ} :
    ⋆f (ofSeq r : αS) (ofSeq s : βS) = (ofSeq t : γS) ↔
      ∀ᶠ n in hyperfilter ℕ, f (r n) (s n) = t n := by
  rw [starMap₂_ofSeq]
  exact Ultrapower.ofSeq_eq_ofSeq

/-- **Exercise 3.12(5).** Addition of hyperreals is the extension of addition of reals. -/
theorem starMap₂_add (x y : ℝ*) : ⋆(fun a b : ℝ => a + b) x y = x + y := rfl

/-- **Exercise 3.12(5).** Multiplication of hyperreals is the extension of multiplication of
reals. -/
theorem starMap₂_mul (x y : ℝ*) : ⋆(fun a b : ℝ => a * b) x y = x * y := rfl

/-- **Exercise 3.12(5).** The maximum of two hyperreals is the extension of the maximum of
reals. -/
theorem starMap₂_max (x y : ℝ*) : ⋆(fun a b : ℝ => max a b) x y = max x y :=
  (Germ.max_def x y).symm

/-- **Exercise 3.12(5), tuples.** The class of a tuple of sequences: a finite tuple of elements
of the ultrapower is turned into a single element of the ultrapower of the type of tuples, by
choosing a representing sequence for each coordinate. The index type is required to be finite,
as every arity in the book is: then the result does not depend on the choice
({lit}`Ultrapower.tuple_ofSeq`), whereas for an infinite index type it would. -/
noncomputable def Ultrapower.tuple {ι : Type*} [Finite ι] (x : ι → αS) : Ultrapower (ι → α) :=
  Germ.ofFun fun n i => Quotient.out (StarType.equiv (x i)) n

/-- **Exercise 3.12(5), tuples.** For a finite index type, the tuple of the classes of
sequences $`r^1, \dots, r^k` is the class of the sequence of tuples
$`n \mapsto (r^1_n, \dots, r^k_n)`. -/
theorem Ultrapower.tuple_ofSeq {ι : Type*} [Finite ι] (r : ι → ℕ → α) :
    Ultrapower.tuple (fun i => (ofSeq (r i) : αS)) = ofSeq fun n i => r i n := by
  refine Germ.coe_eq.2 ?_
  have h : ∀ i, ∀ᶠ n in hyperfilter ℕ,
      Quotient.out (StarType.equiv (ofSeq (r i) : αS)) n = r i n := fun i =>
    Germ.coe_eq.1 ((Quotient.out_eq _).trans (equiv_ofSeq (r i)))
  filter_upwards [almostAll_forall_finite.2 h] with n hn
  funext i
  exact hn i

/-- **Exercise 3.12(5), tuples.** A tuple of standard elements is the standard tuple. -/
theorem Ultrapower.tuple_of {ι : Type*} [Finite ι] (a : ι → α) :
    Ultrapower.tuple (fun i => (of (a i) : αS)) = of a :=
  Ultrapower.tuple_ofSeq fun i _ => a i

/-- **Exercise 3.12(5), tuples.** Every tuple of elements of the ultrapower is a tuple of
classes of sequences. -/
theorem Ultrapower.exists_rep_tuple {ι : Type*} (x : ι → αS) :
    ∃ r : ι → ℕ → α, x = fun i => ofSeq (r i) :=
  ⟨fun i => Quotient.out (StarType.equiv (x i)), funext fun i =>
    ((Equiv.symm_apply_eq _).2 (Quotient.out_eq (StarType.equiv (x i)))).symm⟩

/-- **Exercise 3.15(1).** For a finite index type, tuples of elements of the ultrapower
correspond exactly to elements of the ultrapower of tuples: $`({}^*\mathbb R)^k` is
$`{}^*(\mathbb R^k)`. -/
noncomputable def Ultrapower.tupleEquiv {ι : Type*} [Finite ι] :
    (ι → αS) ≃ Ultrapower (ι → α) where
  toFun := Ultrapower.tuple
  invFun y i := ⋆(fun a : ι → α => a i) y
  left_inv x := by
    obtain ⟨r, rfl⟩ := Ultrapower.exists_rep_tuple (α := α) x
    rw [Ultrapower.tuple_ofSeq]
    funext i
    exact starMap_ofSeq _ _
  right_inv y := by
    obtain ⟨s, rfl⟩ := ofSeq_surjective (α := ι → α) y
    simp only [starMap_ofSeq]
    exact Ultrapower.tuple_ofSeq fun i n => s n i

/-- **Exercise 3.12(5).** The extension of a function of several arguments, the arguments being
indexed by a finite type $`\iota`: apply the function termwise to the tuple of representing
sequences. Finiteness of the index type is a hypothesis of the definition, because only then is
the value independent of the representing sequences ({lit}`Goldblatt.starMapN_ofSeq`). -/
noncomputable def starMapN {ι : Type*} [Finite ι] (f : (ι → α) → β) (x : ι → αS) : βS :=
  ⋆f (Ultrapower.tuple x)

/-- **Exercise 3.12(5).** For finitely many arguments,
$`{}^*f([r^1], \dots, [r^k]) = [f(r^1_n, \dots, r^k_n)]`. -/
theorem starMapN_ofSeq {ι : Type*} [Finite ι] (f : (ι → α) → β) (r : ι → ℕ → α) :
    starMapN f (fun i => (ofSeq (r i) : αS)) = (ofSeq fun n => f fun i => r i n : βS) := by
  rw [starMapN, Ultrapower.tuple_ofSeq, starMap_ofSeq]
  rfl

/-- **Exercise 3.12(5).** The extension of a function of several arguments agrees with the
function on standard arguments. -/
theorem starMapN_of {ι : Type*} [Finite ι] (f : (ι → α) → β) (a : ι → α) :
    starMapN f (fun i => (of (a i) : αS)) = (of (f a) : βS) :=
  starMapN_ofSeq f fun i _ => a i

/-!
## 3.13 Partial Functions and Hypersequences

A function defined only on a subset $`A` extends to a function defined on the enlargement
$`{}^*A`: if $`[r] \in {}^*A` then $`f(r_n)` is defined for almost all $`n`, which is enough to
determine a class. In Lean the partial function is a function on the subtype of $`A`. We first
identify $`{}^*A` with the ultrapower of that subtype ({lit}`starSetEquiv`), which is another
way of saying that a member of $`{}^*A` may be represented by a sequence all of whose terms lie
in $`A`; the extension {lit}`starMapOn` is then the termwise extension through this
identification, and the book's formula with a default value off $`A` is a theorem.

The most important case is a sequence $`s`, a function on the natural numbers: it extends to a
_hypersequence_ defined on all hypernatural numbers, so that $`s_N` makes sense for unlimited
$`N`.
-/

/-- **Section 3.13.** The enlargement of $`A` is the image of the ultrapower of the subtype of
$`A` under the extension of the inclusion. -/
theorem starSet_eq_range_starMap_val (A : Set α) :
    (⋆A : Set αS) = range (⋆(Subtype.val : A → α)) := by
  rw [← starSet_range, Subtype.range_coe]

/-- **Section 3.13.** A member of $`{}^*A` is the class of a sequence all of whose terms lie in
$`A`. -/
theorem exists_subtype_seq {A : Set α} {r : ℕ → α} (h : (ofSeq r : αS) ∈ ⋆A) :
    ∃ r' : ℕ → A, ∀ᶠ n in hyperfilter ℕ, (r' n : α) = r n := by
  refine exists_seq_of_almostAll_exists (p := fun n (a : A) => (a : α) = r n)
    ((ofSeq_mem_starSet.1 h).mono fun n hn => ?_)
  exact ⟨⟨r n, hn⟩, rfl⟩

/-- **Section 3.13.** The enlargement $`{}^*A`, as a subtype of the ultrapower, is the
ultrapower of the subtype $`A`. -/
noncomputable def starSetEquiv (A : Set α) : Ultrapower A ≃ (⋆A : Set αS) :=
  Equiv.ofBijective
    (fun y => ⟨⋆(Subtype.val : A → α) y, by
      rw [starSet_eq_range_starMap_val]
      exact mem_range_self y⟩)
    ⟨fun _ _ h => starMap_injective Subtype.val_injective (congrArg Subtype.val h),
      fun x => by
        have hx : (x : αS) ∈ range (⋆(Subtype.val : A → α)) := by
          rw [← starSet_eq_range_starMap_val]
          exact x.2
        obtain ⟨y, hy⟩ := hx
        exact ⟨y, Subtype.ext hy⟩⟩

/-- **Section 3.13.** The identification of the ultrapower of $`A` with $`{}^*A` sends the
class of a sequence in $`A` to the class of the same sequence. -/
theorem starSetEquiv_ofSeq (A : Set α) (r : ℕ → A) :
    ((starSetEquiv A (ofSeq r) : (⋆A : Set αS)) : αS) = ofSeq fun n => (r n : α) :=
  starMap_ofSeq _ r

/-- **Section 3.13.** The extension of a partial function: for $`f` defined on $`A`, the
function $`{}^*f` defined on $`{}^*A`, so that the domain of the extension is the enlargement
of the domain. -/
noncomputable def starMapOn (A : Set α) (f : A → β) (x : (⋆A : Set αS)) : βS :=
  ⋆f ((starSetEquiv A).symm x)

/-- **Section 3.13.** On the class of a sequence that lies in $`A`, the extension of a partial
function acts termwise. -/
theorem starMapOn_ofSeq_subtype (A : Set α) (f : A → β) (r : ℕ → A)
    (h : (ofSeq (fun n => (r n : α)) : αS) ∈ ⋆A) :
    starMapOn A f ⟨ofSeq fun n => (r n : α), h⟩ = (ofSeq fun n => f (r n) : βS) := by
  have key : (⟨ofSeq fun n => (r n : α), h⟩ : (⋆A : Set αS)) = starSetEquiv A (ofSeq r) :=
    Subtype.ext (starSetEquiv_ofSeq A r).symm
  rw [starMapOn, key, Equiv.symm_apply_apply, starMap_ofSeq]
  rfl

/-- **Section 3.13, almost-all criterion for partial functions.** For $`[r] \in {}^*A`,
$`{}^*f([r]) = [s]` if and only if, for almost all $`n`, $`r_n \in A` and $`f(r_n) = s_n`. -/
theorem starMapOn_ofSeq_eq_ofSeq {A : Set α} {f : A → β} {r : ℕ → α} {s : ℕ → β}
    (h : (ofSeq r : αS) ∈ ⋆A) :
    starMapOn A f ⟨ofSeq r, h⟩ = (ofSeq s : βS) ↔
      ∀ᶠ n in hyperfilter ℕ, ∃ hn : r n ∈ A, f ⟨r n, hn⟩ = s n := by
  obtain ⟨r', hr'⟩ := exists_subtype_seq h
  have key : (⟨ofSeq r, h⟩ : (⋆A : Set αS)) = starSetEquiv A (ofSeq r') :=
    Subtype.ext ((Ultrapower.ofSeq_eq_ofSeq.2 (hr'.mono fun n hn => hn.symm)).trans
      (starSetEquiv_ofSeq A r').symm)
  rw [starMapOn, key, Equiv.symm_apply_apply, starMap_ofSeq_eq_ofSeq]
  constructor
  · intro H
    filter_upwards [hr', H] with n hn Hn
    have hmem : r n ∈ A := hn ▸ (r' n).2
    refine ⟨hmem, ?_⟩
    rw [← Hn]
    exact congrArg f (Subtype.ext hn.symm)
  · intro H
    filter_upwards [hr', H] with n hn Hn
    obtain ⟨hmem, Hn⟩ := Hn
    rw [← Hn]
    exact congrArg f (Subtype.ext hn)

/-- **Section 3.13, the book's definition.** For $`[r] \in {}^*A`, the value $`{}^*f([r])` is
the class of the sequence that is $`f(r_n)` where $`r_n \in A` and a fixed default value $`d`
elsewhere (the book takes $`d = 0`). -/
theorem starMapOn_ofSeq {A : Set α} [DecidablePred (· ∈ A)] (f : A → β) (d : β) {r : ℕ → α}
    (h : (ofSeq r : αS) ∈ ⋆A) :
    starMapOn A f ⟨ofSeq r, h⟩ =
      (ofSeq fun n => if hn : r n ∈ A then f ⟨r n, hn⟩ else d : βS) := by
  rw [starMapOn_ofSeq_eq_ofSeq]
  exact (ofSeq_mem_starSet.1 h).mono fun n hn => ⟨hn, by simp [hn]⟩

/-- **Section 3.13.** The extension of a partial function extends it: for $`a \in A`,
$`{}^*f({}^*a) = {}^*(f(a))`. -/
theorem starMapOn_of {A : Set α} (f : A → β) {a : α} (ha : a ∈ A) :
    starMapOn A f ⟨(of a : αS), of_mem_starSet.2 ha⟩ = (of (f ⟨a, ha⟩) : βS) :=
  starMapOn_ofSeq_subtype A f (fun _ => ⟨a, ha⟩) (of_mem_starSet.2 ha)

/-- **Section 3.13.** If a partial function on $`A` is the restriction of a total function
$`g`, its extension is the restriction of $`{}^*g` to $`{}^*A`. -/
theorem starMapOn_eq_starMap {A : Set α} {f : A → β} {g : α → β} (hg : ∀ a : A, g a = f a)
    (x : (⋆A : Set αS)) : (starMapOn A f x : βS) = ⋆g (x : αS) := by
  obtain ⟨y, rfl⟩ := (starSetEquiv A).surjective x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := A) y
  rw [starMapOn, Equiv.symm_apply_apply, starSetEquiv_ofSeq, starMap_ofSeq, starMap_ofSeq,
    Ultrapower.ofSeq_eq_ofSeq]
  exact Eventually.of_forall fun n => (hg (r n)).symm

/-- **Section 3.13, hypersequences.** The extension of a sequence $`s` to a function on the
hyperreals whose values on the hypernatural numbers form the hypersequence extending $`s`:
at the class of a sequence of natural numbers $`k_n` its value is the class of $`s_{k_n}`
({lit}`hyperSeq_ofSeq_natCast`). Off the hypernaturals the value is of no significance (it is
computed through the integer part). -/
noncomputable def hyperSeq (s : ℕ → β) : ℝ* → βS := ⋆(fun x : ℝ => s ⌊x⌋₊)

/-- **Section 3.13, hypersequences.** At the hypernatural number $`[k_n]`, the hypersequence
extending $`s` takes the value $`[s_{k_n}]`. -/
theorem hyperSeq_ofSeq_natCast (s : ℕ → β) (k : ℕ → ℕ) :
    hyperSeq s (Hyperreal.ofSeq fun n => (k n : ℝ)) = (ofSeq fun n => s (k n) : βS) := by
  rw [hyperSeq, ← Ultrapower.ofSeq_real, starMap_ofSeq_eq_ofSeq]
  exact Eventually.of_forall fun n => by simp

/-- **Section 3.13, hypersequences.** The hypersequence extends the sequence: at a standard
natural number $`n` its value is $`s_n`. -/
theorem hyperSeq_natCast (s : ℕ → β) (n : ℕ) : hyperSeq s (n : ℝ*) = (of (s n) : βS) :=
  hyperSeq_ofSeq_natCast s fun _ => n

/-- **Section 3.13, hypersequences.** For a real sequence, the value of the hypersequence at
$`\omega` is the class of the sequence itself: $`s_\omega = [s]`. -/
theorem hyperSeq_omega (s : ℕ → ℝ) : hyperSeq s ω = Hyperreal.ofSeq s :=
  hyperSeq_ofSeq_natCast s id

/-- **Section 3.13, hypersequences.** The hypersequence is the extension, in the sense of
partial functions, of the sequence regarded as a function defined on the set of natural
numbers inside the reals: any function $`f` on that set with $`f(n) = s_n` has extension
{lit}`hyperSeq s` on $`{}^*\mathbb N`. -/
theorem starMapOn_range_natCast_eq_hyperSeq (s : ℕ → β) (f : range ((↑) : ℕ → ℝ) → β)
    (hf : ∀ n : ℕ, f ⟨n, n, rfl⟩ = s n) (x : ℕ*) :
    (starMapOn (range ((↑) : ℕ → ℝ)) f x : βS) = hyperSeq s x := by
  refine starMapOn_eq_starMap (g := fun x : ℝ => s ⌊x⌋₊) ?_ x
  rintro ⟨_, n, rfl⟩
  simp [hf]

/-- **Section 3.13, hypersequences.** The hypernatural numbers are the ultrapower of the
natural numbers: the extension of the inclusion of the naturals in the reals is an injection of
that ultrapower into the hyperreals with image $`{}^*\mathbb N`. -/
theorem range_starMap_natCast : range (⋆((↑) : ℕ → ℝ) : Ultrapower ℕ → ℝ*) = ℕ* :=
  (starSet_range _).symm

/-- **Section 3.13, hypersequences.** The inclusion of the ultrapower of the natural numbers in
the hyperreals is injective. -/
theorem starMap_natCast_injective :
    Function.Injective (⋆((↑) : ℕ → ℝ) : Ultrapower ℕ → ℝ*) :=
  starMap_injective Nat.cast_injective

/-- **Section 3.13, hypersequences.** On the ultrapower of the natural numbers the
hypersequence is the plain termwise extension of the sequence. -/
theorem hyperSeq_starMap_natCast (s : ℕ → β) (N : Ultrapower ℕ) :
    hyperSeq s (⋆((↑) : ℕ → ℝ) N) = (⋆s N : βS) := by
  obtain ⟨k, rfl⟩ := ofSeq_surjective (α := ℕ) N
  rw [starMap_ofSeq, starMap_ofSeq]
  exact hyperSeq_ofSeq_natCast s k

end Extension

/-!
## 3.14 Enlarging Relations

A relation among standard elements is enlarged by the almost-all criterion: $`{}^*P` holds of
classes of sequences when $`P` holds of their terms at almost all indices. For binary relations
this is {lit}`starRel₂` (Mathlib's {name}`Filter.Germ.LiftRel`). For relations of arbitrary
finite arity we take a $`k`-ary relation to be a set of tuples indexed by a finite type, and
its enlargement {lit}`starRel` is a set of tuples of elements of the ultrapower.

Enlargement of relations subsumes the earlier constructions: the enlargement of a set is the
unary case, equality and order on the ultrapower are the enlargements of equality and order,
and the graph of an extended function is the enlargement of the graph.
-/

section Relations

variable {α αS : Type u} {β βS : Type v} {γ γS : Type w}
  [StarType α αS] [StarType β βS] [StarType γ γS]

/-- **Section 3.14, almost-all criterion for binary relations.** $`{}^*P([r], [s])` if and
only if $`P(r_n, s_n)` for almost all $`n`. -/
theorem starRel₂_ofSeq {P : α → β → Prop} {r : ℕ → α} {s : ℕ → β} :
    ⋆P (ofSeq r : αS) (ofSeq s : βS) ↔ ∀ᶠ n in hyperfilter ℕ, P (r n) (s n) := by
  change Germ.LiftRel P (StarType.equiv (ofSeq r : αS)) (StarType.equiv (ofSeq s : βS)) ↔ _
  rw [equiv_ofSeq, equiv_ofSeq]
  exact Germ.liftRel_coe

/-- **Section 3.14.** $`{}^*P` extends $`P`: on standard elements, $`{}^*P({}^*a, {}^*b)` if
and only if $`P(a, b)`. -/
theorem starRel₂_of {P : α → β → Prop} {a : α} {b : β} :
    ⋆P (of a : αS) (of b : βS) ↔ P a b := by
  rw [of_eq_ofSeq, of_eq_ofSeq, starRel₂_ofSeq, almostAll_const]

/-- **Section 3.14.** The negation of an enlarged relation is the enlargement of the
negation. -/
theorem not_starRel₂ {P : α → β → Prop} {x : αS} {y : βS} :
    ¬ ⋆P x y ↔ ⋆(fun a b => ¬ P a b) x y := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [starRel₂_ofSeq, starRel₂_ofSeq, almostAll_not]

/-- **Section 3.14.** The enlargement of equality is equality. -/
theorem starRel₂_eq {x y : αS} : ⋆(fun a b : α => a = b) x y ↔ x = y := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := α) y
  rw [starRel₂_ofSeq, Ultrapower.ofSeq_eq_ofSeq]

/-- **Section 3.14.** The enlargement of the order relation $`<` on the reals is the order of
the hyperreals. -/
theorem starRel₂_lt {x y : ℝ*} : ⋆(fun a b : ℝ => a < b) x y ↔ x < y := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
  rw [ofSeq_lt_ofSeq_iff]
  exact starRel₂_ofSeq

/-- **Section 3.14.** The enlargement of the relation $`\le` on the reals is the weak order of
the hyperreals. -/
theorem starRel₂_le {x y : ℝ*} : ⋆(fun a b : ℝ => a ≤ b) x y ↔ x ≤ y := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
  rw [ofSeq_le_ofSeq_iff]
  exact starRel₂_ofSeq

/-- **Section 3.14.** The enlargement of the graph of a function is the graph of its
extension. -/
theorem starRel₂_graph (f : α → β) {x : αS} {y : βS} :
    ⋆(fun a b => f a = b) x y ↔ ⋆f x = y := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [starRel₂_ofSeq, starMap_ofSeq_eq_ofSeq]

/-- **Section 3.14.** The enlargement of the graph of a partial function is the graph of its
extension, whose domain is the enlargement of the domain. -/
theorem starRel₂_graph_partial {A : Set α} (f : A → β) {x : αS} {y : βS} :
    ⋆(fun a b => ∃ h : a ∈ A, f ⟨a, h⟩ = b) x y ↔ ∃ h : x ∈ ⋆A, starMapOn A f ⟨x, h⟩ = y := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [starRel₂_ofSeq]
  constructor
  · intro H
    have h : (ofSeq r : αS) ∈ ⋆A := ofSeq_mem_starSet.2 (H.mono fun n hn => hn.1)
    exact ⟨h, (starMapOn_ofSeq_eq_ofSeq h).2 H⟩
  · rintro ⟨h, H⟩
    exact (starMapOn_ofSeq_eq_ofSeq h).1 H

/-- **Section 3.14, transfer of an existential quantifier.** There is a $`y` in the ultrapower
with $`{}^*P([r], y)` if and only if, for almost all $`n`, there is a $`b` with
$`P(r_n, b)`. -/
theorem exists_starRel₂_ofSeq {P : α → β → Prop} {r : ℕ → α} :
    (∃ y : βS, ⋆P (ofSeq r : αS) y) ↔ ∀ᶠ n in hyperfilter ℕ, ∃ b, P (r n) b := by
  rw [(ofSeq_surjective (α := β) (αS := βS)).exists]
  simp only [starRel₂_ofSeq]
  exact almostAll_exists_iff.symm

/-- **Section 3.14, transfer of a universal quantifier.** $`{}^*P([r], y)` holds for all $`y`
in the ultrapower if and only if, for almost all $`n`, $`P(r_n, b)` holds for all $`b`. -/
theorem forall_starRel₂_ofSeq {P : α → β → Prop} {r : ℕ → α} :
    (∀ y : βS, ⋆P (ofSeq r : αS) y) ↔ ∀ᶠ n in hyperfilter ℕ, ∀ b, P (r n) b := by
  rw [(ofSeq_surjective (α := β) (αS := βS)).forall]
  simp only [starRel₂_ofSeq]
  exact almostAll_forall_iff.symm

/-- **Section 3.14, transfer of a bounded existential quantifier.** There is a $`y \in {}^*B`
with $`{}^*P([r], y)` if and only if, for almost all $`n`, there is a $`b \in B` with
$`P(r_n, b)`. -/
theorem exists_mem_starSet_starRel₂_ofSeq {P : α → β → Prop} {B : Set β} {r : ℕ → α} :
    (∃ y ∈ (⋆B : Set βS), ⋆P (ofSeq r : αS) y) ↔ ∀ᶠ n in hyperfilter ℕ, ∃ b ∈ B, P (r n) b := by
  rw [(ofSeq_surjective (α := β) (αS := βS)).exists]
  simp only [starRel₂_ofSeq, ofSeq_mem_starSet, ← almostAll_and]
  exact (almostAll_exists_iff (p := fun n b => b ∈ B ∧ P (r n) b)).symm

/-- **Section 3.14, transfer of a bounded universal quantifier.** $`{}^*P([r], y)` holds for
all $`y \in {}^*B` if and only if, for almost all $`n`, $`P(r_n, b)` holds for all
$`b \in B`. -/
theorem forall_mem_starSet_starRel₂_ofSeq {P : α → β → Prop} {B : Set β} {r : ℕ → α} :
    (∀ y ∈ (⋆B : Set βS), ⋆P (ofSeq r : αS) y) ↔ ∀ᶠ n in hyperfilter ℕ, ∀ b ∈ B, P (r n) b := by
  rw [(ofSeq_surjective (α := β) (αS := βS)).forall]
  simp only [starRel₂_ofSeq, ofSeq_mem_starSet, ← almostAll_imp]
  exact (almostAll_forall_iff (p := fun n b => b ∈ B → P (r n) b)).symm

/-- **Section 3.14.** The statement value
$`[\![ P(r^1, \dots, r^k) ]\!] = \{n : P(r^1_n, \dots, r^k_n)\}` of a relation applied to a
tuple of sequences. -/
def relSet {ι : Type*} (P : Set (ι → α)) (r : ι → ℕ → α) : Set ℕ := {n | (fun i => r i n) ∈ P}

/-- **Section 3.14, well-definedness of enlarged relations.**
$`[\![ r^1 = s^1 ]\!] \cap \dots \cap [\![ r^k = s^k ]\!] \cap [\![ P(r^1, \dots, r^k) ]\!]
\subseteq [\![ P(s^1, \dots, s^k) ]\!]`. -/
theorem iInter_agreementSet_inter_relSet_subset {ι : Type*} (P : Set (ι → α))
    (r s : ι → ℕ → α) : (⋂ i, agreementSet (r i) (s i)) ∩ relSet P r ⊆ relSet P s := by
  rintro n ⟨h₁, h₂⟩
  have h : (fun i => r i n) = fun i => s i n := funext fun i => mem_iInter.1 h₁ i
  simp only [relSet, mem_ofPred_eq] at h₂ ⊢
  rwa [← h]

/-- **Section 3.14, well-definedness of enlarged relations.** For finitely many sequences, if
$`r^i \equiv s^i` for each $`i` and $`[\![ P(r^1, \dots, r^k) ]\!]` is large, then
$`[\![ P(s^1, \dots, s^k) ]\!]` is large. -/
theorem relSet_mem_hyperfilter_of_seqEquiv {ι : Type*} [Finite ι] {P : Set (ι → α)}
    {r s : ι → ℕ → α} (h : ∀ i, r i ≡ᵤ s i) (hP : relSet P r ∈ hyperfilter ℕ) :
    relSet P s ∈ hyperfilter ℕ :=
  mem_hyperfilter_of_superset (inter_mem ((iInter_mem (f := (hyperfilter ℕ : Filter ℕ))).2 h) hP)
    (iInter_agreementSet_inter_relSet_subset P r s)

/-- **Section 3.14.** The enlargement $`{}^*P` of a $`k`-ary relation $`P`, a set of tuples
indexed by a finite type $`\iota`: a tuple of elements of the ultrapower belongs to it when the
corresponding class of tuples belongs to the enlargement of $`P` as a set. Finiteness of the
index type is a hypothesis of the definition, because only then is membership independent of
the representing sequences ({lit}`Goldblatt.starRel_ofSeq`). -/
def starRel {ι : Type*} [Finite ι] (P : Set (ι → α)) : Set (ι → αS) :=
  {x | Ultrapower.tuple x ∈ (⋆P : Set (Ultrapower (ι → α)))}

/-- **Section 3.14, almost-all criterion for relations.** For a relation of finite arity,
$`{}^*P([r^1], \dots, [r^k])` if and only if $`P(r^1_n, \dots, r^k_n)` for almost all $`n`. -/
theorem starRel_ofSeq {ι : Type*} [Finite ι] {P : Set (ι → α)} {r : ι → ℕ → α} :
    (fun i => (ofSeq (r i) : αS)) ∈ starRel P ↔ ∀ᶠ n in hyperfilter ℕ, (fun i => r i n) ∈ P := by
  rw [starRel, mem_ofPred_eq, Ultrapower.tuple_ofSeq, ofSeq_mem_starSet]

/-- **Section 3.14.** $`{}^*P([r^1], \dots, [r^k])` if and only if the statement value
$`[\![ P(r^1, \dots, r^k) ]\!]` is large. -/
theorem starRel_ofSeq_iff_relSet {ι : Type*} [Finite ι] {P : Set (ι → α)} {r : ι → ℕ → α} :
    (fun i => (ofSeq (r i) : αS)) ∈ starRel P ↔ relSet P r ∈ hyperfilter ℕ :=
  starRel_ofSeq

/-- **Section 3.14.** $`{}^*P` extends $`P`: for standard elements $`a_1, \dots, a_k`,
$`{}^*P({}^*a_1, \dots, {}^*a_k)` if and only if $`P(a_1, \dots, a_k)`. -/
theorem starRel_of {ι : Type*} [Finite ι] {P : Set (ι → α)} {a : ι → α} :
    (fun i => (of (a i) : αS)) ∈ starRel P ↔ a ∈ P := by
  rw [starRel, mem_ofPred_eq, Ultrapower.tuple_of, of_mem_starSet]

/-- **Section 3.14.** Enlargement of sets is the unary case of enlargement of relations: for a
relation on one-tuples, $`{}^*P(x)` if and only if $`x` belongs to the enlargement of the
corresponding set. -/
theorem starRel_unary {ι : Type*} [Unique ι] {P : Set (ι → α)} {x : ι → αS} :
    x ∈ starRel P ↔ x default ∈ ⋆{a : α | (fun _ => a) ∈ P} := by
  obtain ⟨r, rfl⟩ := Ultrapower.exists_rep_tuple (α := α) x
  rw [starRel_ofSeq, ofSeq_mem_starSet]
  refine eventually_congr (Eventually.of_forall fun n => ?_)
  have h : (fun i => r i n) = fun _ => r default n := funext fun i => by rw [Unique.eq_default i]
  simp only [mem_ofPred_eq, h]

/-- **Section 3.14.** The binary case of the enlargement of relations is {lit}`starRel₂`. -/
theorem starRel_binary {P : α → α → Prop} {x y : αS} :
    ![x, y] ∈ starRel {a : Fin 2 → α | P (a 0) (a 1)} ↔ ⋆P x y := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := α) y
  have h : (![ofSeq r, ofSeq s] : Fin 2 → αS) = fun i => ofSeq (![r, s] i) := by
    funext i
    fin_cases i <;> rfl
  rw [h, starRel_ofSeq, starRel₂_ofSeq]
  rfl

/-- **Section 3.14, tuple-packed form.** The enlargement of the graph of a function of several
arguments is the graph of its extension, with the arguments packed into a single element of the
ultrapower of tuples and the graph treated as a binary relation between a tuple and a value.
This is the unary statement in disguise; the statement about the enlargement of the graph as a
relation of arity $`m + 1` is {lit}`Goldblatt.starRel_graph`. -/
theorem starRel₂_graph_starMapN {ι : Type*} [Finite ι] (f : (ι → α) → β) {x : ι → αS}
    {y : βS} : ⋆(fun a b => f a = b) (Ultrapower.tuple x) y ↔ starMapN f x = y :=
  starRel₂_graph f

/-- **Section 3.14, appending a coordinate.** Appending the class of a sequence to a tuple of
classes of sequences gives the tuple of classes of the sequences with the new one appended. -/
theorem Ultrapower.snoc_ofSeq {k : ℕ} (r : Fin k → ℕ → α) (s : ℕ → α) :
    Fin.snoc (α := fun _ => αS) (fun i => (ofSeq (r i) : αS)) (ofSeq s) =
      fun i => ofSeq (Fin.snoc (α := fun _ => ℕ → α) r s i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- **Section 3.14, appending a coordinate.** The $`n`-th terms of a tuple of sequences with one
sequence appended are the $`n`-th terms of the tuple with the $`n`-th term of the new sequence
appended. -/
theorem Ultrapower.snoc_apply_apply {k : ℕ} (r : Fin k → ℕ → α) (s : ℕ → α) (n : ℕ) :
    (fun i => Fin.snoc (α := fun _ => ℕ → α) r s i n) =
      Fin.snoc (α := fun _ => α) (fun i => r i n) (s n) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- **Section 3.14.** The enlargement of the graph of a function of $`m` arguments, the graph
being a relation of arity $`m + 1` (a set of tuples of length $`m + 1`) enlarged as such, is the
graph of the extension: $`{}^*(\operatorname{Graph} f)(x_1, \dots, x_m, y)` if and only if
$`{}^*f(x_1, \dots, x_m) = y`. Here a tuple of length $`m + 1` is a tuple of length $`m` with
one more entry appended. -/
theorem starRel_graph {m : ℕ} (f : (Fin m → α) → α) {x : Fin m → αS} {y : αS} :
    Fin.snoc (α := fun _ => αS) x y ∈
        starRel {a : Fin (m + 1) → α | f (Fin.init a) = a (Fin.last m)} ↔
      starMapN f x = y := by
  obtain ⟨r, rfl⟩ := Ultrapower.exists_rep_tuple (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := α) y
  rw [Ultrapower.snoc_ofSeq, starRel_ofSeq, starMapN_ofSeq, Ultrapower.ofSeq_eq_ofSeq]
  refine eventually_congr (Eventually.of_forall fun n => ?_)
  simp [Ultrapower.snoc_apply_apply]

/-!
## 3.15 Exercises on Enlarged Relations

The enlargement of a product of sets is the product of the enlargements, and the enlargement of
the domain of a relation is the domain of the enlarged relation. The second fact is where a
choice of witnesses along the index set is needed.
-/

/-- **Exercise 3.15(1).** $`{}^*(A_1 \times \dots \times A_k) =
{}^*A_1 \times \dots \times {}^*A_k`. -/
theorem starRel_pi {ι : Type*} [Finite ι] (A : ι → Set α) :
    (starRel (univ.pi A) : Set (ι → αS)) = univ.pi fun i => ⋆(A i) := by
  ext x
  obtain ⟨r, rfl⟩ := Ultrapower.exists_rep_tuple (α := α) x
  simp only [starRel_ofSeq, mem_univ_pi, ofSeq_mem_starSet, almostAll_forall_finite]

/-- **Exercise 3.15(1), binary form.** $`{}^*(A \times B) = {}^*A \times {}^*B`. -/
theorem starRel₂_prod (A : Set α) (B : Set β) {x : αS} {y : βS} :
    ⋆(fun a b => a ∈ A ∧ b ∈ B) x y ↔ x ∈ ⋆A ∧ y ∈ ⋆B := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [starRel₂_ofSeq, almostAll_and, ofSeq_mem_starSet, ofSeq_mem_starSet]

/-- **Exercise 3.15(1).** $`{}^*(\mathbb R^k) = ({}^*\mathbb R)^k`: the enlargement of the set
of all $`k`-tuples is the set of all $`k`-tuples of elements of the ultrapower. (The underlying
identification of tuples is {lit}`Ultrapower.tupleEquiv`.) -/
theorem starRel_univ {ι : Type*} [Finite ι] : (starRel (univ : Set (ι → α)) : Set (ι → αS)) = univ := by
  ext x
  simp [starRel, starSet_univ]

/-- **Exercise 3.15(2).** $`{}^*(\operatorname{dom} P) = \operatorname{dom} {}^*P` for a binary
relation $`P`. -/
theorem starSet_dom (P : α → β → Prop) :
    (⋆{a | ∃ b, P a b} : Set αS) = {x | ∃ y : βS, ⋆P x y} := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [ofSeq_mem_starSet, mem_ofPred_eq, exists_starRel₂_ofSeq]
  rfl

/-- **Exercise 3.15(2), companion.** The enlargement of the range of a binary relation is the
range of the enlarged relation. -/
theorem starSet_ran (P : α → β → Prop) :
    (⋆{b | ∃ a, P a b} : Set βS) = {y | ∃ x : αS, ⋆P x y} := by
  ext y
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [ofSeq_mem_starSet, mem_ofPred_eq, (ofSeq_surjective (α := α) (αS := αS)).exists]
  simp only [starRel₂_ofSeq]
  exact almostAll_exists_iff (p := fun n a => P a (s n))

/-- **Exercise 3.15(3).** The generalization to relations of higher arity. Let $`P` be a
relation of arity $`k + 1`, a set of tuples of length $`k + 1`, and let its domain be the
relation of arity $`k` consisting of the tuples that some further entry extends to a member of
$`P`. Then $`{}^*(\operatorname{dom} P) = \operatorname{dom} {}^*P`, both enlargements being
those of Section 3.14: a $`k`-tuple of elements of the ultrapower lies in the enlargement of the
domain if and only if some further element of the ultrapower extends it to a member of
$`{}^*P`. As in the binary case, the proof chooses witnesses along the index set. -/
theorem starRel_dom_snoc {k : ℕ} (P : Set (Fin (k + 1) → α)) :
    (starRel {a : Fin k → α | ∃ b, Fin.snoc (α := fun _ => α) a b ∈ P} : Set (Fin k → αS)) =
      {x | ∃ y : αS, Fin.snoc (α := fun _ => αS) x y ∈ starRel P} := by
  ext x
  obtain ⟨r, rfl⟩ := Ultrapower.exists_rep_tuple (α := α) x
  rw [starRel_ofSeq, mem_ofPred_eq, (ofSeq_surjective (α := α) (αS := αS)).exists]
  simp only [Ultrapower.snoc_ofSeq, starRel_ofSeq]
  refine (almostAll_exists_iff
    (p := fun n b => Fin.snoc (α := fun _ => α) (fun i => r i n) b ∈ P)).trans ?_
  refine exists_congr fun s => eventually_congr (Eventually.of_forall fun n => ?_)
  simp [Ultrapower.snoc_apply_apply]

/-- **Exercise 3.15(3), tuple-packed form.** A variant in which the relation is presented as a
binary relation between a tuple and one further argument, possibly of another type, and the
tuple of elements of the ultrapower is packed into a single element of the ultrapower of
tuples: the packed tuple lies in the enlargement of the domain if and only if the enlarged
binary relation relates it to something. This reduces to the binary case by unfolding; the
statement about a relation of arity $`k + 1` enlarged as in Section 3.14 is
{name}`Goldblatt.starRel_dom_snoc`. -/
theorem starRel_dom {ι : Type*} [Finite ι] (P : (ι → α) → β → Prop) :
    (starRel {a | ∃ b, P a b} : Set (ι → αS)) = {x | ∃ y : βS, ⋆P (Ultrapower.tuple x) y} := by
  ext x
  rw [starRel, mem_ofPred_eq, starSet_dom]
  rfl

/-- **Exercise 3.15(3).** For a partial function $`f` with domain $`A`, the domain of the
extension is the enlargement of the domain: $`x \in {}^*A` if and only if the enlarged graph
relates $`x` to some $`y`. -/
theorem starSet_dom_partial {A : Set α} (f : A → β) :
    (⋆A : Set αS) = {x | ∃ y : βS, ⋆(fun a b => ∃ h : a ∈ A, f ⟨a, h⟩ = b) x y} := by
  ext x
  simp only [mem_ofPred_eq, starRel₂_graph_partial]
  exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩

/-- **Exercise 3.15(3), tuple-packed form.** For a partial function of several arguments with
domain $`A`, a set of tuples, the domain of the extension is the enlargement of $`A` as a
relation. The graph is again treated as a binary relation between a packed tuple and a
value, so this is the unary statement unfolded; the statement in which the graph is a relation
of arity $`m + 1` enlarged as in Section 3.14 is {lit}`Goldblatt.starRel_dom_partial_snoc`. -/
theorem starRel_dom_partial {ι : Type*} [Finite ι] {A : Set (ι → α)} (f : A → β) :
    (starRel A : Set (ι → αS)) =
      {x | ∃ y : βS, ⋆(fun a b => ∃ h : a ∈ A, f ⟨a, h⟩ = b) (Ultrapower.tuple x) y} := by
  ext x
  rw [starRel, mem_ofPred_eq, starSet_dom_partial f]
  rfl

/-- **Exercise 3.15(3), partial functions of several arguments.** The extension of a partial
function $`f` of several arguments whose domain is the relation $`A`: it is defined on the
tuples of elements of the ultrapower that lie in the enlargement $`{}^*A` of Section 3.14, and
is the extension of Section 3.13 applied to the packed tuple. -/
noncomputable def starMapOnN {ι : Type*} [Finite ι] (A : Set (ι → α)) (f : A → β)
    (x : (starRel A : Set (ι → αS))) : βS :=
  starMapOn A f ⟨Ultrapower.tuple (x : ι → αS), x.2⟩

/-- **Exercise 3.15(3), partial functions of several arguments.** The almost-all criterion for
the extension of a partial function of several arguments:
$`{}^*f([r^1], \dots, [r^k]) = [s]` if and only if, for almost all $`n`, the tuple
$`(r^1_n, \dots, r^k_n)` lies in the domain and $`f` sends it to $`s_n`. -/
theorem starMapOnN_ofSeq_eq_ofSeq {ι : Type*} [Finite ι] {A : Set (ι → α)} {f : A → β}
    {r : ι → ℕ → α} {s : ℕ → β} (h : (fun i => (ofSeq (r i) : αS)) ∈ starRel A) :
    starMapOnN A f ⟨fun i => (ofSeq (r i) : αS), h⟩ = (ofSeq s : βS) ↔
      ∀ᶠ n in hyperfilter ℕ, ∃ hn : (fun i => r i n) ∈ A, f ⟨fun i => r i n, hn⟩ = s n := by
  have h' : (ofSeq fun n i => r i n : Ultrapower (ι → α)) ∈ ⋆A := by
    rw [← Ultrapower.tuple_ofSeq (αS := αS)]
    exact h
  have key : starMapOnN A f ⟨fun i => (ofSeq (r i) : αS), h⟩ =
      (starMapOn A f ⟨ofSeq fun n i => r i n, h'⟩ : βS) := by
    unfold starMapOnN
    congr 2
    exact Ultrapower.tuple_ofSeq r
  rw [key, starMapOn_ofSeq_eq_ofSeq]

/-- **Exercise 3.15(3), partial functions of several arguments.** The extension of a partial
function of several arguments agrees with the function on standard tuples of its domain. -/
theorem starMapOnN_of {ι : Type*} [Finite ι] {A : Set (ι → α)} (f : A → β) {a : ι → α}
    (ha : a ∈ A) :
    starMapOnN A f ⟨fun i => (of (a i) : αS), starRel_of.2 ha⟩ = (of (f ⟨a, ha⟩) : βS) :=
  (starMapOnN_ofSeq_eq_ofSeq (r := fun i _ => a i) (s := fun _ => f ⟨a, ha⟩)
    (starRel_of.2 ha)).2 (Eventually.of_forall fun _ => ⟨ha, rfl⟩)

/-- **Section 3.14 and Exercise 3.15(3), partial functions of several arguments.** The
enlargement of the graph of a partial function of $`m` arguments with domain $`A`, the graph
being a relation of arity $`m + 1` enlarged as such, is the graph of the extension:
$`{}^*(\operatorname{Graph} f)(x_1, \dots, x_m, y)` if and only if $`(x_1, \dots, x_m)` lies
in $`{}^*A` and $`{}^*f(x_1, \dots, x_m) = y`. -/
theorem starRel_graph_partial {m : ℕ} {A : Set (Fin m → α)} (f : A → α) {x : Fin m → αS}
    {y : αS} :
    Fin.snoc (α := fun _ => αS) x y ∈ starRel
        {a : Fin (m + 1) → α | ∃ h : Fin.init a ∈ A, f ⟨Fin.init a, h⟩ = a (Fin.last m)} ↔
      ∃ h : x ∈ starRel A, starMapOnN A f ⟨x, h⟩ = y := by
  obtain ⟨r, rfl⟩ := Ultrapower.exists_rep_tuple (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := α) y
  rw [Ultrapower.snoc_ofSeq, starRel_ofSeq]
  have hcongr : (∀ᶠ n in hyperfilter ℕ, (fun i => Fin.snoc (α := fun _ => ℕ → α) r s i n) ∈
        {a : Fin (m + 1) → α | ∃ h : Fin.init a ∈ A, f ⟨Fin.init a, h⟩ = a (Fin.last m)}) ↔
      ∀ᶠ n in hyperfilter ℕ, ∃ hn : (fun i => r i n) ∈ A, f ⟨fun i => r i n, hn⟩ = s n := by
    refine eventually_congr (Eventually.of_forall fun n => ?_)
    simp [Ultrapower.snoc_apply_apply]
  rw [hcongr]
  constructor
  · intro H
    have h : (fun i => (ofSeq (r i) : αS)) ∈ starRel A :=
      starRel_ofSeq.2 (H.mono fun _ hn => hn.1)
    exact ⟨h, (starMapOnN_ofSeq_eq_ofSeq h).2 H⟩
  · rintro ⟨h, H⟩
    exact (starMapOnN_ofSeq_eq_ofSeq h).1 H

/-- **Exercise 3.15(3), partial functions of several arguments.** For a partial function $`f`
of $`m` arguments with domain $`A`, the domain of the extension is the enlargement of the
domain, $`\operatorname{dom} {}^*f = {}^*(\operatorname{dom} f)`, all enlargements being those
of Section 3.14: an $`m`-tuple of elements of the ultrapower lies in $`{}^*A` if and only if
some further element extends it to a member of the enlargement of the graph of $`f`, the graph
being a relation of arity $`m + 1`. By {name}`Goldblatt.starRel_graph_partial` that element is
the value of the extension {name}`Goldblatt.starMapOnN` at the tuple. -/
theorem starRel_dom_partial_snoc {m : ℕ} {A : Set (Fin m → α)} (f : A → α) :
    (starRel A : Set (Fin m → αS)) =
      {x | ∃ y : αS, Fin.snoc (α := fun _ => αS) x y ∈ starRel
        {a : Fin (m + 1) → α | ∃ h : Fin.init a ∈ A, f ⟨Fin.init a, h⟩ = a (Fin.last m)}} := by
  rw [← starRel_dom_snoc]
  congr 1
  ext a
  simp only [Fin.init_snoc, Fin.snoc_last, mem_ofPred_eq]
  exact ⟨fun h => ⟨f ⟨a, h⟩, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩

end Relations

/-!
## 3.16 Is the Hyperreal System Unique?

The construction depends on the choice of the nonprincipal ultrafilter, and there are as many
such ultrafilters on the natural numbers as there are sets of sets of natural numbers
(Chapter 2, {lit}`mk_nonprincipal_ultrafilter`). The book reports that, assuming the continuum
hypothesis, all the resulting ordered fields are isomorphic, and that without that hypothesis
the question is not settled by the usual axioms of set theory. That discussion is not
formalized here: the isomorphism theorem rests on a back-and-forth argument for saturated
real-closed fields of the cardinality of the continuum, which is far outside the scope of this
chapter, and the independence statement is metamathematical.

What can be said precisely at this point is the cardinality of the hyperreals: the same as that
of the reals. Under the continuum hypothesis this is the least uncountable cardinality, which
is the setting of the uniqueness theorem.
-/

section Uniqueness

open Cardinal in
/-- **Section 3.16.** The hyperreals have the cardinality of the continuum: they contain the
reals and are a quotient of the set of real sequences. -/
theorem mk_hyperreal : #ℝ* = 𝔠 := by
  apply le_antisymm
  · calc #ℝ* ≤ #(ℕ → ℝ) := mk_le_of_surjective Hyperreal.ofSeq_surjective
      _ = 𝔠 := by simp [mk_real]
  · rw [← mk_real]
    exact mk_le_of_injective (f := ((↑) : ℝ → ℝ*)) fun _ _ h => ofReal_inj.1 h

/-- **Section 3.16.** The hyperreals are in bijection with the reals, although not by an
isomorphism of ordered fields. -/
theorem nonempty_equiv_hyperreal_real : Nonempty (ℝ* ≃ ℝ) :=
  Cardinal.eq.1 (mk_hyperreal.trans Cardinal.mk_real.symm)

/-- **Section 3.16.** The construction of Section 3.6 works for every ultrafilter on the natural
numbers: the ultrapower of the reals is a linearly ordered field (Mathlib's instances for germs
along an ultrafilter). The choice of ultrafilter matters only up to the isomorphism question
discussed above. -/
noncomputable example (U : Ultrafilter ℕ) : Field (Germ (U : Filter ℕ) ℝ) := inferInstance

end Uniqueness

end Goldblatt
