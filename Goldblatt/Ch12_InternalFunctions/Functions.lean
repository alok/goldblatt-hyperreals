import Goldblatt.Ch11_InternalSets

/-!
# 12 (part 1). Internal Functions: Sections 12.1 and 12.2

This is the first of three parts of Chapter 12 (the overview is on the chapter page
{lit}`Goldblatt.Ch12_InternalFunctions`). It defines the internal function of a sequence of
partial functions, proves that it is determined by almost all terms of the sequence, and works
through the exercises on images, inverse images, composition, injectivity, inverses and
pointwise arithmetic.
-/

universe u v w

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal

/-!
## 12.1 Internal Functions

Chapter 11 turned a sequence of sets into one set of elements of the ultrapower. The same idea
turns a sequence $`(f_n)` of partial functions into one partial function $`[f_n]` on the
ultrapower: its value at the class of $`(r_n)` is the class of $`(f_n(r_n))`, and it is defined
exactly when $`f_n(r_n)` is defined for almost all $`n`. So the domain of $`[f_n]` is the
internal set of the domains. Functions that arise in this way are _internal_; the extension of
a single function is the case of a constant sequence.

Partial functions are Mathlib's {name}`PFun`, so that a function carries its domain with it and
equality of partial functions means what it means in the book: same domain and same values.
As in Chapters 3 and 11 the construction is carried out for arbitrary types with their star
types; the book's case is that of the reals.
-/

section InternalFunctions

variable {α αS : Type u} {β βS : Type v} {γ γS : Type w}
  [StarType α αS] [StarType β βS] [StarType γ γS]

/-- **Section 12.1.** The graph of the internal function of a sequence $`(f_n)` of partial
functions: $`x` is related to $`y` when they are the classes of sequences $`(r_n)` and
$`(s_n)` with $`f_n(r_n) = s_n` for almost all $`n`. -/
def InternalGraph (F : ℕ → α →. β) (x : αS) (y : βS) : Prop :=
  ∃ (r : ℕ → α) (s : ℕ → β), x = ofSeq r ∧ y = ofSeq s ∧
    ∀ᶠ n in hyperfilter ℕ, s n ∈ F n (r n)

/-- **Section 12.1, well-definedness.** Whether $`[r_n]` is related to $`[s_n]` by the graph
does not depend on the representing sequences: it holds if and only if $`f_n(r_n) = s_n` for
almost all $`n`. -/
theorem internalGraph_ofSeq {F : ℕ → α →. β} {r : ℕ → α} {s : ℕ → β} :
    InternalGraph F (ofSeq r : αS) (ofSeq s : βS) ↔
      ∀ᶠ n in hyperfilter ℕ, s n ∈ F n (r n) := by
  constructor
  · rintro ⟨r', s', hr, hs, h⟩
    filter_upwards [Ultrapower.ofSeq_eq_ofSeq.1 hr, Ultrapower.ofSeq_eq_ofSeq.1 hs, h]
      with n h1 h2 h3
    rw [h1, h2]
    exact h3
  · exact fun h => ⟨r, s, rfl, rfl, h⟩

/-- **Section 12.1, well-definedness.** The graph is the graph of a function: an element is
related to at most one element. -/
theorem InternalGraph.unique {F : ℕ → α →. β} {x : αS} {y y' : βS}
    (h : InternalGraph F x y) (h' : InternalGraph F x y') : y = y' := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  obtain ⟨s', rfl⟩ := ofSeq_surjective (α := β) y'
  exact Ultrapower.ofSeq_eq_ofSeq.2
    (((internalGraph_ofSeq.1 h).and (internalGraph_ofSeq.1 h')).mono fun n hn =>
      Part.mem_unique hn.1 hn.2)

/-- **Section 12.1.** The _internal function_ $`[f_n]` of a sequence $`(f_n)` of partial
functions. It is defined at $`[r_n]` when $`f_n(r_n)` is defined for almost all $`n`, and then
$`[f_n]([r_n]) = [f_n(r_n)]`; see {lit}`Goldblatt.ofSeq_mem_internalPFun`. -/
noncomputable def internalPFun (F : ℕ → α →. β) : αS →. βS := fun x =>
  ⟨∃ y, InternalGraph F x y, fun h => h.choose⟩

/-- **Section 12.1.** The value of $`[f_n]` at $`x` is $`y` if and only if $`(x, y)` lies in
the graph. -/
theorem mem_internalPFun {F : ℕ → α →. β} {x : αS} {y : βS} :
    y ∈ internalPFun F x ↔ InternalGraph F x y := by
  constructor
  · rintro ⟨h, rfl⟩
    exact h.choose_spec
  · intro h
    exact ⟨⟨y, h⟩, (Exists.choose_spec (⟨y, h⟩ : ∃ y, InternalGraph F x y)).unique h⟩

/-- **Section 12.1, the almost-all criterion for values.** $`[f_n]([r_n]) = [s_n]` if and only
if $`f_n(r_n)` is defined and equal to $`s_n` for almost all $`n`. -/
theorem ofSeq_mem_internalPFun {F : ℕ → α →. β} {r : ℕ → α} {s : ℕ → β} :
    (ofSeq s : βS) ∈ internalPFun F (ofSeq r : αS) ↔
      ∀ᶠ n in hyperfilter ℕ, s n ∈ F n (r n) :=
  mem_internalPFun.trans internalGraph_ofSeq

/-- **Section 12.1.** The value of $`[f_n]` at the class of $`(r_n)` is $`y` if and only if
$`y` is the class of a sequence $`(s_n)` with $`f_n(r_n) = s_n` for almost all $`n`. -/
theorem mem_internalPFun_ofSeq {F : ℕ → α →. β} {r : ℕ → α} {y : βS} :
    y ∈ internalPFun F (ofSeq r : αS) ↔
      ∃ s : ℕ → β, y = ofSeq s ∧ ∀ᶠ n in hyperfilter ℕ, s n ∈ F n (r n) := by
  constructor
  · intro h
    obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
    exact ⟨s, rfl, ofSeq_mem_internalPFun.1 h⟩
  · rintro ⟨s, rfl, h⟩
    exact ofSeq_mem_internalPFun.2 h

/-- **Section 12.1.** $`[r_n]` lies in the domain of $`[f_n]` if and only if $`r_n` lies in
the domain of $`f_n` for almost all $`n`. -/
theorem ofSeq_mem_dom_internalPFun {F : ℕ → α →. β} {r : ℕ → α} :
    (ofSeq r : αS) ∈ (internalPFun F : αS →. βS).Dom ↔
      ∀ᶠ n in hyperfilter ℕ, r n ∈ (F n).Dom := by
  rw [PFun.mem_dom]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨s, rfl, h⟩ := mem_internalPFun_ofSeq.1 hy
    exact h.mono fun n hn => (PFun.mem_dom _ _).2 ⟨s n, hn⟩
  · intro h
    obtain ⟨s, hs⟩ := exists_seq_of_almostAll_exists
      (h.mono fun n hn => (PFun.mem_dom _ _).1 hn)
    exact ⟨ofSeq s, ofSeq_mem_internalPFun.2 hs⟩

/-- **Section 12.1.** The domain of the internal function $`[f_n]` is the internal set of the
domains: $`\operatorname{dom}[f_n] = [\operatorname{dom} f_n]`. -/
theorem dom_internalPFun (F : ℕ → α →. β) :
    (internalPFun F : αS →. βS).Dom = internalSet fun n => (F n).Dom := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [ofSeq_mem_dom_internalPFun, ofSeq_mem_internalSet]

/-- **Section 12.1.** A partial function between star types is _internal_ if it is
$`[f_n]` for some sequence $`(f_n)` of partial functions between the underlying types. The
underlying types are explicit arguments; for hyperreal functions use
{lit}`Goldblatt.IsInternalFun`. -/
def IsInternalPFun (α : Type u) (β : Type v) {αS : Type u} {βS : Type v}
    [StarType α αS] [StarType β βS] (f : αS →. βS) : Prop :=
  ∃ F : ℕ → α →. β, f = internalPFun F

/-- **Section 12.1.** A partial function from the hyperreals to the hyperreals is _internal_
if it is $`[f_n]` for a sequence $`(f_n)` of partial real functions. -/
abbrev IsInternalFun (f : ℝ* →. ℝ*) : Prop := IsInternalPFun ℝ ℝ f

/-- The function $`[f_n]` is internal. -/
theorem isInternalPFun_internalPFun (F : ℕ → α →. β) :
    IsInternalPFun α β (internalPFun F : αS →. βS) :=
  ⟨F, rfl⟩

/-- **Section 12.1.** The domain of an internal function is an internal set. -/
theorem IsInternalPFun.isInternalSet_dom {f : αS →. βS} (hf : IsInternalPFun α β f) :
    IsInternalSet α f.Dom := by
  obtain ⟨F, rfl⟩ := hf
  exact ⟨_, dom_internalPFun F⟩

/-- **Section 12.1.** The internal function of a sequence $`(f_n)` of _total_ functions, as a
total function on the star type: $`[f_n]([r_n]) = [f_n(r_n)]`
({lit}`Goldblatt.internalMap_ofSeq`). -/
noncomputable def internalMap (f : ℕ → α → β) (x : αS) : βS :=
  ofSeq fun n => f n ((ofSeq_surjective (α := α) x).choose n)

/-- **Section 12.1.** $`[f_n]([r_n]) = [f_n(r_n)]` for a sequence of total functions. -/
theorem internalMap_ofSeq (f : ℕ → α → β) (r : ℕ → α) :
    (internalMap f (ofSeq r : αS) : βS) = ofSeq fun n => f n (r n) := by
  have h := (ofSeq_surjective (α := α) (ofSeq r : αS)).choose_spec
  exact Ultrapower.ofSeq_eq_ofSeq.2
    ((Ultrapower.ofSeq_eq_ofSeq.1 h).mono fun n hn => congrArg (f n) hn)

/-- **Section 12.1.** For real functions: $`[f_n]([r_n]) = [f_n(r_n)]`. -/
theorem internalMap_hyperreal_ofSeq (f : ℕ → ℝ → ℝ) (r : ℕ → ℝ) :
    internalMap f (Hyperreal.ofSeq r) = Hyperreal.ofSeq fun n => f n (r n) :=
  internalMap_ofSeq f r

/-- **Section 12.1.** The internal function of a sequence of total functions is the total
function {lit}`Goldblatt.internalMap`, regarded as a partial function. -/
theorem internalPFun_coe (f : ℕ → α → β) :
    (internalPFun (fun n => (f n : α →. β)) : αS →. βS) = (internalMap f : αS → βS) := by
  refine PFun.ext fun x y => ?_
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [ofSeq_mem_internalPFun, PFun.coe_val, Part.mem_some_iff, internalMap_ofSeq,
    Ultrapower.ofSeq_eq_ofSeq]
  exact eventually_congr (Eventually.of_forall fun n => by
    rw [PFun.coe_val, Part.mem_some_iff])

/-- **Section 12.1.** A total internal function is internal as a partial function. -/
theorem isInternalPFun_internalMap (f : ℕ → α → β) :
    IsInternalPFun α β ((internalMap f : αS → βS) : αS →. βS) :=
  ⟨_, (internalPFun_coe f).symm⟩

/-- **Section 12.1, constant sequences.** The internal function of the constant sequence with
value a total function $`f` is the extension $`{}^*f` of Section 3.11. -/
theorem internalMap_const (f : α → β) : (internalMap (fun _ => f) : αS → βS) = ⋆f := by
  funext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [internalMap_ofSeq, starMap_ofSeq]
  rfl

/-- **Section 12.1, constant sequences.** The extension $`{}^*f` of a function is an internal
function. -/
theorem isInternalPFun_starMap (f : α → β) :
    IsInternalPFun α β ((⋆f : αS → βS) : αS →. βS) := by
  rw [← internalMap_const]
  exact isInternalPFun_internalMap _

/-- **Section 12.1.** A function defined on a set $`A`, as a partial function with domain
$`A`. -/
def pfunOn {X : Type*} {Y : Type*} (A : Set X) (f : A → Y) : X →. Y := fun a =>
  ⟨a ∈ A, fun h => f ⟨a, h⟩⟩

/-- The value of a function on $`A`, as a partial function, at $`a` is $`b` if and only if
$`a \in A` and $`f(a) = b`. -/
theorem mem_pfunOn {X : Type*} {Y : Type*} {A : Set X} {f : A → Y} {a : X} {b : Y} :
    b ∈ pfunOn A f a ↔ ∃ h : a ∈ A, f ⟨a, h⟩ = b :=
  Part.mem_mk_iff

/-- The domain of a function on $`A`, as a partial function, is $`A`. -/
theorem dom_pfunOn {X : Type*} {Y : Type*} (A : Set X) (f : A → Y) : (pfunOn A f).Dom = A :=
  rfl

/-- **Section 12.1, constant sequences.** The internal function of the constant sequence with
value a partial function $`f` defined on $`A` is the extension
$`{}^*f : {}^*A \to {}^*\mathbb R` of Section 3.13: its domain is the enlargement of $`A`
({lit}`Goldblatt.dom_internalPFun`), and its values are those of {lit}`Goldblatt.starMapOn`. -/
theorem starMapOn_mem_internalPFun_const (A : Set α) (f : A → β) (x : (⋆A : Set αS)) :
    (starMapOn A f x : βS) ∈ internalPFun (fun _ : ℕ => pfunOn A f) (x : αS) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, hs⟩ := ofSeq_surjective (α := β) (starMapOn A f ⟨ofSeq r, hx⟩ : βS)
  rw [← hs, ofSeq_mem_internalPFun]
  exact ((starMapOn_ofSeq_eq_ofSeq hx).1 hs.symm).mono fun n hn => mem_pfunOn.2 hn

/-- **Section 12.1, constant sequences.** The internal function of the constant sequence with
value the restriction of $`f` to $`A` is the restriction of $`{}^*f` to $`{}^*A`. -/
theorem mem_internalPFun_const_res {f : α → β} {A : Set α} {x : αS} {y : βS} :
    y ∈ internalPFun (fun _ : ℕ => PFun.res f A) x ↔ x ∈ (⋆A : Set αS) ∧ ⋆f x = y := by
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [ofSeq_mem_internalPFun, starSet_eq_internalSet, ofSeq_mem_internalSet,
    starMap_ofSeq_eq_ofSeq, ← almostAll_and]
  exact eventually_congr (Eventually.of_forall fun n => PFun.mem_res _ _ _ _)

/-- **Theorem 12.1.1.** Two sequences of partial functions define the same internal function
if and only if their terms are equal for almost all indices:
$`[f_n] = [g_n]` exactly when $`\{n : f_n = g_n\}` is large. If the functions differ at almost
all indices, choosing a point where they differ at each such index gives a point of the
ultrapower where $`[f_n]` and $`[g_n]` differ (in domain or in value). -/
theorem internalPFun_eq_iff {F G : ℕ → α →. β} :
    (internalPFun F : αS →. βS) = internalPFun G ↔ ∀ᶠ n in hyperfilter ℕ, F n = G n := by
  constructor
  · intro h
    by_contra hJ
    rw [← almostAll_not] at hJ
    have hex : ∀ᶠ n in hyperfilter ℕ, ∃ p : α × β,
        (p.2 ∈ F n p.1 ∧ p.2 ∉ G n p.1) ∨ (p.2 ∈ G n p.1 ∧ p.2 ∉ F n p.1) := by
      refine hJ.mono fun n hn => ?_
      by_contra hc
      refine hn (PFun.ext fun a b => ?_)
      by_contra h'
      refine hc ⟨(a, b), ?_⟩
      by_cases hb : b ∈ F n a
      · exact Or.inl ⟨hb, fun hg => h' ⟨fun _ => hg, fun _ => hb⟩⟩
      · exact Or.inr ⟨by_contra fun hg => h' ⟨fun h => absurd h hb, fun h => absurd h hg⟩, hb⟩
    obtain ⟨p, hp⟩ := exists_seq_of_almostAll_exists hex
    rcases almostAll_or.1 hp with h1 | h1
    · have hm : (ofSeq (fun n => (p n).2) : βS) ∈
          internalPFun F (ofSeq (fun n => (p n).1) : αS) :=
        ofSeq_mem_internalPFun.2 (h1.mono fun n hn => hn.1)
      rw [h] at hm
      exact almostAll_not.1 (h1.mono fun n hn => hn.2) (ofSeq_mem_internalPFun.1 hm)
    · have hm : (ofSeq (fun n => (p n).2) : βS) ∈
          internalPFun G (ofSeq (fun n => (p n).1) : αS) :=
        ofSeq_mem_internalPFun.2 (h1.mono fun n hn => hn.1)
      rw [← h] at hm
      exact almostAll_not.1 (h1.mono fun n hn => hn.2) (ofSeq_mem_internalPFun.1 hm)
  · intro h
    refine PFun.ext fun x y => ?_
    obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
    obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
    rw [ofSeq_mem_internalPFun, ofSeq_mem_internalPFun]
    exact eventually_congr (h.mono fun n hn => by rw [hn])

/-- **Theorem 12.1.1**, the direction used in practice: sequences of partial functions that
agree at almost all indices define the same internal function. -/
theorem internalPFun_congr {F G : ℕ → α →. β} (h : ∀ᶠ n in hyperfilter ℕ, F n = G n) :
    (internalPFun F : αS →. βS) = internalPFun G :=
  internalPFun_eq_iff.2 h

/-- **Theorem 12.1.1**, negated: $`[f_n] \ne [g_n]` if and only if $`f_n \ne g_n` for almost
all $`n`. -/
theorem internalPFun_ne_iff {F G : ℕ → α →. β} :
    (internalPFun F : αS →. βS) ≠ internalPFun G ↔ ∀ᶠ n in hyperfilter ℕ, F n ≠ G n := by
  rw [Ne, internalPFun_eq_iff, ← almostAll_not]

/-- **Section 12.1, changing the defining sequence.** If almost all terms of a sequence of
partial functions have a property that can be satisfied at every index, then the internal
function is also defined by a sequence all of whose terms have the property. -/
theorem internalPFun_exists_rep_forall {F : ℕ → α →. β} {P : ℕ → (α →. β) → Prop}
    (h : ∀ᶠ n in hyperfilter ℕ, P n (F n)) (D : ℕ → α →. β) (hD : ∀ n, P n (D n)) :
    ∃ F' : ℕ → α →. β, (internalPFun F' : αS →. βS) = internalPFun F ∧ ∀ n, P n (F' n) := by
  classical
  refine ⟨fun n => if P n (F n) then F n else D n,
    internalPFun_congr (h.mono fun n hn => by simp only [hn, ↓reduceIte]), fun n => ?_⟩
  dsimp only
  split_ifs with hn
  exacts [hn, hD n]

end InternalFunctions

/-!
## 12.2 Exercises on Properties of Internal Functions

The exercises say that the operations on functions commute with the passage from a sequence to
its internal function, and so preserve internality: image and inverse image of internal sets,
composition, inverse, and pointwise sum and product. Each is proved by the same two moves:
represent the elements by sequences, and compare the almost-all criteria. Injectivity of
$`[f_n]` is decided by almost all $`f_n`, in the same way as equality was in Theorem 12.1.1.
-/

section Exercises

variable {α αS : Type u} {β βS : Type v} {γ γS : Type w}
  [StarType α αS] [StarType β βS] [StarType γ γS]

/-- **Exercise 12.2(1).** The image of an internal set under an internal function is the
internal set of the images: $`[f_n]([A_n]) = [f_n(A_n)]`. The book assumes that $`[A_n]` is
included in the domain; with the image of a partial function taken over the part of the set
where the function is defined, the hypothesis is not needed. -/
theorem image_internalPFun (F : ℕ → α →. β) (A : ℕ → Set α) :
    (internalPFun F : αS →. βS).image (internalSet A) =
      internalSet fun n => (F n).image (A n) := by
  ext y
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [PFun.mem_image, ofSeq_mem_internalSet]
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
    exact ((ofSeq_mem_internalSet.1 hx).and (ofSeq_mem_internalPFun.1 hy)).mono fun n hn =>
      (PFun.mem_image _ _ _).2 ⟨r n, hn.1, hn.2⟩
  · intro h
    obtain ⟨r, hr⟩ := exists_seq_of_almostAll_exists
      (h.mono fun n hn => (PFun.mem_image _ _ _).1 hn)
    exact ⟨ofSeq r, ofSeq_mem_internalSet.2 (hr.mono fun n hn => hn.1),
      ofSeq_mem_internalPFun.2 (hr.mono fun n hn => hn.2)⟩

/-- **Exercise 12.2(1).** The image of an internal set under an internal function is
internal. -/
theorem IsInternalPFun.isInternalSet_image {f : αS →. βS} (hf : IsInternalPFun α β f)
    {X : Set αS} (hX : IsInternalSet α X) : IsInternalSet β (f.image X) := by
  obtain ⟨F, rfl⟩ := hf
  obtain ⟨A, rfl⟩ := hX
  exact ⟨_, image_internalPFun F A⟩

/-- **Exercise 12.2(1)**, for the range: the range of $`[f_n]` is the internal set of the
ranges. -/
theorem ran_internalPFun (F : ℕ → α →. β) :
    (internalPFun F : αS →. βS).ran = internalSet fun n => (F n).ran := by
  have h1 : ∀ g : α →. β, g.ran = g.image univ := fun g => by
    ext y
    simp only [PFun.ran, PFun.mem_image, mem_univ, true_and, mem_ofPred_eq]
  have h2 : (internalPFun F : αS →. βS).ran = (internalPFun F : αS →. βS).image univ := by
    ext y
    simp only [PFun.ran, PFun.mem_image, mem_univ, true_and, mem_ofPred_eq]
  have h3 : (univ : Set αS) = internalSet fun _ : ℕ => (univ : Set α) := by
    rw [← starSet_eq_internalSet, starSet_univ]
  rw [h2, h3, image_internalPFun]
  simp only [h1]

/-- **Exercise 12.2(1)**, for the range: the range of an internal function is internal. -/
theorem IsInternalPFun.isInternalSet_ran {f : αS →. βS} (hf : IsInternalPFun α β f) :
    IsInternalSet β f.ran := by
  obtain ⟨F, rfl⟩ := hf
  exact ⟨_, ran_internalPFun F⟩

/-- **Exercise 12.2(1)**, for total functions: the image of $`[A_n]` under the internal
function of a sequence of total functions is $`[f_n(A_n)]`. -/
theorem image_internalMap (f : ℕ → α → β) (A : ℕ → Set α) :
    (internalMap f : αS → βS) '' internalSet A = internalSet fun n => f n '' A n := by
  have h := image_internalPFun (αS := αS) (βS := βS) (fun n => (f n : α →. β)) A
  rw [internalPFun_coe] at h
  have h1 : ∀ (X : Type u) (Y : Type v) (g : X → Y) (s : Set X),
      (g : X →. Y).image s = g '' s := fun X Y g s => by
    ext y
    simp only [PFun.mem_image, PFun.coe_val, Part.mem_some_iff, mem_image, eq_comm]
  rw [h1] at h
  rw [h]
  simp only [h1]

/-- **Exercise 12.2(1)**, for extensions: the image of an internal set under the extension
$`{}^*f` of a function is internal. -/
theorem IsInternalSet.image_starMap {X : Set αS} (hX : IsInternalSet α X) (f : α → β) :
    IsInternalSet β ((⋆f : αS → βS) '' X) := by
  obtain ⟨A, rfl⟩ := hX
  rw [← internalMap_const, image_internalMap]
  exact ⟨_, rfl⟩

/-- **Exercise 12.2(2).** The inverse image of an internal set under an internal function is
the internal set of the inverse images: $`[f_n]^{-1}([B_n]) = [f_n^{-1}(B_n)]`. -/
theorem preimage_internalPFun (F : ℕ → α →. β) (B : ℕ → Set β) :
    (internalPFun F : αS →. βS).preimage (internalSet B) =
      internalSet fun n => (F n).preimage (B n) := by
  ext x
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  rw [PFun.mem_preimage, ofSeq_mem_internalSet]
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
    exact ((ofSeq_mem_internalSet.1 hy).and (ofSeq_mem_internalPFun.1 hxy)).mono fun n hn =>
      (PFun.mem_preimage _ _ _).2 ⟨s n, hn.1, hn.2⟩
  · intro h
    obtain ⟨s, hs⟩ := exists_seq_of_almostAll_exists
      (h.mono fun n hn => (PFun.mem_preimage _ _ _).1 hn)
    exact ⟨ofSeq s, ofSeq_mem_internalSet.2 (hs.mono fun n hn => hn.1),
      ofSeq_mem_internalPFun.2 (hs.mono fun n hn => hn.2)⟩

/-- **Exercise 12.2(2).** The inverse image of an internal set under an internal function is
internal. -/
theorem IsInternalPFun.isInternalSet_preimage {f : αS →. βS} (hf : IsInternalPFun α β f)
    {Y : Set βS} (hY : IsInternalSet β Y) : IsInternalSet α (f.preimage Y) := by
  obtain ⟨F, rfl⟩ := hf
  obtain ⟨B, rfl⟩ := hY
  exact ⟨_, preimage_internalPFun F B⟩

/-- The value of a composition of partial functions at $`x` is $`z` if and only if $`z` is the
value of the second function at the value of the first. -/
theorem mem_pfun_comp {X : Type*} {Y : Type*} {Z : Type*} {g : Y →. Z} {f : X →. Y} {x : X}
    {z : Z} : z ∈ g.comp f x ↔ ∃ y ∈ f x, z ∈ g y :=
  Part.mem_bind_iff

/-- **Exercise 12.2(3).** The composition of internal functions is the internal function of
the compositions: $`[g_n] \circ [f_n] = [g_n \circ f_n]`. The composition of partial functions
is defined wherever it makes sense, so the book's hypothesis that the range of the first
function lies in the domain of the second is not needed. -/
theorem comp_internalPFun (G : ℕ → β →. γ) (F : ℕ → α →. β) :
    (internalPFun G : βS →. γS).comp (internalPFun F : αS →. βS) =
      internalPFun fun n => (G n).comp (F n) := by
  refine PFun.ext fun x z => ?_
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨t, rfl⟩ := ofSeq_surjective (α := γ) z
  rw [mem_pfun_comp, ofSeq_mem_internalPFun]
  constructor
  · rintro ⟨y, hy, hz⟩
    obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
    exact ((ofSeq_mem_internalPFun.1 hy).and (ofSeq_mem_internalPFun.1 hz)).mono fun n hn =>
      mem_pfun_comp.2 ⟨s n, hn.1, hn.2⟩
  · intro h
    obtain ⟨s, hs⟩ := exists_seq_of_almostAll_exists (h.mono fun n hn => mem_pfun_comp.1 hn)
    exact ⟨ofSeq s, ofSeq_mem_internalPFun.2 (hs.mono fun n hn => hn.1),
      ofSeq_mem_internalPFun.2 (hs.mono fun n hn => hn.2)⟩

/-- **Exercise 12.2(3).** The composition of internal functions is internal. -/
theorem IsInternalPFun.comp {g : βS →. γS} {f : αS →. βS} (hg : IsInternalPFun β γ g)
    (hf : IsInternalPFun α β f) : IsInternalPFun α γ (g.comp f) := by
  obtain ⟨G, rfl⟩ := hg
  obtain ⟨F, rfl⟩ := hf
  exact ⟨_, comp_internalPFun G F⟩

/-- **Section 12.2.** The restriction of a partial function $`f` to a set $`A`: defined on
the part of $`A` where $`f` is defined. -/
def prestrict {X : Type*} {Y : Type*} (f : X →. Y) (A : Set X) : X →. Y := fun a =>
  ⟨a ∈ A ∧ (f a).Dom, fun h => (f a).get h.2⟩

/-- The value of the restriction of $`f` to $`A` at $`a` is $`b` if and only if $`a \in A`
and $`f(a) = b`. -/
theorem mem_prestrict {X : Type*} {Y : Type*} {f : X →. Y} {A : Set X} {a : X} {b : Y} :
    b ∈ prestrict f A a ↔ a ∈ A ∧ b ∈ f a := by
  rw [prestrict, Part.mem_mk_iff]
  constructor
  · rintro ⟨h, hb⟩
    exact ⟨h.1, h.2, hb⟩
  · rintro ⟨h1, h2, hb⟩
    exact ⟨⟨h1, h2⟩, hb⟩

/-- The domain of the restriction of $`f` to $`A` is the part of $`A` in the domain of
$`f`. -/
theorem dom_prestrict {X : Type*} {Y : Type*} (f : X →. Y) (A : Set X) :
    (prestrict f A).Dom = A ∩ f.Dom :=
  rfl

/-- **Section 12.2.** The restriction of an internal function to an internal set is the
internal function of the restrictions: $`[f_n] \restriction [A_n] = [f_n \restriction A_n]`. -/
theorem prestrict_internalPFun (F : ℕ → α →. β) (A : ℕ → Set α) :
    prestrict (internalPFun F : αS →. βS) (internalSet A) =
      internalPFun fun n => prestrict (F n) (A n) := by
  refine PFun.ext fun x y => ?_
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [mem_prestrict, ofSeq_mem_internalPFun, ofSeq_mem_internalPFun, ofSeq_mem_internalSet,
    ← almostAll_and]
  exact eventually_congr (Eventually.of_forall fun n => mem_prestrict.symm)

/-- **Section 12.2.** The restriction of an internal function to an internal set is
internal. -/
theorem IsInternalPFun.prestrict {f : αS →. βS} (hf : IsInternalPFun α β f) {X : Set αS}
    (hX : IsInternalSet α X) : IsInternalPFun α β (prestrict f X) := by
  obtain ⟨F, rfl⟩ := hf
  obtain ⟨A, rfl⟩ := hX
  exact ⟨_, prestrict_internalPFun F A⟩

/-- **Exercise 12.2(4), definition.** A partial function is _injective_ if no value is taken
at two different points of the domain. -/
def PInjective {X : Type*} {Y : Type*} (f : X →. Y) : Prop :=
  ∀ ⦃a a' : X⦄ ⦃b : Y⦄, b ∈ f a → b ∈ f a' → a = a'

/-- A total function is injective as a partial function if and only if it is injective. -/
theorem pinjective_coe_iff {X : Type*} {Y : Type*} {f : X → Y} :
    PInjective (f : X →. Y) ↔ Function.Injective f := by
  constructor
  · intro h a a' haa'
    exact h (b := f a) (by rw [PFun.coe_val]; exact Part.mem_some _)
      (by rw [PFun.coe_val, haa']; exact Part.mem_some _)
  · intro h a a' b hb hb'
    rw [PFun.coe_val, Part.mem_some_iff] at hb hb'
    exact h (hb.symm.trans hb')

/-- **Exercise 12.2(4).** The internal function $`[f_n]` is injective if and only if $`f_n` is
injective for almost all $`n`. -/
theorem pinjective_internalPFun_iff {F : ℕ → α →. β} :
    PInjective (internalPFun F : αS →. βS) ↔ ∀ᶠ n in hyperfilter ℕ, PInjective (F n) := by
  constructor
  · intro h
    by_contra hJ
    rw [← almostAll_not] at hJ
    have hex : ∀ᶠ n in hyperfilter ℕ, ∃ p : α × α × β,
        p.2.2 ∈ F n p.1 ∧ p.2.2 ∈ F n p.2.1 ∧ p.1 ≠ p.2.1 := by
      refine hJ.mono fun n hn => ?_
      by_contra hc
      push Not at hc
      exact hn fun a a' b hb hb' => hc (a, a', b) hb hb'
    obtain ⟨p, hp⟩ := exists_seq_of_almostAll_exists hex
    have h1 : (ofSeq (fun n => (p n).2.2) : βS) ∈
        internalPFun F (ofSeq (fun n => (p n).1) : αS) :=
      ofSeq_mem_internalPFun.2 (hp.mono fun n hn => hn.1)
    have h2 : (ofSeq (fun n => (p n).2.2) : βS) ∈
        internalPFun F (ofSeq (fun n => (p n).2.1) : αS) :=
      ofSeq_mem_internalPFun.2 (hp.mono fun n hn => hn.2.1)
    exact Ultrapower.ofSeq_ne_ofSeq.2 (hp.mono fun n hn => hn.2.2) (h h1 h2)
  · intro h x x' y hy hy'
    obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
    obtain ⟨r', rfl⟩ := ofSeq_surjective (α := α) x'
    obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
    refine Ultrapower.ofSeq_eq_ofSeq.2 ?_
    filter_upwards [h, ofSeq_mem_internalPFun.1 hy, ofSeq_mem_internalPFun.1 hy']
      with n hn h1 h2 using hn h1 h2


/-- **Exercise 12.2(4)**, for total functions: the internal function of a sequence of total
functions is injective if and only if almost all of the functions are. -/
theorem injective_internalMap_iff {f : ℕ → α → β} :
    Function.Injective (internalMap f : αS → βS) ↔
      ∀ᶠ n in hyperfilter ℕ, Function.Injective (f n) := by
  rw [← pinjective_coe_iff, ← internalPFun_coe, pinjective_internalPFun_iff]
  exact eventually_congr (Eventually.of_forall fun n => pinjective_coe_iff)

/-- **Exercise 12.2(5), definition.** The inverse of a partial function: defined at the values
of the function, where it returns a point at which the value is taken. For an injective
function this point is unique ({lit}`Goldblatt.mem_pinv`). -/
noncomputable def pinv {X : Type*} {Y : Type*} (f : X →. Y) : Y →. X := fun b =>
  ⟨∃ a, b ∈ f a, fun h => h.choose⟩

/-- **Exercise 12.2(5).** For an injective partial function $`f`, the inverse takes the value
$`a` at $`b` if and only if $`f(a) = b`. -/
theorem mem_pinv {X : Type*} {Y : Type*} {f : X →. Y} (hf : PInjective f) {a : X} {b : Y} :
    a ∈ pinv f b ↔ b ∈ f a := by
  rw [pinv, Part.mem_mk_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact h.choose_spec
  · intro h
    exact ⟨⟨a, h⟩, hf (Exists.choose_spec (⟨a, h⟩ : ∃ a, b ∈ f a)) h⟩

/-- The domain of the inverse is the range. -/
theorem dom_pinv {X : Type*} {Y : Type*} (f : X →. Y) : (pinv f).Dom = f.ran :=
  rfl

/-- **Exercise 12.2(5).** The inverse of an injective partial function is injective. -/
theorem PInjective.pinv {X : Type*} {Y : Type*} {f : X →. Y} (hf : PInjective f) :
    PInjective (pinv f) := fun _ _ _ h h' =>
  Part.mem_unique ((mem_pinv hf).1 h) ((mem_pinv hf).1 h')

/-- **Exercise 12.2(5).** The inverse of an injective internal function is the internal
function of the inverses: $`[f_n]^{-1} = [f_n^{-1}]`. By Exercise 12.2(4) almost all $`f_n`
are injective, and by Theorem 12.1.1 the remaining ones do not matter. -/
theorem pinv_internalPFun {F : ℕ → α →. β} (h : PInjective (internalPFun F : αS →. βS)) :
    pinv (internalPFun F : αS →. βS) = internalPFun fun n => pinv (F n) := by
  refine PFun.ext fun y x => ?_
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨s, rfl⟩ := ofSeq_surjective (α := β) y
  rw [mem_pinv h, ofSeq_mem_internalPFun, ofSeq_mem_internalPFun]
  exact eventually_congr ((pinjective_internalPFun_iff.1 h).mono fun n hn => (mem_pinv hn).symm)

/-- **Exercise 12.2(5).** The inverse of an injective internal function is internal. -/
theorem IsInternalPFun.pinv {f : αS →. βS} (hf : IsInternalPFun α β f) (h : PInjective f) :
    IsInternalPFun β α (pinv f) := by
  obtain ⟨F, rfl⟩ := hf
  exact ⟨_, pinv_internalPFun h⟩

end Exercises

section Arithmetic

variable {α αS : Type u} [StarType α αS]

/-- **Exercise 12.2(6), definition.** The pointwise sum of two partial functions, defined
where both are. -/
def padd {X : Type*} {M : Type*} [Add M] (f g : X →. M) : X →. M := fun a =>
  (f a).bind fun y => (g a).map fun z => y + z

/-- **Exercise 12.2(6), definition.** The pointwise product of two partial functions, defined
where both are. -/
def pmul {X : Type*} {M : Type*} [Mul M] (f g : X →. M) : X →. M := fun a =>
  (f a).bind fun y => (g a).map fun z => y * z

/-- The value of a pointwise sum at $`a` is $`c` if and only if $`c = f(a) + g(a)`. -/
theorem mem_padd {X : Type*} {M : Type*} [Add M] {f g : X →. M} {a : X} {c : M} :
    c ∈ padd f g a ↔ ∃ y ∈ f a, ∃ z ∈ g a, y + z = c := by
  simp only [padd, Part.mem_bind_iff, Part.mem_map_iff]

/-- The value of a pointwise product at $`a` is $`c` if and only if $`c = f(a) g(a)`. -/
theorem mem_pmul {X : Type*} {M : Type*} [Mul M] {f g : X →. M} {a : X} {c : M} :
    c ∈ pmul f g a ↔ ∃ y ∈ f a, ∃ z ∈ g a, y * z = c := by
  simp only [pmul, Part.mem_bind_iff, Part.mem_map_iff]

/-- The domain of a pointwise sum is the intersection of the domains. -/
theorem dom_padd {X : Type*} {M : Type*} [Add M] (f g : X →. M) :
    (padd f g).Dom = f.Dom ∩ g.Dom := by
  ext a
  simp only [PFun.mem_dom, mem_padd, mem_inter_iff]
  constructor
  · rintro ⟨_, y, hy, z, hz, -⟩
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    exact ⟨_, y, hy, z, hz, rfl⟩

/-- The domain of a pointwise product is the intersection of the domains. -/
theorem dom_pmul {X : Type*} {M : Type*} [Mul M] (f g : X →. M) :
    (pmul f g).Dom = f.Dom ∩ g.Dom := by
  ext a
  simp only [PFun.mem_dom, mem_pmul, mem_inter_iff]
  constructor
  · rintro ⟨_, y, hy, z, hz, -⟩
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    exact ⟨_, y, hy, z, hz, rfl⟩

/-- **Exercise 12.2(6).** The pointwise sum of internal hyperreal-valued functions is the
internal function of the pointwise sums: $`[f_n] + [g_n] = [f_n + g_n]`. The sum is defined on
the intersection of the domains, so the book's hypothesis that the domains agree is not
needed. -/
theorem padd_internalPFun (F G : ℕ → α →. ℝ) :
    padd (internalPFun F : αS →. ℝ*) (internalPFun G) = internalPFun fun n => padd (F n) (G n) := by
  refine PFun.ext fun x c => ?_
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨t, rfl⟩ := hyperreal_exists_rep c
  change _ ↔ (ofSeq t : ℝ*) ∈ _
  rw [mem_padd, ofSeq_mem_internalPFun]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
    obtain ⟨s', rfl⟩ := hyperreal_exists_rep z
    have h1 : ∀ᶠ n in hyperfilter ℕ, s n ∈ F n (r n) := ofSeq_mem_internalPFun.1 hy
    have h2 : ∀ᶠ n in hyperfilter ℕ, s' n ∈ G n (r n) := ofSeq_mem_internalPFun.1 hz
    have h3 : ∀ᶠ n in hyperfilter ℕ, s n + s' n = t n := ofSeq_eq_ofSeq_iff.1 hyz
    filter_upwards [h1, h2, h3] with n k1 k2 k3 using mem_padd.2 ⟨_, k1, _, k2, k3⟩
  · intro h
    obtain ⟨p, hp⟩ := exists_seq_of_almostAll_exists (β := ℝ × ℝ) (p := fun n p =>
      p.1 ∈ F n (r n) ∧ p.2 ∈ G n (r n) ∧ p.1 + p.2 = t n) (h.mono fun n hn => by
        obtain ⟨y, hy, z, hz, hyz⟩ := mem_padd.1 hn
        exact ⟨(y, z), hy, hz, hyz⟩)
    refine ⟨Hyperreal.ofSeq fun n => (p n).1, ?_, Hyperreal.ofSeq fun n => (p n).2, ?_, ?_⟩
    · exact ofSeq_mem_internalPFun.2 (hp.mono fun n hn => hn.1)
    · exact ofSeq_mem_internalPFun.2 (hp.mono fun n hn => hn.2.1)
    · exact ofSeq_eq_ofSeq_iff.2 (hp.mono fun n hn => hn.2.2)

/-- **Exercise 12.2(6).** The pointwise product of internal hyperreal-valued functions is the
internal function of the pointwise products: $`[f_n] \cdot [g_n] = [f_n \cdot g_n]`. -/
theorem pmul_internalPFun (F G : ℕ → α →. ℝ) :
    pmul (internalPFun F : αS →. ℝ*) (internalPFun G) = internalPFun fun n => pmul (F n) (G n) := by
  refine PFun.ext fun x c => ?_
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨t, rfl⟩ := hyperreal_exists_rep c
  change _ ↔ (ofSeq t : ℝ*) ∈ _
  rw [mem_pmul, ofSeq_mem_internalPFun]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
    obtain ⟨s', rfl⟩ := hyperreal_exists_rep z
    have h1 : ∀ᶠ n in hyperfilter ℕ, s n ∈ F n (r n) := ofSeq_mem_internalPFun.1 hy
    have h2 : ∀ᶠ n in hyperfilter ℕ, s' n ∈ G n (r n) := ofSeq_mem_internalPFun.1 hz
    have h3 : ∀ᶠ n in hyperfilter ℕ, s n * s' n = t n := ofSeq_eq_ofSeq_iff.1 hyz
    filter_upwards [h1, h2, h3] with n k1 k2 k3 using mem_pmul.2 ⟨_, k1, _, k2, k3⟩
  · intro h
    obtain ⟨p, hp⟩ := exists_seq_of_almostAll_exists (β := ℝ × ℝ) (p := fun n p =>
      p.1 ∈ F n (r n) ∧ p.2 ∈ G n (r n) ∧ p.1 * p.2 = t n) (h.mono fun n hn => by
        obtain ⟨y, hy, z, hz, hyz⟩ := mem_pmul.1 hn
        exact ⟨(y, z), hy, hz, hyz⟩)
    refine ⟨Hyperreal.ofSeq fun n => (p n).1, ?_, Hyperreal.ofSeq fun n => (p n).2, ?_, ?_⟩
    · exact ofSeq_mem_internalPFun.2 (hp.mono fun n hn => hn.1)
    · exact ofSeq_mem_internalPFun.2 (hp.mono fun n hn => hn.2.1)
    · exact ofSeq_eq_ofSeq_iff.2 (hp.mono fun n hn => hn.2.2)

/-- **Exercise 12.2(6).** A hyperreal multiple of an internal hyperreal-valued function is the
internal function of the multiples: $`[c_n] \cdot [f_n] = [c_n f_n]`. -/
theorem map_mul_left_internalPFun (c : ℕ → ℝ) (F : ℕ → α →. ℝ) :
    (internalPFun F : αS →. ℝ*).map (fun y => Hyperreal.ofSeq c * y) =
      internalPFun fun n => (F n).map fun y => c n * y := by
  refine PFun.ext fun x d => ?_
  obtain ⟨r, rfl⟩ := ofSeq_surjective (α := α) x
  obtain ⟨t, rfl⟩ := hyperreal_exists_rep d
  change _ ↔ (ofSeq t : ℝ*) ∈ _
  rw [PFun.mem_map, ofSeq_mem_internalPFun]
  constructor
  · rintro ⟨y, hy, hyz⟩
    obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
    have h1 : ∀ᶠ n in hyperfilter ℕ, s n ∈ F n (r n) := ofSeq_mem_internalPFun.1 hy
    have h3 : ∀ᶠ n in hyperfilter ℕ, c n * s n = t n := ofSeq_eq_ofSeq_iff.1 hyz
    filter_upwards [h1, h3] with n k1 k3 using (PFun.mem_map _ _ _ _).2 ⟨_, k1, k3⟩
  · intro h
    obtain ⟨s, hs⟩ := exists_seq_of_almostAll_exists
      (h.mono fun n hn => (PFun.mem_map _ _ _ _).1 hn)
    refine ⟨Hyperreal.ofSeq s, ?_, ?_⟩
    · exact ofSeq_mem_internalPFun.2 (hs.mono fun n hn => hn.1)
    · exact ofSeq_eq_ofSeq_iff.2 (hs.mono fun n hn => hn.2)

/-- **Exercise 12.2(6).** The sum of two internal hyperreal-valued functions is internal. -/
theorem IsInternalPFun.padd {f g : αS →. ℝ*} (hf : IsInternalPFun α ℝ f)
    (hg : IsInternalPFun α ℝ g) : IsInternalPFun α ℝ (padd f g) := by
  obtain ⟨F, rfl⟩ := hf
  obtain ⟨G, rfl⟩ := hg
  exact ⟨_, padd_internalPFun F G⟩

/-- **Exercise 12.2(6).** The product of two internal hyperreal-valued functions is
internal. -/
theorem IsInternalPFun.pmul {f g : αS →. ℝ*} (hf : IsInternalPFun α ℝ f)
    (hg : IsInternalPFun α ℝ g) : IsInternalPFun α ℝ (pmul f g) := by
  obtain ⟨F, rfl⟩ := hf
  obtain ⟨G, rfl⟩ := hg
  exact ⟨_, pmul_internalPFun F G⟩

/-- **Exercise 12.2(6).** A hyperreal multiple $`cf` of an internal hyperreal-valued function
is internal. -/
theorem IsInternalPFun.map_mul_left {f : αS →. ℝ*} (hf : IsInternalPFun α ℝ f) (c : ℝ*) :
    IsInternalPFun α ℝ (f.map fun y => c * y) := by
  obtain ⟨F, rfl⟩ := hf
  obtain ⟨c, rfl⟩ := hyperreal_exists_rep c
  exact ⟨_, map_mul_left_internalPFun c F⟩

/-- **Exercise 12.2(7).** An internal function that is defined somewhere and takes only
infinitesimal values has a range with an infinitesimal least upper bound. The range is a
nonempty internal set by Exercise 12.2(1), and it is bounded above by $`1`, so internal
order-completeness gives a least upper bound, which is infinitesimal because it lies between a
member of the range and every positive real. The hypothesis that the domain is nonempty is
implicit in the book: the empty set has no least upper bound in the hyperreals. -/
theorem IsInternalPFun.exists_isLUB_ran_infinitesimal {f : αS →. ℝ*}
    (hf : IsInternalPFun α ℝ f) (hne : f.Dom.Nonempty)
    (h : ∀ x y, y ∈ f x → Infinitesimal y) : ∃ b, IsLUB f.ran b ∧ Infinitesimal b := by
  have hran : ∀ y ∈ f.ran, Infinitesimal y := fun y ⟨x, hx⟩ => h x y hx
  have hne' : f.ran.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hy⟩ := (PFun.mem_dom _ _).1 hx
    exact ⟨y, x, hy⟩
  have hbdd : BddAbove f.ran := ⟨((1 : ℝ) : ℝ*), fun y hy =>
    (abs_lt.1 (infinitesimal_iff_abs_lt.1 (hran y hy) 1 one_pos)).2.le⟩
  obtain ⟨b, hb⟩ := IsInternal.exists_isLUB hf.isInternalSet_ran hne' hbdd
  exact ⟨b, hb, infinitesimal_of_isLUB hran hne' hb⟩

/-- **Exercise 12.2(8).** An infinite set of real numbers is external, proved from Exercise
12.2(1) in place of the internal set definition principle. An infinite set $`A` of reals can
be mapped onto the natural numbers by a real function $`g`. If $`A` were internal, its image
under $`{}^*g` would be internal; but that image is the set of standard natural numbers,
which is external. -/
theorem isExternal_image_coe_of_infinite_of_image {A : Set ℝ} (hA : A.Infinite) :
    IsExternal (((↑) : ℝ → ℝ*) '' A) := by
  classical
  intro hint
  have : Infinite A := infinite_coe_iff.2 hA
  let e := Infinite.natEmbedding A
  let g : ℝ → ℝ := fun x => if h : ∃ n, ((e n : A) : ℝ) = x then (h.choose : ℝ) else 0
  have hg : ∀ n, g (e n) = n := fun n => by
    have h : ∃ m, ((e m : A) : ℝ) = (e n : ℝ) := ⟨n, rfl⟩
    simp only [g, h, ↓reduceDIte]
    exact congrArg _ (e.injective (Subtype.ext h.choose_spec))
  have hgA : g '' A = range ((↑) : ℕ → ℝ) := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      by_cases h : ∃ n, ((e n : A) : ℝ) = x
      · exact ⟨h.choose, by simp only [g, h, ↓reduceDIte]⟩
      · exact ⟨0, by simp only [g, h, ↓reduceDIte, Nat.cast_zero]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨e n, (e n).2, hg n⟩
  have h1 : (⋆g : ℝ* → ℝ*) '' (((↑) : ℝ → ℝ*) '' A) = range ((↑) : ℕ → ℝ*) := by
    rw [image_image]
    have h2 : (fun x : ℝ => (⋆g : ℝ* → ℝ*) (x : ℝ*)) = fun x : ℝ => ((g x : ℝ) : ℝ*) :=
      funext fun x => starMap_coe g x
    rw [h2, ← image_image (fun y : ℝ => (y : ℝ*)) g, hgA, ← range_comp]
    rfl
  exact isExternal_range_natCast (h1 ▸ IsInternalSet.image_starMap hint g)

end Arithmetic

end Goldblatt
