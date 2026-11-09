import Mathlib

/-!
# 13 (part 1). Sets, Universes and Superstructures: Sections 13.1 to 13.6

This is the first of five parts of Chapter 13 (the overview and the design notes are on the
chapter page {lit}`Goldblatt.Ch13_Universes`). It sets up the set-theoretic world in which
Part IV of the book takes place: ordered pairs, tuples, relations and functions coded as sets,
transitive and strongly transitive sets, universes with all their closure properties, and the
superstructure over a set of individuals, which is the standard example of a universe.

Everything lives inside Mathlib's model {name}`ZFSet` of ZFC. That model has no atoms, so an
_individual_ is not an object without members but an object none of whose members is visible
in the universe at hand; this is exactly the condition the book writes down in Section 13.5,
and it is the device usually called a base set.
-/

noncomputable section

namespace Goldblatt

open ZFSet

universe u

variable {U X Y A B C D R S f g a b c d p : ZFSet.{u}}

/-!
## 13.1 What Do We Need in the Mathematical World?

The section is a wish list. A universe should contain a set of individuals, and with any two
of its sets all functions and relations between them, their unions, intersections,
differences and power sets, and it should be transitive, so that a bounded quantifier over a
member of the universe ranges over members of the universe. Two consequences are drawn at once:
transitivity and closure under power sets give closure under subsets, and closure under
Cartesian products then gives closure under relations. Both are proved below as
{lit}`IsUniverse.isSetOf_of_subset` and {lit}`IsUniverse.isSetOf_of_subset_prod`, once
universes have been defined.

## 13.2 Pairs Are Enough

Functions, tuples and relations can all be built from ordered pairs. A function from $`A` to
$`B` is a set of pairs that is single valued and has domain $`A`; an $`m`-tuple for $`m > 2`
is the function $`i \mapsto a_i` on $`\{1, \dots, m\}`; an $`m`-ary relation is a set of
$`m`-tuples. The definitions are given here in terms of Mathlib's {name}`ZFSet.pair`; the next
section recalls that this pair is itself a set.
-/

/-- **Section 13.2, binary relations.** A set is a binary relation when each of its members is
an ordered pair. -/
def IsRel (R : ZFSet.{u}) : Prop := ∀ p ∈ R, ∃ a b, p = pair a b

/-- **Section 13.5, domain.** The domain $`\operatorname{dom} R = \{a : \exists b\,
(a, b) \in R\}` of a set of pairs. It is cut out of the double union of $`R`, which contains
every component of every pair in $`R`. -/
def dom (R : ZFSet.{u}) : ZFSet.{u} := (⋃₀ (⋃₀ R)).sep fun a => ∃ b, pair a b ∈ R

/-- **Section 13.5, range.** The range $`\operatorname{ran} R = \{b : \exists a\,
(a, b) \in R\}` of a set of pairs. -/
def ran (R : ZFSet.{u}) : ZFSet.{u} := (⋃₀ (⋃₀ R)).sep fun b => ∃ a, pair a b ∈ R

theorem singleton_mem_pair : ({a} : ZFSet) ∈ pair a b := by simp [pair]

theorem pair_mem_pair : ({a, b} : ZFSet) ∈ pair a b := by simp [pair]

theorem fst_mem_sUnion_sUnion (h : pair a b ∈ R) : a ∈ ⋃₀ (⋃₀ R) :=
  mem_sUnion.2 ⟨{a}, mem_sUnion.2 ⟨_, h, singleton_mem_pair⟩, mem_singleton.2 rfl⟩

theorem snd_mem_sUnion_sUnion (h : pair a b ∈ R) : b ∈ ⋃₀ (⋃₀ R) :=
  mem_sUnion.2 ⟨{a, b}, mem_sUnion.2 ⟨_, h, pair_mem_pair⟩, by simp⟩

/-- Membership in the domain of a relation. -/
@[simp]
theorem mem_dom : a ∈ dom R ↔ ∃ b, pair a b ∈ R :=
  ⟨fun h => (mem_sep.1 h).2, fun ⟨b, h⟩ => mem_sep.2 ⟨fst_mem_sUnion_sUnion h, b, h⟩⟩

/-- Membership in the range of a relation. -/
@[simp]
theorem mem_ran : b ∈ ran R ↔ ∃ a, pair a b ∈ R :=
  ⟨fun h => (mem_sep.1 h).2, fun ⟨a, h⟩ => mem_sep.2 ⟨snd_mem_sUnion_sUnion h, a, h⟩⟩

/-- **Section 13.5, image under a relation.** The image
$`R'(C) = \{b : \exists a \in C\, (a, b) \in R\}`. -/
def relImage (R C : ZFSet.{u}) : ZFSet.{u} := (ran R).sep fun b => ∃ a ∈ C, pair a b ∈ R

/-- Membership in the image of a set under a relation. -/
@[simp]
theorem mem_relImage : b ∈ relImage R C ↔ ∃ a ∈ C, pair a b ∈ R :=
  ⟨fun h => (mem_sep.1 h).2, fun ⟨a, ha, h⟩ => mem_sep.2 ⟨mem_ran.2 ⟨a, h⟩, a, ha, h⟩⟩

/-- **Section 13.5, inverse image.** The inverse image
$`R^{-1}(D) = \{a : \exists b \in D\, (a, b) \in R\}`; for a function $`f` this is
$`f^{-1}(D) = \{a : f(a) \in D\}`. -/
def relPreimage (R D : ZFSet.{u}) : ZFSet.{u} := (dom R).sep fun a => ∃ b ∈ D, pair a b ∈ R

/-- Membership in the inverse image of a set under a relation. -/
@[simp]
theorem mem_relPreimage : a ∈ relPreimage R D ↔ ∃ b ∈ D, pair a b ∈ R :=
  ⟨fun h => (mem_sep.1 h).2, fun ⟨b, hb, h⟩ => mem_sep.2 ⟨mem_dom.2 ⟨b, h⟩, b, hb, h⟩⟩

/-- **Section 13.5, inverse relation.** $`R^{-1} = \{(b, a) : (a, b) \in R\}`. -/
def relInv (R : ZFSet.{u}) : ZFSet.{u} :=
  (prod (ran R) (dom R)).sep fun p => ∃ a b, p = pair b a ∧ pair a b ∈ R

/-- Membership in the inverse relation. -/
theorem mem_relInv : p ∈ relInv R ↔ ∃ a b, p = pair b a ∧ pair a b ∈ R := by
  refine ⟨fun h => (mem_sep.1 h).2, fun ⟨a, b, hp, h⟩ => mem_sep.2 ⟨?_, a, b, hp, h⟩⟩
  rw [hp, pair_mem_prod]
  exact ⟨mem_ran.2 ⟨a, h⟩, mem_dom.2 ⟨b, h⟩⟩

/-- A pair lies in the inverse relation exactly when the swapped pair lies in the relation. -/
@[simp]
theorem pair_mem_relInv : pair b a ∈ relInv R ↔ pair a b ∈ R := by
  rw [mem_relInv]
  constructor
  · rintro ⟨a', b', h, h'⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.1 h
    exact h'
  · exact fun h => ⟨a, b, rfl, h⟩

/-- **Section 13.5, composition.** The composite of two relations,
$`\{(a, c) : \exists b\, ((a, b) \in R \text{ and } (b, c) \in S)\}`: first $`R`, then $`S`. -/
def relComp (R S : ZFSet.{u}) : ZFSet.{u} :=
  (prod (dom R) (ran S)).sep fun p => ∃ a b c, p = pair a c ∧ pair a b ∈ R ∧ pair b c ∈ S

/-- Membership in a composite relation. -/
theorem mem_relComp :
    p ∈ relComp R S ↔ ∃ a b c, p = pair a c ∧ pair a b ∈ R ∧ pair b c ∈ S := by
  refine ⟨fun h => (mem_sep.1 h).2, fun ⟨a, b, c, hp, h, h'⟩ => mem_sep.2 ⟨?_, a, b, c, hp, h, h'⟩⟩
  rw [hp, pair_mem_prod]
  exact ⟨mem_dom.2 ⟨b, h⟩, mem_ran.2 ⟨b, h'⟩⟩

/-- A pair lies in a composite exactly when there is an intermediate point. -/
@[simp]
theorem pair_mem_relComp : pair a c ∈ relComp R S ↔ ∃ b, pair a b ∈ R ∧ pair b c ∈ S := by
  rw [mem_relComp]
  constructor
  · rintro ⟨a', b', c', h, h1, h2⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.1 h
    exact ⟨b', h1, h2⟩
  · exact fun ⟨b, h1, h2⟩ => ⟨a, b, c, rfl, h1, h2⟩

/-- **Section 13.2, functions.** A set is a function when it is a set of ordered pairs in
which the second component is determined by the first (clause (ii) of the book's definition).
No domain or codomain is mentioned; the domain is {lit}`dom f`. -/
def IsFunction (f : ZFSet.{u}) : Prop :=
  IsRel f ∧ ∀ a b c, pair a b ∈ f → pair a c ∈ f → b = c

/-- **Section 13.2, functions from one set to another.** The book's definition of a function
from $`A` to $`B` (a set of pairs with (i) components in $`A` and $`B`, (ii) functionality,
(iii) domain all of $`A`) is equivalent to Mathlib's {name}`ZFSet.IsFunc`, which is the
predicate used from here on. -/
theorem isFunc_iff :
    IsFunc A B f ↔ IsRel f ∧ (∀ a b, pair a b ∈ f → a ∈ A ∧ b ∈ B) ∧
      (∀ a b c, pair a b ∈ f → pair a c ∈ f → b = c) ∧ ∀ a ∈ A, ∃ b ∈ B, pair a b ∈ f := by
  constructor
  · rintro ⟨hsub, huniq⟩
    have h1 : ∀ a b, pair a b ∈ f → a ∈ A ∧ b ∈ B := fun a b h => pair_mem_prod.1 (hsub h)
    refine ⟨fun p hp => ?_, h1, fun a b c hb hc => ?_, fun a ha => ?_⟩
    · obtain ⟨a, -, b, -, rfl⟩ := mem_prod.1 (hsub hp)
      exact ⟨a, b, rfl⟩
    · exact (huniq a (h1 a b hb).1).unique hb hc
    · obtain ⟨b, hb, -⟩ := huniq a ha
      exact ⟨b, (h1 a b hb).2, hb⟩
  · rintro ⟨hrel, h1, h2, h3⟩
    refine ⟨fun p hp => ?_, fun a ha => ?_⟩
    · obtain ⟨a, b, rfl⟩ := hrel p hp
      exact pair_mem_prod.2 (h1 a b hp)
    · obtain ⟨b, -, hb⟩ := h3 a ha
      exact ⟨b, hb, fun c hc => h2 a c b hc hb⟩

theorem _root_.ZFSet.IsFunc.isFunction (h : IsFunc A B f) : IsFunction f :=
  let h' := isFunc_iff.1 h
  ⟨h'.1, h'.2.2.1⟩

theorem _root_.ZFSet.IsFunc.dom_eq (h : IsFunc A B f) : dom f = A := by
  obtain ⟨-, h1, -, h3⟩ := isFunc_iff.1 h
  ext a
  rw [mem_dom]
  exact ⟨fun ⟨b, hb⟩ => (h1 a b hb).1, fun ha => let ⟨b, _, hb⟩ := h3 a ha; ⟨b, hb⟩⟩

theorem _root_.ZFSet.IsFunc.ran_subset (h : IsFunc A B f) : ran f ⊆ B := by
  intro b hb
  obtain ⟨a, ha⟩ := mem_ran.1 hb
  exact (pair_mem_prod.1 (h.1 ha)).2

/-- A function in the sense of {lit}`IsFunction` is a function from its domain to its
range. -/
theorem IsFunction.isFunc (h : IsFunction f) : IsFunc (dom f) (ran f) f := by
  refine isFunc_iff.2 ⟨h.1, fun a b hab => ⟨mem_dom.2 ⟨b, hab⟩, mem_ran.2 ⟨a, hab⟩⟩, h.2,
    fun a ha => ?_⟩
  obtain ⟨b, hb⟩ := mem_dom.1 ha
  exact ⟨b, mem_ran.2 ⟨a, hb⟩, hb⟩

/-- **Section 13.2, function values.** The value $`f(a)` of a function $`f` at a point of its
domain. It is defined for every pair of sets as the union of all $`b` with $`(a, b) \in f`,
which is the unique such $`b` when $`f` is a function and $`a` is in its domain. -/
def app (f a : ZFSet.{u}) : ZFSet.{u} := ⋃₀ ((ran f).sep fun b => pair a b ∈ f)

/-- The value of a function at $`a` is the second component of the pair with first
component $`a`. -/
theorem IsFunction.app_eq (hf : IsFunction f) (h : pair a b ∈ f) : app f a = b := by
  have : ((ran f).sep fun b => pair a b ∈ f) = {b} := by
    ext c
    rw [mem_sep, mem_singleton]
    exact ⟨fun hc => hf.2 a c b hc.2 h, fun hc => hc ▸ ⟨mem_ran.2 ⟨a, h⟩, h⟩⟩
  rw [app, this, sUnion_singleton]

/-- The pair $`(a, f(a))` belongs to $`f` when $`a` is in the domain. -/
theorem IsFunction.pair_app_mem (hf : IsFunction f) (ha : a ∈ dom f) : pair a (app f a) ∈ f := by
  obtain ⟨b, hb⟩ := mem_dom.1 ha
  rwa [hf.app_eq hb]

theorem IsFunction.pair_mem_iff (hf : IsFunction f) :
    pair a b ∈ f ↔ a ∈ dom f ∧ app f a = b :=
  ⟨fun h => ⟨mem_dom.2 ⟨b, h⟩, hf.app_eq h⟩, fun ⟨ha, hb⟩ => hb ▸ hf.pair_app_mem ha⟩

/-- A function is injective when no two pairs share their second component. -/
def IsInjective (f : ZFSet.{u}) : Prop := ∀ a a' b, pair a b ∈ f → pair a' b ∈ f → a = a'

/-- **Section 13.5, numerals.** The von Neumann numeral $`n = \{0, 1, \dots, n - 1\}`. The
book asks a universe to contain the positive integers so that tuples can be indexed; with this
choice of the integers every universe contains them ({lit}`IsUniverse.isSetOf_num`), and the
assumption can be dropped. -/
def num : ℕ → ZFSet.{u}
  | 0 => ∅
  | n + 1 => insert (num n) (num n)

theorem num_mem_num_of_lt {m n : ℕ} (h : m < n) : (num m : ZFSet.{u}) ∈ num n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [num, mem_insert_iff]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact Or.inr (ih h)
    · exact Or.inl rfl

/-- Distinct natural numbers have distinct numerals. -/
theorem num_injective : Function.Injective (num : ℕ → ZFSet.{u}) := by
  intro m n h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · have := num_mem_num_of_lt (m := m) (n := n) h'
    rw [h] at this
    exact mem_irrefl _ this
  · have := num_mem_num_of_lt (m := n) (n := m) h'
    rw [h] at this
    exact mem_irrefl _ this

/-- **Section 13.2, tuples.** The $`m`-tuple $`(a_1, \dots, a_m)`. For $`m = 2` it is the
ordered pair; for every other $`m` it is the set of pairs
$`\{(1, a_1), \dots, (m, a_m)\}`, a function on $`\{1, \dots, m\}`, where the indices are the
numerals {lit}`num`. The book forms tuples only for $`m \ge 2`. -/
def tuple (m : ℕ) (a : Fin m → ZFSet.{u}) : ZFSet.{u} :=
  if h : m = 2 then pair (a ⟨0, by omega⟩) (a ⟨1, by omega⟩)
  else ZFSet.range fun i : Fin m => pair (num (i + 1)) (a i)

/-- A 2-tuple is an ordered pair. -/
@[simp]
theorem tuple_two (a : Fin 2 → ZFSet.{u}) : tuple 2 a = pair (a 0) (a 1) := by
  simp [tuple]

theorem mem_tuple {m : ℕ} (hm : m ≠ 2) {a : Fin m → ZFSet.{u}} :
    p ∈ tuple m a ↔ ∃ i : Fin m, p = pair (num (i + 1)) (a i) := by
  simp [tuple, hm, eq_comm]

/-!
## 13.3 Actually, Sets Are Enough

An ordered pair needs only one property, that it determines its two components in order, and
Kuratowski's set $`\{\{a\}, \{a, b\}\}` has it. So pairs, and with them tuples, relations and
functions, are sets, and everything needed to study a structure on a set of individuals is
obtained by applying set theory to that set. The section then derives closure of a universe
under Cartesian products from transitivity, unions and power sets; that derivation is
{lit}`IsUniverse.isSetOf_prod` below.
-/

/-- **Exercise 13.3.1 (i).** $`\{\{a\}, \{a, b\}\} = \{\{c\}, \{c, d\}\}` if and only if
$`a = c` and $`b = d`. This is Mathlib's {name}`ZFSet.pair_inj`, since {name}`ZFSet.pair` is
by definition the Kuratowski pair. -/
theorem kuratowski_pair_eq_iff :
    ({{a}, {a, b}} : ZFSet.{u}) = {{c}, {c, d}} ↔ a = c ∧ b = d :=
  pair_inj (x := a) (y := b) (x' := c) (y' := d)

/-- **Exercise 13.3.1 (ii).** Two $`m`-tuples are equal if and only if they agree in every
component. The book states this for $`m \ge 2`; it holds for every $`m`. -/
theorem tuple_eq_iff {m : ℕ} {a b : Fin m → ZFSet.{u}} :
    tuple m a = tuple m b ↔ ∀ i, a i = b i := by
  refine ⟨fun h i => ?_, fun h => by rw [funext h]⟩
  by_cases hm : m = 2
  · subst hm
    rw [tuple_two, tuple_two, pair_inj] at h
    fin_cases i
    · exact h.1
    · exact h.2
  · have : pair (num ((i : ℕ) + 1)) (a i) ∈ tuple m b := h ▸ (mem_tuple hm).2 ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := (mem_tuple hm).1 this
    obtain ⟨h1, h2⟩ := pair_inj.1 hj
    have hij : i = j := Fin.ext (by simpa using num_injective h1)
    rw [h2, hij]

theorem tuple_injective (m : ℕ) : Function.Injective (tuple m : (Fin m → ZFSet.{u}) → ZFSet.{u}) :=
  fun _ _ h => funext (tuple_eq_iff.1 h)

/-- **Section 13.2, Cartesian products.** The product $`A_1 \times \dots \times A_m`, the set
of all $`m`-tuples $`(a_1, \dots, a_m)` with $`a_i \in A_i`. -/
def tupleProd (m : ℕ) (A : Fin m → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun a : (i : Fin m) → A i => tuple m fun i => (a i : ZFSet.{u})

/-- Membership in a product of $`m` sets. -/
theorem mem_tupleProd {m : ℕ} {A : Fin m → ZFSet.{u}} {t : ZFSet.{u}} :
    t ∈ tupleProd m A ↔ ∃ a : Fin m → ZFSet.{u}, (∀ i, a i ∈ A i) ∧ t = tuple m a := by
  rw [tupleProd, mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨fun i => a i, fun i => (a i).2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fun i => ⟨a i, ha i⟩, rfl⟩

/-- The product of two sets in the sense of tuples is Mathlib's {name}`ZFSet.prod`. -/
theorem tupleProd_two (A : Fin 2 → ZFSet.{u}) : tupleProd 2 A = prod (A 0) (A 1) := by
  ext t
  rw [mem_tupleProd, mem_prod]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a 0, ha 0, a 1, ha 1, tuple_two a⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    refine ⟨![x, y], fun i => ?_, by simp⟩
    fin_cases i
    · exact hx
    · exact hy

/-- **Section 13.2, relations of higher arity.** An $`m`-ary relation is a set of
$`m`-tuples. -/
def IsRelN (m : ℕ) (R : ZFSet.{u}) : Prop := ∀ t ∈ R, ∃ a : Fin m → ZFSet.{u}, t = tuple m a

/-!
## 13.4 Strong Transitivity

Transitivity of a universe puts the components of the pairs of a relation into the universe,
but that only makes the domain of the relation a subset of the universe, not a member. What
is needed is a transitive _member_ of the universe that includes the relation: the domain is
a subset of it, and subsets of members are members. Requiring every set of the universe to be
included in a transitive set of the universe is strong transitivity. It implies ordinary
transitivity.

In {name}`ZFSet` these notions have to be read relative to the universe, because an individual
is a set whose members lie outside the universe. So "a set" means a member of the universe
that is not an individual ({lit}`IsSetOf`), and a transitive set is one that contains the
members, visible in the universe, of its members ({lit}`TransitiveIn`).
-/

/-- **Section 13.5, individuals.** The condition the book imposes on an individual of a
universe $`\mathbb U`: it is not the empty set and no member of $`\mathbb U` is a member of
it. -/
def IsIndividual (U a : ZFSet.{u}) : Prop := a ≠ ∅ ∧ ∀ y ∈ U, y ∉ a

/-- **Section 13.5, sets of a universe.** A member of $`\mathbb U` that is not an individual.
The book's uppercase letters range over such entities. -/
structure IsSetOf (U A : ZFSet.{u}) : Prop where
  /-- The entity belongs to the universe. -/
  mem : A ∈ U
  /-- The entity is the empty set or has a member in the universe. -/
  not_individual : ¬ IsIndividual U A

/-- A member of $`\mathbb U` all of whose members are in $`\mathbb U` is a set of
$`\mathbb U`. -/
theorem isSetOf_of_subset (hA : A ∈ U) (hAU : A ⊆ U) : IsSetOf U A := by
  refine ⟨hA, fun ⟨hne, hall⟩ => hne ?_⟩
  rw [eq_empty]
  exact fun y hy => hall y (hAU hy) hy

/-- A set of $`\mathbb U` is empty or has a member that belongs to $`\mathbb U`. -/
theorem IsSetOf.eq_empty_or (h : IsSetOf U A) : A = ∅ ∨ ∃ y ∈ U, y ∈ A := by
  by_contra hc
  push Not at hc
  exact h.2 ⟨hc.1, hc.2⟩

/-- **Section 13.4, transitive sets.** $`B` is transitive, as seen from $`\mathbb U`: every
member, belonging to $`\mathbb U`, of a member of $`B` is a member of $`B`. For a subset of a
universe this says that every set in $`B` is a subset of $`B`. -/
def TransitiveIn (U B : ZFSet.{u}) : Prop := ∀ y ∈ B, ∀ z ∈ y, z ∈ U → z ∈ B

/-- **Section 13.4, strong transitivity.** Every set $`A` in $`\mathbb U` is included in a
transitive set $`B \in \mathbb U` with $`A \subseteq B \subseteq \mathbb U`. -/
def StronglyTransitive (U : ZFSet.{u}) : Prop :=
  ∀ A, IsSetOf U A → ∃ B, B ∈ U ∧ TransitiveIn U B ∧ A ⊆ B ∧ B ⊆ U

/-- **Section 13.4.** A strongly transitive $`\mathbb U` is transitive: every set in
$`\mathbb U` is a subset of $`\mathbb U`. -/
theorem StronglyTransitive.subset (hU : StronglyTransitive U) (hA : IsSetOf U A) : A ⊆ U := by
  obtain ⟨B, -, -, hAB, hBU⟩ := hU A hA
  exact fun x hx => hBU (hAB hx)

/-!
## 13.5 Universes

A universe is a strongly transitive set closed under unordered pairs, binary unions of sets
and power sets of sets, and containing at least one set. It is a universe over $`X` when $`X`
is one of its sets and the members of $`X` are individuals. The section lists the closure
properties that follow; each item of the list is a theorem below, in the order of the book.

Three points where the formalization has to be explicit about something the book leaves to
the reader's picture of individuals as memberless objects:

* the closure axioms for unions and power sets are stated, as in the book, for sets only, and
  "set" is {lit}`IsSetOf`;
* a binary relation in the universe is a set of the universe whose members are pairs of
  members of the universe ({lit}`RelIn`); this excludes an individual that happens to be a
  pair of foreign objects, which cannot occur in the book;
* the positive integers used to index tuples are the numerals {lit}`num`, which belong to
  every universe, so the book's standing assumption that a universe contains them is a
  theorem here.
-/

/-- **Section 13.5, universes.** A universe is a strongly transitive set, closed under
unordered pairs, under unions of two of its sets and under power sets of its sets, that
contains at least one set. -/
structure IsUniverse (U : ZFSet.{u}) : Prop where
  /-- Every set of the universe is included in a transitive set of the universe. -/
  stronglyTransitive : StronglyTransitive U
  /-- If $`a, b \in \mathbb U` then $`\{a, b\} \in \mathbb U`. -/
  pair_mem : ∀ a ∈ U, ∀ b ∈ U, ({a, b} : ZFSet.{u}) ∈ U
  /-- If $`A` and $`B` are sets in $`\mathbb U` then $`A \cup B \in \mathbb U`. -/
  union_mem : ∀ A B, IsSetOf U A → IsSetOf U B → A ∪ B ∈ U
  /-- If $`A` is a set in $`\mathbb U` then $`\mathcal P(A) \in \mathbb U`. -/
  powerset_mem : ∀ A, IsSetOf U A → powerset A ∈ U
  /-- The universe contains at least one set. -/
  exists_set : ∃ A, IsSetOf U A

/-- **Section 13.5, universes over a set.** $`\mathbb U` is a universe over $`X` when $`X` is
a set belonging to $`\mathbb U` and every member of $`X` is an individual: it is not empty
and has no member in $`\mathbb U`. -/
structure IsUniverseOver (U X : ZFSet.{u}) : Prop extends IsUniverse U where
  /-- $`X` is a set that belongs to the universe. -/
  base_isSetOf : IsSetOf U X
  /-- The members of $`X` are individuals. -/
  individual : ∀ x ∈ X, IsIndividual U x

/-- **Section 13.5, relations in a universe.** A set of pairs of members of
$`\mathbb U`. -/
def RelIn (U R : ZFSet.{u}) : Prop := ∀ p ∈ R, ∃ a ∈ U, ∃ b ∈ U, p = pair a b

theorem RelIn.isRel (h : RelIn U R) : IsRel R := fun p hp =>
  let ⟨a, _, b, _, h⟩ := h p hp; ⟨a, b, h⟩

namespace IsUniverse

variable (hU : IsUniverse U)
include hU

/-- **Section 13.4/13.5, transitivity.** Every set of a universe is a subset of the
universe. -/
theorem subset (hA : IsSetOf U A) : A ⊆ U := hU.stronglyTransitive.subset hA

/-- The sets of a universe are its members that are also subsets of it. -/
theorem isSetOf_iff : IsSetOf U A ↔ A ∈ U ∧ A ⊆ U :=
  ⟨fun h => ⟨h.1, hU.subset h⟩, fun h => isSetOf_of_subset h.1 h.2⟩

theorem mem_of_mem (hA : IsSetOf U A) (ha : a ∈ A) : a ∈ U := hU.subset hA ha

/-- A pair set $`\{a, b\}` of members of the universe is a set of the universe. -/
theorem isSetOf_pair (ha : a ∈ U) (hb : b ∈ U) : IsSetOf U ({a, b} : ZFSet.{u}) :=
  isSetOf_of_subset (hU.pair_mem a ha b hb) fun x hx => by
    rcases mem_pair.1 hx with rfl | rfl <;> assumption

/-- **Section 13.5, set theory (1).** If $`a \in \mathbb U` then $`\{a\} \in \mathbb U`. -/
theorem isSetOf_singleton (ha : a ∈ U) : IsSetOf U ({a} : ZFSet.{u}) := by
  have := hU.isSetOf_pair ha ha
  rwa [show ({a, a} : ZFSet.{u}) = {a} by ext; simp] at this

/-- The union of two sets of the universe is a set of the universe. -/
theorem isSetOf_union (hA : IsSetOf U A) (hB : IsSetOf U B) : IsSetOf U (A ∪ B) :=
  isSetOf_of_subset (hU.union_mem A B hA hB) fun x hx => by
    rcases mem_union.1 hx with h | h
    · exact hU.subset hA h
    · exact hU.subset hB h

/-- The power set of a set of the universe is a set of the universe. -/
theorem isSetOf_powerset (hA : IsSetOf U A) : IsSetOf U (powerset A) :=
  ⟨hU.powerset_mem A hA, fun h => h.2 A hA.1 (mem_powerset.2 fun _ h => h)⟩

/-- **Section 13.1/13.5, set theory (4), subset closure.** If $`A \subseteq B \in \mathbb U`
then $`A \in \mathbb U`. -/
theorem isSetOf_of_subset (hB : IsSetOf U B) (hAB : A ⊆ B) : IsSetOf U A :=
  Goldblatt.isSetOf_of_subset (hU.subset (hU.isSetOf_powerset hB) (mem_powerset.2 hAB))
    fun _ hx => hU.subset hB (hAB hx)

/-- **Section 13.5, set theory (5).** $`\emptyset \in \mathbb U`. -/
theorem isSetOf_empty : IsSetOf U (∅ : ZFSet.{u}) :=
  let ⟨_, hA⟩ := hU.exists_set
  hU.isSetOf_of_subset hA (empty_subset _)

theorem empty_mem : (∅ : ZFSet.{u}) ∈ U := hU.isSetOf_empty.1

/-- Inserting a member of the universe into a set of the universe gives a set of the
universe. -/
theorem isSetOf_insert (ha : a ∈ U) (hA : IsSetOf U A) : IsSetOf U (insert a A) := by
  rw [insert_eq]
  exact hU.isSetOf_union (hU.isSetOf_singleton ha) hA

/-- **Section 13.5, set theory (3).** A universe contains all its finite subsets. -/
theorem isSetOf_of_finite (hAU : A ⊆ U) (hfin : (A : Set ZFSet.{u}).Finite) : IsSetOf U A := by
  generalize hs : (A : Set ZFSet.{u}) = s at hfin
  induction s, hfin using Set.Finite.induction_on generalizing A with
  | empty =>
    have : A = ∅ := by
      rw [eq_empty]
      intro y hy
      have : y ∈ (A : Set ZFSet.{u}) := hy
      rw [hs] at this
      exact this
    exact this ▸ hU.isSetOf_empty
  | @insert a s _ _ ih =>
    have hmem : ∀ x, x ∈ A ↔ x = a ∨ x ∈ s := fun x => by
      rw [← SetLike.mem_coe, hs, Set.mem_insert_iff]
    have hA' : IsSetOf U (A.sep fun x => x ∈ s) :=
      ih (fun x hx => hAU (mem_sep.1 hx).1) (by
        ext x
        simp only [SetLike.mem_coe, mem_sep, hmem]
        tauto)
    have : A = insert a (A.sep fun x => x ∈ s) := by
      ext x
      simp only [mem_insert_iff, mem_sep, hmem]
      tauto
    rw [this]
    exact hU.isSetOf_insert (hAU ((hmem a).2 (Or.inl rfl))) hA'

/-- **Section 13.5, set theory (6).** If $`\{A_i : i \in I\} \subseteq A \in \mathbb U` and
each $`A_i` is a set, then $`\bigcup_{i \in I} A_i \in \mathbb U`. This is where strong
transitivity is used. -/
theorem isSetOf_sUnion_of_subset (hA : IsSetOf U A) (hSA : S ⊆ A)
    (hS : ∀ s ∈ S, IsSetOf U s) : IsSetOf U (⋃₀ S) := by
  obtain ⟨B, hB, hBt, hAB, hBU⟩ := hU.stronglyTransitive A hA
  refine hU.isSetOf_of_subset (Goldblatt.isSetOf_of_subset hB hBU) fun y hy => ?_
  obtain ⟨s, hs, hys⟩ := mem_sUnion.1 hy
  exact hBt s (hAB (hSA hs)) y hys (hU.subset (hS s hs) hys)

/-- **Section 13.5, set theory (7).** A universe is closed under unions of sets of sets: if
$`B \in \mathbb U` is a set all of whose members are sets, then
$`\bigcup B \in \mathbb U`. -/
theorem isSetOf_sUnion (hB : IsSetOf U B) (hS : ∀ s ∈ B, IsSetOf U s) : IsSetOf U (⋃₀ B) :=
  hU.isSetOf_sUnion_of_subset hB (fun _ h => h) hS

/-- **Section 13.5, set theory (2).** A union $`A_1 \cup \dots \cup A_m` of finitely many sets
of the universe is in the universe. -/
theorem isSetOf_iUnion_fin (m : ℕ) (A : Fin m → ZFSet.{u}) (hA : ∀ i, IsSetOf U (A i)) :
    IsSetOf U (⋃₀ (ZFSet.range A)) := by
  refine hU.isSetOf_sUnion (hU.isSetOf_of_finite ?_ ?_) ?_
  · intro x hx
    obtain ⟨i, rfl⟩ := mem_range.1 hx
    exact (hA i).1
  · rw [coe_range]
    exact Set.finite_range A
  · intro s hs
    obtain ⟨i, rfl⟩ := mem_range.1 hs
    exact hA i

/-- **Section 13.5, set theory (8).** A universe is closed under arbitrary intersections of
its sets: for any nonempty family $`\mathcal S` of sets of $`\mathbb U`, whether or not the
family is itself a member of $`\mathbb U`, the intersection is in $`\mathbb U`. The family is
a Lean set of sets and the intersection is cut out of one of its members $`A_0`. -/
theorem isSetOf_sInter (𝒮 : Set ZFSet.{u}) (h𝒮 : ∀ s ∈ 𝒮, IsSetOf U s) {A₀ : ZFSet.{u}}
    (hA₀ : A₀ ∈ 𝒮) : IsSetOf U (A₀.sep fun x => ∀ s ∈ 𝒮, x ∈ s) :=
  hU.isSetOf_of_subset (h𝒮 A₀ hA₀) sep_subset

/-- The intersection of two sets of the universe is a set of the universe. -/
theorem isSetOf_inter (hA : IsSetOf U A) : IsSetOf U (A ∩ B) :=
  hU.isSetOf_of_subset hA fun _ hx => (mem_inter.1 hx).1

/-- The difference of a set of the universe and any set is a set of the universe. -/
theorem isSetOf_sdiff (hA : IsSetOf U A) : IsSetOf U (A \ B) :=
  hU.isSetOf_of_subset hA fun _ hx => (mem_sdiff.1 hx).1

/-- A subset cut out of a set of the universe by any property is a set of the universe. -/
theorem isSetOf_sep (hA : IsSetOf U A) (P : ZFSet.{u} → Prop) : IsSetOf U (A.sep P) :=
  hU.isSetOf_of_subset hA sep_subset

/-- **Section 13.5, relations and functions (1).** If $`a, b \in \mathbb U` then the ordered
pair $`(a, b)` is in $`\mathbb U`. -/
theorem isSetOf_opair (ha : a ∈ U) (hb : b ∈ U) : IsSetOf U (pair a b) :=
  hU.isSetOf_pair (hU.isSetOf_singleton ha).1 (hU.isSetOf_pair ha hb).1

/-- **Section 13.3, product closure.** If $`A` and $`B` are sets in $`\mathbb U` then
$`A \times B \in \mathbb U`, because $`A \times B \subseteq
\mathcal P(\mathcal P(A \cup B))`. -/
theorem isSetOf_prod (hA : IsSetOf U A) (hB : IsSetOf U B) : IsSetOf U (prod A B) := by
  refine hU.isSetOf_of_subset
    (hU.isSetOf_powerset (hU.isSetOf_powerset (hU.isSetOf_union hA hB))) fun p hp => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 hp
  rw [mem_powerset]
  intro q hq
  rw [mem_powerset]
  intro x hx
  rw [mem_union]
  rcases mem_pair.1 hq with rfl | rfl
  · rw [mem_singleton.1 hx]
    exact Or.inl ha
  · rcases mem_pair.1 hx with rfl | rfl
    · exact Or.inl ha
    · exact Or.inr hb

/-- **Section 13.1/13.5, relations and functions (2), relation closure.** If $`A` and $`B`
are sets in $`\mathbb U` and $`R \subseteq A \times B`, then $`R \in \mathbb U`. -/
theorem isSetOf_of_subset_prod (hA : IsSetOf U A) (hB : IsSetOf U B) (hR : R ⊆ prod A B) :
    IsSetOf U R :=
  hU.isSetOf_of_subset (hU.isSetOf_prod hA hB) hR

/-- A subset of a product of two sets of the universe is a relation in the universe. -/
theorem relIn_of_subset_prod (hA : IsSetOf U A) (hB : IsSetOf U B) (hR : R ⊆ prod A B) :
    RelIn U R := fun _ hp =>
  let ⟨a, ha, b, hb, h⟩ := mem_prod.1 (hR hp)
  ⟨a, hU.subset hA ha, b, hU.subset hB hb, h⟩

/-- **Section 13.5, the positive integers.** Every numeral belongs to every universe. -/
theorem isSetOf_num (n : ℕ) : IsSetOf U (num n) := by
  induction n with
  | zero => exact hU.isSetOf_empty
  | succ n ih => exact hU.isSetOf_insert ih.1 ih

/-- **Section 13.5, relations and functions (3).** If $`a_1, \dots, a_m \in \mathbb U` then
the tuple $`(a_1, \dots, a_m)` is in $`\mathbb U`. -/
theorem isSetOf_tuple (m : ℕ) (a : Fin m → ZFSet.{u}) (ha : ∀ i, a i ∈ U) :
    IsSetOf U (tuple m a) := by
  by_cases hm : m = 2
  · subst hm
    rw [tuple_two]
    exact hU.isSetOf_opair (ha 0) (ha 1)
  · refine hU.isSetOf_of_finite (fun p hp => ?_) ?_
    · obtain ⟨i, rfl⟩ := (mem_tuple hm).1 hp
      exact (hU.isSetOf_opair (hU.isSetOf_num _).1 (ha i)).1
    · simp only [tuple, hm, ↓reduceDIte, coe_range]
      exact Set.finite_range _

/-- **Section 13.5.** The product $`A_1 \times \dots \times A_m` of sets of the universe is
a set of the universe. -/
theorem isSetOf_tupleProd (m : ℕ) (A : Fin m → ZFSet.{u}) (hA : ∀ i, IsSetOf U (A i)) :
    IsSetOf U (tupleProd m A) := by
  by_cases hm : m = 2
  · subst hm
    rw [tupleProd_two]
    exact hU.isSetOf_prod (hA 0) (hA 1)
  · have hN : IsSetOf U (ZFSet.range fun i : Fin m => (num ((i : ℕ) + 1) : ZFSet.{u})) := by
      refine hU.isSetOf_of_finite (fun x hx => ?_) (by rw [coe_range]; exact Set.finite_range _)
      obtain ⟨i, rfl⟩ := mem_range.1 hx
      exact (hU.isSetOf_num _).1
    have hW := hU.isSetOf_iUnion_fin m A hA
    refine hU.isSetOf_of_subset (hU.isSetOf_powerset (hU.isSetOf_prod hN hW)) fun t ht => ?_
    obtain ⟨a, ha, rfl⟩ := mem_tupleProd.1 ht
    rw [mem_powerset]
    intro p hp
    obtain ⟨i, rfl⟩ := (mem_tuple hm).1 hp
    rw [pair_mem_prod]
    exact ⟨mem_range.2 ⟨i, rfl⟩, mem_sUnion.2 ⟨A i, mem_range.2 ⟨i, rfl⟩, ha i⟩⟩

/-- **Section 13.5, relations and functions (4).** A universe is closed under finitary
relations: if $`A_1, \dots, A_m` are sets in $`\mathbb U` and
$`R \subseteq A_1 \times \dots \times A_m`, then $`R \in \mathbb U`. -/
theorem isSetOf_of_subset_tupleProd (m : ℕ) (A : Fin m → ZFSet.{u}) (hA : ∀ i, IsSetOf U (A i))
    (hR : R ⊆ tupleProd m A) : IsSetOf U R :=
  hU.isSetOf_of_subset (hU.isSetOf_tupleProd m A hA) hR

/-- The components of the pairs of a relation in the universe all lie in one transitive set
of the universe. -/
theorem exists_transitive_of_relIn (hR : IsSetOf U R) (hrel : RelIn U R) :
    ∃ B, IsSetOf U B ∧ ∀ a b, pair a b ∈ R → a ∈ B ∧ b ∈ B := by
  obtain ⟨B, hB, hBt, hRB, hBU⟩ := hU.stronglyTransitive R hR
  refine ⟨B, Goldblatt.isSetOf_of_subset hB hBU, fun a b hab => ?_⟩
  obtain ⟨a', ha', b', hb', h⟩ := hrel _ hab
  obtain ⟨rfl, rfl⟩ := pair_inj.1 h
  have h1 : ({a} : ZFSet.{u}) ∈ B :=
    hBt _ (hRB hab) _ singleton_mem_pair (hU.isSetOf_singleton ha').1
  have h2 : ({a, b} : ZFSet.{u}) ∈ B :=
    hBt _ (hRB hab) _ pair_mem_pair (hU.isSetOf_pair ha' hb').1
  exact ⟨hBt _ h1 a (mem_singleton.2 rfl) ha', hBt _ h2 b (by simp) hb'⟩

/-- **Section 13.5, relations and functions (5a).** The domain of a binary relation in
$`\mathbb U` is in $`\mathbb U`. -/
theorem isSetOf_dom (hR : IsSetOf U R) (hrel : RelIn U R) : IsSetOf U (dom R) := by
  obtain ⟨B, hB, h⟩ := hU.exists_transitive_of_relIn hR hrel
  refine hU.isSetOf_of_subset hB fun a ha => ?_
  obtain ⟨b, hb⟩ := mem_dom.1 ha
  exact (h a b hb).1

/-- **Section 13.5, relations and functions (5b).** The range of a binary relation in
$`\mathbb U` is in $`\mathbb U`. -/
theorem isSetOf_ran (hR : IsSetOf U R) (hrel : RelIn U R) : IsSetOf U (ran R) := by
  obtain ⟨B, hB, h⟩ := hU.exists_transitive_of_relIn hR hrel
  refine hU.isSetOf_of_subset hB fun b hb => ?_
  obtain ⟨a, ha⟩ := mem_ran.1 hb
  exact (h a b ha).2

/-- **Section 13.5, relations and functions (5c).** The image $`R'(C)` of any set under a
binary relation in $`\mathbb U` is in $`\mathbb U`. The book takes
$`C \subseteq \operatorname{dom} R`; the restriction is not needed. -/
theorem isSetOf_relImage (hR : IsSetOf U R) (hrel : RelIn U R) (C : ZFSet.{u}) :
    IsSetOf U (relImage R C) :=
  hU.isSetOf_of_subset (hU.isSetOf_ran hR hrel) sep_subset

/-- The inverse image of any set under a binary relation in $`\mathbb U` is in
$`\mathbb U`. -/
theorem isSetOf_relPreimage (hR : IsSetOf U R) (hrel : RelIn U R) (D : ZFSet.{u}) :
    IsSetOf U (relPreimage R D) :=
  hU.isSetOf_of_subset (hU.isSetOf_dom hR hrel) sep_subset

/-- **Section 13.5, relations and functions (5d).** The inverse $`R^{-1}` of a binary
relation in $`\mathbb U` is in $`\mathbb U`. -/
theorem isSetOf_relInv (hR : IsSetOf U R) (hrel : RelIn U R) : IsSetOf U (relInv R) :=
  hU.isSetOf_of_subset (hU.isSetOf_prod (hU.isSetOf_ran hR hrel) (hU.isSetOf_dom hR hrel))
    sep_subset

/-- **Section 13.5, relations and functions (6).** The composite of two binary relations in
$`\mathbb U` is in $`\mathbb U`. -/
theorem isSetOf_relComp (hR : IsSetOf U R) (hrel : RelIn U R) (hS : IsSetOf U S)
    (hrelS : RelIn U S) : IsSetOf U (relComp R S) :=
  hU.isSetOf_of_subset (hU.isSetOf_prod (hU.isSetOf_dom hR hrel) (hU.isSetOf_ran hS hrelS))
    sep_subset

/-- **Section 13.5, relations and functions (7a).** A function $`f : A \to B` between sets of
$`\mathbb U` is in $`\mathbb U`. -/
theorem isSetOf_of_isFunc (hA : IsSetOf U A) (hB : IsSetOf U B) (hf : IsFunc A B f) :
    IsSetOf U f :=
  hU.isSetOf_of_subset_prod hA hB hf.1

/-- **Section 13.5, relations and functions (7b).** For a function $`f : A \to B` between
sets of $`\mathbb U` and any $`C`, the image $`f'(C) = \{f(a) : a \in C\}` is in
$`\mathbb U`. -/
theorem isSetOf_image_of_isFunc (hA : IsSetOf U A) (hB : IsSetOf U B) (hf : IsFunc A B f)
    (C : ZFSet.{u}) : IsSetOf U (relImage f C) :=
  hU.isSetOf_relImage (hU.isSetOf_of_isFunc hA hB hf) (hU.relIn_of_subset_prod hA hB hf.1) C

/-- **Section 13.5, relations and functions (7c).** For a function $`f : A \to B` between
sets of $`\mathbb U` and any $`D`, the inverse image $`f^{-1}(D) = \{a \in A : f(a) \in D\}`
is in $`\mathbb U`. -/
theorem isSetOf_preimage_of_isFunc (hA : IsSetOf U A) (hB : IsSetOf U B) (hf : IsFunc A B f)
    (D : ZFSet.{u}) : IsSetOf U (relPreimage f D) :=
  hU.isSetOf_relPreimage (hU.isSetOf_of_isFunc hA hB hf) (hU.relIn_of_subset_prod hA hB hf.1) D

/-- **Section 13.5, relations and functions (8).** If $`A` and $`B` are sets in $`\mathbb U`,
then the set $`B^A` of all functions from $`A` to $`B` (Mathlib's {name}`ZFSet.funs`) is in
$`\mathbb U`. -/
theorem isSetOf_funs (hA : IsSetOf U A) (hB : IsSetOf U B) : IsSetOf U (funs A B) :=
  hU.isSetOf_of_subset (hU.isSetOf_powerset (hU.isSetOf_prod hA hB)) sep_subset

end IsUniverse

/-- **Section 13.5, products of families.** For a family $`(A_i)_{i \in I}`, given as a set
function $`A` with $`A_i` the value {lit}`app A i`, the product $`\prod_{i \in I} A_i` is the
set of all functions $`g` on $`I` with $`g(i) \in A_i` for every $`i \in I`. -/
def piSet (I A : ZFSet.{u}) : ZFSet.{u} :=
  (funs I (⋃₀ (ran A))).sep fun g => ∀ i ∈ I, app g i ∈ app A i

/-- **Section 13.5, relations and functions (9).** If the index set $`I` and the set
$`\{A_i : i \in I\}` of members of the family (the range of $`A`) are sets in $`\mathbb U`,
and each member of the family is a set, then $`\prod_{i \in I} A_i \in \mathbb U`. -/
theorem IsUniverse.isSetOf_piSet (hU : IsUniverse U) {I : ZFSet.{u}} (hI : IsSetOf U I)
    (hA : IsSetOf U (ran A)) (hsets : ∀ s ∈ ran A, IsSetOf U s) : IsSetOf U (piSet I A) :=
  hU.isSetOf_sep (hU.isSetOf_funs hI (hU.isSetOf_sUnion hA hsets)) _

/-!
## 13.6 Superstructures

Universes exist. Starting from a set $`X`, put $`\mathbb U_0(X) = X` and
$`\mathbb U_{n+1}(X) = \mathbb U_n(X) \cup \mathcal P(\mathbb U_n(X))`; the union
$`\mathbb U(X)` of this increasing chain is the superstructure over $`X`. If the members of
$`X` behave as individuals relative to $`\mathbb U(X)`, then $`\mathbb U(X)` is a universe
over $`X`, and it is the smallest universe having $`X` as one of its sets.

In the book the members of $`X` are individuals by decree. Here that is the hypothesis
{lit}`IsBaseSet`, and {lit}`exists_isBaseSet` shows that every type has a copy inside
{name}`ZFSet` that satisfies it, so there is a superstructure over (a copy of) any set
whatever, in particular over the real numbers.
-/

/-- **Section 13.6, cumulative power sets.** $`\mathbb U_0(X) = X` and
$`\mathbb U_{n+1}(X) = \mathbb U_n(X) \cup \mathcal P(\mathbb U_n(X))`. -/
def cumPow (X : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => X
  | n + 1 => cumPow X n ∪ powerset (cumPow X n)

/-- **Section 13.6, superstructure.** The superstructure
$`\mathbb U(X) = \bigcup_n \mathbb U_n(X)` over $`X`. -/
def superstructure (X : ZFSet.{u}) : ZFSet.{u} := ⋃₀ (ZFSet.range (cumPow X))

@[simp]
theorem cumPow_zero : cumPow X 0 = X := rfl

theorem cumPow_succ (n : ℕ) : cumPow X (n + 1) = cumPow X n ∪ powerset (cumPow X n) := rfl

/-- An entity is in the superstructure exactly when it is in one of the cumulative power
sets. -/
theorem mem_superstructure : a ∈ superstructure X ↔ ∃ n, a ∈ cumPow X n := by
  rw [superstructure, mem_sUnion]
  constructor
  · rintro ⟨z, hz, ha⟩
    obtain ⟨n, rfl⟩ := mem_range.1 hz
    exact ⟨n, ha⟩
  · rintro ⟨n, ha⟩
    exact ⟨_, mem_range.2 ⟨n, rfl⟩, ha⟩

theorem cumPow_subset_succ (n : ℕ) : cumPow X n ⊆ cumPow X (n + 1) := fun _ h =>
  mem_union.2 (Or.inl h)

/-- **Section 13.6.** The cumulative power sets increase:
$`\mathbb U_0(X) \subseteq \mathbb U_1(X) \subseteq \cdots`. -/
theorem cumPow_mono {m n : ℕ} (h : m ≤ n) : cumPow X m ⊆ cumPow X n := by
  induction h with
  | refl => exact fun _ h => h
  | step _ ih => exact fun _ h => cumPow_subset_succ _ (ih h)

theorem cumPow_subset_superstructure (n : ℕ) : cumPow X n ⊆ superstructure X := fun _ h =>
  mem_superstructure.2 ⟨n, h⟩

/-- **Section 13.6, rank.** The rank of an entity of the superstructure is the least $`n`
with $`a \in \mathbb U_n(X)` (and is $`0` for entities outside the superstructure). -/
def rank (X a : ZFSet.{u}) : ℕ := sInf {n | a ∈ cumPow X n}

/-- An entity of the superstructure lies in $`\mathbb U_n(X)` exactly from its rank on. -/
theorem mem_cumPow_iff_rank_le (ha : a ∈ superstructure X) {n : ℕ} :
    a ∈ cumPow X n ↔ rank X a ≤ n := by
  have hne : {n | a ∈ cumPow X n}.Nonempty := mem_superstructure.1 ha
  exact ⟨fun h => Nat.sInf_le h, fun h => cumPow_mono h (Nat.sInf_mem hne)⟩

/-- The entities of rank $`0` are the members of $`X`. -/
theorem rank_eq_zero_iff (ha : a ∈ superstructure X) : rank X a = 0 ↔ a ∈ X := by
  rw [← Nat.le_zero, ← mem_cumPow_iff_rank_le ha, cumPow_zero]

/-- **Section 13.6 (1).** $`\mathbb U_{n+1}(X) = X \cup \mathcal P(\mathbb U_n(X))`. -/
theorem cumPow_succ_eq (n : ℕ) : cumPow X (n + 1) = X ∪ powerset (cumPow X n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cumPow_succ (n + 1)]
    ext a
    simp only [mem_union, mem_powerset]
    constructor
    · rintro (h | h)
      · rw [ih] at h
        rcases mem_union.1 h with h | h
        · exact Or.inl h
        · exact Or.inr fun x hx => cumPow_subset_succ n (mem_powerset.1 h hx)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (cumPow_mono (Nat.zero_le _) h)
      · exact Or.inr h

/-- **Section 13.6 (2).** $`\mathbb U_n(X) \in \mathbb U_{n+1}(X)`. -/
theorem cumPow_mem_succ (n : ℕ) : cumPow X n ∈ cumPow X (n + 1) :=
  mem_union.2 (Or.inr (mem_powerset.2 fun _ h => h))

/-- **Section 13.6 (2).** Each $`\mathbb U_n(X)` belongs to the superstructure. -/
theorem cumPow_mem_superstructure (n : ℕ) : cumPow X n ∈ superstructure X :=
  mem_superstructure.2 ⟨n + 1, cumPow_mem_succ n⟩

/-- **Section 13.6 (2).** In particular $`X \in \mathbb U(X)`. -/
theorem base_mem_superstructure : X ∈ superstructure X := cumPow_mem_superstructure 0

/-- A member of $`\mathbb U_{n+1}(X)` that is not in $`X` is a subset of
$`\mathbb U_n(X)`. -/
theorem subset_cumPow_of_mem_succ {n : ℕ} (hB : B ∈ cumPow X (n + 1)) (hBX : B ∉ X) :
    B ⊆ cumPow X n := by
  rw [cumPow_succ_eq] at hB
  rcases mem_union.1 hB with h | h
  · exact absurd h hBX
  · exact mem_powerset.1 h

/-- **Section 13.6 (3).** If $`a \in B \in \mathbb U_{n+1}(X)` and $`B` is a set (not a
member of $`X`), then $`a \in \mathbb U_n(X)`. -/
theorem mem_cumPow_of_mem_of_mem_succ {n : ℕ} (hB : B ∈ cumPow X (n + 1)) (hBX : B ∉ X)
    (ha : a ∈ B) : a ∈ cumPow X n :=
  subset_cumPow_of_mem_succ hB hBX ha

/-- A subset of $`\mathbb U_n(X)` is a member of $`\mathbb U_{n+1}(X)`. -/
theorem mem_cumPow_succ_of_subset {n : ℕ} (h : A ⊆ cumPow X n) : A ∈ cumPow X (n + 1) :=
  mem_union.2 (Or.inr (mem_powerset.2 h))

/-- A member of the superstructure that is not in $`X` is a subset of some
$`\mathbb U_n(X)`. -/
theorem exists_subset_cumPow (hA : A ∈ superstructure X) (hAX : A ∉ X) :
    ∃ n, A ⊆ cumPow X n := by
  obtain ⟨n, hn⟩ := mem_superstructure.1 hA
  cases n with
  | zero => exact absurd hn hAX
  | succ n => exact ⟨n, subset_cumPow_of_mem_succ hn hAX⟩

/-- **Section 13.6 (4).** If $`a, b \in \mathbb U_n(X)` then
$`\{a, b\} \in \mathbb U_{n+1}(X)`. -/
theorem pair_mem_cumPow_succ {n : ℕ} (ha : a ∈ cumPow X n) (hb : b ∈ cumPow X n) :
    ({a, b} : ZFSet.{u}) ∈ cumPow X (n + 1) :=
  mem_cumPow_succ_of_subset fun x hx => by
    rcases mem_pair.1 hx with rfl | rfl <;> assumption

/-- **Section 13.6 (5).** If $`A, B \in \mathbb U_n(X)` are sets (not members of $`X`), then
$`A \cup B \in \mathbb U_{n+1}(X)`; in fact already $`A \cup B \in \mathbb U_n(X)`. -/
theorem union_mem_cumPow {n : ℕ} (hA : A ∈ cumPow X n) (hAX : A ∉ X) (hB : B ∈ cumPow X n)
    (hBX : B ∉ X) : A ∪ B ∈ cumPow X n ∧ A ∪ B ∈ cumPow X (n + 1) := by
  cases n with
  | zero => exact absurd hA hAX
  | succ n =>
    have h : A ∪ B ∈ cumPow X (n + 1) := mem_cumPow_succ_of_subset fun x hx => by
      rcases mem_union.1 hx with h | h
      · exact subset_cumPow_of_mem_succ hA hAX h
      · exact subset_cumPow_of_mem_succ hB hBX h
    exact ⟨h, cumPow_subset_succ _ h⟩

/-- **Section 13.6 (6).** If $`A \in \mathbb U_n(X)` is a set (not a member of $`X`), then
$`\mathcal P(A) \in \mathbb U_{n+2}(X)`; in fact already
$`\mathcal P(A) \in \mathbb U_{n+1}(X)`. -/
theorem powerset_mem_cumPow {n : ℕ} (hA : A ∈ cumPow X n) (hAX : A ∉ X) :
    powerset A ∈ cumPow X (n + 1) ∧ powerset A ∈ cumPow X (n + 2) := by
  cases n with
  | zero => exact absurd hA hAX
  | succ n =>
    have h : powerset A ∈ cumPow X (n + 1 + 1) := mem_cumPow_succ_of_subset fun x hx =>
      mem_cumPow_succ_of_subset fun y hy =>
        subset_cumPow_of_mem_succ hA hAX (mem_powerset.1 hx hy)
    exact ⟨h, cumPow_subset_succ _ h⟩

/-- **Section 13.6, the individuals of a superstructure.** $`X` is a base set when each of
its members is an individual relative to the superstructure over $`X`: it is nonempty and no
member of $`\mathbb U(X)` is a member of it. This is the book's displayed condition on the
entities of rank $`0`. -/
def IsBaseSet (X : ZFSet.{u}) : Prop := ∀ x ∈ X, IsIndividual (superstructure X) x

/-- Over a base set, the sets of the superstructure are its members of positive rank, that
is, those not in $`X`. -/
theorem isSetOf_superstructure_iff (hX : IsBaseSet X) :
    IsSetOf (superstructure X) A ↔ A ∈ superstructure X ∧ A ∉ X := by
  constructor
  · exact fun h => ⟨h.1, fun hAX => h.2 (hX A hAX)⟩
  · rintro ⟨hA, hAX⟩
    obtain ⟨n, hn⟩ := exists_subset_cumPow hA hAX
    exact isSetOf_of_subset hA fun x hx => cumPow_subset_superstructure n (hn hx)

/-- **Section 13.6 (3).** Over a base set, each $`\mathbb U_{n+1}(X)` is transitive. -/
theorem transitiveIn_cumPow_succ (hX : IsBaseSet X) (n : ℕ) :
    TransitiveIn (superstructure X) (cumPow X (n + 1)) := by
  intro y hy z hz hzU
  by_cases hyX : y ∈ X
  · exact absurd hz ((hX y hyX).2 z hzU)
  · exact cumPow_subset_succ n (subset_cumPow_of_mem_succ hy hyX hz)

/-- **Section 13.6.** The superstructure over a base set $`X` is a universe over $`X`: it is
strongly transitive by (3), closed under pairs, unions and power sets by (4) to (6), and
contains $`X` by (2). -/
theorem isUniverseOver_superstructure (hX : IsBaseSet X) :
    IsUniverseOver (superstructure X) X := by
  have hXset : IsSetOf (superstructure X) X :=
    isSetOf_of_subset base_mem_superstructure (cumPow_subset_superstructure 0)
  refine ⟨⟨?_, ?_, ?_, ?_, ⟨X, hXset⟩⟩, hXset, hX⟩
  · intro A hA
    obtain ⟨hA, hAX⟩ := (isSetOf_superstructure_iff hX).1 hA
    obtain ⟨n, hn⟩ := exists_subset_cumPow hA hAX
    exact ⟨cumPow X (n + 1), cumPow_mem_superstructure _, transitiveIn_cumPow_succ hX n,
      fun x hx => cumPow_subset_succ n (hn hx), cumPow_subset_superstructure _⟩
  · intro a ha b hb
    obtain ⟨m, hm⟩ := mem_superstructure.1 ha
    obtain ⟨n, hn⟩ := mem_superstructure.1 hb
    exact mem_superstructure.2 ⟨max m n + 1, pair_mem_cumPow_succ
      (cumPow_mono (le_max_left m n) hm) (cumPow_mono (le_max_right m n) hn)⟩
  · intro A B hA hB
    obtain ⟨hA, hAX⟩ := (isSetOf_superstructure_iff hX).1 hA
    obtain ⟨hB, hBX⟩ := (isSetOf_superstructure_iff hX).1 hB
    obtain ⟨m, hm⟩ := mem_superstructure.1 hA
    obtain ⟨n, hn⟩ := mem_superstructure.1 hB
    exact mem_superstructure.2 ⟨max m n, (union_mem_cumPow
      (cumPow_mono (le_max_left m n) hm) hAX (cumPow_mono (le_max_right m n) hn) hBX).1⟩
  · intro A hA
    obtain ⟨hA, hAX⟩ := (isSetOf_superstructure_iff hX).1 hA
    obtain ⟨n, hn⟩ := mem_superstructure.1 hA
    exact mem_superstructure.2 ⟨n + 1, (powerset_mem_cumPow hn hAX).1⟩

/-- No cumulative power set is a member of $`X`. -/
theorem cumPow_notMem_base (n : ℕ) : cumPow X n ∉ X := fun h =>
  mem_irrefl _ (cumPow_mono (Nat.zero_le n) h)

/-- **Section 13.6, minimality.** The superstructure over $`X` is the smallest universe
containing $`X`: if a universe $`\mathbb U` has $`X` as one of its sets, then
$`\mathbb U(X) \subseteq \mathbb U`. -/
theorem superstructure_subset_of_isUniverse (hU : IsUniverse U) (hX : IsSetOf U X) :
    superstructure X ⊆ U := by
  have h : ∀ n, IsSetOf U (cumPow X n) := fun n => by
    induction n with
    | zero => exact hX
    | succ n ih => exact hU.isSetOf_union ih (hU.isSetOf_powerset ih)
  intro a ha
  obtain ⟨n, hn⟩ := mem_superstructure.1 ha
  exact hU.subset (h n) hn

/-- **Section 13.6, minimality (second form).** The superstructure over $`X` is included in
every set $`W` that contains $`X`, is transitive (every member of $`W` that is not in $`X` is
a subset of $`W`, and so is $`X`), and is closed under binary unions and power sets of its
members not in $`X`. -/
theorem superstructure_subset_of_closed {W : ZFSet.{u}} (hXW : X ∈ W) (hXsub : X ⊆ W)
    (htrans : ∀ A ∈ W, A ∉ X → A ⊆ W)
    (hunion : ∀ A ∈ W, ∀ B ∈ W, A ∉ X → B ∉ X → A ∪ B ∈ W)
    (hpow : ∀ A ∈ W, A ∉ X → powerset A ∈ W) : superstructure X ⊆ W := by
  have h : ∀ n, cumPow X n ∈ W := fun n => by
    induction n with
    | zero => exact hXW
    | succ n ih =>
      exact hunion _ ih _ (hpow _ ih (cumPow_notMem_base n)) (cumPow_notMem_base n) fun h =>
        mem_asymm (mem_powerset.2 fun _ h => h) (cumPow_mono (Nat.zero_le n) h)
  intro a ha
  obtain ⟨n, hn⟩ := mem_superstructure.1 ha
  cases n with
  | zero => exact hXsub hn
  | succ n => exact htrans _ (h (n + 1)) (cumPow_notMem_base _) hn

/-- **Exercise 13.6.1, monotonicity of the cumulative power sets.** If $`X \subseteq Y` then
$`\mathbb U_n(X) \subseteq \mathbb U_n(Y)` for every $`n`. -/
theorem cumPow_subset_cumPow (h : X ⊆ Y) (n : ℕ) : cumPow X n ⊆ cumPow Y n := by
  induction n with
  | zero => exact h
  | succ n ih =>
    intro a ha
    rcases mem_union.1 ha with ha | ha
    · exact mem_union.2 (Or.inl (ih ha))
    · exact mem_union.2 (Or.inr (mem_powerset.2 fun x hx => ih (mem_powerset.1 ha hx)))

/-- **Exercise 13.6.1, monotonicity.** If $`X \subseteq Y` then
$`\mathbb U(X) \subseteq \mathbb U(Y)`. In particular, when $`\mathbb R \subseteq X
\subseteq Y`, one gets $`\mathbb U(\mathbb R) \subseteq \mathbb U(X) \subseteq
\mathbb U(Y)`. -/
theorem superstructure_mono (h : X ⊆ Y) : superstructure X ⊆ superstructure Y := fun _ ha =>
  let ⟨n, hn⟩ := mem_superstructure.1 ha
  mem_superstructure.2 ⟨n, cumPow_subset_cumPow h n hn⟩

/-- **Section 13.6, bounded rank.** Over a base set, a set $`A` belongs to the superstructure
(as a set, that is, as a member not in $`X`) if and only if there is a bound on the ranks of
its members: $`A \subseteq \mathbb U_n(X)` for some $`n`. Thus a universe is not closed under
arbitrary subsets. -/
theorem mem_superstructure_iff_exists_subset_cumPow (hX : IsBaseSet X) :
    (A ∈ superstructure X ∧ A ∉ X) ↔ ∃ n, A ⊆ cumPow X n := by
  constructor
  · exact fun h => exists_subset_cumPow h.1 h.2
  · rintro ⟨n, hn⟩
    refine ⟨mem_superstructure.2 ⟨n + 1, mem_cumPow_succ_of_subset hn⟩, fun hAX => ?_⟩
    obtain ⟨hne, hall⟩ := hX A hAX
    refine hne ((eq_empty A).2 fun y hy => hall y (cumPow_subset_superstructure n (hn hy)) hy)

/-- **Section 13.6.** The superstructure is not a member of itself, although it is a subset
of itself: a universe is not closed under arbitrary subsets. -/
theorem superstructure_notMem_self : superstructure X ∉ superstructure X := mem_irrefl _

/-- **Section 13.6, rank of relations.** If $`A, B \in \mathbb U_n(X)` are sets, then every
subset of $`A \times B`, in particular every function from $`A` to $`B`, is in
$`\mathbb U_{n+2}(X)`: forming a function between given sets raises the rank by at most
$`2`. -/
theorem mem_cumPow_of_subset_prod {n : ℕ} (hA : A ∈ cumPow X n) (hAX : A ∉ X)
    (hB : B ∈ cumPow X n) (hBX : B ∉ X) (hR : R ⊆ prod A B) : R ∈ cumPow X (n + 2) := by
  cases n with
  | zero => exact absurd hA hAX
  | succ n =>
    refine mem_cumPow_succ_of_subset fun p hp => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 (hR hp)
    have ha' := subset_cumPow_of_mem_succ hA hAX ha
    have hb' := subset_cumPow_of_mem_succ hB hBX hb
    have h1 : ({a} : ZFSet.{u}) ∈ cumPow X (n + 1) :=
      mem_cumPow_succ_of_subset fun x hx => mem_singleton.1 hx ▸ ha'
    exact pair_mem_cumPow_succ h1 (pair_mem_cumPow_succ ha' hb')

/-- **Section 13.6, low ranks.** A topology on $`X`, or any other collection of subsets of
$`X`, belongs to $`\mathbb U_2(X)`. -/
theorem mem_cumPow_two_of_subset_powerset {T : ZFSet.{u}} (hT : T ⊆ powerset X) :
    T ∈ cumPow X 2 :=
  mem_cumPow_succ_of_subset fun _ hs => mem_cumPow_succ_of_subset (mem_powerset.1 (hT hs))

/-- **Section 13.6, existence of superstructures.** Every type $`\alpha` (for instance the
real numbers) has a copy inside {name}`ZFSet` that is a base set: there is an injection of
$`\alpha` into {name}`ZFSet` whose range $`X` consists of individuals relative to
$`\mathbb U(X)`. Consequently the superstructure over that copy is a universe over it
({lit}`isUniverseOver_superstructure`). The individual assigned to a point is a singleton
whose only member contains the set of all numerals, which has no finite rank over $`X`. -/
theorem exists_isBaseSet (α : Type u) :
    ∃ ι : α → ZFSet.{u}, Function.Injective ι ∧ IsBaseSet (ZFSet.range ι) := by
  classical
  let g : α → ZFSet.{u} := fun a => (Ordinal.typein (WellOrderingRel (α := α)) a).toZFSet
  have hg : Function.Injective g := fun a b h =>
    Ordinal.typein_injective _ (Ordinal.toZFSet_injective h)
  let t : α → ZFSet.{u} := fun a => {omega, g a}
  let ι : α → ZFSet.{u} := fun a => {t a}
  have hnumω : ∀ k, (num k : ZFSet.{u}) ∈ omega := fun k => by
    induction k with
    | zero => exact omega_zero
    | succ k ih => exact omega_succ ih
  have hιne : ∀ a, (∅ : ZFSet.{u}) ∉ ι a := fun a h => by
    have h1 : (∅ : ZFSet.{u}) = t a := mem_singleton.1 h
    have h2 : (omega : ZFSet.{u}) ∈ t a := by simp [t]
    rw [← h1] at h2
    exact notMem_empty _ h2
  set X := ZFSet.range ι with hXdef
  have hnumX : ∀ k, (num k : ZFSet.{u}) ∉ X := fun k hk => by
    obtain ⟨a, ha⟩ := mem_range.1 hk
    cases k with
    | zero =>
      have : t a ∈ (num 0 : ZFSet.{u}) := ha ▸ mem_singleton.2 rfl
      exact notMem_empty _ this
    | succ k =>
      have : (num 0 : ZFSet.{u}) ∈ num (k + 1) := num_mem_num_of_lt (Nat.succ_pos k)
      rw [← ha] at this
      exact hιne a this
  have hnum : ∀ n, (num (n + 1) : ZFSet.{u}) ∉ cumPow X n := fun n => by
    induction n with
    | zero => exact hnumX 1
    | succ n ih =>
      intro h
      exact ih (subset_cumPow_of_mem_succ h (hnumX _) (num_mem_num_of_lt (Nat.lt_succ_self _)))
  have hωX : (omega : ZFSet.{u}) ∉ X := fun h => by
    obtain ⟨a, ha⟩ := mem_range.1 h
    exact hιne a (ha ▸ omega_zero)
  have hω : ∀ n, (omega : ZFSet.{u}) ∉ cumPow X n := fun n => by
    cases n with
    | zero => exact hωX
    | succ n => exact fun h => hnum n (subset_cumPow_of_mem_succ h hωX (hnumω _))
  have htX : ∀ a, t a ∉ X := fun a h => by
    obtain ⟨b, hb⟩ := mem_range.1 h
    have h1 : (omega : ZFSet.{u}) ∈ ι b := hb ▸ (by simp [t] : (omega : ZFSet.{u}) ∈ t a)
    have h2 : (omega : ZFSet.{u}) = t b := mem_singleton.1 h1
    have h3 : (omega : ZFSet.{u}) ∈ t b := by simp [t]
    rw [← h2] at h3
    exact mem_irrefl _ h3
  have ht : ∀ a n, t a ∉ cumPow X n := fun a n => by
    cases n with
    | zero => exact htX a
    | succ n => exact fun h => hω n (subset_cumPow_of_mem_succ h (htX a) (by simp [t]))
  refine ⟨ι, fun a b h => ?_, fun x hx => ?_⟩
  · have h1 : t a = t b := singleton_injective h
    have h2 : g a ∈ t b := h1 ▸ (by simp [t] : g a ∈ t a)
    have h3 : g b ∈ t a := h1 ▸ (by simp [t] : g b ∈ t b)
    simp only [t, mem_pair] at h2 h3
    rcases h2 with h2 | h2
    · rcases h3 with h3 | h3
      · exact hg (h2.trans h3.symm)
      · exact hg h3.symm
    · exact hg h2
  · obtain ⟨a, rfl⟩ := mem_range.1 hx
    refine ⟨fun h => notMem_empty (t a) (h ▸ mem_singleton.2 rfl), fun y hy hya => ?_⟩
    obtain ⟨n, hn⟩ := mem_superstructure.1 hy
    rw [mem_singleton.1 hya] at hn
    exact ht a n hn

/-- **Section 13.6, existence of universes.** Over every type there is a universe: a copy
$`X` of the type inside {name}`ZFSet` together with a universe over $`X`. -/
theorem exists_isUniverseOver (α : Type u) :
    ∃ (ι : α → ZFSet.{u}) (U : ZFSet.{u}), Function.Injective ι ∧
      IsUniverseOver U (ZFSet.range ι) :=
  let ⟨ι, hι, hX⟩ := exists_isBaseSet α
  ⟨ι, _, hι, isUniverseOver_superstructure hX⟩

end Goldblatt
