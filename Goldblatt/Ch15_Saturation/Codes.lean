import Goldblatt.Ch14_Enlargements

/-!
# 15 (part 1). Standard relations and the hyperreal order

This is the first of seven parts of Chapter 15 (the overview is on the chapter page
{lit}`Goldblatt.Ch15_Saturation`). It contains no numbered item of the book. It prepares the
ground for Sections 15.1 to 15.4, whose statements speak of infinitesimal, limited and
unlimited members of the transform of the real numbers inside an arbitrary nonstandard
framework, where no ultrapower is available to compute with.

Every fact about hyperreal numbers that those sections use is the transform of a fact about
real numbers. To obtain such facts without writing a formula of the language of the universe
each time, relations between real numbers (and between pairs of real numbers) are turned into
sets of the universe in a uniform way, and the preservation properties of the transfer map
from Chapter 13 (subsets, intersections, composites, inverses, domains, inverse images) are
restated for them. A fact about real numbers then transfers by one application of a lemma of
this page.
-/

noncomputable section

namespace Goldblatt

open ZFSet

universe u

namespace NonstandardFramework

variable (F : NonstandardFramework.{u})

/-!
## Encodings of types in the universe

A _code_ for a type is an injection of the type into the standard universe whose values are
fixed by the transfer map and whose range is a set of the universe. The real numbers of a
framework over the reals are the basic example, and codes are closed under products. A set of
members of the type, and a relation between two coded types, then become sets of the
universe.
-/

/-- An encoding of a type in the standard universe of a framework: an injection whose values
are fixed by the transfer map and whose range is a set of the universe. -/
structure Code (α : Type) where
  /-- The entity of the universe that represents a member of the type. -/
  enc : α → ZFSet.{u}
  /-- Distinct members are represented by distinct entities. -/
  enc_injective : Function.Injective enc
  /-- The transfer map fixes every representative. -/
  star_enc : ∀ a, F.star (enc a) = enc a
  /-- The representatives form a set of the universe. -/
  isSetOf_range : IsSetOf F.U (ZFSet.range enc)

namespace Code

variable {F}
variable {α β γ : Type} (c : F.Code α) (d : F.Code β) (e : F.Code γ)
variable {S T : Set α} {P Q : α → β → Prop} {x y z : ZFSet.{u}} {a : α} {b : β}

/-- The set of the universe that represents a set of members of a coded type. -/
def set (S : Set α) : ZFSet.{u} := ZFSet.range fun a : S => c.enc a

/-- The members of the set representing $`S` are the representatives of the members of
$`S`. -/
theorem mem_set : x ∈ c.set S ↔ ∃ a ∈ S, x = c.enc a := by
  rw [set, mem_range]
  exact ⟨fun ⟨a, h⟩ => ⟨a.1, a.2, h.symm⟩, fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h.symm⟩⟩

/-- A representative belongs to the set representing $`S` exactly when the member it
represents belongs to $`S`. -/
@[simp]
theorem enc_mem_set : c.enc a ∈ c.set S ↔ a ∈ S := by
  rw [mem_set]
  exact ⟨fun ⟨a', ha', h⟩ => c.enc_injective h ▸ ha', fun h => ⟨a, h, rfl⟩⟩

/-- The set representing the whole type is the range of the encoding. -/
theorem set_univ : c.set Set.univ = ZFSet.range c.enc := by
  ext x
  rw [mem_set, mem_range]
  exact ⟨fun ⟨a, _, h⟩ => ⟨a, h.symm⟩, fun ⟨a, h⟩ => ⟨a, Set.mem_univ a, h.symm⟩⟩

/-- Representing sets is monotone. -/
theorem set_mono (h : S ⊆ T) : c.set S ⊆ c.set T := fun x hx => by
  obtain ⟨a, ha, rfl⟩ := c.mem_set.1 hx
  exact c.enc_mem_set.2 (h ha)

/-- The set representing a set of members of a coded type is a set of the universe. -/
theorem isSetOf_set (S : Set α) : IsSetOf F.U (c.set S) :=
  F.hU.isSetOf_of_subset c.isSetOf_range (c.set_univ ▸ c.set_mono (Set.subset_univ S))

/-- Every representative belongs to the universe. -/
theorem enc_mem_U (a : α) : c.enc a ∈ F.U :=
  F.hU.mem_of_mem c.isSetOf_range (mem_range.2 ⟨a, rfl⟩)

/-- **Transfer at standard members.** A representative belongs to the transform of the set
representing $`S` exactly when the member it represents belongs to $`S`. -/
@[simp]
theorem enc_mem_star_set : c.enc a ∈ F.star (c.set S) ↔ a ∈ S := by
  have := F.star_mem_star_iff (c.enc_mem_U a) (c.isSetOf_set S).1
  rw [c.star_enc] at this
  rw [this, c.enc_mem_set]

/-- **Transfer of an inclusion.** If $`S \subseteq T` then the transform of the set
representing $`S` is included in that of the set representing $`T`. -/
theorem star_set_mono (h : S ⊆ T) : F.star (c.set S) ⊆ F.star (c.set T) :=
  (F.star_subset_star_iff (c.isSetOf_set S) (c.isSetOf_set T)).2 (c.set_mono h)

/-- The transform of a represented set is included in the transform of the whole type. -/
theorem star_set_subset_univ (S : Set α) : F.star (c.set S) ⊆ F.star (c.set Set.univ) :=
  c.star_set_mono (Set.subset_univ S)

/-- **Transfer of an intersection.** -/
theorem star_set_inter (S T : Set α) :
    F.star (c.set (S ∩ T)) = F.star (c.set S) ∩ F.star (c.set T) := by
  rw [← F.star_inter (c.isSetOf_set S) (c.isSetOf_set T)]
  congr 1
  ext x
  simp only [mem_set, mem_inter, Set.mem_inter_iff]
  constructor
  · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨a, h1, rfl⟩, ⟨a, h2, rfl⟩⟩
  · rintro ⟨⟨a, h1, rfl⟩, ⟨a', h2, h⟩⟩
    exact ⟨a, ⟨h1, c.enc_injective h ▸ h2⟩, rfl⟩

/-- **Transfer of a union.** -/
theorem star_set_union (S T : Set α) :
    F.star (c.set (S ∪ T)) = F.star (c.set S) ∪ F.star (c.set T) := by
  rw [← F.star_union (c.isSetOf_set S) (c.isSetOf_set T)]
  congr 1
  ext x
  simp only [mem_set, mem_union, Set.mem_union]
  constructor
  · rintro ⟨a, h1 | h2, rfl⟩
    · exact Or.inl ⟨a, h1, rfl⟩
    · exact Or.inr ⟨a, h2, rfl⟩
  · rintro (⟨a, h1, rfl⟩ | ⟨a, h2, rfl⟩)
    · exact ⟨a, Or.inl h1, rfl⟩
    · exact ⟨a, Or.inr h2, rfl⟩

/-- The transform of the set representing the empty set is empty. -/
theorem star_set_empty : F.star (c.set (∅ : Set α)) = ∅ := by
  have : c.set (∅ : Set α) = ∅ := by
    rw [eq_empty]
    intro x hx
    obtain ⟨a, ha, -⟩ := c.mem_set.1 hx
    exact ha
  rw [this, F.star_empty]

/-- **Transfer of a contradiction.** If no member of the type satisfies the condition
defining $`S`, then the transform of the set representing $`S` has no members. -/
theorem notMem_star_set (h : ∀ a, a ∉ S) : x ∉ F.star (c.set S) := by
  rw [Set.eq_empty_of_forall_notMem h, c.star_set_empty]
  exact notMem_empty x

/-- **Transfer of a finite set.** The transform of the set representing a finite set has only
the standard members. -/
theorem mem_star_set_of_finite (hS : S.Finite) : x ∈ F.star (c.set S) ↔ ∃ a ∈ S, x = c.enc a := by
  have hfin : (c.set S : Set ZFSet.{u}).Finite := by
    refine (hS.image c.enc).subset fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := c.mem_set.1 hx
    exact ⟨a, ha, rfl⟩
  rw [F.mem_star_of_finite (c.isSetOf_set S) hfin]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨a, ha, rfl⟩ := c.mem_set.1 hw
    exact ⟨a, ha, c.star_enc a⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨c.enc a, c.enc_mem_set.2 ha, (c.star_enc a).symm⟩

/-- The product of two codes: a pair is represented by the ordered pair of the
representatives. -/
def prod : F.Code (α × β) where
  enc q := pair (c.enc q.1) (d.enc q.2)
  enc_injective q q' h := by
    obtain ⟨h1, h2⟩ := pair_inj.1 h
    exact Prod.ext (c.enc_injective h1) (d.enc_injective h2)
  star_enc q := by
    rw [F.star_opair (c.enc_mem_U _) (d.enc_mem_U _), c.star_enc, d.star_enc]
  isSetOf_range := by
    have : ZFSet.range (fun q : α × β => pair (c.enc q.1) (d.enc q.2)) =
        ZFSet.prod (ZFSet.range c.enc) (ZFSet.range d.enc) := by
      ext p
      simp only [mem_range, mem_prod]
      constructor
      · rintro ⟨q, rfl⟩
        exact ⟨_, ⟨q.1, rfl⟩, _, ⟨q.2, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
        exact ⟨(a, b), rfl⟩
    rw [this]
    exact F.hU.isSetOf_prod c.isSetOf_range d.isSetOf_range

/-- The representative of a pair. -/
@[simp]
theorem prod_enc (q : α × β) : (c.prod d).enc q = pair (c.enc q.1) (d.enc q.2) := rfl

/-!
## Relations between coded types

A relation between two coded types is represented by the set of the pairs of representatives
of related members. The lemmas of this section are the working form of the transfer
principle in this chapter: each one turns a statement about the relation, proved in Lean for
members of the types, into the corresponding statement about the transform of its
representing set, for arbitrary members of the transformed types.
-/

/-- The set of pairs of the universe that represents a relation between two coded types. -/
def rel (P : α → β → Prop) : ZFSet.{u} := (c.prod d).set {q | P q.1 q.2}

/-- The members of the set representing a relation. -/
theorem pair_mem_rel : pair x y ∈ rel c d P ↔ ∃ a b, P a b ∧ x = c.enc a ∧ y = d.enc b := by
  rw [rel, mem_set]
  constructor
  · rintro ⟨q, hq, h⟩
    obtain ⟨h1, h2⟩ := pair_inj.1 h
    exact ⟨q.1, q.2, hq, h1, h2⟩
  · rintro ⟨a, b, h, rfl, rfl⟩
    exact ⟨(a, b), h, rfl⟩

/-- The set representing a relation is a set of the universe. -/
theorem isSetOf_rel (P : α → β → Prop) : IsSetOf F.U (rel c d P) := (c.prod d).isSetOf_set _

/-- The set representing a relation is included in the product of the represented types. -/
theorem rel_subset_prod (P : α → β → Prop) :
    rel c d P ⊆ ZFSet.prod (c.set Set.univ) (d.set Set.univ) := fun p hp => by
  obtain ⟨q, -, rfl⟩ := (c.prod d).mem_set.1 hp
  exact pair_mem_prod.2 ⟨c.enc_mem_set.2 (Set.mem_univ _), d.enc_mem_set.2 (Set.mem_univ _)⟩

/-- The set representing a relation is a binary relation of the universe. -/
theorem relIn_rel (P : α → β → Prop) : RelIn F.U (rel c d P) :=
  F.hU.relIn_of_subset_prod (c.isSetOf_set _) (d.isSetOf_set _) (rel_subset_prod c d P)

/-- **Transfer at standard members.** The transform of a relation holds between two
representatives exactly when the relation holds between the members they represent. -/
@[simp]
theorem pair_enc_mem_star_rel : pair (c.enc a) (d.enc b) ∈ F.star (rel c d P) ↔ P a b :=
  (c.prod d).enc_mem_star_set (a := (a, b))

/-- The transform of a relation holds only between members of the transformed types. -/
theorem mem_of_pair_mem_star_rel (h : pair x y ∈ F.star (rel c d P)) :
    x ∈ F.star (c.set Set.univ) ∧ y ∈ F.star (d.set Set.univ) :=
  pair_mem_prod.1 (F.star_subset_prod (c.isSetOf_set _) (d.isSetOf_set _)
    (rel_subset_prod c d P) h)

/-- The transform of a relation is a set of pairs. -/
theorem exists_pair_of_mem_star_rel {p : ZFSet.{u}} (h : p ∈ F.star (rel c d P)) :
    ∃ x ∈ F.star (c.set Set.univ), ∃ y ∈ F.star (d.set Set.univ), p = pair x y :=
  mem_prod.1 (F.star_subset_prod (c.isSetOf_set _) (d.isSetOf_set _) (rel_subset_prod c d P) h)

/-- The transform of the relation that always holds is the product of the transformed
types. -/
theorem pair_mem_star_rel_true :
    pair x y ∈ F.star (rel c d fun _ _ => True) ↔
      x ∈ F.star (c.set Set.univ) ∧ y ∈ F.star (d.set Set.univ) := by
  have : rel c d (fun _ _ => True) = ZFSet.prod (c.set Set.univ) (d.set Set.univ) := by
    refine le_antisymm (rel_subset_prod c d _) fun p hp => ?_
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod.1 hp
    obtain ⟨a, -, rfl⟩ := c.mem_set.1 hx
    obtain ⟨b, -, rfl⟩ := d.mem_set.1 hy
    exact (pair_mem_rel c d).2 ⟨a, b, True.intro, rfl, rfl⟩
  rw [this, F.star_prod (c.isSetOf_set _) (d.isSetOf_set _), pair_mem_prod]

/-- **Transfer of an implication.** If $`P` implies $`Q` then the transform of $`P` implies
the transform of $`Q`. -/
theorem rel_mono (h : ∀ a b, P a b → Q a b) (hxy : pair x y ∈ F.star (rel c d P)) :
    pair x y ∈ F.star (rel c d Q) :=
  (c.prod d).star_set_mono (fun q hq => h q.1 q.2 hq) hxy

/-- **Transfer of a conjunction.** -/
theorem rel_and :
    pair x y ∈ F.star (rel c d fun a b => P a b ∧ Q a b) ↔
      pair x y ∈ F.star (rel c d P) ∧ pair x y ∈ F.star (rel c d Q) := by
  have := (c.prod d).star_set_inter {q | P q.1 q.2} {q | Q q.1 q.2}
  rw [rel, rel, rel, ← mem_inter, ← this]
  rfl

/-- **Transfer of a disjunction.** -/
theorem rel_or :
    pair x y ∈ F.star (rel c d fun a b => P a b ∨ Q a b) ↔
      pair x y ∈ F.star (rel c d P) ∨ pair x y ∈ F.star (rel c d Q) := by
  have := (c.prod d).star_set_union {q | P q.1 q.2} {q | Q q.1 q.2}
  rw [rel, rel, rel, ← mem_union, ← this]
  rfl

/-- **Transfer of a universally valid disjunction.** If one of $`P` and $`Q` always holds,
then one of their transforms holds between any two members of the transformed types. -/
theorem rel_total (h : ∀ a b, P a b ∨ Q a b) (hx : x ∈ F.star (c.set Set.univ))
    (hy : y ∈ F.star (d.set Set.univ)) :
    pair x y ∈ F.star (rel c d P) ∨ pair x y ∈ F.star (rel c d Q) :=
  (rel_or c d).1 (rel_mono c d (fun a b _ => h a b) ((pair_mem_star_rel_true c d).2 ⟨hx, hy⟩))

/-- **Transfer of a contradiction.** The transform of a relation that never holds never
holds. -/
theorem notMem_star_rel (h : ∀ a b, ¬ P a b) : pair x y ∉ F.star (rel c d P) :=
  (c.prod d).notMem_star_set fun q => h q.1 q.2

/-- **Transfer of a composite.** If $`P(a, b)` and $`Q(b, c)` imply $`R(a, c)`, then the
same holds for the transforms. -/
theorem rel_comp {Q : β → γ → Prop} {R : α → γ → Prop}
    (h : ∀ a b c', P a b → Q b c' → R a c') (hxy : pair x y ∈ F.star (rel c d P))
    (hyz : pair y z ∈ F.star (rel d e Q)) : pair x z ∈ F.star (rel c e R) := by
  have hsub : relComp (rel c d P) (rel d e Q) ⊆ rel c e R := fun p hp => by
    obtain ⟨u, v, w, rfl, h1, h2⟩ := mem_relComp.1 hp
    obtain ⟨a, b, hab, rfl, rfl⟩ := (pair_mem_rel c d).1 h1
    obtain ⟨b', c', hbc, hb, rfl⟩ := (pair_mem_rel d e).1 h2
    obtain rfl := d.enc_injective hb
    exact (pair_mem_rel c e).2 ⟨a, c', h a b c' hab hbc, rfl, rfl⟩
  have hset := F.hU.isSetOf_relComp (isSetOf_rel c d P) (relIn_rel c d P) (isSetOf_rel d e Q)
    (relIn_rel d e Q)
  have := (F.star_subset_star_iff hset (isSetOf_rel c e R)).2 hsub
  rw [F.star_relComp (isSetOf_rel c d P) (relIn_rel c d P) (isSetOf_rel d e Q)
    (relIn_rel d e Q)] at this
  exact this (pair_mem_relComp.2 ⟨y, hxy, hyz⟩)

/-- **Transfer of the converse.** -/
theorem rel_swap :
    pair x y ∈ F.star (rel c d P) ↔ pair y x ∈ F.star (rel d c fun b a => P a b) := by
  have h : ∀ {α β : Type} (c : F.Code α) (d : F.Code β) (P : α → β → Prop) {x y : ZFSet.{u}},
      pair x y ∈ F.star (rel c d P) → pair y x ∈ F.star (rel d c fun b a => P a b) := by
    intro α β c d P x y hxy
    have heq : relInv (rel c d P) = rel d c fun b a => P a b := by
      ext p
      rw [mem_relInv]
      constructor
      · rintro ⟨u, v, rfl, h⟩
        obtain ⟨a, b, hab, rfl, rfl⟩ := (pair_mem_rel c d).1 h
        exact (pair_mem_rel d c).2 ⟨b, a, hab, rfl, rfl⟩
      · intro hp
        obtain ⟨q, hq, rfl⟩ := (d.prod c).mem_set.1 hp
        exact ⟨c.enc q.2, d.enc q.1, rfl, (pair_mem_rel c d).2 ⟨q.2, q.1, hq, rfl, rfl⟩⟩
    rw [← heq, F.star_relInv (isSetOf_rel c d P) (relIn_rel c d P)]
    exact pair_mem_relInv.2 hxy
  exact ⟨h c d P, h d c _⟩

/-- **Transfer of an existential statement.** A member of the transformed type is related by
the transform of $`P` to something exactly when it belongs to the transform of the set of the
members that are related by $`P` to something. -/
theorem mem_star_set_exists :
    x ∈ F.star (c.set {a | ∃ b, P a b}) ↔ ∃ y, pair x y ∈ F.star (rel c d P) := by
  have heq : dom (rel c d P) = c.set {a | ∃ b, P a b} := by
    ext u
    rw [mem_dom, mem_set]
    constructor
    · rintro ⟨v, h⟩
      obtain ⟨a, b, hab, rfl, rfl⟩ := (pair_mem_rel c d).1 h
      exact ⟨a, ⟨b, hab⟩, rfl⟩
    · rintro ⟨a, ⟨b, hab⟩, rfl⟩
      exact ⟨d.enc b, (pair_mem_rel c d).2 ⟨a, b, hab, rfl, rfl⟩⟩
  rw [← heq, F.star_dom (isSetOf_rel c d P) (relIn_rel c d P), mem_dom]

/-- **Transfer with a standard parameter on the right.** -/
theorem pair_enc_right_mem_star_rel :
    pair x (d.enc b) ∈ F.star (rel c d P) ↔ x ∈ F.star (c.set {a | P a b}) := by
  have heq : relPreimage (rel c d P) {d.enc b} = c.set {a | P a b} := by
    ext u
    rw [mem_relPreimage, mem_set]
    constructor
    · rintro ⟨v, hv, h⟩
      rw [mem_singleton] at hv
      subst hv
      obtain ⟨a, b', hab, rfl, hb⟩ := (pair_mem_rel c d).1 h
      obtain rfl := d.enc_injective hb
      exact ⟨a, hab, rfl⟩
    · rintro ⟨a, hab, rfl⟩
      exact ⟨d.enc b, mem_singleton.2 rfl, (pair_mem_rel c d).2 ⟨a, b, hab, rfl, rfl⟩⟩
  rw [← heq, F.star_relPreimage (isSetOf_rel c d P) (relIn_rel c d P)
    (F.hU.isSetOf_singleton (d.enc_mem_U b)), F.star_singleton (d.enc_mem_U b), d.star_enc,
    mem_relPreimage]
  exact ⟨fun h => ⟨_, mem_singleton.2 rfl, h⟩, fun ⟨v, hv, h⟩ => by
    rw [mem_singleton] at hv; rwa [hv] at h⟩

/-- **Transfer with a standard parameter on the left.** -/
theorem pair_enc_left_mem_star_rel :
    pair (c.enc a) y ∈ F.star (rel c d P) ↔ y ∈ F.star (d.set {b | P a b}) := by
  rw [rel_swap, pair_enc_right_mem_star_rel]

/-- **Transfer of equality.** The transform of the identity relation on a coded type is the
identity relation on the transformed type. -/
theorem pair_mem_star_rel_eq :
    pair x y ∈ F.star (rel c c fun a a' => a = a') ↔ x ∈ F.star (c.set Set.univ) ∧ x = y := by
  set A := c.set Set.univ with hA
  set D := rel c c fun a a' => a = a' with hD
  have hAset : IsSetOf F.U A := c.isSetOf_set _
  have hDset : IsSetOf F.U D := isSetOf_rel c c _
  have h := F.transfer
    (.all 0 (.const A) (.all 1 (.const A) (.biimp
      (.elem (.opair (.var 0) (.var 1)) (.const D)) (.equal (.var 0) (.var 1)))))
    (by simp [Formula.IsSentence, hAset.1, hDset.1])
  sat_simp at h
  have h' := h.1 (by
    intro u _ hu v _ hv
    obtain ⟨a, -, rfl⟩ := c.mem_set.1 hu
    obtain ⟨a', -, rfl⟩ := c.mem_set.1 hv
    rw [hD, pair_mem_rel]
    constructor
    · rintro ⟨a₁, a₂, rfl, h1, h2⟩
      rw [h1, h2]
    · intro h
      exact ⟨a, a, rfl, rfl, h.symm⟩)
  have hAU := F.star_subset_U' hAset
  constructor
  · intro hxy
    obtain ⟨hx, hy⟩ := mem_of_pair_mem_star_rel c c hxy
    exact ⟨hx, (h' x (hAU hx) hx y (hAU hy) hy).1 hxy⟩
  · rintro ⟨hx, rfl⟩
    exact (h' x (hAU hx) hx x (hAU hx) hx).2 rfl

/-- **Transfer of a reflexive relation.** If $`P(a, a)` always holds, then the transform of
$`P` holds between every member of the transformed type and itself. -/
theorem rel_refl {P : α → α → Prop} (h : ∀ a, P a a) (hx : x ∈ F.star (c.set Set.univ)) :
    pair x x ∈ F.star (rel c c P) :=
  rel_mono c c (P := fun a a' => a = a') (fun a b (hab : a = b) => hab ▸ h a)
    ((pair_mem_star_rel_eq c).2 ⟨hx, rfl⟩)

/-- **Transfer of a statement that forces equality.** -/
theorem eq_of_rel {P : α → α → Prop} (h : ∀ a b, P a b → a = b)
    (hxy : pair x y ∈ F.star (rel c c P)) : x = y :=
  ((pair_mem_star_rel_eq c).1 (rel_mono c c h hxy)).2

/-- **Transfer of a set as a relation.** A member of the transform of the set representing
$`S` is related to itself by the transform of the identity relation restricted to $`S`. -/
theorem pair_self_mem_star_rel_iff :
    pair x x ∈ F.star (rel c c fun a a' => a = a' ∧ a ∈ S) ↔ x ∈ F.star (c.set S) := by
  constructor
  · intro h
    have : x ∈ F.star (c.set {a | ∃ a', a = a' ∧ a ∈ S}) :=
      (mem_star_set_exists c c (P := fun a a' => a = a' ∧ a ∈ S)).2 ⟨x, h⟩
    exact c.star_set_mono (fun a (ha : ∃ a', a = a' ∧ a ∈ S) => ha.choose_spec.2) this
  · intro hx
    have : x ∈ F.star (c.set {a | ∃ a', a = a' ∧ a ∈ S}) :=
      c.star_set_mono (T := {a | ∃ a', a = a' ∧ a ∈ S}) (fun a (ha : a ∈ S) => ⟨a, rfl, ha⟩) hx
    obtain ⟨y, hy⟩ := (mem_star_set_exists c c (P := fun a a' => a = a' ∧ a ∈ S)).1 this
    obtain rfl := eq_of_rel c (P := fun a a' => a = a' ∧ a ∈ S) (fun a b h => h.1) hy
    exact hy

/-- **Transfer of a relation with one side restricted.** -/
theorem rel_of_mem_left (hx : x ∈ F.star (c.set S)) (hxy : pair x y ∈ F.star (rel c d P)) :
    pair x y ∈ F.star (rel c d fun a b => a ∈ S ∧ P a b) :=
  rel_comp c c d (P := fun a a' => a = a' ∧ a ∈ S) (Q := P)
    (R := fun a b => a ∈ S ∧ P a b)
    (fun a a' b h hab => by obtain ⟨rfl, hS⟩ := h; exact ⟨hS, hab⟩)
    ((pair_self_mem_star_rel_iff c).2 hx) hxy

/-- **Transfer of a relation with the other side restricted.** -/
theorem rel_of_mem_right {T : Set β} (hy : y ∈ F.star (d.set T))
    (hxy : pair x y ∈ F.star (rel c d P)) :
    pair x y ∈ F.star (rel c d fun a b => b ∈ T ∧ P a b) := by
  have h1 := rel_of_mem_left d c hy ((rel_swap c d).1 hxy)
  exact (rel_swap c d).2 h1

/-- **Transfer of a function.** For a function $`g` between coded types, every member of
the transformed domain is related to some member of the transformed codomain by the
transform of the graph of $`g`. -/
theorem exists_pair_mem_star_graph (g : α → β) (hx : x ∈ F.star (c.set Set.univ)) :
    ∃ y, pair x y ∈ F.star (rel c d fun a b => b = g a) :=
  (mem_star_set_exists c d (P := fun a b => b = g a)).1
    (c.star_set_mono (T := {a | ∃ b, b = g a}) (fun a _ => ⟨g a, rfl⟩) hx)

/-- **Transfer of a consequence for the left member.** -/
theorem mem_left_of_rel (h : ∀ a b, P a b → a ∈ S) (hxy : pair x y ∈ F.star (rel c d P)) :
    x ∈ F.star (c.set S) :=
  c.star_set_mono (fun a (ha : ∃ b, P a b) => h a ha.choose ha.choose_spec)
    ((mem_star_set_exists c d).2 ⟨y, hxy⟩)

/-- **Transfer of a consequence for the right member.** -/
theorem mem_right_of_rel {T : Set β} (h : ∀ a b, P a b → b ∈ T)
    (hxy : pair x y ∈ F.star (rel c d P)) : y ∈ F.star (d.set T) :=
  mem_left_of_rel d c (P := fun b a => P a b) (fun b a hab => h a b hab) ((rel_swap c d).1 hxy)

/-- **Transfer of the excluded middle.** A member of the transformed type belongs to the
transform of a set or to the transform of its complement. -/
theorem mem_star_set_or_compl (S : Set α) (hx : x ∈ F.star (c.set Set.univ)) :
    x ∈ F.star (c.set S) ∨ x ∈ F.star (c.set Sᶜ) := by
  rw [← mem_union, ← c.star_set_union, Set.union_compl_self]
  exact hx

/-- The transform of a set and the transform of its complement are disjoint. -/
theorem notMem_star_set_compl (hx : x ∈ F.star (c.set S)) : x ∉ F.star (c.set Sᶜ) := fun h => by
  have : x ∈ F.star (c.set (S ∩ Sᶜ)) := by
    rw [c.star_set_inter]
    exact mem_inter.2 ⟨hx, h⟩
  exact c.notMem_star_set (fun a ha => ha.2 ha.1) this

/-- The set representing a product of two sets is the product of the representing sets. -/
theorem prod_set_prod (S : Set α) (T : Set β) :
    (c.prod d).set (S ×ˢ T) = ZFSet.prod (c.set S) (d.set T) := by
  ext p
  rw [mem_set, mem_prod]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨_, c.enc_mem_set.2 hq.1, _, d.enc_mem_set.2 hq.2, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨a, ha, rfl⟩ := c.mem_set.1 hu
    obtain ⟨b, hb, rfl⟩ := d.mem_set.1 hv
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-- **Transfer of a product.** -/
theorem pair_mem_star_prod_set {T : Set β} :
    pair x y ∈ F.star ((c.prod d).set (S ×ˢ T)) ↔
      x ∈ F.star (c.set S) ∧ y ∈ F.star (d.set T) := by
  rw [prod_set_prod, F.star_prod (c.isSetOf_set S) (d.isSetOf_set T), pair_mem_prod]

/-- The transform of the product type consists of pairs. -/
theorem exists_pair_of_mem_star_prod_univ {p : ZFSet.{u}}
    (hp : p ∈ F.star ((c.prod d).set Set.univ)) :
    ∃ x ∈ F.star (c.set Set.univ), ∃ y ∈ F.star (d.set Set.univ), p = pair x y := by
  rw [← Set.univ_prod_univ, prod_set_prod,
    F.star_prod (c.isSetOf_set _) (d.isSetOf_set _)] at hp
  exact mem_prod.1 hp

/-- A pair of members of the transformed types is a member of the transformed product
type. -/
theorem pair_mem_star_prod_univ (hx : x ∈ F.star (c.set Set.univ))
    (hy : y ∈ F.star (d.set Set.univ)) : pair x y ∈ F.star ((c.prod d).set Set.univ) := by
  rw [← Set.univ_prod_univ]
  exact (pair_mem_star_prod_set c d).2 ⟨hx, hy⟩

/-- **Transfer of the first projection.** The transform of the first projection of a product
type relates a pair to its first component only. -/
theorem pair_pair_mem_star_fst :
    pair (pair x y) z ∈ F.star (rel (c.prod d) c fun q a => a = q.1) ↔
      x ∈ F.star (c.set Set.univ) ∧ y ∈ F.star (d.set Set.univ) ∧ z = x := by
  set A := c.set Set.univ with hA
  set B := d.set Set.univ with hB
  set G := rel (c.prod d) c fun q a => a = q.1 with hG
  have hAset : IsSetOf F.U A := c.isSetOf_set _
  have hBset : IsSetOf F.U B := d.isSetOf_set _
  have hGset : IsSetOf F.U G := isSetOf_rel _ _ _
  have h := F.transfer
    (.all 0 (.const A) (.all 1 (.const B) (.all 2 (.const A) (.biimp
      (.elem (.opair (.opair (.var 0) (.var 1)) (.var 2)) (.const G))
      (.equal (.var 2) (.var 0))))))
    (by simp [Formula.IsSentence, hAset.1, hBset.1, hGset.1])
  sat_simp at h
  have h' := h.1 (by
    intro u _ hu v _ hv w _ hw
    obtain ⟨a, -, rfl⟩ := c.mem_set.1 hu
    obtain ⟨b, -, rfl⟩ := d.mem_set.1 hv
    obtain ⟨a', -, rfl⟩ := c.mem_set.1 hw
    rw [hG, pair_mem_rel]
    constructor
    · rintro ⟨q, a₂, rfl, h1, h2⟩
      rw [prod_enc] at h1
      rw [h2, (pair_inj.1 h1).1]
    · intro h
      exact ⟨(a, b), a, rfl, rfl, h⟩)
  have hAU := F.star_subset_U' hAset
  have hBU := F.star_subset_U' hBset
  constructor
  · intro hxyz
    obtain ⟨hp, hz⟩ := mem_of_pair_mem_star_rel (c.prod d) c hxyz
    obtain ⟨x', hx', y', hy', hp'⟩ := exists_pair_of_mem_star_prod_univ c d hp
    obtain ⟨rfl, rfl⟩ := pair_inj.1 hp'
    exact ⟨hx', hy', (h' x (hAU hx') hx' y (hBU hy') hy' z (hAU hz) hz).1 hxyz⟩
  · rintro ⟨hx, hy, rfl⟩
    exact (h' z (hAU hx) hx y (hBU hy) hy z (hAU hx) hx).2 rfl

/-- **Transfer of the second projection.** The transform of the second projection of a
product type relates a pair to its second component only. -/
theorem pair_pair_mem_star_snd :
    pair (pair x y) z ∈ F.star (rel (c.prod d) d fun q b => b = q.2) ↔
      x ∈ F.star (c.set Set.univ) ∧ y ∈ F.star (d.set Set.univ) ∧ z = y := by
  set A := c.set Set.univ with hA
  set B := d.set Set.univ with hB
  set G := rel (c.prod d) d fun q b => b = q.2 with hG
  have hAset : IsSetOf F.U A := c.isSetOf_set _
  have hBset : IsSetOf F.U B := d.isSetOf_set _
  have hGset : IsSetOf F.U G := isSetOf_rel _ _ _
  have h := F.transfer
    (.all 0 (.const A) (.all 1 (.const B) (.all 2 (.const B) (.biimp
      (.elem (.opair (.opair (.var 0) (.var 1)) (.var 2)) (.const G))
      (.equal (.var 2) (.var 1))))))
    (by simp [Formula.IsSentence, hAset.1, hBset.1, hGset.1])
  sat_simp at h
  have h' := h.1 (by
    intro u _ hu v _ hv w _ hw
    obtain ⟨a, -, rfl⟩ := c.mem_set.1 hu
    obtain ⟨b, -, rfl⟩ := d.mem_set.1 hv
    obtain ⟨b', -, rfl⟩ := d.mem_set.1 hw
    rw [hG, pair_mem_rel]
    constructor
    · rintro ⟨q, b₂, rfl, h1, h2⟩
      rw [prod_enc] at h1
      rw [h2, (pair_inj.1 h1).2]
    · intro h
      exact ⟨(a, b), b, rfl, rfl, h⟩)
  have hAU := F.star_subset_U' hAset
  have hBU := F.star_subset_U' hBset
  constructor
  · intro hxyz
    obtain ⟨hp, hz⟩ := mem_of_pair_mem_star_rel (c.prod d) d hxyz
    obtain ⟨x', hx', y', hy', hp'⟩ := exists_pair_of_mem_star_prod_univ c d hp
    obtain ⟨rfl, rfl⟩ := pair_inj.1 hp'
    exact ⟨hx', hy', (h' x (hAU hx') hx' y (hBU hy') hy' z (hBU hz) hz).1 hxyz⟩
  · rintro ⟨hx, hy, rfl⟩
    exact (h' x (hAU hx) hx z (hBU hy) hy z (hBU hy) hy).2 rfl

/-- Transfer of the interchange of components: the pair $`(y, x)` is related to $`(x, y)`
by the transform of the relation "the second pair is the first one with its components
interchanged". -/
theorem pair_pair_mem_star_swap (hx : x ∈ F.star (c.set Set.univ))
    (hy : y ∈ F.star (d.set Set.univ)) :
    pair (pair x y) (pair y x) ∈
      F.star (rel (c.prod d) (d.prod c) fun q q' => q' = (q.2, q.1)) := by
  obtain ⟨w, hw⟩ := exists_pair_mem_star_graph (c.prod d) (d.prod c)
    (fun q : α × β => (q.2, q.1)) (pair_mem_star_prod_univ c d hx hy)
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := exists_pair_of_mem_star_prod_univ d c
    (mem_of_pair_mem_star_rel (c.prod d) (d.prod c) hw).2
  have h1 := rel_comp (c.prod d) (d.prod c) d (P := fun q q' => q' = (q.2, q.1))
    (Q := fun q' b => b = q'.1) (R := fun q b => b = q.2)
    (fun q q' b hq hb => by rw [hb, hq]) hw ((pair_pair_mem_star_fst d c).2 ⟨hw₁, hw₂, rfl⟩)
  have h2 := rel_comp (c.prod d) (d.prod c) c (P := fun q q' => q' = (q.2, q.1))
    (Q := fun q' a => a = q'.2) (R := fun q a => a = q.1)
    (fun q q' a hq ha => by rw [ha, hq]) hw ((pair_pair_mem_star_snd d c).2 ⟨hw₁, hw₂, rfl⟩)
  obtain rfl := ((pair_pair_mem_star_snd c d).1 h1).2.2
  obtain rfl := ((pair_pair_mem_star_fst c d).1 h2).2.2
  exact hw

/-!
## Functions between coded types

A function between coded types is represented by its graph. Its transform is a function
between the transformed types, the extension of the original function in the sense of
Section 13.8.
-/

/-- The graph of a function between coded types, as a set of pairs of the universe. -/
def graph (g : α → β) : ZFSet.{u} := rel c d fun a b => b = g a

/-- The graph of a function between coded types is a function between the representing
sets. -/
theorem isFunc_graph (g : α → β) : IsFunc (c.set Set.univ) (d.set Set.univ) (graph c d g) := by
  refine ⟨rel_subset_prod c d _, fun u hu => ?_⟩
  obtain ⟨a, -, rfl⟩ := c.mem_set.1 hu
  refine ⟨d.enc (g a), (pair_mem_rel c d).2 ⟨a, g a, rfl, rfl, rfl⟩, fun w hw => ?_⟩
  obtain ⟨a', b, hb, ha, rfl⟩ := (pair_mem_rel c d).1 hw
  rw [hb, c.enc_injective ha]

/-- The transform of the graph of a function is a function between the transformed
types. -/
theorem isFunc_star_graph (g : α → β) :
    IsFunc (F.star (c.set Set.univ)) (F.star (d.set Set.univ)) (F.star (graph c d g)) :=
  F.isFunc_star (c.isSetOf_set _) (d.isSetOf_set _) (isFunc_graph c d g)

/-- **Section 13.8, extension of a function.** The value at a member of the transformed
domain of the transform of a function between coded types. -/
def ap (g : α → β) (x : ZFSet.{u}) : ZFSet.{u} := app (F.star (graph c d g)) x

variable {g : α → β}

/-- The pair of an argument and the value of the extended function belongs to the
transformed graph. -/
theorem pair_ap_mem (hx : x ∈ F.star (c.set Set.univ)) :
    pair x (ap c d g x) ∈ F.star (graph c d g) := by
  have hf := isFunc_star_graph c d g
  exact hf.isFunction.pair_app_mem (hf.dom_eq.symm ▸ hx)

/-- The value of the extended function is determined by membership in the transformed
graph. -/
theorem ap_eq_of_pair_mem (h : pair x y ∈ F.star (graph c d g)) : ap c d g x = y :=
  (isFunc_star_graph c d g).isFunction.app_eq h

/-- The values of the extended function lie in the transformed codomain. -/
theorem ap_mem (hx : x ∈ F.star (c.set Set.univ)) : ap c d g x ∈ F.star (d.set Set.univ) :=
  (mem_of_pair_mem_star_rel c d (pair_ap_mem c d hx)).2

/-- **Section 13.8.** The extended function agrees with the original one at standard
arguments. -/
@[simp]
theorem ap_enc (a : α) : ap c d g (c.enc a) = d.enc (g a) :=
  ap_eq_of_pair_mem c d ((pair_enc_mem_star_rel c d).2 rfl)

/-!
## Sections of internal relations

An internal relation between pairs and a third entity has an internal section at every
internal second component: the relation between the first component and the third entity.
This is how an internal parameter is fixed without writing a formula.
-/

/-- The pairing map $`x \mapsto (x, y)` on the transform of a coded type, as a set of
pairs. -/
def pairWith (y : ZFSet.{u}) : ZFSet.{u} :=
  relInv (F.star (rel (c.prod d) c fun q a => a = q.1) ∩
    ZFSet.prod (ZFSet.prod (F.star (c.set Set.univ)) {y}) (F.star (c.set Set.univ)))

/-- The members of the pairing map. -/
theorem pair_mem_pairWith {p : ZFSet.{u}} (hy : y ∈ F.star (d.set Set.univ)) :
    pair x p ∈ pairWith c d y ↔ x ∈ F.star (c.set Set.univ) ∧ p = pair x y := by
  rw [pairWith, pair_mem_relInv, mem_inter, pair_mem_prod]
  constructor
  · rintro ⟨h1, h2, hx⟩
    obtain ⟨u, -, v, hv, rfl⟩ := mem_prod.1 h2
    rw [mem_singleton] at hv
    subst hv
    obtain ⟨-, -, rfl⟩ := (pair_pair_mem_star_fst c d).1 h1
    exact ⟨hx, rfl⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨(pair_pair_mem_star_fst c d).2 ⟨hx, hy, rfl⟩,
      pair_mem_prod.2 ⟨hx, mem_singleton.2 rfl⟩, hx⟩

/-- The pairing map with an internal second component is an internal relation. -/
theorem pairWith_spec (hy : y ∈ F.star (d.set Set.univ)) :
    F.Internal (pairWith c d y) ∧ IsSetOf F.U' (pairWith c d y) ∧
      RelIn F.U' (pairWith c d y) := by
  have hA := c.isSetOf_set Set.univ
  have hB := d.isSetOf_set Set.univ
  have hG := isSetOf_rel (c.prod d) c fun q a => a = q.1
  have hGrel := relIn_rel (c.prod d) c fun q a => a = q.1
  have hyint : F.Internal y := F.internal_of_mem_star hB hy
  have hyU : y ∈ F.U' := hyint.mem_U'
  have hsing := F.isUniverse'.isSetOf_singleton hyU
  have hW : F.Internal (F.star (rel (c.prod d) c fun q a => a = q.1) ∩
      ZFSet.prod (ZFSet.prod (F.star (c.set Set.univ)) {y}) (F.star (c.set Set.univ))) :=
    F.internal_inter (F.internal_star hG.1) (F.isSetOf_star hG)
      (F.internal_prod (F.internal_prod (F.internal_star hA.1) (F.isSetOf_star hA)
        (F.internal_singleton hyint) hsing)
        (F.isUniverse'.isSetOf_prod (F.isSetOf_star hA) hsing) (F.internal_star hA.1)
        (F.isSetOf_star hA))
  have hWset : IsSetOf F.U' (F.star (rel (c.prod d) c fun q a => a = q.1) ∩
      ZFSet.prod (ZFSet.prod (F.star (c.set Set.univ)) {y}) (F.star (c.set Set.univ))) :=
    F.isUniverse'.isSetOf_inter (F.isSetOf_star hG)
  have hWrel : RelIn F.U' (F.star (rel (c.prod d) c fun q a => a = q.1) ∩
      ZFSet.prod (ZFSet.prod (F.star (c.set Set.univ)) {y}) (F.star (c.set Set.univ))) :=
    fun p hp => F.relIn_star hG hGrel p (mem_inter.1 hp).1
  refine ⟨F.internal_relInv hW hWset hWrel, F.isUniverse'.isSetOf_relInv hWset hWrel, ?_⟩
  intro p hp
  obtain ⟨u, v, rfl, huv⟩ := mem_relInv.1 hp
  obtain ⟨u', hu', v', hv', huv'⟩ := hWrel _ huv
  obtain ⟨rfl, rfl⟩ := pair_inj.1 huv'
  exact ⟨v, hv', u, hu', rfl⟩

/-- **Sections.** The section at $`y` of a relation $`W` between pairs and entities: the
set of pairs $`(x, z)` with $`((x, y), z) \in W`, for $`x` in the transformed type. -/
def sect (W y : ZFSet.{u}) : ZFSet.{u} := relComp (pairWith c d y) W

/-- The members of a section. -/
theorem pair_mem_sect {W : ZFSet.{u}} (hy : y ∈ F.star (d.set Set.univ)) :
    pair x z ∈ sect c d W y ↔ x ∈ F.star (c.set Set.univ) ∧ pair (pair x y) z ∈ W := by
  rw [sect, pair_mem_relComp]
  constructor
  · rintro ⟨p, hp, hW⟩
    obtain ⟨hx, rfl⟩ := (pair_mem_pairWith c d hy).1 hp
    exact ⟨hx, hW⟩
  · rintro ⟨hx, hW⟩
    exact ⟨_, (pair_mem_pairWith c d hy).2 ⟨hx, rfl⟩, hW⟩

/-- A section of an internal relation at an internal entity is an internal relation. -/
theorem sect_spec {W : ZFSet.{u}} (hW : F.Internal W) (hWset : IsSetOf F.U' W)
    (hWrel : RelIn F.U' W) (hy : y ∈ F.star (d.set Set.univ)) :
    F.Internal (sect c d W y) ∧ IsSetOf F.U' (sect c d W y) ∧ RelIn F.U' (sect c d W y) := by
  obtain ⟨h1, h2, h3⟩ := pairWith_spec c d hy
  refine ⟨F.internal_relComp h1 h2 h3 hW hWset hWrel,
    F.isUniverse'.isSetOf_relComp h2 h3 hWset hWrel, fun p hp => ?_⟩
  obtain ⟨u, v, w, rfl, huv, hvw⟩ := mem_relComp.1 hp
  obtain ⟨u', hu', _, _, h⟩ := h3 _ huv
  obtain ⟨_, _, w', hw', h'⟩ := hWrel _ hvw
  rw [(pair_inj.1 h).1, (pair_inj.1 h').2]
  exact ⟨u', hu', w', hw', rfl⟩

end Code

/-!
## Internal sets from standard relations

The transform of a binary relation of the standard universe is an internal relation of the
nonstandard one, so images and inverse images of internal sets under it are internal. With
the Boolean closure properties of Chapter 13 this produces, without writing formulas, the
internal sets to which the permanence principles are applied.
-/

variable {F}
variable {Q A D : ZFSet.{u}}

/-- The transform of a binary relation of the universe is an internal set of pairs. -/
theorem star_rel_spec (hQ : IsSetOf F.U Q) (hrel : RelIn F.U Q) :
    F.Internal (F.star Q) ∧ IsSetOf F.U' (F.star Q) ∧ RelIn F.U' (F.star Q) :=
  ⟨F.internal_star hQ.1, F.isSetOf_star hQ, F.relIn_star hQ hrel⟩

/-- The image of an internal set under the transform of a standard relation is internal. -/
theorem internal_relImage_star (hQ : IsSetOf F.U Q) (hrel : RelIn F.U Q) (hD : F.Internal D) :
    F.Internal (relImage (F.star Q) D) :=
  F.internal_relImage (F.internal_star hQ.1) (F.isSetOf_star hQ) (F.relIn_star hQ hrel) hD

/-- The inverse image of an internal set under the transform of a standard relation is
internal. -/
theorem internal_relPreimage_star (hQ : IsSetOf F.U Q) (hrel : RelIn F.U Q)
    (hD : F.Internal D) : F.Internal (relPreimage (F.star Q) D) :=
  F.internal_relPreimage (F.internal_star hQ.1) (F.isSetOf_star hQ) (F.relIn_star hQ hrel) hD

/-- A subset of a transformed set that belongs to the nonstandard universe is a set of that
universe. -/
theorem isSetOf_of_subset_star (hA : IsSetOf F.U A) (hD : D ⊆ F.star A) : IsSetOf F.U' D :=
  F.isUniverse'.isSetOf_of_subset (F.isSetOf_star hA) hD

end NonstandardFramework

end Goldblatt
