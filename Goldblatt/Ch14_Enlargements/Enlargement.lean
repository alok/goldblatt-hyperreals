import Goldblatt.Ch13_Universes

/-!
# 14 (part 1). Enlargements and Concurrence: Sections 14.1 and 14.2

This is the first of five parts of Chapter 14 (the overview is on the chapter page
{lit}`Goldblatt.Ch14_Enlargements`). It works with an arbitrary nonstandard framework in the
sense of Chapter 13 and studies one additional property, being an _enlargement_. Nothing here
depends on how a framework is built; that enlargements exist is proved in the other four
parts.
-/

noncomputable section

namespace Goldblatt

open ZFSet
open scoped Classical

universe u

/-!
## 14.1 Enlargements

A transfer map need not produce anything new: the identity map of a universe is a framework
in which every entity is standard. Chapter 13 therefore carried the existence of a nonstandard
hypernatural number as a hypothesis. This section introduces a single principle from which
nonstandard entities of every kind are obtained. A framework is an enlargement when every
collection of sets in the standard universe that has the finite intersection property acquires
a common element after transfer: some entity of the target universe belongs to the transform
of every member of the collection.

The examples of the section apply the principle to particular collections. Shrinking
intervals $`(0, r)` give a positive infinitesimal, the rays $`(r, \infty)` give an unlimited
hyperreal, and the sets $`A - \{a\}` for an infinite set $`A` give a member of $`{}^*A` that
is not standard. The fourth example, a hyperfinite set between the image of $`A` and
$`{}^*A`, is the implication from (1) to (3) of Theorem 14.2.1 and is recorded after that
theorem as {lit}`NonstandardFramework.IsEnlargement.exists_hyperfinite`. The existence
statement announced at the end of the section, the enlargement theorem, is
{lit}`exists_enlargement` in part 5.
-/

/-- **Section 14.1, finite intersection property.** A collection $`\mathcal A` of sets has
the finite intersection property when every finite subcollection has a common member: for
every finite set $`s` of members of $`\mathcal A` there is a $`y` belonging to all members of
$`s`. Finite subcollections are given as terms of {lit}`Finset`; for the empty subcollection the
condition is vacuous. -/
def FIP (A : ZFSet.{u}) : Prop :=
  ∀ s : Finset ZFSet.{u}, (∀ B ∈ s, B ∈ A) → ∃ y, ∀ B ∈ s, y ∈ B

/-- The set whose members are the members of a finite collection of sets. -/
def ofFinset (s : Finset ZFSet.{u}) : ZFSet.{u} := ZFSet.range fun x : s => x.1

/-- The members of {lit}`ofFinset s` are the members of $`s`. -/
@[simp]
theorem mem_ofFinset {s : Finset ZFSet.{u}} {x : ZFSet.{u}} : x ∈ ofFinset s ↔ x ∈ s := by
  simp [ofFinset]

/-- The set made from a finite collection is finite. -/
theorem finite_ofFinset (s : Finset ZFSet.{u}) : (ofFinset s : Set ZFSet.{u}).Finite := by
  have : (ofFinset s : Set ZFSet.{u}) = ↑s := by
    ext x
    simp
  rw [this]
  exact s.finite_toSet

/-- A singleton is a finite set. -/
theorem finite_coe_singleton (a : ZFSet.{u}) : (({a} : ZFSet.{u}) : Set ZFSet.{u}).Finite :=
  (Set.finite_singleton a).subset fun _ hx => mem_singleton.1 hx

namespace NonstandardFramework

open Formula Term

variable (F : NonstandardFramework.{u}) {A B R : ZFSet.{u}}

/-- **Section 14.1, enlargements.** A nonstandard framework is an enlargement
when for every collection $`\mathcal A \in \mathbb U` of sets with the finite intersection
property there is an entity $`b \in \mathbb U'` that belongs to $`{}^*B` for every
$`B \in \mathcal A`:
$$`b \in \bigcap \{{}^*B : B \in \mathcal A\}.`
The book calls $`\mathbb U'` an enlargement of $`\mathbb U` when some universe embedding has
this property; here the property is attached to the framework, which carries the embedding. -/
def IsEnlargement : Prop :=
  ∀ A, IsSetOf F.U A → (∀ B ∈ A, IsSetOf F.U B) → FIP A → ∃ b ∈ F.U', ∀ B ∈ A, b ∈ F.star B

variable {F}

/-- **Section 14.1, third example.** In an enlargement,
if $`A \in \mathbb U` is an infinite set then $`{}^*A` has a member distinct from $`{}^*a` for
every $`a \in A`: the sets $`A - \{a\}` have the finite intersection property and
$`{}^*(A - \{a\}) = {}^*A - \{{}^*a\}`. -/
theorem IsEnlargement.exists_mem_star_notMem_im (hE : F.IsEnlargement) (hA : IsSetOf F.U A)
    (hinf : (A : Set ZFSet.{u}).Infinite) : ∃ b ∈ F.star A, b ∉ F.im A := by
  set 𝒜 : ZFSet.{u} := ZFSet.range fun a : ↥A => A \ {a.1} with h𝒜def
  have hsets : ∀ B ∈ 𝒜, IsSetOf F.U B := fun B hB => by
    obtain ⟨a, rfl⟩ := mem_range.1 hB
    exact F.hU.isSetOf_sdiff hA
  have h𝒜 : IsSetOf F.U 𝒜 := F.hU.isSetOf_of_subset (F.hU.isSetOf_powerset hA) fun B hB => by
    obtain ⟨a, rfl⟩ := mem_range.1 hB
    exact mem_powerset.2 fun x hx => (mem_sdiff.1 hx).1
  have hfip : FIP 𝒜 := fun s hs => by
    choose x hx using fun B : {B // B ∈ 𝒜} => mem_range.1 B.2
    let g : {B // B ∈ s} → ZFSet.{u} := fun B => (x ⟨B.1, hs B.1 B.2⟩).1
    obtain ⟨y, hyA, hy⟩ := hinf.exists_notMem_finset (s.attach.image g)
    refine ⟨y, fun B hB => ?_⟩
    have e := hx ⟨B, hs B hB⟩
    simp only at e
    rw [← e, mem_sdiff, mem_singleton]
    exact ⟨hyA, fun h => hy (Finset.mem_image.2 ⟨⟨B, hB⟩, Finset.mem_attach _ _, h.symm⟩)⟩
  obtain ⟨b, -, hbm⟩ := hE 𝒜 h𝒜 hsets hfip
  have key : ∀ a ∈ A, b ∈ F.star A ∧ b ≠ F.star a := fun a ha => by
    have haU := F.hU.subset hA ha
    have h := hbm (A \ {a}) (mem_range.2 ⟨⟨a, ha⟩, rfl⟩)
    rw [F.star_sdiff hA (F.hU.isSetOf_singleton haU), F.star_singleton haU, mem_sdiff,
      mem_singleton] at h
    exact h
  obtain ⟨a0, ha0⟩ := hinf.nonempty
  refine ⟨b, (key a0 ha0).1, fun hb => ?_⟩
  obtain ⟨a, ha, rfl⟩ := F.mem_im.1 hb
  exact (key a ha).2 rfl

/-- **Section 14.1, third example.** In an
enlargement every infinite standard set has a nonstandard member. -/
theorem IsEnlargement.exists_nonstandard_mem_star (hE : F.IsEnlargement) (hA : IsSetOf F.U A)
    (hinf : (A : Set ZFSet.{u}).Infinite) : ∃ b ∈ F.star A, F.Nonstandard b := by
  obtain ⟨b, hb, hbim⟩ := hE.exists_mem_star_notMem_im hA hinf
  exact ⟨b, hb, F.star_subset_U' hA hb, fun hs => hbim ((F.mem_im_iff hA).2 ⟨hb, hs⟩)⟩

/-- **Section 14.1, third example.** In an enlargement an infinite
set $`A` of individuals, for instance $`\mathbb N`, $`\mathbb Z` or $`\mathbb Q` when the real
numbers are individuals, is a proper subset of $`{}^*A`. -/
theorem IsEnlargement.ssubset_star (hE : F.IsEnlargement) (hAX : A ⊆ F.X)
    (hinf : (A : Set ZFSet.{u}).Infinite) : A ⊆ F.star A ∧ ∃ b ∈ F.star A, b ∉ A := by
  have hA := F.hU.isSetOf_of_subset F.isUniverseOver.base_isSetOf hAX
  obtain ⟨b, hb, hbim⟩ := hE.exists_mem_star_notMem_im hA hinf
  rw [F.im_eq_of_subset_base hAX] at hbim
  exact ⟨(F.subset_star_of_subset_base hAX).1, b, hb, hbim⟩

/-- **Chapter 14, introduction.** The identity map of a universe that has an infinite set is
a framework but not an enlargement: it has no nonstandard entities. So the enlargement
property is a real restriction. -/
theorem not_isEnlargement_trivial {U X : ZFSet.{u}} (h : IsUniverseOver U X) (hA : IsSetOf U A)
    (hinf : (A : Set ZFSet.{u}).Infinite) : ¬ (NonstandardFramework.trivial h).IsEnlargement :=
  fun hE => by
    obtain ⟨b, hb, hbim⟩ := hE.exists_mem_star_notMem_im (F := NonstandardFramework.trivial h)
      hA hinf
    exact hbim ((NonstandardFramework.trivial h).mem_im.2 ⟨b, hb, rfl⟩)

end NonstandardFramework

namespace RealFramework

variable (F : RealFramework.{u})

/-- The set of natural numbers of a real framework is infinite. -/
theorem infinite_N : (F.N : Set ZFSet.{u}).Infinite := by
  have : (F.N : Set ZFSet.{u}) = Set.range F.nat := by
    ext x
    simp [N]
  rw [this]
  exact Set.infinite_range_of_injective F.nat_injective

variable {F}

/-- **Section 14.1, third example for $`\mathbb N`.** In an enlargement
over the real numbers there is a nonstandard hypernatural number. This is the hypothesis under
which Chapter 13 proves its results on external sets, so in an enlargement all of them hold. -/
theorem exists_nonstandard_nat (hE : F.IsEnlargement) : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N := by
  obtain ⟨b, hb, hbim⟩ := hE.exists_mem_star_notMem_im F.isSetOf_N F.infinite_N
  rw [F.im_N_im_R.1] at hbim
  exact ⟨b, hb, hbim⟩

/-- A family of sets indexed by the positive reals has the finite intersection property as
soon as some point $`w(m)` lies in every member whose index is at least $`m`, for each
positive $`m`: finitely many indices have a positive lower bound. -/
theorem fip_range_of_pos {S : {r : ℝ // 0 < r} → ZFSet.{u}} (w : ℝ → ZFSet.{u})
    (hw : ∀ m : ℝ, 0 < m → ∀ r : {r : ℝ // 0 < r}, m ≤ r.1 → w m ∈ S r) :
    FIP (ZFSet.range S) := fun s hs => by
  choose r hr using fun B : {B // B ∈ ZFSet.range S} => mem_range.1 B.2
  let g : {B // B ∈ s} → ℝ := fun B => (r ⟨B.1, hs B.1 B.2⟩).1
  have hne : (insert 1 (s.attach.image g)).Nonempty := Finset.insert_nonempty _ _
  set m := (insert 1 (s.attach.image g)).min' hne with hm
  have hmpos : 0 < m := by
    rw [hm, Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨B, -, rfl⟩ := Finset.mem_image.1 hy
      exact (r _).2
  refine ⟨w m, fun B hB => ?_⟩
  have hle : m ≤ g ⟨B, hB⟩ := Finset.min'_le _ _
    (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨B, hB⟩, Finset.mem_attach _ _, rfl⟩))
  have e := hr ⟨B, hs B hB⟩
  simp only at e
  rw [← e]
  exact hw m hmpos _ hle

variable (F) in
/-- **Section 14.1, first example: the collection.** The set of all real intervals $`(0, r)`
with $`r` a positive real number. -/
def posIntervals : ZFSet.{u} :=
  ZFSet.range fun r : {r : ℝ // 0 < r} => ooIn F.R F.Le (F.real 0) (F.real r.1)

variable (F) in
/-- **Section 14.1, first example.** The collection of the intervals $`(0, r)` is a set of sets
of the universe. -/
theorem isSetOf_posIntervals :
    IsSetOf F.U F.posIntervals ∧ ∀ B ∈ F.posIntervals, IsSetOf F.U B :=
  ⟨F.hU.isSetOf_of_subset (F.hU.isSetOf_powerset F.isSetOf_R) fun B hB => by
      obtain ⟨r, rfl⟩ := mem_range.1 hB
      exact mem_powerset.2 sep_subset,
    fun B hB => by
      obtain ⟨r, rfl⟩ := mem_range.1 hB
      exact F.hU.isSetOf_sep F.isSetOf_R _⟩

variable (F) in
/-- **Section 14.1, first example.** The intervals $`(0, r)` have the finite intersection
property: finitely many of them all contain $`m/2`, where $`m` is the least of their right
end points. -/
theorem fip_posIntervals : FIP F.posIntervals :=
  fip_range_of_pos (fun m => F.real (m / 2)) fun m hm r hr => by
    rw [ooIn, mem_sep]
    refine ⟨F.mem_R.2 ⟨_, rfl⟩, ⟨F.pair_mem_Le.2 (by linarith), fun h => ?_⟩,
      ⟨F.pair_mem_Le.2 (by linarith), fun h => ?_⟩⟩
    · have := F.real_injective h
      linarith
    · have := F.real_injective h
      linarith

variable (F) in
/-- **Section 14.1, first example: the intersection.** The common members of the transforms
$`{}^*(0, r)`, $`r` a positive real, are exactly the positive infinitesimals: the hyperreals
$`b` with $`0 < b < r` for every positive real $`r`. This holds in every framework; what an
enlargement adds is that the intersection is nonempty. Strict order is written with $`\le` and
$`\ne`, as in Chapter 13. -/
theorem forall_mem_star_posIntervals_iff {b : ZFSet.{u}} :
    (∀ B ∈ F.posIntervals, b ∈ F.star B) ↔
      b ∈ F.star F.R ∧ ∀ r : ℝ, 0 < r →
        (pair (F.real 0) b ∈ F.star F.Le ∧ b ≠ F.real 0) ∧
          (pair b (F.real r) ∈ F.star F.Le ∧ b ≠ F.real r) := by
  constructor
  · intro h
    have key : ∀ r : ℝ, 0 < r → b ∈ ooIn (F.star F.R) (F.star F.Le) (F.real 0) (F.real r) :=
      fun r hr => by
        rw [← F.star_ooIn]
        exact h _ (mem_range.2 ⟨⟨r, hr⟩, rfl⟩)
    exact ⟨(mem_sep.1 (key 1 one_pos)).1, fun r hr => (mem_sep.1 (key r hr)).2⟩
  · rintro ⟨hb, h⟩ B hB
    obtain ⟨r, rfl⟩ := mem_range.1 hB
    rw [F.star_ooIn, ooIn, mem_sep]
    exact ⟨hb, h r.1 r.2⟩

/-- **Section 14.1, first example.** In an enlargement over the real
numbers there is a positive infinitesimal: a hyperreal $`b` with $`0 < b < r` for every positive
real $`r`. It is a common member of all the sets $`{}^*(0, r)`, which exists because the
intervals $`(0, r)` have the finite intersection property. -/
theorem exists_pos_infinitesimal (hE : F.IsEnlargement) :
    ∃ b ∈ F.star F.R, ∀ r : ℝ, 0 < r →
      (pair (F.real 0) b ∈ F.star F.Le ∧ b ≠ F.real 0) ∧
        (pair b (F.real r) ∈ F.star F.Le ∧ b ≠ F.real r) := by
  obtain ⟨b, -, hb⟩ := hE _ F.isSetOf_posIntervals.1 F.isSetOf_posIntervals.2 F.fip_posIntervals
  obtain ⟨h1, h2⟩ := F.forall_mem_star_posIntervals_iff.1 hb
  exact ⟨b, h1, h2⟩

variable (F) in
/-- **Section 14.1, first example, the variant: the collection.** The set of all punctured
intervals $`(-r, r) - \{0\}` with $`r` a positive real number. -/
def puncturedIntervals : ZFSet.{u} :=
  ZFSet.range fun r : {r : ℝ // 0 < r} =>
    ooIn F.R F.Le (F.real (-r.1)) (F.real r.1) \ {F.real 0}

variable (F) in
/-- **Section 14.1, first example, the variant.** The collection of the punctured intervals is
a set of sets of the universe. -/
theorem isSetOf_puncturedIntervals :
    IsSetOf F.U F.puncturedIntervals ∧ ∀ B ∈ F.puncturedIntervals, IsSetOf F.U B :=
  ⟨F.hU.isSetOf_of_subset (F.hU.isSetOf_powerset F.isSetOf_R) fun B hB => by
      obtain ⟨r, rfl⟩ := mem_range.1 hB
      exact mem_powerset.2 fun x hx => (mem_sep.1 (mem_sdiff.1 hx).1).1,
    fun B hB => by
      obtain ⟨r, rfl⟩ := mem_range.1 hB
      exact F.hU.isSetOf_sdiff (F.hU.isSetOf_sep F.isSetOf_R _)⟩

variable (F) in
/-- **Section 14.1, first example, the variant.** The punctured intervals
$`(-r, r) - \{0\}` have the finite intersection property. -/
theorem fip_puncturedIntervals : FIP F.puncturedIntervals :=
  fip_range_of_pos (fun m => F.real (m / 2)) fun m hm r hr => by
    rw [mem_sdiff, mem_singleton, ooIn, mem_sep]
    refine ⟨⟨F.mem_R.2 ⟨_, rfl⟩, ⟨F.pair_mem_Le.2 (by linarith), fun h => ?_⟩,
      ⟨F.pair_mem_Le.2 (by linarith), fun h => ?_⟩⟩, fun h => ?_⟩
    · have := F.real_injective h
      linarith
    · have := F.real_injective h
      linarith
    · have := F.real_injective h
      linarith

variable (F) in
/-- **Section 14.1, first example, the variant: the intersection.** The common members of the
transforms $`{}^*((-r, r) - \{0\})`, $`r` a positive real, are exactly the nonzero
infinitesimals: the hyperreals $`b \ne 0` with $`-r < b < r` for every positive real $`r`. -/
theorem forall_mem_star_puncturedIntervals_iff {b : ZFSet.{u}} :
    (∀ B ∈ F.puncturedIntervals, b ∈ F.star B) ↔
      b ∈ F.star F.R ∧ b ≠ F.real 0 ∧ ∀ r : ℝ, 0 < r →
        (pair (F.real (-r)) b ∈ F.star F.Le ∧ b ≠ F.real (-r)) ∧
          (pair b (F.real r) ∈ F.star F.Le ∧ b ≠ F.real r) := by
  have hstar : ∀ r : ℝ, F.star (ooIn F.R F.Le (F.real (-r)) (F.real r) \ {F.real 0}) =
      ooIn (F.star F.R) (F.star F.Le) (F.real (-r)) (F.real r) \ {F.real 0} := fun r => by
    rw [F.star_sdiff (show IsSetOf F.U (ooIn F.R F.Le (F.real (-r)) (F.real r)) from
        F.hU.isSetOf_sep F.isSetOf_R _) (F.hU.isSetOf_singleton (F.real_mem_U 0)),
      F.star_singleton (F.real_mem_U 0), F.star_real, F.star_ooIn]
  constructor
  · intro h
    have key : ∀ r : ℝ, 0 < r →
        b ∈ ooIn (F.star F.R) (F.star F.Le) (F.real (-r)) (F.real r) ∧ b ≠ F.real 0 :=
      fun r hr => by
        have := h _ (mem_range.2 ⟨⟨r, hr⟩, rfl⟩)
        rwa [hstar, mem_sdiff, mem_singleton] at this
    exact ⟨(mem_sep.1 (key 1 one_pos).1).1, (key 1 one_pos).2,
      fun r hr => (mem_sep.1 (key r hr).1).2⟩
  · rintro ⟨hb, h0, h⟩ B hB
    obtain ⟨r, rfl⟩ := mem_range.1 hB
    rw [hstar, mem_sdiff, mem_singleton, ooIn, mem_sep]
    exact ⟨⟨hb, h r.1 r.2⟩, h0⟩

/-- **Section 14.1, first example, the variant.** In an enlargement over the real numbers
there is a nonzero infinitesimal, obtained as a common member of the transforms of the
punctured intervals $`(-r, r) - \{0\}`. -/
theorem exists_nonzero_infinitesimal (hE : F.IsEnlargement) :
    ∃ b ∈ F.star F.R, b ≠ F.real 0 ∧ ∀ r : ℝ, 0 < r →
      (pair (F.real (-r)) b ∈ F.star F.Le ∧ b ≠ F.real (-r)) ∧
        (pair b (F.real r) ∈ F.star F.Le ∧ b ≠ F.real r) := by
  obtain ⟨b, -, hb⟩ := hE _ F.isSetOf_puncturedIntervals.1 F.isSetOf_puncturedIntervals.2
    F.fip_puncturedIntervals
  obtain ⟨h1, h2⟩ := F.forall_mem_star_puncturedIntervals_iff.1 hb
  exact ⟨b, h1, h2⟩

/-- **Section 14.1, second example.** In an enlargement over the real
numbers there is a positive unlimited hyperreal: a $`b \in {}^*\mathbb R` with $`r < b` for
every real $`r`. It is a member of all the sets $`{}^*(r, \infty)`. -/
theorem exists_pos_unlimited (hE : F.IsEnlargement) :
    ∃ b ∈ F.star F.R, ∀ r : ℝ, pair (F.real r) b ∈ F.star F.Le ∧ b ≠ F.real r := by
  set 𝒜 : ZFSet.{u} := ZFSet.range fun r : ℝ => F.upperRay r with h𝒜def
  have hsets : ∀ B ∈ 𝒜, IsSetOf F.U B := fun B hB => by
    obtain ⟨r, rfl⟩ := mem_range.1 hB
    exact F.hU.isSetOf_sep F.isSetOf_R _
  have h𝒜 : IsSetOf F.U 𝒜 :=
    F.hU.isSetOf_of_subset (F.hU.isSetOf_powerset F.isSetOf_R) fun B hB => by
      obtain ⟨r, rfl⟩ := mem_range.1 hB
      exact mem_powerset.2 sep_subset
  have hfip : FIP 𝒜 := fun s hs => by
    choose r hr using fun B : {B // B ∈ 𝒜} => mem_range.1 B.2
    let g : {B // B ∈ s} → ℝ := fun B => r ⟨B.1, hs B.1 B.2⟩
    have hne : (insert 0 (s.attach.image g)).Nonempty := Finset.insert_nonempty _ _
    set m := (insert 0 (s.attach.image g)).max' hne with hm
    refine ⟨F.real (m + 1), fun B hB => ?_⟩
    have hle : g ⟨B, hB⟩ ≤ m := Finset.le_max' _ _
      (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨B, hB⟩, Finset.mem_attach _ _, rfl⟩))
    have e := hr ⟨B, hs B hB⟩
    simp only at e
    simp only [g] at hle
    rw [← e, upperRay, mem_sep]
    refine ⟨F.mem_R.2 ⟨_, rfl⟩, F.pair_mem_Le.2 (by linarith), fun h => ?_⟩
    have := F.real_injective h
    linarith
  obtain ⟨b, -, hb⟩ := hE 𝒜 h𝒜 hsets hfip
  have key : ∀ r : ℝ, b ∈ (F.star F.R).sep fun x =>
      pair (F.real r) x ∈ F.star F.Le ∧ x ≠ F.real r := fun r => by
    rw [← F.star_upperRay]
    exact hb _ (mem_range.2 ⟨r, rfl⟩)
  exact ⟨b, (mem_sep.1 (key 0)).1, fun r => (mem_sep.1 (key r)).2⟩

end RealFramework

/-!
## 14.2 Concurrence and Hyperfinite Approximation

The enlargement property can be restated in terms of relations. A relation is concurrent when
any finitely many members of its domain are related to a common element; in an enlargement
the transform of a concurrent relation then has an element related to the transforms of all
members of the domain at once. The examples of Section 14.1 are instances: the order on the
positive reals in either direction, the nonidentity relation on an infinite set, and the
membership relation between a set and its finite subsets. Each is formalized below: the
relation is shown to be concurrent, its transform is computed, and a bound of the transformed
relation is shown to be a nonstandard entity of the expected kind.

Theorem 14.2.1 says that three properties of a framework are equivalent: being an
enlargement, having bounds for concurrent relations, and hyperfinite approximation, the
existence for every standard set $`A` of a hyperfinite set containing all standard members of
$`{}^*A`. The three implications are proved separately and then assembled.
-/

/-- **Section 14.2, concurrent relations.** Concurrence, also called finite
satisfiability, of a binary relation $`R`: every finite set $`s` of members of the domain of
$`R` has a common partner, an entity $`y` with $`(x, y) \in R` for each $`x \in s`. As for
the finite intersection property, finite sets are terms of {lit}`Finset`. -/
def Concurrent (R : ZFSet.{u}) : Prop :=
  ∀ s : Finset ZFSet.{u}, (∀ x ∈ s, x ∈ dom R) → ∃ y, ∀ x ∈ s, pair x y ∈ R

/-- **Section 14.2, the membership relation.** The relation
$`\{(a, Z) : a \in Z \in \mathcal P_F(A)\}` between a set $`A` and its finite subsets. -/
def memRel (A : ZFSet.{u}) : ZFSet.{u} :=
  (prod A (finPow A)).sep fun p => ∃ a Z, p = pair a Z ∧ a ∈ Z

/-- A pair $`(a, Z)` belongs to the membership relation of $`A` exactly when
$`Z` is a finite subset of $`A` and $`a \in Z`. -/
theorem pair_mem_memRel {A a Z : ZFSet.{u}} :
    pair a Z ∈ memRel A ↔ a ∈ A ∧ Z ∈ finPow A ∧ a ∈ Z := by
  rw [memRel, mem_sep, pair_mem_prod]
  constructor
  · rintro ⟨⟨h1, h2⟩, a', Z', e, h3⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.1 e
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, a, Z, rfl, h3⟩

/-- The domain of the membership relation of $`A` is $`A`, because every $`a \in A`
belongs to the finite set $`\{a\}`. -/
theorem dom_memRel (A : ZFSet.{u}) : dom (memRel A) = A := by
  ext a
  constructor
  · intro h
    obtain ⟨Z, hZ⟩ := mem_dom.1 h
    exact (pair_mem_memRel.1 hZ).1
  · intro h
    exact mem_dom.2 ⟨{a}, pair_mem_memRel.2 ⟨h, mem_finPow.2 ⟨fun x hx => by
      rwa [mem_singleton.1 hx], finite_coe_singleton a⟩, mem_singleton.2 rfl⟩⟩

/-- **Section 14.2, fourth example.** For every set $`A` the membership
relation between $`A` and $`\mathcal P_F(A)` is concurrent: finitely many members
$`a_1, \dots, a_n` of $`A` all belong to the finite set $`\{a_1, \dots, a_n\}`. -/
theorem concurrent_memRel (A : ZFSet.{u}) : Concurrent (memRel A) := fun s hs => by
  rw [dom_memRel] at hs
  exact ⟨ofFinset s, fun x hx => pair_mem_memRel.2 ⟨hs x hx, mem_finPow.2
    ⟨fun y hy => hs y (mem_ofFinset.1 hy), finite_ofFinset s⟩, mem_ofFinset.2 hx⟩⟩

/-- **Section 14.2, the nonidentity relation.** The relation
$`\{(a, y) \in A \times A : a \ne y\}` on a set $`A`. -/
def neRel (A : ZFSet.{u}) : ZFSet.{u} :=
  (prod A A).sep fun p => ∃ a y, p = pair a y ∧ a ≠ y

/-- A pair $`(a, y)` belongs to the nonidentity relation of $`A` exactly when
$`a` and $`y` are distinct members of $`A`. -/
theorem pair_mem_neRel {A a y : ZFSet.{u}} : pair a y ∈ neRel A ↔ a ∈ A ∧ y ∈ A ∧ a ≠ y := by
  rw [neRel, mem_sep, pair_mem_prod]
  constructor
  · rintro ⟨⟨h1, h2⟩, a', y', e, h3⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.1 e
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, a, y, rfl, h3⟩

/-- **Section 14.2, third example.** The nonidentity relation on $`A` is
concurrent precisely when $`A` is infinite. The book states this without restriction; it needs
$`A` to have at least two members, since for a set with at most one member the relation is
empty and so vacuously concurrent. That hypothesis is added here. -/
theorem concurrent_neRel_iff {A : ZFSet.{u}} (h2 : ∃ a ∈ A, ∃ b ∈ A, a ≠ b) :
    Concurrent (neRel A) ↔ (A : Set ZFSet.{u}).Infinite := by
  obtain ⟨a0, ha0, b0, hb0, hab⟩ := h2
  have hdom : ∀ {a : ZFSet.{u}}, a ∈ dom (neRel A) ↔ a ∈ A := by
    intro a
    constructor
    · intro h
      obtain ⟨y, hy⟩ := mem_dom.1 h
      exact (pair_mem_neRel.1 hy).1
    · intro h
      by_cases ha : a = a0
      · exact mem_dom.2 ⟨b0, pair_mem_neRel.2 ⟨h, hb0, ha ▸ hab⟩⟩
      · exact mem_dom.2 ⟨a0, pair_mem_neRel.2 ⟨h, ha0, ha⟩⟩
  constructor
  · intro hc hfin
    obtain ⟨y, hy⟩ := hc (Set.Finite.toFinset hfin) fun x hx =>
      hdom.2 ((Set.Finite.mem_toFinset hfin).1 hx)
    have hyA : y ∈ A := (pair_mem_neRel.1 (hy a0 ((Set.Finite.mem_toFinset hfin).2 ha0))).2.1
    exact (pair_mem_neRel.1 (hy y ((Set.Finite.mem_toFinset hfin).2 hyA))).2.2 rfl
  · intro hinf s hs
    obtain ⟨y, hyA, hy⟩ := hinf.exists_notMem_finset s
    exact ⟨y, fun x hx => pair_mem_neRel.2 ⟨hdom.1 (hs x hx), hyA, fun h => hy (h ▸ hx)⟩⟩

/-- If $`A` has two distinct members, the domain of its nonidentity relation is $`A`. -/
theorem dom_neRel {A : ZFSet.{u}} (h2 : ∃ a ∈ A, ∃ b ∈ A, a ≠ b) : dom (neRel A) = A := by
  obtain ⟨a0, ha0, b0, hb0, hab⟩ := h2
  ext a
  constructor
  · intro h
    obtain ⟨y, hy⟩ := mem_dom.1 h
    exact (pair_mem_neRel.1 hy).1
  · intro h
    by_cases ha : a = a0
    · exact mem_dom.2 ⟨b0, pair_mem_neRel.2 ⟨h, hb0, ha ▸ hab⟩⟩
    · exact mem_dom.2 ⟨a0, pair_mem_neRel.2 ⟨h, ha0, ha⟩⟩

namespace NonstandardFramework

open Formula Term

variable (F : NonstandardFramework.{u}) {A : ZFSet.{u}}

/-- **Section 14.2, third example.** The transform of the nonidentity relation on a set
$`A \in \mathbb U` is the nonidentity relation on $`{}^*A`, by transfer of
$`(\forall x, y \in A)\,((x, y) \in R \leftrightarrow x \ne y)`. -/
theorem pair_mem_star_neRel (hA : IsSetOf F.U A) {x y : ZFSet.{u}} :
    pair x y ∈ F.star (neRel A) ↔ x ∈ F.star A ∧ y ∈ F.star A ∧ x ≠ y := by
  have hsub : neRel A ⊆ prod A A := sep_subset
  have hR := F.hU.isSetOf_of_subset_prod hA hA hsub
  have ht := F.transfer
    (.all 0 (.const A) (.all 1 (.const A)
      (.biimp (.elem (.opair (.var 0) (.var 1)) (.const (neRel A)))
        (.neg (.equal (.var 0) (.var 1))))))
    (by simp [IsSentence, hA.1, hR.1])
  sat_simp at ht
  have key := ht.1 fun a _ ha y _ hy =>
    ⟨fun h => (pair_mem_neRel.1 h).2.2, fun h => pair_mem_neRel.2 ⟨ha, hy, h⟩⟩
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := pair_mem_prod.1 (F.star_subset_prod hA hA hsub h)
    exact ⟨hx, hy, (key x (F.star_subset_U' hA hx) hx y (F.star_subset_U' hA hy) hy).1 h⟩
  · rintro ⟨hx, hy, h⟩
    exact (key x (F.star_subset_U' hA hx) hx y (F.star_subset_U' hA hy) hy).2 h

variable {F} in
/-- **Section 14.2, third example.** A bound of the transformed nonidentity relation on a set
$`A \in \mathbb U`, that is, an entity $`b` with $`{}^*a \mathrel{{}^*R} b` for all $`a` in the
domain, lies in $`{}^*A`, differs from $`{}^*a` for every $`a \in A`, and so is a nonstandard
member of $`{}^*A`. As in {lit}`concurrent_neRel_iff`, $`A` is assumed to have two distinct
members, so that the domain of the relation is all of $`A`. -/
theorem mem_star_notMem_im_of_bound_neRel (hA : IsSetOf F.U A) (h2 : ∃ a ∈ A, ∃ b ∈ A, a ≠ b)
    {b : ZFSet.{u}} (hb : ∀ x ∈ dom (neRel A), pair (F.star x) b ∈ F.star (neRel A)) :
    b ∈ F.star A ∧ b ∉ F.im A ∧ F.Nonstandard b := by
  rw [dom_neRel h2] at hb
  obtain ⟨a0, ha0, -⟩ := h2
  have hbA : b ∈ F.star A := ((F.pair_mem_star_neRel hA).1 (hb a0 ha0)).2.1
  have hbim : b ∉ F.im A := fun h => by
    obtain ⟨a, ha, rfl⟩ := F.mem_im.1 h
    exact ((F.pair_mem_star_neRel hA).1 (hb a ha)).2.2 rfl
  exact ⟨hbA, hbim, F.star_subset_U' hA hbA, fun hs => hbim ((F.mem_im_iff hA).2 ⟨hbA, hs⟩)⟩

end NonstandardFramework

namespace RealFramework

open Formula Term

variable (F : RealFramework.{u})

/-- A real number belongs to the ray above $`r` exactly when it is greater than $`r`. -/
theorem real_mem_upperRay {r x : ℝ} : F.real x ∈ F.upperRay r ↔ r < x := by
  rw [upperRay, mem_sep, F.pair_mem_Le]
  exact ⟨fun ⟨_, hle, hne⟩ => lt_of_le_of_ne hle fun h => hne (h ▸ rfl),
    fun h => ⟨F.mem_R.2 ⟨x, rfl⟩, h.le, fun e => h.ne' (F.real_injective e)⟩⟩

/-- A member of the ray above $`r` is a real number greater than $`r`. -/
theorem exists_of_mem_upperRay {r : ℝ} {a : ZFSet.{u}} (ha : a ∈ F.upperRay r) :
    ∃ x : ℝ, r < x ∧ a = F.real x := by
  obtain ⟨x, rfl⟩ := F.mem_R.1 (mem_sep.1 ha).1
  exact ⟨x, F.real_mem_upperRay.1 ha, rfl⟩

/-- The set $`\mathbb R^+` of positive reals, the ray above $`0`, is a set of the universe. -/
theorem isSetOf_upperRay (r : ℝ) : IsSetOf F.U (F.upperRay r) := F.hU.isSetOf_sep F.isSetOf_R _

/-- **Section 14.2, first example: the relation.** The "greater than" relation on the positive
reals, $`\{(r, y) \in \mathbb R^+ \times \mathbb R^+ : r > y\}`. The set $`\mathbb R^+` is the
ray {lit}`upperRay 0` of Chapter 13, and $`r > y` is written as $`y \le r` and $`y \ne r`. -/
def gtRel : ZFSet.{u} :=
  (prod (F.upperRay 0) (F.upperRay 0)).sep fun p => ∃ r y, p = pair r y ∧ pair y r ∈ F.Le ∧ y ≠ r

/-- **Section 14.2, second example: the relation.** The "less than" relation on the positive
reals, $`\{(r, y) \in \mathbb R^+ \times \mathbb R^+ : r < y\}`. -/
def ltRel : ZFSet.{u} :=
  (prod (F.upperRay 0) (F.upperRay 0)).sep fun p => ∃ r y, p = pair r y ∧ pair r y ∈ F.Le ∧ y ≠ r

variable {F}

/-- Membership of a pair in the "greater than" relation. -/
theorem pair_mem_gtRel {a y : ZFSet.{u}} :
    pair a y ∈ F.gtRel ↔ a ∈ F.upperRay 0 ∧ y ∈ F.upperRay 0 ∧ pair y a ∈ F.Le ∧ y ≠ a := by
  rw [gtRel, mem_sep, pair_mem_prod]
  constructor
  · rintro ⟨⟨h1, h2⟩, a', y', e, h3⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.1 e
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, a, y, rfl, h3⟩

/-- Membership of a pair in the "less than" relation. -/
theorem pair_mem_ltRel {a y : ZFSet.{u}} :
    pair a y ∈ F.ltRel ↔ a ∈ F.upperRay 0 ∧ y ∈ F.upperRay 0 ∧ pair a y ∈ F.Le ∧ y ≠ a := by
  rw [ltRel, mem_sep, pair_mem_prod]
  constructor
  · rintro ⟨⟨h1, h2⟩, a', y', e, h3⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.1 e
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, a, y, rfl, h3⟩

/-- For real numbers, $`(r, y)` is in the "greater than" relation exactly when
$`0 < y < r`. -/
theorem real_pair_mem_gtRel {r y : ℝ} :
    pair (F.real r) (F.real y) ∈ F.gtRel ↔ 0 < r ∧ 0 < y ∧ y < r := by
  rw [pair_mem_gtRel, F.real_mem_upperRay, F.real_mem_upperRay, F.pair_mem_Le]
  exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, lt_of_le_of_ne h3 fun e => h4 (e ▸ rfl)⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3.le, fun e => h3.ne (F.real_injective e)⟩⟩

/-- For real numbers, $`(r, y)` is in the "less than" relation exactly when
$`0 < r < y`. -/
theorem real_pair_mem_ltRel {r y : ℝ} :
    pair (F.real r) (F.real y) ∈ F.ltRel ↔ 0 < r ∧ 0 < y ∧ r < y := by
  rw [pair_mem_ltRel, F.real_mem_upperRay, F.real_mem_upperRay, F.pair_mem_Le]
  exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, lt_of_le_of_ne h3 fun e => h4 (e ▸ rfl)⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3.le, fun e => h3.ne' (F.real_injective e)⟩⟩

/-- Finitely many members of the ray above $`0` are positive reals with a positive lower
bound $`m` and an upper bound $`M`. -/
theorem exists_bounds_of_finset (s : Finset ZFSet.{u}) (hs : ∀ x ∈ s, x ∈ F.upperRay 0) :
    ∃ m M : ℝ, 0 < m ∧ ∀ x ∈ s, ∃ r : ℝ, x = F.real r ∧ m ≤ r ∧ r ≤ M := by
  choose r hr using fun x : {x // x ∈ s} => F.exists_of_mem_upperRay (hs x.1 x.2)
  have hne : (insert 1 (s.attach.image r)).Nonempty := Finset.insert_nonempty _ _
  refine ⟨(insert 1 (s.attach.image r)).min' hne, (insert 1 (s.attach.image r)).max' hne, ?_,
    fun x hx => ⟨r ⟨x, hx⟩, (hr ⟨x, hx⟩).2, ?_, ?_⟩⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨B, -, rfl⟩ := Finset.mem_image.1 hy
      exact (hr B).1
  · exact Finset.min'_le (insert 1 (s.attach.image r)) _
      (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩))
  · exact Finset.le_max' (insert 1 (s.attach.image r)) _
      (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩))

variable (F) in
/-- **Section 14.2, first example.** The "greater than" relation on the positive reals is
concurrent: finitely many positive reals are all greater than half of the least of them. -/
theorem concurrent_gtRel : Concurrent F.gtRel := fun s hs => by
  obtain ⟨m, M, hm, h⟩ := exists_bounds_of_finset s fun x hx => by
    obtain ⟨y, hy⟩ := mem_dom.1 (hs x hx)
    exact (pair_mem_gtRel.1 hy).1
  refine ⟨F.real (m / 2), fun x hx => ?_⟩
  obtain ⟨r, rfl, h1, -⟩ := h x hx
  exact real_pair_mem_gtRel.2 ⟨by linarith, by linarith, by linarith⟩

variable (F) in
/-- **Section 14.2, second example.** The "less than" relation on the positive reals is
concurrent: finitely many positive reals are all less than their maximum plus one. -/
theorem concurrent_ltRel : Concurrent F.ltRel := fun s hs => by
  obtain ⟨m, M, hm, h⟩ := exists_bounds_of_finset s fun x hx => by
    obtain ⟨y, hy⟩ := mem_dom.1 (hs x hx)
    exact (pair_mem_ltRel.1 hy).1
  refine ⟨F.real (M + 1), fun x hx => ?_⟩
  obtain ⟨r, rfl, h1, h2⟩ := h x hx
  exact real_pair_mem_ltRel.2 ⟨by linarith, by linarith, by linarith⟩

variable (F) in
/-- **Section 14.2, first example.** By transfer, the transform of the "greater than"
relation on $`\mathbb R^+` is the "greater than" relation on $`{}^*\mathbb R^+`. -/
theorem pair_mem_star_gtRel {x y : ZFSet.{u}} :
    pair x y ∈ F.star F.gtRel ↔ x ∈ F.star (F.upperRay 0) ∧ y ∈ F.star (F.upperRay 0) ∧
      pair y x ∈ F.star F.Le ∧ y ≠ x := by
  have hP := F.isSetOf_upperRay 0
  have hsub : F.gtRel ⊆ prod (F.upperRay 0) (F.upperRay 0) := sep_subset
  have hR := F.hU.isSetOf_of_subset_prod hP hP hsub
  have ht := F.transfer
    (.all 0 (.const (F.upperRay 0)) (.all 1 (.const (F.upperRay 0))
      (.biimp (.elem (.opair (.var 0) (.var 1)) (.const F.gtRel))
        (.conj (.elem (.opair (.var 1) (.var 0)) (.const F.Le))
          (.neg (.equal (.var 1) (.var 0)))))))
    (by simp [IsSentence, hP.1, hR.1, F.isSetOf_Le.1])
  sat_simp at ht
  have key := ht.1 fun a _ ha y _ hy =>
    ⟨fun h => (pair_mem_gtRel.1 h).2.2, fun h => pair_mem_gtRel.2 ⟨ha, hy, h⟩⟩
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := pair_mem_prod.1 (F.star_subset_prod hP hP hsub h)
    exact ⟨hx, hy, (key x (F.star_subset_U' hP hx) hx y (F.star_subset_U' hP hy) hy).1 h⟩
  · rintro ⟨hx, hy, h⟩
    exact (key x (F.star_subset_U' hP hx) hx y (F.star_subset_U' hP hy) hy).2 h

variable (F) in
/-- **Section 14.2, second example.** By transfer, the transform of the "less than"
relation on $`\mathbb R^+` is the "less than" relation on $`{}^*\mathbb R^+`. -/
theorem pair_mem_star_ltRel {x y : ZFSet.{u}} :
    pair x y ∈ F.star F.ltRel ↔ x ∈ F.star (F.upperRay 0) ∧ y ∈ F.star (F.upperRay 0) ∧
      pair x y ∈ F.star F.Le ∧ y ≠ x := by
  have hP := F.isSetOf_upperRay 0
  have hsub : F.ltRel ⊆ prod (F.upperRay 0) (F.upperRay 0) := sep_subset
  have hR := F.hU.isSetOf_of_subset_prod hP hP hsub
  have ht := F.transfer
    (.all 0 (.const (F.upperRay 0)) (.all 1 (.const (F.upperRay 0))
      (.biimp (.elem (.opair (.var 0) (.var 1)) (.const F.ltRel))
        (.conj (.elem (.opair (.var 0) (.var 1)) (.const F.Le))
          (.neg (.equal (.var 1) (.var 0)))))))
    (by simp [IsSentence, hP.1, hR.1, F.isSetOf_Le.1])
  sat_simp at ht
  have key := ht.1 fun a _ ha y _ hy =>
    ⟨fun h => (pair_mem_ltRel.1 h).2.2, fun h => pair_mem_ltRel.2 ⟨ha, hy, h⟩⟩
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := pair_mem_prod.1 (F.star_subset_prod hP hP hsub h)
    exact ⟨hx, hy, (key x (F.star_subset_U' hP hx) hx y (F.star_subset_U' hP hy) hy).1 h⟩
  · rintro ⟨hx, hy, h⟩
    exact (key x (F.star_subset_U' hP hx) hx y (F.star_subset_U' hP hy) hy).2 h

/-- **Section 14.2, first example.** A bound of the transformed "greater than" relation on the
positive reals, that is, an entity $`b` with $`r \mathrel{{}^*R} b` for every positive real
$`r`, is a positive infinitesimal: $`b \in {}^*\mathbb R` and $`0 < b < r` for every positive
real $`r`. The conclusion is that of {lit}`exists_pos_infinitesimal`. -/
theorem pos_infinitesimal_of_bound_gtRel {b : ZFSet.{u}}
    (hb : ∀ x ∈ dom F.gtRel, pair (F.star x) b ∈ F.star F.gtRel) :
    b ∈ F.star F.R ∧ ∀ r : ℝ, 0 < r →
      (pair (F.real 0) b ∈ F.star F.Le ∧ b ≠ F.real 0) ∧
        (pair b (F.real r) ∈ F.star F.Le ∧ b ≠ F.real r) := by
  have key : ∀ r : ℝ, 0 < r →
      b ∈ F.star (F.upperRay 0) ∧ pair b (F.real r) ∈ F.star F.Le ∧ b ≠ F.real r := fun r hr => by
    have h := hb (F.real r) (mem_dom.2 ⟨F.real (r / 2),
      real_pair_mem_gtRel.2 ⟨hr, by linarith, by linarith⟩⟩)
    rw [F.star_real] at h
    exact (F.pair_mem_star_gtRel.1 h).2
  have h1 := (key 1 one_pos).1
  rw [F.star_upperRay, mem_sep] at h1
  exact ⟨h1.1, fun r hr => ⟨h1.2, (key r hr).2⟩⟩

/-- **Section 14.2, second example.** A bound of the transformed "less than" relation on the
positive reals, an entity $`b` with $`r \mathrel{{}^*R} b` for every positive real $`r`, is a
positive unlimited hyperreal: $`b \in {}^*\mathbb R` and $`r < b` for every real $`r`. The
conclusion is that of {lit}`exists_pos_unlimited`. -/
theorem pos_unlimited_of_bound_ltRel {b : ZFSet.{u}}
    (hb : ∀ x ∈ dom F.ltRel, pair (F.star x) b ∈ F.star F.ltRel) :
    b ∈ F.star F.R ∧ ∀ r : ℝ, pair (F.real r) b ∈ F.star F.Le ∧ b ≠ F.real r := by
  have key : ∀ r : ℝ, 0 < r →
      b ∈ F.star (F.upperRay 0) ∧ pair (F.real r) b ∈ F.star F.Le ∧ b ≠ F.real r := fun r hr => by
    have h := hb (F.real r) (mem_dom.2 ⟨F.real (r + 1),
      real_pair_mem_ltRel.2 ⟨hr, by linarith, by linarith⟩⟩)
    rw [F.star_real] at h
    exact (F.pair_mem_star_ltRel.1 h).2
  have h1 := (key 1 one_pos).1
  have h0 := h1
  rw [F.star_upperRay, mem_sep] at h0
  refine ⟨h0.1, fun r => ?_⟩
  rcases lt_or_ge 0 r with hr | hr
  · exact (key r hr).2
  · have hsub : F.upperRay 0 ⊆ F.upperRay r := fun a ha => by
      obtain ⟨x, hx, rfl⟩ := F.exists_of_mem_upperRay ha
      exact F.real_mem_upperRay.2 (by linarith)
    have h2 := (F.star_subset_star_iff (F.isSetOf_upperRay 0) (F.isSetOf_upperRay r)).2 hsub h1
    rw [F.star_upperRay, mem_sep] at h2
    exact h2.2

end RealFramework

namespace NonstandardFramework

open Formula Term

variable (F : NonstandardFramework.{u}) {A B R : ZFSet.{u}}

/-- **Theorem 14.2.1, condition (2).** Every concurrent relation
$`R \in \mathbb U` has a bound in $`\mathbb U'`: an entity $`b` with
$`{}^*x \mathrel{{}^*R} b` for all $`x` in the domain of $`R`. -/
def ConcurrentBound : Prop :=
  ∀ R, IsSetOf F.U R → RelIn F.U R → Concurrent R →
    ∃ b ∈ F.U', ∀ x ∈ dom R, pair (F.star x) b ∈ F.star R

/-- **Theorem 14.2.1, condition (3).** Hyperfinite approximation: for each
set $`A \in \mathbb U` there is a hyperfinite $`B \in {}^*\mathcal P_F(A)` that contains every
standard member of $`{}^*A`, that is, the image $`\{{}^*a : a \in A\}` of $`A`. Such a $`B` is
automatically a subset of $`{}^*A`. -/
def HyperfiniteApprox : Prop :=
  ∀ A, IsSetOf F.U A → ∃ B ∈ F.star (finPow A), F.im A ⊆ B

variable {F}

/-- **Theorem 14.2.1, (1) implies (2).** In an enlargement every
concurrent relation $`R \in \mathbb U` has a bound. The sets
$`R[x] = \{y : x \mathrel R y\}` for $`x` in the domain form a collection with the finite
intersection property, an element $`b` of all the $`{}^*(R[x])` exists by the enlargement
property, and transfer of $`(\forall y \in R[x])\,(x, y) \in R` gives
$`{}^*x \mathrel{{}^*R} b`. -/
theorem IsEnlargement.concurrentBound (hE : F.IsEnlargement) : F.ConcurrentBound := by
  intro R hR hrel hc
  have hran := F.hU.isSetOf_ran hR hrel
  have hdom := F.hU.isSetOf_dom hR hrel
  set 𝒜 : ZFSet.{u} := ZFSet.range fun x : ↥(dom R) => (ran R).sep fun y => pair x.1 y ∈ R
    with h𝒜def
  have hsets : ∀ B ∈ 𝒜, IsSetOf F.U B := fun B hB => by
    obtain ⟨x, rfl⟩ := mem_range.1 hB
    exact F.hU.isSetOf_sep hran _
  have h𝒜 : IsSetOf F.U 𝒜 := F.hU.isSetOf_of_subset (F.hU.isSetOf_powerset hran) fun B hB => by
    obtain ⟨x, rfl⟩ := mem_range.1 hB
    exact mem_powerset.2 sep_subset
  have hfip : FIP 𝒜 := fun s hs => by
    choose x hx using fun B : {B // B ∈ 𝒜} => mem_range.1 B.2
    let g : {B // B ∈ s} → ZFSet.{u} := fun B => (x ⟨B.1, hs B.1 B.2⟩).1
    obtain ⟨y, hy⟩ := hc (s.attach.image g) fun a ha => by
      obtain ⟨B, -, rfl⟩ := Finset.mem_image.1 ha
      exact (x _).2
    refine ⟨y, fun B hB => ?_⟩
    have h := hy _ (Finset.mem_image.2 ⟨⟨B, hB⟩, Finset.mem_attach _ _, rfl⟩)
    have e := hx ⟨B, hs B hB⟩
    simp only at e
    rw [← e]
    exact mem_sep.2 ⟨mem_ran.2 ⟨_, h⟩, h⟩
  obtain ⟨b, hb, hbm⟩ := hE 𝒜 h𝒜 hsets hfip
  refine ⟨b, hb, fun x hx => ?_⟩
  have hmem : (ran R).sep (fun y => pair x y ∈ R) ∈ 𝒜 := mem_range.2 ⟨⟨x, hx⟩, rfl⟩
  have ht := F.transfer
    (.all 0 (.const ((ran R).sep fun y => pair x y ∈ R))
      (.elem (.opair (.const x) (.var 0)) (.const R)))
    (by simp [IsSentence, (hsets _ hmem).1, F.hU.subset hdom hx, hR.1])
  sat_simp at ht
  exact ht.1 (fun a _ ha => (mem_sep.1 ha).2) b hb (hbm _ hmem)

/-- **Theorem 14.2.1, (2) implies (3).** If concurrent
relations have bounds, then every set $`A \in \mathbb U` has a hyperfinite approximation: a
bound $`B` of the membership relation between $`A` and $`\mathcal P_F(A)` lies in
$`{}^*\mathcal P_F(A)` and contains $`{}^*a` for every $`a \in A`. -/
theorem ConcurrentBound.hyperfiniteApprox (h2 : F.ConcurrentBound) : F.HyperfiniteApprox := by
  intro A hA
  have hP := F.hU.isSetOf_finPow hA
  by_cases hne : A = ∅
  · subst hne
    refine ⟨F.star ∅, (F.star_mem_star_iff F.hU.empty_mem hP.1).2
      (mem_finPow.2 ⟨fun _ h => h, by simp⟩), fun b hb => ?_⟩
    obtain ⟨a, ha, -⟩ := F.mem_im.1 hb
    exact absurd ha (notMem_empty a)
  obtain ⟨a0, ha0⟩ := (eq_empty_or_nonempty A).resolve_left hne
  set R : ZFSet.{u} := memRel A with hRdef
  have hmemR : ∀ {a Z : ZFSet.{u}}, pair a Z ∈ R ↔ a ∈ A ∧ Z ∈ finPow A ∧ a ∈ Z :=
    pair_mem_memRel
  have hRsub : R ⊆ prod A (finPow A) := sep_subset
  have hR := F.hU.isSetOf_of_subset_prod hA hP hRsub
  have hrel := F.hU.relIn_of_subset_prod hA hP hRsub
  have hAdom : ∀ {a : ZFSet.{u}}, a ∈ A → a ∈ dom R := fun {a} h => by
    rw [hRdef, dom_memRel]
    exact h
  have hconc : Concurrent R := concurrent_memRel A
  obtain ⟨B, hB, hBm⟩ := h2 R hR hrel hconc
  have hstarR := F.star_subset_prod hA hP hRsub
  have hBfin : B ∈ F.star (finPow A) := (pair_mem_prod.1 (hstarR (hBm a0 (hAdom ha0)))).2
  refine ⟨B, hBfin, fun b hb => ?_⟩
  obtain ⟨a, ha, rfl⟩ := F.mem_im.1 hb
  have ht := F.transfer
    (.all 0 (.const A) (.all 1 (.const (finPow A))
      (.imp (.elem (.opair (.var 0) (.var 1)) (.const R)) (.elem (.var 0) (.var 1)))))
    (by simp [IsSentence, hA.1, hP.1, hR.1])
  sat_simp at ht
  exact ht.1 (fun a _ _ Z _ _ h => (hmemR.1 h).2.2) (F.star a) (F.star_mem a (F.hU.subset hA ha))
    ((F.star_mem_star_iff (F.hU.subset hA ha) hA.1).2 ha) B hB hBfin (hBm a (hAdom ha))

/-- **Theorem 14.2.1, (3) implies (1).** A framework with
hyperfinite approximation is an enlargement. For a collection $`\mathcal A` with the finite
intersection property the sentence
$$`(\forall Z \in \mathcal P_F(\mathcal A))(\exists y \in T)(\forall z \in Z)\,(y \in z)`
is true, and its transform is applied to a hyperfinite $`B` containing the image of
$`\mathcal A`. The book takes $`T` transitive with $`\mathcal A \subseteq T`; the formal proof
takes $`T = \bigcup \mathcal A`, which serves the same purpose. -/
theorem HyperfiniteApprox.isEnlargement (h3 : F.HyperfiniteApprox) : F.IsEnlargement := by
  intro 𝒜 h𝒜 hsets hfip
  by_cases hne : 𝒜 = ∅
  · subst hne
    exact ⟨∅, F.isUniverse'.empty_mem, fun B hB => absurd hB (notMem_empty B)⟩
  obtain ⟨B0, hB0⟩ := (eq_empty_or_nonempty 𝒜).resolve_left hne
  have hT := F.hU.isSetOf_sUnion h𝒜 hsets
  have hP := F.hU.isSetOf_finPow h𝒜
  have ht := F.transfer
    (.all 0 (.const (finPow 𝒜)) (.ex 1 (.const (⋃₀ 𝒜)) (.all 2 (.var 0)
      (.elem (.var 1) (.var 2)))))
    (by simp [IsSentence, hP.1, hT.1])
  sat_simp at ht
  obtain ⟨B, hB, him⟩ := h3 𝒜 h𝒜
  obtain ⟨b, hbU, -, hb⟩ := ht.1 (fun Z _ hZ => by
    obtain ⟨hZsub, hZfin⟩ := mem_finPow.1 hZ
    obtain ⟨y, hy⟩ := hfip (insert B0 hZfin.toFinset) fun C hC => by
      rcases Finset.mem_insert.1 hC with rfl | hC
      · exact hB0
      · exact hZsub (hZfin.mem_toFinset.1 hC)
    have hyT : y ∈ ⋃₀ 𝒜 := mem_sUnion.2 ⟨B0, hB0, hy B0 (Finset.mem_insert_self _ _)⟩
    exact ⟨y, F.hU.subset hT hyT, hyT, fun z _ hz =>
      hy z (Finset.mem_insert_of_mem (hZfin.mem_toFinset.2 hz))⟩) B (F.star_subset_U' hP hB) hB
  exact ⟨b, hbU, fun C hC =>
    hb (F.star C) (F.star_mem C (F.hU.subset h𝒜 hC)) (him (F.mem_im.2 ⟨C, hC, rfl⟩))⟩

variable (F) in
/-- **Theorem 14.2.1.** For a nonstandard framework the following are
equivalent: (1) it is an enlargement; (2) every concurrent relation in $`\mathbb U` has a bound
in $`\mathbb U'`; (3) every set $`A \in \mathbb U` has a hyperfinite approximation
$`B \in {}^*\mathcal P_F(A)` containing all $`{}^*a` with $`a \in A`. -/
theorem enlargement_tfae : List.TFAE [F.IsEnlargement, F.ConcurrentBound, F.HyperfiniteApprox] := by
  tfae_have 1 → 2 := IsEnlargement.concurrentBound
  tfae_have 2 → 3 := ConcurrentBound.hyperfiniteApprox
  tfae_have 3 → 1 := HyperfiniteApprox.isEnlargement
  tfae_finish

/-- **Section 14.1, fourth example.** In an enlargement every
set $`A \in \mathbb U` has a hyperfinite approximation: a hyperfinite set $`B` with
$`\{{}^*a : a \in A\} \subseteq B \subseteq {}^*A`. -/
theorem IsEnlargement.exists_hyperfinite (hE : F.IsEnlargement) (hA : IsSetOf F.U A) :
    ∃ B, F.Hyperfinite B ∧ F.im A ⊆ B ∧ B ⊆ F.star A := by
  obtain ⟨B, hB, him⟩ := hE.concurrentBound.hyperfiniteApprox A hA
  exact ⟨B, ⟨A, hA, hB⟩, him, (F.internal_subset_of_mem_star_finPow hA hB).1⟩

end NonstandardFramework

namespace RealFramework

variable {F : RealFramework.{u}}

/-- **Section 14.2, first example.** In an enlargement the "greater than" relation on the
positive reals has a bound, and every bound is a positive infinitesimal. -/
theorem exists_bound_gtRel (hE : F.IsEnlargement) :
    ∃ b, (∀ x ∈ dom F.gtRel, pair (F.star x) b ∈ F.star F.gtRel) ∧ b ∈ F.star F.R ∧
      ∀ r : ℝ, 0 < r → (pair (F.real 0) b ∈ F.star F.Le ∧ b ≠ F.real 0) ∧
        (pair b (F.real r) ∈ F.star F.Le ∧ b ≠ F.real r) := by
  have hP := F.isSetOf_upperRay 0
  obtain ⟨b, -, hb⟩ := hE.concurrentBound F.gtRel (F.hU.isSetOf_of_subset_prod hP hP sep_subset)
    (F.hU.relIn_of_subset_prod hP hP sep_subset) F.concurrent_gtRel
  exact ⟨b, hb, pos_infinitesimal_of_bound_gtRel hb⟩

/-- **Section 14.2, second example.** In an enlargement the "less than" relation on the
positive reals has a bound, and every bound is a positive unlimited hyperreal. -/
theorem exists_bound_ltRel (hE : F.IsEnlargement) :
    ∃ b, (∀ x ∈ dom F.ltRel, pair (F.star x) b ∈ F.star F.ltRel) ∧ b ∈ F.star F.R ∧
      ∀ r : ℝ, pair (F.real r) b ∈ F.star F.Le ∧ b ≠ F.real r := by
  have hP := F.isSetOf_upperRay 0
  obtain ⟨b, -, hb⟩ := hE.concurrentBound F.ltRel (F.hU.isSetOf_of_subset_prod hP hP sep_subset)
    (F.hU.relIn_of_subset_prod hP hP sep_subset) F.concurrent_ltRel
  exact ⟨b, hb, pos_unlimited_of_bound_ltRel hb⟩

end RealFramework

end Goldblatt
