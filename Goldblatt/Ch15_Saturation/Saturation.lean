import Goldblatt.Ch15_Saturation.Ultrapower

/-!
# 15 (part 7). Saturation: Section 15.5

This is the last of seven parts of Chapter 15 (the overview is on the chapter page
{lit}`Goldblatt.Ch15_Saturation`). It restates countable saturation in terms of countable
collections with the finite intersection property, defines $`\kappa`-saturation for a
cardinal $`\kappa`, shows that an infinite internal set of a $`\kappa`-saturated framework
has at least $`\kappa` members, states the existence of $`\kappa`-saturated enlargements,
and proves the characterization of $`\kappa`-saturation by concurrent relations
(Exercise 15.5.1).
-/

noncomputable section

namespace Goldblatt

open ZFSet NonstandardFramework Cardinal

universe u

namespace NonstandardFramework

variable (F : NonstandardFramework.{u}) {A B R : ZFSet.{u}} {κ κ' : Cardinal.{u}}

/-!
## 15.5 Saturation

Countable saturation was defined in Section 15.4 for decreasing sequences. It is the same as
the statement that every countable collection of internal sets with the finite intersection
property has a common member. For uncountable collections the corresponding statement can
fail: the sets $`{}^*\mathbb R - \{r\}`, $`r \in {}^*\mathbb R`, have the finite
intersection property and no common member. The remedy is to bound the size of the
collection by a cardinal $`\kappa`, which gives the notion of a $`\kappa`-saturated
framework.

Collections of sets are given as families indexed by a type. A collection with fewer than
$`\kappa` members, for a cardinal $`\kappa` of the universe level of the sets, can always be
indexed by a type of that level, so nothing is lost.
-/

variable {F}

/-- **Section 15.5, first statement, for sequences.** A framework is countably saturated
if and only if every sequence of internal sets with the finite intersection property has
nonempty intersection. -/
theorem countablySaturated_iff_seq_fip :
    F.CountablySaturated ↔ ∀ A : ℕ → ZFSet.{u}, (∀ n, F.InternalSet (A n)) →
      (∀ t : Finset ℕ, ∃ x, ∀ n ∈ t, x ∈ A n) → ∃ x, ∀ n, x ∈ A n := by
  refine ⟨fun h => h.exists_mem_of_fip, fun h A hA hdec hne => h A hA fun t => ?_⟩
  have hanti : ∀ j k, j ≤ k → A k ⊆ A j := fun j k hjk => by
    induction hjk with
    | refl => exact fun _ h => h
    | step _ ih => exact fun y hy => ih (hdec _ hy)
  obtain ⟨x, hx⟩ := (eq_empty_or_nonempty (A (t.sup id))).resolve_left (hne _)
  exact ⟨x, fun n hn => hanti n _ (Finset.le_sup (f := id) hn) hx⟩

/-- **Section 15.5, first statement.** Countable saturation can be tested on arbitrary
countable collections instead of decreasing sequences. A framework is countably saturated
exactly when, for each countable set $`S` of internal sets in which any finitely many members
have a common point, some point lies in every member of $`S`. The collection is a Lean
{name}`Set.Countable` set of entities, and the finite intersection property is stated for
its finite subsets. -/
theorem countablySaturated_iff_countable_fip :
    F.CountablySaturated ↔ ∀ S : Set ZFSet.{u}, S.Countable → (∀ A ∈ S, F.InternalSet A) →
      (∀ t : Finset ZFSet.{u}, (↑t : Set ZFSet.{u}) ⊆ S → ∃ x, ∀ A ∈ t, x ∈ A) →
        ∃ x, ∀ A ∈ S, x ∈ A := by
  classical
  rw [countablySaturated_iff_seq_fip]
  constructor
  · intro h S hS hint hfip
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, fun A hA => absurd hA (Set.notMem_empty A)⟩
    · obtain ⟨s, rfl⟩ := hS.exists_eq_range hne
      obtain ⟨x, hx⟩ := h s (fun n => hint _ ⟨n, rfl⟩) fun t => by
        obtain ⟨x, hx⟩ := hfip (t.image s) (by
          intro A hA
          obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hA)
          exact ⟨n, rfl⟩)
        exact ⟨x, fun n hn => hx _ (Finset.mem_image_of_mem s hn)⟩
      exact ⟨x, by rintro _ ⟨n, rfl⟩; exact hx n⟩
  · intro h A hA hfip
    obtain ⟨x, hx⟩ := h (Set.range A) (Set.countable_range A)
      (by rintro _ ⟨n, rfl⟩; exact hA n) fun t ht => by
        have hex : ∀ B : {B // B ∈ t}, ∃ n, A n = B.1 := fun B => ht (Finset.mem_coe.2 B.2)
        choose idx hidx using hex
        obtain ⟨x, hx⟩ := hfip (t.attach.image idx)
        refine ⟨x, fun B hB => ?_⟩
        have := hx _ (Finset.mem_image_of_mem idx (Finset.mem_attach t ⟨B, hB⟩))
        rw [hidx ⟨B, hB⟩] at this
        exact this
    exact ⟨x, fun n => hx _ ⟨n, rfl⟩⟩

variable (F) in
/-- **Section 15.5, $`\kappa`-saturation.** Let $`\kappa` be a cardinal. The framework is
$`\kappa`-saturated when the following holds for every family $`(A_i)_{i \in \iota}` of
internal sets whose index type has cardinality below $`\kappa`: if each finite subfamily has
a common point, then the whole family has one. Indexing by a type loses nothing, since a
collection of fewer than $`\kappa` sets can be indexed by a type of the universe level of
$`\kappa`. The book gives the definition for enlargements; the enlargement property is a
separate hypothesis here. -/
def Saturated (κ : Cardinal.{u}) : Prop :=
  ∀ (ι : Type u) (A : ι → ZFSet.{u}), #ι < κ → (∀ i, F.InternalSet (A i)) →
    (∀ t : Finset ι, ∃ x, ∀ i ∈ t, x ∈ A i) → ∃ x, ∀ i, x ∈ A i

/-- A $`\kappa`-saturated framework is $`\kappa'`-saturated for every $`\kappa' \le
\kappa`. -/
theorem Saturated.mono (h : F.Saturated κ) (hκ : κ' ≤ κ) : F.Saturated κ' :=
  fun ι A hι => h ι A (hι.trans_le hκ)

/-- **Section 15.5.** Saturation at the first uncountable cardinal is countable
saturation: a family has fewer than $`\aleph_1` members exactly when it is countable, so
$`\aleph_1`-saturation of a framework and its countable saturation are the same
property. -/
theorem saturated_aleph_one_iff : F.Saturated ℵ₁ ↔ F.CountablySaturated := by
  classical
  rw [countablySaturated_iff_seq_fip]
  constructor
  · intro h A hA hfip
    obtain ⟨x, hx⟩ := h (ULift.{u} ℕ) (fun n => A n.down)
      (lt_aleph_one_iff.2 mk_le_aleph0) (fun n => hA n.down) fun t => by
        obtain ⟨x, hx⟩ := hfip (t.image ULift.down)
        exact ⟨x, fun i hi => hx _ (Finset.mem_image_of_mem _ hi)⟩
    exact ⟨x, fun n => hx ⟨n⟩⟩
  · intro h ι A hι hA hfip
    have hc : Countable ι := mk_le_aleph0_iff.1 (lt_aleph_one_iff.1 hι)
    by_cases hne : Nonempty ι
    · obtain ⟨e, he⟩ := exists_surjective_nat ι
      obtain ⟨x, hx⟩ := h (fun n => A (e n)) (fun n => hA _) fun t => by
        obtain ⟨x, hx⟩ := hfip (t.image e)
        exact ⟨x, fun n hn => hx _ (Finset.mem_image_of_mem e hn)⟩
      exact ⟨x, fun i => by obtain ⟨n, rfl⟩ := he i; exact hx n⟩
    · exact ⟨∅, fun i => absurd ⟨i⟩ hne⟩

/-- **Section 15.5, the example.** For an infinite internal set $`A` (the book takes
$`{}^*\mathbb R`), the internal sets $`A - \{a\}`, $`a \in A`, have the finite intersection
property and no common member. So the statement of countable saturation does not extend to
arbitrary collections of internal sets. -/
theorem fip_sdiff_singleton (hA : F.InternalSet A) (hinf : (A : Set ZFSet.{u}).Infinite) :
    (∀ a ∈ A, F.InternalSet (A \ {a})) ∧
      (∀ t : Finset ZFSet.{u}, ∃ x, ∀ a ∈ t, x ∈ A \ {a}) ∧ ¬ ∃ x, ∀ a ∈ A, x ∈ A \ {a} := by
  refine ⟨fun a ha => ⟨F.internal_sdiff hA.1 hA.2
    (F.internal_singleton (F.internal_of_mem_internal_set hA.1 hA.2 ha)),
    F.isUniverse'.isSetOf_sdiff hA.2⟩, fun t => ?_, ?_⟩
  · obtain ⟨x, hxA, hxt⟩ := hinf.exists_notMem_finset t
    exact ⟨x, fun a ha => mem_sdiff.2 ⟨hxA, fun h => hxt (mem_singleton.1 h ▸ ha)⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := hinf.nonempty
    have hxA : x ∈ A := (mem_sdiff.1 (hx a ha)).1
    exact (mem_sdiff.1 (hx x hxA)).2 (mem_singleton.2 rfl)

/-- **Section 15.5.** In a $`\kappa`-saturated framework every infinite internal set has
at least $`\kappa` members. Otherwise the sets $`A - \{a\}` would form a collection of fewer
than $`\kappa` internal sets with the finite intersection property and empty
intersection. -/
theorem Saturated.lift_le_mk_of_infinite (h : F.Saturated κ) (hA : F.InternalSet A)
    (hinf : (A : Set ZFSet.{u}).Infinite) :
    Cardinal.lift.{u + 1} κ ≤ #(↥A) := by
  classical
  by_contra hlt
  rw [not_le, ← lift_mk_shrink''.{u + 1, u} (↥A), lift_lt] at hlt
  obtain ⟨h1, h2, h3⟩ := fip_sdiff_singleton hA hinf
  let e := equivShrink.{u} (↥A)
  obtain ⟨x, hx⟩ := h (Shrink.{u} (↥A)) (fun i => A \ {(e.symm i).1}) hlt
    (fun i => h1 _ (e.symm i).2) fun t => by
      obtain ⟨x, hx⟩ := h2 (t.image fun i => (e.symm i).1)
      exact ⟨x, fun i hi => hx _ (Finset.mem_image_of_mem _ hi)⟩
  refine h3 ⟨x, fun a ha => ?_⟩
  have := hx (e ⟨a, ha⟩)
  rwa [Equiv.symm_apply_apply] at this

/-- **Section 15.5 (the argument of Section 11.12).** In a countably saturated framework
every infinite internal set is uncountable. -/
theorem CountablySaturated.not_countable_of_infinite (h : F.CountablySaturated)
    (hA : F.InternalSet A) (hinf : (A : Set ZFSet.{u}).Infinite) :
    ¬ (A : Set ZFSet.{u}).Countable := by
  intro hc
  have h1 := (saturated_aleph_one_iff.2 h).lift_le_mk_of_infinite hA hinf
  have hc' : Countable ↥A := hc
  have h2 : #(↥A) ≤ ℵ₀ := mk_le_aleph0_iff.2 hc'
  have h3 : Cardinal.lift.{u + 1} (ℵ₁ : Cardinal.{u}) ≤ ℵ₀ := h1.trans h2
  rw [← lift_aleph0.{u + 1, u}, lift_le] at h3
  exact absurd aleph0_lt_aleph_one (not_lt.2 h3)

/-- **Section 15.5, existence of saturated enlargements, the proved case.** Over an
arbitrary base set $`X` and for every cardinal $`\kappa \le \aleph_1`, the superstructure
$`\mathbb U(X)` has a $`\kappa`-saturated enlargement of the form $`\mathbb U({}^*X)`. It
is the countably saturated enlargement of
{name}`Goldblatt.exists_countablySaturated_enlargement`, which is $`\aleph_1`-saturated by
{name}`Goldblatt.NonstandardFramework.saturated_aleph_one_iff`. -/
theorem exists_saturated_enlargement_of_le_aleph_one {X : ZFSet.{u}} (hX : IsBaseSet X)
    (hκ : κ ≤ ℵ₁) :
    ∃ F : NonstandardFramework.{u}, F.X = X ∧ F.U = superstructure X ∧
      F.U' = superstructure (F.star X) ∧ F.IsEnlargement ∧ F.Saturated κ := by
  obtain ⟨F, h1, h2, h3, h4, -, h6⟩ := exists_countablySaturated_enlargement hX
  exact ⟨F, h1, h2, h3, h4, (saturated_aleph_one_iff.2 h6).mono hκ⟩

/-- **Section 15.5, existence of saturated enlargements.** Whatever the cardinal $`\kappa`
and the base set $`X`, there is a $`\kappa`-saturated enlargement of the superstructure
$`\mathbb U(X)`.

The book asserts this without proof and attributes it to special kinds of ultrafilters. For
$`\kappa \le \aleph_1` it is proved, over any base set
({name}`Goldblatt.NonstandardFramework.exists_saturated_enlargement_of_le_aleph_one`), and
that is all that Part V of the book needs. For $`\kappa > \aleph_1` the statement is
recorded and *not proved*: the single {lit}`sorry` of the chapter is confined to that case.
A proof needs an ultrafilter that is countably incomplete and $`\kappa^+`-good, together
with the theorem that the ultrapower modulo such an ultrafilter is $`\kappa^+`-saturated
(or else a union of a long chain of successive enlargements); neither good ultrafilters nor
either construction is available in Mathlib. The statement has the form of the enlargement
theorem of Chapter 14: the target universe is the superstructure over $`{}^*X`. -/
theorem exists_saturated_enlargement {X : ZFSet.{u}} (hX : IsBaseSet X) (κ : Cardinal.{u}) :
    ∃ F : NonstandardFramework.{u}, F.X = X ∧ F.U = superstructure X ∧
      F.U' = superstructure (F.star X) ∧ F.IsEnlargement ∧ F.Saturated κ := by
  rcases le_or_gt κ ℵ₁ with hκ | hκ
  · exact exists_saturated_enlargement_of_le_aleph_one hX hκ
  · sorry

/-- **Exercise 15.5.1.** Saturation in terms of concurrent relations. The framework is
$`\kappa`-saturated if and only if every internal binary relation $`R` has this property:
whenever $`(a_i)_{i \in \iota}` is a family of points of the domain of $`R`, indexed by a
type of cardinality below $`\kappa`, such that any finitely many of the $`a_i` are
$`R`-related to a common entity, there is one entity $`b` to which every $`a_i` is
$`R`-related, and $`b` lies in the range of $`R` provided the family is not empty.

The family $`(a_i)` plays the part of the book's set $`A`, which is an arbitrary set of
fewer than $`\kappa` points of the domain, internal or not, and the finiteness hypothesis is
concurrency of $`R` on $`A`. The clause on the range is conditional because the book's
unconditional one cannot be met when $`A` and $`R` are both empty; for a nonempty family it
is exactly the book's requirement. -/
theorem saturated_iff_concurrent :
    F.Saturated κ ↔ ∀ R, F.InternalSet R → RelIn F.U' R →
      ∀ (ι : Type u) (a : ι → ZFSet.{u}), #ι < κ → (∀ i, a i ∈ dom R) →
        (∀ t : Finset ι, ∃ b, ∀ i ∈ t, pair (a i) b ∈ R) →
          ∃ b, (Nonempty ι → b ∈ ran R) ∧ ∀ i, pair (a i) b ∈ R := by
  classical
  have hU' := F.isUniverse'
  constructor
  · intro h R hR hrel ι a hι hdom hconc
    have hdomint : F.InternalSet (dom R) :=
      ⟨F.internal_dom hR.1 hR.2 hrel, hU'.isSetOf_dom hR.2 hrel⟩
    obtain ⟨x, hx⟩ := h ι (fun i => relImage R {a i}) hι
      (fun i => ⟨F.internal_relImage hR.1 hR.2 hrel (F.internal_singleton
        (F.internal_of_mem_internal_set hdomint.1 hdomint.2 (hdom i))),
        hU'.isSetOf_relImage hR.2 hrel _⟩)
      fun t => by
        obtain ⟨b, hb⟩ := hconc t
        exact ⟨b, fun i hi => mem_relImage.2 ⟨a i, mem_singleton.2 rfl, hb i hi⟩⟩
    have hall : ∀ i, pair (a i) x ∈ R := fun i => by
      obtain ⟨a', ha', h'⟩ := mem_relImage.1 (hx i)
      rwa [mem_singleton.1 ha'] at h'
    exact ⟨x, fun ⟨i⟩ => mem_ran.2 ⟨a i, hall i⟩, hall⟩
  · intro h ι A hι hA hfip
    by_cases hne : Nonempty ι
    · obtain ⟨i₀⟩ := hne
      obtain ⟨T, hT, -, hsub, -⟩ := F.exists_ambient [A i₀] (by simp [(hA i₀).1])
      have hA0T : A i₀ ⊆ F.star T := hsub _ (by simp) (hA i₀).2
      obtain ⟨hEset, hErel⟩ := memRelOn_spec (F := F) hT
      obtain ⟨hEint, hEset', hErel'⟩ := star_rel_spec hEset hErel
      have hBP : ∀ i, A i ∩ A i₀ ∈ F.star (powerset T) := fun i =>
        (F.mem_star_powerset_iff hT).2 ⟨fun y hy => hA0T (mem_inter.1 hy).2,
          F.internal_inter (hA i).1 (hA i).2 (hA i₀).1⟩
      have hmem : ∀ {i : ι} {x : ZFSet.{u}}, x ∈ A i → x ∈ A i₀ →
          pair (A i ∩ A i₀) x ∈ relInv (F.star (memRelOn T)) := fun {i x} h1 h2 =>
        pair_mem_relInv.2 ((F.pair_mem_star_memRelOn hT).2
          ⟨hA0T h2, hBP i, mem_inter.2 ⟨h1, h2⟩⟩)
      obtain ⟨b, -, hb⟩ := h (relInv (F.star (memRelOn T)))
        ⟨F.internal_relInv hEint hEset' hErel', hU'.isSetOf_relInv hEset' hErel'⟩
        (relIn_relInv hErel') ι (fun i => A i ∩ A i₀) hι
        (fun i => by
          obtain ⟨x, hx⟩ := hfip {i, i₀}
          exact mem_dom.2 ⟨x, hmem (hx i (by simp)) (hx i₀ (by simp))⟩)
        fun t => by
          obtain ⟨x, hx⟩ := hfip (insert i₀ t)
          exact ⟨x, fun i hi => hmem (hx i (Finset.mem_insert_of_mem hi))
            (hx i₀ (Finset.mem_insert_self i₀ t))⟩
      refine ⟨b, fun i => ?_⟩
      have := ((F.pair_mem_star_memRelOn hT).1 (pair_mem_relInv.1 (hb i))).2.2
      exact (mem_inter.1 this).1
    · exact ⟨∅, fun i => absurd ⟨i⟩ hne⟩

end NonstandardFramework

namespace RealFramework

variable {F : RealFramework.{u}} {κ : Cardinal.{u}}

/-- $`{}^*\mathbb R` is infinite: it includes the real numbers. -/
theorem infinite_star_R (F : RealFramework.{u}) : (F.star F.R : Set ZFSet.{u}).Infinite := by
  refine Set.infinite_of_injective_forall_mem F.real_injective fun r => ?_
  exact F.real_mem_star r

/-- **Section 15.5.** In a $`\kappa`-saturated framework over the real numbers,
$`{}^*\mathbb R` is a set of size at least $`\kappa`. -/
theorem lift_le_mk_star_R (h : F.Saturated κ) :
    Cardinal.lift.{u + 1} κ ≤ #(↥(F.star F.R)) :=
  h.lift_le_mk_of_infinite F.star_R_spec F.infinite_star_R

/-- **Section 15.5, the example.** The collection $`\{{}^*\mathbb R - \{r\} : r \in
{}^*\mathbb R\}` of internal sets has the finite intersection property and empty
intersection. -/
theorem fip_star_R_sdiff_singleton (F : RealFramework.{u}) :
    (∀ r ∈ F.star F.R, F.InternalSet (F.star F.R \ {r})) ∧
      (∀ t : Finset ZFSet.{u}, ∃ x, ∀ r ∈ t, x ∈ F.star F.R \ {r}) ∧
      ¬ ∃ x, ∀ r ∈ F.star F.R, x ∈ F.star F.R \ {r} :=
  fip_sdiff_singleton F.star_R_spec F.infinite_star_R

/-- Every hypernatural number has a greater hypernatural number. -/
theorem exists_nat_gt {n : ZFSet.{u}} (hn : n ∈ F.star F.N) : ∃ m ∈ F.star F.N, F.Lt n m := by
  have h1 : n ∈ F.star (F.cR.set {a : ℝ | ∃ b : ℝ, (∃ j : ℕ, b = j) ∧ a < b}) :=
    F.cR.star_set_mono (by
      rintro a ⟨k, rfl⟩
      exact ⟨((k + 1 : ℕ) : ℝ), ⟨k + 1, rfl⟩, by push_cast; linarith⟩) (F.mem_star_N_iff.1 hn)
  obtain ⟨m, hm⟩ := (Code.mem_star_set_exists F.cR F.cR).1 h1
  refine ⟨m, F.mem_star_N_iff.2 (Code.mem_right_of_rel F.cR F.cR (fun a b hab => ?_) hm),
    Code.rel_mono F.cR F.cR (fun a b hab => hab.2) hm⟩
  obtain ⟨j, hj⟩ := hab.1
  exact ⟨j, hj.symm⟩

/-- **Section 15.4, an instance of the uncountability of infinite internal sets.** In a
countably saturated framework, every hypernatural $`K` has uncountably many hypernaturals
greater than it: the internal set $`\{n \in {}^*\mathbb N : K < n\}` is uncountable. -/
theorem not_countable_gt (hS : F.CountablySaturated) {K : ZFSet.{u}} (hK : K ∈ F.star F.N) :
    ¬ ({n | n ∈ F.star F.N ∧ F.Lt K n} : Set ZFSet.{u}).Countable := by
  classical
  obtain ⟨hNint, hNset⟩ := F.star_N_spec
  have hA : F.InternalSet (F.star F.N ∩ relImage (F.star (F.rr (· < ·))) {K}) :=
    ⟨F.internal_inter hNint hNset (internal_relImage_star (Code.isSetOf_rel _ _ _)
      (Code.relIn_rel _ _ _) (F.internal_singleton (F.internal_of_mem_star F.isSetOf_N hK))),
      F.isUniverse'.isSetOf_inter hNset⟩
  have hset : ((F.star F.N ∩ relImage (F.star (F.rr (· < ·))) {K} : ZFSet.{u}) :
      Set ZFSet.{u}) = {n | n ∈ F.star F.N ∧ F.Lt K n} := by
    ext n
    show n ∈ F.star F.N ∩ relImage (F.star (F.rr (· < ·))) {K} ↔ _
    rw [mem_inter, mem_relImage]
    refine and_congr_right fun _ => ⟨?_, fun h => ⟨K, mem_singleton.2 rfl, h⟩⟩
    rintro ⟨w, hw, hwn⟩
    rwa [mem_singleton.1 hw] at hwn
  rw [← hset]
  refine hS.not_countable_of_infinite hA ?_
  rw [hset]
  choose next hnext using fun p : {n // n ∈ F.star F.N} => exists_nat_gt p.2
  let f : ℕ → {n // n ∈ F.star F.N} := fun k =>
    Nat.rec ⟨K, hK⟩ (fun _ p => ⟨next p, (hnext p).1⟩) k
  have hstep : ∀ k, F.Lt (f k).1 (f (k + 1)).1 := fun k => (hnext (f k)).2
  have hmono : ∀ i j, i < j → F.Lt (f i).1 (f j).1 := by
    intro i j hij
    induction hij with
    | refl => exact hstep i
    | step _ ih => exact ih.trans (hstep _)
  refine Set.infinite_of_injective_forall_mem (f := fun k => (f (k + 1)).1) ?_ fun k =>
    ⟨(f (k + 1)).2, hmono 0 (k + 1) (Nat.succ_pos k)⟩
  intro i j hij
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := hmono (i + 1) (j + 1) (by omega)
    rw [show (f (i + 1)).1 = (f (j + 1)).1 from hij] at this
    exact lt_irrefl' this
  · have := hmono (j + 1) (i + 1) (by omega)
    rw [show (f (i + 1)).1 = (f (j + 1)).1 from hij] at this
    exact lt_irrefl' this

/-- **Section 15.4, a second instance.** In a countably saturated framework, an unlimited
hypernatural $`K` has uncountably many hypernaturals less than it: the internal set
$`\{n \in {}^*\mathbb N : n < K\}` is uncountable, while its limited part $`\mathbb N` is
countable. So $`K` has uncountably many unlimited hypernaturals below it. -/
theorem not_countable_lt_unlimited (hS : F.CountablySaturated) {K : ZFSet.{u}}
    (hK : K ∈ F.star F.N) (hKN : K ∉ F.N) :
    ¬ ({n | n ∈ F.star F.N ∧ F.Lt n K} : Set ZFSet.{u}).Countable := by
  obtain ⟨hNint, hNset⟩ := F.star_N_spec
  have hA : F.InternalSet (F.star F.N ∩ relPreimage (F.star (F.rr (· < ·))) {K}) :=
    ⟨F.internal_inter hNint hNset (internal_relPreimage_star (Code.isSetOf_rel _ _ _)
      (Code.relIn_rel _ _ _) (F.internal_singleton (F.internal_of_mem_star F.isSetOf_N hK))),
      F.isUniverse'.isSetOf_inter hNset⟩
  have hset : ((F.star F.N ∩ relPreimage (F.star (F.rr (· < ·))) {K} : ZFSet.{u}) :
      Set ZFSet.{u}) = {n | n ∈ F.star F.N ∧ F.Lt n K} := by
    ext n
    show n ∈ F.star F.N ∩ relPreimage (F.star (F.rr (· < ·))) {K} ↔ _
    rw [mem_inter, mem_relPreimage]
    refine and_congr_right fun _ => ⟨?_, fun h => ⟨K, mem_singleton.2 rfl, h⟩⟩
    rintro ⟨w, hw, hwn⟩
    rwa [mem_singleton.1 hw] at hwn
  rw [← hset]
  refine hS.not_countable_of_infinite hA ?_
  rw [hset]
  exact Set.infinite_of_injective_forall_mem F.nat_injective fun k =>
    ⟨F.N_subset_star (F.mem_N.2 ⟨k, rfl⟩), nat_lt_of_nonstandard hK hKN k⟩

/-- **Section 15.4.** In a countably saturated framework an unlimited hypernatural $`K`
has uncountably many _unlimited_ hypernaturals less than it. -/
theorem not_countable_unlimited_lt (hS : F.CountablySaturated) {K : ZFSet.{u}}
    (hK : K ∈ F.star F.N) (hKN : K ∉ F.N) :
    ¬ ({n | n ∈ F.star F.N ∧ n ∉ F.N ∧ F.Lt n K} : Set ZFSet.{u}).Countable := fun hc =>
  not_countable_lt_unlimited hS hK hKN ((hc.union F.countable_N).mono fun n hn => by
    by_cases hnN : n ∈ F.N
    · exact Or.inr hnN
    · exact Or.inl ⟨hn.1, hnN, hn.2⟩)

/-!
## Countably saturated frameworks over the reals: summary of consequences

Part V of the book works in a countably saturated enlargement. For a framework over the real
numbers, countable saturation alone yields an unlimited hypernatural number, sequential and
countable comprehensiveness, and Robinson's theorem; they are collected here in the form in
which they are used.
-/

/-- A countably saturated framework over the reals is sequentially comprehensive. -/
theorem sequentiallyComprehensive_of_countablySaturated (hS : F.CountablySaturated) :
    F.SequentiallyComprehensive :=
  sequentiallyComprehensive_of_countablyComprehensive hS.countablyComprehensive

/-- **Section 15.4.** In a countably saturated framework over the reals, every sequence
$`(s_n : n \in \mathbb N)` of members of an internal set $`B` extends to an internal
hypersequence $`(s_n : n \in {}^*\mathbb N)` of members of $`B`. -/
theorem exists_internal_extension_of_countablySaturated (hS : F.CountablySaturated)
    {B : ZFSet.{u}} (hB : F.InternalSet B) (s : ℕ → ZFSet.{u}) (hs : ∀ n, s n ∈ B) :
    ∃ g, F.Internal g ∧ IsFunc (F.star F.N) B g ∧ ∀ n : ℕ, app g (F.nat n) = s n :=
  (sequentiallyComprehensive_of_countablySaturated hS).exists_seq hB s hs

/-- **Theorem 15.4.3, in a countably saturated framework.** Every countable set of
unlimited hypernaturals has an unlimited hypernatural below all its members. -/
theorem exists_unlimited_lt_of_countable_of_countablySaturated (hS : F.CountablySaturated)
    (X : Set ZFSet.{u}) (hX : X.Countable) (h : ∀ x ∈ X, x ∈ F.star F.N ∧ x ∉ F.N) :
    ∃ K, K ∈ F.star F.N ∧ K ∉ F.N ∧ ∀ x ∈ X, F.Lt K x :=
  exists_unlimited_lt_of_countable (sequentiallyComprehensive_of_countablySaturated hS)
    (exists_nonstandard_nat_of_countablySaturated hS) X hX h

end RealFramework

end Goldblatt
