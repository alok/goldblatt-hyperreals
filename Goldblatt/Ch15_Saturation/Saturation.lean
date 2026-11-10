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

/-- **Section 15.5, first statement.** Countable saturation is equivalent to the
assertion that every countable collection of internal sets with the finite intersection
property has nonempty intersection. -/
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
/-- **Section 15.5, $`\kappa`-saturation.** A framework is $`\kappa`-saturated when any
collection of fewer than $`\kappa` internal sets with the finite intersection property has
nonempty intersection. The collection is a family indexed by a type with fewer than
$`\kappa` members. The book gives the definition for enlargements; the enlargement property
is a separate hypothesis here. -/
def Saturated (κ : Cardinal.{u}) : Prop :=
  ∀ (ι : Type u) (A : ι → ZFSet.{u}), #ι < κ → (∀ i, F.InternalSet (A i)) →
    (∀ t : Finset ι, ∃ x, ∀ i ∈ t, x ∈ A i) → ∃ x, ∀ i, x ∈ A i

/-- A $`\kappa`-saturated framework is $`\kappa'`-saturated for every $`\kappa' \le
\kappa`. -/
theorem Saturated.mono (h : F.Saturated κ) (hκ : κ' ≤ κ) : F.Saturated κ' :=
  fun ι A hι => h ι A (hι.trans_le hκ)

/-- **Section 15.5.** "Countably saturated" is the same as "$`\aleph_1`-saturated", where
$`\aleph_1` is the least uncountable cardinal. -/
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

/-- **Section 15.5, existence of saturated enlargements.** For any cardinal $`\kappa`, any
superstructure $`\mathbb U(X)` has a $`\kappa`-saturated enlargement.

The book states this without proof, with the remark that it is shown by using special kinds
of ultrafilters. The proof requires an ultrafilter that is countably incomplete and
$`\kappa^+`-good, and the theorem that the ultrapower modulo such an ultrafilter is
$`\kappa^+`-saturated; neither the existence of good ultrafilters nor that theorem is
available in Mathlib. The statement is recorded here and is not proved. The case
$`\kappa = \aleph_1` over the real numbers is proved:
{lit}`Goldblatt.exists_realFramework_countablySaturated`. -/
theorem exists_saturated_enlargement {X : ZFSet.{u}} (hX : IsBaseSet X) (κ : Cardinal.{u}) :
    ∃ F : NonstandardFramework.{u}, F.X = X ∧ F.U = superstructure X ∧
      F.U' = superstructure (F.star X) ∧ F.IsEnlargement ∧ F.Saturated κ := by
  sorry

/-- **Exercise 15.5.1.** $`\kappa`-saturation is equivalent to the following statement:
if an internal relation $`R` is concurrent on a subset $`A` of its domain that has
cardinality less than $`\kappa` ($`A` need not be internal), then there is an entity $`b`
such that $`a \mathrel R b` for all $`a \in A`. The set $`A` is given as a family
$`(a_i)` indexed by a type with fewer than $`\kappa` members, and concurrency on $`A` means
that for finitely many indices there is a $`b` related to all the corresponding $`a_i`.
The entity $`b` belongs to the range of $`R` as soon as $`A` is not empty; for empty $`A`
and empty $`R` the book's requirement that $`b` be in the range cannot be met, so it is not
part of the statement. -/
theorem saturated_iff_concurrent :
    F.Saturated κ ↔ ∀ R, F.InternalSet R → RelIn F.U' R →
      ∀ (ι : Type u) (a : ι → ZFSet.{u}), #ι < κ → (∀ i, a i ∈ dom R) →
        (∀ t : Finset ι, ∃ b, ∀ i ∈ t, pair (a i) b ∈ R) → ∃ b, ∀ i, pair (a i) b ∈ R := by
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
    refine ⟨x, fun i => ?_⟩
    obtain ⟨a', ha', h'⟩ := mem_relImage.1 (hx i)
    rwa [mem_singleton.1 ha'] at h'
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
      obtain ⟨b, hb⟩ := h (relInv (F.star (memRelOn T)))
        ⟨F.internal_relInv hEint hEset' hErel', hU'.isSetOf_relInv hEset' hErel'⟩
        hErel'.relInv ι (fun i => A i ∩ A i₀) hι
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

end RealFramework

end Goldblatt
