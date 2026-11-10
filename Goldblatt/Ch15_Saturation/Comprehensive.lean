import Goldblatt.Ch15_Saturation.Uniform

/-!
# 15 (part 5). Comprehensiveness and countable saturation: Section 15.4

This is the fifth of six parts of Chapter 15 (the overview is on the chapter page
{lit}`Goldblatt.Ch15_Saturation`). It defines comprehensive, countably comprehensive and
sequentially comprehensive frameworks and countable saturation, proves that the three
conditions of Theorem 15.4.2 are equivalent, and proves Robinson's theorem on countable sets
of unlimited hypernaturals (Theorem 15.4.3) in the two ways given in the book. That the
ultrapower of Chapter 14 is comprehensive is proved in part 6.
-/

noncomputable section

namespace Goldblatt

open ZFSet NonstandardFramework

universe u

/-!
## Preliminaries on relations and functions as sets
-/

section Sets

variable {U R S T X Y g x y : ZFSet.{u}}

/-- The inverse of a binary relation of a universe is a binary relation of the universe. -/
theorem RelIn.relInv (h : RelIn U R) : RelIn U (relInv R) := fun p hp => by
  obtain ⟨u, v, rfl, huv⟩ := mem_relInv.1 hp
  obtain ⟨u', hu', v', hv', huv'⟩ := h _ huv
  obtain ⟨rfl, rfl⟩ := pair_inj.1 huv'
  exact ⟨v, hv', u, hu', rfl⟩

/-- A subset of a binary relation of a universe is a binary relation of the universe. -/
theorem RelIn.mono (h : RelIn U R) (hS : S ⊆ R) : RelIn U S := fun p hp => h p (hS hp)

/-- **Changing one value of a function.** If $`g : X \to Y`, $`x \in X` and $`y \in Y`,
then removing from $`g` the pair with first component $`x` and adding $`(x, y)` gives a
function from $`X` to $`Y`. -/
theorem isFunc_update (hg : IsFunc X Y g) (hx : x ∈ X) (hy : y ∈ Y) :
    IsFunc X Y ((g \ ZFSet.prod {x} Y) ∪ {pair x y}) := by
  refine ⟨fun p hp => ?_, fun z hz => ?_⟩
  · rcases mem_union.1 hp with h | h
    · exact hg.1 (mem_sdiff.1 h).1
    · rw [mem_singleton.1 h]
      exact pair_mem_prod.2 ⟨hx, hy⟩
  · by_cases hzx : z = x
    · subst hzx
      refine ⟨y, mem_union.2 (Or.inr (mem_singleton.2 rfl)), fun w hw => ?_⟩
      rcases mem_union.1 hw with h | h
      · exact absurd (pair_mem_prod.2 ⟨mem_singleton.2 rfl,
          (pair_mem_prod.1 (hg.1 (mem_sdiff.1 h).1)).2⟩) (mem_sdiff.1 h).2
      · exact (pair_inj.1 (mem_singleton.1 h)).2
    · obtain ⟨w, hw, huniq⟩ := hg.2 z hz
      refine ⟨w, mem_union.2 (Or.inl (mem_sdiff.2 ⟨hw, fun h =>
        hzx (mem_singleton.1 (pair_mem_prod.1 h).1)⟩)), fun w' hw' => ?_⟩
      rcases mem_union.1 hw' with h | h
      · exact huniq w' (mem_sdiff.1 h).1
      · exact absurd (pair_inj.1 (mem_singleton.1 h)).1 hzx

/-- **The membership relation on a set.** The set of pairs $`(x, S)` with $`x \in S` and
$`S \subseteq T`. Its transform lets membership in a variable internal subset of $`{}^*T`
be handled with the operations on relations. -/
def memRelOn (T : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.prod T (powerset T)).sep fun p => ∃ x S, p = pair x S ∧ x ∈ S

/-- The members of the membership relation on a set. -/
theorem pair_mem_memRelOn : pair x S ∈ memRelOn T ↔ x ∈ T ∧ S ⊆ T ∧ x ∈ S := by
  rw [memRelOn, mem_sep, pair_mem_prod, mem_powerset]
  constructor
  · rintro ⟨⟨hx, hS⟩, x', S', h, hxS⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.1 h
    exact ⟨hx, hS, hxS⟩
  · rintro ⟨hx, hS, hxS⟩
    exact ⟨⟨hx, hS⟩, x, S, rfl, hxS⟩

/-- The $`n`-fold intersection $`A_0 \cap \dots \cap A_n` of a sequence of sets. -/
def interUpTo (A : ℕ → ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => A 0
  | n + 1 => interUpTo A n ∩ A (n + 1)

/-- The members of a finite intersection of an initial part of a sequence of sets. -/
theorem mem_interUpTo (A : ℕ → ZFSet.{u}) (n : ℕ) : x ∈ interUpTo A n ↔ ∀ i ≤ n, x ∈ A i := by
  induction n with
  | zero => simp [interUpTo]
  | succ n ih =>
    rw [interUpTo, mem_inter, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact h1 i (by omega)
      · obtain rfl : i = n + 1 := by omega
        exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h (n + 1) le_rfl⟩

end Sets

namespace NonstandardFramework

variable (F : NonstandardFramework.{u}) {A B T f g x S : ZFSet.{u}}

/-- The membership relation on a set of the universe is a binary relation of the
universe. -/
theorem memRelOn_spec {F : NonstandardFramework.{u}} (hT : IsSetOf F.U T) :
    IsSetOf F.U (memRelOn T) ∧ RelIn F.U (memRelOn T) :=
  ⟨F.hU.isSetOf_of_subset_prod hT (F.hU.isSetOf_powerset hT) sep_subset,
    F.hU.relIn_of_subset_prod hT (F.hU.isSetOf_powerset hT) sep_subset⟩

/-- **Transfer of membership.** The transform of the membership relation on $`T` is the
membership relation between members of $`{}^*T` and internal subsets of $`{}^*T`. -/
theorem pair_mem_star_memRelOn (hT : IsSetOf F.U T) :
    pair x S ∈ F.star (memRelOn T) ↔ x ∈ F.star T ∧ S ∈ F.star (powerset T) ∧ x ∈ S := by
  have hP := F.hU.isSetOf_powerset hT
  obtain ⟨hE, -⟩ := memRelOn_spec (F := F) hT
  have h := F.transfer
    (.all 0 (.const T) (.all 1 (.const (powerset T)) (.biimp
      (.elem (.opair (.var 0) (.var 1)) (.const (memRelOn T))) (.elem (.var 0) (.var 1)))))
    (by simp [Formula.IsSentence, hT.1, hP.1, hE.1])
  sat_simp at h
  have h' := h.1 (by
    intro u _ hu v _ hv
    rw [pair_mem_memRelOn]
    exact ⟨fun h => h.2.2, fun h => ⟨hu, mem_powerset.1 hv, h⟩⟩)
  have hTU := F.star_subset_U' hT
  have hPU := F.star_subset_U' hP
  constructor
  · intro hxS
    obtain ⟨hx, hS⟩ := pair_mem_prod.1 (F.star_subset_prod hT hP sep_subset hxS)
    exact ⟨hx, hS, (h' x (hTU hx) hx S (hPU hS) hS).1 hxS⟩
  · rintro ⟨hx, hS, hxS⟩
    exact (h' x (hTU hx) hx S (hPU hS) hS).2 hxS

/-!
## 15.4 Comprehensiveness

A sequence of real numbers extends to an internal hypersequence, its transform. A sequence
of _hyperreal_ numbers is not in the standard universe and has no transform, and the
question is whether it still extends to an internal function on $`{}^*\mathbb N`. A
framework in which every function from a standard set $`A` to an internal set $`B` extends
to an internal function from $`{}^*A` to $`B` is called comprehensive. The section shows
that the countable form of this property, together with the existence of an unlimited
hypernatural, is equivalent to countable saturation: every decreasing sequence of nonempty
internal sets has a common member.

An _internal set_ is an internal entity that is a set of the nonstandard universe, as
opposed to an individual of it. The function $`f : A \to B` to be extended is any set of
pairs; it need not belong to either universe.
-/

/-- **Section 15.4, internal sets.** An internal entity that is a set of the
nonstandard universe. -/
def InternalSet (A : ZFSet.{u}) : Prop := F.Internal A ∧ IsSetOf F.U' A

/-- **Section 15.4, comprehensive frameworks.** For every set $`A` of the standard
universe and every internal set $`B`, every function $`f : A \to B` extends to an internal
function $`{}^+f : {}^*A \to B`, in the sense that $`{}^+f({}^*a) = f(a)` for all
$`a \in A`. -/
def Comprehensive : Prop :=
  ∀ A B f, IsSetOf F.U A → F.InternalSet B → IsFunc A B f →
    ∃ g, F.Internal g ∧ IsFunc (F.star A) B g ∧ ∀ a ∈ A, app g (F.star a) = app f a

/-- **Section 15.4, countably comprehensive frameworks.** The condition defining
comprehensive frameworks, required only for countable sets $`A`. -/
def CountablyComprehensive : Prop :=
  ∀ A B f, IsSetOf F.U A → (A : Set ZFSet.{u}).Countable → F.InternalSet B → IsFunc A B f →
    ∃ g, F.Internal g ∧ IsFunc (F.star A) B g ∧ ∀ a ∈ A, app g (F.star a) = app f a

/-- **Theorem 15.4.2 (3), countable saturation.** Every decreasing sequence of nonempty
internal sets has nonempty intersection. -/
def CountablySaturated : Prop :=
  ∀ A : ℕ → ZFSet.{u}, (∀ n, F.InternalSet (A n)) → (∀ n, A (n + 1) ⊆ A n) →
    (∀ n, A n ≠ ∅) → ∃ x, ∀ n, x ∈ A n

variable {F}

/-- **Section 15.4.** A comprehensive framework is countably comprehensive. -/
theorem Comprehensive.countablyComprehensive (h : F.Comprehensive) :
    F.CountablyComprehensive := fun A B f hA _ hB hf => h A B f hA hB hf

/-- **Section 15.5 (cf. Corollary 11.10.2).** In a countably saturated framework, a
sequence of internal sets with the finite intersection property has nonempty intersection:
apply saturation to the decreasing sequence of the finite intersections. -/
theorem CountablySaturated.exists_mem_of_fip (hS : F.CountablySaturated) (A : ℕ → ZFSet.{u})
    (hA : ∀ n, F.InternalSet (A n)) (hfip : ∀ t : Finset ℕ, ∃ x, ∀ n ∈ t, x ∈ A n) :
    ∃ x, ∀ n, x ∈ A n := by
  have hDint : ∀ n, F.InternalSet (interUpTo A n) := by
    intro n
    induction n with
    | zero => exact hA 0
    | succ n ih =>
      exact ⟨F.internal_inter ih.1 ih.2 (hA _).1, F.isUniverse'.isSetOf_inter ih.2⟩
  obtain ⟨x, hx⟩ := hS (interUpTo A) hDint (fun n y hy => (mem_inter.1 hy).1) (fun n h0 => by
    obtain ⟨x, hx⟩ := hfip (Finset.range (n + 1))
    have : x ∈ interUpTo A n :=
      (mem_interUpTo A n).2 fun i hi => hx i (Finset.mem_range.2 (by omega))
    rw [h0] at this
    exact notMem_empty x this)
  exact ⟨x, fun n => (mem_interUpTo A n).1 (hx n) n le_rfl⟩

/-- **Theorem 15.4.2, (3) implies countable comprehensiveness.** Let $`A = \{a_n\}` be
countable and $`f : A \to B` with $`B` internal. The sets of the internal functions
$`g : {}^*A \to B` with $`g({}^*a_k) = f(a_k)`, for $`k \in \mathbb N`, are internal and
have the finite intersection property, because a value of an internal function can be
changed at one point. A common member is the required extension. This implication holds in
every framework. -/
theorem CountablySaturated.countablyComprehensive (hS : F.CountablySaturated) :
    F.CountablyComprehensive := by
  intro A B f hA hcount hB hf
  have hU' := F.isUniverse'
  by_cases hne : A = ∅
  · subst hne
    refine ⟨∅, ?_, ?_, fun a ha => absurd ha (notMem_empty a)⟩
    · have := F.internal_star F.hU.empty_mem
      rwa [F.star_empty] at this
    · rw [F.star_empty]
      exact ⟨empty_subset _, fun z hz => absurd hz (notMem_empty z)⟩
  have hAne : (A : Set ZFSet.{u}).Nonempty := by
    obtain ⟨y, hy⟩ := (eq_empty_or_nonempty A).resolve_left hne
    exact ⟨y, hy⟩
  obtain ⟨a, ha⟩ := hcount.exists_eq_range hAne
  have haA : ∀ k, a k ∈ A := fun k => by
    have : a k ∈ (A : Set ZFSet.{u}) := ha ▸ Set.mem_range_self k
    exact this
  have haU : ∀ k, a k ∈ F.U := fun k => F.hU.mem_of_mem hA (haA k)
  have hfa : ∀ k, app f (a k) ∈ B := fun k =>
    (pair_mem_prod.1 (hf.1 (hf.isFunction.pair_app_mem (hf.dom_eq.symm ▸ haA k)))).2
  obtain ⟨T, hT, -, hsub, -⟩ := F.exists_ambient [B] (by simp [hB.1])
  have hBT : B ⊆ F.star T := hsub B (by simp) hB.2
  have hATset : IsSetOf F.U (ZFSet.prod A T) := F.hU.isSetOf_prod hA hT
  have hstarAT : F.star (ZFSet.prod A T) = ZFSet.prod (F.star A) (F.star T) := F.star_prod hA hT
  obtain ⟨hEset, hErel⟩ := memRelOn_spec (F := F) hATset
  have hPint : F.Internal (ZFSet.prod (F.star A) B) :=
    F.internal_prod (F.internal_star hA.1) (F.isSetOf_star hA) hB.1 hB.2
  have hFnset : IsSetOf F.U (funs A T) := F.hU.isSetOf_funs hA hT
  obtain ⟨G, hGdef⟩ : ∃ G, G = F.star (funs A T) \
      relImage (F.star (memRelOn (ZFSet.prod A T)))
        (F.star (ZFSet.prod A T) \ ZFSet.prod (F.star A) B) := ⟨_, rfl⟩
  have hGint : F.Internal G := by
    rw [hGdef]
    exact F.internal_sdiff (F.internal_star hFnset.1) (F.isSetOf_star hFnset)
      (internal_relImage_star hEset hErel
        (F.internal_sdiff (F.internal_star hATset.1) (F.isSetOf_star hATset) hPint))
  have hGset : IsSetOf F.U' G := by
    rw [hGdef]
    exact hU'.isSetOf_sdiff (F.isSetOf_star hFnset)
  have hFnpow : ∀ g ∈ F.star (funs A T), g ∈ F.star (powerset (ZFSet.prod A T)) := fun g hg =>
    (F.star_subset_star_iff hFnset (F.hU.isSetOf_powerset hATset)).2
      (fun w hw => mem_powerset.2 (mem_funs.1 hw).1) hg
  have hGmem : ∀ g, g ∈ G ↔
      (IsFunc (F.star A) (F.star T) g ∧ F.Internal g) ∧ g ⊆ ZFSet.prod (F.star A) B := by
    intro g
    rw [hGdef, mem_sdiff]
    constructor
    · rintro ⟨hgFn, hnot⟩
      have hg := (F.mem_star_funs_iff hA hT).1 hgFn
      refine ⟨hg, fun p hp => ?_⟩
      by_contra hpP
      have hpAT : p ∈ F.star (ZFSet.prod A T) := hstarAT ▸ hg.1.1 hp
      exact hnot (mem_relImage.2 ⟨p, mem_sdiff.2 ⟨hpAT, hpP⟩,
        (F.pair_mem_star_memRelOn hATset).2 ⟨hpAT, hFnpow g hgFn, hp⟩⟩)
    · rintro ⟨hg, hgP⟩
      refine ⟨(F.mem_star_funs_iff hA hT).2 hg, fun hrel => ?_⟩
      obtain ⟨p, hp, hpg⟩ := mem_relImage.1 hrel
      exact (mem_sdiff.1 hp).2 (hgP ((F.pair_mem_star_memRelOn hATset).1 hpg).2.2)
  have hpinAT : ∀ k, pair (F.star (a k)) (app f (a k)) ∈ F.star (ZFSet.prod A T) := fun k =>
    hstarAT ▸ pair_mem_prod.2 ⟨(F.star_mem_star_iff (haU k) hA.1).2 (haA k), hBT (hfa k)⟩
  have hpinint : ∀ k, F.Internal (pair (F.star (a k)) (app f (a k))) := fun k =>
    F.internal_of_mem_star hATset (hpinAT k)
  have hSmem : ∀ k g, g ∈ G ∩ relImage (F.star (memRelOn (ZFSet.prod A T)))
      {pair (F.star (a k)) (app f (a k))} ↔ g ∈ G ∧ pair (F.star (a k)) (app f (a k)) ∈ g := by
    intro k g
    rw [mem_inter]
    refine and_congr_right fun hgG => ?_
    constructor
    · intro hrel
      obtain ⟨p, hp, hpg⟩ := mem_relImage.1 hrel
      rw [mem_singleton] at hp
      subst hp
      exact ((F.pair_mem_star_memRelOn hATset).1 hpg).2.2
    · intro hpg
      have hgFn : g ∈ F.star (funs A T) := (F.mem_star_funs_iff hA hT).2 ((hGmem g).1 hgG).1
      exact mem_relImage.2 ⟨_, mem_singleton.2 rfl,
        (F.pair_mem_star_memRelOn hATset).2 ⟨hpinAT k, hFnpow g hgFn, hpg⟩⟩
  have hfip : ∀ t : Finset ℕ, ∃ g, g ∈ G ∧ ∀ k ∈ t, pair (F.star (a k)) (app f (a k)) ∈ g := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      have hb0 : F.Internal (app f (a 0)) := F.internal_of_mem_internal_set hB.1 hB.2 (hfa 0)
      refine ⟨ZFSet.prod (F.star A) {app f (a 0)}, (hGmem _).2 ⟨⟨⟨fun p hp => ?_,
        fun z hz => ⟨app f (a 0), pair_mem_prod.2 ⟨hz, mem_singleton.2 rfl⟩,
          fun w hw => mem_singleton.1 (pair_mem_prod.1 hw).2⟩⟩, ?_⟩, fun p hp => ?_⟩, by simp⟩
      · obtain ⟨u, hu, v, hv, rfl⟩ := mem_prod.1 hp
        rw [mem_singleton] at hv
        subst hv
        exact pair_mem_prod.2 ⟨hu, hBT (hfa 0)⟩
      · exact F.internal_prod (F.internal_star hA.1) (F.isSetOf_star hA)
          (F.internal_singleton hb0) (hU'.isSetOf_singleton hb0.mem_U')
      · obtain ⟨u, hu, v, hv, rfl⟩ := mem_prod.1 hp
        rw [mem_singleton] at hv
        subst hv
        exact pair_mem_prod.2 ⟨hu, hfa 0⟩
    | insert k t _ ih =>
      obtain ⟨g, hg, hpins⟩ := ih
      obtain ⟨⟨hgf, hgint⟩, hgP⟩ := (hGmem g).1 hg
      have hgset : IsSetOf F.U' g :=
        hU'.isSetOf_of_subset_prod (F.isSetOf_star hA) (F.isSetOf_star hT) hgf.1
      have hakint : F.Internal (F.star (a k)) := F.internal_star (haU k)
      have hx : F.star (a k) ∈ F.star A := (F.star_mem_star_iff (haU k) hA.1).2 (haA k)
      refine ⟨(g \ ZFSet.prod {F.star (a k)} (F.star T)) ∪ {pair (F.star (a k)) (app f (a k))},
        (hGmem _).2 ⟨⟨isFunc_update hgf hx (hBT (hfa k)), ?_⟩, fun p hp => ?_⟩, fun j hj => ?_⟩
      · exact F.internal_union
          (F.internal_sdiff hgint hgset (F.internal_prod (F.internal_singleton hakint)
            (hU'.isSetOf_singleton hakint.mem_U') (F.internal_star hT.1) (F.isSetOf_star hT)))
          (hU'.isSetOf_sdiff hgset) (F.internal_singleton (hpinint k))
          (hU'.isSetOf_singleton (hpinint k).mem_U')
      · rcases mem_union.1 hp with h | h
        · exact hgP (mem_sdiff.1 h).1
        · rw [mem_singleton.1 h]
          exact pair_mem_prod.2 ⟨hx, hfa k⟩
      · rcases Finset.mem_insert.1 hj with rfl | hjt
        · exact mem_union.2 (Or.inr (mem_singleton.2 rfl))
        · by_cases e : F.star (a j) = F.star (a k)
          · have e' : a j = a k := (F.star_eq_iff (haU j) (haU k)).1 e
            rw [e']
            exact mem_union.2 (Or.inr (mem_singleton.2 rfl))
          · exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨hpins j hjt, fun h =>
              e (mem_singleton.1 (pair_mem_prod.1 h).1)⟩))
  obtain ⟨g, hg⟩ := hS.exists_mem_of_fip
    (fun k => G ∩ relImage (F.star (memRelOn (ZFSet.prod A T)))
      {pair (F.star (a k)) (app f (a k))})
    (fun k => ⟨F.internal_inter hGint hGset (internal_relImage_star hEset hErel
      (F.internal_singleton (hpinint k))), hU'.isSetOf_inter hGset⟩)
    (fun t => by
      obtain ⟨g, hg, hp⟩ := hfip t
      exact ⟨g, fun k hk => (hSmem k g).2 ⟨hg, hp k hk⟩⟩)
  obtain ⟨⟨hgf, hgint⟩, hgP⟩ := (hGmem g).1 ((hSmem 0 g).1 (hg 0)).1
  refine ⟨g, hgint, ⟨hgP, hgf.2⟩, fun a' ha' => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, a k = a' := by
    have : a' ∈ Set.range a := ha ▸ ha'
    exact this
  exact hgf.isFunction.app_eq ((hSmem k g).1 (hg k)).2

end NonstandardFramework

namespace RealFramework

variable (F : RealFramework.{u}) {A B X K f g s x : ZFSet.{u}}

/-- **Section 15.4, sequentially comprehensive frameworks.** The condition defining
comprehensive frameworks, required only for $`A = \mathbb N`: every sequence
$`\mathbb N \to B` of members of an internal set $`B` extends to an internal hypersequence
$`{}^*\mathbb N \to B`. Since $`{}^*n = n` for $`n \in \mathbb N`, the extension agrees with
the sequence on $`\mathbb N`. -/
def SequentiallyComprehensive : Prop :=
  ∀ B f, F.InternalSet B → IsFunc F.N B f →
    ∃ g, F.Internal g ∧ IsFunc (F.star F.N) B g ∧ ∀ n : ℕ, app g (F.nat n) = app f (F.nat n)

variable {F}

/-- $`\mathbb N` is countable. -/
theorem countable_N (F : RealFramework.{u}) : (F.N : Set ZFSet.{u}).Countable := by
  have : (F.N : Set ZFSet.{u}) = Set.range F.nat := by
    ext y
    exact F.mem_N.trans ⟨fun ⟨k, h⟩ => ⟨k, h.symm⟩, fun ⟨k, h⟩ => ⟨k, h.symm⟩⟩
  rw [this]
  exact Set.countable_range _

/-- **Theorem 15.4.2, (1) implies (2).** A countably comprehensive framework is
sequentially comprehensive, as $`\mathbb N` is countable. -/
theorem sequentiallyComprehensive_of_countablyComprehensive (h : F.CountablyComprehensive) :
    F.SequentiallyComprehensive := fun B f hB hf => by
  obtain ⟨g, hg, hgf, hgval⟩ := h F.N B f F.isSetOf_N F.countable_N hB hf
  refine ⟨g, hg, hgf, fun n => ?_⟩
  have := hgval (F.nat n) (F.mem_N.2 ⟨n, rfl⟩)
  rwa [F.star_nat] at this

/-- **Section 15.4.** In a sequentially comprehensive framework every sequence
$`(s_n : n \in \mathbb N)` of members of an internal set $`B` extends to an internal
hypersequence $`(s_n : n \in {}^*\mathbb N)` of members of $`B`. The sequence is given here
as a function on Lean's natural numbers. -/
theorem SequentiallyComprehensive.exists_seq (h : F.SequentiallyComprehensive)
    (hB : F.InternalSet B) (s : ℕ → ZFSet.{u}) (hs : ∀ n, s n ∈ B) :
    ∃ g, F.Internal g ∧ IsFunc (F.star F.N) B g ∧ ∀ n : ℕ, app g (F.nat n) = s n := by
  set f := ZFSet.range (fun n : ℕ => pair (F.nat n) (s n)) with hf
  have hmem : ∀ {p}, p ∈ f ↔ ∃ n : ℕ, p = pair (F.nat n) (s n) := fun {p} => by
    rw [hf, mem_range]
    exact ⟨fun ⟨n, h⟩ => ⟨n, h.symm⟩, fun ⟨n, h⟩ => ⟨n, h.symm⟩⟩
  have hfunc : IsFunc F.N B f := by
    refine ⟨fun p hp => ?_, fun z hz => ?_⟩
    · obtain ⟨n, rfl⟩ := hmem.1 hp
      exact pair_mem_prod.2 ⟨F.mem_N.2 ⟨n, rfl⟩, hs n⟩
    · obtain ⟨n, rfl⟩ := F.mem_N.1 hz
      refine ⟨s n, hmem.2 ⟨n, rfl⟩, fun w hw => ?_⟩
      obtain ⟨m, hm⟩ := hmem.1 hw
      obtain ⟨h1, h2⟩ := pair_inj.1 hm
      rw [h2, F.nat_injective h1]
  obtain ⟨g, hg, hgf, hgval⟩ := h B f hB hfunc
  refine ⟨g, hg, hgf, fun n => ?_⟩
  rw [hgval n]
  exact hfunc.isFunction.app_eq (hmem.2 ⟨n, rfl⟩)

/-- **Theorem 15.4.2, (2) implies (3).** A sequentially comprehensive framework with an
unlimited hypernatural is countably saturated. Given a decreasing sequence
$`(A_n : n \in \mathbb N)` of nonempty internal sets, all subsets of a standard set
$`{}^*T`, extend it to an internal hypersequence $`(A_n : n \in {}^*\mathbb N)` of members of
$`{}^*\mathcal P(T)`. The internal set of the $`k \in {}^*\mathbb N` for which some
$`x` belongs to $`A_n` for all $`n \le k` contains every standard $`k`, hence an unlimited
one, and the corresponding $`x` belongs to every $`A_n` with $`n` standard. (The book
applies overflow to the property that $`A_k` is nonempty and included in $`A_n` for all
$`n \le k`; the variant used here needs only the transform of the membership relation.) -/
theorem SequentiallyComprehensive.countablySaturated (hSC : F.SequentiallyComprehensive)
    (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) : F.CountablySaturated := by
  intro A hA hdec hne
  have hU' := F.isUniverse'
  have hanti : ∀ j k, j ≤ k → A k ⊆ A j := fun j k hjk => by
    induction hjk with
    | refl => exact fun _ h => h
    | step _ ih => exact fun y hy => ih (hdec _ hy)
  obtain ⟨T, hT, -, hTr', hA0T⟩ := F.exists_transitive_of_internal (hA 0).1
  have hA0sub : A 0 ⊆ F.star T := fun z hz =>
    hTr' _ hA0T z hz (hU'.mem_of_mem (hA 0).2 hz)
  have hPT := F.hU.isSetOf_powerset hT
  have hAB : ∀ n, A n ∈ F.star (powerset T) := fun n =>
    (F.mem_star_powerset_iff hT).2 ⟨fun z hz => hA0sub (hanti 0 n (Nat.zero_le n) hz), (hA n).1⟩
  obtain ⟨g, hgint, hgf, hgval⟩ :=
    hSC.exists_seq ⟨F.internal_star hPT.1, F.isSetOf_star hPT⟩ A hAB
  obtain ⟨hgset, hgrel, hgfun, hgdom⟩ := isFunc_spec F.star_N_spec.2 (F.isSetOf_star hPT) hgf
  obtain ⟨hEset, hErel⟩ := memRelOn_spec (F := F.toNonstandardFramework) hT
  obtain ⟨hEint, hEset', hErel'⟩ := star_rel_spec hEset hErel
  obtain ⟨hLint, hLset, hLrel⟩ := star_rel_spec F.isSetOf_Le F.relIn_Le
  obtain ⟨hNint, hNset⟩ := F.star_N_spec
  have hTint := F.internal_star hT.1
  have hTset := F.isSetOf_star hT
  have hNTint : F.Internal (ZFSet.prod (F.star F.N) (F.star T)) :=
    F.internal_prod hNint hNset hTint hTset
  have hNTset : IsSetOf F.U' (ZFSet.prod (F.star F.N) (F.star T)) := hU'.isSetOf_prod hNset hTset
  obtain ⟨NotIn, hNotIndef⟩ : ∃ N', N' = ZFSet.prod (F.star F.N) (F.star T) \
      relComp g (relInv (F.star (memRelOn T))) := ⟨_, rfl⟩
  have hNotInint : F.Internal NotIn := by
    rw [hNotIndef]
    exact F.internal_sdiff hNTint hNTset (F.internal_relComp hgint hgset hgrel
      (F.internal_relInv hEint hEset' hErel') (hU'.isSetOf_relInv hEset' hErel') hErel'.relInv)
  have hNotInset : IsSetOf F.U' NotIn := by
    rw [hNotIndef]
    exact hU'.isSetOf_sdiff hNTset
  have hNotInrel : RelIn F.U' NotIn := by
    rw [hNotIndef]
    exact hU'.relIn_of_subset_prod hNset hTset fun p hp => (mem_sdiff.1 hp).1
  have hNotIn : ∀ {n x : ZFSet.{u}}, pair n x ∈ NotIn ↔
      n ∈ F.star F.N ∧ x ∈ F.star T ∧ pair x (app g n) ∉ F.star (memRelOn T) := by
    intro n x
    rw [hNotIndef, mem_sdiff, pair_mem_prod, pair_mem_relComp, and_assoc]
    refine and_congr_right fun hn => and_congr_right fun _ => not_congr ?_
    constructor
    · rintro ⟨S, hnS, hSx⟩
      rw [hgfun.app_eq hnS]
      exact pair_mem_relInv.1 hSx
    · intro h
      exact ⟨app g n, hgfun.pair_app_mem (hgdom.symm ▸ hn), pair_mem_relInv.2 h⟩
  have hYint : F.Internal (dom (ZFSet.prod (F.star F.N) (F.star T) \
      relComp (relInv (F.star F.Le)) NotIn)) :=
    F.internal_dom (F.internal_sdiff hNTint hNTset
      (F.internal_relComp (F.internal_relInv hLint hLset hLrel) (hU'.isSetOf_relInv hLset hLrel)
        hLrel.relInv hNotInint hNotInset hNotInrel))
      (hU'.isSetOf_sdiff hNTset)
      (hU'.relIn_of_subset_prod hNset hTset fun p hp => (mem_sdiff.1 hp).1)
  obtain ⟨K, hK, hKN, hKY⟩ := exists_nonstandard_mem hω hYint (by
    intro m hm
    obtain ⟨k, rfl⟩ := F.mem_N.1 hm
    obtain ⟨x, hx⟩ := (eq_empty_or_nonempty (A k)).resolve_left (hne k)
    have hxT : x ∈ F.star T := hA0sub (hanti 0 k (Nat.zero_le k) hx)
    refine mem_dom.2 ⟨x, mem_sdiff.2 ⟨pair_mem_prod.2 ⟨F.N_subset_star hm, hxT⟩,
      fun hbad => ?_⟩⟩
    obtain ⟨n, hkn, hnx⟩ := pair_mem_relComp.1 hbad
    have hnk := pair_mem_relInv.1 hkn
    obtain ⟨hnN, -, hnot⟩ := hNotIn.1 hnx
    obtain ⟨j, rfl⟩ := F.mem_N.1 (mem_N_of_le_nat hnN hnk)
    have hjk := F.pair_nat_mem_star_Le.1 hnk
    rw [hgval j] at hnot
    exact hnot ((F.pair_mem_star_memRelOn hT).2 ⟨hxT, hAB j, hanti j k hjk hx⟩))
  obtain ⟨x, hx⟩ := mem_dom.1 hKY
  obtain ⟨hKx, hnbad⟩ := mem_sdiff.1 hx
  have hxT := (pair_mem_prod.1 hKx).2
  refine ⟨x, fun n => ?_⟩
  by_contra hxn
  refine hnbad (pair_mem_relComp.2 ⟨F.nat n,
    pair_mem_relInv.2 (F.nat_le_of_nonstandard hK hKN n),
    hNotIn.2 ⟨F.N_subset_star (F.mem_N.2 ⟨n, rfl⟩), hxT, fun h => ?_⟩⟩)
  rw [hgval n] at h
  exact hxn ((F.pair_mem_star_memRelOn hT).1 h).2.2

/-- **Theorem 15.4.2, (3) implies the existence of an unlimited hypernatural.** The sets
$`\{k \in {}^*\mathbb N : n \le k\}`, for $`n \in \mathbb N`, are standard, hence internal,
nonempty and decreasing; a common member is a hypernatural greater than every standard
natural number. -/
theorem exists_nonstandard_nat_of_countablySaturated (hS : F.CountablySaturated) :
    ∃ n, n ∈ F.star F.N ∧ n ∉ F.N := by
  have hsub : ∀ n : ℕ, (F.N.sep fun y => pair (F.nat n) y ∈ F.Le) ⊆ F.N := fun n => sep_subset
  have hset : ∀ n : ℕ, IsSetOf F.U (F.N.sep fun y => pair (F.nat n) y ∈ F.Le) := fun n =>
    F.hU.isSetOf_of_subset F.isSetOf_N (hsub n)
  obtain ⟨x, hx⟩ := hS (fun n => F.star (F.N.sep fun y => pair (F.nat n) y ∈ F.Le))
    (fun n => ⟨F.internal_star (hset n).1, F.isSetOf_star (hset n)⟩)
    (fun n => (F.star_subset_star_iff (hset (n + 1)) (hset n)).2 fun y hy => by
      obtain ⟨hyN, hy⟩ := mem_sep.1 hy
      obtain ⟨j, rfl⟩ := F.mem_N.1 hyN
      exact mem_sep.2 ⟨hyN, F.pair_nat_mem_Le.2 (by have := F.pair_nat_mem_Le.1 hy; omega)⟩)
    (fun n h0 => by
      have : F.nat n ∈ F.star (F.N.sep fun y => pair (F.nat n) y ∈ F.Le) := by
        have := (F.star_mem_star_iff (F.nat_mem_U n) (hset n).1).2
          (mem_sep.2 ⟨F.mem_N.2 ⟨n, rfl⟩, F.pair_nat_mem_Le.2 le_rfl⟩)
        rwa [F.star_nat] at this
      rw [h0] at this
      exact notMem_empty _ this)
  refine ⟨x, (F.star_subset_star_iff (hset 0) F.isSetOf_N).2 (hsub 0) (hx 0), fun hxN => ?_⟩
  obtain ⟨j, rfl⟩ := F.mem_N.1 hxN
  have := hx (j + 1)
  rw [← F.star_nat j, F.star_mem_star_iff (F.nat_mem_U j) (hset (j + 1)).1] at this
  have := F.pair_nat_mem_Le.1 (mem_sep.1 this).2
  omega

/-- **Theorem 15.4.2.** For a framework over the real numbers the following are
equivalent: (1) it is countably comprehensive and has an unlimited hypernatural; (2) it is
sequentially comprehensive and has an unlimited hypernatural; (3) it is countably saturated:
every decreasing sequence of nonempty internal sets has nonempty intersection. -/
theorem countablySaturated_tfae (F : RealFramework.{u}) :
    List.TFAE [F.CountablyComprehensive ∧ ∃ n, n ∈ F.star F.N ∧ n ∉ F.N,
      F.SequentiallyComprehensive ∧ ∃ n, n ∈ F.star F.N ∧ n ∉ F.N,
      F.CountablySaturated] := by
  tfae_have 1 → 2 := fun h => ⟨sequentiallyComprehensive_of_countablyComprehensive h.1, h.2⟩
  tfae_have 2 → 3 := fun h => h.1.countablySaturated h.2
  tfae_have 3 → 1 := fun h =>
    ⟨h.countablyComprehensive, exists_nonstandard_nat_of_countablySaturated h⟩
  tfae_finish

/-- **Theorem 15.4.2 and the remark after it.** A comprehensive framework with an
unlimited hypernatural is countably saturated. -/
theorem countablySaturated_of_comprehensive (hC : F.Comprehensive)
    (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) : F.CountablySaturated :=
  (sequentiallyComprehensive_of_countablyComprehensive
    hC.countablyComprehensive).countablySaturated hω

/-- **Theorem 15.4.3, for sequences.** In a sequentially comprehensive framework with an
unlimited hypernatural, for every sequence $`(s_n : n \in \mathbb N)` of unlimited
hypernaturals there is an unlimited hypernatural $`K` less than every $`s_n`. This is
Robinson's proof: extend the sequence to an internal hypersequence and apply overflow to the
internal set of the $`k` with $`k < s_n` for all $`n \le k`. -/
theorem exists_unlimited_lt_seq (hSC : F.SequentiallyComprehensive)
    (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (s : ℕ → ZFSet.{u})
    (hs : ∀ n, s n ∈ F.star F.N ∧ s n ∉ F.N) :
    ∃ K, K ∈ F.star F.N ∧ K ∉ F.N ∧ ∀ n, F.Lt K (s n) := by
  have hU' := F.isUniverse'
  obtain ⟨hNint, hNset⟩ := F.star_N_spec
  obtain ⟨hLint, hLset, hLrel⟩ := star_rel_spec F.isSetOf_Le F.relIn_Le
  obtain ⟨g, hgint, hgf, hgval⟩ := hSC.exists_seq F.star_N_spec s fun n => (hs n).1
  obtain ⟨hgset, hgrel, hgfun, hgdom⟩ := isFunc_spec hNset hNset hgf
  have hCint : F.Internal (F.star F.Le ∩ relComp g (F.star F.Le)) :=
    F.internal_inter hLint hLset (F.internal_relComp hgint hgset hgrel hLint hLset hLrel)
  have hYint : F.Internal (F.star F.N \ ran (F.star F.Le ∩ relComp g (F.star F.Le))) :=
    F.internal_sdiff hNint hNset (F.internal_ran hCint (hU'.isSetOf_inter hLset)
      fun p hp => hLrel p (mem_inter.1 hp).1)
  obtain ⟨K, hK, hKN, hKY⟩ := exists_nonstandard_mem hω hYint (by
    intro m hm
    obtain ⟨k, rfl⟩ := F.mem_N.1 hm
    refine mem_sdiff.2 ⟨F.N_subset_star hm, fun hran => ?_⟩
    obtain ⟨n, hn⟩ := mem_ran.1 hran
    obtain ⟨hnk, hcomp⟩ := mem_inter.1 hn
    obtain ⟨w, hnw, hwk⟩ := pair_mem_relComp.1 hcomp
    have hnN : n ∈ F.star F.N := (pair_mem_prod.1 (hgf.1 hnw)).1
    obtain ⟨j, rfl⟩ := F.mem_N.1 (mem_N_of_le_nat hnN hnk)
    rw [← hgfun.app_eq hnw, hgval j] at hwk
    exact (hs j).2 (mem_N_of_le_nat (hs j).1 hwk))
  refine ⟨K, hK, hKN, fun n => ?_⟩
  rcases lt_or_le (F.star_N_subset_star_R hK) (F.star_N_subset_star_R (hs n).1) with h | h
  · exact h
  · exfalso
    refine (mem_sdiff.1 hKY).2 (mem_ran.2 ⟨F.nat n, mem_inter.2
      ⟨F.nat_le_of_nonstandard hK hKN n, pair_mem_relComp.2 ⟨s n, ?_, h⟩⟩⟩)
    have := hgfun.pair_app_mem (hgdom.symm ▸ F.N_subset_star (F.mem_N.2 ⟨n, rfl⟩))
    rwa [hgval n] at this

/-- **Theorem 15.4.3.** In a sequentially comprehensive framework with an unlimited
hypernatural (in particular in a sequentially comprehensive enlargement), if $`X` is any
countable set of unlimited hypernaturals, then there is an unlimited hypernatural $`K` less
than every member of $`X`. -/
theorem exists_unlimited_lt_of_countable (hSC : F.SequentiallyComprehensive)
    (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N) (X : Set ZFSet.{u}) (hX : X.Countable)
    (h : ∀ x ∈ X, x ∈ F.star F.N ∧ x ∉ F.N) :
    ∃ K, K ∈ F.star F.N ∧ K ∉ F.N ∧ ∀ x ∈ X, F.Lt K x := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨K, hK, hKN⟩ := hω
    exact ⟨K, hK, hKN, fun x hx => absurd hx (Set.notMem_empty x)⟩
  · obtain ⟨s, rfl⟩ := hX.exists_eq_range hne
    obtain ⟨K, hK, hKN, hlt⟩ := exists_unlimited_lt_seq hSC hω s fun n => h _ ⟨n, rfl⟩
    exact ⟨K, hK, hKN, by rintro _ ⟨n, rfl⟩; exact hlt n⟩

/-- **Theorem 15.4.3, as stated in the book.** In a sequentially comprehensive
enlargement, every countable set of unlimited hypernaturals has an unlimited hypernatural
below all its members. -/
theorem exists_unlimited_lt_of_countable_of_isEnlargement (hSC : F.SequentiallyComprehensive)
    (hE : F.IsEnlargement) (X : Set ZFSet.{u}) (hX : X.Countable)
    (h : ∀ x ∈ X, x ∈ F.star F.N ∧ x ∉ F.N) :
    ∃ K, K ∈ F.star F.N ∧ K ∉ F.N ∧ ∀ x ∈ X, F.Lt K x :=
  exists_unlimited_lt_of_countable hSC (exists_nonstandard_nat hE) X hX h

end RealFramework

end Goldblatt
