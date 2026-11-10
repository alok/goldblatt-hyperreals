import Goldblatt.Ch15_Saturation.Uniform

/-!
# 15 (part 5). Comprehensiveness and countable saturation: Section 15.4

This is the fifth of seven parts of Chapter 15 (the overview is on the chapter page
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
theorem relIn_relInv (h : RelIn U R) : RelIn U (relInv R) := fun p hp => by
  obtain ⟨u, v, rfl, huv⟩ := mem_relInv.1 hp
  obtain ⟨u', hu', v', hv', huv'⟩ := h _ huv
  obtain ⟨rfl, rfl⟩ := pair_inj.1 huv'
  exact ⟨v, hv', u, hu', rfl⟩

/-- **Changing one value of a function.** If $`g : X \to Y`, $`x \in X` and $`y \in Y`,
then removing from $`g` the pair with first component $`x` and adding $`(x, y)` gives a
function from $`X` to $`Y`. -/
private theorem isFunc_update (hg : IsFunc X Y g) (hx : x ∈ X) (hy : y ∈ Y) :
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

/-- The values of a function from $`A` to $`B` belong to $`B`. -/
theorem app_mem_of_isFunc {A B f a : ZFSet.{u}} (hf : IsFunc A B f) (ha : a ∈ A) :
    app f a ∈ B :=
  (pair_mem_prod.1 (hf.1 (hf.isFunction.pair_app_mem (hf.dom_eq.symm ▸ ha)))).2

/-- **The membership relation on a set.** The set of pairs $`(x, S)` with $`x \in S` and
$`S \subseteq T`. Its transform lets membership in a variable internal subset of $`{}^*T`
be handled with the operations on relations. It is not the relation
{name}`Goldblatt.memRel` of Chapter 14, which relates a point only to the _finite_ subsets
that contain it; here $`S` ranges over all subsets of $`T`. -/
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
private def interUpTo (A : ℕ → ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => A 0
  | n + 1 => interUpTo A n ∩ A (n + 1)

/-- The members of a finite intersection of an initial part of a sequence of sets. -/
private theorem mem_interUpTo (A : ℕ → ZFSet.{u}) (n : ℕ) :
    x ∈ interUpTo A n ↔ ∀ i ≤ n, x ∈ A i := by
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

/-- **Theorem 15.4.2 (3), countable saturation.** The framework is countably saturated
when a chain $`A_0 \supseteq A_1 \supseteq \cdots` of internal sets, indexed by the standard
natural numbers and with no $`A_n` empty, always has a point common to all the $`A_n`. The
chain is a Lean sequence {lit}`A : ℕ → ZFSet`; it is not assumed to be internal. -/
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
      (F.internal_relInv hEint hEset' hErel') (hU'.isSetOf_relInv hEset' hErel')
      (relIn_relInv hErel'))
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
        (relIn_relInv hLrel) hNotInint hNotInset hNotInrel))
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
sequentially comprehensive and has an unlimited hypernatural; (3) it is countably saturated
({name}`Goldblatt.NonstandardFramework.CountablySaturated`). -/
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

/-- **Theorem 15.4.3.** Countably many unlimited hypernaturals cannot be coinitial in the
unlimited ones. Let the framework be sequentially comprehensive and possess an unlimited
hypernatural, and let $`X` be a countable set (a Lean {name}`Set.Countable` set of
entities) each of whose members is an unlimited hypernatural. Then a single unlimited
hypernatural $`K` satisfies $`K < x` for all $`x \in X`. The book assumes an enlargement;
only the existence of one unlimited hypernatural is used, and the version with the book's
hypothesis is {lit}`exists_unlimited_lt_of_countable_of_isEnlargement`. -/
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

/-- **Theorem 15.4.3, with the book's hypothesis.** The framework is assumed to be an
enlargement and sequentially comprehensive. Given a countable set $`X` whose members are
unlimited hypernaturals, there is an unlimited hypernatural $`K` with $`K < x` for each
$`x \in X`. An enlargement has an unlimited hypernatural, so this is a case of
{name}`Goldblatt.RealFramework.exists_unlimited_lt_of_countable`. -/
theorem exists_unlimited_lt_of_countable_of_isEnlargement (hSC : F.SequentiallyComprehensive)
    (hE : F.IsEnlargement) (X : Set ZFSet.{u}) (hX : X.Countable)
    (h : ∀ x ∈ X, x ∈ F.star F.N ∧ x ∉ F.N) :
    ∃ K, K ∈ F.star F.N ∧ K ∉ F.N ∧ ∀ x ∈ X, F.Lt K x :=
  exists_unlimited_lt_of_countable hSC (exists_nonstandard_nat hE) X hX h

/-!
### A second proof by Robinson's sequential lemma

The book gives another proof of Theorem 15.4.3 from Robinson's sequential lemma. For an
internal hypersequence $`s` let $`\underline s_n = \min\{s_m : m \le n\}`. The hypersequence
$`\underline s` is internal and decreasing. If $`s_n` is an unlimited hypernatural for all
standard $`n`, then so is $`\underline s_n`, its reciprocal is infinitesimal, and by
Robinson's lemma the reciprocal of $`\underline s_K` is infinitesimal for some unlimited
$`K`. Then $`\underline s_K` is unlimited and at most $`s_n` for every $`n \le K`, in
particular for every standard $`n`.
-/

/-- **Exercise 15.4.4, first part.** For an internal hypersequence
$`s : {}^*\mathbb N \to {}^*\mathbb R`, the hypersequence
$`\underline s_n = \min\{s_m : m \le n\}` is internal: there is an internal
$`t : {}^*\mathbb N \to {}^*\mathbb R` such that, for every hypernatural $`n`, $`t_n` is
$`s_m` for some $`m \le n` and $`t_n \le s_m` for all $`m \le n`. This is the transfer of
the corresponding statement for sequences of real numbers. -/
theorem exists_internal_running_min (hs : F.Internal s)
    (hsf : IsFunc (F.star F.N) (F.star F.R) s) :
    ∃ t, F.Internal t ∧ IsFunc (F.star F.N) (F.star F.R) t ∧ ∀ n ∈ F.star F.N,
      (∃ m ∈ F.star F.N, pair m n ∈ F.star F.Le ∧ app t n = app s m) ∧
      ∀ m ∈ F.star F.N, pair m n ∈ F.star F.Le → pair (app t n) (app s m) ∈ F.star F.Le := by
  have hFN := F.hU.isSetOf_funs F.isSetOf_N F.isSetOf_R
  have h := F.transfer
    (.all 0 (.const (funs F.N F.R)) (.ex 1 (.const (funs F.N F.R)) (.all 2 (.const F.N) (.conj
      (.ex 3 (.const F.N) (.conj (.elem (.opair (.var 3) (.var 2)) (.const F.Le))
        (.ex 4 (.const F.R) (.conj (.elem (.opair (.var 2) (.var 4)) (.var 1))
          (.elem (.opair (.var 3) (.var 4)) (.var 0))))))
      (.all 3 (.const F.N) (.imp (.elem (.opair (.var 3) (.var 2)) (.const F.Le))
        (.all 4 (.const F.R) (.all 5 (.const F.R) (.imp
          (.conj (.elem (.opair (.var 2) (.var 4)) (.var 1))
            (.elem (.opair (.var 3) (.var 5)) (.var 0)))
          (.elem (.opair (.var 4) (.var 5)) (.const F.Le)))))))))))
    (by simp [Formula.IsSentence, hFN.1, F.isSetOf_N.1, F.isSetOf_R.1, F.isSetOf_Le.1])
  sat_simp at h
  have h' := h.1 (by
    intro σ _ hσ
    have hσf : IsFunc F.N F.R σ := mem_funs.1 hσ
    have hσN : ∀ k : ℕ, F.nat k ∈ F.N := fun k => F.mem_N.2 ⟨k, rfl⟩
    have hval : ∀ k : ℕ, app σ (F.nat k) = F.real (F.toReal (app σ (F.nat k))) := fun k => by
      obtain ⟨r, hr⟩ := F.mem_R.1 (app_mem_of_isFunc hσf (hσN k))
      rw [hr, F.toReal_real]
    have hσmem : ∀ k : ℕ, pair (F.nat k) (F.real (F.toReal (app σ (F.nat k)))) ∈ σ := fun k => by
      rw [← hval k]
      exact hσf.isFunction.pair_app_mem (hσf.dom_eq.symm ▸ hσN k)
    set val : ℕ → ℝ := fun k => F.toReal (app σ (F.nat k)) with hvaldef
    set τ : ℕ → ℝ := fun k =>
      (Finset.range (k + 1)).inf' ⟨0, Finset.mem_range.2 (Nat.succ_pos k)⟩ val with hτ
    set T := ZFSet.range (fun k : ℕ => pair (F.nat k) (F.real (τ k))) with hT
    have hmem : ∀ {p}, p ∈ T ↔ ∃ k : ℕ, p = pair (F.nat k) (F.real (τ k)) := fun {p} => by
      rw [hT, mem_range]
      exact ⟨fun ⟨n, h⟩ => ⟨n, h.symm⟩, fun ⟨n, h⟩ => ⟨n, h.symm⟩⟩
    have hTf : IsFunc F.N F.R T := by
      refine ⟨fun p hp => ?_, fun z hz => ?_⟩
      · obtain ⟨k, rfl⟩ := hmem.1 hp
        exact pair_mem_prod.2 ⟨hσN k, F.mem_R.2 ⟨_, rfl⟩⟩
      · obtain ⟨k, rfl⟩ := F.mem_N.1 hz
        refine ⟨F.real (τ k), hmem.2 ⟨k, rfl⟩, fun w hw => ?_⟩
        obtain ⟨j, hj⟩ := hmem.1 hw
        obtain ⟨h1, h2⟩ := pair_inj.1 hj
        rw [h2, F.nat_injective h1]
    refine ⟨T, (F.hU.isSetOf_of_isFunc F.isSetOf_N F.isSetOf_R hTf).1, mem_funs.2 hTf, ?_⟩
    intro n _ hn
    obtain ⟨k, rfl⟩ := F.mem_N.1 hn
    constructor
    · obtain ⟨m, hm, hmin⟩ := Finset.exists_mem_eq_inf' (H := ⟨0, Finset.mem_range.2
        (Nat.succ_pos k)⟩) val
      refine ⟨F.nat m, F.nat_mem_U m, hσN m,
        F.pair_nat_mem_Le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)),
        F.real (τ k), F.real_mem_U _, F.mem_R.2 ⟨_, rfl⟩, hmem.2 ⟨k, rfl⟩, ?_⟩
      have : τ k = val m := hmin
      rw [this]
      exact hσmem m
    · intro m' _ hm' hle y _ _ z _ _ hyz
      obtain ⟨m, rfl⟩ := F.mem_N.1 hm'
      have hmk := F.pair_nat_mem_Le.1 hle
      have hy : y = F.real (τ k) := hTf.isFunction.2 _ _ _ hyz.1 (hmem.2 ⟨k, rfl⟩)
      have hz : z = F.real (val m) := hσf.isFunction.2 _ _ _ hyz.2 (hσmem m)
      rw [hy, hz, F.pair_mem_Le]
      exact Finset.inf'_le val (Finset.mem_range.2 (Nat.lt_succ_of_le hmk)))
  have hNU := F.star_subset_U' F.isSetOf_N
  have hRU := F.star_subset_U' F.isSetOf_R
  obtain ⟨t, -, htFN, ht⟩ := h' s hs.mem_U' ((F.mem_star_funs_iff F.isSetOf_N F.isSetOf_R).2
    ⟨hsf, hs⟩)
  obtain ⟨htf, htint⟩ := (F.mem_star_funs_iff F.isSetOf_N F.isSetOf_R).1 htFN
  refine ⟨t, htint, htf, fun n hn => ?_⟩
  obtain ⟨⟨m, -, hm, hmn, y, -, -, hny, hmy⟩, hall⟩ := ht n (hNU hn) hn
  refine ⟨⟨m, hm, hmn, ?_⟩, fun m' hm' hm'n => ?_⟩
  · rw [htf.isFunction.app_eq hny, hsf.isFunction.app_eq hmy]
  · have h1 := htf.isFunction.pair_app_mem (htf.dom_eq.symm ▸ hn)
    have h2 := hsf.isFunction.pair_app_mem (hsf.dom_eq.symm ▸ hm')
    exact hall m' (hNU hm') hm' hm'n _ (hRU (app_mem_of_isFunc htf hn)) (app_mem_of_isFunc htf hn) _
      (hRU (app_mem_of_isFunc hsf hm')) (app_mem_of_isFunc hsf hm') ⟨h1, h2⟩

/-- **Exercise 15.4.4, second part.** Let $`s : {}^*\mathbb N \to {}^*\mathbb R` be an
internal hypersequence such that $`s_n` is an unlimited hypernatural for all standard $`n`.
Then there is an unlimited hypernatural number less than every $`s_n`, $`n` standard. The
proof applies Robinson's sequential lemma to the reciprocals of the running minima
$`\underline s_n`. The reciprocal is taken of $`\max(\underline s_n, 1)`, so that it is
defined and positive also at the unlimited indices, where nothing is known in advance about
$`\underline s_n`. -/
theorem exists_unlimited_lt_of_internal_seq (hω : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N)
    (hs : F.Internal s) (hsf : IsFunc (F.star F.N) (F.star F.R) s)
    (h : ∀ n : ℕ, app s (F.nat n) ∈ F.star F.N ∧ app s (F.nat n) ∉ F.N) :
    ∃ K, K ∈ F.star F.N ∧ K ∉ F.N ∧ ∀ n : ℕ, F.Lt K (app s (F.nat n)) := by
  have hU' := F.isUniverse'
  obtain ⟨hNint, hNset⟩ := F.star_N_spec
  obtain ⟨hRint, hRset⟩ := F.star_R_spec
  obtain ⟨t, htint, htf, ht⟩ := exists_internal_running_min hs hsf
  obtain ⟨htset, htrel, htfun, htdom⟩ := isFunc_spec hNset hRset htf
  set φ : ℝ → ℝ := fun x => 1 / max x 1 with hφ
  obtain ⟨hGint, hGset, hGrel⟩ :=
    star_rel_spec (F := F.toNonstandardFramework) (Code.isSetOf_rel F.cR F.cR _)
      (Code.relIn_rel F.cR F.cR fun a b => b = φ a)
  have hGf := Code.isFunc_star_graph F.cR F.cR φ
  have hrsub : relComp t (F.star (Code.graph F.cR F.cR φ)) ⊆
      ZFSet.prod (F.star F.N) (F.star F.R) := fun p hp => by
    obtain ⟨a, b, c, rfl, hab, hbc⟩ := mem_relComp.1 hp
    exact pair_mem_prod.2 ⟨(pair_mem_prod.1 (htf.1 hab)).1,
      F.mem_star_R_iff.2 (Code.mem_of_pair_mem_star_rel F.cR F.cR hbc).2⟩
  have hrfun : IsFunction (relComp t (F.star (Code.graph F.cR F.cR φ))) :=
    ⟨fun p hp => let ⟨a, _, c, hpe, _, _⟩ := mem_relComp.1 hp; ⟨a, c, hpe⟩,
      fun a b c hb hc => by
        obtain ⟨w, hw, hwb⟩ := pair_mem_relComp.1 hb
        obtain ⟨w', hw', hwc⟩ := pair_mem_relComp.1 hc
        obtain rfl := htfun.2 _ _ _ hw hw'
        exact hGf.isFunction.2 _ _ _ hwb hwc⟩
  have hrmem : ∀ n ∈ F.star F.N, pair n (Code.ap F.cR F.cR φ (app t n)) ∈
      relComp t (F.star (Code.graph F.cR F.cR φ)) := fun n hn =>
    pair_mem_relComp.2 ⟨app t n, htfun.pair_app_mem (htdom.symm ▸ hn),
      Code.pair_ap_mem F.cR F.cR (F.mem_star_R_iff.1 (app_mem_of_isFunc htf hn))⟩
  have htstd : ∀ n : ℕ, F.PosUnlimited (app t (F.nat n)) := by
    intro n
    obtain ⟨⟨m, hm, hmn, he⟩, -⟩ := ht (F.nat n) (F.N_subset_star (F.mem_N.2 ⟨n, rfl⟩))
    obtain ⟨j, rfl⟩ := F.mem_N.1 (mem_N_of_le_nat hm hmn)
    rw [he]
    exact posUnlimited_of_nonstandard (h j).1 (h j).2
  obtain ⟨K₀, hK₀, hK₀N, hall⟩ := robinson_function hω
    (F.internal_relComp htint htset htrel hGint hGset hGrel)
    (hU'.isSetOf_of_subset_prod hNset hRset hrsub)
    (hU'.relIn_of_subset_prod hNset hRset hrsub) hrfun (by
      intro n
      have hnN : F.nat n ∈ F.star F.N := F.N_subset_star (F.mem_N.2 ⟨n, rfl⟩)
      have hmem := hrmem (F.nat n) hnN
      refine ⟨mem_dom.2 ⟨_, hmem⟩, ?_⟩
      show F.Infinitesimal (app (relComp t (F.star (Code.graph F.cR F.cR φ))) (F.nat n))
      rw [hrfun.app_eq hmem, infinitesimal_iff]
      intro ε hε
      have h1 := real_lt_iff.1 (htstd n (1 / ε + 1))
      refine Code.mem_right_of_rel F.cR F.cR ?_ (Code.rel_of_mem_left F.cR F.cR h1
        (Code.pair_ap_mem F.cR F.cR (g := φ) (F.mem_star_R_iff.1 (app_mem_of_isFunc htf hnN))))
      rintro a b ⟨ha, hb⟩
      have ha' : 1 / ε + 1 < a := ha
      have hpos : 0 < 1 / ε := one_div_pos.2 hε
      have ha1 : max a 1 = a := max_eq_left (by linarith)
      show |b| < ε
      rw [hb, hφ]
      simp only [ha1]
      have hapos : 0 < a := by linarith
      rw [abs_of_pos (one_div_pos.2 hapos), div_lt_iff₀ hapos]
      have := (div_lt_iff₀ hε).1 (by linarith : 1 / ε < a)
      linarith [mul_comm a ε])
  have hK₀R := F.star_N_subset_star_R hK₀
  have hinf : F.Infinitesimal (app (relComp t (F.star (Code.graph F.cR F.cR φ))) K₀) :=
    (hall K₀ hK₀ (F.le_refl hK₀R)).2
  rw [hrfun.app_eq (hrmem K₀ hK₀)] at hinf
  have htK : F.PosUnlimited (app t K₀) := by
    intro q
    have h1 := infinitesimal_iff.1 hinf (1 / (|q| + 1)) (by positivity)
    have h2 := (Code.rel_swap F.cR F.cR).1
      (Code.pair_ap_mem F.cR F.cR (g := φ) (F.mem_star_R_iff.1 (app_mem_of_isFunc htf hK₀)))
    rw [real_lt_iff]
    refine Code.mem_right_of_rel F.cR F.cR ?_ (Code.rel_of_mem_left F.cR F.cR h1 h2)
    rintro b a ⟨hb, hab⟩
    have hb' : |b| < 1 / (|q| + 1) := hb
    show q < a
    have hmpos : (0 : ℝ) < max a 1 := _root_.lt_of_lt_of_le one_pos (le_max_right a 1)
    have hqpos : (0 : ℝ) < |q| + 1 := by positivity
    rw [hab, hφ] at hb'
    simp only [abs_of_pos (one_div_pos.2 hmpos)] at hb'
    have h3 : |q| + 1 < max a 1 := by
      rw [div_lt_div_iff₀ hmpos hqpos] at hb'
      linarith
    have h4 : a = max a 1 := by
      rcases _root_.le_total a 1 with h5 | h5
      · rw [max_eq_right h5] at h3
        linarith [abs_nonneg q]
      · exact (max_eq_left h5).symm
    linarith [le_abs_self q]
  have hBint : F.Internal (F.star F.N ∩ relPreimage (F.star (F.rr (· < ·))) {app t K₀}) :=
    F.internal_inter hNint hNset (internal_relPreimage_star (Code.isSetOf_rel _ _ _)
      (Code.relIn_rel _ _ _) (F.internal_singleton (internal_of_mem_star_R (app_mem_of_isFunc htf hK₀))))
  obtain ⟨K, hK, hKN, hKB⟩ := exists_nonstandard_mem hω hBint (by
    intro m hm
    obtain ⟨k, rfl⟩ := F.mem_N.1 hm
    exact mem_inter.2 ⟨F.N_subset_star hm, mem_relPreimage.2 ⟨_, mem_singleton.2 rfl, htK k⟩⟩)
  obtain ⟨w, hw, hKw⟩ := mem_relPreimage.1 (mem_inter.1 hKB).2
  rw [mem_singleton.1 hw] at hKw
  refine ⟨K, hK, hKN, fun n => ?_⟩
  have hnN : F.nat n ∈ F.star F.N := F.N_subset_star (F.mem_N.2 ⟨n, rfl⟩)
  exact lt_of_lt_of_le hKw ((ht K₀ hK₀).2 (F.nat n) hnN (F.nat_le_of_nonstandard hK₀ hK₀N n))

end RealFramework

end Goldblatt
