import Goldblatt.Ch15_Saturation.Comprehensive

/-!
# 15 (part 6). The ultrapower is comprehensive, and saturation: Sections 15.4 and 15.5

This is the last of six parts of Chapter 15 (the overview is on the chapter page
{lit}`Goldblatt.Ch15_Saturation`). It proves that the bounded ultrapower of Chapter 14 is a
comprehensive framework, by the construction of Section 15.4, with the two parts of Exercise
15.4.1 about that construction; concludes that comprehensive, countably saturated
enlargements exist; and treats the saturation properties of Section 15.5.
-/

noncomputable section

namespace Goldblatt

open ZFSet Filter NonstandardFramework

open scoped Classical

universe u v

/-- Some member of a nonempty set, and the empty set for the empty set. -/
def pick (S : ZFSet.{u}) : ZFSet.{u} := if h : ∃ y, y ∈ S then Classical.choose h else ∅

/-- The chosen member of a nonempty set belongs to it. -/
theorem pick_mem {S : ZFSet.{u}} (h : S ≠ ∅) : pick S ∈ S := by
  have hex : ∃ y, y ∈ S := by
    obtain ⟨y, hy⟩ := (eq_empty_or_nonempty S).resolve_left h
    exact ⟨y, hy⟩
  simp only [pick, hex, ↓reduceDIte]
  exact Classical.choose_spec hex

namespace BoundedUltrapower

variable {I : Type v} [Small.{u} I] {𝓕 : Ultrafilter I} {X : ZFSet.{u}}

/-!
## 15.4 Comprehensiveness: the ultrapower

Let $`B = [H]` be an internal set of the bounded ultrapower and $`f : A \to B` a function on
a set $`A` of the standard universe. For each $`b \in B` choose a function $`p_b` of bounded
rank with $`[p_b] = b`, arranged so that $`p_b(i) \in H(i)` for every index $`i` at which
$`H(i)` is not empty. For each index $`i` let $`f_i` be the function on $`A` with
$`f_i(a) = p_{f(a)}(i)`. The functions $`f_i` have bounded rank uniformly in $`i`, and the
class $`{}^+f = [(f_i : i \in I)]` is an internal function from $`{}^*A` to $`B` with
$`{}^+f([h]) = [(p_{f(h(i))}(i) : i \in I)]`. At $`{}^*a`, the class of a constant
function, this gives $`[p_{f(a)}] = f(a)`.

The choice of the representatives is recorded in a structure, so that the two parts of
Exercise 15.4.1, which are statements about the construction, can be stated.
-/

/-- **Section 15.4, a choice of representatives.** For an internal set $`B` of the bounded
ultrapower: a function $`H` with $`[H] = B` whose values are sets of entities of rank at
most $`n`, and for each $`b \in B` a function $`p_b` with $`[p_b] = b` and
$`p_b(i) \in H(i)` whenever $`H(i)` is not empty. -/
structure Reps (𝓕 : Ultrafilter I) (hX : IsBaseSet X) (B : ZFSet.{u}) where
  /-- A bound on the rank of the members of the values of {lit}`H`. -/
  n : ℕ
  /-- A function representing the internal set. -/
  H : I → ZFSet.{u}
  /-- Every value of {lit}`H` is a set of entities of rank at most {lit}`n`. -/
  H_sub : ∀ i, H i ⊆ cumPow X n
  /-- {lit}`H` represents the internal set. -/
  col_H : col 𝓕 hX H = B
  /-- The representative chosen for a member of the internal set. -/
  P : ZFSet.{u} → I → ZFSet.{u}
  /-- The representative takes its values in the values of {lit}`H`. -/
  P_mem : ∀ b ∈ B, ∀ i, H i ≠ ∅ → P b i ∈ H i
  /-- Where {lit}`H` is empty the representative is the empty set. -/
  P_empty : ∀ b ∈ B, ∀ i, H i = ∅ → P b i = ∅
  /-- The representative represents the member. -/
  col_P : ∀ b ∈ B, col 𝓕 hX (P b) = b

omit [Small.{u} I] in
/-- A function with almost all values in a set of the standard universe has bounded
rank. -/
theorem bdd_of_eventually_mem_set (hX : IsBaseSet X) {A : ZFSet.{u}}
    (hA : IsSetOf (superstructure X) A) {k : I → ZFSet.{u}} (hk : ∀ᶠ i in 𝓕, k i ∈ A) :
    Bdd 𝓕 X k :=
  bdd_of_eventually_mem hX (bdd_const hA.1) (hk.mono fun _ hi =>
    ⟨(isUniverseOver_superstructure hX).toIsUniverse.mem_of_mem hA hi, hi⟩)

namespace Reps

variable {hX : IsBaseSet X} {A B C f g h : ZFSet.{u}} (ρ : Reps 𝓕 hX B)

/-- The function representing the internal set has bounded rank. -/
theorem bdd_H : Bdd 𝓕 X ρ.H :=
  ⟨ρ.n + 1, Eventually.of_forall fun i => mem_cumPow_succ_of_subset (ρ.H_sub i)⟩

/-- The values of the chosen representatives have rank at most $`n + 1`. -/
theorem P_mem_cumPow {b : ZFSet.{u}} (hb : b ∈ B) (i : I) : ρ.P b i ∈ cumPow X (ρ.n + 1) := by
  by_cases h : ρ.H i = ∅
  · rw [ρ.P_empty b hb i h]
    exact mem_cumPow_succ_of_subset (empty_subset _)
  · exact cumPow_subset_succ _ (ρ.H_sub i (ρ.P_mem b hb i h))

/-- The chosen representatives have bounded rank. -/
theorem bdd_P {b : ZFSet.{u}} (hb : b ∈ B) : Bdd 𝓕 X (ρ.P b) :=
  ⟨ρ.n + 1, Eventually.of_forall (ρ.P_mem_cumPow hb)⟩

/-- If the internal set has a member, then almost all values of its representing function
are nonempty. -/
theorem eventually_ne_empty {b : ZFSet.{u}} (hb : b ∈ B) : ∀ᶠ i in 𝓕, ρ.H i ≠ ∅ := by
  have h1 : col 𝓕 hX (ρ.P b) ∈ col 𝓕 hX ρ.H := by
    rw [ρ.col_P b hb, ρ.col_H]
    exact hb
  filter_upwards [(col_mem_col_iff hX (ρ.bdd_P hb) ρ.bdd_H).1 h1] with i hi h0
  rw [h0] at hi
  exact notMem_empty _ hi

/-- **Section 15.4, the functions $`f_i`.** The function on $`A` with value
$`p_{f(a)}(i)` at $`a`, as a set of pairs. -/
def graphAt (A f : ZFSet.{u}) (i : I) : ZFSet.{u} :=
  ZFSet.range fun a : ↥A => pair a.1 (ρ.P (app f a.1) i)

/-- **Section 15.4, the extension $`{}^+f`.** The class of the function
$`i \mapsto f_i`. -/
def ext (A f : ZFSet.{u}) : ZFSet.{u} := col 𝓕 hX (ρ.graphAt A f)

/-- The members of $`f_i`. -/
theorem mem_graphAt {i : I} {p : ZFSet.{u}} :
    p ∈ ρ.graphAt A f i ↔ ∃ a ∈ A, p = pair a (ρ.P (app f a) i) := by
  rw [graphAt, mem_range]
  exact ⟨fun ⟨a, h⟩ => ⟨a.1, a.2, h.symm⟩, fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h.symm⟩⟩

/-- The pairs in $`f_i`. -/
theorem pair_mem_graphAt {i : I} {a w : ZFSet.{u}} :
    pair a w ∈ ρ.graphAt A f i ↔ a ∈ A ∧ w = ρ.P (app f a) i := by
  rw [mem_graphAt]
  constructor
  · rintro ⟨a', ha', h⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.1 h
    exact ⟨ha', rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨a, ha, rfl⟩

/-- $`f_i` is a function. -/
theorem isFunction_graphAt (i : I) : IsFunction (ρ.graphAt A f i) := by
  refine ⟨fun p hp => ?_, fun a b c hb hc => ?_⟩
  · obtain ⟨a, -, rfl⟩ := ρ.mem_graphAt.1 hp
    exact ⟨_, _, rfl⟩
  · rw [(ρ.pair_mem_graphAt.1 hb).2, (ρ.pair_mem_graphAt.1 hc).2]

/-- The value of $`f_i` at a member of $`A`. -/
theorem app_graphAt {i : I} {a : ZFSet.{u}} (ha : a ∈ A) :
    app (ρ.graphAt A f i) a = ρ.P (app f a) i :=
  (ρ.isFunction_graphAt i).app_eq (ρ.pair_mem_graphAt.2 ⟨ha, rfl⟩)

variable (hA : IsSetOf (superstructure X) A) (hf : IsFunc A B f)
include hA hf

/-- $`f_i` is a binary relation of the standard universe. -/
theorem relIn_graphAt (i : I) : RelIn (superstructure X) (ρ.graphAt A f i) := fun p hp => by
  obtain ⟨a, ha, rfl⟩ := ρ.mem_graphAt.1 hp
  exact ⟨a, (isUniverseOver_superstructure hX).toIsUniverse.mem_of_mem hA ha, _,
    cumPow_subset_superstructure _ (ρ.P_mem_cumPow (hf.app_mem ha) i), rfl⟩

/-- **Section 15.4.** The functions $`f_i` have bounded rank, uniformly in $`i`. -/
theorem exists_graphAt_mem_cumPow : ∃ N, ∀ i, ρ.graphAt A f i ∈ cumPow X N := by
  obtain ⟨m, hm⟩ := mem_superstructure.1 hA.1
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  refine ⟨max m (ρ.n + 1) + 2 + 1, fun i => mem_cumPow_succ_of_subset fun p hp => ?_⟩
  obtain ⟨a, ha, rfl⟩ := ρ.mem_graphAt.1 hp
  have ha' : a ∈ cumPow X m := mem_cumPow_of_mem' hX hm ha (hW.mem_of_mem hA ha)
  exact opair_mem_cumPow (cumPow_mono (le_max_left _ _) ha')
    (cumPow_mono (le_max_right _ _) (ρ.P_mem_cumPow (hf.app_mem ha) i))

/-- The function $`i \mapsto f_i` has bounded rank. -/
theorem bdd_graphAt : Bdd 𝓕 X (ρ.graphAt A f) :=
  let ⟨N, hN⟩ := ρ.exists_graphAt_mem_cumPow hA hf
  ⟨N, Eventually.of_forall hN⟩

/-- **Section 15.4.** $`{}^+f` is an internal entity. -/
theorem internal_ext : (framework 𝓕 hX).Internal (ρ.ext A f) := by
  obtain ⟨N, hN⟩ := ρ.exists_graphAt_mem_cumPow hA hf
  exact ⟨cumPow X N,
    isSetOf_of_subset (cumPow_mem_superstructure N) (cumPow_subset_superstructure N),
    (mem_star_cumPow_iff hX N).2 ⟨_, Eventually.of_forall hN, rfl⟩⟩

/-- **Section 15.4, the action of $`{}^+f`.** For $`[h] \in {}^*A`, with $`h(i) \in A` for
almost all $`i`, $`{}^+f([h]) = [(p_{f(h(i))}(i) : i \in I)]`. -/
theorem ext_app {k : I → ZFSet.{u}} (hk : ∀ᶠ i in 𝓕, k i ∈ A) :
    app (ρ.ext A f) (col 𝓕 hX k) = col 𝓕 hX fun i => ρ.P (app f (k i)) i := by
  have hbk := bdd_of_eventually_mem_set hX hA hk
  have hbv : Bdd 𝓕 X fun i => ρ.P (app f (k i)) i :=
    ⟨ρ.n + 1, hk.mono fun i hi => ρ.P_mem_cumPow (hf.app_mem hi) i⟩
  refine (app_col_eq_iff hX (ρ.bdd_graphAt hA hf) hbk hbv
    (Eventually.of_forall fun i => ⟨ρ.isFunction_graphAt i, ρ.relIn_graphAt hA hf i⟩)).2 ?_
  filter_upwards [hk] with i hi
  exact ρ.app_graphAt hi

/-- **Section 15.4.** $`{}^+f({}^*a) = f(a)` for all $`a \in A`. -/
theorem ext_app_star {a : ZFSet.{u}} (ha : a ∈ A) :
    app (ρ.ext A f) (star 𝓕 hX a) = app f a := by
  have := ρ.ext_app hA hf (k := fun _ => a) (Eventually.of_forall fun _ => ha)
  rw [star, this]
  exact ρ.col_P _ (hf.app_mem ha)

/-- **Section 15.4.** $`{}^+f` is a function from $`{}^*A` to $`B`. -/
theorem isFunc_ext : IsFunc (star 𝓕 hX A) B (ρ.ext A f) := by
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  have hW' := (isUniverseOver_superstructure (isBaseSet_base (𝓕 := 𝓕) hX)).toIsUniverse
  have hG := ρ.bdd_graphAt hA hf
  obtain ⟨hfun, hrel⟩ := isFunction_col hX hG
    (Eventually.of_forall fun i => ⟨ρ.isFunction_graphAt i, ρ.relIn_graphAt hA hf i⟩)
  refine ⟨fun y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨u, hu, w, hw, rfl⟩ := hrel y hy
    obtain ⟨fy, hfy, hmem, hcol⟩ :=
      exists_of_mem_col hX (hW'.isSetOf_opair hu hw).1 hy
    have hex : ∀ᶠ i in 𝓕, ∃ a, a ∈ A ∧ fy i = pair a (ρ.P (app f a) i) :=
      hmem.mono fun i hi => ρ.mem_graphAt.1 hi
    obtain ⟨α, hα⟩ := Filter.skolem.1 hex
    have hαA : ∀ᶠ i in 𝓕, α i ∈ A := hα.mono fun i hi => hi.1
    have hbα := bdd_of_eventually_mem_set hX hA hαA
    have hbv : Bdd 𝓕 X fun i => ρ.P (app f (α i)) i :=
      ⟨ρ.n + 1, hαA.mono fun i hi => ρ.P_mem_cumPow (hf.app_mem hi) i⟩
    have e : col 𝓕 hX fy = pair (col 𝓕 hX α) (col 𝓕 hX fun i => ρ.P (app f (α i)) i) := by
      rw [← col_opair hX hbα hbv]
      exact col_congr hX (hα.mono fun i hi => hi.2)
    rw [hcol] at e
    obtain ⟨rfl, rfl⟩ := pair_inj.1 e
    refine pair_mem_prod.2 ⟨(mem_star_iff hX hA).2 ⟨α, hbα, hαA, rfl⟩, ?_⟩
    obtain ⟨i₀, hi₀⟩ := hαA.exists
    have hne := ρ.eventually_ne_empty (hf.app_mem hi₀)
    have hmemH := (col_mem_col_iff hX hbv ρ.bdd_H).2 (by
      filter_upwards [hαA, hne] with i hi hi'
      exact ρ.P_mem _ (hf.app_mem hi) i hi')
    rwa [ρ.col_H] at hmemH
  · obtain ⟨k, hbk, hk, rfl⟩ := (mem_star_iff hX hA).1 hz
    have hbv : Bdd 𝓕 X fun i => ρ.P (app f (k i)) i :=
      ⟨ρ.n + 1, hk.mono fun i hi => ρ.P_mem_cumPow (hf.app_mem hi) i⟩
    have hmem : pair (col 𝓕 hX k) (col 𝓕 hX fun i => ρ.P (app f (k i)) i) ∈ ρ.ext A f :=
      (col_appVal hX hG hbk hbv).2 (hk.mono fun i hi => ρ.pair_mem_graphAt.2 ⟨hi, rfl⟩)
    exact ⟨_, hmem, fun w hw => hfun.2 _ _ _ hw hmem⟩

/-- **Exercise 15.4.1 (1).** If two functions $`f, g : A \to B` differ only at finitely
many members $`a_1, \dots, a_n` of $`A`, then $`{}^+f` and $`{}^+g` differ only at
$`{}^*a_1, \dots, {}^*a_n`: a point of $`{}^*A` at which they differ is $`{}^*a` for some
$`a` with $`f(a) \ne g(a)`. Both extensions are formed with the same choice of
representatives. -/
theorem eq_star_of_ext_app_ne (hg : IsFunc A B g)
    (hfin : {a | a ∈ A ∧ app f a ≠ app g a}.Finite) {z : ZFSet.{u}} (hz : z ∈ star 𝓕 hX A)
    (hne : app (ρ.ext A f) z ≠ app (ρ.ext A g) z) :
    ∃ a ∈ A, app f a ≠ app g a ∧ z = star 𝓕 hX a := by
  obtain ⟨k, -, hk, rfl⟩ := (mem_star_iff hX hA).1 hz
  by_cases hD : ∀ᶠ i in 𝓕, k i ∈ {a | a ∈ A ∧ app f a ≠ app g a}
  · have hU : (⋃ a ∈ {a | a ∈ A ∧ app f a ≠ app g a}, {i | k i = a}) ∈ 𝓕 := by
      filter_upwards [hD] with i hi
      exact Set.mem_biUnion hi rfl
    obtain ⟨a, ha, hka⟩ := (Ultrafilter.finite_biUnion_mem_iff hfin).1 hU
    exact ⟨a, ha.1, ha.2, col_congr hX hka⟩
  · exfalso
    apply hne
    rw [ρ.ext_app hA hf hk, ρ.ext_app hA hg hk]
    refine col_congr hX ?_
    filter_upwards [hk, Ultrafilter.eventually_not.2 hD] with i hi hi'
    have : app f (k i) = app g (k i) := by
      by_contra hfg
      exact hi' ⟨hi, hfg⟩
    show ρ.P (app f (k i)) i = ρ.P (app g (k i)) i
    rw [this]

end Reps

variable {A B C f h : ZFSet.{u}}

/-- **Section 15.4.** Every internal set of the bounded ultrapower has a choice of
representatives. -/
theorem exists_reps (hX : IsBaseSet X) (hB : (framework 𝓕 hX).InternalSet B) :
    Nonempty (Reps 𝓕 hX B) := by
  have hW' := (isUniverseOver_superstructure (isBaseSet_base (𝓕 := 𝓕) hX)).toIsUniverse
  obtain ⟨T, hT, hBT⟩ := hB.1
  obtain ⟨H₀, ⟨n, hn⟩, -, hcol⟩ := (mem_star_iff hX hT).1 hBT
  have hnat : ¬ Atomic 𝓕 X H₀ := fun hat => hB.2.2 (hcol ▸ isIndividual_col hX hat)
  have hnX := not_atomic_iff.1 hnat
  set H : I → ZFSet.{u} := fun i => if H₀ i ∈ cumPow X n ∧ H₀ i ∉ X then H₀ i else ∅ with hH
  have hHeq : H =ᶠ[𝓕] H₀ := by
    filter_upwards [hn, hnX] with i h1 h2
    simp [hH, h1, h2]
  have hHsub : ∀ i, H i ⊆ cumPow X n := by
    intro i
    by_cases hc : H₀ i ∈ cumPow X n ∧ H₀ i ∉ X
    · have e : H i = H₀ i := by simp [hH, hc]
      rw [e]
      cases n with
      | zero => exact absurd (by simpa using hc.1) hc.2
      | succ m => exact fun y hy => cumPow_subset_succ m (subset_cumPow_of_mem_succ hc.1 hc.2 hy)
    · have e : H i = ∅ := by simp [hH, hc]
      rw [e]
      exact empty_subset _
  have hcolH : col 𝓕 hX H = B := by rw [col_congr hX hHeq, hcol]
  have hex : ∀ b : {b // b ∈ B}, ∃ p : I → ZFSet.{u},
      Bdd 𝓕 X p ∧ (∀ᶠ i in 𝓕, p i ∈ H i) ∧ col 𝓕 hX p = b.1 := fun b =>
    exists_of_mem_col hX (hW'.mem_of_mem hB.2 b.2) (hcolH ▸ b.2)
  choose p₀ hp₀ using hex
  refine ⟨{
    n := n
    H := H
    H_sub := hHsub
    col_H := hcolH
    P := fun b i => if hb : b ∈ B then (if p₀ ⟨b, hb⟩ i ∈ H i then p₀ ⟨b, hb⟩ i else pick (H i))
      else ∅
    P_mem := fun b hb i hi => by
      simp only [hb, ↓reduceDIte]
      split_ifs with h1
      · exact h1
      · exact pick_mem hi
    P_empty := fun b hb i hi => by
      simp only [hb, ↓reduceDIte]
      split_ifs with h1
      · rw [hi] at h1
        exact absurd h1 (notMem_empty _)
      · rw [hi]
        simp [pick, notMem_empty]
    col_P := fun b hb => by
      refine Eq.trans (col_congr hX ?_) (hp₀ ⟨b, hb⟩).2.2
      filter_upwards [(hp₀ ⟨b, hb⟩).2.1] with i hi
      simp [hb, hi] }⟩

/-- **Section 15.4, the ultrapower is comprehensive.** For every ultrafilter on a small
index set and every base set $`X`, the bounded ultrapower of $`\mathbb U(X)` is a
comprehensive framework: every function from a set of $`\mathbb U(X)` to an internal set
extends to an internal function on the transform of its domain. -/
theorem comprehensive_framework (𝓕 : Ultrafilter I) (hX : IsBaseSet X) :
    (framework 𝓕 hX).Comprehensive := by
  intro A B f hA hB hf
  obtain ⟨ρ⟩ := exists_reps hX hB
  exact ⟨ρ.ext A f, ρ.internal_ext hA hf, ρ.isFunc_ext hA hf,
    fun a ha => ρ.ext_app_star hA hf ha⟩

/-- **Exercise 15.4.1 (2).** Let $`h : A \to C` be a function in $`\mathbb U(X)` and
$`f : A \to {}^*C` its extension by the transfer map, $`f(a) = {}^*(h(a))`. Then, for a
suitable choice of the representatives, $`{}^+f` is the transform $`{}^*h`. The suitable
choice represents $`{}^*C` by the constant function with value $`C` and each standard member
$`{}^*c` by the constant function with value $`c`. -/
theorem exists_reps_ext_eq_star (hX : IsBaseSet X)
    (hC : IsSetOf (superstructure X) C) (hh : IsFunc A C h)
    (hfh : ∀ a ∈ A, app f a = star 𝓕 hX (app h a)) :
    ∃ ρ : Reps 𝓕 hX (star 𝓕 hX C), ρ.ext A f = star 𝓕 hX h := by
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  obtain ⟨m, hm⟩ := mem_superstructure.1 hC.1
  have hCsub : C ⊆ cumPow X m := fun y hy => mem_cumPow_of_mem' hX hm hy (hW.mem_of_mem hC hy)
  have hex : ∀ b : {b // b ∈ star 𝓕 hX C}, ∃ p : I → ZFSet.{u},
      Bdd 𝓕 X p ∧ (∀ᶠ i in 𝓕, p i ∈ C) ∧ col 𝓕 hX p = b.1 := fun b =>
    (mem_star_iff hX hC).1 b.2
  choose p₀ hp₀ using hex
  have hstd : ∀ {b : ZFSet.{u}} (hb : ∃ c, c ∈ C ∧ b = star 𝓕 hX c),
      Classical.choose hb ∈ C ∧ b = star 𝓕 hX (Classical.choose hb) := fun hb =>
    Classical.choose_spec hb
  let ρ : Reps 𝓕 hX (star 𝓕 hX C) := {
    n := m
    H := fun _ => C
    H_sub := fun _ => hCsub
    col_H := rfl
    P := fun b i => if hb : ∃ c, c ∈ C ∧ b = star 𝓕 hX c then Classical.choose hb
      else if hb' : b ∈ star 𝓕 hX C then (if p₀ ⟨b, hb'⟩ i ∈ C then p₀ ⟨b, hb'⟩ i else pick C)
      else ∅
    P_mem := fun b hb i hi => by
      split_ifs with h1 h2
      · exact (hstd h1).1
      · exact h2
      · exact pick_mem hi
    P_empty := fun b hb i hi => by
      exfalso
      rw [hi, star, col_const_empty] at hb
      exact notMem_empty b hb
    col_P := fun b hb => by
      by_cases h1 : ∃ c, c ∈ C ∧ b = star 𝓕 hX c
      · simp only [h1, ↓reduceDIte]
        exact (hstd h1).2.symm
      · simp only [h1, hb, ↓reduceDIte]
        refine Eq.trans (col_congr hX ?_) (hp₀ ⟨b, hb⟩).2.2
        filter_upwards [(hp₀ ⟨b, hb⟩).2.1] with i hi
        simp [hi] }
  refine ⟨ρ, ?_⟩
  have hval : ∀ a ∈ A, ∀ i, ρ.P (app f a) i = app h a := by
    intro a ha i
    have hha : app h a ∈ C :=
      (pair_mem_prod.1 (hh.1 (hh.isFunction.pair_app_mem (hh.dom_eq.symm ▸ ha)))).2
    have h1 : ∃ c, c ∈ C ∧ app f a = star 𝓕 hX c := ⟨app h a, hha, hfh a ha⟩
    show (if hb : ∃ c, c ∈ C ∧ app f a = star 𝓕 hX c then Classical.choose hb else _) = _
    simp only [h1, ↓reduceDIte]
    obtain ⟨h2, h3⟩ := hstd h1
    have h3' : star 𝓕 hX (Classical.choose h1) = star 𝓕 hX (app h a) := h3.symm.trans (hfh a ha)
    exact ((col_eq_iff hX (bdd_const (hW.mem_of_mem hC h2))
      (bdd_const (hW.mem_of_mem hC hha))).1 h3').exists.choose_spec
  have hgraph : ∀ i, ρ.graphAt A f i = h := by
    intro i
    ext p
    rw [ρ.mem_graphAt]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hval a ha i]
      exact hh.isFunction.pair_app_mem (hh.dom_eq.symm ▸ ha)
    · intro hp
      obtain ⟨a, ha, c, -, rfl⟩ := mem_prod.1 (hh.1 hp)
      exact ⟨a, ha, by rw [hval a ha i, hh.isFunction.app_eq hp]⟩
  show col 𝓕 hX (ρ.graphAt A f) = col 𝓕 hX fun _ => h
  exact congrArg _ (funext hgraph)

/-- **Section 15.4.** The enlargement constructed in Section 14.3 is comprehensive. -/
theorem comprehensive_enlargement (hX : IsBaseSet X) : (enlargement X hX).Comprehensive :=
  comprehensive_framework (ultra X) hX

end BoundedUltrapower

/-!
## Existence of comprehensive and countably saturated enlargements

From what has been proved about ultrapowers, the construction of Section 14.3 produces an
enlargement that is comprehensive, hence countably comprehensive, and so, when the real
numbers are among the individuals, countably saturated by Theorem 15.4.2. These are the
frameworks assumed in Part V of the book.
-/

/-- **Section 15.4.** Over any base set $`X` the superstructure $`\mathbb U(X)` has a
comprehensive enlargement of the form $`\mathbb U({}^*X)`. -/
theorem exists_comprehensive_enlargement {X : ZFSet.{u}} (hX : IsBaseSet X) :
    ∃ F : NonstandardFramework.{u}, F.X = X ∧ F.U = superstructure X ∧
      F.U' = superstructure (F.star X) ∧ F.IsEnlargement ∧ F.Comprehensive :=
  ⟨BoundedUltrapower.enlargement X hX, rfl, rfl,
    by rw [BoundedUltrapower.enlargement_star_base hX]; rfl,
    BoundedUltrapower.isEnlargement_enlargement hX, BoundedUltrapower.comprehensive_enlargement hX⟩

/-- **Section 15.4, existence of countably saturated enlargements over any type.** For
every type $`\alpha` there is a framework over the real numbers whose set of individuals
contains, besides the reals, a copy of $`\alpha`, and which is an enlargement between
superstructures, comprehensive and countably saturated. -/
theorem exists_realFramework_countablySaturated_of_type (α : Type u) :
    ∃ (ι : α → ZFSet.{u}) (F : RealFramework.{u}), Function.Injective ι ∧
      (∀ a, ι a ∈ F.X) ∧ (∀ a r, ι a ≠ F.real r) ∧ F.U = superstructure F.X ∧
      F.U' = superstructure (F.star F.X) ∧ F.IsEnlargement ∧ F.Comprehensive ∧
      F.CountablySaturated := by
  obtain ⟨j, hj, hX⟩ := exists_isBaseSet (α ⊕ ULift.{u} ℝ)
  obtain ⟨F₀, h1, h2, h3, h4, h5⟩ := exists_comprehensive_enlargement hX
  let F : RealFramework.{u} := { F₀ with
    real := fun r => j (Sum.inr ⟨r⟩)
    real_injective := fun _ _ hrs => congrArg ULift.down (Sum.inr_injective (hj hrs))
    real_mem := fun r => h1 ▸ mem_range.2 ⟨Sum.inr ⟨r⟩, rfl⟩ }
  have hE : F.IsEnlargement := h4
  have hC : F.Comprehensive := h5
  refine ⟨fun a => j (Sum.inl a), F, fun _ _ hab => Sum.inl_injective (hj hab),
    fun a => h1 ▸ mem_range.2 ⟨Sum.inl a, rfl⟩, fun a r hne => by simpa using hj hne,
    by rw [show F.U = F₀.U from rfl, h2, ← h1], by rw [show F.U' = F₀.U' from rfl, h3, ← h1],
    hE, hC, RealFramework.countablySaturated_of_comprehensive hC
      (RealFramework.exists_nonstandard_nat hE)⟩

/-- **Section 15.4, existence of a countably saturated enlargement.** There is a framework
over the real numbers that is an enlargement between superstructures, comprehensive,
sequentially comprehensive and countably saturated. -/
theorem exists_realFramework_countablySaturated :
    ∃ F : RealFramework.{u}, F.IsEnlargement ∧ F.Comprehensive ∧ F.SequentiallyComprehensive ∧
      F.CountablySaturated ∧ F.U = superstructure F.X ∧ F.U' = superstructure (F.star F.X) := by
  obtain ⟨-, F, -, -, -, hU, hU', hE, hC, hS⟩ :=
    exists_realFramework_countablySaturated_of_type PEmpty.{u + 1}
  exact ⟨F, hE, hC,
    RealFramework.sequentiallyComprehensive_of_countablyComprehensive hC.countablyComprehensive,
    hS, hU, hU'⟩

end Goldblatt
