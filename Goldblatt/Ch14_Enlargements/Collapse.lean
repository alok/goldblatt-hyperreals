import Goldblatt.Ch13_Universes

noncomputable section

namespace Goldblatt

open ZFSet Filter
open scoped Classical

universe u v

namespace BoundedUltrapower

variable {I : Type v} (𝓕 : Ultrafilter I) (X : ZFSet.{u})

def Bdd (f : I → ZFSet.{u}) : Prop := ∃ n, ∀ᶠ i in 𝓕, f i ∈ cumPow X n

def Atomic (f : I → ZFSet.{u}) : Prop := ∀ᶠ i in 𝓕, f i ∈ X

def E (f g : I → ZFSet.{u}) : Prop := Bdd 𝓕 X f ∧ Bdd 𝓕 X g ∧ ∀ᶠ i in 𝓕, f i ∈ g i

def rk (f : I → ZFSet.{u}) : ℕ := sInf {n | ∀ᶠ i in 𝓕, f i ∈ cumPow X n}

variable {𝓕 X} {f g h : I → ZFSet.{u}}

theorem Bdd.congr (hf : Bdd 𝓕 X f) (hfg : f =ᶠ[𝓕] g) : Bdd 𝓕 X g := by
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, by filter_upwards [hn, hfg] with i h1 h2; rwa [← h2]⟩

theorem bdd_const {a : ZFSet.{u}} (ha : a ∈ superstructure X) : Bdd 𝓕 X fun _ => a := by
  obtain ⟨n, hn⟩ := mem_superstructure.1 ha
  exact ⟨n, Eventually.of_forall fun _ => hn⟩

theorem Bdd.eventually_mem (hf : Bdd 𝓕 X f) : ∀ᶠ i in 𝓕, f i ∈ superstructure X := by
  obtain ⟨n, hn⟩ := hf
  exact hn.mono fun i hi => cumPow_subset_superstructure n hi

theorem Atomic.bdd (hf : Atomic 𝓕 X f) : Bdd 𝓕 X f := ⟨0, hf⟩

theorem Atomic.congr (hf : Atomic 𝓕 X f) (hfg : f =ᶠ[𝓕] g) : Atomic 𝓕 X g := by
  filter_upwards [hf, hfg] with i h1 h2; rwa [← h2]

theorem mem_cumPow_of_mem (hX : IsBaseSet X) {n : ℕ} {y z : ZFSet.{u}}
    (hy : y ∈ cumPow X (n + 1)) (hz : z ∈ y) (hzW : z ∈ superstructure X) : z ∈ cumPow X n :=
  subset_cumPow_of_mem_succ hy (fun h => (hX y h).2 z hzW hz) hz

theorem bdd_of_eventually_mem (hX : IsBaseSet X) (hg : Bdd 𝓕 X g)
    (hf : ∀ᶠ i in 𝓕, f i ∈ superstructure X ∧ f i ∈ g i) : Bdd 𝓕 X f := by
  obtain ⟨n, hn⟩ := hg
  refine ⟨n, ?_⟩
  filter_upwards [hn, hf] with i h1 h2
  exact mem_cumPow_of_mem hX (cumPow_subset_succ n h1) h2.2 h2.1

theorem not_atomic_iff : ¬ Atomic 𝓕 X f ↔ ∀ᶠ i in 𝓕, f i ∉ X :=
  Ultrafilter.eventually_not.symm

theorem eventually_mem_cumPow_rk (hf : Bdd 𝓕 X f) : ∀ᶠ i in 𝓕, f i ∈ cumPow X (rk 𝓕 X f) :=
  Nat.sInf_mem hf

theorem E.rk_lt (hX : IsBaseSet X) (h : E 𝓕 X f g) : rk 𝓕 X f < rk 𝓕 X g := by
  obtain ⟨hf, hg, hfg⟩ := h
  have hgr := eventually_mem_cumPow_rk hg
  have hfW := hf.eventually_mem
  cases hr : rk 𝓕 X g with
  | zero =>
    rw [hr] at hgr
    have : ∀ᶠ _ in (𝓕 : Filter I), False := by
      filter_upwards [hgr, hfg, hfW] with i h1 h2 h3
      exact (hX _ h1).2 _ h3 h2
    exact this.exists.elim (fun _ h => h.elim)
  | succ k =>
    rw [hr] at hgr
    have : ∀ᶠ i in 𝓕, f i ∈ cumPow X k := by
      filter_upwards [hgr, hfg, hfW] with i h1 h2 h3
      exact mem_cumPow_of_mem hX h1 h2 h3
    exact Nat.lt_succ_of_le (Nat.sInf_le this)

theorem E_wf (hX : IsBaseSet X) : WellFounded (E 𝓕 X) :=
  Subrelation.wf (fun h => E.rk_lt hX h) (measure (rk 𝓕 X)).wf



variable (𝓕 X)

def newAtom (c : ZFSet.{u}) : ZFSet.{u} := {pair (superstructure X) c}

abbrev AtomGerm := (𝓕 : Filter I).Germ ↥(insert (∅ : ZFSet.{u}) X)

def atomGerm (f : I → ZFSet.{u}) : AtomGerm 𝓕 X :=
  ((fun i => if h : f i ∈ X then ⟨f i, mem_insert_of_mem _ h⟩ else ⟨∅, mem_insert _ _⟩ :
    I → ↥(insert (∅ : ZFSet.{u}) X)) : AtomGerm 𝓕 X)

variable [Small.{u} I]

instance : Small.{u} (AtomGerm 𝓕 X) :=
  inferInstanceAs (Small.{u} (Quotient (germSetoid (𝓕 : Filter I) _)))

def enc (q : AtomGerm 𝓕 X) : ZFSet.{u} :=
  (Ordinal.typein (WellOrderingRel (α := Shrink.{u} (AtomGerm 𝓕 X))) (equivShrink _ q)).toZFSet

def atomOf (f : I → ZFSet.{u}) : ZFSet.{u} :=
  if h : ∃ x ∈ X, atomGerm 𝓕 X f = atomGerm 𝓕 X fun _ => x then h.choose
  else newAtom X (enc 𝓕 X (atomGerm 𝓕 X f))

def base : ZFSet.{u} := ZFSet.range fun h : I → ↥X => atomOf 𝓕 X fun i => (h i).1

variable {𝓕 X}

omit [Small.{u} I] in
theorem atomGerm_congr (hfg : f =ᶠ[𝓕] g) : atomGerm 𝓕 X f = atomGerm 𝓕 X g :=
  Germ.coe_eq.2 (hfg.mono fun i hi => by simp only [hi])

omit [Small.{u} I] in
theorem eventuallyEq_of_atomGerm_eq (hf : Atomic 𝓕 X f) (hg : Atomic 𝓕 X g)
    (h : atomGerm 𝓕 X f = atomGerm 𝓕 X g) : f =ᶠ[𝓕] g := by
  have h' := Germ.coe_eq.1 h
  filter_upwards [hf, hg, h'] with i h1 h2 h3
  simpa [h1, h2, Subtype.ext_iff] using h3

theorem atomOf_congr (hfg : f =ᶠ[𝓕] g) : atomOf 𝓕 X f = atomOf 𝓕 X g := by
  simp only [atomOf, atomGerm_congr hfg]

theorem atomOf_const {x : ZFSet.{u}} (hx : x ∈ X) : atomOf 𝓕 X (fun _ => x) = x := by
  rw [atomOf]
  split_ifs with h
  · have h1 := eventuallyEq_of_atomGerm_eq (Eventually.of_forall fun _ => hx)
      (Eventually.of_forall fun _ => h.choose_spec.1) h.choose_spec.2
    obtain ⟨_, hi⟩ := h1.exists
    exact hi.symm
  · exact absurd ⟨x, hx, rfl⟩ h

theorem atomOf_mem_or (f : I → ZFSet.{u}) :
    atomOf 𝓕 X f ∈ X ∨ ∃ c, atomOf 𝓕 X f = newAtom X c := by
  rw [atomOf]
  split_ifs with h
  · exact Or.inl h.choose_spec.1
  · exact Or.inr ⟨_, rfl⟩

theorem rank_lt_rank_newAtom (c : ZFSet.{u}) :
    (superstructure X).rank < (newAtom X c).rank := by
  have h1 : superstructure X ∈ ({superstructure X} : ZFSet.{u}) := mem_singleton.2 rfl
  have h2 : ({superstructure X} : ZFSet.{u}) ∈ pair (superstructure X) c := singleton_mem_pair
  have h3 : pair (superstructure X) c ∈ newAtom X c := mem_singleton.2 rfl
  exact (ZFSet.rank_lt_of_mem h1).trans ((ZFSet.rank_lt_of_mem h2).trans (ZFSet.rank_lt_of_mem h3))

theorem rank_lt_of_mem_base {x : ZFSet.{u}} (hx : x ∈ X) : x.rank < (superstructure X).rank :=
  (ZFSet.rank_lt_of_mem hx).trans (ZFSet.rank_lt_of_mem base_mem_superstructure)

theorem newAtom_notMem (c : ZFSet.{u}) : newAtom X c ∉ X := fun h =>
  lt_asymm (rank_lt_rank_newAtom c) (rank_lt_of_mem_base h)

theorem newAtom_injective : Function.Injective (newAtom X) := fun _ _ h =>
  (pair_inj.1 (singleton_injective h)).2

theorem enc_injective : Function.Injective (enc 𝓕 X) := fun _ _ h =>
  (equivShrink _).injective (Ordinal.typein_injective _ (Ordinal.toZFSet_injective h))

theorem atomOf_inj (hf : Atomic 𝓕 X f) (hg : Atomic 𝓕 X g)
    (h : atomOf 𝓕 X f = atomOf 𝓕 X g) : f =ᶠ[𝓕] g := by
  apply eventuallyEq_of_atomGerm_eq hf hg
  rw [atomOf, atomOf] at h
  split_ifs at h with h1 h2 h2
  · rw [h1.choose_spec.2, h2.choose_spec.2, h]
  · exact absurd (h ▸ h1.choose_spec.1) (newAtom_notMem _)
  · exact absurd (h ▸ h2.choose_spec.1) (newAtom_notMem _)
  · exact enc_injective (newAtom_injective h)

theorem atomOf_mem_base (hf : Atomic 𝓕 X f) : atomOf 𝓕 X f ∈ base 𝓕 X := by
  obtain ⟨i0, hi0⟩ := hf.exists
  refine mem_range.2 ⟨fun i => if hi : f i ∈ X then ⟨f i, hi⟩ else ⟨f i0, hi0⟩, atomOf_congr ?_⟩
  filter_upwards [hf] with i hi
  simp [hi]

theorem exists_atomic_of_mem_base {y : ZFSet.{u}} (hy : y ∈ base 𝓕 X) :
    ∃ f, Atomic 𝓕 X f ∧ atomOf 𝓕 X f = y := by
  obtain ⟨h, rfl⟩ := mem_range.1 hy
  exact ⟨_, Eventually.of_forall fun i => (h i).2, rfl⟩

theorem base_subset : X ⊆ base 𝓕 X := fun x hx =>
  mem_range.2 ⟨fun _ => ⟨x, hx⟩, atomOf_const hx⟩

theorem mem_base_cases {y : ZFSet.{u}} (hy : y ∈ base 𝓕 X) : y ∈ X ∨ ∃ c, y = newAtom X c := by
  obtain ⟨h, rfl⟩ := mem_range.1 hy
  exact atomOf_mem_or _

theorem mem_cumPow_of_rank_le :
    ∀ (n : ℕ) {z : ZFSet.{u}}, z ∈ cumPow (base 𝓕 X) n → z.rank ≤ (superstructure X).rank →
      z ∈ cumPow X n
  | 0, z, hz, hr => by
    rcases mem_base_cases hz with h | ⟨c, rfl⟩
    · exact h
    · exact absurd hr (not_le.2 (rank_lt_rank_newAtom c))
  | n + 1, z, hz, hr => by
    rw [cumPow_succ, mem_union] at hz
    rcases hz with hz | hz
    · exact cumPow_subset_succ n (mem_cumPow_of_rank_le n hz hr)
    · exact mem_cumPow_succ_of_subset fun w hw =>
        mem_cumPow_of_rank_le n (mem_powerset.1 hz hw) ((ZFSet.rank_lt_of_mem hw).le.trans hr)

theorem superstructure_notMem_cumPow_base (n : ℕ) :
    superstructure X ∉ cumPow (base 𝓕 X) n := fun h =>
  mem_irrefl _ (cumPow_subset_superstructure n (mem_cumPow_of_rank_le n h le_rfl))

theorem singleton_superstructure_notMem_base :
    ({superstructure X} : ZFSet.{u}) ∉ base 𝓕 X := fun h => by
  have h1 : superstructure X ∈ ({superstructure X} : ZFSet.{u}) := mem_singleton.2 rfl
  rcases mem_base_cases h with h | ⟨c, hc⟩
  · exact lt_asymm (ZFSet.rank_lt_of_mem h1) (rank_lt_of_mem_base h)
  · have h2 : superstructure X = pair (superstructure X) c := singleton_injective hc
    have h3 : ({superstructure X} : ZFSet.{u}) ∈ pair (superstructure X) c := singleton_mem_pair
    rw [← h2] at h3
    exact lt_asymm (ZFSet.rank_lt_of_mem h1) (ZFSet.rank_lt_of_mem h3)

theorem singleton_superstructure_notMem_cumPow_base (n : ℕ) :
    ({superstructure X} : ZFSet.{u}) ∉ cumPow (base 𝓕 X) n := by
  cases n with
  | zero => exact singleton_superstructure_notMem_base
  | succ n =>
    exact fun h => superstructure_notMem_cumPow_base n
      (subset_cumPow_of_mem_succ h singleton_superstructure_notMem_base (mem_singleton.2 rfl))

theorem pair_superstructure_notMem_base (c : ZFSet.{u}) :
    pair (superstructure X) c ∉ base 𝓕 X := fun h => by
  have h1 : superstructure X ∈ ({superstructure X} : ZFSet.{u}) := mem_singleton.2 rfl
  have h2 : ({superstructure X} : ZFSet.{u}) ∈ pair (superstructure X) c := singleton_mem_pair
  rcases mem_base_cases h with h | ⟨d, hd⟩
  · exact lt_asymm ((ZFSet.rank_lt_of_mem h1).trans (ZFSet.rank_lt_of_mem h2)) (rank_lt_of_mem_base h)
  · rw [hd, newAtom, mem_singleton] at h2
    have h3 : ({superstructure X} : ZFSet.{u}) ∈ pair (superstructure X) d := singleton_mem_pair
    rw [← h2] at h3
    exact mem_irrefl _ h3

theorem pair_superstructure_notMem_cumPow_base (c : ZFSet.{u}) (n : ℕ) :
    pair (superstructure X) c ∉ cumPow (base 𝓕 X) n := by
  cases n with
  | zero => exact pair_superstructure_notMem_base c
  | succ n =>
    exact fun h => singleton_superstructure_notMem_cumPow_base n
      (subset_cumPow_of_mem_succ h (pair_superstructure_notMem_base c) singleton_mem_pair)

theorem isBaseSet_base (hX : IsBaseSet X) : IsBaseSet (base 𝓕 X) := by
  intro y hy
  rcases mem_base_cases hy with h | ⟨c, rfl⟩
  · refine ⟨(hX y h).1, fun m hm hmy => ?_⟩
    obtain ⟨n, hn⟩ := mem_superstructure.1 hm
    exact (hX y h).2 m (cumPow_subset_superstructure n (mem_cumPow_of_rank_le n hn
      ((ZFSet.rank_lt_of_mem hmy).trans (rank_lt_of_mem_base h)).le)) hmy
  · refine ⟨fun h => notMem_empty (pair (superstructure X) c) (h ▸ mem_singleton.2 rfl),
      fun m hm hmy => ?_⟩
    obtain ⟨n, hn⟩ := mem_superstructure.1 hm
    rw [newAtom, mem_singleton] at hmy
    exact pair_superstructure_notMem_cumPow_base c n (hmy ▸ hn)

abbrev Rep (X : ZFSet.{u}) (I : Type v) := Σ n : ℕ, I → ↥(cumPow X n)

def Rep.lift (r : Rep X I) : I → ZFSet.{u} := fun i => (r.2 i).1

omit [Small.{u} I] in
theorem Rep.bdd (r : Rep X I) : Bdd 𝓕 X r.lift :=
  ⟨r.1, Eventually.of_forall fun i => (r.2 i).2⟩

omit [Small.{u} I] in
theorem exists_rep (hf : Bdd 𝓕 X f) : ∃ r : Rep X I, r.lift =ᶠ[𝓕] f := by
  obtain ⟨n, hn⟩ := hf
  have h0 : (∅ : ZFSet.{u}) ∈ cumPow X (n + 1) := mem_cumPow_succ_of_subset (empty_subset _)
  refine ⟨⟨n + 1, fun i =>
    if hi : f i ∈ cumPow X n then ⟨f i, cumPow_subset_succ n hi⟩ else ⟨∅, h0⟩⟩, ?_⟩
  filter_upwards [hn] with i hi
  simp [Rep.lift, hi]

variable (𝓕) in
def col (hX : IsBaseSet X) : (I → ZFSet.{u}) → ZFSet.{u} :=
  (E_wf (𝓕 := 𝓕) hX).fix fun g rec =>
    if Atomic 𝓕 X g then atomOf 𝓕 X g
    else ZFSet.range fun r : {r : Rep X I // E 𝓕 X r.lift g} => rec r.1.lift r.2

theorem col_eq (hX : IsBaseSet X) (g : I → ZFSet.{u}) :
    col 𝓕 hX g = if Atomic 𝓕 X g then atomOf 𝓕 X g
      else ZFSet.range fun r : {r : Rep X I // E 𝓕 X r.lift g} => col 𝓕 hX r.1.lift :=
  (E_wf (𝓕 := 𝓕) hX).fix_eq _ g

theorem col_atomic (hX : IsBaseSet X) (hg : Atomic 𝓕 X g) : col 𝓕 hX g = atomOf 𝓕 X g := by
  rw [col_eq]
  simp only [hg, ↓reduceIte]

theorem col_not_atomic (hX : IsBaseSet X) (hg : ¬ Atomic 𝓕 X g) :
    col 𝓕 hX g = ZFSet.range fun r : {r : Rep X I // E 𝓕 X r.lift g} => col 𝓕 hX r.1.lift := by
  rw [col_eq]
  simp only [hg, ↓reduceIte]

omit [Small.{u} I] in
theorem E.congr_right (hfg : f =ᶠ[𝓕] g) (hE : E 𝓕 X h f) : E 𝓕 X h g :=
  ⟨hE.1, hE.2.1.congr hfg, by filter_upwards [hE.2.2, hfg] with i a b; rwa [← b]⟩

omit [Small.{u} I] in
theorem E.congr_left (hfg : f =ᶠ[𝓕] g) (hE : E 𝓕 X f h) : E 𝓕 X g h :=
  ⟨hE.1.congr hfg, hE.2.1, by filter_upwards [hE.2.2, hfg] with i a b; rwa [← b]⟩

theorem col_congr (hX : IsBaseSet X) (hfg : f =ᶠ[𝓕] g) : col 𝓕 hX f = col 𝓕 hX g := by
  by_cases hA : Atomic 𝓕 X f
  · rw [col_atomic hX hA, col_atomic hX (hA.congr hfg), atomOf_congr hfg]
  · rw [col_not_atomic hX hA, col_not_atomic hX fun hg => hA (hg.congr hfg.symm)]
    ext y
    rw [mem_range, mem_range]
    constructor
    · rintro ⟨⟨r, hr⟩, rfl⟩
      exact ⟨⟨r, hr.congr_right hfg⟩, rfl⟩
    · rintro ⟨⟨r, hr⟩, rfl⟩
      exact ⟨⟨r, hr.congr_right hfg.symm⟩, rfl⟩

theorem mem_col (hX : IsBaseSet X) (hg : ¬ Atomic 𝓕 X g) {y : ZFSet.{u}} :
    y ∈ col 𝓕 hX g ↔ ∃ f, E 𝓕 X f g ∧ col 𝓕 hX f = y := by
  rw [col_not_atomic hX hg, mem_range]
  constructor
  · rintro ⟨⟨r, hr⟩, rfl⟩
    exact ⟨_, hr, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨r, hr⟩ := exists_rep hf.1
    exact ⟨⟨r, hf.congr_left hr.symm⟩, col_congr hX hr⟩

theorem col_mem_cumPow (hX : IsBaseSet X) :
    ∀ (n : ℕ) {f : I → ZFSet.{u}}, (∀ᶠ i in 𝓕, f i ∈ cumPow X n) →
      col 𝓕 hX f ∈ cumPow (base 𝓕 X) n
  | 0, f, hf => by
    rw [col_atomic hX hf]
    exact atomOf_mem_base hf
  | n + 1, f, hf => by
    by_cases hA : Atomic 𝓕 X f
    · rw [col_atomic hX hA]
      exact cumPow_mono (Nat.zero_le _) (atomOf_mem_base hA)
    · refine mem_cumPow_succ_of_subset fun y hy => ?_
      obtain ⟨h, hE, rfl⟩ := (mem_col hX hA).1 hy
      refine col_mem_cumPow hX n ?_
      filter_upwards [hf, hE.2.2, hE.1.eventually_mem] with i h1 h2 h3
      exact mem_cumPow_of_mem hX h1 h2 h3

theorem col_mem (hX : IsBaseSet X) (hf : Bdd 𝓕 X f) :
    col 𝓕 hX f ∈ superstructure (base 𝓕 X) := by
  obtain ⟨n, hn⟩ := hf
  exact cumPow_subset_superstructure n (col_mem_cumPow hX n hn)

theorem isIndividual_col (hX : IsBaseSet X) (hf : Atomic 𝓕 X f) :
    IsIndividual (superstructure (base 𝓕 X)) (col 𝓕 hX f) := by
  rw [col_atomic hX hf]
  exact isBaseSet_base hX _ (atomOf_mem_base hf)

theorem col_ne_of_atomic_of_not (hX : IsBaseSet X) (hf : Atomic 𝓕 X f) (hg : ¬ Atomic 𝓕 X g) :
    col 𝓕 hX f ≠ col 𝓕 hX g := fun h => by
  have hind := isIndividual_col hX hf
  rw [h] at hind
  obtain ⟨y, hy⟩ := (eq_empty_or_nonempty (col 𝓕 hX g)).resolve_left hind.1
  obtain ⟨h', hE, rfl⟩ := (mem_col hX hg).1 hy
  exact hind.2 _ (col_mem hX hE.1) hy

theorem eventuallyEq_of_col_eq_aux (hX : IsBaseSet X) (n : ℕ) :
    ∀ {f g : I → ZFSet.{u}}, (∀ᶠ i in 𝓕, f i ∈ cumPow X n) → (∀ᶠ i in 𝓕, g i ∈ cumPow X n) →
      col 𝓕 hX f = col 𝓕 hX g → f =ᶠ[𝓕] g := by
  induction n with
  | zero =>
    intro f g hf hg h
    rw [col_atomic hX hf, col_atomic hX hg] at h
    exact atomOf_inj hf hg h
  | succ n ih =>
    intro f g hf hg h
    by_cases hAf : Atomic 𝓕 X f
    · by_cases hAg : Atomic 𝓕 X g
      · rw [col_atomic hX hAf, col_atomic hX hAg] at h
        exact atomOf_inj hAf hAg h
      · exact absurd h (col_ne_of_atomic_of_not hX hAf hAg)
    · by_cases hAg : Atomic 𝓕 X g
      · exact absurd h.symm (col_ne_of_atomic_of_not hX hAg hAf)
      · have key : ∀ {f g : I → ZFSet.{u}}, (∀ᶠ i in 𝓕, f i ∈ cumPow X (n + 1)) →
            (∀ᶠ i in 𝓕, g i ∈ cumPow X (n + 1)) → ¬ Atomic 𝓕 X f → ¬ Atomic 𝓕 X g →
            col 𝓕 hX f = col 𝓕 hX g → ∀ h : I → ZFSet.{u}, (∀ᶠ i in 𝓕, h i ∈ cumPow X n) →
            (∀ᶠ i in 𝓕, h i ∈ f i) → ∀ᶠ i in 𝓕, h i ∈ g i := by
          intro f g hf hg hAf hAg h k hk hkf
          have hE : E 𝓕 X k f := ⟨⟨n, hk⟩, ⟨n + 1, hf⟩, hkf⟩
          have hmem : col 𝓕 hX k ∈ col 𝓕 hX g := h ▸ (mem_col hX hAf).2 ⟨k, hE, rfl⟩
          obtain ⟨k', hE', heq⟩ := (mem_col hX hAg).1 hmem
          have hk' : ∀ᶠ i in 𝓕, k' i ∈ cumPow X n := by
            filter_upwards [hg, hE'.2.2, hE'.1.eventually_mem] with i h1 h2 h3
            exact mem_cumPow_of_mem hX h1 h2 h3
          filter_upwards [ih hk' hk heq, hE'.2.2] with i h1 h2
          rwa [← h1]
        by_contra hne
        have hne' : ∀ᶠ i in 𝓕, f i ≠ g i := Ultrafilter.eventually_not.2 hne
        have hfs : ∀ᶠ i in 𝓕, f i ⊆ cumPow X n := by
          filter_upwards [hf, not_atomic_iff.1 hAf] with i h1 h2
          exact subset_cumPow_of_mem_succ h1 h2
        have hgs : ∀ᶠ i in 𝓕, g i ⊆ cumPow X n := by
          filter_upwards [hg, not_atomic_iff.1 hAg] with i h1 h2
          exact subset_cumPow_of_mem_succ h1 h2
        have hex : ∀ᶠ i in 𝓕, ∃ z, z ∈ cumPow X n ∧ ¬ (z ∈ f i ↔ z ∈ g i) := by
          filter_upwards [hne', hfs, hgs] with i h1 h2 h3
          by_contra hcon
          push Not at hcon
          refine h1 (ZFSet.ext fun z => ?_)
          by_cases hz : z ∈ cumPow X n
          · exact hcon z hz
          · exact ⟨fun hzf => absurd (h2 hzf) hz, fun hzg => absurd (h3 hzg) hz⟩
        obtain ⟨k, hk⟩ := Filter.skolem.1 hex
        have hkn : ∀ᶠ i in 𝓕, k i ∈ cumPow X n := hk.mono fun i hi => hi.1
        rcases Ultrafilter.eventually_or.1
          (Eventually.of_forall fun i => em (k i ∈ f i) : ∀ᶠ i in 𝓕, k i ∈ f i ∨ k i ∉ f i)
          with c | c
        · have := key hf hg hAf hAg h k hkn c
          have hF : ∀ᶠ _ in (𝓕 : Filter I), False := by
            filter_upwards [hk, c, this] with i h1 h2 h3
            exact h1.2 ⟨fun _ => h3, fun _ => h2⟩
          exact hF.exists.elim fun _ hh => hh
        · have c' : ∀ᶠ i in 𝓕, k i ∈ g i := by
            filter_upwards [hk, c] with i h1 h2
            by_contra h3
            exact h1.2 ⟨fun h => absurd h h2, fun h => absurd h h3⟩
          have := key hg hf hAg hAf h.symm k hkn c'
          have hF : ∀ᶠ _ in (𝓕 : Filter I), False := by
            filter_upwards [c, this] with i h1 h2
            exact h1 h2
          exact hF.exists.elim fun _ hh => hh

theorem col_eq_iff (hX : IsBaseSet X) (hf : Bdd 𝓕 X f) (hg : Bdd 𝓕 X g) :
    col 𝓕 hX f = col 𝓕 hX g ↔ f =ᶠ[𝓕] g := by
  refine ⟨fun h => ?_, col_congr hX⟩
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  exact eventuallyEq_of_col_eq_aux hX (max m n)
    (hm.mono fun i hi => cumPow_mono (le_max_left m n) hi)
    (hn.mono fun i hi => cumPow_mono (le_max_right m n) hi) h

theorem col_mem_col_iff (hX : IsBaseSet X) (hf : Bdd 𝓕 X f) (hg : Bdd 𝓕 X g) :
    col 𝓕 hX f ∈ col 𝓕 hX g ↔ ∀ᶠ i in 𝓕, f i ∈ g i := by
  by_cases hA : Atomic 𝓕 X g
  · constructor
    · exact fun h => absurd h ((isIndividual_col hX hA).2 _ (col_mem hX hf))
    · intro h
      have hF : ∀ᶠ _ in (𝓕 : Filter I), False := by
        filter_upwards [h, hA, hf.eventually_mem] with i h1 h2 h3
        exact (hX _ h2).2 _ h3 h1
      exact hF.exists.elim fun _ hh => hh.elim
  · rw [mem_col hX hA]
    constructor
    · rintro ⟨k, hE, heq⟩
      filter_upwards [(col_eq_iff hX hE.1 hf).1 heq, hE.2.2] with i h1 h2
      rwa [← h1]
    · exact fun h => ⟨f, ⟨hf, hg, h⟩, rfl⟩

theorem exists_of_mem_col (hX : IsBaseSet X) {a : ZFSet.{u}}
    (ha : a ∈ superstructure (base 𝓕 X)) (hag : a ∈ col 𝓕 hX g) :
    ∃ f, Bdd 𝓕 X f ∧ (∀ᶠ i in 𝓕, f i ∈ g i) ∧ col 𝓕 hX f = a := by
  by_cases hA : Atomic 𝓕 X g
  · exact absurd hag ((isIndividual_col hX hA).2 _ ha)
  · obtain ⟨f, hE, rfl⟩ := (mem_col hX hA).1 hag
    exact ⟨f, hE.1, hE.2.2, rfl⟩

theorem col_const_of_mem (hX : IsBaseSet X) {x : ZFSet.{u}} (hx : x ∈ X) :
    col 𝓕 hX (fun _ => x) = x := by
  rw [col_atomic hX (Eventually.of_forall fun _ => hx), atomOf_const hx]

theorem col_const_empty (hX : IsBaseSet X) : col 𝓕 hX (fun _ => ∅) = ∅ := by
  have hA : ¬ Atomic 𝓕 X (fun _ : I => (∅ : ZFSet.{u})) := fun h => by
    obtain ⟨_, hi⟩ := h.exists
    exact (hX _ hi).1 rfl
  rw [eq_empty]
  intro y hy
  obtain ⟨f, hE, -⟩ := (mem_col hX hA).1 hy
  obtain ⟨_, hi⟩ := hE.2.2.exists
  exact notMem_empty _ hi

theorem col_const_base (hX : IsBaseSet X) : col 𝓕 hX (fun _ => X) = base 𝓕 X := by
  have hA : ¬ Atomic 𝓕 X (fun _ : I => X) := fun h => by
    obtain ⟨_, hi⟩ := h.exists
    exact mem_irrefl _ hi
  ext y
  rw [mem_col hX hA]
  constructor
  · rintro ⟨f, hE, rfl⟩
    rw [col_atomic hX hE.2.2]
    exact atomOf_mem_base hE.2.2
  · intro hy
    obtain ⟨f, hf, rfl⟩ := exists_atomic_of_mem_base hy
    exact ⟨f, ⟨hf.bdd, bdd_const base_mem_superstructure, hf⟩, col_atomic hX hf⟩

end BoundedUltrapower
end Goldblatt
