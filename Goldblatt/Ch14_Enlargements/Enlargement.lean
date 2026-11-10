import Goldblatt.Ch13_Universes

noncomputable section

namespace Goldblatt

open ZFSet
open scoped Classical

universe u

/-- finite intersection property -/
def FIP (A : ZFSet.{u}) : Prop :=
  ∀ s : Finset ZFSet.{u}, (∀ B ∈ s, B ∈ A) → ∃ y, ∀ B ∈ s, y ∈ B

/-- concurrent -/
def Concurrent (R : ZFSet.{u}) : Prop :=
  ∀ s : Finset ZFSet.{u}, (∀ x ∈ s, x ∈ dom R) → ∃ y, ∀ x ∈ s, pair x y ∈ R

/-- The set with the members of a finite set of sets. -/
def ofFinset (s : Finset ZFSet.{u}) : ZFSet.{u} := ZFSet.range fun x : s => x.1

@[simp]
theorem mem_ofFinset {s : Finset ZFSet.{u}} {x : ZFSet.{u}} : x ∈ ofFinset s ↔ x ∈ s := by
  simp [ofFinset]

theorem finite_ofFinset (s : Finset ZFSet.{u}) : (ofFinset s : Set ZFSet.{u}).Finite := by
  have : (ofFinset s : Set ZFSet.{u}) = ↑s := by
    ext x
    simp
  rw [this]
  exact s.finite_toSet

theorem finite_coe_singleton (a : ZFSet.{u}) : (({a} : ZFSet.{u}) : Set ZFSet.{u}).Finite :=
  (Set.finite_singleton a).subset fun _ hx => mem_singleton.1 hx

/-- membership relation -/
def memRel (A : ZFSet.{u}) : ZFSet.{u} :=
  (prod A (finPow A)).sep fun p => ∃ a Z, p = pair a Z ∧ a ∈ Z

theorem pair_mem_memRel {A a Z : ZFSet.{u}} :
    pair a Z ∈ memRel A ↔ a ∈ A ∧ Z ∈ finPow A ∧ a ∈ Z := by
  rw [memRel, mem_sep, pair_mem_prod]
  constructor
  · rintro ⟨⟨h1, h2⟩, a', Z', e, h3⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.1 e
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, a, Z, rfl, h3⟩

theorem dom_memRel (A : ZFSet.{u}) : dom (memRel A) = A := by
  ext a
  constructor
  · intro h
    obtain ⟨Z, hZ⟩ := mem_dom.1 h
    exact (pair_mem_memRel.1 hZ).1
  · intro h
    exact mem_dom.2 ⟨{a}, pair_mem_memRel.2 ⟨h, mem_finPow.2 ⟨fun x hx => by
      rwa [mem_singleton.1 hx], finite_coe_singleton a⟩, mem_singleton.2 rfl⟩⟩

theorem concurrent_memRel (A : ZFSet.{u}) : Concurrent (memRel A) := fun s hs => by
  rw [dom_memRel] at hs
  exact ⟨ofFinset s, fun x hx => pair_mem_memRel.2 ⟨hs x hx, mem_finPow.2
    ⟨fun y hy => hs y (mem_ofFinset.1 hy), finite_ofFinset s⟩, mem_ofFinset.2 hx⟩⟩

/-- nonidentity relation -/
def neRel (A : ZFSet.{u}) : ZFSet.{u} :=
  (prod A A).sep fun p => ∃ a y, p = pair a y ∧ a ≠ y

theorem pair_mem_neRel {A a y : ZFSet.{u}} : pair a y ∈ neRel A ↔ a ∈ A ∧ y ∈ A ∧ a ≠ y := by
  rw [neRel, mem_sep, pair_mem_prod]
  constructor
  · rintro ⟨⟨h1, h2⟩, a', y', e, h3⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.1 e
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, a, y, rfl, h3⟩

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

namespace NonstandardFramework

open Formula Term

variable (F : NonstandardFramework.{u}) {A B R : ZFSet.{u}}

/-- enlargement -/
def IsEnlargement : Prop :=
  ∀ A, IsSetOf F.U A → (∀ B ∈ A, IsSetOf F.U B) → FIP A → ∃ b ∈ F.U', ∀ B ∈ A, b ∈ F.star B

/-- concurrent relations have bounds -/
def ConcurrentBound : Prop :=
  ∀ R, IsSetOf F.U R → RelIn F.U R → Concurrent R →
    ∃ b ∈ F.U', ∀ x ∈ dom R, pair (F.star x) b ∈ F.star R

/-- hyperfinite approximation -/
def HyperfiniteApprox : Prop :=
  ∀ A, IsSetOf F.U A → ∃ B ∈ F.star (finPow A), F.im A ⊆ B

variable {F}

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
theorem enlargement_tfae : List.TFAE [F.IsEnlargement, F.ConcurrentBound, F.HyperfiniteApprox] := by
  tfae_have 1 → 2 := IsEnlargement.concurrentBound
  tfae_have 2 → 3 := ConcurrentBound.hyperfiniteApprox
  tfae_have 3 → 1 := HyperfiniteApprox.isEnlargement
  tfae_finish

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

theorem IsEnlargement.exists_nonstandard_mem_star (hE : F.IsEnlargement) (hA : IsSetOf F.U A)
    (hinf : (A : Set ZFSet.{u}).Infinite) : ∃ b ∈ F.star A, F.Nonstandard b := by
  obtain ⟨b, hb, hbim⟩ := hE.exists_mem_star_notMem_im hA hinf
  exact ⟨b, hb, F.star_subset_U' hA hb, fun hs => hbim ((F.mem_im_iff hA).2 ⟨hb, hs⟩)⟩

theorem IsEnlargement.ssubset_star (hE : F.IsEnlargement) (hAX : A ⊆ F.X)
    (hinf : (A : Set ZFSet.{u}).Infinite) : A ⊆ F.star A ∧ ∃ b ∈ F.star A, b ∉ A := by
  have hA := F.hU.isSetOf_of_subset F.isUniverseOver.base_isSetOf hAX
  obtain ⟨b, hb, hbim⟩ := hE.exists_mem_star_notMem_im hA hinf
  rw [F.im_eq_of_subset_base hAX] at hbim
  exact ⟨(F.subset_star_of_subset_base hAX).1, b, hb, hbim⟩

theorem IsEnlargement.exists_hyperfinite (hE : F.IsEnlargement) (hA : IsSetOf F.U A) :
    ∃ B, F.Hyperfinite B ∧ F.im A ⊆ B ∧ B ⊆ F.star A := by
  obtain ⟨B, hB, him⟩ := hE.concurrentBound.hyperfiniteApprox A hA
  exact ⟨B, ⟨A, hA, hB⟩, him, (F.internal_subset_of_mem_star_finPow hA hB).1⟩

end NonstandardFramework

namespace RealFramework

variable (F : RealFramework.{u})

theorem infinite_N : (F.N : Set ZFSet.{u}).Infinite := by
  have : (F.N : Set ZFSet.{u}) = Set.range F.nat := by
    ext x
    simp [N]
  rw [this]
  exact Set.infinite_range_of_injective F.nat_injective

variable {F}

theorem exists_nonstandard_nat (hE : F.IsEnlargement) : ∃ n, n ∈ F.star F.N ∧ n ∉ F.N := by
  obtain ⟨b, hb, hbim⟩ := hE.exists_mem_star_notMem_im F.isSetOf_N F.infinite_N
  rw [F.im_N_im_R.1] at hbim
  exact ⟨b, hb, hbim⟩

theorem exists_pos_infinitesimal (hE : F.IsEnlargement) :
    ∃ b ∈ F.star F.R, ∀ r : ℝ, 0 < r →
      (pair (F.real 0) b ∈ F.star F.Le ∧ b ≠ F.real 0) ∧
        (pair b (F.real r) ∈ F.star F.Le ∧ b ≠ F.real r) := by
  set 𝒜 : ZFSet.{u} :=
    ZFSet.range fun r : {r : ℝ // 0 < r} => ooIn F.R F.Le (F.real 0) (F.real r.1) with h𝒜def
  have hsets : ∀ B ∈ 𝒜, IsSetOf F.U B := fun B hB => by
    obtain ⟨r, rfl⟩ := mem_range.1 hB
    exact F.hU.isSetOf_sep F.isSetOf_R _
  have h𝒜 : IsSetOf F.U 𝒜 :=
    F.hU.isSetOf_of_subset (F.hU.isSetOf_powerset F.isSetOf_R) fun B hB => by
      obtain ⟨r, rfl⟩ := mem_range.1 hB
      exact mem_powerset.2 sep_subset
  have hfip : FIP 𝒜 := fun s hs => by
    choose r hr using fun B : {B // B ∈ 𝒜} => mem_range.1 B.2
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
    refine ⟨F.real (m / 2), fun B hB => ?_⟩
    have hle : m ≤ g ⟨B, hB⟩ := Finset.min'_le _ _
      (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨B, hB⟩, Finset.mem_attach _ _, rfl⟩))
    have e := hr ⟨B, hs B hB⟩
    simp only at e
    rw [← e, ooIn, mem_sep]
    refine ⟨F.mem_R.2 ⟨_, rfl⟩, ⟨F.pair_mem_Le.2 (by linarith), fun h => ?_⟩,
      ⟨F.pair_mem_Le.2 (by simp only [g] at hle; linarith), fun h => ?_⟩⟩
    · have := F.real_injective h
      linarith
    · have := F.real_injective h
      simp only [g] at hle
      linarith
  obtain ⟨b, -, hb⟩ := hE 𝒜 h𝒜 hsets hfip
  have key : ∀ r : ℝ, 0 < r → b ∈ ooIn (F.star F.R) (F.star F.Le) (F.real 0) (F.real r) :=
    fun r hr => by
      rw [← F.star_ooIn]
      exact hb _ (mem_range.2 ⟨⟨r, hr⟩, rfl⟩)
  exact ⟨b, (mem_sep.1 (key 1 one_pos)).1, fun r hr => (mem_sep.1 (key r hr)).2⟩

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

end Goldblatt
