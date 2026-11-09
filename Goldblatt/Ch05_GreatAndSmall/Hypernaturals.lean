import Goldblatt.Ch05_GreatAndSmall.Shadows

/-!
# 5 (part 3). Hypernaturals, Hyperintegers and Hyperprimes: Sections 5.10 to 5.12

This is the third of three parts of Chapter 5 (the overview is on the chapter page
{lit}`Goldblatt.Ch05_GreatAndSmall`). It describes the order structure of the hypernatural
numbers and of the hyperintegers, develops divisibility and prime factors in the hypernaturals,
and gives the nonstandard version of Euclid's proof that there are infinitely many primes.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## 5.10 The Hypernaturals

The hypernaturals are closed under addition and multiplication (Chapter 3). The limited
hypernaturals are exactly the standard natural numbers, so every nonstandard hypernatural is
unlimited and exceeds every standard one. The hypernaturals at limited distance from an
unlimited hypernatural $`K` form a copy of the integers, the galaxy of $`K` within the
hypernaturals. These galaxies are ordered, and the order has no largest element, no smallest
unlimited element, and is dense. So, in order, the hypernaturals are the standard naturals and
then a family of blocks, each ordered like the integers; the family of blocks is dense and has
neither a least nor a greatest block.

Three facts in this section are supplements that Section 5.10 does not state: every
nonnegative hyperreal has a hypernatural integer part
({lit}`exists_hyperNat_le_lt_add_one`), and the set of unlimited hypernaturals has no least
element ({lit}`exists_lt_of_mem_unlimitedHyperNat`,
{lit}`not_exists_isLeast_unlimitedHyperNat`); the book proves only the weaker-looking fact
that there is no smallest unlimited galaxy. The characterisation of the limited hyperintegers
({lit}`limited_hyperInt_iff`) belongs to Exercise 5.11(1) but is proved here, because the
corresponding fact for hypernaturals is derived from it.

Statements about hypernaturals are proved from representing sequences of natural numbers; the
class of such a sequence is written {lit}`hnat k`.
-/

section Hypernaturals

variable {K H M N x : ℝ*}

/-- The hypernatural number represented by a sequence of natural numbers. -/
def hnat (k : ℕ → ℕ) : ℝ* := Hyperreal.ofSeq fun n => (k n : ℝ)

/-- The hyperinteger represented by a sequence of integers. -/
def hint (z : ℕ → ℤ) : ℝ* := Hyperreal.ofSeq fun n => (z n : ℝ)

/-- The class of a sequence of natural numbers is a hypernatural. -/
theorem hnat_mem_hyperNat (k : ℕ → ℕ) : hnat k ∈ ℕ* := mem_hyperNat_iff.2 ⟨k, rfl⟩

/-- The class of a sequence of integers is a hyperinteger. -/
theorem hint_mem_hyperInt (z : ℕ → ℤ) : hint z ∈ ℤ* := mem_hyperInt_iff.2 ⟨z, rfl⟩

/-- Every hypernatural is represented by a sequence of natural numbers. -/
theorem exists_hnat_eq (hK : K ∈ ℕ*) : ∃ k : ℕ → ℕ, K = hnat k := mem_hyperNat_iff.1 hK

/-- Every hyperinteger is represented by a sequence of integers. -/
theorem exists_hint_eq (hK : K ∈ ℤ*) : ∃ z : ℕ → ℤ, K = hint z := mem_hyperInt_iff.1 hK

/-- Two sequences of natural numbers represent the same hypernatural exactly when they agree
almost everywhere. -/
theorem hnat_eq_hnat_iff {k l : ℕ → ℕ} :
    hnat k = hnat l ↔ ∀ᶠ n in hyperfilter ℕ, k n = l n := by
  rw [hnat, hnat, ofSeq_eq_ofSeq_iff]
  simp only [Nat.cast_inj]

/-- Strict order between classes of sequences of natural numbers is strict order of almost all
terms. -/
theorem hnat_lt_hnat_iff {k l : ℕ → ℕ} :
    hnat k < hnat l ↔ ∀ᶠ n in hyperfilter ℕ, k n < l n := by
  rw [hnat, hnat, ofSeq_lt_ofSeq_iff]
  simp only [Nat.cast_lt]

/-- Order between classes of sequences of natural numbers is order of almost all terms. -/
theorem hnat_le_hnat_iff {k l : ℕ → ℕ} :
    hnat k ≤ hnat l ↔ ∀ᶠ n in hyperfilter ℕ, k n ≤ l n := by
  rw [hnat, hnat, ofSeq_le_ofSeq_iff]
  simp only [Nat.cast_le]

/-- Two sequences of integers represent the same hyperinteger exactly when they agree almost
everywhere. -/
theorem hint_eq_hint_iff {z w : ℕ → ℤ} :
    hint z = hint w ↔ ∀ᶠ n in hyperfilter ℕ, z n = w n := by
  rw [hint, hint, ofSeq_eq_ofSeq_iff]
  simp only [Int.cast_inj]

/-- Order between classes of sequences of integers is order of almost all terms. -/
theorem hint_le_hint_iff {z w : ℕ → ℤ} :
    hint z ≤ hint w ↔ ∀ᶠ n in hyperfilter ℕ, z n ≤ w n := by
  rw [hint, hint, ofSeq_le_ofSeq_iff]
  simp only [Int.cast_le]

/-- Classes of sequences of natural numbers are added termwise. -/
theorem hnat_add (k l : ℕ → ℕ) : hnat k + hnat l = hnat fun n => k n + l n := by
  change Hyperreal.ofSeq (fun n => (k n : ℝ) + (l n : ℝ)) = _
  rw [hnat, ofSeq_eq_ofSeq_iff]
  exact Eventually.of_forall fun n => by push_cast; rfl

/-- Classes of sequences of natural numbers are multiplied termwise. -/
theorem hnat_mul (k l : ℕ → ℕ) : hnat k * hnat l = hnat fun n => k n * l n := by
  change Hyperreal.ofSeq (fun n => (k n : ℝ) * (l n : ℝ)) = _
  rw [hnat, ofSeq_eq_ofSeq_iff]
  exact Eventually.of_forall fun n => by push_cast; rfl

/-- A natural number, as a hyperreal, is the class of the constant sequence. -/
theorem natCast_eq_hnat (m : ℕ) : (m : ℝ*) = hnat fun _ => m := rfl

/-- An integer, as a hyperreal, is the class of the constant sequence. -/
theorem intCast_eq_hint (m : ℤ) : (m : ℝ*) = hint fun _ => m := rfl

/-- The class of the constant sequence $`0` of natural numbers is $`0`. -/
@[simp] theorem hnat_const_zero : hnat (fun _ => 0) = 0 := by
  rw [← natCast_eq_hnat, Nat.cast_zero]

/-- The class of the constant sequence $`1` of natural numbers is $`1`. -/
@[simp] theorem hnat_const_one : hnat (fun _ => 1) = 1 := by
  rw [← natCast_eq_hnat, Nat.cast_one]

/-- The class of the constant sequence $`0` of integers is $`0`. -/
@[simp] theorem hint_const_zero : hint (fun _ => 0) = 0 := by
  rw [← intCast_eq_hint, Int.cast_zero]

/-- A sequence of natural numbers, read as a sequence of integers, has the same class. -/
theorem hint_natCast (k : ℕ → ℕ) : hint (fun n => (k n : ℤ)) = hnat k := by
  rw [hint, hnat, ofSeq_eq_ofSeq_iff]
  exact Eventually.of_forall fun n => by push_cast; rfl

/-- **Section 5.10.** The hypernaturals are closed under addition and multiplication. (This
was proved in Chapter 3 by transfer of closure of the natural numbers.) -/
theorem hyperNat_add_mul_mem (hK : K ∈ ℕ*) (hH : H ∈ ℕ*) : K + H ∈ ℕ* ∧ K * H ∈ ℕ* :=
  ⟨add_mem_hyperNat hK hH, mul_mem_hyperNat hK hH⟩

/-- A hyperreal is a hypernatural exactly when it is a nonnegative hyperinteger. -/
theorem mem_hyperNat_iff_hyperInt_nonneg : x ∈ ℕ* ↔ x ∈ ℤ* ∧ 0 ≤ x := by
  constructor
  · exact fun h => ⟨hyperNat_subset_hyperInt h, hyperNat_nonneg h⟩
  · rintro ⟨hz, h0⟩
    obtain ⟨z, rfl⟩ := exists_hint_eq hz
    have h0' : ∀ᶠ n in hyperfilter ℕ, 0 ≤ z n := by
      have : hint (fun _ => 0) ≤ hint z := by rw [hint_const_zero]; exact h0
      exact hint_le_hint_iff.1 this
    have : hint z = hnat fun n => (z n).toNat := by
      rw [← hint_natCast, hint_eq_hint_iff]
      exact h0'.mono fun n hn => (Int.toNat_of_nonneg hn).symm
    rw [this]
    exact hnat_mem_hyperNat _

/-- **Exercise 5.11(1), limited hyperintegers** (placed in the Section 5.10 part of the file
because {lit}`limited_hyperNat_iff` uses it). The only limited hyperintegers are the
standard integers. If $`|k| < m` for a standard $`m`, then by transfer $`k` is one of the
finitely many integers strictly between $`-m` and $`m`. -/
theorem limited_hyperInt_iff (hK : K ∈ ℤ*) : Limited K ↔ ∃ n : ℤ, K = n := by
  constructor
  · intro hl
    obtain ⟨m, hm⟩ := limited_iff_exists_nat.1 hl
    obtain ⟨z, rfl⟩ := exists_hint_eq hK
    have h1 : ∀ᶠ n in hyperfilter ℕ, |(z n : ℝ)| < m := by
      have : Hyperreal.ofSeq (fun n => |(z n : ℝ)|) < Hyperreal.ofSeq (fun _ => (m : ℝ)) := hm
      exact ofSeq_lt_ofSeq_iff.1 this
    have h2 : ∀ᶠ n in hyperfilter ℕ, ∃ i : Set.Ioo (-(m : ℤ)) m, z n = i :=
      h1.mono fun n hn => by
        have : |z n| < (m : ℤ) := by exact_mod_cast hn
        exact ⟨⟨z n, abs_lt.1 this⟩, rfl⟩
    obtain ⟨i, hi⟩ := almostAll_exists_finite.1 h2
    exact ⟨i, by rw [intCast_eq_hint, hint_eq_hint_iff]; exact hi⟩
  · rintro ⟨n, rfl⟩
    exact limited_intCast n

/-- **Section 5.10.** The only limited hypernaturals are the members of $`\mathbb N`. -/
theorem limited_hyperNat_iff (hK : K ∈ ℕ*) : Limited K ↔ ∃ n : ℕ, K = n := by
  constructor
  · intro hl
    obtain ⟨z, rfl⟩ := (limited_hyperInt_iff (hyperNat_subset_hyperInt hK)).1 hl
    have h0 : (0 : ℝ*) ≤ (z : ℝ*) := hyperNat_nonneg hK
    have hz : 0 ≤ z := by exact_mod_cast h0
    exact ⟨z.toNat, by
      rw [← Int.cast_natCast (R := ℝ*), Int.toNat_of_nonneg hz]⟩
  · rintro ⟨n, rfl⟩
    exact limited_natCast n

/-- **Section 5.10.** Every nonstandard hypernatural is unlimited. -/
theorem unlimited_of_mem_hyperNat_of_notMem_range (hK : K ∈ ℕ*)
    (h : K ∉ range ((↑) : ℕ → ℝ*)) : Unlimited K :=
  not_limited_iff_unlimited.1 fun hl =>
    h (by obtain ⟨n, rfl⟩ := (limited_hyperNat_iff hK).1 hl; exact ⟨n, rfl⟩)

/-- An unlimited hypernatural is positive unlimited. -/
theorem posUnlimited_of_mem_hyperNat (hK : K ∈ ℕ*) (hU : Unlimited K) : PosUnlimited K := by
  rcases hU with h | h
  · exact h
  · exact absurd (h 0) (not_lt.2 (by simpa using hyperNat_nonneg hK))

/-- **Section 5.10.** Every nonstandard hypernatural is greater than all members of
$`\mathbb N`. -/
theorem natCast_lt_of_mem_hyperNat_of_notMem_range (hK : K ∈ ℕ*)
    (h : K ∉ range ((↑) : ℕ → ℝ*)) (n : ℕ) : (n : ℝ*) < K :=
  posUnlimited_of_mem_hyperNat hK (unlimited_of_mem_hyperNat_of_notMem_range hK h) n

/-- **Section 5.1 and 5.10.** The set $`{}^*\mathbb N_\infty = {}^*\mathbb N - \mathbb N` of
unlimited hypernaturals. -/
def unlimitedHyperNat : Set ℝ* := ℕ* \ range ((↑) : ℕ → ℝ*)

/-- **Section 5.10.** $`{}^*\mathbb N - \mathbb N` is the set of unlimited members of
$`{}^*\mathbb N`, in the notation $`X_\infty` of Section 5.1. -/
theorem unlimitedHyperNat_eq : unlimitedHyperNat = unlimitedPart ℕ* := by
  ext K
  constructor
  · rintro ⟨hK, h⟩
    exact ⟨hK, unlimited_of_mem_hyperNat_of_notMem_range hK h⟩
  · rintro ⟨hK, hU⟩
    refine ⟨hK, ?_⟩
    rintro ⟨n, rfl⟩
    exact hU.not_limited (limited_natCast n)

/-- The members of the set of unlimited hypernaturals are the hypernaturals that are unlimited.
-/
theorem mem_unlimitedHyperNat : K ∈ unlimitedHyperNat ↔ K ∈ ℕ* ∧ Unlimited K := by
  rw [unlimitedHyperNat_eq]
  rfl

/-- **Section 5.10, non-vacuity.** Unlimited hypernaturals exist: $`\omega` is one. -/
theorem omega_mem_unlimitedHyperNat : (ω : ℝ*) ∈ unlimitedHyperNat :=
  mem_unlimitedHyperNat.2 ⟨omega_mem_hyperNat, unlimited_omega⟩

/-- **Section 5.10, supplement (not stated in the book).** Every nonnegative hyperreal lies
within $`1` of a hypernatural: there is a hypernatural $`N` with $`N \le x < N + 1`. This is
the transfer of the existence of the integer part. -/
theorem exists_hyperNat_le_lt_add_one (hx : 0 ≤ x) : ∃ N ∈ ℕ*, N ≤ x ∧ x < N + 1 :=
  ⟨hfloor x, hfloor_mem_hyperNat hx, hfloor_le x, lt_hfloor_add_one x⟩

/-- Two hyperintegers that differ are at least $`1` apart. -/
theorem add_one_le_of_lt_of_mem_hyperInt (hK : K ∈ ℤ*) (hH : H ∈ ℤ*) (h : K < H) :
    K + 1 ≤ H := by
  obtain ⟨z, rfl⟩ := exists_hint_eq hK
  obtain ⟨w, rfl⟩ := exists_hint_eq hH
  have h' : ∀ᶠ n in hyperfilter ℕ, (z n : ℝ) < w n := ofSeq_lt_ofSeq_iff.1 h
  change Hyperreal.ofSeq (fun n => (z n : ℝ) + 1) ≤ Hyperreal.ofSeq (fun n => (w n : ℝ))
  rw [ofSeq_le_ofSeq_iff]
  exact h'.mono fun n hn => by
    have : z n + 1 ≤ w n := Int.add_one_le_iff.2 (by exact_mod_cast hn)
    exact_mod_cast this

/-- The predecessor of a positive hypernatural is a hypernatural. -/
theorem sub_one_mem_hyperNat (hK : K ∈ ℕ*) (h0 : K ≠ 0) : K - 1 ∈ ℕ* := by
  rw [mem_hyperNat_iff_hyperInt_nonneg]
  have hz := hyperNat_subset_hyperInt hK
  have h1 : (1 : ℝ*) ∈ ℤ* := by simpa using intCast_mem_hyperInt 1
  refine ⟨hyperIntSubring.sub_mem hz h1, ?_⟩
  have h0' : (0 : ℝ*) ∈ ℤ* := by simpa using intCast_mem_hyperInt 0
  have := add_one_le_of_lt_of_mem_hyperInt h0' hz (lt_of_le_of_ne (hyperNat_nonneg hK) h0.symm)
  linarith

/-- **Section 5.10, supplement (not stated in the book).** Below every unlimited hypernatural
there is another: the predecessor of an unlimited hypernatural is an unlimited hypernatural.
The section itself proves only that there is no smallest unlimited galaxy
({lit}`exists_unlimited_hyperNat_galLT`). -/
theorem exists_lt_of_mem_unlimitedHyperNat (hK : K ∈ unlimitedHyperNat) :
    ∃ H ∈ unlimitedHyperNat, H < K := by
  rw [mem_unlimitedHyperNat] at hK
  refine ⟨K - 1, mem_unlimitedHyperNat.2 ⟨sub_one_mem_hyperNat hK.1 hK.2.ne_zero, ?_⟩,
    sub_one_lt K⟩
  rw [sub_eq_add_neg]
  exact hK.2.add_limited limited_one.neg

/-- **Section 5.10, supplement (not stated in the book).** The set
$`{}^*\mathbb N - \mathbb N` of unlimited hypernaturals has no least element. -/
theorem not_exists_isLeast_unlimitedHyperNat : ¬ ∃ K, IsLeast unlimitedHyperNat K := by
  rintro ⟨K, hK, hmin⟩
  obtain ⟨H, hH, hlt⟩ := exists_lt_of_mem_unlimitedHyperNat hK
  exact absurd (hmin hH) (not_le.2 hlt)

/-- **Section 5.10.** The galaxy $`\gamma(K) = \operatorname{gal}(K) \cap {}^*\mathbb N` of
$`K` within the hypernaturals. -/
def natGalaxy (K : ℝ*) : Set ℝ* := gal K ∩ ℕ*

/-- **Section 5.10.** For an unlimited hypernatural $`K`, the galaxy $`\gamma(K)` is
$`\{K\} \cup \{K \pm n : n \in \mathbb N\}`, here written as the set of all $`K + n` with
$`n` a standard integer. -/
theorem natGalaxy_eq_of_unlimited (hK : K ∈ ℕ*) (hU : Unlimited K) :
    natGalaxy K = {H | ∃ n : ℤ, H = K + n} := by
  ext H
  constructor
  · rintro ⟨hgal, hH⟩
    have hz : H - K ∈ ℤ* :=
      hyperIntSubring.sub_mem (hyperNat_subset_hyperInt hH) (hyperNat_subset_hyperInt hK)
    obtain ⟨n, hn⟩ := (limited_hyperInt_iff hz).1 (LimClose.symm hgal)
    exact ⟨n, by rw [← hn]; ring⟩
  · rintro ⟨n, rfl⟩
    refine ⟨?_, mem_hyperNat_iff_hyperInt_nonneg.2
      ⟨hyperIntSubring.add_mem (hyperNat_subset_hyperInt hK) (intCast_mem_hyperInt n), ?_⟩⟩
    · rw [mem_gal, limClose_iff]
      have : K - (K + n) = ((-n : ℤ) : ℝ*) := by push_cast; ring
      rw [this]
      exact limited_intCast _
    · have := posUnlimited_of_mem_hyperNat hK hU ((-n : ℤ) : ℝ)
      rw [ofReal_intCast] at this
      push_cast at this
      linarith

/-- **Section 5.10.** All members of the galaxy of an unlimited hypernatural are
unlimited. -/
theorem unlimited_of_mem_natGalaxy (hU : Unlimited K) (hH : H ∈ natGalaxy K) : Unlimited H := by
  have : H = K + (H - K) := by ring
  rw [this]
  exact hU.add_limited (LimClose.symm hH.1)

/-- **Section 5.10.** The galaxy of an unlimited hypernatural $`K` is a copy of
$`\mathbb Z` under the ordering: $`n \mapsto K + n` is an order isomorphism from the integers
onto $`\gamma(K)`. -/
def natGalaxyOrderIso (hK : K ∈ ℕ*) (hU : Unlimited K) : ℤ ≃o natGalaxy K :=
  StrictMono.orderIsoOfSurjective
    (fun n : ℤ => (⟨K + n, by rw [natGalaxy_eq_of_unlimited hK hU]; exact ⟨n, rfl⟩⟩ : natGalaxy K))
    (fun m n h => by
      change K + (m : ℝ*) < K + n
      have : (m : ℝ*) < n := by exact_mod_cast h
      linarith)
    (fun ⟨H, hH⟩ => by
      have hH' := hH
      rw [natGalaxy_eq_of_unlimited hK hU] at hH'
      obtain ⟨n, rfl⟩ := hH'
      exact ⟨n, rfl⟩)

/-- The order isomorphism between the integers and the galaxy of an unlimited hypernatural $`K`
sends $`n` to $`K + n`. -/
@[simp]
theorem natGalaxyOrderIso_apply (hK : K ∈ ℕ*) (hU : Unlimited K) (n : ℤ) :
    (natGalaxyOrderIso hK hU n : ℝ*) = K + n := rfl

/-- **Section 5.10.** The galaxy of a standard natural number within the hypernaturals is
$`\mathbb N` itself; in particular $`\mathbb N = \operatorname{gal}(1) \cap {}^*\mathbb N`. -/
theorem natGalaxy_natCast (m : ℕ) : natGalaxy (m : ℝ*) = range ((↑) : ℕ → ℝ*) := by
  ext H
  constructor
  · rintro ⟨hgal, hH⟩
    obtain ⟨n, rfl⟩ := (limited_hyperNat_iff hH).1 ((limited_natCast m).of_limClose hgal)
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    refine ⟨?_, natCast_mem_hyperNat n⟩
    rw [mem_gal, limClose_iff]
    exact (limited_natCast m).sub (limited_natCast n)

/-- **Section 5.10.** $`\gamma(K) = \gamma(H)` if and only if $`K \sim H`, for hypernaturals
$`K, H`. -/
theorem natGalaxy_eq_iff (hH : H ∈ ℕ*) : natGalaxy K = natGalaxy H ↔ K ∼ H := by
  constructor
  · intro h
    have : H ∈ natGalaxy K := h ▸ ⟨LimClose.refl H, hH⟩
    exact this.1
  · intro h
    rw [natGalaxy, natGalaxy, gal_eq_gal_iff.2 h]

/-- **Section 5.10.** The ordering of galaxies: $`\operatorname{gal}(b)` lies below
$`\operatorname{gal}(c)` when $`b < c` and $`b \not\sim c`, that is, when $`c - b` is positive
unlimited. For hypernaturals this is the book's $`\gamma(K) < \gamma(H)`. -/
def GalLT (b c : ℝ*) : Prop := b < c ∧ ¬ b ∼ c

/-- The galaxy of $`b` lies below the galaxy of $`c` exactly when $`c - b` is positive
unlimited. -/
theorem galLT_iff_posUnlimited_sub {b c : ℝ*} : GalLT b c ↔ PosUnlimited (c - b) := by
  rw [GalLT, posUnlimited_iff, limClose_iff, not_limited_iff_unlimited, sub_pos, and_comm,
    ← unlimited_neg_iff, neg_sub]

/-- If $`H` is positive unlimited and $`b` is limited then $`H + b` is positive unlimited. -/
theorem PosUnlimited.add_limited {b : ℝ*} (hH : PosUnlimited H) (hb : Limited b) :
    PosUnlimited (H + b) := by
  rw [posUnlimited_iff] at *
  refine ⟨hH.1.add_limited hb, ?_⟩
  obtain ⟨r, hr⟩ := limited_iff_abs_lt.1 hb
  have h1 := posUnlimited_iff.2 hH r
  have h2 := neg_abs_le b
  linarith

/-- Half of a positive unlimited number is positive unlimited. -/
theorem PosUnlimited.div_two (hH : PosUnlimited H) : PosUnlimited (H / 2) := by
  rw [posUnlimited_iff] at *
  refine ⟨?_, by linarith [hH.2]⟩
  have h2 : Appreciable (2 : ℝ*) := by simpa using appreciable_coe (two_ne_zero (α := ℝ))
  exact hH.1.div_appreciable h2

/-- **Section 5.10.** The ordering of galaxies does not depend on the representatives: the
galaxy of $`b` lies below the galaxy of $`c` exactly when every member of the first is less
than every member of the second. -/
theorem galLT_iff_forall_mem_gal {b c : ℝ*} :
    GalLT b c ↔ ∀ x ∈ gal b, ∀ y ∈ gal c, x < y := by
  constructor
  · intro h x hx y hy
    rw [galLT_iff_posUnlimited_sub] at h
    have h1 : Limited ((b - x) - (c - y)) := Limited.sub hx hy
    have h2 := h.add_limited h1
    have h3 : c - b + (b - x - (c - y)) = y - x := by ring
    rw [h3] at h2
    have := h2 0
    simp only [Hyperreal.coe_zero] at this
    linarith
  · intro h
    refine ⟨h b (LimClose.refl b) c (LimClose.refl c), fun hbc => ?_⟩
    exact lt_irrefl c (h c hbc c (LimClose.refl c))

/-- **Section 5.10, no greatest galaxy.** For an unlimited hypernatural $`K`,
$`\gamma(K) < \gamma(2K)`. -/
theorem galLT_two_mul (hK : K ∈ ℕ*) (hU : Unlimited K) : GalLT K (2 * K) := by
  rw [galLT_iff_posUnlimited_sub]
  have : 2 * K - K = K := by ring
  rw [this]
  exact posUnlimited_of_mem_hyperNat hK hU

/-- **Section 5.10, no greatest galaxy.** Above every galaxy of hypernaturals there is
another. -/
theorem exists_hyperNat_galLT (hK : K ∈ ℕ*) : ∃ H ∈ ℕ*, GalLT K H := by
  rcases limited_or_unlimited K with hl | hU
  · refine ⟨ω, omega_mem_hyperNat, galLT_iff_posUnlimited_sub.2 ?_⟩
    rw [sub_eq_add_neg]
    exact posUnlimited_omega.add_limited hl.neg
  · have h2 : (2 : ℝ*) ∈ ℕ* := by simpa using natCast_mem_hyperNat 2
    exact ⟨2 * K, mul_mem_hyperNat h2 hK, galLT_two_mul hK hU⟩

/-- **Section 5.10 and Exercise 5.11(1), parity by transfer.** Every hyperinteger $`K` is even
or odd in the hyperintegers: there is a hyperinteger $`M` with $`K = 2M` or
$`K + 1 = 2M`. -/
theorem exists_hyperInt_two_mul_or (hK : K ∈ ℤ*) : ∃ M ∈ ℤ*, K = 2 * M ∨ K + 1 = 2 * M := by
  obtain ⟨z, rfl⟩ := exists_hint_eq hK
  refine ⟨hint fun n => (z n + 1) / 2, hint_mem_hyperInt _, ?_⟩
  have h : ∀ᶠ n in hyperfilter ℕ,
      z n = 2 * ((z n + 1) / 2) ∨ z n + 1 = 2 * ((z n + 1) / 2) :=
    Eventually.of_forall fun n => by omega
  rcases almostAll_or.1 h with h | h
  · left
    change Hyperreal.ofSeq (fun n => (z n : ℝ)) =
      Hyperreal.ofSeq (fun n => 2 * (((z n + 1) / 2 : ℤ) : ℝ))
    rw [ofSeq_eq_ofSeq_iff]
    exact h.mono fun n hn => by exact_mod_cast hn
  · right
    change Hyperreal.ofSeq (fun n => (z n : ℝ) + 1) =
      Hyperreal.ofSeq (fun n => 2 * (((z n + 1) / 2 : ℤ) : ℝ))
    rw [ofSeq_eq_ofSeq_iff]
    exact h.mono fun n hn => by exact_mod_cast hn

/-- **Section 5.10, parity by transfer.** For every hypernatural $`K`, one of $`K` and
$`K + 1` is even: there is a hypernatural $`M` with $`K = 2M` or $`K + 1 = 2M`. -/
theorem exists_hyperNat_two_mul_or (hK : K ∈ ℕ*) : ∃ M ∈ ℕ*, K = 2 * M ∨ K + 1 = 2 * M := by
  obtain ⟨M, hM, h⟩ := exists_hyperInt_two_mul_or (hyperNat_subset_hyperInt hK)
  refine ⟨M, mem_hyperNat_iff_hyperInt_nonneg.2 ⟨hM, ?_⟩, h⟩
  have := hyperNat_nonneg hK
  rcases h with h | h <;> linarith

/-- **Section 5.10, no smallest unlimited galaxy.** Below the galaxy of every unlimited
hypernatural there is the galaxy of another unlimited hypernatural. Following the book, one of
$`K` and $`K + 1` is even, and half of it serves. -/
theorem exists_unlimited_hyperNat_galLT (hK : K ∈ ℕ*) (hU : Unlimited K) :
    ∃ H ∈ ℕ*, Unlimited H ∧ GalLT H K := by
  have hpos := posUnlimited_of_mem_hyperNat hK hU
  obtain ⟨M, hM, h⟩ := exists_hyperNat_two_mul_or hK
  refine ⟨M, hM, ?_, galLT_iff_posUnlimited_sub.2 ?_⟩
  · rcases h with h | h
    · have : M = K / 2 := by rw [h]; ring
      rw [this]
      exact Or.inl hpos.div_two
    · have : M = (K + 1) / 2 := by rw [h]; ring
      rw [this]
      exact Or.inl (hpos.add_limited limited_one).div_two
  · rcases h with h | h
    · have : K - M = K / 2 := by rw [h]; ring
      rw [this]
      exact hpos.div_two
    · have : K - M = (K + (-1)) / 2 := by
        have : K = 2 * M - 1 := by rw [← h]; ring
        rw [this]
        ring
      rw [this]
      exact (hpos.add_limited limited_one.neg).div_two

/-- **Section 5.10, density of the galaxies.** Between any two galaxies of hypernaturals
there is a third: if $`\gamma(K) < \gamma(H)` then
$`\gamma(K) < \gamma(M) < \gamma(H)` for some hypernatural $`M`, namely half of $`K + H` or
of $`K + H + 1`. -/
theorem exists_hyperNat_galLT_between (hK : K ∈ ℕ*) (hH : H ∈ ℕ*) (h : GalLT K H) :
    ∃ M ∈ ℕ*, GalLT K M ∧ GalLT M H := by
  rw [galLT_iff_posUnlimited_sub] at h
  obtain ⟨M, hM, hM'⟩ := exists_hyperNat_two_mul_or (add_mem_hyperNat hK hH)
  refine ⟨M, hM, galLT_iff_posUnlimited_sub.2 ?_, galLT_iff_posUnlimited_sub.2 ?_⟩
  · rcases hM' with e | e
    · have : M - K = (H - K) / 2 := by
        have : H = 2 * M - K := by rw [← e]; ring
        rw [this]
        ring
      rw [this]
      exact h.div_two
    · have : M - K = (H - K + 1) / 2 := by
        have : H = 2 * M - K - 1 := by rw [← e]; ring
        rw [this]
        ring
      rw [this]
      exact (h.add_limited limited_one).div_two
  · rcases hM' with e | e
    · have : H - M = (H - K) / 2 := by
        have : K = 2 * M - H := by rw [← e]; ring
        rw [this]
        ring
      rw [this]
      exact h.div_two
    · have : H - M = (H - K + (-1)) / 2 := by
        have : K = 2 * M - H - 1 := by rw [← e]; ring
        rw [this]
        ring
      rw [this]
      exact (h.add_limited limited_one.neg).div_two

/-- **Section 5.10, summary.** In order, the hypernaturals are the standard naturals and then a
family of blocks, each ordered like the integers; the family of blocks is dense and has
neither a least nor a greatest block. In detail: the galaxy of a standard number is
$`\mathbb N`; it lies below every unlimited galaxy; above every galaxy there is another; below
every unlimited galaxy there is another unlimited one; and between any two galaxies there is a
third. (That each unlimited galaxy is ordered like $`\mathbb Z` is
{lit}`natGalaxyOrderIso`.) -/
theorem hyperNat_order_structure :
    (∀ m : ℕ, natGalaxy (m : ℝ*) = range ((↑) : ℕ → ℝ*)) ∧
    (∀ m : ℕ, ∀ K ∈ unlimitedHyperNat, GalLT (m : ℝ*) K) ∧
    (∀ K ∈ ℕ*, ∃ H ∈ ℕ*, GalLT K H) ∧
    (∀ K ∈ unlimitedHyperNat, ∃ H ∈ unlimitedHyperNat, GalLT H K) ∧
    (∀ K ∈ ℕ*, ∀ H ∈ ℕ*, GalLT K H → ∃ M ∈ ℕ*, GalLT K M ∧ GalLT M H) := by
  refine ⟨natGalaxy_natCast, fun m K hK => ?_, fun K hK => exists_hyperNat_galLT hK,
    fun K hK => ?_, fun K hK H hH h => exists_hyperNat_galLT_between hK hH h⟩
  · rw [mem_unlimitedHyperNat] at hK
    rw [galLT_iff_posUnlimited_sub, sub_eq_add_neg]
    exact (posUnlimited_of_mem_hyperNat hK.1 hK.2).add_limited (limited_natCast m).neg
  · rw [mem_unlimitedHyperNat] at hK
    obtain ⟨H, hH, hU, hlt⟩ := exists_unlimited_hyperNat_galLT hK.1 hK.2
    exact ⟨H, mem_unlimitedHyperNat.2 ⟨hH, hU⟩, hlt⟩

end Hypernaturals

/-!
## 5.11 Exercises on Hyperintegers and Primes

The first exercise transposes the description of the hypernaturals to the hyperintegers: the
limited hyperintegers are the integers, every galaxy of hyperintegers is a copy of the
integers, and the galaxies are densely ordered without first or last member.

The remaining exercises concern divisibility. A hypernatural $`a` _divides_ $`b` when
$`b = a q` for some hypernatural $`q`. In terms of representing sequences this means that
almost all terms of the first sequence divide the corresponding terms of the second, which
reduces each exercise to a fact about natural numbers. The _hyperprimes_ are the members of
the enlargement of the set of prime numbers.
-/

section HyperintegersAndPrimes

variable {K H M N a b d q x : ℝ*}

/-- **Exercise 5.11(1).** The galaxy $`\operatorname{gal}(K) \cap {}^*\mathbb Z` of $`K`
within the hyperintegers. -/
def intGalaxy (K : ℝ*) : Set ℝ* := gal K ∩ ℤ*

/-- **Exercise 5.11(1).** The galaxy of a hyperinteger $`K` within the hyperintegers is
$`\{K + n : n \in \mathbb Z\}`. -/
theorem intGalaxy_eq (hK : K ∈ ℤ*) : intGalaxy K = {H | ∃ n : ℤ, H = K + n} := by
  ext H
  constructor
  · rintro ⟨hgal, hH⟩
    obtain ⟨n, hn⟩ := (limited_hyperInt_iff (hyperIntSubring.sub_mem hH hK)).1
      (LimClose.symm hgal)
    exact ⟨n, by rw [← hn]; ring⟩
  · rintro ⟨n, rfl⟩
    refine ⟨?_, hyperIntSubring.add_mem hK (intCast_mem_hyperInt n)⟩
    rw [mem_gal, limClose_iff]
    have : K - (K + n) = ((-n : ℤ) : ℝ*) := by push_cast; ring
    rw [this]
    exact limited_intCast _

/-- **Exercise 5.11(1).** The galaxy of a standard integer within the hyperintegers is
$`\mathbb Z`. -/
theorem intGalaxy_intCast (m : ℤ) : intGalaxy (m : ℝ*) = range ((↑) : ℤ → ℝ*) := by
  rw [intGalaxy_eq (intCast_mem_hyperInt m)]
  ext H
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨m + n, by push_cast; rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n - m, by push_cast; ring⟩

/-- **Exercise 5.11(1).** Every galaxy of hyperintegers is a copy of $`\mathbb Z` under the
ordering: $`n \mapsto K + n` is an order isomorphism from the integers onto it. -/
def intGalaxyOrderIso (hK : K ∈ ℤ*) : ℤ ≃o intGalaxy K :=
  StrictMono.orderIsoOfSurjective
    (fun n : ℤ => (⟨K + n, by rw [intGalaxy_eq hK]; exact ⟨n, rfl⟩⟩ : intGalaxy K))
    (fun m n h => by
      change K + (m : ℝ*) < K + n
      have : (m : ℝ*) < n := by exact_mod_cast h
      linarith)
    (fun ⟨H, hH⟩ => by
      have hH' := hH
      rw [intGalaxy_eq hK] at hH'
      obtain ⟨n, rfl⟩ := hH'
      exact ⟨n, rfl⟩)

/-- The order isomorphism between the integers and the galaxy of a hyperinteger $`K` sends $`n`
to $`K + n`. -/
@[simp]
theorem intGalaxyOrderIso_apply (hK : K ∈ ℤ*) (n : ℤ) :
    (intGalaxyOrderIso hK n : ℝ*) = K + n := rfl

/-- **Exercise 5.11(1), no last galaxy.** Above every galaxy of hyperintegers there is
another. -/
theorem exists_hyperInt_galLT (hK : K ∈ ℤ*) : ∃ H ∈ ℤ*, GalLT K H := by
  refine ⟨K + ω, hyperIntSubring.add_mem hK (hyperNat_subset_hyperInt omega_mem_hyperNat),
    galLT_iff_posUnlimited_sub.2 ?_⟩
  have : K + ω - K = ω := by ring
  rw [this]
  exact posUnlimited_omega

/-- **Exercise 5.11(1), no first galaxy.** Below every galaxy of hyperintegers there is
another. -/
theorem exists_hyperInt_galLT' (hK : K ∈ ℤ*) : ∃ H ∈ ℤ*, GalLT H K := by
  refine ⟨K - ω, hyperIntSubring.sub_mem hK (hyperNat_subset_hyperInt omega_mem_hyperNat),
    galLT_iff_posUnlimited_sub.2 ?_⟩
  have : K - (K - ω) = ω := by ring
  rw [this]
  exact posUnlimited_omega

/-- **Exercise 5.11(1), density.** Between any two galaxies of hyperintegers there is a
third. -/
theorem exists_hyperInt_galLT_between (hK : K ∈ ℤ*) (hH : H ∈ ℤ*) (h : GalLT K H) :
    ∃ M ∈ ℤ*, GalLT K M ∧ GalLT M H := by
  rw [galLT_iff_posUnlimited_sub] at h
  obtain ⟨M, hM, hM'⟩ := exists_hyperInt_two_mul_or (hyperIntSubring.add_mem hK hH)
  refine ⟨M, hM, galLT_iff_posUnlimited_sub.2 ?_, galLT_iff_posUnlimited_sub.2 ?_⟩
  · rcases hM' with e | e
    · have : M - K = (H - K) / 2 := by
        have : H = 2 * M - K := by rw [← e]; ring
        rw [this]
        ring
      rw [this]
      exact h.div_two
    · have : M - K = (H - K + 1) / 2 := by
        have : H = 2 * M - K - 1 := by rw [← e]; ring
        rw [this]
        ring
      rw [this]
      exact (h.add_limited limited_one).div_two
  · rcases hM' with e | e
    · have : H - M = (H - K) / 2 := by
        have : K = 2 * M - H := by rw [← e]; ring
        rw [this]
        ring
      rw [this]
      exact h.div_two
    · have : H - M = (H - K + (-1)) / 2 := by
        have : K = 2 * M - H - 1 := by rw [← e]; ring
        rw [this]
        ring
      rw [this]
      exact (h.add_limited limited_one.neg).div_two

/-- **Exercise 5.11(1), summary.** The ordering of the hyperintegers is a densely ordered set
of galaxies, each a copy of $`\mathbb Z`, with no first and no last galaxy; the standard
integers form one of the galaxies. -/
theorem hyperInt_order_structure :
    (∀ m : ℤ, intGalaxy (m : ℝ*) = range ((↑) : ℤ → ℝ*)) ∧
    (∀ K ∈ ℤ*, intGalaxy K = {H | ∃ n : ℤ, H = K + n}) ∧
    (∀ K ∈ ℤ*, ∃ H ∈ ℤ*, GalLT K H) ∧
    (∀ K ∈ ℤ*, ∃ H ∈ ℤ*, GalLT H K) ∧
    (∀ K ∈ ℤ*, ∀ H ∈ ℤ*, GalLT K H → ∃ M ∈ ℤ*, GalLT K M ∧ GalLT M H) :=
  ⟨intGalaxy_intCast, fun _ hK => intGalaxy_eq hK, fun _ hK => exists_hyperInt_galLT hK,
    fun _ hK => exists_hyperInt_galLT' hK,
    fun _ hK _ hH h => exists_hyperInt_galLT_between hK hH h⟩

/-- **Exercise 5.11(2).** Divisibility in the hypernaturals: $`a` divides $`b` in
$`{}^*\mathbb N` when $`b = a q` for some hypernatural $`q`. Written {lit}`a ∣ₕ b`. -/
def HDvd (a b : ℝ*) : Prop := ∃ q ∈ ℕ*, b = a * q

@[inherit_doc] scoped infix:50 " ∣ₕ " => HDvd

/-- **Exercise 5.11, divisibility by transfer.** For hypernaturals given by sequences of
natural numbers, $`[k]` divides $`[l]` if and only if $`k_n` divides $`l_n` for almost all
$`n`. -/
theorem hnat_hdvd_hnat_iff {k l : ℕ → ℕ} :
    hnat k ∣ₕ hnat l ↔ ∀ᶠ n in hyperfilter ℕ, k n ∣ l n := by
  constructor
  · rintro ⟨q, hq, h⟩
    obtain ⟨κ, rfl⟩ := exists_hnat_eq hq
    rw [hnat_mul, hnat_eq_hnat_iff] at h
    exact h.mono fun n hn => ⟨κ n, hn⟩
  · intro h
    refine ⟨hnat fun n => l n / k n, hnat_mem_hyperNat _, ?_⟩
    rw [hnat_mul, hnat_eq_hnat_iff]
    exact h.mono fun n hn => (Nat.mul_div_cancel' hn).symm

/-- A standard natural number $`m` divides the hypernatural $`[l]` if and only if $`m`
divides almost all $`l_n`. -/
theorem natCast_hdvd_hnat_iff {m : ℕ} {l : ℕ → ℕ} :
    (m : ℝ*) ∣ₕ hnat l ↔ ∀ᶠ n in hyperfilter ℕ, m ∣ l n := by
  rw [natCast_eq_hnat, hnat_hdvd_hnat_iff]

/-- Divisibility of standard natural numbers in the hypernaturals is ordinary
divisibility. -/
theorem natCast_hdvd_natCast_iff {m n : ℕ} : (m : ℝ*) ∣ₕ (n : ℝ*) ↔ m ∣ n := by
  rw [natCast_eq_hnat n, natCast_hdvd_hnat_iff, almostAll_const]

/-- Hypernatural divisibility is reflexive: the quotient is $`1`. -/
theorem hdvd_refl (a : ℝ*) : a ∣ₕ a :=
  ⟨1, by simpa using natCast_mem_hyperNat 1, by ring⟩

/-- The numbers divisible by $`1` in the hypernatural sense are exactly the hypernaturals. -/
theorem one_hdvd (a : ℝ*) : 1 ∣ₕ a ↔ a ∈ ℕ* := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro h
    exact ⟨a, h, by ring⟩

/-- Hypernatural divisibility is transitive. -/
theorem HDvd.trans (h₁ : a ∣ₕ b) (h₂ : b ∣ₕ d) : a ∣ₕ d := by
  obtain ⟨q, hq, rfl⟩ := h₁
  obtain ⟨r, hr, rfl⟩ := h₂
  exact ⟨q * r, mul_mem_hyperNat hq hr, by ring⟩

/-- **Exercise 5.11(2), first part.** For every hypernatural $`M` there is a positive
hypernatural $`N` that is divisible in $`{}^*\mathbb N` by all members of
$`\{1, 2, \dots, M\}`. The witness is the transfer of the factorial: if $`M = [m_n]` then
$`N = [m_n!]`. (Positivity is implicit in the book, where the natural numbers start at
$`1`; without it $`N = 0` would do.) -/
theorem exists_hyperNat_forall_le_hdvd (hM : M ∈ ℕ*) :
    ∃ N ∈ ℕ*, 0 < N ∧ ∀ k ∈ ℕ*, 1 ≤ k → k ≤ M → k ∣ₕ N := by
  obtain ⟨m, rfl⟩ := exists_hnat_eq hM
  refine ⟨hnat fun n => (m n).factorial, hnat_mem_hyperNat _, ?_, ?_⟩
  · have : hnat (fun _ => 0) < hnat fun n => (m n).factorial :=
      hnat_lt_hnat_iff.2 (Eventually.of_forall fun n => Nat.factorial_pos _)
    rwa [hnat_const_zero] at this
  · intro k hk h1 hkM
    obtain ⟨κ, rfl⟩ := exists_hnat_eq hk
    have h1' : ∀ᶠ n in hyperfilter ℕ, 1 ≤ κ n := by
      have : hnat (fun _ => 1) ≤ hnat κ := by rw [hnat_const_one]; exact h1
      exact hnat_le_hnat_iff.1 this
    have h2' : ∀ᶠ n in hyperfilter ℕ, κ n ≤ m n := hnat_le_hnat_iff.1 hkM
    rw [hnat_hdvd_hnat_iff]
    filter_upwards [h1', h2'] with n a1 a2 using Nat.dvd_factorial a1 a2

/-- **Exercise 5.11(2), second part.** There is a positive hypernatural number that is
divisible by every standard positive integer. -/
theorem exists_hyperNat_forall_nat_hdvd :
    ∃ N ∈ ℕ*, 0 < N ∧ ∀ n : ℕ, 0 < n → (n : ℝ*) ∣ₕ N := by
  obtain ⟨N, hN, hpos, h⟩ := exists_hyperNat_forall_le_hdvd omega_mem_hyperNat
  refine ⟨N, hN, hpos, fun n hn => h n (natCast_mem_hyperNat n) ?_ ?_⟩
  · exact_mod_cast hn
  · have := posUnlimited_omega n
    rw [ofReal_natCast] at this
    exact this.le

/-- **Exercise 5.11(3).** The set $`{}^*\Pi` of _hyperprimes_: the enlargement of the set
$`\Pi` of standard prime numbers. -/
def hyperPrime : Set ℝ* := ⋆((fun p : ℕ => (p : ℝ)) '' {p : ℕ | p.Prime})

/-- The hypernatural $`[k]` is a hyperprime if and only if almost all $`k_n` are prime. -/
theorem hnat_mem_hyperPrime_iff {k : ℕ → ℕ} :
    hnat k ∈ hyperPrime ↔ ∀ᶠ n in hyperfilter ℕ, (k n).Prime := by
  rw [hyperPrime, hnat, hyperreal_ofSeq_mem_starSet]
  refine eventually_congr (Eventually.of_forall fun n => ?_)
  constructor
  · rintro ⟨p, hp, h⟩
    have : p = k n := Nat.cast_injective (R := ℝ) h
    exact this ▸ hp
  · intro h
    exact ⟨k n, h, rfl⟩

/-- **Exercise 5.11(3).** Every hyperprime is a hypernatural. -/
theorem hyperPrime_subset_hyperNat : hyperPrime ⊆ ℕ* :=
  starSet_mono (by rintro _ ⟨p, -, rfl⟩; exact ⟨p, rfl⟩)

/-- **Exercise 5.11(3).** A standard natural number is a hyperprime exactly when it is
prime. -/
theorem natCast_mem_hyperPrime_iff {p : ℕ} : (p : ℝ*) ∈ hyperPrime ↔ p.Prime := by
  rw [natCast_eq_hnat, hnat_mem_hyperPrime_iff, almostAll_const]

/-- **Exercise 5.11(3)(a).** $`q \in {}^*\Pi` if and only if $`q` is a hypernatural, $`q > 1`,
and the only hypernatural divisors of $`q` are $`1` and $`q`. -/
theorem mem_hyperPrime_iff :
    q ∈ hyperPrime ↔ q ∈ ℕ* ∧ 1 < q ∧ ∀ d ∈ ℕ*, d ∣ₕ q → d = 1 ∨ d = q := by
  constructor
  · intro hq
    obtain ⟨k, rfl⟩ := exists_hnat_eq (hyperPrime_subset_hyperNat hq)
    have hk := hnat_mem_hyperPrime_iff.1 hq
    refine ⟨hnat_mem_hyperNat k, ?_, ?_⟩
    · have : hnat (fun _ => 1) < hnat k :=
        hnat_lt_hnat_iff.2 (hk.mono fun n hn => hn.one_lt)
      rwa [hnat_const_one] at this
    · intro d hd hdvd
      obtain ⟨δ, rfl⟩ := exists_hnat_eq hd
      have h1 := hnat_hdvd_hnat_iff.1 hdvd
      have h2 : ∀ᶠ n in hyperfilter ℕ, δ n = 1 ∨ δ n = k n := by
        filter_upwards [hk, h1] with n a1 a2 using a1.eq_one_or_self_of_dvd _ a2
      rcases almostAll_or.1 h2 with h | h
      · left
        rw [← hnat_const_one, hnat_eq_hnat_iff]
        exact h
      · right
        rw [hnat_eq_hnat_iff]
        exact h
  · rintro ⟨hq, h1, hdiv⟩
    obtain ⟨k, rfl⟩ := exists_hnat_eq hq
    rw [hnat_mem_hyperPrime_iff]
    by_contra hnp
    rw [← almostAll_not] at hnp
    have h1' : ∀ᶠ n in hyperfilter ℕ, 1 < k n := by
      have : hnat (fun _ => 1) < hnat k := by rw [hnat_const_one]; exact h1
      exact hnat_lt_hnat_iff.1 this
    -- the least prime factor of `k n` is a nontrivial factor for almost all `n`
    have hd := hdiv (hnat fun n => (k n).minFac) (hnat_mem_hyperNat _)
      (hnat_hdvd_hnat_iff.2 (Eventually.of_forall fun n => Nat.minFac_dvd _))
    rcases hd with hd | hd
    · rw [← hnat_const_one, hnat_eq_hnat_iff] at hd
      obtain ⟨n, a1, a2⟩ := (hd.and h1').exists
      exact absurd (Nat.minFac_eq_one_iff.1 a1) a2.ne'
    · rw [hnat_eq_hnat_iff] at hd
      obtain ⟨n, a1, a2, a3⟩ := (hd.and (hnp.and h1')).exists
      exact a2 (a1 ▸ Nat.minFac_prime a3.ne')

/-- **Exercise 5.11(3)(b).** If $`N \in {}^*\mathbb N` and $`N > 1`, then some hyperprime
divides $`N`. -/
theorem exists_hyperPrime_hdvd (hN : N ∈ ℕ*) (h1 : 1 < N) : ∃ p ∈ hyperPrime, p ∣ₕ N := by
  obtain ⟨k, rfl⟩ := exists_hnat_eq hN
  have h1' : ∀ᶠ n in hyperfilter ℕ, 1 < k n := by
    have : hnat (fun _ => 1) < hnat k := by rw [hnat_const_one]; exact h1
    exact hnat_lt_hnat_iff.1 this
  exact ⟨hnat fun n => (k n).minFac,
    hnat_mem_hyperPrime_iff.2 (h1'.mono fun n hn => Nat.minFac_prime hn.ne'),
    hnat_hdvd_hnat_iff.2 (Eventually.of_forall fun n => Nat.minFac_dvd _)⟩

/-- For hypernaturals given by sequences, the hyperreal power $`[p_n]^{[e_n]}` of
Exercise 5.2.1 is the hypernatural $`[p_n^{e_n}]`. -/
theorem hpow_hnat (p e : ℕ → ℕ) : hpow (hnat p) (hnat e) = hnat fun n => p n ^ e n := by
  rw [hnat, hnat, hpow_ofSeq_natCast, hnat, ofSeq_eq_ofSeq_iff]
  exact Eventually.of_forall fun n => by push_cast; rfl

/-- **Exercise 5.11(3)(c).** Let $`a, b \in {}^*\mathbb N`. If, for every hyperprime $`p` and
every hypernatural $`n`, the power $`p^n` divides $`a` exactly when it divides $`b`, then
$`a = b`. The power
$`p^n` with hypernatural exponent is the hyperreal power {name}`Goldblatt.hpow`. -/
theorem hyperNat_eq_of_forall_hyperPrime_pow_hdvd (ha : a ∈ ℕ*) (hb : b ∈ ℕ*)
    (h : ∀ p ∈ hyperPrime, ∀ n ∈ ℕ*, (hpow p n ∣ₕ a ↔ hpow p n ∣ₕ b)) : a = b := by
  obtain ⟨α, rfl⟩ := exists_hnat_eq ha
  obtain ⟨β, rfl⟩ := exists_hnat_eq hb
  by_contra hne
  rw [hnat_eq_hnat_iff, ← almostAll_not] at hne
  -- at almost every index some prime power divides exactly one of the two terms
  have hex : ∀ n, ∃ p e : ℕ, p.Prime ∧ (α n ≠ β n → ¬ (p ^ e ∣ α n ↔ p ^ e ∣ β n)) := by
    intro n
    by_cases hn : α n = β n
    · exact ⟨2, 0, Nat.prime_two, fun h => absurd hn h⟩
    · by_contra hcon
      push Not at hcon
      have hiff : ∀ p e : ℕ, p.Prime → (p ^ e ∣ α n ↔ p ^ e ∣ β n) := fun p e hp =>
        (hcon p e hp).2
      exact hn (Nat.dvd_antisymm
        ((Nat.dvd_iff_prime_pow_dvd_dvd _ _).2 fun p e hp hd => (hiff p e hp).1 hd)
        ((Nat.dvd_iff_prime_pow_dvd_dvd _ _).2 fun p e hp hd => (hiff p e hp).2 hd))
  choose p e hp hpe using hex
  have hiff := h (hnat p) (hnat_mem_hyperPrime_iff.2 (Eventually.of_forall hp)) (hnat e)
    (hnat_mem_hyperNat e)
  rw [hpow_hnat, hnat_hdvd_hnat_iff, hnat_hdvd_hnat_iff] at hiff
  have hne' : ∀ᶠ n in hyperfilter ℕ, ¬ (p n ^ e n ∣ α n ↔ p n ^ e n ∣ β n) :=
    hne.mono fun n hn => hpe n hn
  have hcase : ∀ᶠ n in hyperfilter ℕ,
      (p n ^ e n ∣ α n ∧ ¬ p n ^ e n ∣ β n) ∨ (¬ p n ^ e n ∣ α n ∧ p n ^ e n ∣ β n) :=
    hne'.mono fun n hn => by tauto
  rcases almostAll_or.1 hcase with hc | hc
  · obtain ⟨n, a1, a2⟩ := ((hiff.1 (hc.mono fun n hn => hn.1)).and hc).exists
    exact a2.2 a1
  · obtain ⟨n, a1, a2⟩ := ((hiff.2 (hc.mono fun n hn => hn.2)).and hc).exists
    exact a2.1 a1

/-- **Exercise 5.11(3)(d).** For $`N \in {}^*\mathbb N`: every positive $`n \in \mathbb N`
divides $`N` if and only if every standard prime power $`p^n` (with $`p` prime and
$`n \in \mathbb N`) divides $`N`. -/
theorem forall_nat_hdvd_iff_forall_prime_pow_hdvd (hN : N ∈ ℕ*) :
    (∀ n : ℕ, 0 < n → (n : ℝ*) ∣ₕ N) ↔
      ∀ p : ℕ, p.Prime → ∀ n : ℕ, ((p ^ n : ℕ) : ℝ*) ∣ₕ N := by
  constructor
  · intro h p hp n
    exact h (p ^ n) (pow_pos hp.pos n)
  · intro h d hd
    obtain ⟨ν, rfl⟩ := exists_hnat_eq hN
    rw [natCast_hdvd_hnat_iff]
    -- finitely many prime powers divide `d`; almost all terms are divisible by all of them
    have hfin : ∀ c ∈ d.divisors, ∀ᶠ n in hyperfilter ℕ,
        (∃ p k : ℕ, p.Prime ∧ c = p ^ k) → c ∣ ν n := by
      intro c _
      by_cases hc : ∃ p k : ℕ, p.Prime ∧ c = p ^ k
      · obtain ⟨p, k, hp, rfl⟩ := hc
        exact (natCast_hdvd_hnat_iff.1 (h p hp k)).mono fun n hn _ => hn
      · exact Eventually.of_forall fun n hc' => absurd hc' hc
    have hall := (eventually_all_finset d.divisors).2 hfin
    refine hall.mono fun n hn => ?_
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    exact hn (p ^ k) (Nat.mem_divisors.2 ⟨hpk, hd.ne'⟩) ⟨p, k, hp, rfl⟩

end HyperintegersAndPrimes

/-!
## 5.12 On the Existence of Infinitely Many Primes

Since the set of primes is infinite, its enlargement has nonstandard members by
Theorem 3.9.1. The book turns this around: a nonstandard version of Euclid's argument produces
a nonstandard hyperprime directly, and the existence of one shows that the set of primes is
infinite, because the enlargement of a finite set has no nonstandard members.

Take a positive hypernatural $`N` divisible by every standard positive integer and a
hyperprime $`q` dividing $`N + 1`. If $`q` were standard it would divide both $`N` and
$`N + 1`, hence $`1`.
-/

section InfinitelyManyPrimes

/-- **Section 5.12.** There is a nonstandard hyperprime. The proof is the nonstandard form of
Euclid's argument and does not use the infinitude of the primes. -/
theorem exists_nonstandard_hyperPrime :
    ∃ q ∈ hyperPrime, q ∉ range ((↑) : ℕ → ℝ*) := by
  obtain ⟨N, hN, hpos, hdiv⟩ := exists_hyperNat_forall_nat_hdvd
  have h1 : (1 : ℝ*) ∈ ℕ* := by simpa using natCast_mem_hyperNat 1
  obtain ⟨q, hq, hqN⟩ := exists_hyperPrime_hdvd (add_mem_hyperNat hN h1)
    (by linarith : (1 : ℝ*) < N + 1)
  refine ⟨q, hq, ?_⟩
  rintro ⟨p, rfl⟩
  have hp : p.Prime := natCast_mem_hyperPrime_iff.1 hq
  obtain ⟨ν, rfl⟩ := exists_hnat_eq hN
  -- `p` divides both `N` and `N + 1` at almost every index, hence divides `1`
  have e1 : ∀ᶠ n in hyperfilter ℕ, p ∣ ν n := natCast_hdvd_hnat_iff.1 (hdiv p hp.pos)
  have e2 : ∀ᶠ n in hyperfilter ℕ, p ∣ ν n + 1 := by
    have : hnat ν + 1 = hnat fun n => ν n + 1 := by
      rw [← hnat_const_one, hnat_add]
    rw [this] at hqN
    exact natCast_hdvd_hnat_iff.1 hqN
  obtain ⟨n, a1, a2⟩ := (e1.and e2).exists
  exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right a1).1 a2))

/-- **Section 5.12.** There are infinitely many prime numbers. This is deduced from the
existence of a nonstandard hyperprime: a finite set has no nonstandard members in its
enlargement (Exercise 3.10(1)). -/
theorem infinite_setOf_prime_of_nonstandard : {p : ℕ | p.Prime}.Infinite := by
  obtain ⟨q, hq, hns⟩ := exists_nonstandard_hyperPrime
  have hinf : ((fun p : ℕ => (p : ℝ)) '' {p : ℕ | p.Prime}).Infinite := by
    rw [infinite_iff_exists_nonstandard_mem (αS := ℝ*)]
    refine ⟨q, hq, ?_⟩
    rintro ⟨r, rfl⟩
    obtain ⟨n, rfl⟩ := coe_mem_hyperNat_iff.1 (hyperPrime_subset_hyperNat hq)
    exact hns ⟨n, rfl⟩
  exact Set.Infinite.of_image _ hinf

end InfinitelyManyPrimes

end Goldblatt
