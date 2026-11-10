import Goldblatt.Ch10_Topology.Reals

/-!
# 10 (part 2). Topologies on the Hyperreals: Section 10.5

This is the second of two parts of Chapter 10 (the overview is on the chapter page
{lit}`Goldblatt.Ch10_Topology`). It studies three notions of open set on the hyperreal line:
real-open sets, S-open sets and interval-open sets.
-/

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## 10.5 Topologies on the Hyperreals

On the hyperreal line the definition of an open set depends on which intervals are allowed as
neighbourhoods, and the section compares three choices.

* A _real-radius neighbourhood_ is an interval $`(r - e, r + e)` with hyperreal centre and
  positive real radius. Unions of these are the _real-open_ sets. They are closed under unions
  but not under finite intersections, because two real-radius neighbourhoods can overlap in an
  interval of infinitesimal length.
* An _S-neighbourhood_ $`((r - e, r + e))` keeps only the points whose whole halo lies in
  $`(r - e, r + e)`. Unions of these are the _S-open_ sets, and they do form a topology, the
  S-topology. Every S-open set is a union of halos, so the S-topology cannot separate
  infinitely close points.
* Allowing arbitrary hyperreal intervals as neighbourhoods gives the _interval-open_ sets, which
  form the order topology of the hyperreal line and contain every real-open set.

The definitions follow the book in describing each class as the unions of its basic
neighbourhoods; a pointwise criterion is proved for each and used throughout. Chapter 11
returns to these notions for internal sets.
-/

section HyperTopologies

variable {A B : Set ℝ*} {r s x y : ℝ*} {e d : ℝ}

/-- A set is a union of members of a family $`\mathcal B` exactly when each of its points lies
in a member of $`\mathcal B` included in the set. -/
private theorem exists_sUnion_iff_forall_exists {α : Type*} {ℬ : Set (Set α)} {A : Set α} :
    (∃ 𝒮 : Set (Set α), 𝒮 ⊆ ℬ ∧ A = ⋃₀ 𝒮) ↔ ∀ x ∈ A, ∃ S ∈ ℬ, x ∈ S ∧ S ⊆ A := by
  constructor
  · rintro ⟨𝒮, h𝒮, rfl⟩ x ⟨S, hS, hx⟩
    exact ⟨S, h𝒮 hS, hx, subset_sUnion_of_mem hS⟩
  · intro h
    refine ⟨{S | S ∈ ℬ ∧ S ⊆ A}, fun S hS => hS.1, Subset.antisymm ?_ ?_⟩
    · intro x hx
      obtain ⟨S, hS, hxS, hSA⟩ := h x hx
      exact ⟨S, ⟨hS, hSA⟩, hxS⟩
    · exact sUnion_subset fun S hS => hS.2

/-- A hyperreal within real distance of a limited one is limited. -/
private theorem limited_of_abs_sub_lt (hx : Limited x) (h : |y - x| < (e : ℝ*)) : Limited y := by
  have h1 : Limited (y - x) := limited_iff_abs_lt.2 ⟨e, h⟩
  simpa using hx.add h1

/-- The absolute value of a limited hyperreal is limited. -/
private theorem limited_abs (hx : Limited x) : Limited |x| := by
  obtain ⟨t, ht⟩ := limited_iff_abs_lt.1 hx
  exact limited_iff_abs_lt.2 ⟨t, by rwa [abs_abs]⟩

/-! ### Real-open sets -/

/-- **Section 10.5, definition.** The _real-radius neighbourhood_ of the hyperreal $`r` with
real radius $`e` is the hyperreal interval $`(r - e, r + e)`. -/
def realNhd (r : ℝ*) (e : ℝ) : Set ℝ* := Ioo (r - (e : ℝ*)) (r + e)

/-- A point lies in the real-radius neighbourhood $`(r - e, r + e)` exactly when its distance
from $`r` is less than $`e`. -/
theorem mem_realNhd_iff : x ∈ realNhd r e ↔ |x - r| < (e : ℝ*) := mem_Ioo_sub_add_iff_abs_sub_lt

/-- A real-radius neighbourhood of positive radius contains its centre. -/
theorem mem_realNhd_self (he : 0 < e) : r ∈ realNhd r e := by
  rw [mem_realNhd_iff, sub_self, abs_zero]
  exact Hyperreal.coe_pos.2 he

/-- The real-radius neighbourhood of radius $`1`, with the coercion of $`1` removed. -/
private theorem realNhd_one (r : ℝ*) : realNhd r 1 = Ioo (r - 1) (r + 1) := by
  unfold realNhd
  rw [Hyperreal.coe_one]

/-- **Section 10.5, definition.** A set of hyperreals is _real-open_ if it is a union of
real-radius neighbourhoods (of positive real radius). -/
def IsRealOpen (A : Set ℝ*) : Prop :=
  ∃ 𝒮 : Set (Set ℝ*), (∀ S ∈ 𝒮, ∃ (r : ℝ*) (e : ℝ), 0 < e ∧ S = realNhd r e) ∧ A = ⋃₀ 𝒮

/-- **Section 10.5.** Pointwise criterion: $`A` is real-open if and only if every point of
$`A` lies in a real-radius neighbourhood included in $`A`. The neighbourhood need not be
centred at the point. -/
theorem isRealOpen_iff :
    IsRealOpen A ↔
      ∀ x ∈ A, ∃ (r : ℝ*) (e : ℝ), 0 < e ∧ x ∈ realNhd r e ∧ realNhd r e ⊆ A := by
  have h := exists_sUnion_iff_forall_exists (A := A)
    (ℬ := {S | ∃ (r : ℝ*) (e : ℝ), 0 < e ∧ S = realNhd r e})
  refine Iff.trans h (forall₂_congr fun x _ => ⟨?_, ?_⟩)
  · rintro ⟨S, ⟨r, e, he, rfl⟩, hx, hS⟩
    exact ⟨r, e, he, hx, hS⟩
  · rintro ⟨r, e, he, hx, hS⟩
    exact ⟨_, ⟨r, e, he, rfl⟩, hx, hS⟩

/-- **Section 10.5.** Every real-radius neighbourhood is real-open. -/
theorem isRealOpen_realNhd (he : 0 < e) : IsRealOpen (realNhd r e) :=
  isRealOpen_iff.2 fun _ hx => ⟨r, e, he, hx, Subset.rfl⟩

/-- **Section 10.5.** The class of real-open sets is closed under arbitrary unions. -/
theorem IsRealOpen.iUnion {ι : Sort*} {A : ι → Set ℝ*} (h : ∀ i, IsRealOpen (A i)) :
    IsRealOpen (⋃ i, A i) := by
  rw [isRealOpen_iff]
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  obtain ⟨r, e, he, hxr, hsub⟩ := isRealOpen_iff.1 (h i) x hi
  exact ⟨r, e, he, hxr, hsub.trans (subset_iUnion A i)⟩

/-- **Section 10.5, remark on the definition.** The neighbourhood in the pointwise criterion
{name}`Goldblatt.isRealOpen_iff` cannot always be centred at the point: the real-open set
$`(-1, 1)` contains $`1 - \varepsilon`, but no interval of positive real radius $`e` centred
there lies inside it, since $`1 - \varepsilon + \frac e2 \ge 1`. So asking for centred
neighbourhoods is strictly stronger than being real-open. -/
theorem exists_isRealOpen_not_forall_centred :
    ∃ A : Set ℝ*, IsRealOpen A ∧ ¬ ∀ x ∈ A, ∃ e : ℝ, 0 < e ∧ realNhd x e ⊆ A := by
  refine ⟨realNhd 0 1, isRealOpen_realNhd one_pos, fun h => ?_⟩
  have hε := epsilon_pos_infinitesimal
  have hmem : (1 - ε : ℝ*) ∈ realNhd 0 1 := by
    rw [realNhd_one]
    constructor <;> linarith [hε.1, hε.2 1 one_pos, Hyperreal.coe_one]
  obtain ⟨e, he, hsub⟩ := h _ hmem
  have he2 := hε.2 (e / 2) (by positivity)
  have he' : (0 : ℝ*) < (e : ℝ*) := Hyperreal.coe_pos.2 he
  have hcast : ((e / 2 : ℝ) : ℝ*) = (e : ℝ*) / 2 := by push_cast; rfl
  rw [hcast] at he2
  have hy : (1 - ε + (e : ℝ*) / 2 : ℝ*) ∈ realNhd (1 - ε) e := by
    unfold realNhd
    constructor <;> linarith
  have := hsub hy
  rw [realNhd_one] at this
  linarith [this.2]

/-- A set that contains, with each of its points, all points within some positive real distance
of it, is real-open. The converse fails, see
{name}`Goldblatt.exists_isRealOpen_not_forall_centred`. -/
theorem isRealOpen_of_forall_exists_abs
    (h : ∀ x ∈ A, ∃ e : ℝ, 0 < e ∧ ∀ y : ℝ*, |y - x| < (e : ℝ*) → y ∈ A) : IsRealOpen A :=
  isRealOpen_iff.2 fun x hx =>
    let ⟨e, he, h'⟩ := h x hx
    ⟨x, e, he, mem_realNhd_self he, fun _ hy => h' _ (mem_realNhd_iff.1 hy)⟩

/-- The empty set is real-open. -/
theorem isRealOpen_empty : IsRealOpen (∅ : Set ℝ*) :=
  isRealOpen_iff.2 fun _ h => absurd h (notMem_empty _)

/-- **Section 10.5, example.** The enlargement of a real open interval $`(a, b)` is the
hyperreal interval with the same end points, which is the real-radius neighbourhood of the
midpoint with radius $`\frac{b - a}2`; so it is real-open. -/
theorem isRealOpen_starSet_Ioo (a b : ℝ) : IsRealOpen (⋆(Ioo a b) : Set ℝ*) := by
  rw [starSet_Ioo_real]
  rcases le_or_gt b a with hab | hab
  · rw [Ioo_eq_empty (not_lt.2 (Hyperreal.coe_le_coe.2 hab))]
    exact isRealOpen_empty
  · have h : Ioo (a : ℝ*) b = realNhd (((a + b) / 2 : ℝ) : ℝ*) ((b - a) / 2) := by
      have h1 : (a + b) / 2 - (b - a) / 2 = a := by ring
      have h2 : (a + b) / 2 + (b - a) / 2 = b := by ring
      unfold realNhd
      rw [← Hyperreal.coe_sub, ← Hyperreal.coe_add, h1, h2]
    rw [h]
    exact isRealOpen_realNhd (by linarith)

/-- **Section 10.5, example.** The enlargement of a union of open intervals of which only
finitely many are nonempty is real-open: enlargement commutes with finite unions, and each
piece is a real-radius neighbourhood. Compare Exercise 10.5.2(iii), where infinitely many
nonempty intervals give an enlargement that is not real-open. -/
theorem isRealOpen_starSet_iUnion_Ioo_of_finite {a b : ℕ → ℝ} (h : {n | a n < b n}.Finite) :
    IsRealOpen (⋆(⋃ n, Ioo (a n) (b n)) : Set ℝ*) := by
  have : Finite {n // a n < b n} := h.to_subtype
  have hU : (⋃ n, Ioo (a n) (b n)) = ⋃ n : {n // a n < b n}, Ioo (a n) (b n) := by
    ext x
    simp only [mem_iUnion, mem_Ioo]
    constructor
    · rintro ⟨n, h1, h2⟩
      exact ⟨⟨n, h1.trans h2⟩, h1, h2⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, hn⟩
  rw [hU, starSet_iUnion_of_finite]
  exact IsRealOpen.iUnion fun n => isRealOpen_starSet_Ioo _ _

/-- **Section 10.5, example.** The set $`\mathbb L` of limited hyperreals is real-open. -/
theorem isRealOpen_limitedSet : IsRealOpen 𝕃 :=
  isRealOpen_of_forall_exists_abs fun _ hx =>
    ⟨1, one_pos, fun _ hy => limited_of_abs_sub_lt hx hy⟩

/-- **Section 10.5, example.** The set of unlimited hyperreals is real-open. -/
theorem isRealOpen_setOf_unlimited : IsRealOpen {x : ℝ* | Unlimited x} :=
  isRealOpen_of_forall_exists_abs fun x hx =>
    ⟨1, one_pos, fun y hy => not_limited_iff_unlimited.1 fun hl =>
      Unlimited.not_limited hx (limited_of_abs_sub_lt hl (by rwa [abs_sub_comm]))⟩

/-- **Section 10.5, example.** The set of positive unlimited hyperreals is real-open. -/
theorem isRealOpen_setOf_posUnlimited : IsRealOpen {x : ℝ* | PosUnlimited x} :=
  isRealOpen_of_forall_exists_abs fun x hx =>
    ⟨1, one_pos, fun y hy t => by
      have h1 : ((t + 1 : ℝ) : ℝ*) < x := hx (t + 1)
      have h2 := (abs_lt.1 hy).1
      rw [Hyperreal.coe_add] at h1
      linarith⟩

/-- **Section 10.5, example.** The set of negative unlimited hyperreals is real-open. -/
theorem isRealOpen_setOf_negUnlimited : IsRealOpen {x : ℝ* | NegUnlimited x} :=
  isRealOpen_of_forall_exists_abs fun x hx =>
    ⟨1, one_pos, fun y hy t => by
      have h1 : x < ((t - 1 : ℝ) : ℝ*) := hx (t - 1)
      have h2 := (abs_lt.1 hy).2
      rw [Hyperreal.coe_sub] at h1
      linarith⟩

/-- If $`p < |x| < q` for reals $`0 < p < q`, every point within $`p/2` of $`x` is
appreciable. -/
private theorem appreciable_of_abs_sub_lt {p q : ℝ} (hp : 0 < p) (hpx : (p : ℝ*) < |x|)
    (hxq : |x| < q) (h : |y - x| < ((p / 2 : ℝ) : ℝ*)) : Appreciable y := by
  rw [appreciable_iff_abs]
  have h' : |x - y| < ((p / 2 : ℝ) : ℝ*) := by rwa [abs_sub_comm]
  have h1 := abs_sub_abs_le_abs_sub x y
  have h2 := abs_sub_abs_le_abs_sub y x
  refine ⟨p / 2, q + p / 2, by positivity, ?_, ?_⟩
  · push_cast at h h' ⊢
    linarith
  · push_cast at h h' ⊢
    linarith

/-- **Section 10.5, example.** The set of appreciable hyperreals is real-open. -/
theorem isRealOpen_setOf_appreciable : IsRealOpen {x : ℝ* | Appreciable x} :=
  isRealOpen_of_forall_exists_abs fun x hx =>
    let ⟨p, _, hp, hpx, hxq⟩ := appreciable_iff_abs.1 hx
    ⟨p / 2, by positivity, fun _ hy => appreciable_of_abs_sub_lt hp hpx hxq hy⟩

/-- **Section 10.5, example.** The set of positive appreciable hyperreals is real-open. -/
theorem isRealOpen_setOf_pos_appreciable : IsRealOpen {x : ℝ* | 0 < x ∧ Appreciable x} :=
  isRealOpen_of_forall_exists_abs fun x hx => by
    obtain ⟨p, q, hp, hpx, hxq⟩ := appreciable_iff_abs.1 hx.2
    refine ⟨p / 2, by positivity, fun y hy => ⟨?_, appreciable_of_abs_sub_lt hp hpx hxq hy⟩⟩
    have h1 := (abs_lt.1 hy).1
    have h2 : (0 : ℝ*) < p := Hyperreal.coe_pos.2 hp
    rw [abs_of_pos hx.1] at hpx
    push_cast at h1
    linarith

/-- **Section 10.5, example.** The set of negative appreciable hyperreals is real-open. -/
theorem isRealOpen_setOf_neg_appreciable : IsRealOpen {x : ℝ* | x < 0 ∧ Appreciable x} :=
  isRealOpen_of_forall_exists_abs fun x hx => by
    obtain ⟨p, q, hp, hpx, hxq⟩ := appreciable_iff_abs.1 hx.2
    refine ⟨p / 2, by positivity, fun y hy => ⟨?_, appreciable_of_abs_sub_lt hp hpx hxq hy⟩⟩
    have h1 := (abs_lt.1 hy).2
    have h2 : (0 : ℝ*) < p := Hyperreal.coe_pos.2 hp
    rw [abs_of_neg hx.1] at hpx
    push_cast at h1
    linarith

/-- **Section 10.5, example.** Every galaxy is real-open. -/
theorem isRealOpen_gal (b : ℝ*) : IsRealOpen (gal b) :=
  isRealOpen_of_forall_exists_abs fun x hx =>
    ⟨1, one_pos, fun y hy => by
      have h1 : Limited (y - x) := limited_iff_abs_lt.2 ⟨1, hy⟩
      have h2 : Limited (b - x) := hx
      have h3 := h2.sub h1
      have h4 : b - x - (y - x) = b - y := by ring
      rw [h4] at h3
      exact h3⟩

/-- A nonempty real-open set included in a hyperreal interval $`(a, b)` forces $`b - a` to
exceed a positive real number: the set contains a whole interval of real radius. -/
theorem IsRealOpen.exists_real_lt_sub {a b : ℝ*} (hA : IsRealOpen A) (hne : A.Nonempty)
    (hsub : A ⊆ Ioo a b) : ∃ e : ℝ, 0 < e ∧ (e : ℝ*) < b - a := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, e, he, -, hr⟩ := isRealOpen_iff.1 hA x hx
  have he' : (0 : ℝ*) < e := Hyperreal.coe_pos.2 he
  have h1 : r - (e : ℝ*) / 2 ∈ realNhd r e := by
    unfold realNhd
    constructor <;> linarith
  have h2 : r + (e : ℝ*) / 2 ∈ realNhd r e := by
    unfold realNhd
    constructor <;> linarith
  have h3 := (hsub (hr h1)).1
  have h4 := (hsub (hr h2)).2
  exact ⟨e, he, by linarith⟩

/-- **Section 10.5.** A nonempty hyperreal interval whose end points are infinitely close is
not real-open: it has infinitesimal width, so contains no real-radius neighbourhood. -/
theorem not_isRealOpen_Ioo_of_infClose {a b : ℝ*} (hab : a < b) (h : a ≊ b) :
    ¬ IsRealOpen (Ioo a b) := by
  intro hA
  obtain ⟨e, he, hlt⟩ := hA.exists_real_lt_sub ⟨(a + b) / 2, by constructor <;> linarith⟩
    Subset.rfl
  have := infClose_iff_abs_lt.1 h.symm e he
  rw [abs_of_pos (sub_pos.2 hab)] at this
  exact lt_asymm hlt this

/-- **Section 10.5.** Two real-radius neighbourhoods $`(r - e, r + e)` and $`(s - d, s + d)`
that overlap, with the left end point $`s - d` of the second infinitely close to the right end
point $`r + e` of the first, have an intersection that is not real-open: the intersection is
the nonempty interval $`(s - d, r + e)`, which has infinitesimal width. -/
theorem not_isRealOpen_realNhd_inter_of_infClose (he : 0 < e) (hd : 0 < d)
    (hlt : s - (d : ℝ*) < r + e) (h : s - (d : ℝ*) ≊ r + e) :
    ¬ IsRealOpen (realNhd r e ∩ realNhd s d) := by
  intro hA
  have he' : (0 : ℝ*) < e := Hyperreal.coe_pos.2 he
  have hd' : (0 : ℝ*) < d := Hyperreal.coe_pos.2 hd
  have h1 := abs_lt.1 (infClose_iff_abs_lt.1 h e he)
  have h2 := abs_lt.1 (infClose_iff_abs_lt.1 h d hd)
  have hsub : realNhd r e ∩ realNhd s d ⊆ Ioo (s - (d : ℝ*)) (r + e) :=
    fun x hx => ⟨hx.2.1, hx.1.2⟩
  have hne : (realNhd r e ∩ realNhd s d).Nonempty := by
    refine ⟨(s - (d : ℝ*) + (r + e)) / 2, ?_, ?_⟩
    · unfold realNhd
      constructor <;> linarith [h1.1]
    · unfold realNhd
      constructor <;> linarith [h2.1]
  obtain ⟨c, hc, hclt⟩ := hA.exists_real_lt_sub hne hsub
  have h3 := abs_lt.1 (infClose_iff_abs_lt.1 h c hc)
  linarith [h3.1]

/-- **Section 10.5.** The real-open sets do not form a topology: there are two real-radius
neighbourhoods whose intersection is not real-open. This is the instance
$`r = 0`, $`s = 2 - \varepsilon`, $`e = d = 1` of
{name}`Goldblatt.not_isRealOpen_realNhd_inter_of_infClose`: the neighbourhoods $`(-1, 1)` and
$`(1 - \varepsilon, 3 - \varepsilon)` overlap in $`(1 - \varepsilon, 1)`. -/
theorem exists_realNhd_inter_not_isRealOpen :
    ∃ (r s : ℝ*) (e d : ℝ), 0 < e ∧ 0 < d ∧ ¬ IsRealOpen (realNhd r e ∩ realNhd s d) := by
  have hε := epsilon_pos_infinitesimal
  refine ⟨0, 2 - ε, 1, 1, one_pos, one_pos,
    not_isRealOpen_realNhd_inter_of_infClose one_pos one_pos ?_ ?_⟩
  · simp only [Hyperreal.coe_one]
    linarith [hε.1]
  · rw [infClose_iff_abs_lt]
    intro c hc
    have := hε.2 c hc
    simp only [Hyperreal.coe_one]
    rw [abs_lt]
    constructor <;> linarith [hε.1]

/-! ### The S-topology -/

/-- **Section 10.5, definition.** The _S-neighbourhood_ $`((r - e, r + e))` consists of the
hyperreals that are well inside the interval $`(r - e, r + e)`: those whose whole halo is
included in it. -/
def sNeighbourhood (r : ℝ*) (e : ℝ) : Set ℝ* := {x | hal x ⊆ realNhd r e}

/-- **Section 10.5, definition unfolded.** A point belongs to the S-neighbourhood
$`((r - e, r + e))` exactly when its halo lies inside the hyperreal interval
$`(r - e, r + e)`. This holds by definition. The right-hand side is the halo form of the
relation "well inside" of Section 8.11 (in the Chapter 8 module,
{lit}`Goldblatt.wellInside_iff_hal_subset`), which this chapter does not import. -/
theorem mem_sNeighbourhood_iff_hal_subset_Ioo :
    x ∈ sNeighbourhood r e ↔ hal x ⊆ Ioo (r - (e : ℝ*)) (r + e) := Iff.rfl

/-- **Section 10.5.** A point $`x` belongs to $`((r - e, r + e))` if and only if its distance
from $`r` is appreciably less than $`e`, in the sense that $`r - x` is limited and
$`\operatorname{sh}|r - x| < e`. -/
theorem mem_sNeighbourhood_iff :
    x ∈ sNeighbourhood r e ↔ Limited (r - x) ∧ sh |r - x| < e := by
  constructor
  · intro h
    have hx : |x - r| < (e : ℝ*) := mem_realNhd_iff.1 (h (InfClose.refl x))
    rw [abs_sub_comm] at hx
    have hl : Limited (r - x) := limited_iff_abs_lt.2 ⟨e, hx⟩
    have hla := limited_abs hl
    refine ⟨hl, lt_of_le_of_ne (hla.sh_le hx.le) fun heq => ?_⟩
    have hc : |r - x| ≊ (e : ℝ*) := by
      rw [← heq]
      exact hla.infClose_sh
    rcases le_or_gt 0 (r - x) with h0 | h0
    · rw [abs_of_nonneg h0] at hc
      have hy : x ≊ r - e := by
        rw [infClose_iff] at hc ⊢
        have : x - (r - e) = -(r - x - e) := by ring
        rw [this]
        exact hc.neg
      exact lt_irrefl _ (show r - (e : ℝ*) ∈ Ioo (r - (e : ℝ*)) (r + e) from h hy).1
    · rw [abs_of_neg h0] at hc
      have hy : x ≊ r + e := by
        rw [infClose_iff] at hc ⊢
        have : x - (r + e) = -(r - x) - e := by ring
        rw [this]
        exact hc
      exact lt_irrefl _ (show r + (e : ℝ*) ∈ Ioo (r - (e : ℝ*)) (r + e) from h hy).2
  · rintro ⟨hl, hs⟩ y hy
    rw [mem_realNhd_iff, abs_sub_comm]
    have hry : r - y ≊ r - x := (InfClose.refl r).sub (InfClose.symm hy)
    have hl' : Limited (r - y) := hl.of_infClose hry.symm
    have hsh : sh |r - y| = sh |r - x| := by
      rw [sh_abs hl', sh_abs hl, (infClose_iff_sh_eq hl' hl).1 hry]
    exact (limited_abs hl').lt_of_sh_lt (hsh ▸ hs)

/-- An S-neighbourhood of positive radius contains its centre. -/
theorem mem_sNeighbourhood_self (he : 0 < e) : r ∈ sNeighbourhood r e := by
  rw [mem_sNeighbourhood_iff, sub_self, abs_zero, sh_zero]
  exact ⟨limited_zero, he⟩

/-- **Section 10.5.** The S-neighbourhood $`((r - e, r + e))` is included in the real-radius
neighbourhood $`(r - e, r + e)`. -/
theorem sNeighbourhood_subset_realNhd : sNeighbourhood r e ⊆ realNhd r e :=
  fun x hx => hx (InfClose.refl x)

/-- An S-neighbourhood contains the halo of each of its points. -/
theorem hal_subset_sNeighbourhood (hx : x ∈ sNeighbourhood r e) : hal x ⊆ sNeighbourhood r e :=
  fun _ hy _ hz => hx (InfClose.trans hy hz)

/-- S-neighbourhoods with the same centre grow with the radius. -/
theorem sNeighbourhood_mono (h : e ≤ d) : sNeighbourhood r e ⊆ sNeighbourhood r d := by
  intro x hx
  rw [mem_sNeighbourhood_iff] at hx ⊢
  exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩

/-- **Section 10.5.** The second description of the S-neighbourhood: $`x` belongs to
$`((r - e, r + e))` if and only if $`e - |r - x|` is positive and appreciable. The book says
only that $`e - |r - x|` is appreciable; positivity is implicit there and has to be stated,
because for a point far outside the interval the difference is appreciable and negative. -/
theorem mem_sNeighbourhood_iff_appreciable :
    x ∈ sNeighbourhood r e ↔ 0 < (e : ℝ*) - |r - x| ∧ Appreciable ((e : ℝ*) - |r - x|) := by
  rw [mem_sNeighbourhood_iff]
  constructor
  · rintro ⟨hl, hs⟩
    obtain ⟨m, hm1, hm2⟩ := exists_between hs
    have hlt : |r - x| < (m : ℝ*) := (limited_abs hl).lt_of_sh_lt hm1
    have hme : (m : ℝ*) < e := Hyperreal.coe_lt_coe.2 hm2
    have hpos : (0 : ℝ*) < (e : ℝ*) - |r - x| := by linarith
    refine ⟨hpos, appreciable_iff_abs.2 ⟨e - m, e + 1, by linarith, ?_, ?_⟩⟩
    · rw [abs_of_pos hpos]
      push_cast
      linarith
    · rw [abs_of_pos hpos]
      push_cast
      linarith [abs_nonneg (r - x)]
  · rintro ⟨hpos, happ⟩
    obtain ⟨p, -, hp, hlt, -⟩ := appreciable_iff_abs.1 happ
    rw [abs_of_pos hpos] at hlt
    have hlt' : |r - x| < ((e - p : ℝ) : ℝ*) := by
      push_cast
      linarith
    have hl : Limited (r - x) := limited_iff_abs_lt.2 ⟨e - p, hlt'⟩
    exact ⟨hl, lt_of_le_of_lt ((limited_abs hl).sh_le hlt'.le) (by linarith)⟩

/-- **Section 10.5.** Each point of the S-neighbourhood $`((r - e, r + e))` is at appreciable
distance from both end points $`r - e` and $`r + e`. -/
theorem appreciable_sub_of_mem_sNeighbourhood (hx : x ∈ sNeighbourhood r e) :
    Appreciable (x - (r - e)) ∧ Appreciable (r + e - x) := by
  obtain ⟨hl, hs⟩ := mem_sNeighbourhood_iff.1 hx
  obtain ⟨m, hm1, hm2⟩ := exists_between hs
  have hlt : |r - x| < (m : ℝ*) := (limited_abs hl).lt_of_sh_lt hm1
  have hme : (m : ℝ*) < e := Hyperreal.coe_lt_coe.2 hm2
  obtain ⟨h1, h2⟩ := abs_lt.1 hlt
  have hpos : (0 : ℝ) < e - m := by linarith
  constructor
  · rw [appreciable_iff_abs]
    refine ⟨e - m, e + m, hpos, ?_, ?_⟩
    · rw [abs_of_pos (by linarith)]
      push_cast
      linarith
    · rw [abs_of_pos (by linarith)]
      push_cast
      linarith
  · rw [appreciable_iff_abs]
    refine ⟨e - m, e + m, hpos, ?_, ?_⟩
    · rw [abs_of_pos (by linarith)]
      push_cast
      linarith
    · rw [abs_of_pos (by linarith)]
      push_cast
      linarith

/-- **Section 10.5.** If $`t` belongs to $`((r - e, r + e))` and the real number $`g` is at
most $`e - \operatorname{sh}|r - t|`, then $`((t - g, t + g)) \subseteq ((r - e, r + e))`. -/
theorem sNeighbourhood_subset_of_mem {t : ℝ*} {g : ℝ} (ht : t ∈ sNeighbourhood r e)
    (hg : g ≤ e - sh |r - t|) : sNeighbourhood t g ⊆ sNeighbourhood r e := by
  intro x hx
  obtain ⟨hl1, hs1⟩ := mem_sNeighbourhood_iff.1 ht
  obtain ⟨hl2, hs2⟩ := mem_sNeighbourhood_iff.1 hx
  have hl : Limited (r - x) := by
    have := hl1.add hl2
    rwa [sub_add_sub_cancel] at this
  refine mem_sNeighbourhood_iff.2 ⟨hl, ?_⟩
  have hle : |r - x| ≤ |r - t| + |t - x| := abs_sub_le r t x
  have := sh_le_sh (limited_abs hl) ((limited_abs hl1).add (limited_abs hl2)) hle
  rw [sh_add (limited_abs hl1) (limited_abs hl2)] at this
  linarith

/-- **Section 10.5.** If $`t` lies in two S-neighbourhoods $`((r - e, r + e))` and
$`((s - d, s + d))`, then $`((t - g, t + g))` is included in their intersection for every
real $`g \le \min\{e - \operatorname{sh}|r - t|,\ d - \operatorname{sh}|s - t|\}`. -/
theorem sNeighbourhood_subset_inter {t : ℝ*} {g : ℝ} (h1 : t ∈ sNeighbourhood r e)
    (h2 : t ∈ sNeighbourhood s d) (hg : g ≤ min (e - sh |r - t|) (d - sh |s - t|)) :
    sNeighbourhood t g ⊆ sNeighbourhood r e ∩ sNeighbourhood s d :=
  subset_inter (sNeighbourhood_subset_of_mem h1 (hg.trans (min_le_left _ _)))
    (sNeighbourhood_subset_of_mem h2 (hg.trans (min_le_right _ _)))

/-- **Section 10.5, definition.** A set of hyperreals is _S-open_ if it is a union of
S-neighbourhoods. -/
def IsSOpen (A : Set ℝ*) : Prop :=
  ∃ 𝒮 : Set (Set ℝ*), (∀ S ∈ 𝒮, ∃ (r : ℝ*) (e : ℝ), 0 < e ∧ S = sNeighbourhood r e) ∧
    A = ⋃₀ 𝒮

/-- **Section 10.5.** Pointwise criterion: $`A` is S-open if and only if every point of $`A`
lies in an S-neighbourhood included in $`A`. -/
theorem isSOpen_iff :
    IsSOpen A ↔
      ∀ x ∈ A, ∃ (r : ℝ*) (e : ℝ), 0 < e ∧ x ∈ sNeighbourhood r e ∧ sNeighbourhood r e ⊆ A := by
  have h := exists_sUnion_iff_forall_exists (A := A)
    (ℬ := {S | ∃ (r : ℝ*) (e : ℝ), 0 < e ∧ S = sNeighbourhood r e})
  refine Iff.trans h (forall₂_congr fun x _ => ⟨?_, ?_⟩)
  · rintro ⟨S, ⟨r, e, he, rfl⟩, hx, hS⟩
    exact ⟨r, e, he, hx, hS⟩
  · rintro ⟨r, e, he, hx, hS⟩
    exact ⟨_, ⟨r, e, he, rfl⟩, hx, hS⟩

/-- **Section 10.5.** Centred criterion: $`A` is S-open if and only if every point $`x` of
$`A` has an S-neighbourhood $`((x - e, x + e))` centred at $`x` and included in $`A`. This is
where S-neighbourhoods behave better than real-radius neighbourhoods. -/
theorem isSOpen_iff_forall_exists_centred :
    IsSOpen A ↔ ∀ x ∈ A, ∃ e : ℝ, 0 < e ∧ sNeighbourhood x e ⊆ A := by
  rw [isSOpen_iff]
  refine forall₂_congr fun x _ => ⟨?_, ?_⟩
  · rintro ⟨r, e, -, hx, hsub⟩
    have hs := (mem_sNeighbourhood_iff.1 hx).2
    exact ⟨e - sh |r - x|, by linarith, (sNeighbourhood_subset_of_mem hx le_rfl).trans hsub⟩
  · rintro ⟨e, he, hsub⟩
    exact ⟨x, e, he, mem_sNeighbourhood_self he, hsub⟩

/-- **Section 10.5.** Every S-neighbourhood is S-open. -/
theorem isSOpen_sNeighbourhood : IsSOpen (sNeighbourhood r e) :=
  isSOpen_iff_forall_exists_centred.2 fun x hx =>
    ⟨e - sh |r - x|, by linarith [(mem_sNeighbourhood_iff.1 hx).2],
      sNeighbourhood_subset_of_mem hx le_rfl⟩

/-- **Section 10.5.** The S-open sets are closed under arbitrary unions. -/
theorem IsSOpen.iUnion {ι : Sort*} {A : ι → Set ℝ*} (h : ∀ i, IsSOpen (A i)) :
    IsSOpen (⋃ i, A i) := by
  rw [isSOpen_iff_forall_exists_centred]
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  obtain ⟨e, he, hsub⟩ := isSOpen_iff_forall_exists_centred.1 (h i) x hi
  exact ⟨e, he, hsub.trans (subset_iUnion A i)⟩

/-- **Section 10.5.** The intersection of two S-open sets is S-open. -/
theorem IsSOpen.inter (hA : IsSOpen A) (hB : IsSOpen B) : IsSOpen (A ∩ B) := by
  rw [isSOpen_iff_forall_exists_centred] at *
  rintro x ⟨hxA, hxB⟩
  obtain ⟨e, he, h1⟩ := hA x hxA
  obtain ⟨d, hd, h2⟩ := hB x hxB
  exact ⟨min e d, lt_min he hd, fun y hy =>
    ⟨h1 (sNeighbourhood_mono (min_le_left _ _) hy), h2 (sNeighbourhood_mono (min_le_right _ _) hy)⟩⟩

/-- **Section 10.5.** The intersection of two S-neighbourhoods is S-open. -/
theorem isSOpen_sNeighbourhood_inter :
    IsSOpen (sNeighbourhood r e ∩ sNeighbourhood s d) :=
  isSOpen_sNeighbourhood.inter isSOpen_sNeighbourhood

/-- The whole hyperreal line is S-open. -/
theorem isSOpen_univ : IsSOpen (univ : Set ℝ*) :=
  isSOpen_iff_forall_exists_centred.2 fun _ _ => ⟨1, one_pos, subset_univ _⟩

/-- The empty set is S-open. -/
theorem isSOpen_empty : IsSOpen (∅ : Set ℝ*) :=
  isSOpen_iff_forall_exists_centred.2 fun _ hx => absurd hx (notMem_empty _)

/-- **Section 10.5, definition.** The _S-topology_ on the hyperreal line, whose open sets are
the S-open sets. -/
@[instance_reducible]
def sTopology : TopologicalSpace ℝ* where
  IsOpen := IsSOpen
  isOpen_univ := isSOpen_univ
  isOpen_inter := fun _ _ => IsSOpen.inter
  isOpen_sUnion := fun 𝒮 h => by
    rw [sUnion_eq_iUnion]
    exact IsSOpen.iUnion fun S => h S S.2

/-- The open sets of the S-topology are the S-open sets. -/
theorem isOpen_sTopology_iff : IsOpen[sTopology] A ↔ IsSOpen A := Iff.rfl

/-- A real-radius neighbourhood centred at $`x` is included in every S-neighbourhood centred
at $`x` of larger radius. -/
theorem realNhd_subset_sNeighbourhood (h : e < d) : realNhd x e ⊆ sNeighbourhood x d := by
  intro y hy
  rw [mem_realNhd_iff, abs_sub_comm] at hy
  have hl : Limited (x - y) := limited_iff_abs_lt.2 ⟨e, hy⟩
  exact mem_sNeighbourhood_iff.2 ⟨hl, lt_of_le_of_lt ((limited_abs hl).sh_le hy.le) h⟩

/-- **Exercise 10.5.1(i).** Every S-open set is real-open. -/
theorem IsSOpen.isRealOpen (hA : IsSOpen A) : IsRealOpen A := by
  apply isRealOpen_of_forall_exists_abs
  intro x hx
  obtain ⟨e, he, hsub⟩ := isSOpen_iff_forall_exists_centred.1 hA x hx
  exact ⟨e / 2, by positivity, fun y hy =>
    hsub (realNhd_subset_sNeighbourhood (by linarith) (mem_realNhd_iff.2 hy))⟩

/-- **Exercise 10.5.1(ii), first half.** An S-open set contains the halo of each of its
points. -/
theorem IsSOpen.hal_subset (hA : IsSOpen A) (hx : x ∈ A) : hal x ⊆ A := by
  obtain ⟨r, e, -, hxr, hsub⟩ := isSOpen_iff.1 hA x hx
  exact (hal_subset_sNeighbourhood hxr).trans hsub

/-- **Exercise 10.5.1(ii), first half.** Each S-open set is a union of halos: it is the union
of the halos of its points. -/
theorem IsSOpen.eq_biUnion_hal (hA : IsSOpen A) : A = ⋃ x ∈ A, hal x := by
  apply Subset.antisymm
  · exact fun x hx => mem_iUnion₂.2 ⟨x, hx, InfClose.refl x⟩
  · exact iUnion₂_subset fun x hx => hA.hal_subset hx

/-- No real-radius neighbourhood of positive radius fits inside a halo. -/
theorem not_realNhd_subset_hal (he : 0 < e) : ¬ realNhd r e ⊆ hal x := by
  intro h
  have he' : (0 : ℝ*) < e := Hyperreal.coe_pos.2 he
  have h1 : x ≊ r := h (mem_realNhd_self he)
  have h2 : x ≊ r + (e : ℝ*) / 2 := h (by
    unfold realNhd
    constructor <;> linarith)
  have h3 : r ≊ r + (e : ℝ*) / 2 := h1.symm.trans h2
  rw [infClose_iff] at h3
  have h4 : r - (r + (e : ℝ*) / 2) = ((-(e / 2) : ℝ) : ℝ*) := by
    push_cast
    ring
  rw [h4, infinitesimal_coe_iff] at h3
  linarith

/-- **Section 10.5.** No halo is real-open. -/
theorem not_isRealOpen_hal (x : ℝ*) : ¬ IsRealOpen (hal x) := by
  intro h
  obtain ⟨r, e, he, -, hsub⟩ := isRealOpen_iff.1 h x (InfClose.refl x)
  exact not_realNhd_subset_hal he hsub

/-- **Exercise 10.5.1(ii), second half.** No halo is S-open. -/
theorem not_isSOpen_hal (x : ℝ*) : ¬ IsSOpen (hal x) :=
  fun h => not_isRealOpen_hal x h.isRealOpen

/-- **Exercise 10.5.1(ii), second half.** A union of halos need not be S-open: the single halo
of $`0` is a counterexample. -/
theorem exists_biUnion_hal_not_isSOpen : ∃ X : Set ℝ*, ¬ IsSOpen (⋃ x ∈ X, hal x) :=
  ⟨{0}, by
    rw [biUnion_singleton]
    exact not_isSOpen_hal 0⟩

/-- **Exercise 10.5.1(iii).** No real-radius neighbourhood (of positive radius) is S-open: the
point $`r + e - \varepsilon` belongs to $`(r - e, r + e)`, but the end point $`r + e` is in
its halo. -/
theorem not_isSOpen_realNhd (he : 0 < e) : ¬ IsSOpen (realNhd r e) := by
  intro h
  have hε := epsilon_pos_infinitesimal
  have he' := hε.2 (2 * e) (by positivity)
  push_cast at he'
  have hx : r + e - ε ∈ realNhd r e := by
    unfold realNhd
    constructor <;> linarith [hε.1]
  have hy : r + e - ε ≊ r + e := by
    rw [infClose_iff]
    have : r + e - ε - (r + e) = -ε := by ring
    rw [this]
    exact infinitesimal_epsilon.neg
  exact lt_irrefl _ (show r + (e : ℝ*) ∈ Ioo (r - (e : ℝ*)) (r + e) from h.hal_subset hx hy).2

/-- **Section 10.5, supplementary remark.** The S-topology is not Hausdorff: an S-open set
containing $`0` contains the halo of $`0`, so $`0` and $`\varepsilon` cannot be separated.
The book does not state this, but it is the reason the S-topology only sees the real line
behind the limited hyperreals. -/
theorem not_t2Space_sTopology : ¬ @T2Space ℝ* sTopology := by
  let _ := sTopology
  intro h
  obtain ⟨u, v, hu, -, h0, hε, hd⟩ :=
    t2_separation (x := (0 : ℝ*)) (y := ε) epsilon_pos_infinitesimal.1.ne
  have hmem : (ε : ℝ*) ∈ u :=
    IsSOpen.hal_subset hu h0 (infinitesimal_iff_infClose_zero.1 infinitesimal_epsilon).symm
  exact Set.disjoint_left.1 hd hmem hε

/-! ### The interval topology -/

/-- **Section 10.5, definition.** A set of hyperreals is _interval-open_ if it is a union of
hyperreal open intervals $`(a, b)`. -/
def IsIntervalOpen (A : Set ℝ*) : Prop :=
  ∃ 𝒮 : Set (Set ℝ*), (∀ S ∈ 𝒮, ∃ a b : ℝ*, S = Ioo a b) ∧ A = ⋃₀ 𝒮

/-- **Section 10.5.** Pointwise criterion: $`A` is interval-open if and only if every point of
$`A` lies in a hyperreal open interval included in $`A`. -/
theorem isIntervalOpen_iff :
    IsIntervalOpen A ↔ ∀ x ∈ A, ∃ a b : ℝ*, x ∈ Ioo a b ∧ Ioo a b ⊆ A := by
  have h := exists_sUnion_iff_forall_exists (A := A) (ℬ := {S | ∃ a b : ℝ*, S = Ioo a b})
  refine Iff.trans h (forall₂_congr fun x _ => ⟨?_, ?_⟩)
  · rintro ⟨S, ⟨a, b, rfl⟩, hx, hS⟩
    exact ⟨a, b, hx, hS⟩
  · rintro ⟨a, b, hx, hS⟩
    exact ⟨_, ⟨a, b, rfl⟩, hx, hS⟩

/-- **Section 10.5.** Every hyperreal open interval is interval-open. -/
theorem isIntervalOpen_Ioo (a b : ℝ*) : IsIntervalOpen (Ioo a b) :=
  isIntervalOpen_iff.2 fun _ hx => ⟨a, b, hx, Subset.rfl⟩

/-- The interval-open sets are closed under arbitrary unions. -/
theorem IsIntervalOpen.iUnion {ι : Sort*} {A : ι → Set ℝ*} (h : ∀ i, IsIntervalOpen (A i)) :
    IsIntervalOpen (⋃ i, A i) := by
  rw [isIntervalOpen_iff]
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  obtain ⟨a, b, hxab, hsub⟩ := isIntervalOpen_iff.1 (h i) x hi
  exact ⟨a, b, hxab, hsub.trans (subset_iUnion A i)⟩

/-- The intersection of two interval-open sets is interval-open. -/
theorem IsIntervalOpen.inter (hA : IsIntervalOpen A) (hB : IsIntervalOpen B) :
    IsIntervalOpen (A ∩ B) := by
  rw [isIntervalOpen_iff] at *
  rintro x ⟨hxA, hxB⟩
  obtain ⟨a, b, h1, h1'⟩ := hA x hxA
  obtain ⟨c, d, h2, h2'⟩ := hB x hxB
  refine ⟨max a c, min b d, ⟨max_lt h1.1 h2.1, lt_min h1.2 h2.2⟩, fun z hz => ⟨?_, ?_⟩⟩
  · exact h1' ⟨lt_of_le_of_lt (le_max_left _ _) hz.1, lt_of_lt_of_le hz.2 (min_le_left _ _)⟩
  · exact h2' ⟨lt_of_le_of_lt (le_max_right _ _) hz.1, lt_of_lt_of_le hz.2 (min_le_right _ _)⟩

/-- The whole hyperreal line is interval-open. -/
theorem isIntervalOpen_univ : IsIntervalOpen (univ : Set ℝ*) :=
  isIntervalOpen_iff.2 fun x _ => ⟨x - 1, x + 1, ⟨by linarith, by linarith⟩, subset_univ _⟩

/-- **Section 10.5, definition.** The _interval topology_ on the hyperreal line, whose open
sets are the interval-open sets. -/
@[instance_reducible]
def intervalTopology : TopologicalSpace ℝ* where
  IsOpen := IsIntervalOpen
  isOpen_univ := isIntervalOpen_univ
  isOpen_inter := fun _ _ => IsIntervalOpen.inter
  isOpen_sUnion := fun 𝒮 h => by
    rw [sUnion_eq_iUnion]
    exact IsIntervalOpen.iUnion fun S => h S S.2

/-- The open sets of the interval topology are the interval-open sets. -/
theorem isOpen_intervalTopology_iff : IsOpen[intervalTopology] A ↔ IsIntervalOpen A := Iff.rfl

/-- **Section 10.5, supplementary remark.** A set is interval-open if and only if it is open
in the order topology of the hyperreal line, the topology generated by the open rays. The book
does not state this. -/
theorem isIntervalOpen_iff_isOpen_orderTopology :
    IsIntervalOpen A ↔ IsOpen[Preorder.topology ℝ*] A := by
  let _ : TopologicalSpace ℝ* := Preorder.topology ℝ*
  have : OrderTopology ℝ* := ⟨rfl⟩
  rw [isIntervalOpen_iff, isOpen_iff_mem_nhds]
  exact forall₂_congr fun x _ => mem_nhds_iff_exists_Ioo_subset.symm

/-- **Section 10.5, supplementary remark.** The interval topology is the order topology of the
hyperreal line. The book does not state this. -/
theorem intervalTopology_eq_orderTopology : intervalTopology = Preorder.topology ℝ* :=
  TopologicalSpace.ext_iff.2 fun _ => isIntervalOpen_iff_isOpen_orderTopology

/-- **Section 10.5.** Every real-open set is interval-open. -/
theorem IsRealOpen.isIntervalOpen (hA : IsRealOpen A) : IsIntervalOpen A :=
  isIntervalOpen_iff.2 fun x hx =>
    let ⟨r, e, _, hxr, hsub⟩ := isRealOpen_iff.1 hA x hx
    ⟨r - e, r + e, hxr, hsub⟩

/-- **Section 10.5.** Every halo is interval-open (though not real-open): a point $`y` of the
halo of $`x` lies in $`(y - \varepsilon, y + \varepsilon)`, which is included in the halo. -/
theorem isIntervalOpen_hal (x : ℝ*) : IsIntervalOpen (hal x) := by
  rw [isIntervalOpen_iff]
  intro y hy
  have hε := epsilon_pos_infinitesimal.1
  refine ⟨y - ε, y + ε, ⟨by linarith, by linarith⟩, fun z hz => ?_⟩
  have hz' : |z - y| < ε := mem_Ioo_sub_add_iff_abs_sub_lt.1 hz
  have hyz : y ≊ z := by
    rw [infClose_iff]
    refine Infinitesimal.of_abs_le infinitesimal_epsilon ?_
    rw [abs_sub_comm, abs_of_pos hε]
    exact hz'.le
  exact InfClose.trans hy hyz

/-- **Section 10.5.** The converse inclusion fails: there are interval-open sets that are not
real-open, for instance the interval $`(0, \varepsilon)`, or any halo. -/
theorem exists_isIntervalOpen_not_isRealOpen : ∃ A : Set ℝ*, IsIntervalOpen A ∧ ¬ IsRealOpen A :=
  ⟨Ioo 0 ε, isIntervalOpen_Ioo _ _, not_isRealOpen_Ioo_of_infClose epsilon_pos_infinitesimal.1
    (infinitesimal_iff_infClose_zero.1 infinitesimal_epsilon).symm⟩

/-- **Section 10.5.** The intersection of the real-radius neighbourhoods centred at a
hyperreal $`r` is the halo of $`r`. -/
theorem iInter_realNhd_eq_hal (r : ℝ*) : ⋂ (e : ℝ) (_ : 0 < e), realNhd r e = hal r := by
  ext x
  simp only [mem_iInter, mem_realNhd_iff, mem_hal]
  rw [infClose_iff_abs_lt]
  constructor
  · intro h e he
    rw [abs_sub_comm]
    exact h e he
  · intro h e he
    rw [abs_sub_comm]
    exact h e he

/-- **Section 10.5.** For the S-topology, the intersection of the open sets containing a
hyperreal $`r` is the halo of $`r`:
$$`\bigcap \{A : r \in A \text{ and } A \text{ is S-open}\} = \operatorname{hal}(r).` -/
theorem iInter_isSOpen_eq_hal (r : ℝ*) :
    ⋂ (A : Set ℝ*) (_ : IsSOpen A) (_ : r ∈ A), A = hal r := by
  apply Subset.antisymm
  · intro x hx
    simp only [mem_iInter] at hx
    rw [← iInter_realNhd_eq_hal]
    simp only [mem_iInter]
    intro e he
    exact sNeighbourhood_subset_realNhd
      (hx _ isSOpen_sNeighbourhood (mem_sNeighbourhood_self he))
  · intro x hx
    simp only [mem_iInter]
    exact fun A hA hr => hA.hal_subset hr hx

/-- **Section 10.5, corrected.** The intersection of the real-open sets containing a hyperreal
$`r` is $`\{r\}`. The book asserts that this intersection is the halo of $`r`, which is true
for S-open sets ({name}`iInter_isSOpen_eq_hal`) and for the real-radius neighbourhoods centred
at $`r` ({name}`iInter_realNhd_eq_hal`), but not for all real-open sets: the centre of a
real-radius neighbourhood may be any hyperreal, so for $`x > r` the neighbourhood of radius
$`1` with right end point $`\min(x, r + 1)` contains $`r` and omits $`x`. -/
theorem iInter_isRealOpen_eq_singleton (r : ℝ*) :
    ⋂ (A : Set ℝ*) (_ : IsRealOpen A) (_ : r ∈ A), A = {r} := by
  apply Subset.antisymm
  · intro x hx
    simp only [mem_iInter] at hx
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hr : r ∈ realNhd (max x (r - 1) + 1) 1 := by
        rw [realNhd_one]
        exact ⟨by linarith [max_lt hlt (show r - 1 < r by linarith)],
          by linarith [le_max_right x (r - 1)]⟩
      have := hx _ (isRealOpen_realNhd one_pos) hr
      rw [realNhd_one] at this
      linarith [this.1, le_max_left x (r - 1)]
    · have hr : r ∈ realNhd (min x (r + 1) - 1) 1 := by
        rw [realNhd_one]
        exact ⟨by linarith [min_le_right x (r + 1)],
          by linarith [lt_min hgt (show r < r + 1 by linarith)]⟩
      have := hx _ (isRealOpen_realNhd one_pos) hr
      rw [realNhd_one] at this
      linarith [this.2, min_le_left x (r + 1)]
  · rintro x rfl
    simp only [mem_iInter]
    exact fun _ _ h => h

/-- **Section 10.5.** For the interval topology, the intersection of the open sets containing a
hyperreal $`r` is $`\{r\}`. -/
theorem iInter_isIntervalOpen_eq_singleton (r : ℝ*) :
    ⋂ (A : Set ℝ*) (_ : IsIntervalOpen A) (_ : r ∈ A), A = {r} := by
  apply Subset.antisymm
  · rw [← iInter_isRealOpen_eq_singleton r]
    intro x hx
    simp only [mem_iInter] at hx ⊢
    exact fun A hA hr => hx A hA.isIntervalOpen hr
  · rintro x rfl
    simp only [mem_iInter]
    exact fun _ _ h => h

/-- A nonempty hyperreal interval included in a real-radius neighbourhood of radius $`e` has
length at most $`2e`. -/
theorem sub_le_of_Ioo_subset_realNhd {a b : ℝ*} (hab : a < b) (h : Ioo a b ⊆ realNhd r e) :
    b - a ≤ 2 * (e : ℝ*) := by
  by_contra hlt
  push Not at hlt
  have h0 := show (a + b) / 2 ∈ Ioo (r - (e : ℝ*)) (r + e) from h ⟨by linarith, by linarith⟩
  have he : (0 : ℝ*) < e := by linarith [h0.1, h0.2]
  have h1 : a + (b - a - 2 * e) / 3 ∈ Ioo a b := by constructor <;> linarith
  have h2 : b - (b - a - 2 * e) / 3 ∈ Ioo a b := by constructor <;> linarith
  have h3 := (show _ ∈ Ioo (r - (e : ℝ*)) (r + e) from h h1).1
  have h4 := (show _ ∈ Ioo (r - (e : ℝ*)) (r + e) from h h2).2
  linarith

/-- **Section 10.5, counterexample.** The interval $`(0, \omega)` is not the intersection of
two real-radius neighbourhoods. -/
theorem Ioo_zero_omega_ne_realNhd_inter_realNhd (r s : ℝ*) (e d : ℝ) :
    Ioo (0 : ℝ*) ω ≠ realNhd r e ∩ realNhd s d := by
  intro h
  have hpos : (0 : ℝ*) < ω := by simpa using real_lt_omega 0
  have h1 := sub_le_of_Ioo_subset_realNhd (r := r) (e := e) hpos
    (h ▸ inter_subset_left)
  have h2 := real_lt_omega (2 * e)
  push_cast at h2
  linarith

/-- **Section 10.5, corrected.** A hyperreal interval $`(a, b)` of length at most $`2e`, for a
real $`e`, is the intersection of the two real-radius neighbourhoods of radius $`e` that
start at $`a` and end at $`b`. The book makes this claim for every hyperreal interval, but an
interval of unlimited length is not such an intersection
({name}`Goldblatt.Ioo_zero_omega_ne_realNhd_inter_realNhd`). -/
theorem Ioo_eq_realNhd_inter_realNhd {a b : ℝ*} (h : b - a ≤ 2 * (e : ℝ*)) :
    Ioo a b = realNhd (a + e) e ∩ realNhd (b - e) e := by
  ext x
  simp only [realNhd, mem_inter_iff, mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, -⟩, -, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- **Section 10.5.** Any topology on the hyperreal line in which all real-radius
neighbourhoods are open contains every interval-open set. Every point of an interval
$`(a, b)` lies in a subinterval of length at most $`2`, and such a subinterval is the
intersection of two real-radius neighbourhoods of radius $`1`. -/
theorem isOpen_of_isIntervalOpen_of_realNhd (t : TopologicalSpace ℝ*)
    (h : ∀ (r : ℝ*) (e : ℝ), 0 < e → IsOpen[t] (realNhd r e)) (hA : IsIntervalOpen A) :
    IsOpen[t] A := by
  let _ := t
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨a, b, hxab, hsub⟩ := isIntervalOpen_iff.1 hA x hx
  refine ⟨Ioo (max a (x - 1)) (min b (x + 1)), ?_, ?_, ?_⟩
  · exact fun z hz => hsub
      ⟨lt_of_le_of_lt (le_max_left _ _) hz.1, lt_of_lt_of_le hz.2 (min_le_left _ _)⟩
  · have hlen : min b (x + 1) - max a (x - 1) ≤ 2 * ((1 : ℝ) : ℝ*) := by
      rw [Hyperreal.coe_one]
      linarith [min_le_right b (x + 1), le_max_right a (x - 1)]
    rw [Ioo_eq_realNhd_inter_realNhd hlen]
    exact (h _ 1 one_pos).inter (h _ 1 one_pos)
  · exact ⟨max_lt hxab.1 (by linarith), lt_min hxab.2 (by linarith)⟩

/-! ### Enlargements of open sets of reals -/

/-- **Exercise 10.5.2(i).** If $`A` is an open set of real numbers then $`{}^*A` is
interval-open. A point $`[s_n]` of $`{}^*A` has $`s_n \in A` for almost all $`n`; choosing
radii $`e_n > 0` with $`(s_n - e_n, s_n + e_n) \subseteq A` gives the hyperreal interval
$`([s_n - e_n], [s_n + e_n])` about the point, inside $`{}^*A`. -/
theorem isIntervalOpen_starSet_of_isOpen {A : Set ℝ} (hA : IsOpen A) :
    IsIntervalOpen (⋆A : Set ℝ*) := by
  rw [isIntervalOpen_iff]
  intro x hx
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep x
  have hs := hyperreal_ofSeq_mem_starSet.1 hx
  have key : ∀ n, ∃ e : ℝ, 0 < e ∧ (s n ∈ A → Ioo (s n - e) (s n + e) ⊆ A) := by
    intro n
    by_cases hn : s n ∈ A
    · obtain ⟨e, he, h⟩ := isOpen_iff_forall_isInteriorPoint.1 hA _ hn
      exact ⟨e, he, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hn⟩
  choose e he hsub using key
  refine ⟨Hyperreal.ofSeq fun n => s n - e n, Hyperreal.ofSeq fun n => s n + e n, ⟨?_, ?_⟩, ?_⟩
  · exact ofSeq_lt_ofSeq_iff.2 (Eventually.of_forall fun n => by linarith [he n])
  · exact ofSeq_lt_ofSeq_iff.2 (Eventually.of_forall fun n => by linarith [he n])
  · intro y hy
    obtain ⟨t, rfl⟩ := hyperreal_exists_rep y
    have h1 := ofSeq_lt_ofSeq_iff.1 hy.1
    have h2 := ofSeq_lt_ofSeq_iff.1 hy.2
    rw [hyperreal_ofSeq_mem_starSet]
    filter_upwards [hs, h1, h2] with n hn h1 h2
    exact hsub n hn ⟨h1, h2⟩

section DisjointIntervals

variable {a b : ℕ → ℝ}

/-- The right end point of a nonempty member of a family of pairwise disjoint open intervals
belongs to none of them. -/
private theorem right_endpoint_notMem {n : ℕ} (hn : a n < b n)
    (hdisj : Pairwise (Function.onFun Disjoint fun n => Ioo (a n) (b n))) :
    b n ∉ ⋃ m, Ioo (a m) (b m) := by
  intro h
  obtain ⟨m, hm⟩ := mem_iUnion.1 h
  have hne : m ≠ n := by
    rintro rfl
    exact lt_irrefl _ hm.2
  have h1 : max (a n) (a m) < b n := max_lt hn hm.1
  have hz_m : (max (a n) (a m) + b n) / 2 ∈ Ioo (a m) (b m) :=
    ⟨by linarith [le_max_right (a n) (a m)], by linarith [hm.2]⟩
  have hz_n : (max (a n) (a m) + b n) / 2 ∈ Ioo (a n) (b n) :=
    ⟨by linarith [le_max_left (a n) (a m)], by linarith⟩
  exact Set.disjoint_left.1 (hdisj hne) hz_m hz_n

/-- The left end point of one of a family of pairwise disjoint nonempty open intervals belongs
to none of them. -/
private theorem left_endpoint_notMem (hab : ∀ n, a n < b n)
    (hdisj : Pairwise (Function.onFun Disjoint fun n => Ioo (a n) (b n))) (n : ℕ) :
    a n ∉ ⋃ m, Ioo (a m) (b m) := by
  intro h
  obtain ⟨m, hm⟩ := mem_iUnion.1 h
  have hne : m ≠ n := by
    rintro rfl
    exact lt_irrefl _ hm.1
  have h1 : a n < min (b n) (b m) := lt_min (hab n) hm.2
  have hz_m : (a n + min (b n) (b m)) / 2 ∈ Ioo (a m) (b m) :=
    ⟨by linarith [hm.1], by linarith [min_le_right (b n) (b m)]⟩
  have hz_n : (a n + min (b n) (b m)) / 2 ∈ Ioo (a n) (b n) :=
    ⟨by linarith, by linarith [min_le_left (b n) (b m)]⟩
  exact Set.disjoint_left.1 (hdisj hne) hz_m hz_n

/-- **Exercise 10.5.2(ii), under weaker hypotheses.** For the union $`A` of a sequence of
pairwise disjoint open intervals of which at least one is nonempty, some element of $`{}^*A`
is infinitely close to something not in $`{}^*A`. The right end point $`b_n` of a nonempty
interval is a real number outside $`A` that is a closure point of $`A`, so by
Theorem 10.1.1(3) it is infinitely close to a point of $`{}^*A`. No condition on the lengths
is used. -/
theorem exists_mem_starSet_infClose_notMem_of_exists_lt (hab : ∃ n, a n < b n)
    (hdisj : Pairwise (Function.onFun Disjoint fun n => Ioo (a n) (b n))) :
    ∃ x ∈ (⋆(⋃ n, Ioo (a n) (b n)) : Set ℝ*),
      ∃ y ∉ (⋆(⋃ n, Ioo (a n) (b n)) : Set ℝ*), x ≊ y := by
  obtain ⟨n, hn⟩ := hab
  have hcl : IsClosurePoint (⋃ m, Ioo (a m) (b m)) (b n) := by
    intro e he
    have h1 : max (a n) (b n - e) < b n := max_lt hn (sub_lt_self (b n) he)
    have h2 := le_max_left (a n) (b n - e)
    have h3 := le_max_right (a n) (b n - e)
    exact ⟨(max (a n) (b n - e) + b n) / 2, ⟨by linarith, by linarith⟩,
      mem_iUnion.2 ⟨n, by linarith, by linarith⟩⟩
  obtain ⟨x, hx, hbx⟩ := isClosurePoint_iff_exists_infClose.1 hcl
  exact ⟨x, hx, b n, fun h => right_endpoint_notMem hn hdisj (coe_mem_starSet.1 h), hbx.symm⟩

/-- **Exercise 10.5.2(ii), conclusion under weaker hypotheses.** The enlargement of the union
of a sequence of pairwise disjoint open intervals, at least one of them nonempty, is not
S-open. -/
theorem not_isSOpen_starSet_iUnion_Ioo_of_exists_lt (hab : ∃ n, a n < b n)
    (hdisj : Pairwise (Function.onFun Disjoint fun n => Ioo (a n) (b n))) :
    ¬ IsSOpen (⋆(⋃ n, Ioo (a n) (b n)) : Set ℝ*) := by
  intro h
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_mem_starSet_infClose_notMem_of_exists_lt hab hdisj
  exact hy (h.hal_subset hx hxy)

/-- **Exercise 10.5.2(ii).** Let $`A` be the union of a sequence of pairwise disjoint nonempty
open intervals $`A_n = (a_n, b_n)` with the length of $`A_n` less than $`\frac1{n+1}` (the
book indexes from $`1` and writes $`\frac1n`). Then some element of $`{}^*A` is infinitely
close to something not in $`{}^*A`: the class of the midpoints is in $`{}^*A`, the class of
the right end points is not, and their difference is infinitesimal.

The intervals are taken to be nonempty, as the word interval suggests. This part does not need
all of that, nor the bound on the lengths: one nonempty interval is enough, see
{name}`Goldblatt.exists_mem_starSet_infClose_notMem_of_exists_lt`. -/
theorem exists_mem_starSet_infClose_notMem (hab : ∀ n, a n < b n)
    (hdisj : Pairwise (Function.onFun Disjoint fun n => Ioo (a n) (b n)))
    (hlen : ∀ n, b n - a n < 1 / ((n : ℝ) + 1)) :
    ∃ x ∈ (⋆(⋃ n, Ioo (a n) (b n)) : Set ℝ*),
      ∃ y ∉ (⋆(⋃ n, Ioo (a n) (b n)) : Set ℝ*), x ≊ y := by
  refine ⟨Hyperreal.ofSeq fun n => (a n + b n) / 2, ?_, Hyperreal.ofSeq b, ?_, ?_⟩
  · exact hyperreal_ofSeq_mem_starSet.2 (Eventually.of_forall fun n =>
      mem_iUnion.2 ⟨n, by linarith [hab n], by linarith [hab n]⟩)
  · intro h
    obtain ⟨n, hn⟩ := (hyperreal_ofSeq_mem_starSet.1 h).exists
    exact right_endpoint_notMem (hab n) hdisj hn
  · rw [ofSeq_infClose_ofSeq_iff]
    intro η hη
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (eventually_lt_nhds hη)
    refine (eventually_hyperfilter_of_eventually_atTop this).mono fun n hn => ?_
    rw [abs_lt]
    constructor <;> linarith [hab n, hlen n]

/-- **Exercise 10.5.2(ii), conclusion.** For $`A` as in the exercise, $`{}^*A` is not
S-open, since an S-open set contains the halo of each of its points. -/
theorem not_isSOpen_starSet_iUnion_Ioo (hab : ∀ n, a n < b n)
    (hdisj : Pairwise (Function.onFun Disjoint fun n => Ioo (a n) (b n)))
    (hlen : ∀ n, b n - a n < 1 / ((n : ℝ) + 1)) :
    ¬ IsSOpen (⋆(⋃ n, Ioo (a n) (b n)) : Set ℝ*) := by
  intro h
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_mem_starSet_infClose_notMem hab hdisj hlen
  exact hy (h.hal_subset hx hxy)

/-- **Exercise 10.5.2(iii).** For $`A` as in the exercise, $`{}^*A` contains a point that
belongs to no real-radius neighbourhood included in $`{}^*A`. The point is the class of the
midpoints: a real-radius neighbourhood $`([s_n - e], [s_n + e])` containing it is, at almost
every index, longer than $`A_n`, so it reaches an end point of $`A_n`, and the class of those
end points lies in the neighbourhood but not in $`{}^*A`.

Here the nonemptiness of the intervals matters: the conclusion needs infinitely many of them
to be nonempty, since the enlargement is real-open when only finitely many are
({name}`Goldblatt.isRealOpen_starSet_iUnion_Ioo_of_finite`). The statement assumes all of them
nonempty. -/
theorem exists_mem_starSet_forall_realNhd_not_subset (hab : ∀ n, a n < b n)
    (hdisj : Pairwise (Function.onFun Disjoint fun n => Ioo (a n) (b n)))
    (hlen : ∀ n, b n - a n < 1 / ((n : ℝ) + 1)) :
    ∃ x ∈ (⋆(⋃ n, Ioo (a n) (b n)) : Set ℝ*), ∀ (r : ℝ*) (e : ℝ), 0 < e → x ∈ realNhd r e →
      ¬ realNhd r e ⊆ ⋆(⋃ n, Ioo (a n) (b n)) := by
  classical
  refine ⟨Hyperreal.ofSeq fun n => (a n + b n) / 2,
    hyperreal_ofSeq_mem_starSet.2 (Eventually.of_forall fun n =>
      mem_iUnion.2 ⟨n, by linarith [hab n], by linarith [hab n]⟩), ?_⟩
  intro r e he hx hsub
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep r
  have hr1 : Hyperreal.ofSeq s - (e : ℝ*) = Hyperreal.ofSeq fun n => s n - e := rfl
  have hr2 : Hyperreal.ofSeq s + (e : ℝ*) = Hyperreal.ofSeq fun n => s n + e := rfl
  unfold realNhd at hx hsub
  rw [hr1, hr2] at hx hsub
  have h1 := ofSeq_lt_ofSeq_iff.1 hx.1
  have h2 := ofSeq_lt_ofSeq_iff.1 hx.2
  have h3 : ∀ᶠ n : ℕ in hyperfilter ℕ, 1 / ((n : ℝ) + 1) < 2 * e :=
    eventually_hyperfilter_of_eventually_atTop
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (eventually_lt_nhds (by positivity)))
  have hw : (Hyperreal.ofSeq fun n => if s n - e < a n then a n else b n) ∈
      Ioo (Hyperreal.ofSeq fun n => s n - e) (Hyperreal.ofSeq fun n => s n + e) := by
    constructor
    · rw [ofSeq_lt_ofSeq_iff]
      filter_upwards [h1, h2, h3] with n h1 h2 h3
      by_cases hc : s n - e < a n
      · simp only [hc, ↓reduceIte]
      · simp only [hc, ↓reduceIte]
        linarith [hab n]
    · rw [ofSeq_lt_ofSeq_iff]
      filter_upwards [h1, h2, h3] with n h1 h2 h3
      by_cases hc : s n - e < a n
      · simp only [hc, ↓reduceIte]
        linarith [hab n]
      · simp only [hc, ↓reduceIte]
        linarith [hab n, hlen n, not_lt.1 hc]
  obtain ⟨n, hn⟩ := (hyperreal_ofSeq_mem_starSet.1 (hsub hw)).exists
  by_cases hc : s n - e < a n
  · simp only [hc, ↓reduceIte] at hn
    exact left_endpoint_notMem hab hdisj n hn
  · simp only [hc, ↓reduceIte] at hn
    exact right_endpoint_notMem (hab n) hdisj hn

/-- **Exercise 10.5.2(iii), conclusion.** For $`A` as in the exercise, $`{}^*A` is not
real-open. -/
theorem not_isRealOpen_starSet_iUnion_Ioo (hab : ∀ n, a n < b n)
    (hdisj : Pairwise (Function.onFun Disjoint fun n => Ioo (a n) (b n)))
    (hlen : ∀ n, b n - a n < 1 / ((n : ℝ) + 1)) :
    ¬ IsRealOpen (⋆(⋃ n, Ioo (a n) (b n)) : Set ℝ*) := by
  intro h
  obtain ⟨x, hx, hno⟩ := exists_mem_starSet_forall_realNhd_not_subset hab hdisj hlen
  obtain ⟨r, e, he, hxr, hsub⟩ := isRealOpen_iff.1 h x hx
  exact hno r e he hxr hsub

end DisjointIntervals

/-- **Exercise 10.5.2, non-vacuity.** The hypotheses of parts (ii) and (iii) are satisfied by
the intervals $`(n, n + \frac1{n+2})`. Hence there is an open set $`A` of real numbers whose
enlargement is interval-open but neither real-open nor S-open. -/
theorem exists_isOpen_starSet_not_isRealOpen :
    ∃ A : Set ℝ, IsOpen A ∧ IsIntervalOpen (⋆A : Set ℝ*) ∧ ¬ IsRealOpen (⋆A : Set ℝ*) ∧
      ¬ IsSOpen (⋆A : Set ℝ*) := by
  have hab : ∀ n : ℕ, (n : ℝ) < n + 1 / ((n : ℝ) + 2) := fun n => by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hlen : ∀ n : ℕ, (n : ℝ) + 1 / ((n : ℝ) + 2) - n < 1 / ((n : ℝ) + 1) := fun n => by
    have h1 : (n : ℝ) + 1 / ((n : ℝ) + 2) - n = 1 / ((n : ℝ) + 2) := by ring
    rw [h1]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hone : ∀ k : ℕ, 1 / ((k : ℝ) + 2) < 1 := fun k => by
    rw [div_lt_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ => Ioo (n : ℝ) (n + 1 / ((n : ℝ) + 2))) := by
    intro m n hmn
    refine Set.disjoint_left.2 fun x hx1 hx2 => ?_
    rcases lt_or_gt_of_ne hmn with h | h
    · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
      linarith [hx1.2, hx2.1, hone m]
    · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
      linarith [hx2.2, hx1.1, hone n]
  have hA : IsOpen (⋃ n : ℕ, Ioo (n : ℝ) (n + 1 / ((n : ℝ) + 2))) :=
    isOpen_iUnion fun _ => isOpen_Ioo
  exact ⟨_, hA, isIntervalOpen_starSet_of_isOpen hA,
    not_isRealOpen_starSet_iUnion_Ioo hab hdisj hlen,
    not_isSOpen_starSet_iUnion_Ioo hab hdisj hlen⟩

end HyperTopologies

end Goldblatt
