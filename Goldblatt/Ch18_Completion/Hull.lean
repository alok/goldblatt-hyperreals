import Goldblatt.Ch18_Completion.Basic

/-!
# 18 (part 2). Nonstandard hulls: Section 18.3

This is the second of six parts of Chapter 18 (the overview is on the chapter page
{lit}`Goldblatt.Ch18_Completion`). For a metric space $`X` it constructs the nonstandard
hull, the quotient of the limited points of $`{}^*X` by infinite closeness, proves that it
is a complete metric space, and identifies the completion of $`X` inside it as the set of
classes of approachable points.
-/

noncomputable section

namespace Goldblatt.Completion

open Filter

open scoped Hyperreal

/-!
## 18.3 Nonstandard Hulls

The transform $`{}^*d` of a metric $`d` takes hyperreal values, so it is not a metric, but
it satisfies the metric axioms by transfer. Two points of $`{}^*X` are infinitely close when
their distance is infinitesimal and of limited distance when it is limited. A point is
limited when it is of limited distance from a point of $`X`. Taking the shadow of
$`{}^*d` on limited points and identifying infinitely close points gives a metric space, the
nonstandard hull, which contains $`X` and is always complete.

The hull can be too big to be a completion of $`X`. The points that matter are the
approachable ones, those within every positive real distance of a point of $`X`; their
classes form the closure of $`X` in the hull, and that is a completion of $`X`.
-/

section Pseudo

variable {X : Type*} [PseudoMetricSpace X]

/-- **Section 18.3.** The extended distance function $`{}^*d : {}^*X \times {}^*X \to
{}^*\mathbb R`, the transform of the metric. -/
def hdist (x y : Star X) : ℝ* := Germ.map₂ dist x y

theorem hdist_coe (f g : ℕ → X) :
    hdist (↑f : Star X) ↑g = Hyperreal.ofSeq fun i => dist (f i) (g i) := rfl

@[simp]
theorem hdist_const (a b : X) : hdist (↑a : Star X) ↑b = (dist a b : ℝ*) := rfl

/-- A strict inequality between extended distances and a real number, read off
representatives. -/
theorem hdist_coe_lt_iff {f g : ℕ → X} {r : ℝ} :
    hdist (↑f : Star X) ↑g < (r : ℝ*) ↔ ∀ᶠ i in hyperfilter ℕ, dist (f i) (g i) < r :=
  Hyperreal.ofSeq_lt_ofSeq (g := fun _ => r)

theorem hdist_nonneg (x y : Star X) : 0 ≤ hdist x y :=
  Germ.inductionOn₂ x y fun _ _ =>
    (Hyperreal.ofSeq_le_ofSeq (f := fun _ => 0)).2 (Eventually.of_forall fun _ => dist_nonneg)

@[simp]
theorem hdist_self (x : Star X) : hdist x x = 0 :=
  Germ.inductionOn x fun f => by
    show Hyperreal.ofSeq _ = Hyperreal.ofSeq (fun _ => 0)
    exact congrArg _ (funext fun i => dist_self (f i))

theorem hdist_comm (x y : Star X) : hdist x y = hdist y x :=
  Germ.inductionOn₂ x y fun f g => by
    show Hyperreal.ofSeq _ = Hyperreal.ofSeq _
    exact congrArg _ (funext fun i => dist_comm (f i) (g i))

/-- **Section 18.3.** The triangle inequality for $`{}^*d`, by transfer. -/
theorem hdist_triangle (x y z : Star X) : hdist x z ≤ hdist x y + hdist y z :=
  Germ.inductionOn₃ x y z fun f g h => by
    show Hyperreal.ofSeq _ ≤ Hyperreal.ofSeq (fun i => dist (f i) (g i) + dist (g i) (h i))
    exact Hyperreal.ofSeq_le_ofSeq.2 (Eventually.of_forall fun i => dist_triangle _ _ _)

theorem abs_hdist_sub_le (x y x' y' : Star X) :
    |hdist x y - hdist x' y'| ≤ hdist x x' + hdist y y' :=
  Germ.inductionOn₂ x y fun f g => Germ.inductionOn₂ x' y' fun f' g' => by
    show Hyperreal.ofSeq (fun i => |dist (f i) (g i) - dist (f' i) (g' i)|) ≤
      Hyperreal.ofSeq (fun i => dist (f i) (f' i) + dist (g i) (g' i))
    refine Hyperreal.ofSeq_le_ofSeq.2 (Eventually.of_forall fun i => ?_)
    have := dist_dist_dist_le (f i) (g i) (f' i) (g' i)
    rwa [Real.dist_eq] at this

/-- **Section 18.3.** Infinitesimal proximity: $`x \simeq y` when $`{}^*d(x, y)` is
infinitesimal. -/
def InfClose (x y : Star X) : Prop := Infinitesimal (hdist x y)

/-- **Section 18.3.** Limited proximity: $`x \sim y` when $`{}^*d(x, y)` is limited. -/
def LimClose (x y : Star X) : Prop := Limited (hdist x y)

theorem InfClose.limClose {x y : Star X} (h : InfClose x y) : LimClose x y :=
  Infinitesimal.limited h

@[refl]
theorem InfClose.refl (x : Star X) : InfClose x x := by
  unfold InfClose; rw [hdist_self]; exact infinitesimal_zero

@[symm]
theorem InfClose.symm {x y : Star X} (h : InfClose x y) : InfClose y x := by
  unfold InfClose at *; rwa [hdist_comm]

theorem InfClose.trans {x y z : Star X} (h₁ : InfClose x y) (h₂ : InfClose y z) :
    InfClose x z :=
  (Infinitesimal.add h₁ h₂).of_abs_le (by
    rw [abs_of_nonneg (hdist_nonneg x z),
      abs_of_nonneg (add_nonneg (hdist_nonneg x y) (hdist_nonneg y z))]
    exact hdist_triangle x y z)

@[refl]
theorem LimClose.refl (x : Star X) : LimClose x x := (InfClose.refl x).limClose

@[symm]
theorem LimClose.symm {x y : Star X} (h : LimClose x y) : LimClose y x := by
  unfold LimClose at *; rwa [hdist_comm]

theorem LimClose.trans {x y z : Star X} (h₁ : LimClose x y) (h₂ : LimClose y z) :
    LimClose x z :=
  (Limited.add h₁ h₂).of_abs_le (by
    rw [abs_of_nonneg (hdist_nonneg x z),
      abs_of_nonneg (add_nonneg (hdist_nonneg x y) (hdist_nonneg y z))]
    exact hdist_triangle x y z)

/-- **Section 18.3.** Infinitesimal proximity is an equivalence relation on $`{}^*X`. -/
theorem infClose_equivalence : Equivalence (InfClose (X := X)) :=
  ⟨InfClose.refl, InfClose.symm, InfClose.trans⟩

/-- **Section 18.3.** Limited proximity is an equivalence relation on $`{}^*X`. -/
theorem limClose_equivalence : Equivalence (LimClose (X := X)) :=
  ⟨LimClose.refl, LimClose.symm, LimClose.trans⟩

/-- **Section 18.3.** The halo of $`x`, its class under infinitesimal proximity. -/
def halo (x : Star X) : Set (Star X) := {y | InfClose x y}

/-- **Section 18.3.** The galaxy of $`x`, its class under limited proximity. -/
def galaxy (x : Star X) : Set (Star X) := {y | LimClose x y}

theorem halo_subset_galaxy (x : Star X) : halo x ⊆ galaxy x := fun _ h => InfClose.limClose h

/-- **Section 18.3.** A point of $`{}^*X` is limited if it is of limited distance from some
point of $`X`. -/
def LimitedPt (x : Star X) : Prop := ∃ a : X, LimClose x ↑a

theorem limitedPt_const (a : X) : LimitedPt (↑a : Star X) := ⟨a, LimClose.refl _⟩

theorem LimitedPt.of_limClose {x y : Star X} (hy : LimitedPt y) (h : LimClose x y) :
    LimitedPt x := by
  obtain ⟨a, ha⟩ := hy
  exact ⟨a, h.trans ha⟩

/-- **Section 18.3.** The halo of a limited point consists of limited points, so the
limited points are partitioned by their halos. -/
theorem LimitedPt.of_infClose {x y : Star X} (hy : LimitedPt y) (h : InfClose x y) :
    LimitedPt x := hy.of_limClose h.limClose

theorem halo_subset_limitedPt {x : Star X} (hx : LimitedPt x) : halo x ⊆ {y | LimitedPt y} :=
  fun _ h => hx.of_infClose (InfClose.symm h)

/-- Any two limited points are of limited distance from each other. This uses that any two
points of $`X` are of limited (indeed real) distance. -/
theorem LimitedPt.limClose {x y : Star X} (hx : LimitedPt x) (hy : LimitedPt y) :
    LimClose x y := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have hab : LimClose (↑a : Star X) ↑b := by
    unfold LimClose; rw [hdist_const]; exact limited_coe _
  exact (ha.trans hab).trans hb.symm

/-- **Section 18.3, the principal galaxy.** The set of limited points is the galaxy of any
point of $`X`; in particular it is a galaxy that includes $`X`. -/
theorem limitedPt_iff_mem_galaxy (a : X) {x : Star X} :
    LimitedPt x ↔ x ∈ galaxy (↑a : Star X) :=
  ⟨fun h => (limitedPt_const a).limClose h, fun h => ⟨a, LimClose.symm h⟩⟩

variable (X) in
/-- Infinitesimal proximity as a setoid on the limited points. -/
def limitedSetoid : Setoid {x : Star X // LimitedPt x} where
  r x y := InfClose x.1 y.1
  iseqv := ⟨fun x => InfClose.refl x.1, InfClose.symm, InfClose.trans⟩

variable (X) in
/-- **Section 18.3.** The nonstandard hull $`\widehat X` of a metric space: the set of
halos of limited points of $`{}^*X`, that is, the quotient of the limited points by
infinitesimal proximity. -/
def Hull : Type _ := Quotient (limitedSetoid X)

/-- The halo of a limited point, as a point of the nonstandard hull. -/
def Hull.mk (x : Star X) (hx : LimitedPt x) : Hull X := Quotient.mk (limitedSetoid X) ⟨x, hx⟩

theorem Hull.exists_rep (h : Hull X) : ∃ (x : Star X) (hx : LimitedPt x), Hull.mk x hx = h := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := Quotient.exists_rep h
  exact ⟨x, hx, rfl⟩

/-- Two limited points define the same point of the hull exactly when they are infinitely
close. -/
theorem Hull.mk_eq_mk {x y : Star X} {hx : LimitedPt x} {hy : LimitedPt y} :
    Hull.mk x hx = Hull.mk y hy ↔ InfClose x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem sh_hdist_congr {x y x' y' : Star X} (hx : LimitedPt x) (hy : LimitedPt y)
    (hxx : InfClose x x') (hyy : InfClose y y') : sh (hdist x y) = sh (hdist x' y') := by
  have hx' : LimitedPt x' := hx.of_infClose hxx.symm
  have hy' : LimitedPt y' := hy.of_infClose hyy.symm
  rw [sh_eq_sh_iff (hx.limClose hy) (hx'.limClose hy')]
  exact (Infinitesimal.add hxx hyy).of_abs_le (by
    rw [abs_of_nonneg (add_nonneg (hdist_nonneg x x') (hdist_nonneg y y'))]
    exact abs_hdist_sub_le x y x' y')

/-- **Section 18.3.** The metric of the nonstandard hull:
$`d(\operatorname{hal}(x), \operatorname{hal}(y)) = \operatorname{sh}({}^*d(x, y))`. It is
well defined because $`{}^*d(x,y) \simeq {}^*d(x',y')` when $`x \simeq x'` and
$`y \simeq y'`. -/
def Hull.dist' (h k : Hull X) : ℝ :=
  Quotient.liftOn₂ h k (fun x y => sh (hdist x.1 y.1)) fun x y _ _ hxx hyy =>
    sh_hdist_congr x.2 y.2 hxx hyy

instance : Dist (Hull X) := ⟨Hull.dist'⟩

@[simp]
theorem Hull.dist_mk (x y : Star X) (hx : LimitedPt x) (hy : LimitedPt y) :
    dist (Hull.mk x hx) (Hull.mk y hy) = sh (hdist x y) := rfl

/-- **Section 18.3.** The nonstandard hull is a metric space. Identifying infinitely close
points is what makes distinct points have positive distance. -/
instance : MetricSpace (Hull X) where
  dist_self h := by
    obtain ⟨x, hx, rfl⟩ := h.exists_rep
    rw [Hull.dist_mk, hdist_self]; exact sh_coe 0
  dist_comm h k := by
    obtain ⟨x, hx, rfl⟩ := h.exists_rep
    obtain ⟨y, hy, rfl⟩ := k.exists_rep
    rw [Hull.dist_mk, Hull.dist_mk, hdist_comm]
  dist_triangle h k l := by
    obtain ⟨x, hx, rfl⟩ := h.exists_rep
    obtain ⟨y, hy, rfl⟩ := k.exists_rep
    obtain ⟨z, hz, rfl⟩ := l.exists_rep
    simp only [Hull.dist_mk]
    rw [← sh_add (hx.limClose hy) (hy.limClose hz)]
    exact sh_le_sh (hx.limClose hz) (Limited.add (hx.limClose hy) (hy.limClose hz))
      (hdist_triangle x y z)
  eq_of_dist_eq_zero {h k} hd := by
    obtain ⟨x, hx, rfl⟩ := h.exists_rep
    obtain ⟨y, hy, rfl⟩ := k.exists_rep
    rw [Hull.dist_mk] at hd
    exact Hull.mk_eq_mk.2 ((sh_eq_zero_iff (hx.limClose hy)).1 hd)

/-- A real bound on the extended distance bounds the distance in the hull. -/
theorem Hull.dist_mk_le {x y : Star X} {hx : LimitedPt x} {hy : LimitedPt y} {r : ℝ}
    (h : hdist x y ≤ (r : ℝ*)) : dist (Hull.mk x hx) (Hull.mk y hy) ≤ r :=
  sh_le_of_le (hx.limClose hy) h

theorem Hull.lt_of_dist_mk_lt {x y : Star X} {hx : LimitedPt x} {hy : LimitedPt y} {r : ℝ}
    (h : dist (Hull.mk x hx) (Hull.mk y hy) < r) : hdist x y < (r : ℝ*) :=
  lt_of_sh_lt (hx.limClose hy) h

/-- **Section 18.3.** The inclusion of $`X` in its nonstandard hull,
$`a \mapsto \operatorname{hal}(a)`. -/
def Hull.of (a : X) : Hull X := Hull.mk ↑a (limitedPt_const a)

/-- **Section 18.3.** The inclusion of $`X` in its hull preserves distances, so $`X` is a
subspace of the hull. -/
theorem Hull.isometry_of : Isometry (Hull.of : X → Hull X) :=
  Isometry.of_dist_eq fun a b => by
    show sh (hdist (↑a : Star X) ↑b) = dist a b
    rw [hdist_const, sh_coe]

/-- **Section 18.3.** A point is approachable from $`X` if it is within every positive real
distance of some point of $`X`. -/
def Approachable (x : Star X) : Prop := ∀ e : ℝ, 0 < e → ∃ a : X, hdist x ↑a < (e : ℝ*)

/-- **Section 18.3.** A point is near to $`X` (nearstandard) if it is infinitely close to a
point of $`X`. -/
def Near (x : Star X) : Prop := ∃ a : X, InfClose x ↑a

theorem near_const (a : X) : Near (↑a : Star X) := ⟨a, InfClose.refl _⟩

/-- **Section 18.3.** Every point near to $`X` is approachable from $`X`. -/
theorem Near.approachable {x : Star X} (h : Near x) : Approachable x := by
  obtain ⟨a, ha⟩ := h
  intro e he
  refine ⟨a, ?_⟩
  have := ha e he
  rwa [abs_of_nonneg (hdist_nonneg _ _)] at this

/-- **Section 18.3.** Approachable points are limited. -/
theorem Approachable.limitedPt {x : Star X} (h : Approachable x) : LimitedPt x := by
  obtain ⟨a, ha⟩ := h 1 one_pos
  exact ⟨a, 1, by rw [abs_of_nonneg (hdist_nonneg _ _)]; exact ha.le⟩

/-- A point that is within every positive real distance of an approachable point is
approachable. -/
theorem Approachable.of_forall_exists {x : Star X}
    (h : ∀ e : ℝ, 0 < e → ∃ z : Star X, Approachable z ∧ hdist x z < (e : ℝ*)) :
    Approachable x := by
  intro e he
  obtain ⟨z, hz, hxz⟩ := h (e / 2) (half_pos he)
  obtain ⟨a, ha⟩ := hz (e / 2) (half_pos he)
  refine ⟨a, ?_⟩
  calc hdist x ↑a ≤ hdist x z + hdist z ↑a := hdist_triangle _ _ _
    _ < ((e / 2 : ℝ) : ℝ*) + ((e / 2 : ℝ) : ℝ*) := add_lt_add hxz ha
    _ = (e : ℝ*) := by rw [← Hyperreal.coe_add, add_halves]

/-- **Section 18.3.** A point infinitely close to an approachable point is approachable:
the halo of an approachable point consists of approachable points. -/
theorem Approachable.of_infClose {x y : Star X} (hy : Approachable y) (h : InfClose x y) :
    Approachable x :=
  Approachable.of_forall_exists fun e he =>
    ⟨y, hy, by have := h e he; rwa [abs_of_nonneg (hdist_nonneg _ _)] at this⟩

theorem approachable_congr {x y : Star X} (h : InfClose x y) : Approachable x ↔ Approachable y :=
  ⟨fun hx => hx.of_infClose h.symm, fun hy => hy.of_infClose h⟩

/-- A point of the hull is approachable if it is the halo of an approachable point. -/
def Hull.IsApproachable (h : Hull X) : Prop :=
  Quotient.liftOn h (fun x => Approachable x.1) fun _ _ hxy => propext (approachable_congr hxy)

@[simp]
theorem Hull.isApproachable_mk {x : Star X} {hx : LimitedPt x} :
    (Hull.mk x hx).IsApproachable ↔ Approachable x := Iff.rfl

theorem Hull.isApproachable_of (a : X) : (Hull.of a).IsApproachable :=
  (near_const a).approachable

/-- **Section 18.3.** The approachable points of the hull are exactly the points of the
closure of $`X` in the hull. -/
theorem Hull.isApproachable_iff_mem_closure {h : Hull X} :
    h.IsApproachable ↔ h ∈ closure (Set.range (Hull.of : X → Hull X)) := by
  obtain ⟨x, hx, rfl⟩ := h.exists_rep
  rw [Hull.isApproachable_mk, Metric.mem_closure_range_iff]
  constructor
  · intro hap e he
    obtain ⟨a, ha⟩ := hap (e / 2) (half_pos he)
    exact ⟨a, (Hull.dist_mk_le ha.le).trans_lt (half_lt_self he)⟩
  · intro hcl e he
    obtain ⟨a, ha⟩ := hcl e he
    exact ⟨a, Hull.lt_of_dist_mk_lt ha⟩

theorem Hull.isClosed_isApproachable : IsClosed {h : Hull X | h.IsApproachable} := by
  have : {h : Hull X | h.IsApproachable} = closure (Set.range (Hull.of : X → Hull X)) :=
    Set.ext fun _ => Hull.isApproachable_iff_mem_closure
  rw [this]; exact isClosed_closure

/-- **Theorem 18.3.1, the nonstandard core.** Let $`x_0, x_1, \dots` be points of
$`{}^*X`, with $`x_n` represented by the sequence $`r_n`, and suppose that for each $`n`
there is a real bound $`c_n` and a standard index $`k_n` such that
$`{}^*d(x_m, x_{k_n}) < c_n` for all standard $`m \ge k_n`. Then there is an unlimited
hypernatural $`K` such that the term $`x_K` of the extended hypersequence satisfies
$`{}^*d(x_K, x_{k_n}) < c_n` for all standard $`n`. Here $`K = [\kappa]` and
$`x_K = [i \mapsto r_{\kappa(i)}(i)]`. The book obtains $`K` by overflow followed by
Theorem 15.4.3; both steps are applications of countable saturation, used here once. -/
theorem exists_unlimited_index (r : ℕ → ℕ → X) (k : ℕ → ℕ) (c : ℕ → ℝ)
    (h : ∀ n m, k n ≤ m → hdist (↑(r m) : Star X) ↑(r (k n)) < (c n : ℝ*)) :
    ∃ κ : ℕ → ℕ, Unlimited (↑κ : Star ℕ) ∧
      ∀ n, hdist (↑(fun i => r (κ i) i) : Star X) ↑(r (k n)) < (c n : ℝ*) := by
  let A : ℕ → ℕ → Set ℕ := fun n i => {j | n ≤ j ∧ dist (r j i) (r (k n) i) < c n}
  have hA : ∀ n, ∀ᶠ i in hyperfilter ℕ, ∃ j, ∀ m ≤ n, j ∈ A m i := by
    intro n
    let J : ℕ := max n ((Finset.range (n + 1)).sup k)
    have hJ : ∀ m ∈ Finset.range (n + 1),
        ∀ᶠ i in hyperfilter ℕ, dist (r J i) (r (k m) i) < c m := fun m hm =>
      hdist_coe_lt_iff.1 (h m J ((Finset.le_sup hm).trans (le_max_right _ _)))
    filter_upwards [((Finset.range (n + 1)).eventually_all).2 hJ] with i hi
    exact ⟨J, fun m hm => ⟨hm.trans (le_max_left _ _),
      hi m (Finset.mem_range.2 (Nat.lt_succ_of_le hm))⟩⟩
  obtain ⟨κ, hκ⟩ := countable_saturation A hA
  refine ⟨κ, unlimited_coe_iff.2 fun n => ?_, fun n => ?_⟩
  · exact (hκ (n + 1)).mono fun i hi => hi.1
  · exact hdist_coe_lt_iff.2 ((hκ n).mono fun i hi => hi.2)

/-- **Theorem 18.3.1.** The nonstandard hull of a metric space is complete. Given a Cauchy
sequence of halos $`\operatorname{hal}(x_n)`, the sequence converges to
$`\operatorname{hal}(x_K)` for a suitable unlimited $`K`. -/
instance Hull.instCompleteSpace : CompleteSpace (Hull X) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  choose x hx hxu using fun n => (u n).exists_rep
  choose r hr using fun n => (x n).exists_rep
  have hc : ∀ n : ℕ, (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := fun n => by positivity
  choose k hk using fun n => (Metric.cauchySeq_iff'.1 hu) _ (hc n)
  have h1 : ∀ n m, k n ≤ m →
      hdist (↑(r m) : Star X) ↑(r (k n)) < ((1 / (2 * ((n : ℝ) + 1)) : ℝ) : ℝ*) := by
    intro n m hm
    have := hk n m hm
    rw [← hxu m, ← hxu (k n)] at this
    rw [hr, hr]
    exact Hull.lt_of_dist_mk_lt this
  obtain ⟨κ, -, hκ⟩ := exists_unlimited_index r k _ h1
  set y : Star X := ↑(fun i => r (κ i) i) with hy
  have hylim : LimitedPt y := by
    refine (hx (k 0)).of_limClose ⟨1 / (2 * (((0 : ℕ) : ℝ) + 1)), ?_⟩
    rw [abs_of_nonneg (hdist_nonneg _ _), ← hr (k 0)]
    exact (hκ 0).le
  refine ⟨Hull.mk y hylim, Metric.tendsto_atTop.2 fun e he => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt he
  refine ⟨k n, fun m hm => ?_⟩
  have h2 : dist (u m) (u (k n)) < 1 / (2 * ((n : ℝ) + 1)) := hk n m hm
  have h3 : dist (u (k n)) (Hull.mk y hylim) ≤ 1 / (2 * ((n : ℝ) + 1)) := by
    rw [← hxu (k n), dist_comm]
    refine Hull.dist_mk_le ?_
    rw [← hr (k n)]
    exact (hκ n).le
  calc dist (u m) (Hull.mk y hylim) ≤ dist (u m) (u (k n)) + dist (u (k n)) (Hull.mk y hylim) :=
        dist_triangle _ _ _
    _ < 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) := add_lt_add_of_lt_of_le h2 h3
    _ = 1 / ((n : ℝ) + 1) := by field_simp; ring
    _ < e := hn

variable (X) in
/-- **Section 18.3.** The set $`{}^*X^{\mathrm{ap}}/{\simeq}` of halos of approachable
points, as a subspace of the nonstandard hull. -/
abbrev ApHull : Type _ := {h : Hull X // h.IsApproachable}

/-- The inclusion of $`X` in the space of halos of approachable points. -/
def ApHull.of (a : X) : ApHull X := ⟨Hull.of a, Hull.isApproachable_of a⟩

theorem ApHull.isometry_of : Isometry (ApHull.of : X → ApHull X) :=
  Isometry.of_dist_eq fun a b => Hull.isometry_of.dist_eq a b

/-- **Theorem 18.3.2, completeness.** The space of halos of approachable points is
complete: it is a closed subset of the nonstandard hull, because a limit of approachable
points is approachable. -/
instance ApHull.instCompleteSpace : CompleteSpace (ApHull X) :=
  Hull.isClosed_isApproachable.completeSpace_coe

/-- **Theorem 18.3.2, density.** $`X` is dense in the space of halos of approachable
points. -/
theorem ApHull.denseRange_of : DenseRange (ApHull.of : X → ApHull X) := by
  rw [denseRange_iff_forall_exists_dist_lt]
  rintro ⟨h, hap⟩ e he
  obtain ⟨x, hx, rfl⟩ := h.exists_rep
  obtain ⟨a, ha⟩ := (Hull.isApproachable_mk.1 hap) (e / 2) (half_pos he)
  exact ⟨a, (Hull.dist_mk_le (hy := limitedPt_const a) ha.le).trans_lt (half_lt_self he)⟩

end Pseudo

section Metric

variable {X : Type*} [MetricSpace X]

/-- **Section 18.3.** Distinct points of $`X` have distinct (indeed disjoint) halos, so
$`X` is identified with a subset of its hull. -/
theorem Hull.of_injective : Function.Injective (Hull.of : X → Hull X) :=
  Hull.isometry_of.injective

theorem infClose_const_iff {a b : X} : InfClose (↑a : Star X) ↑b ↔ a = b := by
  unfold InfClose
  rw [hdist_const, infinitesimal_coe_iff, dist_eq_zero]

theorem halo_disjoint_of_ne {a b : X} (h : a ≠ b) :
    Disjoint (halo (↑a : Star X)) (halo (↑b : Star X)) :=
  Set.disjoint_left.2 fun _ h1 h2 => h (infClose_const_iff.1 (InfClose.trans h1 (InfClose.symm h2)))

/-- **Theorem 18.3.2.** The space $`({}^*X^{\mathrm{ap}}/{\simeq}, d)` of halos of
approachable points is a completion of $`(X, d)`. -/
theorem isCompletion_apHull : IsCompletion (ApHull.of : X → ApHull X) :=
  ⟨ApHull.isometry_of, inferInstance, ApHull.denseRange_of⟩

variable (X) in
/-- **Theorem 18.3.2, compared with Mathlib.** The completion by enlargement is isometric
to Mathlib's completion {name}`UniformSpace.Completion`, by an isometry that fixes $`X`. -/
def completionEquivApHull : UniformSpace.Completion X ≃ᵢ ApHull X :=
  isCompletion_apHull.equiv

@[simp]
theorem completionEquivApHull_coe (a : X) :
    completionEquivApHull X (a : UniformSpace.Completion X) = ApHull.of a :=
  isCompletion_apHull.equiv_coe a

/-- **Section 18.3.** A limited point that is not near to $`X` gives a point of the hull
that is not a point of $`X`, and conversely. -/
theorem Hull.mk_mem_range_of_iff {x : Star X} {hx : LimitedPt x} :
    Hull.mk x hx ∈ Set.range (Hull.of : X → Hull X) ↔ Near x := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, Hull.mk_eq_mk.1 ha.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (Hull.mk_eq_mk.2 ha).symm⟩

/-- **Corollary 18.3.3.** If every point of $`{}^*X` that is approachable from $`X` is near
to $`X`, then $`(X, d)` is complete. -/
theorem completeSpace_of_approachable_near (h : ∀ x : Star X, Approachable x → Near x) :
    CompleteSpace X := by
  have hsurj : Function.Surjective (ApHull.of : X → ApHull X) := by
    rintro ⟨k, hk⟩
    obtain ⟨x, hx, rfl⟩ := k.exists_rep
    obtain ⟨a, ha⟩ := h x (Hull.isApproachable_mk.1 hk)
    exact ⟨a, Subtype.ext (Hull.mk_eq_mk.2 ha).symm⟩
  rw [completeSpace_iff_isComplete_range ApHull.isometry_of.isUniformInducing,
    hsurj.range_eq]
  exact isComplete_univ

/-- **Exercise 18.3.4.** Conversely, in the enlargement of a complete metric space every
point approachable from $`X` is near to $`X`. -/
theorem Approachable.near [CompleteSpace X] {x : Star X} (hx : Approachable x) : Near x := by
  have hc : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose a ha using fun n : ℕ => hx _ (hc n)
  have hlim : Tendsto (fun n => Hull.of (a n)) atTop (nhds (Hull.mk x hx.limitedPt)) := by
    refine Metric.tendsto_atTop.2 fun e he => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt he
    refine ⟨n, fun m hm => ?_⟩
    rw [dist_comm]
    refine (Hull.dist_mk_le (hy := limitedPt_const (a m)) (ha m).le).trans_lt (lt_of_le_of_lt ?_ hn)
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hm)
  have hcauchy : CauchySeq a := by
    refine (Hull.isometry_of.isUniformInducing.cauchy_map_iff).1 ?_
    rw [Filter.map_map]
    exact hlim.cauchySeq
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim' : Tendsto (fun n => Hull.of (a n)) atTop (nhds (Hull.of b)) :=
    (Hull.isometry_of.continuous.tendsto b).comp hb
  exact ⟨b, Hull.mk_eq_mk.1 (tendsto_nhds_unique hlim hlim')⟩

/-- **Corollary 18.3.3 and Exercise 18.3.4.** A metric space is complete if and only if
every approachable point of its enlargement is near to it. -/
theorem completeSpace_iff_approachable_near :
    CompleteSpace X ↔ ∀ x : Star X, Approachable x → Near x :=
  ⟨fun _ _ hx => hx.near, completeSpace_of_approachable_near⟩

end Metric

/-!
### The rationals

For the rationals with the Euclidean metric the two constructions agree: every limited
hyperrational is approachable from $`\mathbb Q`, because its shadow is a real number and
real numbers are approximated by rationals. So the nonstandard hull of $`\mathbb Q` is its
completion, and the shadow map identifies it with $`\mathbb R`. A hyperrational infinitely
close to $`\sqrt 2` is approachable from $`\mathbb Q` but not near to $`\mathbb Q`, which
reflects the incompleteness of $`\mathbb Q`.
-/

section Rationals

/-- On the hyperrationals the extended Euclidean distance is $`|x - y|`, computed in the
hyperreals. -/
theorem hdist_rat (x y : Star ℚ) : hdist x y = |hratCast x - hratCast y| :=
  Germ.inductionOn₂ x y fun f g => by
    show Hyperreal.ofSeq (fun i => dist (f i) (g i)) =
      Hyperreal.ofSeq (fun i => |(f i : ℝ) - (g i : ℝ)|)
    exact congrArg _ (funext fun i => Rat.dist_eq (f i) (g i))

/-- **Section 18.3.** A hyperrational is limited in the sense of the Euclidean metric
exactly when it is a limited hyperreal. -/
theorem limitedPt_rat_iff {x : Star ℚ} : LimitedPt x ↔ Limited (hratCast x) := by
  constructor
  · rintro ⟨a, ha⟩
    have h1 : Limited (hratCast x - hratCast (Germ.const a)) := by
      have : Limited (hdist x (Germ.const a)) := ha
      rw [hdist_rat] at this
      exact this.of_abs_le (by rw [abs_abs])
    have h2 := h1.add (limited_coe (a : ℝ))
    rwa [hratCast_const, sub_add_cancel] at h2
  · intro h
    refine ⟨0, ?_⟩
    show Limited (hdist x (Germ.const 0))
    rw [hdist_rat, hratCast_const, Rat.cast_zero, Hyperreal.coe_zero, sub_zero]
    exact h.abs

/-- **Section 18.3.** Every limited hyperrational is approachable from $`\mathbb Q`:
$`{}^*\mathbb Q^{\lim} = {}^*\mathbb Q^{\mathrm{ap}}`. -/
theorem approachable_of_limitedPt_rat {x : Star ℚ} (hx : LimitedPt x) : Approachable x := by
  have hlim := limitedPt_rat_iff.1 hx
  intro e he
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show sh (hratCast x) - e / 2 < sh (hratCast x) + e / 2
    by linarith)
  refine ⟨q, ?_⟩
  show hdist x (Germ.const q) < (e : ℝ*)
  rw [hdist_rat, hratCast_const]
  have h1 := infinitesimal_sub_sh hlim (e / 2) (half_pos he)
  have h2 : |((sh (hratCast x) : ℝ) : ℝ*) - ((q : ℝ) : ℝ*)| < ((e / 2 : ℝ) : ℝ*) := by
    rw [← Hyperreal.coe_sub, ← Hyperreal.coe_abs, Hyperreal.coe_lt_coe, abs_lt]
    constructor <;> linarith
  calc |hratCast x - ((q : ℝ) : ℝ*)|
      = |(hratCast x - (sh (hratCast x) : ℝ*)) + ((sh (hratCast x) : ℝ*) - ((q : ℝ) : ℝ*))| := by
        rw [sub_add_sub_cancel]
    _ ≤ |hratCast x - (sh (hratCast x) : ℝ*)| + |(sh (hratCast x) : ℝ*) - ((q : ℝ) : ℝ*)| :=
        abs_add_le _ _
    _ < ((e / 2 : ℝ) : ℝ*) + ((e / 2 : ℝ) : ℝ*) := add_lt_add h1 h2
    _ = (e : ℝ*) := by rw [← Hyperreal.coe_add, add_halves]

/-- **Section 18.3.** The nonstandard hull of $`\mathbb Q` equals its completion: every
point of the hull is approachable. -/
theorem Hull.isApproachable_rat (h : Hull ℚ) : h.IsApproachable := by
  obtain ⟨x, hx, rfl⟩ := h.exists_rep
  exact approachable_of_limitedPt_rat hx

/-- A hyperrational is near to $`\mathbb Q` exactly when its shadow is rational. -/
theorem near_rat_iff {x : Star ℚ} : Near x ↔ ∃ q : ℚ, Infinitesimal (hratCast x - ((q : ℝ) : ℝ*)) := by
  refine exists_congr fun q => ?_
  show Infinitesimal (hdist x (Germ.const q)) ↔ _
  rw [hdist_rat, hratCast_const]
  exact ⟨fun h => h.of_abs_le (by rw [abs_abs]), fun h => h.of_abs_le (by rw [abs_abs])⟩

/-- **Section 18.3, example.** There is a hyperrational that is approachable from
$`\mathbb Q` but not near to $`\mathbb Q`: any hyperrational infinitely close to
$`\sqrt 2`. It is near to $`\mathbb R`, so nearness depends on the set it refers to. -/
theorem exists_approachable_not_near_rat :
    ∃ x : Star ℚ, Approachable x ∧ ¬Near x ∧
      Infinitesimal (hratCast x - ((Real.sqrt 2 : ℝ) : ℝ*)) := by
  obtain ⟨x, -, hx⟩ := exists_hrat_infinitesimal_sub (Real.sqrt 2)
  have hlim : Limited (hratCast x) := limited_of_infinitesimal_sub hx (limited_coe _)
  refine ⟨x, approachable_of_limitedPt_rat (limitedPt_rat_iff.2 hlim), ?_, hx⟩
  intro hnear
  obtain ⟨q, hq⟩ := near_rat_iff.1 hnear
  have h1 := sh_eq_of_infinitesimal_sub hq
  have h2 := sh_eq_of_infinitesimal_sub hx
  exact irrational_sqrt_two.ne_rat q (h2.symm.trans h1)

/-- **Section 18.3.** The shadow map on the nonstandard hull of the rationals. -/
def Hull.shRat (h : Hull ℚ) : ℝ :=
  Quotient.liftOn h (fun x => sh (hratCast x.1)) fun x y hxy => by
    have hxy' : Infinitesimal (hdist x.1 y.1) := hxy
    rw [hdist_rat] at hxy'
    exact (sh_eq_sh_iff (limitedPt_rat_iff.1 x.2) (limitedPt_rat_iff.1 y.2)).2
      (hxy'.of_abs_le (by rw [abs_abs]))

@[simp]
theorem Hull.shRat_mk (x : Star ℚ) (hx : LimitedPt x) :
    Hull.shRat (Hull.mk x hx) = sh (hratCast x) := rfl

theorem Hull.isometry_shRat : Isometry Hull.shRat :=
  Isometry.of_dist_eq fun h k => by
    obtain ⟨x, hx, rfl⟩ := h.exists_rep
    obtain ⟨y, hy, rfl⟩ := k.exists_rep
    rw [Hull.shRat_mk, Hull.shRat_mk, Hull.dist_mk, hdist_rat, Real.dist_eq, sh_abs,
      sh_sub (limitedPt_rat_iff.1 hx) (limitedPt_rat_iff.1 hy)]

theorem Hull.surjective_shRat : Function.Surjective Hull.shRat := fun r => by
  obtain ⟨q, -, hq⟩ := exists_hrat_infinitesimal_sub r
  exact ⟨Hull.mk q (limitedPt_rat_iff.2 (limited_of_infinitesimal_sub hq (limited_coe r))),
    sh_eq_of_infinitesimal_sub hq⟩

/-- **Section 18.3.** The nonstandard hull of $`(\mathbb Q, |\cdot|)` is isometric to
$`\mathbb R` by the shadow map $`\operatorname{hal}(x) \mapsto \operatorname{sh}(x)`. This is
the metric form of the isomorphism of Section 18.1. -/
def hullRatEquivReal : Hull ℚ ≃ᵢ ℝ where
  toEquiv := Equiv.ofBijective Hull.shRat ⟨Hull.isometry_shRat.injective, Hull.surjective_shRat⟩
  isometry_toFun := Hull.isometry_shRat

@[simp]
theorem hullRatEquivReal_of (q : ℚ) : hullRatEquivReal (Hull.of q) = (q : ℝ) :=
  sh_coe (q : ℝ)

end Rationals

end Goldblatt.Completion
