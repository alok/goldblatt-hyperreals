import Goldblatt.Ch07_Continuity.Limits

/-!
# 7 (part 2). Theorems on Intervals, Uniform Continuity, Contractions, Permanence: Sections 7.5 to 7.11

This is the second of three parts of Chapter 7 (the overview is on the chapter page
{lit}`Goldblatt.Ch07_Continuity`). It contains the two classical theorems about continuous
functions on a closed bounded interval, proved by partitioning the interval into unlimitedly
many equal parts; the hyperreal characterisation of uniform continuity and the theorem that a
continuous function on a closed bounded interval is uniformly continuous; the fixed point
theorem for contraction mappings; and the first permanence principle, with the exercises of
Sections 7.8 and 7.11.
-/

noncomputable section

namespace Goldblatt

open Set Filter Ultrapower
open scoped Hyperreal Topology

/-!
## 7.5 The Intermediate Value Theorem

Let $`f` be continuous on $`[a, b]` and let $`d` lie strictly between $`f(a)` and $`f(b)`.
The proof locates a point where $`f` takes the value $`d` by cutting $`[a, b]` into
subintervals of infinitesimal width. For a standard $`n \ge 1`, cut the interval into $`n`
equal parts with end points $`p_k = a + k(b - a)/n`, and (in the case $`f(a) < d < f(b)`) let
$`s_n` be the greatest partition point whose value is below $`d`. Then

$$`a \le s_n < b \quad\text{and}\quad f(s_n) < d \le f(s_n + (b - a)/n).`

By transfer the same holds for an unlimited hypernatural $`N`. The point $`s_N` is limited, so
it has a shadow $`c` in $`[a, b]`; both $`s_N` and $`s_N + (b - a)/N` are infinitely close to
$`c`, so by continuity both values are infinitely close to $`f(c)`. As $`d` lies between
them, $`d \simeq f(c)`, and two real numbers that are infinitely close are equal.

In the ultrapower an unlimited $`N` is the class of a sequence of natural numbers $`k_n` that
tends to infinity along the index ultrafilter, $`s_N` is the class of $`n \mapsto s_{k_n}`,
and "by transfer" means that the displayed facts hold at almost all indices.
-/

section Partition

variable {f : ℝ → ℝ} {a b d : ℝ} {x : ℝ*}

/-- **Section 7.5.** The partition point $`p_k = a + k(b - a)/n` of the division of $`[a, b]`
into $`n` equal parts. -/
def partitionPoint (a b : ℝ) (n k : ℕ) : ℝ := a + k * ((b - a) / n)

/-- **Section 7.5.** The first partition point is $`a`. -/
theorem partitionPoint_zero (a b : ℝ) (n : ℕ) : partitionPoint a b n 0 = a := by
  simp [partitionPoint]

/-- **Section 7.5.** The last partition point is $`b`. -/
theorem partitionPoint_self (a b : ℝ) {n : ℕ} (hn : n ≠ 0) : partitionPoint a b n n = b := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [partitionPoint]
  field_simp
  ring

/-- **Section 7.5.** Consecutive partition points differ by the width $`(b - a)/n`. -/
theorem partitionPoint_succ (a b : ℝ) (n k : ℕ) :
    partitionPoint a b n (k + 1) = partitionPoint a b n k + (b - a) / n := by
  simp only [partitionPoint]
  push_cast
  ring

/-- **Section 7.5.** The partition points with index at most $`n` lie in $`[a, b]`. -/
theorem partitionPoint_mem_Icc (hab : a ≤ b) {n k : ℕ} (hk : k ≤ n) :
    partitionPoint a b n k ∈ Icc a b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [partitionPoint, hab]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hw : 0 ≤ (b - a) / n := div_nonneg (by linarith) hn'.le
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    have h1 : (k : ℝ) * ((b - a) / n) ≤ n * ((b - a) / n) := mul_le_mul_of_nonneg_right hk' hw
    have h2 : (n : ℝ) * ((b - a) / n) = b - a := by field_simp
    constructor
    · simp only [partitionPoint]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hw]
    · simp only [partitionPoint]
      linarith

/-- **Section 7.5, the finite approximation.** If $`f(a) < d \le f(b)` and $`n \ge 1`, then
the greatest partition point $`p_k` of the $`n`-fold division with $`f(p_k) < d` has
$`k < n`, and the next partition point has $`d \le f(p_{k+1})`. -/
theorem exists_partitionPoint_crossing (ha : f a < d) (hb : d ≤ f b) {n : ℕ} (hn : n ≠ 0) :
    ∃ k < n, f (partitionPoint a b n k) < d ∧ d ≤ f (partitionPoint a b n (k + 1)) := by
  classical
  let T := (Finset.range (n + 1)).filter fun k => f (partitionPoint a b n k) < d
  have hT : T.Nonempty := ⟨0, by simp [T, partitionPoint_zero, ha]⟩
  obtain ⟨hKn, hKd⟩ := Finset.mem_filter.1 (T.max'_mem hT)
  have hKn' : T.max' hT ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hKn)
  have hne : T.max' hT ≠ n := by
    intro h
    rw [h, partitionPoint_self a b hn] at hKd
    exact not_le.2 hKd hb
  have hlt : T.max' hT < n := lt_of_le_of_ne hKn' hne
  refine ⟨T.max' hT, hlt, hKd, ?_⟩
  by_contra hcon
  push Not at hcon
  have hmem : T.max' hT + 1 ∈ T :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hcon⟩
  have := T.le_max' _ hmem
  omega

/-- **Section 7.5, tool.** A hyperreal between two reals is limited. -/
theorem limited_of_mem_Icc (h : x ∈ Icc (a : ℝ*) b) : Limited x := by
  refine ⟨a - 1, b + 1, lt_of_lt_of_le ?_ h.1, lt_of_le_of_lt h.2 ?_⟩
  · exact Hyperreal.coe_lt_coe.2 (by linarith)
  · exact Hyperreal.coe_lt_coe.2 (by linarith)

/-- **Section 7.5, tool.** The shadow of a hyperreal between the reals $`a` and $`b` lies in
$`[a, b]`. This is the
property of closed bounded intervals on which the theorems of this part rest. -/
theorem sh_mem_Icc (h : x ∈ Icc (a : ℝ*) b) : sh x ∈ Icc a b :=
  ⟨(limited_of_mem_Icc h).le_sh h.1, (limited_of_mem_Icc h).sh_le h.2⟩

/-- **Section 7.5, tool.** A member of the enlargement of $`[a, b]` is infinitely close to its
shadow, which lies in $`[a, b]`. -/
theorem infClose_sh_of_mem_starSet_Icc (h : x ∈ ⋆(Icc a b)) : x ≊ sh x ∧ sh x ∈ Icc a b := by
  rw [starSet_Icc_real] at h
  exact ⟨(limited_of_mem_Icc h).infClose_sh, sh_mem_Icc h⟩

/-- **Section 7.5, tool.** The width $`(b - a)/N` of the division of $`[a, b]` into an
unlimited number $`N` of parts is infinitesimal. -/
theorem infinitesimal_width {N : ℝ*} (hN : N ∈ unlimitedHyperNat) (a b : ℝ) :
    Infinitesimal (((b - a : ℝ) : ℝ*) / N) :=
  (limited_coe _).div_unlimited (mem_unlimitedHyperNat.1 hN).2

/-- **Section 7.5 (Intermediate Value Theorem), increasing case.** If $`f` is continuous on
$`[a, b]` and $`f(a) < d < f(b)`, then $`f(c) = d` for some $`c \in (a, b)`. The proof is the
book's: $`c` is the shadow of the last point, in a partition of $`[a, b]` into unlimitedly
many equal parts, at which $`f` is still below $`d`. -/
theorem intermediate_value_Icc_of_lt (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (ha : f a < d) (hb : d < f b) : ∃ c ∈ Ioo a b, f c = d := by
  -- the finite approximations
  have hex : ∀ n : ℕ, ∃ k : ℕ, n ≠ 0 →
      k < n ∧ f (partitionPoint a b n k) < d ∧ d ≤ f (partitionPoint a b n (k + 1)) :=
    fun n => by
      by_cases hn : n = 0
      · exact ⟨0, fun h => absurd hn h⟩
      · obtain ⟨k, hk⟩ := exists_partitionPoint_crossing ha hb.le hn
        exact ⟨k, fun _ => hk⟩
  choose K hK using hex
  -- an unlimited hypernatural N, as the class of a sequence k
  obtain ⟨k, hk, hNk⟩ := exists_hnat_of_mem_unlimitedHyperNat omega_mem_unlimitedHyperNat
  have hk0 : ∀ᶠ n in hyperfilter ℕ, k n ≠ 0 :=
    (hk.eventually_ge_atTop 1).mono fun n hn => by omega
  -- the point s_N and the width (b - a) / N
  let s : ℕ → ℝ := fun n => partitionPoint a b (k n) (K (k n))
  let w : ℕ → ℝ := fun n => (b - a) / k n
  have hw : Infinitesimal (Hyperreal.ofSeq w) := by
    have := infinitesimal_width (hnat_mem_unlimitedHyperNat_iff.2 hk) a b
    exact this
  have hsw : Hyperreal.ofSeq s + Hyperreal.ofSeq w = Hyperreal.ofSeq fun n => s n + w n := rfl
  -- transfer of the properties of the finite approximations
  have h1 : Hyperreal.ofSeq s ∈ ⋆(Icc a b) :=
    hyperreal_ofSeq_mem_starSet.2 (hk0.mono fun n hn =>
      partitionPoint_mem_Icc hab (hK _ hn).1.le)
  have h2 : Hyperreal.ofSeq s + Hyperreal.ofSeq w ∈ ⋆(Icc a b) := by
    rw [hsw]
    refine hyperreal_ofSeq_mem_starSet.2 (hk0.mono fun n hn => ?_)
    have := partitionPoint_mem_Icc hab (Nat.succ_le_of_lt (hK _ hn).1)
    rwa [partitionPoint_succ] at this
  have h3 : ⋆f (Hyperreal.ofSeq s) < d := by
    rw [starMap_hyperreal_ofSeq, coe_eq_ofSeq_const, ofSeq_lt_ofSeq_iff]
    exact hk0.mono fun n hn => (hK _ hn).2.1
  have h4 : (d : ℝ*) ≤ ⋆f (Hyperreal.ofSeq s + Hyperreal.ofSeq w) := by
    rw [hsw, starMap_hyperreal_ofSeq, coe_eq_ofSeq_const, ofSeq_le_ofSeq_iff]
    refine hk0.mono fun n hn => ?_
    have := (hK _ hn).2.2
    rwa [partitionPoint_succ] at this
  -- the shadow c of s_N
  obtain ⟨hsc, hc⟩ := infClose_sh_of_mem_starSet_Icc h1
  have hsc' : Hyperreal.ofSeq s + Hyperreal.ofSeq w ≊ sh (Hyperreal.ofSeq s) :=
    (hw.add_infClose _).trans hsc
  have e1 := (hf _ hc).starMap_infClose h1 hsc
  have e2 := (hf _ hc).starMap_infClose h2 hsc'
  have hd : (d : ℝ*) ≊ (f (sh (Hyperreal.ofSeq s)) : ℝ) :=
    infClose_of_le_of_le h3.le h4 e1 e2
  have hfc : f (sh (Hyperreal.ofSeq s)) = d := (infClose_coe_iff.1 hd).symm
  refine ⟨sh (Hyperreal.ofSeq s), ⟨lt_of_le_of_ne hc.1 ?_, lt_of_le_of_ne hc.2 ?_⟩, hfc⟩
  · intro h
    rw [← h] at hfc
    linarith
  · intro h
    rw [h] at hfc
    linarith

/-- **Section 7.5 (Intermediate Value Theorem).** Let $`f` be continuous on $`[a, b]` and let
$`d` lie strictly between the end values $`f(a)` and $`f(b)`. Then $`d` is attained:
$`f(c) = d` for some $`c` with $`a < c < b`. The case $`f(b) < d < f(a)` is
reduced to the increasing case by passing to $`-f`. -/
theorem intermediate_value_Icc (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : (f a < d ∧ d < f b) ∨ (f b < d ∧ d < f a)) : ∃ c ∈ Ioo a b, f c = d := by
  rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact intermediate_value_Icc_of_lt hab hf h1 h2
  · obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc_of_lt (f := fun t => -f t) (d := -d) hab
      hf.neg (by linarith) (by linarith)
    exact ⟨c, hc, by linarith⟩

end Partition

/-!
## 7.6 The Extreme Value Theorem

A continuous function on $`[a, b]` attains a greatest and a least value. Again the interval
is cut into $`N` equal parts with $`N` unlimited. For a standard $`n` the finite set of
partition points has a point $`s_n` where $`f` is greatest among them; by transfer, $`f(s_N)`
dominates the value of $`f` at every point $`a + k(b - a)/N` of the infinitesimal partition.
Let $`d` be the shadow of $`s_N`. The infinitesimal partition comes infinitely close to every
real $`x \in [a, b]`: for a standard $`n` there is a partition point within $`(b - a)/n`
below $`x`, so by transfer there is a point $`y` of the infinitesimal partition with
$`y \simeq x`. Continuity at $`x` and at $`d` gives

$$`f(x) \simeq {}^*f(y) \le {}^*f(s_N) \simeq f(d),`

and therefore $`f(x) \le f(d)`, both numbers being real.
-/

section ExtremeValue

variable {f : ℝ → ℝ} {a b : ℝ}

/-- **Section 7.6, the finite approximation.** Among the partition points
$`a + k(b - a)/n` with $`0 \le k \le n` there is one where $`f` is greatest. -/
theorem exists_partitionPoint_max (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    ∃ k ≤ n, ∀ j ≤ n, f (partitionPoint a b n j) ≤ f (partitionPoint a b n k) := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun k => f (partitionPoint a b n k)) ⟨0, by simp⟩
  exact ⟨k, Nat.lt_succ_iff.1 (Finset.mem_range.1 hk), fun j hj =>
    hmax j (Finset.mem_range.2 (Nat.lt_succ_iff.2 hj))⟩

/-- **Section 7.6, the finite approximation.** For $`n \ge 1`, every real $`t \in [a, b]`
has a partition point of the $`n`-fold division within $`(b - a)/n` below it. -/
theorem exists_partitionPoint_near (hab : a < b) {t : ℝ} (ht : t ∈ Icc a b) {n : ℕ}
    (hn : n ≠ 0) :
    ∃ j ≤ n, partitionPoint a b n j ≤ t ∧ t ≤ partitionPoint a b n j + (b - a) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hw : 0 < (b - a) / n := div_pos (by linarith) hn'
  have h0 : 0 ≤ (t - a) / ((b - a) / n) := div_nonneg (by linarith [ht.1]) hw.le
  refine ⟨⌊(t - a) / ((b - a) / n)⌋₊, ?_, ?_, ?_⟩
  · refine Nat.floor_le_of_le ?_
    rw [div_le_iff₀ hw]
    have : (n : ℝ) * ((b - a) / n) = b - a := by field_simp
    linarith [ht.2]
  · have := (le_div_iff₀ hw).1 (Nat.floor_le h0)
    simp only [partitionPoint]
    linarith
  · have := (div_lt_iff₀ hw).1 (Nat.lt_floor_add_one ((t - a) / ((b - a) / n)))
    simp only [partitionPoint]
    linarith

/-- **Section 7.6 (Extreme Value Theorem), maximum.** If $`f` is continuous on $`[a, b]`,
there is $`d \in [a, b]` with $`f(x) \le f(d)` for all $`x \in [a, b]`. The proof is the
book's: $`d` is the shadow of a point of an infinitesimal partition at which $`f` dominates
its values on the whole partition. -/
theorem exists_forall_le_Icc (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    ∃ d ∈ Icc a b, ∀ t ∈ Icc a b, f t ≤ f d := by
  rcases hab.eq_or_lt with rfl | hlt
  · exact ⟨a, ⟨le_rfl, le_rfl⟩, fun t ht => by rw [le_antisymm ht.2 ht.1]⟩
  -- the finite approximations
  choose K hKn hK using exists_partitionPoint_max f a b
  -- an unlimited hypernatural N, as the class of a sequence k
  obtain ⟨k, hk, -⟩ := exists_hnat_of_mem_unlimitedHyperNat omega_mem_unlimitedHyperNat
  have hk0 : ∀ᶠ n in hyperfilter ℕ, k n ≠ 0 :=
    (hk.eventually_ge_atTop 1).mono fun n hn => by omega
  let s : ℕ → ℝ := fun n => partitionPoint a b (k n) (K (k n))
  let w : ℕ → ℝ := fun n => (b - a) / k n
  have hw : Infinitesimal (Hyperreal.ofSeq w) := by
    have := infinitesimal_width (hnat_mem_unlimitedHyperNat_iff.2 hk) a b
    exact this
  have h1 : Hyperreal.ofSeq s ∈ ⋆(Icc a b) :=
    hyperreal_ofSeq_mem_starSet.2 (Eventually.of_forall fun n =>
      partitionPoint_mem_Icc hab (hKn _))
  obtain ⟨hsd, hd⟩ := infClose_sh_of_mem_starSet_Icc h1
  have e1 := (hf _ hd).starMap_infClose h1 hsd
  refine ⟨sh (Hyperreal.ofSeq s), hd, fun t ht => ?_⟩
  -- a point of the infinitesimal partition infinitely close to t
  have hex : ∀ n : ℕ, ∃ j : ℕ, n ≠ 0 → j ≤ n ∧ partitionPoint a b n j ≤ t ∧
      t ≤ partitionPoint a b n j + (b - a) / n := fun n => by
    by_cases hn : n = 0
    · exact ⟨0, fun h => absurd hn h⟩
    · obtain ⟨j, hj⟩ := exists_partitionPoint_near hlt ht hn
      exact ⟨j, fun _ => hj⟩
  choose J hJ using hex
  let y : ℕ → ℝ := fun n => partitionPoint a b (k n) (J (k n))
  have hy1 : Hyperreal.ofSeq y ∈ ⋆(Icc a b) :=
    hyperreal_ofSeq_mem_starSet.2 (hk0.mono fun n hn =>
      partitionPoint_mem_Icc hab (hJ _ hn).1)
  have hy2 : Hyperreal.ofSeq y ≤ t := by
    rw [coe_eq_ofSeq_const, ofSeq_le_ofSeq_iff]
    exact hk0.mono fun n hn => (hJ _ hn).2.1
  have hy3 : (t : ℝ*) - Hyperreal.ofSeq w ≤ Hyperreal.ofSeq y := by
    have e : (t : ℝ*) - Hyperreal.ofSeq w = Hyperreal.ofSeq fun n => t - w n := rfl
    rw [e, ofSeq_le_ofSeq_iff]
    refine hk0.mono fun n hn => ?_
    have := (hJ _ hn).2.2
    simp only [w, y]
    linarith
  have hyt : Hyperreal.ofSeq y ≊ t := by
    refine infClose_of_le_of_le hy3 hy2 ?_ (InfClose.refl _)
    simpa [sub_eq_add_neg] using hw.neg.add_infClose (t : ℝ*)
  have e2 := (hf _ ht).starMap_infClose hy1 hyt
  -- the value at s_N dominates the values on the partition
  have h3 : ⋆f (Hyperreal.ofSeq y) ≤ ⋆f (Hyperreal.ofSeq s) := by
    rw [starMap_hyperreal_ofSeq, starMap_hyperreal_ofSeq, ofSeq_le_ofSeq_iff]
    exact hk0.mono fun n hn => hK _ _ (hJ _ hn).1
  exact coe_le_coe_of_infClose_le_infClose e2.symm h3 e1

/-- **Section 7.6 (Extreme Value Theorem), minimum.** If $`f` is continuous on $`[a, b]`,
there is $`c \in [a, b]` with $`f(c) \le f(x)` for all $`x \in [a, b]`; apply the maximum
statement to $`-f`. -/
theorem exists_forall_ge_Icc (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    ∃ c ∈ Icc a b, ∀ t ∈ Icc a b, f c ≤ f t := by
  obtain ⟨c, hc, h⟩ := exists_forall_le_Icc (f := fun t => -f t) hab hf.neg
  exact ⟨c, hc, fun t ht => by linarith [h t ht]⟩

/-- **Section 7.6 (Extreme Value Theorem).** A function continuous on $`[a, b]` has a least
and a greatest value there, and both are attained: the interval contains points $`c` and
$`d` such that every value $`f(x)` with $`a \le x \le b` lies between $`f(c)` and
$`f(d)`. -/
theorem extreme_value_Icc (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    ∃ c ∈ Icc a b, ∃ d ∈ Icc a b, ∀ t ∈ Icc a b, f c ≤ f t ∧ f t ≤ f d := by
  obtain ⟨c, hc, h1⟩ := exists_forall_ge_Icc hab hf
  obtain ⟨d, hd, h2⟩ := exists_forall_le_Icc hab hf
  exact ⟨c, hc, d, hd, fun t ht => ⟨h1 t ht, h2 t ht⟩⟩

end ExtremeValue

/-!
## 7.7 Uniform Continuity

A function is uniformly continuous on $`A` when, for a given tolerance, one $`\delta` serves
at all points of $`A` at once. Theorem 7.7.1 says that this holds exactly when the extension
preserves infinite closeness at _all_ pairs of points of the enlargement of $`A`. Compare
Theorem 7.1.3: ordinary continuity on $`A` is the same condition with one of the two points
required to be real. The difference between the two notions is thus the difference between
the real points and all points of the enlargement.

On a closed bounded interval there is no difference (Theorem 7.7.2), because every point of
the enlargement of $`[a, b]` is infinitely close to a real point of $`[a, b]`, its shadow.
The standard side is Mathlib's {name}`UniformContinuousOn`, which unfolds to the book's
sentence by {name}`Metric.uniformContinuousOn_iff`.
-/

section UniformContinuity

variable {f : ℝ → ℝ} {A : Set ℝ} {a b : ℝ} {x y : ℝ*}

/-- **Theorem 7.7.1.** A real function $`f` is uniformly continuous on $`A` if and only if
$`x \simeq y` implies $`{}^*f(x) \simeq {}^*f(y)` for all hyperreals $`x, y \in {}^*A`.

The book leaves the proof as an exercise. If $`f` is uniformly continuous, then for each
real $`\varepsilon` the sentence "all $`s, t \in A` within $`\delta` of each other have
values within $`\varepsilon`" transfers to the enlargement, and infinitely close points are
within $`\delta`. Conversely, if uniform continuity fails for some $`\varepsilon`, choose
for each $`n` points $`s_n, t_n \in A` within $`1/(n+1)` whose values differ by at least
$`\varepsilon`; their classes are infinitely close points of the enlargement with values not
infinitely close. -/
theorem uniformContinuousOn_iff_infClose :
    UniformContinuousOn f A ↔ ∀ x ∈ ⋆A, ∀ y ∈ ⋆A, x ≊ y → ⋆f x ≊ ⋆f y := by
  rw [Metric.uniformContinuousOn_iff]
  constructor
  · intro h x hx y hy hxy
    obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
    obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
    rw [starMap_hyperreal_ofSeq, starMap_hyperreal_ofSeq, ofSeq_infClose_ofSeq_iff]
    intro η hη
    obtain ⟨δ, hδ, hδ'⟩ := h η hη
    filter_upwards [ofSeq_infClose_ofSeq_iff.1 hxy δ hδ, hyperreal_ofSeq_mem_starSet.1 hx,
      hyperreal_ofSeq_mem_starSet.1 hy] with n h1 h2 h3
    have := hδ' _ h2 _ h3 (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨η, hη, hne⟩ := hne
    have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
    choose r hr s hs hd hfd using fun n : ℕ => hne (1 / ((n : ℝ) + 1)) (hpos n)
    have hxy : Hyperreal.ofSeq r ≊ Hyperreal.ofSeq s := by
      rw [ofSeq_infClose_ofSeq_iff]
      intro δ hδ
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      refine eventually_hyperfilter_of_forall_ge m fun n hn => ?_
      have h1 := hd n
      rw [Real.dist_eq] at h1
      have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (m : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      linarith
    have := h _ (hyperreal_ofSeq_mem_starSet.2 (Eventually.of_forall hr)) _
      (hyperreal_ofSeq_mem_starSet.2 (Eventually.of_forall hs)) hxy
    rw [starMap_hyperreal_ofSeq, starMap_hyperreal_ofSeq, ofSeq_infClose_ofSeq_iff] at this
    obtain ⟨n, hn⟩ := (this η hη).exists
    have := hfd n
    rw [Real.dist_eq] at this
    linarith

/-- **Theorem 7.7.1**, for a function on the whole line: $`f` is uniformly continuous if and
only if its extension preserves infinite closeness everywhere. -/
theorem uniformContinuous_iff_infClose :
    UniformContinuous f ↔ ∀ x y : ℝ*, x ≊ y → ⋆f x ≊ ⋆f y := by
  rw [← uniformContinuousOn_univ, uniformContinuousOn_iff_infClose, starSet_univ]
  simp

/-- **Theorem 7.7.1**, forward direction as a rule. -/
theorem _root_.UniformContinuousOn.starMap_infClose (h : UniformContinuousOn f A)
    (hx : x ∈ ⋆A) (hy : y ∈ ⋆A) (hxy : x ≊ y) : ⋆f x ≊ ⋆f y :=
  uniformContinuousOn_iff_infClose.1 h x hx y hy hxy

/-- **Theorem 7.7.2.** On a closed bounded interval $`[a, b]`, continuity is automatically
uniform. Given $`x \simeq y` in the
enlargement of $`[a, b]`, let $`c` be the shadow of $`x`. Then $`c \in [a, b]`, so $`f` is
continuous at $`c`, and both $`{}^*f(x)` and $`{}^*f(y)` are infinitely close to
$`f(c)`. -/
theorem uniformContinuousOn_Icc_of_continuousOn (hf : ContinuousOn f (Icc a b)) :
    UniformContinuousOn f (Icc a b) := by
  rw [uniformContinuousOn_iff_infClose]
  intro x hx y hy hxy
  obtain ⟨hxc, hc⟩ := infClose_sh_of_mem_starSet_Icc hx
  have e1 := (hf _ hc).starMap_infClose hx hxc
  have e2 := (hf _ hc).starMap_infClose hy (hxy.symm.trans hxc)
  exact e1.trans e2.symm

end UniformContinuity

/-!
## 7.8 Exercises on Uniform Continuity

(1) The proof of Theorem 7.7.2 uses that the shadow of a member of the enlargement of
$`[a, b]` exists and lies in $`[a, b]`. For an interval that is not closed the shadow may
fall outside it, as for $`a + \varepsilon` in the enlargement of $`(a, b)` or of $`(a, b]`,
and for $`b - \varepsilon` in the enlargement of $`[a, b)`; for an unbounded interval the
member may be unlimited and have no shadow at all, as for $`\omega` in the enlargement of
$`(a, +\infty)` and $`-\omega` in that of $`(-\infty, b)`. Each of the four kinds of
interval listed in the exercise has its witness below.

(2) The function $`1/x` is continuous but not uniformly continuous on $`(0, 1)`: the points
$`\varepsilon` and $`\varepsilon/2` are infinitely close, but their reciprocals $`\omega` and
$`2\omega` are not.

(3) A uniformly continuous function maps Cauchy sequences to Cauchy sequences, because the
extended terms of the image sequence are the images of the extended terms.

(4) A monotonic function on $`[a, b]` that takes every value between $`f(a)` and $`f(b)` is
continuous: if $`{}^*f(x)` were at appreciable distance from $`f(c)` for some $`x \simeq c`,
an intermediate value would be taken at a real point strictly between $`c` and $`x`, which
is impossible.
-/

section UniformExercises

variable {f : ℝ → ℝ} {A : Set ℝ} {a b : ℝ} {x y : ℝ*}

/-- **Exercise 7.8(1), open intervals.** For $`a < b` the enlargement of $`(a, b)` has a
member, namely $`a + \varepsilon`, whose shadow $`a` is not in $`(a, b)`. So the argument of
Theorem 7.7.2 cannot find a real point of the interval at which to use continuity. -/
theorem exists_mem_starSet_Ioo_sh_notMem (hab : a < b) :
    ∃ x ∈ ⋆(Ioo a b), sh x ∉ Ioo a b := by
  have h1 : (a : ℝ*) + ε ≊ a := infinitesimal_epsilon.add_infClose _
  refine ⟨a + ε, ?_, ?_⟩
  · rw [starSet_Ioo_real]
    refine ⟨lt_add_of_pos_right _ Hyperreal.epsilon_pos, ?_⟩
    have := epsilon_pos_infinitesimal.2 (b - a) (by linarith)
    rw [Hyperreal.coe_sub] at this
    linarith
  · rw [sh_eq_of_infClose h1]
    exact fun h => lt_irrefl _ h.1

/-- **Exercise 7.8(1), unbounded intervals.** The enlargement of $`(a, +\infty)` has a member,
namely $`\omega`, that is not limited and so is infinitely close to no real number. -/
theorem exists_mem_starSet_Ioi_not_limited (a : ℝ) : ∃ x ∈ ⋆(Ioi a), ¬ Limited x := by
  refine ⟨ω, ?_, unlimited_omega.not_limited⟩
  rw [starSet_Ioi_real]
  exact posUnlimited_omega a

/-- **Exercise 7.8(1), intervals open on the left.** For $`a < b` the enlargement of
$`(a, b]` contains $`a + \varepsilon`, whose shadow $`a` is not in $`(a, b]`. -/
theorem exists_mem_starSet_Ioc_sh_notMem (hab : a < b) :
    ∃ x ∈ ⋆(Ioc a b), sh x ∉ Ioc a b := by
  have h1 : (a : ℝ*) + ε ≊ a := infinitesimal_epsilon.add_infClose _
  refine ⟨a + ε, ?_, ?_⟩
  · rw [starSet_Ioc_real]
    refine ⟨lt_add_of_pos_right _ Hyperreal.epsilon_pos, ?_⟩
    have := epsilon_pos_infinitesimal.2 (b - a) (by linarith)
    rw [Hyperreal.coe_sub] at this
    linarith
  · rw [sh_eq_of_infClose h1]
    exact fun h => lt_irrefl _ h.1

/-- **Exercise 7.8(1), intervals open on the right.** For $`a < b` the enlargement of
$`[a, b)` contains $`b - \varepsilon`, whose shadow $`b` is not in $`[a, b)`. -/
theorem exists_mem_starSet_Ico_sh_notMem (hab : a < b) :
    ∃ x ∈ ⋆(Ico a b), sh x ∉ Ico a b := by
  have h1 : (b : ℝ*) - ε ≊ b := by
    have := infinitesimal_epsilon.neg.add_infClose (b : ℝ*)
    rwa [← sub_eq_add_neg] at this
  refine ⟨b - ε, ?_, ?_⟩
  · rw [starSet_Ico_real]
    refine ⟨?_, sub_lt_self _ Hyperreal.epsilon_pos⟩
    have := epsilon_pos_infinitesimal.2 (b - a) (by linarith)
    rw [Hyperreal.coe_sub] at this
    linarith
  · rw [sh_eq_of_infClose h1]
    exact fun h => lt_irrefl _ h.2

/-- **Exercise 7.8(1), intervals unbounded below.** The enlargement of $`(-\infty, b)` has a
member, namely $`-\omega`, that is not limited and so is infinitely close to no real
number. -/
theorem exists_mem_starSet_Iio_not_limited (b : ℝ) : ∃ x ∈ ⋆(Iio b), ¬ Limited x := by
  refine ⟨-ω, ?_, unlimited_omega.neg.not_limited⟩
  rw [starSet_Iio_real]
  have := posUnlimited_omega (-b)
  rw [Hyperreal.coe_neg] at this
  exact neg_lt.1 this

/-- **Exercise 7.8(2), tool.** The extension of the reciprocal function is the reciprocal. -/
theorem starMap_one_div_apply (x : ℝ*) : ⋆(fun t : ℝ => 1 / t) x = 1 / x := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rfl

/-- **Exercise 7.8(2).** The function $`1/x` is not uniformly continuous on $`(0, 1)`: the
infinitely close points $`\varepsilon` and $`\varepsilon/2` of the enlargement have
reciprocals that differ by the unlimited number $`1/\varepsilon`. -/
theorem not_uniformContinuousOn_one_div_Ioo :
    ¬ UniformContinuousOn (fun t : ℝ => 1 / t) (Ioo 0 1) := by
  intro h
  have hε : (0 : ℝ*) < ε := Hyperreal.epsilon_pos
  have hε1 : (ε : ℝ*) < 1 := by
    simpa using epsilon_pos_infinitesimal.2 1 one_pos
  have he2 : Infinitesimal ((ε : ℝ*) / 2) :=
    infinitesimal_epsilon.of_abs_le (by
      rw [abs_of_pos hε, abs_of_pos (by linarith)]
      linarith)
  have hx : (ε : ℝ*) ∈ ⋆(Ioo (0 : ℝ) 1) := by
    rw [starSet_Ioo_real]
    exact ⟨by simp [hε], by simpa using hε1⟩
  have hy : (ε : ℝ*) / 2 ∈ ⋆(Ioo (0 : ℝ) 1) := by
    rw [starSet_Ioo_real]
    refine ⟨by simp [hε], ?_⟩
    simp only [Hyperreal.coe_one]
    linarith
  have hxy : (ε : ℝ*) ≊ ε / 2 := by
    have : (ε : ℝ*) - ε / 2 = ε / 2 := by ring
    rw [infClose_iff, this]
    exact he2
  have := h.starMap_infClose hx hy hxy
  rw [starMap_one_div_apply, starMap_one_div_apply, infClose_iff] at this
  have e : (1 : ℝ*) / ε - 1 / (ε / 2) = -(ε : ℝ*)⁻¹ := by
    field_simp
    ring
  rw [e] at this
  exact (infinitesimal_epsilon.inv_unlimited hε.ne').neg.not_infinitesimal this

/-- **Exercise 7.8(2).** The function $`1/x` is continuous on $`(0, 1)`; so continuity on a
bounded open interval does not imply uniform continuity. This is the standard fact that the
reciprocal is continuous away from zero. -/
theorem continuousOn_one_div_Ioo : ContinuousOn (fun t : ℝ => 1 / t) (Ioo 0 1) :=
  continuousOn_const.div continuousOn_id fun _ ht => ht.1.ne'

/-- **Exercise 7.8(3), tool.** The extended terms of the sequence $`f(s_n)` are the values of
the extension of $`f` at the extended terms of $`s`. -/
theorem hyperSeq_comp (f : ℝ → ℝ) (s : ℕ → ℝ) {N : ℝ*} (hN : N ∈ ℕ*) :
    hyperSeq (fun n => f (s n)) N = ⋆f (hyperSeq s N) := by
  obtain ⟨k, rfl⟩ := exists_hnat_eq hN
  rw [hyperSeq_hnat, hyperSeq_hnat, starMap_hyperreal_ofSeq]

/-- **Exercise 7.8(3).** If $`f` is uniformly continuous on the real line and $`s` is a
Cauchy sequence, then $`f(s_n)` is a Cauchy sequence. By Theorem 6.5.1 the extended terms of
$`s` are infinitely close to one another, and by Theorem 7.7.1 so are their images. -/
theorem cauchySeq_comp_of_uniformContinuous (hf : UniformContinuous f) {s : ℕ → ℝ}
    (hs : CauchySeq s) : CauchySeq fun n => f (s n) := by
  rw [cauchySeq_iff_forall_unlimited_infClose] at *
  intro M hM N hN
  rw [hyperSeq_comp f s hM.1, hyperSeq_comp f s hN.1]
  exact uniformContinuous_iff_infClose.1 hf _ _ (hs M hM N hN)

/-- **Exercise 7.8(4), tool (transfer of monotonicity).** If $`f` is increasing on $`A`, its
extension is increasing on the enlargement of $`A`. -/
theorem _root_.MonotoneOn.starMap_le (hf : MonotoneOn f A) (hx : x ∈ ⋆A) (hy : y ∈ ⋆A)
    (h : x ≤ y) : ⋆f x ≤ ⋆f y := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
  rw [starMap_hyperreal_ofSeq, starMap_hyperreal_ofSeq, ofSeq_le_ofSeq_iff]
  filter_upwards [hyperreal_ofSeq_mem_starSet.1 hx, hyperreal_ofSeq_mem_starSet.1 hy,
    ofSeq_le_ofSeq_iff.1 h] with n h1 h2 h3
  exact hf h1 h2 h3

/-- **Exercise 7.8(4), increasing case.** Let $`f` be increasing on $`[a, b]` and suppose
every real $`r` between $`f(a)` and $`f(b)` is a value $`f(c)` with $`c \in [a, b]`. Then
$`f` is continuous on $`[a, b]`.

Let $`c \in [a, b]` and $`x \simeq c` in the enlargement of the interval, and suppose
$`{}^*f(x)` differs from $`f(c)` by at least a real $`\eta > 0`. If $`x \ge c` then
$`f(c) + \eta \le {}^*f(x) \le f(b)`, so the value $`f(c) + \eta/2` is taken at some real
$`c'`, which must be greater than $`c`. But then $`x < c'`, since $`x \simeq c`, and so
$`{}^*f(x) \le f(c') = f(c) + \eta/2`: a contradiction. The case $`x \le c` is
symmetric. -/
theorem continuousOn_Icc_of_monotoneOn_of_forall_exists (hf : MonotoneOn f (Icc a b))
    (hiv : ∀ r ∈ Icc (f a) (f b), ∃ c ∈ Icc a b, f c = r) : ContinuousOn f (Icc a b) := by
  intro c hc
  have hab : a ≤ b := hc.1.trans hc.2
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab
  rw [continuousWithinAt_iff_infClose]
  intro x hx hxc
  rw [infClose_iff_abs_lt]
  intro η hη
  by_contra hnot
  rw [not_lt] at hnot
  have hc' : (c : ℝ*) ∈ ⋆(Icc a b) := coe_mem_starSet.2 hc
  have hxa : ((f a : ℝ) : ℝ*) ≤ ⋆f x := by
    have := hf.starMap_le (coe_mem_starSet.2 ha) hx (by
      rw [starSet_Icc_real] at hx; exact hx.1)
    rwa [starMap_coe] at this
  have hxb : ⋆f x ≤ ((f b : ℝ) : ℝ*) := by
    have := hf.starMap_le hx (coe_mem_starSet.2 hb) (by
      rw [starSet_Icc_real] at hx; exact hx.2)
    rwa [starMap_coe] at this
  have hη2 : (0 : ℝ) < η / 2 := by linarith
  rcases le_total (c : ℝ*) x with hcx | hxc'
  · have h1 : ((f c : ℝ) : ℝ*) ≤ ⋆f x := by
      have := hf.starMap_le hc' hx hcx
      rwa [starMap_coe] at this
    rw [abs_of_nonneg (sub_nonneg.2 h1)] at hnot
    have h2 : ((f c + η : ℝ) : ℝ*) ≤ ((f b : ℝ) : ℝ*) := by
      rw [Hyperreal.coe_add]
      linarith
    have h2' : f c + η ≤ f b := Hyperreal.coe_le_coe.1 h2
    obtain ⟨c', hc'mem, hfc'⟩ := hiv (f c + η / 2) ⟨by linarith [hf ha hc hc.1], by linarith⟩
    have hcc' : c < c' := by
      by_contra hle
      have := hf hc'mem hc (not_lt.1 hle)
      linarith
    have hxc'' : x < (c' : ℝ*) := by
      have := (abs_lt.1 (infClose_iff_abs_lt.1 hxc (c' - c) (by linarith))).2
      rw [Hyperreal.coe_sub] at this
      linarith
    have h3 : ⋆f x ≤ ((f c' : ℝ) : ℝ*) := by
      have := hf.starMap_le hx (coe_mem_starSet.2 hc'mem) hxc''.le
      rwa [starMap_coe] at this
    rw [hfc', Hyperreal.coe_add] at h3
    have h4 : ((η / 2 : ℝ) : ℝ*) < (η : ℝ*) := Hyperreal.coe_lt_coe.2 (by linarith)
    linarith
  · have h1 : ⋆f x ≤ ((f c : ℝ) : ℝ*) := by
      have := hf.starMap_le hx hc' hxc'
      rwa [starMap_coe] at this
    rw [abs_of_nonpos (sub_nonpos.2 h1)] at hnot
    have h2 : ((f a : ℝ) : ℝ*) ≤ ((f c - η : ℝ) : ℝ*) := by
      rw [Hyperreal.coe_sub]
      linarith
    have h2' : f a ≤ f c - η := Hyperreal.coe_le_coe.1 h2
    obtain ⟨c', hc'mem, hfc'⟩ := hiv (f c - η / 2) ⟨by linarith, by linarith [hf hc hb hc.2]⟩
    have hcc' : c' < c := by
      by_contra hle
      have := hf hc hc'mem (not_lt.1 hle)
      linarith
    have hxc'' : (c' : ℝ*) < x := by
      have := (abs_lt.1 (infClose_iff_abs_lt.1 hxc (c - c') (by linarith))).1
      rw [Hyperreal.coe_sub] at this
      linarith
    have h3 : ((f c' : ℝ) : ℝ*) ≤ ⋆f x := by
      have := hf.starMap_le (coe_mem_starSet.2 hc'mem) hx hxc''.le
      rwa [starMap_coe] at this
    rw [hfc', Hyperreal.coe_sub] at h3
    have h4 : ((η / 2 : ℝ) : ℝ*) < (η : ℝ*) := Hyperreal.coe_lt_coe.2 (by linarith)
    linarith

/-- **Exercise 7.8(4).** A function that is monotone on $`[a, b]`, in either direction, and
whose values on $`[a, b]` fill the whole range from $`f(a)` to $`f(b)`, has no jumps: it is
continuous on $`[a, b]`. The range between the end values is the unordered interval
{name}`Set.uIcc`. The decreasing case
follows from the increasing case applied to $`-f`. -/
theorem continuousOn_Icc_of_monotone_or_antitone
    (hf : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b))
    (hiv : ∀ r ∈ uIcc (f a) (f b), ∃ c ∈ Icc a b, f c = r) : ContinuousOn f (Icc a b) := by
  by_cases hab : a ≤ b
  · have ha : a ∈ Icc a b := left_mem_Icc.2 hab
    have hb : b ∈ Icc a b := right_mem_Icc.2 hab
    rcases hf with hf | hf
    · rw [uIcc_of_le (hf ha hb hab)] at hiv
      exact continuousOn_Icc_of_monotoneOn_of_forall_exists hf hiv
    · rw [uIcc_of_ge (hf ha hb hab)] at hiv
      have hneg : ContinuousOn (fun t => -f t) (Icc a b) :=
        continuousOn_Icc_of_monotoneOn_of_forall_exists (f := fun t => -f t)
          (fun s hs t ht hst => neg_le_neg (hf hs ht hst)) fun r hr => by
            obtain ⟨c, hc, hfc⟩ := hiv (-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
            exact ⟨c, hc, by linarith⟩
      exact hneg.neg.congr fun t _ => (neg_neg (f t)).symm
  · rw [Icc_eq_empty hab]
    exact continuousOn_empty f

end UniformExercises

/-!
## 7.9 Contraction Mappings and Fixed Points

A function $`f` on the real line satisfies a _Lipschitz condition_ with constant $`c` if
$`|f(x) - f(y)| \le c\,|x - y|` for all $`x, y`. By transfer the inequality holds for all
hyperreals, and so $`x \simeq y` implies $`{}^*f(x) \simeq {}^*f(y)`: a Lipschitz function
is uniformly continuous by Theorem 7.7.1. A _contraction mapping_ is a Lipschitz function
with constant $`c < 1`. It has at most one fixed point, and Theorem 7.9.1 shows that it has
one.

The proof starts from any real $`x` and looks at the sequence of iterates
$`s_n = f^n(x)`. Standard estimates give $`|s_n - s_{n+1}| \le c^n |s_0 - s_1|` and
$`|s_0 - s_n| \le |s_0 - s_1| / (1 - c)`. Instead of proving that the sequence is Cauchy,
take an unlimited $`N`. By transfer of the second estimate $`s_N` is limited, so it has a
shadow $`L`. Then

$$`f(L) \simeq {}^*f(s_N) = s_{N+1} \simeq s_N \simeq L,`

by continuity, by transfer of the recursion, and by transfer of the first estimate (the power
$`c^N` is infinitesimal). So $`f(L) = L`. Since the fixed point is unique, all extended
terms have the same shadow, and by Theorem 6.1.1 the iterates converge to the fixed point:
the convergence is a consequence of the proof and not one of its steps.

The Lipschitz condition is stated here directly as the inequality, as in the book, with a
real constant $`c`. Mathlib's notions are {name}`LipschitzWith` and {name}`ContractingWith`,
whose constant is a nonnegative real; {lit}`lipschitzWith_iff_abs_sub_le` translates
between the two forms, and the results of the section are restated for Mathlib's notions as
{lit}`uniformContinuous_of_lipschitzWith`,
{lit}`existsUnique_fixedPoint_of_contractingWith` and
{lit}`tendsto_iterate_of_contractingWith`. The iterates are Mathlib's {lit}`f^[n] x`.
-/

section Contraction

variable {f : ℝ → ℝ} {c : ℝ}

/-- **Section 7.9, transfer of the Lipschitz condition.** If
$`|f(x) - f(y)| \le c\,|x - y|` for all reals, then the same inequality holds for the
extension at all hyperreals. -/
theorem abs_starMap_sub_le_of_lipschitz (h : ∀ x y, |f x - f y| ≤ c * |x - y|) (x y : ℝ*) :
    |⋆f x - ⋆f y| ≤ c * |x - y| := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  obtain ⟨s, rfl⟩ := hyperreal_exists_rep y
  have e1 : ⋆f (Hyperreal.ofSeq r) - ⋆f (Hyperreal.ofSeq s) =
      Hyperreal.ofSeq fun n => f (r n) - f (s n) := rfl
  have e2 : Hyperreal.ofSeq r - Hyperreal.ofSeq s = Hyperreal.ofSeq fun n => r n - s n := rfl
  have e3 : (c : ℝ*) * Hyperreal.ofSeq (fun n => |r n - s n|) =
      Hyperreal.ofSeq fun n => c * |r n - s n| := rfl
  rw [e1, e2, abs_ofSeq, abs_ofSeq, e3, ofSeq_le_ofSeq_iff]
  exact Eventually.of_forall fun n => h _ _

/-- **Section 7.9.** A function satisfying a Lipschitz condition is uniformly continuous: if
$`x \simeq y` then $`c\,|x - y|` is infinitesimal, hence so is
$`{}^*f(x) - {}^*f(y)`. -/
theorem uniformContinuous_of_lipschitz (h : ∀ x y, |f x - f y| ≤ c * |x - y|) :
    UniformContinuous f := by
  rw [uniformContinuous_iff_infClose]
  intro x y hxy
  have h1 : Infinitesimal |x - y| := Infinitesimal.of_abs_le hxy (abs_abs _).le
  have h2 : Infinitesimal ((c : ℝ*) * |x - y|) := (limited_coe c).mul_infinitesimal h1
  exact h2.of_abs_le ((abs_starMap_sub_le_of_lipschitz h x y).trans (le_abs_self _))

/-- **Section 7.9.** A contraction mapping has at most one fixed point: if $`f(x) = x` and
$`f(y) = y` then $`|x - y| \le c\,|x - y|` with $`c < 1`, so $`|x - y| = 0`. -/
theorem fixedPoint_unique_of_contraction (hc : c < 1) (h : ∀ x y, |f x - f y| ≤ c * |x - y|)
    {x y : ℝ} (hx : f x = x) (hy : f y = y) : x = y := by
  have h1 := h x y
  rw [hx, hy] at h1
  have h2 : |x - y| = 0 := by
    by_contra hne
    have hpos : 0 < |x - y| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    nlinarith
  exact sub_eq_zero.1 (abs_eq_zero.1 h2)

/-- **Theorem 7.9.1, estimate (viii).** For the iterates $`s_n = f^n(x)` of a function with
Lipschitz constant $`c \ge 0`, $`|s_n - s_{n+1}| \le c^n |s_0 - s_1|`. -/
theorem abs_iterate_sub_iterate_succ_le (hc0 : 0 ≤ c) (h : ∀ x y, |f x - f y| ≤ c * |x - y|)
    (x : ℝ) (n : ℕ) : |f^[n] x - f^[n + 1] x| ≤ c ^ n * |x - f x| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := h (f^[n] x) (f^[n + 1] x)
    rw [← Function.iterate_succ_apply' f n x, ← Function.iterate_succ_apply' f (n + 1) x] at h1
    calc |f^[n + 1] x - f^[n + 1 + 1] x| ≤ c * |f^[n] x - f^[n + 1] x| := h1
      _ ≤ c * (c ^ n * |x - f x|) := mul_le_mul_of_nonneg_left ih hc0
      _ = c ^ (n + 1) * |x - f x| := by ring

/-- **Theorem 7.9.1, estimate (ix).** For the iterates of a contraction with constant
$`0 \le c < 1`, $`|s_0 - s_n| \le |s_0 - s_1| / (1 - c)` for all $`n`: the distances
$`|s_k - s_{k+1}|` are dominated by a geometric series. -/
theorem abs_sub_iterate_le (hc0 : 0 ≤ c) (hc1 : c < 1)
    (h : ∀ x y, |f x - f y| ≤ c * |x - y|) (x : ℝ) (n : ℕ) :
    |x - f^[n] x| ≤ |x - f x| / (1 - c) := by
  have key : (1 - c) * |x - f^[n] x| ≤ |x - f x| * (1 - c ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : |x - f^[n + 1] x| ≤ |x - f^[n] x| + |f^[n] x - f^[n + 1] x| := by
        have := abs_add_le (x - f^[n] x) (f^[n] x - f^[n + 1] x)
        simpa using this
      have h2 := abs_iterate_sub_iterate_succ_le hc0 h x n
      have h3 : (1 - c) * |x - f^[n + 1] x| ≤
          (1 - c) * (|x - f^[n] x| + c ^ n * |x - f x|) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      calc (1 - c) * |x - f^[n + 1] x|
          ≤ (1 - c) * (|x - f^[n] x| + c ^ n * |x - f x|) := h3
        _ = (1 - c) * |x - f^[n] x| + (1 - c) * (c ^ n * |x - f x|) := by ring
        _ ≤ |x - f x| * (1 - c ^ n) + (1 - c) * (c ^ n * |x - f x|) := by linarith
        _ = |x - f x| * (1 - c ^ (n + 1)) := by ring
  rw [le_div_iff₀ (by linarith)]
  have h4 : |x - f x| * (1 - c ^ n) ≤ |x - f x| :=
    mul_le_of_le_one_right (abs_nonneg _) (by linarith [pow_nonneg hc0 n])
  linarith

/-- **Theorem 7.9.1, the nonstandard core.** Let $`f` be a contraction with constant
$`0 < c < 1`, let $`x` be real and $`s_n = f^n(x)`. For every unlimited hypernatural $`N`
the extended term $`s_N` is limited and its shadow is a fixed point of $`f`. -/
theorem contraction_limited_and_sh_fixed (hc0 : 0 < c) (hc1 : c < 1)
    (h : ∀ x y, |f x - f y| ≤ c * |x - y|) (x : ℝ) {N : ℝ*} (hN : N ∈ unlimitedHyperNat) :
    Limited (hyperSeq (fun n => f^[n] x) N) ∧
      f (sh (hyperSeq (fun n => f^[n] x) N)) = sh (hyperSeq (fun n => f^[n] x) N) := by
  set s : ℕ → ℝ := fun n => f^[n] x with hs
  -- s_N is limited, by transfer of estimate (ix)
  have hlim : Limited (hyperSeq s N) := by
    have h1 : hyperSeq (fun n => |x - s n|) N ≤ ((|x - f x| / (1 - c) : ℝ) : ℝ*) :=
      hyperSeq_le_coe (fun n => abs_sub_iterate_le hc0.le hc1 h x n) N
    have h2 : hyperSeq (fun n => |x - s n|) N = |(x : ℝ*) - hyperSeq s N| := by
      rw [hyperSeq_abs (fun n => x - s n), hyperSeq_sub (fun _ => x) s, hyperSeq_const]
    rw [h2] at h1
    have h3 : Limited ((x : ℝ*) - hyperSeq s N) :=
      limited_iff_abs_lt.2 ⟨|x - f x| / (1 - c) + 1,
        lt_of_le_of_lt h1 (Hyperreal.coe_lt_coe.2 (by linarith))⟩
    have h4 : hyperSeq s N = x - ((x : ℝ*) - hyperSeq s N) := by ring
    rw [h4]
    exact (limited_coe x).sub h3
  refine ⟨hlim, ?_⟩
  have hsL : hyperSeq s N ≊ sh (hyperSeq s N) := hlim.infClose_sh
  -- f(L) ≃ *f(s_N), by continuity
  have e1 : ⋆f (hyperSeq s N) ≊ (f (sh (hyperSeq s N)) : ℝ) := by
    have := uniformContinuous_iff_infClose.1 (uniformContinuous_of_lipschitz h) _ _ hsL
    rwa [starMap_coe] at this
  -- *f(s_N) = s_{N+1}, by transfer of the recursion
  have e2 : ⋆f (hyperSeq s N) = hyperSeq s (N + 1) := by
    rw [hyperSeq_add_one s hN.1, ← hyperSeq_comp f s hN.1]
    congr 1
    funext n
    exact (Function.iterate_succ_apply' f n x).symm
  -- s_{N+1} ≃ s_N, by transfer of estimate (viii)
  have e3 : hyperSeq s N ≊ hyperSeq s (N + 1) := by
    have h1 : hyperSeq (fun n => |s n - s (n + 1)|) N ≤ hyperSeq (fun n => c ^ n * |x - f x|) N :=
      hyperSeq_le_hyperSeq (fun n => abs_iterate_sub_iterate_succ_le hc0.le h x n) N
    have h2 : hyperSeq (fun n => |s n - s (n + 1)|) N = |hyperSeq s N - hyperSeq s (N + 1)| := by
      rw [hyperSeq_abs (fun n => s n - s (n + 1)), hyperSeq_sub s (fun n => s (n + 1)),
        hyperSeq_add_one s hN.1]
    have h3 : Infinitesimal (hyperSeq (fun n => c ^ n * |x - f x|) N) := by
      have ht : Tendsto (fun n : ℕ => c ^ n * |x - f x|) atTop (𝓝 0) := by
        simpa using (tendsto_pow_zero_of_pos_of_lt_one hc0 hc1).mul_const |x - f x|
      have := hyperSeq_infClose_of_tendsto ht hN
      rwa [Hyperreal.coe_zero, ← infinitesimal_iff_infClose_zero] at this
    rw [h2] at h1
    exact h3.of_abs_le (h1.trans (le_abs_self _))
  have e4 : ((f (sh (hyperSeq s N)) : ℝ) : ℝ*) ≊ (sh (hyperSeq s N) : ℝ) := by
    rw [e2] at e1
    exact (e1.symm.trans e3.symm).trans hsL
  exact infClose_coe_iff.1 e4

/-- **Theorem 7.9.1, tool.** A function with Lipschitz constant $`c < 1` also has a Lipschitz
constant strictly between $`0` and $`1`. -/
theorem exists_pos_contraction_constant (hc : c < 1) (h : ∀ x y, |f x - f y| ≤ c * |x - y|) :
    ∃ c' : ℝ, 0 < c' ∧ c' < 1 ∧ ∀ x y, |f x - f y| ≤ c' * |x - y| :=
  ⟨max c (1 / 2), lt_max_of_lt_right (by norm_num), max_lt hc (by norm_num), fun x y =>
    (h x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))⟩

/-- **Theorem 7.9.1.** Every contraction mapping of the real line has a unique fixed point.
The fixed point is the shadow of any extended term of the sequence of iterates starting at
any real number. -/
theorem existsUnique_fixedPoint_of_contraction (hc : c < 1)
    (h : ∀ x y, |f x - f y| ≤ c * |x - y|) : ∃! L : ℝ, f L = L := by
  obtain ⟨c', hc0, hc1, h'⟩ := exists_pos_contraction_constant hc h
  exact ⟨_, (contraction_limited_and_sh_fixed hc0 hc1 h' 0 omega_mem_unlimitedHyperNat).2,
    fun y hy => fixedPoint_unique_of_contraction hc h hy
      (contraction_limited_and_sh_fixed hc0 hc1 h' 0 omega_mem_unlimitedHyperNat).2⟩

/-- **Section 7.9, remark after Theorem 7.9.1.** For a contraction mapping $`f` with fixed
point $`L` and any real starting point $`x`, the iterates $`x, f(x), f(f(x)), \dots`
converge to $`L`. Every extended term has a shadow that is a fixed point, hence equal to
$`L`; so every extended term is infinitely close to $`L`, and Theorem 6.1.1 applies. -/
theorem tendsto_iterate_of_contraction (hc : c < 1) (h : ∀ x y, |f x - f y| ≤ c * |x - y|)
    (x : ℝ) {L : ℝ} (hL : f L = L) : Tendsto (fun n => f^[n] x) atTop (𝓝 L) := by
  obtain ⟨c', hc0, hc1, h'⟩ := exists_pos_contraction_constant hc h
  rw [tendsto_iff_forall_unlimited_infClose]
  intro N hN
  obtain ⟨hlim, hfix⟩ := contraction_limited_and_sh_fixed hc0 hc1 h' x hN
  rw [← fixedPoint_unique_of_contraction hc h hfix hL]
  exact hlim.infClose_sh

/-- **Section 7.9, definition of a Lipschitz condition.** Mathlib's {name}`LipschitzWith` for
a function on the real line, with constant $`K \ge 0`, is the book's inequality
$`|f(x) - f(y)| \le K\,|x - y|` for all real $`x, y`. -/
theorem lipschitzWith_iff_abs_sub_le {K : NNReal} :
    LipschitzWith K f ↔ ∀ x y, |f x - f y| ≤ K * |x - y| := by
  simp only [lipschitzWith_iff_dist_le_mul, Real.dist_eq]

/-- **Section 7.9**, for Mathlib's notion: a function on the real line that is
{name}`LipschitzWith` some constant is uniformly continuous, by the infinitesimal argument of
{name}`uniformContinuous_of_lipschitz`. -/
theorem uniformContinuous_of_lipschitzWith {K : NNReal} (h : LipschitzWith K f) :
    UniformContinuous f :=
  uniformContinuous_of_lipschitz (lipschitzWith_iff_abs_sub_le.1 h)

/-- **Theorem 7.9.1**, for Mathlib's notion of a contraction mapping: a function on the real
line that is {name}`ContractingWith` some constant has a unique fixed point. -/
theorem existsUnique_fixedPoint_of_contractingWith {K : NNReal} (h : ContractingWith K f) :
    ∃! L : ℝ, f L = L :=
  existsUnique_fixedPoint_of_contraction (c := K) (by exact_mod_cast h.1)
    (lipschitzWith_iff_abs_sub_le.1 h.2)

/-- **Section 7.9, remark after Theorem 7.9.1**, for Mathlib's notion of a contraction
mapping: the iterates converge to the fixed point from every starting point. -/
theorem tendsto_iterate_of_contractingWith {K : NNReal} (h : ContractingWith K f) (x : ℝ)
    {L : ℝ} (hL : f L = L) : Tendsto (fun n => f^[n] x) atTop (𝓝 L) :=
  tendsto_iterate_of_contraction (c := K) (by exact_mod_cast h.1)
    (lipschitzWith_iff_abs_sub_le.1 h.2) x hL

/-- **Section 7.9, example.** The map $`f(x) = x/2 + 1/2` satisfies a Lipschitz condition
with constant $`1/2`, which answers the book's question about its constant. -/
theorem halfAddHalf_lipschitz (x y : ℝ) :
    |(x / 2 + 1 / 2) - (y / 2 + 1 / 2)| ≤ 1 / 2 * |x - y| := by
  have : (x / 2 + 1 / 2) - (y / 2 + 1 / 2) = 1 / 2 * (x - y) := by ring
  rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]

/-- **Section 7.9, example.** The $`n`-th iterate of $`f(x) = x/2 + 1/2` at $`x` is
$`x/2^n + 1 - 1/2^n`. -/
theorem halfAddHalf_iterate (x : ℝ) (n : ℕ) :
    (fun t : ℝ => t / 2 + 1 / 2)^[n] x = x / 2 ^ n + 1 - 1 / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    field_simp
    ring

/-- **Section 7.9, example.** The unique fixed point of $`f(x) = x/2 + 1/2` is $`1`, and the
iterates of $`f` converge to $`1` from every starting point. -/
theorem halfAddHalf_fixedPoint (x : ℝ) :
    (∀ L : ℝ, L / 2 + 1 / 2 = L ↔ L = 1) ∧
      Tendsto (fun n => (fun t : ℝ => t / 2 + 1 / 2)^[n] x) atTop (𝓝 1) :=
  ⟨fun L => ⟨fun h => by linarith, fun h => by rw [h]; norm_num⟩,
    tendsto_iterate_of_contraction (f := fun t : ℝ => t / 2 + 1 / 2) (by norm_num)
      halfAddHalf_lipschitz x (by norm_num)⟩

end Contraction

/-!
## 7.10 A First Look at Permanence

A _permanence principle_ says that a property which holds on some domain must continue to
hold on a larger one. The first example, sometimes called _Cauchy's principle_, concerns a
real number $`c` and a property of real numbers: if the transform of the property holds for
all hyperreals within some positive infinitesimal distance of $`c`, then the property holds
for all reals within some positive real distance of $`c`, and so its transform holds for all
hyperreals within that real distance. The argument is one existential transfer followed by
one universal transfer.

In this formalization a property of real numbers is a set $`S` of reals, and its transform is
the enlargement of $`S`. The existential transfer step was proved at the start of the chapter
as {name}`exists_real_radius_of_hyperreal_radius`, where it served for Theorem 7.1.3. The book
remarks that permanence will later be extended to hyperreal $`c` and to a wider class of
properties (Theorems 11.9.1 and 15.1.1).
-/

section Permanence

variable {f : ℝ → ℝ} {S D A : Set ℝ} {c δ : ℝ} {x : ℝ*}

/-- **Section 7.10, tool.** The enlargement of the real interval of radius $`\delta` around
$`c` is the hyperreal interval of the same radius. -/
theorem mem_starSet_abs_sub_lt : x ∈ ⋆{t : ℝ | |t - c| < δ} ↔ |x - c| < δ := by
  obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
  rw [hyperreal_ofSeq_mem_starSet, coe_eq_ofSeq_const c, abs_ofSeq_sub_ofSeq_lt_iff]
  rfl

/-- **Section 7.10 (Cauchy's principle).** For a set $`S` of reals and a real number $`c`
the following are equivalent:

1. there is a positive infinitesimal $`d` such that every hyperreal $`x` with
   $`|x - c| < d` belongs to the enlargement of $`S`;
2. there is a real $`\delta > 0` such that every real $`t` with $`|t - c| < \delta` belongs
   to $`S`;
3. there is a real $`\delta > 0` such that every hyperreal $`x` with $`|x - c| < \delta`
   belongs to the enlargement of $`S`.

The step from (1) to (2) is existential transfer, and the step from (2) to (3) is universal
transfer. -/
theorem cauchy_principle_tfae (S : Set ℝ) (c : ℝ) :
    List.TFAE [∃ d : ℝ*, 0 < d ∧ Infinitesimal d ∧ ∀ x : ℝ*, |x - c| < d → x ∈ ⋆S,
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - c| < δ → t ∈ S,
      ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ*, |x - c| < δ → x ∈ ⋆S] := by
  tfae_have 1 → 2 := fun ⟨_, hd, _, h⟩ => exists_real_radius_of_hyperreal_radius hd h
  tfae_have 2 → 3 := fun ⟨δ, hδ, h⟩ =>
    ⟨δ, hδ, fun x hx => starSet_subset_starSet.2 (fun t ht => h t ht)
      (mem_starSet_abs_sub_lt.2 hx)⟩
  tfae_have 3 → 1 := fun ⟨δ, hδ, h⟩ =>
    ⟨ε, Hyperreal.epsilon_pos, infinitesimal_epsilon, fun x hx =>
      h x (hx.trans (epsilon_pos_infinitesimal.2 δ hδ))⟩
  tfae_finish

/-- **Section 7.10 (Cauchy's principle).** If the transform of a property holds for all
hyperreals within a positive infinitesimal distance $`d` of the real number $`c`, then it
holds for all hyperreals within some positive real distance of $`c`. -/
theorem cauchy_principle {d : ℝ*} (hd : 0 < d) (hd' : Infinitesimal d)
    (h : ∀ x : ℝ*, |x - c| < d → x ∈ ⋆S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ*, |x - c| < δ → x ∈ ⋆S := by
  have := (cauchy_principle_tfae S c).out 1 3
  exact this.1 ⟨d, hd, hd', h⟩

/-!
## 7.11 Exercises on Permanence of Functions

(1) A real function $`f` with domain $`D` has its extension defined on the enlargement of
$`D`. The extension is defined at all points infinitely close to $`c` exactly when $`f` is
defined on a real open interval around $`c`.

(2) If the extension of $`f` is constant on the halo of $`c`, then $`f` is constant on a
real open interval around $`c`.

(3) A function that is continuous on an interval and whose extension takes only real values
on the enlargement of the interval is constant: at each point of the interval the extension
is constant on the halo, so the function is locally constant by (2), and a locally constant
function on an interval is constant.
-/

/-- **Exercise 7.11(1).** Let $`D` be the domain of a real function and $`c` a real number.
The enlargement of $`D` contains the halo of $`c`, so that the extension is defined at all
$`x \simeq c`, if and only if $`D` contains a real open interval
$`(c - \delta, c + \delta)` with $`\delta > 0`. -/
theorem hal_subset_starSet_iff :
    hal (c : ℝ*) ⊆ ⋆D ↔ ∃ δ : ℝ, 0 < δ ∧ Ioo (c - δ) (c + δ) ⊆ D := by
  constructor
  · intro h
    obtain ⟨δ, hδ, hδ'⟩ := exists_real_radius_of_hyperreal_radius (c := c) (S := D)
      Hyperreal.epsilon_pos fun x hx => h (by
        rw [mem_hal, infClose_comm]
        exact infinitesimal_epsilon.of_abs_le (by
          rw [abs_of_pos Hyperreal.epsilon_pos]; exact hx.le))
    exact ⟨δ, hδ, fun t ht => hδ' t (abs_lt.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩)⟩
  · rintro ⟨δ, hδ, h⟩ x hx
    rw [mem_hal, infClose_comm] at hx
    refine starSet_subset_starSet.2 (fun t ht => h ?_)
      (mem_starSet_abs_sub_lt.2 (infClose_iff_abs_lt.1 hx δ hδ))
    have := abs_lt.1 (show |t - c| < δ from ht)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- **Exercise 7.11(2).** If the extension of $`f` is constant on the halo of the real
number $`c`, then $`f` is constant on some real interval $`(c - \delta, c + \delta)`. The
halo is contained in the enlargement of the set where $`f` takes the value $`f(c)`, and
Exercise (1) applies to that set. -/
theorem exists_Ioo_const_of_const_on_hal
    (h : ∀ x ∈ hal (c : ℝ*), ∀ y ∈ hal (c : ℝ*), ⋆f x = ⋆f y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo (c - δ) (c + δ), f t = f c := by
  have hc : (c : ℝ*) ∈ hal (c : ℝ*) := InfClose.refl _
  obtain ⟨δ, hδ, hδ'⟩ := (hal_subset_starSet_iff (D := {t : ℝ | f t = f c})).1 fun x hx => by
    rw [mem_starSet_setOf_eq, h x hx _ hc, starMap_coe]
  exact ⟨δ, hδ, fun t ht => hδ' ht⟩

/-- **Exercise 7.11(3), local step.** Let $`f` be continuous on $`A` and suppose
$`{}^*f(x)` is real for every $`x` in the enlargement of $`A`. Then every $`c \in A` has a
real $`\delta > 0` such that $`f(t) = f(c)` for all $`t \in A` within $`\delta` of $`c`. For
$`x \simeq c` in the enlargement, $`{}^*f(x)` is a real number infinitely close to
$`f(c)`, hence equal to it; so the property "if $`t \in A` then $`f(t) = f(c)`" holds
throughout the halo of $`c`, and Cauchy's principle applies. -/
theorem exists_radius_const_of_starMap_real (hf : ContinuousOn f A)
    (h : ∀ x ∈ ⋆A, ∃ r : ℝ, ⋆f x = r) (hc : c ∈ A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ A, |t - c| < δ → f t = f c := by
  obtain ⟨δ, hδ, hδ'⟩ := exists_real_radius_of_hyperreal_radius (c := c)
    (S := {t : ℝ | t ∈ A → f t = f c}) Hyperreal.epsilon_pos fun x hx => by
      have hxc : x ≊ c := infinitesimal_epsilon.of_abs_le (by
        rw [abs_of_pos Hyperreal.epsilon_pos]; exact hx.le)
      obtain ⟨r, rfl⟩ := hyperreal_exists_rep x
      rw [hyperreal_ofSeq_mem_starSet]
      simp only [mem_ofPred_eq]
      rw [almostAll_imp]
      intro hA
      have hA' := hyperreal_ofSeq_mem_starSet.2 hA
      obtain ⟨v, hv⟩ := h _ hA'
      have e := (hf c hc).starMap_infClose hA' hxc
      rw [hv, infClose_coe_iff] at e
      rw [e, starMap_hyperreal_ofSeq, coe_eq_ofSeq_const, ofSeq_eq_ofSeq_iff] at hv
      exact hv
  exact ⟨δ, hδ, fun t ht htc => hδ' t htc ht⟩

/-- **Exercise 7.11(3).** Let the real function $`f` be continuous on an interval $`A`. If
$`{}^*f(x)` is real for all $`x` in the enlargement of $`A`, then $`f` is constant on $`A`.
An interval is expressed as an order-connected set. The passage from locally constant to
constant uses the standard fact that an interval is connected. -/
theorem eq_of_starMap_real_of_ordConnected (hA : A.OrdConnected) (hf : ContinuousOn f A)
    (h : ∀ x ∈ ⋆A, ∃ r : ℝ, ⋆f x = r) {s t : ℝ} (hs : s ∈ A) (ht : t ∈ A) : f s = f t := by
  have : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.1 hA.isPreconnected
  have hloc : IsLocallyConstant (A.domRestrict f) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro u
    obtain ⟨δ, hδ, hδ'⟩ := exists_radius_const_of_starMap_real hf h u.2
    rw [Metric.eventually_nhds_iff]
    exact ⟨δ, hδ, fun v hv => hδ' v v.2 (by rwa [Subtype.dist_eq, Real.dist_eq] at hv)⟩
  exact hloc.apply_eq_of_preconnectedSpace ⟨s, hs⟩ ⟨t, ht⟩

end Permanence

end Goldblatt
