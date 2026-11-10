import Goldblatt.Ch18_Completion.Hull

/-!
# 18 (part 3). The integers in the p-adic metric: Section 18.4

This is the third of six parts of Chapter 18 (the overview is on the chapter page
{lit}`Goldblatt.Ch18_Completion`). It shows that the ring of $`p`-adic integers is the
nonstandard hull of the integers under the $`p`-adic metric, and that this hull is a
completion of the integers.
-/

noncomputable section

namespace Goldblatt.Completion

open Filter

open scoped Hyperreal

variable (p : ℕ) [hp : Fact p.Prime]

/-!
## 18.4 p-adic Integers

The standard notions are Mathlib's. The $`p`-adic order $`o_p(z)` of an integer is
{name}`padicValInt`, the $`p`-adic norm $`|z|_p = p^{-o_p(z)}` is {name}`padicNorm`, and
the laws stated in the book are {name}`padicValInt.mul`, {name}`padicNorm.mul` and
{name}`padicNorm.nonarchimedean`. The ring $`\mathbb Z_p` is {name}`PadicInt`. The book
presents a $`p`-adic integer as a sequence of residues $`a_n \in \mathbb Z/p^n` with
$`a_{n+1} \equiv a_n \pmod{p^n}`; in Mathlib the residue $`a_n` of $`a` is
{name}`PadicInt.toZModPow`, a $`p`-adic integer is determined by its residues
({name}`PadicInt.ext_of_toZModPow`), and every compatible family of residues comes from a
$`p`-adic integer ({name}`PadicInt.lift`).

In the enlargement, the norm and the order extend to $`{}^*\mathbb Z`. A hyperinteger is
$`p`-adically infinitesimal exactly when it is divisible by every standard power of $`p`.
Reducing a hyperinteger modulo each standard power of $`p` gives a ring homomorphism
$`\theta_p` from $`{}^*\mathbb Z` onto $`\mathbb Z_p` whose kernel is the ideal of
infinitesimals, and $`\theta_p` matches the shadow of the extended norm with the norm of
$`\mathbb Z_p`. So $`\mathbb Z_p` is the nonstandard hull of $`(\mathbb Z, d_p)`, and since
every hyperinteger is approachable from $`\mathbb Z`, it is the completion.
-/

/-- A prime power is nonzero, so the ring of residues modulo it is finite. -/
instance neZero_prime_pow (n : ℕ) : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩

omit hp in
/-- The standard-part map of a finite ring is a ring homomorphism from its enlargement. -/
def stdRingHom (F : Type*) [Semiring F] [Finite F] : Star F →+* F where
  toFun := Star.std
  map_one' := Star.std_const 1
  map_zero' := Star.std_const 0
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := Star.exists_eq_const_of_finite x
    obtain ⟨b, rfl⟩ := Star.exists_eq_const_of_finite y
    rw [Star.std_const, Star.std_const]
    exact Star.std_const (a * b)
  map_add' x y := by
    obtain ⟨a, rfl⟩ := Star.exists_eq_const_of_finite x
    obtain ⟨b, rfl⟩ := Star.exists_eq_const_of_finite y
    rw [Star.std_const, Star.std_const]
    exact Star.std_const (a + b)

/-- **Section 18.4.** The extension of the $`p`-adic norm to the hyperintegers,
$`|x|_p \in {}^*\mathbb R`. -/
def hpnormInt (x : Star ℤ) : ℝ* := Germ.map (fun z : ℤ => ((padicNorm p z : ℚ) : ℝ)) x

omit hp in
theorem hpnormInt_coe (f : ℕ → ℤ) :
    hpnormInt p (↑f : Star ℤ) = Hyperreal.ofSeq fun i => ((padicNorm p (f i) : ℚ) : ℝ) := rfl

/-- **Section 18.4.** The extension of the $`p`-adic order to the hyperintegers, with values
in the nonnegative hyperintegers. -/
def hpval (x : Star ℤ) : Star ℕ := Germ.map (padicValInt p) x

/-- **Section 18.4.** The power $`p^N` for a hypernatural exponent $`N`. -/
def hpow (N : Star ℕ) : Star ℤ := Germ.map (fun k : ℕ => (p : ℤ) ^ k) N

omit hp in
theorem hpnormInt_nonneg (x : Star ℤ) : 0 ≤ hpnormInt p x := by
  obtain ⟨f, rfl⟩ := x.exists_rep
  exact (Hyperreal.ofSeq_le_ofSeq (f := fun _ => 0)).2
    (Eventually.of_forall fun i => by
      show (0 : ℝ) ≤ ((padicNorm p (f i) : ℚ) : ℝ)
      exact_mod_cast padicNorm.nonneg (p := p) (f i : ℚ))

/-- **Section 18.4.** $`|x|_p \le 1` for every hyperinteger, by transfer. Hence every
hyperinteger is $`p`-adically limited. -/
theorem hpnormInt_le_one (x : Star ℤ) : hpnormInt p x ≤ 1 := by
  obtain ⟨f, rfl⟩ := x.exists_rep
  exact (Hyperreal.ofSeq_le_ofSeq (g := fun _ => 1)).2
    (Eventually.of_forall fun i => by
      show ((padicNorm p (f i) : ℚ) : ℝ) ≤ 1
      exact_mod_cast padicNorm.of_int (p := p) (f i))

theorem limited_hpnormInt (x : Star ℤ) : Limited (hpnormInt p x) :=
  ⟨1, by rw [abs_of_nonneg (hpnormInt_nonneg p x)]; exact hpnormInt_le_one p x⟩

omit hp in
theorem hpnormInt_neg (x : Star ℤ) : hpnormInt p (-x) = hpnormInt p x := by
  obtain ⟨f, rfl⟩ := x.exists_rep
  refine congrArg Hyperreal.ofSeq (funext fun i => ?_)
  show ((padicNorm p ((-f i : ℤ) : ℚ) : ℚ) : ℝ) = ((padicNorm p ((f i : ℤ) : ℚ) : ℚ) : ℝ)
  rw [Int.cast_neg, padicNorm.neg]

/-- **Statement (ii) of Section 18.4, in terms of the norm.** For a standard $`n`, the
power $`p^n` divides a hyperinteger $`x` in $`{}^*\mathbb Z` if and only if
$`|x|_p \le p^{-n}`. -/
theorem hpnormInt_le_pow_iff (n : ℕ) {x : Star ℤ} :
    hpnormInt p x ≤ (((p : ℝ) ^ (-(n : ℤ)) : ℝ) : ℝ*) ↔ Germ.const ((p : ℤ) ^ n) ∣ x := by
  obtain ⟨f, rfl⟩ := x.exists_rep
  rw [hpnormInt_coe]
  refine (Hyperreal.ofSeq_le_ofSeq (g := fun _ => (p : ℝ) ^ (-(n : ℤ)))).trans
    ((eventually_congr (Eventually.of_forall fun i => ?_)).trans
      (Star.coe_dvd_coe (f := fun _ => (p : ℤ) ^ n)).symm)
  have key : ((padicNorm p (f i) : ℚ) : ℝ) ≤ (p : ℝ) ^ (-(n : ℤ)) ↔
      padicNorm p (f i) ≤ (p : ℚ) ^ (-(n : ℤ)) := by
    rw [← Rat.cast_le (K := ℝ), Rat.cast_zpow, Rat.cast_natCast]
  show ((padicNorm p (f i) : ℚ) : ℝ) ≤ (p : ℝ) ^ (-(n : ℤ)) ↔ (p : ℤ) ^ n ∣ f i
  rw [← Nat.cast_pow, padicNorm.dvd_iff_norm_le]
  exact key

/-- An integer not divisible by $`p^{m+1}` has $`p`-adic norm at least $`p^{-m}`. -/
theorem le_padicNorm_of_not_dvd {z : ℤ} {m : ℕ} (h : ¬(p : ℤ) ^ (m + 1) ∣ z) :
    (p : ℝ) ^ (-(m : ℤ)) ≤ ((padicNorm p z : ℚ) : ℝ) := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : ‖(z : ℚ_[p])‖ = ((padicNorm p z : ℚ) : ℝ) := by
    have := Padic.eq_padicNorm (p := p) (z : ℚ)
    rwa [Rat.cast_intCast] at this
  rw [← h1, Padic.norm_lt_pow_iff_norm_le_pow_sub_one] at hlt
  have h2 : (-(m : ℤ) - 1) = (-((m + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [h2, Padic.norm_int_le_pow_iff_dvd] at hlt
  exact h hlt

/-- **Theorem 18.4.1, (1) iff (3).** A hyperinteger is $`p`-adically infinitesimal if and
only if it is divisible in $`{}^*\mathbb Z` by $`p^n` for every standard $`n`. -/
theorem infinitesimal_hpnormInt_iff_forall_dvd {x : Star ℤ} :
    Infinitesimal (hpnormInt p x) ↔ ∀ n : ℕ, Germ.const ((p : ℤ) ^ n) ∣ x := by
  constructor
  · intro h n
    have hpos : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) :=
      zpow_pos (by exact_mod_cast hp.out.pos) _
    have := h _ hpos
    rw [abs_of_nonneg (hpnormInt_nonneg p x)] at this
    exact (hpnormInt_le_pow_iff p n).1 this.le
  · intro h r hr
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hr
    rw [abs_of_nonneg (hpnormInt_nonneg p x)]
    exact ((hpnormInt_le_pow_iff p k).2 (h k)).trans_lt (Hyperreal.coe_lt_coe.2 hk)

omit hp in
theorem eventually_ne_zero_of_ne_zero {f : ℕ → ℤ} (h : (↑f : Star ℤ) ≠ 0) :
    ∀ᶠ i in hyperfilter ℕ, f i ≠ 0 :=
  Ultrafilter.eventually_not.2 fun h0 => h (Germ.coe_eq.2 h0)

/-- **Theorem 18.4.1, (2) iff (3).** For a nonzero hyperinteger $`x`, the order
$`o_p(x)` is unlimited if and only if every standard power of $`p` divides $`x`. This is
the transfer of statement (ii): $`p^n \mid x` iff $`n \le o_p(x)`. -/
theorem unlimited_hpval_iff_forall_dvd {x : Star ℤ} (hx : x ≠ 0) :
    Unlimited (hpval p x) ↔ ∀ n : ℕ, Germ.const ((p : ℤ) ^ n) ∣ x := by
  obtain ⟨f, rfl⟩ := x.exists_rep
  have h0 := eventually_ne_zero_of_ne_zero hx
  have key : ∀ n : ℕ, (Germ.const ((p : ℤ) ^ n) ∣ (↑f : Star ℤ)) ↔
      ∀ᶠ i in hyperfilter ℕ, n ≤ padicValInt p (f i) := fun n => by
    rw [show (Germ.const ((p : ℤ) ^ n) : Star ℤ) = ↑(fun _ : ℕ => (p : ℤ) ^ n) from rfl,
      Star.coe_dvd_coe]
    refine eventually_congr (h0.mono fun i hi => ?_)
    rw [padicValInt_dvd_iff]
    exact or_iff_right hi
  show Unlimited (↑(fun i => padicValInt p (f i)) : Star ℕ) ↔ _
  rw [unlimited_coe_iff]
  constructor
  · intro h n
    exact (key n).2 ((h n).mono fun i hi => hi.le)
  · intro h n
    exact ((key (n + 1)).1 (h (n + 1))).mono fun i hi => hi

omit hp in
/-- **Section 18.4.** Every hyperinteger is divisible by $`p^{o_p(x)}`, by transfer. -/
theorem hpow_hpval_dvd (x : Star ℤ) : hpow p (hpval p x) ∣ x := by
  obtain ⟨f, rfl⟩ := x.exists_rep
  show (↑(fun i => (p : ℤ) ^ padicValInt p (f i)) : Star ℤ) ∣ ↑f
  exact Star.coe_dvd_coe.2 (Eventually.of_forall fun i => padicValInt_dvd (f i))

omit hp in
/-- **Theorem 18.4.1, (4) implies (3).** A hyperinteger divisible by $`p^N` for some
unlimited $`N` is divisible by every standard power of $`p`. -/
theorem forall_dvd_of_hpow_dvd {x : Star ℤ} {N : Star ℕ} (hN : Unlimited N)
    (h : hpow p N ∣ x) (n : ℕ) : Germ.const ((p : ℤ) ^ n) ∣ x := by
  refine Dvd.dvd.trans ?_ h
  obtain ⟨κ, rfl⟩ := N.exists_rep
  show (↑(fun _ : ℕ => (p : ℤ) ^ n) : Star ℤ) ∣ ↑(fun i => (p : ℤ) ^ κ i)
  exact Star.coe_dvd_coe.2 ((unlimited_coe_iff.1 hN n).mono fun i hi => pow_dvd_pow _ hi.le)

/-- **Theorem 18.4.1.** For a nonzero hyperinteger $`x` the following are equivalent:
$`x` is $`p`-adically infinitesimal; $`o_p(x)` is unlimited; $`x` is divisible by $`p^n`
for every standard $`n`; $`x` is divisible by $`p^N` for some unlimited $`N`. In the last
step the book finds $`N` by overflow; here $`N = o_p(x)` works. -/
theorem padic_infinitesimal_tfae {x : Star ℤ} (hx : x ≠ 0) :
    List.TFAE [Infinitesimal (hpnormInt p x),
      Unlimited (hpval p x),
      ∀ n : ℕ, Germ.const ((p : ℤ) ^ n) ∣ x,
      ∃ N : Star ℕ, Unlimited N ∧ hpow p N ∣ x] := by
  tfae_have 1 ↔ 3 := infinitesimal_hpnormInt_iff_forall_dvd p
  tfae_have 2 ↔ 3 := unlimited_hpval_iff_forall_dvd p hx
  tfae_have 2 → 4 := fun h => ⟨hpval p x, h, hpow_hpval_dvd p x⟩
  tfae_have 4 → 3 := fun ⟨_, hN, h⟩ => forall_dvd_of_hpow_dvd p hN h
  tfae_finish

/-- **Section 18.4.** The set of $`p`-adic infinitesimals is
$`\{p^N q : N \text{ unlimited},\ q \in {}^*\mathbb Z\}`. -/
theorem infinitesimal_hpnormInt_iff_exists {x : Star ℤ} :
    Infinitesimal (hpnormInt p x) ↔ ∃ (N : Star ℕ) (q : Star ℤ), Unlimited N ∧ x = hpow p N * q := by
  constructor
  · intro h
    by_cases hx : x = 0
    · exact ⟨omegaNat, 0, unlimited_omegaNat, by rw [hx, mul_zero]⟩
    · obtain ⟨q, hq⟩ := hpow_hpval_dvd p x
      exact ⟨hpval p x, q, (unlimited_hpval_iff_forall_dvd p hx).2
        ((infinitesimal_hpnormInt_iff_forall_dvd p).1 h), hq⟩
  · rintro ⟨N, q, hN, rfl⟩
    exact (infinitesimal_hpnormInt_iff_forall_dvd p).2
      (forall_dvd_of_hpow_dvd p hN (Dvd.intro q rfl))

/-- **Section 18.4.** $`p^N` is $`p`-adically infinitesimal whenever $`N` is unlimited. -/
theorem infinitesimal_hpnormInt_hpow {N : Star ℕ} (hN : Unlimited N) :
    Infinitesimal (hpnormInt p (hpow p N)) :=
  (infinitesimal_hpnormInt_iff_exists p).2 ⟨N, 1, hN, (mul_one _).symm⟩

/-- **Non-vacuity.** There is a nonzero $`p`-adically infinitesimal hyperinteger. -/
theorem exists_infinitesimal_hpnormInt_ne_zero :
    ∃ x : Star ℤ, x ≠ 0 ∧ Infinitesimal (hpnormInt p x) := by
  refine ⟨hpow p omegaNat, fun h => ?_, infinitesimal_hpnormInt_hpow p unlimited_omegaNat⟩
  obtain ⟨i, hi⟩ := (Germ.coe_eq.1 h).exists
  exact pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero) hi

/-- **Section 18.4.** Reduction modulo $`p^n` on the hyperintegers,
$`x \mapsto x \bmod p^n`. It is the transform of reduction modulo $`p^n`, with values in
$`{}^*(\mathbb Z/p^n) = \mathbb Z/p^n`. -/
def hmod (n : ℕ) : Star ℤ →+* ZMod (p ^ n) :=
  (stdRingHom (ZMod (p ^ n))).comp (mapRingHom (Int.castRingHom (ZMod (p ^ n))))

theorem hmod_coe_eq_iff {n : ℕ} {f : ℕ → ℤ} {b : ZMod (p ^ n)} :
    hmod p n (↑f : Star ℤ) = b ↔ ∀ᶠ i in hyperfilter ℕ, ((f i : ℤ) : ZMod (p ^ n)) = b :=
  Star.std_eq_iff (f := fun i => ((f i : ℤ) : ZMod (p ^ n)))

@[simp]
theorem hmod_const (n : ℕ) (z : ℤ) : hmod p n (Germ.const z) = (z : ZMod (p ^ n)) :=
  (hmod_coe_eq_iff p).2 (Eventually.of_forall fun _ => rfl)

/-- **Section 18.4.** $`x \bmod p^n = 0` exactly when $`p^n` divides $`x` in
$`{}^*\mathbb Z`. -/
theorem hmod_eq_zero_iff {n : ℕ} {x : Star ℤ} :
    hmod p n x = 0 ↔ Germ.const ((p : ℤ) ^ n) ∣ x := by
  obtain ⟨f, rfl⟩ := x.exists_rep
  rw [hmod_coe_eq_iff, show (Germ.const ((p : ℤ) ^ n) : Star ℤ) = ↑(fun _ : ℕ => (p : ℤ) ^ n)
    from rfl, Star.coe_dvd_coe]
  refine eventually_congr (Eventually.of_forall fun i => ?_)
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]

/-- **Section 18.4.** Each hyperinteger is congruent modulo $`p^n` to the standard residue
$`x \bmod p^n`: the difference is divisible by $`p^n` in $`{}^*\mathbb Z`. -/
theorem dvd_sub_hmod_val (n : ℕ) (x : Star ℤ) :
    Germ.const ((p : ℤ) ^ n) ∣ x - Germ.const (((hmod p n x).val : ℕ) : ℤ) := by
  rw [← hmod_eq_zero_iff, map_sub, hmod_const, Int.cast_natCast, ZMod.natCast_zmod_val,
    sub_self]

/-- **Section 18.4, the instructive exercise.** The residues of a hyperinteger are
compatible: $`(x \bmod p^{n}) \bmod p^m = x \bmod p^m` for $`m \le n`. So the sequence of
residues of $`x` is a $`p`-adic integer. -/
theorem hmod_compat (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (hmod p n) = hmod p m := by
  ext x
  obtain ⟨f, rfl⟩ := x.exists_rep
  rw [RingHom.comp_apply, eq_comm, hmod_coe_eq_iff]
  have h1 := (hmod_coe_eq_iff p (n := n) (f := f)).1 rfl
  filter_upwards [h1] with i hi
  rw [← hi, map_intCast]

/-- **Section 18.4.** The homomorphism $`\theta_p : {}^*\mathbb Z \to \mathbb Z_p`,
$`\theta_p(x) = (x \bmod p, x \bmod p^2, \dots)`. It preserves addition and multiplication
because each reduction does. -/
def theta : Star ℤ →+* ℤ_[p] := PadicInt.lift (hmod_compat p)

/-- The $`n`-th residue of $`\theta_p(x)` is $`x \bmod p^n`. -/
@[simp]
theorem toZModPow_theta (n : ℕ) (x : Star ℤ) :
    PadicInt.toZModPow n (theta p x) = hmod p n x :=
  RingHom.congr_fun (PadicInt.lift_spec (hmod_compat p) n) x

/-- **Section 18.4.** $`\theta_p` leaves the standard integers fixed. -/
@[simp]
theorem theta_const (z : ℤ) : theta p (Germ.const z) = (z : ℤ_[p]) :=
  PadicInt.ext_of_toZModPow.1 fun n => by rw [toZModPow_theta, hmod_const, map_intCast]

theorem theta_eq_zero_iff_forall_dvd {x : Star ℤ} :
    theta p x = 0 ↔ ∀ n : ℕ, Germ.const ((p : ℤ) ^ n) ∣ x := by
  rw [← PadicInt.ext_of_toZModPow]
  exact forall_congr' fun n => by rw [toZModPow_theta, map_zero, hmod_eq_zero_iff]

/-- **Section 18.4.** The kernel of $`\theta_p` is the set of $`p`-adic infinitesimals,
which is therefore an ideal of $`{}^*\mathbb Z`. -/
theorem mem_ker_theta {x : Star ℤ} :
    x ∈ RingHom.ker (theta p) ↔ Infinitesimal (hpnormInt p x) := by
  rw [RingHom.mem_ker, theta_eq_zero_iff_forall_dvd, infinitesimal_hpnormInt_iff_forall_dvd]

/-- **Section 18.4.** The coset of $`x` modulo the infinitesimals is the set of
hyperintegers $`p`-adically infinitely close to $`x`: $`\theta_p(x) = \theta_p(y)` iff
$`|x - y|_p \simeq 0`. -/
theorem theta_eq_theta_iff {x y : Star ℤ} :
    theta p x = theta p y ↔ Infinitesimal (hpnormInt p (x - y)) := by
  rw [← mem_ker_theta, RingHom.mem_ker, map_sub, sub_eq_zero]

/-- **Section 18.4, surjectivity with a positive witness.** Every $`p`-adic integer $`a`
is $`\theta_p(x)` for a positive hyperinteger $`x`, namely the class of the sequence of
residues of $`a`. The book obtains $`x` from the concurrence of the relation
$`x \equiv a_n \pmod{p^n}`; in the ultrapower the witness of a concurrent relation on
$`\mathbb N` is its diagonal sequence. -/
theorem theta_ofNat_appr (a : ℤ_[p]) :
    theta p (↑(fun i => ((a.appr i : ℕ) : ℤ)) : Star ℤ) = a := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  rw [toZModPow_theta, hmod_coe_eq_iff]
  filter_upwards [eventually_ge_hyperfilter n] with i hi
  rw [← PadicInt.cast_toZModPow n i hi a]
  show _ = ZMod.cast ((a.appr i : ℕ) : ZMod (p ^ i))
  rw [ZMod.cast_natCast (pow_dvd_pow p hi), Int.cast_natCast]

/-- **Section 18.4.** $`\theta_p` maps $`{}^*\mathbb Z` onto $`\mathbb Z_p`. -/
theorem theta_surjective : Function.Surjective (theta p) := fun a => ⟨_, theta_ofNat_appr p a⟩

/-- **Section 18.4.** The ring isomorphism
$`{}^*\mathbb Z / {}^*\mathbb Z^{\inf_p} \cong \mathbb Z_p`. -/
def starIntQuotEquiv : (Star ℤ ⧸ RingHom.ker (theta p)) ≃+* ℤ_[p] :=
  RingHom.quotientKerEquivOfSurjective (theta_surjective p)

theorem norm_theta_le_pow_iff (n : ℕ) {x : Star ℤ} :
    ‖theta p x‖ ≤ (p : ℝ) ^ (-(n : ℤ)) ↔ Germ.const ((p : ℤ) ^ n) ∣ x := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    toZModPow_theta, hmod_eq_zero_iff]

/-- **Section 18.4, preserving the metric.** For every hyperinteger $`x`, the shadow of
$`|x|_p` is the norm of $`\theta_p(x)` in $`\mathbb Z_p`. If $`\theta_p(x) = 0` both sides
are zero; otherwise both are $`p^{-n}` for the least standard $`n` with
$`p^{n+1} \nmid x`. -/
theorem sh_hpnormInt (x : Star ℤ) : sh (hpnormInt p x) = ‖theta p x‖ := by
  by_cases hall : ∀ n : ℕ, Germ.const ((p : ℤ) ^ n) ∣ x
  · rw [(theta_eq_zero_iff_forall_dvd p).2 hall, norm_zero]
    exact ((infinitesimal_hpnormInt_iff_forall_dvd p).2 hall).sh_eq
  · classical
    rw [not_forall] at hall
    have hfind := Nat.find_spec hall
    have hne : Nat.find hall ≠ 0 := by
      intro h0
      rw [h0] at hfind
      exact hfind (by
        rw [pow_zero]
        exact one_dvd x)
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
    have hdvd : Germ.const ((p : ℤ) ^ m) ∣ x :=
      not_not.1 (Nat.find_min hall (by rw [hm]; exact Nat.lt_succ_self m))
    rw [hm] at hfind
    have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
    refine le_antisymm ?_ ?_
    · -- the shadow is at most `p ^ (-m)`, and the norm of `θ x` is at least that
      refine (sh_le_of_le (limited_hpnormInt p x) ((hpnormInt_le_pow_iff p m).2 hdvd)).trans ?_
      have h1 : ¬‖theta p x‖ ≤ (p : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := fun h =>
        hfind ((norm_theta_le_pow_iff p (m + 1)).1 h)
      rw [PadicInt.norm_le_pow_iff_norm_lt_pow_add_one, not_lt] at h1
      have h2 : (-((m + 1 : ℕ) : ℤ) + 1) = (-(m : ℤ)) := by push_cast; ring
      rwa [h2] at h1
    · refine ((norm_theta_le_pow_iff p m).2 hdvd).trans ?_
      refine le_sh_of_le (limited_hpnormInt p x) ?_
      obtain ⟨f, rfl⟩ := x.exists_rep
      have h1 : ∀ᶠ i in hyperfilter ℕ, ¬(p : ℤ) ^ (m + 1) ∣ f i :=
        Ultrafilter.eventually_not.2 fun h =>
          hfind ((Star.coe_dvd_coe (f := fun _ => (p : ℤ) ^ (m + 1))).2 h)
      exact (Hyperreal.ofSeq_le_ofSeq (f := fun _ => (p : ℝ) ^ (-(m : ℤ)))).2
        (h1.mono fun i hi => le_padicNorm_of_not_dvd p hi)

/-- **Section 18.4.** Every hyperinteger is within $`p^{-n}` of the standard integer
$`x \bmod p^n` in the $`p`-adic metric. -/
theorem hpnormInt_sub_hmod_le (n : ℕ) (x : Star ℤ) :
    hpnormInt p (x - Germ.const (((hmod p n x).val : ℕ) : ℤ)) ≤
      (((p : ℝ) ^ (-(n : ℤ)) : ℝ) : ℝ*) :=
  (hpnormInt_le_pow_iff p n).2 (dvd_sub_hmod_val p n x)

/-!
### The metric space and its hull

To apply Section 18.3 the integers must carry the $`p`-adic metric. The type
{lit}`PadicZ p` is a copy of $`\mathbb Z` with the metric $`d_p(x, y) = |x - y|_p`.
-/

/-- **Section 18.4.** The integers as a metric space under the $`p`-adic metric
$`d_p(x, y) = |x - y|_p`. -/
def PadicZ (_p : ℕ) : Type := ℤ

/-- The integer underlying a point of the $`p`-adic metric space of integers. -/
def PadicZ.toInt {p : ℕ} (a : PadicZ p) : ℤ := a

/-- An integer as a point of the $`p`-adic metric space of integers. -/
def PadicZ.ofInt (p : ℕ) (z : ℤ) : PadicZ p := z

omit hp in
@[simp]
theorem PadicZ.toInt_ofInt (z : ℤ) : (PadicZ.ofInt p z).toInt = z := rfl

instance : MetricSpace (PadicZ p) where
  dist a b := ((padicNorm p ((a.toInt - b.toInt : ℤ) : ℚ) : ℚ) : ℝ)
  dist_self a := by simp
  dist_comm a b := by
    have : ((b.toInt - a.toInt : ℤ) : ℚ) = -((a.toInt - b.toInt : ℤ) : ℚ) := by push_cast; ring
    show ((padicNorm p _ : ℚ) : ℝ) = ((padicNorm p _ : ℚ) : ℝ)
    rw [this, padicNorm.neg]
  dist_triangle a b c := by
    have e : ((a.toInt - c.toInt : ℤ) : ℚ) =
        ((a.toInt - b.toInt : ℤ) : ℚ) + ((b.toInt - c.toInt : ℤ) : ℚ) := by push_cast; ring
    have h := padicNorm.triangle_ineq (p := p) ((a.toInt - b.toInt : ℤ) : ℚ)
      ((b.toInt - c.toInt : ℤ) : ℚ)
    rw [← e] at h
    show ((padicNorm p ((a.toInt - c.toInt : ℤ) : ℚ) : ℚ) : ℝ) ≤
      ((padicNorm p ((a.toInt - b.toInt : ℤ) : ℚ) : ℚ) : ℝ) +
        ((padicNorm p ((b.toInt - c.toInt : ℤ) : ℚ) : ℚ) : ℝ)
    exact_mod_cast h
  eq_of_dist_eq_zero {a b} h := by
    have h1 : padicNorm p ((a.toInt - b.toInt : ℤ) : ℚ) = 0 := by exact_mod_cast h
    have h2 := padicNorm.zero_of_padicNorm_eq_zero h1
    have h3 : a.toInt - b.toInt = 0 := by exact_mod_cast h2
    exact (sub_eq_zero.1 h3 : a.toInt = b.toInt)

theorem PadicZ.dist_eq (a b : PadicZ p) :
    dist a b = ((padicNorm p ((a.toInt - b.toInt : ℤ) : ℚ) : ℚ) : ℝ) := rfl

/-- The hyperinteger underlying a point of the enlargement of the $`p`-adic metric space of
integers. -/
def fromPadicZ {p : ℕ} (y : Star (PadicZ p)) : Star ℤ := Germ.map PadicZ.toInt y

/-- A hyperinteger as a point of the enlargement of the $`p`-adic metric space. -/
def toPadicZ (x : Star ℤ) : Star (PadicZ p) := Germ.map (PadicZ.ofInt p) x

omit hp in
@[simp]
theorem fromPadicZ_toPadicZ (x : Star ℤ) : fromPadicZ (toPadicZ p x) = x := by
  obtain ⟨f, rfl⟩ := x.exists_rep; rfl

omit hp in
@[simp]
theorem toPadicZ_fromPadicZ (y : Star (PadicZ p)) : toPadicZ p (fromPadicZ y) = y := by
  obtain ⟨f, rfl⟩ := y.exists_rep; rfl

omit hp in
@[simp]
theorem fromPadicZ_const (a : PadicZ p) :
    fromPadicZ (↑a : Star (PadicZ p)) = Germ.const a.toInt := rfl

/-- **Section 18.4.** The extended $`p`-adic distance is
$`{}^*d_p(x, y) = |x - y|_p`. -/
theorem hdist_padicZ (y y' : Star (PadicZ p)) :
    hdist y y' = hpnormInt p (fromPadicZ y - fromPadicZ y') :=
  Germ.inductionOn₂ y y' fun _ _ => rfl

/-- **Section 18.4.** Every member of $`{}^*\mathbb Z` is $`p`-adically limited:
$`{}^*\mathbb Z^{\lim_p} = {}^*\mathbb Z`. -/
theorem limitedPt_padicZ (y : Star (PadicZ p)) : LimitedPt y :=
  ⟨PadicZ.ofInt p 0, by
    show Limited (hdist y _)
    rw [hdist_padicZ]; exact limited_hpnormInt p _⟩

/-- **Section 18.4.** Every member of $`{}^*\mathbb Z` is approachable from $`\mathbb Z`
in the $`p`-adic metric: $`x \bmod p^n` is a standard integer within $`p^{-n}` of $`x`. -/
theorem approachable_padicZ (y : Star (PadicZ p)) : Approachable y := by
  intro e he
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p he
  refine ⟨PadicZ.ofInt p (((hmod p k (fromPadicZ y)).val : ℕ) : ℤ), ?_⟩
  rw [hdist_padicZ, fromPadicZ_const, PadicZ.toInt_ofInt]
  exact (hpnormInt_sub_hmod_le p k _).trans_lt (Hyperreal.coe_lt_coe.2 hk)

/-- **Section 18.4.** Two points are $`p`-adically infinitely close exactly when
$`\theta_p` takes the same value on them. -/
theorem infClose_padicZ_iff {y y' : Star (PadicZ p)} :
    InfClose y y' ↔ theta p (fromPadicZ y) = theta p (fromPadicZ y') := by
  rw [theta_eq_theta_iff, ← hdist_padicZ]; rfl

/-- The map $`\operatorname{hal}_p(x) \mapsto \theta_p(x)` from the nonstandard hull of
$`(\mathbb Z, d_p)` to $`\mathbb Z_p`. -/
def thetaHull (h : Hull (PadicZ p)) : ℤ_[p] :=
  Quotient.liftOn h (fun y => theta p (fromPadicZ y.1)) fun _ _ hyy =>
    (infClose_padicZ_iff p).1 hyy

@[simp]
theorem thetaHull_mk (y : Star (PadicZ p)) (hy : LimitedPt y) :
    thetaHull p (Hull.mk y hy) = theta p (fromPadicZ y) := rfl

/-- **Section 18.4, preserving the metric.** The bijection
$`\operatorname{hal}_p(x) \mapsto \theta_p(x)` preserves distances. -/
theorem isometry_thetaHull : Isometry (thetaHull p) :=
  Isometry.of_dist_eq fun h k => by
    obtain ⟨y, hy, rfl⟩ := h.exists_rep
    obtain ⟨y', hy', rfl⟩ := k.exists_rep
    rw [thetaHull_mk, thetaHull_mk, Hull.dist_mk, hdist_padicZ, sh_hpnormInt, map_sub,
      dist_eq_norm]

theorem surjective_thetaHull : Function.Surjective (thetaHull p) := fun a => by
  obtain ⟨x, rfl⟩ := theta_surjective p a
  exact ⟨Hull.mk (toPadicZ p x) (limitedPt_padicZ p _), by rw [thetaHull_mk, fromPadicZ_toPadicZ]⟩

/-- **Section 18.4.** The nonstandard hull of $`(\mathbb Z, d_p)` is isometric to
$`(\mathbb Z_p, d_p)`, by $`\operatorname{hal}_p(x) \mapsto \theta_p(x)`. -/
def hullPadicZEquiv : Hull (PadicZ p) ≃ᵢ ℤ_[p] where
  toEquiv := Equiv.ofBijective (thetaHull p)
    ⟨(isometry_thetaHull p).injective, surjective_thetaHull p⟩
  isometry_toFun := isometry_thetaHull p

@[simp]
theorem hullPadicZEquiv_of (a : PadicZ p) :
    hullPadicZEquiv p (Hull.of a) = (a.toInt : ℤ_[p]) :=
  theta_const p a.toInt

/-- **Section 18.4.** The nonstandard hull of $`(\mathbb Z, d_p)` coincides with the space
of halos of approachable points. -/
theorem Hull.isApproachable_padicZ (h : Hull (PadicZ p)) : h.IsApproachable := by
  obtain ⟨y, hy, rfl⟩ := h.exists_rep
  exact approachable_padicZ p y

/-- **Section 18.4, conclusion.** $`\mathbb Z_p` is complete and is a completion of
$`(\mathbb Z, d_p)`. Completeness is deduced from Theorem 18.3.1 through the isometry with
the nonstandard hull, and density from the approachability of every hyperinteger; neither
uses the completeness of $`\mathbb Z_p` known to Mathlib. -/
theorem isCompletion_padicZ :
    IsCompletion (fun a : PadicZ p => ((a.toInt : ℤ) : ℤ_[p])) where
  isometry := Isometry.of_dist_eq fun a b => by
    rw [← hullPadicZEquiv_of, ← hullPadicZEquiv_of, (hullPadicZEquiv p).dist_eq,
      Hull.isometry_of.dist_eq]
  complete := by
    have h1 : IsComplete (Set.range (hullPadicZEquiv p)) :=
      (completeSpace_iff_isComplete_range (hullPadicZEquiv p).isometry.isUniformInducing).1
        inferInstance
    rw [(hullPadicZEquiv p).surjective.range_eq] at h1
    exact completeSpace_iff_isComplete_univ.2 h1
  denseRange := by
    rw [denseRange_iff_forall_exists_dist_lt]
    intro a e he
    obtain ⟨h, rfl⟩ := (hullPadicZEquiv p).surjective a
    obtain ⟨b, hb⟩ := Metric.mem_closure_range_iff.1
      (Hull.isApproachable_iff_mem_closure.1 (Hull.isApproachable_padicZ p h)) e he
    exact ⟨b, by rwa [← hullPadicZEquiv_of, (hullPadicZEquiv p).dist_eq]⟩

/-!
### Nearstandard hyperintegers

A hyperinteger is near to $`\mathbb Z` in the $`p`-adic metric when $`\theta_p` maps it to a
standard integer, equivalently when it has the form $`p^N q + z` with $`N` unlimited and
$`z` standard. Since $`\mathbb Z_p` has members that are not integers, there are
hyperintegers that are approachable from $`\mathbb Z` but not near to $`\mathbb Z`.
-/

/-- **Section 18.4.** The $`p`-adically nearstandard hyperintegers are the
$`\theta_p`-preimages of standard integers. -/
theorem near_padicZ_iff {y : Star (PadicZ p)} :
    Near y ↔ ∃ z : ℤ, theta p (fromPadicZ y) = (z : ℤ_[p]) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.toInt, by rw [(infClose_padicZ_iff p).1 ha, fromPadicZ_const, theta_const]⟩
  · rintro ⟨z, hz⟩
    exact ⟨PadicZ.ofInt p z, (infClose_padicZ_iff p).2 (by
      rw [hz, fromPadicZ_const, theta_const, PadicZ.toInt_ofInt])⟩

/-- **Section 18.4.** The nearstandard hyperintegers are those of the form
$`p^N q + z` with $`N` unlimited and $`z` a standard integer. -/
theorem near_padicZ_iff_exists {y : Star (PadicZ p)} :
    Near y ↔ ∃ (N : Star ℕ) (q : Star ℤ) (z : ℤ), Unlimited N ∧
      fromPadicZ y = hpow p N * q + Germ.const z := by
  rw [near_padicZ_iff]
  constructor
  · rintro ⟨z, hz⟩
    rw [← theta_const p z, theta_eq_theta_iff, infinitesimal_hpnormInt_iff_exists] at hz
    obtain ⟨N, q, hN, hq⟩ := hz
    exact ⟨N, q, z, hN, by rw [← hq, sub_add_cancel]⟩
  · rintro ⟨N, q, z, hN, hy⟩
    refine ⟨z, ?_⟩
    rw [← theta_const p z, theta_eq_theta_iff, infinitesimal_hpnormInt_iff_exists]
    exact ⟨N, q, hN, by rw [hy, add_sub_cancel_right]⟩

/-- There is a $`p`-adic integer that is not an integer: the inverse of $`1 + p`. -/
theorem exists_padicInt_not_int : ∃ a : ℤ_[p], ∀ z : ℤ, a ≠ (z : ℤ_[p]) := by
  have hunit : IsUnit ((1 + p : ℤ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => ?_)
    rw [PadicInt.norm_int_lt_one_iff_dvd] at h
    have h1 : (p : ℤ) ∣ 1 := (Int.dvd_add_left (dvd_refl (p : ℤ))).1 h
    have h2 : p ∣ 1 := by exact_mod_cast h1
    exact hp.out.one_lt.ne' (Nat.dvd_one.1 h2)
  obtain ⟨u, hu⟩ := hunit
  refine ⟨((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), fun z hz => ?_⟩
  have h1 : ((1 + p : ℤ) : ℤ_[p]) * (z : ℤ_[p]) = 1 := by
    rw [← hz, ← hu]; exact u.mul_inv
  have h2 : (1 + p : ℤ) * z = 1 := by exact_mod_cast h1
  have h3 : (1 + (p : ℤ)) ∣ 1 := Dvd.intro z h2
  have h4 := Int.le_of_dvd one_pos h3
  have h5 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  linarith

/-- **Section 18.4.** Since $`(\mathbb Z, d_p)` is incomplete, there are points of
$`{}^*\mathbb Z` that are approachable from $`\mathbb Z` but not near to $`\mathbb Z`: any
$`x` with $`\theta_p(x)` outside $`\mathbb Z`. -/
theorem exists_approachable_not_near_padicZ :
    ∃ y : Star (PadicZ p), Approachable y ∧ ¬Near y := by
  obtain ⟨a, ha⟩ := exists_padicInt_not_int p
  obtain ⟨x, rfl⟩ := theta_surjective p a
  refine ⟨toPadicZ p x, approachable_padicZ p _, fun h => ?_⟩
  obtain ⟨z, hz⟩ := (near_padicZ_iff p).1 h
  rw [fromPadicZ_toPadicZ] at hz
  exact ha z hz

/-- **Section 18.4.** The integers are not complete in the $`p`-adic metric
(Corollary 18.3.3 read in the contrapositive). -/
theorem not_completeSpace_padicZ : ¬CompleteSpace (PadicZ p) := fun _ => by
  obtain ⟨y, hy, hny⟩ := exists_approachable_not_near_padicZ p
  exact hny hy.near

end Goldblatt.Completion
