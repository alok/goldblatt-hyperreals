import Goldblatt.Ch14_Enlargements.Los

/-!
# 14 (part 4). Transfer for Terms and the Ultrapower Framework: Section 14.3

This is the fourth of five parts of Chapter 14 (the overview is on the chapter page
{lit}`Goldblatt.Ch14_Enlargements`). It completes the theorem of Łoś by treating tuples and
function values, concludes that every bounded ultrapower of a superstructure is a nonstandard
framework, and proves Exercise 14.4(2).
-/

noncomputable section

namespace Goldblatt

open ZFSet Filter
open scoped Classical

universe u v

/-!
## 14.3 Enlargements as Ultrapowers: terms and the framework

The transfer axiom of Chapter 13 speaks about all sentences of a language whose terms include
tuples $`(\tau_1, \dots, \tau_m)` and function values $`\tau(\sigma)`, and it counts an atomic
formula with an undefined term as false. So the theorem of Łoś has to be proved for such
terms, including the statement that a term is defined at the classes if and only if it is
defined at almost all indices.

The method is to express what is needed by formulas whose only terms are variables, for which
the theorem is already available from part 3. Being an ordered pair, being a function of the
universe with a given entity in its domain, and having a given value at a given argument are
all expressed by bounded formulas in the membership relation alone. For each of these formulas
one checks, inside a single universe and without any ultrafilter, that it says what it is
meant to say; this is where individuals need attention, since an individual has members that
the universe does not see. The theorem of Łoś for the formula then transports the property
between the two universes.

### Bounded formulas for pairs and function values
-/

/-- The term is a variable. -/
def Term.IsVar (t : Term.{u}) : Prop := ∃ n, t = .var n

section Semantic

variable {V P A B z : ZFSet.{u}}

/-- Inside a universe: $`z = \{A\}`. -/
def IsSingIn (V z A : ZFSet.{u}) : Prop := A ∈ z ∧ ∀ w ∈ V, w ∈ z → w = A

/-- Inside a universe: $`z = \{A, B\}`. -/
def IsDblIn (V z A B : ZFSet.{u}) : Prop := A ∈ z ∧ B ∈ z ∧ ∀ w ∈ V, w ∈ z → w = A ∨ w = B

/-- Inside a universe: $`P = (A, B)`. -/
def IsOPairIn (V P A B : ZFSet.{u}) : Prop :=
  (∃ z ∈ V, z ∈ P ∧ IsSingIn V z A) ∧ (∃ z ∈ V, z ∈ P ∧ IsDblIn V z A B) ∧
    ∀ z ∈ V, z ∈ P → IsSingIn V z A ∨ IsDblIn V z A B

/-- A member of a universe that has a member in the universe is a set
of the universe, so all its members are in the universe. -/
theorem IsUniverse.subset_of_mem {y : ZFSet.{u}} (hV : IsUniverse V) (hA : A ∈ V) (hy : y ∈ V)
    (hyA : y ∈ A) : A ⊆ V :=
  hV.subset ⟨hA, fun h => h.2 y hy hyA⟩

/-- In a universe the bounded condition for a singleton says what it should. -/
theorem isSingIn_iff (hV : IsUniverse V) (hz : z ∈ V) (hA : A ∈ V) : IsSingIn V z A ↔ z = {A} := by
  constructor
  · rintro ⟨h1, h2⟩
    have hsub := hV.subset_of_mem hz hA h1
    ext w
    rw [mem_singleton]
    exact ⟨fun hw => h2 w (hsub hw) hw, fun hw => hw ▸ h1⟩
  · rintro rfl
    exact ⟨mem_singleton.2 rfl, fun w _ hw => mem_singleton.1 hw⟩

/-- In a universe the bounded condition for an unordered pair says what it
should. -/
theorem isDblIn_iff (hV : IsUniverse V) (hz : z ∈ V) (hA : A ∈ V) : IsDblIn V z A B ↔ z = {A, B} := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hsub := hV.subset_of_mem hz hA h1
    ext w
    rw [mem_pair]
    exact ⟨fun hw => h3 w (hsub hw) hw, fun hw => by rcases hw with rfl | rfl <;> assumption⟩
  · rintro rfl
    exact ⟨by simp, by simp, fun w _ hw => mem_pair.1 hw⟩

/-- In a universe the bounded condition for an ordered pair says what it should:
for $`P, A, B` in the universe it holds exactly when $`P = (A, B)`. -/
theorem isOPairIn_iff (hV : IsUniverse V) (hP : P ∈ V) (hA : A ∈ V) (hB : B ∈ V) :
    IsOPairIn V P A B ↔ P = pair A B := by
  have hsA := (hV.isSetOf_singleton hA).1
  have hpAB := (hV.isSetOf_pair hA hB).1
  constructor
  · rintro ⟨⟨z1, hz1, hz1P, s1⟩, ⟨z2, hz2, hz2P, d2⟩, hall⟩
    have hsub := hV.subset_of_mem hP hz1 hz1P
    rw [isSingIn_iff hV hz1 hA] at s1
    rw [isDblIn_iff hV hz2 hA] at d2
    subst s1 d2
    ext y
    have : y ∈ pair A B ↔ y = {A} ∨ y = {A, B} := by simp [pair]
    rw [this]
    constructor
    · intro hy
      rcases hall y (hsub hy) hy with h | h
      · exact Or.inl ((isSingIn_iff hV (hsub hy) hA).1 h)
      · exact Or.inr ((isDblIn_iff hV (hsub hy) hA).1 h)
    · rintro (rfl | rfl) <;> assumption
  · rintro rfl
    have m1 : ({A} : ZFSet.{u}) ∈ pair A B := singleton_mem_pair
    have m2 : ({A, B} : ZFSet.{u}) ∈ pair A B := pair_mem_pair
    refine ⟨⟨_, hsA, m1, (isSingIn_iff hV hsA hA).2 rfl⟩, ⟨_, hpAB, m2, (isDblIn_iff hV hpAB hA).2 rfl⟩,
      fun z hz hzP => ?_⟩
    have : z = {A} ∨ z = {A, B} := by simpa [pair] using hzP
    rcases this with rfl | rfl
    · exact Or.inl ((isSingIn_iff hV hz hA).2 rfl)
    · exact Or.inr ((isDblIn_iff hV hz hA).2 rfl)

/-- The formula $`z = \{a\}` for variables $`z, a` with auxiliary bound variable $`w`. -/
def singF (z a w : ℕ) : Formula.{u} :=
  .conj (.elem (.var a) (.var z)) (.all w (.var z) (.equal (.var w) (.var a)))

/-- The formula $`z = \{a, b\}` with auxiliary bound variable $`w`. -/
def dblF (z a b w : ℕ) : Formula.{u} :=
  .conj (.elem (.var a) (.var z)) (.conj (.elem (.var b) (.var z))
    (.all w (.var z) (.disj (.equal (.var w) (.var a)) (.equal (.var w) (.var b)))))

/-- The formula $`p = (a, b)` for variables $`p, a, b`; the bound variables are
$`p + a + b + 1` and $`p + a + b + 2`. -/
def opairF (p a b : ℕ) : Formula.{u} :=
  .conj (.ex (p + a + b + 1) (.var p) (singF (p + a + b + 1) a (p + a + b + 2)))
    (.conj (.ex (p + a + b + 1) (.var p) (dblF (p + a + b + 1) a b (p + a + b + 2)))
      (.all (p + a + b + 1) (.var p) (.disj (singF (p + a + b + 1) a (p + a + b + 2))
        (dblF (p + a + b + 1) a b (p + a + b + 2)))))

/-- Truth of the singleton formula. -/
theorem sat_singF {z a w : ℕ} (v : ℕ → ZFSet.{u}) (haw : a ≠ w) :
    Sat V v (singF z a w) ↔ IsSingIn V (v z) (v a) := by
  simp only [singF, Sat, Term.Defined, Term.val, true_and, forall_true_left,
    Function.update_self, Function.update_of_ne haw, IsSingIn]

/-- Truth of the unordered pair formula. -/
theorem sat_dblF {z a b w : ℕ} (v : ℕ → ZFSet.{u}) (haw : a ≠ w) (hbw : b ≠ w) :
    Sat V v (dblF z a b w) ↔ IsDblIn V (v z) (v a) (v b) := by
  simp only [dblF, Sat, Term.Defined, Term.val, true_and, forall_true_left,
    Function.update_self, Function.update_of_ne haw, Function.update_of_ne hbw, IsDblIn]

/-- Truth of the ordered pair formula. -/
theorem sat_opairF (p a b : ℕ) (v : ℕ → ZFSet.{u}) :
    Sat V v (opairF p a b) ↔ IsOPairIn V (v p) (v a) (v b) := by
  have h1 : a ≠ p + a + b + 2 := by omega
  have h2 : b ≠ p + a + b + 2 := by omega
  have h3 : a ≠ p + a + b + 1 := by omega
  have h4 : b ≠ p + a + b + 1 := by omega
  simp only [opairF, Sat, Term.Defined, Term.val, true_and, forall_true_left, sat_singF _ h1,
    sat_dblF _ h1 h2, Function.update_self, Function.update_of_ne h3, Function.update_of_ne h4,
    IsOPairIn]

/-- The terms of the ordered pair formula are variables. -/
theorem termsSat_opairF (p a b : ℕ) : (opairF p a b : Formula.{u}).TermsSat Term.IsVar := by
  simp [opairF, singF, dblF, Formula.TermsSat, Term.IsVar]

/-- The ordered pair formula has no constants and is its own transform. -/
theorem star_opairF (s : ZFSet.{u} → ZFSet.{u}) (p a b : ℕ) :
    (opairF p a b).star s = opairF p a b := rfl

/-- The formula saying that the variable $`0` is a function of the universe with the variable
$`1` in its domain. -/
def appDefF : Formula.{u} :=
  .conj
    (.all 2 (.var 0) (.ex 3 (.var 2) (.ex 4 (.var 3) (.ex 5 (.var 2) (.ex 6 (.var 5)
      (opairF 2 4 6))))))
    (.conj
      (.all 2 (.var 0) (.all 3 (.var 0) (.all 4 (.var 2) (.all 5 (.var 4) (.all 6 (.var 2)
        (.all 7 (.var 6) (.all 8 (.var 3) (.all 9 (.var 8)
          (.imp (.conj (opairF 2 5 7) (opairF 3 5 9)) (.equal (.var 7) (.var 9)))))))))))
      (.ex 2 (.var 0) (.ex 3 (.var 2) (.ex 4 (.var 3) (opairF 2 1 4)))))

/-- In a universe $`\mathbb V`, for $`f, x \in \mathbb V`, the formula
{lit}`appDefF` is true exactly when the three clauses of definedness of the term $`f(x)` hold:
$`f` is a function, it is a set of pairs of members of $`\mathbb V`, and $`x` is in its domain.
So definedness of a function value is expressed by a bounded formula whose terms are
variables. -/
theorem sat_appDefF (hV : IsUniverse V) (v : ℕ → ZFSet.{u}) (h0 : v 0 ∈ V) (h1 : v 1 ∈ V) :
    Sat V v appDefF ↔ IsFunction (v 0) ∧ RelIn V (v 0) ∧ v 1 ∈ dom (v 0) := by
  simp only [appDefF, Sat, Term.Defined, Term.val, true_and, forall_true_left, sat_opairF,
    Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true,
    OfNat.zero_ne_ofNat, OfNat.one_ne_ofNat, Nat.reduceEqDiff]
  have hs : ∀ {a : ZFSet.{u}}, a ∈ V → ({a} : ZFSet.{u}) ∈ V := fun ha =>
    (hV.isSetOf_singleton ha).1
  have hp : ∀ {a b : ZFSet.{u}}, a ∈ V → b ∈ V → ({a, b} : ZFSet.{u}) ∈ V := fun ha hb =>
    (hV.isSetOf_pair ha hb).1
  constructor
  · rintro ⟨c1, c2, p, hpV, hpF, z, hzV, hzp, b, hbV, hbz, hop⟩
    have hsub : v 0 ⊆ V := hV.subset_of_mem h0 hpV hpF
    have hrel : RelIn V (v 0) := fun q hq => by
      obtain ⟨z, hz, hzq, a, ha, haz, z', hz', hz'q, b, hb, hbz', hop⟩ := c1 q (hsub hq) hq
      exact ⟨a, ha, b, hb, (isOPairIn_iff hV (hsub hq) ha hb).1 hop⟩
    refine ⟨⟨hrel.isRel, fun a b c hab hac => ?_⟩, hrel, mem_dom.2 ⟨b, ?_⟩⟩
    · obtain ⟨a1, ha1, b1, hb1, e1⟩ := hrel _ hab
      obtain ⟨a2, ha2, c', hc', e2⟩ := hrel _ hac
      obtain ⟨rfl, rfl⟩ := pair_inj.1 e1
      obtain ⟨-, rfl⟩ := pair_inj.1 e2
      exact c2 _ (hsub hab) hab _ (hsub hac) hac {a} (hs ha1) singleton_mem_pair a ha1
        (mem_singleton.2 rfl) {a, b} (hp ha1 hb1) pair_mem_pair b hb1 (by simp)
        {a, c} (hp ha1 hc') pair_mem_pair c hc' (by simp)
        ⟨(isOPairIn_iff hV (hsub hab) ha1 hb1).2 rfl, (isOPairIn_iff hV (hsub hac) ha1 hc').2 rfl⟩
    · rw [← (isOPairIn_iff hV hpV h1 hbV).1 hop]
      exact hpF
  · rintro ⟨hfun, hrel, hdom⟩
    refine ⟨fun q hqV hq => ?_, fun p hp' hpF q hq hqF z hz hzp a ha haz z' hz' hz'p b hb hbz'
      z'' hz'' hz''q c hc hcz'' ⟨o1, o2⟩ => ?_, ?_⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := hrel q hq
      exact ⟨{a}, hs ha, singleton_mem_pair, a, ha, mem_singleton.2 rfl, {a, b}, hp ha hb,
        pair_mem_pair, b, hb, by simp, (isOPairIn_iff hV hqV ha hb).2 rfl⟩
    · rw [isOPairIn_iff hV hp' ha hb] at o1
      rw [isOPairIn_iff hV hq ha hc] at o2
      subst o1 o2
      exact hfun.2 a b c hpF hqF
    · obtain ⟨b, hb⟩ := mem_dom.1 hdom
      obtain ⟨a', ha', b', hb', e⟩ := hrel _ hb
      obtain ⟨rfl, rfl⟩ := pair_inj.1 e
      exact ⟨_, (hV.isSetOf_opair ha' hb').1, hb, {v 1, b}, hp ha' hb', pair_mem_pair, b, hb',
        by simp, (isOPairIn_iff hV (hV.isSetOf_opair ha' hb').1 ha' hb').2 rfl⟩

/-- The terms of {lit}`appDefF` are variables. -/
theorem termsSat_appDefF : (appDefF : Formula.{u}).TermsSat Term.IsVar := by
  simp [appDefF, opairF, singF, dblF, Formula.TermsSat, Term.IsVar]

/-- {lit}`appDefF` has no constants and is its own transform. -/
theorem star_appDefF (s : ZFSet.{u} → ZFSet.{u}) : appDefF.star s = appDefF := rfl

/-- The formula saying that the pair of the variables $`1` and $`2` belongs to the variable
$`0`. -/
def appValF : Formula.{u} := .ex 3 (.var 0) (opairF 3 1 2)

/-- In a universe the formula {lit}`appValF` is true exactly when the pair of the
second and third variable belongs to the first. -/
theorem sat_appValF (hV : IsUniverse V) (v : ℕ → ZFSet.{u}) (h1 : v 1 ∈ V) (h2 : v 2 ∈ V) :
    Sat V v appValF ↔ pair (v 1) (v 2) ∈ v 0 := by
  simp only [appValF, Sat, Term.Defined, Term.val, true_and, sat_opairF,
    Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true,
    OfNat.one_ne_ofNat, Nat.reduceEqDiff]
  constructor
  · rintro ⟨p, hpV, hp, hop⟩
    rw [← (isOPairIn_iff hV hpV h1 h2).1 hop]
    exact hp
  · intro h
    have hpV := (hV.isSetOf_opair h1 h2).1
    exact ⟨_, hpV, h, (isOPairIn_iff hV hpV h1 h2).2 rfl⟩

/-- The terms of {lit}`appValF` are variables. -/
theorem termsSat_appValF : (appValF : Formula.{u}).TermsSat Term.IsVar := by
  simp [appValF, opairF, singF, dblF, Formula.TermsSat, Term.IsVar]

/-- {lit}`appValF` has no constants and is its own transform. -/
theorem star_appValF (s : ZFSet.{u} → ZFSet.{u}) : appValF.star s = appValF := rfl

/-- The members of the numeral $`k` are the numerals $`j` with $`j < k`. -/
theorem mem_num_iff {k : ℕ} {y : ZFSet.{u}} : y ∈ num k ↔ ∃ j < k, y = num j := by
  induction k with
  | zero => simp [num]
  | succ k ih =>
    rw [num, mem_insert_iff, ih]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨k, Nat.lt_succ_self k, rfl⟩
      · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
      · exact Or.inr ⟨j, h, rfl⟩
      · exact Or.inl rfl

end Semantic

/-!
### The collapse commutes with pairs, tuples and function values
-/

namespace BoundedUltrapower

variable {I : Type v} [Small.{u} I] {𝓕 : Ultrafilter I} {X : ZFSet.{u}}

/-- **Section 14.3, Łoś's theorem for formulas whose terms are variables.** -/
theorem los_vars (hX : IsBaseSet X) (φ : Formula.{u}) (h : φ.TermsSat Term.IsVar)
    (fs : ℕ → I → ZFSet.{u}) (hfs : ∀ x, Bdd 𝓕 X (fs x)) :
    Sat (superstructure (base 𝓕 X)) (fun y => col 𝓕 hX (fs y)) (φ.star (star 𝓕 hX)) ↔
      ∀ᶠ i in 𝓕, Sat (superstructure X) (fun y => fs y i) φ :=
  los_of_terms hX Term.IsVar (fun _ ⟨n, hn⟩ => hn ▸ termLos_var hX n) φ h fs hfs

/-- An assignment of three functions to the variables $`0, 1, 2`. -/
def env3 (a b c : I → ZFSet.{u}) : ℕ → I → ZFSet.{u}
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => fun _ => ∅

omit [Small.{u} I] in
/-- An assignment made from three functions of bounded rank consists of functions of
bounded rank. -/
theorem bdd_env3 (hX : IsBaseSet X) {a b c : I → ZFSet.{u}} (ha : Bdd 𝓕 X a) (hb : Bdd 𝓕 X b)
    (hc : Bdd 𝓕 X c) : ∀ x, Bdd 𝓕 X (env3 a b c x)
  | 0 => ha
  | 1 => hb
  | 2 => hc
  | _ + 3 => bdd_const (isUniverseOver_superstructure hX).toIsUniverse.empty_mem

/-- The ordered pair of two members of $`\mathbb U_n(X)` belongs to
$`\mathbb U_{n+2}(X)`. -/
theorem opair_mem_cumPow {n : ℕ} {a b : ZFSet.{u}} (ha : a ∈ cumPow X n) (hb : b ∈ cumPow X n) :
    pair a b ∈ cumPow X (n + 2) := by
  have h1 : ({a} : ZFSet.{u}) ∈ cumPow X (n + 1) := by
    simpa using pair_mem_cumPow_succ ha ha
  exact pair_mem_cumPow_succ h1 (pair_mem_cumPow_succ ha hb)

omit [Small.{u} I] in
/-- The pointwise ordered pair of two functions of bounded rank is of bounded
rank. -/
theorem bdd_opair {a b : I → ZFSet.{u}} (ha : Bdd 𝓕 X a) (hb : Bdd 𝓕 X b) :
    Bdd 𝓕 X fun i => pair (a i) (b i) := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  refine ⟨max m n + 2, ?_⟩
  filter_upwards [hm, hn] with i h1 h2
  exact opair_mem_cumPow (cumPow_mono (le_max_left m n) h1) (cumPow_mono (le_max_right m n) h2)

/-- **Exercise 14.4(1), pairs.** The collapse commutes with ordered pairs:
$`[i \mapsto (a(i), b(i))] = ([a], [b])`. This is Łoś's theorem for the formula
$`p = (a, b)`. -/
theorem col_opair (hX : IsBaseSet X) {a b : I → ZFSet.{u}} (ha : Bdd 𝓕 X a) (hb : Bdd 𝓕 X b) :
    col 𝓕 hX (fun i => pair (a i) (b i)) = pair (col 𝓕 hX a) (col 𝓕 hX b) := by
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  have hW' := (isUniverseOver_superstructure (isBaseSet_base (𝓕 := 𝓕) hX)).toIsUniverse
  have hP := bdd_opair ha hb
  have key := los_vars hX (opairF 0 1 2) (termsSat_opairF 0 1 2)
    (env3 (fun i => pair (a i) (b i)) a b) (bdd_env3 hX hP ha hb)
  rw [star_opairF, sat_opairF] at key
  refine (isOPairIn_iff hW' (col_mem hX hP) (col_mem hX ha) (col_mem hX hb)).1 (key.2 ?_)
  filter_upwards [ha.eventually_mem, hb.eventually_mem] with i h1 h2
  exact (sat_opairF 0 1 2 _).2 ((isOPairIn_iff hW (hW.isSetOf_opair h1 h2).1 h1 h2).2 rfl)

/-- **Exercise 14.4(1), numerals.** The numerals that index tuples are fixed by
the transfer map. -/
theorem col_const_num (hX : IsBaseSet X) (k : ℕ) : col 𝓕 hX (fun _ => num k) = num k := by
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hA : ¬ Atomic 𝓕 X (fun _ : I => (num k : ZFSet.{u})) := fun h => by
      obtain ⟨_, hi⟩ := h.exists
      exact (hW.isSetOf_num k).2 (hX _ hi)
    ext y
    rw [mem_col hX hA, mem_num_iff]
    constructor
    · rintro ⟨f, hE, rfl⟩
      have h1 : ∀ᶠ i in 𝓕, ∃ j : Fin k, f i = num j := hE.2.2.mono fun i hi => by
        obtain ⟨j, hj, e⟩ := mem_num_iff.1 hi
        exact ⟨⟨j, hj⟩, e⟩
      obtain ⟨j, hj⟩ := Ultrafilter.eventually_exists_iff.1 h1
      exact ⟨j, j.2, by rw [col_congr hX hj, ih j j.2]⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨fun _ => num j, ⟨bdd_const (hW.isSetOf_num j).1, bdd_const (hW.isSetOf_num k).1,
        Eventually.of_forall fun _ => num_mem_num_of_lt hj⟩, ih j hj⟩

omit [Small.{u} I] in
/-- The pointwise tuple of finitely many functions of bounded rank is of bounded
rank. -/
theorem bdd_tuple (hX : IsBaseSet X) (k : ℕ) (g : Fin k → I → ZFSet.{u})
    (hg : ∀ j, Bdd 𝓕 X (g j)) : Bdd 𝓕 X fun i => tuple k fun j => g j i := by
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  by_cases hk : k = 2
  · subst hk
    simp only [tuple_two]
    exact bdd_opair (hg 0) (hg 1)
  · choose n hn using hg
    choose m hm using fun j : Fin k => mem_superstructure.1 (hW.isSetOf_num (j + 1)).1
    refine ⟨Finset.univ.sup (fun j => max (n j) (m j)) + 3, ?_⟩
    filter_upwards [eventually_all.2 hn] with i hi
    refine mem_cumPow_succ_of_subset fun p hp => ?_
    obtain ⟨j, rfl⟩ := (mem_tuple hk).1 hp
    have hle : max (n j) (m j) ≤ Finset.univ.sup (fun j => max (n j) (m j)) :=
      Finset.le_sup (f := fun j => max (n j) (m j)) (Finset.mem_univ j)
    exact opair_mem_cumPow (cumPow_mono ((le_max_right _ _).trans hle) (hm j))
      (cumPow_mono ((le_max_left _ _).trans hle) (hi j))

/-- **Exercise 14.4(1), tuples.** The collapse commutes with tuples:
$`[i \mapsto (g_1(i), \dots, g_k(i))] = ([g_1], \dots, [g_k])`. -/
theorem col_tuple (hX : IsBaseSet X) (k : ℕ) (g : Fin k → I → ZFSet.{u})
    (hg : ∀ j, Bdd 𝓕 X (g j)) :
    col 𝓕 hX (fun i => tuple k fun j => g j i) = tuple k fun j => col 𝓕 hX (g j) := by
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  by_cases hk : k = 2
  · subst hk
    simp only [tuple_two]
    exact col_opair hX (hg 0) (hg 1)
  · have hGb := bdd_tuple hX k g hg
    have hgW : ∀ᶠ i in 𝓕, ∀ j, g j i ∈ superstructure X :=
      eventually_all.2 fun j => (hg j).eventually_mem
    have hA : ¬ Atomic 𝓕 X (fun i => tuple k fun j => g j i) := fun h => by
      obtain ⟨i, h1, h2⟩ := (h.and hgW).exists
      exact (hW.isSetOf_tuple k _ h2).2 (hX _ h1)
    have hnum : ∀ j : ℕ, Bdd 𝓕 X (fun _ : I => (num j : ZFSet.{u})) := fun j =>
      bdd_const (hW.isSetOf_num j).1
    ext y
    rw [mem_col hX hA, mem_tuple hk]
    constructor
    · rintro ⟨f, hE, rfl⟩
      have h1 : ∀ᶠ i in 𝓕, ∃ j : Fin k, f i = pair (num (j + 1)) (g j i) :=
        hE.2.2.mono fun i hi => (mem_tuple hk).1 hi
      obtain ⟨j, hj⟩ := Ultrafilter.eventually_exists_iff.1 h1
      exact ⟨j, by rw [col_congr hX hj, col_opair hX (hnum _) (hg j), col_const_num]⟩
    · rintro ⟨j, rfl⟩
      refine ⟨fun i => pair (num (j + 1)) (g j i), ⟨bdd_opair (hnum _) (hg j), hGb,
        Eventually.of_forall fun i => (mem_tuple hk).2 ⟨j, rfl⟩⟩, ?_⟩
      rw [col_opair hX (hnum _) (hg j), col_const_num]

/-- **Exercise 14.4(1), definedness of function values.** For $`F, h \in Z`: the
entity $`[F]` is a function of $`\mathbb U(Y)` with $`[h]` in its domain if and only if for
almost all $`i` the entity $`F(i)` is a function of $`\mathbb U(X)` with $`h(i)` in its domain.
This is what the transfer axiom of Chapter 13 requires beyond the book's transfer principle
for defined sentences. -/
theorem col_appDef (hX : IsBaseSet X) {gf gx : I → ZFSet.{u}} (hgf : Bdd 𝓕 X gf)
    (hgx : Bdd 𝓕 X gx) :
    (IsFunction (col 𝓕 hX gf) ∧ RelIn (superstructure (base 𝓕 X)) (col 𝓕 hX gf) ∧
        col 𝓕 hX gx ∈ dom (col 𝓕 hX gf)) ↔
      ∀ᶠ i in 𝓕, IsFunction (gf i) ∧ RelIn (superstructure X) (gf i) ∧ gx i ∈ dom (gf i) := by
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  have hW' := (isUniverseOver_superstructure (isBaseSet_base (𝓕 := 𝓕) hX)).toIsUniverse
  have h0 : Bdd 𝓕 X (fun _ : I => (∅ : ZFSet.{u})) := bdd_const hW.empty_mem
  have key := los_vars hX appDefF termsSat_appDefF (env3 gf gx fun _ => ∅)
    (bdd_env3 hX hgf hgx h0)
  rw [star_appDefF] at key
  refine Iff.trans (sat_appDefF hW' (fun y => col 𝓕 hX (env3 gf gx (fun _ => ∅) y))
    (col_mem hX hgf) (col_mem hX hgx)).symm (key.trans (eventually_congr ?_))
  filter_upwards [hgf.eventually_mem, hgx.eventually_mem] with i h1 h2
  exact sat_appDefF hW (fun y => env3 gf gx (fun _ => ∅) y i) h1 h2

/-- **Exercise 14.4(2).** For $`F, h, k \in Z`,
$$`([h], [k]) \in [F] \iff \{i : (h(i), k(i)) \in F(i)\} \in \mathcal F.` -/
theorem col_appVal (hX : IsBaseSet X) {gf gx g : I → ZFSet.{u}} (hgf : Bdd 𝓕 X gf)
    (hgx : Bdd 𝓕 X gx) (hg : Bdd 𝓕 X g) :
    pair (col 𝓕 hX gx) (col 𝓕 hX g) ∈ col 𝓕 hX gf ↔ ∀ᶠ i in 𝓕, pair (gx i) (g i) ∈ gf i := by
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  have hW' := (isUniverseOver_superstructure (isBaseSet_base (𝓕 := 𝓕) hX)).toIsUniverse
  have key := los_vars hX appValF termsSat_appValF (env3 gf gx g) (bdd_env3 hX hgf hgx hg)
  rw [star_appValF] at key
  refine Iff.trans (sat_appValF hW' (fun y => col 𝓕 hX (env3 gf gx g y))
    (col_mem hX hgx) (col_mem hX hg)).symm (key.trans (eventually_congr ?_))
  filter_upwards [hgx.eventually_mem, hg.eventually_mem] with i h1 h2
  exact sat_appValF hW (fun y => env3 gf gx g y i) h1 h2

/-- A member of a member of $`\mathbb U_n(X)` that belongs to the
superstructure lies in $`\mathbb U_n(X)`. -/
theorem mem_cumPow_of_mem' (hX : IsBaseSet X) {n : ℕ} {y z : ZFSet.{u}} (hy : y ∈ cumPow X n)
    (hz : z ∈ y) (hzW : z ∈ superstructure X) : z ∈ cumPow X n :=
  mem_cumPow_of_mem hX (cumPow_subset_succ n hy) hz hzW

/-!
### Łoś's theorem and the framework
-/

/-- **Section 14.3, Łoś's theorem for terms.** Every term whose constants
belong to $`\mathbb U(X)` satisfies Łoś's theorem for terms, including the statement about
definedness. The proof is by induction on the term, using the theorem for formulas whose terms
are variables to handle tuples and function values. -/
theorem termLos_of_admissible (hX : IsBaseSet X) :
    ∀ t : Term.{u}, t.Admissible (superstructure X) Set.univ → TermLos 𝓕 hX t := by
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  intro t
  induction t with
  | var n => exact fun _ => termLos_var hX n
  | const a => exact fun h => termLos_const hX h
  | tuple m ts ih =>
    intro hadm fs hfs
    have H := fun j => ih j (hadm j) fs hfs
    constructor
    · simp only [Term.star, Term.Defined]
      rw [eventually_all]
      exact forall_congr' fun j => (H j).1
    · intro hev
      have hev' : ∀ j, ∀ᶠ i in 𝓕, (ts j).Defined (superstructure X) fun x => fs x i :=
        eventually_all.1 hev
      choose g hg a1 a2 using fun j => (H j).2 (hev' j)
      refine ⟨fun i => tuple (m + 2) fun j => g j i, bdd_tuple hX _ g hg, ?_, ?_⟩
      · filter_upwards [eventually_all.2 a1] with i hi
        simp only [Term.val]
        congr 1
        funext j
        exact hi j
      · simp only [Term.star, Term.val]
        rw [col_tuple hX _ g hg]
        congr 1
        funext j
        exact a2 j
  | app f x ihf ihx =>
    intro hadm fs hfs
    obtain ⟨hdf, hvf⟩ := ihf hadm.1 fs hfs
    obtain ⟨hdx, hvx⟩ := ihx hadm.2 fs hfs
    constructor
    · simp only [Term.star, Term.Defined]
      constructor
      · rintro ⟨d1, d2, c⟩
        have e1 := hdf.1 d1
        have e2 := hdx.1 d2
        obtain ⟨gf, hgf, a1, a2⟩ := hvf e1
        obtain ⟨gx, hgx, b1, b2⟩ := hvx e2
        rw [a2, b2] at c
        filter_upwards [e1, e2, a1, b1, (col_appDef hX hgf hgx).1 c] with i c1 c2 c3 c4 c5
        exact ⟨c1, c2, by rw [← c3, ← c4]; exact c5⟩
      · intro hev
        have e1 := hev.mono fun i hi => hi.1
        have e2 := hev.mono fun i hi => hi.2.1
        obtain ⟨gf, hgf, a1, a2⟩ := hvf e1
        obtain ⟨gx, hgx, b1, b2⟩ := hvx e2
        refine ⟨hdf.2 e1, hdx.2 e2, ?_⟩
        rw [a2, b2]
        refine (col_appDef hX hgf hgx).2 ?_
        filter_upwards [hev, a1, b1] with i c1 c2 c3
        rw [c2, c3]
        exact c1.2.2
    · intro hev
      simp only [Term.Defined] at hev
      have e1 := hev.mono fun i hi => hi.1
      have e2 := hev.mono fun i hi => hi.2.1
      obtain ⟨gf, hgf, a1, a2⟩ := hvf e1
      obtain ⟨gx, hgx, b1, b2⟩ := hvx e2
      have hc : ∀ᶠ i in 𝓕, IsFunction (gf i) ∧ RelIn (superstructure X) (gf i) ∧
          gx i ∈ dom (gf i) := by
        filter_upwards [hev, a1, b1] with i c1 c2 c3
        rw [c2, c3]
        exact c1.2.2
      have hmem : ∀ᶠ i in 𝓕, pair (gx i) (app (gf i) (gx i)) ∈ gf i :=
        hc.mono fun i hi => hi.1.pair_app_mem hi.2.2
      have hgW : ∀ᶠ i in 𝓕, app (gf i) (gx i) ∈ superstructure X := by
        filter_upwards [hc, hmem] with i h1 h2
        obtain ⟨a, -, b, hb, e⟩ := h1.2.1 _ h2
        rw [(pair_inj.1 e).2]
        exact hb
      have hgb : Bdd 𝓕 X fun i => app (gf i) (gx i) := by
        obtain ⟨n, hn⟩ := hgf
        refine ⟨n, ?_⟩
        filter_upwards [hn, hmem, hgW, hgx.eventually_mem] with i h1 h2 h3 h4
        have p1 := mem_cumPow_of_mem' hX h1 h2 (hW.isSetOf_opair h4 h3).1
        have p2 := mem_cumPow_of_mem' hX p1 pair_mem_pair (hW.isSetOf_pair h4 h3).1
        exact mem_cumPow_of_mem' hX p2 (by simp) h3
      refine ⟨fun i => app (gf i) (gx i), hgb, ?_, ?_⟩
      · filter_upwards [a1, b1] with i c1 c2
        simp only [Term.val]
        rw [c1, c2]
      · simp only [Term.star, Term.val]
        rw [a2, b2]
        exact ((col_appDef hX hgf hgx).2 hc).1.app_eq ((col_appVal hX hgf hgx hgb).2 hmem)

/-- **Section 14.3, Łoś's theorem.** Truth in the collapsed ultrapower is truth at almost
all indices. Let $`\varphi` be a formula of the language of $`\mathbb U(X)` and assign to its
free variables functions $`f_1, \dots, f_p` of bounded rank. Then
$$`\mathbb U(Y) \models {}^*\varphi([f_1], \dots, [f_p]) \iff
\{i \in I : \mathbb U(X) \models \varphi(f_1(i), \dots, f_p(i))\} \in \mathcal F.`
In the Lean statement an assignment gives a function to every variable, and admissibility of
$`\varphi` says that its constants name members of $`\mathbb U(X)`. The theorem is proved for all formulas of the deep embedding of Chapter 13, in which an atomic
formula with an undefined term is false. So it includes the statement that definedness of terms
is preserved, which the book's version for defined sentences does not need. -/
theorem los (hX : IsBaseSet X) (φ : Formula.{u}) {b : Set ℕ}
    (hφ : φ.Admissible (superstructure X) b) (fs : ℕ → I → ZFSet.{u})
    (hfs : ∀ x, Bdd 𝓕 X (fs x)) :
    Sat (superstructure (base 𝓕 X)) (fun y => col 𝓕 hX (fs y)) (φ.star (star 𝓕 hX)) ↔
      ∀ᶠ i in 𝓕, Sat (superstructure X) (fun y => fs y i) φ :=
  los_of_terms hX _ (fun t ht => termLos_of_admissible hX t ht) φ
    (Formula.termsSat_of_admissible hφ) fs hfs

variable (𝓕) in
/-- **Section 14.3 and Exercise 14.4(1), the ultrapower framework.** For an
ultrafilter $`\mathcal F` on a small index set $`I` and a set $`X` of individuals, the bounded
ultrapower of $`\mathbb U(X)` is a nonstandard framework for $`X`: the standard universe is
$`\mathbb U(X)`, the target universe is $`\mathbb U(Y)` with $`Y = {}^*X`, and the transfer map
is $`a \mapsto [a^I]`. The transfer principle is Łoś's theorem at constant functions. No
condition on the ultrafilter is needed; for a principal ultrafilter the framework is a copy of
the trivial one. -/
def framework (hX : IsBaseSet X) : NonstandardFramework.{u} where
  U := superstructure X
  X := X
  U' := superstructure (base 𝓕 X)
  star := star 𝓕 hX
  isUniverseOver := isUniverseOver_superstructure hX
  isUniverse' := (isUniverseOver_superstructure (isBaseSet_base hX)).toIsUniverse
  star_mem := fun _ ha => col_mem hX (bdd_const ha)
  star_individual := fun _ ha => col_const_of_mem hX ha
  star_empty := col_const_empty hX
  transfer := fun φ hφ => by
    have h0 : Bdd 𝓕 X (fun _ : I => (∅ : ZFSet.{u})) :=
      bdd_const (isUniverseOver_superstructure hX).toIsUniverse.empty_mem
    have key := los hX φ hφ (fun _ _ => ∅) (fun _ => h0)
    simp only [col_const_empty, eventually_const] at key
    exact key.symm

/-- **Section 14.3.** For a set $`a \in \mathbb U(X)`,
$$`{}^*a = \{[f] : f \in Z,\ \{i : f(i) \in a\} \in \mathcal F\}.` -/
theorem mem_star_iff (hX : IsBaseSet X) {a y : ZFSet.{u}}
    (ha : IsSetOf (superstructure X) a) :
    y ∈ star 𝓕 hX a ↔ ∃ f, Bdd 𝓕 X f ∧ (∀ᶠ i in 𝓕, f i ∈ a) ∧ col 𝓕 hX f = y := by
  have hA : ¬ Atomic 𝓕 X (fun _ : I => a) := fun h => by
    obtain ⟨_, hi⟩ := h.exists
    exact ha.2 (hX _ hi)
  rw [star, mem_col hX hA]
  exact ⟨fun ⟨f, hE, h⟩ => ⟨f, hE.1, hE.2.2, h⟩, fun ⟨f, h1, h2, h3⟩ =>
    ⟨f, ⟨h1, bdd_const ha.1, h2⟩, h3⟩⟩

/-- **Section 14.3.**
$`{}^*\mathbb U_n(X) = \{[f] : \{i : f(i) \in \mathbb U_n(X)\} \in \mathcal F\}`, the
collapses of the functions of rank at most $`n`. -/
theorem mem_star_cumPow_iff (hX : IsBaseSet X) (n : ℕ) {y : ZFSet.{u}} :
    y ∈ star 𝓕 hX (cumPow X n) ↔ ∃ f, (∀ᶠ i in 𝓕, f i ∈ cumPow X n) ∧ col 𝓕 hX f = y := by
  rw [mem_star_iff hX (isSetOf_of_subset (cumPow_mem_superstructure n)
    (cumPow_subset_superstructure n))]
  exact ⟨fun ⟨f, _, h2, h3⟩ => ⟨f, h2, h3⟩, fun ⟨f, h2, h3⟩ => ⟨f, ⟨n, h2⟩, h2, h3⟩⟩

omit [Small.{u} I] in
/-- **Section 14.3, rank of a function.** A function $`f \in Z` has a
well-defined rank: there is exactly one $`k` such that $`\{i : f(i) \text{ has rank } k\}`
belongs to the ultrafilter. -/
theorem existsUnique_rank {f : I → ZFSet.{u}} (hf : Bdd 𝓕 X f) :
    ∃! k, ∀ᶠ i in 𝓕, rank X (f i) = k := by
  obtain ⟨n, hn⟩ := hf
  have h1 : ∀ᶠ i in 𝓕, ∃ k : Fin (n + 1), rank X (f i) = k := hn.mono fun i hi =>
    ⟨⟨rank X (f i), Nat.lt_succ_of_le (rank_le_of_mem_cumPow hi)⟩, rfl⟩
  obtain ⟨k, hk⟩ := Ultrafilter.eventually_exists_iff.1 h1
  refine ⟨k, hk, fun k' hk' => ?_⟩
  obtain ⟨i, h2, h3⟩ := (hk'.and hk).exists
  exact h2.symm.trans h3

omit [Small.{u} I] in
/-- **Section 14.3, rank of a function.** For $`f \in Z`, the rank {lit}`rk` of $`f` is at
most $`n` exactly when $`f \in Z_n`. -/
theorem rk_le_iff {f : I → ZFSet.{u}} (hf : Bdd 𝓕 X f) {n : ℕ} :
    rk 𝓕 X f ≤ n ↔ ∀ᶠ i in 𝓕, f i ∈ cumPow X n :=
  ⟨fun h => (eventually_mem_cumPow_rk hf).mono fun _ hi => cumPow_mono h hi,
    fun h => Nat.sInf_le h⟩

omit [Small.{u} I] in
/-- **Section 14.3, rank of a function.** The two descriptions of the rank of $`f \in Z` agree:
the least $`n` with $`f \in Z_n` ({lit}`rk`) is the number $`k` for which
$`\{i : f(i) \text{ has rank } k\}` belongs to the ultrafilter. -/
theorem eventually_rank_eq_rk {f : I → ZFSet.{u}} (hf : Bdd 𝓕 X f) :
    ∀ᶠ i in 𝓕, rank X (f i) = rk 𝓕 X f := by
  obtain ⟨k, hk, -⟩ := existsUnique_rank hf
  have h1 : rk 𝓕 X f ≤ k := (rk_le_iff hf).2 (by
    filter_upwards [hk, hf.eventually_mem] with i h2 h3
    exact (mem_cumPow_iff_rank_le h3).2 h2.le)
  have h2 : k ≤ rk 𝓕 X f := by
    obtain ⟨i, h3, h4⟩ := (hk.and (eventually_mem_cumPow_rk hf)).exists
    exact h3 ▸ rank_le_of_mem_cumPow h4
  exact hk.mono fun i hi => hi.trans (le_antisymm h2 h1)

omit [Small.{u} I] in
/-- **Section 14.3, rank of a function.** The functions of rank $`n + 1` are those in
$`Z_{n+1} - Z_n`. -/
theorem rk_eq_succ_iff {f : I → ZFSet.{u}} {n : ℕ} :
    (Bdd 𝓕 X f ∧ rk 𝓕 X f = n + 1) ↔
      (∀ᶠ i in 𝓕, f i ∈ cumPow X (n + 1)) ∧ ¬ ∀ᶠ i in 𝓕, f i ∈ cumPow X n := by
  constructor
  · rintro ⟨hf, h⟩
    exact ⟨(rk_le_iff hf).1 h.le, fun h' => by have := (rk_le_iff hf).2 h'; omega⟩
  · rintro ⟨h1, h2⟩
    have hf : Bdd 𝓕 X f := ⟨n + 1, h1⟩
    have h3 := (rk_le_iff hf).2 h1
    have h4 : ¬ rk 𝓕 X f ≤ n := fun h => h2 ((rk_le_iff hf).1 h)
    exact ⟨hf, by omega⟩

omit [Small.{u} I] in
/-- **Section 14.3, rank of a function.** The functions of rank $`0` are those in $`Z_0`. -/
theorem rk_eq_zero_iff {f : I → ZFSet.{u}} (hf : Bdd 𝓕 X f) : rk 𝓕 X f = 0 ↔ Atomic 𝓕 X f := by
  rw [← Nat.le_zero, rk_le_iff hf]
  rfl

omit [Small.{u} I] in
/-- **Section 14.3, rank of a function.** The rank of the constant function $`a^I` is the rank
of the entity $`a` in $`\mathbb U(X)`. -/
theorem rk_const {a : ZFSet.{u}} (ha : a ∈ superstructure X) :
    rk 𝓕 X (fun _ : I => a) = rank X a := by
  obtain ⟨_, h⟩ := (eventually_rank_eq_rk (𝓕 := 𝓕) (bdd_const ha)).exists
  exact h.symm

/-!
## 14.4 Exercises on the Ultrapower Construction: Exercise (2)

The second exercise asks for the behaviour of the class of a function-valued function. Its
main clause is {lit}`BoundedUltrapower.col_appVal` above; the two statements below complete
it. Exercises (1) and (3) are in part 5.
-/

/-- **Exercise 14.4(2).** If $`F \in Z` and $`F(i)` is a function for almost
all $`i`, then $`[F]` is a function. A function of a universe is a single-valued set of
pairs of members of the universe. -/
theorem isFunction_col (hX : IsBaseSet X) {G : I → ZFSet.{u}} (hG : Bdd 𝓕 X G)
    (hfun : ∀ᶠ i in 𝓕, IsFunction (G i) ∧ RelIn (superstructure X) (G i)) :
    IsFunction (col 𝓕 hX G) ∧ RelIn (superstructure (base 𝓕 X)) (col 𝓕 hX G) := by
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  by_cases h0 : ∀ᶠ i in 𝓕, G i = ∅
  · rw [col_congr hX (show G =ᶠ[𝓕] fun _ => ∅ from h0), col_const_empty]
    exact ⟨⟨fun p hp => absurd hp (notMem_empty p), fun a b c h => absurd h (notMem_empty _)⟩,
      fun p hp => absurd hp (notMem_empty p)⟩
  · have h1 : ∀ᶠ i in 𝓕, ∃ x, x ∈ superstructure X ∧ x ∈ dom (G i) := by
      filter_upwards [Ultrafilter.eventually_not.2 h0, hfun] with i h2 h3
      obtain ⟨p, hp⟩ := (eq_empty_or_nonempty (G i)).resolve_left h2
      obtain ⟨a, ha, b, -, rfl⟩ := h3.2 p hp
      exact ⟨a, ha, mem_dom.2 ⟨b, hp⟩⟩
    obtain ⟨x, hx⟩ := Filter.skolem.1 h1
    have hxb : Bdd 𝓕 X x := by
      obtain ⟨n, hn⟩ := hG
      refine ⟨n, ?_⟩
      filter_upwards [hn, hx, hfun] with i c1 c2 c3
      obtain ⟨b, hb⟩ := mem_dom.1 c2.2
      obtain ⟨a', ha', b', hb', e⟩ := c3.2 _ hb
      have p1 := mem_cumPow_of_mem' hX c1 hb (e ▸ (hW.isSetOf_opair ha' hb').1)
      have p2 := mem_cumPow_of_mem' hX p1 singleton_mem_pair (hW.isSetOf_singleton c2.1).1
      exact mem_cumPow_of_mem' hX p2 (mem_singleton.2 rfl) c2.1
    have := (col_appDef hX hG hxb).2 (by
      filter_upwards [hfun, hx] with i c1 c2
      exact ⟨c1.1, c1.2, c2.2⟩)
    exact ⟨this.1, this.2.1⟩

/-- Outside the domain, the value {lit}`app` is the empty set: it is the union of an empty
set of candidates. -/
theorem app_of_notMem_dom {f a : ZFSet.{u}} (h : a ∉ dom f) : app f a = ∅ := by
  have : ((ran f).sep fun b => pair a b ∈ f) = ∅ := by
    ext b
    rw [mem_sep]
    exact ⟨fun hb => absurd (mem_dom.2 ⟨b, hb.2⟩) h, fun hb => absurd hb (notMem_empty b)⟩
  rw [app, this, sUnion_empty]

/-- **Exercise 14.4(2).** If $`F \in Z` is a function almost everywhere, then for all
$`h, k \in Z`
$$`[F]([h]) = [k] \iff \{i : F(i)(h(i)) = k(i)\} \in \mathcal F.`
As in the book there is no hypothesis on the domains. Where $`h(i)` is in the domain of
$`F(i)` for almost all $`i` this is the expected statement about values. In the other case
$`[h]` is not in the domain of $`[F]`, both sides refer to the value {lit}`app` outside the
domain, which is the empty set by convention, and the equivalence says that $`[k]` is empty
exactly when $`k(i)` is empty almost everywhere. "Function" means function of the universe: a
single-valued set of pairs of members of $`\mathbb U(X)`. -/
theorem app_col_eq_iff (hX : IsBaseSet X) {G h k : I → ZFSet.{u}} (hG : Bdd 𝓕 X G)
    (hh : Bdd 𝓕 X h) (hk : Bdd 𝓕 X k)
    (hfun : ∀ᶠ i in 𝓕, IsFunction (G i) ∧ RelIn (superstructure X) (G i)) :
    app (col 𝓕 hX G) (col 𝓕 hX h) = col 𝓕 hX k ↔ ∀ᶠ i in 𝓕, app (G i) (h i) = k i := by
  by_cases hdom : ∀ᶠ i in 𝓕, h i ∈ dom (G i)
  · have hdef := (col_appDef hX hG hh).2 (by
      filter_upwards [hfun, hdom] with i c1 c2
      exact ⟨c1.1, c1.2, c2⟩)
    constructor
    · intro e
      have hmem := hdef.1.pair_app_mem hdef.2.2
      rw [e] at hmem
      filter_upwards [(col_appVal hX hG hh hk).1 hmem, hfun] with i c1 c2
      exact c2.1.app_eq c1
    · intro hev
      refine hdef.1.app_eq ((col_appVal hX hG hh hk).2 ?_)
      filter_upwards [hev, hfun, hdom] with i c1 c2 c3
      rw [← c1]
      exact c2.1.pair_app_mem c3
  · have hW := (isUniverseOver_superstructure hX).toIsUniverse
    have hnd : ∀ᶠ i in 𝓕, h i ∉ dom (G i) := Ultrafilter.eventually_not.2 hdom
    have h1 : col 𝓕 hX h ∉ dom (col 𝓕 hX G) := fun hc => by
      have hfc := isFunction_col hX hG hfun
      obtain ⟨i, c1, c2⟩ := (((col_appDef hX hG hh).1 ⟨hfc.1, hfc.2, hc⟩).and hnd).exists
      exact c2 c1.2.2
    have h2 : (∀ᶠ i in 𝓕, app (G i) (h i) = k i) ↔ ∀ᶠ i in 𝓕, k i = ∅ :=
      eventually_congr (hnd.mono fun i hi => by rw [app_of_notMem_dom hi, eq_comm])
    rw [app_of_notMem_dom h1, h2]
    exact ⟨fun e => (col_eq_iff hX hk (bdd_const hW.empty_mem)).1
        (e.symm.trans (col_const_empty (𝓕 := 𝓕) hX).symm),
      fun e => ((col_congr hX (show k =ᶠ[𝓕] fun _ => ∅ from e)).trans (col_const_empty hX)).symm⟩

end BoundedUltrapower

end Goldblatt
