import Goldblatt.Ch13_Universes.Hyperfinite

/-!
# 13 (part 6). Hyperfinite Sets and Internal Cardinality

This is the sixth of seven parts of Chapter 13 (the overview is on the chapter page
{lit}`Goldblatt.Ch13_Universes`). It covers the theory of hyperfinite sets of Sections 13.17
and 13.18: the finite power set and its transform, Theorem 13.17.1 characterizing the
hyperfinite sets as those in internal bijection with an initial segment of the hypernaturals,
internal cardinality, and the exercises on hyperfinite sets and their sizes. It uses the
numbers of part 5. Hyperfinite sums (Sections 13.19 and 13.20) are in part 7.

The two sections follow the book's order, with one exception forced by the order of the
proofs: two exercises of Section 13.18 that do not involve numbers, (2) in its first half and
(6), are proved in Section 13.17, where later proofs of that section use them. Within Section
13.18 the exercises appear in the order in which their proofs depend on each other.
-/

noncomputable section

namespace Goldblatt

open ZFSet

universe u

/-!
## 13.17 Hyperfiniteness

For a set $`A` of the universe, $`\mathcal P_F(A)` is the set of its finite subsets. The
members of $`{}^*\mathcal P_F(A)` are the hyperfinite subsets of $`{}^*A`; each is an internal
subset of $`{}^*A`, but in general not a finite one. Theorem 13.17.1 characterizes the
hyperfinite sets as those in internal bijection with an initial segment
$`\{1, \dots, n\}` of the hypernaturals.
-/

/-- **Section 13.17.** The set $`\mathcal P_F(A) = \{B \subseteq A : B \text{ is finite}\}`
of all finite subsets of $`A`. -/
def finPow (A : ZFSet.{u}) : ZFSet.{u} :=
  (powerset A).sep fun B => (B : Set ZFSet.{u}).Finite

/-- **Section 13.17.** The members of $`\mathcal P_F(A)` are the finite subsets of $`A`. -/
theorem mem_finPow {A B : ZFSet.{u}} : B ∈ finPow A ↔ B ⊆ A ∧ (B : Set ZFSet.{u}).Finite := by
  rw [finPow, mem_sep, mem_powerset]

/-- **Section 13.17.** If $`A \in \mathbb U` then $`\mathcal P_F(A) \in \mathbb U`. -/
theorem IsUniverse.isSetOf_finPow {U A : ZFSet.{u}} (hU : IsUniverse U) (hA : IsSetOf U A) :
    IsSetOf U (finPow A) :=
  hU.isSetOf_sep (hU.isSetOf_powerset hA) _

namespace NonstandardFramework

variable (F : NonstandardFramework.{u}) {A B : ZFSet.{u}}

/-- **Section 13.17, hyperfinite sets.** A set is hyperfinite when it belongs to
$`{}^*\mathcal P_F(A)` for some set $`A \in \mathbb U`. -/
def Hyperfinite (B : ZFSet.{u}) : Prop := ∃ A, IsSetOf F.U A ∧ B ∈ F.star (finPow A)

/-- **Section 13.17.** $`{}^*\mathcal P_F(A) \subseteq {}^*\mathcal P(A) \subseteq
\mathcal P({}^*A)`. -/
theorem star_finPow_subset (hA : IsSetOf F.U A) :
    F.star (finPow A) ⊆ F.star (powerset A) ∧ F.star (powerset A) ⊆ powerset (F.star A) :=
  ⟨(F.star_subset_star_iff (F.hU.isSetOf_finPow hA) (F.hU.isSetOf_powerset hA)).2 sep_subset,
    F.star_powerset_subset hA⟩

/-- **Section 13.17.** Each member of $`{}^*\mathcal P_F(A)` is an internal subset of
$`{}^*A`. -/
theorem internal_subset_of_mem_star_finPow (hA : IsSetOf F.U A) (hB : B ∈ F.star (finPow A)) :
    B ⊆ F.star A ∧ F.Internal B :=
  (F.mem_star_powerset_iff hA).1 ((F.star_finPow_subset hA).1 hB)

variable {F} in
/-- A hyperfinite set is internal. -/
theorem Hyperfinite.internal (h : F.Hyperfinite B) : F.Internal B :=
  let ⟨_, hA, hB⟩ := h
  (F.internal_subset_of_mem_star_finPow hA hB).2

variable {F} in
/-- A hyperfinite set is a set of $`\mathbb U'`. -/
theorem Hyperfinite.isSetOf (h : F.Hyperfinite B) : IsSetOf F.U' B :=
  let ⟨_, hA, hB⟩ := h
  F.isSetOf_of_mem_star_powerset hA ((F.star_finPow_subset hA).1 hB)

variable {F} in
/-- A hyperfinite subset of a standard set $`{}^*C` belongs to $`{}^*\mathcal P_F(C)`. -/
theorem Hyperfinite.mem_star_finPow {C : ZFSet.{u}} (h : F.Hyperfinite B) (hC : IsSetOf F.U C)
    (hBC : B ⊆ F.star C) : B ∈ F.star (finPow C) := by
  obtain ⟨A, hA, hB⟩ := h
  have hFA := F.hU.isSetOf_finPow hA
  have hFC := F.hU.isSetOf_finPow hC
  have h := F.transfer
    (.all 0 (.const (finPow A)) (.imp (.all 1 (.var 0) (.elem (.var 1) (.const C)))
      (.elem (.var 0) (.const (finPow C)))))
    (by simp [Formula.IsSentence, hFA.1, hFC.1, hC.1])
  sat_simp at h
  exact h.1 (fun x _ hx hxC => mem_finPow.2
    ⟨fun y hy => hxC y (F.hU.subset hA ((mem_finPow.1 hx).1 hy)) hy, (mem_finPow.1 hx).2⟩)
    B (F.star_subset_U' hFA hB) hB fun y _ hy => hBC hy

variable {F} in
/-- **Exercise 13.18 (2), first part.** Any internal subset of a hyperfinite set is
hyperfinite. -/
theorem Hyperfinite.of_internal_subset (hA : F.Hyperfinite A) (hB : F.Internal B)
    (hBA : B ⊆ A) : F.Hyperfinite B := by
  obtain ⟨T, hT, hAT⟩ := hA
  have hFT := F.hU.isSetOf_finPow hT
  have hPT := F.hU.isSetOf_powerset hT
  have hAsub := (F.internal_subset_of_mem_star_finPow hT hAT).1
  have hBP := (F.mem_star_powerset_iff hT).2 ⟨fun x hx => hAsub (hBA hx), hB⟩
  have h := F.transfer
    (.all 0 (.const (finPow T)) (.all 1 (.const (powerset T))
      (.imp (.all 2 (.var 1) (.elem (.var 2) (.var 0))) (.elem (.var 1) (.const (finPow T))))))
    (by simp [Formula.IsSentence, hFT.1, hPT.1])
  sat_simp at h
  refine ⟨T, hT, h.1 ?_ A (F.star_subset_U' hFT hAT) hAT B hB.mem_U' hBP fun z _ hz => hBA hz⟩
  intro x _ hx y _ hy hyx
  rw [mem_powerset] at hy
  have hsub : y ⊆ x := fun z hz => hyx z (F.hU.subset hT (hy hz)) hz
  exact mem_finPow.2 ⟨hy, (mem_finPow.1 hx).2.subset fun z hz => hsub hz⟩

variable {F} in
/-- **Exercise 13.18 (6).** Internal images of hyperfinite sets are hyperfinite: if $`f` is
an internal function and $`B` is hyperfinite, then $`f(B)` is hyperfinite. -/
theorem Hyperfinite.relImage {f : ZFSet.{u}} (hB : F.Hyperfinite B) (hf : F.Internal f)
    (hrel : RelIn F.U' f) (hfun : IsFunction f) : F.Hyperfinite (relImage f B) := by
  have hfU' : f ⊆ F.U' := fun p hp => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hrel p hp
    exact (F.isUniverse'.isSetOf_opair ha hb).1
  have hfset : IsSetOf F.U' f := isSetOf_of_subset hf.mem_U' hfU'
  obtain ⟨T, hT, -, hsubT, hrelT⟩ := F.exists_ambient [f, B] (by simp [hf, hB.internal])
  have hfT := hrelT f (by simp) hfset hrel
  have hBT := hsubT B (by simp) hB.isSetOf
  have hTT := F.hU.isSetOf_prod hT hT
  have hPTT := F.hU.isSetOf_powerset hTT
  have hPT := F.hU.isSetOf_powerset hT
  have hFT := F.hU.isSetOf_finPow hT
  have hfP : f ∈ F.star (powerset (prod T T)) :=
    (F.mem_star_powerset_iff hTT).2 ⟨by rw [F.star_prod hT hT]; exact hfT, hf⟩
  have hBF := hB.mem_star_finPow hT hBT
  have himg := F.internal_relImage hf hfset hrel hB.internal
  have himgT : Goldblatt.relImage f B ⊆ F.star T := fun b hb => by
    obtain ⟨a, -, hab⟩ := mem_relImage.1 hb
    exact (pair_mem_prod.1 (hfT hab)).2
  have hyP := (F.mem_star_powerset_iff hT).2 ⟨himgT, himg⟩
  have h := F.transfer
    (.all 0 (.const (powerset (prod T T))) (.all 1 (.const (finPow T))
      (.all 2 (.const (powerset T)) (.imp (.conj
        (.all 3 (.const T) (.all 4 (.const T) (.all 5 (.const T) (.imp
          (.conj (.elem (.opair (.var 3) (.var 4)) (.var 0))
            (.elem (.opair (.var 3) (.var 5)) (.var 0)))
          (.equal (.var 4) (.var 5))))))
        (.all 4 (.var 2) (.ex 3 (.var 1) (.elem (.opair (.var 3) (.var 4)) (.var 0)))))
      (.elem (.var 2) (.const (finPow T)))))))
    (by simp [Formula.IsSentence, hPTT.1, hFT.1, hPT.1, hT.1])
  sat_simp at h
  refine ⟨T, hT, h.1 ?_ f hf.mem_U' hfP B hB.internal.mem_U' hBF _ himg.mem_U' hyP ⟨?_, ?_⟩⟩
  · rintro g - hg x - hx y - hy ⟨hfunc, himg⟩
    rw [mem_powerset] at hg hy
    have hg' : IsFunction g := ⟨fun p hp => let ⟨a, _, b, _, h⟩ := mem_prod.1 (hg hp); ⟨a, b, h⟩,
      fun a b c hab hac => by
        have h1 := pair_mem_prod.1 (hg hab)
        have h2 := pair_mem_prod.1 (hg hac)
        exact hfunc a (F.hU.subset hT h1.1) h1.1 b (F.hU.subset hT h1.2) h1.2 c
          (F.hU.subset hT h2.2) h2.2 ⟨hab, hac⟩⟩
    refine mem_finPow.2 ⟨hy, ((mem_finPow.1 hx).2.image (app g)).subset fun b hb => ?_⟩
    obtain ⟨a, -, hax, hab⟩ := himg b (F.hU.subset hT (hy hb)) hb
    exact ⟨a, hax, hg'.app_eq hab⟩
  · exact fun a _ _ b _ _ c _ _ h => hfun.2 a b c h.1 h.2
  · intro b _ hb
    obtain ⟨a, ha, hab⟩ := mem_relImage.1 hb
    exact ⟨a, F.star_subset_U' hT (hBT ha), ha, hab⟩

end NonstandardFramework

/-!
### The characterization by internal bijections

The proof of Theorem 13.17.1 transfers two sentences built on one formula, which says that
$`f` is a bijection from the initial segment determined by $`n` onto $`Z`. The formula and its
meaning are set up first.
-/

/-- **Theorem 13.17.1, the statement transferred.** The statement, with all quantifiers bounded and ranging over a universe $`W`, that $`V` is
the initial segment $`\{x \in N : 1 \le x \le n\}` and that $`f` is a bijection from $`V` onto
$`Z`. Its seven clauses are the seven formulas in the book's proof of Theorem 13.17.1. -/
def BijSpec (W N' Le' one V Z n f : ZFSet.{u}) : Prop :=
  (∀ x ∈ W, x ∈ V → x ∈ N' ∧ pair one x ∈ Le' ∧ pair x n ∈ Le') ∧
  (∀ x ∈ W, x ∈ N' → pair one x ∈ Le' ∧ pair x n ∈ Le' → x ∈ V) ∧
  (∀ b ∈ W, b ∈ f → ∃ x ∈ W, x ∈ V ∧ ∃ y ∈ W, y ∈ Z ∧ b = pair x y) ∧
  (∀ x ∈ W, x ∈ V → ∀ y ∈ W, y ∈ Z → ∀ z ∈ W, z ∈ Z →
    pair x y ∈ f ∧ pair x z ∈ f → y = z) ∧
  (∀ x ∈ W, x ∈ V → ∃ y ∈ W, y ∈ Z ∧ pair x y ∈ f) ∧
  (∀ y ∈ W, y ∈ Z → ∃ x ∈ W, x ∈ V ∧ pair x y ∈ f) ∧
  (∀ x ∈ W, x ∈ V → ∀ y ∈ W, y ∈ V → ∀ z ∈ W, z ∈ Z →
    pair x z ∈ f ∧ pair y z ∈ f → x = y)

/-- **Theorem 13.17.1, the formula of the proof.** The formula $`\varphi(n, f, Z)`: there is
$`V \in \mathcal P(\mathbb N)` such that $`V = \{1, \dots, n\}` and $`f` is a bijection from
$`V` onto $`Z`. The variables $`0, 1, 2` stand for $`Z, n, f`. -/
def bijFormula (PN N' Le' one : ZFSet.{u}) : Formula.{u} :=
  .ex 3 (.const PN) (.conj
    (.all 4 (.var 3) (.conj (.elem (.var 4) (.const N'))
      (.conj (.elem (.opair (.const one) (.var 4)) (.const Le'))
        (.elem (.opair (.var 4) (.var 1)) (.const Le')))))
    (.conj (.all 4 (.const N') (.imp
        (.conj (.elem (.opair (.const one) (.var 4)) (.const Le'))
          (.elem (.opair (.var 4) (.var 1)) (.const Le')))
        (.elem (.var 4) (.var 3))))
    (.conj (.all 4 (.var 2) (.ex 5 (.var 3) (.ex 6 (.var 0)
        (.equal (.var 4) (.opair (.var 5) (.var 6))))))
    (.conj (.all 4 (.var 3) (.all 5 (.var 0) (.all 6 (.var 0) (.imp
        (.conj (.elem (.opair (.var 4) (.var 5)) (.var 2))
          (.elem (.opair (.var 4) (.var 6)) (.var 2)))
        (.equal (.var 5) (.var 6))))))
    (.conj (.all 4 (.var 3) (.ex 5 (.var 0) (.elem (.opair (.var 4) (.var 5)) (.var 2))))
    (.conj (.all 5 (.var 0) (.ex 4 (.var 3) (.elem (.opair (.var 4) (.var 5)) (.var 2))))
      (.all 4 (.var 3) (.all 5 (.var 3) (.all 6 (.var 0) (.imp
        (.conj (.elem (.opair (.var 4) (.var 6)) (.var 2))
          (.elem (.opair (.var 5) (.var 6)) (.var 2)))
        (.equal (.var 4) (.var 5))))))))))))

/-- The transform of the formula {lit}`bijFormula` is the same formula with transformed constants.
-/
theorem star_bijFormula (s : ZFSet.{u} → ZFSet.{u}) (PN N' Le' one : ZFSet.{u}) :
    (bijFormula PN N' Le' one).star s = bijFormula (s PN) (s N') (s Le') (s one) := by
  simp [bijFormula]

/-- The formula {lit}`bijFormula` holds exactly when some $`V` satisfies {lit}`BijSpec`. -/
theorem sat_bijFormula (W PN N' Le' one : ZFSet.{u}) (v : ℕ → ZFSet.{u}) :
    Sat W v (bijFormula PN N' Le' one) ↔
      ∃ V ∈ W, V ∈ PN ∧ BijSpec W N' Le' one V (v 0) (v 1) (v 2) := by
  simp only [bijFormula, BijSpec]
  sat_simp

/-- The formula {lit}`bijFormula` is a formula of the language of $`\mathbb U` in the variables
$`0, 1, 2`. -/
theorem admissible_bijFormula {U PN N' Le' one : ZFSet.{u}} (hPN : PN ∈ U) (hN : N' ∈ U)
    (hLe : Le' ∈ U) (hone : one ∈ U) :
    (bijFormula PN N' Le' one).Admissible U (insert 2 (insert 1 (insert 0 ∅))) := by
  simp [bijFormula, hPN, hN, hLe, hone]

/-- The bounded statement {lit}`BijSpec` says what it is meant to say. -/
theorem bijSpec_iff {W N' Le' one V Z n f : ZFSet.{u}} (hV : V ⊆ W) (hZ : Z ⊆ W) (hN : N' ⊆ W)
    (hf : f ⊆ W) :
    BijSpec W N' Le' one V Z n f ↔
      V = (N'.sep fun x => pair one x ∈ Le' ∧ pair x n ∈ Le') ∧ IsFunc V Z f ∧
        IsInjective f ∧ ran f = Z := by
  constructor
  · rintro ⟨e1, e2, e3, e4, e5, e6, e7⟩
    have hsub : f ⊆ prod V Z := fun b hb => by
      obtain ⟨x, -, hx, y, -, hy, rfl⟩ := e3 b (hf hb) hb
      exact pair_mem_prod.2 ⟨hx, hy⟩
    refine ⟨?_, ⟨hsub, fun x hx => ?_⟩, fun a a' b hab hab' => ?_, ?_⟩
    · ext x
      rw [mem_sep]
      exact ⟨fun hx => e1 x (hV hx) hx, fun hx => e2 x (hN hx.1) hx.1 hx.2⟩
    · obtain ⟨y, -, hy, hxy⟩ := e5 x (hV hx) hx
      refine ⟨y, hxy, fun w hw => ?_⟩
      have hwZ := (pair_mem_prod.1 (hsub hw)).2
      exact e4 x (hV hx) hx w (hZ hwZ) hwZ y (hZ hy) hy ⟨hw, hxy⟩
    · have h1 := pair_mem_prod.1 (hsub hab)
      have h2 := pair_mem_prod.1 (hsub hab')
      exact e7 a (hV h1.1) h1.1 a' (hV h2.1) h2.1 b (hZ h1.2) h1.2 ⟨hab, hab'⟩
    · ext y
      rw [mem_ran]
      constructor
      · rintro ⟨x, hxy⟩
        exact (pair_mem_prod.1 (hsub hxy)).2
      · intro hy
        obtain ⟨x, -, -, hxy⟩ := e6 y (hZ hy) hy
        exact ⟨x, hxy⟩
  · rintro ⟨rfl, hfunc, hinj, hran⟩
    refine ⟨fun x _ hx => mem_sep.1 hx, fun x _ hx h => mem_sep.2 ⟨hx, h⟩, fun b _ hb => ?_,
      fun x _ hx y _ _ z _ _ h => ?_, fun x _ hx => ?_, fun y _ hy => ?_,
      fun x _ _ y _ _ z _ _ h => hinj x y z h.1 h.2⟩
    · obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod.1 (hfunc.1 hb)
      exact ⟨x, hV hx, hx, y, hZ hy, hy, rfl⟩
    · exact hfunc.isFunction.2 x y z h.1 h.2
    · obtain ⟨y, hy, -⟩ := hfunc.2 x hx
      have hyZ := (pair_mem_prod.1 (hfunc.1 hy)).2
      exact ⟨y, hZ hyZ, hyZ, hy⟩
    · rw [← hran, mem_ran] at hy
      obtain ⟨x, hxy⟩ := hy
      have hxV := (pair_mem_prod.1 (hfunc.1 hxy)).1
      exact ⟨x, hV hxV, hxV, hxy⟩

/-- Unfold the truth definition of a formula built from {lit}`bijFormula`. -/
macro "bij_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Formula.Holds, Formula.star, Term.star, star_bijFormula, Sat,
    sat_bijFormula, Term.Defined, Term.val, Term.val_opair, Term.defined_opair,
    Term.star_opair, forall_true_left, true_and, and_true, and_self,
    Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, zero_ne_one,
    one_ne_zero, OfNat.ofNat_ne_zero, OfNat.zero_ne_ofNat, OfNat.ofNat_ne_one,
    OfNat.one_ne_ofNat, Nat.reduceEqDiff] $[$loc]?)

namespace RealFramework

open Formula Term NonstandardFramework

variable (F : RealFramework.{u}) {A B C D f a b c n x : ZFSet.{u}}

/-- In the standard universe, the initial segment determined by the natural number $`m`
consists of the numbers $`1, \dots, m`. -/
theorem mem_sep_seg_iff {m : ℕ} :
    x ∈ (F.N.sep fun x => pair (F.nat 1) x ∈ F.Le ∧ pair x (F.nat m) ∈ F.Le) ↔
      ∃ k, 1 ≤ k ∧ k ≤ m ∧ x = F.nat k := by
  rw [mem_sep, F.mem_N]
  constructor
  · rintro ⟨⟨k, rfl⟩, h1, h2⟩
    exact ⟨k, F.pair_nat_mem_Le.1 h1, F.pair_nat_mem_Le.1 h2, rfl⟩
  · rintro ⟨k, h1, h2, rfl⟩
    exact ⟨⟨k, rfl⟩, F.pair_nat_mem_Le.2 h1, F.pair_nat_mem_Le.2 h2⟩

/-- **Theorem 13.17.1.** A set $`B` is hyperfinite if and only if there is an internal
bijection $`f : \{1, \dots, n\} \to B` for some $`n \in {}^*\mathbb N`. An internal function
is an internal set of pairs of members of $`\mathbb U'`; in the second sentence transferred
in the proof, the clause that $`Z` is a set is added to the book's hypothesis (it is
automatic there because the book's $`\mathbb N` does not contain $`0`). -/
theorem hyperfinite_iff :
    F.Hyperfinite B ↔ ∃ n ∈ F.star F.N, ∃ f, F.Internal f ∧ RelIn F.U' f ∧
      IsFunc (F.seg n) B f ∧ IsInjective f ∧ ran f = B := by
  have hPN := F.hU.isSetOf_powerset F.isSetOf_N
  have hNU' := F.star_subset_U' F.isSetOf_N
  constructor
  · rintro ⟨A, hA, hB⟩
    have hFP := F.hU.isSetOf_finPow hA
    have hNA := F.hU.isSetOf_prod F.isSetOf_N hA
    have hPNA := F.hU.isSetOf_powerset hNA
    have hsent : (Formula.all 0 (.const (finPow A)) (.ex 1 (.const F.N)
        (.ex 2 (.const (powerset (prod F.N A)))
          (bijFormula (powerset F.N) F.N F.Le (F.nat 1))))).IsSentence F.U :=
      ⟨hFP.1, F.isSetOf_N.1, hPNA.1,
        admissible_bijFormula hPN.1 F.isSetOf_N.1 F.isSetOf_Le.1 (F.nat_mem_U 1)⟩
    have h := F.transfer _ hsent
    bij_simp at h
    rw [F.star_nat] at h
    have hBsub := (F.internal_subset_of_mem_star_finPow hA hB).1
    have hBU : B ⊆ F.U' := fun y hy => F.star_subset_U' hA (hBsub hy)
    obtain ⟨n, -, hn, f, -, hf, V, -, hV, hspec⟩ := h.1 (by
      intro Z _ hZ
      obtain ⟨hZA, hZfin⟩ := mem_finPow.1 hZ
      have := hZfin.to_subtype
      let e := (Finite.equivFin (Z : Set ZFSet.{u})).symm
      set m := Nat.card (Z : Set ZFSet.{u}) with hm
      set V : ZFSet.{u} := F.N.sep fun x => pair (F.nat 1) x ∈ F.Le ∧ pair x (F.nat m) ∈ F.Le
        with hVdef
      set f : ZFSet.{u} := ZFSet.range fun i : Fin m => pair (F.nat (i + 1)) (e i : ZFSet.{u})
        with hfdef
      have hfmem : ∀ p, p ∈ f ↔ ∃ i : Fin m, p = pair (F.nat (i + 1)) (e i) := by
        intro p
        rw [hfdef, mem_range]
        exact ⟨fun ⟨k, h⟩ => ⟨k, h.symm⟩, fun ⟨k, h⟩ => ⟨k, h.symm⟩⟩
      have hVmem : ∀ x, x ∈ V ↔ ∃ i : Fin m, x = F.nat (i + 1) := by
        intro x
        rw [hVdef, F.mem_sep_seg_iff]
        constructor
        · rintro ⟨k, h1, h2, rfl⟩
          exact ⟨⟨k - 1, by omega⟩, by congr 1; simp; omega⟩
        · rintro ⟨i, rfl⟩
          exact ⟨i + 1, by omega, by omega, rfl⟩
      have heZ : ∀ i, (e i : ZFSet.{u}) ∈ Z := fun i => (e i).2
      have hfunc : IsFunc V Z f := by
        refine ⟨fun p hp => ?_, fun z hz => ?_⟩
        · obtain ⟨i, rfl⟩ := (hfmem p).1 hp
          exact pair_mem_prod.2 ⟨(hVmem _).2 ⟨i, rfl⟩, heZ i⟩
        · obtain ⟨i, rfl⟩ := (hVmem z).1 hz
          refine ⟨e i, (hfmem _).2 ⟨i, rfl⟩, fun w hw => ?_⟩
          obtain ⟨j, hj⟩ := (hfmem _).1 hw
          obtain ⟨h1, h2⟩ := pair_inj.1 hj
          have : i = j := Fin.ext (by simpa using F.nat_injective h1)
          rw [h2, this]
      have hinj : IsInjective f := by
        intro a a' b hab hab'
        obtain ⟨i, hi⟩ := (hfmem _).1 hab
        obtain ⟨j, hj⟩ := (hfmem _).1 hab'
        obtain ⟨rfl, h2⟩ := pair_inj.1 hi
        obtain ⟨rfl, h2'⟩ := pair_inj.1 hj
        have : e i = e j := Subtype.ext (h2.symm.trans h2')
        rw [e.injective this]
      have hran : ran f = Z := by
        ext z
        rw [mem_ran]
        constructor
        · rintro ⟨x, hx⟩
          exact (pair_mem_prod.1 (hfunc.1 hx)).2
        · intro hz
          refine ⟨F.nat ((e.symm ⟨z, hz⟩ : ℕ) + 1), (hfmem _).2 ⟨e.symm ⟨z, hz⟩, ?_⟩⟩
          rw [Equiv.apply_symm_apply]
      have hVN : V ⊆ F.N := sep_subset
      have hZU : Z ⊆ F.U := fun y hy => F.hU.subset hA (hZA hy)
      have hfNA : f ⊆ prod F.N A := fun p hp => by
        obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 (hfunc.1 hp)
        exact pair_mem_prod.2 ⟨hVN ha, hZA hb⟩
      have hfU : f ⊆ F.U := fun p hp => F.hU.subset hNA (hfNA hp)
      refine ⟨F.nat m, F.nat_mem_U m, F.mem_N.2 ⟨m, rfl⟩, f,
        (F.hU.isSetOf_of_subset hNA hfNA).1, mem_powerset.2 hfNA, V,
        (F.hU.isSetOf_of_subset F.isSetOf_N hVN).1, mem_powerset.2 hVN, ?_⟩
      exact (bijSpec_iff (fun x hx => F.hU.subset F.isSetOf_N (hVN hx)) hZU
        (F.hU.subset F.isSetOf_N) hfU).2 ⟨rfl, hfunc, hinj, hran⟩) B
      (F.internal_subset_of_mem_star_finPow hA hB).2.mem_U' hB
    have hVN := mem_powerset.1 (F.star_powerset_subset F.isSetOf_N hV)
    have hfsub := mem_powerset.1 (F.star_powerset_subset hNA hf)
    have hfU' : f ⊆ F.U' := fun p hp => F.star_subset_U' hNA (hfsub hp)
    obtain ⟨rfl, hfunc, hinj, hran⟩ :=
      (bijSpec_iff (fun x hx => hNU' (hVN hx)) hBU hNU' hfU').1 hspec
    refine ⟨n, hn, f, F.internal_of_mem_star hPNA hf, fun p hp => ?_, hfunc, hinj, hran⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 (hfunc.1 hp)
    exact ⟨a, hNU' (hVN ha), b, hBU hb, rfl⟩
  · rintro ⟨n, hn, f, hfint, hfrel, hfunc, hinj, hran⟩
    have hfU' : f ⊆ F.U' := fun p hp => by
      obtain ⟨a, ha, b, hb, rfl⟩ := hfrel p hp
      exact (F.isUniverse'.isSetOf_opair ha hb).1
    have hfset : IsSetOf F.U' f := isSetOf_of_subset hfint.mem_U' hfU'
    have hBint : F.Internal B := hran ▸ F.internal_ran hfint hfset hfrel
    have hBU : B ⊆ F.U' := fun y hy => by
      rw [← hran, mem_ran] at hy
      obtain ⟨x, hxy⟩ := hy
      obtain ⟨a, -, b, hb, h⟩ := hfrel _ hxy
      rw [(pair_inj.1 h).2]
      exact hb
    obtain ⟨T, hT, hTt, hTt', hBT⟩ := F.exists_transitive_of_internal hBint
    have hBsubT : B ⊆ F.star T := fun y hy => hTt' B hBT y hy (hBU hy)
    have hNT := F.hU.isSetOf_prod F.isSetOf_N hT
    have hPNT := F.hU.isSetOf_powerset hNT
    have hFP := F.hU.isSetOf_finPow hT
    have hfmem : f ∈ F.star (powerset (prod F.N T)) := by
      refine (F.mem_star_powerset_iff hNT).2 ⟨fun p hp => ?_, hfint⟩
      rw [F.star_prod F.isSetOf_N hT]
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 (hfunc.1 hp)
      exact pair_mem_prod.2 ⟨(mem_sep.1 ha).1, hBsubT hb⟩
    have hS : (Formula.disj (.equal (.var 0) (.const ∅))
        (.ex 1 (.var 0) (.equal (.var 1) (.var 1)))).Admissible F.U (insert 0 ∅) := by
      simp [F.hU.empty_mem]
    have hsent : (Formula.all 0 (.const T) (.imp (.conj
          (.disj (.equal (.var 0) (.const ∅)) (.ex 1 (.var 0) (.equal (.var 1) (.var 1))))
          (.ex 1 (.const F.N) (.ex 2 (.const (powerset (prod F.N T)))
            (bijFormula (powerset F.N) F.N F.Le (F.nat 1)))))
        (.elem (.var 0) (.const (finPow T))))).IsSentence F.U :=
      ⟨hT.1, ⟨hS, F.isSetOf_N.1, hPNT.1,
        admissible_bijFormula hPN.1 F.isSetOf_N.1 F.isSetOf_Le.1 (F.nat_mem_U 1)⟩,
        Set.mem_insert _ _, hFP.1⟩
    have h := F.transfer _ hsent
    bij_simp at h
    rw [F.star_empty, F.star_nat] at h
    refine ⟨T, hT, h.1 ?_ B hBint.mem_U' hBT ⟨?_, n, hNU' hn, hn, f, hfint.mem_U', hfmem,
      F.seg n, (F.internal_seg hn).mem_U', F.seg_mem_star_powerset hn, ?_⟩⟩
    · rintro Z hZU hZT ⟨hZset, m', -, hm', f', -, hf', V', -, hV', hspec⟩
      have hZs : IsSetOf F.U Z := ⟨hZU, fun hi => by
        rcases hZset with rfl | ⟨y, hy, hyZ⟩
        · exact hi.1 rfl
        · exact hi.2 y hy hyZ⟩
      have hZsubU := F.hU.subset hZs
      have hZsubT : Z ⊆ T := fun y hy => hTt Z hZT y hy (hZsubU hy)
      rw [mem_powerset] at hf' hV'
      obtain ⟨rfl, hfunc', -, hran'⟩ := (bijSpec_iff
        (fun x hx => F.hU.subset F.isSetOf_N (hV' hx)) hZsubU (F.hU.subset F.isSetOf_N)
        (fun p hp => F.hU.subset hNT (hf' hp))).1 hspec
      obtain ⟨m, rfl⟩ := F.mem_N.1 hm'
      refine mem_finPow.2 ⟨hZsubT, ?_⟩
      refine ((Set.finite_Iic m).image fun k => app f' (F.nat k)).subset fun z hz => ?_
      have hz' : z ∈ ran f' := by
        rw [hran']
        exact hz
      obtain ⟨x, hxz⟩ := mem_ran.1 hz'
      obtain ⟨k, -, hk, rfl⟩ := F.mem_sep_seg_iff.1 (pair_mem_prod.1 (hfunc'.1 hxz)).1
      exact ⟨k, hk, hfunc'.isFunction.app_eq hxz⟩
    · rcases eq_empty_or_nonempty B with rfl | ⟨y, hy⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨y, hBU hy, hy⟩
    · exact (bijSpec_iff (fun x hx => hNU' (mem_sep.1 hx).1) hBU hNU' hfU').2
        ⟨rfl, hfunc, hinj, hran⟩

/-!
### Initial segments are hyperfinite

Initial segments are hyperfinite, and infinite when their end point is unlimited.
-/

/-- **Section 13.17.** For each $`n \in {}^*\mathbb N`, the initial segment
$`\{1, \dots, n\}` of $`{}^*\mathbb N` belongs to $`{}^*\mathcal P_F(\mathbb N)`: it is
hyperfinite. -/
theorem hyperfinite_seg (hn : n ∈ F.star F.N) : F.Hyperfinite (F.seg n) := by
  have hFP := F.hU.isSetOf_finPow F.isSetOf_N
  have h := F.transfer
    (.all 1 (.const F.N) (.ex 2 (.const (finPow F.N)) (.all 0 (.const F.N)
      (.biimp (.elem (.var 0) (.var 2))
        (.conj (.elem (.opair (.const (F.nat 1)) (.var 0)) (.const F.Le))
          (.elem (.opair (.var 0) (.var 1)) (.const F.Le)))))))
    (by simp [IsSentence, F.isSetOf_N.1, hFP.1, F.isSetOf_Le.1, F.nat_mem_U])
  sat_simp at h
  rw [F.star_nat] at h
  obtain ⟨V, -, hV, hVmem⟩ := h.1 (by
    intro m' _ hm'
    obtain ⟨m, rfl⟩ := F.mem_N.1 hm'
    refine ⟨F.N.sep fun x => pair (F.nat 1) x ∈ F.Le ∧ pair x (F.nat m) ∈ F.Le,
      (F.hU.isSetOf_sep F.isSetOf_N _).1, mem_finPow.2 ⟨sep_subset, ?_⟩, fun x _ hx => by
        rw [mem_sep]
        exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩⟩
    refine ((Set.finite_Iic m).image F.nat).subset fun x hx => ?_
    obtain ⟨k, -, hk, rfl⟩ := F.mem_sep_seg_iff.1 hx
    exact ⟨k, hk, rfl⟩) n (F.star_subset_U' F.isSetOf_N hn) hn
  have hVsub := (F.internal_subset_of_mem_star_finPow F.isSetOf_N hV).1
  have : F.seg n = V := by
    ext x
    rw [seg, mem_sep]
    constructor
    · rintro ⟨hx, h⟩
      exact (hVmem x (F.star_subset_U' F.isSetOf_N hx) hx).2 h
    · intro hx
      exact ⟨hVsub hx, (hVmem x (F.star_subset_U' F.isSetOf_N (hVsub hx)) (hVsub hx)).1 hx⟩
  rw [this]
  exact ⟨F.N, F.isSetOf_N, hV⟩

/-- **Section 13.17.** When $`n` is an unlimited hypernatural, the hyperfinite set
$`\{1, \dots, n\}` contains every positive natural number and is infinite. So
$`{}^*\mathcal P_F(\mathbb N)` is not included in $`\mathcal P_F({}^*\mathbb N)`. -/
theorem infinite_seg (hn : n ∈ F.star F.N) (hnN : n ∉ F.N) :
    (F.seg n : Set ZFSet.{u}).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => F.nat (k + 1))
    (fun i j h => by simpa using F.nat_injective h) fun k => ?_
  exact mem_sep.2 ⟨F.N_subset_star (F.mem_N.2 ⟨k + 1, rfl⟩),
    F.pair_nat_mem_star_Le.2 (Nat.le_add_left 1 k), F.nat_le_of_nonstandard hn hnN (k + 1)⟩

/-!
### Internal cardinality

The number of elements of a finite subset of $`A` is a function from $`\mathcal P_F(A)` to
$`\mathbb N` in the universe. Its transform assigns to every hyperfinite subset of
$`{}^*A` a hypernatural number, its internal cardinality, and this is the number $`n` of
Theorem 13.17.1.
-/

end RealFramework

/-- The graph of a map defined on the members of a set is a function on that set. -/
theorem isFunc_graph (A B : ZFSet.{u}) (h : A → ZFSet.{u}) (hB : ∀ a, h a ∈ B) :
    IsFunc A B (ZFSet.range fun a : A => pair (a : ZFSet.{u}) (h a)) := by
  refine ⟨fun p hp => ?_, fun z hz => ?_⟩
  · obtain ⟨a, rfl⟩ := mem_range.1 hp
    exact pair_mem_prod.2 ⟨a.2, hB a⟩
  · refine ⟨h ⟨z, hz⟩, mem_range.2 ⟨⟨z, hz⟩, rfl⟩, fun w hw => ?_⟩
    obtain ⟨a, ha⟩ := mem_range.1 hw
    obtain ⟨h1, h2⟩ := pair_inj.1 ha
    have : a = ⟨z, hz⟩ := Subtype.ext h1
    rw [← h2, this]

/-- The value at $`a` of the graph of a map is the value of the map. -/
theorem app_graph (A B : ZFSet.{u}) (h : A → ZFSet.{u}) (hB : ∀ a, h a ∈ B) (a : A) :
    app (ZFSet.range fun a : A => pair (a : ZFSet.{u}) (h a)) a = h a :=
  (isFunc_graph A B h hB).isFunction.app_eq (mem_range.2 ⟨a, rfl⟩)

namespace RealFramework

open Formula Term NonstandardFramework

variable (F : RealFramework.{u}) {A B C D T f a b c n x : ZFSet.{u}}

/-- **Section 13.17, cardinality of finite sets.** The function $`\mathcal P_F(A) \to
\mathbb N` assigning to each finite subset of $`A` its number of elements, as a set of pairs
in the universe. -/
def cardFn (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun Z : (finPow A : ZFSet.{u}) =>
    pair (Z : ZFSet.{u}) (F.nat (Nat.card ((Z : ZFSet.{u}) : Set ZFSet.{u})))

/-- **Section 13.17.** The cardinality function is a function from $`\mathcal P_F(A)` to $`\mathbb
N`. -/
theorem isFunc_cardFn (A : ZFSet.{u}) : IsFunc (finPow A) F.N (F.cardFn A) :=
  isFunc_graph _ _ _ fun _ => F.mem_N.2 ⟨_, rfl⟩

/-- **Section 13.17, internal cardinality.** The internal cardinality $`|B|` of a hyperfinite
set $`B \in {}^*\mathcal P_F(A)`: the value at $`B` of the transform of the cardinality
function $`\mathcal P_F(A) \to \mathbb N`. -/
def icard (A B : ZFSet.{u}) : ZFSet.{u} := app (F.star (F.cardFn A)) B

/-- **Section 13.17.** The map $`B \mapsto |B|` is an internal function from
$`{}^*\mathcal P_F(A)` to $`{}^*\mathbb N`: it is the transform of the cardinality
function. -/
theorem isFunc_star_cardFn (hA : IsSetOf F.U A) :
    IsFunc (F.star (finPow A)) (F.star F.N) (F.star (F.cardFn A)) ∧
      F.Internal (F.star (F.cardFn A)) :=
  ⟨F.isFunc_star (F.hU.isSetOf_finPow hA) F.isSetOf_N (F.isFunc_cardFn A),
    F.internal_star (F.hU.isSetOf_of_isFunc (F.hU.isSetOf_finPow hA) F.isSetOf_N
      (F.isFunc_cardFn A)).1⟩

/-- The internal cardinality of a hyperfinite subset of $`{}^*A` is a hypernatural number. -/
theorem icard_mem (hA : IsSetOf F.U A) (hB : B ∈ F.star (finPow A)) :
    F.icard A B ∈ F.star F.N := by
  have hf := (F.isFunc_star_cardFn hA).1
  exact (pair_mem_prod.1 (hf.1 (hf.isFunction.pair_app_mem (hf.dom_eq ▸ hB)))).2

/-- **Section 13.17.** On (the transform of) a finite set the internal cardinality is the
ordinary number of elements. -/
theorem icard_star {Z : ZFSet.{u}} (hA : IsSetOf F.U A) (hZ : Z ∈ finPow A) :
    F.icard A (F.star Z) = F.nat (Nat.card (Z : Set ZFSet.{u})) := by
  rw [icard, ← F.star_app (F.hU.isSetOf_finPow hA) F.isSetOf_N (F.isFunc_cardFn A) hZ]
  have : app (F.cardFn A) Z = F.nat (Nat.card (Z : Set ZFSet.{u})) :=
    app_graph (finPow A) F.N _ (fun _ => F.mem_N.2 ⟨_, rfl⟩) ⟨Z, hZ⟩
  rw [this, F.star_nat]

/-- In the standard universe, a set in bijection with $`\{1, \dots, m\}` has $`m`
elements. -/
theorem card_eq_of_bijection {m : ℕ} {Z g : ZFSet.{u}}
    (hfunc : IsFunc (F.N.sep fun x => pair (F.nat 1) x ∈ F.Le ∧ pair x (F.nat m) ∈ F.Le) Z g)
    (hinj : IsInjective g) (hran : ran g = Z) : Nat.card (Z : Set ZFSet.{u}) = m := by
  have hV : ∀ i : Fin m, F.nat (i + 1) ∈
      (F.N.sep fun x => pair (F.nat 1) x ∈ F.Le ∧ pair x (F.nat m) ∈ F.Le) := fun i =>
    F.mem_sep_seg_iff.2 ⟨i + 1, by omega, by omega, rfl⟩
  have hpair : ∀ i : Fin m, pair (F.nat (i + 1)) (app g (F.nat (i + 1))) ∈ g := fun i =>
    hfunc.isFunction.pair_app_mem (hfunc.dom_eq ▸ hV i)
  let φ : Fin m → (Z : Set ZFSet.{u}) := fun i =>
    ⟨app g (F.nat (i + 1)), (pair_mem_prod.1 (hfunc.1 (hpair i))).2⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro i j hij
      have h1 : app g (F.nat (i + 1)) = app g (F.nat (j + 1)) := congrArg Subtype.val hij
      have h2 := hpair j
      rw [← h1] at h2
      exact Fin.ext (by simpa using F.nat_injective (hinj _ _ _ (hpair i) h2))
    · rintro ⟨z, hz⟩
      have hz' : z ∈ ran g := by
        rw [hran]
        exact hz
      obtain ⟨x, hxz⟩ := mem_ran.1 hz'
      obtain ⟨k, hk1, hk2, rfl⟩ := F.mem_sep_seg_iff.1 (pair_mem_prod.1 (hfunc.1 hxz)).1
      refine ⟨⟨k - 1, by omega⟩, Subtype.ext ?_⟩
      have hk : k - 1 + 1 = k := by omega
      show app g (F.nat (k - 1 + 1)) = z
      rw [hk]
      exact hfunc.isFunction.app_eq hxz
  simpa using (Nat.card_eq_of_bijective φ hφ).symm

/-- **Section 13.17.** The number $`n` in Theorem 13.17.1 is the internal cardinality of
$`B`: if there is an internal bijection from $`\{1, \dots, n\}` onto a hyperfinite subset
$`B` of $`{}^*A`, then $`|B| = n`. -/
theorem icard_eq_of_bijection (hA : IsSetOf F.U A) (hB : B ∈ F.star (finPow A))
    (hn : n ∈ F.star F.N) (hf : F.Internal f) (hfunc : IsFunc (F.seg n) B f)
    (hinj : IsInjective f) (hran : ran f = B) : F.icard A B = n := by
  have hPN := F.hU.isSetOf_powerset F.isSetOf_N
  have hNU' := F.star_subset_U' F.isSetOf_N
  have hFP := F.hU.isSetOf_finPow hA
  have hNA := F.hU.isSetOf_prod F.isSetOf_N hA
  have hPNA := F.hU.isSetOf_powerset hNA
  have hC := F.hU.isSetOf_of_isFunc hFP F.isSetOf_N (F.isFunc_cardFn A)
  have hBsub := (F.internal_subset_of_mem_star_finPow hA hB).1
  have hBU : B ⊆ F.U' := fun y hy => F.star_subset_U' hA (hBsub hy)
  have hfsub : f ⊆ prod (F.star F.N) (F.star A) := fun p hp => by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 (hfunc.1 hp)
    exact pair_mem_prod.2 ⟨(mem_sep.1 ha).1, hBsub hb⟩
  have hfmem : f ∈ F.star (powerset (prod F.N A)) :=
    (F.mem_star_powerset_iff hNA).2 ⟨by rw [F.star_prod F.isSetOf_N hA]; exact hfsub, hf⟩
  have hfU' : f ⊆ F.U' := fun p hp => by
    have := hfsub hp
    rw [← F.star_prod F.isSetOf_N hA] at this
    exact F.star_subset_U' hNA this
  have hsent : (Formula.all 0 (.const (finPow A)) (.all 1 (.const F.N)
      (.all 2 (.const (powerset (prod F.N A))) (.imp
        (bijFormula (powerset F.N) F.N F.Le (F.nat 1))
        (.elem (.opair (.var 0) (.var 1)) (.const (F.cardFn A))))))).IsSentence F.U :=
    ⟨hFP.1, F.isSetOf_N.1, hPNA.1,
      admissible_bijFormula hPN.1 F.isSetOf_N.1 F.isSetOf_Le.1 (F.nat_mem_U 1),
      by simp [hC.1]⟩
  have h := F.transfer _ hsent
  bij_simp at h
  rw [F.star_nat] at h
  have h' := h.1 (by
    rintro Z - hZ m' - hm' g - hg ⟨V, -, hV, hspec⟩
    obtain ⟨m, rfl⟩ := F.mem_N.1 hm'
    rw [mem_powerset] at hg hV
    have hZU : Z ⊆ F.U := fun y hy => F.hU.subset hA ((mem_finPow.1 hZ).1 hy)
    obtain ⟨rfl, hfunc', hinj', hran'⟩ := (bijSpec_iff
      (fun x hx => F.hU.subset F.isSetOf_N (hV hx)) hZU (F.hU.subset F.isSetOf_N)
      (fun p hp => F.hU.subset hNA (hg hp))).1 hspec
    refine mem_range.2 ⟨⟨Z, hZ⟩, ?_⟩
    show pair Z (F.nat (Nat.card (Z : Set ZFSet.{u}))) = pair Z (F.nat m)
    rw [F.card_eq_of_bijection hfunc' hinj' hran'])
  have hmem := h' B (F.star_subset_U' hFP hB) hB n (hNU' hn) hn f hf.mem_U' hfmem
    ⟨F.seg n, (F.internal_seg hn).mem_U', F.seg_mem_star_powerset hn,
      (bijSpec_iff (fun x hx => hNU' (mem_sep.1 hx).1) hBU hNU' hfU').2
        ⟨rfl, hfunc, hinj, hran⟩⟩
  exact (F.isFunc_star_cardFn hA).1.isFunction.app_eq hmem

/-- **Section 13.17.** The identity function on a set, as a set of pairs; it is the internal
bijection showing that an initial segment has itself as internal cardinality. -/
def _root_.Goldblatt.idOn (S : ZFSet.{u}) : ZFSet.{u} :=
  (prod S S).sep fun p => ∃ a, p = pair a a

/-- The pairs of the identity function on $`S` are the pairs $`(a, a)` with $`a \in S`. -/
theorem _root_.Goldblatt.pair_mem_idOn {S : ZFSet.{u}} : pair a b ∈ idOn S ↔ a ∈ S ∧ a = b := by
  rw [idOn, mem_sep, pair_mem_prod]
  constructor
  · rintro ⟨⟨ha, -⟩, c, hc⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.1 hc
    exact ⟨ha, rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨⟨ha, ha⟩, a, rfl⟩

/-- The identity function on $`S` is a bijection of $`S` onto itself. -/
theorem _root_.Goldblatt.isFunc_idOn (S : ZFSet.{u}) :
    IsFunc S S (idOn S) ∧ IsInjective (idOn S) ∧ ran (idOn S) = S := by
  refine ⟨⟨sep_subset, fun z hz => ⟨z, pair_mem_idOn.2 ⟨hz, rfl⟩, fun w hw =>
    (pair_mem_idOn.1 hw).2.symm⟩⟩, fun a a' b h h' => ?_, ?_⟩
  · rw [(pair_mem_idOn.1 h).2, (pair_mem_idOn.1 h').2]
  · ext b
    rw [mem_ran]
    exact ⟨fun ⟨a, h⟩ => (pair_mem_idOn.1 h).2 ▸ (pair_mem_idOn.1 h).1,
      fun hb => ⟨b, pair_mem_idOn.2 ⟨hb, rfl⟩⟩⟩

/-- The identity function on an internal set is internal. -/
theorem internal_idOn {S : ZFSet.{u}} (hS : F.Internal S) (hSset : IsSetOf F.U' S) :
    F.Internal (idOn S) := by
  have hP := F.internal_prod hS hSset hS hSset
  have hSU := F.isUniverse'.subset hSset
  have hPset : IsSetOf F.U' (prod S S) := isSetOf_of_subset hP.mem_U' fun p hp => by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 hp
    exact (F.isUniverse'.isSetOf_opair (hSU ha) (hSU hb)).1
  have := F.internal_sep (.ex 1 (.var 2) (.equal (.var 0) (.opair (.var 1) (.var 1)))) [2] 0
    (by simp) (fun _ => S) (by simp [hS]) hP hPset
  sat_simp at this
  have e : idOn S = (prod S S).sep fun p => ∃ a ∈ F.U', a ∈ S ∧ p = pair a a := by
    ext p
    rw [idOn, mem_sep, mem_sep]
    constructor
    · rintro ⟨hp, a, rfl⟩
      have ha := (pair_mem_prod.1 hp).1
      exact ⟨hp, a, hSU ha, ha, rfl⟩
    · rintro ⟨hp, a, -, -, rfl⟩
      exact ⟨hp, a, rfl⟩
  rw [e]
  exact this

/-- **Section 13.17.** The internal cardinality of the initial segment
$`\{1, \dots, n\}` is $`n`. -/
theorem icard_seg (hn : n ∈ F.star F.N) : F.icard F.N (F.seg n) = n := by
  have hseg := F.hyperfinite_seg hn
  obtain ⟨h1, h2, h3⟩ := isFunc_idOn (F.seg n)
  exact F.icard_eq_of_bijection F.isSetOf_N (hseg.mem_star_finPow F.isSetOf_N sep_subset) hn
    (F.internal_idOn hseg.internal hseg.isSetOf) h1 h2 h3

/-!
## 13.18 Exercises on Hyperfinite Sets and Sizes

The exercises of Section 13.18: bounds for internal injections between initial segments,
hyperfiniteness and size of internal subsets and of the internal power set, greatest and
least elements, and the characterization of hyperfinite sets by internal surjections. Two
parts that do not involve numbers, that internal subsets and internal images of hyperfinite
sets are hyperfinite (Exercises 13.18 (2) and (6)), are proved in Section 13.17 above for
arbitrary frameworks, where the later proofs of that section use them. The exercises appear
here in the order (2), (1), (4), (3), (5), because the first uses the second.
-/

/-- **Exercise 13.18 (2), second part.** If $`B \subseteq A` are hyperfinite subsets of
$`{}^*T`, then $`|B| \le |A|`. -/
theorem icard_le_of_subset (hT : IsSetOf F.U T) (hA : A ∈ F.star (finPow T))
    (hB : B ∈ F.star (finPow T)) (hBA : B ⊆ A) :
    pair (F.icard T B) (F.icard T A) ∈ F.star F.Le := by
  have hFP := F.hU.isSetOf_finPow hT
  have hC := F.hU.isSetOf_of_isFunc hFP F.isSetOf_N (F.isFunc_cardFn T)
  have h := F.transfer
    (.all 0 (.const (finPow T)) (.all 1 (.const (finPow T)) (.imp
      (.all 2 (.var 1) (.elem (.var 2) (.var 0)))
      (.ex 3 (.const F.N) (.ex 4 (.const F.N) (.conj
        (.elem (.opair (.var 1) (.var 3)) (.const (F.cardFn T)))
        (.conj (.elem (.opair (.var 0) (.var 4)) (.const (F.cardFn T)))
          (.elem (.opair (.var 3) (.var 4)) (.const F.Le)))))))))
    (by simp [IsSentence, hFP.1, hC.1, F.isSetOf_N.1, F.isSetOf_Le.1])
  sat_simp at h
  obtain ⟨c, -, -, d, -, -, hc, hd, hcd⟩ := h.1 (by
    intro x _ hx y _ hy hyx
    have hxT := mem_finPow.1 hx
    have hsub : (y : Set ZFSet.{u}) ⊆ x := fun z hz =>
      hyx z (F.hU.subset hT ((mem_finPow.1 hy).1 hz)) hz
    exact ⟨_, F.nat_mem_U _, F.mem_N.2 ⟨_, rfl⟩, _, F.nat_mem_U _, F.mem_N.2 ⟨_, rfl⟩,
      mem_range.2 ⟨⟨y, hy⟩, rfl⟩, mem_range.2 ⟨⟨x, hx⟩, rfl⟩,
      F.pair_nat_mem_Le.2 (Nat.card_mono hxT.2 hsub)⟩)
    A (F.star_subset_U' hFP hA) hA B (F.star_subset_U' hFP hB) hB fun z _ hz => hBA hz
  have hfun := (F.isFunc_star_cardFn hT).1.isFunction
  rw [icard, icard, hfun.app_eq hc, hfun.app_eq hd]
  exact hcd

/-- **Exercise 13.18 (1), first part.** If there is an internal injection
$`\{1, \dots, n\} \to \{1, \dots, m\}`, then $`n \le m`. -/
theorem le_of_internal_injection {m : ZFSet.{u}} (hn : n ∈ F.star F.N) (hm : m ∈ F.star F.N)
    (hf : F.Internal f) (hrel : RelIn F.U' f) (hfunc : IsFunc (F.seg n) (F.seg m) f)
    (hinj : IsInjective f) : pair n m ∈ F.star F.Le := by
  have hfU' : f ⊆ F.U' := fun p hp => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hrel p hp
    exact (F.isUniverse'.isSetOf_opair ha hb).1
  have hfset : IsSetOf F.U' f := isSetOf_of_subset hf.mem_U' hfU'
  have hran := F.internal_ran hf hfset hrel
  have hsub : ran f ⊆ F.seg m := hfunc.ran_subset
  have hsegm := F.hyperfinite_seg hm
  have hB := (hsegm.of_internal_subset hran hsub).mem_star_finPow F.isSetOf_N
    fun y hy => (mem_sep.1 (hsub hy)).1
  have hfunc' : IsFunc (F.seg n) (ran f) f := by
    refine ⟨fun p hp => ?_, hfunc.2⟩
    obtain ⟨a, ha, b, -, rfl⟩ := mem_prod.1 (hfunc.1 hp)
    exact pair_mem_prod.2 ⟨ha, mem_ran.2 ⟨a, hp⟩⟩
  have h1 := F.icard_eq_of_bijection F.isSetOf_N hB hn hf hfunc' hinj rfl
  have h2 := F.icard_seg hm
  have := F.icard_le_of_subset F.isSetOf_N (hsegm.mem_star_finPow F.isSetOf_N sep_subset) hB hsub
  rwa [h1, h2] at this

/-- **Exercise 13.18 (1), second part.** If there is an internal bijection
$`\{1, \dots, n\} \to \{1, \dots, m\}`, then $`n = m`. Hence the number $`n` in Theorem
13.17.1 is uniquely determined by the hyperfinite set. -/
theorem eq_of_internal_bijection {m : ZFSet.{u}} (hn : n ∈ F.star F.N) (hm : m ∈ F.star F.N)
    (hf : F.Internal f) (hfunc : IsFunc (F.seg n) (F.seg m) f) (hinj : IsInjective f)
    (hran : ran f = F.seg m) : n = m := by
  have hsegm := F.hyperfinite_seg hm
  rw [← F.icard_eq_of_bijection F.isSetOf_N (hsegm.mem_star_finPow F.isSetOf_N sep_subset) hn hf
    hfunc hinj hran, F.icard_seg hm]

/-- The power set of a finite set is finite. -/
theorem _root_.Goldblatt.finite_coe_powerset {x : ZFSet.{u}} (h : (x : Set ZFSet.{u}).Finite) :
    ((powerset x : ZFSet.{u}) : Set ZFSet.{u}).Finite := by
  have : Finite (𝒫 (x : Set ZFSet.{u})) := h.powerset.to_subtype
  have : Finite (powerset x) := Finite.of_equiv _ (powersetEquiv x).symm
  exact Set.toFinite _

/-- The power set of a finite set with $`k` elements has $`2^k` elements. -/
theorem _root_.Goldblatt.card_coe_powerset {x : ZFSet.{u}} (h : (x : Set ZFSet.{u}).Finite) :
    Nat.card ((powerset x : ZFSet.{u}) : Set ZFSet.{u}) = 2 ^ Nat.card (x : Set ZFSet.{u}) := by
  have e : Nat.card ((powerset x : ZFSet.{u}) : Set ZFSet.{u}) =
      Nat.card (𝒫 (x : Set ZFSet.{u})) := Nat.card_congr (powersetEquiv x)
  rw [e, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_powerset _ h]

/-- **Exercise 13.18 (4).** The internal power set
$`\mathcal P_I(A) = \mathcal P(A) \cap {}^*\mathbb U = \{B \subseteq A : B \text{ is
internal}\}`. -/
def internalPowerset (A : ZFSet.{u}) : ZFSet.{u} := (powerset A).sep F.Internal

/-- **Exercise 13.18 (4).** The function $`k \mapsto 2^k` on the natural numbers, as a set of
pairs in the universe. -/
def powFn : ZFSet.{u} := ZFSet.range fun k : ℕ => pair (F.nat k) (F.nat (2 ^ k))

/-- **Exercise 13.18 (4).** The function $`k \mapsto 2^k` is a function from $`\mathbb N` to
$`\mathbb N`. -/
theorem isFunc_powFn : IsFunc F.N F.N F.powFn := by
  refine ⟨fun p hp => ?_, fun z hz => ?_⟩
  · obtain ⟨k, rfl⟩ := mem_range.1 hp
    exact pair_mem_prod.2 ⟨F.mem_N.2 ⟨k, rfl⟩, F.mem_N.2 ⟨_, rfl⟩⟩
  · obtain ⟨k, rfl⟩ := F.mem_N.1 hz
    refine ⟨F.nat (2 ^ k), mem_range.2 ⟨k, rfl⟩, fun w hw => ?_⟩
    obtain ⟨j, hj⟩ := mem_range.1 hw
    obtain ⟨h1, h2⟩ := pair_inj.1 hj
    rw [← h2, F.nat_injective h1]

/-- **Exercise 13.18 (4).** If $`A` is hyperfinite, then so is its internal power set
$`\mathcal P_I(A)`. Moreover, if $`|A| = n` then $`|\mathcal P_I(A)| = 2^n`, where
$`n \mapsto 2^n` is the transform of the exponential function on $`\mathbb N`. -/
theorem hyperfinite_internalPowerset (hT : IsSetOf F.U T) (hA : A ∈ F.star (finPow T)) :
    F.internalPowerset A ∈ F.star (finPow (powerset T)) ∧
      F.icard (powerset T) (F.internalPowerset A) = app (F.star F.powFn) (F.icard T A) := by
  have hPT := F.hU.isSetOf_powerset hT
  have hFT := F.hU.isSetOf_finPow hT
  have hFPT := F.hU.isSetOf_finPow hPT
  have hC := F.hU.isSetOf_of_isFunc hFT F.isSetOf_N (F.isFunc_cardFn T)
  have hC' := F.hU.isSetOf_of_isFunc hFPT F.isSetOf_N (F.isFunc_cardFn (powerset T))
  have hpow := F.hU.isSetOf_of_isFunc F.isSetOf_N F.isSetOf_N F.isFunc_powFn
  have h := F.transfer
    (.all 0 (.const (finPow T)) (.ex 1 (.const (finPow (powerset T))) (.conj
      (.all 2 (.const (powerset T)) (.biimp (.elem (.var 2) (.var 1))
        (.all 3 (.var 2) (.elem (.var 3) (.var 0)))))
      (.ex 4 (.const F.N) (.ex 5 (.const F.N) (.conj
        (.elem (.opair (.var 0) (.var 4)) (.const (F.cardFn T)))
        (.conj (.elem (.opair (.var 1) (.var 5)) (.const (F.cardFn (powerset T))))
          (.elem (.opair (.var 4) (.var 5)) (.const F.powFn)))))))))
    (by simp [IsSentence, hFT.1, hFPT.1, hPT.1, hC.1, hC'.1, hpow.1, F.isSetOf_N.1])
  sat_simp at h
  obtain ⟨y, -, hy, hymem, c, -, -, d, -, -, hc, hd, hcd⟩ := h.1 (by
    intro x _ hx
    obtain ⟨hxT, hxfin⟩ := mem_finPow.1 hx
    have hPx : powerset x ∈ finPow (powerset T) := mem_finPow.2
      ⟨fun z hz => mem_powerset.2 fun w hw => hxT (mem_powerset.1 hz hw), finite_coe_powerset hxfin⟩
    refine ⟨powerset x, (F.hU.subset hFPT hPx), hPx, fun z _ hz => ?_, _, F.nat_mem_U _,
      F.mem_N.2 ⟨_, rfl⟩, _, F.nat_mem_U _, F.mem_N.2 ⟨_, rfl⟩, mem_range.2 ⟨⟨x, hx⟩, rfl⟩,
      mem_range.2 ⟨⟨powerset x, hPx⟩, rfl⟩, ?_⟩
    · rw [mem_powerset]
      exact ⟨fun h w _ hw => h hw,
        fun h w hw => h w (F.hU.subset hT (mem_powerset.1 hz hw)) hw⟩
    · rw [card_coe_powerset hxfin]
      exact mem_range.2 ⟨_, rfl⟩) A (F.star_subset_U' hFT hA) hA
  have hysub := (F.internal_subset_of_mem_star_finPow hPT hy).1
  have hAsub := (F.internal_subset_of_mem_star_finPow hT hA).1
  have hPI : F.internalPowerset A = y := by
    ext z
    rw [internalPowerset, mem_sep, mem_powerset]
    constructor
    · rintro ⟨hzA, hzint⟩
      have hzP := (F.mem_star_powerset_iff hT).2 ⟨fun w hw => hAsub (hzA hw), hzint⟩
      exact (hymem z (F.star_subset_U' hPT hzP) hzP).2 fun w _ hw => hzA hw
    · intro hzy
      have hzP := hysub hzy
      obtain ⟨hzT, hzint⟩ := (F.mem_star_powerset_iff hT).1 hzP
      exact ⟨fun w hw => (hymem z (F.star_subset_U' hPT hzP) hzP).1 hzy w
        (F.star_subset_U' hT (hzT hw)) hw, hzint⟩
  rw [hPI]
  refine ⟨hy, ?_⟩
  rw [icard, icard, (F.isFunc_star_cardFn hPT).1.isFunction.app_eq hd,
    (F.isFunc_star_cardFn hT).1.isFunction.app_eq hc]
  exact ((F.isFunc_star F.isSetOf_N F.isSetOf_N F.isFunc_powFn).isFunction.app_eq hcd).symm

/-- **Exercise 13.18 (4).** If $`A` is hyperfinite, then so is its internal power set. -/
theorem hyperfinite_internalPowerset' (hA : F.Hyperfinite A) :
    F.Hyperfinite (F.internalPowerset A) :=
  let ⟨T, hT, hAT⟩ := hA
  ⟨powerset T, F.hU.isSetOf_powerset hT, (F.hyperfinite_internalPowerset hT hAT).1⟩

/-- **Exercise 13.18 (3).** Any nonempty hyperfinite subset of $`{}^*\mathbb R` has a
greatest and a least element. The book omits the word nonempty. -/
theorem exists_greatest_least (hB : F.Hyperfinite B) (hBR : B ⊆ F.star F.R) (hne : B ≠ ∅) :
    (∃ y ∈ B, ∀ z ∈ B, pair z y ∈ F.star F.Le) ∧ ∃ y ∈ B, ∀ z ∈ B, pair y z ∈ F.star F.Le := by
  have hFP := F.hU.isSetOf_finPow F.isSetOf_R
  have hBF := hB.mem_star_finPow F.isSetOf_R hBR
  have h := F.transfer
    (.all 0 (.const (finPow F.R)) (.imp (.neg (.equal (.var 0) (.const ∅))) (.conj
      (.ex 1 (.var 0) (.all 2 (.var 0) (.elem (.opair (.var 2) (.var 1)) (.const F.Le))))
      (.ex 1 (.var 0) (.all 2 (.var 0) (.elem (.opair (.var 1) (.var 2)) (.const F.Le)))))))
    (by simp [IsSentence, hFP.1, F.hU.empty_mem, F.isSetOf_Le.1])
  sat_simp at h
  rw [F.star_empty] at h
  have hBU : B ⊆ F.U' := fun y hy => F.star_subset_U' F.isSetOf_R (hBR hy)
  obtain ⟨⟨y, -, hy, hmax⟩, ⟨w, -, hw, hmin⟩⟩ := h.1 (by
    intro x _ hx hne
    obtain ⟨hxR, hxfin⟩ := mem_finPow.1 hx
    have hSfin : {r : ℝ | F.real r ∈ x}.Finite :=
      hxfin.preimage (F.real_injective.injOn (s := {r : ℝ | F.real r ∈ x}))
    have hSne : {r : ℝ | F.real r ∈ x}.Nonempty := by
      obtain ⟨y, hy⟩ := (eq_empty_or_nonempty x).resolve_left hne
      obtain ⟨r, rfl⟩ := F.mem_R.1 (hxR hy)
      exact ⟨r, hy⟩
    obtain ⟨M, hM, hMmax⟩ := Set.exists_max_image _ id hSfin hSne
    obtain ⟨m, hm, hmmin⟩ := Set.exists_min_image _ id hSfin hSne
    refine ⟨⟨F.real M, F.real_mem_U M, hM, fun z _ hz => ?_⟩,
      ⟨F.real m, F.real_mem_U m, hm, fun z _ hz => ?_⟩⟩
    · obtain ⟨r, rfl⟩ := F.mem_R.1 (hxR hz)
      exact F.pair_mem_Le.2 (hMmax r hz)
    · obtain ⟨r, rfl⟩ := F.mem_R.1 (hxR hz)
      exact F.pair_mem_Le.2 (hmmin r hz)) B hB.internal.mem_U' hBF hne
  exact ⟨⟨y, hy, fun z hz => hmax z (hBU hz) hz⟩, ⟨w, hw, fun z hz => hmin z (hBU hz) hz⟩⟩

/-- **Exercise 13.18 (5).** A set $`B` is hyperfinite if and only if there is an internal
surjection $`f : \{1, \dots, n\} \to B` for some $`n \in {}^*\mathbb N`. -/
theorem hyperfinite_iff_surjection :
    F.Hyperfinite B ↔ ∃ n ∈ F.star F.N, ∃ f, F.Internal f ∧ RelIn F.U' f ∧
      IsFunc (F.seg n) B f ∧ ran f = B := by
  constructor
  · intro h
    obtain ⟨n, hn, f, h1, h2, h3, -, h5⟩ := F.hyperfinite_iff.1 h
    exact ⟨n, hn, f, h1, h2, h3, h5⟩
  · rintro ⟨n, hn, f, hfint, hfrel, hfunc, hran⟩
    have : B = relImage f (F.seg n) := by
      ext b
      rw [← hran, mem_ran, mem_relImage]
      exact ⟨fun ⟨a, hab⟩ => ⟨a, (pair_mem_prod.1 (hfunc.1 hab)).1, hab⟩,
        fun ⟨a, _, hab⟩ => ⟨a, hab⟩⟩
    rw [this]
    exact (F.hyperfinite_seg hn).relImage hfint hfrel hfunc.isFunction

end RealFramework

end Goldblatt
