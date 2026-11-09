import Goldblatt.Ch13_Universes.Framework

/-!
# 13 (part 4). Internal Entities: Sections 13.10 to 13.12, 13.15 and 13.16

This is the fourth of five parts of Chapter 13 (the overview is on the chapter page
{lit}`Goldblatt.Ch13_Universes`). It defines internal entities, proves that they form a
strongly transitive collection, establishes the internal set definition principle and the
internal function definition principle, derives the closure properties of internal sets, and
identifies the transform of a power set with the set of internal subsets.

The internal set definition principle is Section 13.15 of the book, but it is proved here
before the closure properties of Section 13.11, because each of those is an instance of it.
The book proves one closure property by hand, as a model for the others, and that argument is
the proof of the principle.
-/

noncomputable section

namespace Goldblatt

open ZFSet

universe u

namespace NonstandardFramework

open Formula Term

variable (F : NonstandardFramework.{u}) {A B C D R S T f a b c x : ZFSet.{u}}

/-!
## 13.10 Internal Entities

An entity of $`\mathbb U'` is internal when it belongs to some standard set, and external
otherwise. Standard entities are internal. The internal entities form a transitive
collection, and more: every internal set is a member, and so a subset, of a transitive
standard set (Theorem 13.10.1).
-/

/-- **Section 13.10, internal entities.** $`a` is internal when $`a \in {}^*B` for some set
$`B \in \mathbb U`. The collection of all internal entities is the book's
$`{}^*\mathbb U`. -/
def Internal (a : ZFSet.{u}) : Prop := ∃ B, IsSetOf F.U B ∧ a ∈ F.star B

/-- **Section 13.10, external entities.** The members of $`\mathbb U'` that are not
internal. -/
def External (a : ZFSet.{u}) : Prop := a ∈ F.U' ∧ ¬ F.Internal a

variable {F}

theorem Internal.mem_U' (h : F.Internal a) : a ∈ F.U' :=
  let ⟨_, hB, ha⟩ := h
  F.star_subset_U' hB ha

variable (F)

/-- **Section 13.10.** Every standard entity is internal, because $`{}^*a \in {}^*\{a\}`. -/
theorem internal_star (ha : a ∈ F.U) : F.Internal (F.star a) :=
  ⟨{a}, F.hU.isSetOf_singleton ha,
    (F.star_mem_star_iff ha (F.hU.isSetOf_singleton ha).1).2 (mem_singleton.2 rfl)⟩

theorem internal_of_standard (h : F.Standard a) : F.Internal a := by
  obtain ⟨b, hb, rfl⟩ := h
  exact F.internal_star hb

/-- Members of standard sets are internal. -/
theorem internal_of_mem_star (hB : IsSetOf F.U B) (ha : a ∈ F.star B) : F.Internal a :=
  ⟨B, hB, ha⟩

/-- Finitely many internal entities all belong to one transitive standard set. -/
theorem exists_transitive_of_internal_list (l : List ZFSet.{u}) (h : ∀ a ∈ l, F.Internal a) :
    ∃ T, IsSetOf F.U T ∧ TransitiveIn F.U T ∧ ∀ a ∈ l, a ∈ F.star T := by
  induction l with
  | nil =>
    exact ⟨∅, F.hU.isSetOf_empty, fun y hy => absurd hy (notMem_empty y), by simp⟩
  | cons a l ih =>
    obtain ⟨T₁, hT₁, -, hl⟩ := ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    obtain ⟨B, hB, haB⟩ := h a (List.mem_cons_self ..)
    have hBT := F.hU.isSetOf_union hB hT₁
    obtain ⟨T, hT, hTt, hsub, hTU⟩ := F.hU.stronglyTransitive _ hBT
    have hTset := isSetOf_of_subset hT hTU
    refine ⟨T, hTset, hTt, fun c hc => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact (F.star_subset_star_iff hB hTset).2 (fun y hy => hsub (mem_union.2 (Or.inl hy))) haB
    · exact (F.star_subset_star_iff hT₁ hTset).2 (fun y hy => hsub (mem_union.2 (Or.inr hy)))
        (hl c hc)

/-- **Theorem 13.10.1 (first part).** Any internal entity belongs to a standard set
$`{}^*T` that is transitive, with $`T` a transitive set of $`\mathbb U`. -/
theorem exists_transitive_of_internal (h : F.Internal a) :
    ∃ T, IsSetOf F.U T ∧ TransitiveIn F.U T ∧ TransitiveIn F.U' (F.star T) ∧ a ∈ F.star T := by
  obtain ⟨T, hT, hTt, hmem⟩ := F.exists_transitive_of_internal_list [a] (by simpa using h)
  exact ⟨T, hT, hTt, F.transitiveIn_star hT hTt, hmem a (by simp)⟩

/-- **Theorem 13.10.1 (second part).** The internal entities are strongly transitive: every
internal set $`A` is included in a transitive internal set, namely a standard set
$`{}^*T`, all of whose members are internal. -/
theorem exists_transitive_superset_of_internal (h : F.Internal A) (hAset : IsSetOf F.U' A) :
    ∃ T', F.Internal T' ∧ TransitiveIn F.U' T' ∧ A ⊆ T' ∧ ∀ x ∈ T', F.Internal x := by
  obtain ⟨T, hT, -, hTt', hAT⟩ := F.exists_transitive_of_internal h
  exact ⟨F.star T, F.internal_star hT.1, hTt',
    fun x hx => hTt' A hAT x hx (F.isUniverse'.subset hAset hx),
    fun x hx => F.internal_of_mem_star hT hx⟩

/-- **Theorem 13.10.1 (third part).** Every member of an internal set is internal. A member
is understood as a member that belongs to $`\mathbb U'`. -/
theorem internal_of_mem_internal (h : F.Internal A) (hx : x ∈ A) (hxU : x ∈ F.U') :
    F.Internal x := by
  obtain ⟨T, hT, -, hTt', hAT⟩ := F.exists_transitive_of_internal h
  exact F.internal_of_mem_star hT (hTt' A hAT x hx hxU)

/-- **Theorem 13.10.1 (third part).** Every member of an internal set is internal. -/
theorem internal_of_mem_internal_set (h : F.Internal A) (hAset : IsSetOf F.U' A) (hx : x ∈ A) :
    F.Internal x :=
  F.internal_of_mem_internal h hx (F.isUniverse'.subset hAset hx)

/-!
## 13.15 Internal Set Definition Principle

If a property is expressed by a formula of the language of $`\mathbb U'` all of whose
constants are internal, then the members of an internal set with that property form an
internal set.

The principle is proved first for a formula that is the transform of a formula of the
language of $`\mathbb U`, with internal entities assigned to its free variables as parameters
({lit}`NonstandardFramework.internal_sep`). The book's proof begins by replacing the internal
constants of a formula by variables, which produces exactly such a formula without constants,
so this is the form the proof actually handles, and it is the convenient form for
applications. The principle for a formula with internal constants
({lit}`NonstandardFramework.internal_sep_of_internal_consts`) is then obtained by carrying
out that replacement.
-/

theorem _root_.Goldblatt.exists_fresh_var (ys : List ℕ) (x : ℕ) :
    ∃ N, x < N ∧ ∀ y ∈ ys, y < N := by
  induction ys with
  | nil => exact ⟨x + 1, Nat.lt_succ_self x, by simp⟩
  | cons y ys ih =>
    obtain ⟨N, h1, h2⟩ := ih
    refine ⟨max N (y + 1), lt_max_of_lt_left h1, fun z hz => ?_⟩
    rcases List.mem_cons.1 hz with rfl | hz
    · exact lt_max_of_lt_right (Nat.lt_succ_self _)
    · exact lt_max_of_lt_left (h2 z hz)

/-- **Section 13.15, internal set definition principle (parameter form).** Let $`\psi` be a
formula of the language of $`\mathbb U` whose free variables are $`x` and the variables in the
list {lit}`ys`, let internal entities be assigned to the variables in {lit}`ys`, and let
$`A` be an internal set. Then
$$`\{a \in A : {}^*\psi(a) \text{ is true}\}`
is internal. -/
theorem internal_sep (ψ : Formula.{u}) (ys : List ℕ) (x : ℕ)
    (hψ : ψ.Admissible F.U (insert x {y | y ∈ ys})) (v : ℕ → ZFSet.{u})
    (hv : ∀ y ∈ ys, F.Internal (v y)) (hA : F.Internal A) (hAset : IsSetOf F.U' A) :
    F.Internal (A.sep fun a => Sat F.U' (Function.update v x a) (ψ.star F.star)) := by
  obtain ⟨N, hxN, hysN⟩ := exists_fresh_var ys x
  obtain ⟨T, hT, hTt, hTmem⟩ := F.exists_transitive_of_internal_list (A :: ys.map v) (by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hA
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
      exact hv y hy)
  have hAT : A ∈ F.star T := hTmem A (List.mem_cons_self ..)
  have hvT : ∀ y ∈ ys, v y ∈ F.star T := fun y hy =>
    hTmem _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨y, hy, rfl⟩))
  have hPT := F.hU.isSetOf_powerset hT
  have hNx : N ≠ x := (ne_of_lt hxN).symm
  have hN1x : N + 1 ≠ x := by omega
  have hNN1 : N ≠ N + 1 := by omega
  set l : List (ℕ × ZFSet.{u}) := (N, T) :: ys.map (fun y => (y, T)) with hl
  let body : Formula.{u} := .ex (N + 1) (.const (powerset T)) (.all x (.const T)
    (.biimp (.elem (.var x) (.var (N + 1))) (.conj (.elem (.var x) (.var N)) ψ)))
  have hlU : ∀ p ∈ l, p.2 ∈ F.U := by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hT.1
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hp
      exact hT.1
  have hfst : ∀ y, y ∈ l.map Prod.fst ↔ y = N ∨ y ∈ ys := by
    intro y
    simp [hl, Function.comp_def]
  have hsent : (alls l body).IsSentence F.U := by
    refine admissible_alls hlU ⟨hPT.1, hT.1, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hψ.mono ?_⟩
    · simp
    · simp
    · simp
    · simp [hfst]
    · intro y hy
      rcases hy with rfl | hy
      · simp
      · have : y ∈ ys := hy
        simp [hfst, this]
  have hU : (alls l body).Holds F.U := by
    rw [Holds, sat_alls]
    intro w _
    simp only [body, Sat, Term.Defined, Term.val, true_and, forall_true_left,
      Function.update_self, Function.update_of_ne hN1x, Function.update_of_ne hNx,
      Function.update_of_ne hNN1]
    refine ⟨T.sep fun a => a ∈ w N ∧ Sat F.U (Function.update w x a) ψ,
      (F.hU.isSetOf_sep hT _).1, mem_powerset.2 sep_subset, fun a _ haT => ?_⟩
    rw [mem_sep]
    have : Sat F.U (Function.update (Function.update w (N + 1)
        (T.sep fun a => a ∈ w N ∧ Sat F.U (Function.update w x a) ψ)) x a) ψ ↔
        Sat F.U (Function.update w x a) ψ := sat_congr hψ fun y hy => by
      rcases hy with rfl | hy
      · simp
      · have hy' : y ∈ ys := hy
        have h1 : y ≠ N + 1 := by have := hysN y hy'; omega
        by_cases hyx : y = x
        · subst hyx; simp
        · simp [Function.update_of_ne hyx, Function.update_of_ne h1]
    rw [this]
    exact ⟨fun h => h.2, fun h => ⟨haT, h⟩⟩
  have h' := (F.transfer _ hsent).1 hU
  rw [holds_iff_sat (hsent.star F.star_mem) (Function.update v N A), star_alls, sat_alls] at h'
  have hw : Function.update v N A ∈
      reach F.U' (l.map fun p => (p.1, F.star p.2)) (Function.update v N A) := by
    refine mem_reach_of (fun p hp => ?_) (fun _ _ => rfl)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    rcases List.mem_cons.1 hq with rfl | hq
    · simp only [Function.update_self]
      exact ⟨hA.mem_U', hAT⟩
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hq
      have : y ≠ N := (hysN y hy).ne
      simp only [Function.update_of_ne this]
      exact ⟨F.star_subset_U' hT (hvT y hy), hvT y hy⟩
  have h'' := h' _ hw
  simp only [body, Formula.star, Term.star, Sat, Term.Defined, Term.val, true_and,
    forall_true_left, Function.update_self, Function.update_of_ne hN1x,
    Function.update_of_ne hNx, Function.update_of_ne hNN1] at h''
  obtain ⟨Z, -, hZ, hZmem⟩ := h''
  have hZsub := mem_powerset.1 (F.star_powerset_subset hT hZ)
  have hTt' := F.transitiveIn_star hT hTt
  have hAsub : A ⊆ F.star T := fun a ha => hTt' A hAT a ha (F.isUniverse'.subset hAset ha)
  have hcongr : ∀ a, Sat F.U' (Function.update (Function.update (Function.update v N A)
      (N + 1) Z) x a) (ψ.star F.star) ↔ Sat F.U' (Function.update v x a) (ψ.star F.star) :=
    fun a => sat_congr (hψ.star F.star_mem) fun y hy => by
      rcases hy with rfl | hy
      · simp
      · have hy' : y ∈ ys := hy
        have h1 : y ≠ N + 1 := by have := hysN y hy'; omega
        have h2 : y ≠ N := (hysN y hy').ne
        by_cases hyx : y = x
        · subst hyx; simp
        · simp [Function.update_of_ne hyx, Function.update_of_ne h1, Function.update_of_ne h2]
  have : (A.sep fun a => Sat F.U' (Function.update v x a) (ψ.star F.star)) = Z := by
    ext a
    rw [mem_sep]
    constructor
    · rintro ⟨haA, hs⟩
      exact (hZmem a (F.isUniverse'.subset hAset haA) (hAsub haA)).2 ⟨haA, (hcongr a).2 hs⟩
    · intro haZ
      have := (hZmem a (F.star_subset_U' hT (hZsub haZ)) (hZsub haZ)).1 haZ
      exact ⟨this.1, (hcongr a).1 this.2⟩
  rw [this]
  exact ⟨powerset T, hPT, hZ⟩

/-- **Section 13.15, internal set definition principle.** If $`\varphi(x)` is an internal
formula of the language of $`\mathbb U'` (all of its constants are internal) with $`x` the
only free variable, then for any internal set $`A` the set
$$`\{a \in A : \varphi(a) \text{ is true}\}`
is internal. As in the book, the proof replaces the constants of $`\varphi` by new variables
and applies the parameter form of the principle. -/
theorem internal_sep_of_internal_consts (φ : Formula.{u}) (x : ℕ)
    (hφ : φ.Admissible F.U' {x}) (hconsts : φ.ConstsSat F.Internal) (v : ℕ → ZFSet.{u})
    (hA : F.Internal A) (hAset : IsSetOf F.U' A) :
    F.Internal (A.sep fun a => Sat F.U' (Function.update v x a) φ) := by
  classical
  obtain ⟨N₀, hN₀⟩ := hconsts
  obtain ⟨N₁, L, hL, hB₁⟩ := Formula.exists_below hN₀
  set N := max N₁ (x + 1) with hN
  have hxN : x < N := lt_of_lt_of_le (Nat.lt_succ_self x) (le_max_right _ _)
  have hB : φ.Below N (· ∈ L) := hB₁.mono (le_max_left _ _) fun _ h => h
  let e : ZFSet.{u} → ℕ := fun c => N + L.idxOf c
  let w : ℕ → ZFSet.{u} := fun n => if n < N then v n else L.getD (n - N) ∅
  have hwe : ∀ c ∈ L, w (e c) = c := by
    intro c hc
    have h1 : ¬ N + L.idxOf c < N := by omega
    simp only [w, e, h1, ite_false, Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hc), List.getElem_idxOf]
  have he : ∀ c ∈ L, N ≤ e c := fun c _ => Nat.le_add_right _ _
  have hwx : ∀ a, ∀ c ∈ L, N ≤ e c ∧ Function.update w x a (e c) = c := fun a c hc =>
    ⟨he c hc, by
      have := he c hc
      rw [Function.update_of_ne (by omega)]
      exact hwe c hc⟩
  have hadm : (φ.abs e).Admissible F.U (insert x {y | y ∈ L.map e}) :=
    (Formula.admissible_abs hφ hB he).mono fun n hn => by
      rcases hn with hn | ⟨c, hc, rfl⟩
      · exact Or.inl hn
      · exact Or.inr (List.mem_map.2 ⟨c, hc, rfl⟩)
  have hv : ∀ y ∈ L.map e, F.Internal (w y) := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    rw [hwe c hc]
    exact hL c hc
  have := F.internal_sep (φ.abs e) (L.map e) x hadm w hv hA hAset
  rw [Formula.star_abs] at this
  have hsat : ∀ a, Sat F.U' (Function.update w x a) (φ.abs e) ↔
      Sat F.U' (Function.update v x a) φ := fun a => by
    rw [Formula.sat_abs hB (hwx a)]
    exact Formula.sat_congr hφ fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]
      simp
  simpa only [hsat] using this

/-!
## 13.11 Closure Properties of Internal Sets

Internal sets are closed under the Boolean operations and products, under unions and
intersections of internal collections, under forming finite sets and tuples, and under the
operations on relations and functions. Each statement follows from the internal set
definition principle applied inside a transitive standard set that contains the given
internal entities.
-/

/-- Finitely many internal entities lie in one standard set $`{}^*T` which includes every
set among them and whose square includes every relation among them. -/
theorem exists_ambient (l : List ZFSet.{u}) (h : ∀ a ∈ l, F.Internal a) :
    ∃ T, IsSetOf F.U T ∧ (∀ a ∈ l, a ∈ F.star T) ∧
      (∀ a ∈ l, IsSetOf F.U' a → a ⊆ F.star T) ∧
      ∀ R ∈ l, IsSetOf F.U' R → RelIn F.U' R → R ⊆ prod (F.star T) (F.star T) := by
  obtain ⟨T, hT, hTt, hmem⟩ := F.exists_transitive_of_internal_list l h
  have hTt' := F.transitiveIn_star hT hTt
  have hsub : ∀ a ∈ l, IsSetOf F.U' a → a ⊆ F.star T := fun a ha haset x hx =>
    hTt' a (hmem a ha) x hx (F.isUniverse'.subset haset hx)
  refine ⟨T, hT, hmem, hsub, fun R hR hRset hrel p hp => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := hrel p hp
  have hpT := hsub R hR hRset hp
  have h1 : ({a} : ZFSet.{u}) ∈ F.star T :=
    hTt' _ hpT _ singleton_mem_pair (F.isUniverse'.isSetOf_singleton ha).1
  have h2 : ({a, b} : ZFSet.{u}) ∈ F.star T :=
    hTt' _ hpT _ pair_mem_pair (F.isUniverse'.isSetOf_pair ha hb).1
  exact pair_mem_prod.2 ⟨hTt' _ h1 a (mem_singleton.2 rfl) ha, hTt' _ h2 b (by simp) hb⟩

/-- **Section 13.11 (1a).** The intersection of two internal sets is internal. -/
theorem internal_inter (hA : F.Internal A) (hAset : IsSetOf F.U' A) (hB : F.Internal B) :
    F.Internal (A ∩ B) := by
  have := F.internal_sep (.elem (.var 0) (.var 1)) [1] 0 (by simp) (fun _ => B) (by simp [hB])
    hA hAset
  sat_simp at this
  exact this

/-- **Section 13.11 (1c).** The difference of two internal sets is internal. -/
theorem internal_sdiff (hA : F.Internal A) (hAset : IsSetOf F.U' A) (hB : F.Internal B) :
    F.Internal (A \ B) := by
  have := F.internal_sep (.neg (.elem (.var 0) (.var 1))) [1] 0 (by simp) (fun _ => B)
    (by simp [hB]) hA hAset
  sat_simp at this
  exact this

/-- **Section 13.11 (1b).** The union of two internal sets is internal. This is the closure
property the book proves in detail. -/
theorem internal_union (hA : F.Internal A) (hAset : IsSetOf F.U' A) (hB : F.Internal B)
    (hBset : IsSetOf F.U' B) : F.Internal (A ∪ B) := by
  obtain ⟨T, hT, -, hsub, -⟩ := F.exists_ambient [A, B] (by simp [hA, hB])
  have := F.internal_sep (.disj (.elem (.var 0) (.var 1)) (.elem (.var 0) (.var 2))) [1, 2] 0
    (by simp) (Function.update (fun _ => B) 1 A) (by simp [hA, hB]) (F.internal_star hT.1)
    (F.isSetOf_star hT)
  sat_simp at this
  have e : A ∪ B = (F.star T).sep fun a => a ∈ A ∨ a ∈ B := by
    ext a
    rw [mem_union, mem_sep]
    refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    rcases h with h | h
    · exact hsub A (by simp) hAset h
    · exact hsub B (by simp) hBset h
  rw [e]
  exact this

/-- **Section 13.11 (1d).** The Cartesian product of two internal sets is internal. -/
theorem internal_prod (hA : F.Internal A) (hAset : IsSetOf F.U' A) (hB : F.Internal B)
    (hBset : IsSetOf F.U' B) : F.Internal (prod A B) := by
  obtain ⟨T, hT, -, hsub, -⟩ := F.exists_ambient [A, B] (by simp [hA, hB])
  have hP := F.hU.isSetOf_prod hT hT
  have := F.internal_sep (.ex 3 (.var 1) (.ex 4 (.var 2)
      (.equal (.var 0) (.opair (.var 3) (.var 4))))) [1, 2] 0
    (by simp) (Function.update (fun _ => B) 1 A) (by simp [hA, hB]) (F.internal_star hP.1)
    (F.isSetOf_star hP)
  sat_simp at this
  have e : prod A B = (F.star (prod T T)).sep fun p =>
      ∃ a ∈ F.U', a ∈ A ∧ ∃ b ∈ F.U', b ∈ B ∧ p = pair a b := by
    ext p
    rw [mem_prod, mem_sep, F.star_prod hT hT]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨pair_mem_prod.2 ⟨hsub A (by simp) hAset ha, hsub B (by simp) hBset hb⟩, a,
        F.isUniverse'.subset hAset ha, ha, b, F.isUniverse'.subset hBset hb, hb, rfl⟩
    · rintro ⟨-, a, -, ha, b, -, hb, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  rw [e]
  exact this

/-- **Section 13.11 (2a).** The union of an internal collection of sets is internal. That
the collection itself is internal is essential; a collection of internal sets does not
suffice. -/
theorem internal_sUnion (hA : F.Internal A) (hAset : IsSetOf F.U' A)
    (hsets : ∀ s ∈ A, IsSetOf F.U' s) : F.Internal (⋃₀ A) := by
  obtain ⟨T, hT, hTt, hTt', hAT⟩ := F.exists_transitive_of_internal hA
  have := F.internal_sep (.ex 2 (.var 1) (.elem (.var 0) (.var 2))) [1] 0
    (by simp) (fun _ => A) (by simp [hA]) (F.internal_star hT.1) (F.isSetOf_star hT)
  sat_simp at this
  have e : ⋃₀ A = (F.star T).sep fun a => ∃ s ∈ F.U', s ∈ A ∧ a ∈ s := by
    ext a
    rw [mem_sUnion, mem_sep]
    constructor
    · rintro ⟨s, hs, has⟩
      have hsU := F.isUniverse'.subset hAset hs
      have hsT := hTt' A hAT s hs hsU
      exact ⟨hTt' s hsT a has (F.isUniverse'.subset (hsets s hs) has), s, hsU, hs, has⟩
    · rintro ⟨-, s, -, hs, has⟩
      exact ⟨s, hs, has⟩
  rw [e]
  exact this

theorem sUnion_subset_U' (hsets : ∀ s ∈ A, IsSetOf F.U' s) : ⋃₀ A ⊆ F.U' := fun _ ha =>
  let ⟨s, hs, has⟩ := mem_sUnion.1 ha
  F.isUniverse'.subset (hsets s hs) has

/-- **Section 13.11 (2b).** The intersection of an internal collection of sets is
internal. -/
theorem internal_sInter (hA : F.Internal A) (hAset : IsSetOf F.U' A)
    (hsets : ∀ s ∈ A, IsSetOf F.U' s) : F.Internal (⋂₀ A) := by
  have hU := F.internal_sUnion hA hAset hsets
  have := F.internal_sep (.all 2 (.var 1) (.elem (.var 0) (.var 2))) [1] 0
    (by simp) (fun _ => A) (by simp [hA]) hU
    (isSetOf_of_subset hU.mem_U' (F.sUnion_subset_U' hsets))
  sat_simp at this
  have e : ⋂₀ A = (⋃₀ A).sep fun a => ∀ s ∈ F.U', s ∈ A → a ∈ s := by
    ext a
    simp only [sInter, mem_sep]
    exact and_congr_right fun _ => ⟨fun h s _ hs => h s hs,
      fun h s hs => h s (F.isUniverse'.subset hAset hs) hs⟩
  rw [e]
  exact this

/-- **Section 13.11 (3), one element.** If $`a` is internal then $`\{a\}` is internal. -/
theorem internal_singleton (ha : F.Internal a) : F.Internal ({a} : ZFSet.{u}) := by
  obtain ⟨T, hT, haT⟩ := ha
  have := F.internal_sep (.equal (.var 0) (.var 1)) [1] 0
    (by simp) (fun _ => a) (by simpa using F.internal_of_mem_star hT haT) (F.internal_star hT.1)
    (F.isSetOf_star hT)
  sat_simp at this
  have e : ({a} : ZFSet.{u}) = (F.star T).sep fun x => x = a := by
    ext x
    rw [mem_singleton, mem_sep]
    exact ⟨fun h => ⟨h ▸ haT, h⟩, fun h => h.2⟩
  rw [e]
  exact this

/-- Inserting an internal entity into an internal set gives an internal set. -/
theorem internal_insert (ha : F.Internal a) (hA : F.Internal A) (hAset : IsSetOf F.U' A) :
    F.Internal (insert a A) := by
  rw [insert_eq]
  exact F.internal_union (F.internal_singleton ha)
    (F.isUniverse'.isSetOf_singleton ha.mem_U') hA hAset

/-- **Section 13.11 (3).** If $`a_1, \dots, a_m` are internal, then so is the finite set
$`\{a_1, \dots, a_m\}`: a finite set of internal entities is internal. -/
theorem internal_of_finite (hfin : (A : Set ZFSet.{u}).Finite) (h : ∀ a ∈ A, F.Internal a) :
    F.Internal A := by
  generalize hs : (A : Set ZFSet.{u}) = s at hfin
  induction s, hfin using Set.Finite.induction_on generalizing A with
  | empty =>
    have : A = ∅ := by
      rw [eq_empty]
      intro y hy
      have : y ∈ (A : Set ZFSet.{u}) := hy
      rw [hs] at this
      exact this
    rw [this, ← F.star_empty]
    exact F.internal_star F.hU.empty_mem
  | @insert a s _ _ ih =>
    have hmem : ∀ x, x ∈ A ↔ x = a ∨ x ∈ s := fun x => by
      rw [← SetLike.mem_coe, hs, Set.mem_insert_iff]
    have hA' : F.Internal (A.sep fun x => x ∈ s) :=
      ih (fun x hx => h x (mem_sep.1 hx).1) (by
        ext x
        simp only [SetLike.mem_coe, mem_sep, hmem]
        tauto)
    have : A = insert a (A.sep fun x => x ∈ s) := by
      ext x
      simp only [mem_insert_iff, mem_sep, hmem]
      tauto
    rw [this]
    exact F.internal_insert (h a ((hmem a).2 (Or.inl rfl))) hA'
      (isSetOf_of_subset hA'.mem_U' fun x hx => (h x (mem_sep.1 hx).1).mem_U')

/-- The ordered pair of two internal entities is internal. -/
theorem internal_opair (ha : F.Internal a) (hb : F.Internal b) : F.Internal (pair a b) := by
  refine F.internal_of_finite (A := pair a b) ?_ fun x hx => ?_
  · simp [pair]
  · rcases mem_pair.1 hx with rfl | rfl
    · exact F.internal_singleton ha
    · exact F.internal_of_finite (by simp) fun y hy => by
        rcases mem_pair.1 hy with rfl | rfl <;> assumption

/-- **Section 13.11 (3).** If $`a_1, \dots, a_m` are internal, then so is the tuple
$`(a_1, \dots, a_m)`. -/
theorem internal_tuple (m : ℕ) (a : Fin m → ZFSet.{u}) (ha : ∀ i, F.Internal (a i)) :
    F.Internal (tuple m a) := by
  by_cases hm : m = 2
  · subst hm
    rw [tuple_two]
    exact F.internal_opair (ha 0) (ha 1)
  · refine F.internal_of_finite ?_ fun p hp => ?_
    · simp only [tuple, hm, ↓reduceDIte, coe_range]
      exact Set.finite_range _
    · obtain ⟨i, rfl⟩ := (mem_tuple hm).1 hp
      refine F.internal_opair ?_ (ha i)
      rw [← F.star_num]
      exact F.internal_star (F.hU.isSetOf_num _).1

/-- **Section 13.11 (4a).** The domain of an internal binary relation is internal. -/
theorem internal_dom (hR : F.Internal R) (hRset : IsSetOf F.U' R) (hrel : RelIn F.U' R) :
    F.Internal (dom R) := by
  obtain ⟨T, hT, -, -, hRT⟩ := F.exists_ambient [R] (by simp [hR])
  have hRT := hRT R (by simp) hRset hrel
  have := F.internal_sep (.ex 2 (.const T) (.elem (.opair (.var 0) (.var 2)) (.var 1))) [1] 0
    (by simp [hT.1]) (fun _ => R) (by simp [hR]) (F.internal_star hT.1) (F.isSetOf_star hT)
  sat_simp at this
  have e : dom R = (F.star T).sep fun a => ∃ b ∈ F.U', b ∈ F.star T ∧ pair a b ∈ R := by
    ext a
    rw [mem_dom, mem_sep]
    constructor
    · rintro ⟨b, hab⟩
      have := pair_mem_prod.1 (hRT hab)
      exact ⟨this.1, b, F.star_subset_U' hT this.2, this.2, hab⟩
    · rintro ⟨-, b, -, -, hab⟩
      exact ⟨b, hab⟩
  rw [e]
  exact this

/-- **Section 13.11 (4b).** The range of an internal binary relation is internal. -/
theorem internal_ran (hR : F.Internal R) (hRset : IsSetOf F.U' R) (hrel : RelIn F.U' R) :
    F.Internal (ran R) := by
  obtain ⟨T, hT, -, -, hRT⟩ := F.exists_ambient [R] (by simp [hR])
  have hRT := hRT R (by simp) hRset hrel
  have := F.internal_sep (.ex 2 (.const T) (.elem (.opair (.var 2) (.var 0)) (.var 1))) [1] 0
    (by simp [hT.1]) (fun _ => R) (by simp [hR]) (F.internal_star hT.1) (F.isSetOf_star hT)
  sat_simp at this
  have e : ran R = (F.star T).sep fun b => ∃ a ∈ F.U', a ∈ F.star T ∧ pair a b ∈ R := by
    ext b
    rw [mem_ran, mem_sep]
    constructor
    · rintro ⟨a, hab⟩
      have := pair_mem_prod.1 (hRT hab)
      exact ⟨this.2, a, F.star_subset_U' hT this.1, this.1, hab⟩
    · rintro ⟨-, a, -, -, hab⟩
      exact ⟨a, hab⟩
  rw [e]
  exact this

/-- **Section 13.11 (4c).** The inverse of an internal binary relation is internal. -/
theorem internal_relInv (hR : F.Internal R) (hRset : IsSetOf F.U' R) (hrel : RelIn F.U' R) :
    F.Internal (relInv R) := by
  obtain ⟨T, hT, -, -, hRT⟩ := F.exists_ambient [R] (by simp [hR])
  have hRT := hRT R (by simp) hRset hrel
  have hP := F.hU.isSetOf_prod hT hT
  have := F.internal_sep (.ex 2 (.const T) (.ex 3 (.const T)
      (.conj (.equal (.var 0) (.opair (.var 3) (.var 2)))
        (.elem (.opair (.var 2) (.var 3)) (.var 1))))) [1] 0
    (by simp [hT.1]) (fun _ => R) (by simp [hR]) (F.internal_star hP.1) (F.isSetOf_star hP)
  sat_simp at this
  have e : relInv R = (F.star (prod T T)).sep fun p => ∃ a ∈ F.U', a ∈ F.star T ∧
      ∃ b ∈ F.U', b ∈ F.star T ∧ p = pair b a ∧ pair a b ∈ R := by
    ext p
    rw [mem_relInv, mem_sep, F.star_prod hT hT]
    constructor
    · rintro ⟨a, b, rfl, hab⟩
      have := pair_mem_prod.1 (hRT hab)
      exact ⟨pair_mem_prod.2 ⟨this.2, this.1⟩, a, F.star_subset_U' hT this.1, this.1, b,
        F.star_subset_U' hT this.2, this.2, rfl, hab⟩
    · rintro ⟨-, a, -, -, b, -, -, rfl, hab⟩
      exact ⟨a, b, rfl, hab⟩
  rw [e]
  exact this

/-- **Section 13.11 (4d).** The image $`R'(C)` of an internal set under an internal binary
relation is internal. The book takes $`C \subseteq \operatorname{dom} R`; this is not
needed. -/
theorem internal_relImage (hR : F.Internal R) (hRset : IsSetOf F.U' R) (hrel : RelIn F.U' R)
    (hC : F.Internal C) : F.Internal (relImage R C) := by
  obtain ⟨T, hT, -, -, hRT⟩ := F.exists_ambient [R] (by simp [hR])
  have hRT := hRT R (by simp) hRset hrel
  have := F.internal_sep (.ex 3 (.var 2) (.elem (.opair (.var 3) (.var 0)) (.var 1))) [1, 2] 0
    (by simp) (Function.update (fun _ => C) 1 R) (by simp [hR, hC]) (F.internal_star hT.1)
    (F.isSetOf_star hT)
  sat_simp at this
  have e : relImage R C = (F.star T).sep fun b => ∃ a ∈ F.U', a ∈ C ∧ pair a b ∈ R := by
    ext b
    rw [mem_relImage, mem_sep]
    constructor
    · rintro ⟨a, ha, hab⟩
      have := pair_mem_prod.1 (hRT hab)
      exact ⟨this.2, a, F.star_subset_U' hT this.1, ha, hab⟩
    · rintro ⟨-, a, -, ha, hab⟩
      exact ⟨a, ha, hab⟩
  rw [e]
  exact this

/-- **Section 13.11 (6c).** The inverse image of an internal set under an internal binary
relation, in particular under an internal function, is internal. -/
theorem internal_relPreimage (hR : F.Internal R) (hRset : IsSetOf F.U' R)
    (hrel : RelIn F.U' R) (hD : F.Internal D) : F.Internal (relPreimage R D) := by
  obtain ⟨T, hT, -, -, hRT⟩ := F.exists_ambient [R] (by simp [hR])
  have hRT := hRT R (by simp) hRset hrel
  have := F.internal_sep (.ex 3 (.var 2) (.elem (.opair (.var 0) (.var 3)) (.var 1))) [1, 2] 0
    (by simp) (Function.update (fun _ => D) 1 R) (by simp [hR, hD]) (F.internal_star hT.1)
    (F.isSetOf_star hT)
  sat_simp at this
  have e : relPreimage R D = (F.star T).sep fun a => ∃ b ∈ F.U', b ∈ D ∧ pair a b ∈ R := by
    ext a
    rw [mem_relPreimage, mem_sep]
    constructor
    · rintro ⟨b, hb, hab⟩
      have := pair_mem_prod.1 (hRT hab)
      exact ⟨this.1, b, F.star_subset_U' hT this.2, hb, hab⟩
    · rintro ⟨-, b, -, hb, hab⟩
      exact ⟨b, hb, hab⟩
  rw [e]
  exact this

/-- **Section 13.11 (5).** The composition of two internal binary relations is internal. -/
theorem internal_relComp (hR : F.Internal R) (hRset : IsSetOf F.U' R) (hrel : RelIn F.U' R)
    (hS : F.Internal S) (hSset : IsSetOf F.U' S) (hrelS : RelIn F.U' S) :
    F.Internal (relComp R S) := by
  obtain ⟨T, hT, -, -, hT'⟩ := F.exists_ambient [R, S] (by simp [hR, hS])
  have hRT := hT' R (by simp) hRset hrel
  have hST := hT' S (by simp) hSset hrelS
  have hP := F.hU.isSetOf_prod hT hT
  have := F.internal_sep (.ex 3 (.const T) (.ex 4 (.const T) (.ex 5 (.const T)
      (.conj (.equal (.var 0) (.opair (.var 3) (.var 5)))
        (.conj (.elem (.opair (.var 3) (.var 4)) (.var 1))
          (.elem (.opair (.var 4) (.var 5)) (.var 2))))))) [1, 2] 0
    (by simp [hT.1]) (Function.update (fun _ => S) 1 R) (by simp [hR, hS])
    (F.internal_star hP.1) (F.isSetOf_star hP)
  sat_simp at this
  have e : relComp R S = (F.star (prod T T)).sep fun p => ∃ a ∈ F.U', a ∈ F.star T ∧
      ∃ b ∈ F.U', b ∈ F.star T ∧ ∃ c ∈ F.U', c ∈ F.star T ∧
        p = pair a c ∧ pair a b ∈ R ∧ pair b c ∈ S := by
    ext p
    rw [mem_relComp, mem_sep, F.star_prod hT hT]
    constructor
    · rintro ⟨a, b, c, rfl, hab, hbc⟩
      have h1 := pair_mem_prod.1 (hRT hab)
      have h2 := pair_mem_prod.1 (hST hbc)
      exact ⟨pair_mem_prod.2 ⟨h1.1, h2.2⟩, a, F.star_subset_U' hT h1.1, h1.1, b,
        F.star_subset_U' hT h1.2, h1.2, c, F.star_subset_U' hT h2.2, h2.2, rfl, hab, hbc⟩
    · rintro ⟨-, a, -, -, b, -, -, c, -, -, rfl, hab, hbc⟩
      exact ⟨a, b, c, rfl, hab, hbc⟩
  rw [e]
  exact this

/-- **Section 13.11 (6a).** If a function $`f` is internal and $`a` is in its domain, then
$`f(a)` is internal. -/
theorem internal_app (hf : F.Internal f) (hfset : IsSetOf F.U' f) (hrel : RelIn F.U' f)
    (hfun : IsFunction f) (ha : a ∈ dom f) : F.Internal (app f a) := by
  obtain ⟨T, hT, -, -, hfT⟩ := F.exists_ambient [f] (by simp [hf])
  exact F.internal_of_mem_star hT
    (pair_mem_prod.1 (hfT f (by simp) hfset hrel (hfun.pair_app_mem ha))).2

/-- **Section 13.11 (6b).** The image $`f'(C)` of an internal set under an internal function
is internal. -/
theorem internal_image (hf : F.Internal f) (hfset : IsSetOf F.U' f) (hrel : RelIn F.U' f)
    (hC : F.Internal C) : F.Internal (relImage f C) :=
  F.internal_relImage hf hfset hrel hC

/-!
## 13.12 Transformed Power Sets

The internal entities do not form a universe, because they are not closed under power sets.
The transform of the power set of $`A` is not the power set of $`{}^*A` but the set of its
internal subsets (Theorem 13.12.1). Consequently a statement about all subsets of $`A`
transfers to a statement about all internal subsets of $`{}^*A`; this is how the internal
least number principle and internal induction arise, and they are derived this way in
part 5.
-/

/-- **Theorem 13.12.1.** $`{}^*\mathcal P(A)` is the set of all internal subsets of
$`{}^*A`:
$$`{}^*\mathcal P(A) = \mathcal P({}^*A) \cap {}^*\mathbb U
  = \{B \subseteq {}^*A : B \text{ is internal}\}.`
The sentence transferred in the proof carries the extra clause that $`x` is a set, which the
book leaves implicit. -/
theorem mem_star_powerset_iff (hA : IsSetOf F.U A) :
    b ∈ F.star (powerset A) ↔ b ⊆ F.star A ∧ F.Internal b := by
  have hP := F.hU.isSetOf_powerset hA
  constructor
  · exact fun hb => ⟨mem_powerset.1 (F.star_powerset_subset hA hb), F.internal_of_mem_star hP hb⟩
  · rintro ⟨hbA, C, hC, hbC⟩
    have h := F.transfer
      (.all 0 (.const C) (.imp (.conj
          (.disj (.equal (.var 0) (.const ∅)) (.ex 1 (.var 0) (.equal (.var 1) (.var 1))))
          (.all 1 (.var 0) (.elem (.var 1) (.const A))))
        (.elem (.var 0) (.const (powerset A)))))
      (by simp [IsSentence, hC.1, hA.1, hP.1, F.hU.empty_mem])
    sat_simp at h
    rw [F.star_empty] at h
    have h' := h.1 (by
      rintro x hx - ⟨hset, hsub⟩
      rw [mem_powerset]
      rcases hset with rfl | ⟨y, hy, hyx⟩
      · exact empty_subset _
      · have hxset : IsSetOf F.U x := ⟨hx, fun hi => hi.2 y hy hyx⟩
        exact fun z hz => hsub z (F.hU.subset hxset hz) hz)
    refine h' b (F.star_subset_U' hC hbC) hbC ⟨?_, fun y _ hy => hbA hy⟩
    rcases eq_empty_or_nonempty b with rfl | ⟨y, hy⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨y, F.star_subset_U' hA (hbA hy), hy⟩

/-- **Section 13.12.** The three sets derived from a power set are nested:
$`\operatorname{im} \mathcal P(A) \subseteq {}^*\mathcal P(A) \subseteq
\mathcal P({}^*A)`. -/
theorem im_powerset_subset (hA : IsSetOf F.U A) :
    F.im (powerset A) ⊆ F.star (powerset A) ∧ F.star (powerset A) ⊆ powerset (F.star A) :=
  ⟨F.im_subset_star (F.hU.isSetOf_powerset hA), F.star_powerset_subset hA⟩

/-- **Section 13.12.** The image of $`\mathcal P(A)` is the collection of all standard
subsets of $`{}^*A`. -/
theorem mem_im_powerset_iff (hA : IsSetOf F.U A) :
    b ∈ F.im (powerset A) ↔ b ⊆ F.star A ∧ F.Standard b := by
  rw [F.mem_im_iff (F.hU.isSetOf_powerset hA), F.mem_star_powerset_iff hA]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, F.internal_of_standard h.2⟩, h.2⟩⟩

/-- **Exercise 13.14.3.** If $`A` is finite then $`{}^*\mathcal P(A) = \mathcal P({}^*A)`:
every subset of $`{}^*A = \{{}^*a : a \in A\}` is the transform of a subset of $`A`. -/
theorem star_powerset_eq_of_finite (hA : IsSetOf F.U A) (hfin : (A : Set ZFSet.{u}).Finite) :
    F.star (powerset A) = powerset (F.star A) := by
  refine le_antisymm (F.star_powerset_subset hA) fun b hb => ?_
  rw [mem_powerset] at hb
  have hA₀ : IsSetOf F.U (A.sep fun a => F.star a ∈ b) := F.hU.isSetOf_sep hA _
  have hfin₀ : ((A.sep fun a => F.star a ∈ b : ZFSet.{u}) : Set ZFSet.{u}).Finite :=
    hfin.subset fun x hx => (mem_sep.1 hx).1
  have : b = F.star (A.sep fun a => F.star a ∈ b) := by
    ext x
    rw [F.mem_star_of_finite hA₀ hfin₀]
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := (F.mem_star_of_finite hA hfin).1 (hb hx)
      exact ⟨a, mem_sep.2 ⟨ha, hx⟩, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact (mem_sep.1 ha).2
  rw [this]
  exact (F.star_mem_star_iff hA₀.1 (F.hU.isSetOf_powerset hA).1).2 (mem_powerset.2 sep_subset)

/-!
## 13.16 Internal Function Definition Principle

A function between internal sets whose values are given by a term with internal constants is
an internal function, because its graph is cut out of the internal product of domain and
codomain by a formula with internal constants. As for sets, the principle is proved first
for the transform of a term of the language of $`\mathbb U` with internal entities assigned
to its parameters, and then for a term with internal constants.
-/

/-- **Section 13.16, internal function definition principle.** Let $`f : A \to B` be a
function between internal sets, and let $`\tau(x)` be a term (the transform of a term $`t` of
the language of $`\mathbb U`, with internal entities assigned to its variables other than
$`x`) such that $`f(a) = \tau(a)` for all $`a \in A`. Then $`f` is internal. -/
theorem internal_of_term (t : Term.{u}) (ys : List ℕ) (x : ℕ)
    (ht : t.Admissible F.U (insert x {y | y ∈ ys})) (v : ℕ → ZFSet.{u})
    (hv : ∀ y ∈ ys, F.Internal (v y)) (hA : F.Internal A) (hAset : IsSetOf F.U' A)
    (hB : F.Internal B) (hBset : IsSetOf F.U' B) (hf : IsFunc A B f)
    (hval : ∀ a ∈ A, (t.star F.star).Defined F.U' (Function.update v x a) ∧
      app f a = (t.star F.star).val (Function.update v x a)) : F.Internal f := by
  obtain ⟨N, hxN, hysN⟩ := exists_fresh_var ys x
  have h0 : x ≠ N := by omega
  have h1 : x ≠ N + 1 := by omega
  have h2 : x ≠ N + 2 := by omega
  have h3 : x ≠ N + 3 := by omega
  let ψ : Formula.{u} := .ex x (.var (N + 1)) (.ex (N + 3) (.var (N + 2))
    (.conj (.equal (.var N) (.opair (.var x) (.var (N + 3)))) (.equal (.var (N + 3)) t)))
  let v' : ℕ → ZFSet.{u} := Function.update (Function.update v (N + 1) A) (N + 2) B
  let env : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ℕ → ZFSet.{u} := fun c a b =>
    Function.update (Function.update (Function.update v' N c) x a) (N + 3) b
  have hP := F.internal_prod hA hAset hB hBset
  have hPset : IsSetOf F.U' (prod A B) := isSetOf_of_subset hP.mem_U' fun p hp => by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 hp
    exact (F.isUniverse'.isSetOf_opair (F.isUniverse'.subset hAset ha)
      (F.isUniverse'.subset hBset hb)).1
  have hadm : ψ.Admissible F.U (insert N {y | y ∈ (N + 1) :: (N + 2) :: ys}) := by
    simp only [ψ, Formula.Admissible, Term.Admissible, Term.admissible_opair]
    refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ht.mono ?_⟩
    · simp [h1.symm]
    · simp
    · simp
    · simp
    · simp
    · simp
    · intro y hy
      rcases hy with rfl | hy
      · simp
      · have : y ∈ ys := hy
        simp [this]
  have hv' : ∀ y ∈ (N + 1) :: (N + 2) :: ys, F.Internal (v' y) := by
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · simpa [v', Function.update_apply] using hA
    · rcases List.mem_cons.1 hy with rfl | hy
      · simpa [v', Function.update_apply] using hB
      · have := hysN y hy
        have e : v' y = v y := by
          simp [v', Function.update_of_ne (show y ≠ N + 2 by omega),
            Function.update_of_ne (show y ≠ N + 1 by omega)]
        rw [e]
        exact hv y hy
  have := F.internal_sep ψ ((N + 1) :: (N + 2) :: ys) N hadm v' hv' hP hPset
  have e1 : ∀ c, Function.update v' N c (N + 1) = A := fun c => by
    simp [v']
  have e2 : ∀ c a, Function.update (Function.update v' N c) x a (N + 2) = B := fun c a => by
    simp [v', h2.symm]
  have e3 : ∀ c a b, env c a b N = c := fun c a b => by
    simp [env, h0.symm]
  have e4 : ∀ c a b, env c a b x = a := fun c a b => by
    simp [env, h3]
  have e5 : ∀ c a b, env c a b (N + 3) = b := fun c a b => by
    simp [env]
  have hagree : ∀ c a b, ∀ y ∈ insert x {y | y ∈ ys}, env c a b y = Function.update v x a y := by
    intro c a b y hy
    have hyN : y < N := by
      rcases hy with rfl | hy
      · exact hxN
      · exact hysN y hy
    simp only [env, v']
    by_cases hyx : y = x
    · subst hyx
      simp [Function.update_of_ne h3]
    · simp [Function.update_of_ne hyx, Function.update_of_ne (show y ≠ N + 3 by omega),
        Function.update_of_ne (show y ≠ N by omega),
        Function.update_of_ne (show y ≠ N + 2 by omega),
        Function.update_of_ne (show y ≠ N + 1 by omega)]
  have ht' : (t.star F.star).Admissible F.U' (insert x {y | y ∈ ys}) := ht.star F.star_mem
  have key : ∀ c, Sat F.U' (Function.update v' N c) (ψ.star F.star) ↔
      ∃ a ∈ F.U', a ∈ A ∧ ∃ b ∈ F.U', b ∈ B ∧ c = pair a b ∧
        (t.star F.star).Defined F.U' (Function.update v x a) ∧
        b = (t.star F.star).val (Function.update v x a) := by
    intro c
    simp only [ψ, Formula.star, Term.star, Sat, Term.Defined, Term.val, Term.val_opair,
      Term.defined_opair, Term.star_opair, true_and, e1, e2]
    refine exists_congr fun a => and_congr_right fun _ => and_congr_right fun _ =>
      exists_congr fun b => and_congr_right fun _ => and_congr_right fun _ => ?_
    change (env c a b N = pair (env c a b x) (env c a b (N + 3))) ∧
      ((t.star F.star).Defined F.U' (env c a b) ∧
        env c a b (N + 3) = (t.star F.star).val (env c a b)) ↔ _
    rw [e3, e4, e5, Term.defined_congr ht' (hagree c a b), Term.val_congr ht' (hagree c a b)]
  have e : f = (prod A B).sep fun c => Sat F.U' (Function.update v' N c) (ψ.star F.star) := by
    ext c
    rw [mem_sep, key]
    constructor
    · intro hc
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 (hf.1 hc)
      have hab := hf.isFunction.app_eq hc
      refine ⟨hf.1 hc, a, F.isUniverse'.subset hAset ha, ha, b, F.isUniverse'.subset hBset hb,
        hb, rfl, (hval a ha).1, ?_⟩
      rw [← (hval a ha).2, hab]
    · rintro ⟨-, a, -, ha, b, -, -, rfl, -, hb⟩
      rw [hb, ← (hval a ha).2]
      exact hf.isFunction.pair_app_mem (hf.dom_eq ▸ ha)
  rw [e]
  exact this

/-- **Section 13.16, internal function definition principle.** Let $`f : A \to B` be a
function between internal sets $`A` and $`B`. Suppose that there is an internal term
$`\tau(x)` of the language of $`\mathbb U'` (all of its constants are internal) with sole
variable $`x` such that $`f(a) = \tau(a)` for all $`a \in A`. Then $`f` is an internal
function. -/
theorem internal_of_term_of_internal_consts (t : Term.{u}) (x : ℕ)
    (ht : t.Admissible F.U' {x}) (hconsts : ∃ N, t.Below N F.Internal) (v : ℕ → ZFSet.{u})
    (hA : F.Internal A) (hAset : IsSetOf F.U' A) (hB : F.Internal B) (hBset : IsSetOf F.U' B)
    (hf : IsFunc A B f)
    (hval : ∀ a ∈ A, t.Defined F.U' (Function.update v x a) ∧
      app f a = t.val (Function.update v x a)) : F.Internal f := by
  classical
  obtain ⟨N₀, hN₀⟩ := hconsts
  obtain ⟨N₁, L, hL, hB₁⟩ := Term.exists_below hN₀
  set N := max N₁ (x + 1) with hN
  have hxN : x < N := lt_of_lt_of_le (Nat.lt_succ_self x) (le_max_right _ _)
  have hBel : t.Below N (· ∈ L) := hB₁.mono (le_max_left _ _) fun _ h => h
  let e : ZFSet.{u} → ℕ := fun c => N + L.idxOf c
  let w : ℕ → ZFSet.{u} := fun n => if n < N then v n else L.getD (n - N) ∅
  have hwe : ∀ c ∈ L, w (e c) = c := by
    intro c hc
    have h1 : ¬ N + L.idxOf c < N := by omega
    simp only [w, e, h1, ite_false, Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hc), List.getElem_idxOf]
  have hwx : ∀ a, ∀ c ∈ L, Function.update w x a (e c) = c := fun a c hc => by
    have : N ≤ e c := Nat.le_add_right _ _
    rw [Function.update_of_ne (by omega)]
    exact hwe c hc
  have hadm : (t.abs e).Admissible F.U (insert x {y | y ∈ L.map e}) :=
    (Term.admissible_abs ht hBel).mono fun n hn => by
      rcases hn with hn | ⟨c, hc, rfl⟩
      · exact Or.inl hn
      · exact Or.inr (List.mem_map.2 ⟨c, hc, rfl⟩)
  have hv : ∀ y ∈ L.map e, F.Internal (w y) := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    rw [hwe c hc]
    exact hL c hc
  have hagree : ∀ a, ∀ y ∈ ({x} : Set ℕ), Function.update w x a y = Function.update v x a y :=
    fun a y hy => by
      rw [Set.mem_singleton_iff.1 hy]
      simp
  refine F.internal_of_term (t.abs e) (L.map e) x hadm w hv hA hAset hB hBset hf fun a ha => ?_
  rw [Term.star_abs, Term.defined_abs hBel (hwx a), Term.val_abs hBel (hwx a),
    Term.defined_congr ht (hagree a), Term.val_congr ht (hagree a)]
  exact hval a ha

end NonstandardFramework

end Goldblatt
