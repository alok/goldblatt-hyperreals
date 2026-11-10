import Goldblatt.Ch02_LargeSets
import Goldblatt.Ch14_Enlargements.Enlargement
import Goldblatt.Ch14_Enlargements.Terms

/-!
# 14 (part 5). The Enlargement Theorem: Sections 14.3 and 14.4

This is the last of five parts of Chapter 14 (the overview is on the chapter page
{lit}`Goldblatt.Ch14_Enlargements`). It chooses the ultrafilter for which the bounded
ultrapower of part 4 is an enlargement, and states the enlargement theorem.
-/

noncomputable section

namespace Goldblatt

open ZFSet Filter
open scoped Classical

universe u

/-!
## 14.3 Enlargements as Ultrapowers: the choice of the ultrafilter

Every ultrafilter gives a framework, but an enlargement needs a particular one. The index set
is the set $`I` of all finite subsets of the superstructure $`\mathbb U(X)`. For $`a \in I`
let $`I_a` be the set of all $`b \in I` that include $`a`. Finitely many of these sets always
have a common member, the union of the corresponding finite sets, so by the ultrafilter
theorem of Chapter 2 there is an ultrafilter that contains every $`I_a`.

With this ultrafilter a function on $`I` may be defined by saying what it does to a finite
set $`b` of entities, and "almost all $`b`" includes "all $`b` that contain a given entity".
Given a collection with the finite intersection property, choose for each $`b` a common
member of the finitely many members of the collection that belong to $`b`; the class of this
function lies in the transform of every member of the collection. That is the enlargement
property.
-/

namespace BoundedUltrapower

variable (X : ZFSet.{u})

/-- **Section 14.3, the index set.** $`I = \mathcal P_F(\mathbb U(X))`, the set of all
finite subsets of the superstructure, as a type. -/
abbrev Index : Type (u + 1) := ↥(finPow (superstructure X))

/-- **Section 14.3, the sets $`I_a`.** For $`a \in I`, the set
$`I_a = \{b \in I : a \subseteq b\}`. -/
def cone (a : Index X) : Set (Index X) := {b | a.1 ⊆ b.1}

/-- The index set is nonempty: it contains the empty set. -/
instance : Nonempty (Index X) :=
  ⟨⟨∅, mem_finPow.2 ⟨fun _ h => absurd h (notMem_empty _), by simp⟩⟩⟩

/-- **Section 14.3.** Finitely many members of $`I` are all included in one
member of $`I`, their union. -/
theorem exists_upper_bound (t : Finset (Index X)) : ∃ b : Index X, ∀ a ∈ t, a.1 ⊆ b.1 := by
  induction t using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary _, fun a ha => absurd ha (Finset.notMem_empty a)⟩
  | insert a t _ ih =>
    obtain ⟨b, hb⟩ := ih
    have ha := mem_finPow.1 a.2
    have hb' := mem_finPow.1 b.2
    have hfin : ((a.1 ∪ b.1 : ZFSet.{u}) : Set ZFSet.{u}).Finite := by
      have : ((a.1 ∪ b.1 : ZFSet.{u}) : Set ZFSet.{u}) = ↑a.1 ∪ ↑b.1 := by
        ext x
        simp
      rw [this]
      exact ha.2.union hb'.2
    refine ⟨⟨a.1 ∪ b.1, mem_finPow.2 ⟨fun x hx => ?_, hfin⟩⟩, fun c hc => ?_⟩
    · rcases mem_union.1 hx with h | h
      · exact ha.1 h
      · exact hb'.1 h
    · rcases Finset.mem_insert.1 hc with rfl | hc
      · exact fun x hx => mem_union.2 (Or.inl hx)
      · exact fun x hx => mem_union.2 (Or.inr (hb c hc hx))

/-- **Section 14.3.** The collection $`\{I_a : a \in I\}` has the finite
intersection property: $`a_1 \cup \dots \cup a_n \in I_{a_1} \cap \dots \cap I_{a_n}`. -/
theorem hasFIP_cones : HasFIP (Set.range (cone X)) := by
  intro s _ hs
  choose a ha using fun S : {S // S ∈ s} => hs S.2
  obtain ⟨b, hb⟩ := exists_upper_bound X (s.attach.image a)
  refine ⟨b, fun S hS => ?_⟩
  have e := ha ⟨S, hS⟩
  simp only at e
  rw [← e]
  exact hb _ (Finset.mem_image.2 ⟨⟨S, hS⟩, Finset.mem_attach _ _, rfl⟩)

/-- **Section 14.3, the ultrafilter.** An ultrafilter on $`I` that includes all the sets
$`I_a`, obtained from the ultrafilter theorem (Theorem 2.6.1 of Chapter 2). -/
def ultra : Ultrafilter (Index X) :=
  (hasFIP_cones X).exists_isUltrafilter_superset.choose_spec.1.toUltrafilter

/-- **Section 14.3.** Every $`I_a` belongs to the ultrafilter. -/
theorem cone_mem_ultra (a : Index X) : cone X a ∈ ultra X :=
  (hasFIP_cones X).exists_isUltrafilter_superset.choose_spec.2 ⟨a, rfl⟩

variable {X}

/-- The index $`\{a\}` for $`a \in \mathbb U(X)`. -/
def singleIndex {a : ZFSet.{u}} (ha : a ∈ superstructure X) : Index X :=
  ⟨{a}, mem_finPow.2 ⟨fun x hx => by rwa [mem_singleton.1 hx], finite_coe_singleton a⟩⟩

/-- **Section 14.3.** For $`a \in \mathbb U(X)` the set
$`I_{\{a\}} = \{b \in I : a \in b\}` belongs to the ultrafilter. -/
theorem eventually_mem_index {a : ZFSet.{u}} (ha : a ∈ superstructure X) :
    ∀ᶠ b in (ultra X : Filter (Index X)), a ∈ b.1 :=
  mem_of_superset (cone_mem_ultra X (singleIndex ha)) fun _ hb => hb (mem_singleton.2 rfl)

variable (X) in
/-- **Section 14.3.** The bounded ultrapower of $`\mathbb U(X)` modulo the
ultrafilter on $`\mathcal P_F(\mathbb U(X))` that includes the sets $`I_a`. -/
def enlargement (hX : IsBaseSet X) : NonstandardFramework.{u} := framework (ultra X) hX

/-- **Section 14.3.** The target universe of the construction is the
superstructure over $`{}^*X`. -/
theorem enlargement_star_base (hX : IsBaseSet X) :
    (enlargement X hX).star X = base (ultra X) X :=
  col_const_base hX

/-- **Section 14.3, the enlargement property.** The framework just
constructed is an enlargement. For a collection $`\mathcal A` with the finite intersection
property choose $`f(b) \in \bigcap (b \cap \mathcal A)` for each $`b \in I`. If
$`B \in \mathcal A` then $`I_{\{B\}} \subseteq \{b : f(b) \in B\}`, so $`[f] \in {}^*B`. The
formal proof chooses $`f(b)` also in a fixed member of $`\mathcal A`, which makes its bounded
rank evident and removes the book's case distinction. -/
theorem isEnlargement_enlargement (hX : IsBaseSet X) : (enlargement X hX).IsEnlargement := by
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  intro 𝒜 h𝒜 hsets hfip
  by_cases hne : 𝒜 = ∅
  · subst hne
    exact ⟨∅, (enlargement X hX).isUniverse'.empty_mem, fun B hB => absurd hB (notMem_empty B)⟩
  obtain ⟨B0, hB0⟩ := (eq_empty_or_nonempty 𝒜).resolve_left hne
  have hB0set : IsSetOf (superstructure X) B0 := hsets B0 hB0
  choose f hf using fun b : Index X =>
    hfip (insert B0 ((mem_finPow.1 b.2).2.toFinset.filter (· ∈ 𝒜))) fun C hC => by
      rcases Finset.mem_insert.1 hC with rfl | hC
      · exact hB0
      · exact (Finset.mem_filter.1 hC).2
  have hfB0 : ∀ b, f b ∈ B0 := fun b => hf b B0 (Finset.mem_insert_self _ _)
  have hfb : Bdd (ultra X) X f :=
    bdd_of_eventually_mem hX (bdd_const hB0set.1)
      (Eventually.of_forall fun b => ⟨hW.subset hB0set (hfB0 b), hfB0 b⟩)
  refine ⟨col (ultra X) hX f, col_mem hX hfb, fun B hB => ?_⟩
  have hBW : B ∈ superstructure X := hW.subset h𝒜 hB
  refine (col_mem_col_iff hX hfb (bdd_const hBW)).2 ?_
  filter_upwards [eventually_mem_index hBW] with b hb
  exact hf b B (Finset.mem_insert_of_mem (Finset.mem_filter.2
    ⟨(Set.Finite.mem_toFinset _).2 hb, hB⟩))

/-- **Section 14.3, the alternative proof.** The hyperfinite
approximation property holds in the constructed framework by a direct argument: for a set
$`A \in \mathbb U(X)` put $`g(b) = b \cap A`. Then $`[g] \in {}^*\mathcal P_F(A)`, and
$`{}^*a \in [g]` for every $`a \in A` because $`I_{\{a\}} = \{b : a \in b \cap A\}`. -/
theorem hyperfiniteApprox_enlargement (hX : IsBaseSet X) {A : ZFSet.{u}}
    (hA : IsSetOf (superstructure X) A) :
    ∃ B ∈ (enlargement X hX).star (finPow A), (enlargement X hX).im A ⊆ B := by
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  have hP := hW.isSetOf_finPow hA
  have hgP : ∀ b : Index X, b.1 ∩ A ∈ finPow A := fun b => by
    refine mem_finPow.2 ⟨fun x hx => (mem_inter.1 hx).2, (mem_finPow.1 b.2).2.subset fun x hx => ?_⟩
    exact (mem_inter.1 hx).1
  have hgb : Bdd (ultra X) X fun b : Index X => b.1 ∩ A :=
    bdd_of_eventually_mem hX (bdd_const hP.1)
      (Eventually.of_forall fun b => ⟨hW.subset hP (hgP b), hgP b⟩)
  refine ⟨col (ultra X) hX fun b : Index X => b.1 ∩ A,
    (col_mem_col_iff hX hgb (bdd_const hP.1)).2 (Eventually.of_forall hgP), fun y hy => ?_⟩
  obtain ⟨a, ha, rfl⟩ := (enlargement X hX).mem_im.1 hy
  have haW : a ∈ superstructure X := hW.subset hA ha
  refine (col_mem_col_iff hX (bdd_const haW) hgb).2 ?_
  filter_upwards [eventually_mem_index haW] with b hb
  exact mem_inter.2 ⟨hb, ha⟩

/-- **Section 14.3, nonprincipal ultrafilters on
$`\mathbb N`.** In the bounded ultrapower modulo a nonprincipal ultrafilter on $`\mathbb N`, as
in Sections 3.8 and 3.9, every infinite set $`A \in \mathbb U(X)` has a member of $`{}^*A`
that is not of the form $`{}^*a`: the class of an injective sequence in $`A`. For a general
index set nonprincipality alone does not give this; the special ultrafilter of this section
is what works in general. -/
theorem exists_mem_star_notMem_im_hyperfilter (hX : IsBaseSet X) {A : ZFSet.{u}}
    (hA : IsSetOf (superstructure X) A) (hinf : (A : Set ZFSet.{u}).Infinite) :
    ∃ b ∈ (framework (hyperfilter ℕ) hX).star A, b ∉ (framework (hyperfilter ℕ) hX).im A := by
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  let g := hinf.natEmbedding
  have hgA : ∀ n, (g n).1 ∈ A := fun n => (g n).2
  have hgb : Bdd (hyperfilter ℕ) X fun n => (g n).1 :=
    bdd_of_eventually_mem hX (bdd_const hA.1)
      (Eventually.of_forall fun n => ⟨hW.subset hA (hgA n), hgA n⟩)
  refine ⟨col (hyperfilter ℕ) hX fun n => (g n).1,
    (col_mem_col_iff hX hgb (bdd_const hA.1)).2 (Eventually.of_forall hgA), fun hb => ?_⟩
  obtain ⟨a, ha, e⟩ := (framework (hyperfilter ℕ) hX).mem_im.1 hb
  have h1 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (g n).1 = a :=
    (col_eq_iff hX hgb (bdd_const (hW.subset hA ha))).1 e
  have hsub : {n : ℕ | (g n).1 = a}.Subsingleton := fun m hm n hn =>
    g.injective (Subtype.ext (hm.trans hn.symm))
  have h2 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (g n).1 ≠ a :=
    mem_hyperfilter_of_finite_compl (by
      have : {n : ℕ | (g n).1 ≠ a}ᶜ = {n : ℕ | (g n).1 = a} := by
        ext n
        simp
      rw [this]
      exact hsub.finite)
  obtain ⟨n, c1, c2⟩ := (h1.and h2).exists
  exact c2 c1

/-!
## 14.4 Exercises on the Ultrapower Construction: Exercises (1) and (3)

Exercise (1) asks for the details of the construction. They are the content of parts 2 to 4:
well-definedness of the collapse and its two basic properties
({lit}`BoundedUltrapower.col_eq_iff`, {lit}`BoundedUltrapower.col_mem_col_iff`), the
computation of the transfer map ({lit}`BoundedUltrapower.mem_star_iff`,
{lit}`BoundedUltrapower.col_const_base`, {lit}`BoundedUltrapower.col_const_empty`), the theorem
of Łoś ({lit}`BoundedUltrapower.los`) and the resulting framework
({lit}`BoundedUltrapower.framework`). Exercise (2) is in part 4. Exercise (3) asks whether the
ultrafilter of the construction is nonprincipal; it is.
-/

/-- **Exercise 14.4(3).** The ultrafilter used in the construction is
nonprincipal. If it were generated by a point $`b`, then $`b` would lie in every $`I_{\{a\}}`,
so the finite set $`b` would contain every member of the infinite set $`\mathbb U(X)`. -/
theorem ultra_ne_pure (hX : IsBaseSet X) (b : Index X) : ultra X ≠ pure b := by
  have hW := (isUniverseOver_superstructure hX).toIsUniverse
  have hinf : (superstructure X : Set ZFSet.{u}).Infinite :=
    Set.infinite_of_injective_forall_mem num_injective fun k => (hW.isSetOf_num k).1
  obtain ⟨a, ha, hab⟩ := hinf.exists_notMem_finite (mem_finPow.1 b.2).2
  intro h
  have h1 : ∀ᶠ c in ((pure b : Ultrafilter (Index X)) : Filter (Index X)), a ∈ c.1 :=
    h ▸ eventually_mem_index ha
  rw [Ultrafilter.coe_pure, eventually_pure] at h1
  exact hab h1

end BoundedUltrapower

/-!
## The enlargement theorem

The statement announced at the end of Section 14.1.
-/

open BoundedUltrapower in
/-- **Enlargement Theorem (Sections 14.1 and 14.3).** For any set $`X` of
individuals there exists an enlargement of $`\mathbb U(X)` that is of the form
$`\mathbb U({}^*X)`: a nonstandard framework for $`X` with standard universe $`\mathbb U(X)`,
target universe $`\mathbb U({}^*X)`, and the enlargement property. -/
theorem exists_enlargement {X : ZFSet.{u}} (hX : IsBaseSet X) :
    ∃ F : NonstandardFramework.{u}, F.X = X ∧ F.U = superstructure X ∧
      F.U' = superstructure (F.star X) ∧ F.IsEnlargement :=
  ⟨enlargement X hX, rfl, rfl, by rw [enlargement_star_base hX]; rfl,
    isEnlargement_enlargement hX⟩

/-- **Enlargement Theorem, for a type.** Every type has a copy
$`X` inside the sets such that $`\mathbb U(X)` has an enlargement of the form
$`\mathbb U({}^*X)`. This removes the hypothesis that $`X` consists of individuals. -/
theorem exists_enlargement_of_type (α : Type u) :
    ∃ (ι : α → ZFSet.{u}) (F : NonstandardFramework.{u}), Function.Injective ι ∧
      F.X = ZFSet.range ι ∧ F.U = superstructure F.X ∧ F.U' = superstructure (F.star F.X) ∧
      F.IsEnlargement := by
  obtain ⟨ι, hι, hX⟩ := exists_isBaseSet α
  obtain ⟨F, h1, h2, h3, h4⟩ := exists_enlargement hX
  exact ⟨ι, F, hι, h1, by rw [h2, h1], by rw [h3, h1], h4⟩

/-- **Enlargement Theorem, over the real numbers.** There is
an enlargement in which the real numbers are individuals: a real framework in the sense of
Chapter 13 with the enlargement property, between superstructures. -/
theorem exists_realFramework_isEnlargement :
    ∃ F : RealFramework.{u}, F.IsEnlargement ∧ F.U = superstructure F.X ∧
      F.U' = superstructure (F.star F.X) := by
  obtain ⟨ι, F, hι, h1, h2, h3, h4⟩ := exists_enlargement_of_type (ULift.{u} ℝ)
  exact ⟨{ F with
    real := fun r => ι ⟨r⟩
    real_injective := fun _ _ hrs => congrArg ULift.down (hι hrs)
    real_mem := fun r => h1 ▸ mem_range.2 ⟨⟨r⟩, rfl⟩ }, h4, h2, h3⟩

/-- **Chapter 14, the opening question.** There is a
nonstandard framework over the real numbers in which $`{}^*\mathbb N` has a nonstandard member.
So the hypothesis of the results of Chapter 13 on external sets can be satisfied. -/
theorem exists_realFramework_nonstandard :
    ∃ F : RealFramework.{u}, ∃ n, n ∈ F.star F.N ∧ n ∉ F.N := by
  obtain ⟨F, hE, -, -⟩ := exists_realFramework_isEnlargement.{u}
  exact ⟨F, F.exists_nonstandard_nat hE⟩

end Goldblatt
