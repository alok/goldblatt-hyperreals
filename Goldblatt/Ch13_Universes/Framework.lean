import Goldblatt.Ch13_Universes.Language

/-!
# 13 (part 3). Nonstandard Frameworks and Standard Entities: Sections 13.8 and 13.9

This is the third of five parts of Chapter 13 (the overview is on the chapter page
{lit}`Goldblatt.Ch13_Universes`). It defines nonstandard frameworks, a universe together with
a transfer map into a second universe, as a structure whose fields are the book's axioms, and
derives from the transfer principle the list of set-theoretic operations that the transfer
map preserves. It then treats standard entities and the image of a set.
-/

noncomputable section

namespace Goldblatt

open ZFSet

universe u

/-!
## 13.8 Nonstandard Frameworks

A nonstandard framework for $`X` is a universe $`\mathbb U` over $`X`, a second universe
$`\mathbb U'` and a map $`a \mapsto {}^*a` from the first to the second that fixes the
individuals in $`X`, fixes the empty set, and satisfies the transfer principle: a sentence of
the language of $`\mathbb U` is true in $`\mathbb U` if and only if its transform is true in
$`\mathbb U'`. Everything in this part is a consequence of these axioms; that frameworks
exist is the subject of Chapter 14.

The typical argument transfers one explicitly written sentence. For sets cut out by a
formula there is a general statement, Exercise 13.8.2 ({lit}`NonstandardFramework.mem_star_sep`
below), and most of the preservation properties are obtained from it, as the exercise
suggests.
-/

/-- **Section 13.8, nonstandard frameworks.** A nonstandard framework for a set $`X`: a
universe $`\mathbb U` over $`X`, a universe $`\mathbb U'`, and a transfer map
$`a \mapsto {}^*a` taking members of $`\mathbb U` to members of $`\mathbb U'`, with
$`{}^*a = a` for $`a \in X`, with $`{}^*\emptyset = \emptyset`, and such that every sentence
of the language of $`\mathbb U` is true in $`\mathbb U` exactly when its transform is true in
$`\mathbb U'`. The map is a function on all of {name}`ZFSet`; only its values on
$`\mathbb U` matter. -/
structure NonstandardFramework where
  /-- The standard universe $`\mathbb U`. -/
  U : ZFSet.{u}
  /-- The set $`X` of individuals. -/
  X : ZFSet.{u}
  /-- The target universe $`\mathbb U'`. -/
  U' : ZFSet.{u}
  /-- The transfer map $`a \mapsto {}^*a`. -/
  star : ZFSet.{u} → ZFSet.{u}
  /-- $`\mathbb U` is a universe over $`X`. -/
  isUniverseOver : IsUniverseOver U X
  /-- $`\mathbb U'` is a universe. -/
  isUniverse' : IsUniverse U'
  /-- The transfer map takes $`\mathbb U` into $`\mathbb U'`. -/
  star_mem : ∀ a ∈ U, star a ∈ U'
  /-- $`{}^*a = a` for every individual $`a \in X`. -/
  star_individual : ∀ a ∈ X, star a = a
  /-- $`{}^*\emptyset = \emptyset`. -/
  star_empty : star ∅ = ∅
  /-- **Transfer.** A sentence $`\varphi` of the language of $`\mathbb U` is true if and only
  if $`{}^*\varphi` is true. -/
  transfer : ∀ φ : Formula.{u}, φ.IsSentence U → (φ.Holds U ↔ (φ.star star).Holds U')

namespace NonstandardFramework

open Formula Term

variable (F : NonstandardFramework.{u}) {A B C D R S T f a b c : ZFSet.{u}}

theorem hU : IsUniverse F.U := F.isUniverseOver.toIsUniverse

/-- **Section 13.8, transfer map (1).** $`a = b` if and only if $`{}^*a = {}^*b`. -/
theorem star_eq_iff (ha : a ∈ F.U) (hb : b ∈ F.U) : F.star a = F.star b ↔ a = b := by
  have h := F.transfer (.equal (.const a) (.const b)) (by simp [IsSentence, ha, hb])
  simpa [Holds] using h.symm

/-- **Section 13.8, transfer map (1).** The transfer map is injective on $`\mathbb U`. -/
theorem star_injOn : Set.InjOn F.star (F.U : Set ZFSet.{u}) := fun _ ha _ hb h =>
  (F.star_eq_iff ha hb).1 h

/-- **Section 13.8, transfer map (2).** $`a \in B` if and only if $`{}^*a \in {}^*B`. -/
theorem star_mem_star_iff (ha : a ∈ F.U) (hB : B ∈ F.U) : F.star a ∈ F.star B ↔ a ∈ B := by
  have h := F.transfer (.elem (.const a) (.const B)) (by simp [IsSentence, ha, hB])
  simpa [Holds] using h.symm

/-- The transform of a set of $`\mathbb U` is a set of $`\mathbb U'`, not an individual. -/
theorem isSetOf_star (hA : IsSetOf F.U A) : IsSetOf F.U' (F.star A) := by
  rcases hA.eq_empty_or with rfl | ⟨y, hy, hyA⟩
  · rw [F.star_empty]
    exact F.isUniverse'.isSetOf_empty
  · exact ⟨F.star_mem A hA.1, fun h =>
      h.2 _ (F.star_mem y hy) ((F.star_mem_star_iff hy hA.1).2 hyA)⟩

theorem star_subset_U' (hA : IsSetOf F.U A) : F.star A ⊆ F.U' :=
  F.isUniverse'.subset (F.isSetOf_star hA)

end NonstandardFramework

/-- Two sets of a universe with the same members in the universe are equal. -/
theorem IsUniverse.ext {U A B : ZFSet.{u}} (hU : IsUniverse U) (hA : IsSetOf U A)
    (hB : IsSetOf U B) (h : ∀ x ∈ U, x ∈ A ↔ x ∈ B) : A = B := by
  ext x
  exact ⟨fun hx => (h x (hU.subset hA hx)).1 hx, fun hx => (h x (hU.subset hB hx)).2 hx⟩

namespace NonstandardFramework

open Formula Term

variable (F : NonstandardFramework.{u}) {A B C D R S T f a b c : ZFSet.{u}}

/-- **Section 13.8, transfer map (3).** $`A \subseteq B` if and only if
$`{}^*A \subseteq {}^*B`. -/
theorem star_subset_star_iff (hA : IsSetOf F.U A) (hB : IsSetOf F.U B) :
    F.star A ⊆ F.star B ↔ A ⊆ B := by
  have h := F.transfer (.all 0 (.const A) (.elem (.var 0) (.const B)))
    (by simp [IsSentence, hA.1, hB.1])
  simp only [Holds, Formula.star, Term.star, Sat, Term.Defined, Term.val, forall_true_left,
    true_and, Function.update_self] at h
  constructor
  · exact fun hs x hx => h.2 (fun y _ hy => hs hy) x (F.hU.subset hA hx) hx
  · exact fun hs x hx => h.1 (fun y _ hy => hs hy) x (F.star_subset_U' hA hx) hx

/-- **Exercise 13.8.2 (one variable).** If $`\varphi(x)` is a formula of the language of
$`\mathbb U` with only $`x` free and $`A` is a set in $`\mathbb U`, then
$$`{}^*\{a \in A : \varphi(a)\} = \{b \in {}^*A : {}^*\varphi(b)\}.`
The statement is membership-wise, for any set $`C` with the members
$`\{a \in A : \varphi(a)\}`; the free variable is the variable $`0`. -/
theorem mem_star_sep (hA : IsSetOf F.U A) (φ : Formula.{u}) (hφ : φ.Admissible F.U {0})
    (hC : ∀ a, a ∈ C ↔ a ∈ A ∧ Sat F.U (Function.update (fun _ => ∅) 0 a) φ) (b : ZFSet.{u}) :
    b ∈ F.star C ↔
      b ∈ F.star A ∧ Sat F.U' (Function.update (fun _ => ∅) 0 b) (φ.star F.star) := by
  have hCA : C ⊆ A := fun a ha => ((hC a).1 ha).1
  have hCset := F.hU.isSetOf_of_subset hA hCA
  have h := F.transfer
    (.conj (.all 0 (.const C) (.conj (.elem (.var 0) (.const A)) φ))
      (.all 0 (.const A) (.imp φ (.elem (.var 0) (.const C)))))
    (by simp [IsSentence, hA.1, hCset.1, hφ])
  simp only [Holds, Formula.star, Term.star, Sat, Term.Defined, Term.val, forall_true_left,
    true_and, Function.update_self] at h
  obtain ⟨h1, h2⟩ := h.1 ⟨fun a _ ha => (hC a).1 ha, fun a _ ha hs => (hC a).2 ⟨ha, hs⟩⟩
  exact ⟨fun hb => h1 b (F.star_subset_U' hCset hb) hb,
    fun hb => h2 b (F.star_subset_U' hA hb.1) hb.1 hb.2⟩

/-- **Section 13.8, transfer map (5).** $`{}^*(A \cap B) = {}^*A \cap {}^*B`. -/
theorem star_inter (hA : IsSetOf F.U A) (hB : IsSetOf F.U B) :
    F.star (A ∩ B) = F.star A ∩ F.star B := by
  ext x
  have := F.mem_star_sep hA (.elem (.var 0) (.const B)) (by simp [hB.1]) (C := A ∩ B)
    (by intro a; sat_simp; exact mem_inter) x
  sat_simp at this
  rw [this, mem_inter]

/-- **Section 13.8, transfer map (5).** $`{}^*(A - B) = {}^*A - {}^*B`. -/
theorem star_sdiff (hA : IsSetOf F.U A) (hB : IsSetOf F.U B) :
    F.star (A \ B) = F.star A \ F.star B := by
  ext x
  have := F.mem_star_sep hA (.neg (.elem (.var 0) (.const B))) (by simp [hB.1]) (C := A \ B)
    (by intro a; sat_simp; exact mem_sdiff) x
  sat_simp at this
  rw [this, mem_sdiff]

/-- **Section 13.8, transfer map (5).** $`{}^*(A \cup B) = {}^*A \cup {}^*B`. -/
theorem star_union (hA : IsSetOf F.U A) (hB : IsSetOf F.U B) :
    F.star (A ∪ B) = F.star A ∪ F.star B := by
  have hAB := F.hU.isSetOf_union hA hB
  ext x
  have := F.mem_star_sep hAB (.disj (.elem (.var 0) (.const A)) (.elem (.var 0) (.const B)))
    (by simp [hA.1, hB.1]) (C := A ∪ B) (by intro a; sat_simp; simp) x
  sat_simp at this
  rw [mem_union]
  refine ⟨fun hx => (this.1 hx).2, ?_⟩
  rintro (hx | hx)
  · exact (F.star_subset_star_iff hA hAB).2 (fun y hy => mem_union.2 (Or.inl hy)) hx
  · exact (F.star_subset_star_iff hB hAB).2 (fun y hy => mem_union.2 (Or.inr hy)) hx

/-- **Section 13.8, transfer map (6), one element.** $`{}^*\{a\} = \{{}^*a\}`. -/
theorem star_singleton (ha : a ∈ F.U) : F.star {a} = {F.star a} := by
  have hs := F.hU.isSetOf_singleton ha
  ext x
  have := F.mem_star_sep hs (.equal (.var 0) (.const a)) (by simp [ha]) (C := {a})
    (by intro b; sat_simp; simp) x
  sat_simp at this
  rw [mem_singleton]
  refine ⟨fun hx => (this.1 hx).2, fun hx => ?_⟩
  rw [hx]
  exact (F.star_mem_star_iff ha hs.1).2 (mem_singleton.2 rfl)

/-- $`{}^*(\{a\} \cup A) = \{{}^*a\} \cup {}^*A`. -/
theorem star_insert (ha : a ∈ F.U) (hA : IsSetOf F.U A) :
    F.star (insert a A) = insert (F.star a) (F.star A) := by
  rw [insert_eq, F.star_union (F.hU.isSetOf_singleton ha) hA, F.star_singleton ha, ← insert_eq]

/-- **Section 13.8, transfer map (6), two elements.** $`{}^*\{a, b\} = \{{}^*a, {}^*b\}`. -/
theorem star_pair (ha : a ∈ F.U) (hb : b ∈ F.U) :
    F.star ({a, b} : ZFSet.{u}) = {F.star a, F.star b} := by
  rw [F.star_insert ha (F.hU.isSetOf_singleton hb), F.star_singleton hb]

/-- **Section 13.8, transfer map (6).** $`{}^*\{a_1, \dots, a_m\} = \{{}^*a_1, \dots,
{}^*a_m\}`: if $`A` is a finite set of $`\mathbb U`, then $`{}^*A = \{{}^*a : a \in A\}`. -/
theorem mem_star_of_finite (hA : IsSetOf F.U A) (hfin : (A : Set ZFSet.{u}).Finite) :
    b ∈ F.star A ↔ ∃ a ∈ A, b = F.star a := by
  generalize hs : (A : Set ZFSet.{u}) = s at hfin
  induction s, hfin using Set.Finite.induction_on generalizing A with
  | empty =>
    have : A = ∅ := by
      rw [eq_empty]
      intro y hy
      have : y ∈ (A : Set ZFSet.{u}) := hy
      rw [hs] at this
      exact this
    subst this
    simp [F.star_empty]
  | @insert a s _ _ ih =>
    have hmem : ∀ x, x ∈ A ↔ x = a ∨ x ∈ s := fun x => by
      rw [← SetLike.mem_coe, hs, Set.mem_insert_iff]
    have hA' : IsSetOf F.U (A.sep fun x => x ∈ s) := F.hU.isSetOf_sep hA _
    have ih' := ih hA' (by
      ext x
      simp only [SetLike.mem_coe, mem_sep, hmem]
      tauto)
    have haU : a ∈ F.U := F.hU.subset hA ((hmem a).2 (Or.inl rfl))
    have : A = insert a (A.sep fun x => x ∈ s) := by
      ext x
      simp only [mem_insert_iff, mem_sep, hmem]
      tauto
    rw [this, F.star_insert haU hA', mem_insert_iff, ih']
    constructor
    · rintro (rfl | ⟨c, hc, rfl⟩)
      · exact ⟨a, mem_insert _ _, rfl⟩
      · exact ⟨c, mem_insert_of_mem _ hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      rcases mem_insert_iff.1 hc with rfl | hc
      · exact Or.inl rfl
      · exact Or.inr ⟨c, hc, rfl⟩

/-- **Section 13.8, transfer map.** The transform of an ordered pair is the pair of the
transforms: $`{}^*(a, b) = ({}^*a, {}^*b)`. -/
theorem star_opair (ha : a ∈ F.U) (hb : b ∈ F.U) :
    F.star (pair a b) = pair (F.star a) (F.star b) := by
  show F.star ({{a}, {a, b}} : ZFSet.{u}) = {{F.star a}, {F.star a, F.star b}}
  rw [F.star_pair (F.hU.isSetOf_singleton ha).1 (F.hU.isSetOf_pair ha hb).1,
    F.star_singleton ha, F.star_pair ha hb]

/-- The numerals are fixed by the transfer map. -/
theorem star_num (n : ℕ) : F.star (num n) = num n := by
  induction n with
  | zero => exact F.star_empty
  | succ n ih =>
    show F.star (insert (num n) (num n)) = insert (num n) (num n)
    rw [F.star_insert (F.hU.isSetOf_num n).1 (F.hU.isSetOf_num n), ih]

/-- **Section 13.8, transfer map.** The transform of a tuple is the tuple of the transforms:
$`{}^*(a_1, \dots, a_m) = ({}^*a_1, \dots, {}^*a_m)`. -/
theorem star_tuple (m : ℕ) (a : Fin m → ZFSet.{u}) (ha : ∀ i, a i ∈ F.U) :
    F.star (tuple m a) = tuple m fun i => F.star (a i) := by
  by_cases hm : m = 2
  · subst hm
    rw [tuple_two, tuple_two, F.star_opair (ha 0) (ha 1)]
  · ext x
    have hfin : (tuple m a : Set ZFSet.{u}).Finite := by
      simp only [tuple, hm, ↓reduceDIte, coe_range]
      exact Set.finite_range _
    rw [F.mem_star_of_finite (F.hU.isSetOf_tuple m a ha) hfin, mem_tuple hm]
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨i, rfl⟩ := (mem_tuple hm).1 hp
      exact ⟨i, by rw [F.star_opair (F.hU.isSetOf_num _).1 (ha i), F.star_num]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, (mem_tuple hm).2 ⟨i, rfl⟩,
        by rw [F.star_opair (F.hU.isSetOf_num _).1 (ha i), F.star_num]⟩

/-- **Section 13.8, transfer map (4).** If $`A \subseteq X` then
$`A \subseteq {}^*A \subseteq {}^*X`. -/
theorem subset_star_of_subset_base (hAX : A ⊆ F.X) : A ⊆ F.star A ∧ F.star A ⊆ F.star F.X := by
  have hX := F.isUniverseOver.base_isSetOf
  have hA := F.hU.isSetOf_of_subset hX hAX
  refine ⟨fun a ha => ?_, (F.star_subset_star_iff hA hX).2 hAX⟩
  have := (F.star_mem_star_iff (F.hU.subset hA ha) hA.1).2 ha
  rwa [F.star_individual a (hAX ha)] at this

/-- **Section 13.8, transfer map (4).** In particular $`X \subseteq {}^*X`. -/
theorem base_subset_star_base : F.X ⊆ F.star F.X :=
  (F.subset_star_of_subset_base fun _ h => h).1

/-- **Section 13.8, transfer map (7).** All members of $`{}^*X` are individuals in
$`\mathbb U'`. -/
theorem isIndividual_of_mem_star_base (hb : b ∈ F.star F.X) : IsIndividual F.U' b := by
  have hX := F.isUniverseOver.base_isSetOf
  have h := F.transfer
    (.all 0 (.const F.X) (.conj (.neg (.equal (.var 0) (.const ∅)))
      (.neg (.ex 1 (.var 0) (.equal (.var 1) (.var 1))))))
    (by simp [IsSentence, hX.1, F.hU.empty_mem])
  sat_simp at h
  rw [F.star_empty] at h
  have h' := h.1 (fun a _ ha => ⟨(F.isUniverseOver.individual a ha).1,
    fun ⟨y, hy, hya⟩ => (F.isUniverseOver.individual a ha).2 y hy hya⟩)
    b (F.star_subset_U' hX hb) hb
  exact ⟨h'.1, fun y hy hyb => h'.2 ⟨y, hy, hyb⟩⟩

/-- **Section 13.8, transfer map (8).** The transfer map preserves transitivity: if $`A` is a
transitive set in $`\mathbb U`, then $`{}^*A` is transitive. -/
theorem transitiveIn_star (hA : IsSetOf F.U A) (h : TransitiveIn F.U A) :
    TransitiveIn F.U' (F.star A) := by
  have ht := F.transfer (.all 0 (.const A) (.all 1 (.var 0) (.elem (.var 1) (.const A))))
    (by simp [IsSentence, hA.1])
  sat_simp at ht
  have ht' := ht.1 fun y _ hy z hz hzy => h y hy z hzy hz
  exact fun y hy z hz hzU => ht' y (F.star_subset_U' hA hy) hy z hzU hz

/-- If every member of a set $`C` of $`\mathbb U` is a set, then every member of $`{}^*C` is
a set of $`\mathbb U'`. -/
theorem isSetOf_of_mem_star (hC : IsSetOf F.U C) (hsets : ∀ c ∈ C, IsSetOf F.U c)
    (hb : b ∈ F.star C) : IsSetOf F.U' b := by
  have h := F.transfer
    (.all 0 (.const C) (.disj (.equal (.var 0) (.const ∅)) (.ex 1 (.var 0) (.equal (.var 1) (.var 1)))))
    (by simp [IsSentence, hC.1, F.hU.empty_mem])
  sat_simp at h
  rw [F.star_empty] at h
  have hbU := F.star_subset_U' hC hb
  rcases h.1 (fun c _ hc => (hsets c hc).eq_empty_or.imp id fun ⟨y, hy, hyc⟩ => ⟨y, hy, hyc⟩)
    b hbU hb with rfl | ⟨y, hy, hyb⟩
  · exact F.isUniverse'.isSetOf_empty
  · exact ⟨hbU, fun hi => hi.2 y hy hyb⟩

/-- Every member of $`{}^*\mathcal P(A)` is a set of $`\mathbb U'`. -/
theorem isSetOf_of_mem_star_powerset (hA : IsSetOf F.U A) (hb : b ∈ F.star (powerset A)) :
    IsSetOf F.U' b :=
  F.isSetOf_of_mem_star (F.hU.isSetOf_powerset hA)
    (fun _ hc => F.hU.isSetOf_of_subset hA (mem_powerset.1 hc)) hb

/-- **Section 13.8, transfer map (9).** $`{}^*\mathcal P(A) \subseteq \mathcal P({}^*A)`. -/
theorem star_powerset_subset (hA : IsSetOf F.U A) :
    F.star (powerset A) ⊆ powerset (F.star A) := by
  intro b hb
  have hP := F.hU.isSetOf_powerset hA
  have h := F.transfer
    (.all 0 (.const (powerset A)) (.all 1 (.var 0) (.elem (.var 1) (.const A))))
    (by simp [IsSentence, hA.1, hP.1])
  sat_simp at h
  have h' := h.1 fun x _ hx y _ hy => mem_powerset.1 hx hy
  have hbset := F.isSetOf_of_mem_star_powerset hA hb
  rw [mem_powerset]
  exact fun y hy => h' b hbset.1 hb y (F.isUniverse'.subset hbset hy) hy

/-- **Section 13.8, transfer map (11), two factors.**
$`{}^*(A \times B) = {}^*A \times {}^*B`. -/
theorem star_prod (hA : IsSetOf F.U A) (hB : IsSetOf F.U B) :
    F.star (prod A B) = prod (F.star A) (F.star B) := by
  have hP := F.hU.isSetOf_prod hA hB
  have h := F.transfer
    (.conj (.all 0 (.const (prod A B)) (.ex 1 (.const A) (.ex 2 (.const B)
        (.equal (.var 0) (.opair (.var 1) (.var 2))))))
      (.all 1 (.const A) (.all 2 (.const B) (.elem (.opair (.var 1) (.var 2)) (.const (prod A B))))))
    (by simp [IsSentence, hA.1, hB.1, hP.1])
  sat_simp at h
  obtain ⟨h1, h2⟩ := h.1 ⟨fun p _ hp => by
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 hp
      exact ⟨a, F.hU.subset hA ha, ha, b, F.hU.subset hB hb, hb, rfl⟩,
    fun a _ ha b _ hb => pair_mem_prod.2 ⟨ha, hb⟩⟩
  ext p
  rw [mem_prod]
  constructor
  · intro hp
    obtain ⟨a, -, ha, b, -, hb, rfl⟩ := h1 p (F.star_subset_U' hP hp) hp
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact h2 a (F.star_subset_U' hA ha) ha b (F.star_subset_U' hB hb) hb

/-- A relation between sets of $`\mathbb U` transforms to a relation between their
transforms. -/
theorem star_subset_prod (hA : IsSetOf F.U A) (hB : IsSetOf F.U B) (hR : R ⊆ prod A B) :
    F.star R ⊆ prod (F.star A) (F.star B) := by
  rw [← F.star_prod hA hB]
  exact (F.star_subset_star_iff (F.hU.isSetOf_of_subset_prod hA hB hR)
    (F.hU.isSetOf_prod hA hB)).2 hR

end NonstandardFramework

/-- A binary relation in a universe is a relation on some set of the universe. -/
theorem IsUniverse.exists_subset_prod_self {U R : ZFSet.{u}} (hU : IsUniverse U)
    (hR : IsSetOf U R) (hrel : RelIn U R) : ∃ B, IsSetOf U B ∧ R ⊆ prod B B := by
  obtain ⟨B, hB, h⟩ := hU.exists_transitive_of_relIn hR hrel
  refine ⟨B, hB, fun p hp => ?_⟩
  obtain ⟨a, -, b, -, rfl⟩ := hrel p hp
  exact pair_mem_prod.2 (h a b hp)

namespace NonstandardFramework

open Formula Term

variable (F : NonstandardFramework.{u}) {A B C D R S T f a b c : ZFSet.{u}}

/-- **Section 13.8, transfer map (10), binary case.** If $`R \in \mathbb U` is a binary
relation, then so is $`{}^*R`. -/
theorem relIn_star (hR : IsSetOf F.U R) (hrel : RelIn F.U R) : RelIn F.U' (F.star R) := by
  obtain ⟨B, hB, hRB⟩ := F.hU.exists_subset_prod_self hR hrel
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 (F.star_subset_prod hB hB hRB hp)
  exact ⟨a, F.star_subset_U' hB ha, b, F.star_subset_U' hB hb, rfl⟩

/-- **Section 13.8, transfer map (12a).**
$`{}^*(\operatorname{dom} R) = \operatorname{dom} {}^*R`. -/
theorem star_dom (hR : IsSetOf F.U R) (hrel : RelIn F.U R) : F.star (dom R) = dom (F.star R) := by
  obtain ⟨B, hB, hRB⟩ := F.hU.exists_subset_prod_self hR hrel
  have hRB' := F.star_subset_prod hB hB hRB
  ext x
  have := F.mem_star_sep hB (.ex 1 (.const B) (.elem (.opair (.var 0) (.var 1)) (.const R)))
    (by simp [hB.1, hR.1]) (C := dom R) (by
      intro a
      sat_simp
      rw [mem_dom]
      constructor
      · rintro ⟨b, hab⟩
        have := pair_mem_prod.1 (hRB hab)
        exact ⟨this.1, b, F.hU.subset hB this.2, this.2, hab⟩
      · rintro ⟨-, b, -, -, hab⟩
        exact ⟨b, hab⟩) x
  sat_simp at this
  rw [this, mem_dom]
  constructor
  · rintro ⟨-, b, -, -, hab⟩
    exact ⟨b, hab⟩
  · rintro ⟨b, hab⟩
    have := pair_mem_prod.1 (hRB' hab)
    exact ⟨this.1, b, F.star_subset_U' hB this.2, this.2, hab⟩

/-- **Section 13.8, transfer map (12b).**
$`{}^*(\operatorname{ran} R) = \operatorname{ran} {}^*R`. -/
theorem star_ran (hR : IsSetOf F.U R) (hrel : RelIn F.U R) : F.star (ran R) = ran (F.star R) := by
  obtain ⟨B, hB, hRB⟩ := F.hU.exists_subset_prod_self hR hrel
  have hRB' := F.star_subset_prod hB hB hRB
  ext x
  have := F.mem_star_sep hB (.ex 1 (.const B) (.elem (.opair (.var 1) (.var 0)) (.const R)))
    (by simp [hB.1, hR.1]) (C := ran R) (by
      intro b
      sat_simp
      rw [mem_ran]
      constructor
      · rintro ⟨a, hab⟩
        have := pair_mem_prod.1 (hRB hab)
        exact ⟨this.2, a, F.hU.subset hB this.1, this.1, hab⟩
      · rintro ⟨-, a, -, -, hab⟩
        exact ⟨a, hab⟩) x
  sat_simp at this
  rw [this, mem_ran]
  constructor
  · rintro ⟨-, a, -, -, hab⟩
    exact ⟨a, hab⟩
  · rintro ⟨a, hab⟩
    have := pair_mem_prod.1 (hRB' hab)
    exact ⟨this.2, a, F.star_subset_U' hB this.1, this.1, hab⟩

/-- **Section 13.8, transfer map (12d).** $`{}^*(R'(C)) = ({}^*R)'({}^*C)` for every set
$`C` of $`\mathbb U` (the book takes $`C \subseteq \operatorname{dom} R`). -/
theorem star_relImage (hR : IsSetOf F.U R) (hrel : RelIn F.U R) (hC : IsSetOf F.U C) :
    F.star (relImage R C) = relImage (F.star R) (F.star C) := by
  obtain ⟨B, hB, hRB⟩ := F.hU.exists_subset_prod_self hR hrel
  have hRB' := F.star_subset_prod hB hB hRB
  ext x
  have := F.mem_star_sep hB (.ex 1 (.const C) (.elem (.opair (.var 1) (.var 0)) (.const R)))
    (by simp [hC.1, hR.1]) (C := relImage R C) (by
      intro b
      sat_simp
      rw [mem_relImage]
      constructor
      · rintro ⟨a, ha, hab⟩
        exact ⟨(pair_mem_prod.1 (hRB hab)).2, a, F.hU.subset hC ha, ha, hab⟩
      · rintro ⟨-, a, -, ha, hab⟩
        exact ⟨a, ha, hab⟩) x
  sat_simp at this
  rw [this, mem_relImage]
  constructor
  · rintro ⟨-, a, -, ha, hab⟩
    exact ⟨a, ha, hab⟩
  · rintro ⟨a, ha, hab⟩
    exact ⟨(pair_mem_prod.1 (hRB' hab)).2, a, F.star_subset_U' hC ha, ha, hab⟩

/-- **Section 13.8, transfer map (12e).** $`{}^*(R^{-1}(C)) = ({}^*R)^{-1}({}^*C)` for every
set $`C` of $`\mathbb U` (the book takes $`C \subseteq \operatorname{ran} R`). -/
theorem star_relPreimage (hR : IsSetOf F.U R) (hrel : RelIn F.U R) (hC : IsSetOf F.U C) :
    F.star (relPreimage R C) = relPreimage (F.star R) (F.star C) := by
  obtain ⟨B, hB, hRB⟩ := F.hU.exists_subset_prod_self hR hrel
  have hRB' := F.star_subset_prod hB hB hRB
  ext x
  have := F.mem_star_sep hB (.ex 1 (.const C) (.elem (.opair (.var 0) (.var 1)) (.const R)))
    (by simp [hC.1, hR.1]) (C := relPreimage R C) (by
      intro a
      sat_simp
      rw [mem_relPreimage]
      constructor
      · rintro ⟨b, hb, hab⟩
        exact ⟨(pair_mem_prod.1 (hRB hab)).1, b, F.hU.subset hC hb, hb, hab⟩
      · rintro ⟨-, b, -, hb, hab⟩
        exact ⟨b, hb, hab⟩) x
  sat_simp at this
  rw [this, mem_relPreimage]
  constructor
  · rintro ⟨-, b, -, hb, hab⟩
    exact ⟨b, hb, hab⟩
  · rintro ⟨b, hb, hab⟩
    exact ⟨(pair_mem_prod.1 (hRB' hab)).1, b, F.star_subset_U' hC hb, hb, hab⟩

/-- **Section 13.8, transfer map (12c).** $`{}^*(R^{-1}) = ({}^*R)^{-1}`. -/
theorem star_relInv (hR : IsSetOf F.U R) (hrel : RelIn F.U R) :
    F.star (relInv R) = relInv (F.star R) := by
  obtain ⟨B, hB, hRB⟩ := F.hU.exists_subset_prod_self hR hrel
  have hRB' := F.star_subset_prod hB hB hRB
  have hP := F.hU.isSetOf_prod hB hB
  ext x
  have := F.mem_star_sep hP (.ex 1 (.const B) (.ex 2 (.const B)
      (.conj (.equal (.var 0) (.opair (.var 2) (.var 1)))
        (.elem (.opair (.var 1) (.var 2)) (.const R)))))
    (by simp [hB.1, hR.1]) (C := relInv R) (by
      intro p
      sat_simp
      rw [mem_relInv]
      constructor
      · rintro ⟨a, b, rfl, hab⟩
        have := pair_mem_prod.1 (hRB hab)
        exact ⟨pair_mem_prod.2 ⟨this.2, this.1⟩, a, F.hU.subset hB this.1, this.1, b,
          F.hU.subset hB this.2, this.2, rfl, hab⟩
      · rintro ⟨-, a, -, -, b, -, -, rfl, hab⟩
        exact ⟨a, b, rfl, hab⟩) x
  sat_simp at this
  rw [this, mem_relInv, F.star_prod hB hB]
  constructor
  · rintro ⟨-, a, -, -, b, -, -, rfl, hab⟩
    exact ⟨a, b, rfl, hab⟩
  · rintro ⟨a, b, rfl, hab⟩
    have := pair_mem_prod.1 (hRB' hab)
    exact ⟨pair_mem_prod.2 ⟨this.2, this.1⟩, a, F.star_subset_U' hB this.1, this.1, b,
      F.star_subset_U' hB this.2, this.2, rfl, hab⟩

/-- **Section 13.8, transfer map (13).** $`{}^*(R \circ S) = {}^*R \circ {}^*S`. -/
theorem star_relComp (hR : IsSetOf F.U R) (hrel : RelIn F.U R) (hS : IsSetOf F.U S)
    (hrelS : RelIn F.U S) : F.star (relComp R S) = relComp (F.star R) (F.star S) := by
  obtain ⟨B₁, hB₁, hRB₁⟩ := F.hU.exists_subset_prod_self hR hrel
  obtain ⟨B₂, hB₂, hSB₂⟩ := F.hU.exists_subset_prod_self hS hrelS
  have hB := F.hU.isSetOf_union hB₁ hB₂
  have hRB : R ⊆ prod (B₁ ∪ B₂) (B₁ ∪ B₂) := fun p hp => by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 (hRB₁ hp)
    exact pair_mem_prod.2 ⟨mem_union.2 (Or.inl ha), mem_union.2 (Or.inl hb)⟩
  have hSB : S ⊆ prod (B₁ ∪ B₂) (B₁ ∪ B₂) := fun p hp => by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 (hSB₂ hp)
    exact pair_mem_prod.2 ⟨mem_union.2 (Or.inr ha), mem_union.2 (Or.inr hb)⟩
  have hRB' := F.star_subset_prod hB hB hRB
  have hSB' := F.star_subset_prod hB hB hSB
  have hP := F.hU.isSetOf_prod hB hB
  ext x
  have := F.mem_star_sep hP (.ex 1 (.const (B₁ ∪ B₂)) (.ex 2 (.const (B₁ ∪ B₂))
      (.ex 3 (.const (B₁ ∪ B₂)) (.conj (.equal (.var 0) (.opair (.var 1) (.var 3)))
        (.conj (.elem (.opair (.var 1) (.var 2)) (.const R))
          (.elem (.opair (.var 2) (.var 3)) (.const S)))))))
    (by simp [hB.1, hR.1, hS.1]) (C := relComp R S) (by
      intro p
      sat_simp
      rw [mem_relComp]
      constructor
      · rintro ⟨a, b, c, rfl, hab, hbc⟩
        have h1 := pair_mem_prod.1 (hRB hab)
        have h2 := pair_mem_prod.1 (hSB hbc)
        exact ⟨pair_mem_prod.2 ⟨h1.1, h2.2⟩, a, F.hU.subset hB h1.1, h1.1, b,
          F.hU.subset hB h1.2, h1.2, c, F.hU.subset hB h2.2, h2.2, rfl, hab, hbc⟩
      · rintro ⟨-, a, -, -, b, -, -, c, -, -, rfl, hab, hbc⟩
        exact ⟨a, b, c, rfl, hab, hbc⟩) x
  sat_simp at this
  rw [this, mem_relComp, F.star_prod hB hB]
  constructor
  · rintro ⟨-, a, -, -, b, -, -, c, -, -, rfl, hab, hbc⟩
    exact ⟨a, b, c, rfl, hab, hbc⟩
  · rintro ⟨a, b, c, rfl, hab, hbc⟩
    have h1 := pair_mem_prod.1 (hRB' hab)
    have h2 := pair_mem_prod.1 (hSB' hbc)
    exact ⟨pair_mem_prod.2 ⟨h1.1, h2.2⟩, a, F.star_subset_U' hB h1.1, h1.1, b,
      F.star_subset_U' hB h1.2, h1.2, c, F.star_subset_U' hB h2.2, h2.2, rfl, hab, hbc⟩

/-- **Section 13.8, transfer map (14a).** If a function $`f : A \to B` belongs to
$`\mathbb U`, then $`{}^*f` is a function from $`{}^*A` to $`{}^*B`. -/
theorem isFunc_star (hA : IsSetOf F.U A) (hB : IsSetOf F.U B) (hf : IsFunc A B f) :
    IsFunc (F.star A) (F.star B) (F.star f) := by
  have hfset := F.hU.isSetOf_of_isFunc hA hB hf
  have hsub := F.star_subset_prod hA hB hf.1
  obtain ⟨-, h1, h2, h3⟩ := isFunc_iff.1 hf
  have h := F.transfer
    (.conj (.all 0 (.const A) (.ex 1 (.const B) (.elem (.opair (.var 0) (.var 1)) (.const f))))
      (.all 0 (.const A) (.all 1 (.const B) (.all 2 (.const B)
        (.imp (.conj (.elem (.opair (.var 0) (.var 1)) (.const f))
          (.elem (.opair (.var 0) (.var 2)) (.const f))) (.equal (.var 1) (.var 2)))))))
    (by simp [IsSentence, hA.1, hB.1, hfset.1])
  sat_simp at h
  obtain ⟨k1, k2⟩ := h.1 ⟨fun a _ ha => let ⟨b, hb, hab⟩ := h3 a ha; ⟨b, F.hU.subset hB hb, hb, hab⟩,
    fun a _ _ b _ _ c _ _ hbc => h2 a b c hbc.1 hbc.2⟩
  refine ⟨hsub, fun a ha => ?_⟩
  obtain ⟨b, -, hb, hab⟩ := k1 a (F.star_subset_U' hA ha) ha
  refine ⟨b, hab, fun c hc => ?_⟩
  have hc' := (pair_mem_prod.1 (hsub hc)).2
  exact k2 a (F.star_subset_U' hA ha) ha c (F.star_subset_U' hB hc') hc' b
    (F.star_subset_U' hB hb) hb ⟨hc, hab⟩

/-- **Section 13.8, transfer map (14b).** If a function $`f : A \to B` belongs to
$`\mathbb U`, then $`{}^*(f(a)) = {}^*f({}^*a)` for all $`a \in A`. -/
theorem star_app (hA : IsSetOf F.U A) (hB : IsSetOf F.U B) (hf : IsFunc A B f) (ha : a ∈ A) :
    F.star (app f a) = app (F.star f) (F.star a) := by
  have hfset := F.hU.isSetOf_of_isFunc hA hB hf
  have hmem : pair a (app f a) ∈ f := hf.isFunction.pair_app_mem (hf.dom_eq ▸ ha)
  have hb := (pair_mem_prod.1 (hf.1 hmem)).2
  have haU := F.hU.subset hA ha
  have hbU := F.hU.subset hB hb
  have := (F.star_mem_star_iff (F.hU.isSetOf_opair haU hbU).1 hfset.1).2 hmem
  rw [F.star_opair haU hbU] at this
  exact ((F.isFunc_star hA hB hf).isFunction.app_eq this).symm

/-- Injectivity of a relation between two sets of a universe, written with quantifiers
bounded by those sets. -/
theorem _root_.Goldblatt.isInjective_iff_bounded {V : ZFSet.{u}} (hA : A ⊆ V) (hB : B ⊆ V)
    (hf : f ⊆ prod A B) :
    IsInjective f ↔ ∀ a ∈ V, a ∈ A → ∀ a' ∈ V, a' ∈ A → ∀ b ∈ V, b ∈ B →
      pair a b ∈ f ∧ pair a' b ∈ f → a = a' := by
  constructor
  · exact fun h a _ _ a' _ _ b _ _ hab => h a a' b hab.1 hab.2
  · intro h a a' b hab hab'
    have h1 := pair_mem_prod.1 (hf hab)
    have h2 := pair_mem_prod.1 (hf hab')
    exact h a (hA h1.1) h1.1 a' (hA h2.1) h2.1 b (hB h1.2) h1.2 ⟨hab, hab'⟩

/-- **Section 13.8, transfer map (14c).** A function $`f : A \to B` in $`\mathbb U` is
injective if and only if $`{}^*f` is. -/
theorem isInjective_star_iff (hA : IsSetOf F.U A) (hB : IsSetOf F.U B) (hf : IsFunc A B f) :
    IsInjective (F.star f) ↔ IsInjective f := by
  have hfset := F.hU.isSetOf_of_isFunc hA hB hf
  have h := F.transfer
    (.all 0 (.const A) (.all 1 (.const A) (.all 2 (.const B)
        (.imp (.conj (.elem (.opair (.var 0) (.var 2)) (.const f))
          (.elem (.opair (.var 1) (.var 2)) (.const f))) (.equal (.var 0) (.var 1))))))
    (by simp [IsSentence, hA.1, hB.1, hfset.1])
  sat_simp at h
  rw [isInjective_iff_bounded (F.hU.subset hA) (F.hU.subset hB) hf.1,
    isInjective_iff_bounded (F.star_subset_U' hA) (F.star_subset_U' hB)
      (F.star_subset_prod hA hB hf.1)]
  exact h.symm

/-- **Section 13.8, transfer map (14d).** A function $`f : A \to B` in $`\mathbb U` is
surjective if and only if $`{}^*f` is: the range of $`f` is $`B` exactly when the range of
$`{}^*f` is $`{}^*B`. -/
theorem ran_star_eq_iff (hA : IsSetOf F.U A) (hB : IsSetOf F.U B) (hf : IsFunc A B f) :
    ran (F.star f) = F.star B ↔ ran f = B := by
  have hfset := F.hU.isSetOf_of_isFunc hA hB hf
  have hrel := F.hU.relIn_of_subset_prod hA hB hf.1
  rw [← F.star_ran hfset hrel, F.star_eq_iff (F.hU.isSetOf_ran hfset hrel).1 hB.1]

/-- The assignment giving the variables $`0, \dots, n - 1` the values $`c_0, \dots, c_{n-1}`
and every other variable the empty set. -/
def _root_.Goldblatt.envOf {n : ℕ} (c : Fin n → ZFSet.{u}) : ℕ → ZFSet.{u} :=
  fun y => if h : y < n then c ⟨y, h⟩ else ∅

@[simp]
theorem _root_.Goldblatt.envOf_coe {n : ℕ} (c : Fin n → ZFSet.{u}) (i : Fin n) :
    envOf c i = c i := by
  simp [envOf]

/-- Truth of the sentence saying that $`P` is the product of the sets $`A_i`, with the
quantifiers written out. -/
theorem _root_.Goldblatt.sat_tupleProd_sentence {V : ZFSet.{u}} (k : ℕ)
    (A : Fin (k + 2) → ZFSet.{u}) (P : ZFSet.{u}) (v : ℕ → ZFSet.{u}) :
    Sat V v (.conj
        (.all (k + 2) (.const P) (exs (List.ofFn fun i : Fin (k + 2) => ((i : ℕ), A i))
          (.equal (.var (k + 2)) (.tuple k fun i => .var i))))
        (alls (List.ofFn fun i : Fin (k + 2) => ((i : ℕ), A i))
          (.elem (.tuple k fun i => .var i) (.const P)))) ↔
      (∀ a ∈ V, a ∈ P → ∃ c : Fin (k + 2) → ZFSet.{u}, (∀ i, c i ∈ V ∧ c i ∈ A i) ∧
        a = tuple (k + 2) c) ∧
      ∀ c : Fin (k + 2) → ZFSet.{u}, (∀ i, c i ∈ V ∧ c i ∈ A i) → tuple (k + 2) c ∈ P := by
  simp only [Sat, sat_exs, sat_alls, mem_reach_ofFn_iff, Term.Defined, Term.val, true_and,
    implies_true, forall_true_left]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a ha haP => ?_, fun c hc => ?_⟩
    · obtain ⟨w, ⟨hw, hw'⟩, he⟩ := h1 a ha haP
      refine ⟨fun i => w i, hw, ?_⟩
      rw [← he, hw' _ le_rfl, Function.update_self]
    · have := h2 (fun y => if h : y < k + 2 then c ⟨y, h⟩ else v y)
        ⟨fun i => by simpa using hc i, fun y hy => by simp [not_lt.2 hy]⟩
      simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun a ha haP => ?_, fun w hw => h2 _ hw.1⟩
    obtain ⟨c, hc, rfl⟩ := h1 a ha haP
    refine ⟨fun y => if h : y < k + 2 then c ⟨y, h⟩ else Function.update v (k + 2) (tuple (k + 2) c) y,
      ⟨fun i => by simpa using hc i, fun y hy => by simp [not_lt.2 hy]⟩, ?_⟩
    simp

/-- **Section 13.8, transfer map (11).**
$`{}^*(A_1 \times \dots \times A_m) = {}^*A_1 \times \dots \times {}^*A_m`, for $`m = k + 2`.
Taking all factors equal gives $`{}^*(A^m) = ({}^*A)^m`. -/
theorem star_tupleProd (k : ℕ) (A : Fin (k + 2) → ZFSet.{u}) (hA : ∀ i, IsSetOf F.U (A i)) :
    F.star (tupleProd (k + 2) A) = tupleProd (k + 2) fun i => F.star (A i) := by
  have hPset : IsSetOf F.U (tupleProd (k + 2) A) := F.hU.isSetOf_tupleProd _ _ hA
  set l : List (ℕ × ZFSet.{u}) := List.ofFn fun i : Fin (k + 2) => ((i : ℕ), A i) with hl
  have hlU : ∀ p ∈ l, p.2 ∈ F.U := by
    intro p hp
    rw [hl, List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    exact (hA i).1
  have hvars : ∀ i : Fin (k + 2), (i : ℕ) ∈ l.map Prod.fst := fun i =>
    List.mem_map.2 ⟨((i : ℕ), A i), by rw [hl, List.mem_ofFn]; exact ⟨i, rfl⟩, rfl⟩
  let ψ : Formula.{u} := .conj
    (.all (k + 2) (.const (tupleProd (k + 2) A)) (exs l
      (.equal (.var (k + 2)) (.tuple k fun i => .var i))))
    (alls l (.elem (.tuple k fun i => .var i) (.const (tupleProd (k + 2) A))))
  have hsent : ψ.IsSentence F.U :=
    ⟨⟨hPset.1, admissible_exs hlU ⟨Or.inl (Set.mem_insert _ _), fun i => Or.inr (hvars i)⟩⟩,
      admissible_alls hlU ⟨fun i => Or.inr (hvars i), hPset.1⟩⟩
  have h := F.transfer ψ hsent
  have e : ψ.star F.star = .conj
      (.all (k + 2) (.const (F.star (tupleProd (k + 2) A)))
        (exs (List.ofFn fun i : Fin (k + 2) => ((i : ℕ), F.star (A i)))
          (.equal (.var (k + 2)) (.tuple k fun i => .var i))))
      (alls (List.ofFn fun i : Fin (k + 2) => ((i : ℕ), F.star (A i)))
        (.elem (.tuple k fun i => .var i) (.const (F.star (tupleProd (k + 2) A))))) := by
    simp only [ψ, hl, Formula.star, Term.star, star_alls, star_exs, List.map_ofFn]
    rfl
  rw [e] at h
  simp only [Holds, ψ, hl] at h
  rw [sat_tupleProd_sentence, sat_tupleProd_sentence] at h
  obtain ⟨h1, h2⟩ := h.1 ⟨fun a _ ha => by
      obtain ⟨c, hc, rfl⟩ := mem_tupleProd.1 ha
      exact ⟨c, fun i => ⟨F.hU.subset (hA i) (hc i), hc i⟩, rfl⟩,
    fun c hc => mem_tupleProd.2 ⟨c, fun i => (hc i).2, rfl⟩⟩
  ext t
  rw [mem_tupleProd]
  constructor
  · intro ht
    obtain ⟨c, hc, rfl⟩ := h1 t (F.star_subset_U' hPset ht) ht
    exact ⟨c, fun i => (hc i).2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact h2 c fun i => ⟨F.star_subset_U' (hA i) (hc i), hc i⟩

/-- **Section 13.8, transfer map (10).** If $`R \in \mathbb U` is an $`m`-ary relation, on
sets $`A_1, \dots, A_m` of $`\mathbb U`, then $`{}^*R` is an $`m`-ary relation, on
$`{}^*A_1, \dots, {}^*A_m`. -/
theorem star_subset_tupleProd (k : ℕ) (A : Fin (k + 2) → ZFSet.{u})
    (hA : ∀ i, IsSetOf F.U (A i)) (hR : R ⊆ tupleProd (k + 2) A) :
    F.star R ⊆ (tupleProd (k + 2) fun i => F.star (A i)) ∧ IsRelN (k + 2) (F.star R) := by
  have hP := F.hU.isSetOf_tupleProd _ _ hA
  have h : F.star R ⊆ tupleProd (k + 2) fun i => F.star (A i) := by
    rw [← F.star_tupleProd k A hA]
    exact (F.star_subset_star_iff (F.hU.isSetOf_of_subset hP hR) hP).2 hR
  exact ⟨h, fun t ht => let ⟨c, _, hc⟩ := mem_tupleProd.1 (h ht); ⟨c, hc⟩⟩

/-- **Exercise 13.8.2.** If $`\varphi(x_1, \dots, x_m)` is a formula of the language of
$`\mathbb U` and $`A_1, \dots, A_m` are sets in $`\mathbb U`, then
$$`{}^*\{(a_1, \dots, a_m) \in A_1 \times \dots \times A_m : \varphi(a_1, \dots, a_m)\} =
\{(b_1, \dots, b_m) \in {}^*A_1 \times \dots \times {}^*A_m : {}^*\varphi(b_1, \dots, b_m)\}.`
The statement is membership-wise, for $`m = k + 2`, with the free variables of $`\varphi` among
the variables $`0, \dots, m - 1`; the book has all $`A_i` equal. -/
theorem mem_star_sep_tuple (k : ℕ) (A : Fin (k + 2) → ZFSet.{u}) (hA : ∀ i, IsSetOf F.U (A i))
    (φ : Formula.{u}) (hφ : φ.Admissible F.U {y | y < k + 2})
    (hC : ∀ t, t ∈ C ↔ ∃ c : Fin (k + 2) → ZFSet.{u}, (∀ i, c i ∈ A i) ∧ t = tuple (k + 2) c ∧
      Sat F.U (envOf c) φ) (t : ZFSet.{u}) :
    t ∈ F.star C ↔ ∃ c : Fin (k + 2) → ZFSet.{u}, (∀ i, c i ∈ F.star (A i)) ∧
      t = tuple (k + 2) c ∧ Sat F.U' (envOf c) (φ.star F.star) := by
  have hPset : IsSetOf F.U (tupleProd (k + 2) A) := F.hU.isSetOf_tupleProd _ _ hA
  have hCP : C ⊆ tupleProd (k + 2) A := fun t ht => by
    obtain ⟨c, hc, rfl, -⟩ := (hC t).1 ht
    exact mem_tupleProd.2 ⟨c, hc, rfl⟩
  have hCset := F.hU.isSetOf_of_subset hPset hCP
  set l : List (ℕ × ZFSet.{u}) := List.ofFn fun i : Fin (k + 2) => ((i : ℕ), A i) with hl
  have hlU : ∀ p ∈ l, p.2 ∈ F.U := by
    intro p hp
    rw [hl, List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    exact (hA i).1
  have hvars : {y | y ∈ l.map Prod.fst} = {y | y < k + 2} := by
    ext y
    simp only [hl, List.map_ofFn, List.mem_ofFn, Set.mem_ofPred_eq, Function.comp]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ i.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩
  let ψ : Formula.{u} := alls l (.biimp (.elem (.tuple k fun i => .var i) (.const C)) φ)
  have hsent : ψ.IsSentence F.U := by
    refine admissible_alls hlU ?_
    rw [hvars, Set.empty_union]
    exact ⟨⟨fun i => i.2, hCset.1⟩, hφ⟩
  have h := F.transfer ψ hsent
  have e : ψ.star F.star = alls (List.ofFn fun i : Fin (k + 2) => ((i : ℕ), F.star (A i)))
      (.biimp (.elem (.tuple k fun i => .var i) (.const (F.star C))) (φ.star F.star)) := by
    simp only [ψ, hl, Formula.star, Term.star, star_alls, List.map_ofFn]
    rfl
  rw [e] at h
  simp only [Holds, ψ, hl, sat_alls, mem_reach_ofFn_iff, Sat, Term.Defined, Term.val, true_and,
    implies_true] at h
  have hφ' : (φ.star F.star).Admissible F.U' {y | y < k + 2} := hφ.star F.star_mem
  have h' := h.1 (by
    rintro w ⟨hw, -⟩
    have hsat : Sat F.U (envOf fun i : Fin (k + 2) => w i) φ ↔ Sat F.U w φ :=
      sat_congr hφ fun y hy => by simp [envOf, show y < k + 2 from hy]
    rw [hC, ← hsat]
    constructor
    · rintro ⟨c, -, hc, hs⟩
      rwa [funext (tuple_eq_iff.1 hc)]
    · exact fun hs => ⟨fun i => w i, fun i => (hw i).2, rfl, hs⟩)
  constructor
  · intro ht
    have ht' := (F.star_subset_star_iff hCset hPset).2 hCP ht
    rw [F.star_tupleProd k A hA] at ht'
    obtain ⟨c, hc, rfl⟩ := mem_tupleProd.1 ht'
    refine ⟨c, hc, rfl, ?_⟩
    have := h' (envOf c) ⟨fun i => by
      rw [envOf_coe]; exact ⟨F.star_subset_U' (hA i) (hc i), hc i⟩, fun y hy => by simp [envOf, hy]⟩
    simp only [envOf_coe] at this
    exact this.1 ht
  · rintro ⟨c, hc, rfl, hs⟩
    have := h' (envOf c) ⟨fun i => by
      rw [envOf_coe]; exact ⟨F.star_subset_U' (hA i) (hc i), hc i⟩, fun y hy => by simp [envOf, hy]⟩
    simp only [envOf_coe] at this
    exact this.2 hs

/-!
## 13.9 Standard Entities

The members of $`\mathbb U'` of the form $`{}^*a` are the standard entities; all others are
nonstandard. A standard set $`{}^*A` may have nonstandard members, and when it does it differs
from the image $`\{{}^*a : a \in A\}` of $`A` under the transfer map, which is the set of its
standard members (Theorem 13.9.2). The examples of the section that involve the natural and
real numbers (initial segments of the hypernaturals, hyperreal intervals) need the numbers to
be individuals of the framework; they are in part 5.
-/

/-- **Section 13.9, standard entities.** An entity is standard when it is $`{}^*a` for some
$`a \in \mathbb U`. -/
def Standard (b : ZFSet.{u}) : Prop := ∃ a ∈ F.U, b = F.star a

/-- **Section 13.9, nonstandard entities.** The members of $`\mathbb U'` that are not
standard. -/
def Nonstandard (b : ZFSet.{u}) : Prop := b ∈ F.U' ∧ ¬ F.Standard b

theorem standard_star (ha : a ∈ F.U) : F.Standard (F.star a) := ⟨a, ha, rfl⟩

/-- **Section 13.9.** Every element of $`X` is standard. -/
theorem standard_of_mem_base (ha : a ∈ F.X) : F.Standard a :=
  ⟨a, F.hU.subset F.isUniverseOver.base_isSetOf ha, (F.star_individual a ha).symm⟩

/-- **Section 13.9.** If $`A \subseteq X`, then every standard member of $`{}^*A` is in $`A`;
so every member of $`{}^*A - A` is nonstandard. In particular the standard hypernaturals are
the natural numbers. -/
theorem mem_of_standard_of_mem_star (hAX : A ⊆ F.X) (hs : F.Standard b) (hb : b ∈ F.star A) :
    b ∈ A := by
  obtain ⟨a, ha, rfl⟩ := hs
  have hA := F.hU.isSetOf_of_subset F.isUniverseOver.base_isSetOf hAX
  have haA := (F.star_mem_star_iff ha hA.1).1 hb
  rwa [F.star_individual a (hAX haA)]

theorem nonstandard_of_mem_star_sdiff (hAX : A ⊆ F.X) (hb : b ∈ F.star A \ A) :
    F.Nonstandard b := by
  have hA := F.hU.isSetOf_of_subset F.isUniverseOver.base_isSetOf hAX
  rw [mem_sdiff] at hb
  exact ⟨F.star_subset_U' hA hb.1, fun hs => hb.2 (F.mem_of_standard_of_mem_star hAX hs hb.1)⟩

/-- **Section 13.9, image.** The image $`\operatorname{im} A = \{{}^*a : a \in A\}` of a set
under the transfer map. -/
def im (A : ZFSet.{u}) : ZFSet.{u} := ZFSet.range fun a : A => F.star a

@[simp]
theorem mem_im : b ∈ F.im A ↔ ∃ a ∈ A, b = F.star a := by
  rw [im, mem_range]
  exact ⟨fun ⟨a, h⟩ => ⟨a, a.2, h.symm⟩, fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h.symm⟩⟩

/-- **Section 13.9.** The image of $`A` is a subset of $`{}^*A`. -/
theorem im_subset_star (hA : IsSetOf F.U A) : F.im A ⊆ F.star A := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := F.mem_im.1 hb
  exact (F.star_mem_star_iff (F.hU.subset hA ha) hA.1).2 ha

/-- **Section 13.9.** The transfer map is a bijection between $`A` and its image. -/
theorem bijOn_star_im (hA : IsSetOf F.U A) :
    Set.BijOn F.star (A : Set ZFSet.{u}) (F.im A : Set ZFSet.{u}) :=
  ⟨fun a ha => F.mem_im.2 ⟨a, ha, rfl⟩,
    F.star_injOn.mono fun _ ha => F.hU.subset hA ha,
    fun _ hb => let ⟨a, ha, h⟩ := F.mem_im.1 hb; ⟨a, ha, h.symm⟩⟩

/-- **Section 13.9.** If $`A \subseteq X` then $`\operatorname{im} A = A`; for instance the
image of the set of natural numbers is itself. -/
theorem im_eq_of_subset_base (hAX : A ⊆ F.X) : F.im A = A := by
  ext b
  rw [mem_im]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [F.star_individual a (hAX ha)]
  · exact fun hb => ⟨b, hb, (F.star_individual b (hAX hb)).symm⟩

/-- **Section 13.8/13.9.** If $`A` is finite then $`{}^*A = \{{}^*a : a \in A\}`. -/
theorem star_eq_im_of_finite (hA : IsSetOf F.U A) (hfin : (A : Set ZFSet.{u}).Finite) :
    F.star A = F.im A := by
  ext b
  rw [F.mem_star_of_finite hA hfin, mem_im]

/-- **Theorem 13.9.2.** The image of $`A` is the set of all standard members of
$`{}^*A`. Hence $`{}^*A` and its image have the same standard elements, and the nonstandard
members of $`{}^*A` are the members of $`{}^*A - \operatorname{im} A`. -/
theorem mem_im_iff (hA : IsSetOf F.U A) : b ∈ F.im A ↔ b ∈ F.star A ∧ F.Standard b := by
  constructor
  · intro hb
    obtain ⟨a, ha, rfl⟩ := F.mem_im.1 hb
    exact ⟨F.im_subset_star hA hb, a, F.hU.subset hA ha, rfl⟩
  · rintro ⟨hb, a, ha, rfl⟩
    exact F.mem_im.2 ⟨a, (F.star_mem_star_iff ha hA.1).1 hb, rfl⟩

/-- **Theorem 13.9.2, consequence.** The nonstandard members of $`{}^*A` are exactly the
members of $`{}^*A - \operatorname{im} A`. -/
theorem mem_star_sdiff_im_iff (hA : IsSetOf F.U A) :
    b ∈ F.star A \ F.im A ↔ b ∈ F.star A ∧ F.Nonstandard b := by
  rw [mem_sdiff, F.mem_im_iff hA]
  constructor
  · exact fun ⟨hb, hn⟩ => ⟨hb, F.star_subset_U' hA hb, fun hs => hn ⟨hb, hs⟩⟩
  · exact fun ⟨hb, hn⟩ => ⟨hb, fun h => hn.2 h.2⟩

/-- **Exercise 13.9.3.** Standard sets are determined by their standard members: if
$`{}^*A` and $`{}^*B` have the same standard members, then they are equal. -/
theorem star_eq_star_of_standard_mem (hA : IsSetOf F.U A) (hB : IsSetOf F.U B)
    (h : ∀ b, F.Standard b → (b ∈ F.star A ↔ b ∈ F.star B)) : F.star A = F.star B := by
  have : A = B := F.hU.ext hA hB fun x hx => by
    rw [← F.star_mem_star_iff hx hA.1, ← F.star_mem_star_iff hx hB.1]
    exact h _ ⟨x, hx, rfl⟩
  rw [this]

/-- **Section 13.8/13.9.** A finite set of individuals is its own transform. -/
theorem star_eq_self_of_finite_subset_base (hAX : A ⊆ F.X)
    (hfin : (A : Set ZFSet.{u}).Finite) : F.star A = A := by
  rw [F.star_eq_im_of_finite (F.hU.isSetOf_of_subset F.isUniverseOver.base_isSetOf hAX) hfin,
    F.im_eq_of_subset_base hAX]

end NonstandardFramework

/-- **Section 13.8, consistency of the axioms.** Every universe over $`X` carries a
nonstandard framework, the trivial one in which the transfer map is the identity. It has no
nonstandard entities; frameworks that do are constructed in Chapter 14. -/
def NonstandardFramework.trivial {U X : ZFSet.{u}} (h : IsUniverseOver U X) :
    NonstandardFramework.{u} where
  U := U
  X := X
  U' := U
  star := id
  isUniverseOver := h
  isUniverse' := h.toIsUniverse
  star_mem := fun _ ha => ha
  star_individual := fun _ _ => rfl
  star_empty := rfl
  transfer := fun φ _ => by rw [Formula.star_id]

/-- **Section 13.8.** Nonstandard frameworks exist. -/
instance : Nonempty NonstandardFramework.{u} :=
  let ⟨_, _, _, h⟩ := exists_isUniverseOver PEmpty.{u + 1}
  ⟨NonstandardFramework.trivial h⟩

namespace NonstandardFramework

variable (F : NonstandardFramework.{u})

end NonstandardFramework

end Goldblatt
