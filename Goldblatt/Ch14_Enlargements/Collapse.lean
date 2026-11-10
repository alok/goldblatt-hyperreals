import Goldblatt.Ch13_Universes

/-!
# 14 (part 2). The Bounded Ultrapower and Its Collapse: Section 14.3

This is the second of five parts of Chapter 14 (the overview is on the chapter page
{lit}`Goldblatt.Ch14_Enlargements`). It carries out the first half of the ultrapower
construction of Section 14.3: the functions of bounded rank from an index set into a
superstructure, and the map that sends such a function $`f` to an entity $`[f]` of a second
superstructure in such a way that membership and equality of the images are membership and
equality of the functions almost everywhere.
-/

noncomputable section

namespace Goldblatt

open ZFSet Filter
open scoped Classical

universe u v

/-!
## 14.3 Enlargements as Ultrapowers: the collapse

Let $`X` be a set of individuals, $`I` an index set and $`\mathcal F` an ultrafilter on
$`I`. In Chapter 3 the hyperreals were sequences of reals modulo an ultrafilter. The same
idea applied to the whole superstructure $`\mathbb U(X)` runs into a difficulty: a function
from $`I` to $`\mathbb U(X)` can take values of higher and higher rank, and then it does not
represent anything of a definite rank. The construction therefore keeps only the functions of
_bounded rank_, those that take almost all their values in one level $`\mathbb U_n(X)`.

Among functions of bounded rank, membership almost everywhere is a well-founded relation,
because it lowers the rank. This makes it possible to define $`[f]` by recursion: for $`f` of
rank zero it is an individual, and otherwise it is the set of all $`[g]` with
$`g(i) \in f(i)` for almost all $`i`. The individuals $`[f]`, for $`f` of rank zero, form a
set $`Y`, and every $`[f]` lies in the superstructure $`\mathbb U(Y)`. This is the collapsing
map of Mostowski applied to the bounded ultrapower.

Three points need care in the formalization, all of them invisible in the book.

* The index set is a type $`I` that is small relative to the universe level of the sets, and
  functions on it are functions of Lean, not sets. For $`[f]` to be a set, the functions over
  which the recursion ranges are replaced by a small type of representatives
  ({lit}`BoundedUltrapower.Rep`).
* Individuals are sets none of whose members lie in the universe (Chapter 13). The members of
  $`X` must be fixed by the construction, so they are also individuals of the new universe, and
  it has to be checked that they remain individuals relative to the larger superstructure
  $`\mathbb U(Y)`. The new individuals are chosen of large set-theoretic rank to make this true
  ({lit}`BoundedUltrapower.isBaseSet_base`).
* The book states the two basic properties of the map $`f \mapsto [f]`, for equality and for
  membership, without proof. They are {lit}`BoundedUltrapower.col_eq_iff` and
  {lit}`BoundedUltrapower.col_mem_col_iff`, proved by induction on rank.

### Functions of bounded rank
-/

namespace BoundedUltrapower

variable {I : Type v} (𝓕 : Ultrafilter I) (X : ZFSet.{u})

/-- **Section 14.3, the sets $`Z_n` and $`Z`.** A function $`f` on $`I` is of bounded rank
when for some $`n` the set of indices $`i` with $`f(i) \in \mathbb U_n(X)` is in the
ultrafilter; that condition for a fixed $`n` is the book's $`f \in Z_n`, and the functions of
bounded rank form $`Z = \bigcup_n Z_n`. The Lean definition differs in shape from the book's:
there $`Z_n` consists of functions all of whose values are in $`\mathbb U(X)`, while here the
values of $`f` off a set of the ultrafilter are unconstrained. Every such $`f` agrees almost
everywhere with a function into $`\mathbb U_n(X)` ({lit}`exists_rep`), and the collapse depends
only on the values almost everywhere ({lit}`col_congr`), so this is the book's $`Z` up to
almost-everywhere equality. -/
def Bdd (f : I → ZFSet.{u}) : Prop := ∃ n, ∀ᶠ i in 𝓕, f i ∈ cumPow X n

/-- **Section 14.3, the set $`Z_0`.** A function is of rank zero when almost all of
its values are individuals. As for {lit}`Bdd`, the values off a set of the ultrafilter are not
constrained. -/
def Atomic (f : I → ZFSet.{u}) : Prop := ∀ᶠ i in 𝓕, f i ∈ X

/-- **Section 14.3, membership modulo the ultrafilter.** For functions of bounded rank,
$`f \mathrel E g` when $`\{i : f(i) \in g(i)\}` belongs to the ultrafilter. -/
def E (f g : I → ZFSet.{u}) : Prop := Bdd 𝓕 X f ∧ Bdd 𝓕 X g ∧ ∀ᶠ i in 𝓕, f i ∈ g i

/-- **Section 14.3, rank of a function.** The least $`n` such that almost all values of
$`f` lie in $`\mathbb U_n(X)`. -/
def rk (f : I → ZFSet.{u}) : ℕ := sInf {n | ∀ᶠ i in 𝓕, f i ∈ cumPow X n}

variable {𝓕 X} {f g h : I → ZFSet.{u}}

/-- Bounded rank depends only on the values on a set of the ultrafilter. -/
theorem Bdd.congr (hf : Bdd 𝓕 X f) (hfg : f =ᶠ[𝓕] g) : Bdd 𝓕 X g := by
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, by filter_upwards [hn, hfg] with i h1 h2; rwa [← h2]⟩

/-- **Section 14.3.** A constant function $`a^I` with $`a \in \mathbb U(X)` is of
bounded rank. -/
theorem bdd_const {a : ZFSet.{u}} (ha : a ∈ superstructure X) : Bdd 𝓕 X fun _ => a := by
  obtain ⟨n, hn⟩ := mem_superstructure.1 ha
  exact ⟨n, Eventually.of_forall fun _ => hn⟩

/-- Almost all values of a function of bounded rank lie in the
superstructure. -/
theorem Bdd.eventually_mem (hf : Bdd 𝓕 X f) : ∀ᶠ i in 𝓕, f i ∈ superstructure X := by
  obtain ⟨n, hn⟩ := hf
  exact hn.mono fun i hi => cumPow_subset_superstructure n hi

/-- A function of rank zero is of bounded rank. -/
theorem Atomic.bdd (hf : Atomic 𝓕 X f) : Bdd 𝓕 X f := ⟨0, hf⟩

/-- Being of rank zero depends only on the values on a set of the ultrafilter. -/
theorem Atomic.congr (hf : Atomic 𝓕 X f) (hfg : f =ᶠ[𝓕] g) : Atomic 𝓕 X g := by
  filter_upwards [hf, hfg] with i h1 h2; rwa [← h2]

/-- A member of a member of $`\mathbb U_{n+1}(X)` that belongs to the
superstructure lies in $`\mathbb U_n(X)`: individuals have no members there. -/
theorem mem_cumPow_of_mem (hX : IsBaseSet X) {n : ℕ} {y z : ZFSet.{u}}
    (hy : y ∈ cumPow X (n + 1)) (hz : z ∈ y) (hzW : z ∈ superstructure X) : z ∈ cumPow X n :=
  subset_cumPow_of_mem_succ hy (fun h => (hX y h).2 z hzW hz) hz

/-- A function whose values are almost everywhere members of the values
of a function of bounded rank, and lie in the superstructure, is of bounded rank. -/
theorem bdd_of_eventually_mem (hX : IsBaseSet X) (hg : Bdd 𝓕 X g)
    (hf : ∀ᶠ i in 𝓕, f i ∈ superstructure X ∧ f i ∈ g i) : Bdd 𝓕 X f := by
  obtain ⟨n, hn⟩ := hg
  refine ⟨n, ?_⟩
  filter_upwards [hn, hf] with i h1 h2
  exact mem_cumPow_of_mem hX (cumPow_subset_succ n h1) h2.2 h2.1

/-- A function is not of rank zero exactly when almost none of its values is an
individual; this uses that the filter is an ultrafilter. -/
theorem not_atomic_iff : ¬ Atomic 𝓕 X f ↔ ∀ᶠ i in 𝓕, f i ∉ X :=
  Ultrafilter.eventually_not.symm

/-- **Section 14.3, the chain $`Z_0 \subseteq Z_1 \subseteq \cdots`.** If $`m \le n` then
$`Z_m \subseteq Z_n`: a function with almost all values in $`\mathbb U_m(X)` has almost all
values in $`\mathbb U_n(X)`. -/
theorem eventually_mem_cumPow_mono {m n : ℕ} (h : m ≤ n) (hf : ∀ᶠ i in 𝓕, f i ∈ cumPow X m) :
    ∀ᶠ i in 𝓕, f i ∈ cumPow X n :=
  hf.mono fun _ hi => cumPow_mono h hi

/-!
### The rank of a function

A function of bounded rank has a rank of its own: the ranks of its values are almost
everywhere one and the same number, which is also the least $`n` with $`f \in Z_n`. Membership
almost everywhere lowers this rank, which is why it is a well-founded relation.
-/

/-- Almost all values of a function of bounded rank lie in the level
given by its rank. -/
theorem eventually_mem_cumPow_rk (hf : Bdd 𝓕 X f) : ∀ᶠ i in 𝓕, f i ∈ cumPow X (rk 𝓕 X f) :=
  Nat.sInf_mem hf

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

/-- **Section 14.3, rank of a function.** For $`f \in Z`, the rank {lit}`rk` of $`f` is at
most $`n` exactly when $`f \in Z_n`. -/
theorem rk_le_iff {f : I → ZFSet.{u}} (hf : Bdd 𝓕 X f) {n : ℕ} :
    rk 𝓕 X f ≤ n ↔ ∀ᶠ i in 𝓕, f i ∈ cumPow X n :=
  ⟨fun h => (eventually_mem_cumPow_rk hf).mono fun _ hi => cumPow_mono h hi,
    fun h => Nat.sInf_le h⟩

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

/-- **Section 14.3, rank of a function.** The functions of rank $`0` are those in $`Z_0`. -/
theorem rk_eq_zero_iff {f : I → ZFSet.{u}} (hf : Bdd 𝓕 X f) : rk 𝓕 X f = 0 ↔ Atomic 𝓕 X f := by
  rw [← Nat.le_zero, rk_le_iff hf]
  rfl

/-- **Section 14.3, rank of a function.** The rank of the constant function $`a^I` is the rank
of the entity $`a` in $`\mathbb U(X)`. -/
theorem rk_const {a : ZFSet.{u}} (ha : a ∈ superstructure X) :
    rk 𝓕 X (fun _ : I => a) = rank X a := by
  obtain ⟨_, h⟩ := (eventually_rank_eq_rk (𝓕 := 𝓕) (bdd_const ha)).exists
  exact h.symm

/-- **Section 14.3.** Membership modulo the ultrafilter lowers the rank: if
$`f \mathrel E g` then the rank of $`f` is smaller than that of $`g`. -/
theorem E.rk_lt (hX : IsBaseSet X) (h : E 𝓕 X f g) : rk 𝓕 X f < rk 𝓕 X g := by
  obtain ⟨hf, hg, hfg⟩ := h
  have hgr := eventually_mem_cumPow_rk hg
  have hfW := hf.eventually_mem
  cases hr : rk 𝓕 X g with
  | zero =>
    rw [hr] at hgr
    have : ∀ᶠ _ in (𝓕 : Filter I), False := by
      filter_upwards [hgr, hfg, hfW] with i h1 h2 h3
      exact (hX _ h1).2 _ h3 h2
    exact this.exists.elim (fun _ h => h.elim)
  | succ k =>
    rw [hr] at hgr
    have : ∀ᶠ i in 𝓕, f i ∈ cumPow X k := by
      filter_upwards [hgr, hfg, hfW] with i h1 h2 h3
      exact mem_cumPow_of_mem hX h1 h2 h3
    exact Nat.lt_succ_of_le (Nat.sInf_le this)

/-- **Section 14.3.** Membership modulo the ultrafilter is a well-founded relation on
functions of bounded rank, since it lowers the rank. This is what allows the definition of
$`[f]` by recursion; without the bound on ranks an ultrapower of a universe need not be
well-founded. -/
theorem E_wf (hX : IsBaseSet X) : WellFounded (E 𝓕 X) :=
  Subrelation.wf (fun h => E.rk_lt hX h) (measure (rk 𝓕 X)).wf



/-!
### The individuals of the ultrapower

The class of a function of rank zero has to be an individual of the new universe, and the
class of a function that is almost everywhere a fixed $`x \in X` has to be $`x` itself. All
other classes are assigned new individuals. A new individual is the singleton of a set that
contains the whole superstructure over $`X` as a member of a member, so it cannot occur at any
finite level over the old and new individuals.
-/

variable (𝓕 X)

/-- A new individual with a given code: the singleton of the pair of the
superstructure and the code. Its only member is not in any superstructure built over the old
and new individuals, which is what makes it an individual there. -/
def newAtom (c : ZFSet.{u}) : ZFSet.{u} := {pair (superstructure X) c}

/-- Functions into the individuals (with the empty set as a default value) modulo
the ultrafilter. -/
abbrev AtomGerm := (𝓕 : Filter I).Germ ↥(insert (∅ : ZFSet.{u}) X)

/-- The class modulo the ultrafilter of a function, with values that are not
individuals replaced by the empty set. -/
def atomGerm (f : I → ZFSet.{u}) : AtomGerm 𝓕 X :=
  ((fun i => if h : f i ∈ X then ⟨f i, mem_insert_of_mem _ h⟩ else ⟨∅, mem_insert _ _⟩ :
    I → ↥(insert (∅ : ZFSet.{u}) X)) : AtomGerm 𝓕 X)

variable [Small.{u} I]

/-- The classes of functions into a set, on a small index type, form a small type. -/
instance : Small.{u} (AtomGerm 𝓕 X) :=
  inferInstanceAs (Small.{u} (Quotient (germSetoid (𝓕 : Filter I) _)))

/-- An injection of the classes of rank-zero functions into sets, through a well-ordering
of a small copy of the type of classes. -/
def enc (q : AtomGerm 𝓕 X) : ZFSet.{u} :=
  (Ordinal.typein (WellOrderingRel (α := Shrink.{u} (AtomGerm 𝓕 X))) (equivShrink _ q)).toZFSet

/-- **Section 14.3, the individual $`[f]` for $`f \in Z_0`.** The class of a function
that is almost everywhere equal to an individual $`x \in X` is $`x` itself, so that $`x` is
identified with $`{}^*x`; the class of any other function of rank zero is a new individual. -/
def atomOf (f : I → ZFSet.{u}) : ZFSet.{u} :=
  if h : ∃ x ∈ X, atomGerm 𝓕 X f = atomGerm 𝓕 X fun _ => x then h.choose
  else newAtom X (enc 𝓕 X (atomGerm 𝓕 X f))

/-- **Section 14.3, the set $`Y = \{[f] : f \in Z_0\}`.** The set of individuals of
the ultrapower, which turns out to be $`{}^*X`. -/
def base : ZFSet.{u} := ZFSet.range fun h : I → ↥X => atomOf 𝓕 X fun i => (h i).1

variable {𝓕 X}

omit [Small.{u} I] in
/-- Functions that agree almost everywhere have the same class. -/
theorem atomGerm_congr (hfg : f =ᶠ[𝓕] g) : atomGerm 𝓕 X f = atomGerm 𝓕 X g :=
  Germ.coe_eq.2 (hfg.mono fun i hi => by simp only [hi])

omit [Small.{u} I] in
/-- Functions of rank zero with the same class agree almost
everywhere. -/
theorem eventuallyEq_of_atomGerm_eq (hf : Atomic 𝓕 X f) (hg : Atomic 𝓕 X g)
    (h : atomGerm 𝓕 X f = atomGerm 𝓕 X g) : f =ᶠ[𝓕] g := by
  have h' := Germ.coe_eq.1 h
  filter_upwards [hf, hg, h'] with i h1 h2 h3
  simpa [h1, h2, Subtype.ext_iff] using h3

/-- The individual assigned to a function depends only on its values on a set of
the ultrafilter. -/
theorem atomOf_congr (hfg : f =ᶠ[𝓕] g) : atomOf 𝓕 X f = atomOf 𝓕 X g := by
  simp only [atomOf, atomGerm_congr hfg]

/-- **Section 14.3.** The individual assigned to the constant function $`x^I`,
for $`x \in X`, is $`x`. -/
theorem atomOf_const {x : ZFSet.{u}} (hx : x ∈ X) : atomOf 𝓕 X (fun _ => x) = x := by
  rw [atomOf]
  split_ifs with h
  · have h1 := eventuallyEq_of_atomGerm_eq (Eventually.of_forall fun _ => hx)
      (Eventually.of_forall fun _ => h.choose_spec.1) h.choose_spec.2
    obtain ⟨_, hi⟩ := h1.exists
    exact hi.symm
  · exact absurd ⟨x, hx, rfl⟩ h

/-- The individual assigned to a function is either an old individual or a new
one. -/
theorem atomOf_mem_or (f : I → ZFSet.{u}) :
    atomOf 𝓕 X f ∈ X ∨ ∃ c, atomOf 𝓕 X f = newAtom X c := by
  rw [atomOf]
  split_ifs with h
  · exact Or.inl h.choose_spec.1
  · exact Or.inr ⟨_, rfl⟩

/-- A new individual has larger set-theoretic rank than the
superstructure over $`X`. -/
theorem rank_lt_rank_newAtom (c : ZFSet.{u}) :
    (superstructure X).rank < (newAtom X c).rank := by
  have h1 : superstructure X ∈ ({superstructure X} : ZFSet.{u}) := mem_singleton.2 rfl
  have h2 : ({superstructure X} : ZFSet.{u}) ∈ pair (superstructure X) c := singleton_mem_pair
  have h3 : pair (superstructure X) c ∈ newAtom X c := mem_singleton.2 rfl
  exact (ZFSet.rank_lt_of_mem h1).trans ((ZFSet.rank_lt_of_mem h2).trans (ZFSet.rank_lt_of_mem h3))

/-- A member of $`X` has smaller set-theoretic rank than the
superstructure over $`X`. -/
theorem rank_lt_of_mem_base {x : ZFSet.{u}} (hx : x ∈ X) : x.rank < (superstructure X).rank :=
  (ZFSet.rank_lt_of_mem hx).trans (ZFSet.rank_lt_of_mem base_mem_superstructure)

/-- A new individual is not a member of $`X`. -/
theorem newAtom_notMem (c : ZFSet.{u}) : newAtom X c ∉ X := fun h =>
  lt_asymm (rank_lt_rank_newAtom c) (rank_lt_of_mem_base h)

/-- New individuals with different codes are different. -/
theorem newAtom_injective : Function.Injective (newAtom X) := fun _ _ h =>
  (pair_inj.1 (singleton_injective h)).2

/-- Different classes have different codes. -/
theorem enc_injective : Function.Injective (enc 𝓕 X) := fun _ _ h =>
  (equivShrink _).injective (Ordinal.typein_injective _ (Ordinal.toZFSet_injective h))

/-- **Section 14.3.** For $`f, g \in Z_0`: if $`[f] = [g]` then
$`\{i : f(i) = g(i)\}` is in the ultrafilter. -/
theorem atomOf_inj (hf : Atomic 𝓕 X f) (hg : Atomic 𝓕 X g)
    (h : atomOf 𝓕 X f = atomOf 𝓕 X g) : f =ᶠ[𝓕] g := by
  apply eventuallyEq_of_atomGerm_eq hf hg
  rw [atomOf, atomOf] at h
  split_ifs at h with h1 h2 h2
  · rw [h1.choose_spec.2, h2.choose_spec.2, h]
  · exact absurd (h ▸ h1.choose_spec.1) (newAtom_notMem _)
  · exact absurd (h ▸ h2.choose_spec.1) (newAtom_notMem _)
  · exact enc_injective (newAtom_injective h)

/-- The individual assigned to a function of rank zero belongs to $`Y`. -/
theorem atomOf_mem_base (hf : Atomic 𝓕 X f) : atomOf 𝓕 X f ∈ base 𝓕 X := by
  obtain ⟨i0, hi0⟩ := hf.exists
  refine mem_range.2 ⟨fun i => if hi : f i ∈ X then ⟨f i, hi⟩ else ⟨f i0, hi0⟩, atomOf_congr ?_⟩
  filter_upwards [hf] with i hi
  simp [hi]

/-- Every member of $`Y` is the individual assigned to a function of
rank zero. -/
theorem exists_atomic_of_mem_base {y : ZFSet.{u}} (hy : y ∈ base 𝓕 X) :
    ∃ f, Atomic 𝓕 X f ∧ atomOf 𝓕 X f = y := by
  obtain ⟨h, rfl⟩ := mem_range.1 hy
  exact ⟨_, Eventually.of_forall fun i => (h i).2, rfl⟩

/-- **Section 14.3.** $`X \subseteq Y`. -/
theorem base_subset : X ⊆ base 𝓕 X := fun x hx =>
  mem_range.2 ⟨fun _ => ⟨x, hx⟩, atomOf_const hx⟩

/-- A member of $`Y` is an old individual or a new one. -/
theorem mem_base_cases {y : ZFSet.{u}} (hy : y ∈ base 𝓕 X) : y ∈ X ∨ ∃ c, y = newAtom X c := by
  obtain ⟨h, rfl⟩ := mem_range.1 hy
  exact atomOf_mem_or _

/-- A member of $`\mathbb U_n(Y)` whose set-theoretic rank is at most
that of $`\mathbb U(X)` belongs to $`\mathbb U_n(X)`: the new individuals, the only difference
between the two superstructures, have larger rank. -/
theorem mem_cumPow_of_rank_le :
    ∀ (n : ℕ) {z : ZFSet.{u}}, z ∈ cumPow (base 𝓕 X) n → z.rank ≤ (superstructure X).rank →
      z ∈ cumPow X n
  | 0, z, hz, hr => by
    rcases mem_base_cases hz with h | ⟨c, rfl⟩
    · exact h
    · exact absurd hr (not_le.2 (rank_lt_rank_newAtom c))
  | n + 1, z, hz, hr => by
    rw [cumPow_succ, mem_union] at hz
    rcases hz with hz | hz
    · exact cumPow_subset_succ n (mem_cumPow_of_rank_le n hz hr)
    · exact mem_cumPow_succ_of_subset fun w hw =>
        mem_cumPow_of_rank_le n (mem_powerset.1 hz hw) ((ZFSet.rank_lt_of_mem hw).le.trans hr)

/-- The superstructure over $`X` is not a member of the
superstructure over $`Y`. -/
theorem superstructure_notMem_cumPow_base (n : ℕ) :
    superstructure X ∉ cumPow (base 𝓕 X) n := fun h =>
  mem_irrefl _ (cumPow_subset_superstructure n (mem_cumPow_of_rank_le n h le_rfl))

/-- The singleton of the superstructure over $`X` is not
a member of $`Y`. -/
theorem singleton_superstructure_notMem_base :
    ({superstructure X} : ZFSet.{u}) ∉ base 𝓕 X := fun h => by
  have h1 : superstructure X ∈ ({superstructure X} : ZFSet.{u}) := mem_singleton.2 rfl
  rcases mem_base_cases h with h | ⟨c, hc⟩
  · exact lt_asymm (ZFSet.rank_lt_of_mem h1) (rank_lt_of_mem_base h)
  · have h2 : superstructure X = pair (superstructure X) c := singleton_injective hc
    have h3 : ({superstructure X} : ZFSet.{u}) ∈ pair (superstructure X) c := singleton_mem_pair
    rw [← h2] at h3
    exact lt_asymm (ZFSet.rank_lt_of_mem h1) (ZFSet.rank_lt_of_mem h3)

/-- The singleton of the superstructure over $`X`
is not a member of the superstructure over $`Y`. -/
theorem singleton_superstructure_notMem_cumPow_base (n : ℕ) :
    ({superstructure X} : ZFSet.{u}) ∉ cumPow (base 𝓕 X) n := by
  cases n with
  | zero => exact singleton_superstructure_notMem_base
  | succ n =>
    exact fun h => superstructure_notMem_cumPow_base n
      (subset_cumPow_of_mem_succ h singleton_superstructure_notMem_base (mem_singleton.2 rfl))

/-- The only member of a new individual is not a member of
$`Y`. -/
theorem pair_superstructure_notMem_base (c : ZFSet.{u}) :
    pair (superstructure X) c ∉ base 𝓕 X := fun h => by
  have h1 : superstructure X ∈ ({superstructure X} : ZFSet.{u}) := mem_singleton.2 rfl
  have h2 : ({superstructure X} : ZFSet.{u}) ∈ pair (superstructure X) c := singleton_mem_pair
  rcases mem_base_cases h with h | ⟨d, hd⟩
  · exact lt_asymm ((ZFSet.rank_lt_of_mem h1).trans (ZFSet.rank_lt_of_mem h2)) (rank_lt_of_mem_base h)
  · rw [hd, newAtom, mem_singleton] at h2
    have h3 : ({superstructure X} : ZFSet.{u}) ∈ pair (superstructure X) d := singleton_mem_pair
    rw [← h2] at h3
    exact mem_irrefl _ h3

/-- The only member of a new individual is not a
member of the superstructure over $`Y`. -/
theorem pair_superstructure_notMem_cumPow_base (c : ZFSet.{u}) (n : ℕ) :
    pair (superstructure X) c ∉ cumPow (base 𝓕 X) n := by
  cases n with
  | zero => exact pair_superstructure_notMem_base c
  | succ n =>
    exact fun h => singleton_superstructure_notMem_cumPow_base n
      (subset_cumPow_of_mem_succ h (pair_superstructure_notMem_base c) singleton_mem_pair)

/-- **Section 14.3.** The members of $`Y` are individuals relative to the
superstructure $`\mathbb U(Y)`, so that $`\mathbb U(Y)` is a universe over $`Y`. In the book
this is true by decree; here the new individuals have to be chosen so that it holds, and the
old ones have to remain individuals in the larger superstructure. -/
theorem isBaseSet_base (hX : IsBaseSet X) : IsBaseSet (base 𝓕 X) := by
  intro y hy
  rcases mem_base_cases hy with h | ⟨c, rfl⟩
  · refine ⟨(hX y h).1, fun m hm hmy => ?_⟩
    obtain ⟨n, hn⟩ := mem_superstructure.1 hm
    exact (hX y h).2 m (cumPow_subset_superstructure n (mem_cumPow_of_rank_le n hn
      ((ZFSet.rank_lt_of_mem hmy).trans (rank_lt_of_mem_base h)).le)) hmy
  · refine ⟨fun h => notMem_empty (pair (superstructure X) c) (h ▸ mem_singleton.2 rfl),
      fun m hm hmy => ?_⟩
    obtain ⟨n, hn⟩ := mem_superstructure.1 hm
    rw [newAtom, mem_singleton] at hmy
    exact pair_superstructure_notMem_cumPow_base c n (hmy ▸ hn)

/-!
### The collapse

The map $`f \mapsto [f]` is defined by well-founded recursion, and then its basic properties
are proved: it depends only on the class of $`f`, it maps functions of rank at most $`n` into
$`\mathbb U_n(Y)`, and it is injective and membership-preserving modulo the ultrafilter.
-/

/-- Representatives of the functions of bounded rank that form a small type: a level $`n`
and a function into $`\mathbb U_n(X)`. -/
abbrev Rep (X : ZFSet.{u}) (I : Type v) := Σ n : ℕ, I → ↥(cumPow X n)

/-- The function into sets given by a representative. -/
def Rep.lift (r : Rep X I) : I → ZFSet.{u} := fun i => (r.2 i).1

omit [Small.{u} I] in
/-- The function given by a representative is of bounded rank. -/
theorem Rep.bdd (r : Rep X I) : Bdd 𝓕 X r.lift :=
  ⟨r.1, Eventually.of_forall fun i => (r.2 i).2⟩

omit [Small.{u} I] in
/-- Every function of bounded rank agrees almost everywhere with the function
given by a representative. -/
theorem exists_rep (hf : Bdd 𝓕 X f) : ∃ r : Rep X I, r.lift =ᶠ[𝓕] f := by
  obtain ⟨n, hn⟩ := hf
  have h0 : (∅ : ZFSet.{u}) ∈ cumPow X (n + 1) := mem_cumPow_succ_of_subset (empty_subset _)
  refine ⟨⟨n + 1, fun i =>
    if hi : f i ∈ cumPow X n then ⟨f i, cumPow_subset_succ n hi⟩ else ⟨∅, h0⟩⟩, ?_⟩
  filter_upwards [hn] with i hi
  simp [Rep.lift, hi]

variable (𝓕) in
/-- **Section 14.3, the map $`f \mapsto [f]`.** The collapse of the bounded ultrapower
into the superstructure over $`Y`, defined by recursion on rank: for $`f \in Z_0` it is the
individual assigned to $`f`, and otherwise
$$`[g] = \{[f] : f \in Z,\ \{i : f(i) \in g(i)\} \in \mathcal F\}.`
The recursion is well-founded recursion along membership modulo the ultrafilter. So that the
right-hand side is a set, $`f` ranges over a small type of representatives. -/
def col (hX : IsBaseSet X) : (I → ZFSet.{u}) → ZFSet.{u} :=
  (E_wf (𝓕 := 𝓕) hX).fix fun g rec =>
    if Atomic 𝓕 X g then atomOf 𝓕 X g
    else ZFSet.range fun r : {r : Rep X I // E 𝓕 X r.lift g} => rec r.1.lift r.2

/-- The defining equation of the collapse. -/
theorem col_eq (hX : IsBaseSet X) (g : I → ZFSet.{u}) :
    col 𝓕 hX g = if Atomic 𝓕 X g then atomOf 𝓕 X g
      else ZFSet.range fun r : {r : Rep X I // E 𝓕 X r.lift g} => col 𝓕 hX r.1.lift :=
  (E_wf (𝓕 := 𝓕) hX).fix_eq _ g

/-- **Section 14.3.** On a function of rank zero the collapse is the assigned
individual. -/
theorem col_atomic (hX : IsBaseSet X) (hg : Atomic 𝓕 X g) : col 𝓕 hX g = atomOf 𝓕 X g := by
  rw [col_eq]
  simp only [hg, ↓reduceIte]

/-- The collapse of a function that is not of rank zero, as the set of
collapses of representatives. -/
theorem col_not_atomic (hX : IsBaseSet X) (hg : ¬ Atomic 𝓕 X g) :
    col 𝓕 hX g = ZFSet.range fun r : {r : Rep X I // E 𝓕 X r.lift g} => col 𝓕 hX r.1.lift := by
  rw [col_eq]
  simp only [hg, ↓reduceIte]

omit [Small.{u} I] in
/-- Membership modulo the ultrafilter respects almost-everywhere equality on the
right. -/
theorem E.congr_right (hfg : f =ᶠ[𝓕] g) (hE : E 𝓕 X h f) : E 𝓕 X h g :=
  ⟨hE.1, hE.2.1.congr hfg, by filter_upwards [hE.2.2, hfg] with i a b; rwa [← b]⟩

omit [Small.{u} I] in
/-- Membership modulo the ultrafilter respects almost-everywhere equality on the
left. -/
theorem E.congr_left (hfg : f =ᶠ[𝓕] g) (hE : E 𝓕 X f h) : E 𝓕 X g h :=
  ⟨hE.1.congr hfg, hE.2.1, by filter_upwards [hE.2.2, hfg] with i a b; rwa [← b]⟩

/-- **Section 14.3.** Functions that agree on a set of the ultrafilter have the same
collapse. -/
theorem col_congr (hX : IsBaseSet X) (hfg : f =ᶠ[𝓕] g) : col 𝓕 hX f = col 𝓕 hX g := by
  by_cases hA : Atomic 𝓕 X f
  · rw [col_atomic hX hA, col_atomic hX (hA.congr hfg), atomOf_congr hfg]
  · rw [col_not_atomic hX hA, col_not_atomic hX fun hg => hA (hg.congr hfg.symm)]
    ext y
    rw [mem_range, mem_range]
    constructor
    · rintro ⟨⟨r, hr⟩, rfl⟩
      exact ⟨⟨r, hr.congr_right hfg⟩, rfl⟩
    · rintro ⟨⟨r, hr⟩, rfl⟩
      exact ⟨⟨r, hr.congr_right hfg.symm⟩, rfl⟩

/-- **Section 14.3, the inductive clause.** If $`g` is not of rank zero, the members
of $`[g]` are the $`[f]` with $`f \in Z` and $`\{i : f(i) \in g(i)\} \in \mathcal F`. -/
theorem mem_col (hX : IsBaseSet X) (hg : ¬ Atomic 𝓕 X g) {y : ZFSet.{u}} :
    y ∈ col 𝓕 hX g ↔ ∃ f, E 𝓕 X f g ∧ col 𝓕 hX f = y := by
  rw [col_not_atomic hX hg, mem_range]
  constructor
  · rintro ⟨⟨r, hr⟩, rfl⟩
    exact ⟨_, hr, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨r, hr⟩ := exists_rep hf.1
    exact ⟨⟨r, hf.congr_left hr.symm⟩, col_congr hX hr⟩

/-- **Section 14.3.** If $`f \in Z_n` then $`[f] \in \mathbb U_n(Y)`. -/
theorem col_mem_cumPow (hX : IsBaseSet X) :
    ∀ (n : ℕ) {f : I → ZFSet.{u}}, (∀ᶠ i in 𝓕, f i ∈ cumPow X n) →
      col 𝓕 hX f ∈ cumPow (base 𝓕 X) n
  | 0, f, hf => by
    rw [col_atomic hX hf]
    exact atomOf_mem_base hf
  | n + 1, f, hf => by
    by_cases hA : Atomic 𝓕 X f
    · rw [col_atomic hX hA]
      exact cumPow_mono (Nat.zero_le _) (atomOf_mem_base hA)
    · refine mem_cumPow_succ_of_subset fun y hy => ?_
      obtain ⟨h, hE, rfl⟩ := (mem_col hX hA).1 hy
      refine col_mem_cumPow hX n ?_
      filter_upwards [hf, hE.2.2, hE.1.eventually_mem] with i h1 h2 h3
      exact mem_cumPow_of_mem hX h1 h2 h3

/-- **Section 14.3.** The collapse maps $`Z` into the superstructure
$`\mathbb U(Y)`. -/
theorem col_mem (hX : IsBaseSet X) (hf : Bdd 𝓕 X f) :
    col 𝓕 hX f ∈ superstructure (base 𝓕 X) := by
  obtain ⟨n, hn⟩ := hf
  exact cumPow_subset_superstructure n (col_mem_cumPow hX n hn)

/-- The collapse of a function of rank zero is an individual of
$`\mathbb U(Y)`. -/
theorem isIndividual_col (hX : IsBaseSet X) (hf : Atomic 𝓕 X f) :
    IsIndividual (superstructure (base 𝓕 X)) (col 𝓕 hX f) := by
  rw [col_atomic hX hf]
  exact isBaseSet_base hX _ (atomOf_mem_base hf)

/-- The collapse of a function of rank zero differs from the collapse
of a function that is not of rank zero: the first is an individual and the second is a set of
$`\mathbb U(Y)`. -/
theorem col_ne_of_atomic_of_not (hX : IsBaseSet X) (hf : Atomic 𝓕 X f) (hg : ¬ Atomic 𝓕 X g) :
    col 𝓕 hX f ≠ col 𝓕 hX g := fun h => by
  have hind := isIndividual_col hX hf
  rw [h] at hind
  obtain ⟨y, hy⟩ := (eq_empty_or_nonempty (col 𝓕 hX g)).resolve_left hind.1
  obtain ⟨h', hE, rfl⟩ := (mem_col hX hg).1 hy
  exact hind.2 _ (col_mem hX hE.1) hy

/-- Injectivity of the collapse modulo the ultrafilter, by
induction on a common level $`n` of the two functions. The inductive step is extensionality: if
$`f` and $`g` differ almost everywhere, a function choosing a member of the symmetric difference
of $`f(i)` and $`g(i)` has its collapse in exactly one of $`[f]` and $`[g]`. -/
theorem eventuallyEq_of_col_eq_aux (hX : IsBaseSet X) (n : ℕ) :
    ∀ {f g : I → ZFSet.{u}}, (∀ᶠ i in 𝓕, f i ∈ cumPow X n) → (∀ᶠ i in 𝓕, g i ∈ cumPow X n) →
      col 𝓕 hX f = col 𝓕 hX g → f =ᶠ[𝓕] g := by
  induction n with
  | zero =>
    intro f g hf hg h
    rw [col_atomic hX hf, col_atomic hX hg] at h
    exact atomOf_inj hf hg h
  | succ n ih =>
    intro f g hf hg h
    by_cases hAf : Atomic 𝓕 X f
    · by_cases hAg : Atomic 𝓕 X g
      · rw [col_atomic hX hAf, col_atomic hX hAg] at h
        exact atomOf_inj hAf hAg h
      · exact absurd h (col_ne_of_atomic_of_not hX hAf hAg)
    · by_cases hAg : Atomic 𝓕 X g
      · exact absurd h.symm (col_ne_of_atomic_of_not hX hAg hAf)
      · have key : ∀ {f g : I → ZFSet.{u}}, (∀ᶠ i in 𝓕, f i ∈ cumPow X (n + 1)) →
            (∀ᶠ i in 𝓕, g i ∈ cumPow X (n + 1)) → ¬ Atomic 𝓕 X f → ¬ Atomic 𝓕 X g →
            col 𝓕 hX f = col 𝓕 hX g → ∀ h : I → ZFSet.{u}, (∀ᶠ i in 𝓕, h i ∈ cumPow X n) →
            (∀ᶠ i in 𝓕, h i ∈ f i) → ∀ᶠ i in 𝓕, h i ∈ g i := by
          intro f g hf hg hAf hAg h k hk hkf
          have hE : E 𝓕 X k f := ⟨⟨n, hk⟩, ⟨n + 1, hf⟩, hkf⟩
          have hmem : col 𝓕 hX k ∈ col 𝓕 hX g := h ▸ (mem_col hX hAf).2 ⟨k, hE, rfl⟩
          obtain ⟨k', hE', heq⟩ := (mem_col hX hAg).1 hmem
          have hk' : ∀ᶠ i in 𝓕, k' i ∈ cumPow X n := by
            filter_upwards [hg, hE'.2.2, hE'.1.eventually_mem] with i h1 h2 h3
            exact mem_cumPow_of_mem hX h1 h2 h3
          filter_upwards [ih hk' hk heq, hE'.2.2] with i h1 h2
          rwa [← h1]
        by_contra hne
        have hne' : ∀ᶠ i in 𝓕, f i ≠ g i := Ultrafilter.eventually_not.2 hne
        have hfs : ∀ᶠ i in 𝓕, f i ⊆ cumPow X n := by
          filter_upwards [hf, not_atomic_iff.1 hAf] with i h1 h2
          exact subset_cumPow_of_mem_succ h1 h2
        have hgs : ∀ᶠ i in 𝓕, g i ⊆ cumPow X n := by
          filter_upwards [hg, not_atomic_iff.1 hAg] with i h1 h2
          exact subset_cumPow_of_mem_succ h1 h2
        have hex : ∀ᶠ i in 𝓕, ∃ z, z ∈ cumPow X n ∧ ¬ (z ∈ f i ↔ z ∈ g i) := by
          filter_upwards [hne', hfs, hgs] with i h1 h2 h3
          by_contra hcon
          push Not at hcon
          refine h1 (ZFSet.ext fun z => ?_)
          by_cases hz : z ∈ cumPow X n
          · exact hcon z hz
          · exact ⟨fun hzf => absurd (h2 hzf) hz, fun hzg => absurd (h3 hzg) hz⟩
        obtain ⟨k, hk⟩ := Filter.skolem.1 hex
        have hkn : ∀ᶠ i in 𝓕, k i ∈ cumPow X n := hk.mono fun i hi => hi.1
        rcases Ultrafilter.eventually_or.1
          (Eventually.of_forall fun i => em (k i ∈ f i) : ∀ᶠ i in 𝓕, k i ∈ f i ∨ k i ∉ f i)
          with c | c
        · have := key hf hg hAf hAg h k hkn c
          have hF : ∀ᶠ _ in (𝓕 : Filter I), False := by
            filter_upwards [hk, c, this] with i h1 h2 h3
            exact h1.2 ⟨fun _ => h3, fun _ => h2⟩
          exact hF.exists.elim fun _ hh => hh
        · have c' : ∀ᶠ i in 𝓕, k i ∈ g i := by
            filter_upwards [hk, c] with i h1 h2
            by_contra h3
            exact h1.2 ⟨fun h => absurd h h2, fun h => absurd h h3⟩
          have := key hg hf hAg hAf h.symm k hkn c'
          have hF : ∀ᶠ _ in (𝓕 : Filter I), False := by
            filter_upwards [c, this] with i h1 h2
            exact h1 h2
          exact hF.exists.elim fun _ hh => hh

/-- **Section 14.3, equality.** For $`f, g \in Z`,
$$`[f] = [g] \iff \{i \in I : f(i) = g(i)\} \in \mathcal F.`
The book states this without proof. -/
theorem col_eq_iff (hX : IsBaseSet X) (hf : Bdd 𝓕 X f) (hg : Bdd 𝓕 X g) :
    col 𝓕 hX f = col 𝓕 hX g ↔ f =ᶠ[𝓕] g := by
  refine ⟨fun h => ?_, col_congr hX⟩
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  exact eventuallyEq_of_col_eq_aux hX (max m n)
    (hm.mono fun i hi => cumPow_mono (le_max_left m n) hi)
    (hn.mono fun i hi => cumPow_mono (le_max_right m n) hi) h

/-- **Section 14.3, membership.** For $`f, g \in Z`,
$$`[f] \in [g] \iff \{i \in I : f(i) \in g(i)\} \in \mathcal F.`
The book states this without proof. -/
theorem col_mem_col_iff (hX : IsBaseSet X) (hf : Bdd 𝓕 X f) (hg : Bdd 𝓕 X g) :
    col 𝓕 hX f ∈ col 𝓕 hX g ↔ ∀ᶠ i in 𝓕, f i ∈ g i := by
  by_cases hA : Atomic 𝓕 X g
  · constructor
    · exact fun h => absurd h ((isIndividual_col hX hA).2 _ (col_mem hX hf))
    · intro h
      have hF : ∀ᶠ _ in (𝓕 : Filter I), False := by
        filter_upwards [h, hA, hf.eventually_mem] with i h1 h2 h3
        exact (hX _ h2).2 _ h3 h1
      exact hF.exists.elim fun _ hh => hh.elim
  · rw [mem_col hX hA]
    constructor
    · rintro ⟨k, hE, heq⟩
      filter_upwards [(col_eq_iff hX hE.1 hf).1 heq, hE.2.2] with i h1 h2
      rwa [← h1]
    · exact fun h => ⟨f, ⟨hf, hg, h⟩, rfl⟩

/-- A member of $`[g]` that belongs to $`\mathbb U(Y)` is $`[f]` for some
$`f \in Z` with $`f(i) \in g(i)` almost everywhere. So the image of the collapse is transitive
in $`\mathbb U(Y)`, which is what bounded quantifiers need. -/
theorem exists_of_mem_col (hX : IsBaseSet X) {a : ZFSet.{u}}
    (ha : a ∈ superstructure (base 𝓕 X)) (hag : a ∈ col 𝓕 hX g) :
    ∃ f, Bdd 𝓕 X f ∧ (∀ᶠ i in 𝓕, f i ∈ g i) ∧ col 𝓕 hX f = a := by
  by_cases hA : Atomic 𝓕 X g
  · exact absurd hag ((isIndividual_col hX hA).2 _ ha)
  · obtain ⟨f, hE, rfl⟩ := (mem_col hX hA).1 hag
    exact ⟨f, hE.1, hE.2.2, rfl⟩

/-- **Section 14.3.** For $`a \in X` the collapse of the constant function is
$`a`: individuals are fixed by the transfer map. -/
theorem col_const_of_mem (hX : IsBaseSet X) {x : ZFSet.{u}} (hx : x ∈ X) :
    col 𝓕 hX (fun _ => x) = x := by
  rw [col_atomic hX (Eventually.of_forall fun _ => hx), atomOf_const hx]

/-- **Section 14.3.** $`{}^*\emptyset = \emptyset`. -/
theorem col_const_empty (hX : IsBaseSet X) : col 𝓕 hX (fun _ => ∅) = ∅ := by
  have hA : ¬ Atomic 𝓕 X (fun _ : I => (∅ : ZFSet.{u})) := fun h => by
    obtain ⟨_, hi⟩ := h.exists
    exact (hX _ hi).1 rfl
  rw [eq_empty]
  intro y hy
  obtain ⟨f, hE, -⟩ := (mem_col hX hA).1 hy
  obtain ⟨_, hi⟩ := hE.2.2.exists
  exact notMem_empty _ hi

/-- **Section 14.3.** $`{}^*X = \{[f] : \{i : f(i) \in X\} \in \mathcal F\}
= Y`, so the target universe $`\mathbb U(Y)` is $`\mathbb U({}^*X)`. -/
theorem col_const_base (hX : IsBaseSet X) : col 𝓕 hX (fun _ => X) = base 𝓕 X := by
  have hA : ¬ Atomic 𝓕 X (fun _ : I => X) := fun h => by
    obtain ⟨_, hi⟩ := h.exists
    exact mem_irrefl _ hi
  ext y
  rw [mem_col hX hA]
  constructor
  · rintro ⟨f, hE, rfl⟩
    rw [col_atomic hX hE.2.2]
    exact atomOf_mem_base hE.2.2
  · intro hy
    obtain ⟨f, hf, rfl⟩ := exists_atomic_of_mem_base hy
    exact ⟨f, ⟨hf.bdd, bdd_const base_mem_superstructure, hf⟩, col_atomic hX hf⟩

end BoundedUltrapower
end Goldblatt
