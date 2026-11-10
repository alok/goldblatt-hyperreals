import Goldblatt.Ch15_Saturation.Codes

/-!
# 15 (part 2). Infinitesimal, limited and unlimited numbers in a framework

This is the second of five parts of Chapter 15 (the overview is on the chapter page
{lit}`Goldblatt.Ch15_Saturation`). Like part 1 it contains no numbered item of the book. It
defines, for a framework whose individuals include the real numbers, the notions that the
statements of Sections 15.1 to 15.4 use: the strict order of the hyperreals, infinitesimal,
limited and unlimited hyperreals, and the relation of being infinitely close. In Parts I to
III of the book these were defined inside the ultrapower of the reals; here they are defined
from the transforms of relations on the reals, and their basic properties are obtained by
transfer with the lemmas of part 1.
-/

noncomputable section

namespace Goldblatt

open ZFSet NonstandardFramework

universe u

namespace RealFramework

variable (F : RealFramework.{u}) {A B a b c n x y z : ZFSet.{u}} {r s : ℝ}

/-!
## The real numbers as a coded type
-/

/-- The real numbers of a framework are a coded type: a real number is represented by the
individual {lit}`F.real r`. -/
def cR : F.Code ℝ where
  enc := F.real
  enc_injective := F.real_injective
  star_enc := F.star_real
  isSetOf_range := F.isSetOf_R

/-- The representative of a real number. -/
@[simp]
theorem cR_enc (r : ℝ) : F.cR.enc r = F.real r := rfl

/-- The set representing all real numbers is $`\mathbb R`. -/
theorem cR_set_univ : F.cR.set Set.univ = F.R := F.cR.set_univ

/-- The set representing the natural numbers among the reals is $`\mathbb N`. -/
theorem cR_set_nat : F.cR.set (Set.range ((↑) : ℕ → ℝ)) = F.N := by
  ext u
  rw [Code.mem_set, F.mem_N]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, ⟨k, rfl⟩, rfl⟩

/-- The set of pairs of the universe representing a relation between real numbers. -/
abbrev rr (P : ℝ → ℝ → Prop) : ZFSet.{u} := Code.rel F.cR F.cR P

/-- The order relation of Chapter 13 is the set representing $`\le`. -/
theorem Le_eq : F.Le = F.rr (· ≤ ·) := by
  ext p
  rw [Le, mem_sep, rr, Code.rel, Code.mem_set]
  constructor
  · rintro ⟨-, r, s, hrs, rfl⟩
    exact ⟨(r, s), hrs, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨pair_mem_prod.2 ⟨F.mem_R.2 ⟨_, rfl⟩, F.mem_R.2 ⟨_, rfl⟩⟩, q.1, q.2, hq, rfl⟩

/-- The order relation is a binary relation of the universe. -/
theorem relIn_Le : RelIn F.U F.Le :=
  F.hU.relIn_of_subset_prod F.isSetOf_R F.isSetOf_R sep_subset

/-- A member of $`{}^*\mathbb R` in the notation of part 1. -/
theorem mem_star_R_iff : a ∈ F.star F.R ↔ a ∈ F.star (F.cR.set Set.univ) := by
  rw [F.cR_set_univ]

/-- A member of $`{}^*\mathbb N` in the notation of part 1. -/
theorem mem_star_N_iff : a ∈ F.star F.N ↔ a ∈ F.star (F.cR.set (Set.range ((↑) : ℕ → ℝ))) := by
  rw [F.cR_set_nat]

/-!
## The order of the hyperreals
-/

/-- The transformed order holds only between hyperreals. -/
theorem mem_of_le (h : pair a b ∈ F.star F.Le) : a ∈ F.star F.R ∧ b ∈ F.star F.R := by
  rw [F.Le_eq] at h
  have := Code.mem_of_pair_mem_star_rel F.cR F.cR h
  rwa [F.cR_set_univ] at this

/-- The order of the hyperreals is reflexive. -/
theorem le_refl (ha : a ∈ F.star F.R) : pair a a ∈ F.star F.Le := by
  rw [F.Le_eq]
  exact Code.rel_refl F.cR (fun r => le_rfl) (F.mem_star_R_iff.1 ha)

/-- The order of the hyperreals is transitive. -/
theorem le_trans (hab : pair a b ∈ F.star F.Le) (hbc : pair b c ∈ F.star F.Le) :
    pair a c ∈ F.star F.Le := by
  rw [F.Le_eq] at hab hbc ⊢
  exact Code.rel_comp F.cR F.cR F.cR (P := (· ≤ ·)) (Q := (· ≤ ·)) (R := (· ≤ ·))
    (fun _ _ _ h h' => _root_.le_trans h h') hab hbc

/-- The order of the hyperreals is antisymmetric. -/
theorem le_antisymm (hab : pair a b ∈ F.star F.Le) (hba : pair b a ∈ F.star F.Le) : a = b := by
  rw [F.Le_eq] at hab hba
  exact Code.eq_of_rel F.cR (P := fun r s => r ≤ s ∧ s ≤ r) (fun _ _ h => _root_.le_antisymm h.1 h.2)
    ((Code.rel_and F.cR F.cR).2 ⟨hab, (Code.rel_swap F.cR F.cR).1 hba⟩)

/-- The order of the hyperreals is total. -/
theorem le_total (ha : a ∈ F.star F.R) (hb : b ∈ F.star F.R) :
    pair a b ∈ F.star F.Le ∨ pair b a ∈ F.star F.Le := by
  rw [F.Le_eq]
  rcases Code.rel_total F.cR F.cR (P := (· ≤ ·)) (Q := fun r s => s ≤ r)
    (fun r s => _root_.le_total r s) (F.mem_star_R_iff.1 ha) (F.mem_star_R_iff.1 hb) with h | h
  · exact Or.inl h
  · exact Or.inr ((Code.rel_swap F.cR F.cR).1 h)

/-- **The strict order of the hyperreals.** $`a < b` in $`{}^*\mathbb R`: the pair belongs to
the transform of the relation $`<` on the real numbers. By {lit}`lt_iff` this is the same as
$`a \le b` and $`a \ne b`, the form used in Chapters 13 and 14. -/
def Lt (a b : ZFSet.{u}) : Prop := pair a b ∈ F.star (F.rr (· < ·))

variable {F}

/-- $`a < b` exactly when $`a \le b` and $`a \ne b`. -/
theorem lt_iff : F.Lt a b ↔ pair a b ∈ F.star F.Le ∧ a ≠ b := by
  rw [F.Le_eq]
  constructor
  · intro h
    refine ⟨Code.rel_mono F.cR F.cR (fun _ _ => le_of_lt) h, ?_⟩
    rintro rfl
    have ha := (Code.mem_of_pair_mem_star_rel F.cR F.cR h).1
    have heq := (Code.pair_mem_star_rel_eq F.cR).2 ⟨ha, rfl⟩
    exact Code.notMem_star_rel F.cR F.cR (P := fun r s => r < s ∧ r = s)
      (fun r s h => absurd h.1 (h.2 ▸ lt_irrefl r)) ((Code.rel_and F.cR F.cR).2 ⟨h, heq⟩)
  · rintro ⟨hle, hne⟩
    obtain ⟨ha, hb⟩ := Code.mem_of_pair_mem_star_rel F.cR F.cR hle
    rcases Code.rel_total F.cR F.cR (P := (· < ·)) (Q := fun r s => s ≤ r)
      (fun r s => lt_or_ge r s) ha hb with h | h
    · exact h
    · exact absurd (Code.eq_of_rel F.cR (P := fun r s => r ≤ s ∧ s ≤ r)
        (fun _ _ h => _root_.le_antisymm h.1 h.2) ((Code.rel_and F.cR F.cR).2 ⟨hle, h⟩)) hne

/-- The strict order holds only between hyperreals. -/
theorem Lt.mem (h : F.Lt a b) : a ∈ F.star F.R ∧ b ∈ F.star F.R :=
  F.mem_of_le (lt_iff.1 h).1

/-- $`a < b` implies $`a \le b`. -/
theorem Lt.le (h : F.Lt a b) : pair a b ∈ F.star F.Le := (lt_iff.1 h).1

/-- Transitivity of $`<` after $`\le`. -/
theorem lt_of_le_of_lt (hab : pair a b ∈ F.star F.Le) (hbc : F.Lt b c) : F.Lt a c := by
  rw [F.Le_eq] at hab
  exact Code.rel_comp F.cR F.cR F.cR (P := (· ≤ ·)) (Q := (· < ·)) (R := (· < ·))
    (fun _ _ _ h h' => _root_.lt_of_le_of_lt h h') hab hbc

/-- Transitivity of $`\le` after $`<`. -/
theorem lt_of_lt_of_le (hab : F.Lt a b) (hbc : pair b c ∈ F.star F.Le) : F.Lt a c := by
  rw [F.Le_eq] at hbc
  exact Code.rel_comp F.cR F.cR F.cR (P := (· < ·)) (Q := (· ≤ ·)) (R := (· < ·))
    (fun _ _ _ h h' => _root_.lt_of_lt_of_le h h') hab hbc

/-- Transitivity of $`<`. -/
theorem Lt.trans (hab : F.Lt a b) (hbc : F.Lt b c) : F.Lt a c := lt_of_lt_of_le hab hbc.le

/-- No hyperreal is less than itself. -/
theorem lt_irrefl' : ¬ F.Lt a a := fun h => (lt_iff.1 h).2 rfl

/-- Any two hyperreals satisfy $`a < b` or $`b \le a`. -/
theorem lt_or_le (ha : a ∈ F.star F.R) (hb : b ∈ F.star F.R) :
    F.Lt a b ∨ pair b a ∈ F.star F.Le := by
  rcases F.le_total ha hb with h | h
  · by_cases hab : a = b
    · subst hab
      exact Or.inr h
    · exact Or.inl (lt_iff.2 ⟨h, hab⟩)
  · exact Or.inr h

/-- $`a < b` excludes $`b \le a`. -/
theorem Lt.not_le (h : F.Lt a b) : pair b a ∉ F.star F.Le := fun h' =>
  (lt_iff.1 h).2 (F.le_antisymm h.le h')

/-- On real numbers the strict order of the hyperreals is the usual one. -/
@[simp]
theorem real_lt_real : F.Lt (F.real r) (F.real s) ↔ r < s :=
  Code.pair_enc_mem_star_rel F.cR F.cR (a := r) (b := s)

/-- A hyperreal is below a real number $`r` exactly when it belongs to the transform of the
ray below $`r`. -/
theorem lt_real_iff : F.Lt a (F.real r) ↔ a ∈ F.star (F.cR.set (Set.Iio r)) :=
  Code.pair_enc_right_mem_star_rel F.cR F.cR (b := r)

/-- A hyperreal is above a real number $`r` exactly when it belongs to the transform of the
ray above $`r`. -/
theorem real_lt_iff : F.Lt (F.real r) a ↔ a ∈ F.star (F.cR.set (Set.Ioi r)) :=
  Code.pair_enc_left_mem_star_rel F.cR F.cR (a := r)

/-- A hyperreal is at most a real number $`r` exactly when it belongs to the transform of the
closed ray below $`r`. -/
theorem le_real_iff : pair a (F.real r) ∈ F.star F.Le ↔ a ∈ F.star (F.cR.set (Set.Iic r)) := by
  rw [F.Le_eq]
  exact Code.pair_enc_right_mem_star_rel F.cR F.cR (b := r)

/-- A hyperreal is at least a real number $`r` exactly when it belongs to the transform of the
closed ray above $`r`. -/
theorem real_le_iff : pair (F.real r) a ∈ F.star F.Le ↔ a ∈ F.star (F.cR.set (Set.Ici r)) := by
  rw [F.Le_eq]
  exact Code.pair_enc_left_mem_star_rel F.cR F.cR (a := r)

/-!
## Infinitesimal, limited and unlimited hyperreals
-/

variable (F)

/-- **Infinitesimals.** A hyperreal $`b` with $`-r < b < r` for every positive real
$`r`. -/
def Infinitesimal (b : ZFSet.{u}) : Prop :=
  ∀ r : ℝ, 0 < r → F.Lt (F.real (-r)) b ∧ F.Lt b (F.real r)

/-- **Limited hyperreals.** A hyperreal $`b` with $`-r < b < r` for some real $`r`. -/
def Limited (b : ZFSet.{u}) : Prop := ∃ r : ℝ, F.Lt (F.real (-r)) b ∧ F.Lt b (F.real r)

/-- **Positive unlimited hyperreals.** A hyperreal greater than every real number. -/
def PosUnlimited (b : ZFSet.{u}) : Prop := ∀ r : ℝ, F.Lt (F.real r) b

/-- **Negative unlimited hyperreals.** A hyperreal less than every real number. -/
def NegUnlimited (b : ZFSet.{u}) : Prop := ∀ r : ℝ, F.Lt b (F.real r)

/-- **Distance below a real bound.** $`|a - b| < r` for hyperreals $`a, b` and a real number
$`r`: the pair belongs to the transform of the relation $`|x - y| < r` on the reals. -/
def Within (r : ℝ) (a b : ZFSet.{u}) : Prop := pair a b ∈ F.star (F.rr fun x y => |x - y| < r)

/-- **Infinitely close.** $`a \simeq b`: the hyperreals $`a` and $`b` are within every
positive real distance of each other. -/
def Near (a b : ZFSet.{u}) : Prop := ∀ r : ℝ, 0 < r → F.Within r a b

variable {F}

/-- $`-r < b < r` exactly when $`b` belongs to the transform of the set of reals of absolute
value below $`r`. -/
theorem lt_and_lt_iff : (F.Lt (F.real (-r)) b ∧ F.Lt b (F.real r)) ↔
    b ∈ F.star (F.cR.set {x | |x| < r}) := by
  rw [real_lt_iff, lt_real_iff, ← mem_inter, ← F.cR.star_set_inter]
  have : Set.Ioi (-r) ∩ Set.Iio r = {x : ℝ | |x| < r} := by
    ext x
    simp [abs_lt]
  rw [this]

/-- A hyperreal is infinitesimal exactly when, for every positive real $`r`, it belongs to
the transform of the set of reals of absolute value below $`r`. -/
theorem infinitesimal_iff :
    F.Infinitesimal b ↔ ∀ r : ℝ, 0 < r → b ∈ F.star (F.cR.set {x | |x| < r}) :=
  forall₂_congr fun _ _ => lt_and_lt_iff

/-- A hyperreal is limited exactly when it belongs to the transform of the set of reals of
absolute value below some real $`r`. -/
theorem limited_iff : F.Limited b ↔ ∃ r : ℝ, b ∈ F.star (F.cR.set {x | |x| < r}) :=
  exists_congr fun _ => lt_and_lt_iff

/-- The transform of a set of real numbers consists of hyperreals. -/
theorem mem_star_R_of_mem_star_set {S : Set ℝ} (h : a ∈ F.star (F.cR.set S)) :
    a ∈ F.star F.R :=
  F.mem_star_R_iff.2 (F.cR.star_set_subset_univ S h)

/-- Infinitesimals are hyperreals. -/
theorem Infinitesimal.mem (h : F.Infinitesimal b) : b ∈ F.star F.R := (h 1 one_pos).1.mem.2

/-- Limited numbers are hyperreals. -/
theorem Limited.mem (h : F.Limited b) : b ∈ F.star F.R := let ⟨_, hr⟩ := h; hr.1.mem.2

/-- Positive unlimited numbers are hyperreals. -/
theorem PosUnlimited.mem (h : F.PosUnlimited b) : b ∈ F.star F.R := (h 0).mem.2

/-- Negative unlimited numbers are hyperreals. -/
theorem NegUnlimited.mem (h : F.NegUnlimited b) : b ∈ F.star F.R := (h 0).mem.1

/-- Infinitesimals are limited. -/
theorem Infinitesimal.limited (h : F.Infinitesimal b) : F.Limited b := ⟨1, h 1 one_pos⟩

/-- Real numbers are limited. -/
theorem limited_real (r : ℝ) : F.Limited (F.real r) :=
  ⟨|r| + 1, real_lt_real.2 (by linarith [neg_abs_le r]), real_lt_real.2 (by linarith [le_abs_self r])⟩

/-- Zero is infinitesimal. -/
theorem infinitesimal_zero : F.Infinitesimal (F.real 0) := fun r hr =>
  ⟨real_lt_real.2 (by linarith), real_lt_real.2 hr⟩

/-- A real number is infinitesimal only if it is zero. -/
theorem infinitesimal_real_iff : F.Infinitesimal (F.real r) ↔ r = 0 := by
  constructor
  · intro h
    by_contra hr
    have := h |r| (abs_pos.2 hr)
    rw [real_lt_real, real_lt_real] at this
    rcases abs_cases r with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [this.1, this.2]
  · rintro rfl
    exact infinitesimal_zero

/-- A positive unlimited number is not limited. -/
theorem PosUnlimited.not_limited (h : F.PosUnlimited b) : ¬ F.Limited b := fun ⟨r, _, hr⟩ =>
  lt_irrefl' ((h r).trans hr)

/-- A negative unlimited number is not limited. -/
theorem NegUnlimited.not_limited (h : F.NegUnlimited b) : ¬ F.Limited b := fun ⟨r, hr, _⟩ =>
  lt_irrefl' (hr.trans (h (-r)))

/-- A hyperreal between two real numbers is limited. -/
theorem limited_of_le_of_le (h1 : pair (F.real r) a ∈ F.star F.Le)
    (h2 : pair a (F.real s) ∈ F.star F.Le) : F.Limited a := by
  refine ⟨|r| + |s| + 1, lt_of_lt_of_le (real_lt_real.2 ?_) h1, lt_of_le_of_lt h2 (real_lt_real.2 ?_)⟩
  · linarith [neg_abs_le r, abs_nonneg s]
  · linarith [le_abs_self s, abs_nonneg r]

/-- A hyperreal that is at least a positive unlimited number is positive unlimited. -/
theorem PosUnlimited.of_le (h : F.PosUnlimited a) (hab : pair a b ∈ F.star F.Le) :
    F.PosUnlimited b := fun r => lt_of_lt_of_le (h r) hab

/-- A hyperreal that is at most a negative unlimited number is negative unlimited. -/
theorem NegUnlimited.of_le (h : F.NegUnlimited b) (hab : pair a b ∈ F.star F.Le) :
    F.NegUnlimited a := fun r => lt_of_le_of_lt hab (h r)

/-- The description of positive unlimited numbers used in Chapter 14. -/
theorem posUnlimited_iff :
    F.PosUnlimited b ↔ ∀ r : ℝ, pair (F.real r) b ∈ F.star F.Le ∧ b ≠ F.real r :=
  forall_congr' fun _ => lt_iff.trans (and_congr_right fun _ => ne_comm)

/-!
## Infinitely close hyperreals
-/

/-- Distance below a real bound is a relation between hyperreals. -/
theorem Within.mem (h : F.Within r a b) : a ∈ F.star F.R ∧ b ∈ F.star F.R := by
  have := Code.mem_of_pair_mem_star_rel F.cR F.cR h
  rwa [F.cR_set_univ] at this

/-- Every hyperreal is within every positive real distance of itself. -/
theorem within_refl (hr : 0 < r) (ha : a ∈ F.star F.R) : F.Within r a a :=
  Code.rel_refl F.cR (fun x => by simpa using hr) (F.mem_star_R_iff.1 ha)

/-- Distance below a real bound is symmetric. -/
theorem Within.symm (h : F.Within r a b) : F.Within r b a :=
  Code.rel_mono F.cR F.cR (fun x y (hxy : |y - x| < r) => by rwa [abs_sub_comm])
    ((Code.rel_swap F.cR F.cR).1 h)

/-- The triangle inequality for distances below real bounds. -/
theorem Within.trans (h : F.Within r a b) (h' : F.Within s b c) : F.Within (r + s) a c :=
  Code.rel_comp F.cR F.cR F.cR (fun x y z (h1 : |x - y| < r) (h2 : |y - z| < s) => by
    have := abs_sub_le x y z
    show |x - z| < r + s
    linarith) h h'

/-- Distance below a real bound is monotone in the bound. -/
theorem Within.mono (h : F.Within r a b) (hrs : r ≤ s) : F.Within s a b :=
  Code.rel_mono F.cR F.cR (fun x y (hxy : |x - y| < r) => _root_.lt_of_lt_of_le hxy hrs) h

/-- Distance to a real number: $`|a - s| < r` exactly when $`a` belongs to the transform of
the set of reals within $`r` of $`s`. -/
theorem within_real_iff : F.Within r a (F.real s) ↔ a ∈ F.star (F.cR.set {x | |x - s| < r}) :=
  Code.pair_enc_right_mem_star_rel F.cR F.cR (b := s)

/-- On real numbers, distance below a real bound is the usual notion. -/
@[simp]
theorem within_real_real {x y : ℝ} : F.Within r (F.real x) (F.real y) ↔ |x - y| < r :=
  Code.pair_enc_mem_star_rel F.cR F.cR (a := x) (b := y)

/-- Infinitely close numbers are hyperreals. -/
theorem Near.mem (h : F.Near a b) : a ∈ F.star F.R ∧ b ∈ F.star F.R := (h 1 one_pos).mem

/-- Every hyperreal is infinitely close to itself. -/
theorem near_refl (ha : a ∈ F.star F.R) : F.Near a a := fun _ hr => within_refl hr ha

/-- Being infinitely close is symmetric. -/
theorem Near.symm (h : F.Near a b) : F.Near b a := fun r hr => (h r hr).symm

/-- Being infinitely close is transitive. -/
theorem Near.trans (h : F.Near a b) (h' : F.Near b c) : F.Near a c := fun r hr => by
  have := (h (r / 2) (half_pos hr)).trans (h' (r / 2) (half_pos hr))
  rwa [add_halves] at this

/-- A hyperreal is infinitesimal exactly when it is infinitely close to zero. -/
theorem near_zero_iff : F.Near b (F.real 0) ↔ F.Infinitesimal b := by
  rw [infinitesimal_iff]
  refine forall₂_congr fun r _ => ?_
  rw [within_real_iff]
  simp

/-- Two real numbers are infinitely close only if they are equal. -/
theorem near_real_real {x y : ℝ} : F.Near (F.real x) (F.real y) ↔ x = y := by
  constructor
  · intro h
    by_contra hxy
    have := h |x - y| (abs_pos.2 (sub_ne_zero.2 hxy))
    rw [within_real_real] at this
    exact lt_irrefl _ this
  · rintro rfl
    exact near_refl (F.real_mem_star x)

/-!
## Hypernatural numbers
-/

/-- Zero is the least hypernatural number. -/
theorem nat_zero_le (hn : n ∈ F.star F.N) : pair (F.nat 0) n ∈ F.star F.Le := by
  have : F.nat 0 = F.real 0 := by simp [RealFramework.nat]
  rw [this, real_le_iff]
  refine F.cR.star_set_mono (fun x hx => ?_) (F.mem_star_N_iff.1 hn)
  obtain ⟨k, rfl⟩ := hx
  exact (Nat.cast_nonneg k : (0 : ℝ) ≤ k)

/-- A hypernatural number below a standard natural number is standard. -/
theorem mem_N_of_le_nat {j : ℕ} (hn : n ∈ F.star F.N) (h : pair n (F.nat j) ∈ F.star F.Le) :
    n ∈ F.N := by
  by_contra hnN
  have h1 := F.nat_le_of_nonstandard hn hnN (j + 1)
  have := F.pair_nat_mem_star_Le.1 (F.le_trans h1 h)
  omega

/-- A hypernatural number above a nonstandard one is nonstandard. -/
theorem notMem_N_of_le (hn : n ∈ F.star F.N) (hnN : n ∉ F.N) {m : ZFSet.{u}}
    (h : pair n m ∈ F.star F.Le) : m ∉ F.N := fun hm => by
  obtain ⟨j, rfl⟩ := F.mem_N.1 hm
  exact hnN (mem_N_of_le_nat hn h)

/-- A nonstandard hypernatural number is positive unlimited. -/
theorem posUnlimited_of_nonstandard (hn : n ∈ F.star F.N) (hnN : n ∉ F.N) :
    F.PosUnlimited n := fun r => by
  obtain ⟨k, hk⟩ := exists_nat_gt r
  have h1 : F.Lt (F.real r) (F.nat k) := real_lt_real.2 hk
  exact lt_of_lt_of_le h1 (F.nat_le_of_nonstandard hn hnN k)

/-- A hypernatural number is nonstandard exactly when it is positive unlimited. -/
theorem notMem_N_iff_posUnlimited (hn : n ∈ F.star F.N) : n ∉ F.N ↔ F.PosUnlimited n :=
  ⟨posUnlimited_of_nonstandard hn, fun h hnN => by
    obtain ⟨k, rfl⟩ := F.mem_N.1 hnN
    exact lt_irrefl' (h k)⟩

/-- A standard natural number is below every nonstandard hypernatural number. -/
theorem nat_lt_of_nonstandard (hn : n ∈ F.star F.N) (hnN : n ∉ F.N) (k : ℕ) :
    F.Lt (F.nat k) n :=
  posUnlimited_of_nonstandard hn hnN k

end RealFramework

end Goldblatt
