# Coverage ledger

Every section, numbered theorem and exercise of Goldblatt's *Lectures on the Hyperreals*
that has been formalized, with its status. The rows come from the ledgers written while
each chapter was formalized and independently reviewed against the book.

Status values: `proved` (stated and proved in Lean, no `sorry`), `sorry` (faithful statement,
proof incomplete), `mathlib` (direct alias of an existing Mathlib result), `prose` (discussion
with no formal content, summarized in the chapter's text), `omitted` (with the reason).

Where one book item is covered by several declarations, the row names the main one and the
note lists the others. Statement-shape differences from the book are described in the note
and in the declaration's docstring.

Deviations from `SPEC.md` that apply to whole chapters:

* Chapter 1 is an overview; its preview definitions live in `Goldblatt.Intro` so that they do
  not collide with the real definitions of Chapter 5.
* Chapter 4 lives in `Goldblatt.Transfer`, because Chapter 13 defines a second formal
  language (for universes) with the same constructor names.
* The book's last numbered chapter is 19; what follows it is the bibliography.

## Summary

| Chapter | Items | proved | sorry | mathlib | prose | omitted |
|---|---|---|---|---|---|---|
| 1. What Are the Hyperreals? | 19 | 15 | 0 | 2 | 2 | 0 |
| 2. Large Sets | 38 | 36 | 0 | 1 | 1 | 0 |
| 3. Ultrapower Construction of the Hyperreals | 53 | 51 | 0 | 1 | 1 | 0 |
| 4. The Transfer Principle | 30 | 30 | 0 | 0 | 0 | 0 |
| 5. Hyperreals Great and Small | 61 | 61 | 0 | 0 | 0 | 0 |
| 6. Convergence of Sequences and Series | 50 | 49 | 0 | 1 | 0 | 0 |
| 7. Continuous Functions | 58 | 56 | 0 | 0 | 2 | 0 |
| 8. Differentiation | not yet formalized | | | | | |
| 9. The Riemann Integral | not yet formalized | | | | | |
| 10. Topology of the Reals | not yet formalized | | | | | |
| 11. Internal and External Sets | 67 | 66 | 0 | 0 | 1 | 0 |
| 12. Internal Functions and Hyperfinite Sets | 38 | 38 | 0 | 0 | 0 | 0 |
| 13. Universes and Frameworks | 60 | 59 | 0 | 1 | 0 | 0 |
| 14. The Existence of Nonstandard Entities | 52 | 52 | 0 | 0 | 0 | 0 |
| 15. Permanence, Comprehensiveness, Saturation | not yet formalized | | | | | |
| 16. Loeb Measure | not yet formalized | | | | | |
| 17. Ramsey Theory | 20 | 18 | 0 | 0 | 1 | 1 |
| 18. Completion by Enlargement | not yet formalized | | | | | |
| 19. Hyperfinite Approximation | not yet formalized | | | | | |
| **Total** | 546 | 531 | 0 | 6 | 8 | 1 |

## 1. What Are the Hyperreals?

| Book item | Status | Lean declaration | Note |
|---|---|---|---|
| Section 1.1 definition (infinitely small) | proved | `Goldblatt.Intro.InfinitelySmall` | Definition over any ordered field: \|x\| < 1/n for all positive n. Zero allowed; the book's infinitesimals are the nonzero ones. Non-vacuity: epsilon_infinitelySmall. Bridge to Mathlib: infinitelySmall_iff_archimedeanClassMk_pos (InfinitelySmall x ↔ 0 < ArchimedeanClass.mk x). Mathlib v4.35 has no Hyperreal.Infinitesimal, so the bridge targets ArchimedeanClass. |
| Section 1.1 definition (infinitely large) | proved | `Goldblatt.Intro.InfinitelyLarge` | Definition: n < \|w\| for all positive n. Non-vacuity: omega_infinitelyLarge. Bridge to Mathlib: infinitelyLarge_iff_archimedeanClassMk_neg (InfinitelyLarge w ↔ ArchimedeanClass.mk w < 0). |
| Section 1.1 claim (reciprocal of a nonzero infinitesimal is infinite) | proved | `Goldblatt.Intro.InfinitelySmall.infinitelyLarge_inv` |  |
| Section 1.1 claim (reciprocal of an infinite number is a nonzero infinitesimal) | proved | `Goldblatt.Intro.InfinitelyLarge.infinitelySmall_inv` |  |
| Section 1.1 claim (R has no nonzero infinitesimals) | proved | `Goldblatt.Intro.InfinitelySmall.eq_zero` | Stated for any Archimedean ordered field, which covers R. |
| Section 1.1 claim (R has no infinitely large numbers) | proved | `Goldblatt.Intro.not_infinitelyLarge` | Stated for any Archimedean ordered field. |
| Section 1.1 claim (R* contains a nonzero infinitesimal) | proved | `Goldblatt.Intro.epsilon_infinitelySmall` | Witness is Hyperreal.epsilon. Also exists_pos_infinitesimal: a positive hyperreal below every positive real. |
| Section 1.1 claim (R* contains an infinitely large number) | proved | `Goldblatt.Intro.omega_infinitelyLarge` | Witness is Hyperreal.omega. Also exists_unlimited: a hyperreal above every real. |
| Section 1.1 claim (R* is a proper ordered field extension of R) | proved | `Goldblatt.Intro.hyperreal_coe_not_surjective` | Renamed from coe_not_surjective. With hyperreal_coe_strictMono (the embedding is strictly increasing); the ordered ring hom itself is Mathlib's Hyperreal.coeRingHom. |
| Section 1.2 (Newton and Leibniz), p. 5: increment of a product | proved | `Goldblatt.Intro.leibniz_product_increment` | (x+dx)(y+dy) - xy = x dy + y dx + dx dy for hyperreals, by ring. This is the book's only displayed computation in Section 1.2. |
| Section 1.2 (Newton and Leibniz), p. 5: the omitted term dx dy is comparatively infinitely small | proved | `Goldblatt.Intro.leibniz_omitted_term_infinitelySmall` | For nonzero infinitely small dx, dy: dx*dy/dx and dx*dy/dy are both InfinitelySmall. The book's phrase is informal ('infinitely small in comparison with the rest'); the docstring says this is the reading made precise. |
| Section 1.2 Historical Background (project illustration, not in the book) | proved | `Goldblatt.Intro.sq_increment_quotient` | ((x+eps)^2 - x^2)/eps = 2x + eps, and sq_increment_quotient_sub_infinitelySmall. Now marked in the module doc and both docstrings as an addition of this project. The rest of the section is original historical prose. |
| Section 1.2 (Robinson), p. 11: the hyperreals fail Dedekind completeness | proved | `Goldblatt.Intro.hyperreal_not_dedekind_complete` | A claim of Section 1.2 (stated there without proof), not an addition; the previous ledger note was wrong. The range of the coercion R -> R* is nonempty, bounded above, and has no IsLUB. Moved under the 1.2 heading. |
| Section 1.3 answer (2): R is Dedekind complete | mathlib | `Goldblatt.Intro.real_exists_isLUB` | Direct alias of Real.exists_isLUB. |
| Section 1.3 answer (2): any two complete ordered fields are isomorphic | mathlib | `Goldblatt.Intro.completeOrderedField_iso` | Via ConditionallyCompleteLinearOrderedField.inducedOrderRingIso. Uniqueness of the isomorphism: completeOrderedField_iso_unique. |
| Section 1.3 answers (1), (3), (4): decimals, Dedekind cuts, Cauchy sequences | prose |  | Described in exposition only; Mathlib's Real is the Cauchy-sequence construction. |
| Section 1.3 Eudoxus-Archimedes principle in R, p. 13 | proved | `Goldblatt.Intro.real_eudoxus_archimedes` | For a > 0 and any real b there is a natural n with b < n*a; the book's case is b > 0, and the docstring now says so. Also real_exists_nat_gt. |
| Section 1.3 claim (the principle fails on the hyperreal line) | proved | `Goldblatt.Intro.hyperreal_not_archimedean` | Not (Archimedean R*); the docstring now has an informal statement. Also hyperreal_eudoxus_archimedes_fails (n * 1 < omega for all n). |
| Section 1.4 Historical References | prose |  | Reading list; no mathematical content. |

## 2. Large Sets

| Book item | Status | Lean declaration | Note |
|---|---|---|---|
| Section 2.1 | prose |  | Historical motivation (Cauchy); original exposition only, no formal content. |
| Section 2.2 definition (agreement set E_rs) | proved | `Goldblatt.agreementSet` | With agreementSet_self, agreementSet_comm, agreementSet_inter_subset (E_rs ∩ E_st ⊆ E_rt). |
| Section 2.2 definition (L_rs) and alternating-sequence example | proved | `Goldblatt.lessSet_alternatingOneZero` | lessSet, alternatingOneZero, alternatingZeroOne; agreement set empty (agreementSet_alternating); L_rs = evens, L_sr = odds; neither is cofinite (not_finite_compl_setOf_even / _odd); infinite_setOf_even / _odd, compl_setOf_even. |
| Section 2.2 requirement (A, B large and A ∩ B ⊆ C imply C large) | proved | `Goldblatt.IsFilter.mem_of_inter_subset` | Equivalence with the two closure axioms for an arbitrary collection: filter_axioms_iff_mem_of_inter_subset; filter characterisation: isFilter_iff_mem_of_inter_subset. |
| Section 2.2 requirement (A and its complement not both large; exactly one large) | proved | `Goldblatt.IsFilter.isUltrafilter_iff_xor` | Also IsProperFilter.not_mem_and_compl_mem and IsFilter.isUltrafilter_iff_compl_mem_iff. |
| Section 2.3 definition (filter) | proved | `Goldblatt.IsFilter` | Structure on Set (Set I): nonempty, inter_mem, superset_mem. Dictionary: IsFilter.toFilter, isFilter_sets. |
| Section 2.3 definition (proper filter) | proved | `Goldblatt.IsProperFilter` | Extends IsFilter with empty_notMem. Dictionary to Filter.NeBot: isProperFilter_sets_iff, IsFilter.toFilter_neBot_iff. |
| Section 2.3 definition (ultrafilter) | proved | `Goldblatt.IsUltrafilter` | Extends IsProperFilter with mem_or_compl_mem. Dictionary: IsUltrafilter.toUltrafilter, isUltrafilter_sets, ultrafilterEquiv ({F // IsUltrafilter F} ≃ Ultrafilter I). |
| Section 2.3 remark (B ∈ F if A1 ∩ ... ∩ An ⊆ B) | proved | `Goldblatt.IsFilter.mem_of_sInter_subset` | Finite subcollection given as a Finset; also IsFilter.sInter_mem. |
| Section 2.3 remark (∅ ∈ F iff F = P(I)) | proved | `Goldblatt.IsFilter.empty_mem_iff` | Also isFilter_univ, IsFilter.isProperFilter_iff_ne_univ. |
| Section 2.3 remark (every filter contains I; {I} is the smallest filter) | proved | `Goldblatt.IsFilter.singleton_univ_subset` | With IsFilter.univ_mem and isFilter_singleton_univ. |
| Example 2.4(1) (principal ultrafilter F^i is an ultrafilter) | proved | `Goldblatt.isUltrafilter_principalUltrafilter` | Defs principalUltrafilter, IsPrincipal; dictionary principalUltrafilter_eq_pure_sets, isPrincipal_sets_iff. |
| Example 2.4(1) second claim (finite I: every ultrafilter principal) | proved | `Goldblatt.IsUltrafilter.isPrincipal_of_finite` | Same theorem as Exercise 2.7(3); placed after Fact 2.5(5), which its proof uses. |
| Example 2.4(2) (cofinite filter; proper iff I infinite; not an ultrafilter) | proved | `Goldblatt.not_isUltrafilter_cofiniteFilter` | cofiniteFilter, isFilter_cofiniteFilter, isProperFilter_cofiniteFilter_iff, empty_notMem_cofiniteFilter_iff, cofiniteFilter_eq_cofinite_sets. Not-an-ultrafilter holds for every I (finite: improper; infinite: image of the evens under an embedding of ℕ). |
| Example 2.4(3) (filter generated by H; H = ∅ gives {I}) | proved | `Goldblatt.generatedFilter` | Defined with finite subcollections as Finsets, so the empty intersection gives {I} (generatedFilter_empty). Added this round: mem_generatedFilter_iff_of_nonempty, the book's literal description with n ≥ 1 members (nonempty Finset) for nonempty H, and the unfolding lemma mem_generatedFilter_iff. Also generatedFilter_mono, IsFilter.generatedFilter_eq, generatedFilter_eq_generate_sets (equals Filter.generate). |
| Example 2.4(3) (principal filter generated by B; F^i is the case B = {i}) | proved | `Goldblatt.generatedFilter_singleton` | principalFilter, isFilter_principalFilter, principalFilter_eq_principal_sets, principalUltrafilter_eq_principalFilter. |
| Example 2.4(4) (union of a chain of filters) | proved | `Goldblatt.isFilter_iUnion_of_chain` | Needs the family nonempty (implicit in the book). Set forms isFilter_sUnion_of_chain and isProperFilter_sUnion_of_chain are the ones used with Zorn. |
| Fact 2.5(1) | proved | `Goldblatt.filter_axioms_iff_inter_mem_iff` | Also isFilter_iff_inter_mem_iff, IsFilter.inter_mem_iff. |
| Fact 2.5(2) | proved | `Goldblatt.nonempty_iff_univ_mem_of_superset` | Consequence {I} ⊆ F is IsFilter.singleton_univ_subset. |
| Fact 2.5(3) | proved | `Goldblatt.IsUltrafilter.union_mem_iff` | Three parts: IsUltrafilter.inter_mem_iff, IsUltrafilter.union_mem_iff, IsUltrafilter.compl_mem_iff. |
| Fact 2.5(4) | proved | `Goldblatt.IsUltrafilter.existsUnique_mem_of_biUnion_mem` | Family indexed over a Finset with Set.PairwiseDisjoint; conclusion ∃! i, i ∈ s ∧ A i ∈ F. Existence half without disjointness: IsUltrafilter.exists_mem_of_biUnion_mem. |
| Fact 2.5(5) | proved | `Goldblatt.IsUltrafilter.cofiniteFilter_subset` | Steps: exists_singleton_mem_of_finite_mem, eq_principalUltrafilter_of_singleton_mem, isPrincipal_of_finite_mem. Converse not_isPrincipal_iff_cofiniteFilter_subset and not_finite_of_mem. |
| Fact 2.5(6) | proved | `Goldblatt.isUltrafilter_iff_maximal` | Proved through Exercise 2.7(5)(i) as the book directs; placed after 2.5(7),(8). Mathlib Maximal form: isUltrafilter_iff_maximal_isProperFilter. |
| Fact 2.5(7) definition (finite intersection property) | proved | `Goldblatt.HasFIP` | Quantifies over nonempty Finsets of members, as in the book. Helpers not_hasFIP_iff, HasFIP.mono. |
| Fact 2.5(7) (F^H proper iff H has fip) | proved | `Goldblatt.isProperFilter_generatedFilter_iff` | Requires [Nonempty I] (false on an empty index set). Also empty_notMem_generatedFilter_iff, IsProperFilter.hasFIP, hasFIP_iff_exists_isProperFilter. |
| Fact 2.5(8) | proved | `Goldblatt.HasFIP.insert_or_insert_compl` | Requires [Nonempty I] (the empty collection on an empty index set is a counterexample). The two private helper docstrings are now re-wrapped at 100 columns. |
| Section 2.6 (Zorn's lemma) | mathlib | `Goldblatt.zorn_lemma` | Mathlib's zorn_le restated in the book's wording; the book's AC sketch is prose. |
| Theorem 2.6.1 | proved | `Goldblatt.HasFIP.exists_isUltrafilter_superset` | Book's Zorn proof via IsProperFilter.exists_isUltrafilter_superset. Requires [Nonempty I]. Docstring reworded this round to original exposition (it previously matched the book's sentence). Converse hasFIP_iff_exists_isUltrafilter. |
| Corollary 2.6.2 | proved | `Goldblatt.exists_isUltrafilter_not_isPrincipal` | Also hasFIP_cofiniteFilter, the iff with Infinite I (exists_isUltrafilter_not_isPrincipal_iff), and the Mathlib form exists_ultrafilter_ne_pure. |
| Section 2.6 closing remark (number of nonprincipal ultrafilters is \|P(P(I))\|) | proved | `Goldblatt.mk_isUltrafilter_not_isPrincipal` | #{F : Set (Set I) // IsUltrafilter F ∧ ¬ IsPrincipal F} = #(Set (Set I)); bijection form nonempty_equiv_isUltrafilter_not_isPrincipal. Stated without proof in the book; transported along ultrafilterEquiv from mk_nonprincipal_ultrafilter, which rests on Mathlib's Cardinal.mk_ultrafilter_of_infinite. |
| Exercise 2.7(1) | proved | `Goldblatt.exists_isUltrafilter_mem` | Uses the principal ultrafilter at a point of A; converse exists_isUltrafilter_mem_iff. |
| Exercise 2.7(2) | proved | `Goldblatt.exists_isUltrafilter_not_isPrincipal_even` | Also _odd; general form exists_isUltrafilter_not_isPrincipal_mem (every infinite set lies in a nonprincipal ultrafilter) with its converse; exists_isUltrafilter_even_ne_odd shows the two ultrafilters differ. |
| Exercise 2.7(3) | proved | `Goldblatt.IsUltrafilter.isPrincipal_of_finite` | Same theorem as Example 2.4(1) second claim. |
| Exercise 2.7(4)(i) | proved | `Goldblatt.isFilter_generatedFilter` | With subset_generatedFilter (H ⊆ F^H). Located in the 2.4 section. |
| Exercise 2.7(4)(ii) | proved | `Goldblatt.generatedFilter_subset` | Located in the 2.4 section. |
| Exercise 2.7(5)(i) | proved | `Goldblatt.IsProperFilter.hasFIP_insert_compl_iff` | HasFIP (insert Aᶜ F) ↔ A ∉ F. Located in the 2.5 section. |
| Exercise 2.7(5)(ii) | proved | `Goldblatt.isUltrafilter_iff_maximal` | Same theorem as Fact 2.5(6), deduced from (i). |
| Project convention: index ultrafilter (not a book item) | proved | `Goldblatt.isUltrafilter_hyperfilter` | Named properties of Filter.hyperfilter for any infinite index type, with ℕ-specific forms; listed in apiNotes. |

## 3. Ultrapower Construction of the Hyperreals

| Book item | Status | Lean declaration | Note |
|---|---|---|---|
| Section 3.1 (ring of real sequences) | mathlib | `Goldblatt.seq_add_apply` | CommRing (ℕ → ℝ) is Mathlib's Pi instance; termwise lemmas seq_add_apply, seq_mul_apply, seq_neg_apply, seq_zero_apply, seq_one_apply. |
| Section 3.1 (not a field, zero divisors) | proved | `Goldblatt.not_isField_seq` | Also alternating_mul_eq_zero, exists_seq_zero_divisors, isUnit_seq_iff, not_isUnit_seq_of_zero_term; reuses Ch2 alternatingOneZero / alternatingZeroOne. |
| Section 3.2 definition (equivalence modulo the ultrafilter) | proved | `Goldblatt.SeqEquiv` | Notation r ≡ᵤ s; defined via Ch2 agreementSet; seqEquiv_iff_eventually, seqEquiv_iff_eventuallyEq. |
| Exercise 3.3(1) | proved | `Goldblatt.seqEquiv_equivalence` | SeqEquiv.refl / symm / trans. |
| Exercise 3.3(2) | proved | `Goldblatt.seqEquiv_congruence` | SeqEquiv.add, SeqEquiv.mul, SeqEquiv.neg. |
| Exercise 3.3(3) | proved | `Goldblatt.not_seqEquiv_one_div_zero` | Sequence written n ↦ 1/(n+1) because Lean indexes from 0. |
| Section 3.4 definition (statement values) | proved | `Goldblatt.leSet` | agreementSet and lessSet come from Ch2; adds leSet, leSet_eq_union, setOf_gt_eq_lessSet. memSet and relSet are in 3.9 / 3.14. |
| Exercise 3.5(1) | proved | `Goldblatt.agreementSet_inter_agreementSet_subset` |  |
| Exercise 3.5(2) | proved | `Goldblatt.agreementSet_inter_subset_add_mul` |  |
| Exercise 3.5(3) | proved | `Goldblatt.agreementSet_inter_lessSet_subset` |  |
| Exercise 3.5(4) | proved | `Goldblatt.lessSet_mem_hyperfilter_congr` |  |
| Section 3.5 (Boolean laws under an ultrafilter; not numbered in the book) | proved | `Goldblatt.almostAll_not` | almostAll_and / or / not / imp / iff / const / forall_finite / exists_finite, plus witness choice exists_seq_of_almostAll_exists, almostAll_exists_iff, almostAll_forall_iff. |
| Section 3.6 definition (the ultrapower *ℝ) | proved | `Goldblatt.ultrapowerEquiv` | ℝ* is Mathlib's Hyperreal; ultrapowerEquiv : Quotient seqSetoid ≃ ℝ* identifies the book's quotient with it. General types: Ultrapower α, class StarType (instances instStarTypeReal, instStarTypeUltrapower), Ultrapower.ofSeq, Ultrapower.of. This round: docstring of Ultrapower.equiv_ofSeq rewrapped at 100 columns. |
| Section 3.6 definitions of +, ·, < on classes | proved | `Goldblatt.ofSeq_add` | ofSeq_add, ofSeq_mul, ofSeq_neg, ofSeq_sub, ofSeq_zero, ofSeq_one (all rfl), ofSeq_lt_ofSeq_iff_lessSet. |
| Section 3.6 almost-all criterion (=, <, +, ·) | proved | `Goldblatt.ofSeq_eq_ofSeq_iff` | ofSeq_eq_ofSeq_iff, ofSeq_ne_ofSeq_iff, ofSeq_lt_ofSeq_iff, ofSeq_le_ofSeq_iff, ofSeq_add_eq_ofSeq, ofSeq_mul_eq_ofSeq. |
| Theorem 3.6.1 | proved | `Goldblatt.hyperreal_ordered_field` | Field / LinearOrder are Mathlib instances. Book's a.e. arguments proved separately: ofSeq_mul_ofSeq_invSeq, inv_ofSeq, trichotomy_statement_values, hyperreal_trichotomy, and the exercise left in the proof, ofSeq_add_pos / ofSeq_mul_pos. |
| Section 3.7 (inclusion of ℝ: *(r+s), *(r·s), <, =) | proved | `Goldblatt.coe_eq_ofSeq_const` | ofReal_add, ofReal_mul (aliases of Mathlib), ofReal_lt_ofReal and ofReal_inj proved via the almost-all criterion. |
| Theorem 3.7.1 | proved | `Goldblatt.coe_orderEmbedding` | Stated for Mathlib's Hyperreal.coeRingHom: injective and strictly monotone. Also realSubfieldEquiv : ℝ ≃+* fieldRange. |
| Section 3.8 (ε positive infinitesimal) | proved | `Goldblatt.epsilon_pos_infinitesimal` | zero_lt_epsilon, epsilon_lt_coe by the book's cofinite-set argument. Book's own sequence: ofSeq_one_div_pos_infinitesimal. Serves as the non-vacuity witness for a nonzero infinitesimal. |
| Section 3.8 (ω unlimited, ε·ω = 1, ω ∉ ℝ) | proved | `Goldblatt.real_lt_omega` | epsilon_mul_omega_eq_one, omega_eq_inv_epsilon, epsilon_eq_inv_omega, omega_ne_coe, omega_notMem_range_coe, coe_not_surjective. |
| Section 3.8 (null sequences infinitesimal, divergent sequences unlimited) | proved | `Goldblatt.abs_ofSeq_lt_of_tendsto_zero` | Also coe_lt_ofSeq_of_tendsto_atTop, abs_ofSeq. |
| Section 3.8 (principal ultrafilter exercise) | proved | `Goldblatt.constOrderRingIsoOfPrincipal` | Ordered-ring isomorphism ℝ ≃+*o Germ (pure j) ℝ built on const_bijective_of_principal (with constOrderRingIsoOfPrincipal_apply). Converse for any nonprincipal ultrafilter on ℕ: const_not_surjective_of_nonprincipal. |
| Exercise 3.8.1 | proved | `Goldblatt.lt_inv_of_pos_infinitesimal` | Stated for any ordered field K with a strictly monotone ring hom ℝ →+* K, ordered-field reasoning only. Hyperreal instance: coe_lt_inv_epsilon. |
| Section 3.9 definition (enlargement *A) | proved | `Goldblatt.starSet` | Notation ⋆A, general over StarType: result is Set ℝ* for α = ℝ and Set (Ultrapower α) otherwise. memSet and well-definedness: agreementSet_inter_memSet_subset, memSet_mem_hyperfilter_of_seqEquiv. Criteria: ofSeq_mem_starSet, hyperreal_ofSeq_mem_starSet, of_mem_starSet, coe_mem_starSet, image_of_subset_starSet. This round: docstring of the ⋆ syntax rewrapped at 100 columns. |
| Section 3.9 (ω ∈ *ℕ, nonstandard natural) | proved | `Goldblatt.omega_nonstandard_nat` | hyperNat / hyperInt / hyperRat (notation ℕ*, ℤ*, ℚ*) with mem_hyperNat_iff etc., natCast_mem_hyperNat, hyperNat_subset_hyperInt, hyperInt_subset_hyperRat. |
| Theorem 3.9.1 | proved | `Goldblatt.exists_nonstandard_mem_starSet` | Book's proof (sequence of distinct elements), for any type. Real form: exists_nonstandard_mem_starSet_real. With converse: infinite_iff_exists_nonstandard_mem. |
| Exercise 3.10(1) | proved | `Goldblatt.starSet_of_finite` | Also finite_iff_starSet_eq_image, starSet_singleton, mem_range_of_of_mem_starSet_of_finite, and real forms starSet_of_finite_real, starSet_singleton_real. |
| Exercise 3.10(2) | proved | `Goldblatt.starSet_subset_starSet` | Also starSet_mono, starSet_inj. |
| Exercise 3.10(3) | proved | `Goldblatt.starSet_union` | starSet_union, starSet_inter, starSet_diff, starSet_empty, plus starSet_compl, starSet_univ. |
| Exercise 3.10(4) | proved | `Goldblatt.starSet_iUnion_ne_iUnion_starSet` | Answer is no: counterexample with the singletons {n} and ω. Positive parts: iUnion_starSet_subset, starSet_iUnion_of_finite, starSet_iInter_of_finite, starSet_iInter_subset. |
| Exercise 3.10(5) | proved | `Goldblatt.starSet_inter_range_coe` | General forms preimage_of_starSet, starSet_inter_range_of. |
| Exercise 3.10(6) | proved | `Goldblatt.starSet_Icc_real` | All eight interval shapes, for any preorder (starSet_Icc … starSet_Iio on Ultrapower α) and for ℝ (the _real versions). |
| Exercise 3.10(7) | proved | `Goldblatt.hyperIntSubring` | Subring ℝ* with carrier ℤ*. General closure lemmas add/mul/neg/inv_mem_starSet; add_mem_hyperNat, mul_mem_hyperNat; hyperRatSubfield as a companion. |
| Exercise 3.10(8) | proved | `Goldblatt.starSet_pos_real` |  |
| Section 3.11 definition (extension *f) | proved | `Goldblatt.starMap` | Notation ⋆f. starMap_ofSeq, starMap_hyperreal_ofSeq, criterion starMap_ofSeq_eq_ofSeq; well-definedness agreementSet_subset_agreementSet_comp, SeqEquiv.comp_left. Extras: starSet_image, starSet_range, starSet_preimage, starMap_mem_starSet. |
| Exercise 3.12(1) | proved | `Goldblatt.starMap_of` | Real form starMap_coe. |
| Exercise 3.12(2) | proved | `Goldblatt.starMap_injective` | Surjectivity question answered yes: starMap_surjective. Both as iffs (starMap_injective_iff, starMap_surjective_iff). Also starMap_comp, starMap_starMap, starMap_id. |
| Exercise 3.12(3) | proved | `Goldblatt.starMap_abs` | hyperreal_abs_cases proves Mathlib's \|x\| on ℝ* equals the book's definition by cases; starMap_abs gives \|[r]\| = [\|r_n\|]. Also abs_ofSeq and ofReal_abs. |
| Exercise 3.12(4) | proved | `Goldblatt.starMap_indicator` | Characteristic function as Set.indicator of the constant 1, real-valued. |
| Exercise 3.12(5) | proved | `Goldblatt.starMapN` | Binary: starMap₂ with starMap₂_ofSeq / _of / _ofSeq_eq_ofSeq / _add / _mul / _max. Finite arity: Ultrapower.tuple, tuple_ofSeq, tupleEquiv, starMapN_ofSeq, starMapN_of. Review fix this round: Ultrapower.tuple and starMapN now take [Finite ι] in the definition, so they cannot be used at an infinite index type where the value would depend on chosen representatives. |
| Section 3.13 definition (extension of partial functions, dom *f = *(dom f)) | proved | `Goldblatt.starMapOn` | f : A → β extends to ⋆A → βS via starSetEquiv : Ultrapower A ≃ ⋆A. Book's formula with a default value is the theorem starMapOn_ofSeq; criterion starMapOn_ofSeq_eq_ofSeq; starMapOn_of (extends f); starMapOn_eq_starMap. |
| Section 3.13 (hypersequences) | proved | `Goldblatt.hyperSeq` | hyperSeq s : ℝ* → βS is a total function (junk off ℕ*). hyperSeq_ofSeq_natCast, hyperSeq_natCast, hyperSeq_omega, starMapOn_range_natCast_eq_hyperSeq, range_starMap_natCast, starMap_natCast_injective, hyperSeq_starMap_natCast. |
| Section 3.14 definition (enlargement *P of a k-ary relation) | proved | `Goldblatt.starRel` | k-ary relations are sets of tuples ι → α. Review fix this round: starRel now takes [Finite ι] in the definition (documented in its docstring). relSet and well-definedness: iInter_agreementSet_inter_relSet_subset, relSet_mem_hyperfilter_of_seqEquiv. Criteria starRel_ofSeq, starRel_ofSeq_iff_relSet. Binary: starRel₂ with starRel₂_ofSeq. Helpers Ultrapower.snoc_ofSeq, Ultrapower.snoc_apply_apply. |
| Section 3.14 (*P extends P) | proved | `Goldblatt.starRel_of` | Binary form starRel₂_of. |
| Section 3.14 (sets as unary relations; =, <, ≤ are their own enlargements) | proved | `Goldblatt.starRel_unary` | starRel_binary, starRel₂_eq, starRel₂_lt, starRel₂_le, not_starRel₂. |
| Section 3.14 (*(Graph f) = Graph(*f), including partial f) | proved | `Goldblatt.starRel_graph` | starRel_graph is the homogeneous m-ary statement for total f. New this round: starRel_graph_partial, the same for a partial m-ary f with domain A (Fin.snoc x y in the enlarged (m+1)-ary graph iff x ∈ starRel A and starMapOnN A f x = y). Unary: starRel₂_graph; unary partial: starRel₂_graph_partial; starRel₂_graph_starMapN is the tuple-packed form (now with [Finite ι]). |
| Section 3.14 (single-quantifier transfer helpers; not in the book) | proved | `Goldblatt.exists_starRel₂_ofSeq` | forall_starRel₂_ofSeq and bounded forms exists_mem_starSet_starRel₂_ofSeq, forall_mem_starSet_starRel₂_ofSeq. Added for Chapter 4. |
| Exercise 3.15(1) | proved | `Goldblatt.starRel_pi` | Binary form starRel₂_prod. *(ℝ^k) = (*ℝ)^k as starRel_univ (now with [Finite ι]); underlying identification Ultrapower.tupleEquiv. |
| Exercise 3.15(2) | proved | `Goldblatt.starSet_dom` | Companion for the range: starSet_ran. |
| Exercise 3.15(3), first sentence (k-ary relations: *(dom P) = dom *P) | proved | `Goldblatt.starRel_dom_snoc` | Homogeneous (k+1)-ary form. starRel_dom is the tuple-packed variant (now with [Finite ι]). |
| Exercise 3.15(3), second sentence (partial m-ary f: dom *f = *(dom f)) | proved | `Goldblatt.starRel_dom_partial_snoc` | New this round, addressing the review finding: homogeneous statement with the graph as an (m+1)-ary relation enlarged as in Section 3.14. Also new: the m-ary partial extension starMapOnN (defined on tuples in starRel A) with starMapOnN_ofSeq_eq_ofSeq and starMapOnN_of. Unary: starSet_dom_partial. starRel_dom_partial is kept and relabelled as the tuple-packed form. |
| Section 3.16 (cardinality of *ℝ is the continuum) | proved | `Goldblatt.mk_hyperreal` | Also nonempty_equiv_hyperreal_real (a bijection ℝ* ≃ ℝ exists). |
| Section 3.16 (uniqueness of *ℝ up to isomorphism under CH; dependence on the ultrafilter without CH) | prose |  | Discussed in the section's module doc only; the isomorphism theorem needs a back-and-forth argument for saturated models and is not formalized. No Lean statement claims it. |

## 4. The Transfer Principle

| Book item | Status | Lean declaration | Note |
|---|---|---|---|
| Section 4.1 example 1 (Eudoxus-Archimedes) | proved | `Goldblatt.Transfer.exists_hyperNat_gt` | Bounded-quantifier sentence archimedeanSentence with reading lemmas isTrue_archimedeanSentence and isTrue_star_archimedeanSentence; proved by transfer. The book's first formulation archimedeanSentence' (range shown by a conjunct) is now complete: isTrue_archimedeanSentence' (reading over R), archimedeanSentence'_isTrue (truth), isTrue_star_archimedeanSentence' (reading of the transform), exists_hyperNat_gt' (by transfer). Mixed sentence with unstarred N: not_isTrue_mixedArchimedeanSentence, not_over_mixedArchimedeanSentence. |
| Section 4.1 example 2 (density of the rationals) | proved | `Goldblatt.Transfer.exists_hyperRat_btwn` | densitySentence, isTrue_densitySentence, isTrue_star_densitySentence; by transfer. |
| Section 4.1 example 3 (finiteness) | proved | `Goldblatt.Transfer.starSet_of_finite_by_transfer` | finiteSentence built from Formula.anyEq; generic type; the inclusion of *A in A is by transfer, the reverse by Ch03 image_of_subset_starSet; the empty set is handled by starSet_empty_by_transfer. |
| Section 4.1 example 4 (finitary set operations) | proved | `Goldblatt.Transfer.starSet_union_by_transfer` | Also starSet_inter_by_transfer, starSet_diff_by_transfer; generic type; by transfer. |
| Section 4.1 example 5 (discreteness of N) | proved | `Goldblatt.Transfer.hyperNat_eq_or_eq_add_one` | By transfer of discreteSentence n. Least element given twice: hyperNat_nonneg (x >= 0 for the project's hypernaturals, the enlargement of Lean's N) and the book-literal one_le_of_mem_starSet_posNat (x >= 1 on the enlargement of posNat = {1,2,...}), linked by starSet_posNat_by_transfer. Also natCast_lt_of_mem_hyperNat_of_nonstandard. |
| Section 4.1 example 6 (unbounded sets of reals) | proved | `Goldblatt.Transfer.exists_gt_of_exists_unlimited_mem_starSet` | Transfer from the hyperreals back to the reals via exceedsSentence; exists_nat_gt_by_transfer derives Archimedes from omega. 'Unlimited' is stated inline as greater than every real, since Ch05 is not importable. |
| Exercise 4.1.1 | proved | `Goldblatt.Transfer.exists_hyperNat_gt` | Truth of the transforms in examples 1-5: exists_hyperNat_gt and exists_hyperNat_gt' (both formulations of example 1), exists_hyperRat_btwn, starSet_of_finite_by_transfer, starSet_union_by_transfer, hyperNat_eq_or_eq_add_one, hyperNat_nonneg and one_le_of_mem_starSet_posNat. No single theorem carries the exercise. |
| Section 4.2 definition (relational structure, full structure, *R) | proved | `Goldblatt.Transfer.RelStructure` | RelStructure, RelStructure.full, RelStructure.star, unaryRel, mem_star_rel, mem_star_fun, starRel_unaryRel, unaryRel_mem_star_iff, star_ne_full_real. The book's nonemptiness requirement on the universe is not imposed. |
| Exercise 4.2.1 | proved | `Goldblatt.Transfer.unaryRel_image_of_notMem_star` | Generic type. Also image_of_ne_starSet, image_coe_ne_starSet_real, number_systems_ne_starSet (N, Z, Q, R are not enlargements). |
| Section 4.3 definition (terms, what a term names, closed/undefined terms) | proved | `Goldblatt.Transfer.Term` | Term.Names (relational), Term.Closed, Term.Denotes, Term.Defined, Names.unique, defined_iff_denotes, names_congr, closed_iff. Partial function symbols are a domain plus a function on it. |
| Section 4.3 definition (atomic formulae, formulae, bounded quantifiers, defined formulae) | proved | `Goldblatt.Transfer.Formula` | Formula, Formula.Defined, Term.Over, Formula.Over (language of a structure), over_full, Term.Over.subst / Formula.Over.subst. Notation helpers mem, rel₂, eq, lt, le, app₁, app₂, papp₁ and scoped notation in Goldblatt.Lang. |
| Section 4.3 definition (sentences, free and bound occurrences) | proved | `Goldblatt.Transfer.Formula.IsSentence` | freeVars, IsSentence, IsDefined, IsTrue, holds_congr, defined_congr, IsSentence.holds_iff. Book example in two readings: freeBoundExample (Lean's N) and the book-literal freeBoundExample' over posNat with holds_freeBoundExample'_zero and not_holds_freeBoundExample'_two. |
| Section 4.3 definition (truth and quantification) | proved | `Goldblatt.Transfer.Formula.Holds` | Book's truth rules including the skipping of undefined instances. Formula.subst with holds_subst, defined_subst; isTrue_all_iff and isTrue_ex_iff restate the quantifier rules with substituted constants. tan example: tanOddSentence, isTrue_tanOddSentence, not_isDefined_tanOddFormula_subst, starTan_neg (by transfer). |
| Section 4.4 definition (star-transform) | proved | `Goldblatt.Transfer.Formula.star` | Term.star, Formula.star, freeVars_star, IsSentence.star, star_over, star_subst. 'Dropping the stars': holds_star_mem, holds_star_rel₂, holds_star_eq, holds_star_lt, holds_star_le, names_star_app₁/app₂/papp₁. |
| Section 4.4 displayed examples of transforms | proved | `Goldblatt.Transfer.holds_star_pi_lt_app` | *(pi < f(x+1)) is pi < *f(x+1) (holds_star_pi_lt_app) and *(sin e^x in Q) is sin e^x in *Q (holds_star_sin_exp_mem_rat), computed from the formal definition under an arbitrary valuation. |
| Exercise 4.4.1 | proved | `Goldblatt.Transfer.isTrue_star_densitySentence` | Each example of 4.1 is a formal sentence; the isTrue_star_* lemmas show the formal transform is the informal one (archimedean in both formulations, density, finite, union, exceeds, addComm, trichotomy, inverse, bounded, lub). Examples whose transform is unfolded inline by simp (inter, diff, discrete, interval, sin, cosh/sinh, log, posNat, positive, closure sentences) have no separate reading lemma. |
| Section 4.5 Transfer Principle | proved | `Goldblatt.Transfer.Formula.transfer` | phi.star.IsTrue iff phi.IsTrue for every formula over any type with a StarType; no definedness or sentence hypothesis needed. Companions: transfer_defined, holds_star_of and defined_star_of (standard parameters), isTrue_star_subst_of. |
| Section 4.5 Universal Transfer | proved | `Goldblatt.Transfer.Formula.universal_transfer` | Stated with substituted constants and the book's definedness proviso. |
| Section 4.5 Existential Transfer | proved | `Goldblatt.Transfer.Formula.existential_transfer` | Dual form. Book's bounded-sequence application bounded_of_hyperSeq_limited follows the book's argument step by step: isTrue_omegaBoundSentence, then isTrue_star_boundedSentence_of_omegaBoundSentence (docstring reworded, no quotation from the book), then transfer down. Reading lemma isTrue_star_boundedBody_subst. |
| Section 4.5 examples (ordered field axioms) | proved | `Goldblatt.Transfer.hyperreal_exists_inverse_by_transfer` | Also hyperreal_add_comm_by_transfer, hyperreal_mul_one_by_transfer, hyperreal_trichotomy_by_transfer; each by transfer of an explicit sentence. |
| Section 4.5 example (enlargement of [a,b]) | proved | `Goldblatt.Transfer.starSet_Icc_by_transfer` | By transfer of intervalSentence. |
| Section 4.5 examples (sin, cosh/sinh, log) | proved | `Goldblatt.Transfer.starMap_sin_pi_sub` | Also starMap_cosh_add_sinh, starMap_log_mul (for positive hyperreals); by transfer. |
| Exercise 4.5.1 | proved | `Goldblatt.Transfer.hyperInt_closed_by_transfer` | Discussion question, answered part by part on the page. 3.10(1) starSet_of_finite_by_transfer; (2) starSet_subset_starSet_by_transfer and starSet_eq_starSet_by_transfer; (3) union/inter/diff and starSet_empty_by_transfer; (5) of_mem_starSet_by_transfer; (6) starSet_Icc_by_transfer; (7) hyperInt_closed_by_transfer from starMap₂_mem_starSet_by_transfer and starMap_mem_starSet_by_transfer, plus add_mem_starSet_by_transfer; (8) starSet_Ioi_zero_by_transfer. 3.10(4) is not a sentence and is false (Ch03 starSet_iUnion_ne_iUnion_starSet). |
| Section 4.6 Łoś's theorem | proved | `Goldblatt.Transfer.Formula.los` | Full proof by induction, for definedness and truth together, over assignments of sequences to variables (SeqValuation). Halves holds_star_germ, defined_star_germ; book notation holds_star_germ_iff_mem; one-variable substitution form isTrue_star_subst_ofSeq. Term level: Term.names_star_germ, denotes_star_germ, defined_star_germ. |
| Section 4.6 special cases (=, <, membership, *P) | proved | `Goldblatt.Transfer.Formula.starRel_ofSeq_by_los` | Also ofSeq_eq_ofSeq_by_los, ofSeq_mem_starSet_by_los, ofSeq_lt_ofSeq_by_los, each derived from Łoś. These are round trips, since the atomic case of Łoś uses Ch03's starRel_ofSeq. |
| Section 4.6 example (substitution notation phi(x1,x2)) | proved | `Goldblatt.Transfer.isTrue_star_sumSquaresFormula_subst_ofSeq` | sumSquaresFormula and isTrue_sumSquaresFormula_subst now sit under a new '## 4.6 Justifying Transfer: examples' heading in Applications.lean (moved out of the 4.3 heading). New: Łoś applied to the example (isTrue_star_sumSquaresFormula_subst_ofSeq, via isTrue_star_subst_ofSeq), the hyperreal reading isTrue_star_sumSquaresFormula_subst, and the combined exists_hyperRat_gt_sumSquares_iff. The docstring says honestly that both sides of the last equivalence are always true; the point is that it is an instance of Łoś. |
| Section 4.7 (enlargement of any structure) | proved | `Goldblatt.Transfer.transfer_complex` | The whole development is generic in the type; this is the instance for the complex numbers. |
| Section 4.7 (sentences with nonstandard constants) | proved | `Goldblatt.Transfer.omegaBoundSentence_ne_star` | omegaBoundSentence s := (boundedBody s).star.subst 0 ω. Proved: it is a defined sentence saying (forall n in *N)(\|*s(n)\| < omega) (isTrue_omegaBoundSentence, omegaBoundSentence_isSentence); it lies in the language of *R (omegaBoundSentence_over); it is not a star-transform of any formula (omegaBoundSentence_ne_star, via Formula.consts_star_subset); it implies the transform of the existential sentence. Łoś still applies to such sentences (isTrue_star_subst_ofSeq). |
| Section 4.7 (Dedekind completeness not expressible) | proved | `Goldblatt.Transfer.no_formula_expresses_dedekind` | New theorem: there is no formula phi of the language of R such that phi.IsTrue is equivalent to Dedekind completeness of R and phi.star.IsTrue is equivalent to Dedekind completeness of R*; proved from Formula.transfer, Real.exists_isLUB and not_dedekindComplete_hyperreal. This is the provable form of the book's remark; the purely syntactic claim that the set-quantified statement is not a sentence remains prose. Per-set completeness transfers: lubSentence, isTrue_lubSentence, isTrue_star_lubSentence, exists_isLUB_starSet; ne_starSet_of_not_exists_isLUB. |
| Section 4.7 (summary: ordered field with unlimited N and transfer) | proved | `Goldblatt.Transfer.exists_unlimited_hyperNat` | A nonstandard hypernatural exceeding every real, with positive infinitesimal reciprocal (witness omega). |

## 5. Hyperreals Great and Small

| Book item | Status | Lean declaration | Note |
|---|---|---|---|
| Chapter 5 opening remark (hyperrationals are quotients of hyperintegers) | proved | `Goldblatt.mem_hyperRat_iff_exists_div` | x in Q* iff x = m/n with m, n hyperintegers, n != 0 |
| Section 5.1 definition: limited | proved | `Goldblatt.Limited` | working forms limited_iff_abs_lt, limited_iff_exists_nat; Mathlib bridge limited_iff_mk_nonneg |
| Section 5.1 definition: positive/negative unlimited, unlimited | proved | `Goldblatt.Unlimited` | also PosUnlimited, NegUnlimited; unlimited_iff_abs_gt, unlimited_iff_forall_nat, not_limited_iff_unlimited, posUnlimited_iff, negUnlimited_iff, unlimited_iff_mk_neg |
| Section 5.1 definition: positive/negative infinitesimal, infinitesimal | proved | `Goldblatt.Infinitesimal` | also PosInfinitesimal, NegInfinitesimal; infinitesimal_iff_abs_lt, infinitesimal_iff_forall_nat, infinitesimal_iff_mk_pos |
| Section 5.1 definition: appreciable | proved | `Goldblatt.Appreciable` | appreciable_iff_abs, appreciable_iff_exists_nat, appreciable_iff_mk_eq_zero, appreciable_iff_not_infinitesimal_and_not_unlimited (docstring reworded this pass; module doc no longer says 'word for word') |
| Section 5.1: reals and infinitesimals are limited; only infinitesimal real is 0; other reals appreciable | proved | `Goldblatt.infinitesimal_coe_iff` | with limited_coe, Infinitesimal.limited, appreciable_coe, appreciable_coe_iff, infinitesimal_or_appreciable_or_unlimited |
| Section 5.1: natural-number reformulations (four bullets) | proved | `Goldblatt.limited_iff_exists_nat` | plus unlimited_iff_forall_nat, infinitesimal_iff_forall_nat, appreciable_iff_exists_nat |
| Section 5.1 notation: L, I, X_inf, X+, X-, *N_inf | proved | `Goldblatt.limitedSet` | limitedSet, infinitesimalSet, unlimitedPart, positivePart, negativePart, unlimitedHyperNat |
| Section 5.1 non-vacuity | proved | `Goldblatt.exists_infinitesimal_ne_zero` | infinitesimal_epsilon, unlimited_omega, posUnlimited_omega, appreciable_one |
| Section 5.2 table: sums | proved | `Goldblatt.Infinitesimal.add` | Appreciable.add_infinitesimal, Appreciable.add_limited, exists_appreciable_add_infinitesimal, Unlimited.add_infinitesimal, Unlimited.add_appreciable, Unlimited.add_limited, Limited.add |
| Section 5.2 table: opposites | proved | `Goldblatt.Infinitesimal.neg` | Appreciable.neg, Unlimited.neg, plus simp iff lemmas |
| Section 5.2 table: products | proved | `Goldblatt.Infinitesimal.mul` | Infinitesimal.mul_appreciable, mul_limited, Appreciable.mul, Appreciable.mul_unlimited, Unlimited.mul, Limited.mul |
| Section 5.2 table: reciprocals | proved | `Goldblatt.Infinitesimal.inv_unlimited` | Appreciable.inv, Unlimited.inv_infinitesimal, unlimited_iff_inv_infinitesimal |
| Section 5.2 table: quotients | proved | `Goldblatt.Infinitesimal.div_appreciable` | Infinitesimal.div_unlimited, Appreciable.div_unlimited, Appreciable.div, Appreciable.div_infinitesimal, Unlimited.div_infinitesimal, Unlimited.div_appreciable |
| Section 5.2 table: roots | proved | `Goldblatt.Infinitesimal.hroot` | hroot n = extension of x^(1/n); hroot_pow, hroot_nonneg, hroot_pos; Appreciable.hroot, Unlimited.hroot; infinitesimal_of_pow, appreciable_of_pow, unlimited_of_pow |
| Section 5.2 table: indeterminate forms | proved | `Goldblatt.indeterminate_infinitesimal_div_infinitesimal` | each form shown to take infinitesimal, appreciable and unlimited values; also indeterminate_unlimited_div_unlimited, indeterminate_infinitesimal_mul_unlimited, indeterminate_unlimited_add_unlimited |
| Section 5.2: L and I are subrings; I is an ideal of L | proved | `Goldblatt.infinitesimalIdeal` | limitedSubring, infinitesimalNonUnitalSubring, infinitesimalIdeal, infinitesimalIdeal_ne_top |
| Section 5.2: nth roots for hypernatural n (transfer remark) | proved | `Goldblatt.exists_hpow_eq` | every positive hyperreal has a positive N-th root for nonzero hypernatural N |
| Exercise 5.2.1 | proved | `Goldblatt.hpow` | hpow = extension of real rpow, with the exponent laws |
| Section 5.3 (finite vs infinite) | proved | `Goldblatt.infinite_setOf_hyperNat_le` | the one formal claim; the rest is prose |
| Section 5.4 definition: infinitely close, halo | proved | `Goldblatt.InfClose` | notation b ≊ c; hal; infinitesimal_iff_infClose_zero, hal_zero, hal_eq_hal_iff, infClose_coe_iff |
| Section 5.4 definition: limited distance, galaxy | proved | `Goldblatt.LimClose` | notation b ∼ c; gal; limited_iff_limClose_zero, gal_zero, gal_eq_gal_iff |
| Exercise 5.5(1) | proved | `Goldblatt.infClose_equivalence` | and limClose_equivalence; Trans instances |
| Exercise 5.5(2) | proved | `Goldblatt.coe_le_coe_of_infClose_le_infClose` | non-real case le_or_infClose_of_infClose_le_infClose and counterexample exists_infClose_le_infClose_not_le |
| Exercise 5.5(3) | proved | `Goldblatt.hal_eq_image_add` |  |
| Exercise 5.5(4) | proved | `Goldblatt.gal_eq_image_add` |  |
| Exercise 5.5(5) | proved | `Goldblatt.InfClose.mul_left` | failure for unlimited b: exists_infClose_mul_unlimited_not_infClose |
| Exercise 5.5(6) | proved | `Goldblatt.exists_hyperInt_mem_gal` | plus exists_hyperRat_not_hyperInt_mem_gal and exists_not_hyperRat_mem_gal |
| Section 5.5 Real Comparisons | proved | `Goldblatt.lt_of_mem_hal_of_coe_lt` | disjoint_hal_coe, coe_le_coe_of_infClose_le, coe_le_coe_of_le_infClose |
| Theorem 5.6.1 | proved | `Goldblatt.Limited.existsUnique_infClose` | sh b := sSup {r \| r < b}; Limited.infClose_sh follows the book's Dedekind proof; sh_eq_of_infClose; sh_eq_stdPart bridges to Mathlib |
| Theorem 5.6.2(1) | proved | `Goldblatt.sh_add` | sh_sub, sh_neg |
| Theorem 5.6.2(2) | proved | `Goldblatt.sh_mul` |  |
| Theorem 5.6.2(3) | proved | `Goldblatt.sh_div` | hypothesis sh c != 0; Appreciable.sh_inv; Limited.appreciable_iff_sh_ne_zero |
| Theorem 5.6.2(4) | proved | `Goldblatt.sh_pow` |  |
| Theorem 5.6.2(5) | proved | `Goldblatt.sh_abs` |  |
| Theorem 5.6.2(6) | proved | `Goldblatt.sh_hroot` | sh (hroot n b) = sh b ^ (1/n) for limited b >= 0, n != 0; sh_hsqrt is the case n = 2; hsqrt_eq_hroot_two |
| Theorem 5.6.2(7) | proved | `Goldblatt.sh_le_sh` | plus Limited.sh_le, Limited.le_sh, Limited.lt_of_sh_lt, Limited.lt_of_lt_sh, lt_of_sh_lt_sh, sh_nonneg |
| Section 5.6: sh is an order-preserving ring homomorphism of L onto R with kernel I; cosets are halos | proved | `Goldblatt.shadowHom` | shadowHom_monotone, shadowHom_surjective, ker_shadowHom, quotient_mk_eq_iff_mem_hal |
| Theorem 5.6.3 | proved | `Goldblatt.limitedQuotientEquiv` | limitedSubring / infinitesimalIdeal ring-isomorphic to R; infinitesimalIdeal_isMaximal |
| Exercise 5.7(1) | proved | `Goldblatt.InfClose.div` | InfClose.add, sub, mul, inv; counterexample exists_infClose_div_not_infClose |
| Exercise 5.7(2) | proved | `Goldblatt.Infinitesimal.hsin_div_infClose` | hsin/hcos/htan extensions; hsin_infClose, hcos_infClose, htan_infClose, hcos_sub_one_div_infClose via transferred inequalities |
| Exercise 5.7(3) | proved | `Goldblatt.exists_hyperRat_infClose` | docstring reworded this pass |
| Exercise 5.7(4) | proved | `Goldblatt.limitedHyperRatQuotientEquiv` | limitedHyperRat / infinitesimalHyperRat ring-isomorphic to R; docstring reworded this pass |
| Theorem 5.8.1 | proved | `Goldblatt.cauchy_converges_of_shadowProperty` | stated for an arbitrary ordered field with ShadowProperty so it is not vacuous; cauSeq_isComplete_of_shadowProperty; real form real_cauchy_converges_of_shadows; converse shadowProperty_of_exists_isLUB |
| Sections 5.8-5.9 preliminary (not a numbered book item) | proved | `Goldblatt.archimedean_of_shadowProperty` | the shadow property implies the Archimedean property |
| Exercise 5.9(a) | proved | `Goldblatt.exists_least_int_div_mem_upperBounds` | stated for an Archimedean ordered field, which is what this part uses |
| Exercise 5.9(b) | proved | `Goldblatt.limited_least_int_div` | GENERALIZED this pass: now for every positive hypernatural N = [k_n] (k eventually positive w.r.t. the hyperfilter), s_m least for every m > 0; conclusion: class of s_{k_n}/k_n lies between two field elements. Core lemma limited_of_eventually_least_int_div (pointwise form); old special case N = [1,2,3,...] kept as limited_least_int_div_succ; helper exists_mem_lt_of_least_int_div |
| Exercise 5.9(c) | proved | `Goldblatt.exists_isLUB_of_shadowProperty` | uses limited_least_int_div_succ; shadowProperty_iff_exists_isLUB; real form real_exists_isLUB_of_shadows |
| Section 5.10: *N closed under + and · | proved | `Goldblatt.hyperNat_add_mul_mem` | restates Ch03 |
| Section 5.10: limited hypernaturals are exactly N; nonstandard ones are unlimited and exceed N | proved | `Goldblatt.limited_hyperNat_iff` | unlimited_of_mem_hyperNat_of_notMem_range, natCast_lt_of_mem_hyperNat_of_notMem_range, omega_mem_unlimitedHyperNat |
| Section 5.10: galaxies of hypernaturals are copies of Z; N = gal(1) ∩ *N; equal galaxies iff limited distance | proved | `Goldblatt.natGalaxy_eq_of_unlimited` | natGalaxy, natGalaxyOrderIso, natGalaxy_natCast, natGalaxy_eq_iff |
| Section 5.10: ordering of *N-galaxies; no greatest, no smallest unlimited, dense | proved | `Goldblatt.hyperNat_order_structure` | GalLT, galLT_iff_forall_mem_gal, exists_hyperNat_galLT, exists_unlimited_hyperNat_galLT, exists_hyperNat_galLT_between; summary docstring and 5.10 module doc reworded this pass |
| Section 5.10 supplement (not in the book; task extras): floor and no least unlimited hypernatural | proved | `Goldblatt.not_exists_isLeast_unlimitedHyperNat` | exists_hyperNat_le_lt_add_one (N <= x < N+1 for x >= 0), exists_lt_of_mem_unlimitedHyperNat; docstrings now marked 'supplement (not stated in the book)' and listed in the 5.10 module doc |
| Exercise 5.11(1) | proved | `Goldblatt.hyperInt_order_structure` | limited_hyperInt_iff (kept in the 5.10 part of the file because limited_hyperNat_iff depends on it; now documented), intGalaxy, intGalaxyOrderIso, exists_hyperInt_galLT, exists_hyperInt_galLT', exists_hyperInt_galLT_between |
| Exercise 5.11(2) | proved | `Goldblatt.exists_hyperNat_forall_le_hdvd` | HDvd (a ∣ₕ b), hnat_hdvd_hnat_iff, natCast_hdvd_natCast_iff, HDvd.trans; second part exists_hyperNat_forall_nat_hdvd. Statement not re-audited in this pass. |
| Exercise 5.11(3) definition of hyperprimes | proved | `Goldblatt.hyperPrime` | hyperPrime_subset_hyperNat, natCast_mem_hyperPrime_iff, hnat_mem_hyperPrime_iff. Statement not re-audited in this pass. |
| Exercise 5.11(3)(a) | proved | `Goldblatt.mem_hyperPrime_iff` | docstring reworded this pass |
| Exercise 5.11(3)(b) | proved | `Goldblatt.exists_hyperPrime_hdvd` | docstring reworded this pass |
| Exercise 5.11(3)(c) | proved | `Goldblatt.hyperNat_eq_of_forall_hyperPrime_pow_hdvd` | powers with hypernatural exponent via hpow (hpow_hnat); docstring reworded this pass |
| Exercise 5.11(3)(d) | proved | `Goldblatt.forall_nat_hdvd_iff_forall_prime_pow_hdvd` | docstring reworded this pass |
| Section 5.12 (nonstandard proof of infinitely many primes) | proved | `Goldblatt.infinite_setOf_prime_of_nonstandard` | exists_nonstandard_hyperPrime (nonstandard Euclid argument), then infinitude of the primes deduced from it. Entry rebuilt from the file (previous ledger truncated); statement not re-audited in this pass. |

## 6. Convergence of Sequences and Series

| Book item | Status | Lean declaration | Note |
|---|---|---|---|
| Chapter 6 opening: extended terms | proved | `Goldblatt.hyperSeq_hnat` | Uses Ch03 hyperSeq. Also hnat_mem_unlimitedHyperNat_iff, exists_hnat_of_mem_unlimitedHyperNat, mem_unlimitedHyperNat_of_le, add_one_mem_unlimitedHyperNat, hyperSeq_add/sub/mul/div/neg/abs/const/const_mul, hyperSeq_add_one, hyperSeq_mono, hyperSeq_le_hyperSeq, hyperSeq_le_coe, coe_le_hyperSeq. Docstrings now carry bold book references. |
| Chapter 6 opening: extended tail | proved | `Goldblatt.extendedTail` | def extendedTail s := hyperSeq s '' unlimitedHyperNat, with mem_extendedTail_iff, hyperSeq_mem_extendedTail, extendedTail_nonempty, forall_mem_extendedTail_iff. Overview prose rewritten in independent wording. |
| Theorem 6.1.1 | proved | `Goldblatt.tendsto_iff_forall_unlimited_infClose` | Tendsto s atTop (nhds L) iff hyperSeq s N ≊ L for all unlimited N. Also hyperSeq_infClose_of_tendsto, tendsto_iff_extendedTail_subset_hal, sh_hyperSeq_of_tendsto; example hyperSeq_one_div_omega. |
| Theorem 6.2.1 | proved | `Goldblatt.exists_tendsto_of_monotone_or_antitone` | Book's proof: shadow of an extended term is the LUB. Parts are now in the ROOT namespace: Monotone.isLUB_sh_hyperSeq, Monotone.exists_isLUB_tendsto (1), Antitone.exists_isGLB_tendsto (2), so dot notation on hs : Monotone s works. Section intro reworded. |
| Section 6.2 application (c^n -> 0 for 0<c<1) | proved | `Goldblatt.tendsto_pow_zero_of_pos_of_lt_one` | Book's argument L ≊ c^(N+1) = c·c^N ≊ cL. |
| Section 6.3 uniqueness of limits | proved | `Goldblatt.limit_unique` |  |
| Theorem 6.3.1 | proved | `Goldblatt.limit_add` | (1) limit_add, (2) limit_const_mul, (3) limit_mul, (4) limit_div; supplement limit_sub. |
| Theorem 6.4.1 | proved | `Goldblatt.bounded_iff_forall_unlimited_limited` | Book form (exists b, \|s n\| < b). Also isBounded_range_iff_forall_unlimited_limited and limited_hyperSeq_of_forall_unlimited. |
| Section 6.4 refinements (bounded above / below) | proved | `Goldblatt.bddAbove_range_iff_forall_unlimited_not_posUnlimited` | And bddBelow_range_iff_forall_unlimited_not_negUnlimited. |
| Section 6.4 definition of divergence to infinity | proved | `Goldblatt.tendsto_atTop_iff_forall_exists_tail` | Book's definition identified with Tendsto s atTop atTop. |
| Section 6.4 definition of divergence to minus infinity | proved | `Goldblatt.tendsto_atBot_iff_forall_exists_tail` | Book's definition identified with Tendsto s atTop atBot. |
| Theorem 6.4.2 | proved | `Goldblatt.tendsto_atTop_iff_forall_unlimited_posUnlimited` | (1); (2) is tendsto_atBot_iff_forall_unlimited_negUnlimited. Book-definition forms: forall_exists_tail_gt_iff_forall_unlimited_posUnlimited and forall_exists_tail_lt_iff_forall_unlimited_negUnlimited. |
| Theorem 6.5.1 | proved | `Goldblatt.cauchySeq_iff_forall_unlimited_infClose` | CauchySeq s iff s_M ≊ s_N for all unlimited M, N. |
| Theorem 6.5.2 (Cauchy's convergence criterion) | proved | `Goldblatt.cauchySeq_iff_exists_tendsto` | Limitedness of extended terms proved directly by transfer; that lemma is now the root-namespace CauchySeq.limited_hyperSeq. |
| Section 6.6 definition of cluster point | proved | `Goldblatt.mapClusterPt_iff_forall_exists` | MapClusterPt L atTop s iff the book's sentence. clusterSet s is the set C_s. |
| Section 6.6 cluster points and subsequences | mathlib | `Goldblatt.mapClusterPt_iff_exists_subseq` | Book quotes this as known; proved from Mathlib's subseq_tendsto_of_neBot. |
| Theorem 6.6.1 | proved | `Goldblatt.mapClusterPt_iff_exists_unlimited_infClose` | Also mem_clusterSet_iff, sh_hyperSeq_mem_clusterSet, clusterSet_eq_shadows, clusterSet_eq_image_sh, clusterSet_eq_sh_image_extendedTail. |
| Theorem 6.6.2 (Bolzano-Weierstrass) | proved | `Goldblatt.exists_mapClusterPt_of_bounded` |  |
| Exercise 6.7(1) | proved | `Goldblatt.limit_le_limit` |  |
| Exercise 6.7(2) | proved | `Goldblatt.limit_squeeze` |  |
| Exercise 6.7(3) | proved | `Goldblatt.existsUnique_mapClusterPt_of_tendsto` |  |
| Exercise 6.7(4) | proved | `Goldblatt.tendsto_of_bounded_of_unique_mapClusterPt` | Bounded case: yes. Unbounded case: counterexample exists_unique_mapClusterPt_not_tendsto. |
| Section 6.8 (bounds of the sequence are bounds of C_s) | proved | `Goldblatt.le_of_mem_clusterSet_of_forall_le` | NEW faithful form: if s n ≤ b for all n and c is a cluster point then c ≤ b; mirror le_of_mem_clusterSet_of_forall_ge. Set forms upperBounds_range_subset_upperBounds_clusterSet and lowerBounds_range_subset_lowerBounds_clusterSet. bddAbove_clusterSet / bddBelow_clusterSet are kept as corollaries with corrected docstrings. |
| Section 6.8 definition of lim sup / lim inf (bounded sequences) | proved | `Goldblatt.limSup` | limSup s = sSup (clusterSet s), limInf s = sInf (clusterSet s); limSup_eq_sSup_image_sh, limInf_eq_sInf_image_sh, isGreatest_limSup, isLeast_limInf, limInf_le_limSup. Agreement with Mathlib: limSup_eq_limsup, limInf_eq_liminf. limSup_limInf_neg_one_pow is now labelled as an illustration that is not in the book. |
| Exercise 6.8.1 | proved | `Goldblatt.limSup_mem_clusterSet` | And limInf_mem_clusterSet. Nonstandard proof via principle (b). |
| Theorem 6.8.2 | proved | `Goldblatt.eq_limSup_iff` | Lim inf formulation: eq_limInf_iff. |
| Theorem 6.8.3 | proved | `Goldblatt.tendsto_iff_limSup_eq_and_limInf_eq` |  |
| Theorem 6.8.4 | proved | `Goldblatt.eventually_lt_limSup_add` | (1) eventually_lt_limSup_add / finite_setOf_limSup_add_le; (2) frequently_limSup_sub_lt / infinite_setOf_limSup_sub_lt. |
| Section 6.8 principles (a) and (b) | proved | `Goldblatt.forall_unlimited_mem_starSet_iff` | (a) forall_unlimited_mem_starSet_iff, (b) exists_unlimited_mem_starSet_iff; term forms forall_/exists_unlimited_hyperSeq_mem_starSet_iff; order forms forall_unlimited_hyperSeq_lt_iff, forall_unlimited_lt_hyperSeq_iff, exists_unlimited_hyperSeq_lt_iff, exists_unlimited_lt_hyperSeq_iff (docstrings now start with the bold reference); sequence forms eventually_atTop_iff_forall_tendsto_hyperfilter, frequently_atTop_iff_exists_tendsto_hyperfilter. |
| Theorem 6.8.5 | proved | `Goldblatt.tendsto_tailSup_limSup` | tailSup s n = sSup (s '' Ici n); also limSup_eq_iInf_tailSup, le_tailSup. |
| Section 6.8 lim sup of an arbitrary sequence | proved | `Goldblatt.limSupE` | EReal-valued definition by the book's cases; limSupE_eq_limsup (agreement with Mathlib). Case lemmas limSupE_of_not_bddAbove (1), limSupE_of_tendsto_atBot (2)(i), limSupE_of_bddAbove_of_not_tendsto_atBot (2)(ii); limSupE_eq_coe_limSup, eventually_lt_of_limSupE_lt. |
| Exercise 6.9(1) | proved | `Goldblatt.limInfE` | Definition by cases; limInfE_eq_neg_limSupE_neg, limInfE_eq_liminf, limInfE_eq_coe_limInf, eventually_gt_of_lt_limInfE. |
| Exercise 6.9(2) | proved | `Goldblatt.tendsto_tailInf_limInf` | Counterparts of 6.8.4: eventually_limInf_sub_lt, finite_setOf_le_limInf_sub, frequently_lt_limInf_add, infinite_setOf_lt_limInf_add; of 6.8.5: tendsto_tailInf_limInf, limInf_eq_iSup_tailInf; reduction step tailInf_eq_neg_tailSup_neg. |
| Exercise 6.9(3) | proved | `Goldblatt.exists_tail_subset_Ioo` |  |
| Section 6.10 definitions (partial sums, hyperfinite sums) | proved | `Goldblatt.hyperSumIcc` | partialSum, SeriesSum, SeriesConverges, hyperSum, hyperSumIcc; indexed from 0. Transfer steps hyperSum_add_one, hyperSumIcc_hnat, hyperSumIcc_le_hyperSumIcc, hyperSumIcc_nonneg, abs_hyperSumIcc_le (now with bold references). Mathlib bridges: seriesSum_of_hasSum, seriesConverges_iff_summable_of_nonneg, seriesConverges_abs_iff_summable. |
| Section 6.10 first bullet (sum = L iff hyperfinite sums ≊ L) | proved | `Goldblatt.seriesSum_iff_forall_unlimited_infClose` | Also SeriesSum.eq_sh. |
| Section 6.10 second bullet (Cauchy criterion for series) | proved | `Goldblatt.seriesConverges_iff_forall_unlimited_hyperSumIcc` |  |
| Section 6.10 third bullet (terms tend to 0) | proved | `Goldblatt.SeriesConverges.tendsto_zero` |  |
| Section 6.10 absolute convergence implies convergence | proved | `Goldblatt.seriesConverges_of_abs` | Nonstandard proof via the Cauchy criterion and the transferred triangle inequality. |
| Exercise 6.11(1) | proved | `Goldblatt.exists_diverging_series_with_infinitesimal_terms` | Harmonic series; divergence proved nonstandardly. |
| Exercise 6.11(2) | proved | `Goldblatt.SeriesSum.add` | SeriesSum.add, SeriesSum.sub, SeriesSum.const_mul. |
| Exercise 6.11(3) | proved | `Goldblatt.seriesConverges_iff_forall_limited_of_nonneg` | And forall_limited_iff_exists_limited_of_nonneg, seriesConverges_of_exists_limited_of_nonneg. |
| Exercise 6.11(4) (comparison test) | proved | `Goldblatt.seriesConverges_of_nonneg_of_le` | Uses result (3) as the book asks. |
| Exercise 6.11(5) | proved | `Goldblatt.seriesConverges_of_forall_unlimited_le` | Also forall_unlimited_hyperSeq_le_iff, seriesConverges_of_forall_ge_le. |
| Exercise 6.11(6) | proved | `Goldblatt.infinitesimal_hyperSumIcc_iff_of_tendsto_div` | CORRECTED: printed statement is false when a_i/b_i tends to 0. Proved with nonzero limit (also seriesConverges_iff_of_tendsto_div); half valid for any limit: infinitesimal_hyperSumIcc_of_tendsto_div / seriesConverges_of_tendsto_div; counterexample exists_tendsto_div_seriesConverges_not_seriesConverges. |
| Exercise 6.11(7) | proved | `Goldblatt.seriesSum_geometric` | (a) seriesSum_geometric via hyperSum_geometric; (b) infinitesimal_hyperSumIcc_geometric. |
| Exercise 6.11(8) (ratio test, convergence) | proved | `Goldblatt.seriesConverges_abs_of_limSupE_ratio_lt_one` | (a) exists_forall_unlimited_ratio_lt, (b) exists_forall_ge_ratio_lt, (c) abs_le_pow_mul_abs_of_ratio (weak, all n), abs_lt_pow_mul_abs_of_ratio (book's strict form, n >= 1), sum_Icc_abs_le_of_ratio (block-sum inequality). (d) RE-PROVED by the book's route: the block-sum inequality of (c) is transferred to unlimited blocks via hyperSumIcc_hnat and combined with 7(b) (infinitesimal_hyperSumIcc_geometric) and the Cauchy criterion. Added hypothesis a_i ≠ 0 (implicit in the book); lim sup in EReal. Transfer steps hyperSeq_ne_zero, hyperSeq_ratio. Section 6.11 intro no longer contradicts the overview. |
| Exercise 6.11(9) (ratio test, divergence) | proved | `Goldblatt.not_seriesConverges_of_one_lt_limInfE_ratio` | (a) abs_hyperSeq_lt_abs_hyperSeq_add_one and exists_forall_gt_abs_lt, (b) main theorem. Hypothesis 1 < limInfE (EReal), allowing +∞. |
| Exercise 6.11(10) | proved | `Goldblatt.infinitesimal_pow_div_factorial` | Via the ratio test as the book asks; x = 0 handled separately. |
| Exercise 6.11(11) (Leibniz alternating series test) | proved | `Goldblatt.seriesConverges_alternating` | Inequality abs_sum_Icc_alternating_le transferred to unlimited blocks. Sign is (-1)^i because of 0-indexing. |

## 7. Continuous Functions

| Book item | Status | Lean declaration | Note |
|---|---|---|---|
| Chapter 7 opening remark (*(a,b) is the hyperreal interval) | prose | `Goldblatt.starSet_Ioo_real` | Already proved in Chapter 3; cited in the preliminary section's exposition (line reflowed). |
| Chapter 7 convention (functions on a domain A) | proved | `Goldblatt.continuousAt_subtype_iff_infClose` | Theorem 7.1.3 for f : A → ℝ with the Chapter 3 extension starMapOn, reduced to the total-function form via starMapOn_eq_starMap. |
| Chapter 7 transfer tool (limits by transfer, not a numbered item) | proved | `Goldblatt.tendsto_iff_starMap_mem_filterMonad` | For a countably generated source filter, Tendsto f l l' iff ⋆f maps filterMonad l into filterMonad l'. Companions: filterMonad, ofSeq_mem_filterMonad, filterMonad_inf_principal, mem_filterMonad_nhds / _atTop / _atBot, tendsto_inf_principal_iff_filterMonad. |
| Theorem 7.1.1 | proved | `Goldblatt.continuousAt_iff_infClose` | ContinuousAt f c iff x ≊ c implies ⋆f x ≊ f c. Halo form continuousAt_iff_image_hal_subset; global form continuous_iff_infClose; rule form ContinuousAt.starMap_infClose. |
| Corollary 7.1.2 | proved | `Goldblatt.continuousAt_tfae` | Three-way TFAE including the positive-infinitesimal-radius condition; rule form continuousAt_of_exists_radius. |
| Theorem 7.1.3 | proved | `Goldblatt.continuousWithinAt_tfae` | TFAE for continuity relative to A, without the book's assumption c ∈ A. Also continuousWithinAt_iff_infClose, continuousOn_iff_infClose, continuousWithinAt_of_exists_radius. |
| Section 7.2 (continuity of sine) | proved | `Goldblatt.continuous_sin` | Book's argument via the transferred addition formula (hsin_add) and Exercise 5.7(2); cosine done the same way (continuous_cos). |
| Section 7.3 item 1 (right-hand limit) | proved | `Goldblatt.tendsto_nhdsWithin_Ioi_iff_infClose` | Filter 𝓝[A ∩ Ioi c] c. |
| Section 7.3 item 2 (left-hand limit) | proved | `Goldblatt.tendsto_nhdsWithin_Iio_iff_infClose` | Filter 𝓝[A ∩ Iio c] c. |
| Section 7.3 item 3 (two-sided limit) | proved | `Goldblatt.tendsto_nhdsWithin_diff_singleton_iff_infClose` | Filter 𝓝[A \ {c}] c. Whole-line variants tendsto_punctured_nhds_iff_infClose, tendsto_nhds_iff_infClose. |
| Section 7.3 item 4 (limit +∞ at c) | proved | `Goldblatt.tendsto_nhdsWithin_diff_singleton_atTop_iff` | Target expressed as PosUnlimited (⋆f x). |
| Section 7.3 item 5 (limit −∞ at c) | proved | `Goldblatt.tendsto_nhdsWithin_diff_singleton_atBot_iff` | Target expressed as NegUnlimited (⋆f x). |
| Section 7.3 item 6 (limit at +∞) | proved | `Goldblatt.tendsto_atTop_inf_principal_iff_infClose` | Filter atTop ⊓ 𝓟 A. The book's proviso is exists_posUnlimited_mem_starSet_iff. Whole-line variant tendsto_atTop_nhds_iff_infClose. |
| Section 7.3 item 7 (limit at −∞) | proved | `Goldblatt.tendsto_atBot_inf_principal_iff_infClose` | Proviso: exists_negUnlimited_mem_starSet_iff. Whole-line variant tendsto_atBot_nhds_iff_infClose. |
| Exercise 7.4(1) | proved | `Goldblatt.tendsto_inf_principal_iff_filterMonad` | The derivations of the seven characterisations are the proofs of the Section 7.3 items, all through this lemma. |
| Exercise 7.4(2) first item (two-sided iff both one-sided) | proved | `Goldblatt.tendsto_diff_singleton_iff_Ioi_and_Iio` |  |
| Exercise 7.4(2) second item (sum, product, quotient of limits) | proved | `Goldblatt.tendsto_diff_singleton_add` | Also tendsto_diff_singleton_mul and tendsto_diff_singleton_div (M ≠ 0), via Exercise 5.7(1). |
| Exercise 7.4(2) third item (continuous iff limit equals value) | proved | `Goldblatt.continuousWithinAt_iff_tendsto_diff_singleton` | Also continuousAt_iff_tendsto_punctured. |
| Exercise 7.4(3) f1 = sin(1/x) | proved | `Goldblatt.continuousAt_sinInv_iff` | Continuous at c iff c ≠ 0; nonstandard proofs in both directions. |
| Exercise 7.4(3) f2 = x sin(1/x) | proved | `Goldblatt.continuous_mulSinInv` | Continuous everywhere. |
| Exercise 7.4(3) f3 (indicator of the rationals) | proved | `Goldblatt.not_continuousAt_ratIndicator` | Continuous nowhere. |
| Exercise 7.4(3) f4 (x on rationals, −x on irrationals) | proved | `Goldblatt.continuousAt_ratSign_iff` | Continuous at c iff c = 0. |
| Exercise 7.4(3) f5 (Thomae function) | proved | `Goldblatt.continuousAt_thomae_iff` | Continuous at c iff c irrational. |
| Section 7.5 definition (partition points) | proved | `Goldblatt.partitionPoint` | p_k = a + k(b−a)/n for standard n, k, with partitionPoint_zero / _self / _succ / _mem_Icc and the finite step exists_partitionPoint_crossing. Tools limited_of_mem_Icc, sh_mem_Icc, infClose_sh_of_mem_starSet_Icc, infinitesimal_width. |
| Sections 7.5 and 7.6 (points a + K(b−a)/N of the partition with hypernatural indices) | proved | `Goldblatt.hyperPartitionPoint` | NEW in this pass (review finding 3). Definition on ℝ*, with hyperPartitionPoint_hnat (class of standard partition points), _natCast, _zero, _self, _add_one, and hyperPartitionPoint_mem_starSet_Icc (K ≤ N hypernaturals gives a member of ⋆[a,b]). |
| Section 7.5 remark (s_N has the form a + K(b−a)/N) | proved | `Goldblatt.exists_hyperPartitionPoint_crossing` | NEW. For a nonzero hypernatural N there is a hypernatural K < N with ⋆f(s_N) < d ≤ ⋆f(s_N + (b−a)/N); transfer of exists_partitionPoint_crossing. |
| Section 7.5 Intermediate Value Theorem | proved | `Goldblatt.intermediate_value_Icc` | Book's proof: c is the shadow of s_N for N = ω. The increasing case intermediate_value_Icc_of_lt is now proved from exists_hyperPartitionPoint_crossing instead of inline sequences; statement unchanged. Does not use Mathlib's IVT. Docstring reflowed. |
| Section 7.6 (property of the infinitesimal partition: it meets every halo) | proved | `Goldblatt.exists_hyperPartitionPoint_infClose` | NEW (review finding 3). For a < b, real t ∈ [a,b] and unlimited hypernatural N there is a hypernatural K ≤ N with a + K(b−a)/N ≤ t and a + K(b−a)/N ≊ t. Companion exists_hyperPartitionPoint_max: some K ≤ N where ⋆f dominates its values at all partition points. |
| Section 7.6 Extreme Value Theorem | proved | `Goldblatt.extreme_value_Icc` | Book's proof with the infinitesimal partition. exists_forall_le_Icc is now proved from exists_hyperPartitionPoint_max and exists_hyperPartitionPoint_infClose; minimum via −f (exists_forall_ge_Icc). Does not use Mathlib's EVT. |
| Theorem 7.7.1 | proved | `Goldblatt.uniformContinuousOn_iff_infClose` | UniformContinuousOn f A iff x ≊ y implies ⋆f x ≊ ⋆f y for all x, y ∈ ⋆A. Also uniformContinuous_iff_infClose and UniformContinuousOn.starMap_infClose. |
| Theorem 7.7.2 | proved | `Goldblatt.uniformContinuousOn_Icc_of_continuousOn` | Book's shadow argument. Docstring reflowed. |
| Exercise 7.8(1) | proved | `Goldblatt.exists_mem_starSet_Ioo_sh_notMem` | 'Explain why' formalized as witnesses for every kind of interval listed: also exists_mem_starSet_Ioc_sh_notMem, exists_mem_starSet_Ico_sh_notMem, exists_mem_starSet_Ioi_not_limited, exists_mem_starSet_Iio_not_limited. |
| Exercise 7.8(2) | proved | `Goldblatt.not_uniformContinuousOn_one_div_Ioo` | Uses ε and ε/2. continuousOn_one_div_Ioo (Mathlib one-liner) is included for contrast. |
| Exercise 7.8(3) | proved | `Goldblatt.cauchySeq_comp_of_uniformContinuous` | Via Theorem 6.5.1 and hyperSeq_comp. |
| Exercise 7.8(4) | proved | `Goldblatt.continuousOn_Icc_of_monotone_or_antitone` | Hypothesis: every r ∈ uIcc (f a) (f b) is a value on [a,b]. Increasing case continuousOn_Icc_of_monotoneOn_of_forall_exists. Docstring reflowed. |
| Section 7.9 definitions (Lipschitz condition, contraction mapping) | proved | `Goldblatt.lipschitzWith_iff_abs_sub_le` | Bridge to Mathlib's LipschitzWith; the section's results are also given for LipschitzWith and ContractingWith. |
| Section 7.9 (Lipschitz implies uniformly continuous) | proved | `Goldblatt.uniformContinuous_of_lipschitz` | Transfer step is abs_starMap_sub_le_of_lipschitz. |
| Section 7.9 (uniqueness of the fixed point) | proved | `Goldblatt.fixedPoint_unique_of_contraction` |  |
| Theorem 7.9.1 | proved | `Goldblatt.existsUnique_fixedPoint_of_contraction` | Book's proof: shadow of an extended term of the iterates, with estimates (viii) and (ix). Stated for any constant c < 1. |
| Section 7.9 remark (iterates converge to the fixed point) | proved | `Goldblatt.tendsto_iterate_of_contraction` | Via Theorem 6.1.1. |
| Section 7.9 example f(x) = x/2 + 1/2 | proved | `Goldblatt.halfAddHalf_fixedPoint` | Also halfAddHalf_lipschitz and halfAddHalf_iterate. |
| Section 7.10 (Cauchy's principle) | proved | `Goldblatt.cauchy_principle_tfae` | A property is a set S of reals, its transform is ⋆S. Core exists_real_radius_of_hyperreal_radius is in Limits.lean; rule form cauchy_principle. |
| Exercise 7.11(1) | proved | `Goldblatt.hal_subset_starSet_iff` | hal c ⊆ ⋆D iff D contains some (c−δ, c+δ). |
| Exercise 7.11(2) | proved | `Goldblatt.exists_Ioo_const_of_const_on_hal` |  |
| Exercise 7.11(3) | proved | `Goldblatt.eq_of_starMap_real_of_ordConnected` | Interval expressed as Set.OrdConnected. Local step exists_radius_const_of_starMap_real applies Cauchy's principle relative to A; the Section 7.11 module doc now says this instead of claiming it follows from Exercise (2). Locally-constant-to-constant uses Mathlib's connectedness of intervals. |
| Section 7.12 definition (hypersequence of functions) | proved | `Goldblatt.hyperFunSeq` | ⋆(fun t x => F ⌊t⌋₊ x). Both book remarks proved: hyperFunSeq_natCast and hyperFunSeq_coe. |
| Theorem 7.12.1 | proved | `Goldblatt.tendsto_pointwise_iff_infClose` | Immediate from Theorem 6.1.1. |
| Theorem 7.12.2 | proved | `Goldblatt.tendstoUniformlyOn_iff_infClose` | Standard side is Mathlib's TendstoUniformlyOn F f atTop A. Rule form TendstoUniformlyOn.hyperFunSeq_infClose. |
| Section 7.12 example, pointwise limit of x^n on [0,1] | proved | `Goldblatt.tendsto_pow_powLimit` | Limit function powLimit; NEW starMap_powLimit_of_lt_one (⋆powLimit x = 0 for hyperreal x < 1). |
| Section 7.12 example, claim (b): some M with x^n ≃ 0 beyond M, for arbitrary x < 1 in *[0,1] | proved | `Goldblatt.exists_hyperNat_forall_pow_infClose_zero` | NEW (review finding 1). Universally quantified in x as in the book. Stated with K ≥ M where the book has n > M (equivalent up to M+1; noted in the docstring). |
| Section 7.12 example: any such M is unlimited when x ≃ 1 | proved | `Goldblatt.mem_unlimitedHyperNat_of_hyperFunSeq_pow_infClose_zero` | NEW. From hyperFunSeq_pow_infClose_one (x^n ≃ 1 for standard n). |
| Section 7.12 example, claim (c): unlimited N with {x^n : n ≤ N} inside hal(1), for arbitrary x ≃ 1 in *[0,1] | proved | `Goldblatt.exists_unlimited_forall_pow_infClose_one` | NEW. The book appeals to Robinson's sequential lemma (Chapter 15); here N = [⌊1/√d_n⌋] is constructed directly with Bernoulli's inequality, disclosed in the docstring and on the chapter page. |
| Section 7.12 example: x^n does not converge uniformly on [0,1] | proved | `Goldblatt.not_tendstoUniformlyOn_pow` | Re-proved by the book's argument: x < 1, x ≃ 1, unlimited N with x^N ≃ 1, while ⋆f(x) = 0, contradicting Theorem 7.12.2. |
| Section 7.12 example, explicit instance (not in the book) | proved | `Goldblatt.exists_hyperFunSeq_pow_eq_half` | Kept as an illustration and existence witness: x = [(1/2)^(1/(n+1))] with x^N = 1/2 at N = [n+1] and x^K ≃ 0 for K ≥ [(n+1)^2]. Docstring relabelled 'an explicit instance'. |
| Theorem 7.13.1 | proved | `Goldblatt.continuousOn_of_tendstoUniformlyOn` | Book's first proof with the ε/4 estimate. Docstring reflowed. |
| Theorem 7.14.1 | proved | `Goldblatt.exists_infinitesimal_radius_hyperFunSeq` | For every hypernatural N and y ∈ ⋆A there is a positive infinitesimal d with f_N(x) ≃ f_N(y) for x ∈ ⋆A within d of y. |
| Section 7.14 (second proof of Theorem 7.13.1) | proved | `Goldblatt.continuousOn_of_tendstoUniformlyOn'` | Uses Theorem 7.12.2 at ω, Theorem 7.14.1 and the criterion of Theorem 7.1.3(3). |
| Section 7.15 (Was Cauchy Right?) | prose |  | Historical discussion with no formal content; summarized in original prose. |

## 11. Internal and External Sets

| Book item | Status | Lean declaration | Note |
|---|---|---|---|
| Section 11.1 definition (internal set [A_n]) | proved | `Goldblatt.internalSet` | Generic over StarType; membership criterion ofSeq_mem_internalSet / hyperreal_ofSeq_mem_internalSet; well-definedness almostAll_mem_congr; germ form internalSetOfGerm. |
| Section 11.1 definition (internal / external) | proved | `Goldblatt.IsInternal` | IsInternalSet α X is generic with α explicit; IsInternal is the abbrev for Set ℝ*; IsExternal is its negation. |
| Section 11.1 example 1 (enlargements, *N, *Z, *Q, *R, finite sets of reals are internal) | proved | `Goldblatt.isInternalSet_starSet` | Also starSet_eq_internalSet, isInternal_hyperNat/hyperInt/hyperRat/univ, isInternal_image_coe_of_finite. |
| Section 11.1 example 2 (finite sets of hyperreals are internal) | proved | `Goldblatt.isInternalSet_of_finite` | Also internalSet_singleton, internalSet_range_finite, isInternal_of_finite. |
| Section 11.1 example 3 (hyperreal intervals are internal; not enlargements when a is unlimited) | proved | `Goldblatt.internalSet_Ioo` | All eight interval shapes (internalSet_Ixx, isInternal_Ixx). Non-enlargement: ne_starSet_of_subset_Ici_posUnlimited, Ioo_ne_starSet_of_posUnlimited; 'unlimited' corrected to 'positive unlimited'. |
| Section 11.1 example 4 ({k in *N : k <= N} internal) | proved | `Goldblatt.setOf_hyperNat_le_eq_internalSet` | 0-based; the book's {1..N} is setOf_hyperNat_one_le_le_eq_internalSet; isInternal_setOf_hyperNat_le, isInternal_setOf_hyperNat_one_le_le. |
| Section 11.1 example 5 ({k/N : k <= N} internal) | proved | `Goldblatt.setOf_div_hyperNat_eq_internalSet` | Also isInternal_setOf_div_hyperNat. |
| Theorem 11.2(1) | proved | `Goldblatt.internalSet_inter` | internalSet_inter/union/diff/compl; IsInternalSet.inter/union/diff/compl; IsInternal.* wrappers; finite unions and intersections isInternalSet_biUnion_finset / biInter_finset. |
| Theorem 11.2(2) | proved | `Goldblatt.internalSet_subset_iff` | Book's proof (choose a point of A_n - B_n). |
| Theorem 11.2(3) | proved | `Goldblatt.internalSet_eq_iff` | Also internalSet_congr, internalSet_eq_empty_iff, internalSet_nonempty_iff, internalSet_subset_starSet_iff. |
| Theorem 11.2(4) | proved | `Goldblatt.internalSet_ne_iff` |  |
| Section 11.2 remark (changing the defining sequence) | proved | `Goldblatt.internalSet_exists_rep_forall` | Corollaries IsInternalSet.exists_rep_nonempty, exists_rep_subset, exists_rep_nonempty_subset; exists_rep_forall_mem. |
| Section 11.2 (type-level view: internal sets are germs) | proved | `Goldblatt.internalSetEquiv` | Germ (hyperfilter ℕ) (Set α) ≃ {X // IsInternalSet α X}; internalSetOfGerm_injective, isInternalSet_iff_exists_germ. Supplement requested by the task. |
| Section 11.2 (subsets of an internal set of reals are internal) | proved | `Goldblatt.IsInternal.image_coe_subset` | Generic version IsInternalSet.image_of_subset. |
| Theorem 11.3.1 | proved | `Goldblatt.IsInternal.exists_isLeast` | With min[A_n] = [min A_n] as isLeast_internalSet_ofSeq. Second proof by the dagger transfer principle: IsInternal.exists_isLeast_of_transfer. |
| Theorem 11.3.2 | proved | `Goldblatt.IsInternal.induction` | From 0 (project convention); the book's form from 1 is IsInternal.induction_from_one. |
| Section 11.4 (N is external, by internal induction) | proved | `Goldblatt.isExternal_range_natCast` |  |
| Theorem 11.4.1 | proved | `Goldblatt.IsInternal.overflow` | Book's proof; stated without the unnecessary hypothesis X ⊆ *N. |
| Exercise 11.4.2 | proved | `Goldblatt.overflowPrinciple_iff_unboundedPrinciple` | Equivalence for any class closed under complement relative to *N (OverflowPrinciple, UnboundedPrinciple); instance for internal sets IsInternal.exists_natCast_mem_of_forall_exists_unlimited_le. |
| Section 11.4 (cofinite subsets of N are external) | proved | `Goldblatt.isExternal_image_natCast_of_finite_compl` |  |
| Section 11.5 (R has no least upper bound in *R) | proved | `Goldblatt.not_exists_isLUB_range_coe` | With upperBounds_range_coe (upper bounds of R are the positive unlimited numbers). |
| Theorem 11.5.1 | proved | `Goldblatt.IsInternal.exists_isLUB` | Lower-bound half IsInternal.exists_isGLB; lub[A_n] = [lub A_n] as isLUB_internalSet_ofSeq; key step ofSeq_mem_upperBounds_internalSet_iff. Second proof by the dagger transfer principle: IsInternal.exists_isLUB_of_transfer (new). |
| Exercise 11.5.2(i) | proved | `Goldblatt.IsInternal.exists_posUnlimited_mem` |  |
| Exercise 11.5.2(ii) | proved | `Goldblatt.IsInternal.subset_Icc_of_forall_limited` |  |
| Exercise 11.5.2(iii) | proved | `Goldblatt.IsInternal.exists_pos_limited_mem` |  |
| Exercise 11.5.2(iv) | proved | `Goldblatt.IsInternal.exists_posUnlimited_of_forall_not_limited` | Gives a positive unlimited b; common core IsInternal.exists_posUnlimited_lt. |
| Section 11.6 (unlimited hypernaturals are external) | proved | `Goldblatt.isExternal_unlimitedHyperNat` |  |
| Section 11.6 (N is external, via *N - N) | proved | `Goldblatt.isExternal_range_natCast'` | Second proof. |
| Section 11.6 (R is external) | proved | `Goldblatt.isExternal_range_coe` | Both proofs: via R ∩ *N = N, and isExternal_range_coe' via no least upper bound. |
| Section 11.6 (L is external; L is an intersection of internal intervals) | proved | `Goldblatt.isExternal_limitedSet` | limitedSet_eq_iInter_Ioo (over positive unlimited b; the book's 'unlimited' corrected); exists_iInter_isInternal_isExternal. |
| Section 11.6 (internal X ⊇ L contains [-b, b] with b unlimited) | proved | `Goldblatt.IsInternal.exists_posUnlimited_Icc_subset` | Also IsInternal.exists_unlimited_mem_of_limitedSet_subset. |
| Section 11.6 (infinitesimals, halos and half-halos are external) | proved | `Goldblatt.isExternal_infinitesimalSet` | isExternal_hal (any hyperreal centre), isExternal_hal_inter_Ioi, isExternal_hal_inter_Iio, isExternal_setOf_pos_infinitesimal, isExternal_setOf_neg_infinitesimal. |
| Section 11.6 (internal subset of I lies in [-c, c] with c infinitesimal) | proved | `Goldblatt.IsInternal.subset_Icc_of_forall_infinitesimal` | With infinitesimal_of_isLUB and infinitesimal_of_isGLB, which hold for any nonempty set of infinitesimals that has the bound. |
| Exercise 11.6.1 | proved | `Goldblatt.isExternal_image_coe_Ioi_zero` | All seven sets: positive reals, isExternal_range_intCast, isExternal_range_ratCast, isExternal_setOf_unlimited, isExternal_setOf_posUnlimited, isExternal_setOf_negUnlimited, isExternal_setOf_appreciable. |
| Section 11.7 (equivalence of (i) and (ii)) | proved | `Goldblatt.IFormula.starRealize_ofSeq` | For the deep embedding IFormula α k (atoms: sequences of k-ary relations; not, and, all; derived or, imp, ex, and now falsum and finite disjunction disj with starRealize_falsum / starRealize_disj). Atoms mem, rel₂, star (bridged to Ch03 starRel), relTerms, memMap, rel₂Map. Sentence forms starRealize_sentence, IFormula.starRealize_of_forall_realize. With set symbols: SFormula.starRealize_internalSet_ofSeq. New: internalRel_eq (equality is the internal relation of standard equality). |
| Section 11.7 transfer principle (†) | proved | `Goldblatt.SFormula.starRealize_of_forall_realize` | Language SFormula α m k with m set symbols (subst, realize, starRealize). If Φ holds for all tuples of standard sets (at every index, for all standard values of the free variables) then its transform holds for all tuples of internal sets; the book's statement is m = 1, k = 0. Worked examples: both sentences the book discusses, IsInternal.exists_isLeast_of_transfer and IsInternal.exists_isLUB_of_transfer. |
| Section 11.7 second example sentence (order-completeness by transfer) | proved | `Goldblatt.IsInternal.exists_isLUB_of_transfer` | New. Derived from the dagger principle with an SFormula sentence. The sentence as printed in the book is false for the empty set, so the dagger principle does not apply to it literally; the antecedent carries the extra conjunct 'A is nonempty', documented in the docstring. The standard-side proof uses completeness of the reals (sSup), which the book assumes. |
| Theorem 11.7.1 (Internal Set Definition Principle) | proved | `Goldblatt.SFormula.isInternalSet_setOf_starRealize` | New: the book's literal shape, for a formula with set symbols read as arbitrary internal sets X_1..X_m and parameters c_1..c_k; application form SFormula.isInternalSet_of_forall_iff. It reduces to the version over internal relations IFormula.isInternalSet_setOf_starRealize (with defining sequence IFormula.setOf_starRealize_eq_internalSet, application form IFormula.isInternalSet_of_forall_iff). Direct working versions: forall_star_iff, exists_star_iff, hyperreal_forall_iff, hyperreal_exists_iff; binary internalRel with internalRel_ofSeq, setOf_internalRel_ofSeq, setOf_exists/forall(_mem)_internalRel, not_internalRel, internalRel_and/or. |
| Section 11.7 first example after the principle (finite sets via x0 = x1 ∨ ... ∨ x0 = xn) | proved | `Goldblatt.isInternalSet_range_of_definition` | New. The formula is the genuine finite disjunction IFormula.disj of the atoms x_0 = x_i (rel₂ with equality), generic over StarType; corollaries isInternalSet_of_finite_of_definition and isInternal_of_finite_of_definition. |
| Section 11.7 second example after the principle (open intervals) | proved | `Goldblatt.isInternal_Ioo_of_definition` | Ioo derived through IFormula; quantified example IsInternal.isInternal_setOf_Ioo_subset (the formula discussed before the principle). |
| Section 11.7 (every infinite set of reals is external) | proved | `Goldblatt.finite_of_isInternal_image_coe` | Book's proof; the set {n in *N : *f(n) in X} is obtained from the definition principle (atom IFormula.memMap). isExternal_image_coe_of_infinite, isInternal_image_coe_iff. |
| Exercise 11.7.1 | proved | `Goldblatt.isInternal_Icc_of_definition` | By the internal set definition principle, as the exercise asks: isInternal_Ioc/Ico/Icc/Ioi/Ici/Iio/Iic_of_definition, isInternal_setOf_hyperNat_one_le_le_of_definition, isInternal_setOf_div_hyperNat_of_definition (ternary atom with a function symbol, bridged by starRealize_eq_div). |
| Theorem 11.8.1 | proved | `Goldblatt.IsInternal.underflow` | Book's proof; the definable set IsInternal.isInternal_setOf_segment_subset is derived through IFormula.isInternalSet_of_forall_iff with the book's formula; no X ⊆ *N hypothesis. |
| Exercise 11.8.2 | proved | `Goldblatt.underflowPrinciple_iff_smallUnlimitedPrinciple` | Class-level equivalence (UnderflowPrinciple, SmallUnlimitedPrinciple); IsInternal.exists_unlimited_le_mem; deduction exists_unlimited_mem_starSet_le for infinite A ⊆ N. |
| Section 11.9 (a set defined by a transformed formula is never a halo) | proved | `Goldblatt.IFormula.setOf_starRealize_ne_hal` | New. Also SFormula.setOf_starRealize_ne_hal (set symbols read as internal sets) and the permanence form IFormula.exists_starRealize_not_mem_hal (a definable property holding on a whole halo holds somewhere outside it). The book's case is one free variable and no parameters (k = 0). |
| Section 11.9 (remaining discussion of permanence) | prose |  | Exposition relating overflow, underflow, spillover and universal transfer; each of those is a separate proved item. |
| Theorem 11.9.1 | proved | `Goldblatt.IsInternal.exists_real_ball_subset` | Via underflow, as in the book; the definable set IsInternal.isInternal_setOf_ball_subset is derived through IFormula with the atom \|z - y\| < 1/x (starRealize_abs_sub_lt_one_div). |
| Theorem 11.10.1 | proved | `Goldblatt.iInter_nonempty_of_isInternalSet` | Book's diagonal argument (iInter_internalSet_nonempty), generic over StarType; hyperreal form iInter_nonempty_of_isInternal. |
| Corollary 11.10.2(1) | proved | `Goldblatt.iInter_nonempty_of_fip` | FIP stated over finsets of indices. |
| Corollary 11.10.2(2) | proved | `Goldblatt.IsInternalSet.exists_subset_biUnion_le` |  |
| Corollary 11.10.2(3) | proved | `Goldblatt.IsInternalSet.exists_biInter_le_subset` |  |
| Corollary 11.10.2(4) | proved | `Goldblatt.exists_iUnion_eq_biUnion_le` |  |
| Corollary 11.10.2(5) | proved | `Goldblatt.exists_iInter_eq_biInter_le` |  |
| Exercise 11.10.3 | proved | `Goldblatt.not_isInternalSet_iUnion_of_ssubset_succ` | Strictly increasing unions and strictly decreasing intersections (not_isInternalSet_iInter_of_ssubset_succ) are external. The exercise's claim about the union of a strictly decreasing sequence is false (the union is the first term, isInternalSet_iUnion_of_antitone); the correction is recorded in the docstrings. |
| Section 11.11 (saturation gives positive infinitesimals; bounds for sequences) | proved | `Goldblatt.exists_posInfinitesimal_of_saturation` | iInter_Ioo_zero_one_div (intervals (0, 1/(n+1)), 0-based); exists_infinitesimal_upper_bound, exists_unlimited_hyperNat_lower_bound. |
| Exercise 11.11.1 | proved | `Goldblatt.exists_posUnlimited_of_saturation` | Also exists_negUnlimited_of_saturation. |
| Exercise 11.11.2 | proved | `Goldblatt.unlimited_lower_bound_of_infinitesimal_upper_bound` | Both halves, with the pointwise constructions hfloor_inv_unlimited_lower_bound and inv_infinitesimal_upper_bound; second half infinitesimal_upper_bound_of_unlimited_lower_bound. |
| Section 11.12 (an internal set is finite or uncountable) | proved | `Goldblatt.IsInternalSet.finite_or_not_countable` | IsInternalSet.finite_of_countable, not_countable_of_infinite, finite_of_isInternalSet_image_of, not_countable_setOf_hyperNat_le, not_countable_setOf_unlimited_hyperNat_le, not_countable_image_natGalaxy. |
| Theorem 11.13.1 | proved | `Goldblatt.IsInternal.isClosed_shSet` | shSet, mem_shSet_iff, examples shSet_Ioo_of_limited and shSet_Ioo_of_posUnlimited, first step exists_mem_Ioo_of_mem_closure_shSet. |
| Exercise 11.13.2 | proved | `Goldblatt.IsInternal.isClosed_shSet_of_overflow` | Proof by overflow, with the definable set IsInternal.isInternal_setOf_ball_inter_nonempty obtained from the definition principle. |
| Section 11.14 definitions (hyper-open sets; Section 10.5 notions recalled) | proved | `Goldblatt.HyperOpen` | hyperOpen_internalSet_iff, HyperOpen.isInternal, hyperOpen_Ioo. IntervalOpen, RealOpen, sNhd, SOpen are local restatements in Goldblatt.HyperTopology because Ch11 may not import Ch10 (no Ch10 file exists yet); to be bridged when Ch10 lands. |
| Lemma 11.14.1 | proved | `Goldblatt.HyperOpen.intervalOpen` |  |
| Section 11.14 (L is interval-open but not hyper-open; hyper-open sets are a base of the interval topology) | proved | `Goldblatt.intervalOpen_iff_sUnion_hyperOpen` | New base theorem: a set is interval-open iff it is a union of hyper-open sets. Also limitedSet_eq_iUnion_Ioo, intervalOpen_limitedSet, not_hyperOpen_limitedSet (docstring now cites the base theorem), sOpen_limitedSet, realOpen_limitedSet, not_realOpen_Ioo_of_infinitesimal. |
| Exercise 11.14.2 | proved | `Goldblatt.hyperOpen_biUnion_finset` | HyperOpen.union, hyperOpen_empty. |
| Exercise 11.14.3 | proved | `Goldblatt.internalSet_interior_eq_sUnion` | hyperOpen_internalSet_interior, internalSet_interior_subset, HyperTopology.IntervalOpen.subset_internalSet_interior; deduction IsInternal.intervalOpen_iff_hyperOpen. |
| Theorem 11.14.4 | proved | `Goldblatt.IsInternal.sOpen_iff_forall_hal_subset` | Easy direction HyperTopology.SOpen.hal_subset holds without internality. |
| Review finding 4 (helper lemmas in the root namespace; HyperTopology restatements) | proved | `Goldblatt.PosUnlimited.hfloor` | Not changed; cannot be fixed inside Ch11's edit scope. PosUnlimited.sub_one, PosUnlimited.of_le, PosUnlimited.min, Limited.lt_posUnlimited, negUnlimited_neg_iff, posUnlimited_of_not_limited_of_nonneg, PosUnlimited.hfloor are Chapter-5-style facts in namespace Goldblatt. No other module declares these names today. protected would not prevent a clash and private would break cross-submodule use. Orchestrator: move them to Ch05 in a coordinated edit and record the pending Ch10 bridge in COVERAGE.md (which does not exist yet). |

## 12. Internal Functions and Hyperfinite Sets

| Book item | Status | Lean declaration | Note |
|---|---|---|---|
| Section 12.1 definition (internal function [f_n]) | proved | `Goldblatt.internalPFun` | Sequence of Mathlib PFun's gives a PFun on star types; graph InternalGraph, criterion ofSeq_mem_internalPFun, well-definedness InternalGraph.unique. Total version internalMap with internalMap_ofSeq and internalPFun_coe. |
| Section 12.1 (dom [f_n] = [dom f_n]) | proved | `Goldblatt.dom_internalPFun` | Also ofSeq_mem_dom_internalPFun and IsInternalPFun.isInternalSet_dom. |
| Section 12.1 definition (internal function predicate) | proved | `Goldblatt.IsInternalPFun` | Explicit underlying types; abbreviation IsInternalFun for hyperreal partial functions. |
| Section 12.1 (constant sequence gives *f) | proved | `Goldblatt.internalMap_const` | Total-function case (Section 3.11 extension); docstring now says so and points to the book's partial case (Section 3.13): starMapOn_mem_internalPFun_const and mem_internalPFun_const_res. Also isInternalPFun_starMap. |
| Theorem 12.1.1 | proved | `Goldblatt.internalPFun_eq_iff` | [f_n] = [g_n] iff f_n = g_n for almost all n. Corollaries internalPFun_congr, internalPFun_ne_iff, internalPFun_exists_rep_forall. |
| Exercise 12.2(1) | proved | `Goldblatt.image_internalPFun` | [f_n]([A_n]) = [f_n(A_n)] without the domain hypothesis. Also IsInternalPFun.isInternalSet_image, ran_internalPFun, image_internalMap, IsInternalSet.image_starMap. |
| Exercise 12.2(2) | proved | `Goldblatt.preimage_internalPFun` | Also IsInternalPFun.isInternalSet_preimage. |
| Exercise 12.2(3) | proved | `Goldblatt.comp_internalPFun` | [g_n] ∘ [f_n] = [g_n ∘ f_n], no range hypothesis needed; IsInternalPFun.comp. Extra: prestrict_internalPFun (restriction to an internal set). |
| Exercise 12.2(4) | proved | `Goldblatt.pinjective_internalPFun_iff` | Injectivity of partial functions is the new def PInjective; total version injective_internalMap_iff. |
| Exercise 12.2(5) | proved | `Goldblatt.pinv_internalPFun` | Inverse pinv (def), mem_pinv, PInjective.pinv, IsInternalPFun.pinv. |
| Exercise 12.2(6) | proved | `Goldblatt.padd_internalPFun` | Also pmul_internalPFun and map_mul_left_internalPFun; closure statements IsInternalPFun.padd, .pmul, .map_mul_left. Sum and product are defined on the intersection of the domains. |
| Exercise 12.2(7) | proved | `Goldblatt.IsInternalPFun.exists_isLUB_ran_infinitesimal` | Hypothesis that the domain is nonempty added (the empty set has no least upper bound). |
| Exercise 12.2(8) | proved | `Goldblatt.isExternal_image_coe_of_infinite_of_image` | Alternative proof via Exercise 12.2(1): map the infinite set onto N by a real function. |
| Section 12.3 definition (hyperfinite set) | proved | `Goldblatt.IsHyperfiniteSet` | Abbreviation IsHyperfinite for sets of hyperreals. isHyperfiniteSet_internalSet_iff, not_isHyperfiniteSet_internalSet_iff, exists_rep_finite, isHyperfiniteSet_iff_exists_finset. |
| Section 12.3 definition (internal cardinality) | proved | `Goldblatt.internalCard` | Abbreviation hcard. internalCard_internalSet: \|[A_n]\| = [\|A_n\|] (via Set.ncard) for any defining sequence; internalCard_mem_hyperNat, internalCard_empty, internalCard_singleton. |
| Section 12.3 example 1 ([{1..n}] contains N, uncountable) | proved | `Goldblatt.hcard_setOf_hyperNat_one_le_le_omega` | Also natCast_mem_setOf_hyperNat_one_le_le and not_countable_setOf_hyperNat_one_le_le for any unlimited N. |
| Section 12.3 example 2 (countable B has hyperfinite A with B ⊆ A ⊆ *B) | proved | `Goldblatt.exists_isHyperfiniteSet_between` | Real version exists_isHyperfinite_between. Correction to the book (documented): the unconditional 'internal size ω' needs an enumeration without repetitions (fails for finite B); proved under Function.Injective as internalCard_internalSet_image_Iio. |
| Section 12.3 example 3 (finite sets are hyperfinite) | proved | `Goldblatt.isHyperfiniteSet_of_finite` | Also internalCard_of_finite (= ncard). Extra: IsHyperfiniteSet.finite_iff_limited_internalCard and finite_or_not_countable. |
| Section 12.3 example 4 ({1,...,N} hyperfinite of size N) | proved | `Goldblatt.hcard_setOf_hyperNat_one_le_le` | With isHyperfinite_setOf_hyperNat_one_le_le; from 0: isHyperfinite_setOf_hyperNat_le, hcard_setOf_hyperNat_le (= N+1). |
| Section 12.3 example 5 ({0,1/N,...,1} hyperfinite of size N+1) | proved | `Goldblatt.hcard_setOf_div_hyperNat` | With isHyperfinite_setOf_div_hyperNat. Indexed by hypernaturals k ≤ N, equivalent to the book's hyperintegers 0 ≤ k ≤ N; both docstrings now say so. |
| Section 12.3 example 6 (uniform partition of [a,b]) | proved | `Goldblatt.hcard_setOf_uniform_partition` | Hyperfiniteness (isHyperfinite_setOf_uniform_partition) holds for all a, b; the count N+1 needs a ≠ b, a correction to the book. |
| Exercise 12.4(1) | proved | `Goldblatt.IsHyperfinite.exists_isGreatest` | And IsHyperfinite.exists_isLeast; nonemptiness hypothesis added. |
| Exercise 12.4(2) | proved | `Goldblatt.internalCard_union` | IsHyperfiniteSet.union, .inter, internalCard_union_add_internalCard_inter, internalCard_union_of_disjoint. |
| Exercise 12.4(3) | proved | `Goldblatt.IsHyperfiniteSet.subset` | Plus internalCard_le_of_subset, internalCard_lt_of_ssubset, IsHyperfiniteSet.diff, internalCard_diff. |
| Theorem 12.5.1 | proved | `Goldblatt.isHyperfiniteSet_and_internalCard_eq_iff` | Hyperfinite with internal cardinality N iff there is an injective internal function with domain {1..N} and range the set. The book's hypothesis that the set is internal is dropped. Existential form isHyperfiniteSet_iff_exists_internal_bijection. |
| Theorem 12.6.1 | proved | `Goldblatt.isHyperfiniteSet_iff_pigeonhole` | Forward direction separately as IsHyperfiniteSet.image_eq_of_pinjective. |
| Section 12.6 example (non-internal function) | proved | `Goldblatt.not_isInternalFun_doubleStandard` | doubleStandard doubles standard naturals and fixes nonstandard hypernaturals. The book applies the pigeonhole principle to *N, which is not hyperfinite; the proof uses {0..ω}. |
| Section 12.7 definition (hyperfinite sum) | proved | `Goldblatt.internalSum` | Abbreviation hsum. internalSum_internalPFun gives the class of the sequence of sums for any defining sequences; Finset and total-function forms internalSum_internalPFun_finset, internalSum_internalMap, internalSum_internalMap_finset. Partial functions count as 0 off their domain (pval). |
| Section 12.7 property 1 (Σ c f = c Σ f) | proved | `Goldblatt.internalSum_map_mul_left` | Also internalSum_map_mul_right. |
| Section 12.7 property 2 (Σ (f+g) = Σ f + Σ g) | proved | `Goldblatt.internalSum_padd` | Requires the set to lie in both domains. |
| Section 12.7 property 3 (disjoint union) | proved | `Goldblatt.internalSum_union` |  |
| Section 12.7 property 4 (monotonicity) | proved | `Goldblatt.internalSum_le_internalSum` | Extra: internalSum_one (sum of the constant 1 is the internal cardinality), internalSum_empty. |
| Section 12.7 / Section 9.1 (partition P_Δx and ordinary Riemann sum S_a^b(f,Δx)) | proved | `Goldblatt.riemannSum` | Section 9.1 definitions placed in Ch12 provisionally (Ch09 not importable). RENAMED this round to avoid the clash with Ch07's n-part partition: widthPartitionCard, widthPartitionPoint (and lemmas widthPartitionPoint_zero, _of_lt, widthPartitionPoint_widthPartitionCard, _le_succ, le_widthPartitionPoint, widthPartitionPoint_le, _succ_sub_le, lt_widthPartitionCard_iff). Verified that Ch07 and Ch12 import together. Orchestrator: Ch09 must reuse these names or bridge to them. |
| Section 12.7 (hyperfinite partition P = [P_n], size N) | proved | `Goldblatt.hpartition` | hpartition_eq_internalSet, hpartition_eq_internalSet_finset, isHyperfinite_hpartition, hcard_hpartition, unlimited_hcard_hpartition. |
| Section 12.7 (S(f,Δx) = Σ_{x∈P} f(x)Δx) | proved | `Goldblatt.infClose_starMap_riemannSum_hsum_mul` | Corrected: the book's equality holds only up to an infinitesimal (last subinterval width). Stated for any f bounded on [a,b]; standard estimate abs_uniformSum_sub_riemannSum_le. Exact identities: starMap_uniformSum_eq_hsum_mul, hsum_starMap_mul_hpartition, hsum_starMap_hpartition. |
| Section 12.7 final theorem (integral = sh of hyperfinite Riemann sum, f Riemann integrable), general form | proved | `Goldblatt.RiemannSumsConverge.eq_sh_hsum_hpartition` | CONDITIONAL ON CHAPTER 9; record in COVERAGE as 'proved (continuous case); general case conditional on Ch09: integrable => bounded and RiemannSumsConverge', not plain proved. The Lean theorem itself is fully proved (standard axioms only) but takes boundedness on [a,b] and RiemannSumsConverge f a b I as hypotheses instead of Riemann integrability. Its first conjunct restates hI via riemannSumsConverge_iff_forall_infClose; the Ch12 content is the hsum conjunct. The book's integrable-f statement is not yet unconditionally proved; when Ch09 lands, add the corollary RiemannIntegrable f a b -> integral = sh(hsum ...) there or in a bridge module. Supporting: RiemannSumsConverge (def), .infClose_starMap_riemannSum, .infClose_hsum_hpartition, .unique. |
| Section 12.7 final theorem, continuous case | proved | `Goldblatt.integral_eq_sh_hsum_hpartition` | Unconditional for f continuous on [a,b] with Mathlib's interval integral, as a corollary of the general form via riemannSumsConverge_integral_of_continuousOn (standard fact abs_riemannSum_sub_integral_lt) and exists_abs_le_of_continuousOn_Icc. Also infClose_starMap_riemannSum_integral, infClose_hsum_hpartition_integral. Non-vacuity: sh_hsum_id_epsilon (= 1/2). |
| Exercise 12.7.1 | proved | `Goldblatt.hpartition_eq_setOf_lt_hcard` | P = {a + kΔx : k hypernatural, k < N}; membership form exists_lt_hcard_of_mem_hpartition. |

## 13. Universes and Frameworks

| Book item | Status | Lean declaration | Note |
|---|---|---|---|
| Section 13.1 (subset and relation closure) | proved | `Goldblatt.IsUniverse.isSetOf_of_subset` | Also IsUniverse.isSetOf_of_subset_prod. The rest of 13.1 is a wish list (prose). |
| Section 13.2 definitions (functions, tuples, relations, products) | proved | `Goldblatt.tuple` | IsRel, IsFunction, isFunc_iff, app, dom, ran, relImage, relPreimage, relInv, relComp, tupleProd, IsRelN, num, IsInjective. A 2-tuple is the pair; other lengths are functions on numerals. |
| Exercise 13.3.1(i) | mathlib | `Goldblatt.kuratowski_pair_eq_iff` | Direct alias of ZFSet.pair_inj. |
| Exercise 13.3.1(ii) | proved | `Goldblatt.tuple_eq_iff` | Proved for every m, not only m >= 2. |
| Section 13.3 product closure | proved | `Goldblatt.IsUniverse.isSetOf_prod` | Via A x B inside PP(A u B), as in the book. |
| Section 13.4 definition (strong transitivity) | proved | `Goldblatt.StronglyTransitive` | With TransitiveIn, IsIndividual, IsSetOf; StronglyTransitive.subset. The remark that B inside U is superfluous in a transitive U, and the transitive closure Tr(A), are prose only. |
| Section 13.5 definition (universe, universe over X) | proved | `Goldblatt.IsUniverse` | IsUniverse and IsUniverseOver are structures with the book's axioms. 'Contains the positive integers' is a theorem (IsUniverse.isSetOf_num). |
| Section 13.5 set theory closure list (8 items) | proved | `Goldblatt.IsUniverse.isSetOf_sUnion_of_subset` | isSetOf_singleton, isSetOf_iUnion_fin, isSetOf_of_finite, isSetOf_of_subset, isSetOf_empty, isSetOf_sUnion_of_subset, isSetOf_sUnion, isSetOf_sInter, plus inter/sdiff/sep. |
| Section 13.5 relations and functions closure list (9 items) | proved | `Goldblatt.IsUniverse.isSetOf_funs` | isSetOf_opair, isSetOf_of_subset_prod, isSetOf_tuple, isSetOf_tupleProd, isSetOf_dom / ran / relImage / relInv, isSetOf_relComp, isSetOf_of_isFunc, isSetOf_funs, isSetOf_piSet. Relations in U carry the hypothesis RelIn U R. |
| Section 13.6 definitions (cumulative power sets, superstructure, rank) | proved | `Goldblatt.superstructure` | cumPow, superstructure, rank, mem_cumPow_iff_rank_le, rank_eq_zero_iff, IsBaseSet; new rank_le_of_mem_cumPow, mem_cumPow_rank. |
| Section 13.6 (1)-(6) / Exercise 13.6.1 | proved | `Goldblatt.cumPow_succ_eq` | cumPow_succ_eq, cumPow_mem_succ, mem_cumPow_of_mem_of_mem_succ / transitiveIn_cumPow_succ, pair_mem_cumPow_succ, union_mem_cumPow, powerset_mem_cumPow. Set hypotheses are written as 'not in X'. |
| Section 13.6 theorem: superstructure is a universe over X | proved | `Goldblatt.isUniverseOver_superstructure` | Under IsBaseSet X. |
| Section 13.6 minimality / Exercise 13.6.1 | proved | `Goldblatt.superstructure_subset_of_isUniverse` | Also superstructure_subset_of_closed, superstructure_mono, mem_superstructure_iff_exists_subset_cumPow, superstructure_notMem_self. |
| Section 13.6 existence of universes | proved | `Goldblatt.exists_isUniverseOver` | exists_isBaseSet: every type embeds in ZFSet as a base set. |
| Section 13.6 rank remarks, upper bounds (relations, topologies, measures, X x X, metrics, Riemann integral) | proved | `Goldblatt.mem_cumPow_of_subset_prod` | mem_cumPow_two_of_subset_powerset, mem_cumPow_three_of_subset_powerset_powerset, mem_cumPow_four_of_subset_prod_powerset, mem_cumPow_five_of_measures, prod_base_mem_cumPow_three, mem_cumPow_five_of_subset_prod_prod, mem_cumPow_six_of_metrics, mem_cumPow_six_of_integral. Membership in U_n, i.e. rank <= n; each docstring now says the book states equality and points to the exact theorem. |
| Section 13.6 rank remarks, exact ranks (X x X rank 3; topology 2; set of topologies 3; measure 4; set of measures 5; metric 5; set of metrics 6; integrable function 3, their set 4, integral 6) | proved | `Goldblatt.IsBaseSet.rank_prod_base` | NEW in this pass. rank_lt_of_mem, rank_eq_succ, IsBaseSet.rank_of_subset (=1), IsBaseSet.rank_pair (= max of the two ranks + 2), rank_pair_base (=2), rank_prod_base (=3, X nonempty), rank_of_subset_powerset (=2, nonempty), rank_of_subset_powerset_powerset (=3), rank_of_subset_prod, rank_measure (=4, nonempty), rank_measures (=5), rank_metric (=5, nonempty), rank_metrics (=6), rank_integral (3/4/6). Nondegeneracy hypotheses (nonempty) are necessary: the book's equalities fail for empty relations. |
| Section 13.7 definitions (terms, formulas, truth, sentences) | proved | `Goldblatt.Formula` | Term, Term.val, Term.Defined, Formula, Sat, Formula.IsSentence, Formula.Holds, sat_congr, holds_iff_sat. Undefined terms make atomic formulas false (the book restricts to defined sentences). |
| Section 13.7 defined sentences (definedness is bounded) | proved | `Goldblatt.Term.sat_definedF` | Term.BoundedBy, Term.definedF, Formula.conjFin, Formula.verum. For a term whose function parts are subsets of T x T, a bounded formula holds iff the term is defined. |
| Section 13.8 definition (transform, nonstandard framework) | proved | `Goldblatt.NonstandardFramework` | Term.star, Formula.star, IsSentence.star; structure fields are the book's axioms, except that transfer quantifies over all sentences of the deep embedding and so is stronger than the book's defined-sentence transfer. The field docstring now says explicitly that Chapter 14 must prove the field as stated (Los theorem for Sat including Term.Defined clauses) and that no reduction lemma exists. Constructor ofDefinedTransfer NOT built (documentation option of the finding taken). Non-vacuity: NonstandardFramework.trivial. |
| Section 13.8 transfer-map list / Exercise 13.8.1 | proved | `Goldblatt.NonstandardFramework.star_relComp` | star_eq_iff / star_injOn, star_mem_star_iff, star_subset_star_iff, subset_star_of_subset_base, star_inter / union / sdiff, star_singleton / pair / mem_star_of_finite, isIndividual_of_mem_star_base, transitiveIn_star, star_powerset_subset, star_prod / star_tupleProd, star_dom / ran / relInv / relImage / relPreimage, star_relComp, isFunc_star / star_app / isInjective_star_iff / ran_star_eq_iff, star_opair, star_tuple, star_num. |
| Exercise 13.8.2 | proved | `Goldblatt.NonstandardFramework.mem_star_sep_tuple` | General m = k+2 with factors A_i; mem_star_sep is the one-variable case. |
| Section 13.8 operations on R as entities | proved | `Goldblatt.RealFramework.hop_real` | Sums.lean (part 7): toReal, binFn, isFunc_binFn, isFunc_star_binFn, hop / hadd / hmul, hop_mem, hop_real, R_subset_star, star_N_subset_star_R. |
| Section 13.8 example f(r) = {x > r} | proved | `Goldblatt.RealFramework.app_star_rayFn` | upperRay, rayFn, star_upperRay, app_star_rayFn, app_star_rayFn_ne. The inequality is proved under the hypothesis that a nonstandard hypernatural exists. |
| Section 13.9 definitions (standard, nonstandard, image) | proved | `Goldblatt.NonstandardFramework.Standard` | Standard, Nonstandard, im, standard_of_mem_base, mem_of_standard_of_mem_star, nonstandard_of_mem_star_sdiff, im_subset_star, bijOn_star_im, im_eq_of_subset_base, star_eq_im_of_finite. |
| Section 13.9 the sets R and N | proved | `Goldblatt.RealFramework.N` | RealFramework adds an injection of the reals into X. N is the image of Lean's naturals and starts at 0 (book: 1); the docstring of N now warns later chapters. |
| Section 13.9 initial segments example | proved | `Goldblatt.RealFramework.not_standard_seg` | seg (lower bound 1 written explicitly), internal_seg, seg_mem_star_powerset, nat_le_of_nonstandard, not_standard_seg. |
| Section 13.9 intervals example | proved | `Goldblatt.RealFramework.mem_star_Int` | star_ooIn and mem_star_Int. |
| Exercise 13.9.1 | proved | `Goldblatt.RealFramework.standard_mem_star_Int_iff` |  |
| Theorem 13.9.2 | proved | `Goldblatt.NonstandardFramework.mem_im_iff` | Also mem_star_sdiff_im_iff. |
| Exercise 13.9.3 | proved | `Goldblatt.NonstandardFramework.star_eq_star_of_standard_mem` |  |
| Section 13.10 definition (internal, external) | proved | `Goldblatt.NonstandardFramework.Internal` | Internal, External, internal_star, internal_of_standard. |
| Theorem 13.10.1 | proved | `Goldblatt.NonstandardFramework.exists_transitive_of_internal` | Three parts: exists_transitive_of_internal, exists_transitive_superset_of_internal, internal_of_mem_internal(_set). |
| Section 13.10 examples (segments, hyperreal intervals) | proved | `Goldblatt.RealFramework.internal_ooIn` | internal_ooIn, internal_seg. |
| Section 13.10 uniform partition example | proved | `Goldblatt.RealFramework.partition_mem_star_powerset` | partFn, partition, partition_mem_star_powerset, internal_partition. One function of the universe computes the partition points; k ranges over hypernaturals <= n. Docstring of partition now notes that n = 0 is allowed and gives {a} by the division-by-zero convention. |
| Section 13.11 closure properties / Exercise 13.11.1 | proved | `Goldblatt.NonstandardFramework.internal_union` | internal_inter / union / sdiff / prod, internal_sUnion / sInter, internal_singleton / insert / of_finite / opair / tuple, internal_dom / ran / relInv / relImage, internal_relComp, internal_app / image / relPreimage. |
| Theorem 13.12.1 | proved | `Goldblatt.NonstandardFramework.mem_star_powerset_iff` | The transferred sentence carries the extra clause 'x is a set'. Also im_powerset_subset and mem_im_powerset_iff. |
| Section 13.12 internal least number principle, N external | proved | `Goldblatt.RealFramework.internal_least` | internal_least, not_internal_N, external_N (under existence of a nonstandard hypernatural). |
| Exercise 13.13(1) | proved | `Goldblatt.RealFramework.internal_induction` | internal_induction and internal_order_complete. Base case is F.nat 0 because N starts at 0; now stated in the docstring. |
| Exercise 13.13(2) | proved | `Goldblatt.NonstandardFramework.bijOn_chi_star` | bijOn_chi and bijOn_chi_star; 0 and 1 are the numerals. |
| Exercise 13.13(3) | proved | `Goldblatt.NonstandardFramework.mem_star_funs_iff` |  |
| Theorem 13.14.1 | proved | `Goldblatt.RealFramework.not_internal_im` | Hypothesis: a nonstandard hypernatural exists (the book's standing assumption). Also external_im, exists_nonstandard_mem_star, im_mem_powerset_star_sdiff. |
| Exercise 13.14.2 | proved | `Goldblatt.RealFramework.relPreimage_star_im_ran` | Helper im_inter_star. |
| Exercise 13.14.3 | proved | `Goldblatt.NonstandardFramework.star_powerset_eq_of_finite` |  |
| Section 13.15 internal set definition principle | proved | `Goldblatt.NonstandardFramework.internal_sep_of_internal_consts` | Parameter form internal_sep (used in applications) and the book's form with internal constants. |
| Section 13.15 illustration (uniform partition by definition) | proved | `Goldblatt.RealFramework.internal_partition_of_definition` | In Sums.lean (part 7). |
| Section 13.16 internal function definition principle | proved | `Goldblatt.NonstandardFramework.internal_of_term_of_internal_consts` | Parameter form internal_of_term and the book's form. |
| Section 13.16 illustration (partition as range of an internal function) | proved | `Goldblatt.RealFramework.partition_eq_ran_internal` | In Sums.lean (part 7). |
| Section 13.17 definitions (finite power set, hyperfinite) | proved | `Goldblatt.NonstandardFramework.Hyperfinite` | Now in the new submodule Goldblatt.Ch13_Universes.HyperfiniteSets (part 6). finPow, mem_finPow, IsUniverse.isSetOf_finPow, star_finPow_subset, internal_subset_of_mem_star_finPow, Hyperfinite.internal / isSetOf / mem_star_finPow. |
| Theorem 13.17.1 | proved | `Goldblatt.RealFramework.hyperfinite_iff` | Hyperfinite iff internal bijection with an initial segment {1..n}. The transferred sentence carries the clause 'x is empty or has a member' in its second half. Helpers BijSpec, bijFormula, bijSpec_iff. |
| Section 13.17 examples and internal cardinality | proved | `Goldblatt.RealFramework.icard` | hyperfinite_seg, infinite_seg, cardFn, isFunc_star_cardFn, icard_mem, icard_star, icard_eq_of_bijection, icard_seg. |
| Exercise 13.18 (1) | proved | `Goldblatt.RealFramework.le_of_internal_injection` | le_of_internal_injection and eq_of_internal_bijection. |
| Exercise 13.18 (2) | proved | `Goldblatt.NonstandardFramework.Hyperfinite.of_internal_subset` | First part of_internal_subset (proved in the 13.17 section because later proofs use it); second part RealFramework.icard_le_of_subset. |
| Exercise 13.18 (3) | proved | `Goldblatt.RealFramework.exists_greatest_least` | With 'nonempty' added (the book's statement is false for the empty set). |
| Exercise 13.18 (4) | proved | `Goldblatt.RealFramework.hyperfinite_internalPowerset` | internalPowerset, powFn; internal power set of a hyperfinite set is hyperfinite of internal size 2^\|A\|; also hyperfinite_internalPowerset'. |
| Exercise 13.18 (5) | proved | `Goldblatt.RealFramework.hyperfinite_iff_surjection` |  |
| Exercise 13.18 (6) | proved | `Goldblatt.NonstandardFramework.Hyperfinite.relImage` | Proved in the 13.17 section. |
| Section 13.19 sum of a hyperfinite set | proved | `Goldblatt.RealFramework.hsum` | sumFn, hsum, hsum_mem, hsum_of_finite. |
| Section 13.19 sum of an internal function over a hyperfinite set | proved | `Goldblatt.RealFramework.hfsum` | Correction to the book: the book defines the sum as the sum of the set f(B), which is right only for f injective on B. hfsum transfers the summation operator on pairs (function, finite set); hfsum_mem, hfsum_star, hfsum_mono_ambient, hfsum_ambient_irrel; the book's formula is recovered in the injective case by hfsum_eq_hsum_relImage. |
| Exercise 13.20 (1) | proved | `Goldblatt.RealFramework.hfsum_add` | Four properties: hfsum_smul, hfsum_add, hfsum_union (disjoint), hfsum_le. |
| Exercise 13.20 (2) | proved | `Goldblatt.RealFramework.isum_succ` | isum, isum_mem, isum_zero, isum_succ, isum_nat (agrees with the ordinary finite sum for standard length). |

## 14. The Existence of Nonstandard Entities

| Book item | Status | Lean declaration | Note |
|---|---|---|---|
| Section 14.1 definition (finite intersection property) | proved | `Goldblatt.FIP` | Definition; finite subcollections are Finsets of ZFSet. |
| Section 14.1 definition (enlargement) | proved | `Goldblatt.NonstandardFramework.IsEnlargement` | Definition, attached to the framework. Docstring reworded in original terms this pass. |
| Section 14.1 chapter introduction (identity embedding has nothing new) | proved | `Goldblatt.NonstandardFramework.not_isEnlargement_trivial` | The trivial framework on a universe with an infinite set is not an enlargement. |
| Section 14.1 example 1 (positive infinitesimal from intervals (0,r)) | proved | `Goldblatt.RealFramework.exists_pos_infinitesimal` | Derived from posIntervals, fip_posIntervals and the characterization below. |
| Section 14.1 example 1 (the intersection of the *(0,r) is exactly the positive infinitesimals) | proved | `Goldblatt.RealFramework.forall_mem_star_posIntervals_iff` | Holds in every framework. |
| Section 14.1 example 1 variant (intervals (-r,r) minus {0}, nonzero infinitesimals) | proved | `Goldblatt.RealFramework.forall_mem_star_puncturedIntervals_iff` | With puncturedIntervals, fip_puncturedIntervals, exists_nonzero_infinitesimal. |
| Section 14.1 example 2 (any member of the intersection of the *(r,∞), r in R+, is a positive unlimited hyperreal) | proved | `Goldblatt.RealFramework.forall_mem_star_posRays_iff` | New. Collection RealFramework.posRays indexed by positive reals as in the book, isSetOf_posRays, fip_posRays; iff with b in *R and r < b for every real r (step from r > 0 to all r via (max r 1, ∞) ⊆ (r, ∞)). Holds in every framework. |
| Section 14.1 example 2 (existence of a positive unlimited hyperreal) | proved | `Goldblatt.RealFramework.exists_pos_unlimited` | Now derived from posRays / fip_posRays / forall_mem_star_posRays_iff. |
| Section 14.1 example 3 (infinite A has b in *A minus im A) | proved | `Goldblatt.NonstandardFramework.IsEnlargement.exists_mem_star_notMem_im` | Via the collection {A - {a}}. |
| Section 14.1 example 3 (every infinite standard set has a nonstandard member) | proved | `Goldblatt.NonstandardFramework.IsEnlargement.exists_nonstandard_mem_star` | Docstring reworded this pass. |
| Section 14.1 example 3 (infinite A ⊆ X is a proper subset of *A) | proved | `Goldblatt.NonstandardFramework.IsEnlargement.ssubset_star` | Stated as A ⊆ *A together with a member of *A not in A. |
| Section 14.1 example 3 for N (nonstandard hypernatural) | proved | `Goldblatt.RealFramework.exists_nonstandard_nat` | Discharges the hypothesis used throughout Ch13 (helper: RealFramework.infinite_N). |
| Section 14.1 example 4 (the collection {A_a : a in A} has the finite intersection property) | proved | `Goldblatt.fip_finSupersets` | New. Definition Goldblatt.finSupersets A a = {Z in P_F(A) : a in Z}, mem_finSupersets. |
| Section 14.1 example 4 (any B in the intersection of the *(A_a) is hyperfinite with im A ⊆ B ⊆ *A) | proved | `Goldblatt.NonstandardFramework.hyperfinite_of_forall_mem_star_finSupersets` | New. By transfer of (∀Z ∈ A_a)(a ∈ Z), in every framework. Hypothesis A ≠ ∅ added (for empty A the hypothesis is vacuous and the book's claim fails as stated); docstring says so. Conclusion: B ∈ *P_F(A), im A ⊆ B, B ⊆ *A, Hyperfinite B. |
| Section 14.1 example 4 (existence of hyperfinite B with im A ⊆ B ⊆ *A) | proved | `Goldblatt.NonstandardFramework.IsEnlargement.exists_hyperfinite` | Now proved by the book's argument from the collection {A_a} and placed in the 14.1 section (no longer via Theorem 14.2.1); no nonemptiness hypothesis (empty case handled separately). |
| Enlargement Theorem (Section 14.1, proved in 14.3) | proved | `Goldblatt.exists_enlargement` | For IsBaseSet X: a framework with F.X = X, F.U = superstructure X, F.U' = superstructure (F.star X), and IsEnlargement. No sorry; standard axioms only. |
| Enlargement Theorem, for an arbitrary type | proved | `Goldblatt.exists_enlargement_of_type` | Every type has a copy X in ZFSet with an enlargement of U(X) of the form U(*X). |
| Enlargement Theorem, over the reals | proved | `Goldblatt.exists_realFramework_isEnlargement` | Also Goldblatt.exists_realFramework_nonstandard. |
| Section 14.2 definition (concurrent relation) | proved | `Goldblatt.Concurrent` | Definition. |
| Section 14.2 example 1 (greater-than on R+; a bound is a positive infinitesimal) | proved | `Goldblatt.RealFramework.pos_infinitesimal_of_bound_gtRel` | gtRel, concurrent_gtRel, pair_mem_star_gtRel, exists_bound_gtRel. |
| Section 14.2 example 2 (less-than on R+; a bound is a positive unlimited hyperreal) | proved | `Goldblatt.RealFramework.pos_unlimited_of_bound_ltRel` | ltRel, concurrent_ltRel, pair_mem_star_ltRel, exists_bound_ltRel. |
| Section 14.2 example 3 (nonidentity relation concurrent iff A infinite) | proved | `Goldblatt.concurrent_neRel_iff` | Corrected statement: needs A to have two distinct members (otherwise the relation is empty and vacuously concurrent). neRel, dom_neRel. |
| Section 14.2 example 3 (*R is the nonidentity relation on *A; a bound is a nonstandard member of *A) | proved | `Goldblatt.NonstandardFramework.mem_star_notMem_im_of_bound_neRel` | With pair_mem_star_neRel. |
| Section 14.2 example 4 (membership relation between A and P_F(A) is concurrent) | proved | `Goldblatt.concurrent_memRel` | memRel, dom_memRel, pair_mem_memRel. |
| Section 14.2 example 4 (a bound of *R is a hyperfinite subset of *A including im A) | proved | `Goldblatt.NonstandardFramework.mem_star_finPow_of_bound_memRel` | New. With pair_mem_star_memRel (the transform is membership between *A and *P_F(A)). Hypothesis A ≠ ∅ added (for empty A every entity is a bound); docstring says so. Reused in ConcurrentBound.hyperfiniteApprox. |
| Theorem 14.2.1 | proved | `Goldblatt.NonstandardFramework.enlargement_tfae` | List.TFAE [IsEnlargement, ConcurrentBound, HyperfiniteApprox]. |
| Theorem 14.2.1 (1)⇒(2) | proved | `Goldblatt.NonstandardFramework.IsEnlargement.concurrentBound` | Book's proof via the sets R[x]. |
| Theorem 14.2.1 (2)⇒(3) | proved | `Goldblatt.NonstandardFramework.ConcurrentBound.hyperfiniteApprox` | Book's proof via the membership relation, now through mem_star_finPow_of_bound_memRel. |
| Theorem 14.2.1 (3)⇒(1) | proved | `Goldblatt.NonstandardFramework.HyperfiniteApprox.isEnlargement` | Book's sentence with T = ⋃𝒜 in place of a transitive T. |
| Section 14.3 definition (Z_n, Z: functions of bounded rank) | proved | `Goldblatt.BoundedUltrapower.Bdd` | Docstring now states the divergence from the book (values off an ultrafilter set unconstrained; exists_rep, col_congr). Also Atomic (Z_0), E, rk; E_wf. |
| Section 14.3 (chain Z_0 ⊆ Z_1 ⊆ ...) | proved | `Goldblatt.BoundedUltrapower.eventually_mem_cumPow_mono` | New. |
| Section 14.3 (rank of f is well defined) | proved | `Goldblatt.BoundedUltrapower.existsUnique_rank` | Moved to Collapse.lean under '### The rank of a function', in the book's order. |
| Section 14.3 (rank of a function: Z_n minus Z_{n-1} is the functions of rank n; rank of a^I is rank of a) | proved | `Goldblatt.BoundedUltrapower.eventually_rank_eq_rk` | With rk_le_iff, rk_eq_succ_iff, rk_eq_zero_iff, rk_const; all moved to Collapse.lean. |
| Section 14.3 definition (Y = {[f] : f ∈ Z_0}) | proved | `Goldblatt.BoundedUltrapower.base` | Old individuals kept, new ones are {(U(X), code)}; isBaseSet_base. |
| Section 14.3 definition (the map f ↦ [f], Mostowski collapse) | proved | `Goldblatt.BoundedUltrapower.col` | Well-founded recursion; mem_col, col_mem_cumPow. |
| Section 14.3 ([f] ∈ [g] iff {i : f(i) ∈ g(i)} ∈ F) | proved | `Goldblatt.BoundedUltrapower.col_mem_col_iff` | Stated without proof in the book. |
| Section 14.3 ([f] = [g] iff {i : f(i) = g(i)} ∈ F) | proved | `Goldblatt.BoundedUltrapower.col_eq_iff` | Stated without proof in the book. |
| Section 14.3 (*a = {[f] : f ∈ Z, [f ∈ a] ∈ F}) | proved | `Goldblatt.BoundedUltrapower.mem_star_iff` | Transfer map is BoundedUltrapower.star, a ↦ [a^I]. |
| Section 14.3 (*U_n(X) = {[f] : [f ∈ U_n(X)] ∈ F}) | proved | `Goldblatt.BoundedUltrapower.mem_star_cumPow_iff` |  |
| Section 14.3 (*X = Y, so U(Y) = U(*X)) | proved | `Goldblatt.BoundedUltrapower.col_const_base` | Also col_const_of_mem and base_subset. |
| Section 14.3 (*∅ = ∅) | proved | `Goldblatt.BoundedUltrapower.col_const_empty` |  |
| Section 14.3 Łoś's theorem | proved | `Goldblatt.BoundedUltrapower.los` | For all admissible formulas of the Ch13 deep embedding, with the definedness convention. |
| Section 14.3 (the ultrapower is a universe embedding / framework) | proved | `Goldblatt.BoundedUltrapower.framework` | For any ultrafilter on any Small.{u} index type and any IsBaseSet X. |
| Section 14.3 remark (nonprincipal ultrafilter gives nonstandard members, cf. 3.8/3.9) | proved | `Goldblatt.BoundedUltrapower.exists_mem_star_notMem_im_of_nonprincipal` | Any nonprincipal ultrafilter on ℕ; exists_mem_star_notMem_im_of_countablyIncomplete for countably incomplete ultrafilters on any Small index type. Restricted on purpose: the unrestricted remark fails for a countably complete nonprincipal ultrafilter. |
| Section 14.3 definition (I = P_F(U(X)), sets I_a, the ultrafilter) | proved | `Goldblatt.BoundedUltrapower.ultra` | Index, cone, hasFIP_cones, cone_mem_ultra; uses Ch02 HasFIP.exists_isUltrafilter_superset (Theorem 2.6.1). |
| Section 14.3 remark (each member of I belongs to U(X)) | proved | `Goldblatt.BoundedUltrapower.index_mem_superstructure` | New. No base-set hypothesis needed. |
| Section 14.3 remark (I itself does not belong to U(X)) | proved | `Goldblatt.BoundedUltrapower.finPow_superstructure_notMem` | New. For IsBaseSet X; the union of P_F(U(X)) is U(X), which would then be a member of itself. Index docstring now explains the Type (u+1) level. |
| Section 14.3 (U(*X) is an enlargement, main proof) | proved | `Goldblatt.BoundedUltrapower.isEnlargement_enlargement` | Book's argument; f(b) also chosen in a fixed member of the collection, removing the book's case split. |
| Section 14.3 (alternative proof via hyperfinite approximation, g(b) = b ∩ A) | proved | `Goldblatt.BoundedUltrapower.hyperfiniteApprox_enlargement` |  |
| Exercise 14.4(1) | proved | `Goldblatt.BoundedUltrapower.framework` | The details of the construction: col_congr, col_eq_iff, col_mem_col_iff, col_opair, col_const_num, col_tuple, col_appDef, los, framework. |
| Exercise 14.4(2) | proved | `Goldblatt.BoundedUltrapower.app_col_eq_iff` | [F]([h]) = [k] iff F(i)(h(i)) = k(i) a.e., no domain hypothesis; with isFunction_col and col_appVal. |
| Exercise 14.4(3) | proved | `Goldblatt.BoundedUltrapower.ultra_ne_pure` | Yes: the ultrafilter of the construction is nonprincipal. |

## 17. Ramsey Theory

| Book item | Status | Lean declaration | Note |
|---|---|---|---|
| Section 17.1 definition [A]^k | proved | `Goldblatt.kSubsets` | Set (Finset α) of k-element subsets of A. Lemmas mem_kSubsets, kSubsets_mono (the book's remark that [B]^k ⊆ [A]^k), kSubsets_coe (equals Finset.powersetCard for a finite set), kSubsets_zero, kSubsets_one, kSubsets_nonempty. |
| Section 17.1 definition (monochromatic set) | proved | `Goldblatt.IsMonochromatic` | Cover form: ∃ i, [B]^k ⊆ C i. isMonochromatic_fibres_iff relates it to the function form of a colouring. A concrete example (parity-of-sum colouring of pairs, even numbers monochromatic) is given for non-vacuity. |
| Section 17.1 opening observation (infinite pigeonhole) | proved | `Goldblatt.exists_infinite_inter_of_subset_iUnion` | Also the colouring form exists_infinite_monochromatic_points. Proved from Mathlib's finite-union-of-finite-sets fact, which the book takes as evident. |
| Ramsey's Theorem (Section 17.1 statement, Section 17.3 proof) | proved | `Goldblatt.infinite_ramsey` | Function colouring into a Finite type, any type α, any infinite A. Also infinite_ramsey' (no kSubsets notation) and infinite_ramsey_cover (the book's cover formulation). Book's nonstandard proof; no Mathlib Ramsey theorem used. |
| Section 17.3 reduction to 2-colourings | proved | `Goldblatt.ramsey_of_two_colours` | The book's induction on the number of colours, done as induction on a Finset of colours. |
| Section 17.3 enlarged colouring of t ∪ {π} | proved | `Goldblatt.StarBlack` | Defined with Ch03 starMap and starSet. starBlack_ofSeq is the almost-all criterion; not_starBlack_iff shows the enlarged classes 2-colour the sets t ∪ {π}. |
| Section 17.3 extension of the 2-colouring to *([A]^(k+1)) (cover by *C_b ∪ *C_w, disjointness) | proved | `Goldblatt.starSet_black_union_white` | New sharp form per review: ⋆{c = true} ∪ ⋆{c = false} = univ and the two classes are disjoint (from Ch03 starSet_compl). Goldblatt.starSet_black_white (the book's phrasing, ⋆(kSubsets A k) ⊆ union, plus disjointness) is kept as an immediate corollary; its docstring states that A and k play no role. Docstring re-wrapped to 100 columns. |
| Section 17.3 construction of the sequence, property (iii), conditions (vi)-(ix) | proved | `Goldblatt.exists_seq_like_nonstandard` | The existential transfer step is exists_standard_like_nonstandard. Property (iii) is proved for sets t of earlier terms of any size, which is stronger than the book's k-element case. |
| Section 17.3 inductive step in k and two-colour theorem | proved | `Goldblatt.ramsey_two_colours` | Step lemma is ramsey_two_colours_succ. Induction starts at k = 0 (trivial) rather than the book's k = 1. |
| Section 17.3 base case k = 1 | proved | `Goldblatt.ramsey_one` | The book's base case from the pigeonhole principle; proved separately and not used by the main induction. |
| Theorem 17.1.1 | proved | `Goldblatt.exists_strictMono_or_strictAnti_or_antichain` | Section 17.1 proof via Ramsey for pairs. Statement: ∃ s : ℕ → P, StrictMono s ∨ StrictAnti s ∨ ∀ m n, m ≠ n → ¬ s m ≤ s n. The chain case is exists_strictMono_or_strictAnti_of_chain. |
| Section 17.2 nonstandard proof of Theorem 17.1.1 | proved | `Goldblatt.exists_strictMono_or_strictAnti_or_antichain_nonstandard` | L, U, M as in the book, with π nonstandard in *P. Deviation: no least/greatest elements adjoined; an empty L or U imposes no bound. Antichain construction is exists_antichain_of_incomparable_nonstandard; helpers exists_strictMono_of_forall_exists_gt, exists_strictAnti_of_forall_exists_lt. |
| Exercise 17.3.1 | proved | `Goldblatt.bijOn_internalElems_starSet_kSubsets` | Set.BijOn internalElems (⋆(kSubsets A k)) (coe '' kSubsets (⋆A) k), for every k: the two sides live in different types in the ultrapower, so the equality is a bijection via the element set of an internal finite set. internalElems_injective supplies injectivity; image_internalElems_starSet_kSubsets is the surjectivity/maps-to half; key computation internalElems_ofSeq_eq_range. |
| Finite Ramsey Theorem (Section 17.4) | proved | `Goldblatt.finite_ramsey` | ∀ k r m, ∃ n, ∀ c : Finset ℕ → Fin r, ∃ B ⊆ Finset.Icc 1 n, m ≤ B.card ∧ monochromatic. Nonstandard proof via eventually_forall_exists_monochromatic and finite_ramsey_with. Variants: finite_ramsey_powersetCard (any Finite colour type, Mathlib vocabulary) and finite_ramsey_cover (cover form). |
| Section 17.4 claim *ψ(N) for unlimited N | proved | `Goldblatt.eventually_finite_ramsey_of_unlimited` | For hnat ν ∈ unlimitedHyperNat (Ch05), ψ(ν n) holds for almost all n. Bridge lemma eventually_le_of_hnat_mem_unlimitedHyperNat; internal-colouring lemma exists_infinite_homogeneous_internal. |
| Exercise 17.4.1 | omitted |  | Verification that ψ(n) is a formula of the formal language; no formal language is used in this chapter (the Ch04 language is not an allowed import). The two transfer steps are eventually_forall_exists_monochromatic and finite_ramsey_with; a module-doc subsection explains this. Status changed from prose to omitted per review; record this way in COVERAGE.md. |
| Section 17.5 definition (relatively large) | proved | `Goldblatt.RelativelyLarge` | ∃ b, IsLeast ↑B b ∧ b ≤ B.card. relativelyLarge_iff gives the Finset.min' form; an example shows {2,5} is relatively large and {3,5} is not. |
| Section 17.5 selection of relatively large subsets | proved | `Goldblatt.exists_relativelyLarge_subset` | Every infinite D ⊆ ℕ has a relatively large finite subset with at least m elements, built as in the book with \|B\| = min B = j. |
| Paris–Harrington version (Section 17.5) | proved | `Goldblatt.paris_harrington` | Truth of the statement only, by the same nonstandard argument. finite_ramsey_of_paris_harrington shows it implies the finite Ramsey theorem. Unprovability in Peano arithmetic is metamathematics and is not formalized. |
| Section 17.6 Reference | prose |  | Attribution to Hirshfeld in the module doc, rewritten in original wording with full citation: Nonstandard combinatorics, Studia Logica 47 (1988), 221-232. The book's text prints 1980; 1988 is from my own knowledge of the journal volume, not checked online, and the doc notes the discrepancy. |
