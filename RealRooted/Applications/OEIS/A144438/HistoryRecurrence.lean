import RealRooted.Applications.OEIS.A144438.ExactLayer
import RealRooted.Applications.OEIS.A144438.HistoryExtension
import RealRooted.Combinatorics.ComparisonBottomInsertion

/-!
# Polynomial recurrences for Deco history fibers

This file translates the last-step equivalences for fixed exceptional-history
fibers into identities for their comparison-bottom enumerators.  It also
records compatibility with the operator-defined exact layers.  The generic
minimum-insertion identities remain in the combinatorics namespace.
-/

namespace RealRooted.Applications.OEIS

open scoped BigOperators
open MinimumInsertionWord

noncomputable section

/-- A height-two inverse word has no comparison bottoms. -/
theorem comparisonBottomSupport_inverseWord_eq_empty_height_two
    (H : DecoExceptionalHistory 2) (c : DecoHistoryFiber H) :
    comparisonBottomSupport c.1.1.inverseWord = ∅ := by
  have hlength := c.1.1.length_inverseWord
  have hascent := c.1.1.inverseWord_startsWithAscent c.1.2 (by lia)
  generalize hword : c.1.1.inverseWord = w at hlength hascent ⊢
  cases w with
  | nil => simp at hlength
  | cons a w =>
      cases w with
      | nil => simp at hlength
      | cons b w =>
          cases w with
          | nil => simpa [comparisonBottomSupport, hascent]
          | cons d w => simp at hlength

/-- Every comparison-bottom label in a fixed height-`n+2` history fiber is
one of the exact layer coordinates `1, ..., n`. -/
theorem mem_comparisonBottomSupport_inverseWord_bounds :
    ∀ {n : Nat} (H : DecoExceptionalHistory (n + 2))
      (c : DecoHistoryFiber H) {x : Nat},
      x ∈ comparisonBottomSupport c.1.1.inverseWord → 1 ≤ x ∧ x ≤ n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro H c x hx
      rw [comparisonBottomSupport_inverseWord_eq_empty_height_two H c] at hx
      simp at hx
  | one =>
      intro H c x hx
      rcases H.exists_last_step with hnormal | hexceptional
      · obtain ⟨H', rfl⟩ := hnormal
        let p := (normalHistoryExtensionEquiv H').symm c
        have hc : normalHistoryExtension H' p = c :=
          (normalHistoryExtensionEquiv H').apply_symm_apply c
        rw [← hc] at hx
        change x ∈ comparisonBottomSupport
          (p.1.1.1.1.snoc p.1.2).inverseWord at hx
        rw [DecoCode.inverseWord_snoc] at hx
        have hr : (p.1.2 : Nat) ≤ p.1.1.1.1.inverseWord.length := by
          rw [p.1.1.1.1.length_inverseWord]
          have := p.1.2.isLt
          lia
        apply mem_comparisonBottomSupport_step_bounds
          p.1.1.1.1.inverseWord_isPositive hr (fun y hy => ?_) hx
        rw [comparisonBottomSupport_inverseWord_eq_empty_height_two
          H' p.1.1] at hy
        simp at hy
      · obtain ⟨H', _⟩ := hexceptional
        have := H'.admissible.1
        lia
  | more n ih0 ih1 =>
      intro H c x hx
      rcases H.exists_last_step with hnormal | hexceptional
      · obtain ⟨H', rfl⟩ := hnormal
        let p := (normalHistoryExtensionEquiv H').symm c
        have hc : normalHistoryExtension H' p = c :=
          (normalHistoryExtensionEquiv H').apply_symm_apply c
        rw [← hc] at hx
        change x ∈ comparisonBottomSupport
          (p.1.1.1.1.snoc p.1.2).inverseWord at hx
        rw [DecoCode.inverseWord_snoc] at hx
        have hr : (p.1.2 : Nat) ≤ p.1.1.1.1.inverseWord.length := by
          rw [p.1.1.1.1.length_inverseWord]
          have := p.1.2.isLt
          lia
        exact mem_comparisonBottomSupport_step_bounds
          p.1.1.1.1.inverseWord_isPositive hr
          (fun y hy => (ih1 H' p.1.1 hy).2) hx
      · obtain ⟨H', rfl⟩ := hexceptional
        let c' := (exceptionalHistoryExtensionEquiv H').symm c
        have hc : exceptionalHistoryExtension H' c' = c :=
          (exceptionalHistoryExtensionEquiv H').apply_symm_apply c
        rw [← hc] at hx
        change x ∈ comparisonBottomSupport
          (c'.1.1.exceptionalExtension (by lia)).inverseWord at hx
        rw [DecoCode.inverseWord_exceptionalExtension] at hx
        exact mem_comparisonBottomSupport_exceptional_pair_bounds
          (c'.1.1.inverseWord_startsWithAscent c'.1.2 (by lia))
          (fun y hy => (ih0 H' c' hy).2) hx

/-- Summing derivatives in the finite exact-layer coordinates removes each
element of a bounded squarefree support once. -/
theorem sum_pderiv_finsetMonomial_eq_sum_erase
    {R : Type*} [CommSemiring R] {n : Nat} (S : Finset Nat)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ n) :
    (∑ i : Fin n,
        MvPolynomial.pderiv (decoLayerBottomEmbedding n i)
          (MvPolynomial.finsetMonomial S : MvPolynomial Nat R)) =
      ∑ x ∈ S, MvPolynomial.finsetMonomial (S.erase x) := by
  classical
  unfold MvPolynomial.finsetMonomial
  simp_rw [MvPolynomial.pderiv_finsetProd_X]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i _ => decoLayerBottomEmbedding n i)
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    exact (decoLayerBottomEmbedding n).injective hij
  · intro x hx
    have hxpos : 0 < x := (hS x hx).1
    have hpred : x - 1 < x := Nat.sub_lt hxpos Nat.zero_lt_one
    let i : Fin n := ⟨x - 1, hpred.trans_le (hS x hx).2⟩
    refine ⟨i, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ i, ?_⟩
      change x - 1 + 1 ∈ S
      rw [Nat.sub_add_cancel (hS x hx).1]
      exact hx
    · change x - 1 + 1 = x
      exact Nat.sub_add_cancel (hS x hx).1
  · intro i hi
    rfl

/-- The finite-coordinate Euler sum of a bounded squarefree monomial is its
support cardinality times that monomial. -/
theorem sum_X_mul_pderiv_finsetMonomial
    {R : Type*} [CommSemiring R] {n : Nat} (S : Finset Nat)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ n) :
    (∑ i : Fin n,
        MvPolynomial.X (decoLayerBottomEmbedding n i) *
          MvPolynomial.pderiv (decoLayerBottomEmbedding n i)
            (MvPolynomial.finsetMonomial S : MvPolynomial Nat R)) =
      MvPolynomial.C (S.card : R) * MvPolynomial.finsetMonomial S := by
  classical
  unfold MvPolynomial.finsetMonomial
  simp_rw [MvPolynomial.pderiv_finsetProd_X, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  calc
    (∑ i ∈ Finset.univ.filter
        (fun i : Fin n => decoLayerBottomEmbedding n i ∈ S),
        MvPolynomial.X (decoLayerBottomEmbedding n i) *
          ∏ y ∈ S.erase (decoLayerBottomEmbedding n i),
            MvPolynomial.X y) =
        ∑ x ∈ S,
          MvPolynomial.X x *
            ∏ y ∈ S.erase x, MvPolynomial.X y := by
      apply Finset.sum_bij (fun i _ => decoLayerBottomEmbedding n i)
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i hi j hj hij
        exact (decoLayerBottomEmbedding n).injective hij
      · intro x hx
        have hxpos : 0 < x := (hS x hx).1
        have hpred : x - 1 < x := Nat.sub_lt hxpos Nat.zero_lt_one
        let i : Fin n := ⟨x - 1, hpred.trans_le (hS x hx).2⟩
        refine ⟨i, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ i, ?_⟩
          change x - 1 + 1 ∈ S
          rw [Nat.sub_add_cancel (hS x hx).1]
          exact hx
        · change x - 1 + 1 = x
          exact Nat.sub_add_cancel (hS x hx).1
      · intro i hi
        rfl
    _ = ∑ _x ∈ S, ∏ y ∈ S, MvPolynomial.X y := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.mul_prod_erase S (fun y => MvPolynomial.X y) hx
    _ = MvPolynomial.C (S.card : R) *
          ∏ y ∈ S, MvPolynomial.X y := by
      rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul R,
        MvPolynomial.smul_eq_C_mul]

/-- For a fixed history fiber, the support normal form is exactly the
ordinary-label Euler/partial-derivative core. -/
theorem comparisonBottomInsertionCore_inverseWord_tail
    {R : Type*} [CommRing R] {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) (c : DecoHistoryFiber H) :
    comparisonBottomInsertionCore (R := R) c.1.1.inverseWord.tail =
      decoNormalBottomCore n
        (comparisonBottomMonomial (R := R) c.1.1.inverseWord) := by
  let w := c.1.1.inverseWord
  let S := comparisonBottomSupport w
  have hascent := c.1.1.inverseWord_startsWithAscent c.1.2 (by lia)
  have hsupport : comparisonBottomSupport w.tail = S := by
    exact comparisonBottomSupport_tail_eq_of_startsWithAscent hascent
  have hlength : w.tail.length = n + 1 := by
    have hwlength := c.1.1.length_inverseWord
    change w.length = n + 2 at hwlength
    rw [List.length_tail, hwlength]
    lia
  have hnodup : w.Nodup := c.1.1.inverseWord_nodup
  have hcard : S.card ≤ n + 1 := by
    have := card_comparisonBottomSupport_le_length hnodup.tail
    rw [hsupport, hlength] at this
    exact this
  have hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ n := by
    intro x hx
    exact mem_comparisonBottomSupport_inverseWord_bounds H c hx
  have hwordSupport : comparisonBottomSupport c.1.1.inverseWord = S := rfl
  have hderiv :
      (∑ x ∈ S,
          MvPolynomial.pderiv x
            (MvPolynomial.finsetMonomial S : MvPolynomial Nat R)) =
        ∑ x ∈ S, MvPolynomial.finsetMonomial (S.erase x) := by
    apply Finset.sum_congr rfl
    intro x hx
    unfold MvPolynomial.finsetMonomial
    rw [MvPolynomial.pderiv_finsetProd_X, if_pos hx]
  rw [comparisonBottomInsertionCore_eq_pderiv]
  unfold decoNormalBottomCore comparisonBottomMonomial
  rw [hsupport, hlength, hwordSupport]
  change MvPolynomial.C (((n + 1 - S.card : Nat) : R)) *
          MvPolynomial.finsetMonomial S +
        ∑ x ∈ S,
          MvPolynomial.pderiv x (MvPolynomial.finsetMonomial S) = _
  rw [hderiv, sum_pderiv_finsetMonomial_eq_sum_erase S hS,
    sum_X_mul_pderiv_finsetMonomial S hS]
  rw [Nat.cast_sub hcard]
  simp only [Nat.cast_add, Nat.cast_one, map_sub, map_add, map_one]
  ring

/-- Summing the fiberwise insertion cores applies the ordinary-label normal
operator core to the whole fixed-history fiber polynomial. -/
theorem sum_comparisonBottomInsertionCore_inverseWord_tail
    {R : Type*} [CommRing R] {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) :
    (∑ c : DecoHistoryFiber H,
        comparisonBottomInsertionCore (R := R) c.1.1.inverseWord.tail) =
      decoNormalBottomCore n (historyFiberPolynomial (R := R) H) := by
  calc
    (∑ c : DecoHistoryFiber H,
        comparisonBottomInsertionCore (R := R) c.1.1.inverseWord.tail) =
        ∑ c : DecoHistoryFiber H,
          decoNormalBottomCore n
            (comparisonBottomMonomial (R := R) c.1.1.inverseWord) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact comparisonBottomInsertionCore_inverseWord_tail H c
    _ = decoNormalBottomCore n (historyFiberPolynomial (R := R) H) := by
      unfold decoNormalBottomCore historyFiberPolynomial
      simp only [Finset.mul_sum, map_sum, Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      congr 1
      rw [Finset.sum_comm]

/-- A normal history step is the shifted old fiber polynomial plus the
shifted insertion core summed over the old fiber. -/
theorem historyFiberPolynomial_normal_core
    {R : Type*} [CommRing R] {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) :
    historyFiberPolynomial (R := R) (DecoExceptionalHistory.normal H) =
      MvPolynomial.rename MinimumInsertionWord.succEmbedding
          (historyFiberPolynomial (R := R) H) +
        MvPolynomial.X 1 *
          MvPolynomial.rename MinimumInsertionWord.succEmbedding
            (∑ c : DecoHistoryFiber H,
              MinimumInsertionWord.comparisonBottomInsertionCore
                (R := R) c.1.1.inverseWord.tail) := by
  unfold historyFiberPolynomial
  calc
    (∑ c : DecoHistoryFiber (DecoExceptionalHistory.normal H),
        MinimumInsertionWord.comparisonBottomMonomial c.1.1.inverseWord) =
        ∑ p : DecoNormalHistoryExtension H,
          MinimumInsertionWord.comparisonBottomMonomial
            (normalHistoryExtension H p).1.1.inverseWord := by
      apply Fintype.sum_equiv (normalHistoryExtensionEquiv H).symm
      intro c
      have hc := (normalHistoryExtensionEquiv H).apply_symm_apply c
      change normalHistoryExtension H
        ((normalHistoryExtensionEquiv H).symm c) = c at hc
      rw [hc]
    _ = ∑ p : Σ _c : DecoHistoryFiber H,
          {r : Fin (n + 3) // (r : Nat) ≠ 1},
          MinimumInsertionWord.comparisonBottomMonomial
            (normalHistoryExtension H
              ((normalHistoryExtensionSigmaEquiv H).symm p)).1.1.inverseWord := by
      apply Fintype.sum_equiv (normalHistoryExtensionSigmaEquiv H)
      intro p
      have hp := (normalHistoryExtensionSigmaEquiv H).symm_apply_apply p
      rw [hp]
    _ = ∑ c : DecoHistoryFiber H,
          ∑ r : {r : Fin (n + 3) // (r : Nat) ≠ 1},
            MinimumInsertionWord.comparisonBottomMonomial
              (MinimumInsertionWord.step r.1 c.1.1.inverseWord) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro r hr
      simp [normalHistoryExtensionSigmaEquiv, normalHistoryExtension]
    _ = ∑ c : DecoHistoryFiber H,
          (MvPolynomial.rename MinimumInsertionWord.succEmbedding
              (MinimumInsertionWord.comparisonBottomMonomial
                c.1.1.inverseWord) +
            MvPolynomial.X 1 *
              MvPolynomial.rename MinimumInsertionWord.succEmbedding
                (MinimumInsertionWord.comparisonBottomInsertionCore
                  (R := R) c.1.1.inverseWord.tail)) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hlength := c.1.1.length_inverseWord
      have hsum :=
        sum_val_ne_one_comparisonBottomMonomial_step_of_startsWithAscent
          (R := R) c.1.1.inverseWord_isPositive c.1.1.inverseWord_nodup
            (c.1.1.inverseWord_startsWithAscent c.1.2 (by lia))
      rw [hlength] at hsum
      simpa only [Nat.add_assoc] using hsum
    _ = MvPolynomial.rename MinimumInsertionWord.succEmbedding
          (∑ c : DecoHistoryFiber H,
            MinimumInsertionWord.comparisonBottomMonomial
              c.1.1.inverseWord) +
        MvPolynomial.X 1 *
          MvPolynomial.rename MinimumInsertionWord.succEmbedding
            (∑ c : DecoHistoryFiber H,
              MinimumInsertionWord.comparisonBottomInsertionCore
                (R := R) c.1.1.inverseWord.tail) := by
      rw [Finset.sum_add_distrib, map_sum, map_sum, Finset.mul_sum]

/-- The exact-layer identification is preserved by a normal history step. -/
theorem historyFiberPolynomial_normal_eq_exactLayer
    {n : Nat} (H : DecoExceptionalHistory (n + 2))
    (hH : historyFiberPolynomial (R := ℝ) H =
      MvPolynomial.rename (decoLayerBottomEmbedding n)
        (MvPolynomial.dehomogenize (decoExactLayer H))) :
    historyFiberPolynomial (R := ℝ) (DecoExceptionalHistory.normal H) =
      MvPolynomial.rename (decoLayerBottomEmbedding (n + 1))
        (MvPolynomial.dehomogenize
          (decoExactLayer (DecoExceptionalHistory.normal H))) := by
  rw [historyFiberPolynomial_normal_core,
    sum_comparisonBottomInsertionCore_inverseWord_tail, hH,
    decoExactLayer_normal]
  simpa [succEmbedding, Nat.succ_eq_add_one] using
    (rename_decoLayerBottomEmbedding_dehomogenize_normal
      (decoExactLayer_isHomogeneous H)).symm

/-- An exceptional history step shifts every old bottom variable by two and
adjoins the new bottom variable `X 2`. -/
theorem historyFiberPolynomial_exceptional
    {R : Type*} [CommSemiring R] {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) :
    historyFiberPolynomial (R := R) (DecoExceptionalHistory.exceptional H) =
      MvPolynomial.X 2 *
        MvPolynomial.rename
          (MinimumInsertionWord.succEmbedding.trans
            MinimumInsertionWord.succEmbedding)
          (historyFiberPolynomial (R := R) H) := by
  unfold historyFiberPolynomial
  calc
    (∑ c : DecoHistoryFiber (DecoExceptionalHistory.exceptional H),
        MinimumInsertionWord.comparisonBottomMonomial c.1.1.inverseWord) =
        ∑ c : DecoHistoryFiber H,
          MinimumInsertionWord.comparisonBottomMonomial
            (exceptionalHistoryExtension H c).1.1.inverseWord := by
      apply Fintype.sum_equiv (exceptionalHistoryExtensionEquiv H).symm
      intro c
      have hc := (exceptionalHistoryExtensionEquiv H).apply_symm_apply c
      change exceptionalHistoryExtension H
        ((exceptionalHistoryExtensionEquiv H).symm c) = c at hc
      rw [hc]
    _ = ∑ c : DecoHistoryFiber H,
          MvPolynomial.X 2 *
            MvPolynomial.rename
              (MinimumInsertionWord.succEmbedding.trans
                MinimumInsertionWord.succEmbedding)
              (MinimumInsertionWord.comparisonBottomMonomial
                c.1.1.inverseWord) := by
      apply Finset.sum_congr rfl
      intro c hc
      change MinimumInsertionWord.comparisonBottomMonomial
          (c.1.1.exceptionalExtension (by lia)).inverseWord = _
      rw [DecoCode.inverseWord_exceptionalExtension]
      exact MinimumInsertionWord.comparisonBottomMonomial_exceptional_pair
        c.1.1.inverseWord_isPositive
        (c.1.1.inverseWord_startsWithAscent c.1.2 (by lia))
    _ = MvPolynomial.X 2 *
          MvPolynomial.rename
            (MinimumInsertionWord.succEmbedding.trans
              MinimumInsertionWord.succEmbedding)
            (∑ c : DecoHistoryFiber H,
              MinimumInsertionWord.comparisonBottomMonomial
                c.1.1.inverseWord) := by
      rw [map_sum, Finset.mul_sum]

/-- The exact-layer identification is preserved by an exceptional history
step. -/
theorem historyFiberPolynomial_exceptional_eq_exactLayer
    {n : Nat} (H : DecoExceptionalHistory (n + 2))
    (hH : historyFiberPolynomial (R := ℝ) H =
      MvPolynomial.rename (decoLayerBottomEmbedding n)
        (MvPolynomial.dehomogenize (decoExactLayer H))) :
    historyFiberPolynomial (R := ℝ)
        (DecoExceptionalHistory.exceptional H) =
      MvPolynomial.rename (decoLayerBottomEmbedding (n + 2))
        (MvPolynomial.dehomogenize
          (decoExactLayer (DecoExceptionalHistory.exceptional H))) := by
  rw [historyFiberPolynomial_exceptional, hH,
    decoExactLayer_exceptional]
  exact
    (rename_decoLayerBottomEmbedding_dehomogenize_exceptional
      (decoExactLayer H)).symm

/-- Every fixed-history fiber polynomial is its operator-defined exact layer. -/
theorem historyFiberPolynomial_eq_exactLayer :
    ∀ {n : Nat} (H : DecoExceptionalHistory (n + 2)),
      historyFiberPolynomial (R := ℝ) H =
        MvPolynomial.rename (decoLayerBottomEmbedding n)
          (MvPolynomial.dehomogenize (decoExactLayer H)) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro H
      rw [H.eq_seed, historyFiberPolynomial_seed, decoExactLayer_seed]
      simp
  | one =>
      intro H
      rcases H.exists_last_step with hnormal | hexceptional
      · obtain ⟨H', rfl⟩ := hnormal
        apply historyFiberPolynomial_normal_eq_exactLayer
        rw [H'.eq_seed, historyFiberPolynomial_seed, decoExactLayer_seed]
        simp
      · obtain ⟨H', _⟩ := hexceptional
        have := H'.admissible.1
        lia
  | more n ih0 ih1 =>
      intro H
      rcases H.exists_last_step with hnormal | hexceptional
      · obtain ⟨H', rfl⟩ := hnormal
        exact historyFiberPolynomial_normal_eq_exactLayer H' (ih1 H')
      · obtain ⟨H', rfl⟩ := hexceptional
        exact historyFiberPolynomial_exceptional_eq_exactLayer H' (ih0 H')

/-- The admissible-code enumerator is the exact sum of its operator-defined
history layers.  This identity does not assert stability of the outer sum. -/
theorem admissibleCodePolynomial_eq_sum_exactLayers (n : Nat) :
    admissibleCodePolynomial (R := ℝ) (n + 2) =
      ∑ H : DecoExceptionalHistory (n + 2),
        MvPolynomial.rename (decoLayerBottomEmbedding n)
          (MvPolynomial.dehomogenize (decoExactLayer H)) := by
  rw [admissibleCodePolynomial_eq_sum_historyFiberPolynomial]
  apply Finset.sum_congr rfl
  intro H hH
  exact historyFiberPolynomial_eq_exactLayer H

end

end RealRooted.Applications.OEIS
