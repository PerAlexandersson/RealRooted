import RealRooted.BorceaBranden.FiniteSymbolBasis
import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.Symbol
import RealRooted.MultiaffineReciprocalRight

/-!
# The source-reciprocal finite-symbol identity

This module proves the algebraic identity used in the reciprocal step of
Borcea--Branden, arXiv:0809.0401, Lemma 2.2.  Only the finite source block is
reciprocated; the target variables are unrestricted spectators.
-/

namespace RealRooted.BorceaBranden

noncomputable section

open BigOperators
open MvPolynomial

private def sumInrEmbedding (tau sigma : Type*) : sigma ↪ Sum tau sigma :=
  ⟨Sum.inr, Sum.inr_injective⟩

private theorem boxChoose_one
    {sigma : Type*} [Fintype sigma]
    (m : {m : sigma →₀ ℕ // ∀ i, m i ≤ 1}) :
    boxChoose (fun _ : sigma => 1) m.1 = 1 := by
  unfold boxChoose
  apply Finset.prod_eq_one
  intro i hi
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (m.2 i) with hzero | hone
  · simp [hzero]
  · simp [hone]

private theorem prod_X_eq_monomial_indicator_map
    {R sigma tau : Type*} [CommSemiring R]
    (e : sigma ↪ tau) (s : Finset sigma) :
    ∏ i ∈ s, (X (e i) : MvPolynomial tau R) =
      monomial (Finsupp.indicator (s.map e) (fun _ _ => 1)) 1 := by
  classical
  simpa [Finset.prod_map] using
    (MvPolynomial.prod_X_pow (R := R) (fun _ : tau => 1) (s.map e))

private theorem rightComplementMonomial_one
    {R sigma tau : Type*} [CommSemiring R]
    [Fintype sigma] [DecidableEq sigma]
    (m : {m : sigma →₀ ℕ // ∀ i, m i ≤ 1}) :
    rightComplementMonomial (R := R) (τ := tau)
        (fun _ : sigma => 1) m.1 =
      monomial
        (Finsupp.indicator
          ((Finset.univ \ m.1.support).map
            (sumInrEmbedding tau sigma)) (fun _ _ => 1)) 1 := by
  classical
  unfold rightComplementMonomial
  have hone (i : sigma) (hi : i ∈ m.1.support) : m.1 i = 1 := by
    have hne : m.1 i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hle := m.2 i
    cases hdi : m.1 i with
    | zero => exact (hne hdi).elim
    | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
            rw [hdi] at hle
            exact (Nat.not_succ_le_zero n
              (Nat.le_of_succ_le_succ hle)).elim
  calc
    ∏ i, X (Sum.inr i) ^ (1 - m.1 i) =
        ∏ i ∈ Finset.univ \ m.1.support,
          (X (Sum.inr i) : MvPolynomial (tau ⊕ sigma) R) := by
      calc
        (∏ i, (X (Sum.inr i) : MvPolynomial (tau ⊕ sigma) R) ^
            (1 - m.1 i)) =
            ∏ i ∈ Finset.univ \ m.1.support,
              (X (Sum.inr i) : MvPolynomial (tau ⊕ sigma) R) ^
                (1 - m.1 i) := by
          symm
          apply Finset.prod_subset Finset.sdiff_subset
          intro i hi_univ hi_diff
          have hi_support : i ∈ m.1.support := by
            by_contra hi
            exact hi_diff (Finset.mem_sdiff.mpr ⟨hi_univ, hi⟩)
          simp [hone i hi_support]
        _ = ∏ i ∈ Finset.univ \ m.1.support,
              (X (Sum.inr i) : MvPolynomial (tau ⊕ sigma) R) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hzero : m.1 i = 0 :=
            Finsupp.notMem_support_iff.mp (Finset.mem_sdiff.mp hi).2
          simp [hzero]
    _ = monomial
          (Finsupp.indicator
            ((Finset.univ \ m.1.support).map
              (sumInrEmbedding tau sigma)) (fun _ _ => 1)) 1 := by
      exact prod_X_eq_monomial_indicator_map
        (sumInrEmbedding tau sigma) (Finset.univ \ m.1.support)

private theorem degreeOf_rightComplementMonomial_one_le
    {sigma tau : Type*} [Fintype sigma] [DecidableEq sigma]
    (m : {m : sigma →₀ ℕ // ∀ i, m i ≤ 1}) :
    ∀ i : sigma,
      (rightComplementMonomial (R := ℂ) (τ := tau)
        (fun _ : sigma => 1) m.1).degreeOf (Sum.inr i) ≤ 1 := by
  classical
  rw [rightComplementMonomial_one m]
  intro i
  rw [degreeOf_le_iff]
  intro d hd
  simp only [support_monomial, if_neg one_ne_zero,
    Finset.mem_singleton] at hd
  subst d
  by_cases hi : Sum.inr i ∈
      (Finset.univ \ m.1.support).map (sumInrEmbedding tau sigma)
  · simp [Finsupp.indicator_apply, hi]
  · simp [Finsupp.indicator_apply, hi]

private theorem degreeOf_rename_inl_le_zero
    {sigma tau : Type*} (A : MvPolynomial tau ℂ) (i : sigma) :
    (rename (Sum.inl : tau → Sum tau sigma) A).degreeOf (Sum.inr i) ≤ 0 := by
  rw [degreeOf_le_iff]
  intro d hd
  apply Nat.le_zero.mpr
  by_contra hdi
  have hmem : Sum.inr i ∈
      (rename (Sum.inl : tau → Sum tau sigma) A).vars := by
    rw [mem_vars]
    exact ⟨d, hd, Finsupp.mem_support_iff.mpr hdi⟩
  obtain ⟨j, hj, hji⟩ := mem_vars_rename Sum.inl A hmem
  exact Sum.inl_ne_inr hji

private theorem signedMultiaffineReciprocalRight_target_mul
    {sigma tau : Type*} [Fintype sigma]
    (A : MvPolynomial tau ℂ) (P : MvPolynomial (Sum tau sigma) ℂ)
    (hP : ∀ i : sigma, P.degreeOf (Sum.inr i) ≤ 1) :
    signedMultiaffineReciprocalRight (rename Sum.inl A * P) =
      rename Sum.inl A * signedMultiaffineReciprocalRight P := by
  let s : Sum tau sigma → Set ℂ :=
    Sum.elim (fun _ => Set.univ) (fun _ => {z | z ≠ 0})
  apply MvPolynomial.funext_set s
  · intro x
    cases x with
    | inl j => exact Set.infinite_univ
    | inr i =>
        exact Set.infinite_of_injective_forall_mem
          UpperHalfPlane.coe_injective fun z => fun hzero => by
            have hz := z.coe_im_pos
            rw [hzero] at hz
            simp at hz
  · intro z hz
    have hz0 : ∀ i : sigma, z (Sum.inr i) ≠ 0 := by
      intro i
      simpa [s] using hz (Sum.inr i) (Set.mem_univ _)
    have hprod : ∀ i : sigma,
        (rename Sum.inl A * P).degreeOf (Sum.inr i) ≤ 1 := by
      intro i
      calc
        (rename Sum.inl A * P).degreeOf (Sum.inr i) ≤
            (rename Sum.inl A).degreeOf (Sum.inr i) +
              P.degreeOf (Sum.inr i) :=
          degreeOf_mul_le _ _ _
        _ ≤ 0 + 1 := add_le_add (degreeOf_rename_inl_le_zero A i) (hP i)
        _ = 1 := by simp
    rw [eval_signedMultiaffineReciprocalRight hprod z hz0]
    simp only [eval_mul, eval_rename]
    rw [eval_signedMultiaffineReciprocalRight hP z hz0]
    have hcomp :
        (Sum.elim
          (fun i => z (Sum.inl i))
          (fun i => -(z (Sum.inr i))⁻¹) ∘ Sum.inl) =
          z ∘ Sum.inl := by
      funext i
      rfl
    rw [hcomp]
    ring

private theorem normalized_reciprocal_rightComplementMonomial_one
    {sigma tau : Type*} [Fintype sigma] [DecidableEq sigma]
    (m : {m : sigma →₀ ℕ // ∀ i, m i ≤ 1}) :
    C ((-1 : ℂ) ^ Fintype.card sigma) *
        signedMultiaffineReciprocalRight
          (rightComplementMonomial (R := ℂ) (τ := tau)
            (fun _ : sigma => 1) m.1) =
      ∏ i : sigma, (-X (Sum.inr i)) ^ m.1 i := by
  let s : Sum tau sigma → Set ℂ :=
    Sum.elim (fun _ => Set.univ) (fun _ => {z | z ≠ 0})
  apply MvPolynomial.funext_set s
  · intro x
    cases x with
    | inl j => exact Set.infinite_univ
    | inr i =>
        exact Set.infinite_of_injective_forall_mem
          UpperHalfPlane.coe_injective fun z => fun hzero => by
            have hz := z.coe_im_pos
            rw [hzero] at hz
            simp at hz
  · intro z hz
    have hz0 : ∀ i : sigma, z (Sum.inr i) ≠ 0 := by
      intro i
      simpa [s] using hz (Sum.inr i) (Set.mem_univ _)
    rw [eval_mul, eval_C,
      eval_signedMultiaffineReciprocalRight
        (degreeOf_rightComplementMonomial_one_le m) z hz0]
    unfold rightComplementMonomial
    simp only [map_prod, map_pow, map_neg, eval_X]
    have hpoint (i : sigma) :
        (-1 : ℂ) * z (Sum.inr i) *
            (-(z (Sum.inr i))⁻¹) ^ (1 - m.1 i) =
          (-z (Sum.inr i)) ^ m.1 i := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (m.2 i) with hzero | hone
      · simp [hzero, hz0 i]
      · simp [hone]
    calc
      (-1 : ℂ) ^ Fintype.card sigma *
          ((∏ i : sigma, z (Sum.inr i)) *
            ∏ i : sigma,
              (-(z (Sum.inr i))⁻¹) ^ (1 - m.1 i)) =
          ∏ i : sigma,
            ((-1 : ℂ) * z (Sum.inr i) *
              (-(z (Sum.inr i))⁻¹) ^ (1 - m.1 i)) := by
        rw [show (-1 : ℂ) ^ Fintype.card sigma =
            ∏ _i : sigma, (-1 : ℂ) by simp]
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        simp only [mul_assoc]
      _ = ∏ i : sigma, (-z (Sum.inr i)) ^ m.1 i := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hpoint i

/-- The paper-normalized signed reciprocal of the finite algebraic symbol in
the source block.  The factor `(-1) ^ card sigma` is the global sign needed to
turn the exact reciprocal convention into the paper's expansion in `(-w)^m`.
Target variables are unrestricted spectators. -/
theorem paperNormalized_signedMultiaffineReciprocalRight_algebraicSymbol_one
    {sigma tau : Type*} [Fintype sigma]
    (T : degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ] MvPolynomial tau ℂ) :
    C ((-1 : ℂ) ^ Fintype.card sigma) *
        signedMultiaffineReciprocalRight
          (algebraicSymbol (fun _ : sigma => 1) T) =
      ∑ m : {m : sigma →₀ ℕ // ∀ i, m i ≤ 1},
        rename (Sum.inl : tau → tau ⊕ sigma)
            (T (basisDegreeOfLE (R := ℂ) (fun _ : sigma => 1) m)) *
          ∏ i : sigma, (-X (Sum.inr i)) ^ m.1 i := by
  classical
  rw [algebraicSymbol, signedMultiaffineReciprocalRight_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [boxChoose_one m, Nat.cast_one, map_one, one_mul]
  rw [signedMultiaffineReciprocalRight_target_mul]
  · calc
      C ((-1 : ℂ) ^ Fintype.card sigma) *
          (rename Sum.inl
              (T (basisDegreeOfLE (R := ℂ) (fun _ : sigma => 1) m)) *
            signedMultiaffineReciprocalRight
              (rightComplementMonomial (R := ℂ) (τ := tau)
                (fun _ : sigma => 1) m.1)) =
          rename Sum.inl
              (T (basisDegreeOfLE (R := ℂ) (fun _ : sigma => 1) m)) *
            (C ((-1 : ℂ) ^ Fintype.card sigma) *
              signedMultiaffineReciprocalRight
                (rightComplementMonomial (R := ℂ) (τ := tau)
                  (fun _ : sigma => 1) m.1)) := by
        ring
      _ = rename Sum.inl
              (T (basisDegreeOfLE (R := ℂ) (fun _ : sigma => 1) m)) *
            ∏ i : sigma, (-X (Sum.inr i)) ^ m.1 i := by
        rw [normalized_reciprocal_rightComplementMonomial_one m]
  · exact degreeOf_rightComplementMonomial_one_le m

end

end RealRooted.BorceaBranden
