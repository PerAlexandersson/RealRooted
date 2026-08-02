import RealRooted.BorceaBranden.FiniteSymbolBasis
import RealRooted.BorceaBranden.FiniteSymbolCoefficient
import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.DegreeBox

/-!
# Reconstruction coefficients for the finite-symbol argument

This module isolates two algebraic steps from Borcea--Branden,
arXiv:0809.0401, Lemma 2.2: squarefree derivatives evaluated at zero recover
coefficients, and specializing an independent right block to zero evaluates
that block at zero.  Target variables remain unrestricted.
-/

namespace RealRooted.BorceaBranden

noncomputable section

/-- For a multiaffine polynomial, the squarefree derivative indexed by `m`,
evaluated at zero, is the coefficient of the monomial indexed by `m`.  This is
the derivative-at-zero coefficient step in Borcea--Branden, Lemma 2.2. -/
theorem eval_zero_applyMonomialDifferential_oneBox
    {sigma : Type*} [Fintype sigma]
    (f : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1))
    (m : {m : sigma →₀ ℕ // ∀ i, m i ≤ 1}) :
    MvPolynomial.eval (fun _ : sigma => 0)
        (applyMonomialDifferential m.1 f.1) =
      MvPolynomial.coeff m.1 f.1 := by
  classical
  let lhs :
      MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ] ℂ :=
    { toFun := fun g =>
        MvPolynomial.eval (fun _ : sigma => 0)
          (applyMonomialDifferential m.1 g.1)
      map_add' := by
        intro g h
        simp [applyMonomialDifferential_add]
      map_smul' := by
        intro c g
        simp [Algebra.smul_def, applyMonomialDifferential_C_mul] }
  let rhs :
      MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ] ℂ :=
    { toFun := fun g => MvPolynomial.coeff m.1 g.1
      map_add' := by
        intro g h
        simp
      map_smul' := by
        intro c g
        simp }
  change lhs f = rhs f
  apply LinearMap.congr_fun ?_ f
  apply (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ : sigma => 1)).ext
  intro n
  change MvPolynomial.eval (fun _ : sigma => 0)
      (applyMonomialDifferential m.1
        (MvPolynomial.basisDegreeOfLE
          (R := ℂ) (fun _ : sigma => 1) n).1) =
    MvPolynomial.coeff m.1
      (MvPolynomial.basisDegreeOfLE
        (R := ℂ) (fun _ : sigma => 1) n).1
  rw [MvPolynomial.coe_basisDegreeOfLE]
  by_cases hsupport : m.1.support = n.1.support
  · have hmn : m.1 = n.1 :=
      (finsupp_eq_iff_support_eq_of_le_one
        m.1 n.1 m.2 n.2).2 hsupport
    have hmnSubtype : m = n := Subtype.ext hmn
    subst n
    rw [finsupp_eq_indicator_support_of_le_one m.1 m.2,
      applyMonomialDifferential_indicator_monomial]
    simp
  · have hmn : m.1 ≠ n.1 := by
      intro h
      exact hsupport (congrArg Finsupp.support h)
    have hrhs :
        MvPolynomial.coeff m.1 (MvPolynomial.monomial n.1 (1 : ℂ)) = 0 := by
      simp [hmn]
    rw [hrhs, finsupp_eq_indicator_support_of_le_one m.1 m.2,
      finsupp_eq_indicator_support_of_le_one n.1 n.2,
      applyMonomialDifferential_indicator_monomial]
    by_cases hsubset : m.1.support ⊆ n.1.support
    · rw [if_pos hsubset]
      have hdiff : n.1.support \ m.1.support ≠ ∅ := by
        intro h
        have hnsub : n.1.support ⊆ m.1.support :=
          Finset.sdiff_eq_empty_iff_subset.mp h
        exact hsupport (Finset.Subset.antisymm hsubset hnsub)
      have hindicator :
          Finsupp.indicator (n.1.support \ m.1.support)
              (fun _ _ => 1) ≠ (0 : sigma →₀ ℕ) := by
        intro hzero
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hdiff
        have hvalue := congrArg (fun d : sigma →₀ ℕ => d i) hzero
        simp [Finsupp.indicator_of_mem hi] at hvalue
      simp [MvPolynomial.eval_zero', hindicator]
    · rw [if_neg hsubset]
      simp

/-- Specializing the right block to zero evaluates a polynomial supported in
that block at zero, while leaving an unrestricted target polynomial unchanged.
-/
theorem specializeRight_zero_targetMul_input
    {sigma tau : Type*}
    (A : MvPolynomial tau ℂ) (D : MvPolynomial sigma ℂ) :
    specializeRight (fun _ : sigma => 0)
        (MvPolynomial.rename Sum.inl A *
          MvPolynomial.rename Sum.inr D) =
      A * MvPolynomial.C
        (MvPolynomial.eval (fun _ : sigma => 0) D) := by
  classical
  unfold specializeRight
  rw [map_mul]
  congr 1
  · rw [MvPolynomial.aeval_rename]
    induction A using MvPolynomial.induction_on with
    | C c => simp
    | add P Q hP hQ => simp [hP, hQ]
    | mul_X P i hP => simp [hP]
  · rw [MvPolynomial.aeval_rename]
    induction D using MvPolynomial.induction_on with
    | C c => simp
    | add P Q hP hQ => simp [hP, hQ]
    | mul_X P i hP => simp [hP]

end

end RealRooted.BorceaBranden
