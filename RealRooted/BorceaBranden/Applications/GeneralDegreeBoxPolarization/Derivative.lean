import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization
import RealRooted.LiebSokalPointwise
import RealRooted.Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Partial derivatives through general degree-box polarization

This file uses block symmetry and the derivative chain rule for noninjective
renamings to transport partial derivatives through blockwise polarization.
-/

open scoped BigOperators

namespace RealRooted.BorceaBranden

noncomputable section

private theorem pderiv_rename_fst_eq_smul_clone
    {σ : Type*} [Finite σ] (κ : σ → ℕ)
    (Q : MvPolynomial (PolarizedSource κ) ℂ)
    (hsym : ∀ e : ∀ i, Equiv.Perm (Fin (κ i)),
      MvPolynomial.rename (Equiv.Perm.sigmaCongrRight e) Q = Q)
    (i : σ) (hki : 0 < κ i) :
    MvPolynomial.pderiv i (MvPolynomial.rename Sigma.fst Q) =
      (κ i : ℂ) • MvPolynomial.rename Sigma.fst
        (MvPolynomial.pderiv ⟨i, ⟨0, hki⟩⟩ Q) := by
  classical
  letI := Fintype.ofFinite σ
  rw [MvPolynomial.pderiv_rename_eq_sum_fiber]
  simp only [Finset.sum_filter, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp_rw [show ∀ j : Fin (κ i),
        MvPolynomial.rename Sigma.fst (MvPolynomial.pderiv ⟨i, j⟩ Q) =
          MvPolynomial.rename Sigma.fst
            (MvPolynomial.pderiv ⟨i, ⟨0, hki⟩⟩ Q) from fun j =>
      rename_pderiv_block_clone_eq κ Q hsym i j ⟨0, hki⟩]
    rw [MvPolynomial.smul_eq_C_mul]
    simp
  · intro j _ hji
    simp [hji]
  · simp

/-- Differentiating a polynomial in one coordinate agrees with differentiating
one clone of its blockwise polarization, diagonally projecting, and multiplying
by the number of clones. -/
theorem pderiv_eq_smul_rename_pderiv_blockwisePolarizationDegreeBoxGeneral
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (p : MvPolynomial.degreeOfLE σ ℂ κ) (i : σ) (hki : 0 < κ i) :
    MvPolynomial.pderiv i p.1 =
      (κ i : ℂ) • MvPolynomial.rename Sigma.fst
        (MvPolynomial.pderiv ⟨i, ⟨0, hki⟩⟩
          (blockwisePolarizationDegreeBoxGeneral κ p).1) := by
  have hsection := congrArg Subtype.val
    (diagonalProjectionDegreeBoxGeneral_blockwisePolarization κ p)
  rw [coe_diagonalProjectionDegreeBoxGeneral] at hsection
  rw [← hsection]
  apply pderiv_rename_fst_eq_smul_clone κ
  exact rename_blockwisePolarizationDegreeBoxGeneral_sigmaCongrRight κ p

/-- Over finitely many variables, an arbitrary partial derivative of a stable
polynomial is either zero or stable. -/
theorem _root_.RealRooted.MvUpperHalfPlaneStable.pderiv_zero_or_of_finite
    {σ : Type*} [Finite σ] {P : MvPolynomial σ ℂ}
    (hP : MvUpperHalfPlaneStable P) (i : σ) :
    MvPolynomial.pderiv i P = 0 ∨
      MvUpperHalfPlaneStable (MvPolynomial.pderiv i P) := by
  classical
  letI := Fintype.ofFinite σ
  let κ : σ → ℕ := fun j => P.degreeOf j
  let p : MvPolynomial.degreeOfLE σ ℂ κ :=
    ⟨P, (MvPolynomial.mem_degreeOfLE_iff_degreeOf P).2 fun _ => le_rfl⟩
  by_cases hki : κ i = 0
  · left
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    rwa [MvPolynomial.mem_vars_iff_degreeOf_ne_zero, not_not]
  · have hkiPos : 0 < κ i := Nat.pos_of_ne_zero hki
    let Q := blockwisePolarizationDegreeBoxGeneral κ p
    have hQstable : MvUpperHalfPlaneStable Q.1 :=
      mvUpperHalfPlaneStable_blockwisePolarizationDegreeBoxGeneral κ p hP
    have hQma : MvPolynomial.IsMultiaffine Q.1 :=
      (MvPolynomial.mem_degreeOfLE_iff_degreeOf Q.1).mp Q.2
    have hclone : MvUpperHalfPlaneStableOrZero
        (MvPolynomial.pderiv ⟨i, ⟨0, hkiPos⟩⟩ Q.1) :=
      hQstable.pderiv_zero_or hQma ⟨i, ⟨0, hkiPos⟩⟩
    have hscaled := (hclone.rename Sigma.fst).C_mul (κ i : ℂ)
    dsimp [Q] at hscaled
    rw [pderiv_eq_smul_rename_pderiv_blockwisePolarizationDegreeBoxGeneral
      κ p i hkiPos]
    simpa only [MvPolynomial.smul_eq_C_mul, MvUpperHalfPlaneStableOrZero] using hscaled

end

end RealRooted.BorceaBranden
