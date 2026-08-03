import RealRooted.Polarization

/-!
# Source polarization for degree-box operators

This file implements the source-side operator lift from Borcea--Brändén,
equation (2.2), for a one-variable degree-`n` source box. The lift first
diagonalizes a multiaffine input and then applies the original operator.
-/

namespace RealRooted.BorceaBranden

noncomputable section

/-- Lift an operator with a one-variable degree-`n` source to a multiaffine
`Fin n` source by precomposing with diagonal projection. -/
def sourcePolarizedOperator {τ : Type*} (n : ℕ)
    (T : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ) :
    MvPolynomial.degreeOfLE (Fin n) ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial τ ℂ :=
  T.comp (diagonalProjectionDegreeBox n)

/-- Source-side equation (2.2): restricting the lifted operator along source
polarization reconstructs the original operator. -/
theorem sourcePolarizedOperator_comp_polarizationDegreeBoxLinearMap
    {τ : Type*} {n : ℕ}
    (T : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ) :
    (sourcePolarizedOperator n T).comp
      (polarizationDegreeBoxLinearMap n) = T := by
  ext q
  change T (diagonalProjectionDegreeBox n
    (polarizationDegreeBoxLinearMap n q)) = T q
  rw [diagonalProjectionDegreeBox_comp_polarizationDegreeBoxLinearMap q]

end

end RealRooted.BorceaBranden
