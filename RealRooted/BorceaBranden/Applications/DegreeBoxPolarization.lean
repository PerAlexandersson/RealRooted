import RealRooted.BorceaBranden.FiniteSymbolBasis
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

/-- The source-polarized operator sends a multiaffine basis monomial to the
original operator applied to the one-variable basis monomial of the same total
degree. This is the basis-level content of Borcea--Branden Lemma 2.5. -/
theorem sourcePolarizedOperator_basisDegreeOfLE
    {τ : Type*} {n : ℕ}
    (T : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ)
    (m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1}) :
    sourcePolarizedOperator n T
        (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ : Fin n => 1) m) =
      T (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => n)
        (diagonalDegreeBoxIndex m)) := by
  change T (diagonalProjectionDegreeBox n
    (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ : Fin n => 1) m)) = _
  rw [diagonalProjectionDegreeBox_basisDegreeOfLE]

/-- Reindex a sum over multiaffine exponent vectors by their finite supports.
This is the subset reindexing in the source-side proof of Lemma 2.5. -/
theorem sum_degreeOneExponent_eq_sum_finset
    {M : Type*} [AddCommMonoid M] {n : ℕ}
    (f : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1} → M) :
    ∑ m, f m =
      ∑ s : Finset (Fin n),
        f ((degreeOneExponentEquivFinset (Fin n)).symm s) := by
  apply Fintype.sum_equiv (degreeOneExponentEquivFinset (Fin n))
  intro m
  simp

end

end RealRooted.BorceaBranden
