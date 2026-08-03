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

/-- Partition a sum over subsets of `Fin n` by subset cardinality. -/
theorem sum_finset_eq_sum_powersetCard
    {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : Finset (Fin n) → M) :
    ∑ s, f s =
      ∑ k ∈ Finset.range (n + 1),
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, f s := by
  simpa using
    Finset.sum_powerset (Finset.univ : Finset (Fin n)) f

/-- Summing a cardinality-dependent contribution over subsets of `Fin n`
produces the corresponding binomial coefficients. -/
theorem sum_finset_cardFunction
    {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ∑ s : Finset (Fin n), g s.card =
      ∑ k ∈ Finset.range (n + 1), n.choose k • g k := by
  rw [sum_finset_eq_sum_powersetCard]
  apply Finset.sum_congr rfl
  intro k hk
  simpa using
    Finset.sum_powersetCard k (Finset.univ : Finset (Fin n)) g

/-- The coefficient grouping for multiaffine source exponents: one term for
each zero-one exponent vector becomes `choose n k` copies of the contribution
of total degree `k`. -/
theorem sum_degreeOneExponent_degreeFunction
    {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ∑ m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1}, g m.1.degree =
      ∑ k ∈ Finset.range (n + 1), n.choose k • g k := by
  rw [sum_degreeOneExponent_eq_sum_finset]
  simpa using sum_finset_cardFunction n g

end

end RealRooted.BorceaBranden
