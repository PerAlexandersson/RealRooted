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

namespace MvPolynomial

/-- The coefficient of source degree `k`, after viewing a polynomial in
`tau ⊕ Fin 1` as a polynomial in the single source variable with coefficients
in the output-variable ring `MvPolynomial tau ℂ`. -/
noncomputable def sourceCoefficient {τ : Type*}
    (P : MvPolynomial (τ ⊕ Fin 1) ℂ) (k : ℕ) : MvPolynomial τ ℂ :=
  (sumAlgEquiv ℂ (Fin 1) τ
    (rename (Equiv.sumComm τ (Fin 1)) P)).coeff
      (Finsupp.single default k)

/-- Polarize only the single source variable of a polynomial whose output
variables are indexed by `τ`.

This is the one-source-coordinate instance of Borcea--Brändén's operator
`Π↑` from Proposition 2.4 and Lemma 2.5: the source coefficient of degree `k`
is divided by `choose n k`, and the source monomial is replaced by the
elementary symmetric polynomial `e_k` in the `Fin n` source block. -/
noncomputable def sourceBlockPolarization {τ : Type*} (n : ℕ)
    (P : MvPolynomial (τ ⊕ Fin 1) ℂ) :
    MvPolynomial (τ ⊕ Fin n) ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    C ((n.choose k : ℂ)⁻¹) *
      rename Sum.inl (sourceCoefficient P k) *
        rename Sum.inr (esymm (Fin n) ℂ k)

/-- Identify all polarized source variables while leaving output variables
unchanged. -/
def sourceDiagonalVariableMap {τ : Type*} {n : ℕ} :
    τ ⊕ Fin n → τ ⊕ Fin 1
  | Sum.inl i => Sum.inl i
  | Sum.inr _ => Sum.inr default

/-- Diagonalizing source variables leaves the output-variable block
unchanged. -/
@[simp] theorem rename_sourceDiagonalVariableMap_rename_inl
    {τ : Type*} {n : ℕ} (p : MvPolynomial τ ℂ) :
    rename (sourceDiagonalVariableMap (τ := τ) (n := n))
        (rename (Sum.inl : τ → τ ⊕ Fin n) p) =
      rename (Sum.inl : τ → τ ⊕ Fin 1) p := by
  rw [rename_rename]
  rfl

/-- Diagonalizing a complementary zero-one source monomial records only its
complementary total degree. -/
theorem rename_rightComplementMonomial_one
    {τ : Type*} {n : ℕ} (m : Fin n →₀ ℕ)
    (hm : ∀ i, m i ≤ 1) :
    rename (sourceDiagonalVariableMap (τ := τ) (n := n))
        (rightComplementMonomial (R := ℂ) (τ := τ)
          (fun _ : Fin n => 1) m) =
      X (Sum.inr default) ^ (n - m.degree) := by
  rw [rightComplementMonomial_eq_prod]
  simp only [map_prod, map_pow, rename_X, sourceDiagonalVariableMap]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simpa using Finsupp.sum_one_sub_eq_card_sub_degree m hm

end MvPolynomial

namespace RealRooted.BorceaBranden

noncomputable section

open MvPolynomial

lemma finOneDegreeIndex_degree_eq_diagonalDegreeBoxIndex
    {n : ℕ} (m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1}) :
    finOneDegreeIndex n m.1.degree = diagonalDegreeBoxIndex m := by
  apply (degreeOfLEFinOneEquiv n).injective
  apply Fin.ext
  simp [finOneDegreeIndex, degreeOfLEFinOneEquiv_val,
    diagonalDegreeBoxIndex,
    Nat.min_eq_left (degree_le_fin_card_of_le_one m.1 m.2)]

/-- Termwise form of the source-polarized algebraic symbol after identifying
all polarized source variables. -/
theorem rename_algebraicSymbol_sourcePolarizedOperator_eq_sum
    {τ : Type*} (n : ℕ)
    (T : degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ) :
    MvPolynomial.rename
        (MvPolynomial.sourceDiagonalVariableMap (τ := τ) (n := n))
        (algebraicSymbol (fun _ : Fin n => 1)
          (sourcePolarizedOperator n T)) =
      ∑ m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1},
        rename (Sum.inl : τ → τ ⊕ Fin 1)
            (T (basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => n)
              (diagonalDegreeBoxIndex m))) *
          X (Sum.inr default) ^ (n - m.1.degree) := by
  classical
  rw [algebraicSymbol, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [map_mul, rename_C]
  rw [boxChoose_one_of_le_one m.1 m.2, Nat.cast_one, map_one,
    one_mul, MvPolynomial.rename_sourceDiagonalVariableMap_rename_inl,
    sourcePolarizedOperator_basisDegreeOfLE,
    MvPolynomial.rename_rightComplementMonomial_one m.1 m.2]

/-- Diagonal consequence of the source-side Borcea--Brändén Lemma 2.5 route:
identifying the multiaffine source variables recovers the original degree-box
symbol.  The full Lemma 2.5 identity before diagonalization is strictly
stronger and uses `MvPolynomial.sourceBlockPolarization`. -/
theorem rename_algebraicSymbol_sourcePolarizedOperator
    {τ : Type*} (n : ℕ)
    (T : degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ) :
    MvPolynomial.rename
        (MvPolynomial.sourceDiagonalVariableMap (τ := τ) (n := n))
        (algebraicSymbol (fun _ : Fin n => 1)
          (sourcePolarizedOperator n T)) =
      algebraicSymbol (fun _ : Fin 1 => n) T := by
  classical
  let g : ℕ → MvPolynomial (τ ⊕ Fin 1) ℂ := fun k =>
    rename (Sum.inl : τ → τ ⊕ Fin 1)
        (T (basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => n)
          (finOneDegreeIndex n k))) *
      X (Sum.inr default) ^ (n - k)
  calc
    MvPolynomial.rename
          (MvPolynomial.sourceDiagonalVariableMap (τ := τ) (n := n))
          (algebraicSymbol (fun _ : Fin n => 1)
            (sourcePolarizedOperator n T)) =
        ∑ m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1},
          g m.1.degree := by
      rw [rename_algebraicSymbol_sourcePolarizedOperator_eq_sum]
      apply Finset.sum_congr rfl
      intro m _
      simp only [g]
      rw [finOneDegreeIndex_degree_eq_diagonalDegreeBoxIndex]
    _ = ∑ k ∈ Finset.range (n + 1), n.choose k • g k :=
      sum_degreeOneExponent_degreeFunction n g
    _ = algebraicSymbol (fun _ : Fin 1 => n) T := by
      rw [algebraicSymbol_finOne_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k _
      simp [g, mul_assoc]

end

end RealRooted.BorceaBranden
