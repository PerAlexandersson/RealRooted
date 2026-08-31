import RealRooted.Hadamard.GarloffWagner

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Hurwitz Hadamard reductions

The Hurwitz-stability and Hurwitz-matrix interfaces for Garloff--Wagner
Theorem 1, including the checked low-order reductions.
-/

/-- **Hadamard product preserves Hurwitz stability** (Garloff--Wagner,
Theorem 1) — precise external interface.

This is the main theorem of Garloff--Wagner, *Hadamard Products of Stable
Polynomials Are Stable*: the coefficientwise Hadamard product of two
Hurwitz-stable real polynomials is again Hurwitz stable, provided the
coefficientwise product is nonzero.  The nonzero side condition is part of the
interface because this project's `IsHurwitzStable` convention excludes the zero
polynomial, while coefficientwise products of two nonzero stable polynomials can
vanish when their coefficient supports are disjoint.  This is the genuinely
deep classical input (its classical proofs go through Polya--Schur /
total-nonnegativity machinery that is not available in Mathlib), recorded here
as a precise interface. This is the only new external interface needed below;
the remaining inputs are the Hermite--Biehler odd/even bridges already recorded
in `RealRooted.VeroneseSection`. -/
def hadamardPreservesHurwitzStableStatement : Prop :=
  ∀ {a b : ℝ[X]},
    IsHurwitzStable a →
    IsHurwitzStable b →
    hadamardProduct a b ≠ 0 →
    IsHurwitzStable (hadamardProduct a b)

/-! ### Sharper sub-interfaces for Garloff--Wagner Theorem 1

The Hurwitz-stability conclusion `IsHurwitzStable (hadamardProduct a b)` unfolds
to two parts: nonnegativity of the coefficients and right-half-plane stability
of the complexification.  The first part is elementary
(`HasNonnegCoeffs.hadamardProduct`); the genuinely deep content is the second
part.  We record that split, and the faithful Hurwitz-matrix decomposition of
Garloff--Wagner Theorem 1, as fully checked reductions. -/

/-- The deep half of Garloff--Wagner Theorem 1: the complexified coefficientwise
Hadamard product of two right-half-plane-stable, nonnegative-coefficient
polynomials is again right-half-plane stable when the product is nonzero. -/
def hadamardPreservesRightHalfPlaneStableStatement : Prop :=
  ∀ {a b : ℝ[X]},
    HasNonnegCoeffs a →
    HasNonnegCoeffs b →
    IsRightHalfPlaneStable (complexify a) →
    IsRightHalfPlaneStable (complexify b) →
    hadamardProduct a b ≠ 0 →
    IsRightHalfPlaneStable (complexify (hadamardProduct a b))

/-- Reduction of Garloff--Wagner Theorem 1 to its deep half: the
nonnegative-coefficient half of Hurwitz stability is discharged here, so only
right-half-plane stability of the product remains. -/
theorem hadamardPreservesHurwitzStable_of_rightHalfPlane
    (h : hadamardPreservesRightHalfPlaneStableStatement) :
    hadamardPreservesHurwitzStableStatement :=
  fun ha hb hprod => ⟨ha.1.hadamardProduct hb.1, h ha.1 hb.1 ha.2 hb.2 hprod⟩

/-- The analytic core is conversely implied by Garloff--Wagner Theorem 1, so the
two interfaces are equivalent: isolating the right-half-plane half loses no
content. -/
theorem hadamardPreservesRightHalfPlaneStable_of_hurwitzStable
    (h : hadamardPreservesHurwitzStableStatement) :
    hadamardPreservesRightHalfPlaneStableStatement :=
  fun hann hbnn harhp hbrhp hprod => (h ⟨hann, harhp⟩ ⟨hbnn, hbrhp⟩ hprod).2

/-- Garloff--Wagner Theorem 1 is equivalent to its right-half-plane analytic
core; coefficient nonnegativity of the product is elementary. -/
theorem hadamardPreservesHurwitzStable_iff_rightHalfPlane :
    hadamardPreservesHurwitzStableStatement ↔
      hadamardPreservesRightHalfPlaneStableStatement :=
  ⟨hadamardPreservesRightHalfPlaneStable_of_hurwitzStable,
    hadamardPreservesHurwitzStable_of_rightHalfPlane⟩

/-- The combinatorial heart of Garloff--Wagner Theorem 1, as a pure matrix
statement: total nonnegativity of the row-oriented Hurwitz matrix is preserved
under coefficientwise products. -/
def hadamardPreservesHurwitzMatrixTNStatement : Prop :=
  ∀ {a b : ℝ[X]},
    (hurwitz a.coeff).IsTotallyNonneg →
    (hurwitz b.coeff).IsTotallyNonneg →
    (hurwitz (hadamardProduct a b).coeff).IsTotallyNonneg

/-- Hurwitz-matrix form of the coefficientwise Hadamard product of two
polynomials. -/
theorem hurwitz_hadamardProduct_matrix (a b : ℝ[X]) :
    hurwitz (hadamardProduct a b).coeff =
      Matrix.of fun i j => hurwitz a.coeff i j * hurwitz b.coeff i j := by
  rw [show (hadamardProduct a b).coeff = fun n => a.coeff n * b.coeff n by
    funext n
    exact coeff_hadamardProduct a b n]
  exact hurwitz_mul_entrywise_matrix a.coeff b.coeff

/-- Low-order checked part of the Hurwitz-matrix Hadamard leaf: every minor of
size at most two is nonnegative.  The first remaining case for
`hadamardPreservesHurwitzMatrixTNStatement` is the `3 × 3` Hurwitz-specific
minor. -/
theorem hadamardPreservesHurwitzMatrixTN_det_of_card_le_two
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg)
    {n : ℕ} {rows cols : Fin n → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hn : n ≤ 2) :
    0 ≤ (((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det) := by
  simpa [hurwitz_hadamardProduct_matrix] using
    hurwitz_schurProduct_det_of_card_le_two ha hb hrows hcols hn

/-- Structural `3 × 3` band-fail case for the Hurwitz matrix of a Hadamard
product.  This is the polynomial-facing form of
`hurwitz_schurProduct_det_fin_three_of_band_fail`. -/
theorem hurwitz_hadamardProduct_det_fin_three_of_band_fail
    {a b : ℝ[X]} {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows)
    (hcols : StrictMono cols) (l : Fin 3) (hl : rows l < 2 * cols l) :
    ((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det = 0 := by
  simpa [hurwitz_hadamardProduct_matrix] using
    hurwitz_schurProduct_det_fin_three_of_band_fail hrows hcols l hl

/-- Nonnegativity form of the structural `3 × 3` band-fail case for the
Hurwitz matrix of a Hadamard product. -/
theorem hurwitz_hadamardProduct_det_fin_three_nonneg_of_band_fail
    {a b : ℝ[X]} {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows)
    (hcols : StrictMono cols) (l : Fin 3) (hl : rows l < 2 * cols l) :
    0 ≤ ((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det := by
  rw [hurwitz_hadamardProduct_det_fin_three_of_band_fail hrows hcols l hl]

/-- `3 × 3` Hurwitz-matrix Hadamard minors from the pure in-band `3 × 3`
matrix core.  The out-of-band case is handled structurally by the
band-fail zero lemma. -/
theorem hadamardPreservesHurwitzMatrixTN_det_fin_three
    (hInBand : HurwitzMatrixSchurProductDetFinThreeInBandStatement)
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg)
    {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 ≤ ((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det := by
  simpa [hurwitz_hadamardProduct_matrix] using
    hurwitz_schurProduct_det_fin_three hInBand ha hb hrows hcols

/-- Low-order checked part of the Hurwitz-matrix Hadamard leaf through size
three, assuming the pure in-band `3 × 3` matrix core. -/
theorem hadamardPreservesHurwitzMatrixTN_det_of_card_le_three
    (hInBand : HurwitzMatrixSchurProductDetFinThreeInBandStatement)
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg)
    {n : ℕ} {rows cols : Fin n → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hn : n ≤ 3) :
    0 ≤ (((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det) := by
  simpa [hurwitz_hadamardProduct_matrix] using
    hurwitz_schurProduct_det_of_card_le_three hInBand ha hb hrows hcols hn

/-- Low-order, size-`≤ 3`, form of the Hurwitz-matrix Hadamard leaf. -/
def hadamardPreservesHurwitzMatrixTNDetLeThreeStatement : Prop :=
  ∀ {a b : ℝ[X]},
    (hurwitz a.coeff).IsTotallyNonneg →
    (hurwitz b.coeff).IsTotallyNonneg →
    ∀ {n : ℕ} {rows cols : Fin n → ℕ},
      StrictMono rows →
      StrictMono cols →
      n ≤ 3 →
      0 ≤ (((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det)

/-- The isolated in-band `3 × 3` core implies the low-order, size-`≤ 3`,
Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_inBand
    (hInBand : HurwitzMatrixSchurProductDetFinThreeInBandStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  @hadamardPreservesHurwitzMatrixTN_det_of_card_le_three hInBand

/-- The fully in-band top-right subcase of the `3 × 3` Hurwitz Schur-product
core implies the low-order, size-`≤ 3`, Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_fullBand
    (hF : HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_inBand
    (hurwitzMatrixSchurProductDetFinThreeInBand_of_fullBand hF)

/-- The single-matrix corner-zeroed determinant subtarget implies the
low-order, size-`≤ 3`, Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingle
    (hSingle :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_inBand
    (hurwitzMatrixSchurProductDetFinThreeInBand_of_cornerZeroedSingle hSingle)

/-- The column-normalized single-matrix corner-zeroed determinant subtarget
implies the low-order, size-`≤ 3`, Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleColZero
    (hZero :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingle
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingle_of_colZero hZero)

/-- The first-column normal form implies the low-order, size-`≤ 3`,
Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleFirstCol
    (hFirst :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleColZero
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_firstCol
      hFirst)

/-- The strict-remainder first-column branch implies the low-order,
size-`≤ 3`, Hurwitz-matrix Hadamard leaf. -/
theorem
    hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleFirstColPositiveRemainder
    (hPos : HurwitzMatrixSchurProductDetFirstColPositiveRemainderStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleFirstCol
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_positiveRemainder
      hPos)

/-- The pure size-`≤ 3` Hurwitz matrix Schur-product statement implies the
Hadamard-product Hurwitz-matrix size-`≤ 3` statement. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_hurwitzLeThree
    (hLeThree : HurwitzMatrixSchurProductDetLeThreeStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  fun {_a _b} ha hb {_n} {_rows} {_cols} hrows hcols hn => by
    simpa [hurwitz_hadamardProduct_matrix] using hLeThree ha hb hrows hcols hn

/-- The full Hurwitz-matrix Hadamard leaf implies its named low-order,
size-`≤ 3`, consequence. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_matrixTN
    (h : hadamardPreservesHurwitzMatrixTNStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  fun {_a _b} ha hb {_n} {_rows} {_cols} hrows hcols _hn => h ha hb hrows hcols

/-- Odd/even coefficient-subsequence PF consequence of the Hurwitz-matrix
Hadamard leaf. -/
def hadamardPreservesHurwitzMatrixOddEvenPFStatement : Prop :=
  ∀ {a b : ℝ[X]},
    (hurwitz a.coeff).IsTotallyNonneg →
    (hurwitz b.coeff).IsTotallyNonneg →
    IsPolyaFreqSeq (fun n => (hadamardProduct a b).coeff (2 * n + 1)) ∧
      IsPolyaFreqSeq (fun n => (hadamardProduct a b).coeff (2 * n))

/-- The Hurwitz-matrix Hadamard leaf makes the odd coefficient subsequence of
the Hadamard product Pólya-frequency. -/
theorem hadamardProduct_oddCoeff_isPolyaFreqSeq_of_matrixTN
    (h : hadamardPreservesHurwitzMatrixTNStatement)
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg) :
    IsPolyaFreqSeq (fun n => (hadamardProduct a b).coeff (2 * n + 1)) :=
  hurwitz_isPolyaFreqSeq_odd (h ha hb)

/-- The Hurwitz-matrix Hadamard leaf makes the even coefficient subsequence of
the Hadamard product Pólya-frequency. -/
theorem hadamardProduct_evenCoeff_isPolyaFreqSeq_of_matrixTN
    (h : hadamardPreservesHurwitzMatrixTNStatement)
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg) :
    IsPolyaFreqSeq (fun n => (hadamardProduct a b).coeff (2 * n)) :=
  hurwitz_isPolyaFreqSeq_even (h ha hb)

/-- Bundled odd/even PF consequence of the Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixOddEvenPF_of_matrixTN
    (h : hadamardPreservesHurwitzMatrixTNStatement) :
    hadamardPreservesHurwitzMatrixOddEvenPFStatement :=
  fun ha hb =>
    ⟨hurwitz_isPolyaFreqSeq_odd (h ha hb),
      hurwitz_isPolyaFreqSeq_even (h ha hb)⟩
end RealRooted
