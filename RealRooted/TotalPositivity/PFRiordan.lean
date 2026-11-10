module

public import RealRooted.TotalPositivity.LeftProductionMatrix
public import RealRooted.BrandenVecchi.SupersymmetricCoefficients
public import RealRooted.BrandenLeite.TwoKernelAlgebra
import RealRooted.PolyaFrequencyConvolution.Basic
import RealRooted.AissenSchoenbergWhitney
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
import RealRooted.BrandenLeite.CompositionRow
import RealRooted.BrandenVecchi.ChowZeroPrefix

/-!
# Pólya-frequency Riordan arrays

We specialize the left-production theorem to the ordinary Riordan array

`[z^n] d(z) (z d(z) K(z))^k`.

Its left production matrix is the product of the lower Toeplitz matrix of `d`
and the block diagonal matrix `diag(1, T(K))`.  Thus PF coefficient sequences
`d` and `K` give PF rows, hence row polynomials which split with nonpositive
roots.  We also package finite rational PF products and a coefficient-recurrence
interface for applications.

Reference: X. Chen, L. Fu, and J. Ruan, *A unified planar network approach to
total positivity of combinatorial matrices and real-rootedness of polynomials*,
Theorems 1.3 and 1.4, arXiv:2512.08369.
-/

@[expose] public section

open Matrix Polynomial BigOperators

noncomputable section

namespace RealRooted
namespace PFRiordan

/-- The left production matrix of the Riordan array associated with
`(d, z d K)`, in entrywise form. -/
def production (d K : ℕ → ℝ) (n k : ℕ) : ℝ :=
  if k = 0 then d n
  else if k ≤ n then
    PowerSeries.coeff (n - k) (PowerSeries.mk d * PowerSeries.mk K)
  else 0

/-- The Riordan array whose `k`th column has generating series
`d(z) (z d(z) K(z))^k`. -/
def array (d K : ℕ → ℝ) (n k : ℕ) : ℝ :=
  PowerSeries.coeff n
    (PowerSeries.mk d ^ (k + 1) *
      (PowerSeries.X * PowerSeries.mk K) ^ k)

/-- The matrix `diag(1, T(K))` occurring in the production factorization. -/
def oneToeplitz (K : ℕ → ℝ) : LowerTriangularMatrix ℝ :=
  LeftProductionMatrix.prefixIdentity (toeplitz K) 1

/-- A lower Toeplitz matrix, regarded as an infinite lower-triangular matrix. -/
def lowerToeplitz (d : ℕ → ℝ) : LowerTriangularMatrix ℝ :=
  fun i j => toeplitz d i j

/-- A lower Toeplitz matrix is lower triangular. -/
theorem toeplitz_isLowerTriangular (d : ℕ → ℝ) :
    LowerTriangularMatrix.IsLowerTriangular (lowerToeplitz d) := by
  intro i j hij
  simp [lowerToeplitz, toeplitz_apply, not_le_of_gt hij]

/-- The block matrix `diag(1, T(K))` is lower triangular. -/
theorem oneToeplitz_isLowerTriangular (K : ℕ → ℝ) :
    LowerTriangularMatrix.IsLowerTriangular (oneToeplitz K) := by
  intro i j hij
  by_cases hi : i < 1
  · simp [oneToeplitz, LeftProductionMatrix.prefixIdentity, hi,
      Nat.ne_of_lt hij]
  · have hj : ¬j < 1 := fun hj => hi (hij.trans hj)
    have hsub : ¬j - 1 ≤ i - 1 := by lia
    simp [oneToeplitz, LeftProductionMatrix.prefixIdentity, hi, hj,
      toeplitz_apply, hsub]

/-- The entrywise production matrix is exactly
`T(d) · diag(1, T(K))`. -/
theorem production_eq_toeplitz_mul_oneToeplitz (d K : ℕ → ℝ) :
    production d K =
      LowerTriangularMatrix.mul (lowerToeplitz d) (oneToeplitz K) := by
  funext n k
  by_cases hkn : k ≤ n
  · cases k with
    | zero =>
        rw [production, ite_eq_left rfl, LowerTriangularMatrix.mul_apply]
        rw [Finset.sum_eq_single 0]
        · simp [lowerToeplitz, oneToeplitz, toeplitz_apply]
        · intro b hb hb0
          simp [lowerToeplitz, oneToeplitz,
            LeftProductionMatrix.prefixIdentity, hb0]
        · simp [hkn]
    | succ k =>
        rw [production, ite_eq_right (Nat.succ_ne_zero k), ite_eq_left hkn,
          LowerTriangularMatrix.mul_apply]
        simp only [lowerToeplitz, toeplitz_apply]
        rw [← Finset.Ico_add_one_right_eq_Icc]
        rw [Finset.sum_Ico_eq_sum_range]
        have hsize : n + 1 - (k + 1) = n - (k + 1) + 1 := by lia
        rw [hsize]
        rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp only [PowerSeries.coeff_mk]
        rw [← Finset.sum_range_reflect]
        apply Finset.sum_congr rfl
        intro t ht
        have ht' : t ≤ n - (k + 1) := by
          have := Finset.mem_range.mp ht
          lia
        rw [oneToeplitz,
          LeftProductionMatrix.prefixIdentity_apply_ge _ (by lia) (by lia)]
        rw [toeplitz_apply, ite_eq_left (by lia)]
        simp only [Nat.succ_sub_one]
        have hleft :
            n - (k + 1) - (n - (k + 1) - t) = t :=
          Nat.sub_sub_self ht'
        rw [hleft, ite_eq_left (by lia)]
        congr 2 <;> lia
  · have hnk : n < k := Nat.lt_of_not_ge hkn
    rw [production, ite_eq_right (by lia), ite_eq_right hkn,
      LowerTriangularMatrix.mul_apply]
    have hempty : Finset.Icc k n = ∅ := by
      ext x
      simp
      lia
    rw [hempty]
    simp

/-- The Riordan array is lower triangular. -/
theorem array_isLowerTriangular (d K : ℕ → ℝ) :
    LowerTriangularMatrix.IsLowerTriangular (array d K) := by
  intro n k hnk
  apply BrandenLeite.coeff_twoKernelTerm_eq_zero_of_lt
    (g := PowerSeries.mk d) (h := PowerSeries.X * PowerSeries.mk K)
  · simp
  · exact hnk

/-- The successor-column coefficient is the causal convolution used by the
left-production recursion. -/
theorem array_succ_succ (d K : ℕ → ℝ) (n k : ℕ) :
    array d K (n + 1) (k + 1) =
      PowerSeries.coeff n
        ((PowerSeries.mk d ^ (k + 1) *
            (PowerSeries.X * PowerSeries.mk K) ^ k) *
          (PowerSeries.mk d * PowerSeries.mk K)) := by
  rw [array]
  have hseries :
      PowerSeries.mk d ^ (k + 1 + 1) *
          (PowerSeries.X * PowerSeries.mk K) ^ (k + 1) =
        PowerSeries.X *
          ((PowerSeries.mk d ^ (k + 1) *
              (PowerSeries.X * PowerSeries.mk K) ^ k) *
            (PowerSeries.mk d * PowerSeries.mk K)) := by
    rw [pow_succ (PowerSeries.mk d) (k + 1),
      pow_succ (PowerSeries.X * PowerSeries.mk K) k]
    ac_rfl
  rw [hseries, PowerSeries.coeff_succ_X_mul]

/-- The Riordan array of `(d, z d K)` is generated by its stated left
production matrix. -/
theorem isLeftProductionArray (d K : ℕ → ℝ) :
    IsLeftProductionArray (production d K) (array d K) := by
  refine ⟨?_, ?_, array_isLowerTriangular d K⟩
  · intro n
    simp [array, production]
  · intro n k
    rw [array_succ_succ]
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    symm
    let f : ℕ → ℝ := fun j =>
      PowerSeries.coeff j
          (PowerSeries.mk d ^ (k + 1) *
            (PowerSeries.X * PowerSeries.mk K) ^ k) *
        PowerSeries.coeff (n - j)
          (PowerSeries.mk d * PowerSeries.mk K)
    calc
      (∑ j ∈ Finset.Icc k n,
          production d K (n + 1) (j + 1) * array d K j k) =
          ∑ j ∈ Finset.Icc k n, f j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [production, ite_eq_right (Nat.succ_ne_zero j),
              ite_eq_left (by
                have := (Finset.mem_Icc.mp hj).2
                lia)]
            simp only [array, f]
            have hjn := (Finset.mem_Icc.mp hj).2
            have hsub : n + 1 - (j + 1) = n - j := by lia
            rw [hsub]
            ring
      _ = ∑ j ∈ Finset.range (n + 1), f j := by
        apply Finset.sum_subset
        · intro j hj
          exact Finset.mem_range.mpr (by
            have := (Finset.mem_Icc.mp hj).2
            lia)
        · intro j hjRange hjIcc
          have hjn : j ≤ n := by
            have := Finset.mem_range.mp hjRange
            lia
          have hjk : j < k := by
            by_contra h
            exact hjIcc (Finset.mem_Icc.mpr ⟨Nat.le_of_not_gt h, hjn⟩)
          change array d K j k *
            PowerSeries.coeff (n - j)
              (PowerSeries.mk d * PowerSeries.mk K) = 0
          rw [array_isLowerTriangular d K hjk]
          simp
      _ = ∑ x ∈ Finset.range n.succ,
          PowerSeries.coeff x
              (PowerSeries.mk d ^ (k + 1) *
                (PowerSeries.X * PowerSeries.mk K) ^ k) *
            PowerSeries.coeff (n - x)
              (PowerSeries.mk d * PowerSeries.mk K) := by
        rfl

/-- The Riordan production matrix is lower triangular. -/
theorem production_isLowerTriangular (d K : ℕ → ℝ) :
    LowerTriangularMatrix.IsLowerTriangular (production d K) := by
  rw [production_eq_toeplitz_mul_oneToeplitz]
  exact LowerTriangularMatrix.IsLowerTriangular.mul
    (B := oneToeplitz K) (toeplitz_isLowerTriangular d)

/-- PF coefficient sequences make every leading truncation of the Riordan
production matrix totally nonnegative. -/
theorem production_hasTotallyNonnegativeLeadingTruncations
    {d K : ℕ → ℝ} (hd : IsPolyaFreqSeq d) (hK : IsPolyaFreqSeq K) :
    HasTotallyNonnegativeLeadingTruncations (production d K) := by
  intro N
  rw [production_eq_toeplitz_mul_oneToeplitz]
  change
    (Matrix.submatrix
      (Matrix.of
        (LowerTriangularMatrix.mul (lowerToeplitz d) (oneToeplitz K)))
      (Fin.val : Fin (N + 1) → ℕ)
      (Fin.val : Fin (N + 1) → ℕ)).IsTotallyNonneg
  rw [LeftProductionMatrix.truncation_mul
    (toeplitz_isLowerTriangular d) (oneToeplitz_isLowerTriangular K)]
  apply Matrix.IsTotallyNonneg.mul
  · have hd' :
        ((toeplitz d).submatrix
          (Fin.val : Fin (N + 1) → ℕ)
          (Fin.val : Fin (N + 1) → ℕ)).IsTotallyNonneg :=
      hd.submatrix Fin.val_strictMono Fin.val_strictMono
    convert hd' using 1
    ext i j
    rfl
  · exact LeftProductionMatrix.prefixIdentity_fin_isTotallyNonneg
      hK 1 (N + 1)

/-- The polynomial whose coefficients are row `n` of the Riordan array. -/
def rowPolynomial (d K : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  LeftProductionMatrix.rowPolynomial (array d K) n

/-- The row polynomial has the literal Riordan-array coefficients. -/
theorem coeff_rowPolynomial (d K : ℕ → ℝ) (n k : ℕ) :
    (rowPolynomial d K n).coeff k = array d K n k :=
  LeftProductionMatrix.coeff_rowPolynomial (isLeftProductionArray d K) n k

/-- The Riordan row is the literal two-kernel coefficient row. -/
theorem rowPolynomial_eq_twoKernelRow (d K : ℕ → ℝ) (n : ℕ) :
    rowPolynomial d K n =
      BrandenLeite.twoKernelRow (PowerSeries.mk d)
        (PowerSeries.X * PowerSeries.mk K) n := by
  ext k
  rw [coeff_rowPolynomial,
    BrandenLeite.coeff_twoKernelRow (by simp)]
  rfl

/-- The polynomial-valued generating series of the Riordan rows. -/
def rowGeneratingSeries (d K : ℕ → ℝ) : PowerSeries ℝ[X] :=
  PowerSeries.mk (rowPolynomial d K)

/-- The row-generating series is the literal two-kernel series. -/
theorem rowGeneratingSeries_eq_twoKernelGeneratingSeries
    (d K : ℕ → ℝ) :
    rowGeneratingSeries d K =
      BrandenLeite.twoKernelGeneratingSeries (PowerSeries.mk d)
        (PowerSeries.X * PowerSeries.mk K) := by
  apply PowerSeries.ext
  intro n
  simp [rowGeneratingSeries, rowPolynomial_eq_twoKernelRow]

/-- Clearing scalar denominators gives the exact polynomial-valued generating
series identity behind the recurrence-family theorem. -/
theorem denominator_mul_rowGeneratingSeries
    {D₀ L N d K : ℕ → ℝ}
    (hdIdentity : PowerSeries.mk D₀ * PowerSeries.mk d = PowerSeries.mk N)
    (hKIdentity :
      PowerSeries.X * PowerSeries.mk N * PowerSeries.mk K =
        PowerSeries.mk L) :
    (BrandenLeite.polynomialLift (PowerSeries.mk D₀) -
        PowerSeries.C X * BrandenLeite.polynomialLift (PowerSeries.mk L)) *
      rowGeneratingSeries d K =
        BrandenLeite.polynomialLift (PowerSeries.mk N) := by
  have hscalar :
      PowerSeries.mk D₀ *
          (PowerSeries.mk d *
            (PowerSeries.X * PowerSeries.mk K)) =
        PowerSeries.mk L := by
    calc
      PowerSeries.mk D₀ *
          (PowerSeries.mk d *
            (PowerSeries.X * PowerSeries.mk K)) =
          (PowerSeries.mk D₀ * PowerSeries.mk d) *
            (PowerSeries.X * PowerSeries.mk K) := by rw [mul_assoc]
      _ = PowerSeries.mk N *
            (PowerSeries.X * PowerSeries.mk K) := by rw [hdIdentity]
      _ = PowerSeries.X * PowerSeries.mk N *
            PowerSeries.mk K := by ring
      _ = PowerSeries.mk L := hKIdentity
  rw [rowGeneratingSeries_eq_twoKernelGeneratingSeries]
  have hbase := BrandenLeite.one_sub_mul_twoKernelGeneratingSeries
    (g := PowerSeries.mk d)
    (h := PowerSeries.X * PowerSeries.mk K) (by simp)
  calc
    (BrandenLeite.polynomialLift (PowerSeries.mk D₀) -
          PowerSeries.C X * BrandenLeite.polynomialLift (PowerSeries.mk L)) *
        BrandenLeite.twoKernelGeneratingSeries (PowerSeries.mk d)
          (PowerSeries.X * PowerSeries.mk K) =
      BrandenLeite.polynomialLift (PowerSeries.mk D₀) *
        ((1 - PowerSeries.C X *
            BrandenLeite.polynomialLift
              (PowerSeries.mk d *
                (PowerSeries.X * PowerSeries.mk K))) *
          BrandenLeite.twoKernelGeneratingSeries (PowerSeries.mk d)
            (PowerSeries.X * PowerSeries.mk K)) := by
      rw [← mul_assoc]
      congr 1
      symm
      calc
        BrandenLeite.polynomialLift (PowerSeries.mk D₀) *
            (1 - PowerSeries.C X *
              BrandenLeite.polynomialLift
                (PowerSeries.mk d *
                  (PowerSeries.X * PowerSeries.mk K))) =
          BrandenLeite.polynomialLift (PowerSeries.mk D₀) -
            PowerSeries.C X *
              (BrandenLeite.polynomialLift (PowerSeries.mk D₀) *
                BrandenLeite.polynomialLift
                  (PowerSeries.mk d *
                    (PowerSeries.X * PowerSeries.mk K))) := by ring
        _ = BrandenLeite.polynomialLift (PowerSeries.mk D₀) -
            PowerSeries.C X *
              BrandenLeite.polynomialLift
                (PowerSeries.mk D₀ *
                  (PowerSeries.mk d *
                    (PowerSeries.X * PowerSeries.mk K))) := by
          rw [← BrandenLeite.polynomialLift_mul]
        _ = BrandenLeite.polynomialLift (PowerSeries.mk D₀) -
            PowerSeries.C X *
              BrandenLeite.polynomialLift (PowerSeries.mk L) := by rw [hscalar]
    _ = BrandenLeite.polynomialLift (PowerSeries.mk D₀) *
        BrandenLeite.polynomialLift (PowerSeries.mk d) := by rw [hbase]
    _ = BrandenLeite.polynomialLift
        (PowerSeries.mk D₀ * PowerSeries.mk d) := by
          rw [BrandenLeite.polynomialLift_mul]
    _ = BrandenLeite.polynomialLift (PowerSeries.mk N) := by rw [hdIdentity]

/-- If `d` and `K` are PF, every row of the Riordan array of
`(d, z d K)` splits and all its roots are nonpositive. -/
theorem rowPolynomial_splits_and_roots_nonpos
    {d K : ℕ → ℝ} (hd : IsPolyaFreqSeq d) (hK : IsPolyaFreqSeq K)
    (n : ℕ) :
    (rowPolynomial d K n).Splits ∧
      ∀ r ∈ (rowPolynomial d K n).roots, r ≤ 0 := by
  exact
    LeftProductionMatrix.rowPolynomial_splits_and_roots_nonpos_of_isLeftProductionArray
      (isLeftProductionArray d K) (production_isLowerTriangular d K)
      (production_hasTotallyNonnegativeLeadingTruncations hd hK) n

/-! ## Finite rational PF products -/

/-- Coefficients of
`c z^r ∏_i (1 + α_i z) / ∏_j (1 - β_j z)`. -/
def rationalPFCoeff (c : ℝ) (r : ℕ) (alphas betas : List ℝ)
    (n : ℕ) : ℝ :=
  c * if r ≤ n then
    BrandenVecchi.finiteSupersymmetricCoeff alphas betas (n - r)
  else 0

/-- The coefficient definition is literally the stated finite rational
product as a formal power series. -/
theorem mk_rationalPFCoeff (c : ℝ) (r : ℕ)
    (alphas betas : List ℝ) :
    PowerSeries.mk (rationalPFCoeff c r alphas betas) =
      PowerSeries.C c * PowerSeries.X ^ r *
        BrandenVecchi.finiteSupersymmetricSeries alphas betas := by
  ext n
  rw [PowerSeries.coeff_mk, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul']
  simp [rationalPFCoeff, BrandenVecchi.finiteSupersymmetricCoeff]

/-- A finite rational product with nonnegative linear and geometric
parameters, a nonnegative scalar, and an arbitrary monomial shift has a PF
coefficient sequence. -/
theorem rationalPFCoeff_isPolyaFreqSeq
    {c : ℝ} (hc : 0 ≤ c) (r : ℕ)
    {alphas betas : List ℝ}
    (halphas : ∀ a ∈ alphas, 0 ≤ a)
    (hbetas : ∀ b ∈ betas, 0 ≤ b) :
    IsPolyaFreqSeq (rationalPFCoeff c r alphas betas) := by
  have hbase :=
    BrandenVecchi.finiteSupersymmetricCoeff_isPolyaFreqSeq
      halphas hbetas
  have hshift := hbase.prefix_zeros r
  exact BrandenVecchi.IsPolyaFreqSeq.const_mul_sequence hshift c hc

/-! ## Coefficient-recurrence interface -/

/-- A recurrence with denominator `D₀(z) - X L(z)` and numerator `N(z)`
has the PF Riordan rows whenever `d = N / D₀` and `K = L / (z N)` are
certified coefficientwise and are PF.

The recurrence is an explicit hypothesis on an arbitrary polynomial sequence;
no definitional identification of that sequence is assumed. -/
theorem recurrence_splits_and_roots_nonpos
    {P : ℕ → ℝ[X]} {D₀ L N d K : ℕ → ℝ}
    (hD₀zero : D₀ 0 = 1)
    (hrec : ∀ n,
      ∑ j ∈ Finset.range (n + 1),
          (C (D₀ j) - X * C (L j)) * P (n - j) = C (N n))
    (hdIdentity : PowerSeries.mk D₀ * PowerSeries.mk d = PowerSeries.mk N)
    (hKIdentity :
      PowerSeries.X * PowerSeries.mk N * PowerSeries.mk K =
        PowerSeries.mk L)
    (hd : IsPolyaFreqSeq d) (hK : IsPolyaFreqSeq K) (n : ℕ) :
    (P n).Splits ∧ ∀ r ∈ (P n).roots, r ≤ 0 := by
  let Dcoeff : ℕ → ℝ[X] := fun j => C (D₀ j) - X * C (L j)
  let Ecoeff : ℕ → ℝ[X] := fun j => C (N j)
  let Q : ℕ → ℝ[X] := rowPolynomial d K
  let Dseries : PowerSeries ℝ[X] :=
    BrandenLeite.polynomialLift (PowerSeries.mk D₀) -
      PowerSeries.C X * BrandenLeite.polynomialLift (PowerSeries.mk L)
  let F : PowerSeries ℝ[X] :=
    BrandenLeite.twoKernelGeneratingSeries (PowerSeries.mk d)
      (PowerSeries.X * PowerSeries.mk K)
  have hLzero : L 0 = 0 := by
    have h := congrArg (PowerSeries.coeff 0) hKIdentity
    simpa using h.symm
  have hDcoeff : PowerSeries.mk Dcoeff = Dseries := by
    apply PowerSeries.ext
    intro m
    simp [Dcoeff, Dseries, BrandenLeite.polynomialLift]
  have hEcoeff : PowerSeries.mk Ecoeff =
      BrandenLeite.polynomialLift (PowerSeries.mk N) := by
    apply PowerSeries.ext
    intro m
    simp [Ecoeff, BrandenLeite.polynomialLift]
  have hQseries : PowerSeries.mk Q = F := by
    apply PowerSeries.ext
    intro m
    simp [Q, F, rowPolynomial_eq_twoKernelRow]
  have hcandidate : Dseries * F =
      BrandenLeite.polynomialLift (PowerSeries.mk N) := by
    simpa [Dseries, F, rowGeneratingSeries_eq_twoKernelGeneratingSeries] using
      denominator_mul_rowGeneratingSeries hdIdentity hKIdentity
  have hQrec : ∀ m,
      ∑ j ∈ Finset.range (m + 1), Dcoeff j * Q (m - j) = Ecoeff m := by
    apply (BrandenLeite.mk_mul_mk_eq_mk_iff Dcoeff Q Ecoeff).mp
    rw [hDcoeff, hQseries, hEcoeff]
    exact hcandidate
  have hDcoeffZero : Dcoeff 0 = 1 := by
    simp [Dcoeff, hD₀zero, hLzero]
  have hPQ : P = Q :=
    BrandenLeite.eq_of_finite_denominator_numerator hDcoeffZero
      (by simpa [Dcoeff, Ecoeff] using hrec) hQrec
  rw [hPQ]
  exact rowPolynomial_splits_and_roots_nonpos hd hK n

/-! ## Validation families -/

/-- Coefficients of the geometric series `1 / (1 - z)`. -/
def geometricOneCoeff : ℕ → ℝ :=
  rationalPFCoeff 1 0 [] [1]

/-- The geometric coefficient series is the inverse of `1 - z`. -/
theorem mk_geometricOneCoeff_mul_one_sub :
    PowerSeries.mk geometricOneCoeff * (1 - PowerSeries.X) = 1 := by
  rw [geometricOneCoeff, mk_rationalPFCoeff]
  simpa [BrandenVecchi.finiteSupersymmetricSeries] using
    BrandenVecchi.supersymmetricDenominatorFactor_mul_one_sub 1

/-- Coefficients of `(1 + z)^2 / (1 - z)`, the `K`-series for A114123. -/
def a114123KCoeff : ℕ → ℝ :=
  rationalPFCoeff 1 0 [1, 1] [1]

/-- The A114123 `K`-series has the claimed finite rational factorization. -/
theorem mk_a114123KCoeff_mul_one_sub :
    PowerSeries.mk a114123KCoeff * (1 - PowerSeries.X) =
      (1 + PowerSeries.X) ^ 2 := by
  rw [a114123KCoeff, mk_rationalPFCoeff]
  simpa [BrandenVecchi.supersymmetricNumeratorFactor, pow_two] using
    BrandenVecchi.finiteSupersymmetricSeries_mul_denominators
      ([1, 1] : List ℝ) ([1] : List ℝ)

/-- The A114123 rows, equivalently
`[z^n] (1-z) / ((1-z)^2 - X z (1+z)^2)`. -/
def a114123Row (n : ℕ) : ℝ[X] :=
  rowPolynomial geometricOneCoeff a114123KCoeff n

/-- Exact generating-series identity
`((1-z)^2 - X z (1+z)^2) F(X,z) = 1-z` for the A114123 rows. -/
theorem a114123_denominator_mul_rowGeneratingSeries :
    (BrandenLeite.polynomialLift ((1 - PowerSeries.X) ^ 2) -
        PowerSeries.C X * BrandenLeite.polynomialLift
          (PowerSeries.X * (1 + PowerSeries.X) ^ 2)) *
      rowGeneratingSeries geometricOneCoeff a114123KCoeff =
        BrandenLeite.polynomialLift (1 - PowerSeries.X) := by
  have hd :
      (1 - PowerSeries.X) ^ 2 * PowerSeries.mk geometricOneCoeff =
        1 - PowerSeries.X := by
    calc
      (1 - PowerSeries.X) ^ 2 * PowerSeries.mk geometricOneCoeff =
          (1 - PowerSeries.X) *
            (PowerSeries.mk geometricOneCoeff * (1 - PowerSeries.X)) := by ring
      _ = 1 - PowerSeries.X := by rw [mk_geometricOneCoeff_mul_one_sub]; ring
  have hK :
      PowerSeries.X * (1 - PowerSeries.X) *
          PowerSeries.mk a114123KCoeff =
        PowerSeries.X * (1 + PowerSeries.X) ^ 2 := by
    calc
      PowerSeries.X * (1 - PowerSeries.X) *
          PowerSeries.mk a114123KCoeff =
          PowerSeries.X *
            (PowerSeries.mk a114123KCoeff * (1 - PowerSeries.X)) := by ring
      _ = PowerSeries.X * (1 + PowerSeries.X) ^ 2 := by
        rw [mk_a114123KCoeff_mul_one_sub]
  have hd' :
      PowerSeries.mk
            (fun n => PowerSeries.coeff n ((1 - PowerSeries.X) ^ 2)) *
          PowerSeries.mk geometricOneCoeff =
        PowerSeries.mk (fun n => PowerSeries.coeff n (1 - PowerSeries.X)) := by
    simpa only [BrandenLeite.mk_coeff_eq] using hd
  have hK' :
      PowerSeries.X *
          PowerSeries.mk (fun n => PowerSeries.coeff n (1 - PowerSeries.X)) *
          PowerSeries.mk a114123KCoeff =
        PowerSeries.mk (fun n => PowerSeries.coeff n
          (PowerSeries.X * (1 + PowerSeries.X) ^ 2)) := by
    simpa only [BrandenLeite.mk_coeff_eq] using hK
  simpa only [BrandenLeite.mk_coeff_eq] using
    denominator_mul_rowGeneratingSeries
      (D₀ := fun n => PowerSeries.coeff n ((1 - PowerSeries.X) ^ 2))
      (L := fun n => PowerSeries.coeff n
        (PowerSeries.X * (1 + PowerSeries.X) ^ 2))
      (N := fun n => PowerSeries.coeff n (1 - PowerSeries.X))
      (d := geometricOneCoeff) (K := a114123KCoeff) hd' hK'

/-- Every A114123 row splits and has only nonpositive roots. -/
theorem a114123Row_splits_and_roots_nonpos (n : ℕ) :
    (a114123Row n).Splits ∧
      ∀ r ∈ (a114123Row n).roots, r ≤ 0 := by
  apply rowPolynomial_splits_and_roots_nonpos
  · exact rationalPFCoeff_isPolyaFreqSeq
      (c := 1) (by norm_num) 0 (by simp) (by simp)
  · exact rationalPFCoeff_isPolyaFreqSeq
      (c := 1) (by norm_num) 0 (by simp) (by simp)

/-- Coefficients of `z^2 / (1 - z)`, the `K`-series for the rows
`R_m(X) = ∑_j binom(m-j,2j) X^j`. -/
def evenBinomialKCoeff : ℕ → ℝ :=
  rationalPFCoeff 1 2 [] [1]

/-- The even-binomial `K`-series is `z^2 / (1-z)`. -/
theorem mk_evenBinomialKCoeff_mul_one_sub :
    PowerSeries.mk evenBinomialKCoeff * (1 - PowerSeries.X) =
      PowerSeries.X ^ 2 := by
  rw [evenBinomialKCoeff, mk_rationalPFCoeff]
  have hs :
      BrandenVecchi.finiteSupersymmetricSeries ([] : List ℝ) [1] *
          (1 - PowerSeries.X) = 1 := by
    simpa using
      BrandenVecchi.finiteSupersymmetricSeries_mul_denominators
        ([] : List ℝ) ([1] : List ℝ)
  calc
    PowerSeries.C 1 * PowerSeries.X ^ 2 *
          BrandenVecchi.finiteSupersymmetricSeries [] [1] *
        (1 - PowerSeries.X) =
      PowerSeries.X ^ 2 *
        (BrandenVecchi.finiteSupersymmetricSeries [] [1] *
          (1 - PowerSeries.X)) := by
            simp only [map_one]
            ring
    _ = PowerSeries.X ^ 2 := by
      rw [hs]
      simp

/-- The Riordan realization of
`R_m(X) = ∑_j binom(m-j,2j) X^j`. -/
def evenBinomialRow (m : ℕ) : ℝ[X] :=
  rowPolynomial geometricOneCoeff evenBinomialKCoeff m

/-- Exact generating-series identity
`((1-z)^2 - X z^3) F(X,z) = 1-z` for the even-binomial rows. -/
theorem evenBinomial_denominator_mul_rowGeneratingSeries :
    (BrandenLeite.polynomialLift ((1 - PowerSeries.X) ^ 2) -
        PowerSeries.C X *
          BrandenLeite.polynomialLift (PowerSeries.X ^ 3)) *
      rowGeneratingSeries geometricOneCoeff evenBinomialKCoeff =
        BrandenLeite.polynomialLift (1 - PowerSeries.X) := by
  have hd :
      (1 - PowerSeries.X) ^ 2 * PowerSeries.mk geometricOneCoeff =
        1 - PowerSeries.X := by
    calc
      (1 - PowerSeries.X) ^ 2 * PowerSeries.mk geometricOneCoeff =
          (1 - PowerSeries.X) *
            (PowerSeries.mk geometricOneCoeff * (1 - PowerSeries.X)) := by ring
      _ = 1 - PowerSeries.X := by rw [mk_geometricOneCoeff_mul_one_sub]; ring
  have hK :
      PowerSeries.X * (1 - PowerSeries.X) *
          PowerSeries.mk evenBinomialKCoeff = PowerSeries.X ^ 3 := by
    calc
      PowerSeries.X * (1 - PowerSeries.X) *
          PowerSeries.mk evenBinomialKCoeff =
          PowerSeries.X *
            (PowerSeries.mk evenBinomialKCoeff * (1 - PowerSeries.X)) := by ring
      _ = PowerSeries.X ^ 3 := by
        rw [mk_evenBinomialKCoeff_mul_one_sub]
        ring
  have hd' :
      PowerSeries.mk
            (fun n => PowerSeries.coeff n ((1 - PowerSeries.X) ^ 2)) *
          PowerSeries.mk geometricOneCoeff =
        PowerSeries.mk (fun n => PowerSeries.coeff n (1 - PowerSeries.X)) := by
    simpa only [BrandenLeite.mk_coeff_eq] using hd
  have hK' :
      PowerSeries.X *
          PowerSeries.mk (fun n => PowerSeries.coeff n (1 - PowerSeries.X)) *
          PowerSeries.mk evenBinomialKCoeff =
        PowerSeries.mk (fun n => PowerSeries.coeff n (PowerSeries.X ^ 3)) := by
    simpa only [BrandenLeite.mk_coeff_eq] using hK
  simpa only [BrandenLeite.mk_coeff_eq] using
    denominator_mul_rowGeneratingSeries
      (D₀ := fun n => PowerSeries.coeff n ((1 - PowerSeries.X) ^ 2))
      (L := fun n => PowerSeries.coeff n (PowerSeries.X ^ 3))
      (N := fun n => PowerSeries.coeff n (1 - PowerSeries.X))
      (d := geometricOneCoeff) (K := evenBinomialKCoeff) hd' hK'

/-- Every even-binomial Riordan row splits and has only nonpositive roots. -/
theorem evenBinomialRow_splits_and_roots_nonpos (m : ℕ) :
    (evenBinomialRow m).Splits ∧
      ∀ r ∈ (evenBinomialRow m).roots, r ≤ 0 := by
  apply rowPolynomial_splits_and_roots_nonpos
  · exact rationalPFCoeff_isPolyaFreqSeq
      (c := 1) (by norm_num) 0 (by simp) (by simp)
  · exact rationalPFCoeff_isPolyaFreqSeq
      (c := 1) (by norm_num) 2 (by simp) (by simp)

end PFRiordan
end RealRooted
