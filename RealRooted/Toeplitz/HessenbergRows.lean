module

import RealRooted.Toeplitz.HessenbergDeterminant
public import Mathlib.RingTheory.PowerSeries.Inverse
public import RealRooted.MatrixInterlacing.TP2Step

/-!
# Rows of the Hessenberg generating function `1 / (det (I + z A) - t z)`

For a square real matrix `A` of size `d = n + 1 ≥ 1` put `F(z) = det (I + z A)` and let
`P_k(t)` be the coefficients of the power series `1 / (F(z) - t z)` in `z` with coefficients in
`ℝ[t]` (`Polynomial.coeToPowerSeries` is used to regard `F` as such a series).

Let `J = 𝟙 e₁ᵀ`. The vector `f_k(x) = (A + x J)ᵏ 𝟙` (`hessenbergVector`) is defined by
the affine step `f_{k+1} = (A + X J) f_k`, `f_0 = 𝟙`. When the matrix has the shape
`A_{ij} = A_{jj}` for `i ≤ j` (so that `A = 𝟙 cᵀ - L` with `L` strictly lower triangular),
the first coordinate of `f_k` is the `k`-th row up to the reflection `t ↦ -t`:

`P_k(t) = (-1)^k f_{k,1}(-t)`  (`hessenbergRow_eq`).

The proof solves the triangular system for the generating series of the signed vector
`(-1)^k f_k(-t)` and compares with the matrix determinant lemma for `det (I + z A)`.
-/

@[expose] public section

open Polynomial Matrix

noncomputable section

namespace RealRooted

variable {n : ℕ}

/-- The determinant polynomial `F(z) = det (I + z A)`, written with the variable `X`. -/
def hessenbergDet (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ[X] :=
  (1 + (X : ℝ[X]) • A.map C).det

/-- Regard a polynomial `F(z)` over `ℝ` as a power series in `z` whose coefficients are
constant polynomials in the second variable `t`. -/
def hessenbergCoeffs : ℝ[X] →+* PowerSeries ℝ[X] :=
  (PowerSeries.map (C : ℝ →+* ℝ[X])).comp Polynomial.coeToPowerSeries.ringHom

/-- The denominator `F(z) - t z` of the generating function, a power series in `z` over
`ℝ[t]`. -/
def hessenbergDenominator (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : PowerSeries ℝ[X] :=
  hessenbergCoeffs (hessenbergDet A) - PowerSeries.C X * PowerSeries.X

lemma hessenbergDet_coeff_zero (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (hessenbergDet A).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, hessenbergDet, ← Polynomial.coe_evalRingHom,
    RingHom.map_det, RingHom.mapMatrix_apply]
  have : (1 + (X : ℝ[X]) • A.map C).map (Polynomial.evalRingHom 0) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [this, det_one]

lemma constantCoeff_hessenbergDenominator (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    PowerSeries.constantCoeff (hessenbergDenominator A) = ((1 : (ℝ[X])ˣ) : ℝ[X]) := by
  rw [hessenbergDenominator, map_sub, map_mul, PowerSeries.constantCoeff_X, mul_zero, sub_zero,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [hessenbergCoeffs, hessenbergDet_coeff_zero]

/-- The power series `1 / (F(z) - t z)` in `z` over `ℝ[t]`, where `F(z) = det (I + z A)`. -/
def hessenbergRowSeries (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : PowerSeries ℝ[X] :=
  PowerSeries.invOfUnit (hessenbergDenominator A) 1

/-- The `k`-th row `P_k(t)`: the coefficient of `z ^ k` in `1 / (det (I + z A) - t z)`. -/
def hessenbergRow (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : ℕ) : ℝ[X] :=
  PowerSeries.coeff k (hessenbergRowSeries A)

/-- The rows form the generating function of `1 / (det (I + z A) - t z)`. -/
theorem hessenbergDenominator_mul_mk_hessenbergRow
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    hessenbergDenominator A * PowerSeries.mk (hessenbergRow A) = 1 := by
  have : PowerSeries.mk (hessenbergRow A) = hessenbergRowSeries A := by
    ext k; simp [hessenbergRow]
  rw [this, hessenbergRowSeries]
  exact PowerSeries.mul_invOfUnit _ _ (by simpa using constantCoeff_hessenbergDenominator A)

/-- The vector `(A + X J)ᵏ 𝟙`, `J = 𝟙 e₁ᵀ`: `f₀ = 𝟙` and `f_{k+1} = (A + X J) f_k`. -/
def hessenbergVector (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ℕ → Fin (n + 1) → ℝ[X]
  | 0 => fun _ => 1
  | k + 1 => tp2AffineStep A 1 (hessenbergVector A k)

/-- The signed reflected vector `(-1)ᵏ f_k(-t)`. -/
def hessenbergSignedVector (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : ℕ)
    (i : Fin (n + 1)) : ℝ[X] :=
  C ((-1 : ℝ) ^ k) * (hessenbergVector A k i).comp (-X)

lemma hessenbergSignedVector_zero (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    hessenbergSignedVector A 0 i = 1 := by
  simp [hessenbergSignedVector, hessenbergVector]

lemma hessenbergSignedVector_succ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : ℕ)
    (i : Fin (n + 1)) :
    hessenbergSignedVector A (k + 1) i =
      X * hessenbergSignedVector A k 0 -
        ∑ j, C (A i j) * hessenbergSignedVector A k j := by
  have h1 : hessenbergVector A (k + 1) i =
      ∑ j, C (A i j) * hessenbergVector A k j + X * hessenbergVector A k 0 := by
    simp [hessenbergVector, tp2AffineStep, smul_eq_C_mul]
  have h2 : (∑ j, C (A i j) * hessenbergVector A k j + X * hessenbergVector A k 0).comp (-X) =
      ∑ j, C (A i j) * (hessenbergVector A k j).comp (-X) +
        (-X) * (hessenbergVector A k 0).comp (-X) := by
    rw [add_comp, mul_comp, X_comp, ← Polynomial.coe_compRingHom_apply, map_sum]
    simp [mul_comp]
  simp only [hessenbergSignedVector, h1, h2, pow_succ, map_mul, map_neg, map_one]
  have hS : ∑ j, C (A i j) * (C ((-1 : ℝ) ^ k) * (hessenbergVector A k j).comp (-X)) =
      C ((-1 : ℝ) ^ k) * ∑ j, C (A i j) * (hessenbergVector A k j).comp (-X) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hS]
  ring

/-! ### The generating series of the signed vector -/

/-- The inclusion `ℝ → ℝ[t]⟦z⟧` of real constants. -/
def hessenbergEmbed : ℝ →+* PowerSeries ℝ[X] :=
  (PowerSeries.C : ℝ[X] →+* PowerSeries ℝ[X]).comp (C : ℝ →+* ℝ[X])

lemma hessenbergEmbed_apply (a : ℝ) : hessenbergEmbed a = PowerSeries.C (C a) := rfl

@[simp] lemma hessenbergCoeffs_C (a : ℝ) :
    hessenbergCoeffs (C a) = hessenbergEmbed a := by
  simp [hessenbergCoeffs, hessenbergEmbed_apply]

@[simp] lemma hessenbergCoeffs_X : hessenbergCoeffs X = PowerSeries.X := by
  simp [hessenbergCoeffs]

/-- `hessenbergCoeffs` maps `1 + z A` to `1 + z A` over the series ring. -/
lemma hessenbergCoeffs_mapMatrix (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    hessenbergCoeffs.mapMatrix (1 + (X : ℝ[X]) • A.map C) =
      1 + (PowerSeries.X : PowerSeries ℝ[X]) • A.map hessenbergEmbed := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j
  · subst h
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, map_add, map_mul, map_one, hessenbergCoeffs_X,
      hessenbergCoeffs_C]
  · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply_ne h, smul_eq_mul, map_add, map_mul, map_zero, hessenbergCoeffs_X,
      hessenbergCoeffs_C]

/-- The generating series `∑ₖ (-1)ᵏ f_{k,i}(-t) zᵏ` of a coordinate of the signed vector. -/
def hessenbergSeries (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    PowerSeries ℝ[X] :=
  PowerSeries.mk fun k => hessenbergSignedVector A k i

/-- The coordinate series satisfy `G_i = 1 + z (t G_0 - ∑ⱼ A_{ij} G_j)`. -/
lemma hessenbergSeries_eq (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    hessenbergSeries A i = 1 + PowerSeries.X * (PowerSeries.C X * hessenbergSeries A 0 -
      ∑ j, hessenbergEmbed (A i j) * hessenbergSeries A j) := by
  ext k
  rcases k with _ | k
  · simp [hessenbergSeries, hessenbergSignedVector_zero]
  · rw [map_add, PowerSeries.coeff_succ_X_mul, map_sub, map_sum]
    simp only [hessenbergSeries, PowerSeries.coeff_mk, hessenbergSignedVector_succ,
      hessenbergEmbed_apply, PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
    simp

/-- Entrywise, `(1 + z L) G = G_0 𝟙`. -/
lemma hessenbergSeries_mulVec (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (i : Fin (n + 1)) :
    hessenbergSeries A i + PowerSeries.X * ∑ j, hessenbergEmbed (A i j - A j j) *
      hessenbergSeries A j = hessenbergSeries A 0 := by
  have h0 := hessenbergSeries_eq A 0
  have hi := hessenbergSeries_eq A i
  have hsum : ∑ j, hessenbergEmbed (A i j - A j j) * hessenbergSeries A j =
      ∑ j, hessenbergEmbed (A i j) * hessenbergSeries A j -
        ∑ j, hessenbergEmbed (A 0 j) * hessenbergSeries A j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hrow (Fin.zero_le j), map_sub, sub_mul]
  rw [hsum]
  linear_combination hi - h0

/-- **Resolvent identity for the triangular system.** If a family `S` of power series satisfies
`S_i + z ∑ⱼ (A_{ij} - A_{jj}) S_j = S_0` for all `i`, where `A_{ij} = A_{jj}` for `i ≤ j`, then
`z ∑ⱼ A_{jj} S_j = S_0 (det (I + z A) - 1)`. -/
theorem X_mul_sum_diag_mul_eq (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (S : Fin (n + 1) → PowerSeries ℝ[X])
    (hS : ∀ i, S i + PowerSeries.X * ∑ j, hessenbergEmbed (A i j - A j j) * S j = S 0) :
    PowerSeries.X * ∑ j, hessenbergEmbed (A j j) * S j =
      S 0 * (hessenbergCoeffs (hessenbergDet A) - 1) := by
  set L : Matrix (Fin (n + 1)) (Fin (n + 1)) (PowerSeries ℝ[X]) :=
    Matrix.of fun i j => hessenbergEmbed (A i j - A j j) with hL
  set c : Fin (n + 1) → PowerSeries ℝ[X] := fun j => hessenbergEmbed (A j j) with hc
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) (PowerSeries ℝ[X]) :=
    1 + (PowerSeries.X : PowerSeries ℝ[X]) • L with hBdef
  have hLlow : ∀ i j, i ≤ j → L i j = 0 := fun i j hij => by simp [hL, hrow hij]
  have hB : B.det = 1 := det_one_add_smul_of_lower _ L hLlow
  have hdet : hessenbergCoeffs (hessenbergDet A) =
      1 + PowerSeries.X * (c ⬝ᵥ (B⁻¹ *ᵥ fun _ => 1)) := by
    rw [hessenbergDet, RingHom.map_det, hessenbergCoeffs_mapMatrix]
    exact det_one_add_smul_eq_of_lower _ c L _ hLlow fun i j => by
      simp only [hc, hL, Matrix.map_apply, Matrix.of_apply, ← map_add]
      congr 1
      ring
  have hmul : B *ᵥ S = fun _ => S 0 := by
    rw [hBdef, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hS i
  have hsol : S = S 0 • (B⁻¹ *ᵥ fun _ => 1) := by
    have hinv := Matrix.nonsing_inv_mul B (by rw [hB]; exact isUnit_one)
    have hconst : (fun _ : Fin (n + 1) => S 0) = S 0 • fun _ => (1 : PowerSeries ℝ[X]) := by
      funext j; simp
    calc S = (B⁻¹ * B) *ᵥ S := by rw [hinv, Matrix.one_mulVec]
      _ = B⁻¹ *ᵥ (B *ᵥ S) := by rw [Matrix.mulVec_mulVec]
      _ = B⁻¹ *ᵥ (S 0 • fun _ => 1) := by rw [hmul, hconst]
      _ = S 0 • (B⁻¹ *ᵥ fun _ => 1) := by rw [Matrix.mulVec_smul]
  have hsum : ∑ j, hessenbergEmbed (A j j) * S j = S 0 * (c ⬝ᵥ (B⁻¹ *ᵥ fun _ => 1)) := by
    have h2 := congrArg (fun v => c ⬝ᵥ v) hsol
    simp only [dotProduct_smul, smul_eq_mul] at h2
    rw [show ∑ j, hessenbergEmbed (A j j) * S j = c ⬝ᵥ S from rfl, h2, mul_comm]
  rw [hsum, hdet]
  ring

/-- **Generating function of the signed vector.** For a matrix whose entries satisfy
`A_{ij} = A_{jj}` for `i ≤ j`, the first coordinate series `G_0` of the signed vector
`(-1)ᵏ f_k(-t)` is `1 / (det (I + z A) - t z)`. -/
theorem hessenbergDenominator_mul_hessenbergSeries_zero
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) :
    hessenbergDenominator A * hessenbergSeries A 0 = 1 := by
  have hkey := X_mul_sum_diag_mul_eq A hrow (hessenbergSeries A)
    (hessenbergSeries_mulVec A hrow)
  have h0 := hessenbergSeries_eq A 0
  have hsum : ∑ j, hessenbergEmbed (A 0 j) * hessenbergSeries A j =
      ∑ j, hessenbergEmbed (A j j) * hessenbergSeries A j :=
    Finset.sum_congr rfl fun j _ => by rw [hrow (Fin.zero_le j)]
  rw [hsum] at h0
  rw [hessenbergDenominator]
  linear_combination h0 - hkey

/-- The row series `1 / (det (I + z A) - t z)` is the first coordinate series of the signed
vector. -/
theorem hessenbergRowSeries_eq_hessenbergSeries_zero (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) :
    hessenbergRowSeries A = hessenbergSeries A 0 := by
  have h := hessenbergDenominator_mul_hessenbergSeries_zero A hrow
  have h1 := PowerSeries.mul_invOfUnit (hessenbergDenominator A) 1
    (by simpa using constantCoeff_hessenbergDenominator A)
  calc hessenbergRowSeries A
      = (hessenbergDenominator A * hessenbergSeries A 0) * hessenbergRowSeries A := by
        rw [h, one_mul]
    _ = hessenbergSeries A 0 * (hessenbergDenominator A * hessenbergRowSeries A) := by ring
    _ = hessenbergSeries A 0 := by rw [hessenbergRowSeries, h1, mul_one]

/-- **The rows are the signed first coordinate of the vector recursion.** If `A_{ij} = A_{jj}`
for `i ≤ j`, the coefficient of `zᵏ` in `1 / (det (I + z A) - t z)` is
`P_k(t) = (-1)ᵏ f_{k,1}(-t)`, where `f_k = (A + X J)ᵏ 𝟙`. -/
theorem hessenbergRow_eq (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (k : ℕ) :
    hessenbergRow A k = C ((-1 : ℝ) ^ k) * (hessenbergVector A k 0).comp (-X) := by
  simp [hessenbergRow, hessenbergRowSeries_eq_hessenbergSeries_zero A hrow, hessenbergSeries,
    hessenbergSignedVector]

end RealRooted
