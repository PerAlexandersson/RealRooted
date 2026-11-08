module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Binomial
public import RealRooted.BrandenLeite.WeightedDerivativeKernel.Basic
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Checkerboard
import RealRooted.BrandenLeite.NegativePowerDeterminant
import RealRooted.BrandenLeite.WeightedDerivativeKernel.Pencil

/-! Polynomial parameter rows of a formal negative power. -/

public section

open PowerSeries

namespace RealRooted.BrandenLeite

/-- A normalized denominator `Q` and a numerator `B` with zero constant term give the
affine series `Q - t B` constant coefficient one. -/
theorem constantCoeff_map_C_sub_C_X_mul_map_C {R : Type*} [CommRing R]
    {Q B : PowerSeries R} (hQ : constantCoeff Q = 1) (hB : constantCoeff B = 0) :
    constantCoeff (map Polynomial.C Q - C Polynomial.X * map Polynomial.C B) = 1 := by
  have hmap (F : PowerSeries R) :
      constantCoeff (map Polynomial.C F) = Polynomial.C (constantCoeff F) := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
  simp only [map_sub, map_mul, constantCoeff_C, hmap, hQ, hB]
  simp

variable {R : Type*} [CommRing R] [BinomialRing (Polynomial R)]

/-- The coefficient of degree `n` in `(Q(u)-t B(u))^(-κ)`, as a polynomial in `t`.
The binomial substitution is meaningful when `Q(0)=1` and `B(0)=0`. -/
@[expose] noncomputable def affineNegativePowerCoeff
    (κ : R) (Q B : PowerSeries R) (n : ℕ) : Polynomial R :=
  coeff n (subst (map Polynomial.C Q - C Polynomial.X * map Polynomial.C B - 1)
    (binomialSeries (Polynomial R) (-Polynomial.C κ)))

/-- The weighted-kernel pencil determinant is the factorial multiple of the
canonical formal negative-power coefficient row. -/
theorem det_weightedDerivativeKernel_affineNegativePowerCoeff
    (κ : R) (Q B : PowerSeries R) (hQ : constantCoeff Q = 1)
    (hB : constantCoeff B = 0) (n : ℕ) :
    Matrix.det
      ((((weightedDerivativeKernel κ (fun k => (-1 : R) ^ k * coeff k Q)).submatrix
        Fin.val Fin.val : Matrix (Fin n) (Fin n) R).map Polynomial.C) +
      (Polynomial.X : Polynomial R) • (Matrix.checkerboard
        ((weightedDerivativeKernel κ (fun k => coeff k B)).submatrix
          Fin.val Fin.val : Matrix (Fin n) (Fin n) R)).map Polynomial.C) =
      (n.factorial : Polynomial R) * affineNegativePowerCoeff κ Q B n := by
  let H := map Polynomial.C Q - C Polynomial.X * map Polynomial.C B
  have hH : constantCoeff H = 1 := constantCoeff_map_C_sub_C_X_mul_map_C hQ hB
  have hid := det_weightedDerivativeKernel_subst_binomialSeries_neg
    (Polynomial.C κ) H hH n
  have hcoeff (k : ℕ) : coeff k H =
      Polynomial.C (coeff k Q) - Polynomial.X * Polynomial.C (coeff k B) := by
    simp [H, coeff_C_mul]
  simp_rw [hcoeff] at hid
  rw [weightedDerivativeKernel_signed_sub_X_mul] at hid
  exact hid

end RealRooted.BrandenLeite
