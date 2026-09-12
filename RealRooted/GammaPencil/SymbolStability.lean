/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.BorceaBranden.Applications.RealUnivariateSymbol
import RealRooted.GammaPencil.Symbol
import RealRooted.HermiteBiehler.Converse
import RealRooted.LinearPowerFamily

/-!
# Stability of the gamma-pencil finite symbol

The explicit residual factors in the gamma-pencil finite symbol are in
proper position in both parity cases.  This gives upper-half-plane stability
of the residual and, with the factorization from `Symbol`, of the finite
algebraic symbol.
-/

open Polynomial

noncomputable section

namespace RealRooted

private theorem eval_complexPolynomialInFirstMv
    (p : ℂ[X]) (z : Fin 2 → ℂ) :
    MvPolynomial.eval z (BorceaBranden.complexPolynomialInFirstMv p) =
      p.eval (z 0) := by
  rw [BorceaBranden.complexPolynomialInFirstMv, Polynomial.hom_eval₂]
  have hcomp :
      (MvPolynomial.eval z).comp
          (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ) = RingHom.id ℂ := by
    ext a
    simp
  rw [hcomp]
  rw [MvPolynomial.eval_X]
  exact Polynomial.eval₂_at_apply (p := p) (RingHom.id ℂ) (z 0)

private theorem gammaSymbol_residual_stable
    {p q : ℝ[X]} (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q)
    (hpq : Prec q p) (hdegree : 1 ≤ p.natDegree) :
    MvUpperHalfPlaneStable
      (complexifyMv
        (BorceaBranden.polynomialInFirstMv p +
          MvPolynomial.X 1 * BorceaBranden.polynomialInFirstMv q)) := by
  simp only [complexifyMv, map_add, map_mul, MvPolynomial.map_X]
  change MvUpperHalfPlaneStable
    (complexifyMv (BorceaBranden.polynomialInFirstMv p) +
      MvPolynomial.X 1 * complexifyMv (BorceaBranden.polynomialInFirstMv q))
  rw [← BorceaBranden.complexPolynomialInFirstMv_complexify p,
    ← BorceaBranden.complexPolynomialInFirstMv_complexify q]
  intro z hz hzero
  have hpzero : p ≠ 0 := hp.ne_zero
  have hpsplits : p.Splits := hpq.2.1.2
  have hpz : (complexify p).eval (z 0) ≠ 0 :=
    eval_complexify_ne_zero_of_splits_of_im_pos hpsplits hpzero (hz 0)
  have hratio : ((complexify q).eval (z 0) / (complexify p).eval (z 0)).im ≤ 0 :=
    im_ratio_nonpos_general hp hq hpq hdegree (hz 0)
  have hzone : z 1 ≠ 0 := by
    intro hz0
    have := hz 1
    simp [hz0] at this
  have heval :
      (complexify p).eval (z 0) + z 1 * (complexify q).eval (z 0) = 0 := by
    simpa [eval_complexPolynomialInFirstMv] using hzero
  have hratio_eq :
      (complexify q).eval (z 0) / (complexify p).eval (z 0) = -(1 / z 1) := by
    field_simp [hpz, hzone]
    linear_combination heval
  rw [hratio_eq] at hratio
  have hnorm : 0 < Complex.normSq (z 1) := Complex.normSq_pos.mpr hzone
  have hpositive : 0 < (-(1 / z 1)).im := by
    rw [one_div, Complex.neg_im, Complex.inv_im]
    simpa only [neg_div, neg_neg] using div_pos (hz 1) hnorm
  linarith

/-- In the even case the first residual factor is a positive multiple of `X`. -/
theorem gammaSymbolP_even (m : ℕ) :
    gammaSymbolP (2 * m) m = C ((m : ℝ) + 1) * X := by
  have hzero :
      (2 : ℝ) * ((2 * m : ℕ) : ℝ) - 4 * (m : ℝ) = 0 := by
    push_cast
    ring
  change X * (C ((m : ℝ) + 1) +
    C ((2 : ℝ) * ((2 * m : ℕ) : ℝ) - 4 * (m : ℝ)) * X) = _
  rw [hzero]
  simp
  ring

/-- The even first factor has root zero. -/
theorem gammaSymbolP_even_isRoot (m : ℕ) :
    (gammaSymbolP (2 * m) m).IsRoot 0 := by
  rw [gammaSymbolP_even]
  simp [Polynomial.IsRoot]

/-- In the even case the second residual factor has its unique root left of zero. -/
theorem gammaSymbolQ_even (m : ℕ) (hm : 0 < m) :
    gammaSymbolQ (2 * m) =
      C (4 * (m : ℝ)) * (X + C (1 / (4 * (m : ℝ)))) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hfour : (4 : ℝ) * (m : ℝ) ≠ 0 := by positivity
  have hcoeff : (2 : ℝ) * ((2 * m : ℕ) : ℝ) = 4 * (m : ℝ) := by
    push_cast
    ring
  have hone :
      C (4 * (m : ℝ)) * C (1 / (4 * (m : ℝ))) = (1 : ℝ[X]) := by
    have hCinv (a : ℝ) (ha : a ≠ 0) :
        C a * C (1 / a) = (1 : ℝ[X]) := by
      rw [← C_mul]
      simp [ha]
    exact hCinv (4 * (m : ℝ)) hfour
  change 1 + C ((2 : ℝ) * ((2 * m : ℕ) : ℝ)) * X = _
  rw [hcoeff]
  calc
    1 + C (4 * (m : ℝ)) * X = C (4 * (m : ℝ)) * X + 1 := by ring
    _ = C (4 * (m : ℝ)) * (X + C (1 / (4 * (m : ℝ)))) := by
      rw [mul_add]
      congr 1
      exact hone.symm

/-- The even second factor has the displayed strictly negative root. -/
theorem gammaSymbolQ_even_isRoot (m : ℕ) (hm : 0 < m) :
    (gammaSymbolQ (2 * m)).IsRoot (-(1 / (4 * (m : ℝ)))) := by
  rw [gammaSymbolQ_even m hm]
  simp [Polynomial.IsRoot]

/-- The root of the even second factor lies strictly left of the root of the first. -/
theorem gammaSymbol_even_root_order (m : ℕ) (hm : 0 < m) :
    -(1 / (4 * (m : ℝ))) < 0 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  exact neg_lt_zero.mpr (one_div_pos.mpr (by positivity))

/-- The even residual factors are in the required directed proper position. -/
theorem gammaSymbol_even_prec (m : ℕ) (hm : 0 < m) :
    Prec (gammaSymbolQ (2 * m)) (gammaSymbolP (2 * m) m) := by
  rw [gammaSymbolP_even, gammaSymbolQ_even m hm]
  apply prec_C_mul_right
  · apply prec_C_mul_left
    · simpa using
        (prec_X_add_C_iff (a := (0 : ℝ)) (b := 1 / (4 * (m : ℝ))).mpr
          (by positivity))
    · positivity
  · positivity

/-- For odd rank, the two roots of the first residual factor are displayed
explicitly by its positive scalar factorization. -/
theorem gammaSymbolP_odd (m : ℕ) :
    gammaSymbolP (2 * m + 1) m =
      C (2 : ℝ) * ((X - C (-(m + 1 : ℝ) / 2)) * X) := by
  have hcoeff :
      (2 : ℝ) * ((2 * m + 1 : ℕ) : ℝ) - 4 * (m : ℝ) = 2 := by
    push_cast
    ring
  have hroot :
      C (2 : ℝ) * C (-(m + 1 : ℝ) / 2) = -C ((m : ℝ) + 1) := by
    rw [← C_mul, ← C_neg]
    congr 1
    ring
  have hrootX :
      C (2 : ℝ) * (C (-(m + 1 : ℝ) / 2) * X) =
        -C ((m : ℝ) + 1) * X := by
    rw [← mul_assoc, hroot]
  change X * (C ((m : ℝ) + 1) +
    C ((2 : ℝ) * ((2 * m + 1 : ℕ) : ℝ) - 4 * (m : ℝ)) * X) = _
  rw [hcoeff, sub_mul, mul_sub, hrootX]
  ring

/-- The odd first factor has the left root displayed by its factorization. -/
theorem gammaSymbolP_odd_isRoot_left (m : ℕ) :
    (gammaSymbolP (2 * m + 1) m).IsRoot (-(m + 1 : ℝ) / 2) := by
  rw [gammaSymbolP_odd]
  simp [Polynomial.IsRoot]

/-- The odd first factor also has root zero. -/
theorem gammaSymbolP_odd_isRoot_zero (m : ℕ) :
    (gammaSymbolP (2 * m + 1) m).IsRoot 0 := by
  rw [gammaSymbolP_odd]
  simp [Polynomial.IsRoot]

/-- In the odd case the second residual factor has the displayed linear form. -/
theorem gammaSymbolQ_odd (m : ℕ) :
    gammaSymbolQ (2 * m + 1) =
      C (4 * (m : ℝ) + 2) * (X + C (1 / (4 * (m : ℝ) + 2))) := by
  have hden : 4 * (m : ℝ) + 2 ≠ 0 := by positivity
  have hcoeff : (2 : ℝ) * ((2 * m + 1 : ℕ) : ℝ) = 4 * (m : ℝ) + 2 := by
    push_cast
    ring
  change 1 + C ((2 : ℝ) * ((2 * m + 1 : ℕ) : ℝ)) * X = _
  rw [hcoeff]
  calc
    1 + C (4 * (m : ℝ) + 2) * X = C (4 * (m : ℝ) + 2) * X + 1 := by ring
    _ = C (4 * (m : ℝ) + 2) * (X + C (1 / (4 * (m : ℝ) + 2))) := by
      rw [mul_add, ← C_mul]
      simp [hden]

/-- The odd factors have the exact directed root order. -/
theorem gammaSymbol_odd_root_order (m : ℕ) (hm : 0 < m) :
    -(m + 1 : ℝ) / 2 < -(1 / (4 * (m : ℝ) + 2)) ∧
      -(1 / (4 * (m : ℝ) + 2)) < 0 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  constructor <;> field_simp <;> nlinarith

/-- The odd second factor has its displayed root. -/
theorem gammaSymbolQ_odd_isRoot (m : ℕ) :
    (gammaSymbolQ (2 * m + 1)).IsRoot (-(1 / (4 * (m : ℝ) + 2))) := by
  rw [gammaSymbolQ_odd]
  simp [Polynomial.IsRoot]

/-- The odd residual factors are in the required directed proper position. -/
theorem gammaSymbol_odd_prec (m : ℕ) (hm : 0 < m) :
    Prec (gammaSymbolQ (2 * m + 1)) (gammaSymbolP (2 * m + 1) m) := by
  rw [gammaSymbolP_odd, gammaSymbolQ_odd]
  apply prec_C_mul_left
  · simpa [sub_eq_add_neg] using
      (interlaces_linear_quadratic_of_roots_between
        (α := -(1 / (4 * (m : ℝ) + 2)))
        (r := -(m + 1 : ℝ) / 2) (s := 0) (c := (2 : ℝ))
        (by norm_num) (gammaSymbol_odd_root_order m hm).1.le
        (gammaSymbol_odd_root_order m hm).2.le).toPrec
  · positivity

private theorem gammaSymbolP_even_pos (m : ℕ) :
    HasPosLeadingCoeff (gammaSymbolP (2 * m) m) := by
  rw [gammaSymbolP_even]
  apply hasPosLeadingCoeff_C_mul (by positivity)
  simpa using hasPosLeadingCoeff_X_sub_C (0 : ℝ)

private theorem gammaSymbolQ_even_pos (m : ℕ) (hm : 0 < m) :
    HasPosLeadingCoeff (gammaSymbolQ (2 * m)) := by
  rw [gammaSymbolQ_even m hm]
  exact hasPosLeadingCoeff_C_mul (by positivity) (hasPosLeadingCoeff_X_add_C _)

private theorem gammaSymbolP_odd_pos (m : ℕ) :
    HasPosLeadingCoeff (gammaSymbolP (2 * m + 1) m) := by
  rw [gammaSymbolP_odd]
  exact hasPosLeadingCoeff_C_mul (by positivity)
    ((hasPosLeadingCoeff_X_sub_C _).mul (by
      simpa using hasPosLeadingCoeff_X_sub_C (0 : ℝ)))

private theorem gammaSymbolQ_odd_pos (m : ℕ) :
    HasPosLeadingCoeff (gammaSymbolQ (2 * m + 1)) := by
  rw [gammaSymbolQ_odd]
  exact hasPosLeadingCoeff_C_mul (by positivity) (hasPosLeadingCoeff_X_add_C _)

private theorem gammaSymbolP_even_natDegree (m : ℕ) :
    (gammaSymbolP (2 * m) m).natDegree = 1 := by
  rw [gammaSymbolP_even, natDegree_C_mul (by positivity)]
  simp

private theorem gammaSymbolP_odd_natDegree (m : ℕ) :
    (gammaSymbolP (2 * m + 1) m).natDegree = 2 := by
  rw [gammaSymbolP_odd, natDegree_C_mul (by norm_num),
    natDegree_mul (X_sub_C_ne_zero _) X_ne_zero]
  simp

/-- The even finite algebraic gamma symbol is upper-half-plane stable. -/
theorem finiteAlgebraicSymbol_gammaOperator_even_stable (m : ℕ) (hm : 0 < m) :
    MvUpperHalfPlaneStable
      (complexifyMv (BorceaBranden.finiteAlgebraicSymbol m (gammaOperator (2 * m)))) := by
  rw [finiteAlgebraicSymbol_gammaOperator_factorization _ _ hm]
  have hresidual := gammaSymbol_residual_stable
    (gammaSymbolP_even_pos m) (gammaSymbolQ_even_pos m hm)
    (gammaSymbol_even_prec m hm) (by rw [gammaSymbolP_even_natDegree])
  simpa [complexifyMv] using hresidual.mul_X_add_X_pow 0 1 (m - 1)

/-- The odd finite algebraic gamma symbol is upper-half-plane stable. -/
theorem finiteAlgebraicSymbol_gammaOperator_odd_stable (m : ℕ) (hm : 0 < m) :
    MvUpperHalfPlaneStable
      (complexifyMv
        (BorceaBranden.finiteAlgebraicSymbol m (gammaOperator (2 * m + 1)))) := by
  rw [finiteAlgebraicSymbol_gammaOperator_factorization _ _ hm]
  have hresidual := gammaSymbol_residual_stable
    (gammaSymbolP_odd_pos m) (gammaSymbolQ_odd_pos m)
    (gammaSymbol_odd_prec m hm) (by rw [gammaSymbolP_odd_natDegree]; norm_num)
  simpa [complexifyMv] using hresidual.mul_X_add_X_pow 0 1 (m - 1)

/-- The finite algebraic gamma symbol in its canonical degree box is stable. -/
theorem finiteAlgebraicSymbol_gammaOperator_stable (n : ℕ) (hn : 2 ≤ n) :
    MvUpperHalfPlaneStable
      (complexifyMv
        (BorceaBranden.finiteAlgebraicSymbol (n / 2) (gammaOperator n))) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 0 < m := by lia
    simpa using finiteAlgebraicSymbol_gammaOperator_even_stable m hm
  · have hm : 0 < m := by lia
    have hdiv : (2 * m + 1) / 2 = m := by lia
    rw [hdiv]
    exact finiteAlgebraicSymbol_gammaOperator_odd_stable m hm

end RealRooted
