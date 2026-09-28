import RealRooted.BinaryRunTransformation.Contraction
import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization.Derivative
import RealRooted.BorceaBranden.Applications.HomogenizeStable
import RealRooted.PFPolynomial

/-!
# The binary-run pointing pencil

This file constructs the homogenized source used in the binary-run pointing
argument.  Its variables are the retained pair `(Z, W)` followed by the two
contracted source variables `(S, T)`.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- The homogenized source
`(Z + T)^(n+1) p(t (Z + S) / (Z + T))`, expressed without division. -/
def binaryRunHomogenizedSource (n : ℕ) (p : ℝ[X]) (t : ℝ) :
    MvPolynomial (Fin 2 ⊕ Fin 2) ℂ :=
  MvPolynomial.aeval ![
      MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0),
      MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1)]
    (complexifyMv ((scalePolynomial t p).homogenize (n + 1)))

/-- The source after differentiating in `S` and adjoining the pointing factor
`S + W`. -/
def binaryRunPointingSource (n : ℕ) (p : ℝ[X]) (t : ℝ) :
    MvPolynomial (Fin 2 ⊕ Fin 2) ℂ :=
  (MvPolynomial.X (Sum.inr 0) + MvPolynomial.X (Sum.inl 1)) *
    MvPolynomial.pderiv (Sum.inr 0) (binaryRunHomogenizedSource n p t)

theorem binaryRunHomogenizedSource_eq_sum (n : ℕ) (p : ℝ[X]) (t : ℝ) :
    binaryRunHomogenizedSource n p t =
      ∑ m ∈ Finset.range (n + 2),
        MvPolynomial.C ((scalePolynomial t p).coeff m : ℂ) *
          (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0)) ^ m *
            (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1)) ^
              (n + 1 - m) := by
  rw [binaryRunHomogenizedSource,
    ← BorceaBranden.homogenizeBivariate_eq_homogenize]
  simp [homogenizeBivariate, complexifyMv]

theorem pderiv_binaryRunHomogenizedSource_eq_sum
    (n : ℕ) (p : ℝ[X]) (t : ℝ) :
    MvPolynomial.pderiv (Sum.inr 0)
        (binaryRunHomogenizedSource n p t) =
      ∑ m ∈ Finset.range (n + 2),
        MvPolynomial.C ((m : ℂ) * (scalePolynomial t p).coeff m) *
          (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0)) ^
              (m - 1) *
            (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1)) ^
              (n + 1 - m) := by
  rw [binaryRunHomogenizedSource_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp
  ring

@[simp] theorem eval_binaryRunHomogenizedSource
    (n : ℕ) (p : ℝ[X]) (t : ℝ) (z : Fin 2 ⊕ Fin 2 → ℂ) :
    MvPolynomial.eval z (binaryRunHomogenizedSource n p t) =
      MvPolynomial.eval ![z (Sum.inl 0) + z (Sum.inr 0),
        z (Sum.inl 0) + z (Sum.inr 1)]
        (complexifyMv ((scalePolynomial t p).homogenize (n + 1))) := by
  rw [binaryRunHomogenizedSource, MvPolynomial.aeval_def,
    MvPolynomial.eval_eval₂]
  congr 1
  · ext c
    simp
  · funext i
    fin_cases i <;> simp

/-- The homogenized binary-run source is stable for a positive scaling of a
nonzero PF polynomial in the degree box. -/
theorem mvUpperHalfPlaneStable_binaryRunHomogenizedSource
    {n : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : p ≠ 0)
    (hdegree : p.natDegree ≤ n) {t : ℝ} (ht : 0 < t) :
    MvUpperHalfPlaneStable (binaryRunHomogenizedSource n p t) := by
  have hscaled : IsPFPolynomial (scalePolynomial t p) := by
    simpa [scalePolynomial] using
      hp.comp_C_mul_X_add_C (a := t) (d := 0) ht le_rfl
  have hscaled0 : scalePolynomial t p ≠ 0 := by
    rw [scalePolynomial]
    intro hzero
    apply hp0
    exact (Polynomial.comp_C_mul_X_eq_zero_iff (by simpa using ht.ne')).mp
      hzero
  have hscaledDegree : (scalePolynomial t p).natDegree ≤ n + 1 :=
    (natDegree_scalePolynomial_le t p).trans (by lia)
  have hhom :=
    BorceaBranden.homogenize_stable_of_splits_nonpos_of_natDegree_le
      hscaledDegree hscaled0 (hscaled.ne_zero_and_splits hscaled0).2
        hscaled.roots_nonpos
  intro z hz
  rw [eval_binaryRunHomogenizedSource]
  apply hhom
  intro i
  fin_cases i
  · simpa using add_pos (hz (Sum.inl 0)) (hz (Sum.inr 0))
  · simpa using add_pos (hz (Sum.inl 0)) (hz (Sum.inr 1))

/-- Pointing and differentiating the stable homogenized source preserves weak
stability. -/
theorem mvUpperHalfPlaneStableOrZero_binaryRunPointingSource
    {n : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : p ≠ 0)
    (hdegree : p.natDegree ≤ n) {t : ℝ} (ht : 0 < t) :
    MvUpperHalfPlaneStableOrZero (binaryRunPointingSource n p t) := by
  have hsource := mvUpperHalfPlaneStable_binaryRunHomogenizedSource
    hp hp0 hdegree ht
  have hderiv := hsource.pderiv_zero_or_of_finite (Sum.inr 0)
  exact (MvUpperHalfPlaneStable.X_add_X (Sum.inr 0) (Sum.inl 1)).orZero.mul
    hderiv

end

end RealRooted
