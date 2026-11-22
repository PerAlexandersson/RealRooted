module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Algebra.Polynomial.Splits
import RealRooted.BorceaBranden.Transcendental.JensenMultiplier
import RealRooted.HermiteBiehler.Basic

/-!
# Uniform bounds from the first real polynomial coefficients

The multivariate Szász estimate gives a uniform Gaussian majorant for
normalized real-rooted univariate polynomials when their linear and quadratic
coefficients are bounded. The degree is unrestricted.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- A uniform bound on the first two nonconstant coefficients of normalized
real-rooted polynomials gives a degree-independent Gaussian bound. -/
theorem exists_norm_eval_le_exp_of_coeff_bounds {K : ℝ} (hK : 0 ≤ K) :
    ∃ B > 0, ∃ C ≥ 0, ∀ p : ℝ[X], p.Splits → p.coeff 0 = 1 →
      ‖p.coeff 1‖ ≤ K → ‖p.coeff 2‖ ≤ K → ∀ z : ℂ,
      ‖(p.map ofRealHom).eval z‖ ≤ B * Real.exp (C * ‖z‖ ^ 2) := by
  let B := 2 * (Real.sqrt (2 * Real.exp 1 ^ 2 - Real.exp 1) / (Real.exp 1 - 1))
  let C := 6 * Real.exp 1 ^ 2 * K ^ 2 + 4 * Real.exp 1 ^ 2 * K
  have he : 1 < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hB : 0 < B := by
    dsimp [B]
    apply mul_pos (by norm_num)
    apply div_pos (Real.sqrt_pos.mpr _) (by linarith)
    nlinarith
  refine ⟨B, hB, C, by dsimp [C]; positivity, ?_⟩
  intro p hp hp0 hp1 hp2 z
  let f : MvPolynomial Unit ℂ := (MvPolynomial.uniqueAlgEquiv ℂ Unit).symm (p.map ofRealHom)
  have hf0 : f.coeff 0 = 1 := by
    dsimp only [f]
    rw [MvPolynomial.coeff_uniqueAlgEquiv_symm]
    simp [hp0]
  have hpne : p ≠ 0 := by intro h; simp [h] at hp0
  have hstable : MvUpperHalfPlaneStable f := by
    intro w hw
    change MvPolynomial.eval₂ (RingHom.id ℂ) w f ≠ 0
    rw [show f = (MvPolynomial.uniqueAlgEquiv ℂ Unit).symm (p.map ofRealHom) from rfl,
      MvPolynomial.eval₂_uniqueAlgEquiv_symm]
    exact isUpperHalfPlaneStable_complexify_of_splits hp hpne (w ()) (hw ())
  have hJ (β : Unit →₀ ℕ) : MvUpperHalfPlaneStable (MvPolynomial.jensenOp β f) :=
    (BorceaBranden.jensenOp_stableOrZero β hstable).resolve_left (fun h => by
      have hc := congrArg (fun q => q.coeff 0) h
      simp [MvPolynomial.coeff_jensenOp, MvPolynomial.jensen, hf0] at hc)
  have h1 : ‖f.coeff (Finsupp.single () 1)‖ ≤ K := by
    dsimp only [f]
    rw [MvPolynomial.coeff_uniqueAlgEquiv_symm]
    simpa using hp1
  have h2 : ‖f.coeff (Finsupp.single () 1 + Finsupp.single () 1)‖ ≤ K := by
    dsimp only [f]
    rw [MvPolynomial.coeff_uniqueAlgEquiv_symm]
    simpa using hp2
  have hC : MvPolynomial.szaszC f ≤ C := by
    simp only [MvPolynomial.szaszC, Finset.univ_unique, Finset.sum_singleton]
    dsimp [C]
    gcongr
  have hs := MvPolynomial.norm_eval_le_of_forall_jensenOp_stable f hf0 hJ
    (norm_nonneg z) (fun _ : Unit => z) (fun _ => le_rfl)
  have heval : MvPolynomial.eval (fun _ : Unit => z) f = (p.map ofRealHom).eval z := by
    change MvPolynomial.eval₂ (RingHom.id ℂ) (fun _ : Unit => z) f = _
    rw [show f = (MvPolynomial.uniqueAlgEquiv ℂ Unit).symm (p.map ofRealHom) from rfl,
      MvPolynomial.eval₂_uniqueAlgEquiv_symm]
    rfl
  rw [heval] at hs
  have hs' : ‖(p.map ofRealHom).eval z‖ ≤ B * Real.exp (MvPolynomial.szaszC f * ‖z‖ ^ 2) := by
    simpa [B] using hs
  exact hs'.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hC (sq_nonneg _))) hB.le)

end RealRooted
