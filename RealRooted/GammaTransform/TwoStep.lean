module

public import RealRooted.GammaTransform.ProperPosition

/-!
# Two-step gamma-transform interlacing

An adjacent proper-position pair of gamma polynomials lifts through the two
successive ambient degrees `2n`, `2n + 1`, and `2n + 2`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- An adjacent proper-position pair of gamma polynomials gives two successive
proper-position steps after applying the gamma transform. -/
theorem strictInterl_gammaTransform_two_step
    {n : ℕ} {γ δ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ n) (hδdeg : δ.natDegree ≤ n + 1)
    (hγnn : HasNonnegCoeffs γ) (hδnn : HasNonnegCoeffs δ)
    (hγ0 : γ.coeff 0 ≠ 0) (hδ0 : δ.coeff 0 ≠ 0)
    (hpair : StrictInterl γ δ) :
    StrictInterl (gammaTransform (2 * n) γ)
        ((X + 1) * gammaTransform (2 * n) γ) ∧
      StrictInterl ((X + 1) * gammaTransform (2 * n) γ)
        (gammaTransform (2 * n + 2) δ) := by
  have hγdegEven : γ.natDegree ≤ (2 * n) / 2 := by
    convert hγdeg using 1
    grind
  have hγdegOdd : γ.natDegree ≤ (2 * n + 1) / 2 := by
    convert hγdeg using 1
    grind
  have hδdegEven : δ.natDegree ≤ (2 * n + 1 + 1) / 2 := by
    convert hδdeg using 1
    lia
  have hself : StrictInterl γ γ :=
    StrictInterl.refl hpair.1.1 hpair.1.2
  have hfirst :=
    (strictInterl_gammaTransform_succ_iff hγdegEven hγdegOdd
      hγnn hγnn hγ0 hγ0).2 hself
  have hsecond :=
    (strictInterl_gammaTransform_succ_iff hγdegOdd hδdegEven
      hγnn hδnn hγ0 hδ0).2 hpair
  have hpad := gammaTransform_pad_one (d := 2 * n) hγdegEven
  constructor
  · rw [← hpad]
    exact hfirst
  · rw [← hpad]
    convert hsecond using 1

/-- The three polynomials in the two-step gamma-transform chain have the
expected consecutive ambient degrees. -/
theorem natDegree_gammaTransform_two_step
    {n : ℕ} {γ δ : ℝ[X]}
    (hγ0 : γ.coeff 0 ≠ 0) (hδ0 : δ.coeff 0 ≠ 0) :
    (gammaTransform (2 * n) γ).natDegree = 2 * n ∧
      ((X + 1) * gammaTransform (2 * n) γ).natDegree = 2 * n + 1 ∧
        (gammaTransform (2 * n + 2) δ).natDegree = 2 * n + 2 := by
  have degree_eq (d : ℕ) (p : ℝ[X]) (h0 : p.coeff 0 ≠ 0) :
      (gammaTransform d p).natDegree = d := by
    refine Nat.le_antisymm (natDegree_gammaTransform_le d p) ?_
    exact le_natDegree_of_ne_zero (by simpa only [coeff_ambient_gammaTransform] using h0)
  have hFdeg := degree_eq (2 * n) γ hγ0
  have hFne : gammaTransform (2 * n) γ ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun p : ℝ[X] ↦ p.coeff (2 * n)) hzero
    apply hγ0
    simpa only [coeff_ambient_gammaTransform, coeff_zero] using hcoeff
  have hlinearMonic : (X + 1 : ℝ[X]).Monic := by
    monicity!
  have hlinear : (X + 1 : ℝ[X]).natDegree = 1 := by
    compute_degree!
  refine ⟨hFdeg, ?_, degree_eq (2 * n + 2) δ hδ0⟩
  rw [natDegree_mul hlinearMonic.ne_zero hFne, hlinear, hFdeg]
  lia

end RealRooted
