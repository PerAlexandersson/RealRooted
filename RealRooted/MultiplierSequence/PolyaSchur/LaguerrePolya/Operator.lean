import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.Hermite.Poulain
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots.Real
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff

/-!
# Laguerre–Pólya functions of the derivative

If `φ` is in the Laguerre–Pólya class (a locally uniform limit of real-rooted real
polynomials), then `φ(D)`, acting on polynomials through the Taylor coefficients
`aₖ = φ⁽ᵏ⁾(0) / k!`, preserves real-rootedness.  This is the Laguerre–Pólya operator theorem
(G. Pólya and I. Schur, J. Reine Angew. Math. 144 (1914); see also B. Ja. Levin, *Distribution
of zeros of entire functions*, Ch. VIII).  Hermite–Poulain gives it for each approximating
polynomial; the Taylor coefficients converge, and real-rootedness passes to limits of bounded
degree.
-/

open Polynomial Filter Topology RealRooted.HermitePoulain

noncomputable section

namespace RealRooted

/-- The operator `φ(D)` on a real polynomial `g`, through the real parts of the Taylor
coefficients of `φ` at `0` (only `k ≤ deg g` matter). -/
def taylorDifferentialOperator (φ : ℂ → ℂ) (g : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (g.natDegree + 1),
    C ((iteratedDeriv k φ 0 / k.factorial).re) * (derivative^[k]) g

/-- If the coefficients of real-rooted polynomials `p n` converge to the Taylor coefficients of
`φ`, then `φ(D)` maps real-rooted polynomials to real-rooted polynomials or zero. -/
theorem taylorDifferentialOperator_eq_zero_or_splits_of_tendsto_coeff {φ : ℂ → ℂ}
    {p : ℕ → ℝ[X]} (hp : ∀ n, p n = 0 ∨ (p n).Splits)
    (hcoeff : ∀ k, Tendsto (fun n => (p n).coeff k) atTop
      (𝓝 ((iteratedDeriv k φ 0 / k.factorial).re)))
    {g : ℝ[X]} (hg : g.Splits) :
    taylorDifferentialOperator φ g = 0 ∨ (taylorDifferentialOperator φ g).Splits := by
  by_cases hg0 : g = 0
  · left; simp [taylorDifferentialOperator, hg0]
  refine eq_zero_or_splits_of_tendsto_eval_of_natDegree_le (N := g.natDegree)
    (p := fun n => applyAsDifferentialOperator (p n) g) (fun n => ?_) (fun n => ?_) fun z => ?_
  · rw [applyAsDifferentialOperator_eq_sum_range_right]
    refine (natDegree_sum_le_of_forall_le _ _ fun k _ => ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    exact (natDegree_iterate_derivative _ _).trans (Nat.sub_le _ _)
  · rcases hp n with h | h
    · left; simp [applyAsDifferentialOperator, h]
    · by_cases hpn : p n = 0
      · left; simp [applyAsDifferentialOperator, hpn]
      exact differential_operator_preserves_real_rooted ⟨hpn, h⟩ ⟨hg0, hg⟩
  · simp only [applyAsDifferentialOperator_eq_sum_range_right, taylorDifferentialOperator,
      Polynomial.map_sum, Polynomial.map_mul, map_C, eval_finsetSum, eval_mul, eval_C]
    refine tendsto_finsetSum _ fun k _ => ?_
    exact ((Complex.continuous_ofReal.tendsto _).comp (hcoeff k)).mul tendsto_const_nhds

/-- **The Laguerre–Pólya operator theorem.**  For `φ` in the Laguerre–Pólya class, `φ(D)`
maps real-rooted real polynomials to real-rooted polynomials or zero. -/
theorem IsLaguerrePolya.taylorDifferentialOperator_eq_zero_or_splits {φ : ℂ → ℂ}
    (hφ : IsLaguerrePolya φ) {g : ℝ[X]} (hg : g.Splits) :
    taylorDifferentialOperator φ g = 0 ∨ (taylorDifferentialOperator φ g).Splits := by
  obtain ⟨p, hp, hconv⟩ := hφ
  exact taylorDifferentialOperator_eq_zero_or_splits_of_tendsto_coeff hp
    (fun k => Polynomial.tendsto_coeff_of_tendstoLocallyUniformly hconv k) hg

end RealRooted
