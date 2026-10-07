import RealRooted.MultivariateStability.Rayleigh

/-!
# Strongly Rayleigh measures are negatively correlated

A weight function `μ` on the subsets of a finite set `σ` has generating polynomial
`subsetGenPoly μ = ∑ S, μ S ∏_{i ∈ S} X i`, which is multiaffine.  The measure is *strongly
Rayleigh* when this polynomial is real stable.  Evaluating the Rayleigh inequality
`∂ᵢP ∂ⱼP ≥ P ∂ᵢ∂ⱼP` (`MvRealStable.isRayleigh_of_isMultiaffine`) at the all-ones point gives
pairwise negative correlation: `μ(i, j ∈ S) μ(Ω) ≤ μ(i ∈ S) μ(j ∈ S)` for `i ≠ j`.

## References

* J. Borcea, P. Brändén, T. M. Liggett, *Negative dependence and the geometry of polynomials*,
  J. Amer. Math. Soc. 22 (2009), 521–567.
-/

open MvPolynomial

noncomputable section

namespace RealRooted

variable {σ : Type*}

private theorem C_mul_prod_X (c : ℝ) (S : Finset σ) :
    C c * ∏ i ∈ S, (X i : MvPolynomial σ ℝ) = monomial (∑ i ∈ S, Finsupp.single i 1) c := by
  have h : ∏ i ∈ S, (X i : MvPolynomial σ ℝ) = monomial (∑ i ∈ S, Finsupp.single i 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [h, C_mul_monomial, mul_one]

variable [Fintype σ]

/-- The generating polynomial `∑ S, μ S ∏_{i ∈ S} X i` of a weight function on subsets. -/
def subsetGenPoly (μ : Finset σ → ℝ) : MvPolynomial σ ℝ :=
  ∑ S, C (μ S) * ∏ i ∈ S, X i

theorem isMultiaffine_subsetGenPoly (μ : Finset σ → ℝ) : (subsetGenPoly μ).IsMultiaffine :=
  IsMultiaffine.sum fun S _ => (IsMultiaffine.prod_X S).C_mul (μ S)

theorem eval_one_subsetGenPoly (μ : Finset σ → ℝ) :
    eval 1 (subsetGenPoly μ) = ∑ S, μ S := by
  simp [subsetGenPoly, map_sum]

theorem eval_one_pderiv_subsetGenPoly [DecidableEq σ] (μ : Finset σ → ℝ) (i : σ) :
    eval 1 (pderiv i (subsetGenPoly μ)) = ∑ S with i ∈ S, μ S := by
  simp [subsetGenPoly, map_sum, C_mul_prod_X, pderiv_monomial, eval_monomial,
    Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_filter]

theorem eval_one_pderiv_pderiv_subsetGenPoly [DecidableEq σ] (μ : Finset σ → ℝ) {i j : σ}
    (hij : i ≠ j) :
    eval 1 (pderiv i (pderiv j (subsetGenPoly μ))) = ∑ S with i ∈ S ∧ j ∈ S, μ S := by
  simp [subsetGenPoly, map_sum, C_mul_prod_X, pderiv_monomial, eval_monomial,
    Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_filter, ite_and, hij]

/-- **Strongly Rayleigh measures are negatively correlated** (Borcea–Brändén–Liggett): if the
generating polynomial of `μ` is real stable, then for `i ≠ j`,
`μ(Ω) μ(i, j ∈ S) ≤ μ(i ∈ S) μ(j ∈ S)`. -/
theorem sum_mul_sum_le_of_mvRealStable_subsetGenPoly [DecidableEq σ] {μ : Finset σ → ℝ}
    (hμ : MvRealStable (subsetGenPoly μ)) {i j : σ} (hij : i ≠ j) :
    (∑ S, μ S) * ∑ S with i ∈ S ∧ j ∈ S, μ S ≤
      (∑ S with i ∈ S, μ S) * ∑ S with j ∈ S, μ S := by
  have h := hμ.isRayleigh_of_isMultiaffine (isMultiaffine_subsetGenPoly μ) i j 1
  rw [eval_rayleighDifference, eval_one_subsetGenPoly, eval_one_pderiv_subsetGenPoly,
    eval_one_pderiv_subsetGenPoly, eval_one_pderiv_pderiv_subsetGenPoly μ hij] at h
  linarith

end RealRooted
