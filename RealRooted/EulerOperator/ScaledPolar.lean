import RealRooted.EulerOperator.Polar
import RealRooted.RootContinuity

/-!
# Scale-two polar operator

The transformed polar operator `N - 2 theta` preserves polynomial
Pólya-frequency data in the degree range where its coefficients stay
nonnegative.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Composing `theta` with the `-X²` substitution doubles its eigenvalue. -/
theorem theta_comp_negXsq (p : ℝ[X]) :
    theta (p.comp (-(X : ℝ[X]) ^ 2)) = C 2 * (theta p).comp (-(X : ℝ[X]) ^ 2) := by
  unfold theta
  rw [Polynomial.derivative_comp]
  simp [Polynomial.derivative_neg, Polynomial.derivative_pow]
  ring

/-- The scale-two polar operator becomes `polarTheta` after the `-X²`
substitution. -/
theorem scaledPolarTwo_comp_negXsq (N : ℕ) (h : ℝ[X]) :
    (C (N : ℝ) * h - C 2 * theta h).comp (-(X : ℝ[X]) ^ 2)
      = polarTheta N (h.comp (-(X : ℝ[X]) ^ 2)) := by
  unfold polarTheta
  rw [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.C_comp, theta_comp_negXsq]

/-- The substitution `X ↦ -X²` turns a linear factor with a nonpositive real
root into a split quadratic. -/
theorem X_sub_C_comp_negXsq_splits (r : ℝ) (hr : r ≤ 0) :
    ((X - C r).comp (-(X : ℝ[X]) ^ 2)).Splits := by
  have hsquare : (Real.sqrt (-r)) ^ 2 = -r := Real.sq_sqrt (by linarith)
  set s := Real.sqrt (-r) with hsdef
  have hfactor : (X - C r).comp (-(X : ℝ[X]) ^ 2)
      = -((X - C s) * (X + C s)) := by
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    have hconstant_square : (C s) ^ 2 = C (-r) := by
      rw [← Polynomial.C_pow, hsquare]
    have hroot : (C r : ℝ[X]) = -(C s) ^ 2 := by
      rw [hconstant_square]
      simp
    rw [hroot]
    ring
  rw [hfactor]
  refine Polynomial.Splits.neg (Polynomial.Splits.mul ?_ ?_)
  · exact (isRealRooted_X_sub_C s).2
  · have hrewrite : (X + C s : ℝ[X]) = X - C (-s) := by
      rw [map_neg]
      ring
    rw [hrewrite]
    exact (isRealRooted_X_sub_C (-s)).2

/-- The substitution `X ↦ -X²` preserves splitness for PF polynomials. -/
theorem comp_negXsq_splits_of_isPFPolynomial {h : ℝ[X]} (hh : IsPFPolynomial h) :
    (h.comp (-(X : ℝ[X]) ^ 2)).Splits := by
  by_cases hzero : h = 0
  · simp [hzero]
  have hsplits : h.Splits := (hh.ne_zero_and_splits hzero).2
  have hroots_card : h.roots.card = h.natDegree := card_roots_of_splits hsplits
  have hfactor : h = C h.leadingCoeff * (h.roots.map fun r => X - C r).prod :=
    (C_leadingCoeff_mul_prod_multiset_X_sub_C hroots_card).symm
  rw [hfactor, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.multiset_prod_comp]
  apply Polynomial.Splits.mul (Polynomial.Splits.C _)
  rw [Multiset.map_map]
  refine Multiset.prod_induction (fun q : ℝ[X] => q.Splits) _
    (fun a b ha hb => Polynomial.Splits.mul ha hb) Polynomial.Splits.one ?_
  intro q hq
  simp only [Multiset.mem_map, Function.comp] at hq
  obtain ⟨r, hr_mem, rfl⟩ := hq
  exact X_sub_C_comp_negXsq_splits r (hh.roots_nonpos r hr_mem)

/-- If `P.comp (-X²)` splits, then `P` splits. -/
theorem splits_of_comp_negXsq_splits {P : ℝ[X]}
    (hcomp : (P.comp (-(X : ℝ[X]) ^ 2)).Splits) :
    P.Splits := by
  by_cases hzero : P = 0
  · simp [hzero]
  have hquadratic_degree : (-(X : ℝ[X]) ^ 2).natDegree = 2 := by
    rw [Polynomial.natDegree_neg, Polynomial.natDegree_X_pow]
  have hcomposition_nonzero : P.comp (-(X : ℝ[X]) ^ 2) ≠ 0 := by
    intro hcomposition_zero
    have hdegree : (P.comp (-(X : ℝ[X]) ^ 2)).natDegree = P.natDegree * 2 := by
      rw [Polynomial.natDegree_comp, hquadratic_degree]
    rw [hcomposition_zero, Polynomial.natDegree_zero] at hdegree
    have hP_degree : P.natDegree = 0 := by
      lia
    have hself : P.comp (-(X : ℝ[X]) ^ 2) = P := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hP_degree, Polynomial.C_comp]
    rw [hself] at hcomposition_zero
    exact hzero hcomposition_zero
  apply splits_of_forall_aeval_im_eq_zero
  intro w hw
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z ^ 2 = -w := by
    obtain ⟨z, hz⟩ := Complex.exists_root (f := X ^ 2 - C (-w))
      (by rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num)
    have hz' : z ^ 2 - (-w) = 0 := by
      simpa [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C] using hz
    exact ⟨z, by linear_combination hz'⟩
  have hzroot : (P.comp (-(X : ℝ[X]) ^ 2)).aeval z = 0 := by
    rw [Polynomial.aeval_comp]
    have hsubstitution : (aeval z) (-(X : ℝ[X]) ^ 2) = -(z ^ 2) := by
      simp
    rw [hsubstitution, hz, neg_neg]
    exact hw
  have hzim : z.im = 0 := im_eq_zero_of_aeval_eq_zero hcomposition_nonzero hcomp hzroot
  have hrewrite : w = -(z ^ 2) := by
    rw [hz]
    ring
  rw [hrewrite, Complex.neg_im]
  have hsquare_im : (z ^ 2).im = 0 := by
    rw [pow_two, Complex.mul_im, hzim]
    ring
  rw [hsquare_im]
  ring

/-- **Scale-two polar operator preserves the PF cone under a degree bound.** -/
theorem scaledPolarTwo_preserves_pf {N : ℕ} {h : ℝ[X]}
    (hh : IsPFPolynomial h) (hdegree : 2 * h.natDegree ≤ N) :
    IsPFPolynomial (C (N : ℝ) * h - C 2 * theta h) := by
  have hnonnegative : HasNonnegCoeffs (C (N : ℝ) * h - C 2 * theta h) := by
    intro k
    have hcoefficient :
        (C (N : ℝ) * h - C 2 * theta h).coeff k = ((N : ℝ) - 2 * k) * h.coeff k := by
      simp [coeff_theta]
      ring
    rw [hcoefficient]
    by_cases hindex : k ≤ h.natDegree
    · have hindex_bound : (2 : ℝ) * k ≤ N := by
        have hnatural : 2 * k ≤ N := le_trans (Nat.mul_le_mul_left 2 hindex) hdegree
        exact_mod_cast hnatural
      exact mul_nonneg (by linarith) (hh.hasNonnegCoeffs k)
    · have hcoefficient_zero : h.coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_le hindex)
      simp [hcoefficient_zero]
  have hsplits : (C (N : ℝ) * h - C 2 * theta h).Splits := by
    apply splits_of_comp_negXsq_splits
    rw [scaledPolarTwo_comp_negXsq]
    have hcomposition_splits : (h.comp (-(X : ℝ[X]) ^ 2)).Splits :=
      comp_negXsq_splits_of_isPFPolynomial hh
    have hcomposition_degree : (h.comp (-(X : ℝ[X]) ^ 2)).natDegree ≤ N := by
      have hquadratic_degree : (-(X : ℝ[X]) ^ 2).natDegree = 2 := by
        rw [Polynomial.natDegree_neg, Polynomial.natDegree_X_pow]
      rw [Polynomial.natDegree_comp, hquadratic_degree]
      lia
    exact polarTheta_splits_of_splits hcomposition_splits hcomposition_degree
  exact IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hnonnegative (Or.inr hsplits)

end RealRooted
