import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Derivative
import RealRooted.Wagner

set_option linter.unnecessarySimpa false

open Polynomial

noncomputable section

namespace RealRooted

lemma nonnegCoeffs_derivative {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs p.derivative := by
  intro n
  rw [coeff_derivative]
  exact mul_nonneg (hp (n + 1)) (by positivity)

lemma hasPosLeadingCoeff_derivative {f : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hdeg : 1 ≤ f.natDegree) :
    HasPosLeadingCoeff f.derivative := by
  unfold HasPosLeadingCoeff at hf_pos ⊢
  rw [leadingCoeff, natDegree_derivative_eq hdeg, coeff_derivative]
  rw [Nat.sub_add_cancel hdeg, coeff_natDegree] at *
  have hdeg_pos : 0 < (f.natDegree : ℝ) := by
    exact_mod_cast hdeg
  nlinarith

lemma interlaces_one_linear {p : ℝ[X]} (hp_deg : p.natDegree = 1) :
    Interlaces (1 : ℝ[X]) p := by
  have h1_rr : IsRealRooted (1 : ℝ[X]) := by
    simpa using isRealRooted_of_deg_zero (p := (1 : ℝ[X])) one_ne_zero (by simp)
  have hp_rr : IsRealRooted p := isRealRooted_of_degree_one hp_deg
  have hp_deg' : p.degree = 1 := by
    rw [degree_eq_natDegree hp_rr.1, hp_deg]
    norm_num
  refine ⟨hp_rr, h1_rr, by simpa [Polynomial.natDegree_one, hp_deg], ?_⟩
  refine ⟨[-(p.coeff 1)⁻¹ * p.coeff 0], [], by simp, by simp, ?_, by simp, by simp [ListInterlaces]⟩
  simpa [hp_deg'] using (Polynomial.roots_degree_eq_one (p := p) hp_deg').symm

lemma roots_neg_of_nonnegCoeffs_of_eval_zero_pos {p : ℝ[X]}
    (hrr : IsRealRooted p) (hnn : HasNonnegCoeffs p) (hzero : 0 < p.eval 0) :
    ∀ r ∈ p.roots, r < 0 := by
  intro r hr
  have hr_nonpos : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hrr hnn r hr
  by_contra hnot
  have hr_zero : r = 0 := by
    linarith
  have hroot0 : p.IsRoot 0 := by
    simpa [hr_zero] using (mem_roots hrr.1).mp hr
  have hEval0 : p.eval 0 = 0 := by
    simpa [Polynomial.IsRoot.def] using hroot0
  linarith

end RealRooted
