import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Derivative
import RealRooted.Wagner

/-!
# Common Combinatorial Example Lemmas

Shared coefficient, leading-coefficient, and elementary interlacing helpers for
the combinatorial example files.
-/

open Polynomial

noncomputable section

namespace RealRooted

lemma nonnegCoeffs_C_mul {a : ℝ} (ha : 0 ≤ a) {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (C a * p) := by
  intro n
  rw [coeff_C_mul]
  exact mul_nonneg ha (hp n)

lemma interlaces_one_linear {p : ℝ[X]} (hp_deg : p.natDegree = 1) :
    Interlaces (1 : ℝ[X]) p := by
  have h1_rr : ((1 : ℝ[X]) ≠ 0 ∧ (1 : ℝ[X]).roots.card = (1 : ℝ[X]).natDegree) := by simp
  have hp_rr : (p ≠ 0 ∧ p.roots.card = p.natDegree) := isRealRooted_of_degree_one hp_deg
  have hp_deg' : p.degree = 1 := by
    rw [degree_eq_natDegree hp_rr.1, hp_deg]
    norm_num
  refine ⟨hp_rr, h1_rr, by simp [Polynomial.natDegree_one, hp_deg], ?_⟩
  refine ⟨[-(p.coeff 1)⁻¹ * p.coeff 0], [], by simp, by simp, ?_, by simp, by simp [ListInterlaces]⟩
  simpa [hp_deg'] using (Polynomial.roots_degree_eq_one (p := p) hp_deg').symm

lemma roots_neg_of_nonnegCoeffs_of_eval_zero_pos {p : ℝ[X]}
    (hrr : p ≠ 0 ∧ p.roots.card = p.natDegree) (hnn : HasNonnegCoeffs p) (hzero : 0 < p.eval 0) :
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
