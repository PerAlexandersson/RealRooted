import RealRooted.AissenSchoenbergWhitney
import RealRooted.ClassicalHurwitzMatrix.Stability.Extraction
import RealRooted.ClassicalHurwitzMatrix.TotallyNonnegative

/-!
# Terminal degenerations of the classical Hurwitz criterion

This file handles the boundary where the constant coefficient is positive but
the linear coefficient vanishes. Total nonnegativity then kills every odd
coefficient, while forward ASW controls the remaining even contraction.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- If the corrected Hurwitz matrix is totally nonnegative, a positive
constant coefficient and vanishing linear coefficient force the polynomial to
be Hurwitz stable. -/
theorem isHurwitzStable_of_classicalHurwitzMatrix_isTotallyNonneg_of_coeff_one_eq_zero
    {p : ℝ[X]} (h : (Matrix.hurwitz p.coeff).IsTotallyNonneg)
    (hzero : 0 < p.coeff 0) (hone : p.coeff 1 = 0) :
    IsHurwitzStable p := by
  let q := Polynomial.contract 2 p
  have hodd : ∀ n : ℕ, p.coeff (2 * n + 1) = 0 :=
    h.hurwitz_odd_coeff_eq_zero_of_coeff_one_eq_zero hzero hone
  have hoddContract : Polynomial.contract 2 p.divX = 0 := by
    ext n
    rw [Polynomial.coeff_contract (by decide), Polynomial.coeff_divX,
      coeff_zero]
    simpa [Nat.mul_comm] using hodd n
  have hreconstruct : oddEvenPolynomial 0 q = p := by
    simpa [q, hoddContract] using oddEvenPolynomial_contract_divX_contract p
  have hqcoeffZero : q.coeff 0 = p.coeff 0 := by
    simp [q, Polynomial.coeff_contract]
  have hqne : q ≠ 0 := by
    intro hq
    rw [hq, coeff_zero] at hqcoeffZero
    linarith
  have hqASW := aissenSchoenbergWhitneyForward
    h.hurwitz_contract_two_isPolyaFreqSeq
  apply isHurwitzStable_of_classicalHurwitzMatrix_isTotallyNonneg h
  intro z hz hroot
  have hqroot : (complexify q).IsRoot (z ^ 2) := by
    rw [← hreconstruct] at hroot
    simpa [Polynomial.IsRoot] using hroot
  obtain ⟨r, hr⟩ : z ^ 2 ∈ Complex.ofRealHom.range :=
    hqASW.1.mem_range_of_isRoot hqne hqroot
  have hrroot : q.IsRoot r := by
    have hev : (q.map Complex.ofRealHom).eval (z ^ 2) = 0 := hqroot
    rw [← hr, Polynomial.eval_map, Polynomial.eval₂_hom] at hev
    simp_all
  have hrle : r ≤ 0 := hqASW.2 r ((Polynomial.mem_roots hqne).mpr hrroot)
  have him := congrArg Complex.im hr
  have hre := congrArg Complex.re hr
  simp only [Complex.ofRealHom_eq_coe, Complex.ofReal_im, Complex.ofReal_re,
    pow_two, Complex.mul_im, Complex.mul_re] at him hre
  have hzim : z.im = 0 := by nlinarith
  nlinarith

end RealRooted
