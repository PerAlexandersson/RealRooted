module

public import RealRooted.NarayanaTransformation.Basis
public import Mathlib.Basic.Complex.Basic
import RealRooted.Transforms.StirlingRootRegions
import RealRooted.QuadraticRoot
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# The parabolic root criterion for the Stirling transform

We prove the monic PF version of Brenti--Royle--Wagner, *Location of zeros of chromatic
and related polynomials of graphs*, Canad. J. Math. 46 (1994), Theorem 4.7, pp. 67--68,
DOI: 10.4153/CJM-1994-002-3. All inequalities are weak. The paper states the root-location
conclusion without a sign normalization; monicity also gives nonnegative coefficients.

We remove real linear factors or conjugate-pair quadratic factors, translate by the
falling-factorial length, and use the existing Touchard/Poisson multiplication theorem.
The disk corollary is the root-region calculation used in Proposition 4.10 for cycles.
-/

public section

open Polynomial

namespace RealRooted.StirlingRootRegion

noncomputable section

/-- A translated real linear factor has PF Touchard image when its root is at most the
translation parameter, as in Brenti--Royle--Wagner, Theorem 4.7. -/
theorem isPFPolynomial_linear {m r : ℝ} (hr : r ≤ m) :
    IsPFPolynomial (basisTransform touchard ((X - C r).comp (X + C m))) := by
  have hcomp : (X - C r : ℝ[X]).comp (X + C m) = X + C (m - r) := by
    simp only [sub_comp, X_comp, C_comp, map_sub]
    ring
  rw [hcomp, basisTransform_touchard_X_add_C]
  exact isPFPolynomial_X_add_C (sub_nonneg.mpr hr)

/-- The translated conjugate-pair quadratic in Brenti--Royle--Wagner, Theorem 4.7,
has PF Touchard image on the closed parabola. -/
theorem isPFPolynomial_quadratic {m s t : ℝ}
    (ht : 4 * t ^ 2 ≤ 1 + 4 * m - 4 * s) :
    IsPFPolynomial (basisTransform touchard
      (((X - C s) ^ 2 + C (t ^ 2)).comp (X + C m))) := by
  have htransform : basisTransform touchard
      (((X - C s) ^ 2 + C (t ^ 2)).comp (X + C m)) =
      X ^ 2 + C (1 + 2 * m - 2 * s) * X + C ((m - s) ^ 2 + t ^ 2) := by
    have hcomp : ((X - C s) ^ 2 + C (t ^ 2) : ℝ[X]).comp (X + C m) =
        (X + C (m - s)) * (X + C (m - s)) + C (t ^ 2) := by
      simp only [add_comp, pow_comp, sub_comp, X_comp, C_comp, map_sub]
      ring
    rw [hcomp, Polynomial.basisTransform_add, basisTransform_touchard_mul_X_add_C,
      basisTransform_touchard_X_add_C]
    simp only [Polynomial.basisTransform_C, touchard_zero, mul_one,
      derivative_add, derivative_X, derivative_C, add_zero]
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
    ring
  rw [htransform]
  apply IsPFPolynomial.of_realRooted_nonneg
  · exact ((hasNonnegCoeffs_X.pow 2).add
      ((hasNonnegCoeffs_C (by nlinarith [sq_nonneg t])).mul hasNonnegCoeffs_X)).add
        (hasNonnegCoeffs_C (by positivity))
  · apply monicQuadraticPoly_splits_iff_discrim_nonneg.mpr
    nlinarith

/-- A positive-degree monic polynomial satisfying the root bounds has an admissible
linear or conjugate-pair quadratic factor. -/
private theorem exists_factor {m : ℝ} {p : ℝ[X]} (hd : p.natDegree ≠ 0)
    (hr : ∀ r : ℝ, p.IsRoot r → r ≤ m)
    (hz : ∀ z : ℂ, aeval z p = 0 → z.im ≠ 0 → 4 * z.im ^ 2 ≤ 1 + 4 * m - 4 * z.re) :
    ∃ g q : ℝ[X], p = g * q ∧ g.Monic ∧ 0 < g.natDegree ∧
      IsPFPolynomial (basisTransform touchard (g.comp (X + C m))) := by
  obtain ⟨z, hzp⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ p
    (degree_ne_of_natDegree_ne hd)
  by_cases hi : z.im = 0
  · have hzr : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hi]
    have hre : p.IsRoot z.re := by
      apply isRoot_of_aeval_algebraMap_eq_zero (S := ℂ)
      simpa only [Complex.coe_algebraMap, ← hzr] using hzp
    obtain ⟨q, hq⟩ := (dvd_iff_isRoot).mpr hre
    exact ⟨X - C z.re, q, hq, monic_X_sub_C _, by simp,
      isPFPolynomial_linear (hr _ hre)⟩
  · obtain ⟨q, hq⟩ := p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hzp hi
    have heq : X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) =
        (X - C z.re) ^ 2 + C (z.im ^ 2) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [map_add, map_mul, map_ofNat, pow_two]
      ring
    refine ⟨_, q, hq, (isMonicOfDegree_sub_add_two _ _).monic, ?_, ?_⟩
    · rw [(isMonicOfDegree_sub_add_two (2 * z.re) (‖z‖ ^ 2)).natDegree_eq]
      norm_num
    · rw [heq]
      exact isPFPolynomial_quadratic (hz z hzp hi)

/-- The translated Touchard image is PF under the closed root bounds of
Brenti--Royle--Wagner, Theorem 4.7. -/
theorem isPFPolynomial_comp {m : ℝ} {p : ℝ[X]} (hp : p.Monic)
    (hr : ∀ r : ℝ, p.IsRoot r → r ≤ m)
    (hz : ∀ z : ℂ, aeval z p = 0 → z.im ≠ 0 → 4 * z.im ^ 2 ≤ 1 + 4 * m - 4 * z.re) :
    IsPFPolynomial (basisTransform touchard (p.comp (X + C m))) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hd : p.natDegree = 0
    · rw [eq_one_of_monic_natDegree_zero hp hd, one_comp]
      exact touchardTransformPreservesPF IsPFPolynomial.one
    obtain ⟨g, q, hfac, hg, hgdeg, hgpf⟩ := exists_factor hd hr hz
    have hq : q.Monic := hg.of_mul_monic_left (hfac ▸ hp)
    have hqdeg : q.natDegree < n := by
      have hdeg := natDegree_mul hg.ne_zero hq.ne_zero
      rw [← hfac, hn] at hdeg
      lia
    rw [hfac, mul_comp]
    apply isPFPolynomial_basisTransform_touchard_mul hgpf
    apply ih q.natDegree hqdeg hq
    · intro r hroot
      apply hr r
      simp only [hfac, IsRoot.def, eval_mul, hroot.eq_zero, mul_zero]
    · intro z hroot hi
      apply hz z _ hi
      simp only [hfac, map_mul, hroot, mul_zero]
    · rfl

/-- Brenti--Royle--Wagner's parabolic criterion (Theorem 4.7), with monicity
ensuring nonnegative coefficients as well as real nonpositive zeros. The natural
number `m` is the falling-factorial prefix length; all root inequalities are weak. -/
theorem isPFPolynomial_fallingFactorial_mul (m : ℕ) {p : ℝ[X]} (hp : p.Monic)
    (hr : ∀ r : ℝ, p.IsRoot r → r ≤ (m : ℝ))
    (hz : ∀ z : ℂ, aeval z p = 0 → z.im ≠ 0 →
      4 * z.im ^ 2 ≤ 1 + 4 * (m : ℝ) - 4 * z.re) :
    IsPFPolynomial (basisTransform touchard (fallingFactorialPolynomial m * p)) := by
  exact isPFPolynomial_basisTransform_touchard_fallingFactorial_mul m
    (isPFPolynomial_comp hp hr hz)

/-- The closed disk about one of radius one lies in the root region for `m = 2`.
This is the criterion used for cycles in Brenti--Royle--Wagner, Proposition 4.10,
after removing the falling-factorial factor `X * (X - 1)` from the chromatic polynomial. -/
theorem isPFPolynomial_fallingFactorial_two_mul {p : ℝ[X]} (hp : p.Monic)
    (hroot : ∀ z : ℂ, aeval z p = 0 → (z.re - 1) ^ 2 + z.im ^ 2 ≤ 1) :
    IsPFPolynomial (basisTransform touchard (fallingFactorialPolynomial 2 * p)) := by
  apply isPFPolynomial_fallingFactorial_mul 2 hp
  · intro r hr
    have hz : aeval (r : ℂ) p = 0 := by
      rw [← Complex.coe_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval, hr.eq_zero,
        map_zero]
    have hdisk := hroot (r : ℂ) hz
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_pow (by decide : 2 ≠ 0),
      add_zero] at hdisk
    change r ≤ 2
    nlinarith
  · intro z hz _
    have hdisk := hroot z hz
    norm_num
    nlinarith [sq_nonneg (2 * z.re - 3)]

/-- Brenti--Royle--Wagner, Proposition 4.10: the Stirling transform of the cycle
chromatic polynomial is PF. For graphs the usual range is `n ≥ 3`; the polynomial
formula also works for `n = 2`. No graph-model identity is assumed in this statement. -/
theorem isPFPolynomial_cycle (n : ℕ) (hn : 2 ≤ n) :
    IsPFPolynomial (basisTransform touchard
      ((X - C 1) ^ n + C ((-1 : ℝ) ^ n) * (X - C 1))) := by
  let p : ℝ[X] := (X - C 1) ^ n + C ((-1 : ℝ) ^ n) * (X - C 1)
  have hp : p.Monic := by
    exact (((isMonicOfDegree_X_sub_one (1 : ℝ)).pow n).add_right
      (lt_of_le_of_lt (natDegree_C_mul_le _ _)
        (by rw [natDegree_X_sub_C, one_mul]; lia))).monic
  have hdvd : X * (X - C 1) ∣ p := by
    have hc : IsCoprime (X : ℝ[X]) (X - C 1) := by
      simpa using (isCoprime_X_sub_C_of_isUnit_sub
        (a := (0 : ℝ)) (b := 1) (by norm_num))
    apply hc.mul_dvd
    · have hzero : p.IsRoot 0 := by simp [p, IsRoot.def]
      simpa using (dvd_iff_isRoot).mpr hzero
    · apply (dvd_iff_isRoot).mpr
      simp [p, IsRoot.def, show n ≠ 0 by lia]
  obtain ⟨q, hq⟩ := hdvd
  have hff : fallingFactorialPolynomial 2 = X * (X - C 1) := by
    norm_num [fallingFactorialPolynomial, Finset.prod_range_succ]
  change IsPFPolynomial (basisTransform touchard p)
  rw [hq, ← hff]
  apply isPFPolynomial_fallingFactorial_two_mul
    (((monic_X).mul (monic_X_sub_C 1)).of_mul_monic_left (hq ▸ hp))
  intro z hzq
  have hz : aeval z p = 0 := by rw [hq, map_mul, hzq, mul_zero]
  have heq : (z - 1) ^ n = -((-1 : ℂ) ^ n * (z - 1)) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa [p] using hz
  have hnorm : ‖z - 1‖ ^ n = ‖z - 1‖ := by
    simpa only [norm_pow, norm_neg, norm_mul, norm_one, one_pow, one_mul]
      using congrArg norm heq
  have hle : ‖z - 1‖ ≤ 1 := by
    by_cases hzero : ‖z - 1‖ = 0
    · rw [hzero]; norm_num
    have hpow : ‖z - 1‖ ^ (n - 1) = 1 := by
      apply mul_right_cancel₀ hzero
      rw [← pow_succ, Nat.sub_add_cancel (by lia : 1 ≤ n), hnorm, one_mul]
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by lia : n - 1 ≠ 0)).mp hpow.le
  have hsq : ‖z - 1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z - 1)]
  rw [Complex.sq_norm, Complex.normSq_apply] at hsq
  simpa [pow_two] using hsq

end

end RealRooted.StirlingRootRegion
