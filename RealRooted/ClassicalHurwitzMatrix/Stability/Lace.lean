import RealRooted.ClassicalHurwitzMatrix.Stability.OddEvenConverse
import RealRooted.ClassicalHurwitzMatrix.Stability.WeakConverse

/-!
# The two-row Lace matrix of a Hurwitz-stable polynomial

For `F = q(X²) + X p(X²)` with coefficients `c`, the two-row Lace matrix of `q` and `p` has
entries `lacePair q.coeff p.coeff i j = c (i - 2 j)` (zero when `i < 2 j`).  It is the
submatrix, shifted by `N ≥ deg F`, of the classical Hurwitz matrix of the reversal
`reflect N F`.  Reversal preserves Hurwitz stability, so the Hurwitz criterion
(`Matrix.hurwitz_isTotallyNonneg_of_hurwitzStable`) makes the Lace matrix totally
nonnegative (issue #1113).
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Reversal of a complex polynomial keeps it free of zeros in the open right half-plane:
`(reflect N f)(z) = 0` iff `f(z⁻¹) = 0`, and `z⁻¹` lies in the same half-plane. -/
private theorem reflect_eval_ne_zero_of_re_pos {f : ℂ[X]} {N : ℕ} (hN : f.natDegree ≤ N)
    (hf : ∀ z : ℂ, 0 < z.re → f.eval z ≠ 0) :
    ∀ z : ℂ, 0 < z.re → (reflect N f).eval z ≠ 0 := by
  intro z hz h
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  let _ : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz0)
  have key := eval₂_reflect_eq_zero_iff (RingHom.id ℂ) z⁻¹ N f hN
  rw [invOf_eq_inv, inv_inv] at key
  refine hf z⁻¹ ?_ (key.mp h)
  rw [Complex.inv_re]
  exact div_pos hz (Complex.normSq_pos.mpr hz0)

/-- Reversal `x ↦ xᴺ F(1/x)` preserves Hurwitz stability. -/
theorem IsHurwitzStable.reflect {F : ℝ[X]} (hF : IsHurwitzStable F) {N : ℕ}
    (hN : F.natDegree ≤ N) : IsHurwitzStable (reflect N F) := by
  refine ⟨fun k ↦ by simpa [coeff_reflect] using hF.hasNonnegCoeffs (revAt N k), ?_⟩
  have h := reflect_eval_ne_zero_of_re_pos (f := complexify F) (natDegree_map_le.trans hN)
    hF.rightHalfPlaneStable
  simpa [complexify, reflect_map, IsRightHalfPlaneStable] using h

/-- The Lace matrix of the even and odd parts is a shifted submatrix of the Hurwitz matrix of
the reversed polynomial. -/
theorem lacePair_eq_submatrix_hurwitz_reflect (p q : ℝ[X]) {N : ℕ}
    (hN : (oddEvenPolynomial p q).natDegree ≤ N) :
    lacePair q.coeff p.coeff =
      (Matrix.hurwitz (reflect N (oddEvenPolynomial p q)).coeff).submatrix (· + N) (· + N) := by
  ext i j
  have hc (k : ℕ) (hk : N < k) : (oddEvenPolynomial p q).coeff k = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN.trans_lt hk)
  simp only [lacePair, Matrix.of_apply, toeplitz_apply, Matrix.submatrix_apply,
    Matrix.hurwitz_apply, coeff_reflect]
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' i
  · simp only [Nat.mul_mod_right, ite_true, Nat.mul_div_cancel_left _ two_pos]
    by_cases hj : j ≤ r
    · rw [ite_eq_left hj]
      by_cases hle : 2 * r + N ≤ 2 * (j + N)
      · rw [ite_eq_left hle, revAt_le (by lia),
          show N - (2 * (j + N) - (2 * r + N)) = 2 * (r - j) by lia,
          coeff_oddEvenPolynomial_even]
      · rw [ite_eq_right hle, ← coeff_oddEvenPolynomial_even p q, hc _ (by lia)]
    · rw [ite_eq_right hj, ite_eq_left (by lia), revAt_eq_self_of_lt (by lia), hc _ (by lia)]
  · have h1 : (2 * r + 1) % 2 = 1 := by lia
    have h2 : (2 * r + 1) / 2 = r := by lia
    simp only [h1, h2, one_ne_zero, ite_false]
    by_cases hj : j ≤ r
    · rw [ite_eq_left hj]
      by_cases hle : 2 * r + 1 + N ≤ 2 * (j + N)
      · rw [ite_eq_left hle, revAt_le (by lia),
          show N - (2 * (j + N) - (2 * r + 1 + N)) = 2 * (r - j) + 1 by lia,
          coeff_oddEvenPolynomial_odd]
      · rw [ite_eq_right hle, ← coeff_oddEvenPolynomial_odd p q, hc _ (by lia)]
    · rw [ite_eq_right hj, ite_eq_left (by lia), revAt_eq_self_of_lt (by lia), hc _ (by lia)]

/-- If `q(X²) + X p(X²)` is Hurwitz stable, then the two-row Lace matrix of `q` and `p` is
totally nonnegative (issue #1113).  This is the reversed-row orientation: the forward
orientation `FullyInterlacingPair p.coeff q.coeff` fails already for `X + 2`, `X + 1`. -/
theorem fullyInterlacingPair_of_isHurwitzStable_oddEvenPolynomial {p q : ℝ[X]}
    (h : IsHurwitzStable (oddEvenPolynomial p q)) : FullyInterlacingPair q.coeff p.coeff := by
  rw [FullyInterlacingPair, lacePair_eq_submatrix_hurwitz_reflect p q le_rfl]
  exact (Matrix.hurwitz_isTotallyNonneg_of_hurwitzStable (h.reflect le_rfl)).submatrix
    (strictMono_id.add_const _) (strictMono_id.add_const _)

/-- Strictly interlacing nonnegative odd and even parts have a totally nonnegative Lace
matrix: the Lace form of the Hermite–Biehler theorem. -/
theorem StrictInterl.fullyInterlacingPair {p q : ℝ[X]} (hp : HasNonnegCoeffs p)
    (hq : HasNonnegCoeffs q) (hpq : StrictInterl p q) : FullyInterlacingPair q.coeff p.coeff :=
  fullyInterlacingPair_of_isHurwitzStable_oddEvenPolynomial
    ((isHurwitzStable_oddEvenPolynomial_iff hpq.1.1 hpq.2.1.1).mpr ⟨hp, hq, hpq⟩)

end RealRooted
