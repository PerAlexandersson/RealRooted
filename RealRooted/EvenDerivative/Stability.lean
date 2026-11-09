module

public import RealRooted.EvenDerivative.Basic
public import RealRooted.Multiaffine
public import RealRooted.HermiteBiehler.Basic
import RealRooted.BorceaBranden.Applications.PolarizationIff
import RealRooted.ClassicalHurwitzMatrix.Stability.HermiteBiehler
import RealRooted.Mathlib.Algebra.Polynomial.Derivative.Prod

/-!
# The polarization of the even-derivative test is real stable

For a coefficient sequence `c` with `c 0 = 1` we form the symmetric multiaffine polynomial
`M_n(z) = ∑_{k ≤ n/2} (-1)ᵏ cₖ (2k)! eₙ₋₂ₖ(z)`.  Its diagonal is the test polynomial `p_n`
(`evenDerivativeTest c n`), so by Grace–Walsh–Szegő `M_n` is real stable as soon as `p_n` is
real-rooted.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

variable {c : ℕ → ℝ}

/-- The polarization `M_n(z) = ∑_{k ≤ n/2} (-1)ᵏ cₖ (2k)! eₙ₋₂ₖ(z)` of the test polynomial. -/
def evenDerivativePolarization (c : ℕ → ℝ) (n : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    MvPolynomial.C ((-1) ^ k * c k * ((2 * k).factorial : ℝ)) *
      MvPolynomial.esymm (Fin n) ℝ (n - 2 * k)

/-- The polarization `M_n` is symmetric. -/
theorem isSymmetric_evenDerivativePolarization (n : ℕ) :
    (evenDerivativePolarization c n).IsSymmetric := by
  change evenDerivativePolarization c n ∈ MvPolynomial.symmetricSubalgebra (Fin n) ℝ
  refine Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (fun e => MvPolynomial.rename_C e _)
    (MvPolynomial.esymm_isSymmetric (σ := Fin n) ℝ _)

/-- The polarization `M_n` is multiaffine. -/
theorem isMultiaffine_evenDerivativePolarization (n : ℕ) :
    MvPolynomial.IsMultiaffine (evenDerivativePolarization c n) :=
  MvPolynomial.IsMultiaffine.sum fun _ _ => (MvPolynomial.IsMultiaffine.esymm _).C_mul _

/-- The diagonal specialization of `e_j` is `C(n, j) Xʲ`. -/
private theorem aeval_X_esymm (n j : ℕ) :
    MvPolynomial.aeval (fun _ : Fin n => (X : ℝ[X])) (MvPolynomial.esymm (Fin n) ℝ j) =
      C (n.choose j : ℝ) * X ^ j := by
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, Finset.esymm_map_val]
  have : ∀ t ∈ (Finset.univ : Finset (Fin n)).powersetCard j, ∏ _i ∈ t, (X : ℝ[X]) = X ^ j :=
    fun t ht => by rw [Finset.prod_const, (Finset.mem_powersetCard.mp ht).2]
  rw [Finset.sum_congr rfl this]
  simp [Finset.card_powersetCard, nsmul_eq_mul]

/-- The diagonal of the polarization is the test polynomial. -/
theorem aeval_X_evenDerivativePolarization (n : ℕ) :
    MvPolynomial.aeval (fun _ : Fin n => (X : ℝ[X])) (evenDerivativePolarization c n) =
      evenDerivativeTest c n := by
  rw [evenDerivativePolarization, evenDerivativeTest, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : 2 * k ≤ n := by simp only [Finset.mem_range] at hk; lia
  rw [map_mul, MvPolynomial.aeval_C, aeval_X_esymm, Nat.choose_symm hk',
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [Polynomial.algebraMap_eq, ← mul_assoc, ← C_mul]
  push_cast
  ring_nf

/-- If `p_n` is real-rooted, then the polarization `M_n` is real stable
(Grace–Walsh–Szegő). -/
theorem mvRealStable_evenDerivativePolarization (hc : c 0 = 1) {n : ℕ}
    (h : (evenDerivativeTest c n).Splits) : MvRealStable (evenDerivativePolarization c n) := by
  refine (mvRealStable_iff_aeval_X_ne_zero_and_splits (isSymmetric_evenDerivativePolarization n)
    (isMultiaffine_evenDerivativePolarization n)).2 ?_
  rw [aeval_X_evenDerivativePolarization]
  exact ⟨evenDerivativeTest_ne_zero hc n, h⟩

/-- Evaluation of the complexification of `T_c f`. -/
theorem eval_complexify_evenDerivativeOperator {f : ℝ[X]} {m : ℕ} (hm : f.natDegree / 2 < m)
    (w : ℂ) :
    (complexify (evenDerivativeOperator c f)).eval w =
      ∑ k ∈ Finset.range m, (c k : ℂ) * w ^ k * ((derivative^[2 * k]) (complexify f)).eval w := by
  rw [evenDerivativeOperator_eq_sum_range hm]
  simp only [complexify, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Polynomial.iterate_derivative_map]
  rfl

private theorem eval_complexifyMv_C_mul_esymm {n : ℕ} (a : ℝ) (j : ℕ) (s : Fin n → ℂ) :
    MvPolynomial.eval s (MvPolynomial.map Complex.ofRealHom
        (MvPolynomial.C a * MvPolynomial.esymm (Fin n) ℝ j)) =
      (a : ℂ) * ∑ t ∈ (Finset.univ : Finset (Fin n)).powersetCard j, ∏ i ∈ t, s i := by
  simp [MvPolynomial.esymm]

private theorem neg_sq_pow_mul_neg_pow (z : ℂ) (k m : ℕ) :
    (-z ^ 2) ^ k * (-z) ^ m = (-1) ^ (2 * k + m) * z ^ (2 * k + m) * (-1) ^ k := by
  rw [neg_pow (z ^ 2), neg_pow z, pow_add, pow_add, pow_mul, pow_mul, neg_one_sq, one_pow]
  ring

private theorem natDegree_prod_X_add_C_le {n : ℕ} (r : Fin n → ℝ) :
    (∏ i, (X + C (r i))).natDegree ≤ n :=
  (natDegree_prod_le _ _).trans (by simp)

/-- **The polarization identity.**  For `f = ∏ᵢ (u + rᵢ)` and `z ≠ 0`,
`T_c f(-z²) = (-1)ⁿ zⁿ M_n(s₁(z), …, sₙ(z))` with `sᵢ(z) = z - rᵢ / z`. -/
theorem eval_complexify_evenDerivativeOperator_prod {n : ℕ} (r : Fin n → ℝ) {z : ℂ}
    (hz : z ≠ 0) :
    (complexify (evenDerivativeOperator c (∏ i, (X + C (r i))))).eval (-z ^ 2) =
      (-1) ^ n * z ^ n * MvPolynomial.eval (fun i => z - (r i : ℂ) / z)
        (complexifyMv (evenDerivativePolarization c n)) := by
  have hdeg := natDegree_prod_X_add_C_le r
  have hfC : complexify (∏ i, (X + C (r i))) = ∏ i, (X + C (r i : ℂ)) := by
    simp [complexify, Polynomial.map_prod]
  rw [eval_complexify_evenDerivativeOperator (m := n / 2 + 1) (by lia), hfC,
    evenDerivativePolarization]
  simp only [complexifyMv, map_sum, eval_complexifyMv_C_mul_esymm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : 2 * k ≤ n := by simp only [Finset.mem_range] at hk; lia
  rw [eval_iterate_derivative_prod_X_add_C _ _ (by simpa using hk')]
  have key : ∀ t ∈ (Finset.univ : Finset (Fin n)).powersetCard (n - 2 * k),
      ∏ i ∈ t, (-z ^ 2 + (r i : ℂ)) = (-z) ^ (n - 2 * k) * ∏ i ∈ t, (z - (r i : ℂ) / z) := by
    intro t ht
    have hcard := (Finset.mem_powersetCard.1 ht).2
    rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    field_simp
    ring
  rw [Finset.card_univ, Fintype.card_fin, Finset.sum_congr rfl key, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have h := neg_sq_pow_mul_neg_pow z k (n - 2 * k)
  rw [show 2 * k + (n - 2 * k) = n by lia] at h
  push_cast
  linear_combination (c k * ((2 * k).factorial : ℂ) *
    ∑ t ∈ (Finset.univ : Finset (Fin n)).powersetCard (n - 2 * k), ∏ i ∈ t, (z - (r i : ℂ) / z)) * h

/-- The half-plane map `s(z) = z - r / z` sends the upper half-plane into itself for `r ≥ 0`. -/
private theorem im_sub_div_pos {z : ℂ} (hz : 0 < z.im) {r : ℝ} (hr : 0 ≤ r) :
    0 < (z - (r : ℂ) / z).im := by
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.2 fun h => by simp [h] at hz
  rw [Complex.sub_im, Complex.div_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, zero_sub]
  have : 0 ≤ r * z.im / Complex.normSq z := by positivity
  linarith [show - -(r * z.im / Complex.normSq z) = r * z.im / Complex.normSq z by ring]

/-- **Real-rootedness of the image of a product of linear factors.**  If the test polynomial `p_n`
is real-rooted, then `T_c ∏ᵢ (u + rᵢ)` is real-rooted for all `rᵢ ≥ 0`. -/
theorem splits_evenDerivativeOperator_prod (hc : c 0 = 1) {n : ℕ}
    (htest : (evenDerivativeTest c n).Splits) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) :
    (evenDerivativeOperator c (∏ i, (X + C (r i)))).Splits := by
  refine Polynomial.Splits.of_comp_neg_X_sq (IsUpperHalfPlaneStable.splits_complexify ?_)
  intro z hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hcomp : (complexify ((evenDerivativeOperator c (∏ i, (X + C (r i)))).comp (-(X ^ 2)))).eval
      z = (complexify (evenDerivativeOperator c (∏ i, (X + C (r i))))).eval (-z ^ 2) := by
    simp only [complexify, Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_pow,
      Polynomial.map_X, eval_comp, eval_neg, eval_pow, eval_X]
  rw [hcomp, eval_complexify_evenDerivativeOperator_prod r hz0]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) (pow_ne_zero _ hz0)) ?_
  exact mvRealStable_evenDerivativePolarization hc htest _ (fun i => im_sub_div_pos hz (hr i))

end RealRooted
