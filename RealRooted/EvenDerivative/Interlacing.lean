module

public import RealRooted.EvenDerivative.Basic
public import RealRooted.HermiteBiehler.Basic
public import RealRooted.PFPolynomial
import RealRooted.EvenDerivative.Preserver
import RealRooted.OperatorInterlacingUpgrade.RootOrder
import RealRooted.ClassicalHurwitzMatrix.Stability.OddEvenConverse
import RealRooted.HermiteBiehler.Forward
import RealRooted.ObreschkoffConverse.Forward
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Even-derivative operators preserve directed interlacing

Let `T_c f = ∑ₖ cₖ xᵏ f^{(2k)}` with `c 0 = 1`, `cₖ ≥ 0`, and suppose the test polynomial `p_N`
is real-rooted.  We show that consecutive monomial images interlace,
`T_c(uᵐ) ≪ T_c(uᵐ⁺¹)` for `m < N`, and deduce from the monomial-chain interlacing upgrade that
`T_c` preserves directed interlacing of nonnegative-coefficient pairs in degrees at most `N`.

The monomial step is a Hermite--Biehler argument.  Folding gives
`T_c(uᴺ)(-z²) = (-1)ᴺ zᴺ p_N(z)` and `p_{m+1}' = (m+1) p_m`; the log-derivative of the real-rooted
`p_{m+1}` has negative imaginary part in the upper half-plane, so `p_{m+1} + i p_m` is
upper-half-plane stable.  Rotating, `T_c(uᵐ⁺¹)(s²) + s T_c(uᵐ)(s²)` is Hurwitz stable, and the
converse odd/even Hermite--Biehler theorem gives the interlacing.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

variable {c : ℕ → ℝ}

/-- Evaluation of the folding identity `T_c(uᴺ)(-z²) = (-1)ᴺ zᴺ p_N(z)` at a complex point. -/
theorem eval_complexify_evenDerivativeOperator_X_pow (N : ℕ) (z : ℂ) :
    (complexify (evenDerivativeOperator c (X ^ N))).eval (-z ^ 2) =
      (-1) ^ N * z ^ N * (complexify (evenDerivativeTest c N)).eval z := by
  have h := congrArg (fun q => (complexify q).eval z) (evenDerivativeOperator_X_pow_comp (c := c) N)
  simp only [complexify, Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_pow,
    Polynomial.map_X, eval_comp, eval_neg, eval_pow, eval_X, Polynomial.map_mul,
    Polynomial.map_C, eval_mul, eval_C] at h
  simpa [complexify] using h

/-- For `c 0 = 1` the test polynomial `p_N` has degree `N`. -/
theorem natDegree_evenDerivativeTest (hc0 : c 0 = 1) (N : ℕ) :
    (evenDerivativeTest c N).natDegree = N := by
  have h := congrArg natDegree (evenDerivativeOperator_X_pow_comp (c := c) N)
  rw [natDegree_comp, natDegree_evenDerivativeOperator hc0, natDegree_X_pow,
    natDegree_mul (by simp) (evenDerivativeTest_ne_zero hc0 N), natDegree_mul (by simp) (by simp),
    natDegree_C, natDegree_X_pow, natDegree_neg, natDegree_X_pow] at h
  lia

/-- The test polynomials satisfy `p_{m+1}' = (m+1) p_m`. -/
theorem derivative_evenDerivativeTest (m : ℕ) :
    derivative (evenDerivativeTest c (m + 1)) = C ((m + 1 : ℕ) : ℝ) * evenDerivativeTest c m := by
  simpa using iterate_derivative_evenDerivativeTest (c := c) (Nat.le_succ m)

/-- The ratio `p_m / p_{m+1}` has nonpositive imaginary part in the upper half-plane. -/
private theorem im_ratio_evenDerivativeTest_nonpos (hc0 : c 0 = 1) {m : ℕ}
    (hsplit : (evenDerivativeTest c (m + 1)).Splits) {z : ℂ} (hz : 0 < z.im) :
    ((complexify (evenDerivativeTest c m)).eval z /
      (complexify (evenDerivativeTest c (m + 1))).eval z).im ≤ 0 := by
  have hder := congrArg (fun q => (complexify q).eval z) (derivative_evenDerivativeTest (c := c) m)
  simp only [complexify, eval_mul, eval_C, Polynomial.map_mul,
    Polynomial.map_C, Complex.ofRealHom_eq_coe] at hder
  have hlog := logDeriv_complexify_im_neg hsplit (evenDerivativeTest_ne_zero hc0 _)
    (by rw [natDegree_evenDerivativeTest hc0]; lia) hz
  have hne : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have : (complexify (evenDerivativeTest c m)).eval z =
      (1 / ((m + 1 : ℕ) : ℝ) : ℝ) *
        (complexify (evenDerivativeTest c (m + 1))).derivative.eval z := by
    simp only [complexify] at hlog ⊢
    rw [Polynomial.derivative_map, hder]
    push_cast
    field_simp
  rw [this, mul_div_assoc]
  exact im_real_mul_nonpos _ _ (by positivity) hlog.le

/-- **Consecutive monomial images interlace.** If `p_N` is real-rooted and `m < N`, then
`T_c(uᵐ) ≪ T_c(uᵐ⁺¹)`. -/
theorem strictInterl_evenDerivativeOperator_X_pow_succ (hc0 : c 0 = 1) (hc : ∀ k, 0 ≤ c k)
    {m N : ℕ} (hmN : m + 1 ≤ N) (htest : (evenDerivativeTest c N).Splits) :
    StrictInterl (evenDerivativeOperator c (X ^ m)) (evenDerivativeOperator c (X ^ (m + 1))) := by
  have hsplit := splits_evenDerivativeTest_of_le hmN htest
  have ha := evenDerivativeOperator_ne_zero hc0 (pow_ne_zero m (X_ne_zero (R := ℝ)))
  have hb := evenDerivativeOperator_ne_zero hc0 (pow_ne_zero (m + 1) (X_ne_zero (R := ℝ)))
  apply strictInterl_of_isHurwitzStable_oddEvenPolynomial ha hb
  refine ⟨hasNonnegCoeffs_oddEvenPolynomial
    (HasNonnegCoeffs.evenDerivativeOperator hc (hasNonnegCoeffs_X.pow m))
    (HasNonnegCoeffs.evenDerivativeOperator hc (hasNonnegCoeffs_X.pow (m + 1))), ?_⟩
  intro s hs hzero
  rw [eval_complexify_oddEvenPolynomial] at hzero
  set z : ℂ := Complex.I * s with hzdef
  have hs2 : s ^ 2 = -z ^ 2 := by rw [hzdef]; ring_nf; simp
  have hsz : s = -Complex.I * z := by rw [hzdef]; ring_nf; simp
  have him : 0 < z.im := by simpa [hzdef] using hs
  have hz0 : z ≠ 0 := fun h => by simp [h] at him
  rw [hs2, eval_complexify_evenDerivativeOperator_X_pow,
    eval_complexify_evenDerivativeOperator_X_pow, hsz] at hzero
  have hstab := stable_of_im_ratio_nonpos (evenDerivativeTest_ne_zero hc0 (m + 1)) hsplit
    (fun w hw => im_ratio_evenDerivativeTest_nonpos hc0 hsplit hw) z him
  rw [eval_hermiteBiehlerPolynomial] at hstab
  apply hstab
  have hfac : (-1) ^ (m + 1) * z ^ (m + 1) *
      ((complexify (evenDerivativeTest c (m + 1))).eval z +
        Complex.I * (complexify (evenDerivativeTest c m)).eval z) = 0 := by
    rw [← hzero]; ring
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd h (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hz0))
  · exact h

/-- **Interlacing preservation.**  If `p_N` is real-rooted, `T_c` maps an oriented interlacing
pair `f ≪ g` of nonnegative-coefficient polynomials with `deg g ≤ N` to an oriented interlacing
pair. -/
theorem strictInterl_evenDerivativeOperator (hc0 : c 0 = 1) (hc : ∀ k, 0 ≤ c k) {N : ℕ}
    (htest : (evenDerivativeTest c N).Splits) {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g) (hgdeg : g.natDegree ≤ N) :
    StrictInterl (evenDerivativeOperator c f) (evenDerivativeOperator c g) :=
  strictInterl_map_of_monomialChain (T := evenDerivativeLinearMap c) (D := N) hfg hf hg hgdeg
    (fun _ hp => HasNonnegCoeffs.evenDerivativeOperator hc hp)
    (fun _ hp hp0 hd => ⟨evenDerivativeOperator_ne_zero hc0 hp0,
      (isPFPolynomial_evenDerivativeOperator hc0 hc htest hp hd).splits⟩)
    (fun _ hm => strictInterl_evenDerivativeOperator_X_pow_succ hc0 hc hm htest)

/-- `T_c` preserves directed weak interlacing of PF pairs of degree at most `N` whenever the
test polynomial `p_N` is real-rooted. -/
theorem interl_evenDerivativeOperator (hc0 : c 0 = 1) (hc : ∀ k, 0 ≤ c k) {N : ℕ}
    (htest : (evenDerivativeTest c N).Splits) {f g : ℝ[X]} (hf : IsPFPolynomial f)
    (hg : IsPFPolynomial g) (hgdeg : g.natDegree ≤ N) (h : Interl f g) :
    Interl (evenDerivativeOperator c f) (evenDerivativeOperator c g) := by
  rcases h with rfl | rfl | hs
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inr (Or.inr (strictInterl_evenDerivativeOperator hc0 hc htest hs hf.hasNonnegCoeffs
      hg.hasNonnegCoeffs hgdeg))

/-- **One extra root of either sign.**  If `p_N` is real-rooted, `h` is PF and `deg h < N`, then
`T_c((u + a) h)` is real-rooted for *every* real `a`: the input `(u + a) h` may have one positive
root.  Indeed `T_c h ≪ T_c(u h)`, and `T_c((u + a) h) = a T_c h + T_c(u h)` is a combination of
the interlacing pair. -/
theorem splits_evenDerivativeOperator_X_add_C_mul (hc0 : c 0 = 1) (hc : ∀ k, 0 ≤ c k) {N : ℕ}
    (htest : (evenDerivativeTest c N).Splits) {h : ℝ[X]} (hh : IsPFPolynomial h) (a : ℝ)
    (hdeg : h.natDegree + 1 ≤ N) : (evenDerivativeOperator c ((X + C a) * h)).Splits := by
  rcases eq_or_ne h 0 with rfl | hh0
  · simp
  have hXh : (X * h).natDegree = h.natDegree + 1 := by
    rw [natDegree_mul X_ne_zero hh0, natDegree_X]; ring
  have hint := strictInterl_evenDerivativeOperator hc0 hc htest
    (strictInterl_self_X_mul_of_nonneg hh0 hh.splits hh.hasNonnegCoeffs) hh.hasNonnegCoeffs
    (isPFPolynomial_X.mul hh).hasNonnegCoeffs (hXh ▸ hdeg)
  have hall := allComboRealRooted_of_strictInterl hint a 1
  have hsum : evenDerivativeOperator c ((X + C a) * h) =
      C a * evenDerivativeOperator c h + C 1 * evenDerivativeOperator c (X * h) := by
    have := (evenDerivativeLinearMap c).map_add (X * h) (a • h)
    simp only [evenDerivativeLinearMap_apply, map_smul] at this
    rw [show (X + C a) * h = X * h + a • h by simp [Polynomial.smul_eq_C_mul, add_mul], this,
      Polynomial.smul_eq_C_mul]
    simp [add_comm]
  rwa [hsum]

end RealRooted
