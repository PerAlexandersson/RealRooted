import RealRooted.DerivativeRecurrence.QuadraticLagStrict
import RealRooted.EulerOperator
import RealRooted.FactorialCompression.Basic

/-!
# The common factorial-compression kernel: recurrences and strict interlacing

The common kernel `h_r = commonKernel r` of Zhang (SSRN 7510941) satisfies the three-term
recurrence `h_{r+2} = h_{r+1} + 2 (r + 1) x h_r` and the derivative identity
`h_r = h_{r+1} - 2 / (r + 1) * x h_{r+1}'`.  Eliminating `h_r` gives the derivative-lag
recurrence `h_{r+2} = (1 + 2 (r + 1) x) h_{r+1} - 4 x² h_{r+1}'`, so that the strict-interlacing
backend `derivLag_strictInterl_and_noCommonRoot` shows that `h_{r+1}` and `h_{r+2}` strictly
interlace and have no common root.  Consequently all roots of `h_r` are negative and simple.
-/

open Polynomial

namespace RealRooted.FactorialCompression

private theorem factorial_real_pred (r : ℕ) (hr : 1 ≤ r) :
    (r.factorial : ℝ) = (r : ℝ) * ((r - 1).factorial : ℝ) := by
  have heq : r = (r - 1) + 1 := by lia
  conv_lhs => rw [heq, Nat.factorial_succ]
  push_cast
  congr 1
  exact_mod_cast (show (r - 1) + 1 = r by lia)

private theorem coeff_commonKernel_succ_succ (r k : ℕ) (hr : 1 ≤ r) :
    (commonKernel (r + 1)).coeff (k + 1) = (commonKernel r).coeff (k + 1) +
      (2 * (r : ℝ)) * (commonKernel (r - 1)).coeff k := by
  by_cases hguard : 2 * (k + 1) ≤ r + 1
  · have hprev : 2 * k ≤ r - 1 := by lia
    by_cases hmid : 2 * (k + 1) ≤ r
    · have hd : r + 1 - 2 * (k + 1) = (r - 2 * (k + 1)) + 1 := by lia
      have he : r - 1 - 2 * k = (r - 2 * (k + 1)) + 1 := by lia
      have hrreal : (r : ℝ) = ((r - 2 * (k + 1) : ℕ) : ℝ) + 2 * (k : ℝ) + 2 := by
        exact_mod_cast (show r = (r - 2 * (k + 1)) + 2 * k + 2 by lia)
      rw [coeff_commonKernel, ite_eq_left hguard, coeff_commonKernel, ite_eq_left hmid,
        coeff_commonKernel, ite_eq_left hprev, hd, he]
      simp only [Nat.factorial_succ]
      push_cast
      simp only [factorial_real_pred r hr, hrreal]
      have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
      have hdfac : ((r - 2 * (k + 1)).factorial : ℝ) ≠ 0 := by positivity
      have hkpos : (k : ℝ) + 1 ≠ 0 := by positivity
      have hdpos : ((r - 2 * (k + 1) : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    · have hbound : 2 * (k + 1) = r + 1 := by lia
      have hd : r + 1 - 2 * (k + 1) = 0 := by lia
      have he : r - 1 - 2 * k = 0 := by lia
      have hrreal : (r : ℝ) = 2 * (k : ℝ) + 1 := by
        exact_mod_cast (show r = 2 * k + 1 by lia)
      rw [coeff_commonKernel, ite_eq_left hguard, coeff_commonKernel, ite_eq_right hmid,
        coeff_commonKernel, ite_eq_left hprev, hd, he, Nat.factorial_zero]
      simp only [Nat.factorial_succ]
      push_cast
      simp only [factorial_real_pred r hr, hrreal]
      have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
      have hkpos : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
  · have hmid : ¬ 2 * (k + 1) ≤ r := by lia
    have hprev : ¬ 2 * k ≤ r - 1 := by lia
    simp [coeff_commonKernel, hguard, hmid, hprev]

/-- The three-term recurrence `h_{r+2} = h_{r+1} + 2 (r + 1) x h_r` of the common kernel
(Zhang, SSRN 7510941). -/
theorem commonKernel_add_two (r : ℕ) :
    commonKernel (r + 2) =
      commonKernel (r + 1) + C (2 * ((r : ℝ) + 1)) * X * commonKernel r := by
  ext k
  cases k with
  | zero => simp [mul_assoc]
  | succ k =>
      have h := coeff_commonKernel_succ_succ (r + 1) k (by lia)
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
      rw [mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul]
      exact h

/-- The derivative identity `h_r = h_{r+1} - 2 / (r + 1) * x h_{r+1}'` of the common kernel
(Zhang, SSRN 7510941). -/
theorem commonKernel_eq_sub_derivative (r : ℕ) :
    commonKernel r =
      commonKernel (r + 1) - C (2 / ((r : ℝ) + 1)) * (X * (commonKernel (r + 1)).derivative) := by
  ext k
  rw [coeff_sub, coeff_C_mul]
  change (commonKernel r).coeff k = (commonKernel (r + 1)).coeff k -
    (2 / ((r : ℝ) + 1)) * (theta (commonKernel (r + 1))).coeff k
  rw [coeff_theta]
  have hlower := mul_coeff_commonKernel_succ r k
  have hrne : (r : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  nlinarith [hlower]

/-- The derivative-lag recurrence `h_{r+2} = (1 + 2 (r + 1) x) h_{r+1} - 4 x² h_{r+1}'`. -/
theorem commonKernel_add_two_eq_derivative (r : ℕ) :
    commonKernel (r + 2) =
      (1 + C (2 * ((r : ℝ) + 1)) * X) * commonKernel (r + 1) +
        (-(C 4 * X ^ 2)) * (commonKernel (r + 1)).derivative := by
  have hrne : (r : ℝ) + 1 ≠ 0 := by positivity
  have hC : C (2 * ((r : ℝ) + 1)) * C (2 / ((r : ℝ) + 1)) = C 4 := by
    rw [← C_mul]
    congr 1
    field_simp
    norm_num
  rw [commonKernel_add_two, commonKernel_eq_sub_derivative r]
  linear_combination (-(X ^ 2) * (commonKernel (r + 1)).derivative) * hC

private theorem eval_zero_commonKernel (r : ℕ) : (commonKernel r).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_commonKernel_zero]

/-- All roots of the common kernel are negative. -/
theorem lt_zero_of_isRoot_commonKernel {r : ℕ} {x : ℝ} (hx : (commonKernel r).IsRoot x) :
    x < 0 :=
  derivLag_roots_neg (P := fun _ => commonKernel r)
    (fun _ => hasPosLeadingCoeff_commonKernel r) (fun _ => hasNonnegCoeffs_commonKernel r)
    (fun _ => by rw [eval_zero_commonKernel]; exact one_pos) 0 x hx

private theorem commonKernel_one : commonKernel 1 = 1 := by
  ext k
  cases k with
  | zero => simp
  | succ k => simp [coeff_commonKernel, coeff_one, show ¬ 2 * (k + 1) ≤ 1 by lia]

private theorem strictInterl_commonKernel_one_two :
    StrictInterl (commonKernel 1) (commonKernel 2) := by
  have h1 := commonKernel_one
  have h2 : commonKernel 2 = C (2 : ℝ) * (X - C (-1 / 2 : ℝ)) := by
    ext k
    cases k with
    | zero => norm_num [coeff_commonKernel]
    | succ k =>
        cases k with
        | zero => norm_num [coeff_commonKernel]
        | succ k => simp [coeff_commonKernel, coeff_X, show ¬ 2 * (k + 1 + 1) ≤ 2 by lia]
  have h2roots : (commonKernel 2).roots = {-1 / 2} := by
    rw [h2, roots_C_mul _ (by norm_num), roots_X_sub_C]
  refine ⟨⟨by rw [h1]; exact one_ne_zero, ?_⟩, ⟨commonKernel_ne_zero 2, ?_⟩,
    [], [-1 / 2], by simp, by simp, ?_, ?_, Or.inl ⟨by simp, trivial⟩⟩
  · rw [h1]
    exact Splits.one
  · exact Splits.of_natDegree_eq_one (by simpa using natDegree_commonKernel 2)
  · simp [h1]
  · simp [h2roots]

/-- The common kernels `h_{r+1}` and `h_{r+2}` strictly interlace and have no common root
(Zhang, SSRN 7510941). -/
theorem strictInterl_commonKernel (r : ℕ) :
    StrictInterl (commonKernel (r + 1)) (commonKernel (r + 2)) ∧
      ∀ x : ℝ, (commonKernel (r + 2)).IsRoot x → ¬ (commonKernel (r + 1)).IsRoot x := by
  refine derivLag_strictInterl_and_noCommonRoot
    (P := fun n => commonKernel (n + 1)) (U := fun n => 1 + C (2 * ((n : ℝ) + 2)) * X)
    (V := fun _ => -(C 4 * X ^ 2)) (W := fun _ => 0) ?_ ?_ ?_
    (fun n => hasPosLeadingCoeff_commonKernel (n + 1))
    (fun _ _ hx => lt_zero_of_isRoot_commonKernel hx) ?_
    (fun _ _ _ => by simp) strictInterl_commonKernel_one_two ?_ r
  · intro n
    have h := commonKernel_add_two_eq_derivative (n + 1)
    simp only [Nat.cast_add, Nat.cast_one] at h
    simpa [add_assoc, one_add_one_eq_two] using h
  · intro n
    simp only [natDegree_commonKernel]
    lia
  · intro n
    simp only [natDegree_commonKernel]
    lia
  · intro n x hx
    have hx2 : 0 < x ^ 2 := by nlinarith
    simp only [eval_neg, eval_mul, eval_C, eval_pow, eval_X]
    linarith
  · intro x _ hx1
    rw [commonKernel_one] at hx1
    simp at hx1

/-- The common kernel `h_r` has real roots, for `r ≥ 2`. -/
theorem splits_commonKernel {r : ℕ} (hr : 2 ≤ r) : (commonKernel r).Splits := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by lia⟩
  exact (strictInterl_commonKernel s).1.2.1.2

/-- The common kernel `h_r` has only simple roots, for `r ≥ 2`. -/
theorem hasSimpleRoots_commonKernel {r : ℕ} (hr : 2 ≤ r) : HasSimpleRoots (commonKernel r) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by lia⟩
  have h := strictInterl_commonKernel s
  exact (h.1.hasSimpleRoots_of_no_common_root fun x hx => h.2 x hx.2 hx.1).2

end RealRooted.FactorialCompression
