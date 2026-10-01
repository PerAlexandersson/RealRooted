import RealRooted.BalancedRunTransformation
import RealRooted.BinaryRunTransformation.Coefficients
import RealRooted.EulerOperator

/-!
# Kernel identities between the binary-run and balanced run transforms

For the binary-run kernel `J_{n,m}` and the balanced kernel `U_{n,m}`, with
`N = n + 1` and `1 ≤ m ≤ n`, this file proves the three basis identities

* `m J_{n,m} + (1 - X) J_{n,m}' = m U_{n,m-1}`,
* `(N - 2m) J_{n,m} = (N - m) U_{n,m} - m U_{n,m-1}`,
* `N J_{n+1,m} = (N - m) J_{n,m} + m X U_{n,m-1}`.

They drive the cross-length comparison of `J_n` and `J_{n+1}`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Real form of `Nat.choose_succ_right_eq`, valid without an order
hypothesis. -/
private theorem cast_succ_mul_choose_succ (a k : ℕ) :
    ((k : ℝ) + 1) * (a.choose (k + 1) : ℝ) = ((a : ℝ) - k) * (a.choose k : ℝ) := by
  rcases le_or_gt k a with h | h
  · have hnat := congrArg (Nat.cast (R := ℝ)) (Nat.choose_succ_right_eq a k)
    push_cast [Nat.cast_sub h] at hnat
    linarith
  · simp [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by lia : a < k + 1)]

/-- The ratio of consecutive normalizers of the binary-run kernel. -/
private theorem cast_choose_succ_mul (n m : ℕ) :
    (n.choose (m + 1) : ℝ) * ((m : ℝ) + 1) =
      (n.choose m : ℝ) * ((n - m : ℕ) : ℝ) := by
  have hnat := congrArg (Nat.cast (R := ℝ)) (Nat.choose_succ_right_eq n m)
  push_cast at hnat
  exact hnat

private theorem coeff_binaryRunPolynomial_succ (n m k : ℕ) :
    (binaryRunPolynomial n (m + 1)).coeff (k + 1) =
      (m.choose k : ℝ) * ((n - m).choose (k + 1) : ℝ) /
        (n.choose (m + 1) : ℝ) := by
  rw [coeff_binaryRunPolynomial_of_pos_formula n (m + 1) (k + 1) (by lia) (by lia)]
  simp

/-- Derivative identity `m J_{n,m} + (1 - X) J_{n,m}' = m U_{n,m-1}`, written
with `m = j + 1`. -/
theorem binaryRunPolynomial_derivative_identity (n j : ℕ) (hj : j < n) :
    C ((j : ℝ) + 1) * binaryRunPolynomial n (j + 1) +
        (1 - X) * derivative (binaryRunPolynomial n (j + 1)) =
      C ((j : ℝ) + 1) * balancedRunPolynomial n j := by
  have hc0 : (n.choose j : ℝ) ≠ 0 := Nat.cast_choose_ne_zero hj.le
  have hc1 : (n.choose (j + 1) : ℝ) ≠ 0 := Nat.cast_choose_ne_zero hj
  have hrat := cast_choose_succ_mul n j
  ext k
  rw [sub_mul, one_mul, coeff_add, coeff_sub, coeff_C_mul, coeff_C_mul,
    coeff_balancedRunPolynomial n j k hj.le]
  cases k with
  | zero =>
      rw [coeff_derivative, coeff_zero_binaryRunPolynomial_of_pos n _ (by lia),
        Polynomial.coeff_X_mul_zero, coeff_binaryRunPolynomial_succ]
      field_simp
      simp
      linear_combination -hrat
  | succ k =>
      rw [coeff_derivative, Polynomial.coeff_X_mul, coeff_derivative,
        coeff_binaryRunPolynomial_succ, coeff_binaryRunPolynomial_succ]
      have h2 := cast_succ_mul_choose_succ j k
      have h3 := cast_succ_mul_choose_succ (n - j) (k + 1)
      field_simp
      push_cast at h2 h3 ⊢
      linear_combination
        -((n.choose j : ℝ) * ((n - j).choose (k + 1) : ℝ)) * h2 +
          (n.choose j : ℝ) * (j.choose (k + 1) : ℝ) * h3 -
          ((n - j).choose (k + 1) : ℝ) * (j.choose (k + 1) : ℝ) * hrat

/-- Derivative-free identity `(N - 2m) J_{n,m} = (N - m) U_{n,m} - m U_{n,m-1}`,
written with `N = n + 1` and `m = j + 1`. -/
theorem binaryRunPolynomial_balanced_identity (n j : ℕ) (hj : j < n) :
    C ((n : ℝ) - 2 * j - 1) * binaryRunPolynomial n (j + 1) =
      C ((n : ℝ) - j) * balancedRunPolynomial n (j + 1) -
        C ((j : ℝ) + 1) * balancedRunPolynomial n j := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_lt hj
  have hc0 : ((j + b + 1).choose j : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (by lia)
  have hc1 : ((j + b + 1).choose (j + 1) : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (by lia)
  have hrat := cast_choose_succ_mul (j + b + 1) j
  have ha : j + b + 1 - j = b + 1 := by lia
  have ha' : j + b + 1 - (j + 1) = b := by lia
  rw [ha] at hrat
  ext k
  rw [coeff_sub, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    coeff_balancedRunPolynomial _ _ k (by lia),
    coeff_balancedRunPolynomial _ _ k (by lia), ha, ha']
  cases k with
  | zero =>
      rw [coeff_zero_binaryRunPolynomial_of_pos _ _ (by lia)]
      field_simp
      push_cast at hrat ⊢
      simp only [Nat.choose_zero_right, Nat.cast_one, mul_one]
      linear_combination hrat
  | succ t =>
      rw [coeff_binaryRunPolynomial_succ, ha]
      have f1 : ((j + 1).choose (t + 1) : ℝ) =
          (j.choose t : ℝ) + (j.choose (t + 1) : ℝ) := by
        exact_mod_cast Nat.choose_succ_succ' j t
      have f2 : ((b + 1).choose (t + 1) : ℝ) =
          (b.choose t : ℝ) + (b.choose (t + 1) : ℝ) := by
        exact_mod_cast Nat.choose_succ_succ' b t
      have f4 : ((t : ℝ) + 1) * ((b + 1).choose (t + 1) : ℝ) =
          ((b : ℝ) + 1) * (b.choose t : ℝ) := by
        have := congrArg (Nat.cast (R := ℝ)) (Nat.add_one_mul_choose_eq b t)
        push_cast at this
        linarith
      have f5 := cast_succ_mul_choose_succ j t
      field_simp
      push_cast at hrat ⊢
      linear_combination
        ((j + b + 1).choose j : ℝ) *
            (-((b : ℝ) + 1) * (b.choose (t + 1) : ℝ) * f1 - (j.choose t : ℝ) * f4 +
              ((b : ℝ) + 1) * (j.choose t : ℝ) * f2 + ((b + 1).choose (t + 1) : ℝ) * f5 -
              (j.choose (t + 1) : ℝ) * f4 + ((b : ℝ) + 1) * (j.choose (t + 1) : ℝ) * f2) +
          (j.choose (t + 1) : ℝ) * ((b + 1).choose (t + 1) : ℝ) * hrat

/-- Derivative-free cross-length identity
`N J_{n+1,m} = (N - m) J_{n,m} + m X U_{n,m-1}`, written with `N = n + 1` and
`m = j + 1`. -/
theorem binaryRunPolynomial_succ_length_identity (n j : ℕ) (hj : j < n) :
    C ((n : ℝ) + 1) * binaryRunPolynomial (n + 1) (j + 1) =
      C ((n : ℝ) - j) * binaryRunPolynomial n (j + 1) +
        C ((j : ℝ) + 1) * (X * balancedRunPolynomial n j) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_lt hj
  have hc0 : ((j + b + 1).choose j : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (by lia)
  have hc1 : ((j + b + 1).choose (j + 1) : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (by lia)
  have hd : ((j + b + 1 + 1).choose (j + 1) : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (by lia)
  have hrat := cast_choose_succ_mul (j + b + 1) j
  have ha : j + b + 1 - j = b + 1 := by lia
  have ha2 : j + b + 1 + 1 - j = b + 2 := by lia
  rw [ha] at hrat
  have g1 : ((j : ℝ) + b + 1 + 1) * ((j + b + 1).choose j : ℝ) =
      ((j + b + 1 + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) := by
    have := congrArg (Nat.cast (R := ℝ)) (Nat.add_one_mul_choose_eq (j + b + 1) j)
    push_cast at this
    linarith
  ext k
  rw [coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul]
  cases k with
  | zero =>
      rw [coeff_zero_binaryRunPolynomial_of_pos _ _ (by lia),
        coeff_zero_binaryRunPolynomial_of_pos _ _ (by lia), Polynomial.coeff_X_mul_zero]
      simp
  | succ t =>
      rw [coeff_binaryRunPolynomial_succ, coeff_binaryRunPolynomial_succ,
        Polynomial.coeff_X_mul, coeff_balancedRunPolynomial _ _ t (by lia), ha, ha2]
      have hp : ((b + 2).choose (t + 1) : ℝ) =
          ((b + 1).choose t : ℝ) + ((b + 1).choose (t + 1) : ℝ) := by
        exact_mod_cast Nat.choose_succ_succ' (b + 1) t
      field_simp
      push_cast at hrat ⊢
      linear_combination
        (j.choose t : ℝ) *
          (((j + b + 1 + 1).choose (j + 1) : ℝ) *
              (((j + b + 1).choose j : ℝ) * ((b : ℝ) + 1) * hp +
                (((b + 2).choose (t + 1) : ℝ) - ((b + 1).choose t : ℝ)) * hrat) +
            ((b + 2).choose (t + 1) : ℝ) * ((j + b + 1).choose (j + 1) : ℝ) * g1)

/-! ### Transform-level identities -/

/-- Two real-linear maps agreeing on `X ^ m` for `m ≤ n` agree on every
polynomial of degree at most `n`. -/
private theorem linearMap_eq_of_X_pow {Φ Ψ : ℝ[X] →ₗ[ℝ] ℝ[X]} {n : ℕ}
    (h : ∀ m ≤ n, Φ (X ^ m) = Ψ (X ^ m)) {p : ℝ[X]} (hp : p.natDegree ≤ n) :
    Φ p = Ψ p := by
  rw [p.as_sum_range_C_mul_X_pow]
  simp only [map_sum, ← smul_eq_C_mul, map_smul]
  exact Finset.sum_congr rfl fun m hm => by
    rw [h m ((Finset.mem_range_succ_iff.mp hm).trans hp)]

private def binaryRunLM (n : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := binaryRunTransform n
  map_add' := binaryRunTransform_add n
  map_smul' a p := by
    simpa [Polynomial.smul_eq_C_mul] using binaryRunTransform_smul n a p

private def thetaLM : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  LinearMap.mulLeft ℝ X ∘ₗ derivative

private theorem thetaLM_apply (p : ℝ[X]) : thetaLM p = theta p := rfl

/-- The combination `J_n(Θp) + (1 - X) J_n(p)'` as a linear map. -/
private def edgeLM (n : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  binaryRunLM n ∘ₗ thetaLM +
    LinearMap.mulLeft ℝ (1 - X) ∘ₗ derivative ∘ₗ binaryRunLM n

private theorem edgeLM_apply (n : ℕ) (p : ℝ[X]) :
    edgeLM n p = binaryRunTransform n (theta p) +
      (1 - X) * derivative (binaryRunTransform n p) := rfl

private theorem theta_X_pow (m : ℕ) : theta (X ^ m : ℝ[X]) = C (m : ℝ) * X ^ m := by
  cases m with
  | zero => simp [theta]
  | succ j =>
      rw [theta, derivative_X_pow]
      simp only [Nat.add_sub_cancel]
      rw [← mul_assoc, mul_comm X, mul_assoc, ← pow_succ']

/-- The balanced kernel of the derivative is the binary-run edge combination:
`K_n(p') = J_n(Θp) + (1 - X) J_n(p)'`. -/
theorem balancedRunTransform_derivative_eq {n : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ n) :
    balancedRunTransform n (derivative p) =
      binaryRunTransform n (theta p) +
        (1 - X) * derivative (binaryRunTransform n p) := by
  rw [← edgeLM_apply]
  change (balancedRunTransformLinearMap n ∘ₗ derivative) p = edgeLM n p
  refine linearMap_eq_of_X_pow (fun m hm => ?_) hp
  simp only [LinearMap.comp_apply, edgeLM_apply]
  rcases m with _ | j
  · simp [theta]
  · rw [derivative_X_pow, theta_X_pow]
    simp only [Nat.add_sub_cancel, balancedRunTransformLinearMap_apply]
    rw [← smul_eq_C_mul, ← smul_eq_C_mul, balancedRunTransform_smul,
      binaryRunTransform_smul]
    simp only [balancedRunTransform_X_pow, binaryRunTransform_X_pow,
      smul_eq_C_mul, Nat.cast_add, Nat.cast_one]
    exact (binaryRunPolynomial_derivative_identity n j (by lia)).symm

private theorem polarTheta_X_pow (N m : ℕ) :
    polarTheta N (X ^ m : ℝ[X]) = C ((N : ℝ) - m) * X ^ m := by
  rw [polarTheta, theta_X_pow, C_sub, sub_mul]

private def polarLM (N : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := polarTheta N
  map_add' p q := by
    simp only [polarTheta, theta, derivative_add]
    ring
  map_smul' a p := by
    simp only [polarTheta, theta, smul_eq_C_mul, derivative_C_mul, RingHom.id_apply]
    ring

private theorem balancedRunTransform_C_mul_X_pow (n m : ℕ) (a : ℝ) :
    balancedRunTransform n (C a * X ^ m) = C a * balancedRunPolynomial n m := by
  rw [← smul_eq_C_mul, balancedRunTransform_smul, balancedRunTransform_X_pow,
    smul_eq_C_mul]

private theorem binaryRunTransform_C_mul_X_pow (n m : ℕ) (a : ℝ) :
    binaryRunTransform n (C a * X ^ m) = C a * binaryRunPolynomial n m := by
  rw [← smul_eq_C_mul, binaryRunTransform_smul, binaryRunTransform_X_pow]

private theorem derivative_X_pow_succ (j : ℕ) :
    derivative (X ^ (j + 1) : ℝ[X]) = C ((j : ℝ) + 1) * X ^ j := by
  rw [derivative_X_pow, Nat.add_sub_cancel]
  push_cast
  rfl

/-- The balanced kernel of the polar derivative:
`K_n((N - Θ)p) = J_n((N - Θ)p) - J_n(Θp) + K_n(p')` with `N = n + 1`. -/
theorem balancedRunTransform_polarTheta_eq {n : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ n) :
    balancedRunTransform n (polarTheta (n + 1) p) =
      binaryRunTransform n (polarTheta (n + 1) p) -
        binaryRunTransform n (theta p) +
          balancedRunTransform n (derivative p) := by
  refine linearMap_eq_of_X_pow
    (Φ := balancedRunTransformLinearMap n ∘ₗ polarLM (n + 1))
    (Ψ := binaryRunLM n ∘ₗ polarLM (n + 1) - binaryRunLM n ∘ₗ thetaLM +
      balancedRunTransformLinearMap n ∘ₗ derivative) (fun m hm => ?_) hp
  change balancedRunTransform n (polarTheta (n + 1) (X ^ m)) =
    binaryRunTransform n (polarTheta (n + 1) (X ^ m)) -
      binaryRunTransform n (theta (X ^ m)) +
        balancedRunTransform n (derivative (X ^ m))
  rw [polarTheta_X_pow, theta_X_pow, balancedRunTransform_C_mul_X_pow,
    binaryRunTransform_C_mul_X_pow, binaryRunTransform_C_mul_X_pow]
  rcases m with _ | j
  · simp
  · rw [derivative_X_pow_succ, balancedRunTransform_C_mul_X_pow]
    have hii := binaryRunPolynomial_balanced_identity n j (by lia)
    push_cast
    simp only [map_sub, map_add, map_one, map_natCast, map_mul, map_ofNat] at hii ⊢
    linear_combination (-1 : ℝ[X]) * hii

/-- Cross-length identity `N J_{n+1}(p) = J_n((N - Θ)p) + X K_n(p')` with
`N = n + 1`. -/
theorem binaryRunTransform_succ_eq {n : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ n) :
    C ((n : ℝ) + 1) * binaryRunTransform (n + 1) p =
      binaryRunTransform n (polarTheta (n + 1) p) +
        X * balancedRunTransform n (derivative p) := by
  refine linearMap_eq_of_X_pow
    (Φ := LinearMap.mulLeft ℝ (C ((n : ℝ) + 1)) ∘ₗ binaryRunLM (n + 1))
    (Ψ := binaryRunLM n ∘ₗ polarLM (n + 1) +
      LinearMap.mulLeft ℝ X ∘ₗ balancedRunTransformLinearMap n ∘ₗ derivative)
    (fun m hm => ?_) hp
  change C ((n : ℝ) + 1) * binaryRunTransform (n + 1) (X ^ m) =
    binaryRunTransform n (polarTheta (n + 1) (X ^ m)) +
      X * balancedRunTransform n (derivative (X ^ m))
  rw [polarTheta_X_pow, binaryRunTransform_C_mul_X_pow, binaryRunTransform_X_pow]
  rcases m with _ | j
  · simp
  · rw [derivative_X_pow_succ, balancedRunTransform_C_mul_X_pow]
    have hiii := binaryRunPolynomial_succ_length_identity n j (by lia)
    push_cast
    simp only [map_sub, map_add, map_one, map_natCast] at hiii ⊢
    linear_combination hiii

end RealRooted
