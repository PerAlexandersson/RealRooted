module

public import RealRooted.EulerianTriangles.LagTwoRecurrence

/-!
# Positive lag-two Eulerian triangles

This module defines the triangle through its row polynomials, recovers the
coefficient recurrence, and then defines the finite row polynomial directly
from the triangle.  The latter is identified with the recursive polynomial
and therefore inherits the general interlacing theorem.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Recursive polynomial rows for the positive lag-two Eulerian triangle. -/
def lagTwoEulerPolynomial (m : ℝ) (lambda : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      lagTwoEulerStep (n + 1) 1 m (lagTwoEulerPolynomial m lambda (n + 1)) +
        C (m * lambda (n + 2)) * X *
          lagTwoEulerCore n (lagTwoEulerPolynomial m lambda n)

/-- The coefficient triangle attached to `lagTwoEulerPolynomial`. -/
def lagTwoEulerTriangle (m : ℝ) (lambda : ℕ → ℝ) (n k : ℕ) : ℝ :=
  (lagTwoEulerPolynomial m lambda n).coeff k

/-- The finite row polynomial defined directly from the triangle entries. -/
def lagTwoEulerRow (m : ℝ) (lambda : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (lagTwoEulerTriangle m lambda n k) * X ^ k

@[simp] theorem lagTwoEulerPolynomial_zero (m : ℝ) (lambda : ℕ → ℝ) :
    lagTwoEulerPolynomial m lambda 0 = 1 := rfl

@[simp] theorem lagTwoEulerPolynomial_one (m : ℝ) (lambda : ℕ → ℝ) :
    lagTwoEulerPolynomial m lambda 1 = 1 + X := rfl

theorem lagTwoEulerPolynomial_succ_succ (m : ℝ) (lambda : ℕ → ℝ) (n : ℕ) :
    lagTwoEulerPolynomial m lambda (n + 2) =
      lagTwoEulerStep (n + 1) 1 m (lagTwoEulerPolynomial m lambda (n + 1)) +
        C (m * lambda (n + 2)) * X *
          lagTwoEulerCore n (lagTwoEulerPolynomial m lambda n) :=
  rfl

/-- The triangle satisfies the stated lag-two coefficient recurrence. -/
theorem lagTwoEulerTriangle_succ_succ
    (m : ℝ) (lambda : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n + 1) :
    lagTwoEulerTriangle m lambda (n + 2) (k + 1) =
      (m * ((n + 1 - k : ℕ) : ℝ) + 1) *
          lagTwoEulerTriangle m lambda (n + 1) k +
        (m * ((k + 1 : ℕ) : ℝ) + 1) *
          lagTwoEulerTriangle m lambda (n + 1) (k + 1) +
        lambda (n + 2) * m * ((k + 1 : ℕ) : ℝ) *
          ((n + 1 - k : ℕ) : ℝ) * lagTwoEulerTriangle m lambda n k := by
  rw [lagTwoEulerTriangle, lagTwoEulerPolynomial_succ_succ, coeff_add,
    coeff_lagTwoEulerStep_succ]
  have hlag : C (m * lambda (n + 2)) * X *
      lagTwoEulerCore n (lagTwoEulerPolynomial m lambda n) =
        C (m * lambda (n + 2)) *
          (X * lagTwoEulerCore n (lagTwoEulerPolynomial m lambda n)) := by ring
  rw [hlag, coeff_C_mul, coeff_X_mul, coeff_lagTwoEulerCore]
  simp only [lagTwoEulerTriangle]
  push_cast
  have hcast : ((n + 1 - k : ℕ) : ℝ) = (n : ℝ) + 1 - k := by
    rw [Nat.cast_sub hk]
    push_cast
    ring
  rw [hcast]
  ring

/-- The general recurrence certificate specialized to the triangle. -/
theorem lagTwoEulerPolynomial_certificate
    {m : ℝ} {lambda : ℕ → ℝ} (hm : 1 ≤ m)
    (hlambda : ∀ n, 0 ≤ lambda n) (n : ℕ) :
    LagTwoEulerPairCertificate (lagTwoEulerPolynomial m lambda) n := by
  apply lagTwoEuler_recurrence_certificate
    (lagTwoEulerPolynomial m lambda) (fun _ ↦ 1) (fun _ ↦ m)
      (fun j ↦ m * lambda j) 1 1 1
  · norm_num
  · norm_num
  · norm_num
  · rfl
  · simp [lagTwoEulerPolynomial]
  · intro k
    norm_num
  · intro k
    simpa using hm
  · intro k
    exact mul_nonneg (by linarith) (hlambda (k + 2))
  · exact lagTwoEulerPolynomial_succ_succ m lambda

/-- The finite sum of triangle entries is the recursive row polynomial. -/
theorem lagTwoEulerRow_eq
    {m : ℝ} {lambda : ℕ → ℝ} (hm : 1 ≤ m)
    (hlambda : ∀ n, 0 ≤ lambda n) (n : ℕ) :
    lagTwoEulerRow m lambda n = lagTwoEulerPolynomial m lambda n := by
  apply Polynomial.ext
  intro k
  rw [lagTwoEulerRow]
  by_cases hk : k < n + 1
  · simp [hk, lagTwoEulerTriangle]
  · have hkn : n < k := by lia
    have hzero : (lagTwoEulerPolynomial m lambda n).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by
        rw [(lagTwoEulerPolynomial_certificate hm hlambda n).current.natDegree_eq]
        exact hkn)
    simp [hk, hzero]

/-- Theta-form recurrence for the row polynomials defined from the triangle. -/
theorem lagTwoEulerRow_theta_recurrence
    {m : ℝ} {lambda : ℕ → ℝ} (hm : 1 ≤ m)
    (hlambda : ∀ n, 0 ≤ lambda n) (n : ℕ) :
    lagTwoEulerRow m lambda (n + 2) =
      lagTwoEulerStep (n + 1) 1 m (lagTwoEulerRow m lambda (n + 1)) +
        C (m * lambda (n + 2)) * X * lagTwoEulerCore n (lagTwoEulerRow m lambda n) := by
  rw [lagTwoEulerRow_eq hm hlambda, lagTwoEulerRow_eq hm hlambda,
    lagTwoEulerRow_eq hm hlambda]
  exact lagTwoEulerPolynomial_succ_succ m lambda n

/-- Every triangle row has simple negative roots and consecutive rows strictly
interlace. -/
theorem lagTwoEulerRow_simpleNegRooted_and_strictInterl
    {m : ℝ} {lambda : ℕ → ℝ} (hm : 1 ≤ m)
    (hlambda : ∀ n, 0 ≤ lambda n) (n : ℕ) :
    SimpleNegRooted (lagTwoEulerRow m lambda n) n ∧
      StrictInterl (lagTwoEulerRow m lambda n) (lagTwoEulerRow m lambda (n + 1)) ∧
      StrictInterl (lagTwoEulerCore n (lagTwoEulerRow m lambda n))
        (lagTwoEulerRow m lambda (n + 1)) := by
  have h := lagTwoEulerPolynomial_certificate hm hlambda n
  simpa [lagTwoEulerRow_eq hm hlambda] using
    (show SimpleNegRooted (lagTwoEulerPolynomial m lambda n) n ∧
      StrictInterl (lagTwoEulerPolynomial m lambda n)
        (lagTwoEulerPolynomial m lambda (n + 1)) ∧
      StrictInterl (lagTwoEulerCore n (lagTwoEulerPolynomial m lambda n))
        (lagTwoEulerPolynomial m lambda (n + 1)) from
      ⟨h.current, h.adjacent, h.auxiliary⟩)

/-- The constant-lag family, including the A157147--A157151 shape at
`lambda = 1`. -/
abbrev constantLagTwoEulerRow (m lambda : ℝ) (n : ℕ) : ℝ[X] :=
  lagTwoEulerRow m (fun _ ↦ lambda) n

/-- The `lambda = 1` shape represented by A157147--A157151. -/
abbrev unitLagTwoEulerRow (m : ℝ) (n : ℕ) : ℝ[X] :=
  constantLagTwoEulerRow m 1 n

/-- The A157637 specialization `lambda_n = n / 2`. -/
abbrev halfIndexLagTwoEulerRow (m : ℝ) (n : ℕ) : ℝ[X] :=
  lagTwoEulerRow m (fun j ↦ (j : ℝ) / 2) n

theorem constantLagTwoEulerRow_simpleNegRooted_and_strictInterl
    {m lambda : ℝ} (hm : 1 ≤ m) (hlambda : 0 ≤ lambda) (n : ℕ) :
    SimpleNegRooted (constantLagTwoEulerRow m lambda n) n ∧
      StrictInterl (constantLagTwoEulerRow m lambda n)
        (constantLagTwoEulerRow m lambda (n + 1)) := by
  have h := lagTwoEulerRow_simpleNegRooted_and_strictInterl hm (fun _ ↦ hlambda) n
  exact ⟨h.1, h.2.1⟩

theorem unitLagTwoEulerRow_simpleNegRooted_and_strictInterl
    {m : ℝ} (hm : 1 ≤ m) (n : ℕ) :
    SimpleNegRooted (unitLagTwoEulerRow m n) n ∧
      StrictInterl (unitLagTwoEulerRow m n) (unitLagTwoEulerRow m (n + 1)) := by
  exact constantLagTwoEulerRow_simpleNegRooted_and_strictInterl hm (by norm_num) n

theorem halfIndexLagTwoEulerRow_simpleNegRooted_and_strictInterl
    {m : ℝ} (hm : 1 ≤ m) (n : ℕ) :
    SimpleNegRooted (halfIndexLagTwoEulerRow m n) n ∧
      StrictInterl (halfIndexLagTwoEulerRow m n) (halfIndexLagTwoEulerRow m (n + 1)) := by
  have hnonneg : ∀ j : ℕ, 0 ≤ (j : ℝ) / 2 := by intro j; positivity
  have h := lagTwoEulerRow_simpleNegRooted_and_strictInterl hm hnonneg n
  exact ⟨h.1, h.2.1⟩

end RealRooted
