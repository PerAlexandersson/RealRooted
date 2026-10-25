module

public import RealRooted.DerivativeRecurrence.QuadraticLagStrict
public import RealRooted.Linear

/-!
# The auxiliary polynomials for separable permutations

The polynomials `B_0 = 1`, `B_{N+1} = (X + (N + 2) / 2) B_N + X B_N'` of Zhang
(SSRN 7510941, (3.4)).  They are the input of the factorial compression that
produces the gamma-polynomials of the descent enumerators of separable
permutations.  We prove that `B_N` is monic of degree `N` with positive
coefficients and simple negative roots, and that consecutive polynomials strictly
interlace without common roots.  The interlacing step is an instance of the
strict derivative-lag recurrence `derivLag_strictInterl_and_noCommonRoot` with
multipliers `U n = X + (n + 3) / 2`, `V n = X`, `W n = 0`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.SeparablePermutations

/-- Zhang's auxiliary polynomials: `B_0 = 1` and
`B_{N+1} = (X + (N + 2) / 2) B_N + X B_N'` (SSRN 7510941, (3.4)). -/
def compressionSourcePolynomial : ℕ → ℝ[X]
  | 0 => 1
  | N + 1 =>
      (X + C (((N : ℝ) + 2) / 2)) * compressionSourcePolynomial N +
        X * (compressionSourcePolynomial N).derivative

@[simp] theorem compressionSourcePolynomial_zero : compressionSourcePolynomial 0 = 1 := rfl

theorem compressionSourcePolynomial_succ (N : ℕ) :
    compressionSourcePolynomial (N + 1) =
      (X + C (((N : ℝ) + 2) / 2)) * compressionSourcePolynomial N +
        X * (compressionSourcePolynomial N).derivative := rfl

@[simp] theorem compressionSourcePolynomial_one : compressionSourcePolynomial 1 = X + 1 := by
  simp [compressionSourcePolynomial_succ]

private theorem coeff_compressionSourcePolynomial_succ_zero (N : ℕ) :
    (compressionSourcePolynomial (N + 1)).coeff 0 =
      (((N : ℝ) + 2) / 2) * (compressionSourcePolynomial N).coeff 0 := by
  simp [compressionSourcePolynomial_succ, add_mul]

private theorem coeff_compressionSourcePolynomial_succ_succ (N k : ℕ) :
    (compressionSourcePolynomial (N + 1)).coeff (k + 1) =
      (compressionSourcePolynomial N).coeff k +
        (((N : ℝ) + 2) / 2 + ((k : ℝ) + 1)) *
          (compressionSourcePolynomial N).coeff (k + 1) := by
  simp only [compressionSourcePolynomial_succ, add_mul, coeff_add, coeff_X_mul,
    coeff_C_mul, coeff_derivative]
  ring

private theorem natDegree_le_and_coeff_compressionSourcePolynomial (N : ℕ) :
    (compressionSourcePolynomial N).natDegree ≤ N ∧
      (compressionSourcePolynomial N).coeff N = 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    obtain ⟨hle, hcoeff⟩ := ih
    have hzero : ∀ k, N < k → (compressionSourcePolynomial N).coeff k = 0 := fun k hk =>
      coeff_eq_zero_of_natDegree_lt (by lia)
    refine ⟨natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_, ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
      rw [coeff_compressionSourcePolynomial_succ_succ, hzero j (by lia), hzero (j + 1) (by lia)]
      simp
    · rw [coeff_compressionSourcePolynomial_succ_succ, hcoeff, hzero (N + 1) (by lia)]
      simp

/-- `B_N` has degree `N`. -/
theorem natDegree_compressionSourcePolynomial (N : ℕ) :
    (compressionSourcePolynomial N).natDegree = N :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_and_coeff_compressionSourcePolynomial N).1
    (by rw [(natDegree_le_and_coeff_compressionSourcePolynomial N).2]; exact one_ne_zero)

/-- `B_N` is monic. -/
theorem monic_compressionSourcePolynomial (N : ℕ) : (compressionSourcePolynomial N).Monic := by
  rw [Monic, leadingCoeff, natDegree_compressionSourcePolynomial]
  exact (natDegree_le_and_coeff_compressionSourcePolynomial N).2

/-- All coefficients of `B_N` are nonnegative. -/
theorem hasNonnegCoeffs_compressionSourcePolynomial (N : ℕ) :
    RealRooted.HasNonnegCoeffs (compressionSourcePolynomial N) := by
  induction N with
  | zero =>
    intro k
    rw [compressionSourcePolynomial_zero, coeff_one]
    split_ifs <;> norm_num
  | succ N ih =>
    intro k
    cases k with
    | zero =>
      rw [coeff_compressionSourcePolynomial_succ_zero]
      have := ih 0
      positivity
    | succ k =>
      rw [coeff_compressionSourcePolynomial_succ_succ]
      have h1 := ih k
      have h2 := ih (k + 1)
      positivity

/-- The constant term of `B_N` is positive. -/
theorem coeff_zero_compressionSourcePolynomial_pos (N : ℕ) :
    0 < (compressionSourcePolynomial N).coeff 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [coeff_compressionSourcePolynomial_succ_zero]
    positivity

/-- The coefficients `0, …, N` of `B_N` are positive. -/
theorem coeff_compressionSourcePolynomial_pos {N k : ℕ} (hk : k ≤ N) :
    0 < (compressionSourcePolynomial N).coeff k := by
  induction N generalizing k with
  | zero =>
    obtain rfl : k = 0 := by lia
    exact coeff_zero_compressionSourcePolynomial_pos 0
  | succ N ih =>
    cases k with
    | zero => exact coeff_zero_compressionSourcePolynomial_pos _
    | succ k =>
      rw [coeff_compressionSourcePolynomial_succ_succ]
      have h1 := ih (k := k) (by lia)
      have h2 := hasNonnegCoeffs_compressionSourcePolynomial N (k + 1)
      positivity

/-- `B_N` has a positive leading coefficient. -/
theorem hasPosLeadingCoeff_compressionSourcePolynomial (N : ℕ) :
    RealRooted.HasPosLeadingCoeff (compressionSourcePolynomial N) := by
  unfold RealRooted.HasPosLeadingCoeff
  rw [(monic_compressionSourcePolynomial N).leadingCoeff]
  exact one_pos

private theorem isRoot_compressionSourcePolynomial_neg {N : ℕ} {r : ℝ}
    (hr : (compressionSourcePolynomial N).IsRoot r) :
    r < 0 := by
  have hne : compressionSourcePolynomial N ≠ 0 := (monic_compressionSourcePolynomial N).ne_zero
  refine lt_of_le_of_ne
    (RealRooted.isRoot_nonpos_of_hasNonnegCoeffs
      (hasNonnegCoeffs_compressionSourcePolynomial N) hne hr) ?_
  rintro rfl
  have h0 := coeff_zero_compressionSourcePolynomial_pos N
  rw [coeff_zero_eq_eval_zero] at h0
  exact h0.ne' hr

/-- All real roots of `B_N` are negative. -/
theorem roots_compressionSourcePolynomial_neg (N : ℕ) :
    ∀ r ∈ (compressionSourcePolynomial N).roots, r < 0 := fun _ hr =>
  isRoot_compressionSourcePolynomial_neg
    ((mem_roots (monic_compressionSourcePolynomial N).ne_zero).mp hr)

/-- Consecutive auxiliary polynomials strictly interlace and have no common root. -/
theorem strictInterl_compressionSourcePolynomial (N : ℕ) :
    RealRooted.StrictInterl
        (compressionSourcePolynomial N) (compressionSourcePolynomial (N + 1)) ∧
      ∀ r : ℝ, ¬ ((compressionSourcePolynomial N).IsRoot r ∧
        (compressionSourcePolynomial (N + 1)).IsRoot r) := by
  have hbase : RealRooted.StrictInterl
      (compressionSourcePolynomial 0) (compressionSourcePolynomial 1) :=
    (RealRooted.interlaces_one_linear (p := compressionSourcePolynomial 1)
      (by rw [natDegree_compressionSourcePolynomial])).toStrictInterl
  have key := RealRooted.derivLag_strictInterl_and_noCommonRoot
    (P := compressionSourcePolynomial) (U := fun n => X + C (((n : ℝ) + 3) / 2)) (V := fun _ => X)
    (W := fun _ => 0)
    (fun n => by
      rw [compressionSourcePolynomial_succ (n + 1)]
      push_cast
      rw [show ((n : ℝ) + 1 + 2) / 2 = ((n : ℝ) + 3) / 2 by ring]
      ring)
    (fun n => Or.inr (by
      rw [natDegree_compressionSourcePolynomial, natDegree_compressionSourcePolynomial]))
    (fun n => by rw [natDegree_compressionSourcePolynomial]; lia)
    hasPosLeadingCoeff_compressionSourcePolynomial
    (fun n _ hr => isRoot_compressionSourcePolynomial_neg hr) (fun n x hx => by simpa using hx)
    (fun n x _ => by simp) hbase (fun r hr hr0 => by simp [compressionSourcePolynomial] at hr0) N
  exact ⟨key.1, fun r hr => key.2 r hr.2 hr.1⟩

/-- `B_N` has simple roots. -/
theorem hasSimpleRoots_compressionSourcePolynomial (N : ℕ) :
    RealRooted.HasSimpleRoots (compressionSourcePolynomial N) :=
  ((strictInterl_compressionSourcePolynomial N).1.hasSimpleRoots_of_no_common_root
    (strictInterl_compressionSourcePolynomial N).2).1

end RealRooted.SeparablePermutations
