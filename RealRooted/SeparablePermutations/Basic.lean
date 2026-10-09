import RealRooted.DerivativeRecurrence.QuadraticLagStrict
import RealRooted.Linear

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

open Polynomial

noncomputable section

namespace RealRooted.SeparablePermutations

/-- Zhang's auxiliary polynomials: `B_0 = 1` and
`B_{N+1} = (X + (N + 2) / 2) B_N + X B_N'` (SSRN 7510941, (3.4)). -/
def auxPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | N + 1 => (X + C (((N : ℝ) + 2) / 2)) * auxPolynomial N + X * (auxPolynomial N).derivative

@[simp] theorem auxPolynomial_zero : auxPolynomial 0 = 1 := rfl

theorem auxPolynomial_succ (N : ℕ) :
    auxPolynomial (N + 1) =
      (X + C (((N : ℝ) + 2) / 2)) * auxPolynomial N + X * (auxPolynomial N).derivative := rfl

@[simp] theorem auxPolynomial_one : auxPolynomial 1 = X + 1 := by
  simp [auxPolynomial_succ]

private theorem coeff_auxPolynomial_succ_zero (N : ℕ) :
    (auxPolynomial (N + 1)).coeff 0 = (((N : ℝ) + 2) / 2) * (auxPolynomial N).coeff 0 := by
  simp [auxPolynomial_succ, add_mul]

private theorem coeff_auxPolynomial_succ_succ (N k : ℕ) :
    (auxPolynomial (N + 1)).coeff (k + 1) =
      (auxPolynomial N).coeff k +
        (((N : ℝ) + 2) / 2 + ((k : ℝ) + 1)) * (auxPolynomial N).coeff (k + 1) := by
  simp only [auxPolynomial_succ, add_mul, coeff_add, coeff_X_mul, coeff_C_mul, coeff_derivative]
  ring

private theorem natDegree_le_and_coeff_auxPolynomial (N : ℕ) :
    (auxPolynomial N).natDegree ≤ N ∧ (auxPolynomial N).coeff N = 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    obtain ⟨hle, hcoeff⟩ := ih
    have hzero : ∀ k, N < k → (auxPolynomial N).coeff k = 0 := fun k hk =>
      coeff_eq_zero_of_natDegree_lt (by lia)
    refine ⟨natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_, ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
      rw [coeff_auxPolynomial_succ_succ, hzero j (by lia), hzero (j + 1) (by lia)]
      simp
    · rw [coeff_auxPolynomial_succ_succ, hcoeff, hzero (N + 1) (by lia)]
      simp

/-- `B_N` has degree `N`. -/
theorem natDegree_auxPolynomial (N : ℕ) : (auxPolynomial N).natDegree = N :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_and_coeff_auxPolynomial N).1
    (by rw [(natDegree_le_and_coeff_auxPolynomial N).2]; exact one_ne_zero)

/-- `B_N` is monic. -/
theorem monic_auxPolynomial (N : ℕ) : (auxPolynomial N).Monic := by
  rw [Monic, leadingCoeff, natDegree_auxPolynomial]
  exact (natDegree_le_and_coeff_auxPolynomial N).2

/-- All coefficients of `B_N` are nonnegative. -/
theorem hasNonnegCoeffs_auxPolynomial (N : ℕ) :
    RealRooted.HasNonnegCoeffs (auxPolynomial N) := by
  induction N with
  | zero =>
    intro k
    rw [auxPolynomial_zero, coeff_one]
    split_ifs <;> norm_num
  | succ N ih =>
    intro k
    cases k with
    | zero =>
      rw [coeff_auxPolynomial_succ_zero]
      have := ih 0
      positivity
    | succ k =>
      rw [coeff_auxPolynomial_succ_succ]
      have h1 := ih k
      have h2 := ih (k + 1)
      positivity

/-- The constant term of `B_N` is positive. -/
theorem coeff_zero_auxPolynomial_pos (N : ℕ) : 0 < (auxPolynomial N).coeff 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [coeff_auxPolynomial_succ_zero]
    positivity

/-- The coefficients `0, …, N` of `B_N` are positive. -/
theorem coeff_auxPolynomial_pos {N k : ℕ} (hk : k ≤ N) : 0 < (auxPolynomial N).coeff k := by
  induction N generalizing k with
  | zero =>
    obtain rfl : k = 0 := by lia
    exact coeff_zero_auxPolynomial_pos 0
  | succ N ih =>
    cases k with
    | zero => exact coeff_zero_auxPolynomial_pos _
    | succ k =>
      rw [coeff_auxPolynomial_succ_succ]
      have h1 := ih (k := k) (by lia)
      have h2 := hasNonnegCoeffs_auxPolynomial N (k + 1)
      positivity

/-- `B_N` has a positive leading coefficient. -/
theorem hasPosLeadingCoeff_auxPolynomial (N : ℕ) :
    RealRooted.HasPosLeadingCoeff (auxPolynomial N) := by
  unfold RealRooted.HasPosLeadingCoeff
  rw [(monic_auxPolynomial N).leadingCoeff]
  exact one_pos

private theorem isRoot_auxPolynomial_neg {N : ℕ} {r : ℝ} (hr : (auxPolynomial N).IsRoot r) :
    r < 0 := by
  have hne : auxPolynomial N ≠ 0 := (monic_auxPolynomial N).ne_zero
  refine lt_of_le_of_ne
    (RealRooted.isRoot_nonpos_of_hasNonnegCoeffs (hasNonnegCoeffs_auxPolynomial N) hne hr) ?_
  rintro rfl
  have h0 := coeff_zero_auxPolynomial_pos N
  rw [coeff_zero_eq_eval_zero] at h0
  exact h0.ne' hr

/-- All real roots of `B_N` are negative. -/
theorem roots_auxPolynomial_neg (N : ℕ) : ∀ r ∈ (auxPolynomial N).roots, r < 0 := fun _ hr =>
  isRoot_auxPolynomial_neg ((mem_roots (monic_auxPolynomial N).ne_zero).mp hr)

/-- Consecutive auxiliary polynomials strictly interlace and have no common root. -/
theorem strictInterl_auxPolynomial (N : ℕ) :
    RealRooted.StrictInterl (auxPolynomial N) (auxPolynomial (N + 1)) ∧
      ∀ r : ℝ, ¬ ((auxPolynomial N).IsRoot r ∧ (auxPolynomial (N + 1)).IsRoot r) := by
  have hbase : RealRooted.StrictInterl (auxPolynomial 0) (auxPolynomial 1) :=
    (RealRooted.interlaces_one_linear (p := auxPolynomial 1)
      (by rw [natDegree_auxPolynomial])).toStrictInterl
  have key := RealRooted.derivLag_strictInterl_and_noCommonRoot
    (P := auxPolynomial) (U := fun n => X + C (((n : ℝ) + 3) / 2)) (V := fun _ => X)
    (W := fun _ => 0)
    (fun n => by
      rw [auxPolynomial_succ (n + 1)]
      push_cast
      rw [show ((n : ℝ) + 1 + 2) / 2 = ((n : ℝ) + 3) / 2 by ring]
      ring)
    (fun n => Or.inr (by rw [natDegree_auxPolynomial, natDegree_auxPolynomial]))
    (fun n => by rw [natDegree_auxPolynomial]; lia) hasPosLeadingCoeff_auxPolynomial
    (fun n _ hr => isRoot_auxPolynomial_neg hr) (fun n x hx => by simpa using hx)
    (fun n x _ => by simp) hbase (fun r hr hr0 => by simp [auxPolynomial] at hr0) N
  exact ⟨key.1, fun r hr => key.2 r hr.2 hr.1⟩

/-- `B_N` has simple roots. -/
theorem hasSimpleRoots_auxPolynomial (N : ℕ) : RealRooted.HasSimpleRoots (auxPolynomial N) :=
  ((strictInterl_auxPolynomial N).1.hasSimpleRoots_of_no_common_root
    (strictInterl_auxPolynomial N).2).1

end RealRooted.SeparablePermutations
