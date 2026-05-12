import RealRooted.CombinatorialExamples.Common
import RealRooted.MaWang
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace RealRooted

/-- The linear coefficient block in the colored set-partition recurrence. -/
def coloredSetPartitionsCoeffA (c : Nat) : ℝ[X] :=
  X + C (c : ℝ)

/-- The derivative coefficient block in the colored set-partition recurrence. -/
def coloredSetPartitionsCoeffB (m : Nat) : ℝ[X] :=
  C (m : ℝ) * X

/-- The generic colored set-partition family satisfying
`T_{n+1}(X) = (X + c) T_n(X) + m X T'_n(X)` with `T_0(X) = 1`. -/
def coloredSetPartitions (c m : Nat) : Nat → ℝ[X]
  | 0 => 1
  | n + 1 =>
      coloredSetPartitionsCoeffA c * coloredSetPartitions c m n +
        coloredSetPartitionsCoeffB m * (coloredSetPartitions c m n).derivative

@[simp] lemma coloredSetPartitions_zero (c m : Nat) :
    coloredSetPartitions c m 0 = 1 := rfl

lemma coloredSetPartitions_succ (c m n : Nat) :
    coloredSetPartitions c m (n + 1) =
      coloredSetPartitionsCoeffA c * coloredSetPartitions c m n +
        coloredSetPartitionsCoeffB m * (coloredSetPartitions c m n).derivative := rfl

lemma coloredSetPartitions_one (c m : Nat) :
    coloredSetPartitions c m 1 = X + C (c : ℝ) := by
  simp [coloredSetPartitions, coloredSetPartitionsCoeffA, coloredSetPartitionsCoeffB]

lemma coeff_coloredSetPartitionsCoeffA_mul (c k : Nat) (p : ℝ[X]) :
    coeff (coloredSetPartitionsCoeffA c * p) (k + 1) =
      coeff p k + (c : ℝ) * coeff p (k + 1) := by
  rw [coloredSetPartitionsCoeffA, add_mul, coeff_add, coeff_X_mul, coeff_C_mul]

lemma coeff_coloredSetPartitionsCoeffB_mul_derivative (m k : Nat) (p : ℝ[X]) :
    coeff (coloredSetPartitionsCoeffB m * p.derivative) (k + 1) =
      ((m : ℝ) * (k + 1 : ℝ)) * coeff p (k + 1) := by
  calc
    coeff (coloredSetPartitionsCoeffB m * p.derivative) (k + 1)
        = coeff (C (m : ℝ) * (X * p.derivative)) (k + 1) := by
            rw [coloredSetPartitionsCoeffB, mul_assoc]
    _ = (m : ℝ) * coeff (X * p.derivative) (k + 1) := by
          rw [coeff_C_mul]
    _ = (m : ℝ) * coeff p.derivative k := by
          rw [coeff_X_mul]
    _ = (m : ℝ) * ((k + 1 : ℝ) * coeff p (k + 1)) := by
          rw [coeff_derivative]
          ring
    _ = ((m : ℝ) * (k + 1 : ℝ)) * coeff p (k + 1) := by ring

lemma coeff_coloredSetPartitions_succ (c m n k : Nat) :
    coeff (coloredSetPartitions c m (n + 1)) (k + 1) =
      coeff (coloredSetPartitions c m n) k +
        ((c : ℝ) + (m : ℝ) * (k + 1 : ℝ)) * coeff (coloredSetPartitions c m n) (k + 1) := by
  rw [coloredSetPartitions_succ, coeff_add, coeff_coloredSetPartitionsCoeffA_mul,
    coeff_coloredSetPartitionsCoeffB_mul_derivative]
  ring

lemma coeff_coloredSetPartitions_top_and_above :
    ∀ c m n : Nat,
      coeff (coloredSetPartitions c m n) n = 1 ∧
        ∀ k > n, coeff (coloredSetPartitions c m n) k = 0
  | c, m, 0 => by
      constructor
      · simp [coloredSetPartitions_zero]
      · intro k hk
        rw [coloredSetPartitions_zero, coeff_one, if_neg hk.ne']
  | c, m, n + 1 => by
      rcases coeff_coloredSetPartitions_top_and_above c m n with ⟨htop, habove⟩
      constructor
      · rw [show n + 1 = n + 0 + 1 by omega, coeff_coloredSetPartitions_succ]
        have hzero : coeff (coloredSetPartitions c m n) (n + 1) = 0 :=
          habove (n + 1) (by omega)
        simp [htop, hzero]
      · intro k hk
        cases k with
        | zero =>
            omega
        | succ j =>
            rw [show j + 1 = j + 0 + 1 by omega, coeff_coloredSetPartitions_succ]
            have hj : n < j := by omega
            have hj' : n < j + 1 := by omega
            simp [habove j hj, habove (j + 1) hj']

lemma natDegree_coloredSetPartitions (c m n : Nat) :
    (coloredSetPartitions c m n).natDegree = n := by
  rcases coeff_coloredSetPartitions_top_and_above c m n with ⟨htop, habove⟩
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => habove k hk)
  · simp [htop]

lemma monic_coloredSetPartitions (c m n : Nat) :
    (coloredSetPartitions c m n).Monic := by
  rcases coeff_coloredSetPartitions_top_and_above c m n with ⟨htop, _⟩
  rw [Monic.def, leadingCoeff, natDegree_coloredSetPartitions]
  simpa using htop

lemma coloredSetPartitions_ne_zero (c m n : Nat) :
    coloredSetPartitions c m n ≠ 0 :=
  (monic_coloredSetPartitions c m n).ne_zero

lemma coloredSetPartitions_posLeadingCoeff (c m n : Nat) :
    HasPosLeadingCoeff (coloredSetPartitions c m n) := by
  unfold HasPosLeadingCoeff
  rw [(monic_coloredSetPartitions c m n).leadingCoeff]
  norm_num

lemma coloredSetPartitions_nonnegCoeffs :
    ∀ c m n : Nat, HasNonnegCoeffs (coloredSetPartitions c m n)
  | c, m, 0 => by
      intro k
      cases k with
      | zero =>
          simp [coloredSetPartitions_zero]
      | succ k =>
          rw [coloredSetPartitions_zero, coeff_one, if_neg (Nat.succ_ne_zero k)]
  | c, m, n + 1 => by
      intro k
      cases k with
      | zero =>
          have hX_zero :
              coeff (X * coloredSetPartitions c m n) 0 = 0 := by
            simp
          have hC_zero :
              coeff (C (c : ℝ) * coloredSetPartitions c m n) 0 =
                (c : ℝ) * coeff (coloredSetPartitions c m n) 0 := by
            rw [coeff_C_mul]
          have hB_zero :
              coeff (coloredSetPartitionsCoeffB m *
                (coloredSetPartitions c m n).derivative) 0 = 0 := by
            simp [coloredSetPartitionsCoeffB]
          rw [coloredSetPartitions_succ, coeff_add, coloredSetPartitionsCoeffA, add_mul, coeff_add,
            hX_zero, hC_zero, hB_zero]
          have hc_nonneg : 0 ≤ (c : ℝ) := by positivity
          simpa using mul_nonneg hc_nonneg (coloredSetPartitions_nonnegCoeffs c m n 0)
      | succ j =>
          rw [coeff_coloredSetPartitions_succ]
          exact add_nonneg
            (coloredSetPartitions_nonnegCoeffs c m n j)
            (mul_nonneg
              (by positivity)
              (coloredSetPartitions_nonnegCoeffs c m n (j + 1)))

lemma roots_nonpos_coloredSetPartitions_of_isRealRooted {c m n : Nat}
    (hrr : IsRealRooted (coloredSetPartitions c m n)) :
    ∀ r ∈ (coloredSetPartitions c m n).roots, r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs hrr (coloredSetPartitions_nonnegCoeffs c m n)

lemma interlaces_coloredSetPartitions_zero_one (c m : Nat) :
    Interlaces (coloredSetPartitions c m 0) (coloredSetPartitions c m 1) := by
  have hdeg : (coloredSetPartitions c m 1).natDegree = 1 := by
    simpa using natDegree_coloredSetPartitions c m 1
  simpa [coloredSetPartitions_zero, coloredSetPartitions_one] using
    interlaces_one_linear (p := coloredSetPartitions c m 1) hdeg

lemma eval_coloredSetPartitionsCoeffB_nonpos_of_nonpos (m : Nat) {r : ℝ} (hr : r ≤ 0) :
    (coloredSetPartitionsCoeffB m).eval r ≤ 0 := by
  unfold coloredSetPartitionsCoeffB
  rw [eval_mul, eval_C, eval_X]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hr

lemma prec_coloredSetPartitions_one_two (c m : Nat) :
    Prec (coloredSetPartitions c m 1) (coloredSetPartitions c m 2) := by
  have hdeg : (coloredSetPartitions c m 1).natDegree = 1 := by
    simpa using natDegree_coloredSetPartitions c m 1
  have hf : IsRealRooted (coloredSetPartitions c m 1) := isRealRooted_of_degree_one hdeg
  have hInter :
      Interlaces (coloredSetPartitions c m 1).derivative (coloredSetPartitions c m 1) := by
    simpa [coloredSetPartitions_one] using
      interlaces_one_linear (p := coloredSetPartitions c m 1) hdeg
  have hg_pos :
      HasPosLeadingCoeff (coloredSetPartitions c m 1).derivative :=
    hasPosLeadingCoeff_derivative (coloredSetPartitions_posLeadingCoeff c m 1) (by
      simp [hdeg])
  have hNext_eq :
      coloredSetPartitionsCoeffA c * coloredSetPartitions c m 1 +
          coloredSetPartitionsCoeffB m * (coloredSetPartitions c m 1).derivative =
        coloredSetPartitions c m 2 := by
    exact (coloredSetPartitions_succ c m 1).symm
  have hF_pos :
      HasPosLeadingCoeff
        (coloredSetPartitionsCoeffA c * coloredSetPartitions c m 1 +
          coloredSetPartitionsCoeffB m * (coloredSetPartitions c m 1).derivative) := by
    rw [hNext_eq]
    exact coloredSetPartitions_posLeadingCoeff c m 2
  have hdeg_lo :
      (coloredSetPartitions c m 1).natDegree ≤
        (coloredSetPartitionsCoeffA c * coloredSetPartitions c m 1 +
          coloredSetPartitionsCoeffB m * (coloredSetPartitions c m 1).derivative).natDegree := by
    rw [hNext_eq, natDegree_coloredSetPartitions, natDegree_coloredSetPartitions]
    omega
  have hdeg_hi :
      (coloredSetPartitionsCoeffA c * coloredSetPartitions c m 1 +
          coloredSetPartitionsCoeffB m * (coloredSetPartitions c m 1).derivative).natDegree ≤
        (coloredSetPartitions c m 1).natDegree + 1 := by
    rw [hNext_eq, natDegree_coloredSetPartitions, natDegree_coloredSetPartitions]
  have hb_nonpos :
      ∀ r, (coloredSetPartitions c m 1).IsRoot r →
        (coloredSetPartitionsCoeffB m).eval r ≤ 0 := by
    intro r hr
    have hr_nonpos :
        r ≤ 0 :=
      roots_nonpos_coloredSetPartitions_of_isRealRooted hf r ((mem_roots hf.1).mpr hr)
    exact eval_coloredSetPartitionsCoeffB_nonpos_of_nonpos m hr_nonpos
  rw [← hNext_eq]
  exact
    prec_of_interlaces_evalCoeff_nonpos
      (f := coloredSetPartitions c m 1)
      (g := (coloredSetPartitions c m 1).derivative)
      (a := coloredSetPartitionsCoeffA c)
      (b := coloredSetPartitionsCoeffB m)
      hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos

/-- Consecutive colored set-partition polynomials satisfy `Prec`, hence form a
Sturm sequence. -/
theorem prec_coloredSetPartitions_succ (c m : Nat) :
    ∀ n : Nat, Prec (coloredSetPartitions c m n) (coloredSetPartitions c m (n + 1))
  | 0 => (interlaces_coloredSetPartitions_zero_one c m).toPrec
  | 1 => prec_coloredSetPartitions_one_two c m
  | n + 2 => by
      have hprev : Prec (coloredSetPartitions c m (n + 1))
          (coloredSetPartitions c m (n + 2)) :=
        prec_coloredSetPartitions_succ c m (n + 1)
      have hf : IsRealRooted (coloredSetPartitions c m (n + 2)) := hprev.2.1
      have hdegf : 2 ≤ (coloredSetPartitions c m (n + 2)).natDegree := by
        rw [natDegree_coloredSetPartitions]
        omega
      have hInter :
          Interlaces (coloredSetPartitions c m (n + 2)).derivative
            (coloredSetPartitions c m (n + 2)) :=
        derivative_interlaces hf hdegf
      have hg_pos :
          HasPosLeadingCoeff (coloredSetPartitions c m (n + 2)).derivative :=
        hasPosLeadingCoeff_derivative (coloredSetPartitions_posLeadingCoeff c m (n + 2)) (by
          rw [natDegree_coloredSetPartitions]
          omega)
      have hNext_eq :
          coloredSetPartitionsCoeffA c * coloredSetPartitions c m (n + 2) +
              coloredSetPartitionsCoeffB m * (coloredSetPartitions c m (n + 2)).derivative =
            coloredSetPartitions c m (n + 3) := by
        exact (coloredSetPartitions_succ c m (n + 2)).symm
      have hF_pos :
          HasPosLeadingCoeff
            (coloredSetPartitionsCoeffA c * coloredSetPartitions c m (n + 2) +
              coloredSetPartitionsCoeffB m * (coloredSetPartitions c m (n + 2)).derivative) := by
        rw [hNext_eq]
        exact coloredSetPartitions_posLeadingCoeff c m (n + 3)
      have hdeg_lo :
          (coloredSetPartitions c m (n + 2)).natDegree ≤
            (coloredSetPartitionsCoeffA c * coloredSetPartitions c m (n + 2) +
              coloredSetPartitionsCoeffB m *
                (coloredSetPartitions c m (n + 2)).derivative).natDegree := by
        rw [hNext_eq, natDegree_coloredSetPartitions, natDegree_coloredSetPartitions]
        omega
      have hdeg_hi :
          (coloredSetPartitionsCoeffA c * coloredSetPartitions c m (n + 2) +
              coloredSetPartitionsCoeffB m *
                (coloredSetPartitions c m (n + 2)).derivative).natDegree ≤
            (coloredSetPartitions c m (n + 2)).natDegree + 1 := by
        rw [hNext_eq, natDegree_coloredSetPartitions, natDegree_coloredSetPartitions]
      have hb_nonpos :
          ∀ r, (coloredSetPartitions c m (n + 2)).IsRoot r →
            (coloredSetPartitionsCoeffB m).eval r ≤ 0 := by
        intro r hr
        have hr_nonpos :
            r ≤ 0 :=
          roots_nonpos_coloredSetPartitions_of_isRealRooted hf r ((mem_roots hf.1).mpr hr)
        exact eval_coloredSetPartitionsCoeffB_nonpos_of_nonpos m hr_nonpos
      rw [← hNext_eq]
      exact
        prec_of_interlaces_evalCoeff_nonpos
          (f := coloredSetPartitions c m (n + 2))
          (g := (coloredSetPartitions c m (n + 2)).derivative)
          (a := coloredSetPartitionsCoeffA c)
          (b := coloredSetPartitionsCoeffB m)
          hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos

theorem interlaces_coloredSetPartitions_succ (c m n : Nat) :
    Interlaces (coloredSetPartitions c m n) (coloredSetPartitions c m (n + 1)) := by
  apply (prec_coloredSetPartitions_succ c m n).toInterlaces
  simp [natDegree_coloredSetPartitions]

theorem isRealRooted_coloredSetPartitions (c m : Nat) :
    ∀ n : Nat, IsRealRooted (coloredSetPartitions c m n)
  | 0 => by
      simpa [coloredSetPartitions_zero] using
        isRealRooted_of_deg_zero (p := (1 : ℝ[X])) one_ne_zero (by simp)
  | n + 1 => (prec_coloredSetPartitions_succ c m n).2.1

/-- The descending prefix `[T_n, T_{n-1}, ..., T_0]` of the colored
set-partition sequence. -/
def coloredSetPartitionsPrefix (c m : Nat) : Nat → List ℝ[X]
  | 0 => [coloredSetPartitions c m 0]
  | n + 1 => coloredSetPartitions c m (n + 1) :: coloredSetPartitionsPrefix c m n

@[simp] lemma coloredSetPartitionsPrefix_zero (c m : Nat) :
    coloredSetPartitionsPrefix c m 0 = [coloredSetPartitions c m 0] := rfl

@[simp] lemma coloredSetPartitionsPrefix_succ (c m n : Nat) :
    coloredSetPartitionsPrefix c m (n + 1) =
      coloredSetPartitions c m (n + 1) :: coloredSetPartitionsPrefix c m n := rfl

theorem isSturmSeq_coloredSetPartitionsPrefix (c m : Nat) :
    ∀ n : Nat, IsSturmSeq (coloredSetPartitionsPrefix c m n) := by
  intro n
  induction n with
  | zero =>
      simp [coloredSetPartitionsPrefix, IsSturmSeq]
  | succ n ih =>
      cases n with
      | zero =>
          simpa [coloredSetPartitionsPrefix, IsSturmSeq] using
            interlaces_coloredSetPartitions_zero_one c m
      | succ k =>
          simpa [coloredSetPartitionsPrefix, IsSturmSeq] using
            And.intro (interlaces_coloredSetPartitions_succ c m (k + 1)) ih

/-- The type `B` set-partition family is the first nontrivial colored
specialization. -/
abbrev typeBSetPartitions : Nat → ℝ[X] :=
  coloredSetPartitions 1 2

theorem interlaces_typeBSetPartitions_succ (n : Nat) :
    Interlaces (typeBSetPartitions n) (typeBSetPartitions (n + 1)) :=
  interlaces_coloredSetPartitions_succ 1 2 n

theorem isRealRooted_typeBSetPartitions (n : Nat) :
    IsRealRooted (typeBSetPartitions n) :=
  isRealRooted_coloredSetPartitions 1 2 n

end RealRooted
