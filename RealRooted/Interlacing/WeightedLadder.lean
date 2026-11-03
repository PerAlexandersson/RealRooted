module

public import RealRooted.BinaryRunTransformation.CriticalValue
public import RealRooted.Interlacing.CoupledQuadraticRecurrence
import RealRooted.BalancedRunTransformation.Preservation

/-!
# Weighted ladder polynomials

For real `u v` define `L₀ = 1`, `L₁ = 1 + u x`, `C₀ = 0` (so `C₁ = 1`), and
`Cₙ₊₁ = Lₙ + v x Cₙ`, `Lₙ₊₁ = (1 + u x) Lₙ + 2 v x Cₙ + v² x² Lₙ₋₁` for `n ≥ 1`.
We prove the degree bounds `deg Lₙ = n`, `deg Cₙ ≤ n - 1` and nonnegativity of the coefficients
for `u, v ≥ 0`, `u > 0`, and the scalar recurrence
`Lₙ₊₃ = (1 + (u + v) x) Lₙ₊₂ + v x (1 + (v - u) x) Lₙ₊₁ - v³ x³ Lₙ`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

mutual

/-- The weighted ladder polynomial `Lₙ`: `L₀ = 1`, `L₁ = 1 + u x` and
`Lₙ₊₁ = (1 + u x) Lₙ + 2 v x Cₙ + v² x² Lₙ₋₁` for `n ≥ 1`. -/
def ladderL (u v : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + C u * X
  | n + 2 => (1 + C u * X) * ladderL u v (n + 1) + 2 * C v * X * ladderC u v (n + 1)
      + C v ^ 2 * X ^ 2 * ladderL u v n

/-- The auxiliary ladder polynomial `Cₙ`: `C₀ = 0` and `Cₙ₊₁ = Lₙ + v x Cₙ`, so `C₁ = 1`. -/
def ladderC (u v : ℝ) : ℕ → ℝ[X]
  | 0 => 0
  | n + 1 => ladderL u v n + C v * X * ladderC u v n

end

variable {u v : ℝ}

/-- `L₀ = 1`. -/
@[simp] theorem ladderL_zero : ladderL u v 0 = 1 := by simp [ladderL]

/-- `L₁ = 1 + u x`. -/
theorem ladderL_one : ladderL u v 1 = 1 + C u * X := by simp [ladderL]

/-- The recurrence `Lₙ₊₁ = (1 + u x) Lₙ + 2 v x Cₙ + v² x² Lₙ₋₁` for `n ≥ 1`. -/
theorem ladderL_add_two (n : ℕ) :
    ladderL u v (n + 2) = (1 + C u * X) * ladderL u v (n + 1) + 2 * C v * X * ladderC u v (n + 1)
      + C v ^ 2 * X ^ 2 * ladderL u v n := by
  rw [ladderL]

/-- `C₀ = 0`. -/
@[simp] theorem ladderC_zero : ladderC u v 0 = 0 := by simp [ladderC]

/-- The recurrence `Cₙ₊₁ = Lₙ + v x Cₙ`. -/
theorem ladderC_succ (n : ℕ) : ladderC u v (n + 1) = ladderL u v n + C v * X * ladderC u v n := by
  rw [ladderC]

/-- `C₁ = 1`. -/
@[simp] theorem ladderC_one : ladderC u v 1 = 1 := by simp [ladderC_succ]

/-! ### Scalar recurrence -/

/-- The scalar recurrence `Lₙ₊₃ = (1 + (u + v) x) Lₙ₊₂ + v x (1 + (v - u) x) Lₙ₊₁ - v³ x³ Lₙ`,
obtained by eliminating `C`.  Its residual is `E₍ₙ₊₂₎ - v x E₍ₙ₊₁₎ + 2 v x G₍ₙ₊₁₎`, where `E`
and `G` are the residuals of the defining recurrences. -/
theorem ladderL_add_three (n : ℕ) :
    ladderL u v (n + 3) = (1 + C (u + v) * X) * ladderL u v (n + 2)
      + C v * X * (1 + C (v - u) * X) * ladderL u v (n + 1) - C v ^ 3 * X ^ 3 * ladderL u v n := by
  have hE := ladderL_add_two (u := u) (v := v) (n + 1)
  have hE' := ladderL_add_two (u := u) (v := v) n
  have hG := ladderC_succ (u := u) (v := v) (n + 1)
  simp only [map_add, map_sub]
  linear_combination hE + (- C v * X) * hE' + 2 * C v * X * hG

/-! ### Degrees and coefficients -/

private lemma natDegree_one_add_C_mul_X_le : (1 + C u * X).natDegree ≤ 1 := by
  rw [add_comm, ← C_1]
  exact natDegree_linear_le

private lemma natDegree_ladder_le (u v : ℝ) (n : ℕ) :
    (ladderL u v n).natDegree ≤ n ∧ (ladderL u v (n + 1)).natDegree ≤ n + 1 ∧
      (ladderC u v (n + 1)).natDegree ≤ n := by
  induction n with
  | zero =>
    refine ⟨by simp, ?_, by simp⟩
    rw [ladderL_one]
    exact natDegree_one_add_C_mul_X_le
  | succ n ih =>
    obtain ⟨h0, h1, hC⟩ := ih
    have hlin : (1 + C u * X).natDegree ≤ 1 := natDegree_one_add_C_mul_X_le
    have hX : (2 * C v * X : ℝ[X]).natDegree ≤ 1 := by compute_degree
    have hX2 : (C v ^ 2 * X ^ 2 : ℝ[X]).natDegree ≤ 2 := by compute_degree
    have hC' : (ladderC u v (n + 2)).natDegree ≤ n + 1 := by
      rw [ladderC_succ]
      refine natDegree_add_le_of_degree_le h1 ?_
      have := natDegree_mul_le (p := C v * X) (q := ladderC u v (n + 1))
      have h2 : (C v * X : ℝ[X]).natDegree ≤ 1 := by compute_degree
      lia
    refine ⟨h1, ?_, hC'⟩
    rw [ladderL_add_two]
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
    · have := natDegree_mul_le (p := 1 + C u * X) (q := ladderL u v (n + 1))
      lia
    · have := natDegree_mul_le (p := 2 * C v * X) (q := ladderC u v (n + 1))
      lia
    · have := natDegree_mul_le (p := C v ^ 2 * X ^ 2) (q := ladderL u v n)
      lia

/-- `deg Lₙ ≤ n`. -/
theorem natDegree_ladderL_le (u v : ℝ) (n : ℕ) : (ladderL u v n).natDegree ≤ n :=
  (natDegree_ladder_le u v n).1

/-- `deg Cₙ ≤ n - 1`. -/
theorem natDegree_ladderC_le (u v : ℝ) (n : ℕ) : (ladderC u v n).natDegree ≤ n - 1 := by
  cases n with
  | zero => simp
  | succ n => simpa using (natDegree_ladder_le u v n).2.2

/-- The constant coefficient of `Lₙ` is `1`. -/
theorem coeff_zero_ladderL (u v : ℝ) (n : ℕ) : (ladderL u v n).coeff 0 = 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [ladderL_one]
  | more n h0 h1 =>
    rw [coeff_zero_eq_eval_zero] at h1 ⊢
    simp [ladderL_add_two, h1]

/-- The constant coefficient of `Cₙ₊₁` is `1`. -/
theorem coeff_zero_ladderC_succ (u v : ℝ) (n : ℕ) : (ladderC u v (n + 1)).coeff 0 = 1 := by
  rw [ladderC_succ, coeff_zero_eq_eval_zero]
  simpa [coeff_zero_eq_eval_zero] using coeff_zero_ladderL u v n

private lemma coeff_one_add_C_mul_X_mul (q : ℝ[X]) (k : ℕ) :
    ((1 + C u * X) * q).coeff (k + 1) = q.coeff (k + 1) + u * q.coeff k := by
  rw [add_mul, one_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul]

/-- The nonnegativity, leading-coefficient and constant-term invariants of the ladder. -/
private lemma hasNonnegCoeffs_ladder (hu : 0 < u) (hv : 0 ≤ v) (n : ℕ) :
    HasNonnegCoeffs (ladderL u v n) ∧ HasNonnegCoeffs (ladderL u v (n + 1)) ∧
      HasNonnegCoeffs (ladderC u v (n + 1)) ∧ 0 < (ladderL u v n).coeff n ∧
      0 < (ladderL u v (n + 1)).coeff (n + 1) := by
  induction n with
  | zero =>
    refine ⟨by simpa using hasNonnegCoeffs_one, ?_, by simpa using hasNonnegCoeffs_one, by simp,
      by simp [ladderL_one, coeff_one, hu]⟩
    rw [ladderL_one]
    exact hasNonnegCoeffs_one.add (hasNonnegCoeffs_C_mul hu.le hasNonnegCoeffs_X)
  | succ n ih =>
    obtain ⟨hL0, hL1, hC1, hp0, hp1⟩ := ih
    have hlin : HasNonnegCoeffs (1 + C u * X) :=
      hasNonnegCoeffs_one.add (hasNonnegCoeffs_C_mul hu.le hasNonnegCoeffs_X)
    have hvX : HasNonnegCoeffs (C v * X) := hasNonnegCoeffs_C_mul hv hasNonnegCoeffs_X
    have hC2 : HasNonnegCoeffs (ladderC u v (n + 2)) := by
      rw [ladderC_succ]
      exact hL1.add (hvX.mul hC1)
    have hT1 : HasNonnegCoeffs ((1 + C u * X) * ladderL u v (n + 1)) := hlin.mul hL1
    have hT2 : HasNonnegCoeffs (2 * C v * X * ladderC u v (n + 1)) := by
      have : (2 * C v * X * ladderC u v (n + 1) : ℝ[X]) =
          C (2 : ℝ) * (C v * X) * ladderC u v (n + 1) := by
        rw [show C (2 : ℝ) = (2 : ℝ[X]) from map_ofNat C 2]
        ring
      rw [this]
      exact (hasNonnegCoeffs_C_mul (by norm_num) hvX).mul hC1
    have hT3 : HasNonnegCoeffs (C v ^ 2 * X ^ 2 * ladderL u v n) :=
      (((hasNonnegCoeffs_C hv).pow 2).mul (hasNonnegCoeffs_X.pow 2)).mul hL0
    have hL2 : HasNonnegCoeffs (ladderL u v (n + 2)) := by
      rw [ladderL_add_two]
      exact (hT1.add hT2).add hT3
    refine ⟨hL1, hL2, hC2, hp1, ?_⟩
    rw [ladderL_add_two, coeff_add, coeff_add, coeff_one_add_C_mul_X_mul]
    have := hT2 (n + 1 + 1)
    have := hT3 (n + 1 + 1)
    have := hL1 (n + 1 + 1)
    nlinarith [mul_pos hu hp1]

/-- `Lₙ` has nonnegative coefficients. -/
theorem hasNonnegCoeffs_ladderL (hu : 0 < u) (hv : 0 ≤ v) (n : ℕ) :
    HasNonnegCoeffs (ladderL u v n) :=
  (hasNonnegCoeffs_ladder hu hv n).1

/-- `Cₙ` has nonnegative coefficients. -/
theorem hasNonnegCoeffs_ladderC (hu : 0 < u) (hv : 0 ≤ v) (n : ℕ) :
    HasNonnegCoeffs (ladderC u v n) := by
  cases n with
  | zero => simpa using hasNonnegCoeffs_zero
  | succ n => exact (hasNonnegCoeffs_ladder hu hv n).2.2.1

/-- `deg Lₙ = n`. -/
theorem natDegree_ladderL (hu : 0 < u) (hv : 0 ≤ v) (n : ℕ) : (ladderL u v n).natDegree = n :=
  le_antisymm (natDegree_ladderL_le u v n)
    (le_natDegree_of_ne_zero (hasNonnegCoeffs_ladder hu hv n).2.2.2.1.ne')

/-- `Lₙ` has positive leading coefficient. -/
theorem hasPosLeadingCoeff_ladderL (hu : 0 < u) (hv : 0 ≤ v) (n : ℕ) :
    HasPosLeadingCoeff (ladderL u v n) :=
  (hasNonnegCoeffs_ladderL hu hv n).pos_leadingCoeff fun h0 => by
    simpa [h0] using coeff_zero_ladderL u v n

/-- `Lₙ` has strictly negative roots only. -/
theorem lt_zero_of_mem_roots_ladderL (hu : 0 < u) (hv : 0 ≤ v) (n : ℕ) :
    ∀ r ∈ (ladderL u v n).roots, r < 0 :=
  roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne (hasNonnegCoeffs_ladderL hu hv n)
    (by simp [coeff_zero_ladderL])

/-! ### Signed parity lifts -/

private lemma eq_of_forall_eval_eq_of_ne_zero {p q : ℝ[X]}
    (h : ∀ r : ℝ, r ≠ 0 → p.eval r = q.eval r) : p = q := by
  have hX : (X : ℝ[X]) * p = X * q := by
    refine Polynomial.funext fun r => ?_
    by_cases hr : r = 0
    · simp [hr]
    · simp [h r hr]
  exact mul_left_cancel₀ X_ne_zero hX

private lemma eval_signedParityLift_ladderL (u v : ℝ) (n : ℕ) {r : ℝ} (hr : r ≠ 0) :
    (signedParityLift (2 * n) (ladderL u v n)).eval r =
      r ^ (2 * n) * (ladderL u v n).eval (-(r ^ 2)⁻¹) :=
  eval_signedParityLift (by have := natDegree_ladderL_le u v n; lia) hr

private lemma eval_signedParityLift_ladderC (u v : ℝ) (n : ℕ) {r : ℝ} (hr : r ≠ 0) :
    (signedParityLift (2 * n + 1) (ladderC u v (n + 1))).eval r =
      r ^ (2 * n + 1) * (ladderC u v (n + 1)).eval (-(r ^ 2)⁻¹) :=
  eval_signedParityLift (by have := natDegree_ladderC_le u v (n + 1); lia) hr

/-- The signed parity lifts `Aₙ(t) = t^{2n} Lₙ(-t⁻²)` and `Bₙ(t) = t^{2n-1} Cₙ(-t⁻²)` of the
weighted ladder satisfy the coupled quadratic recurrence with `ℓₙ = t`, `uₙ = u`, `vₙ = v`. -/
theorem CoupledQuadraticRecurrence.signedParityLift_ladder (hu : 0 < u) (hv : 0 < v) :
    CoupledQuadraticRecurrence (fun _ => 1) (fun _ => 0) (fun _ => u) (fun _ => v)
      (fun n => signedParityLift (2 * n) (ladderL u v n))
      (fun n => signedParityLift (2 * n - 1) (ladderC u v n)) where
  a_pos _ := one_pos
  u_zero_pos := hu
  u_nonneg _ := hu.le
  v_pos _ := hv
  A_zero := by simp [signedParityLift]
  B_one := by
    refine eq_of_forall_eval_eq_of_ne_zero fun r hr => ?_
    have := eval_signedParityLift_ladderC u v 0 hr
    simpa using this
  A_one := by
    refine eq_of_forall_eval_eq_of_ne_zero fun r hr => ?_
    have := eval_signedParityLift_ladderL u v 1 hr
    simp only [ladderL_one, eval_add, eval_mul, eval_C, eval_X, eval_one, eval_sub,
      eval_pow] at this ⊢
    rw [this]
    field_simp
    ring
  B_succ n := by
    refine eq_of_forall_eval_eq_of_ne_zero fun r hr => ?_
    have e1 : 2 * (n + 2) - 1 = 2 * (n + 1) + 1 := by lia
    have e2 : 2 * (n + 1) - 1 = 2 * n + 1 := by lia
    have hs : r ^ 2 * -(r ^ 2)⁻¹ = -1 := by field_simp
    simp only [e1, e2, eval_sub, eval_mul, eval_add, eval_C, eval_X]
    rw [eval_signedParityLift_ladderC u v (n + 1) hr, eval_signedParityLift_ladderL u v (n + 1) hr,
      eval_signedParityLift_ladderC u v n hr, ladderC_succ]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    linear_combination (v * r ^ (2 * n + 1) * (ladderC u v (n + 1)).eval (-(r ^ 2)⁻¹)) * hs
  A_succ n := by
    refine eq_of_forall_eval_eq_of_ne_zero fun r hr => ?_
    have e2 : 2 * (n + 1) - 1 = 2 * n + 1 := by lia
    have hs : r ^ 2 * -(r ^ 2)⁻¹ = -1 := by field_simp
    simp only [e2, eval_sub, eval_mul, eval_add, eval_C, eval_X, eval_pow, eval_ofNat]
    rw [eval_signedParityLift_ladderL u v (n + 2) hr, eval_signedParityLift_ladderL u v (n + 1) hr,
      eval_signedParityLift_ladderC u v n hr, eval_signedParityLift_ladderL u v n hr,
      ladderL_add_two]
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_one, eval_ofNat]
    linear_combination (u * r ^ (2 * n + 2) * (ladderL u v (n + 1)).eval (-(r ^ 2)⁻¹)
      + 2 * v * r ^ (2 * n + 2) * (ladderC u v (n + 1)).eval (-(r ^ 2)⁻¹)
      + v ^ 2 * r ^ (2 * n) * (ladderL u v n).eval (-(r ^ 2)⁻¹)
        * (r ^ 2 * -(r ^ 2)⁻¹ - 1)) * hs

/-! ### Splitting and simple roots -/

/-- A nonzero polynomial with only negative roots has simple roots when its signed parity lift
has simple roots (`p` is recovered from `t ^ N p(-t⁻²)`). -/
theorem HasSimpleRoots.of_signedParityLift {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N / 2)
    (hp0 : p ≠ 0) (hneg : ∀ s, p.IsRoot s → s < 0) (h : HasSimpleRoots (signedParityLift N p)) :
    HasSimpleRoots p := by
  intro s hs
  have hsneg := hneg s hs
  have hder : ¬ p.derivative.IsRoot s := by
    intro hd
    have hsqrt : 0 < Real.sqrt (-s) := Real.sqrt_pos.mpr (neg_pos.mpr hsneg)
    have hr : 0 < (Real.sqrt (-s))⁻¹ := inv_pos.mpr hsqrt
    have hrs : -(((Real.sqrt (-s))⁻¹) ^ 2)⁻¹ = s := by
      rw [inv_pow, inv_inv, Real.sq_sqrt (neg_nonneg.mpr hsneg.le), neg_neg]
    have hroot : (signedParityLift N p).IsRoot (Real.sqrt (-s))⁻¹ := by
      rw [IsRoot, eval_signedParityLift hp hr.ne', hrs, hs.eq_zero, mul_zero]
    have hXp : (X * p.derivative).natDegree ≤ N / 2 := by
      by_cases hd0 : p.natDegree = 0
      · simp [derivative_of_natDegree_zero hd0]
      · have := natDegree_mul_le (p := (X : ℝ[X])) (q := p.derivative)
        have := natDegree_derivative_le p
        have : (X : ℝ[X]).natDegree ≤ 1 := natDegree_X_le
        lia
    have hxd := congrArg (eval (Real.sqrt (-s))⁻¹) (X_mul_derivative_signedParityLift N p)
    rw [eval_mul, eval_sub, eval_mul, eval_mul, eval_C, eval_C, eval_X, hroot.eq_zero,
      eval_signedParityLift hXp hr.ne', hrs, eval_mul, eval_X, hd.eq_zero] at hxd
    have hzero : (signedParityLift N p).derivative.eval (Real.sqrt (-s))⁻¹ = 0 := by
      simpa [hr.ne'] using hxd
    exact h.eval_derivative_ne_zero hroot hzero
  have hpos : 0 < p.rootMultiplicity s := (rootMultiplicity_pos hp0).2 hs
  by_contra hne
  exact hder ((one_lt_rootMultiplicity_iff_isRoot hp0).1 (by lia)).2

/-- Every `Lₙ` splits over `ℝ`, for `u, v > 0`.  It is the descent of the real-rooted lift `Aₙ`. -/
theorem splits_ladderL (hu : 0 < u) (hv : 0 < v) (n : ℕ) : (ladderL u v n).Splits := by
  cases n with
  | zero => simp
  | succ n =>
    have h := CoupledQuadraticRecurrence.signedParityLift_ladder hu hv
    have hA := (h.strictInterl_B_succ_A_succ n).2.1.2
    exact splits_of_signedParityLift_splits (n := 2 * (n + 1))
      (by have := natDegree_ladderL_le u v (n + 1); lia) hA

/-- Every `Lₙ` has simple real roots, for `u, v > 0`. -/
theorem hasSimpleRoots_ladderL (hu : 0 < u) (hv : 0 < v) (n : ℕ) :
    HasSimpleRoots (ladderL u v n) := by
  cases n with
  | zero => intro r hr; simp at hr
  | succ n =>
    have h := CoupledQuadraticRecurrence.signedParityLift_ladder hu hv
    have hne := (hasPosLeadingCoeff_ladderL hu hv.le (n + 1)).ne_zero
    exact HasSimpleRoots.of_signedParityLift (N := 2 * (n + 1))
      (by have := natDegree_ladderL_le u v (n + 1); lia) hne
      (fun r hr => lt_zero_of_mem_roots_ladderL hu hv.le _ r ((mem_roots hne).2 hr))
      (h.hasSimpleRoots_A_succ n)

/-! ### The scalar recurrence -/

/-- `L₂ = 1 + 2 (u + v) x + (u² + v²) x²`. -/
theorem ladderL_two :
    ladderL u v 2 = 1 + C (2 * (u + v)) * X + C (u ^ 2 + v ^ 2) * X ^ 2 := by
  rw [ladderL_add_two 0]
  simp only [zero_add, ladderL_zero, ladderL_one, ladderC_one, map_add, map_mul, map_pow,
    map_ofNat]
  ring

/-- A sequence of polynomials satisfying the scalar recurrence for the weighted ladder: the seeds
`1`, `1 + u x`, `1 + 2 (u + v) x + (u² + v²) x²` and
`Fₙ₊₃ = (1 + (u + v) x) Fₙ₊₂ + v x (1 + (v - u) x) Fₙ₊₁ - v³ x³ Fₙ`. -/
structure LadderScalarRecurrence (u v : ℝ) (F : ℕ → ℝ[X]) : Prop where
  /-- `F₀ = 1`. -/
  F_zero : F 0 = 1
  /-- `F₁ = 1 + u x`. -/
  F_one : F 1 = 1 + C u * X
  /-- `F₂ = 1 + 2 (u + v) x + (u² + v²) x²`. -/
  F_two : F 2 = 1 + C (2 * (u + v)) * X + C (u ^ 2 + v ^ 2) * X ^ 2
  /-- The scalar recurrence. -/
  F_add_three : ∀ n, F (n + 3) = (1 + C (u + v) * X) * F (n + 2)
    + C v * X * (1 + C (v - u) * X) * F (n + 1) - C v ^ 3 * X ^ 3 * F n

/-- The weighted ladder satisfies its scalar recurrence. -/
theorem LadderScalarRecurrence.of_ladderL (u v : ℝ) : LadderScalarRecurrence u v (ladderL u v) where
  F_zero := ladderL_zero
  F_one := ladderL_one
  F_two := ladderL_two
  F_add_three := ladderL_add_three

/-- Three seeds and the scalar recurrence determine the weighted ladder. -/
theorem LadderScalarRecurrence.eq_ladderL {F : ℕ → ℝ[X]} (h : LadderScalarRecurrence u v F)
    (n : ℕ) : F n = ladderL u v n := by
  have key : ∀ n, F n = ladderL u v n ∧ F (n + 1) = ladderL u v (n + 1) ∧
      F (n + 2) = ladderL u v (n + 2) := by
    intro n
    induction n with
    | zero =>
      exact ⟨by simp [h.F_zero], by simp [h.F_one, ladderL_one], by rw [h.F_two, ladderL_two]⟩
    | succ n ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      refine ⟨h1, h2, ?_⟩
      rw [h.F_add_three, ladderL_add_three, h0, h1, h2]
  exact (key n).1

/-- Real-rootedness of the scalar recurrence: every `Fₙ` splits when `u, v > 0`. -/
theorem LadderScalarRecurrence.splits {F : ℕ → ℝ[X]} (h : LadderScalarRecurrence u v F)
    (hu : 0 < u) (hv : 0 < v) (n : ℕ) : (F n).Splits := by
  rw [h.eq_ladderL]
  exact splits_ladderL hu hv n

/-- Every `Fₙ` has simple real roots when `u, v > 0`. -/
theorem LadderScalarRecurrence.hasSimpleRoots {F : ℕ → ℝ[X]} (h : LadderScalarRecurrence u v F)
    (hu : 0 < u) (hv : 0 < v) (n : ℕ) : HasSimpleRoots (F n) := by
  rw [h.eq_ladderL]
  exact hasSimpleRoots_ladderL hu hv n

/-- Every `Fₙ` has nonnegative coefficients when `u > 0` and `v ≥ 0`. -/
theorem LadderScalarRecurrence.hasNonnegCoeffs {F : ℕ → ℝ[X]} (h : LadderScalarRecurrence u v F)
    (hu : 0 < u) (hv : 0 ≤ v) (n : ℕ) : HasNonnegCoeffs (F n) := by
  rw [h.eq_ladderL]
  exact hasNonnegCoeffs_ladderL hu hv n

end RealRooted
