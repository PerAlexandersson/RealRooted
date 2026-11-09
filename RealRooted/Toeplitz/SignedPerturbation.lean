module

public import RealRooted.Basic.ProperPosition
public import RealRooted.SimpleRoots
public import RealRooted.Toeplitz.SignedPerturbation.Rows
import RealRooted.Toeplitz.SignedPerturbation.Interlacing

/-!
# Signed Toeplitz perturbations: strict interlacing of all rows

For real `c₂, …, c_s` (`s ≥ 2`) let `P_n` be the rows defined by
`∑_n P_n(t) zⁿ = 1 / (1 - t z + z² + ∑_{j=2}^s c_j z^{j+1})`.  For `R > 1` put
`A(R) = ∑ j |c_j| R^{j+1}` and `B(R) = ∑ j (j - 1) |c_j| R^{j+1}`.

If `A(R) ≤ R² - 1` and `B(R) ≤ 1`, then every row `P_n` has only real roots, all simple, and
consecutive rows strictly interlace and have no common root (`splits_row`,
`hasSimpleRoots_row`, `strictInterl_row_succ`, `eval_row_ne_zero_of_isRoot_row_succ`).  The
coefficients may have either sign, and equality is allowed.  In particular this holds whenever
`∑_{j=2}^s j |c_j| ≤ (1/s) (1 - 1/s)^{(s-1)/2}`
(`strictInterl_row_succ_of_sum_le`).

The proof parametrizes the real values `λ = b(ρ e^{iθ})` of `b(z) = z⁻¹ + z + ∑ c_j z^j` along the
curve `Im b = 0` (`Curve`), factors the rescaled denominator as `(1 - 2 cos θ z + z²) C_θ(z)`
with `‖C_θ - 1‖₁ ≤ 1/2` (`Factorization`, `CofactorBounds`), and reads off the signs of
`P_n(λ(θ))` at the grid angles `(2 j + 1) π / (2 (n + 1))` (`Interlacing`).
-/

public section

open Polynomial

noncomputable section

namespace RealRooted.ToeplitzPerturbation

variable {s : ℕ} {c : ℕ → ℝ} {R : ℝ}


theorem splits_row (hR : 0 < R) (hA : perturbationA s c R ≤ R ^ 2 - 1)
    (hB : perturbationB s c R ≤ 1) (n : ℕ) : (row s c n).Splits := by
  cases n with
  | zero => simp [row_zero]
  | succ m => exact (row_succ_splits_strictInterl hR hA hB m).1

theorem hasSimpleRoots_row (hR : 0 < R) (hA : perturbationA s c R ≤ R ^ 2 - 1)
    (hB : perturbationB s c R ≤ 1) (n : ℕ) : RealRooted.HasSimpleRoots (row s c n) := by
  cases n with
  | zero => simp [row_zero, RealRooted.HasSimpleRoots]
  | succ m => exact (row_succ_splits_strictInterl hR hA hB m).2.1

theorem strictInterl_row_succ (hR : 0 < R) (hA : perturbationA s c R ≤ R ^ 2 - 1)
    (hB : perturbationB s c R ≤ 1) (n : ℕ) :
    RealRooted.StrictInterl (row s c n) (row s c (n + 1)) :=
  (row_succ_splits_strictInterl hR hA hB n).2.2.1

theorem eval_row_ne_zero_of_isRoot_row_succ (hR : 0 < R) (hA : perturbationA s c R ≤ R ^ 2 - 1)
    (hB : perturbationB s c R ≤ 1) (n : ℕ) {x : ℝ} (hx : (row s c (n + 1)).IsRoot x) :
    (row s c n).eval x ≠ 0 :=
  (row_succ_splits_strictInterl hR hA hB n).2.2.2 x hx



/-- The numerical identity behind the bandwidth criterion. -/
theorem rpow_mul_sqrt_pow (hs : 2 ≤ s) :
    (1 - 1 / (s : ℝ)) ^ (((s : ℝ) - 1) / 2) * (Real.sqrt ((s : ℝ) / (s - 1))) ^ (s + 1) =
      (s : ℝ) / (s - 1) := by
  have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hq : (0 : ℝ) < (s : ℝ) / (s - 1) := div_pos (by linarith) (by linarith)
  set q : ℝ := (s : ℝ) / (s - 1) with hqdef
  have h1 : 1 - 1 / (s : ℝ) = q⁻¹ := by rw [hqdef]; field_simp
  have h2 : (Real.sqrt q) ^ (s + 1) = q ^ (((s : ℝ) + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hq.le]
    congr 1; push_cast; ring
  rw [h1, h2, Real.inv_rpow hq.le, ← Real.rpow_neg hq.le, ← Real.rpow_add hq]
  have : -(((s : ℝ) - 1) / 2) + ((s : ℝ) + 1) / 2 = 1 := by ring
  rw [this, Real.rpow_one]

theorem exists_perturbationA_le_of_sum_le (hs : 2 ≤ s)
    (hS : ∑ j ∈ Finset.Icc 2 s, (j : ℝ) * |c j| ≤ 1 / s * (1 - 1 / (s : ℝ)) ^ (((s : ℝ) - 1) / 2)) :
    ∃ R : ℝ, 1 < R ∧ perturbationA s c R ≤ R ^ 2 - 1 ∧ perturbationB s c R ≤ 1 := by
  have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hs1 : (0 : ℝ) < (s : ℝ) - 1 := by linarith
  set q : ℝ := (s : ℝ) / (s - 1) with hqdef
  have hq1 : 1 < q := by rw [hqdef, lt_div_iff₀ hs1]; linarith
  set R : ℝ := Real.sqrt q with hRdef
  have hR1 : 1 < R := by rw [hRdef]; exact Real.lt_sqrt_of_sq_lt (by simpa using hq1)
  have hR2 : R ^ 2 = q := Real.sq_sqrt (by linarith)
  have hkey := rpow_mul_sqrt_pow hs
  rw [← hqdef, ← hRdef] at hkey
  set S : ℝ := ∑ j ∈ Finset.Icc 2 s, (j : ℝ) * |c j| with hSdef
  have hSR : S * R ^ (s + 1) ≤ 1 / (s - 1) := by
    calc S * R ^ (s + 1) ≤ 1 / s * (1 - 1 / (s : ℝ)) ^ (((s : ℝ) - 1) / 2) * R ^ (s + 1) :=
          mul_le_mul_of_nonneg_right hS (by positivity)
      _ = 1 / s * q := by rw [mul_assoc, hkey]
      _ = 1 / (s - 1) := by rw [hqdef]; field_simp
  refine ⟨R, hR1, ?_, ?_⟩
  · calc perturbationA s c R ≤ ∑ j ∈ Finset.Icc 2 s, (j : ℝ) * |c j| * R ^ (s + 1) := by
          unfold perturbationA
          refine Finset.sum_le_sum fun j hj => ?_
          have := (Finset.mem_Icc.mp hj).2
          have h0 : (0 : ℝ) ≤ j * |c j| := by positivity
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1.le (by lia)) h0
      _ = S * R ^ (s + 1) := by rw [hSdef, Finset.sum_mul]
      _ ≤ 1 / (s - 1) := hSR
      _ = R ^ 2 - 1 := by rw [hR2, hqdef]; field_simp; ring
  · calc perturbationB s c R ≤ ∑ j ∈ Finset.Icc 2 s, ((s : ℝ) - 1) * ((j : ℝ) * |c j|) *
            R ^ (s + 1) := by
          unfold perturbationB
          refine Finset.sum_le_sum fun j hj => ?_
          have hj2 := Finset.mem_Icc.mp hj
          have hjs : (j : ℝ) ≤ s := by exact_mod_cast hj2.2
          have h0 : (0 : ℝ) ≤ (j : ℝ) * |c j| := by positivity
          have h1 : (j : ℝ) * (j - 1) * |c j| ≤ ((s : ℝ) - 1) * ((j : ℝ) * |c j|) := by
            have : (0 : ℝ) ≤ ((s : ℝ) - j) * ((j : ℝ) * |c j|) := mul_nonneg (by linarith) h0
            nlinarith
          calc (j : ℝ) * (j - 1) * |c j| * R ^ (j + 1)
              ≤ ((s : ℝ) - 1) * ((j : ℝ) * |c j|) * R ^ (j + 1) := by gcongr
            _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1.le (by lia))
              (mul_nonneg hs1.le h0)
      _ = ((s : ℝ) - 1) * (S * R ^ (s + 1)) := by
          rw [hSdef, Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ((s : ℝ) - 1) * (1 / (s - 1)) := mul_le_mul_of_nonneg_left hSR hs1.le
      _ = 1 := by field_simp

theorem splits_row_of_sum_le (hs : 2 ≤ s)
    (hS : ∑ j ∈ Finset.Icc 2 s, (j : ℝ) * |c j| ≤ 1 / s * (1 - 1 / (s : ℝ)) ^ (((s : ℝ) - 1) / 2))
    (n : ℕ) : (row s c n).Splits := by
  obtain ⟨R, hR, hA, hB⟩ := exists_perturbationA_le_of_sum_le hs hS
  exact splits_row (zero_lt_one.trans hR) hA hB n

theorem hasSimpleRoots_row_of_sum_le (hs : 2 ≤ s)
    (hS : ∑ j ∈ Finset.Icc 2 s, (j : ℝ) * |c j| ≤ 1 / s * (1 - 1 / (s : ℝ)) ^ (((s : ℝ) - 1) / 2))
    (n : ℕ) : RealRooted.HasSimpleRoots (row s c n) := by
  obtain ⟨R, hR, hA, hB⟩ := exists_perturbationA_le_of_sum_le hs hS
  exact hasSimpleRoots_row (zero_lt_one.trans hR) hA hB n

theorem strictInterl_row_succ_of_sum_le (hs : 2 ≤ s)
    (hS : ∑ j ∈ Finset.Icc 2 s, (j : ℝ) * |c j| ≤ 1 / s * (1 - 1 / (s : ℝ)) ^ (((s : ℝ) - 1) / 2))
    (n : ℕ) : RealRooted.StrictInterl (row s c n) (row s c (n + 1)) := by
  obtain ⟨R, hR, hA, hB⟩ := exists_perturbationA_le_of_sum_le hs hS
  exact strictInterl_row_succ (zero_lt_one.trans hR) hA hB n

theorem eval_row_ne_zero_of_isRoot_row_succ_of_sum_le (hs : 2 ≤ s)
    (hS : ∑ j ∈ Finset.Icc 2 s, (j : ℝ) * |c j| ≤ 1 / s * (1 - 1 / (s : ℝ)) ^ (((s : ℝ) - 1) / 2))
    (n : ℕ) {x : ℝ} (hx : (row s c (n + 1)).IsRoot x) : (row s c n).eval x ≠ 0 := by
  obtain ⟨R, hR, hA, hB⟩ := exists_perturbationA_le_of_sum_le hs hS
  exact eval_row_ne_zero_of_isRoot_row_succ (zero_lt_one.trans hR) hA hB n hx

end RealRooted.ToeplitzPerturbation
