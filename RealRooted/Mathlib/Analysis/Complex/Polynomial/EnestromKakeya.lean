import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Eneström–Kakeya theorem

If `p = a₀ + a₁ X + ⋯ + aₙ Xⁿ` is a real polynomial with `0 < a₀ ≤ a₁ ≤ ⋯ ≤ aₙ`, then every
complex root `z` of `p` satisfies `‖z‖ ≤ 1`.  By scaling and reversal, if all coefficients are
positive then every root lies in the annulus `m ≤ ‖z‖ ≤ M`, where `m` and `M` bound the ratios
`aᵢ / aᵢ₊₁` from below and above.
-/

namespace Polynomial

open Finset

private lemma sub_one_mul_sum_range (a : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    (z - 1) * ∑ k ∈ range (n + 1), a k * z ^ k =
      a n * z ^ (n + 1) - a 0 - ∑ k ∈ range n, (a (k + 1) - a k) * z ^ (k + 1) := by
  induction n with
  | zero => rw [sum_range_one, sum_range_zero]; ring
  | succ n ih => rw [sum_range_succ, mul_add, ih, sum_range_succ]; ring

private lemma norm_le_one_of_sum_eq_zero {a : ℕ → ℝ} {n : ℕ} (h0 : 0 < a 0)
    (hmono : ∀ i < n, a i ≤ a (i + 1)) {z : ℂ}
    (hz : ∑ k ∈ range (n + 1), (a k : ℂ) * z ^ k = 0) : ‖z‖ ≤ 1 := by
  by_contra! hr
  have hd : ∀ k ∈ range n, 0 ≤ a (k + 1) - a k :=
    fun k hk => sub_nonneg.2 (hmono k (mem_range.1 hk))
  have hsum : a n = a 0 + ∑ k ∈ range n, (a (k + 1) - a k) := by
    rw [sum_range_sub]; ring
  have han : 0 < a n := by
    rw [hsum]; exact add_pos_of_pos_of_nonneg h0 (sum_nonneg hd)
  have key := sub_one_mul_sum_range (fun k => (a k : ℂ)) z n
  rw [hz, mul_zero] at key
  have heq : (a n : ℂ) * z ^ (n + 1) =
      a 0 + ∑ k ∈ range n, ((a (k + 1) : ℂ) - a k) * z ^ (k + 1) := by
    linear_combination -key
  have hle : a n * ‖z‖ ^ (n + 1) ≤ a n * ‖z‖ ^ n :=
    calc a n * ‖z‖ ^ (n + 1) = ‖(a n : ℂ) * z ^ (n + 1)‖ := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg han.le]
      _ ≤ ‖(a 0 : ℂ)‖ + ∑ k ∈ range n, ‖((a (k + 1) : ℂ) - a k) * z ^ (k + 1)‖ := by
          rw [heq]
          exact (norm_add_le _ _).trans (by gcongr; exact norm_sum_le _ _)
      _ ≤ a 0 * ‖z‖ ^ n + ∑ k ∈ range n, (a (k + 1) - a k) * ‖z‖ ^ n := by
          gcongr with k hk
          · rw [Complex.norm_real, Real.norm_of_nonneg h0.le]
            exact le_mul_of_one_le_right h0.le (one_le_pow₀ hr.le)
          · rw [norm_mul, norm_pow, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_of_nonneg (hd k hk)]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr.le (mem_range.1 hk))
              (hd k hk)
      _ = a n * ‖z‖ ^ n := by rw [← sum_mul, hsum]; ring
  exact absurd hle (not_le.2 (mul_lt_mul_of_pos_left (pow_lt_pow_right₀ hr n.lt_succ_self) han))

private lemma norm_le_of_sum_eq_zero {a : ℕ → ℝ} {n : ℕ} {M : ℝ} (h0 : 0 < a 0)
    (hM0 : 0 < M) (hM : ∀ i < n, a i ≤ M * a (i + 1)) {z : ℂ}
    (hz : ∑ k ∈ range (n + 1), (a k : ℂ) * z ^ k = 0) : ‖z‖ ≤ M := by
  have hM0' : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hM0.ne'
  have h := norm_le_one_of_sum_eq_zero (a := fun k => a k * M ^ k) (n := n) (z := z / M)
    (by simpa using h0) (fun i hi => by
      calc a i * M ^ i ≤ M * a (i + 1) * M ^ i :=
            mul_le_mul_of_nonneg_right (hM i hi) (by positivity)
        _ = a (i + 1) * M ^ (i + 1) := by ring)
    (by
      rw [← hz]
      refine sum_congr rfl fun k _ => ?_
      push_cast
      rw [div_pow]
      field_simp)
  rwa [norm_div, Complex.norm_real, Real.norm_of_nonneg hM0.le, div_le_one hM0] at h

private lemma le_norm_of_sum_eq_zero {a : ℕ → ℝ} {n : ℕ} {m : ℝ} (hn : 0 < a n)
    (hm0 : 0 < m) (hm : ∀ i < n, m * a (i + 1) ≤ a i) {z : ℂ}
    (hz : ∑ k ∈ range (n + 1), (a k : ℂ) * z ^ k = 0) : m ≤ ‖z‖ := by
  have hpos : ∀ j ≤ n, 0 < a (n - j) := by
    intro j
    induction j with
    | zero => simpa using hn
    | succ j ih =>
      intro hj
      have h := hm (n - (j + 1)) (by lia)
      rw [show n - (j + 1) + 1 = n - j by lia] at h
      exact (mul_pos hm0 (ih (by lia))).trans_le h
  have hz0 : z ≠ 0 := by
    rintro rfl
    have h0 : (a 0 : ℂ) = 0 := by simpa [sum_range_succ'] using hz
    exact (by simpa using hpos n le_rfl : 0 < a 0).ne' (mod_cast h0)
  have hwz : z⁻¹ * z = 1 := inv_mul_cancel₀ hz0
  have h := norm_le_of_sum_eq_zero (a := fun k => a (n - k)) (n := n) (M := m⁻¹) (z := z⁻¹)
    (by simpa using hn) (inv_pos.2 hm0) (fun i hi => by
      have h := hm (n - (i + 1)) (by lia)
      rw [show n - (i + 1) + 1 = n - i by lia] at h
      rw [le_inv_mul_iff₀ hm0]
      exact h) ?_
  · rw [norm_inv] at h
    exact (inv_le_inv₀ (norm_pos_iff.2 hz0) hm0).1 h
  · calc ∑ k ∈ range (n + 1), (a (n - k) : ℂ) * z⁻¹ ^ k
        = ∑ j ∈ range (n + 1), (a (n - (n + 1 - 1 - j)) : ℂ) * z⁻¹ ^ (n + 1 - 1 - j) :=
          (sum_range_reflect (fun k => (a (n - k) : ℂ) * z⁻¹ ^ k) (n + 1)).symm
      _ = z⁻¹ ^ n * ∑ j ∈ range (n + 1), (a j : ℂ) * z ^ j := by
          rw [mul_sum]
          refine sum_congr rfl fun j hj => ?_
          obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (mem_range.1 hj))
          rw [show n + 1 - 1 - j = i by lia, show n - i = j by lia, hi]
          linear_combination (-(a j : ℂ) * z⁻¹ ^ i) * congrArg (· ^ j) hwz
      _ = 0 := by rw [hz, mul_zero]

private lemma sum_eq_zero_of_isRoot {p : ℝ[X]} {z : ℂ}
    (hz : (p.map (algebraMap ℝ ℂ)).IsRoot z) :
    ∑ k ∈ range (p.natDegree + 1), (p.coeff k : ℂ) * z ^ k = 0 := by
  rw [IsRoot.def, eval_map, eval₂_eq_sum_range] at hz
  simpa using hz

/-- **Eneström–Kakeya theorem.** If the coefficients of a real polynomial satisfy
`0 < a₀ ≤ a₁ ≤ ⋯ ≤ aₙ`, then every complex root `z` satisfies `‖z‖ ≤ 1`. -/
theorem norm_le_one_of_isRoot_of_coeff_monotone {p : ℝ[X]} (h0 : 0 < p.coeff 0)
    (hmono : ∀ i < p.natDegree, p.coeff i ≤ p.coeff (i + 1)) {z : ℂ}
    (hz : (p.map (algebraMap ℝ ℂ)).IsRoot z) : ‖z‖ ≤ 1 :=
  norm_le_one_of_sum_eq_zero h0 hmono (sum_eq_zero_of_isRoot hz)

/-- **Eneström–Kakeya theorem**, upper bound: if `0 < a₀`, `0 < M` and `aᵢ ≤ M aᵢ₊₁` for all
`i < n`, then every complex root `z` satisfies `‖z‖ ≤ M`. -/
theorem norm_le_of_isRoot_of_coeff_le_mul {p : ℝ[X]} {M : ℝ} (h0 : 0 < p.coeff 0)
    (hM0 : 0 < M) (hM : ∀ i < p.natDegree, p.coeff i ≤ M * p.coeff (i + 1)) {z : ℂ}
    (hz : (p.map (algebraMap ℝ ℂ)).IsRoot z) : ‖z‖ ≤ M :=
  norm_le_of_sum_eq_zero h0 hM0 hM (sum_eq_zero_of_isRoot hz)

/-- **Eneström–Kakeya theorem**, lower bound: if the leading coefficient is positive and
`m aᵢ₊₁ ≤ aᵢ` for all `i < n`, then every complex root `z` satisfies `m ≤ ‖z‖`. -/
theorem le_norm_of_isRoot_of_mul_coeff_le {p : ℝ[X]} {m : ℝ} (hn : 0 < p.leadingCoeff)
    (hm : ∀ i < p.natDegree, m * p.coeff (i + 1) ≤ p.coeff i) {z : ℂ}
    (hz : (p.map (algebraMap ℝ ℂ)).IsRoot z) : m ≤ ‖z‖ := by
  rcases le_or_gt m 0 with hm0 | hm0
  · exact hm0.trans (norm_nonneg z)
  · exact le_norm_of_sum_eq_zero hn hm0 hm (sum_eq_zero_of_isRoot hz)

/-- **Eneström–Kakeya theorem**, annulus form: if all coefficients `a₀, …, aₙ` are positive and
`m aᵢ₊₁ ≤ aᵢ ≤ M aᵢ₊₁` for all `i < n`, then every complex root `z` satisfies
`m ≤ ‖z‖ ≤ M`. -/
theorem norm_mem_Icc_of_isRoot_of_coeff_pos {p : ℝ[X]} {m M : ℝ}
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hm : ∀ i < p.natDegree, m * p.coeff (i + 1) ≤ p.coeff i)
    (hM : ∀ i < p.natDegree, p.coeff i ≤ M * p.coeff (i + 1)) {z : ℂ}
    (hz : (p.map (algebraMap ℝ ℂ)).IsRoot z) : ‖z‖ ∈ Set.Icc m M := by
  have hn : p.natDegree ≠ 0 := by
    intro h
    have hs := sum_eq_zero_of_isRoot hz
    rw [h, sum_range_one, pow_zero, mul_one] at hs
    exact (hpos 0 (Nat.zero_le _)).ne' (mod_cast hs)
  have hM0 : 0 < M := by
    have h1 := hM 0 (Nat.pos_of_ne_zero hn)
    have h2 := hpos 0 (Nat.zero_le _)
    have h3 := hpos 1 (Nat.one_le_iff_ne_zero.2 hn)
    nlinarith
  exact ⟨le_norm_of_isRoot_of_mul_coeff_le (hpos _ le_rfl) hm hz,
    norm_le_of_isRoot_of_coeff_le_mul (hpos 0 (Nat.zero_le _)) hM0 hM hz⟩

end Polynomial
