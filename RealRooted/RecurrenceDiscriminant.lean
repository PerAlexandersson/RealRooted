import Mathlib

/-!
# Nonnegative second-order recurrences have real characteristic roots

This file isolates the analytic core of the degree-two forward
Aissen--Schoenberg--Whitney theorem: a second-order linear recurrence whose
terms are all nonnegative must have a real characteristic polynomial.
-/

namespace RealRooted

set_option linter.flexible false in
/-- A second-order linear recurrence whose terms are all nonnegative has real
characteristic roots.  If `D 0 = 1`, `D 1 = b`,
`D (n + 2) = b * D (n + 1) - Q * D n`, and every `D n` is nonnegative, then
the characteristic polynomial `x^2 - b x + Q` has nonnegative discriminant:
`4 * Q ≤ b ^ 2`. -/
lemma four_mul_le_sq_of_recurrence_nonneg {b Q : ℝ} {D : ℕ → ℝ}
    (h0 : D 0 = 1) (h1 : D 1 = b)
    (hrec : ∀ n, D (n + 2) = b * D (n + 1) - Q * D n)
    (hpos : ∀ n, 0 ≤ D n) :
    4 * Q ≤ b ^ 2 := by
  by_contra h
  obtain ⟨ρ, θ, hθ_pos, hθ_lt_pi, h_eq⟩ :
      ∃ ρ θ : ℝ,
        0 < ρ ∧ 0 < θ ∧ θ < Real.pi ∧ b = 2 * ρ * Real.cos θ ∧ Q = ρ ^ 2 := by
    use Real.sqrt Q, Real.arccos (b / (2 * Real.sqrt Q))
    refine
      ⟨Real.sqrt_pos.mpr (by nlinarith), Real.arccos_pos.mpr ?_,
        lt_of_le_of_ne (Real.arccos_le_pi _) ?_, ?_, ?_⟩
    · rw [div_lt_iff₀] <;>
        nlinarith [Real.sqrt_nonneg Q, Real.sq_sqrt (show 0 ≤ Q by nlinarith),
          hpos 0, hpos 1, hpos 2, hrec 0, hrec 1]
    · norm_num [Real.arccos_eq_pi]
      rw [lt_div_iff₀] <;>
        nlinarith [Real.sqrt_nonneg Q, Real.sq_sqrt (show 0 ≤ Q by nlinarith)]
    · rw [Real.cos_arccos]
      · rw [mul_div_cancel₀ _
          (mul_ne_zero two_ne_zero (Real.sqrt_ne_zero'.mpr (by nlinarith)))]
      · rw [le_div_iff₀] <;>
          nlinarith [Real.sqrt_nonneg Q, Real.sq_sqrt (show 0 ≤ Q by nlinarith)]
      · exact
          div_le_one_of_le₀
            (by
              nlinarith [Real.sqrt_nonneg Q,
                Real.sq_sqrt (show 0 ≤ Q by nlinarith)])
            (by positivity)
    · rw [Real.sq_sqrt (by nlinarith)]
  have h_induction :
      ∀ n, D n = ρ ^ n * Real.sin ((n + 1) * θ) / Real.sin θ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        rcases n with _ | _ | n <;> simp_all +decide
        · rw [div_self (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ_lt_pi h_eq.1))]
        · rw [eq_div_iff h0]
          norm_num [Real.sin_two_mul]
          ring
        · rw [show ((n + 1 + 1 + 1 : ℝ) * θ) = (n + 1 + 1) * θ + θ by ring,
            show ((n + 1 : ℝ) * θ) = (n + 1 + 1) * θ - θ by ring]
          norm_num [Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub]
          ring
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Real.pi < (N + 1) * θ ∧ (N + 1) * θ < 2 * Real.pi := by
    refine ⟨⌊Real.pi / θ⌋₊, ?_, ?_⟩
    · nlinarith [Nat.lt_floor_add_one (Real.pi / θ),
        mul_div_cancel₀ Real.pi hθ_lt_pi.ne']
    · nlinarith [Nat.floor_le (show 0 ≤ Real.pi / θ by positivity),
        mul_div_cancel₀ Real.pi hθ_lt_pi.ne']
  have h_neg : D N < 0 := by
    rw [h_induction, div_lt_iff₀] <;>
      nlinarith [Real.sin_pos_of_pos_of_lt_pi hθ_lt_pi h_eq.1,
        pow_pos hθ_pos N,
        show Real.sin ((N + 1) * θ) < 0 from by
          rw [← Real.cos_sub_pi_div_two]
          exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)]
  linarith [hpos N]

end RealRooted
