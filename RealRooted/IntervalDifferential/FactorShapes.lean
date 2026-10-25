/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.ParityQuarticFactor
public import Mathlib.Tactic

/-!
# Real factor shapes and inheritance of a complex root disk

These elementary factor lemmas prepare the induction in Appendix C.4 of
`alternating_eulerian_shorter_proof.md`. A real monic quadratic is either a
product of two real linear factors or a conjugate-pair factor.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace RealRooted.IntervalDifferential


/-- A monic parity polynomial of degree three has the cubic seed form. -/
theorem monic_parity_cubic_shape {q : ℝ[X]} (hq : q.Monic)
    (hdeg : q.natDegree = 3)
    (hparity : q.comp (-X) = q ∨ q.comp (-X) = -q) :
    ∃ k : ℝ, q = X ^ 3 + C k * X := by
  have hlead : q.coeff 3 = 1 := by simpa [hdeg] using hq.coeff_natDegree
  rcases hparity with heven | hodd
  · have h := congrArg (fun f : ℝ[X] => f.coeff 3) heven
    rw [coeff_comp_neg_X] at h
    norm_num [hlead] at h
  · have hzero := congrArg (fun f : ℝ[X] => f.coeff 0) hodd
    have htwo := congrArg (fun f : ℝ[X] => f.coeff 2) hodd
    rw [coeff_comp_neg_X, coeff_neg] at hzero htwo
    have hz : q.coeff 0 = 0 := by norm_num at hzero; linarith
    have ht : q.coeff 2 = 0 := by norm_num at htwo; linarith
    refine ⟨q.coeff 1, ?_⟩
    calc
      q = ∑ i ∈ Finset.range 4, C (q.coeff i) * X ^ i := by
        simpa [hdeg] using q.as_sum_range_C_mul_X_pow
      _ = X ^ 3 + C (q.coeff 1) * X := by
        simp [Finset.sum_range_succ, hlead, hz, ht]
        ring

/-- A complex root disk passes from a polynomial to every divisor. -/
theorem root_normSq_le_of_dvd {P Q : ℝ[X]} {radius : ℝ} (hPQ : P ∣ Q)
    (hQ : ∀ c : ℂ, (Q.map (algebraMap ℝ ℂ)).eval c = 0 →
      Complex.normSq c ≤ radius) :
    ∀ c : ℂ, (P.map (algebraMap ℝ ℂ)).eval c = 0 →
      Complex.normSq c ≤ radius := by
  obtain ⟨R, hR⟩ := hPQ
  intro c hc
  apply hQ c
  rw [hR, Polynomial.map_mul, eval_mul, hc, zero_mul]

/-- The disk assumption on a real linear factor gives its scalar bound. -/
theorem real_linear_sq_le_of_disk (a : ℝ)
    (hroot : ∀ c : ℂ,
      (((X - C a : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0) →
        Complex.normSq c ≤ 13 / 3) :
    a ^ 2 ≤ 13 / 3 := by
  have ha := hroot (a : ℂ) (by simp)
  simpa only [Complex.normSq_ofReal, pow_two] using ha

/-- A conjugate-pair factor inherits the squared-radius bound on its parameters. -/
theorem real_pair_sq_le_of_disk (a b : ℝ)
    (hroot : ∀ c : ℂ,
      ((((X - C a) ^ 2 + C (b ^ 2) : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0) →
        Complex.normSq c ≤ 13 / 3) :
    a ^ 2 + b ^ 2 ≤ 13 / 3 := by
  let c : ℂ := ⟨a, b⟩
  have hceq : c = (a : ℂ) + (b : ℂ) * Complex.I := Complex.mk_eq_add_mul_I a b
  have heval :
      (((X - C a) ^ 2 + C (b ^ 2) : ℝ[X]).map (algebraMap ℝ ℂ)).eval c =
        (c - (a : ℂ)) ^ 2 + (b : ℂ) ^ 2 := by
    simp
  have hc : ((((X - C a) ^ 2 + C (b ^ 2) : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0) := by
    rw [heval, hceq]
    calc
      ((a : ℂ) + (b : ℂ) * Complex.I - (a : ℂ)) ^ 2 + (b : ℂ) ^ 2 =
          (b : ℂ) ^ 2 * (Complex.I ^ 2 + 1) := by ring
      _ = 0 := by rw [Complex.I_sq]; ring
  have hb := hroot c hc
  simpa only [c, Complex.normSq_mk, pow_two] using hb

end RealRooted.IntervalDifferential
