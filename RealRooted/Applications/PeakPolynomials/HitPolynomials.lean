import RealRooted.Applications.PeakPolynomials.PeakInduction
import RealRooted.SymmetricDecomposition.FPolynomial

/-!
# A conditional induction step for restricted hit polynomials

This file records the abstract cover-interlacing step behind the restricted hit
polynomials (Section `section:hit`) of

* P. Alexandersson, A. Jal and M. Quemener,
  *Rook-Eulerian polynomials and permutation ideals*.

Their real-rootedness is Conjecture `conj:hit_rr` of the paper, which is open.
Nothing here proves that conjecture: the DU condition and real-rootedness at
the higher levels are explicit hypotheses of every theorem below. They would
come from a row-expansion induction that is not formalized.

The structure parallels the peak recursion: with a cover identity
`H_μ = H_{μ + e_j} + (X - 1) · S_j` and `Q_j = H_{μ + e_j} - S_j`, we have
`H_μ = X · S_j + Q_j` and `H_{μ + e_j} = S_j + Q_j` (compare `W = X D + U` and
`A = D + U`). The DU condition `S_j ≪₀ Q_j`, together with real-rootedness at
the higher level, gives cover interlacing by the shift lemma, and hence
real-rootedness.

## Main results

* `interl_hit_update_succ`: cover interlacing `H_{μ + e_j} ≪₀ H_μ`, conditional
  on the DU condition and higher-level real-rootedness.
* `splits_hit_of_cover_of_du`: the resulting real-rootedness of `H_μ`, under the
  same hypotheses.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.PeakPolynomials

/-- Cover interlacing `H_{μ + e_j} ≪₀ H_μ` for a family `H` of polynomials with
nonnegative coefficients. This is a conditional induction step: we assume
- a cover identity `H_μ = H_{μ + e_j} + (X - 1) · S_j` with `S_j` nonnegative,
- the DU condition `S_j ≪₀ Q_j` for `Q_j = H_{μ + e_j} - S_j`,
- nonnegativity of the coefficients of `Q_j`, and
- real-rootedness of the hit polynomials at the higher level (in the paper's
  setting this would come from induction on `|λ| - |μ|`).

The DU condition is not proved here; Conjecture `conj:hit_rr` remains open. -/
theorem interl_hit_update_succ
    {n : ℕ}
    (H : (Fin n → ℕ) → ℝ[X])
    (H_nn : ∀ μ, HasNonnegCoeffs (H μ))
    (cover : ∀ (μ : Fin n → ℕ) (j : Fin n),
      ∃ Sⱼ : ℝ[X], HasNonnegCoeffs Sⱼ ∧
        H μ = H (Function.update μ j (μ j + 1)) + (X - C 1) * Sⱼ)
    (du : ∀ (μ : Fin n → ℕ) (j : Fin n) (Sⱼ : ℝ[X]),
      HasNonnegCoeffs Sⱼ →
      H μ = H (Function.update μ j (μ j + 1)) + (X - C 1) * Sⱼ →
      Interl Sⱼ (H (Function.update μ j (μ j + 1)) - Sⱼ))
    (Q_nn : ∀ (μ : Fin n → ℕ) (j : Fin n) (Sⱼ : ℝ[X]),
      HasNonnegCoeffs Sⱼ →
      H μ = H (Function.update μ j (μ j + 1)) + (X - C 1) * Sⱼ →
      HasNonnegCoeffs (H (Function.update μ j (μ j + 1)) - Sⱼ))
    (higher_splits : ∀ (μ : Fin n → ℕ) (j : Fin n), (H (Function.update μ j (μ j + 1))).Splits)
    (μ : Fin n → ℕ) (j : Fin n) :
    Interl (H (Function.update μ j (μ j + 1))) (H μ) := by
  obtain ⟨Sⱼ, hSnn, hcov⟩ := cover μ j
  have hDU := du μ j Sⱼ hSnn hcov
  have hQ_nn := Q_nn μ j Sⱼ hSnn hcov
  have hsplits := higher_splits μ j
  -- Self-interlacing of `Sⱼ`
  have hSS : Interl Sⱼ Sⱼ := by
    rcases hDU with hS0 | hQ0 | hstrict
    · rw [hS0]; exact interl_zero_left 0
    · rw [sub_eq_zero.mp hQ0] at hsplits
      exact Interl.refl fun _ => hsplits
    · exact Interl.refl fun _ => hstrict.1.2
  -- Left cone: `Sⱼ ≪₀ Sⱼ + Qⱼ = H_{μ + e_j}`
  have hSH : Interl Sⱼ (H (Function.update μ j (μ j + 1))) := by
    simpa using Interl.sum_left_of_common_left_of_nonneg
      [Sⱼ, H (Function.update μ j (μ j + 1)) - Sⱼ] Sⱼ (by simp [hSS, hDU])
      (by simp [hSnn, hQ_nn])
  -- Boundary: `Sⱼ(0) ≤ H_{μ + e_j}(0)`
  have hbound : Sⱼ.eval 0 ≤ (H (Function.update μ j (μ j + 1))).eval 0 := by
    have h1 : 0 ≤ (H μ).eval 0 := by
      rw [← coeff_zero_eq_eval_zero]
      exact H_nn μ 0
    rw [hcov] at h1
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C] at h1
    linarith
  rw [hcov]
  exact interl_add_X_sub_C_one_mul hSH (H_nn _) hSnn hsplits hbound

/-- Real-rootedness of the hit polynomial `H_μ`, conditional on the same
hypotheses as `interl_hit_update_succ`: the cover identities, the DU condition
`S_j ≪₀ Q_j`, nonnegativity of `Q_j`, and real-rootedness at the higher level.
This is an induction step only; the DU condition is not proved here and
Conjecture `conj:hit_rr` remains open. -/
theorem splits_hit_of_cover_of_du
    {n : ℕ} (hn : n ≠ 0)
    (H : (Fin n → ℕ) → ℝ[X])
    (H_nn : ∀ μ, HasNonnegCoeffs (H μ))
    (cover : ∀ (μ : Fin n → ℕ) (j : Fin n),
      ∃ Sⱼ : ℝ[X], HasNonnegCoeffs Sⱼ ∧
        H μ = H (Function.update μ j (μ j + 1)) + (X - C 1) * Sⱼ)
    (du : ∀ (μ : Fin n → ℕ) (j : Fin n) (Sⱼ : ℝ[X]),
      HasNonnegCoeffs Sⱼ →
      H μ = H (Function.update μ j (μ j + 1)) + (X - C 1) * Sⱼ →
      Interl Sⱼ (H (Function.update μ j (μ j + 1)) - Sⱼ))
    (Q_nn : ∀ (μ : Fin n → ℕ) (j : Fin n) (Sⱼ : ℝ[X]),
      HasNonnegCoeffs Sⱼ →
      H μ = H (Function.update μ j (μ j + 1)) + (X - C 1) * Sⱼ →
      HasNonnegCoeffs (H (Function.update μ j (μ j + 1)) - Sⱼ))
    (higher_splits : ∀ (μ : Fin n → ℕ) (j : Fin n), (H (Function.update μ j (μ j + 1))).Splits)
    (μ : Fin n → ℕ) :
    (H μ).Splits := by
  let j₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  rcases eq_or_ne (H μ) 0 with hH0 | hne
  · rw [hH0]; exact Splits.zero
  rcases interl_hit_update_succ H H_nn cover du Q_nn higher_splits μ j₀ with hH'0 | hH0 | hstrict
  · -- `H_{μ + e_j} = 0` forces `H_μ = (X - 1) · S`, which vanishes at `1`; but a
    -- nonzero polynomial with nonnegative coefficients is positive at `1`.
    obtain ⟨Sⱼ, -, hScov⟩ := cover μ j₀
    have hzero : (H μ).eval 1 = 0 := by
      simp [hScov, hH'0]
    exact absurd hzero (eval_one_pos_of_hasNonnegCoeffs (H_nn μ) hne).ne'
  · exact absurd hH0 hne
  · exact hstrict.2.1.2

end RealRooted.Applications.PeakPolynomials
