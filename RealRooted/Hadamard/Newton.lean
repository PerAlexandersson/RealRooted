module

public import RealRooted.Hadamard.Finite
public import RealRooted.Hadamard.Basic
import RealRooted.CoefficientShape
import RealRooted.Linear
import RealRooted.Mathlib.Data.Nat.Choose.Cast

public section

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Normalized coefficient inequalities

Newton inequalities in the level-`n` normalization, normalized log-concavity, and the
degree-two PF Schur--Szego base case.
-/

/-- Newton's first coefficient inequality (`k = 1`) in the level-`n`
normalization, for a splitting polynomial of degree at most `n`: the level-`n`
ultra-log-concavity inequality `coeffUltraLogConcaveUpTo_of_natDegree_le` at `k = 1`. -/
theorem two_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_of_natDegree_le
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) (hs : p.Splits) :
    2 * (n : ℝ) * (p.coeff 0 * p.coeff 2) ≤ ((n : ℝ) - 1) * p.coeff 1 ^ 2 := by
  have h := coeffUltraLogConcaveUpTo_of_natDegree_le hpdeg (Or.inr hs) 1 one_pos (by lia)
  have h1 : ((n - 1 + 1 : ℕ) : ℝ) = n := by rw [Nat.sub_add_cancel (by lia)]
  simp only [h1, Nat.cast_sub (by lia : 1 ≤ n)] at h
  norm_num at h
  linarith

/-- First adjacent normalized log-concavity inequality for a splitting polynomial at
binomial level `n`.

Writing `γ k = p.coeff k / (n.choose k)`, the inequality `γ 0 * γ 2 ≤ γ 1 ^ 2` holds when `p`
splits and has degree at most `n`.  It is the level-`n` Newton inequality at `k = 1`, divided
through by the binomial factors. -/
theorem normalized_coeff_left_logConcave_of_splits_natDegree_le
    {n : ℕ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) (hs : p.Splits) :
    (p.coeff 0 / (n.choose 0 : ℝ)) * (p.coeff 2 / (n.choose 2 : ℝ)) ≤
      (p.coeff 1 / (n.choose 1 : ℝ)) ^ 2 := by
  set N : ℝ := (n : ℝ) with hN_def
  rcases le_or_gt 2 n with h2 | h2
  · have hpd :=
      two_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_of_natDegree_le h2 hpdeg hs
    have hN2 : (2 : ℝ) ≤ N := by rw [hN_def]; exact_mod_cast h2
    have hNpos : (0 : ℝ) < N := by linarith
    have hN1pos : (0 : ℝ) < N - 1 := by linarith
    have hc0 : (n.choose 0 : ℝ) = 1 := by norm_num
    have hc1 : (n.choose 1 : ℝ) = N := by rw [Nat.choose_one_right, hN_def]
    have hc2 : (n.choose 2 : ℝ) = N * (N - 1) / 2 := by rw [Nat.cast_choose_two, hN_def]
    rw [hc0, hc1, hc2]
    have key1 :
        p.coeff 0 / 1 * (p.coeff 2 / (N * (N - 1) / 2))
          = 2 * (p.coeff 0 * p.coeff 2) / (N * (N - 1)) := by
      field_simp
    have key2 : (p.coeff 1 / N) ^ 2 = p.coeff 1 ^ 2 / N ^ 2 := by rw [div_pow]
    rw [key1, key2, div_le_div_iff₀ (mul_pos hNpos hN1pos) (pow_pos hNpos 2)]
    linarith [mul_le_mul_of_nonneg_right hpd hNpos.le, hpd]
  · rw [Nat.choose_eq_zero_of_lt h2, Nat.cast_zero, div_zero, mul_zero]
    positivity

/-- Binomially normalized coefficients of a PF polynomial are nonnegative. -/
theorem normalized_coeff_nonneg_of_isPF (n : ℕ) {f : ℝ[X]}
    (hf : IsPFPolynomial f) :
    ∀ k, 0 ≤ f.coeff k / (Nat.choose n k : ℝ) :=
  fun k =>
    div_nonneg (hf.hasNonnegCoeffs k)
      (by exact_mod_cast Nat.zero_le (Nat.choose n k))

/-- Pure arithmetic core of the Schur--Szego discriminant inequality when only
the PF factor has degree at most two.  Here `a`, `b`, `c` are the coefficients of
the PF factor and `d`, `e`, `g` those of the splitting factor, with the level-`N`
Newton inequality `2 N (d g) ≤ (N - 1) e^2` replacing the quadratic
discriminant of the splitting factor. -/
private theorem schurSzegoComp_pf_disc_arith
    {a b c d e g N : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hfd : 4 * (a * c) ≤ b ^ 2)
    (hpd : 2 * N * (d * g) ≤ (N - 1) * e ^ 2)
    (hN : 2 ≤ N) :
    4 * (a * d * (c * g / (N * (N - 1) / 2))) ≤ (b * e / N) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have hac : 0 ≤ a * c := mul_nonneg ha hc
  have hkey : 4 * (a * d * (c * g / (N * (N - 1) / 2))) =
      8 * (a * c) * (d * g) / (N * (N - 1)) := by
    field_simp
    ring
  rw [hkey, div_pow, div_le_div_iff₀ (mul_pos hNpos hN1) (pow_pos hNpos 2)]
  rcases le_total (d * g) 0 with hdg | hdg
  · linarith [mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hac (sq_nonneg N)) hdg,
      mul_nonneg (sq_nonneg (b * e)) (mul_pos hNpos hN1).le]
  · have hmul : 4 * (a * c) * (2 * N * (d * g)) ≤
        b ^ 2 * ((N - 1) * e ^ 2) :=
      mul_le_mul hfd hpd (by positivity) (sq_nonneg b)
    linarith [mul_le_mul_of_nonneg_right hmul hNpos.le, sq_nonneg (b * e)]

/-- **Schur--Szego discriminant inequality with a degree-`≤ 2` PF factor.**
For a level `n ≥ 2`, a PF factor `f` of degree at most two, and a splitting
factor `p` of arbitrary degree at most `n`, the fixed-degree Schur--Szego
composition satisfies the quadratic discriminant inequality
`4 * coeff 0 * coeff 2 ≤ coeff 1 ^ 2`.

The input for `f` is its degree-`≤ 2` quadratic discriminant inequality
`quadratic_disc_coeff_le_of_splits_natDegree_le_two` (with the nonnegativity of
its coefficients); the input for `p` is the level-`n` Newton inequality
`two_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_of_natDegree_le`. -/
theorem four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp_of_pf
    {n : ℕ} (hn : 2 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    4 * ((schurSzegoComp n f p).coeff 0 * (schurSzegoComp n f p).coeff 2) ≤
      (schurSzegoComp n f p).coeff 1 ^ 2 := by
  have h0n : 0 ≤ n := Nat.zero_le n
  have h1n : 1 ≤ n := le_trans (by norm_num) hn
  have hfd : 4 * (f.coeff 0 * f.coeff 2) ≤ f.coeff 1 ^ 2 := by
    rcases hf.eq_zero_or_splits with h | h
    · simp [h]
    · exact quadratic_disc_coeff_le_of_splits_natDegree_le_two hfdeg h
  have hpd : 2 * (n : ℝ) * (p.coeff 0 * p.coeff 2) ≤
      ((n : ℝ) - 1) * p.coeff 1 ^ 2 :=
    two_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_of_natDegree_le
      hn hpdeg hsplit
  have hf0 : 0 ≤ f.coeff 0 := hf.hasNonnegCoeffs 0
  have hf2 : 0 ≤ f.coeff 2 := hf.hasNonnegCoeffs 2
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [coeff_schurSzegoComp_of_le h0n, coeff_schurSzegoComp_of_le h1n,
    coeff_schurSzegoComp_of_le hn, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.cast_one, div_one, Nat.cast_choose_two]
  exact schurSzegoComp_pf_disc_arith hf0 hf2 hfd hpd hnR

/-- **Fixed-degree Schur--Szego composition with a degree-`≤ 2` PF factor.**

For an arbitrary level `n`, a PF polynomial `f` of degree at most two, and a
splitting polynomial `p` of arbitrary degree at most `n`, the fixed-degree
Schur--Szego composition `schurSzegoComp n f p` is either zero or splits over
`ℝ`.

The composition has degree at most two (it inherits the degree bound of the PF
factor), so it is settled by the quadratic discriminant inequality
`four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp_of_pf`; the
low-level cases (composition of degree at most one) are handled separately.
Unlike `finiteSchurSzegoComposition_of_factors_natDegree_le_two`, here the
splitting factor `p` may have arbitrary degree up to the level `n`. -/
theorem finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  by_cases hq0 : schurSzegoComp n f p = 0
  · exact Or.inl hq0
  by_cases hqle1 : (schurSzegoComp n f p).natDegree ≤ 1
  · exact Or.inr (isRealRooted_of_natDegree_le_one hq0 hqle1).2
  have hqle2 : (schurSzegoComp n f p).natDegree ≤ 2 :=
    le_trans (natDegree_schurSzegoComp_le_left n f p) hfdeg
  have hqdeg : (schurSzegoComp n f p).natDegree = 2 :=
    le_antisymm hqle2 (Nat.succ_le_of_lt (not_le.mp hqle1))
  have hn : 2 ≤ n := hqdeg ▸ natDegree_schurSzegoComp_le n f p
  have hdisc : 0 ≤ (schurSzegoComp n f p).coeff 1 ^ 2 -
      4 * (schurSzegoComp n f p).coeff 2 * (schurSzegoComp n f p).coeff 0 := by
    linarith [four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp_of_pf
      hn hf hfdeg hpdeg hsplit]
  exact Or.inr (splits_of_natDegree_eq_two_of_discrim_nonneg hqdeg (by
    simpa [discrim] using hdisc))
end RealRooted
