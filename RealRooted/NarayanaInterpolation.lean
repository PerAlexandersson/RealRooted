import RealRooted.GammaTransform.Basic
import RealRooted.Hadamard.Grace
import RealRooted.MultiplierSequence.InvPochhammer
import RealRooted.NarayanaTransformation.Coefficients

/-!
# Continuous Narayana interpolation

This file formalizes the elementary coefficient, gamma-expansion, and
real-rootedness results for the continuous Narayana interpolation from
J. Zeng, *Continuous Narayana Interpolations: Hankel Total Positivity and
Log-Convexity Preservation*, arXiv:2610.19548v2.

## Main results

* `RealRooted.narayanaInterpolation_eq_sum_gamma`: the `γ`-expansion (paper (1.3)).
* `RealRooted.narayanaInterpolation_isPF`, `narayanaInterpolation_splits`,
  `narayanaInterpolation_roots_neg`: for `-1 < θ` the polynomials are Pólya-frequency, so all
  zeros are real and negative (paper Corollary 3.5, which assumes `θ ≥ 0`).

The real-rootedness proof writes `P_n` as a positive multiple of the Schur–Szegő composition of
the Jensen polynomial of `1 / (θ + 1)_k` with its reversal.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- The coefficient `N_θ(n,k)` in the continuous Narayana interpolation. -/
def narayanaInterpolationCoeff (θ : ℝ) (n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) * (ascPochhammer ℝ n).eval (θ + 1) /
    ((ascPochhammer ℝ k).eval (θ + 1) *
      (ascPochhammer ℝ (n - k)).eval (θ + 1))

/-- The degree-`n` continuous Narayana interpolation polynomial. -/
noncomputable def narayanaInterpolation (θ : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ range (n + 1), C (narayanaInterpolationCoeff θ n k) * X ^ k

/-- The coefficient of `X ^ k` inside the defining degree range. -/
@[simp]
theorem coeff_narayanaInterpolation_of_le {θ : ℝ} {n k : ℕ} (hk : k ≤ n) :
    (narayanaInterpolation θ n).coeff k = narayanaInterpolationCoeff θ n k := by
  simp [narayanaInterpolation, hk]

/-- Coefficients above the defining degree range vanish. -/
@[simp]
theorem coeff_narayanaInterpolation_of_lt {θ : ℝ} {n k : ℕ} (hk : n < k) :
    (narayanaInterpolation θ n).coeff k = 0 := by
  simp [narayanaInterpolation, hk.not_ge]

private theorem factorial_mul_ring_choose_eq_ascPochhammer (θ : ℝ) (k : ℕ) :
    (k.factorial : ℝ) * Ring.choose (θ + k) k =
      (ascPochhammer ℝ k).eval (θ + 1) := by
  rw [Ring.choose_eq_smul]
  simp only [smul_eq_mul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  congr 2
  ring

private theorem narayanaInterpolationCoeff_eq_choose_ratio
    {θ : ℝ} {n k : ℕ} (hθ : -1 < θ) (hk : k ≤ n) :
    narayanaInterpolationCoeff θ n k =
      (Nat.choose n k : ℝ) * Ring.choose (n + θ) k / Ring.choose (θ + k) k := by
  have hα : 0 < θ + 1 := by linarith
  have hkP : (ascPochhammer ℝ k).eval (θ + 1) ≠ 0 :=
    (ascPochhammer_pos k (θ + 1) hα).ne'
  have hnkP : (ascPochhammer ℝ (n - k)).eval (θ + 1) ≠ 0 :=
    (ascPochhammer_pos (n - k) (θ + 1) hα).ne'
  have hchoose : Ring.choose (θ + k) k ≠ 0 := by
    intro h
    have heq := factorial_mul_ring_choose_eq_ascPochhammer θ k
    rw [h, mul_zero] at heq
    exact hkP heq.symm
  have hsplit := congrArg (eval (θ + 1)) (ascPochhammer_mul ℝ (n - k) k)
  rw [Nat.sub_add_cancel hk, eval_mul, eval_comp, eval_add, eval_X,
    eval_natCast] at hsplit
  have htop : (ascPochhammer ℝ k).eval (θ + 1 + ((n - k : ℕ) : ℝ)) =
      k.factorial * Ring.choose (n + θ) k := by
    rw [show θ + 1 + ((n - k : ℕ) : ℝ) =
      θ + ((n - k : ℕ) : ℝ) + 1 by ring]
    rw [← factorial_mul_ring_choose_eq_ascPochhammer
      (θ + ((n - k : ℕ) : ℝ)) k]
    congr 2
    rw [Nat.cast_sub hk]
    ring
  rw [htop] at hsplit
  have hden := factorial_mul_ring_choose_eq_ascPochhammer θ k
  unfold narayanaInterpolationCoeff
  rw [← hden]
  field_simp [hkP, hnkP, hchoose]
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial hk
  nlinarith

/-- Every coefficient is nonnegative throughout the open range `θ > -1`. -/
theorem narayanaInterpolationCoeff_nonneg {θ : ℝ} (hθ : -1 < θ) (n k : ℕ) :
    0 ≤ narayanaInterpolationCoeff θ n k := by
  unfold narayanaInterpolationCoeff
  have hα : 0 < θ + 1 := by linarith
  exact div_nonneg
    (mul_nonneg (Nat.cast_nonneg' (Nat.choose n k))
      (ascPochhammer_pos n (θ + 1) hα).le)
    (mul_nonneg (ascPochhammer_pos k (θ + 1) hα).le
      (ascPochhammer_pos (n - k) (θ + 1) hα).le)

/-- The continuous Narayana polynomial has nonnegative coefficients for `θ > -1`. -/
theorem narayanaInterpolation_hasNonnegCoeffs {θ : ℝ} (hθ : -1 < θ) (n : ℕ) :
    HasNonnegCoeffs (narayanaInterpolation θ n) := by
  intro k
  by_cases hk : k ≤ n
  · rw [coeff_narayanaInterpolation_of_le hk]
    exact narayanaInterpolationCoeff_nonneg hθ n k
  · rw [coeff_narayanaInterpolation_of_lt (Nat.lt_of_not_ge hk)]

/-- At `θ = 0`, the coefficients are squares of binomial coefficients. -/
theorem narayanaInterpolationCoeff_zero (n k : ℕ) :
    narayanaInterpolationCoeff 0 n k = (Nat.choose n k : ℝ) ^ 2 := by
  by_cases hk : k ≤ n
  · rw [narayanaInterpolationCoeff_eq_choose_ratio (by norm_num) hk]
    norm_num [Ring.choose_natCast, Nat.choose_symm hk, pow_two]
  · have hchoose : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)
    simp [narayanaInterpolationCoeff, hchoose]

/-- The `θ = 0` specialization is the binomial-square polynomial. -/
theorem narayanaInterpolation_zero (n : ℕ) :
    narayanaInterpolation 0 n =
      ∑ k ∈ range (n + 1), C ((Nat.choose n k : ℝ) ^ 2) * X ^ k := by
  simp_rw [narayanaInterpolation, narayanaInterpolationCoeff_zero]

private theorem ring_choose_mul_nat_choose_div
    {θ : ℝ} {k j : ℕ} (hθ : -1 < θ) (hj : j ≤ k) :
    Ring.choose (θ + k) k * (Nat.choose k j : ℝ) / Ring.choose (θ + j) j =
      Ring.choose (θ + k) (k - j) := by
  have hjChoose : Ring.choose (θ + j) j ≠ 0 := by
    intro h
    have heq := factorial_mul_ring_choose_eq_ascPochhammer θ j
    rw [h, mul_zero] at heq
    exact (ascPochhammer_pos j (θ + 1) (by linarith)).ne' heq.symm
  apply (div_eq_iff hjChoose).2
  have hmult : (j.factorial : ℝ) * (k - j).factorial ≠ 0 := by positivity
  apply mul_left_cancel₀ hmult
  have hkChoose := factorial_mul_ring_choose_eq_ascPochhammer θ k
  have hjChooseEq := factorial_mul_ring_choose_eq_ascPochhammer θ j
  have htailChoose :=
    factorial_mul_ring_choose_eq_ascPochhammer (θ + j) (k - j)
  have htopEq : θ + (j : ℝ) + (k - j : ℕ) = θ + k := by
    rw [Nat.cast_sub hj]
    ring
  rw [htopEq] at htailChoose
  have hsplit := congrArg (eval (θ + 1)) (ascPochhammer_mul ℝ j (k - j))
  rw [Nat.add_sub_cancel' hj, eval_mul, eval_comp, eval_add, eval_X,
    eval_natCast] at hsplit
  have hnat : (Nat.choose k j : ℝ) * j.factorial * (k - j).factorial =
      k.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  calc
    (j.factorial : ℝ) * (k - j).factorial *
          (Ring.choose (θ + k) k * (Nat.choose k j : ℝ)) =
        (k.factorial : ℝ) * Ring.choose (θ + k) k := by
          rw [← hnat]
          ring
    _ = (ascPochhammer ℝ k).eval (θ + 1) := hkChoose
    _ = (ascPochhammer ℝ j).eval (θ + 1) *
        (ascPochhammer ℝ (k - j)).eval (θ + 1 + j) := hsplit.symm
    _ = (j.factorial : ℝ) * Ring.choose (θ + j) j *
        ((k - j).factorial * Ring.choose (θ + k) (k - j)) := by
          rw [← hjChooseEq]
          rw [show θ + 1 + (j : ℝ) = θ + j + 1 by ring]
          rw [← htailChoose]
    _ = (j.factorial : ℝ) * (k - j).factorial *
        (Ring.choose (θ + k) (k - j) * Ring.choose (θ + j) j) := by ring

private theorem continuous_vandermonde
    {θ : ℝ} {n k : ℕ} (hθ : -1 < θ) (hk : k ≤ n) :
    ∑ j ∈ range (k + 1),
        (Nat.choose k j : ℝ) * Nat.choose (n - k) j / Ring.choose (θ + j) j =
      Ring.choose (n + θ) k / Ring.choose (θ + k) k := by
  have hkChoose : Ring.choose (θ + k) k ≠ 0 := by
    intro h
    have heq := factorial_mul_ring_choose_eq_ascPochhammer θ k
    rw [h, mul_zero] at heq
    exact (ascPochhammer_pos k (θ + 1) (by linarith)).ne' heq.symm
  apply (eq_div_iff hkChoose).2
  rw [Finset.sum_mul]
  have hv := Ring.add_choose_eq (R := ℝ) k
    (Commute.all ((n - k : ℕ) : ℝ) (θ + k))
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  calc
    ∑ j ∈ range (k + 1),
        ((Nat.choose k j : ℝ) * Nat.choose (n - k) j /
          Ring.choose (θ + j) j) * Ring.choose (θ + k) k =
        ∑ j ∈ range (k + 1),
          Ring.choose ((n - k : ℕ) : ℝ) j *
            Ring.choose (θ + k) (k - j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjk : j ≤ k := by simpa using hj
          rw [Ring.choose_natCast]
          rw [show ((Nat.choose k j : ℝ) * Nat.choose (n - k) j /
              Ring.choose (θ + j) j) * Ring.choose (θ + k) k =
              (Ring.choose (θ + k) k * (Nat.choose k j : ℝ) /
                Ring.choose (θ + j) j) * Nat.choose (n - k) j by ring,
            ring_choose_mul_nat_choose_div hθ hjk]
          ring
    _ = Ring.choose (((n - k : ℕ) : ℝ) + (θ + k)) k := hv.symm
    _ = Ring.choose (n + θ) k := by
      apply congrArg (fun x : ℝ ↦ Ring.choose x k)
      rw [Nat.cast_sub hk]
      ring

private def narayanaInterpolationGammaCoeff (θ : ℝ) (n j : ℕ) : ℝ :=
  ((Nat.choose n j * Nat.choose (n - j) j : ℕ) : ℝ) /
    Ring.choose (θ + j) j

private def narayanaInterpolationGammaPolynomial (θ : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ j ∈ range (n / 2 + 1),
    monomial j (narayanaInterpolationGammaCoeff θ n j)

private theorem coeff_narayanaInterpolationGammaPolynomial (n j : ℕ) (θ : ℝ) :
    (narayanaInterpolationGammaPolynomial θ n).coeff j =
      if j ≤ n / 2 then narayanaInterpolationGammaCoeff θ n j else 0 := by
  simpa only [narayanaInterpolationGammaPolynomial, Nat.lt_succ_iff] using
    Polynomial.coeff_sum_range_monomial
      (narayanaInterpolationGammaCoeff θ n) (n / 2 + 1) j

private theorem gammaTransform_narayanaInterpolationGammaPolynomial
    {θ : ℝ} (hθ : -1 < θ) (n : ℕ) :
    gammaTransform n (narayanaInterpolationGammaPolynomial θ n) =
      narayanaInterpolation θ n := by
  ext k
  by_cases hk : k ≤ n
  · rw [coeff_narayanaInterpolation_of_le hk]
    have hcoeff :
        (gammaTransform n (narayanaInterpolationGammaPolynomial θ n)).coeff k =
          ∑ j ∈ range (n / 2 + 1),
            if j ≤ k then
              narayanaInterpolationGammaCoeff θ n j *
                (Nat.choose (n - 2 * j) (k - j) : ℝ)
            else 0 := by
      rw [gammaTransform, Polynomial.finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro j hj
      have hjhalf : j ≤ n / 2 := by simpa using hj
      rw [coeff_C_mul, coeff_gammaBasisTerm,
        coeff_narayanaInterpolationGammaPolynomial, ite_eq_left hjhalf]
      split_ifs <;> ring
    rw [hcoeff]
    let t (j : ℕ) := narayanaInterpolationGammaCoeff θ n j *
      (Nat.choose (n - 2 * j) (k - j) : ℝ)
    have hrange :
        ∑ j ∈ range (n / 2 + 1), (if j ≤ k then t j else 0) =
          ∑ j ∈ range (k + 1), t j := by
      by_cases hkn : k ≤ n / 2
      · symm
        calc
          ∑ j ∈ range (k + 1), t j =
              ∑ j ∈ range (k + 1), if j ≤ k then t j else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [ite_eq_left (by simpa using hj)]
          _ = ∑ j ∈ range (n / 2 + 1), if j ≤ k then t j else 0 := by
            apply Finset.sum_subset (Finset.range_mono (by lia))
            intro j _ hnot
            have hkj : k < j := by simpa using hnot
            simp [hkj.not_ge]
      · have hhalfk : n / 2 < k := Nat.lt_of_not_ge hkn
        calc
          ∑ j ∈ range (n / 2 + 1), (if j ≤ k then t j else 0) =
              ∑ j ∈ range (n / 2 + 1), t j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [ite_eq_left (by have := Finset.mem_range.mp hj; lia)]
          _ = ∑ j ∈ range (k + 1), t j := by
            apply Finset.sum_subset (Finset.range_mono (by lia))
            intro j _ hnot
            have hchoose : Nat.choose (n - j) j = 0 := by
              apply Nat.choose_eq_zero_of_lt
              have hjhalf : n / 2 < j := by simpa using hnot
              lia
            simp [t, narayanaInterpolationGammaCoeff, hchoose]
    rw [hrange]
    dsimp only [t]
    calc
      ∑ j ∈ range (k + 1),
          narayanaInterpolationGammaCoeff θ n j *
            (Nat.choose (n - 2 * j) (k - j) : ℝ) =
          (Nat.choose n k : ℝ) *
            ∑ j ∈ range (k + 1),
              (Nat.choose k j : ℝ) * Nat.choose (n - k) j /
                Ring.choose (θ + j) j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            have hjk : j ≤ k := by simpa using hj
            have hterm := choose_gamma_term n k j hk hjk
            unfold narayanaInterpolationGammaCoeff
            have htermR :
                (Nat.choose n j : ℝ) * Nat.choose (n - j) j *
                    Nat.choose (n - 2 * j) (k - j) =
                  (Nat.choose n k : ℝ) * Nat.choose k j *
                    Nat.choose (n - k) j := by
              exact_mod_cast hterm
            norm_num only [Nat.cast_mul]
            rw [div_eq_mul_inv]
            linear_combination (Ring.choose (θ + j) j)⁻¹ * htermR
      _ = (Nat.choose n k : ℝ) *
          (Ring.choose (n + θ) k / Ring.choose (θ + k) k) := by
            rw [continuous_vandermonde hθ hk]
      _ = narayanaInterpolationCoeff θ n k := by
        rw [narayanaInterpolationCoeff_eq_choose_ratio hθ hk]
        ring
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [coeff_narayanaInterpolation_of_lt hnk]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt
      (natDegree_gammaTransform_le n (narayanaInterpolationGammaPolynomial θ n)) hnk

private theorem narayanaInterpolationGammaCoeff_eq_factorial
    {θ : ℝ} (hθ : -1 < θ) {n j : ℕ} (hj : 2 * j ≤ n) :
    narayanaInterpolationGammaCoeff θ n j =
      (n.factorial : ℝ) /
        ((j.factorial : ℝ) * (n - 2 * j).factorial *
          (ascPochhammer ℝ j).eval (θ + 1)) := by
  have hα : 0 < θ + 1 := by linarith
  have hjn : j ≤ n := by lia
  have hjrest : j ≤ n - j := by lia
  have hpoch : (ascPochhammer ℝ j).eval (θ + 1) ≠ 0 :=
    (ascPochhammer_pos j (θ + 1) hα).ne'
  have hchoose : Ring.choose (θ + j) j ≠ 0 := by
    intro h
    have heq := factorial_mul_ring_choose_eq_ascPochhammer θ j
    rw [h, mul_zero] at heq
    exact hpoch heq.symm
  have hden := factorial_mul_ring_choose_eq_ascPochhammer θ j
  have hfirst := Nat.choose_mul_factorial_mul_factorial hjn
  have hsecond := Nat.choose_mul_factorial_mul_factorial hjrest
  rw [show n - j - j = n - 2 * j by lia] at hsecond
  have hnat :
      (Nat.choose n j * Nat.choose (n - j) j) *
          (j.factorial * j.factorial * (n - 2 * j).factorial) = n.factorial := by
    calc
      (Nat.choose n j * Nat.choose (n - j) j) *
            (j.factorial * j.factorial * (n - 2 * j).factorial) =
          Nat.choose n j * j.factorial *
            (Nat.choose (n - j) j * j.factorial *
              (n - 2 * j).factorial) := by ring
      _ = Nat.choose n j * j.factorial * (n - j).factorial := by rw [hsecond]
      _ = n.factorial := hfirst
  have hnatR :
      ((Nat.choose n j * Nat.choose (n - j) j : ℕ) : ℝ) *
          ((j.factorial : ℝ) * j.factorial * (n - 2 * j).factorial) =
        n.factorial := by
    exact_mod_cast hnat
  unfold narayanaInterpolationGammaCoeff
  rw [← hden]
  field_simp [hchoose, hpoch]
  simpa [pow_two, mul_assoc] using hnatR

/-- Zeng's gamma expansion for the continuous Narayana interpolation. -/
theorem narayanaInterpolation_eq_sum_gamma {θ : ℝ} (hθ : -1 < θ) (n : ℕ) :
    narayanaInterpolation θ n =
      ∑ j ∈ range (n / 2 + 1),
        C ((n.factorial : ℝ) /
          ((j.factorial : ℝ) * (n - 2 * j).factorial *
            (ascPochhammer ℝ j).eval (θ + 1))) *
          X ^ j * (1 + X) ^ (n - 2 * j) := by
  rw [← gammaTransform_narayanaInterpolationGammaPolynomial hθ n]
  unfold gammaTransform
  apply Finset.sum_congr rfl
  intro j hj
  have hjhalf : j ≤ n / 2 := by simpa using hj
  have hjtwo : 2 * j ≤ n := by lia
  rw [coeff_narayanaInterpolationGammaPolynomial, ite_eq_left hjhalf,
    narayanaInterpolationGammaCoeff_eq_factorial hθ hjtwo]
  simp only [gammaBasisTerm]
  ring

private def invPochhammerJensen (θ : ℝ) (n : ℕ) : ℝ[X] :=
  jensenPolynomial n fun k ↦ ((ascPochhammer ℝ k).eval (θ + 1))⁻¹

private theorem narayanaInterpolation_eq_schurSzego
    {θ : ℝ} (hθ : -1 < θ) (n : ℕ) :
    narayanaInterpolation θ n =
      C ((ascPochhammer ℝ n).eval (θ + 1)) *
        schurSzegoComp n (invPochhammerJensen θ n)
          (Polynomial.reflect n (invPochhammerJensen θ n)) := by
  ext k
  by_cases hk : k ≤ n
  · rw [coeff_narayanaInterpolation_of_le hk, coeff_C_mul,
      coeff_schurSzegoComp_of_le hk, Polynomial.coeff_reflect,
      Polynomial.revAt_le hk]
    simp only [invPochhammerJensen, coeff_jensenPolynomial, ite_eq_left hk]
    rw [ite_eq_left (Nat.sub_le n k), Nat.choose_symm hk]
    have hα : 0 < θ + 1 := by linarith
    have hkP : (ascPochhammer ℝ k).eval (θ + 1) ≠ 0 :=
      (ascPochhammer_pos k (θ + 1) hα).ne'
    have hnkP : (ascPochhammer ℝ (n - k)).eval (θ + 1) ≠ 0 :=
      (ascPochhammer_pos (n - k) (θ + 1) hα).ne'
    have hchoose : (Nat.choose n k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk).ne'
    unfold narayanaInterpolationCoeff
    field_simp
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [coeff_narayanaInterpolation_of_lt hnk, coeff_C_mul,
      coeff_schurSzegoComp_eq_zero_of_lt hnk]
    simp

/-- The constant coefficient is one throughout the open range `θ > -1`. -/
theorem coeff_zero_narayanaInterpolation {θ : ℝ} (hθ : -1 < θ) (n : ℕ) :
    (narayanaInterpolation θ n).coeff 0 = 1 := by
  rw [coeff_narayanaInterpolation_of_le (Nat.zero_le n)]
  have hα : 0 < θ + 1 := by linarith
  have hnP : (ascPochhammer ℝ n).eval (θ + 1) ≠ 0 :=
    (ascPochhammer_pos n (θ + 1) hα).ne'
  simp [narayanaInterpolationCoeff, hnP]

/-- The continuous Narayana polynomial is Pólya-frequency for `θ > -1`. -/
theorem narayanaInterpolation_isPF {θ : ℝ} (hθ : -1 < θ) (n : ℕ) :
    IsPFPolynomial (narayanaInterpolation θ n) := by
  have hα : 0 < θ + 1 := by linarith
  have hJ : IsPFPolynomial (invPochhammerJensen θ n) := by
    unfold invPochhammerJensen
    exact (isPFMultiplierSequence_iff_jensenPolynomial_isPF.mp
      (isPFMultiplierSequence_inv_ascPochhammer hα)) n
  have hJdeg : (invPochhammerJensen θ n).natDegree ≤ n := by
    exact natDegree_jensenPolynomial_le n _
  have href : IsPFPolynomial
      (Polynomial.reflect n (invPochhammerJensen θ n)) :=
    isPFPolynomial_reflect hJ hJdeg
  have hrefdeg :
      (Polynomial.reflect n (invPochhammerJensen θ n)).natDegree ≤ n :=
    Polynomial.natDegree_reflect_le.trans (max_le le_rfl hJdeg)
  have hcomp := hJ.schurSzegoComp href hJdeg hrefdeg
  rw [narayanaInterpolation_eq_schurSzego hθ n]
  exact hcomp.const_mul (ascPochhammer_pos n (θ + 1) hα)

/-- The continuous Narayana polynomial splits over `ℝ` for `θ > -1`. -/
theorem narayanaInterpolation_splits {θ : ℝ} (hθ : -1 < θ) (n : ℕ) :
    (narayanaInterpolation θ n).Splits := by
  refine (narayanaInterpolation_isPF hθ n).eq_zero_or_splits.resolve_left fun hzero ↦ ?_
  have hcoeff := congrArg (fun p : ℝ[X] ↦ p.coeff 0) hzero
  simp [coeff_zero_narayanaInterpolation hθ n] at hcoeff

/-- Every real root of the continuous Narayana polynomial is strictly negative. -/
theorem narayanaInterpolation_roots_neg {θ : ℝ} (hθ : -1 < θ) (n : ℕ) :
    ∀ r ∈ (narayanaInterpolation θ n).roots, r < 0 := by
  intro r hr
  refine lt_of_le_of_ne (roots_nonpos_of_hasNonnegCoeffs
    (narayanaInterpolation_hasNonnegCoeffs hθ n) r hr) fun hrzero ↦ ?_
  have hroot := isRoot_of_mem_roots hr
  subst r
  simp [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero,
    coeff_zero_narayanaInterpolation hθ n] at hroot

/-- The degree-zero continuous Narayana polynomial is one. -/
@[simp] theorem narayanaInterpolation_zero_right (θ : ℝ) :
    narayanaInterpolation θ 0 = 1 := by
  simp [narayanaInterpolation, narayanaInterpolationCoeff]

/-- The degree-one continuous Narayana polynomial is `1 + X`. -/
theorem narayanaInterpolation_one_right {θ : ℝ} (hθ : -1 < θ) :
    narayanaInterpolation θ 1 = 1 + X := by
  rw [narayanaInterpolation_eq_sum_gamma hθ]
  norm_num [Finset.sum_range_succ]

/-- The explicit degree-two continuous Narayana polynomial. -/
theorem narayanaInterpolation_two_right {θ : ℝ} (hθ : -1 < θ) :
    narayanaInterpolation θ 2 =
      1 + C (2 * (θ + 2) / (θ + 1)) * X + X ^ 2 := by
  rw [narayanaInterpolation_eq_sum_gamma hθ]
  have hne : θ + 1 ≠ 0 := by linarith
  norm_num [Finset.sum_range_succ, ascPochhammer]
  have hscalar :
      (2 : ℝ) + 2 / (θ + 1) = 2 * (θ + 2) / (θ + 1) := by
    field_simp
    ring
  calc
    (1 + X) ^ 2 + C (2 / (θ + 1)) * X =
        1 + C (2 + 2 / (θ + 1)) * X + X ^ 2 := by
          rw [map_add, C_ofNat]
          ring
    _ = 1 + C (2 * (θ + 2) / (θ + 1)) * X + X ^ 2 := by rw [hscalar]

end RealRooted
