module

public import RealRooted.Chebyshev.Levels
public import RealRooted.CombinatorialExamples.EvenBinomPerturbation
public import RealRooted.Transforms.RationalSubstitution
import RealRooted.Transforms.RationalSubstitutionDerivative

/-!
# Chebyshev transport for even-binomial polynomials

The Mobius substitution with numerator `1 + X` and denominator `1 - X`
identifies Chebyshev polynomials with even-binomial polynomials.  We use the
cleared identity to transport the obstruction from shifted Chebyshev
polynomials to sharp coefficient perturbations.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The even-binomial polynomials of even index satisfy the recurrence induced
by the Chebyshev recurrence under the cleared Mobius substitution. -/
private theorem evenBinomPolyReal_two_step (n : ℕ) :
    BigDescents.evenBinomPolyReal (n + 4) =
      C 2 * (1 + X) * BigDescents.evenBinomPolyReal (n + 2) -
        (1 - X) ^ 2 * BigDescents.evenBinomPolyReal n := by
  rw [show n + 4 = (n + 2) + 2 by lia,
    BigDescents.evenBinomPolyReal_recurrence]
  rw [show n + 3 = (n + 1) + 2 by lia,
    BigDescents.evenBinomPolyReal_recurrence]
  rw [BigDescents.evenBinomPolyReal_recurrence n]
  simp only [Polynomial.C_ofNat]
  ring_nf

/-- Clearing the Mobius substitution `x = (1 + X) / (1 - X)` sends the
degree-`d` Chebyshev polynomial to the even-binomial polynomial of index `2d`. -/
theorem homogenizedSubstitution_chebyshev_T_eq_evenBinomPolyReal (d : ℕ) :
    homogenizedSubstitution d (1 + X) (1 - X)
        (Polynomial.Chebyshev.T ℝ d) =
      BigDescents.evenBinomPolyReal (2 * d) := by
  induction d using Nat.twoStepInduction with
  | zero =>
      norm_num [Polynomial.Chebyshev.T_zero, homogenizedSubstitution_eq_sum,
        BigDescents.evenBinomPolyReal, Finset.sum_range_succ]
  | one =>
      norm_num [Polynomial.Chebyshev.T_one, homogenizedSubstitution_eq_sum,
        BigDescents.evenBinomPolyReal, Finset.sum_range_succ]
  | more d ih₀ ih₁ =>
      let T₀ := Polynomial.Chebyshev.T ℝ (d : ℤ)
      let T₁ := Polynomial.Chebyshev.T ℝ ((d + 1 : ℕ) : ℤ)
      have hT₀degree : T₀.natDegree = d := by
        dsimp [T₀]
        rw [Polynomial.Chebyshev.natDegree_T]
        simp
      have hT₁degree : T₁.natDegree = d + 1 := by
        dsimp [T₁]
        rw [Polynomial.Chebyshev.natDegree_T]
        rw [show (d : ℤ) + 1 = ((d + 1 : ℕ) : ℤ) by norm_num,
          Int.natAbs_natCast]
      have hrec : Polynomial.Chebyshev.T ℝ ((d + 2 : ℕ) : ℤ) =
          C 2 * (X * T₁) + C (-1) * T₀ := by
        rw [show ((d + 2 : ℕ) : ℤ) = (d : ℤ) + 2 by norm_num]
        rw [Polynomial.Chebyshev.T_add_two]
        dsimp [T₀, T₁]
        simp only [Polynomial.C_ofNat, map_neg, map_one]
        ring_nf
      have hXdegree : (X * T₁).natDegree ≤ d + 2 := by
        calc
          _ ≤ X.natDegree + T₁.natDegree := natDegree_mul_le
          _ = d + 2 := by rw [hT₁degree, natDegree_X]; lia
      have hfirst : homogenizedSubstitution (d + 2) (1 + X) (1 - X)
          (C 2 * (X * T₁)) =
          C 2 * (1 + X) * homogenizedSubstitution (d + 1) (1 + X) (1 - X) T₁ := by
        rw [homogenizedSubstitution_C_mul 2 hXdegree]
        rw [show d + 2 = (d + 1) + 1 by lia,
          homogenizedSubstitution_X_mul hT₁degree.le]
        ring_nf
      have hsecond : homogenizedSubstitution (d + 2) (1 + X) (1 - X)
          (C (-1) * T₀) =
          C (-1) * (1 - X) ^ 2 * homogenizedSubstitution d (1 + X) (1 - X) T₀ := by
        rw [homogenizedSubstitution_C_mul (-1) (hT₀degree.le.trans (by lia))]
        rw [show d + 2 = (d + 1) + 1 by lia,
          homogenizedSubstitution_succ (hT₀degree.le.trans (by lia))]
        rw [homogenizedSubstitution_succ hT₀degree.le]
        ring_nf
      rw [hrec, homogenizedSubstitution_add
        ((natDegree_C_mul_le 2 _).trans hXdegree)
        ((natDegree_C_mul_le (-1) _).trans (hT₀degree.le.trans (by lia)))]
      rw [hfirst, hsecond]
      change _ * homogenizedSubstitution (d + 1) (1 + X) (1 - X)
          (Polynomial.Chebyshev.T ℝ ((d + 1 : ℕ) : ℤ)) +
        _ * homogenizedSubstitution d (1 + X) (1 - X)
          (Polynomial.Chebyshev.T ℝ (d : ℤ)) = _
      rw [ih₀, ih₁]
      rw [show 2 * (d + 2) = 2 * d + 4 by lia,
        evenBinomPolyReal_two_step]
      rw [show (C (-1) : ℝ[X]) = -1 by norm_num]
      ring_nf

/-- The natural-degree cleared Mobius substitution sends a constant shift of
`T d` to the corresponding alternating binomial perturbation. -/
theorem rationalSubstitution_chebyshev_T_add_C_eq_evenBinomPolyReal_add
    (d : ℕ) (c : ℝ) :
    rationalSubstitution (1 + X) (1 - X)
        (Polynomial.Chebyshev.T ℝ d + C c) =
      BigDescents.evenBinomPolyReal (2 * d) + C c * (1 - X) ^ d := by
  have hdegree :
      (Polynomial.Chebyshev.T ℝ d + C c).natDegree = d := by
    simp
  have hconstant : homogenizedSubstitution d (1 + X) (1 - X) (C c) =
      C c * (1 - X) ^ d := by
    simpa using homogenizedSubstitution_C_mul_X_pow
      (N := d) (1 + X) (1 - X) c (Nat.zero_le d)
  rw [rationalSubstitution_eq_sum, hdegree,
    ← homogenizedSubstitution_eq_sum hdegree.le]
  rw [homogenizedSubstitution_add (by simp) (by simp)]
  rw [homogenizedSubstitution_chebyshev_T_eq_evenBinomPolyReal, hconstant]

/-- The denominator `1 - X` in the Mobius substitution is nonzero. -/
private theorem one_sub_X_ne_zero : (1 - X : ℝ[X]) ≠ 0 := by
  intro hzero
  have heval := congrArg (Polynomial.eval (0 : ℝ)) hzero
  norm_num at heval

/-- The numerator and denominator of the Mobius substitution are coprime. -/
private theorem isCoprime_one_add_X_one_sub_X :
    IsCoprime (1 + X : ℝ[X]) (1 - X) := by
  refine ⟨C (1 / 2), C (1 / 2), ?_⟩
  ring_nf
  change C (1 / 2) * C (2 : ℝ) = C 1
  rw [← map_mul]
  norm_num

/-- The quotient `(1 + X) / (1 - X)` is nonconstant. -/
private theorem hasNonconstantRatio_one_add_X_one_sub_X :
    HasNonconstantRatio (1 + X : ℝ[X]) (1 - X) := by
  rw [hasNonconstantRatio_iff]
  intro z hzero
  have heval := congrArg (Polynomial.eval (1 : ℂ)) hzero
  norm_num at heval

/-- An alternating binomial perturbation with multiplier greater than one
does not split in any degree at least two. -/
theorem evenBinomPolyReal_add_C_mul_one_sub_X_pow_not_splits
    {d : ℕ} {c : ℝ} (hd : 2 ≤ d) (hc : 1 < c) :
    ¬(BigDescents.evenBinomPolyReal (2 * d) + C c * (1 - X) ^ d).Splits := by
  let q := Polynomial.Chebyshev.T ℝ d + C c
  have hqNotSplits : ¬q.Splits := by
    exact Chebyshev.not_splits_T_add_C_of_one_lt hd hc
  have hq : q ≠ 0 := by
    intro hzero
    apply hqNotSplits
    rw [hzero]
    exact Splits.zero
  intro hsplit
  apply hqNotSplits
  have htransport := (rationalSubstitution_splits_iff hq one_sub_X_ne_zero
    isCoprime_one_add_X_one_sub_X hasNonconstantRatio_one_add_X_one_sub_X).mp
  apply (htransport ?_).1
  rw [rationalSubstitution_chebyshev_T_add_C_eq_evenBinomPolyReal_add]
  exact hsplit

/-- In every degree at least two, all binomially bounded perturbations are
zero or real-rooted exactly up to the sharp coefficient bound. -/
theorem all_evenBinomPolyReal_add_eq_zero_or_splits_iff_le
    {d : ℕ} {alpha M : ℝ} (hd : 2 ≤ d) (halpha : 0 < alpha) (hM : 0 ≤ M) :
    (∀ h : ℝ[X], h.natDegree ≤ d →
      (∀ k ≤ d, |h.coeff k| ≤ M * d.choose k) →
      C alpha * BigDescents.evenBinomPolyReal (2 * d) + h = 0 ∨
        (C alpha * BigDescents.evenBinomPolyReal (2 * d) + h).Splits) ↔
      M ≤ alpha := by
  constructor
  · intro hall
    by_contra hnot
    have hMalpha : alpha < M := lt_of_not_ge hnot
    let h : ℝ[X] := C M * (1 - X) ^ d
    have hdegree : h.natDegree ≤ d := by
      dsimp [h]
      calc
        _ ≤ ((1 - X : ℝ[X]) ^ d).natDegree := natDegree_C_mul_le M _
        _ ≤ d := by compute_degree
    have hcoeff : ∀ k ≤ d, |h.coeff k| ≤ M * d.choose k := by
      intro k hk
      dsimp [h]
      rw [coeff_C_mul, Polynomial.coeff_one_sub_X_pow]
      simp [abs_mul, abs_of_nonneg hM]
    have hpSplits := (hall h hdegree hcoeff).elim (fun hzero ↦ hzero ▸ Splits.zero) id
    let q : ℝ[X] := BigDescents.evenBinomPolyReal (2 * d) +
      C (M / alpha) * (1 - X) ^ d
    have hc : 1 < M / alpha := (one_lt_div halpha).mpr hMalpha
    have hqNotSplits : ¬q.Splits := by
      exact evenBinomPolyReal_add_C_mul_one_sub_X_pow_not_splits hd hc
    have hq : q ≠ 0 := by
      intro hzero
      apply hqNotSplits
      rw [hzero]
      exact Splits.zero
    have hscalar : alpha * (M / alpha) = M := by
      field_simp
    have hpEq : C alpha * BigDescents.evenBinomPolyReal (2 * d) + h =
        C alpha * q := by
      dsimp [h, q]
      calc
        _ = C alpha * BigDescents.evenBinomPolyReal (2 * d) +
            C (alpha * (M / alpha)) * (1 - X) ^ d := by rw [hscalar]
        _ = _ := by rw [map_mul]; ring_nf
    apply hqNotSplits
    apply hpSplits.of_dvd
    · rw [hpEq]
      exact mul_ne_zero (C_ne_zero.mpr halpha.ne') hq
    · rw [hpEq]
      exact ⟨C alpha, by ring_nf⟩
  · intro hMalpha h hdegree hcoeff
    exact (evenBinomPolyReal_add_isPFPolynomial_of_coeff_bound
      (by lia) halpha hM hMalpha hdegree hcoeff).eq_zero_or_splits

end RealRooted
