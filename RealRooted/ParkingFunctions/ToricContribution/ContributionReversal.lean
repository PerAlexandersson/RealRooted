import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import RealRooted.ParkingFunctions.ToricContribution.CommonInterlacer
import RealRooted.ReciprocalShift.ProperPosition

/-!
# Coefficient reversal for the A390883 toric contributions

This file identifies the coefficient-reversed EHR contribution packets with
the normalized hypergeometric polynomials used by the common-interlacer
theorem.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace ParkingFunctions
namespace ToricContribution

/-- The coefficient of the reversed EHR packet at offset `d`. -/
def reversedContributionCoeff (m ε d k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k *
    ((Nat.choose (m + ε + k) (m - k) * catalan (d + ε + k) : ℕ) : ℝ)

/-- The coefficient-reversed EHR contribution at offset `d`. -/
def reversedContribution (m ε d : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m + 1),
    monomial k (reversedContributionCoeff m ε d k)

@[simp]
theorem coeff_reversedContribution (m ε d k : ℕ) :
    (reversedContribution m ε d).coeff k =
      if k ≤ m then reversedContributionCoeff m ε d k else 0 := by
  simp only [reversedContribution, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (m + 1)) k]
  simp

@[simp]
theorem reversedContributionCoeff_zero (m ε d : ℕ) :
    reversedContributionCoeff m ε d 0 =
      (Nat.choose (m + ε) m * catalan (d + ε) : ℕ) := by
  simp [reversedContributionCoeff]

private theorem choose_offset_succ_mul
    (m ε k : ℕ) (hk : k < m) :
    Nat.choose (m + ε + (k + 1)) (m - (k + 1)) *
        ((ε + 2 * k + 1) * (ε + 2 * k + 2)) =
      Nat.choose (m + ε + k) (m - k) *
        ((m + ε + k + 1) * (m - k)) := by
  let n := m + ε + k
  let r := m - k
  have hr : 0 < r := by
    dsimp only [r]
    lia
  have hrn : r ≤ n := by
    dsimp only [r, n]
    lia
  have hfirst := Nat.choose_succ_right_eq (n + 1) (r - 1)
  have hsecond := Nat.choose_mul_succ_eq n r
  have hrsub : r - 1 + 1 = r := by lia
  have hnsub : n + 1 - (r - 1) = ε + 2 * k + 2 := by
    dsimp only [n, r]
    lia
  have hnsub' : n + 1 - r = ε + 2 * k + 1 := by
    dsimp only [n, r]
    lia
  rw [hrsub] at hfirst
  have hcombine :
      Nat.choose (n + 1) (r - 1) *
          ((n + 1 - r) * (n + 1 - (r - 1))) =
        Nat.choose n r * ((n + 1) * r) := by
    calc
      Nat.choose (n + 1) (r - 1) *
          ((n + 1 - r) * (n + 1 - (r - 1))) =
          (Nat.choose (n + 1) (r - 1) *
            (n + 1 - (r - 1))) * (n + 1 - r) := by ring
      _ = (Nat.choose (n + 1) r * r) * (n + 1 - r) := by
        rw [← hfirst]
      _ = (Nat.choose (n + 1) r * (n + 1 - r)) * r := by ring
      _ = (Nat.choose n r * (n + 1)) * r := by rw [← hsecond]
      _ = Nat.choose n r * ((n + 1) * r) := by ring
  rw [hnsub, hnsub'] at hcombine
  dsimp only [n, r] at hcombine ⊢
  have htop : m + ε + (k + 1) = m + ε + k + 1 := by lia
  rw [htop, show m - (k + 1) = m - k - 1 by lia]
  exact hcombine

/-- The Catalan quotient in successive reversed packet coefficients. -/
private theorem catalan_succ_mul (q : ℕ) :
    (q + 2) * catalan (q + 1) =
      2 * (2 * q + 1) * catalan q := by
  have hzero := succ_mul_catalan_eq_centralBinom q
  have hsucc := succ_mul_catalan_eq_centralBinom (q + 1)
  have hcentral := Nat.succ_mul_centralBinom_succ q
  rw [← hzero, ← hsucc] at hcentral
  rw [show q + 1 + 1 = q + 2 by lia] at hcentral
  have hcentral' :
      (q + 1) * ((q + 2) * catalan (q + 1)) =
        (q + 1) * (2 * (2 * q + 1) * catalan q) := by
    calc
      (q + 1) * ((q + 2) * catalan (q + 1)) =
          2 * (2 * q + 1) * ((q + 1) * catalan q) := hcentral
      _ = (q + 1) * (2 * (2 * q + 1) * catalan q) := by ring
  exact Nat.mul_left_cancel (Nat.succ_pos q) hcentral'

/-- Successive reversed EHR coefficients satisfy the same hypergeometric
recurrence as `rCoeff` when `ε` is a parity bit. -/
theorem reversedContributionCoeff_succ_mul
    (m ε d k : ℕ) (hε : ε ≤ 1) (hk : k < m) :
    ((ε : ℝ) + 1 / 2 + k) * ((ε : ℝ) + d + 2 + k) * (k + 1) *
        reversedContributionCoeff m ε d (k + 1) =
      (-(m : ℝ) + k) * ((m : ℝ) + 1 + ε + k) *
        ((ε : ℝ) + 1 / 2 + d + k) *
          reversedContributionCoeff m ε d k := by
  have hchoose := choose_offset_succ_mul m ε k hk
  have hcatalan := catalan_succ_mul (d + ε + k)
  have hchooseR :
      (Nat.choose (m + ε + (k + 1)) (m - (k + 1)) : ℝ) *
          ((ε + 2 * k + 1) * (ε + 2 * k + 2) : ℕ) =
        (Nat.choose (m + ε + k) (m - k) : ℝ) *
          ((m + ε + k + 1) * (m - k) : ℕ) := by
    exact_mod_cast hchoose
  have hcatalanR :
      ((d + ε + k + 2 : ℕ) : ℝ) * catalan (d + ε + k + 1) =
        2 * ((2 * (d + ε + k) + 1 : ℕ) : ℝ) *
          catalan (d + ε + k) := by
    exact_mod_cast hcatalan
  dsimp only [reversedContributionCoeff]
  push_cast at hchooseR hcatalanR ⊢
  have hproduct := congrArg₂ (· * ·) hchooseR hcatalanR
  have hsub : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by
    rw [Nat.cast_sub (Nat.le_of_lt hk)]
  rw [hsub] at hproduct
  rcases Nat.eq_zero_or_pos ε with rfl | hεpos
  · simp only [Nat.cast_zero, zero_add] at hchooseR hcatalanR ⊢
    rw [pow_succ]
    ring_nf at hproduct ⊢
    linear_combination (-((-1 : ℝ) ^ k) / 4) * hproduct
  · have hεone : ε = 1 := by lia
    subst ε
    norm_num only [Nat.cast_one] at hchooseR hcatalanR ⊢
    rw [pow_succ]
    ring_nf at hproduct ⊢
    linear_combination (-((-1 : ℝ) ^ k) / 4) * hproduct

/-- Successive `rCoeff` values in the coefficient normalization used by the
EHR reversal. -/
theorem rCoeff_succ_mul (m ε d k : ℕ) :
    ((ε : ℝ) + 1 / 2 + k) * ((ε : ℝ) + d + 2 + k) * (k + 1) *
        rCoeff m ε d (k + 1) =
      (-(m : ℝ) + k) * ((m : ℝ) + 1 + ε + k) *
        ((ε : ℝ) + 1 / 2 + d + k) * rCoeff m ε d k := by
  simp only [rCoeff]
  rw [realRisingFactorial_succ, realRisingFactorial_succ,
    realRisingFactorial_succ, realRisingFactorial_succ,
    realRisingFactorial_succ, Nat.factorial_succ]
  have h₁ : 0 < realRisingFactorial ((ε : ℝ) + 1 / 2) k := by
    apply realRisingFactorial_pos
    positivity
  have h₂ : 0 < realRisingFactorial ((ε : ℝ) + 1 / 2 + d + 3 / 2) k := by
    apply realRisingFactorial_pos
    positivity
  have hkfac : 0 < (k.factorial : ℝ) := by positivity
  have hksucc : 0 < (k : ℝ) + 1 := by positivity
  push_cast
  field_simp [h₁.ne', h₂.ne', hkfac.ne', hksucc.ne']
  ring

theorem catalan_pos (n : ℕ) : 0 < catalan n := by
  have hproduct : 0 < (n + 1) * catalan n := by
    rw [succ_mul_catalan_eq_centralBinom]
    exact Nat.centralBinom_pos n
  exact pos_of_mul_pos_right hproduct (Nat.zero_le _)

/-- The reversed EHR coefficient is its positive constant term times the
normalized hypergeometric coefficient. -/
theorem reversedContributionCoeff_eq_mul_rCoeff
    (m ε d k : ℕ) (hε : ε ≤ 1) (hk : k ≤ m) :
    reversedContributionCoeff m ε d k =
      ((Nat.choose (m + ε) m * catalan (d + ε) : ℕ) : ℝ) *
        rCoeff m ε d k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt : k < m := by lia
      have hkle : k ≤ m := Nat.le_of_lt hklt
      let a : ℝ :=
        ((ε : ℝ) + 1 / 2 + k) * ((ε : ℝ) + d + 2 + k) * (k + 1)
      let b : ℝ :=
        (-(m : ℝ) + k) * ((m : ℝ) + 1 + ε + k) *
          ((ε : ℝ) + 1 / 2 + d + k)
      let scale : ℝ :=
        ((Nat.choose (m + ε) m * catalan (d + ε) : ℕ) : ℝ)
      have ha : a ≠ 0 := by
        dsimp only [a]
        positivity
      have hleft :
          a * reversedContributionCoeff m ε d (k + 1) =
            b * reversedContributionCoeff m ε d k := by
        exact reversedContributionCoeff_succ_mul m ε d k hε hklt
      have hright :
          a * rCoeff m ε d (k + 1) = b * rCoeff m ε d k := by
        exact rCoeff_succ_mul m ε d k
      apply mul_left_cancel₀ ha
      calc
        a * reversedContributionCoeff m ε d (k + 1) =
            b * reversedContributionCoeff m ε d k := hleft
        _ = b * (scale * rCoeff m ε d k) := by
          rw [ih hkle]
        _ = scale * (b * rCoeff m ε d k) := by ring
        _ = scale * (a * rCoeff m ε d (k + 1)) := by rw [← hright]
        _ = a * (scale * rCoeff m ε d (k + 1)) := by ring

/-- Exact coefficient-reversal normalization of an EHR contribution packet. -/
theorem reversedContribution_eq_C_mul_rPolynomial
    (m ε d : ℕ) (hε : ε ≤ 1) :
    reversedContribution m ε d =
      C ((Nat.choose (m + ε) m * catalan (d + ε) : ℕ) : ℝ) *
        rPolynomial m ε d := by
  ext k
  rw [coeff_reversedContribution, coeff_C_mul, coeff_rPolynomial]
  by_cases hk : k ≤ m
  · rw [if_pos hk, if_pos hk,
      reversedContributionCoeff_eq_mul_rCoeff m ε d k hε hk]
  · rw [if_neg hk, if_neg hk, mul_zero]

theorem reversedContribution_scale_pos (m ε d : ℕ) :
    0 < ((Nat.choose (m + ε) m * catalan (d + ε) : ℕ) : ℝ) := by
  exact_mod_cast Nat.mul_pos (Nat.choose_pos (by lia)) (catalan_pos (d + ε))

/-- Every parity-normalized reversed contribution has positive leading
coefficient. -/
theorem normalizedReversedContribution_hasPosLeadingCoeff
    (m ε d : ℕ) (hε : ε ≤ 1) :
    HasPosLeadingCoeff
      (C ((-1 : ℝ) ^ m) * reversedContribution m ε d) := by
  rw [reversedContribution_eq_C_mul_rPolynomial m ε d hε]
  have h := hasPosLeadingCoeff_C_mul
    (reversedContribution_scale_pos m ε d)
    (normalizedRPolynomial_hasPosLeadingCoeff m ε d)
  convert h using 1
  simp only [normalizedRPolynomial]
  ring

/-- A parity-normalized reversed EHR contribution. -/
def normalizedReversedContribution (m ε d : ℕ) : ℝ[X] :=
  C ((-1 : ℝ) ^ m) * reversedContribution m ε d

/-- A normalized reversed EHR contribution is a positive scalar multiple of
the corresponding normalized hypergeometric polynomial. -/
theorem normalizedReversedContribution_eq_C_mul_normalizedRPolynomial
    (m ε d : ℕ) (hε : ε ≤ 1) :
    normalizedReversedContribution m ε d =
      C ((Nat.choose (m + ε) m * catalan (d + ε) : ℕ) : ℝ) *
        normalizedRPolynomial m ε d := by
  rw [normalizedReversedContribution,
    reversedContribution_eq_C_mul_rPolynomial m ε d hε]
  simp only [normalizedRPolynomial]
  ring

/-- The concrete reversed EHR contributions inherit the fixed-row proper
position orientation. -/
theorem normalizedReversedContribution_prec_of_lt
    (m ε d e : ℕ) (hm : 0 < m) (hε : ε ≤ 1)
    (hde : d < e) (he : e ≤ m) :
    Prec (normalizedReversedContribution m ε e)
      (normalizedReversedContribution m ε d) := by
  rw [normalizedReversedContribution_eq_C_mul_normalizedRPolynomial m ε e hε,
    normalizedReversedContribution_eq_C_mul_normalizedRPolynomial m ε d hε]
  exact prec_C_mul_right
    (prec_C_mul_left
      (normalizedRPolynomial_prec_of_lt m ε d e hm hde he)
      (reversedContribution_scale_pos m ε e).ne')
    (reversedContribution_scale_pos m ε d).ne'

/-! ## The original toric contribution polynomials -/

/-- The coefficient of `y^k` in
`g_(2m+ε,m-d)(1+y)`. -/
def shiftedToricContributionCoeff (m ε d k : ℕ) : ℝ :=
  ((Nat.choose (2 * m + ε - k) k * catalan (m + ε + d - k) : ℕ) : ℝ)

/-- The toric contribution in the shifted variable `y = x - 1`. -/
def shiftedToricContribution (m ε d : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m + 1),
    monomial k (shiftedToricContributionCoeff m ε d k)

@[simp]
theorem coeff_shiftedToricContribution (m ε d k : ℕ) :
    (shiftedToricContribution m ε d).coeff k =
      if k ≤ m then shiftedToricContributionCoeff m ε d k else 0 := by
  simp only [shiftedToricContribution, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (m + 1)) k]
  simp

theorem shiftedToricContribution_hasNonnegCoeffs (m ε d : ℕ) :
    HasNonnegCoeffs (shiftedToricContribution m ε d) := by
  intro k
  rw [coeff_shiftedToricContribution]
  split
  · simp only [shiftedToricContributionCoeff]
    positivity
  · exact le_rfl

theorem natDegree_shiftedToricContribution_le (m ε d : ℕ) :
    (shiftedToricContribution m ε d).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_shiftedToricContribution, if_neg (by lia)]

/-- Reversing the shifted toric contribution gives the concrete normalized
reciprocal contribution. -/
theorem reciprocalShift_shiftedToricContribution
    (m ε d : ℕ) :
    reciprocalShift m (shiftedToricContribution m ε d) =
      C ((-1 : ℝ) ^ m) *
        (normalizedReversedContribution m ε d).comp (-X) := by
  ext k
  have hneg : (-X : ℝ[X]) = C (-1 : ℝ) * X := by simp
  rw [coeff_reciprocalShift, coeff_C_mul, hneg,
    Polynomial.comp_C_mul_X_coeff]
  simp only [normalizedReversedContribution, coeff_C_mul,
    coeff_reversedContribution]
  by_cases hk : k ≤ m
  · rw [Polynomial.revAt_le hk, coeff_shiftedToricContribution,
      if_pos (Nat.sub_le m k), if_pos hk]
    simp only [shiftedToricContributionCoeff, reversedContributionCoeff]
    have hchoose : 2 * m + ε - (m - k) = m + ε + k := by lia
    have hcatalan : m + ε + d - (m - k) = d + ε + k := by lia
    rw [hchoose, hcatalan]
    ring_nf
    rw [(show Even (m * 2) from ⟨m, by lia⟩).neg_one_pow,
      (show Even (k * 2) from ⟨k, by lia⟩).neg_one_pow]
    ring
  · have hmk : m < k := Nat.lt_of_not_ge hk
    rw [Polynomial.revAt_eq_self_of_lt hmk,
      coeff_shiftedToricContribution, if_neg hk, if_neg hk]
    simp

theorem normalizedReversedContribution_natDegree
    (m ε d : ℕ) (hε : ε ≤ 1) :
    (normalizedReversedContribution m ε d).natDegree = m := by
  rw [normalizedReversedContribution_eq_C_mul_normalizedRPolynomial m ε d hε,
    Polynomial.natDegree_C_mul (reversedContribution_scale_pos m ε d).ne']
  simp only [normalizedRPolynomial]
  rw [Polynomial.natDegree_C_mul (pow_ne_zero m (by norm_num)),
    rPolynomial_natDegree]

/-- The EHR toric contribution `g_(2m+ε,m-d)(x)`. -/
def toricContribution (m ε d : ℕ) : ℝ[X] :=
  (shiftedToricContribution m ε d).comp (X - 1)

theorem toricContribution_eq_sum (m ε d : ℕ) :
    toricContribution m ε d =
      ∑ k ∈ Finset.range (m + 1),
        C (shiftedToricContributionCoeff m ε d k) * (X - 1) ^ k := by
  simp [toricContribution, shiftedToricContribution, Polynomial.monomial_comp]

/-- Larger reverse offsets precede smaller reverse offsets for the original
toric contribution polynomials. -/
theorem toricContribution_prec_of_lt
    (m ε d e : ℕ) (hm : 0 < m) (hε : ε ≤ 1)
    (hde : d < e) (he : e ≤ m) :
    Prec (toricContribution m ε e) (toricContribution m ε d) := by
  have hrev := normalizedReversedContribution_prec_of_lt
    m ε d e hm hε hde he
  have hdegree :
      (normalizedReversedContribution m ε e).natDegree =
        (normalizedReversedContribution m ε d).natDegree := by
    rw [normalizedReversedContribution_natDegree m ε e hε,
      normalizedReversedContribution_natDegree m ε d hε]
  have hreflected := prec_comp_neg_X_of_sameDegree hrev hdegree
  have hsign : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  have hreciprocal :
      Prec (reciprocalShift m (shiftedToricContribution m ε d))
        (reciprocalShift m (shiftedToricContribution m ε e)) := by
    rw [reciprocalShift_shiftedToricContribution,
      reciprocalShift_shiftedToricContribution]
    exact prec_C_mul_right (prec_C_mul_left hreflected hsign) hsign
  have hdPF : IsPFPolynomial
      (reciprocalShift m (shiftedToricContribution m ε d)) :=
    IsPFPolynomial.of_realRooted_nonneg
      (shiftedToricContribution_hasNonnegCoeffs m ε d).reciprocalShift
      hreciprocal.1.2
  have hePF : IsPFPolynomial
      (reciprocalShift m (shiftedToricContribution m ε e)) :=
    IsPFPolynomial.of_realRooted_nonneg
      (shiftedToricContribution_hasNonnegCoeffs m ε e).reciprocalShift
      hreciprocal.2.1.2
  have hdDegree :
      (reciprocalShift m (shiftedToricContribution m ε d)).natDegree ≤ m := by
    exact Polynomial.natDegree_reflect_le.trans (max_le le_rfl
      (natDegree_shiftedToricContribution_le m ε d))
  have heDegree :
      (reciprocalShift m (shiftedToricContribution m ε e)).natDegree ≤ m := by
    exact Polynomial.natDegree_reflect_le.trans (max_le le_rfl
      (natDegree_shiftedToricContribution_le m ε e))
  have hshifted := reciprocalShift_reverses_prec
    hdPF hePF hdDegree heDegree hreciprocal
  have hshifted' :
      Prec (shiftedToricContribution m ε e)
        (shiftedToricContribution m ε d) := by
    simpa [reciprocalShift] using hshifted
  simpa [toricContribution, sub_eq_add_neg] using
    prec_comp_X_add_C hshifted' (-1)

/-- The fixed row `(g_(n,0), ..., g_(n,floor (n/2)))`, parametrized by
`n = 2m+ε`. -/
def toricContributionRow (m ε : ℕ) : List ℝ[X] :=
  (List.range (m + 1)).map fun j => toricContribution m ε (m - j)

@[simp]
theorem length_toricContributionRow (m ε : ℕ) :
    (toricContributionRow m ε).length = m + 1 := by
  simp [toricContributionRow]

/-- The fixed row of toric contributions is an oriented all-pairs
interlacing sequence. This is Xiao's Conjecture 4.2. -/
theorem toricContributionRow_isInterlacingSeq
    (m ε : ℕ) (hε : ε ≤ 1) :
    IsInterlacingSeq (toricContributionRow m ε) := by
  apply isInterlacingSeq_reverseOffsetRow
  intro d e hde he
  exact toricContribution_prec_of_lt m ε d e (by lia) hε hde he

/-- The normalized reversed contributions with a scalar weight at each
offset. -/
def weightedNormalizedReversedContributionFamily
    (m ε : ℕ) (w : ℕ → ℝ) : List ℝ[X] :=
  (Finset.range (m + 1)).toList.map fun d =>
    C (w d) * (C ((-1 : ℝ) ^ m) * reversedContribution m ε d)

theorem weightedNormalizedReversedContributionFamily_eq
    (m ε : ℕ) (hε : ε ≤ 1) (w : ℕ → ℝ) :
    weightedNormalizedReversedContributionFamily m ε w =
      weightedNormalizedRPolynomialFamily m ε fun d =>
        w d *
          ((Nat.choose (m + ε) m * catalan (d + ε) : ℕ) : ℝ) := by
  simp only [weightedNormalizedReversedContributionFamily,
    weightedNormalizedRPolynomialFamily]
  apply List.map_congr_left
  intro d _
  rw [reversedContribution_eq_C_mul_rPolynomial m ε d hε]
  simp only [normalizedRPolynomial]
  calc
    C (w d) * (C ((-1 : ℝ) ^ m) *
          (C ((Nat.choose (m + ε) m * catalan (d + ε) : ℕ) : ℝ) *
            rPolynomial m ε d)) =
        (C (w d) *
          C ((Nat.choose (m + ε) m * catalan (d + ε) : ℕ) : ℝ)) *
          (C ((-1 : ℝ) ^ m) * rPolynomial m ε d) := by ring
    _ = C (w d *
          ((Nat.choose (m + ε) m * catalan (d + ε) : ℕ) : ℝ)) *
        (C ((-1 : ℝ) ^ m) * rPolynomial m ε d) := by rw [C_mul]

/-- Every strictly positive weighted sum of normalized reversed EHR
contributions is split. -/
theorem weightedNormalizedReversedContributionFamily_sum_splits
    (m ε : ℕ) (hm : 0 < m) (hε : ε ≤ 1) (w : ℕ → ℝ)
    (hw : ∀ d, d ≤ m → 0 < w d) :
    (weightedNormalizedReversedContributionFamily m ε w).sum.Splits := by
  rw [weightedNormalizedReversedContributionFamily_eq m ε hε w]
  apply normalizedRPolynomialFamily_weighted_sum_splits m ε hm
  intro d hd
  exact mul_pos (hw d hd) (reversedContribution_scale_pos m ε d)

end ToricContribution
end ParkingFunctions
end RealRooted
