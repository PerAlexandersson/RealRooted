import RealRooted.BinaryRunTransformation.Contraction
import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization.Derivative
import RealRooted.BorceaBranden.Applications.HomogenizeStable
import RealRooted.PFPolynomial

/-!
# The binary-run pointing pencil

This file constructs the homogenized source used in the binary-run pointing
argument.  Its variables are the retained pair `(Z, W)` followed by the two
contracted source variables `(S, T)`.
-/

open Polynomial

namespace RealRooted

noncomputable section

open BorceaBranden

/-- The homogenized source
`(Z + T)^(n+1) p(t (Z + S) / (Z + T))`, expressed without division. -/
def binaryRunHomogenizedSource (n : ℕ) (p : ℝ[X]) (t : ℝ) :
    MvPolynomial (Fin 2 ⊕ Fin 2) ℂ :=
  MvPolynomial.aeval ![
      MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0),
      MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1)]
    (complexifyMv ((scalePolynomial t p).homogenize (n + 1)))

/-- The source after differentiating in `S` and adjoining the pointing factor
`S + W`. -/
def binaryRunPointingSource (n : ℕ) (p : ℝ[X]) (t : ℝ) :
    MvPolynomial (Fin 2 ⊕ Fin 2) ℂ :=
  (MvPolynomial.X (Sum.inr 0) + MvPolynomial.X (Sum.inl 1)) *
    MvPolynomial.pderiv (Sum.inr 0) (binaryRunHomogenizedSource n p t)

/-- Output exponent supported only in the retained `Z` coordinate. -/
def binaryRunOutputIndex (k : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 k

/-- Fully expanded monomial form of the homogenized source. -/
def binaryRunExpandedSource (n : ℕ) (p : ℝ[X]) (t : ℝ) :
    MvPolynomial (Fin 2 ⊕ Fin 2) ℂ :=
  ∑ m ∈ Finset.range (n + 2),
    ∑ a ∈ Finset.range (m + 1),
      ∑ b ∈ Finset.range (n + 2 - m),
        MvPolynomial.monomial
          ((binaryRunOutputIndex (n + 1 - a - b)).sumElim
            (binaryRunSourceIndex a b))
          ((scalePolynomial t p).coeff m * Nat.choose m a *
            Nat.choose (n + 1 - m) b)

private theorem binaryRun_expanded_monomial
    (n m a b : ℕ) (hm : m ≤ n + 1) (ha : a ≤ m)
    (hb : b ≤ n + 1 - m) (c : ℂ) :
    MvPolynomial.C (c * Nat.choose m a * Nat.choose (n + 1 - m) b) *
        MvPolynomial.X (Sum.inl 0) ^ (m - a) *
          MvPolynomial.X (Sum.inr 0) ^ a *
            MvPolynomial.X (Sum.inl 0) ^ (n + 1 - m - b) *
              MvPolynomial.X (Sum.inr 1) ^ b =
      MvPolynomial.monomial
        ((binaryRunOutputIndex (n + 1 - a - b)).sumElim
          (binaryRunSourceIndex a b))
        (c * Nat.choose m a * Nat.choose (n + 1 - m) b) := by
  have hindex :
      (0 : (Fin 2 ⊕ Fin 2) →₀ ℕ) +
            Finsupp.single (Sum.inl 0) (m - a) +
          Finsupp.single (Sum.inr 0) a +
        Finsupp.single (Sum.inl 0) (n + 1 - m - b) +
      Finsupp.single (Sum.inr 1) b =
        (binaryRunOutputIndex (n + 1 - a - b)).sumElim
          (binaryRunSourceIndex a b) := by
    ext i
    rcases i with i | i
    · fin_cases i
      · simp [binaryRunOutputIndex]
        lia
      · simp [binaryRunOutputIndex]
    · fin_cases i
      · simp [binaryRunSourceIndex]
      · simp [binaryRunSourceIndex]
  rw [MvPolynomial.C_apply]
  simp only [MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial]
  rw [hindex]
  simp

theorem binaryRunHomogenizedSource_eq_sum (n : ℕ) (p : ℝ[X]) (t : ℝ) :
    binaryRunHomogenizedSource n p t =
      ∑ m ∈ Finset.range (n + 2),
        MvPolynomial.C ((scalePolynomial t p).coeff m : ℂ) *
          (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0)) ^ m *
            (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1)) ^
              (n + 1 - m) := by
  rw [binaryRunHomogenizedSource,
    ← BorceaBranden.homogenizeBivariate_eq_homogenize]
  simp [homogenizeBivariate, complexifyMv]

theorem binaryRunHomogenizedSource_eq_expanded
    (n : ℕ) (p : ℝ[X]) (t : ℝ) :
    binaryRunHomogenizedSource n p t = binaryRunExpandedSource n p t := by
  rw [binaryRunHomogenizedSource_eq_sum, binaryRunExpandedSource]
  apply Finset.sum_congr rfl
  intro m hm
  have hmle : m ≤ n + 1 := by
    simp only [Finset.mem_range] at hm
    lia
  rw [show MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0) =
      (MvPolynomial.X (Sum.inr 0) + MvPolynomial.X (Sum.inl 0) :
        MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) by ring,
    show MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1) =
      (MvPolynomial.X (Sum.inr 1) + MvPolynomial.X (Sum.inl 0) :
        MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) by ring,
    add_pow, add_pow]
  simp only [Finset.mul_sum, Finset.sum_mul]
  have hrange : n + 1 - m + 1 = n + 2 - m := by lia
  rw [hrange]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hale : a ≤ m := by simpa [Finset.mem_range] using ha
  have hble : b ≤ n + 1 - m := by
    simp only [Finset.mem_range] at hb
    lia
  rw [← binaryRun_expanded_monomial n m a b hmle hale hble
    ((scalePolynomial t p).coeff m : ℂ)]
  rw [show (Nat.choose m a : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) =
      MvPolynomial.C (Nat.choose m a : ℂ) by simp,
    show (Nat.choose (n + 1 - m) b : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) =
      MvPolynomial.C (Nat.choose (n + 1 - m) b : ℂ) by simp]
  rw [map_mul, map_mul]
  ring

theorem binaryRunSourceIndex_inj {a b c d : ℕ} :
    binaryRunSourceIndex a b = binaryRunSourceIndex c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    constructor
    · have := DFunLike.congr_fun h 0
      simpa [binaryRunSourceIndex] using this
    · have := DFunLike.congr_fun h 1
      simpa [binaryRunSourceIndex] using this
  · rintro ⟨rfl, rfl⟩
    rfl

theorem sourceCoefficientGeneral_binaryRunHomogenizedSource
    (n : ℕ) (p : ℝ[X]) (t : ℝ) (r : Fin 2 →₀ ℕ) :
    sourceCoefficientGeneral (binaryRunHomogenizedSource n p t) r =
      ∑ m ∈ Finset.range (n + 2),
        ∑ a ∈ Finset.range (m + 1),
          ∑ b ∈ Finset.range (n + 2 - m),
            if r = binaryRunSourceIndex a b then
              MvPolynomial.monomial
                (binaryRunOutputIndex (n + 1 - a - b))
                (((scalePolynomial t p).coeff m : ℂ) * Nat.choose m a *
                  Nat.choose (n + 1 - m) b)
            else 0 := by
  rw [binaryRunHomogenizedSource_eq_expanded, binaryRunExpandedSource]
  simp only [sourceCoefficientGeneral_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact sourceCoefficientGeneral_monomial_sumElim
    (binaryRunOutputIndex (n + 1 - a - b))
    (binaryRunSourceIndex a b) r _

theorem sourceCoefficientGeneral_binaryRunHomogenizedSource_index
    (n : ℕ) (p : ℝ[X]) (t : ℝ) (k l : ℕ) :
    sourceCoefficientGeneral (binaryRunHomogenizedSource n p t)
        (binaryRunSourceIndex k l) =
      ∑ m ∈ Finset.range (n + 2),
        if k ∈ Finset.range (m + 1) then
          if l ∈ Finset.range (n + 2 - m) then
            MvPolynomial.monomial
              (binaryRunOutputIndex (n + 1 - k - l))
              (((scalePolynomial t p).coeff m : ℂ) * Nat.choose m k *
                Nat.choose (n + 1 - m) l)
          else 0
        else 0 := by
  rw [sourceCoefficientGeneral_binaryRunHomogenizedSource]
  apply Finset.sum_congr rfl
  intro m hm
  simp [binaryRunSourceIndex_inj, ite_and]

theorem sourceCoefficientGeneral_binaryRunHomogenizedSource_monomial
    (n : ℕ) (p : ℝ[X]) (t : ℝ) (k l : ℕ) :
    sourceCoefficientGeneral (binaryRunHomogenizedSource n p t)
        (binaryRunSourceIndex k l) =
      MvPolynomial.monomial
        (binaryRunOutputIndex (n + 1 - k - l))
        (∑ m ∈ Finset.range (n + 2),
          ((scalePolynomial t p).coeff m : ℂ) * Nat.choose m k *
            Nat.choose (n + 1 - m) l) := by
  rw [sourceCoefficientGeneral_binaryRunHomogenizedSource_index]
  calc
    _ = ∑ m ∈ Finset.range (n + 2),
          MvPolynomial.monomial
            (binaryRunOutputIndex (n + 1 - k - l))
            (((scalePolynomial t p).coeff m : ℂ) * Nat.choose m k *
              Nat.choose (n + 1 - m) l) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmle : m ≤ n + 1 := by
          simp only [Finset.mem_range] at hm
          lia
        by_cases hkm : k ∈ Finset.range (m + 1)
        · rw [ite_eq_left hkm]
          by_cases hkl : l ∈ Finset.range (n + 2 - m)
          · rw [ite_eq_left hkl]
          · rw [ite_eq_right hkl]
            have hlt : n + 1 - m < l := by
              simp only [Finset.mem_range, not_lt] at hkl
              lia
            rw [Nat.choose_eq_zero_of_lt hlt]
            simp
        · rw [ite_eq_right hkm]
          have hlt : m < k := by
            simp only [Finset.mem_range, not_lt] at hkm
            lia
          rw [Nat.choose_eq_zero_of_lt hlt]
          simp
    _ = _ := by simp

theorem binaryRunHomogenizedSource_diagonal_scalar
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ)
    {k : ℕ} (hk : k ≤ n) :
    (∑ m ∈ Finset.range (n + 2),
        (scalePolynomial t p).coeff m * (Nat.choose m k : ℝ) *
          (Nat.choose (n + 1 - m) k : ℝ)) =
      (Nat.choose n k : ℝ) *
        (shiftedBinaryRunDeformation n p t).coeff k := by
  have hdegree : (scalePolynomial t p).natDegree ≤ n :=
    (natDegree_scalePolynomial_le t p).trans hp
  have htop : (scalePolynomial t p).coeff (n + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by lia)
  rw [Finset.sum_range_succ, htop]
  simp only [zero_mul, add_zero]
  rw [coeff_shiftedBinaryRunDeformation_eq_sum_range hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hchoose : (Nat.choose n k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hk))
  field_simp

theorem sourceCoefficientGeneral_binaryRunHomogenizedSource_diagonal
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ)
    {k : ℕ} (hk : k ≤ n) :
    sourceCoefficientGeneral (binaryRunHomogenizedSource n p t)
        (binaryRunSourceIndex k k) =
      MvPolynomial.C
          ((Nat.choose n k : ℂ) *
            (shiftedBinaryRunDeformation n p t).coeff k) *
        MvPolynomial.X 0 ^ (n + 1 - 2 * k) := by
  rw [sourceCoefficientGeneral_binaryRunHomogenizedSource_monomial]
  have hscalar := congrArg Complex.ofReal
    (binaryRunHomogenizedSource_diagonal_scalar hp t hk)
  push_cast at hscalar
  rw [hscalar]
  rw [MvPolynomial.C_mul_X_pow_eq_monomial]
  have hindex : binaryRunOutputIndex (n + 1 - k - k) =
      Finsupp.single 0 (n + 1 - 2 * k) := by
    ext i
    fin_cases i
    · simp [binaryRunOutputIndex]
      lia
    · simp [binaryRunOutputIndex]
  rw [hindex]

/-- Source-coefficient extraction commutes with a source partial derivative,
with the expected falling-factor multiplier. -/
theorem sourceCoefficientGeneral_pderiv_source
    {σ τ : Type*} (P : MvPolynomial (τ ⊕ σ) ℂ)
    (i : σ) (r : σ →₀ ℕ) :
    sourceCoefficientGeneral (MvPolynomial.pderiv (Sum.inr i) P) r =
      MvPolynomial.C (r i + 1 : ℂ) *
        sourceCoefficientGeneral P (r + Finsupp.single i 1) := by
  classical
  ext u
  rw [coeff_sourceCoefficientGeneral, MvPolynomial.coeff_pderiv,
    MvPolynomial.coeff_C_mul, coeff_sourceCoefficientGeneral]
  have hindex :
      u.sumElim r + Finsupp.single (Sum.inr i) 1 =
        u.sumElim (r + Finsupp.single i 1) := by
    ext j
    rcases j with j | j
    · simp
    · by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
  rw [hindex]
  simp
  ring

/-- Multiplication by a retained variable commutes with source-coefficient
extraction. -/
theorem sourceCoefficientGeneral_output_X_mul
    {σ τ : Type*} (P : MvPolynomial (τ ⊕ σ) ℂ) (j : τ)
    (r : σ →₀ ℕ) :
    sourceCoefficientGeneral (MvPolynomial.X (Sum.inl j) * P) r =
      MvPolynomial.X j * sourceCoefficientGeneral P r := by
  classical
  ext u
  rw [coeff_sourceCoefficientGeneral, MvPolynomial.coeff_X_mul',
    MvPolynomial.coeff_X_mul']
  have hmem : Sum.inl j ∈ (u.sumElim r).support ↔ j ∈ u.support := by
    simp [Finsupp.mem_support_iff]
  rw [if_congr hmem rfl rfl]
  split_ifs with hj
  · rw [coeff_sourceCoefficientGeneral]
    congr 1
    ext i
    rcases i with i | i
    · by_cases hij : i = j <;> simp [hij]
    · simp
  · rfl

/-- The source Euler operator multiplies a source coefficient by the
corresponding exponent. -/
theorem sourceCoefficientGeneral_X_mul_pderiv_source
    {σ τ : Type*} (P : MvPolynomial (τ ⊕ σ) ℂ) (i : σ)
    (r : σ →₀ ℕ) :
    sourceCoefficientGeneral
        (MvPolynomial.X (Sum.inr i) * MvPolynomial.pderiv (Sum.inr i) P) r =
      MvPolynomial.C (r i : ℂ) * sourceCoefficientGeneral P r := by
  classical
  ext u
  rw [coeff_sourceCoefficientGeneral, MvPolynomial.coeff_X_mul']
  by_cases hi : r i = 0
  · have hnotmem : Sum.inr i ∉ (u.sumElim r).support := by
      simp [Finsupp.mem_support_iff, hi]
    rw [ite_eq_right hnotmem]
    simp [hi]
  · have himem : Sum.inr i ∈ (u.sumElim r).support := by
      simp [Finsupp.mem_support_iff, hi]
    rw [ite_eq_left himem, MvPolynomial.coeff_pderiv,
      MvPolynomial.coeff_C_mul, coeff_sourceCoefficientGeneral]
    have hle : Finsupp.single (Sum.inr i) 1 ≤ u.sumElim r := by
      rw [Finsupp.single_le_iff]
      simpa using Nat.one_le_iff_ne_zero.mpr hi
    have hrestore :
        u.sumElim r - Finsupp.single (Sum.inr i) 1 +
            Finsupp.single (Sum.inr i) 1 = u.sumElim r := by
      exact tsub_add_cancel_of_le hle
    rw [hrestore]
    have hcoord :
        (u.sumElim r - Finsupp.single (Sum.inr i) 1 :
          (τ ⊕ σ) →₀ ℕ) (Sum.inr i) + 1 =
          r i := by
      simp
      lia
    have hcoordC :
        ((u.sumElim r - Finsupp.single (Sum.inr i) 1 :
            (τ ⊕ σ) →₀ ℕ) (Sum.inr i) : ℂ) + 1 = (r i : ℂ) := by
      norm_cast
    rw [hcoordC]
    ring

/-- Applying a coordinate Euler operator cannot introduce a new monomial, so
it cannot increase the degree in any coordinate. -/
theorem degreeOf_X_mul_pderiv_le
    {σ : Type*} (P : MvPolynomial σ ℂ) (i j : σ) :
    (MvPolynomial.X i * MvPolynomial.pderiv i P).degreeOf j ≤
      P.degreeOf j := by
  classical
  rw [MvPolynomial.degreeOf_le_iff]
  intro d hd
  apply MvPolynomial.monomial_le_degreeOf j
  rw [MvPolynomial.mem_support_iff] at hd ⊢
  have himem : i ∈ d.support := by
    by_contra hi
    rw [MvPolynomial.coeff_X_mul', ite_eq_right hi] at hd
    exact hd rfl
  rw [MvPolynomial.coeff_X_mul', ite_eq_left himem,
    MvPolynomial.coeff_pderiv] at hd
  have hle : Finsupp.single i 1 ≤ d := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp himem)
  have hrestore : d - Finsupp.single i 1 + Finsupp.single i 1 = d :=
    tsub_add_cancel_of_le hle
  rw [hrestore] at hd
  intro hzero
  simp [hzero] at hd

theorem binaryRunHomogenizedSource_pointing_scalar
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ)
    {k : ℕ} (hk : k ≤ n) :
    (k + 1 : ℝ) *
        (∑ m ∈ Finset.range (n + 2),
          (scalePolynomial t p).coeff m * (Nat.choose m (k + 1) : ℝ) *
            (Nat.choose (n + 1 - m) k : ℝ)) =
      (Nat.choose n k : ℝ) *
        (binaryRunPointingRemainder n p t).coeff k := by
  have hdegree : (scalePolynomial t p).natDegree ≤ n :=
    (natDegree_scalePolynomial_le t p).trans hp
  have htop : (scalePolynomial t p).coeff (n + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by lia)
  rw [Finset.sum_range_succ, htop]
  simp only [zero_mul, add_zero]
  rw [binaryRunPointingRemainder, coeff_sub,
    coeff_shiftedBinaryRunPointing_eq_sum_range hp,
    Polynomial.coeff_X_mul_derivative,
    coeff_shiftedBinaryRunDeformation_eq_sum_range hp,
    Finset.mul_sum, mul_sub]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hchoose : (Nat.choose n k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hk))
  have hbinomial := congrArg (fun x : ℕ => (x : ℝ))
    (Nat.choose_succ_right_eq m k)
  push_cast at hbinomial
  by_cases hkm : k ≤ m
  · rw [Nat.cast_sub hkm] at hbinomial
    field_simp
    linear_combination
      ((scalePolynomial t p).coeff m *
        (Nat.choose (n + 1 - m) k : ℝ)) * hbinomial
  · have hmk : m < k := Nat.lt_of_not_ge hkm
    rw [Nat.choose_eq_zero_of_lt hmk,
      Nat.choose_eq_zero_of_lt (hmk.trans k.lt_succ_self)]
    simp

theorem sourceCoefficientGeneral_pderiv_binaryRunHomogenizedSource_diagonal
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ)
    {k : ℕ} (hk : k ≤ n) :
    sourceCoefficientGeneral
        (MvPolynomial.pderiv (Sum.inr 0)
          (binaryRunHomogenizedSource n p t))
        (binaryRunSourceIndex k k) =
      MvPolynomial.C
          ((Nat.choose n k : ℂ) *
            (binaryRunPointingRemainder n p t).coeff k) *
        MvPolynomial.X 0 ^ (n - 2 * k) := by
  rw [sourceCoefficientGeneral_pderiv_source]
  have hindex : binaryRunSourceIndex k k + Finsupp.single 0 1 =
      binaryRunSourceIndex (k + 1) k := by
    ext i
    fin_cases i <;> simp [binaryRunSourceIndex]
  rw [hindex, sourceCoefficientGeneral_binaryRunHomogenizedSource_monomial]
  have hscalar := congrArg Complex.ofReal
    (binaryRunHomogenizedSource_pointing_scalar hp t hk)
  push_cast at hscalar
  have hsource : (binaryRunSourceIndex k k) 0 = k := by
    simp [binaryRunSourceIndex]
  rw [hsource, MvPolynomial.C_mul_monomial, hscalar]
  rw [MvPolynomial.C_mul_X_pow_eq_monomial]
  have hout : binaryRunOutputIndex (n + 1 - (k + 1) - k) =
      Finsupp.single 0 (n - 2 * k) := by
    ext i
    fin_cases i
    · simp [binaryRunOutputIndex]
      lia
    · simp [binaryRunOutputIndex]
  rw [hout]

/-- On a diagonal source exponent, the two terms of the pointing source are
respectively the source Euler term and multiplication by the retained `W`
variable. -/
theorem sourceCoefficientGeneral_binaryRunPointingSource_diagonal_aux
    (n : ℕ) (p : ℝ[X]) (t : ℝ) (k : ℕ) :
    sourceCoefficientGeneral (binaryRunPointingSource n p t)
        (binaryRunSourceIndex k k) =
      MvPolynomial.C (k : ℂ) *
          sourceCoefficientGeneral (binaryRunHomogenizedSource n p t)
            (binaryRunSourceIndex k k) +
        MvPolynomial.X 1 *
          sourceCoefficientGeneral
            (MvPolynomial.pderiv (Sum.inr 0)
              (binaryRunHomogenizedSource n p t))
            (binaryRunSourceIndex k k) := by
  rw [binaryRunPointingSource, add_mul, sourceCoefficientGeneral_add,
    sourceCoefficientGeneral_X_mul_pderiv_source,
    sourceCoefficientGeneral_output_X_mul]
  simp [binaryRunSourceIndex]

/-- Exact diagonal coefficient of the pointing source.  These are precisely
the coefficients retained by normalized diagonal contraction. -/
theorem sourceCoefficientGeneral_binaryRunPointingSource_diagonal
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ)
    {k : ℕ} (hk : k ≤ n) :
    sourceCoefficientGeneral (binaryRunPointingSource n p t)
        (binaryRunSourceIndex k k) =
      MvPolynomial.C (Nat.choose n k : ℂ) *
        (MvPolynomial.C
              ((k : ℂ) * (shiftedBinaryRunDeformation n p t).coeff k) *
            MvPolynomial.X 0 ^ (n + 1 - 2 * k) +
          MvPolynomial.X 1 *
            MvPolynomial.C ((binaryRunPointingRemainder n p t).coeff k : ℂ) *
              MvPolynomial.X 0 ^ (n - 2 * k)) := by
  rw [sourceCoefficientGeneral_binaryRunPointingSource_diagonal_aux,
    sourceCoefficientGeneral_binaryRunHomogenizedSource_diagonal hp t hk,
    sourceCoefficientGeneral_pderiv_binaryRunHomogenizedSource_diagonal hp t hk]
  simp only [map_mul]
  ring

theorem eval₂_complexify_signedParityLift_eq_sum
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n / 2) :
    (complexify (signedParityLift n p)).eval₂
        (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
        (MvPolynomial.X 0) =
      ∑ k : Fin (n + 1),
        MvPolynomial.C ((-1 : ℂ) ^ (k : ℕ) * p.coeff k) *
          MvPolynomial.X 0 ^ (n - 2 * (k : ℕ)) := by
  rw [signedParityLift_eq_sum_range_succ hp]
  unfold complexify
  rw [Polynomial.map_sum, Polynomial.eval₂_finsetSum,
    ← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_congr
  intro k
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_X]
  simp

theorem eval₂_complexify_neg_signedParityLift_derivative_eq_sum
    {n : ℕ} (hn : 1 ≤ n) (q : ℝ[X])
    (hq : q.derivative.natDegree ≤ (n - 1) / 2) :
    (complexify (-(signedParityLift (n - 1) q.derivative))).eval₂
        (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
        (MvPolynomial.X 0) =
      ∑ k : Fin (n + 1),
        MvPolynomial.C
            ((-1 : ℂ) ^ (k : ℕ) * (k : ℂ) * q.coeff k) *
          MvPolynomial.X 0 ^ (n + 1 - 2 * (k : ℕ)) := by
  have hnsub : n - 1 + 1 = n := by lia
  rw [show complexify (-(signedParityLift (n - 1) q.derivative)) =
      -(complexify (signedParityLift (n - 1) q.derivative)) by
        simp [complexify],
    Polynomial.eval₂_neg,
    eval₂_complexify_signedParityLift_eq_sum hq]
  rw [← Finset.sum_neg_distrib]
  rw [hnsub]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    -(MvPolynomial.C ((-1 : ℂ) ^ k * q.derivative.coeff k) *
      MvPolynomial.X 0 ^ (n - 1 - 2 * k)))]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    MvPolynomial.C ((-1 : ℂ) ^ k * (k : ℂ) * q.coeff k) *
      MvPolynomial.X 0 ^ (n + 1 - 2 * k)), Finset.sum_range_succ']
  norm_num
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  rw [Polynomial.coeff_derivative]
  have hpow : n + 1 - 2 * (k + 1) = n - 1 - 2 * k := by lia
  rw [hpow, pow_succ]
  push_cast
  simp only [map_add, map_mul, map_natCast, map_one]
  ring

/-- The contracted pointing source is the explicit signed diagonal sum before
the two summands are repackaged as signed parity lifts. -/
theorem normalizedDiagonalContraction_binaryRunPointingSource_eq_sum
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ) :
    normalizedDiagonalContraction n (binaryRunPointingSource n p t) =
      ∑ k : Fin (n + 1),
        (MvPolynomial.C
              ((-1 : ℂ) ^ (k : ℕ) * (k : ℂ) *
                (shiftedBinaryRunDeformation n p t).coeff k) *
            MvPolynomial.X 0 ^ (n + 1 - 2 * (k : ℕ)) +
          MvPolynomial.X 1 *
            MvPolynomial.C
              ((-1 : ℂ) ^ (k : ℕ) *
                (binaryRunPointingRemainder n p t).coeff k) *
              MvPolynomial.X 0 ^ (n - 2 * (k : ℕ))) := by
  classical
  rw [normalizedDiagonalContraction_eq_diagonal_sum]
  apply Fintype.sum_congr
  intro k
  have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.isLt
  rw [sourceCoefficientGeneral_binaryRunPointingSource_diagonal hp t hk]
  have hchoose : (Nat.choose n (k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hk)
  rw [← mul_assoc, ← MvPolynomial.C_mul]
  simp [hchoose]
  ring

/-- Normalized diagonal contraction of the stable pointing source is exactly
the bivariate signed-parity pencil used by the critical-value argument. -/
theorem normalizedDiagonalContraction_binaryRunPointingSource
    {n : ℕ} (hn : 1 ≤ n) {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ) :
    normalizedDiagonalContraction n (binaryRunPointingSource n p t) =
      bivariatePencil
        (-(signedParityLift (n - 1)
          (shiftedBinaryRunDeformation n p t).derivative))
        (signedParityLift n (binaryRunPointingRemainder n p t)) := by
  rw [normalizedDiagonalContraction_binaryRunPointingSource_eq_sum hp t]
  unfold bivariatePencil
  rw [eval₂_complexify_neg_signedParityLift_derivative_eq_sum hn
      (shiftedBinaryRunDeformation n p t)
      (natDegree_derivative_shiftedBinaryRunDeformation_le hp t),
    eval₂_complexify_signedParityLift_eq_sum
      (natDegree_binaryRunPointingRemainder_le hp t),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro k
  ring

theorem pderiv_binaryRunHomogenizedSource_eq_sum
    (n : ℕ) (p : ℝ[X]) (t : ℝ) :
    MvPolynomial.pderiv (Sum.inr 0)
        (binaryRunHomogenizedSource n p t) =
      ∑ m ∈ Finset.range (n + 2),
        MvPolynomial.C ((m : ℂ) * (scalePolynomial t p).coeff m) *
          (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0)) ^
              (m - 1) *
            (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1)) ^
              (n + 1 - m) := by
  rw [binaryRunHomogenizedSource_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp
  ring

theorem degreeOf_binaryRunHomogenizedSource_source_zero_le
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ) :
    (binaryRunHomogenizedSource n p t).degreeOf (Sum.inr 0) ≤ n := by
  rw [binaryRunHomogenizedSource_eq_sum]
  refine (MvPolynomial.degreeOf_sum_le (Sum.inr 0) (Finset.range (n + 2))
    (fun m =>
      MvPolynomial.C ((scalePolynomial t p).coeff m : ℂ) *
        (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0)) ^ m *
          (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1)) ^
            (n + 1 - m))).trans ?_
  apply Finset.sup_le
  intro m hm
  by_cases hmn : m ≤ n
  · have hfirst :
        (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0) :
          MvPolynomial (Fin 2 ⊕ Fin 2) ℂ).degreeOf (Sum.inr 0) ≤ 1 :=
      (MvPolynomial.degreeOf_add_le _ _ _).trans (by
        simp [MvPolynomial.degreeOf_X])
    have hsecond :
        (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1) :
          MvPolynomial (Fin 2 ⊕ Fin 2) ℂ).degreeOf (Sum.inr 0) ≤ 0 :=
      (MvPolynomial.degreeOf_add_le _ _ _).trans (by
        simp [MvPolynomial.degreeOf_X])
    calc
      _ ≤
          (MvPolynomial.C ((scalePolynomial t p).coeff m : ℂ) *
            (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0)) ^ m :
              MvPolynomial (Fin 2 ⊕ Fin 2) ℂ).degreeOf (Sum.inr 0) +
            ((MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1)) ^
              (n + 1 - m) : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ).degreeOf
                (Sum.inr 0) := MvPolynomial.degreeOf_mul_le _ _ _
      _ ≤ (0 + m) + 0 := Nat.add_le_add
        ((MvPolynomial.degreeOf_mul_le _ _ _).trans <|
          Nat.add_le_add (by simp)
            ((MvPolynomial.degreeOf_pow_le _ _ _).trans <| by
              simpa using Nat.mul_le_mul_left m hfirst))
        ((MvPolynomial.degreeOf_pow_le _ _ _).trans <| by
          simpa using Nat.mul_le_mul_left (n + 1 - m) hsecond)
      _ ≤ n := by simpa using hmn
  · have hmTop : m = n + 1 := by
      simp only [Finset.mem_range] at hm
      lia
    subst m
    have hdegree : (scalePolynomial t p).natDegree ≤ n :=
      (natDegree_scalePolynomial_le t p).trans hp
    have hcoeff : (scalePolynomial t p).coeff (n + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by lia)
    simp [hcoeff]

theorem degreeOf_pderiv_binaryRunHomogenizedSource_source_one_le
    (n : ℕ) (p : ℝ[X]) (t : ℝ) :
    (MvPolynomial.pderiv (Sum.inr 0)
      (binaryRunHomogenizedSource n p t)).degreeOf (Sum.inr 1) ≤ n := by
  rw [pderiv_binaryRunHomogenizedSource_eq_sum]
  refine (MvPolynomial.degreeOf_sum_le (Sum.inr 1) (Finset.range (n + 2))
    (fun m =>
      MvPolynomial.C ((m : ℂ) * (scalePolynomial t p).coeff m) *
        (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0)) ^ (m - 1) *
          (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1)) ^
            (n + 1 - m))).trans ?_
  apply Finset.sup_le
  intro m _hm
  by_cases hm0 : m = 0
  · subst m
    simp
  · let A : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ :=
      MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0)
    let B : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ :=
      MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1)
    change (MvPolynomial.C
        ((m : ℂ) * (scalePolynomial t p).coeff m) * A ^ (m - 1) *
          B ^ (n + 1 - m)).degreeOf (Sum.inr 1) ≤ n
    have hfirst : A.degreeOf (Sum.inr 1) ≤ 0 :=
      (MvPolynomial.degreeOf_add_le _ _ _).trans (by
        simp [MvPolynomial.degreeOf_X])
    have hsecond : B.degreeOf (Sum.inr 1) ≤ 1 :=
      (MvPolynomial.degreeOf_add_le _ _ _).trans (by
        simp [MvPolynomial.degreeOf_X])
    have hconst :
        (MvPolynomial.C ((m : ℂ) * (scalePolynomial t p).coeff m) :
          MvPolynomial (Fin 2 ⊕ Fin 2) ℂ).degreeOf (Sum.inr 1) ≤ 0 := by
      exact le_of_eq (MvPolynomial.degreeOf_C _ _)
    have hfirstPow : (A ^ (m - 1)).degreeOf (Sum.inr 1) ≤ 0 :=
      (MvPolynomial.degreeOf_pow_le _ _ _).trans <| by
        simpa using Nat.mul_le_mul_left (m - 1) hfirst
    have hsecondPow : (B ^ (n + 1 - m)).degreeOf (Sum.inr 1) ≤
        n + 1 - m :=
      (MvPolynomial.degreeOf_pow_le _ _ _).trans <| by
        simpa using Nat.mul_le_mul_left (n + 1 - m) hsecond
    calc
      _ ≤ (MvPolynomial.C
          ((m : ℂ) * (scalePolynomial t p).coeff m) *
            A ^ (m - 1)).degreeOf (Sum.inr 1) +
          (B ^ (n + 1 - m)).degreeOf (Sum.inr 1) :=
        MvPolynomial.degreeOf_mul_le _ _ _
      _ ≤ (0 + 0) + (n + 1 - m) := Nat.add_le_add
        ((MvPolynomial.degreeOf_mul_le _ _ _).trans <|
          Nat.add_le_add hconst hfirstPow)
        hsecondPow
      _ ≤ n := by
        have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        lia

/-- Both contracted source variables of the pointing source lie in the
degree-`n` box required by normalized diagonal contraction. -/
theorem degreeOf_binaryRunPointingSource_source_le
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ) (i : Fin 2) :
    (binaryRunPointingSource n p t).degreeOf (Sum.inr i) ≤ n := by
  have hzero := degreeOf_binaryRunHomogenizedSource_source_zero_le hp t
  have hderivZero :
      (MvPolynomial.pderiv (Sum.inr 0)
        (binaryRunHomogenizedSource n p t)).degreeOf (Sum.inr 0) ≤ n :=
    (MvPolynomial.degreeOf_pderiv_le _ _ _).trans hzero
  have hderivOne :=
    degreeOf_pderiv_binaryRunHomogenizedSource_source_one_le n p t
  rw [binaryRunPointingSource, add_mul]
  refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
  · fin_cases i
    · exact (degreeOf_X_mul_pderiv_le _ _ _).trans hzero
    · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by
        simpa [MvPolynomial.degreeOf_X] using hderivOne)
  · fin_cases i
    · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by
        simpa [MvPolynomial.degreeOf_X] using hderivZero)
    · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by
        simpa [MvPolynomial.degreeOf_X] using hderivOne)

@[simp] theorem eval_binaryRunHomogenizedSource
    (n : ℕ) (p : ℝ[X]) (t : ℝ) (z : Fin 2 ⊕ Fin 2 → ℂ) :
    MvPolynomial.eval z (binaryRunHomogenizedSource n p t) =
      MvPolynomial.eval ![z (Sum.inl 0) + z (Sum.inr 0),
        z (Sum.inl 0) + z (Sum.inr 1)]
        (complexifyMv ((scalePolynomial t p).homogenize (n + 1))) := by
  rw [binaryRunHomogenizedSource, MvPolynomial.aeval_def,
    MvPolynomial.eval_eval₂]
  congr 1
  · ext c
    simp
  · funext i
    fin_cases i <;> simp

/-- The homogenized binary-run source is stable for a positive scaling of a
nonzero PF polynomial in the degree box. -/
theorem mvUpperHalfPlaneStable_binaryRunHomogenizedSource
    {n : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : p ≠ 0)
    (hdegree : p.natDegree ≤ n) {t : ℝ} (ht : 0 < t) :
    MvUpperHalfPlaneStable (binaryRunHomogenizedSource n p t) := by
  have hscaled : IsPFPolynomial (scalePolynomial t p) := by
    simpa [scalePolynomial] using
      hp.comp_C_mul_X_add_C (a := t) (d := 0) ht le_rfl
  have hscaled0 : scalePolynomial t p ≠ 0 := by
    rw [scalePolynomial]
    intro hzero
    apply hp0
    exact (Polynomial.comp_C_mul_X_eq_zero_iff (by simpa using ht.ne')).mp
      hzero
  have hscaledDegree : (scalePolynomial t p).natDegree ≤ n + 1 :=
    (natDegree_scalePolynomial_le t p).trans (by lia)
  have hhom :=
    BorceaBranden.homogenize_stable_of_splits_nonpos_of_natDegree_le
      hscaledDegree hscaled0 (hscaled.ne_zero_and_splits hscaled0).2
        hscaled.roots_nonpos
  intro z hz
  rw [eval_binaryRunHomogenizedSource]
  apply hhom
  intro i
  fin_cases i
  · simpa using add_pos (hz (Sum.inl 0)) (hz (Sum.inr 0))
  · simpa using add_pos (hz (Sum.inl 0)) (hz (Sum.inr 1))

/-- Pointing and differentiating the stable homogenized source preserves weak
stability. -/
theorem mvUpperHalfPlaneStableOrZero_binaryRunPointingSource
    {n : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : p ≠ 0)
    (hdegree : p.natDegree ≤ n) {t : ℝ} (ht : 0 < t) :
    MvUpperHalfPlaneStableOrZero (binaryRunPointingSource n p t) := by
  have hsource := mvUpperHalfPlaneStable_binaryRunHomogenizedSource
    hp hp0 hdegree ht
  have hderiv := hsource.pderiv_zero_or_of_finite (Sum.inr 0)
  exact (MvUpperHalfPlaneStable.X_add_X (Sum.inr 0) (Sum.inl 1)).orZero.mul
    hderiv

/-- The concrete signed-parity pencil obtained from the pointing construction
is stable, with the zero-pair alternative retained explicitly. -/
theorem mvUpperHalfPlaneStableOrZero_binaryRunPointingPencil
    {n : ℕ} (hn : 1 ≤ n) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hp0 : p ≠ 0) (hdegree : p.natDegree ≤ n) {t : ℝ} (ht : 0 < t) :
    MvUpperHalfPlaneStableOrZero
      (bivariatePencil
        (-(signedParityLift (n - 1)
          (shiftedBinaryRunDeformation n p t).derivative))
        (signedParityLift n (binaryRunPointingRemainder n p t))) := by
  have hsource := mvUpperHalfPlaneStableOrZero_binaryRunPointingSource
    hp hp0 hdegree ht
  have hcontracted := hsource.normalizedDiagonalContraction
    (fun i => degreeOf_binaryRunPointingSource_source_le hdegree t i)
  rw [normalizedDiagonalContraction_binaryRunPointingSource hn hdegree t]
    at hcontracted
  exact hcontracted

/-- The pointing construction discharges the stable-pencil hypothesis in the
critical-value sign theorem. The degenerate zero-pencil branch makes the
pointing polynomial itself zero and hence satisfies the inequality directly.
-/
theorem binaryRunDeformation_critical_sign
    {n : ℕ} (hn : 4 ≤ n) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hp0 : p ≠ 0) (hdegree : p.natDegree ≤ n) {t r : ℝ} (ht : 0 < t)
    (hr : 0 < r)
    (hcritical :
      (shiftedBinaryRunDeformation n p t).derivative.eval
        (-(r ^ 2)⁻¹) = 0) :
    (shiftedBinaryRunPointing n p t).eval (-(r ^ 2)⁻¹) *
      (shiftedBinaryRunDeformation n p t).derivative.derivative.eval
        (-(r ^ 2)⁻¹) ≤ 0 := by
  have hpencil := mvUpperHalfPlaneStableOrZero_binaryRunPointingPencil
    (by lia) hp hp0 hdegree ht
  rcases hpencil.eq_zero_pair_or_stablePencil with hzero | hstable
  · have hqzero :
        (shiftedBinaryRunDeformation n p t).derivative = 0 := by
      apply (signedParityLift_eq_zero_iff
        (natDegree_derivative_shiftedBinaryRunDeformation_le hdegree t)).mp
      exact neg_eq_zero.mp hzero.1
    have hEzero : binaryRunPointingRemainder n p t = 0 := by
      apply (signedParityLift_eq_zero_iff
        (natDegree_binaryRunPointingRemainder_le hdegree t)).mp
      exact hzero.2
    have hpointing : shiftedBinaryRunPointing n p t = 0 := by
      rw [shiftedBinaryRunPointing_eq_remainder_add, hEzero, hqzero]
      simp
    rw [hpointing]
    simp
  · exact binaryRunDeformation_critical_sign_of_stablePencil
      hn hdegree hr hcritical hstable

/-- Equivalent negative-coordinate form of the critical-value inequality. -/
theorem binaryRunDeformation_critical_sign_of_neg
    {n : ℕ} (hn : 4 ≤ n) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hp0 : p ≠ 0) (hdegree : p.natDegree ≤ n) {t y : ℝ} (ht : 0 < t)
    (hy : y < 0)
    (hcritical :
      (shiftedBinaryRunDeformation n p t).derivative.eval y = 0) :
    (shiftedBinaryRunPointing n p t).eval y *
      (shiftedBinaryRunDeformation n p t).derivative.derivative.eval y ≤ 0 := by
  let r : ℝ := Real.sqrt (-y)⁻¹
  have hinv : 0 < (-y)⁻¹ := inv_pos.mpr (neg_pos.mpr hy)
  have hr : 0 < r := Real.sqrt_pos.mpr hinv
  have hr_sq : r ^ 2 = (-y)⁻¹ := Real.sq_sqrt hinv.le
  have hcoord : -(r ^ 2)⁻¹ = y := by
    rw [hr_sq, inv_inv]
    ring
  rw [← hcoord] at hcritical ⊢
  exact binaryRunDeformation_critical_sign hn hp hp0 hdegree ht hr hcritical

end

end RealRooted
