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

/-- Source exponent with powers `S^a T^b`. -/
def binaryRunSourceIndex (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

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

end

end RealRooted
