import Mathlib
import RealRooted.AffineFamily
import RealRooted.Linear
import RealRooted.Tactic.Finish
import RealRooted.WagnerX

/-!
# Linear-power families

Reusable certificates for polynomial sequences built from a fixed positive
linear factor.  The main applications are first-order product recurrences
whose tail is `C u + C v * X` or `C u * X`, together with the confluent
interlacing of powers of a single linear factor.
-/

open Polynomial

namespace RealRooted

/-- `Prec (X^n) (X^(n+1))`: repeated root at `0`. -/
theorem prec_X_pow_succ (n : ℕ) : Prec ((X : ℝ[X]) ^ n) (X ^ (n + 1)) := by
  have hne : (X : ℝ[X]) ^ n ≠ 0 := pow_ne_zero _ X_ne_zero
  have hsplits : ((X : ℝ[X]) ^ n).Splits := Polynomial.Splits.X_pow n
  have hnn : HasNonnegCoeffs ((X : ℝ[X]) ^ n) := by
    intro m
    rw [coeff_X_pow]
    split <;> norm_num
  have hprec := prec_self_mul_X_of_nonneg hne hsplits hnn
  rwa [show (X : ℝ[X]) * X ^ n = X ^ (n + 1) by ring] at hprec

/-- `Prec ((X + C r)^n) ((X + C r)^(n+1))` by translating the repeated root. -/
theorem prec_X_add_C_pow_succ (r : ℝ) (n : ℕ) :
    Prec ((X + C r) ^ n) ((X + C r) ^ (n + 1)) := by
  have hprec := prec_X_pow_succ n
  rw [← prec_comp_X_add_C_iff r] at hprec
  simpa [pow_comp, X_comp] using hprec

/-- Confluent interlacing for a positive linear factor `a + bX`, with `b > 0`. -/
theorem interlaces_linear_pow (a b : ℝ) (hb : 0 < b) (n : ℕ) :
    Interlaces ((C a + C b * X) ^ n) ((C a + C b * X) ^ (n + 1)) := by
  have hfac : (C a + C b * X : ℝ[X]) = C b * (X + C (a / b)) := by
    rw [mul_add, ← C_mul]
    have : b * (a / b) = a := by field_simp
    rw [this]
    ring
  rw [hfac, mul_pow, mul_pow, ← C_pow, ← C_pow]
  have hbase := prec_X_add_C_pow_succ (a / b) n
  have hprec :
      Prec (C (b ^ n) * (X + C (a / b)) ^ n)
        (C (b ^ (n + 1)) * (X + C (a / b)) ^ (n + 1)) :=
    prec_C_mul_right (prec_C_mul_left hbase (by positivity)) (by positivity)
  have hd₁ : (C (b ^ n) * (X + C (a / b)) ^ n).natDegree = n := by
    rw [natDegree_C_mul (by positivity), natDegree_pow, natDegree_X_add_C, mul_one]
  have hd₂ : (C (b ^ (n + 1)) * (X + C (a / b)) ^ (n + 1)).natDegree = n + 1 := by
    rw [natDegree_C_mul (by positivity), natDegree_pow, natDegree_X_add_C, mul_one]
  exact hprec.toInterlaces (by rw [hd₁, hd₂])

/-- Scalar multiple of `interlaces_linear_pow`; scaling by `C c` preserves roots. -/
theorem interlaces_C_mul_linear_pow (c a b : ℝ) (hc : c ≠ 0) (hb : 0 < b)
    (n : ℕ) :
    Interlaces (C c * (C a + C b * X) ^ n)
      (C c * (C a + C b * X) ^ (n + 1)) := by
  have hbase := interlaces_linear_pow a b hb n
  have hprec : Prec (C c * (C a + C b * X) ^ n)
      (C c * (C a + C b * X) ^ (n + 1)) :=
    prec_C_mul_right (prec_C_mul_left hbase.toPrec hc) hc
  have hlin_deg : (C a + C b * X : ℝ[X]).natDegree = 1 := by
    compute_degree!
    exact hb.ne'
  have hd₁ : (C c * (C a + C b * X) ^ n).natDegree = n := by
    rw [natDegree_C_mul hc, natDegree_pow, hlin_deg, mul_one]
  have hd₂ : (C c * (C a + C b * X) ^ (n + 1)).natDegree = n + 1 := by
    rw [natDegree_C_mul hc, natDegree_pow, hlin_deg, mul_one]
  exact hprec.toInterlaces (by rw [hd₁, hd₂])

/-- Nonnegative coefficients of `(C a + C b * X)^n` when `a, b ≥ 0`. -/
theorem hasNonnegCoeffs_linear_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (n : ℕ) :
    HasNonnegCoeffs ((C a + C b * X) ^ n) := by
  apply HasNonnegCoeffs.pow
  intro m
  rw [coeff_add, coeff_C_mul, coeff_C, coeff_X]
  rcases m with _ | m
  · simp [ha]
  · rcases m with _ | m <;> simp [hb]

/-- A nonzero constant interlaces any degree-one polynomial. -/
theorem interlaces_const_linear {c p : ℝ[X]}
    (hc₀ : c ≠ 0) (hcdeg : c.natDegree = 0) (hp_deg : p.natDegree = 1) :
    Interlaces c p := by
  have hc_rr : c ≠ 0 ∧ c.Splits := isRealRooted_of_deg_zero hc₀ hcdeg
  have hp_rr : p ≠ 0 ∧ p.Splits := isRealRooted_of_degree_one hp_deg
  have hp_deg' : p.degree = 1 := by simpa [hp_deg] using degree_eq_natDegree hp_rr.1
  have hc_roots : c.roots = 0 := by
    rw [← Multiset.card_eq_zero]
    have hcard := card_roots_of_splits hc_rr.2
    rw [hcdeg] at hcard
    omega
  refine ⟨hp_rr, hc_rr, by simp [hcdeg, hp_deg], ?_⟩
  refine ⟨[-(p.coeff 1)⁻¹ * p.coeff 0], [], by simp, by simp, ?_, ?_,
    by simp [ListInterlaces]⟩
  · simpa [hp_deg'] using (Polynomial.roots_degree_eq_one (p := p) hp_deg').symm
  · simp [hc_roots]

/-- Nonvanishing for a sequence with constant and linear bases and fixed linear tail. -/
theorem linear_tail_sequence_ne_zero {A : ℕ → ℝ[X]} {c a b u v : ℝ}
    (hc : c ≠ 0) (hb : b ≠ 0) (hv : v ≠ 0)
    (h0 : A 0 = C c) (h1 : A 1 = C a + C b * X)
    (hstep : ∀ n, A (n + 2) = (C u + C v * X) * A (n + 1)) :
    ∀ n, A n ≠ 0
  | 0 => by
      rw [h0]
      exact C_ne_zero.mpr hc
  | 1 => by
      rw [h1]
      intro hzero
      have hdeg : (C a + C b * X : ℝ[X]).natDegree = 1 := by
        compute_degree!
      rw [hzero] at hdeg
      simp at hdeg
  | n + 2 => by
      rw [hstep n]
      have htail : (C u + C v * X : ℝ[X]) ≠ 0 := by
        intro hzero
        have hdeg : (C u + C v * X : ℝ[X]).natDegree = 1 := by
          compute_degree!
        rw [hzero] at hdeg
        simp at hdeg
      exact mul_ne_zero htail
        (linear_tail_sequence_ne_zero (A := A) hc hb hv h0 h1 hstep (n + 1))

/-- Splitting for a sequence with constant and linear bases and fixed linear tail. -/
theorem linear_tail_sequence_splits {A : ℕ → ℝ[X]} {c a b u v : ℝ}
    (h0 : A 0 = C c) (h1 : A 1 = C a + C b * X)
    (hstep : ∀ n, A (n + 2) = (C u + C v * X) * A (n + 1)) :
    ∀ n, (A n).Splits
  | 0 => by
      rw [h0]
      exact Polynomial.Splits.C c
  | 1 => by
      rw [h1]
      apply Polynomial.Splits.of_natDegree_le_one
      compute_degree!
  | n + 2 => by
      rw [hstep n]
      have htail_splits : (C u + C v * X : ℝ[X]).Splits := by
        apply Polynomial.Splits.of_natDegree_le_one
        compute_degree!
      exact htail_splits.mul
        (linear_tail_sequence_splits (A := A) (c := c) (a := a) (b := b) (u := u)
          (v := v) h0 h1 hstep (n + 1))

/-- Coefficientwise nonnegativity for constant/linear bases and fixed linear tail. -/
theorem linear_tail_sequence_nonneg {A : ℕ → ℝ[X]} {c a b u v : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h0 : A 0 = C c) (h1 : A 1 = C a + C b * X)
    (hstep : ∀ n, A (n + 2) = (C u + C v * X) * A (n + 1)) :
    ∀ n, HasNonnegCoeffs (A n)
  | 0 => by
      rw [h0]
      simpa [pow_one] using
        (hasNonnegCoeffs_linear_pow (a := c) (b := 0) hc (by norm_num) 1)
  | 1 => by
      rw [h1]
      simpa [pow_one] using hasNonnegCoeffs_linear_pow (a := a) (b := b) ha hb 1
  | n + 2 => by
      rw [hstep n]
      have htail_nonneg : HasNonnegCoeffs (C u + C v * X : ℝ[X]) := by
        simpa [pow_one] using
          hasNonnegCoeffs_linear_pow (a := u) (b := v) hu hv 1
      exact htail_nonneg.mul
        (linear_tail_sequence_nonneg (A := A) hc ha hb hu hv h0 h1 hstep (n + 1))

/-- Degree profile for constant/linear bases and fixed degree-one linear tail. -/
theorem linear_tail_sequence_natDegree {A : ℕ → ℝ[X]} {c a b u v : ℝ}
    (hc : c ≠ 0) (hb : b ≠ 0) (hv : v ≠ 0)
    (h0 : A 0 = C c) (h1 : A 1 = C a + C b * X)
    (hstep : ∀ n, A (n + 2) = (C u + C v * X) * A (n + 1)) :
    ∀ n, (A n).natDegree = n
  | 0 => by
      rw [h0]
      simp
  | 1 => by
      rw [h1]
      compute_degree!
  | n + 2 => by
      rw [hstep n]
      have htail_ne : (C u + C v * X : ℝ[X]) ≠ 0 := by
        intro hzero
        have hdeg : (C u + C v * X : ℝ[X]).natDegree = 1 := by
          compute_degree!
        rw [hzero] at hdeg
        simp at hdeg
      have htail_deg : (C u + C v * X : ℝ[X]).natDegree = 1 := by
        compute_degree!
      rw [natDegree_mul htail_ne
        (linear_tail_sequence_ne_zero (A := A) hc hb hv h0 h1 hstep (n + 1)),
        htail_deg,
        linear_tail_sequence_natDegree (A := A) hc hb hv h0 h1 hstep (n + 1)]
      omega

/-- Multiplication by a positive linear factor appends a negative root and interlaces. -/
theorem interlaces_self_mul_C_add_C_mul_X_of_nonnegCoeffs {f : ℝ[X]}
    (hne : f ≠ 0) (hsplits : f.Splits) (_hnn : HasNonnegCoeffs f)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Interlaces f ((C a + C b * X) * f) := by
  have h1X : Prec (1 : ℝ[X]) X := (interlaces_one_linear (p := X) (by simp)).toPrec
  have hXpos : HasPosLeadingCoeff (X : ℝ[X]) := by
    unfold HasPosLeadingCoeff
    simp
  have hcop : IsCoprime (C a * (1 : ℝ[X])) (C b * X) := by
    refine ⟨C a⁻¹, 0, ?_⟩
    rw [mul_one, ← C_mul, inv_mul_cancel₀ ha.ne']
    simp
  have hsum_ne : (C a * (1 : ℝ[X]) + C b * X) ≠ 0 := by
    intro hzero
    have hdeg : (C a * (1 : ℝ[X]) + C b * X).natDegree = 1 := by
      compute_degree!
      exact hb.ne'
    rw [hzero] at hdeg
    simp at hdeg
  have hsum_splits : (C a * (1 : ℝ[X]) + C b * X).Splits := by
    apply Polynomial.Splits.of_natDegree_le_one
    compute_degree!
  have hprec : Prec (f * 1) (C a * (f * 1) + C b * (f * X)) :=
    prec_convex_left_of_common_factor (d := f) (f' := 1) (g' := X)
      hne hsplits (by ring) (by ring) h1X hasPosLeadingCoeff_one hXpos ha hb
      hsum_ne hsum_splits hcop
  rw [mul_one] at hprec
  have heq : C a * f + C b * (f * X) = (C a + C b * X) * f := by
    ring
  rw [heq] at hprec
  have hlin_ne : (C a + C b * X : ℝ[X]) ≠ 0 := by
    intro hzero
    have hdeg : (C a + C b * X : ℝ[X]).natDegree = 1 := by
      compute_degree!
      exact hb.ne'
    rw [hzero] at hdeg
    simp at hdeg
  have hlin_deg : (C a + C b * X : ℝ[X]).natDegree = 1 := by
    compute_degree!
    exact hb.ne'
  have hdeg : f.natDegree + 1 = ((C a + C b * X) * f).natDegree := by
    rw [natDegree_mul hlin_ne hne, hlin_deg]
    ring
  exact hprec.toInterlaces hdeg

/-- Unit-slope variant of `interlaces_self_mul_C_add_C_mul_X_of_nonnegCoeffs`. -/
theorem interlaces_self_mul_C_add_X_of_nonnegCoeffs {f : ℝ[X]} (hne : f ≠ 0)
    (hsplits : f.Splits) (hnn : HasNonnegCoeffs f) {c : ℝ} (hc : 0 < c) :
    Interlaces f ((C c + X) * f) := by
  simpa [C_1] using
    interlaces_self_mul_C_add_C_mul_X_of_nonnegCoeffs hne hsplits hnn hc
      (by norm_num : (0 : ℝ) < 1)

/-- Consecutive interlacing for a positive constant/linear-base fixed-linear-tail sequence. -/
theorem linear_tail_sequence_interlaces {A : ℕ → ℝ[X]} {c a b u v : ℝ}
    (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 < b) (hu : 0 < u) (hv : 0 < v)
    (h0 : A 0 = C c) (h1 : A 1 = C a + C b * X)
    (hstep : ∀ n, A (n + 2) = (C u + C v * X) * A (n + 1)) :
    ∀ n, Interlaces (A n) (A (n + 1))
  | 0 => by
      exact
        interlaces_const_linear
          (linear_tail_sequence_ne_zero (A := A) hc.ne' hb.ne' hv.ne' h0 h1 hstep 0)
          (linear_tail_sequence_natDegree (A := A) hc.ne' hb.ne' hv.ne' h0 h1 hstep 0)
          (linear_tail_sequence_natDegree (A := A) hc.ne' hb.ne' hv.ne' h0 h1 hstep 1)
  | n + 1 => by
      change Interlaces (A (n + 1)) (A (n + 2))
      rw [hstep n]
      exact
        interlaces_self_mul_C_add_C_mul_X_of_nonnegCoeffs
          (linear_tail_sequence_ne_zero (A := A) hc.ne' hb.ne' hv.ne' h0 h1 hstep
            (n + 1))
          (linear_tail_sequence_splits (A := A) (c := c) (a := a) (b := b) (u := u)
            (v := v) h0 h1 hstep (n + 1))
          (linear_tail_sequence_nonneg (A := A) hc.le ha hb.le hu.le hv.le h0 h1 hstep
            (n + 1))
          hu hv

/-- Nonvanishing for a sequence with fixed monomial tail recurrence. -/
theorem monomial_tail_sequence_ne_zero {A : ℕ → ℝ[X]} {c a b u : ℝ}
    (hc : c ≠ 0) (hb : b ≠ 0) (hu : u ≠ 0)
    (h0 : A 0 = C c) (h1 : A 1 = C a + C b * X)
    (hstep : ∀ n, A (n + 2) = (C u * X) * A (n + 1)) :
    ∀ n, A n ≠ 0
  | 0 => by
      rw [h0]
      exact C_ne_zero.mpr hc
  | 1 => by
      rw [h1]
      intro hzero
      have hdeg : (C a + C b * X : ℝ[X]).natDegree = 1 := by
        compute_degree!
      rw [hzero] at hdeg
      simp at hdeg
  | n + 2 => by
      rw [hstep n]
      have htail : (C u * X : ℝ[X]) ≠ 0 :=
        mul_ne_zero (C_ne_zero.mpr hu) X_ne_zero
      exact mul_ne_zero htail
        (monomial_tail_sequence_ne_zero (A := A) hc hb hu h0 h1 hstep (n + 1))

/-- Splitting for a sequence with fixed monomial tail recurrence. -/
theorem monomial_tail_sequence_splits {A : ℕ → ℝ[X]} {c a b u : ℝ}
    (h0 : A 0 = C c) (h1 : A 1 = C a + C b * X)
    (hstep : ∀ n, A (n + 2) = (C u * X) * A (n + 1)) :
    ∀ n, (A n).Splits
  | 0 => by
      rw [h0]
      exact Polynomial.Splits.C c
  | 1 => by
      rw [h1]
      apply Polynomial.Splits.of_natDegree_le_one
      compute_degree!
  | n + 2 => by
      rw [hstep n]
      have htail_splits : (C u * X : ℝ[X]).Splits := by
        apply Polynomial.Splits.of_natDegree_le_one
        compute_degree!
      exact htail_splits.mul
        (monomial_tail_sequence_splits (A := A) (c := c) (a := a) (b := b) (u := u)
          h0 h1 hstep (n + 1))

/-- Coefficientwise nonnegativity for a sequence with fixed monomial tail recurrence. -/
theorem monomial_tail_sequence_nonneg {A : ℕ → ℝ[X]} {c a b u : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (h0 : A 0 = C c) (h1 : A 1 = C a + C b * X)
    (hstep : ∀ n, A (n + 2) = (C u * X) * A (n + 1)) :
    ∀ n, HasNonnegCoeffs (A n)
  | 0 => by
      rw [h0]
      simpa [pow_one] using
        hasNonnegCoeffs_linear_pow (a := c) (b := 0) hc (by norm_num) 1
  | 1 => by
      rw [h1]
      simpa [pow_one] using hasNonnegCoeffs_linear_pow (a := a) (b := b) ha hb 1
  | n + 2 => by
      rw [hstep n]
      have htail_nonneg : HasNonnegCoeffs (C u * X : ℝ[X]) := by
        simpa [pow_one, zero_add] using
          hasNonnegCoeffs_linear_pow (a := 0) (b := u) (by norm_num) hu 1
      exact htail_nonneg.mul
        (monomial_tail_sequence_nonneg (A := A) hc ha hb hu h0 h1 hstep (n + 1))

/-- Degree profile for constant/linear bases and fixed nonzero monomial tail. -/
theorem monomial_tail_sequence_natDegree {A : ℕ → ℝ[X]} {c a b u : ℝ}
    (hc : c ≠ 0) (hb : b ≠ 0) (hu : u ≠ 0)
    (h0 : A 0 = C c) (h1 : A 1 = C a + C b * X)
    (hstep : ∀ n, A (n + 2) = (C u * X) * A (n + 1)) :
    ∀ n, (A n).natDegree = n
  | 0 => by
      rw [h0]
      simp
  | 1 => by
      rw [h1]
      compute_degree!
  | n + 2 => by
      rw [hstep n]
      have htail_ne : (C u * X : ℝ[X]) ≠ 0 :=
        mul_ne_zero (C_ne_zero.mpr hu) X_ne_zero
      rw [natDegree_mul htail_ne
        (monomial_tail_sequence_ne_zero (A := A) hc hb hu h0 h1 hstep (n + 1)),
        natDegree_C_mul_X u hu,
        monomial_tail_sequence_natDegree (A := A) hc hb hu h0 h1 hstep (n + 1)]
      omega

/-- Consecutive interlacing for a positive constant/linear-base monomial-tail sequence. -/
theorem monomial_tail_sequence_interlaces {A : ℕ → ℝ[X]} {c a b u : ℝ}
    (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 < b) (hu : 0 < u)
    (h0 : A 0 = C c) (h1 : A 1 = C a + C b * X)
    (hstep : ∀ n, A (n + 2) = (C u * X) * A (n + 1)) :
    ∀ n, Interlaces (A n) (A (n + 1))
  | 0 => by
      exact
        interlaces_const_linear
          (monomial_tail_sequence_ne_zero (A := A) hc.ne' hb.ne' hu.ne' h0 h1 hstep 0)
          (monomial_tail_sequence_natDegree (A := A) hc.ne' hb.ne' hu.ne' h0 h1 hstep 0)
          (monomial_tail_sequence_natDegree (A := A) hc.ne' hb.ne' hu.ne' h0 h1 hstep 1)
  | n + 1 => by
      change Interlaces (A (n + 1)) (A (n + 2))
      rw [hstep n]
      have hne :=
        monomial_tail_sequence_ne_zero (A := A) hc.ne' hb.ne' hu.ne' h0 h1 hstep (n + 1)
      have hsplits :=
        monomial_tail_sequence_splits (A := A) (c := c) (a := a) (b := b) (u := u)
          h0 h1 hstep (n + 1)
      have hnn :=
        monomial_tail_sequence_nonneg (A := A) hc.le ha hb.le hu.le h0 h1 hstep (n + 1)
      have hprecX : Prec (A (n + 1)) (X * A (n + 1)) :=
        prec_self_mul_X_of_nonneg hne hsplits hnn
      have hprec : Prec (A (n + 1)) ((C u * X) * A (n + 1)) := by
        have hscaled := prec_C_mul_right hprecX hu.ne'
        simpa [mul_assoc] using hscaled
      have htail_ne : (C u * X : ℝ[X]) ≠ 0 :=
        mul_ne_zero (C_ne_zero.mpr hu.ne') X_ne_zero
      have hdeg : (A (n + 1)).natDegree + 1 = ((C u * X) * A (n + 1)).natDegree := by
        rw [natDegree_mul htail_ne hne, natDegree_C_mul_X u hu.ne']
        ring
      exact hprec.toInterlaces hdeg

/-- A linear factor interlaces the factored quadratic when its root is between the two roots. -/
theorem interlaces_linear_quadratic_of_roots_between {α r s c : ℝ} (hc : c ≠ 0)
    (hrα : r ≤ α) (hαs : α ≤ s) :
    Interlaces (X - C α) (C c * ((X - C r) * (X - C s))) := by
  have hlin_ne : (X - C α) ≠ 0 := X_sub_C_ne_zero α
  have hquad_ne : (C c * ((X - C r) * (X - C s))) ≠ 0 :=
    mul_ne_zero (by simpa using hc) (mul_ne_zero (X_sub_C_ne_zero r) (X_sub_C_ne_zero s))
  have hlin_split : (X - C α).Splits := Polynomial.Splits.X_sub_C _
  have hquad_split : (C c * ((X - C r) * (X - C s))).Splits :=
    (Polynomial.Splits.C _).mul
      ((Polynomial.Splits.X_sub_C r).mul (Polynomial.Splits.X_sub_C s))
  have hlin_deg : (X - C α).natDegree = 1 := natDegree_X_sub_C α
  have hquad_deg : (C c * ((X - C r) * (X - C s))).natDegree = 2 := by
    rw [natDegree_C_mul hc, natDegree_mul (X_sub_C_ne_zero r) (X_sub_C_ne_zero s),
      natDegree_X_sub_C, natDegree_X_sub_C]
  have hlin_roots : (X - C α).roots = {α} := roots_X_sub_C α
  have hquad_roots : (C c * ((X - C r) * (X - C s))).roots = {r, s} := by
    rw [roots_C_mul _ hc, roots_mul (mul_ne_zero (X_sub_C_ne_zero r) (X_sub_C_ne_zero s)),
      roots_X_sub_C, roots_X_sub_C]
    rfl
  refine ⟨⟨hquad_ne, hquad_split⟩, ⟨hlin_ne, hlin_split⟩,
    by rw [hlin_deg, hquad_deg], [r, s], [α], ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrα.trans hαs]
  · simp
  · rw [hquad_roots]
    rfl
  · rw [hlin_roots]
    rfl
  · simp [ListInterlaces, hrα, hαs]

/-- Common-factor variant: `(X - C r)^m * (a+bX)^n` interlaces its successor. -/
theorem interlaces_X_sub_C_pow_mul_linear_pow (r : ℝ) (m : ℕ) (a b : ℝ)
    (hb : 0 < b) (n : ℕ) :
    Interlaces ((X - C r) ^ m * (C a + C b * X) ^ n)
      ((X - C r) ^ m * (C a + C b * X) ^ (n + 1)) := by
  have hprec := (interlaces_linear_pow a b hb n).toPrec
  have hmul :
      ∀ j,
        Prec ((X - C r) ^ j * (C a + C b * X) ^ n)
          ((X - C r) ^ j * (C a + C b * X) ^ (n + 1)) := by
    intro j
    induction j with
    | zero =>
        simpa using hprec
    | succ j ihj =>
        have hnext := prec_mul_X_sub_C_both r ihj
        rw [show (X - C r) * ((X - C r) ^ j * (C a + C b * X) ^ n) =
              (X - C r) ^ (j + 1) * (C a + C b * X) ^ n by ring,
            show (X - C r) * ((X - C r) ^ j * (C a + C b * X) ^ (n + 1)) =
              (X - C r) ^ (j + 1) * (C a + C b * X) ^ (n + 1) by ring] at hnext
        exact hnext
  have hprecm := hmul m
  have hlin_deg : (C a + C b * X : ℝ[X]).natDegree = 1 := by
    compute_degree!
    exact hb.ne'
  have hlin_ne : (C a + C b * X : ℝ[X]) ≠ 0 := by
    intro hzero
    rw [hzero] at hlin_deg
    simp at hlin_deg
  have hdegree : ∀ k, ((X - C r) ^ m * (C a + C b * X) ^ k).natDegree = m + k := by
    intro k
    rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero r)) (pow_ne_zero _ hlin_ne),
      natDegree_pow, natDegree_X_sub_C, mul_one, natDegree_pow, hlin_deg, mul_one]
  exact hprecm.toInterlaces (by rw [hdegree n, hdegree (n + 1)]; omega)

end RealRooted
