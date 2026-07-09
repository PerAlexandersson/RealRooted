import RealRooted

/-!
# Super-recurrence Eulerian polynomials

This module stages the formalization of the proof in
`SuperEulerian/super-eulerian-real-rootedness.tex`.

The standard real-rootedness inputs are not reproved here.  They are packaged
as theorem interfaces from `RealRooted`.  The project-specific coefficient
identities, PF reductions, and interlacing reductions are checked Lean proofs.
-/

open Polynomial
open scoped Polynomial

noncomputable section

namespace SuperEulerian

open RealRooted

/-- The super-recurrence Eulerian coefficients.

The row index starts at `n = 1`.  The dummy row `n = 0` is zero, which keeps the
definition total.  The parameter `l` is a natural number; all main theorems use
`0 < l`.
-/
def superEulerianCoeff (l : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | 1, k => if k = 0 then 1 else 0
  | n + 2, k =>
      ((k + 1 : ℕ) : ℝ) ^ l * superEulerianCoeff l (n + 1) k +
        (((n + 2 - k : ℕ) : ℝ) ^ l) *
          if k = 0 then 0 else superEulerianCoeff l (n + 1) (k - 1)

theorem superEulerianCoeff_eq_zero_of_le (l n k : ℕ) (hnk : n ≤ k) :
    superEulerianCoeff l n k = 0 := by
  induction n generalizing k with
  | zero =>
      simp [superEulerianCoeff]
  | succ n ih =>
      cases n with
      | zero =>
          simp [superEulerianCoeff]
          have hk0 : k ≠ 0 := by
            lia
          simp [hk0]
      | succ n =>
          have hprev : n + 1 ≤ k := by
            lia
          have hprevPred : n + 1 ≤ k - 1 := by
            lia
          simp [superEulerianCoeff, ih k hprev, ih (k - 1) hprevPred]

theorem superEulerianCoeff_palindromic (l n k : ℕ) (hk : k < n) :
    superEulerianCoeff l n (n - 1 - k) = superEulerianCoeff l n k := by
  induction n generalizing k with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ hk)
  | succ n ih =>
      cases n with
      | zero =>
          have hk0 : k = 0 := by
            lia
          simp [hk0, superEulerianCoeff]
      | succ n =>
          by_cases hk0 : k = 0
          · subst k
            simpa [superEulerianCoeff, superEulerianCoeff_eq_zero_of_le] using
              ih 0 (by lia)
          · by_cases hktop : k = n + 1
            · subst k
              simpa [superEulerianCoeff, superEulerianCoeff_eq_zero_of_le] using
                (ih 0 (by lia)).symm
            · have hpredIndex : k - 1 < n + 1 := by
                lia
              have hsymA :
                  superEulerianCoeff l (n + 1) (n + 1 - k) =
                    superEulerianCoeff l (n + 1) (k - 1) := by
                have h := ih (k - 1) hpredIndex
                have harith : n - (k - 1) = n + 1 - k := by
                  lia
                simpa [harith] using h
              have hsymB :
                  superEulerianCoeff l (n + 1) (n + 1 - k - 1) =
                    superEulerianCoeff l (n + 1) k := by
                have h := ih k (by lia)
                have harith : n - k = n + 1 - k - 1 := by
                  lia
                simpa [harith] using h
              have hleft_ne : n + 1 - k ≠ 0 := by
                lia
              have hfactorA : n + 1 - k + 1 = n + 2 - k := by
                lia
              have hfactorB : n + 2 - (n + 1 - k) = k + 1 := by
                lia
              rw [show n + 1 + 1 - 1 - k = n + 1 - k by lia]
              simp only [superEulerianCoeff]
              rw [hsymA, hsymB]
              simp only [hk0, hleft_ne, if_false]
              rw [hfactorA, hfactorB]
              norm_num [Nat.cast_add]
              ring

/-- The row polynomial `E_n^{(l)}(t)`. -/
def row (l n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range n, C (superEulerianCoeff l n k) * X ^ k

/-- The normalized row `Q_n^{(l)}(t)`. -/
def normalizedRow (l n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range n,
    C (superEulerianCoeff l n k / ((Nat.choose (n - 1) k : ℝ) ^ l)) * X ^ k

/-- The binomial-power Hadamard kernel `B_{d,l}`. -/
def binomialKernel (l d : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1), C ((Nat.choose d k : ℝ) ^ l) * X ^ k

/-- The diagonal kernel `K_{d,l}` used for `(theta + 1)^l E_n`. -/
def diagonalKernel (l d : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C (((k + 1 : ℕ) : ℝ) ^ l * (Nat.choose d k : ℝ) ^ l) * X ^ k

/-- The boundary polynomial `A_n^{(l)} = (theta + 1)^l E_n^{(l)}`. -/
def boundary (l n : ℕ) : ℝ[X] :=
  RealRooted.iterateThetaPlusOne l (row l n)

/-- The shifted reciprocal boundary term `t^n A_n^{(l)}(1/t)`. -/
def reciprocalBoundary (l n : ℕ) : ℝ[X] :=
  RealRooted.reciprocalShift n (boundary l n)

/-- Closed-form version of the cumulative block-leader prefix `P_{n,m}^{(l)}`.

The combinatorial block-leader definition is in the TeX blueprint.  This
closed form is the version used by the final prefix-interlacing reduction.
-/
def prefixPoly (l n m : ℕ) : ℝ[X] :=
  RealRooted.iterateThetaPlusOne (l * (n - m)) (row l m)

@[simp] theorem coeff_row (l n k : ℕ) :
    (row l n).coeff k = if k < n then superEulerianCoeff l n k else 0 := by
  classical
  simp [row]

@[simp] theorem coeff_normalizedRow (l n k : ℕ) :
    (normalizedRow l n).coeff k =
      if k < n then
        superEulerianCoeff l n k / ((Nat.choose (n - 1) k : ℝ) ^ l)
      else 0 := by
  classical
  simp [normalizedRow]

@[simp] theorem coeff_binomialKernel (l d k : ℕ) :
    (binomialKernel l d).coeff k =
      if k < d + 1 then (Nat.choose d k : ℝ) ^ l else 0 := by
  classical
  by_cases hk : k < d + 1
  · have hmem : k ∈ Finset.range (d + 1) := by
      simpa using hk
    rw [binomialKernel, finsetSum_coeff]
    rw [Finset.sum_eq_single k]
    · rw [coeff_C_mul]
      simp [hk]
    · intro b _hb hbk
      have hkb : k ≠ b := fun h => hbk h.symm
      rw [coeff_C_mul]
      simp [hkb]
    · intro hknot
      exact False.elim (hknot hmem)
  · rw [binomialKernel, finsetSum_coeff]
    rw [Finset.sum_eq_zero]
    · simp [hk]
    · intro b hb
      have hbk : k ≠ b := by
        intro h
        subst k
        exact hk (by simpa using hb)
      rw [coeff_C_mul]
      simp [hbk]

@[simp] theorem coeff_diagonalKernel (l d k : ℕ) :
    (diagonalKernel l d).coeff k =
      if k < d + 1 then
        ((k + 1 : ℕ) : ℝ) ^ l * (Nat.choose d k : ℝ) ^ l
      else 0 := by
  classical
  by_cases hk : k < d + 1
  · have hmem : k ∈ Finset.range (d + 1) := by
      simpa using hk
    rw [diagonalKernel, finsetSum_coeff]
    rw [Finset.sum_eq_single k]
    · rw [coeff_C_mul]
      simp [hk]
    · intro b _hb hbk
      have hkb : k ≠ b := fun h => hbk h.symm
      rw [coeff_C_mul]
      simp [hkb]
    · intro hknot
      exact False.elim (hknot hmem)
  · rw [diagonalKernel, finsetSum_coeff]
    rw [Finset.sum_eq_zero]
    · simp [hk]
    · intro b hb
      have hbk : k ≠ b := by
        intro h
        subst k
        exact hk (by simpa using hb)
      rw [coeff_C_mul]
      simp [hbk]

@[simp] theorem coeff_iterateThetaPlusOne (l k : ℕ) (p : ℝ[X]) :
    (RealRooted.iterateThetaPlusOne l p).coeff k =
      ((k + 1 : ℕ) : ℝ) ^ l * p.coeff k := by
  induction l generalizing p with
  | zero =>
      simp
  | succ l ih =>
      rw [RealRooted.iterateThetaPlusOne_succ, RealRooted.coeff_thetaPlusOne, ih]
      norm_num [Nat.cast_add, pow_succ]
      ring

@[simp] theorem coeff_boundary (l n k : ℕ) :
    (boundary l n).coeff k =
      if k < n then
        ((k + 1 : ℕ) : ℝ) ^ l * superEulerianCoeff l n k
      else 0 := by
  simp [boundary]

theorem diagonalKernel_eq_iterateThetaPlusOne (l d : ℕ) :
    diagonalKernel l d =
      RealRooted.iterateThetaPlusOne l (binomialKernel l d) := by
  ext k
  rw [coeff_diagonalKernel, coeff_iterateThetaPlusOne, coeff_binomialKernel]
  by_cases hk : k < d + 1
  · simp [hk]
  · simp [hk]

/-- Local compatibility token for theorem statements that used to be bundled as
external standard facts.  The reusable inputs used below are now supplied by
proved `RealRooted` declarations. -/
structure StandardFacts where

namespace StandardFacts

theorem garloffWagnerPFPrec0 (_std : StandardFacts) :
    RealRooted.garloffWagnerHadamardPFPrec0Statement :=
  RealRooted.garloffWagnerHadamardPFPrec0_of_nonnegPrec

theorem hadamardPF (std : StandardFacts) {p q : ℝ[X]}
    (hp : RealRooted.IsPFPolynomial p) (hq : RealRooted.IsPFPolynomial q) :
    RealRooted.IsPFPolynomial (RealRooted.hadamardProduct p q) :=
  RealRooted.hadamardProduct_preserves_pf_of_garloffWagner
    std.garloffWagnerPFPrec0 hp hq

theorem hadamardPrec0Right (std : StandardFacts) {f g p : ℝ[X]}
    (hf : RealRooted.IsPFPolynomial f) (hg : RealRooted.IsPFPolynomial g)
    (hp : RealRooted.IsPFPolynomial p) (hfg : RealRooted.Prec0 f g) :
    RealRooted.Prec0
      (RealRooted.hadamardProduct f p)
      (RealRooted.hadamardProduct g p) :=
  RealRooted.hadamardProduct_preserves_prec0_right
    std.garloffWagnerPFPrec0 hf hg hp hfg

theorem hadamardPrec0Left (std : StandardFacts) {f p q : ℝ[X]}
    (hf : RealRooted.IsPFPolynomial f) (hp : RealRooted.IsPFPolynomial p)
    (hq : RealRooted.IsPFPolynomial q) (hpq : RealRooted.Prec0 p q) :
    RealRooted.Prec0
      (RealRooted.hadamardProduct f p)
      (RealRooted.hadamardProduct f q) :=
  RealRooted.hadamardProduct_preserves_prec0_left
    std.garloffWagnerPFPrec0 hf hp hq hpq

theorem iterateThetaPlusOne_pf (l : ℕ) {p : ℝ[X]}
    (hp : RealRooted.IsPFPolynomial p) :
    RealRooted.IsPFPolynomial (RealRooted.iterateThetaPlusOne l p) :=
  RealRooted.iterateThetaPlusOne_preserves_pf
    RealRooted.thetaPlusOne_preserves_pf l hp

theorem iterateThetaPlusOne_prec0 (_std : StandardFacts) (l : ℕ) {p q : ℝ[X]}
    (hp : RealRooted.IsPFPolynomial p) (hq : RealRooted.IsPFPolynomial q)
    (hpq : RealRooted.Prec0 p q) :
  RealRooted.Prec0
      (RealRooted.iterateThetaPlusOne l p)
      (RealRooted.iterateThetaPlusOne l q) :=
  RealRooted.iterateThetaPlusOne_preserves_prec0
    RealRooted.thetaPlusOne_preserves_pf
    (RealRooted.thetaPlusOnePreservesPrec0_of_derivative
      (RealRooted.derivativePreservesPrec0_of_sameDegree
        (RealRooted.derivativePreservesPrecSameDegree_of_two_le_natDegree
          (RealRooted.derivativePreservesPrecSameDegree_of_posLeading
            (RealRooted.derivativePreservesPrecSameDegree_of_monic
              RealRooted.derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonic)))))
    l hp hq hpq

end StandardFacts

theorem isPFPolynomial_one : RealRooted.IsPFPolynomial (1 : ℝ[X]) :=
  RealRooted.IsPFPolynomial.of_realRooted_nonneg RealRooted.hasNonnegCoeffs_one
    (by simp)

theorem isPFPolynomial_X_add_one_pow (d : ℕ) :
    RealRooted.IsPFPolynomial ((X + 1 : ℝ[X]) ^ d) := by
  induction d with
  | zero =>
      simpa using isPFPolynomial_one
  | succ d ih =>
      rw [pow_succ']
      exact RealRooted.isPFPolynomial_mul_X_add_one ih

theorem binomialKernel_one_eq_X_add_one_pow (d : ℕ) :
    binomialKernel 1 d = (X + 1 : ℝ[X]) ^ d := by
  ext k
  rw [coeff_binomialKernel]
  rw [show (((X + 1 : ℝ[X]) ^ d).coeff k : ℝ) = (Nat.choose d k : ℝ) by
    simpa using Polynomial.coeff_X_add_C_pow (R := ℝ) (r := 1) d k]
  by_cases hk : k < d + 1
  · simp [hk]
  · have hdk : d < k := by
      lia
    simp [hk, Nat.choose_eq_zero_of_lt hdk]

theorem diagonalKernel_one_eq_X_add_one_pow_mul_linear (d : ℕ) (hd : 0 < d) :
    diagonalKernel 1 d =
      (X + 1 : ℝ[X]) ^ (d - 1) * (C ((d + 1 : ℕ) : ℝ) * X + 1) := by
  rw [diagonalKernel_eq_iterateThetaPlusOne, binomialKernel_one_eq_X_add_one_pow]
  rw [RealRooted.iterateThetaPlusOne_succ, RealRooted.iterateThetaPlusOne_zero]
  rw [RealRooted.thetaPlusOne_eq_derivative_X_mul]
  rw [derivative_mul, derivative_X, one_mul]
  rw [derivative_pow]
  rw [derivative_add, derivative_X, derivative_one, add_zero]
  simp only [map_natCast, mul_one, Nat.cast_add, Nat.cast_one, map_add, map_one]
  have hd_eq : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.succ_le_of_lt hd)
  conv_lhs =>
    rw [show d = d - 1 + 1 by exact hd_eq.symm]
    rw [pow_succ]
  simp only [hd_eq]
  ring

private theorem reflect_two_C_mul_X_add_one (a : ℝ) :
    Polynomial.reflect 2 (C a * X + 1 : ℝ[X]) = X * (X + C a) := by
  conv_lhs =>
    arg 2
    rw [show (X : ℝ[X]) = X ^ 1 by ring]
    rw [show (1 : ℝ[X]) = C (1 : ℝ) * X ^ 0 by simp]
  rw [Polynomial.reflect_add, Polynomial.reflect_C_mul_X_pow,
    Polynomial.reflect_C_mul_X_pow]
  norm_num [Polynomial.revAt_le]
  ring

theorem reciprocalDiagonalKernel_one_eq_X_add_one_pow_mul_X_mul_linear
    (d : ℕ) (hd : 0 < d) :
    RealRooted.reciprocalShift (d + 1) (diagonalKernel 1 d) =
      (X + 1 : ℝ[X]) ^ (d - 1) * (X * (X + C ((d + 1 : ℕ) : ℝ))) := by
  rw [RealRooted.reciprocalShift]
  rw [diagonalKernel_one_eq_X_add_one_pow_mul_linear d hd]
  have hdegLeft : ((X + 1 : ℝ[X]) ^ (d - 1)).natDegree ≤ d - 1 := by
    exact RealRooted.natDegree_X_add_one_pow_le (d - 1)
  have hdegRight : (C ((d + 1 : ℕ) : ℝ) * X + 1 : ℝ[X]).natDegree ≤ 2 := by
    calc
      (C ((d + 1 : ℕ) : ℝ) * X + 1 : ℝ[X]).natDegree ≤
          max (C ((d + 1 : ℕ) : ℝ) * X : ℝ[X]).natDegree
            (1 : ℝ[X]).natDegree :=
        Polynomial.natDegree_add_le _ _
      _ ≤ 2 := by
        have hcx : (C ((d + 1 : ℕ) : ℝ) * X : ℝ[X]).natDegree ≤ 1 := by
          simpa only [pow_one] using
            Polynomial.natDegree_C_mul_X_pow_le (a := ((d + 1 : ℕ) : ℝ)) 1
        exact max_le (hcx.trans (by norm_num)) (by norm_num)
  have hreflect := Polynomial.reflect_mul
    ((X + 1 : ℝ[X]) ^ (d - 1))
    (C ((d + 1 : ℕ) : ℝ) * X + 1)
    hdegLeft hdegRight
  have hsum : d - 1 + 2 = d + 1 := by
    lia
  rw [hsum] at hreflect
  rw [hreflect]
  change RealRooted.IdTransform (d - 1) ((X + 1 : ℝ[X]) ^ (d - 1)) *
      Polynomial.reflect 2 (C ((d + 1 : ℕ) : ℝ) * X + 1 : ℝ[X]) =
    (X + 1 : ℝ[X]) ^ (d - 1) * (X * (X + C ((d + 1 : ℕ) : ℝ)))
  rw [RealRooted.IdTransform_X_add_one_pow]
  rw [reflect_two_C_mul_X_add_one]

theorem binomialKernel_succ_eq_hadamardProduct (l d : ℕ) :
    binomialKernel (l + 1) d =
      RealRooted.hadamardProduct (binomialKernel 1 d) (binomialKernel l d) := by
  ext k
  rw [coeff_binomialKernel, RealRooted.coeff_hadamardProduct, coeff_binomialKernel,
    coeff_binomialKernel]
  by_cases hk : k < d + 1
  · simp [hk, pow_succ, mul_comm]
  · simp [hk]

theorem diagonalKernel_succ_eq_hadamardProduct (l d : ℕ) :
    diagonalKernel (l + 1) d =
      RealRooted.hadamardProduct (diagonalKernel 1 d) (diagonalKernel l d) := by
  ext k
  rw [coeff_diagonalKernel, RealRooted.coeff_hadamardProduct, coeff_diagonalKernel,
    coeff_diagonalKernel]
  by_cases hk : k < d + 1
  · simp [hk, pow_succ, mul_comm, mul_left_comm, mul_assoc]
  · simp [hk]

theorem reciprocalDiagonalKernel_succ_eq_hadamardProduct (l d : ℕ) :
    RealRooted.reciprocalShift (d + 1) (diagonalKernel (l + 1) d) =
      RealRooted.hadamardProduct
        (RealRooted.reciprocalShift (d + 1) (diagonalKernel 1 d))
        (RealRooted.reciprocalShift (d + 1) (diagonalKernel l d)) := by
  rw [diagonalKernel_succ_eq_hadamardProduct]
  rw [RealRooted.reciprocalShift_hadamardProduct]

theorem binomialKernel_succ_isPF (std : StandardFacts) (l d : ℕ) :
    RealRooted.IsPFPolynomial (binomialKernel (l + 1) d) := by
  induction l with
  | zero =>
      rw [binomialKernel_one_eq_X_add_one_pow]
      exact isPFPolynomial_X_add_one_pow d
  | succ l ih =>
      rw [binomialKernel_succ_eq_hadamardProduct]
      exact std.hadamardPF
        (by
          rw [binomialKernel_one_eq_X_add_one_pow]
          exact isPFPolynomial_X_add_one_pow d)
        ih

/-! ## Project-specific proof obligations from the TeX blueprint -/

/-- One normalized transfer step:
`p ↦ (1 / N) * (theta + 1) ((N - theta) p)`. -/
def normalizedStep (N : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C ((N : ℝ)⁻¹) * RealRooted.thetaPlusOne (RealRooted.polarTheta N p)

/-- The `l`-fold normalized transfer step. -/
def iterateNormalizedStep (N l : ℕ) (p : ℝ[X]) : ℝ[X] :=
  ((normalizedStep N)^[l]) p

@[simp] theorem iterateNormalizedStep_zero (N : ℕ) (p : ℝ[X]) :
    iterateNormalizedStep N 0 p = p :=
  rfl

@[simp] theorem iterateNormalizedStep_succ (N l : ℕ) (p : ℝ[X]) :
    iterateNormalizedStep N (l + 1) p =
      normalizedStep N (iterateNormalizedStep N l p) := by
  simpa [iterateNormalizedStep] using
    Function.iterate_succ_apply' (normalizedStep N) l p

@[simp] theorem coeff_normalizedStep (N : ℕ) (p : ℝ[X]) (k : ℕ) :
    (normalizedStep N p).coeff k =
      ((N : ℝ)⁻¹ * (((k : ℝ) + 1) * ((N : ℝ) - k))) * p.coeff k := by
  simp [normalizedStep]
  ring

@[simp] theorem coeff_iterateNormalizedStep (N l : ℕ) (p : ℝ[X]) (k : ℕ) :
    (iterateNormalizedStep N l p).coeff k =
      (((N : ℝ)⁻¹ * (((k : ℝ) + 1) * ((N : ℝ) - k))) ^ l) *
        p.coeff k := by
  induction l generalizing p with
  | zero =>
      simp
  | succ l ih =>
      rw [iterateNormalizedStep_succ, coeff_normalizedStep, ih]
      ring

theorem polarTheta_natDegree_le {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) :
    (RealRooted.polarTheta N p).natDegree ≤ N := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro k hk
  rw [RealRooted.coeff_polarTheta]
  have hpcoeff : p.coeff k = 0 := by
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hk)
  simp [hpcoeff]

theorem thetaPlusOne_natDegree_le {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) :
    (RealRooted.thetaPlusOne p).natDegree ≤ N := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro k hk
  rw [RealRooted.coeff_thetaPlusOne]
  have hpcoeff : p.coeff k = 0 := by
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hk)
  simp [hpcoeff]

theorem normalizedStep_natDegree_le {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) :
    (normalizedStep N p).natDegree ≤ N := by
  calc
    (normalizedStep N p).natDegree ≤
        (RealRooted.thetaPlusOne (RealRooted.polarTheta N p)).natDegree := by
      exact Polynomial.natDegree_C_mul_le _ _
    _ ≤ N := thetaPlusOne_natDegree_le (polarTheta_natDegree_le hp)

theorem iterateNormalizedStep_natDegree_le (N l : ℕ) {p : ℝ[X]}
    (hp : p.natDegree ≤ N) :
    (iterateNormalizedStep N l p).natDegree ≤ N := by
  induction l generalizing p with
  | zero =>
      simpa using hp
  | succ l ih =>
      rw [iterateNormalizedStep_succ]
      exact normalizedStep_natDegree_le (ih hp)

theorem normalizedStep_isPF (_std : StandardFacts) {N : ℕ} (hN : 0 < N)
    {p : ℝ[X]} (hp : RealRooted.IsPFPolynomial p) (hdeg : p.natDegree ≤ N) :
    RealRooted.IsPFPolynomial (normalizedStep N p) := by
  unfold normalizedStep
  exact RealRooted.IsPFPolynomial.const_mul (by positivity)
    (RealRooted.thetaPlusOne_preserves_pf
      (RealRooted.polarTheta_preserves_pf hp hdeg))

theorem iterateNormalizedStep_isPF (std : StandardFacts) (N l : ℕ) (hN : 0 < N)
    {p : ℝ[X]} (hp : RealRooted.IsPFPolynomial p) (hdeg : p.natDegree ≤ N) :
    RealRooted.IsPFPolynomial (iterateNormalizedStep N l p) := by
  induction l generalizing p with
  | zero =>
      simpa using hp
  | succ l ih =>
      rw [iterateNormalizedStep_succ]
      exact normalizedStep_isPF std hN (ih hp hdeg)
        (iterateNormalizedStep_natDegree_le N l hdeg)

theorem normalizedRow_natDegree_le (l n : ℕ) :
    (normalizedRow l n).natDegree ≤ n - 1 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro k hk
  rw [coeff_normalizedRow]
  have hnot : ¬ k < n := by
    lia
  simp [hnot]

theorem normalizedRow_one (l : ℕ) :
    normalizedRow l 1 = 1 := by
  ext k
  simp [normalizedRow, superEulerianCoeff]

private theorem normalizedTransfer_ratio_left (d k : ℕ) (hk : k < d) :
    (((d : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) * (((d : ℝ) + 1) - k))) /
        (Nat.choose d k : ℝ) =
      ((d + 1 - k : ℕ) : ℝ) / (Nat.choose (d + 1) (k + 1) : ℝ) := by
  have hNne : ((d : ℝ) + 1) ≠ 0 := by positivity
  have hchooseDk0 : (Nat.choose d k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero (Nat.le_of_lt hk))
  have hchooseD1k10 : (Nat.choose (d + 1) (k + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero (by lia : k + 1 ≤ d + 1))
  have h1 : ((d : ℝ) + 1) * (Nat.choose d k : ℝ) =
      (Nat.choose (d + 1) (k + 1) : ℝ) * ((k : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq d k
  have hsub : (d : ℝ) + 1 - (k : ℝ) = ((d + 1 - k : ℕ) : ℝ) := by
    have hsub' :
        (((d + 1 : ℕ) : ℝ) - (k : ℝ)) = ((d + 1 - k : ℕ) : ℝ) := by
      exact (Nat.cast_sub (by lia : k ≤ d + 1)).symm
    norm_num [Nat.cast_add] at hsub'
    exact hsub'
  field_simp [hNne, hchooseDk0, hchooseD1k10]
  rw [hsub]
  nlinarith [h1]

private theorem normalizedTransfer_ratio_right (d k : ℕ) (hk : k < d) :
    (((d : ℝ) + 1)⁻¹ * (((k : ℝ) + 1 + 1) * ((d : ℝ) - k))) /
        (Nat.choose d (k + 1) : ℝ) =
      ((k : ℝ) + 1 + 1) / (Nat.choose (d + 1) (k + 1) : ℝ) := by
  have hNne : ((d : ℝ) + 1) ≠ 0 := by positivity
  have hchooseDk1 : (Nat.choose d (k + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero (Nat.succ_le_of_lt hk))
  have hchooseD1k10 : (Nat.choose (d + 1) (k + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero (by lia : k + 1 ≤ d + 1))
  have h2 : (Nat.choose d (k + 1) : ℝ) * ((d : ℝ) + 1) =
      (Nat.choose (d + 1) (k + 1) : ℝ) * ((d - k : ℕ) : ℝ) := by
    have h := Nat.choose_mul_succ_eq d (k + 1)
    rw [show d + 1 - (k + 1) = d - k by lia] at h
    exact_mod_cast h
  have hsub : (d : ℝ) - (k : ℝ) = ((d - k : ℕ) : ℝ) := by
    exact (Nat.cast_sub (by lia : k ≤ d)).symm
  field_simp [hNne, hchooseDk1, hchooseD1k10]
  rw [hsub]
  nlinarith [h2]

/-- Project-specific coefficient identity for the normalized transfer. -/
theorem normalizedTransferIdentity (l n : ℕ) (hn : 1 < n) :
    normalizedRow l n =
      (X + 1) * iterateNormalizedStep (n - 1) l (normalizedRow l (n - 1)) := by
  cases n with
  | zero =>
      contradiction
  | succ n =>
      cases n with
      | zero =>
          contradiction
      | succ d =>
          ext k
          let P := iterateNormalizedStep (d + 1) l (normalizedRow l (d + 1))
          change (normalizedRow l (d + 2)).coeff k = ((X + 1) * P).coeff k
          rw [show (X + 1 : ℝ[X]) * P = X * P + P by ring, coeff_add]
          cases k with
          | zero =>
              suffices hzero : superEulerianCoeff l (d + 1) 0 =
                  (((d : ℝ) + 1)⁻¹ * ((d : ℝ) + 1)) ^ l *
                    superEulerianCoeff l (d + 1) 0 by
                simpa [P, normalizedRow, superEulerianCoeff] using hzero
              have hfactor : ((d : ℝ) + 1)⁻¹ * ((d : ℝ) + 1) = 1 := by
                field_simp
              rw [hfactor]
              simp
          | succ k =>
              rw [coeff_X_mul]
              by_cases hklt : k < d
              · suffices hmiddle :
                    ((((k : ℝ) + 1 + 1) ^ l *
                          superEulerianCoeff l (d + 1) (k + 1) +
                        ((d + 1 - k : ℕ) : ℝ) ^ l *
                          superEulerianCoeff l (d + 1) k) /
                        ((Nat.choose (d + 1) (k + 1) : ℝ) ^ l) =
                      ((((d : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) *
                            ((d : ℝ) + 1 - k))) ^ l) *
                          (superEulerianCoeff l (d + 1) k /
                            ((Nat.choose d k : ℝ) ^ l)) +
                        ((((d : ℝ) + 1)⁻¹ * (((k : ℝ) + 1 + 1) *
                              ((d : ℝ) - k))) ^ l) *
                          (superEulerianCoeff l (d + 1) (k + 1) /
                            ((Nat.choose d (k + 1) : ℝ) ^ l))) by
                  simpa [P, normalizedRow, superEulerianCoeff, hklt, Nat.le_of_lt hklt]
                    using hmiddle
                have hf1 := normalizedTransfer_ratio_left d k hklt
                have hf2 := normalizedTransfer_ratio_right d k hklt
                have hterm1 :
                    (((((d : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) *
                          ((d : ℝ) + 1 - k))) ^ l) *
                        (superEulerianCoeff l (d + 1) k /
                          ((Nat.choose d k : ℝ) ^ l))) =
                      (((d + 1 - k : ℕ) : ℝ) ^ l *
                          superEulerianCoeff l (d + 1) k) /
                        ((Nat.choose (d + 1) (k + 1) : ℝ) ^ l) := by
                  have hpow :
                      ((((d : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) *
                            ((d : ℝ) + 1 - k))) ^ l) /
                          ((Nat.choose d k : ℝ) ^ l) =
                        (((d + 1 - k : ℕ) : ℝ) ^ l) /
                          ((Nat.choose (d + 1) (k + 1) : ℝ) ^ l) := by
                    simpa [div_pow] using congrArg (fun x : ℝ => x ^ l) hf1
                  calc
                    (((((d : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) *
                          ((d : ℝ) + 1 - k))) ^ l) *
                        (superEulerianCoeff l (d + 1) k /
                          ((Nat.choose d k : ℝ) ^ l)))
                        = superEulerianCoeff l (d + 1) k *
                            (((((d : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) *
                                ((d : ℝ) + 1 - k))) ^ l) /
                              ((Nat.choose d k : ℝ) ^ l)) := by
                            ring
                    _ = superEulerianCoeff l (d + 1) k *
                            ((((d + 1 - k : ℕ) : ℝ) ^ l) /
                              ((Nat.choose (d + 1) (k + 1) : ℝ) ^ l)) := by
                            rw [hpow]
                    _ = (((d + 1 - k : ℕ) : ℝ) ^ l *
                          superEulerianCoeff l (d + 1) k) /
                        ((Nat.choose (d + 1) (k + 1) : ℝ) ^ l) := by
                            ring
                have hterm2 :
                    (((((d : ℝ) + 1)⁻¹ * (((k : ℝ) + 1 + 1) *
                          ((d : ℝ) - k))) ^ l) *
                        (superEulerianCoeff l (d + 1) (k + 1) /
                          ((Nat.choose d (k + 1) : ℝ) ^ l))) =
                      ((((k : ℝ) + 1 + 1) ^ l *
                          superEulerianCoeff l (d + 1) (k + 1)) /
                        ((Nat.choose (d + 1) (k + 1) : ℝ) ^ l)) := by
                  have hpow :
                      ((((d : ℝ) + 1)⁻¹ * (((k : ℝ) + 1 + 1) *
                            ((d : ℝ) - k))) ^ l) /
                          ((Nat.choose d (k + 1) : ℝ) ^ l) =
                        ((((k : ℝ) + 1 + 1) ^ l) /
                          ((Nat.choose (d + 1) (k + 1) : ℝ) ^ l)) := by
                    simpa [div_pow] using congrArg (fun x : ℝ => x ^ l) hf2
                  calc
                    (((((d : ℝ) + 1)⁻¹ * (((k : ℝ) + 1 + 1) *
                          ((d : ℝ) - k))) ^ l) *
                        (superEulerianCoeff l (d + 1) (k + 1) /
                          ((Nat.choose d (k + 1) : ℝ) ^ l)))
                        = superEulerianCoeff l (d + 1) (k + 1) *
                            (((((d : ℝ) + 1)⁻¹ * (((k : ℝ) + 1 + 1) *
                                ((d : ℝ) - k))) ^ l) /
                              ((Nat.choose d (k + 1) : ℝ) ^ l)) := by
                            ring
                    _ = superEulerianCoeff l (d + 1) (k + 1) *
                            ((((k : ℝ) + 1 + 1) ^ l) /
                              ((Nat.choose (d + 1) (k + 1) : ℝ) ^ l)) := by
                            rw [hpow]
                    _ = ((((k : ℝ) + 1 + 1) ^ l *
                          superEulerianCoeff l (d + 1) (k + 1)) /
                        ((Nat.choose (d + 1) (k + 1) : ℝ) ^ l)) := by
                            ring
                rw [hterm1, hterm2]
                ring
              · by_cases hkeq : k = d
                · subst k
                  suffices htop : superEulerianCoeff l (d + 1) d =
                      (((d : ℝ) + 1)⁻¹ * ((d : ℝ) + 1)) ^ l *
                        superEulerianCoeff l (d + 1) d by
                    simpa [P, normalizedRow, superEulerianCoeff,
                      superEulerianCoeff_eq_zero_of_le] using htop
                  have hfactor : ((d : ℝ) + 1)⁻¹ * ((d : ℝ) + 1) = 1 := by
                    field_simp
                  rw [hfactor]
                  simp
                · have hnotle : ¬ k ≤ d := by
                    lia
                  simp [P, normalizedRow, superEulerianCoeff, hklt, hnotle]

theorem normalizedRow_isPF (std : StandardFacts) {l n : ℕ}
    (_hl : 0 < l) (hn : 0 < n) :
    RealRooted.IsPFPolynomial (normalizedRow l n) := by
  induction n with
  | zero =>
      contradiction
  | succ n ih =>
      cases n with
      | zero =>
          rw [normalizedRow_one]
          exact isPFPolynomial_one
      | succ d =>
          rw [normalizedTransferIdentity l (d + 2) (by norm_num)]
          exact RealRooted.isPFPolynomial_mul_X_add_one
            (iterateNormalizedStep_isPF std (d + 1) l (by positivity)
              (ih (by positivity))
              ((normalizedRow_natDegree_le l (d + 1)).trans (by lia)))

theorem binomialKernel_isPF (std : StandardFacts) {l d : ℕ}
    (hl : 0 < l) :
    RealRooted.IsPFPolynomial (binomialKernel l d) := by
  cases l with
  | zero =>
      contradiction
  | succ l =>
      exact binomialKernel_succ_isPF std l d

theorem diagonalKernel_isPF (std : StandardFacts) {l d : ℕ}
    (hl : 0 < l) :
    RealRooted.IsPFPolynomial (diagonalKernel l d) := by
  rw [diagonalKernel_eq_iterateThetaPlusOne]
  exact StandardFacts.iterateThetaPlusOne_pf l (binomialKernel_isPF std hl)

theorem diagonalKernel_natDegree_le (l d : ℕ) :
    (diagonalKernel l d).natDegree ≤ d := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro k hk
  rw [coeff_diagonalKernel]
  have hnot : ¬k < d + 1 := by
    lia
  simp [hnot]

theorem reciprocalDiagonalKernel_one_isPF (d : ℕ) :
    RealRooted.IsPFPolynomial
      (RealRooted.reciprocalShift (d + 1) (diagonalKernel 1 d)) := by
  cases d with
  | zero =>
      simpa [RealRooted.reciprocalShift, diagonalKernel] using
        RealRooted.isPFPolynomial_X
  | succ e =>
      rw [reciprocalDiagonalKernel_one_eq_X_add_one_pow_mul_X_mul_linear
        (e + 1) (by positivity)]
      exact (isPFPolynomial_X_add_one_pow e).mul
        (RealRooted.isPFPolynomial_X.mul
          (RealRooted.isPFPolynomial_X_add_C
            (a := (((e + 1) + 1 : ℕ) : ℝ)) (by positivity)))

theorem reciprocalDiagonalKernel_succ_isPF (std : StandardFacts) (l d : ℕ) :
    RealRooted.IsPFPolynomial
      (RealRooted.reciprocalShift (d + 1) (diagonalKernel (l + 1) d)) := by
  induction l with
  | zero =>
      exact reciprocalDiagonalKernel_one_isPF d
  | succ l ih =>
      rw [reciprocalDiagonalKernel_succ_eq_hadamardProduct]
      exact std.hadamardPF
        (reciprocalDiagonalKernel_one_isPF d)
        ih

theorem reciprocalDiagonalKernel_isPF (std : StandardFacts) {l d : ℕ}
    (hl : 0 < l) :
    RealRooted.IsPFPolynomial
      (RealRooted.reciprocalShift (d + 1) (diagonalKernel l d)) := by
  cases l with
  | zero =>
      contradiction
  | succ l =>
      exact reciprocalDiagonalKernel_succ_isPF std l d

theorem row_hadamardFactorization (l n : ℕ) :
    row l n =
      RealRooted.hadamardProduct
        (binomialKernel l (n - 1))
        (normalizedRow l n) := by
  classical
  ext k
  rw [RealRooted.coeff_hadamardProduct]
  rw [coeff_row, coeff_binomialKernel, coeff_normalizedRow]
  by_cases hk : k < n
  · have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
    have hkernelRange : k < n - 1 + 1 := by
      rwa [Nat.sub_add_cancel hnpos]
    simp only [if_pos hk, if_pos hkernelRange]
    have hkn : k ≤ n - 1 := Nat.le_sub_one_of_lt hk
    have hchoose_pos : 0 < Nat.choose (n - 1) k := Nat.choose_pos hkn
    have hchoose_ne : ((Nat.choose (n - 1) k : ℝ) ^ l) ≠ 0 := by
      exact pow_ne_zero _ (by exact_mod_cast (ne_of_gt hchoose_pos))
    field_simp [hchoose_ne]
  · simp [hk]

theorem boundary_hadamardFactorization (l n : ℕ) :
    boundary l n =
      RealRooted.hadamardProduct
        (diagonalKernel l (n - 1))
        (normalizedRow l n) := by
  classical
  ext k
  rw [RealRooted.coeff_hadamardProduct]
  rw [coeff_boundary, coeff_diagonalKernel, coeff_normalizedRow]
  by_cases hk : k < n
  · have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
    have hkernelRange : k < n - 1 + 1 := by
      rwa [Nat.sub_add_cancel hnpos]
    simp only [if_pos hk, if_pos hkernelRange]
    have hkn : k ≤ n - 1 := Nat.le_sub_one_of_lt hk
    have hchoose_pos : 0 < Nat.choose (n - 1) k := Nat.choose_pos hkn
    have hchoose_ne : ((Nat.choose (n - 1) k : ℝ) ^ l) ≠ 0 := by
      exact pow_ne_zero _ (by exact_mod_cast (ne_of_gt hchoose_pos))
    field_simp [hchoose_ne]
  · simp [hk]

theorem reciprocalShift_normalizedRow_eq_X_mul (l n : ℕ) :
    RealRooted.reciprocalShift n (normalizedRow l n) = X * normalizedRow l n := by
  classical
  ext k
  rw [RealRooted.coeff_reciprocalShift]
  cases k with
  | zero =>
      simp
  | succ k =>
      by_cases hk : k + 1 ≤ n
      · have hrev : Polynomial.revAt n (k + 1) = n - (k + 1) := by
          simpa using Polynomial.revAt_le hk
        by_cases hn0 : n = 0
        · subst n
          simp at hk
        · have hrev_lt : n - (k + 1) < n := by
            lia
          have hkpred : k < n := by
            lia
          have hsym :
              superEulerianCoeff l n (n - (k + 1)) = superEulerianCoeff l n k := by
            have h := superEulerianCoeff_palindromic l n k hkpred
            have harith : n - 1 - k = n - (k + 1) := by
              lia
            simpa [harith] using h
          have hchoose :
              Nat.choose (n - 1) (n - (k + 1)) = Nat.choose (n - 1) k := by
            have hle : k ≤ n - 1 := by
              lia
            have harith : n - 1 - k = n - (k + 1) := by
              lia
            rw [← harith]
            exact Nat.choose_symm hle
          simp [hrev, hrev_lt, hkpred, coeff_X_mul, hsym, hchoose]
      · have hkgt : n < k + 1 := by
          lia
        have hrev : Polynomial.revAt n (k + 1) = k + 1 :=
          Polynomial.revAt_eq_self_of_lt hkgt
        have hknot : ¬k < n := by
          lia
        have hsuccnot : ¬k + 1 < n := by
          lia
        simp [hrev, hknot, hsuccnot, coeff_X_mul]

theorem reciprocalBoundary_hadamardFactorization (l n : ℕ) :
    reciprocalBoundary l n =
      RealRooted.hadamardProduct
        (RealRooted.reciprocalShift n (diagonalKernel l (n - 1)))
        (X * normalizedRow l n) := by
  rw [reciprocalBoundary, boundary_hadamardFactorization]
  rw [RealRooted.reciprocalShift_hadamardProduct]
  rw [reciprocalShift_normalizedRow_eq_X_mul]

theorem row_succ_boundaryDecomposition (l n : ℕ) (hn : 0 < n) :
    row l (n + 1) = boundary l n + reciprocalBoundary l n := by
  classical
  cases n with
  | zero =>
      contradiction
  | succ d =>
      ext k
      rw [coeff_row, coeff_add, coeff_boundary]
      rw [reciprocalBoundary, RealRooted.coeff_reciprocalShift, coeff_boundary]
      by_cases hkrow : k < d + 1 + 1
      · have hk_le : k ≤ d + 1 := Nat.lt_succ_iff.mp hkrow
        by_cases hk0 : k = 0
        · subst k
          simp [superEulerianCoeff]
        · have hrev : Polynomial.revAt (d + 1) k = d + 1 - k := by
            simpa using Polynomial.revAt_le hk_le
          by_cases hktop : k = d + 1
          · subst k
            have hsymTop :
                superEulerianCoeff l (d + 1) d =
                  superEulerianCoeff l (d + 1) 0 := by
              simpa using superEulerianCoeff_palindromic l (d + 1) 0 (by lia)
            simp [superEulerianCoeff, superEulerianCoeff_eq_zero_of_le, hrev, hsymTop]
          · have hk_lt_prev : k < d + 1 := by
              lia
            have hrev_lt : d + 1 - k < d + 1 := by
              lia
            have hsym :
                superEulerianCoeff l (d + 1) (d + 1 - k) =
                  superEulerianCoeff l (d + 1) (k - 1) := by
              have h := superEulerianCoeff_palindromic l (d + 1) (k - 1) (by lia)
              have harith : d - (k - 1) = d + 1 - k := by
                lia
              simpa [harith] using h
            rw [if_pos hkrow, if_pos hk_lt_prev, hrev, if_pos hrev_lt]
            simp only [superEulerianCoeff]
            rw [hsym]
            simp only [hk0, if_false]
            rw [show d + 1 - k + 1 = d + 2 - k by lia]
      · have hk_not_prev : ¬k < d + 1 := by
          lia
        have hk_gt : d + 1 < k := by
          lia
        have hrev : Polynomial.revAt (d + 1) k = k :=
          Polynomial.revAt_eq_self_of_lt hk_gt
        simp [hkrow, hk_not_prev, hrev]

private theorem X_add_C_ne_zero (a : ℝ) : (X + C a : ℝ[X]) ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 1) h
  simp at hcoeff

private theorem C_mul_X_add_one_ne_zero (a : ℝ) :
    (C a * X + 1 : ℝ[X]) ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) h
  simp at hcoeff

private theorem kernelDiagonalBase_linear_prec0 (d : ℕ) :
    RealRooted.Prec0 (X + 1 : ℝ[X])
      (C ((d + 1 : ℕ) : ℝ) * X + 1) := by
  have hcross : (1 : ℝ) * 1 ≤ ((d + 1 : ℕ) : ℝ) * 1 := by
    have h : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    nlinarith
  simpa using
    RealRooted.prec0_affine_linear_affine_linear_of_cross
      (u := 1) (v := 1) (U := ((d + 1 : ℕ) : ℝ)) (V := 1)
      (by norm_num) (by positivity) hcross

theorem kernel_prec_diagonal_one (d : ℕ) :
    RealRooted.Prec0 (binomialKernel 1 d) (diagonalKernel 1 d) := by
  cases d with
  | zero =>
      rw [binomialKernel_one_eq_X_add_one_pow]
      simpa [diagonalKernel] using RealRooted.isPFPolynomial_one.prec0_self
  | succ e =>
      rw [binomialKernel_one_eq_X_add_one_pow]
      rw [diagonalKernel_one_eq_X_add_one_pow_mul_linear (e + 1) (by positivity)]
      rw [pow_succ]
      have hbase0 := kernelDiagonalBase_linear_prec0 (e + 1)
      have hbase : RealRooted.Prec (X + 1 : ℝ[X])
          (C (((e + 1) + 1 : ℕ) : ℝ) * X + 1) :=
        hbase0.toPrec_of_ne (X_add_C_ne_zero 1)
          (C_mul_X_add_one_ne_zero (((e + 1) + 1 : ℕ) : ℝ))
      exact (RealRooted.prec_mul_common_factor
        (RealRooted.isRealRooted_X_add_one_pow e).1
        (RealRooted.isRealRooted_X_add_one_pow e).2 hbase).toPrec0

theorem kernel_prec_diagonal_succ (std : StandardFacts) (l d : ℕ) :
    RealRooted.Prec0 (binomialKernel (l + 1) d) (diagonalKernel (l + 1) d) := by
  induction l with
  | zero =>
      exact kernel_prec_diagonal_one d
  | succ l ih =>
      rw [binomialKernel_succ_eq_hadamardProduct]
      rw [diagonalKernel_succ_eq_hadamardProduct]
      exact std.garloffWagnerPFPrec0
        (binomialKernel_isPF std (by norm_num))
        (diagonalKernel_isPF std (by norm_num))
        (binomialKernel_isPF std (by positivity))
        (diagonalKernel_isPF std (by positivity))
        (kernel_prec_diagonal_one d)
        ih

theorem kernel_prec_diagonal (std : StandardFacts) {l d : ℕ} (hl : 0 < l) :
    RealRooted.Prec0 (binomialKernel l d) (diagonalKernel l d) := by
  cases l with
  | zero =>
      contradiction
  | succ l =>
      exact kernel_prec_diagonal_succ std l d

private theorem kernelBase_linear_prec0 (d : ℕ) :
    RealRooted.Prec0 (X + 1 : ℝ[X]) (X * (X + C ((d + 1 : ℕ) : ℝ))) := by
  have hbase :
      RealRooted.Prec0 (X + C ((d + 1 : ℕ) : ℝ) : ℝ[X]) (X + 1) := by
    have hcross : (1 : ℝ) * 1 ≤ 1 * ((d + 1 : ℕ) : ℝ) := by
      have h : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
      nlinarith
    simpa using
      RealRooted.prec0_affine_linear_affine_linear_of_cross
        (u := 1) (v := ((d + 1 : ℕ) : ℝ)) (U := 1) (V := 1)
        (by norm_num) (by norm_num) hcross
  exact RealRooted.prec0_mul_X_of_prec0 hbase
    (RealRooted.hasNonnegCoeffs_X.add (RealRooted.hasNonnegCoeffs_C (by positivity)))
    (by simpa using RealRooted.hasNonnegCoeffs_X_add_one)

private theorem diagonalBase_linear_prec0 (d : ℕ) :
    RealRooted.Prec0 (C ((d + 1 : ℕ) : ℝ) * X + 1 : ℝ[X])
      (X * (X + C ((d + 1 : ℕ) : ℝ))) := by
  have hbase :
      RealRooted.Prec0 (X + C ((d + 1 : ℕ) : ℝ) : ℝ[X])
        (C ((d + 1 : ℕ) : ℝ) * X + 1) := by
    have hcross :
        (1 : ℝ) * 1 ≤ ((d + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ) := by
      have h : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
      nlinarith
    have hU : 0 < ((d + 1 : ℕ) : ℝ) := by positivity
    simpa using
      RealRooted.prec0_affine_linear_affine_linear_of_cross
        (u := 1) (v := ((d + 1 : ℕ) : ℝ))
        (U := ((d + 1 : ℕ) : ℝ)) (V := 1)
        (by norm_num) hU hcross
  exact RealRooted.prec0_mul_X_of_prec0 hbase
    (RealRooted.hasNonnegCoeffs_X.add (RealRooted.hasNonnegCoeffs_C (by positivity)))
    ((RealRooted.nonnegCoeffs_C_mul (by positivity) RealRooted.hasNonnegCoeffs_X).add
      RealRooted.hasNonnegCoeffs_one)

theorem kernel_prec_reciprocalDiagonal_one (d : ℕ) :
    RealRooted.Prec0
      (binomialKernel 1 d)
      (RealRooted.reciprocalShift (d + 1) (diagonalKernel 1 d)) := by
  cases d with
  | zero =>
      rw [binomialKernel_one_eq_X_add_one_pow]
      simp [RealRooted.reciprocalShift, diagonalKernel]
      simpa using RealRooted.prec0_mul_X_of_prec0 isPFPolynomial_one.prec0_self
        RealRooted.hasNonnegCoeffs_one RealRooted.hasNonnegCoeffs_one
  | succ e =>
      rw [binomialKernel_one_eq_X_add_one_pow]
      rw [reciprocalDiagonalKernel_one_eq_X_add_one_pow_mul_X_mul_linear
        (e + 1) (by positivity)]
      rw [pow_succ]
      have hbase0 := kernelBase_linear_prec0 (e + 1)
      have hbase : RealRooted.Prec (X + 1 : ℝ[X])
          (X * (X + C (((e + 1) + 1 : ℕ) : ℝ))) :=
        hbase0.toPrec_of_ne (X_add_C_ne_zero 1)
          (mul_ne_zero X_ne_zero (X_add_C_ne_zero (((e + 1) + 1 : ℕ) : ℝ)))
      exact (RealRooted.prec_mul_common_factor
        (RealRooted.isRealRooted_X_add_one_pow e).1
        (RealRooted.isRealRooted_X_add_one_pow e).2 hbase).toPrec0

theorem diagonal_prec_reciprocalDiagonal_one (d : ℕ) :
    RealRooted.Prec0
      (diagonalKernel 1 d)
      (RealRooted.reciprocalShift (d + 1) (diagonalKernel 1 d)) := by
  cases d with
  | zero =>
      simp [RealRooted.reciprocalShift, diagonalKernel]
      simpa using RealRooted.prec0_mul_X_of_prec0 isPFPolynomial_one.prec0_self
        RealRooted.hasNonnegCoeffs_one RealRooted.hasNonnegCoeffs_one
  | succ e =>
      rw [reciprocalDiagonalKernel_one_eq_X_add_one_pow_mul_X_mul_linear
        (e + 1) (by positivity)]
      rw [diagonalKernel_one_eq_X_add_one_pow_mul_linear (e + 1) (by positivity)]
      have hbase0 := diagonalBase_linear_prec0 (e + 1)
      have hbase : RealRooted.Prec (C (((e + 1) + 1 : ℕ) : ℝ) * X + 1 : ℝ[X])
          (X * (X + C (((e + 1) + 1 : ℕ) : ℝ))) :=
        hbase0.toPrec_of_ne
          (C_mul_X_add_one_ne_zero (((e + 1) + 1 : ℕ) : ℝ))
          (mul_ne_zero X_ne_zero (X_add_C_ne_zero (((e + 1) + 1 : ℕ) : ℝ)))
      exact (RealRooted.prec_mul_common_factor
        (RealRooted.isRealRooted_X_add_one_pow e).1
        (RealRooted.isRealRooted_X_add_one_pow e).2 hbase).toPrec0

theorem kernel_prec_reciprocalDiagonal_succ (std : StandardFacts) (l d : ℕ) :
    RealRooted.Prec0
      (binomialKernel (l + 1) d)
      (RealRooted.reciprocalShift (d + 1) (diagonalKernel (l + 1) d)) := by
  induction l with
  | zero =>
      exact kernel_prec_reciprocalDiagonal_one d
  | succ l ih =>
      have hlSucc : 0 < l + 1 := by
        positivity
      rw [binomialKernel_succ_eq_hadamardProduct]
      rw [reciprocalDiagonalKernel_succ_eq_hadamardProduct]
      exact std.garloffWagnerPFPrec0
        (binomialKernel_isPF std (by norm_num))
        (reciprocalDiagonalKernel_isPF std (by norm_num))
        (binomialKernel_isPF std hlSucc)
        (reciprocalDiagonalKernel_isPF std hlSucc)
        (kernel_prec_reciprocalDiagonal_one d)
        ih

theorem kernel_prec_reciprocalDiagonal (std : StandardFacts) {l d : ℕ} (hl : 0 < l) :
    RealRooted.Prec0
      (binomialKernel l d)
      (RealRooted.reciprocalShift (d + 1) (diagonalKernel l d)) := by
  cases l with
  | zero =>
      contradiction
  | succ l =>
      exact kernel_prec_reciprocalDiagonal_succ std l d

theorem diagonal_prec_reciprocalDiagonal_succ (std : StandardFacts) (l d : ℕ) :
    RealRooted.Prec0
      (diagonalKernel (l + 1) d)
      (RealRooted.reciprocalShift (d + 1) (diagonalKernel (l + 1) d)) := by
  induction l with
  | zero =>
      exact diagonal_prec_reciprocalDiagonal_one d
  | succ l ih =>
      have hlSucc : 0 < l + 1 := by
        positivity
      rw [diagonalKernel_succ_eq_hadamardProduct]
      rw [RealRooted.reciprocalShift_hadamardProduct]
      exact std.garloffWagnerPFPrec0
        (diagonalKernel_isPF std (by norm_num))
        (reciprocalDiagonalKernel_isPF std (by norm_num))
        (diagonalKernel_isPF std hlSucc)
        (reciprocalDiagonalKernel_isPF std hlSucc)
        (diagonal_prec_reciprocalDiagonal_one d)
        ih

theorem diagonal_prec_reciprocalDiagonal (std : StandardFacts) {l d : ℕ} (hl : 0 < l) :
    RealRooted.Prec0
      (diagonalKernel l d)
      (RealRooted.reciprocalShift (d + 1) (diagonalKernel l d)) := by
  cases l with
  | zero =>
      contradiction
  | succ l =>
      exact diagonal_prec_reciprocalDiagonal_succ std l d

/-! ## Checked reductions -/

theorem row_isPF (std : StandardFacts) {l n : ℕ}
    (hl : 0 < l) (hn : 0 < n) :
    RealRooted.IsPFPolynomial (row l n) := by
  rw [row_hadamardFactorization]
  exact std.hadamardPF
    (binomialKernel_isPF std hl)
    (normalizedRow_isPF std hl hn)

theorem boundary_isPF (std : StandardFacts) {l n : ℕ}
    (hl : 0 < l) (hn : 0 < n) :
    RealRooted.IsPFPolynomial (boundary l n) := by
  rw [boundary_hadamardFactorization]
  exact std.hadamardPF
    (diagonalKernel_isPF std hl)
    (normalizedRow_isPF std hl hn)

theorem reciprocalBoundary_isPF (std : StandardFacts) {l n : ℕ}
    (hl : 0 < l) (hn : 0 < n) :
    RealRooted.IsPFPolynomial (reciprocalBoundary l n) := by
  rw [reciprocalBoundary_hadamardFactorization]
  have hK :
      RealRooted.IsPFPolynomial
        (RealRooted.reciprocalShift n (diagonalKernel l (n - 1))) := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)] using
      (reciprocalDiagonalKernel_isPF (std := std) (l := l) (d := n - 1) hl)
  exact std.hadamardPF
    hK
    ((normalizedRow_isPF std hl hn).X_mul)

theorem row_prec_boundary (std : StandardFacts) {l n : ℕ}
    (hl : 0 < l) (hn : 0 < n) :
    RealRooted.Prec0 (row l n) (boundary l n) := by
  rw [row_hadamardFactorization, boundary_hadamardFactorization]
  exact std.hadamardPrec0Right
    (binomialKernel_isPF std hl)
    (diagonalKernel_isPF std hl)
    (normalizedRow_isPF std hl hn)
    (kernel_prec_diagonal std hl)

theorem row_prec_reciprocalBoundary (std : StandardFacts) {l n : ℕ}
    (hl : 0 < l) (hn : 0 < n) :
    RealRooted.Prec0 (row l n) (reciprocalBoundary l n) := by
  rw [row_hadamardFactorization, reciprocalBoundary_hadamardFactorization]
  have hQ : RealRooted.IsPFPolynomial (normalizedRow l n) :=
    normalizedRow_isPF std hl hn
  have hQX : RealRooted.Prec0 (normalizedRow l n) (X * normalizedRow l n) :=
    RealRooted.prec0_mul_X_of_prec0
      hQ.prec0_self hQ.hasNonnegCoeffs hQ.hasNonnegCoeffs
  have hK :
      RealRooted.IsPFPolynomial
        (RealRooted.reciprocalShift n (diagonalKernel l (n - 1))) := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)] using
      (reciprocalDiagonalKernel_isPF (std := std) (l := l) (d := n - 1) hl)
  have hKR :
      RealRooted.Prec0
        (binomialKernel l (n - 1))
        (RealRooted.reciprocalShift n (diagonalKernel l (n - 1))) := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)] using
      (kernel_prec_reciprocalDiagonal std (l := l) (d := n - 1) hl)
  exact std.garloffWagnerPFPrec0
    (binomialKernel_isPF std hl)
    hK
    hQ
    hQ.X_mul
    hKR
    hQX

theorem boundary_prec_reciprocalBoundary (std : StandardFacts) {l n : ℕ}
    (hl : 0 < l) (hn : 0 < n) :
    RealRooted.Prec0 (boundary l n) (reciprocalBoundary l n) := by
  rw [boundary_hadamardFactorization, reciprocalBoundary_hadamardFactorization]
  have hQ : RealRooted.IsPFPolynomial (normalizedRow l n) :=
    normalizedRow_isPF std hl hn
  have hQX : RealRooted.Prec0 (normalizedRow l n) (X * normalizedRow l n) :=
    RealRooted.prec0_mul_X_of_prec0
      hQ.prec0_self hQ.hasNonnegCoeffs hQ.hasNonnegCoeffs
  have hK :
      RealRooted.IsPFPolynomial
        (RealRooted.reciprocalShift n (diagonalKernel l (n - 1))) := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)] using
      (reciprocalDiagonalKernel_isPF (std := std) (l := l) (d := n - 1) hl)
  have hDR :
      RealRooted.Prec0
        (diagonalKernel l (n - 1))
        (RealRooted.reciprocalShift n (diagonalKernel l (n - 1))) := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)] using
      (diagonal_prec_reciprocalDiagonal std (l := l) (d := n - 1) hl)
  exact std.garloffWagnerPFPrec0
    (diagonalKernel_isPF std hl)
    hK
    hQ
    hQ.X_mul
    hDR
    hQX

theorem boundary_prec_row_succ (std : StandardFacts) {l n : ℕ}
    (hl : 0 < l) (hn : 0 < n) :
    RealRooted.Prec0 (boundary l n) (row l (n + 1)) := by
  have hAA : RealRooted.Prec0 (boundary l n) (boundary l n) :=
    (boundary_isPF std hl hn).prec0_self
  have hAR : RealRooted.Prec0 (boundary l n) (reciprocalBoundary l n) :=
    boundary_prec_reciprocalBoundary std hl hn
  have hsum : RealRooted.Prec0 (boundary l n)
      (boundary l n + reciprocalBoundary l n) :=
    RealRooted.prec0_add_right_of_common_left_of_nonneg hAA hAR
      (boundary_isPF std hl hn).hasNonnegCoeffs
      (reciprocalBoundary_isPF std hl hn).hasNonnegCoeffs
  rwa [row_succ_boundaryDecomposition l n hn]

theorem row_consecutive_prec0 (std : StandardFacts) {l n : ℕ}
    (hl : 0 < l) (hn : 0 < n) :
    RealRooted.Prec0 (row l n) (row l (n + 1)) := by
  have hpA : RealRooted.Prec0 (row l n) (boundary l n) :=
    row_prec_boundary std hl hn
  have hpR : RealRooted.Prec0 (row l n) (reciprocalBoundary l n) :=
    row_prec_reciprocalBoundary std hl hn
  have hsum : RealRooted.Prec0 (row l n)
      (boundary l n + reciprocalBoundary l n) :=
    RealRooted.prec0_add_right_of_common_left_of_nonneg hpA hpR
      (boundary_isPF std hl hn).hasNonnegCoeffs
      (reciprocalBoundary_isPF std hl hn).hasNonnegCoeffs
  rwa [row_succ_boundaryDecomposition l n hn]

/-- Prefix interlacing in the closed-form prefix model.

This is the final reduction from the TeX proof.  It is obtained by applying
`theta + 1` to the endpoint interlacing between the previous boundary term and
the next row.
-/
theorem prefix_prec0 (std : StandardFacts) {l n m : ℕ}
    (hl : 0 < l) (hm : 1 < m) (hmn : m ≤ n) :
    RealRooted.Prec0 (prefixPoly l n (m - 1)) (prefixPoly l n m) := by
  let r := l * (n - m)
  have hmPredPos : 0 < m - 1 := Nat.sub_pos_of_lt hm
  have hmpos : 0 < m := lt_trans Nat.zero_lt_one hm
  have hmPredSucc : m - 1 + 1 = m :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hmpos)
  have hbase : RealRooted.Prec0 (boundary l (m - 1)) (row l m) := by
    simpa [hmPredSucc] using
      (boundary_prec_row_succ (std := std) (l := l) (n := m - 1) hl hmPredPos)
  have hBoundaryPF : RealRooted.IsPFPolynomial (boundary l (m - 1)) :=
    boundary_isPF std hl hmPredPos
  have hRowPF : RealRooted.IsPFPolynomial (row l m) :=
    row_isPF std hl hmpos
  have hiter :
      RealRooted.Prec0
        (RealRooted.iterateThetaPlusOne r (boundary l (m - 1)))
        (RealRooted.iterateThetaPlusOne r (row l m)) :=
    StandardFacts.iterateThetaPlusOne_prec0 std r hBoundaryPF hRowPF hbase
  have hleft :
      RealRooted.iterateThetaPlusOne r (boundary l (m - 1)) =
        prefixPoly l n (m - 1) := by
    have harith : r + l = l * (n - (m - 1)) := by
      dsimp [r]
      have hsub : n - (m - 1) = n - m + 1 := by
        lia
      rw [hsub, Nat.mul_add]
      simp
    unfold prefixPoly boundary RealRooted.iterateThetaPlusOne
    rw [← harith]
    rw [← Function.iterate_add_apply]
  have hright :
      RealRooted.iterateThetaPlusOne r (row l m) = prefixPoly l n m := by
    simp [prefixPoly, r]
  rwa [hleft, hright] at hiter

end SuperEulerian
