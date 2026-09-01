import RealRooted.BorceaBranden.Applications.AffineFiniteSymbol

open Polynomial
open scoped BigOperators
open RealRooted

noncomputable section

namespace RealRooted.BorceaBranden

def eulerAlpha (k : ℕ) : ℝ := k + 1
def eulerBeta (d k : ℕ) : ℝ := d + 1 - k

def eulerAlphaWithConstant (c : ℝ) (k : ℕ) : ℝ := c + k

theorem eulerAffineBidiagonalSymbolWithConstant_eq
    (c : ℝ) (d : ℕ) (hd : 1 ≤ d) :
    affineBidiagonalSymbol (eulerAlphaWithConstant c) (eulerBeta d) d =
      (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (d - 1) *
        (MvPolynomial.X 0 ^ 2 +
          MvPolynomial.C ((d + 1 : ℕ) : ℝ) * MvPolynomial.X 0 * MvPolynomial.X 1 +
          MvPolynomial.C ((d : ℝ) + c) * MvPolynomial.X 0 +
          MvPolynomial.C c * MvPolynomial.X 1) := by
  let x : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0
  let y : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 1
  let S : MvPolynomial (Fin 2) ℝ := (x + y) ^ d
  have hdx : MvPolynomial.pderiv 0 x = 1 := by simp [x]
  have hdy : MvPolynomial.pderiv 0 y = 0 := by simp [y]
  have htermder (k : ℕ) :
      x * MvPolynomial.pderiv 0
          (MvPolynomial.C (d.choose k : ℝ) * x ^ k * y ^ (d - k)) =
        MvPolynomial.C (k : ℝ) *
          (MvPolynomial.C (d.choose k : ℝ) * x ^ k * y ^ (d - k)) := by
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_C, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_pow, hdx, hdy]
    cases k with
    | zero => simp
    | succ k =>
        rw [show k + 1 - 1 = k by omega, pow_succ]
        push_cast
        rw [show MvPolynomial.C ((k : ℝ) + 1) =
          MvPolynomial.C (k : ℝ) + (1 : MvPolynomial (Fin 2) ℝ) by
            rw [map_add, map_one]]
        rw [map_natCast]
        rw [show MvPolynomial.C (k : ℝ) =
          (k : MvPolynomial (Fin 2) ℝ) by exact map_natCast _ k]
        ring
  have hS : S = ∑ k ∈ Finset.range (d + 1),
      MvPolynomial.C (d.choose k : ℝ) * x ^ k * y ^ (d - k) := by
    dsimp [S]
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    simp
    ring
  have hder : MvPolynomial.pderiv 0 S =
      MvPolynomial.C (d : ℝ) * (x + y) ^ (d - 1) := by
    dsimp [S]
    rw [MvPolynomial.pderiv_pow]
    simp [x, y]
  have hA : ∑ k ∈ Finset.range (d + 1),
      MvPolynomial.C (d.choose k : ℝ) *
        (MvPolynomial.C (eulerAlphaWithConstant c k) * x ^ k) * y ^ (d - k) =
      x * MvPolynomial.pderiv 0 S + MvPolynomial.C c * S := by
    rw [hS]
    simp only [map_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [htermder]
    simp [eulerAlphaWithConstant]
    ring
  have hB : ∑ k ∈ Finset.range (d + 1),
      MvPolynomial.C (d.choose k : ℝ) *
        (MvPolynomial.C (eulerBeta d k) * x ^ (k + 1)) * y ^ (d - k) =
      x * (MvPolynomial.C ((d + 1 : ℕ) : ℝ) * S -
        x * MvPolynomial.pderiv 0 S) := by
    rw [hS]
    simp only [map_sum, Finset.mul_sum, mul_sub]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    unfold eulerBeta
    rw [htermder]
    simp [pow_succ]
    ring
  rw [affineBidiagonalSymbol]
  change (∑ k ∈ Finset.range (d + 1),
      MvPolynomial.C (d.choose k : ℝ) *
        (MvPolynomial.C (eulerAlphaWithConstant c k) * x ^ k +
          MvPolynomial.C (eulerBeta d k) * x ^ (k + 1)) * y ^ (d - k)) = _
  rw [show (∑ k ∈ Finset.range (d + 1),
      MvPolynomial.C (d.choose k : ℝ) *
        (MvPolynomial.C (eulerAlphaWithConstant c k) * x ^ k +
          MvPolynomial.C (eulerBeta d k) * x ^ (k + 1)) * y ^ (d - k)) =
      (∑ k ∈ Finset.range (d + 1),
        MvPolynomial.C (d.choose k : ℝ) *
          (MvPolynomial.C (eulerAlphaWithConstant c k) * x ^ k) * y ^ (d - k)) +
      (∑ k ∈ Finset.range (d + 1),
        MvPolynomial.C (d.choose k : ℝ) *
          (MvPolynomial.C (eulerBeta d k) * x ^ (k + 1)) * y ^ (d - k)) by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring, hA, hB]
  rw [hder]
  dsimp [S]
  dsimp [x, y]
  push_cast
  have hpow :
      (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ) ^ d =
        (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (d - 1) *
          (MvPolynomial.X 0 + MvPolynomial.X 1) := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
  rw [hpow]
  rw [show MvPolynomial.C ((d : ℝ) + 1) =
    MvPolynomial.C (d : ℝ) + (1 : MvPolynomial (Fin 2) ℝ) by
      rw [map_add, map_one]]
  rw [show MvPolynomial.C ((d : ℝ) + c) =
    MvPolynomial.C (d : ℝ) + MvPolynomial.C c by rw [map_add]]
  ring

theorem eulerAffineBidiagonalSymbol_eq (d : ℕ) (hd : 1 ≤ d) :
    affineBidiagonalSymbol eulerAlpha (eulerBeta d) d =
      (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (d - 1) *
        (MvPolynomial.X 0 ^ 2 +
          MvPolynomial.C ((d + 1 : ℕ) : ℝ) * MvPolynomial.X 0 * MvPolynomial.X 1 +
          MvPolynomial.C ((d + 1 : ℕ) : ℝ) * MvPolynomial.X 0 +
          MvPolynomial.X 1) := by
  have halpha : eulerAlphaWithConstant 1 = eulerAlpha := by
    funext k
    simp [eulerAlpha, eulerAlphaWithConstant]
    ring
  rw [← halpha]
  simpa using eulerAffineBidiagonalSymbolWithConstant_eq (1 : ℝ) d hd

/-- The irreducible quadratic factor of the Euler bidiagonal symbol is stable.
The proof is the explicit imaginary-part calculation obtained by solving the
polynomial for its second variable. -/
theorem eulerAffineBidiagonalResidualWithConstant_stable
    (c : ℝ) (hc : 1 ≤ c) (d : ℕ) (hd : 1 ≤ d) :
    MvUpperHalfPlaneStable (complexifyMv
      ((MvPolynomial.X 0 ^ 2 +
        MvPolynomial.C ((d + 1 : ℕ) : ℝ) * MvPolynomial.X 0 * MvPolynomial.X 1 +
        MvPolynomial.C ((d : ℝ) + c) * MvPolynomial.X 0 +
        MvPolynomial.C c * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ))) := by
  intro z hz
  simp [complexifyMv]
  intro hzero
  have hb : 0 < (z 0).im := hz 0
  have he : 0 < (z 1).im := hz 1
  have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hD : 0 < (d : ℝ) + 1 := by positivity
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hre := congrArg Complex.re hzero
  have him := congrArg Complex.im hzero
  simp [Complex.mul_re, Complex.mul_im, pow_two] at hre him
  have hbracket :
      0 < ((d : ℝ) + 1) * ((z 0).re ^ 2 + (z 0).im ^ 2) +
        2 * c * (z 0).re + ((d : ℝ) + 1) * c + c ^ 2 - c := by
    have hid :
        ((d : ℝ) + 1) *
            (((d : ℝ) + 1) * ((z 0).re ^ 2 + (z 0).im ^ 2) +
              2 * c * (z 0).re + ((d : ℝ) + 1) * c + c ^ 2 - c) =
          (((d : ℝ) + 1) * (z 0).re + c) ^ 2 +
            (((d : ℝ) + 1) * (z 0).im) ^ 2 +
            c * ((d : ℝ) + 1 - 1) * ((d : ℝ) + 1 + c) := by ring
    have hrem :
        0 < c * ((d : ℝ) + 1 - 1) * ((d : ℝ) + 1 + c) := by
      have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hd)
      have hmiddle : 0 < (d : ℝ) + 1 - 1 := by linarith
      have hlast : 0 < (d : ℝ) + 1 + c := by linarith
      exact mul_pos (mul_pos hcpos hmiddle) hlast
    nlinarith [sq_nonneg (((d : ℝ) + 1) * (z 0).re + c),
      sq_nonneg (((d : ℝ) + 1) * (z 0).im)]
  have hcombo :
      (z 1).im *
          ((((d : ℝ) + 1) * (z 0).re + c) ^ 2 +
            (((d : ℝ) + 1) * (z 0).im) ^ 2) +
        (z 0).im *
          (((d : ℝ) + 1) * ((z 0).re ^ 2 + (z 0).im ^ 2) +
            2 * c * (z 0).re + ((d : ℝ) + 1) * c + c ^ 2 - c) = 0 := by
    linear_combination
      (((d : ℝ) + 1) * (z 0).re + c) * him -
        (((d : ℝ) + 1) * (z 0).im) * hre
  have hdenpos :
      0 < (((d : ℝ) + 1) * (z 0).re + c) ^ 2 +
        (((d : ℝ) + 1) * (z 0).im) ^ 2 := by
    have himul : 0 < ((d : ℝ) + 1) * (z 0).im := mul_pos hD hb
    nlinarith [sq_nonneg (((d : ℝ) + 1) * (z 0).re + c),
      sq_pos_of_pos himul]
  nlinarith [mul_pos he hdenpos, mul_pos hb hbracket]

theorem eulerAffineBidiagonalResidual_stable (d : ℕ) (hd : 1 ≤ d) :
    MvUpperHalfPlaneStable (complexifyMv
      ((MvPolynomial.X 0 ^ 2 +
        MvPolynomial.C ((d + 1 : ℕ) : ℝ) * MvPolynomial.X 0 * MvPolynomial.X 1 +
        MvPolynomial.C ((d + 1 : ℕ) : ℝ) * MvPolynomial.X 0 +
        MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ))) := by
  simpa using eulerAffineBidiagonalResidualWithConstant_stable (1 : ℝ)
    (by norm_num) d hd

/-- The genuine finite symbol remains stable when the constant diagonal weight
is any real `c ≥ 1`. -/
theorem eulerAffineBidiagonalSymbolWithConstant_stable
    (c : ℝ) (hc : 1 ≤ c) (d : ℕ) (hd : 1 ≤ d) :
    MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d
          (bidiagonalLinearMap (eulerAlphaWithConstant c) (eulerBeta d)))) := by
  rw [finiteAlgebraicSymbol_bidiagonalLinearMap,
    eulerAffineBidiagonalSymbolWithConstant_eq c d hd]
  simpa [complexifyMv] using
    (eulerAffineBidiagonalResidualWithConstant_stable c hc d hd).mul_X_add_X_pow
      0 1 (d - 1)

/-- The genuine finite algebraic symbol of the Euler bidiagonal operator is
upper-half-plane stable on every positive degree box. -/
theorem eulerAffineBidiagonalSymbol_stable (d : ℕ) (hd : 1 ≤ d) :
    MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d
          (bidiagonalLinearMap eulerAlpha (eulerBeta d)))) := by
  rw [finiteAlgebraicSymbol_bidiagonalLinearMap,
    eulerAffineBidiagonalSymbol_eq d hd]
  simpa [complexifyMv] using
    (eulerAffineBidiagonalResidual_stable d hd).mul_X_add_X_pow 0 1 (d - 1)

/-- The Euler coefficient-bidiagonal step in the derivative form used by the
generated OEIS recurrences. -/
def eulerBidiagonalStep (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (1 + C ((d : ℝ) + 1) * X) * p + (X - X ^ 2) * p.derivative

/-- The Euler step with an arbitrary constant diagonal weight. -/
def eulerBidiagonalStepWithConstant (c : ℝ) (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (C c + C ((d : ℝ) + 1) * X) * p + (X - X ^ 2) * p.derivative

theorem eulerBidiagonalStepWithConstant_eq_bidiagonalOperator
    (c : ℝ) (d : ℕ) (p : ℝ[X]) :
    eulerBidiagonalStepWithConstant c d p =
      bidiagonalOperator (eulerAlphaWithConstant c) (eulerBeta d) p := by
  have hform : eulerBidiagonalStepWithConstant c d p =
      C c * p + C ((d : ℝ) + 1) * (X * p) + X * p.derivative -
        X ^ 2 * p.derivative := by
    simp [eulerBidiagonalStepWithConstant]
    ring
  rw [hform]
  ext k
  cases k with
  | zero => simp [bidiagonalOperator, eulerAlphaWithConstant]
  | succ k =>
      cases k <;>
        simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul,
          coeff_X_pow_mul', coeff_derivative,
          coeff_bidiagonalOperator_succ] <;>
        simp [eulerAlphaWithConstant, eulerBeta] <;> ring

/-- On its natural degree box, a nonzero positive-leading input gains exactly
one degree under the Euler step and keeps positive leading coefficient. -/
theorem eulerBidiagonalStepWithConstant_degree_pos
    {c : ℝ} {d : ℕ} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hp : HasPosLeadingCoeff p) :
    (eulerBidiagonalStepWithConstant c d p).natDegree = p.natDegree + 1 ∧
      HasPosLeadingCoeff (eulerBidiagonalStepWithConstant c d p) := by
  let m := p.natDegree
  have hcoeff :
      (eulerBidiagonalStepWithConstant c d p).coeff (m + 1) =
        ((d : ℝ) + 1 - (m : ℝ)) * p.leadingCoeff := by
    rw [eulerBidiagonalStepWithConstant_eq_bidiagonalOperator,
      coeff_bidiagonalOperator_succ]
    have hzero : p.coeff (m + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simp [m])
    rw [hzero, mul_zero, zero_add]
    have htop : p.coeff m = p.leadingCoeff := by
      exact p.coeff_natDegree
    rw [htop]
    simp [eulerBeta]
  have hbeta : 0 < (d : ℝ) + 1 - (m : ℝ) := by
    have hcast : (m : ℝ) ≤ (d : ℝ) := by exact_mod_cast hpdeg
    linarith
  have hcoeff_pos :
      0 < (eulerBidiagonalStepWithConstant c d p).coeff (m + 1) := by
    rw [hcoeff]
    exact mul_pos hbeta hp
  have hupper :
      (eulerBidiagonalStepWithConstant c d p).natDegree ≤ m + 1 := by
    rw [eulerBidiagonalStepWithConstant_eq_bidiagonalOperator]
    exact natDegree_bidiagonalOperator_le _ _ _
  have hdegree :
      (eulerBidiagonalStepWithConstant c d p).natDegree = m + 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero hupper hcoeff_pos.ne'
  refine ⟨hdegree, ?_⟩
  rw [HasPosLeadingCoeff, leadingCoeff, hdegree]
  exact hcoeff_pos

theorem eulerBidiagonalStep_eq_stepWithConstant_one (d : ℕ) (p : ℝ[X]) :
    eulerBidiagonalStep d p = eulerBidiagonalStepWithConstant 1 d p := by
  simp [eulerBidiagonalStep, eulerBidiagonalStepWithConstant]

/-- The derivative presentation of the Euler step is exactly the bidiagonal
operator certified by `eulerAffineBidiagonalSymbol_stable`. -/
theorem eulerBidiagonalStep_eq_bidiagonalOperator (d : ℕ) (p : ℝ[X]) :
    eulerBidiagonalStep d p =
      bidiagonalOperator eulerAlpha (eulerBeta d) p := by
  have hform : eulerBidiagonalStep d p =
      p + C ((d : ℝ) + 1) * (X * p) + X * p.derivative -
        X ^ 2 * p.derivative := by
    simp [eulerBidiagonalStep]
    ring
  rw [hform]
  ext k
  cases k with
  | zero => simp [bidiagonalOperator, eulerAlpha]
  | succ k =>
      cases k <;>
        simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul,
          coeff_X_pow_mul', coeff_derivative,
          coeff_bidiagonalOperator_succ] <;>
        simp [eulerAlpha, eulerBeta] <;> ring

theorem eulerBidiagonalStepWithConstant_eq_zero_or_splits
    {c : ℝ} (hc : 1 ≤ c) {d : ℕ} (hd : 1 ≤ d) {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hp : p.Splits) :
    eulerBidiagonalStepWithConstant c d p = 0 ∨
      (eulerBidiagonalStepWithConstant c d p).Splits := by
  rw [eulerBidiagonalStepWithConstant_eq_bidiagonalOperator]
  exact bidiagonalOperator_splits_of_affineSymbol_stable
    (eulerAffineBidiagonalSymbolWithConstant_stable c hc d hd) hpdeg hp

theorem eulerBidiagonalStepWithConstant_splits
    {c : ℝ} (hc : 1 ≤ c) {d : ℕ} (hd : 1 ≤ d) {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hpPos : HasPosLeadingCoeff p)
    (hp : p.Splits) : (eulerBidiagonalStepWithConstant c d p).Splits := by
  rcases eulerBidiagonalStepWithConstant_eq_zero_or_splits hc hd hpdeg hp with
    hzero | hsplits
  · have hout :=
      (eulerBidiagonalStepWithConstant_degree_pos (c := c) hpdeg hpPos).2
    exact (hout.ne_zero hzero).elim
  · exact hsplits

theorem eulerBidiagonalStepWithConstant_prec
    {c : ℝ} (hc : 1 ≤ c) {d : ℕ} (hd : 1 ≤ d) {p q : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d)
    (hpq : Prec q p)
    (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q)
    (hpout : HasPosLeadingCoeff (eulerBidiagonalStepWithConstant c d p))
    (hqout : HasPosLeadingCoeff (eulerBidiagonalStepWithConstant c d q))
    (hpoutdeg : 1 ≤ (eulerBidiagonalStepWithConstant c d p).natDegree) :
    Prec (eulerBidiagonalStepWithConstant c d q)
      (eulerBidiagonalStepWithConstant c d p) := by
  simp only [eulerBidiagonalStepWithConstant_eq_bidiagonalOperator] at hpout hqout hpoutdeg ⊢
  exact bidiagonalOperator_prec_of_affineSymbol_stable
    (eulerAffineBidiagonalSymbolWithConstant_stable c hc d hd)
    hpdeg hqdeg hpq hp hq hpout hqout hpoutdeg

/-- The Euler derivative step preserves real-rootedness on its natural degree
box.  The disjunction is the standard zero-output convention of finite-symbol
preserver theorems. -/
theorem eulerBidiagonalStep_eq_zero_or_splits
    {d : ℕ} (hd : 1 ≤ d) {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hp : p.Splits) :
    eulerBidiagonalStep d p = 0 ∨ (eulerBidiagonalStep d p).Splits := by
  rw [eulerBidiagonalStep_eq_bidiagonalOperator]
  exact bidiagonalOperator_splits_of_affineSymbol_stable
    (eulerAffineBidiagonalSymbol_stable d hd) hpdeg hp

/-- The Euler derivative step preserves an oriented interlacing pair whenever
the degree-box inputs and nonzero output orientations are certified. -/
theorem eulerBidiagonalStep_prec
    {d : ℕ} (hd : 1 ≤ d) {p q : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d)
    (hpq : Prec q p)
    (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q)
    (hpout : HasPosLeadingCoeff (eulerBidiagonalStep d p))
    (hqout : HasPosLeadingCoeff (eulerBidiagonalStep d q))
    (hpoutdeg : 1 ≤ (eulerBidiagonalStep d p).natDegree) :
    Prec (eulerBidiagonalStep d q) (eulerBidiagonalStep d p) := by
  simp only [eulerBidiagonalStep_eq_bidiagonalOperator] at hpout hqout hpoutdeg ⊢
  exact bidiagonalOperator_prec_of_affineSymbol_stable
    (eulerAffineBidiagonalSymbol_stable d hd)
    hpdeg hqdeg hpq hp hq hpout hqout hpoutdeg

end RealRooted.BorceaBranden
