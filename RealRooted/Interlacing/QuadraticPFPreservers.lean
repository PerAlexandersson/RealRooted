module

import RealRooted.OperatorMatrix.Directed
public import RealRooted.PFPolynomial
import RealRooted.CubicDiscriminant

/-!
# Quadratic differential PF preservers

This file formalizes the common-interlacer argument from RealRooted issue #2108.
For positive `a` and `b` and nonnegative `c`, the operator

`p ↦ X (D + b) (D + a) p + c p`

preserves Pólya-frequency polynomials.  It also records a small exact
counterexample below the sharp coefficient threshold.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The first-order differential operator `(D + a I)`. -/
def affineDerivative (a : ℝ) (p : ℝ[X]) : ℝ[X] :=
  p.derivative + C a * p

/-- The quadratic differential operator `X (D + b I) (D + a I) + c I`. -/
def quadraticPFOperator (a b c : ℝ) (p : ℝ[X]) : ℝ[X] :=
  X * affineDerivative b (affineDerivative a p) + C c * p

/-- A nonnegative affine derivative preserves the PF cone. -/
theorem IsPFPolynomial.affineDerivative_of_nonneg {p : ℝ[X]}
    (hp : IsPFPolynomial p)
    {a : ℝ} (ha : 0 ≤ a) : IsPFPolynomial (affineDerivative a p) := by
  unfold affineDerivative
  exact hp.derivative.add_of_interl ((IsPFPolynomial.of_C_nonneg ha).mul hp)
    (hp.interl_derivative_self.C_mul_right_of_nonneg ha)

/-- A nonnegative affine derivative precedes its input in zero-aware proper position. -/
theorem IsPFPolynomial.interl_affineDerivative_self {p : ℝ[X]}
    (hp : IsPFPolynomial p) {a : ℝ} (ha : 0 ≤ a) :
    Interl (affineDerivative a p) p := by
  unfold affineDerivative
  exact interl_add_left_of_common_right_of_nonneg hp.interl_derivative_self
    (hp.interl_self.C_mul_left_of_nonneg ha)
    hp.derivative.hasNonnegCoeffs
    (hasNonnegCoeffs_C_mul ha hp.hasNonnegCoeffs)

private theorem affineDerivative_degree_and_leadingCoeff
    {p : ℝ[X]} (hp0 : p ≠ 0) {a : ℝ} (ha : a ≠ 0) :
    (affineDerivative a p).natDegree = p.natDegree ∧
      (affineDerivative a p).leadingCoeff = a * p.leadingCoeff := by
  have htop : (a + 0 * (p.natDegree : ℝ)) * p.leadingCoeff ≠ 0 := by
    simpa using mul_ne_zero ha (leadingCoeff_ne_zero.mpr hp0)
  have hdegree :=
    Polynomial.natDegree_and_leadingCoeff_C_mul_add_affine_mul_derivative
      p a 1 0 htop
  simpa [affineDerivative, add_comm] using hdegree

/-- On a nonzero input, the quadratic operator with positive affine shifts
raises the natural degree by one. -/
theorem natDegree_quadraticPFOperator {p : ℝ[X]} (hp0 : p ≠ 0)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (quadraticPFOperator a b c p).natDegree = p.natDegree + 1 := by
  let g := affineDerivative a p
  let h := affineDerivative b g
  have hg := affineDerivative_degree_and_leadingCoeff hp0 ha.ne'
  have hg0 : g ≠ 0 := by
    apply leadingCoeff_ne_zero.mp
    rw [show g.leadingCoeff = a * p.leadingCoeff by simpa [g] using hg.2]
    exact mul_ne_zero ha.ne' (leadingCoeff_ne_zero.mpr hp0)
  have hh := affineDerivative_degree_and_leadingCoeff hg0 hb.ne'
  have hh0 : h ≠ 0 := by
    apply leadingCoeff_ne_zero.mp
    rw [show h.leadingCoeff = b * g.leadingCoeff by simpa [h] using hh.2]
    exact mul_ne_zero hb.ne' (leadingCoeff_ne_zero.mpr hg0)
  have hsmall : (C c * p).natDegree < (X * h).natDegree := by
    rw [natDegree_mul X_ne_zero hh0, natDegree_X, hh.1, hg.1]
    exact (natDegree_C_mul_le c p).trans_lt (by lia)
  rw [quadraticPFOperator, natDegree_add_eq_left_of_natDegree_lt hsmall,
    natDegree_mul X_ne_zero hh0, natDegree_X, hh.1, hg.1]
  simp [Nat.add_comm]

/-- Positive affine derivatives followed by multiplication by `X`, with a
nonnegative copy of the input added, preserve PF polynomials.  This is the
scalar common-interlacer theorem of RealRooted issue #2108. -/
theorem IsPFPolynomial.quadraticPFOperator_of_pos {p : ℝ[X]}
    (hp : IsPFPolynomial p) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) :
    IsPFPolynomial (quadraticPFOperator a b c p) := by
  by_cases hp0 : p = 0
  · simp [hp0, quadraticPFOperator, affineDerivative, IsPFPolynomial.zero]
  let g := affineDerivative a p
  let h := affineDerivative b g
  have hgp : IsPFPolynomial g := hp.affineDerivative_of_nonneg ha.le
  have hhp : IsPFPolynomial h := hgp.affineDerivative_of_nonneg hb.le
  have hg0 : g ≠ 0 := by
    dsimp [g, affineDerivative]
    exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      hp.derivative.hasNonnegCoeffs
      (hasNonnegCoeffs_C_mul ha.le hp.hasNonnegCoeffs)
      (mul_ne_zero (C_ne_zero.mpr ha.ne') hp0)
  have hg_p : Interl g p := hp.interl_affineDerivative_self ha.le
  have hh_g : Interl h g := hgp.interl_affineDerivative_self hb.le
  have hg_Xh : Interl g (X * h) :=
    (interl_iff_interl_X_mul hhp hgp).mp hh_g
  have hg_cp : Interl g (C c * p) :=
    hg_p.C_mul_right_of_nonneg hc
  have hg_out : Interl g (X * h + C c * p) :=
    interl_add_right_of_common_left_of_nonneg hg_Xh hg_cp
      hhp.X_mul.hasNonnegCoeffs
      (hasNonnegCoeffs_C_mul hc hp.hasNonnegCoeffs)
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
  · simpa [quadraticPFOperator, g, h] using
      hhp.X_mul.hasNonnegCoeffs.add
        (hasNonnegCoeffs_C_mul hc hp.hasNonnegCoeffs)
  · simpa [quadraticPFOperator, g, h] using
      (show X * h + C c * p = 0 ∨ (X * h + C c * p).Splits by
        rcases hg_out with hgzero | houtzero | hgstrict
        · exact (hg0 hgzero).elim
        · exact Or.inl houtzero
        · exact Or.inr hgstrict.2.1.2)

/-- The coefficient-form operator `X (A D² + B D + C) + E I`. -/
def secondOrderPFOperator (A B C₀ E : ℝ) (p : ℝ[X]) : ℝ[X] :=
  X * (C A * p.derivative.derivative + C B * p.derivative + C C₀ * p) +
    C E * p

private theorem secondOrderPFOperator_eq_factor
    (A B C₀ E a b : ℝ) (p : ℝ[X]) (hA : A ≠ 0)
    (hsum : A * (a + b) = B) (hprod : A * a * b = C₀) :
    secondOrderPFOperator A B C₀ E p =
      C A * quadraticPFOperator a b (E / A) p := by
  simp only [secondOrderPFOperator, quadraticPFOperator, affineDerivative,
    derivative_add, derivative_mul, derivative_C, zero_mul]
  rw [← hsum, ← hprod]
  simp only [map_mul, map_add]
  ring_nf
  have hCEA : C A * C (E * A⁻¹) = C E := by
    rw [← map_mul]
    congr 1
    field_simp
  rw [← hCEA]
  ring

/-- The division-free sufficient criterion from RealRooted issue #2108:
if `A,C > 0`, `B,E ≥ 0`, and `B² ≥ 4AC`, then
`X (A D² + B D + C) + E I` preserves every PF polynomial. -/
theorem IsPFPolynomial.secondOrderPFOperator_of_discrim_nonneg
    {p : ℝ[X]} (hp : IsPFPolynomial p) {A B C₀ E : ℝ}
    (hA : 0 < A) (hC : 0 < C₀) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hdisc : 4 * A * C₀ ≤ B ^ 2) :
    IsPFPolynomial (secondOrderPFOperator A B C₀ E p) := by
  let delta := B ^ 2 - 4 * A * C₀
  let a := (B + Real.sqrt delta) / (2 * A)
  let b := (B - Real.sqrt delta) / (2 * A)
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    linarith
  have hsqrt_sq : (Real.sqrt delta) ^ 2 = delta := Real.sq_sqrt hdelta
  have hsqrt_nonneg : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg delta
  have hsqrt_lt : Real.sqrt delta < B := by
    dsimp [delta] at hsqrt_sq
    nlinarith
  have hBpos : 0 < B := lt_of_le_of_lt hsqrt_nonneg hsqrt_lt
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (add_pos_of_pos_of_nonneg hBpos hsqrt_nonneg) (by positivity)
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos (sub_pos.mpr hsqrt_lt) (by positivity)
  have hsum : A * (a + b) = B := by
    dsimp [a, b]
    field_simp
    ring
  have hprod : A * a * b = C₀ := by
    dsimp [a, b, delta] at hsqrt_sq ⊢
    field_simp [hA.ne']
    ring_nf at hsqrt_sq ⊢
    nlinarith
  rw [secondOrderPFOperator_eq_factor A B C₀ E a b p hA.ne' hsum hprod]
  exact (hp.quadraticPFOperator_of_pos ha hb (div_nonneg hE hA.le)).const_mul hA

/-- The normalized operator `X D² + rho X D + X + gamma I`. -/
def rhoGammaOperator (rho gamma : ℝ) (p : ℝ[X]) : ℝ[X] :=
  X * p.derivative.derivative + C rho * X * p.derivative + X * p + C gamma * p

/-- For `rho ≥ 2` and `gamma ≥ 0`, the normalized quadratic operator
preserves every PF polynomial. -/
theorem IsPFPolynomial.rhoGammaOperator_of_two_le {p : ℝ[X]}
    (hp : IsPFPolynomial p) {rho gamma : ℝ} (hrho : 2 ≤ rho)
    (hgamma : 0 ≤ gamma) : IsPFPolynomial (rhoGammaOperator rho gamma p) := by
  have hpres := hp.secondOrderPFOperator_of_discrim_nonneg
    (A := 1) (B := rho) (C₀ := 1) (E := gamma)
    (by norm_num) (by norm_num) (by linarith) hgamma (by nlinarith)
  have hop : rhoGammaOperator rho gamma p =
      secondOrderPFOperator 1 rho 1 gamma p := by
    simp only [secondOrderPFOperator, rhoGammaOperator, map_one, one_mul]
    ring
  rw [hop]
  exact hpres

/-- The boundary normalization `rho = 2` preserves the PF cone for every
nonnegative constant term. -/
theorem IsPFPolynomial.rhoGammaOperator_two {p : ℝ[X]}
    (hp : IsPFPolynomial p) {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    IsPFPolynomial (rhoGammaOperator 2 gamma p) :=
  hp.rhoGammaOperator_of_two_le (by norm_num) hgamma

/-- At `rho = 0`, `gamma = 1`, the normalized operator already fails on
the PF input `(X + 1)²`; its cubic output has negative discriminant. -/
theorem not_isPFPolynomial_rhoGammaOperator_zero_one :
    ¬IsPFPolynomial
      (rhoGammaOperator 0 1 ((X + 1 : ℝ[X]) ^ 2)) := by
  let q : ℝ[X] := C 1 * X ^ 3 + C 3 * X ^ 2 + C 5 * X + C 1
  have hout : rhoGammaOperator 0 1 ((X + 1 : ℝ[X]) ^ 2) = q := by
    dsimp [rhoGammaOperator, q]
    simp only [derivative_pow, derivative_mul, derivative_add, derivative_X,
      derivative_one, derivative_ofNat, add_zero, Nat.cast_ofNat, map_ofNat,
      mul_one]
    norm_num
    ring
  have hdeg_eq : q.natDegree = 3 := by
    dsimp [q]
    compute_degree <;> norm_num
  have hdisc : cubicDiscr q < 0 := by
    dsimp [q]
    rw [cubicDiscr_of_coeffs]
    norm_num
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg_eq
    simp at hdeg_eq
  intro hpf
  have hsplit : q.Splits := by
    rcases hpf.eq_zero_or_splits with hzero | hsplit
    · exact (hq0 (hout.symm.trans hzero)).elim
    · simpa [hout] using hsplit
  exact (not_splits_of_cubicDiscr_neg_of_natDegree_le_three hdeg_eq.le hdisc) hsplit

/-- A concrete failure below the threshold: `(X + 1)²` is PF, but its
image under the normalized operator at `rho = 0`, `gamma = 1` is not. -/
theorem rhoGammaOperator_zero_one_counterexample :
    IsPFPolynomial ((X + 1 : ℝ[X]) ^ 2) ∧
      ¬IsPFPolynomial
        (rhoGammaOperator 0 1 ((X + 1 : ℝ[X]) ^ 2)) :=
  ⟨isPFPolynomial_X_add_one.pow 2,
    not_isPFPolynomial_rhoGammaOperator_zero_one⟩

end RealRooted
