module

public import RealRooted.PFPolynomial
public import RealRooted.Interlacing.QuadraticPFPreservers
public import RealRooted.Interlacing.SecondOrderClassification
import RealRooted.Interlacing.SecondOrderIff
public import RealRooted.CubicDiscriminant
public import RealRooted.RootCounting.Descartes

import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots.Real
import RealRooted.Interlacing.SecondOrderPreservation
import RealRooted.Linear
import RealRooted.Mathlib.Algebra.Polynomial.RuleOfSigns
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignVariation
import RealRooted.QuadraticRoot

/-!
# Necessity for second-order ray preservers

Finite polynomial obstructions obtained from the degree-four residuals of
shifted powers and their quadratic limit.
-/

public section

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- The bounded-degree factor left after removing the prescribed roots from
the upper-obstruction test polynomial. -/
def secondOrderUpperResidual (a b c d f t : ℝ) (m n : ℕ) : ℝ[X] :=
  let N : ℝ := n + 2
  let e : ℝ := t / N
  let h : ℝ[X] := 1 + C e * X
  (C a + C b * X) * X * h ^ 2 +
    (C c + C d * X) * h * (C (m : ℝ) * h + C (N * e) * X) +
      C f * (C ((m : ℝ) * (m - 1)) * h ^ 2 +
        C (2 * m * N * e) * X * h + C (N * (N - 1) * e ^ 2) * X ^ 2)

/-- The image of the finite upper-obstruction test polynomial factors into
prescribed real-rooted factors and its bounded-degree residual. -/
theorem secondOrderRayOperator_upper_test_factor
    (a b c d f t : ℝ) (m n : ℕ) (hm : 1 ≤ m) :
    secondOrderRayOperator a b c d f
        (X ^ m * (1 + C (t / (n + 2 : ℝ)) * X) ^ (n + 2)) =
      X ^ (m - 1) * (1 + C (t / (n + 2 : ℝ)) * X) ^ n *
        secondOrderUpperResidual a b c d f t m n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  cases k with
  | zero =>
      let e : ℝ := t / (n + 2 : ℝ)
      let h : ℝ[X] := 1 + C e * X
      have hp₁ : (X * h ^ (n + 2)).derivative =
          h ^ (n + 2) + C ((n + 2 : ℝ) * e) * X * h ^ (n + 1) := by
        simp [h, derivative_mul, derivative_pow]
        ring
      have hp₂ : (X * h ^ (n + 2)).derivative.derivative =
          C (2 * (n + 2 : ℝ) * e) * h ^ (n + 1) +
            C ((n + 2 : ℝ) * (n + 1) * e ^ 2) * X * h ^ n := by
        rw [hp₁]
        simp [h, derivative_mul, derivative_pow]
        simp only [map_ofNat]
        ring
      simp only [Nat.add_zero, pow_one, Nat.sub_self, pow_zero, one_mul]
      change secondOrderRayOperator a b c d f (X * h ^ (n + 2)) = _
      rw [secondOrderRayOperator_eq_formula, hp₂, hp₁]
      simp only [secondOrderUpperResidual]
      rw [show t / (n + 2 : ℝ) = e by rfl]
      rw [show 1 + C e * X = h by rfl]
      simp
      simp only [map_ofNat]
      ring
  | succ k =>
      let e : ℝ := t / (n + 2 : ℝ)
      let h : ℝ[X] := 1 + C e * X
      let M : ℝ := k + 2
      let N : ℝ := n + 2
      have hp₁ : (X ^ (k + 2) * h ^ (n + 2)).derivative =
          C M * X ^ (k + 1) * h ^ (n + 2) +
            C (N * e) * X ^ (k + 2) * h ^ (n + 1) := by
        simp [h, M, N, derivative_mul, derivative_pow]
        ring
      have hp₂ : (X ^ (k + 2) * h ^ (n + 2)).derivative.derivative =
          C (M * (M - 1)) * X ^ k * h ^ (n + 2) +
            C (2 * M * N * e) * X ^ (k + 1) * h ^ (n + 1) +
              C (N * (N - 1) * e ^ 2) * X ^ (k + 2) * h ^ n := by
        rw [hp₁]
        simp [h, M, N, derivative_mul, derivative_pow]
        simp only [map_ofNat]
        ring
      simp only [Nat.one_add, Nat.succ_sub_one]
      change secondOrderRayOperator a b c d f (X ^ (k + 2) * h ^ (n + 2)) = _
      rw [secondOrderRayOperator_eq_formula, hp₂, hp₁]
      simp only [secondOrderUpperResidual]
      rw [show (n + 2 : ℝ) = N by rfl]
      rw [show t / N = e by rfl]
      rw [show 1 + C e * X = h by rfl]
      rw [show ((k + 1).succ : ℝ) = M by dsimp [M]; norm_cast]
      simp
      simp only [pow_succ]
      simp only [map_ofNat]
      ring

/-- A fixed-degree deformation of the limiting quadratic, with deformation
parameter equal to the reciprocal test degree. -/
def secondOrderUpperResidualApprox
    (a b c d f t : ℝ) (m : ℕ) (s : ℝ) : ℝ[X] :=
  let h : ℝ[X] := 1 + C (t * s) * X
  (C a + C b * X) * X * h ^ 2 +
    (C c + C d * X) * h * (C (m : ℝ) * h + C t * X) +
      C f * (C ((m : ℝ) * (m - 1)) * h ^ 2 +
        C (2 * m * t) * X * h + C (t ^ 2 * (1 - s)) * X ^ 2)

/-- The quadratic limit of the bounded-degree upper-obstruction residuals. -/
def secondOrderUpperLimit (a b c d f t : ℝ) (m : ℕ) : ℝ[X] :=
  C (b + d * t + f * t ^ 2) * X ^ 2 +
    C (a + d * m + (c + 2 * f * m) * t) * X +
      C (m * (c + f * (m - 1)))

/-- Substituting the reciprocal degree into the fixed-degree deformation
recovers the finite residual exactly. -/
theorem secondOrderUpperResidual_eq_approx
    (a b c d f t : ℝ) (m n : ℕ) :
    secondOrderUpperResidual a b c d f t m n =
      secondOrderUpperResidualApprox a b c d f t m (1 / (n + 2 : ℝ)) := by
  apply Polynomial.funext
  intro x
  simp [secondOrderUpperResidual, secondOrderUpperResidualApprox]
  field_simp

/-- At deformation parameter zero, the residual deformation is the explicit
quadratic limit. -/
theorem secondOrderUpperResidualApprox_zero
    (a b c d f t : ℝ) (m : ℕ) :
    secondOrderUpperResidualApprox a b c d f t m 0 =
      secondOrderUpperLimit a b c d f t m := by
  apply Polynomial.funext
  intro x
  simp [secondOrderUpperResidualApprox, secondOrderUpperLimit]
  ring

/-- Multiplication adds any available natural-degree bounds. -/
private theorem natDegree_mul_le_of_bounds {p q : ℝ[X]} {r s : ℕ}
    (hp : p.natDegree ≤ r) (hq : q.natDegree ≤ s) :
    (p * q).natDegree ≤ r + s :=
  natDegree_mul_le.trans (Nat.add_le_add hp hq)

/-- Addition takes the maximum of any available natural-degree bounds. -/
private theorem natDegree_add_le_of_bounds {p q : ℝ[X]} {r s : ℕ}
    (hp : p.natDegree ≤ r) (hq : q.natDegree ≤ s) :
    (p + q).natDegree ≤ max r s :=
  (natDegree_add_le p q).trans (max_le_max hp hq)

/-- The fixed-degree deformation has degree at most four. -/
private theorem secondOrderUpperResidualApprox_natDegree_le
    (a b c d f t s : ℝ) (m : ℕ) :
    (secondOrderUpperResidualApprox a b c d f t m s).natDegree ≤ 4 := by
  let h : ℝ[X] := 1 + C (t * s) * X
  have hh : h.natDegree ≤ 1 := by dsimp [h]; compute_degree
  have hh₂ : (h ^ 2).natDegree ≤ 2 := by
    exact natDegree_pow_le.trans (by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 hh)
  have haff : (C a + C b * X : ℝ[X]).natDegree ≤ 1 := by compute_degree
  have hder : (C c + C d * X : ℝ[X]).natDegree ≤ 1 := by compute_degree
  have hmh : (C (m : ℝ) * h).natDegree ≤ 1 := by
    exact (natDegree_mul_le_of_bounds (by rw [natDegree_C]) hh).trans (by norm_num)
  have htx : (C t * X).natDegree ≤ 1 := by compute_degree
  have hinner : (C (m : ℝ) * h + C t * X).natDegree ≤ 1 := by
    exact (natDegree_add_le_of_bounds hmh htx).trans (by norm_num)
  have hterm₁ : ((C a + C b * X) * X * h ^ 2).natDegree ≤ 4 := by
    exact natDegree_mul_le_of_bounds
      (natDegree_mul_le_of_bounds haff (by rw [natDegree_X])) hh₂
  have hterm₂ :
      ((C c + C d * X) * h * (C (m : ℝ) * h + C t * X)).natDegree ≤ 3 := by
    exact natDegree_mul_le_of_bounds
      (natDegree_mul_le_of_bounds hder hh) hinner
  have hquad :
      (C ((m : ℝ) * (m - 1)) * h ^ 2 +
        C (2 * m * t) * X * h + C (t ^ 2 * (1 - s)) * X ^ 2).natDegree ≤ 2 := by
    apply (natDegree_add_le_of_bounds
      (natDegree_add_le_of_bounds
        (natDegree_mul_le_of_bounds (by rw [natDegree_C]) hh₂)
        (natDegree_mul_le_of_bounds
          (natDegree_mul_le_of_bounds
            (by rw [natDegree_C]) (by rw [natDegree_X])) hh))
      (natDegree_mul_le_of_bounds
        (by rw [natDegree_C]) (by compute_degree))).trans
    norm_num
  have hterm₃ : (C f *
      (C ((m : ℝ) * (m - 1)) * h ^ 2 +
        C (2 * m * t) * X * h + C (t ^ 2 * (1 - s)) * X ^ 2)).natDegree ≤ 2 := by
    exact (natDegree_mul_le_of_bounds (by rw [natDegree_C]) hquad).trans
      (by norm_num)
  change ((C a + C b * X) * X * h ^ 2 +
    (C c + C d * X) * h * (C (m : ℝ) * h + C t * X) + C f *
      (C ((m : ℝ) * (m - 1)) * h ^ 2 +
        C (2 * m * t) * X * h + C (t ^ 2 * (1 - s)) * X ^ 2)).natDegree ≤ 4
  exact (natDegree_add_le_of_bounds
    (natDegree_add_le_of_bounds hterm₁ hterm₂) hterm₃).trans (by norm_num)

/-- Every finite upper residual has degree at most four, uniformly in the
test degree. -/
theorem secondOrderUpperResidual_natDegree_le
    (a b c d f t : ℝ) (m n : ℕ) :
    (secondOrderUpperResidual a b c d f t m n).natDegree ≤ 4 := by
  rw [secondOrderUpperResidual_eq_approx]
  exact secondOrderUpperResidualApprox_natDegree_le a b c d f t _ m

/-- The finite residuals converge pointwise after complexification to their
explicit quadratic limit. -/
theorem secondOrderUpperResidual_tendsto_eval
    (a b c d f t : ℝ) (m : ℕ) (z : ℂ) :
    Tendsto
      (fun n ↦ ((secondOrderUpperResidual a b c d f t m n).map
        Complex.ofRealHom).eval z) atTop
      (𝓝 (((secondOrderUpperLimit a b c d f t m).map
        Complex.ofRealHom).eval z)) := by
  let H : ℝ → ℂ := fun s ↦ 1 + ((t * s : ℝ) : ℂ) * z
  let F : ℝ → ℂ := fun s ↦
    ((a : ℂ) + (b : ℂ) * z) * z * H s ^ 2 +
      ((c : ℂ) + (d : ℂ) * z) * H s *
        (((m : ℝ) : ℂ) * H s + (t : ℂ) * z) +
      (f : ℂ) *
        ((((m : ℝ) * (m - 1) : ℝ) : ℂ) * H s ^ 2 +
          ((2 * m * t : ℝ) : ℂ) * z * H s +
            ((t ^ 2 * (1 - s) : ℝ) : ℂ) * z ^ 2)
  have hF : Continuous F := by
    dsimp only [F, H]
    fun_prop
  have hcontinuous : Continuous (fun s : ℝ ↦
      ((secondOrderUpperResidualApprox a b c d f t m s).map
        Complex.ofRealHom).eval z) := by
    simpa [F, H, secondOrderUpperResidualApprox] using hF
  have hshift := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 1)
  have hrecip : Tendsto (fun n : ℕ ↦ 1 / (n + 2 : ℝ)) atTop (𝓝 0) := by
    convert hshift using 1
    ext n
    simp only [Function.comp_apply, one_div]
    congr 1
    norm_cast
  rw [show (secondOrderUpperLimit a b c d f t m).map Complex.ofRealHom =
      (secondOrderUpperResidualApprox a b c d f t m 0).map
        Complex.ofRealHom by rw [secondOrderUpperResidualApprox_zero]]
  simpa [secondOrderUpperResidual_eq_approx, Function.comp_def] using
    hcontinuous.continuousAt.tendsto.comp hrecip

/-- If the quadratic limit does not split, one finite residual already fails
to split. This is the fixed-degree closure step. -/
theorem exists_not_splits_secondOrderUpperResidual_of_limit
    {a b c d f t : ℝ} {m : ℕ}
    (hlimit : ¬(secondOrderUpperLimit a b c d f t m).Splits) :
    ∃ n, ¬(secondOrderUpperResidual a b c d f t m n).Splits := by
  by_contra hall
  have hsplits : ∀ n, (secondOrderUpperResidual a b c d f t m n).Splits := by
    intro n
    exact Classical.byContradiction fun hn ↦ hall ⟨n, hn⟩
  have hclosed := Polynomial.eq_zero_or_splits_of_tendsto_eval_of_natDegree_le
    (N := 4) (fun n ↦ secondOrderUpperResidual_natDegree_le a b c d f t m n)
    (fun n ↦ Or.inr (hsplits n))
    (secondOrderUpperResidual_tendsto_eval a b c d f t m)
  rcases hclosed with hzero | hsplits
  · apply hlimit
    rw [hzero]
    exact Polynomial.Splits.zero
  · exact hlimit hsplits

/-- A positive upper test parameter gives a finite PF test polynomial. -/
theorem isPFPolynomial_secondOrder_upper_test
    {t : ℝ} (ht : 0 < t) (m n : ℕ) :
    IsPFPolynomial
      (X ^ m * (1 + C (t / (n + 2 : ℝ)) * X) ^ (n + 2)) := by
  have heps : 0 < t / (n + 2 : ℝ) := by positivity
  have hlinear : IsPFPolynomial (1 + C (t / (n + 2 : ℝ)) * X) := by
    have h := IsPFPolynomial.C_mul_X_add_C_sub_C heps zero_le_one (le_refl 0)
    simpa only [map_zero, sub_zero, map_one, add_comm] using h
  exact (isPFPolynomial_X_pow m).mul (hlinear.pow (n + 2))

/-- Nonsplitting of one residual transfers through the prescribed factors to
nonsplitting of the corresponding operator image. -/
theorem not_splits_secondOrderRayOperator_upper_test_of_residual
    {a b c d f t : ℝ} {m n : ℕ} (hm : 1 ≤ m)
    (hres : ¬(secondOrderUpperResidual a b c d f t m n).Splits) :
    ¬(secondOrderRayOperator a b c d f
      (X ^ m * (1 + C (t / (n + 2 : ℝ)) * X) ^ (n + 2))).Splits := by
  intro hout
  rw [secondOrderRayOperator_upper_test_factor a b c d f t m n hm] at hout
  let q := secondOrderUpperResidual a b c d f t m n
  let u := X ^ (m - 1) * (1 + C (t / (n + 2 : ℝ)) * X) ^ n
  have hq : q ≠ 0 := by
    intro hzero
    apply hres
    change q.Splits
    rw [hzero]
    exact Polynomial.Splits.zero
  have hu : u ≠ 0 := by
    dsimp only [u]
    apply mul_ne_zero (pow_ne_zero _ X_ne_zero)
    apply pow_ne_zero
    intro hzero
    have hconst := congrArg (fun p : ℝ[X] ↦ p.coeff 0) hzero
    simp at hconst
  have hqsplit := isRealRooted_of_dvd (mul_ne_zero hu hq) hout hq
    (dvd_mul_left q u)
  exact hres hqsplit.2

/-- A nonsplitting upper quadratic limit yields an explicit finite PF
counterexample to universal preservation. -/
theorem not_secondOrderRayPreserving_of_upper_limit
    {a b c d f t : ℝ} {m : ℕ} (hm : 1 ≤ m) (ht : 0 < t)
    (hlimit : ¬(secondOrderUpperLimit a b c d f t m).Splits) :
    ¬SecondOrderRayPreserving a b c d f := by
  obtain ⟨n, hn⟩ :=
    exists_not_splits_secondOrderUpperResidual_of_limit hlimit
  intro hpres
  have hout := hpres _ (isPFPolynomial_secondOrder_upper_test ht m n)
  exact not_splits_secondOrderRayOperator_upper_test_of_residual hm hn hout.splits

/-- A negative discriminant makes the explicit upper quadratic limit
nonsplitting. -/
theorem not_splits_secondOrderUpperLimit_of_discrim_neg
    {a b c d f t : ℝ} {m : ℕ}
    (hlead : b + d * t + f * t ^ 2 ≠ 0)
    (hdisc : discrim (b + d * t + f * t ^ 2)
      (a + d * m + (c + 2 * f * m) * t)
      (m * (c + f * (m - 1))) < 0) :
    ¬(secondOrderUpperLimit a b c d f t m).Splits := by
  simpa only [secondOrderUpperLimit] using
    quadraticPoly_not_splits_of_discrim_neg hlead hdisc

/-- The discriminant of the limiting residual is a scalar quadratic in its
positive test parameter. -/
theorem discrim_secondOrderUpperLimit
    (a b c d f t : ℝ) (m : ℕ) :
    discrim (b + d * t + f * t ^ 2)
        (a + d * m + (c + 2 * f * m) * t)
        (m * (c + f * (m - 1))) =
      (a + d * m) ^ 2 - 4 * b * m * (c + f * (m - 1)) +
        2 * ((a + d * m) * (c + 2 * f * m) -
          2 * d * m * (c + f * (m - 1))) * t +
        (c ^ 2 + 4 * f ^ 2 * m) * t ^ 2 := by
  simp only [discrim]
  ring

/-- Positivity of the upper obstruction expression, together with a negative
linear coefficient, produces a finite PF counterexample. -/
theorem not_secondOrderRayPreserving_of_upper_obstruction
    {a b c d f : ℝ} {m : ℕ}
    (hb : 0 < b) (_hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 < f) (hm : 1 ≤ m)
    (hconstant : 0 < c + f * (m - 1))
    (hlinear :
      (a + d * m) * (c + 2 * f * m) -
        2 * d * m * (c + f * (m - 1)) < 0)
    (hupper : 0 < b * c ^ 2 - a * d * c +
      f * (a ^ 2 - m * (d ^ 2 - 4 * b * f))) :
    ¬SecondOrderRayPreserving a b c d f := by
  let B := (a + d * m) * (c + 2 * f * m) -
    2 * d * m * (c + f * (m - 1))
  let C₀ := (a + d * m) ^ 2 - 4 * b * m * (c + f * (m - 1))
  let L := c ^ 2 + 4 * f ^ 2 * m
  have hmreal : (0 : ℝ) < m := by positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hid := secondOrder_upper_obstruction_identity_at_index a b c d f m
  have hdisc : L * C₀ < B ^ 2 := by
    dsimp only at hid
    dsimp [L, C₀, B]
    nlinarith [mul_pos (mul_pos hmreal hconstant) hupper]
  obtain ⟨t, ht, htneg⟩ :=
    exists_pos_quadratic_lt_zero hL hlinear hdisc
  have hlead : 0 < b + d * t + f * t ^ 2 := by positivity
  apply not_secondOrderRayPreserving_of_upper_limit hm ht
  apply not_splits_secondOrderUpperLimit_of_discrim_neg hlead.ne'
  rw [discrim_secondOrderUpperLimit]
  simpa only [B, C₀, L] using htneg

/-- Crossing the positive quadratic root makes the upper obstruction
expression strictly positive. -/
private theorem secondOrder_upper_expression_pos
    {a b c d f delta K : ℝ} {m : ℕ}
    (hb : 0 < b) (hdisc : delta = d ^ 2 - 4 * b * f) (hK : 0 < K)
    (hKsq : K ^ 2 = delta * (a ^ 2 + 4 * b * f * m))
    (h2bc : a * d + K < 2 * b * c) :
    0 < b * c ^ 2 - a * d * c +
      f * (a ^ 2 - m * (d ^ 2 - 4 * b * f)) := by
  have hdiff : 0 < (2 * b * c - a * d) ^ 2 - K ^ 2 := by
    have hminus : 0 < 2 * b * c - a * d - K := by
      nlinarith only [h2bc]
    have hplus : 0 < 2 * b * c - a * d + K := by
      nlinarith only [h2bc, hK]
    nlinarith only [mul_pos hminus hplus]
  have hid : (2 * b * c - a * d) ^ 2 - K ^ 2 =
      4 * b * (b * c ^ 2 - a * d * c +
        f * (a ^ 2 - m * (d ^ 2 - 4 * b * f))) := by
    rw [hKsq, hdisc]
    ring
  nlinarith only [hdiff, hid, hb]

/-- Above the explicit upper threshold, the scalar data have the signs needed
by the limiting-quadratic obstruction. -/
private theorem secondOrder_upper_obstruction_signs
    {a b c d f delta : ℝ} {m : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hm : 1 ≤ m)
    (hupperBranch : a ^ 2 + 4 * b * f * m < (m : ℝ) ^ 2 * delta)
    (habove : (a * d + Real.sqrt
      (delta * (a ^ 2 + 4 * b * f * m))) / (2 * b) < c) :
    0 < c + f * (m - 1) ∧
      (a + d * m) * (c + 2 * f * m) -
        2 * d * m * (c + f * (m - 1)) < 0 ∧
      0 < b * c ^ 2 - a * d * c +
        f * (a ^ 2 - m * (d ^ 2 - 4 * b * f)) := by
  let K := Real.sqrt (delta * (a ^ 2 + 4 * b * f * m))
  have hmreal : (0 : ℝ) < m := by positivity
  have hinside : 0 < delta * (a ^ 2 + 4 * b * f * m) := by positivity
  have hK : 0 < K := Real.sqrt_pos.2 hinside
  have hKsq : K ^ 2 = delta * (a ^ 2 + 4 * b * f * m) :=
    Real.sq_sqrt hinside.le
  have h2bc : a * d + K < 2 * b * c := by
    have hraw := (div_lt_iff₀ (by positivity : 0 < 2 * b)).mp habove
    dsimp only [K]
    nlinarith only [hraw]
  have hc : 0 < c := by nlinarith [mul_nonneg ha hd]
  have hconstant : 0 < c + f * (m - 1) := by
    have : (0 : ℝ) ≤ m - 1 := by norm_cast; lia
    positivity
  have hq : 0 < d * m - a := by
    have hdm : a ^ 2 < (d * m) ^ 2 := by
      rw [hdisc] at hupperBranch
      nlinarith [mul_pos (mul_pos hb hf) hmreal]
    by_contra hnot
    have hnonpos := le_of_not_gt hnot
    have hle : d * m ≤ a := by linarith only [hnonpos]
    have h₁ : 0 ≤ a - d * m := sub_nonneg.mpr hle
    have h₂ : 0 ≤ a + d * m := by positivity
    have hprod := mul_nonneg h₁ h₂
    nlinarith only [hdm, hprod]
  let R := 4 * b * f * m * (a + d) - (d * m - a) * a * d
  have hsquares : R ^ 2 < ((d * m - a) * K) ^ 2 := by
    have hfactor :
        ((d * m - a) * K) ^ 2 - R ^ 2 =
          -4 * b * f * (a ^ 2 + d ^ 2 * m) *
            (a ^ 2 + 4 * b * f * m ^ 2 + 4 * b * f * m - d ^ 2 * m ^ 2) := by
      dsimp [R]
      rw [mul_pow, hKsq, hdisc]
      ring
    have hlast :
        a ^ 2 + 4 * b * f * m ^ 2 + 4 * b * f * m - d ^ 2 * m ^ 2 < 0 := by
      rw [hdisc] at hupperBranch
      nlinarith
    have hapos : 0 < a ^ 2 + d ^ 2 * m := by
      have hdpos : 0 < d := by
        rw [hdisc] at hdelta
        nlinarith [mul_pos hb hf]
      positivity
    rw [← sub_pos, hfactor]
    have hcoef : -4 * b * f * (a ^ 2 + d ^ 2 * m) < 0 := by
      have hp : 0 < 4 * b * f * (a ^ 2 + d ^ 2 * m) := by positivity
      nlinarith only [hp]
    exact mul_pos_of_neg_of_neg hcoef hlast
  have hR : R < (d * m - a) * K := by
    nlinarith only [hsquares, mul_pos hq hK,
      sq_nonneg (R + (d * m - a) * K)]
  have hproduct :
      4 * b * f * m * (a + d) < (d * m - a) * (a * d + K) := by
    dsimp [R] at hR
    nlinarith
  have hscaled := mul_lt_mul_of_pos_left h2bc hq
  have hlinear :
      (a + d * m) * (c + 2 * f * m) -
        2 * d * m * (c + f * (m - 1)) < 0 := by
    have : 2 * f * m * (a + d) < c * (d * m - a) := by
      nlinarith [mul_pos hb (mul_pos hq hc)]
    nlinarith
  have hupper := secondOrder_upper_expression_pos hb hdisc hK hKsq h2bc
  exact ⟨hconstant, hlinear, hupper⟩

/-- In the upper scalar branch, exceeding the explicit threshold gives a
finite PF counterexample, hence universal preservation is impossible. -/
theorem not_secondOrderRayPreserving_of_upper_branch
    {a b c d f delta : ℝ} {m : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hm : 1 ≤ m)
    (hupperBranch : a ^ 2 + 4 * b * f * m < (m : ℝ) ^ 2 * delta)
    (habove : (a * d + Real.sqrt
      (delta * (a ^ 2 + 4 * b * f * m))) / (2 * b) < c) :
    ¬SecondOrderRayPreserving a b c d f := by
  obtain ⟨hconstant, hlinear, hupper⟩ :=
    secondOrder_upper_obstruction_signs ha hb hd hf hdelta hdisc hm
      hupperBranch habove
  exact not_secondOrderRayPreserving_of_upper_obstruction
    hb hc hd hf hm hconstant hlinear hupper

/-- In the upper branch at the minimizing index, universal preservation is
equivalent to the explicit upper threshold. -/
theorem secondOrderRayPreserving_iff_upper_bound_at_index
    {a b c d f delta : ℝ} {m : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hm : 1 ≤ m)
    (hmlo : delta * (m : ℝ) * ((m : ℝ) - 1) ≤ a ^ 2)
    (hmhi : a ^ 2 ≤ delta * (m : ℝ) * ((m : ℝ) + 1))
    (hupperBranch : a ^ 2 + 4 * b * f * m < (m : ℝ) ^ 2 * delta) :
    SecondOrderRayPreserving a b c d f ↔
      c ≤ (a * d + Real.sqrt
        (delta * (a ^ 2 + 4 * b * f * m))) / (2 * b) := by
  constructor
  · intro hpres
    by_contra hbound
    exact (not_secondOrderRayPreserving_of_upper_branch
      ha hb hc hd hf hdelta hdisc hm hupperBranch (lt_of_not_ge hbound)) hpres
  · intro hbound
    apply secondOrderRayPreserving_of_three_branch_at_index
      ha hb hc hd hf hdelta hdisc hm hmlo hmhi
    right
    right
    refine ⟨?_, ?_, hbound⟩
    · intro hlower
      have hmreal : (0 : ℝ) < m := by positivity
      nlinarith only [hupperBranch, hlower, mul_pos (mul_pos hb hf) hmreal]
    · intro hmiddle
      have hmreal : (0 : ℝ) < m := by positivity
      have hdiff : 0 < (m : ℝ) ^ 2 * delta - a ^ 2 := by
        nlinarith only [hupperBranch, mul_pos (mul_pos hb hf) hmreal]
      rw [abs_of_pos hdiff] at hmiddle
      nlinarith only [hupperBranch, hmiddle]

/-- A negative explicit monomial residual discriminant obstructs splitting.
This API avoids unfolding the opaque discriminant abbreviation. -/
theorem _root_.RealRooted.SecondOrderRay.not_splits_X_pow_of_discrim_neg
    {a b c d f : ℝ} {m : ℕ} (hm : 1 ≤ m) (hb : b ≠ 0)
    (hneg : (a + d * m) ^ 2 - 4 * b * m * (c + f * (m - 1)) < 0) :
    ¬(secondOrderRayOperator a b c d f (X ^ m)).Splits := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : m ≠ 0)
  rw [secondOrderRayOperator_X_pow_succ_factor]
  intro hout
  let q : ℝ[X] := C b * X ^ 2 + C (a + d * (n + 1)) * X +
    C ((n + 1) * (c + f * n))
  have hq : q ≠ 0 := by
    intro hzero
    have hdegree : q.natDegree = 2 := by
      dsimp only [q]
      exact natDegree_quadratic hb
    rw [hzero] at hdegree
    simp at hdegree
  have hqsplit := isRealRooted_of_dvd
    (mul_ne_zero (pow_ne_zero n X_ne_zero) hq) hout hq (dvd_mul_left q (X ^ n))
  apply quadraticPoly_not_splits_of_discrim_neg hb _ hqsplit.2
  simp only [discrim]
  norm_num [Nat.cast_succ] at hneg
  nlinarith

/-- In the middle branch at the minimizing index, universal preservation is
equivalent to nonnegativity of the monomial residual discriminant. -/
theorem secondOrderRayPreserving_iff_middle_discrim_at_index
    {a b c d f delta : ℝ} {m : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hm : 1 ≤ m)
    (hmlo : delta * (m : ℝ) * ((m : ℝ) - 1) ≤ a ^ 2)
    (hmhi : a ^ 2 ≤ delta * (m : ℝ) * ((m : ℝ) + 1))
    (hmiddle : |(m : ℝ) ^ 2 * delta - a ^ 2| ≤ 4 * b * f * m) :
    SecondOrderRayPreserving a b c d f ↔
      0 ≤ (a + d * m) ^ 2 - 4 * b * m * (c + f * (m - 1)) := by
  constructor
  · intro hpres
    by_contra hnonneg
    have hnot := RealRooted.SecondOrderRay.not_splits_X_pow_of_discrim_neg
      hm hb.ne' (lt_of_not_ge hnonneg)
    have hout := hpres _ (isPFPolynomial_X_pow m)
    exact hnot hout.splits
  · intro hmonomial
    apply secondOrderRayPreserving_of_three_branch_at_index
      ha hb hc hd hf hdelta hdisc hm hmlo hmhi
    right
    left
    refine ⟨?_, hmiddle, ?_⟩
    · intro hlower
      have hmreal : (0 : ℝ) < m := by positivity
      have hpos := mul_pos (mul_pos hb hf) hmreal
      have habs : 4 * b * f * m < |(m : ℝ) ^ 2 * delta - a ^ 2| := by
        rw [abs_of_neg (by nlinarith only [hlower, hpos])]
        nlinarith only [hlower]
      exact (not_lt_of_ge hmiddle) habs
    · have hmreal : (0 : ℝ) < m := by positivity
      rw [hdisc]
      field_simp [hb.ne', hmreal.ne']
      nlinarith only [hmonomial]

/-! ## The lower shifted-power obstruction -/

/-- The cubic obtained by perturbing the double-root lower boundary, written
in a variable translated by `r`. -/
def secondOrderLowerPerturbedCubic
    (b u h s r : ℝ) : ℝ[X] :=
  C b * X ^ 3 + C (b * (3 * r + 2 * u - h)) * X ^ 2 +
    C (b * (3 * r ^ 2 + 2 * r * (2 * u - h) + u ^ 2 - 2 * u * h) + s) * X +
      C (b * (r + u) ^ 2 * (r - h) + s * r)

/-- Factored form of the translated lower-boundary perturbation. -/
theorem secondOrderLowerPerturbedCubic_eq_factor
    (b u h s r : ℝ) :
    secondOrderLowerPerturbedCubic b u h s r =
      C b * (X + C r + C u) ^ 2 * (X + C r - C h) + C s * (X + C r) := by
  simp only [secondOrderLowerPerturbedCubic, map_add, map_sub, map_mul,
    map_pow, map_ofNat]
  ring

/-- The discriminant of the perturbed lower-boundary cubic. -/
theorem cubicDiscr_secondOrderLowerPerturbedCubic
    (b u h s r : ℝ) :
    cubicDiscr (secondOrderLowerPerturbedCubic b u h s r) =
      -b * s *
        (4 * b ^ 2 * u * (u + h) ^ 3 -
          b * (h ^ 2 + 20 * u * h - 8 * u ^ 2) * s + 4 * s ^ 2) := by
  rw [secondOrderLowerPerturbedCubic, cubicDiscr_of_coeffs]
  ring

/-- Increasing the linear coefficient away from the double-root boundary
makes the lower cubic discriminant negative. -/
theorem cubicDiscr_secondOrderLowerPerturbedCubic_neg
    {b u h s r : ℝ}
    (hb : 0 < b) (hu : 0 < u) (hh : 0 < h) (hhu : h < 2 * u)
    (hs : 0 < s) :
    cubicDiscr (secondOrderLowerPerturbedCubic b u h s r) < 0 := by
  let A := h ^ 2 + 20 * u * h - 8 * u ^ 2
  let B := 4 * b ^ 2 * u * (u + h) ^ 3 - b * A * s + 4 * s ^ 2
  have hgap : 0 < 8 * u - h := by linarith
  have htail : 0 < b ^ 2 / 4 * h * (8 * u - h) ^ 3 := by positivity
  have hid : 4 * B = (4 * s - b * A / 2) ^ 2 +
      b ^ 2 / 4 * h * (8 * u - h) ^ 3 := by
    dsimp [A, B]
    ring
  have hB : 0 < B := by nlinarith [sq_nonneg (4 * s - b * A / 2)]
  rw [cubicDiscr_secondOrderLowerPerturbedCubic]
  dsimp only [A, B] at hB
  nlinarith [mul_pos (mul_pos hb hs) hB]

/-- The lower perturbed cubic has degree three and only one coefficient sign
variation. -/
private theorem secondOrderLowerPerturbedCubic_degree_and_signVariations
    {b u h s : ℝ}
    (hb : 0 < b) (hu : 0 < u) (hh : 0 < h) (hhu : h < 2 * u)
    (_hs : 0 < s) :
    (secondOrderLowerPerturbedCubic b u h s 0).natDegree = 3 ∧
      (secondOrderLowerPerturbedCubic b u h s 0).signVariations ≤ 1 := by
  let p := secondOrderLowerPerturbedCubic b u h s 0
  have hpdeg : p.natDegree = 3 := by
    dsimp only [p, secondOrderLowerPerturbedCubic]
    exact natDegree_cubic hb.ne'
  have hpcoeff3 : p.coeff 3 = b := by
    dsimp only [p, secondOrderLowerPerturbedCubic]
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X,
      mul_ite, mul_one, mul_zero]
    norm_num
  have hpcoeff2 : p.coeff 2 = b * (2 * u - h) := by
    dsimp only [p, secondOrderLowerPerturbedCubic]
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X,
      mul_ite, mul_one, mul_zero]
    norm_num
  have hpcoeff0 : p.coeff 0 = -(b * u ^ 2 * h) := by
    dsimp only [p, secondOrderLowerPerturbedCubic]
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X,
      mul_ite, mul_one, mul_zero]
    norm_num
  have hlead : 0 < p.leadingCoeff := by
    rw [leadingCoeff, hpdeg]
    rwa [hpcoeff3]
  have hnext : 0 < p.nextCoeff := by
    rw [nextCoeff_of_natDegree_pos (hpdeg.symm ▸ by norm_num), hpdeg]
    rw [hpcoeff2]
    exact mul_pos hb (by linarith)
  refine ⟨hpdeg, ?_⟩
  rw [← signVariations_eraseLead (P := p) (by
    rw [sign_pos hlead, sign_pos hnext])]
  have hvariation :=
    List.signVariations_le_length_sub_one p.eraseLead.coeffList
  have hdeg : p.eraseLead.natDegree = 2 := by
    rw [natDegree_eraseLead hnext.ne', hpdeg]
  have he0 : p.eraseLead ≠ 0 :=
    mt nextCoeff_eq_zero_of_eraseLead_eq_zero hnext.ne'
  have hle : p.eraseLead.signVariations ≤ 2 := by
    simpa [Polynomial.signVariations, he0, hdeg] using hvariation
  have htrailp : p.trailingCoeff = -(b * u ^ 2 * h) := by
    rw [trailingCoeff_eq_coeff_zero]
    · exact hpcoeff0
    · rw [hpcoeff0]
      exact neg_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero hb.ne' (pow_ne_zero 2 hu.ne')) hh.ne')
  have htrail : p.eraseLead.trailingCoeff < 0 := by
    rw [trailingCoeff_eraseLead_of_ne_zero he0, htrailp]
    exact neg_neg_of_pos (mul_pos (mul_pos hb (sq_pos_of_pos hu)) hh)
  have hqlead : 0 < p.eraseLead.leadingCoeff := by
    rw [leadingCoeff_eraseLead_eq_nextCoeff hnext.ne']
    exact hnext
  have hodd : Odd p.eraseLead.signVariations := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have hsign :=
      (even_signVariations_iff_sign_leadingCoeff_eq_sign_trailingCoeff he0).mp heven
    rw [sign_pos hqlead, sign_neg htrail] at hsign
    simp at hsign
  rcases hodd with ⟨k, hk⟩
  lia

/-- The recentered lower perturbation is strictly negative on the
nonpositive half-line. -/
private theorem secondOrderLowerPerturbedCubic_eval_neg_of_nonpos
    {b u h s x : ℝ} (hb : 0 < b) (hu : 0 < u) (hh : 0 < h)
    (hs : 0 < s) (hx : x ≤ 0) :
    (secondOrderLowerPerturbedCubic b u h s 0).eval x < 0 := by
  have hevalform : (secondOrderLowerPerturbedCubic b u h s 0).eval x =
      b * (x + u) ^ 2 * (x - h) + s * x := by
    rw [secondOrderLowerPerturbedCubic_eq_factor]
    simp
  by_cases hxzero : x = 0
  · subst x
    rw [hevalform]
    nlinarith [mul_pos (mul_pos hb (sq_pos_of_pos hu)) hh]
  · have hxneg : x < 0 := lt_of_le_of_ne hx hxzero
    have hfirst : b * (x + u) ^ 2 * (x - h) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hb.le (sq_nonneg _)) (by linarith)
    rw [hevalform]
    nlinarith [mul_neg_of_pos_of_neg hs hxneg]

/-- A positive perturbation of the lower-boundary cubic has only one real
root, counted with multiplicity; that root is positive in recentered
coordinates. -/
theorem positiveRootCount_secondOrderLowerPerturbedCubic_eq_one
    {b u h s : ℝ}
    (hb : 0 < b) (hu : 0 < u) (hh : 0 < h) (hhu : h < 2 * u)
    (hs : 0 < s) :
    (secondOrderLowerPerturbedCubic b u h s 0).positiveRootCount = 1 := by
  let p := secondOrderLowerPerturbedCubic b u h s 0
  obtain ⟨hpdeg, hvar⟩ :=
    secondOrderLowerPerturbedCubic_degree_and_signVariations hb hu hh hhu hs
  change p.natDegree = 3 at hpdeg
  change p.signVariations ≤ 1 at hvar
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp] at hpdeg
    norm_num at hpdeg
  obtain ⟨x, hx⟩ := cubic_exists_isRoot hpdeg
  have hxpos : 0 < x := by
    by_contra hxnot
    have heval := secondOrderLowerPerturbedCubic_eval_neg_of_nonpos
      hb hu hh hs (le_of_not_gt hxnot)
    exact (ne_of_lt heval) hx
  have hxmem : x ∈ p.roots := (mem_roots hp0).2 hx
  have hcountPos : 0 < p.positiveRootCount :=
    Multiset.countP_pos_of_mem hxmem hxpos
  have hcountLe := (descartes_rule_of_signs p).1.trans hvar
  lia

/-- The perturbed boundary cubic has exactly one real root counted with
multiplicity: its positive-root count is one and every real root is positive. -/
theorem secondOrderLowerPerturbedCubic_has_one_real_root
    {b u h s : ℝ}
    (hb : 0 < b) (hu : 0 < u) (hh : 0 < h) (hhu : h < 2 * u)
    (hs : 0 < s) :
    (secondOrderLowerPerturbedCubic b u h s 0).positiveRootCount = 1 ∧
      ∀ x, (secondOrderLowerPerturbedCubic b u h s 0).IsRoot x → 0 < x := by
  refine ⟨positiveRootCount_secondOrderLowerPerturbedCubic_eq_one
    hb hu hh hhu hs, ?_⟩
  intro x hx
  by_contra hxnot
  have heval := secondOrderLowerPerturbedCubic_eval_neg_of_nonpos
    hb hu hh hs (le_of_not_gt hxnot)
  exact (ne_of_lt heval) hx

/-- Coefficient matching identifies the shifted-power residual with the
translated perturbation of the lower-boundary cubic. -/
theorem secondOrderRayOperator_shifted_pow_eq_lowerPerturbedCubic
    (a b c d f r u h T : ℝ) (n : ℕ)
    (hquad : a - b * r + d * (n + 2) = b * (2 * u - h))
    (hlin : (n + 2) * (T - d * r + f * (n + 1)) =
      b * (u ^ 2 - 2 * u * h))
    (hconst : (n + 2) * (n + 1) * f * r = b * u ^ 2 * h) :
    secondOrderRayOperator a b c d f ((X + C r) ^ (n + 2)) =
      (X + C r) ^ n *
        secondOrderLowerPerturbedCubic b u h ((n + 2) * (c - T)) r := by
  rw [secondOrderRayOperator_shifted_pow_recentered_cubic,
    secondOrderLowerPerturbedCubic_eq_factor]
  simp only [map_add, map_sub, map_mul]
  congr 1
  apply Polynomial.funext
  intro x
  simp only [map_natCast, map_one, eval_sub, eval_add, eval_mul, eval_C,
    eval_pow, eval_X, eval_natCast, eval_one]
  rw [hquad, hconst]
  linear_combination (x + r) * hlin

/-- At the lower threshold, the shifted-power residual has the boundary
factorization `b (y+u)^2 (y-h)`. -/
theorem secondOrderRayOperator_shifted_pow_lower_boundary_factor
    (a b d f r u h T : ℝ) (n : ℕ)
    (hquad : a - b * r + d * (n + 2) = b * (2 * u - h))
    (hlin : (n + 2) * (T - d * r + f * (n + 1)) =
      b * (u ^ 2 - 2 * u * h))
    (hconst : (n + 2) * (n + 1) * f * r = b * u ^ 2 * h) :
    secondOrderRayOperator a b T d f ((X + C r) ^ (n + 2)) =
      (X + C r) ^ n *
        (C b * (X + C r + C u) ^ 2 * (X + C r - C h)) := by
  rw [secondOrderRayOperator_shifted_pow_eq_lowerPerturbedCubic
    a b T d f r u h T n hquad hlin hconst,
    secondOrderLowerPerturbedCubic_eq_factor]
  simp

/-- Above the lower boundary, the matched shifted-power residual has negative
cubic discriminant and therefore does not split. -/
theorem not_splits_secondOrderRayOperator_shifted_pow_of_lower_data
    {a b c d f r u h T : ℝ} {n : ℕ}
    (hb : 0 < b) (hu : 0 < u) (hh : 0 < h) (hhu : h < 2 * u)
    (hc : T < c)
    (hquad : a - b * r + d * (n + 2) = b * (2 * u - h))
    (hlin : (n + 2) * (T - d * r + f * (n + 1)) =
      b * (u ^ 2 - 2 * u * h))
    (hconst : (n + 2) * (n + 1) * f * r = b * u ^ 2 * h) :
    ¬(secondOrderRayOperator a b c d f ((X + C r) ^ (n + 2))).Splits := by
  let s : ℝ := (n + 2) * (c - T)
  let q := secondOrderLowerPerturbedCubic b u h s r
  have hs : 0 < s := by dsimp [s]; positivity
  have hqdeg : q.natDegree ≤ 3 := by
    dsimp only [q, secondOrderLowerPerturbedCubic]
    exact (natDegree_cubic hb.ne').le
  have hqdisc : cubicDiscr q < 0 :=
    cubicDiscr_secondOrderLowerPerturbedCubic_neg hb hu hh hhu hs
  have hqsplit : ¬q.Splits :=
    not_splits_of_cubicDiscr_neg_of_natDegree_le_three hqdeg hqdisc
  intro hout
  rw [secondOrderRayOperator_shifted_pow_eq_lowerPerturbedCubic
    a b c d f r u h T n hquad hlin hconst] at hout
  change ((X + C r) ^ n * q).Splits at hout
  have hq0 : q ≠ 0 := by
    intro hzero
    apply hqsplit
    rw [hzero]
    exact Polynomial.Splits.zero
  have hfactor0 : (X + C r) ^ n ≠ 0 := by
    exact pow_ne_zero n (X_add_C_ne_zero r)
  have hqreal := isRealRooted_of_dvd (mul_ne_zero hfactor0 hq0) hout hq0
    (dvd_mul_left q ((X + C r) ^ n))
  exact hqsplit hqreal.2

/-- The quadratic coefficient identity follows from the elementary lower
shift formulas and the simplified value of `b*h`. -/
private theorem secondOrder_lower_quad_identity
    {a b d k M r u h : ℝ} (hb : b ≠ 0) (hk : k ≠ 0)
    (hr : r = (a - M * k) * (d + k) / (2 * b * k))
    (hu : u = M * (d + k) / (2 * b))
    (hbeq : b * h = (a - M * k) * (d - k) / (2 * k)) :
    a - b * r + d * M = b * (2 * u - h) := by
  rw [mul_sub, hbeq, hr, hu]
  field_simp [hb, hk]
  ring

/-- The linear coefficient identity follows from the same lower shift data
and the scalar relation replacing `f*(M-1)`. -/
private theorem secondOrder_lower_linear_identity
    {a b d f k M r u h T : ℝ} (hb : b ≠ 0) (hk : k ≠ 0)
    (hr : r = (a - M * k) * (d + k) / (2 * b * k))
    (hu : u = M * (d + k) / (2 * b))
    (hT : T = a * (d + k) / (2 * b))
    (hbeq : b * h = (a - M * k) * (d - k) / (2 * k))
    (hfrel : f * (M - 1) = M * (d ^ 2 - k ^ 2) / (4 * b)) :
    M * (T - d * r + f * (M - 1)) = b * (u ^ 2 - 2 * u * h) := by
  rw [show b * (u ^ 2 - 2 * u * h) =
    b * u ^ 2 - 2 * u * (b * h) by ring, hbeq, hr, hu, hT, hfrel]
  field_simp [hb, hk]
  ring

/-- The lower-branch index inequalities make all shifted-power parameters
positive and force the quadratic coefficient condition `h < 2u`. -/
private theorem secondOrder_lower_shift_signs
    {a b d f delta M k : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hM : 1 < M) (hk : 0 < k)
    (hksq : k ^ 2 = delta + 4 * b * f / M)
    (hmhi : a ^ 2 ≤ delta * M * (M + 1))
    (hlower : M ^ 2 * delta + 4 * b * f * M < a ^ 2) :
    let r := (a - M * k) * (d + k) / (2 * b * k)
    let u := M * (d + k) / (2 * b)
    let h := f * M * (M - 1) * r / (b * u ^ 2)
    0 < r ∧ 0 < u ∧ 0 < h ∧ h < 2 * u := by
  dsimp only
  let r := (a - M * k) * (d + k) / (2 * b * k)
  let u := M * (d + k) / (2 * b)
  let h := f * M * (M - 1) * r / (b * u ^ 2)
  have haMk : M * k < a := by
    have hsquares : (M * k) ^ 2 < a ^ 2 := by
      rw [mul_pow, hksq]
      field_simp [ne_of_gt hM]
      nlinarith
    nlinarith [sq_nonneg (a + M * k)]
  have hr : 0 < r := by dsimp [r]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hdiff : a - M * k < k := by
    have hproductLe :
        (a - M * k) * (a + M * k) ≤ M * (delta - 4 * b * f) := by
      have hid : (a - M * k) * (a + M * k) = a ^ 2 - M ^ 2 * k ^ 2 := by ring
      rw [hid, hksq]
      field_simp [ne_of_gt hM]
      nlinarith
    have hproduct : (a - M * k) * (a + M * k) < M * k ^ 2 := by
      apply hproductLe.trans_lt
      have hpos : 0 < 4 * b * f / M := by positivity
      have : delta - 4 * b * f < k ^ 2 := by rw [hksq]; nlinarith
      exact mul_lt_mul_of_pos_left this (lt_trans zero_lt_one hM)
    by_contra hnot
    have hkdiff : k ≤ a - M * k := le_of_not_gt hnot
    have hsum : M * k < a + M * k := by nlinarith
    have hsmall : M * k * k < k * (a + M * k) := by
      nlinarith [mul_lt_mul_of_pos_right hsum hk]
    have hlarge : k * (a + M * k) ≤ (a - M * k) * (a + M * k) :=
      mul_le_mul_of_nonneg_right hkdiff (by nlinarith)
    nlinarith
  have htarget :
      2 * b * f * (M - 1) * (a - M * k) < M ^ 2 * k * (d + k) ^ 2 := by
    have hleft :
        2 * b * f * (M - 1) * (a - M * k) < k ^ 2 * M * k := by
      have hbfk : 2 * b * f < k ^ 2 := by
        rw [hksq]
        have : 0 ≤ 4 * b * f / M := by positivity
        nlinarith
      gcongr
      nlinarith
    have hdpos : 0 < d := by
      rw [hdisc] at hdelta
      nlinarith [mul_pos hb hf, sq_nonneg d]
    have hsq : k ^ 2 < (d + k) ^ 2 := by nlinarith
    have hMpow : M < M ^ 2 := by nlinarith
    have hfirst := mul_lt_mul_of_pos_right hMpow (mul_pos (sq_pos_of_pos hk) hk)
    have hMpos : 0 < M := lt_trans zero_lt_one hM
    have hsecond := mul_lt_mul_of_pos_left hsq (mul_pos (sq_pos_of_pos hMpos) hk)
    nlinarith
  have hhu : h < 2 * u := by
    dsimp [h, u, r]
    field_simp [hb.ne', hk.ne', ne_of_gt hM]
    nlinarith
  exact ⟨hr, hu, hh, hhu⟩

/-- The minimizing-index inequalities make the lower shifted-power parameters
positive, keep `h < 2u`, and give the three coefficient identities. -/
private theorem exists_secondOrder_lower_shift_data
    {a b d f delta : ℝ} {m : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hm : 2 ≤ m)
    (hmhi : a ^ 2 ≤ delta * (m : ℝ) * ((m : ℝ) + 1))
    (hlower : (m : ℝ) ^ 2 * delta + 4 * b * f * m < a ^ 2) :
    ∃ k r u h T : ℝ,
      k = Real.sqrt (delta + 4 * b * f / m) ∧
      r = (a - m * k) * (d + k) / (2 * b * k) ∧
      u = m * (d + k) / (2 * b) ∧
      h = f * m * (m - 1) * r / (b * u ^ 2) ∧
      T = a * (d + k) / (2 * b) ∧
      0 < r ∧ 0 < u ∧ 0 < h ∧ h < 2 * u ∧
      a - b * r + d * m = b * (2 * u - h) ∧
      m * (T - d * r + f * (m - 1)) = b * (u ^ 2 - 2 * u * h) ∧
      m * (m - 1) * f * r = b * u ^ 2 * h := by
  let M : ℝ := m
  let k := Real.sqrt (delta + 4 * b * f / M)
  let r := (a - M * k) * (d + k) / (2 * b * k)
  let u := M * (d + k) / (2 * b)
  let h := f * M * (M - 1) * r / (b * u ^ 2)
  let T := a * (d + k) / (2 * b)
  have hM : 1 < M := by dsimp [M]; norm_cast
  have hkarg : 0 < delta + 4 * b * f / M := by positivity
  have hk : 0 < k := Real.sqrt_pos.2 hkarg
  have hksq : k ^ 2 = delta + 4 * b * f / M :=
    Real.sq_sqrt hkarg.le
  obtain ⟨hr, hu, hh, hhu⟩ := secondOrder_lower_shift_signs
    ha hb hd hf hdelta hdisc hM hk hksq hmhi hlower
  change 0 < r at hr
  change 0 < u at hu
  change 0 < h at hh
  change h < 2 * u at hhu
  have hconst : M * (M - 1) * f * r = b * u ^ 2 * h := by
    dsimp [h]
    field_simp [hb.ne', hu.ne']
  have hrel : 4 * b * f * (M - 1) = M * (d ^ 2 - k ^ 2) := by
    field_simp [ne_of_gt hM] at hksq
    linear_combination hksq + M * hdisc
  have hhalf : 2 * b * f * (M - 1) = M * (d ^ 2 - k ^ 2) / 2 := by
    calc
      _ = (4 * b * f * (M - 1)) / 2 := by ring
      _ = _ := by rw [hrel]
  have hfrel : f * (M - 1) = M * (d ^ 2 - k ^ 2) / (4 * b) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hb.ne')).2
    calc
      f * (M - 1) * (4 * b) = 4 * b * f * (M - 1) := by ring
      _ = _ := hrel
  have hbeq : b * h = (a - M * k) * (d - k) / (2 * k) := by
    have hfirst : b * h =
        2 * b * f * (M - 1) * (a - M * k) / (M * k * (d + k)) := by
      dsimp [h, r, u]
      field_simp [hb.ne', hk.ne', ne_of_gt hM]
    rw [hfirst]
    rw [hhalf]
    field_simp [hk.ne', ne_of_gt hM, (show d + k ≠ 0 by positivity)]
    ring
  have hquad : a - b * r + d * M = b * (2 * u - h) := by
    exact secondOrder_lower_quad_identity hb.ne' hk.ne' rfl rfl hbeq
  have hlin : M * (T - d * r + f * (M - 1)) =
      b * (u ^ 2 - 2 * u * h) := by
    exact secondOrder_lower_linear_identity hb.ne' hk.ne' rfl rfl rfl hbeq hfrel
  refine ⟨k, r, u, h, T, rfl, rfl, rfl, rfl, rfl, hr, hu, hh, hhu, ?_⟩
  exact ⟨hquad, hlin, hconst⟩

/-- The degree-one shifted-power test gives the quadratic obstruction in the
lower branch. -/
private theorem not_secondOrderRayPreserving_of_lower_branch_one
    {a b c d f delta : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hd : 0 ≤ d)
    (hdisc : delta = d ^ 2 - 4 * b * f)
    (hlower : d ^ 2 < a ^ 2)
    (habove : a * (d + Real.sqrt (delta + 4 * b * f)) / (2 * b) < c) :
    ¬SecondOrderRayPreserving a b c d f := by
  have hsqrt : Real.sqrt (delta + 4 * b * f) = d := by
    rw [hdisc]
    simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hd]
  have hc : a * d / b < c := by
    rw [hsqrt] at habove
    field_simp [hb.ne'] at habove ⊢
    nlinarith
  have had : d < a := by
    nlinarith [sq_nonneg (a + d)]
  let r := (a - d) / b
  have hr : 0 < r := by dsimp [r]; positivity
  have hinput : IsPFPolynomial ((X + C r) : ℝ[X]) :=
    isPFPolynomial_X_add_C hr.le
  have hout : secondOrderRayOperator a b c d f (X + C r) =
      C b * X ^ 2 + C (2 * a) * X + C (a * r + c) := by
    rw [secondOrderRayOperator_eq_formula]
    apply Polynomial.funext
    intro x
    simp [r]
    field_simp [hb.ne']
    ring
  have hnegative : discrim b (2 * a) (a * r + c) < 0 := by
    have hbc : a * d < b * c := by
      simpa [mul_comm] using (div_lt_iff₀ hb).mp hc
    have hid : discrim b (2 * a) (a * r + c) = 4 * (a * d - b * c) := by
      dsimp [r]
      simp only [discrim]
      field_simp [hb.ne']
      ring
    rw [hid]
    nlinarith
  intro hpres
  have hsplits := (hpres _ hinput).eq_zero_or_splits
  rw [hout] at hsplits
  rcases hsplits with hzero | hsplits
  · have hdegree : (C b * X ^ 2 + C (2 * a) * X + C (a * r + c)).natDegree = 2 :=
      natDegree_quadratic hb.ne'
    rw [hzero] at hdegree
    simp at hdegree
  · exact (quadraticPoly_not_splits_of_discrim_neg hb.ne' hnegative) hsplits

/-- In the lower scalar branch, exceeding the explicit threshold produces a
shifted-power PF counterexample. The case `m = 1` is the separate quadratic
test; higher degrees use the perturbed boundary cubic. -/
theorem not_secondOrderRayPreserving_of_lower_branch
    {a b c d f delta : ℝ} {m : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hm : 1 ≤ m)
    (hmhi : a ^ 2 ≤ delta * (m : ℝ) * ((m : ℝ) + 1))
    (hlower : (m : ℝ) ^ 2 * delta + 4 * b * f * m < a ^ 2)
    (habove : a * (d + Real.sqrt (delta + 4 * b * f / m)) / (2 * b) < c) :
    ¬SecondOrderRayPreserving a b c d f := by
  by_cases hmone : m = 1
  · subst m
    apply not_secondOrderRayPreserving_of_lower_branch_one ha hb hd hdisc
    · norm_num at hlower ⊢
      rw [hdisc] at hlower
      nlinarith
    · simpa using habove
  have hmtwo : 2 ≤ m := by lia
  obtain ⟨k, r, u, h, T, hk, hrdef, hudef, hhdef, hT, hr, hu, hh, hhu,
      hquad, hlin, hconst⟩ :=
    exists_secondOrder_lower_shift_data ha hb hd hf hdelta hdisc hmtwo hmhi hlower
  have hTc : T < c := by rw [hT, hk]; exact habove
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hmtwo
  norm_num [Nat.cast_add] at hquad hlin hconst
  have hnot : ¬(secondOrderRayOperator a b c d f
      ((X + C r) ^ (n + 2))).Splits := by
    apply not_splits_secondOrderRayOperator_shifted_pow_of_lower_data
      hb hu hh hhu hTc
    · convert hquad using 1; ring
    · convert hlin using 1; ring
    · convert hconst using 1; ring
  intro hpres
  have hout := hpres _ ((isPFPolynomial_X_add_C hr.le).pow (n + 2))
  apply hnot
  exact hout.splits

/-- In the lower branch at the minimizing index, universal preservation is
equivalent to the explicit lower threshold. -/
theorem secondOrderRayPreserving_iff_lower_bound_at_index
    {a b c d f delta : ℝ} {m : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hm : 1 ≤ m)
    (hmlo : delta * (m : ℝ) * ((m : ℝ) - 1) ≤ a ^ 2)
    (hmhi : a ^ 2 ≤ delta * (m : ℝ) * ((m : ℝ) + 1))
    (hlower : (m : ℝ) ^ 2 * delta + 4 * b * f * m < a ^ 2) :
    SecondOrderRayPreserving a b c d f ↔
      c ≤ a * (d + Real.sqrt (delta + 4 * b * f / m)) / (2 * b) := by
  constructor
  · intro hpres
    by_contra hbound
    exact (not_secondOrderRayPreserving_of_lower_branch
      ha hb hd hf hdelta hdisc hm hmhi hlower (lt_of_not_ge hbound)) hpres
  · intro hbound
    apply secondOrderRayPreserving_of_three_branch_at_index
      ha hb hc hd hf hdelta hdisc hm hmlo hmhi
    exact Or.inl ⟨hlower, hbound⟩

/-- The middle threshold is exactly the nonnegative monomial-residual
discriminant bound. -/
private theorem secondOrder_middle_discrim_nonneg_iff_bound
    {a b c d f delta : ℝ} {m : ℕ}
    (hb : 0 < b) (hm : 1 ≤ m)
    (hdisc : delta = d ^ 2 - 4 * b * f) :
    0 ≤ (a + d * m) ^ 2 - 4 * b * m * (c + f * (m - 1)) ↔
      c ≤ f + a * d / (2 * b) + m * delta / (4 * b) +
        a ^ 2 / (4 * b * m) := by
  have hmreal : (0 : ℝ) < m := by positivity
  constructor <;> intro h
  · rw [hdisc]
    field_simp [hb.ne', hmreal.ne'] at h ⊢
    nlinarith
  · rw [hdisc] at h
    field_simp [hb.ne', hmreal.ne'] at h ⊢
    nlinarith

/-- Failure of both the lower and middle tests forces the strict upper
branch inequality. -/
private theorem secondOrder_upper_branch_of_not_lower_not_middle
    {a b f delta : ℝ} {m : ℕ}
    (hb : 0 < b) (hf : 0 < f) (hm : 1 ≤ m)
    (hlower : ¬a ^ 2 > (m : ℝ) ^ 2 * delta + 4 * b * f * m)
    (hmiddle : ¬|(m : ℝ) ^ 2 * delta - a ^ 2| ≤ 4 * b * f * m) :
    a ^ 2 + 4 * b * f * m < (m : ℝ) ^ 2 * delta := by
  have hmreal : (0 : ℝ) < m := by positivity
  have hq : 0 < 4 * b * f * (m : ℝ) := by positivity
  have hlower' := le_of_not_gt hlower
  have hmiddle' := lt_of_not_ge hmiddle
  by_cases hsign : 0 ≤ (m : ℝ) ^ 2 * delta - a ^ 2
  · rw [abs_of_nonneg hsign] at hmiddle'
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge hsign)] at hmiddle'
    nlinarith

/-- Complete three-branch classification at the minimizing integer index.
The three alternatives are the lower, middle, and upper formulas for the
minimum gap threshold. -/
theorem secondOrderRayPreserving_iff_three_branch_at_index
    {a b c d f delta : ℝ} {m : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hm : 1 ≤ m)
    (hmlo : delta * (m : ℝ) * ((m : ℝ) - 1) ≤ a ^ 2)
    (hmhi : a ^ 2 ≤ delta * (m : ℝ) * ((m : ℝ) + 1)) :
    SecondOrderRayPreserving a b c d f ↔
      ((a ^ 2 > (m : ℝ) ^ 2 * delta + 4 * b * f * m ∧
        c ≤ a * (d + Real.sqrt (delta + 4 * b * f / m)) / (2 * b)) ∨
      (¬a ^ 2 > (m : ℝ) ^ 2 * delta + 4 * b * f * m ∧
        |(m : ℝ) ^ 2 * delta - a ^ 2| ≤ 4 * b * f * m ∧
        c ≤ f + a * d / (2 * b) + m * delta / (4 * b) +
          a ^ 2 / (4 * b * m)) ∨
      (¬a ^ 2 > (m : ℝ) ^ 2 * delta + 4 * b * f * m ∧
        ¬|(m : ℝ) ^ 2 * delta - a ^ 2| ≤ 4 * b * f * m ∧
        c ≤ (a * d + Real.sqrt
          (delta * (a ^ 2 + 4 * b * f * m))) / (2 * b))) := by
  constructor
  · intro hpres
    by_cases hlower : a ^ 2 > (m : ℝ) ^ 2 * delta + 4 * b * f * m
    · left
      exact ⟨hlower, (secondOrderRayPreserving_iff_lower_bound_at_index
        ha hb hc hd hf hdelta hdisc hm hmlo hmhi hlower).mp hpres⟩
    by_cases hmiddle :
        |(m : ℝ) ^ 2 * delta - a ^ 2| ≤ 4 * b * f * m
    · right
      left
      have hmonomial := (secondOrderRayPreserving_iff_middle_discrim_at_index
        ha hb hc hd hf hdelta hdisc hm hmlo hmhi hmiddle).mp hpres
      exact ⟨hlower, hmiddle,
        (secondOrder_middle_discrim_nonneg_iff_bound hb hm hdisc).mp hmonomial⟩
    · right
      right
      have hupper := secondOrder_upper_branch_of_not_lower_not_middle
        hb hf hm hlower hmiddle
      exact ⟨hlower, hmiddle, (secondOrderRayPreserving_iff_upper_bound_at_index
        ha hb hc hd hf hdelta hdisc hm hmlo hmhi hupper).mp hpres⟩
  · intro hbranch
    exact secondOrderRayPreserving_of_three_branch_at_index
      ha hb hc hd hf hdelta hdisc hm hmlo hmhi hbranch

end RealRooted
