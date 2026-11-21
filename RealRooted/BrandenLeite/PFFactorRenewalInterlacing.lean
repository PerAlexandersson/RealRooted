module

public import RealRooted.CombinatorialExamples.WeightedRenewal
import RealRooted.Linear

/-!
# Cross-residue interlacing for PF renewal polynomials

We complete the cross-residue part of issue #2160 using the window proof in
issue #2037 (unpublished manuscript). The periodic weighted fixed-delay
reduction is already formalized in `CombinatorialExamples.WeightedRenewal`.
We extend its normalized driver, whose constant coefficient is one, to any
PF driver with positive constant coefficient by rescaling both variables.

The full window is `R.natDegree * s ≤ R.natDegree * m + 1`. In particular,
any two rows at distance at most `m` interlace, including rows from distinct
residue classes. No transitivity of interlacing is used. As throughout the
library, `StrictInterl` allows shared and repeated roots.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Scaling the renewal driver by a nonzero constant rescales each row and
its variable. The truncated exponent contributes zero outside the range
`m * j ≤ n`, except for the constant coefficient. -/
theorem renewalPolynomial_C_mul (R : ℝ[X]) {c : ℝ} (hc : c ≠ 0)
    {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    renewalPolynomial (C c * R) m n =
      C (c ^ n) * (renewalPolynomial R m n).comp (C ((c ^ m)⁻¹) * X) := by
  ext j
  rw [coeff_renewalPolynomial _ _ _ _ hm, coeff_C_mul,
    comp_C_mul_X_coeff, coeff_renewalPolynomial _ _ _ _ hm,
    mul_pow, ← C_pow, coeff_C_mul]
  by_cases hj : m * j ≤ n
  · have hexp : c ^ (n - m * j) * c ^ (m * j) = c ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    rw [inv_pow, ← pow_mul]
    have hpow : c ^ (m * j) ≠ 0 := pow_ne_zero _ hc
    apply (mul_right_cancel₀ hpow)
    calc
      c ^ (n - m * j) * (R ^ (n - m * j)).coeff j * c ^ (m * j) =
          c ^ n * (R ^ (n - m * j)).coeff j := by
            rw [mul_right_comm, hexp]
      _ = c ^ n * ((R ^ (n - m * j)).coeff j * (c ^ (m * j))⁻¹) *
          c ^ (m * j) := by field_simp
  · have hj0 : j ≠ 0 := by intro h; simp [h] at hj
    simp [Nat.sub_eq_zero_of_le (by lia : n ≤ m * j), coeff_one, hj0]

/-- The full renewal interlacing window for a PF driver with positive
constant coefficient. This is the normalized periodic fixed-delay theorem
after a positive rescaling; the rows need not have the same residue. -/
theorem strictInterl_renewalPolynomial_add_of_coeff_zero_pos
    {R : ℝ[X]} (hR : IsPFPolynomial R) (hR0 : 0 < R.coeff 0)
    {m : ℕ} (hm : m ≠ 0) (n s : ℕ)
    (hs : R.natDegree * s ≤ R.natDegree * m + 1) :
    StrictInterl (renewalPolynomial R m n) (renewalPolynomial R m (n + s)) := by
  let S := C (R.coeff 0)⁻¹ * R
  have hS : IsPFPolynomial S := hR.const_mul (inv_pos.mpr hR0)
  have hS0 : S.coeff 0 = 1 := by simp [S, hR0.ne']
  have hSd : S.natDegree = R.natDegree := natDegree_C_mul (inv_ne_zero hR0.ne')
  have hRS : R = C (R.coeff 0) * S := by
    simp [S, ← mul_assoc, ← C_mul, hR0.ne']
  have hwindow := strictInterl_renewalPolynomial_add S m n s
    hS.hasNonnegCoeffs hS0 hS.splits hm (by simpa [hSd] using hs)
  have hscaled := ((hwindow.comp_C_mul_X (inv_pos.mpr (pow_pos hR0 m))).C_mul_left
    (pow_ne_zero n hR0.ne')).C_mul_right (pow_ne_zero (n + s) hR0.ne')
  conv_lhs => rw [hRS, renewalPolynomial_C_mul S hR0.ne' hm n]
  conv_rhs => rw [hRS, renewalPolynomial_C_mul S hR0.ne' hm (n + s)]
  exact hscaled

/-- Any two renewal rows at distance at most the delay interlace, with no
restriction on their residue classes. Constants and the initial rows are
included. -/
theorem strictInterl_renewalPolynomial_of_le_add
    {R : ℝ[X]} (hR : IsPFPolynomial R) (hR0 : 0 < R.coeff 0)
    {m i j : ℕ} (hm : m ≠ 0) (hij : i ≤ j) (hji : j ≤ i + m) :
    StrictInterl (renewalPolynomial R m i) (renewalPolynomial R m j) := by
  have hgap : R.natDegree * (j - i) ≤ R.natDegree * m + 1 := by
    exact (Nat.mul_le_mul_left R.natDegree (by lia : j - i ≤ m)).trans (by lia)
  simpa [Nat.add_sub_of_le hij] using
    strictInterl_renewalPolynomial_add_of_coeff_zero_pos hR hR0 hm i (j - i) hgap

/-- Ordered residues in one quotient block interlace for a positive-constant
PF driver. The endpoints may coincide. -/
theorem strictInterl_renewalPolynomial_residue_le
    {R : ℝ[X]} (hR : IsPFPolynomial R) (hR0 : 0 < R.coeff 0)
    {m r s : ℕ} (hrs : r ≤ s) (hsm : s < m) (q : ℕ) :
    StrictInterl (renewalPolynomial R m (m * q + r))
      (renewalPolynomial R m (m * q + s)) := by
  exact strictInterl_renewalPolynomial_of_le_add hR hR0 (by lia) (by lia) (by lia)

/-- The residue window crosses the quotient boundary: residue `r` in one
block interlaces residue `s ≤ r` in the next block. This includes consecutive
rows at the last and first residues, and the within-residue comparison. -/
theorem strictInterl_renewalPolynomial_residue_wrap
    {R : ℝ[X]} (hR : IsPFPolynomial R) (hR0 : 0 < R.coeff 0)
    {m r s : ℕ} (hsr : s ≤ r) (hrm : r < m) (q : ℕ) :
    StrictInterl (renewalPolynomial R m (m * q + r))
      (renewalPolynomial R m (m * (q + 1) + s)) := by
  apply strictInterl_renewalPolynomial_of_le_add hR hR0 (by lia)
  · lia
  · lia

end RealRooted
