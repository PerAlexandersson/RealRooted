module

public import RealRooted.DegreeDropReversal
public import RealRooted.Hadamard.Basic
public import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas
public import RealRooted.Mathlib.Algebra.Ring.Parity

/-!
# Finite-free multiplicative convolution

This file fixes the coefficient normalization for degree-`d` signed
reciprocal reversal and finite-free multiplicative convolution.  With these
conventions, signed reciprocal reversal carries Schur--Szegő composition to
finite-free multiplicative convolution exactly, including in odd degree.
-/

@[expose] public noncomputable section

open Polynomial

namespace RealRooted

/-- Degree-`d` signed reciprocal reversal.  When `p.natDegree ≤ d`, this is
the polynomial `z ^ d * p (-1 / z)`. -/
def signedReciprocal (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  reflect d (p.comp (-X))

/-- Degree-`d` finite-free multiplicative convolution, in the convention

`p = ∑ k, (-1)^k * choose d k * e_k(p) * X^(d-k)`.

The global sign is essential in odd degree. -/
def finiteFreeMultiplicativeConvolution (d : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  C ((-1 : ℝ) ^ d) * (schurSzegoComp d p q).comp (-X)

/-- Coefficients of signed reciprocal reversal, using Mathlib's involutive
`revAt` index. -/
theorem coeff_signedReciprocal (d j : ℕ) (p : ℝ[X]) :
    (signedReciprocal d p).coeff j =
      p.coeff (revAt d j) * (-1 : ℝ) ^ (revAt d j) := by
  rw [signedReciprocal, coeff_reflect, coeff_comp_neg_X]

/-- Coefficients of signed reciprocal reversal inside the degree box. -/
theorem coeff_signedReciprocal_of_le {d j : ℕ} (hj : j ≤ d) (p : ℝ[X]) :
    (signedReciprocal d p).coeff j =
      (-1 : ℝ) ^ (d - j) * p.coeff (d - j) := by
  rw [coeff_signedReciprocal, revAt_le hj]
  ring

/-- Coefficients of finite-free multiplicative convolution. -/
theorem coeff_finiteFreeMultiplicativeConvolution
    (d j : ℕ) (p q : ℝ[X]) :
    (finiteFreeMultiplicativeConvolution d p q).coeff j =
      if j ≤ d then
        (-1 : ℝ) ^ (d - j) *
          (p.coeff j * q.coeff j / (Nat.choose d j : ℝ))
      else 0 := by
  rw [finiteFreeMultiplicativeConvolution, coeff_C_mul,
    coeff_comp_neg_X, coeff_schurSzegoComp]
  by_cases hj : j ≤ d
  · simp only [ite_eq_left hj]
    calc
      (-1 : ℝ) ^ d *
          (p.coeff j * q.coeff j / (Nat.choose d j : ℝ) *
            (-1 : ℝ) ^ j) =
          ((-1 : ℝ) ^ d * (-1 : ℝ) ^ j) *
            (p.coeff j * q.coeff j / (Nat.choose d j : ℝ)) := by ring
      _ = (-1 : ℝ) ^ (d - j) *
            (p.coeff j * q.coeff j / (Nat.choose d j : ℝ)) := by
        rw [Parity.neg_one_pow_mul_eq_neg_one_pow_sub hj]
  · simp only [ite_eq_right hj]
    simp

/-- Signed reciprocal reversal does not leave a valid degree box. -/
theorem natDegree_signedReciprocal_le {d : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ d) :
    (signedReciprocal d p).natDegree ≤ d := by
  unfold signedReciprocal
  simpa only [Polynomial.natDegree_comp_neg_X, max_eq_left hp] using
    (Polynomial.natDegree_reflect_le (N := d) (p := p.comp (-X)))

/-- Finite-free multiplicative convolution has degree at most its ambient
degree. -/
theorem natDegree_finiteFreeMultiplicativeConvolution_le
    (d : ℕ) (p q : ℝ[X]) :
    (finiteFreeMultiplicativeConvolution d p q).natDegree ≤ d := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_finiteFreeMultiplicativeConvolution, ite_eq_right (not_le_of_gt hj)]

@[simp] theorem signedReciprocal_zero (d : ℕ) :
    signedReciprocal d (0 : ℝ[X]) = 0 := by
  simp [signedReciprocal]

@[simp] theorem finiteFreeMultiplicativeConvolution_zero_left
    (d : ℕ) (q : ℝ[X]) :
    finiteFreeMultiplicativeConvolution d 0 q = 0 := by
  simp [finiteFreeMultiplicativeConvolution]

@[simp] theorem finiteFreeMultiplicativeConvolution_zero_right
    (d : ℕ) (p : ℝ[X]) :
    finiteFreeMultiplicativeConvolution d p 0 = 0 := by
  rw [finiteFreeMultiplicativeConvolution, schurSzegoComp_zero_right]
  simp

/-- Signed reciprocal reversal commutes with scalar multiplication. -/
theorem signedReciprocal_C_mul (d : ℕ) (a : ℝ) (p : ℝ[X]) :
    signedReciprocal d (C a * p) = C a * signedReciprocal d p := by
  simp only [signedReciprocal, mul_comp, C_comp, reflect_C_mul]

/-- Finite-free multiplicative convolution is commutative. -/
theorem finiteFreeMultiplicativeConvolution_comm
    (d : ℕ) (p q : ℝ[X]) :
    finiteFreeMultiplicativeConvolution d p q =
      finiteFreeMultiplicativeConvolution d q p := by
  rw [finiteFreeMultiplicativeConvolution,
    finiteFreeMultiplicativeConvolution, schurSzegoComp_comm]

/-- Scalar multiplication in the left convolution input scales the output. -/
theorem finiteFreeMultiplicativeConvolution_C_mul_left
    (d : ℕ) (a : ℝ) (p q : ℝ[X]) :
    finiteFreeMultiplicativeConvolution d (C a * p) q =
      C a * finiteFreeMultiplicativeConvolution d p q := by
  simp only [finiteFreeMultiplicativeConvolution,
    schurSzegoComp_C_mul_left, mul_comp, C_comp]
  ring

/-- Scalar multiplication in the right convolution input scales the output. -/
theorem finiteFreeMultiplicativeConvolution_C_mul_right
    (d : ℕ) (a : ℝ) (p q : ℝ[X]) :
    finiteFreeMultiplicativeConvolution d p (C a * q) =
      C a * finiteFreeMultiplicativeConvolution d p q := by
  rw [finiteFreeMultiplicativeConvolution_comm d p (C a * q),
    finiteFreeMultiplicativeConvolution_C_mul_left,
    finiteFreeMultiplicativeConvolution_comm d q p]

/-- Signed reciprocal reversal is zero exactly when its input is zero. -/
@[simp] theorem signedReciprocal_eq_zero_iff {d : ℕ} {p : ℝ[X]} :
    signedReciprocal d p = 0 ↔ p = 0 := by
  rw [signedReciprocal, reflect_eq_zero_iff, comp_neg_X_eq_zero_iff]

private theorem natDegree_comp_neg_X_le {d : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ d) :
    (p.comp (-X)).natDegree ≤ d := by
  simpa only [Polynomial.natDegree_comp_neg_X] using hp

/-- A nonzero constant coefficient makes the signed reciprocal have exactly
the ambient degree. -/
theorem natDegree_signedReciprocal_eq_of_coeff_zero_ne
    {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) (hp0 : p.coeff 0 ≠ 0) :
    (signedReciprocal d p).natDegree = d := by
  apply DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne
    (natDegree_comp_neg_X_le hp)
  simpa [coeff_comp_neg_X] using hp0

/-- The leading coefficient of a full-degree signed reciprocal is the
original constant coefficient. -/
theorem leadingCoeff_signedReciprocal_eq_coeff_zero
    {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) (hp0 : p.coeff 0 ≠ 0) :
    (signedReciprocal d p).leadingCoeff = p.coeff 0 := by
  have hcomp0 : (p.comp (-X)).coeff 0 ≠ 0 := by simpa [coeff_comp_neg_X] using hp0
  unfold signedReciprocal
  rw [DegreeDropReversal.leadingCoeff_reflect_eq_coeff_zero_of_natDegree_le
    (natDegree_comp_neg_X_le hp) hcomp0]
  simp [coeff_comp_neg_X]

/-- Signed reciprocal reversal preserves splitting inside its degree box. -/
theorem signedReciprocal_splits_of_splits
    {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) (hsplit : p.Splits) :
    (signedReciprocal d p).Splits :=
  Polynomial.Splits.reflect hsplit.comp_neg_X
    (natDegree_comp_neg_X_le hp)

/-- Applying degree-`d` signed reciprocal reversal twice gives the parity
scalar `(-1)^d`.  Thus this operation is not literally involutive in odd
degree. -/
theorem signedReciprocal_signedReciprocal
    {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) :
    signedReciprocal d (signedReciprocal d p) =
      C ((-1 : ℝ) ^ d) * p := by
  unfold signedReciprocal
  have hcomp : (p.comp (-X)).natDegree ≤ d := by
    simpa only [Polynomial.natDegree_comp_neg_X] using hp
  have hreflect : (reflect d (p.comp (-X))).natDegree ≤ d := by
    simpa only [max_eq_left hcomp] using
      (Polynomial.natDegree_reflect_le (N := d) (p := p.comp (-X)))
  rw [Polynomial.reflect_comp_neg_X_of_natDegree_le hreflect,
    Polynomial.reflect_reflect, Polynomial.comp_neg_X_comp_neg_X]

/-- The normalized elementary coefficient in the standard finite-free
multiplicative convention. -/
def finiteElementaryCoeff (d k : ℕ) (p : ℝ[X]) : ℝ :=
  (-1 : ℝ) ^ k * p.coeff (d - k) / (Nat.choose d k : ℝ)

/-- Finite-free multiplicative convolution multiplies normalized elementary
coefficients. -/
theorem finiteElementaryCoeff_finiteFreeMultiplicativeConvolution
    {d k : ℕ} (hk : k ≤ d) (p q : ℝ[X]) :
    finiteElementaryCoeff d k
        (finiteFreeMultiplicativeConvolution d p q) =
      finiteElementaryCoeff d k p * finiteElementaryCoeff d k q := by
  unfold finiteElementaryCoeff
  rw [coeff_finiteFreeMultiplicativeConvolution,
    ite_eq_left (Nat.sub_le d k), Nat.sub_sub_self hk, Nat.choose_symm hk]
  let s : ℝ := (-1 : ℝ) ^ k
  have hs : s * s = 1 := by simpa [pow_two] using (Parity.neg_one_pow_sq k)
  have hchoose : (Nat.choose d k : ℝ) ≠ 0 :=
    Nat.cast_choose_ne_zero (R := ℝ) hk
  change
    s * (s * (p.coeff (d - k) * q.coeff (d - k) /
      (Nat.choose d k : ℝ))) / (Nat.choose d k : ℝ) =
      (s * p.coeff (d - k) / (Nat.choose d k : ℝ)) *
        (s * q.coeff (d - k) / (Nat.choose d k : ℝ))
  field_simp [hchoose]

/-- Finite-free multiplicative convolution of monic degree-`d` polynomials
is again monic of degree `d`. -/
theorem finiteFreeMultiplicativeConvolution_monic
    {d : ℕ} {p q : ℝ[X]} (hp : p.Monic) (hq : q.Monic)
    (hpdeg : p.natDegree = d) (hqdeg : q.natDegree = d) :
    (finiteFreeMultiplicativeConvolution d p q).Monic := by
  have hpcoeff : p.coeff d = 1 := by
    rw [← hpdeg, ← leadingCoeff]
    exact hp.leadingCoeff
  have hqcoeff : q.coeff d = 1 := by
    rw [← hqdeg, ← leadingCoeff]
    exact hq.leadingCoeff
  have houtcoeff :
      (finiteFreeMultiplicativeConvolution d p q).coeff d = 1 := by
    rw [coeff_finiteFreeMultiplicativeConvolution, ite_eq_left le_rfl,
      Nat.sub_self, pow_zero, one_mul, hpcoeff, hqcoeff]
    simp
  have houtdeg :
      (finiteFreeMultiplicativeConvolution d p q).natDegree = d :=
    natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_finiteFreeMultiplicativeConvolution_le d p q)
      (by simp [houtcoeff])
  rw [Monic.def, leadingCoeff, houtdeg, houtcoeff]

/-- Signed reciprocal reversal turns Schur--Szegő composition into
finite-free multiplicative convolution. -/
theorem signedReciprocal_schurSzegoComp
    (d : ℕ) (f g : ℝ[X]) :
    signedReciprocal d (schurSzegoComp d f g) =
      finiteFreeMultiplicativeConvolution d
        (signedReciprocal d f) (signedReciprocal d g) := by
  unfold signedReciprocal finiteFreeMultiplicativeConvolution
  rw [← reflect_schurSzegoComp, schurSzegoComp_comp_neg_X_both]
  exact Polynomial.reflect_comp_neg_X_of_natDegree_le
    (natDegree_schurSzegoComp_le d f g)

/-- Convolution with a signed reciprocal on the right cancels the finite-free
sign and becomes Schur--Szegő composition with ordinary degree-`d`
reflection.  No degree hypotheses are needed because both operations truncate
to the ambient degree box. -/
theorem finiteFreeMultiplicativeConvolution_signedReciprocal_right
    (d : ℕ) (P p : ℝ[X]) :
    finiteFreeMultiplicativeConvolution d P (signedReciprocal d p) =
      schurSzegoComp d P (reflect d p) := by
  ext j
  by_cases hj : j ≤ d
  · rw [coeff_finiteFreeMultiplicativeConvolution, ite_eq_left hj,
      coeff_signedReciprocal_of_le hj,
      coeff_schurSzegoComp_of_le hj, coeff_reflect, revAt_le hj]
    let s : ℝ := (-1 : ℝ) ^ (d - j)
    have hs : s * s = 1 := by simpa [pow_two] using (Parity.neg_one_pow_sq (d - j))
    change
      s * (P.coeff j * (s * p.coeff (d - j)) /
        (Nat.choose d j : ℝ)) =
      P.coeff j * p.coeff (d - j) / (Nat.choose d j : ℝ)
    calc
      s * (P.coeff j * (s * p.coeff (d - j)) /
          (Nat.choose d j : ℝ)) =
          (s * s) *
            (P.coeff j * p.coeff (d - j) / (Nat.choose d j : ℝ)) := by
        ring
      _ = P.coeff j * p.coeff (d - j) /
          (Nat.choose d j : ℝ) := by rw [hs, one_mul]
  · have hjlt : d < j := Nat.lt_of_not_ge hj
    rw [coeff_finiteFreeMultiplicativeConvolution, ite_eq_right hj,
      coeff_schurSzegoComp_eq_zero_of_lt hjlt]

end RealRooted
