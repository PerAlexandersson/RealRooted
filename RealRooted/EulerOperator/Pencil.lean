import RealRooted.EulerOperator
import RealRooted.WagnerX.ProperPosition

/-!
# Positive Euler pencils

Proper-position comparisons for positive shifts of the Euler operator
`theta p = X * p'` on polynomial PF families.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A positive Euler pencil lies in proper position with `X * f` for a
polynomial-PF `f` of degree at least two. -/
theorem prec_thetac_X_mul {f : ℝ[X]} (hf : IsPFPolynomial f)
    (hdeg : 2 ≤ f.natDegree) {c : ℝ} (hc : 0 < c) :
    Prec (X * f.derivative + C c * f) (X * f) := by
  have hf0 : f ≠ 0 := by
    intro hzero
    simp_all
  have hfs : f ≠ 0 ∧ f.Splits := hf.ne_zero_and_splits hf0
  have hnn : HasNonnegCoeffs f := hf.hasNonnegCoeffs
  have hleft : Prec (X * f.derivative) (X * f) :=
    prec_X_derivative_X_self_of_splits_nonneg hfs.2 hdeg hnn
  have hself : Prec f (X * f) := prec_self_X_mul_of_nonneg hfs.1 hfs.2 hnn
  have hright : Prec (C c * f) (X * f) := prec_C_mul_left hself hc.ne'
  have hfd_ne : f.derivative ≠ 0 :=
    derivative_ne_zero_of_natDegree_ne_zero (by lia)
  have hXfd_ne : X * f.derivative ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hfd_ne
  have hpos_left : HasPosLeadingCoeff (X * f.derivative) :=
    (hnn.derivative.X_mul).pos_leadingCoeff hXfd_ne
  have hCc_ne : (C c : ℝ[X]) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero]
    grind
  have hCf_ne : C c * f ≠ 0 := mul_ne_zero hCc_ne hf0
  have hpos_right : HasPosLeadingCoeff (C c * f) :=
    (nonnegCoeffs_C_mul hc.le hnn).pos_leadingCoeff hCf_ne
  exact prec_add_of_prec_right_of_posLeadingCoeff hleft hright hpos_left hpos_right

/-- A polynomial-PF `f` precedes every positive Euler pencil of `f` when its
degree is at least two. -/
theorem prec_self_thetac {f : ℝ[X]} (hf : IsPFPolynomial f)
    (hdeg : 2 ≤ f.natDegree) {c : ℝ} (hc : 0 < c) :
    Prec f (X * f.derivative + C c * f) := by
  have hnn : HasNonnegCoeffs f := hf.hasNonnegCoeffs
  have hnn_thc : HasNonnegCoeffs (X * f.derivative + C c * f) :=
    HasNonnegCoeffs.add hnn.derivative.X_mul (nonnegCoeffs_C_mul hc.le hnn)
  exact prec_of_prec_X_mul_of_nonneg (prec_thetac_X_mul hf hdeg hc) hnn hnn_thc

/-- Positive Euler pencils are ordered by the scalar shift. -/
theorem prec_thetaa_thetab {f : ℝ[X]} (hf : IsPFPolynomial f)
    (hdeg : 2 ≤ f.natDegree) {a b : ℝ} (hb : 0 < b) (hab : b < a) :
    Prec (X * f.derivative + C a * f) (X * f.derivative + C b * f) := by
  have hf0 : f ≠ 0 := by
    intro hzero
    simp_all
  have hnn : HasNonnegCoeffs f := hf.hasNonnegCoeffs
  set g := X * f.derivative + C b * f with hg
  have hfg : Prec f g := prec_self_thetac hf hdeg hb
  have hab0 : (0 : ℝ) < a - b := by linarith
  have hcf : Prec (C (a - b) * f) g := prec_C_mul_left hfg hab0.ne'
  have hg0 : g ≠ 0 := hfg.2.1.1
  have hgs : g.Splits := hfg.2.1.2
  have hgg : Prec g g := prec_refl hg0 hgs
  have hCab_ne : (C (a - b) : ℝ[X]) ≠ 0 := by grind
  have hCf_ne : C (a - b) * f ≠ 0 := mul_ne_zero hCab_ne hf0
  have hpos_cf : HasPosLeadingCoeff (C (a - b) * f) :=
    (nonnegCoeffs_C_mul hab0.le hnn).pos_leadingCoeff hCf_ne
  have hnn_g : HasNonnegCoeffs g :=
    HasNonnegCoeffs.add hnn.derivative.X_mul (nonnegCoeffs_C_mul hb.le hnn)
  have hpos_g : HasPosLeadingCoeff g := hnn_g.pos_leadingCoeff hg0
  have hsum : Prec (C (a - b) * f + g) g :=
    prec_add_of_prec_right_of_posLeadingCoeff hcf hgg hpos_cf hpos_g
  grind

end RealRooted
