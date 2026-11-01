module

public import RealRooted.SimpleRoots
public import RealRooted.HermiteBiehler.Basic
public import Mathlib.Algebra.Polynomial.HasseDeriv
import RealRooted.HermiteBiehler.Converse
import RealRooted.CommonInterleaver.RightPencil
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Imaginary central differences

The normalized imaginary central difference is expressed as the finite sum of its odd
derivatives.  Taylor expansion identifies it with evaluation at the two imaginary shifts.
The Hermite--Biehler theorem then gives real, simple roots.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The normalized imaginary central difference of a real polynomial.  The Hasse derivative
`hasseDeriv n` is the ordinary `n`-th derivative divided by `n!`. -/
def imaginaryCentralDifference (h : ℝ) (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    C ((-1) ^ k * h ^ (2 * k)) * hasseDeriv (2 * k + 1) p

/-- The real part of the Taylor shift by `i h`. -/
private def imaginaryShiftRealPart (h : ℝ) (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    C ((-1) ^ k * h ^ (2 * k)) * hasseDeriv (2 * k) p

private lemma C_mul_hasseDeriv_eq_C_mul_iterate_derivative
    (a : ℝ) (n : ℕ) (p : ℝ[X]) :
    C a * hasseDeriv n p = C (a / (n.factorial : ℝ)) * (derivative^[n]) p := by
  have hfactorial : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hderiv := congrFun (factorial_smul_hasseDeriv (R := ℝ) n) p
  have hderiv' : C (n.factorial : ℝ) * hasseDeriv n p = (derivative^[n]) p := by
    simpa [nsmul_eq_mul] using hderiv
  rw [← hderiv', ← mul_assoc, ← C_mul]
  congr 1
  field_simp

/-- The central difference written with ordinary iterated derivatives and factorials. -/
theorem imaginaryCentralDifference_eq_sum_iterate_derivative (h : ℝ) (p : ℝ[X]) :
    imaginaryCentralDifference h p =
      ∑ k ∈ Finset.range (p.natDegree + 1),
        C (((-1) ^ k * h ^ (2 * k)) / ((2 * k + 1).factorial : ℝ)) *
          (derivative^[2 * k + 1]) p := by
  rw [imaginaryCentralDifference]
  apply Finset.sum_congr rfl
  intro k _
  exact C_mul_hasseDeriv_eq_C_mul_iterate_derivative _ _ _

private lemma imaginaryCentralDifference_C_mul {h c : ℝ} (hc : c ≠ 0) (p : ℝ[X]) :
    imaginaryCentralDifference h (C c * p) = C c * imaginaryCentralDifference h p := by
  rw [imaginaryCentralDifference, natDegree_C_mul hc, imaginaryCentralDifference,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show C c * p = c • p by rw [smul_eq_C_mul]]
  rw [LinearMap.map_smul]
  simp only [smul_eq_C_mul]
  ring

private lemma imaginaryShiftRealPart_C_mul {h c : ℝ} (hc : c ≠ 0) (p : ℝ[X]) :
    imaginaryShiftRealPart h (C c * p) = C c * imaginaryShiftRealPart h p := by
  rw [imaginaryShiftRealPart, natDegree_C_mul hc, imaginaryShiftRealPart,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show C c * p = c • p by rw [smul_eq_C_mul]]
  rw [LinearMap.map_smul]
  simp only [smul_eq_C_mul]
  ring

/-- The imaginary central difference of a constant polynomial is zero. -/
theorem imaginaryCentralDifference_eq_zero_of_natDegree_eq_zero
    {p : ℝ[X]} (hp : p.natDegree = 0) (h : ℝ) :
    imaginaryCentralDifference h p = 0 := by
  rw [imaginaryCentralDifference]
  apply Finset.sum_eq_zero
  intro k _
  rw [hasseDeriv_eq_zero_of_lt_natDegree p (2 * k + 1) (by lia), mul_zero]

private lemma natDegree_imaginaryCentralDifference_le (h : ℝ) (p : ℝ[X]) :
    (imaginaryCentralDifference h p).natDegree ≤ p.natDegree - 1 := by
  rw [imaginaryCentralDifference]
  apply natDegree_sum_le_of_forall_le
  intro k _
  exact (natDegree_C_mul_le _ _).trans
    ((natDegree_hasseDeriv_le p (2 * k + 1)).trans (by lia))

private lemma coeff_imaginaryCentralDifference_top {p : ℝ[X]}
    (hp : 1 ≤ p.natDegree) (h : ℝ) :
    (imaginaryCentralDifference h p).coeff (p.natDegree - 1) =
      (p.natDegree : ℝ) * p.leadingCoeff := by
  rw [imaginaryCentralDifference, finsetSum_coeff, Finset.sum_eq_single 0]
  · norm_num
    rw [coeff_derivative, Nat.sub_add_cancel hp, coeff_natDegree]
    rw [show ((p.natDegree - 1 : ℕ) : ℝ) + 1 = p.natDegree by
      exact_mod_cast Nat.sub_add_cancel hp]
    ring
  · intro k hk hk0
    have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hindex : p.natDegree < p.natDegree - 1 + (2 * k + 1) := by
      rw [show p.natDegree - 1 + (2 * k + 1) = p.natDegree + 2 * k by lia]
      lia
    have hcoeff : p.coeff (p.natDegree - 1 + (2 * k + 1)) = 0 :=
      coeff_eq_zero_of_natDegree_lt hindex
    change (C ((-1) ^ k * h ^ (2 * k)) * hasseDeriv (2 * k + 1) p).coeff
      (p.natDegree - 1) = 0
    rw [coeff_C_mul, hasseDeriv_coeff, hcoeff, mul_zero, mul_zero]
  · simp

/-- A nonconstant input loses exactly one degree under the imaginary central difference. -/
theorem natDegree_imaginaryCentralDifference {p : ℝ[X]}
    (hp : 1 ≤ p.natDegree) (h : ℝ) :
    (imaginaryCentralDifference h p).natDegree = p.natDegree - 1 := by
  apply le_antisymm (natDegree_imaginaryCentralDifference_le h p)
  apply le_natDegree_of_ne_zero
  rw [coeff_imaginaryCentralDifference_top hp h]
  exact mul_ne_zero (by positivity) (leadingCoeff_ne_zero.mpr (by
    intro hp0
    rw [hp0, natDegree_zero] at hp
    lia))

/-- The leading coefficient of a nonconstant input is multiplied by its degree. -/
theorem leadingCoeff_imaginaryCentralDifference {p : ℝ[X]}
    (hp : 1 ≤ p.natDegree) (h : ℝ) :
    (imaginaryCentralDifference h p).leadingCoeff =
      (p.natDegree : ℝ) * p.leadingCoeff := by
  rw [leadingCoeff, natDegree_imaginaryCentralDifference hp h,
    coeff_imaginaryCentralDifference_top hp h]

private lemma sum_even_odd_split {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N : ℕ) (hf : ∀ k, N < k → f k = 0) :
    ∑ k ∈ Finset.range (N + 1), f k =
      ∑ j ∈ Finset.range (N + 1), f (2 * j) +
        ∑ j ∈ Finset.range (N + 1), f (2 * j + 1) := by
  have hpair (m : ℕ) :
      ∑ k ∈ Finset.range (2 * m), f k =
        ∑ j ∈ Finset.range m, f (2 * j) + ∑ j ∈ Finset.range m, f (2 * j + 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ]
      abel
  rw [← hpair]
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    lia
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    exact hf k (by lia)

private lemma pow_I_mul_even (h : ℝ) (k : ℕ) :
    (Complex.I * (h : ℂ)) ^ (2 * k) = ((-1) ^ k * h ^ (2 * k) : ℝ) := by
  have hI : Complex.I ^ (2 * k) = (-1 : ℂ) ^ k := by
    rw [pow_mul, Complex.I_sq]
  rw [mul_pow, hI]
  norm_cast

private lemma pow_I_mul_odd (h : ℝ) (k : ℕ) :
    (Complex.I * (h : ℂ)) ^ (2 * k + 1) =
      Complex.I * (((-1) ^ k * h ^ (2 * k + 1) : ℝ) : ℂ) := by
  rw [pow_succ, pow_I_mul_even, pow_succ]
  push_cast
  ring

private lemma eval_add_eq_sum_hasseDeriv (p : ℂ[X]) (z w : ℂ) :
    p.eval (z + w) = ∑ k ∈ Finset.range (p.natDegree + 1),
      (hasseDeriv k p).eval z * w ^ k := by
  rw [add_comm z w, ← taylor_eval z p w, Polynomial.eval_eq_sum_range, natDegree_taylor]
  apply Finset.sum_congr rfl
  intro k _
  rw [taylor_coeff]

private lemma eval_complexify_imaginary_shift (h : ℝ) (p : ℝ[X]) (z : ℂ) :
    (complexify p).eval (z + Complex.I * h) =
      (complexify (imaginaryShiftRealPart h p)).eval z +
        Complex.I * h * (complexify (imaginaryCentralDifference h p)).eval z := by
  rw [eval_add_eq_sum_hasseDeriv]
  have hdegree : (complexify p).natDegree = p.natDegree := by
    exact Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective p
  rw [hdegree, sum_even_odd_split]
  · simp only [imaginaryShiftRealPart, imaginaryCentralDifference, complexify,
      Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, hasseDeriv_map,
      eval_finsetSum, eval_mul, eval_C, Complex.ofRealHom_eq_coe]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      rw [pow_I_mul_even]
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_I_mul_odd]
      push_cast
      ring
  · intro k hk
    rw [hasseDeriv_eq_zero_of_lt_natDegree _ _ (by simpa [hdegree] using hk), eval_zero,
      zero_mul]

/-- Complex evaluation of the imaginary central difference is the normalized difference of the
two imaginary shifts. -/
theorem eval_complexify_imaginaryCentralDifference {h : ℝ} (hh : h ≠ 0)
    (p : ℝ[X]) (z : ℂ) :
    (complexify (imaginaryCentralDifference h p)).eval z =
      ((complexify p).eval (z + Complex.I * h) -
        (complexify p).eval (z - Complex.I * h)) / (2 * Complex.I * h) := by
  have hplus := eval_complexify_imaginary_shift h p z
  have hminus := eval_complexify_imaginary_shift (-h) p z
  have heven : imaginaryShiftRealPart (-h) p = imaginaryShiftRealPart h p := by
    simp only [imaginaryShiftRealPart]
    apply Finset.sum_congr rfl
    intro k _
    rw [Even.neg_pow (even_two_mul k)]
  have hodd : imaginaryCentralDifference (-h) p = imaginaryCentralDifference h p := by
    simp only [imaginaryCentralDifference]
    apply Finset.sum_congr rfl
    intro k _
    rw [Even.neg_pow (even_two_mul k)]
  rw [heven, hodd] at hminus
  have hh_complex : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  rw [show z + Complex.I * (-h : ℝ) = z - Complex.I * h by push_cast; ring] at hminus
  rw [hplus, hminus]
  field_simp
  push_cast
  ring

private lemma natDegree_imaginaryShiftRealPart_le (h : ℝ) (p : ℝ[X]) :
    (imaginaryShiftRealPart h p).natDegree ≤ p.natDegree := by
  rw [imaginaryShiftRealPart]
  apply natDegree_sum_le_of_forall_le
  intro k _
  exact (natDegree_C_mul_le _ _).trans
    ((natDegree_hasseDeriv_le p (2 * k)).trans (Nat.sub_le _ _))

private lemma coeff_imaginaryShiftRealPart_top (p : ℝ[X]) (h : ℝ) :
    (imaginaryShiftRealPart h p).coeff p.natDegree = p.leadingCoeff := by
  rw [imaginaryShiftRealPart, finsetSum_coeff, Finset.sum_eq_single 0]
  · norm_num
  · intro k hk hk0
    have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hindex : p.natDegree < p.natDegree + 2 * k := by lia
    have hcoeff : p.coeff (p.natDegree + 2 * k) = 0 :=
      coeff_eq_zero_of_natDegree_lt hindex
    change (C ((-1) ^ k * h ^ (2 * k)) * hasseDeriv (2 * k) p).coeff
      p.natDegree = 0
    rw [coeff_C_mul, hasseDeriv_coeff, hcoeff, mul_zero, mul_zero]
  · simp

private lemma natDegree_imaginaryShiftRealPart {p : ℝ[X]} (hp : p ≠ 0) (h : ℝ) :
    (imaginaryShiftRealPart h p).natDegree = p.natDegree := by
  apply le_antisymm (natDegree_imaginaryShiftRealPart_le h p)
  apply le_natDegree_of_ne_zero
  rw [coeff_imaginaryShiftRealPart_top p h]
  exact leadingCoeff_ne_zero.mpr hp

private lemma leadingCoeff_imaginaryShiftRealPart {p : ℝ[X]} (hp : p ≠ 0) (h : ℝ) :
    (imaginaryShiftRealPart h p).leadingCoeff = p.leadingCoeff := by
  rw [leadingCoeff, natDegree_imaginaryShiftRealPart hp h,
    coeff_imaginaryShiftRealPart_top p h]

private theorem imaginaryCentralDifference_splits_simple_of_posLeadingCoeff
    {h : ℝ} (hh : 0 < h) {p : ℝ[X]} (hp0 : p ≠ 0) (hps : p.Splits)
    (hpdeg : 1 ≤ p.natDegree) (hppos : HasPosLeadingCoeff p) :
    (imaginaryCentralDifference h p).Splits ∧
      HasSimpleRoots (imaginaryCentralDifference h p) := by
  let E := imaginaryShiftRealPart h p
  let D := imaginaryCentralDifference h p
  let G := C h * D
  have hEpos : HasPosLeadingCoeff E := by
    change 0 < (imaginaryShiftRealPart h p).leadingCoeff
    rw [leadingCoeff_imaginaryShiftRealPart hp0 h]
    exact hppos
  have hD0 : D ≠ 0 := by
    change imaginaryCentralDifference h p ≠ 0
    apply leadingCoeff_ne_zero.mp
    rw [leadingCoeff_imaginaryCentralDifference hpdeg h]
    exact mul_ne_zero (by positivity) (leadingCoeff_ne_zero.mpr hp0)
  have hGpos : HasPosLeadingCoeff G := by
    change 0 < (C h * imaginaryCentralDifference h p).leadingCoeff
    rw [leadingCoeff_mul, leadingCoeff_C,
      leadingCoeff_imaginaryCentralDifference hpdeg h]
    exact mul_pos hh (mul_pos (by positivity) hppos)
  have hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial E G) := by
    intro z hz
    have hshift := eval_complexify_imaginary_shift h p z
    have hrewrite : (hermiteBiehlerPolynomial E G).eval z =
        (complexify p).eval (z + Complex.I * h) := by
      rw [eval_hermiteBiehlerPolynomial]
      change (complexify (imaginaryShiftRealPart h p)).eval z +
        Complex.I * (complexify (C h * imaginaryCentralDifference h p)).eval z = _
      rw [show complexify (C h * imaginaryCentralDifference h p) =
        C (h : ℂ) * complexify (imaginaryCentralDifference h p) by
          simp [complexify]]
      simp only [eval_mul, eval_C]
      simpa only [mul_assoc] using hshift.symm
    rw [hrewrite]
    apply eval_complexify_ne_zero_of_splits_of_im_pos hps hp0
    simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im]
    linarith
  have hno : ∀ r : ℝ, ¬ (G.IsRoot r ∧ E.IsRoot r) := by
    intro r hr
    have hshift := eval_complexify_imaginary_shift h p (r : ℂ)
    have hrG : G.eval r = 0 := hr.1
    have hrE : (imaginaryShiftRealPart h p).eval r = 0 := by
      exact hr.2
    have hrD : (imaginaryCentralDifference h p).eval r = 0 := by
      change (C h * imaginaryCentralDifference h p).eval r = 0 at hrG
      simpa [eval_mul, eval_C, hh.ne'] using hrG
    have hzero : (complexify p).eval ((r : ℂ) + Complex.I * h) = 0 := by
      rw [hshift]
      rw [eval_complexify_ofReal, hrE, eval_complexify_ofReal, hrD]
      simp
    exact (eval_complexify_ne_zero_of_splits_of_im_pos hps hp0 (by
      simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im]
      linarith)) hzero
  have hEdeg : 1 ≤ E.natDegree := by
    change 1 ≤ (imaginaryShiftRealPart h p).natDegree
    rw [natDegree_imaginaryShiftRealPart hp0 h]
    exact hpdeg
  have hinterl : StrictInterl G E :=
    strictInterl_of_stable_general hEpos hGpos hstab hEdeg
  have hsimpleG : HasSimpleRoots G :=
    (hinterl.hasSimpleRoots_of_no_common_root hno).1
  have hscale : C h⁻¹ * G = D := by
    change C h⁻¹ * (C h * imaginaryCentralDifference h p) =
      imaginaryCentralDifference h p
    rw [← mul_assoc, ← C_mul]
    simp [hh.ne']
  constructor
  · change D.Splits
    rw [← hscale]
    exact hinterl.1.2.C_mul h⁻¹
  · change HasSimpleRoots D
    rw [← hscale]
    exact hsimpleG.C_mul (inv_ne_zero hh.ne')

/-- A positive imaginary central difference of a nonzero split polynomial has only simple real
roots. -/
theorem imaginaryCentralDifference_splits_and_hasSimpleRoots
    {h : ℝ} (hh : 0 < h) {p : ℝ[X]} (hp0 : p ≠ 0) (hps : p.Splits)
    (hpdeg : 1 ≤ p.natDegree) :
    (imaginaryCentralDifference h p).Splits ∧
      HasSimpleRoots (imaginaryCentralDifference h p) := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  let q := C p.leadingCoeff⁻¹ * p
  have hq0 : q ≠ 0 := mul_ne_zero (C_ne_zero.mpr (inv_ne_zero hlc)) hp0
  have hqs : q.Splits := hps.C_mul p.leadingCoeff⁻¹
  have hqdeg : 1 ≤ q.natDegree := by
    change 1 ≤ (C p.leadingCoeff⁻¹ * p).natDegree
    rw [natDegree_C_mul (inv_ne_zero hlc)]
    exact hpdeg
  have hqpos : HasPosLeadingCoeff q := by
    apply hasPosLeadingCoeff_of_monic
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ hlc
  obtain ⟨hDs, hDsimple⟩ :=
    imaginaryCentralDifference_splits_simple_of_posLeadingCoeff hh hq0 hqs hqdeg hqpos
  have hDq : imaginaryCentralDifference h q =
      C p.leadingCoeff⁻¹ * imaginaryCentralDifference h p := by
    exact imaginaryCentralDifference_C_mul (inv_ne_zero hlc) p
  have hscale : C p.leadingCoeff * imaginaryCentralDifference h q =
      imaginaryCentralDifference h p := by
    rw [hDq, ← mul_assoc, ← C_mul]
    simp [hlc]
  constructor
  · rw [← hscale]
    exact hDs.C_mul p.leadingCoeff
  · rw [← hscale]
    exact hDsimple.C_mul hlc

/-- Complete degree, leading-coefficient, splitting, and simplicity package for the positive
imaginary central difference of a nonzero real-rooted polynomial. -/
theorem imaginaryCentralDifference_spec {h : ℝ} (hh : 0 < h)
    {p : ℝ[X]} (hp0 : p ≠ 0) (hps : p.Splits) (hpdeg : 1 ≤ p.natDegree) :
    (imaginaryCentralDifference h p).natDegree = p.natDegree - 1 ∧
      (imaginaryCentralDifference h p).leadingCoeff =
        (p.natDegree : ℝ) * p.leadingCoeff ∧
      (imaginaryCentralDifference h p).Splits ∧
      HasSimpleRoots (imaginaryCentralDifference h p) := by
  exact ⟨natDegree_imaginaryCentralDifference hpdeg h,
    leadingCoeff_imaginaryCentralDifference hpdeg h,
    imaginaryCentralDifference_splits_and_hasSimpleRoots hh hp0 hps hpdeg⟩

end RealRooted
