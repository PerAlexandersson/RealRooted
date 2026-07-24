import RealRooted.ASWCubicEqualModulus
import RealRooted.ASWCubicNonrealFactor

/-!
# The cubic Aissen--Schoenberg--Whitney theorem

This file proves the forward Aissen--Schoenberg--Whitney splitting theorem in
exact degree three.  A negative coefficient discriminant would give one real
and two nonreal conjugate roots of the shift-one minor recurrence.  Total
nonnegativity supplies three nonnegative families of Toeplitz minors, while
the cubic recurrence argument rules out precisely that root configuration.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A degree-three Pólya-frequency polynomial with positive constant
coefficient has nonnegative cubic discriminant. -/
theorem cubicDiscr_nonneg_of_isPolyaFreqSeq_natDegree_three
    {p : ℝ[X]} (hdeg : p.natDegree = 3) (hconst : 0 < p.coeff 0)
    (hpf : IsPolyaFreqSeq p.coeff) :
    0 ≤ cubicDiscr p := by
  by_contra hnonneg
  have hdisc : cubicDiscr p < 0 := lt_of_not_ge hnonneg
  have hdisc' : cubicDiscr
      (C (p.coeff 3) * X ^ 3 + C (p.coeff 2) * X ^ 2 +
        C (p.coeff 1) * X + C (p.coeff 0)) < 0 := by
    rw [cubicDiscr_of_coeffs]
    simpa [cubicDiscr] using hdisc
  have hconst_ne : p.coeff 0 ≠ 0 := hconst.ne'
  obtain ⟨r, z, hz, _hfactor, hsum, hpairs, hprod⟩ :=
    aswCubicShiftOneCharPoly_complex_factor_of_cubicDiscr_neg
      (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) hconst_ne hdisc'
  have hp_ne : p ≠ 0 := by
    intro hp
    rw [hp, coeff_zero] at hconst_ne
    exact hconst_ne rfl
  have hlead_ne : p.coeff 3 ≠ 0 := by
    rw [← hdeg, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp_ne
  have hlead_pos : 0 < p.coeff 3 :=
    (hpf.nonneg 3).lt_of_ne (Ne.symm hlead_ne)
  have hz_ne : z ≠ 0 := by
    intro hz0
    rw [hz0] at hz
    exact hz (by simp)
  have hprodReal : r * Complex.normSq z = p.coeff 0 ^ 2 * p.coeff 3 := by
    rw [mul_assoc, Complex.mul_conj] at hprod
    exact_mod_cast hprod
  have hr : 0 < r := by
    have hnormSq : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz_ne
    have hright : 0 < p.coeff 0 ^ 2 * p.coeff 3 :=
      mul_pos (sq_pos_of_pos hconst) hlead_pos
    nlinarith
  have hsupport : ∀ j, 4 ≤ j → p.coeff j = 0 := by
    intro j hj
    apply coeff_eq_zero_of_natDegree_lt
    rw [hdeg]
    lia
  exact false_of_nonreal_aswCubicCharacteristicRoots
    p.coeff hsupport r hr hz hsum hpairs hprod hconst
    (fun n ↦ hpf.aswShiftedToeplitzMinor_nonneg 1 n)
    (fun n ↦ hpf.aswShiftedToeplitzMinor_nonneg 2 n)
    (fun n ↦ hpf.aswGapToeplitzMinor_nonneg n)

/-- Exact-degree-three case of the forward
Aissen--Schoenberg--Whitney splitting theorem. -/
theorem splits_of_isPolyaFreqSeq_coeff_of_natDegree_three
    {p : ℝ[X]} (hdeg : p.natDegree = 3) (hconst : 0 < p.coeff 0)
    (hpf : IsPolyaFreqSeq p.coeff) :
    p.Splits :=
  splits_of_natDegree_le_three_cubicDiscr_nonneg hdeg.le
    (cubicDiscr_nonneg_of_isPolyaFreqSeq_natDegree_three hdeg hconst hpf)

end RealRooted
