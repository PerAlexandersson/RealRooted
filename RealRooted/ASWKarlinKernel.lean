import RealRooted.ASWKarlinMatrix
import RealRooted.ASWKarlinThreshold
import RealRooted.ASWKarlinVariation
import RealRooted.ASWKarlinVectors
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Complex-root kernel vectors for Karlin's matrix

For a complex root `z` of a real polynomial, the vector with entries
`im (z ^ j)` lies in the kernel of every repeated Karlin coefficient-window
matrix.  This is the algebraic input to the finite-order sector argument.
-/

open Polynomial Matrix BigOperators

noncomputable section

namespace RealRooted

/-- Reindex a finite sum supported on a shifted coefficient window. -/
lemma sum_fin_shifted_window {R : Type*} [Semiring R]
    (u : ℕ → R) (f : ℕ → R) (N s d : ℕ)
    (hsd : s + d ≤ N) (hu : ∀ k, d < k → u k = 0) :
    (∑ j : Fin (N + 1),
        if s ≤ (j : ℕ) then u ((j : ℕ) - s) * f (j : ℕ) else 0) =
      ∑ k ∈ Finset.range (d + 1), u k * f (s + k) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j => if s ≤ j then u (j - s) * f j else 0) (N + 1)]
  have hcut : s + (d + 1) ≤ N + 1 := by
    lia
  have hN : N + 1 = s + (d + 1) + (N + 1 - (s + (d + 1))) := by
    lia
  conv_lhs => rw [hN, Finset.sum_range_add]
  have hbefore :
      (∑ x ∈ Finset.range s, if s ≤ x then u (x - s) * f x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [if_neg]
    exact Nat.not_le_of_lt (Finset.mem_range.mp hx)
  have hfirst :
      (∑ x ∈ Finset.range (s + (d + 1)),
        if s ≤ x then u (x - s) * f x else 0) =
        ∑ k ∈ Finset.range (d + 1), u k * f (s + k) := by
    rw [Finset.sum_range_add, hbefore, zero_add]
    simp
  have htail :
      (∑ k ∈ Finset.range (N + 1 - (s + (d + 1))),
        if s ≤ s + (d + 1) + k then
          u (s + (d + 1) + k - s) * f (s + (d + 1) + k) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : d < s + (d + 1) + k - s := by
      lia
    simp [hu _ hk']
  rw [hfirst, htail, add_zero]

lemma sum_coeff_mul_im_pow_add_eq_zero {p : ℝ[X]} {z : ℂ}
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots) (s : ℕ) :
    ∑ k ∈ Finset.range (p.natDegree + 1),
      p.coeff k * (z ^ (s + k)).im = 0 := by
  have hroot :
      ∑ k ∈ Finset.range (p.natDegree + 1),
        (p.coeff k : ℂ) * z ^ k = 0 := by
    have hzroot : (p.map (algebraMap ℝ ℂ)).IsRoot z :=
      isRoot_of_mem_roots hz
    rw [Polynomial.IsRoot.def, Polynomial.eval_eq_sum_range] at hzroot
    simpa [Polynomial.natDegree_map_eq_of_injective
      (algebraMap ℝ ℂ).injective, mul_comm] using hzroot
  have hshift :
      ∑ k ∈ Finset.range (p.natDegree + 1),
          (p.coeff k : ℂ) * z ^ (s + k) = 0 := by
    calc
      _ = z ^ s * ∑ k ∈ Finset.range (p.natDegree + 1),
          (p.coeff k : ℂ) * z ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [pow_add]
        ring
      _ = 0 := by rw [hroot, mul_zero]
  have him := congrArg Complex.im hshift
  simpa using him

lemma sum_coeff_mul_phase_im_pow_add_eq_zero {p : ℝ[X]} {z : ℂ}
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots) (phase : ℝ) (s : ℕ) :
    ∑ k ∈ Finset.range (p.natDegree + 1),
      p.coeff k * (Complex.exp (phase * Complex.I) * z ^ (s + k)).im = 0 := by
  have hroot :
      ∑ k ∈ Finset.range (p.natDegree + 1),
        (p.coeff k : ℂ) * z ^ k = 0 := by
    have hzroot : (p.map (algebraMap ℝ ℂ)).IsRoot z :=
      isRoot_of_mem_roots hz
    rw [Polynomial.IsRoot.def, Polynomial.eval_eq_sum_range] at hzroot
    simpa [Polynomial.natDegree_map_eq_of_injective
      (algebraMap ℝ ℂ).injective, mul_comm] using hzroot
  have hshift :
      ∑ k ∈ Finset.range (p.natDegree + 1),
          (p.coeff k : ℂ) * z ^ (s + k) = 0 := by
    calc
      _ = z ^ s * ∑ k ∈ Finset.range (p.natDegree + 1),
          (p.coeff k : ℂ) * z ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [pow_add]
        ring
      _ = 0 := by rw [hroot, mul_zero]
  have hphase :
      ∑ k ∈ Finset.range (p.natDegree + 1),
          (p.coeff k : ℂ) *
            (Complex.exp (phase * Complex.I) * z ^ (s + k)) = 0 := by
    calc
      _ = Complex.exp (phase * Complex.I) *
            ∑ k ∈ Finset.range (p.natDegree + 1),
              (p.coeff k : ℂ) * z ^ (s + k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = 0 := by rw [hshift, mul_zero]
  have him := congrArg Complex.im hphase
  simpa [Complex.mul_im] using him

/-- Every complex root supplies a kernel vector for every repeated Karlin
coefficient-window matrix. -/
theorem aswKarlinMatrix_mulVec_rootVector {p : ℝ[X]} {z : ℂ}
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots)
    (order blocks : ℕ) (hdegree : 0 < p.natDegree) (horder : 0 < order) :
    aswKarlinMatrix p.coeff p.natDegree order blocks *ᵥ
      aswKarlinRootVector z p.natDegree order blocks = 0 := by
  funext i
  rw [Matrix.mulVec, dotProduct]
  simp only [aswKarlinMatrix_apply, aswKarlinRootVector, Pi.zero_apply,
    ite_mul, zero_mul]
  rw [sum_fin_shifted_window p.coeff (fun j => (z ^ j).im)
    (blocks * (p.natDegree + order - 1))
    (aswKarlinRowPos p.natDegree order i) p.natDegree
    (aswKarlinRowPos_add_degree_le p.natDegree order blocks hdegree horder i)
    (fun k hk => Polynomial.coeff_eq_zero_of_natDegree_lt hk)]
  exact sum_coeff_mul_im_pow_add_eq_zero hz _

/-- Every complex root supplies a phase-rotated kernel vector for every
repeated Karlin coefficient-window matrix. -/
theorem aswKarlinMatrix_mulVec_phasedRootVector {p : ℝ[X]} {z : ℂ}
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots)
    (phase : ℝ) (order blocks : ℕ)
    (hdegree : 0 < p.natDegree) (horder : 0 < order) :
    aswKarlinMatrix p.coeff p.natDegree order blocks *ᵥ
      aswKarlinPhasedRootVector z phase p.natDegree order blocks = 0 := by
  funext i
  rw [Matrix.mulVec, dotProduct]
  simp only [aswKarlinMatrix_apply, aswKarlinPhasedRootVector, Pi.zero_apply,
    ite_mul, zero_mul]
  rw [sum_fin_shifted_window p.coeff
    (fun j => (Complex.exp (phase * Complex.I) * z ^ j).im)
    (blocks * (p.natDegree + order - 1))
    (aswKarlinRowPos p.natDegree order i) p.natDegree
    (aswKarlinRowPos_add_degree_le p.natDegree order blocks hdegree horder i)
    (fun k hk => Polynomial.coeff_eq_zero_of_natDegree_lt hk)]
  exact sum_coeff_mul_phase_im_pow_add_eq_zero hz phase _

/-- A complex root of a real polynomial with positive constant coefficient is
nonzero. -/
lemma complex_root_ne_zero_of_coeff_zero_pos {p : ℝ[X]} {z : ℂ}
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots) (hconst : 0 < p.coeff 0) :
    z ≠ 0 := by
  intro hz0
  have hzroot : (p.map (algebraMap ℝ ℂ)).IsRoot z :=
    isRoot_of_mem_roots hz
  rw [Polynomial.IsRoot.def] at hzroot
  rw [hz0, Polynomial.eval_map_algebraMap] at hzroot
  have hroot_map : (Polynomial.aeval (algebraMap ℝ ℂ (0 : ℝ)) p) = 0 := by
    simpa using hzroot
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at hroot_map
  have heval : p.eval 0 = 0 := Complex.ofReal_eq_zero.mp hroot_map
  have hcoeff : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact heval
  linarith

/-- Choose a phase for a complex root so the phase-rotated root vector is both
in Karlin's repeated matrix kernel and coordinatewise nonzero. -/
theorem exists_phase_phasedRootVector_kernel_zeroFree
    {p : ℝ[X]} {z : ℂ}
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots)
    (order blocks : ℕ) (hdegree : 0 < p.natDegree)
    (horder : 0 < order) (hconst : 0 < p.coeff 0) :
    ∃ phase : ℝ,
      AswKarlinPhaseAvoidsZeros phase z.arg p.natDegree order blocks ∧
        aswKarlinMatrix p.coeff p.natDegree order blocks *ᵥ
          aswKarlinPhasedRootVector z phase p.natDegree order blocks = 0 ∧
        ∀ j : Fin (blocks * (p.natDegree + order - 1) + 1),
          aswKarlinPhasedRootVector z phase p.natDegree order blocks j ≠ 0 := by
  obtain ⟨phase, hphase⟩ :=
    exists_phase_avoidsZeros_aswKarlinPhasedSineVector
      z.arg p.natDegree order blocks
  refine ⟨phase, hphase, ?_, ?_⟩
  · exact aswKarlinMatrix_mulVec_phasedRootVector hz phase order blocks
      hdegree horder
  · exact aswKarlinPhasedRootVector_zeroFree_of_phaseAvoids
      (complex_root_ne_zero_of_coeff_zero_pos hz hconst) hphase

/-- The zero-free repeated-matrix classical input gives the sign-variation
lower bound for a phased complex-root vector. -/
theorem aswKarlinRepeated_phasedRootVector_signVariation_lower
    (hclassical :
      AswKarlinRepeatedZeroFreeKernelSignVariationClassicalInputStatement)
    {p : ℝ[X]} {z : ℂ} {phase : ℝ} {order blocks : ℕ}
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots)
    (hphase : AswKarlinPhaseAvoidsZeros phase z.arg p.natDegree order blocks)
    (hdegree : 0 < p.natDegree) (horder : 0 < order)
    (hblocks : 0 < blocks) (hconst : 0 < p.coeff 0)
    (hlead : 0 < p.coeff p.natDegree) (hpf : IsPolyaFreqSeq p.coeff) :
    blocks * order ≤
      Fin.signVariations
        (aswKarlinPhasedRootVector z phase p.natDegree order blocks) := by
  have hsupport : ∀ k, p.natDegree < k → p.coeff k = 0 :=
    fun k hk => Polynomial.coeff_eq_zero_of_natDegree_lt hk
  exact hclassical hdegree horder hblocks hconst hlead hsupport hpf
    (aswKarlinMatrix_mulVec_phasedRootVector hz phase order blocks
      hdegree horder)
    (aswKarlinPhasedRootVector_zeroFree_of_phaseAvoids
      (complex_root_ne_zero_of_coeff_zero_pos hz hconst) hphase)

/-- The zero-free repeated-matrix classical input gives the same lower bound
for the corresponding phased sampled-sine vector. -/
theorem aswKarlinRepeated_phasedSine_signVariation_lower
    (hclassical :
      AswKarlinRepeatedZeroFreeKernelSignVariationClassicalInputStatement)
    {p : ℝ[X]} {z : ℂ} {phase : ℝ} {order blocks : ℕ}
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots)
    (hphase : AswKarlinPhaseAvoidsZeros phase z.arg p.natDegree order blocks)
    (hdegree : 0 < p.natDegree) (horder : 0 < order)
    (hblocks : 0 < blocks) (hconst : 0 < p.coeff 0)
    (hlead : 0 < p.coeff p.natDegree) (hpf : IsPolyaFreqSeq p.coeff) :
    blocks * order ≤
      Fin.signVariations
        (aswKarlinPhasedSineVector phase z.arg p.natDegree order blocks) := by
  rw [← signVariations_aswKarlinPhasedRootVector_eq_phasedSine
    (complex_root_ne_zero_of_coeff_zero_pos hz hconst)]
  exact aswKarlinRepeated_phasedRootVector_signVariation_lower hclassical hz
    hphase hdegree horder hblocks hconst hlead hpf

/-- Evaluation of a real-coefficient polynomial at a conjugate complex point. -/
lemma eval_map_algebraMap_conj (p : ℝ[X]) (z : ℂ) :
    (p.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) =
      starRingEnd ℂ ((p.map (algebraMap ℝ ℂ)).eval z) := by
  have hcomp : (starRingEnd ℂ).comp (algebraMap ℝ ℂ) = algebraMap ℝ ℂ := by
    ext x
    simp
  simp [Polynomial.eval_map, Polynomial.hom_eval₂, hcomp]

/-- A complex root of a real-coefficient polynomial has conjugate root. -/
lemma complex_root_conj_of_real_coeff {p : ℝ[X]} {z : ℂ} (hp : p ≠ 0)
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots) :
    starRingEnd ℂ z ∈ (p.map (algebraMap ℝ ℂ)).roots := by
  have hpmap : p.map (algebraMap ℝ ℂ) ≠ 0 :=
    Polynomial.map_ne_zero hp
  have hzroot : (p.map (algebraMap ℝ ℂ)).IsRoot z :=
    isRoot_of_mem_roots hz
  have hconjroot :
      (p.map (algebraMap ℝ ℂ)).IsRoot (starRingEnd ℂ z) := by
    rw [Polynomial.IsRoot.def, eval_map_algebraMap_conj p z]
    rw [Polynomial.IsRoot.def] at hzroot
    simp [hzroot]
  exact (Polynomial.mem_roots hpmap).mpr hconjroot

/-- Repeated zero-free classical input gives Karlin's sector bound for roots
whose argument is nonnegative. -/
theorem aswKarlinSectorThreshold_le_arg_of_repeatedZeroFreeClassicalInput
    (hclassical :
      AswKarlinRepeatedZeroFreeKernelSignVariationClassicalInputStatement)
    {p : ℝ[X]} {z : ℂ} (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots)
    (hdegree : 0 < p.natDegree) (hconst : 0 < p.coeff 0)
    (hpf : IsPolyaFreqSeq p.coeff) {order blocks : ℕ}
    (horder : 0 < order) (hblocks : 0 < blocks) (harg0 : 0 ≤ z.arg) :
    aswSectorThreshold p.natDegree order ≤ z.arg := by
  have hp_ne : p ≠ 0 := by
    intro hp
    simp [hp] at hdegree
  have hlead_ne : p.coeff p.natDegree ≠ 0 := by
    change p.leadingCoeff ≠ 0
    exact Polynomial.leadingCoeff_ne_zero.mpr hp_ne
  have hlead : 0 < p.coeff p.natDegree :=
    (hpf.nonneg p.natDegree).lt_of_ne (Ne.symm hlead_ne)
  apply aswSectorThreshold_le_of_repeated_phasedSine_bounds_of_nonneg
    hdegree horder hblocks harg0
  intro phase hphase
  exact aswKarlinRepeated_phasedSine_signVariation_lower hclassical hz hphase
    hdegree horder hblocks hconst hlead hpf

/-- Repeated zero-free classical input gives Karlin's absolute sector bound
for complex roots. -/
theorem aswKarlinSectorThreshold_le_abs_arg_of_repeatedZeroFreeClassicalInput
    (hclassical :
      AswKarlinRepeatedZeroFreeKernelSignVariationClassicalInputStatement)
    {p : ℝ[X]} {z : ℂ} (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots)
    (hdegree : 0 < p.natDegree) (hconst : 0 < p.coeff 0)
    (hpf : IsPolyaFreqSeq p.coeff) {order blocks : ℕ}
    (horder : 0 < order) (hblocks : 0 < blocks) :
    aswSectorThreshold p.natDegree order ≤ |z.arg| := by
  have hp_ne : p ≠ 0 := by
    intro hp
    simp [hp] at hdegree
  by_cases harg0 : 0 ≤ z.arg
  · have hbound :=
      aswKarlinSectorThreshold_le_arg_of_repeatedZeroFreeClassicalInput
        hclassical hz hdegree hconst hpf horder hblocks harg0
    simpa [abs_of_nonneg harg0] using hbound
  · have harg_neg : z.arg < 0 := lt_of_not_ge harg0
    have hconj_root :
        starRingEnd ℂ z ∈ (p.map (algebraMap ℝ ℂ)).roots :=
      complex_root_conj_of_real_coeff hp_ne hz
    have harg_pi : z.arg ≠ Real.pi := by
      linarith [Real.pi_pos]
    have hconj_arg : (starRingEnd ℂ z).arg = -z.arg := by
      simpa [harg_pi] using Complex.arg_conj z
    have hconj_arg_nonneg : 0 ≤ (starRingEnd ℂ z).arg := by
      rw [hconj_arg]
      linarith
    have hbound :=
      aswKarlinSectorThreshold_le_arg_of_repeatedZeroFreeClassicalInput
        hclassical hconj_root hdegree hconst hpf horder hblocks
        hconj_arg_nonneg
    rw [hconj_arg] at hbound
    simpa [abs_of_neg harg_neg] using hbound

/-- A real complex root of a positive-constant PF polynomial lies on the
negative real ray. -/
lemma arg_eq_pi_of_real_complex_root_of_isPolyaFreqSeq_coeff {p : ℝ[X]} {z : ℂ}
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots)
    (hconst : 0 < p.coeff 0) (hpf : IsPolyaFreqSeq p.coeff)
    (him : z.im = 0) :
    z.arg = Real.pi := by
  have hpnn : HasNonnegCoeffs p := fun k => hpf.nonneg k
  have hzroot : (p.map (algebraMap ℝ ℂ)).IsRoot z :=
    isRoot_of_mem_roots hz
  have hz_ne : z ≠ 0 := complex_root_ne_zero_of_coeff_zero_pos hz hconst
  have hp0 : p ≠ 0 := by
    intro hp
    have : p.coeff 0 = 0 := by simp [hp]
    linarith
  have hz_eq : z = (z.re : ℂ) :=
    Complex.ext (by simp) (by simpa using him)
  have hzroot_real : p.IsRoot z.re := by
    rw [Polynomial.IsRoot.def] at hzroot ⊢
    rw [hz_eq, Polynomial.eval_map_algebraMap] at hzroot
    have hroot_map :
        (Polynomial.aeval (algebraMap ℝ ℂ z.re) p) = 0 := by
      simpa using hzroot
    rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at hroot_map
    exact Complex.ofReal_eq_zero.mp hroot_map
  have hzmem : z.re ∈ p.roots := (Polynomial.mem_roots hp0).mpr hzroot_real
  have hnonpos : z.re ≤ 0 := roots_nonpos_of_hasNonnegCoeffs hpnn z.re hzmem
  have hzre_ne : z.re ≠ 0 := by
    intro hzre
    exact hz_ne (Complex.ext hzre him)
  have hzre_neg : z.re < 0 := lt_of_le_of_ne hnonpos hzre_ne
  exact Complex.arg_eq_pi_iff.mpr ⟨hzre_neg, him⟩

/-- Conditional Karlin finite-order sector estimate for a nonreal complex root,
with the classical sign-variation input supplied explicitly. -/
theorem aswKarlinSectorThreshold_le_abs_arg_of_im_ne_zero_of_classicalInput
    (hclassical : AswKarlinKernelSignVariationClassicalInputStatement)
    {p : ℝ[X]} {z : ℂ} (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots)
    (hdegree : 0 < p.natDegree) (hconst : 0 < p.coeff 0)
    (hpf : IsPolyaFreqSeq p.coeff) {order : ℕ} (horder : 0 < order)
    (him : z.im ≠ 0) :
    aswSectorThreshold p.natDegree order ≤ |z.arg| := by
  have hkernelLower :
      AswKarlinKernelSignVariationLowerBound p.natDegree order p.coeff :=
    have hp_ne : p ≠ 0 := by
      intro hp
      simp [hp] at hdegree
    have hlead_ne : p.coeff p.natDegree ≠ 0 := by
      change p.leadingCoeff ≠ 0
      exact Polynomial.leadingCoeff_ne_zero.mpr hp_ne
    have hlead : 0 < p.coeff p.natDegree :=
      (hpf.nonneg p.natDegree).lt_of_ne (Ne.symm hlead_ne)
    have hsupport : ∀ k, p.natDegree < k → p.coeff k = 0 :=
      fun k hk => Polynomial.coeff_eq_zero_of_natDegree_lt hk
    hpf.aswKarlinKernelSignVariationLowerBound_of_classicalInput
      hclassical p.natDegree order hdegree horder hconst hlead hsupport
  have hker :
      aswKarlinMatrix p.coeff p.natDegree order 1 *ᵥ
        aswKarlinRootVector z p.natDegree order 1 = 0 :=
    aswKarlinMatrix_mulVec_rootVector hz order 1 hdegree horder
  have hvec_ne :
      aswKarlinRootVector z p.natDegree order 1 ≠ 0 :=
    aswKarlinRootVector_ne_zero_of_im_ne_zero hdegree horder him
  have hsign :
      Fin.signVariations (aswKarlinRootVector z p.natDegree order 1) =
        Fin.signVariations (aswKarlinSineVector z.arg p.natDegree order 1) :=
    signVariations_aswKarlinRootVector_eq_sine
      (complex_root_ne_zero_of_coeff_zero_pos hz hconst) p.natDegree order 1
  exact aswSectorThreshold_le_abs_arg_of_karlin_matrix_kernel_of_threshold
    hdegree horder hkernelLower hker hvec_ne hsign

/-- Karlin's finite-order sector estimate for a nonreal complex root of a
positive constant-coefficient PF polynomial.

The checked algebraic inputs above provide the repeated totally nonnegative
coefficient-window matrix, its full row rank from the positive constant
coefficient, and the root-supplied kernel vector.  The remaining hard ingredient
is the classical variation-diminishing/sign-regular kernel theorem. -/
theorem aswKarlinSectorThreshold_le_abs_arg_of_im_ne_zero {p : ℝ[X]} {z : ℂ}
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots)
    (hdegree : 0 < p.natDegree) (hconst : 0 < p.coeff 0)
    (hpf : IsPolyaFreqSeq p.coeff) {order : ℕ} (horder : 0 < order)
    (_him : z.im ≠ 0) :
    aswSectorThreshold p.natDegree order ≤ |z.arg| :=
  aswKarlinSectorThreshold_le_abs_arg_of_repeatedZeroFreeClassicalInput
    aswKarlinRepeatedZeroFreeKernelSignVariationClassicalInput hz hdegree
    hconst hpf horder (by norm_num : 0 < 1)

/-- Conditional Karlin finite-order sector estimate for one complex root, with
the classical sign-variation input supplied explicitly. -/
theorem aswKarlinSectorThreshold_le_abs_arg_of_classicalInput
    (hclassical : AswKarlinKernelSignVariationClassicalInputStatement)
    {p : ℝ[X]} {z : ℂ} (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots)
    (hdegree : 0 < p.natDegree) (hconst : 0 < p.coeff 0)
    (hpf : IsPolyaFreqSeq p.coeff) {order : ℕ} (horder : 0 < order) :
    aswSectorThreshold p.natDegree order ≤ |z.arg| := by
  by_cases him : z.im = 0
  · rw [arg_eq_pi_of_real_complex_root_of_isPolyaFreqSeq_coeff hz hconst hpf him,
      abs_of_pos Real.pi_pos]
    exact aswSectorThreshold_le_pi p.natDegree order hdegree horder
  · exact aswKarlinSectorThreshold_le_abs_arg_of_im_ne_zero_of_classicalInput
      hclassical hz hdegree hconst hpf horder him

/-- Karlin's finite-order sector estimate for one complex root of a positive
constant-coefficient PF polynomial.  The real-root branch follows from
coefficient nonnegativity; the nonreal branch is the remaining
variation-diminishing leaf. -/
theorem aswKarlinSectorThreshold_le_abs_arg {p : ℝ[X]} {z : ℂ}
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots)
    (hdegree : 0 < p.natDegree) (hconst : 0 < p.coeff 0)
    (hpf : IsPolyaFreqSeq p.coeff) {order : ℕ} (horder : 0 < order) :
    aswSectorThreshold p.natDegree order ≤ |z.arg| :=
  aswKarlinSectorThreshold_le_abs_arg_of_repeatedZeroFreeClassicalInput
    aswKarlinRepeatedZeroFreeKernelSignVariationClassicalInput hz hdegree
    hconst hpf horder (by norm_num : 0 < 1)

end RealRooted
