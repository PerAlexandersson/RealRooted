import RealRooted.ASWKarlinMatrix
import RealRooted.ASWKarlinThreshold
import RealRooted.ASWKarlinVariation
import RealRooted.ASWKarlinVectors
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularRankDeficient
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

/-- Karlin's repeated matrices force a linear lower bound on the sampled sine
vector's sign variations, up to the fixed two-endpoint perturbation loss. -/
theorem aswKarlinRepeatedSineVariationLowerBound
    {p : ℝ[X]} {z : ℂ} (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots)
    (hdegree : 0 < p.natDegree) (hconst : 0 < p.coeff 0)
    (hpf : IsPolyaFreqSeq p.coeff) {order blocks : ℕ}
    (horder : 0 < order) (hblocks : 0 < blocks) (him : z.im ≠ 0) :
    blocks * order - 1 ≤
      Fin.signVariations
        (aswKarlinSineVector z.arg p.natDegree order blocks) + 2 := by
  have hwidth : 0 < blocks * (p.natDegree + order - 1) :=
    Nat.mul_pos hblocks (by lia)
  have hcols :
      blocks * (p.natDegree + order - 1) + 1 =
        (blocks * (p.natDegree + order - 1) - 1) + 2 := by
    lia
  have hnodal :
      ∀ i : Fin (blocks * (p.natDegree + order - 1) - 1),
        aswKarlinRootVector z p.natDegree order blocks
            (Fin.cast hcols.symm i.succ.castSucc) = 0 →
          aswKarlinRootVector z p.natDegree order blocks
              (Fin.cast hcols.symm i.castSucc.castSucc) *
            aswKarlinRootVector z p.natDegree order blocks
              (Fin.cast hcols.symm i.succ.succ) < 0 := by
    intro i hi
    change (z ^ ((i : ℕ) + 1)).im = 0 at hi
    change (z ^ (i : ℕ)).im * (z ^ ((i : ℕ) + 2)).im < 0
    exact
      im_pow_mul_im_pow_add_two_neg_of_im_pow_add_one_eq_zero him i hi
  have hbound :=
    Matrix.IsTotallyNonnegRect.card_sub_one_le_signVariations_add_two_of_surjective_of_card_eq
      (hpf.aswKarlinMatrix_isTotallyNonnegRect
        p.natDegree order blocks)
      hcols
      (aswKarlinMatrix_mulVec_surjective p.natDegree order blocks
        hdegree horder hconst)
      (aswKarlinMatrix_mulVec_rootVector hz order blocks hdegree horder)
      hnodal
  rw [signVariations_aswKarlinRootVector_eq_sine
    (complex_root_ne_zero_of_coeff_zero_pos hz hconst)
    p.natDegree order blocks] at hbound
  exact hbound

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
    (him : z.im ≠ 0) :
    aswSectorThreshold p.natDegree order ≤ |z.arg| :=
  aswKarlinSectorThreshold_le_abs_arg_of_im_ne_zero_of_classicalInput
    aswKarlinKernelSignVariationClassicalInput hz hdegree hconst hpf horder
    him

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
  aswKarlinSectorThreshold_le_abs_arg_of_classicalInput
    aswKarlinKernelSignVariationClassicalInput hz hdegree hconst hpf horder

end RealRooted
