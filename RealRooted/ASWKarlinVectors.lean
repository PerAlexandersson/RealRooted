import RealRooted.Mathlib.LinearAlgebra.Matrix.SignVariation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Set.Countable

/-!
# Karlin root and sine vectors

This file contains the finite vectors used in Karlin's sector proof.  The
root vector records imaginary parts of powers of a complex root; after
normalizing by the positive powers of the norm, it has the same sign pattern
as the corresponding sampled sine vector.
-/

noncomputable section

namespace RealRooted

/-- The imaginary parts of successive powers of a complex number, truncated
to the columns of Karlin's repeated matrix. -/
def aswKarlinRootVector (z : ℂ) (degree order blocks : ℕ) :
    Fin (blocks * (degree + order - 1) + 1) → ℝ :=
  fun j => (z ^ (j : ℕ)).im

/-- The sampled sine vector corresponding to the argument of a complex root. -/
def aswKarlinSineVector (θ : ℝ) (degree order blocks : ℕ) :
    Fin (blocks * (degree + order - 1) + 1) → ℝ :=
  fun j => Real.sin ((j : ℕ) * θ)

/-- The imaginary parts of a phase-rotated power vector, truncated to the
columns of Karlin's repeated matrix. -/
def aswKarlinPhasedRootVector (z : ℂ) (phase : ℝ) (degree order blocks : ℕ) :
    Fin (blocks * (degree + order - 1) + 1) → ℝ :=
  fun j => (Complex.exp (phase * Complex.I) * z ^ (j : ℕ)).im

/-- The sampled sine vector corresponding to a phase and an argument. -/
def aswKarlinPhasedSineVector (phase θ : ℝ) (degree order blocks : ℕ) :
    Fin (blocks * (degree + order - 1) + 1) → ℝ :=
  fun j => Real.sin (phase + (j : ℕ) * θ)

/-- A phase avoids all zero coordinates in Karlin's finite sampled sine
vector. -/
def AswKarlinPhaseAvoidsZeros
    (phase θ : ℝ) (degree order blocks : ℕ) : Prop :=
  ∀ j : Fin (blocks * (degree + order - 1) + 1),
    aswKarlinPhasedSineVector phase θ degree order blocks j ≠ 0

/-- For a fixed shift, the phases where the corresponding sampled sine
coordinate vanishes form a countable set. -/
private lemma aswKarlin_sine_zero_phase_set_countable (c : ℝ) :
    Set.Countable {phase : ℝ | Real.sin (phase + c) = 0} := by
  let f : ℤ → ℝ := fun n => (n : ℝ) * Real.pi - c
  refine (Set.countable_range f).mono ?_
  intro phase hphase
  rcases Real.sin_eq_zero_iff.mp hphase with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  dsimp [f]
  linarith

/-- There is always a phase avoiding all zero coordinates in Karlin's finite
sampled sine vector. -/
theorem exists_phase_avoidsZeros_aswKarlinPhasedSineVector
    (θ : ℝ) (degree order blocks : ℕ) :
    ∃ phase : ℝ, AswKarlinPhaseAvoidsZeros phase θ degree order blocks := by
  classical
  let bad : Set ℝ :=
    ⋃ j : Fin (blocks * (degree + order - 1) + 1),
      {phase : ℝ | Real.sin (phase + (j : ℕ) * θ) = 0}
  have hbad_countable : bad.Countable := by
    dsimp [bad]
    exact Set.countable_iUnion fun j =>
      aswKarlin_sine_zero_phase_set_countable ((j : ℕ) * θ)
  by_contra hnone
  have huniv_subset_bad : (Set.univ : Set ℝ) ⊆ bad := by
    intro phase _
    have hnot :
        ¬ AswKarlinPhaseAvoidsZeros phase θ degree order blocks := by
      intro havoid
      exact hnone ⟨phase, havoid⟩
    rw [AswKarlinPhaseAvoidsZeros] at hnot
    push Not at hnot
    rcases hnot with ⟨j, hj⟩
    exact Set.mem_iUnion.2 ⟨j, by
      simpa [aswKarlinPhasedSineVector] using hj⟩
  have huniv_countable : (Set.univ : Set ℝ).Countable :=
    hbad_countable.mono huniv_subset_bad
  exact Set.not_countable_univ huniv_countable

/-- There is always an arbitrarily small positive phase avoiding all zero
coordinates in Karlin's finite sampled sine vector. -/
theorem exists_phase_mem_Ioo_avoidsZeros_aswKarlinPhasedSineVector
    {ε θ : ℝ} (hε : 0 < ε) (degree order blocks : ℕ) :
    ∃ phase : ℝ,
      phase ∈ Set.Ioo 0 ε ∧
        AswKarlinPhaseAvoidsZeros phase θ degree order blocks := by
  classical
  let bad : Set ℝ :=
    ⋃ j : Fin (blocks * (degree + order - 1) + 1),
      {phase : ℝ | Real.sin (phase + (j : ℕ) * θ) = 0}
  have hbad_countable : bad.Countable := by
    dsimp [bad]
    exact Set.countable_iUnion fun j =>
      aswKarlin_sine_zero_phase_set_countable ((j : ℕ) * θ)
  by_contra hnone
  have hIoo_subset_bad : Set.Ioo (0 : ℝ) ε ⊆ bad := by
    intro phase hphase_mem
    have hnot :
        ¬ AswKarlinPhaseAvoidsZeros phase θ degree order blocks := by
      intro havoid
      exact hnone ⟨phase, hphase_mem, havoid⟩
    rw [AswKarlinPhaseAvoidsZeros] at hnot
    push Not at hnot
    rcases hnot with ⟨j, hj⟩
    exact Set.mem_iUnion.2 ⟨j, by
      simpa [aswKarlinPhasedSineVector] using hj⟩
  have hIoo_countable : (Set.Ioo (0 : ℝ) ε).Countable :=
    hbad_countable.mono hIoo_subset_bad
  have hIoo_not_countable : ¬ (Set.Ioo (0 : ℝ) ε).Countable := by
    rw [← Cardinal.le_aleph0_iff_set_countable,
      Cardinal.mk_Ioo_real hε, not_le]
    exact Cardinal.aleph0_lt_continuum
  exact hIoo_not_countable hIoo_countable

/-- If a last unphased sampled angle is strictly below an integral multiple
of `π`, there is a positive zero-avoiding phase preserving that strict
endpoint bound. -/
theorem exists_phase_avoidsZeros_with_last_lt_nat_mul_pi
    {θ : ℝ} {N orderBound : ℕ}
    (hmargin : (N : ℝ) * θ < (orderBound : ℝ) * Real.pi)
    (degree order blocks : ℕ) :
    ∃ phase : ℝ,
      AswKarlinPhaseAvoidsZeros phase θ degree order blocks ∧
        0 < phase ∧
          phase + (N : ℝ) * θ < (orderBound : ℝ) * Real.pi := by
  let ε := (orderBound : ℝ) * Real.pi - (N : ℝ) * θ
  have hε : 0 < ε := sub_pos.mpr hmargin
  obtain ⟨phase, hphase_mem, havoid⟩ :=
    exists_phase_mem_Ioo_avoidsZeros_aswKarlinPhasedSineVector
      (ε := ε) (θ := θ) hε degree order blocks
  refine ⟨phase, havoid, hphase_mem.1, ?_⟩
  have hphase_lt : phase < ε := hphase_mem.2
  dsimp [ε] at hphase_lt
  linarith

/-- ASW-indexed form of
`exists_phase_avoidsZeros_with_last_lt_nat_mul_pi`, using the final sampled
index and target variation count from Karlin's repeated matrix. -/
theorem exists_phase_avoidsZeros_aswKarlin_with_last_lt_order_pi
    {θ : ℝ} {degree order blocks : ℕ}
    (hmargin :
      ((blocks * (degree + order - 1) : ℕ) : ℝ) * θ <
        ((blocks * order : ℕ) : ℝ) * Real.pi) :
    ∃ phase : ℝ,
      AswKarlinPhaseAvoidsZeros phase θ degree order blocks ∧
        0 < phase ∧
          phase + ((blocks * (degree + order - 1) : ℕ) : ℝ) * θ <
            ((blocks * order : ℕ) : ℝ) * Real.pi := by
  exact
    exists_phase_avoidsZeros_with_last_lt_nat_mul_pi
      (N := blocks * (degree + order - 1))
      (orderBound := blocks * order) hmargin degree order blocks

@[simp]
lemma aswKarlinPhasedRootVector_zero_phase (z : ℂ) (degree order blocks : ℕ) :
    aswKarlinPhasedRootVector z 0 degree order blocks =
      aswKarlinRootVector z degree order blocks := by
  funext j
  simp [aswKarlinPhasedRootVector, aswKarlinRootVector]

@[simp]
lemma aswKarlinPhasedSineVector_zero_phase
    (θ : ℝ) (degree order blocks : ℕ) :
    aswKarlinPhasedSineVector 0 θ degree order blocks =
      aswKarlinSineVector θ degree order blocks := by
  funext j
  simp [aswKarlinPhasedSineVector, aswKarlinSineVector]

@[simp]
lemma aswKarlinSineVector_zero_apply (degree order blocks : ℕ)
    (j : Fin (blocks * (degree + order - 1) + 1)) :
    aswKarlinSineVector 0 degree order blocks j = 0 := by
  simp [aswKarlinSineVector]

lemma aswKarlinSineVector_neg (θ : ℝ) (degree order blocks : ℕ) :
    aswKarlinSineVector (-θ) degree order blocks =
      fun j => -aswKarlinSineVector θ degree order blocks j := by
  funext j
  simp [aswKarlinSineVector, mul_neg]

lemma im_pow_eq_norm_pow_mul_sin_arg (z : ℂ) (n : ℕ) :
    (z ^ n).im = ‖z‖ ^ n * Real.sin (n * z.arg) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_im]
  simp

/-- If a nonreal complex geometric progression has an interior zero imaginary
part, the adjacent imaginary parts have opposite strict signs. -/
lemma im_pow_mul_im_pow_add_two_neg_of_im_pow_add_one_eq_zero
    {z : ℂ} (him : z.im ≠ 0) (i : ℕ)
    (hzero : (z ^ (i + 1)).im = 0) :
    (z ^ i).im * (z ^ (i + 2)).im < 0 := by
  let θ := z.arg
  have hz : z ≠ 0 := by
    intro hz
    apply him
    simp [hz]
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hsin : Real.sin θ ≠ 0 := by
    have hpolar := im_pow_eq_norm_pow_mul_sin_arg z 1
    simp only [pow_one, Nat.cast_one, one_mul] at hpolar
    intro hs
    apply him
    rw [hpolar, hs, mul_zero]
  have hzeroSin : Real.sin ((i + 1 : ℕ) * θ) = 0 := by
    rw [im_pow_eq_norm_pow_mul_sin_arg] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hnorm.ne')
  have hcos : Real.cos ((i + 1 : ℕ) * θ) ≠ 0 := by
    intro hc
    have hsq := Real.sin_sq_add_cos_sq ((i + 1 : ℕ) * θ)
    rw [hzeroSin, hc] at hsq
    norm_num at hsq
  have hprev :
      Real.sin (i * θ) =
        -Real.cos ((i + 1 : ℕ) * θ) * Real.sin θ := by
    have harg :
        (i : ℝ) * θ = ((i + 1 : ℕ) : ℝ) * θ - θ := by
      push_cast
      ring
    rw [harg, Real.sin_sub, hzeroSin]
    ring
  have hnext :
      Real.sin ((i + 2 : ℕ) * θ) =
        Real.cos ((i + 1 : ℕ) * θ) * Real.sin θ := by
    have harg :
        ((i + 2 : ℕ) : ℝ) * θ =
          ((i + 1 : ℕ) : ℝ) * θ + θ := by
      push_cast
      ring
    rw [harg, Real.sin_add, hzeroSin]
    ring
  have htrig :
      Real.sin (i * θ) * Real.sin ((i + 2 : ℕ) * θ) < 0 := by
    rw [hprev, hnext]
    calc
      (-Real.cos ((i + 1 : ℕ) * θ) * Real.sin θ) *
          (Real.cos ((i + 1 : ℕ) * θ) * Real.sin θ) =
          -(Real.cos ((i + 1 : ℕ) * θ) ^ 2 * Real.sin θ ^ 2) := by ring
      _ < 0 := neg_lt_zero.mpr
        (mul_pos (sq_pos_of_ne_zero hcos) (sq_pos_of_ne_zero hsin))
  rw [im_pow_eq_norm_pow_mul_sin_arg,
    im_pow_eq_norm_pow_mul_sin_arg]
  calc
    (‖z‖ ^ i * Real.sin (i * θ)) *
        (‖z‖ ^ (i + 2) * Real.sin ((i + 2 : ℕ) * θ)) =
        (‖z‖ ^ i * ‖z‖ ^ (i + 2)) *
          (Real.sin (i * θ) * Real.sin ((i + 2 : ℕ) * θ)) := by ring
    _ < 0 := mul_neg_of_pos_of_neg
      (mul_pos (pow_pos hnorm _) (pow_pos hnorm _)) htrig
lemma im_phase_mul_pow_eq_norm_pow_mul_sin_add_arg
    (z : ℂ) (phase : ℝ) (n : ℕ) :
    (Complex.exp (phase * Complex.I) * z ^ n).im =
      ‖z‖ ^ n * Real.sin (phase + n * z.arg) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow]
  rw [← mul_assoc]
  rw [mul_comm (Complex.exp (↑phase * Complex.I)) (↑(‖z‖ ^ n) : ℂ)]
  rw [mul_assoc, ← Complex.exp_add]
  rw [show ↑phase * Complex.I + ↑n * (↑z.arg * Complex.I) =
      ↑(phase + n * z.arg) * Complex.I by
    norm_num
    ring]
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_im]
  simp

/-- A nonzero complex number's root vector and sampled sine vector have the
same coordinate signs. -/
lemma signVariations_aswKarlinRootVector_eq_sine {z : ℂ} (hz : z ≠ 0)
    (degree order blocks : ℕ) :
    Fin.signVariations (aswKarlinRootVector z degree order blocks) =
      Fin.signVariations (aswKarlinSineVector z.arg degree order blocks) := by
  apply Fin.signVariations_congr_sign
  intro j
  rw [aswKarlinRootVector, aswKarlinSineVector,
    im_pow_eq_norm_pow_mul_sin_arg, sign_mul]
  have hnorm : 0 < ‖z‖ ^ (j : ℕ) := pow_pos (norm_pos_iff.mpr hz) _
  simp [hnorm]

/-- A nonzero complex number's phase-rotated root vector and phased sampled
sine vector have the same coordinate signs. -/
lemma signVariations_aswKarlinPhasedRootVector_eq_phasedSine
    {z : ℂ} (hz : z ≠ 0) (phase : ℝ) (degree order blocks : ℕ) :
    Fin.signVariations
        (aswKarlinPhasedRootVector z phase degree order blocks) =
      Fin.signVariations
        (aswKarlinPhasedSineVector phase z.arg degree order blocks) := by
  apply Fin.signVariations_congr_sign
  intro j
  rw [aswKarlinPhasedRootVector, aswKarlinPhasedSineVector,
    im_phase_mul_pow_eq_norm_pow_mul_sin_add_arg, sign_mul]
  have hnorm : 0 < ‖z‖ ^ (j : ℕ) := pow_pos (norm_pos_iff.mpr hz) _
  simp [hnorm]

/-- If the sampled sine vector has no zero coordinates, then the corresponding
phase-rotated root vector has no zero coordinates. -/
theorem aswKarlinPhasedRootVector_zeroFree_of_phaseAvoids
    {z : ℂ} {phase : ℝ} {degree order blocks : ℕ} (hz : z ≠ 0)
    (hphase : AswKarlinPhaseAvoidsZeros phase z.arg degree order blocks) :
    ∀ j : Fin (blocks * (degree + order - 1) + 1),
      aswKarlinPhasedRootVector z phase degree order blocks j ≠ 0 := by
  intro j hzero
  have hcoord :
      ‖z‖ ^ (j : ℕ) * Real.sin (phase + (j : ℕ) * z.arg) = 0 := by
    simpa [aswKarlinPhasedRootVector,
      im_phase_mul_pow_eq_norm_pow_mul_sin_add_arg z phase (j : ℕ)] using hzero
  have hnorm : ‖z‖ ^ (j : ℕ) ≠ 0 :=
    (pow_pos (norm_pos_iff.mpr hz) (j : ℕ)).ne'
  have hsine : Real.sin (phase + (j : ℕ) * z.arg) = 0 :=
    (mul_eq_zero.mp hcoord).resolve_left hnorm
  exact hphase j (by simpa [aswKarlinPhasedSineVector] using hsine)

lemma signVariations_aswKarlinSineVector_neg (θ : ℝ) (degree order blocks : ℕ) :
    Fin.signVariations (aswKarlinSineVector (-θ) degree order blocks) =
      Fin.signVariations (aswKarlinSineVector θ degree order blocks) := by
  rw [aswKarlinSineVector_neg]
  exact Fin.signVariations_neg (aswKarlinSineVector θ degree order blocks)

@[simp]
lemma signVariations_aswKarlinSineVector_zero (degree order blocks : ℕ) :
    Fin.signVariations (aswKarlinSineVector 0 degree order blocks) = 0 := by
  simp [Fin.signVariations, List.signVariations]

/-- In the one-block Karlin matrix, a nonreal complex number gives a nonzero
root vector: the coordinate at exponent one is its imaginary part. -/
lemma aswKarlinRootVector_ne_zero_of_im_ne_zero {z : ℂ} {degree order : ℕ}
    (hdegree : 0 < degree) (horder : 0 < order) (him : z.im ≠ 0) :
    aswKarlinRootVector z degree order 1 ≠ 0 := by
  intro hzero
  have hcols : 1 < 1 * (degree + order - 1) + 1 := by
    have hsum : 1 ≤ degree + order - 1 := by lia
    lia
  have hcoord :=
    congrFun hzero (⟨1, hcols⟩ : Fin (1 * (degree + order - 1) + 1))
  exact him (by simpa [aswKarlinRootVector] using hcoord)

end RealRooted
