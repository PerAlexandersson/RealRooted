module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import RealRooted.ExponentialRows.TwoSizeExponential
import RealRooted.BinaryRunTransformation.MultiplierMotzkin
import RealRooted.BinaryRunTransformation.Anchor
import RealRooted.PosCombo
import RealRooted.WagnerRightSum.Sign
import RealRooted.PFPolynomial.LowCoefficients
import RealRooted.DegreeDropReversal
import RealRooted.QuadraticRoot
import RealRooted.Mathlib.Algebra.Polynomial.Splits.Complex
import Mathlib.Tactic

/-!
# Exact two-size exponential and ordered boundaries

We use small reciprocal roots of complete-graph matching polynomials to
supply Hermite pencil parameters approaching zero. Outside `ad ≥ bc`, those
parameters give nonreal zeros of an exponential row. Path-matching roots
give the ordered counterpart, whose sufficient direction follows by translation
and an interlacing recurrence.

Source: unpublished manuscript, RealRooted #2415 and #2590, round two:
https://github.com/PerAlexandersson/RealRooted/issues/2415#issuecomment-7136509900.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- The complete matching polynomial on an even number of vertices has
exactly half that many degrees. -/
private theorem matching_natDegree (m : ℕ) :
    (completeMatchingPolynomial (2 * m)).natDegree = m := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_completeMatchingPolynomial, completeMatchingCount_eq_zero (by lia)]
  · rw [coeff_completeMatchingPolynomial]
    exact (completeMatchingCount_pos (by lia)).ne'

/-- The three lowest normalized reciprocal coefficients are elementary
polynomials in half the vertex count. -/
private theorem matching_reverse_low_coeff (m : ℕ) :
    let f := completeMatchingPolynomial (2 * (m + 2))
    let g := C (f.leadingCoeff)⁻¹ * f.reverse
    g.coeff 0 = 1 ∧ g.coeff 1 = (m + 2 : ℝ) ∧
      g.coeff 2 = (m + 2 : ℝ) * (m + 1) / 6 := by
  let f := completeMatchingPolynomial (2 * (m + 2))
  have hdeg : f.natDegree = m + 2 := matching_natDegree (m + 2)
  have hc (k : ℕ) (hk : k ≤ m + 2) :
      f.reverse.coeff k = completeMatchingCount (2 * (m + 2)) (m + 2 - k) := by
    rw [coeff_reverse, hdeg, revAt_le hk, coeff_completeMatchingPolynomial]
  have hlc : f.leadingCoeff = completeMatchingCount (2 * (m + 2)) (m + 2) := by
    rw [leadingCoeff, hdeg, coeff_completeMatchingPolynomial]
  have ha : f.leadingCoeff ≠ 0 := by
    rw [hlc]
    exact (completeMatchingCount_pos (by lia)).ne'
  change (C f.leadingCoeff⁻¹ * f.reverse).coeff 0 = 1 ∧ _
  simp only [coeff_C_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [coeff_reverse, revAt_le (Nat.zero_le _), Nat.sub_zero, coeff_natDegree,
      inv_mul_cancel₀ ha]
  · rw [hc 1 (by lia), hlc,
      show m + 2 - 1 = m + 1 by lia,
      completeMatchingCount_of_le (by lia), completeMatchingCount_of_le (by lia),
      show 2 * (m + 2) - 2 * (m + 2) = 0 by lia,
      show 2 * (m + 2) - 2 * (m + 1) = 2 by lia]
    have hF : ((2 * (m + 2)).factorial : ℝ) ≠ 0 := by positivity
    have hM : (m.factorial : ℝ) ≠ 0 := by positivity
    generalize ((2 * (m + 2)).factorial : ℝ) = F at hF ⊢
    simp only [Nat.factorial_zero, Nat.cast_one,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, pow_succ]
    field_simp
    ring
  · rw [hc 2 (by lia), hlc,
      show m + 2 - 2 = m by lia,
      completeMatchingCount_of_le (by lia), completeMatchingCount_of_le (by lia),
      show 2 * (m + 2) - 2 * (m + 2) = 0 by lia,
      show 2 * (m + 2) - 2 * m = 4 by lia]
    have hF : ((2 * (m + 2)).factorial : ℝ) ≠ 0 := by positivity
    have hM : (m.factorial : ℝ) ≠ 0 := by positivity
    generalize ((2 * (m + 2)).factorial : ℝ) = F at hF ⊢
    norm_num only [Nat.factorial_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat, pow_succ]
    field_simp
    ring

/-- Complete matching polynomials have negative roots whose inverse magnitude
is arbitrarily small as the even vertex count grows. -/
private theorem matching_exists_small_inverse_root (m : ℕ) :
    ∃ v : ℝ, 0 < v ∧ v < 2 / (m + 2 : ℝ) ∧
      (completeMatchingPolynomial (2 * (m + 2))).eval (-v⁻¹) = 0 := by
  let f := completeMatchingPolynomial (2 * (m + 2))
  let g := C f.leadingCoeff⁻¹ * f.reverse
  have hf := completeMatchingPolynomial_isPFPolynomial (2 * (m + 2))
  have hlc : 0 < f.leadingCoeff := hf.hasNonnegCoeffs.pos_leadingCoeff (by
    intro hz
    have h := matching_natDegree (m + 2)
    rw [hz, natDegree_zero] at h
    lia)
  have hg : IsPFPolynomial g := hf.reverse.const_mul (inv_pos.mpr hlc)
  obtain ⟨h0, h1, h2⟩ := matching_reverse_low_coeff m
  have hm : 0 < (m + 2 : ℝ) := by positivity
  let e := (m + 1 : ℝ) / (3 * (m + 2))
  have he : 2 * g.coeff 2 = e * g.coeff 1 ^ 2 := by
    rw [h1, h2]
    dsimp only [e]
    field_simp
    ring
  have he2 : e < 1 / 2 := by
    dsimp only [e]
    rw [div_lt_iff₀ (by positivity)]
    linarith
  obtain ⟨v, hv, hroot, _, _, _, hvlt, _, _, _⟩ :=
    hg.exists_largest_root_lt_two_div_coeff_one h0 (h1 ▸ hm) he he2
  refine ⟨v, hv, ?_, ?_⟩
  · rw [h1] at hvlt
    exact hvlt
  · have hrev : -v ∈ f.reverse.roots := by
      simpa only [g, roots_C_mul _ (inv_ne_zero hlc.ne')] using hroot
    obtain ⟨r, hr, heq⟩ := (DegreeDropReversal.mem_roots_reverse_iff hf.splits
      (by
        rw [coeff_completeMatchingPolynomial, completeMatchingCount_zero_right]
        exact one_ne_zero)).mp hrev
    have hrval : r = -v⁻¹ := by
      have h := congrArg Inv.inv heq
      simpa only [inv_inv, inv_neg] using h
    rw [← hrval]
    exact isRoot_of_mem_roots hr

/-- Evaluation of the complete matching polynomial is a homogeneous Hermite
polynomial with half the matching activity as variance. -/
private theorem matching_eval_hermite (t : ℝ) (n : ℕ) :
    (completeMatchingPolynomial n).eval t = hermiteHomogeneous 1 (t / 2) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [completeMatchingPolynomial_zero, eval_one, hermiteHomogeneous_zero]
  | one => simp only [completeMatchingPolynomial_one, eval_one, hermiteHomogeneous_one]
  | more n ih ih' =>
    rw [completeMatchingPolynomial_succ_succ, eval_add, eval_mul, eval_mul, eval_C,
      eval_X, ih, ih', hermiteHomogeneous_add_two]
    push_cast
    ring

/-- Simultaneous scaling in the two homogeneous arguments has the expected
weight, without a nonvanishing hypothesis on the scale. -/
private theorem hermite_scaled {R : Type*} [CommRing R] (u x y : R) (n : ℕ) :
    hermiteHomogeneous (u * x) (u ^ 2 * y) n = u ^ n * hermiteHomogeneous x y n := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [hermiteHomogeneous_zero, pow_zero, mul_one]
  | one => simp only [hermiteHomogeneous_one, pow_one]
  | more n ih ih' =>
    rw [hermiteHomogeneous_add_two, ih, ih', hermiteHomogeneous_add_two]
    simp only [pow_succ]
    ring

/-- Nonnegative variance and a positive linear argument make every numerical
homogeneous Hermite polynomial positive. -/
private theorem hermite_pos {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (n : ℕ) :
    0 < hermiteHomogeneous x y n := by
  induction n using Nat.twoStepInduction with
  | zero => exact zero_lt_one
  | one => exact hx
  | more n ih ih' =>
    rw [hermiteHomogeneous_add_two]
    exact add_pos_of_pos_of_nonneg (mul_pos hx ih') (by positivity)

/-- A reciprocal matching root supplies an entire quadratic factor locus
of the corresponding polynomial-weight Hermite row. -/
private theorem hermite_eq_zero_of_matching_root {v : ℝ} (hv : 0 < v) {n : ℕ}
    (hroot : (completeMatchingPolynomial n).eval (-v⁻¹) = 0)
    {x y : ℂ} (hxy : x ^ 2 + (2 * v : ℂ) * y = 0) :
    hermiteHomogeneous x y n = 0 := by
  rw [matching_eval_hermite] at hroot
  have hc := congrArg Complex.ofRealHom hroot
  rw [map_hermiteHomogeneous] at hc
  simp only [map_one, map_div₀, map_neg, map_inv₀, map_ofNat, map_zero,
    Complex.ofRealHom_eq_coe] at hc
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  have hy : y = x ^ 2 * (-(v : ℂ)⁻¹ / 2) := by
    field_simp
    linear_combination hxy
  rw [hy]
  simpa only [mul_one, hc, mul_zero] using hermite_scaled x 1 (-(v : ℂ)⁻¹ / 2) n

/-- Outside the affine boundary, every sufficiently small positive pencil
parameter gives a nonsplitting quadratic. -/
private theorem exists_bad_affine_interval {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hdet : a * d < b * c) :
    ∃ M : ℝ, 0 < M ∧ ∀ v : ℝ, 0 < v → v < M →
      ¬ ((C a + C b * X) ^ 2 + C v * (C c + C d * X)).Splits := by
  have hbpos : 0 < b := by
    by_contra h
    have hbzero : b = 0 := le_antisymm (le_of_not_gt h) hb
    rw [hbzero, zero_mul] at hdet
    exact (not_lt_of_ge (mul_nonneg ha hd)) hdet
  let u := b * (b * c - a * d)
  have hu : 0 < u := mul_pos hbpos (sub_pos.mpr hdet)
  let M := u / (d ^ 2 + u + 1)
  have hden : 0 < d ^ 2 + u + 1 := by positivity
  have hM : 0 < M := div_pos hu hden
  have hMeq : M * (d ^ 2 + u + 1) = u := div_mul_cancel₀ _ hden.ne'
  have hMd : M * d ^ 2 < u := by nlinarith
  refine ⟨M, hM, ?_⟩
  intro v hv hvM
  have hvd : v * d ^ 2 < u :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hvM.le (sq_nonneg d)) hMd
  let F : ℝ[X] := (C a + C b * X) ^ 2 + C v * (C c + C d * X)
  have he : F = C (b ^ 2) * X ^ 2 + C (2 * a * b + v * d) * X +
      C (a ^ 2 + v * c) := by
    dsimp only [F]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  change ¬ F.Splits
  rw [he]
  apply quadraticPoly_not_splits_of_discrim_neg (pow_ne_zero _ hbpos.ne')
  rw [discrim]
  have heq : (2 * a * b + v * d) ^ 2 -
      4 * b ^ 2 * (a ^ 2 + v * c) = v * (v * d ^ 2 - 4 * u) := by
    dsimp only [u]
    ring
  rw [heq]
  exact mul_neg_of_pos_of_neg hv (by linarith)

/-- An affine two-size family outside the determinant boundary has a
nonsplitting homogeneous Hermite row. The row index is not uniformly bounded. -/
theorem exists_not_splits_two_size {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hdet : a * d < b * c) :
    ∃ n : ℕ, ¬ (hermiteHomogeneous (C a + C b * X) (C c + C d * X) n).Splits := by
  have hbpos : 0 < b := by
    by_contra h
    have hbzero : b = 0 := le_antisymm (le_of_not_gt h) hb
    rw [hbzero, zero_mul] at hdet
    exact (not_lt_of_ge (mul_nonneg ha hd)) hdet
  obtain ⟨M, hM, hbadM⟩ := exists_bad_affine_interval ha hb hd hdet
  obtain ⟨m, hm⟩ := exists_nat_gt (4 / M)
  have hmpos : 0 < (m + 2 : ℝ) := by positivity
  have hbound : 4 / (m + 2 : ℝ) < M := by
    rw [div_lt_iff₀ hmpos]
    have hcancel : 4 / M * M = 4 := div_mul_cancel₀ _ hM.ne'
    nlinarith
  obtain ⟨v, hv, hvm, hroot⟩ := matching_exists_small_inverse_root m
  have hvM : 2 * v < M := by
    have hdiv : 2 * (2 / (m + 2 : ℝ)) = 4 / (m + 2 : ℝ) := by ring
    linarith
  let F : ℝ[X] := (C a + C b * X) ^ 2 + C (2 * v) * (C c + C d * X)
  have hbad : ¬ F.Splits := hbadM (2 * v) (by positivity) hvM
  obtain ⟨z, hz, hzim⟩ : ∃ z : ℂ, (F.map Complex.ofRealHom).eval z = 0 ∧ z.im ≠ 0 := by
    by_contra! h
    exact hbad (Polynomial.splits_of_all_roots_real h)
  refine ⟨2 * (m + 2), ?_⟩
  intro hs
  let G := hermiteHomogeneous (C a + C b * X) (C c + C d * X) (2 * (m + 2))
  have hGne : G ≠ 0 := by
    intro hzero
    have he : G.eval 1 = hermiteHomogeneous (a + b) (c + d) (2 * (m + 2)) := by
      dsimp only [G]
      have H := map_hermiteHomogeneous (evalRingHom (1 : ℝ))
        (C a + C b * X) (C c + C d * X) (2 * (m + 2))
      change (hermiteHomogeneous (C a + C b * X) (C c + C d * X)
        (2 * (m + 2))).eval 1 = hermiteHomogeneous
          ((C a + C b * X).eval 1) ((C c + C d * X).eval 1) (2 * (m + 2)) at H
      simpa only [eval_add, eval_mul, eval_C, eval_X, mul_one] using H
    rw [hzero, eval_zero] at he
    exact (hermite_pos (by linarith) (by positivity) (2 * (m + 2))).ne' he.symm
  have hGz : (G.map Complex.ofRealHom).IsRoot z := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map]
    change (eval₂RingHom Complex.ofRealHom z) G = 0
    dsimp only [G]
    rw [map_hermiteHomogeneous]
    apply hermite_eq_zero_of_matching_root hv hroot
    change (eval₂ Complex.ofRealHom z (C a + C b * X)) ^ 2 +
      (2 * v : ℂ) * eval₂ Complex.ofRealHom z (C c + C d * X) = 0
    simpa only [F, eval_map, eval₂_add, eval₂_pow, eval₂_mul, eval₂_C, eval₂_ofNat,
      map_mul, map_ofNat, Complex.ofRealHom_eq_coe] using hz
  obtain ⟨r, hr⟩ := hs.mem_range_of_isRoot hGne hGz
  exact hzim (by rw [← hr]; exact Complex.ofReal_im r)

/-- Every exponential two-size row splits exactly on `ad ≥ bc`, for all
nonnegative parameter choices, including zero coefficients. -/
theorem insertionRow_splits_two_size_iff {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (∀ n : ℕ, (insertionRow (affineBlockWeights
      (PowerSeries.C a * PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 2)
      (PowerSeries.C b * PowerSeries.X + PowerSeries.C d * PowerSeries.X ^ 2)) n).Splits) ↔
      b * c ≤ a * d := by
  constructor
  · intro h
    by_contra hdet
    obtain ⟨n, hn⟩ := exists_not_splits_two_size ha hb hc hd (lt_of_not_ge hdet)
    apply hn
    rw [← insertionRow_two_size_eq_hermite]
    exact h n
  · intro hdet n
    exact insertionRow_splits_two_size_of_le ha hb hc hd hdet n

/-- The formal series for ordered weighted set partitions. The unit inverse
is valid over the polynomial coefficient ring because the denominator starts at one. -/
@[expose] noncomputable def orderedBlockSeries (w : ℕ → ℝ[X]) : PowerSeries ℝ[X] :=
  PowerSeries.invOfUnit (1 - blockWeightSeries w) 1

/-- Multiplication by the ordered denominator gives one, so `orderedBlockSeries`
is the formal reciprocal of `1 - blockWeightSeries w`. -/
theorem one_sub_blockWeightSeries_mul_orderedBlockSeries (w : ℕ → ℝ[X]) :
    (1 - blockWeightSeries w) * orderedBlockSeries w = 1 := by
  apply PowerSeries.mul_invOfUnit _ 1
  simp only [map_sub, map_one, blockWeightSeries_constantCoeff, sub_zero, Units.val_one]

/-- Factorial-scaled coefficient rows of the ordered block series. -/
@[expose] noncomputable def orderedBlockRow (w : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  factorialCoeff (orderedBlockSeries w) n

/-- The ordinary coefficients of a two-size ordered series obey its
second-order recurrence, including the two initial coefficients. -/
private theorem ordered_coeff_recurrence (p q : ℝ[X]) :
    let F := PowerSeries.invOfUnit
      (1 - PowerSeries.C p * PowerSeries.X - PowerSeries.C q * PowerSeries.X ^ 2) 1
    PowerSeries.coeff 0 F = 1 ∧ PowerSeries.coeff 1 F = p ∧
      ∀ n : ℕ, PowerSeries.coeff (n + 2) F =
        p * PowerSeries.coeff (n + 1) F + q * PowerSeries.coeff n F := by
  let F : PowerSeries ℝ[X] := PowerSeries.invOfUnit
    (1 - PowerSeries.C p * PowerSeries.X - PowerSeries.C q * PowerSeries.X ^ 2) 1
  have hzero : PowerSeries.constantCoeff
      (1 - PowerSeries.C p * PowerSeries.X - PowerSeries.C q * PowerSeries.X ^ 2) = 1 := by
    simp only [map_sub, map_one, map_mul, map_pow, PowerSeries.constantCoeff_X,
      zero_pow two_ne_zero, mul_zero, sub_zero]
  have hmul : F - PowerSeries.C p * (PowerSeries.X * F) -
      PowerSeries.C q * (PowerSeries.X ^ 2 * F) = 1 := by
    have h := PowerSeries.mul_invOfUnit
      (1 - PowerSeries.C p * PowerSeries.X - PowerSeries.C q * PowerSeries.X ^ 2) 1 hzero
    change _ * F = 1 at h
    linear_combination h
  have h0 : PowerSeries.coeff 0 F = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit]
    rfl
  have h1 : PowerSeries.coeff 1 F = p := by
    have h := congrArg (PowerSeries.coeff 1) hmul
    simp only [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_X_pow_mul', Nat.not_ofNat_le_one,
      ↓reduceIte, PowerSeries.coeff_one, Nat.one_ne_zero, h0, mul_one, mul_zero, sub_zero] at h
    exact sub_eq_zero.mp h
  refine ⟨h0, h1, ?_⟩
  intro n
  have h := congrArg (PowerSeries.coeff (n + 2)) hmul
  rw [map_sub, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul] at h
  rw [PowerSeries.coeff_one, ite_eq_right (by lia : n + 2 ≠ 0)] at h
  linear_combination h

/-- The first three reversed path-matching coefficients are explicit. -/
private theorem path_reverse_low_coeff (m : ℕ) :
    let g := (pathMatchingPolynomial (2 * (m + 2))).reverse
    g.coeff 0 = 1 ∧ g.coeff 1 = (m + 2 : ℝ) * (m + 3) / 2 ∧
      g.coeff 2 = (m + 1 : ℝ) * (m + 2) * (m + 3) * (m + 4) / 24 := by
  have hc (k : ℕ) (hk : k ≤ m + 2) :
      (pathMatchingPolynomial (2 * (m + 2))).reverse.coeff k =
        ((m + 2 + k).choose (m + 2 - k) : ℝ) := by
    rw [coeff_reverse, natDegree_pathMatchingPolynomial, Nat.mul_div_cancel_left _ two_pos,
      revAt_le hk, coeff_pathMatchingPolynomial]
    rw [show 2 * (m + 2) - (m + 2 - k) = m + 2 + k by lia]
  refine ⟨?_, ?_, ?_⟩
  · rw [hc 0 (by lia)]
    simp only [Nat.add_zero, Nat.sub_zero, Nat.choose_self, Nat.cast_one]
  · rw [hc 1 (by lia), show m + 2 - 1 = m + 1 by lia,
      show m + 2 + 1 = m + 3 by lia,
      Nat.choose_symm_of_eq_add (show m + 3 = (m + 1) + 2 by lia), Nat.cast_choose_two]
    push_cast
    ring
  · rw [hc 2 (by lia), show m + 2 - 2 = m by lia,
      show m + 2 + 2 = m + 4 by lia,
      Nat.choose_symm_of_eq_add (show m + 4 = m + 4 by rfl),
      Nat.cast_choose ℝ (by lia), show m + 4 - 4 = m by lia]
    have hM : (m.factorial : ℝ) ≠ 0 := by positivity
    norm_num only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp
    ring

/-- Small reciprocal path-matching roots supply ordered pencil parameters
arbitrarily close to zero. -/
private theorem path_exists_small_inverse_root (m : ℕ) :
    ∃ v : ℝ, 0 < v ∧ v < 2 / (m + 2 : ℝ) ∧
      (pathMatchingPolynomial (2 * (m + 2))).eval (-v⁻¹) = 0 := by
  let f := pathMatchingPolynomial (2 * (m + 2))
  let g := f.reverse
  have hf := isPFPolynomial_pathMatchingPolynomial (2 * (m + 2))
  have hg : IsPFPolynomial g := hf.reverse
  obtain ⟨h0, h1, h2⟩ := path_reverse_low_coeff m
  have hpos : 0 < g.coeff 1 := by rw [h1]; positivity
  let e := (m + 1 : ℝ) * (m + 4) / (3 * (m + 2) * (m + 3))
  have he : 2 * g.coeff 2 = e * g.coeff 1 ^ 2 := by
    rw [h1, h2]
    dsimp only [e]
    field_simp
    ring
  have he2 : e < 1 / 2 := by
    dsimp only [e]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨v, hv, hroot, _, _, _, hvlt, _, _, _⟩ :=
    hg.exists_largest_root_lt_two_div_coeff_one h0 hpos he he2
  refine ⟨v, hv, ?_, ?_⟩
  · rw [h1] at hvlt
    have hh : 2 / ((m + 2 : ℝ) * (m + 3) / 2) ≤ 2 / (m + 2 : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    exact hvlt.trans_le hh
  · obtain ⟨r, hr, heq⟩ := (DegreeDropReversal.mem_roots_reverse_iff hf.splits
      (by rw [coeff_zero_pathMatchingPolynomial]; exact one_ne_zero)).mp hroot
    have hrval : r = -v⁻¹ := by
      have h := congrArg Inv.inv heq
      simpa only [inv_inv, inv_neg] using h
    rw [← hrval]
    exact isRoot_of_mem_roots hr

/-- The ordered recurrence with activities `s+bX` and `dX` preserves the
nonnegative PF cone and consecutive weak interlacing, including zero rows. -/
private theorem ordered_shifted_pf {s b d : ℝ}
    (hs : 0 ≤ s) (hb : 0 ≤ b) (hd : 0 ≤ d) (R : ℕ → ℝ[X])
    (h0 : R 0 = 1) (h1 : R 1 = C s + C b * X)
    (hrec : ∀ n, R (n + 2) = (C s + C b * X) * R (n + 1) + C d * (X * R n)) :
    ∀ n, IsPFPolynomial (R n) ∧ IsPFPolynomial (R (n + 1)) ∧ Interl (R n) (R (n + 1)) := by
  have hp : IsPFPolynomial (C s + C b * X) := by
    apply IsPFPolynomial.of_realRooted_nonneg
      ((hasNonnegCoeffs_C hs).add (hasNonnegCoeffs_C_mul hb hasNonnegCoeffs_X))
    exact Splits.of_natDegree_le_one (by compute_degree)
  intro n
  induction n with
  | zero =>
    rw [h0, h1]
    refine ⟨IsPFPolynomial.one, hp, ?_⟩
    have hself : Interl (1 : ℝ[X]) 1 := Interl.refl (fun _ => Splits.one)
    have hx := interl_mul_X_of_interl hself hasNonnegCoeffs_one hasNonnegCoeffs_one
    have H := interl_add_right_of_common_left_of_nonneg
      (hself.C_mul_right_of_nonneg hs) (hx.C_mul_right_of_nonneg hb)
      ((hasNonnegCoeffs_C hs).mul hasNonnegCoeffs_one)
      (hasNonnegCoeffs_C_mul hb (hasNonnegCoeffs_X.mul hasNonnegCoeffs_one))
    simpa only [mul_one] using H
  | succ n ih =>
    have hn := ih.1.hasNonnegCoeffs
    have hn' := ih.2.1.hasNonnegCoeffs
    have hself : Interl (R (n + 1)) (R (n + 1)) := Interl.refl (fun _ => ih.2.1.splits)
    have hxself := interl_mul_X_of_interl hself hn' hn'
    have hx := interl_mul_X_of_interl ih.2.2 hn hn'
    have hsum := interl_add_right_of_common_left_of_nonneg
      (hself.C_mul_right_of_nonneg hs) (hxself.C_mul_right_of_nonneg hb)
      (hasNonnegCoeffs_C_mul hs hn') (hasNonnegCoeffs_C_mul hb hn'.X_mul)
    have hnn := ((hasNonnegCoeffs_C_mul hs hn').add
      (hasNonnegCoeffs_C_mul hb hn'.X_mul)).add (hasNonnegCoeffs_C_mul hd hn.X_mul)
    have hout := interl_add_right_of_common_left_of_nonneg hsum
      (hx.C_mul_right_of_nonneg hd)
      ((hasNonnegCoeffs_C_mul hs hn').add (hasNonnegCoeffs_C_mul hb hn'.X_mul))
      (hasNonnegCoeffs_C_mul hd hn.X_mul)
    have hform : C s * R (n + 1) + C b * (X * R (n + 1)) + C d * (X * R n) =
        R (n + 2) := by rw [hrec]; ring
    rw [hform] at hout hnn
    refine ⟨ih.2.1, IsPFPolynomial.of_realRooted_nonneg hnn ?_, hout⟩
    by_cases hcur : R (n + 1) = 0
    · rw [hrec, hcur, mul_zero, zero_add]
      exact ih.1.X_mul.splits.C_mul d
    by_cases hnew : R (n + 2) = 0
    · rw [hnew]
      exact Splits.zero
    exact (hout.toStrictInterl_of_ne hcur hnew).2.1.2

/-- Every affine ordered two-size recurrence splits throughout `ad ≥ bc`.
Translation reduces positive `d` to the zero-constant pair activity `dX`. -/
private theorem ordered_recurrence_splits_of_le {a b c d : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hdet : b * c ≤ a * d)
    (R : ℕ → ℝ[X]) (h0 : R 0 = 1) (h1 : R 1 = C a + C b * X)
    (hrec : ∀ n, R (n + 2) = (C a + C b * X) * R (n + 1) + (C c + C d * X) * R n) :
    ∀ n, (R n).Splits := by
  by_cases hd0 : d = 0
  · by_cases hc0 : c = 0
    · have hpow : ∀ n, R n = (C a + C b * X) ^ n := by
        intro n
        induction n using Nat.twoStepInduction with
        | zero => simpa only [pow_zero] using h0
        | one => simpa only [pow_one] using h1
        | more n _ ih =>
          simp only [hrec, hd0, hc0, C_0, zero_mul, add_zero, ih]
          exact (pow_succ' _ (n + 1)).symm
      intro n
      rw [hpow]
      exact (Splits.of_natDegree_le_one (by compute_degree)).pow n
    · have hb0 : b = 0 := by
        have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
        rw [hd0, mul_zero] at hdet
        nlinarith
      have hdeg : ∀ n, (R n).natDegree = 0 := by
        intro n
        induction n using Nat.twoStepInduction with
        | zero => rw [h0, natDegree_one]
        | one => simp only [h1, hb0, C_0, zero_mul, add_zero, natDegree_C]
        | more n ih ih' =>
          simp only [hrec, hb0, hd0, C_0, zero_mul, add_zero]
          have hleft := (natDegree_C_mul_le a (R (n + 1))).trans (le_of_eq ih')
          have hright := (natDegree_C_mul_le c (R n)).trans (le_of_eq ih)
          exact Nat.eq_zero_of_le_zero (natDegree_add_le_of_degree_le hleft hright)
      exact fun n => Splits.of_natDegree_eq_zero (hdeg n)
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    let s := a - b * c / d
    have hs : 0 ≤ s := by
      dsimp only [s]
      rw [sub_nonneg, div_le_iff₀ hdpos]
      exact hdet
    let S (n : ℕ) := (R n).comp (X - C (c / d))
    have hp : (C a + C b * X).comp (X - C (c / d)) = C s + C b * X := by
      simp only [add_comp, mul_comp, C_comp, X_comp, s, map_sub, div_eq_mul_inv, map_mul]
      ring
    have hq : (C c + C d * X).comp (X - C (c / d)) = C d * X := by
      simp only [add_comp, mul_comp, C_comp, X_comp]
      have hh : d * (c / d) = c := mul_div_cancel₀ c hd0
      have HH := congrArg C hh
      simp only [map_mul] at HH
      linear_combination -HH
    have hS : ∀ n, IsPFPolynomial (S n) ∧ IsPFPolynomial (S (n + 1)) ∧
        Interl (S n) (S (n + 1)) := by
      apply ordered_shifted_pf hs hb hd S
      · simp only [S, h0, one_comp]
      · simp only [S, h1, hp]
      · intro n
        simp only [S, hrec, add_comp, mul_comp, hp, hq, mul_assoc]
    intro n
    have H := (hS n).1.splits.comp_X_add_C (c / d)
    simpa only [S, comp_assoc, sub_comp, X_comp, C_comp, add_sub_cancel_right, comp_X] using H

/-- A reciprocal path-matching root becomes a zero of any two-size ordered
recurrence on the corresponding quadratic pencil locus. -/
private theorem ordered_eval_eq_of_pencil_root
    {a b c d : ℝ} (R : ℕ → ℝ[X]) (h0 : R 0 = 1) (h1 : R 1 = C a + C b * X)
    (hrec : ∀ n, R (n + 2) = (C a + C b * X) * R (n + 1) + (C c + C d * X) * R n)
    {v : ℝ} (hv : 0 < v) {z : ℂ}
    (hz : ((C a + C b * X) ^ 2 + C v * (C c + C d * X)).eval₂ Complex.ofRealHom z = 0)
    (n : ℕ) :
    (R n).eval₂ Complex.ofRealHom z =
      ((C a + C b * X).eval₂ Complex.ofRealHom z) ^ n *
        (((pathMatchingPolynomial n).eval (-v⁻¹) : ℝ) : ℂ) := by
  let x := (C a + C b * X).eval₂ Complex.ofRealHom z
  let y := (C c + C d * X).eval₂ Complex.ofRealHom z
  have hxy : x ^ 2 + (v : ℂ) * y = 0 := by
    change ((C a + C b * X).eval₂ Complex.ofRealHom z) ^ 2 +
      (v : ℂ) * (C c + C d * X).eval₂ Complex.ofRealHom z = 0
    simpa only [eval₂_add, eval₂_pow, eval₂_mul, eval₂_C, Complex.ofRealHom_eq_coe] using hz
  have hy : y = x ^ 2 * (-(v : ℂ)⁻¹) := by
    have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    field_simp
    linear_combination hxy
  have hr (n : ℕ) : (R (n + 2)).eval₂ Complex.ofRealHom z =
      x * (R (n + 1)).eval₂ Complex.ofRealHom z + y * (R n).eval₂ Complex.ofRealHom z := by
    rw [hrec, eval₂_add, eval₂_mul, eval₂_mul]
  induction n using Nat.twoStepInduction with
  | zero => norm_num [h0, pathMatchingPolynomial]
  | one => norm_num [h1, pathMatchingPolynomial]
  | more n ih ih' =>
    rw [hr, ih, ih', pathMatchingPolynomial_add_two, eval_add, eval_mul, eval_X]
    change x * (x ^ (n + 1) * _) + y * (x ^ n * _) = x ^ (n + 2) * _
    rw [hy]
    push_cast
    simp only [pow_succ]
    ring

/-- Every affine ordered two-size recurrence splits for all indices exactly
when `ad ≥ bc`. No positivity or degree nondegeneracy is imposed on a row. -/
theorem ordered_recurrence_splits_iff {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (R : ℕ → ℝ[X]) (h0 : R 0 = 1) (h1 : R 1 = C a + C b * X)
    (hrec : ∀ n, R (n + 2) = (C a + C b * X) * R (n + 1) + (C c + C d * X) * R n) :
    (∀ n, (R n).Splits) ↔ b * c ≤ a * d := by
  constructor
  · intro hsplit
    by_contra hdet
    have hdet' : a * d < b * c := lt_of_not_ge hdet
    have hbpos : 0 < b := by
      by_contra h
      have hbzero : b = 0 := le_antisymm (le_of_not_gt h) hb
      rw [hbzero, zero_mul] at hdet'
      exact (not_lt_of_ge (mul_nonneg ha hd)) hdet'
    obtain ⟨M, hM, hbadM⟩ := exists_bad_affine_interval ha hb hd hdet'
    obtain ⟨m, hm⟩ := exists_nat_gt (2 / M)
    have hbound : 2 / (m + 2 : ℝ) < M := by
      rw [div_lt_iff₀ (by positivity)]
      have hcancel : 2 / M * M = 2 := div_mul_cancel₀ _ hM.ne'
      nlinarith
    obtain ⟨v, hv, hvm, hroot⟩ := path_exists_small_inverse_root m
    let F : ℝ[X] := (C a + C b * X) ^ 2 + C v * (C c + C d * X)
    have hbad : ¬ F.Splits := hbadM v hv (hvm.trans hbound)
    obtain ⟨z, hz, hzim⟩ : ∃ z : ℂ, (F.map Complex.ofRealHom).eval z = 0 ∧ z.im ≠ 0 := by
      by_contra! h
      exact hbad (Polynomial.splits_of_all_roots_real h)
    have hpos (n : ℕ) : 0 < (R n).eval 1 := by
      induction n using Nat.twoStepInduction with
      | zero => simp only [h0, eval_one, zero_lt_one]
      | one =>
        simp only [h1, eval_add, eval_mul, eval_C, eval_X, mul_one]
        linarith
      | more n ih ih' =>
        rw [hrec, eval_add, eval_mul, eval_mul]
        simp only [eval_add, eval_mul, eval_C, eval_X, mul_one]
        exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) ih') (by positivity)
    have hne : R (2 * (m + 2)) ≠ 0 := by
      intro he
      have h := hpos (2 * (m + 2))
      rw [he, eval_zero] at h
      exact (lt_irrefl 0) h
    have hzR : ((R (2 * (m + 2))).map Complex.ofRealHom).IsRoot z := by
      rw [Polynomial.IsRoot.def, Polynomial.eval_map]
      rw [ordered_eval_eq_of_pencil_root R h0 h1 hrec hv (by
        simpa only [F, eval_map] using hz), hroot, Complex.ofReal_zero, mul_zero]
    obtain ⟨r, hr⟩ := (hsplit (2 * (m + 2))).mem_range_of_isRoot hne hzR
    exact hzim (by rw [← hr]; exact Complex.ofReal_im r)
  · exact fun hdet => ordered_recurrence_splits_of_le hb hc hd hdet R h0 h1 hrec

/-- The canonical factorial-scaled ordered block rows for two affine sizes
are real-rooted in every rank exactly on the same boundary as exponential rows. -/
theorem orderedBlockRow_splits_two_size_iff {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (∀ n : ℕ, (orderedBlockRow (affineBlockWeights
      (PowerSeries.C a * PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 2)
      (PowerSeries.C b * PowerSeries.X + PowerSeries.C d * PowerSeries.X ^ 2)) n).Splits) ↔
      b * c ≤ a * d := by
  let w := affineBlockWeights
    (PowerSeries.C a * PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 2)
    (PowerSeries.C b * PowerSeries.X + PowerSeries.C d * PowerSeries.X ^ 2)
  let F : PowerSeries ℝ[X] := PowerSeries.invOfUnit
    (1 - PowerSeries.C (C a + C b * X) * PowerSeries.X -
      PowerSeries.C (C c + C d * X) * PowerSeries.X ^ 2) 1
  have hzero (v w : ℝ) : PowerSeries.constantCoeff
      (PowerSeries.C v * PowerSeries.X + PowerSeries.C w * PowerSeries.X ^ 2) = 0 := by
    simp only [map_add, map_mul, map_pow, PowerSeries.constantCoeff_X,
      zero_pow two_ne_zero, mul_zero, add_zero]
  have hseries : orderedBlockSeries w = F := by
    dsimp only [orderedBlockSeries, w, F]
    rw [blockWeightSeries_affineBlockWeights (hzero a c) (hzero b d)]
    congr 1
    simp only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
    ring
  obtain ⟨h0, h1, hrec⟩ := ordered_coeff_recurrence (C a + C b * X) (C c + C d * X)
  have H := ordered_recurrence_splits_iff ha hb hc hd (fun n => PowerSeries.coeff n F)
    h0 h1 hrec
  constructor
  · intro h
    apply H.mp
    intro n
    have hh := (h n).C_mul ((n.factorial : ℝ)⁻¹)
    change (C ((n.factorial : ℝ)⁻¹) * factorialCoeff (orderedBlockSeries w) n).Splits at hh
    rw [hseries, factorialCoeff, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ (by positivity), map_one, one_mul] at hh
    exact hh
  · intro hdet n
    change (factorialCoeff (orderedBlockSeries w) n).Splits
    rw [hseries, factorialCoeff]
    exact (H.mpr hdet n).C_mul (n.factorial : ℝ)

end RealRooted.ExponentialRows
