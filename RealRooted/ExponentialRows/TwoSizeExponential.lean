module

public import RealRooted.ExponentialRows.SubstitutionRows
public import RealRooted.Hermite.Homogeneous
import RealRooted.ExponentialRows.TwoSizePencil
import RealRooted.Mathlib.Algebra.Polynomial.Splits.Complex
import Mathlib.Tactic

/-!
# Exponential rows with two polynomial block weights

A nonnegative polynomial pair `p,q` gives split homogeneous Hermite rows if
`p² + λq` splits for every nonnegative `λ`. For affine block
weights, `ad ≥ bc` implies the required pencil condition, including all
parameter boundaries.

Source: unpublished manuscript, RealRooted #2415 and #2590, round two:
https://github.com/PerAlexandersson/RealRooted/issues/2415#issuecomment-7136509900.
The converse all-row criterion is not asserted here.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- A nonnegative polynomial pencil containing a nonzero square cannot vanish. -/
private theorem affine_square_pencil_ne_zero {p q : ℝ[X]} (hp : HasNonnegCoeffs p)
    (hq : HasNonnegCoeffs q) (hpne : p ≠ 0) {l : ℝ} (hl : 0 ≤ l) :
    p ^ 2 + C l * q ≠ 0 := by
  have hp1 : 0 < p.eval 1 := eval_pos_of_hasNonnegCoeffs hp hpne zero_lt_one
  have hq1 : 0 ≤ q.eval 1 := hq.eval_nonneg zero_le_one
  intro hz
  have h := congrArg (fun f : ℝ[X] => f.eval 1) hz
  simp only [eval_add, eval_pow, eval_mul, eval_C, eval_zero] at h
  nlinarith

/-- The nonnegative quadratic-pencil condition is sufficient for every
homogeneous Hermite row with polynomial block weights to split. -/
theorem hermiteHomogeneous_splits_of_nonneg_pencil {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hpencil : ∀ l : ℝ, 0 ≤ l → (p ^ 2 + C l * q).Splits) (n : ℕ) :
    (hermiteHomogeneous p q n).Splits := by
  by_cases hpne : p = 0
  · subst p
    have hqs : q.Splits := by
      simpa only [zero_pow two_ne_zero, map_one, one_mul, zero_add] using
        hpencil 1 zero_le_one
    induction n using Nat.twoStepInduction with
    | zero => simp only [hermiteHomogeneous_zero, Splits.one]
    | one => simp only [hermiteHomogeneous_one, Splits.zero]
    | more n ih _ =>
      rw [hermiteHomogeneous_add_two, zero_mul, zero_add]
      apply Splits.mul _ ih
      apply Splits.mul _ hqs
      exact Splits.of_natDegree_le_one (by compute_degree; norm_num)
  · apply Polynomial.splits_of_all_roots_real
    intro z hz
    rw [Polynomial.eval_map] at hz
    have hz' : hermiteHomogeneous (p.eval₂ Complex.ofRealHom z)
        (q.eval₂ Complex.ofRealHom z) n = 0 := by
      change (Polynomial.eval₂RingHom Complex.ofRealHom z) (hermiteHomogeneous p q n) = 0
        at hz
      rw [map_hermiteHomogeneous] at hz
      exact hz
    obtain ⟨l, hl, heq⟩ := exists_nonneg_sq_add_eq_zero_of_hermiteHomogeneous_eq_zero hz'
    have hroot : ((p ^ 2 + C l * q).map Complex.ofRealHom).IsRoot z := by
      simpa only [Polynomial.IsRoot.def, Polynomial.eval_map, eval₂_add,
        eval₂_pow, eval₂_mul, eval₂_C, Complex.ofRealHom_eq_coe] using heq
    obtain ⟨r, hr⟩ := (hpencil l hl).mem_range_of_isRoot
      (affine_square_pencil_ne_zero hp hq hpne hl) hroot
    rw [← hr]
    exact Complex.ofReal_im r

/-- Factorial coefficients of the two-size exponential are homogeneous
Hermite polynomials, with arbitrary polynomial activities. -/
theorem factorialCoeff_exp_two_size (p q : ℝ[X]) (n : ℕ) :
    factorialCoeff ((PowerSeries.exp ℝ[X]).subst
      (PowerSeries.C p * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2)) n =
      hermiteHomogeneous p q n := by
  let G : PowerSeries ℝ[X] := PowerSeries.C p * PowerSeries.X +
    PowerSeries.C q * PowerSeries.X ^ 2
  let H : PowerSeries ℝ[X] := (PowerSeries.exp ℝ[X]).subst G
  have hG : PowerSeries.constantCoeff G = 0 := by
    simp only [G, map_add, map_mul, map_pow, PowerSeries.constantCoeff_X,
      zero_pow two_ne_zero, mul_zero, add_zero]
  have h0 : factorialCoeff H 0 = 1 := by
    rw [factorialCoeff, Nat.factorial_zero, Nat.cast_one, map_one, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_eq,
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero hG]
    change (algebraMap ℝ[X] ℝ[X]) (PowerSeries.constantCoeff (PowerSeries.exp ℝ[X])) = 1
    rw [PowerSeries.constantCoeff_exp, map_one]
  have hder : PowerSeries.derivative H =
      PowerSeries.C p * H + PowerSeries.C (2 * q) * (PowerSeries.X * H) := by
    dsimp only [H]
    rw [PowerSeries.derivative_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' hG), PowerSeries.derivative_exp]
    have hDG : PowerSeries.derivative G =
        PowerSeries.C p + PowerSeries.C (2 * q) * PowerSeries.X := by
      simp only [G, map_add, PowerSeries.derivative.leibniz, PowerSeries.derivative_C,
        PowerSeries.derivative_X, PowerSeries.derivative_X_pow, Nat.cast_ofNat,
        Nat.reduceSub, pow_one, smul_eq_mul, map_mul, map_ofNat]
      ring
    rw [hDG]
    change H * _ = _
    ring
  have h1 : factorialCoeff H 1 = p := by
    have hh := congrArg (fun f => factorialCoeff f 0) hder
    rw [factorialCoeff_derivative, factorialCoeff_add, factorialCoeff_C_mul,
      factorialCoeff_C_mul, h0] at hh
    have hz : factorialCoeff (PowerSeries.X * H) 0 = 0 := by
      simp only [factorialCoeff, PowerSeries.coeff_zero_X_mul, mul_zero]
    simpa only [hz, mul_zero, add_zero, mul_one] using hh
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih ih' =>
    have hh := congrArg (fun f => factorialCoeff f (n + 1)) hder
    rw [factorialCoeff_derivative, factorialCoeff_add, factorialCoeff_C_mul,
      factorialCoeff_C_mul, factorialCoeff_X_mul, ih, ih'] at hh
    rw [hermiteHomogeneous_add_two, hh]
    simp only [map_add, map_one, map_natCast]
    push_cast
    ring

/-- The polynomial-weight two-size exponential has split rows whenever its
nonnegative quadratic pencils split. -/
theorem factorialCoeff_exp_two_size_splits {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hpencil : ∀ l : ℝ, 0 ≤ l → (p ^ 2 + C l * q).Splits) (n : ℕ) :
    (factorialCoeff ((PowerSeries.exp ℝ[X]).subst
      (PowerSeries.C p * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2)) n).Splits := by
  rw [factorialCoeff_exp_two_size]
  exact hermiteHomogeneous_splits_of_nonneg_pencil hp hq hpencil n

/-- The canonical affine-block insertion rows for sizes one and two are
homogeneous Hermite polynomials in the two activities. -/
theorem insertionRow_two_size_eq_hermite (a b c d : ℝ) (n : ℕ) :
    insertionRow (affineBlockWeights
      (PowerSeries.C a * PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 2)
      (PowerSeries.C b * PowerSeries.X + PowerSeries.C d * PowerSeries.X ^ 2)) n =
      hermiteHomogeneous (C a + C b * X) (C c + C d * X) n := by
  have hzero (v w : ℝ) : PowerSeries.constantCoeff
      (PowerSeries.C v * PowerSeries.X + PowerSeries.C w * PowerSeries.X ^ 2) = 0 := by
    simp only [map_add, map_mul, map_pow, PowerSeries.constantCoeff_X,
      zero_pow two_ne_zero, mul_zero, add_zero]
  rw [insertionRow_affineBlockWeights_eq_exponential (hzero a c) (hzero b d)]
  have hexp :
      (PowerSeries.C a * PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 2).map C +
        PowerSeries.C X *
          (PowerSeries.C b * PowerSeries.X + PowerSeries.C d * PowerSeries.X ^ 2).map C =
      PowerSeries.C (C a + C b * X) * PowerSeries.X +
        PowerSeries.C (C c + C d * X) * PowerSeries.X ^ 2 := by
    simp only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
    ring
  rw [hexp, factorialCoeff_exp_two_size]

/-- The exact boundary's sufficient direction for all exponential insertion
rows with two affine block weights. Every nonnegative parameter face is included. -/
theorem insertionRow_splits_two_size_of_le {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hdet : b * c ≤ a * d) (n : ℕ) :
    (insertionRow (affineBlockWeights
      (PowerSeries.C a * PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 2)
      (PowerSeries.C b * PowerSeries.X + PowerSeries.C d * PowerSeries.X ^ 2)) n).Splits := by
  rw [insertionRow_two_size_eq_hermite]
  apply hermiteHomogeneous_splits_of_nonneg_pencil
    ((hasNonnegCoeffs_C ha).add (hasNonnegCoeffs_C_mul hb hasNonnegCoeffs_X))
    ((hasNonnegCoeffs_C hc).add (hasNonnegCoeffs_C_mul hd hasNonnegCoeffs_X))
  exact fun _ hl => splits_affine_pencil_of_le hb hl hdet

end RealRooted.ExponentialRows
