import RealRooted.ASWCubicCharacteristic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# A nonreal conjugate factor for the shift-one cubic characteristic polynomial

Let `a b c d : ℝ` and consider the real cubic `C d * X ^ 3 + C c * X ^ 2 +
C b * X + C a`.  When its coefficient discriminant `cubicDiscr` is negative,
the (complexified) shift-one characteristic polynomial
`aswCubicShiftOneCharPoly (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ)` factors as
`(X - C r) * (X - C z) * (X - C (conj z))` with `r` real and `z` genuinely
nonreal (`z.im ≠ 0`).

The hypothesis `a ≠ 0` is genuinely required: the discriminant of the
characteristic polynomial equals `a ^ 2` times the coefficient discriminant of
the original cubic (`cubicDiscr_aswCubicShiftOneCharPoly`).  If `a = 0` the
characteristic polynomial degenerates to `X ^ 2 * (X - C b)`, whose roots are
all real, even though the original discriminant may still be negative (e.g.
`a = 0, b = 1, c = 0, d = 1` gives original discriminant `-4`).  So without
`a ≠ 0` the statement is false.

The proof follows the route suggested by the discriminant criterion.  A real
cubic has a real root `r` (`cubic_exists_isRoot`); dividing out `X - C r`
leaves a real quadratic cofactor `C 1 * X ^ 2 + C s * X + C t` whose discriminant
`s ^ 2 - 4 t` is negative (because `cubicDiscr` of the characteristic polynomial
is `a ^ 2` times the negative original discriminant, and factors through the
cofactor discriminant via `cubicDiscr_eq_of_factor`).  The two complex roots of
that quadratic are the conjugate pair `z, conj z` with `z = ⟨-s/2, √(4t - s²)/2⟩`,
and the factorization follows from the Vieta identities
`r + z + conj z = b`, `r * z + z * conj z + conj z * r = a * c`, and
`r * z * conj z = a ^ 2 * d`, followed by a direct ring expansion.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- **Nonreal conjugate factorization from a negative discriminant.**  For real
`a b c d` with `a ≠ 0` and negative coefficient discriminant of the cubic
`C d * X ^ 3 + C c * X ^ 2 + C b * X + C a`, the complexified shift-one
characteristic polynomial factors as `(X - C r) * (X - C z) * (X - C (conj z))`
with `r` real and `z` nonreal.  The hypothesis `a ≠ 0` is required (see the
module docstring). -/
theorem aswCubicShiftOneCharPoly_complex_factor_of_cubicDiscr_neg
    (a b c d : ℝ) (ha : a ≠ 0)
    (hdisc : cubicDiscr (C d * X ^ 3 + C c * X ^ 2 + C b * X + C a) < 0) :
    ∃ (r : ℝ) (z : ℂ), z.im ≠ 0 ∧
      aswCubicShiftOneCharPoly (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) =
          (X - C (r : ℂ)) * (X - C z) * (X - C (starRingEnd ℂ z)) ∧
        (r : ℂ) + z + starRingEnd ℂ z = b ∧
        (r : ℂ) * z + (r : ℂ) * starRingEnd ℂ z + z * starRingEnd ℂ z = a * c ∧
        (r : ℂ) * z * starRingEnd ℂ z = a ^ 2 * d := by
  -- The characteristic polynomial has degree three, hence a real root `r`.
  have hform : aswCubicShiftOneCharPoly a b c d
      = C 1 * X ^ 3 + C (-b) * X ^ 2 + C (a * c) * X + C (-(a ^ 2 * d)) := by
    simp only [aswCubicShiftOneCharPoly, C_1, C_neg]
    ring
  have hdeg : (aswCubicShiftOneCharPoly a b c d).natDegree = 3 := by
    rw [hform]; exact natDegree_cubic one_ne_zero
  obtain ⟨r, hr⟩ := cubic_exists_isRoot hdeg
  have hr' : r ^ 3 - b * r ^ 2 + a * c * r - a ^ 2 * d = 0 := by
    have h := hr
    simp only [IsRoot.def, aswCubicShiftOneCharPoly, eval_sub, eval_add,
      eval_mul, eval_pow, eval_C, eval_X] at h
    linear_combination h
  -- Cofactor coefficients `s`, `t` and the root relation `r * t = a ^ 2 * d`.
  set s : ℝ := r - b with hs
  set t : ℝ := r * r - b * r + a * c with ht
  have hrt : r * t = a ^ 2 * d := by rw [ht]; linear_combination hr'
  set q : ℝ[X] := C 1 * X ^ 2 + C s * X + C t with hq
  have hqdeg : q.natDegree = 2 := by rw [hq]; exact natDegree_quadratic one_ne_zero
  -- Lifted (polynomial) versions of the defining relations.
  have hsC : (C s : ℝ[X]) = C r - C b := by rw [hs, C_sub]
  have htC : (C t : ℝ[X]) = C r * C r - C b * C r + C (a * c) := by
    rw [ht]; simp only [C_add, C_sub, C_mul]
  have hrtC : (C r : ℝ[X]) * C t = C (a ^ 2 * d) := by rw [← C_mul, hrt]
  -- `P = (X - C r) * q`.
  have hP : aswCubicShiftOneCharPoly a b c d = (X - C r) * q := by
    rw [hq]
    simp only [C_1, one_mul]
    change X ^ 3 - C b * X ^ 2 + C (a * c) * X - C (a ^ 2 * d)
        = (X - C r) * (X ^ 2 + C s * X + C t)
    linear_combination (-X ^ 2 + C r * X) * hsC + (-X) * htC + hrtC
  -- The cofactor discriminant `s ^ 2 - 4 t` is negative.
  have ha2 : (0 : ℝ) < a ^ 2 := (sq_nonneg a).lt_of_ne (Ne.symm (pow_ne_zero 2 ha))
  have hdiscP : cubicDiscr (aswCubicShiftOneCharPoly a b c d) < 0 := by
    rw [cubicDiscr_aswCubicShiftOneCharPoly]
    exact mul_neg_of_pos_of_neg ha2 hdisc
  have hkey : cubicDiscr (aswCubicShiftOneCharPoly a b c d)
      = (q.eval r) ^ 2 * discrim (q.coeff 2) (q.coeff 1) (q.coeff 0) := by
    rw [hP]; exact cubicDiscr_eq_of_factor hqdeg
  have hc2 : q.coeff 2 = 1 := by rw [hq]; simp [coeff_add, coeff_X_pow]
  have hc1 : q.coeff 1 = s := by rw [hq]; simp [coeff_add, coeff_X_pow]
  have hc0 : q.coeff 0 = t := by rw [hq]; simp [coeff_add, coeff_X_pow]
  have hprodneg : (q.eval r) ^ 2 * discrim (q.coeff 2) (q.coeff 1) (q.coeff 0) < 0 :=
    hkey ▸ hdiscP
  have hdd : discrim (q.coeff 2) (q.coeff 1) (q.coeff 0) < 0 := by
    rcases mul_neg_iff.mp hprodneg with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h (not_lt.mpr (sq_nonneg _))
  have hst : discrim (q.coeff 2) (q.coeff 1) (q.coeff 0) = s ^ 2 - 4 * t := by
    rw [hc2, hc1, hc0]; simp only [discrim]; ring
  have hsneg : s ^ 2 - 4 * t < 0 := hst ▸ hdd
  have hpos4 : (0 : ℝ) < 4 * t - s ^ 2 := by linarith
  -- The nonreal conjugate root pair.
  set w : ℝ := Real.sqrt (4 * t - s ^ 2) with hw
  have hw2 : w ^ 2 = 4 * t - s ^ 2 := by rw [hw]; exact Real.sq_sqrt (le_of_lt hpos4)
  have hwpos : (0 : ℝ) < w := by rw [hw]; exact Real.sqrt_pos.mpr hpos4
  set z : ℂ := ⟨-s / 2, w / 2⟩ with hz
  have hzre : z.re = -s / 2 := by rw [hz]
  have hzim : z.im = w / 2 := by rw [hz]
  have hzim_pos : (0 : ℝ) < z.im := by rw [hzim]; linarith
  -- Elementary symmetric relations for `z` and `conj z`.
  have h1 : z + starRingEnd ℂ z = -(s : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.conj_re, Complex.neg_re, Complex.ofReal_re, hzre]
      ring
    · simp only [Complex.add_im, Complex.conj_im, Complex.neg_im, Complex.ofReal_im, hzim]
      ring
  have h2 : z * starRingEnd ℂ z = (t : ℂ) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        hzre, hzim]
      linear_combination (1 / 4 : ℝ) * hw2
    · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_im,
        hzre, hzim]
      ring
  -- The three Vieta identities matching the characteristic polynomial.
  have V1 : (r : ℂ) + z + starRingEnd ℂ z = (b : ℂ) := by
    rw [add_assoc, h1, hs]; push_cast; ring
  have V2 : (r : ℂ) * z + z * starRingEnd ℂ z + starRingEnd ℂ z * (r : ℂ)
      = (a : ℂ) * (c : ℂ) := by
    have e : (r : ℂ) * z + z * starRingEnd ℂ z + starRingEnd ℂ z * (r : ℂ)
        = (r : ℂ) * (z + starRingEnd ℂ z) + z * starRingEnd ℂ z := by ring
    rw [e, h1, h2, hs, ht]; push_cast; ring
  have V3 : (r : ℂ) * z * starRingEnd ℂ z = (a : ℂ) ^ 2 * (d : ℂ) := by
    rw [mul_assoc, h2]
    have hrtc : (r : ℂ) * (t : ℂ) = (a : ℂ) ^ 2 * (d : ℂ) := by exact_mod_cast hrt
    rw [hrtc]
  -- Assemble the factorization.
  refine ⟨r, z, hzim_pos.ne', ?_, V1, ?_, V3⟩
  · change X ^ 3 - C (b : ℂ) * X ^ 2 + C ((a : ℂ) * (c : ℂ)) * X -
        C ((a : ℂ) ^ 2 * (d : ℂ)) =
      (X - C (r : ℂ)) * (X - C z) * (X - C (starRingEnd ℂ z))
    rw [show
      (X - C (r : ℂ)) * (X - C z) * (X - C (starRingEnd ℂ z)) =
        X ^ 3 - C ((r : ℂ) + z + starRingEnd ℂ z) * X ^ 2 +
          C ((r : ℂ) * z + z * starRingEnd ℂ z +
            starRingEnd ℂ z * (r : ℂ)) * X -
              C ((r : ℂ) * z * starRingEnd ℂ z) by
      simp only [C_add, C_mul]
      ring]
    rw [V1, V2, V3]
  · linear_combination V2

end RealRooted
