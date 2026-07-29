module

public import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Lemmas

public section

namespace Polynomial

/-- If `p` has strictly larger degree than `q`, then `p + C a * q` has the
same degree as `p`. -/
theorem natDegree_add_C_mul_eq_left_of_natDegree_lt
    {R : Type*} [Semiring R] {p q : R[X]} {a : R}
    (hdeg : q.natDegree < p.natDegree) :
    (p + C a * q).natDegree = p.natDegree :=
  natDegree_add_eq_left_of_natDegree_lt ((natDegree_C_mul_le a q).trans_lt hdeg)

/-- If `g` has strictly larger degree than `f`, then `f + C a * g` has the
same degree as `g`, provided `a ≠ 0`. -/
theorem natDegree_add_C_mul_of_natDegree_lt {R : Type*} [Semiring R] [NoZeroDivisors R]
    {f g : R[X]} {a : R} (ha : a ≠ 0) (hdeg : f.natDegree < g.natDegree) :
    (f + C a * g).natDegree = g.natDegree := by
  have hag_deg : (C a * g).natDegree = g.natDegree :=
    natDegree_C_mul (p := g) ha
  rw [natDegree_add_eq_right_of_natDegree_lt (by simpa [hag_deg] using hdeg),
    hag_deg]

/-- If `g` has strictly larger degree than `f`, then the leading coefficient of
`f + C a * g` is the scaled leading coefficient of `g`. -/
theorem leadingCoeff_add_C_mul_of_natDegree_lt {R : Type*} [Semiring R] [NoZeroDivisors R]
    {f g : R[X]} {a : R} (ha : a ≠ 0) (hdeg : f.natDegree < g.natDegree) :
    (f + C a * g).leadingCoeff = a * g.leadingCoeff := by
  have hsum_deg := natDegree_add_C_mul_of_natDegree_lt ha hdeg
  rw [leadingCoeff, hsum_deg, coeff_add, coeff_C_mul]
  rw [coeff_eq_zero_of_natDegree_lt hdeg, zero_add]
  rfl

/-- If `q` has degree at most that of `p`, and the coefficient of degree
`p.natDegree` in `p + C a * q` does not vanish, then the sum keeps the degree
of `p`. -/
theorem natDegree_add_C_mul_eq_left_of_natDegree_le_of_coeff_add_ne_zero
    {R : Type*} [Semiring R] {p q : R[X]} {a : R}
    (hdeg : q.natDegree ≤ p.natDegree)
    (hcoeff : p.leadingCoeff + a * q.coeff p.natDegree ≠ 0) :
    (p + C a * q).natDegree = p.natDegree := by
  apply le_antisymm
  · exact (natDegree_add_le _ _).trans <|
      max_le le_rfl ((natDegree_C_mul_le a q).trans hdeg)
  · apply le_natDegree_of_ne_zero
    intro hzero
    apply hcoeff
    have hsum_zero : p.coeff p.natDegree + a * q.coeff p.natDegree = 0 := by
      simpa [coeff_add, coeff_C_mul] using hzero
    exact hsum_zero

end Polynomial
