module

public import Mathlib.Algebra.Polynomial.Derivative

public section

namespace Polynomial
variable {R : Type*} [CommRing R] [IsAddTorsionFree R] {p : R[X]}

/-- The next coefficient of the derivative is `(n - 1)` times the next
coefficient of the original polynomial, for degree `n ≥ 2`. -/
lemma nextCoeff_derivative_of_two_le_natDegree (p : R[X])
    (htwo : 2 ≤ p.natDegree) :
    p.derivative.nextCoeff = (p.natDegree - 1 : R) * p.nextCoeff := by
  have hpder_deg : p.derivative.natDegree = p.natDegree - 1 :=
    p.natDegree_derivative
  rw [Polynomial.nextCoeff_of_natDegree_pos, hpder_deg]
  · rw [Polynomial.nextCoeff_of_natDegree_pos (by lia)]
    rw [coeff_derivative]
    have hidx : p.natDegree - 1 - 1 + 1 = p.natDegree - 1 := by lia
    have hcast : ((p.natDegree - 1 - 1 : ℕ) : R) + 1 =
        (p.natDegree - 1 : R) := by
      rw [Nat.cast_sub (by show 1 ≤ p.natDegree - 1; lia),
        Nat.cast_sub (by show 1 ≤ p.natDegree; lia)]
      ring
    grind
  · grind

variable {S : Type*} [Field S] [LinearOrder S] [IsStrictOrderedRing S]

/-- A nonresonant first-order Euler equation inherits the degree bound of its
remainder.  The coarse bound rules out the homogeneous solution of degree
`a`. -/
theorem natDegree_le_of_C_mul_eq_X_add_C_mul_derivative_add
    (p q : S[X]) (a b d N : ℕ)
    (hp : p ≠ 0) (hcoarse : p.natDegree ≤ N) (hN : N < a)
    (hq : q.natDegree ≤ d)
    (hrec : C (a : S) * p = (X + C (b : S)) * p.derivative + q) :
    p.natDegree ≤ d := by
  by_contra hdegree
  have hdlt : d < p.natDegree := by lia
  let k := p.natDegree
  let j := k - 1
  have hkpos : 0 < k := by dsimp [k]; lia
  have hkj : k = j + 1 := by dsimp [j]; lia
  have hqzero : q.coeff (j + 1) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [← hkj]
    exact lt_of_le_of_lt hq (by simpa [k] using hdlt)
  have hnext : p.coeff (j + 2) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    change k < j + 2
    lia
  have htop : p.coeff k ≠ 0 := by
    change p.leadingCoeff ≠ 0
    exact leadingCoeff_ne_zero.mpr hp
  rw [show (X + C (b : S)) * p.derivative =
      X * p.derivative + C (b : S) * p.derivative by ring] at hrec
  have hcoeff := congrArg (fun r : S[X] => r.coeff (j + 1)) hrec
  rw [coeff_C_mul, coeff_add, coeff_add, coeff_X_mul, coeff_C_mul,
    coeff_derivative, coeff_derivative, hnext, hqzero] at hcoeff
  simp only [add_zero] at hcoeff
  have hfactor : ((a : S) - k) * p.coeff k = 0 := by
    rw [hkj]
    push_cast
    linarith
  rcases mul_eq_zero.mp hfactor with hzero | hzero
  · have hklt : k < a := lt_of_le_of_lt hcoarse hN
    have hkltS : (k : S) < (a : S) := by exact_mod_cast hklt
    exact (ne_of_gt (sub_pos.mpr hkltS)) hzero
  · exact htop hzero

end Polynomial
