import RealRooted.DegreeDropReversal
import RealRooted.GarloffWagner

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Falling-factorial multiplier steps for array-counting polynomials

Let `t (n, k)` count the `n × 3` arrays over `{0,1,2}` with all row sums `3`,
all column sums `n`, and exactly `k` rows of the weighted type, so that the
row polynomial is `p n = ∑ k, t (n, k) * X ^ k`.  Writing `(n)_k` for the
falling factorial, the normalized polynomial is
`D n = ∑ k, (t (n, k) / (n)_k ^ 3) * X ^ k`.

The argument recovering `p n` from `D n` multiplies the `k`-th coefficient by
`(n)_k` three times.  Since `(n)_k = k ! * n.choose k`, each such step is
exactly a Garloff--Wagner factorial-normalized Schur product against
`(X + 1) ^ n`, so it preserves the Polya-frequency cone by
`gwSchurProductPF`.  That is the content of `IsPFPolynomial.fallingSchur`
and its threefold iterate below.

Nothing here assumes the deep input of that argument, namely that `D n` itself
is a Polya-frequency polynomial (which comes from total nonnegativity of an
associated matrix together with the Gantmacher--Krein eigenvalue theorem).
That input is carried as an explicit hypothesis, so every statement in this
file is unconditional about what it proves.
-/

/-- One falling-factorial multiplier step, realized as a Garloff--Wagner
Schur product against `(X + 1) ^ n`.  Its effect on coefficients is
multiplication by `k ! * n.choose k`, which is the falling factorial `(n)_k`. -/
def fallingSchur (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  gwSchurProduct p ((X + 1 : ℝ[X]) ^ n)

@[simp] theorem coeff_fallingSchur (n : ℕ) (p : ℝ[X]) (k : ℕ) :
    (fallingSchur n p).coeff k
      = (Nat.factorial k : ℝ) * (n.choose k : ℝ) * p.coeff k := by
  rw [fallingSchur, coeff_gwSchurProduct, coeff_X_add_one_pow]
  ring

/-- The coefficient multiplier of `fallingSchur n` is the falling factorial. -/
theorem coeff_fallingSchur_eq_descFactorial (n : ℕ) (p : ℝ[X]) (k : ℕ) :
    (fallingSchur n p).coeff k = (n.descFactorial k : ℝ) * p.coeff k := by
  rw [coeff_fallingSchur, ← Nat.cast_mul, Nat.descFactorial_eq_factorial_mul_choose]

@[simp] theorem fallingSchur_zero_poly (n : ℕ) : fallingSchur n (0 : ℝ[X]) = 0 := by
  simp [fallingSchur]

theorem natDegree_fallingSchur_le (n : ℕ) (p : ℝ[X]) :
    (fallingSchur n p).natDegree ≤ p.natDegree :=
  natDegree_gwSchurProduct_le_left _ _

/-- `(X + 1) ^ n` is a Polya-frequency polynomial. -/
theorem isPFPolynomial_X_add_one_pow (n : ℕ) :
    IsPFPolynomial ((X + 1 : ℝ[X]) ^ n) := by
  have h : IsPFPolynomial (X + C (1 : ℝ)) := isPFPolynomial_X_add_C zero_le_one
  simpa using h.pow n

/-- A falling-factorial multiplier step preserves the Polya-frequency cone.
This is Section 5 of the array-polynomial argument, for a single step. -/
theorem isPFPolynomial_fallingSchur {p : ℝ[X]} (hp : IsPFPolynomial p) (n : ℕ) :
    IsPFPolynomial (fallingSchur n p) :=
  gwSchurProductPF hp (isPFPolynomial_X_add_one_pow n)

/-- Iterating the falling-factorial step preserves the Polya-frequency cone. -/
theorem isPFPolynomial_fallingSchur_iterate {p : ℝ[X]} (hp : IsPFPolynomial p)
    (n : ℕ) : ∀ m : ℕ, IsPFPolynomial ((fallingSchur n)^[m] p)
  | 0 => by simpa using hp
  | m + 1 => by
      rw [Function.iterate_succ_apply]
      exact isPFPolynomial_fallingSchur_iterate (isPFPolynomial_fallingSchur hp n) n m

/-- The `k`-th coefficient after `m` falling-factorial steps. -/
theorem coeff_fallingSchur_iterate (n : ℕ) (p : ℝ[X]) (k : ℕ) :
    ∀ m : ℕ, ((fallingSchur n)^[m] p).coeff k
      = (n.descFactorial k : ℝ) ^ m * p.coeff k
  | 0 => by simp
  | m + 1 => by
      rw [Function.iterate_succ_apply', coeff_fallingSchur_eq_descFactorial,
        coeff_fallingSchur_iterate n p k m]
      ring

/-- **The multiplier step of the array-polynomial argument.**  If the
normalized polynomial `D` is Polya-frequency and the row polynomial `p` is
obtained from it by multiplying the `k`-th coefficient by `(n)_k ^ 3`, then `p`
is Polya-frequency; in particular `p` is real-rooted with only nonpositive
roots. -/
theorem isPFPolynomial_of_coeff_eq_descFactorial_pow_three
    {D p : ℝ[X]} {n : ℕ} (hD : IsPFPolynomial D)
    (hp : ∀ k : ℕ, p.coeff k = (n.descFactorial k : ℝ) ^ 3 * D.coeff k) :
    IsPFPolynomial p := by
  have hEq : p = (fallingSchur n)^[3] D := by
    ext k
    rw [hp k, coeff_fallingSchur_iterate]
  rw [hEq]
  exact isPFPolynomial_fallingSchur_iterate hD n 3

/-- The same conclusion in the form used downstream: the row polynomial splits
once the normalized polynomial is Polya-frequency and nonzero. -/
theorem splits_of_coeff_eq_descFactorial_pow_three
    {D p : ℝ[X]} {n : ℕ} (hD : IsPFPolynomial D) (hp0 : p ≠ 0)
    (hp : ∀ k : ℕ, p.coeff k = (n.descFactorial k : ℝ) ^ 3 * D.coeff k) :
    p.Splits :=
  ((isPFPolynomial_of_coeff_eq_descFactorial_pow_three hD hp).2.1).resolve_left hp0

/-- **Transfer to the array row.**  The array row polynomial is the degree-`n`
reflection of the weighted row polynomial, `P n = reflect n (p n)`; concretely
`P n (t) = t ^ n * p n (1 / t)`.  Reflection preserves splitting, so once the
row polynomial is Polya-frequency the array row splits: its roots are the
reciprocals of the roots of `p n`, together with `0` to multiplicity
`n - (p n).natDegree`. -/
theorem splits_reflect_of_isPFPolynomial {p : ℝ[X]} {n : ℕ}
    (hp : IsPFPolynomial p) (hp0 : p ≠ 0) (hn : p.natDegree ≤ n) :
    (reflect n p).Splits := by
  rw [DegreeDropReversal.reflect_eq_X_pow_mul_reverse p hn]
  exact DegreeDropReversal.splits_X_pow_mul_reverse (hp.2.1.resolve_left hp0) n

/-- **The array-polynomial conclusion, modulo the normalized input.**  If the
normalized polynomial `D` is Polya-frequency and the array row `P` is the
degree-`n` reflection of a polynomial whose coefficients are those of `D`
scaled by `(n)_k ^ 3`, then `P` splits.  This is the whole chain of Sections 3
to 5 of the argument, with the Gantmacher--Krein input `hD` as a hypothesis. -/
theorem splits_reflect_of_coeff_eq_descFactorial_pow_three
    {D p P : ℝ[X]} {n : ℕ} (hD : IsPFPolynomial D) (hp0 : p ≠ 0)
    (hn : p.natDegree ≤ n)
    (hp : ∀ k : ℕ, p.coeff k = (n.descFactorial k : ℝ) ^ 3 * D.coeff k)
    (hP : P = reflect n p) :
    P.Splits := by
  rw [hP]
  exact splits_reflect_of_isPFPolynomial
    (isPFPolynomial_of_coeff_eq_descFactorial_pow_three hD hp) hp0 hn

end RealRooted
