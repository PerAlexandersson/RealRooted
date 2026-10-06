import RealRooted.Hadamard.Product
import RealRooted.IteratedDerivativeShift
import RealRooted.ObreschkoffConverse
import RealRooted.WeightedSum

/-!
# Garloff--Wagner factorial and differential algebra

The factorial Hadamard product (Schur's factorial product) and the operators
`L = divFactorial`, `D = derivative`, and `J = antiderivative` used in the
direct Garloff--Wagner proof.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The factorial Hadamard product, also called Schur's factorial product or
Garloff--Wagner's normalized Schur product: `factorialHadamardProduct p q` has
`k`th coefficient `k! * p_k * q_k`. -/
def factorialHadamardProduct (p q : ℝ[X]) : ℝ[X] :=
  diagonalOperator (fun k => (Nat.factorial k : ℝ) * q.coeff k) p

@[simp] theorem coeff_factorialHadamardProduct (p q : ℝ[X]) (k : ℕ) :
    (factorialHadamardProduct p q).coeff k =
      (Nat.factorial k : ℝ) * p.coeff k * q.coeff k := by
  rw [factorialHadamardProduct, coeff_diagonalOperator]
  ring

theorem factorialHadamardProduct_comm (p q : ℝ[X]) :
    factorialHadamardProduct p q = factorialHadamardProduct q p := by
  ext k
  simp [mul_comm, mul_left_comm]

theorem factorialHadamardProduct_assoc (p q r : ℝ[X]) :
    factorialHadamardProduct (factorialHadamardProduct p q) r =
      factorialHadamardProduct p (factorialHadamardProduct q r) := by
  ext k
  simp [mul_left_comm, mul_assoc]

@[simp] theorem factorialHadamardProduct_zero_left (p : ℝ[X]) :
    factorialHadamardProduct 0 p = 0 := by
  ext k
  simp

@[simp] theorem factorialHadamardProduct_zero_right (p : ℝ[X]) :
    factorialHadamardProduct p 0 = 0 := by
  ext k
  simp

theorem factorialHadamardProduct_add_left (p q r : ℝ[X]) :
    factorialHadamardProduct (p + q) r =
      factorialHadamardProduct p r + factorialHadamardProduct q r := by
  ext k
  simp [mul_add, add_mul]

theorem factorialHadamardProduct_add_right (p q r : ℝ[X]) :
    factorialHadamardProduct p (q + r) =
      factorialHadamardProduct p q + factorialHadamardProduct p r := by
  rw [factorialHadamardProduct_comm p (q + r), factorialHadamardProduct_add_left q r p,
    factorialHadamardProduct_comm q p, factorialHadamardProduct_comm r p]

theorem factorialHadamardProduct_C_mul_left (a : ℝ) (p q : ℝ[X]) :
    factorialHadamardProduct (C a * p) q = C a * factorialHadamardProduct p q := by
  ext k
  simp [mul_comm, mul_left_comm]

theorem factorialHadamardProduct_C_mul_right (a : ℝ) (p q : ℝ[X]) :
    factorialHadamardProduct p (C a * q) = C a * factorialHadamardProduct p q := by
  rw [factorialHadamardProduct_comm p (C a * q), factorialHadamardProduct_C_mul_left,
    factorialHadamardProduct_comm q p]

theorem HasNonnegCoeffs.factorialHadamardProduct {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (factorialHadamardProduct p q) := by
  intro k
  rw [coeff_factorialHadamardProduct]
  exact mul_nonneg (mul_nonneg (by positivity) (hp k)) (hq k)

theorem natDegree_factorialHadamardProduct_le_left (p q : ℝ[X]) :
    (factorialHadamardProduct p q).natDegree ≤ p.natDegree := by
  simpa [factorialHadamardProduct] using
    natDegree_diagonalOperator_le (fun k => (Nat.factorial k : ℝ) * q.coeff k) p

theorem natDegree_factorialHadamardProduct_le_right (p q : ℝ[X]) :
    (factorialHadamardProduct p q).natDegree ≤ q.natDegree := by
  rw [factorialHadamardProduct_comm]
  exact natDegree_factorialHadamardProduct_le_left q p

/-- Garloff--Wagner's `L` operator: divide the `k`th coefficient by `k!`. -/
def divFactorial (p : ℝ[X]) : ℝ[X] :=
  diagonalOperator (fun k => ((Nat.factorial k : ℝ)⁻¹)) p

@[deprecated (since := "2026-10-06")]
alias gwL := divFactorial

@[simp] theorem coeff_divFactorial (p : ℝ[X]) (k : ℕ) :
    (divFactorial p).coeff k = (Nat.factorial k : ℝ)⁻¹ * p.coeff k := by
  rw [divFactorial, coeff_diagonalOperator]

@[deprecated (since := "2026-10-06")]
alias coeff_gwL := coeff_divFactorial

theorem divFactorial_zero :
    divFactorial (0 : ℝ[X]) = 0 := by
  ext k
  simp

theorem divFactorial_add (p q : ℝ[X]) :
    divFactorial (p + q) = divFactorial p + divFactorial q := by
  simpa [divFactorial] using diagonalOperator_add (fun k => ((Nat.factorial k : ℝ)⁻¹)) p q

theorem divFactorial_sub (p q : ℝ[X]) :
    divFactorial (p - q) = divFactorial p - divFactorial q := by
  simpa [divFactorial] using diagonalOperator_sub (fun k => ((Nat.factorial k : ℝ)⁻¹)) p q

theorem divFactorial_C_mul (a : ℝ) (p : ℝ[X]) :
    divFactorial (C a * p) = C a * divFactorial p := by
  simpa [divFactorial] using
    diagonalOperator_C_mul (fun k => ((Nat.factorial k : ℝ)⁻¹)) a p

@[simp] theorem divFactorial_C (a : ℝ) :
    divFactorial (C a) = C a := by
  ext k
  cases k <;> simp

theorem divFactorial_eq_zero_iff (p : ℝ[X]) :
    divFactorial p = 0 ↔ p = 0 := by
  constructor
  · intro h
    ext k
    have hk := congrArg (fun q : ℝ[X] => q.coeff k) h
    rw [coeff_divFactorial] at hk
    have hfact : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp hk).resolve_left (inv_ne_zero hfact)
  · intro h
    rw [h, divFactorial_zero]

theorem divFactorial_ne_zero_iff (p : ℝ[X]) :
    divFactorial p ≠ 0 ↔ p ≠ 0 := by
  rw [ne_eq, ne_eq, divFactorial_eq_zero_iff]

@[deprecated (since := "2026-10-06")]
alias gwL_ne_zero_iff := divFactorial_ne_zero_iff

theorem natDegree_divFactorial_le (p : ℝ[X]) :
    (divFactorial p).natDegree ≤ p.natDegree := by
  simpa [divFactorial] using
    natDegree_diagonalOperator_le (fun k => ((Nat.factorial k : ℝ)⁻¹)) p

theorem natDegree_divFactorial {p : ℝ[X]} (hp : p ≠ 0) :
    (divFactorial p).natDegree = p.natDegree := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_divFactorial_le p) ?_
  rw [coeff_divFactorial, coeff_natDegree]
  exact mul_ne_zero (inv_ne_zero (by positivity)) (leadingCoeff_ne_zero.mpr hp)

theorem leadingCoeff_divFactorial (p : ℝ[X]) :
    (divFactorial p).leadingCoeff =
      (Nat.factorial p.natDegree : ℝ)⁻¹ * p.leadingCoeff := by
  by_cases hp : p = 0
  · simp [hp, divFactorial_zero]
  · rw [leadingCoeff, natDegree_divFactorial hp, coeff_divFactorial, leadingCoeff]

theorem HasPosLeadingCoeff.divFactorial {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (divFactorial p) := by
  rw [HasPosLeadingCoeff, leadingCoeff_divFactorial]
  rw [HasPosLeadingCoeff] at hp
  exact mul_pos (inv_pos.mpr (by positivity)) hp

theorem HasNonnegCoeffs.divFactorial {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (divFactorial p) := by
  simpa [RealRooted.divFactorial] using
    hp.diagonalOperator (fun k => show 0 ≤ (Nat.factorial k : ℝ)⁻¹ by positivity)

/-- Garloff--Wagner's `J` operator: integrate with zero constant term. -/
def antiderivative (p : ℝ[X]) : ℝ[X] :=
  X * diagonalOperator (fun n => ((n + 1 : ℝ)⁻¹)) p

@[simp] theorem coeff_antiderivative_zero (p : ℝ[X]) :
    (antiderivative p).coeff 0 = 0 := by
  simp [antiderivative]

@[simp] theorem coeff_antiderivative_succ (p : ℝ[X]) (n : ℕ) :
    (antiderivative p).coeff (n + 1) = (n + 1 : ℝ)⁻¹ * p.coeff n := by
  simp [antiderivative]

@[deprecated (since := "2026-10-06")]
alias coeff_gwJ_succ := coeff_antiderivative_succ

@[simp] theorem antiderivative_zero :
    antiderivative (0 : ℝ[X]) = 0 := by
  ext n
  cases n <;> simp

theorem antiderivative_add (p q : ℝ[X]) :
    antiderivative (p + q) = antiderivative p + antiderivative q := by
  ext n
  cases n <;> simp [mul_add]

theorem antiderivative_sub (p q : ℝ[X]) :
    antiderivative (p - q) = antiderivative p - antiderivative q := by
  ext n
  cases n <;> simp [mul_sub]

theorem antiderivative_C_mul (a : ℝ) (p : ℝ[X]) :
    antiderivative (C a * p) = C a * antiderivative p := by
  ext n
  cases n <;> simp [mul_comm, mul_left_comm]

theorem derivative_antiderivative (p : ℝ[X]) :
    derivative (antiderivative p) = p := by
  ext n
  rw [coeff_derivative, coeff_antiderivative_succ]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hn]

theorem antiderivative_derivative (p : ℝ[X]) :
    antiderivative (derivative p) = p - C (p.coeff 0) := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [coeff_antiderivative_succ, coeff_derivative]
      simp
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hn]

theorem antiderivative_eq_zero_iff (p : ℝ[X]) :
    antiderivative p = 0 ↔ p = 0 := by
  constructor
  · intro h
    calc
      p = derivative (antiderivative p) := (derivative_antiderivative p).symm
      _ = 0 := by rw [h, derivative_zero]
  · intro h
    rw [h, antiderivative_zero]

theorem antiderivative_ne_zero_iff (p : ℝ[X]) :
    antiderivative p ≠ 0 ↔ p ≠ 0 := by
  rw [ne_eq, ne_eq, antiderivative_eq_zero_iff]

private theorem natDegree_diagonalOperator_inv_succ {p : ℝ[X]} (hp : p ≠ 0) :
    (diagonalOperator (fun n => ((n + 1 : ℝ)⁻¹)) p).natDegree =
      p.natDegree := by
  refine natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_diagonalOperator_le (fun n => ((n + 1 : ℝ)⁻¹)) p) ?_
  rw [coeff_diagonalOperator, coeff_natDegree]
  exact mul_ne_zero (inv_ne_zero (by positivity)) (leadingCoeff_ne_zero.mpr hp)

theorem natDegree_antiderivative {p : ℝ[X]} (hp : p ≠ 0) :
    (antiderivative p).natDegree = p.natDegree + 1 := by
  rw [antiderivative]
  have hcore :
      diagonalOperator (fun n => ((n + 1 : ℝ)⁻¹)) p ≠ 0 := by
    intro hcore
    have hJ : antiderivative p = 0 := by simp [antiderivative, hcore]
    exact hp ((antiderivative_eq_zero_iff p).mp hJ)
  rw [natDegree_X_mul hcore, natDegree_diagonalOperator_inv_succ hp]

theorem leadingCoeff_antiderivative {p : ℝ[X]} (hp : p ≠ 0) :
    (antiderivative p).leadingCoeff = (p.natDegree + 1 : ℝ)⁻¹ * p.leadingCoeff := by
  rw [leadingCoeff, natDegree_antiderivative hp, coeff_antiderivative_succ, leadingCoeff]

theorem HasPosLeadingCoeff.antiderivative {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (antiderivative p) := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, HasPosLeadingCoeff, leadingCoeff_zero] at hp
    linarith
  rw [HasPosLeadingCoeff, leadingCoeff_antiderivative hp0]
  rw [HasPosLeadingCoeff] at hp
  exact mul_pos (inv_pos.mpr (by positivity)) hp

theorem HasNonnegCoeffs.antiderivative {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (antiderivative p) := by
  intro n
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [coeff_antiderivative_succ]
      exact mul_nonneg (by positivity) (hp n)

/-- Lemma 10(e): applying `L` after multiplication by `X` is `J ∘ L`. -/
theorem divFactorial_X_mul (p : ℝ[X]) :
    divFactorial (X * p) = antiderivative (divFactorial p) := by
  ext n
  cases n with
  | zero =>
      simp [divFactorial]
  | succ n =>
      rw [coeff_divFactorial, coeff_X_mul, coeff_antiderivative_succ, coeff_divFactorial]
      rw [Nat.factorial_succ]
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      have hfact : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      field_simp [hn, hfact]
      norm_num only [Nat.cast_add, Nat.cast_mul]
      ring_nf

/-- Lemma 10(f): shifting the right input becomes differentiating the left input. -/
theorem factorialHadamardProduct_X_mul_right (f g : ℝ[X]) :
    factorialHadamardProduct f (X * g) = X * factorialHadamardProduct (derivative f) g := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [coeff_factorialHadamardProduct, coeff_X_mul, coeff_X_mul, coeff_factorialHadamardProduct,
        coeff_derivative]
      rw [Nat.factorial_succ]
      norm_num only [Nat.cast_add, Nat.cast_mul]
      ring_nf

/-- Multiplying the right Schur-product input by a real linear factor gives
the recurrence used in Garloff--Wagner, Theorem 12. -/
theorem factorialHadamardProduct_X_sub_C_mul_right (f p : ℝ[X]) (u : ℝ) :
    factorialHadamardProduct f ((X - C u) * p) =
      X * factorialHadamardProduct (derivative f) p - C u * factorialHadamardProduct f p := by
  ext n
  cases n with
  | zero =>
      simp [coeff_factorialHadamardProduct]
      ring
  | succ n =>
      rw [coeff_factorialHadamardProduct, coeff_X_sub_C_mul, coeff_sub, coeff_X_mul,
        coeff_C_mul, coeff_factorialHadamardProduct, coeff_derivative,
        coeff_factorialHadamardProduct]
      rw [ite_eq_right (Nat.succ_ne_zero n), Nat.succ_sub_one, Nat.factorial_succ]
      norm_num only [Nat.cast_add, Nat.cast_mul]
      ring_nf

/-- Left-input version of `factorialHadamardProduct_X_sub_C_mul_right`, by
commutativity. -/
theorem factorialHadamardProduct_X_sub_C_mul_left (f p : ℝ[X]) (u : ℝ) :
    factorialHadamardProduct ((X - C u) * f) p =
      X * factorialHadamardProduct (derivative p) f - C u * factorialHadamardProduct f p := by
  rw [factorialHadamardProduct_comm ((X - C u) * f) p,
    factorialHadamardProduct_X_sub_C_mul_right, factorialHadamardProduct_comm p f]

/-- Lemma 10(g): `D` distributes over the Garloff--Wagner Schur product. -/
theorem derivative_factorialHadamardProduct (f g : ℝ[X]) :
    derivative (factorialHadamardProduct f g) =
      factorialHadamardProduct (derivative f) (derivative g) := by
  ext n
  rw [coeff_derivative, coeff_factorialHadamardProduct, coeff_factorialHadamardProduct,
    coeff_derivative, coeff_derivative]
  rw [Nat.factorial_succ]
  norm_num only [Nat.cast_add, Nat.cast_mul]
  ring_nf

/-- Lemma 10(h): `J` distributes over the Garloff--Wagner Schur product. -/
theorem antiderivative_factorialHadamardProduct (f g : ℝ[X]) :
    antiderivative (factorialHadamardProduct f g) =
      factorialHadamardProduct (antiderivative f) (antiderivative g) := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [coeff_antiderivative_succ, coeff_factorialHadamardProduct, coeff_factorialHadamardProduct,
        coeff_antiderivative_succ, coeff_antiderivative_succ]
      rw [Nat.factorial_succ]
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hn]
      norm_num only [Nat.cast_add, Nat.cast_mul]
      ring_nf

/-- Lemma 10(i), first form: `L (f ( g) = f ⊙ g`. -/
theorem divFactorial_factorialHadamardProduct (p q : ℝ[X]) :
    divFactorial (factorialHadamardProduct p q) = hadamardProduct p q := by
  ext k
  rw [coeff_divFactorial, coeff_factorialHadamardProduct, coeff_hadamardProduct]
  have hfact : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hfact]

/-- Lemma 10(i), second form: `L f ( g = f ⊙ g`. -/
theorem factorialHadamardProduct_divFactorial_left (p q : ℝ[X]) :
    factorialHadamardProduct (divFactorial p) q = hadamardProduct p q := by
  ext k
  rw [coeff_factorialHadamardProduct, coeff_divFactorial, coeff_hadamardProduct]
  have hfact : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hfact]

/-- Lemma 10(i), third form: `f ( L g = f ⊙ g`. -/
theorem factorialHadamardProduct_divFactorial_right (p q : ℝ[X]) :
    factorialHadamardProduct p (divFactorial q) = hadamardProduct p q := by
  rw [factorialHadamardProduct_comm p (divFactorial q),
    factorialHadamardProduct_divFactorial_left q p, hadamardProduct_comm q p]

end RealRooted
