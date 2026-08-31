import RealRooted.HadamardProduct
import RealRooted.IteratedDerivativeShift
import RealRooted.ObreschkoffConverse
import RealRooted.WeightedSum

/-!
# Garloff--Wagner factorial and differential algebra

The normalized Schur product and the `L`, `D`, and `J` operators used in the
direct Garloff--Wagner proof.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Garloff--Wagner's factorial-normalized Schur product:
`gwSchurProduct p q` has `k`th coefficient `k! * p_k * q_k`. -/
def gwSchurProduct (p q : ℝ[X]) : ℝ[X] :=
  diagonalOperator (fun k => (Nat.factorial k : ℝ) * q.coeff k) p

@[simp] theorem coeff_gwSchurProduct (p q : ℝ[X]) (k : ℕ) :
    (gwSchurProduct p q).coeff k =
      (Nat.factorial k : ℝ) * p.coeff k * q.coeff k := by
  rw [gwSchurProduct, coeff_diagonalOperator]
  ring

theorem gwSchurProduct_comm (p q : ℝ[X]) :
    gwSchurProduct p q = gwSchurProduct q p := by
  ext k
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem gwSchurProduct_assoc (p q r : ℝ[X]) :
    gwSchurProduct (gwSchurProduct p q) r =
      gwSchurProduct p (gwSchurProduct q r) := by
  ext k
  simp [mul_left_comm, mul_assoc]

@[simp] theorem gwSchurProduct_zero_left (p : ℝ[X]) :
    gwSchurProduct 0 p = 0 := by
  ext k
  simp

@[simp] theorem gwSchurProduct_zero_right (p : ℝ[X]) :
    gwSchurProduct p 0 = 0 := by
  ext k
  simp

theorem gwSchurProduct_add_left (p q r : ℝ[X]) :
    gwSchurProduct (p + q) r =
      gwSchurProduct p r + gwSchurProduct q r := by
  ext k
  simp [mul_add, add_mul]

theorem gwSchurProduct_add_right (p q r : ℝ[X]) :
    gwSchurProduct p (q + r) =
      gwSchurProduct p q + gwSchurProduct p r := by
  rw [gwSchurProduct_comm p (q + r), gwSchurProduct_add_left q r p,
    gwSchurProduct_comm q p, gwSchurProduct_comm r p]

theorem gwSchurProduct_C_mul_left (a : ℝ) (p q : ℝ[X]) :
    gwSchurProduct (C a * p) q = C a * gwSchurProduct p q := by
  ext k
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem gwSchurProduct_C_mul_right (a : ℝ) (p q : ℝ[X]) :
    gwSchurProduct p (C a * q) = C a * gwSchurProduct p q := by
  rw [gwSchurProduct_comm p (C a * q), gwSchurProduct_C_mul_left,
    gwSchurProduct_comm q p]

theorem HasNonnegCoeffs.gwSchurProduct {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (gwSchurProduct p q) := by
  intro k
  rw [coeff_gwSchurProduct]
  exact mul_nonneg (mul_nonneg (by positivity) (hp k)) (hq k)

theorem natDegree_gwSchurProduct_le_left (p q : ℝ[X]) :
    (gwSchurProduct p q).natDegree ≤ p.natDegree := by
  simpa [gwSchurProduct] using
    natDegree_diagonalOperator_le (fun k => (Nat.factorial k : ℝ) * q.coeff k) p

theorem natDegree_gwSchurProduct_le_right (p q : ℝ[X]) :
    (gwSchurProduct p q).natDegree ≤ q.natDegree := by
  rw [gwSchurProduct_comm]
  exact natDegree_gwSchurProduct_le_left q p

/-- Garloff--Wagner's `L` operator: divide the `k`th coefficient by `k!`. -/
def gwL (p : ℝ[X]) : ℝ[X] :=
  diagonalOperator (fun k => ((Nat.factorial k : ℝ)⁻¹)) p

@[simp] theorem coeff_gwL (p : ℝ[X]) (k : ℕ) :
    (gwL p).coeff k = (Nat.factorial k : ℝ)⁻¹ * p.coeff k := by
  rw [gwL, coeff_diagonalOperator]

theorem gwL_zero :
    gwL (0 : ℝ[X]) = 0 := by
  ext k
  simp

theorem gwL_add (p q : ℝ[X]) :
    gwL (p + q) = gwL p + gwL q := by
  simpa [gwL] using diagonalOperator_add (fun k => ((Nat.factorial k : ℝ)⁻¹)) p q

theorem gwL_sub (p q : ℝ[X]) :
    gwL (p - q) = gwL p - gwL q := by
  simpa [gwL] using diagonalOperator_sub (fun k => ((Nat.factorial k : ℝ)⁻¹)) p q

theorem gwL_C_mul (a : ℝ) (p : ℝ[X]) :
    gwL (C a * p) = C a * gwL p := by
  simpa [gwL] using
    diagonalOperator_C_mul (fun k => ((Nat.factorial k : ℝ)⁻¹)) a p

@[simp] theorem gwL_C (a : ℝ) :
    gwL (C a) = C a := by
  ext k
  cases k <;> simp

theorem gwL_eq_zero_iff (p : ℝ[X]) :
    gwL p = 0 ↔ p = 0 := by
  constructor
  · intro h
    ext k
    have hk := congrArg (fun q : ℝ[X] => q.coeff k) h
    rw [coeff_gwL] at hk
    have hfact : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp hk).resolve_left (inv_ne_zero hfact)
  · intro h
    rw [h, gwL_zero]

theorem gwL_ne_zero_iff (p : ℝ[X]) :
    gwL p ≠ 0 ↔ p ≠ 0 := by
  rw [ne_eq, ne_eq, gwL_eq_zero_iff]

theorem natDegree_gwL_le (p : ℝ[X]) :
    (gwL p).natDegree ≤ p.natDegree := by
  simpa [gwL] using
    natDegree_diagonalOperator_le (fun k => ((Nat.factorial k : ℝ)⁻¹)) p

theorem natDegree_gwL {p : ℝ[X]} (hp : p ≠ 0) :
    (gwL p).natDegree = p.natDegree := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_gwL_le p) ?_
  rw [coeff_gwL, coeff_natDegree]
  exact mul_ne_zero (inv_ne_zero (by positivity)) (leadingCoeff_ne_zero.mpr hp)

theorem leadingCoeff_gwL (p : ℝ[X]) :
    (gwL p).leadingCoeff =
      (Nat.factorial p.natDegree : ℝ)⁻¹ * p.leadingCoeff := by
  by_cases hp : p = 0
  · simp [hp, gwL_zero]
  · rw [leadingCoeff, natDegree_gwL hp, coeff_gwL, leadingCoeff]

theorem HasPosLeadingCoeff.gwL {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (gwL p) := by
  rw [HasPosLeadingCoeff, leadingCoeff_gwL]
  rw [HasPosLeadingCoeff] at hp
  exact mul_pos (inv_pos.mpr (by positivity)) hp

theorem HasNonnegCoeffs.gwL {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (gwL p) := by
  simpa [RealRooted.gwL] using
    hp.diagonalOperator (fun k => show 0 ≤ (Nat.factorial k : ℝ)⁻¹ by positivity)

/-- Garloff--Wagner's `J` operator: integrate with zero constant term. -/
def gwJ (p : ℝ[X]) : ℝ[X] :=
  X * diagonalOperator (fun n => ((n + 1 : ℝ)⁻¹)) p

/-- Garloff--Wagner's `D` operator, the usual derivative. -/
def gwD (p : ℝ[X]) : ℝ[X] :=
  derivative p

@[simp] theorem coeff_gwJ_zero (p : ℝ[X]) :
    (gwJ p).coeff 0 = 0 := by
  simp [gwJ]

@[simp] theorem coeff_gwJ_succ (p : ℝ[X]) (n : ℕ) :
    (gwJ p).coeff (n + 1) = (n + 1 : ℝ)⁻¹ * p.coeff n := by
  simp [gwJ]

@[simp] theorem coeff_gwD (p : ℝ[X]) (n : ℕ) :
    (gwD p).coeff n = p.coeff (n + 1) * (n + 1 : ℝ) := by
  rw [gwD, coeff_derivative]

@[simp] theorem gwJ_zero :
    gwJ (0 : ℝ[X]) = 0 := by
  ext n
  cases n <;> simp

theorem gwJ_add (p q : ℝ[X]) :
    gwJ (p + q) = gwJ p + gwJ q := by
  ext n
  cases n <;> simp [mul_add]

theorem gwJ_sub (p q : ℝ[X]) :
    gwJ (p - q) = gwJ p - gwJ q := by
  ext n
  cases n <;> simp [mul_sub]

theorem gwJ_C_mul (a : ℝ) (p : ℝ[X]) :
    gwJ (C a * p) = C a * gwJ p := by
  ext n
  cases n <;> simp [mul_comm, mul_left_comm]

@[simp] theorem gwD_zero :
    gwD (0 : ℝ[X]) = 0 := by
  simp [gwD]

theorem gwD_add (p q : ℝ[X]) :
    gwD (p + q) = gwD p + gwD q := by
  simp [gwD]

theorem gwD_sub (p q : ℝ[X]) :
    gwD (p - q) = gwD p - gwD q := by
  simp [gwD]

theorem gwD_C_mul (a : ℝ) (p : ℝ[X]) :
    gwD (C a * p) = C a * gwD p := by
  ext n
  simp [gwD, coeff_derivative, mul_comm]

theorem gwD_gwJ (p : ℝ[X]) :
    gwD (gwJ p) = p := by
  ext n
  rw [coeff_gwD, coeff_gwJ_succ]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hn]

theorem gwJ_gwD (p : ℝ[X]) :
    gwJ (gwD p) = p - C (p.coeff 0) := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [coeff_gwJ_succ, coeff_gwD]
      simp
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hn]

theorem gwJ_eq_zero_iff (p : ℝ[X]) :
    gwJ p = 0 ↔ p = 0 := by
  constructor
  · intro h
    calc
      p = gwD (gwJ p) := (gwD_gwJ p).symm
      _ = 0 := by rw [h, gwD_zero]
  · intro h
    rw [h, gwJ_zero]

theorem gwJ_ne_zero_iff (p : ℝ[X]) :
    gwJ p ≠ 0 ↔ p ≠ 0 := by
  rw [ne_eq, ne_eq, gwJ_eq_zero_iff]

theorem natDegree_gwJCore {p : ℝ[X]} (hp : p ≠ 0) :
    (diagonalOperator (fun n => ((n + 1 : ℝ)⁻¹)) p).natDegree =
      p.natDegree := by
  refine natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_diagonalOperator_le (fun n => ((n + 1 : ℝ)⁻¹)) p) ?_
  rw [coeff_diagonalOperator, coeff_natDegree]
  exact mul_ne_zero (inv_ne_zero (by positivity)) (leadingCoeff_ne_zero.mpr hp)

theorem natDegree_gwJ {p : ℝ[X]} (hp : p ≠ 0) :
    (gwJ p).natDegree = p.natDegree + 1 := by
  rw [gwJ]
  have hcore :
      diagonalOperator (fun n => ((n + 1 : ℝ)⁻¹)) p ≠ 0 := by
    intro hcore
    have hJ : gwJ p = 0 := by simp [gwJ, hcore]
    exact hp ((gwJ_eq_zero_iff p).mp hJ)
  rw [natDegree_X_mul hcore, natDegree_gwJCore hp]

theorem leadingCoeff_gwJ {p : ℝ[X]} (hp : p ≠ 0) :
    (gwJ p).leadingCoeff = (p.natDegree + 1 : ℝ)⁻¹ * p.leadingCoeff := by
  rw [leadingCoeff, natDegree_gwJ hp, coeff_gwJ_succ, leadingCoeff]

theorem HasPosLeadingCoeff.gwJ {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (gwJ p) := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, HasPosLeadingCoeff, leadingCoeff_zero] at hp
    linarith
  rw [HasPosLeadingCoeff, leadingCoeff_gwJ hp0]
  rw [HasPosLeadingCoeff] at hp
  exact mul_pos (inv_pos.mpr (by positivity)) hp

theorem HasNonnegCoeffs.gwJ {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (gwJ p) := by
  intro n
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [coeff_gwJ_succ]
      exact mul_nonneg (by positivity) (hp n)

theorem HasNonnegCoeffs.gwD {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (gwD p) := by
  simpa [RealRooted.gwD] using hp.derivative

/-- Lemma 10(e): applying `L` after multiplication by `X` is `J ∘ L`. -/
theorem gwL_X_mul (p : ℝ[X]) :
    gwL (X * p) = gwJ (gwL p) := by
  ext n
  cases n with
  | zero =>
      simp [gwL]
  | succ n =>
      rw [coeff_gwL, coeff_X_mul, coeff_gwJ_succ, coeff_gwL]
      rw [Nat.factorial_succ]
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      have hfact : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      field_simp [hn, hfact]
      norm_num only [Nat.cast_add, Nat.cast_mul]
      ring_nf

/-- Lemma 10(f): shifting the right input becomes differentiating the left input. -/
theorem gwSchurProduct_X_mul_right (f g : ℝ[X]) :
    gwSchurProduct f (X * g) = X * gwSchurProduct (gwD f) g := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [coeff_gwSchurProduct, coeff_X_mul, coeff_X_mul, coeff_gwSchurProduct,
        coeff_gwD]
      rw [Nat.factorial_succ]
      norm_num only [Nat.cast_add, Nat.cast_mul]
      ring_nf

/-- Multiplying the right Schur-product input by a real linear factor gives
the recurrence used in Garloff--Wagner, Theorem 12. -/
theorem gwSchurProduct_X_sub_C_mul_right (f p : ℝ[X]) (u : ℝ) :
    gwSchurProduct f ((X - C u) * p) =
      X * gwSchurProduct (gwD f) p - C u * gwSchurProduct f p := by
  ext n
  cases n with
  | zero =>
      simp [coeff_gwSchurProduct]
      ring
  | succ n =>
      rw [coeff_gwSchurProduct, coeff_X_sub_C_mul, coeff_sub, coeff_X_mul,
        coeff_C_mul, coeff_gwSchurProduct, coeff_gwD, coeff_gwSchurProduct]
      rw [if_neg (Nat.succ_ne_zero n), Nat.succ_sub_one, Nat.factorial_succ]
      norm_num only [Nat.cast_add, Nat.cast_mul]
      ring_nf

/-- Left-input version of `gwSchurProduct_X_sub_C_mul_right`, by commutativity. -/
theorem gwSchurProduct_X_sub_C_mul_left (f p : ℝ[X]) (u : ℝ) :
    gwSchurProduct ((X - C u) * f) p =
      X * gwSchurProduct (gwD p) f - C u * gwSchurProduct f p := by
  rw [gwSchurProduct_comm ((X - C u) * f) p,
    gwSchurProduct_X_sub_C_mul_right, gwSchurProduct_comm p f]

/-- Lemma 10(g): `D` distributes over the Garloff--Wagner Schur product. -/
theorem gwD_gwSchurProduct (f g : ℝ[X]) :
    gwD (gwSchurProduct f g) = gwSchurProduct (gwD f) (gwD g) := by
  ext n
  rw [coeff_gwD, coeff_gwSchurProduct, coeff_gwSchurProduct, coeff_gwD,
    coeff_gwD]
  rw [Nat.factorial_succ]
  norm_num only [Nat.cast_add, Nat.cast_mul]
  ring_nf

/-- Lemma 10(h): `J` distributes over the Garloff--Wagner Schur product. -/
theorem gwJ_gwSchurProduct (f g : ℝ[X]) :
    gwJ (gwSchurProduct f g) = gwSchurProduct (gwJ f) (gwJ g) := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [coeff_gwJ_succ, coeff_gwSchurProduct, coeff_gwSchurProduct,
        coeff_gwJ_succ, coeff_gwJ_succ]
      rw [Nat.factorial_succ]
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hn]
      norm_num only [Nat.cast_add, Nat.cast_mul]
      ring_nf

/-- Lemma 10(i), first form: `L (f ( g) = f ⊙ g`. -/
theorem gwL_gwSchurProduct (p q : ℝ[X]) :
    gwL (gwSchurProduct p q) = hadamardProduct p q := by
  ext k
  rw [coeff_gwL, coeff_gwSchurProduct, coeff_hadamardProduct]
  have hfact : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hfact]

/-- Lemma 10(i), second form: `L f ( g = f ⊙ g`. -/
theorem gwSchurProduct_gwL_left (p q : ℝ[X]) :
    gwSchurProduct (gwL p) q = hadamardProduct p q := by
  ext k
  rw [coeff_gwSchurProduct, coeff_gwL, coeff_hadamardProduct]
  have hfact : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hfact]

/-- Lemma 10(i), third form: `f ( L g = f ⊙ g`. -/
theorem gwSchurProduct_gwL_right (p q : ℝ[X]) :
    gwSchurProduct p (gwL q) = hadamardProduct p q := by
  rw [gwSchurProduct_comm p (gwL q), gwSchurProduct_gwL_left q p,
    hadamardProduct_comm q p]

end RealRooted
