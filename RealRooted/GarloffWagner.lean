import RealRooted.HadamardProduct
import RealRooted.IteratedDerivativeShift
import RealRooted.ObreschkoffConverse
import RealRooted.WeightedSum

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Garloff-Wagner algebra

This file starts the direct proof route for Garloff--Wagner, Theorem 4, from
the paper *Hadamard Products of Stable Polynomials Are Stable*.

The paper uses, besides the ordinary coefficientwise Hadamard product, a
factorial-normalized Schur product

```text
f ( g = sum k, k! * a_k * b_k * X^k
```

and a diagonal operator `L` dividing the `k`th coefficient by `k!`.  Lemma 10(i)
in the paper says that applying `L` to the Schur product, or applying `L` to
one input before taking the Schur product, recovers the ordinary Hadamard
product.  The checked lemmas below record this algebraic part in the local
coefficient conventions.

The same lemma also uses the derivative `D` and an integration operator `J`
with zero constant term.  We normalize `J` by
`coeff (J p) (n + 1) = (n + 1)⁻¹ * coeff p n`.
-/

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
  have hfact : (Nat.factorial k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hfact]

/-- Lemma 10(i), second form: `L f ( g = f ⊙ g`. -/
theorem gwSchurProduct_gwL_left (p q : ℝ[X]) :
    gwSchurProduct (gwL p) q = hadamardProduct p q := by
  ext k
  rw [coeff_gwSchurProduct, coeff_gwL, coeff_hadamardProduct]
  have hfact : (Nat.factorial k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hfact]

/-- Lemma 10(i), third form: `f ( L g = f ⊙ g`. -/
theorem gwSchurProduct_gwL_right (p q : ℝ[X]) :
    gwSchurProduct p (gwL q) = hadamardProduct p q := by
  rw [gwSchurProduct_comm p (gwL q), gwSchurProduct_gwL_left q p,
    hadamardProduct_comm q p]

/-! ## Literature theorem interfaces

The next declarations record the project-shaped theorem targets from
Garloff--Wagner, Theorems 11 and 12.  They are `Prop` interfaces rather than
proof stubs; the preceding algebraic lemmas are the checked Lemma 10 input for
proving them.
-/

/-- The operator `J^k L` from Garloff--Wagner, Theorem 11. -/
def gwJL (k : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (gwJ^[k]) (gwL p)

@[simp] theorem gwJL_zero_apply (p : ℝ[X]) :
    gwJL 0 p = gwL p :=
  rfl

theorem gwJL_succ (k : ℕ) (p : ℝ[X]) :
    gwJL (k + 1) p = gwJ (gwJL k p) := by
  rw [gwJL, gwJL, Function.iterate_succ_apply']

@[simp] theorem gwJL_zero (k : ℕ) :
    gwJL k (0 : ℝ[X]) = 0 := by
  induction k with
  | zero =>
      simp [gwJL, gwL_zero]
  | succ k ih =>
      rw [gwJL_succ, ih, gwJ_zero]

theorem gwJL_add (k : ℕ) (p q : ℝ[X]) :
    gwJL k (p + q) = gwJL k p + gwJL k q := by
  induction k with
  | zero =>
      simp [gwJL, gwL_add]
  | succ k ih =>
      rw [gwJL_succ, gwJL_succ, gwJL_succ, ih, gwJ_add]

theorem gwJL_sub (k : ℕ) (p q : ℝ[X]) :
    gwJL k (p - q) = gwJL k p - gwJL k q := by
  induction k with
  | zero =>
      simp [gwJL, gwL_sub]
  | succ k ih =>
      rw [gwJL_succ, gwJL_succ, gwJL_succ, ih, gwJ_sub]

theorem gwJL_C_mul (a : ℝ) (k : ℕ) (p : ℝ[X]) :
    gwJL k (C a * p) = C a * gwJL k p := by
  induction k with
  | zero =>
      simp [gwJL, gwL_C_mul]
  | succ k ih =>
      rw [gwJL_succ, gwJL_succ, ih, gwJ_C_mul]

theorem gwJL_list_sum (k : ℕ) :
    ∀ l : List ℝ[X], gwJL k l.sum = (l.map (gwJL k)).sum
  | [] => by simp
  | p :: l => by
      simp [gwJL_add, gwJL_list_sum k l]

theorem gwJL_weightedSum (k : ℕ) :
    ∀ l : List (ℝ × ℝ[X]),
      gwJL k (weightedSum l) =
        weightedSum (l.map fun ap => (ap.1, gwJL k ap.2))
  | [] => by simp
  | (a, p) :: l => by
      simp [weightedSum_cons, gwJL_add, gwJL_C_mul, gwJL_weightedSum k l]

theorem gwJL_eq_zero_iff (k : ℕ) (p : ℝ[X]) :
    gwJL k p = 0 ↔ p = 0 := by
  induction k with
  | zero =>
      simp [gwJL, gwL_eq_zero_iff]
  | succ k ih =>
      rw [gwJL_succ, gwJ_eq_zero_iff, ih]

theorem gwJL_ne_zero_iff (k : ℕ) (p : ℝ[X]) :
    gwJL k p ≠ 0 ↔ p ≠ 0 := by
  rw [ne_eq, ne_eq, gwJL_eq_zero_iff]

theorem natDegree_gwJL (k : ℕ) {p : ℝ[X]} (hp : p ≠ 0) :
    (gwJL k p).natDegree = p.natDegree + k := by
  induction k with
  | zero =>
      simp [gwJL, natDegree_gwL hp]
  | succ k ih =>
      rw [gwJL_succ, natDegree_gwJ, ih]
      · ring
      · exact (gwJL_ne_zero_iff k p).2 hp

theorem gwD_gwJL_succ (k : ℕ) (p : ℝ[X]) :
    gwD (gwJL (k + 1) p) = gwJL k p := by
  rw [gwJL_succ, gwD_gwJ]

theorem HasPosLeadingCoeff.gwJL {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) (k : ℕ) :
    HasPosLeadingCoeff (gwJL k p) := by
  induction k with
  | zero =>
      simpa [gwJL] using hp.gwL
  | succ k ih =>
      rw [gwJL_succ]
      exact ih.gwJ

theorem HasNonnegCoeffs.gwJL {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (k : ℕ) :
    HasNonnegCoeffs (gwJL k p) := by
  induction k with
  | zero =>
      simpa [gwJL] using hp.gwL
  | succ k ih =>
      rw [gwJL_succ]
      exact ih.gwJ

/-- The algebraic induction step in Garloff--Wagner, Theorem 11. -/
theorem gwJL_X_sub_C_mul (k : ℕ) (u : ℝ) (f : ℝ[X]) :
    gwJL k ((X - C u) * f) = gwJL (k + 1) f - C u * gwJL k f := by
  induction k with
  | zero =>
      simp only [gwJL_zero_apply]
      rw [sub_mul, gwL_sub, gwL_X_mul, gwL_C_mul, gwJL_succ, gwJL_zero_apply]
  | succ k ih =>
      rw [gwJL_succ, ih, gwJ_sub, gwJ_C_mul, ← gwJL_succ, ← gwJL_succ]

/-- The `k = 0` form of `gwJL_X_sub_C_mul`, matching the first transport step
in Garloff--Wagner's proof of Theorem 4(b). -/
theorem gwL_X_sub_C_mul (u : ℝ) (f : ℝ[X]) :
    gwL ((X - C u) * f) = gwJ (gwL f) - C u * gwL f := by
  simpa [gwJL_zero_apply, gwJL_succ] using gwJL_X_sub_C_mul 0 u f

/-- Derivative of the preceding `L`-transport identity. -/
theorem gwD_gwL_X_sub_C_mul (u : ℝ) (f : ℝ[X]) :
    gwD (gwL ((X - C u) * f)) = gwL f - C u * gwD (gwL f) := by
  rw [gwL_X_sub_C_mul, gwD_sub, gwD_C_mul, gwD_gwJ]

/-- Algebraic expansion of the two-linear-factor ordinary Hadamard product
used in Garloff--Wagner's double-deleted paragraph of Theorem 4(b). -/
theorem hadamardProduct_X_sub_C_mul_X_sub_C_mul_eq
    (j u : ℝ) (g q : ℝ[X]) :
    hadamardProduct ((X - C j) * g) ((X - C u) * q) =
      X * gwSchurProduct g (gwL q - C u * gwD (gwL q)) -
        C j * gwSchurProduct g (gwJ (gwL q) - C u * gwL q) := by
  rw [← gwSchurProduct_gwL_right ((X - C j) * g) ((X - C u) * q)]
  rw [gwL_X_sub_C_mul, gwSchurProduct_X_sub_C_mul_left]
  rw [gwD_sub, gwD_C_mul, gwD_gwJ]
  rw [gwSchurProduct_comm (gwL q - C u * gwD (gwL q)) g]

/-- The same induction step written as `(1 - uD) J^(k+1) L f`. -/
theorem gwJL_X_sub_C_mul_eq_sub_gwD (k : ℕ) (u : ℝ) (f : ℝ[X]) :
    gwJL k ((X - C u) * f) =
      gwJL (k + 1) f - C u * gwD (gwJL (k + 1) f) := by
  rw [gwJL_X_sub_C_mul, gwD_gwJL_succ]

/-- Garloff--Wagner's Theorem 11 induction step in `TDeriv` form. -/
theorem gwJL_X_sub_C_mul_eq_TDeriv (k : ℕ) (u : ℝ) (f : ℝ[X]) :
    gwJL k ((X - C u) * f) = TDeriv u (gwJL (k + 1) f) := by
  rw [gwJL_X_sub_C_mul_eq_sub_gwD]
  simp [TDeriv, gwD]

/-- Real-rootedness part of the Garloff--Wagner Theorem 11 induction step. -/
theorem gwJL_X_sub_C_mul_splits {k : ℕ} {u : ℝ} {f : ℝ[X]}
    (h : (gwJL (k + 1) f).Splits) :
    (gwJL k ((X - C u) * f)).Splits := by
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  exact splits_tderiv_all h

/-- All-real derivative-shift form of Garloff--Wagner formula (3):
if `p` is nonconstant and real-rooted, then `p'` precedes `p - ε p'` for
every real `ε`. -/
theorem derivative_prec_TDeriv_of_splits {eps : ℝ} {p : ℝ[X]}
    (hp0 : p ≠ 0) (hp : p.Splits) (hdeg : 1 ≤ p.natDegree) :
    Prec p.derivative (TDeriv eps p) := by
  by_cases hdeg1 : p.natDegree = 1
  · exact derivative_prec_TDeriv_of_natDegree_one hdeg1
  have hdeg2 : 2 ≤ p.natDegree := by
    lia
  have hder : Interlaces p.derivative p := derivative_interlaces hp hdeg2
  have hder_rr : p.derivative ≠ 0 ∧ p.derivative.Splits := hder.2.1
  have hT_rr : TDeriv eps p ≠ 0 ∧ (TDeriv eps p).Splits :=
    ⟨TDeriv_ne_zero hp0, splits_tderiv_all hp⟩
  have hall : AllComboRealRooted p.derivative (TDeriv eps p) := by
    intro α β
    by_cases hβ : β = 0
    · subst β
      by_cases hα : α = 0
      · simp [hα]
      · simpa using (isRealRooted_C_mul hder_rr.1 hder_rr.2 hα).2
    · have hcombo :
          C α * p.derivative + C β * TDeriv eps p =
            C β * TDeriv (eps - β⁻¹ * α) p := by
        ext n
        simp only [TDeriv, coeff_add, coeff_sub, coeff_C_mul]
        field_simp [hβ]
        ring
      rw [hcombo]
      exact (Polynomial.Splits.C (R := ℝ) β).mul (splits_tderiv_all hp)
  have hsucc :
      (TDeriv eps p).natDegree = p.derivative.natDegree + 1 := by
    rw [natDegree_TDeriv, p.natDegree_derivative]
    lia
  have hprec_or :
      Prec p.derivative (TDeriv eps p) ∨
        Prec (TDeriv eps p) p.derivative :=
    prec_of_allComboRealRooted hder_rr.1 hder_rr.2 hT_rr.1 hT_rr.2 hall
      (Or.inl hsucc.symm)
  exact prec_forward_of_orientation_of_succDegree hsucc hprec_or

/-- Coprime/simple-root branch of Garloff--Wagner's formula (3):
`J^k L f` precedes `J^k L ((X - u)f)` when `u ≤ 0`.  The remaining
multiple-root case is the common-factor reduction used later in Theorem 11. -/
theorem gwJL_factor_prec_of_nonpos_of_coprime {k : ℕ} {u : ℝ} {f : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hFs : (gwJL (k + 1) f).Splits)
    (hfpos : HasPosLeadingCoeff f)
    (hcop : u < 0 →
      IsCoprime (gwJL (k + 1) f) (C (-u) * (gwJL (k + 1) f).derivative)) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  have hFpos : HasPosLeadingCoeff (gwJL (k + 1) f) := hfpos.gwJL (k + 1)
  have hdeg : 1 ≤ (gwJL (k + 1) f).natDegree := by
    rw [natDegree_gwJL (k + 1) hf0]
    lia
  have hprec :=
    derivative_prec_TDeriv_of_nonpos_of_coprime
      (eps := u) (p := gwJL (k + 1) f) hu hF0 hFs hFpos hdeg hcop
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by
    simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

/-- Common-factor branch of Garloff--Wagner's formula (3).  For
`F = J^(k+1)L f`, if `F = d q` and `F' = d r`, then the formula (3) proper
position step reduces to the quotient statement `r ≪ q` plus the no-common
Wagner hypothesis for `q` and `-u r`.

The remaining full formula (3) proof must construct this quotient data from
the common roots of `F` and `F'`. -/
theorem gwJL_factor_prec_of_nonpos_of_common_factor {k : ℕ} {u : ℝ} {f d q r : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hFs : (gwJL (k + 1) f).Splits)
    (hF_def : gwJL (k + 1) f = d * q)
    (hFder_def : (gwJL (k + 1) f).derivative = d * r)
    (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    (hrq : Prec r q) (hq_pos : HasPosLeadingCoeff q)
    (hr_pos : HasPosLeadingCoeff r)
    (hcop : u < 0 → IsCoprime q (C (-u) * r)) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  have hdeg : 1 ≤ (gwJL (k + 1) f).natDegree := by
    rw [natDegree_gwJL (k + 1) hf0]
    lia
  have hprec :=
    derivative_prec_TDeriv_of_nonpos_of_common_factor
      (eps := u) (p := gwJL (k + 1) f) (d := d) (q := q) (r := r)
      hu hF0 hFs hdeg hd_ne hd_splits hF_def hFder_def
      hrq hq_pos hr_pos hcop
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by
    simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

/-- Common-factor branch of formula (3), with quotient coprimality expressed
as absence of common real roots. -/
theorem gwJL_factor_prec_of_nonpos_of_common_factor_no_common
    {k : ℕ} {u : ℝ} {f d q r : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hFs : (gwJL (k + 1) f).Splits)
    (hF_def : gwJL (k + 1) f = d * q)
    (hFder_def : (gwJL (k + 1) f).derivative = d * r)
    (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    (hrq : Prec r q) (hq_pos : HasPosLeadingCoeff q)
    (hr_pos : HasPosLeadingCoeff r)
    (hno : ∀ x : ℝ, q.IsRoot x → ¬ r.IsRoot x) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  have hdeg : 1 ≤ (gwJL (k + 1) f).natDegree := by
    rw [natDegree_gwJL (k + 1) hf0]
    lia
  have hprec :=
    derivative_prec_TDeriv_of_nonpos_of_common_factor_no_common
      (eps := u) (p := gwJL (k + 1) f) (d := d) (q := q) (r := r)
      hu hF0 hFs hdeg hd_ne hd_splits hF_def hFder_def
      hrq hq_pos hr_pos hno
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by
    simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

/-- Exact-root squarefree-quotient branch of Garloff--Wagner's formula (3).
If `F = J^(k+1)L f = (X - C a)^m q` and the remaining quotient `q` has simple
roots with no further `X - C a` factor, then the formula (3) proper-position
step follows. -/
theorem gwJL_factor_prec_of_nonpos_of_pow_X_sub_C_factor_hasSimpleRoots
    {k : ℕ} {u a : ℝ} {m : ℕ} {f q : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hFs : (gwJL (k + 1) f).Splits)
    (hfpos : HasPosLeadingCoeff f)
    (hdeg : 2 ≤ (gwJL (k + 1) f).natDegree)
    (hm : 1 ≤ m) (hF_factor : gwJL (k + 1) f = (X - C a) ^ m * q)
    (hq_nodvd : ¬ (X - C a) ∣ q) (hq_simple : HasSimpleRoots q) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  have hFpos : HasPosLeadingCoeff (gwJL (k + 1) f) := hfpos.gwJL (k + 1)
  have hprec :=
    derivative_prec_TDeriv_of_nonpos_of_pow_X_sub_C_factor_hasSimpleRoots
      (eps := u) (p := gwJL (k + 1) f) (q := q) (a := a) (m := m)
      hu hF0 hFs hFpos hdeg hm hF_factor hq_nodvd hq_simple
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by
    simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

/-- Root-multiplicity squarefree-quotient branch of Garloff--Wagner's formula
(3), using the canonical factorization of `F = J^(k+1)L f` at a root `a`. -/
theorem gwJL_factor_prec_of_nonpos_of_rootMultiplicity_factor_hasSimpleRoots
    {k : ℕ} {u a : ℝ} {f : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hFs : (gwJL (k + 1) f).Splits)
    (hfpos : HasPosLeadingCoeff f)
    (hdeg : 2 ≤ (gwJL (k + 1) f).natDegree)
    (hm : 1 ≤ (gwJL (k + 1) f).rootMultiplicity a)
    (hsimple : ∀ q : ℝ[X],
      gwJL (k + 1) f =
        (X - C a) ^ (gwJL (k + 1) f).rootMultiplicity a * q →
      ¬ (X - C a) ∣ q → HasSimpleRoots q) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  have hFpos : HasPosLeadingCoeff (gwJL (k + 1) f) := hfpos.gwJL (k + 1)
  have hprec :=
    derivative_prec_TDeriv_of_nonpos_of_rootMultiplicity_factor_hasSimpleRoots
      (eps := u) (p := gwJL (k + 1) f) (a := a)
      hu hF0 hFs hFpos hdeg hm hsimple
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by
    simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

/-- Formula (3) branch when `F = J^(k+1)L f` has simple roots away from the
chosen exceptional root `a`.  For Garloff--Wagner Theorem 11(b), the intended
choice is `a = 0`. -/
theorem gwJL_factor_prec_of_nonpos_of_rootMultiplicity_factor_hasSimpleRootsExcept
    {k : ℕ} {u a : ℝ} {f : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hFs : (gwJL (k + 1) f).Splits)
    (hfpos : HasPosLeadingCoeff f)
    (hdeg : 2 ≤ (gwJL (k + 1) f).natDegree)
    (hm : 1 ≤ (gwJL (k + 1) f).rootMultiplicity a)
    (hsimple : HasSimpleRootsExcept (gwJL (k + 1) f) a) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  have hFpos : HasPosLeadingCoeff (gwJL (k + 1) f) := hfpos.gwJL (k + 1)
  have hprec :=
    derivative_prec_TDeriv_of_nonpos_of_rootMultiplicity_factor_hasSimpleRootsExcept
      (eps := u) (p := gwJL (k + 1) f) (a := a)
      hu hF0 hFs hFpos hdeg hm hsimple
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by
    simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

theorem gwJ_C_mul_X_pow (a : ℝ) (k : ℕ) :
    gwJ (C a * X ^ k) = C (a * (k + 1 : ℝ)⁻¹) * X ^ (k + 1) := by
  ext n
  cases n with
  | zero =>
      rw [coeff_gwJ_zero, coeff_C_mul_X_pow]
      simp
  | succ n =>
      rw [coeff_gwJ_succ, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
      by_cases hn : n = k
      · subst n
        simp
        ring
      · simp [hn]

theorem gwJL_C_eq_C_mul_X_pow (a : ℝ) :
    ∀ k : ℕ, ∃ b : ℝ, gwJL k (C a) = C b * X ^ k
  | 0 => by
      refine ⟨a, ?_⟩
      simp [gwJL]
  | k + 1 => by
      obtain ⟨b, hb⟩ := gwJL_C_eq_C_mul_X_pow a k
      refine ⟨b * (k + 1 : ℝ)⁻¹, ?_⟩
      rw [gwJL_succ, hb, gwJ_C_mul_X_pow]

theorem gwJL_C_splits (a : ℝ) (k : ℕ) :
    (gwJL k (C a)).Splits := by
  obtain ⟨b, hb⟩ := gwJL_C_eq_C_mul_X_pow a k
  rw [hb]
  exact (Polynomial.Splits.C (R := ℝ) b).mul (Polynomial.Splits.X_pow k)

lemma hasSimpleRootsExcept_zero_C_mul_X_pow {a : ℝ} (ha : a ≠ 0) (k : ℕ) :
    HasSimpleRootsExcept (C a * X ^ k) 0 := by
  intro r hr0 hroot
  exfalso
  have hzero : a * r ^ k = 0 := by
    simpa [Polynomial.IsRoot.def] using hroot
  exact (mul_ne_zero ha (pow_ne_zero k hr0)) hzero

theorem gwJL_splits_of_splits {f : ℝ[X]} (hf0 : f ≠ 0) (hfs : f.Splits) :
    ∀ k, (gwJL k f).Splits := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ {f : ℝ[X]}, f.natDegree = n → f ≠ 0 → f.Splits → ∀ k, (gwJL k f).Splits
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro f hfdeg hf0 hfs k
        by_cases hn0 : n = 0
        · have hfC : f = C (f.coeff 0) := by
            apply eq_C_of_natDegree_eq_zero
            rw [hfdeg, hn0]
          rw [hfC]
          exact gwJL_C_splits (f.coeff 0) k
        · have hroots_pos : 0 < f.roots.card := by
            rw [card_roots_of_splits hfs, hfdeg]
            exact Nat.pos_of_ne_zero hn0
          obtain ⟨u, hu_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
          have hu_root : f.IsRoot u := (mem_roots hf0).mp hu_mem
          obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hu_root
          have hq_dvd : q ∣ f := ⟨X - C u, by rw [hq]; ring⟩
          have hq0 : q ≠ 0 := by
            intro hq0
            rw [hq0, mul_zero] at hq
            exact hf0 hq
          have hq_splits : q.Splits :=
            (isRealRooted_of_dvd hf0 hfs hq0 hq_dvd).2
          have hqdeg_lt : q.natDegree < n := by
            have hmuldeg : n = q.natDegree + 1 := by
              rw [← hfdeg, hq, natDegree_mul (X_sub_C_ne_zero u) hq0,
                natDegree_X_sub_C]
              lia
            lia
          have ihq : (gwJL (k + 1) q).Splits :=
            ih q.natDegree hqdeg_lt (f := q) rfl hq0 hq_splits (k + 1)
          rw [hq]
          exact gwJL_X_sub_C_mul_splits (k := k) (u := u) (f := q) ihq
  exact hP f.natDegree rfl hf0 hfs

/-- All-real Garloff--Wagner formula (3), in the local `J^k L` notation. -/
theorem gwJL_factor_prec_of_splits {k : ℕ} {u : ℝ} {f : ℝ[X]}
    (hf0 : f ≠ 0) (hfs : f.Splits) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  have hFs : (gwJL (k + 1) f).Splits :=
    gwJL_splits_of_splits hf0 hfs (k + 1)
  have hdeg : 1 ≤ (gwJL (k + 1) f).natDegree := by
    rw [natDegree_gwJL (k + 1) hf0]
    lia
  have hprec :=
    derivative_prec_TDeriv_of_splits
      (eps := u) (p := gwJL (k + 1) f) hF0 hFs hdeg
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by
    simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

/-- Theorem 11(a), real-rooted part: `J^k L` preserves real-rootedness. -/
def gwTheorem11RealRootedStatement : Prop :=
  ∀ {f : ℝ[X]}, f ≠ 0 → f.Splits → ∀ k, (gwJL k f).Splits

theorem gwTheorem11RealRooted :
    gwTheorem11RealRootedStatement := by
  intro f hf0 hfs
  exact gwJL_splits_of_splits hf0 hfs

/-- Theorem 11(b), zero-aware PF-cone form: `J^k L` preserves PF polynomials. -/
def gwTheorem11PFStatement : Prop :=
  ∀ {f : ℝ[X]}, IsPFPolynomial f → ∀ k, IsPFPolynomial (gwJL k f)

theorem gwTheorem11PF_of_realRooted
    (h : gwTheorem11RealRootedStatement) :
    gwTheorem11PFStatement := by
  intro f hf k
  by_cases hf0 : f = 0
  · simpa [hf0] using IsPFPolynomial.zero
  · exact IsPFPolynomial.of_realRooted_nonneg
      (hf.hasNonnegCoeffs.gwJL k) (h hf0 (hf.ne_zero_and_splits hf0).2 k)

theorem gwTheorem11PF :
    gwTheorem11PFStatement :=
  gwTheorem11PF_of_realRooted gwTheorem11RealRooted

/-- The standard nonpositive-root part of Garloff--Wagner, Theorem 11(b),
without the later simple-root/common-factor strengthening. -/
def gwTheorem11NonposStatement : Prop :=
  ∀ {f : ℝ[X]},
    f ≠ 0 →
    f.Splits →
    HasPosLeadingCoeff f →
    (∀ r ∈ f.roots, r ≤ 0) →
    ∀ k,
      (gwJL k f).Splits ∧
        HasPosLeadingCoeff (gwJL k f) ∧
        ∀ r ∈ (gwJL k f).roots, r ≤ 0

theorem gwJL_splits_pos_roots_nonpos_of_splits_pos_roots_nonpos {f : ℝ[X]}
    (hf0 : f ≠ 0) (hfs : f.Splits) (hfpos : HasPosLeadingCoeff f)
    (hfroots : ∀ r ∈ f.roots, r ≤ 0) (k : ℕ) :
    (gwJL k f).Splits ∧
      HasPosLeadingCoeff (gwJL k f) ∧
      ∀ r ∈ (gwJL k f).roots, r ≤ 0 := by
  have hfnn : HasNonnegCoeffs f :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hfs).2
      ⟨hfpos, hfroots⟩).1
  have hsplit : (gwJL k f).Splits := gwTheorem11RealRooted hf0 hfs k
  exact ⟨hsplit, hfpos.gwJL k, roots_nonpos_of_nonneg_coeffs hsplit (hfnn.gwJL k)⟩

theorem gwTheorem11Nonpos :
    gwTheorem11NonposStatement := by
  intro f hf0 hfs hfpos hfroots k
  exact gwJL_splits_pos_roots_nonpos_of_splits_pos_roots_nonpos
    hf0 hfs hfpos hfroots k

/-- Simple-except-origin part of Garloff--Wagner, Theorem 11(b). -/
theorem gwJL_hasSimpleRootsExcept_zero_of_splits_roots_nonpos_hasSimpleRootsExcept
    {f : ℝ[X]} (hf0 : f ≠ 0) (hfs : f.Splits)
    (hfroots : ∀ r ∈ f.roots, r ≤ 0)
    (hfsimple : HasSimpleRootsExcept f 0) :
    ∀ k, HasSimpleRootsExcept (gwJL k f) 0 := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ {f : ℝ[X]}, f.natDegree = n → f ≠ 0 → f.Splits →
      (∀ r ∈ f.roots, r ≤ 0) → HasSimpleRootsExcept f 0 →
      ∀ k, HasSimpleRootsExcept (gwJL k f) 0
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro f hfdeg hf0 hfs hfroots hfsimple k
        by_cases hn0 : n = 0
        · have hfC : f = C (f.coeff 0) := by
            apply eq_C_of_natDegree_eq_zero
            rw [hfdeg, hn0]
          obtain ⟨b, hb⟩ := gwJL_C_eq_C_mul_X_pow (f.coeff 0) k
          have hgw0 : gwJL k f ≠ 0 := (gwJL_ne_zero_iff k f).2 hf0
          have hb_ne : b ≠ 0 := by
            intro hb0
            exact hgw0 (by rw [hfC, hb, hb0]; simp)
          rw [hfC, hb]
          exact hasSimpleRootsExcept_zero_C_mul_X_pow hb_ne k
        · have hroots_pos : 0 < f.roots.card := by
            rw [card_roots_of_splits hfs, hfdeg]
            exact Nat.pos_of_ne_zero hn0
          obtain ⟨u, hu_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
          have hu_root : f.IsRoot u := (mem_roots hf0).mp hu_mem
          have hu_nonpos : u ≤ 0 := hfroots u hu_mem
          obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hu_root
          have hq_dvd : q ∣ f := ⟨X - C u, by rw [hq]; ring⟩
          have hq0 : q ≠ 0 := by
            intro hq0
            rw [hq0, mul_zero] at hq
            exact hf0 hq
          have hq_splits : q.Splits :=
            (isRealRooted_of_dvd hf0 hfs hq0 hq_dvd).2
          have hqroots : ∀ r ∈ q.roots, r ≤ 0 := by
            intro r hr
            have hr_root : q.IsRoot r := (mem_roots hq0).mp hr
            have hf_root : f.IsRoot r := by
              rw [hq, Polynomial.IsRoot.def, eval_mul]
              simp [Polynomial.IsRoot.def] at hr_root
              simp [hr_root]
            exact hfroots r ((mem_roots hf0).mpr hf_root)
          have hq_simple : HasSimpleRootsExcept q 0 :=
            hasSimpleRootsExcept_of_X_sub_C_mul hq hfsimple
          have hqdeg_lt : q.natDegree < n := by
            have hmuldeg : n = q.natDegree + 1 := by
              rw [← hfdeg, hq, natDegree_mul (X_sub_C_ne_zero u) hq0,
                natDegree_X_sub_C]
              lia
            lia
          have ihq : ∀ k, HasSimpleRootsExcept (gwJL k q) 0 :=
            ih q.natDegree hqdeg_lt (f := q) rfl hq0 hq_splits hqroots hq_simple
          by_cases hu0 : u = 0
          · subst u
            have hstep : gwJL k ((X - C 0) * q) = gwJL (k + 1) q := by
              rw [gwJL_X_sub_C_mul_eq_TDeriv, TDeriv_zero_eps]
            rw [hq, hstep]
            exact ihq (k + 1)
          · have hstep :
                gwJL k ((X - C u) * q) = TDeriv u (gwJL (k + 1) q) :=
              gwJL_X_sub_C_mul_eq_TDeriv k u q
            have hF0 : gwJL (k + 1) q ≠ 0 :=
              (gwJL_ne_zero_iff (k + 1) q).2 hq0
            have hFs : (gwJL (k + 1) q).Splits :=
              gwTheorem11RealRooted hq0 hq_splits (k + 1)
            rw [hq, hstep]
            exact hasSimpleRootsExcept_TDeriv (ihq (k + 1)) hu0 hF0 hFs
  exact hP f.natDegree rfl hf0 hfs hfroots hfsimple

/-- Theorem 11(b) with the simple-except-origin strengthening included. -/
def gwTheorem11NonposSimpleExceptStatement : Prop :=
  ∀ {f : ℝ[X]},
    f ≠ 0 →
    f.Splits →
    HasPosLeadingCoeff f →
    (∀ r ∈ f.roots, r ≤ 0) →
    HasSimpleRootsExcept f 0 →
    ∀ k,
      (gwJL k f).Splits ∧
        HasPosLeadingCoeff (gwJL k f) ∧
        (∀ r ∈ (gwJL k f).roots, r ≤ 0) ∧
        HasSimpleRootsExcept (gwJL k f) 0

theorem gwJL_splits_pos_roots_nonpos_simpleExcept_of_splits_pos_roots_nonpos_simpleExcept
    {f : ℝ[X]} (hf0 : f ≠ 0) (hfs : f.Splits)
    (hfpos : HasPosLeadingCoeff f) (hfroots : ∀ r ∈ f.roots, r ≤ 0)
    (hfsimple : HasSimpleRootsExcept f 0) (k : ℕ) :
    (gwJL k f).Splits ∧
      HasPosLeadingCoeff (gwJL k f) ∧
      (∀ r ∈ (gwJL k f).roots, r ≤ 0) ∧
      HasSimpleRootsExcept (gwJL k f) 0 := by
  obtain ⟨hsplits, hpos, hroots⟩ :=
    gwJL_splits_pos_roots_nonpos_of_splits_pos_roots_nonpos
      hf0 hfs hfpos hfroots k
  exact ⟨hsplits, hpos, hroots,
    gwJL_hasSimpleRootsExcept_zero_of_splits_roots_nonpos_hasSimpleRootsExcept
      hf0 hfs hfroots hfsimple k⟩

theorem gwTheorem11NonposSimpleExcept :
    gwTheorem11NonposSimpleExceptStatement := by
  intro f hf0 hfs hfpos hfroots hfsimple k
  exact
    gwJL_splits_pos_roots_nonpos_simpleExcept_of_splits_pos_roots_nonpos_simpleExcept
      hf0 hfs hfpos hfroots hfsimple k

/-- Garloff--Wagner formula (3) for a standard polynomial with nonpositive
roots and simple roots except possibly at the origin. -/
theorem gwJL_factor_prec_of_nonpos_of_hasSimpleRootsExcept_zero
    {k : ℕ} {u : ℝ} {f : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hfs : f.Splits)
    (hfpos : HasPosLeadingCoeff f) (hfroots : ∀ r ∈ f.roots, r ≤ 0)
    (hfsimple : HasSimpleRootsExcept f 0) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  obtain ⟨hFs, hFpos, _hFroots, hFsimple⟩ :=
    gwJL_splits_pos_roots_nonpos_simpleExcept_of_splits_pos_roots_nonpos_simpleExcept
      hf0 hfs hfpos hfroots hfsimple (k + 1)
  have hdeg : 1 ≤ (gwJL (k + 1) f).natDegree := by
    rw [natDegree_gwJL (k + 1) hf0]
    lia
  have hprec :=
    derivative_prec_TDeriv_of_nonpos_of_hasSimpleRootsExcept_zero
      (eps := u) (p := gwJL (k + 1) f)
      hu hF0 hFs hFpos hdeg hFsimple
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by
    simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

/-- Garloff--Wagner formula (3), packaged under the Theorem 11(b) hypotheses
that will be available in the Theorem 11(c) induction. -/
theorem gwJL_factor_prec_of_nonpos
    {k : ℕ} {u : ℝ} {f : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hfs : f.Splits)
    (hfpos : HasPosLeadingCoeff f) (hfroots : ∀ r ∈ f.roots, r ≤ 0)
    (hfsimple : HasSimpleRootsExcept f 0) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) :=
  gwJL_factor_prec_of_nonpos_of_hasSimpleRootsExcept_zero
    hu hf0 hfs hfpos hfroots hfsimple

/-- Theorem 11(c), in the local orientation:
Garloff--Wagner's `g $ f` is represented by `Prec f g`. -/
def gwTheorem11PrecStatement : Prop :=
  ∀ {f g : ℝ[X]}, Prec f g → ∀ k, Prec (gwJL k f) (gwJL k g)

/-- Reduction for the Lemma 7/Krein step in Garloff--Wagner, Theorem 11(c):
once `g` is expressed as a weighted sum whose `J^k L` images are compatible
with the common left bound `J^k L f`, Wagner's finite weighted-sum theorem
gives the desired proper-position conclusion. -/
theorem gwJL_prec_of_weightedCompatibleExpansion
    {k : ℕ} {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hg : g = weightedSum l)
    (hcomp :
      WeightedCompatibleLeft (gwJL k f)
        (l.map fun ap => (ap.1, gwJL k ap.2))) :
    Prec (gwJL k f) (gwJL k g) := by
  rw [hg, gwJL_weightedSum]
  exact prec_weightedSum_left hcomp

/-- Interface isolating the remaining Krein-expansion and Wagner-compatibility
work for Garloff--Wagner, Theorem 11(c). -/
def gwTheorem11PrecWeightedExpansionStatement : Prop :=
  ∀ {f g : ℝ[X]}, Prec f g → ∀ k, ∃ l : List (ℝ × ℝ[X]),
    g = weightedSum l ∧
      WeightedCompatibleLeft (gwJL k f)
        (l.map fun ap => (ap.1, gwJL k ap.2))

theorem gwTheorem11Prec_of_weightedCompatibleExpansion
    (h : gwTheorem11PrecWeightedExpansionStatement) :
    gwTheorem11PrecStatement := by
  intro f g hfg k
  rcases h hfg k with ⟨l, hg, hcomp⟩
  exact gwJL_prec_of_weightedCompatibleExpansion hg hcomp

/-- Variable-swapped common-right weighted reduction for the Lemma 7/Krein
step.  If `g` is expanded in summands bounded on the right by `f`, Wagner's
common-right finite-sum theorem gives the reverse conclusion
`J^k L g ≪ J^k L f`. -/
theorem gwJL_weightedExpansion_prec_right
    {k : ℕ} {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hg : g = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hprec : ∀ ap ∈ l, Prec (gwJL k ap.2) (gwJL k f))
    (hpos : ∀ ap ∈ l, HasPosLeadingCoeff (gwJL k ap.2))
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    Prec (gwJL k g) (gwJL k f) := by
  rw [hg, gwJL_weightedSum]
  exact
    prec_weightedSum_right
      (l.map fun ap => (ap.1, gwJL k ap.2)) (gwJL k f)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap₀, hap₀, rfl⟩
        exact hnonneg ap₀ hap₀)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap₀, hap₀, rfl⟩
        exact hprec ap₀ hap₀)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap₀, hap₀, rfl⟩
        exact hpos ap₀ hap₀)
      (by
        rcases hex with ⟨ap, hap, hapos⟩
        exact ⟨(ap.1, gwJL k ap.2), List.mem_map.mpr ⟨ap, hap, rfl⟩, hapos⟩)

/-- Interface for the variable-swapped common-right Krein-expansion direction.
This is not the final Theorem 11(c) orientation by itself; see
`gwTheorem11PrecRightWeightedExpansionStatement` for the forward package. -/
def gwTheorem11RightWeightedExpansionStatement : Prop :=
  ∀ {f g : ℝ[X]}, Prec f g → ∀ k, ∃ l : List (ℝ × ℝ[X]),
    g = weightedSum l ∧
      (∀ ap ∈ l, 0 ≤ ap.1) ∧
      (∀ ap ∈ l, Prec (gwJL k ap.2) (gwJL k f)) ∧
      (∀ ap ∈ l, HasPosLeadingCoeff (gwJL k ap.2)) ∧
      ∃ ap ∈ l, 0 < ap.1

theorem gwTheorem11RevPrec_of_rightWeightedExpansion
    (h : gwTheorem11RightWeightedExpansionStatement) :
    ∀ {f g : ℝ[X]}, Prec f g → ∀ k, Prec (gwJL k g) (gwJL k f) := by
  intro f g hfg k
  rcases h hfg k with ⟨l, hg, hnonneg, hprec, hpos, hex⟩
  exact gwJL_weightedExpansion_prec_right hg hnonneg hprec hpos hex

/-- Common-right weighted reduction in the forward Theorem 11(c) orientation.
If the left input `f` is a nonnegative weighted sum whose `J^k L` images all
precede the common right bound `J^k L g`, then the image of `f` also precedes
the image of `g`. -/
theorem gwJL_prec_of_rightWeightedExpansion
    {k : ℕ} {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hprec : ∀ ap ∈ l, Prec (gwJL k ap.2) (gwJL k g))
    (hpos : ∀ ap ∈ l, HasPosLeadingCoeff (gwJL k ap.2))
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    Prec (gwJL k f) (gwJL k g) := by
  rw [hf, gwJL_weightedSum]
  exact
    prec_weightedSum_right
      (l.map fun ap => (ap.1, gwJL k ap.2)) (gwJL k g)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
        exact hnonneg ap0 hap0)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
        exact hprec ap0 hap0)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
        exact hpos ap0 hap0)
      (by
        rcases hex with ⟨ap, hap, hapos⟩
        exact ⟨(ap.1, gwJL k ap.2), List.mem_map.mpr ⟨ap, hap, rfl⟩, hapos⟩)

/-- Forward Theorem 11(c) interface for the common-right Krein expansion:
given `Prec f g`, write the left input `f` as a nonnegative weighted sum of
summands whose `J^k L` images precede `J^k L g`. -/
def gwTheorem11PrecRightWeightedExpansionStatement : Prop :=
  ∀ {f g : ℝ[X]}, Prec f g → ∀ k, ∃ l : List (ℝ × ℝ[X]),
    f = weightedSum l ∧
      (∀ ap ∈ l, 0 ≤ ap.1) ∧
      (∀ ap ∈ l, Prec (gwJL k ap.2) (gwJL k g)) ∧
      (∀ ap ∈ l, HasPosLeadingCoeff (gwJL k ap.2)) ∧
      ∃ ap ∈ l, 0 < ap.1

theorem gwTheorem11Prec_of_rightWeightedExpansion
    (h : gwTheorem11PrecRightWeightedExpansionStatement) :
    gwTheorem11PrecStatement := by
  intro f g hfg k
  rcases h hfg k with ⟨l, hf, hnonneg, hprec, hpos, hex⟩
  exact gwJL_prec_of_rightWeightedExpansion hf hnonneg hprec hpos hex

private lemma listInterlaces_right_tail_ge :
    ∀ {ss rs : List ℝ} {r : ℝ}, ListInterlaces ss (r :: rs) → ∀ x ∈ rs, r ≤ x
  | [], [], _, _ => by simp
  | [], _ :: _, _, h => by simp [ListInterlaces] at h
  | _ :: _, [], _, _ => by simp
  | s :: ss, r₂ :: rs, r, h => by
      rcases h with ⟨hr_s, hs_r₂, htail⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_trans hr_s hs_r₂
      · exact le_trans (le_trans hr_s hs_r₂)
          (listInterlaces_right_tail_ge htail x hx)

private lemma listInterlaces_left_ge_head :
    ∀ {ss rs : List ℝ} {r : ℝ}, ListInterlaces ss (r :: rs) → ∀ x ∈ ss, r ≤ x
  | [], _, _, _ => by simp
  | _ :: _, [], _, h => by simp [ListInterlaces] at h
  | s :: ss, r₂ :: rs, r, h => by
      rcases h with ⟨hr_s, hs_r₂, htail⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hr_s
      · exact le_trans (le_trans hr_s hs_r₂)
          (listInterlaces_left_ge_head htail x hx)

private lemma listInterlaces_count_right_le_left_add_one (u : ℝ) :
    ∀ {ss rs : List ℝ}, ListInterlaces ss rs → rs.count u ≤ ss.count u + 1
  | [], [], _ => by simp
  | [], [r], _ => by
      by_cases hr : r = u <;> simp [hr]
  | [], _ :: _ :: _, h => by simp [ListInterlaces] at h
  | _ :: _, [], h => by simp [ListInterlaces] at h
  | _ :: _, [_], h => by simp [ListInterlaces] at h
  | s :: ss, r₁ :: r₂ :: rs, h => by
      rcases h with ⟨hr₁s, hs_r₂, htail⟩
      by_cases hr₁ : r₁ = u
      · by_cases hs : s = u
        · subst r₁
          subst s
          have ih := listInterlaces_count_right_le_left_add_one u htail
          simp [List.count_cons] at ih ⊢
          lia
        · subst r₁
          have hu_lt_s : u < s := lt_of_le_of_ne hr₁s (by simpa [eq_comm] using hs)
          have hu_lt_r₂ : u < r₂ := lt_of_lt_of_le hu_lt_s hs_r₂
          have htail_no_mem : u ∉ r₂ :: rs := by
            intro hu_mem
            rcases List.mem_cons.mp hu_mem with hu_eq | hu_rs
            · exact ne_of_gt hu_lt_r₂ hu_eq.symm
            · have hge := listInterlaces_right_tail_ge htail u hu_rs
              linarith
          have htail_count : (r₂ :: rs).count u = 0 :=
            List.count_eq_zero.mpr htail_no_mem
          have hss_no_mem : u ∉ ss := by
            intro hu_mem
            have hge := listInterlaces_left_ge_head htail u hu_mem
            linarith
          have hss_count : ss.count u = 0 := List.count_eq_zero.mpr hss_no_mem
          simp [htail_count, hss_count, hs]
      · have ih := listInterlaces_count_right_le_left_add_one u htail
        by_cases hs : s = u
        · simp [hr₁, hs] at ih ⊢
          lia
        · simpa [hr₁, hs] using ih

private lemma listAlternates_count_right_le_left_add_one (u : ℝ) :
    ∀ {ss rs : List ℝ}, ListAlternates ss rs → rs.count u ≤ ss.count u + 1
  | [], [], _ => by simp
  | [], _ :: _, h => by simp [ListAlternates] at h
  | _ :: _, [], h => by simp [ListAlternates] at h
  | s :: ss, _ :: rs, h => by
      rcases h with ⟨_, htail⟩
      have ih := listInterlaces_count_right_le_left_add_one u htail
      by_cases hs : s = u
      · simp [hs] at ih ⊢
        lia
      · simpa [hs] using ih

/-- Proper position forces every root of the right polynomial to occur on the
left with multiplicity at least one less.  This is the first multiplicity input
for the Garloff--Wagner Lemma 7/Krein expansion. -/
theorem rootMultiplicity_sub_one_le_of_prec_right {f g : ℝ[X]} (h : Prec f g)
    (u : ℝ) :
    g.rootMultiplicity u - 1 ≤ f.rootMultiplicity u := by
  rcases h with ⟨_, _, ss, rs, _, _, hss_eq, hrs_eq, hshape⟩
  have hcount : rs.count u ≤ ss.count u + 1 := by
    rcases hshape with ⟨_, hint⟩ | ⟨_, halt⟩
    · exact listInterlaces_count_right_le_left_add_one u hint
    · exact listAlternates_count_right_le_left_add_one u halt
  have hrs_count : rs.count u = g.rootMultiplicity u := by
    rw [← count_roots g, ← hrs_eq]
    exact (Multiset.coe_count u rs).symm
  have hss_count : ss.count u = f.rootMultiplicity u := by
    rw [← count_roots f, ← hss_eq]
    exact (Multiset.coe_count u ss).symm
  rw [hrs_count, hss_count] at hcount
  lia

/-- If `f ≪ g` and `u` is a root of `g`, then `f` is divisible by all but
one copy of the `u`-factor of `g`.  This is the quotient of the left input
used before defining the Krein coefficient at `u`. -/
theorem exists_precLeft_factor_of_right_isRoot {f g : ℝ[X]} (h : Prec f g)
    {u : ℝ} (hu : g.IsRoot u) :
    ∃ s : ℝ[X],
      f = (X - C u) ^ (g.rootMultiplicity u - 1) * s ∧
        s ≠ 0 ∧ s.Splits ∧
        1 ≤ g.rootMultiplicity u := by
  have hf0 : f ≠ 0 := h.1.1
  have hfs : f.Splits := h.1.2
  have hmul : g.rootMultiplicity u - 1 ≤ f.rootMultiplicity u :=
    rootMultiplicity_sub_one_le_of_prec_right h u
  have hdvd : (X - C u) ^ (g.rootMultiplicity u - 1) ∣ f :=
    (le_rootMultiplicity_iff hf0).mp hmul
  obtain ⟨s, hs⟩ := hdvd
  have hs0 : s ≠ 0 := by
    intro hs_zero
    rw [hs_zero, mul_zero] at hs
    exact hf0 hs
  have hs_dvd : s ∣ f := ⟨(X - C u) ^ (g.rootMultiplicity u - 1), by
    rw [hs]
    ring⟩
  exact ⟨s, hs, hs0, (isRealRooted_of_dvd hf0 hfs hs0 hs_dvd).2,
    Nat.succ_le_of_lt ((rootMultiplicity_pos h.2.1.1).2 hu)⟩

/-- For the coefficient construction, every residual `f - c g` is divisible by
the same one-less-than-full `u`-factor measured from the right input `g`. -/
theorem exists_precResidual_factor_of_right_rootMultiplicity {f g : ℝ[X]}
    (h : Prec f g) (u : ℝ) (c : ℝ) :
    ∃ s : ℝ[X],
      f - C c * g = (X - C u) ^ (g.rootMultiplicity u - 1) * s := by
  let d : ℝ[X] := (X - C u) ^ (g.rootMultiplicity u - 1)
  have hdvd_f : d ∣ f := by
    have hf0 : f ≠ 0 := h.1.1
    have hmul : g.rootMultiplicity u - 1 ≤ f.rootMultiplicity u :=
      rootMultiplicity_sub_one_le_of_prec_right h u
    dsimp [d]
    exact (le_rootMultiplicity_iff hf0).mp hmul
  have hg0 : g ≠ 0 := h.2.1.1
  have hmul_g : g.rootMultiplicity u - 1 ≤ g.rootMultiplicity u := Nat.sub_le _ _
  have hdvd_g : d ∣ g := by
    dsimp [d]
    exact (le_rootMultiplicity_iff hg0).mp hmul_g
  obtain ⟨sf, hf⟩ := hdvd_f
  obtain ⟨sg, hg⟩ := hdvd_g
  refine ⟨sf - C c * sg, ?_⟩
  change f - C c * g = d * (sf - C c * sg)
  rw [hf, hg]
  ring

/-- If two polynomials have the same `(m - 1)`-fold root factor at `u`, then
choosing the coefficient by quotient evaluation makes their difference gain
the full `m`-fold root factor. -/
theorem kreinCoefficient_sub_dvd_fullRoot
    {h q r s : ℝ[X]} {u : ℝ} {m : ℕ}
    (hm : 1 ≤ m)
    (hh : h = (X - C u) ^ (m - 1) * s)
    (hq : q = (X - C u) ^ (m - 1) * r)
    (hr : r.eval u ≠ 0) :
    (X - C u) ^ m ∣ h - C (s.eval u / r.eval u) * q := by
  let a : ℝ := s.eval u / r.eval u
  change (X - C u) ^ m ∣ h - C a * q
  have hroot : (s - C a * r).IsRoot u := by
    rw [Polynomial.IsRoot.def, eval_sub, eval_mul, eval_C]
    dsimp [a]
    field_simp [hr]
    ring
  obtain ⟨t, ht⟩ := (dvd_iff_isRoot).2 hroot
  refine ⟨t, ?_⟩
  rw [hh, hq]
  calc
    (X - C u) ^ (m - 1) * s - C a * ((X - C u) ^ (m - 1) * r)
        = (X - C u) ^ (m - 1) * (s - C a * r) := by ring
    _ = (X - C u) ^ (m - 1) * ((X - C u) * t) := by rw [ht]
    _ = (X - C u) ^ m * t := by
      nth_rw 2 [show m = m - 1 + 1 by exact (Nat.sub_add_cancel hm).symm]
      ring

/-- Coefficient-evaluation divisibility step in the local Garloff--Wagner
orientation.  After factoring a residual and a deleted-root summand by the
same one-less-than-full right-root power, subtracting the evaluation coefficient
makes the new residual divisible by the full right-root power. -/
theorem kreinCoefficient_sub_dvd_rightRootMultiplicity
    {f g q r s : ℝ[X]} (hfg : Prec f g) {u c : ℝ} (hu : g.IsRoot u)
    (hres : f - C c * g = (X - C u) ^ (g.rootMultiplicity u - 1) * s)
    (hq : q = (X - C u) ^ (g.rootMultiplicity u - 1) * r)
    (hr : r.eval u ≠ 0) :
    (X - C u) ^ (g.rootMultiplicity u) ∣
      f - C c * g - C (s.eval u / r.eval u) * q :=
  kreinCoefficient_sub_dvd_fullRoot
    (m := g.rootMultiplicity u)
    (Nat.succ_le_of_lt ((rootMultiplicity_pos hfg.2.1.1).2 hu))
    hres hq hr

/-- Deleting the root `u` from `g` leaves the full root multiplicity at every
different root `v`.  This is the preservation input for iterating the
coefficient subtraction over distinct roots. -/
theorem kreinDeletedSummand_dvd_fullRootMultiplicity_of_ne
    {g q : ℝ[X]} {u v : ℝ} (hg0 : g ≠ 0)
    (hfactor : g = (X - C u) * q) (hvu : v ≠ u) :
    (X - C v) ^ (g.rootMultiplicity v) ∣ q := by
  have hq0 : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hfactor
    exact hg0 hfactor
  have hmul0 : (X - C u) * q ≠ 0 := by
    rw [← hfactor]
    exact hg0
  have hmul := rootMultiplicity_mul (x := v) hmul0
  have hlin : (X - C u : ℝ[X]).rootMultiplicity v = 0 := by
    rw [rootMultiplicity_X_sub_C]
    simp [hvu]
  have hmult : g.rootMultiplicity v = q.rootMultiplicity v := by
    rw [hfactor, hmul, hlin, zero_add]
  exact (le_rootMultiplicity_iff hq0).mp hmult.le

/-- Subtracting a multiple of a root-deleted summand preserves full-power
divisibility at every other root. -/
theorem fullRootMultiplicity_dvd_sub_kreinDeletedSummand_of_ne
    {g h q : ℝ[X]} {u v a : ℝ}
    (hdvd : (X - C v) ^ (g.rootMultiplicity v) ∣ h)
    (hg0 : g ≠ 0) (hfactor : g = (X - C u) * q) (hvu : v ≠ u) :
    (X - C v) ^ (g.rootMultiplicity v) ∣ h - C a * q := by
  have hq_dvd : (X - C v) ^ (g.rootMultiplicity v) ∣ q :=
    kreinDeletedSummand_dvd_fullRootMultiplicity_of_ne hg0 hfactor hvu
  exact dvd_sub hdvd (dvd_mul_of_dvd_right hq_dvd (C a))

/-- A finite list of deleted-root summands preserves full divisibility at a
fixed different root. -/
theorem fullRootMultiplicity_dvd_sub_weightedSum_deletedSummands_of_forall_ne
    {g h : ℝ[X]} {v : ℝ} (hg0 : g ≠ 0)
    {l : List (ℝ × ℝ[X])}
    (hdvd : (X - C v) ^ (g.rootMultiplicity v) ∣ h)
    (hfactor : ∀ ap ∈ l, ∃ u : ℝ, g = (X - C u) * ap.2 ∧ v ≠ u) :
    (X - C v) ^ (g.rootMultiplicity v) ∣ h - weightedSum l := by
  induction l generalizing h with
  | nil =>
      simpa using hdvd
  | cons ap l ih =>
      rcases ap with ⟨a, p⟩
      rcases hfactor (a, p) (by simp) with ⟨u, hfactor_u, hvu⟩
      have htail : ∀ bp ∈ l, ∃ w : ℝ, g = (X - C w) * bp.2 ∧ v ≠ w := by
        intro bp hbp
        exact hfactor bp (by simp [hbp])
      have hstep : (X - C v) ^ (g.rootMultiplicity v) ∣ h - C a * p :=
        fullRootMultiplicity_dvd_sub_kreinDeletedSummand_of_ne
          hdvd hg0 hfactor_u hvu
      have htail_dvd :
          (X - C v) ^ (g.rootMultiplicity v) ∣
            (h - C a * p) - weightedSum l :=
        ih hstep htail
      convert htail_dvd using 1
      simp [weightedSum_cons]
      ring_nf

/-- Simultaneously subtracting the coefficient attached to each distinct root
of `g` leaves a residual divisible by the full root power at every processed
root, provided the one-root coefficient step has been proved for each root. -/
theorem fullRootMultiplicity_dvd_sub_weightedSum_rootDeleted
    {g h : ℝ[X]} (hg0 : g ≠ 0)
    (roots : List ℝ) (hnodup : roots.Nodup)
    (a : ℝ → ℝ) (q : ℝ → ℝ[X])
    (hfactor : ∀ u ∈ roots, g = (X - C u) * q u)
    (hgain : ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ h - C (a u) * q u) :
    ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣
        h - weightedSum (roots.map fun v => (a v, q v)) := by
  induction roots generalizing h with
  | nil =>
      simp
  | cons x xs ih =>
      intro u hu
      have hx_not_mem : x ∉ xs := (List.nodup_cons.mp hnodup).1
      have hxs_nodup : xs.Nodup := (List.nodup_cons.mp hnodup).2
      rcases List.mem_cons.mp hu with hux | hu_xs
      · subst u
        have hdvd_x :
            (X - C x) ^ (g.rootMultiplicity x) ∣ h - C (a x) * q x :=
          hgain x (by simp)
        have htail_factor :
            ∀ ap ∈ xs.map fun v => (a v, q v),
              ∃ y : ℝ, g = (X - C y) * ap.2 ∧ x ≠ y := by
          intro ap hap
          rcases List.mem_map.mp hap with ⟨y, hy, rfl⟩
          have hxy : x ≠ y := by
            intro hxy
            exact hx_not_mem (by simpa [hxy] using hy)
          exact ⟨y, hfactor y (by simp [hy]), hxy⟩
        have htail_dvd :
            (X - C x) ^ (g.rootMultiplicity x) ∣
              (h - C (a x) * q x) - weightedSum (xs.map fun v => (a v, q v)) :=
          fullRootMultiplicity_dvd_sub_weightedSum_deletedSummands_of_forall_ne
            hg0 hdvd_x htail_factor
        convert htail_dvd using 1
        simp [weightedSum_cons]
        ring_nf
      · have hfactor_tail : ∀ v ∈ xs, g = (X - C v) * q v := by
          intro v hv
          exact hfactor v (by simp [hv])
        have hgain_tail : ∀ v ∈ xs,
            (X - C v) ^ (g.rootMultiplicity v) ∣
              (h - C (a x) * q x) - C (a v) * q v := by
          intro v hv
          have hdvd_v :
              (X - C v) ^ (g.rootMultiplicity v) ∣ h - C (a v) * q v :=
            hgain v (by simp [hv])
          have hvx : v ≠ x := by
            intro hvx
            exact hx_not_mem (by simpa [hvx] using hv)
          have hpres :
              (X - C v) ^ (g.rootMultiplicity v) ∣
                (h - C (a v) * q v) - C (a x) * q x :=
            fullRootMultiplicity_dvd_sub_kreinDeletedSummand_of_ne
              hdvd_v hg0 (hfactor x (by simp)) hvx
          convert hpres using 1
          ring
        have htail_dvd :
            (X - C u) ^ (g.rootMultiplicity u) ∣
              (h - C (a x) * q x) -
                weightedSum (xs.map fun v => (a v, q v)) :=
          ih hxs_nodup hfactor_tail hgain_tail u hu_xs
        convert htail_dvd using 1
        simp [weightedSum_cons]
        ring_nf

/-- If a residual is divisible by every full root power of a splitting
polynomial `g`, then it is divisible by `g`. -/
theorem dvd_of_forall_fullRootMultiplicity_dvd
    {g h : ℝ[X]} (hg0 : g ≠ 0) (hgs : g.Splits)
    (hdiv : ∀ u : ℝ, (X - C u) ^ g.rootMultiplicity u ∣ h) :
    g ∣ h := by
  by_cases hh0 : h = 0
  · simp [hh0]
  apply hgs.dvd_of_roots_le_roots hg0
  rw [Multiset.le_iff_count]
  intro u
  rw [count_roots g, count_roots h]
  exact (le_rootMultiplicity_iff hh0).mpr (hdiv u)

/-- Root-list version of `dvd_of_forall_fullRootMultiplicity_dvd`, matching the
output expected from the finite distinct-root assembly. -/
theorem dvd_of_roots_fullRootMultiplicity_dvd
    {g h : ℝ[X]} (hg0 : g ≠ 0) (hgs : g.Splits)
    (hdiv : ∀ u ∈ g.roots, (X - C u) ^ g.rootMultiplicity u ∣ h) :
    g ∣ h := by
  by_cases hh0 : h = 0
  · simp [hh0]
  apply hgs.dvd_of_roots_le_roots hg0
  rw [Multiset.le_iff_count]
  intro u
  rw [count_roots g, count_roots h]
  by_cases hu : u ∈ g.roots
  · exact (le_rootMultiplicity_iff hh0).mpr (hdiv u hu)
  · have hcount : rootMultiplicity u g = 0 := by
      rw [← count_roots g]
      exact Multiset.count_eq_zero.mpr hu
    simp [hcount]

/-- A summand of the cone in Garloff--Wagner Lemma 7, relative to the right
polynomial `g`: either `g` itself or the quotient obtained by deleting one
linear root factor from `g`. -/
def IsGWKreinSummand (g q : ℝ[X]) : Prop :=
  q = g ∨ ∃ u : ℝ, g = (X - C u) * q

namespace IsGWKreinSummand

theorem ne_zero_and_splits {g q : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg0 : g ≠ 0) (hgs : g.Splits) :
    q ≠ 0 ∧ q.Splits := by
  rcases h with hself | ⟨u, hq⟩
  · simpa [hself] using ⟨hg0, hgs⟩
  · have hq0 : q ≠ 0 := by
      intro hq0
      rw [hq0, mul_zero] at hq
      exact hg0 hq
    have hq_dvd : q ∣ g := ⟨X - C u, by rw [hq]; ring⟩
    exact isRealRooted_of_dvd hg0 hgs hq0 hq_dvd

theorem hasPosLeadingCoeff {g q : ℝ[X]} (h : IsGWKreinSummand g q)
    (hgpos : HasPosLeadingCoeff g) :
    HasPosLeadingCoeff q := by
  rcases h with hself | ⟨u, hq⟩
  · simpa [hself] using hgpos
  · have hmul : HasPosLeadingCoeff ((X - C u) * q) := by
      simpa [hq] using hgpos
    exact hasPosLeadingCoeff_of_X_sub_C_mul hmul

theorem gwJL_prec {k : ℕ} {g q : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg0 : g ≠ 0) (hgs : g.Splits) :
    Prec (gwJL k q) (gwJL k g) := by
  rcases h with hself | ⟨u, hq⟩
  · rw [hself]
    exact prec_refl ((gwJL_ne_zero_iff k g).2 hg0)
      (gwJL_splits_of_splits hg0 hgs k)
  · obtain ⟨hq0, hqs⟩ := ne_zero_and_splits (g := g) (q := q) (Or.inr ⟨u, hq⟩)
      hg0 hgs
    rw [hq]
    exact gwJL_factor_prec_of_splits (k := k) (u := u) (f := q) hq0 hqs

end IsGWKreinSummand

/-- Factor a root of `g` into the one-root-deleted Krein summand and the
full-multiplicity residual.  The residual is nonzero at the deleted root, which
is the algebraic input used to define the corresponding Krein coefficient. -/
theorem exists_kreinSummand_factor_of_isRoot {g : ℝ[X]} (hg0 : g ≠ 0)
    (hgs : g.Splits) {u : ℝ} (hu : g.IsRoot u) :
    ∃ q r : ℝ[X],
      g = (X - C u) * q ∧
        q = (X - C u) ^ (g.rootMultiplicity u - 1) * r ∧
        ¬ (X - C u) ∣ r ∧
        r.eval u ≠ 0 ∧
        q ≠ 0 ∧ q.Splits ∧
        r ≠ 0 ∧ r.Splits ∧
        IsGWKreinSummand g q := by
  obtain ⟨r, hgr, hr_nodvd⟩ :=
    exists_eq_pow_rootMultiplicity_mul_and_not_dvd g hg0 u
  let q : ℝ[X] := (X - C u) ^ (g.rootMultiplicity u - 1) * r
  have hm : 1 ≤ g.rootMultiplicity u :=
    Nat.succ_le_of_lt ((rootMultiplicity_pos hg0).2 hu)
  have hfactor : g = (X - C u) * q := by
    rw [hgr]
    change (X - C u) ^ g.rootMultiplicity u * r =
      (X - C u) * ((X - C u) ^ (g.rootMultiplicity u - 1) * r)
    nth_rw 1 [show g.rootMultiplicity u = g.rootMultiplicity u - 1 + 1 by
      exact (Nat.sub_add_cancel hm).symm]
    ring
  have hq0 : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hfactor
    exact hg0 hfactor
  have hq_dvd : q ∣ g := ⟨X - C u, by simpa [mul_comm] using hfactor⟩
  have hq_split : q.Splits := (isRealRooted_of_dvd hg0 hgs hq0 hq_dvd).2
  have hr0 : r ≠ 0 := by
    intro hr0
    rw [hr0, mul_zero] at hgr
    exact hg0 hgr
  have hr_dvd : r ∣ g := ⟨(X - C u) ^ g.rootMultiplicity u, by
    simpa [mul_comm] using hgr⟩
  have hr_split : r.Splits := (isRealRooted_of_dvd hg0 hgs hr0 hr_dvd).2
  exact ⟨q, r, hfactor, rfl, hr_nodvd,
    (fun hroot => hr_nodvd ((dvd_iff_isRoot).2 hroot)),
    hq0, hq_split, hr0, hr_split, Or.inr ⟨u, hfactor⟩⟩

/-- Single-root coefficient package for the Garloff--Wagner Lemma 7
construction.  For a root `u` of the right polynomial, this chooses the
deleted-root summand and the coefficient that gains the full `u`-root power. -/
theorem exists_kreinCoefficientData_of_right_isRoot {f g : ℝ[X]}
    (hfg : Prec f g) (hgs : g.Splits) (c : ℝ) {u : ℝ}
    (hu : g.IsRoot u) :
    ∃ a : ℝ, ∃ q : ℝ[X],
      g = (X - C u) * q ∧
        IsGWKreinSummand g q ∧
        (X - C u) ^ (g.rootMultiplicity u) ∣
          f - C c * g - C a * q := by
  rcases exists_kreinSummand_factor_of_isRoot hfg.2.1.1 hgs hu with
    ⟨q, r, hfactor, hq, _, hr_eval, _, _, _, _, hsummand⟩
  rcases exists_precResidual_factor_of_right_rootMultiplicity hfg u c with
    ⟨s, hres⟩
  exact ⟨s.eval u / r.eval u, q, hfactor, hsummand,
    kreinCoefficient_sub_dvd_rightRootMultiplicity hfg hu hres hq hr_eval⟩

/-- Subtracting the coefficient chosen at each distinct root of `g` gives a
residual divisible by `g`.  This is the identity-side part of the
Garloff--Wagner Lemma 7 expansion, before the final degree and sign arguments. -/
theorem exists_kreinRootDeletedSub_dvd_right {f g : ℝ[X]}
    (hfg : Prec f g) (c : ℝ) :
    ∃ l : List (ℝ × ℝ[X]),
      (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        g ∣ f - C c * g - weightedSum l := by
  classical
  let roots : List ℝ := g.roots.toFinset.toList
  have hroots_nodup : roots.Nodup := Finset.nodup_toList _
  have hroot : ∀ u ∈ roots, g.IsRoot u := by
    intro u hu
    exact (mem_roots hfg.2.1.1).mp
      (Multiset.mem_toFinset.mp (Finset.mem_toList.mp hu))
  have hdata : ∀ u ∈ roots, ∃ a : ℝ, ∃ q : ℝ[X],
      g = (X - C u) * q ∧
        IsGWKreinSummand g q ∧
        (X - C u) ^ (g.rootMultiplicity u) ∣
          f - C c * g - C a * q := by
    intro u hu
    exact exists_kreinCoefficientData_of_right_isRoot hfg hfg.2.1.2 c (hroot u hu)
  choose a q hfactor hsummand hgain using hdata
  let a' : ℝ → ℝ := fun u => if hu : u ∈ roots then a u hu else 0
  let q' : ℝ → ℝ[X] := fun u => if hu : u ∈ roots then q u hu else 0
  let l : List (ℝ × ℝ[X]) := roots.map fun u => (a' u, q' u)
  have hfactor' : ∀ u ∈ roots, g = (X - C u) * q' u := by
    intro u hu
    simp [q', hu, hfactor u hu]
  have hgain' : ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ f - C c * g - C (a' u) * q' u := by
    intro u hu
    simp [a', q', hu, hgain u hu]
  have hdiv_roots : ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ f - C c * g - weightedSum l := by
    simpa [l] using
      fullRootMultiplicity_dvd_sub_weightedSum_rootDeleted
        hfg.2.1.1 roots hroots_nodup a' q' hfactor' hgain'
  have hdiv_all_roots : ∀ u ∈ g.roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ f - C c * g - weightedSum l := by
    intro u hu
    exact hdiv_roots u (by
      rw [Finset.mem_toList, Multiset.mem_toFinset]
      exact hu)
  refine ⟨l, ?_, dvd_of_roots_fullRootMultiplicity_dvd hfg.2.1.1 hfg.2.1.2 hdiv_all_roots⟩
  intro ap hap
  rcases List.mem_map.mp hap with ⟨u, hu, rfl⟩
  simp [q', hu, hsummand u hu]

/-- Degree bound for a finite weighted sum, assuming every summand has degree
at most the same bound. -/
theorem natDegree_weightedSum_le_of_forall {l : List (ℝ × ℝ[X])} {n : ℕ}
    (h : ∀ ap ∈ l, ap.2.natDegree ≤ n) :
    (weightedSum l).natDegree ≤ n := by
  induction l with
  | nil => simp
  | cons ap l ih =>
      rcases ap with ⟨a, p⟩
      have hp : (C a * p).natDegree ≤ n :=
        (natDegree_C_mul_le a p).trans (h (a, p) (by simp))
      have htail : (weightedSum l).natDegree ≤ n := by
        apply ih
        intro bp hbp
        exact h bp (by simp [hbp])
      simpa [weightedSum_cons] using natDegree_add_le_of_le hp htail

/-- Strict version of `natDegree_weightedSum_le_of_forall`, for positive
degree bounds. -/
theorem natDegree_weightedSum_lt_of_forall {l : List (ℝ × ℝ[X])} {n : ℕ}
    (hn : 0 < n) (h : ∀ ap ∈ l, ap.2.natDegree < n) :
    (weightedSum l).natDegree < n := by
  have hle : (weightedSum l).natDegree ≤ n - 1 :=
    natDegree_weightedSum_le_of_forall (l := l) (n := n - 1) (by
      intro ap hap
      exact Nat.le_pred_of_lt (h ap hap))
  lia

/-- Deleting one linear factor from a nonzero polynomial strictly lowers
`natDegree`. -/
theorem natDegree_lt_of_kreinDeleted_factor {g q : ℝ[X]} {u : ℝ}
    (hg0 : g ≠ 0) (hfactor : g = (X - C u) * q) :
    q.natDegree < g.natDegree := by
  have hq0 : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hfactor
    exact hg0 hfactor
  have hdeg : g.natDegree = q.natDegree + 1 := by
    rw [hfactor, natDegree_mul (X_sub_C_ne_zero u) hq0, natDegree_X_sub_C]
    exact Nat.add_comm 1 q.natDegree
  rw [hdeg]
  exact Nat.lt_succ_self _

/-- A weighted sum of one-root-deleted factors of `g` has degree strictly
smaller than `g`, provided `g` has positive degree. -/
theorem natDegree_weightedSum_deletedFactors_lt {g : ℝ[X]}
    (hg0 : g ≠ 0) (hgdeg : 0 < g.natDegree)
    (roots : List ℝ) (a : ℝ → ℝ) (q : ℝ → ℝ[X])
    (hfactor : ∀ u ∈ roots, g = (X - C u) * q u) :
    (weightedSum (roots.map fun u => (a u, q u))).natDegree < g.natDegree := by
  apply natDegree_weightedSum_lt_of_forall hgdeg
  intro ap hap
  rcases List.mem_map.mp hap with ⟨u, hu, rfl⟩
  exact natDegree_lt_of_kreinDeleted_factor hg0 (hfactor u hu)

/-- If two polynomials have degree strictly below a positive bound, then so does
their difference. -/
theorem natDegree_sub_lt_of_both_lt {p q : ℝ[X]} {n : ℕ}
    (hn : 0 < n) (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p - q).natDegree < n := by
  have hle : (p - q).natDegree ≤ n - 1 := by
    simpa using
      natDegree_sub_le_of_le (Nat.le_pred_of_lt hp) (Nat.le_pred_of_lt hq)
  lia

/-- If the coefficient at a positive upper degree bound vanishes, the actual
degree is strictly smaller than that bound. -/
theorem natDegree_lt_of_le_of_coeff_eq_zero {p : ℝ[X]} {n : ℕ}
    (hn : 0 < n) (hle : p.natDegree ≤ n) (hcoeff : p.coeff n = 0) :
    p.natDegree < n := by
  by_cases hp0 : p = 0
  · simp [hp0, hn]
  · by_contra hnot
    have hge : n ≤ p.natDegree := le_of_not_gt hnot
    have heq : p.natDegree = n := le_antisymm hle hge
    have hcoeff_ne : p.coeff n ≠ 0 := by
      rw [← heq]
      exact leadingCoeff_ne_zero.mpr hp0
    exact hcoeff_ne hcoeff

/-- Choose the scalar multiple of `g` that cancels the leading term of `f`,
when `f` has degree at most the positive degree of `g`. -/
theorem exists_C_mul_sub_natDegree_lt_of_le {f g : ℝ[X]}
    (hg0 : g ≠ 0) (hgdeg : 0 < g.natDegree) (hdeg : f.natDegree ≤ g.natDegree) :
    ∃ c : ℝ, (f - C c * g).natDegree < g.natDegree := by
  by_cases hlt : f.natDegree < g.natDegree
  · refine ⟨0, ?_⟩
    simpa using hlt
  · have hdeg_eq : f.natDegree = g.natDegree := le_antisymm hdeg (le_of_not_gt hlt)
    let c : ℝ := f.leadingCoeff / g.leadingCoeff
    refine ⟨c, ?_⟩
    have hc_top : (f - C c * g).coeff g.natDegree = 0 := by
      have hg_lc_ne : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
      have hfcoeff : f.coeff g.natDegree = f.leadingCoeff := by
        rw [← hdeg_eq]
        rfl
      rw [coeff_sub, coeff_C_mul, hfcoeff]
      change f.leadingCoeff -
        (f.leadingCoeff / g.leadingCoeff) * g.leadingCoeff = 0
      field_simp [hg_lc_ne]
      ring
    have hle : (f - C c * g).natDegree ≤ g.natDegree := by
      simpa using natDegree_sub_le_of_le hdeg (natDegree_C_mul_le c g)
    exact natDegree_lt_of_le_of_coeff_eq_zero hgdeg hle hc_top

/-- Choose a nonnegative scalar multiple of `g` that cancels the leading term
of `f`, when both polynomials have positive leading coefficient and
`deg f ≤ deg g`. -/
theorem exists_nonneg_C_mul_sub_natDegree_lt_of_le {f g : ℝ[X]}
    (hfpos : HasPosLeadingCoeff f) (hgpos : HasPosLeadingCoeff g)
    (hgdeg : 0 < g.natDegree) (hdeg : f.natDegree ≤ g.natDegree) :
    ∃ c : ℝ, 0 ≤ c ∧ (f - C c * g).natDegree < g.natDegree := by
  by_cases hlt : f.natDegree < g.natDegree
  · refine ⟨0, by norm_num, ?_⟩
    simpa using hlt
  · have hdeg_eq : f.natDegree = g.natDegree := le_antisymm hdeg (le_of_not_gt hlt)
    let c : ℝ := f.leadingCoeff / g.leadingCoeff
    refine ⟨c, ?_, ?_⟩
    · dsimp [c]
      exact div_nonneg hfpos.le hgpos.le
    · have hg_lc_ne : g.leadingCoeff ≠ 0 := ne_of_gt hgpos
      have hc_top : (f - C c * g).coeff g.natDegree = 0 := by
        have hfcoeff : f.coeff g.natDegree = f.leadingCoeff := by
          rw [← hdeg_eq]
          rfl
        rw [coeff_sub, coeff_C_mul, hfcoeff]
        change f.leadingCoeff -
          (f.leadingCoeff / g.leadingCoeff) * g.leadingCoeff = 0
        field_simp [hg_lc_ne]
        ring
      have hle : (f - C c * g).natDegree ≤ g.natDegree := by
        simpa using natDegree_sub_le_of_le hdeg (natDegree_C_mul_le c g)
      exact natDegree_lt_of_le_of_coeff_eq_zero hgdeg hle hc_top

/-- A nonzero divisor cannot divide a polynomial of strictly smaller degree,
unless the smaller polynomial is zero. -/
theorem eq_zero_of_dvd_of_natDegree_lt {g h : ℝ[X]}
    (hg0 : g ≠ 0) (hdvd : g ∣ h) (hlt : h.natDegree < g.natDegree) :
    h = 0 := by
  rcases hdvd with ⟨r, rfl⟩
  by_cases hr0 : r = 0
  · simp [hr0]
  · exfalso
    rw [natDegree_mul hg0 hr0] at hlt
    lia

/-- Positive-degree identity part of Garloff--Wagner Lemma 7: `f` is a scalar
multiple of the right polynomial plus a weighted sum of one-root-deleted
factors of the right polynomial.  Coefficient nonnegativity is the remaining
separate sign step. -/
theorem exists_kreinRootDeletedExpansion_right {f g : ℝ[X]}
    (hfg : Prec f g) (hgdeg : 0 < g.natDegree) :
    ∃ c : ℝ, ∃ l : List (ℝ × ℝ[X]),
      (∀ ap ∈ l, ∃ u : ℝ, g = (X - C u) * ap.2) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        f = C c * g + weightedSum l := by
  classical
  rcases exists_C_mul_sub_natDegree_lt_of_le hfg.2.1.1 hgdeg
      hfg.natDegree_le with ⟨c, hcdeg⟩
  let roots : List ℝ := g.roots.toFinset.toList
  have hroots_nodup : roots.Nodup := Finset.nodup_toList _
  have hroot : ∀ u ∈ roots, g.IsRoot u := by
    intro u hu
    exact (mem_roots hfg.2.1.1).mp
      (Multiset.mem_toFinset.mp (Finset.mem_toList.mp hu))
  have hdata : ∀ u ∈ roots, ∃ a : ℝ, ∃ q : ℝ[X],
      g = (X - C u) * q ∧
        IsGWKreinSummand g q ∧
        (X - C u) ^ (g.rootMultiplicity u) ∣
          f - C c * g - C a * q := by
    intro u hu
    exact exists_kreinCoefficientData_of_right_isRoot hfg hfg.2.1.2 c (hroot u hu)
  choose a q hfactor hsummand hgain using hdata
  let a' : ℝ → ℝ := fun u => if hu : u ∈ roots then a u hu else 0
  let q' : ℝ → ℝ[X] := fun u => if hu : u ∈ roots then q u hu else 0
  let l : List (ℝ × ℝ[X]) := roots.map fun u => (a' u, q' u)
  have hfactor' : ∀ u ∈ roots, g = (X - C u) * q' u := by
    intro u hu
    simp [q', hu, hfactor u hu]
  have hgain' : ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ f - C c * g - C (a' u) * q' u := by
    intro u hu
    simp [a', q', hu, hgain u hu]
  have hdiv_roots : ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ f - C c * g - weightedSum l := by
    simpa [l] using
      fullRootMultiplicity_dvd_sub_weightedSum_rootDeleted
        hfg.2.1.1 roots hroots_nodup a' q' hfactor' hgain'
  have hdiv_all_roots : ∀ u ∈ g.roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ f - C c * g - weightedSum l := by
    intro u hu
    exact hdiv_roots u (by
      rw [Finset.mem_toList, Multiset.mem_toFinset]
      exact hu)
  have hdiv : g ∣ f - C c * g - weightedSum l :=
    dvd_of_roots_fullRootMultiplicity_dvd hfg.2.1.1 hfg.2.1.2 hdiv_all_roots
  have hwsdeg : (weightedSum l).natDegree < g.natDegree := by
    simpa [l] using
      natDegree_weightedSum_deletedFactors_lt hfg.2.1.1 hgdeg roots a' q' hfactor'
  have hresdeg : (f - C c * g - weightedSum l).natDegree < g.natDegree :=
    natDegree_sub_lt_of_both_lt hgdeg hcdeg hwsdeg
  have hzero : f - C c * g - weightedSum l = 0 :=
    eq_zero_of_dvd_of_natDegree_lt hfg.2.1.1 hdiv hresdeg
  refine ⟨c, l, ?_, ?_, ?_⟩
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨u, hu, rfl⟩
    exact ⟨u, hfactor' u hu⟩
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨u, hu, rfl⟩
    simp [q', hu, hsummand u hu]
  · have hsub : f - C c * g = weightedSum l := sub_eq_zero.mp hzero
    rw [← hsub]
    ring

/-- A nonzero splitting polynomial precedes the polynomial obtained by adding
one real linear factor. -/
theorem prec_self_X_sub_C_mul {r : ℝ[X]} (hr0 : r ≠ 0) (hrs : r.Splits)
    (u : ℝ) :
    Prec r ((X - C u) * r) := by
  have hright0 : (X - C u) * r ≠ 0 := mul_ne_zero (X_sub_C_ne_zero u) hr0
  have hright_splits : ((X - C u) * r).Splits :=
    (Polynomial.Splits.X_sub_C u).mul hrs
  have hall : AllComboRealRooted r ((X - C u) * r) := by
    intro α β
    have hlin_splits : (C α + C β * (X - C u : ℝ[X])).Splits := by
      apply Polynomial.Splits.of_natDegree_le_one
      have hdegC : (C α : ℝ[X]).natDegree ≤ 1 := by
        simp
      have hdegmul : (C β * (X - C u : ℝ[X])).natDegree ≤ 1 := by
        exact (natDegree_C_mul_le β (X - C u : ℝ[X])).trans (by simp)
      exact natDegree_add_le_of_le hdegC hdegmul
    have hfact :
        C α * r + C β * ((X - C u) * r) =
          (C α + C β * (X - C u)) * r := by
      ring
    rw [hfact]
    exact hlin_splits.mul hrs
  have hdeg : r.natDegree + 1 = ((X - C u) * r).natDegree := by
    rw [natDegree_mul (X_sub_C_ne_zero u) hr0, natDegree_X_sub_C]
    exact (Nat.add_comm 1 r.natDegree).symm
  have hprec_or :=
    prec_of_allComboRealRooted hr0 hrs hright0 hright_splits hall (Or.inl hdeg)
  exact prec_forward_of_orientation_of_succDegree hdeg.symm hprec_or

/-- Sign input for the Krein coefficient: after stripping the common
`(X - C u)^(m - 1)` factor from `f ≪ g`, the quotient of `f` has the same sign
as the full root-deleted quotient of `g` at `u`. -/
theorem kreinCoefficient_eval_div_nonneg
    {f g s r : ℝ[X]} {u : ℝ}
    (hfg : Prec f g) (hfpos : HasPosLeadingCoeff f)
    (hgpos : HasPosLeadingCoeff g) (hu : g.IsRoot u)
    (hf_factor : f = (X - C u) ^ (g.rootMultiplicity u - 1) * s)
    (hg_factor : g = (X - C u) ^ (g.rootMultiplicity u) * r)
    (hr0 : r ≠ 0) (hrs : r.Splits) (hr_eval : r.eval u ≠ 0) :
    0 ≤ s.eval u / r.eval u := by
  let m : ℕ := g.rootMultiplicity u
  by_cases hs_eval : s.eval u = 0
  · simp [hs_eval]
  have hm : 1 ≤ m := by
    dsimp [m]
    exact Nat.succ_le_of_lt ((rootMultiplicity_pos hfg.2.1.1).2 hu)
  have hf_factor_m : f = (X - C u) ^ (m - 1) * s := by
    simpa [m] using hf_factor
  have hg_factor_m : g = (X - C u) ^ m * r := by
    simpa [m] using hg_factor
  have hg_common : g = (X - C u) ^ (m - 1) * ((X - C u) * r) := by
    rw [hg_factor_m]
    nth_rw 1 [show m = m - 1 + 1 by exact (Nat.sub_add_cancel hm).symm]
    ring_nf
  have hprec_common :
      Prec ((X - C u) ^ (m - 1) * s)
        ((X - C u) ^ (m - 1) * ((X - C u) * r)) := by
    rw [← hf_factor_m, ← hg_common]
    exact hfg
  have hsr_prec : Prec s ((X - C u) * r) :=
    prec_of_prec_mul_pow_X_sub_C_both u (m - 1) hprec_common
  have hs_pos : HasPosLeadingCoeff s := by
    have hfpos' : HasPosLeadingCoeff ((X - C u) ^ (m - 1) * s) := by
      rw [← hf_factor_m]
      exact hfpos
    exact hasPosLeadingCoeff_of_pow_X_sub_C_mul hfpos'
  have hr_pos : HasPosLeadingCoeff r := by
    have hgpos' : HasPosLeadingCoeff ((X - C u) ^ m * r) := by
      rw [← hg_factor_m]
      exact hgpos
    exact hasPosLeadingCoeff_of_pow_X_sub_C_mul hgpos'
  have hrr_prec : Prec r ((X - C u) * r) := prec_self_X_sub_C_mul hr0 hrs u
  have hroot_right : ((X - C u) * r).IsRoot u := by
    rw [Polynomial.IsRoot.def, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hprod : 0 ≤ s.eval u * r.eval u :=
    eval_mul_eval_nonneg_of_prec_right hsr_prec hrr_prec hs_pos hr_pos hroot_right
  have hsq_pos : 0 < r.eval u * r.eval u := mul_self_pos.mpr hr_eval
  have hquot : 0 ≤ (s.eval u * r.eval u) / (r.eval u * r.eval u) :=
    div_nonneg hprod hsq_pos.le
  convert hquot using 1
  field_simp [hr_eval]

/-- Residual form of `kreinCoefficient_eval_div_nonneg`, matching the quotient
`s` produced from `f - c g` in the coefficient construction.  The scalar
multiple of `g` contributes one extra factor of `X - C u`, so it does not
change the quotient evaluation at `u`. -/
theorem kreinCoefficient_residual_eval_div_nonneg
    {f g q r s : ℝ[X]} {u c : ℝ}
    (hfg : Prec f g) (hfpos : HasPosLeadingCoeff f)
    (hgpos : HasPosLeadingCoeff g) (hu : g.IsRoot u)
    (hres : f - C c * g = (X - C u) ^ (g.rootMultiplicity u - 1) * s)
    (hfactor : g = (X - C u) * q)
    (hq : q = (X - C u) ^ (g.rootMultiplicity u - 1) * r)
    (hr0 : r ≠ 0) (hrs : r.Splits) (hr_eval : r.eval u ≠ 0) :
    0 ≤ s.eval u / r.eval u := by
  let m : ℕ := g.rootMultiplicity u
  let d : ℝ[X] := (X - C u) ^ (m - 1)
  rcases exists_precLeft_factor_of_right_isRoot hfg hu with ⟨t, hf_t, _, _, _⟩
  have hf_t_m : f = d * t := by
    simpa [d, m] using hf_t
  have hq_m : q = d * r := by
    simpa [d, m] using hq
  have hg_common : g = d * ((X - C u) * r) := by
    rw [hfactor, hq_m]
    dsimp [d]
    ring
  have hres_m : f - C c * g = d * s := by
    simpa [d, m] using hres
  have hd0 : d ≠ 0 := by
    dsimp [d]
    exact pow_ne_zero _ (X_sub_C_ne_zero u)
  have hs_eq : s = t - C c * ((X - C u) * r) := by
    apply mul_left_cancel₀ hd0
    rw [← hres_m, hf_t_m, hg_common]
    ring
  have hs_eval : s.eval u = t.eval u := by
    rw [hs_eq, eval_sub, eval_mul, eval_C, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hm : 1 ≤ m := by
    dsimp [m]
    exact Nat.succ_le_of_lt ((rootMultiplicity_pos hfg.2.1.1).2 hu)
  have hg_full_m : g = (X - C u) ^ m * r := by
    rw [hg_common]
    dsimp [d]
    nth_rw 2 [show m = m - 1 + 1 by exact (Nat.sub_add_cancel hm).symm]
    ring_nf
  have hg_full : g = (X - C u) ^ g.rootMultiplicity u * r := by
    simpa [m] using hg_full_m
  have hnonneg : 0 ≤ t.eval u / r.eval u :=
    kreinCoefficient_eval_div_nonneg hfg hfpos hgpos hu hf_t hg_full hr0 hrs
      hr_eval
  rwa [hs_eval]

/-- Single-root coefficient package with the sign conclusion included. -/
theorem exists_kreinCoefficientData_nonneg_of_right_isRoot {f g : ℝ[X]}
    (hfg : Prec f g) (hfpos : HasPosLeadingCoeff f)
    (hgpos : HasPosLeadingCoeff g) (hgs : g.Splits) (c : ℝ) {u : ℝ}
    (hu : g.IsRoot u) :
    ∃ a : ℝ, ∃ q : ℝ[X],
      0 ≤ a ∧
        g = (X - C u) * q ∧
        IsGWKreinSummand g q ∧
        (X - C u) ^ (g.rootMultiplicity u) ∣
          f - C c * g - C a * q := by
  rcases exists_kreinSummand_factor_of_isRoot hfg.2.1.1 hgs hu with
    ⟨q, r, hfactor, hq, _, hr_eval, _, _, hr0, hrs, hsummand⟩
  rcases exists_precResidual_factor_of_right_rootMultiplicity hfg u c with
    ⟨s, hres⟩
  refine ⟨s.eval u / r.eval u, q, ?_, hfactor, hsummand, ?_⟩
  · exact
      kreinCoefficient_residual_eval_div_nonneg hfg hfpos hgpos hu hres hfactor hq
        hr0 hrs hr_eval
  · exact kreinCoefficient_sub_dvd_rightRootMultiplicity hfg hu hres hq hr_eval

/-- Positive-degree Garloff--Wagner Lemma 7 package: if `f ≪ g` and both
polynomials have positive leading coefficient, then `f` is a nonnegative
weighted sum of `g` and the one-root-deleted Krein summands of `g`. -/
theorem exists_kreinSummandExpansion_nonneg_right_of_pos_natDegree {f g : ℝ[X]}
    (hfg : Prec f g) (hfpos : HasPosLeadingCoeff f)
    (hgpos : HasPosLeadingCoeff g) (hgdeg : 0 < g.natDegree) :
    ∃ l : List (ℝ × ℝ[X]),
      f = weightedSum l ∧
        (∀ ap ∈ l, 0 ≤ ap.1) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        ∃ ap ∈ l, 0 < ap.1 := by
  classical
  rcases exists_nonneg_C_mul_sub_natDegree_lt_of_le hfpos hgpos hgdeg
      hfg.natDegree_le with ⟨c, hc_nonneg, hcdeg⟩
  let roots : List ℝ := g.roots.toFinset.toList
  have hroots_nodup : roots.Nodup := Finset.nodup_toList _
  have hroot : ∀ u ∈ roots, g.IsRoot u := by
    intro u hu
    exact (mem_roots hfg.2.1.1).mp
      (Multiset.mem_toFinset.mp (Finset.mem_toList.mp hu))
  have hdata : ∀ u ∈ roots, ∃ a : ℝ, ∃ q : ℝ[X],
      0 ≤ a ∧
        g = (X - C u) * q ∧
        IsGWKreinSummand g q ∧
        (X - C u) ^ (g.rootMultiplicity u) ∣
          f - C c * g - C a * q := by
    intro u hu
    exact exists_kreinCoefficientData_nonneg_of_right_isRoot hfg hfpos hgpos
      hfg.2.1.2 c (hroot u hu)
  choose a q ha hfactor hsummand hgain using hdata
  let a' : ℝ → ℝ := fun u => if hu : u ∈ roots then a u hu else 0
  let q' : ℝ → ℝ[X] := fun u => if hu : u ∈ roots then q u hu else 0
  let tail : List (ℝ × ℝ[X]) := roots.map fun u => (a' u, q' u)
  let l : List (ℝ × ℝ[X]) := (c, g) :: tail
  have hfactor' : ∀ u ∈ roots, g = (X - C u) * q' u := by
    intro u hu
    simp [q', hu, hfactor u hu]
  have hgain' : ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ f - C c * g - C (a' u) * q' u := by
    intro u hu
    simp [a', q', hu, hgain u hu]
  have hdiv_roots : ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣
        f - C c * g - weightedSum tail := by
    simpa [tail] using
      fullRootMultiplicity_dvd_sub_weightedSum_rootDeleted
        hfg.2.1.1 roots hroots_nodup a' q' hfactor' hgain'
  have hdiv_all_roots : ∀ u ∈ g.roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣
        f - C c * g - weightedSum tail := by
    intro u hu
    exact hdiv_roots u (by
      rw [Finset.mem_toList, Multiset.mem_toFinset]
      exact hu)
  have hdiv : g ∣ f - C c * g - weightedSum tail :=
    dvd_of_roots_fullRootMultiplicity_dvd hfg.2.1.1 hfg.2.1.2 hdiv_all_roots
  have htail_deg : (weightedSum tail).natDegree < g.natDegree := by
    simpa [tail] using
      natDegree_weightedSum_deletedFactors_lt hfg.2.1.1 hgdeg roots a' q' hfactor'
  have hresdeg : (f - C c * g - weightedSum tail).natDegree < g.natDegree :=
    natDegree_sub_lt_of_both_lt hgdeg hcdeg htail_deg
  have hzero : f - C c * g - weightedSum tail = 0 :=
    eq_zero_of_dvd_of_natDegree_lt hfg.2.1.1 hdiv hresdeg
  have hf : f = weightedSum l := by
    have hsub : f - C c * g = weightedSum tail := sub_eq_zero.mp hzero
    change f = weightedSum ((c, g) :: tail)
    rw [weightedSum_cons, ← hsub]
    ring
  have hnonneg : ∀ ap ∈ l, 0 ≤ ap.1 := by
    intro ap hap
    change ap ∈ (c, g) :: tail at hap
    rcases List.mem_cons.mp hap with hhead | htail_mem
    · rcases hhead with rfl
      exact hc_nonneg
    · change ap ∈ roots.map (fun u => (a' u, q' u)) at htail_mem
      rcases List.mem_map.mp htail_mem with ⟨u, hu, rfl⟩
      simp [a', hu, ha u hu]
  have hsummand_all : ∀ ap ∈ l, IsGWKreinSummand g ap.2 := by
    intro ap hap
    change ap ∈ (c, g) :: tail at hap
    rcases List.mem_cons.mp hap with hhead | htail_mem
    · rcases hhead with rfl
      exact Or.inl rfl
    · change ap ∈ roots.map (fun u => (a' u, q' u)) at htail_mem
      rcases List.mem_map.mp htail_mem with ⟨u, hu, rfl⟩
      simp [q', hu, hsummand u hu]
  have hex : ∃ ap ∈ l, 0 < ap.1 := by
    by_contra hnot
    have hzero_weights : ∀ ap ∈ l, ap.1 = 0 := by
      intro ap hap
      exact le_antisymm
        (not_lt.mp fun hpos => hnot ⟨ap, hap, hpos⟩)
        (hnonneg ap hap)
    have hws0 : weightedSum l = 0 :=
      weightedSum_eq_zero_of_forall_coeff_zero l hzero_weights
    exact hfg.1.1 (by rw [hf, hws0])
  exact ⟨l, hf, hnonneg, hsummand_all, hex⟩

/-- Constant-degree Garloff--Wagner Lemma 7 package.  If `g` is constant, then
`Prec f g` forces `f` to be constant as well, so `f` is a positive scalar
multiple of the Krein summand `g`. -/
theorem exists_kreinSummandExpansion_nonneg_right_of_natDegree_eq_zero {f g : ℝ[X]}
    (hfg : Prec f g) (hfpos : HasPosLeadingCoeff f)
    (hgpos : HasPosLeadingCoeff g) (hgdeg : g.natDegree = 0) :
    ∃ l : List (ℝ × ℝ[X]),
      f = weightedSum l ∧
        (∀ ap ∈ l, 0 ≤ ap.1) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        ∃ ap ∈ l, 0 < ap.1 := by
  have hfdeg : f.natDegree = 0 := by
    have hfg_le := hfg.natDegree_le
    lia
  let c : ℝ := f.leadingCoeff / g.leadingCoeff
  have hc_pos : 0 < c := by
    dsimp [c]
    exact div_pos hfpos hgpos
  have hfC : f = C f.leadingCoeff := by
    have hfC0 : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hfdeg
    have hlc : f.leadingCoeff = f.coeff 0 := by rw [leadingCoeff, hfdeg]
    simpa [hlc] using hfC0
  have hgC : g = C g.leadingCoeff := by
    have hgC0 : g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero hgdeg
    have hlc : g.leadingCoeff = g.coeff 0 := by rw [leadingCoeff, hgdeg]
    simpa [hlc] using hgC0
  have hscalar : C c * g = f := by
    rw [hgC, hfC, ← C_mul]
    congr 1
    dsimp [c]
    field_simp [ne_of_gt hgpos]
  refine ⟨[(c, g)], ?_, ?_, ?_, ?_⟩
  · simpa [weightedSum_cons] using hscalar.symm
  · intro ap hap
    rcases List.mem_singleton.mp hap with rfl
    exact hc_pos.le
  · intro ap hap
    rcases List.mem_singleton.mp hap with rfl
    exact Or.inl rfl
  · exact ⟨(c, g), List.mem_singleton_self _, hc_pos⟩

/-- Normalizing a nonzero polynomial by its leading coefficient makes it
standard, without changing its roots. -/
lemma hasPosLeadingCoeff_C_inv_leadingCoeff_mul {p : ℝ[X]} (hp0 : p ≠ 0) :
    HasPosLeadingCoeff (C p.leadingCoeff⁻¹ * p) := by
  apply hasPosLeadingCoeff_of_monic
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  exact inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hp0)

/-- A Lemma 7/Krein expansion in root-deleted summands supplies the weighted
common-right hypotheses needed for the checked Theorem 11(c) package. -/
theorem gwJL_prec_of_kreinSummandExpansion
    {k : ℕ} {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hg0 : g ≠ 0) (hgs : g.Splits) (hgpos : HasPosLeadingCoeff g)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hsummand : ∀ ap ∈ l, IsGWKreinSummand g ap.2)
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    Prec (gwJL k f) (gwJL k g) :=
  gwJL_prec_of_rightWeightedExpansion hf hnonneg
    (fun ap hap => (hsummand ap hap).gwJL_prec hg0 hgs)
    (fun ap hap => ((hsummand ap hap).hasPosLeadingCoeff hgpos).gwJL k)
    hex

/-- The trivial one-term Krein expansion of the right polynomial itself. -/
theorem kreinSummandExpansion_self (g : ℝ[X]) :
    ∃ l : List (ℝ × ℝ[X]),
      g = weightedSum l ∧
        (∀ ap ∈ l, 0 ≤ ap.1) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        ∃ ap ∈ l, 0 < ap.1 := by
  refine ⟨[(1, g)], ?_, ?_, ?_, ?_⟩
  · simp [weightedSum_cons]
  · intro ap hap
    rcases List.mem_singleton.mp hap with rfl
    norm_num
  · intro ap hap
    rcases List.mem_singleton.mp hap with rfl
    exact Or.inl rfl
  · exact ⟨(1, g), List.mem_singleton_self _, by norm_num⟩

/-- Any individual Krein summand gives a one-term nonnegative expansion. -/
theorem kreinSummandExpansion_of_summand {g q : ℝ[X]}
    (h : IsGWKreinSummand g q) :
    ∃ l : List (ℝ × ℝ[X]),
      q = weightedSum l ∧
        (∀ ap ∈ l, 0 ≤ ap.1) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        ∃ ap ∈ l, 0 < ap.1 := by
  refine ⟨[(1, q)], ?_, ?_, ?_, ?_⟩
  · simp [weightedSum_cons]
  · intro ap hap
    rcases List.mem_singleton.mp hap with rfl
    norm_num
  · intro ap hap
    rcases List.mem_singleton.mp hap with rfl
    exact h
  · exact ⟨(1, q), List.mem_singleton_self _, by norm_num⟩

/-- Package raw list data as a Krein summand expansion.  This is the shape the
eventual coefficient proof of Lemma 7 should hand back once the coefficients
and deleted-root factors have been constructed. -/
theorem kreinSummandExpansion_of_weightedSum {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hsummand : ∀ ap ∈ l, IsGWKreinSummand g ap.2)
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    ∃ l : List (ℝ × ℝ[X]),
      f = weightedSum l ∧
        (∀ ap ∈ l, 0 ≤ ap.1) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        ∃ ap ∈ l, 0 < ap.1 :=
  ⟨l, hf, hnonneg, hsummand, hex⟩

/-- Lemma 7-facing interface for Theorem 11(c).  After normalizing the right
polynomial to be standard, the left polynomial should expand as a nonnegative
weighted sum of the right polynomial and its one-root-deleted factors. -/
def gwTheorem11PrecKreinSummandExpansionStatement : Prop :=
  ∀ {f g : ℝ[X]}, Prec f g → HasPosLeadingCoeff f → HasPosLeadingCoeff g →
    ∃ l : List (ℝ × ℝ[X]),
      f = weightedSum l ∧
        (∀ ap ∈ l, 0 ≤ ap.1) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        ∃ ap ∈ l, 0 < ap.1

theorem gwTheorem11Prec_of_kreinSummandExpansion
    (h : gwTheorem11PrecKreinSummandExpansionStatement) :
    gwTheorem11PrecStatement := by
  intro f g hfg k
  let sf : ℝ := f.leadingCoeff⁻¹
  let sg : ℝ := g.leadingCoeff⁻¹
  have hf0 : f ≠ 0 := hfg.1.1
  have hg0 : g ≠ 0 := hfg.2.1.1
  have hsf : sf ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hf0)
  have hsg : sg ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hg0)
  have hfg_scaled : Prec (C sf * f) (C sg * g) :=
    prec_C_mul_right (prec_C_mul_left hfg hsf) hsg
  have hsf_pos : HasPosLeadingCoeff (C sf * f) :=
    hasPosLeadingCoeff_C_inv_leadingCoeff_mul hf0
  have hsg_pos : HasPosLeadingCoeff (C sg * g) :=
    hasPosLeadingCoeff_C_inv_leadingCoeff_mul hg0
  rcases h (f := C sf * f) (g := C sg * g) hfg_scaled hsf_pos hsg_pos with
    ⟨l, hf, hnonneg, hsummand, hex⟩
  have hscaled :
      Prec (gwJL k (C sf * f)) (gwJL k (C sg * g)) :=
    gwJL_prec_of_kreinSummandExpansion hf hfg_scaled.2.1.1 hfg_scaled.2.1.2
      hsg_pos hnonneg hsummand hex
  have hscaled' : Prec (C sf * gwJL k f) (C sg * gwJL k g) := by
    simpa [gwJL_C_mul] using hscaled
  have hleft :
      Prec (gwJL k f) (C sg * gwJL k g) := by
    have htmp := prec_C_mul_left hscaled' (inv_ne_zero hsf)
    have hscale : C sf⁻¹ * (C sf * gwJL k f) = gwJL k f := by
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hsf, C_1, one_mul]
    simpa [hscale] using htmp
  have hright := prec_C_mul_right hleft (inv_ne_zero hsg)
  have hscale : C sg⁻¹ * (C sg * gwJL k g) = gwJL k g := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hsg, C_1, one_mul]
  simpa [hscale] using hright

/-- Garloff--Wagner, Theorem 11(c), reduced to the checked Krein expansion
package. -/
theorem gwTheorem11PrecKreinSummandExpansion :
    gwTheorem11PrecKreinSummandExpansionStatement := by
  intro f g hfg hfpos hgpos
  by_cases hgdeg0 : g.natDegree = 0
  · exact exists_kreinSummandExpansion_nonneg_right_of_natDegree_eq_zero hfg hfpos
      hgpos hgdeg0
  · exact exists_kreinSummandExpansion_nonneg_right_of_pos_natDegree hfg hfpos
      hgpos (Nat.pos_of_ne_zero hgdeg0)

/-- Garloff--Wagner, Theorem 11(c), in the local `Prec` orientation. -/
theorem gwTheorem11Prec :
    gwTheorem11PrecStatement :=
  gwTheorem11Prec_of_kreinSummandExpansion gwTheorem11PrecKreinSummandExpansion

/-! ## Theorem 12 infrastructure -/

/-- Degree-zero polynomials are in zero-aware proper position. -/
theorem prec0_of_natDegree_eq_zero {p q : ℝ[X]}
    (hpdeg : p.natDegree = 0) (hqdeg : q.natDegree = 0) :
    Prec0 p q := by
  by_cases hp0 : p = 0
  · exact Or.inl hp0
  by_cases hq0 : q = 0
  · exact Or.inr (Or.inl hq0)
  exact
    (prec_degree_zero_degree_zero hp0
      (Polynomial.Splits.of_natDegree_eq_zero hpdeg) hq0
      (Polynomial.Splits.of_natDegree_eq_zero hqdeg) hpdeg hqdeg).toPrec0

namespace IsGWKreinSummand

/-- Krein summands of a PF polynomial are in proper position with the parent. -/
theorem prec {g q : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg0 : g ≠ 0) (hgs : g.Splits) :
    Prec q g := by
  rcases h with hself | ⟨u, hfactor⟩
  · rw [hself]
    exact prec_refl hg0 hgs
  · obtain ⟨hq0, hqs⟩ :=
      (show IsGWKreinSummand g q from Or.inr ⟨u, hfactor⟩).ne_zero_and_splits
        hg0 hgs
    rw [hfactor]
    exact prec_self_X_sub_C_mul hq0 hqs u

/-- Zero-aware form of `IsGWKreinSummand.prec`. -/
theorem prec0 {g q : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg0 : g ≠ 0) (hgs : g.Splits) :
    Prec0 q g :=
  (h.prec hg0 hgs).toPrec0

/-- Krein summands of a PF polynomial are PF. -/
theorem isPFPolynomial {g q : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg : IsPFPolynomial g) :
    IsPFPolynomial q := by
  rcases h with hself | ⟨u, hfactor⟩
  · simpa [hself] using hg
  · exact hg.of_X_sub_C_mul_factor hfactor

end IsGWKreinSummand

/-- Constant right input base case for Theorem 12(b). -/
theorem gwSchurProduct_prec0_of_right_natDegree_eq_zero
    (f g p : ℝ[X]) (hpdeg : p.natDegree = 0) :
    Prec0 (gwSchurProduct f p) (gwSchurProduct g p) := by
  have hfdeg : (gwSchurProduct f p).natDegree = 0 := by
    exact le_antisymm
      ((natDegree_gwSchurProduct_le_right f p).trans (le_of_eq hpdeg))
      (Nat.zero_le _)
  have hgdeg : (gwSchurProduct g p).natDegree = 0 := by
    exact le_antisymm
      ((natDegree_gwSchurProduct_le_right g p).trans (le_of_eq hpdeg))
      (Nat.zero_le _)
  exact prec0_of_natDegree_eq_zero hfdeg hgdeg

/-- Constant right input base case for Theorem 12(a). -/
theorem gwSchurProduct_pf_of_right_natDegree_eq_zero {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hpdeg : p.natDegree = 0) :
    IsPFPolynomial (gwSchurProduct f p) := by
  have hdeg : (gwSchurProduct f p).natDegree = 0 := by
    exact le_antisymm
      ((natDegree_gwSchurProduct_le_right f p).trans (le_of_eq hpdeg))
      (Nat.zero_le _)
  exact IsPFPolynomial.of_realRooted_nonneg
    (hf.hasNonnegCoeffs.gwSchurProduct hp.hasNonnegCoeffs)
    (Polynomial.Splits.of_natDegree_eq_zero hdeg)

/-- Theorem 12(a) induction step in relational form: if the Schur product of
`D f` with `p` precedes the Schur product of `f` with `p`, then multiplying
the right input by a nonpositive linear factor keeps the previous product as a
left interleaver. -/
theorem gwSchurProduct_prec0_right_linearFactor_of_derivative_prec0
    {f p : ℝ[X]} {u : ℝ}
    (hu : u ≤ 0)
    (hder :
      Prec0 (gwSchurProduct (gwD f) p) (gwSchurProduct f p))
    (hF : IsPFPolynomial (gwSchurProduct f p))
    (hD : IsPFPolynomial (gwSchurProduct (gwD f) p)) :
    Prec0 (gwSchurProduct f p) (gwSchurProduct f ((X - C u) * p)) := by
  have hX :
      Prec0 (gwSchurProduct f p)
        (X * gwSchurProduct (gwD f) p) :=
    prec0_mul_X_of_prec0 hder hD.hasNonnegCoeffs hF.hasNonnegCoeffs
  have hself : Prec0 (gwSchurProduct f p) (gwSchurProduct f p) :=
    hF.prec0_self
  have hcombo :
      Prec0 (gwSchurProduct f p)
        (C (1 : ℝ) * (X * gwSchurProduct (gwD f) p) +
          C (-u) * gwSchurProduct f p) :=
    prec0_nonneg_combo_right_of_common_left_of_nonneg hX hself
      (hD.X_mul.hasNonnegCoeffs) hF.hasNonnegCoeffs zero_le_one (by linarith)
  rw [gwSchurProduct_X_sub_C_mul_right]
  simpa [sub_eq_add_neg] using hcombo

/-- PF-preservation form of
`gwSchurProduct_prec0_right_linearFactor_of_derivative_prec0`. -/
theorem gwSchurProduct_pf_right_linearFactor_of_derivative_prec0
    {f p : ℝ[X]} {u : ℝ}
    (hu : u ≤ 0)
    (hder :
      Prec0 (gwSchurProduct (gwD f) p) (gwSchurProduct f p))
    (hF : IsPFPolynomial (gwSchurProduct f p))
    (hD : IsPFPolynomial (gwSchurProduct (gwD f) p)) :
    IsPFPolynomial (gwSchurProduct f ((X - C u) * p)) := by
  let F : ℝ[X] := gwSchurProduct f p
  let D : ℝ[X] := gwSchurProduct (gwD f) p
  have hprec :
      Prec0 F (gwSchurProduct f ((X - C u) * p)) :=
    gwSchurProduct_prec0_right_linearFactor_of_derivative_prec0
      hu hder hF hD
  have htarget_nn : HasNonnegCoeffs (gwSchurProduct f ((X - C u) * p)) := by
    rw [gwSchurProduct_X_sub_C_mul_right, sub_eq_add_neg]
    have hneg :
        HasNonnegCoeffs (-(C u * gwSchurProduct f p)) := by
      simpa [neg_mul, C_neg] using
        nonnegCoeffs_C_mul (by linarith : 0 ≤ -u) hF.hasNonnegCoeffs
    exact hD.hasNonnegCoeffs.X_mul.add hneg
  by_cases hF0 : F = 0
  · rw [gwSchurProduct_X_sub_C_mul_right]
    change IsPFPolynomial (X * D - C u * F)
    rw [hF0, mul_zero, sub_zero]
    exact hD.X_mul
  · rcases hprec with hleft0 | hright0 | hstrict
    · exact False.elim (hF0 hleft0)
    · simpa [hright0] using IsPFPolynomial.zero
    · exact IsPFPolynomial.of_realRooted_nonneg htarget_nn hstrict.2.1.2

/-- Multiplying the left polynomial in a zero-aware `Prec0` relation by a
nonnegative scalar preserves the relation. -/
theorem prec0_C_mul_left_of_nonneg {f g : ℝ[X]}
    (h : Prec0 f g) {a : ℝ} (ha : 0 ≤ a) :
    Prec0 (C a * f) g := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp [prec0_zero_left]
  rcases h with hf0 | hg0 | hprec
  · simp [hf0, prec0_zero_left]
  · simpa [hg0] using prec0_zero_right (C a * f)
  · exact (prec_C_mul_left hprec ha_pos.ne').toPrec0

/-- Adding two nonnegative-coefficient left summands with a common right bound
preserves zero-aware proper position. -/
theorem prec0_add_left_of_common_right_of_nonneg {p q h : ℝ[X]}
    (hph : Prec0 p h) (hqh : Prec0 q h)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q) :
    Prec0 (p + q) h := by
  classical
  have hsum :
      (Finset.univ.sum (fun b : Bool => cond b p q)) = p + q := by
    simp
  rw [← hsum]
  apply prec0_finsetSum_right_of_nonneg
  · intro b _
    cases b <;> simp [hph, hqh]
  · intro b _
    cases b <;> simp [hpnn, hqnn]

theorem HasNonnegCoeffs.weightedSum :
    ∀ l : List (ℝ × ℝ[X]),
      (∀ ap ∈ l, 0 ≤ ap.1) →
      (∀ ap ∈ l, HasNonnegCoeffs ap.2) →
      HasNonnegCoeffs (weightedSum l)
  | [], _, _ => by
      intro n
      simp
  | (a, p) :: l, hnonneg, hnn => by
      have ha : 0 ≤ a := hnonneg (a, p) (by simp)
      have hp : HasNonnegCoeffs p := hnn (a, p) (by simp)
      have htail_nonneg : ∀ ap ∈ l, 0 ≤ ap.1 :=
        fun ap hap => hnonneg ap (by simp [hap])
      have htail_nn : ∀ ap ∈ l, HasNonnegCoeffs ap.2 :=
        fun ap hap => hnn ap (by simp [hap])
      simpa [weightedSum_cons] using
        (nonnegCoeffs_C_mul ha hp).add
          (HasNonnegCoeffs.weightedSum l htail_nonneg htail_nn)

/-- Zero-aware weighted common-right cone closure. -/
theorem prec0_weightedSum_right_of_nonneg :
    ∀ (l : List (ℝ × ℝ[X])) (h : ℝ[X]),
      (∀ ap ∈ l, 0 ≤ ap.1) →
      (∀ ap ∈ l, Prec0 ap.2 h) →
      (∀ ap ∈ l, HasNonnegCoeffs ap.2) →
      Prec0 (weightedSum l) h
  | [], h, _, _, _ => by
      simp [prec0_zero_left]
  | (a, p) :: l, h, hnonneg, hprec, hnn => by
      have ha : 0 ≤ a := hnonneg (a, p) (by simp)
      have hp_prec : Prec0 p h := hprec (a, p) (by simp)
      have hp_nn : HasNonnegCoeffs p := hnn (a, p) (by simp)
      have htail_nonneg : ∀ ap ∈ l, 0 ≤ ap.1 :=
        fun ap hap => hnonneg ap (by simp [hap])
      have htail_prec : ∀ ap ∈ l, Prec0 ap.2 h :=
        fun ap hap => hprec ap (by simp [hap])
      have htail_nn : ∀ ap ∈ l, HasNonnegCoeffs ap.2 :=
        fun ap hap => hnn ap (by simp [hap])
      have hhead_prec : Prec0 (C a * p) h :=
        prec0_C_mul_left_of_nonneg hp_prec ha
      have htail_prec_sum : Prec0 (weightedSum l) h :=
        prec0_weightedSum_right_of_nonneg l h htail_nonneg htail_prec htail_nn
      have hhead_nn : HasNonnegCoeffs (C a * p) :=
        nonnegCoeffs_C_mul ha hp_nn
      have htail_sum_nn : HasNonnegCoeffs (weightedSum l) :=
        HasNonnegCoeffs.weightedSum l htail_nonneg htail_nn
      simpa [weightedSum_cons] using
        prec0_add_left_of_common_right_of_nonneg hhead_prec htail_prec_sum
          hhead_nn htail_sum_nn

theorem gwSchurProduct_weightedSum_left :
    ∀ (l : List (ℝ × ℝ[X])) (p : ℝ[X]),
      gwSchurProduct (weightedSum l) p =
        weightedSum (l.map fun ap => (ap.1, gwSchurProduct ap.2 p))
  | [], _ => by
      simp
  | (a, q) :: l, p => by
      rw [weightedSum_cons, gwSchurProduct_add_left, gwSchurProduct_C_mul_left,
        gwSchurProduct_weightedSum_left l p]
      rfl

/-- Apply the Schur product to a nonnegative weighted expansion whose summands
all precede the same right Schur product. -/
theorem gwSchurProduct_prec0_of_weightedSum_right {f g p : ℝ[X]}
    {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hprec :
      ∀ ap ∈ l, Prec0 (gwSchurProduct ap.2 p) (gwSchurProduct g p))
    (hnn : ∀ ap ∈ l, HasNonnegCoeffs (gwSchurProduct ap.2 p)) :
    Prec0 (gwSchurProduct f p) (gwSchurProduct g p) := by
  rw [hf, gwSchurProduct_weightedSum_left]
  apply prec0_weightedSum_right_of_nonneg
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hnonneg ap0 hap0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hprec ap0 hap0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hnn ap0 hap0

/-- Theorem 12(b) reducer after Lemma 7 has expanded the left input into
Krein summands of the right input. -/
theorem gwSchurProduct_prec0_of_kreinSummandExpansion {f g p : ℝ[X]}
    {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hsummand : ∀ ap ∈ l, IsGWKreinSummand g ap.2)
    (hprec :
      ∀ q : ℝ[X], IsGWKreinSummand g q →
        Prec0 (gwSchurProduct q p) (gwSchurProduct g p))
    (hnn :
      ∀ q : ℝ[X], IsGWKreinSummand g q →
        HasNonnegCoeffs (gwSchurProduct q p)) :
    Prec0 (gwSchurProduct f p) (gwSchurProduct g p) :=
  gwSchurProduct_prec0_of_weightedSum_right hf hnonneg
    (fun ap hap => hprec ap.2 (hsummand ap hap))
    (fun ap hap => hnn ap.2 (hsummand ap hap))

/-- A PF polynomial's derivative precedes the polynomial itself in the
zero-aware orientation. -/
theorem IsPFPolynomial.derivative_prec0_self {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    Prec0 p.derivative p := by
  by_cases hp0 : p = 0
  · rw [hp0, derivative_zero]
    exact prec0_zero_left 0
  have hps := hp.ne_zero_and_splits hp0
  by_cases hdeg0 : p.natDegree = 0
  · have hder0 : p.derivative = 0 :=
      derivative_eq_zero_of_natDegree_eq_zero hdeg0
    rw [hder0]
    exact prec0_zero_left p
  by_cases hdeg1 : p.natDegree = 1
  · have hder_ne : p.derivative ≠ 0 :=
      Polynomial.derivative_ne_zero.mpr hdeg0
    have hder_deg0 : p.derivative.natDegree = 0 := by
      rw [p.natDegree_derivative, hdeg1]
    exact
      (prec_degree_zero_right_of_degree_one hder_ne
        (Polynomial.Splits.of_natDegree_eq_zero hder_deg0) hp0 hps.2 hder_deg0
        hdeg1).toPrec0
  · have hdeg2 : 2 ≤ p.natDegree := by lia
    exact (derivative_interlaces hps.2 hdeg2).toPrec.toPrec0

/-- The first one-variable relation in Garloff--Wagner's double-deleted
paragraph: for `u <= 0`, `(1 - uD)Lp` precedes `Lp`. -/
theorem gwL_sub_C_mul_gwD_gwL_prec0_self {p : ℝ[X]} {u : ℝ}
    (hp : IsPFPolynomial p) (hu : u ≤ 0) :
    Prec0 (gwL p - C u * gwD (gwL p)) (gwL p) := by
  have hpL : IsPFPolynomial (gwL p) := by
    simpa [gwJL_zero_apply] using gwTheorem11PF hp 0
  have hder :
      Prec0 (gwD (gwL p)) (gwL p) := by
    simpa [gwD] using hpL.derivative_prec0_self
  have hscaled :
      Prec0 (C (-u) * gwD (gwL p)) (gwL p) :=
    prec0_C_mul_left_of_nonneg hder (by linarith)
  have hDnn : HasNonnegCoeffs (gwD (gwL p)) := by
    simpa [gwD] using hpL.derivative.hasNonnegCoeffs
  have hscaled_nn :
      HasNonnegCoeffs (C (-u) * gwD (gwL p)) :=
    nonnegCoeffs_C_mul (by linarith : 0 ≤ -u) hDnn
  have hsum :
      Prec0 (gwL p + C (-u) * gwD (gwL p)) (gwL p) :=
    prec0_add_left_of_common_right_of_nonneg hpL.prec0_self hscaled
      hpL.hasNonnegCoeffs hscaled_nn
  simpa [sub_eq_add_neg, C_neg, neg_mul] using hsum

/-- PF-cone form of `gwL_sub_C_mul_gwD_gwL_prec0_self`. -/
theorem gwL_sub_C_mul_gwD_gwL_pf {p : ℝ[X]} {u : ℝ}
    (hp : IsPFPolynomial p) (hu : u ≤ 0) :
    IsPFPolynomial (gwL p - C u * gwD (gwL p)) := by
  let T : ℝ[X] := gwL p - C u * gwD (gwL p)
  have hpL : IsPFPolynomial (gwL p) := by
    simpa [gwJL_zero_apply] using gwTheorem11PF hp 0
  have hprec : Prec0 T (gwL p) :=
    gwL_sub_C_mul_gwD_gwL_prec0_self hp hu
  have hDnn : HasNonnegCoeffs (gwD (gwL p)) := by
    simpa [gwD] using hpL.derivative.hasNonnegCoeffs
  have hTnn : HasNonnegCoeffs T := by
    change HasNonnegCoeffs (gwL p - C u * gwD (gwL p))
    have hscaled_nn :
        HasNonnegCoeffs (C (-u) * gwD (gwL p)) :=
      nonnegCoeffs_C_mul (by linarith : 0 ≤ -u) hDnn
    simpa [sub_eq_add_neg, C_neg, neg_mul] using
      hpL.hasNonnegCoeffs.add hscaled_nn
  by_cases hT0 : T = 0
  · simpa [T, hT0] using IsPFPolynomial.zero
  rcases hprec with hleft0 | hright0 | hstrict
  · exact False.elim (hT0 hleft0)
  · have hp0 : p = 0 := (gwL_eq_zero_iff p).1 hright0
    have hTzero : T = 0 := by
      simp [T, hp0, gwL_zero, gwD_zero]
    exact False.elim (hT0 hTzero)
  · exact IsPFPolynomial.of_realRooted_nonneg hTnn hstrict.1.2

/-- Theorem 12(a), zero-aware PF-cone form for the factorial Schur product. -/
def gwSchurProductPFStatement : Prop :=
  ∀ {f p : ℝ[X]},
    IsPFPolynomial f →
    IsPFPolynomial p →
    IsPFPolynomial (gwSchurProduct f p)

/-- Theorem 12(b), one fixed Schur-product factor, in the local orientation. -/
def gwSchurProductPrecStatement : Prop :=
  ∀ {f g p : ℝ[X]},
    IsPFPolynomial f →
    IsPFPolynomial g →
    IsPFPolynomial p →
    Prec f g →
    Prec0 (gwSchurProduct f p) (gwSchurProduct g p)

theorem gwSchurProductPF_of_prec
    (h : gwSchurProductPrecStatement) :
    gwSchurProductPFStatement := by
  intro f p hf hp
  by_cases hf0 : f = 0
  · simpa [hf0] using IsPFPolynomial.zero
  have hfs := hf.ne_zero_and_splits hf0
  exact IsPFPolynomial.of_prec0_self
    (hf.hasNonnegCoeffs.gwSchurProduct hp.hasNonnegCoeffs)
    (h hf hf hp (prec_refl hfs.1 hfs.2))

theorem gwSchurProductPrec0_of_prec
    (h : gwSchurProductPrecStatement) :
    ∀ {f g p : ℝ[X]},
      IsPFPolynomial f →
      IsPFPolynomial g →
      IsPFPolynomial p →
      Prec0 f g →
      Prec0 (gwSchurProduct f p) (gwSchurProduct g p) := by
  intro f g p hf hg hp hfg
  rcases hfg with hf0 | hg0 | hstrict
  · simpa [hf0] using prec0_zero_left (gwSchurProduct g p)
  · simpa [hg0] using prec0_zero_right (gwSchurProduct f p)
  · exact h hf hg hp hstrict

theorem gwSchurProduct_derivative_prec0_self_of_prec
    (h : gwSchurProductPrecStatement) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) :
    Prec0 (gwSchurProduct (gwD f) p) (gwSchurProduct f p) := by
  simpa [gwD] using
    gwSchurProductPrec0_of_prec h hf.derivative hf hp hf.derivative_prec0_self

/-- Symmetric form of the Theorem 12(a) linear-factor step, used for
one-root-deleted Krein summands in Theorem 12(b). -/
theorem gwSchurProduct_prec0_left_linearFactor_of_derivative_prec0
    {q p : ℝ[X]} {u : ℝ}
    (hu : u ≤ 0)
    (hder :
      Prec0 (gwSchurProduct (gwD p) q) (gwSchurProduct p q))
    (hF : IsPFPolynomial (gwSchurProduct p q))
    (hD : IsPFPolynomial (gwSchurProduct (gwD p) q)) :
    Prec0 (gwSchurProduct q p) (gwSchurProduct ((X - C u) * q) p) := by
  rw [gwSchurProduct_comm q p, gwSchurProduct_comm ((X - C u) * q) p]
  exact gwSchurProduct_prec0_right_linearFactor_of_derivative_prec0
    hu hder hF hD

/-- If `q` is obtained from a PF polynomial `g` by deleting one linear root
factor, then the Schur product with `q` precedes the Schur product with `g`,
assuming the derivative-product recursive relation for the other factor. -/
theorem gwSchurProduct_prec0_of_kreinDeletedFactor
    {g q p : ℝ[X]} {u : ℝ}
    (hg : IsPFPolynomial g) (hfactor : g = (X - C u) * q)
    (hder :
      Prec0 (gwSchurProduct (gwD p) q) (gwSchurProduct p q))
    (hF : IsPFPolynomial (gwSchurProduct p q))
    (hD : IsPFPolynomial (gwSchurProduct (gwD p) q)) :
    Prec0 (gwSchurProduct q p) (gwSchurProduct g p) := by
  by_cases hq0 : q = 0
  · have hg0 : g = 0 := by
      rw [hfactor, hq0, mul_zero]
    simp [hq0, hg0, prec0_zero_left]
  have hg0 : g ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero (X_sub_C_ne_zero u) hq0
  have hu_root : g.IsRoot u := by
    rw [hfactor, Polynomial.IsRoot.def, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hu : u ≤ 0 :=
    hg.roots_nonpos u ((mem_roots hg0).mpr hu_root)
  simpa [hfactor] using
    gwSchurProduct_prec0_left_linearFactor_of_derivative_prec0
      (q := q) (p := p) (u := u) hu hder hF hD

namespace IsGWKreinSummand

/-- Per-summand Theorem 12(b) step for a Krein summand of the right input. -/
theorem gwSchurProduct_prec0_of_derivative
    {g q p : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg : IsPFPolynomial g)
    (hgp : IsPFPolynomial (gwSchurProduct g p))
    (hder :
      Prec0 (gwSchurProduct (gwD p) q) (gwSchurProduct p q))
    (hF : IsPFPolynomial (gwSchurProduct p q))
    (hD : IsPFPolynomial (gwSchurProduct (gwD p) q)) :
    Prec0 (gwSchurProduct q p) (gwSchurProduct g p) := by
  rcases h with hself | ⟨u, hfactor⟩
  · simpa [hself] using hgp.prec0_self
  · exact gwSchurProduct_prec0_of_kreinDeletedFactor hg hfactor hder hF hD

end IsGWKreinSummand

/-- Theorem 12(b) reducer in the exact form produced by the Lemma 7 expansion:
it remains only to discharge the recursive derivative/PF obligations for each
Krein summand. -/
theorem gwSchurProduct_prec0_of_kreinSummandExpansion_of_derivative
    {f g p : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hsummand : ∀ ap ∈ l, IsGWKreinSummand g ap.2)
    (hg : IsPFPolynomial g)
    (hgp : IsPFPolynomial (gwSchurProduct g p))
    (hder :
      ∀ (q : ℝ[X]) (u : ℝ), g = (X - C u) * q →
        Prec0 (gwSchurProduct (gwD p) q) (gwSchurProduct p q))
    (hF :
      ∀ (q : ℝ[X]) (u : ℝ), g = (X - C u) * q →
        IsPFPolynomial (gwSchurProduct p q))
    (hD :
      ∀ (q : ℝ[X]) (u : ℝ), g = (X - C u) * q →
        IsPFPolynomial (gwSchurProduct (gwD p) q)) :
    Prec0 (gwSchurProduct f p) (gwSchurProduct g p) :=
  gwSchurProduct_prec0_of_kreinSummandExpansion hf hnonneg hsummand
    (fun q hq => by
      rcases hq with hself | ⟨u, hfactor⟩
      · simpa [hself] using hgp.prec0_self
      · exact gwSchurProduct_prec0_of_kreinDeletedFactor hg hfactor
          (hder q u hfactor) (hF q u hfactor) (hD q u hfactor))
    (fun q hq => by
      rcases hq with hself | ⟨u, hfactor⟩
      · simpa [hself] using hgp.hasNonnegCoeffs
      · simpa [gwSchurProduct_comm q p] using
          (hF q u hfactor).hasNonnegCoeffs)

/-- Garloff--Wagner, Theorem 12, for the factorial Schur product.

The induction is over the total degree of the two active Schur-product
arguments.  At each measure we first prove PF preservation, then use that
same-measure result as the common-right PF input for the fixed-factor
proper-position statement.  All derivative and one-root-deleted calls have
strictly smaller total degree. -/
theorem gwSchurProductPFAndPrec :
    gwSchurProductPFStatement ∧ gwSchurProductPrecStatement := by
  classical
  let P : ℕ → Prop := fun n =>
    (∀ {f p : ℝ[X]},
      IsPFPolynomial f → IsPFPolynomial p →
        f.natDegree + p.natDegree = n →
          IsPFPolynomial (gwSchurProduct f p)) ∧
    (∀ {f g p : ℝ[X]},
      IsPFPolynomial f → IsPFPolynomial g → IsPFPolynomial p →
        Prec0 f g → g.natDegree + p.natDegree = n →
          Prec0 (gwSchurProduct f p) (gwSchurProduct g p))
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        have hA_lt :
            ∀ {f p : ℝ[X]},
              IsPFPolynomial f → IsPFPolynomial p →
                f.natDegree + p.natDegree < n →
                  IsPFPolynomial (gwSchurProduct f p) := by
          intro f p hf hp hlt
          exact (ih (f.natDegree + p.natDegree) hlt).1 hf hp rfl
        have hB_lt :
            ∀ {f g p : ℝ[X]},
              IsPFPolynomial f → IsPFPolynomial g → IsPFPolynomial p →
                Prec0 f g → g.natDegree + p.natDegree < n →
                  Prec0 (gwSchurProduct f p) (gwSchurProduct g p) := by
          intro f g p hf hg hp hfg hlt
          exact (ih (g.natDegree + p.natDegree) hlt).2 hf hg hp hfg rfl
        have hA :
            ∀ {f p : ℝ[X]},
              IsPFPolynomial f → IsPFPolynomial p →
                f.natDegree + p.natDegree = n →
                  IsPFPolynomial (gwSchurProduct f p) := by
          intro f p hf hp hmeasure
          by_cases hf0 : f = 0
          · rw [hf0, gwSchurProduct_zero_left]
            exact IsPFPolynomial.zero
          by_cases hp0 : p = 0
          · rw [hp0, gwSchurProduct_zero_right]
            exact IsPFPolynomial.zero
          by_cases hpdeg0 : p.natDegree = 0
          · exact gwSchurProduct_pf_of_right_natDegree_eq_zero hf hp hpdeg0
          rcases hp.exists_X_sub_C_factor_of_pos_natDegree
              (Nat.pos_of_ne_zero hpdeg0) with
            ⟨u, q, hu, hfactor, hq, hqdeg⟩
          have hF : IsPFPolynomial (gwSchurProduct f q) := by
            apply hA_lt hf hq
            rw [← hmeasure]
            lia
          have hD : IsPFPolynomial (gwSchurProduct (gwD f) q) := by
            have hfD : IsPFPolynomial (gwD f) := by
              change IsPFPolynomial f.derivative
              exact hf.derivative
            apply hA_lt hfD hq
            have hDdeg : (gwD f).natDegree ≤ f.natDegree := by
              simp [gwD]
            rw [← hmeasure]
            lia
          have hder :
              Prec0 (gwSchurProduct (gwD f) q) (gwSchurProduct f q) := by
            have hfD : IsPFPolynomial (gwD f) := by
              change IsPFPolynomial f.derivative
              exact hf.derivative
            have hprecD : Prec0 (gwD f) f := by
              change Prec0 f.derivative f
              exact hf.derivative_prec0_self
            apply hB_lt hfD hf hq hprecD
            rw [← hmeasure]
            lia
          rw [hfactor]
          exact gwSchurProduct_pf_right_linearFactor_of_derivative_prec0
            hu hder hF hD
        have hB :
            ∀ {f g p : ℝ[X]},
              IsPFPolynomial f → IsPFPolynomial g → IsPFPolynomial p →
                Prec0 f g → g.natDegree + p.natDegree = n →
                  Prec0 (gwSchurProduct f p) (gwSchurProduct g p) := by
          intro f g p hf hg hp hfg hmeasure
          rcases hfg with hf0 | hg0 | hstrict
          · rw [hf0, gwSchurProduct_zero_left]
            exact prec0_zero_left (gwSchurProduct g p)
          · rw [hg0, gwSchurProduct_zero_left]
            exact prec0_zero_right (gwSchurProduct f p)
          by_cases hpdeg0 : p.natDegree = 0
          · exact gwSchurProduct_prec0_of_right_natDegree_eq_zero f g p hpdeg0
          by_cases hgdeg0 : g.natDegree = 0
          · have hfdeg0 : f.natDegree = 0 := by
              have hstrict_le := hstrict.natDegree_le
              lia
            have hleftdeg : (gwSchurProduct f p).natDegree = 0 := by
              exact le_antisymm
                ((natDegree_gwSchurProduct_le_left f p).trans
                  (le_of_eq hfdeg0))
                (Nat.zero_le _)
            have hrightdeg : (gwSchurProduct g p).natDegree = 0 := by
              exact le_antisymm
                ((natDegree_gwSchurProduct_le_left g p).trans
                  (le_of_eq hgdeg0))
                (Nat.zero_le _)
            exact prec0_of_natDegree_eq_zero hleftdeg hrightdeg
          have hgp : IsPFPolynomial (gwSchurProduct g p) :=
            hA hg hp hmeasure
          have hfpos : HasPosLeadingCoeff f :=
            hf.hasNonnegCoeffs.pos_leadingCoeff hstrict.1.1
          have hgpos : HasPosLeadingCoeff g :=
            hg.hasNonnegCoeffs.pos_leadingCoeff hstrict.2.1.1
          rcases gwTheorem11PrecKreinSummandExpansion hstrict hfpos hgpos with
            ⟨l, hfexp, hnonneg, hsummand, _hex⟩
          have hdeleted :
              ∀ (q : ℝ[X]) (u : ℝ), g = (X - C u) * q →
                IsPFPolynomial q ∧ q.natDegree < g.natDegree := by
            intro q u hfactor
            have hq : IsPFPolynomial q := hg.of_X_sub_C_mul_factor hfactor
            have hq0 : q ≠ 0 := by
              intro hq0
              rw [hfactor, hq0, mul_zero] at hstrict
              exact hstrict.2.1.1 rfl
            have hqdeg : q.natDegree < g.natDegree := by
              rw [hfactor, natDegree_mul (X_sub_C_ne_zero u) hq0,
                natDegree_X_sub_C]
              lia
            exact ⟨hq, hqdeg⟩
          exact gwSchurProduct_prec0_of_kreinSummandExpansion_of_derivative
            hfexp hnonneg hsummand hg hgp
            (fun q u hfactor => by
              have hq := (hdeleted q u hfactor).1
              have hqdeg := (hdeleted q u hfactor).2
              have hpD : IsPFPolynomial (gwD p) := by
                change IsPFPolynomial p.derivative
                exact hp.derivative
              have hprecD : Prec0 (gwD p) p := by
                change Prec0 p.derivative p
                exact hp.derivative_prec0_self
              apply hB_lt hpD hp hq hprecD
              rw [← hmeasure]
              lia)
            (fun q u hfactor => by
              have hq := (hdeleted q u hfactor).1
              have hqdeg := (hdeleted q u hfactor).2
              apply hA_lt hp hq
              rw [← hmeasure]
              lia)
            (fun q u hfactor => by
              have hq := (hdeleted q u hfactor).1
              have hqdeg := (hdeleted q u hfactor).2
              have hpD : IsPFPolynomial (gwD p) := by
                change IsPFPolynomial p.derivative
                exact hp.derivative
              apply hA_lt hpD hq
              have hDdeg : (gwD p).natDegree ≤ p.natDegree := by
                simp [gwD]
              rw [← hmeasure]
              lia)
        exact ⟨hA, hB⟩
  constructor
  · intro f p hf hp
    exact (hP (f.natDegree + p.natDegree)).1 hf hp rfl
  · intro f g p hf hg hp hfg
    exact (hP (g.natDegree + p.natDegree)).2 hf hg hp hfg.toPrec0 rfl

theorem gwSchurProductPF :
    gwSchurProductPFStatement :=
  gwSchurProductPFAndPrec.1

/-- Ordinary Hadamard products preserve PF polynomials, obtained by applying
the Schur-product theorem to the `L`-normalized left input. -/
theorem gwHadamardProductPF {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) := by
  have hpL : IsPFPolynomial (gwL p) := by
    simpa [gwJL_zero_apply] using gwTheorem11PF hp 0
  simpa [gwSchurProduct_gwL_left] using gwSchurProductPF hpL hq

/-- The `L` operator preserves the PF cone. -/
theorem gwL_pf {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (gwL p) := by
  simpa [gwJL_zero_apply] using gwTheorem11PF hp 0

/-- The `L` operator preserves strict proper position. -/
theorem gwL_prec {f g : ℝ[X]} (hfg : Prec f g) :
    Prec (gwL f) (gwL g) := by
  simpa [gwJL_zero_apply] using gwTheorem11Prec hfg 0

/-- The `L` operator preserves zero-aware proper position. -/
theorem gwL_prec0 {f g : ℝ[X]} (hfg : Prec0 f g) :
    Prec0 (gwL f) (gwL g) := by
  rcases hfg with hf0 | hg0 | hstrict
  · rw [hf0, gwL_zero]
    exact prec0_zero_left (gwL g)
  · rw [hg0, gwL_zero]
    exact prec0_zero_right (gwL f)
  · exact (gwL_prec hstrict).toPrec0

theorem gwSchurProductPrec :
    gwSchurProductPrecStatement :=
  gwSchurProductPFAndPrec.2

theorem gwSchurProductPrec0 :
    ∀ {f g p : ℝ[X]},
      IsPFPolynomial f →
      IsPFPolynomial g →
      IsPFPolynomial p →
      Prec0 f g →
      Prec0 (gwSchurProduct f p) (gwSchurProduct g p) :=
  gwSchurProductPrec0_of_prec gwSchurProductPrec

/-- Symmetric fixed-factor form of `gwSchurProductPrec0`. -/
theorem gwSchurProductPrec0_left {f p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Prec0 p q) :
    Prec0 (gwSchurProduct f p) (gwSchurProduct f q) := by
  simpa [gwSchurProduct_comm f p, gwSchurProduct_comm f q] using
    gwSchurProductPrec0 hp hq hf hpq

/-- Ordinary Hadamard products preserve zero-aware proper position in a fixed
right factor, via `L` and the checked Schur-product theorem. -/
theorem gwHadamardProductPrec0 {f g p : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hp : IsPFPolynomial p)
    (hfg : Prec0 f g) :
    Prec0 (hadamardProduct f p) (hadamardProduct g p) := by
  have hfL : IsPFPolynomial (gwL f) := gwL_pf hf
  have hgL : IsPFPolynomial (gwL g) := gwL_pf hg
  have hfgL : Prec0 (gwL f) (gwL g) := gwL_prec0 hfg
  simpa [gwSchurProduct_gwL_left] using
    gwSchurProductPrec0 hfL hgL hp hfgL

/-- Symmetric fixed-factor form of `gwHadamardProductPrec0`. -/
theorem gwHadamardProductPrec0_left {f p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Prec0 p q) :
    Prec0 (hadamardProduct f p) (hadamardProduct f q) := by
  simpa [hadamardProduct_comm f p, hadamardProduct_comm f q] using
    gwHadamardProductPrec0 hp hq hf hpq

/-- The remaining local core of Garloff--Wagner, Theorem 4(b), after the
fixed-factor cases are discharged: both factors are one-root-deleted Krein
summands. -/
def gwSchurProductDoubleDeletedKreinStatement : Prop :=
  ∀ {g q f p : ℝ[X]} {u v : ℝ},
    IsPFPolynomial g →
    IsPFPolynomial q →
    g ≠ 0 →
    q ≠ 0 →
    g = (X - C u) * f →
    q = (X - C v) * p →
    Prec0 (gwSchurProduct f p) (gwSchurProduct g q)

/-- Ordinary-Hadamard version of the double-deleted core in the proof of
Garloff--Wagner, Theorem 4(b).  This is the statement matching the paragraph
which expands `((X - j)g) ⊙ ((X - u)q)` through `L`, `J`, and `D`. -/
def gwHadamardProductDoubleDeletedKreinStatement : Prop :=
  ∀ {g q f p : ℝ[X]} {u v : ℝ},
    IsPFPolynomial g →
    IsPFPolynomial q →
    g ≠ 0 →
    q ≠ 0 →
    g = (X - C u) * f →
    q = (X - C v) * p →
    Prec0 (hadamardProduct f p) (hadamardProduct g q)

/-- First Schur term in Garloff--Wagner's double-deleted paragraph: the base
Hadamard product precedes the `X`-shifted term. -/
theorem gwSchurProduct_firstDoubleDeletedTerm_prec0
    {f p : ℝ[X]} {u : ℝ}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hu : u ≤ 0) :
    Prec0 (gwSchurProduct f (gwL p))
      (X * gwSchurProduct f (gwL p - C u * gwD (gwL p))) := by
  have hpL : IsPFPolynomial (gwL p) := gwL_pf hp
  have hT : IsPFPolynomial (gwL p - C u * gwD (gwL p)) :=
    gwL_sub_C_mul_gwD_gwL_pf hp hu
  have hprecT :
      Prec0 (gwSchurProduct f (gwL p - C u * gwD (gwL p)))
        (gwSchurProduct f (gwL p)) :=
    gwSchurProductPrec0_left hf hT hpL
      (gwL_sub_C_mul_gwD_gwL_prec0_self hp hu)
  exact
    prec0_mul_X_of_prec0 hprecT
      (gwSchurProductPF hf hT).hasNonnegCoeffs
      (gwSchurProductPF hf hpL).hasNonnegCoeffs

/-- Second Schur term in Garloff--Wagner's double-deleted paragraph: the base
Hadamard product precedes the `JL` transported full right factor. -/
theorem gwSchurProduct_secondDoubleDeletedTerm_prec0
    {f q p : ℝ[X]} {u : ℝ}
    (hf : IsPFPolynomial f) (hq : IsPFPolynomial q)
    (hq0 : q ≠ 0) (hfactor : q = (X - C u) * p) :
    Prec0 (gwSchurProduct f (gwL p))
      (gwSchurProduct f (gwJ (gwL p) - C u * gwL p)) := by
  have hsummand : IsGWKreinSummand q p := Or.inr ⟨u, hfactor⟩
  have hp : IsPFPolynomial p := hsummand.isPFPolynomial hq
  have hpL : IsPFPolynomial (gwL p) := gwL_pf hp
  have hqL : IsPFPolynomial (gwL q) := gwL_pf hq
  have hpq : Prec0 p q :=
    hsummand.prec0 hq0 (hq.ne_zero_and_splits hq0).2
  have hLpLq : Prec0 (gwL p) (gwL q) := gwL_prec0 hpq
  have hSchur :
      Prec0 (gwSchurProduct f (gwL p)) (gwSchurProduct f (gwL q)) :=
    gwSchurProductPrec0_left hf hpL hqL hLpLq
  simpa [hfactor, gwL_X_sub_C_mul] using hSchur

/-- Garloff--Wagner's double-deleted compatibility paragraph in Theorem 4(b),
in the ordinary-Hadamard form needed for the two-pair theorem. -/
theorem gwHadamardProductDoubleDeletedKrein :
    gwHadamardProductDoubleDeletedKreinStatement := by
  intro g q f p u v hg hq hg0 hq0 hgfactor hqfactor
  have hfsummand : IsGWKreinSummand g f := Or.inr ⟨u, hgfactor⟩
  have hpsummand : IsGWKreinSummand q p := Or.inr ⟨v, hqfactor⟩
  have hf : IsPFPolynomial f := hfsummand.isPFPolynomial hg
  have hp : IsPFPolynomial p := hpsummand.isPFPolynomial hq
  have hu_root : g.IsRoot u := by
    rw [hgfactor, Polynomial.IsRoot.def, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hv_root : q.IsRoot v := by
    rw [hqfactor, Polynomial.IsRoot.def, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hu : u ≤ 0 :=
    hg.roots_nonpos u ((mem_roots hg0).mpr hu_root)
  have hv : v ≤ 0 :=
    hq.roots_nonpos v ((mem_roots hq0).mpr hv_root)
  let B : ℝ[X] := gwSchurProduct f (gwL p)
  let S₁ : ℝ[X] := gwSchurProduct f (gwL p - C v * gwD (gwL p))
  let S₂ : ℝ[X] := gwSchurProduct f (gwJ (gwL p) - C v * gwL p)
  have hfirst : Prec0 B (X * S₁) := by
    change Prec0 (gwSchurProduct f (gwL p))
      (X * gwSchurProduct f (gwL p - C v * gwD (gwL p)))
    exact gwSchurProduct_firstDoubleDeletedTerm_prec0 hf hp hv
  have hsecond : Prec0 B S₂ := by
    change Prec0 (gwSchurProduct f (gwL p))
      (gwSchurProduct f (gwJ (gwL p) - C v * gwL p))
    exact gwSchurProduct_secondDoubleDeletedTerm_prec0 hf hq hq0 hqfactor
  have hS₁ : IsPFPolynomial S₁ := by
    change IsPFPolynomial (gwSchurProduct f (gwL p - C v * gwD (gwL p)))
    exact gwSchurProductPF hf (gwL_sub_C_mul_gwD_gwL_pf hp hv)
  have hS₂ : IsPFPolynomial S₂ := by
    change IsPFPolynomial (gwSchurProduct f (gwJ (gwL p) - C v * gwL p))
    have hqL : IsPFPolynomial (gwL q) := gwL_pf hq
    simpa [hqfactor, gwL_X_sub_C_mul] using gwSchurProductPF hf hqL
  have hcombo :
      Prec0 B (C (1 : ℝ) * (X * S₁) + C (-u) * S₂) :=
    prec0_nonneg_combo_right_of_common_left_of_nonneg hfirst hsecond
      hS₁.X_mul.hasNonnegCoeffs hS₂.hasNonnegCoeffs zero_le_one (by linarith)
  rw [← gwSchurProduct_gwL_right f p, hgfactor, hqfactor,
    hadamardProduct_X_sub_C_mul_X_sub_C_mul_eq]
  change Prec0 B (X * S₁ - C u * S₂)
  simpa [sub_eq_add_neg, C_neg, neg_mul] using hcombo

namespace IsGWKreinSummand

/-- Fixed-factor Schur products of a Krein summand precede the parent product. -/
theorem gwSchurProduct_prec0 {g q p : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg : IsPFPolynomial g) (hp : IsPFPolynomial p) (hg0 : g ≠ 0) :
    Prec0 (gwSchurProduct q p) (gwSchurProduct g p) :=
  gwSchurProductPrec0 (h.isPFPolynomial hg) hg hp
    (h.prec0 hg0 (hg.ne_zero_and_splits hg0).2)

/-- Two arbitrary Krein summands reduce to the genuinely double-deleted case. -/
theorem gwSchurProduct_prec0_of_doubleDeleted
    (hDouble : gwSchurProductDoubleDeletedKreinStatement)
    {g q f p : ℝ[X]} (hf : IsGWKreinSummand g f)
    (hp : IsGWKreinSummand q p)
    (hg : IsPFPolynomial g) (hq : IsPFPolynomial q)
    (hg0 : g ≠ 0) (hq0 : q ≠ 0) :
    Prec0 (gwSchurProduct f p) (gwSchurProduct g q) := by
  rcases hf with hfg_self | ⟨u, hfg_factor⟩
  · rw [hfg_self]
    simpa [gwSchurProduct_comm p g, gwSchurProduct_comm q g] using
      hp.gwSchurProduct_prec0 hq hg hq0
  rcases hp with hpq_self | ⟨v, hpq_factor⟩
  · rw [hpq_self]
    exact (show IsGWKreinSummand g f from Or.inr ⟨u, hfg_factor⟩).gwSchurProduct_prec0
      hg hq hg0
  · exact hDouble hg hq hg0 hq0 hfg_factor hpq_factor

/-- Fixed-factor ordinary Hadamard products of a Krein summand precede the
parent product. -/
theorem gwHadamardProduct_prec0 {g q p : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg : IsPFPolynomial g) (hp : IsPFPolynomial p) (hg0 : g ≠ 0) :
    Prec0 (hadamardProduct q p) (hadamardProduct g p) :=
  gwHadamardProductPrec0 (h.isPFPolynomial hg) hg hp
    (h.prec0 hg0 (hg.ne_zero_and_splits hg0).2)

/-- Two arbitrary Krein summands reduce to the genuinely double-deleted
ordinary-Hadamard case. -/
theorem gwHadamardProduct_prec0_of_doubleDeleted
    (hDouble : gwHadamardProductDoubleDeletedKreinStatement)
    {g q f p : ℝ[X]} (hf : IsGWKreinSummand g f)
    (hp : IsGWKreinSummand q p)
    (hg : IsPFPolynomial g) (hq : IsPFPolynomial q)
    (hg0 : g ≠ 0) (hq0 : q ≠ 0) :
    Prec0 (hadamardProduct f p) (hadamardProduct g q) := by
  rcases hf with hfg_self | ⟨u, hfg_factor⟩
  · rw [hfg_self]
    simpa [hadamardProduct_comm p g, hadamardProduct_comm q g] using
      hp.gwHadamardProduct_prec0 hq hg hq0
  rcases hp with hpq_self | ⟨v, hpq_factor⟩
  · rw [hpq_self]
    exact (show IsGWKreinSummand g f from Or.inr ⟨u, hfg_factor⟩).gwHadamardProduct_prec0
      hg hq hg0
  · exact hDouble hg hq hg0 hq0 hfg_factor hpq_factor

end IsGWKreinSummand

/-- Hadamard product distributes over a weighted sum in the left argument. -/
theorem hadamardProduct_weightedSum_left :
    ∀ (l : List (ℝ × ℝ[X])) (p : ℝ[X]),
      hadamardProduct (weightedSum l) p =
        weightedSum (l.map fun ap => (ap.1, hadamardProduct ap.2 p))
  | [], _ => by
      simp
  | (a, q) :: l, p => by
      rw [weightedSum_cons, hadamardProduct_add_left, hadamardProduct_C_mul_left,
        hadamardProduct_weightedSum_left l p]
      rfl

/-- Hadamard product distributes over a weighted sum in the right argument. -/
theorem hadamardProduct_weightedSum_right :
    ∀ (p : ℝ[X]) (l : List (ℝ × ℝ[X])),
      hadamardProduct p (weightedSum l) =
        weightedSum (l.map fun ap => (ap.1, hadamardProduct p ap.2))
  | _, [] => by
      simp
  | p, (a, q) :: l => by
      rw [weightedSum_cons, hadamardProduct_add_right, hadamardProduct_C_mul_right,
        hadamardProduct_weightedSum_right p l]
      rfl

/-- If the left input is expanded into Krein summands and the right input is a
single Krein summand, every Hadamard summand has the same right bound. -/
theorem hadamardProduct_prec0_of_kreinSummandExpansion_left
    {f g p q : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hsummand : ∀ ap ∈ l, IsGWKreinSummand g ap.2)
    (hp : IsGWKreinSummand q p)
    (hg : IsPFPolynomial g) (hq : IsPFPolynomial q)
    (hg0 : g ≠ 0) (hq0 : q ≠ 0) :
    Prec0 (hadamardProduct f p) (hadamardProduct g q) := by
  rw [hf, hadamardProduct_weightedSum_left]
  apply prec0_weightedSum_right_of_nonneg
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hnonneg ap0 hap0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact (hsummand ap0 hap0).gwHadamardProduct_prec0_of_doubleDeleted
      gwHadamardProductDoubleDeletedKrein hp hg hq hg0 hq0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact
      (gwHadamardProductPF ((hsummand ap0 hap0).isPFPolynomial hg)
        (hp.isPFPolynomial hq)).hasNonnegCoeffs

/-- Two Krein expansions assemble the ordinary-Hadamard two-pair theorem. -/
theorem hadamardProduct_prec0_of_kreinSummandExpansions
    {f g p q : ℝ[X]} {lf lp : List (ℝ × ℝ[X])}
    (hf : f = weightedSum lf) (hp : p = weightedSum lp)
    (hfnonneg : ∀ ap ∈ lf, 0 ≤ ap.1)
    (hpnonneg : ∀ ap ∈ lp, 0 ≤ ap.1)
    (hfsummand : ∀ ap ∈ lf, IsGWKreinSummand g ap.2)
    (hpsummand : ∀ ap ∈ lp, IsGWKreinSummand q ap.2)
    (hfPF : IsPFPolynomial f) (hg : IsPFPolynomial g) (hq : IsPFPolynomial q)
    (hg0 : g ≠ 0) (hq0 : q ≠ 0) :
    Prec0 (hadamardProduct f p) (hadamardProduct g q) := by
  rw [hp, hadamardProduct_weightedSum_right]
  apply prec0_weightedSum_right_of_nonneg
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hpnonneg ap0 hap0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hadamardProduct_prec0_of_kreinSummandExpansion_left
      hf hfnonneg hfsummand (hpsummand ap0 hap0) hg hq hg0 hq0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact
      (gwHadamardProductPF hfPF
        ((hpsummand ap0 hap0).isPFPolynomial hq)).hasNonnegCoeffs

/-- Garloff--Wagner, Theorem 4(b), for PF polynomials in the local
orientation. -/
theorem gwHadamardProductPrec0_of_prec {f g p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hfg : Prec f g) (hpq : Prec p q) :
    Prec0 (hadamardProduct f p) (hadamardProduct g q) := by
  have hfpos : HasPosLeadingCoeff f :=
    hf.hasNonnegCoeffs.pos_leadingCoeff hfg.1.1
  have hgpos : HasPosLeadingCoeff g :=
    hg.hasNonnegCoeffs.pos_leadingCoeff hfg.2.1.1
  have hppos : HasPosLeadingCoeff p :=
    hp.hasNonnegCoeffs.pos_leadingCoeff hpq.1.1
  have hqpos : HasPosLeadingCoeff q :=
    hq.hasNonnegCoeffs.pos_leadingCoeff hpq.2.1.1
  rcases gwTheorem11PrecKreinSummandExpansion hfg hfpos hgpos with
    ⟨lf, hfeq, hfnonneg, hfsummand, _⟩
  rcases gwTheorem11PrecKreinSummandExpansion hpq hppos hqpos with
    ⟨lp, hpeq, hpnonneg, hpsummand, _⟩
  exact hadamardProduct_prec0_of_kreinSummandExpansions
    hfeq hpeq hfnonneg hpnonneg hfsummand hpsummand
    hf hg hq hfg.2.1.1 hpq.2.1.1

/-- Garloff--Wagner, Theorem 4(b), in the nonnegative-coefficient form used by
the `Hadamard` module. -/
theorem gwHadamardProductNonnegPrec {f g p q : ℝ[X]}
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hfg : Prec f g) (hpq : Prec p q) :
    Prec0 (hadamardProduct f p) (hadamardProduct g q) := by
  exact gwHadamardProductPrec0_of_prec
    (IsPFPolynomial.of_realRooted_nonneg hf hfg.1.2)
    (IsPFPolynomial.of_realRooted_nonneg hg hfg.2.1.2)
    (IsPFPolynomial.of_realRooted_nonneg hp hpq.1.2)
    (IsPFPolynomial.of_realRooted_nonneg hq hpq.2.1.2)
    hfg hpq

end RealRooted
