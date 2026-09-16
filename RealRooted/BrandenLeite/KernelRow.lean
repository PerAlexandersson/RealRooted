import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import RealRooted.Mathlib.LinearAlgebra.Matrix.StrictLower

/-!
# Finite kernel-row polynomials

This file packages the finite polynomial whose coefficients are entries of
`G * (K * G) ^ q`.  It contains only finite matrix and polynomial algebra; no
total-nonnegativity, root, or limiting hypotheses occur here.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenLeite

noncomputable section

/-- The kernel row attached to row `i` of two square matrices of size
`N + 1`. -/
def kernelRow {R : Type*} [CommSemiring R] {N : ℕ}
    (G K : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i : Fin (N + 1)) : R[X] :=
  ∑ q ∈ Finset.range (N + 1),
    C ((G * (K * G) ^ q) i 0) * X ^ q

/-- The coefficient formula for a kernel row, including indices outside its
finite defining range. -/
theorem coeff_kernelRow {R : Type*} [CommSemiring R] {N : ℕ}
    (G K : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i : Fin (N + 1)) (q : ℕ) :
    (kernelRow G K i).coeff q =
      if q < N + 1 then (G * (K * G) ^ q) i 0 else 0 := by
  rw [kernelRow, Polynomial.finsetSum_coeff]
  by_cases hq : q ∈ Finset.range (N + 1)
  · rw [Finset.sum_eq_single q]
    · simp [Finset.mem_range.mp hq]
    · intro j hj hjq
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hjq]
    · exact fun hnot => (hnot hq).elim
  · have hNq : ¬q < N + 1 := by simpa using hq
    rw [if_neg hNq]
    apply Finset.sum_eq_zero
    intro j hj
    have hjq : j ≠ q := by
      intro heq
      subst j
      exact hq hj
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hjq]

/-- Every kernel row has degree at most the ambient top index. -/
theorem natDegree_kernelRow_le {R : Type*} [CommSemiring R] {N : ℕ}
    (G K : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i : Fin (N + 1)) :
    (kernelRow G K i).natDegree ≤ N := by
  unfold kernelRow
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro q hq
  exact (Polynomial.natDegree_C_mul_X_pow_le _ q).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hq))

/-- Under the triangular hypotheses, coefficients above the row index vanish.
This is sharper than the ambient finite-range bound. -/
theorem coeff_kernelRow_eq_zero_of_row_lt
    {R : Type*} [CommSemiring R] {N : ℕ}
    (G K : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (hG : ∀ i j, i < j → G i j = 0)
    (hK : ∀ i j, i.val ≤ j.val → K i j = 0)
    (i : Fin (N + 1)) {q : ℕ} (hiq : i.val < q) :
    (kernelRow G K i).coeff q = 0 := by
  rw [coeff_kernelRow]
  split
  next _ =>
    apply Matrix.mul_pow_apply_eq_zero_of_lt_add_of_lower_strictLower
      G (K * G) hG
    · intro a b hab
      exact Matrix.mul_apply_eq_zero_of_le_of_strictLower_lower K G hK hG hab
    · simpa using hiq
  next _ => rfl

/-- For lower `G` and strictly lower `K`, row `i` has degree at most `i`. -/
theorem natDegree_kernelRow_le_row
    {R : Type*} [CommSemiring R] {N : ℕ}
    (G K : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (hG : ∀ i j, i < j → G i j = 0)
    (hK : ∀ i j, i.val ≤ j.val → K i j = 0)
    (i : Fin (N + 1)) :
    (kernelRow G K i).natDegree ≤ i.val := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro q hiq
  exact coeff_kernelRow_eq_zero_of_row_lt G K hG hK i hiq

/-- With zero kernel, every kernel row is the corresponding constant entry of
`G`. -/
@[simp]
theorem kernelRow_zero_kernel {R : Type*} [CommSemiring R] {N : ℕ}
    (G : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i : Fin (N + 1)) :
    kernelRow G 0 i = C (G i 0) := by
  ext q
  rw [coeff_kernelRow]
  cases q with
  | zero => simp
  | succ q => simp [pow_succ]

/-- In the one-by-one (`N = 0`) case, the finite row has only its constant
coefficient, independently of the kernel. -/
@[simp]
theorem kernelRow_zero_size {R : Type*} [CommSemiring R]
    (G K : Matrix (Fin 1) (Fin 1) R) (i : Fin 1) :
    kernelRow G K i = C (G i 0) := by
  simp [kernelRow]

end

end RealRooted.BrandenLeite
