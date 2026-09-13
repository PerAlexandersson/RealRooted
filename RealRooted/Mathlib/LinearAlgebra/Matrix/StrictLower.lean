import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Matrix.Mul

/-!
# Strictly lower triangular matrix powers

This file records finite support, nilpotence, and geometric-sum identities for
strictly lower triangular matrices.  The support statements use explicit entry
hypotheses so that they do not depend on a particular triangular-matrix
predicate.
-/

open BigOperators

namespace Matrix

noncomputable section

/-- Retain precisely the entries strictly below the diagonal. -/
def strictLowerPart {R ι : Type*} [Zero R] [LinearOrder ι]
    (A : Matrix ι ι R) : Matrix ι ι R :=
  fun i j => if j < i then A i j else 0

@[simp]
theorem strictLowerPart_apply_of_lt {R ι : Type*} [Zero R] [LinearOrder ι]
    (A : Matrix ι ι R) {i j : ι} (hji : j < i) :
    strictLowerPart A i j = A i j := by
  simp [strictLowerPart, hji]

@[simp]
theorem strictLowerPart_apply_of_not_lt
    {R ι : Type*} [Zero R] [LinearOrder ι]
    (A : Matrix ι ι R) {i j : ι} (hji : ¬j < i) :
    strictLowerPart A i j = 0 := by
  simp [strictLowerPart, hji]

/-- The strict-lower part is strictly lower triangular without assumptions on
the original matrix. -/
theorem strictLowerPart_apply_eq_zero_of_le
    {R ι : Type*} [Zero R] [LinearOrder ι]
    (A : Matrix ι ι R) {i j : ι} (hij : i ≤ j) :
    strictLowerPart A i j = 0 := by
  exact strictLowerPart_apply_of_not_lt A (not_lt_of_ge hij)

/-- A lower triangular matrix with zero diagonal equals its strict-lower
part. -/
theorem strictLowerPart_eq_self_of_lower_diagonal_zero
    {R ι : Type*} [Zero R] [LinearOrder ι]
    (A : Matrix ι ι R)
    (hA : ∀ i j, i < j → A i j = 0)
    (hdiag : ∀ i, A i i = 0) :
    strictLowerPart A = A := by
  ext i j
  rcases lt_trichotomy j i with hji | rfl | hij
  · exact strictLowerPart_apply_of_lt A hji
  · simp [strictLowerPart, hdiag]
  · simp [strictLowerPart, hA i j hij, not_lt_of_ge hij.le]

/-- The `q`th power of a strictly lower triangular matrix vanishes at `(i, j)`
whenever `i < j + q`. -/
theorem pow_apply_eq_zero_of_lt_add_of_strictLower
    {R : Type*} [Semiring R] {N q : ℕ}
    (K : Matrix (Fin N) (Fin N) R)
    (hK : ∀ i j, i.val ≤ j.val → K i j = 0)
    {i j : Fin N} (hij : i.val < j.val + q) :
    (K ^ q) i j = 0 := by
  induction q generalizing i j with
  | zero =>
      simp only [Nat.add_zero] at hij
      have hij' : i < j := Fin.mk_lt_mk.mpr hij
      simp [ne_of_lt hij']
  | succ q ih =>
      rw [pow_succ, mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : i.val < k.val + q
      · rw [ih hik, zero_mul]
      · have hkj : k.val ≤ j.val := by lia
        rw [hK k j hkj, mul_zero]

/-- A strictly lower triangular matrix on `Fin N` is nilpotent at exponent
`N`.  For `N = 0` this is the equality between the unique empty matrices. -/
theorem pow_card_eq_zero_of_strictLower
    {R : Type*} [Semiring R] {N : ℕ}
    (K : Matrix (Fin N) (Fin N) R)
    (hK : ∀ i j, i.val ≤ j.val → K i j = 0) :
    K ^ N = 0 := by
  ext i j
  apply pow_apply_eq_zero_of_lt_add_of_strictLower K hK
  have hi := i.isLt
  have hj := Nat.zero_le j.val
  lia

/-- Multiplying a strictly lower triangular matrix on the right by a lower
triangular matrix preserves strict lower triangularity. -/
theorem mul_apply_eq_zero_of_le_of_strictLower_lower
    {R : Type*} [Semiring R] {N : ℕ}
    (K G : Matrix (Fin N) (Fin N) R)
    (hK : ∀ i j, i.val ≤ j.val → K i j = 0)
    (hG : ∀ i j, i < j → G i j = 0)
    {i j : Fin N} (hij : i.val ≤ j.val) :
    (K * G) i j = 0 := by
  rw [mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i.val ≤ k.val
  · rw [hK i k hik, zero_mul]
  · have hkj : k < j := by
      have hki : k < i := Fin.mk_lt_mk.mpr (Nat.lt_of_not_ge hik)
      have hij' : i ≤ j := Fin.mk_le_mk.mpr hij
      exact hki.trans_le hij'
    rw [hG k j hkj, mul_zero]

/-- Multiplying a lower triangular matrix on the right by a strictly lower
triangular matrix preserves strict lower triangularity. -/
theorem mul_apply_eq_zero_of_le_of_lower_strictLower
    {R : Type*} [Semiring R] {N : ℕ}
    (G K : Matrix (Fin N) (Fin N) R)
    (hG : ∀ i j, i < j → G i j = 0)
    (hK : ∀ i j, i.val ≤ j.val → K i j = 0)
    {i j : Fin N} (hij : i.val ≤ j.val) :
    (G * K) i j = 0 := by
  rw [mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i < k
  · rw [hG i k hik, zero_mul]
  · have hkj : k.val ≤ j.val :=
      (Fin.mk_le_mk.mp (le_of_not_gt hik)).trans hij
    rw [hK k j hkj, mul_zero]

/-- A strictly lower matrix followed by a lower matrix is nilpotent at the
cardinality of its finite index type. -/
theorem mul_pow_card_eq_zero_of_strictLower_lower
    {R : Type*} [Semiring R] {N : ℕ}
    (K G : Matrix (Fin N) (Fin N) R)
    (hK : ∀ i j, i.val ≤ j.val → K i j = 0)
    (hG : ∀ i j, i < j → G i j = 0) :
    (K * G) ^ N = 0 := by
  apply pow_card_eq_zero_of_strictLower
  intro i j hij
  exact mul_apply_eq_zero_of_le_of_strictLower_lower K G hK hG hij

/-- A lower triangular matrix followed by a power of a strictly lower
triangular matrix has the same sharp support shift as that power. -/
theorem mul_pow_apply_eq_zero_of_lt_add_of_lower_strictLower
    {R : Type*} [Semiring R] {N q : ℕ}
    (G K : Matrix (Fin N) (Fin N) R)
    (hG : ∀ i j, i < j → G i j = 0)
    (hK : ∀ i j, i.val ≤ j.val → K i j = 0)
    {i j : Fin N} (hij : i.val < j.val + q) :
    (G * K ^ q) i j = 0 := by
  rw [mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i < k
  · rw [hG i k hik, zero_mul]
  · have hkj : k.val < j.val + q := by
      exact lt_of_le_of_lt (Fin.mk_le_mk.mp (le_of_not_gt hik)) hij
    rw [pow_apply_eq_zero_of_lt_add_of_strictLower K hK hkj, mul_zero]

/-- A power of a strictly lower triangular matrix followed by a lower
triangular matrix has the same sharp support shift as that power. -/
theorem pow_mul_apply_eq_zero_of_lt_add_of_strictLower_lower
    {R : Type*} [Semiring R] {N q : ℕ}
    (K G : Matrix (Fin N) (Fin N) R)
    (hK : ∀ i j, i.val ≤ j.val → K i j = 0)
    (hG : ∀ i j, i < j → G i j = 0)
    {i j : Fin N} (hij : i.val < j.val + q) :
    (K ^ q * G) i j = 0 := by
  rw [mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hkj : k < j
  · rw [hG k j hkj, mul_zero]
  · have hik : i.val < k.val + q := by
      have hjk : j.val ≤ k.val := Fin.mk_le_mk.mp (le_of_not_gt hkj)
      exact lt_of_lt_of_le hij (Nat.add_le_add_right hjk q)
    rw [pow_apply_eq_zero_of_lt_add_of_strictLower K hK hik, zero_mul]

/-- Moving the terminal factor through a power interchanges the two possible
orders of a matrix product. -/
theorem mul_pow_mul_eq_mul_mul_pow
    {R ι : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]
    (G K : Matrix ι ι R) (q : ℕ) :
    (G * K) ^ q * G = G * (K * G) ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
      calc
        (G * K) ^ (q + 1) * G = ((G * K) ^ q * G) * K * G := by
          simp [pow_succ, mul_assoc]
        _ = (G * (K * G) ^ q) * K * G := by rw [ih]
        _ = G * (K * G) ^ (q + 1) := by simp [pow_succ, mul_assoc]

/-- The finite geometric sum of a square matrix. -/
def finiteGeomSum {R ι : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (n : ℕ) : Matrix ι ι R :=
  ∑ q ∈ Finset.range n, A ^ q

/-- Right finite resolvent identity. -/
theorem finiteGeomSum_mul_one_sub
    {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (n : ℕ) :
    finiteGeomSum A n * (1 - A) = 1 - A ^ n := by
  simpa [finiteGeomSum] using geom_sum_mul_neg A n

/-- Left finite resolvent identity. -/
theorem one_sub_mul_finiteGeomSum
    {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (n : ℕ) :
    (1 - A) * finiteGeomSum A n = 1 - A ^ n := by
  simpa [finiteGeomSum] using mul_neg_geom_sum A n

/-- A nilpotence witness turns the finite geometric sum into a right inverse
of `1 - A`. -/
theorem finiteGeomSum_mul_one_sub_of_pow_eq_zero
    {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) {n : ℕ} (hA : A ^ n = 0) :
    finiteGeomSum A n * (1 - A) = 1 := by
  rw [finiteGeomSum_mul_one_sub, hA, sub_zero]

/-- A nilpotence witness turns the finite geometric sum into a left inverse
of `1 - A`. -/
theorem one_sub_mul_finiteGeomSum_of_pow_eq_zero
    {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) {n : ℕ} (hA : A ^ n = 0) :
    (1 - A) * finiteGeomSum A n = 1 := by
  rw [one_sub_mul_finiteGeomSum, hA, sub_zero]

/-- Finite geometric sums inherit the product-order transport identity. -/
theorem finiteGeomSum_mul
    {R ι : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]
    (G K : Matrix ι ι R) (n : ℕ) :
    finiteGeomSum (G * K) n * G = G * finiteGeomSum (K * G) n := by
  simp_rw [finiteGeomSum, Finset.sum_mul, Finset.mul_sum,
    mul_pow_mul_eq_mul_mul_pow G K]

end

end Matrix
