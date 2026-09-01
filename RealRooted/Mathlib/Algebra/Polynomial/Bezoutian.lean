import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Polynomial Bezoutians

Coefficient-level definitions and algebraic identities for the Bezoutian of
two univariate polynomials. These statements use only commutative-ring
structure and are intended to be suitable for Mathlib.
-/

open scoped BigOperators

noncomputable section

namespace Polynomial

/-- The `(i,j)` coefficient of the Bezoutian determined by two coefficient
sequences. -/
def bezoutSeqEntry {A : Type*} [CommRing A] (a b : ℕ → A) (i j : ℕ) : A :=
  Finset.sum (Finset.range (min i j + 1)) fun k ↦
    a (i + j + 1 - k) * b k - b (i + j + 1 - k) * a k

lemma bezoutSeqEntry.comm {A : Type*} [CommRing A] (a b : ℕ → A) (i j : ℕ) :
    bezoutSeqEntry a b i j = bezoutSeqEntry a b j i := by
  simp [bezoutSeqEntry, Nat.add_comm, Nat.add_assoc, min_comm]

lemma bezoutSeqEntry.eq_zero_of_le_left {A : Type*} [CommRing A] (a b : ℕ → A)
    {n : ℕ} {i j : ℕ}
    (ha : ∀ k, n < k → a k = 0) (hb : ∀ k, n < k → b k = 0) (hi : n ≤ i) :
    bezoutSeqEntry a b i j = 0 := by
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  have hk_le : k ≤ min i j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hj_le : k ≤ j := hk_le.trans (min_le_right i j)
  have hp0 : a (i + j + 1 - k) = 0 := ha _ (by lia)
  have hq0 : b (i + j + 1 - k) = 0 := hb _ (by lia)
  simp [hp0, hq0]

lemma bezoutSeqEntry.eq_zero_of_le_right {A : Type*} [CommRing A] (a b : ℕ → A)
    {n : ℕ} {i j : ℕ}
    (ha : ∀ k, n < k → a k = 0) (hb : ∀ k, n < k → b k = 0) (hj : n ≤ j) :
    bezoutSeqEntry a b i j = 0 :=
  bezoutSeqEntry.comm a b j i ▸ bezoutSeqEntry.eq_zero_of_le_left a b ha hb hj

lemma bezoutSeqEntry.telescoping {A : Type*} [CommRing A] (a b : ℕ → A) (i j : ℕ) :
    bezoutSeqEntry a b i (j + 1) - bezoutSeqEntry a b (i + 1) j =
    a (i + 1) * b (j + 1) - a (j + 1) * b (i + 1) := by
  rcases le_or_gt i j with hij | hij
  · rcases eq_or_lt_of_le hij with rfl | h_lt
    · rw [bezoutSeqEntry.comm a b i (i + 1), sub_self]
      simp [*]
    · have hmin₁ : min i (j + 1) = i := min_eq_left (Nat.le_succ_of_le hij)
      have hmin₂ : min (i + 1) j = i + 1 := min_eq_left h_lt
      have h_index : (i + 1) + j + 1 - (i + 1) = j + 1 := by lia
      simp only [bezoutSeqEntry, hmin₁, hmin₂, Finset.sum_sub_distrib,
        Finset.sum_range_succ]
      rw [h_index]
      ring_nf
  · have hmin₁ : min i (j + 1) = j + 1 := min_eq_right hij
    have hmin₂ : min (i + 1) j = j := min_eq_right (Nat.le_succ_of_le hij.le)
    have h_index : i + (j + 1) + 1 - (j + 1) = i + 1 := by lia
    simp only [bezoutSeqEntry, hmin₁, hmin₂, Finset.sum_sub_distrib,
      Finset.sum_range_succ]
    rw [h_index]
    ring_nf

lemma bezoutSeqEntry.coeff_mul_sub_coeff_mul {A : Type*} [CommRing A] (a b : ℕ → A)
    (i j : ℕ) :
    a i * b j - a j * b i =
      (if i ≠ 0 then bezoutSeqEntry a b (i - 1) j else 0) -
        (if j ≠ 0 then bezoutSeqEntry a b i (j - 1) else 0) := by
  rcases i with _ | i
  · rcases j with _ | j
    · simp
    · simp [bezoutSeqEntry]
      ring
  · rcases j with _ | j
    · simp [bezoutSeqEntry]
      ring
    · simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        not_false_eq_true, ↓reduceIte, add_tsub_cancel_right]
      rw [← bezoutSeqEntry.telescoping]

lemma bezoutSeqEntry.bilinear_mul_sub {A : Type*} [CommRing A] (a b : ℕ → A)
    (n : ℕ) (t₁ t₂ : A)
    (ha : ∀ k, n < k → a k = 0) (hb : ∀ k, n < k → b k = 0) :
    (t₁ - t₂) * ∑ i : Fin n, ∑ j : Fin n,
    bezoutSeqEntry a b i.val j.val * t₁ ^ i.val * t₂ ^ j.val =
    (∑ i ∈ Finset.range (n + 1), a i * t₁ ^ i) *
      (∑ j ∈ Finset.range (n + 1), b j * t₂ ^ j) -
    (∑ i ∈ Finset.range (n + 1), a i * t₂ ^ i) *
      (∑ j ∈ Finset.range (n + 1), b j * t₁ ^ j) := by
  have h_eq_left (i j : ℕ) (hi : n ≤ i) : bezoutSeqEntry a b i j = 0 :=
    bezoutSeqEntry.eq_zero_of_le_left a b ha hb hi
  have h_eq_right (i j : ℕ) (hj : n ≤ j) : bezoutSeqEntry a b i j = 0 :=
    bezoutSeqEntry.eq_zero_of_le_right a b ha hb hj
  have h_telescope (i j : ℕ) :
      a i * b j - a j * b i =
        (if i ≠ 0 then bezoutSeqEntry a b (i - 1) j else 0) -
          (if j ≠ 0 then bezoutSeqEntry a b i (j - 1) else 0) :=
    bezoutSeqEntry.coeff_mul_sub_coeff_mul a b i j
  have h_rhs :
      (∑ i ∈ Finset.range (n + 1), a i * t₁ ^ i) *
        (∑ j ∈ Finset.range (n + 1), b j * t₂ ^ j) -
      (∑ i ∈ Finset.range (n + 1), a i * t₂ ^ i) *
        (∑ j ∈ Finset.range (n + 1), b j * t₁ ^ j) =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        (a i * b j - a j * b i) * t₁ ^ i * t₂ ^ j := by
    have h_expand₁ :
        (∑ i ∈ Finset.range (n + 1), a i * t₁ ^ i) *
          (∑ j ∈ Finset.range (n + 1), b j * t₂ ^ j) =
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          a i * b j * t₁ ^ i * t₂ ^ j := by
      rw [Finset.sum_mul_sum]
      simp only [mul_assoc, mul_left_comm]
    have h_expand₂ :
        (∑ i ∈ Finset.range (n + 1), a i * t₂ ^ i) *
          (∑ j ∈ Finset.range (n + 1), b j * t₁ ^ j) =
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          a j * b i * t₁ ^ i * t₂ ^ j := by
      rw [Finset.sum_mul_sum, Finset.sum_comm]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    simp only [h_expand₁, h_expand₂, sub_mul, Finset.sum_sub_distrib]
  have h_rhs_sum :
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        (a i * b j - a j * b i) * t₁ ^ i * t₂ ^ j =
      t₁ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n + 1),
        bezoutSeqEntry a b i j * t₁ ^ i * t₂ ^ j -
      t₂ * ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range n,
        bezoutSeqEntry a b i j * t₁ ^ i * t₂ ^ j := by
    have h_telescope_sum :
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (a i * b j - a j * b i) * t₁ ^ i * t₂ ^ j =
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (if i ≠ 0 then bezoutSeqEntry a b (i - 1) j else 0) * t₁ ^ i * t₂ ^ j -
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (if j ≠ 0 then bezoutSeqEntry a b i (j - 1) else 0) * t₁ ^ i * t₂ ^ j := by
      simp only [h_telescope, sub_mul, Finset.sum_sub_distrib]
    convert h_telescope_sum using 2 <;> norm_num [Finset.sum_range_succ']
    · simp only [pow_succ', mul_assoc, mul_add, mul_comm, mul_left_comm, Finset.mul_sum]
    · simp only [pow_succ', mul_comm, mul_assoc, mul_left_comm, mul_add, Finset.mul_sum]
  rw [h_rhs, h_rhs_sum]
  simp [Finset.sum_range, Fin.sum_univ_castSucc, sub_mul, h_eq_left, h_eq_right]

/-- The `(i,j)` coefficient of the Bezoutian
`(p(X) q(Y) - p(Y) q(X)) / (X - Y)`.

This definition is independent of a matrix size. Coefficients outside the
degrees of `p` and `q` vanish through `Polynomial.coeff`. -/
def bezoutEntry {R : Type*} [CommRing R] (p q : R[X]) (i j : ℕ) : R :=
  bezoutSeqEntry p.coeff q.coeff i j

/-- The `n × n` Bezout matrix attached to two polynomials. -/
def bezoutMatrix {R : Type*} [CommRing R] (n : ℕ) (p q : R[X]) :
    Matrix (Fin n) (Fin n) R :=
  fun i j ↦ bezoutEntry p q i.1 j.1

/-- The `i`th Bezoutian row interpreted as a polynomial. -/
def bezoutRowPoly {R : Type*} [CommRing R] (n : ℕ) (p q : R[X]) (i : Fin n) : R[X] :=
  ∑ j : Fin n, C (bezoutEntry p q i j) * X ^ (j : ℕ)

lemma bezoutEntry.comm {R : Type*} [CommRing R] (p q : R[X]) (i j : ℕ) :
    bezoutEntry p q i j = bezoutEntry p q j i :=
  bezoutSeqEntry.comm p.coeff q.coeff i j

end Polynomial
