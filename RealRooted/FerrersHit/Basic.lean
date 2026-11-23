module

public import RealRooted.Mathlib.RingTheory.Polynomial.Pochhammer
public import RealRooted.Transforms.BrandenE.Inverse
public import RealRooted.Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic
import RealRooted.Mathlib.Algebra.Polynomial.Chow

/-!
# Ferrers rook numbers and the rook-to-hit transform

We use the algebraic normalization of the Goldman--Joichi--White factorization:
the rook numbers are the reversed coordinates of the column-height product in
the descending-Pochhammer basis. No counting model is assumed.

The hit transform is the one on page 2 of Haglund--Ono--Wagner,
*Theorems and conjectures involving rook polynomials with only real zeros*
(1999). Their Theorem 1 asserts real-rootedness for Ferrers boards.
-/

@[expose] public section

open Polynomial
open scoped BigOperators

namespace RealRooted.FerrersHit

noncomputable section

/-- Weakly increasing column heights of a board in the `n × n` square. -/
def IsFerrers {n : ℕ} (h : Fin n → ℕ) : Prop :=
  Monotone h ∧ ∀ i, h i ≤ n

/-- The Goldman--Joichi--White column-height product, indexed from zero. -/
def factorialPolynomial {n : ℕ} (h : Fin n → ℕ) : ℝ[X] :=
  ∏ i, (X + C ((h i : ℝ) - (i : ℕ)))

/-- Algebraic rook numbers, defined by the falling-factorial coordinates.
For a Ferrers board these are the standard Goldman--Joichi--White rook numbers. -/
def rookNumber {n : ℕ} (h : Fin n → ℕ) (k : ℕ) : ℝ :=
  if k ≤ n then (descPochhammerBasis ℝ).repr (factorialPolynomial h) (n - k) else 0

/-- The standard rook-to-hit transform. -/
def hitPolynomial {n : ℕ} (h : Fin n → ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (rookNumber h k * ((n - k).factorial : ℝ)) * (X - 1) ^ k

/-- The height product is monic of degree `n`. -/
theorem factorialPolynomial_monic_natDegree {n : ℕ} (h : Fin n → ℕ) :
    (factorialPolynomial h).Monic ∧ (factorialPolynomial h).natDegree = n := by
  have hm : ∀ i : Fin n, (X + C ((h i : ℝ) - (i : ℕ))).Monic :=
    fun _ => monic_X_add_C _
  refine ⟨monic_prod_of_monic _ _ (fun i _ => hm i), ?_⟩
  change (∏ i, (X + C ((h i : ℝ) - (i : ℕ)))).natDegree = n
  rw [natDegree_prod_of_monic _ _ (fun i _ => hm i)]
  simp only [natDegree_X_add_C]
  simp

/-- The finite falling-factorial expansion of the column-height product. -/
theorem factorialPolynomial_eq_sum {n : ℕ} (h : Fin n → ℕ) :
    factorialPolynomial h = ∑ j ∈ Finset.range (n + 1),
      C ((descPochhammerBasis ℝ).repr (factorialPolynomial h) j) *
        descPochhammer ℝ j := by
  let b := descPochhammerBasis ℝ
  have hbound : ∀ j, n < j → b.repr (factorialPolynomial h) j = 0 :=
    natDegree_le_iff_repr_descPochhammerBasis.mp
      (factorialPolynomial_monic_natDegree h).2.le
  have hexp := b.linearCombination_repr (factorialPolynomial h)
  rw [Finsupp.linearCombination_apply] at hexp
  rw [Finsupp.sum_of_support_subset _ (s := Finset.range (n + 1))] at hexp
  · simpa [b, smul_eq_C_mul] using hexp.symm
  · intro j hj
    have hjne := Finsupp.mem_support_iff.mp hj
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using
      le_of_not_gt (fun hjgt => hjne (hbound j hjgt))
  · intros
    simp

/-- **Goldman--Joichi--White factorization**, with rook numbers defined by
the falling-factorial formula rather than by rook-placement bijections. -/
theorem sum_rookNumber_descPochhammer {n : ℕ} (h : Fin n → ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      C (rookNumber h k) * descPochhammer ℝ (n - k)) =
        ∏ i, (X + C ((h i : ℝ) - (i : ℕ))) := by
  rw [← factorialPolynomial, factorialPolynomial_eq_sum]
  rw [← Finset.sum_range_reflect (fun j =>
    C ((descPochhammerBasis ℝ).repr (factorialPolynomial h) j) *
      descPochhammer ℝ j) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using hk
  simp [rookNumber, hk']

/-- Brändén's E transform of the factorial product is the factorial-weighted,
reversed rook polynomial. -/
theorem brandenE_factorialPolynomial {n : ℕ} (h : Fin n → ℕ) :
    brandenE (factorialPolynomial h) =
      ∑ j ∈ Finset.range (n + 1),
        C ((descPochhammerBasis ℝ).repr (factorialPolynomial h) j *
          (j.factorial : ℝ)) * X ^ j := by
  conv_lhs => rw [factorialPolynomial_eq_sum]
  rw [brandenE_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [brandenE_C_mul, brandenE_descPochhammer, ← mul_assoc, ← C_mul]

/-- The hit polynomial is a shift of a bounded reversal of the E transform. -/
theorem hitPolynomial_eq_reflect_comp {n : ℕ} (h : Fin n → ℕ) :
    hitPolynomial h =
      (reflect n (brandenE (factorialPolynomial h))).comp (X - 1) := by
  rw [brandenE_factorialPolynomial, reflect_finset_sum_C_mul, sum_comp]
  conv_rhs => rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using hk
  simp [rookNumber, hk', reflect_monomial,
    revAt_le (Nat.sub_le n k), Nat.sub_sub_self hk']

end

end RealRooted.FerrersHit
