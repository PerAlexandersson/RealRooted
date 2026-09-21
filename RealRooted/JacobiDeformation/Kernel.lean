import RealRooted.JacobiDeformation.Basic
import RealRooted.SpectralProduct

/-!
# Finite Jacobi kernel and Newton-weight algebra

This file begins the finite kernel layer for the Jacobi deformation.  It
defines the quadratic differential eigenvalues, their Newton products, the
kernel weights, and the positive Newton coefficients from equations (5)--(8)
of the Jacobi-deformation proof.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The positive differential eigenvalue `j (j + s - 1)`.  The library's
shifted-Jacobi differential operator itself has the negative of this
eigenvalue. -/
def eigenvalue (s : ℝ) (j : ℕ) : ℝ :=
  j * (j + s - 1)

@[simp]
theorem eigenvalue_zero (s : ℝ) : eigenvalue s 0 = 0 := by
  simp [eigenvalue]

theorem eigenvalue_succ_sub (s : ℝ) (j : ℕ) :
    eigenvalue s (j + 1) - eigenvalue s j = 2 * j + s := by
  unfold eigenvalue
  push_cast
  ring

theorem eigenvalue_strictMono {s : ℝ} (hs : 0 < s) :
    StrictMono (eigenvalue s) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [← sub_pos, eigenvalue_succ_sub]
  positivity

/-- The Newton factor polynomial
`Λₖ(t) = ∏_{l < k} (t - λ_l)`. -/
def newtonPolynomial (s : ℝ) (k : ℕ) : ℝ[X] :=
  ∏ l ∈ Finset.range k, (X - C (eigenvalue s l))

@[simp]
theorem newtonPolynomial_zero (s : ℝ) : newtonPolynomial s 0 = 1 := by
  simp [newtonPolynomial]

theorem newtonPolynomial_succ (s : ℝ) (k : ℕ) :
    newtonPolynomial s (k + 1) =
      newtonPolynomial s k * (X - C (eigenvalue s k)) := by
  simp [newtonPolynomial, Finset.prod_range_succ]

/-- Exact evaluation of the Newton factors on the quadratic Jacobi spectrum:
`Λₖ(λ_j) = j^{\underline k} (j+s-1)_k`. -/
theorem eval_newtonPolynomial (s : ℝ) (k j : ℕ) :
    (newtonPolynomial s k).eval (eigenvalue s j) =
      (descPochhammer ℝ k).eval (j : ℝ) *
        (ascPochhammer ℝ k).eval ((j : ℝ) + s - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [newtonPolynomial_succ, eval_mul, eval_sub, eval_X, eval_C, ih,
        descPochhammer_succ_eval, ascPochhammer_succ_eval]
      unfold eigenvalue
      ring

theorem eval_newtonPolynomial_eq_zero {s : ℝ} {j k : ℕ} (hjk : j < k) :
    (newtonPolynomial s k).eval (eigenvalue s j) = 0 := by
  rw [eval_newtonPolynomial,
    descPochhammer_eval_coe_nat_of_lt (R := ℝ) hjk, zero_mul]

theorem eval_newtonPolynomial_pos {s : ℝ} (hs : 0 < s)
    {j k : ℕ} (hkj : k ≤ j) :
    0 < (newtonPolynomial s k).eval (eigenvalue s j) := by
  cases k with
  | zero => simp
  | succ k =>
      rw [eval_newtonPolynomial]
      apply mul_pos
      · rw [descPochhammer_eval_eq_descFactorial]
        exact_mod_cast Nat.descFactorial_pos.mpr hkj
      · apply ascPochhammer_pos
        have hj : 1 ≤ j := by lia
        have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
        linarith

/-- The kernel weight `w_j(δ)` from equation (5). -/
def kernelWeight (m : ℕ) (δ s : ℝ) (j : ℕ) : ℝ :=
  ((descPochhammer ℝ j).eval (m : ℝ)) *
    risingFactorial ((m : ℝ) + s - 1 + δ) j *
    risingFactorial δ (m - j) /
    risingFactorial s (m + j)

/-- The Newton coefficient `a_k(δ)` from equation (7). -/
def newtonCoefficient (m : ℕ) (δ s : ℝ) (k : ℕ) : ℝ :=
  risingFactorial (1 - δ) k /
    ((descPochhammer ℝ k).eval ((m : ℝ) + δ - 1) *
      risingFactorial ((m : ℝ) + s) k * k.factorial)

theorem kernelWeight_pos {m j : ℕ} {δ s : ℝ}
    (hjm : j ≤ m) (hδ : 0 < δ) (hs : 0 < s) :
    0 < kernelWeight m δ s j := by
  cases j with
  | zero =>
      simp only [kernelWeight, descPochhammer_zero, eval_one,
        risingFactorial_zero, mul_one, one_mul, Nat.sub_zero]
      exact div_pos (risingFactorial_pos _ hδ) (risingFactorial_pos _ hs)
  | succ j =>
      have hfall : 0 < (descPochhammer ℝ (j + 1)).eval (m : ℝ) := by
        rw [descPochhammer_eval_eq_descFactorial]
        exact_mod_cast Nat.descFactorial_pos.mpr hjm
      have hm : 1 ≤ m := by lia
      have hbase : 0 < (m : ℝ) + s - 1 + δ := by
        have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      unfold kernelWeight
      exact div_pos
        (mul_pos (mul_pos hfall (risingFactorial_pos _ hbase))
          (risingFactorial_pos _ hδ))
        (risingFactorial_pos _ hs)

theorem newtonCoefficient_pos {m k : ℕ} {δ s : ℝ}
    (hkm : k ≤ m) (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 0 < s) :
    0 < newtonCoefficient m δ s k := by
  have hfall : 0 <
      (descPochhammer ℝ k).eval ((m : ℝ) + δ - 1) := by
    apply descPochhammer_pos
    have hcast : (k : ℝ) ≤ m := by exact_mod_cast hkm
    linarith
  have hms : 0 < (m : ℝ) + s := by
    have hm : 0 ≤ (m : ℝ) := by positivity
    linarith
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  unfold newtonCoefficient
  exact div_pos (risingFactorial_pos _ (sub_pos.mpr hδ1))
    (mul_pos (mul_pos hfall (risingFactorial_pos _ hms)) hfac)

@[simp]
theorem newtonCoefficient_zero (m : ℕ) (δ s : ℝ) :
    newtonCoefficient m δ s 0 = 1 := by
  simp [newtonCoefficient]

theorem newtonCoefficient_one (m : ℕ) (δ s : ℝ) :
    newtonCoefficient m δ s 1 =
      (1 - δ) / (((m : ℝ) + δ - 1) * ((m : ℝ) + s)) := by
  simp [newtonCoefficient, risingFactorial]

theorem newtonCoefficient_one_pos {m : ℕ} {δ s : ℝ}
    (hm : 1 ≤ m) (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 0 < s) :
    0 < newtonCoefficient m δ s 1 := by
  exact newtonCoefficient_pos hm hδ hδ1 hs

/-- The finite Newton polynomial formed from the positive coefficients in
equation (7). -/
def weightNewtonPolynomial (m : ℕ) (δ s : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m + 1),
    C (newtonCoefficient m δ s k) * newtonPolynomial s k

theorem eval_weightNewtonPolynomial_pos {m j : ℕ} {δ s : ℝ}
    (_hjm : j ≤ m) (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 0 < s) :
    0 < (weightNewtonPolynomial m δ s).eval (eigenvalue s j) := by
  rw [weightNewtonPolynomial, eval_finsetSum]
  apply Finset.sum_pos'
  · intro k hk
    simp only [mem_range] at hk
    rw [eval_mul, eval_C]
    by_cases hkj : k ≤ j
    · exact (mul_pos (newtonCoefficient_pos (by lia) hδ hδ1 hs)
        (eval_newtonPolynomial_pos hs hkj)).le
    · rw [eval_newtonPolynomial_eq_zero (Nat.lt_of_not_ge hkj), mul_zero]
  · refine ⟨0, mem_range.mpr (Nat.zero_lt_succ m), ?_⟩
    simp

end RealRooted.JacobiDeformation
