import RealRooted.PFPolynomial
import RealRooted.MultiplierSequence
import RealRooted.VeroneseSection
import RealRooted.HurwitzMatrix
import RealRooted.Apolarity

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Hadamard products of real-rooted polynomials

This file defines the coefficientwise Hadamard product of two real
polynomials and records theorem interfaces for the classical preservation
results used by downstream combinatorial applications.

The main external reference is J. Garloff and D. G. Wagner, *Hadamard Products
of Stable Polynomials Are Stable*, J. Math. Anal. Appl. 202 (1996), 797--809.
Theorem 1 is the Hurwitz-stability form. Theorem 4 is the real-rooted
nonpositive-root form, including preservation of the interlacing/proper-position
relation.
-/

/-- Coefficientwise Hadamard product of two real polynomials. -/
def hadamardProduct (p q : ℝ[X]) : ℝ[X] :=
  p.sum fun n a => monomial n (a * q.coeff n)

@[simp] theorem coeff_hadamardProduct (p q : ℝ[X]) (n : ℕ) :
    (hadamardProduct p q).coeff n = p.coeff n * q.coeff n := by
  classical
  rw [hadamardProduct, Polynomial.coeff_sum]
  simp only [Polynomial.coeff_monomial]
  rw [Polynomial.sum_def]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _ hbn
    simp [hbn]
  · intro hn
    rw [(Polynomial.notMem_support_iff).mp hn]
    simp

theorem hadamardProduct_comm (p q : ℝ[X]) :
    hadamardProduct p q = hadamardProduct q p := by
  ext n
  simp [mul_comm]

/-- A Hadamard product is a diagonal operator whose diagonal is given by the
right factor's coefficients. -/
theorem hadamardProduct_eq_diagonalOperator (p q : ℝ[X]) :
    hadamardProduct p q = diagonalOperator (fun n => q.coeff n) p := by
  ext n
  rw [coeff_hadamardProduct, coeff_diagonalOperator, mul_comm]

theorem hadamardProduct_assoc (p q r : ℝ[X]) :
    hadamardProduct (hadamardProduct p q) r =
      hadamardProduct p (hadamardProduct q r) := by
  ext n
  simp [mul_assoc]

@[simp] theorem hadamardProduct_zero_left (p : ℝ[X]) :
    hadamardProduct 0 p = 0 := by
  ext n
  simp

@[simp] theorem hadamardProduct_zero_right (p : ℝ[X]) :
    hadamardProduct p 0 = 0 := by
  rw [hadamardProduct_comm, hadamardProduct_zero_left]

theorem hadamardProduct_add_left (p q r : ℝ[X]) :
    hadamardProduct (p + q) r =
      hadamardProduct p r + hadamardProduct q r := by
  rw [hadamardProduct_eq_diagonalOperator, diagonalOperator_add,
    ← hadamardProduct_eq_diagonalOperator p r,
    ← hadamardProduct_eq_diagonalOperator q r]

theorem hadamardProduct_add_right (p q r : ℝ[X]) :
    hadamardProduct p (q + r) =
      hadamardProduct p q + hadamardProduct p r := by
  rw [hadamardProduct_comm p (q + r), hadamardProduct_add_left,
    hadamardProduct_comm q p, hadamardProduct_comm r p]

theorem hadamardProduct_C_mul_left (a : ℝ) (p q : ℝ[X]) :
    hadamardProduct (C a * p) q =
      C a * hadamardProduct p q := by
  rw [hadamardProduct_eq_diagonalOperator, diagonalOperator_C_mul,
    ← hadamardProduct_eq_diagonalOperator p q]

theorem hadamardProduct_C_mul_right (a : ℝ) (p q : ℝ[X]) :
    hadamardProduct p (C a * q) =
      C a * hadamardProduct p q := by
  rw [hadamardProduct_comm p (C a * q), hadamardProduct_C_mul_left,
    hadamardProduct_comm q p]

theorem support_hadamardProduct_eq_filter_right (p q : ℝ[X]) :
    (hadamardProduct p q).support = p.support.filter fun n => q.coeff n ≠ 0 := by
  rw [hadamardProduct_eq_diagonalOperator, support_diagonalOperator_eq_filter]

theorem support_hadamardProduct_eq_filter_left (p q : ℝ[X]) :
    (hadamardProduct p q).support = q.support.filter fun n => p.coeff n ≠ 0 := by
  rw [hadamardProduct_comm]
  exact support_hadamardProduct_eq_filter_right q p

/-- The support of a Hadamard product is the intersection of the two
supports. -/
theorem support_hadamardProduct_eq (p q : ℝ[X]) :
    (hadamardProduct p q).support = p.support ∩ q.support := by
  rw [support_hadamardProduct_eq_filter_right]
  ext n
  simp [mem_support_iff]

/-- The support of a Hadamard product is contained in the left support. -/
theorem support_hadamardProduct_subset_left (p q : ℝ[X]) :
    (hadamardProduct p q).support ⊆ p.support := by
  rw [support_hadamardProduct_eq]
  exact Finset.inter_subset_left

/-- The support of a Hadamard product is contained in the right support. -/
theorem support_hadamardProduct_subset_right (p q : ℝ[X]) :
    (hadamardProduct p q).support ⊆ q.support := by
  rw [support_hadamardProduct_eq]
  exact Finset.inter_subset_right

theorem natDegree_hadamardProduct_le_left (p q : ℝ[X]) :
    (hadamardProduct p q).natDegree ≤ p.natDegree := by
  rw [hadamardProduct_eq_diagonalOperator]
  exact natDegree_diagonalOperator_le _ _

theorem natDegree_hadamardProduct_le_right (p q : ℝ[X]) :
    (hadamardProduct p q).natDegree ≤ q.natDegree := by
  rw [hadamardProduct_comm]
  exact natDegree_hadamardProduct_le_left q p

/-- A Hadamard product vanishes exactly when the two coefficient supports are
disjoint. -/
theorem hadamardProduct_eq_zero_iff_support_disjoint (p q : ℝ[X]) :
    hadamardProduct p q = 0 ↔ Disjoint p.support q.support := by
  rw [← support_eq_empty, support_hadamardProduct_eq,
    Finset.disjoint_iff_inter_eq_empty]

/-- Fixed-degree Schur--Szego composition.  If
`f = ∑ binom(n,k) a_k X^k` and `g = ∑ binom(n,k) b_k X^k`, then
`schurSzegoComp n f g = ∑ binom(n,k) a_k b_k X^k`. -/
def schurSzegoComp (n : Nat) (f g : ℝ[X]) : ℝ[X] :=
  Finset.sum (Finset.range (n + 1))
    (fun k => monomial k (f.coeff k * g.coeff k / (Nat.choose n k : ℝ)))

theorem coeff_schurSzegoComp (n k : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).coeff k =
      if k ≤ n then f.coeff k * g.coeff k / (Nat.choose n k : ℝ) else 0 := by
  rw [schurSzegoComp, finsetSum_coeff]
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    simp [coeff_monomial, hk]
  · rw [if_neg hk]
    simp [coeff_monomial, Nat.not_lt.mpr (Nat.succ_le_of_lt (Nat.lt_of_not_le hk))]

theorem coeff_schurSzegoComp_of_le {n k : Nat} (hk : k ≤ n) (f g : ℝ[X]) :
    (schurSzegoComp n f g).coeff k =
      f.coeff k * g.coeff k / (Nat.choose n k : ℝ) := by
  simp [coeff_schurSzegoComp, hk]

theorem coeff_schurSzegoComp_eq_zero_of_lt {n k : Nat} (hk : n < k) (f g : ℝ[X]) :
    (schurSzegoComp n f g).coeff k = 0 := by
  simp [coeff_schurSzegoComp, not_le_of_gt hk]

theorem schurSzegoComp_comm (n : Nat) (f g : ℝ[X]) :
    schurSzegoComp n f g = schurSzegoComp n g f := by
  ext k
  simp [coeff_schurSzegoComp, mul_comm]

theorem natDegree_schurSzegoComp_le (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hk =>
    coeff_schurSzegoComp_eq_zero_of_lt hk f g

/-- The fixed-degree Schur--Szegő composition of two binomial lifts is the
binomial lift of the coefficientwise Hadamard product of the underlying
coefficient sequences. -/
theorem schurSzegoComp_binomialLift (n : Nat) (f₀ g₀ : ℝ[X]) :
    schurSzegoComp n (binomialLift n f₀) (binomialLift n g₀) =
      binomialLift n (hadamardProduct f₀ g₀) := by
  ext k
  simp only [coeff_schurSzegoComp, coeff_binomialLift, coeff_hadamardProduct]
  by_cases hk : k ≤ n
  · simp only [if_pos hk]
    have hchoose : (Nat.choose n k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk).ne'
    field_simp
  · simp only [if_neg hk]

/-- Evaluation form of `schurSzegoComp_binomialLift`. -/
theorem schurSzegoComp_eval_eq_apolarEval (n : Nat) (f₀ g₀ : ℝ[X]) (z : ℝ) :
    (schurSzegoComp n (binomialLift n f₀) (binomialLift n g₀)).eval z =
      apolarEval n (hadamardProduct f₀ g₀) z := by
  rw [schurSzegoComp_binomialLift, eval_binomialLift]

theorem choose_mul_coeff_schurSzegoComp_of_le {n k : Nat} (hk : k ≤ n) (f g : ℝ[X]) :
    (Nat.choose n k : ℝ) * (schurSzegoComp n f g).coeff k =
      f.coeff k * g.coeff k := by
  rw [coeff_schurSzegoComp_of_le hk]
  field_simp [Nat.cast_choose_ne_zero (R := ℝ) hk]

theorem choose_mul_coeff_schurSzegoComp_eq_coeff_hadamardProduct_of_le
    {n k : Nat} (hk : k ≤ n) (f g : ℝ[X]) :
    (Nat.choose n k : ℝ) * (schurSzegoComp n f g).coeff k =
      (hadamardProduct f g).coeff k := by
  rw [choose_mul_coeff_schurSzegoComp_of_le hk, coeff_hadamardProduct]

/-- Fixed-degree Schur--Szego composition is a diagonal operator. -/
theorem schurSzegoComp_eq_diagonalOperator (n : Nat) (f g : ℝ[X]) :
    schurSzegoComp n f g =
      diagonalOperator (fun k => g.coeff k / (Nat.choose n k : ℝ)) f := by
  ext k
  rw [coeff_diagonalOperator, coeff_schurSzegoComp]
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    ring
  · rw [if_neg hk]
    simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hk)]

/-- Coefficient expansion of the cubic discriminant of a fixed-degree
Schur--Szegő composition.  This is the Schur--Szegő analogue of
`cubicDiscr_diagonalOperator`, with the second factor converted to the
normalized diagonal sequence `g.coeff k / Nat.choose n k`. -/
theorem cubicDiscr_schurSzegoComp (n : Nat) (f g : ℝ[X]) :
    cubicDiscr (schurSzegoComp n f g) =
      18 * ((g.coeff 3 / (Nat.choose n 3 : ℝ)) * f.coeff 3) *
          ((g.coeff 2 / (Nat.choose n 2 : ℝ)) * f.coeff 2) *
          ((g.coeff 1 / (Nat.choose n 1 : ℝ)) * f.coeff 1) *
          ((g.coeff 0 / (Nat.choose n 0 : ℝ)) * f.coeff 0)
        - 4 * ((g.coeff 2 / (Nat.choose n 2 : ℝ)) * f.coeff 2) ^ 3 *
          ((g.coeff 0 / (Nat.choose n 0 : ℝ)) * f.coeff 0)
        + ((g.coeff 2 / (Nat.choose n 2 : ℝ)) * f.coeff 2) ^ 2 *
          ((g.coeff 1 / (Nat.choose n 1 : ℝ)) * f.coeff 1) ^ 2
        - 4 * ((g.coeff 3 / (Nat.choose n 3 : ℝ)) * f.coeff 3) *
          ((g.coeff 1 / (Nat.choose n 1 : ℝ)) * f.coeff 1) ^ 3
        - 27 * ((g.coeff 3 / (Nat.choose n 3 : ℝ)) * f.coeff 3) ^ 2 *
          ((g.coeff 0 / (Nat.choose n 0 : ℝ)) * f.coeff 0) ^ 2 := by
  rw [schurSzegoComp_eq_diagonalOperator, cubicDiscr_diagonalOperator]

theorem support_schurSzegoComp_eq_filter_right (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).support =
      f.support.filter (fun k => g.coeff k / (Nat.choose n k : ℝ) ≠ 0) := by
  rw [schurSzegoComp_eq_diagonalOperator, support_diagonalOperator_eq_filter]

theorem support_schurSzegoComp_eq_filter_left (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).support =
      g.support.filter (fun k => f.coeff k / (Nat.choose n k : ℝ) ≠ 0) := by
  rw [schurSzegoComp_comm]
  exact support_schurSzegoComp_eq_filter_right n g f

theorem support_schurSzegoComp_eq_hadamardProduct_inter_range
    (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).support =
      (hadamardProduct f g).support ∩ Finset.range (n + 1) := by
  rw [support_schurSzegoComp_eq_filter_right, support_hadamardProduct_eq_filter_right]
  ext k
  by_cases hk : k ≤ n
  · have hchoose_nat : Nat.choose n k ≠ 0 := Nat.choose_ne_zero hk
    simp [Finset.mem_filter, Finset.mem_inter, Finset.mem_range, hk, hchoose_nat]
  · have hchoose_nat : Nat.choose n k = 0 :=
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hk)
    simp [Finset.mem_filter, Finset.mem_inter, Finset.mem_range, hk, hchoose_nat]

theorem support_schurSzegoComp_eq_hadamardProduct_of_hadamardProduct_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hfg : (hadamardProduct f g).natDegree ≤ n) :
    (schurSzegoComp n f g).support = (hadamardProduct f g).support := by
  rw [support_schurSzegoComp_eq_hadamardProduct_inter_range, Finset.inter_eq_left]
  intro k hk
  have hk_le : k ≤ (hadamardProduct f g).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (mem_support_iff.mp hk)
  simpa [Finset.mem_range] using Nat.lt_succ_of_le (hk_le.trans hfg)

theorem schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_hadamardProduct_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hfg : (hadamardProduct f g).natDegree ≤ n) :
    schurSzegoComp n f g = 0 ↔ hadamardProduct f g = 0 := by
  rw [← support_eq_empty, ← support_eq_empty,
    support_schurSzegoComp_eq_hadamardProduct_of_hadamardProduct_natDegree_le hfg]

theorem support_schurSzegoComp_eq_inter_of_hadamardProduct_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hfg : (hadamardProduct f g).natDegree ≤ n) :
    (schurSzegoComp n f g).support = f.support ∩ g.support := by
  rw [support_schurSzegoComp_eq_hadamardProduct_of_hadamardProduct_natDegree_le hfg,
    support_hadamardProduct_eq]

theorem schurSzegoComp_eq_zero_iff_support_disjoint_of_hadamardProduct_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hfg : (hadamardProduct f g).natDegree ≤ n) :
    schurSzegoComp n f g = 0 ↔ Disjoint f.support g.support := by
  rw [schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_hadamardProduct_natDegree_le hfg,
    hadamardProduct_eq_zero_iff_support_disjoint]

theorem support_schurSzegoComp_eq_hadamardProduct_of_left_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hf : f.natDegree ≤ n) :
    (schurSzegoComp n f g).support = (hadamardProduct f g).support :=
  support_schurSzegoComp_eq_hadamardProduct_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_left f g).trans hf)

theorem schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_left_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hf : f.natDegree ≤ n) :
    schurSzegoComp n f g = 0 ↔ hadamardProduct f g = 0 :=
  schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_left f g).trans hf)

theorem support_schurSzegoComp_eq_inter_of_left_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hf : f.natDegree ≤ n) :
    (schurSzegoComp n f g).support = f.support ∩ g.support :=
  support_schurSzegoComp_eq_inter_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_left f g).trans hf)

theorem schurSzegoComp_eq_zero_iff_support_disjoint_of_left_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hf : f.natDegree ≤ n) :
    schurSzegoComp n f g = 0 ↔ Disjoint f.support g.support :=
  schurSzegoComp_eq_zero_iff_support_disjoint_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_left f g).trans hf)

theorem support_schurSzegoComp_eq_hadamardProduct_of_right_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hg : g.natDegree ≤ n) :
    (schurSzegoComp n f g).support = (hadamardProduct f g).support :=
  support_schurSzegoComp_eq_hadamardProduct_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_right f g).trans hg)

theorem schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_right_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hg : g.natDegree ≤ n) :
    schurSzegoComp n f g = 0 ↔ hadamardProduct f g = 0 :=
  schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_right f g).trans hg)

theorem support_schurSzegoComp_eq_inter_of_right_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hg : g.natDegree ≤ n) :
    (schurSzegoComp n f g).support = f.support ∩ g.support :=
  support_schurSzegoComp_eq_inter_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_right f g).trans hg)

theorem schurSzegoComp_eq_zero_iff_support_disjoint_of_right_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hg : g.natDegree ≤ n) :
    schurSzegoComp n f g = 0 ↔ Disjoint f.support g.support :=
  schurSzegoComp_eq_zero_iff_support_disjoint_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_right f g).trans hg)

theorem schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le
    {n : Nat} {gamma : ℕ → ℝ} {p : ℝ[X]} (hp : p.natDegree ≤ n) :
    schurSzegoComp n (jensenPolynomial n gamma) p = diagonalOperator gamma p := by
  rw [schurSzegoComp_eq_diagonalOperator]
  ext k
  rw [coeff_diagonalOperator, coeff_diagonalOperator, coeff_jensenPolynomial]
  by_cases hk : k ≤ n
  · have hchoose : (Nat.choose n k : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℝ) hk
    simp only [hk, if_true]
    field_simp [hchoose]
  · have hk_lt : n < k := Nat.lt_of_not_le hk
    have hp_coeff : p.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hk_lt)
    simp [hk, hp_coeff]

@[simp] theorem schurSzegoComp_zero_left (n : Nat) (p : ℝ[X]) :
    schurSzegoComp n 0 p = 0 := by
  ext k
  simp [coeff_schurSzegoComp]

@[simp] theorem schurSzegoComp_zero_right (n : Nat) (f : ℝ[X]) :
    schurSzegoComp n f 0 = 0 := by
  rw [schurSzegoComp_comm, schurSzegoComp_zero_left]

/-- Schur--Szego composition is additive in its left argument. -/
theorem schurSzegoComp_add_left (n : Nat) (f f' g : ℝ[X]) :
    schurSzegoComp n (f + f') g =
      schurSzegoComp n f g + schurSzegoComp n f' g := by
  rw [schurSzegoComp_eq_diagonalOperator, diagonalOperator_add,
    ← schurSzegoComp_eq_diagonalOperator n f g,
    ← schurSzegoComp_eq_diagonalOperator n f' g]

/-- Schur--Szego composition is additive in its right argument. -/
theorem schurSzegoComp_add_right (n : Nat) (f g g' : ℝ[X]) :
    schurSzegoComp n f (g + g') =
      schurSzegoComp n f g + schurSzegoComp n f g' := by
  rw [schurSzegoComp_comm, schurSzegoComp_add_left, schurSzegoComp_comm n g f,
    schurSzegoComp_comm n g' f]

/-- Scalars pull out of the left argument of a Schur--Szego composition. -/
theorem schurSzegoComp_C_mul_left (n : Nat) (a : ℝ) (f g : ℝ[X]) :
    schurSzegoComp n (C a * f) g = C a * schurSzegoComp n f g := by
  rw [schurSzegoComp_eq_diagonalOperator, diagonalOperator_C_mul,
    ← schurSzegoComp_eq_diagonalOperator n f g]

/-- Scalars pull out of the right argument of a Schur--Szego composition. -/
theorem schurSzegoComp_C_mul_right (n : Nat) (a : ℝ) (f g : ℝ[X]) :
    schurSzegoComp n f (C a * g) = C a * schurSzegoComp n f g := by
  rw [schurSzegoComp_comm, schurSzegoComp_C_mul_left, schurSzegoComp_comm n g f]

theorem natDegree_schurSzegoComp_le_left (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).natDegree ≤ f.natDegree := by
  rw [schurSzegoComp_eq_diagonalOperator]
  exact natDegree_diagonalOperator_le _ _

theorem natDegree_schurSzegoComp_le_right (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).natDegree ≤ g.natDegree := by
  rw [schurSzegoComp_comm]
  exact natDegree_schurSzegoComp_le_left n g f

/-- The support of a Schur--Szego composition is contained in the left
support. -/
theorem support_schurSzegoComp_subset_left (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).support ⊆ f.support := by
  rw [support_schurSzegoComp_eq_filter_right]
  exact Finset.filter_subset _ _

/-- The support of a Schur--Szego composition is contained in the right
support. -/
theorem support_schurSzegoComp_subset_right (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).support ⊆ g.support := by
  rw [support_schurSzegoComp_eq_filter_left]
  exact Finset.filter_subset _ _

/-- Nonnegative coefficients are preserved by fixed-degree Schur--Szego
composition. -/
theorem HasNonnegCoeffs.schurSzegoComp {n : Nat} {f g : ℝ[X]}
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g) :
    HasNonnegCoeffs (schurSzegoComp n f g) := by
  rw [schurSzegoComp_eq_diagonalOperator]
  exact hf.diagonalOperator fun k => div_nonneg (hg k) (by positivity)

/-- **Finite Schur--Szegő composition theorem** (classical input).

If `f` is a PF polynomial (only real, nonpositive zeros) of degree at most `n`
and `p` has only real zeros, then their fixed-degree Schur--Szegő composition
`schurSzegoComp n f p` again has only real zeros, unless it vanishes
identically.

This is the classical composition/coincidence result of Schur and Szegő; it is
the single remaining analytic input behind the backward direction of the finite
Pólya--Schur theorem, isolated here as a named statement. -/
def finiteSchurSzegoCompositionStatement : Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    IsPFPolynomial f →
    f.natDegree ≤ n →
    p.natDegree ≤ n →
    p.Splits →
      schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits

/-- Nonzero core of the finite Schur--Szegő composition theorem.  The full
statement is equivalent to this one because the zero cases make the composition
identically zero. -/
def finiteSchurSzegoCompositionNonzeroStatement : Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    IsPFPolynomial f →
    f ≠ 0 →
    f.natDegree ≤ n →
    p ≠ 0 →
    p.natDegree ≤ n →
    p.Splits →
      schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits

theorem finiteSchurSzegoCompositionNonzero_of_full
    (h : finiteSchurSzegoCompositionStatement) :
    finiteSchurSzegoCompositionNonzeroStatement :=
  fun {_ _ _} hf _hf0 hfdeg _hp0 hpdeg hp => h hf hfdeg hpdeg hp

theorem finiteSchurSzegoComposition_of_nonzero
    (h : finiteSchurSzegoCompositionNonzeroStatement) :
    finiteSchurSzegoCompositionStatement := by
  intro n f p hf hfdeg hpdeg hp
  by_cases hf0 : f = 0
  · exact Or.inl (by rw [hf0]; exact schurSzegoComp_zero_left n p)
  by_cases hp0 : p = 0
  · exact Or.inl (by rw [hp0]; exact schurSzegoComp_zero_right n f)
  exact h hf hf0 hfdeg hp0 hpdeg hp

theorem finiteSchurSzegoCompositionStatement_iff_nonzero :
    finiteSchurSzegoCompositionStatement ↔
      finiteSchurSzegoCompositionNonzeroStatement :=
  ⟨finiteSchurSzegoCompositionNonzero_of_full,
    finiteSchurSzegoComposition_of_nonzero⟩

/-- The backward direction of the finite Pólya--Schur theorem follows, by a
`sorry`-free reduction, from the finite Schur--Szegő composition theorem: the
diagonal operator attached to `gamma` acting on a polynomial `p` of degree at
most `n` is exactly the Schur--Szegő composition of the PF Jensen polynomial of
`gamma` with `p`. -/
theorem finitePolyaSchurNonnegBackward_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement) :
    finitePolyaSchurNonnegBackwardStatement := by
  intro n gamma _hgamma hjensen p hp hsplit
  have hfdeg : (jensenPolynomial n gamma).natDegree ≤ n :=
    natDegree_jensenPolynomial_le n gamma
  have heq :
      schurSzegoComp n (jensenPolynomial n gamma) p = diagonalOperator gamma p :=
    schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le hp
  rw [← heq]
  exact hSZ hjensen hfdeg hp hsplit

/-- The backward finite Pólya--Schur direction follows directly from the
nonzero core of the finite Schur--Szegő theorem. -/
theorem finitePolyaSchurNonnegBackward_of_schurSzegoNonzero
    (hSZ : finiteSchurSzegoCompositionNonzeroStatement) :
    finitePolyaSchurNonnegBackwardStatement :=
  finitePolyaSchurNonnegBackward_of_schurSzego
    (finiteSchurSzegoComposition_of_nonzero hSZ)

/-- Full finite Pólya--Schur from the nonzero core of finite Schur--Szegő. -/
theorem finitePolyaSchur_nonneg_of_schurSzegoNonzero
    (hSZ : finiteSchurSzegoCompositionNonzeroStatement) :
    finitePolyaSchurNonnegStatement :=
  finitePolyaSchur_nonneg_of_backward
    (finitePolyaSchurNonnegBackward_of_schurSzegoNonzero hSZ)

/-- The finite Pólya--Schur theorem implies fixed-degree Schur--Szegő
composition.

The diagonal sequence used here is the binomially normalized coefficient
sequence of the PF factor.  The theorem
`jensenPolynomial_normalized_coeff_eq_of_natDegree_le` identifies its Jensen
polynomial with that factor, and the fixed-degree Schur--Szegő composition is
the corresponding diagonal operator on the other factor. -/
theorem finiteSchurSzegoComposition_of_finitePolyaSchur
    (hFPS : finitePolyaSchurNonnegStatement) :
    finiteSchurSzegoCompositionStatement := by
  intro n f p hf hfdeg hpdeg hsplit
  let gamma : ℕ → ℝ := fun k => f.coeff k / (Nat.choose n k : ℝ)
  have hgamma : ∀ k, 0 ≤ gamma k := fun k =>
    div_nonneg (hf.hasNonnegCoeffs k) (by positivity)
  have hjensen_eq : jensenPolynomial n gamma = f := by
    simpa [gamma] using jensenPolynomial_normalized_coeff_eq_of_natDegree_le hfdeg
  have hjensen : IsPFPolynomial (jensenPolynomial n gamma) := by
    rw [hjensen_eq]
    exact hf
  have hmult : IsFiniteMultiplierSequence n gamma :=
    (hFPS hgamma).2 hjensen
  have heq : schurSzegoComp n f p = diagonalOperator gamma p := by
    rw [schurSzegoComp_comm, schurSzegoComp_eq_diagonalOperator]
  rw [heq]
  exact hmult hpdeg hsplit

/-- Low-degree fixed-degree Schur--Szegő composition, through degree two.

This is the specialization of the finite Pólya--Schur route using the checked
degree-`≤ 2` backward theorem from `RealRooted.MultiplierSequence`; it does
not use the remaining classical Schur--Szegő input. -/
theorem finiteSchurSzegoComposition_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  let gamma : ℕ → ℝ := fun k => f.coeff k / (Nat.choose n k : ℝ)
  have hgamma : ∀ k, 0 ≤ gamma k := fun k =>
    div_nonneg (hf.hasNonnegCoeffs k) (by positivity)
  have hjensen_eq : jensenPolynomial n gamma = f := by
    simpa [gamma] using jensenPolynomial_normalized_coeff_eq_of_natDegree_le hfdeg
  have hjensen : IsPFPolynomial (jensenPolynomial n gamma) := by
    rw [hjensen_eq]
    exact hf
  have hmult : IsFiniteMultiplierSequence n gamma :=
    finitePolyaSchurNonnegBackward_of_natDegree_le_two hn hgamma hjensen
  have heq : schurSzegoComp n f p = diagonalOperator gamma p := by
    rw [schurSzegoComp_comm, schurSzegoComp_eq_diagonalOperator]
  rw [heq]
  exact hmult hpdeg hsplit

/-- Nonzero-core version of the checked degree-`≤ 2` Schur--Szegő composition
case. -/
theorem finiteSchurSzegoCompositionNonzero_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ n)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_natDegree_le_two hn hf hfdeg hpdeg hsplit

/-- Pure arithmetic core of the Schur--Szego discriminant inequality for two
degree-`≤ 2` factors at level `N ≥ 2`.  Here `a`, `b`, `c` are the coefficients
of the PF factor and `d`, `e`, `g` those of the splitting factor. -/
private theorem schurSzegoComp_disc_arith
    {a b c d e g N : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hfd : 4 * (a * c) ≤ b ^ 2)
    (hpd : 4 * (d * g) ≤ e ^ 2)
    (hN : 2 ≤ N) :
    4 * (a * d * (c * g / (N * (N - 1) / 2))) ≤ (b * e / N) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hN1ne : N - 1 ≠ 0 := ne_of_gt hN1
  have hac : 0 ≤ a * c := mul_nonneg ha hc
  have hkey : 4 * (a * d * (c * g / (N * (N - 1) / 2))) =
      8 * (a * c) * (d * g) / (N * (N - 1)) := by
    field_simp
    ring
  rw [hkey, div_pow, div_le_div_iff₀ (mul_pos hNpos hN1) (pow_pos hNpos 2)]
  rcases le_total (d * g) 0 with hdg | hdg
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hac (sq_nonneg N)) hdg,
      mul_nonneg (sq_nonneg (b * e)) (mul_pos hNpos hN1).le]
  · have h4dg : (0 : ℝ) ≤ 4 * (d * g) := by linarith
    have hmul : 4 * (a * c) * (4 * (d * g)) ≤ b ^ 2 * e ^ 2 :=
      mul_le_mul hfd hpd h4dg (sq_nonneg b)
    nlinarith [hmul, mul_nonneg hac hdg, sq_nonneg N,
      mul_nonneg (mul_nonneg hac hdg) (sq_nonneg N),
      mul_nonneg (mul_nonneg (sq_nonneg b) (sq_nonneg e))
        (mul_nonneg hNpos.le (show (0 : ℝ) ≤ N - 2 by linarith)),
      mul_nonneg (sq_nonneg (b * e)) (mul_pos hNpos hN1).le]

/-- **Schur--Szego discriminant inequality.**  For a level `n ≥ 2`, a PF factor
`f` of degree at most two, and a splitting factor `p` of degree at most two, the
fixed-degree Schur--Szego composition satisfies the quadratic discriminant
inequality `4 * coeff 0 * coeff 2 ≤ coeff 1 ^ 2`.

The two inputs to the estimate are the quadratic discriminant inequality
`quadratic_disc_coeff_le_of_splits_natDegree_le_two` applied to `f` (which
splits, being a PF polynomial) and to `p`, together with the nonnegativity of
the coefficients of `f`. -/
theorem four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp
    {n : ℕ} (hn : 2 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ 2) (hsplit : p.Splits) :
    4 * ((schurSzegoComp n f p).coeff 0 * (schurSzegoComp n f p).coeff 2) ≤
      (schurSzegoComp n f p).coeff 1 ^ 2 := by
  have h0n : 0 ≤ n := Nat.zero_le n
  have h1n : 1 ≤ n := le_trans (by norm_num) hn
  have hfd : 4 * (f.coeff 0 * f.coeff 2) ≤ f.coeff 1 ^ 2 := by
    rcases hf.eq_zero_or_splits with h | h
    · simp [h]
    · exact quadratic_disc_coeff_le_of_splits_natDegree_le_two hfdeg h
  have hpd : 4 * (p.coeff 0 * p.coeff 2) ≤ p.coeff 1 ^ 2 :=
    quadratic_disc_coeff_le_of_splits_natDegree_le_two hpdeg hsplit
  have hf0 : 0 ≤ f.coeff 0 := hf.hasNonnegCoeffs 0
  have hf2 : 0 ≤ f.coeff 2 := hf.hasNonnegCoeffs 2
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [coeff_schurSzegoComp_of_le h0n, coeff_schurSzegoComp_of_le h1n,
    coeff_schurSzegoComp_of_le hn, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.cast_one, div_one, Nat.cast_choose_two]
  exact schurSzegoComp_disc_arith hf0 hf2 hfd hpd hnR

/-- **Low-degree fixed-degree Schur--Szego composition (degree-`≤ 2` factors).**

For an arbitrary level `n`, a PF polynomial `f` of degree at most two, and a
splitting polynomial `p` of degree at most two, the fixed-degree Schur--Szego
composition `schurSzegoComp n f p` is either zero or splits over `ℝ`.

The composition has degree at most two, so it is settled by the quadratic
discriminant inequality
`four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp`; the
low-level cases `n ≤ 1` (where the composition already has degree at most one)
are handled separately.  Unlike
`finiteSchurSzegoComposition_of_natDegree_le_two`, here the level `n` is
unrestricted and the degree bound is placed on the two factors. -/
theorem finiteSchurSzegoComposition_of_factors_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ 2) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  by_cases hq0 : schurSzegoComp n f p = 0
  · exact Or.inl hq0
  by_cases hqle1 : (schurSzegoComp n f p).natDegree ≤ 1
  · exact Or.inr (isRealRooted_of_natDegree_le_one hq0 hqle1).2
  have hqle2 : (schurSzegoComp n f p).natDegree ≤ 2 :=
    le_trans (natDegree_schurSzegoComp_le_left n f p) hfdeg
  have hqdeg : (schurSzegoComp n f p).natDegree = 2 :=
    le_antisymm hqle2 (Nat.succ_le_of_lt (not_le.mp hqle1))
  have hn : 2 ≤ n := hqdeg ▸ natDegree_schurSzegoComp_le n f p
  have hdisc : 0 ≤ (schurSzegoComp n f p).coeff 1 ^ 2 -
      4 * (schurSzegoComp n f p).coeff 2 * (schurSzegoComp n f p).coeff 0 := by
    have := four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp
      hn hf hfdeg hpdeg hsplit
    nlinarith [this]
  obtain ⟨x, hx⟩ := exists_root_of_disc_nonneg
    (a := (schurSzegoComp n f p).coeff 2)
    (b := (schurSzegoComp n f p).coeff 1)
    (c := (schurSzegoComp n f p).coeff 0)
    (by
      have hlc : (schurSzegoComp n f p).leadingCoeff ≠ 0 :=
        leadingCoeff_ne_zero.mpr hq0
      rwa [Polynomial.leadingCoeff, hqdeg] at hlc)
    hdisc
  have hroot : (schurSzegoComp n f p).IsRoot x := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_eq_sum_range, hqdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    linear_combination hx
  exact Or.inr (Polynomial.Splits.of_natDegree_eq_two hqdeg hroot)

/-- Newton's first coefficient inequality (`k = 1`) for a real polynomial that
splits and has degree at least two, in the level-`natDegree` normalization:
`2 * natDegree * coeff 0 * coeff 2 ≤ (natDegree - 1) * coeff 1 ^ 2`.

This is the splitting-only form of the ultra-log-concavity inequality
`hasUltraLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits` at index
`k = 1`; no nonnegativity of the coefficients is assumed. -/
theorem two_natDegree_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits
    {p : ℝ[X]} (hdeg : 2 ≤ p.natDegree) (hs : p.Splits) :
    2 * (p.natDegree : ℝ) * (p.coeff 0 * p.coeff 2) ≤
      ((p.natDegree : ℝ) - 1) * p.coeff 1 ^ 2 := by
  set t := p.roots.map Neg.neg with ht_def
  have htcard : Multiset.card t = p.natDegree := by
    rw [ht_def, Multiset.card_map, card_roots_of_splits hs]
  have h1d : 1 ≤ p.natDegree := le_trans one_le_two hdeg
  have hc0 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 0) (Nat.zero_le _)
  have hc1 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 1) h1d
  have hc2 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 2) hdeg
  rw [← ht_def] at hc0 hc1 hc2
  have hnewton := NewtonAux.newton_esymm_ineq t (n := p.natDegree)
    (m := p.natDegree - 1) htcard
    (Nat.sub_pos_of_lt (lt_of_lt_of_le one_lt_two hdeg))
    (Nat.sub_lt (lt_of_lt_of_le (by norm_num) hdeg) Nat.one_pos)
  have idxm1 : p.natDegree - 1 - 1 = p.natDegree - 2 := by rw [Nat.sub_sub]
  have idxp1 : p.natDegree - 1 + 1 = p.natDegree := Nat.sub_add_cancel h1d
  rw [idxm1, idxp1] at hnewton
  have hi0 : p.natDegree - 0 = p.natDegree := Nat.sub_zero _
  rw [hi0] at hc0
  have hcast_m : ((p.natDegree - 1 : ℕ) : ℝ) = (p.natDegree : ℝ) - 1 := by
    rw [Nat.cast_sub h1d]
    norm_num
  have hself : p.natDegree - (p.natDegree - 1) = 1 := Nat.sub_sub_self h1d
  have hcast_nm : ((p.natDegree - (p.natDegree - 1) : ℕ) : ℝ) = 1 := by
    rw [hself]
    norm_num
  have hcast_nm1 : ((p.natDegree - (p.natDegree - 1) + 1 : ℕ) : ℝ) = 2 := by
    rw [hself]
    norm_num
  rw [hcast_m, hcast_nm, hcast_nm1] at hnewton
  rw [hc0, hc1, hc2]
  nlinarith [mul_le_mul_of_nonneg_left hnewton (sq_nonneg p.leadingCoeff),
    sq_nonneg p.leadingCoeff]

/-- Level-lift arithmetic for Newton's `k = 1` inequality: an inequality in the
level-`N` normalization lifts to any larger level `M ≥ N`.  The key algebraic
identity is
`(N - 1) * ((M - 1) * A - 2 * M * B) =
  (M - 1) * ((N - 1) * A - 2 * N * B) + 2 * B * (M - N)`. -/
private theorem newton_level_lift_arith {A B M N : ℝ}
    (hA : 0 ≤ A) (hMN : N ≤ M) (hN1 : 1 < N)
    (hnat : 2 * N * B ≤ (N - 1) * A) :
    2 * M * B ≤ (M - 1) * A := by
  rcases le_or_gt B 0 with hB | hB
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ M - 1 by linarith) hA,
      mul_nonneg (show (0 : ℝ) ≤ M by linarith)
        (show (0 : ℝ) ≤ -B by linarith)]
  · have key : (N - 1) * ((M - 1) * A - 2 * M * B)
        = (M - 1) * ((N - 1) * A - 2 * N * B) + 2 * B * (M - N) := by
      ring
    nlinarith [key,
      mul_nonneg (show (0 : ℝ) ≤ M - 1 by linarith)
        (show (0 : ℝ) ≤ (N - 1) * A - 2 * N * B by linarith),
      mul_nonneg hB.le (show (0 : ℝ) ≤ M - N by linarith), hN1]

/-- Newton's first coefficient inequality (`k = 1`) in the level-`n`
normalization, for a splitting polynomial of degree at most `n`.  It is the
level-`natDegree` inequality
`two_natDegree_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits` lifted to
level `n` via `newton_level_lift_arith`; the low-degree cases (`natDegree ≤ 1`)
have `coeff 2 = 0`. -/
theorem two_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_of_natDegree_le
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) (hs : p.Splits) :
    2 * (n : ℝ) * (p.coeff 0 * p.coeff 2) ≤ ((n : ℝ) - 1) * p.coeff 1 ^ 2 := by
  rcases le_or_gt 2 p.natDegree with hdeg | hdeg
  · have hnat :=
      two_natDegree_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits hdeg hs
    have hNn : (p.natDegree : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpdeg
    have h1N : (1 : ℝ) < (p.natDegree : ℝ) := by
      have : (2 : ℝ) ≤ (p.natDegree : ℝ) := by exact_mod_cast hdeg
      linarith
    exact newton_level_lift_arith (A := p.coeff 1 ^ 2)
      (B := p.coeff 0 * p.coeff 2) (M := (n : ℝ)) (N := (p.natDegree : ℝ))
      (sq_nonneg _) hNn h1N hnat
  · have hc2 : p.coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt hdeg
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [hc2]
    nlinarith [sq_nonneg (p.coeff 1), hnR]

/-- Pure arithmetic core of the Schur--Szego discriminant inequality when only
the PF factor has degree at most two.  Here `a`, `b`, `c` are the coefficients of
the PF factor and `d`, `e`, `g` those of the splitting factor, with the level-`N`
Newton inequality `2 N (d g) ≤ (N - 1) e^2` replacing the quadratic
discriminant of the splitting factor. -/
private theorem schurSzegoComp_pf_disc_arith
    {a b c d e g N : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hfd : 4 * (a * c) ≤ b ^ 2)
    (hpd : 2 * N * (d * g) ≤ (N - 1) * e ^ 2)
    (hN : 2 ≤ N) :
    4 * (a * d * (c * g / (N * (N - 1) / 2))) ≤ (b * e / N) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have hac : 0 ≤ a * c := mul_nonneg ha hc
  have hkey : 4 * (a * d * (c * g / (N * (N - 1) / 2))) =
      8 * (a * c) * (d * g) / (N * (N - 1)) := by
    field_simp
    ring
  rw [hkey, div_pow, div_le_div_iff₀ (mul_pos hNpos hN1) (pow_pos hNpos 2)]
  rcases le_total (d * g) 0 with hdg | hdg
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hac (sq_nonneg N)) hdg,
      mul_nonneg (sq_nonneg (b * e)) (mul_pos hNpos hN1).le]
  · have hmul : 4 * (a * c) * (2 * N * (d * g)) ≤
        b ^ 2 * ((N - 1) * e ^ 2) :=
      mul_le_mul hfd hpd (by nlinarith [hdg, hNpos.le]) (sq_nonneg b)
    nlinarith [mul_le_mul_of_nonneg_right hmul hNpos.le, sq_nonneg (b * e)]

/-- **Schur--Szego discriminant inequality with a degree-`≤ 2` PF factor.**
For a level `n ≥ 2`, a PF factor `f` of degree at most two, and a splitting
factor `p` of arbitrary degree at most `n`, the fixed-degree Schur--Szego
composition satisfies the quadratic discriminant inequality
`4 * coeff 0 * coeff 2 ≤ coeff 1 ^ 2`.

The input for `f` is its degree-`≤ 2` quadratic discriminant inequality
`quadratic_disc_coeff_le_of_splits_natDegree_le_two` (with the nonnegativity of
its coefficients); the input for `p` is the level-`n` Newton inequality
`two_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_of_natDegree_le`. -/
theorem four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp_of_pf
    {n : ℕ} (hn : 2 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    4 * ((schurSzegoComp n f p).coeff 0 * (schurSzegoComp n f p).coeff 2) ≤
      (schurSzegoComp n f p).coeff 1 ^ 2 := by
  have h0n : 0 ≤ n := Nat.zero_le n
  have h1n : 1 ≤ n := le_trans (by norm_num) hn
  have hfd : 4 * (f.coeff 0 * f.coeff 2) ≤ f.coeff 1 ^ 2 := by
    rcases hf.eq_zero_or_splits with h | h
    · simp [h]
    · exact quadratic_disc_coeff_le_of_splits_natDegree_le_two hfdeg h
  have hpd : 2 * (n : ℝ) * (p.coeff 0 * p.coeff 2) ≤
      ((n : ℝ) - 1) * p.coeff 1 ^ 2 :=
    two_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_of_natDegree_le
      hn hpdeg hsplit
  have hf0 : 0 ≤ f.coeff 0 := hf.hasNonnegCoeffs 0
  have hf2 : 0 ≤ f.coeff 2 := hf.hasNonnegCoeffs 2
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [coeff_schurSzegoComp_of_le h0n, coeff_schurSzegoComp_of_le h1n,
    coeff_schurSzegoComp_of_le hn, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.cast_one, div_one, Nat.cast_choose_two]
  exact schurSzegoComp_pf_disc_arith hf0 hf2 hfd hpd hnR

/-- **Fixed-degree Schur--Szego composition with a degree-`≤ 2` PF factor.**

For an arbitrary level `n`, a PF polynomial `f` of degree at most two, and a
splitting polynomial `p` of arbitrary degree at most `n`, the fixed-degree
Schur--Szego composition `schurSzegoComp n f p` is either zero or splits over
`ℝ`.

The composition has degree at most two (it inherits the degree bound of the PF
factor), so it is settled by the quadratic discriminant inequality
`four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp_of_pf`; the
low-level cases (composition of degree at most one) are handled separately.
Unlike `finiteSchurSzegoComposition_of_factors_natDegree_le_two`, here the
splitting factor `p` may have arbitrary degree up to the level `n`. -/
theorem finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  by_cases hq0 : schurSzegoComp n f p = 0
  · exact Or.inl hq0
  by_cases hqle1 : (schurSzegoComp n f p).natDegree ≤ 1
  · exact Or.inr (isRealRooted_of_natDegree_le_one hq0 hqle1).2
  have hqle2 : (schurSzegoComp n f p).natDegree ≤ 2 :=
    le_trans (natDegree_schurSzegoComp_le_left n f p) hfdeg
  have hqdeg : (schurSzegoComp n f p).natDegree = 2 :=
    le_antisymm hqle2 (Nat.succ_le_of_lt (not_le.mp hqle1))
  have hn : 2 ≤ n := hqdeg ▸ natDegree_schurSzegoComp_le n f p
  have hdisc : 0 ≤ (schurSzegoComp n f p).coeff 1 ^ 2 -
      4 * (schurSzegoComp n f p).coeff 2 * (schurSzegoComp n f p).coeff 0 := by
    have := four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp_of_pf
      hn hf hfdeg hpdeg hsplit
    nlinarith [this]
  obtain ⟨x, hx⟩ := exists_root_of_disc_nonneg
    (a := (schurSzegoComp n f p).coeff 2)
    (b := (schurSzegoComp n f p).coeff 1)
    (c := (schurSzegoComp n f p).coeff 0)
    (by
      have hlc : (schurSzegoComp n f p).leadingCoeff ≠ 0 :=
        leadingCoeff_ne_zero.mpr hq0
      rwa [Polynomial.leadingCoeff, hqdeg] at hlc)
    hdisc
  have hroot : (schurSzegoComp n f p).IsRoot x := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_eq_sum_range, hqdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    linear_combination hx
  exact Or.inr (Polynomial.Splits.of_natDegree_eq_two hqdeg hroot)

/-- Nonzero-core version of the arbitrary-level Schur--Szego base case with a
degree-`≤ 2` PF factor. -/
theorem finiteSchurSzegoCompositionNonzero_of_pf_factor_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 2)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
    hf hfdeg hpdeg hsplit

/-- If the degree-`n` Jensen polynomial is PF and itself has degree at most
two, then the diagonal sequence is a finite multiplier sequence through degree
`n`.

Unlike `isFiniteMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two`,
the degree bound here is on the Jensen polynomial, not on the ambient level
`n`.  The proof is the Schur--Szegő base case with a degree-`≤ 2` PF factor,
applied to the Jensen polynomial and then identified with the diagonal
operator. -/
theorem isFiniteMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma))
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFiniteMultiplierSequence n gamma := by
  intro p hp hsplit
  have hschur : schurSzegoComp n (jensenPolynomial n gamma) p = 0 ∨
      (schurSzegoComp n (jensenPolynomial n gamma) p).Splits :=
    finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
      hjensen hjdeg hp hsplit
  have heq : schurSzegoComp n (jensenPolynomial n gamma) p =
      diagonalOperator gamma p :=
    schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le hp
  rwa [heq] at hschur

/-- PF-preservation version of
`isFiniteMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two`. -/
theorem isFinitePFMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma))
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_finiteMultiplierSequence hgamma
    (isFiniteMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
      hjensen hjdeg)

/-- Finite multiplier sequences are classified by the PF Jensen polynomial in
the special case where that Jensen polynomial has degree at most two. -/
theorem isFiniteMultiplierSequence_iff_jensenPolynomial_of_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFiniteMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  ⟨isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence hgamma,
    fun hjensen =>
      isFiniteMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
        hjensen hjdeg⟩

/-- PF-preservation classification in the special case where the Jensen
polynomial has degree at most two. -/
theorem isFinitePFMultiplierSequence_iff_jensenPolynomial_of_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFinitePFMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  ⟨isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence,
    fun hjensen =>
      isFinitePFMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
        hgamma hjensen hjdeg⟩

/-- Nonzero-core version of the arbitrary-level degree-`≤ 2` Schur--Szego
base case. -/
theorem finiteSchurSzegoCompositionNonzero_of_factors_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 2)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ 2) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_factors_natDegree_le_two
    hf hfdeg hpdeg hsplit

/-- Cubic-discriminant splitting route for the fixed-degree Schur--Szegő
composition with a degree-`≤ 3` factor.

Once the fixed-degree Schur--Szegő composition's cubic coefficient discriminant
`cubicDiscr (schurSzegoComp n f p)` is known to be nonnegative, the composition
is either zero or splits over `ℝ`.  The composition inherits the degree bound of
the degree-`≤ 3` factor `f` via `natDegree_schurSzegoComp_le_left`, so the
result is the degree-`≤ 3` cubic discriminant criterion applied to it. -/
theorem finiteSchurSzegoComposition_of_natDegree_le_three_cubicDiscr_nonneg
    {n : ℕ} {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3)
    (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p)) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  by_cases hq0 : schurSzegoComp n f p = 0
  · exact Or.inl hq0
  · refine Or.inr (splits_of_natDegree_le_three_cubicDiscr_nonneg ?_ hdisc)
    exact le_trans (natDegree_schurSzegoComp_le_left n f p) hfdeg

/-- Nonzero-core version of the degree-`≤ 3` cubic-discriminant splitting route
for the fixed-degree Schur--Szegő composition. -/
theorem finiteSchurSzegoCompositionNonzero_of_natDegree_le_three_cubicDiscr_nonneg
    {n : ℕ} {f p : ℝ[X]} (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p)) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_natDegree_le_three_cubicDiscr_nonneg
    hfdeg hdisc

/-- The full finite Schur--Szegő theorem implies the finite Pólya--Schur
theorem. -/
theorem finitePolyaSchur_nonneg_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement) :
    finitePolyaSchurNonnegStatement :=
  finitePolyaSchur_nonneg_of_backward
    (finitePolyaSchurNonnegBackward_of_schurSzego hSZ)

/-- Fixed-degree Schur--Szegő composition and finite Pólya--Schur are
equivalent classical inputs in the nonnegative-coefficient convention used
here. -/
theorem finiteSchurSzegoCompositionStatement_iff_finitePolyaSchur :
    finiteSchurSzegoCompositionStatement ↔ finitePolyaSchurNonnegStatement :=
  ⟨finitePolyaSchur_nonneg_of_schurSzego,
    finiteSchurSzegoComposition_of_finitePolyaSchur⟩

/-- The finite Pólya--Schur theorem implies the nonzero core of fixed-degree
Schur--Szegő composition. -/
theorem finiteSchurSzegoCompositionNonzero_of_finitePolyaSchur
    (hFPS : finitePolyaSchurNonnegStatement) :
    finiteSchurSzegoCompositionNonzeroStatement :=
  finiteSchurSzegoCompositionNonzero_of_full
    (finiteSchurSzegoComposition_of_finitePolyaSchur hFPS)

/-- The nonzero core of fixed-degree Schur--Szegő composition and finite
Pólya--Schur are equivalent classical inputs in the local convention. -/
theorem finiteSchurSzegoCompositionNonzeroStatement_iff_finitePolyaSchur :
    finiteSchurSzegoCompositionNonzeroStatement ↔ finitePolyaSchurNonnegStatement :=
  ⟨finitePolyaSchur_nonneg_of_schurSzegoNonzero,
    finiteSchurSzegoCompositionNonzero_of_finitePolyaSchur⟩

/-- The nonzero Schur--Szegő core is equivalent to the hard backward direction
of finite Pólya--Schur. -/
theorem finiteSchurSzegoCompositionNonzeroStatement_iff_finitePolyaSchurBackward :
    finiteSchurSzegoCompositionNonzeroStatement ↔
      finitePolyaSchurNonnegBackwardStatement :=
  ⟨finitePolyaSchurNonnegBackward_of_schurSzegoNonzero,
    fun hBack =>
      finiteSchurSzegoCompositionNonzero_of_finitePolyaSchur
        (finitePolyaSchur_nonneg_of_backward hBack)⟩

/-- Nonzero finite Schur--Szegő composition theorem.  This is the substantive
classical leaf: `f` is a nonzero PF polynomial, `p` is a nonzero real-rooted
polynomial, both have degree at most `n`, and the fixed-degree Schur--Szegő
composition is either zero or real-rooted. -/
theorem finiteSchurSzegoCompositionNonzero :
    finiteSchurSzegoCompositionNonzeroStatement := by
  intro n f p hf hf0 hfdeg hp0 hp hsplit
  sorry

/-- Finite Schur--Szegő composition theorem. The degenerate cases (`f = 0` or
`p = 0`, where the composition vanishes) are discharged by
`finiteSchurSzegoComposition_of_nonzero`; the remaining classical content is
`finiteSchurSzegoCompositionNonzero`. -/
theorem finiteSchurSzegoComposition : finiteSchurSzegoCompositionStatement :=
  finiteSchurSzegoComposition_of_nonzero finiteSchurSzegoCompositionNonzero

/-- Directly applicable form of the finite Schur--Szegő composition theorem:
for a PF polynomial `f` and a real-rooted polynomial `p`, both of degree at most
`n`, the fixed-degree Schur--Szegő composition is either zero or real-rooted. -/
theorem schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hp : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition hf hfdeg hpdeg hp

/-- The backward direction of the finite Pólya--Schur theorem, obtained from the
finite Schur--Szegő composition theorem. -/
theorem finitePolyaSchurNonnegBackward : finitePolyaSchurNonnegBackwardStatement :=
  finitePolyaSchurNonnegBackward_of_schurSzegoNonzero finiteSchurSzegoCompositionNonzero

/-- Classical finite Pólya--Schur theorem (nonnegative-coefficient convention).
The only remaining analytic obligation is isolated in
`finiteSchurSzegoComposition`. -/
theorem finitePolyaSchur_nonneg : finitePolyaSchurNonnegStatement :=
  finitePolyaSchur_nonneg_of_schurSzegoNonzero finiteSchurSzegoCompositionNonzero

/-- Nonnegative coefficients are preserved by coefficientwise Hadamard
products. -/
theorem HasNonnegCoeffs.hadamardProduct {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (hadamardProduct p q) := by
  rw [hadamardProduct_eq_diagonalOperator]
  exact hp.diagonalOperator hq

/-- **Odd/even Hadamard identity.**  The coefficientwise Hadamard product
commutes with the odd/even construction `oddEvenPolynomial p q = q(x²) + x·p(x²)`:
the even coefficients multiply the `q`-parts and the odd coefficients multiply
the `p`-parts. This is the algebraic bridge that reduces the two-pair
Garloff--Wagner interlacing theorem to the single-polynomial Hurwitz-stability
fact through the Hermite--Biehler odd/even correspondence. -/
theorem hadamardProduct_oddEvenPolynomial (p q p' q' : ℝ[X]) :
    hadamardProduct (oddEvenPolynomial p q) (oddEvenPolynomial p' q') =
      oddEvenPolynomial (hadamardProduct p p') (hadamardProduct q q') := by
  ext n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [show k + k = 2 * k by ring]
    simp
  · subst hk
    simp

/-- Nonnegative-coefficient Schur--Polya/Garloff--Wagner real-rootedness
interface for coefficientwise Hadamard products.

Garloff--Wagner, Theorem 4(a), proves this in the standard-polynomial setting
with only nonpositive zeros. The hypotheses below are the corresponding
nonnegative-coefficient wrapper: real-rooted nonzero polynomials with
nonnegative coefficients automatically have only nonpositive roots. The conclusion is
zero-aware because the Hadamard product can vanish when supports are disjoint.
-/
def garloffWagnerHadamardNonnegRealRootedStatement : Prop :=
  ∀ {p q : ℝ[X]},
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    (p ≠ 0 ∧ p.Splits) →
    (q ≠ 0 ∧ q.Splits) →
    (hadamardProduct p q = 0 ∨ (hadamardProduct p q).Splits) ∧
      HasNonnegCoeffs (hadamardProduct p q) ∧
      ∀ r ∈ (hadamardProduct p q).roots, r ≤ 0

theorem IsPFPolynomial.hadamardProduct
    (hGW : garloffWagnerHadamardNonnegRealRootedStatement)
    {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) := by
  by_cases hp0 : p = 0
  · subst p
    simpa using IsPFPolynomial.zero
  by_cases hq0 : q = 0
  · subst q
    simpa using IsPFPolynomial.zero
  rcases hGW hp.hasNonnegCoeffs hq.hasNonnegCoeffs
      (hp.ne_zero_and_splits hp0)
      (hq.ne_zero_and_splits hq0) with ⟨hrr, hnn, hroots⟩
  exact ⟨hnn, hrr, hroots⟩

/-- Polynomial PF form of the Schur--Polya--Wagner Hadamard theorem. -/
def schurPolyaWagnerHadamardPFStatement : Prop :=
  ∀ {p q : ℝ[X]},
    IsPFPolynomial p →
    IsPFPolynomial q →
    IsPFPolynomial (hadamardProduct p q)

theorem schurPolyaWagnerHadamardPF_of_garloffWagner_nonneg
    (hGW : garloffWagnerHadamardNonnegRealRootedStatement) :
    schurPolyaWagnerHadamardPFStatement :=
  fun {_ _} hp hq => hp.hadamardProduct hGW hq

/-- Nonnegative-coefficient Garloff--Wagner interlacing interface for
coefficientwise Hadamard products.

This is the `Prec`/`Prec0` wrapper around Garloff--Wagner, Theorem 4(b):
if two nonnegative-coefficient real-rooted pairs are in the same
proper-position relation, then the pair of Hadamard products is again in
proper position.  The conclusion is zero-aware for the same support reason as
`garloffWagnerHadamardNonnegRealRootedStatement`.

Orientation audit: in this repository `Prec f g` is the convention `f ≪ g`.
In the differ-by-one case, `g` has the rightmost root; in the same-degree case,
each root of `f` is weakly to the left of the corresponding root of `g`.  Thus
for linear factors we have `Prec (X + C b) (X + C a) ↔ a ≤ b`, because their
roots are `-b` and `-a`.  Consequently the Garloff--Wagner hypotheses written
as `g $ f` and `q $ p` are represented here as `Prec f g` and `Prec p q`, and
the conclusion is `Prec0 (f ⊙ p) (g ⊙ q)`.

TODO T9: formalize this statement in RealRooted, following Garloff--Wagner,
Theorem 4(b).  It is the remaining standard input used by the SuperEulerian
proof through its `StandardFacts` bundle.
-/
def garloffWagnerHadamardNonnegPrecStatement : Prop :=
  ∀ {f g p q : ℝ[X]},
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    Prec f g →
    Prec p q →
    Prec0 (hadamardProduct f p) (hadamardProduct g q)

/-- Linear-factor sanity check for the orientation used in
`garloffWagnerHadamardNonnegPrecStatement`. -/
theorem garloffWagnerHadamard_linear_orientation_sanity {a b : ℝ} :
    Prec (X + C b) (X + C a) ↔ a ≤ b :=
  prec_X_add_C_iff

/-- **Hadamard product preserves Hurwitz stability** (Garloff--Wagner,
Theorem 1) — precise external interface.

This is the main theorem of Garloff--Wagner, *Hadamard Products of Stable
Polynomials Are Stable*: the coefficientwise Hadamard product of two
Hurwitz-stable real polynomials is again Hurwitz stable. In the present
`IsHurwitzStable` convention this is the genuinely deep classical input (its
classical proofs go through Polya--Schur / total-nonnegativity machinery that is
not available in Mathlib), recorded here as a precise interface. This is the
only new external interface needed below; the remaining inputs are the
Hermite--Biehler odd/even bridges already recorded in
`RealRooted.VeroneseSection`. -/
def hadamardPreservesHurwitzStableStatement : Prop :=
  ∀ {a b : ℝ[X]},
    IsHurwitzStable a →
    IsHurwitzStable b →
    IsHurwitzStable (hadamardProduct a b)

/-! ### Sharper sub-interfaces for Garloff--Wagner Theorem 1

The Hurwitz-stability conclusion `IsHurwitzStable (hadamardProduct a b)` unfolds
to two parts: nonnegativity of the coefficients and right-half-plane stability
of the complexification.  The first part is elementary
(`HasNonnegCoeffs.hadamardProduct`); the genuinely deep content is the second
part.  We record that split, and the faithful Hurwitz-matrix decomposition of
Garloff--Wagner Theorem 1, as checked `sorry`-free reductions. -/

/-- The deep half of Garloff--Wagner Theorem 1: the complexified coefficientwise
Hadamard product of two right-half-plane-stable, nonnegative-coefficient
polynomials is again right-half-plane stable. -/
def hadamardPreservesRightHalfPlaneStableStatement : Prop :=
  ∀ {a b : ℝ[X]},
    HasNonnegCoeffs a →
    HasNonnegCoeffs b →
    IsRightHalfPlaneStable (complexify a) →
    IsRightHalfPlaneStable (complexify b) →
    IsRightHalfPlaneStable (complexify (hadamardProduct a b))

/-- Reduction of Garloff--Wagner Theorem 1 to its deep half: the
nonnegative-coefficient half of Hurwitz stability is discharged here, so only
right-half-plane stability of the product remains. -/
theorem hadamardPreservesHurwitzStable_of_rightHalfPlane
    (h : hadamardPreservesRightHalfPlaneStableStatement) :
    hadamardPreservesHurwitzStableStatement :=
  fun {_ _} ha hb => ⟨ha.1.hadamardProduct hb.1, h ha.1 hb.1 ha.2 hb.2⟩

/-- The analytic core is conversely implied by Garloff--Wagner Theorem 1, so the
two interfaces are equivalent: isolating the right-half-plane half loses no
content. -/
theorem hadamardPreservesRightHalfPlaneStable_of_hurwitzStable
    (h : hadamardPreservesHurwitzStableStatement) :
    hadamardPreservesRightHalfPlaneStableStatement :=
  fun {_ _} hann hbnn harhp hbrhp => (h ⟨hann, harhp⟩ ⟨hbnn, hbrhp⟩).2

/-- Garloff--Wagner Theorem 1 is equivalent to its right-half-plane analytic
core; coefficient nonnegativity of the product is elementary. -/
theorem hadamardPreservesHurwitzStable_iff_rightHalfPlane :
    hadamardPreservesHurwitzStableStatement ↔
      hadamardPreservesRightHalfPlaneStableStatement :=
  ⟨hadamardPreservesRightHalfPlaneStable_of_hurwitzStable,
    hadamardPreservesHurwitzStable_of_rightHalfPlane⟩

/-- The combinatorial heart of Garloff--Wagner Theorem 1, as a pure matrix
statement: total nonnegativity of the row-oriented Hurwitz matrix is preserved
under coefficientwise products. -/
def hadamardPreservesHurwitzMatrixTNStatement : Prop :=
  ∀ {a b : ℝ[X]},
    (hurwitz a.coeff).IsTotallyNonneg →
    (hurwitz b.coeff).IsTotallyNonneg →
    (hurwitz (hadamardProduct a b).coeff).IsTotallyNonneg

/-- Faithful Hurwitz-matrix decomposition of Garloff--Wagner Theorem 1.

This mirrors the classical proof through the Asner--Kemperman Hurwitz-matrix
total-nonnegativity criterion: forward criterion, matrix Hadamard core, and
converse criterion. -/
theorem hadamardPreservesHurwitzStable_of_matrixRoute
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hHad : hadamardPreservesHurwitzMatrixTNStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    hadamardPreservesHurwitzStableStatement :=
  fun {_ _} ha hb => hBwd (hHad (hFwd ha) (hFwd hb))

/-- Hurwitz-matrix form of the coefficientwise Hadamard product of two
polynomials. -/
theorem hurwitz_hadamardProduct_matrix (a b : ℝ[X]) :
    hurwitz (hadamardProduct a b).coeff =
      Matrix.of fun i j => hurwitz a.coeff i j * hurwitz b.coeff i j := by
  rw [show (hadamardProduct a b).coeff = fun n => a.coeff n * b.coeff n by
    funext n
    exact coeff_hadamardProduct a b n]
  exact hurwitz_mul_entrywise_matrix a.coeff b.coeff

/-- Low-order checked part of the Hurwitz-matrix Hadamard leaf: every minor of
size at most two is nonnegative.  The first remaining case for
`hadamardPreservesHurwitzMatrixTNStatement` is the `3 × 3` Hurwitz-specific
minor. -/
theorem hadamardPreservesHurwitzMatrixTN_det_of_card_le_two
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg)
    {n : ℕ} {rows cols : Fin n → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hn : n ≤ 2) :
    0 ≤ (((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det) := by
  rw [hurwitz_hadamardProduct_matrix]
  exact hurwitz_schurProduct_det_of_card_le_two ha hb hrows hcols hn

/-- Structural `3 × 3` band-fail case for the Hurwitz matrix of a Hadamard
product.  This is the polynomial-facing form of
`hurwitz_schurProduct_det_fin_three_of_band_fail`. -/
theorem hurwitz_hadamardProduct_det_fin_three_of_band_fail
    {a b : ℝ[X]} {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows)
    (hcols : StrictMono cols) (l : Fin 3) (hl : rows l < 2 * cols l) :
    ((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det = 0 := by
  rw [hurwitz_hadamardProduct_matrix]
  exact hurwitz_schurProduct_det_fin_three_of_band_fail hrows hcols l hl

/-- Nonnegativity form of the structural `3 × 3` band-fail case for the
Hurwitz matrix of a Hadamard product. -/
theorem hurwitz_hadamardProduct_det_fin_three_nonneg_of_band_fail
    {a b : ℝ[X]} {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows)
    (hcols : StrictMono cols) (l : Fin 3) (hl : rows l < 2 * cols l) :
    0 ≤ ((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det := by
  rw [hurwitz_hadamardProduct_det_fin_three_of_band_fail hrows hcols l hl]

/-- `3 × 3` Hurwitz-matrix Hadamard minors from the pure in-band `3 × 3`
matrix core.  The out-of-band case is handled structurally by the
band-fail zero lemma. -/
theorem hadamardPreservesHurwitzMatrixTN_det_fin_three
    (hInBand : HurwitzMatrixSchurProductDetFinThreeInBandStatement)
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg)
    {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 ≤ ((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det := by
  rw [hurwitz_hadamardProduct_matrix]
  exact hurwitz_schurProduct_det_fin_three hInBand ha hb hrows hcols

/-- Low-order checked part of the Hurwitz-matrix Hadamard leaf through size
three, assuming the pure in-band `3 × 3` matrix core. -/
theorem hadamardPreservesHurwitzMatrixTN_det_of_card_le_three
    (hInBand : HurwitzMatrixSchurProductDetFinThreeInBandStatement)
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg)
    {n : ℕ} {rows cols : Fin n → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hn : n ≤ 3) :
    0 ≤ (((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det) := by
  rw [hurwitz_hadamardProduct_matrix]
  exact hurwitz_schurProduct_det_of_card_le_three hInBand ha hb hrows hcols hn

/-- Low-order, size-`≤ 3`, form of the Hurwitz-matrix Hadamard leaf. -/
def hadamardPreservesHurwitzMatrixTNDetLeThreeStatement : Prop :=
  ∀ {a b : ℝ[X]},
    (hurwitz a.coeff).IsTotallyNonneg →
    (hurwitz b.coeff).IsTotallyNonneg →
    ∀ {n : ℕ} {rows cols : Fin n → ℕ},
      StrictMono rows →
      StrictMono cols →
      n ≤ 3 →
      0 ≤ (((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det)

/-- The isolated in-band `3 × 3` core implies the low-order, size-`≤ 3`,
Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_inBand
    (hInBand : HurwitzMatrixSchurProductDetFinThreeInBandStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement := by
  intro a b ha hb n rows cols hrows hcols hn
  exact hadamardPreservesHurwitzMatrixTN_det_of_card_le_three
    hInBand ha hb hrows hcols hn

/-- The fully in-band top-right subcase of the `3 × 3` Hurwitz Schur-product
core implies the low-order, size-`≤ 3`, Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_fullBand
    (hF : HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_inBand
    (hurwitzMatrixSchurProductDetFinThreeInBand_of_fullBand hF)

/-- The single-matrix corner-zeroed determinant subtarget implies the
low-order, size-`≤ 3`, Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingle
    (hSingle :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_inBand
    (hurwitzMatrixSchurProductDetFinThreeInBand_of_cornerZeroedSingle hSingle)

/-- The column-normalized single-matrix corner-zeroed determinant subtarget
implies the low-order, size-`≤ 3`, Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleColZero
    (hZero :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingle
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingle_of_colZero hZero)

/-- The first-column normal form implies the low-order, size-`≤ 3`,
Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleFirstCol
    (hFirst :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleColZero
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_firstCol
      hFirst)

/-- The strict-remainder first-column branch implies the low-order,
size-`≤ 3`, Hurwitz-matrix Hadamard leaf. -/
theorem
    hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleFirstColPositiveRemainder
    (hPos : HurwitzMatrixSchurProductDetFirstColPositiveRemainderStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleFirstCol
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_positiveRemainder
      hPos)

/-- The pure size-`≤ 3` Hurwitz matrix Schur-product statement implies the
Hadamard-product Hurwitz-matrix size-`≤ 3` statement. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_hurwitzLeThree
    (hLeThree : HurwitzMatrixSchurProductDetLeThreeStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement := by
  intro a b ha hb n rows cols hrows hcols hn
  rw [hurwitz_hadamardProduct_matrix]
  exact hLeThree ha hb hrows hcols hn

/-- The full Hurwitz-matrix Hadamard leaf implies its named low-order,
size-`≤ 3`, consequence. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_matrixTN
    (h : hadamardPreservesHurwitzMatrixTNStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement := by
  intro a b ha hb n rows cols hrows hcols _hn
  exact h ha hb hrows hcols

/-- The Hurwitz-matrix Hadamard leaf reduces to the pure matrix Schur core.

Using `hurwitz_mul_entrywise_matrix`, this strips away the coefficient
bookkeeping from `hadamardPreservesHurwitzMatrixTNStatement`; the remaining
input is only that entrywise products of totally nonnegative Hurwitz matrices
are totally nonnegative. -/
theorem hadamardPreservesHurwitzMatrixTN_of_schur
    (h : HurwitzMatrixSchurProductTNStatement) :
    hadamardPreservesHurwitzMatrixTNStatement := by
  intro a b ha hb
  rw [hurwitz_hadamardProduct_matrix]
  exact h ha hb

/-- Odd/even coefficient-subsequence PF consequence of the Hurwitz-matrix
Hadamard leaf. -/
def hadamardPreservesHurwitzMatrixOddEvenPFStatement : Prop :=
  ∀ {a b : ℝ[X]},
    (hurwitz a.coeff).IsTotallyNonneg →
    (hurwitz b.coeff).IsTotallyNonneg →
    IsPolyaFreqSeq (fun n => (hadamardProduct a b).coeff (2 * n + 1)) ∧
      IsPolyaFreqSeq (fun n => (hadamardProduct a b).coeff (2 * n))

/-- The Hurwitz-matrix Hadamard leaf makes the odd coefficient subsequence of
the Hadamard product Pólya-frequency. -/
theorem hadamardProduct_oddCoeff_isPolyaFreqSeq_of_matrixTN
    (h : hadamardPreservesHurwitzMatrixTNStatement)
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg) :
    IsPolyaFreqSeq (fun n => (hadamardProduct a b).coeff (2 * n + 1)) :=
  hurwitz_isPolyaFreqSeq_odd (h ha hb)

/-- The Hurwitz-matrix Hadamard leaf makes the even coefficient subsequence of
the Hadamard product Pólya-frequency. -/
theorem hadamardProduct_evenCoeff_isPolyaFreqSeq_of_matrixTN
    (h : hadamardPreservesHurwitzMatrixTNStatement)
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg) :
    IsPolyaFreqSeq (fun n => (hadamardProduct a b).coeff (2 * n)) :=
  hurwitz_isPolyaFreqSeq_even (h ha hb)

/-- Bundled odd/even PF consequence of the Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixOddEvenPF_of_matrixTN
    (h : hadamardPreservesHurwitzMatrixTNStatement) :
    hadamardPreservesHurwitzMatrixOddEvenPFStatement :=
  fun {_ _} ha hb =>
    ⟨hadamardProduct_oddCoeff_isPolyaFreqSeq_of_matrixTN h ha hb,
      hadamardProduct_evenCoeff_isPolyaFreqSeq_of_matrixTN h ha hb⟩

/-- The pure Hurwitz Schur-product core gives the odd/even PF consequence for
Hadamard products. -/
theorem hadamardPreservesHurwitzMatrixOddEvenPF_of_schur
    (h : HurwitzMatrixSchurProductTNStatement) :
    hadamardPreservesHurwitzMatrixOddEvenPFStatement :=
  hadamardPreservesHurwitzMatrixOddEvenPF_of_matrixTN
    (hadamardPreservesHurwitzMatrixTN_of_schur h)

/-- The pure Hurwitz Schur-product core implies the named low-order,
size-`≤ 3`, Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_schur
    (h : HurwitzMatrixSchurProductTNStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_matrixTN
    (hadamardPreservesHurwitzMatrixTN_of_schur h)

/-- Garloff--Wagner Theorem 1 from the pure Hurwitz Schur-product core and the
two directions of the Hurwitz-matrix criterion. -/
theorem hadamardPreservesHurwitzStable_of_hurwitzSchur
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hSchur : HurwitzMatrixSchurProductTNStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    hadamardPreservesHurwitzStableStatement :=
  hadamardPreservesHurwitzStable_of_matrixRoute hFwd
    (hadamardPreservesHurwitzMatrixTN_of_schur hSchur) hBwd

/-- The Hurwitz-matrix Hadamard leaf also follows from Garloff--Wagner
Theorem 1 plus both directions of the Hurwitz-matrix total-nonnegativity
criterion.  Together with `hadamardPreservesHurwitzStable_of_matrixRoute`, this
records the equivalence of the matrix leaf and Theorem 1 modulo that criterion. -/
theorem hadamardPreservesHurwitzMatrixTN_of_stableRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hadamardPreservesHurwitzStableStatement)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hadamardPreservesHurwitzMatrixTNStatement :=
  fun {_ _} ha hb => hFwd (hThm1 (hBwd ha) (hBwd hb))

/-- Low-order Hurwitz-matrix Hadamard minors from Garloff--Wagner Theorem 1
plus both directions of the Hurwitz-matrix total-nonnegativity criterion. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_stableRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hadamardPreservesHurwitzStableStatement)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_matrixTN
    (hadamardPreservesHurwitzMatrixTN_of_stableRoute hBwd hThm1 hFwd)

/-- Odd/even PF consequence from Garloff--Wagner Theorem 1 plus both
directions of the Hurwitz-matrix total-nonnegativity criterion. -/
theorem hadamardPreservesHurwitzMatrixOddEvenPF_of_stableRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hadamardPreservesHurwitzStableStatement)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hadamardPreservesHurwitzMatrixOddEvenPFStatement :=
  hadamardPreservesHurwitzMatrixOddEvenPF_of_matrixTN
    (hadamardPreservesHurwitzMatrixTN_of_stableRoute hBwd hThm1 hFwd)

/-- Under the two directions of the Hurwitz-matrix criterion, Garloff--Wagner
Theorem 1 is equivalent to the Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzStable_iff_matrixTN
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    hadamardPreservesHurwitzStableStatement ↔
      hadamardPreservesHurwitzMatrixTNStatement :=
  ⟨fun h => hadamardPreservesHurwitzMatrixTN_of_stableRoute hBwd h hFwd,
    fun h => hadamardPreservesHurwitzStable_of_matrixRoute hFwd h hBwd⟩

/-- Under the Hurwitz-matrix criterion, the right-half-plane analytic core of
Garloff--Wagner Theorem 1 is equivalent to the matrix Hadamard leaf. -/
theorem hadamardPreservesRightHalfPlaneStable_iff_matrixTN
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    hadamardPreservesRightHalfPlaneStableStatement ↔
      hadamardPreservesHurwitzMatrixTNStatement :=
  hadamardPreservesHurwitzStable_iff_rightHalfPlane.symm.trans
    (hadamardPreservesHurwitzStable_iff_matrixTN hFwd hBwd)

/-- The matrix route also gives the right-half-plane analytic core directly. -/
theorem hadamardPreservesRightHalfPlaneStable_of_matrixRoute
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hHad : hadamardPreservesHurwitzMatrixTNStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    hadamardPreservesRightHalfPlaneStableStatement :=
  (hadamardPreservesRightHalfPlaneStable_iff_matrixTN hFwd hBwd).2 hHad

/-- Conversely, the right-half-plane analytic core gives the matrix leaf through
the Hurwitz-matrix criterion. -/
theorem hadamardPreservesHurwitzMatrixTN_of_rightHalfPlaneRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : hadamardPreservesRightHalfPlaneStableStatement)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hadamardPreservesHurwitzMatrixTNStatement :=
  (hadamardPreservesRightHalfPlaneStable_iff_matrixTN hFwd hBwd).1 hRHP

/-- Odd/even PF consequence from the right-half-plane analytic core plus the
Hurwitz-matrix total-nonnegativity criterion. -/
theorem hadamardPreservesHurwitzMatrixOddEvenPF_of_rightHalfPlaneRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : hadamardPreservesRightHalfPlaneStableStatement)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hadamardPreservesHurwitzMatrixOddEvenPFStatement :=
  hadamardPreservesHurwitzMatrixOddEvenPF_of_matrixTN
    (hadamardPreservesHurwitzMatrixTN_of_rightHalfPlaneRoute hBwd hRHP hFwd)

/-- The pure Hurwitz Schur-product core implies the right-half-plane analytic
core, modulo the two directions of the Hurwitz-matrix criterion. -/
theorem hadamardPreservesRightHalfPlaneStable_of_hurwitzSchur
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hSchur : HurwitzMatrixSchurProductTNStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    hadamardPreservesRightHalfPlaneStableStatement :=
  hadamardPreservesRightHalfPlaneStable_of_matrixRoute hFwd
    (hadamardPreservesHurwitzMatrixTN_of_schur hSchur) hBwd

/-- **Garloff--Wagner, Theorem 4(b), reduced to its classical inputs** (TODO T9).

The two-pair interlacing form of the Garloff--Wagner Hadamard theorem follows,
with a fully checked (`sorry`-free) reduction, from the following classical
inputs (the latter three are pre-existing interfaces from
`RealRooted.VeroneseSection`):

* `hadamardPreservesHurwitzStableStatement` — Garloff--Wagner Theorem 1
  (Hadamard products of Hurwitz-stable polynomials are Hurwitz stable);
* `NonnegPrecToHurwitzOddEvenStatement` — the forward Hermite--Biehler bridge
  from proper position `Prec f g` of nonnegative-coefficient polynomials to
  Hurwitz stability of `oddEvenPolynomial f g = g(x²) + x·f(x²)`;
* `HurwitzOddEvenToFullyInterlacingPairStatement` — from Hurwitz stability of
  the odd/even polynomial to full interlacing of the coefficient rows; and
* `FullyInterlacingPairToPrec0Statement` — the converse lace-to-interlacing
  bridge back to zero-aware proper position.

The bridge between the two-pair and single-polynomial worlds is the proven
algebraic identity `hadamardProduct_oddEvenPolynomial`:
`oddEvenPolynomial f g ⊙ oddEvenPolynomial p q
   = oddEvenPolynomial (f ⊙ p) (g ⊙ q)`,
whose even part is `g ⊙ q` and whose odd part is `f ⊙ p`.

Thus all of the interlacing bookkeeping of Theorem 4(b) is discharged here.
Note that the odd/even polynomial of an interlacing pair is Hurwitz stable, not
real-rooted (e.g. `f = 1`, `g = X + 1` gives `X² + X + 1`), which is why the
reduction goes through `IsHurwitzStable` (Theorem 1) rather than the
single-polynomial real-rootedness fact
`garloffWagnerHadamardNonnegRealRootedStatement`. -/
theorem garloffWagnerHadamardNonnegPrec_of_oddEven
    (hThm1 : hadamardPreservesHurwitzStableStatement)
    (hPrecToHurwitz : NonnegPrecToHurwitzOddEvenStatement)
    (hHurwitzToFull : HurwitzOddEvenToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerHadamardNonnegPrecStatement := by
  intro f g p q hf hg hp hq hfg hpq
  have hOE1 : IsHurwitzStable (oddEvenPolynomial f g) := hPrecToHurwitz hf hg hfg
  have hOE2 : IsHurwitzStable (oddEvenPolynomial p q) := hPrecToHurwitz hp hq hpq
  have hHad :
      IsHurwitzStable
        (hadamardProduct (oddEvenPolynomial f g) (oddEvenPolynomial p q)) :=
    hThm1 hOE1 hOE2
  rw [hadamardProduct_oddEvenPolynomial] at hHad
  exact hFullToPrec0 (hHurwitzToFull hHad)

/-- **Garloff--Wagner two-pair theorem reduced to its irreducible classical
inputs** (issue #34 / TODO T9).

This composes the existing checked reductions for the four mid-level interfaces
used by `garloffWagnerHadamardNonnegPrec_of_oddEven` into a single `sorry`-free
reduction of the #34 target `garloffWagnerHadamardNonnegPrecStatement` onto six
classical bottom-level inputs:

* `hadamardPreservesRightHalfPlaneStableStatement` — the analytic core of
  Garloff--Wagner Theorem 1;
* `hermiteBiehlerForwardPosStatement` and
  `HermiteBiehlerStableToHurwitzOddEvenStatement` — the forward
  Hermite--Biehler bridge and conformal substitution;
* `HurwitzStableToMatrixTotallyNonnegativeStatement` — the forward matrix
  Hurwitz criterion;
* `aissenSchoenbergWhitneyForwardStatement` and
  `FullyInterlacingPairInterlaceStatement` — forward
  Aissen--Schoenberg--Whitney and the combinatorial interlacing-extraction
  core.

This pins down the remaining analytic and combinatorial obligations for the
#34 target in one place. -/
theorem garloffWagnerHadamardNonnegPrec_of_classicalInputs
    (hRHP : hadamardPreservesRightHalfPlaneStableStatement)
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerHadamardNonnegPrecStatement :=
  garloffWagnerHadamardNonnegPrec_of_oddEven
    (hadamardPreservesHurwitzStable_of_rightHalfPlane hRHP)
    (nonnegPrecToHurwitzOddEven_of_hermiteBiehlerPos hHB hHBToHurwitz)
    (hurwitzOddEvenToFullyInterlacingPair_of_matrixTNN hHurwitzToMatrix)
    (fullyInterlacingPairToPrec0_of_forwardASW_interlace hASW hInt)

/-- The six classical inputs for the Garloff--Wagner two-pair theorem, with
the shared Hermite--Biehler/Hurwitz-matrix route bundled. -/
structure GarloffWagnerClassicalInputs : Prop where
  /-- Analytic core of Garloff--Wagner Theorem 1. -/
  hadamardPreservesRightHalfPlaneStable : hadamardPreservesRightHalfPlaneStableStatement
  /-- Shared sign-normalized Hermite--Biehler/Hurwitz-matrix route. -/
  route : HermiteBiehlerHurwitzRoute
  /-- Forward Aissen--Schoenberg--Whitney. -/
  aissenSchoenbergWhitneyForward : aissenSchoenbergWhitneyForwardStatement
  /-- Combinatorial interlacing-extraction core. -/
  fullyInterlacingPairInterlace : FullyInterlacingPairInterlaceStatement

/-- Garloff--Wagner two-pair theorem reduced to a bundled set of classical
inputs. -/
theorem garloffWagnerHadamardNonnegPrec_of_classicalInputsBundle
    (h : GarloffWagnerClassicalInputs) :
    garloffWagnerHadamardNonnegPrecStatement :=
  garloffWagnerHadamardNonnegPrec_of_classicalInputs
    h.hadamardPreservesRightHalfPlaneStable
    h.route.hermiteBiehlerForwardPos
    h.route.hermiteBiehlerStableToHurwitzOddEven
    h.route.hurwitzStableToMatrixTotallyNonnegative
    h.aissenSchoenbergWhitneyForward
    h.fullyInterlacingPairInterlace

/-- Garloff--Wagner two-pair theorem via the pure Hurwitz-matrix Hadamard
core.

This sharper reduction of issue #34 avoids converting the product back to
Hurwitz stability.  It stays in the total-nonnegativity/interlacing dictionary:
proper position gives fully interlacing coefficient rows, the matrix Hadamard
core preserves total nonnegativity of the odd/even Hurwitz matrix, and the
converse dictionary returns zero-aware proper position. -/
theorem garloffWagnerHadamardNonnegPrec_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerHadamardNonnegPrecStatement := by
  intro f g p q hf hg hp hq hfg hpq
  have hFull1 : FullyInterlacingPair f.coeff (fun n => g.coeff n) :=
    hToFull hf hg hfg
  have hFull2 : FullyInterlacingPair p.coeff (fun n => q.coeff n) :=
    hToFull hp hq hpq
  have hM1 : (hurwitz (oddEvenPolynomial f g).coeff).IsTotallyNonneg :=
    (hurwitzMatrixTotallyNonnegative_oddEvenPolynomial_iff_fullyInterlacingPair
      f g).mpr hFull1
  have hM2 : (hurwitz (oddEvenPolynomial p q).coeff).IsTotallyNonneg :=
    (hurwitzMatrixTotallyNonnegative_oddEvenPolynomial_iff_fullyInterlacingPair
      p q).mpr hFull2
  have hMprod := hMatHad hM1 hM2
  rw [hadamardProduct_oddEvenPolynomial] at hMprod
  have hFull :
      FullyInterlacingPair (hadamardProduct f p).coeff
        (fun n => (hadamardProduct g q).coeff n) :=
    (hurwitzMatrixTotallyNonnegative_oddEvenPolynomial_iff_fullyInterlacingPair
      (hadamardProduct f p) (hadamardProduct g q)).mp hMprod
  exact hFullToPrec0 hFull

/-- Garloff--Wagner two-pair theorem via the pure Hurwitz Schur-product core. -/
theorem garloffWagnerHadamardNonnegPrec_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hSchur : HurwitzMatrixSchurProductTNStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerHadamardNonnegPrecStatement :=
  garloffWagnerHadamardNonnegPrec_of_matrixHadamardBridges hToFull
    (hadamardPreservesHurwitzMatrixTN_of_schur hSchur) hFullToPrec0

/-- Matrix-core version of the Garloff--Wagner two-pair reduction, with the
non-Hadamard leaves discharged by the shared Hermite--Biehler route and the
forward Aissen--Schoenberg--Whitney/interlacing-extraction route. -/
theorem garloffWagnerHadamardNonnegPrec_of_matrixClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerHadamardNonnegPrecStatement :=
  garloffWagnerHadamardNonnegPrec_of_matrixHadamardBridges
    hRoute.toNonnegPrecToFullyInterlacingPair
    hMatHad
    (fullyInterlacingPairToPrec0_of_forwardASW_interlace hASW hInt)

theorem garloffWagnerHadamardNonnegPrec_of_hurwitzSchurClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hSchur : HurwitzMatrixSchurProductTNStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerHadamardNonnegPrecStatement :=
  garloffWagnerHadamardNonnegPrec_of_matrixClassicalInputs hRoute
    (hadamardPreservesHurwitzMatrixTN_of_schur hSchur) hASW hInt

/-- PF-polynomial wrapper around the strict Garloff--Wagner two-pair theorem. -/
def garloffWagnerHadamardPFPrecStatement : Prop :=
  ∀ {f g p q : ℝ[X]},
    IsPFPolynomial f →
    IsPFPolynomial g →
    IsPFPolynomial p →
    IsPFPolynomial q →
    Prec f g →
    Prec p q →
    Prec0 (hadamardProduct f p) (hadamardProduct g q)

theorem garloffWagnerHadamardPFPrec_of_nonnegPrec
    (hGW : garloffWagnerHadamardNonnegPrecStatement) :
    garloffWagnerHadamardPFPrecStatement :=
  fun {_ _ _ _} hf hg hp hq hfg hpq =>
    hGW hf.hasNonnegCoeffs hg.hasNonnegCoeffs
      hp.hasNonnegCoeffs hq.hasNonnegCoeffs hfg hpq

/-- Zero-aware PF-polynomial wrapper around the Garloff--Wagner two-pair
theorem. This is the form most convenient for recursive arguments where a
support specialization may produce the zero polynomial. -/
def garloffWagnerHadamardPFPrec0Statement : Prop :=
  ∀ {f g p q : ℝ[X]},
    IsPFPolynomial f →
    IsPFPolynomial g →
    IsPFPolynomial p →
    IsPFPolynomial q →
    Prec0 f g →
    Prec0 p q →
    Prec0 (hadamardProduct f p) (hadamardProduct g q)

theorem garloffWagnerHadamardPFPrec0_of_prec
    (hGW : garloffWagnerHadamardPFPrecStatement) :
    garloffWagnerHadamardPFPrec0Statement := by
  intro f g p q hf hg hp hq hfg hpq
  rcases hfg with rfl | rfl | hfg'
  · simpa using prec0_zero_left (hadamardProduct g q)
  · simpa using prec0_zero_right (hadamardProduct f p)
  rcases hpq with rfl | rfl | hpq'
  · simpa using prec0_zero_left (hadamardProduct g q)
  · simpa using prec0_zero_right (hadamardProduct f p)
  exact hGW hf hg hp hq hfg' hpq'

theorem garloffWagnerHadamardPFPrec0_of_nonnegPrec
    (hGW : garloffWagnerHadamardNonnegPrecStatement) :
    garloffWagnerHadamardPFPrec0Statement :=
  garloffWagnerHadamardPFPrec0_of_prec
    (garloffWagnerHadamardPFPrec_of_nonnegPrec hGW)

theorem garloffWagnerHadamardPFPrec0_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerHadamardPFPrec0Statement :=
  garloffWagnerHadamardPFPrec0_of_nonnegPrec
    (garloffWagnerHadamardNonnegPrec_of_matrixHadamardBridges
      hToFull hMatHad hFullToPrec0)

theorem garloffWagnerHadamardPFPrec0_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hSchur : HurwitzMatrixSchurProductTNStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerHadamardPFPrec0Statement :=
  garloffWagnerHadamardPFPrec0_of_nonnegPrec
    (garloffWagnerHadamardNonnegPrec_of_hurwitzSchur
      hToFull hSchur hFullToPrec0)

theorem garloffWagnerHadamardPFPrec0_of_matrixClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerHadamardPFPrec0Statement :=
  garloffWagnerHadamardPFPrec0_of_nonnegPrec
    (garloffWagnerHadamardNonnegPrec_of_matrixClassicalInputs
      hRoute hMatHad hASW hInt)

theorem garloffWagnerHadamardPFPrec0_of_hurwitzSchurClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hSchur : HurwitzMatrixSchurProductTNStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerHadamardPFPrec0Statement :=
  garloffWagnerHadamardPFPrec0_of_nonnegPrec
    (garloffWagnerHadamardNonnegPrec_of_hurwitzSchurClassicalInputs
      hRoute hSchur hASW hInt)

/-- PF-polynomial closure under Hadamard product, stated directly from the
zero-aware Garloff--Wagner PF wrapper. -/
theorem hadamardProduct_preserves_pf_of_garloffWagner
    (hGW : garloffWagnerHadamardPFPrec0Statement)
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) :=
  IsPFPolynomial.of_prec0_self
    (hp.hasNonnegCoeffs.hadamardProduct hq.hasNonnegCoeffs)
    (hGW hp hp hq hq hp.prec0_self hq.prec0_self)

theorem hadamardProduct_preserves_pf_of_nonnegPrec
    (hGW : garloffWagnerHadamardNonnegPrecStatement)
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) :=
  hadamardProduct_preserves_pf_of_garloffWagner
    (garloffWagnerHadamardPFPrec0_of_nonnegPrec hGW) hp hq

theorem hadamardProduct_preserves_pf_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) :=
  hadamardProduct_preserves_pf_of_garloffWagner
    (garloffWagnerHadamardPFPrec0_of_matrixHadamardBridges
      hToFull hMatHad hFullToPrec0) hp hq

theorem hadamardProduct_preserves_pf_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hSchur : HurwitzMatrixSchurProductTNStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) :=
  hadamardProduct_preserves_pf_of_garloffWagner
    (garloffWagnerHadamardPFPrec0_of_hurwitzSchur
      hToFull hSchur hFullToPrec0) hp hq

theorem hadamardProduct_preserves_pf_of_matrixClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement)
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) :=
  hadamardProduct_preserves_pf_of_garloffWagner
    (garloffWagnerHadamardPFPrec0_of_matrixClassicalInputs
      hRoute hMatHad hASW hInt) hp hq

theorem hadamardProduct_preserves_pf_of_hurwitzSchurClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hSchur : HurwitzMatrixSchurProductTNStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement)
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) :=
  hadamardProduct_preserves_pf_of_garloffWagner
    (garloffWagnerHadamardPFPrec0_of_hurwitzSchurClassicalInputs
      hRoute hSchur hASW hInt) hp hq

theorem schurPolyaWagnerHadamardPF_of_garloffWagner_prec0
    (hGW : garloffWagnerHadamardPFPrec0Statement) :
    schurPolyaWagnerHadamardPFStatement :=
  fun {_ _} hp hq => hadamardProduct_preserves_pf_of_garloffWagner hGW hp hq

theorem schurPolyaWagnerHadamardPF_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    schurPolyaWagnerHadamardPFStatement :=
  fun {_ _} hp hq =>
    hadamardProduct_preserves_pf_of_matrixHadamardBridges
      hToFull hMatHad hFullToPrec0 hp hq

theorem schurPolyaWagnerHadamardPF_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hSchur : HurwitzMatrixSchurProductTNStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    schurPolyaWagnerHadamardPFStatement :=
  fun {_ _} hp hq =>
    hadamardProduct_preserves_pf_of_hurwitzSchur
      hToFull hSchur hFullToPrec0 hp hq

theorem schurPolyaWagnerHadamardPF_of_matrixClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    schurPolyaWagnerHadamardPFStatement :=
  fun {_ _} hp hq =>
    hadamardProduct_preserves_pf_of_matrixClassicalInputs
      hRoute hMatHad hASW hInt hp hq

theorem schurPolyaWagnerHadamardPF_of_hurwitzSchurClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hSchur : HurwitzMatrixSchurProductTNStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    schurPolyaWagnerHadamardPFStatement :=
  fun {_ _} hp hq =>
    hadamardProduct_preserves_pf_of_hurwitzSchurClassicalInputs
      hRoute hSchur hASW hInt hp hq

/-- The nonnegative two-pair Garloff--Wagner theorem gives PF closure under
Hadamard products through the zero-aware PF wrapper. -/
theorem schurPolyaWagnerHadamardPF_of_garloffWagner_nonnegPrec
    (hGW : garloffWagnerHadamardNonnegPrecStatement) :
    schurPolyaWagnerHadamardPFStatement :=
  schurPolyaWagnerHadamardPF_of_garloffWagner_prec0
    (garloffWagnerHadamardPFPrec0_of_nonnegPrec hGW)

/-- The two-pair Garloff--Wagner theorem implies the one-polynomial
real-rootedness/PF Hadamard theorem by applying it to self-pairs. -/
theorem garloffWagnerHadamardNonnegRealRooted_of_nonnegPrec
    (hGW : garloffWagnerHadamardNonnegPrecStatement) :
    garloffWagnerHadamardNonnegRealRootedStatement := by
  intro p q hpnn hqnn hprr hqrr
  have hp : IsPFPolynomial p := IsPFPolynomial.of_realRooted_nonneg hpnn hprr.2
  have hq : IsPFPolynomial q := IsPFPolynomial.of_realRooted_nonneg hqnn hqrr.2
  have hpf : IsPFPolynomial (hadamardProduct p q) :=
    hadamardProduct_preserves_pf_of_nonnegPrec hGW hp hq
  exact ⟨hpf.eq_zero_or_splits, hpf.hasNonnegCoeffs, hpf.roots_nonpos⟩

/-- Fixed-right Hadamard multiplication preserves zero-aware proper position
inside the PF cone. -/
theorem hadamardProduct_preserves_prec0_right
    (hGW : garloffWagnerHadamardPFPrec0Statement)
    {f g p : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hp : IsPFPolynomial p)
    (hfg : Prec0 f g) :
    Prec0 (hadamardProduct f p) (hadamardProduct g p) :=
  hGW hf hg hp hp hfg hp.prec0_self

/-- Fixed-left Hadamard multiplication preserves zero-aware proper position
inside the PF cone. -/
theorem hadamardProduct_preserves_prec0_left
    (hGW : garloffWagnerHadamardPFPrec0Statement)
    {f p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Prec0 p q) :
    Prec0 (hadamardProduct f p) (hadamardProduct f q) := by
  simpa [hadamardProduct_comm] using
    hadamardProduct_preserves_prec0_right hGW hp hq hf hpq

theorem reciprocalShift_hadamardProduct (D : ℕ) (p q : ℝ[X]) :
    reciprocalShift D (hadamardProduct p q) =
      hadamardProduct (reciprocalShift D p) (reciprocalShift D q) := by
  ext n
  simp

/-- Hadamard closure for the reciprocal-interlacing cone. -/
def hadamardReciprocalConeClosureStatement : Prop :=
  ∀ {D : ℕ} {p q : ℝ[X]},
    IsPFPolynomial p →
    IsPFPolynomial q →
    Prec p (reciprocalShift D p) →
    Prec q (reciprocalShift D q) →
    Prec0 (hadamardProduct p q)
      (reciprocalShift D (hadamardProduct p q))

/-- Hadamard closure for the reciprocal-interlacing cone, obtained from the
zero-aware PF two-pair Garloff--Wagner wrapper. -/
theorem hadamardReciprocalConeClosure_of_garloffWagner_prec0
    (hGW : garloffWagnerHadamardPFPrec0Statement) :
    hadamardReciprocalConeClosureStatement := by
  intro D p q hp hq hprec_p hprec_q
  have hp_shift : IsPFPolynomial (reciprocalShift D p) :=
    IsPFPolynomial.of_realRooted_nonneg hp.hasNonnegCoeffs.reciprocalShift hprec_p.2.1.2
  have hq_shift : IsPFPolynomial (reciprocalShift D q) :=
    IsPFPolynomial.of_realRooted_nonneg hq.hasNonnegCoeffs.reciprocalShift hprec_q.2.1.2
  simpa [reciprocalShift_hadamardProduct] using
    hGW hp hp_shift hq hq_shift hprec_p.toPrec0 hprec_q.toPrec0

/-- Hadamard closure for the reciprocal-interlacing cone, obtained from the
nonnegative two-pair Garloff--Wagner theorem. -/
theorem hadamardReciprocalConeClosure_of_garloffWagner
    (hGW : garloffWagnerHadamardNonnegPrecStatement) :
    hadamardReciprocalConeClosureStatement :=
  hadamardReciprocalConeClosure_of_garloffWagner_prec0
    (garloffWagnerHadamardPFPrec0_of_nonnegPrec hGW)

theorem hadamardReciprocalConeClosure_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    hadamardReciprocalConeClosureStatement :=
  hadamardReciprocalConeClosure_of_garloffWagner_prec0
    (garloffWagnerHadamardPFPrec0_of_matrixHadamardBridges
      hToFull hMatHad hFullToPrec0)

theorem hadamardReciprocalConeClosure_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hSchur : HurwitzMatrixSchurProductTNStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    hadamardReciprocalConeClosureStatement :=
  hadamardReciprocalConeClosure_of_garloffWagner_prec0
    (garloffWagnerHadamardPFPrec0_of_hurwitzSchur
      hToFull hSchur hFullToPrec0)

theorem hadamardReciprocalConeClosure_of_matrixClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    hadamardReciprocalConeClosureStatement :=
  hadamardReciprocalConeClosure_of_garloffWagner_prec0
    (garloffWagnerHadamardPFPrec0_of_matrixClassicalInputs
      hRoute hMatHad hASW hInt)

theorem hadamardReciprocalConeClosure_of_hurwitzSchurClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hSchur : HurwitzMatrixSchurProductTNStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    hadamardReciprocalConeClosureStatement :=
  hadamardReciprocalConeClosure_of_garloffWagner_prec0
    (garloffWagnerHadamardPFPrec0_of_hurwitzSchurClassicalInputs
      hRoute hSchur hASW hInt)

/-- Polynomial-coefficient form of Polya-frequency closure under termwise
products. This is finite-sequence closure packaged through coefficient
polynomials. -/
def polyaFrequencyHadamardCoeffStatement : Prop :=
  ∀ {p q : ℝ[X]},
    IsPolyaFreqSeq (fun n => p.coeff n) →
    IsPolyaFreqSeq (fun n => q.coeff n) →
    IsPolyaFreqSeq (fun n => (hadamardProduct p q).coeff n)

theorem polyaFrequencyHadamardCoeff_of_schurPolyaWagner
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hSPW : schurPolyaWagnerHadamardPFStatement) :
    polyaFrequencyHadamardCoeffStatement :=
  fun {_ _} hp hq =>
    (hSPW (IsPFPolynomial.of_sequence hASW hp)
      (IsPFPolynomial.of_sequence hASW hq)).to_sequence

theorem polyaFrequencyHadamardCoeff_of_garloffWagner_nonneg
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hGW : garloffWagnerHadamardNonnegRealRootedStatement) :
    polyaFrequencyHadamardCoeffStatement :=
  polyaFrequencyHadamardCoeff_of_schurPolyaWagner hASW
    (schurPolyaWagnerHadamardPF_of_garloffWagner_nonneg hGW)

theorem polyaFrequencyHadamardCoeff_of_garloffWagner_nonnegPrec
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hGW : garloffWagnerHadamardNonnegPrecStatement) :
    polyaFrequencyHadamardCoeffStatement :=
  polyaFrequencyHadamardCoeff_of_schurPolyaWagner hASW
    (schurPolyaWagnerHadamardPF_of_garloffWagner_nonnegPrec hGW)

theorem polyaFrequencyHadamardCoeff_of_matrixHadamardBridges
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    polyaFrequencyHadamardCoeffStatement :=
  polyaFrequencyHadamardCoeff_of_schurPolyaWagner hASW
    (schurPolyaWagnerHadamardPF_of_matrixHadamardBridges
      hToFull hMatHad hFullToPrec0)

theorem polyaFrequencyHadamardCoeff_of_hurwitzSchur
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hSchur : HurwitzMatrixSchurProductTNStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    polyaFrequencyHadamardCoeffStatement :=
  polyaFrequencyHadamardCoeff_of_schurPolyaWagner hASW
    (schurPolyaWagnerHadamardPF_of_hurwitzSchur
      hToFull hSchur hFullToPrec0)

theorem polyaFrequencyHadamardCoeff_of_matrixClassicalInputs
    (hASW0 : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    polyaFrequencyHadamardCoeffStatement :=
  polyaFrequencyHadamardCoeff_of_schurPolyaWagner hASW0
    (schurPolyaWagnerHadamardPF_of_matrixClassicalInputs
      hRoute hMatHad hASW hInt)

theorem polyaFrequencyHadamardCoeff_of_hurwitzSchurClassicalInputs
    (hASW0 : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hSchur : HurwitzMatrixSchurProductTNStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    polyaFrequencyHadamardCoeffStatement :=
  polyaFrequencyHadamardCoeff_of_schurPolyaWagner hASW0
    (schurPolyaWagnerHadamardPF_of_hurwitzSchurClassicalInputs
      hRoute hSchur hASW hInt)

end RealRooted
