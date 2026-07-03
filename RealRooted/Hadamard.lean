import RealRooted.PFPolynomial
import RealRooted.MultiplierSequence
import RealRooted.VeroneseSection
import RealRooted.HurwitzMatrix

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
