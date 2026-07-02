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
  ext n
  simp [add_mul]

theorem hadamardProduct_add_right (p q r : ℝ[X]) :
    hadamardProduct p (q + r) =
      hadamardProduct p q + hadamardProduct p r := by
  rw [hadamardProduct_comm p (q + r), hadamardProduct_add_left,
    hadamardProduct_comm q p, hadamardProduct_comm r p]

theorem hadamardProduct_C_mul_left (a : ℝ) (p q : ℝ[X]) :
    hadamardProduct (C a * p) q =
      C a * hadamardProduct p q := by
  ext n
  simp [mul_assoc]

theorem hadamardProduct_C_mul_right (a : ℝ) (p q : ℝ[X]) :
    hadamardProduct p (C a * q) =
      C a * hadamardProduct p q := by
  rw [hadamardProduct_comm p (C a * q), hadamardProduct_C_mul_left,
    hadamardProduct_comm q p]

/-- The support of a Hadamard product is contained in the left support. -/
theorem support_hadamardProduct_subset_left (p q : ℝ[X]) :
    (hadamardProduct p q).support ⊆ p.support := by
  intro n hn
  rw [mem_support_iff] at hn ⊢
  rw [coeff_hadamardProduct] at hn
  exact left_ne_zero_of_mul hn

/-- The support of a Hadamard product is contained in the right support. -/
theorem support_hadamardProduct_subset_right (p q : ℝ[X]) :
    (hadamardProduct p q).support ⊆ q.support := by
  rw [hadamardProduct_comm]
  exact support_hadamardProduct_subset_left q p

theorem natDegree_hadamardProduct_le_left (p q : ℝ[X]) :
    (hadamardProduct p q).natDegree ≤ p.natDegree := by
  refine natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  rw [coeff_hadamardProduct, coeff_eq_zero_of_natDegree_lt hn, zero_mul]

theorem natDegree_hadamardProduct_le_right (p q : ℝ[X]) :
    (hadamardProduct p q).natDegree ≤ q.natDegree := by
  rw [hadamardProduct_comm]
  exact natDegree_hadamardProduct_le_left q p

/-- A Hadamard product vanishes exactly when the two coefficient supports are
disjoint. -/
theorem hadamardProduct_eq_zero_iff_support_disjoint (p q : ℝ[X]) :
    hadamardProduct p q = 0 ↔ Disjoint p.support q.support := by
  constructor
  · intro h
    rw [Finset.disjoint_left]
    intro n hnp hnq
    have hzero : (hadamardProduct p q).coeff n = 0 := by simp [h]
    rw [coeff_hadamardProduct] at hzero
    rw [mem_support_iff] at hnp hnq
    exact (mul_ne_zero hnp hnq) hzero
  · intro hdisj
    ext n
    by_cases hnp : n ∈ p.support
    · have hnq : n ∉ q.support := Finset.disjoint_left.mp hdisj hnp
      simp [coeff_hadamardProduct, (notMem_support_iff).mp hnq]
    · simp [coeff_hadamardProduct, (notMem_support_iff).mp hnp]

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
    (schurSzegoComp n f g).natDegree ≤ n := by
  refine natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro k hk
  exact coeff_schurSzegoComp_eq_zero_of_lt hk f g

theorem choose_mul_coeff_schurSzegoComp_of_le {n k : Nat} (hk : k ≤ n) (f g : ℝ[X]) :
    (Nat.choose n k : ℝ) * (schurSzegoComp n f g).coeff k =
      f.coeff k * g.coeff k := by
  rw [coeff_schurSzegoComp_of_le hk]
  field_simp [show (Nat.choose n k : ℝ) ≠ 0 by exact_mod_cast Nat.choose_ne_zero hk]

theorem choose_mul_coeff_schurSzegoComp_eq_coeff_hadamardProduct_of_le
    {n k : Nat} (hk : k ≤ n) (f g : ℝ[X]) :
    (Nat.choose n k : ℝ) * (schurSzegoComp n f g).coeff k =
      (hadamardProduct f g).coeff k := by
  rw [choose_mul_coeff_schurSzegoComp_of_le hk, coeff_hadamardProduct]

theorem schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_left_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hf : f.natDegree ≤ n) :
    schurSzegoComp n f g = 0 ↔ hadamardProduct f g = 0 := by
  constructor
  · intro h
    ext k
    by_cases hk : k ≤ n
    · rw [← choose_mul_coeff_schurSzegoComp_eq_coeff_hadamardProduct_of_le hk,
        h, coeff_zero, mul_zero]
    · have hk_lt : n < k := Nat.lt_of_not_le hk
      have hf_coeff : f.coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hf hk_lt)
      simp [coeff_hadamardProduct, hf_coeff]
  · intro h
    ext k
    by_cases hk : k ≤ n
    · have hcoeff : f.coeff k * g.coeff k = 0 := by
        simpa [coeff_hadamardProduct] using congrArg (fun p : ℝ[X] => p.coeff k) h
      rw [coeff_schurSzegoComp_of_le hk, hcoeff, zero_div, coeff_zero]
    · simp [coeff_schurSzegoComp, hk]

theorem schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_right_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hg : g.natDegree ≤ n) :
    schurSzegoComp n f g = 0 ↔ hadamardProduct f g = 0 := by
  rw [schurSzegoComp_comm, hadamardProduct_comm]
  exact schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_left_natDegree_le hg

theorem schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le
    {n : Nat} {gamma : ℕ → ℝ} {p : ℝ[X]} (hp : p.natDegree ≤ n) :
    schurSzegoComp n (jensenPolynomial n gamma) p = diagonalOperator gamma p := by
  ext k
  by_cases hk : k ≤ n
  · have hchoose : (Nat.choose n k : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hk
    rw [coeff_schurSzegoComp_of_le hk, coeff_jensenPolynomial, coeff_diagonalOperator]
    simp only [hk, if_true]
    field_simp [hchoose]
  · have hk_lt : n < k := Nat.lt_of_not_le hk
    have hp_coeff : p.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hk_lt)
    rw [coeff_schurSzegoComp, if_neg hk, coeff_diagonalOperator, hp_coeff, mul_zero]

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
  ext k
  by_cases hk : k ≤ n
  · simp only [coeff_schurSzegoComp_of_le hk, coeff_add, add_mul, add_div]
  · simp [coeff_schurSzegoComp_eq_zero_of_lt (Nat.lt_of_not_le hk)]

/-- Schur--Szego composition is additive in its right argument. -/
theorem schurSzegoComp_add_right (n : Nat) (f g g' : ℝ[X]) :
    schurSzegoComp n f (g + g') =
      schurSzegoComp n f g + schurSzegoComp n f g' := by
  rw [schurSzegoComp_comm, schurSzegoComp_add_left, schurSzegoComp_comm n g f,
    schurSzegoComp_comm n g' f]

/-- Scalars pull out of the left argument of a Schur--Szego composition. -/
theorem schurSzegoComp_C_mul_left (n : Nat) (a : ℝ) (f g : ℝ[X]) :
    schurSzegoComp n (C a * f) g = C a * schurSzegoComp n f g := by
  ext k
  by_cases hk : k ≤ n
  · rw [coeff_schurSzegoComp_of_le hk, coeff_C_mul, coeff_C_mul,
      coeff_schurSzegoComp_of_le hk, mul_assoc, mul_div_assoc]
  · simp [coeff_schurSzegoComp_eq_zero_of_lt (Nat.lt_of_not_le hk)]

/-- Scalars pull out of the right argument of a Schur--Szego composition. -/
theorem schurSzegoComp_C_mul_right (n : Nat) (a : ℝ) (f g : ℝ[X]) :
    schurSzegoComp n f (C a * g) = C a * schurSzegoComp n f g := by
  rw [schurSzegoComp_comm, schurSzegoComp_C_mul_left, schurSzegoComp_comm n g f]

/-- The support of a Schur--Szego composition is contained in the left
support. -/
theorem support_schurSzegoComp_subset_left (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).support ⊆ f.support := by
  intro k hk
  rw [mem_support_iff, coeff_schurSzegoComp] at hk
  rw [mem_support_iff]
  intro hfk
  exact hk (by simp [hfk])

/-- The support of a Schur--Szego composition is contained in the right
support. -/
theorem support_schurSzegoComp_subset_right (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).support ⊆ g.support := by
  rw [schurSzegoComp_comm]
  exact support_schurSzegoComp_subset_left n g f

/-- Nonnegative coefficients are preserved by fixed-degree Schur--Szego
composition. -/
theorem HasNonnegCoeffs.schurSzegoComp {n : Nat} {f g : ℝ[X]}
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g) :
    HasNonnegCoeffs (schurSzegoComp n f g) := by
  intro k
  rw [coeff_schurSzegoComp]
  split
  · exact div_nonneg (mul_nonneg (hf k) (hg k)) (by positivity)
  · exact le_refl 0

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

/-- Finite Schur--Szegő composition theorem. The degenerate cases (`f = 0` or
`p = 0`, where the composition vanishes) are discharged; the remaining
obligation is the substantive case of a nonzero PF polynomial `f` composed with
a nonzero real-rooted polynomial `p`. -/
theorem finiteSchurSzegoComposition : finiteSchurSzegoCompositionStatement := by
  intro n f p hf hfdeg hp hsplit
  by_cases hf0 : f = 0
  · exact Or.inl (by rw [hf0]; exact schurSzegoComp_zero_left n p)
  by_cases hp0 : p = 0
  · exact Or.inl (by rw [hp0]; exact schurSzegoComp_zero_right n f)
  -- Substantive case: `f ≠ 0` PF (real, nonpositive zeros) and `p ≠ 0` with
  -- only real zeros. Then `schurSzegoComp n f p` has only real zeros.
  sorry

/-- The backward direction of the finite Pólya--Schur theorem, obtained from the
finite Schur--Szegő composition theorem. -/
theorem finitePolyaSchurNonnegBackward : finitePolyaSchurNonnegBackwardStatement :=
  finitePolyaSchurNonnegBackward_of_schurSzego finiteSchurSzegoComposition

/-- Classical finite Pólya--Schur theorem (nonnegative-coefficient convention).
The only remaining analytic obligation is isolated in
`finiteSchurSzegoComposition`. -/
theorem finitePolyaSchur_nonneg : finitePolyaSchurNonnegStatement :=
  finitePolyaSchur_nonneg_of_backward finitePolyaSchurNonnegBackward

/-- Nonnegative coefficients are preserved by coefficientwise Hadamard
products. -/
theorem HasNonnegCoeffs.hadamardProduct {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (hadamardProduct p q) := by
  intro n
  simpa using mul_nonneg (hp n) (hq n)

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
    hadamardPreservesHurwitzStableStatement := by
  intro a b ha hb
  obtain ⟨hann, harhp⟩ := ha
  obtain ⟨hbnn, hbrhp⟩ := hb
  exact ⟨hann.hadamardProduct hbnn, h hann hbnn harhp hbrhp⟩

/-- The analytic core is conversely implied by Garloff--Wagner Theorem 1, so the
two interfaces are equivalent: isolating the right-half-plane half loses no
content. -/
theorem hadamardPreservesRightHalfPlaneStable_of_hurwitzStable
    (h : hadamardPreservesHurwitzStableStatement) :
    hadamardPreservesRightHalfPlaneStableStatement := by
  intro a b hann hbnn harhp hbrhp
  exact (h ⟨hann, harhp⟩ ⟨hbnn, hbrhp⟩).2

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

theorem garloffWagnerHadamardPFPrec0_of_nonnegPrec
    (hGW : garloffWagnerHadamardNonnegPrecStatement) :
    garloffWagnerHadamardPFPrec0Statement := by
  intro f g p q hf hg hp hq hfg hpq
  rcases hfg with rfl | rfl | hfg'
  · simpa using prec0_zero_left (hadamardProduct g q)
  · simpa using prec0_zero_right (hadamardProduct f p)
  rcases hpq with rfl | rfl | hpq'
  · simpa using prec0_zero_left (hadamardProduct g q)
  · simpa using prec0_zero_right (hadamardProduct f p)
  exact hGW hf.hasNonnegCoeffs hg.hasNonnegCoeffs
    hp.hasNonnegCoeffs hq.hasNonnegCoeffs hfg' hpq'

/-- The two-pair Garloff--Wagner theorem implies the one-polynomial
real-rootedness/PF Hadamard theorem by applying it to self-pairs. -/
theorem garloffWagnerHadamardNonnegRealRooted_of_nonnegPrec
    (hGW : garloffWagnerHadamardNonnegPrecStatement) :
    garloffWagnerHadamardNonnegRealRootedStatement := by
  intro p q hpnn hqnn hprr hqrr
  have hpf : IsPFPolynomial (hadamardProduct p q) :=
    IsPFPolynomial.of_prec0_self (hpnn.hadamardProduct hqnn)
      (hGW hpnn hpnn hqnn hqnn (prec_refl hprr.1 hprr.2) (prec_refl hqrr.1 hqrr.2))
  exact ⟨hpf.eq_zero_or_splits, hpf.hasNonnegCoeffs, hpf.roots_nonpos⟩

theorem schurPolyaWagnerHadamardPF_of_garloffWagner_prec0
    (hGW : garloffWagnerHadamardPFPrec0Statement) :
    schurPolyaWagnerHadamardPFStatement := by
  intro p q hp hq
  exact IsPFPolynomial.of_prec0_self
    (hp.hasNonnegCoeffs.hadamardProduct hq.hasNonnegCoeffs)
    (hGW hp hp hq hq hp.prec0_self hq.prec0_self)

/-- PF-polynomial closure under Hadamard product, stated directly from the
zero-aware Garloff--Wagner PF wrapper. -/
theorem hadamardProduct_preserves_pf_of_garloffWagner
    (hGW : garloffWagnerHadamardPFPrec0Statement)
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) :=
  schurPolyaWagnerHadamardPF_of_garloffWagner_prec0 hGW hp hq

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
    Prec0 (hadamardProduct f p) (hadamardProduct f q) :=
  hGW hf hf hp hq hf.prec0_self hpq

theorem reciprocalShift_hadamardProduct (D : ℕ) (p q : ℝ[X]) :
    reciprocalShift D (hadamardProduct p q) =
      hadamardProduct (reciprocalShift D p) (reciprocalShift D q) := by
  ext n
  simp

/-- Hadamard closure for the reciprocal-interlacing cone, obtained from the
two-pair Garloff--Wagner theorem. -/
def hadamardReciprocalConeClosureStatement : Prop :=
  ∀ {D : ℕ} {p q : ℝ[X]},
    IsPFPolynomial p →
    IsPFPolynomial q →
    Prec p (reciprocalShift D p) →
    Prec q (reciprocalShift D q) →
    Prec0 (hadamardProduct p q)
      (reciprocalShift D (hadamardProduct p q))

theorem hadamardReciprocalConeClosure_of_garloffWagner
    (hGW : garloffWagnerHadamardNonnegPrecStatement) :
    hadamardReciprocalConeClosureStatement := by
  intro D p q hp hq hprec_p hprec_q
  simpa [reciprocalShift_hadamardProduct] using
    hGW hp.hasNonnegCoeffs hp.hasNonnegCoeffs.reciprocalShift
      hq.hasNonnegCoeffs hq.hasNonnegCoeffs.reciprocalShift hprec_p hprec_q

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

end RealRooted
