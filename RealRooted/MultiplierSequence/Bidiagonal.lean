import RealRooted.MultiplierSequence

/-!
# Coefficient-bidiagonal polynomial operators

This module contains the elementary coefficient-bidiagonal operator shared by
finite-symbol and Pólya-frequency arguments.  It is independent of tactic
elaboration and of any particular real-rootedness preserver criterion.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Coefficient-bidiagonal operator.

`bidiagonalOperator alpha beta` sends a coefficient vector `(a_k)` to
`(alpha_k a_k + beta_{k-1} a_{k-1})`, with the second term omitted at `k = 0`.
Equivalently, it is `diagonalOperator alpha p + X * diagonalOperator beta p`.
-/
def bidiagonalOperator (alpha beta : ℕ → ℝ) (p : ℝ[X]) : ℝ[X] :=
  diagonalOperator alpha p + X * diagonalOperator beta p

@[simp] theorem bidiagonalOperator_zero (alpha beta : ℕ → ℝ) :
    bidiagonalOperator alpha beta 0 = 0 := by
  simp [bidiagonalOperator]

@[simp] theorem coeff_bidiagonalOperator_zero
    (alpha beta : ℕ → ℝ) (p : ℝ[X]) :
    (bidiagonalOperator alpha beta p).coeff 0 = alpha 0 * p.coeff 0 := by
  simp [bidiagonalOperator]

@[simp] theorem coeff_bidiagonalOperator_succ
    (alpha beta : ℕ → ℝ) (p : ℝ[X]) (n : ℕ) :
    (bidiagonalOperator alpha beta p).coeff (n + 1) =
      alpha (n + 1) * p.coeff (n + 1) + beta n * p.coeff n := by
  simp [bidiagonalOperator]

/-- The bidiagonal operator raises degree by at most one. -/
theorem natDegree_bidiagonalOperator_le
    (alpha beta : ℕ → ℝ) (p : ℝ[X]) :
    (bidiagonalOperator alpha beta p).natDegree ≤ p.natDegree + 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  cases n with
  | zero =>
      lia
  | succ n =>
      have hpn1 : p.coeff (n + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
      have hpn : p.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
      simp [hpn1, hpn]

/-- Nonnegative bidiagonal entries preserve coefficient nonnegativity. -/
theorem HasNonnegCoeffs.bidiagonalOperator
    {alpha beta : ℕ → ℝ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p)
    (halpha : ∀ n : ℕ, 0 ≤ alpha n)
    (hbeta : ∀ n : ℕ, 0 ≤ beta n) :
    HasNonnegCoeffs (RealRooted.bidiagonalOperator alpha beta p) := by
  intro n
  cases n with
  | zero =>
      simpa using mul_nonneg (halpha 0) (hp 0)
  | succ n =>
      simpa using add_nonneg
        (mul_nonneg (halpha (n + 1)) (hp (n + 1)))
        (mul_nonneg (hbeta n) (hp n))

/-- Degree-local nonnegative bidiagonal entries preserve coefficient
nonnegativity on inputs of degree at most `d`. -/
theorem HasNonnegCoeffs.bidiagonalOperator_of_degree_le
    {alpha beta : ℕ → ℝ} {p : ℝ[X]} {d : ℕ}
    (hp : HasNonnegCoeffs p) (hdeg : p.natDegree ≤ d)
    (halpha : ∀ k, k ≤ d → 0 ≤ alpha k)
    (hbeta : ∀ k, k ≤ d → 0 ≤ beta k) :
    HasNonnegCoeffs (RealRooted.bidiagonalOperator alpha beta p) := by
  intro k
  cases k with
  | zero =>
      simpa using mul_nonneg (halpha 0 (Nat.zero_le d)) (hp 0)
  | succ k =>
      rw [coeff_bidiagonalOperator_succ]
      by_cases hk : k ≤ d
      · by_cases hks : k + 1 ≤ d
        · exact add_nonneg
            (mul_nonneg (halpha (k + 1) hks) (hp (k + 1)))
            (mul_nonneg (hbeta k hk) (hp k))
        · have hcoeff : p.coeff (k + 1) = 0 :=
            coeff_eq_zero_of_natDegree_lt (by lia)
          rw [hcoeff, mul_zero, zero_add]
          exact mul_nonneg (hbeta k hk) (hp k)
      · have hcoeff : p.coeff k = 0 :=
          coeff_eq_zero_of_natDegree_lt (by lia)
        have hcoeff_succ : p.coeff (k + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by lia)
        simp [hcoeff, hcoeff_succ]

/-- Degree-bounded PF-preserver interface for a coefficient-bidiagonal
operator. -/
def BidiagonalPFPreserver (alpha beta : ℕ → ℝ) (d : ℕ) : Prop :=
  ∀ {p : ℝ[X]},
    IsPFPolynomial p →
    p.natDegree ≤ d →
    IsPFPolynomial (bidiagonalOperator alpha beta p)

/-- Replace a coefficient sequence by zero above degree `d`. -/
def degreeTruncate (d : ℕ) (gamma : ℕ → ℝ) : ℕ → ℝ :=
  fun k => if k ≤ d then gamma k else 0

theorem degreeTruncate_eq_of_le (d : ℕ) (gamma : ℕ → ℝ) {k : ℕ}
    (hk : k ≤ d) :
    degreeTruncate d gamma k = gamma k := by
  simp [degreeTruncate, hk]

theorem degreeTruncate_nonneg {d : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, k ≤ d → 0 ≤ gamma k) :
    ∀ k, 0 ≤ degreeTruncate d gamma k := by
  intro k
  by_cases hk : k ≤ d
  · rw [degreeTruncate_eq_of_le d gamma hk]
    exact hgamma k hk
  · simp [degreeTruncate, hk]

theorem diagonalOperator_congr_of_eq_on_degree
    {gamma delta : ℕ → ℝ} {p : ℝ[X]} {d : ℕ}
    (hgamma : ∀ k, k ≤ d → gamma k = delta k)
    (hp : p.natDegree ≤ d) :
    diagonalOperator gamma p = diagonalOperator delta p := by
  ext k
  rw [coeff_diagonalOperator, coeff_diagonalOperator]
  by_cases hk : k ≤ d
  · rw [hgamma k hk]
  · have hdk : d < k := Nat.lt_of_not_ge hk
    have hklt : p.natDegree < k := lt_of_le_of_lt hp hdk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hklt]
    ring

theorem bidiagonalOperator_congr_of_eq_on_degree
    {alpha beta alpha' beta' : ℕ → ℝ} {p : ℝ[X]} {d : ℕ}
    (halpha : ∀ k, k ≤ d → alpha k = alpha' k)
    (hbeta : ∀ k, k ≤ d → beta k = beta' k)
    (hp : p.natDegree ≤ d) :
    bidiagonalOperator alpha beta p = bidiagonalOperator alpha' beta' p := by
  unfold bidiagonalOperator
  rw [diagonalOperator_congr_of_eq_on_degree halpha hp]
  rw [diagonalOperator_congr_of_eq_on_degree hbeta hp]

theorem BidiagonalPFPreserver.of_eq_on_degree
    {alpha beta alpha' beta' : ℕ → ℝ} {d : ℕ}
    (hpres : BidiagonalPFPreserver alpha' beta' d)
    (halpha : ∀ k, k ≤ d → alpha k = alpha' k)
    (hbeta : ∀ k, k ≤ d → beta k = beta' k) :
    BidiagonalPFPreserver alpha beta d := by
  intro p hp hdeg
  rw [bidiagonalOperator_congr_of_eq_on_degree halpha hbeta hdeg]
  exact hpres hp hdeg

end RealRooted
