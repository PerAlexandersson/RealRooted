module

public import RealRooted.Bezoutian.MatrixBasics
public import RealRooted.PFPolynomial
import RealRooted.SimpleRoots
import RealRooted.Mathlib.LinearAlgebra.Matrix.PosSemidefPencil

/-!
# Finite LMI certificates for a fixed Bezout ray

Bilinearity gives the exact padded quadratic matrix identity, with no degree or nonzero
gates. The finite LMI then characterizes positive semidefiniteness along the whole ray.
The interlacing consumer keeps coordinate PF, degree bounds and the padded weak-Bezout
bridge explicit. That bridge is the separate, still unproved task RealRooted #1936;
this module does not assume interlacing of the output ray.

Source: unpublished manuscript, `full-operator-block-common-input-reduction.md`,
formulas (5c)–(5f); RealRooted #1781 and #1991.
-/

public section

open Polynomial Matrix

namespace RealRooted

/-- Homogeneous mixing of two polynomial pairs gives the homogeneous quadratic Bezout
pencil. The two weights may both vanish, so no projective denominator is required. -/
theorem bezoutMatrix.homogeneous_eq_quadratic
    (n : ℕ) (a b c d : ℝ[X]) (u v : ℝ) :
    bezoutMatrix n (C u * c + C v * d) (C u * a + C v * b) =
      u ^ 2 • bezoutMatrix n c a + (u * v) • (bezoutMatrix n c b + bezoutMatrix n d a) +
        v ^ 2 • bezoutMatrix n d b := by
  ext i j
  simp only [bezoutMatrix, Polynomial.bezoutMatrix, Polynomial.bezoutEntry,
    bezoutSeqEntry, coeff_add, coeff_C_mul, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The Bezout matrix of two affine polynomial rays is a quadratic matrix pencil.
The matrix size is arbitrary, allowing padding, constants, zero polynomials and degree drops. -/
theorem bezoutMatrix.affine_eq_quadratic (n : ℕ) (a b c d : ℝ[X]) (t : ℝ) :
    bezoutMatrix n (c + C t * d) (a + C t * b) =
      bezoutMatrix n c a + t • (bezoutMatrix n c b + bezoutMatrix n d a) +
        t ^ 2 • bezoutMatrix n d b := by
  simpa only [C_1, one_mul, one_pow, one_smul] using
    bezoutMatrix.homogeneous_eq_quadratic n a b c d 1 t

/-- Scalar-board mixing of a fixed ray has exactly the homogeneous coefficient action
used by `Matrix.posSemidef_quadratic_pencil_transport`. This identity has no positivity,
degree, determinant or denominator gates. -/
theorem bezoutMatrix.board_affine_eq_quadratic (n : ℕ) (a b c d : ℝ[X])
    (α β γ δ t : ℝ) :
    bezoutMatrix n
      ((C δ * c + C β * d) + C t * (C γ * c + C α * d))
      ((C δ * a + C β * b) + C t * (C γ * a + C α * b)) =
      (δ ^ 2 • bezoutMatrix n c a +
        (β * δ) • (bezoutMatrix n c b + bezoutMatrix n d a) +
        β ^ 2 • bezoutMatrix n d b) +
      t • ((2 * γ * δ) • bezoutMatrix n c a +
        (α * δ + β * γ) • (bezoutMatrix n c b + bezoutMatrix n d a) +
        (2 * α * β) • bezoutMatrix n d b) +
      t ^ 2 • (γ ^ 2 • bezoutMatrix n c a +
        (α * γ) • (bezoutMatrix n c b + bezoutMatrix n d a) +
        α ^ 2 • bezoutMatrix n d b) := by
  have heq (p q : ℝ[X]) :
      (C δ * p + C β * q) + C t * (C γ * p + C α * q) =
        C (δ + γ * t) * p + C (β + α * t) * q := by
    simp only [C_add, C_mul]
    ring
  rw [heq c d, heq a b, bezoutMatrix.homogeneous_eq_quadratic]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Exact finite Gram LMI for the entire fixed padded Bezout ray. This statement concerns
matrix positivity only; coordinate PF and leading orientation are separate obligations. -/
theorem bezoutMatrix.posSemidef_affine_iff (n : ℕ) (a b c d : ℝ[X]) :
    (∀ t : ℝ, 0 ≤ t → (bezoutMatrix n (c + C t * d) (a + C t * b)).PosSemidef) ↔
      ∃ S Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧
        (fromBlocks (bezoutMatrix n c a) S Sᵀ (bezoutMatrix n d b)).PosSemidef ∧
        bezoutMatrix n c b + bezoutMatrix n d a = S + Sᵀ + Z := by
  simp_rw [bezoutMatrix.affine_eq_quadratic]
  exact posSemidef_quadratic_pencil_iff _ _ _
    (bezoutMatrix.isHermitian n c a)
    ((bezoutMatrix.isHermitian n c b).add (bezoutMatrix.isHermitian n d a))
    (bezoutMatrix.isHermitian n d b)

/-- Under the coordinate PF and padded weak-Bezout gates, the LMI certifies exactly the
ordered fixed ray. The explicit bridge is the general theorem tracked in #1936, whose
formalization is independent of the quadratic matrix certificate (#1991). -/
theorem interl_affine_iff_exists_posSemidef_fromBlocks
    (n : ℕ) (a b c d : ℝ[X])
    (hPF : ∀ t : ℝ, 0 ≤ t → IsPFPolynomial (a + C t * b) ∧ IsPFPolynomial (c + C t * d))
    (hdeg : ∀ t : ℝ, 0 ≤ t → (a + C t * b).natDegree ≤ n ∧ (c + C t * d).natDegree ≤ n)
    (hbez : ∀ f g : ℝ[X], IsPFPolynomial f → IsPFPolynomial g →
      f.natDegree ≤ n → g.natDegree ≤ n →
      (Interl f g ↔ (bezoutMatrix n g f).PosSemidef)) :
    (∀ t : ℝ, 0 ≤ t → Interl (a + C t * b) (c + C t * d)) ↔
      ∃ S Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧
        (fromBlocks (bezoutMatrix n c a) S Sᵀ (bezoutMatrix n d b)).PosSemidef ∧
        bezoutMatrix n c b + bezoutMatrix n d a = S + Sᵀ + Z := by
  rw [← bezoutMatrix.posSemidef_affine_iff]
  exact forall_congr' fun t => forall_congr' fun ht =>
    hbez _ _ (hPF t ht).1 (hPF t ht).2 (hdeg t ht).1 (hdeg t ht).2

/-- Both coordinate polynomials of the repeated-cubic regression are PF, including
its zero-coordinate endpoint. -/
theorem isPFPolynomial_repeated_cubic (t : ℝ) (ht : 0 ≤ t) :
    IsPFPolynomial ((X + C 2) ^ 3 : ℝ[X]) ∧
      IsPFPolynomial (C t * (X + C 1) ^ 3 : ℝ[X]) := by
  refine ⟨(isPFPolynomial_X_add_C (by norm_num : (0 : ℝ) ≤ 2)).pow 3, ?_⟩
  rcases ht.eq_or_lt with ht | ht
  · rw [← ht, C_0, zero_mul]
    exact IsPFPolynomial.zero
  · exact ((isPFPolynomial_X_add_C (by norm_num : (0 : ℝ) ≤ 1)).pow 3).const_mul ht

/-- The separated triple roots in the repeated-cubic example do not interlace, at any
positive ray parameter. This uses multiplicities, not a test of sampled roots. -/
theorem not_interl_repeated_cubic (t : ℝ) (ht : 0 < t) :
    ¬ Interl ((X + C 2) ^ 3 : ℝ[X]) (C t * (X + C 1) ^ 3) := by
  intro h
  have hf : ((X + C 2) ^ 3 : ℝ[X]) ≠ 0 := pow_ne_zero _ (X_add_C_ne_zero 2)
  have hg : (C t * (X + C 1) ^ 3 : ℝ[X]) ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr ht.ne') (pow_ne_zero _ (X_add_C_ne_zero 1))
  have hno (r : ℝ) :
      ¬ (((X + C 2) ^ 3 : ℝ[X]).IsRoot r ∧ (C t * (X + C 1) ^ 3 : ℝ[X]).IsRoot r) := by
    rintro ⟨hrf, hrg⟩
    have hrf' : (r + 2) ^ 3 = 0 := by
      simpa only [IsRoot.def, eval_pow, eval_add, eval_X, eval_C] using hrf
    have hrg' : t * (r + 1) ^ 3 = 0 := by
      simpa only [IsRoot.def, eval_mul, eval_C, eval_pow, eval_add, eval_X] using hrg
    have hr₂ := eq_zero_of_pow_eq_zero hrf'
    have hr₁ := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hrg').resolve_left ht.ne')
    linarith
  have hs := ((h.toStrictInterl_of_ne hf hg).hasSimpleRoots_of_no_common_root hno).1
  have hroot : ((X + C 2) ^ 3 : ℝ[X]).IsRoot (-2) := by
    norm_num [IsRoot.def]
  have hd := hs.eval_derivative_ne_zero hroot
  norm_num [derivative_pow] at hd

/-- The diagonal Wronskian of the repeated-cubic regression is everywhere nonnegative.
This does not replace the full matrix certificate. -/
theorem repeated_cubic_wronskian_nonneg (t x : ℝ) (ht : 0 ≤ t) :
    0 ≤ ((C t * (X + C 1) ^ 3 : ℝ[X]).derivative.eval x) *
        (((X + C 2) ^ 3 : ℝ[X]).eval x) -
      ((C t * (X + C 1) ^ 3 : ℝ[X]).eval x) *
        (((X + C 2) ^ 3 : ℝ[X]).derivative.eval x) := by
  have heq : ((C t * (X + C 1) ^ 3 : ℝ[X]).derivative.eval x) *
        (((X + C 2) ^ 3 : ℝ[X]).eval x) -
      ((C t * (X + C 1) ^ 3 : ℝ[X]).eval x) *
        (((X + C 2) ^ 3 : ℝ[X]).derivative.eval x) =
      3 * t * (x + 2) ^ 2 * (x + 1) ^ 2 := by
    norm_num [derivative_mul, derivative_pow, eval_mul, eval_pow]
    ring
  rw [heq]
  positivity

/-- The repeated-cubic ray has a negative Bezout quadratic form at `(3,-2,0)` for every
positive scale, although its diagonal Wronskian is nonnegative everywhere. -/
theorem not_posSemidef_bezoutMatrix_repeated_cubic (t : ℝ) (ht : 0 < t) :
    ¬ (bezoutMatrix 3 (C t * (X + C 1) ^ 3) ((X + C 2) ^ 3)).PosSemidef := by
  intro h
  have hv := h.dotProduct_mulVec_nonneg ![3, -2, 0]
  norm_num [bezoutMatrix, Polynomial.bezoutMatrix, Polynomial.bezoutEntry,
    bezoutSeqEntry, coeff_C_mul, coeff_X_add_C_pow, coeff_X_add_one_pow,
    Finset.sum_range_succ, Fin.sum_univ_succ,
    dotProduct, mulVec] at hv
  linarith

end RealRooted
