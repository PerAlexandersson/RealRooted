import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.ComputeDegree
import RealRooted.MultiplierSequence
import RealRooted.MultivariateStability
import RealRooted.Tactic.PFBidiagonal
import RealRooted.BorceaBranden.Applications.HomogenizeStable

/-!
# Finite-symbol PF-bidiagonal interface

This file records the finite Borcea-Branden symbol route for
coefficient-bidiagonal operators as a tactic-facing interface.

The deep analytic inputs are deliberately `Prop`-valued statements, not
axioms.  The proved declarations in this file only assemble those interfaces
with a residual factorization certificate.
-/

open Polynomial BigOperators

namespace RealRooted
namespace Tactic
namespace FiniteSymbolPF

noncomputable section

/-! ## Compatibility exports

The tactic namespace historically carried local copies of these declarations.
Keep its public surface while routing every implementation through the
canonical multiplier-sequence or tactic owner. -/

export RealRooted
  (bidiagonalOperator
    BidiagonalPFPreserver
    degreeTruncate
    degreeTruncate_eq_of_le
    degreeTruncate_nonneg
    diagonalOperator_congr_of_eq_on_degree
    bidiagonalOperator_congr_of_eq_on_degree
    BidiagonalPFPreserver.of_eq_on_degree
    bidiagonalJensenPencil
    quadraticJensenResidual
    quadraticBidiagonalResidual
    quadraticBidiagonalPencilResidual
    quadraticBidiagonalPencilResidual_one
    quadraticJensen_eq_jensenPolynomial
    quadraticJensen_eq_factor_residual
    quadraticBidiagonalJensenPencil_eq_factor_residual
    quadraticBidiagonalJensenPencil_eq_factor_residual_one
    isPFPolynomial_of_bidiagonalOperator_sequence
    isPFPolynomial_of_bidiagonalOperator_sequence_from)

/-! ## Second-derivative recurrence normalization -/

/-- The second-derivative recurrence shape used by the direct Family H rows. -/
def secondDerivativeBidiagonalForm
    (a0 a1 b1 b2 c2 : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C a0 * p + C a1 * (X * p) +
    C b1 * (X * p.derivative) +
      C b2 * (X * (X * p.derivative)) +
        C c2 * (X * (X * p.derivative.derivative))

/-- Diagonal coefficient induced by `secondDerivativeBidiagonalForm`. -/
def secondDerivativeAlpha (a0 b1 c2 : ℝ) (k : ℕ) : ℝ :=
  a0 + b1 * (k : ℝ) + c2 * (k : ℝ) * ((k : ℝ) - 1)

/-- Subdiagonal coefficient induced by `secondDerivativeBidiagonalForm`. -/
def secondDerivativeBeta (a1 b2 : ℝ) (k : ℕ) : ℝ :=
  a1 + b2 * (k : ℝ)

/-- Coefficient-level normalization of a second-derivative recurrence into a
coefficient-bidiagonal operator. -/
theorem secondDerivativeBidiagonalForm_eq_bidiagonalOperator
    (a0 a1 b1 b2 c2 : ℝ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm a0 a1 b1 b2 c2 p =
      bidiagonalOperator
        (secondDerivativeAlpha a0 b1 c2)
        (secondDerivativeBeta a1 b2) p := by
  ext m
  cases m with
  | zero =>
      simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
        secondDerivativeAlpha, secondDerivativeBeta]
  | succ m =>
      cases m with
      | zero =>
          simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
            secondDerivativeAlpha, secondDerivativeBeta, Polynomial.coeff_X_mul,
            Polynomial.coeff_derivative]
          ring_nf
      | succ m =>
          simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
            secondDerivativeAlpha, secondDerivativeBeta, Polynomial.coeff_X_mul,
            Polynomial.coeff_derivative]
          ring_nf

/-- The normalized internal second-derivative form agrees with the recurrence
shape generated in the OEIS files. -/
theorem secondDerivativeBidiagonalForm_eq_written
    (a0 a1 b1 b2 c2 : ℝ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm a0 a1 b1 b2 c2 p =
      (C a0 + C a1 * X) * p +
        (C b1 * X + C b2 * X ^ 2) * p.derivative +
          C c2 * X ^ 2 * p.derivative.derivative := by
  simp [secondDerivativeBidiagonalForm]
  ring

/-- Direct normalization from the OEIS-written second-derivative recurrence
shape to a coefficient-bidiagonal operator. -/
theorem writtenSecondDerivativeBidiagonalForm_eq_bidiagonalOperator
    (a0 a1 b1 b2 c2 : ℝ) (p : ℝ[X]) :
    (C a0 + C a1 * X) * p +
        (C b1 * X + C b2 * X ^ 2) * p.derivative +
          C c2 * X ^ 2 * p.derivative.derivative =
      bidiagonalOperator
        (secondDerivativeAlpha a0 b1 c2)
        (secondDerivativeBeta a1 b2) p := by
  rw [← secondDerivativeBidiagonalForm_eq_written]
  exact secondDerivativeBidiagonalForm_eq_bidiagonalOperator a0 a1 b1 b2 c2 p

/-! ## Shifted second-derivative recurrence normalization -/

/-- The shifted second-derivative recurrence shape where `p''` contributes to
the subdiagonal coefficient. -/
def shiftedSecondDerivativeBidiagonalForm
    (a0 a1 b1 b2 c3 : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C a0 * p + C a1 * (X * p) +
    C b1 * (X * p.derivative) +
      C b2 * (X * (X * p.derivative)) +
        C c3 * (X * (X * (X * p.derivative.derivative)))

/-- Diagonal coefficient induced by `shiftedSecondDerivativeBidiagonalForm`. -/
def shiftedSecondDerivativeAlpha (a0 b1 : ℝ) (k : ℕ) : ℝ :=
  a0 + b1 * (k : ℝ)

/-- Subdiagonal coefficient induced by `shiftedSecondDerivativeBidiagonalForm`. -/
def shiftedSecondDerivativeBeta (a1 b2 c3 : ℝ) (k : ℕ) : ℝ :=
  a1 + b2 * (k : ℝ) + c3 * (k : ℝ) * ((k : ℝ) - 1)

/-- Coefficient-level normalization of a shifted second-derivative recurrence
into a coefficient-bidiagonal operator. -/
theorem shiftedSecondDerivativeBidiagonalForm_eq_bidiagonalOperator
    (a0 a1 b1 b2 c3 : ℝ) (p : ℝ[X]) :
    shiftedSecondDerivativeBidiagonalForm a0 a1 b1 b2 c3 p =
      bidiagonalOperator
        (shiftedSecondDerivativeAlpha a0 b1)
        (shiftedSecondDerivativeBeta a1 b2 c3) p := by
  ext m
  cases m with
  | zero =>
      simp [shiftedSecondDerivativeBidiagonalForm, bidiagonalOperator,
        shiftedSecondDerivativeAlpha, shiftedSecondDerivativeBeta]
  | succ m =>
      cases m with
      | zero =>
          simp [shiftedSecondDerivativeBidiagonalForm, bidiagonalOperator,
            shiftedSecondDerivativeAlpha, shiftedSecondDerivativeBeta,
            Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
          ring_nf
      | succ m =>
          cases m with
          | zero =>
              simp [shiftedSecondDerivativeBidiagonalForm, bidiagonalOperator,
                shiftedSecondDerivativeAlpha, shiftedSecondDerivativeBeta,
                Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
              ring_nf
          | succ m =>
              simp [shiftedSecondDerivativeBidiagonalForm, bidiagonalOperator,
                shiftedSecondDerivativeAlpha, shiftedSecondDerivativeBeta,
                Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
              ring_nf

/-- The normalized shifted second-derivative form agrees with the recurrence
shape generated in the OEIS files. -/
theorem shiftedSecondDerivativeBidiagonalForm_eq_written
    (a0 a1 b1 b2 c3 : ℝ) (p : ℝ[X]) :
    shiftedSecondDerivativeBidiagonalForm a0 a1 b1 b2 c3 p =
      (C a0 + C a1 * X) * p +
        (C b1 * X + C b2 * X ^ 2) * p.derivative +
          C c3 * X ^ 3 * p.derivative.derivative := by
  simp [shiftedSecondDerivativeBidiagonalForm]
  ring

/-- Direct normalization from the OEIS-written shifted second-derivative
recurrence shape to a coefficient-bidiagonal operator. -/
theorem writtenShiftedSecondDerivativeBidiagonalForm_eq_bidiagonalOperator
    (a0 a1 b1 b2 c3 : ℝ) (p : ℝ[X]) :
    (C a0 + C a1 * X) * p +
        (C b1 * X + C b2 * X ^ 2) * p.derivative +
          C c3 * X ^ 3 * p.derivative.derivative =
      bidiagonalOperator
        (shiftedSecondDerivativeAlpha a0 b1)
        (shiftedSecondDerivativeBeta a1 b2 c3) p := by
  rw [← shiftedSecondDerivativeBidiagonalForm_eq_written]
  exact shiftedSecondDerivativeBidiagonalForm_eq_bidiagonalOperator a0 a1 b1 b2 c3 p

/-- The homogenized finite algebraic symbol for
`T(X^k) = alpha k X^k + beta k X^(k+1)`.

Variable `0` is `X`; variable `1` is `Y`.  The diagonal branch carries one
extra `Y`, so both branches have total degree `d + 1`.  Dehomogenizing at
`Y = 1` recovers the usual Jensen pencil. -/
def finiteSymbol (alpha beta : ℕ → ℝ) (d : ℕ) :
    MvPolynomial (Fin 2) ℝ :=
  ∑ k ∈ Finset.range (d + 1),
    MvPolynomial.C ((Nat.choose d k : ℝ)) *
      (MvPolynomial.C (alpha k) * (MvPolynomial.X 0) ^ k *
          MvPolynomial.X 1 +
        MvPolynomial.C (beta k) * (MvPolynomial.X 0) ^ (k + 1)) *
      (MvPolynomial.X 1) ^ (d - k)

theorem finiteSymbol_congr_of_eq_on_degree
    {alpha beta alpha' beta' : ℕ → ℝ} {d : ℕ}
    (halpha : ∀ k, k ≤ d → alpha k = alpha' k)
    (hbeta : ∀ k, k ≤ d → beta k = beta' k) :
    finiteSymbol alpha beta d = finiteSymbol alpha' beta' d := by
  unfold finiteSymbol
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [halpha k hk_le, hbeta k hk_le]



/-! ## Classical interfaces -/

/-- Bivariate stability is closed under multiplication by `(X+Y)^m`, kept as
a named interface. -/
theorem bivariateStableMulXAddYPow :
    ∀ (m : ℕ) {P : MvPolynomial (Fin 2) ℂ},
      IsBivariateUpperStable P →
      IsBivariateUpperStable
        (((MvPolynomial.X 0 + MvPolynomial.X 1) ^ m) * P) := by
  intro m P hP
  exact hP.mul_X_add_X_pow 0 1 m

/-! ## Residual certificates and assembly -/

/-- Residual certificate for the finite-symbol PF-bidiagonal route. -/
structure BidiagonalCubicResidualCertificate
    (alpha beta : ℕ → ℝ) (d : ℕ) where
  residual : ℝ[X]
  residual_cubic : residual.natDegree = 3
  symbol_factor :
    complexifyMv (finiteSymbol alpha beta d) =
      ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ (d - 2)) *
        complexifyMv (homogenizeBivariate residual.natDegree residual)
  residual_pf : IsPFPolynomial residual
  alpha_nonneg : ∀ n, 0 ≤ alpha n
  beta_nonneg : ∀ n, 0 ≤ beta n

/-- If the finite symbol factors through a stable residual, then the finite
symbol is stable. -/
theorem finiteSymbol_stable_of_residual_factor
    {alpha beta : ℕ → ℝ} {d : ℕ} {residual : ℝ[X]}
    (hfac : complexifyMv (finiteSymbol alpha beta d) =
      ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ (d - 2)) *
        complexifyMv (homogenizeBivariate residual.natDegree residual))
    (hres : IsBivariateUpperStable
      (complexifyMv (homogenizeBivariate residual.natDegree residual))) :
    IsBivariateUpperStable (complexifyMv (finiteSymbol alpha beta d)) := by
  rw [hfac]
  exact bivariateStableMulXAddYPow (d - 2) hres

/-- A residual PF certificate gives finite-symbol stability after the checked
homogenization and multiplication closures. -/
theorem finiteSymbol_stable_of_residual_certificate
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (cert : BidiagonalCubicResidualCertificate alpha beta d) :
    IsBivariateUpperStable (complexifyMv (finiteSymbol alpha beta d)) := by
  have h_ne : cert.residual ≠ 0 := by
    intro h_eq
    have h_deg := cert.residual_cubic
    rw [h_eq] at h_deg
    simp at h_deg
  have h_splits : cert.residual.Splits := by
    rcases cert.residual_pf.eq_zero_or_splits with h_eq | hsp
    · contradiction
    · exact hsp
  exact finiteSymbol_stable_of_residual_factor cert.symbol_factor
    (RealRooted.BorceaBranden.homogenizeBivariate_stable_of_splits_nonpos
      h_ne h_splits cert.residual_pf.roots_nonpos)

/-- Algebraic dehomogenization identity connecting the finite symbol to the
existing Jensen pencil. -/
theorem finiteSymbol_dehomog (alpha beta : ℕ → ℝ) (d : ℕ) :
    (finiteSymbol alpha beta d).eval₂ (Polynomial.C : ℝ →+* ℝ[X])
        (fun i => if i = 0 then Polynomial.X else 1) =
      bidiagonalJensenPencil alpha beta d 1 := by
  simp only [finiteSymbol, bidiagonalJensenPencil, jensenPolynomial,
    MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, MvPolynomial.eval₂_pow,
    Fin.isValue, if_true, one_ne_zero, if_false, one_pow, mul_one,
    ← Polynomial.C_mul_X_pow_eq_monomial, mul_add, add_mul, mul_assoc]
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _hk
    rw [← mul_assoc, ← Polynomial.C_mul]
  · simp only [Polynomial.C_1, one_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [← mul_assoc, ← Polynomial.C_mul]
    rw [pow_succ]
    ring_nf

private lemma scale_pow_div (x y : ℝ) (n k : ℕ) (hy : y ≠ 0) (hk : k ≤ n) :
    y ^ n * (x / y) ^ k = x ^ k * y ^ (n - k) := by
  rw [div_pow, pow_sub₀ y hy hk]
  ring

/-- Evaluating the finite symbol at `(x,y)` with `y ≠ 0` is the homogenized
dehomogenized Jensen pencil. -/
theorem finiteSymbol_eval_eq_y_pow_dehomog
    (alpha beta : ℕ → ℝ) (d : ℕ) (x y : ℝ) (hy : y ≠ 0) :
    MvPolynomial.eval ![x, y] (finiteSymbol alpha beta d) =
      y ^ (d + 1) * Polynomial.eval (x / y)
        (bidiagonalJensenPencil alpha beta d 1) := by
  simp only [finiteSymbol, bidiagonalJensenPencil, jensenPolynomial,
    MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_add,
    MvPolynomial.eval_C, MvPolynomial.eval_X, Polynomial.eval_finsetSum,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, MvPolynomial.eval_pow, Polynomial.eval_pow,
    Fin.isValue, one_mul, ← Polynomial.C_mul_X_pow_eq_monomial]
  rw [mul_add]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc
    (d.choose k : ℝ) * (alpha k * x ^ k * y + beta k * x ^ (k + 1)) *
        y ^ (d - k)
        = (d.choose k : ℝ) * alpha k * (x ^ k * y ^ (d + 1 - k)) +
          (d.choose k : ℝ) * beta k *
            (x ^ (k + 1) * y ^ (d + 1 - (k + 1))) := by
            have hsub₀ : d + 1 - k = d - k + 1 := by lia
            have hsub₁ : d + 1 - (k + 1) = d - k := by lia
            rw [hsub₀, hsub₁]
            ring
    _ = (d.choose k : ℝ) * alpha k * (y ^ (d + 1) * (x / y) ^ k) +
          (d.choose k : ℝ) * beta k *
            (y ^ (d + 1) * (x / y) ^ (k + 1)) := by
            rw [scale_pow_div x y (d + 1) k hy (by lia)]
            rw [scale_pow_div x y (d + 1) (k + 1) hy (by lia)]
    _ = y ^ (d + 1) * ((d.choose k : ℝ) * alpha k * (x / y) ^ k) +
          y ^ (d + 1) *
            (x / y * ((d.choose k : ℝ) * beta k * (x / y) ^ k)) := by ring_nf

/-- Evaluating a homogeneous bivariate lift at `(x,y)` with `y ≠ 0`
recovers `y^n p(x/y)`. -/
theorem homogenizeBivariate_eval_eq_y_pow_eval
    (p : ℝ[X]) {n : ℕ} (hn : p.natDegree ≤ n) (x y : ℝ) (hy : y ≠ 0) :
    MvPolynomial.eval ![x, y] (homogenizeBivariate n p) =
      y ^ n * p.eval (x / y) := by
  rw [Polynomial.eval_eq_sum_range' (show p.natDegree < n + 1 by lia)]
  simp only [homogenizeBivariate, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, map_pow, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hscale := scale_pow_div x y n k hy hk_le
  calc
    p.coeff k * x ^ k * y ^ (n - k)
        = p.coeff k * (x ^ k * y ^ (n - k)) := by ring
    _ = p.coeff k * (y ^ n * (x / y) ^ k) := by rw [← hscale]
    _ = y ^ n * (p.coeff k * (x / y) ^ k) := by ring

/-- The quadratic Jensen residual has degree at most two. -/
theorem quadraticJensenResidual_natDegree_le_two
    (a b c : ℝ) (d : ℕ) :
    (quadraticJensenResidual a b c d).natDegree ≤ 2 := by
  rw [quadraticJensenResidual]
  compute_degree!

/-- The quadratic bidiagonal residual has degree at most three. -/
theorem quadraticBidiagonalResidual_natDegree_le_three
    (aa ab ac ba bb bc : ℝ) (d : ℕ) :
    (quadraticBidiagonalResidual aa ab ac ba bb bc d).natDegree ≤ 3 := by
  rw [quadraticBidiagonalResidual]
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (quadraticJensenResidual_natDegree_le_two aa ab ac d).trans
      (by norm_num)
  · calc
      (X * quadraticJensenResidual ba bb bc d).natDegree
          ≤ (X : ℝ[X]).natDegree +
              (quadraticJensenResidual ba bb bc d).natDegree :=
            Polynomial.natDegree_mul_le
      _ ≤ 1 + 2 := by
            gcongr
            · rw [Polynomial.natDegree_X]
            · exact quadraticJensenResidual_natDegree_le_two ba bb bc d
      _ = 3 := by norm_num

/-- Quadratic coefficient functions give an explicit cubic residual after
dehomogenizing the finite symbol. -/
theorem finiteSymbol_quadratic_dehomog_eq_factor_residual
    (aa ab ac ba bb bc : ℝ) {d : ℕ} (hd : 2 ≤ d) :
    (finiteSymbol
        (quadraticJensenWeight aa ab ac)
        (quadraticJensenWeight ba bb bc) d).eval₂
        (Polynomial.C : ℝ →+* ℝ[X])
        (fun i => if i = 0 then Polynomial.X else 1) =
      (X + 1) ^ (d - 2) *
        quadraticBidiagonalResidual aa ab ac ba bb bc d := by
  rw [finiteSymbol_dehomog]
  exact quadraticBidiagonalJensenPencil_eq_factor_residual_one
    aa ab ac ba bb bc hd

/-- Quadratic coefficient functions give an explicit bivariate finite-symbol
factorization through the cubic residual homogenized to degree three. -/
theorem finiteSymbol_quadratic_eq_factor_homogenize_three
    (aa ab ac ba bb bc : ℝ) {d : ℕ} (hd : 2 ≤ d) :
    finiteSymbol
        (quadraticJensenWeight aa ab ac)
        (quadraticJensenWeight ba bb bc) d =
      (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (d - 2) *
        homogenizeBivariate 3
          (quadraticBidiagonalResidual aa ab ac ba bb bc d) := by
  let s : Fin 2 → Set ℝ := fun i => if i = 1 then {y | y ≠ 0} else Set.univ
  apply MvPolynomial.funext_set s
  · intro i
    fin_cases i
    · exact Set.infinite_univ
    · have hinf : (Set.univ \ ({0} : Set ℝ)).Infinite :=
        Set.infinite_univ.sdiff (Set.finite_singleton (0 : ℝ))
      convert hinf using 1
      ext y
      simp [s]
  · intro z hz
    have hy : z 1 ≠ 0 := by
      have hz1 := hz 1 (Set.mem_univ 1)
      simpa [s] using hz1
    set x : ℝ := z 0
    set y : ℝ := z 1
    have hzvec : ![x, y] = z := by
      funext i
      fin_cases i <;> simp [x, y]
    have hfin := finiteSymbol_eval_eq_y_pow_dehomog
      (quadraticJensenWeight aa ab ac)
      (quadraticJensenWeight ba bb bc) d x y hy
    have hquad := congrArg (Polynomial.eval (x / y))
      (quadraticBidiagonalJensenPencil_eq_factor_residual_one
        aa ab ac ba bb bc hd)
    have hhom := homogenizeBivariate_eval_eq_y_pow_eval
      (quadraticBidiagonalResidual aa ab ac ba bb bc d)
      (n := 3)
      (quadraticBidiagonalResidual_natDegree_le_three aa ab ac ba bb bc d)
      x y hy
    rw [hzvec] at hfin hhom
    rw [hfin]
    rw [hquad]
    simp only [hhom, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
      Fin.isValue, map_mul, map_pow, map_add, MvPolynomial.eval_X]
    have hxy : x / y + 1 = (x + y) / y := by field_simp [hy]
    rw [hxy]
    have hsplit : y ^ (d + 1) = y ^ 3 * y ^ (d - 2) := by
      have hdadd : d + 1 = 3 + (d - 2) := by lia
      rw [hdadd, pow_add]
    rw [hsplit]
    rw [show z 0 + z 1 = x + y by simp [x, y]]
    rw [mul_assoc (y ^ 3) (y ^ (d - 2))
      (((x + y) / y) ^ (d - 2) *
        Polynomial.eval (x / y)
          (quadraticBidiagonalResidual aa ab ac ba bb bc d))]
    rw [← mul_assoc (y ^ (d - 2)) (((x + y) / y) ^ (d - 2))]
    have hscale := scale_pow_div (x + y) y (d - 2) (d - 2) hy le_rfl
    have hscale' :
        y ^ (d - 2) * ((x + y) / y) ^ (d - 2) = (x + y) ^ (d - 2) := by
      simpa only [tsub_self, pow_zero, mul_one] using hscale
    rw [hscale']
    ring

/-- Complexified form of the quadratic bivariate finite-symbol factorization,
with the homogenization degree rewritten to the residual's cubic degree. -/
theorem finiteSymbol_quadratic_complex_eq_factor_homogenize
    (aa ab ac ba bb bc : ℝ) {d : ℕ} (hd : 2 ≤ d)
    (hdeg : (quadraticBidiagonalResidual aa ab ac ba bb bc d).natDegree = 3) :
    complexifyMv
        (finiteSymbol
          (quadraticJensenWeight aa ab ac)
          (quadraticJensenWeight ba bb bc) d) =
      ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ (d - 2)) *
        complexifyMv
          (homogenizeBivariate
            (quadraticBidiagonalResidual aa ab ac ba bb bc d).natDegree
            (quadraticBidiagonalResidual aa ab ac ba bb bc d)) := by
  have hreal := finiteSymbol_quadratic_eq_factor_homogenize_three
    aa ab ac ba bb bc hd
  unfold complexifyMv
  rw [hreal]
  rw [hdeg]
  simp

/-- Certificate constructor for quadratic coefficient functions once the cubic
residual has been proved PF and genuinely cubic. -/
def quadraticBidiagonalCubicResidualCertificate
    (aa ab ac ba bb bc : ℝ) {d : ℕ} (hd : 2 ≤ d)
    (hdeg : (quadraticBidiagonalResidual aa ab ac ba bb bc d).natDegree = 3)
    (hpf : IsPFPolynomial (quadraticBidiagonalResidual aa ab ac ba bb bc d))
    (halpha : ∀ n, 0 ≤ quadraticJensenWeight aa ab ac n)
    (hbeta : ∀ n, 0 ≤ quadraticJensenWeight ba bb bc n) :
    BidiagonalCubicResidualCertificate
      (quadraticJensenWeight aa ab ac)
      (quadraticJensenWeight ba bb bc) d where
  residual := quadraticBidiagonalResidual aa ab ac ba bb bc d
  residual_cubic := hdeg
  symbol_factor := finiteSymbol_quadratic_complex_eq_factor_homogenize
    aa ab ac ba bb bc hd hdeg
  residual_pf := hpf
  alpha_nonneg := halpha
  beta_nonneg := hbeta

/-- Diagonal coefficient of the second-derivative form as a quadratic Jensen
weight. -/
theorem secondDerivativeAlpha_eq_quadraticJensenWeight
    (a0 b1 c2 : ℝ) :
    secondDerivativeAlpha a0 b1 c2 =
      quadraticJensenWeight c2 (b1 - c2) a0 := by
  funext k
  simp [secondDerivativeAlpha, quadraticJensenWeight]
  ring

/-- Subdiagonal coefficient of the second-derivative form as a quadratic
Jensen weight. -/
theorem secondDerivativeBeta_eq_quadraticJensenWeight
    (a1 b2 : ℝ) :
    secondDerivativeBeta a1 b2 =
      quadraticJensenWeight 0 b2 a1 := by
  funext k
  simp [secondDerivativeBeta, quadraticJensenWeight]
  ring

/-- Diagonal coefficient of the shifted second-derivative form as a quadratic
Jensen weight. -/
theorem shiftedSecondDerivativeAlpha_eq_quadraticJensenWeight
    (a0 b1 : ℝ) :
    shiftedSecondDerivativeAlpha a0 b1 =
      quadraticJensenWeight 0 b1 a0 := by
  funext k
  simp [shiftedSecondDerivativeAlpha, quadraticJensenWeight]
  ring

/-- Subdiagonal coefficient of the shifted second-derivative form as a
quadratic Jensen weight. -/
theorem shiftedSecondDerivativeBeta_eq_quadraticJensenWeight
    (a1 b2 c3 : ℝ) :
    shiftedSecondDerivativeBeta a1 b2 c3 =
      quadraticJensenWeight c3 (b2 - c3) a1 := by
  funext k
  simp [shiftedSecondDerivativeBeta, quadraticJensenWeight]
  ring

/-- Algebraic dehomogenization statement connecting the finite symbol to the
existing Jensen pencil. -/
def finiteSymbolDehomogStatement : Prop :=
  ∀ (alpha beta : ℕ → ℝ) (d : ℕ),
    (finiteSymbol alpha beta d).eval₂ (Polynomial.C : ℝ →+* ℝ[X])
        (fun i => if i = 0 then Polynomial.X else 1) =
      bidiagonalJensenPencil alpha beta d 1

/-- The dehomogenization interface is discharged by `finiteSymbol_dehomog`. -/
theorem finiteSymbolDehomogStatement_valid :
    finiteSymbolDehomogStatement :=
  finiteSymbol_dehomog

end

end FiniteSymbolPF
end Tactic
end RealRooted
