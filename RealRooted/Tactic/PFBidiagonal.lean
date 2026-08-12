import RealRooted.BorceaBranden.Applications.BidiagonalSymbol
import RealRooted.HermiteBiehler
import RealRooted.MultiplierSequence
import RealRooted.Tactic.Finish
import RealRooted.Tactic.PFPolynomial
import RealRooted.Tactic.Lookup

/-!
# PF bidiagonal operator shells

This file packages the coefficient-bidiagonal operator that appears in the
remaining one-step second-derivative OEIS recurrences. Genuine affine-symbol
stability gives a checked PF-preserver route. The weaker one-sided Jensen
pencil remains an explicit conjectural backend.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Coefficient-bidiagonal operator

`bidiagonalOperator alpha beta` sends a coefficient vector `(a_k)` to
`(alpha_k a_k + beta_{k-1} a_{k-1})`, with the second term omitted at `k=0`.
Equivalently,

```text
L(p) = diagonalOperator alpha p + X * diagonalOperator beta p.
```
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

/-- Quadratic coefficient shape produced by
`a + b X D + c X^2 D^2` on the diagonal, and by the shifted
`a X + b X^2 D + c X^3 D^2` part on the lower bidiagonal. -/
def secondDerivativeQuadraticCoeff (a b c : ℝ) (k : ℕ) : ℝ :=
  a + b * (k : ℝ) + c * (k : ℝ) * ((k : ℝ) - 1)

/-- Six-parameter second-derivative operator whose coefficient action is
lower bidiagonal.

The parameters are the coefficients of
`a₀ + a₁ X + b₁ X D + b₂ X² D + c₂ X² D² + c₃ X³ D²`.
The nested `X * (...)` presentation is deliberate: it keeps coefficient
normalization close to repeated uses of `coeff_X_mul`. -/
def secondDerivativeBidiagonalForm
    (a0 a1 b1 b2 c2 c3 : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C a0 * p +
    C a1 * (X * p) +
    C b1 * (X * p.derivative) +
    C b2 * (X * (X * p.derivative)) +
    C c2 * (X * (X * p.derivative.derivative)) +
    C c3 * (X * (X * (X * p.derivative.derivative)))

/-- The six-parameter second-derivative form acts as a coefficient-bidiagonal
operator. -/
theorem secondDerivativeBidiagonalForm_eq_bidiagonalOperator
    (a0 a1 b1 b2 c2 c3 : ℝ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm a0 a1 b1 b2 c2 c3 p =
      bidiagonalOperator
        (fun k => secondDerivativeQuadraticCoeff a0 b1 c2 k)
        (fun k => secondDerivativeQuadraticCoeff a1 b2 c3 k)
        p := by
  ext k
  cases k with
  | zero =>
      simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
        secondDerivativeQuadraticCoeff]
  | succ k =>
      cases k with
      | zero =>
          simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
            secondDerivativeQuadraticCoeff, coeff_derivative]
          ring
      | succ k =>
          cases k with
          | zero =>
              simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
                secondDerivativeQuadraticCoeff, coeff_derivative]
              ring
          | succ k =>
              simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
                secondDerivativeQuadraticCoeff, coeff_derivative]
              ring

/-- Normalize a second-derivative differential form to a named coefficient
bidiagonal operator by identifying the two quadratic coefficient functions. -/
theorem secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq
    {alpha beta : ℕ → ℝ} {a0 a1 b1 b2 c2 c3 : ℝ} (p : ℝ[X])
    (halpha : ∀ k : ℕ, secondDerivativeQuadraticCoeff a0 b1 c2 k = alpha k)
    (hbeta : ∀ k : ℕ, secondDerivativeQuadraticCoeff a1 b2 c3 k = beta k) :
    secondDerivativeBidiagonalForm a0 a1 b1 b2 c2 c3 p =
      bidiagonalOperator alpha beta p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    exact halpha k
  · funext k
    exact hbeta k

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
    HasNonnegCoeffs (bidiagonalOperator alpha beta p) := by
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

/-- Backend certificate for one coefficient-bidiagonal PF preserver.

Entrywise nonnegativity of `alpha` and `beta` is useful for coefficient
nonnegativity, but it is not by itself a proof of PF preservation.  Concrete
backends should prove this predicate from an appropriate total-nonnegativity,
stable-polynomial, or finite multiplier-sequence criterion. -/
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

private theorem complexBidiagonalLinearMap_complexify
    (alpha beta : ℕ → ℝ) (p : ℝ[X]) :
    BorceaBranden.complexBidiagonalLinearMap alpha beta (complexify p) =
      complexify (bidiagonalOperator alpha beta p) := by
  ext n
  cases n with
  | zero =>
      simp [BorceaBranden.complexBidiagonalLinearMap, bidiagonalOperator,
        complexify]
  | succ n =>
      simp [BorceaBranden.complexBidiagonalLinearMap, bidiagonalOperator,
        complexify, coeff_X_mul]

/-- A genuinely stable affine Borcea--Branden symbol gives a degree-bounded
PF-bidiagonal preserver when the relevant coefficient weights are nonnegative.

This is the sound replacement for the insufficient one-sided Jensen-pencil
criterion tracked by issue #240. It invokes the checked degree-box sufficiency
theorem from issue #297 and does not assume a PF-preserver conclusion. -/
theorem bidiagonalPFPreserver_of_affineSymbol
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d
          (BorceaBranden.bidiagonalLinearMap alpha beta))))
    (halpha : ∀ k, k ≤ d → 0 ≤ alpha k)
    (hbeta : ∀ k, k ≤ d → 0 ≤ beta k) :
    BidiagonalPFPreserver alpha beta d := by
  intro p hp hdeg
  have hout_nonneg : HasNonnegCoeffs (bidiagonalOperator alpha beta p) :=
    hp.hasNonnegCoeffs.bidiagonalOperator_of_degree_le hdeg halpha hbeta
  by_cases hp0 : p = 0
  · simpa [hp0] using IsPFPolynomial.zero
  let fmv : MvPolynomial (Fin 1) ℂ :=
    (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm (complexify p)
  have hfmem : fmv ∈ MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) := by
    rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
    intro i
    rw [Subsingleton.elim i default]
    simpa [fmv] using
      (MvPolynomial.degreeOf_uniqueAlgEquiv_symm (σ := Fin 1)
        (complexify p)).trans_le (Polynomial.natDegree_map_le.trans hdeg)
  let f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) := ⟨fmv, hfmem⟩
  have hinput_stable : MvUpperHalfPlaneStable f.1 := by
    simpa [f, fmv] using
      (isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable (complexify p)).mp
        (fun z hz =>
          eval_complexify_ne_zero_of_splits_of_im_pos
            (hp.eq_zero_or_splits.resolve_left hp0) hp0 hz)
  have hout := BorceaBranden.complexBidiagonalDegreeBox_preserves_stability
    alpha beta d hSymbol f hinput_stable
  change MvUpperHalfPlaneStableOrZero
    ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
      (BorceaBranden.complexBidiagonalLinearMap alpha beta
        (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) f.1))) at hout
  have hfpoly :
      MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) f.1 = complexify p := by
    change MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
        ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm (complexify p)) =
      complexify p
    exact (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).apply_symm_apply (complexify p)
  rw [hfpoly] at hout
  rcases hout with hzero | hstable
  · have hcomplex_zero :
        BorceaBranden.complexBidiagonalLinearMap alpha beta (complexify p) = 0 := by
      apply (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm.injective
      simpa using hzero
    rw [complexBidiagonalLinearMap_complexify] at hcomplex_zero
    have hout_zero : bidiagonalOperator alpha beta p = 0 :=
      (Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp hcomplex_zero
    simpa [hout_zero] using IsPFPolynomial.zero
  · apply IsPFPolynomial.of_realRooted_nonneg hout_nonneg
    apply IsUpperHalfPlaneStable.splits_complexify
    rw [isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable]
    simpa [complexBidiagonalLinearMap_complexify] using hstable

/-- Jensen-pencil attached to a coefficient-bidiagonal operator.

For a degree bound `d`, the two diagonal parts have finite Jensen kernels
`jensenPolynomial d alpha` and `jensenPolynomial d beta`.  The pencil

```text
J_alpha,d(t) + lambda * t * J_beta,d(t)
```

is the finite Schur--Szego/proper-position certificate we expect to use for
the Family H coefficient-bidiagonal operators. -/
def bidiagonalJensenPencil (alpha beta : ℕ → ℝ) (d : ℕ) (lam : ℝ) : ℝ[X] :=
  jensenPolynomial d alpha + C lam * X * jensenPolynomial d beta

/-- Quadratic coefficient function `a k^2 + b k + c`. -/
def quadraticJensenWeight (a b c : ℝ) (k : ℕ) : ℝ :=
  a * (k : ℝ) ^ 2 + b * (k : ℝ) + c

/-- Jensen polynomial attached to `quadraticJensenWeight`. -/
def quadraticJensen (a b c : ℝ) (d : ℕ) : ℝ[X] :=
  jensenPolynomial d (quadraticJensenWeight a b c)

/-- The residual quadratic after removing the common `(1+X)^(d-2)` factor. -/
def quadraticJensenResidual (a b c : ℝ) (d : ℕ) : ℝ[X] :=
  C c * (X + 1) ^ 2 +
    C ((a + b) * (d : ℝ)) * X * (X + 1) +
      C (a * (d : ℝ) * ((d : ℝ) - 1)) * X ^ 2

/-- Cubic residual for a bidiagonal Jensen pencil with quadratic coefficient functions. -/
def quadraticBidiagonalResidual
    (aa ab ac ba bb bc : ℝ) (d : ℕ) : ℝ[X] :=
  quadraticJensenResidual aa ab ac d + X * quadraticJensenResidual ba bb bc d

/-- Cubic residual pencil for a bidiagonal Jensen pencil with quadratic coefficients. -/
def quadraticBidiagonalPencilResidual
    (aa ab ac ba bb bc lam : ℝ) (d : ℕ) : ℝ[X] :=
  quadraticJensenResidual aa ab ac d +
    C lam * X * quadraticJensenResidual ba bb bc d

theorem quadraticBidiagonalPencilResidual_one
    (aa ab ac ba bb bc : ℝ) (d : ℕ) :
    quadraticBidiagonalPencilResidual aa ab ac ba bb bc 1 d =
      quadraticBidiagonalResidual aa ab ac ba bb bc d := by
  simp [quadraticBidiagonalPencilResidual, quadraticBidiagonalResidual]

/-- The written second-derivative quadratic coefficient is a quadratic Jensen weight. -/
theorem secondDerivativeQuadraticCoeff_eq_quadraticJensenWeight
    (a b c : ℝ) :
    secondDerivativeQuadraticCoeff a b c = quadraticJensenWeight c (b - c) a := by
  funext k
  simp [secondDerivativeQuadraticCoeff, quadraticJensenWeight]
  ring

/-- `quadraticJensen` is the Jensen polynomial for `quadraticJensenWeight`. -/
theorem quadraticJensen_eq_jensenPolynomial (a b c : ℝ) (d : ℕ) :
    quadraticJensen a b c d =
      jensenPolynomial d (quadraticJensenWeight a b c) := rfl

/-- Factorization of a quadratic Jensen polynomial through its residual. -/
theorem quadraticJensen_eq_factor_residual
    (a b c : ℝ) {d : ℕ} (hd : 2 ≤ d) :
    quadraticJensen a b c d =
      (X + 1) ^ (d - 2) * quadraticJensenResidual a b c d := by
  change jensenPolynomial d (fun k => a * (k : ℝ) ^ 2 + b * (k : ℝ) + c) =
    (X + 1) ^ (d - 2) * quadraticJensenResidual a b c d
  simpa [quadraticJensenResidual] using
    jensenPolynomial_quadratic_sequence_factor a b c d hd

/-- Quadratic coefficient functions give a cubic residual pencil after the common factor. -/
theorem quadraticBidiagonalJensenPencil_eq_factor_residual
    (aa ab ac ba bb bc lam : ℝ) {d : ℕ} (hd : 2 ≤ d) :
    bidiagonalJensenPencil
        (quadraticJensenWeight aa ab ac)
        (quadraticJensenWeight ba bb bc) d lam =
      (X + 1) ^ (d - 2) *
        quadraticBidiagonalPencilResidual aa ab ac ba bb bc lam d := by
  rw [bidiagonalJensenPencil]
  change quadraticJensen aa ab ac d + C lam * X * quadraticJensen ba bb bc d =
    (X + 1) ^ (d - 2) *
      quadraticBidiagonalPencilResidual aa ab ac ba bb bc lam d
  rw [quadraticJensen_eq_factor_residual aa ab ac hd]
  rw [quadraticJensen_eq_factor_residual ba bb bc hd]
  simp [quadraticBidiagonalPencilResidual]
  ring

/-- The `lambda = 1` specialization of the quadratic bidiagonal residual factorization. -/
theorem quadraticBidiagonalJensenPencil_eq_factor_residual_one
    (aa ab ac ba bb bc : ℝ) {d : ℕ} (hd : 2 ≤ d) :
    bidiagonalJensenPencil
        (quadraticJensenWeight aa ab ac)
        (quadraticJensenWeight ba bb bc) d 1 =
      (X + 1) ^ (d - 2) *
        quadraticBidiagonalResidual aa ab ac ba bb bc d := by
  rw [quadraticBidiagonalJensenPencil_eq_factor_residual aa ab ac ba bb bc 1 hd]
  rw [quadraticBidiagonalPencilResidual_one]

@[simp] theorem bidiagonalJensenPencil_zero_lambda
    (alpha beta : ℕ → ℝ) (d : ℕ) :
    bidiagonalJensenPencil alpha beta d 0 = jensenPolynomial d alpha := by
  simp [bidiagonalJensenPencil]

/-- The Jensen pencil has degree at most `d+1`. -/
theorem natDegree_bidiagonalJensenPencil_le
    (alpha beta : ℕ → ℝ) (d : ℕ) (lam : ℝ) :
    (bidiagonalJensenPencil alpha beta d lam).natDegree ≤ d + 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have halpha : (jensenPolynomial d alpha).coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_jensenPolynomial_le d alpha) (by lia))
  cases n with
  | zero =>
      simp [bidiagonalJensenPencil, halpha]
  | succ n =>
      have hbeta : (jensenPolynomial d beta).coeff n = 0 :=
        coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (natDegree_jensenPolynomial_le d beta) (by lia))
      simp [bidiagonalJensenPencil, halpha, mul_assoc, hbeta]

/-- Small explicit PF certificate for a residual cubic.

For Family H, after the common `(1 + X)`-power is factored from the
Jensen-pencil, the remaining residual has degree at most three.  Nonnegative
coefficients plus a nonnegative cubic discriminant make this residual PF. -/
def CubicPFDiscriminantCertificate (p : ℝ[X]) : Prop :=
  HasNonnegCoeffs p ∧ p.natDegree ≤ 3 ∧ 0 ≤ cubicDiscr p

/-- Convert a cubic residual discriminant certificate to the PF predicate. -/
theorem isPFPolynomial_of_cubicPFDiscriminantCertificate
    {p : ℝ[X]} (hcert : CubicPFDiscriminantCertificate p) :
    IsPFPolynomial p :=
  IsPFPolynomial.of_realRooted_nonneg hcert.1 <|
    splits_of_natDegree_le_three_cubicDiscr_nonneg hcert.2.1 hcert.2.2

/-- Multiplication by a power of `1 + X` preserves the PF predicate. -/
theorem isPFPolynomial_X_add_one_pow_mul
    (m : ℕ) {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (((X + 1 : ℝ[X]) ^ m) * p) :=
  (isPFPolynomial_X_add_one.pow m).mul hp

/-- Finite Jensen-pencil certificate for a coefficient-bidiagonal PF backend.

This predicate records the concrete one-sided finite pencil condition.  The
condition does not by itself supply the orientation required by the
Garloff--Wagner proper-position theorem, so the general implication to
`BidiagonalPFPreserver` remains conjectural. -/
def BidiagonalJensenPencilCertificate
    (alpha beta : ℕ → ℝ) (d : ℕ) : Prop :=
  IsPFPolynomial (jensenPolynomial d alpha) ∧
  IsPFPolynomial (X * jensenPolynomial d beta) ∧
  ∀ lam : ℝ, 0 ≤ lam →
    IsPFPolynomial (bidiagonalJensenPencil alpha beta d lam)

/-- A Jensen-pencil certificate makes the diagonal coefficients nonnegative
through the certified degree bound. -/
theorem BidiagonalJensenPencilCertificate.alpha_nonneg_of_le
    {alpha beta : ℕ → ℝ} {d k : ℕ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) (hk : k ≤ d) :
    0 ≤ alpha k := by
  have hcoeff := hcert.1.hasNonnegCoeffs k
  rw [coeff_jensenPolynomial, if_pos hk] at hcoeff
  have hchoose : (0 : ℝ) < Nat.choose d k := by
    exact_mod_cast Nat.choose_pos hk
  nlinarith

/-- A Jensen-pencil certificate makes the subdiagonal coefficients
nonnegative through the certified degree bound. -/
theorem BidiagonalJensenPencilCertificate.beta_nonneg_of_le
    {alpha beta : ℕ → ℝ} {d k : ℕ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) (hk : k ≤ d) :
    0 ≤ beta k := by
  have hcoeff := hcert.2.1.hasNonnegCoeffs (k + 1)
  simp [coeff_jensenPolynomial, hk] at hcoeff
  have hchoose : (0 : ℝ) < Nat.choose d k := by
    exact_mod_cast Nat.choose_pos hk
  nlinarith

/-- In degree one, the output discriminant is the Jensen-pencil discriminant
at `lambda = p.coeff 0 / p.coeff 1`, scaled by `p.coeff 1 ^ 2`. -/
private theorem bidiagonalOperator_discrim_eq_sq_mul_jensenPencil_one
    {alpha beta : ℕ → ℝ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ 1)
    (hp1 : p.coeff 1 ≠ 0) :
    discrim
        ((bidiagonalOperator alpha beta p).coeff 2)
        ((bidiagonalOperator alpha beta p).coeff 1)
        ((bidiagonalOperator alpha beta p).coeff 0) =
      p.coeff 1 ^ 2 * discrim
        ((bidiagonalJensenPencil alpha beta 1
          (p.coeff 0 / p.coeff 1)).coeff 2)
        ((bidiagonalJensenPencil alpha beta 1
          (p.coeff 0 / p.coeff 1)).coeff 1)
        ((bidiagonalJensenPencil alpha beta 1
          (p.coeff 0 / p.coeff 1)).coeff 0) := by
  have hp2 : p.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg (by norm_num))
  have hpencil0 :
      (bidiagonalJensenPencil alpha beta 1
        (p.coeff 0 / p.coeff 1)).coeff 0 = alpha 0 := by
    simp [bidiagonalJensenPencil, mul_assoc, coeff_jensenPolynomial]
  have hpencil1 :
      (bidiagonalJensenPencil alpha beta 1
        (p.coeff 0 / p.coeff 1)).coeff 1 =
          alpha 1 + (p.coeff 0 / p.coeff 1) * beta 0 := by
    simp [bidiagonalJensenPencil, mul_assoc, coeff_jensenPolynomial]
  have hpencil2 :
      (bidiagonalJensenPencil alpha beta 1
        (p.coeff 0 / p.coeff 1)).coeff 2 =
          (p.coeff 0 / p.coeff 1) * beta 1 := by
    simp [bidiagonalJensenPencil, mul_assoc, coeff_jensenPolynomial]
  rw [hpencil0, hpencil1, hpencil2]
  simp only [coeff_bidiagonalOperator_succ, Nat.reduceAdd, hp2, mul_zero,
    zero_add, coeff_bidiagonalOperator_zero]
  unfold discrim
  field_simp [hp1]

/-- The one-sided Jensen-pencil certificate is sufficient in degrees at most
one. -/
theorem jensenPencilBidiagonalPreserver_of_degree_le_one
    {alpha beta : ℕ → ℝ} {d : ℕ} (hd : d ≤ 1)
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d := by
  intro p hp hdeg
  have halpha : ∀ k, k ≤ d → 0 ≤ alpha k :=
    fun k hk ↦ hcert.alpha_nonneg_of_le hk
  have hbeta : ∀ k, k ≤ d → 0 ≤ beta k :=
    fun k hk ↦ hcert.beta_nonneg_of_le hk
  have hout_nonneg : HasNonnegCoeffs (bidiagonalOperator alpha beta p) :=
    hp.hasNonnegCoeffs.bidiagonalOperator_of_degree_le hdeg halpha hbeta
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hout_nonneg
  by_cases hout_zero : bidiagonalOperator alpha beta p = 0
  · exact Or.inl hout_zero
  right
  by_cases hd0 : d = 0
  · have hpdeg0 : p.natDegree = 0 := by lia
    exact (isRealRooted_of_natDegree_le_one hout_zero
      ((natDegree_bidiagonalOperator_le alpha beta p).trans (by lia))).2
  have hd1 : d = 1 := by lia
  subst d
  have hpdeg : p.natDegree ≤ 1 := hdeg
  by_cases hp1 : p.coeff 1 = 0
  · have hpdeg0 : p.natDegree ≤ 0 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro n hn
      by_cases hn1 : n = 1
      · simpa [hn1] using hp1
      · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg (by lia))
    exact (isRealRooted_of_natDegree_le_one hout_zero
      ((natDegree_bidiagonalOperator_le alpha beta p).trans (by lia))).2
  · have hp1_pos : 0 < p.coeff 1 :=
      lt_of_le_of_ne (hp.hasNonnegCoeffs 1) (Ne.symm hp1)
    let lam : ℝ := p.coeff 0 / p.coeff 1
    have hlam : 0 ≤ lam := div_nonneg (hp.hasNonnegCoeffs 0) hp1_pos.le
    have hpencil := hcert.2.2 lam hlam
    have hpencil_disc :
        4 * ((bidiagonalJensenPencil alpha beta 1 lam).coeff 0 *
          (bidiagonalJensenPencil alpha beta 1 lam).coeff 2) ≤
            (bidiagonalJensenPencil alpha beta 1 lam).coeff 1 ^ 2 := by
      rcases hpencil.eq_zero_or_splits with hpencil_zero | hpencil_splits
      · simp [hpencil_zero]
      · exact quadratic_disc_coeff_le_of_splits_natDegree_le_two
          (natDegree_bidiagonalJensenPencil_le alpha beta 1 lam) hpencil_splits
    have hpencil_discrim : 0 ≤ discrim
        ((bidiagonalJensenPencil alpha beta 1 lam).coeff 2)
        ((bidiagonalJensenPencil alpha beta 1 lam).coeff 1)
        ((bidiagonalJensenPencil alpha beta 1 lam).coeff 0) := by
      unfold discrim
      linarith
    have hout_discrim : 0 ≤ discrim
        ((bidiagonalOperator alpha beta p).coeff 2)
        ((bidiagonalOperator alpha beta p).coeff 1)
        ((bidiagonalOperator alpha beta p).coeff 0) := by
      rw [bidiagonalOperator_discrim_eq_sq_mul_jensenPencil_one hpdeg hp1]
      exact mul_nonneg (sq_nonneg _) hpencil_discrim
    have hout_deg : (bidiagonalOperator alpha beta p).natDegree ≤ 2 :=
      (natDegree_bidiagonalOperator_le alpha beta p).trans (by lia)
    rw [Polynomial.eq_quadratic_of_degree_le_two
      (Polynomial.degree_le_of_natDegree_le hout_deg)]
    exact quadraticPoly_splits_of_discrim_nonneg_or_linear hout_discrim

/-- If the last subdiagonal coefficient vanishes, the bidiagonal operator does
not raise the input degree. -/
private theorem natDegree_bidiagonalOperator_le_of_beta_eq_zero
    {alpha beta : ℕ → ℝ} {p : ℝ[X]} {d : ℕ}
    (hpdeg : p.natDegree ≤ d) (hbeta : beta d = 0) :
    (bidiagonalOperator alpha beta p).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  cases n with
  | zero => lia
  | succ k =>
      rw [coeff_bidiagonalOperator_succ]
      have hp_succ : p.coeff (k + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg hn)
      by_cases hk : k = d
      · subst k
        simp [hp_succ, hbeta]
      · have hdk : d < k := by lia
        have hp_k : p.coeff k = 0 :=
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg hdk)
        simp [hp_succ, hp_k]

/-- If the last subdiagonal coefficient vanishes, the Jensen pencil stays
within the certified degree. -/
private theorem natDegree_bidiagonalJensenPencil_le_of_beta_eq_zero
    {alpha beta : ℕ → ℝ} {d : ℕ} {lam : ℝ}
    (hbeta : beta d = 0) :
    (bidiagonalJensenPencil alpha beta d lam).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have halpha : (jensenPolynomial d alpha).coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_jensenPolynomial_le d alpha) hn)
  cases n with
  | zero => lia
  | succ k =>
      by_cases hk : k = d
      · subst k
        simp [bidiagonalJensenPencil, mul_assoc, halpha,
          coeff_jensenPolynomial, hbeta]
      · have hdk : d < k := by lia
        have hbeta_coeff : (jensenPolynomial d beta).coeff k = 0 :=
          coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt (natDegree_jensenPolynomial_le d beta) hdk)
        simp [bidiagonalJensenPencil, mul_assoc, halpha, hbeta_coeff]

/-- Degree-two output discriminant identity at the coefficient-determined
Jensen-pencil parameter. -/
private theorem four_mul_bidiagonalOperator_discrim_eq_jensenPencil_two
    {alpha beta : ℕ → ℝ} {p : ℝ[X]} (hp1 : p.coeff 1 ≠ 0) :
    4 * discrim
        ((bidiagonalOperator alpha beta p).coeff 2)
        ((bidiagonalOperator alpha beta p).coeff 1)
        ((bidiagonalOperator alpha beta p).coeff 0) =
      p.coeff 1 ^ 2 * discrim
        ((bidiagonalJensenPencil alpha beta 2
          (2 * p.coeff 0 / p.coeff 1)).coeff 2)
        ((bidiagonalJensenPencil alpha beta 2
          (2 * p.coeff 0 / p.coeff 1)).coeff 1)
        ((bidiagonalJensenPencil alpha beta 2
          (2 * p.coeff 0 / p.coeff 1)).coeff 0) +
        4 * alpha 0 * alpha 2 *
          (p.coeff 1 ^ 2 - 4 * p.coeff 0 * p.coeff 2) := by
  have hpencil0 :
      (bidiagonalJensenPencil alpha beta 2
        (2 * p.coeff 0 / p.coeff 1)).coeff 0 = alpha 0 := by
    simp [bidiagonalJensenPencil, mul_assoc, coeff_jensenPolynomial]
  have hpencil1 :
      (bidiagonalJensenPencil alpha beta 2
        (2 * p.coeff 0 / p.coeff 1)).coeff 1 =
          2 * alpha 1 + (2 * p.coeff 0 / p.coeff 1) * beta 0 := by
    simp [bidiagonalJensenPencil, mul_assoc, coeff_jensenPolynomial]
  have hpencil2 :
      (bidiagonalJensenPencil alpha beta 2
        (2 * p.coeff 0 / p.coeff 1)).coeff 2 =
          alpha 2 + 2 * (2 * p.coeff 0 / p.coeff 1) * beta 1 := by
    simp [bidiagonalJensenPencil, mul_assoc, coeff_jensenPolynomial]
    ring
  rw [hpencil0, hpencil1, hpencil2]
  simp only [coeff_bidiagonalOperator_succ, Nat.reduceAdd, zero_add,
    coeff_bidiagonalOperator_zero]
  unfold discrim
  field_simp [hp1]
  ring

/-- In degree two, the one-sided Jensen-pencil certificate is sufficient when
the last subdiagonal coefficient vanishes. -/
theorem jensenPencilBidiagonalPreserver_two_of_beta_two_eq_zero
    {alpha beta : ℕ → ℝ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta 2)
    (hbeta2 : beta 2 = 0) :
    BidiagonalPFPreserver alpha beta 2 := by
  intro p hp hdeg
  have halpha : ∀ k, k ≤ 2 → 0 ≤ alpha k :=
    fun k hk ↦ hcert.alpha_nonneg_of_le hk
  have hbeta : ∀ k, k ≤ 2 → 0 ≤ beta k :=
    fun k hk ↦ hcert.beta_nonneg_of_le hk
  have hout_nonneg : HasNonnegCoeffs (bidiagonalOperator alpha beta p) :=
    hp.hasNonnegCoeffs.bidiagonalOperator_of_degree_le hdeg halpha hbeta
  apply IsPFPolynomial.of_realRooted_nonneg hout_nonneg
  have hout_deg : (bidiagonalOperator alpha beta p).natDegree ≤ 2 :=
    natDegree_bidiagonalOperator_le_of_beta_eq_zero hdeg hbeta2
  have hp_disc : 4 * (p.coeff 0 * p.coeff 2) ≤ p.coeff 1 ^ 2 :=
    disc_nonneg_of_isPolyaFreqSeq_natDegree_le_two hp.to_sequence hdeg
  have hout_discrim : 0 ≤ discrim
      ((bidiagonalOperator alpha beta p).coeff 2)
      ((bidiagonalOperator alpha beta p).coeff 1)
      ((bidiagonalOperator alpha beta p).coeff 0) := by
    by_cases hp1 : p.coeff 1 = 0
    · have hp02 : p.coeff 0 * p.coeff 2 = 0 := by
        have hp0 := hp.hasNonnegCoeffs 0
        have hp2 := hp.hasNonnegCoeffs 2
        rw [hp1] at hp_disc
        nlinarith
      rcases mul_eq_zero.mp hp02 with hp0 | hp2
      · simp [coeff_bidiagonalOperator_succ, hp1, hp0, discrim]
      · simpa [coeff_bidiagonalOperator_succ, hp1, hp2, discrim] using
          sq_nonneg (beta 0 * p.coeff 0)
    · have hp1_pos : 0 < p.coeff 1 :=
        lt_of_le_of_ne (hp.hasNonnegCoeffs 1) (Ne.symm hp1)
      let lam : ℝ := 2 * p.coeff 0 / p.coeff 1
      have hlam : 0 ≤ lam := div_nonneg
        (mul_nonneg (by norm_num) (hp.hasNonnegCoeffs 0)) hp1_pos.le
      have hpencil := hcert.2.2 lam hlam
      have hpencil_deg :
          (bidiagonalJensenPencil alpha beta 2 lam).natDegree ≤ 2 :=
        natDegree_bidiagonalJensenPencil_le_of_beta_eq_zero hbeta2
      have hpencil_disc : 4 *
          ((bidiagonalJensenPencil alpha beta 2 lam).coeff 0 *
            (bidiagonalJensenPencil alpha beta 2 lam).coeff 2) ≤
          (bidiagonalJensenPencil alpha beta 2 lam).coeff 1 ^ 2 :=
        disc_nonneg_of_isPolyaFreqSeq_natDegree_le_two
          hpencil.to_sequence hpencil_deg
      have hpencil_discrim : 0 ≤ discrim
          ((bidiagonalJensenPencil alpha beta 2 lam).coeff 2)
          ((bidiagonalJensenPencil alpha beta 2 lam).coeff 1)
          ((bidiagonalJensenPencil alpha beta 2 lam).coeff 0) := by
        unfold discrim
        linarith
      have hinput_discrim :
          0 ≤ p.coeff 1 ^ 2 - 4 * p.coeff 0 * p.coeff 2 := by
        linarith
      have hfour_alpha02 : 0 ≤ 4 * alpha 0 * alpha 2 :=
        mul_nonneg
          (mul_nonneg (by norm_num) (halpha 0 (by norm_num)))
          (halpha 2 (by norm_num))
      have hidentity :=
        four_mul_bidiagonalOperator_discrim_eq_jensenPencil_two
          (alpha := alpha) (beta := beta) hp1
      have hpencil_discrim' : 0 ≤ discrim
          ((bidiagonalJensenPencil alpha beta 2
            (2 * p.coeff 0 / p.coeff 1)).coeff 2)
          ((bidiagonalJensenPencil alpha beta 2
            (2 * p.coeff 0 / p.coeff 1)).coeff 1)
          ((bidiagonalJensenPencil alpha beta 2
            (2 * p.coeff 0 / p.coeff 1)).coeff 0) := by
        simpa [lam] using hpencil_discrim
      have hrhs_nonneg : 0 ≤
          p.coeff 1 ^ 2 * discrim
            ((bidiagonalJensenPencil alpha beta 2
              (2 * p.coeff 0 / p.coeff 1)).coeff 2)
            ((bidiagonalJensenPencil alpha beta 2
              (2 * p.coeff 0 / p.coeff 1)).coeff 1)
            ((bidiagonalJensenPencil alpha beta 2
              (2 * p.coeff 0 / p.coeff 1)).coeff 0) +
            4 * alpha 0 * alpha 2 *
              (p.coeff 1 ^ 2 - 4 * p.coeff 0 * p.coeff 2) := add_nonneg
        (mul_nonneg (sq_nonneg _) hpencil_discrim')
        (mul_nonneg hfour_alpha02 hinput_discrim)
      nlinarith [hidentity]
  rw [Polynomial.eq_quadratic_of_degree_le_two
    (Polynomial.degree_le_of_natDegree_le hout_deg)]
  exact quadraticPoly_splits_of_discrim_nonneg_or_linear hout_discrim

/-- Conjectural Jensen-pencil implication for coefficient-bidiagonal PF
preservers, retained as an explicit admission.

This is the single explicit admission for this project conjecture. It is not a
checked proof; checked applications should prefer
`bidiagonalPFPreserver_of_affineSymbol`. -/
theorem jensenPencilBidiagonalPreserver :
    ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d := by
  sorry

/-- Apply the named Jensen-pencil backend theorem. -/
theorem bidiagonalPFPreserver_of_jensenPencil
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  jensenPencilBidiagonalPreserver hcert

/-- A Jensen-pencil certificate gives a coefficient-bidiagonal PF preserver
once the global backend is available. -/
theorem BidiagonalJensenPencilCertificate.toPFPreserver
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  bidiagonalPFPreserver_of_jensenPencil hcert

/-- Rowwise Jensen-pencil certificates give rowwise coefficient-bidiagonal
PF preservers. -/
theorem BidiagonalJensenPencilCertificate.toPFPreserver_sequence
    {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hcert : ∀ n : Nat,
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n)) :
    ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n) :=
  fun n => (hcert n).toPFPreserver

/-- Tail-start rowwise version of
`BidiagonalJensenPencilCertificate.toPFPreserver_sequence`. -/
theorem BidiagonalJensenPencilCertificate.toPFPreserver_sequence_from
    (N : Nat) {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n)) :
    ∀ n : Nat, N ≤ n → BidiagonalPFPreserver (alpha n) (beta n) (d n) :=
  fun n hn => (hcert n hn).toPFPreserver

/-- Build a Jensen-pencil certificate from a common `(1 + X)`-power
factorization and cubic residual discriminant certificates.

This is the Lean-facing shape of the Family H symbolic proof: for each row
degree, factor `J_alpha,d`, `X * J_beta,d`, and the full nonnegative pencil
through the same PF factor `(1 + X)^m`; then discharge only residual cubic
nonnegativity and discriminant side goals. -/
theorem bidiagonalJensenPencilCertificate_of_cubicResidual
    {alpha beta : ℕ → ℝ} {d m : ℕ}
    {A B : ℝ[X]} {S : ℝ → ℝ[X]}
    (halpha : jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * A)
    (hbeta : X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * B)
    (hpencil : ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil alpha beta d lam =
        ((X + 1 : ℝ[X]) ^ m) * S lam)
    (hA : CubicPFDiscriminantCertificate A)
    (hB : CubicPFDiscriminantCertificate B)
    (hS : ∀ lam : ℝ, 0 ≤ lam → CubicPFDiscriminantCertificate (S lam)) :
    BidiagonalJensenPencilCertificate alpha beta d := by
  refine ⟨?_, ?_, ?_⟩
  · rw [halpha]
    exact isPFPolynomial_X_add_one_pow_mul m
      (isPFPolynomial_of_cubicPFDiscriminantCertificate hA)
  · rw [hbeta]
    exact isPFPolynomial_X_add_one_pow_mul m
      (isPFPolynomial_of_cubicPFDiscriminantCertificate hB)
  · intro lam hlam
    rw [hpencil lam hlam]
    exact isPFPolynomial_X_add_one_pow_mul m
      (isPFPolynomial_of_cubicPFDiscriminantCertificate (hS lam hlam))

/-- The full Jensen-pencil factorization follows from the two endpoint
factorizations when the residual pencil is `A + C lam * B`. -/
theorem bidiagonalJensenPencil_factor_of_endpoint_factors
    {alpha beta : ℕ → ℝ} {d m : ℕ} {A B : ℝ[X]}
    (halpha : jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * A)
    (hbeta : X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * B)
    (lam : ℝ) :
    bidiagonalJensenPencil alpha beta d lam =
      ((X + 1 : ℝ[X]) ^ m) * (A + C lam * B) := by
  rw [bidiagonalJensenPencil]
  calc
    jensenPolynomial d alpha + C lam * X * jensenPolynomial d beta =
        ((X + 1 : ℝ[X]) ^ m) * A + C lam * X * jensenPolynomial d beta := by
      rw [halpha]
    _ = ((X + 1 : ℝ[X]) ^ m) * A +
        C lam * (X * jensenPolynomial d beta) := by
      ring
    _ = ((X + 1 : ℝ[X]) ^ m) * A + C lam *
        (((X + 1 : ℝ[X]) ^ m) * B) := by
      rw [hbeta]
    _ = ((X + 1 : ℝ[X]) ^ m) * (A + C lam * B) := by
      ring

/-- Build a Jensen-pencil certificate from endpoint factorizations and the
derived residual pencil `A + C lam * B`. -/
theorem bidiagonalJensenPencilCertificate_of_endpoint_cubicResidual
    {alpha beta : ℕ → ℝ} {d m : ℕ} {A B : ℝ[X]}
    (halpha : jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * A)
    (hbeta : X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * B)
    (hA : CubicPFDiscriminantCertificate A)
    (hB : CubicPFDiscriminantCertificate B)
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A + C lam * B)) :
    BidiagonalJensenPencilCertificate alpha beta d :=
  bidiagonalJensenPencilCertificate_of_cubicResidual
    halpha hbeta
    (fun lam _hlam =>
      bidiagonalJensenPencil_factor_of_endpoint_factors halpha hbeta lam)
    hA hB hS

/-- Bundled cubic-residual certificate for one coefficient-bidiagonal
Jensen pencil.

This is the hint object intended for OEIS use.  A sequence-specific certificate
can choose its own common factor exponent, residual cubics, active-degree
cutoff, and arithmetic proof.  The tactic layer then only needs this bundle,
the recurrence, and the global PF-bidiagonal backend theorem. -/
structure BidiagonalCubicResidualCertificate
    (alpha beta : ℕ → ℝ) (d : ℕ) where
  m : ℕ
  alphaResidual : ℝ[X]
  betaResidual : ℝ[X]
  pencilResidual : ℝ → ℝ[X]
  alpha_factor :
    jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * alphaResidual
  beta_factor :
    X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * betaResidual
  pencil_factor : ∀ lam : ℝ, 0 ≤ lam →
    bidiagonalJensenPencil alpha beta d lam =
      ((X + 1 : ℝ[X]) ^ m) * pencilResidual lam
  alpha_cubic : CubicPFDiscriminantCertificate alphaResidual
  beta_cubic : CubicPFDiscriminantCertificate betaResidual
  pencil_cubic : ∀ lam : ℝ, 0 ≤ lam →
    CubicPFDiscriminantCertificate (pencilResidual lam)

/-- Build the bundled cubic-residual certificate from its arithmetic leaves. -/
def bidiagonalCubicResidualCertificate_of_cubicResidual
    {alpha beta : ℕ → ℝ} {d m : ℕ}
    {A B : ℝ[X]} {S : ℝ → ℝ[X]}
    (halpha : jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * A)
    (hbeta : X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * B)
    (hpencil : ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil alpha beta d lam = ((X + 1 : ℝ[X]) ^ m) * S lam)
    (hA : CubicPFDiscriminantCertificate A)
    (hB : CubicPFDiscriminantCertificate B)
    (hS : ∀ lam : ℝ, 0 ≤ lam → CubicPFDiscriminantCertificate (S lam)) :
    BidiagonalCubicResidualCertificate alpha beta d where
  m := m
  alphaResidual := A
  betaResidual := B
  pencilResidual := S
  alpha_factor := halpha
  beta_factor := hbeta
  pencil_factor := hpencil
  alpha_cubic := hA
  beta_cubic := hB
  pencil_cubic := hS

/-- Build the bundled cubic-residual certificate from endpoint factorizations
and the derived residual pencil `A + C lam * B`. -/
def bidiagonalCubicResidualCertificate_of_endpoint_cubicResidual
    {alpha beta : ℕ → ℝ} {d m : ℕ} {A B : ℝ[X]}
    (halpha : jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * A)
    (hbeta : X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * B)
    (hA : CubicPFDiscriminantCertificate A)
    (hB : CubicPFDiscriminantCertificate B)
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A + C lam * B)) :
    BidiagonalCubicResidualCertificate alpha beta d :=
  bidiagonalCubicResidualCertificate_of_cubicResidual
    halpha hbeta
    (fun lam _hlam =>
      bidiagonalJensenPencil_factor_of_endpoint_factors halpha hbeta lam)
    hA hB hS

/-- Build a rowwise bundled cubic-residual certificate sequence from its
arithmetic leaves. -/
def bidiagonalCubicResidualCertificate_sequence_of_cubicResidual
    {alpha beta : Nat → ℕ → ℝ} {d m : Nat → ℕ}
    {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hpencil : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil (alpha n) (beta n) (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * S n lam)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (S n lam)) :
    ∀ n : Nat, BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n) :=
  fun n =>
    bidiagonalCubicResidualCertificate_of_cubicResidual
      (halpha n) (hbeta n) (hpencil n) (hA n) (hB n) (hS n)

/-- Tail-start version of
`bidiagonalCubicResidualCertificate_sequence_of_cubicResidual`. -/
def bidiagonalCubicResidualCertificate_sequence_of_cubicResidual_from
    {alpha beta : Nat → ℕ → ℝ} {d m : Nat → ℕ}
    {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (N : Nat)
    (halpha : ∀ n : Nat, N ≤ n →
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat, N ≤ n →
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hpencil : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil (alpha n) (beta n) (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * S n lam)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (S n lam)) :
    ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n) :=
  fun n hn =>
    bidiagonalCubicResidualCertificate_of_cubicResidual
      (halpha n hn) (hbeta n hn) (hpencil n hn)
      (hA n hn) (hB n hn) (hS n hn)

/-- Build a rowwise bundled cubic-residual certificate sequence from endpoint
factorizations and the derived residual pencil `A n + C lam * B n`. -/
def bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual
    {alpha beta : Nat → ℕ → ℝ} {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n)) :
    ∀ n : Nat, BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n) :=
  fun n =>
    bidiagonalCubicResidualCertificate_of_endpoint_cubicResidual
      (halpha n) (hbeta n) (hA n) (hB n) (hS n)

/-- Tail-start version of
`bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual`. -/
def bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual_from
    {alpha beta : Nat → ℕ → ℝ} {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
    (N : Nat)
    (halpha : ∀ n : Nat, N ≤ n →
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat, N ≤ n →
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n)) :
    ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n) :=
  fun n hn =>
    bidiagonalCubicResidualCertificate_of_endpoint_cubicResidual
      (halpha n hn) (hbeta n hn) (hA n hn) (hB n hn) (hS n hn)

/-- Cubic-residual certificate specialized to quadratic Jensen coefficient functions. -/
def quadraticBidiagonalCubicResidualCertificate
    (aa ab ac ba bb bc : ℝ) {d : ℕ} (hd : 2 ≤ d)
    (hA : CubicPFDiscriminantCertificate (quadraticJensenResidual aa ab ac d))
    (hB : CubicPFDiscriminantCertificate (X * quadraticJensenResidual ba bb bc d))
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual aa ab ac ba bb bc lam d)) :
    BidiagonalCubicResidualCertificate
      (quadraticJensenWeight aa ab ac)
      (quadraticJensenWeight ba bb bc) d where
  m := d - 2
  alphaResidual := quadraticJensenResidual aa ab ac d
  betaResidual := X * quadraticJensenResidual ba bb bc d
  pencilResidual := fun lam => quadraticBidiagonalPencilResidual aa ab ac ba bb bc lam d
  alpha_factor := quadraticJensen_eq_factor_residual aa ab ac hd
  beta_factor := by
    have hbeta := quadraticJensen_eq_factor_residual ba bb bc hd
    change X * quadraticJensen ba bb bc d =
      (X + 1) ^ (d - 2) * (X * quadraticJensenResidual ba bb bc d)
    rw [hbeta]
    ring
  pencil_factor := fun lam _ =>
    quadraticBidiagonalJensenPencil_eq_factor_residual aa ab ac ba bb bc lam hd
  alpha_cubic := hA
  beta_cubic := hB
  pencil_cubic := hS

/-- Cubic-residual certificate specialized to the canonical quadratic
coefficient functions of a second-derivative bidiagonal form. -/
def secondDerivativeBidiagonalCubicResidualCertificate
    {a0 a1 b1 b2 c2 c3 : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hA : CubicPFDiscriminantCertificate
      (quadraticJensenResidual c2 (b1 - c2) a0 d))
    (hB : CubicPFDiscriminantCertificate
      (X * quadraticJensenResidual c3 (b2 - c3) a1 d))
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual
          c2 (b1 - c2) a0 c3 (b2 - c3) a1 lam d)) :
    BidiagonalCubicResidualCertificate
      (fun k => secondDerivativeQuadraticCoeff a0 b1 c2 k)
      (fun k => secondDerivativeQuadraticCoeff a1 b2 c3 k) d := by
  simpa [secondDerivativeQuadraticCoeff_eq_quadraticJensenWeight] using
    quadraticBidiagonalCubicResidualCertificate
      c2 (b1 - c2) a0 c3 (b2 - c3) a1 hd hA hB hS

/-- Rowwise canonical second-derivative cubic-residual certificates. -/
def secondDerivativeBidiagonalCubicResidualCertificate_sequence
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate
      (quadraticJensenResidual (c2 n) (b1 n - c2 n) (a0 n) (d n)))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate
      (X * quadraticJensenResidual (c3 n) (b2 n - c3 n) (a1 n) (d n)))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual
          (c2 n) (b1 n - c2 n) (a0 n)
          (c3 n) (b2 n - c3 n) (a1 n) lam (d n))) :
    ∀ n : Nat,
      BidiagonalCubicResidualCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n) :=
  fun n =>
    secondDerivativeBidiagonalCubicResidualCertificate
      (a0 := a0 n) (a1 := a1 n) (b1 := b1 n)
      (b2 := b2 n) (c2 := c2 n) (c3 := c3 n)
      (hd n) (hA n) (hB n) (hS n)

/-- Tail-start version of
`secondDerivativeBidiagonalCubicResidualCertificate_sequence`. -/
def secondDerivativeBidiagonalCubicResidualCertificate_sequence_from
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hd : ∀ n : Nat, N ≤ n → 2 ≤ d n)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate
      (quadraticJensenResidual (c2 n) (b1 n - c2 n) (a0 n) (d n)))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate
      (X * quadraticJensenResidual (c3 n) (b2 n - c3 n) (a1 n) (d n)))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual
          (c2 n) (b1 n - c2 n) (a0 n)
          (c3 n) (b2 n - c3 n) (a1 n) lam (d n))) :
    ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n) :=
  fun n hn =>
    secondDerivativeBidiagonalCubicResidualCertificate
      (a0 := a0 n) (a1 := a1 n) (b1 := b1 n)
      (b2 := b2 n) (c2 := c2 n) (c3 := c3 n)
      (hd n hn) (hA n hn) (hB n hn) (hS n hn)

/-- Forget a bundled cubic-residual certificate to the Jensen-pencil
certificate used by the PF-bidiagonal backend. -/
theorem BidiagonalCubicResidualCertificate.toJensenPencilCertificate
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalCubicResidualCertificate alpha beta d) :
    BidiagonalJensenPencilCertificate alpha beta d :=
  bidiagonalJensenPencilCertificate_of_cubicResidual
    hcert.alpha_factor hcert.beta_factor hcert.pencil_factor
    hcert.alpha_cubic hcert.beta_cubic hcert.pencil_cubic

/-- A bundled cubic-residual certificate gives a coefficient-bidiagonal PF
preserver once the global Jensen-pencil backend is available. -/
theorem BidiagonalCubicResidualCertificate.toPFPreserver
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalCubicResidualCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  bidiagonalPFPreserver_of_jensenPencil hcert.toJensenPencilCertificate

/-- Rowwise cubic-residual certificates give rowwise coefficient-bidiagonal
PF preservers. -/
theorem BidiagonalCubicResidualCertificate.toPFPreserver_sequence
    {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n)) :
    ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n) :=
  fun n => (hcert n).toPFPreserver

/-- Tail-start rowwise version of
`BidiagonalCubicResidualCertificate.toPFPreserver_sequence`. -/
theorem BidiagonalCubicResidualCertificate.toPFPreserver_sequence_from
    (N : Nat) {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n)) :
    ∀ n : Nat, N ≤ n → BidiagonalPFPreserver (alpha n) (beta n) (d n) :=
  fun n hn => (hcert n hn).toPFPreserver

/-- Apply a bundled cubic-residual certificate as a PF-bidiagonal preserver. -/
theorem bidiagonalPFPreserver_of_cubicResidualCertificate
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalCubicResidualCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  hcert.toPFPreserver

/-- Method-style compatibility spelling for cubic-residual PF-bidiagonal certificates. -/
theorem BidiagonalPFPreserver.of_cubicResidualCertificate
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalCubicResidualCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  bidiagonalPFPreserver_of_cubicResidualCertificate hcert

/-- Quadratic Jensen residual certificate route for a coefficient-bidiagonal preserver. -/
theorem quadraticBidiagonalPFPreserver_of_cubicResidualCertificate
    (aa ab ac ba bb bc : ℝ) {d : ℕ} (hd : 2 ≤ d)
    (hA : CubicPFDiscriminantCertificate (quadraticJensenResidual aa ab ac d))
    (hB : CubicPFDiscriminantCertificate (X * quadraticJensenResidual ba bb bc d))
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual aa ab ac ba bb bc lam d)) :
    BidiagonalPFPreserver
      (quadraticJensenWeight aa ab ac)
      (quadraticJensenWeight ba bb bc) d :=
  bidiagonalPFPreserver_of_cubicResidualCertificate
    (quadraticBidiagonalCubicResidualCertificate aa ab ac ba bb bc hd hA hB hS)

/-- Quadratic residual certificate route for the canonical coefficient
functions of a second-derivative bidiagonal form. -/
theorem secondDerivativeBidiagonalPFPreserver_of_cubicResidualCertificate
    {a0 a1 b1 b2 c2 c3 : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hA : CubicPFDiscriminantCertificate
      (quadraticJensenResidual c2 (b1 - c2) a0 d))
    (hB : CubicPFDiscriminantCertificate
      (X * quadraticJensenResidual c3 (b2 - c3) a1 d))
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual
          c2 (b1 - c2) a0 c3 (b2 - c3) a1 lam d)) :
    BidiagonalPFPreserver
      (fun k => secondDerivativeQuadraticCoeff a0 b1 c2 k)
      (fun k => secondDerivativeQuadraticCoeff a1 b2 c3 k) d :=
  bidiagonalPFPreserver_of_cubicResidualCertificate
    (secondDerivativeBidiagonalCubicResidualCertificate hd hA hB hS)

/-- Apply a PF-bidiagonal preserver certificate to one polynomial. -/
theorem isPFPolynomial_bidiagonalOperator_of_preserver
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hpres : BidiagonalPFPreserver alpha beta d)
    (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ d) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) :=
  hpres hp hdeg

/-- Apply a Jensen-pencil backend certificate to one polynomial. -/
theorem isPFPolynomial_bidiagonalOperator_of_jensenPencil
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d)
    (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ d) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) :=
  isPFPolynomial_bidiagonalOperator_of_preserver
    hcert.toPFPreserver hp hdeg

/-- Apply a bundled cubic-residual certificate to one coefficient-bidiagonal
operator. -/
theorem isPFPolynomial_bidiagonalOperator_of_cubicResidualCertificate
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hcert : BidiagonalCubicResidualCertificate alpha beta d)
    (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ d) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) :=
  isPFPolynomial_bidiagonalOperator_of_preserver
    hcert.toPFPreserver hp hdeg

/-- Project splitting from a zero-aware PF certificate. -/
theorem splits_of_isPFPolynomial {p : ℝ[X]} (hp : IsPFPolynomial p) :
    p.Splits :=
  RealRooted.Tactic.pf_splits hp

/-- Project one row from a PF sequence certificate. -/
theorem at_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) (n : Nat) :
    IsPFPolynomial (P n) :=
  hP n

/-- Project row-wise coefficient nonnegativity from a PF sequence certificate. -/
theorem hasNonnegCoeffs_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, HasNonnegCoeffs (P n) :=
  RealRooted.Tactic.pf_sequence_has_nonneg hP

/-- Project row-wise zero-or-splitting from a PF sequence certificate. -/
theorem eq_zero_or_splits_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits :=
  RealRooted.Tactic.pf_sequence_zero_or_splits hP

/-- Project row-wise splitting from a PF sequence certificate. -/
theorem splits_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, (P n).Splits :=
  RealRooted.Tactic.pf_sequence_splits hP

/-- Combine a PF sequence certificate with row-wise nonvanishing to obtain the
strict real-rootedness shape used by the scalar recurrence tactics. -/
theorem isRealRooted_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n))
    (hne : ∀ n : Nat, P n ≠ 0) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  RealRooted.Tactic.pf_sequence_realrooted hP hne

/-- Sequence wrapper for first-order recurrences by coefficient-bidiagonal
PF-preserving operators. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  sequence_of_base_and_step hbase fun n hP => by
    simpa [hrec n] using
      isPFPolynomial_bidiagonalOperator_of_preserver (hpres n) hP (hdeg n)

/-- Sequence wrapper for first-order recurrences whose PF-bidiagonal
certificate only starts from a cutoff row.  The finitely many rows before the
cutoff are supplied as base cases. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, N ≤ n → BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  sequence_of_base_interval_and_step_from N hbase fun n hn hP => by
    simpa [hrec n hn] using
      isPFPolynomial_bidiagonalOperator_of_preserver (hpres n hn) hP (hdeg n hn)

/-- Sequence wrapper using per-row Jensen-pencil certificates. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_jensenPencil
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence hbase hdeg
    (BidiagonalJensenPencilCertificate.toPFPreserver_sequence hcert) hrec

/-- Tail-start sequence wrapper using per-row Jensen-pencil certificates. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_jensenPencil_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_from N hbase hdeg
    (BidiagonalJensenPencilCertificate.toPFPreserver_sequence_from
       N hcert) hrec

/-- Sequence wrapper using bundled cubic-residual certificates as row hints. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence hbase hdeg
    (BidiagonalCubicResidualCertificate.toPFPreserver_sequence hcert) hrec

/-- Tail-start sequence wrapper using bundled cubic-residual certificates as
row hints. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_from N hbase hdeg
    (BidiagonalCubicResidualCertificate.toPFPreserver_sequence_from
       N hcert) hrec

/-- Sequence wrapper for Family H-style second-derivative recurrences with an
explicit per-row PF-bidiagonal preserver.

This is the lightweight tactic surface: once a recurrence has been normalized
to the six-parameter differential form, a backend only has to prove the
coefficient-bidiagonal preserver for the corresponding `alpha` and `beta`
sequences. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat,
      BidiagonalPFPreserver
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence hbase hdeg hpres
    (fun n => (hrec n).trans
      (secondDerivativeBidiagonalForm_eq_bidiagonalOperator
        (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)))

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence`. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_from
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, N ≤ n →
      BidiagonalPFPreserver
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_from N hbase hdeg hpres
    (fun n hn => (hrec n hn).trans
      (secondDerivativeBidiagonalForm_eq_bidiagonalOperator
        (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)))

/-- Sequence wrapper for second-derivative recurrences whose preserver is
stated using named coefficient-bidiagonal functions. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat,
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence hbase hdeg hpres
    (fun n => (hrec n).trans (hnorm n))

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm`. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, N ≤ n →
      BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat, N ≤ n →
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_from N hbase hdeg hpres
    (fun n hn => (hrec n hn).trans (hnorm n hn))

/-- Sequence wrapper for Family H-style second-derivative recurrences using
per-row Jensen-pencil certificates. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalJensenPencilCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence hbase hdeg
    (BidiagonalJensenPencilCertificate.toPFPreserver_sequence hcert) hrec

/-- Tail-start second-derivative wrapper using per-row Jensen-pencil
certificates for the canonical coefficient functions. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_from
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalJensenPencilCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_from N hbase hdeg
    (BidiagonalJensenPencilCertificate.toPFPreserver_sequence_from
       N hcert) hrec

/-- Sequence wrapper for second-derivative recurrences whose Jensen
certificates are attached to named coefficient-bidiagonal functions. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_norm
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat,
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm hbase hdeg
    (BidiagonalJensenPencilCertificate.toPFPreserver_sequence hcert)
    hnorm hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_norm`. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_norm_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat, N ≤ n →
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm_from N hbase hdeg
    (BidiagonalJensenPencilCertificate.toPFPreserver_sequence_from
       N hcert) hnorm hrec

/-- Sequence wrapper for second-derivative PF-bidiagonal recurrences using
bundled cubic-residual certificates as row hints. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidualCertificate
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence hbase hdeg
    (BidiagonalCubicResidualCertificate.toPFPreserver_sequence hcert) hrec

/-- Tail-start second-derivative wrapper using bundled cubic-residual
certificates attached to the canonical coefficient functions. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidualCertificate_from
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_from N hbase hdeg
    (BidiagonalCubicResidualCertificate.toPFPreserver_sequence_from
       N hcert) hrec

/-- Short compatibility spelling for the bundled cubic-residual version of the
second-derivative PF-bidiagonal sequence wrapper. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidualCertificate
     hbase hdeg hcert hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert`.

This is the direct version for certificates attached to the canonical
quadratic coefficient functions of the second-derivative form. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_from
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidualCertificate_from
     N hbase hdeg hcert hrec

/-- Sequence wrapper for second-derivative recurrences whose certificate is
stated using named coefficient-bidiagonal functions.

This is useful for promoted sequence shells: the recurrence is often recorded
in differential form, while the generated Jensen/cubic certificate is attached
to named `alpha` and `beta` coefficient functions. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat,
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm hbase hdeg
    (BidiagonalCubicResidualCertificate.toPFPreserver_sequence hcert)
    hnorm hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm`.

This is useful for `n`-dependent coefficient-bidiagonal certificates whose
common Jensen factor only has the stable residual shape from a cutoff row
onward. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat, N ≤ n →
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm_from N hbase hdeg
    (BidiagonalCubicResidualCertificate.toPFPreserver_sequence_from
       N hcert) hnorm hrec

/-- Sequence wrapper whose per-row Jensen-pencil certificates are supplied by
common-factor residual cubic certificates. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidual
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hpencil : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil (alpha n) (beta n) (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * S n lam)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (S n lam))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate
     hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_cubicResidual
      halpha hbeta hpencil hA hB hS)
    hrec

/-- Tail-start version of
`isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidual`. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidual_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat, N ≤ n →
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat, N ≤ n →
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hpencil : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil (alpha n) (beta n) (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * S n lam)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (S n lam))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate_from
     N hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_cubicResidual_from
      N halpha hbeta hpencil hA hB hS)
    hrec

/-- Sequence wrapper whose residual pencil is derived from the endpoint
factorizations as `A n + C lam * B n`. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_endpoint_cubicResidual
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate
     hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual
      halpha hbeta hA hB hS)
    hrec

/-- Tail-start version of
`isPFPolynomial_of_bidiagonalOperator_sequence_of_endpoint_cubicResidual`. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_endpoint_cubicResidual_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat, N ≤ n →
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat, N ≤ n →
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate_from
     N hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual_from
      N halpha hbeta hA hB hS)
    hrec

/-- Sequence wrapper for Family H-style second-derivative recurrences.

The recurrence is supplied in differential form using
`secondDerivativeBidiagonalForm`; this theorem normalizes it to
`bidiagonalOperator` and then applies the Jensen-pencil/cubic-residual PF
sequence wrapper. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hpencil : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil
          (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
          (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
          (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * S n lam)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (S n lam))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert
     hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_cubicResidual
      halpha hbeta hpencil hA hB hS)
    hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual`. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual_from
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat, N ≤ n →
      jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat, N ≤ n →
      X * jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hpencil : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil
          (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
          (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
          (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * S n lam)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (S n lam))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_from
     N hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_cubicResidual_from
      N halpha hbeta hpencil hA hB hS)
    hrec

/-- Second-derivative sequence wrapper whose residual pencil is derived from
the endpoint factorizations as `A n + C lam * B n`. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert
     hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual
      halpha hbeta hA hB hS)
    hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual`. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual_from
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat, N ≤ n →
      jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat, N ≤ n →
      X * jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_from
     N hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual_from
      N halpha hbeta hA hB hS)
    hrec

/-- Second-derivative sequence wrapper using the quadratic Jensen
factorization of the canonical coefficient functions.

This is the Family H route when each row supplies only the active degree
condition `2 ≤ d n` and cubic certificates for the quadratic residual pencil. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_quadraticCubicResidual
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate
      (quadraticJensenResidual (c2 n) (b1 n - c2 n) (a0 n) (d n)))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate
      (X * quadraticJensenResidual (c3 n) (b2 n - c3 n) (a1 n) (d n)))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual
          (c2 n) (b1 n - c2 n) (a0 n)
          (c3 n) (b2 n - c3 n) (a1 n) lam (d n)))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert
     hbase hdeg
    (secondDerivativeBidiagonalCubicResidualCertificate_sequence
      hd hA hB hS)
    hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_quadraticCubicResidual`. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_quadraticCubicResidual_from
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, N ≤ n → 2 ≤ d n)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate
      (quadraticJensenResidual (c2 n) (b1 n - c2 n) (a0 n) (d n)))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate
      (X * quadraticJensenResidual (c3 n) (b2 n - c3 n) (a1 n) (d n)))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual
          (c2 n) (b1 n - c2 n) (a0 n)
          (c3 n) (b2 n - c3 n) (a1 n) lam (d n)))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_from
     N hbase hdeg
    (secondDerivativeBidiagonalCubicResidualCertificate_sequence_from
      N hd hA hB hS)
    hrec

/-- Sequence wrapper for second-derivative recurrences with unbundled
common-factor residual cubic certificates attached to named coefficient
bidiagonal functions. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual_norm
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hpencil : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil (alpha n) (beta n) (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * S n lam)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (S n lam))
    (hnorm : ∀ n : Nat,
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm
     hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_cubicResidual
      halpha hbeta hpencil hA hB hS)
    hnorm hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual_norm`. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual_norm_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat, N ≤ n →
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat, N ≤ n →
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hpencil : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil (alpha n) (beta n) (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * S n lam)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (S n lam))
    (hnorm : ∀ n : Nat, N ≤ n →
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm_from
     N hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_cubicResidual_from
      N halpha hbeta hpencil hA hB hS)
    hnorm hrec

/-- Normalized second-derivative sequence wrapper whose residual pencil is
derived from the endpoint factorizations as `A n + C lam * B n`. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual_norm
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n))
    (hnorm : ∀ n : Nat,
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm
     hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual
      halpha hbeta hA hB hS)
    hnorm hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual_norm`. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual_norm_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat, N ≤ n →
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat, N ≤ n →
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n))
    (hnorm : ∀ n : Nat, N ≤ n →
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm_from
     N hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual_from
      N halpha hbeta hA hB hS)
    hnorm hrec


end RealRooted
