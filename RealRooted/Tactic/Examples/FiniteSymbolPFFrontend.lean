import RealRooted.Tactic.FiniteSymbolPFFrontend

open Polynomial

namespace RealRooted
namespace Tactic
namespace FiniteSymbolPF


example {alpha beta : ℕ → ℝ} {d : ℕ}
    (hBB : finiteSymbolBBStatement)
    (hstab : IsBivariateUpperStable (complexifyMv (finiteSymbol alpha beta d)))
    (halpha : ∀ n, 0 ≤ alpha n)
    (hbeta : ∀ n, 0 ≤ beta n) :
    BidiagonalPFPreserver alpha beta d := by
  rr_fsp_finite_symbol_backend using
    bb_backend := hBB,
    stable := hstab,
    alpha_nonneg := halpha,
    beta_nonneg := hbeta

example {alpha beta : ℕ → ℝ} {d : ℕ} {residual : ℝ[X]}
    (hmul : bivariateStableMulXAddYPowStatement)
    (hfac : complexifyMv (finiteSymbol alpha beta d) =
      ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ (d - 2)) *
        complexifyMv (homogenizeBivariate residual.natDegree residual))
    (hres : IsBivariateUpperStable
      (complexifyMv (homogenizeBivariate residual.natDegree residual))) :
    IsBivariateUpperStable (complexifyMv (finiteSymbol alpha beta d)) := by
  rr_fsp_stable_of_residual_factor using
    mul_stable := hmul,
    factor := hfac,
    residual_stable := hres

example {alpha beta : ℕ → ℝ} {d : ℕ}
    (hhom : homogenizeStableStatement)
    (hmul : bivariateStableMulXAddYPowStatement)
    (cert : BidiagonalCubicResidualCertificate alpha beta d) :
    IsBivariateUpperStable (complexifyMv (finiteSymbol alpha beta d)) := by
  rr_fsp_stable_of_residual_certificate using
    homogenize_stable := hhom,
    mul_stable := hmul,
    certificate := cert

example {alpha beta : ℕ → ℝ} {d : ℕ}
    (hBB : finiteSymbolBBStatement)
    (hhom : homogenizeStableStatement)
    (hmul : bivariateStableMulXAddYPowStatement)
    (cert : BidiagonalCubicResidualCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d := by
  rr_fsp_preserver_of_residual_certificate using
    bb_backend := hBB,
    homogenize_stable := hhom,
    mul_stable := hmul,
    certificate := cert

example (hBB : finiteSymbolBBStatement)
    (hhom : homogenizeStableStatement)
    (hmul : bivariateStableMulXAddYPowStatement)
    (aa ab ac ba bb bc : ℝ) {d : ℕ} (hd : 2 ≤ d)
    (hdeg : (quadraticBidiagonalResidual aa ab ac ba bb bc d).natDegree = 3)
    (hpf : IsPFPolynomial (quadraticBidiagonalResidual aa ab ac ba bb bc d))
    (halpha : ∀ n, 0 ≤ quadraticJensenWeight aa ab ac n)
    (hbeta : ∀ n, 0 ≤ quadraticJensenWeight ba bb bc n) :
    BidiagonalPFPreserver
      (quadraticJensenWeight aa ab ac)
      (quadraticJensenWeight ba bb bc) d := by
  rr_fsp_quadratic_preserver using
    bb_backend := hBB,
    homogenize_stable := hhom,
    mul_stable := hmul,
    degree_ge_two := hd,
    cubic_degree := hdeg,
    residual_pf := hpf,
    alpha_nonneg := halpha,
    beta_nonneg := hbeta

example (hBB : finiteSymbolBBStatement)
    (hhom : homogenizeStableStatement)
    (hmul : bivariateStableMulXAddYPowStatement)
    (a0 a1 b1 b2 c2 : ℝ) {d : ℕ} (hd : 2 ≤ d)
    (hdeg : (quadraticBidiagonalResidual
      c2 (b1 - c2) a0 0 b2 a1 d).natDegree = 3)
    (hpf : IsPFPolynomial
      (quadraticBidiagonalResidual c2 (b1 - c2) a0 0 b2 a1 d))
    (halpha : ∀ n, 0 ≤ secondDerivativeAlpha a0 b1 c2 n)
    (hbeta : ∀ n, 0 ≤ secondDerivativeBeta a1 b2 n) :
    BidiagonalPFPreserver
      (secondDerivativeAlpha a0 b1 c2)
      (secondDerivativeBeta a1 b2) d := by
  rr_fsp_second_derivative_preserver using
    bb_backend := hBB,
    homogenize_stable := hhom,
    mul_stable := hmul,
    degree_ge_two := hd,
    cubic_degree := hdeg,
    residual_pf := hpf,
    alpha_nonneg := halpha,
    beta_nonneg := hbeta

example (hBB : finiteSymbolBBStatement)
    (hhom : homogenizeStableStatement)
    (hmul : bivariateStableMulXAddYPowStatement)
    (a0 a1 b1 b2 c2 : ℝ) {d : ℕ} (hd : 2 ≤ d)
    (hdeg : (quadraticBidiagonalResidual
      c2 (b1 - c2) a0 0 b2 a1 d).natDegree = 3)
    (hpf : IsPFPolynomial
      (quadraticBidiagonalResidual c2 (b1 - c2) a0 0 b2 a1 d))
    (halpha : ∀ n, n ≤ d → 0 ≤ secondDerivativeAlpha a0 b1 c2 n)
    (hbeta : ∀ n, n ≤ d → 0 ≤ secondDerivativeBeta a1 b2 n) :
    BidiagonalPFPreserver
      (secondDerivativeAlpha a0 b1 c2)
      (secondDerivativeBeta a1 b2) d := by
  rr_fsp_second_derivative_preserver_on_degree using
    bb_backend := hBB,
    homogenize_stable := hhom,
    mul_stable := hmul,
    degree_ge_two := hd,
    cubic_degree := hdeg,
    residual_pf := hpf,
    alpha_nonneg := halpha,
    beta_nonneg := hbeta

example (hBB : finiteSymbolBBStatement)
    (hhom : homogenizeStableStatement)
    (hmul : bivariateStableMulXAddYPowStatement)
    (a0 a1 b1 b2 c3 : ℝ) {d : ℕ} (hd : 2 ≤ d)
    (hdeg : (quadraticBidiagonalResidual
      0 b1 a0 c3 (b2 - c3) a1 d).natDegree = 3)
    (hpf : IsPFPolynomial
      (quadraticBidiagonalResidual 0 b1 a0 c3 (b2 - c3) a1 d))
    (halpha : ∀ n, 0 ≤ shiftedSecondDerivativeAlpha a0 b1 n)
    (hbeta : ∀ n, 0 ≤ shiftedSecondDerivativeBeta a1 b2 c3 n) :
    BidiagonalPFPreserver
      (shiftedSecondDerivativeAlpha a0 b1)
      (shiftedSecondDerivativeBeta a1 b2 c3) d := by
  rr_fsp_shifted_second_derivative_preserver using
    bb_backend := hBB,
    homogenize_stable := hhom,
    mul_stable := hmul,
    degree_ge_two := hd,
    cubic_degree := hdeg,
    residual_pf := hpf,
    alpha_nonneg := halpha,
    beta_nonneg := hbeta

example (hBB : finiteSymbolBBStatement)
    (hhom : homogenizeStableStatement)
    (hmul : bivariateStableMulXAddYPowStatement)
    {P : ℕ → ℝ[X]} {a0 a1 b1 b2 c2 : ℕ → ℝ}
    {degreeBound : ℕ → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdegree : ∀ n, (P n).natDegree ≤ degreeBound n)
    (hd : ∀ n, 2 ≤ degreeBound n)
    (hdeg : ∀ n,
      (quadraticBidiagonalResidual
        (c2 n) (b1 n - c2 n) (a0 n) 0 (b2 n) (a1 n)
        (degreeBound n)).natDegree = 3)
    (hpf : ∀ n,
      IsPFPolynomial
        (quadraticBidiagonalResidual
          (c2 n) (b1 n - c2 n) (a0 n) 0 (b2 n) (a1 n)
          (degreeBound n)))
    (halpha : ∀ n k, 0 ≤ secondDerivativeAlpha (a0 n) (b1 n) (c2 n) k)
    (hbeta : ∀ n k, 0 ≤ secondDerivativeBeta (a1 n) (b2 n) k)
    (hrec : ∀ n,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (P n)) :
    ∀ n, IsPFPolynomial (P n) := by
  rr_fsp_second_derivative_sequence using
    bb_backend := hBB,
    homogenize_stable := hhom,
    mul_stable := hmul,
    base := hbase,
    degree := hdegree,
    degree_ge_two := hd,
    cubic_degree := hdeg,
    residual_pf := hpf,
    alpha_nonneg := halpha,
    beta_nonneg := hbeta,
    recurrence := hrec

example (hBB : finiteSymbolBBStatement)
    (hhom : homogenizeStableStatement)
    (hmul : bivariateStableMulXAddYPowStatement)
    {P : ℕ → ℝ[X]} {a0 a1 b1 b2 c2 : ℕ → ℝ}
    {degreeBound : ℕ → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdegree : ∀ n, (P n).natDegree ≤ degreeBound n)
    (hd : ∀ n, 2 ≤ degreeBound n)
    (hdeg : ∀ n,
      (quadraticBidiagonalResidual
        (c2 n) (b1 n - c2 n) (a0 n) 0 (b2 n) (a1 n)
        (degreeBound n)).natDegree = 3)
    (hpf : ∀ n,
      IsPFPolynomial
        (quadraticBidiagonalResidual
          (c2 n) (b1 n - c2 n) (a0 n) 0 (b2 n) (a1 n)
          (degreeBound n)))
    (halpha : ∀ n k, 0 ≤ secondDerivativeAlpha (a0 n) (b1 n) (c2 n) k)
    (hbeta : ∀ n k, 0 ≤ secondDerivativeBeta (a1 n) (b2 n) k)
    (hne : ∀ n, P n ≠ 0)
    (hrec : ∀ n,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (P n)) :
    ∀ n, P n ≠ 0 ∧ (P n).Splits := by
  rr_fsp_second_derivative_sequence using
    bb_backend := hBB,
    homogenize_stable := hhom,
    mul_stable := hmul,
    base := hbase,
    degree := hdegree,
    degree_ge_two := hd,
    cubic_degree := hdeg,
    residual_pf := hpf,
    alpha_nonneg := halpha,
    beta_nonneg := hbeta,
    recurrence := hrec,
    nonzero := hne

example (hBB : finiteSymbolBBStatement)
    (hhom : homogenizeStableStatement)
    (hmul : bivariateStableMulXAddYPowStatement)
    {P : ℕ → ℝ[X]} {a0 a1 b1 b2 c2 : ℕ → ℝ}
    {degreeBound : ℕ → ℕ} (N : ℕ)
    (hbase : ∀ n, n ≤ N → IsPFPolynomial (P n))
    (hdegree : ∀ n, N ≤ n → (P n).natDegree ≤ degreeBound n)
    (hd : ∀ n, N ≤ n → 2 ≤ degreeBound n)
    (hdeg : ∀ n, N ≤ n →
      (quadraticBidiagonalResidual
        (c2 n) (b1 n - c2 n) (a0 n) 0 (b2 n) (a1 n)
        (degreeBound n)).natDegree = 3)
    (hpf : ∀ n, N ≤ n →
      IsPFPolynomial
        (quadraticBidiagonalResidual
          (c2 n) (b1 n - c2 n) (a0 n) 0 (b2 n) (a1 n)
          (degreeBound n)))
    (halpha : ∀ n k, N ≤ n → 0 ≤ secondDerivativeAlpha (a0 n) (b1 n) (c2 n) k)
    (hbeta : ∀ n k, N ≤ n → 0 ≤ secondDerivativeBeta (a1 n) (b2 n) k)
    (hne : ∀ n, P n ≠ 0)
    (hrec : ∀ n, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (P n)) :
    ∀ n, P n ≠ 0 ∧ (P n).Splits := by
  rr_fsp_second_derivative_sequence using
    bb_backend := hBB,
    homogenize_stable := hhom,
    mul_stable := hmul,
    cutoff := N,
    base := hbase,
    degree := hdegree,
    degree_ge_two := hd,
    cubic_degree := hdeg,
    residual_pf := hpf,
    alpha_nonneg := halpha,
    beta_nonneg := hbeta,
    recurrence := hrec,
    nonzero := hne

example (hBB : finiteSymbolBBStatement)
    (hhom : homogenizeStableStatement)
    (hmul : bivariateStableMulXAddYPowStatement)
    {P : ℕ → ℝ[X]} {a0 a1 b1 b2 c3 : ℕ → ℝ}
    {degreeBound : ℕ → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdegree : ∀ n, (P n).natDegree ≤ degreeBound n)
    (hd : ∀ n, 2 ≤ degreeBound n)
    (hdeg : ∀ n,
      (quadraticBidiagonalResidual
        0 (b1 n) (a0 n) (c3 n) (b2 n - c3 n) (a1 n)
        (degreeBound n)).natDegree = 3)
    (hpf : ∀ n,
      IsPFPolynomial
        (quadraticBidiagonalResidual
          0 (b1 n) (a0 n) (c3 n) (b2 n - c3 n) (a1 n)
          (degreeBound n)))
    (halpha : ∀ n k, 0 ≤ shiftedSecondDerivativeAlpha (a0 n) (b1 n) k)
    (hbeta : ∀ n k, 0 ≤ shiftedSecondDerivativeBeta (a1 n) (b2 n) (c3 n) k)
    (hrec : ∀ n,
      P (n + 1) =
        shiftedSecondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c3 n) (P n)) :
    ∀ n, IsPFPolynomial (P n) := by
  rr_fsp_shifted_second_derivative_sequence using
    bb_backend := hBB,
    homogenize_stable := hhom,
    mul_stable := hmul,
    base := hbase,
    degree := hdegree,
    degree_ge_two := hd,
    cubic_degree := hdeg,
    residual_pf := hpf,
    alpha_nonneg := halpha,
    beta_nonneg := hbeta,
    recurrence := hrec

example (hBB : finiteSymbolBBStatement)
    (hhom : homogenizeStableStatement)
    (hmul : bivariateStableMulXAddYPowStatement)
    {P : ℕ → ℝ[X]} {a0 a1 b1 b2 c3 : ℕ → ℝ}
    {degreeBound : ℕ → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdegree : ∀ n, (P n).natDegree ≤ degreeBound n)
    (hd : ∀ n, 2 ≤ degreeBound n)
    (hdeg : ∀ n,
      (quadraticBidiagonalResidual
        0 (b1 n) (a0 n) (c3 n) (b2 n - c3 n) (a1 n)
        (degreeBound n)).natDegree = 3)
    (hpf : ∀ n,
      IsPFPolynomial
        (quadraticBidiagonalResidual
          0 (b1 n) (a0 n) (c3 n) (b2 n - c3 n) (a1 n)
          (degreeBound n)))
    (halpha : ∀ n k, 0 ≤ shiftedSecondDerivativeAlpha (a0 n) (b1 n) k)
    (hbeta : ∀ n k, 0 ≤ shiftedSecondDerivativeBeta (a1 n) (b2 n) (c3 n) k)
    (hne : ∀ n, P n ≠ 0)
    (hrec : ∀ n,
      P (n + 1) =
        shiftedSecondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c3 n) (P n)) :
    ∀ n, P n ≠ 0 ∧ (P n).Splits := by
  rr_fsp_shifted_second_derivative_sequence using
    bb_backend := hBB,
    homogenize_stable := hhom,
    mul_stable := hmul,
    base := hbase,
    degree := hdegree,
    degree_ge_two := hd,
    cubic_degree := hdeg,
    residual_pf := hpf,
    alpha_nonneg := halpha,
    beta_nonneg := hbeta,
    recurrence := hrec,
    nonzero := hne

example (hBB : finiteSymbolBBStatement)
    (hhom : homogenizeStableStatement)
    (hmul : bivariateStableMulXAddYPowStatement)
    {P : ℕ → ℝ[X]} {a0 a1 b1 b2 c3 : ℕ → ℝ}
    {degreeBound : ℕ → ℕ} (N : ℕ)
    (hbase : ∀ n, n ≤ N → IsPFPolynomial (P n))
    (hdegree : ∀ n, N ≤ n → (P n).natDegree ≤ degreeBound n)
    (hd : ∀ n, N ≤ n → 2 ≤ degreeBound n)
    (hdeg : ∀ n, N ≤ n →
      (quadraticBidiagonalResidual
        0 (b1 n) (a0 n) (c3 n) (b2 n - c3 n) (a1 n)
        (degreeBound n)).natDegree = 3)
    (hpf : ∀ n, N ≤ n →
      IsPFPolynomial
        (quadraticBidiagonalResidual
          0 (b1 n) (a0 n) (c3 n) (b2 n - c3 n) (a1 n)
          (degreeBound n)))
    (halpha : ∀ n k, N ≤ n → 0 ≤ shiftedSecondDerivativeAlpha (a0 n) (b1 n) k)
    (hbeta : ∀ n k, N ≤ n →
      0 ≤ shiftedSecondDerivativeBeta (a1 n) (b2 n) (c3 n) k)
    (hne : ∀ n, P n ≠ 0)
    (hrec : ∀ n, N ≤ n →
      P (n + 1) =
        shiftedSecondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c3 n) (P n)) :
    ∀ n, P n ≠ 0 ∧ (P n).Splits := by
  rr_fsp_shifted_second_derivative_sequence using
    bb_backend := hBB,
    homogenize_stable := hhom,
    mul_stable := hmul,
    cutoff := N,
    base := hbase,
    degree := hdegree,
    degree_ge_two := hd,
    cubic_degree := hdeg,
    residual_pf := hpf,
    alpha_nonneg := halpha,
    beta_nonneg := hbeta,
    recurrence := hrec,
    nonzero := hne

end FiniteSymbolPF
end Tactic
end RealRooted
