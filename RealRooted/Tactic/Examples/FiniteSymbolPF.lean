import RealRooted.Tactic.FiniteSymbolPF

/-!
# Smoke examples for direct finite-symbol PF endpoints
-/

open Polynomial

namespace RealRooted
namespace Tactic
namespace FiniteSymbolPF

example {alpha beta : ℕ → ℝ} {d : ℕ}
    (hBB : finiteSymbolBBStatement)
    (hstable : IsBivariateUpperStable (complexifyMv (finiteSymbol alpha beta d)))
    (halpha : ∀ n, 0 ≤ alpha n)
    (hbeta : ∀ n, 0 ≤ beta n) :
    BidiagonalPFPreserver alpha beta d :=
  finite_symbol_pf_bidiagonal_backend hBB hstable halpha hbeta

example {alpha beta : ℕ → ℝ} {d : ℕ}
    (hBB : finiteSymbolBBStatement)
    (hhom : homogenizeStableStatement)
    (cert : BidiagonalCubicResidualCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  bidiagonalPFPreserver_of_finiteSymbol_residual_certificate
    hBB hhom cert

example {P : ℕ → ℝ[X]} {alpha beta : ℕ → ℕ → ℝ}
    {degreeBound : ℕ → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdegree : ∀ n, (P n).natDegree ≤ degreeBound n)
    (hpres : ∀ n, BidiagonalPFPreserver (alpha n) (beta n) (degreeBound n))
    (hrec : ∀ n, P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence hbase hdegree hpres hrec

example {P : ℕ → ℝ[X]} {alpha beta : ℕ → ℕ → ℝ}
    {degreeBound : ℕ → ℕ} (N : ℕ)
    (hbase : ∀ n, n ≤ N → IsPFPolynomial (P n))
    (hdegree : ∀ n, N ≤ n → (P n).natDegree ≤ degreeBound n)
    (hpres : ∀ n, N ≤ n →
      BidiagonalPFPreserver (alpha n) (beta n) (degreeBound n))
    (hrec : ∀ n, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_from
    N hbase hdegree hpres hrec

end FiniteSymbolPF
end Tactic
end RealRooted
