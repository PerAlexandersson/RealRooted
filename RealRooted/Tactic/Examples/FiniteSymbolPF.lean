import RealRooted.Tactic.FiniteSymbolPF

/-!
# Smoke examples for direct finite-symbol PF endpoints
-/

open Polynomial

namespace RealRooted
namespace Tactic
namespace FiniteSymbolPF

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
