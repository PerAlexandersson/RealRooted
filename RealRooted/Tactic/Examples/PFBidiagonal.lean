import RealRooted.Tactic.PFBidiagonal

/-!
# PF-bidiagonal API smoke tests

These examples cover the checked affine-symbol route, the Jensen-pencil
preserver, and the generic recurrence induction wrapper.
-/

open Polynomial

namespace RealRooted

example {alpha beta : ℕ → ℝ} {d : ℕ}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (RealRooted.BorceaBranden.finiteAlgebraicSymbol d
          (BorceaBranden.bidiagonalLinearMap alpha beta))))
    (halpha : ∀ k, k ≤ d → 0 ≤ alpha k)
    (hbeta : ∀ k, k ≤ d → 0 ≤ beta k) :
    BidiagonalPFPreserver alpha beta d :=
  bidiagonalPFPreserver_of_affineSymbol hSymbol halpha hbeta

example {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  hcert.toPFPreserver

example {P : ℕ → ℝ[X]} {alpha beta : ℕ → ℕ → ℝ} {d : ℕ → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n, (P n).natDegree ≤ d n)
    (hpres : ∀ n, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hrec : ∀ n, P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence hbase hdeg hpres hrec

end RealRooted
