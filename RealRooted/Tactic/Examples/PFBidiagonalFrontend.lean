import RealRooted.Tactic.PFBidiagonalFrontend

/-!
# Smoke examples for the legacy PF-bidiagonal frontend import
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

end FiniteSymbolPF
end Tactic
end RealRooted
