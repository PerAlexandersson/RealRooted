import RealRooted.Tactic.FiniteSymbol

namespace RealRooted
namespace Tactic

example {sigma tau : Type*} [Fintype sigma]
    (T : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial tau ℂ)
    (hSymbol : MvUpperHalfPlaneStable
      (MvPolynomial.algebraicSymbol (fun _ : sigma => 1) T))
    (f : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1))
    (hf : MvUpperHalfPlaneStable f.1) :
    MvUpperHalfPlaneStableOrZero (T f) := by
  rr_finite_symbol_stable_or_zero using
    operator := T,
    symbol_stable := hSymbol,
    input := f,
    input_stable := hf

example {sigma tau : Type*} [Fintype sigma]
    (T : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial tau ℂ)
    (hSymbol : MvUpperHalfPlaneStable
      (MvPolynomial.algebraicSymbol (fun _ : sigma => 1) T))
    (f : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1))
    (hf : MvUpperHalfPlaneStable f.1) :
    MvUpperHalfPlaneStableOrZero (T f) := by
  rr_finite_symbol_stable_or_zero using
    symbol_stable := hSymbol,
    input_stable := hf

end Tactic
end RealRooted
