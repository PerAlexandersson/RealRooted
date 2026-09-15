import RealRooted.BoundarySpecializationGeneral

/-!
# Real boundary specialization

This file transfers the general complex boundary-specialization theorem to
multivariate polynomials with real coefficients.  Specializing real values may
annihilate the polynomial, so the natural conclusion is stability or zero.
-/

namespace RealRooted

noncomputable section

/-- Complexification commutes with specialization of one coordinate at a real
value. -/
@[simp] theorem complexifyMv_specializeAt {σ : Type*}
    (i : σ) (c : ℝ) (P : MvPolynomial σ ℝ) :
    complexifyMv (MvPolynomial.specializeAt i c P) =
      MvPolynomial.specializeAt i (c : ℂ) (complexifyMv P) := by
  exact MvPolynomial.map_specializeAt Complex.ofRealHom i c P

/-- Complexification commutes with ordered specialization at real values. -/
@[simp] theorem complexifyMv_specializeAtList {σ : Type*}
    (c : σ → ℝ) (l : List σ) (P : MvPolynomial σ ℝ) :
    complexifyMv (MvPolynomial.specializeAtList c l P) =
      MvPolynomial.specializeAtList (fun i => (c i : ℂ)) l
        (complexifyMv P) := by
  exact MvPolynomial.map_specializeAtList Complex.ofRealHom c l P

/-- Real stability is preserved, up to the zero polynomial, by specializing an
ordered list of coordinates at real values.  Repeated coordinates are allowed. -/
theorem MvRealStable.specializeAtList_zero_or_general
    {σ : Type*} {P : MvPolynomial σ ℝ} (hP : MvRealStable P)
    (c : σ → ℝ) (l : List σ) :
    MvPolynomial.specializeAtList c l P = 0 ∨
      MvRealStable (MvPolynomial.specializeAtList c l P) := by
  unfold MvRealStable at hP ⊢
  have hcomplex := hP.orZero.specializeAtList_real_general c l
  rw [← complexifyMv_specializeAtList] at hcomplex
  rcases hcomplex with hzero | hstable
  · left
    exact MvPolynomial.map_injective Complex.ofRealHom
      Complex.ofRealHom.injective hzero
  · exact Or.inr hstable

/-- Real stability is preserved, up to the zero polynomial, by specializing
one coordinate at a real value. -/
theorem MvRealStable.specializeAt_zero_or_general
    {σ : Type*} {P : MvPolynomial σ ℝ} (hP : MvRealStable P)
    (i : σ) (c : ℝ) :
    MvPolynomial.specializeAt i c P = 0 ∨
      MvRealStable (MvPolynomial.specializeAt i c P) := by
  simpa using hP.specializeAtList_zero_or_general (fun _ => c) [i]

/-- Weak real stability is preserved by specializing an ordered list of
coordinates at real values. -/
theorem MvRealStableOrZero.specializeAtList_general
    {σ : Type*} {P : MvPolynomial σ ℝ} (hP : MvRealStableOrZero P)
    (c : σ → ℝ) (l : List σ) :
    MvRealStableOrZero (MvPolynomial.specializeAtList c l P) := by
  rcases hP with rfl | hP
  · simpa using (MvRealStableOrZero.zero (sigma := σ))
  · exact hP.specializeAtList_zero_or_general c l

/-- Weak real stability is preserved by specializing one coordinate at a real
value. -/
theorem MvRealStableOrZero.specializeAt_general
    {σ : Type*} {P : MvPolynomial σ ℝ} (hP : MvRealStableOrZero P)
    (i : σ) (c : ℝ) :
    MvRealStableOrZero (MvPolynomial.specializeAt i c P) := by
  simpa using hP.specializeAtList_general (fun _ => c) [i]

end

end RealRooted
