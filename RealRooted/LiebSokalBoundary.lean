import RealRooted.BoundarySpecializationGeneral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Real boundary consequences of the Lieb--Sokal operator

This module transports the checked complex `1 - ∂ᵢ` stability theorem to real
coefficients, composes finite operator lists with real boundary specialization,
and records a degree-two mixed-characteristic-shaped example. It does not use
or assert an MSS root bound.
-/

open Complex

namespace RealRooted

noncomputable section

/-- Complexification commutes with one application of `1 - ∂ᵢ`. -/
@[simp] theorem complexifyMv_oneSubPderiv {sigma : Type*}
    (i : sigma) (P : MvPolynomial sigma ℝ) :
    complexifyMv (oneSubPderiv i P) =
      oneSubPderiv i (complexifyMv P) := by
  simp [complexifyMv, oneSubPderiv, MvPolynomial.pderiv_map]

/-- Complexification commutes with an ordered list of `1 - ∂ᵢ` operators. -/
@[simp] theorem complexifyMv_oneSubPderivList {sigma : Type*}
    (l : List sigma) (P : MvPolynomial sigma ℝ) :
    complexifyMv (oneSubPderivList l P) =
      oneSubPderivList l (complexifyMv P) := by
  induction l generalizing P with
  | nil => rfl
  | cons i l ih =>
      rw [oneSubPderivList_cons, oneSubPderivList_cons, ih,
        complexifyMv_oneSubPderiv]

/-- Complexification commutes with ordered scalar specialization. -/
@[simp] theorem complexifyMv_specializeAtList {sigma : Type*}
    (c : sigma → ℝ) (l : List sigma) (P : MvPolynomial sigma ℝ) :
    complexifyMv (MvPolynomial.specializeAtList c l P) =
      MvPolynomial.specializeAtList (fun i => (c i : ℂ)) l
        (complexifyMv P) := by
  exact MvPolynomial.map_specializeAtList Complex.ofRealHom c l P

/-- Strict upper-half-plane stability is preserved by an ordered list of
`1 - ∂ᵢ` operators. -/
theorem MvUpperHalfPlaneStable.oneSubPderivList
    {sigma : Type*} {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P) (l : List sigma) :
    MvUpperHalfPlaneStable (oneSubPderivList l P) := by
  induction l generalizing P with
  | nil => exact hP
  | cons i l ih => exact ih (hP.oneSubPderiv i)

/-- The real `1 - ∂ᵢ` operator preserves real stability in arbitrary coordinate
degree. -/
theorem MvRealStable.oneSubPderiv {sigma : Type*}
    {P : MvPolynomial sigma ℝ} (hP : MvRealStable P) (i : sigma) :
    MvRealStable (oneSubPderiv i P) := by
  unfold MvRealStable at hP ⊢
  rw [complexifyMv_oneSubPderiv]
  exact hP.oneSubPderiv i

/-- Ordered finite iteration of the real `1 - ∂ᵢ` operator preserves real
stability. Repeated coordinates are allowed. -/
theorem MvRealStable.oneSubPderivList {sigma : Type*}
    {P : MvPolynomial sigma ℝ} (hP : MvRealStable P) (l : List sigma) :
    MvRealStable (oneSubPderivList l P) := by
  unfold MvRealStable at hP ⊢
  rw [complexifyMv_oneSubPderivList]
  exact hP.oneSubPderivList l

/-- Real stability is preserved, up to the zero polynomial, by specializing an
ordered list of coordinates at real values. -/
theorem MvRealStable.specializeAtList_zero_or_general
    {sigma : Type*} {P : MvPolynomial sigma ℝ}
    (hP : MvRealStable P) (c : sigma → ℝ) (l : List sigma) :
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

/-- Applying an ordered operator list and then specializing coordinates at
real values preserves real stability up to the zero polynomial. -/
theorem MvRealStable.oneSubPderivList_specializeAtList_zero_or_general
    {sigma : Type*} {P : MvPolynomial sigma ℝ}
    (hP : MvRealStable P) (operators : List sigma)
    (c : sigma → ℝ) (coordinates : List sigma) :
    MvPolynomial.specializeAtList c coordinates
        (_root_.RealRooted.oneSubPderivList operators P) = 0 ∨
      MvRealStable
        (MvPolynomial.specializeAtList c coordinates
          (_root_.RealRooted.oneSubPderivList operators P)) :=
  (MvRealStable.oneSubPderivList hP operators).specializeAtList_zero_or_general
    c coordinates

/-- Applying an ordered operator list and then specializing coordinates to zero
preserves complex upper-half-plane stability up to the zero polynomial. -/
theorem MvUpperHalfPlaneStable.oneSubPderivList_specializeZeroList_zero_or_general
    {sigma : Type*} {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P) (operators coordinates : List sigma) :
    MvUpperHalfPlaneStableOrZero
      (specializeZeroList coordinates
        (_root_.RealRooted.oneSubPderivList operators P)) :=
  (MvUpperHalfPlaneStable.oneSubPderivList hP operators)
    |>.specializeZeroList_zero_or_general coordinates

section MixedCharacteristicExample

/-- A degree-two mixed-characteristic-shaped input in an output variable and
two auxiliary variables. -/
def mixedCharacteristicQuadratic : MvPolynomial (Fin 3) ℝ :=
  (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2) ^ 2

/-- The degree-two mixed-characteristic-shaped input is real stable. -/
theorem mvRealStable_mixedCharacteristicQuadratic :
    MvRealStable mixedCharacteristicQuadratic := by
  have hlinear : MvUpperHalfPlaneStable
      (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 :
        MvPolynomial (Fin 3) ℂ) := by
    intro z hz hzero
    have hz0 : 0 < (z 0).im := hz 0
    have hz1 : 0 < (z 1).im := hz 1
    have hz2 : 0 < (z 2).im := hz 2
    have him : (z 0).im + (z 1).im + (z 2).im = 0 := by
      simpa using congrArg Complex.im hzero
    linarith
  simpa [MvRealStable, complexifyMv, mixedCharacteristicQuadratic, pow_two] using
    hlinear.mul hlinear

/-- Applying `1 - ∂ᵧ` and `1 - ∂z` produces the expected quadratic. -/
theorem oneSubPderivList_mixedCharacteristicQuadratic :
    _root_.RealRooted.oneSubPderivList [1, 2]
        mixedCharacteristicQuadratic =
      (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2) ^ 2 -
        MvPolynomial.C 4 *
          (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2) +
        MvPolynomial.C 2 := by
  let S : MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2
  have hdy : MvPolynomial.pderiv 1 S = 1 := by
    simp [S, MvPolynomial.pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 1),
      MvPolynomial.pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 1)]
  have hdz : MvPolynomial.pderiv 2 S = 1 := by
    simp [S, MvPolynomial.pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 2),
      MvPolynomial.pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 2)]
  have hdc : MvPolynomial.pderiv (2 : Fin 3)
      (2 : MvPolynomial (Fin 3) ℝ) = 0 := by
    change MvPolynomial.pderiv 2 (MvPolynomial.C 2) = 0
    exact MvPolynomial.pderiv_C
  have hfirst : MvPolynomial.pderiv 1 (S ^ 2) = 2 * S := by
    rw [MvPolynomial.pderiv_pow, hdy]
    norm_num
  have hsecond : MvPolynomial.pderiv 2 (S ^ 2 - 2 * S) = 2 * S - 2 := by
    rw [map_sub, MvPolynomial.pderiv_pow, hdz, MvPolynomial.pderiv_mul,
      hdc, hdz]
    norm_num
  change oneSubPderiv 2 (oneSubPderiv 1 (S ^ 2)) =
    S ^ 2 - MvPolynomial.C 4 * S + MvPolynomial.C 2
  rw [show oneSubPderiv 1 (S ^ 2) = S ^ 2 - 2 * S by
    rw [oneSubPderiv, hfirst]]
  rw [oneSubPderiv, hsecond]
  rw [_root_.map_ofNat
      (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 3) ℝ) 2,
    _root_.map_ofNat
      (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 3) ℝ) 4]
  ring

/-- Specializing the two auxiliary variables to zero yields
`t² - 4t + 2`. -/
theorem specialize_mixedCharacteristicQuadratic :
    MvPolynomial.specializeAtList (fun _ => 0) [1, 2]
        (_root_.RealRooted.oneSubPderivList [1, 2]
          mixedCharacteristicQuadratic) =
      MvPolynomial.X 0 ^ 2 - MvPolynomial.C 4 * MvPolynomial.X 0 +
        MvPolynomial.C 2 := by
  rw [oneSubPderivList_mixedCharacteristicQuadratic]
  simp [MvPolynomial.specializeAtList,
    (by decide : (0 : Fin 3) ≠ 1), (by decide : (0 : Fin 3) ≠ 2),
    (by decide : (2 : Fin 3) ≠ 1)]

/-- The specialized degree-two example is real stable, obtained without an
MSS barrier estimate. -/
theorem mvRealStable_specialized_mixedCharacteristicQuadratic :
    MvRealStable
      (MvPolynomial.X 0 ^ 2 - MvPolynomial.C 4 * MvPolynomial.X 0 +
        MvPolynomial.C 2 : MvPolynomial (Fin 3) ℝ) := by
  have hzero_or :=
    mvRealStable_mixedCharacteristicQuadratic
      |>.oneSubPderivList_specializeAtList_zero_or_general
        [1, 2] (fun _ => 0) [1, 2]
  rw [specialize_mixedCharacteristicQuadratic] at hzero_or
  exact hzero_or.resolve_left (by
    intro hzero
    have heval := congrArg
      (MvPolynomial.eval (fun _ : Fin 3 => 0)) hzero
    norm_num at heval)

end MixedCharacteristicExample

end

end RealRooted
