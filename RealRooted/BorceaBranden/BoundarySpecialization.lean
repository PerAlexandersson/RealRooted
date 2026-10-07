import RealRooted.LiebSokalPointwise
import RealRooted.MultivariateStability

/-!
# Boundary specialization for finite variable blocks

This module packages the repeated boundary-specialization step used in the
proof of Borcea--Branden, Lemma 2.2.  A multiaffine stable polynomial remains
stable or becomes zero after a finite block of variables is specialized to
zero.
-/

open Complex

namespace RealRooted

noncomputable section

/-- Successively specialize the variables in `l` to zero. -/
def specializeZeroList {sigma : Type*} (l : List sigma)
    (P : MvPolynomial sigma ℂ) : MvPolynomial sigma ℂ :=
  l.foldl (fun Q i => MvPolynomial.specializeZero i Q) P

@[simp]
theorem specializeZeroList_nil {sigma : Type*} (P : MvPolynomial sigma ℂ) :
    specializeZeroList [] P = P :=
  rfl

@[simp]
theorem specializeZeroList_cons {sigma : Type*} (i : sigma) (l : List sigma)
    (P : MvPolynomial sigma ℂ) :
    specializeZeroList (i :: l) P =
      specializeZeroList l (MvPolynomial.specializeZero i P) :=
  rfl

@[simp]
theorem specializeZeroList_zero {sigma : Type*} (l : List sigma) :
    specializeZeroList l (0 : MvPolynomial sigma ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [specializeZeroList_cons, ih]

/-- Evaluation after a list of zero specializations. -/
theorem eval_specializeZeroList {sigma : Type*} [DecidableEq sigma]
    (l : List sigma)
    (P : MvPolynomial sigma ℂ) (z : sigma → ℂ) :
    MvPolynomial.eval z (specializeZeroList l P) =
      MvPolynomial.eval (fun i => if i ∈ l then 0 else z i) P := by
  classical
  induction l generalizing P with
  | nil => simp
  | cons i l ih =>
      rw [specializeZeroList_cons, ih, MvPolynomial.eval_specializeZero]
      apply congrArg (fun w : sigma → ℂ => MvPolynomial.eval w P)
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]

/-- Repeated zero specialization preserves multiaffineness. -/
theorem MvPolynomial.IsMultiaffine.specializeZeroList_preserves
    {sigma : Type*} {P : MvPolynomial sigma ℂ}
    (hP : MvPolynomial.IsMultiaffine P) (l : List sigma) :
    MvPolynomial.IsMultiaffine (specializeZeroList l P) := by
  induction l generalizing P with
  | nil => exact hP
  | cons i l ih =>
      exact ih (hP.specializeZero_preserves i)

/-- Repeated specialization at zero preserves upper-half-plane stability, up
to the zero polynomial. -/
theorem MvUpperHalfPlaneStable.specializeZeroList_zero_or
    {sigma : Type*} [Finite sigma] {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P) (hPma : MvPolynomial.IsMultiaffine P)
    (l : List sigma) :
    specializeZeroList l P = 0 ∨
      MvUpperHalfPlaneStable (specializeZeroList l P) := by
  induction l generalizing P with
  | nil => exact Or.inr hP
  | cons i l ih =>
      rcases hP.specializeZero_zero_or hPma i with hzero | hstable
      · left
        simp [specializeZeroList_cons, hzero]
      · exact ih hstable (hPma.specializeZero_preserves i)

/-- Block specialization from list specialization: if zero-specializing the variables in `l`,
which are exactly the right-block variables, gives a stable or zero polynomial, then so does
specializing the whole right block at zero. -/
theorem MvUpperHalfPlaneStableOrZero.specializeRight_zero_of_specializeZeroList
    {tau sigma : Type*} {P : MvPolynomial (Sum tau sigma) ℂ} (l : List (Sum tau sigma))
    (hl : ∀ j, j ∈ l ↔ j.isRight = true)
    (hQ : MvUpperHalfPlaneStableOrZero (specializeZeroList l P)) :
    MvUpperHalfPlaneStableOrZero
      (_root_.RealRooted.specializeRight (fun _ : sigma => 0) P) := by
  classical
  have hQeval (x : tau → ℂ) (y : sigma → ℂ) :
      MvPolynomial.eval (Sum.elim x y) (specializeZeroList l P) =
        MvPolynomial.eval (Sum.elim x (fun _ => 0)) P := by
    rw [eval_specializeZeroList]
    apply congrArg (fun w : Sum tau sigma → ℂ => MvPolynomial.eval w P)
    funext j
    cases j <;> simp [hl]
  by_cases hzero : _root_.RealRooted.specializeRight (fun _ : sigma => 0) P = 0
  · exact Or.inl hzero
  have hQne : specializeZeroList l P ≠ 0 := by
    intro hQzero
    obtain ⟨x, _hx, heval⟩ := exists_upperHalfPlane_eval_ne_zero hzero
    apply heval
    rw [eval_specializeRight, ← hQeval x (fun _ => I), hQzero]
    simp
  right
  intro x hx
  rw [eval_specializeRight, ← hQeval x (fun _ => I)]
  exact (hQ.resolve_left hQne) (Sum.elim x (fun _ => I)) fun j => by
    cases j with
    | inl i => exact hx i
    | inr _ => simp

end

end RealRooted
