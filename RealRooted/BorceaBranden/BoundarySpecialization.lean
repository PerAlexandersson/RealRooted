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
      congr 1
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

/-- Specializing an entire finite right block at the real boundary point zero
preserves upper-half-plane stability up to the zero polynomial. -/
theorem MvUpperHalfPlaneStable.specializeRight_zero_or
    {sigma tau : Type*} [Fintype sigma] [Fintype tau]
    {P : MvPolynomial (Sum sigma tau) ℂ}
    (hP : MvUpperHalfPlaneStable P) (hPma : MvPolynomial.IsMultiaffine P) :
    MvUpperHalfPlaneStableOrZero
      (_root_.RealRooted.specializeRight (fun _ : tau => 0) P) := by
  classical
  let l : List (Sum sigma tau) :=
    (Finset.univ.toList.map (Sum.inr : tau → Sum sigma tau))
  let Q : MvPolynomial (Sum sigma tau) ℂ := specializeZeroList l P
  have hQeval (x : sigma → ℂ) (y : tau → ℂ) :
      MvPolynomial.eval (Sum.elim x y) Q =
        MvPolynomial.eval (Sum.elim x (fun _ => 0)) P := by
    rw [Q, eval_specializeZeroList]
    congr 1
    funext j
    cases j <;> simp [l]
  have hQzero_or : Q = 0 ∨ MvUpperHalfPlaneStable Q := by
    simpa [Q] using hP.specializeZeroList_zero_or hPma l
  by_cases hzero :
      _root_.RealRooted.specializeRight (fun _ : tau => 0) P = 0
  · exact Or.inl hzero
  have hQne : Q ≠ 0 := by
    intro hQzero
    obtain ⟨x, _hx, heval⟩ := exists_upperHalfPlane_eval_ne_zero hzero
    apply heval
    rw [eval_specializeRight, ← hQeval x (fun _ => I), hQzero]
    simp
  right
  have hQstable : MvUpperHalfPlaneStable Q :=
    hQzero_or.resolve_left hQne
  intro x hx
  rw [eval_specializeRight, ← hQeval x (fun _ => I)]
  exact hQstable (Sum.elim x (fun _ => I)) fun j => by
    cases j with
    | inl i => exact hx i
    | inr _ => simp

end

end RealRooted
