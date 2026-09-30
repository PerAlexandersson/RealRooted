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

end

end RealRooted
