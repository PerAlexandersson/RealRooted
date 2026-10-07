import RealRooted.BorceaBranden.BoundarySpecialization

/-!
# Boundary specialization with unrestricted spectator variables

This module supplies the boundary step used in Borcea--Branden, Lemma 2.2.
Only the finite right block is specialized.  The left block consists of
spectator variables and may have arbitrary cardinality and arbitrary degrees.
-/

open Complex

namespace RealRooted

noncomputable section

private theorem specializeZeroList_zero_or_of_degreeOf_le_one_unrestricted
    {alpha : Type*} {P : MvPolynomial alpha ℂ}
    (hP : MvUpperHalfPlaneStable P) (l : List alpha)
    (hdegree : ∀ i ∈ l, P.degreeOf i ≤ 1) :
    specializeZeroList l P = 0 ∨
      MvUpperHalfPlaneStable (specializeZeroList l P) := by
  induction l generalizing P with
  | nil => exact Or.inr hP
  | cons i l ih =>
      rcases hP.specializeZero_zero_or_of_degreeOf_le_one i (hdegree i (by simp)) with
        hzero | hstable
      · left
        simp [specializeZeroList_cons, hzero]
      · apply ih hstable
        intro j hj
        exact (MvPolynomial.degreeOf_specializeZero_le P i j).trans
          (hdegree j (by simp [hj]))

/-- Specializing a finite right block at zero preserves upper-half-plane
stability up to the zero polynomial.  Only the specialized coordinates must
have degree at most one; the target variables are unrestricted spectators. -/
theorem MvUpperHalfPlaneStable.specializeRight_zero_or_of_degreeOf_le_one
    {tau sigma : Type*} [Finite sigma]
    {P : MvPolynomial (Sum tau sigma) ℂ}
    (hP : MvUpperHalfPlaneStable P)
    (hdegree : ∀ i : sigma, P.degreeOf (Sum.inr i) ≤ 1) :
    MvUpperHalfPlaneStableOrZero
      (_root_.RealRooted.specializeRight (fun _ : sigma => 0) P) := by
  classical
  let := Fintype.ofFinite sigma
  let l : List (Sum tau sigma) := Finset.univ.toList.map Sum.inr
  refine MvUpperHalfPlaneStableOrZero.specializeRight_zero_of_specializeZeroList l
    (fun j => by cases j <;> simp [l]) ?_
  apply specializeZeroList_zero_or_of_degreeOf_le_one_unrestricted hP l
  intro j hj
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
  exact hdegree i

end

end RealRooted
