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

private theorem eval_eq_of_eq_on_vars {alpha : Type*}
    (P : MvPolynomial alpha ℂ) (x y : alpha → ℂ)
    (hxy : ∀ i ∈ P.vars, x i = y i) :
    MvPolynomial.eval x P = MvPolynomial.eval y P := by
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) x P =
    MvPolynomial.eval₂Hom (RingHom.id ℂ) y P
  exact MvPolynomial.eval₂Hom_congr' rfl (fun i hi _ => hxy i hi) rfl

/-- The one-coordinate boundary argument, localized to the finite support of
the polynomial being specialized.  This removes the ambient finiteness
assumption from `specializeZero_zero_or_of_degreeOf_le_one` without changing
its affine-line/Hurwitz argument. -/
private theorem specializeZero_zero_or_of_degreeOf_le_one_unrestricted
    {alpha : Type*} {P : MvPolynomial alpha ℂ}
    (hP : MvUpperHalfPlaneStable P) (i : alpha)
    (hi : P.degreeOf i ≤ 1) :
    MvPolynomial.specializeZero i P = 0 ∨
      MvUpperHalfPlaneStable (MvPolynomial.specializeZero i P) := by
  classical
  let Q := MvPolynomial.specializeZero i P
  by_cases hQ : Q = 0
  · exact Or.inl hQ
  right
  intro z hz hQz
  obtain ⟨u, _, hQu⟩ := exists_upperHalfPlane_eval_ne_zero hQ
  let z₁ : alpha → ℂ := fun j => if j ∈ Q.vars then u j else z j
  have hQz₁ : MvPolynomial.eval z₁ Q ≠ 0 := by
    have heval : MvPolynomial.eval z₁ Q = MvPolynomial.eval u Q :=
      eval_eq_of_eq_on_vars Q z₁ u (by
        intro j hj
        simp [z₁, hj])
    rw [heval]
    exact hQu
  let v : alpha → ℂ := fun j => z₁ j - z j
  let A : Polynomial ℂ := affineLineRestriction z v Q
  let B : Polynomial ℂ := affineLineRestriction z v (MvPolynomial.pderiv i P)
  have hA0 : A.eval 0 = 0 := by
    simp only [A, eval_affineLineRestriction, mul_zero, add_zero]
    simpa [Q] using hQz
  have hA1 : A.eval 1 ≠ 0 := by
    simpa [A, v] using hQz₁
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.eval_zero] at hA1
    exact hA1 rfl
  have hPz : MvPolynomial.eval z P ≠ 0 := hP z hz
  have hPaff := MvPolynomial.eval_update_eq_eval_pderiv_mul_add_of_degreeOf_le_one
    hi z (z i)
  have hQeval : MvPolynomial.eval z Q =
      MvPolynomial.eval (Function.update z i 0) P := by
    exact MvPolynomial.eval_specializeZero i P z
  have hB0 : B.eval 0 ≠ 0 := by
    simp only [B, eval_affineLineRestriction, mul_zero, add_zero]
    intro hzero
    rw [Function.update_eq_self] at hPaff
    rw [hzero, zero_mul, zero_add, ← hQeval, hQz] at hPaff
    exact hPz hPaff
  let U : Set ℂ := {t | ∀ j ∈ Q.vars, 0 < (z j + v j * t).im}
  have hUopen : IsOpen U := by
    rw [show U = ⋂ j ∈ Q.vars, {t : ℂ | 0 < (z j + v j * t).im} by
      ext t
      simp [U]]
    exact isOpen_biInter_finset fun _ _ =>
      isOpen_lt continuous_const (by fun_prop)
  have hzeroU : (0 : ℂ) ∈ U := by
    intro j _
    simpa using hz j
  have hUnhds : U ∈ 𝒩 0 := hUopen.mem_nhds hzeroU
  obtain ⟨t, htU, _, hBt, hroot⟩ :=
    Polynomial.exists_neg_self_div_im_pos_of_mem_nhds A B hA hA0 hB0 U hUnhds
  let zt : alpha → ℂ := fun j => z j + v j * t
  let r : ℂ := -A.eval t / B.eval t
  have hr : 0 < r.im := hroot
  have hzroot : ∀ j, 0 < (Function.update zt i r j).im := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hr
    · rw [Function.update_of_ne hji]
      by_cases hjQ : j ∈ Q.vars
      · exact htU j hjQ
      · simpa [zt, v, z₁, hjQ] using hz j
  apply hP (Function.update zt i r) hzroot
  rw [MvPolynomial.eval_update_eq_eval_pderiv_mul_add_of_degreeOf_le_one hi]
  have hBeval :
      MvPolynomial.eval zt (MvPolynomial.pderiv i P) = B.eval t := by
    simp [B, zt]
  have hAeval : MvPolynomial.eval (Function.update zt i 0) P = A.eval t := by
    rw [← MvPolynomial.eval_specializeZero i P zt]
    simp [A, zt, Q]
  rw [hBeval, hAeval]
  dsimp [r]
  field_simp
  ring

private theorem specializeZeroList_zero_or_of_degreeOf_le_one_unrestricted
    {alpha : Type*} {P : MvPolynomial alpha ℂ}
    (hP : MvUpperHalfPlaneStable P) (l : List alpha)
    (hdegree : ∀ i ∈ l, P.degreeOf i ≤ 1) :
    specializeZeroList l P = 0 ∨
      MvUpperHalfPlaneStable (specializeZeroList l P) := by
  induction l generalizing P with
  | nil => exact Or.inr hP
  | cons i l ih =>
      rcases specializeZero_zero_or_of_degreeOf_le_one_unrestricted
          hP i (hdegree i (by simp)) with hzero | hstable
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
  letI := Fintype.ofFinite sigma
  let l : List (Sum tau sigma) :=
    Finset.univ.toList.map (Sum.inr : sigma → Sum tau sigma)
  let Q : MvPolynomial (Sum tau sigma) ℂ := specializeZeroList l P
  have hQeval (x : tau → ℂ) (y : sigma → ℂ) :
      MvPolynomial.eval (Sum.elim x y) Q =
        MvPolynomial.eval (Sum.elim x (fun _ => 0)) P := by
    change
      MvPolynomial.eval (Sum.elim x y) (specializeZeroList l P) =
        MvPolynomial.eval (Sum.elim x (fun _ => 0)) P
    rw [eval_specializeZeroList]
    apply congrArg (fun w : Sum tau sigma → ℂ => MvPolynomial.eval w P)
    funext j
    cases j <;> simp [l]
  have hQzero_or : Q = 0 ∨ MvUpperHalfPlaneStable Q := by
    apply specializeZeroList_zero_or_of_degreeOf_le_one_unrestricted hP l
    intro j hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
    exact hdegree i
  by_cases hzero :
      _root_.RealRooted.specializeRight (fun _ : sigma => 0) P = 0
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
