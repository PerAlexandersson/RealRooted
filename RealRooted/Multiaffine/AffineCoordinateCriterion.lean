import RealRooted.Mathlib.Algebra.MvPolynomial.Eval
import RealRooted.Multiaffine.AffineCoordinateExtension
import RealRooted.Multiaffine.AffineLineRestriction

/-!
# Exact Rayleigh criterion for affine coordinate extensions

For multiaffine polynomials independent of a fresh coordinate, this file
packages the endpoint, cross-Wronskian, and quadratic-discriminant conditions
as a necessary and sufficient criterion for `P + X k * Q` to be Rayleigh.
-/

namespace MvPolynomial

noncomputable section

private theorem notMem_vars_pderiv_of_notMem_vars
    {R σ : Type*} [CommSemiring R] {P : MvPolynomial σ R}
    {k : σ} (hk : k ∉ P.vars) (i : σ) :
    k ∉ (pderiv i P).vars :=
  fun h => hk (vars_pderiv_subset P i h)

private theorem notMem_vars_mul_of_notMem_vars
    {R σ : Type*} [CommSemiring R] {P Q : MvPolynomial σ R}
    {k : σ} (hkP : k ∉ P.vars) (hkQ : k ∉ Q.vars) :
    k ∉ (P * Q).vars := by
  classical
  intro h
  exact (Finset.mem_union.mp (vars_mul P Q h)).elim hkP hkQ

private theorem notMem_vars_add_of_notMem_vars
    {R σ : Type*} [CommSemiring R] {P Q : MvPolynomial σ R}
    {k : σ} (hkP : k ∉ P.vars) (hkQ : k ∉ Q.vars) :
    k ∉ (P + Q).vars := by
  classical
  intro h
  exact (Finset.mem_union.mp (vars_add_subset P Q h)).elim hkP hkQ

private theorem notMem_vars_sub_of_notMem_vars
    {R σ : Type*} [CommRing R] {P Q : MvPolynomial σ R}
    {k : σ} (hkP : k ∉ P.vars) (hkQ : k ∉ Q.vars) :
    k ∉ (P - Q).vars := by
  classical
  intro h
  exact (Finset.mem_union.mp
    (vars_sub_subset (p := P) (q := Q) h)).elim hkP hkQ

private theorem notMem_vars_rayleighDifference_of_notMem_vars
    {R σ : Type*} [CommRing R] {P : MvPolynomial σ R}
    {k : σ} (hkP : k ∉ P.vars) (i j : σ) :
    k ∉ (rayleighDifference P i j).vars := by
  have hPi := notMem_vars_pderiv_of_notMem_vars hkP i
  have hPj := notMem_vars_pderiv_of_notMem_vars hkP j
  have hPji := notMem_vars_pderiv_of_notMem_vars hPj i
  rw [rayleighDifference]
  apply notMem_vars_sub_of_notMem_vars
  · exact notMem_vars_mul_of_notMem_vars hPi hPj
  · exact notMem_vars_mul_of_notMem_vars hkP hPji

private theorem notMem_vars_mixedRayleighDifference_of_notMem_vars
    {R σ : Type*} [CommRing R] {P Q : MvPolynomial σ R}
    {k : σ} (hkP : k ∉ P.vars) (hkQ : k ∉ Q.vars) (i j : σ) :
    k ∉ (mixedRayleighDifference P Q i j).vars := by
  have hPi := notMem_vars_pderiv_of_notMem_vars hkP i
  have hPj := notMem_vars_pderiv_of_notMem_vars hkP j
  have hQi := notMem_vars_pderiv_of_notMem_vars hkQ i
  have hQj := notMem_vars_pderiv_of_notMem_vars hkQ j
  have hPji := notMem_vars_pderiv_of_notMem_vars hPj i
  have hQji := notMem_vars_pderiv_of_notMem_vars hQj i
  have hleft := notMem_vars_add_of_notMem_vars
    (notMem_vars_mul_of_notMem_vars hPi hQj)
    (notMem_vars_mul_of_notMem_vars hQi hPj)
  have hmiddle := notMem_vars_sub_of_notMem_vars hleft
    (notMem_vars_mul_of_notMem_vars hkP hQji)
  have hright := notMem_vars_mul_of_notMem_vars hkQ hPji
  rw [mixedRayleighDifference]
  exact notMem_vars_sub_of_notMem_vars hmiddle hright

/-- A fresh multiaffine extension `P + X k * Q` is Rayleigh exactly when its
two endpoints are Rayleigh, every fresh-coordinate Wronskian is nonnegative,
and every old-coordinate quadratic discriminant is nonpositive. -/
theorem isRayleigh_add_X_mul_iff_of_fresh
    {σ : Type*} {P Q : MvPolynomial σ ℝ} {k : σ}
    (hPma : IsMultiaffine P) (hQma : IsMultiaffine Q)
    (hkP : k ∉ P.vars) (hkQ : k ∉ Q.vars) :
    IsRayleigh (P + X k * Q) ↔
      IsRayleigh P ∧ IsRayleigh Q ∧
        (∀ i x, 0 ≤ eval x (coordinateWronskian Q P i)) ∧
        (∀ i j x, i ≠ k → j ≠ k →
          eval x (affineRayleighDiscriminant P Q i j) ≤ 0) := by
  classical
  let F := P + X k * Q
  have hFma : IsMultiaffine F :=
    hPma.add (hQma.X_mul_of_notMem_vars hkQ)
  constructor
  · intro hF
    have hPspec : specializeAt k 0 F = P := by
      dsimp only [F]
      have hPfixed : specializeAt k 0 P = P := by
        apply MvPolynomial.funext
        intro x
        rw [eval_specializeAt, eval_update_eq_of_notMem_vars hkP]
      rw [specializeAt_add, specializeAt_mul, specializeAt_X, hPfixed]
      simp
    have hP : IsRayleigh P := by
      have h := hF.specializeAt k 0
      rwa [hPspec] at h
    have hPk : pderiv k P = 0 := pderiv_eq_zero_of_notMem_vars hkP
    have hQk : pderiv k Q = 0 := pderiv_eq_zero_of_notMem_vars hkQ
    have hFderiv : pderiv k F = Q := by
      dsimp only [F]
      simp only [map_add, pderiv_mul, pderiv_X_self, hPk, hQk,
        zero_add, mul_zero, one_mul, add_zero]
    have hQ : IsRayleigh Q := by
      have h := hF.pderiv_of_isMultiaffine hFma k
      rwa [hFderiv] at h
    refine ⟨hP, hQ, ?_, ?_⟩
    · intro i x
      by_cases hik : i = k
      · subst i
        rw [coordinateWronskian, hPk, hQk]
        simp
      · rw [← rayleighDifference_add_X_mul_fresh P Q k i hik hkP hkQ]
        exact hF k i x
    · intro i j x hik hjk
      have hPdiff : k ∉ (rayleighDifference P i j).vars :=
        notMem_vars_rayleighDifference_of_notMem_vars hkP i j
      have hQdiff : k ∉ (rayleighDifference Q i j).vars :=
        notMem_vars_rayleighDifference_of_notMem_vars hkQ i j
      have hmixed : k ∉ (mixedRayleighDifference P Q i j).vars :=
        notMem_vars_mixedRayleighDifference_of_notMem_vars hkP hkQ i j
      have hquad (t : ℝ) :
          0 ≤ eval x (rayleighDifference Q i j) * (t * t) +
            eval x (mixedRayleighDifference P Q i j) * t +
            eval x (rayleighDifference P i j) := by
        have h := hF i j (Function.update x k t)
        rw [rayleighDifference_add_X_mul_of_ne P Q k i j hik hjk] at h
        simp only [map_add, map_mul, map_pow, eval_X,
          Function.update_self] at h
        rw [eval_update_eq_of_notMem_vars hPdiff,
          eval_update_eq_of_notMem_vars hmixed,
          eval_update_eq_of_notMem_vars hQdiff] at h
        nlinarith
      simpa [affineRayleighDiscriminant, discrim] using
        (discrim_le_zero hquad)
  · rintro ⟨hP, hQ, hcross, hdisc⟩
    exact hP.add_X_mul_of_fresh hQ hPma hQma hkP hkQ hcross hdisc

/-- The exact fresh-coordinate criterion with the vacuous discriminants at
the fresh coordinate included in the quantified family. -/
theorem isRayleigh_add_X_mul_iff_of_fresh_all_discriminants
    {σ : Type*} {P Q : MvPolynomial σ ℝ} {k : σ}
    (hPma : IsMultiaffine P) (hQma : IsMultiaffine Q)
    (hkP : k ∉ P.vars) (hkQ : k ∉ Q.vars) :
    IsRayleigh (P + X k * Q) ↔
      IsRayleigh P ∧ IsRayleigh Q ∧
        (∀ i x, 0 ≤ eval x (coordinateWronskian Q P i)) ∧
        (∀ i j x, eval x (affineRayleighDiscriminant P Q i j) ≤ 0) := by
  rw [isRayleigh_add_X_mul_iff_of_fresh hPma hQma hkP hkQ]
  constructor
  · rintro ⟨hP, hQ, hcross, hdisc⟩
    refine ⟨hP, hQ, hcross, ?_⟩
    intro i j x
    by_cases hik : i = k
    · subst i
      rw [affineRayleighDiscriminant_eq_zero_of_notMem_vars
        P Q k j hkP hkQ]
      simp
    · by_cases hjk : j = k
      · subst j
        rw [affineRayleighDiscriminant_comm_coord]
        rw [affineRayleighDiscriminant_eq_zero_of_notMem_vars
          P Q k i hkP hkQ]
        simp
      · exact hdisc i j x hik hjk
  · rintro ⟨hP, hQ, hcross, hdisc⟩
    exact ⟨hP, hQ, hcross, fun i j x _ _ => hdisc i j x⟩

end

end MvPolynomial
