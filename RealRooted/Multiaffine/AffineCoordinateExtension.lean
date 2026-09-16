import RealRooted.Multiaffine.CoordinateWronskian

/-!
# Rayleigh criteria for affine coordinate extensions

This file isolates the algebra needed to prove that a polynomial of the form
`P + X k * Q` is Rayleigh. For old coordinate pairs, its Rayleigh difference
is a quadratic in the fresh variable. For a pair involving the fresh
coordinate, the difference is the oriented Wronskian `Q * ∂ P - P * ∂ Q`.
-/

namespace MvPolynomial

noncomputable section

/-- The mixed term in the polarization of the Rayleigh difference. -/
def mixedRayleighDifference {R σ : Type*} [CommRing R]
    (P Q : MvPolynomial σ R) (i j : σ) : MvPolynomial σ R :=
  pderiv i P * pderiv j Q + pderiv i Q * pderiv j P -
    P * pderiv i (pderiv j Q) - Q * pderiv i (pderiv j P)

/-- The mixed Rayleigh difference is symmetric in the two polynomials. -/
theorem mixedRayleighDifference_comm_poly {R σ : Type*} [CommRing R]
    (P Q : MvPolynomial σ R) (i j : σ) :
    mixedRayleighDifference P Q i j = mixedRayleighDifference Q P i j := by
  simp only [mixedRayleighDifference]
  ring

/-- The mixed Rayleigh difference is symmetric in the two coordinates. -/
theorem mixedRayleighDifference_comm_coord {R σ : Type*} [CommRing R]
    (P Q : MvPolynomial σ R) (i j : σ) :
    mixedRayleighDifference P Q i j = mixedRayleighDifference P Q j i := by
  simp only [mixedRayleighDifference, pderiv_comm]
  ring

/-- Mixed Rayleigh differences commute with injective variable renamings. -/
theorem mixedRayleighDifference_rename {R σ τ : Type*} [CommRing R]
    (f : σ → τ) (hf : Function.Injective f)
    (P Q : MvPolynomial σ R) (i j : σ) :
    mixedRayleighDifference (rename f P) (rename f Q) (f i) (f j) =
      rename f (mixedRayleighDifference P Q i j) := by
  simp only [mixedRayleighDifference, pderiv_rename hf, map_add, map_mul,
    map_sub]

/-- Rayleigh differences polarize into two pure terms and one mixed term. -/
theorem rayleighDifference_add {R σ : Type*} [CommRing R]
    (P Q : MvPolynomial σ R) (i j : σ) :
    rayleighDifference (P + Q) i j =
      rayleighDifference P i j + mixedRayleighDifference P Q i j +
        rayleighDifference Q i j := by
  simp only [rayleighDifference, mixedRayleighDifference, map_add]
  ring

/-- At two old coordinates, adjoining an affine coordinate produces a
quadratic Rayleigh difference. -/
theorem rayleighDifference_add_X_mul_of_ne {R σ : Type*} [CommRing R]
    (P Q : MvPolynomial σ R) (k i j : σ)
    (hik : i ≠ k) (hjk : j ≠ k) :
    rayleighDifference (P + X k * Q) i j =
      rayleighDifference P i j + X k * mixedRayleighDifference P Q i j +
        X k ^ 2 * rayleighDifference Q i j := by
  simp only [rayleighDifference, mixedRayleighDifference, map_add, pderiv_mul,
    pderiv_X_of_ne (Ne.symm hik), pderiv_X_of_ne (Ne.symm hjk), zero_mul,
    zero_add]
  ring

/-- At the new and an old coordinate, the Rayleigh difference of a fresh
affine extension is an oriented Wronskian. -/
theorem rayleighDifference_add_X_mul_fresh {R σ : Type*} [CommRing R]
    (P Q : MvPolynomial σ R) (k i : σ) (hik : i ≠ k)
    (hkP : k ∉ P.vars) (hkQ : k ∉ Q.vars) :
    rayleighDifference (P + X k * Q) k i =
      coordinateWronskian Q P i := by
  have hPk : pderiv k P = 0 := pderiv_eq_zero_of_notMem_vars hkP
  have hQk : pderiv k Q = 0 := pderiv_eq_zero_of_notMem_vars hkQ
  simp only [rayleighDifference, coordinateWronskian, map_add, pderiv_mul,
    pderiv_X_self,
    pderiv_X_of_ne (Ne.symm hik), pderiv_comm k i, hPk, hQk, map_zero,
    zero_mul, mul_zero, zero_add, one_mul]
  ring

/-- The discriminant controlling the old-coordinate Rayleigh difference of
an affine coordinate extension. -/
def affineRayleighDiscriminant {R σ : Type*} [CommRing R]
    (P Q : MvPolynomial σ R) (i j : σ) : MvPolynomial σ R :=
  mixedRayleighDifference P Q i j ^ 2 -
    C 4 * rayleighDifference Q i j * rayleighDifference P i j

/-- The affine Rayleigh discriminant is symmetric in its two coordinates. -/
theorem affineRayleighDiscriminant_comm_coord
    {R σ : Type*} [CommRing R] (P Q : MvPolynomial σ R) (i j : σ) :
    affineRayleighDiscriminant P Q i j =
      affineRayleighDiscriminant P Q j i := by
  rw [affineRayleighDiscriminant, affineRayleighDiscriminant,
    mixedRayleighDifference_comm_coord, rayleighDifference_comm P i j,
    rayleighDifference_comm Q i j]

/-- For two multiaffine endpoint polynomials, the affine Rayleigh
discriminant vanishes when both old coordinates coincide. -/
theorem IsMultiaffine.affineRayleighDiscriminant_self
    {R σ : Type*} [CommRing R] {P Q : MvPolynomial σ R}
    (hP : IsMultiaffine P) (hQ : IsMultiaffine Q) (i : σ) :
    affineRayleighDiscriminant P Q i i = 0 := by
  rw [affineRayleighDiscriminant, mixedRayleighDifference,
    hP.pderiv_pderiv_self_eq_zero, hQ.pderiv_pderiv_self_eq_zero,
    hQ.rayleighDifference_self, hP.rayleighDifference_self]
  simp only [map_ofNat]
  ring

/-- Affine Rayleigh discriminants commute with injective variable
renamings. -/
theorem affineRayleighDiscriminant_rename {R σ τ : Type*} [CommRing R]
    (f : σ → τ) (hf : Function.Injective f)
    (P Q : MvPolynomial σ R) (i j : σ) :
    affineRayleighDiscriminant (rename f P) (rename f Q) (f i) (f j) =
      rename f (affineRayleighDiscriminant P Q i j) := by
  simp only [affineRayleighDiscriminant,
    mixedRayleighDifference_rename f hf P Q i j,
    rayleighDifference_rename f hf Q i j,
    rayleighDifference_rename f hf P i j, map_pow, map_sub, map_mul,
    rename_C]

/-- If one coordinate is absent from both endpoints, the corresponding
affine Rayleigh discriminant vanishes. -/
theorem affineRayleighDiscriminant_eq_zero_of_notMem_vars
    {R σ : Type*} [CommRing R] (P Q : MvPolynomial σ R) (k j : σ)
    (hkP : k ∉ P.vars) (hkQ : k ∉ Q.vars) :
    affineRayleighDiscriminant P Q k j = 0 := by
  have hPk : pderiv k P = 0 := pderiv_eq_zero_of_notMem_vars hkP
  have hQk : pderiv k Q = 0 := pderiv_eq_zero_of_notMem_vars hkQ
  simp only [affineRayleighDiscriminant, mixedRayleighDifference,
    rayleighDifference, hPk, hQk, pderiv_comm k j, map_zero, zero_mul,
    mul_zero, add_zero, sub_zero]
  ring

/-- Pointwise nonpositivity of affine Rayleigh discriminants on a common
finite support controls every coordinate pair. -/
theorem eval_affineRayleighDiscriminant_nonpos_of_vars_subset
    {σ : Type*} (P Q : MvPolynomial σ ℝ) (s : Finset σ)
    (hPvars : P.vars ⊆ s) (hQvars : Q.vars ⊆ s)
    (hdisc : ∀ i ∈ s, ∀ j ∈ s, ∀ x,
      eval x (affineRayleighDiscriminant P Q i j) ≤ 0) :
    ∀ i j x, eval x (affineRayleighDiscriminant P Q i j) ≤ 0 := by
  intro i j x
  by_cases hi : i ∈ s
  · by_cases hj : j ∈ s
    · exact hdisc i hi j hj x
    · rw [affineRayleighDiscriminant_comm_coord,
        affineRayleighDiscriminant_eq_zero_of_notMem_vars P Q j i
          (fun hjP => hj (hPvars hjP)) (fun hjQ => hj (hQvars hjQ))]
      simp
  · rw [affineRayleighDiscriminant_eq_zero_of_notMem_vars P Q i j
        (fun hiP => hi (hPvars hiP)) (fun hiQ => hi (hQvars hiQ))]
    simp

/-- For multiaffine endpoints with common finite support, only distinct
supported coordinate pairs require affine-discriminant checks. -/
theorem IsMultiaffine.eval_affineRayleighDiscriminant_nonpos_of_vars_subset
    {σ : Type*} {P Q : MvPolynomial σ ℝ}
    (hP : IsMultiaffine P) (hQ : IsMultiaffine Q) (s : Finset σ)
    (hPvars : P.vars ⊆ s) (hQvars : Q.vars ⊆ s)
    (hdisc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x,
      eval x (affineRayleighDiscriminant P Q i j) ≤ 0) :
    ∀ i j x, eval x (affineRayleighDiscriminant P Q i j) ≤ 0 := by
  apply MvPolynomial.eval_affineRayleighDiscriminant_nonpos_of_vars_subset
    P Q s hPvars hQvars
  intro i hi j hj x
  by_cases hij : i = j
  · subst j
    rw [hP.affineRayleighDiscriminant_self hQ]
    simp
  · exact hdisc i hi j hj hij x

/-- If two multiaffine polynomials use at most two variables, pointwise
nonpositivity of their one cross discriminant controls every coordinate
pair. -/
theorem IsMultiaffine.eval_affineRayleighDiscriminant_nonpos_of_vars_subset_pair
    {σ : Type*} [DecidableEq σ] {P Q : MvPolynomial σ ℝ} {a b : σ}
    (hP : IsMultiaffine P) (hQ : IsMultiaffine Q)
    (hPvars : P.vars ⊆ {a, b}) (hQvars : Q.vars ⊆ {a, b})
    (hab : ∀ x, eval x (affineRayleighDiscriminant P Q a b) ≤ 0) :
    ∀ i j x, eval x (affineRayleighDiscriminant P Q i j) ≤ 0 := by
  apply hP.eval_affineRayleighDiscriminant_nonpos_of_vars_subset
    hQ {a, b} hPvars hQvars
  intro i hi j hj hij x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with hi | hi
  · subst i
    rcases hj with hj | hj
    · subst j
      exact (hij rfl).elim
    · subst j
      exact hab x
  · subst i
    rcases hj with hj | hj
    · subst j
      rw [affineRayleighDiscriminant_comm_coord]
      exact hab x
    · subst j
      exact (hij rfl).elim

/-- A fresh affine coordinate extension is Rayleigh when its two endpoint
polynomials are Rayleigh, its fresh-coordinate Wronskians are nonnegative,
and the old-coordinate quadratic discriminants are nonpositive. -/
theorem IsRayleigh.add_X_mul_of_fresh
    {σ : Type*} {P Q : MvPolynomial σ ℝ} {k : σ}
    (hP : IsRayleigh P) (hQ : IsRayleigh Q)
    (hPma : IsMultiaffine P) (hQma : IsMultiaffine Q)
    (hkP : k ∉ P.vars) (hkQ : k ∉ Q.vars)
    (hcross : ∀ i x, 0 ≤ eval x (coordinateWronskian Q P i))
    (hdisc : ∀ i j x, i ≠ k → j ≠ k →
      eval x (affineRayleighDiscriminant P Q i j) ≤ 0) :
    IsRayleigh (P + X k * Q) := by
  classical
  have hma : IsMultiaffine (P + X k * Q) :=
    hPma.add (hQma.X_mul_of_notMem_vars hkQ)
  intro i j x
  by_cases hik : i = k
  · subst i
    by_cases hjk : j = k
    · subst j
      exact hma.eval_rayleighDifference_self_nonneg k x
    · rw [rayleighDifference_add_X_mul_fresh P Q k j hjk hkP hkQ]
      exact hcross j x
  · by_cases hjk : j = k
    · subst j
      rw [rayleighDifference_comm]
      rw [rayleighDifference_add_X_mul_fresh P Q k i hik hkP hkQ]
      exact hcross i x
    · rw [rayleighDifference_add_X_mul_of_ne P Q k i j hik hjk]
      simp only [map_add, map_mul, map_pow, eval_X]
      have hdisceval :
          discrim (eval x (rayleighDifference Q i j))
              (eval x (mixedRayleighDifference P Q i j))
              (eval x (rayleighDifference P i j)) ≤ 0 := by
        simpa [affineRayleighDiscriminant, discrim] using
          hdisc i j x hik hjk
      have hquad := quadratic_nonneg_of_nonneg_of_discrim_nonpos
        (hQ i j x) (hP i j x) hdisceval (x k)
      simpa [pow_two, add_comm, add_left_comm, add_assoc, mul_comm] using hquad

end

end MvPolynomial
