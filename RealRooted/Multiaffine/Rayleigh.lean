import RealRooted.Mathlib.Algebra.MvPolynomial.PDeriv
import RealRooted.Mathlib.Algebra.MvPolynomial.PDerivSpecialize
import RealRooted.Mathlib.Algebra.QuadraticDiscriminant
import RealRooted.Multiaffine
import Mathlib.Data.Real.Basic

/-!
# Rayleigh differences of multiaffine polynomials

This file provides the coefficient-ring algebra for the Rayleigh criterion.
The stability implications belong in the multivariate-stability layer; the
definitions and identities here require no root theory.
-/

namespace MvPolynomial

noncomputable section

/-- The Rayleigh difference in coordinates `i` and `j`. -/
def rayleighDifference {R σ : Type*} [CommRing R]
    (P : MvPolynomial σ R) (i j : σ) : MvPolynomial σ R :=
  pderiv i P * pderiv j P - P * pderiv i (pderiv j P)

/-- Rayleigh differences are symmetric in their two coordinates. -/
theorem rayleighDifference_comm {R σ : Type*} [CommRing R]
    (P : MvPolynomial σ R) (i j : σ) :
    rayleighDifference P i j = rayleighDifference P j i := by
  rw [rayleighDifference, rayleighDifference, pderiv_comm]
  ring

/-- A partial derivative paired with a directional derivative is the weighted
sum of the corresponding row of Rayleigh differences. -/
theorem pderiv_mul_directionalPDeriv_sub
    {R σ : Type*} [CommRing R] [Fintype σ]
    (b : σ → R) (P : MvPolynomial σ R) (i : σ) :
    pderiv i P * RealRooted.directionalPDeriv b P -
        P * RealRooted.directionalPDeriv b (pderiv i P) =
      ∑ j, C (b j) * rayleighDifference P i j := by
  classical
  simp only [RealRooted.directionalPDeriv, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [rayleighDifference, pderiv_comm j i]
  ring

/-- Rayleigh differences commute with coefficient maps. -/
theorem rayleighDifference_map {R S σ : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : MvPolynomial σ R) (i j : σ) :
    rayleighDifference (map f P) i j =
      map f (rayleighDifference P i j) := by
  simp only [rayleighDifference, pderiv_map, map_mul, map_sub]

/-- Rayleigh differences commute with injective variable renamings. -/
theorem rayleighDifference_rename {R σ τ : Type*} [CommRing R]
    (f : σ → τ) (hf : Function.Injective f)
    (P : MvPolynomial σ R) (i j : σ) :
    rayleighDifference (rename f P) (f i) (f j) =
      rename f (rayleighDifference P i j) := by
  simp only [rayleighDifference, pderiv_rename hf, map_mul, map_sub]

/-- Rayleigh differences commute with specialization away from their two
active coordinates. -/
theorem rayleighDifference_specializeAt_of_ne {R σ : Type*} [CommRing R]
    {i j k : σ} (hik : i ≠ k) (hjk : j ≠ k) (c : R)
    (P : MvPolynomial σ R) :
    rayleighDifference (specializeAt k c P) i j =
      specializeAt k c (rayleighDifference P i j) := by
  simp only [rayleighDifference, pderiv_specializeAt_of_ne hik,
    pderiv_specializeAt_of_ne hjk, specializeAt_mul, specializeAt_sub]

/-- Evaluation of a Rayleigh difference is the corresponding scalar
determinant. -/
theorem eval_rayleighDifference {R σ : Type*} [CommRing R]
    (z : σ → R) (P : MvPolynomial σ R) (i j : σ) :
    eval z (rayleighDifference P i j) =
      eval z (pderiv i P) * eval z (pderiv j P) -
        eval z P * eval z (pderiv i (pderiv j P)) := by
  simp only [rayleighDifference, map_sub, map_mul]

/-- The Rayleigh difference of a bivariate multiaffine coefficient form is
its two-by-two coefficient determinant. -/
theorem rayleighDifference_bivariate {R σ : Type*} [CommRing R]
    (i j : σ) (hij : i ≠ j) (a b c d : R) :
    rayleighDifference
        (C a + C b * X i + C c * X j + C d * X i * X j) i j =
      C (b * c - a * d) := by
  classical
  simp only [rayleighDifference, map_add, pderiv_C, pderiv_mul,
    pderiv_X_self, pderiv_X_of_ne hij, pderiv_X_of_ne (Ne.symm hij),
    zero_mul, mul_zero, zero_add, add_zero, mul_one]
  calc
    _ = C b * C c - C a * C d := by ring
    _ = C (b * c - a * d) := by simp only [map_sub, map_mul]

/-- A bivariate coefficient form in two distinct coordinates is
multiaffine. -/
theorem isMultiaffine_bivariate {R σ : Type*} [CommRing R] [Nontrivial R]
    (i j : σ) (hij : i ≠ j) (a b c d : R) :
    IsMultiaffine
      (C a + C b * X i + C c * X j + C d * X i * X j) := by
  classical
  have hlast : IsMultiaffine (C d * X i * X j : MvPolynomial σ R) := by
    have hprod := (IsMultiaffine.prod_X (R := R) ({i, j} : Finset σ)).C_mul d
    simpa [hij, Ne.symm hij, mul_assoc] using hprod
  exact (((IsMultiaffine.C a).add ((IsMultiaffine.X i).C_mul b)).add
    ((IsMultiaffine.X j).C_mul c)).add hlast

/-- In a multiaffine polynomial, the same-coordinate Rayleigh difference is
the square of the corresponding partial derivative. -/
theorem IsMultiaffine.rayleighDifference_self {R σ : Type*} [CommRing R]
    {P : MvPolynomial σ R} (hP : IsMultiaffine P) (i : σ) :
    rayleighDifference P i i = MvPolynomial.pderiv i P ^ 2 := by
  rw [rayleighDifference, hP.pderiv_pderiv_self_eq_zero]
  ring

/-- Along any one coordinate, a Rayleigh difference of a multiaffine
polynomial is quadratic, with leading coefficient the corresponding Rayleigh
difference of the partial derivative. -/
theorem IsMultiaffine.exists_eval_update_rayleighDifference_quadratic
    {R σ : Type*} [CommRing R] [DecidableEq σ]
    {P : MvPolynomial σ R}
    (hP : IsMultiaffine P) (i j k : σ) (x : σ → R) :
    ∃ b c : R, ∀ t : R,
      eval (Function.update x k t) (rayleighDifference P i j) =
        eval x (rayleighDifference (MvPolynomial.pderiv k P) i j) * t ^ 2 +
          b * t + c := by
  classical
  let Q := MvPolynomial.pderiv k P
  let b :=
    eval x (MvPolynomial.pderiv i Q) *
          eval (Function.update x k 0) (MvPolynomial.pderiv j P) +
      eval (Function.update x k 0) (MvPolynomial.pderiv i P) *
          eval x (MvPolynomial.pderiv j Q) -
      (eval x Q *
          eval (Function.update x k 0)
            (MvPolynomial.pderiv i (MvPolynomial.pderiv j P)) +
        eval (Function.update x k 0) P *
          eval x (MvPolynomial.pderiv i (MvPolynomial.pderiv j Q)))
  let c :=
    eval (Function.update x k 0) (MvPolynomial.pderiv i P) *
          eval (Function.update x k 0) (MvPolynomial.pderiv j P) -
      eval (Function.update x k 0) P *
        eval (Function.update x k 0)
          (MvPolynomial.pderiv i (MvPolynomial.pderiv j P))
  refine ⟨b, c, fun t => ?_⟩
  rw [eval_rayleighDifference,
    hP.eval_update_eq_eval_pderiv_mul_add,
    (hP.pderiv i).eval_update_eq_eval_pderiv_mul_add,
    (hP.pderiv j).eval_update_eq_eval_pderiv_mul_add,
    ((hP.pderiv j).pderiv i).eval_update_eq_eval_pderiv_mul_add]
  dsimp only [b, c, Q]
  rw [eval_rayleighDifference]
  simp only [pderiv_comm]
  ring

/-- A real polynomial is Rayleigh when every Rayleigh difference is
nonnegative at every real point. -/
def IsRayleigh {σ : Type*} (P : MvPolynomial σ ℝ) : Prop :=
  ∀ i j x, 0 ≤ eval x (rayleighDifference P i j)

/-- Scaling a polynomial scales every Rayleigh difference by the square of
the scalar. -/
theorem rayleighDifference_C_mul {σ : Type*}
    (c : ℝ) (P : MvPolynomial σ ℝ) (i j : σ) :
    rayleighDifference (C c * P) i j = C (c ^ 2) * rayleighDifference P i j := by
  simp only [rayleighDifference, pderiv_C_mul]
  rw [map_pow]
  ring

/-- Real scalar multiplication preserves the Rayleigh property, including at
the zero scalar. -/
theorem IsRayleigh.C_mul {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : IsRayleigh P) (c : ℝ) : IsRayleigh (C c * P) := by
  intro i j x
  rw [rayleighDifference_C_mul, eval_mul, eval_C]
  exact mul_nonneg (sq_nonneg c) (hP i j x)

/-- An injective variable renaming preserves the Rayleigh property. -/
theorem IsRayleigh.rename {σ τ : Type*} {P : MvPolynomial σ ℝ}
    (hP : IsRayleigh P) (f : σ → τ) (hf : Function.Injective f) :
    IsRayleigh (MvPolynomial.rename f P) := by
  classical
  have hnotMem_of_not_range {i : τ} (hi : i ∉ Set.range f) :
      i ∉ (MvPolynomial.rename f P).vars := by
    intro hivars
    obtain ⟨j, hj, hji⟩ := mem_vars_rename f P hivars
    exact hi ⟨j, hji⟩
  have hdiff_zero {i : τ}
      (hi : i ∉ (MvPolynomial.rename f P).vars) (j : τ) :
      rayleighDifference (MvPolynomial.rename f P) i j = 0 := by
    rw [rayleighDifference, pderiv_eq_zero_of_notMem_vars hi,
      pderiv_comm i j, pderiv_eq_zero_of_notMem_vars hi]
    simp
  intro i j x
  by_cases hi : i ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hi
    by_cases hj : j ∈ Set.range f
    · obtain ⟨b, rfl⟩ := hj
      rw [rayleighDifference_rename f hf, eval_rename]
      exact hP a b _
    · rw [rayleighDifference_comm,
        hdiff_zero (hnotMem_of_not_range hj)]
      simp
  · rw [hdiff_zero (hnotMem_of_not_range hi)]
    simp

/-- The Rayleigh property is reflected by an injective variable renaming. -/
theorem IsRayleigh.of_rename {σ τ : Type*} {P : MvPolynomial σ ℝ}
    {f : σ → τ} (hP : IsRayleigh (MvPolynomial.rename f P))
    (hf : Function.Injective f) : IsRayleigh P := by
  classical
  intro i j x
  let z : τ → ℝ := Function.extend f x 0
  have hz : z ∘ f = x := Function.extend_comp hf x 0
  have h := hP (f i) (f j) z
  rw [rayleighDifference_rename f hf, eval_rename, hz] at h
  exact h

/-- An injective variable renaming preserves and reflects the Rayleigh
property. -/
theorem isRayleigh_rename_iff {σ τ : Type*} {P : MvPolynomial σ ℝ}
    {f : σ → τ} (hf : Function.Injective f) :
    IsRayleigh (MvPolynomial.rename f P) ↔ IsRayleigh P :=
  ⟨fun h => h.of_rename hf, fun h => h.rename f hf⟩

/-- Real scalar specialization preserves the Rayleigh property. -/
theorem IsRayleigh.specializeAt {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : IsRayleigh P) (k : σ) (c : ℝ) :
    IsRayleigh (MvPolynomial.specializeAt k c P) := by
  classical
  intro i j x
  by_cases hik : i = k
  · subst i
    rw [rayleighDifference, pderiv_comm k j]
    simp
  · by_cases hjk : j = k
    · subst j
      simp [rayleighDifference]
    · rw [rayleighDifference_specializeAt_of_ne hik hjk,
        eval_specializeAt]
      exact hP i j (Function.update x k c)

/-- Iterated real scalar specialization preserves the Rayleigh property. -/
theorem IsRayleigh.specializeAtList {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : IsRayleigh P) (c : σ → ℝ) (l : List σ) :
    IsRayleigh (MvPolynomial.specializeAtList c l P) := by
  induction l generalizing P with
  | nil => simpa using hP
  | cons i l ih =>
      rw [MvPolynomial.specializeAtList_cons]
      exact ih (hP.specializeAt i (c i))

/-- Partial differentiation preserves the Rayleigh property for multiaffine
real polynomials. -/
theorem IsRayleigh.pderiv_of_isMultiaffine {σ : Type*}
    {P : MvPolynomial σ ℝ} (hP : IsRayleigh P)
    (hPma : IsMultiaffine P) (k : σ) :
    IsRayleigh (MvPolynomial.pderiv k P) := by
  classical
  intro i j x
  obtain ⟨b, c, hquad⟩ :=
    hPma.exists_eval_update_rayleighDifference_quadratic i j k x
  apply quadratic_leadingCoeff_nonneg (b := b) (c := c)
  intro t
  rw [← pow_two, ← hquad]
  exact hP i j (Function.update x k t)

/-- Same-coordinate Rayleigh inequalities hold automatically for a
multiaffine real polynomial. -/
theorem IsMultiaffine.eval_rayleighDifference_self_nonneg
    {σ : Type*} {P : MvPolynomial σ ℝ} (hP : IsMultiaffine P)
    (i : σ) (x : σ → ℝ) :
    0 ≤ eval x (rayleighDifference P i i) := by
  rw [hP.rayleighDifference_self, map_pow]
  positivity

/-- To prove that a multiaffine polynomial is Rayleigh, it suffices to check
distinct coordinate pairs in any finite set containing all its variables. -/
theorem IsMultiaffine.isRayleigh_of_vars_subset
    {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : IsMultiaffine P) (s : Finset σ) (hvars : P.vars ⊆ s)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x : σ → ℝ,
      0 ≤ eval x (rayleighDifference P i j)) :
    IsRayleigh P := by
  classical
  intro i j x
  by_cases hij : i = j
  · subst j
    exact hP.eval_rayleighDifference_self_nonneg i x
  by_cases hi : i ∈ P.vars
  · by_cases hj : j ∈ P.vars
    · exact hpair i (hvars hi) j (hvars hj) hij x
    · rw [rayleighDifference, pderiv_eq_zero_of_notMem_vars hj]
      simp
  · rw [rayleighDifference, pderiv_eq_zero_of_notMem_vars hi,
      pderiv_comm i j, pderiv_eq_zero_of_notMem_vars hi]
    simp

end

end MvPolynomial
