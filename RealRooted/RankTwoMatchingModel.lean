import Mathlib.Data.Multiset.Fintype
import RealRooted.PFPolynomial

open Polynomial
open scoped BigOperators

namespace RealRooted

namespace RankTwoMatchingModel

noncomputable section

/-- Bivariate polynomials represented as polynomials in the right variable
whose coefficients are polynomials in the left variable. -/
abbrev Bivariate := Polynomial ℝ[X]

/-- Embed a real scalar into a bivariate polynomial. -/
def embedRealHom : ℝ →+* Bivariate :=
  Polynomial.C.comp Polynomial.C

/-- Embed a real scalar into a bivariate polynomial. -/
def embedReal (a : ℝ) : Bivariate :=
  embedRealHom a

/-- The left variable of a nested bivariate polynomial. -/
def leftVariable : Bivariate :=
  Polynomial.C Polynomial.X

/-- The right variable of a nested bivariate polynomial. -/
def rightVariable : Bivariate :=
  Polynomial.X

/-- A normalized affine factor used by the rank-two matching model. -/
def normalizedFactor (a b : ℝ) : Bivariate :=
  1 + embedReal a * leftVariable + embedReal b * rightVariable

/-- The shifted affine factor obtained from `1 + g * X`. -/
def rawFactor (g : ℝ) : Bivariate :=
  (1 + rightVariable) + embedReal g * (1 + leftVariable)

theorem scalar_mul_normalizedFactor (g : ℝ) (hg : 0 < g) :
    embedReal (1 + g) * normalizedFactor (g / (1 + g)) (1 / (1 + g)) =
      rawFactor g := by
  have hne : 1 + g ≠ 0 := ne_of_gt (by linarith)
  have hga : (1 + g) * (g / (1 + g)) = g := by
    field_simp
  have hgb : (1 + g) * (1 / (1 + g)) = 1 := by
    field_simp
  have ha :
      embedReal (1 + g) * embedReal (g / (1 + g)) = embedReal g := by
    change
      embedRealHom (1 + g) * embedRealHom (g / (1 + g)) =
        embedRealHom g
    rw [← map_mul, hga]
  have hb :
      embedReal (1 + g) * embedReal (1 / (1 + g)) = 1 := by
    change embedRealHom (1 + g) * embedRealHom (1 / (1 + g)) = 1
    rw [← map_mul, hgb, map_one]
  have hc : embedReal (1 + g) = 1 + embedReal g := by
    simp [embedReal, embedRealHom]
  simp only [normalizedFactor, rawFactor]
  rw [mul_add, mul_add, ← mul_assoc, ha, ← mul_assoc, hb, hc]
  ring

private def alphaSum {I : Type*} {M : ℕ} [Fintype I]
    (g : I → ℝ) : I ⊕ Fin (M - Fintype.card I) → ℝ
  | Sum.inl i => g i / (1 + g i)
  | Sum.inr _ => 0

private def betaSum {I : Type*} {M : ℕ} [Fintype I]
    (g : I → ℝ) : I ⊕ Fin (M - Fintype.card I) → ℝ
  | Sum.inl i => 1 / (1 + g i)
  | Sum.inr _ => 1

private theorem multiset_prod_map_eq_fintype_prod
    {A N : Type*} [DecidableEq A] [CommMonoid N]
    (s : Multiset A) (f : A → N) :
    (s.map f).prod = ∏ i : s, f i := by
  change
    (s.map f).prod =
      (((Finset.univ : Finset s).val.map fun i : s ↦ f (i : A)).prod)
  rw [Multiset.map_univ]

/-- Positive root factors, padded by copies of `1 + v`, admit a `Fin M`
indexing whose normalized affine coefficients are nonnegative. -/
theorem exists_nonneg_factors_fin
    {I : Type*} [Fintype I] {M : ℕ}
    (g : I → ℝ) (hg : ∀ i, 0 < g i) (hcard : Fintype.card I ≤ M) :
    ∃ a b : Fin M → ℝ,
      (∀ i, 0 ≤ a i) ∧
        (∀ i, 0 ≤ b i) ∧
          (∏ i, embedReal (1 + g i)) *
              (∏ j, normalizedFactor (a j) (b j)) =
            (∏ i, rawFactor (g i)) * (1 + rightVariable) ^
              (M - Fintype.card I) := by
  let e : (I ⊕ Fin (M - Fintype.card I)) ≃ Fin M :=
    Fintype.equivFinOfCardEq (by simp [Nat.add_sub_of_le hcard])
  let a : Fin M → ℝ := fun j => alphaSum g (e.symm j)
  let b : Fin M → ℝ := fun j => betaSum g (e.symm j)
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro j
    rcases h : e.symm j with i | i
    · simp only [a, h, alphaSum]
      exact div_nonneg (le_of_lt (hg i)) (by linarith [hg i])
    · simp [a, h, alphaSum]
  · intro j
    rcases h : e.symm j with i | i
    · simp only [b, h, betaSum]
      exact div_nonneg zero_le_one (by linarith [hg i])
    · simp [b, h, betaSum]
  · have hprod :
        (∏ q : I ⊕ Fin (M - Fintype.card I),
            normalizedFactor (alphaSum g q) (betaSum g q)) =
          ∏ j : Fin M, normalizedFactor (a j) (b j) := by
      apply Fintype.prod_equiv e
      intro q
      simp only [a, b, Equiv.symm_apply_apply]
    rw [← hprod, Fintype.prod_sum_type]
    simp only [alphaSum, betaSum]
    have hpad :
        (∏ _i : Fin (M - Fintype.card I), normalizedFactor 0 1) =
          (1 + rightVariable) ^ (M - Fintype.card I) := by
      simp [normalizedFactor, embedReal, leftVariable, rightVariable]
    rw [hpad, ← mul_assoc]
    congr 1
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact scalar_mul_normalizedFactor (g i) (hg i)

/-- Version whose normalization scalar is read from the original univariate
polynomial. -/
theorem exists_nonneg_factors_fin_of_prod
    {p : ℝ[X]} {I : Type*} [Fintype I] {M : ℕ}
    (g : I → ℝ) (hg : ∀ i, 0 < g i) (hcard : Fintype.card I ≤ M)
    (hp : p = ∏ i, (1 + Polynomial.C (g i) * Polynomial.X)) :
    ∃ a b : Fin M → ℝ,
      (∀ i, 0 ≤ a i) ∧
        (∀ i, 0 ≤ b i) ∧
          embedReal (p.eval 1) *
              (∏ j, normalizedFactor (a j) (b j)) =
            (∏ i, rawFactor (g i)) * (1 + rightVariable) ^
              (M - Fintype.card I) := by
  obtain ⟨a, b, ha, hb, hab⟩ :=
    exists_nonneg_factors_fin g hg hcard
  refine ⟨a, b, ha, hb, ?_⟩
  have hp_eval : p.eval 1 = ∏ i, (1 + g i) := by
    rw [hp, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro i hi
    simp
  rw [hp_eval]
  change
    embedRealHom (∏ i, (1 + g i)) *
        (∏ j, normalizedFactor (a j) (b j)) = _
  rw [map_prod]
  exact hab

/-- A constant-one PF polynomial of degree at most `M` supplies all normalized
rank-two factors used in the weighted complete-graph matching model. -/
theorem exists_factors_of_isPFPolynomial
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hconst : p.coeff 0 = 1)
    {M : ℕ} (hdegree : p.natDegree ≤ M) :
    ∃ (s : Multiset ℝ) (a b : Fin M → ℝ),
      (∀ g ∈ s, 0 < g) ∧
        s.card = p.natDegree ∧
          p = (s.map fun g ↦ 1 + Polynomial.C g * Polynomial.X).prod ∧
            (∀ i, 0 ≤ a i) ∧
              (∀ i, 0 ≤ b i) ∧
                embedReal (p.eval 1) *
                    (∏ j, normalizedFactor (a j) (b j)) =
                  (s.map rawFactor).prod *
                    (1 + rightVariable) ^ (M - s.card) := by
  classical
  obtain ⟨s, hs, hscard, hp_factor⟩ :=
    hp.exists_pos_multiset_prod_one_add_C_mul_X hconst
  have hg : ∀ i : s, 0 < (i : ℝ) := by
    intro i
    exact hs i Multiset.coe_mem
  have hcard : Fintype.card s ≤ M := by
    simpa [hscard] using hdegree
  have hp_factor' :
      p = ∏ i : s, (1 + Polynomial.C (i : ℝ) * Polynomial.X) := by
    rw [hp_factor]
    exact multiset_prod_map_eq_fintype_prod s _
  obtain ⟨a, b, ha, hb, hab⟩ :=
    exists_nonneg_factors_fin_of_prod
      (p := p) (fun i : s ↦ (i : ℝ)) hg hcard hp_factor'
  refine ⟨s, a, b, hs, hscard, hp_factor, ha, hb, ?_⟩
  rw [← multiset_prod_map_eq_fintype_prod s] at hab
  simpa [Multiset.card_coe] using hab

end

end RankTwoMatchingModel

end RealRooted
