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

/-- The total weight of ordered disjoint pairs of `k`-subsets. -/
def disjointSubsetWeight {I : Type*} [Fintype I]
    (a b : I → ℝ) (k : ℕ) : ℝ := by
  classical
  exact
    ∑ B ∈ (Finset.univ : Finset I).powersetCard k,
      (∏ i ∈ B, b i) *
        ∑ A ∈ ((Finset.univ : Finset I) \ B).powersetCard k,
          ∏ i ∈ A, a i

private theorem prod_C_mul_X_eq {I R : Type*} [CommSemiring R]
    (s : Finset I) (c : I → R) :
    ∏ i ∈ s, (Polynomial.C (c i) * Polynomial.X) =
      Polynomial.C (∏ i ∈ s, c i) * Polynomial.X ^ s.card := by
  rw [Finset.prod_mul_distrib, ← map_prod]
  simp

private theorem coeff_prod_one_add_C_mul_X {I : Type*}
    (s : Finset I) (c : I → ℝ) (k : ℕ) :
    (∏ i ∈ s, (1 + Polynomial.C (c i) * Polynomial.X)).coeff k =
      ∑ A ∈ s.powersetCard k, ∏ i ∈ A, c i := by
  classical
  rw [Finset.prod_one_add, Polynomial.finsetSum_coeff]
  have hterm (A : Finset I) :
      (∏ i ∈ A, (Polynomial.C (c i) * Polynomial.X)).coeff k =
        if k = A.card then ∏ i ∈ A, c i else 0 := by
    rw [prod_C_mul_X_eq, Polynomial.coeff_C_mul_X_pow]
  simp_rw [hterm]
  rw [Finset.powersetCard_eq_filter]
  rw [Finset.sum_filter]
  simp only [eq_comm]

/-- The double disjoint-subset weight is the diagonal bivariate coefficient of
the normalized rank-two product. -/
theorem disjointSubsetWeight_eq_diagonal_coeff
    {I : Type*} [Fintype I] (a b : I → ℝ) (k : ℕ) :
    disjointSubsetWeight a b k =
      ((∏ i, normalizedFactor (a i) (b i)).coeff k).coeff k := by
  classical
  have hfactor (i : I) :
      normalizedFactor (a i) (b i) =
        Polynomial.C (Polynomial.C (b i)) * Polynomial.X +
          Polynomial.C (1 + Polynomial.C (a i) * Polynomial.X) := by
    simp [normalizedFactor, embedReal, embedRealHom, leftVariable, rightVariable]
    ring
  rw [show (∏ i, normalizedFactor (a i) (b i)) =
      ∏ i, (Polynomial.C (Polynomial.C (b i)) * Polynomial.X +
        Polynomial.C (1 + Polynomial.C (a i) * Polynomial.X)) by
      apply Finset.prod_congr rfl
      intro i _hi
      exact hfactor i]
  rw [Fintype.prod_add]
  simp only [Polynomial.finsetSum_coeff]
  have houter (B : Finset I) :
      (((∏ i ∈ B, Polynomial.C (Polynomial.C (b i)) * Polynomial.X) *
            ∏ i ∈ Bᶜ,
              Polynomial.C (1 + Polynomial.C (a i) * Polynomial.X)).coeff k).coeff k =
        if k = B.card then
          (∏ i ∈ B, b i) *
            ((∏ i ∈ Bᶜ,
              (1 + Polynomial.C (a i) * Polynomial.X)).coeff k)
        else 0 := by
    have hleft :
        (∏ i ∈ B, Polynomial.C (Polynomial.C (b i)) * Polynomial.X) =
          Polynomial.C (Polynomial.C (∏ i ∈ B, b i)) *
            Polynomial.X ^ B.card := by
      simpa only [map_prod] using
        (prod_C_mul_X_eq B (fun i ↦ Polynomial.C (b i)))
    have hright :
        (∏ i ∈ Bᶜ,
            Polynomial.C (1 + Polynomial.C (a i) * Polynomial.X)) =
          Polynomial.C
            (∏ i ∈ Bᶜ, (1 + Polynomial.C (a i) * Polynomial.X)) := by
      rw [map_prod]
    rw [hleft, hright]
    have hcombine :
        (Polynomial.C (Polynomial.C (∏ i ∈ B, b i)) *
            Polynomial.X ^ B.card) *
            Polynomial.C
              (∏ i ∈ Bᶜ, (1 + Polynomial.C (a i) * Polynomial.X)) =
          Polynomial.C
              (Polynomial.C (∏ i ∈ B, b i) *
                ∏ i ∈ Bᶜ, (1 + Polynomial.C (a i) * Polynomial.X)) *
            Polynomial.X ^ B.card := by
      rw [Polynomial.C_mul]
      ring
    rw [hcombine, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hk
    · rw [Polynomial.coeff_C_mul]
    · simp
  simp_rw [houter]
  simp_rw [coeff_prod_one_add_C_mul_X]
  have hpowerset_univ :
      (Finset.univ : Finset I).powerset =
        (Finset.univ : Finset (Finset I)) := by
    ext B
    simp
  simp only [disjointSubsetWeight]
  rw [Finset.powersetCard_eq_filter, Finset.sum_filter, hpowerset_univ]
  simp only [Finset.compl_eq_univ_sdiff, eq_comm]

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
