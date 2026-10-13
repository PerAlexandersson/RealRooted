import RealRooted.Mathlib.Analysis.Complex.Polynomial.SzaszMultivariate
import RealRooted.BorceaBranden.Applications.CoordinatePFMultiplier

/-!
# Multivariate Jensen multipliers

This file proves the stability-preserver statement used in Borcea--Brändén,
arXiv:0809.0401, Lemma 5.2.  The proof applies the descending-factorial PF
multiplier in each coordinate and composes it with a positive geometric
rescaling.
-/

open scoped BigOperators

namespace RealRooted.BorceaBranden

noncomputable section

open Polynomial

private theorem isPFMultiplierSequence_pow {c : ℝ} (hc : 0 < c) :
    IsPFMultiplierSequence (fun k => c ^ k) := by
  rw [isPFMultiplierSequence_iff_preserves]
  intro p hp
  have hscaled := hp.comp_C_mul_X_add_C hc le_rfl
  have heq : diagonalOperator (fun k => c ^ k) p =
      p.comp (C c * X + C 0) := by
    ext k
    rw [coeff_diagonalOperator]
    simp only [C_0, add_zero, Polynomial.comp_C_mul_X_coeff]
    ring
  rw [heq]
  exact hscaled

private theorem isPFMultiplierSequence_normalizedDescFactorial (n : ℕ) :
    IsPFMultiplierSequence
      (fun k => (n.descFactorial k : ℝ) / (n : ℝ) ^ k) := by
  by_cases hn : n = 0
  · subst n
    have hpf := isPFMultiplierSequence_descFactorial 0
    convert hpf using 1
    funext k
    cases k with
    | zero => norm_num
    | succ k => simp
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hscale : IsPFMultiplierSequence (fun k => ((n : ℝ)⁻¹) ^ k) :=
      isPFMultiplierSequence_pow (inv_pos.mpr hnpos)
    have hmul := (isPFMultiplierSequence_descFactorial n).mul hscale
    convert hmul using 1
    funext k
    rw [div_eq_mul_inv, inv_pow]

private theorem exists_coordinateJensenTransform_stableOrZero
    {σ : Type*} [Finite σ] (β : σ →₀ ℕ) (f : MvPolynomial σ ℂ)
    (hf : MvUpperHalfPlaneStable f) (s : Finset σ) :
    ∃ g : MvPolynomial σ ℂ,
      MvUpperHalfPlaneStableOrZero g ∧
        ∀ α : σ →₀ ℕ,
          g.coeff α =
            ((∏ i ∈ s,
              ((β i).descFactorial (α i) : ℝ) / (β i : ℝ) ^ (α i) : ℝ) : ℂ) *
              f.coeff α := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨f, hf.orZero, ?_⟩
      intro α
      simp
  | @insert q s hqs ih =>
      obtain ⟨g, hg, hcoeff⟩ := ih
      rcases hg with hzero | hg
      · subst g
        refine ⟨0, Or.inl rfl, ?_⟩
        intro α
        have hz :
            ((∏ i ∈ s,
              ((β i).descFactorial (α i) : ℝ) / (β i : ℝ) ^ (α i) : ℝ) : ℂ) *
                f.coeff α = 0 := (hcoeff α).symm
        push_cast at hz
        rw [Finset.prod_insert hqs]
        push_cast
        rw [mul_assoc, hz, mul_zero]
        simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      · let gamma : ℕ → ℝ := fun k =>
          ((β q).descFactorial k : ℝ) / (β q : ℝ) ^ k
        let g' := coordinateDiagonalOperator gamma q g
        have hg' : MvUpperHalfPlaneStableOrZero g' :=
          IsPFMultiplierSequence.coordinateDiagonalOperator_preserves_stability
            (isPFMultiplierSequence_normalizedDescFactorial (β q))
              (g.degreeOf q) q le_rfl hg
        refine ⟨g', hg', ?_⟩
        intro α
        rw [show g' = coordinateDiagonalOperator gamma q g from rfl,
          coeff_coordinateDiagonalOperator, hcoeff]
        simp only [gamma]
        rw [Finset.prod_insert hqs]
        push_cast
        ring

/-- The Jensen operator preserves upper-half-plane stability, with zero output allowed.
This is Borcea--Brändén, arXiv:0809.0401, Lemma 5.2. -/
theorem jensenOp_stableOrZero {σ : Type*} [Fintype σ]
    (β : σ →₀ ℕ) {f : MvPolynomial σ ℂ} (hf : MvUpperHalfPlaneStable f) :
    MvUpperHalfPlaneStableOrZero (MvPolynomial.jensenOp β f) := by
  obtain ⟨g, hg, hcoeff⟩ :=
    exists_coordinateJensenTransform_stableOrZero β f hf Finset.univ
  have heq : g = MvPolynomial.jensenOp β f := by
    ext α
    rw [hcoeff, MvPolynomial.coeff_jensenOp]
    simp only [MvPolynomial.jensen]
  rw [← heq]
  exact hg

end

end RealRooted.BorceaBranden
