import RealRooted.MultivariateStability.Rayleigh
import RealRooted.MultivariateStability.RayleighPencil

/-!
# The multiaffine Rayleigh converse

This module proves the finite-variable converse to the Rayleigh criterion by
induction on the variables that actually occur.  The one-coordinate analytic
step lives in `RayleighPencil`; this file owns only the finite-support
induction and its algebraic closure facts.
-/

namespace RealRooted

noncomputable section

/-- Every real linear combination of one zero-specialization and its matching
partial derivative remains Rayleigh. -/
theorem MvPolynomial.IsRayleigh.allComboRayleigh_specializeZero_pderiv
    {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : P.IsRayleigh) (hma : P.IsMultiaffine) (i : σ) (α β : ℝ) :
    (MvPolynomial.C α * MvPolynomial.specializeZero i P +
      MvPolynomial.C β * MvPolynomial.pderiv i P).IsRayleigh := by
  by_cases hα : α = 0
  · subst α
    simpa using (hP.pderiv_of_isMultiaffine hma i).C_mul β
  · have hspecialize := (hP.specializeAt i (β / α)).C_mul α
    rw [MvPolynomial.IsMultiaffine.specializeAt_eq_specializeZero_add_C_mul_pderiv
      hma i (β / α)] at hspecialize
    convert hspecialize using 1
    rw [mul_add, ← mul_assoc, ← MvPolynomial.C_mul]
    field_simp

/-- A real linear combination of one zero-specialization and its matching
partial derivative uses only old variables other than that coordinate. -/
theorem MvPolynomial.IsMultiaffine.vars_combo_specializeZero_pderiv_subset_erase
    {σ : Type*} [DecidableEq σ] {P : MvPolynomial σ ℝ}
    (hma : P.IsMultiaffine) (i : σ) (α β : ℝ) :
    (MvPolynomial.C α * MvPolynomial.specializeZero i P +
        MvPolynomial.C β * MvPolynomial.pderiv i P).vars ⊆
      P.vars.erase i := by
  have hleft :
      (MvPolynomial.C α * MvPolynomial.specializeZero i P).vars ⊆
        (MvPolynomial.specializeZero i P).vars := by
    exact (MvPolynomial.vars_mul _ _).trans (by simp)
  have hright :
      (MvPolynomial.C β * MvPolynomial.pderiv i P).vars ⊆
        (MvPolynomial.pderiv i P).vars := by
    exact (MvPolynomial.vars_mul _ _).trans (by simp)
  exact (MvPolynomial.vars_add_subset _ _).trans
    (Finset.union_subset
      (hleft.trans (MvPolynomial.vars_specializeZero_subset_erase P i))
      (hright.trans (hma.vars_pderiv_subset_erase i)))

/-- For finite variable types, every multiaffine Rayleigh polynomial is zero
or multivariate real stable. -/
theorem MvPolynomial.IsRayleigh.mvRealStableOrZero_of_isMultiaffine
    {σ : Type*} [Finite σ] {P : MvPolynomial σ ℝ}
    (hP : P.IsRayleigh) (hma : P.IsMultiaffine) :
    MvRealStableOrZero P := by
  classical
  have hmain : ∀ n, ∀ Q : MvPolynomial σ ℝ,
      Q.vars.card = n → Q.IsRayleigh → Q.IsMultiaffine →
        MvRealStableOrZero Q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro Q hcard hQ hQma
        by_cases hvars : Q.vars = ∅
        · rw [MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars]
          by_cases hc : Q.coeff 0 = 0
          · left
            simp [hc]
          · right
            simpa using (MvRealStable.one (sigma := σ)).C_mul hc
        · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hvars
          apply
            MvPolynomial.IsRayleigh.mvRealStableOrZero_of_allCombo_specializeZero_pderiv
              hQ hQma i
          intro α β
          let R :=
            MvPolynomial.C α * MvPolynomial.specializeZero i Q +
              MvPolynomial.C β * MvPolynomial.pderiv i Q
          have hRvars : R.vars ⊆ Q.vars.erase i := by
            exact
              MvPolynomial.IsMultiaffine.vars_combo_specializeZero_pderiv_subset_erase
                hQma i α β
          have hRcard : R.vars.card < n := by
            rw [← hcard]
            exact (Finset.card_le_card hRvars).trans_lt
              (Finset.card_erase_lt_of_mem hi)
          apply ih R.vars.card hRcard R rfl
          · exact
              MvPolynomial.IsRayleigh.allComboRayleigh_specializeZero_pderiv
                hQ hQma i α β
          · exact ((hQma.specializeZero_preserves i).C_mul α).add
              ((hQma.pderiv i).C_mul β)
  exact hmain P.vars.card P rfl hP hma

/-- Finite-variable multiaffine real stability is equivalent to nontrivial
Rayleighness. -/
theorem MvPolynomial.IsMultiaffine.mvRealStable_iff_isRayleigh_and_ne_zero
    {σ : Type*} [Finite σ] {P : MvPolynomial σ ℝ} (hma : P.IsMultiaffine) :
    MvRealStable P ↔ P.IsRayleigh ∧ P ≠ 0 := by
  constructor
  · intro hstable
    exact
      ⟨MvRealStable.isRayleigh_of_isMultiaffine hstable hma,
        hstable.ne_zero⟩
  · rintro ⟨hP, hP0⟩
    rcases MvPolynomial.IsRayleigh.mvRealStableOrZero_of_isMultiaffine
        hP hma with hzero | hstable
    · exact (hP0 hzero).elim
    · exact hstable

end

end RealRooted
