import RealRooted.HermiteBiehler.Converse.Wronskian

/-!
# Converse Hermite--Biehler theorem

This file proves that upper-half-plane stability of `f + i g`, together with
positive leading coefficients, forces the appropriate interlacing relation.
It contains the common-root inductions and ratio endpoints built on the
Wronskian and degree-at-most-two converse layers.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Planning stub for the converse Hermite--Biehler theorem.

The exact orientation hypotheses may still be adjusted, but the target is that
upper-half-plane stability of `f + i g` forces an interlacing relation between
-/
abbrev hermiteBiehlerConverseStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) →
    Prec g f ∨ Prec f g

theorem isUpperHalfPlaneStable_cofactor_of_stable {f g : ℝ[X]} {r : ℝ}
    (hrf : f.IsRoot r) (hrg : g.IsRoot r)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    IsUpperHalfPlaneStable
      (hermiteBiehlerPolynomial (f /ₘ (X - C r)) (g /ₘ (X - C r))) := by
  intro z hz hroot
  refine hstab z hz ?_
  rw [hermiteBiehlerPolynomial_factor_common_root hrf hrg, eval_mul, hroot, mul_zero]

theorem hermiteBiehlerConverse_general :
    ∀ (n : ℕ) (f g : ℝ[X]), f.natDegree = n → HasPosLeadingCoeff f →
      HasPosLeadingCoeff g → IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) →
      Prec g f ∨ Prec f g := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f g h_fn hf hg hstab
    rcases Nat.lt_or_ge n 3 with h_lt | h_ge
    · exact hermiteBiehlerConverse_of_natDegree_le_two hf hg (by lia) hstab
    · by_cases hc : ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r
      · obtain ⟨r, hrf, hrg⟩ := hc
        set f₁ := f /ₘ (X - C r) with hf₁
        set g₁ := g /ₘ (X - C r) with hg₁
        have h_f_drop : f₁.natDegree = f.natDegree - 1 := by
          rw [hf₁, natDegree_divByMonic f (monic_X_sub_C r), natDegree_X_sub_C]
        have h_f₁_pos : HasPosLeadingCoeff f₁ :=
          hf₁ ▸ hf.divByMonic_X_sub_C hrf
        have h_g₁_pos : HasPosLeadingCoeff g₁ :=
          hg₁ ▸ hg.divByMonic_X_sub_C hrg
        have h_stab₁ : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f₁ g₁) :=
          isUpperHalfPlaneStable_cofactor_of_stable hrf hrg hstab
        have h_lt₁ : f₁.natDegree < n := by rw [h_f_drop, h_fn]; lia
        rcases ih f₁.natDegree h_lt₁ f₁ g₁ rfl h_f₁_pos h_g₁_pos h_stab₁ with h | h
        · exact Or.inl (prec_of_prec_cofactor hrf hrg h)
        · exact Or.inr (prec_of_prec_cofactor hrg hrf h)
      · push Not at hc
        obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable hf hg hstab
        rcases Nat.lt_or_ge g.natDegree f.natDegree with h_g_lt | h_g_ge
        · exact Or.inl (prec_of_stable_succ_degree hf hg hstab (by
            simp_all) (by lia))
        · have h_deg : f.natDegree = g.natDegree := by lia
          exact Or.inl (prec_of_stable_same_degree_no_common hf hg hstab
            (by simp_all) h_deg (by lia))

theorem hermiteBiehlerConverse {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (h : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    Prec g f ∨ Prec f g :=
  hermiteBiehlerConverse_general f.natDegree f g rfl hf hg h

theorem ratio_cofactor_eq {f g : ℝ[X]} {r : ℝ} (hrf : f.IsRoot r) (hrg : g.IsRoot r) {z : ℂ}
    (hz : z ≠ (r : ℂ)) :
    (complexify (g /ₘ (X - C r))).eval z / (complexify (f /ₘ (X - C r))).eval z
      = (complexify g).eval z / (complexify f).eval z := by
  have hff : f = (X - C r) * (f /ₘ (X - C r)) := (mul_divByMonic_eq_iff_isRoot.mpr hrf).symm
  have hgg : g = (X - C r) * (g /ₘ (X - C r)) := (mul_divByMonic_eq_iff_isRoot.mpr hrg).symm
  have hfac : ∀ (h : ℝ[X]), (complexify ((X - C r) * h)).eval z
      = (z - (r : ℂ)) * (complexify h).eval z := by
    intro h
    simp [complexify, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  conv_rhs => rw [hff, hgg, hfac, hfac]
  rw [mul_div_mul_left]
  exact sub_ne_zero.mpr hz

theorem im_ratio_nonpos_general {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (hpq : Prec g f)
    (h_deg₁ : 1 ≤ f.natDegree)
    {z : ℂ} (hz : 0 < z.im) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f g with
  | _ n ih =>
    subst hn
    by_cases hcom : ∃ r, r ∈ f.roots ∧ r ∈ g.roots
    · obtain ⟨r, hrf, hrg⟩ := hcom
      have hrfroot : f.IsRoot r := isRoot_of_mem_roots hrf
      have hrgroot : g.IsRoot r := isRoot_of_mem_roots hrg
      have hzr : z ≠ (r : ℂ) := by intro h; simp_all
      rw [← ratio_cofactor_eq hrfroot hrgroot hzr]
      have hpq₁ : Prec (g /ₘ (X - C r)) (f /ₘ (X - C r)) :=
        prec_cofactor_of_common_root hpq hrfroot hrgroot
      have hf₁ : HasPosLeadingCoeff (f /ₘ (X - C r)) :=
        hf.divByMonic_X_sub_C hrfroot
      have hg₁ : HasPosLeadingCoeff (g /ₘ (X - C r)) :=
        hg.divByMonic_X_sub_C hrgroot
      have hf₁deg : (f /ₘ (X - C r)).natDegree < f.natDegree := by
        rw [natDegree_divByMonic f (monic_X_sub_C r), natDegree_X_sub_C]; lia
      by_cases hd₁ : 1 ≤ (f /ₘ (X - C r)).natDegree
      · exact ih _ hf₁deg hf₁ hg₁ hpq₁ hd₁ rfl
      · push Not at hd₁
        have hf₁deg₀ : (f /ₘ (X - C r)).natDegree = 0 := by lia
        have hg₁deg₀ : (g /ₘ (X - C r)).natDegree = 0 := by
          have hg₁_le := hpq₁.natDegree_le
          lia
        have hf₁c : complexify (f /ₘ (X - C r)) = C ((f /ₘ (X - C r)).coeff 0 : ℂ) := by
          rw [complexify, eq_C_of_natDegree_eq_zero hf₁deg₀]; simp
        have hg₁c : complexify (g /ₘ (X - C r)) = C ((g /ₘ (X - C r)).coeff 0 : ℂ) := by
          rw [complexify, eq_C_of_natDegree_eq_zero hg₁deg₀]; simp
        simp [*]
    · push Not at hcom
      have hfnd : f.roots.Nodup := by
        by_contra hnd
        obtain ⟨r, hrf, hrg⟩ := exists_common_root_of_not_nodup hpq hnd
        simp_all
      have hgnd : g.roots.Nodup := by
        by_contra hnd
        obtain ⟨r, hrf, hrg⟩ := exists_common_root_of_not_nodup_g hpq hnd
        simp_all
      exact im_ratio_nonpos hpq hf hg hfnd hgnd (fun s hsf hsg ↦ hcom s hsf hsg) h_deg₁ hz

theorem prec_of_stable_general {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (h_deg₁ : 1 ≤ f.natDegree) : Prec g f := by
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f g with
  | _ n ih =>
    subst hn
    by_cases hcom : ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r
    · obtain ⟨r, hrf, hrg⟩ := hcom
      have hstab₁ := isUpperHalfPlaneStable_cofactor_of_stable hrf hrg hstab
      have hf₁ : HasPosLeadingCoeff (f /ₘ (X - C r)) :=
        hf.divByMonic_X_sub_C hrf
      have hg₁ : HasPosLeadingCoeff (g /ₘ (X - C r)) :=
        hg.divByMonic_X_sub_C hrg
      have hf₁deg : (f /ₘ (X - C r)).natDegree < f.natDegree := by
        rw [natDegree_divByMonic f (monic_X_sub_C r), natDegree_X_sub_C]; lia
      by_cases hd₁ : 1 ≤ (f /ₘ (X - C r)).natDegree
      · exact prec_of_prec_cofactor hrf hrg (ih _ hf₁deg hf₁ hg₁ hstab₁ hd₁ rfl)
      · push Not at hd₁
        have hf₁d₀ : (f /ₘ (X - C r)).natDegree = 0 := by lia
        have hfd₁ : f.natDegree = 1 := by
          rw [natDegree_divByMonic f (monic_X_sub_C r), natDegree_X_sub_C] at hf₁d₀; lia
        obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable hf hg hstab
        have hg₁d₀ : (g /ₘ (X - C r)).natDegree = 0 := by
          rw [natDegree_divByMonic g (monic_X_sub_C r), natDegree_X_sub_C]; lia
        refine prec_of_prec_cofactor hrf hrg ?_
        obtain ⟨⟨hg₁₀, hg₁s⟩, ⟨hf₁₀, hf₁s⟩⟩ :
            ((g /ₘ (X - C r)) ≠ 0 ∧ (g /ₘ (X - C r)).Splits) ∧
              ((f /ₘ (X - C r)) ≠ 0 ∧ (f /ₘ (X - C r)).Splits) :=
          ⟨isRealRooted_of_deg_zero hg₁.ne_zero hg₁d₀,
            isRealRooted_of_deg_zero hf₁.ne_zero hf₁d₀⟩
        exact prec_degree_zero_degree_zero hg₁₀ hg₁s hf₁₀ hf₁s hg₁d₀ hf₁d₀
    · push Not at hcom
      obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable hf hg hstab
      rcases Nat.lt_or_ge g.natDegree f.natDegree with hglt | hgge
      · exact prec_of_stable_succ_degree hf hg hstab
          (fun ⟨r, hrf, hrg⟩ => hcom r hrf hrg) (by lia)
      · exact prec_of_stable_same_degree_no_common hf hg hstab
          (fun ⟨r, hrf, hrg⟩ => hcom r hrf hrg) (by lia) h_deg₁

end RealRooted
