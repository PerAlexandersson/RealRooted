import RealRooted.Basic
import RealRooted.Bezoutian
import RealRooted.CommonInterleaverTwo
import RealRooted.HermiteBiehler.Basic
import RealRooted.HermiteBiehler.ConverseLowDegree
import RealRooted.HermiteBiehler.Converse.RootGeometry
import RealRooted.HermiteBiehler.Forward
import RealRooted.Interlacing.Multiplicity
import RealRooted.Interlacing.Residue
import Mathlib.Data.Complex.Basic

/-!
# Converse Hermite--Biehler theorem

This file proves that upper-half-plane stability of `f + i g`, together with
positive leading coefficients, forces the appropriate interlacing relation.
It contains the Wronskian and common-root inductions built on the root-geometry
and degree-at-most-two converse layers.
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

/-- Value of a complexified real polynomial at a real point. -/
theorem eval_complexify_ofReal (p : ℝ[X]) (t : ℝ) :
    (complexify p).eval (t : ℂ) = ((p.eval t : ℝ) : ℂ) := by
  simpa [complexify] using Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := p) t

theorem eval_derivative_eq_sum_complex (p : ℂ[X]) (x : ℂ) :
    p.derivative.eval x
      = p.leadingCoeff * (p.roots.map (fun w =>
          ((p.roots.erase w).map (fun u => x - u)).prod)).sum :=
  (IsAlgClosed.splits p).eval_derivative x

theorem im_deriv_mul_conj_eq (p : ℂ[X]) (x : ℝ) :
    (p.derivative.eval (x : ℂ) * (starRingEnd ℂ) (p.eval (x : ℂ))).im
      = Complex.normSq p.leadingCoeff *
          (p.roots.map (fun w =>
            Complex.normSq ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod * w.im)).sum := by
  rw [eval_derivative_eq_sum_complex, eval_eq_prod_roots_complex, map_mul]
  set S := (p.roots.map (fun w =>
    ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod)).sum with hS
  set T := (p.roots.map (fun u => (x : ℂ) - u)).prod with hT
  have hre : p.leadingCoeff * S * ((starRingEnd ℂ) p.leadingCoeff * (starRingEnd ℂ) T)
      = ((Complex.normSq p.leadingCoeff : ℝ) : ℂ) * (S * (starRingEnd ℂ) T) := by
    rw [← Complex.mul_conj]
    ring
  rw [hre, Complex.im_ofReal_mul]
  congr 1
  rw [hS, ← Multiset.sum_map_mul_right, multiset_sum_im, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro w hw
  simp only [Function.comp_apply]
  rw [hT, ← Multiset.prod_map_erase (f := fun u => (x : ℂ) - u) hw, map_mul]
  set P := ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod with hP
  have hps : P * ((starRingEnd ℂ) ((x : ℂ) - w) * (starRingEnd ℂ) P)
      = ((Complex.normSq P : ℝ) : ℂ) * (starRingEnd ℂ) ((x : ℂ) - w) := by
    rw [← Complex.mul_conj]
    ring
  simp_all

theorem im_deriv_mul_conj_neg {p : ℂ[X]}
    (hroots : ∀ w ∈ p.roots, w.im ≤ 0)
    {x : ℝ} (hne : p.eval (x : ℂ) ≠ 0)
    {w₀ : ℂ} (hw₀ : w₀ ∈ p.roots) (hneg : w₀.im < 0) :
    (p.derivative.eval (x : ℂ) * (starRingEnd ℂ) (p.eval (x : ℂ))).im < 0 := by
  have hp₀ : p ≠ 0 := fun h_zero => hne (by simp [h_zero])
  rw [im_deriv_mul_conj_eq]
  have hlc : 0 < Complex.normSq p.leadingCoeff :=
    Complex.normSq_pos.mpr (leadingCoeff_ne_zero.mpr hp₀)
  apply mul_neg_of_pos_of_neg hlc
  have hfac : ∀ w ∈ p.roots,
      ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod ≠ 0 := by
    intro w hw hzero
    apply hne
    rw [eval_eq_prod_roots_complex, ← Multiset.prod_map_erase (f := fun u => (x : ℂ) - u) hw,
      hzero, mul_zero, mul_zero]
  rw [← Multiset.sum_map_erase (f := fun w =>
    Complex.normSq ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod * w.im) hw₀]
  have hterm :
      Complex.normSq ((p.roots.erase w₀).map (fun u => (x : ℂ) - u)).prod *
        w₀.im < 0 := by
    have hP : ((p.roots.erase w₀).map (fun u => (x : ℂ) - u)).prod ≠ 0 := hfac w₀ hw₀
    exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hP) hneg
  have hrest : ((p.roots.erase w₀).map (fun w =>
      Complex.normSq ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod * w.im)).sum ≤ 0 := by
    apply multiset_sum_nonpos
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
    have hwmem : w ∈ p.roots := Multiset.mem_of_mem_erase hw
    exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (hroots w hwmem)
  linarith

theorem derivative_hermiteBiehler (f g : ℝ[X]) :
    (hermiteBiehlerPolynomial f g).derivative
      = hermiteBiehlerPolynomial f.derivative g.derivative := by
  simp [hermiteBiehlerPolynomial, complexify, derivative_map]

theorem im_hb_deriv_mul_conj (f g : ℝ[X]) (x : ℝ) :
    ((hermiteBiehlerPolynomial f g).derivative.eval (x : ℂ) *
        (starRingEnd ℂ) ((hermiteBiehlerPolynomial f g).eval (x : ℂ))).im
      = f.eval x * g.derivative.eval x - f.derivative.eval x * g.eval x := by
  rw [derivative_hermiteBiehler, eval_hermiteBiehlerPolynomial, eval_hermiteBiehlerPolynomial,
    eval_complexify_ofReal, eval_complexify_ofReal, eval_complexify_ofReal,
    eval_complexify_ofReal]
  simp [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.conj_I,
    Complex.conj_ofReal]
  ring

theorem wronskian_pos_of_stable {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnoreal : ∀ t : ℝ, (hermiteBiehlerPolynomial f g).eval (t : ℂ) ≠ 0)
    {w₀ : ℂ} (hw₀ : w₀ ∈ (hermiteBiehlerPolynomial f g).roots) (hneg : w₀.im < 0)
    (t : ℝ) :
    0 < f.derivative.eval t * g.eval t - f.eval t * g.derivative.eval t := by
  have him := im_deriv_mul_conj_neg
    (fun w hw => im_nonpos_of_stable_root hstab (isRoot_of_mem_roots hw)) (hnoreal t) hw₀ hneg
  rw [im_hb_deriv_mul_conj] at him
  linarith

theorem prec_of_stable_same_degree {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnoreal : ∀ t : ℝ, (hermiteBiehlerPolynomial f g).eval (t : ℂ) ≠ 0)
    {w₀ : ℂ} (hw₀ : w₀ ∈ (hermiteBiehlerPolynomial f g).roots) (hneg : w₀.im < 0)
    (hdeg : f.natDegree = g.natDegree) : Prec g f := by
  obtain ⟨hfs, hgs⟩ := splits_of_stable hf hg hstab
  exact (StrictPrecSameDegree.of_wronskian_pos (n := f.natDegree) hg hf hdeg.symm rfl hgs hfs
    (fun t => wronskian_pos_of_stable hstab hnoreal hw₀ hneg t)).to_prec

theorem hnoreal_of_no_common_real_root {f g : ℝ[X]}
    (hnc : ¬ ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r) :
    ∀ t : ℝ, (hermiteBiehlerPolynomial f g).eval (t : ℂ) ≠ 0 := by
  intro t ht
  rw [eval_hermiteBiehlerPolynomial, eval_complexify_ofReal, eval_complexify_ofReal] at ht
  have hf : f.eval t = 0 := by simpa using congrArg Complex.re ht
  have hg : g.eval t = 0 := by simpa using congrArg Complex.im ht
  exact hnc ⟨t, hf, hg⟩

theorem exists_neg_root_of_stable_no_real {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnoreal : ∀ t : ℝ, (hermiteBiehlerPolynomial f g).eval (t : ℂ) ≠ 0)
    (hpos : 0 < (hermiteBiehlerPolynomial f g).natDegree) :
    ∃ w₀ ∈ (hermiteBiehlerPolynomial f g).roots, w₀.im < 0 := by
  have hsplits : (hermiteBiehlerPolynomial f g).Splits := IsAlgClosed.splits _
  have hne_roots : (hermiteBiehlerPolynomial f g).roots ≠ 0 := by
    intro h₀
    have h_card : (hermiteBiehlerPolynomial f g).roots.card = 0 := by simp [h₀]
    rw [splits_iff_card_roots.mp hsplits] at h_card
    rw [h_card] at hpos
    lia
  obtain ⟨w₀, hw₀⟩ := Multiset.exists_mem_of_ne_zero hne_roots
  refine ⟨w₀, hw₀, ?_⟩
  have h_le : w₀.im ≤ 0 := im_nonpos_of_stable_root hstab (isRoot_of_mem_roots hw₀)
  rcases lt_or_eq_of_le h_le with h_lt | h_eq
  · exact h_lt
  · exfalso
    have hreal : w₀ = ((w₀.re : ℝ) : ℂ) := Complex.ext rfl h_eq
    have hroot : (hermiteBiehlerPolynomial f g).eval w₀ = 0 := isRoot_of_mem_roots hw₀
    rw [hreal] at hroot
    exact hnoreal w₀.re hroot

theorem prec_of_stable_same_degree_no_common {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnc : ¬ ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r)
    (hdeg : f.natDegree = g.natDegree) (hfpos : 0 < f.natDegree) : Prec g f := by
  have hnoreal := hnoreal_of_no_common_real_root hnc
  have hlead : 0 < f.coeff f.natDegree := hf
  have : (hermiteBiehlerPolynomial f g).natDegree = f.natDegree :=
    (hermiteBiehler_natDegree_of_posLead hlead rfl hdeg.symm).1
  have hpos : 0 < (hermiteBiehlerPolynomial f g).natDegree := by simp_all
  obtain ⟨w₀, hw₀mem, hw₀neg⟩ := exists_neg_root_of_stable_no_real hstab hnoreal hpos
  exact prec_of_stable_same_degree hf hg hstab hnoreal hw₀mem hw₀neg hdeg

theorem prec_of_stable_succ_degree {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnc : ¬ ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r)
    (hdeg : f.natDegree = g.natDegree + 1) : Prec g f := by
  have hnoreal := hnoreal_of_no_common_real_root hnc
  have : (hermiteBiehlerPolynomial f g).natDegree = f.natDegree :=
    (hermiteBiehler_natDegree_of_left_dominant hf.ne_zero (by simp [*])).1
  have hpos : 0 < (hermiteBiehlerPolynomial f g).natDegree := by simp [*]
  obtain ⟨w₀, hw₀mem, hw₀neg⟩ := exists_neg_root_of_stable_no_real hstab hnoreal hpos
  obtain ⟨hfs, hgs⟩ := splits_of_stable hf hg hstab
  exact prec_of_wronskian_pos_succ hf hg hdeg rfl hfs hgs
    (fun t => wronskian_pos_of_stable hstab hnoreal hw₀mem hw₀neg t)

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
        have h_f₁_pos : HasPosLeadingCoeff f₁ := by
          rw [HasPosLeadingCoeff, hf₁, leadingCoeff_divByMonic_X_sub_C hrf]; exact hf
        have h_g₁_pos : HasPosLeadingCoeff g₁ := by
          rw [HasPosLeadingCoeff, hg₁, leadingCoeff_divByMonic_X_sub_C hrg]; exact hg
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
      have hf₁ : HasPosLeadingCoeff (f /ₘ (X - C r)) := by
        unfold HasPosLeadingCoeff at hf ⊢
        rw [leadingCoeff_divByMonic_X_sub_C hrfroot]; exact hf
      have hg₁ : HasPosLeadingCoeff (g /ₘ (X - C r)) := by
        unfold HasPosLeadingCoeff at hg ⊢
        rw [leadingCoeff_divByMonic_X_sub_C hrgroot]; exact hg
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
      have hf₁ : HasPosLeadingCoeff (f /ₘ (X - C r)) := by
        unfold HasPosLeadingCoeff at hf ⊢
        rw [leadingCoeff_divByMonic_X_sub_C hrf]; exact hf
      have hg₁ : HasPosLeadingCoeff (g /ₘ (X - C r)) := by
        unfold HasPosLeadingCoeff at hg ⊢
        rw [leadingCoeff_divByMonic_X_sub_C hrg]; exact hg
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
