import RealRooted.Bezoutian
import RealRooted.HermiteBiehler.Converse.RootGeometry

/-!
# Wronskian layer for the converse Hermite--Biehler theorem

This file converts upper-half-plane root geometry into Wronskian positivity and
then into same-degree or successor-degree proper position. The later common-root
induction and ratio endpoints build on this layer.
-/

open Polynomial

noncomputable section

namespace RealRooted

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
  have hlc : p.leadingCoeff ≠ 0 := fun h =>
    hne (by rw [eval_eq_prod_roots_complex, h, zero_mul])
  have hprod : ((p.roots.erase w₀).map (fun u => (x : ℂ) - u)).prod ≠ 0 :=
    right_ne_zero_of_mul (a := (x : ℂ) - w₀) (by
      rw [Multiset.prod_map_erase hw₀]
      exact fun h => hne (by rw [eval_eq_prod_roots_complex, h, mul_zero]))
  rw [im_deriv_mul_conj_eq, ← Multiset.sum_map_erase hw₀]
  refine mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hlc) ?_
  have hterm : Complex.normSq
      ((p.roots.erase w₀).map (fun u => (x : ℂ) - u)).prod * w₀.im < 0 :=
    mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hprod) hneg
  have hrest : ((p.roots.erase w₀).map (fun w =>
      Complex.normSq ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod * w.im)).sum ≤ 0 := by
    refine multiset_sum_nonpos _ fun y hy => ?_
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
    exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _)
      (hroots w (Multiset.mem_of_mem_erase hw))
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
  exact hnc ⟨t, by simpa using congrArg Complex.re ht,
    by simpa using congrArg Complex.im ht⟩

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

end RealRooted
