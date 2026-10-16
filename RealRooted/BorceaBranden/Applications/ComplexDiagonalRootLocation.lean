import RealRooted.BorceaBranden.Applications.QuadraticExponentialMultiplier
import RealRooted.BorceaBranden.Applications.BidiagonalSymbol
import RealRooted.HermiteBiehler.Basic
import RealRooted.Mathlib.Analysis.Complex.Polynomial.RootsOpen

/-!
# Complex diagonal multipliers and upper-half-plane roots
-/

open Polynomial

namespace RealRooted.BorceaBranden

noncomputable section

/-- Apply a real diagonal sequence to a complex polynomial. -/
def realDiagonalOperator (gamma : ℕ → ℝ) (p : ℂ[X]) : ℂ[X] :=
  complexDiagonalOperator (fun n => (gamma n : ℂ)) p

@[simp]
theorem coeff_realDiagonalOperator (gamma : ℕ → ℝ) (p : ℂ[X])
    (n : ℕ) :
    (realDiagonalOperator gamma p).coeff n =
      (gamma n : ℂ) * p.coeff n := by
  classical
  exact coeff_complexDiagonalOperator _ p n

theorem realDiagonalOperator_ne_zero {gamma : ℕ → ℝ}
    (hgamma : ∀ n, gamma n ≠ 0) {p : ℂ[X]} (hp : p ≠ 0) :
    realDiagonalOperator gamma p ≠ 0 := by
  intro hzero
  apply hp
  ext n
  have hcoeff := congrArg (fun r : ℂ[X] => r.coeff n) hzero
  simp only [coeff_realDiagonalOperator, coeff_zero] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left (by exact_mod_cast hgamma n)

theorem natDegree_realDiagonalOperator_le (gamma : ℕ → ℝ)
    (p : ℂ[X]) :
    (realDiagonalOperator gamma p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_realDiagonalOperator,
    coeff_eq_zero_of_natDegree_lt hn, mul_zero]

private theorem uniqueAlgEquiv_realDiagonalOperator
    (gamma : ℕ → ℝ) (p : ℂ[X]) :
    (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
        (realDiagonalOperator gamma p) =
      coordinateDiagonalOperator gamma 0
        ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm p) := by
  ext m
  rw [MvPolynomial.coeff_uniqueAlgEquiv_symm,
    coeff_realDiagonalOperator, coeff_coordinateDiagonalOperator,
    MvPolynomial.coeff_uniqueAlgEquiv_symm]
  congr 2

private theorem degreeOf_uniqueAlgEquiv_symm_le_natDegree (p : ℂ[X]) :
    ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm p).degreeOf 0 ≤
      p.natDegree := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro m hm
  apply Polynomial.le_natDegree_of_ne_zero
  have hm0 := MvPolynomial.mem_support_iff.mp hm
  rwa [MvPolynomial.coeff_uniqueAlgEquiv_symm] at hm0

/-- A PF multiplier preserves univariate upper-half-plane stability, with a
possible zero output. -/
theorem IsPFMultiplierSequence.isUpperHalfPlaneStableOrZero_complexDiagonal
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma)
    {p : ℂ[X]} (hp : IsUpperHalfPlaneStable p) :
    realDiagonalOperator gamma p = 0 ∨
      IsUpperHalfPlaneStable (realDiagonalOperator gamma p) := by
  have hpMv := (isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable p).mp hp
  have hout :=
    IsPFMultiplierSequence.coordinateDiagonalOperator_preserves_stability
      hgamma p.natDegree 0
      (degreeOf_uniqueAlgEquiv_symm_le_natDegree p) hpMv
  rw [← uniqueAlgEquiv_realDiagonalOperator] at hout
  rcases hout with hzero | hstable
  · left
    exact (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm.injective
      (by simpa using hzero)
  · right
    exact (isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable _).mpr hstable

/-- A nowhere-zero PF multiplier preserves univariate upper-half-plane
stability. -/
theorem IsPFMultiplierSequence.isUpperHalfPlaneStable_complexDiagonal
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma)
    (hgamma0 : ∀ n, gamma n ≠ 0) {p : ℂ[X]}
    (hp : IsUpperHalfPlaneStable p) :
    IsUpperHalfPlaneStable (realDiagonalOperator gamma p) := by
  rcases IsPFMultiplierSequence.isUpperHalfPlaneStableOrZero_complexDiagonal
      hgamma hp with
      hzero | hstable
  · have hp0 : p ≠ 0 := by
      intro hpzero
      subst p
      exact (hp Complex.I (by simp)) (by simp)
    exact (realDiagonalOperator_ne_zero hgamma0 hp0 hzero).elim
  · exact hstable

private theorem realDiagonalOperator_comp_neg_X
    (gamma : ℕ → ℝ) (p : ℂ[X]) :
    realDiagonalOperator gamma (p.comp (-X)) =
      (realDiagonalOperator gamma p).comp (-X) := by
  ext n
  simp only [coeff_realDiagonalOperator, Polynomial.coeff_comp_neg_X]
  ring

private theorem isUpperHalfPlaneStable_comp_neg_X_of_roots_im_nonneg
    {p : ℂ[X]} (hp : p ≠ 0)
    (hroots : ∀ z ∈ p.roots, 0 ≤ z.im) :
    IsUpperHalfPlaneStable (p.comp (-X)) := by
  intro z hz hzero
  have hroot : -z ∈ p.roots := by
    rw [mem_roots hp, IsRoot.def]
    simpa [Polynomial.eval_comp] using hzero
  have := hroots (-z) hroot
  simp only [Complex.neg_im] at this
  linarith

/-- A nowhere-zero PF multiplier sends polynomials whose roots lie in the
closed upper half-plane to polynomials with the same root location. -/
theorem IsPFMultiplierSequence.roots_im_nonneg_complexDiagonal
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma)
    (hgamma0 : ∀ n, gamma n ≠ 0) {p : ℂ[X]} (hp : p ≠ 0)
    (hroots : ∀ z ∈ p.roots, 0 ≤ z.im) :
    ∀ z ∈ (realDiagonalOperator gamma p).roots, 0 ≤ z.im := by
  have hreflected :=
    IsPFMultiplierSequence.isUpperHalfPlaneStable_complexDiagonal
      hgamma hgamma0
      (isUpperHalfPlaneStable_comp_neg_X_of_roots_im_nonneg hp hroots)
  rw [realDiagonalOperator_comp_neg_X] at hreflected
  intro z hz
  by_contra hnonneg
  have hzneg : z.im < 0 := lt_of_not_ge hnonneg
  have hroot := Polynomial.isRoot_of_mem_roots hz
  apply hreflected (-z) (by simpa)
  simpa [Polynomial.eval_comp, Polynomial.IsRoot.def] using hroot

/-- The quadratic exponential multiplier preserves closed upper-half-plane
root location. -/
theorem roots_im_nonneg_quadraticExponentialMultiplier {t : ℝ}
    (ht : 0 ≤ t) {p : ℂ[X]} (hp : p ≠ 0)
    (hroots : ∀ z ∈ p.roots, 0 ≤ z.im) :
    ∀ z ∈
        (realDiagonalOperator
          (quadraticExponentialMultiplier t) p).roots,
      0 ≤ z.im :=
  IsPFMultiplierSequence.roots_im_nonneg_complexDiagonal
    (isPFMultiplierSequence_quadraticExponentialMultiplier ht)
    (fun _ => Real.exp_ne_zero _) hp hroots

private theorem realDiagonalOperator_inverse (gamma : ℕ → ℝ)
    (hgamma : ∀ n, gamma n ≠ 0) (p : ℂ[X]) :
    realDiagonalOperator gamma
        (realDiagonalOperator (fun n => (gamma n)⁻¹) p) = p := by
  ext n
  simp only [coeff_realDiagonalOperator]
  push_cast
  have hn : (gamma n : ℂ) ≠ 0 := by exact_mod_cast hgamma n
  field_simp

private theorem continuous_coeff_comp_X_add_C_complex (p : ℂ[X])
    (i : ℕ) :
    Continuous fun z : ℂ => (p.comp (X + C z)).coeff i := by
  rw [show (fun z : ℂ => (p.comp (X + C z)).coeff i) =
      fun z : ℂ => ∑ n ∈ p.support,
        (C (p.coeff n) * (X + C z) ^ n).coeff i by
    funext z
    rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def,
      Polynomial.finsetSum_coeff]]
  apply continuous_finsetSum p.support
  intro n _hn
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  fun_prop

private def shiftedPreimage (gamma : ℕ → ℝ) (p : ℂ[X])
    (r : ℝ) : ℂ[X] :=
  realDiagonalOperator (fun n => (gamma n)⁻¹)
    (p.comp (X + C ((r : ℂ) * Complex.I)))

private theorem tendsto_coeff_shiftedPreimage (gamma : ℕ → ℝ)
    (hgamma : ∀ n, gamma n ≠ 0) (f : ℂ[X]) (j : ℕ) :
    Filter.Tendsto
        (fun n : ℕ =>
          (shiftedPreimage gamma (realDiagonalOperator gamma f)
            (1 / (n + 1 : ℝ))).coeff j)
        Filter.atTop (nhds (f.coeff j)) := by
  have heps : Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)))
      Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have harg : Filter.Tendsto
      (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ) * Complex.I)
      Filter.atTop (nhds 0) := by
    simpa using ((Complex.continuous_ofReal.tendsto 0).comp heps).mul_const
      Complex.I
  have hshift :=
    (continuous_coeff_comp_X_add_C_complex
      (realDiagonalOperator gamma f) j).tendsto 0 |>.comp harg
  have hshift' : Filter.Tendsto
      (fun n : ℕ =>
        ((realDiagonalOperator gamma f).comp
          (X + C (((1 / (n + 1 : ℝ) : ℝ) : ℂ) * Complex.I))).coeff j)
      Filter.atTop (nhds ((realDiagonalOperator gamma f).coeff j)) := by
    change Filter.Tendsto
      (fun n : ℕ =>
        ((realDiagonalOperator gamma f).comp
          (X + C (((1 / (n + 1 : ℝ) : ℝ) : ℂ) * Complex.I))).coeff j)
      Filter.atTop
      (nhds (((realDiagonalOperator gamma f).comp (X + C 0)).coeff j))
      at hshift
    simpa using hshift
  have hscaled := (tendsto_const_nhds.mul hshift' : Filter.Tendsto
    (fun n : ℕ => ((gamma j : ℂ)⁻¹) *
      ((realDiagonalOperator gamma f).comp
        (X + C (((1 / (n + 1 : ℝ) : ℝ) : ℂ) * Complex.I))).coeff j)
    Filter.atTop (nhds (((gamma j : ℂ)⁻¹) *
      (realDiagonalOperator gamma f).coeff j)))
  simpa [shiftedPreimage, coeff_realDiagonalOperator, hgamma j]
    using hscaled

private theorem natDegree_shiftedPreimage_le (gamma : ℕ → ℝ)
    (p : ℂ[X]) (r : ℝ) :
    (shiftedPreimage gamma p r).natDegree ≤ p.natDegree := by
  refine (natDegree_realDiagonalOperator_le _ _).trans ?_
  calc
    (p.comp (X + C ((r : ℂ) * Complex.I))).natDegree ≤
        p.natDegree * (X + C ((r : ℂ) * Complex.I)).natDegree :=
      Polynomial.natDegree_comp_le
    _ = p.natDegree := by
      rw [Polynomial.natDegree_X_add_C, Nat.mul_one]

/-- A nowhere-zero PF multiplier preserves the open upper root half-plane. -/
theorem IsPFMultiplierSequence.roots_im_pos_complexDiagonal
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma)
    (hgamma0 : ∀ n, gamma n ≠ 0) {f : ℂ[X]} (hf : f ≠ 0)
    (hroots : ∀ z ∈ f.roots, 0 < z.im) :
    ∀ z ∈ (realDiagonalOperator gamma f).roots, 0 < z.im := by
  let Tf := realDiagonalOperator gamma f
  have hTf0 : Tf ≠ 0 := realDiagonalOperator_ne_zero hgamma0 hf
  have hweak : ∀ z ∈ Tf.roots, 0 ≤ z.im :=
    IsPFMultiplierSequence.roots_im_nonneg_complexDiagonal hgamma
      hgamma0 hf (fun z hz => (hroots z hz).le)
  intro z hz
  have hznonneg := hweak z hz
  by_contra hzpos
  have hzim : z.im = 0 := le_antisymm (le_of_not_gt hzpos) hznonneg
  obtain ⟨δ, hδ, hopenδ⟩ :=
    Polynomial.roots_im_pos_of_coeff_near hf hroots
  have hclose : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ j ∈ Finset.range (f.natDegree + 1),
        ‖(shiftedPreimage gamma Tf (1 / (n + 1 : ℝ))).coeff j -
          f.coeff j‖ < δ := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have htend := tendsto_coeff_shiftedPreimage gamma hgamma0 f j
    have hmetric := Metric.tendsto_nhds.mp htend δ hδ
    filter_upwards [hmetric] with n hn
    simpa [dist_eq_norm] using hn
  obtain ⟨n, hn⟩ := hclose.exists
  let r : ℝ := 1 / (n + 1 : ℝ)
  let g : ℂ[X] := shiftedPreimage gamma Tf r
  have hr : 0 < r := by positivity
  have hgdeg : g.natDegree ≤ f.natDegree :=
    (natDegree_shiftedPreimage_le gamma Tf r).trans
      (natDegree_realDiagonalOperator_le gamma f)
  have hgclose : ∀ j ≤ f.natDegree,
      ‖g.coeff j - f.coeff j‖ < δ := by
    intro j hj
    exact hn j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  have hgroots : ∀ w ∈ g.roots, 0 < w.im :=
    hopenδ g hgdeg hgclose
  have hshift0 : Tf.comp (X + C ((r : ℂ) * Complex.I)) ≠ 0 :=
    Polynomial.comp_X_add_C_ne_zero_iff.mpr hTf0
  have hg0 : g ≠ 0 := by
    exact realDiagonalOperator_ne_zero
      (fun j => inv_ne_zero (hgamma0 j)) hshift0
  have hgweak :=
    IsPFMultiplierSequence.roots_im_nonneg_complexDiagonal hgamma
      hgamma0 hg0 (fun w hw => (hgroots w hw).le)
  have hTg : realDiagonalOperator gamma g =
      Tf.comp (X + C ((r : ℂ) * Complex.I)) := by
    exact realDiagonalOperator_inverse gamma hgamma0 _
  let w : ℂ := z - (r : ℂ) * Complex.I
  have hzroot : Tf.IsRoot z := by
    simpa [Tf] using Polynomial.isRoot_of_mem_roots hz
  have hweval :
      (Tf.comp (X + C ((r : ℂ) * Complex.I))).eval w = 0 := by
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    rw [show w + (r : ℂ) * Complex.I = z by simp [w]]
    exact hzroot
  have hwroot : w ∈ (realDiagonalOperator gamma g).roots := by
    rw [mem_roots (realDiagonalOperator_ne_zero hgamma0 hg0),
      Polynomial.IsRoot.def, hTg]
    exact hweval
  have hwim := hgweak w hwroot
  have hwim_eq : w.im = -r := by
    simp [w, hzim]
  exact (not_lt_of_ge hwim) (hwim_eq.symm ▸ neg_neg_of_pos hr)


end

end RealRooted.BorceaBranden
