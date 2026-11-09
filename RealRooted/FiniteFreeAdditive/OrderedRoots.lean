module

public import RealRooted.FiniteFreeAdditive
import RealRooted.FiniteFreeAdditive.Preservation
import RealRooted.FiniteFreeAdditive.RootWindow
import RealRooted.Linear
public import RealRooted.OrderedRoots
import RealRooted.OperatorInterlacingUpgrade.RootOrder
import RealRooted.OperatorPreservesInterlacing
public import RealRooted.RootLocation.Basic

/-!
# Ordered roots of finite-free additive convolution

This module proves the coordinatewise Weyl bounds for finite-free additive
convolution.  Convolution by a fixed split polynomial preserves full-degree
one-root moves; the orientation left ambiguous by Obreschkoff's theorem is
resolved by the additive formula for the sum of the roots.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

private theorem finiteFreeAdditiveConvolution_add_right
    (d : ℕ) (p q r : ℝ[X]) :
    finiteFreeAdditiveConvolution d p (q + r) =
      finiteFreeAdditiveConvolution d p q +
        finiteFreeAdditiveConvolution d p r := by
  ext j
  simp only [coeff_add, coeff_finiteFreeAdditiveConvolution]
  split_ifs
  · simp only [finiteFreeAdditiveConvolutionCoeff, coeff_add, mul_add,
      Finset.sum_add_distrib]
  · simp

private def finiteFreeAdditiveConvolutionRightLinearMap
    (d : ℕ) (p : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun q := finiteFreeAdditiveConvolution d p q
  map_add' q r := finiteFreeAdditiveConvolution_add_right d p q r
  map_smul' c q := by
    simpa [smul_eq_C_mul] using
      finiteFreeAdditiveConvolution_C_mul_right d c p q

private theorem finiteFreeAdditiveConvolutionGamma_zero_one
    (d : ℕ) :
    finiteFreeAdditiveConvolutionGamma d 0 1 = 1 := by
  unfold finiteFreeAdditiveConvolutionGamma
  simp only [Nat.sub_zero]
  have hfac : ((d.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hpred : (((d - 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

private theorem finiteFreeAdditiveConvolution_coeff_pred
    {d : ℕ} (hd : d ≠ 0) (p q : ℝ[X]) :
    (finiteFreeAdditiveConvolution d p q).coeff (d - 1) =
      p.coeff (d - 1) * q.coeff d + p.coeff d * q.coeff (d - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  rw [coeff_finiteFreeAdditiveConvolution_of_le _ _ _ (by lia)]
  rw [show d.succ - (d.succ - 1) = 1 by lia]
  simp only [finiteFreeAdditiveConvolutionCoeff, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self]
  rw [finiteFreeAdditiveConvolutionGamma_zero_one,
    finiteFreeAdditiveConvolutionGamma_symm,
    finiteFreeAdditiveConvolutionGamma_zero_one]
  simp
  ring

private theorem roots_sum_finiteFreeAdditiveConvolution
    {d : ℕ} (hd : d ≠ 0) {p q : ℝ[X]}
    (hpd : p.natDegree = d) (hqd : q.natDegree = d)
    (hp : p.Splits) (hq : q.Splits)
    (hout : (finiteFreeAdditiveConvolution d p q).Splits) :
    (finiteFreeAdditiveConvolution d p q).roots.sum =
      p.roots.sum + q.roots.sum := by
  have hp0 : p ≠ 0 := by
    intro hp0
    simp [hp0] at hpd
    exact hd hpd.symm
  have hq0 : q ≠ 0 := by
    intro hq0
    simp [hq0] at hqd
    exact hd hqd.symm
  have houtdeg := natDegree_finiteFreeAdditiveConvolution_eq d hpd hqd hp0 hq0
  have hp_vieta := hp.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hq_vieta := hq.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hout_vieta := hout.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [Polynomial.nextCoeff, hpd, Polynomial.leadingCoeff, hpd] at hp_vieta
  rw [Polynomial.nextCoeff, hqd, Polynomial.leadingCoeff, hqd] at hq_vieta
  rw [Polynomial.nextCoeff, houtdeg, Polynomial.leadingCoeff, houtdeg,
    finiteFreeAdditiveConvolution_coeff_pred hd,
    coeff_finiteFreeAdditiveConvolution_top] at hout_vieta
  simp only [hd, ↓reduceIte] at hp_vieta hq_vieta hout_vieta
  have hp_top : p.coeff d ≠ 0 := by
    rw [← hpd, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hq_top : q.coeff d ≠ 0 := by
    rw [← hqd, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq0
  apply mul_left_cancel₀ (mul_ne_zero hp_top hq_top)
  calc
    p.coeff d * q.coeff d *
          (finiteFreeAdditiveConvolution d p q).roots.sum =
        -(p.coeff (d - 1) * q.coeff d +
          p.coeff d * q.coeff (d - 1)) := by
      linarith
    _ = p.coeff d * q.coeff d * (p.roots.sum + q.roots.sum) := by
      rw [hp_vieta, hq_vieta]
      ring

private theorem finiteFreeAdditiveConvolution_preservesFullDegreeRootMoves
    {d : ℕ} (hd : d ≠ 0) {p : ℝ[X]}
    (hpd : p.natDegree = d) (hp : p.Splits) :
    PreservesFullDegreeRootMoves d
      (fun q => finiteFreeAdditiveConvolution d p q) := by
  have hp0 : p ≠ 0 := by
    intro hp0
    simp [hp0] at hpd
    exact hd hpd.symm
  constructor
  · intro q hqd
    have hq0 : q ≠ 0 := by
      intro hq0
      simp [hq0] at hqd
      exact hd hqd.symm
    exact natDegree_finiteFreeAdditiveConvolution_eq d hpd hqd hp0 hq0
  · intro f g hfd hgd hfg
    have hf0 : f ≠ 0 := hfg.1.1
    have hg0 : g ≠ 0 := hfg.2.1.1
    have hTf0 := finiteFreeAdditiveConvolution_ne_zero_of_natDegree_eq
      d hpd hfd hp0 hf0
    have hTg0 := finiteFreeAdditiveConvolution_ne_zero_of_natDegree_eq
      d hpd hgd hp0 hg0
    have hTfdeg := natDegree_finiteFreeAdditiveConvolution_eq
      d hpd hfd hp0 hf0
    have hTgdeg := natDegree_finiteFreeAdditiveConvolution_eq
      d hpd hgd hp0 hg0
    have horient := interl_or_reverse_map_of_pencil
      (T := finiteFreeAdditiveConvolutionRightLinearMap d p)
      (allComboRealRooted_of_strictInterl hfg) (fun a b hab => by
        apply Or.inr
        apply splits_finiteFreeAdditiveConvolution d hp hab.2 hpd.le
        exact (Polynomial.natDegree_add_le _ _).trans <| max_le
          ((Polynomial.natDegree_C_mul_le a f).trans hfd.le)
          ((Polynomial.natDegree_C_mul_le b g).trans hgd.le))
    rcases horient with hforward | hreverse
    · exact hforward.toStrictInterl_of_ne hTf0 hTg0
    · have hreverse' := hreverse.toStrictInterl_of_ne hTg0 hTf0
      change StrictInterl (finiteFreeAdditiveConvolution d p g)
        (finiteFreeAdditiveConvolution d p f) at hreverse'
      apply hreverse'.of_reverse_of_roots_sum_le
        (hTfdeg.trans hTgdeg.symm)
      rw [roots_sum_finiteFreeAdditiveConvolution hd hpd hfd hp hfg.1.2
          (splits_finiteFreeAdditiveConvolution d hp hfg.1.2 hpd.le hfd.le),
        roots_sum_finiteFreeAdditiveConvolution hd hpd hgd hp hfg.2.1.2
          (splits_finiteFreeAdditiveConvolution d hp hfg.2.1.2 hpd.le hgd.le)]
      exact add_le_add_right
        (hfg.roots_sum_le_of_sameDegree (hfd.trans hgd.symm)) _

private theorem finiteFreeAdditiveConvolution_X_pow_right
    (d : ℕ) {p : ℝ[X]} (hpd : p.natDegree ≤ d) :
    finiteFreeAdditiveConvolution d p (X ^ d) = p := by
  rw [finiteFreeAdditiveConvolution_comm,
    finiteFreeAdditiveConvolution_eq_sum_iterate_derivative d (X ^ d) hpd]
  rw [Finset.sum_eq_single 0]
  · have hfac : (d.factorial : ℝ) ≠ 0 := by positivity
    simp [hfac]
  · intro i hi hi0
    have hi_le : i ≤ d := by simpa using hi
    have hne : d - i ≠ d := by lia
    simp [coeff_X_pow, hne]
  · simp

private theorem finiteFreeAdditiveConvolution_pow_X_sub_C_right
    (d : ℕ) {p : ℝ[X]} (hpd : p.natDegree ≤ d) (c : ℝ) :
    finiteFreeAdditiveConvolution d p ((X - C c) ^ d) =
      p.comp (X - C c) := by
  have hpow : (X - C c) ^ d = (X ^ d).comp (X + C (-c)) := by
    simp [sub_eq_add_neg]
  rw [hpow, finiteFreeAdditiveConvolution_comp_X_add_C_right d p
      (by simp) (-c), finiteFreeAdditiveConvolution_X_pow_right d hpd]
  simp [sub_eq_add_neg]

private theorem roots_comp_X_sub_C (p : ℝ[X]) (c : ℝ) :
    (p.comp (X - C c)).roots = p.roots.map (fun x => x + c) := by
  rw [show X - C c = X + C (-c) by simp [sub_eq_add_neg],
    roots_comp_X_add_C]
  simp

private theorem sort_roots_comp_X_sub_C (p : ℝ[X]) (c : ℝ) :
    (p.comp (X - C c)).roots.sort (· ≤ ·) =
      (p.roots.sort (· ≤ ·)).map (fun x => x + c) := by
  have hrs : (p.roots.sort (· ≤ ·)).Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort p.roots (· ≤ ·)
  have hmap : ((p.roots.sort (· ≤ ·)).map
      (fun x => x + c)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact hrs.imp (by intro x y hxy; linarith)
  apply List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) hmap
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq, roots_comp_X_sub_C, ← Multiset.map_coe,
    Multiset.sort_eq]

private theorem orderedRoot_comp_X_sub_C
    (p : ℝ[X]) {n : ℕ} (hcard : p.roots.card = n)
    (c : ℝ) (i : Fin n) :
    orderedRoot (p.comp (X - C c)) n i = orderedRoot p n i + c := by
  have hi : (i : ℕ) < (p.roots.sort (· ≤ ·)).length := by
    rw [Multiset.length_sort, hcard]
    exact i.2
  unfold orderedRoot
  rw [sort_roots_comp_X_sub_C]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [List.getElem?_eq_getElem hi]
  simp

private theorem RootwiseLE.orderedRoot_le
    {p q : ℝ[X]} (h : RootwiseLE p q) {n : ℕ}
    (hp : p.roots.card = n) (hq : q.roots.card = n) (i : Fin n) :
    orderedRoot p n i ≤ orderedRoot q n i := by
  have hip : i.val < (p.roots.sort (· ≤ ·)).length := by
    simpa using i.2.trans_eq hp.symm
  have hiq : i.val < (q.roots.sort (· ≤ ·)).length := by
    simpa using i.2.trans_eq hq.symm
  unfold orderedRoot
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hip, List.getElem?_eq_getElem hiq]
  simpa using h.get hip hiq

/-- **Ordered-root Weyl bounds for finite-free additive convolution.**
If the roots of `q` lie in `[a, b]`, then its convolution with `p` moves the
`i`th ordered root of `p` by an amount between `a` and `b`. -/
theorem orderedRoot_finiteFreeAdditiveConvolution_bounds
    {d : ℕ} {p q : ℝ[X]} {a b : ℝ}
    (hpd : p.natDegree = d) (hqd : q.natDegree = d)
    (hp : p ≠ 0 ∧ p.Splits) (hq : IsRealRootedIn (Set.Icc a b) q)
    (i : Fin d) :
    orderedRoot p d i + a ≤
        orderedRoot (finiteFreeAdditiveConvolution d p q) d i ∧
      orderedRoot (finiteFreeAdditiveConvolution d p q) d i ≤
        orderedRoot p d i + b := by
  have hd : d ≠ 0 := by lia [i.isLt]
  have hqlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq.ne_zero
  let qMonic : ℝ[X] := C q.leadingCoeff⁻¹ * q
  have hqMonic : qMonic.Monic := by
    dsimp [qMonic]
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ hqlc
  have hqMonic_splits : qMonic.Splits := hq.splits.C_mul q.leadingCoeff⁻¹
  have hqMonic_deg : qMonic.natDegree = d := by
    dsimp [qMonic]
    rw [natDegree_C_mul (inv_ne_zero hqlc), hqd]
  have hqMonic_roots : qMonic.roots = q.roots := by
    dsimp [qMonic]
    exact roots_C_mul q (inv_ne_zero hqlc)
  have hbounds :=
    (finiteFreeAdditiveConvolution_preservesFullDegreeRootMoves hd hpd hp.2).rootwiseLE_bounds
      hqMonic hqMonic_splits hqMonic_deg
      (a := -b) (b := -a)
      (by
        intro r hr
        rw [hqMonic_roots] at hr
        linarith [hq.mem_of_mem_roots hr |>.1])
      (by
        intro r hr
        rw [hqMonic_roots] at hr
        linarith [hq.mem_of_mem_roots hr |>.2])
  have hscale : finiteFreeAdditiveConvolution d p qMonic =
      C q.leadingCoeff⁻¹ * finiteFreeAdditiveConvolution d p q := by
    dsimp [qMonic]
    exact finiteFreeAdditiveConvolution_C_mul_right d _ p q
  have hconv_deg := natDegree_finiteFreeAdditiveConvolution_eq
    d hpd hqd hp.1 hq.ne_zero
  have hconv_splits := splits_finiteFreeAdditiveConvolution
    d hp.2 hq.splits hpd.le hqd.le
  have hp_card : p.roots.card = d := by
    rw [Polynomial.splits_iff_card_roots.mp hp.2, hpd]
  have hconv_card : (finiteFreeAdditiveConvolution d p q).roots.card = d := by
    rw [Polynomial.splits_iff_card_roots.mp hconv_splits, hconv_deg]
  have hscale_roots :
      (finiteFreeAdditiveConvolution d p qMonic).roots =
        (finiteFreeAdditiveConvolution d p q).roots := by
    rw [hscale, roots_C_mul _ (inv_ne_zero hqlc)]
  have hleft := hbounds.1
  have hright := hbounds.2
  rw [show X + C (-a) = X - C a by simp [sub_eq_add_neg],
    finiteFreeAdditiveConvolution_pow_X_sub_C_right d hpd.le] at hleft
  rw [
    show X + C (-b) = X - C b by simp [sub_eq_add_neg],
    finiteFreeAdditiveConvolution_pow_X_sub_C_right d hpd.le] at hright
  have hleft' : RootwiseLE (p.comp (X - C a))
      (finiteFreeAdditiveConvolution d p q) := by
    unfold RootwiseLE at hleft ⊢
    rwa [hscale_roots] at hleft
  have hright' : RootwiseLE (finiteFreeAdditiveConvolution d p q)
      (p.comp (X - C b)) := by
    unfold RootwiseLE at hright ⊢
    rwa [hscale_roots] at hright
  constructor
  · rw [← orderedRoot_comp_X_sub_C p hp_card a i]
    exact hleft'.orderedRoot_le
      (by simp [roots_comp_X_sub_C, hp_card]) hconv_card i
  · rw [← orderedRoot_comp_X_sub_C p hp_card b i]
    exact hright'.orderedRoot_le hconv_card
      (by simp [roots_comp_X_sub_C, hp_card]) i

end RealRooted
