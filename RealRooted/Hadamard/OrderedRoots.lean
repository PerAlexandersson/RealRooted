module

public import RealRooted.FiniteFreeRootCount
public import RealRooted.Hadamard.RootIntervals
public import RealRooted.OrderedRoots
import RealRooted.OperatorInterlacingUpgrade.RootOrder
import RealRooted.Hadamard.SchurSzegoStrict
import RealRooted.Hadamard.SchurSzegoSigns
import RealRooted.LinearPowerFamily

/-!
# Ordered roots of Schur--Szegő compositions

For an input `f` rooted in `[-v, -u]`, fixed-right-factor Schur--Szegő composition moves
the `i`th root between the images of the repeated-root endpoints.  After reducing the fixed
factor `G` to the degree of `f`, these endpoint roots are `v βᵢ` and `u βᵢ`.
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- Coordinatewise root order bounds the corresponding canonically ordered roots. -/
theorem RootwiseLE.orderedRoot_le {p q : ℝ[X]} {n : ℕ} (h : RootwiseLE p q)
    (hp : p.Splits) (hq : q.Splits) (hpdeg : p.natDegree = n)
    (hqdeg : q.natDegree = n) (i : Fin n) :
    orderedRoot p n i ≤ orderedRoot q n i := by
  have hpLen : (p.roots.sort (· ≤ ·)).length = n := by
    simp [Polynomial.splits_iff_card_roots.mp hp, hpdeg]
  have hqLen : (q.roots.sort (· ≤ ·)).length = n := by
    simp [Polynomial.splits_iff_card_roots.mp hq, hqdeg]
  unfold RootwiseLE at h
  unfold orderedRoot
  rw [List.getD_eq_getElem _ _ (hpLen.trans_gt i.isLt),
    List.getD_eq_getElem _ _ (hqLen.trans_gt i.isLt)]
  exact h.get (hpLen.trans_gt i.isLt) (hqLen.trans_gt i.isLt)

/-- Positive rescaling of the variable divides every ordered root by the scale. -/
theorem orderedRoot_comp_C_mul_X {p : ℝ[X]} {n : ℕ} {a : ℝ} (ha : 0 < a)
    (i : Fin n) :
    orderedRoot (p.comp (C a * X)) n i = a⁻¹ * orderedRoot p n i := by
  have haUnit : IsUnit a := isUnit_iff_ne_zero.mpr ha.ne'
  have hsort :
      (p.roots.sort (· ≤ ·)).map (a⁻¹ * ·) =
        (p.roots.map (a⁻¹ * ·)).sort (· ≤ ·) := by
    apply Multiset.map_sort
    intro x hx y hy
    simpa [mul_comm] using (mul_le_mul_iff_left₀ (inv_pos.mpr ha)).symm
  rw [orderedRoot, orderedRoot, show C a * X = C a * X + C 0 by simp,
    Polynomial.roots_comp_C_mul_X_add_C p a 0 haUnit]
  simp only [sub_zero]
  simp only [Ring.inverse_eq_inv]
  rw [← hsort]
  simpa using
    (List.getD_map (l := p.roots.sort (· ≤ ·)) (d := 0) (n := i)
      (fun x => a⁻¹ * x))

private theorem schurSzegoComp_X_add_C_pow (m : ℕ) (H : ℝ[X])
    (hHdeg : H.natDegree ≤ m) {c : ℝ} (hc : 0 < c) :
    schurSzegoComp m ((X + C c) ^ m) H =
      C (c ^ m) * H.comp (C c⁻¹ * X) := by
  ext k
  rw [coeff_schurSzegoComp, coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
    Polynomial.coeff_X_add_C_pow]
  by_cases hk : k ≤ m
  · simp only [hk, ite_true]
    have hchoose : (m.choose k : ℝ) ≠ 0 := Nat.cast_choose_ne_zero hk
    field_simp [hchoose]
    rw [pow_sub₀ c hc.ne' hk]
    simp only [one_div, inv_pow]
    ring
  · have hHk : H.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (hHdeg.trans_lt (Nat.lt_of_not_ge hk))
    simp [hk, hHk]

private theorem orderedRoot_schurSzegoComp_X_add_C_pow
    {m : ℕ} {H : ℝ[X]} (hHdeg : H.natDegree = m) (hH0 : H ≠ 0)
    {c : ℝ} (hc : 0 ≤ c) (i : Fin m) :
    orderedRoot (schurSzegoComp m ((X + C c) ^ m) H) m i =
      c * orderedRoot H m i := by
  rcases hc.eq_or_lt with rfl | hc'
  · have htop : H.coeff m ≠ 0 := by
      rw [← hHdeg, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hH0
    have hpoly : schurSzegoComp m (X ^ m) H = C (H.coeff m) * X ^ m := by
      ext k
      by_cases hkm : k = m
      · subst k
        simp [coeff_schurSzegoComp]
      · simp [coeff_schurSzegoComp, coeff_X_pow, hkm]
    rw [show (X + C 0 : ℝ[X]) ^ m = X ^ m by simp, hpoly]
    have hcard : (C (H.coeff m) * X ^ m).roots.card = m := by
      rw [roots_C_mul _ htop, roots_X_pow]
      simp
    have hmem := orderedRoot_mem_roots hcard i
    rw [roots_C_mul _ htop, roots_X_pow] at hmem
    have hzero : ¬ m = 0 ∧ orderedRoot (C (H.coeff m) * X ^ m) m i = 0 := by
      simpa using hmem
    simpa using hzero.2
  · rw [schurSzegoComp_X_add_C_pow m H hHdeg.le hc', orderedRoot,
      roots_C_mul _ (pow_ne_zero m hc'.ne'), ← orderedRoot]
    have hscale := orderedRoot_comp_C_mul_X (p := H) (a := c⁻¹) (inv_pos.mpr hc') i
    simpa [inv_inv] using hscale

/-- **Ordered roots of a Schur--Szegő composition.** Let `m = f.natDegree`, let `βᵢ` be
the increasing roots of the reduced factor `schurSzegoReduction D m G`, and let `ρᵢ` be
the increasing roots of `schurSzegoComp D f G`. If the roots of `f` lie in `[-v, -u]`, then
`v βᵢ ≤ ρᵢ ≤ u βᵢ` for every `i`. -/
theorem IsRealRootedIn.orderedRoot_schurSzegoComp_bounds
    {D : ℕ} {f G : ℝ[X]} {a b u v : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hu : 0 ≤ u) (huv : u ≤ v)
    (hf : IsRealRootedIn (Icc (-v) (-u)) f)
    (hG : IsRealRootedIn (Icc (-b) (-a)) G)
    (hfdeg : f.natDegree ≤ D) (hGdeg : G.natDegree = D) :
    ∀ i : Fin f.natDegree,
      v * orderedRoot (schurSzegoReduction D f.natDegree G) f.natDegree i ≤
        orderedRoot (schurSzegoComp D f G) f.natDegree i ∧
      orderedRoot (schurSzegoComp D f G) f.natDegree i ≤
        u * orderedRoot (schurSzegoReduction D f.natDegree G) f.natDegree i := by
  let m := f.natDegree
  let H := schurSzegoReduction D m G
  obtain ⟨hHrooted, hHdeg⟩ := hG.schurSzegoReduction_Icc ha hab hfdeg hGdeg
  have hflc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.ne_zero
  have hHlc : H.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hHrooted.ne_zero
  let p := C f.leadingCoeff⁻¹ * f
  let Q := C H.leadingCoeff⁻¹ * H
  let T := schurSzegoCompRightLinearMap m Q
  change H.natDegree = m at hHdeg
  have hpMonic : p.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ hflc
  have hpdeg : p.natDegree = m := by
    simp [p, m, natDegree_C_mul, hflc]
  have hpSplits : p.Splits := (Splits.C _).mul hf.splits
  have hQMonic : Q.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ hHlc
  have hQdeg : Q.natDegree = m := by
    simp [Q, natDegree_C_mul, hHlc, hHdeg]
  have hQSplits : Q.Splits := (Splits.C _).mul hHrooted.splits
  have hQneg : ∀ r ∈ Q.roots, r < 0 := by
    intro r hr
    change r ∈ (C H.leadingCoeff⁻¹ * H).roots at hr
    rw [roots_C_mul _ (inv_ne_zero hHlc)] at hr
    have hrIcc := hHrooted.mem_of_mem_roots hr
    exact lt_of_le_of_lt hrIcc.2 (neg_neg_of_pos ha)
  have hQpos : HasPosLeadingCoeff Q := hasPosLeadingCoeff_of_monic hQMonic
  have hQnn : HasNonnegCoeffs Q :=
    (hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hQSplits).2
      ⟨hQpos, fun r hr => (hQneg r hr).le⟩ |>.1
  have hQpf : IsPFPolynomial Q :=
    IsPFPolynomial.of_realRooted_nonneg hQnn hQSplits
  have hTdegree : ∀ {q : ℝ[X]}, q.natDegree = m → (T q).natDegree = m := by
    intro q hqdeg
    rw [show T q = schurSzegoComp m q Q by rfl,
      natDegree_schurSzegoComp_of_roots_neg hqdeg.le hQdeg hQSplits hQpos hQneg,
      hqdeg]
  have hTnn : ∀ ⦃q : ℝ[X]⦄, HasNonnegCoeffs q → HasNonnegCoeffs (T q) := by
    intro q hq
    simpa [T] using hq.schurSzegoComp hQnn
  have hTrr : ∀ ⦃q : ℝ[X]⦄, IsPFPolynomial q → q ≠ 0 →
      q.natDegree ≤ m → T q ≠ 0 ∧ (T q).Splits := by
    intro q hq hq0 hqdeg
    constructor
    · simpa [T] using
        schurSzegoComp_ne_zero_of_roots_neg hqdeg hq0 hQdeg hQSplits hQpos hQneg
    · simpa [T] using
        splits_schurSzegoComp_of_roots_neg hqdeg hq.splits hQdeg.le hQSplits hQneg
  have hmap (j : ℕ) (hj : j ≤ m) :
      T (X ^ j) = C (Q.coeff j / (m.choose j : ℝ)) * X ^ j := by
    ext k
    by_cases hkj : k = j
    · subst k
      simp [T, coeff_schurSzegoComp, coeff_X_pow, hj]
    · simp [T, coeff_schurSzegoComp, coeff_X_pow, hkj]
  have hcoeff (j : ℕ) (hj : j ≤ m) : 0 < Q.coeff j / (m.choose j : ℝ) := by
    have hprod := leadingCoeff_mul_coeff_pos_of_roots_neg
      hQSplits hQpos.ne_zero hQneg (hQdeg ▸ hj)
    rw [hQMonic.leadingCoeff, one_mul] at hprod
    exact div_pos hprod (by exact_mod_cast Nat.choose_pos hj)
  have hmono : ∀ j : ℕ, j + 1 ≤ m →
      StrictInterl (T (X ^ j)) (T (X ^ (j + 1))) := by
    intro j hj
    rw [hmap j (by lia), hmap (j + 1) hj]
    exact (strictInterl_X_pow_succ j).C_mul_left (hcoeff j (by lia)).ne'
      |>.C_mul_right (hcoeff (j + 1) hj).ne'
  have hpLo : ∀ r ∈ p.roots, -v ≤ r := by
    intro r hr
    change r ∈ (C f.leadingCoeff⁻¹ * f).roots at hr
    rw [roots_C_mul _ (inv_ne_zero hflc)] at hr
    exact (hf.mem_of_mem_roots hr).1
  have hpHi : ∀ r ∈ p.roots, r ≤ -u := by
    intro r hr
    change r ∈ (C f.leadingCoeff⁻¹ * f).roots at hr
    rw [roots_C_mul _ (inv_ne_zero hflc)] at hr
    exact (hf.mem_of_mem_roots hr).2
  obtain ⟨hlo, hhi⟩ := rootwiseLE_monomialChain_component_bounds hpMonic hpSplits hpdeg
    hu huv hpLo hpHi hTdegree hTnn hTrr hmono
  have hTpdeg : (T p).natDegree = m := hTdegree hpdeg
  have hTpSplits : (T p).Splits := (hTrr
    (IsPFPolynomial.of_realRooted_nonneg
      ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hpSplits).2
        ⟨hasPosLeadingCoeff_of_monic hpMonic, fun r hr =>
          (hpHi r hr).trans (neg_nonpos.mpr hu)⟩ |>.1)
      hpSplits)
    hpMonic.ne_zero hpdeg.le).2
  have hEndpointSplits (c : ℝ) (hc : 0 ≤ c) : (T ((X + C c) ^ m)).Splits := by
    have hpf : IsPFPolynomial ((X + C c) ^ m) := (isPFPolynomial_X_add_C hc).pow m
    exact (hTrr hpf (pow_ne_zero m (X_add_C_ne_zero c)) (by compute_degree)).2
  have hEndpointDeg (c : ℝ) : (T ((X + C c) ^ m)).natDegree = m := by
    apply hTdegree
    simp
  have hTp : T p = C (f.leadingCoeff⁻¹ * H.leadingCoeff⁻¹) *
      schurSzegoComp D f G := by
    change schurSzegoComp m (C f.leadingCoeff⁻¹ * f)
        (C H.leadingCoeff⁻¹ * H) = _
    rw [
      schurSzegoComp_C_mul_left, schurSzegoComp_C_mul_right, ← mul_assoc, ← C_mul,
      schurSzegoComp_eq_schurSzegoComp_reduction hfdeg le_rfl]
  have hTpRoots : (T p).roots = (schurSzegoComp D f G).roots := by
    rw [hTp, roots_C_mul _ (mul_ne_zero (inv_ne_zero hflc) (inv_ne_zero hHlc))]
  have hQRoots : Q.roots = H.roots := by
    change (C H.leadingCoeff⁻¹ * H).roots = H.roots
    rw [roots_C_mul _ (inv_ne_zero hHlc)]
  intro i
  have hloi := hlo.orderedRoot_le (hEndpointSplits v (hu.trans huv)) hTpSplits
    (hEndpointDeg v) hTpdeg i
  have hhii := hhi.orderedRoot_le hTpSplits (hEndpointSplits u hu)
    hTpdeg (hEndpointDeg u) i
  change orderedRoot (schurSzegoComp m ((X + C v) ^ m) Q) m i ≤
      orderedRoot (T p) m i at hloi
  change orderedRoot (T p) m i ≤
      orderedRoot (schurSzegoComp m ((X + C u) ^ m) Q) m i at hhii
  rw [orderedRoot_schurSzegoComp_X_add_C_pow hQdeg hQMonic.ne_zero (hu.trans huv)] at hloi
  rw [orderedRoot_schurSzegoComp_X_add_C_pow hQdeg hQMonic.ne_zero hu] at hhii
  have horderedTp : orderedRoot (T p) m i =
      orderedRoot (schurSzegoComp D f G) m i := by
    simp only [orderedRoot, hTpRoots]
  have horderedQ : orderedRoot Q m i = orderedRoot H m i := by
    simp only [orderedRoot, hQRoots]
  rw [horderedTp, horderedQ] at hloi hhii
  simpa [H, m] using ⟨hloi, hhii⟩

end RealRooted
