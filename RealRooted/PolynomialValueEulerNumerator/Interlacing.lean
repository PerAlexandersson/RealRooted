module

import RealRooted.Transforms.BrandenE.Interlacing
public import RealRooted.Transforms.BrandenE.Basic
import RealRooted.Transforms.BrandenE.IntervalPreserver
public import RealRooted.PolynomialValueEulerNumerator
import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Algebra
public import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Basic
import RealRooted.Transforms.BrandenE.Inverse
import RealRooted.DerivativeRecurrence.RootWindow
import RealRooted.MaWang.Weak.Endpoint
import RealRooted.CommonInterleaver.RootDesc
import RealRooted.Mesh.FallingFactorial
public import RealRooted.FiniteFreeRootCount

/-!
# Euler numerators preserve rootwise order as interlacing

The canonical Euler numerator of `p` (`polynomialValueEulerNumerator`) is the Cayley transform of
Brändén's `brandenE p` (`polynomialValueEulerNumerator_eq_cayleyTransform_brandenE`), and the
Cayley transform preserves interlacing of polynomials with roots in `[-1, 0]`, including the
degree drop at roots `-1` (`strictInterl_cayleyTransform_of_roots_mem_Icc`).  Together with
Brändén's Theorem 4.6 (`brandenE_strictInterl_of_rootwiseLE`) this gives
`polynomialValueEulerNumerator_strictInterl_of_rootwiseLE`: monic polynomials of the same
positive degree with roots in `[-1, 0]` and coordinatewise ordered roots have interlacing Euler
numerators (P. Brändén, Trans. Amer. Math. Soc. 358 (2006), Theorem 4.6, in the numerator
normalization of F. Brenti).
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

private lemma coeff_brandenE_eq_factorial_mul_repr (p : ℝ[X]) (k : ℕ) :
    (brandenE p).coeff k =
      (k.factorial : ℝ) * (descPochhammerBasis ℝ).repr p k := by
  let T : ℝ[X] →ₗ[ℝ] ℝ :=
    (Polynomial.lcoeff ℝ k).comp
      (Polynomial.basisTransformₗ (orderedBellPolynomial (R := ℝ)))
  let S : ℝ[X] →ₗ[ℝ] ℝ :=
    (k.factorial : ℝ) • (descPochhammerBasis ℝ).coord k
  have hTS : T = S := by
    refine (descPochhammerBasis ℝ).ext fun i => ?_
    simp only [T, S, LinearMap.comp_apply, Polynomial.lcoeff_apply,
      Polynomial.basisTransformₗ_apply, LinearMap.smul_apply,
      smul_eq_mul, Module.Basis.coord_apply]
    rw [descPochhammerBasis_apply]
    change (brandenE (descPochhammer ℝ i)).coeff k =
      (k.factorial : ℝ) *
        (descPochhammerBasis ℝ).repr (descPochhammer ℝ i) k
    rw [brandenE_descPochhammer]
    conv_rhs =>
      rw [← descPochhammerBasis_apply i, Module.Basis.repr_self]
    by_cases hki : k = i
    · subst i
      simp
    · simp [hki]
  exact LinearMap.congr_fun hTS p

private lemma repr_iterate_forwardDifference (r : ℕ) :
    ∀ (p : ℝ[X]) (k : ℕ),
      (descPochhammerBasis ℝ).repr ((⇑forwardDifference)^[r] p) k =
        ((k + 1).ascFactorial r : ℝ) *
          (descPochhammerBasis ℝ).repr p (k + r) := by
  induction r with
  | zero => simp
  | succ r ih =>
      intro p k
      rw [Function.iterate_succ_apply', descPochhammerBasis_repr_forwardDifference,
        ih]
      have hfac :
          (k + 1) * (k + 2).ascFactorial r =
            (k + 1).ascFactorial (r + 1) := by
        rw [Nat.succ_ascFactorial, Nat.ascFactorial_succ]
      have hfacR :
          ((k + 1 : ℕ) : ℝ) * ((k + 2).ascFactorial r : ℕ) =
            ((k + 1).ascFactorial (r + 1) : ℕ) := by
        exact_mod_cast hfac
      push_cast at hfacR ⊢
      rw [← mul_assoc, hfacR]
      congr 2
      lia

private lemma eval_iterate_forwardDifference (r : ℕ) :
    ∀ (p : ℝ[X]) (x : ℝ),
      (((⇑forwardDifference)^[r] p).eval x) =
        ((fwdDiff (1 : ℝ))^[r] p.eval) x := by
  induction r with
  | zero => simp
  | succ r ih =>
      intro p x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        forwardDifference_apply]
      simp only [eval_sub, eval_comp, eval_add, eval_X, eval_C, fwdDiff]
      rw [ih, ih]

private lemma coeff_brandenE_eq_fwdDiff (p : ℝ[X]) (k : ℕ) :
    (brandenE p).coeff k =
      ((fwdDiff (1 : ℕ))^[k] (polynomialValueSeq p)) 0 := by
  rw [fwdDiff_iter_polynomialValueSeq]
  simp only [Nat.cast_zero]
  rw [← eval_iterate_forwardDifference]
  rw [← descPochhammerBasis_repr_zero,
    repr_iterate_forwardDifference]
  simp [coeff_brandenE_eq_factorial_mul_repr]

private lemma cayleyTransform_eq_finiteSum {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree ≤ n) :
    Polynomial.cayleyTransform n p =
      ∑ k ∈ Finset.range (n + 1),
        C (p.coeff k) * X ^ k * (1 - X) ^ (n - k) := by
  rw [Polynomial.cayleyTransform,
    Polynomial.homogenize_eq_sum_range_C_mul_X_pow hdeg]
  simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_C]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [MvPolynomial.eval₂_X, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [← Polynomial.C_eq_algebraMap]
  ring

/-- The canonical Euler numerator is the degree-capped Cayley transform of
Brändén's `E` transform.  Roots at `-1` are represented by the resulting
degree drop rather than by an additional factor. -/
theorem polynomialValueEulerNumerator_eq_cayleyTransform_brandenE (p : ℝ[X]) :
    polynomialValueEulerNumerator p =
      Polynomial.cayleyTransform p.natDegree (brandenE p) := by
  rw [polynomialValueEulerNumerator, finiteEulerNumerator,
    cayleyTransform_eq_finiteSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [coeff_brandenE_eq_fwdDiff]
  · exact Polynomial.basisTransform_natDegree_le_of_natDegree_le
      (fun n => (orderedBellPolynomial_natDegree (R := ℝ) n).le) p

private def cayleyRoot (r : ℝ) : ℝ := r / (1 + r)

private def cayleyRootList (rs : List ℝ) : List ℝ :=
  (rs.filter fun r => r ≠ -1).map cayleyRoot

private lemma cayleyRoot_mono {r s : ℝ} (hr : -1 < r) (hrs : r ≤ s) :
    cayleyRoot r ≤ cayleyRoot s := by
  have hs : -1 < s := hr.trans_le hrs
  rw [cayleyRoot, cayleyRoot, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private lemma listInterlaces_map_cayleyRoot :
    ∀ {ss rs : List ℝ}, ListInterlaces ss rs →
      (∀ x ∈ ss, -1 < x) → (∀ x ∈ rs, -1 < x) →
      ListInterlaces (ss.map cayleyRoot) (rs.map cayleyRoot)
  | [], [], _, _, _ => by simp [ListInterlaces]
  | [], [_], _, _, _ => by simp [ListInterlaces]
  | s :: ss, r₁ :: r₂ :: rs, h, hs, hr => by
      simp only [ListInterlaces] at h ⊢
      exact ⟨cayleyRoot_mono (hr r₁ (by simp)) h.1,
        cayleyRoot_mono (hs s (by simp)) h.2.1,
        listInterlaces_map_cayleyRoot h.2.2
          (fun x hx => hs x (by simp [hx]))
          (fun x hx => hr x (by simp [hx]))⟩
  | [], _ :: _ :: _, h, _, _ => by simp [ListInterlaces] at h
  | _ :: _, [], h, _, _ => by simp [ListInterlaces] at h
  | _ :: _, [_], h, _, _ => by simp [ListInterlaces] at h

private lemma listAlternates_map_cayleyRoot :
    ∀ {ss rs : List ℝ}, ListAlternates ss rs →
      (∀ x ∈ ss, -1 < x) → (∀ x ∈ rs, -1 < x) →
      ListAlternates (ss.map cayleyRoot) (rs.map cayleyRoot)
  | [], [], _, _, _ => by simp [ListAlternates]
  | s :: ss, r :: rs, h, hs, hr => by
      simp only [ListAlternates] at h ⊢
      exact ⟨cayleyRoot_mono (hs s (by simp)) h.1,
        listInterlaces_map_cayleyRoot h.2
          (fun x hx => hs x (by simp [hx]))
          (fun x hx => hr x (by simp [hx]))⟩
  | [], _ :: _, h, _, _ => by simp [ListAlternates] at h
  | _ :: _, [], h, _, _ => by simp [ListAlternates] at h

private lemma listAlternates_of_listInterlaces_cons :
    ∀ {ss rs : List ℝ} {r : ℝ},
      ListInterlaces ss (r :: rs) → ListAlternates ss rs
  | [], [], _, _ => by simp [ListAlternates]
  | s :: ss, r₂ :: rs, r, h => by
      simpa [ListInterlaces, ListAlternates] using h.2
  | [], _ :: _, _, h => by simp [ListInterlaces] at h
  | _ :: _, [], _, h => by simp [ListInterlaces] at h

private lemma all_ge_head_of_pairwise {r : ℝ} {rs : List ℝ}
    (h : (r :: rs).Pairwise (· ≤ ·)) :
    ∀ x ∈ r :: rs, r ≤ x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact le_rfl
  · exact (List.pairwise_cons.mp h).1 x hx

private lemma all_ge_right_head_of_listInterlaces :
    ∀ {ss rs : List ℝ} {r : ℝ}, ListInterlaces ss (r :: rs) →
      (∀ x ∈ ss, r ≤ x) ∧ (∀ x ∈ r :: rs, r ≤ x)
  | [], [], _, _ => by simp
  | s :: ss, r₂ :: rs, r, h => by
      have ht := all_ge_right_head_of_listInterlaces h.2.2
      constructor
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h.1
        · exact h.1.trans (h.2.1.trans (ht.1 x hx))
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact h.1.trans h.2.1
          · exact (h.1.trans h.2.1).trans (ht.2 x (by simp [hx]))
  | [], _ :: _, _, h => by simp [ListInterlaces] at h
  | _ :: _, [], _, h => by simp [ListInterlaces] at h

private lemma cayleyRootList_eq_map {rs : List ℝ}
    (h : ∀ r ∈ rs, -1 < r) :
    cayleyRootList rs = rs.map cayleyRoot := by
  unfold cayleyRootList
  congr 1
  apply List.filter_eq_self.mpr
  intro r hr
  simp only [decide_eq_true_eq]
  intro hre
  subst r
  linarith [h (-1) hr]

private lemma listAlternates_cayleyRootList_shape :
    ∀ {ss rs : List ℝ}, ss.Pairwise (· ≤ ·) → rs.Pairwise (· ≤ ·) →
      ss.length = rs.length → ListAlternates ss rs →
      (∀ x ∈ ss, -1 ≤ x) → (∀ x ∈ rs, -1 ≤ x) →
      ((cayleyRootList ss).length + 1 = (cayleyRootList rs).length ∧
          ListInterlaces (cayleyRootList ss) (cayleyRootList rs)) ∨
        ((cayleyRootList ss).length = (cayleyRootList rs).length ∧
          ListAlternates (cayleyRootList ss) (cayleyRootList rs))
  | [], [], _, _, _, _, _, _ => Or.inr ⟨rfl, by simp [cayleyRootList, ListAlternates]⟩
  | s :: ss, r :: rs, hss, hrs, hlen, halt, hsb, hrb => by
      have hsr : s ≤ r := halt.1
      by_cases hs : s = -1
      · subst s
        by_cases hr : r = -1
        · subst r
          have htail_alt := listAlternates_of_listInterlaces_cons halt.2
          have htail_len : ss.length = rs.length := Nat.succ.inj hlen
          have hrec := listAlternates_cayleyRootList_shape
            (List.pairwise_cons.mp hss).2 (List.pairwise_cons.mp hrs).2
            htail_len htail_alt
            (fun x hx => hsb x (by simp [hx]))
            (fun x hx => hrb x (by simp [hx]))
          simpa [cayleyRootList] using hrec
        · have hrgt : -1 < r := lt_of_le_of_ne (hrb r (by simp)) (Ne.symm hr)
          have hge := all_ge_right_head_of_listInterlaces halt.2
          have hs_gt : ∀ x ∈ ss, -1 < x := fun x hx => hrgt.trans_le (hge.1 x hx)
          have hr_gt : ∀ x ∈ r :: rs, -1 < x := fun x hx => hrgt.trans_le (hge.2 x hx)
          have hmap := listInterlaces_map_cayleyRoot halt.2 hs_gt hr_gt
          rw [show cayleyRootList (-1 :: ss) = cayleyRootList ss by
            simp [cayleyRootList]]
          rw [cayleyRootList_eq_map hs_gt, cayleyRootList_eq_map hr_gt]
          exact Or.inl ⟨by simpa using hlen, hmap⟩
      · have hsgt : -1 < s := lt_of_le_of_ne (hsb s (by simp)) (Ne.symm hs)
        have hs_gt : ∀ x ∈ s :: ss, -1 < x := fun x hx =>
          hsgt.trans_le (all_ge_head_of_pairwise hss x hx)
        have hr_gt : ∀ x ∈ r :: rs, -1 < x := fun x hx =>
          hsgt.trans_le (hsr.trans (all_ge_head_of_pairwise hrs x hx))
        have hmap := listAlternates_map_cayleyRoot halt hs_gt hr_gt
        rw [cayleyRootList_eq_map hs_gt, cayleyRootList_eq_map hr_gt]
        exact Or.inr ⟨by simpa using hlen, hmap⟩
  | [], _ :: _, _, _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _, _, _ => by simp at hlen

private def cayleyRootMultiset (rs : Multiset ℝ) : Multiset ℝ :=
  (rs.filter fun r => r ≠ -1).map cayleyRoot

private def cayleyRootFactor (r : ℝ) : ℝ[X] :=
  (1 + C r) * X - C r

private lemma cayleyRootFactor_data (r : ℝ) :
    cayleyRootFactor r ≠ 0 ∧ (cayleyRootFactor r).Splits ∧
      (cayleyRootFactor r).roots =
        if r = -1 then 0 else ({cayleyRoot r} : Multiset ℝ) := by
  by_cases hr : r = -1
  · subst r
    simp [cayleyRootFactor]
  · have hden : 1 + r ≠ 0 := by
      intro hzero
      apply hr
      linarith
    have heq : cayleyRootFactor r =
        C (1 + r) * (X - C (cayleyRoot r)) := by
      rw [cayleyRootFactor, cayleyRoot, mul_sub, ← C_mul]
      have hfrac : (1 + r) * (r / (1 + r)) = r := by
        field_simp
      rw [hfrac]
      simp only [map_add, map_one]
    rw [heq]
    refine ⟨mul_ne_zero (C_ne_zero.mpr hden) (X_sub_C_ne_zero _),
      (Polynomial.Splits.C (1 + r)).mul
        (Polynomial.Splits.of_natDegree_le_one (by compute_degree)), ?_⟩
    rw [roots_C_mul _ hden, roots_X_sub_C]
    simp [hr]

private lemma cayleyRootFactorProduct_data (rs : Multiset ℝ) :
      (rs.map cayleyRootFactor).prod ≠ 0 ∧
        (rs.map cayleyRootFactor).prod.Splits ∧
        (rs.map cayleyRootFactor).prod.roots = cayleyRootMultiset rs := by
  induction rs using Multiset.induction_on with
  | empty => simp [cayleyRootMultiset]
  | @cons r rs ih =>
      have hr := cayleyRootFactor_data r
      simp only [Multiset.map_cons, Multiset.prod_cons]
      refine ⟨mul_ne_zero hr.1 ih.1, hr.2.1.mul ih.2.1, ?_⟩
      rw [roots_mul (mul_ne_zero hr.1 ih.1), hr.2.2, ih.2.2]
      by_cases h : r = -1
      · simp [h, cayleyRootMultiset]
      · simp [h, cayleyRootMultiset]

private lemma cayleyTransform_data {p : ℝ[X]} {n : ℕ}
    (hp0 : p ≠ 0) (hp : p.Splits) (hdeg : p.natDegree = n) :
    Polynomial.cayleyTransform n p ≠ 0 ∧
      (Polynomial.cayleyTransform n p).Splits ∧
      (Polynomial.cayleyTransform n p).roots = cayleyRootMultiset p.roots := by
  rw [Polynomial.cayleyTransform_eq_rootFactorProduct hp hdeg]
  have hprod := cayleyRootFactorProduct_data p.roots
  change C p.leadingCoeff * (p.roots.map cayleyRootFactor).prod ≠ 0 ∧
    (C p.leadingCoeff * (p.roots.map cayleyRootFactor).prod).Splits ∧
    (C p.leadingCoeff * (p.roots.map cayleyRootFactor).prod).roots =
      cayleyRootMultiset p.roots
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  refine ⟨mul_ne_zero (by simp [hlc]) hprod.1,
    (Polynomial.Splits.C p.leadingCoeff).mul hprod.2.1, ?_⟩
  rw [roots_C_mul _ hlc, hprod.2.2]

private lemma coe_cayleyRootList (rs : List ℝ) :
    (↑(cayleyRootList rs) : Multiset ℝ) = cayleyRootMultiset (↑rs) := by
  simp [cayleyRootList, cayleyRootMultiset]

private lemma pairwise_map_cayleyRoot : ∀ {rs : List ℝ},
    rs.Pairwise (· ≤ ·) → (∀ r ∈ rs, -1 < r) →
    (rs.map cayleyRoot).Pairwise (· ≤ ·)
  | [], _, _ => by simp
  | r :: rs, hsorted, hbound => by
      rw [List.pairwise_cons] at hsorted
      simp only [List.map_cons, List.pairwise_cons]
      constructor
      · intro s hs
        rcases List.mem_map.mp hs with ⟨t, ht, rfl⟩
        exact cayleyRoot_mono (hbound r (by simp)) (hsorted.1 t ht)
      · exact pairwise_map_cayleyRoot hsorted.2
          (fun s hs => hbound s (by simp [hs]))

private lemma pairwise_cayleyRootList {rs : List ℝ}
    (hsorted : rs.Pairwise (· ≤ ·)) (hbound : ∀ r ∈ rs, -1 ≤ r) :
    (cayleyRootList rs).Pairwise (· ≤ ·) := by
  unfold cayleyRootList
  apply pairwise_map_cayleyRoot (hsorted.filter _)
  intro r hr
  have hrmem : r ∈ rs := List.mem_of_mem_filter hr
  have hrne : r ≠ -1 := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hr).2
  exact lt_of_le_of_ne (hbound r hrmem) (Ne.symm hrne)

/-- The degree-capped Cayley transform preserves oriented weak interlacing
for same-degree real-rooted pairs whose roots lie in `[-1, 0]`.  Factors at
`-1` disappear, and the list proof records the resulting degree drop. -/
theorem strictInterl_cayleyTransform_of_roots_mem_Icc
    {p q : ℝ[X]} {n : ℕ}
    (hpdeg : p.natDegree = n) (hqdeg : q.natDegree = n)
    (h : StrictInterl p q)
    (hp_roots : ∀ r ∈ p.roots, (-1 : ℝ) ≤ r ∧ r ≤ 0)
    (hq_roots : ∀ r ∈ q.roots, (-1 : ℝ) ≤ r ∧ r ≤ 0) :
    StrictInterl (Polynomial.cayleyTransform n p)
      (Polynomial.cayleyTransform n q) := by
  rcases h with ⟨hp_rr, hq_rr, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hss_len : ss.length = n := by
    rw [← Multiset.coe_card, hss_eq, Polynomial.splits_iff_card_roots.mp hp_rr.2, hpdeg]
  have hrs_len : rs.length = n := by
    rw [← Multiset.coe_card, hrs_eq, Polynomial.splits_iff_card_roots.mp hq_rr.2, hqdeg]
  have halt : ListAlternates ss rs := by
    rcases hshape with hdiff | hsame
    · lia
    · exact hsame.2
  have hss_box : ∀ r ∈ ss, (-1 : ℝ) ≤ r ∧ r ≤ 0 := by
    intro r hr
    exact hp_roots r (by simpa [hss_eq] using Multiset.mem_coe.mpr hr)
  have hrs_box : ∀ r ∈ rs, (-1 : ℝ) ≤ r ∧ r ≤ 0 := by
    intro r hr
    exact hq_roots r (by simpa [hrs_eq] using Multiset.mem_coe.mpr hr)
  have hp_cayley := cayleyTransform_data hp_rr.1 hp_rr.2 hpdeg
  have hq_cayley := cayleyTransform_data hq_rr.1 hq_rr.2 hqdeg
  refine ⟨⟨hp_cayley.1, hp_cayley.2.1⟩, ⟨hq_cayley.1, hq_cayley.2.1⟩,
    cayleyRootList ss, cayleyRootList rs,
    pairwise_cayleyRootList hss (fun r hr => (hss_box r hr).1),
    pairwise_cayleyRootList hrs (fun r hr => (hrs_box r hr).1), ?_, ?_, ?_⟩
  · rw [coe_cayleyRootList, hss_eq, hp_cayley.2.2]
  · rw [coe_cayleyRootList, hrs_eq, hq_cayley.2.2]
  · exact listAlternates_cayleyRootList_shape hss hrs
      (hss_len.trans hrs_len.symm) halt
      (fun r hr => (hss_box r hr).1) (fun r hr => (hrs_box r hr).1)

/-- A monic split interval-rooted input has its `E`-image rooted in the same
closed interval. -/
lemma brandenE_roots_mem_Icc_of_monic {p : ℝ[X]}
    (hp_monic : p.Monic) (hp_splits : p.Splits)
    (hp_roots : ∀ r ∈ p.roots, (-1 : ℝ) ≤ r ∧ r ≤ 0) :
    ∀ r ∈ (brandenE p).roots, (-1 : ℝ) ≤ r ∧ r ≤ 0 := by
  have hp_poly : rootPolynomial p.roots = p := by
    simpa [rootPolynomial] using
      (hp_splits.eq_prod_roots_of_monic hp_monic).symm
  have hlo := brandenE_rootPolynomial_roots_ge_neg_one p.roots hp_roots
  rw [hp_poly] at hlo
  have hpE0 : brandenE p ≠ 0 := by
    intro hzero
    apply hp_monic.ne_zero
    apply brandenE_injective (R := ℝ)
    simpa using hzero
  have hnonpos := brandenE_eq_zero_or_splits_and_roots_nonpos
    hp_splits hp_roots
  rcases hnonpos with hzero | hdata
  · exact (hpE0 hzero).elim
  · exact fun r hr => ⟨hlo r hr, hdata.2.2 r hr⟩

/-- Brändén's Theorem 4.6 in canonical Euler-numerator coordinates. -/
theorem polynomialValueEulerNumerator_strictInterl_of_rootwiseLE
    {f g : ℝ[X]} {n : ℕ}
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hf_degree : f.natDegree = n) (hg_degree : g.natDegree = n)
    (hn : n ≠ 0)
    (hf_roots : ∀ r ∈ f.roots, (-1 : ℝ) ≤ r ∧ r ≤ 0)
    (hg_roots : ∀ r ∈ g.roots, (-1 : ℝ) ≤ r ∧ r ≤ 0)
    (hfg : RootwiseLE f g) :
    StrictInterl (polynomialValueEulerNumerator f)
      (polynomialValueEulerNumerator g) := by
  have hE := brandenE_strictInterl_of_rootwiseLE
    hf_monic hg_monic hf_splits hg_splits hf_degree hg_degree hn
    hf_roots hg_roots hfg
  have hfE_roots := brandenE_roots_mem_Icc_of_monic
    hf_monic hf_splits hf_roots
  have hgE_roots := brandenE_roots_mem_Icc_of_monic
    hg_monic hg_splits hg_roots
  have hfE_degree : (brandenE f).natDegree = n := by
    have h := (brandenE_rootPolynomial_degree_pos f.roots).1
    rw [show rootPolynomial f.roots = f by
      simpa [rootPolynomial] using
        (hf_splits.eq_prod_roots_of_monic hf_monic).symm] at h
    rw [← hf_splits.natDegree_eq_card_roots, hf_degree] at h
    exact h
  have hgE_degree : (brandenE g).natDegree = n := by
    have h := (brandenE_rootPolynomial_degree_pos g.roots).1
    rw [show rootPolynomial g.roots = g by
      simpa [rootPolynomial] using
        (hg_splits.eq_prod_roots_of_monic hg_monic).symm] at h
    rw [← hg_splits.natDegree_eq_card_roots, hg_degree] at h
    exact h
  simpa only [polynomialValueEulerNumerator_eq_cayleyTransform_brandenE,
    hf_degree, hg_degree] using
    strictInterl_cayleyTransform_of_roots_mem_Icc
      hfE_degree hgE_degree hE hfE_roots hgE_roots

/-- Multiplying a nonzero source polynomial by a scalar multiplies its
canonical Euler numerator by the same scalar. -/
theorem polynomialValueEulerNumerator_C_mul {a : ℝ} (ha : a ≠ 0) (p : ℝ[X]) :
    polynomialValueEulerNumerator (C a * p) =
      C a * polynomialValueEulerNumerator p := by
  rw [polynomialValueEulerNumerator_eq_cayleyTransform_brandenE,
    Polynomial.natDegree_C_mul ha, brandenE_C_mul,
    Polynomial.cayleyTransform_C_mul,
    ← polynomialValueEulerNumerator_eq_cayleyTransform_brandenE]

end RealRooted
