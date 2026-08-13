import RealRooted.FiniteFreeMultiplicative
import RealRooted.LiuOppositeSigns.JensenRootCount
import RealRooted.OperatorPreservesInterlacing

/-!
# Root-count contraction for finite free multiplication

This file proves the finite root-replacement argument behind one-sided
root-count contraction.  The operator layer first orients Schur--Szegő
composition with a reflected PF factor.  The combinatorial layer then raises
finitely many roots and compares the resulting ordered root lists.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Fixed-right-factor Schur--Szegő composition as a real linear map. -/
def schurSzegoRightLinearMap (d : ℕ) (p : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := fun q ↦ schurSzegoComp d q p
  map_add' f g := schurSzegoComp_add_left d f g p
  map_smul' c f := by
    simp only [smul_eq_C_mul]
    exact schurSzegoComp_C_mul_left d c f p

@[simp] theorem schurSzegoRightLinearMap_apply (d : ℕ) (p f : ℝ[X]) :
    schurSzegoRightLinearMap d p f = schurSzegoComp d f p :=
  rfl

/-- A fixed PF right factor preserves real-rootedness up to a zero output. -/
theorem schurSzegoRightLinearMap_preservesRealRootedOrZeroUpTo
    {d : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p) (hpdeg : p.natDegree ≤ d) :
    ∀ q : ℝ[X], q.natDegree ≤ d →
      (q ≠ 0 ∧ q.Splits) →
      schurSzegoRightLinearMap d p q = 0 ∨
        (schurSzegoRightLinearMap d p q).Splits := by
  intro q hqdeg hq
  rw [schurSzegoRightLinearMap_apply, schurSzegoComp_comm]
  exact schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial
    hp hpdeg hqdeg hq.2

/-- Fixed Schur--Szegő composition preserves a proper-position pair, up to
the orientation ambiguity in the generic operator theorem. -/
theorem schurSzegoComp_prec0_or_revPrec0
    {d : ℕ} {f g p : ℝ[X]}
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree ≤ d)
    (hfdeg : f.natDegree ≤ d) (hgdeg : g.natDegree ≤ d)
    (hfg : Prec f g) :
    Prec0 (schurSzegoComp d f p) (schurSzegoComp d g p) ∨
      Prec0 (schurSzegoComp d g p) (schurSzegoComp d f p) := by
  apply prec0_or_revPrec0_map_of_pencil (T := schurSzegoRightLinearMap d p)
    (allComboRealRooted_of_prec hfg)
  intro a b hab
  apply schurSzegoRightLinearMap_preservesRealRootedOrZeroUpTo hp hpdeg
  · exact (Polynomial.natDegree_add_le _ _).trans <|
      max_le
        ((Polynomial.natDegree_C_mul_le a f).trans hfdeg)
        ((Polynomial.natDegree_C_mul_le b g).trans hgdeg)
  · exact hab

@[simp] theorem coeff_schurSzegoComp_top (d : ℕ) (f p : ℝ[X]) :
    (schurSzegoComp d f p).coeff d = f.coeff d * p.coeff d := by
  simp [coeff_schurSzegoComp_of_le]

theorem coeff_schurSzegoComp_pred {d : ℕ} (hd : d ≠ 0) (f p : ℝ[X]) :
    (schurSzegoComp d f p).coeff (d - 1) =
      f.coeff (d - 1) * p.coeff (d - 1) / (d : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  simp [coeff_schurSzegoComp_of_le]

theorem natDegree_schurSzegoComp_eq_of_coeff_top_ne
    {d : ℕ} {f p : ℝ[X]} (hf : f.coeff d ≠ 0) (hp : p.coeff d ≠ 0) :
    (schurSzegoComp d f p).natDegree = d := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_schurSzegoComp_le d f p)
  simp [hf, hp]

/-- Vieta turns the next-to-leading coefficient formula into the exact
root-sum scaling needed to resolve the operator orientation. -/
theorem roots_sum_schurSzegoComp_scaled
    {d : ℕ} {f p : ℝ[X]} (hd : d ≠ 0)
    (hfdeg : f.natDegree = d) (hpdeg : p.natDegree = d)
    (hfs : f.Splits) (houts : (schurSzegoComp d f p).Splits) :
    (d : ℝ) * p.coeff d * (schurSzegoComp d f p).roots.sum =
      p.coeff (d - 1) * f.roots.sum := by
  have hf_top : f.coeff d ≠ 0 := by
    rw [← hfdeg, ← Polynomial.leadingCoeff]
    apply Polynomial.leadingCoeff_ne_zero.mpr
    intro hf0
    subst f
    simp at hfdeg
    exact hd hfdeg.symm
  have hp_top : p.coeff d ≠ 0 := by
    rw [← hpdeg, ← Polynomial.leadingCoeff]
    apply Polynomial.leadingCoeff_ne_zero.mpr
    intro hp0
    subst p
    simp at hpdeg
    exact hd hpdeg.symm
  have houtdeg : (schurSzegoComp d f p).natDegree = d :=
    natDegree_schurSzegoComp_eq_of_coeff_top_ne hf_top hp_top
  have hf_vieta := hfs.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hout_vieta := houts.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [Polynomial.nextCoeff, hfdeg, Polynomial.leadingCoeff, hfdeg] at hf_vieta
  rw [Polynomial.nextCoeff, houtdeg, Polynomial.leadingCoeff, houtdeg,
    coeff_schurSzegoComp_pred hd, coeff_schurSzegoComp_top] at hout_vieta
  simp [hd] at hf_vieta hout_vieta
  have hd_real : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  field_simp [hd_real] at hout_vieta
  apply mul_left_cancel₀ hf_top
  calc
    f.coeff d * ((d : ℝ) * p.coeff d * (schurSzegoComp d f p).roots.sum) =
        -((d : ℝ) *
          (-(schurSzegoComp d f p).roots.sum *
            (f.coeff d * p.coeff d))) := by ring
    _ = -(f.coeff (d - 1) * p.coeff (d - 1)) := by
      nlinarith [hout_vieta]
    _ = f.coeff d * (p.coeff (d - 1) * f.roots.sum) := by
      rw [hf_vieta]
      ring

/-- A positive next-to-leading coefficient fixes the orientation left
ambiguous by the generic operator theorem. -/
theorem schurSzegoComp_prec_of_pred_coeff_pos
    {d : ℕ} {f g p : ℝ[X]} (hd : d ≠ 0)
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree = d)
    (hp_pred : 0 < p.coeff (d - 1))
    (hfdeg : f.natDegree = d) (hgdeg : g.natDegree = d)
    (hfg : Prec f g) :
    Prec (schurSzegoComp d f p) (schurSzegoComp d g p) := by
  have hp0 : p ≠ 0 := by
    intro hp_zero
    subst p
    simp at hpdeg
    exact hd hpdeg.symm
  have hp_top_pos : 0 < p.coeff d := by
    rw [← hpdeg, ← Polynomial.leadingCoeff]
    exact hp.hasNonnegCoeffs.pos_leadingCoeff hp0
  have hf_top : f.coeff d ≠ 0 := by
    rw [← hfdeg, ← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hfg.1.1
  have hg_top : g.coeff d ≠ 0 := by
    rw [← hgdeg, ← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hfg.2.1.1
  have hTfdeg : (schurSzegoComp d f p).natDegree = d :=
    natDegree_schurSzegoComp_eq_of_coeff_top_ne hf_top hp_top_pos.ne'
  have hTgdeg : (schurSzegoComp d g p).natDegree = d :=
    natDegree_schurSzegoComp_eq_of_coeff_top_ne hg_top hp_top_pos.ne'
  have hTf0 : schurSzegoComp d f p ≠ 0 := by
    intro hzero
    rw [hzero] at hTfdeg
    simp at hTfdeg
    exact hd hTfdeg.symm
  have hTg0 : schurSzegoComp d g p ≠ 0 := by
    intro hzero
    rw [hzero] at hTgdeg
    simp at hTgdeg
    exact hd hTgdeg.symm
  have hor := schurSzegoComp_prec0_or_revPrec0
    hp hpdeg.le hfdeg.le hgdeg.le hfg
  rcases hor with hforward | hreverse
  · rcases hforward with hzero | hzero | hprec
    · exact (hTf0 hzero).elim
    · exact (hTg0 hzero).elim
    · exact hprec
  · rcases hreverse with hzero | hzero | hprec
    · exact (hTg0 hzero).elim
    · exact (hTf0 hzero).elim
    · apply prec_of_reverse_prec_of_roots_sum_le hprec
        (hTfdeg.trans hTgdeg.symm)
      have hinput_sum : f.roots.sum ≤ g.roots.sum :=
        roots_sum_le_of_prec_sameDegree hfg (hfdeg.trans hgdeg.symm)
      have hscaled_input :=
        mul_le_mul_of_nonneg_left hinput_sum hp_pred.le
      have hscale_f := roots_sum_schurSzegoComp_scaled
        hd hfdeg hpdeg hfg.1.2 hprec.2.1.2
      have hscale_g := roots_sum_schurSzegoComp_scaled
        hd hgdeg hpdeg hfg.2.1.2 hprec.1.2
      have hscale_pos : 0 < (d : ℝ) * p.coeff d := by
        exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hd) hp_top_pos
      apply (mul_le_mul_iff_left₀ hscale_pos).mp
      calc
        (schurSzegoComp d f p).roots.sum * ((d : ℝ) * p.coeff d) =
            (d : ℝ) * p.coeff d *
              (schurSzegoComp d f p).roots.sum := by ring
        _ = p.coeff (d - 1) * f.roots.sum := hscale_f
        _ ≤ p.coeff (d - 1) * g.roots.sum := hscaled_input
        _ = (d : ℝ) * p.coeff d *
              (schurSzegoComp d g p).roots.sum := hscale_g.symm
        _ = (schurSzegoComp d g p).roots.sum *
              ((d : ℝ) * p.coeff d) := by ring

/-- Positive constant and linear coefficients of the original PF factor
orient Schur--Szegő composition with its ordinary reflection. -/
theorem schurSzegoComp_prec_of_reflect_pf_factor
    {d : ℕ} {f g p : ℝ[X]} (hd : d ≠ 0)
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree ≤ d)
    (hp0 : p.coeff 0 ≠ 0) (hp1 : 0 < p.coeff 1)
    (hfdeg : f.natDegree = d) (hgdeg : g.natDegree = d)
    (hfg : Prec f g) :
    Prec (schurSzegoComp d f (reflect d p))
      (schurSzegoComp d g (reflect d p)) := by
  have hrefdeg : (reflect d p).natDegree = d :=
    DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne hpdeg hp0
  have hrefpred : 0 < (reflect d p).coeff (d - 1) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
    simpa using hp1
  exact schurSzegoComp_prec_of_pred_coeff_pos hd
    (isPFPolynomial_reflect hp hpdeg) hrefdeg hrefpred hfdeg hgdeg hfg

/-- The monic polynomial with root multiset `s`. -/
def rootPolynomial (s : Multiset ℝ) : ℝ[X] :=
  (s.map fun r => X - C r).prod

@[simp] theorem roots_rootPolynomial (s : Multiset ℝ) :
    (rootPolynomial s).roots = s :=
  Polynomial.roots_multiset_prod_X_sub_C s

theorem rootPolynomial_monic (s : Multiset ℝ) : (rootPolynomial s).Monic :=
  Polynomial.monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r

theorem rootPolynomial_splits (s : Multiset ℝ) : (rootPolynomial s).Splits := by
  apply splits_of_card_roots
  simp [rootPolynomial, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]

@[simp] theorem natDegree_rootPolynomial (s : Multiset ℝ) :
    (rootPolynomial s).natDegree = s.card := by
  rw [rootPolynomial, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]

theorem prec_linear_root_move {u v : ℝ} (huv : u ≤ v) :
    Prec (X - C u) (X - C v) := by
  simpa [sub_eq_add_neg] using
    (prec_X_add_C_iff (a := -v) (b := -u)).mpr (by linarith)

theorem prec_rootPolynomial_cons_move (s : Multiset ℝ) {u v : ℝ}
    (huv : u ≤ v) :
    Prec (rootPolynomial (u ::ₘ s)) (rootPolynomial (v ::ₘ s)) := by
  have h := prec_mul_common_factor (rootPolynomial_monic s).ne_zero
    (rootPolynomial_splits s) (prec_linear_root_move huv)
  simpa [rootPolynomial, mul_comm] using h

/-- The operator property needed by the finite root-replacement proof. -/
def PreservesFullDegreeRootMoves (d : ℕ) (T : ℝ[X] → ℝ[X]) : Prop :=
  (∀ {f : ℝ[X]}, f.natDegree = d → (T f).natDegree = d) ∧
    ∀ {f g : ℝ[X]}, f.natDegree = d → g.natDegree = d →
      Prec f g → Prec (T f) (T g)

/-- Coordinatewise order on increasingly sorted root lists. -/
def RootwiseLE (p q : ℝ[X]) : Prop :=
  List.Forall₂ (· ≤ ·) (p.roots.sort (· ≤ ·)) (q.roots.sort (· ≤ ·))

private theorem forall₂_le_trans :
    ∀ {a b c : List ℝ}, List.Forall₂ (· ≤ ·) a b →
      List.Forall₂ (· ≤ ·) b c → List.Forall₂ (· ≤ ·) a c
  | [], [], [], List.Forall₂.nil, List.Forall₂.nil => List.Forall₂.nil
  | _ :: _, _ :: _, _ :: _, List.Forall₂.cons hab htail,
      List.Forall₂.cons hbc htail₂ =>
    List.Forall₂.cons (hab.trans hbc) (forall₂_le_trans htail htail₂)

theorem RootwiseLE.refl (p : ℝ[X]) : RootwiseLE p p :=
  List.forall₂_refl _

theorem RootwiseLE.trans {p q r : ℝ[X]}
    (hpq : RootwiseLE p q) (hqr : RootwiseLE q r) : RootwiseLE p r :=
  forall₂_le_trans hpq hqr

theorem RootwiseLE.of_prec_sameDegree {p q : ℝ[X]} (hpq : Prec p q)
    (hdeg : p.natDegree = q.natDegree) : RootwiseLE p q := by
  rcases hpq with ⟨hp, hq, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hlen : ss.length = rs.length := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hp.2,
      ← Multiset.coe_card, hrs_eq, card_roots_of_splits hq.2, hdeg]
  have halt : ListAlternates ss rs := by
    rcases hshape with hbad | halt
    · exfalso
      lia
    · exact halt.2
  have hsort_ss : p.roots.sort (· ≤ ·) = ss := by
    apply List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) hss
    exact Multiset.coe_eq_coe.mp
      ((Multiset.sort_eq p.roots (· ≤ ·)).trans hss_eq.symm)
  have hsort_rs : q.roots.sort (· ≤ ·) = rs := by
    apply List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) hrs
    exact Multiset.coe_eq_coe.mp
      ((Multiset.sort_eq q.roots (· ≤ ·)).trans hrs_eq.symm)
  unfold RootwiseLE
  rw [hsort_ss, hsort_rs]
  exact listAlternates_forall₂_le halt

private theorem forall₂_filter_gt_length_le (t : ℝ) :
    ∀ {xs ys : List ℝ}, List.Forall₂ (· ≤ ·) xs ys →
      (xs.filter (t < ·)).length ≤ (ys.filter (t < ·)).length
  | [], [], List.Forall₂.nil => by simp
  | x :: xs, y :: ys, List.Forall₂.cons hxy htail => by
      have ih := forall₂_filter_gt_length_le t htail
      by_cases htx : t < x
      · have hty : t < y := htx.trans_le hxy
        simp [htx, hty, ih]
      · by_cases hty : t < y
        · simp [htx, hty]
          lia
        · simp [htx, hty, ih]

private theorem sorted_card_filter_ge_at_index
    {l : List ℝ} (hl : l.Pairwise (· ≤ ·)) {i : ℕ} (hi : i < l.length) :
    l.length - i ≤ (l.filter (l[i] ≤ ·)).length := by
  have hsuffix : ∀ y ∈ l.drop i, l[i] ≤ y := by
    intro y hy
    obtain ⟨j, rfl⟩ := List.get_of_mem hy
    have hjlt : i + j < l.length := by
      have hj : j < l.length - i := by simpa using j.isLt
      have hadd := Nat.lt_sub_iff_add_lt.mp hj
      simpa [Nat.add_comm] using hadd
    have hle := hl.rel_get_of_le (a := ⟨i, hi⟩)
      (b := ⟨i + j, hjlt⟩) (by simp)
    have heq : (l.drop i).get j = l.get ⟨i + j, hjlt⟩ :=
      List.getElem_drop
    rw [heq]
    exact hle
  have hfilter : (l.drop i).filter (l[i] ≤ ·) = l.drop i := by
    apply List.filter_eq_self.mpr
    intro y hy
    exact decide_eq_true (hsuffix y hy)
  have hsub := List.drop_sublist i l
  have hfsub := hsub.filter (l[i] ≤ ·)
  have hlen := hfsub.length_le
  simpa [hfilter] using hlen

private theorem sorted_card_filter_ge_le_of_index_lt
    {l : List ℝ} (hl : l.Pairwise (· ≤ ·)) {j : ℕ} (hj : j < l.length)
    {x : ℝ} (h : l[j] < x) :
    (l.filter (x ≤ ·)).length ≤ l.length - (j + 1) := by
  have hprefix : ∀ y ∈ l.take (j + 1), ¬x ≤ y := by
    intro y hy hxy
    obtain ⟨i, rfl⟩ := List.get_of_mem hy
    have hi_j : i < j + 1 := by
      simpa [List.length_take, Nat.min_eq_left (by lia : j + 1 ≤ l.length)]
        using i.isLt
    have hi : i < l.length := by lia
    have hle : l[i] ≤ l[j] := hl.rel_get_of_le
      (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (by simpa using Nat.le_of_lt_succ hi_j)
    have hxy' : x ≤ l[i] := by simpa using hxy
    linarith
  have hfilter_prefix : (l.take (j + 1)).filter (x ≤ ·) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro y hy hdec
    exact hprefix y hy (of_decide_eq_true hdec)
  have hsplit := List.take_append_drop (j + 1) l
  rw [← hsplit, List.filter_append, hfilter_prefix, List.nil_append]
  have hlen := List.length_filter_le (x ≤ ·) (l.drop (j + 1))
  simpa using hlen

/-- An upper-count offset gives coordinatewise order after raising the
smallest roots on the comparison side. -/
theorem forall₂_drop_append_replicate_of_upper_count_offset
    {ps qs : List ℝ} {ell : ℕ} {M : ℝ}
    (hps : ps.Pairwise (· ≤ ·)) (hqs : qs.Pairwise (· ≤ ·))
    (hlen : ps.length = qs.length) (hell : ell ≤ ps.length)
    (hM : ∀ q ∈ qs, q ≤ M)
    (hcount : ∀ x : ℝ,
      (qs.filter (x ≤ ·)).length ≤ (ps.filter (x ≤ ·)).length + ell) :
    List.Forall₂ (· ≤ ·) qs
      (ps.drop ell ++ List.replicate ell M) := by
  apply List.forall₂_of_length_eq_of_get
  · rw [List.length_append, List.length_drop, List.length_replicate,
      Nat.sub_add_cancel hell, hlen]
  intro i hiq hit
  by_cases hi : i < (ps.drop ell).length
  · have hi_shift : i + ell < ps.length := by
      rw [List.length_drop] at hi
      exact Nat.lt_sub_iff_add_lt.mp hi
    have hcoord : qs[i] ≤ ps[i + ell] := by
      by_contra hnot
      have hlt : ps[i + ell] < qs[i] := lt_of_not_ge hnot
      have hq_lower := sorted_card_filter_ge_at_index hqs hiq
      have hp_upper := sorted_card_filter_ge_le_of_index_lt hps hi_shift hlt
      have hcnt := hcount qs[i]
      rw [← hlen] at hq_lower
      lia
    have htarget :
        (ps.drop ell ++ List.replicate ell M).get ⟨i, hit⟩ =
          ps[i + ell] := by
      change (ps.drop ell ++ List.replicate ell M)[i] = ps[i + ell]
      rw [List.getElem_append_left hi]
      simp [Nat.add_comm]
    rw [htarget]
    exact hcoord
  · have hqmem : qs.get ⟨i, hiq⟩ ∈ qs := List.get_mem _ _
    have hqiM := hM _ hqmem
    have htarget :
        (ps.drop ell ++ List.replicate ell M).get ⟨i, hit⟩ = M := by
      change (ps.drop ell ++ List.replicate ell M)[i] = M
      rw [List.getElem_append_right (Nat.le_of_not_gt hi)]
      simp
    rw [htarget]
    exact hqiM

theorem RootwiseLE.rootCountAbove_le {p q : ℝ[X]} (hpq : RootwiseLE p q)
    (t : ℝ) :
    (p.roots.filter (t < ·)).card ≤ (q.roots.filter (t < ·)).card := by
  have hlen := forall₂_filter_gt_length_le t hpq
  have hp_sort : (↑(p.roots.sort (· ≤ ·)) : Multiset ℝ) = p.roots :=
    Multiset.sort_eq p.roots (· ≤ ·)
  have hq_sort : (↑(q.roots.sort (· ≤ ·)) : Multiset ℝ) = q.roots :=
    Multiset.sort_eq q.roots (· ≤ ·)
  rw [← hp_sort, ← hq_sort, Multiset.filter_coe, Multiset.filter_coe]
  exact hlen

/-- Coordinatewise root order is preserved by an operator satisfying the
full-degree one-root-move hypothesis. -/
theorem rootwiseLE_map_rootPolynomial_of_forall₂
    {d : ℕ} {T : ℝ[X] → ℝ[X]} (hT : PreservesFullDegreeRootMoves d T)
    {xs ys : List ℝ} (hxy : List.Forall₂ (· ≤ ·) xs ys)
    (fixed : Multiset ℝ) (htotal : xs.length + fixed.card = d) :
    RootwiseLE
      (T (rootPolynomial ((xs : Multiset ℝ) + fixed)))
      (T (rootPolynomial ((ys : Multiset ℝ) + fixed))) := by
  induction hxy generalizing fixed with
  | nil => exact RootwiseLE.refl _
  | cons hxy htail ih =>
      rename_i x y xs ys
      let s : Multiset ℝ := (xs : Multiset ℝ) + fixed
      have hdegx : (rootPolynomial (x ::ₘ s)).natDegree = d := by
        rw [natDegree_rootPolynomial]
        simpa [s, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal
      have hdegy : (rootPolynomial (y ::ₘ s)).natDegree = d := by
        rw [natDegree_rootPolynomial]
        simpa [s, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal
      have hprec :
          Prec (rootPolynomial (x ::ₘ s)) (rootPolynomial (y ::ₘ s)) :=
        prec_rootPolynomial_cons_move s hxy
      have hTprec := hT.2 hdegx hdegy hprec
      have hstep :
          RootwiseLE (T (rootPolynomial (x ::ₘ s)))
            (T (rootPolynomial (y ::ₘ s))) :=
        RootwiseLE.of_prec_sameDegree hTprec
          ((hT.1 hdegx).trans (hT.1 hdegy).symm)
      have htotal' : xs.length + (y ::ₘ fixed).card = d := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal
      have hrec := ih (fixed := y ::ₘ fixed) htotal'
      have hx : (↑(x :: xs) : Multiset ℝ) + fixed = x ::ₘ s := by
        change (x ::ₘ (↑xs : Multiset ℝ)) + fixed =
          x ::ₘ ((↑xs : Multiset ℝ) + fixed)
        exact Multiset.cons_add x (↑xs : Multiset ℝ) fixed
      have hy : (↑(y :: ys) : Multiset ℝ) + fixed =
          (↑ys : Multiset ℝ) + (y ::ₘ fixed) := by
        change (y ::ₘ (↑ys : Multiset ℝ)) + fixed =
          (↑ys : Multiset ℝ) + (y ::ₘ fixed)
        ext z
        by_cases hzy : z = y
        · simp [Multiset.count_add, hzy, add_comm, add_left_comm, add_assoc]
        · simp [Multiset.count_add, hzy, Ne.symm hzy, add_comm]
      rw [hx, hy]
      apply hstep.trans
      simpa [s, add_comm, add_left_comm, add_assoc] using hrec

/-- Replace the first `ell` roots by a common upper guard. -/
def raiseSmallest : List ℝ → ℕ → ℝ → Multiset ℝ
  | xs, 0, _ => xs
  | [], _ + 1, _ => 0
  | _ :: xs, n + 1, M => M ::ₘ raiseSmallest xs n M

theorem raiseSmallest_eq {xs : List ℝ} {ell : ℕ}
    (hell : ell ≤ xs.length) (M : ℝ) :
    raiseSmallest xs ell M =
      (↑(xs.drop ell ++ List.replicate ell M) : Multiset ℝ) := by
  induction ell generalizing xs with
  | zero => simp [raiseSmallest]
  | succ ell ih =>
      cases xs with
      | nil => simp at hell
      | cons a xs =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at hell
          rw [show raiseSmallest (a :: xs) (ell + 1) M =
            M ::ₘ raiseSmallest xs ell M from rfl, ih hell]
          rw [List.replicate_succ]
          simp only [List.drop_succ_cons]
          apply Multiset.coe_eq_coe.mpr
          exact List.perm_cons_append_cons M (List.Perm.refl _)

/-- Raising `ell` roots produces at most `ell` extra output roots above any
threshold. -/
theorem rootCountAbove_map_raiseSmallest_le
    {d ell : ℕ} {T : ℝ[X] → ℝ[X]} (hT : PreservesFullDegreeRootMoves d T)
    {xs : List ℝ} {fixed : Multiset ℝ} {M : ℝ}
    (hell : ell ≤ xs.length) (hM : ∀ x ∈ xs, x ≤ M)
    (htotal : xs.length + fixed.card = d) :
    ∀ t : ℝ,
      ((T (rootPolynomial (raiseSmallest xs ell M + fixed))).roots.filter
          (t < ·)).card ≤
        ((T (rootPolynomial ((xs : Multiset ℝ) + fixed))).roots.filter
          (t < ·)).card + ell := by
  induction ell generalizing xs fixed with
  | zero => simp [raiseSmallest]
  | succ ell ih =>
      cases xs with
      | nil => simp at hell
      | cons a xs =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at hell
          have haM : a ≤ M := hM a (by simp)
          have htailM : ∀ x ∈ xs, x ≤ M :=
            fun x hx => hM x (by simp [hx])
          let s : Multiset ℝ := (xs : Multiset ℝ) + fixed
          have hdeg0 : (rootPolynomial (a ::ₘ s)).natDegree = d := by
            rw [natDegree_rootPolynomial]
            simpa [s, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal
          have hdeg1 : (rootPolynomial (M ::ₘ s)).natDegree = d := by
            rw [natDegree_rootPolynomial]
            simpa [s, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal
          have hprec := hT.2 hdeg0 hdeg1
            (prec_rootPolynomial_cons_move s haM)
          have hcoe : (↑(a :: xs) : Multiset ℝ) + fixed = a ::ₘ s := by
            change (a ::ₘ (↑xs : Multiset ℝ)) + fixed =
              a ::ₘ ((↑xs : Multiset ℝ) + fixed)
            exact Multiset.cons_add a (↑xs : Multiset ℝ) fixed
          intro t
          have hstep := (rootCountAboveOriented_of_prec hprec t).2
          have htotal' : xs.length + (M ::ₘ fixed).card = d := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal
          have hrec := ih hell htailM htotal' t
          simp only [raiseSmallest, Multiset.cons_add]
          change
            ((T (rootPolynomial
              (M ::ₘ (raiseSmallest xs ell M + fixed)))).roots.filter
                (t < ·)).card ≤
              ((T (rootPolynomial
                ((↑(a :: xs) : Multiset ℝ) + fixed))).roots.filter
                  (t < ·)).card + (ell + 1)
          have hrec' :
              ((T (rootPolynomial
                (M ::ₘ (raiseSmallest xs ell M + fixed)))).roots.filter
                  (t < ·)).card ≤
                ((T (rootPolynomial (M ::ₘ s))).roots.filter
                  (t < ·)).card + ell := by
            simpa [s, add_comm, add_left_comm, add_assoc] using hrec
          have hstep' :
              ((T (rootPolynomial (M ::ₘ s))).roots.filter (t < ·)).card ≤
                ((T (rootPolynomial
                  ((↑(a :: xs) : Multiset ℝ) + fixed))).roots.filter
                    (t < ·)).card + 1 := by
            rw [hcoe]
            exact (show
              ((T (rootPolynomial (M ::ₘ s))).roots.filter (t < ·)).card ≤
                ((T (rootPolynomial (a ::ₘ s))).roots.filter
                  (t < ·)).card + 1 by
                    exact_mod_cast hstep)
          lia

/-- Finite root-replacement contraction: an input upper-count offset survives
every operator preserving oriented full-degree root moves. -/
theorem rootCountAbove_map_le_add_of_input_offset
    {d ell : ℕ} {T : ℝ[X] → ℝ[X]} (hT : PreservesFullDegreeRootMoves d T)
    {ps qs : List ℝ} {M : ℝ}
    (hps : ps.Pairwise (· ≤ ·)) (hqs : qs.Pairwise (· ≤ ·))
    (hlen : ps.length = qs.length) (hd : ps.length = d)
    (hell : ell ≤ ps.length)
    (hMps : ∀ p ∈ ps, p ≤ M) (hMqs : ∀ q ∈ qs, q ≤ M)
    (hcount : ∀ x : ℝ,
      (qs.filter (x ≤ ·)).length ≤ (ps.filter (x ≤ ·)).length + ell) :
    ∀ t : ℝ,
      ((T (rootPolynomial (qs : Multiset ℝ))).roots.filter (t < ·)).card ≤
        ((T (rootPolynomial (ps : Multiset ℝ))).roots.filter
          (t < ·)).card + ell := by
  let raised := ps.drop ell ++ List.replicate ell M
  have hcoord : List.Forall₂ (· ≤ ·) qs raised :=
    forall₂_drop_append_replicate_of_upper_count_offset
      hps hqs hlen hell hMqs hcount
  have hqraised :
      RootwiseLE (T (rootPolynomial (qs : Multiset ℝ)))
        (T (rootPolynomial (raised : Multiset ℝ))) := by
    have hraw := rootwiseLE_map_rootPolynomial_of_forall₂ hT hcoord 0
      (by simpa [raised, hd] using hlen.symm)
    simpa using hraw
  have hraise := rootCountAbove_map_raiseSmallest_le
    (T := T) hT hell hMps (fixed := 0) (by simpa using hd)
  intro t
  have hqr := hqraised.rootCountAbove_le t
  have hrp := hraise t
  rw [raiseSmallest_eq hell] at hrp
  have hrp' :
      ((T (rootPolynomial (raised : Multiset ℝ))).roots.filter
          (t < ·)).card ≤
        ((T (rootPolynomial (ps : Multiset ℝ))).roots.filter
          (t < ·)).card + ell := by
    simpa [raised] using hrp
  exact hqr.trans hrp'

/-- The reflected-PF Schur operator satisfies the root-move hypotheses used by
the abstract contraction theorem. -/
theorem schurSzegoComp_reflect_preservesFullDegreeRootMoves
    {d : ℕ} {p : ℝ[X]} (hd : d ≠ 0)
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree ≤ d)
    (hp0 : p.coeff 0 ≠ 0) (hp1 : 0 < p.coeff 1) :
    PreservesFullDegreeRootMoves d
      (fun f => schurSzegoComp d f (reflect d p)) := by
  constructor
  · intro f hfdeg
    have hf_top : f.coeff d ≠ 0 := by
      rw [← hfdeg, ← Polynomial.leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr (by
        intro hfzero
        subst f
        simp at hfdeg
        exact hd hfdeg.symm)
    have href_top : (reflect d p).coeff d ≠ 0 := by
      simpa [coeff_reflect] using hp0
    exact natDegree_schurSzegoComp_eq_of_coeff_top_ne hf_top href_top
  · intro f g hfdeg hgdeg hfg
    exact schurSzegoComp_prec_of_reflect_pf_factor
      hd hp hpdeg hp0 hp1 hfdeg hgdeg hfg

private def listUpperBound : List ℝ → ℝ
  | [] => 0
  | x :: xs => max x (listUpperBound xs)

private theorem le_listUpperBound {x : ℝ} :
    ∀ {xs : List ℝ}, x ∈ xs → x ≤ listUpperBound xs
  | [], hx => by simp at hx
  | y :: ys, hx => by
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_max_left _ _
      · exact (le_listUpperBound hx).trans (le_max_right _ _)

/-- Strict-upper root-count contraction for Schur--Szegő composition with a
reflected PF factor.  The hypothesis uses closed upper counts so repeated roots
at the threshold are handled without a genericity assumption. -/
theorem rootCountAbove_schurSzegoComp_reflect_le_add
    {d ell : ℕ} {P Q p : ℝ[X]} (hd : d ≠ 0)
    (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPsplit : P.Splits) (hQsplit : Q.Splits)
    (hPdeg : P.natDegree = d) (hQdeg : Q.natDegree = d)
    (hell : ell ≤ d)
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree ≤ d)
    (hp0 : p.coeff 0 ≠ 0) (hp1 : 0 < p.coeff 1)
    (hcount : ∀ x : ℝ,
      (Q.roots.filter (x ≤ ·)).card ≤
        (P.roots.filter (x ≤ ·)).card + ell) :
    ∀ t : ℝ,
      ((schurSzegoComp d Q (reflect d p)).roots.filter (t < ·)).card ≤
        ((schurSzegoComp d P (reflect d p)).roots.filter
          (t < ·)).card + ell := by
  let ps := P.roots.sort (· ≤ ·)
  let qs := Q.roots.sort (· ≤ ·)
  let M := max (listUpperBound ps) (listUpperBound qs)
  have hps_pair : ps.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hqs_pair : qs.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hps_len : ps.length = d := by
    simp [ps, card_roots_of_splits hPsplit, hPdeg]
  have hqs_len : qs.length = d := by
    simp [qs, card_roots_of_splits hQsplit, hQdeg]
  have hlen : ps.length = qs.length := hps_len.trans hqs_len.symm
  have hMps : ∀ r ∈ ps, r ≤ M := by
    intro r hr
    exact (le_listUpperBound hr).trans (le_max_left _ _)
  have hMqs : ∀ r ∈ qs, r ≤ M := by
    intro r hr
    exact (le_listUpperBound hr).trans (le_max_right _ _)
  have hcount_lists : ∀ x : ℝ,
      (qs.filter (x ≤ ·)).length ≤ (ps.filter (x ≤ ·)).length + ell := by
    intro x
    have hx := hcount x
    have hPsort : (↑ps : Multiset ℝ) = P.roots :=
      Multiset.sort_eq P.roots (· ≤ ·)
    have hQsort : (↑qs : Multiset ℝ) = Q.roots :=
      Multiset.sort_eq Q.roots (· ≤ ·)
    rw [← hPsort, ← hQsort, Multiset.filter_coe, Multiset.filter_coe] at hx
    exact hx
  have hcontract := rootCountAbove_map_le_add_of_input_offset
    (T := fun f => schurSzegoComp d f (reflect d p))
    (schurSzegoComp_reflect_preservesFullDegreeRootMoves
      hd hp hpdeg hp0 hp1)
    hps_pair hqs_pair hlen hps_len (by simpa [hps_len] using hell)
    hMps hMqs hcount_lists
  have hPpoly : rootPolynomial (ps : Multiset ℝ) = P := by
    have hPsort : (↑ps : Multiset ℝ) = P.roots :=
      Multiset.sort_eq P.roots (· ≤ ·)
    rw [hPsort]
    simpa [rootPolynomial] using
      (hPsplit.eq_prod_roots_of_monic hPmonic).symm
  have hQpoly : rootPolynomial (qs : Multiset ℝ) = Q := by
    have hQsort : (↑qs : Multiset ℝ) = Q.roots :=
      Multiset.sort_eq Q.roots (· ≤ ·)
    rw [hQsort]
    simpa [rootPolynomial] using
      (hQsplit.eq_prod_roots_of_monic hQmonic).symm
  simpa [hPpoly, hQpoly] using hcontract

/-- Signed reciprocal reversal transports a closed upper count on negative PF
roots to the corresponding closed upper count on positive reciprocal roots. -/
theorem card_roots_signedReciprocal_filter_ge
    {d : ℕ} {F : ℝ[X]} (hF : IsPFPolynomial F)
    (hFdeg : F.natDegree ≤ d) (hF0 : F.coeff 0 ≠ 0)
    {s : ℝ} (hs : 0 < s) :
    ((signedReciprocal d F).roots.filter (s ≤ ·)).card =
      (F.roots.filter (-s⁻¹ ≤ ·)).card := by
  have hFne : F ≠ 0 := by
    intro hzero
    subst F
    simp at hF0
  have hFsplit : F.Splits := hF.2.1.resolve_left hFne
  let q := F.comp (-X)
  have hqsplit : q.Splits := hFsplit.comp_neg_X
  have hq0 : q.coeff 0 ≠ 0 := by
    simpa [q, Polynomial.coeff_zero_eq_eval_zero] using hF0
  have hqdeg : q.natDegree ≤ d := by
    dsimp [q]
    rw [Polynomial.natDegree_comp]
    simpa using hFdeg
  have hrev0 : q.reverse ≠ 0 :=
    DegreeDropReversal.reverse_ne_zero_of_coeff_zero_ne hq0
  have hpad :
      Multiset.filter (s ≤ ·)
        ((d - q.natDegree) • ({0} : Multiset ℝ)) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x hx
    rw [Multiset.mem_nsmul, Multiset.mem_singleton] at hx
    rcases hx with ⟨_, rfl⟩
    exact not_le_of_gt hs
  rw [signedReciprocal,
    DegreeDropReversal.reflect_eq_X_pow_mul_reverse q hqdeg,
    Polynomial.roots_mul
      (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hrev0),
    Polynomial.roots_pow, Polynomial.roots_X, Multiset.filter_add,
    Multiset.card_add, hpad, Multiset.card_zero, zero_add,
    DegreeDropReversal.card_filter_reverse_roots hqsplit hq0]
  dsimp [q]
  rw [Polynomial.roots_comp_neg_X, Multiset.filter_map, Multiset.card_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro x hx
  have hxle : x ≤ 0 := hF.2.2 x hx
  have hxne : x ≠ 0 := by
    intro hxzero
    subst x
    have hroot : F.IsRoot 0 := (Polynomial.mem_roots hFne).mp hx
    exact hF0 (by
      simpa [Polynomial.IsRoot.def, Polynomial.coeff_zero_eq_eval_zero]
        using hroot)
  have hxneg : x < 0 := lt_of_le_of_ne hxle hxne
  have hnegpos : 0 < -x := neg_pos.mpr hxneg
  change (s ≤ (-x)⁻¹) ↔ -s⁻¹ ≤ x
  rw [le_inv_comm₀ hs hnegpos]
  constructor <;> intro h <;> linarith

end RealRooted
