import RealRooted.BrandenVecchi.Chow
import RealRooted.ProductOrientation

/-!
# Leading-sign certificates for the Chow operator

This file isolates the endpoint-product rigidity needed in the leading-sign
part of Brändén--Vecchi's Chow-operator argument.  The polynomial statement is
independent of the Chow construction: equality in the endpoint-product
orientation forces normalized equality when neither polynomial has a zero
root.
-/

open Polynomial

noncomputable section

namespace RealRooted

private lemma prod_le_prod_of_forall₂_of_nonneg :
    ∀ {xs ys : List ℝ},
      List.Forall₂ (fun x y : ℝ => x ≤ y) xs ys →
      (∀ x ∈ xs, 0 ≤ x) → (∀ y ∈ ys, 0 ≤ y) →
      xs.prod ≤ ys.prod
  | [], [], _, _, _ => by simp
  | x :: xs, y :: ys, hxy, hx, hy => by
      simp only [List.forall₂_cons] at hxy
      simp only [List.prod_cons]
      exact mul_le_mul hxy.1
        (prod_le_prod_of_forall₂_of_nonneg hxy.2 (by simp_all) (by simp_all))
        (List.prod_nonneg (by simp_all)) (hy y (by simp))

private lemma list_eq_of_forall₂_le_of_pos_of_prod_eq :
    ∀ {xs ys : List ℝ},
      List.Forall₂ (fun x y : ℝ => x ≤ y) xs ys →
      (∀ x ∈ xs, 0 < x) → (∀ y ∈ ys, 0 < y) →
      xs.prod = ys.prod → xs = ys
  | [], [], _, _, _, _ => rfl
  | x :: xs, y :: ys, hxy, hx, hy, hprod => by
      simp only [List.forall₂_cons] at hxy
      simp only [List.prod_cons] at hprod
      have hxs : 0 < xs.prod := List.prod_pos (by simp_all)
      have hys : 0 < ys.prod := List.prod_pos (by simp_all)
      have htail_le : xs.prod ≤ ys.prod :=
        prod_le_prod_of_forall₂_of_nonneg hxy.2
          (fun a ha => le_of_lt (hx a (by simp [ha])))
          (fun a ha => le_of_lt (hy a (by simp [ha])))
      have hhead : x = y := by
        apply le_antisymm hxy.1
        by_contra hnot
        have hxy_lt : x < y := lt_of_not_ge hnot
        have hlt : x * xs.prod < y * ys.prod :=
          (mul_lt_mul_of_pos_right hxy_lt hxs).trans_le
            (mul_le_mul_of_nonneg_left htail_le (le_of_lt (hy y (by simp))))
        exact (ne_of_lt hlt) hprod
      subst y
      have htail : xs.prod = ys.prod := by
        exact mul_left_cancel₀ (ne_of_gt (hx x (by simp))) hprod
      rw [list_eq_of_forall₂_le_of_pos_of_prod_eq hxy.2 (by simp_all) (by simp_all) htail]

private lemma forall₂_map_zero_sub_rev :
    ∀ {xs ys : List ℝ},
      List.Forall₂ (fun x y : ℝ => x ≤ y) xs ys →
      List.Forall₂ (fun x y : ℝ => x ≤ y)
        (ys.map (0 - ·)) (xs.map (0 - ·))
  | [], [], _ => by simp
  | x :: xs, y :: ys, h => by
      simp only [List.forall₂_cons] at h
      exact List.Forall₂.cons (by simp_all) (forall₂_map_zero_sub_rev h.2)

/-- Equality in the same-degree endpoint-product orientation makes two
nonnegative proper-position polynomials equal after cross-normalization by
their leading coefficients.  The nonzero endpoint hypotheses exclude a zero
root, so equality of the positive root products is rigid. -/
theorem leadingCoeff_cross_mul_eq_of_prec_sameDegree_of_nonneg_of_eval_cross_eq
    {f g : ℝ[X]}
    (hprec : Prec f g) (hdeg : f.natDegree = g.natDegree)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hf0 : f.eval 0 ≠ 0) (hg0 : g.eval 0 ≠ 0)
    (hcross : g.eval 0 * f.leadingCoeff =
      f.eval 0 * g.leadingCoeff) :
    C g.leadingCoeff * f = C f.leadingCoeff * g := by
  rcases hprec with ⟨hf, hg, ss, rs, _hss_sorted, _hrs_sorted,
    hss_eq, hrs_eq, hshape⟩
  have hlen_ss : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hlen_rs : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  have halt : ListAlternates ss rs := by simp_all
  have hpair : List.Forall₂ (fun x y : ℝ => x ≤ y) ss rs :=
    listAlternates_forall₂_le halt
  have hpair_neg :
      List.Forall₂ (fun x y : ℝ => x ≤ y)
        (rs.map (0 - ·)) (ss.map (0 - ·)) :=
    forall₂_map_zero_sub_rev hpair
  have hrs_pos : ∀ x ∈ rs.map (0 - ·), 0 < x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hrroot : r ∈ g.roots := by
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr hr
    have hr_nonpos := roots_nonpos_of_hasNonnegCoeffs hgnn r hrroot
    have hr_ne : r ≠ 0 := by
      intro hrzero
      subst r
      exact hg0 (by
        simpa [Polynomial.IsRoot.def] using
          (Polynomial.isRoot_of_mem_roots hrroot))
    exact sub_pos.mpr (lt_of_le_of_ne hr_nonpos hr_ne)
  have hss_pos : ∀ x ∈ ss.map (0 - ·), 0 < x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hrroot : r ∈ f.roots := by
      rw [← hss_eq]
      exact Multiset.mem_coe.mpr hr
    have hr_nonpos := roots_nonpos_of_hasNonnegCoeffs hfnn r hrroot
    have hr_ne : r ≠ 0 := by
      intro hrzero
      subst r
      exact hf0 (by
        simpa [Polynomial.IsRoot.def] using
          (Polynomial.isRoot_of_mem_roots hrroot))
    exact sub_pos.mpr (lt_of_le_of_ne hr_nonpos hr_ne)
  have hflc : 0 < f.leadingCoeff := hfnn.pos_leadingCoeff hf.1
  have hglc : 0 < g.leadingCoeff := hgnn.pos_leadingCoeff hg.1
  have hprod : (rs.map (0 - ·)).prod = (ss.map (0 - ·)).prod := by
    rw [eval_eq_leadingCoeff_mul_prod_sub hf.2 0,
      eval_eq_leadingCoeff_mul_prod_sub hg.2 0, ← hss_eq, ← hrs_eq] at hcross
    simp only [Multiset.map_coe, Multiset.prod_coe] at hcross
    have hcancel : f.leadingCoeff * g.leadingCoeff * (rs.map (0 - ·)).prod =
        f.leadingCoeff * g.leadingCoeff * (ss.map (0 - ·)).prod := by
      calc
        f.leadingCoeff * g.leadingCoeff * (rs.map (0 - ·)).prod =
            g.leadingCoeff * (rs.map (0 - ·)).prod * f.leadingCoeff := by ring
        _ = f.leadingCoeff * (ss.map (0 - ·)).prod * g.leadingCoeff := hcross
        _ = f.leadingCoeff * g.leadingCoeff * (ss.map (0 - ·)).prod := by ring
    exact mul_left_cancel₀ (mul_ne_zero (ne_of_gt hflc) (ne_of_gt hglc)) hcancel
  have hmaps : rs.map (0 - ·) = ss.map (0 - ·) :=
    list_eq_of_forall₂_le_of_pos_of_prod_eq hpair_neg hrs_pos hss_pos hprod
  have hrs_ss : rs = ss := by
    have := congrArg (List.map fun x : ℝ => 0 - x) hmaps
    simpa using this
  have hroots : g.roots = f.roots := by simp_all
  have hffactor := Polynomial.Splits.eq_prod_roots hf.2
  have hgfactor := Polynomial.Splits.eq_prod_roots hg.2
  calc
    C g.leadingCoeff * f =
        C g.leadingCoeff *
          (C f.leadingCoeff * (f.roots.map fun x => X - C x).prod) := by
      exact congrArg (fun p : ℝ[X] => C g.leadingCoeff * p) hffactor
    _ = C f.leadingCoeff *
          (C g.leadingCoeff * (g.roots.map fun x => X - C x).prod) := by
      rw [hroots]
      ring
    _ = C f.leadingCoeff * g := by
      exact congrArg (fun p : ℝ[X] => C f.leadingCoeff * p) hgfactor.symm

private lemma hasPosLeadingCoeff_chowS_of_hasPosLeadingCoeff_reflect_sub
    {n : ℕ} {f : ℝ[X]} (hdegree : f.natDegree ≤ n)
    (hpos : HasPosLeadingCoeff (f.reflect n - f)) :
    HasPosLeadingCoeff (Polynomial.chowS n f) := by
  have hmul := Polynomial.X_sub_one_mul_chowS n f hdegree
  have hlc := congrArg Polynomial.leadingCoeff hmul
  have hfactorlc : (X - 1 : ℝ[X]).leadingCoeff = 1 := by
    simpa using Polynomial.leadingCoeff_X_sub_C (1 : ℝ)
  rw [Polynomial.leadingCoeff_mul, hfactorlc, one_mul] at hlc
  change 0 < (Polynomial.chowS n f).leadingCoeff
  rw [hlc]
  exact hpos

/-- Leading-sign dichotomy for the Chow operator when the input has no zero
root.  Proper position against the degree-`n` reflection either makes the
input reflection-invariant, or makes the exact quotient have positive leading
coefficient. -/
theorem chowS_eq_zero_or_hasPosLeadingCoeff_of_coeff_zero_ne
    {n : ℕ} {f : ℝ[X]} (hdegree : f.natDegree ≤ n)
    (hfnn : HasNonnegCoeffs f) (hcoeff0 : f.coeff 0 ≠ 0)
    (hprec : Prec f (f.reflect n)) :
    Polynomial.chowS n f = 0 ∨ HasPosLeadingCoeff (Polynomial.chowS n f) := by
  let g := f.reflect n
  have hgdegree : g.natDegree = n :=
    DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne hdegree hcoeff0
  have hglc : g.leadingCoeff = f.coeff 0 :=
    DegreeDropReversal.leadingCoeff_reflect_eq_coeff_zero_of_natDegree_le
      hdegree hcoeff0
  have hgnn : HasNonnegCoeffs g := hfnn.reflect n
  have hfne : f ≠ 0 := hprec.1.1
  have hgne : g ≠ 0 := hprec.2.1.1
  have hf_lc_pos : 0 < f.leadingCoeff := hfnn.pos_leadingCoeff hfne
  have hf_zero_pos : 0 < f.coeff 0 := lt_of_le_of_ne (hfnn 0) (Ne.symm hcoeff0)
  rcases hprec.natDegree_eq_or_eq_succ with heq | hsucc
  · have hfdegree : f.natDegree = n := by simpa [g, hgdegree] using heq.symm
    have hsame : f.natDegree = g.natDegree := by simp [hfdegree, hgdegree]
    have hcross_le := eval_cross_le_of_prec_sameDegree_of_nonneg
      hprec hsame hfnn hgnn
    have hge : f.leadingCoeff ≤ f.coeff 0 := by
      have hgeval0 : g.eval 0 = f.leadingCoeff := by
        change (f.reflect n).eval 0 = f.leadingCoeff
        rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
          Polynomial.revAt_zero, ← hfdegree, Polynomial.coeff_natDegree]
      change g.eval 0 * f.leadingCoeff ≤ f.eval 0 * g.leadingCoeff at hcross_le
      rw [hgeval0, ← Polynomial.coeff_zero_eq_eval_zero, hglc] at hcross_le
      nlinarith
    rcases eq_or_lt_of_le hge with hlc_eq | hlc_lt
    · left
      have hcross_eq : g.eval 0 * f.leadingCoeff =
          f.eval 0 * g.leadingCoeff := by
        have hgeval0 : g.eval 0 = f.leadingCoeff := by
          change (f.reflect n).eval 0 = f.leadingCoeff
          rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
            Polynomial.revAt_zero, ← hfdegree, Polynomial.coeff_natDegree]
        rw [hgeval0, ← Polynomial.coeff_zero_eq_eval_zero, hglc, hlc_eq]
      have hnormalized :=
        leadingCoeff_cross_mul_eq_of_prec_sameDegree_of_nonneg_of_eval_cross_eq
          hprec hsame hfnn hgnn
          (by simpa [Polynomial.coeff_zero_eq_eval_zero] using hcoeff0)
          (by
            have hgeval0 : g.eval 0 = f.leadingCoeff := by
              change (f.reflect n).eval 0 = f.leadingCoeff
              rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
                Polynomial.revAt_zero, ← hfdegree, Polynomial.coeff_natDegree]
            rw [hgeval0]
            exact ne_of_gt hf_lc_pos)
          hcross_eq
      have hfg : f = g := by
        have hnormalized' : C (f.coeff 0) * f = C (f.coeff 0) * g := by
          calc
            C (f.coeff 0) * f = C g.leadingCoeff * f := by rw [hglc]
            _ = C f.leadingCoeff * g := hnormalized
            _ = C (f.coeff 0) * g := by rw [hlc_eq]
        ext k
        have hk := congrArg (fun p : ℝ[X] => p.coeff k) hnormalized'
        simp only [Polynomial.coeff_C_mul] at hk
        exact mul_left_cancel₀ hcoeff0 hk
      have hmul := Polynomial.X_sub_one_mul_chowS n f hdegree
      rw [show f.reflect n = f from hfg.symm, sub_self] at hmul
      apply (Polynomial.monic_X_sub_C (1 : ℝ)).isRegular.left
      simpa using hmul
    · right
      apply hasPosLeadingCoeff_chowS_of_hasPosLeadingCoeff_reflect_sub hdegree
      have hdeg_eq : g.degree = f.degree := by
        rw [Polynomial.degree_eq_natDegree hgne, Polynomial.degree_eq_natDegree hfne,
          ← hsame]
      change 0 < (g - f).leadingCoeff
      rw [Polynomial.leadingCoeff_sub_of_degree_eq hdeg_eq
        (by simpa [hglc] using ne_of_gt hlc_lt)]
      exact sub_pos.mpr (by simpa [hglc] using hlc_lt)
  · right
    apply hasPosLeadingCoeff_chowS_of_hasPosLeadingCoeff_reflect_sub hdegree
    have hnat_lt : f.natDegree < g.natDegree := by
      rw [hsucc]
      exact Nat.lt_succ_self _
    change 0 < (g - f).leadingCoeff
    rw [Polynomial.leadingCoeff_sub_of_degree_lt (Polynomial.degree_lt_degree hnat_lt), hglc]
    exact hf_zero_pos

/-- If a nonzero polynomial has zero constant coefficient and degree strictly
below the reflection bound, its reflection has the same common factor `X`;
after removing it, the reflection bound drops by two. -/
theorem reflect_eq_X_mul_reflect_divX_of_coeff_zero_of_natDegree_lt
    {n : ℕ} {f : ℝ[X]} (hfne : f ≠ 0) (hcoeff0 : f.coeff 0 = 0)
    (hdegree : f.natDegree < n) :
    f.reflect n = X * (f.divX.reflect (n - 2)) := by
  have hfactor : f = X * f.divX :=
    DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hcoeff0
  have hdivne : f.divX ≠ 0 := by
    intro hzero
    rw [hfactor, hzero, mul_zero] at hfne
    exact hfne rfl
  have hfdeg_pos : 0 < f.natDegree := by
    rw [hfactor, Polynomial.natDegree_X_mul hdivne]
    exact Nat.succ_pos _
  have hn : 2 ≤ n := by lia
  have hf_le : f.natDegree ≤ n - 1 := by lia
  have hdiv_le : f.divX.natDegree ≤ n - 2 := by
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    lia
  have hshift : f.reflect n = f.reflect (n - 1) * X := by
    have h := Polynomial.reflect_mul f (1 : ℝ[X]) hf_le (by simp : (1 : ℝ[X]).natDegree ≤ 1)
    rw [Nat.sub_add_cancel (by lia : 1 ≤ n)] at h
    simpa using h
  have hcore : f.reflect (n - 1) = f.divX.reflect (n - 2) := by
    calc
      f.reflect (n - 1) = (X * f.divX).reflect (n - 1) :=
        congrArg (fun p : ℝ[X] => p.reflect (n - 1)) hfactor
      _ = X.reflect 1 * f.divX.reflect (n - 2) := by
        rw [show n - 1 = 1 + (n - 2) by lia,
          Polynomial.reflect_mul X f.divX (by simp) hdiv_le]
      _ = f.divX.reflect (n - 2) := by simp
  rw [hshift, hcore]
  ring

/-- Removing the common zero root from the input lowers the Chow reflection
bound by two and contributes one factor of `X` to the exact quotient. -/
theorem chowS_eq_X_mul_chowS_divX_of_coeff_zero_of_natDegree_lt
    {n : ℕ} {f : ℝ[X]} (hfne : f ≠ 0) (hcoeff0 : f.coeff 0 = 0)
    (hdegree : f.natDegree < n) :
    Polynomial.chowS n f = X * Polynomial.chowS (n - 2) f.divX := by
  have hfactor : f = X * f.divX :=
    DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hcoeff0
  have hdivne : f.divX ≠ 0 := by
    intro hzero
    rw [hfactor, hzero, mul_zero] at hfne
    exact hfne rfl
  have hfdeg_pos : 0 < f.natDegree := by
    rw [hfactor, Polynomial.natDegree_X_mul hdivne]
    exact Nat.succ_pos _
  have hn : 2 ≤ n := by lia
  have hdiv_le : f.divX.natDegree ≤ n - 2 := by
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    lia
  have hhigh := Polynomial.X_sub_one_mul_chowS n f hdegree.le
  have hlow := Polynomial.X_sub_one_mul_chowS (n - 2) f.divX hdiv_le
  have hreflect :=
    reflect_eq_X_mul_reflect_divX_of_coeff_zero_of_natDegree_lt hfne hcoeff0 hdegree
  apply (Polynomial.monic_X_sub_C (1 : ℝ)).isRegular.left
  calc
    (X - 1) * Polynomial.chowS n f = f.reflect n - f := hhigh
    _ = X * f.divX.reflect (n - 2) - X * f.divX := by
      rw [hreflect]
      exact congrArg (fun p : ℝ[X] => X * f.divX.reflect (n - 2) - p) hfactor
    _ = X * (f.divX.reflect (n - 2) - f.divX) := by ring
    _ = X * ((X - 1) * Polynomial.chowS (n - 2) f.divX) := by rw [hlow]
    _ = (X - 1) * (X * Polynomial.chowS (n - 2) f.divX) := by ring

/-- Brändén--Vecchi's leading-sign certificate for the Chow operator.  For a
nonnegative polynomial in proper position with its degree-bounded reflection,
the Chow quotient is either zero or has positive leading coefficient. -/
theorem chowS_eq_zero_or_hasPosLeadingCoeff
    {n : ℕ} {f : ℝ[X]} (hdegree : f.natDegree ≤ n)
    (hfnn : HasNonnegCoeffs f) (hprec : Prec f (f.reflect n)) :
    Polynomial.chowS n f = 0 ∨ HasPosLeadingCoeff (Polynomial.chowS n f) := by
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hcoeff0 : f.coeff 0 = 0
    · have hfne : f ≠ 0 := hprec.1.1
      have hg_ne : f.reflect n ≠ 0 := hprec.2.1.1
      have href_degree_le : (f.reflect n).natDegree ≤ n := by
        exact Polynomial.natDegree_reflect_le.trans (by simp [hdegree])
      have href_degree_ne : (f.reflect n).natDegree ≠ n := by
        intro heq
        have hlc_ne := Polynomial.leadingCoeff_ne_zero.mpr hg_ne
        apply hlc_ne
        rw [Polynomial.leadingCoeff, heq, Polynomial.coeff_reflect,
          Polynomial.revAt_le le_rfl, Nat.sub_self]
        exact hcoeff0
      have hfdegree_lt : f.natDegree < n :=
        lt_of_le_of_lt hprec.natDegree_le (lt_of_le_of_ne href_degree_le href_degree_ne)
      have hfactor : f = X * f.divX :=
        DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hcoeff0
      have hreflect :=
        reflect_eq_X_mul_reflect_divX_of_coeff_zero_of_natDegree_lt
          hfne hcoeff0 hfdegree_lt
      have hdivne : f.divX ≠ 0 := by
        intro hzero
        rw [hfactor, hzero, mul_zero] at hfne
        exact hfne rfl
      have hn : 2 ≤ n := by
        have hfdeg_pos : 0 < f.natDegree := by
          rw [hfactor, Polynomial.natDegree_X_mul hdivne]
          exact Nat.succ_pos _
        lia
      have hdiv_le : f.divX.natDegree ≤ n - 2 := by
        rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
        lia
      have hdiv_prec : Prec f.divX (f.divX.reflect (n - 2)) := by
        apply prec_of_prec_mul_X_sub_C_both 0
        have hprec' : Prec (X * f.divX) (X * f.divX.reflect (n - 2)) := by
          rw [← hfactor, ← hreflect]
          exact hprec
        simpa using hprec'
      have hrec := ih (n - 2) (by lia) hdiv_le hfnn.divX hdiv_prec
      have hchow :=
        chowS_eq_X_mul_chowS_divX_of_coeff_zero_of_natDegree_lt
          hfne hcoeff0 hfdegree_lt
      rcases hrec with hzero | hpos
      · left
        rw [hchow, hzero, mul_zero]
      · right
        rw [hchow]
        exact hpos.X_mul
    · exact chowS_eq_zero_or_hasPosLeadingCoeff_of_coeff_zero_ne
        hdegree hfnn hcoeff0 hprec

end RealRooted
