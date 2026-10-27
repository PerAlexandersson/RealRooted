module

import RealRooted.Linear
import RealRooted.OrderedRoots
import RealRooted.WagnerRightSum
public import RealRooted.Mesh.FiniteDifference

/-!
# Discrete multiplier operators

The operator `p ↦ a p + b X (p - p(X - 1))` of Brändén, Krasikov, and Shapiro, *Elements of
Pólya--Schur theory in finite difference setting*, Proc. AMS 144 (2016), Theorem 5, preserves
real-rooted polynomials with nonnegative roots and mesh at least one, provided `a` and `b` have
the same sign.  See RealRooted issue #2070.

The paper's proof shows that `W = a p + b X Δp` is in proper position with both `p(x)` and
`p(x - 1)`, where `Δp = p(x) - p(x - 1)`.  The ordered roots then satisfy
`w_i ≤ θ_i` and `θ_i + 1 ≤ w_{i+1}`, which is exactly the mesh bound.  The nonnegative roots of
`W` follow because `p` and `X Δp` have the same sign on the negative reals.
-/

public section

open Polynomial

namespace RealRooted

noncomputable section

/-! ### Stable pencils and the difference `p - p(X - 1)` -/

private theorem neg_inv_im_pos {w : ℂ} (hw : 0 < w.im) : 0 < (-w⁻¹).im := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hquot : 0 < w.im / Complex.normSq w := div_pos hw (Complex.normSq_pos.mpr hw0)
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact hquot

/-- If `q + w p` is stable, then so is `p + w (p - q)`. -/
private theorem stablePencil_sub_of_stable {p q : ℝ[X]}
    (h : IsUpperHalfPlaneStablePencil q p) :
    IsUpperHalfPlaneStablePencil p (p - q) := by
  intro z w hz hw hzero
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hu : 0 < (-w⁻¹ - 1).im := by
    simpa using neg_inv_im_pos hw
  apply h z (-w⁻¹ - 1) hz hu
  have hmap : complexify (p - q) = complexify p - complexify q := by simp [complexify]
  rw [hmap, eval_sub] at hzero
  have hinv : w * w⁻¹ = 1 := mul_inv_cancel₀ hw0
  have hmul : w * ((complexify q).eval z + (-w⁻¹ - 1) * (complexify p).eval z) = 0 := by
    linear_combination (-1 : ℂ) * hzero + (-(complexify p).eval z) * hinv
  exact (mul_eq_zero.mp hmul).resolve_left hw0

/-- If `q + w p` is stable, then so is `q + w (p - q)`. -/
private theorem stablePencil_left_sub_of_stable {p q : ℝ[X]}
    (h : IsUpperHalfPlaneStablePencil q p) :
    IsUpperHalfPlaneStablePencil q (p - q) := by
  intro z w hz hw hzero
  have hv : 0 < (w - 1).im := by simpa using hw
  have hv0 : w - 1 ≠ 0 := by
    intro h0
    rw [h0] at hv
    simp at hv
  have hu : 0 < (-(w - 1)⁻¹ - 1).im := by
    simpa using neg_inv_im_pos hv
  apply h z (-(w - 1)⁻¹ - 1) hz hu
  have hmap : complexify (p - q) = complexify p - complexify q := by simp [complexify]
  rw [hmap, eval_sub] at hzero
  have hinv : (w - 1) * (w - 1)⁻¹ = 1 := mul_inv_cancel₀ hv0
  have hmul : (w - 1) * ((complexify q).eval z +
      (-(w - 1)⁻¹ - 1) * (complexify p).eval z) = 0 := by
    linear_combination (-1 : ℂ) * hzero + (-(complexify p).eval z) * hinv
  exact (mul_eq_zero.mp hmul).resolve_left hv0

private theorem natDegree_comp_X_sub_C_one (p : ℝ[X]) :
    (p.comp (X - C 1)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_X_sub_C, mul_one]

private theorem leadingCoeff_comp_X_sub_C_one (p : ℝ[X]) :
    (p.comp (X - C 1)).leadingCoeff = p.leadingCoeff := by
  rw [leadingCoeff_comp (by rw [natDegree_X_sub_C]; exact one_ne_zero), leadingCoeff_X_sub_C,
    one_pow, mul_one]

private theorem roots_comp_X_sub_C_one (p : ℝ[X]) :
    (p.comp (X - C 1)).roots = p.roots.map (· + 1) := by
  rw [show X - C (1 : ℝ) = X + C (-1) by simp [sub_eq_add_neg], roots_comp_X_add_C]
  simp only [sub_neg_eq_add]

private theorem sort_roots_comp_X_sub_C_one (p : ℝ[X]) :
    (p.comp (X - C 1)).roots.sort (· ≤ ·) = (p.roots.sort (· ≤ ·)).map (· + 1) := by
  have hrs : (p.roots.sort (· ≤ ·)).Pairwise (· ≤ ·) := Multiset.pairwise_sort p.roots (· ≤ ·)
  have hmap : ((p.roots.sort (· ≤ ·)).map (· + 1)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact hrs.imp (by intro a b hab; linarith)
  apply List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) hmap
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq, roots_comp_X_sub_C_one, ← Multiset.map_coe, Multiset.sort_eq]

private theorem orderedRoot_comp_X_sub_C_one (p : ℝ[X]) {n : ℕ} (hcard : p.roots.card = n)
    (i : Fin n) :
    orderedRoot (p.comp (X - C 1)) n i = orderedRoot p n i + 1 := by
  have hi : (i : ℕ) < (p.roots.sort (· ≤ ·)).length := by
    rw [Multiset.length_sort, hcard]
    exact i.2
  unfold orderedRoot
  rw [sort_roots_comp_X_sub_C_one]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [List.getElem?_eq_getElem hi]
  simp

/-- The difference `p - p(X - 1)` of a polynomial of degree `m + 1` has degree `m` and
leading coefficient `(m + 1)` times that of `p`. -/
private theorem sub_comp_X_sub_C_one_natDegree_coeff {p : ℝ[X]} {m : ℕ}
    (hp : p.natDegree = m + 1) :
    (p - p.comp (X - C 1)).natDegree = m ∧
      (p - p.comp (X - C 1)).coeff m = ((m : ℝ) + 1) * p.leadingCoeff := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp
  have hq : p.comp (X - C 1) = taylor (-1 : ℝ) p := by
    rw [taylor_apply]
    congr 1
    simp [sub_eq_add_neg]
  rw [hq]
  have htop : (taylor (-1 : ℝ) p).coeff (m + 1) = p.coeff (m + 1) := by
    have h := coeff_taylor_natDegree (r := (-1 : ℝ)) (f := p)
    rw [hp] at h
    rw [h, leadingCoeff, hp]
  have hmid : (taylor (-1 : ℝ) p).coeff m = p.coeff m - ((m : ℝ) + 1) * p.leadingCoeff := by
    rw [taylor_coeff]
    have hdeg : (hasseDeriv m p).natDegree < 2 := by
      have := natDegree_hasseDeriv_le p m
      lia
    rw [eval_eq_sum_range' hdeg]
    have h1 : (1 + m).choose m = m + 1 := by
      rw [add_comm]
      exact Nat.choose_succ_self_right m
    have h2 : p.coeff (1 + m) = p.leadingCoeff := by
      rw [add_comm, leadingCoeff, hp]
    simp [Finset.sum_range_succ, hasseDeriv_coeff, h1, h2]
    ring
  have hcoef : (p - taylor (-1 : ℝ) p).coeff m = ((m : ℝ) + 1) * p.leadingCoeff := by
    rw [coeff_sub, hmid]
    ring
  have hle : (p - taylor (-1 : ℝ) p).natDegree ≤ m := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_sub]
    rcases Nat.lt_or_ge (m + 1) N with h | h
    · have h1 : p.coeff N = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
      have h2 : (taylor (-1 : ℝ) p).coeff N = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [natDegree_taylor]; lia)
      rw [h1, h2, sub_zero]
    · have hN' : N = m + 1 := by lia
      subst hN'
      rw [htop, sub_self]
  have hne : ((m : ℝ) + 1) * p.leadingCoeff ≠ 0 :=
    mul_ne_zero (by positivity) (leadingCoeff_ne_zero.mpr hp0)
  exact ⟨natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hcoef]; exact hne), hcoef⟩

/-- Proper position of the difference `p - p(X - 1)` with `p(x)` and `p(x - 1)`, for `p` of
positive leading coefficient and mesh at least one. -/
theorem strictInterl_sub_comp_X_sub_C_one {p : ℝ[X]} {m : ℕ}
    (hpos : HasPosLeadingCoeff p) (hn : p.natDegree = m + 1) (hmesh : p.MeshGE 1) :
    HasPosLeadingCoeff (p - p.comp (X - C 1)) ∧ (p - p.comp (X - C 1)).natDegree = m ∧
      StrictInterl (p - p.comp (X - C 1)) p ∧
      StrictInterl (p - p.comp (X - C 1)) (p.comp (X - C 1)) := by
  obtain ⟨hdeg, hcoeff⟩ := sub_comp_X_sub_C_one_natDegree_coeff hn
  have hpos' : 0 < p.leadingCoeff := hpos
  have hTpos : HasPosLeadingCoeff (p - p.comp (X - C 1)) := by
    unfold HasPosLeadingCoeff
    rw [leadingCoeff, hdeg, hcoeff]
    exact mul_pos (by positivity) hpos'
  have hp0 : p ≠ 0 := hpos.ne_zero
  have hstable : IsUpperHalfPlaneStablePencil (p.comp (X - C 1)) p :=
    ((Polynomial.MeshGE.iff_eq_zero_or_stablePencil one_pos).1 hmesh).resolve_left hp0
  have hqpos : HasPosLeadingCoeff (p.comp (X - C 1)) := by
    unfold HasPosLeadingCoeff
    rw [leadingCoeff_comp_X_sub_C_one]
    exact hpos'
  have hqdeg : (p.comp (X - C 1)).natDegree ≠ 0 := by
    rw [natDegree_comp_X_sub_C_one]
    lia
  exact ⟨hTpos, hdeg,
    (isUpperHalfPlaneStablePencil_iff_strictInterl hpos hTpos (by lia)).1
      (stablePencil_sub_of_stable hstable),
    (isUpperHalfPlaneStablePencil_iff_strictInterl hqpos hTpos hqdeg).1
      (stablePencil_left_sub_of_stable hstable)⟩

/-! ### Multiplying by `X` -/

private theorem listInterlaces_exists_le :
    ∀ (ss rs : List ℝ), ListInterlaces ss rs → ∀ s ∈ ss, ∃ r ∈ rs, r ≤ s
  | [], _, _, s, hs => by simp at hs
  | _ :: _, [], h, _, _ => by simp [ListInterlaces] at h
  | _ :: _, [_], h, _, _ => by simp [ListInterlaces] at h
  | _ :: ss, r₁ :: r₂ :: rs, h, s, hs => by
      obtain ⟨hr, _, htail⟩ := h
      rcases List.mem_cons.mp hs with hs0 | hs'
      · exact ⟨r₁, by simp, hs0 ▸ hr⟩
      · obtain ⟨r, hr', hle⟩ := listInterlaces_exists_le ss (r₂ :: rs) htail s hs'
        exact ⟨r, List.mem_cons_of_mem _ hr', hle⟩

/-- If `T ≪ p` with `deg T + 1 = deg p` and `p` has nonnegative roots, then `X T ≪ p`, and
`T` has nonnegative roots. -/
private theorem strictInterl_X_mul_of_succDegree {T p : ℝ[X]} (h : StrictInterl T p)
    (hdeg : T.natDegree + 1 = p.natDegree) (hp : ∀ r ∈ p.roots, 0 ≤ r) :
    StrictInterl (X * T) p ∧ ∀ s ∈ T.roots, 0 ≤ s := by
  obtain ⟨hT, hP, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩ := h
  have hsslen : ss.length = T.natDegree := hT.2.length_eq_natDegree_of_coe_eq_roots hss_eq
  have hrslen : rs.length = p.natDegree := hP.2.length_eq_natDegree_of_coe_eq_roots hrs_eq
  have hint : ListInterlaces ss rs := by
    rcases hshape with ⟨_, hint⟩ | ⟨hlen, _⟩
    · exact hint
    · exfalso
      lia
  have hnonneg : ∀ s ∈ ss, 0 ≤ s := by
    intro s hs
    obtain ⟨r, hr, hle⟩ := listInterlaces_exists_le ss rs hint s hs
    have hrmem : r ∈ p.roots := by
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr hr
    exact (hp r hrmem).trans hle
  have hTnn : ∀ s ∈ T.roots, 0 ≤ s := by
    intro s hs
    rw [← hss_eq] at hs
    exact hnonneg s (Multiset.mem_coe.mp hs)
  have hrsne : rs ≠ [] := by
    rintro rfl
    simp at hrslen
    lia
  obtain ⟨r₁, rs', rfl⟩ := List.exists_cons_of_ne_nil hrsne
  have hr₁ : 0 ≤ r₁ := by
    apply hp
    rw [← hrs_eq]
    simp
  have hXTne : X * T ≠ 0 := mul_ne_zero X_ne_zero hT.1
  have hroots : (↑(0 :: ss) : Multiset ℝ) = (X * T).roots := by
    rw [roots_mul hXTne, roots_X, ← hss_eq]
    simp
  simp only [List.length_cons] at hrslen
  refine ⟨⟨⟨hXTne, Polynomial.Splits.X.mul hT.2⟩, hP, 0 :: ss, r₁ :: rs',
    List.pairwise_cons.mpr ⟨hnonneg, hss⟩, hrs, hroots, hrs_eq,
    Or.inr ⟨?_, ⟨hr₁, hint⟩⟩⟩, hTnn⟩
  simp only [List.length_cons]
  lia

/-! ### The sum `a p + b X T` -/

private theorem strictInterl_add_C_mul_X_mul {p q T : ℝ[X]} {a b : ℝ} {n : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a ∨ 0 < b)
    (hpos : HasPosLeadingCoeff p) (hpdeg : p.natDegree = n) (hpq : StrictInterl p q)
    (hTpos : HasPosLeadingCoeff T) (hTdeg : T.natDegree + 1 = n)
    (hXTp : StrictInterl (X * T) p) (hXTq : StrictInterl (X * T) q) :
    StrictInterl (C a * p + C b * (X * T)) p ∧ StrictInterl (C a * p + C b * (X * T)) q ∧
      (C a * p + C b * (X * T)).natDegree = n ∧
        HasPosLeadingCoeff (C a * p + C b * (X * T)) := by
  have hp0 : p ≠ 0 := hpos.ne_zero
  have hT0 : T ≠ 0 := hTpos.ne_zero
  have hXTdeg : (X * T).natDegree = n := by
    rw [natDegree_X_mul hT0]
    lia
  have hf1 : ∀ c : ℝ, 0 < c → StrictInterl (C c * p) p ∧ StrictInterl (C c * p) q ∧
      (C c * p).natDegree = n ∧ HasPosLeadingCoeff (C c * p) := by
    intro c hc
    exact ⟨(StrictInterl.refl hp0 hpq.1.2).C_mul_left hc.ne', hpq.C_mul_left hc.ne',
      by rw [natDegree_C_mul hc.ne', hpdeg], hasPosLeadingCoeff_C_mul hc hpos⟩
  have hf2 : ∀ c : ℝ, 0 < c → StrictInterl (C c * (X * T)) p ∧
      StrictInterl (C c * (X * T)) q ∧ (C c * (X * T)).natDegree = n ∧
        HasPosLeadingCoeff (C c * (X * T)) := by
    intro c hc
    exact ⟨hXTp.C_mul_left hc.ne', hXTq.C_mul_left hc.ne',
      by rw [natDegree_C_mul hc.ne', hXTdeg], hasPosLeadingCoeff_C_mul hc hTpos.X_mul⟩
  rcases ha.eq_or_lt with ha0 | ha'
  · subst ha0
    have hb' : 0 < b := hab.resolve_left (lt_irrefl 0)
    have e : C (0 : ℝ) * p + C b * (X * T) = C b * (X * T) := by simp
    rw [e]
    exact hf2 b hb'
  · rcases hb.eq_or_lt with hb0 | hb'
    · subst hb0
      have e : C a * p + C (0 : ℝ) * (X * T) = C a * p := by simp
      rw [e]
      exact hf1 a ha'
    · obtain ⟨h1p, h1q, h1d, h1pos⟩ := hf1 a ha'
      obtain ⟨h2p, h2q, h2d, h2pos⟩ := hf2 b hb'
      have hdeg : (C a * p).natDegree = (C b * (X * T)).natDegree := by rw [h1d, h2d]
      refine ⟨StrictInterl.add_of_right_of_posLeadingCoeff h1p h2p h1pos h2pos,
        StrictInterl.add_of_right_of_posLeadingCoeff h1q h2q h1pos h2pos, ?_,
        hasPosLeadingCoeff_add_of_same_natDegree hdeg h1pos h2pos⟩
      rw [natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff hdeg h1pos h2pos, h1d]

/-- If `W ≪ p` and `W ≪ p(x - 1)` have the same degree as `p`, then `W` has mesh at least one:
`w_i ≤ θ_i` and `θ_i + 1 ≤ w_{i + 1}`. -/
private theorem meshGE_one_of_strictInterl_comp {W p : ℝ[X]} {n : ℕ}
    (hWp : StrictInterl W p) (hWq : StrictInterl W (p.comp (X - C 1)))
    (hWdeg : W.natDegree = n) (hpdeg : p.natDegree = n) : W.MeshGE 1 := by
  have hWs : W.Splits := hWp.1.2
  have hps : p.Splits := hWp.2.1.2
  have hqs : (p.comp (X - C 1)).Splits := hWq.2.1.2
  have hcardp : p.roots.card = n := by
    rw [splits_iff_card_roots.mp hps, hpdeg]
  have hcardW : W.roots.card = n := by
    rw [splits_iff_card_roots.mp hWs, hWdeg]
  have hqdeg : (p.comp (X - C 1)).natDegree = n := by
    rw [natDegree_comp_X_sub_C_one, hpdeg]
  have hb1 := (strictInterl_iff_orderedRoot_bounds hWp.1.1 hWs hWp.2.1.1 hps hWdeg hpdeg).mp hWp
  have hb2 := (strictInterl_iff_orderedRoot_bounds hWq.1.1 hWs hWq.2.1.1 hqs hWdeg hqdeg).mp hWq
  refine ⟨hWs, zero_le_one, fun i hi => ?_⟩
  have hlen : (W.roots.sort (· ≤ ·)).length = n := by
    rw [Multiset.length_sort, hcardW]
  rw [hlen] at hi
  have hi0 : i < n := by lia
  have h1 : orderedRoot W n ⟨i, hi0⟩ ≤ orderedRoot p n ⟨i, hi0⟩ := hb1.1 ⟨i, hi0⟩
  have h2 : orderedRoot (p.comp (X - C 1)) n ⟨i, hi0⟩ ≤ orderedRoot W n ⟨i + 1, hi⟩ :=
    hb2.2 ⟨i, hi0⟩ hi
  rw [orderedRoot_comp_X_sub_C_one p hcardp] at h2
  change orderedRoot W n ⟨i, hi0⟩ + 1 ≤ orderedRoot W n ⟨i + 1, hi⟩
  linarith

/-- On the negative reals `a p + b X T` has no zero when `p` and `X T` have positive leading
coefficients, degree `n`, and nonnegative roots. -/
private theorem hasOnlyNonnegRoots_add_C_mul_X_mul {p T : ℝ[X]} {a b : ℝ} {n : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a ∨ 0 < b)
    (hpos : HasPosLeadingCoeff p) (hpdeg : p.natDegree = n) (hnn : ∀ r ∈ p.roots, 0 ≤ r)
    (hTpos : HasPosLeadingCoeff T) (hTdeg : T.natDegree + 1 = n)
    (hTnn : ∀ s ∈ T.roots, 0 ≤ s)
    (hWne : C a * p + C b * (X * T) ≠ 0) (hWs : (C a * p + C b * (X * T)).Splits) :
    HasOnlyNonnegRoots (C a * p + C b * (X * T)) := by
  have hp0 : p ≠ 0 := hpos.ne_zero
  have hT0 : T ≠ 0 := hTpos.ne_zero
  have hXTne : X * T ≠ 0 := mul_ne_zero X_ne_zero hT0
  have hXTdeg : (X * T).natDegree = n := by
    rw [natDegree_X_mul hT0]
    lia
  have hXTpos : HasPosLeadingCoeff (X * T) := hTpos.X_mul
  refine Or.inr ⟨hWs, fun r hr => ?_⟩
  by_contra hneg
  have hneg' : r < 0 := lt_of_not_ge hneg
  have hroot : (C a * p + C b * (X * T)).eval r = 0 :=
    Polynomial.IsRoot.def.mp ((mem_roots hWne).mp hr)
  have hr' : ∀ t ∈ p.roots, r < t := fun t ht => lt_of_lt_of_le hneg' (hnn t ht)
  have hXTroots : ∀ t ∈ (X * T).roots, r < t := by
    intro t ht
    rw [roots_mul hXTne, roots_X] at ht
    rcases Multiset.mem_add.mp ht with h | h
    · rw [Multiset.mem_singleton] at h
      rw [h]
      exact hneg'
    · exact lt_of_lt_of_le hneg' (hTnn t h)
  simp only [eval_add, eval_C, eval_mul, eval_X] at hroot
  rcases Nat.even_or_odd n with he | ho
  · have h1 : 0 < p.eval r := eval_pos_of_all_roots_gt_of_even hp0 hpos (by rwa [hpdeg]) hr'
    have h2 : 0 < (X * T).eval r :=
      eval_pos_of_all_roots_gt_of_even hXTne hXTpos (by rwa [hXTdeg]) hXTroots
    have h2' : 0 < r * T.eval r := by simpa using h2
    rcases hab with h | h
    · linarith [mul_pos h h1, mul_nonneg hb h2'.le]
    · linarith [mul_pos h h2', mul_nonneg ha h1.le]
  · have h1 : p.eval r < 0 := eval_neg_of_all_roots_gt_of_odd hp0 hpos (by rwa [hpdeg]) hr'
    have h2 : (X * T).eval r < 0 :=
      eval_neg_of_all_roots_gt_of_odd hXTne hXTpos (by rwa [hXTdeg]) hXTroots
    have h2' : r * T.eval r < 0 := by simpa using h2
    rcases hab with h | h
    · linarith [mul_pos h (neg_pos.mpr h1), mul_nonneg hb (neg_nonneg.mpr h2'.le)]
    · linarith [mul_pos h (neg_pos.mpr h2'), mul_nonneg ha (neg_nonneg.mpr h1.le)]

/-! ### The main theorems -/

private theorem discreteMultiplier_of_posLeadingCoeff {p : ℝ[X]} {m : ℕ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a ∨ 0 < b)
    (hpos : HasPosLeadingCoeff p) (hn : p.natDegree = m + 1) (hmesh : p.MeshGE 1)
    (hnn : ∀ r ∈ p.roots, 0 ≤ r) :
    (C a * p + C b * (X * (p - p.comp (X - C 1)))).MeshGE 1 ∧
      HasOnlyNonnegRoots (C a * p + C b * (X * (p - p.comp (X - C 1)))) := by
  obtain ⟨hTpos, hTdeg, hTp, hTq⟩ := strictInterl_sub_comp_X_sub_C_one hpos hn hmesh
  have hp0 : p ≠ 0 := hpos.ne_zero
  have hq0 : p.comp (X - C 1) ≠ 0 :=
    leadingCoeff_ne_zero.mp (by
      rw [leadingCoeff_comp_X_sub_C_one]
      exact leadingCoeff_ne_zero.mpr hp0)
  have hpq : StrictInterl p (p.comp (X - C 1)) :=
    ((Polynomial.MeshGE.iff_interl_comp_sub one_pos).1 hmesh).toStrictInterl_of_ne hp0 hq0
  have hqnn : ∀ r ∈ (p.comp (X - C 1)).roots, 0 ≤ r := by
    intro r hr
    rw [roots_comp_X_sub_C_one] at hr
    obtain ⟨s, hs, hsr⟩ := Multiset.mem_map.mp hr
    have hs0 := hnn s hs
    have hr' : r = s + 1 := hsr.symm
    linarith
  have hqdeg : (p.comp (X - C 1)).natDegree = m + 1 := by
    rw [natDegree_comp_X_sub_C_one, hn]
  obtain ⟨hXTp, hTnn⟩ := strictInterl_X_mul_of_succDegree hTp (by lia) hnn
  obtain ⟨hXTq, -⟩ := strictInterl_X_mul_of_succDegree hTq (by lia) hqnn
  obtain ⟨hWp, hWq, hWdeg, hWpos⟩ := strictInterl_add_C_mul_X_mul ha hb hab hpos hn hpq
    hTpos (by lia) hXTp hXTq
  exact ⟨meshGE_one_of_strictInterl_comp hWp hWq hWdeg hn,
    hasOnlyNonnegRoots_add_C_mul_X_mul ha hb hab hpos hn hnn hTpos (by lia) hTnn
      hWpos.ne_zero hWp.1.2⟩

/-- Multiplication by a nonzero scalar does not change the property of having only nonnegative
roots. -/
theorem HasOnlyNonnegRoots.C_mul_iff {c : ℝ} (hc : c ≠ 0) (p : ℝ[X]) :
    HasOnlyNonnegRoots (C c * p) ↔ HasOnlyNonnegRoots p := by
  by_cases hp0 : p = 0
  · simp [hp0, HasOnlyNonnegRoots]
  have hne : C c * p ≠ 0 := mul_ne_zero (C_ne_zero.mpr hc) hp0
  unfold HasOnlyNonnegRoots
  rw [roots_C_mul p hc]
  constructor
  · rintro (h | ⟨hs, hr⟩)
    · exact absurd h hne
    · exact Or.inr ⟨hs.of_dvd hne (dvd_mul_left p (C c)), hr⟩
  · rintro (h | ⟨hs, hr⟩)
    · exact absurd h hp0
    · exact Or.inr ⟨hs.C_mul c, hr⟩

private theorem discreteMultiplier_of_natDegree_ne_zero {p : ℝ[X]} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a ∨ 0 < b)
    (hp : p.MeshGE 1) (hpnn : HasOnlyNonnegRoots p) (hdeg : p.natDegree ≠ 0) :
    (C a * p + C b * (X * (p - p.comp (X - C 1)))).MeshGE 1 ∧
      HasOnlyNonnegRoots (C a * p + C b * (X * (p - p.comp (X - C 1)))) := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hdeg
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hdeg
  have hn : p.natDegree = m + 1 := hm
  have hnn : ∀ r ∈ p.roots, 0 ≤ r := (hpnn.resolve_left hp0).2
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp0) with hneg | hposlc
  · have hp' : (C (-1 : ℝ) * p).MeshGE 1 :=
      (Polynomial.MeshGE.C_mul_iff p 1 (by norm_num)).2 hp
    have hnn' : ∀ r ∈ (C (-1 : ℝ) * p).roots, 0 ≤ r := by
      rw [roots_C_mul p (by norm_num)]
      exact hnn
    have hdeg' : (C (-1 : ℝ) * p).natDegree = m + 1 := by
      rw [natDegree_C_mul (by norm_num), hn]
    have hpos' : HasPosLeadingCoeff (C (-1 : ℝ) * p) := by
      unfold HasPosLeadingCoeff
      rw [leadingCoeff_mul, leadingCoeff_C]
      linarith
    obtain ⟨h1, h2⟩ := discreteMultiplier_of_posLeadingCoeff ha hb hab hpos' hdeg' hp' hnn'
    have e : C a * (C (-1 : ℝ) * p) +
        C b * (X * (C (-1 : ℝ) * p - (C (-1 : ℝ) * p).comp (X - C 1))) =
        C (-1 : ℝ) * (C a * p + C b * (X * (p - p.comp (X - C 1)))) := by
      simp only [mul_comp, C_comp]
      ring
    rw [e] at h1 h2
    exact ⟨(Polynomial.MeshGE.C_mul_iff _ 1 (by norm_num)).1 h1,
      (HasOnlyNonnegRoots.C_mul_iff (by norm_num) _).1 h2⟩
  · exact discreteMultiplier_of_posLeadingCoeff ha hb hab hposlc hn hp hnn

/-- BKS 2016, Theorem 5: `p ↦ a p + b X (p - p(X - 1))` with `a, b ≥ 0` preserves real-rooted
polynomials with nonnegative roots and mesh at least one. -/
theorem meshGE_one_add_X_mul_meshDifference {p : ℝ[X]} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : p.MeshGE 1) (hpnn : HasOnlyNonnegRoots p) :
    (C a * p + C b * (X * meshDifference 1 1 p)).MeshGE 1 ∧
      HasOnlyNonnegRoots (C a * p + C b * (X * meshDifference 1 1 p)) := by
  have hT : meshDifference 1 1 p = p - p.comp (X - C 1) := by simp [meshDifference]
  rw [hT]
  by_cases hdeg : p.natDegree = 0
  · have hTzero : p - p.comp (X - C 1) = 0 := by
      rw [eq_C_of_natDegree_eq_zero hdeg]
      simp
    rw [hTzero, mul_zero, mul_zero, add_zero]
    refine ⟨Polynomial.MeshGE.of_natDegree_le_one (hp.1.C_mul a)
      ((natDegree_C_mul_le a p).trans (by lia)) zero_le_one, ?_⟩
    by_cases ha0 : a = 0
    · left
      simp [ha0]
    · exact (HasOnlyNonnegRoots.C_mul_iff ha0 p).2 hpnn
  · rcases ha.eq_or_lt with ha0 | ha'
    · rcases hb.eq_or_lt with hb0 | hb'
      · subst ha0
        subst hb0
        have e : C (0 : ℝ) * p + C (0 : ℝ) * (X * (p - p.comp (X - C 1))) = 0 := by simp
        rw [e]
        exact ⟨Polynomial.MeshGE.of_natDegree_le_one (by simp) (by simp) zero_le_one,
          Or.inl rfl⟩
      · exact discreteMultiplier_of_natDegree_ne_zero ha hb (Or.inr hb') hp hpnn hdeg
    · exact discreteMultiplier_of_natDegree_ne_zero ha hb (Or.inl ha') hp hpnn hdeg

/-- BKS 2016, Theorem 5 for nonpositive coefficients: `p ↦ a p + b X (p - p(X - 1))` with
`a, b ≤ 0` preserves real-rooted polynomials with nonnegative roots and mesh at least one. -/
theorem meshGE_one_add_X_mul_meshDifference_of_nonpos {p : ℝ[X]} {a b : ℝ} (ha : a ≤ 0)
    (hb : b ≤ 0) (hp : p.MeshGE 1) (hpnn : HasOnlyNonnegRoots p) :
    (C a * p + C b * (X * meshDifference 1 1 p)).MeshGE 1 ∧
      HasOnlyNonnegRoots (C a * p + C b * (X * meshDifference 1 1 p)) := by
  obtain ⟨h1, h2⟩ := meshGE_one_add_X_mul_meshDifference (neg_nonneg.mpr ha)
    (neg_nonneg.mpr hb) hp hpnn
  have e : C a * p + C b * (X * meshDifference 1 1 p) =
      C (-1 : ℝ) * (C (-a) * p + C (-b) * (X * meshDifference 1 1 p)) := by
    simp only [map_neg, map_one]
    ring
  rw [e]
  exact ⟨(Polynomial.MeshGE.C_mul_iff _ 1 (by norm_num)).2 h1,
    (HasOnlyNonnegRoots.C_mul_iff (by norm_num) _).2 h2⟩

end

end RealRooted
