module

import RealRooted.HermiteBiehler.Converse.RootGeometry
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots
public import RealRooted.Mesh.Basic
import RealRooted.RootPolynomial
import RealRooted.CommonInterleaver.RootDesc
import RealRooted.PFPolynomial.Closure
public import RealRooted.NarayanaTransformation.RootGeometry
import RealRooted.OrderedRoots
import RealRooted.ObreschkoffConverse.Forward

/-!
# Mesh and finite differences

The root-replacement and Hurwitz-limit proof of the finite-difference theorem
of Brändén, Krasikov, and Shapiro, *Elements of Pólya--Schur theory in finite
difference setting*, Proc. AMS 144 (2016), Theorem 2. See RealRooted issue #2070.
-/

@[expose] public section

open Polynomial

namespace RealRooted

noncomputable section

/-- The BKS one-step finite-difference operator `p(x) - λ p(x - α)`. -/
def meshDifference (α lam : ℝ) (p : ℝ[X]) : ℝ[X] :=
  p - C lam * p.comp (X - C α)

/-- Finite differences commute with translations of the variable. -/
theorem meshDifference_comp_X_add_C (α lam r : ℝ) (p : ℝ[X]) :
    (meshDifference α lam p).comp (X + C r) =
      meshDifference α lam (p.comp (X + C r)) := by
  simp only [meshDifference, sub_comp, mul_comp, C_comp, comp_assoc, add_comp,
    X_comp]
  congr 3
  ring

/-- BKS identity `T(x p) = (x - α)T(p) + α p`. -/
theorem meshDifference_X_mul (α lam : ℝ) (p : ℝ[X]) :
    meshDifference α lam (X * p) =
      (X - C α) * meshDifference α lam p + C α * p := by
  simp only [meshDifference, mul_comp, X_comp]
  ring

/-- Finite differences respect a real linear factor up to the image of its
constant term. -/
theorem meshDifference_X_sub_C_mul (α lam a : ℝ) (p : ℝ[X]) :
    meshDifference α lam ((X - C a) * p) =
      meshDifference α lam (X * p) - C a * meshDifference α lam p := by
  simp only [meshDifference, mul_comp, sub_comp, X_comp, C_comp]
  ring

/-- A finite difference commutes with every real translation, including the
shift used in the mesh criterion. -/
theorem meshDifference_comp_X_sub_C (α lam β : ℝ) (p : ℝ[X]) :
    (meshDifference α lam p).comp (X - C β) =
      meshDifference α lam (p.comp (X - C β)) := by
  simpa [sub_eq_add_neg] using meshDifference_comp_X_add_C α lam (-β) p

/-- Finite differences commute with multiplication by a real scalar. -/
theorem meshDifference_C_mul (α lam c : ℝ) (p : ℝ[X]) :
    meshDifference α lam (C c * p) = C c * meshDifference α lam p := by
  simp only [meshDifference, mul_comp, C_comp]
  ring

private theorem IsUpperHalfPlaneStablePencil.add_real_base_to_direction
    {f g : ℝ[X]} (h : IsUpperHalfPlaneStablePencil f g) (a : ℝ) :
    IsUpperHalfPlaneStablePencil f (g + C a * f) := by
  intro z w hz hw
  let d : ℂ := 1 + (a : ℂ) * w
  have hd : d ≠ 0 := by
    intro hd0
    have him := congrArg Complex.im hd0
    have ha0 : a = 0 := by
      have hmul : a * w.im = 0 := by simpa [d] using him
      exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hw)
    simp [d, ha0] at hd0
  let v : ℂ := w / d
  have hvim : v.im = w.im / Complex.normSq d := by
    dsimp [v]
    rw [Complex.div_im]
    simp [d, Complex.mul_re, Complex.mul_im]
    ring
  have hv : 0 < v.im := by
    rw [hvim]
    exact div_pos hw (Complex.normSq_pos.mpr hd)
  have hne := h z v hz hv
  let F := (complexify f).eval z
  let G := (complexify g).eval z
  change F + v * G ≠ 0 at hne
  have hmap : complexify (g + C a * f) =
      complexify g + C (a : ℂ) * complexify f := by
    simp [complexify]
  rw [hmap, eval_add, eval_mul, eval_C]
  change F + w * (G + (a : ℂ) * F) ≠ 0
  have heq : F + w * (G + (a : ℂ) * F) = d * (F + v * G) := by
    dsimp only [v]
    field_simp [hd]
    dsimp [d]
    ring
  rw [heq]
  exact mul_ne_zero hd hne

private theorem IsUpperHalfPlaneStablePencil.positive_scale_direction
    {f g : ℝ[X]} (h : IsUpperHalfPlaneStablePencil f g)
    {a : ℝ} (ha : 0 < a) :
    IsUpperHalfPlaneStablePencil f (C a * g) := by
  intro z w hz hw
  have hw' : 0 < (w * (a : ℂ)).im := by
    simpa using mul_pos hw ha
  have hne := h z (w * (a : ℂ)) hz hw'
  simpa [complexify, mul_assoc] using hne

private theorem IsUpperHalfPlaneStablePencil.add_real_direction_to_base
    {f g : ℝ[X]} (h : IsUpperHalfPlaneStablePencil f g) (a : ℝ) :
    IsUpperHalfPlaneStablePencil (f + C a * g) g := by
  intro z w hz hw
  have hw' : 0 < ((a : ℂ) + w).im := by simpa using hw
  have hne := h z ((a : ℂ) + w) hz hw'
  simpa [complexify, add_mul, mul_add, add_assoc] using hne

private theorem IsUpperHalfPlaneStablePencil.base_direction_shear
    {f g : ℝ[X]} (h : IsUpperHalfPlaneStablePencil f g)
    {a : ℝ} (ha : 0 < a) :
    IsUpperHalfPlaneStablePencil g (g - C a * f) := by
  simpa [sub_eq_add_neg, add_comm, mul_assoc] using
    (h.swap_neg.positive_scale_direction ha).add_real_base_to_direction 1

private theorem IsUpperHalfPlaneStablePencil.positive_scale_base
    {f g : ℝ[X]} (h : IsUpperHalfPlaneStablePencil f g)
    {a : ℝ} (ha : 0 < a) :
    IsUpperHalfPlaneStablePencil (C a * f) g := by
  intro z w hz hw
  have hw' : 0 < (w / (a : ℂ)).im := by
    simpa using div_pos hw ha
  have hne := h z (w / (a : ℂ)) hz hw'
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hmap : complexify (C a * f) = C (a : ℂ) * complexify f := by
    simp [complexify]
  rw [hmap, eval_mul, eval_C]
  have heq : (a : ℂ) * (complexify f).eval z + w * (complexify g).eval z =
      (a : ℂ) * ((complexify f).eval z + w / (a : ℂ) *
        (complexify g).eval z) := by
    field_simp [ha0]
  rw [heq]
  exact mul_ne_zero ha0 hne

private theorem stablePencil_im_ratio_nonneg
    {f g : ℝ[X]} (hf0 : f ≠ 0) (hfs : f.Splits)
    (h : IsUpperHalfPlaneStablePencil g f)
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ ((complexify g).eval z / (complexify f).eval z).im := by
  let F := (complexify f).eval z
  let G := (complexify g).eval z
  have hF : F ≠ 0 :=
    eval_complexify_ne_zero_of_splits_of_im_pos hfs hf0 hz
  by_contra hnonneg
  have hneg : (G / F).im < 0 := lt_of_not_ge hnonneg
  let w : ℂ := -(G / F)
  have hw : 0 < w.im := by
    dsimp [w]
    linarith
  have hne := h z w hz hw
  change G + w * F ≠ 0 at hne
  apply hne
  dsimp [w]
  field_simp [hF]
  ring

private theorem stablePencil_add_base_of_common_direction
    {f g h : ℝ[X]} (hf0 : f ≠ 0) (hfs : f.Splits)
    (hgf : IsUpperHalfPlaneStablePencil g f)
    (hhf : IsUpperHalfPlaneStablePencil h f) :
    IsUpperHalfPlaneStablePencil (g + h) f := by
  intro z w hz hw
  let F := (complexify f).eval z
  let G := (complexify g).eval z
  let H := (complexify h).eval z
  have hF : F ≠ 0 :=
    eval_complexify_ne_zero_of_splits_of_im_pos hfs hf0 hz
  have hG : 0 ≤ (G / F).im := stablePencil_im_ratio_nonneg hf0 hfs hgf hz
  have hH : 0 ≤ (H / F).im := stablePencil_im_ratio_nonneg hf0 hfs hhf hz
  have hsum : (G + H) / F = G / F + H / F := by ring
  have hmap : complexify (g + h) = complexify g + complexify h := by
    simp [complexify]
  rw [hmap, eval_add]
  change G + H + w * F ≠ 0
  intro hzero
  have hw_eq : w = -((G + H) / F) := by
    rw [← neg_div]
    apply (eq_div_iff hF).2
    linear_combination hzero
  rw [hw_eq, Complex.neg_im, hsum, Complex.add_im] at hw
  linarith

private theorem stablePencil_X_sub_C_mul_self
    {p : ℝ[X]} (hp0 : p ≠ 0) (hps : p.Splits) (α : ℝ) :
    IsUpperHalfPlaneStablePencil ((X - C α) * p) p := by
  intro z w hz hw
  have hP : (complexify p).eval z ≠ 0 :=
    eval_complexify_ne_zero_of_splits_of_im_pos hps hp0 hz
  have hfactor : z - (α : ℂ) + w ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im,
      Complex.zero_im] at him
    linarith
  have hmap : complexify ((X - C α) * p) =
      (X - C (α : ℂ)) * complexify p := by
    simp [complexify]
  rw [hmap, eval_mul, eval_sub, eval_X, eval_C]
  have heq : (z - (α : ℂ)) * (complexify p).eval z +
      w * (complexify p).eval z =
      (z - (α : ℂ) + w) * (complexify p).eval z := by ring
  rw [heq]
  exact mul_ne_zero hfactor hP

private theorem stablePencil_self {p : ℝ[X]} (hp0 : p ≠ 0) (hps : p.Splits) :
    IsUpperHalfPlaneStablePencil p p := by
  intro z w hz hw
  have hP : (complexify p).eval z ≠ 0 :=
    eval_complexify_ne_zero_of_splits_of_im_pos hps hp0 hz
  have hw1 : 1 + w ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.add_im, Complex.one_im, zero_add, Complex.zero_im] at him
    exact (ne_of_gt hw) him
  have heq : (complexify p).eval z + w * (complexify p).eval z =
      (1 + w) * (complexify p).eval z := by ring
  rw [heq]
  exact mul_ne_zero hw1 hP

/-- The local proper-position step behind BKS Theorem 2.  If the difference of
`r` vanishes, the first disjunct uses the paper's zero convention.  Otherwise
the stable pencil records `T(r) ≪ T(Xr)` with its Wronskian orientation. -/
theorem meshDifference_properPosition_X_mul
    {r : ℝ[X]} {α lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hr : r.MeshGE α) :
    meshDifference α lam r = 0 ∨
      IsUpperHalfPlaneStablePencil
        (meshDifference α lam (X * r)) (meshDifference α lam r) := by
  by_cases hr0 : r = 0
  · left
    simp [meshDifference, hr0]
  have hq0 : r.comp (X - C α) ≠ 0 := by
    rw [show X - C α = X + C (-α) by simp [sub_eq_add_neg],
      comp_X_add_C_ne_zero_iff]
    exact hr0
  have hstrict : StrictInterl r (r.comp (X - C α)) :=
    ((Polynomial.MeshGE.iff_interl_comp_sub hα).1 hr).toStrictInterl_of_ne hr0 hq0
  have hTsplit : (meshDifference α lam r).Splits := by
    have hall := allComboRealRooted_of_strictInterl hstrict
    simpa [meshDifference, sub_eq_add_neg] using hall 1 (-lam)
  have hproper : IsUpperHalfPlaneStablePencil (r.comp (X - C α)) r :=
    ((Polynomial.MeshGE.iff_eq_zero_or_stablePencil hα).1 hr).resolve_left hr0
  let t := meshDifference α lam r
  have htr : IsUpperHalfPlaneStablePencil r t := by
    simpa [t, meshDifference] using hproper.base_direction_shear hlam
  by_cases ht0 : t = 0
  · exact Or.inl ht0
  right
  have hlinear : IsUpperHalfPlaneStablePencil ((X - C α) * t) t :=
    stablePencil_X_sub_C_mul_self ht0 hTsplit α
  have hscaled : IsUpperHalfPlaneStablePencil (C α * r) t :=
    htr.positive_scale_base hα
  have hsum := stablePencil_add_base_of_common_direction
    ht0 hTsplit hlinear hscaled
  simpa [t, meshDifference_X_mul] using hsum

/-- The one-root replacement step (BKS equation (5)): moving a single root to
the right preserves the proper-position orientation after applying `T`.
The zero alternative is needed when the transformed first polynomial cancels. -/
theorem meshDifference_properPosition_root_move
    {r : ℝ[X]} {α lam a b : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hr : r.MeshGE α) (hab : a ≤ b) :
    meshDifference α lam ((X - C a) * r) = 0 ∨
      IsUpperHalfPlaneStablePencil
        (meshDifference α lam ((X - C b) * r))
        (meshDifference α lam ((X - C a) * r)) := by
  let t := meshDifference α lam r
  let u := meshDifference α lam (X * r)
  have hform (c : ℝ) :
      meshDifference α lam ((X - C c) * r) = u - C c * t := by
    exact meshDifference_X_sub_C_mul α lam c r
  rcases meshDifference_properPosition_X_mul hα hlam hr with ht0 | hproper
  · have hu : u = C α * r := by
      dsimp only [u]
      rw [meshDifference_X_mul, ht0]
      ring
    have ht : t = 0 := ht0
    have hsame (c : ℝ) :
        meshDifference α lam ((X - C c) * r) = C α * r := by
      rw [hform, ht, mul_zero, sub_zero, hu]
    rw [hsame a, hsame b]
    by_cases hr0 : r = 0
    · exact Or.inl (by simp [hr0])
    · right
      have hnonzero : C α * r ≠ 0 :=
        mul_ne_zero (C_ne_zero.mpr hα.ne') hr0
      exact stablePencil_self hnonzero (hr.1.C_mul α)
  have hbase : IsUpperHalfPlaneStablePencil (u - C b * t) t := by
    simpa [u, t, sub_eq_add_neg] using
      hproper.add_real_direction_to_base (-b)
  by_cases heq : a = b
  · subst b
    rw [hform a]
    rcases hbase.hermiteBiehler.left_eq_zero_or_splits with hzero | hsplit
    · exact Or.inl hzero
    · by_cases hzero : u - C a * t = 0
      · exact Or.inl hzero
      · exact Or.inr (stablePencil_self hzero hsplit)
  have hlt : a < b := lt_of_le_of_ne hab heq
  have hscaled : IsUpperHalfPlaneStablePencil
      (u - C b * t) (C (b - a) * t) :=
    hbase.positive_scale_direction (sub_pos.mpr hlt)
  have hshear := hscaled.add_real_base_to_direction 1
  have hrew : C (b - a) * t + (u - C b * t) = u - C a * t := by
    rw [map_sub]
    ring
  right
  rw [hform a, hform b]
  simpa only [C_1, one_mul, hrew] using hshear

/-- A finite difference with positive step and positive weight is real-rooted on
the mesh cone.  This is the real-rootedness part of BKS Theorem 2. -/
theorem meshDifference_splits {p : ℝ[X]} {α lam : ℝ}
    (hα : 0 < α) (hp : p.MeshGE α) :
    (meshDifference α lam p).Splits := by
  by_cases hp0 : p = 0
  · simp [meshDifference, hp0]
  have hq0 : p.comp (X - C α) ≠ 0 := by
    rw [show X - C α = X + C (-α) by simp [sub_eq_add_neg],
      comp_X_add_C_ne_zero_iff]
    exact hp0
  have hstrict : StrictInterl p (p.comp (X - C α)) :=
    ((Polynomial.MeshGE.iff_interl_comp_sub hα).1 hp).toStrictInterl_of_ne hp0 hq0
  have hall := allComboRealRooted_of_strictInterl hstrict
  simpa [meshDifference, sub_eq_add_neg] using hall 1 (-lam)

/-- Away from the cancelling weight `λ = 1`, the finite difference has exactly
the degree of its input. -/
theorem meshDifference_natDegree_of_ne_one (p : ℝ[X]) (α lam : ℝ)
    (hlam : lam ≠ 1) : (meshDifference α lam p).natDegree = p.natDegree := by
  by_cases hp0 : p = 0
  · simp [meshDifference, hp0]
  let q := p.comp (X - C α)
  have hqdeg : q.natDegree = p.natDegree := by
    dsimp [q]
    rw [natDegree_comp_eq_of_mul_ne_zero (by simp [hp0])]
    simp
  have hqlead : q.leadingCoeff = p.leadingCoeff := by
    dsimp [q]
    rw [leadingCoeff_comp (by simp), leadingCoeff_X_sub_C, one_pow, mul_one]
  have hcoeff : (meshDifference α lam p).coeff p.natDegree =
      (1 - lam) * p.leadingCoeff := by
    have hqcoeff : q.coeff p.natDegree = p.leadingCoeff := by
      rw [← hqdeg, coeff_natDegree, hqlead]
    simp only [meshDifference, coeff_sub, coeff_C_mul]
    change p.coeff p.natDegree - lam * q.coeff p.natDegree = _
    rw [coeff_natDegree, hqcoeff]
    ring
  have hcoeff0 : (meshDifference α lam p).coeff p.natDegree ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hlam))
      (leadingCoeff_ne_zero.mpr hp0)
  apply le_antisymm
  · exact (natDegree_sub_le _ _).trans (max_le le_rfl (by
      simpa [q, hqdeg] using natDegree_C_mul_le lam q))
  · exact le_natDegree_of_ne_zero hcoeff0

/-- The finite difference never raises degree, including at `λ = 1`. -/
theorem meshDifference_natDegree_le (p : ℝ[X]) (α lam : ℝ) :
    (meshDifference α lam p).natDegree ≤ p.natDegree := by
  by_cases hp0 : p = 0
  · simp [meshDifference, hp0]
  have hcomp : (p.comp (X - C α)).natDegree = p.natDegree := by
    rw [natDegree_comp_eq_of_mul_ne_zero (by simp [hp0])]
    simp
  exact (natDegree_sub_le _ _).trans
    (max_le le_rfl ((natDegree_C_mul_le lam _).trans hcomp.le))

/-- The leading coefficient of a non-cancelling finite difference is scaled by
`1 - λ`. -/
theorem meshDifference_leadingCoeff_of_ne_one (p : ℝ[X]) (α lam : ℝ)
    (hlam : lam ≠ 1) :
    (meshDifference α lam p).leadingCoeff = (1 - lam) * p.leadingCoeff := by
  by_cases hp0 : p = 0
  · simp [meshDifference, hp0]
  let q := p.comp (X - C α)
  have hqdeg : q.natDegree = p.natDegree := by
    dsimp [q]
    rw [natDegree_comp_eq_of_mul_ne_zero (by simp [hp0])]
    simp
  have hqlead : q.leadingCoeff = p.leadingCoeff := by
    dsimp [q]
    rw [leadingCoeff_comp (by simp), leadingCoeff_X_sub_C, one_pow, mul_one]
  change (meshDifference α lam p).coeff (meshDifference α lam p).natDegree = _
  rw [meshDifference_natDegree_of_ne_one p α lam hlam]
  have hqcoeff : q.coeff p.natDegree = p.leadingCoeff := by
    rw [← hqdeg, coeff_natDegree, hqlead]
  simp only [meshDifference, coeff_sub, coeff_C_mul]
  change p.coeff p.natDegree - lam * q.coeff p.natDegree = _
  rw [coeff_natDegree, hqcoeff]
  ring

private theorem strictInterl_of_stable_same_degree_lc {f g : ℝ[X]}
    (hdeg : f.natDegree = g.natDegree) (hn : 0 < f.natDegree)
    (hlc : f.leadingCoeff = g.leadingCoeff) (hlc0 : f.leadingCoeff ≠ 0)
    (hstable : IsUpperHalfPlaneStablePencil g f) : StrictInterl f g := by
  rcases lt_or_gt_of_ne hlc0 with hneg | hpos
  · have hfpos : HasPosLeadingCoeff (-f) := by
      simpa [HasPosLeadingCoeff] using neg_pos.mpr hneg
    have hgpos : HasPosLeadingCoeff (-g) := by
      simpa [HasPosLeadingCoeff, ← hlc] using neg_pos.mpr hneg
    have hgdeg : (-g).natDegree ≠ 0 := by simpa [← hdeg] using hn.ne'
    have hstrict : StrictInterl (-f) (-g) :=
      (isUpperHalfPlaneStablePencil_iff_strictInterl hgpos hfpos hgdeg).1
        hstable.neg_neg
    have hleft := hstrict.C_mul_left (a := -1) (by norm_num)
    have hboth := hleft.C_mul_right (a := -1) (by norm_num)
    simpa using hboth
  · have hfpos : HasPosLeadingCoeff f := hpos
    have hgpos : HasPosLeadingCoeff g := by simpa [HasPosLeadingCoeff, ← hlc] using hpos
    have hgdeg : g.natDegree ≠ 0 := by lia
    exact (isUpperHalfPlaneStablePencil_iff_strictInterl hgpos hfpos hgdeg).1 hstable

private theorem meshGE_rootPolynomial_of_chain (rs : List ℝ) {α : ℝ}
    (hα : 0 ≤ α) (hgap : rs.IsChain (fun a b : ℝ => a + α ≤ b)) :
    (rootPolynomial (rs : Multiset ℝ)).MeshGE α := by
  have htrans : Trans (fun a b : ℝ => a + α ≤ b)
      (fun a b : ℝ => a + α ≤ b) (fun a b : ℝ => a + α ≤ b) :=
    ⟨by intro a b c hab hbc; linarith⟩
  have hpair : rs.Pairwise (fun a b : ℝ => a + α ≤ b) :=
    @List.IsChain.pairwise ℝ (fun a b : ℝ => a + α ≤ b) rs htrans hgap
  have hsorted : rs.Pairwise (· ≤ ·) :=
    hpair.imp (by intro a b hab; linarith)
  have hsort : (rootPolynomial (rs : Multiset ℝ)).roots.sort (· ≤ ·) = rs := by
    rw [roots_rootPolynomial]
    apply List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) hsorted
    exact Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _)
  refine ⟨rootPolynomial_splits _, hα, ?_⟩
  intro i hi
  rw [hsort] at hi ⊢
  have hstep := List.isChain_iff_getElem.mp hgap i hi
  simpa [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by lia : i < rs.length),
    List.getElem?_eq_getElem hi, Option.getD_some] using hstep

private theorem meshGE_roots_chain {p : ℝ[X]} {β : ℝ} (hp : p.MeshGE β) :
    (p.roots.sort (· ≤ ·)).IsChain (fun a b : ℝ => a + β ≤ b) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hgap := hp.2.2 i hi
  simpa [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by lia : i < (p.roots.sort (· ≤ ·)).length),
    List.getElem?_eq_getElem hi, Option.getD_some] using hgap

private theorem meshGE_left_cofactor (rs : List ℝ) {α β : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hgap : rs.IsChain (fun a b : ℝ => a + β ≤ b)) (k : ℕ) :
    (rootPolynomial
      (((rs.take k).map (· + β) ++ rs.drop (k + 1)) : Multiset ℝ)).MeshGE α := by
  have hleft : ((rs.take k).map (· + β)).IsChain
      (fun a b : ℝ => a + α ≤ b) := by
    rw [List.isChain_map]
    exact (hgap.take k).imp (by intro a b hab; linarith)
  have hright : (rs.drop (k + 1)).IsChain (fun a b : ℝ => a + α ≤ b) :=
    (hgap.drop (k + 1)).imp (by intro a b hab; linarith)
  apply meshGE_rootPolynomial_of_chain _ hα
  apply hleft.append hright
  intro x hx y hy
  by_cases hk : k = 0
  · simp [hk] at hx
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  by_cases hlast : k + 1 < rs.length
  · have hkprev : k - 1 < rs.length := by lia
    have htake : rs.take k = rs.take (k - 1) ++ [rs[k - 1]] := by
      simp [Nat.sub_add_cancel hkpos]
    have hlast_take : (rs.take k).getLast? = some rs[k - 1] := by
      rw [htake, List.getLast?_append]
      simp
    rw [List.getLast?_map, hlast_take] at hx
    simp [List.head?_drop, List.getElem?_eq_getElem hlast] at hy
    have hxeq : rs[k - 1] + β = x := by simpa using hx
    subst x
    subst y
    have hgap1 := List.isChain_iff_getElem.mp hgap (k - 1) (by lia)
    have hgap2 := List.isChain_iff_getElem.mp hgap k hlast
    simp only [Nat.sub_add_cancel hkpos] at hgap1
    linarith
  · have hdrop : rs.drop (k + 1) = [] := List.drop_eq_nil_of_le (by lia)
    simp [hdrop] at hy

private theorem meshGE_right_cofactor (rs : List ℝ) {α β : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hgap : rs.IsChain (fun a b : ℝ => a + β ≤ b)) (k : ℕ) :
    (rootPolynomial
      (((rs.drop 1).take k ++ (rs.drop (k + 1)).map (· + β)) : Multiset ℝ)).MeshGE α := by
  have hleft : ((rs.drop 1).take k).IsChain (fun a b : ℝ => a + α ≤ b) :=
    ((hgap.drop 1).take k).imp (by intro a b hab; linarith)
  have hright : ((rs.drop (k + 1)).map (· + β)).IsChain
      (fun a b : ℝ => a + α ≤ b) := by
    rw [List.isChain_map]
    exact (hgap.drop (k + 1)).imp (by intro a b hab; linarith)
  apply meshGE_rootPolynomial_of_chain _ hα
  apply hleft.append hright
  intro x hx y hy
  by_cases hk : k = 0
  · simp [hk] at hx
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  by_cases hlast : k + 1 < rs.length
  · have hkprev : k - 1 < (rs.drop 1).length := by simp; lia
    have htake : (rs.drop 1).take k =
        (rs.drop 1).take (k - 1) ++ [rs[k]] := by
      simpa [Nat.sub_add_cancel hkpos] using
        (List.take_concat_get' (rs.drop 1) (k - 1) hkprev).symm
    have hlast_take : ((rs.drop 1).take k).getLast? = some rs[k] := by
      rw [htake, List.getLast?_append]
      simp
    rw [hlast_take] at hx
    simp [List.head?_drop, List.getElem?_eq_getElem hlast] at hy
    have hxeq : rs[k] = x := by simpa using hx
    subst x
    subst y
    have hstep := List.isChain_iff_getElem.mp hgap k hlast
    linarith
  · have hdrop : rs.drop (k + 1) = [] := List.drop_eq_nil_of_le (by lia)
    simp [hdrop] at hy

private theorem rootPolynomial_insert (u v : List ℝ) (a : ℝ) :
    rootPolynomial ((u ++ a :: v : List ℝ) : Multiset ℝ) =
      (X - C a) * rootPolynomial ((u ++ v : List ℝ) : Multiset ℝ) := by
  simp only [rootPolynomial_coe, List.map_append, List.map_cons,
    List.prod_append, List.prod_cons]
  ring

private theorem rootPolynomial_comp_X_sub_C (rs : List ℝ) (β : ℝ) :
    (rootPolynomial (rs : Multiset ℝ)).comp (X - C β) =
      rootPolynomial ((rs.map (· + β)) : Multiset ℝ) := by
  simp only [rootPolynomial, multiset_prod_comp, Multiset.map_map]
  congr 1
  conv_rhs => rw [← Multiset.map_coe, Multiset.map_map]
  change (rs : Multiset ℝ).map (fun r => (X - C r).comp (X - C β)) =
    (rs : Multiset ℝ).map (fun r => X - C (r + β))
  congr 1
  funext r
  simp only [sub_comp, X_comp, C_comp, map_add]
  abel

private def leftRootChain (rs : List ℝ) (β : ℝ) (k : ℕ) : ℝ[X] :=
  rootPolynomial (((rs.take k).map (· + β) ++ rs.drop k) : Multiset ℝ)

private def rightRootChain (rs : List ℝ) (β : ℝ) (k : ℕ) : ℝ[X] :=
  rootPolynomial (((rs.drop 1).take k ++ (rs.drop k).map (· + β)) : Multiset ℝ)

private theorem leftRootChain_natDegree (rs : List ℝ) (β : ℝ) {k : ℕ}
    (hk : k ≤ rs.length) : (leftRootChain rs β k).natDegree = rs.length := by
  simp [leftRootChain, List.length_take, List.length_drop, Nat.min_eq_left hk]
  lia

private theorem rightRootChain_natDegree (rs : List ℝ) (β : ℝ) {k : ℕ}
    (hk : k + 1 ≤ rs.length) : (rightRootChain rs β k).natDegree = rs.length := by
  simp [rightRootChain, List.length_take, List.length_drop]
  lia

private theorem leftRootChain_monic (rs : List ℝ) (β : ℝ) (k : ℕ) :
    (leftRootChain rs β k).Monic := rootPolynomial_monic _

private theorem rightRootChain_monic (rs : List ℝ) (β : ℝ) (k : ℕ) :
    (rightRootChain rs β k).Monic := rootPolynomial_monic _

private theorem leftRootChain_last_eq_rightRootChain_zero (rs : List ℝ) (β : ℝ) :
    leftRootChain rs β rs.length = rightRootChain rs β 0 := by
  simp [leftRootChain, rightRootChain]

private def rootReplacementChain (rs : List ℝ) (β : ℝ) (k : ℕ) : ℝ[X] :=
  if k < rs.length then leftRootChain rs β k
  else rightRootChain rs β (k - rs.length)

private theorem rootReplacementChain_monic (rs : List ℝ) (β : ℝ) (k : ℕ) :
    (rootReplacementChain rs β k).Monic := by
  unfold rootReplacementChain
  split_ifs <;> exact rootPolynomial_monic _

private theorem rootReplacementChain_natDegree (rs : List ℝ) (β : ℝ)
    {k : ℕ} (hk : k < 2 * rs.length) :
    (rootReplacementChain rs β k).natDegree = rs.length := by
  unfold rootReplacementChain
  split_ifs with hleft
  · exact leftRootChain_natDegree rs β hleft.le
  · exact rightRootChain_natDegree rs β (by lia)

private theorem leftRootChain_factor (rs : List ℝ) (β : ℝ) {k : ℕ}
    (hk : k < rs.length) :
    leftRootChain rs β k =
      (X - C rs[k]) *
        rootPolynomial
          (((rs.take k).map (· + β) ++ rs.drop (k + 1)) : Multiset ℝ) := by
  unfold leftRootChain
  rw [← List.cons_getElem_drop_succ (h := hk)]
  exact rootPolynomial_insert _ _ _

private theorem leftRootChain_succ_factor (rs : List ℝ) (β : ℝ) {k : ℕ}
    (hk : k < rs.length) :
    leftRootChain rs β (k + 1) =
      (X - C (rs[k] + β)) *
        rootPolynomial
          (((rs.take k).map (· + β) ++ rs.drop (k + 1)) : Multiset ℝ) := by
  unfold leftRootChain
  rw [← List.take_concat_get' rs k hk, List.map_append]
  simp only [List.map_singleton]
  rw [List.append_assoc, List.singleton_append]
  exact rootPolynomial_insert _ _ _

private theorem rightRootChain_factor (rs : List ℝ) (β : ℝ) {k : ℕ}
    (hk : k + 1 < rs.length) :
    rightRootChain rs β k =
      (X - C (rs[k] + β)) *
        rootPolynomial
          (((rs.drop 1).take k ++ (rs.drop (k + 1)).map (· + β)) : Multiset ℝ) := by
  unfold rightRootChain
  have hk0 : k < rs.length := by lia
  rw [← List.cons_getElem_drop_succ (h := hk0), List.map_cons]
  exact rootPolynomial_insert _ _ _

private theorem rightRootChain_succ_factor (rs : List ℝ) (β : ℝ) {k : ℕ}
    (hk : k + 1 < rs.length) :
    rightRootChain rs β (k + 1) =
      (X - C rs[k + 1]) *
        rootPolynomial
          (((rs.drop 1).take k ++ (rs.drop (k + 1)).map (· + β)) : Multiset ℝ) := by
  unfold rightRootChain
  have hk' : k < (rs.drop 1).length := by simp; lia
  rw [← List.take_concat_get' (rs.drop 1) k hk']
  simp only [List.getElem_drop, Nat.add_comm]
  rw [List.append_assoc, List.singleton_append]
  exact rootPolynomial_insert _ _ _

private theorem meshDifference_leftRootChain_step (rs : List ℝ) {α β lam : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hlam : 0 < lam)
    (hgap : rs.IsChain (fun a b : ℝ => a + β ≤ b)) {k : ℕ}
    (hk : k < rs.length) :
    meshDifference α lam (leftRootChain rs β k) = 0 ∨
      IsUpperHalfPlaneStablePencil
        (meshDifference α lam (leftRootChain rs β (k + 1)))
        (meshDifference α lam (leftRootChain rs β k)) := by
  rw [leftRootChain_factor rs β hk, leftRootChain_succ_factor rs β hk]
  exact meshDifference_properPosition_root_move hα hlam
    (meshGE_left_cofactor rs hα.le hαβ hgap k) (by linarith)

private theorem meshDifference_rightRootChain_step (rs : List ℝ) {α β lam : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hlam : 0 < lam)
    (hgap : rs.IsChain (fun a b : ℝ => a + β ≤ b)) {k : ℕ}
    (hk : k + 1 < rs.length) :
    meshDifference α lam (rightRootChain rs β k) = 0 ∨
      IsUpperHalfPlaneStablePencil
        (meshDifference α lam (rightRootChain rs β (k + 1)))
        (meshDifference α lam (rightRootChain rs β k)) := by
  rw [rightRootChain_factor rs β hk, rightRootChain_succ_factor rs β hk]
  have hab : rs[k] + β ≤ rs[k + 1] :=
    List.isChain_iff_getElem.mp hgap k hk
  exact meshDifference_properPosition_root_move hα hlam
    (meshGE_right_cofactor rs hα.le hαβ hgap k) hab

private theorem meshDifference_rootChain_endpoint (rs : List ℝ) {α β lam : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hlam : 0 < lam)
    (hgap : rs.IsChain (fun a b : ℝ => a + β ≤ b))
    (hn : 0 < rs.length) :
    meshDifference α lam (leftRootChain rs β 0) = 0 ∨
      IsUpperHalfPlaneStablePencil
        (meshDifference α lam (rightRootChain rs β (rs.length - 1)))
        (meshDifference α lam (leftRootChain rs β 0)) := by
  have hfirst : rs = rs[0] :: rs.drop 1 :=
    (List.cons_getElem_drop_succ (h := hn)).symm
  have hlast : rs.drop (rs.length - 1) = [rs[rs.length - 1]] := by
    simpa only [List.getLast_eq_getElem] using
      List.drop_length_sub_one (List.ne_nil_of_length_pos hn)
  have htake : (rs.drop 1).take (rs.length - 1) = rs.drop 1 := by
    apply List.take_of_length_le
    simp
  have hleft : leftRootChain rs β 0 =
      (X - C rs[0]) * rootPolynomial (rs.drop 1 : Multiset ℝ) := by
    simp only [leftRootChain, List.take_zero, List.map_nil, List.nil_append,
      List.drop_zero]
    calc
      rootPolynomial (rs : Multiset ℝ) =
          rootPolynomial ((rs[0] :: rs.drop 1 : List ℝ) : Multiset ℝ) :=
        congrArg (fun s : List ℝ => rootPolynomial (s : Multiset ℝ)) hfirst
      _ = (X - C rs[0]) * rootPolynomial (rs.drop 1 : Multiset ℝ) := by
        simpa using rootPolynomial_insert ([] : List ℝ) (rs.drop 1) rs[0]
  have hright : rightRootChain rs β (rs.length - 1) =
      (X - C (rs[rs.length - 1] + β)) *
        rootPolynomial (rs.drop 1 : Multiset ℝ) := by
    simp only [rightRootChain, htake, hlast, List.map_singleton]
    simpa [List.append_assoc] using
      rootPolynomial_insert (rs.drop 1) ([] : List ℝ) (rs[rs.length - 1] + β)
  have hordered : rs.Pairwise (· ≤ ·) :=
    List.isChain_iff_pairwise.mp (hgap.imp (by intro a b hab; linarith))
  have hmono : rs[0] ≤ rs[rs.length - 1] := by
    by_cases hone : rs.length = 1
    · simp [hone]
    · exact hordered.rel_get_of_le (a := ⟨0, hn⟩)
        (b := ⟨rs.length - 1, by lia⟩) (by simp)
  rw [hleft, hright]
  exact meshDifference_properPosition_root_move hα hlam
    (meshGE_rootPolynomial_of_chain _ hα.le
      ((hgap.drop 1).imp (by intro a b hab; linarith)))
    (by linarith)

private theorem meshDifference_rootReplacementChain_step (rs : List ℝ) {α β lam : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hlam : 0 < lam)
    (hgap : rs.IsChain (fun a b : ℝ => a + β ≤ b))
    {k : ℕ} (hk : k < 2 * rs.length - 1) :
    meshDifference α lam (rootReplacementChain rs β k) = 0 ∨
      IsUpperHalfPlaneStablePencil
        (meshDifference α lam (rootReplacementChain rs β (k + 1)))
        (meshDifference α lam (rootReplacementChain rs β k)) := by
  by_cases hleft : k + 1 < rs.length
  · have hk0 : k < rs.length := by lia
    simpa [rootReplacementChain, hk0, hleft] using
      meshDifference_leftRootChain_step rs hα hαβ hlam hgap hk0
  by_cases hboundary : k + 1 = rs.length
  · have hk0 : k < rs.length := by lia
    have hk1 : ¬k + 1 < rs.length := by lia
    have hstep := meshDifference_leftRootChain_step rs hα hαβ hlam hgap hk0
    rw [hboundary, leftRootChain_last_eq_rightRootChain_zero] at hstep
    simpa [rootReplacementChain, hk0, hk1, hboundary] using hstep
  · have hk0 : ¬k < rs.length := by lia
    have hk1 : ¬k + 1 < rs.length := by lia
    have hidx : (k + 1) - rs.length = k - rs.length + 1 := by lia
    have hqstep := meshDifference_rightRootChain_step rs hα hαβ hlam hgap
      (k := k - rs.length) (by lia)
    simpa [rootReplacementChain, hk0, hk1, hidx] using hqstep

private theorem meshDifference_rootReplacementChain_endpoint (rs : List ℝ)
    {α β lam : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hlam : 0 < lam)
    (hgap : rs.IsChain (fun a b : ℝ => a + β ≤ b))
    (hn : 0 < rs.length) :
    meshDifference α lam (rootReplacementChain rs β 0) = 0 ∨
      IsUpperHalfPlaneStablePencil
        (meshDifference α lam (rootReplacementChain rs β (2 * rs.length - 1)))
        (meshDifference α lam (rootReplacementChain rs β 0)) := by
  have hlast : ¬2 * rs.length - 1 < rs.length := by lia
  have hidx : 2 * rs.length - 1 - rs.length = rs.length - 1 := by lia
  simpa [rootReplacementChain, hn, hlast, hidx] using
    meshDifference_rootChain_endpoint rs hα hαβ hlam hgap hn

private theorem meshDifference_rootReplacementChain_leadingCoeff (rs : List ℝ)
    (β α lam : ℝ) (hlam : lam ≠ 1) (k : ℕ) :
    (meshDifference α lam (rootReplacementChain rs β k)).leadingCoeff = 1 - lam := by
  rw [meshDifference_leadingCoeff_of_ne_one _ _ _ hlam,
    (rootReplacementChain_monic rs β k).leadingCoeff, mul_one]

private theorem meshDifference_rootReplacementChain_strict_of_stable
    (rs : List ℝ) (β α lam : ℝ) (hlam : lam ≠ 1)
    {i j : ℕ} (hi : i < 2 * rs.length) (hj : j < 2 * rs.length)
    (hn : 0 < rs.length)
    (hstable : IsUpperHalfPlaneStablePencil
      (meshDifference α lam (rootReplacementChain rs β j))
      (meshDifference α lam (rootReplacementChain rs β i))) :
    StrictInterl (meshDifference α lam (rootReplacementChain rs β i))
      (meshDifference α lam (rootReplacementChain rs β j)) := by
  have hdeg {k : ℕ} (hk : k < 2 * rs.length) :
      (meshDifference α lam (rootReplacementChain rs β k)).natDegree = rs.length := by
    rw [meshDifference_natDegree_of_ne_one _ _ _ hlam,
      rootReplacementChain_natDegree rs β hk]
  have hlci := meshDifference_rootReplacementChain_leadingCoeff rs β α lam hlam i
  have hlcj := meshDifference_rootReplacementChain_leadingCoeff rs β α lam hlam j
  apply strictInterl_of_stable_same_degree_lc
    (by rw [hdeg hi, hdeg hj]) (by rw [hdeg hi]; exact hn)
    (by rw [hlci, hlcj]) (by rw [hlci]; exact sub_ne_zero.mpr (Ne.symm hlam))
    hstable

private theorem meshDifference_rootReplacementChain_nonzero
    (rs : List ℝ) (β α lam : ℝ) (hlam : lam ≠ 1) (k : ℕ) :
    meshDifference α lam (rootReplacementChain rs β k) ≠ 0 := by
  rw [← leadingCoeff_ne_zero,
    meshDifference_rootReplacementChain_leadingCoeff rs β α lam hlam k]
  exact sub_ne_zero.mpr (Ne.symm hlam)

private theorem meshDifference_rootReplacementChain_interl (rs : List ℝ)
    {α β lam : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hlam : 0 < lam)
    (hlam1 : lam ≠ 1) (hgap : rs.IsChain (fun a b : ℝ => a + β ≤ b))
    (hn : 0 < rs.length) :
    StrictInterl
      (meshDifference α lam (rootReplacementChain rs β 0))
      (meshDifference α lam (rootReplacementChain rs β rs.length)) := by
  let F : ℕ → ℝ[X] := fun k => meshDifference α lam (rootReplacementChain rs β k)
  have hcons : ∀ k, 0 ≤ k → k < 2 * rs.length - 1 →
      StrictInterl (F k) (F (k + 1)) := by
    intro k _ hk
    have hstep := meshDifference_rootReplacementChain_step rs hα hαβ hlam hgap hk
    rcases hstep with hzero | hstable
    · exact False.elim (meshDifference_rootReplacementChain_nonzero rs β α lam
        hlam1 k hzero)
    · exact meshDifference_rootReplacementChain_strict_of_stable rs β α lam
        hlam1 (by lia) (by lia) hn hstable
  have hstep := meshDifference_rootReplacementChain_endpoint rs hα hαβ hlam hgap hn
  have hext : StrictInterl (F 0) (F (2 * rs.length - 1)) := by
    rcases hstep with hzero | hstable
    · exact False.elim (meshDifference_rootReplacementChain_nonzero rs β α lam
        hlam1 0 hzero)
    · exact meshDifference_rootReplacementChain_strict_of_stable rs β α lam
        hlam1 (by lia) (by lia) hn hstable
  exact strictInterl_chain_of_consecutive_of_endpoint F 0 (2 * rs.length - 1)
    hcons hext 0 rs.length (by lia) (by lia) (by lia)

private theorem meshDifference_rootPolynomial_meshGE (rs : List ℝ)
    {α β lam : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hlam : 0 < lam)
    (hlam1 : lam ≠ 1) (hgap : rs.IsChain (fun a b : ℝ => a + β ≤ b))
    (hn : 0 < rs.length) :
    (meshDifference α lam (rootPolynomial (rs : Multiset ℝ))).MeshGE β := by
  have hfirst : rootReplacementChain rs β 0 = rootPolynomial (rs : Multiset ℝ) := by
    simp [rootReplacementChain, leftRootChain, hn]
  have hlast : rootReplacementChain rs β rs.length =
      (rootPolynomial (rs : Multiset ℝ)).comp (X - C β) := by
    simp [rootReplacementChain, rightRootChain, rootPolynomial_comp_X_sub_C]
  have hstrict : StrictInterl
      (meshDifference α lam (rootPolynomial (rs : Multiset ℝ)))
      (meshDifference α lam
        ((rootPolynomial (rs : Multiset ℝ)).comp (X - C β))) := by
    simpa only [hfirst, hlast] using
      meshDifference_rootReplacementChain_interl rs hα hαβ hlam hlam1 hgap hn
  rw [Polynomial.MeshGE.iff_interl_comp_sub (lt_of_lt_of_le hα hαβ)]
  rw [meshDifference_comp_X_sub_C]
  exact hstrict.toInterl

/-- BKS Theorem 2 away from the degree-drop weight.  Every mesh bound at least
the step size survives the positive finite-difference operator. -/
theorem meshDifference_meshGE_of_ne_one {p : ℝ[X]} {α β lam : ℝ}
    (hα : 0 < α) (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hp : p.MeshGE β) (hαβ : α ≤ β) :
    (meshDifference α lam p).MeshGE β := by
  by_cases hp0 : p = 0
  · subst p
    exact Polynomial.MeshGE.of_natDegree_le_one (by simp [meshDifference])
      (by simp [meshDifference]) (by linarith)
  let rs := p.roots.sort (· ≤ ·)
  have hroots : (rs : Multiset ℝ) = p.roots := Multiset.sort_eq _ _
  have hfac : p = C p.leadingCoeff * rootPolynomial (rs : Multiset ℝ) := by
    conv_lhs => rw [hp.1.eq_prod_roots]
    simp only [rootPolynomial, hroots]
  have hlc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  by_cases hnil : rs = []
  · have hpdeg : p.natDegree = 0 := by
      rw [← Polynomial.splits_iff_card_roots.mp hp.1]
      simp [← hroots, hnil]
    have hTd : (meshDifference α lam p).natDegree = 0 := by
      rw [meshDifference_natDegree_of_ne_one p α lam hlam1, hpdeg]
    exact Polynomial.MeshGE.of_natDegree_le_one
      (meshDifference_splits hα (hp.antitone hα.le hαβ)) (by lia) (by linarith)
  have hn : 0 < rs.length := List.length_pos_iff_ne_nil.mpr hnil
  have hmono : (meshDifference α lam (rootPolynomial (rs : Multiset ℝ))).MeshGE β :=
    meshDifference_rootPolynomial_meshGE rs hα hαβ hlam hlam1
      (meshGE_roots_chain hp) hn
  rw [hfac, meshDifference_C_mul]
  exact (Polynomial.MeshGE.C_mul_iff _ _ hlc0).2 hmono

private theorem complex_pencil_ne_zero {f g : ℝ[X]} (hf : f ≠ 0)
    {w : ℂ} (hw : 0 < w.im) :
    complexify g + C w * complexify f ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun P : ℂ[X] => P.coeff f.natDegree) hzero
  simp only [coeff_add, coeff_C_mul, coeff_zero] at hcoeff
  have hcoe : (g.coeff f.natDegree : ℂ) +
      w * (f.leadingCoeff : ℂ) = 0 := by
    simpa [complexify, coeff_natDegree] using hcoeff
  have him := congrArg Complex.im hcoe
  have hmul : w.im * f.leadingCoeff = 0 := by
    simpa [Complex.add_im, Complex.mul_im] using him
  have hlead : f.leadingCoeff = 0 := (mul_eq_zero.mp hmul).resolve_left hw.ne'
  exact (leadingCoeff_ne_zero.mpr hf) hlead

/-- A bounded-degree evaluation limit of stable pencils with nonzero direction is a stable
pencil (Hurwitz). -/
theorem IsUpperHalfPlaneStablePencil.of_tendsto_eval_of_natDegree_le
    {f g : ℕ → ℝ[X]} {f₀ g₀ : ℝ[X]} {N : ℕ}
    (hstable : ∀ k, IsUpperHalfPlaneStablePencil (f k) (g k))
    (hfdeg : ∀ k, (f k).natDegree ≤ N)
    (hgdeg : ∀ k, (g k).natDegree ≤ N)
    (hfeval : ∀ z : ℂ, Filter.Tendsto
      (fun k => (complexify (f k)).eval z) Filter.atTop
        (nhds ((complexify f₀).eval z)))
    (hgeval : ∀ z : ℂ, Filter.Tendsto
      (fun k => (complexify (g k)).eval z) Filter.atTop
        (nhds ((complexify g₀).eval z)))
    (hg₀ : g₀ ≠ 0) : IsUpperHalfPlaneStablePencil f₀ g₀ := by
  intro z w hz hw
  let H : ℕ → ℂ[X] := fun k => complexify (f k) + C w * complexify (g k)
  let H₀ : ℂ[X] := complexify f₀ + C w * complexify g₀
  have hH₀ : H₀ ≠ 0 := complex_pencil_ne_zero hg₀ hw
  have hHdeg (k : ℕ) : (H k).natDegree ≤ N := by
    have hf : (complexify (f k)).natDegree ≤ N :=
      Polynomial.natDegree_map_le.trans (hfdeg k)
    have hg : (complexify (g k)).natDegree ≤ N :=
      Polynomial.natDegree_map_le.trans (hgdeg k)
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le hf ((Polynomial.natDegree_C_mul_le w _).trans hg))
  have hHstable (k : ℕ) : IsUpperHalfPlaneStable (H k) := by
    intro u hu
    simpa [H, eval_add, eval_mul, eval_C] using hstable k u w hu hw
  have hHeval (u : ℂ) : Filter.Tendsto (fun k => (H k).eval u)
      Filter.atTop (nhds (H₀.eval u)) := by
    simp only [H, H₀, eval_add, eval_mul, eval_C]
    exact (hfeval u).add ((hgeval u).const_mul w)
  have hHlimit : IsUpperHalfPlaneStable H₀ :=
    isUpperHalfPlaneStable_of_tendsto_eval_of_natDegree_le
      hH₀ hHdeg (fun k => Or.inr (hHstable k)) hHeval
  simpa [H₀, eval_add, eval_mul, eval_C] using hHlimit z hz

private theorem meshDifference_tendsto_eval_complexify
    (p : ℝ[X]) (α : ℝ) {lam : ℕ → ℝ}
    (hlam : Filter.Tendsto lam Filter.atTop (nhds 1)) (z : ℂ) :
    Filter.Tendsto
      (fun k => (complexify (meshDifference α (lam k) p)).eval z)
      Filter.atTop
      (nhds ((complexify (meshDifference α 1 p)).eval z)) := by
  let q := p.comp (X - C α)
  have hform (a : ℝ) :
      (complexify (meshDifference α a p)).eval z =
        (complexify p).eval z - (a : ℂ) * (complexify q).eval z := by
    simp [meshDifference, complexify, q]
  have hcoe : Filter.Tendsto (fun k => (lam k : ℂ)) Filter.atTop (nhds 1) :=
    (Complex.continuous_ofReal.tendsto 1).comp hlam
  have hconst : Filter.Tendsto (fun _ : ℕ => (complexify p).eval z)
      Filter.atTop (nhds ((complexify p).eval z)) := tendsto_const_nhds
  have hlim : Filter.Tendsto
      (fun k => (complexify p).eval z - (lam k : ℂ) * (complexify q).eval z)
      Filter.atTop
      (nhds ((complexify p).eval z - (1 : ℂ) * (complexify q).eval z)) :=
    hconst.sub (hcoe.mul_const _)
  simpa [hform] using hlim

private theorem eval_complexify_comp_X_sub_C (p : ℝ[X]) (β : ℝ) (z : ℂ) :
    (complexify (p.comp (X - C β))).eval z =
      (complexify p).eval (z - (β : ℂ)) := by
  simp [complexify, Polynomial.map_comp, eval_comp]

/-- A bounded-degree evaluation limit of polynomials with only nonnegative roots, which splits,
has only nonnegative roots. -/
theorem HasOnlyNonnegRoots.of_tendsto_eval_of_natDegree_le
    {f : ℕ → ℝ[X]} {f₀ : ℝ[X]} {N : ℕ}
    (hf : ∀ k, HasOnlyNonnegRoots (f k))
    (hdeg : ∀ k, (f k).natDegree ≤ N)
    (heval : ∀ z : ℂ, Filter.Tendsto
      (fun k => (complexify (f k)).eval z) Filter.atTop
        (nhds ((complexify f₀).eval z)))
    (hf₀s : f₀.Splits) : HasOnlyNonnegRoots f₀ := by
  let S : Set ℂ := {z | 0 ≤ z.re}
  have hS : IsClosed S := isClosed_le continuous_const Complex.continuous_re
  have hdeg' (k : ℕ) : (complexify (f k)).natDegree ≤ N :=
    Polynomial.natDegree_map_le.trans (hdeg k)
  have hroots (k : ℕ) (z : ℂ) (hz : z ∈ (complexify (f k)).roots) : z ∈ S := by
    rcases hf k with hzero | ⟨hs, hnn⟩
    · simp [complexify, hzero] at hz
    · have hmap := hs.roots_map_of_injective Complex.ofRealHom.injective
      change (complexify (f k)).roots = _ at hmap
      rw [hmap] at hz
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hz
      exact_mod_cast hnn r hr
  have hlimit := Polynomial.roots_mem_of_tendsto_eval_of_natDegree_le
    hS hdeg' hroots heval
  right
  refine ⟨hf₀s, ?_⟩
  intro r hr
  have hmap := hf₀s.roots_map_of_injective Complex.ofRealHom.injective
  change (complexify f₀).roots = _ at hmap
  have hrcomplex : (r : ℂ) ∈ (complexify f₀).roots := by
    rw [hmap]
    exact Multiset.mem_map.mpr ⟨r, hr, rfl⟩
  have hrr : (0 : ℝ) ≤ r := by
    have hz := hlimit (r : ℂ) hrcomplex
    simpa [S] using hz
  exact hrr

/-- The cancelling weight follows by Hurwitz closure of the stable pencils.
The output degree may drop at `λ = 1`. -/
theorem meshDifference_meshGE_one {p : ℝ[X]} {α β : ℝ}
    (hα : 0 < α) (hp : p.MeshGE β) (hαβ : α ≤ β) :
    (meshDifference α 1 p).MeshGE β := by
  by_cases hT0 : meshDifference α 1 p = 0
  · rw [hT0]
    exact Polynomial.MeshGE.of_natDegree_le_one (by simp) (by simp) (by linarith)
  have hp0 : p ≠ 0 := by
    intro hz
    exact hT0 (by simp [meshDifference, hz])
  let lam : ℕ → ℝ := fun k => 1 + 1 / (k + 1 : ℝ)
  have hlam_gt (k : ℕ) : 1 < lam k := by
    norm_num [lam]
    positivity
  have hlam_pos (k : ℕ) : 0 < lam k := lt_trans zero_lt_one (hlam_gt k)
  have hlam_ne (k : ℕ) : lam k ≠ 1 := ne_of_gt (hlam_gt k)
  have hlam_lim : Filter.Tendsto lam Filter.atTop (nhds 1) := by
    simpa [lam] using (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let F : ℕ → ℝ[X] := fun k => meshDifference α (lam k) p
  let G : ℕ → ℝ[X] := fun k => (F k).comp (X - C β)
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hstable (k : ℕ) : IsUpperHalfPlaneStablePencil (G k) (F k) := by
    have hmesh : (F k).MeshGE β :=
      meshDifference_meshGE_of_ne_one hα (hlam_pos k) (hlam_ne k) hp hαβ
    have hF0 : F k ≠ 0 := by
      intro hz
      have hlc := meshDifference_leadingCoeff_of_ne_one p α (lam k) (hlam_ne k)
      rw [← show F k = meshDifference α (lam k) p from rfl, hz,
        leadingCoeff_zero] at hlc
      exact (mul_ne_zero (sub_ne_zero.mpr (Ne.symm (hlam_ne k)))
        (leadingCoeff_ne_zero.mpr hp0)) hlc.symm
    exact (((Polynomial.MeshGE.iff_eq_zero_or_stablePencil hβ).1 hmesh).resolve_left
      hF0)
  have hFdeg (k : ℕ) : (F k).natDegree ≤ p.natDegree :=
    meshDifference_natDegree_le p α (lam k)
  have hGdeg (k : ℕ) : (G k).natDegree ≤ p.natDegree := by
    calc
      (G k).natDegree ≤ (F k).natDegree * (X - C β : ℝ[X]).natDegree :=
        natDegree_comp_le
      _ = (F k).natDegree := by simp
      _ ≤ p.natDegree := hFdeg k
  have hFeval (z : ℂ) : Filter.Tendsto
      (fun k => (complexify (F k)).eval z) Filter.atTop
        (nhds ((complexify (meshDifference α 1 p)).eval z)) :=
    meshDifference_tendsto_eval_complexify p α hlam_lim z
  have hGeval (z : ℂ) : Filter.Tendsto
      (fun k => (complexify (G k)).eval z) Filter.atTop
        (nhds ((complexify ((meshDifference α 1 p).comp (X - C β))).eval z)) := by
    simpa [G, F, eval_complexify_comp_X_sub_C] using
      hFeval (z - (β : ℂ))
  have hlim : IsUpperHalfPlaneStablePencil
      ((meshDifference α 1 p).comp (X - C β)) (meshDifference α 1 p) :=
    IsUpperHalfPlaneStablePencil.of_tendsto_eval_of_natDegree_le hstable hGdeg hFdeg
      hGeval hFeval hT0
  exact (Polynomial.MeshGE.iff_eq_zero_or_stablePencil hβ).2 (Or.inr hlim)

/-- Brändén--Krasikov--Shapiro Theorem 2: a positive finite difference preserves
every mesh lower bound at least as large as its step. -/
theorem meshDifference_meshGE {p : ℝ[X]} {α β lam : ℝ}
    (hα : 0 < α) (hlam : 0 < lam) (hp : p.MeshGE β) (hαβ : α ≤ β) :
    (meshDifference α lam p).MeshGE β := by
  by_cases hne : lam = 1
  · subst lam
    exact meshDifference_meshGE_one hα hp hαβ
  · exact meshDifference_meshGE_of_ne_one hα hlam hne hp hαβ

/-- For `λ > 1`, every ordered root of the finite difference lies weakly to
the right of the corresponding input root. -/
theorem meshDifference_strictInterl_of_one_lt {p : ℝ[X]} {α lam : ℝ}
    (hα : 0 < α) (hlam : 1 < lam) (hp : p.MeshGE α)
    (hdeg : 0 < p.natDegree) :
    StrictInterl p (meshDifference α lam p) := by
  have hp0 : p ≠ 0 := by intro hz; simp [hz] at hdeg
  have hproper : IsUpperHalfPlaneStablePencil (p.comp (X - C α)) p :=
    ((Polynomial.MeshGE.iff_eq_zero_or_stablePencil hα).1 hp).resolve_left hp0
  have htr : IsUpperHalfPlaneStablePencil p (meshDifference α lam p) := by
    simpa [meshDifference] using hproper.base_direction_shear (lt_trans zero_lt_one hlam)
  have hswap := htr.swap_neg
  have hlam1 : lam ≠ 1 := ne_of_gt hlam
  have hTdeg : (meshDifference α lam p).natDegree = p.natDegree :=
    meshDifference_natDegree_of_ne_one p α lam hlam1
  have hTlc : (meshDifference α lam p).leadingCoeff =
      (1 - lam) * p.leadingCoeff :=
    meshDifference_leadingCoeff_of_ne_one p α lam hlam1
  have hlc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  rcases lt_or_gt_of_ne hlc0 with hneg | hpos
  · have hfpos : HasPosLeadingCoeff (-p) := by
      simpa [HasPosLeadingCoeff] using neg_pos.mpr hneg
    have hgpos : HasPosLeadingCoeff (meshDifference α lam p) := by
      rw [HasPosLeadingCoeff, hTlc]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr hlam) hneg
    have hgdeg : (meshDifference α lam p).natDegree ≠ 0 := by lia
    have hstrict : StrictInterl (-p) (meshDifference α lam p) :=
      (isUpperHalfPlaneStablePencil_iff_strictInterl hgpos hfpos hgdeg).1 hswap
    have hscaled := hstrict.C_mul_left (a := -1) (by norm_num)
    simpa using hscaled
  · have hfpos : HasPosLeadingCoeff p := hpos
    have hgpos : HasPosLeadingCoeff (-(meshDifference α lam p)) := by
      rw [HasPosLeadingCoeff, leadingCoeff_neg, hTlc]
      exact neg_pos.mpr (mul_neg_of_neg_of_pos (sub_neg.mpr hlam) hpos)
    have hgdeg : (-(meshDifference α lam p)).natDegree ≠ 0 := by
      simpa [hTdeg] using hdeg.ne'
    have hstable : IsUpperHalfPlaneStablePencil
        (-(meshDifference α lam p)) p := by simpa using hswap.neg_neg
    have hstrict : StrictInterl p (-(meshDifference α lam p)) :=
      (isUpperHalfPlaneStablePencil_iff_strictInterl hgpos hfpos hgdeg).1
        hstable
    have hscaled := hstrict.C_mul_right (a := -1) (by norm_num)
    simpa using hscaled

private theorem hasOnlyNonnegRoots_of_strictInterl_sameDegree
    {p q : ℝ[X]} (h : StrictInterl p q)
    (hdeg : p.natDegree = q.natDegree)
    (hp : HasOnlyNonnegRoots p) : HasOnlyNonnegRoots q := by
  rcases hp with hp0 | ⟨_, hpnn⟩
  · exact False.elim (h.1.1 hp0)
  right
  refine ⟨h.2.1.2, ?_⟩
  intro r hr
  have hmem : r ∈ q.roots.sort (· ≤ ·) := (Multiset.mem_sort (· ≤ ·)).mpr hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
  let n := p.natDegree
  have hqlen : (q.roots.sort (· ≤ ·)).length = n := by
    rw [Multiset.length_sort, Polynomial.splits_iff_card_roots.mp h.2.1.2,
      ← hdeg]
  let j : Fin n := ⟨i, by simpa [hqlen] using hi⟩
  have hqroot : orderedRoot q n j = (q.roots.sort (· ≤ ·))[i] := by
    simp [orderedRoot, j, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi]
  have hple : 0 ≤ orderedRoot p n j := by
    apply hpnn
    exact orderedRoot_mem_roots
      (Polynomial.splits_iff_card_roots.mp h.1.2) j
  have hle : orderedRoot p n j ≤ orderedRoot q n j :=
    h.orderedRoot_le rfl hdeg.symm j
  rw [hqroot] at hle
  linarith

/-- For `λ > 1`, finite differences preserve nonnegative roots as well as mesh. -/
theorem meshDifference_hasOnlyNonnegRoots_of_one_lt
    {p : ℝ[X]} {α β lam : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hlam : 1 < lam)
    (hpmesh : p.MeshGE β) (hpnn : HasOnlyNonnegRoots p) :
    HasOnlyNonnegRoots (meshDifference α lam p) := by
  by_cases hp0 : p = 0
  · left
    simp [meshDifference, hp0]
  by_cases hdeg : p.natDegree = 0
  · right
    refine ⟨(meshDifference_meshGE hα (lt_trans zero_lt_one hlam) hpmesh hαβ).1,
      ?_⟩
    intro r hr
    have hTdeg : (meshDifference α lam p).natDegree = 0 := by
      rw [meshDifference_natDegree_of_ne_one p α lam (ne_of_gt hlam), hdeg]
    have hcard : (meshDifference α lam p).roots.card = 0 := by
      rw [Polynomial.splits_iff_card_roots.mp
        (meshDifference_meshGE hα (lt_trans zero_lt_one hlam) hpmesh hαβ).1,
        hTdeg]
    simp [Multiset.card_eq_zero.mp hcard] at hr
  · have hstrict := meshDifference_strictInterl_of_one_lt hα hlam
      (hpmesh.antitone hα.le hαβ) (Nat.pos_of_ne_zero hdeg)
    exact hasOnlyNonnegRoots_of_strictInterl_sameDegree hstrict
      (meshDifference_natDegree_of_ne_one p α lam (ne_of_gt hlam)).symm hpnn

/-- At `λ = 1`, nonnegative roots survive by the same bounded-degree root
closure used for the mesh boundary. -/
theorem meshDifference_hasOnlyNonnegRoots_one
    {p : ℝ[X]} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hpmesh : p.MeshGE β) (hpnn : HasOnlyNonnegRoots p) :
    HasOnlyNonnegRoots (meshDifference α 1 p) := by
  by_cases hT0 : meshDifference α 1 p = 0
  · exact Or.inl hT0
  let lam : ℕ → ℝ := fun k => 1 + 1 / (k + 1 : ℝ)
  have hlam_gt (k : ℕ) : 1 < lam k := by
    norm_num [lam]
    positivity
  have hlam_lim : Filter.Tendsto lam Filter.atTop (nhds 1) := by
    simpa [lam] using (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let F : ℕ → ℝ[X] := fun k => meshDifference α (lam k) p
  have hFnn (k : ℕ) : HasOnlyNonnegRoots (F k) :=
    meshDifference_hasOnlyNonnegRoots_of_one_lt hα hαβ (hlam_gt k) hpmesh hpnn
  have hFdeg (k : ℕ) : (F k).natDegree ≤ p.natDegree :=
    meshDifference_natDegree_le p α (lam k)
  have hFeval (z : ℂ) : Filter.Tendsto
      (fun k => (complexify (F k)).eval z) Filter.atTop
        (nhds ((complexify (meshDifference α 1 p)).eval z)) :=
    meshDifference_tendsto_eval_complexify p α hlam_lim z
  exact HasOnlyNonnegRoots.of_tendsto_eval_of_natDegree_le hFnn hFdeg
    hFeval (meshDifference_meshGE_one hα hpmesh hαβ).1

/-- The nonnegative-zero clause of BKS Theorem 2 for `λ ≥ 1`. -/
theorem meshDifference_hasOnlyNonnegRoots
    {p : ℝ[X]} {α β lam : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hlam : 1 ≤ lam) (hpmesh : p.MeshGE β)
    (hpnn : HasOnlyNonnegRoots p) :
    HasOnlyNonnegRoots (meshDifference α lam p) := by
  rcases eq_or_lt_of_le hlam with heq | hlt
  · subst lam
    exact meshDifference_hasOnlyNonnegRoots_one hα hαβ hpmesh hpnn
  · exact meshDifference_hasOnlyNonnegRoots_of_one_lt hα hαβ hlt hpmesh hpnn

end

end RealRooted
