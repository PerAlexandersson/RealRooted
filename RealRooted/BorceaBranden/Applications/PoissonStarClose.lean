module

public import RealRooted.BorceaBranden.Applications.PoissonStarTransport
public import RealRooted.Interlacing.OuterDifference

/-!
# Closing consequences for the univariate Poisson product

This file proves the missing affine-test necessity in the exact fixed-factor
classification.  The proof deletes all but one copy of a chosen root from the
Euler pencil and uses the forced orientation of the resulting degree-growth-one
pair.
-/

@[expose] public section

open Polynomial

namespace RealRooted.Poisson

noncomputable section

/-- A nonzero fixed factor which preserves splitting on every affine input
satisfies the root-sign admissibility condition. -/
theorem isAdmissible_of_preservesAffineRealRooted {c : ℝ} {f : ℝ[X]}
    (hf0 : f ≠ 0) (hpres : PreservesAffineRealRooted c f) :
    IsAdmissible c f := by
  have hfs : f.Splits := by
    have hs := hpres 1 0
    rw [show C 1 + C 0 * X = (1 : ℝ[X]) by simp, starC_one_right] at hs
    exact hs
  refine ⟨hf0, hfs, ?_⟩
  intro r hr
  have hfr : f.IsRoot r := (mem_roots hf0).mp hr
  let m := f.rootMultiplicity r
  let q : ℝ[X] := X - C r
  obtain ⟨h, hfactor, hnotdvd⟩ :=
    f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hf0 r
  change f = q ^ m * h at hfactor
  have hmpos : 0 < m := by
    exact (rootMultiplicity_pos hf0).mpr hfr
  have hmcast : 0 < (m : ℝ) := by positivity
  have hm_eq : m - 1 + 1 = m := by lia
  have hq0 : q ≠ 0 := X_sub_C_ne_zero r
  have hh0 : h ≠ 0 := by
    intro hh
    apply hf0
    rw [hfactor, hh, mul_zero]
  have hheval : h.eval r ≠ 0 := by
    intro heval
    apply hnotdvd
    rw [dvd_iff_isRoot, Polynomial.IsRoot.def]
    exact heval
  let D : ℝ[X] := q ^ (m - 1)
  let F : ℝ[X] := q * h
  let G : ℝ[X] :=
    X * (q * h + C (c * m) * h + C c * q * h.derivative)
  have hfDF : f = D * F := by
    rw [hfactor]
    dsimp only [D, F]
    have hpow : q ^ m = q ^ (m - 1) * q := by
      rw [← pow_succ, hm_eq]
    rw [hpow]
    ring
  have hA : X * (f + C c * f.derivative) = D * G := by
    rw [hfactor]
    dsimp only [D, G]
    rw [derivative_mul, derivative_pow, derivative_sub, derivative_X,
      derivative_C, sub_zero]
    rw [show q ^ m = q ^ (m - 1) * q by rw [← pow_succ, hm_eq]]
    simp only [map_mul]
    ring
  have hD0 : D ≠ 0 := pow_ne_zero _ hq0
  have hDs : D.Splits := by
    dsimp only [D, q]
    exact (Polynomial.Splits.X_sub_C r).pow (m - 1)
  have hall : AllComboRealRooted F G := by
    intro a b
    have hs := hpres a b
    rw [starC_affine_right] at hs
    apply (splits_mul_iff_right hD0 hDs).mp
    convert hs using 1
    calc
      D * (C a * F + C b * G) = C a * (D * F) + C b * (D * G) := by ring
      _ = C a * f + C b * (X * (f + C c * f.derivative)) := by
        rw [← hfDF, ← hA]
      _ = C a * f + C b * X * (f + C c * f.derivative) := by ring
  have hF0 : F ≠ 0 := mul_ne_zero hq0 hh0
  have hdegfpos : 0 < f.natDegree := by
    have hmle := rootMultiplicity_le_natDegree f r
    lia
  have hderlt : f.derivative.natDegree < f.natDegree :=
    natDegree_derivative_lt (by lia)
  have hcderlt : (C c * f.derivative).natDegree < f.natDegree :=
    (natDegree_C_mul_le c f.derivative).trans_lt hderlt
  have hsumdeg : (f + C c * f.derivative).natDegree = f.natDegree :=
    natDegree_add_eq_left_of_natDegree_lt hcderlt
  have hsum0 : f + C c * f.derivative ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hsumdeg
    lia
  have hA0 : X * (f + C c * f.derivative) ≠ 0 :=
    mul_ne_zero X_ne_zero hsum0
  have hG0 : G ≠ 0 := by
    intro hzero
    apply hA0
    rw [hA, hzero, mul_zero]
  have hFdeg : f.natDegree = D.natDegree + F.natDegree := by
    rw [hfDF, natDegree_mul hD0 hF0]
  have hGdeg : f.natDegree + 1 = D.natDegree + G.natDegree := by
    rw [← hsumdeg, ← natDegree_X_mul hsum0, hA,
      natDegree_mul hD0 hG0]
  have hsucc : G.natDegree = F.natDegree + 1 := by lia
  have hFs : F.Splits := hall.left_splits
  have hGs : G.Splits := hall.right_splits
  have hinter_or : StrictInterl F G ∨ StrictInterl G F :=
    strictInterl_of_allComboRealRooted hF0 hFs hG0 hGs hall
      (Or.inl hsucc.symm)
  have hinter : StrictInterl F G :=
    StrictInterl.forward_of_orientation_of_succDegree hsucc hinter_or
  have hDmonic : D.Monic := (monic_X_sub_C r).pow (m - 1)
  have hFlc : F.leadingCoeff = f.leadingCoeff := by
    have hlc := congrArg leadingCoeff hfDF
    simpa only [leadingCoeff_mul, hDmonic.leadingCoeff, one_mul] using hlc.symm
  have hAlc : (X * (f + C c * f.derivative)).leadingCoeff = f.leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_X, one_mul, leadingCoeff, hsumdeg,
      coeff_add, coeff_C_mul, coeff_eq_zero_of_natDegree_lt hderlt, mul_zero,
      add_zero, coeff_natDegree]
  have hGlc : G.leadingCoeff = f.leadingCoeff := by
    have hlc := congrArg leadingCoeff hA
    rw [hAlc, leadingCoeff_mul, hDmonic.leadingCoeff, one_mul] at hlc
    exact hlc.symm
  let a : ℝ := f.leadingCoeff⁻¹
  have hflc0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have ha0 : a ≠ 0 := inv_ne_zero hflc0
  have hscaled : StrictInterl (C a * F) (C a * G) :=
    (hinter.C_mul_left ha0).C_mul_right ha0
  have hFpos : HasPosLeadingCoeff (C a * F) := by
    unfold HasPosLeadingCoeff
    rw [leadingCoeff_mul, leadingCoeff_C, hFlc]
    rw [inv_mul_cancel₀ hflc0]
    norm_num
  have hGpos : HasPosLeadingCoeff (C a * G) := by
    unfold HasPosLeadingCoeff
    rw [leadingCoeff_mul, leadingCoeff_C, hGlc]
    rw [inv_mul_cancel₀ hflc0]
    norm_num
  have hFroot : (C a * F).IsRoot r := by
    rw [Polynomial.IsRoot.def]
    simp only [eval_mul, eval_C]
    dsimp only [F, q]
    simp
  have hsign :=
    hscaled.eval_mul_derivative_nonpos_of_left_root hFpos hGpos hFroot
  have ha_sq : 0 < a ^ 2 := sq_pos_of_ne_zero ha0
  have hh_sq : 0 < (h.eval r) ^ 2 := sq_pos_of_ne_zero hheval
  dsimp only [F, G, q] at hsign
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, eval_mul, eval_add, eval_sub, eval_X, eval_C, zero_mul,
    zero_add, sub_self, one_mul] at hsign
  have hsign' : a ^ 2 * (c * r) * (m : ℝ) * (h.eval r) ^ 2 ≤ 0 := by
    convert hsign using 1
    ring
  by_contra hcr
  have hcrpos : 0 < c * r := lt_of_not_ge hcr
  have hpositive : 0 < a ^ 2 * (c * r) * (m : ℝ) * (h.eval r) ^ 2 := by
    apply mul_pos
    · exact mul_pos (mul_pos ha_sq hcrpos) hmcast
    · exact hh_sq
  exact (not_lt_of_ge hsign') hpositive

/-- For a nonzero fixed factor, affine real-rootedness preservation is
equivalent to the exact root-sign admissibility condition. -/
theorem preservesAffineRealRooted_iff_isAdmissible {c : ℝ} {f : ℝ[X]}
    (hf0 : f ≠ 0) :
    PreservesAffineRealRooted c f ↔ IsAdmissible c f := by
  constructor
  · exact isAdmissible_of_preservesAffineRealRooted hf0
  · intro hf a b
    let g : ℝ[X] := C a + C b * X
    change (starC c f g).Splits
    by_cases hg0 : g = 0
    · rw [hg0, starC_zero_right]
      exact Polynomial.Splits.zero
    · have hgs : g.Splits := Polynomial.Splits.of_natDegree_le_one (by
        dsimp only [g]
        refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
        exact natDegree_mul_le.trans (by simp))
      rcases hf.preservesRealRootedOrZero g ⟨hg0, hgs⟩ with hzero | hs
      · rw [starCLinearMap_apply] at hzero
        rw [hzero]
        exact Polynomial.Splits.zero
      · simpa only [starCLinearMap_apply] using hs

/-- Preservation on every nonzero split input implies preservation on the
affine test class. -/
theorem preservesAffineRealRooted_of_preservesRealRootedOrZero
    {c : ℝ} {f : ℝ[X]}
    (hpres : PreservesRealRootedOrZero (starCLinearMap c f)) :
    PreservesAffineRealRooted c f := by
  intro a b
  let g : ℝ[X] := C a + C b * X
  change (starC c f g).Splits
  by_cases hg0 : g = 0
  · rw [hg0, starC_zero_right]
    exact Polynomial.Splits.zero
  · have hgs : g.Splits := Polynomial.Splits.of_natDegree_le_one (by
      dsimp only [g]
      refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
      exact natDegree_mul_le.trans (by simp))
    rcases hpres g ⟨hg0, hgs⟩ with hzero | hs
    · rw [starCLinearMap_apply] at hzero
      rw [hzero]
      exact Polynomial.Splits.zero
    · simpa only [starCLinearMap_apply] using hs

/-- For a nonzero fixed factor, preservation on all split inputs is equivalent
to preservation on affine inputs. -/
theorem preservesRealRootedOrZero_iff_preservesAffineRealRooted
    {c : ℝ} {f : ℝ[X]} (hf0 : f ≠ 0) :
    PreservesRealRootedOrZero (starCLinearMap c f) ↔
      PreservesAffineRealRooted c f := by
  constructor
  · exact preservesAffineRealRooted_of_preservesRealRootedOrZero
  · intro hpres
    exact (isAdmissible_of_preservesAffineRealRooted hf0 hpres).preservesRealRootedOrZero

/-- For a nonzero fixed factor, preservation on every split input is
equivalent to the exact root-sign admissibility condition. -/
theorem preservesRealRootedOrZero_iff_isAdmissible
    {c : ℝ} {f : ℝ[X]} (hf0 : f ≠ 0) :
    PreservesRealRootedOrZero (starCLinearMap c f) ↔ IsAdmissible c f := by
  rw [preservesRealRootedOrZero_iff_preservesAffineRealRooted hf0,
    preservesAffineRealRooted_iff_isAdmissible hf0]

end

end RealRooted.Poisson
