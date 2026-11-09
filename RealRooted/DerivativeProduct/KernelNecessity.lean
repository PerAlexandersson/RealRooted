module

public import RealRooted.DerivativeProduct.Basic
public import RealRooted.RootLocation.Basic
import RealRooted.AllCombo
import RealRooted.Interlacing.OuterDifference
import RealRooted.ObreschkoffConverse.Converse
import RealRooted.Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic

/-!
# Necessity in the fixed-factor criterion for derivative products

Let `w` be a quadratic weight with nonnegative `X ^ 2`-coefficient and let `c` be a coefficient
sequence with `c 0 = 1`, `c k ≥ 0` and `c 1 > 0`.  If a nonzero polynomial `g` satisfies that
`g ⋆ (α + β X)` is real-rooted for all real `α, β`, then `g` is real-rooted and `w r ≤ 0` at every
root `r` of `g`.

The inputs `1` and `X` give the pencil `g, F = X g + c 1 * w * g'`, whose combinations are
real-rooted; the degree of `F` is `deg g + 1` and its leading coefficient is
`(1 + c 1 * A * deg g) * lc g`, so the pencil is in directed proper position.  Deleting all but one
copy of a root `r` of `g` keeps this structure, and the sign condition for proper position at a
root of the left polynomial gives `c 1 * m * w r * h r ^ 2 ≤ 0`.  This is the residue argument of
issue #2369 (Theorem 2) and issue #2363, following the Poisson case
`RealRooted.Poisson.isAdmissible_of_preservesAffineRealRooted`.
-/

public section

open Polynomial Set

namespace RealRooted

noncomputable section

variable {w : ℝ[X]} {c : ℕ → ℝ}

/-- The affine inputs of a derivative product with `c 0 = 1` give the pencil spanned by `g` and
`X * g + c 1 * w * g'`. -/
theorem derivProduct_affine_right (hc : c 0 = 1) (g : ℝ[X]) (α β : ℝ) :
    derivProduct w c g (C α + C β * X) =
      C α * g + C β * (X * g + C (c 1) * w * derivative g) := by
  rw [derivProduct_add_right, derivProduct_C_mul_right, derivProduct_X_right hc,
    derivProduct_comm, derivProduct_C_left, hc, one_mul]

/-- The pencil partner `X * g + c 1 * w * g'` of a derivative product with `X`, with all but one
copy of the root `r` of `g` deleted. -/
private lemma pencil_eq_mul_reduced {g h : ℝ[X]} {r : ℝ} {m : ℕ} (hm : 0 < m)
    (hg : g = (X - C r) ^ m * h) (c1 : ℝ) :
    X * g + C c1 * w * derivative g = (X - C r) ^ (m - 1) *
      (X * ((X - C r) * h) +
        C c1 * w * (C (m : ℝ) * h + (X - C r) * derivative h)) := by
  have hm1 : m - 1 + 1 = m := by lia
  have hpow : (X - C r) ^ m = (X - C r) ^ (m - 1) * (X - C r) := by rw [← pow_succ, hm1]
  have hderiv : derivative ((X - C r) ^ m) =
      C (m : ℝ) * (X - C r) ^ (m - 1) := by
    rw [derivative_pow]
    simp
  rw [hg, derivative_mul, hderiv, hpow]
  ring

/-- The sign argument: the reduced pencil is in proper position, which forces `w r ≤ 0`. -/
private lemma weight_nonpos_of_reduced_pencil {W : ℝ[X]} {c1 : ℝ} (hc1 : 0 < c1) {r : ℝ}
    {h : ℝ[X]} {m : ℕ} (hm : 0 < m) (hh : h.eval r ≠ 0) {a b : ℝ} (hab : 0 < a * b)
    {F G : ℝ[X]} (hF : F = (X - C r) * h)
    (hG : G = X * ((X - C r) * h) +
      C c1 * W * (C (m : ℝ) * h + (X - C r) * derivative h))
    (hinter : StrictInterl (C a * F) (C b * G))
    (hFpos : HasPosLeadingCoeff (C a * F)) (hGpos : HasPosLeadingCoeff (C b * G)) :
    W.eval r ≤ 0 := by
  have hFroot : (C a * F).IsRoot r := by
    rw [IsRoot.def, hF]
    simp
  have hsign := hinter.eval_mul_derivative_nonpos_of_left_root hFpos hGpos hFroot
  rw [hF, hG] at hsign
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, eval_mul,
    eval_add, eval_sub, eval_X, eval_C, sub_self, zero_mul, one_mul, mul_zero,
    zero_add, add_zero] at hsign
  have hpos : 0 < a * b * (c1 * (m : ℝ) * h.eval r ^ 2) := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    have := sq_pos_of_ne_zero hh
    positivity
  by_contra hW
  push Not at hW
  nlinarith [mul_pos hpos hW]

/-- **Fixed-factor necessity for derivative products.**  Let `w` be a quadratic weight with
nonnegative `X ^ 2`-coefficient and `c` a coefficient sequence with `c 0 = 1`, `c k ≥ 0` and
`c 1 > 0`.  If a nonzero `g` has `g ⋆ (α + β X)` real-rooted for all real `α, β`, then `g` is
real-rooted and `w r ≤ 0` at each root `r` of `g`. -/
theorem isRealRootedIn_of_splits_derivProduct_affine (hw : w.natDegree ≤ 2)
    (hA : 0 ≤ w.coeff 2) (hc0 : c 0 = 1) (hc : ∀ k, 0 ≤ c k) (hc1 : 0 < c 1) {g : ℝ[X]}
    (hg0 : g ≠ 0) (hpres : ∀ α β : ℝ, (derivProduct w c g (C α + C β * X)).Splits) :
    IsRealRootedIn {r | w.eval r ≤ 0} g := by
  have hgs : g.Splits := by
    have h := hpres 1 0
    rw [derivProduct_affine_right hc0] at h
    simpa using h
  refine ⟨hg0, hgs, fun r hr ↦ ?_⟩
  have hgr : g.IsRoot r := (mem_roots hg0).mp hr
  obtain ⟨h, hfactor, hnotdvd⟩ := g.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hg0 r
  set m := g.rootMultiplicity r with hmdef
  have hm : 0 < m := (rootMultiplicity_pos hg0).mpr hgr
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hg0 (by rw [hfactor, mul_zero])
  have hheval : h.eval r ≠ 0 := fun heval ↦ hnotdvd (dvd_iff_isRoot.mpr heval)
  set q : ℝ[X] := X - C r with hq
  set D : ℝ[X] := q ^ (m - 1) with hD
  set F : ℝ[X] := q * h with hF
  set G : ℝ[X] := X * (q * h) + C (c 1) * w * (C (m : ℝ) * h + q * derivative h) with hG
  set E : ℝ[X] := X * g + C (c 1) * w * derivative g with hEdef
  have hEDG : E = D * G := pencil_eq_mul_reduced hm hfactor (c 1)
  have hgDF : g = D * F := by
    rw [hfactor, hD, hF, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hm]
  have hE : E = derivProduct w c X g := by rw [derivProduct_X_left hc0]
  have hEne : E ≠ 0 := by
    rw [hE]
    exact derivProduct_ne_zero hw hA hc0 hc X_ne_zero hg0
  have hEdeg : E.natDegree = 1 + g.natDegree := by
    rw [hE, natDegree_derivProduct hw hA hc0 hc X_ne_zero hg0, natDegree_X]
  set k : ℝ := 1 + c 1 * w.coeff 2 * g.natDegree with hk
  have hkpos : 0 < k := by
    have : 0 ≤ c 1 * w.coeff 2 * g.natDegree := by positivity
    rw [hk]
    linarith
  have hElc : E.leadingCoeff = g.leadingCoeff * k := by
    rw [hE, leadingCoeff_derivProduct hw hA hc0 hc X_ne_zero hg0, leadingCoeff_X, natDegree_X,
      derivProductLeadingFactor_one_left _ _ hc0, one_mul, hk]
  have hq0 : q ≠ 0 := X_sub_C_ne_zero r
  have hD0 : D ≠ 0 := pow_ne_zero _ hq0
  have hDmonic : D.Monic := (monic_X_sub_C r).pow (m - 1)
  have hDs : D.Splits := (Polynomial.Splits.X_sub_C r).pow (m - 1)
  have hF0 : F ≠ 0 := mul_ne_zero hq0 hh0
  have hG0 : G ≠ 0 := by
    rintro hzero
    exact hEne (by rw [hEDG, hzero, mul_zero])
  have hFdeg : g.natDegree = D.natDegree + F.natDegree := by
    rw [← natDegree_mul hD0 hF0, ← hgDF]
  have hGdeg : E.natDegree = D.natDegree + G.natDegree := by
    rw [hEDG, natDegree_mul hD0 hG0]
  have hsucc : G.natDegree = F.natDegree + 1 := by lia
  have hFlc : F.leadingCoeff = g.leadingCoeff := by
    have := congrArg leadingCoeff hgDF
    rwa [leadingCoeff_mul, hDmonic.leadingCoeff, one_mul, eq_comm] at this
  have hGlc : G.leadingCoeff = g.leadingCoeff * k := by
    have := congrArg leadingCoeff hEDG
    rwa [leadingCoeff_mul, hDmonic.leadingCoeff, one_mul, hElc, eq_comm] at this
  have hall : AllComboRealRooted F G := by
    intro α β
    have hs := hpres α β
    rw [derivProduct_affine_right hc0] at hs
    apply (splits_mul_iff_right hD0 hDs).mp
    convert hs using 1
    rw [← hEdef, hEDG, hgDF]
    ring
  have hinter_or := strictInterl_of_allComboRealRooted hF0 hall.left_splits hG0 hall.right_splits
    hall (Or.inl hsucc.symm)
  have hinter : StrictInterl F G :=
    StrictInterl.forward_of_orientation_of_succDegree hsucc hinter_or
  have hlc0 : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  have ha0 : (g.leadingCoeff)⁻¹ ≠ 0 := inv_ne_zero hlc0
  have hb0 : (g.leadingCoeff * k)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hlc0 hkpos.ne')
  have hscaled := (hinter.C_mul_left ha0).C_mul_right hb0
  have hFpos : HasPosLeadingCoeff (C (g.leadingCoeff)⁻¹ * F) := by
    unfold HasPosLeadingCoeff
    rw [leadingCoeff_mul, leadingCoeff_C, hFlc, inv_mul_cancel₀ hlc0]
    exact one_pos
  have hGpos : HasPosLeadingCoeff (C (g.leadingCoeff * k)⁻¹ * G) := by
    unfold HasPosLeadingCoeff
    rw [leadingCoeff_mul, leadingCoeff_C, hGlc, inv_mul_cancel₀ (mul_ne_zero hlc0 hkpos.ne')]
    exact one_pos
  have hab : 0 < (g.leadingCoeff)⁻¹ * (g.leadingCoeff * k)⁻¹ := by
    have : (g.leadingCoeff)⁻¹ * (g.leadingCoeff * k)⁻¹ = (g.leadingCoeff ^ 2 * k)⁻¹ := by
      field_simp
    rw [this]
    exact inv_pos.mpr (mul_pos (sq_pos_of_ne_zero hlc0) hkpos)
  exact weight_nonpos_of_reduced_pencil hc1 hm hheval hab hF hG hscaled hFpos hGpos

end

end RealRooted
