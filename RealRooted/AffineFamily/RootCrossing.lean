/-
# Affine-family root crossing

Double-root exclusion, simple-root consequences, and positive pencil-parameter
crossing data for the affine-family criterion.
-/
import RealRooted.ProductFamily
import RealRooted.AffineDerivative
import RealRooted.AffineFamily.Basic
import RealRooted.AffineFamily.PositiveFamily
import RealRooted.AffineFamily.Boundary
import RealRooted.PosCombo
import RealRooted.SuccDegreeLeftEndpoint
import RealRooted.ObreschkoffConverse
import RealRooted.FolkloreLemma
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

open Polynomial

noncomputable section

namespace RealRooted

/-- Downward boundary closure: if `g - C μ * f` is real-rooted for all
sufficiently small `μ > 0`, and `f.natDegree < g.natDegree` with both
having positive leading coefficients, then `g` is real-rooted.

The proof is the same complex-root continuity argument as
`AffineFamily.isRealRooted_of_add_C_mul_right_family_of_natDegree_lt`, applied with
`-f` as the perturbation (the sign doesn't affect coefficient convergence). -/
private theorem isRealRooted_of_sub_C_mul_right_family_of_natDegree_lt
    {f g : ℝ[X]}
    (hfamily : ∀ {μ : ℝ}, 0 < μ → ((g - C μ * f) ≠ 0 ∧ (g - C μ * f).Splits))
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : f.natDegree < g.natDegree) : (g ≠ 0 ∧ g.Splits) := by
  -- Reduce to the upward-closure lemma by replacing f with -f.
  -- Note: g - C μ * f = g + C μ * (-f) and (-f).natDegree = f.natDegree.
  -- We need HasPosLeadingCoeff (-f) which fails, so we bypass and work
  -- with the monic normalization directly.
  let f₀ : ℝ[X] := C f.leadingCoeff⁻¹ * f
  let g₀ : ℝ[X] := C g.leadingCoeff⁻¹ * g
  have hf_lc_ne : f.leadingCoeff ≠ 0 := ne_of_gt hf_pos
  have hg_lc_ne : g.leadingCoeff ≠ 0 := ne_of_gt hg_pos
  have hf₀_monic : f₀.Monic := by
    unfold f₀
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hg₀_monic : g₀.Monic := by
    unfold g₀
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hg₀_pos : HasPosLeadingCoeff g₀ := hasPosLeadingCoeff_of_monic hg₀_monic
  have hdeg₀ : f₀.natDegree < g₀.natDegree := by
    simp [f₀, g₀, natDegree_C_mul, hf_lc_ne, hg_lc_ne, hdeg]
  -- Monic subtraction family: g₀ - C μ'' * f₀ is real-rooted for small μ'' > 0.
  have hfamily₀ :
      ∀ {μ : ℝ}, 0 < μ → ((g₀ - C μ * f₀) ≠ 0 ∧ (g₀ - C μ * f₀).Splits) := by
    intro μ hμ
    have hμ' : 0 < μ * g.leadingCoeff / f.leadingCoeff :=
      div_pos (mul_pos hμ hg_pos) hf_pos
    have hbase : ((g - C (μ * g.leadingCoeff / f.leadingCoeff) * f) ≠ 0 ∧
      (g - C (μ * g.leadingCoeff / f.leadingCoeff) * f).Splits) :=
      hfamily hμ'
    have hscaled :
        ((C g.leadingCoeff⁻¹ *
            (g - C (μ * g.leadingCoeff / f.leadingCoeff) * f)) ≠ 0 ∧
          (C g.leadingCoeff⁻¹ *
              (g - C (μ * g.leadingCoeff / f.leadingCoeff) * f)).Splits) :=
      isRealRooted_C_mul hbase.1 hbase.2 (inv_ne_zero hg_lc_ne)
    have hEq :
        C g.leadingCoeff⁻¹ *
            (g - C (μ * g.leadingCoeff / f.leadingCoeff) * f) =
          g₀ - C μ * f₀ := by
      ext n
      simp [g₀, f₀, mul_sub]
      grind
    lia
  -- Now: g₀ - C μ * f₀ is real-rooted, monic, same degree as g₀, and
  -- its coefficients converge to those of g₀ as μ → 0⁺.
  -- Use the same complex-root continuity argument to show g₀ is real-rooted.
  have hg₀_rr : (g₀ ≠ 0 ∧ g₀.Splits) := by
    have hroots_real :
        ∀ z ∈ (g₀.map (algebraMap ℝ ℂ)).roots, z ∈ (algebraMap ℝ ℂ).range := by
      intro z hz_mem
      have hmap_ne : g₀.map (algebraMap ℝ ℂ) ≠ 0 :=
        (Polynomial.map_ne_zero_iff (RingHom.injective (algebraMap ℝ ℂ))).2
          hg₀_monic.ne_zero
      have hz_root : (g₀.map (algebraMap ℝ ℂ)).IsRoot z :=
        (Polynomial.mem_roots hmap_ne).1 hz_mem
      have hz_aeval : g₀.aeval z = 0 := by simp_all
      by_contra hz_range
      have hz_im_ne : z.im ≠ 0 := by
        intro hz_im; apply hz_range; exact ⟨z.re, Complex.ext_iff.2 (by simp [hz_im])⟩
      let δ : ℝ := |z.im| / 2
      let R : ℝ := max ‖z‖ 1
      have hδ_pos : 0 < δ := half_pos (abs_pos.mpr hz_im_ne)
      have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      have hg₀_deg_pos : 0 < g₀.natDegree := lt_of_le_of_lt (Nat.zero_le _) hdeg₀
      have hdeg_nat_ne : g₀.natDegree ≠ 0 := Nat.ne_of_gt hg₀_deg_pos
      let u : ℝ := δ / (2 * R)
      let ε : ℝ := (u ^ g₀.natDegree) / (g₀.natDegree + 1)
      have hu_nonneg : 0 ≤ u := by positivity
      have hu_pos : 0 < u := by positivity
      have hε_pos : 0 < ε := by positivity
      let μ : ℝ := ε / (coeffSumRange f₀ + 1)
      have hcoeff_nonneg : 0 ≤ coeffSumRange f₀ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hμ_pos : 0 < μ := by positivity
      have hμ_bound : μ * coeffSumRange f₀ < ε := by
        unfold μ
        have hden_pos : 0 < coeffSumRange f₀ + 1 := by linarith
        have hfrac_lt_one : coeffSumRange f₀ / (coeffSumRange f₀ + 1) < 1 := by
          rw [div_lt_iff₀ hden_pos]; simp
        have hcalc :
            (ε / (coeffSumRange f₀ + 1)) * coeffSumRange f₀ =
              ε * (coeffSumRange f₀ / (coeffSumRange f₀ + 1)) := by
          grind
        simp_all
      -- Coefficient closeness:
      -- ‖(g₀ - C μ * f₀).coeff i - g₀.coeff i‖ = μ * |f₀.coeff i|
      have hcoeff :
          ∀ i : ℕ, ‖(g₀ - C μ * f₀).coeff i - g₀.coeff i‖ < ε := by
        intro i
        have : (g₀ - C μ * f₀).coeff i - g₀.coeff i = -(μ * f₀.coeff i) := by
          simp [coeff_sub, coeff_C_mul]
        rw [this, norm_neg]
        calc
          ‖μ * f₀.coeff i‖ = μ * ‖f₀.coeff i‖ := by
            rw [norm_mul, Real.norm_of_nonneg hμ_pos.le]
          _ ≤ μ * coeffSumRange f₀ :=
              mul_le_mul_of_nonneg_left (coeff_norm_le_coeffSumRange f₀ i) hμ_pos.le
          _ < ε := hμ_bound
      have hμf_deg_lt : (C μ * f₀).natDegree < g₀.natDegree := by
        simpa [natDegree_C_mul hμ_pos.ne'] using hdeg₀
      have hdiff_deg : (g₀ - C μ * f₀).natDegree = g₀.natDegree := by
        rw [sub_eq_add_neg, ← neg_mul]
        exact natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff
          (by simp_all) hg₀_pos
      have hdiff_monic : (g₀ - C μ * f₀).Monic := by
        unfold Polynomial.Monic Polynomial.leadingCoeff
        rw [hdiff_deg, coeff_sub, coeff_eq_zero_of_natDegree_lt hμf_deg_lt,
          hg₀_monic.coeff_natDegree, sub_zero]
      obtain ⟨w, hw_root, hw_dist⟩ :=
        exists_complex_aroot_near_of_isRealRooted_of_monic_of_coeff_close
          (f := g₀) (g := g₀ - C μ * f₀) (z := z) (ε := ε)
          hε_pos hz_aeval hg₀_monic hdiff_monic hdiff_deg hcoeff
            (hfamily₀ hμ_pos).2
      have hw_im_zero : w.im = 0 :=
        RealRooted.im_eq_zero_of_mem_aroots_of_isRealRooted
          (hfamily₀ hμ_pos).1 (hfamily₀ hμ_pos).2 hw_root
      have hbound_eq :
          ((g₀.natDegree + 1) * ε) ^ ((g₀.natDegree : ℝ)⁻¹) * R = δ / 2 := by
        have hmul : ((g₀.natDegree + 1 : ℝ) * ε) = u ^ g₀.natDegree := by grind
        calc ((g₀.natDegree + 1) * ε) ^ ((g₀.natDegree : ℝ)⁻¹) * R
            = (u ^ g₀.natDegree) ^ ((g₀.natDegree : ℝ)⁻¹) * R := by lia
          _ = u * R := by rw [Real.pow_rpow_inv_natCast hu_nonneg hdeg_nat_ne]
          _ = δ / 2 := by grind
      have hdist_lt : ‖z - w‖ < δ := by grind
      have him_le : |z.im| ≤ ‖z - w‖ := by
        simpa [Complex.sub_im, hw_im_zero] using (Complex.abs_im_le_norm (z - w))
      grind
    have hsplit : g₀.Splits :=
      Polynomial.Splits.of_splits_map (i := algebraMap ℝ ℂ)
        (IsAlgClosed.splits _) hroots_real
    exact ⟨hg₀_monic.ne_zero, hsplit⟩
  simpa [show C g.leadingCoeff * g₀ = g from by ext n; grind] using
    isRealRooted_C_mul hg₀_rr.1 hg₀_rr.2 hg_lc_ne

/-- Local bounded right-family double-root obstruction.

If `p` has an exact double root at `x`, `q(x) ≠ 0`, and every sufficiently
small positive perturbation `p + β q` in a fixed right-family window remains
real-rooted, then the standard non-root second-derivative inequality rules out
the positive-sign case `p''(x) * q(x) > 0`. -/
private lemma false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
    {p q : ℝ[X]} {x βmax : ℝ}
    (hfamily :
      ∀ {β : ℝ}, 0 < β → β ≤ βmax → ((p + C β * q) ≠ 0 ∧ (p + C β * q).Splits))
    (hβmax : 0 < βmax)
    (hp_mult : p.rootMultiplicity x = 2)
    (hq_eval_ne : q.eval x ≠ 0)
    (hprod_pos : 0 < p.derivative.derivative.eval x * q.eval x) :
    False := by
  have hp0 : p ≠ 0 := by
    intro hp0
    simp [hp0] at hp_mult
  have hp_root : p.IsRoot x :=
    (rootMultiplicity_pos hp0).mp (by lia)
  have hp_der_root : p.derivative.IsRoot x :=
    isRoot_derivative_of_rootMultiplicity_ge_two (by lia)
  have hp_eval0 : p.eval x = 0 := by simp_all
  have hp_der_eval0 : p.derivative.eval x = 0 := by simp_all
  let pp : ℝ := p.derivative.derivative.eval x
  let qx : ℝ := q.eval x
  let qp : ℝ := q.derivative.eval x
  let qq : ℝ := q.derivative.derivative.eval x
  have hpp_ne : pp ≠ 0 := by grind
  have hqx_ne : qx ≠ 0 := by lia
  let A : ℝ := pp * qx
  let B : ℝ := qp ^ 2 - qq * qx
  let δ₁ : ℝ := A / (2 * (|B| + 1))
  let δ₂ : ℝ := |pp| / (2 * (|qq| + 1))
  let β₀ : ℝ := min δ₁ δ₂
  let β : ℝ := min β₀ βmax
  have hA_pos : 0 < A := by lia
  have hβ_pos : 0 < β := by
    dsimp [β, β₀, δ₁, δ₂, A, B]
    positivity
  have hβ_ne : β ≠ 0 := hβ_pos.ne'
  have hβ_le_β₀ : β ≤ β₀ := min_le_left _ _
  have hβ_le_δ₁ : β ≤ δ₁ := by grind
  have hβ_le_δ₂ : β ≤ δ₂ := by grind
  have hβ_le_max : β ≤ βmax := min_le_right _ _
  have hsecond_small : |β * qq| ≤ |pp| / 2 := by
    calc
      |β * qq| = β * |qq| := by rw [abs_mul, abs_of_nonneg (le_of_lt hβ_pos)]
      _ ≤ β * (|qq| + 1) := by simp_all
      _ ≤ δ₂ * (|qq| + 1) := by gcongr
      _ = |pp| / 2 := by grind
  have hcombo_der2_ne :
      (p.derivative.derivative.eval x + β * q.derivative.derivative.eval x) ≠ 0 := by
    grind
  have hcombo_nonzero :
      p + C β * q ≠ 0 := by
    grind
  have hcombo_rr : ((p + C β * q) ≠ 0 ∧ (p + C β * q).Splits) := hfamily hβ_pos hβ_le_max
  have hcombo_eval_ne :
      (p + C β * q).eval x ≠ 0 := by
    simp_all
  have hcombo_deg_ge2 : 2 ≤ (p + C β * q).natDegree := by
    by_contra hlt
    have hdeg_lt2 : (p + C β * q).natDegree < 2 := by lia
    have hder2_zero : (derivative^[2]) (p + C β * q) = 0 :=
      iterate_derivative_eq_zero hdeg_lt2
    have hder2_eval_zero :
        (p + C β * q).derivative.derivative.eval x = 0 := by
      simp_all
    have : p.derivative.derivative.eval x + β * q.derivative.derivative.eval x = 0 := by
      simpa [derivative_add, derivative_C_mul] using hder2_eval_zero
    lia
  have hineq_raw :=
    deriv2_mul_lt_deriv_sq_at_non_root hcombo_rr.2 (by lia) hcombo_eval_ne
  have hineq : A < β * B := by
    dsimp [A, B, pp, qx, qp, qq]
    have hineq' := hineq_raw
    simp [hp_eval0, hp_der_eval0, derivative_add] at hineq'
    nlinarith [hβ_pos]
  have hβB_lt : β * |B| < A := by
    calc
      β * |B| ≤ β * (|B| + 1) := by simp_all
      _ ≤ δ₁ * (|B| + 1) := by gcongr
      _ = A / 2 := by grind
      _ < A := by grind
  have hineq_le : β * B ≤ β * |B| := by
    have hB_le : B ≤ |B| := le_abs_self B
    simp_all
  grind

/-- Affine-family endpoint obstruction for an exact double root of `g`.

At a negative root `r`, the affine family contains the one-parameter right
families
`g + β * ((X - C r + C c) * f)` for every fixed `c > r`.  Choosing `c` so that
`c * g''(r) * f(r) > 0`, the bounded right-family double-root obstruction above
rules out an exact double root of `g` at `r` whenever `f(r) ≠ 0`. -/
private lemma false_of_affine_family_double_root
    {f g : ℝ[X]} {r : ℝ}
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hr_neg : r < 0)
    (hg_mult : g.rootMultiplicity r = 2)
    (hf_eval_ne : f.eval r ≠ 0) :
    False := by
  have hg0 : g ≠ 0 := by
    intro hg0
    simp [hg0] at hg_mult
  let G : ℝ := g.derivative.derivative.eval r * f.eval r
  have hG_ne : G ≠ 0 := by
    dsimp [G]
    exact mul_ne_zero
      (eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two hg0 hg_mult)
      hf_eval_ne
  by_cases hG_pos : 0 < G
  · let q : ℝ[X] := (X - C r + C (1 : ℝ)) * f
    have hfamily :
        ∀ {β : ℝ}, 0 < β → β ≤ 1 →
          ((g + C β * q) ≠ 0 ∧ (g + C β * q).Splits) := by
      intro β hβ
      have hEq :
          g + C β * q =
            (((C β * X + C (β * (1 - r))) * f) + g) := by
        grind
      have hβt_pos : 0 < β * (1 - r) := by
        have : 0 < 1 - r := by linarith
        positivity
      grind
    have hq_eval_ne : q.eval r ≠ 0 := by
      dsimp [q]
      simp_all
    have hprod_pos :
        0 < g.derivative.derivative.eval r * q.eval r := by
      dsimp [q, G] at hG_pos ⊢
      simp_all
    exact
      false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
        (p := g) (q := q) (x := r) (βmax := 1)
        hfamily zero_lt_one hg_mult hq_eval_ne hprod_pos
  · let c : ℝ := r / 2
    let q : ℝ[X] := (X - C r + C c) * f
    have hc_gt_r : r < c := by grind
    have hc_neg : c < 0 := by grind
    have hfamily :
        ∀ {β : ℝ}, 0 < β → β ≤ 1 →
          ((g + C β * q) ≠ 0 ∧ (g + C β * q).Splits) := by
      intro β hβ
      have hEq :
          g + C β * q =
            (((C β * X + C (β * (c - r))) * f) + g) := by
        grind
      have hβt_pos : 0 < β * (c - r) := by simp_all
      grind
    have hq_eval_ne : q.eval r ≠ 0 := by
      dsimp [q, c]
      rw [eval_mul]
      have hlin : (X - C r + C (r / 2)).eval r = r / 2 := by simp
      grind
    have hG_neg :
        G < 0 := by
      grind
    have hprod_pos :
        0 < g.derivative.derivative.eval r * q.eval r := by
      have hcG_pos : 0 < c * G := by
        dsimp [c, G]
        nlinarith [hr_neg, hG_neg]
      dsimp [q, c]
      rw [eval_mul]
      have hlin : (X - C r + C (r / 2)).eval r = r / 2 := by simp
      grind
    exact
      false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
        (p := g) (q := q) (x := r) (βmax := 1)
        hfamily zero_lt_one hg_mult hq_eval_ne hprod_pos

/-- In the succ-degree affine branch with `g(0) ≠ 0`, the endpoint polynomial
`g` itself has simple roots.

The proof is the endpoint analogue of the interior `iterateTDeriv` shortening
argument used below. If `g` had a multiple root at `r < 0`, we shorten its
multiplicity to an exact double root by a small `iterateTDeriv` run, while
keeping two affine companion families nonvanishing at `r`:
`(X - C r + 1) * f` and `(X - C r + C (r/2)) * f`. Their evaluations at `r`
have opposite signs, so after regularization one of them has the same sign as
the second derivative of the shortened endpoint, and the bounded affine-family
double-root obstruction applies. -/
protected lemma AffineFamily.hasSimpleRoots_right_of_affine_family_succDegree_not_isRoot_zero
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg_root0 : ¬ g.IsRoot 0) :
    HasSimpleRoots g := by
  have hg_rr : (g ≠ 0 ∧ g.Splits) :=
    AffineFamily.isRealRooted_right_of_affine_family_succDegree hf0 hg0 hfnn hgnn haff hsucc.symm
  have hno_right :
      ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r :=
    no_common_right_pair_of_no_common_of_not_isRoot_zero hno hg_root0
  intro r hgr
  by_contra hmult_ne
  have hmult_pos : 0 < g.rootMultiplicity r := by simp_all
  have hmult_ge2 : 2 ≤ g.rootMultiplicity r := by lia
  have hr_mem : r ∈ g.roots := (mem_roots hg_rr.1).mpr hgr
  have hr_neg : r < 0 :=
    roots_strictly_neg_of_nonneg_of_no_common_right_pair
      hg_rr.1 hg_rr.2 hgnn hno_right r hr_mem
  have hf_not_root : ¬ f.IsRoot r := hno r hgr
  have hf_eval_ne : f.eval r ≠ 0 := by simp_all
  let m : ℕ := g.rootMultiplicity r
  let k : ℕ := m - 2
  let qPos : ℝ[X] := (X - C r + C (1 : ℝ)) * f
  let qNeg : ℝ[X] := (X - C r + C (r / 2)) * f
  have hqPos_eval : qPos.eval r = f.eval r := by
    dsimp [qPos]
    simp
  have hqNeg_eval : qNeg.eval r = (r / 2) * f.eval r := by
    dsimp [qNeg]
    simp
  have hqPos_eval_ne : qPos.eval r ≠ 0 := by lia
  have hqNeg_eval_ne : qNeg.eval r ≠ 0 := by simp_all
  obtain ⟨δPos, hδPos, hqPos_keep⟩ :=
    exists_delta_eval_mul_pos_iterateTDeriv_at_zero k
      (p := qPos) (x := r) hqPos_eval_ne
  obtain ⟨δNeg, hδNeg, hqNeg_keep⟩ :=
    exists_delta_eval_mul_pos_iterateTDeriv_at_zero k
      (p := qNeg) (x := r) hqNeg_eval_ne
  let η : ℝ := min δPos δNeg / 2
  have hη_pos : 0 < η := by exact half_pos (lt_min_iff.mpr ⟨hδPos, hδNeg⟩)
  have hη_smallPos : ‖η‖ < δPos := by
    have hη_norm : ‖η‖ = min δPos δNeg / 2 := by
      rw [Real.norm_eq_abs, show η = min δPos δNeg / 2 by rfl, abs_of_pos hη_pos]
    have hmin : min δPos δNeg ≤ δPos := min_le_left _ _
    linarith
  have hη_smallNeg : ‖η‖ < δNeg := by
    have hη_norm : ‖η‖ = min δPos δNeg / 2 := by
      rw [Real.norm_eq_abs, show η = min δPos δNeg / 2 by rfl, abs_of_pos hη_pos]
    have hmin : min δPos δNeg ≤ δNeg := min_le_right _ _
    linarith
  let pη : ℝ[X] := iterateTDeriv η k g
  let qPosη : ℝ[X] := iterateTDeriv η k qPos
  let qNegη : ℝ[X] := iterateTDeriv η k qNeg
  have hk_le : k ≤ g.rootMultiplicity r := by lia
  have hpη_mult : pη.rootMultiplicity r = 2 := by
    calc
      pη.rootMultiplicity r = g.rootMultiplicity r - k := by
        dsimp [pη]
        exact rootMultiplicity_iterateTDeriv_eq_tsub hη_pos hg_rr.1 hg_rr.2 hk_le
      _ = 2 := by lia
  have hpη_rr : (pη ≠ 0 ∧ pη.Splits) := by
    dsimp [pη]
    exact ⟨iterateTDeriv_ne_zero hg_rr.1, splits_iterateTDeriv hη_pos hg_rr.2⟩
  have hpη_ne : pη ≠ 0 := hpη_rr.1
  have hpp_ne : pη.derivative.derivative.eval r ≠ 0 :=
    eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two
      hpη_ne hpη_mult
  have hqPosη_keep : 0 < qPosη.eval r * qPos.eval r := hqPos_keep hη_smallPos
  have hqNegη_keep : 0 < qNegη.eval r * qNeg.eval r := hqNeg_keep hη_smallNeg
  have hqPosη_eval_ne : qPosη.eval r ≠ 0 := by
    intro h
    rw [h, zero_mul] at hqPosη_keep
    linarith
  have hqNegη_eval_ne : qNegη.eval r ≠ 0 := by
    intro h
    rw [h, zero_mul] at hqNegη_keep
    linarith
  have hqOpp :
      qPosη.eval r * qNegη.eval r < 0 := by
    by_cases hqPos_pos : 0 < qPos.eval r
    · have hqPosη_pos : 0 < qPosη.eval r := by simp_all
      have hqNeg_neg : qNeg.eval r < 0 := by
        rw [hqNeg_eval, hqPos_eval] at *
        nlinarith [hr_neg, hqPos_pos]
      have hqNegη_neg : qNegη.eval r < 0 := by nlinarith [hqNegη_keep, hqNeg_neg]
      exact mul_neg_of_pos_of_neg hqPosη_pos hqNegη_neg
    · have hqPos_neg : qPos.eval r < 0 :=
        lt_of_le_of_ne (le_of_not_gt hqPos_pos) hqPos_eval_ne
      have hqPosη_neg : qPosη.eval r < 0 := by nlinarith [hqPosη_keep, hqPos_neg]
      have hqNeg_pos : 0 < qNeg.eval r := by
        rw [hqNeg_eval, hqPos_eval] at *
        nlinarith [hr_neg, hqPos_neg]
      have hqNegη_pos : 0 < qNegη.eval r := by simp_all
      exact mul_neg_of_neg_of_pos hqPosη_neg hqNegη_pos
  have hfamilyPos :
      ∀ {β : ℝ}, 0 < β → β ≤ 1 →
        ((g + C β * qPos) ≠ 0 ∧ (g + C β * qPos).Splits) := by
    intro β hβ _
    have hfac : C β * (X - C r + C (1 : ℝ)) = C β * X + C (β * (1 - r)) := by
      simp only [map_sub, map_mul, Polynomial.C_1]
      ring
    have hEq :
        g + C β * qPos =
          (((C β * X + C (β * (1 - r))) * f) + g) := by
      dsimp [qPos]
      rw [← mul_assoc, hfac]
      ring
    have hβt_pos : 0 < β * (1 - r) := by
      have : 0 < 1 - r := by linarith
      positivity
    rw [hEq]
    exact haff hβ hβt_pos
  have hfamilyNeg :
      ∀ {β : ℝ}, 0 < β → β ≤ 1 →
        ((g + C β * qNeg) ≠ 0 ∧ (g + C β * qNeg).Splits) := by
    intro β hβ _
    have hfac : C β * (X - C r + C (r / 2)) = C β * X + C (β * (r / 2 - r)) := by
      simp only [map_sub, map_mul]
      ring
    have hEq :
        g + C β * qNeg =
          (((C β * X + C (β * (r / 2 - r))) * f) + g) := by
      dsimp [qNeg]
      rw [← mul_assoc, hfac]
      ring
    have hβt_pos : 0 < β * (r / 2 - r) := by
      have : 0 < r / 2 - r := by linarith
      positivity
    rw [hEq]
    exact haff hβ hβt_pos
  have hfamilyPosη :
      ∀ {β : ℝ}, 0 < β → β ≤ 1 →
        ((pη + C β * qPosη) ≠ 0 ∧ (pη + C β * qPosη).Splits) := by
    intro β hβ hβ_le
    have hrr : ((g + C β * qPos) ≠ 0 ∧ (g + C β * qPos).Splits) := hfamilyPos hβ hβ_le
    have hiter :
        ((iterateTDeriv η k (g + C β * qPos)) ≠ 0 ∧
          (iterateTDeriv η k (g + C β * qPos)).Splits) :=
      ⟨iterateTDeriv_ne_zero hrr.1, splits_iterateTDeriv hη_pos hrr.2⟩
    have hEq :
        pη + C β * qPosη = iterateTDeriv η k (g + C β * qPos) := by
      dsimp [pη, qPosη]
      rw [iterateTDeriv_add, iterateTDeriv_C_mul]
    lia
  have hfamilyNegη :
      ∀ {β : ℝ}, 0 < β → β ≤ 1 →
        ((pη + C β * qNegη) ≠ 0 ∧ (pη + C β * qNegη).Splits) := by
    intro β hβ hβ_le
    have hrr : ((g + C β * qNeg) ≠ 0 ∧ (g + C β * qNeg).Splits) := hfamilyNeg hβ hβ_le
    have hiter :
        ((iterateTDeriv η k (g + C β * qNeg)) ≠ 0 ∧
          (iterateTDeriv η k (g + C β * qNeg)).Splits) :=
      ⟨iterateTDeriv_ne_zero hrr.1, splits_iterateTDeriv hη_pos hrr.2⟩
    have hEq :
        pη + C β * qNegη = iterateTDeriv η k (g + C β * qNeg) := by
      dsimp [pη, qNegη]
      rw [iterateTDeriv_add, iterateTDeriv_C_mul]
    lia
  by_cases hprodPos :
      0 < pη.derivative.derivative.eval r * qPosη.eval r
  · exact
      false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
        (p := pη) (q := qPosη) (x := r) (βmax := 1)
        hfamilyPosη zero_lt_one hpη_mult hqPosη_eval_ne hprodPos
  · have hprodPos_ne :
      pη.derivative.derivative.eval r * qPosη.eval r ≠ 0 :=
      mul_ne_zero hpp_ne hqPosη_eval_ne
    have hprodPos_neg :
        pη.derivative.derivative.eval r * qPosη.eval r < 0 :=
      lt_of_le_of_ne (le_of_not_gt hprodPos) hprodPos_ne
    by_cases hqPosη_pos : 0 < qPosη.eval r
    · have hqNegη_neg : qNegη.eval r < 0 := by
        have hqNegη_ne : qNegη.eval r ≠ 0 := hqNegη_eval_ne
        have hqNegη_not_pos : ¬ 0 < qNegη.eval r :=
          fun hqNegη_pos =>
            (not_lt_of_ge (le_of_lt hqOpp)) (mul_pos hqPosη_pos hqNegη_pos)
        exact lt_of_le_of_ne (le_of_not_gt hqNegη_not_pos) hqNegη_ne
      have hpp_neg : pη.derivative.derivative.eval r < 0 :=
        (neg_iff_pos_of_mul_neg hprodPos_neg).mpr hqPosη_pos
      have hprodNeg_pos :
          0 < pη.derivative.derivative.eval r * qNegη.eval r :=
        mul_pos_of_neg_of_neg hpp_neg hqNegη_neg
      exact
        false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
          (p := pη) (q := qNegη) (x := r) (βmax := 1)
          hfamilyNegη zero_lt_one hpη_mult hqNegη_eval_ne hprodNeg_pos
    · have hqPosη_neg : qPosη.eval r < 0 :=
        lt_of_le_of_ne (le_of_not_gt hqPosη_pos) hqPosη_eval_ne
      have hqNegη_pos : 0 < qNegη.eval r := by
        have hqNegη_ne : qNegη.eval r ≠ 0 := hqNegη_eval_ne
        have hqNegη_not_neg : ¬ qNegη.eval r < 0 :=
          fun hqNegη_neg =>
            (not_lt_of_ge (le_of_lt hqOpp)) (mul_pos_of_neg_of_neg hqPosη_neg hqNegη_neg)
        exact lt_of_le_of_ne (le_of_not_gt hqNegη_not_neg) hqNegη_ne.symm
      have hpp_pos : 0 < pη.derivative.derivative.eval r :=
        (pos_iff_neg_of_mul_neg hprodPos_neg).mpr hqPosη_neg
      have hprodNeg_pos :
          0 < pη.derivative.derivative.eval r * qNegη.eval r := by
        simp_all
      exact
        false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
          (p := pη) (q := qNegη) (x := r) (βmax := 1)
          hfamilyNegη zero_lt_one hpη_mult hqNegη_eval_ne hprodNeg_pos

/-- Exact double roots are impossible in interior positive combinations of a
positive-combination real-rooted family. This is the local obstruction that the
affine-family frontier can use without leaving the positive cone. -/
private lemma rootMultiplicity_ne_two_add_right_of_posComboRealRooted
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {μ x : ℝ}
    (hμ : 0 < μ) :
    (f + C μ * g).rootMultiplicity x ≠ 2 := by
  intro hmult
  have hp_root : (f + C μ * g).IsRoot x :=
    (rootMultiplicity_pos (show f + C μ * g ≠ 0 from
      (PosComboRealRooted.isRealRooted_add_right hfg hμ).1)).mp (by lia)
  have hg_eval_ne : g.eval x ≠ 0 := fun hg0 => by simp_all
  by_cases hprod_pos :
      0 < (f + C μ * g).derivative.derivative.eval x * g.eval x
  · exact
      false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
        (p := f + C μ * g) (q := g) (x := x) (βmax := 1)
        (by
          intro β hβ hβ_le
          have hμβ : 0 < μ + β := by linarith
          have hrr := PosComboRealRooted.isRealRooted_add_right hfg hμβ
          grind)
        zero_lt_one hmult hg_eval_ne hprod_pos
  · have hpp_ne :
        (f + C μ * g).derivative.derivative.eval x ≠ 0 :=
      eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two
        (show f + C μ * g ≠ 0 from (PosComboRealRooted.isRealRooted_add_right hfg hμ).1)
        hmult
    have hprod_ne :
        (f + C μ * g).derivative.derivative.eval x * g.eval x ≠ 0 :=
      mul_ne_zero hpp_ne hg_eval_ne
    have hprod_neg :
        (f + C μ * g).derivative.derivative.eval x * g.eval x < 0 := by
      grind
    have hneg_eval_ne : (-g).eval x ≠ 0 := by simp_all
    have hneg_pos :
        0 < (f + C μ * g).derivative.derivative.eval x * (-g).eval x := by
      simp_all
    exact
      false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
        (p := f + C μ * g) (q := -g) (x := x) (βmax := μ / 2)
        (by
          intro β hβ hβ_le
          have hμβ : 0 < μ - β := by linarith
          have hrr := PosComboRealRooted.isRealRooted_add_right hfg hμβ
          grind)
        (by grind) hmult hneg_eval_ne hneg_pos

/-- Every interior positive combination of a no-common positive-combination
family has simple roots.

This is the exact `iterateTDeriv`-shortening step from the completed
Obreschkoff converse, specialized to the positive cone: if
`p = f + C μ * g` had a multiple root at `x`, keep `g` nonvanishing at `x`
along a short `iterateTDeriv` run, shorten the multiplicity of `p` until it
becomes exactly `2`, and then contradict the exact-double-root obstruction
above. -/
private lemma hasSimpleRoots_add_right_of_posComboRealRooted
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {μ : ℝ}
    (hμ : 0 < μ) :
    HasSimpleRoots (f + C μ * g) := by
  let p : ℝ[X] := f + C μ * g
  have hp_rr : (p ≠ 0 ∧
    p.Splits) := PosComboRealRooted.isRealRooted_add_right hfg hμ
  have hp_ne : p ≠ 0 := hp_rr.1
  intro x hx
  by_contra hmult_ne
  have hmult_pos : 0 < p.rootMultiplicity x :=
    (rootMultiplicity_pos hp_ne).mpr (by lia)
  have hmult_gt : 1 < p.rootMultiplicity x := by lia
  have hg_not_root : ¬ g.IsRoot x := fun hgx => by simp_all
  let m : ℕ := p.rootMultiplicity x
  let k : ℕ := m - 2
  obtain ⟨δ, hδ, hgk_not_root⟩ :=
    exists_delta_not_isRoot_iterateTDeriv_at_point k hg_not_root
  let η : ℝ := δ / 2
  have hη_pos : 0 < η := by grind
  have hη_small : ‖η‖ < δ := by
    have hη_norm : ‖η‖ = δ / 2 := by
      rw [Real.norm_eq_abs, show η = δ / 2 by lia, abs_of_pos hη_pos]
    simp_all
  have hgk_not_root_x : ¬ (iterateTDeriv η k g).IsRoot x := hgk_not_root hη_small
  have hgk_eval_ne : (iterateTDeriv η k g).eval x ≠ 0 := by simp_all
  have hk_le : k ≤ p.rootMultiplicity x := by lia
  have hpk_mult :
      (iterateTDeriv η k p).rootMultiplicity x = 2 := by
    calc
      (iterateTDeriv η k p).rootMultiplicity x = p.rootMultiplicity x - k :=
        rootMultiplicity_iterateTDeriv_eq_tsub hη_pos hp_rr.1 hp_rr.2 hk_le
      _ = 2 := by lia
  let pη : ℝ[X] := iterateTDeriv η k p
  let gη : ℝ[X] := iterateTDeriv η k g
  have hpη_eq :
      pη = iterateTDeriv η k f + C μ * gη := by
    dsimp [pη, p, gη]
    rw [iterateTDeriv_add, iterateTDeriv_C_mul]
  by_cases hprod_pos :
      0 < pη.derivative.derivative.eval x * gη.eval x
  · exact
      false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
        (p := pη) (q := gη) (x := x) (βmax := 1)
        (by
          intro β hβ
          have hμβ : 0 < μ + β := by linarith
          have hrr := PosComboRealRooted.isRealRooted_add_right hfg hμβ
          have hiter :
              ((iterateTDeriv η k (f + C (μ + β) * g)) ≠ 0 ∧
                (iterateTDeriv η k (f + C (μ + β) * g)).Splits) :=
            ⟨iterateTDeriv_ne_zero hrr.1,
              splits_iterateTDeriv (eps := η) (k := k) hη_pos hrr.2⟩
          have hEq : pη + C β * gη = iterateTDeriv η k (f + C (μ + β) * g) := by
            calc
              pη + C β * gη
                  = (iterateTDeriv η k f + C μ * gη) + C β * gη := by lia
              _ = iterateTDeriv η k f + (C μ * gη + C β * gη) := by grind
              _ = iterateTDeriv η k f + (C μ + C β) * gη := by grind
              _ = iterateTDeriv η k f + C (μ + β) * gη := by simp
              _ = iterateTDeriv η k (f + C (μ + β) * g) := by
                    rw [iterateTDeriv_add, iterateTDeriv_C_mul]
          lia)
        zero_lt_one hpk_mult hgk_eval_ne hprod_pos
  · have hpη_rr : (pη ≠ 0 ∧ pη.Splits) :=
      ⟨iterateTDeriv_ne_zero hp_rr.1,
        splits_iterateTDeriv (eps := η) (k := k) hη_pos hp_rr.2⟩
    have hpη_ne : pη ≠ 0 := hpη_rr.1
    have hpηpp_ne :
        pη.derivative.derivative.eval x ≠ 0 :=
      eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two hpη_ne hpk_mult
    have hprod_ne :
        pη.derivative.derivative.eval x * gη.eval x ≠ 0 :=
      mul_ne_zero hpηpp_ne hgk_eval_ne
    have hprod_neg :
        pη.derivative.derivative.eval x * gη.eval x < 0 := by
      grind
    have hneg_eval_ne : (-gη).eval x ≠ 0 := by simp_all
    have hneg_pos :
        0 < pη.derivative.derivative.eval x * (-gη).eval x := by
      simp_all
    exact
      false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
        (p := pη) (q := -gη) (x := x) (βmax := μ / 2)
        (by
          intro β hβ hβ_le
          have hμβ : 0 < μ - β := by linarith
          have hrr := PosComboRealRooted.isRealRooted_add_right hfg hμβ
          have hiter :
              ((iterateTDeriv η k (f + C (μ - β) * g)) ≠ 0 ∧
                (iterateTDeriv η k (f + C (μ - β) * g)).Splits) :=
            ⟨iterateTDeriv_ne_zero hrr.1,
              splits_iterateTDeriv (eps := η) (k := k) hη_pos hrr.2⟩
          have hEq : pη + C β * (-gη) = iterateTDeriv η k (f + C (μ - β) * g) := by
            calc
              pη + C β * (-gη)
                  = (iterateTDeriv η k f + C μ * gη) + C β * (-gη) := by lia
              _ = iterateTDeriv η k f + (C μ * gη + C β * (-gη)) := by grind
              _ = iterateTDeriv η k f + (C μ * gη - C β * gη) := by grind
              _ = iterateTDeriv η k f + (C μ - C β) * gη := by grind
              _ = iterateTDeriv η k f + C (μ - β) * gη := by simp
              _ = iterateTDeriv η k (f + C (μ - β) * g) := by
                    rw [iterateTDeriv_add, iterateTDeriv_C_mul]
          lia)
        (by grind) hpk_mult hneg_eval_ne hneg_pos

/-- Every interior positive combination of a no-common positive-combination
family has simple roots. -/
theorem PosComboRealRooted.hasSimpleRoots_add_right
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {μ : ℝ}
    (hμ : 0 < μ) :
    HasSimpleRoots (f + C μ * g) :=
  hasSimpleRoots_add_right_of_posComboRealRooted hfg hno hμ

/-- Left-family form of `PosComboRealRooted.hasSimpleRoots_add_right`. -/
theorem PosComboRealRooted.hasSimpleRoots_add_left
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {lam : ℝ}
    (hlam : 0 < lam) :
    HasSimpleRoots (C lam * f + g) := by
  have hno' : ∀ r, g.IsRoot r → ¬ f.IsRoot r := by
    intro r hg hf
    exact hno r hf hg
  simpa [add_comm] using
    PosComboRealRooted.hasSimpleRoots_add_right
      (f := g) (g := f) (PosComboRealRooted.comm hfg) hno' hlam

/-- For a fixed point where `g` does not vanish, the right pencil
`f + C mu * g` has a root at that point for exactly one parameter. -/
theorem isRoot_add_right_iff_parameter_eq
    {f g : ℝ[X]} {mu x : ℝ} (hgx : g.eval x ≠ 0) :
    (f + C mu * g).IsRoot x ↔ mu = -f.eval x / g.eval x := by
  rw [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C]
  constructor
  · intro hroot
    have hmul : mu * g.eval x = -f.eval x := by linarith
    calc
      mu = (mu * g.eval x) / g.eval x := by field_simp [hgx]
      _ = -f.eval x / g.eval x := by rw [hmul]
  · intro hmu
    rw [hmu]
    field_simp [hgx]
    ring

/-- Left-family form of `isRoot_add_right_iff_parameter_eq`. -/
theorem isRoot_add_left_iff_parameter_eq
    {f g : ℝ[X]} {lam x : ℝ} (hfx : f.eval x ≠ 0) :
    (C lam * f + g).IsRoot x ↔ lam = -g.eval x / f.eval x := by
  simpa [add_comm] using
    isRoot_add_right_iff_parameter_eq (f := g) (g := f) (mu := lam) (x := x) hfx

/-- A fixed point `x` is hit by the right pencil `f + C μ * g` for some
positive parameter exactly when the endpoint evaluations have opposite signs. -/
theorem exists_pos_isRoot_add_right_iff_eval_mul_neg
    {f g : ℝ[X]} {x : ℝ} (hfx : f.eval x ≠ 0) :
    (∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) ↔ f.eval x * g.eval x < 0 := by
  constructor
  · rintro ⟨μ, hμ, hroot⟩
    have hroot_eval : f.eval x + μ * g.eval x = 0 := by
      simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C] using hroot
    have hgx : g.eval x ≠ 0 := by
      intro hgx
      rw [hgx, mul_zero, add_zero] at hroot_eval
      exact hfx hroot_eval
    have hsquare : 0 < g.eval x * g.eval x := mul_self_pos.mpr hgx
    have hf_eq : f.eval x = -μ * g.eval x := by linarith
    rw [hf_eq]
    nlinarith
  · intro hmul
    have hgx : g.eval x ≠ 0 := by
      intro hgx
      rw [hgx, mul_zero] at hmul
      linarith
    refine ⟨-f.eval x / g.eval x, ?_, ?_⟩
    · have hsquare : 0 < g.eval x * g.eval x := mul_self_pos.mpr hgx
      have hrewrite :
          -f.eval x / g.eval x = -(f.eval x * g.eval x) / (g.eval x * g.eval x) := by
        field_simp [hgx]
      rw [hrewrite]
      exact div_pos (by linarith) hsquare
    · exact (isRoot_add_right_iff_parameter_eq (f := f) (g := g) (x := x) hgx).mpr rfl

/-- Left-family form of `exists_pos_isRoot_add_right_iff_eval_mul_neg`. -/
theorem exists_pos_isRoot_add_left_iff_eval_mul_neg
    {f g : ℝ[X]} {x : ℝ} (hgx : g.eval x ≠ 0) :
    (∃ lam : ℝ, 0 < lam ∧ (C lam * f + g).IsRoot x) ↔ f.eval x * g.eval x < 0 := by
  simpa [add_comm, mul_comm] using
    exists_pos_isRoot_add_right_iff_eval_mul_neg (f := g) (g := f) (x := x) hgx

/-- If no positive right-pencil member vanishes at `x`, then the endpoint
evaluations have the same sign. -/
theorem eval_pos_iff_of_not_exists_pos_isRoot_add_right
    {f g : ℝ[X]} {x : ℝ} (hfx : f.eval x ≠ 0) (hgx : g.eval x ≠ 0)
    (hno : ¬ ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :
    (0 < f.eval x ↔ 0 < g.eval x) := by
  have hnot_mul : ¬ f.eval x * g.eval x < 0 := by
    intro hmul
    exact hno ((exists_pos_isRoot_add_right_iff_eval_mul_neg hfx).mpr hmul)
  constructor
  · intro hfpos
    by_contra hnot
    have hgneg : g.eval x < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hgx
    exact hnot_mul (by nlinarith)
  · intro hgpos
    by_contra hnot
    have hfneg : f.eval x < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hfx
    exact hnot_mul (by nlinarith)

/-- Same-sign endpoint evaluations rule out positive right-pencil roots at the
fixed point. -/
theorem not_exists_pos_isRoot_add_right_of_eval_pos_iff
    {f g : ℝ[X]} {x : ℝ} (hfx : f.eval x ≠ 0)
    (hsign : (0 < f.eval x ↔ 0 < g.eval x)) :
    ¬ ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x := by
  rw [exists_pos_isRoot_add_right_iff_eval_mul_neg hfx]
  intro hmul
  rcases lt_or_gt_of_ne hfx with hfneg | hfpos
  · have hgpos : 0 < g.eval x := by nlinarith
    have hfpos' : 0 < f.eval x := hsign.mpr hgpos
    linarith
  · have hgneg : g.eval x < 0 := by nlinarith
    have hgpos : 0 < g.eval x := hsign.mp hfpos
    linarith

/-- Absence of a positive right-pencil root at `x` is equivalent to same-sign
endpoint evaluations, provided neither endpoint vanishes at `x`. -/
theorem not_exists_pos_isRoot_add_right_iff_eval_pos_iff
    {f g : ℝ[X]} {x : ℝ} (hfx : f.eval x ≠ 0) (hgx : g.eval x ≠ 0) :
    (¬ ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) ↔
      (0 < f.eval x ↔ 0 < g.eval x) :=
  ⟨eval_pos_iff_of_not_exists_pos_isRoot_add_right hfx hgx,
    not_exists_pos_isRoot_add_right_of_eval_pos_iff hfx⟩

/-- Under a no-common-root hypothesis, a root of `f` is not a zero of `g`. -/
theorem eval_right_ne_zero_of_isRoot_of_no_common
    {f g : ℝ[X]} {x : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfx : f.IsRoot x) :
    g.eval x ≠ 0 := by
  intro hgx
  exact hno x hfx (by simpa [Polynomial.IsRoot.def] using hgx)

/-- Symmetric endpoint-evaluation form of
`eval_right_ne_zero_of_isRoot_of_no_common`. -/
theorem eval_left_ne_zero_of_isRoot_of_no_common
    {f g : ℝ[X]} {x : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hgx : g.IsRoot x) :
    f.eval x ≠ 0 := by
  intro hfx
  exact hno x (by simpa [Polynomial.IsRoot.def] using hfx) hgx

/-- At a root of a no-common right pencil, the right endpoint does not vanish. -/
theorem eval_right_ne_zero_of_isRoot_add_right_of_no_common
    {f g : ℝ[X]} {mu x : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hroot : (f + C mu * g).IsRoot x) :
    g.eval x ≠ 0 := by
  intro hgx
  have hroot_eval : f.eval x + mu * g.eval x = 0 := by
    simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C] using hroot
  have hfx : f.IsRoot x := by
    have hfx_eval : f.eval x = 0 := by
      rw [hgx, mul_zero, add_zero] at hroot_eval
      exact hroot_eval
    simpa [Polynomial.IsRoot.def] using hfx_eval
  exact hno x hfx (by simpa [Polynomial.IsRoot.def] using hgx)

/-- At a root of an interior no-common right pencil, the left endpoint does not
vanish. -/
theorem eval_left_ne_zero_of_isRoot_add_right_of_no_common
    {f g : ℝ[X]} {mu x : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hmu : 0 < mu)
    (hroot : (f + C mu * g).IsRoot x) :
    f.eval x ≠ 0 := by
  intro hfx
  have hroot_eval : f.eval x + mu * g.eval x = 0 := by
    simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C] using hroot
  have hgx_eval : g.eval x = 0 := by
    have hmul : mu * g.eval x = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left hmu.ne'
  exact hno x (by simpa [Polynomial.IsRoot.def] using hfx)
    (by simpa [Polynomial.IsRoot.def] using hgx_eval)

/-- At a root of a no-common left pencil, the left endpoint does not vanish. -/
theorem eval_left_ne_zero_of_isRoot_add_left_of_no_common
    {f g : ℝ[X]} {lam x : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hroot : (C lam * f + g).IsRoot x) :
    f.eval x ≠ 0 := by
  simpa [add_comm] using
    eval_right_ne_zero_of_isRoot_add_right_of_no_common
      (f := g) (g := f) (mu := lam) (x := x)
      (fun r hg hf => hno r hf hg) (by simpa [add_comm] using hroot)

/-- At a root of an interior no-common left pencil, the right endpoint does not
vanish. -/
theorem eval_right_ne_zero_of_isRoot_add_left_of_no_common
    {f g : ℝ[X]} {lam x : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hlam : 0 < lam)
    (hroot : (C lam * f + g).IsRoot x) :
    g.eval x ≠ 0 := by
  simpa [add_comm] using
    eval_left_ne_zero_of_isRoot_add_right_of_no_common
      (f := g) (g := f) (mu := lam) (x := x)
      (fun r hg hf => hno r hf hg) hlam (by simpa [add_comm] using hroot)

/-- Positive-parameter no-common form of
`isRoot_add_right_iff_parameter_eq`, with the endpoint nonvanishing inferred
from the root/no-common hypotheses on the forward implication and from
positivity on the reverse implication. -/
theorem isRoot_add_right_iff_parameter_eq_of_no_common
    {f g : ℝ[X]} {mu x : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hmu : 0 < mu) :
    (f + C mu * g).IsRoot x ↔ mu = -f.eval x / g.eval x := by
  constructor
  · intro hroot
    exact
      (isRoot_add_right_iff_parameter_eq
        (eval_right_ne_zero_of_isRoot_add_right_of_no_common hno hroot)).mp hroot
  · intro hmu_eq
    have hgx : g.eval x ≠ 0 := by
      intro hgx
      have hmu0 : mu = 0 := by simpa [hgx] using hmu_eq
      exact hmu.ne' hmu0
    exact (isRoot_add_right_iff_parameter_eq hgx).mpr hmu_eq

/-- Left-family form of
`isRoot_add_right_iff_parameter_eq_of_no_common`. -/
theorem isRoot_add_left_iff_parameter_eq_of_no_common
    {f g : ℝ[X]} {lam x : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hlam : 0 < lam) :
    (C lam * f + g).IsRoot x ↔ lam = -g.eval x / f.eval x := by
  constructor
  · intro hroot
    exact
      (isRoot_add_left_iff_parameter_eq
        (eval_left_ne_zero_of_isRoot_add_left_of_no_common hno hroot)).mp hroot
  · intro hlam_eq
    have hfx : f.eval x ≠ 0 := by
      intro hfx
      have hlam0 : lam = 0 := by simpa [hfx] using hlam_eq
      exact hlam.ne' hlam0
    exact (isRoot_add_left_iff_parameter_eq hfx).mpr hlam_eq

/-- A fixed threshold can be a root of a no-common right pencil for at most one
parameter. -/
theorem pencil_parameter_unique_of_isRoot_of_no_common
    {f g : ℝ[X]} (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {mu1 mu2 x : ℝ}
    (h1 : (f + C mu1 * g).IsRoot x)
    (h2 : (f + C mu2 * g).IsRoot x) :
    mu1 = mu2 := by
  have hgx : g.eval x ≠ 0 :=
    eval_right_ne_zero_of_isRoot_add_right_of_no_common hno h1
  have hmu1 : mu1 = -f.eval x / g.eval x :=
    (isRoot_add_right_iff_parameter_eq hgx).mp h1
  have hmu2 : mu2 = -f.eval x / g.eval x :=
    (isRoot_add_right_iff_parameter_eq hgx).mp h2
  exact hmu1.trans hmu2.symm

/-- Left-family form of `pencil_parameter_unique_of_isRoot_of_no_common`. -/
theorem pencil_parameter_unique_left_of_isRoot_of_no_common
    {f g : ℝ[X]} (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {lam eta x : ℝ}
    (h1 : (C lam * f + g).IsRoot x)
    (h2 : (C eta * f + g).IsRoot x) :
    lam = eta :=
  pencil_parameter_unique_of_isRoot_of_no_common
    (f := g) (g := f) (mu1 := lam) (mu2 := eta) (x := x)
    (fun r hg hf => hno r hf hg) (by simpa [add_comm] using h1)
    (by simpa [add_comm] using h2)

/-- A fixed threshold can be a root of a no-common right pencil for at most one
positive parameter. -/
theorem root_parameter_unique_add_right_of_no_common
    {f g : ℝ[X]} {mu nu x : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (_hmu : 0 < mu) (_hnu : 0 < nu)
    (hroot_mu : (f + C mu * g).IsRoot x)
    (hroot_nu : (f + C nu * g).IsRoot x) :
    mu = nu :=
  pencil_parameter_unique_of_isRoot_of_no_common hno hroot_mu hroot_nu

/-- Left-family form of `root_parameter_unique_add_right_of_no_common`. -/
theorem root_parameter_unique_add_left_of_no_common
    {f g : ℝ[X]} {lam eta x : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (_hlam : 0 < lam) (_heta : 0 < eta)
    (hroot_lam : (C lam * f + g).IsRoot x)
    (hroot_eta : (C eta * f + g).IsRoot x) :
    lam = eta :=
  pencil_parameter_unique_left_of_isRoot_of_no_common hno hroot_lam hroot_eta

/-- At a root of an interior right positive combination, the derivative does
not vanish. -/
theorem PosComboRealRooted.derivative_eval_ne_zero_add_right
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {mu x : ℝ}
    (hmu : 0 < mu)
    (hroot : (f + C mu * g).IsRoot x) :
    (f + C mu * g).derivative.eval x ≠ 0 :=
  (hfg.hasSimpleRoots_add_right hno hmu).eval_derivative_ne_zero hroot

/-- Left-family form of
`PosComboRealRooted.derivative_eval_ne_zero_add_right`. -/
theorem PosComboRealRooted.derivative_eval_ne_zero_add_left
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {lam x : ℝ}
    (hlam : 0 < lam)
    (hroot : (C lam * f + g).IsRoot x) :
    (C lam * f + g).derivative.eval x ≠ 0 :=
  (hfg.hasSimpleRoots_add_left hno hlam).eval_derivative_ne_zero hroot

/-- A root of an interior no-common right positive pencil carries both the
unique parameter formula and simple-crossing derivative nonvanishing. -/
theorem PosComboRealRooted.root_parameter_eq_and_derivative_ne_zero_add_right
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {mu x : ℝ}
    (hmu : 0 < mu)
    (hroot : (f + C mu * g).IsRoot x) :
    mu = -f.eval x / g.eval x ∧
      (f + C mu * g).derivative.eval x ≠ 0 :=
  ⟨(isRoot_add_right_iff_parameter_eq_of_no_common hno hmu).mp hroot,
    hfg.derivative_eval_ne_zero_add_right hno hmu hroot⟩

/-- A root of two positive right-pencil members has a unique parameter, and
the corresponding root is simple in the first member. -/
theorem PosComboRealRooted.parameter_unique_and_derivative_ne_zero_add_right
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {mu nu x : ℝ}
    (hmu : 0 < mu) (hnu : 0 < nu)
    (hroot_mu : (f + C mu * g).IsRoot x)
    (hroot_nu : (f + C nu * g).IsRoot x) :
    mu = nu ∧ (f + C mu * g).derivative.eval x ≠ 0 :=
  ⟨root_parameter_unique_add_right_of_no_common hno hmu hnu hroot_mu hroot_nu,
    hfg.derivative_eval_ne_zero_add_right hno hmu hroot_mu⟩

/-- A root of an interior no-common right positive pencil carries endpoint
nonvanishing, the unique parameter formula, and simple-crossing derivative
nonvanishing. -/
theorem PosComboRealRooted.root_crossing_data_add_right
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {mu x : ℝ}
    (hmu : 0 < mu)
    (hroot : (f + C mu * g).IsRoot x) :
    g.eval x ≠ 0 ∧ f.eval x ≠ 0 ∧
      mu = -f.eval x / g.eval x ∧
      (f + C mu * g).derivative.eval x ≠ 0 := by
  have hdata := hfg.root_parameter_eq_and_derivative_ne_zero_add_right hno hmu hroot
  exact
    ⟨eval_right_ne_zero_of_isRoot_add_right_of_no_common hno hroot,
      eval_left_ne_zero_of_isRoot_add_right_of_no_common hno hmu hroot,
      hdata.1, hdata.2⟩

/-- Left-family form of
`PosComboRealRooted.root_parameter_eq_and_derivative_ne_zero_add_right`. -/
theorem PosComboRealRooted.root_parameter_eq_and_derivative_ne_zero_add_left
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {lam x : ℝ}
    (hlam : 0 < lam)
    (hroot : (C lam * f + g).IsRoot x) :
    lam = -g.eval x / f.eval x ∧
      (C lam * f + g).derivative.eval x ≠ 0 :=
  ⟨(isRoot_add_left_iff_parameter_eq_of_no_common hno hlam).mp hroot,
    hfg.derivative_eval_ne_zero_add_left hno hlam hroot⟩

/-- Left-family form of
`PosComboRealRooted.parameter_unique_and_derivative_ne_zero_add_right`. -/
theorem PosComboRealRooted.parameter_unique_and_derivative_ne_zero_add_left
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {lam eta x : ℝ}
    (hlam : 0 < lam) (heta : 0 < eta)
    (hroot_lam : (C lam * f + g).IsRoot x)
    (hroot_eta : (C eta * f + g).IsRoot x) :
    lam = eta ∧ (C lam * f + g).derivative.eval x ≠ 0 :=
  ⟨root_parameter_unique_add_left_of_no_common hno hlam heta hroot_lam hroot_eta,
    hfg.derivative_eval_ne_zero_add_left hno hlam hroot_lam⟩

/-- Left-family form of
`PosComboRealRooted.root_crossing_data_add_right`. -/
theorem PosComboRealRooted.root_crossing_data_add_left
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {lam x : ℝ}
    (hlam : 0 < lam)
    (hroot : (C lam * f + g).IsRoot x) :
    f.eval x ≠ 0 ∧ g.eval x ≠ 0 ∧
      lam = -g.eval x / f.eval x ∧
      (C lam * f + g).derivative.eval x ≠ 0 := by
  have hdata := hfg.root_parameter_eq_and_derivative_ne_zero_add_left hno hlam hroot
  exact
    ⟨eval_left_ne_zero_of_isRoot_add_left_of_no_common hno hroot,
      eval_right_ne_zero_of_isRoot_add_left_of_no_common hno hlam hroot,
      hdata.1, hdata.2⟩

/-- Full crossing data at a right-pencil root, extending
`PosComboRealRooted.root_crossing_data_add_right` with uniqueness of the
positive parameter placing `x` on the pencil. This packages the
`parameter_unique_and_derivative_ne_zero_add_right` uniqueness into a single
statement downstream direct-crossing code can use without re-deriving the
affine-family plumbing. -/
theorem PosComboRealRooted.root_crossing_data_unique_add_right
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {mu x : ℝ}
    (hmu : 0 < mu)
    (hroot : (f + C mu * g).IsRoot x) :
    g.eval x ≠ 0 ∧ f.eval x ≠ 0 ∧
      mu = -f.eval x / g.eval x ∧
      (f + C mu * g).derivative.eval x ≠ 0 ∧
      (∀ nu : ℝ, 0 < nu → (f + C nu * g).IsRoot x → nu = mu) := by
  obtain ⟨hg, hf, hpar, hder⟩ :=
    hfg.root_crossing_data_add_right hno hmu hroot
  refine ⟨hg, hf, hpar, hder, ?_⟩
  intro nu hnu hroot_nu
  exact
    (hfg.parameter_unique_and_derivative_ne_zero_add_right hno hnu hmu
      hroot_nu hroot).1

/-- Left-family form of
`PosComboRealRooted.root_crossing_data_unique_add_right`. -/
theorem PosComboRealRooted.root_crossing_data_unique_add_left
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {lam x : ℝ}
    (hlam : 0 < lam)
    (hroot : (C lam * f + g).IsRoot x) :
    f.eval x ≠ 0 ∧ g.eval x ≠ 0 ∧
      lam = -g.eval x / f.eval x ∧
      (C lam * f + g).derivative.eval x ≠ 0 ∧
      (∀ eta : ℝ, 0 < eta → (C eta * f + g).IsRoot x → eta = lam) := by
  obtain ⟨hf, hg, hpar, hder⟩ :=
    hfg.root_crossing_data_add_left hno hlam hroot
  refine ⟨hf, hg, hpar, hder, ?_⟩
  intro eta heta hroot_eta
  exact
    (hfg.parameter_unique_and_derivative_ne_zero_add_left hno heta hlam
      hroot_eta hroot).1

/-- Endpoint-sign wrapper for the right pencil: when the two endpoint
evaluations have opposite signs at `x`, there is a positive parameter placing
`x` on the pencil `f + C μ * g`; that parameter is unique among positive
parameters, is given by `-f(x)/g(x)`, and `x` is a simple root of the
corresponding member (its derivative does not vanish). This is the endpoint
entry point for direct simple-crossing code: it needs only the endpoint sign
condition, not a supplied root. -/
theorem PosComboRealRooted.exists_unique_pos_parameter_crossing_add_right
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {x : ℝ} (hfx : f.eval x ≠ 0)
    (hsign : f.eval x * g.eval x < 0) :
    ∃ mu : ℝ, 0 < mu ∧ (f + C mu * g).IsRoot x ∧
      mu = -f.eval x / g.eval x ∧
      (f + C mu * g).derivative.eval x ≠ 0 ∧
      (∀ nu : ℝ, 0 < nu → (f + C nu * g).IsRoot x → nu = mu) := by
  obtain ⟨mu, hmu, hroot⟩ :=
    (exists_pos_isRoot_add_right_iff_eval_mul_neg hfx).mpr hsign
  obtain ⟨_, _, hpar, hder, huniq⟩ :=
    hfg.root_crossing_data_unique_add_right hno hmu hroot
  exact ⟨mu, hmu, hroot, hpar, hder, huniq⟩

/-- Left-family form of
`PosComboRealRooted.exists_unique_pos_parameter_crossing_add_right`. -/
theorem PosComboRealRooted.exists_unique_pos_parameter_crossing_add_left
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {x : ℝ} (hgx : g.eval x ≠ 0)
    (hsign : f.eval x * g.eval x < 0) :
    ∃ lam : ℝ, 0 < lam ∧ (C lam * f + g).IsRoot x ∧
      lam = -g.eval x / f.eval x ∧
      (C lam * f + g).derivative.eval x ≠ 0 ∧
      (∀ eta : ℝ, 0 < eta → (C eta * f + g).IsRoot x → eta = lam) := by
  obtain ⟨lam, hlam, hroot⟩ :=
    (exists_pos_isRoot_add_left_iff_eval_mul_neg hgx).mpr hsign
  obtain ⟨_, _, hpar, hder, huniq⟩ :=
    hfg.root_crossing_data_unique_add_left hno hlam hroot
  exact ⟨lam, hlam, hroot, hpar, hder, huniq⟩

/-- Projection of `PosComboRealRooted.root_crossing_data_unique_add_right`
keeping only the derivative nonvanishing and parameter uniqueness facts. -/
theorem PosComboRealRooted.derivative_ne_zero_and_parameter_unique_add_right
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {mu x : ℝ}
    (hmu : 0 < mu)
    (hroot : (f + C mu * g).IsRoot x) :
    (f + C mu * g).derivative.eval x ≠ 0 ∧
      (∀ nu : ℝ, 0 < nu → (f + C nu * g).IsRoot x → nu = mu) := by
  obtain ⟨_, _, _, hder, huniq⟩ :=
    hfg.root_crossing_data_unique_add_right hno hmu hroot
  exact ⟨hder, huniq⟩

/-- Left-family form of
`PosComboRealRooted.derivative_ne_zero_and_parameter_unique_add_right`. -/
theorem PosComboRealRooted.derivative_ne_zero_and_parameter_unique_add_left
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {lam x : ℝ}
    (hlam : 0 < lam)
    (hroot : (C lam * f + g).IsRoot x) :
    (C lam * f + g).derivative.eval x ≠ 0 ∧
      (∀ eta : ℝ, 0 < eta → (C eta * f + g).IsRoot x → eta = lam) := by
  obtain ⟨_, _, _, hder, huniq⟩ :=
    hfg.root_crossing_data_unique_add_left hno hlam hroot
  exact ⟨hder, huniq⟩

/-- Endpoint-sign entry point for the right pencil, deriving endpoint
nonvanishing from the opposite-sign condition. -/
theorem PosComboRealRooted.exists_unique_pos_parameter_crossing_add_right_of_sign
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {x : ℝ} (hsign : f.eval x * g.eval x < 0) :
    ∃ mu : ℝ, 0 < mu ∧ (f + C mu * g).IsRoot x ∧
      mu = -f.eval x / g.eval x ∧
      (f + C mu * g).derivative.eval x ≠ 0 ∧
      (∀ nu : ℝ, 0 < nu → (f + C nu * g).IsRoot x → nu = mu) :=
  hfg.exists_unique_pos_parameter_crossing_add_right hno
    (left_ne_zero_of_mul (ne_of_lt hsign)) hsign

/-- Left-family form of
`PosComboRealRooted.exists_unique_pos_parameter_crossing_add_right_of_sign`. -/
theorem PosComboRealRooted.exists_unique_pos_parameter_crossing_add_left_of_sign
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {x : ℝ} (hsign : f.eval x * g.eval x < 0) :
    ∃ lam : ℝ, 0 < lam ∧ (C lam * f + g).IsRoot x ∧
      lam = -g.eval x / f.eval x ∧
      (C lam * f + g).derivative.eval x ≠ 0 ∧
      (∀ eta : ℝ, 0 < eta → (C eta * f + g).IsRoot x → eta = lam) :=
  hfg.exists_unique_pos_parameter_crossing_add_left hno
    (right_ne_zero_of_mul (ne_of_lt hsign)) hsign

/-- Bundled right-and-left endpoint-sign crossing entry point. -/
theorem PosComboRealRooted.exists_unique_pos_parameters_crossing_of_sign
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {x : ℝ} (hsign : f.eval x * g.eval x < 0) :
    (∃ mu : ℝ, 0 < mu ∧ (f + C mu * g).IsRoot x ∧
        mu = -f.eval x / g.eval x ∧
        (f + C mu * g).derivative.eval x ≠ 0 ∧
        (∀ nu : ℝ, 0 < nu → (f + C nu * g).IsRoot x → nu = mu)) ∧
      (∃ lam : ℝ, 0 < lam ∧ (C lam * f + g).IsRoot x ∧
        lam = -g.eval x / f.eval x ∧
        (C lam * f + g).derivative.eval x ≠ 0 ∧
        (∀ eta : ℝ, 0 < eta → (C eta * f + g).IsRoot x → eta = lam)) :=
  ⟨hfg.exists_unique_pos_parameter_crossing_add_right_of_sign hno hsign,
    hfg.exists_unique_pos_parameter_crossing_add_left_of_sign hno hsign⟩

end RealRooted
