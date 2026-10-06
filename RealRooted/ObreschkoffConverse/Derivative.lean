import RealRooted.ObreschkoffConverse.Converse
import RealRooted.ObreschkoffConverse.Forward

/-!
# Derivative preservation of interlacing

The derivative-preservation consequences of the two directions of
Obreschkoff's theorem.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

/-- Differ-by-one case of the standard fact that differentiation preserves
oriented weak interlacing.

The proof uses the forward Obreschkoff direction, differentiates the whole
two-dimensional span, and applies the converse.  In the differ-by-one case the
degree gap rules out the reversed orientation returned by the unoriented
converse. -/
theorem derivative_interl_of_strictInterl_succDegree {f g : ℝ[X]}
    (hfg : StrictInterl f g) (hdeg : f.natDegree + 1 = g.natDegree) :
    Interl f.derivative g.derivative := by
  rcases derivative_eq_zero_or_ne_zero_and_splits hfg.1.2 with hfzero | hfrr
  · rw [hfzero]
    exact interl_zero_left _
  rcases derivative_eq_zero_or_ne_zero_and_splits hfg.2.1.2 with hgzero | hgrr
  · simp_all
  have hall : AllComboRealRooted f.derivative g.derivative :=
    allComboRealRooted_derivative (allComboRealRooted_of_strictInterl hfg)
  have hfdeg : f.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hfrr.1
  have hgdeg : g.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hgrr.1
  have hfgdeg' : f.derivative.natDegree + 1 = g.derivative.natDegree := by
    rw [f.natDegree_derivative, g.natDegree_derivative]
    lia
  have hdeg' : f.derivative.natDegree + 1 = g.derivative.natDegree ∨
      f.derivative.natDegree = g.derivative.natDegree := Or.inl hfgdeg'
  exact
    (StrictInterl.forward_of_orientation_of_succDegree hfgdeg'.symm
      (strictInterl_of_allComboRealRooted hfrr.1 hfrr.2 hgrr.1 hgrr.2 hall hdeg')).toInterl

/-- In the same-degree case, existing Obreschkoff machinery gives the
derivative pair in an interlacing relation up to orientation.  The remaining standard
input below is exactly the oriented branch selection. -/
theorem derivative_interl_or_reverse_of_strictInterl_sameDegree {f g : ℝ[X]}
    (hfg : StrictInterl f g) (hdeg : f.natDegree = g.natDegree) :
    Interl f.derivative g.derivative ∨ Interl g.derivative f.derivative := by
  rcases derivative_eq_zero_or_ne_zero_and_splits hfg.1.2 with hfzero | hfrr
  · left
    rw [hfzero]
    exact interl_zero_left _
  rcases derivative_eq_zero_or_ne_zero_and_splits hfg.2.1.2 with hgzero | hgrr
  · simp_all
  have hall : AllComboRealRooted f.derivative g.derivative :=
    allComboRealRooted_derivative (allComboRealRooted_of_strictInterl hfg)
  have hfdeg : f.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hfrr.1
  have hgdeg : g.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hgrr.1
  have hdeg' : f.derivative.natDegree = g.derivative.natDegree := by simp_all
  rcases strictInterl_of_allComboRealRooted hfrr.1 hfrr.2 hgrr.1 hgrr.2 hall
    (Or.inr hdeg') with hstrictInterl | hrev
  · exact Or.inl hstrictInterl.toInterl
  · exact Or.inr hrev.toInterl

/-- For monic same-degree polynomials in an interlacing relation, the roots of the
derivatives have the same forward sum order. -/
theorem derivative_roots_sum_le_of_strictInterl_sameDegree_monic {f g : ℝ[X]}
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hfg : StrictInterl f g) (hdeg : f.natDegree = g.natDegree) (htwo : 2 ≤ f.natDegree)
    (hfder_splits : f.derivative.Splits) (hgder_splits : g.derivative.Splits) :
    f.derivative.roots.sum ≤ g.derivative.roots.sum := by
  have hg_two : 2 ≤ g.natDegree := by lia
  have hnext : g.nextCoeff ≤ f.nextCoeff :=
    hfg.nextCoeff_le_of_sameDegree_monic hf_monic hg_monic hdeg
  have hf_next_der :
      f.derivative.nextCoeff = (f.natDegree - 1 : ℝ) * f.nextCoeff :=
    Polynomial.nextCoeff_derivative_of_two_le_natDegree f htwo
  have hg_next_der :
      g.derivative.nextCoeff = (f.natDegree - 1 : ℝ) * g.nextCoeff := by
    simpa [hdeg] using Polynomial.nextCoeff_derivative_of_two_le_natDegree g hg_two
  have hfactor_nonneg : 0 ≤ (f.natDegree - 1 : ℝ) := by
    have hcast : (1 : ℝ) ≤ (f.natDegree : ℝ) := by
      simpa using
        (Nat.cast_le.mpr (by lia : 1 ≤ f.natDegree) :
          ((1 : Nat) : ℝ) ≤ (f.natDegree : ℝ))
    linarith
  have hnext_der : g.derivative.nextCoeff ≤ f.derivative.nextCoeff := by
    rw [hf_next_der, hg_next_der]
    exact mul_le_mul_of_nonneg_left hnext hfactor_nonneg
  have hf_lc_der : f.derivative.leadingCoeff = (f.natDegree : ℝ) := by
    simp [hf_monic.leadingCoeff]
  have hg_lc_der : g.derivative.leadingCoeff = (f.natDegree : ℝ) := by
    simp [hg_monic.leadingCoeff, hdeg]
  have hf_next_roots :
      f.derivative.nextCoeff = -(f.natDegree : ℝ) * f.derivative.roots.sum := by
    simpa [hf_lc_der] using hfder_splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hg_next_roots :
      g.derivative.nextCoeff = -(f.natDegree : ℝ) * g.derivative.roots.sum := by
    simpa [hg_lc_der] using hgder_splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hdeg_pos : 0 < (f.natDegree : ℝ) := by positivity
  nlinarith

/-- Scaling both sides by nonzero constants preserves zero-aware proper
position. -/
private lemma interl_C_mul_left_right {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {f g : ℝ[X]} (h : Interl f g) :
    Interl (C a * f) (C b * g) := by
  rcases h with rfl | rfl | hstrictInterl
  · simp [interl_zero_left]
  · simp [interl_zero_right]
  · exact (StrictInterl.C_mul_right (StrictInterl.C_mul_left hstrictInterl ha) hb).toInterl

/-- Degree-zero polynomials satisfy `StrictInterl` in both orientations. -/
lemma StrictInterl.of_degree_zero_degree_zero
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hf_deg0 : f.natDegree = 0) (hg_deg0 : g.natDegree = 0) :
    StrictInterl f g := by
  have hroots_f : f.roots = 0 := by
    apply Multiset.card_eq_zero.mp
    rw [card_roots_of_splits hf_splits, hf_deg0]
  have hroots_g : g.roots = 0 := by
    apply Multiset.card_eq_zero.mp
    rw [card_roots_of_splits hg_splits, hg_deg0]
  refine ⟨⟨hf_ne, hf_splits⟩, ⟨hg_ne, hg_splits⟩, [], [], by simp, by simp, ?_, ?_, ?_⟩
  · simp [hroots_f]
  · simp [hroots_g]
  · exact Or.inr ⟨by lia, by simp [ListAlternates]⟩

/-- Monic degree-at-least-two same-degree branch of the standard fact that
differentiation preserves oriented weak interlacing. -/
theorem derivative_interl_of_strictInterl_sameDegree_monic {f g : ℝ[X]}
    (hf_monic : f.Monic) (hg_monic : g.Monic) (hfg : StrictInterl f g)
    (hdeg : f.natDegree = g.natDegree) (htwo : 2 ≤ f.natDegree) :
    Interl f.derivative g.derivative := by
  have hfder_ne : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hgder_ne : g.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hdeg_der : f.derivative.natDegree = g.derivative.natDegree := by simp_all
  rcases derivative_interl_or_reverse_of_strictInterl_sameDegree hfg hdeg with
    hinterl | hreverse
  · grind
  · have hrev : StrictInterl g.derivative f.derivative :=
      hreverse.toStrictInterl_of_ne hgder_ne hfder_ne
    have hsum_der : f.derivative.roots.sum ≤ g.derivative.roots.sum :=
      derivative_roots_sum_le_of_strictInterl_sameDegree_monic
        hf_monic hg_monic hfg hdeg htwo hrev.2.1.2 hrev.1.2
    exact (hrev.of_reverse_of_roots_sum_le hdeg_der hsum_der).toInterl

/-- Positive-leading-coefficient degree-at-least-two same-degree branch,
obtained from the monic branch by normalizing both polynomials by their leading
coefficients. -/
theorem derivative_interl_of_strictInterl_sameDegree_posLeading {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : StrictInterl f g) (hdeg : f.natDegree = g.natDegree)
    (htwo : 2 ≤ f.natDegree) :
    Interl f.derivative g.derivative := by
  have hf_lc_ne : f.leadingCoeff ≠ 0 := ne_of_gt hf_pos
  have hg_lc_ne : g.leadingCoeff ≠ 0 := ne_of_gt hg_pos
  let f₀ : ℝ[X] := C f.leadingCoeff⁻¹ * f
  let g₀ : ℝ[X] := C g.leadingCoeff⁻¹ * g
  have hf₀_monic : f₀.Monic := by
    unfold f₀
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hg₀_monic : g₀.Monic := by
    unfold g₀
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hfg₀ : StrictInterl f₀ g₀ :=
    StrictInterl.C_mul_right (StrictInterl.C_mul_left hfg (inv_ne_zero hf_lc_ne))
      (inv_ne_zero hg_lc_ne)
  have hdeg₀ : f₀.natDegree = g₀.natDegree := by
    simpa [f₀, g₀, natDegree_C_mul (inv_ne_zero hf_lc_ne),
      natDegree_C_mul (inv_ne_zero hg_lc_ne)] using hdeg
  have htwo₀ : 2 ≤ f₀.natDegree := by
    simpa [f₀, natDegree_C_mul (inv_ne_zero hf_lc_ne)] using htwo
  have hscaled : Interl f₀.derivative g₀.derivative :=
    derivative_interl_of_strictInterl_sameDegree_monic hf₀_monic hg₀_monic hfg₀ hdeg₀ htwo₀
  have hscaled' :
      Interl (C f.leadingCoeff⁻¹ * f.derivative)
        (C g.leadingCoeff⁻¹ * g.derivative) := by
    simpa [f₀, g₀, derivative_C_mul] using hscaled
  have hback :
      Interl (C f.leadingCoeff * (C f.leadingCoeff⁻¹ * f.derivative))
        (C g.leadingCoeff * (C g.leadingCoeff⁻¹ * g.derivative)) :=
    interl_C_mul_left_right hf_lc_ne hg_lc_ne hscaled'
  have hf_inv :
      C f.leadingCoeff * (C f.leadingCoeff⁻¹ * f.derivative) =
        f.derivative := by
    rw [← mul_assoc, ← C_mul]
    simp [hf_lc_ne]
  have hg_inv :
      C g.leadingCoeff * (C g.leadingCoeff⁻¹ * g.derivative) =
        g.derivative := by
    rw [← mul_assoc, ← C_mul]
    simp [hg_lc_ne]
  simp_all

/-- Degree-at-least-two same-degree branch, obtained from the
positive-leading-coefficient form by scaling both polynomials by signs. -/
theorem derivative_interl_of_strictInterl_sameDegree_two_le {f g : ℝ[X]}
    (hfg : StrictInterl f g) (hdeg : f.natDegree = g.natDegree)
    (htwo : 2 ≤ f.natDegree) :
    Interl f.derivative g.derivative := by
  have hf_lc_ne : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hfg.1.1
  have hg_lc_ne : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hfg.2.1.1
  let sf : ℝ := if 0 < f.leadingCoeff then 1 else -1
  let sg : ℝ := if 0 < g.leadingCoeff then 1 else -1
  have hsf_ne : sf ≠ 0 := by grind
  have hsg_ne : sg ≠ 0 := by grind
  have hsf_pos : 0 < sf * f.leadingCoeff := by
    dsimp [sf]
    split_ifs with hposf
    · lia
    · grind
  have hsg_pos : 0 < sg * g.leadingCoeff := by
    dsimp [sg]
    split_ifs with hposg
    · lia
    · grind
  let f₀ : ℝ[X] := C sf * f
  let g₀ : ℝ[X] := C sg * g
  have hf₀_pos : HasPosLeadingCoeff f₀ := by
    unfold HasPosLeadingCoeff f₀
    simp_all
  have hg₀_pos : HasPosLeadingCoeff g₀ := by
    unfold HasPosLeadingCoeff g₀
    simp_all
  have hfg₀ : StrictInterl f₀ g₀ :=
    StrictInterl.C_mul_right (StrictInterl.C_mul_left hfg hsf_ne) hsg_ne
  have hdeg₀ : f₀.natDegree = g₀.natDegree := by
    simpa [f₀, g₀, natDegree_C_mul hsf_ne, natDegree_C_mul hsg_ne] using hdeg
  have htwo₀ : 2 ≤ f₀.natDegree := by simpa [f₀, natDegree_C_mul hsf_ne] using htwo
  have hscaled : Interl f₀.derivative g₀.derivative :=
    derivative_interl_of_strictInterl_sameDegree_posLeading hf₀_pos hg₀_pos hfg₀ hdeg₀ htwo₀
  have hscaled' : Interl (C sf * f.derivative) (C sg * g.derivative) := by
    simpa [f₀, g₀, derivative_C_mul] using hscaled
  have hback :
      Interl (C sf⁻¹ * (C sf * f.derivative))
        (C sg⁻¹ * (C sg * g.derivative)) :=
    interl_C_mul_left_right (inv_ne_zero hsf_ne) (inv_ne_zero hsg_ne) hscaled'
  grind

/-- Same-degree branch of differentiation preserving weak interlacing.
Degrees zero and one are elementary because the derivatives are zero or nonzero
constants. -/
theorem derivative_interl_of_strictInterl_sameDegree {f g : ℝ[X]}
    (hfg : StrictInterl f g) (hdeg : f.natDegree = g.natDegree) :
    Interl f.derivative g.derivative := by
  by_cases hlarge_deg : 2 ≤ f.natDegree
  · exact derivative_interl_of_strictInterl_sameDegree_two_le hfg hdeg hlarge_deg
  · by_cases hfdeg0 : f.natDegree = 0
    · have hfder : f.derivative = 0 :=
        Polynomial.derivative_eq_zero.mpr hfdeg0
      have hgdeg0 : g.natDegree = 0 := by lia
      have hgder : g.derivative = 0 :=
        Polynomial.derivative_eq_zero.mpr hgdeg0
      rw [hfder, hgder]
      exact interl_zero_zero
    · have hfdeg1 : f.natDegree = 1 := by lia
      have hgdeg1 : g.natDegree = 1 := by lia
      have hfder_ne : f.derivative ≠ 0 :=
        Polynomial.derivative_ne_zero.mpr (by lia)
      have hgder_ne : g.derivative ≠ 0 :=
        Polynomial.derivative_ne_zero.mpr (by lia)
      have hfder_deg0 : f.derivative.natDegree = 0 := by simp_all
      have hgder_deg0 : g.derivative.natDegree = 0 := by simp_all
      have hfder_rr : (f.derivative ≠ 0 ∧ f.derivative.Splits) :=
        isRealRooted_of_deg_zero hfder_ne hfder_deg0
      have hgder_rr : (g.derivative ≠ 0 ∧ g.derivative.Splits) :=
        isRealRooted_of_deg_zero hgder_ne hgder_deg0
      exact
        (StrictInterl.of_degree_zero_degree_zero hfder_rr.1 hfder_rr.2 hgder_rr.1 hgder_rr.2
          hfder_deg0 hgder_deg0).toInterl

/-- Differentiation preserves zero-aware weak interlacing (Rolle--Obreschkoff).
The same-degree branch is `derivative_interl_of_strictInterl_sameDegree`; the
differ-by-one branch is `derivative_interl_of_strictInterl_succDegree`, proved
above from the forward and converse Obreschkoff theorems. -/
theorem derivativePreservesInterl {p q : ℝ[X]} (hfg : Interl p q) :
    Interl p.derivative q.derivative := by
  rcases hfg with hfzero | hgzero | hfg'
  · rw [hfzero, derivative_zero]
    exact interl_zero_left _
  · rw [hgzero, derivative_zero]
    exact interl_zero_right _
  · rcases hfg'.natDegree_eq_or_eq_succ with hsameDegree | hsuccDegree
    · exact derivative_interl_of_strictInterl_sameDegree hfg' hsameDegree.symm
    · exact derivative_interl_of_strictInterl_succDegree hfg' hsuccDegree.symm

/-! ### Strict derivative preservation -/

/-- A `StrictInterl` input yields zero-aware derivative preservation. -/
theorem derivative_interl_of_strictInterl {f g : ℝ[X]} (h : StrictInterl f g) :
    Interl f.derivative g.derivative :=
  derivativePreservesInterl h.toInterl

/-- Strict `StrictInterl` output in the same-degree case. -/
theorem derivative_strictInterl_of_strictInterl_sameDegree
    {f g : ℝ[X]} (h : StrictInterl f g)
    (hdeg : f.natDegree = g.natDegree) (hpos : 1 ≤ f.natDegree) :
    StrictInterl f.derivative g.derivative := by
  have hfder_ne : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hgder_ne : g.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  exact
    (derivative_interl_of_strictInterl_sameDegree h hdeg).toStrictInterl_of_ne hfder_ne hgder_ne

/-- Strict `StrictInterl` output in the succ-degree case. -/
theorem derivative_strictInterl_of_strictInterl_succDegree
    {f g : ℝ[X]} (h : StrictInterl f g)
    (hdeg : f.natDegree + 1 = g.natDegree) (hpos : 1 ≤ f.natDegree) :
    StrictInterl f.derivative g.derivative := by
  have hfder_ne : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hgder_ne : g.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  exact
    (derivative_interl_of_strictInterl_succDegree h hdeg).toStrictInterl_of_ne
      hfder_ne hgder_ne

end
end RealRooted
