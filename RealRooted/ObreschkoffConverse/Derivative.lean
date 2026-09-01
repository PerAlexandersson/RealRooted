import RealRooted.ObreschkoffConverse.Converse
import RealRooted.ObreschkoffConverse.Forward

/-!
# Derivative preservation of proper position

The derivative-preservation consequences of the two directions of
Obreschkoff's theorem.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

/-- Differ-by-one case of the standard fact that differentiation preserves
oriented weak proper position.

The proof uses the forward Obreschkoff direction, differentiates the whole
two-dimensional span, and applies the converse.  In the differ-by-one case the
degree gap rules out the reversed orientation returned by the unoriented
converse. -/
theorem derivative_prec0_of_prec_succDegree {f g : ℝ[X]}
    (hfg : Prec f g) (hdeg : f.natDegree + 1 = g.natDegree) :
    Prec0 f.derivative g.derivative := by
  rcases derivative_eq_zero_or_ne_zero_and_splits hfg.1.2 with hfzero | hfrr
  · rw [hfzero]
    exact prec0_zero_left _
  rcases derivative_eq_zero_or_ne_zero_and_splits hfg.2.1.2 with hgzero | hgrr
  · simp_all
  have hall : AllComboRealRooted f.derivative g.derivative :=
    allComboRealRooted_derivative (allComboRealRooted_of_prec hfg)
  have hfdeg : f.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hfrr.1
  have hgdeg : g.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hgrr.1
  have hfgdeg' : f.derivative.natDegree + 1 = g.derivative.natDegree := by
    rw [f.natDegree_derivative, g.natDegree_derivative]
    lia
  have hdeg' : f.derivative.natDegree + 1 = g.derivative.natDegree ∨
      f.derivative.natDegree = g.derivative.natDegree := Or.inl hfgdeg'
  exact
    (prec_forward_of_orientation_of_succDegree hfgdeg'.symm
      (prec_of_allComboRealRooted hfrr.1 hfrr.2 hgrr.1 hgrr.2 hall hdeg')).toPrec0

/-- In the same-degree case, existing Obreschkoff machinery gives the
derivative pair in proper position up to orientation.  The remaining standard
input below is exactly the oriented branch selection. -/
theorem derivative_prec0_or_revPrec0_of_prec_sameDegree {f g : ℝ[X]}
    (hfg : Prec f g) (hdeg : f.natDegree = g.natDegree) :
    Prec0 f.derivative g.derivative ∨ Prec0 g.derivative f.derivative := by
  rcases derivative_eq_zero_or_ne_zero_and_splits hfg.1.2 with hfzero | hfrr
  · left
    rw [hfzero]
    exact prec0_zero_left _
  rcases derivative_eq_zero_or_ne_zero_and_splits hfg.2.1.2 with hgzero | hgrr
  · simp_all
  have hall : AllComboRealRooted f.derivative g.derivative :=
    allComboRealRooted_derivative (allComboRealRooted_of_prec hfg)
  have hfdeg : f.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hfrr.1
  have hgdeg : g.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hgrr.1
  have hdeg' : f.derivative.natDegree = g.derivative.natDegree := by simp_all
  rcases prec_of_allComboRealRooted hfrr.1 hfrr.2 hgrr.1 hgrr.2 hall
    (Or.inr hdeg') with hprec | hrev
  · exact Or.inl hprec.toPrec0
  · exact Or.inr hrev.toPrec0

/-- For monic same-degree polynomials in proper position, the roots of the
derivatives have the same forward sum order. -/
theorem derivative_roots_sum_le_of_prec_sameDegree_monic {f g : ℝ[X]}
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hfg : Prec f g) (hdeg : f.natDegree = g.natDegree) (htwo : 2 ≤ f.natDegree)
    (hfder_splits : f.derivative.Splits) (hgder_splits : g.derivative.Splits) :
    f.derivative.roots.sum ≤ g.derivative.roots.sum := by
  have hg_two : 2 ≤ g.natDegree := by lia
  have hnext : g.nextCoeff ≤ f.nextCoeff :=
    nextCoeff_le_of_prec_sameDegree_monic hf_monic hg_monic hfg hdeg
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

/-- Same-degree branch of the standard fact that differentiation preserves
oriented weak proper position. -/
def derivativePreservesPrecSameDegreeStatement : Prop :=
  ∀ {f g : ℝ[X]}, Prec f g → f.natDegree = g.natDegree →
    Prec0 f.derivative g.derivative

/-- Scaling both sides by nonzero constants preserves zero-aware proper
position. -/
private lemma prec0_C_mul_left_right {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {f g : ℝ[X]} (h : Prec0 f g) :
    Prec0 (C a * f) (C b * g) := by
  rcases h with rfl | rfl | hprec
  · simp [prec0_zero_left]
  · simp [prec0_zero_right]
  · exact (prec_C_mul_right (prec_C_mul_left hprec ha) hb).toPrec0

/-- Degree-zero polynomials satisfy `Prec` in both orientations. -/
lemma prec_degree_zero_degree_zero
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hf_deg0 : f.natDegree = 0) (hg_deg0 : g.natDegree = 0) :
    Prec f g := by
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

/-- Degree-at-least-two same-degree branch of the standard fact that
differentiation preserves oriented weak proper position. -/
def derivativePreservesPrecSameDegreeOfTwoLeNatDegreeStatement : Prop :=
  ∀ {f g : ℝ[X]}, Prec f g → f.natDegree = g.natDegree → 2 ≤ f.natDegree →
    Prec0 f.derivative g.derivative

/-- Positive-leading-coefficient form of the degree-at-least-two same-degree
derivative-preservation branch. -/
def derivativePreservesPrecSameDegreeOfTwoLeNatDegreePosLeadingStatement : Prop :=
  ∀ {f g : ℝ[X]}, HasPosLeadingCoeff f → HasPosLeadingCoeff g →
    Prec f g → f.natDegree = g.natDegree → 2 ≤ f.natDegree →
    Prec0 f.derivative g.derivative

/-- Monic form of the degree-at-least-two same-degree derivative-preservation
branch. -/
def derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicStatement : Prop :=
  ∀ {f g : ℝ[X]}, f.Monic → g.Monic →
    Prec f g → f.natDegree = g.natDegree → 2 ≤ f.natDegree →
    Prec0 f.derivative g.derivative

/-- Strict-`Prec` monic form of the degree-at-least-two same-degree
derivative-preservation branch. -/
def derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicPrecStatement : Prop :=
  ∀ {f g : ℝ[X]}, f.Monic → g.Monic →
    Prec f g → f.natDegree = g.natDegree → 2 ≤ f.natDegree →
    Prec f.derivative g.derivative

/-- Monic degree-at-least-two same-degree branch of the standard fact that
differentiation preserves oriented weak proper position. -/
theorem derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonic :
    derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicStatement := by
  intro f g hf_monic hg_monic hfg hdeg htwo
  have hfder_ne : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hgder_ne : g.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hdeg_der : f.derivative.natDegree = g.derivative.natDegree := by simp_all
  rcases derivative_prec0_or_revPrec0_of_prec_sameDegree hfg hdeg with hprec0 | hrev0
  · grind
  · have hrev : Prec g.derivative f.derivative :=
      hrev0.toPrec_of_ne hgder_ne hfder_ne
    have hsum_der : f.derivative.roots.sum ≤ g.derivative.roots.sum :=
      derivative_roots_sum_le_of_prec_sameDegree_monic hf_monic hg_monic hfg hdeg htwo
        hrev.2.1.2 hrev.1.2
    exact (prec_of_reverse_prec_of_roots_sum_le hrev hdeg_der hsum_der).toPrec0

/-- The strict-`Prec` monic branch follows from the zero-aware monic branch,
since the degree hypotheses make both derivatives nonzero. -/
theorem derivativePreservesPrecSameDegree_monicPrec_of_monic
    (hmonic : derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicStatement) :
    derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicPrecStatement := by
  intro f g hf_monic hg_monic hfg hdeg htwo
  have hfder_ne : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hgder_ne : g.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  rcases hmonic hf_monic hg_monic hfg hdeg htwo with hfzero | hgzero | hprec <;> simp_all

/-- The zero-aware monic branch follows from the strict-`Prec` monic branch. -/
theorem derivativePreservesPrecSameDegree_of_monicPrec
    (hmonic : derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicPrecStatement) :
    derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicStatement :=
  fun {_ _} hf_monic hg_monic hfg hdeg htwo =>
    (hmonic hf_monic hg_monic hfg hdeg htwo).toPrec0

/-- The positive-leading-coefficient branch follows from the monic branch by
normalizing both polynomials by their leading coefficients. -/
theorem derivativePreservesPrecSameDegree_of_monic
    (hmonic : derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicStatement) :
    derivativePreservesPrecSameDegreeOfTwoLeNatDegreePosLeadingStatement := by
  intro f g hf_pos hg_pos hfg hdeg htwo
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
  have hfg₀ : Prec f₀ g₀ :=
    prec_C_mul_right (prec_C_mul_left hfg (inv_ne_zero hf_lc_ne))
      (inv_ne_zero hg_lc_ne)
  have hdeg₀ : f₀.natDegree = g₀.natDegree := by
    simpa [f₀, g₀, natDegree_C_mul (inv_ne_zero hf_lc_ne),
      natDegree_C_mul (inv_ne_zero hg_lc_ne)] using hdeg
  have htwo₀ : 2 ≤ f₀.natDegree := by
    simpa [f₀, natDegree_C_mul (inv_ne_zero hf_lc_ne)] using htwo
  have hscaled : Prec0 f₀.derivative g₀.derivative :=
    hmonic hf₀_monic hg₀_monic hfg₀ hdeg₀ htwo₀
  have hscaled' :
      Prec0 (C f.leadingCoeff⁻¹ * f.derivative)
        (C g.leadingCoeff⁻¹ * g.derivative) := by
    simpa [f₀, g₀, derivative_C_mul] using hscaled
  have hback :
      Prec0 (C f.leadingCoeff * (C f.leadingCoeff⁻¹ * f.derivative))
        (C g.leadingCoeff * (C g.leadingCoeff⁻¹ * g.derivative)) :=
    prec0_C_mul_left_right hf_lc_ne hg_lc_ne hscaled'
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

/-- The degree-at-least-two same-degree branch follows from its
positive-leading-coefficient form by scaling both polynomials by signs. -/
theorem derivativePreservesPrecSameDegree_of_posLeading
    (hpos :
      derivativePreservesPrecSameDegreeOfTwoLeNatDegreePosLeadingStatement) :
    derivativePreservesPrecSameDegreeOfTwoLeNatDegreeStatement := by
  intro f g hfg hdeg htwo
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
  have hfg₀ : Prec f₀ g₀ :=
    prec_C_mul_right (prec_C_mul_left hfg hsf_ne) hsg_ne
  have hdeg₀ : f₀.natDegree = g₀.natDegree := by
    simpa [f₀, g₀, natDegree_C_mul hsf_ne, natDegree_C_mul hsg_ne] using hdeg
  have htwo₀ : 2 ≤ f₀.natDegree := by simpa [f₀, natDegree_C_mul hsf_ne] using htwo
  have hscaled : Prec0 f₀.derivative g₀.derivative :=
    hpos hf₀_pos hg₀_pos hfg₀ hdeg₀ htwo₀
  have hscaled' : Prec0 (C sf * f.derivative) (C sg * g.derivative) := by
    simpa [f₀, g₀, derivative_C_mul] using hscaled
  have hback :
      Prec0 (C sf⁻¹ * (C sf * f.derivative))
        (C sg⁻¹ * (C sg * g.derivative)) :=
    prec0_C_mul_left_right (inv_ne_zero hsf_ne) (inv_ne_zero hsg_ne) hscaled'
  grind

/-- The same-degree derivative-preservation statement follows from its
degree-at-least-two branch.  Degrees zero and one are elementary because the
derivatives are zero or nonzero constants. -/
theorem derivativePreservesPrecSameDegree_of_two_le_natDegree
    (hlarge : derivativePreservesPrecSameDegreeOfTwoLeNatDegreeStatement) :
    derivativePreservesPrecSameDegreeStatement := by
  intro f g hfg hdeg
  by_cases hlarge_deg : 2 ≤ f.natDegree
  · exact hlarge hfg hdeg hlarge_deg
  · by_cases hfdeg0 : f.natDegree = 0
    · have hfder : f.derivative = 0 :=
        Polynomial.derivative_eq_zero.mpr hfdeg0
      have hgdeg0 : g.natDegree = 0 := by lia
      have hgder : g.derivative = 0 :=
        Polynomial.derivative_eq_zero.mpr hgdeg0
      rw [hfder, hgder]
      exact prec0_zero_zero
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
        (prec_degree_zero_degree_zero hfder_rr.1 hfder_rr.2 hgder_rr.1 hgder_rr.2
          hfder_deg0 hgder_deg0).toPrec0

/-- The full zero-aware derivative-preservation statement follows from the
same-degree branch.  The differ-by-one branch is
`derivative_prec0_of_prec_succDegree`, proved above from the forward and
converse Obreschkoff theorems. -/
theorem derivativePreservesPrec0_of_sameDegree
    (hsame : derivativePreservesPrecSameDegreeStatement) :
    derivativePreservesPrec0Statement := by
  intro f g hfg
  rcases hfg with hfzero | hgzero | hfg'
  · rw [hfzero, derivative_zero]
    exact prec0_zero_left _
  · rw [hgzero, derivative_zero]
    exact prec0_zero_right _
  · have hfg_le := hfg'.natDegree_le
    have hgf_le := hfg'.natDegree_le_succ
    by_cases hdeg : f.natDegree = g.natDegree
    · exact hsame hfg' hdeg
    · exact derivative_prec0_of_prec_succDegree hfg' (by lia)

/-- Same-degree branch of differentiation preserving weak proper position. -/
theorem derivativePreservesPrecSameDegree :
    derivativePreservesPrecSameDegreeStatement :=
  derivativePreservesPrecSameDegree_of_two_le_natDegree <|
    derivativePreservesPrecSameDegree_of_posLeading <|
      derivativePreservesPrecSameDegree_of_monic
        derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonic

/-- Differentiation preserves zero-aware weak proper position. -/
theorem derivativePreservesPrec0 : derivativePreservesPrec0Statement :=
  derivativePreservesPrec0_of_sameDegree derivativePreservesPrecSameDegree

/-!
### Direct #42 / shared #41 derivative-preservation API

These wrappers repackage `derivativePreservesPrecSameDegree` and
`derivativePreservesPrec0` in applied forms used by the closed-segment and
common-interleaver routes.
-/

/-- Zero-aware derivative preservation, applied form of `derivativePreservesPrec0`. -/
theorem derivative_prec0_of_prec0 {f g : ℝ[X]} (h : Prec0 f g) :
    Prec0 f.derivative g.derivative :=
  derivativePreservesPrec0 h

/-- Explicit-binder variant of `derivative_prec0_of_prec0`. -/
theorem derivative_prec0_of_prec0' (f g : ℝ[X]) (h : Prec0 f g) :
    Prec0 f.derivative g.derivative :=
  derivativePreservesPrec0 h

/-- A strict `Prec` input yields zero-aware derivative preservation. -/
theorem derivative_prec0_of_prec {f g : ℝ[X]} (h : Prec f g) :
    Prec0 f.derivative g.derivative :=
  derivativePreservesPrec0 h.toPrec0

/-- Explicit-binder variant of `derivative_prec0_of_prec`. -/
theorem derivative_prec0_of_prec' (f g : ℝ[X]) (h : Prec f g) :
    Prec0 f.derivative g.derivative :=
  derivativePreservesPrec0 h.toPrec0

/-- Same-degree derivative preservation, applied form of
`derivativePreservesPrecSameDegree`. -/
theorem derivative_prec0_of_prec_sameDegree {f g : ℝ[X]} (h : Prec f g)
    (hdeg : f.natDegree = g.natDegree) :
    Prec0 f.derivative g.derivative :=
  derivativePreservesPrecSameDegree h hdeg

/-- Explicit-binder variant of `derivative_prec0_of_prec_sameDegree`. -/
theorem derivative_prec0_of_prec_sameDegree' (f g : ℝ[X]) (h : Prec f g)
    (hdeg : f.natDegree = g.natDegree) :
    Prec0 f.derivative g.derivative :=
  derivativePreservesPrecSameDegree h hdeg

/-- Strict `Prec` output in the same-degree case. -/
theorem derivative_prec_of_prec_sameDegree {f g : ℝ[X]} (h : Prec f g)
    (hdeg : f.natDegree = g.natDegree) (hpos : 1 ≤ f.natDegree) :
    Prec f.derivative g.derivative := by
  have hfder_ne : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hgder_ne : g.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  exact (derivativePreservesPrecSameDegree h hdeg).toPrec_of_ne hfder_ne hgder_ne

/-- Explicit-binder variant of `derivative_prec_of_prec_sameDegree`. -/
theorem derivative_prec_of_prec_sameDegree' (f g : ℝ[X]) (h : Prec f g)
    (hdeg : f.natDegree = g.natDegree) (hpos : 1 ≤ f.natDegree) :
    Prec f.derivative g.derivative :=
  derivative_prec_of_prec_sameDegree h hdeg hpos

/-- Strict `Prec` output in the succ-degree case. -/
theorem derivative_prec_of_prec_succDegree {f g : ℝ[X]} (h : Prec f g)
    (hdeg : f.natDegree + 1 = g.natDegree) (hpos : 1 ≤ f.natDegree) :
    Prec f.derivative g.derivative := by
  have hfder_ne : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hgder_ne : g.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  exact (derivative_prec0_of_prec_succDegree h hdeg).toPrec_of_ne hfder_ne hgder_ne
end
end RealRooted
