module

public import RealRooted.AffineFamily

/-!
# Positive-combination tactic frontends

Thin wrappers for `PosComboRealRooted` and positive/nonnegative linear
combination certificates.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

theorem posCombo_sequence_nonneg_right_strictInterl
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hfg : ∀ i : Nat, StrictInterl (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (ha : ∀ i : Nat, 0 ≤ a i)
    (hb : ∀ i : Nat, 0 ≤ b i)
    (hab : ∀ i : Nat, 0 < a i ∨ 0 < b i) :
    ∀ i : Nat, StrictInterl (C (a i) * F i + C (b i) * G i) (G i) := fun i =>
  StrictInterl.nonneg_combo_right (hfg i) (hF i) (hG i) (ha i) (hb i) (hab i)

theorem posCombo_sequence_nonneg_realrooted
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hfg : ∀ i : Nat, StrictInterl (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (ha : ∀ i : Nat, 0 ≤ a i)
    (hb : ∀ i : Nat, 0 ≤ b i)
    (hab : ∀ i : Nat, 0 < a i ∨ 0 < b i) :
    ∀ i : Nat,
      (C (a i) * F i + C (b i) * G i) ≠ 0 ∧
        (C (a i) * F i + C (b i) * G i).Splits := fun i =>
  StrictInterl.isRealRooted_nonneg_combo
    (hfg i) (hF i) (hG i) (ha i) (hb i) (hab i)

theorem posCombo_sequence_positive_realrooted
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hfg : ∀ i : Nat, StrictInterl (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (ha : ∀ i : Nat, 0 < a i)
    (hb : ∀ i : Nat, 0 < b i) :
    ∀ i : Nat,
      (C (a i) * F i + C (b i) * G i) ≠ 0 ∧
        (C (a i) * F i + C (b i) * G i).Splits := fun i =>
  StrictInterl.isRealRooted_pos_combo
    (hfg i) (hF i) (hG i) (ha i) (hb i)

theorem posCombo_sequence_comm {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i)) :
    ∀ i : Nat, PosComboRealRooted (G i) (F i) := fun i =>
  PosComboRealRooted.comm (hfg i)

theorem posCombo_sequence_add_realrooted {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i)) :
    ∀ i : Nat, F i + G i ≠ 0 ∧ (F i + G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_add (hfg i)

theorem posCombo_sequence_add_right_realrooted
    {F G : Nat → ℝ[X]} {mu : Nat → ℝ}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hmu : ∀ i : Nat, 0 < mu i) :
    ∀ i : Nat, F i + C (mu i) * G i ≠ 0 ∧
      (F i + C (mu i) * G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_add_right (hfg i) (hmu i)

theorem posCombo_sequence_add_left_realrooted
    {F G : Nat → ℝ[X]} {lam : Nat → ℝ}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hlam : ∀ i : Nat, 0 < lam i) :
    ∀ i : Nat, C (lam i) * F i + G i ≠ 0 ∧
      (C (lam i) * F i + G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_add_left (hfg i) (hlam i)

theorem posCombo_sequence_of_strictInterl {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, StrictInterl (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i)) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := fun i =>
  PosComboRealRooted.of_strictInterl (hfg i) (hF i) (hG i)

theorem posCombo_sequence_of_common_left {F G H : Nat → ℝ[X]}
    (hHF : ∀ i : Nat, StrictInterl (H i) (F i))
    (hHG : ∀ i : Nat, StrictInterl (H i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i)) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := fun i =>
  PosComboRealRooted.of_commonLeftInterleaver
    (hHF i) (hHG i) (hF i) (hG i)

theorem posCombo_sequence_left_same_degree_realrooted
    {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree) :
    ∀ i : Nat, F i ≠ 0 ∧ (F i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_left_of_sameDegree
    (hfg i) (hF i) (hG i) (hdeg i)

theorem posCombo_sequence_right_same_degree_realrooted
    {F G : Nat → ℝ[X]}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree) :
    ∀ i : Nat, G i ≠ 0 ∧ (G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_right_of_sameDegree
    (hfg i) (hF i) (hG i) (hdeg i)

theorem posCombo_sequence_closed_segment_same_degree_realrooted
    {F G : Nat → ℝ[X]} {beta : Nat → ℝ}
    (hfg : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hbeta0 : ∀ i : Nat, 0 ≤ beta i)
    (hbeta1 : ∀ i : Nat, beta i ≤ 1) :
    ∀ i : Nat, C (1 - beta i) * F i + C (beta i) * G i ≠ 0 ∧
      (C (1 - beta i) * F i + C (beta i) * G i).Splits := fun i =>
  PosComboRealRooted.isRealRooted_closed_segment_of_sameDegree
    (hfg i) (hF i) (hG i) (hdeg i) (hbeta0 i) (hbeta1 i)

/-- Closes `StrictInterl (C a * f + C b * g) g` from `strictInterl : StrictInterl f g`, the positive
leading coefficients `left_pos_lc` and `right_pos_lc`, the coefficient bounds
`left_coeff_nonneg : 0 ≤ a` and `right_coeff_nonneg : 0 ≤ b`, and
`some_coeff_pos : 0 < a ∨ 0 < b`. -/
syntax (name := rr_pos_combo_nonneg_right_strict_interl_named)
  "rr_pos_combo_nonneg_right_strict_interl" " using "
    "strictInterl" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "some_coeff_pos" ":=" term :
  tactic

/-- Sequence form of `rr_pos_combo_nonneg_right_strict_interl`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_pos_combo_sequence_nonneg_right_strict_interl_named)
  "rr_pos_combo_sequence_nonneg_right_strict_interl" " using "
    "strictInterl" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "some_coeff_pos" ":=" term :
  tactic

/-- Closes `C a * f + C b * g ≠ 0 ∧ (C a * f + C b * g).Splits` from the same arguments as
`rr_pos_combo_nonneg_right_strict_interl`. -/
syntax (name := rr_pos_combo_nonneg_realrooted_named)
  "rr_pos_combo_nonneg_realrooted" " using "
    "strictInterl" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "some_coeff_pos" ":=" term :
  tactic

/-- Sequence form of `rr_pos_combo_nonneg_realrooted`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_pos_combo_sequence_nonneg_realrooted_named)
  "rr_pos_combo_sequence_nonneg_realrooted" " using "
    "strictInterl" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "some_coeff_pos" ":=" term :
  tactic

/-- Closes `C a * f + C b * g ≠ 0 ∧ (C a * f + C b * g).Splits` from
`strictInterl : StrictInterl f g`, the positive leading coefficients `left_pos_lc` and
`right_pos_lc`, and the strictly positive weights `left_coeff_pos : 0 < a` and
`right_coeff_pos : 0 < b`. -/
syntax (name := rr_pos_combo_positive_realrooted_named)
  "rr_pos_combo_positive_realrooted" " using "
    "strictInterl" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_pos" ":=" term ","
    "right_coeff_pos" ":=" term :
  tactic

/-- Sequence form of `rr_pos_combo_positive_realrooted`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_pos_combo_sequence_positive_realrooted_named)
  "rr_pos_combo_sequence_positive_realrooted" " using "
    "strictInterl" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_pos" ":=" term ","
    "right_coeff_pos" ":=" term :
  tactic

/-- Closes `PosComboRealRooted g f` from `pos_combo : PosComboRealRooted f g`. -/
syntax (name := rr_pos_combo_comm_named)
  "rr_pos_combo_comm" " using " "pos_combo" ":=" term :
  tactic

/-- Sequence form of `rr_pos_combo_comm`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_pos_combo_sequence_comm_named)
  "rr_pos_combo_sequence_comm" " using " "pos_combo" ":=" term :
  tactic

/-- Closes `PosComboRealRooted (reflect N f) (reflect N g)` from
`pos_combo : PosComboRealRooted f g` and the degree bounds `left_degree_bound : f.natDegree ≤ N` and
`right_degree_bound : g.natDegree ≤ N`. -/
syntax (name := rr_pos_combo_reflect_named)
  "rr_pos_combo_reflect" " using "
    "pos_combo" ":=" term ","
    "left_degree_bound" ":=" term ","
    "right_degree_bound" ":=" term :
  tactic

/-- Closes `PosComboRealRooted (reflect N f) (reflect N g) ↔ PosComboRealRooted f g` from the degree
bounds `left_degree_bound : f.natDegree ≤ N` and `right_degree_bound : g.natDegree ≤ N`. -/
syntax (name := rr_pos_combo_reflect_iff_named)
  "rr_pos_combo_reflect_iff" " using "
    "left_degree_bound" ":=" term ","
    "right_degree_bound" ":=" term :
  tactic

/-- Closes `f + g ≠ 0 ∧ (f + g).Splits` from `pos_combo : PosComboRealRooted f g`. -/
syntax (name := rr_pos_combo_add_realrooted_named)
  "rr_pos_combo_add_realrooted" " using " "pos_combo" ":=" term :
  tactic

/-- Sequence form of `rr_pos_combo_add_realrooted`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_pos_combo_sequence_add_realrooted_named)
  "rr_pos_combo_sequence_add_realrooted" " using " "pos_combo" ":=" term :
  tactic

/-- Closes `PosComboRealRooted f.divX g.divX` from `pos_combo : PosComboRealRooted f g` and the
vanishing constant coefficients `left_const_zero` and `right_const_zero`. -/
syntax (name := rr_pos_combo_divX_named)
  "rr_pos_combo_divX" " using "
    "pos_combo" ":=" term ","
    "left_const_zero" ":=" term ","
    "right_const_zero" ":=" term :
  tactic

/-- Closes `f + C μ * g ≠ 0 ∧ (f + C μ * g).Splits` from `pos_combo : PosComboRealRooted f g` and
`parameter_pos : 0 < μ`. -/
syntax (name := rr_pos_combo_add_right_realrooted_named)
  "rr_pos_combo_add_right_realrooted" " using "
    "pos_combo" ":=" term ","
    "parameter_pos" ":=" term :
  tactic

/-- Sequence form of `rr_pos_combo_add_right_realrooted`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_pos_combo_sequence_add_right_realrooted_named)
  "rr_pos_combo_sequence_add_right_realrooted" " using "
    "pos_combo" ":=" term ","
    "parameter_pos" ":=" term :
  tactic

/-- Closes `C lam * f + g ≠ 0 ∧ (C lam * f + g).Splits` from `pos_combo : PosComboRealRooted f g`
and `parameter_pos : 0 < lam`. -/
syntax (name := rr_pos_combo_add_left_realrooted_named)
  "rr_pos_combo_add_left_realrooted" " using "
    "pos_combo" ":=" term ","
    "parameter_pos" ":=" term :
  tactic

/-- Sequence form of `rr_pos_combo_add_left_realrooted`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_pos_combo_sequence_add_left_realrooted_named)
  "rr_pos_combo_sequence_add_left_realrooted" " using "
    "pos_combo" ":=" term ","
    "parameter_pos" ":=" term :
  tactic

/-- Closes `PosComboRealRooted f g` from `strictInterl : StrictInterl f g` and the positive leading
coefficients `left_pos_lc` and `right_pos_lc`. -/
syntax (name := rr_pos_combo_of_strict_interl_named)
  "rr_pos_combo_of_strict_interl" " using "
    "strictInterl" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Sequence form of `rr_pos_combo_of_strict_interl`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_pos_combo_sequence_of_strict_interl_named)
  "rr_pos_combo_sequence_of_strict_interl" " using "
    "strictInterl" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Closes `PosComboRealRooted f g ↔ ∀ μ > 0, f + C μ * g ≠ 0 ∧ (f + C μ * g).Splits`. -/
syntax (name := rr_pos_combo_iff_add_right_named)
  "rr_pos_combo_iff_add_right" :
  tactic

/-- Closes `PosComboRealRooted f g ↔ ∀ lam > 0, C lam * f + g ≠ 0 ∧ (C lam * f + g).Splits`. -/
syntax (name := rr_pos_combo_iff_add_left_named)
  "rr_pos_combo_iff_add_left" :
  tactic

/-- Closes `PosComboRealRooted f g` from `family`, which says that `f + C μ * g` is real-rooted for
every `μ > 0`. -/
syntax (name := rr_pos_combo_of_add_right_named)
  "rr_pos_combo_of_add_right" " using " "family" ":=" term :
  tactic

/-- Closes `PosComboRealRooted f g` from `family`, which says that `C lam * f + g` is real-rooted
for every `lam > 0`. -/
syntax (name := rr_pos_combo_of_add_left_named)
  "rr_pos_combo_of_add_left" " using " "family" ":=" term :
  tactic

/-- Closes `PosComboRealRooted f g` from a common left interleaver `h`, given by
`common_to_left : StrictInterl h f` and `common_to_right : StrictInterl h g`, and the positive
leading coefficients `left_pos_lc` and `right_pos_lc`. -/
syntax (name := rr_pos_combo_of_common_left_named)
  "rr_pos_combo_of_common_left" " using "
    "common_to_left" ":=" term ","
    "common_to_right" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Sequence form of `rr_pos_combo_of_common_left`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_pos_combo_sequence_of_common_left_named)
  "rr_pos_combo_sequence_of_common_left" " using "
    "common_to_left" ":=" term ","
    "common_to_right" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Closes `f ≠ 0 ∧ f.Splits` from `pos_combo : PosComboRealRooted f g`, the positive leading
coefficients `left_pos_lc` and `right_pos_lc`, and `same_degree : g.natDegree = f.natDegree`. -/
syntax (name := rr_pos_combo_left_same_degree_realrooted_named)
  "rr_pos_combo_left_same_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term :
  tactic

/-- Sequence form of `rr_pos_combo_left_same_degree_realrooted`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_pos_combo_sequence_left_same_degree_realrooted_named)
  "rr_pos_combo_sequence_left_same_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term :
  tactic

/-- Closes `g ≠ 0 ∧ g.Splits` from `pos_combo : PosComboRealRooted f g`, the positive leading
coefficients `left_pos_lc` and `right_pos_lc`, and `same_degree : g.natDegree = f.natDegree`. -/
syntax (name := rr_pos_combo_right_same_degree_realrooted_named)
  "rr_pos_combo_right_same_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term :
  tactic

/-- Sequence form of `rr_pos_combo_right_same_degree_realrooted`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_pos_combo_sequence_right_same_degree_realrooted_named)
  "rr_pos_combo_sequence_right_same_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term :
  tactic

/-- Closes real-rootedness of `C (1 - β) * f + C β * g` on the closed segment from
`pos_combo : PosComboRealRooted f g`, the real-rootedness of both endpoints (`left_ne_zero`,
`left_splits`, `right_ne_zero`, `right_splits`), and `parameter_nonneg : 0 ≤ β` and
`parameter_le_one : β ≤ 1`. -/
syntax (name := rr_pos_combo_closed_segment_realrooted_named)
  "rr_pos_combo_closed_segment_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_ne_zero" ":=" term ","
    "left_splits" ":=" term ","
    "right_ne_zero" ":=" term ","
    "right_splits" ":=" term ","
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term :
  tactic

/-- Closes real-rootedness of `C (1 - β) * f + C β * g` on the closed segment from
`pos_combo : PosComboRealRooted f g`, the positive leading coefficients,
`same_degree : g.natDegree = f.natDegree`, and `parameter_nonneg : 0 ≤ β` and
`parameter_le_one : β ≤ 1`. -/
syntax (name := rr_pos_combo_closed_segment_same_degree_realrooted_named)
  "rr_pos_combo_closed_segment_same_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term :
  tactic

/-- Sequence form of `rr_pos_combo_closed_segment_same_degree_realrooted`: the same certificate for
every index `i : Nat`. -/
syntax (name := rr_pos_combo_sequence_closed_segment_same_degree_realrooted_named)
  "rr_pos_combo_sequence_closed_segment_same_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term :
  tactic

/-- Closes `PosComboRealRooted f g` by the Aissen--Schoenberg--Whitney theorem, from
`nonzero : ∀ z ≥ 0, f + C z * g ≠ 0` and `pf`, which says that the coefficient sequence of each
`f + C z * g` with `z ≥ 0` is a Polya frequency sequence. -/
syntax (name := rr_pos_combo_asw_right_pencil_named)
  "rr_pos_combo_asw_right_pencil" " using "
    "nonzero" ":=" term ","
    "pf" ":=" term :
  tactic

/-- Variant of `rr_pos_combo_asw_right_pencil` whose Polya frequency hypothesis is supplied as
`tnn`, total nonnegativity of the coefficient sequences. -/
syntax (name := rr_pos_combo_asw_right_pencil_tnn_named)
  "rr_pos_combo_asw_right_pencil_tnn" " using "
    "nonzero" ":=" term ","
    "tnn" ":=" term :
  tactic

/-- Closes `PosComboRealRooted (f + C μ₁ * g) (f + C μ₂ * g)` from
`pos_combo : PosComboRealRooted f g` and the positivity of `first_parameter_pos : 0 < μ₁` and
`second_parameter_pos : 0 < μ₂`. -/
syntax (name := rr_pos_combo_family_pair_right_named)
  "rr_pos_combo_family_pair_right" " using "
    "pos_combo" ":=" term ","
    "first_parameter_pos" ":=" term ","
    "second_parameter_pos" ":=" term :
  tactic

/-- Closes `PosComboRealRooted (C lam₁ * f + g) (C lam₂ * f + g)` from
`pos_combo : PosComboRealRooted f g` and the positivity of `first_parameter_pos : 0 < lam₁` and
`second_parameter_pos : 0 < lam₂`. -/
syntax (name := rr_pos_combo_family_pair_left_named)
  "rr_pos_combo_family_pair_left" " using "
    "pos_combo" ":=" term ","
    "first_parameter_pos" ":=" term ","
    "second_parameter_pos" ":=" term :
  tactic

/-- Closes `PosComboRealRooted (C (1 - β₁) * f + C β₁ * g) (C (1 - β₂) * f + C β₂ * g)` from
`pos_combo : PosComboRealRooted f g` and interior parameters, given by `first_parameter_pos`,
`first_parameter_lt_one`, `second_parameter_pos` and `second_parameter_lt_one`. -/
syntax (name := rr_pos_combo_family_pair_segment_named)
  "rr_pos_combo_family_pair_segment" " using "
    "pos_combo" ":=" term ","
    "first_parameter_pos" ":=" term ","
    "first_parameter_lt_one" ":=" term ","
    "second_parameter_pos" ":=" term ","
    "second_parameter_lt_one" ":=" term :
  tactic

/-- Closes the statement that `f + C μ₁ * g` and `f + C μ₂ * g` have no common root, from
`no_common_roots` for `f` and `g` and `parameters_ne : μ₁ ≠ μ₂`. -/
syntax (name := rr_pos_combo_family_no_common_right_named)
  "rr_pos_combo_family_no_common_right" " using "
    "no_common_roots" ":=" term ","
    "parameters_ne" ":=" term :
  tactic

/-- Closes the statement that `C lam₁ * f + g` and `C lam₂ * f + g` have no common root, from
`no_common_roots` for `f` and `g` and `parameters_ne : lam₁ ≠ lam₂`. -/
syntax (name := rr_pos_combo_family_no_common_left_named)
  "rr_pos_combo_family_no_common_left" " using "
    "no_common_roots" ":=" term ","
    "parameters_ne" ":=" term :
  tactic

/-- Closes `IsCoprime (f + C μ₁ * g) (f + C μ₂ * g)` from `pos_combo : PosComboRealRooted f g`,
`no_common_roots` for `f` and `g`, `first_parameter_pos : 0 < μ₁` and `parameters_ne : μ₁ ≠ μ₂`. -/
syntax (name := rr_pos_combo_family_isCoprime_right_named)
  "rr_pos_combo_family_isCoprime_right" " using "
    "pos_combo" ":=" term ","
    "no_common_roots" ":=" term ","
    "first_parameter_pos" ":=" term ","
    "parameters_ne" ":=" term :
  tactic

/-- Closes `IsCoprime (C lam₁ * f + g) (C lam₂ * f + g)` from `pos_combo : PosComboRealRooted f g`,
`no_common_roots` for `f` and `g`, `first_parameter_pos : 0 < lam₁` and
`parameters_ne : lam₁ ≠ lam₂`. -/
syntax (name := rr_pos_combo_family_isCoprime_left_named)
  "rr_pos_combo_family_isCoprime_left" " using "
    "pos_combo" ":=" term ","
    "no_common_roots" ":=" term ","
    "first_parameter_pos" ":=" term ","
    "parameters_ne" ":=" term :
  tactic

/-- Closes the statement that two distinct closed-segment members `C (1 - β₁) * f + C β₁ * g` and
`C (1 - β₂) * f + C β₂ * g` have no common root, from `no_common_roots` for `f` and `g` and
`parameters_ne : β₁ ≠ β₂`. -/
syntax (name := rr_pos_combo_family_no_common_segment_named)
  "rr_pos_combo_family_no_common_segment" " using "
    "no_common_roots" ":=" term ","
    "parameters_ne" ":=" term :
  tactic

/-- Closes `IsCoprime (C (1 - β₁) * f + C β₁ * g) (C (1 - β₂) * f + C β₂ * g)` from
`pos_combo : PosComboRealRooted f g`, `no_common_roots` for `f` and `g`, an interior first parameter
(`first_parameter_pos`, `first_parameter_lt_one`) and `parameters_ne : β₁ ≠ β₂`. -/
syntax (name := rr_pos_combo_family_isCoprime_segment_named)
  "rr_pos_combo_family_isCoprime_segment" " using "
    "pos_combo" ":=" term ","
    "no_common_roots" ":=" term ","
    "first_parameter_pos" ":=" term ","
    "first_parameter_lt_one" ":=" term ","
    "parameters_ne" ":=" term :
  tactic

/-- Closes `PosComboRealRooted f g` from `pos_combo : PosComboRealRooted (d * f) (d * g)`. -/
syntax (name := rr_pos_combo_mul_common_factor_named)
  "rr_pos_combo_mul_common_factor" " using " "pos_combo" ":=" term :
  tactic

/-- Closes `PosComboRealRooted f g` from
`pos_combo : PosComboRealRooted ((X - C r) * f) ((X - C r) * g)`. -/
syntax (name := rr_pos_combo_mul_X_sub_C_named)
  "rr_pos_combo_mul_X_sub_C" " using " "pos_combo" ":=" term :
  tactic

/-- Closes `StrictInterl (C a * f + C b * g) g` from `strictInterl : StrictInterl f g`, the positive
leading coefficients, and the strictly positive weights `left_coeff_pos : 0 < a` and
`right_coeff_pos : 0 < b`. -/
syntax (name := rr_pos_combo_convex_right_strict_interl_named)
  "rr_pos_combo_convex_right_strict_interl" " using "
    "strictInterl" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_pos" ":=" term ","
    "right_coeff_pos" ":=" term :
  tactic

/-- Closes `StrictInterl f (C a * f + C b * g)` from `strictInterl : StrictInterl f g`, the positive
leading coefficients, the bounds `left_coeff_nonneg : 0 ≤ a` and `right_coeff_nonneg : 0 ≤ b`, and
`some_coeff_pos : 0 < a ∨ 0 < b`. -/
syntax (name := rr_pos_combo_nonneg_left_strict_interl_named)
  "rr_pos_combo_nonneg_left_strict_interl" " using "
    "strictInterl" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_nonneg" ":=" term ","
    "right_coeff_nonneg" ":=" term ","
    "some_coeff_pos" ":=" term :
  tactic

/-- Closes `StrictInterl f (C a * f + C b * g)` from `strictInterl : StrictInterl f g`, the positive
leading coefficients, and the strictly positive weights `left_coeff_pos : 0 < a` and
`right_coeff_pos : 0 < b`. -/
syntax (name := rr_pos_combo_convex_left_strict_interl_named)
  "rr_pos_combo_convex_left_strict_interl" " using "
    "strictInterl" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_coeff_pos" ":=" term ","
    "right_coeff_pos" ":=" term :
  tactic

/-- Closes `StrictInterl f (C a * f + C b * g)` for `f = d * f'` and `g = d * g'` with a real-rooted
common factor `d` (`factor_ne_zero`, `factor_splits`, `left_factorization`, `right_factorization`),
from `reduced_strictInterl : StrictInterl f' g'`, positive leading coefficients of `f'` and `g'`,
and the positive weights `left_coeff_pos` and `right_coeff_pos`. -/
syntax (name := rr_pos_combo_convex_left_common_factor_strict_interl_named)
  "rr_pos_combo_convex_left_common_factor_strict_interl" " using "
    "factor_ne_zero" ":=" term ","
    "factor_splits" ":=" term ","
    "left_factorization" ":=" term ","
    "right_factorization" ":=" term ","
    "reduced_strictInterl" ":=" term ","
    "reduced_left_pos_lc" ":=" term ","
    "reduced_right_pos_lc" ":=" term ","
    "left_coeff_pos" ":=" term ","
    "right_coeff_pos" ":=" term :
  tactic

/-- Closes `g ≠ 0 ∧ g.Splits` from `pos_combo : PosComboRealRooted f g`, the positive leading
coefficients, and `degree_le : f.natDegree ≤ g.natDegree`. -/
syntax (name := rr_pos_combo_right_natDegree_le_realrooted_named)
  "rr_pos_combo_right_natDegree_le_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "degree_le" ":=" term :
  tactic

/-- Closes `f ≠ 0 ∧ f.Splits` from `pos_combo : PosComboRealRooted f g`, the positive leading
coefficients, and `degree_le : g.natDegree ≤ f.natDegree`. -/
syntax (name := rr_pos_combo_left_natDegree_le_realrooted_named)
  "rr_pos_combo_left_natDegree_le_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "degree_le" ":=" term :
  tactic

/-- Closes `g ≠ 0 ∧ g.Splits` from `pos_combo : PosComboRealRooted f g`, the positive leading
coefficients, and `succ_degree : g.natDegree = f.natDegree + 1`. -/
syntax (name := rr_pos_combo_right_succ_degree_realrooted_named)
  "rr_pos_combo_right_succ_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Closes `f ≠ 0 ∧ f.Splits` from `pos_combo : PosComboRealRooted f g`, the positive leading
coefficients, and `succ_degree : g.natDegree = f.natDegree + 1`. -/
syntax (name := rr_pos_combo_left_succ_degree_realrooted_named)
  "rr_pos_combo_left_succ_degree_realrooted" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Closes `f.Splits` from `pos_combo : PosComboRealRooted f g`, the positive leading coefficients,
and `succ_degree : g.natDegree = f.natDegree + 1`. -/
syntax (name := rr_pos_combo_left_succ_degree_splits_named)
  "rr_pos_combo_left_succ_degree_splits" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Closes `g.Splits` from `pos_combo : PosComboRealRooted f g`, the positive leading coefficients,
and `succ_degree : f.natDegree = g.natDegree + 1`. -/
syntax (name := rr_pos_combo_right_succ_degree_splits_named)
  "rr_pos_combo_right_succ_degree_splits" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Closes `f.Splits` at the lower-degree endpoint of a closed-segment family, from the positive
leading coefficients, `pos_combo : PosComboRealRooted f g` and
`succ_degree : g.natDegree = f.natDegree + 1`. -/
syntax (name := rr_pos_combo_left_closed_segment_succ_degree_splits_named)
  "rr_pos_combo_left_closed_segment_succ_degree_splits" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Closes `g.Splits` at the endpoint `g` of a closed-segment family, from the positive leading
coefficients, `pos_combo : PosComboRealRooted f g` and
`succ_degree : f.natDegree = g.natDegree + 1`. -/
syntax (name := rr_pos_combo_right_closed_segment_succ_degree_splits_named)
  "rr_pos_combo_right_closed_segment_succ_degree_splits" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Closes `f ≠ 0 ∧ f.Splits` at the lower-degree endpoint of a closed-segment family, from the
positive leading coefficients, `pos_combo : PosComboRealRooted f g` and
`succ_degree : g.natDegree = f.natDegree + 1`. -/
syntax (name := rr_pos_combo_left_closed_segment_succ_degree_realrooted_named)
  "rr_pos_combo_left_closed_segment_succ_degree_realrooted" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Closes `g ≠ 0 ∧ g.Splits` at the endpoint `g` of a closed-segment family, from the positive
leading coefficients, `pos_combo : PosComboRealRooted f g` and
`succ_degree : f.natDegree = g.natDegree + 1`. -/
syntax (name := rr_pos_combo_right_closed_segment_succ_degree_realrooted_named)
  "rr_pos_combo_right_closed_segment_succ_degree_realrooted" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_pos_combo_nonneg_right_strict_interl using
        strictInterl := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        some_coeff_pos := $hab:term) =>
      `(tactic|
        exact RealRooted.StrictInterl.nonneg_combo_right
          $hfg $hfpos $hgpos $ha $hb $hab)
  | `(tactic|
      rr_pos_combo_sequence_nonneg_right_strict_interl using
        strictInterl := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        some_coeff_pos := $hab:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_nonneg_right_strictInterl
          $hfg $hfpos $hgpos $ha $hb $hab)
  | `(tactic|
      rr_pos_combo_nonneg_realrooted using
        strictInterl := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        some_coeff_pos := $hab:term) =>
      `(tactic|
        exact RealRooted.StrictInterl.isRealRooted_nonneg_combo
          $hfg $hfpos $hgpos $ha $hb $hab)
  | `(tactic|
      rr_pos_combo_sequence_nonneg_realrooted using
        strictInterl := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        some_coeff_pos := $hab:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_nonneg_realrooted
          $hfg $hfpos $hgpos $ha $hb $hab)
  | `(tactic|
      rr_pos_combo_positive_realrooted using
        strictInterl := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_pos := $ha:term,
        right_coeff_pos := $hb:term) =>
      `(tactic|
        exact RealRooted.StrictInterl.isRealRooted_pos_combo
          $hfg $hfpos $hgpos $ha $hb)
  | `(tactic|
      rr_pos_combo_sequence_positive_realrooted using
        strictInterl := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_pos := $ha:term,
        right_coeff_pos := $hb:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_positive_realrooted
          $hfg $hfpos $hgpos $ha $hb)
  | `(tactic| rr_pos_combo_comm using pos_combo := $hfg:term) =>
      `(tactic| exact RealRooted.PosComboRealRooted.comm $hfg)
  | `(tactic| rr_pos_combo_sequence_comm using pos_combo := $hfg:term) =>
      `(tactic| exact RealRooted.Tactic.posCombo_sequence_comm $hfg)
  | `(tactic|
      rr_pos_combo_reflect using
        pos_combo := $hfg:term,
        left_degree_bound := $hfN:term,
        right_degree_bound := $hgN:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.reflect_of_natDegree_le
          $hfg $hfN $hgN)
  | `(tactic|
      rr_pos_combo_reflect_iff using
        left_degree_bound := $hfN:term,
        right_degree_bound := $hgN:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.reflect_iff_natDegree_le
          $hfN $hgN)
  | `(tactic| rr_pos_combo_add_realrooted using pos_combo := $hfg:term) =>
      `(tactic| exact RealRooted.PosComboRealRooted.isRealRooted_add $hfg)
  | `(tactic| rr_pos_combo_sequence_add_realrooted using pos_combo := $hfg:term) =>
      `(tactic| exact RealRooted.Tactic.posCombo_sequence_add_realrooted $hfg)
  | `(tactic|
      rr_pos_combo_divX using
        pos_combo := $hfg:term,
        left_const_zero := $hf0:term,
        right_const_zero := $hg0:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.divX_of_coeff_zero
          $hfg $hf0 $hg0)
  | `(tactic|
      rr_pos_combo_add_right_realrooted using
        pos_combo := $hfg:term,
        parameter_pos := $hμ:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_add_right $hfg $hμ)
  | `(tactic|
      rr_pos_combo_sequence_add_right_realrooted using
        pos_combo := $hfg:term,
        parameter_pos := $hμ:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_add_right_realrooted
          $hfg $hμ)
  | `(tactic|
      rr_pos_combo_add_left_realrooted using
        pos_combo := $hfg:term,
        parameter_pos := $hlam:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_add_left $hfg $hlam)
  | `(tactic|
      rr_pos_combo_sequence_add_left_realrooted using
        pos_combo := $hfg:term,
        parameter_pos := $hlam:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_add_left_realrooted
          $hfg $hlam)
  | `(tactic|
      rr_pos_combo_of_strict_interl using
        strictInterl := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.of_strictInterl
          $hfg $hfpos $hgpos)
  | `(tactic|
      rr_pos_combo_sequence_of_strict_interl using
        strictInterl := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_of_strictInterl
          $hfg $hfpos $hgpos)
  | `(tactic| rr_pos_combo_iff_add_right) =>
      `(tactic| exact RealRooted.PosComboRealRooted.iff_add_right)
  | `(tactic| rr_pos_combo_iff_add_left) =>
      `(tactic| exact RealRooted.PosComboRealRooted.iff_add_left)
  | `(tactic| rr_pos_combo_of_add_right using family := $hfamily:term) =>
      `(tactic| exact RealRooted.PosComboRealRooted.of_add_right $hfamily)
  | `(tactic| rr_pos_combo_of_add_left using family := $hfamily:term) =>
      `(tactic| exact RealRooted.PosComboRealRooted.of_add_left $hfamily)
  | `(tactic|
      rr_pos_combo_of_common_left using
        common_to_left := $hhf:term,
        common_to_right := $hhg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.of_commonLeftInterleaver
          $hhf $hhg $hfpos $hgpos)
  | `(tactic|
      rr_pos_combo_sequence_of_common_left using
        common_to_left := $hhf:term,
        common_to_right := $hhg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_of_common_left
          $hhf $hhg $hfpos $hgpos)
  | `(tactic|
      rr_pos_combo_left_same_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_left_of_sameDegree
          $hfg $hfpos $hgpos $hdeg)
  | `(tactic|
      rr_pos_combo_sequence_left_same_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_left_same_degree_realrooted
          $hfg $hfpos $hgpos $hdeg)
  | `(tactic|
      rr_pos_combo_right_same_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_right_of_sameDegree
          $hfg $hfpos $hgpos $hdeg)
  | `(tactic|
      rr_pos_combo_sequence_right_same_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sequence_right_same_degree_realrooted
          $hfg $hfpos $hgpos $hdeg)
  | `(tactic|
      rr_pos_combo_closed_segment_realrooted using
        pos_combo := $hfg:term,
        left_ne_zero := $hfne:term,
        left_splits := $hfsplits:term,
        right_ne_zero := $hgne:term,
        right_splits := $hgsplits:term,
        parameter_nonneg := $hβ0:term,
        parameter_le_one := $hβ1:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_closed_segment
          $hfg $hfne $hfsplits $hgne $hgsplits $hβ0 $hβ1)
  | `(tactic|
      rr_pos_combo_closed_segment_same_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term,
        parameter_nonneg := $hβ0:term,
        parameter_le_one := $hβ1:term) =>
      `(tactic|
        exact
          RealRooted.PosComboRealRooted.isRealRooted_closed_segment_of_sameDegree
            $hfg $hfpos $hgpos $hdeg $hβ0 $hβ1)
  | `(tactic|
      rr_pos_combo_sequence_closed_segment_same_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term,
        parameter_nonneg := $hβ0:term,
        parameter_le_one := $hβ1:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.posCombo_sequence_closed_segment_same_degree_realrooted
            $hfg $hfpos $hgpos $hdeg $hβ0 $hβ1)
  | `(tactic|
      rr_pos_combo_asw_right_pencil using
        nonzero := $hne:term,
        pf := $hpf:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.of_aissenSchoenbergWhitney_right_pencil $hne $hpf)
  | `(tactic|
      rr_pos_combo_asw_right_pencil_tnn using
        nonzero := $hne:term,
        tnn := $htnn:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.of_aissenSchoenbergWhitney_right_pencil $hne $htnn)
  | `(tactic|
      rr_pos_combo_family_pair_right using
        pos_combo := $hfg:term,
        first_parameter_pos := $hμ₁:term,
        second_parameter_pos := $hμ₂:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_pair_right
          $hfg $hμ₁ $hμ₂)
  | `(tactic|
      rr_pos_combo_family_pair_left using
        pos_combo := $hfg:term,
        first_parameter_pos := $hlam₁:term,
        second_parameter_pos := $hlam₂:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_pair_left
          $hfg $hlam₁ $hlam₂)
  | `(tactic|
      rr_pos_combo_family_pair_segment using
        pos_combo := $hfg:term,
        first_parameter_pos := $hβ₁0:term,
        first_parameter_lt_one := $hβ₁1:term,
        second_parameter_pos := $hβ₂0:term,
        second_parameter_lt_one := $hβ₂1:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_pair_segment
          $hfg $hβ₁0 $hβ₁1 $hβ₂0 $hβ₂1)
  | `(tactic|
      rr_pos_combo_family_no_common_right using
        no_common_roots := $hno:term,
        parameters_ne := $hμ:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_no_common_right $hno $hμ)
  | `(tactic|
      rr_pos_combo_family_no_common_left using
        no_common_roots := $hno:term,
        parameters_ne := $hlam:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_no_common_left $hno $hlam)
  | `(tactic|
      rr_pos_combo_family_isCoprime_right using
        pos_combo := $hfg:term,
        no_common_roots := $hno:term,
        first_parameter_pos := $hμ₁:term,
        parameters_ne := $hμ:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_isCoprime_right
          $hfg $hno $hμ₁ $hμ)
  | `(tactic|
      rr_pos_combo_family_isCoprime_left using
        pos_combo := $hfg:term,
        no_common_roots := $hno:term,
        first_parameter_pos := $hlam₁:term,
        parameters_ne := $hlam:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_isCoprime_left
          $hfg $hno $hlam₁ $hlam)
  | `(tactic|
      rr_pos_combo_family_no_common_segment using
        no_common_roots := $hno:term,
        parameters_ne := $hβ:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_no_common_segment $hno $hβ)
  | `(tactic|
      rr_pos_combo_family_isCoprime_segment using
        pos_combo := $hfg:term,
        no_common_roots := $hno:term,
        first_parameter_pos := $hβ₁0:term,
        first_parameter_lt_one := $hβ₁1:term,
        parameters_ne := $hβ:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.family_isCoprime_segment
          $hfg $hno $hβ₁0 $hβ₁1 $hβ)
  | `(tactic| rr_pos_combo_mul_common_factor using pos_combo := $hfg:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.of_mul_common_factor $hfg)
  | `(tactic| rr_pos_combo_mul_X_sub_C using pos_combo := $hfg:term) =>
      `(tactic| exact RealRooted.PosComboRealRooted.of_mul_X_sub_C $hfg)
  | `(tactic|
      rr_pos_combo_convex_right_strict_interl using
        strictInterl := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_pos := $ha:term,
        right_coeff_pos := $hb:term) =>
      `(tactic|
        exact RealRooted.StrictInterl.convex_right
          $hfg $hfpos $hgpos $ha $hb)
  | `(tactic|
      rr_pos_combo_nonneg_left_strict_interl using
        strictInterl := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_nonneg := $ha:term,
        right_coeff_nonneg := $hb:term,
        some_coeff_pos := $hab:term) =>
      `(tactic|
        exact RealRooted.StrictInterl.nonneg_combo_left
          $hfg $hfpos $hgpos $ha $hb $hab)
  | `(tactic|
      rr_pos_combo_convex_left_strict_interl using
        strictInterl := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_coeff_pos := $ha:term,
        right_coeff_pos := $hb:term) =>
      `(tactic|
        exact RealRooted.StrictInterl.convex_left
          $hfg $hfpos $hgpos $ha $hb)
  | `(tactic|
      rr_pos_combo_convex_left_common_factor_strict_interl using
        factor_ne_zero := $hdne:term,
        factor_splits := $hdsplits:term,
        left_factorization := $hfdef:term,
        right_factorization := $hgdef:term,
        reduced_strictInterl := $hfg:term,
        reduced_left_pos_lc := $hfpos:term,
        reduced_right_pos_lc := $hgpos:term,
        left_coeff_pos := $ha:term,
        right_coeff_pos := $hb:term) =>
      `(tactic|
        exact RealRooted.StrictInterl.convex_left_of_common_factor
          $hdne $hdsplits $hfdef $hgdef $hfg $hfpos $hgpos
          $ha $hb)
  | `(tactic|
      rr_pos_combo_right_natDegree_le_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        degree_le := $hdeg:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_right_of_natDegree_le
          $hfg $hfpos $hgpos $hdeg)
  | `(tactic|
      rr_pos_combo_left_natDegree_le_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        degree_le := $hdeg:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_left_of_natDegree_le
          $hfg $hfpos $hgpos $hdeg)
  | `(tactic|
      rr_pos_combo_right_succ_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_right_of_succDegree
          $hfg $hfpos $hgpos $hsucc)
  | `(tactic|
      rr_pos_combo_left_succ_degree_realrooted using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.isRealRooted_left_of_succDegree
          $hfg $hfpos $hgpos $hsucc)
  | `(tactic|
      rr_pos_combo_left_succ_degree_splits using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.left_splits_of_succDegree
          $hfg $hfpos $hgpos $hsucc)
  | `(tactic|
      rr_pos_combo_right_succ_degree_splits using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.right_splits_of_succDegree
          $hfg $hfpos $hgpos $hsucc)
  | `(tactic|
      rr_pos_combo_left_closed_segment_succ_degree_splits using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.left_splits_of_succDegree
          $hfg $hfpos $hgpos $hsucc)
  | `(tactic|
      rr_pos_combo_right_closed_segment_succ_degree_splits using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.PosComboRealRooted.right_splits_of_succDegree
          $hfg $hfpos $hgpos $hsucc)
  | `(tactic|
      rr_pos_combo_left_closed_segment_succ_degree_realrooted using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.left_ne_zero_and_splits_closedSegment_of_succDegree
          $hfpos $hgpos $hfg $hsucc)
  | `(tactic|
      rr_pos_combo_right_closed_segment_succ_degree_realrooted using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.right_ne_zero_and_splits_closedSegment_of_succDegree
          $hfpos $hgpos $hfg $hsucc)

end Tactic
end RealRooted
namespace RealRooted
namespace Tactic

end Tactic
end RealRooted
