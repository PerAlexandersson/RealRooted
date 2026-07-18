import RealRooted.Tactic.PosCombo

open Polynomial

namespace RealRooted
namespace Tactic

example {f g : ℝ[X]} {a b : ℝ}
    (hfg : Prec f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hab : 0 < a ∨ 0 < b) :
    Prec (C a * f + C b * g) g := by
  rr_pos_combo_nonneg_right_prec using
    prec := hfg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_coeff_nonneg := ha,
    right_coeff_nonneg := hb,
    some_coeff_pos := hab

example {f g : ℝ[X]} {a b : ℝ}
    (hfg : Prec f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hab : 0 < a ∨ 0 < b) :
    ((C a * f + C b * g) ≠ 0 ∧ (C a * f + C b * g).Splits) := by
  rr_pos_combo_nonneg_realrooted using
    prec := hfg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_coeff_nonneg := ha,
    right_coeff_nonneg := hb,
    some_coeff_pos := hab

example {f g : ℝ[X]} {a b : ℝ}
    (hfg : Prec f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (ha : 0 < a)
    (hb : 0 < b) :
    ((C a * f + C b * g) ≠ 0 ∧ (C a * f + C b * g).Splits) := by
  rr_pos_combo_positive_realrooted using
    prec := hfg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_coeff_pos := ha,
    right_coeff_pos := hb

example {f g : ℝ[X]} (hfg : PosComboRealRooted f g) :
    RealRooted.PosComboHyp f g := by
  rr_pos_combo_to_hyp using pos_combo := hfg

example {f g : ℝ[X]} (hfg : PosComboRealRooted f g) :
    PosComboRealRooted g f := by
  rr_pos_combo_comm using pos_combo := hfg

example {f g : ℝ[X]} {N : ℕ}
    (hfg : PosComboRealRooted f g)
    (hfN : f.natDegree ≤ N)
    (hgN : g.natDegree ≤ N) :
    PosComboRealRooted (reflect N f) (reflect N g) := by
  rr_pos_combo_reflect using
    pos_combo := hfg,
    left_degree_bound := hfN,
    right_degree_bound := hgN

example {f g : ℝ[X]} {N : ℕ}
    (hfN : f.natDegree ≤ N)
    (hgN : g.natDegree ≤ N) :
    PosComboRealRooted (reflect N f) (reflect N g) ↔ PosComboRealRooted f g := by
  rr_pos_combo_reflect_iff using
    left_degree_bound := hfN,
    right_degree_bound := hgN

example {f g : ℝ[X]} (hfg : PosComboRealRooted f g) :
    ((f + g) ≠ 0 ∧ (f + g).Splits) := by
  rr_pos_combo_add_realrooted using pos_combo := hfg

example {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf0 : f.coeff 0 = 0)
    (hg0 : g.coeff 0 = 0) :
    PosComboRealRooted f.divX g.divX := by
  rr_pos_combo_divX using
    pos_combo := hfg,
    left_const_zero := hf0,
    right_const_zero := hg0

example {f g : ℝ[X]} {μ : ℝ}
    (hfg : PosComboRealRooted f g)
    (hμ : 0 < μ) :
    ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits) := by
  rr_pos_combo_add_right_realrooted using pos_combo := hfg, parameter_pos := hμ

example {f g : ℝ[X]} {lam : ℝ}
    (hfg : PosComboRealRooted f g)
    (hlam : 0 < lam) :
    ((C lam * f + g) ≠ 0 ∧ (C lam * f + g).Splits) := by
  rr_pos_combo_add_left_realrooted using pos_combo := hfg, parameter_pos := hlam

example {f g : ℝ[X]}
    (hfg : Prec f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    PosComboRealRooted f g := by
  rr_pos_combo_of_prec using
    prec := hfg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

example {f g : ℝ[X]} :
    PosComboRealRooted f g ↔
      ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits) := by
  rr_pos_combo_iff_add_right

example {f g : ℝ[X]} :
    PosComboRealRooted f g ↔
      ∀ {lam : ℝ}, 0 < lam → ((C lam * f + g) ≠ 0 ∧
        (C lam * f + g).Splits) := by
  rr_pos_combo_iff_add_left

example {f g : ℝ[X]}
    (hfamily : ∀ {μ : ℝ}, 0 < μ →
      ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits)) :
    PosComboRealRooted f g := by
  rr_pos_combo_of_add_right using family := hfamily

example {f g : ℝ[X]}
    (hfamily : ∀ {lam : ℝ}, 0 < lam →
      ((C lam * f + g) ≠ 0 ∧ (C lam * f + g).Splits)) :
    PosComboRealRooted f g := by
  rr_pos_combo_of_add_left using family := hfamily

example {f g h : ℝ[X]}
    (hhf : Prec h f)
    (hhg : Prec h g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    PosComboRealRooted f g := by
  rr_pos_combo_of_common_left using
    common_to_left := hhf,
    common_to_right := hhg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos

example {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) :
    (f ≠ 0 ∧ f.Splits) := by
  rr_pos_combo_left_same_degree_realrooted using
    pos_combo := hfg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    same_degree := hdeg

example {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) :
    (g ≠ 0 ∧ g.Splits) := by
  rr_pos_combo_right_same_degree_realrooted using
    pos_combo := hfg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    same_degree := hdeg

example {f g : ℝ[X]} {β : ℝ}
    (hfg : PosComboRealRooted f g)
    (hf_ne : f ≠ 0)
    (hf_splits : f.Splits)
    (hg_ne : g ≠ 0)
    (hg_splits : g.Splits)
    (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) :
    ((C (1 - β) * f + C β * g) ≠ 0 ∧
      (C (1 - β) * f + C β * g).Splits) := by
  rr_pos_combo_closed_segment_realrooted using
    pos_combo := hfg,
    left_ne_zero := hf_ne,
    left_splits := hf_splits,
    right_ne_zero := hg_ne,
    right_splits := hg_splits,
    parameter_nonneg := hβ0,
    parameter_le_one := hβ1

example {f g : ℝ[X]} {β : ℝ}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) :
    ((C (1 - β) * f + C β * g) ≠ 0 ∧
      (C (1 - β) * f + C β * g).Splits) := by
  rr_pos_combo_closed_segment_same_degree_realrooted using
    pos_combo := hfg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    same_degree := hdeg,
    parameter_nonneg := hβ0,
    parameter_le_one := hβ1

example {f g : ℝ[X]}
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hne : ∀ {z : ℝ}, 0 ≤ z → f + C z * g ≠ 0)
    (hpf : ∀ {z : ℝ}, 0 ≤ z → IsPolyaFreqSeq (f + C z * g).coeff) :
    PosComboRealRooted f g := by
  rr_pos_combo_asw_right_pencil using asw := hASW, nonzero := hne, pf := hpf

example {f g : ℝ[X]}
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hne : ∀ {z : ℝ}, 0 ≤ z → f + C z * g ≠ 0)
    (htnn : ∀ {z : ℝ}, 0 ≤ z → IsPolyaFreqSeq (f + C z * g).coeff) :
    PosComboRealRooted f g := by
  rr_pos_combo_asw_right_pencil_tnn using
    asw := hASW,
    nonzero := hne,
    tnn := htnn

example {f g : ℝ[X]} {μ₁ μ₂ : ℝ}
    (hfg : PosComboRealRooted f g)
    (hμ₁ : 0 < μ₁)
    (hμ₂ : 0 < μ₂) :
    PosComboRealRooted (f + C μ₁ * g) (f + C μ₂ * g) := by
  rr_pos_combo_family_pair_right using
    pos_combo := hfg,
    first_parameter_pos := hμ₁,
    second_parameter_pos := hμ₂

example {f g : ℝ[X]} {lam₁ lam₂ : ℝ}
    (hfg : PosComboRealRooted f g)
    (hlam₁ : 0 < lam₁)
    (hlam₂ : 0 < lam₂) :
    PosComboRealRooted (C lam₁ * f + g) (C lam₂ * f + g) := by
  rr_pos_combo_family_pair_left using
    pos_combo := hfg,
    first_parameter_pos := hlam₁,
    second_parameter_pos := hlam₂

example {f g : ℝ[X]} {β₁ β₂ : ℝ}
    (hfg : PosComboRealRooted f g)
    (hβ₁0 : 0 < β₁)
    (hβ₁1 : β₁ < 1)
    (hβ₂0 : 0 < β₂)
    (hβ₂1 : β₂ < 1) :
    PosComboRealRooted (C (1 - β₁) * f + C β₁ * g)
      (C (1 - β₂) * f + C β₂ * g) := by
  rr_pos_combo_family_pair_segment using
    pos_combo := hfg,
    first_parameter_pos := hβ₁0,
    first_parameter_lt_one := hβ₁1,
    second_parameter_pos := hβ₂0,
    second_parameter_lt_one := hβ₂1

example {f g : ℝ[X]} {μ₁ μ₂ : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hμ : μ₁ ≠ μ₂) :
    ∀ r, (f + C μ₁ * g).IsRoot r → ¬ (f + C μ₂ * g).IsRoot r := by
  rr_pos_combo_family_no_common_right using
    no_common_roots := hno,
    parameters_ne := hμ

example {f g : ℝ[X]} {lam₁ lam₂ : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hlam : lam₁ ≠ lam₂) :
    ∀ r, (C lam₁ * f + g).IsRoot r → ¬ (C lam₂ * f + g).IsRoot r := by
  rr_pos_combo_family_no_common_left using
    no_common_roots := hno,
    parameters_ne := hlam

example {f g : ℝ[X]} {μ₁ μ₂ : ℝ}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hμ₁ : 0 < μ₁)
    (hμ : μ₁ ≠ μ₂) :
    IsCoprime (f + C μ₁ * g) (f + C μ₂ * g) := by
  rr_pos_combo_family_isCoprime_right using
    pos_combo := hfg,
    no_common_roots := hno,
    first_parameter_pos := hμ₁,
    parameters_ne := hμ

example {f g : ℝ[X]} {lam₁ lam₂ : ℝ}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hlam₁ : 0 < lam₁)
    (hlam : lam₁ ≠ lam₂) :
    IsCoprime (C lam₁ * f + g) (C lam₂ * f + g) := by
  rr_pos_combo_family_isCoprime_left using
    pos_combo := hfg,
    no_common_roots := hno,
    first_parameter_pos := hlam₁,
    parameters_ne := hlam

example {f g : ℝ[X]} {β₁ β₂ : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hβ : β₁ ≠ β₂) :
    ∀ r, (C (1 - β₁) * f + C β₁ * g).IsRoot r →
      ¬ (C (1 - β₂) * f + C β₂ * g).IsRoot r := by
  rr_pos_combo_family_no_common_segment using
    no_common_roots := hno,
    parameters_ne := hβ

example {f g : ℝ[X]} {β₁ β₂ : ℝ}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hβ₁0 : 0 < β₁)
    (hβ₁1 : β₁ < 1)
    (hβ : β₁ ≠ β₂) :
    IsCoprime (C (1 - β₁) * f + C β₁ * g)
      (C (1 - β₂) * f + C β₂ * g) := by
  rr_pos_combo_family_isCoprime_segment using
    pos_combo := hfg,
    no_common_roots := hno,
    first_parameter_pos := hβ₁0,
    first_parameter_lt_one := hβ₁1,
    parameters_ne := hβ

example {d f g : ℝ[X]}
    (hfg : PosComboRealRooted (d * f) (d * g)) :
    PosComboRealRooted f g := by
  rr_pos_combo_mul_common_factor using pos_combo := hfg

example {f g : ℝ[X]} {r : ℝ}
    (hfg : PosComboRealRooted ((X - C r) * f) ((X - C r) * g)) :
    PosComboRealRooted f g := by
  rr_pos_combo_mul_X_sub_C using pos_combo := hfg

example {f g : ℝ[X]} {a b : ℝ}
    (hfg : Prec f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (ha : 0 < a)
    (hb : 0 < b) :
    Prec (C a * f + C b * g) g := by
  rr_pos_combo_convex_right_prec using
    prec := hfg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_coeff_pos := ha,
    right_coeff_pos := hb

example {f g : ℝ[X]} {a b : ℝ}
    (hfg : Prec f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hab : 0 < a ∨ 0 < b)
    (hne : C a * f + C b * g ≠ 0)
    (hsplits : (C a * f + C b * g).Splits)
    (hcop : IsCoprime (C a * f) (C b * g)) :
    Prec f (C a * f + C b * g) := by
  rr_pos_combo_nonneg_left_prec using
    prec := hfg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_coeff_nonneg := ha,
    right_coeff_nonneg := hb,
    some_coeff_pos := hab,
    combo_ne_zero := hne,
    combo_splits := hsplits,
    coprime := hcop

example {f g : ℝ[X]} {a b : ℝ}
    (hfg : Prec f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (ha : 0 < a)
    (hb : 0 < b)
    (hne : C a * f + C b * g ≠ 0)
    (hsplits : (C a * f + C b * g).Splits)
    (hcop : IsCoprime (C a * f) (C b * g)) :
    Prec f (C a * f + C b * g) := by
  rr_pos_combo_convex_left_prec using
    prec := hfg,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_coeff_pos := ha,
    right_coeff_pos := hb,
    combo_ne_zero := hne,
    combo_splits := hsplits,
    coprime := hcop

example {d f g f' g' : ℝ[X]} {a b : ℝ}
    (hd_ne : d ≠ 0)
    (hd_splits : d.Splits)
    (hf_def : f = d * f')
    (hg_def : g = d * g')
    (hfg : Prec f' g')
    (hf_pos : HasPosLeadingCoeff f')
    (hg_pos : HasPosLeadingCoeff g')
    (ha : 0 < a)
    (hb : 0 < b)
    (hne : C a * f' + C b * g' ≠ 0)
    (hsplits : (C a * f' + C b * g').Splits)
    (hcop : IsCoprime (C a * f') (C b * g')) :
    Prec f (C a * f + C b * g) := by
  rr_pos_combo_convex_left_common_factor_prec using
    factor_ne_zero := hd_ne,
    factor_splits := hd_splits,
    left_factorization := hf_def,
    right_factorization := hg_def,
    reduced_prec := hfg,
    reduced_left_pos_lc := hf_pos,
    reduced_right_pos_lc := hg_pos,
    left_coeff_pos := ha,
    right_coeff_pos := hb,
    reduced_combo_ne_zero := hne,
    reduced_combo_splits := hsplits,
    reduced_coprime := hcop

end Tactic
end RealRooted
