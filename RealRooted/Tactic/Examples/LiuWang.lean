import RealRooted.Tactic.LiuWang

/-!
# `rr_liu_wang` examples

Abstract smoke tests for the generalized Liu-Wang dispatcher tactics.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg_lo : f.natDegree ≤ (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree)
    (hdeg_hi :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang using
    hgf, hg_pos, hl_inter, hl_pos, hl_nonpos, hF_pos, hdeg_lo, hdeg_hi, hno,
    hb_nonpos

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg_lo : f.natDegree ≤ (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree)
    (hdeg_hi :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    tail_interlaces := hl_inter,
    tail_pos_lc := hl_pos,
    tail_nonpos := hl_nonpos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno,
    head_nonpos := hb_nonpos

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg_lo : f.natDegree ≤ (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree)
    (hdeg_hi :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang_strict using
    hgf, hg_pos, hl_inter, hl_pos, hl_nonpos, hF_pos, hdeg_lo, hdeg_hi, hno,
    hb_neg

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg_lo : f.natDegree ≤ (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree)
    (hdeg_hi :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang_strict using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    tail_interlaces := hl_inter,
    tail_pos_lc := hl_pos,
    tail_nonpos := hl_nonpos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno,
    head_neg := hb_neg

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg : (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang_strict_same using
    hgf, hg_pos, hl_inter, hl_pos, hl_nonpos, hF_pos, hdeg, hno, hb_neg

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg : (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang_strict_same using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    tail_interlaces := hl_inter,
    tail_pos_lc := hl_pos,
    tail_nonpos := hl_nonpos,
    target_pos_lc := hF_pos,
    degree := hdeg,
    no_common_roots := hno,
    head_neg := hb_neg

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang_strict_succ using
    hgf, hg_pos, hl_inter, hl_pos, hl_nonpos, hF_pos, hdeg, hno, hb_neg

example {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  rr_liu_wang_strict_succ using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    tail_interlaces := hl_inter,
    tail_pos_lc := hl_pos,
    tail_nonpos := hl_nonpos,
    target_pos_lc := hF_pos,
    degree := hdeg,
    no_common_roots := hno,
    head_neg := hb_neg

end Tactic
end RealRooted
