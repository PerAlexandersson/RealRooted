import RealRooted.Tactic.Bezoutian

open Polynomial

namespace RealRooted
namespace Tactic

variable {p q : ℝ[X]} {n : Nat}

example
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hstrict : StrictInterlSameDegree p q) :
    (bezoutMatrix n q p).PosDef := by
  rr_bezout_pos_def_of_strict_interl_same_degree using
    left_pos_lc := hp_pos,
    right_pos_lc := hq_pos,
    left_degree := hp_deg,
    right_degree := hq_deg,
    strict_interl_same_degree := hstrict

example
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hpos : (bezoutMatrix n q p).PosDef) :
    StrictInterlSameDegree p q := by
  rr_bezout_strict_interl_same_degree_of_pos_def using
    left_pos_lc := hp_pos,
    right_pos_lc := hq_pos,
    left_degree := hp_deg,
    right_degree := hq_deg,
    pos_def := hpos

example
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hpos : (bezoutMatrix n q p).PosDef) :
    StrictInterl p q := by
  rr_bezout_strict_interl_of_pos_def using
    left_pos_lc := hp_pos,
    right_pos_lc := hq_pos,
    left_degree := hp_deg,
    right_degree := hq_deg,
    pos_def := hpos

variable {d : Nat → Nat} {P Q : Nat → ℝ[X]}

example {a b : ℝ} (hab : a < b) :
    (bezoutMatrix 1 (X + C a) (X + C b)).PosDef := by
  rr_bezout_pos_def_of_strict_interl_same_degree using
    left_pos_lc := by simp [HasPosLeadingCoeff],
    right_pos_lc := by simp [HasPosLeadingCoeff],
    left_degree := by simp [natDegree_add_eq_left_of_natDegree_lt],
    right_degree := by simp [natDegree_add_eq_left_of_natDegree_lt],
    strict_interl_same_degree := StrictInterlSameDegree.X_add_C_iff.2 hab

/-! The deprecated parser forms remain checked compatibility entry points. -/

example
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hstrict : StrictInterlSameDegree p q) :
    (bezoutMatrix n q p).PosDef := by
  rr_bezout_pos_def_of_strict_interl_same_degree using
    left_pos_lc := hp_pos,
    right_pos_lc := hq_pos,
    left_degree := hp_deg,
    right_degree := hq_deg,
    strict_interl_same_degree := hstrict

example
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hpos : (bezoutMatrix n q p).PosDef) :
    StrictInterlSameDegree p q := by
  rr_bezout_strict_interl_same_degree_of_pos_def using
    left_pos_lc := hp_pos,
    right_pos_lc := hq_pos,
    left_degree := hp_deg,
    right_degree := hq_deg,
    pos_def := hpos

end Tactic
end RealRooted
