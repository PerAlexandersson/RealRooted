import RealRooted.Tactic.Bezoutian

open Polynomial

namespace RealRooted
namespace Tactic

variable {p q : ℝ[X]} {n : Nat}

example
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n) :
    StrictPrecSameDegree p q ↔ (bezoutMatrix n q p).PosDef := by
  rr_bezout_strict_prec_same_degree_iff using
    left_pos_lc := hp_pos,
    right_pos_lc := hq_pos,
    left_degree := hp_deg,
    right_degree := hq_deg

example
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hstrict : StrictPrecSameDegree p q) :
    (bezoutMatrix n q p).PosDef := by
  rr_bezout_pos_def_of_strict_prec_same_degree using
    left_pos_lc := hp_pos,
    right_pos_lc := hq_pos,
    left_degree := hp_deg,
    right_degree := hq_deg,
    strict_prec_same_degree := hstrict

example
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hpos : (bezoutMatrix n q p).PosDef) :
    StrictPrecSameDegree p q := by
  rr_bezout_strict_prec_same_degree_of_pos_def using
    left_pos_lc := hp_pos,
    right_pos_lc := hq_pos,
    left_degree := hp_deg,
    right_degree := hq_deg,
    pos_def := hpos

example
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hpos : (bezoutMatrix n q p).PosDef) :
    Prec p q := by
  rr_bezout_prec_of_pos_def using
    left_pos_lc := hp_pos,
    right_pos_lc := hq_pos,
    left_degree := hp_deg,
    right_degree := hq_deg,
    pos_def := hpos

example
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hpos : (bezoutMatrix n q p).PosDef) :
    (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits) := by
  rr_bezout_realrooted_of_pos_def using
    left_pos_lc := hp_pos,
    right_pos_lc := hq_pos,
    left_degree := hp_deg,
    right_degree := hq_deg,
    pos_def := hpos

example
    (hn : n ≠ 0) (hp_deg : p.natDegree ≤ n) (hq_deg : q.natDegree ≤ n)
    (hpos : (bezoutMatrix n q p).PosDef) :
    ∀ r : ℝ, p.IsRoot r → ¬ q.IsRoot r := by
  rr_bezout_no_common_root_of_pos_def using
    size_ne_zero := hn,
    left_degree_le := hp_deg,
    right_degree_le := hq_deg,
    pos_def := hpos

variable {d : Nat → Nat} {P Q : Nat → ℝ[X]}

example
    (hP_pos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hQ_pos : ∀ i : Nat, HasPosLeadingCoeff (Q i))
    (hP_deg : ∀ i : Nat, (P i).natDegree = d i)
    (hQ_deg : ∀ i : Nat, (Q i).natDegree = d i)
    (hstrict : ∀ i : Nat, StrictPrecSameDegree (P i) (Q i)) :
    ∀ i : Nat, (bezoutMatrix (d i) (Q i) (P i)).PosDef := by
  rr_bezout_sequence_pos_def_of_strict_prec_same_degree using
    left_pos_lc := hP_pos,
    right_pos_lc := hQ_pos,
    left_degree := hP_deg,
    right_degree := hQ_deg,
    strict_prec_same_degree := hstrict

example
    (hP_pos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hQ_pos : ∀ i : Nat, HasPosLeadingCoeff (Q i))
    (hP_deg : ∀ i : Nat, (P i).natDegree = d i)
    (hQ_deg : ∀ i : Nat, (Q i).natDegree = d i)
    (hpos : ∀ i : Nat, (bezoutMatrix (d i) (Q i) (P i)).PosDef) :
    ∀ i : Nat, StrictPrecSameDegree (P i) (Q i) := by
  rr_bezout_sequence_strict_prec_same_degree_of_pos_def using
    left_pos_lc := hP_pos,
    right_pos_lc := hQ_pos,
    left_degree := hP_deg,
    right_degree := hQ_deg,
    pos_def := hpos

example
    (hP_pos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hQ_pos : ∀ i : Nat, HasPosLeadingCoeff (Q i))
    (hP_deg : ∀ i : Nat, (P i).natDegree = d i)
    (hQ_deg : ∀ i : Nat, (Q i).natDegree = d i)
    (hpos : ∀ i : Nat, (bezoutMatrix (d i) (Q i) (P i)).PosDef) :
    ∀ i : Nat, Prec (P i) (Q i) := by
  rr_bezout_sequence_prec_of_pos_def using
    left_pos_lc := hP_pos,
    right_pos_lc := hQ_pos,
    left_degree := hP_deg,
    right_degree := hQ_deg,
    pos_def := hpos

example
    (hP_pos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hQ_pos : ∀ i : Nat, HasPosLeadingCoeff (Q i))
    (hP_deg : ∀ i : Nat, (P i).natDegree = d i)
    (hQ_deg : ∀ i : Nat, (Q i).natDegree = d i)
    (hpos : ∀ i : Nat, (bezoutMatrix (d i) (Q i) (P i)).PosDef) :
    ∀ i : Nat,
      (P i ≠ 0 ∧ (P i).Splits) ∧ (Q i ≠ 0 ∧ (Q i).Splits) := by
  rr_bezout_sequence_realrooted_of_pos_def using
    left_pos_lc := hP_pos,
    right_pos_lc := hQ_pos,
    left_degree := hP_deg,
    right_degree := hQ_deg,
    pos_def := hpos

example
    (hd : ∀ i : Nat, d i ≠ 0)
    (hP_deg : ∀ i : Nat, (P i).natDegree ≤ d i)
    (hQ_deg : ∀ i : Nat, (Q i).natDegree ≤ d i)
    (hpos : ∀ i : Nat, (bezoutMatrix (d i) (Q i) (P i)).PosDef) :
    ∀ i : Nat, ∀ r : ℝ, (P i).IsRoot r → ¬ (Q i).IsRoot r := by
  rr_bezout_sequence_no_common_root_of_pos_def using
    size_ne_zero := hd,
    left_degree_le := hP_deg,
    right_degree_le := hQ_deg,
    pos_def := hpos

example {a b : ℝ} (hab : a < b) :
    (bezoutMatrix 1 (X + C a) (X + C b)).PosDef := by
  rr_bezout_pos_def_of_strict_prec_same_degree using
    left_pos_lc := by simp [HasPosLeadingCoeff],
    right_pos_lc := by simp [HasPosLeadingCoeff],
    left_degree := by simp [natDegree_add_eq_left_of_natDegree_lt],
    right_degree := by simp [natDegree_add_eq_left_of_natDegree_lt],
    strict_prec_same_degree := StrictPrecSameDegree.X_add_C_iff.2 hab

end Tactic
end RealRooted
