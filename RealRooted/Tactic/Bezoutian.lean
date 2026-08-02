import RealRooted.Bezoutian

/-!
# Bezoutian tactic frontends

Certificate-driven wrappers around the proved same-degree Bezoutian
characterization.  The orientation is important: `StrictPrecSameDegree p q`
corresponds to positive definiteness of `bezoutMatrix n q p`.

These tactics consume an explicit positive-definiteness certificate; they do
not attempt to prove matrix positive definiteness automatically.  Degree zero
is supported by the characterization, while the no-common-root route requires
a nonzero matrix size.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem bezout_realrooted_of_posDef
    {p q : ℝ[X]} {n : Nat}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hpos : (bezoutMatrix n q p).PosDef) :
    (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits) := by
  have hstrict : StrictPrecSameDegree p q :=
    (strictPrecSameDegree_iff_bezoutMatrix_posDef hp_pos hq_pos hp_deg hq_deg).2 hpos
  exact ⟨hstrict.1, hstrict.2.1⟩

theorem bezout_no_common_root_of_posDef
    {p q : ℝ[X]} {n : Nat}
    (hn : n ≠ 0) (hp_deg : p.natDegree ≤ n) (hq_deg : q.natDegree ≤ n)
    (hpos : (bezoutMatrix n q p).PosDef) :
    ∀ r : ℝ, p.IsRoot r → ¬ q.IsRoot r := by
  intro r hp hq
  exact bezoutMatrix.no_common_real_root_of_posDef
    hn hq_deg hp_deg hpos r ⟨hq, hp⟩

theorem bezout_sequence_posDef_of_strictPrecSameDegree
    {d : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hP_pos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hQ_pos : ∀ i : Nat, HasPosLeadingCoeff (Q i))
    (hP_deg : ∀ i : Nat, (P i).natDegree = d i)
    (hQ_deg : ∀ i : Nat, (Q i).natDegree = d i)
    (hstrict : ∀ i : Nat, StrictPrecSameDegree (P i) (Q i)) :
    ∀ i : Nat, (bezoutMatrix (d i) (Q i) (P i)).PosDef := fun i =>
  (strictPrecSameDegree_iff_bezoutMatrix_posDef
    (hP_pos i) (hQ_pos i) (hP_deg i) (hQ_deg i)).1 (hstrict i)

theorem bezout_sequence_strictPrecSameDegree_of_posDef
    {d : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hP_pos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hQ_pos : ∀ i : Nat, HasPosLeadingCoeff (Q i))
    (hP_deg : ∀ i : Nat, (P i).natDegree = d i)
    (hQ_deg : ∀ i : Nat, (Q i).natDegree = d i)
    (hpos : ∀ i : Nat, (bezoutMatrix (d i) (Q i) (P i)).PosDef) :
    ∀ i : Nat, StrictPrecSameDegree (P i) (Q i) := fun i =>
  (strictPrecSameDegree_iff_bezoutMatrix_posDef
    (hP_pos i) (hQ_pos i) (hP_deg i) (hQ_deg i)).2 (hpos i)

theorem bezout_sequence_prec_of_posDef
    {d : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hP_pos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hQ_pos : ∀ i : Nat, HasPosLeadingCoeff (Q i))
    (hP_deg : ∀ i : Nat, (P i).natDegree = d i)
    (hQ_deg : ∀ i : Nat, (Q i).natDegree = d i)
    (hpos : ∀ i : Nat, (bezoutMatrix (d i) (Q i) (P i)).PosDef) :
    ∀ i : Nat, Prec (P i) (Q i) := fun i =>
  ((strictPrecSameDegree_iff_bezoutMatrix_posDef
    (hP_pos i) (hQ_pos i) (hP_deg i) (hQ_deg i)).2 (hpos i)).to_prec

theorem bezout_sequence_realrooted_of_posDef
    {d : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hP_pos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hQ_pos : ∀ i : Nat, HasPosLeadingCoeff (Q i))
    (hP_deg : ∀ i : Nat, (P i).natDegree = d i)
    (hQ_deg : ∀ i : Nat, (Q i).natDegree = d i)
    (hpos : ∀ i : Nat, (bezoutMatrix (d i) (Q i) (P i)).PosDef) :
    ∀ i : Nat,
      (P i ≠ 0 ∧ (P i).Splits) ∧ (Q i ≠ 0 ∧ (Q i).Splits) := fun i =>
  bezout_realrooted_of_posDef
    (hP_pos i) (hQ_pos i) (hP_deg i) (hQ_deg i) (hpos i)

theorem bezout_sequence_no_common_root_of_posDef
    {d : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hd : ∀ i : Nat, d i ≠ 0)
    (hP_deg : ∀ i : Nat, (P i).natDegree ≤ d i)
    (hQ_deg : ∀ i : Nat, (Q i).natDegree ≤ d i)
    (hpos : ∀ i : Nat, (bezoutMatrix (d i) (Q i) (P i)).PosDef) :
    ∀ i : Nat, ∀ r : ℝ, (P i).IsRoot r → ¬ (Q i).IsRoot r := fun i =>
  bezout_no_common_root_of_posDef (hd i) (hP_deg i) (hQ_deg i) (hpos i)

syntax (name := rr_bezout_strict_prec_same_degree_iff_named)
  "rr_bezout_strict_prec_same_degree_iff" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_degree" ":=" term ","
    "right_degree" ":=" term :
  tactic

syntax (name := rr_bezout_pos_def_of_strict_prec_same_degree_named)
  "rr_bezout_pos_def_of_strict_prec_same_degree" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "strict_prec_same_degree" ":=" term :
  tactic

syntax (name := rr_bezout_strict_prec_same_degree_of_pos_def_named)
  "rr_bezout_strict_prec_same_degree_of_pos_def" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "pos_def" ":=" term :
  tactic

syntax (name := rr_bezout_prec_of_pos_def_named)
  "rr_bezout_prec_of_pos_def" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "pos_def" ":=" term :
  tactic

syntax (name := rr_bezout_realrooted_of_pos_def_named)
  "rr_bezout_realrooted_of_pos_def" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "pos_def" ":=" term :
  tactic

syntax (name := rr_bezout_no_common_root_of_pos_def_named)
  "rr_bezout_no_common_root_of_pos_def" " using "
    "size_ne_zero" ":=" term ","
    "left_degree_le" ":=" term ","
    "right_degree_le" ":=" term ","
    "pos_def" ":=" term :
  tactic

syntax (name := rr_bezout_sequence_pos_def_of_strict_prec_same_degree_named)
  "rr_bezout_sequence_pos_def_of_strict_prec_same_degree" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "strict_prec_same_degree" ":=" term :
  tactic

syntax (name := rr_bezout_sequence_strict_prec_same_degree_of_pos_def_named)
  "rr_bezout_sequence_strict_prec_same_degree_of_pos_def" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "pos_def" ":=" term :
  tactic

syntax (name := rr_bezout_sequence_prec_of_pos_def_named)
  "rr_bezout_sequence_prec_of_pos_def" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "pos_def" ":=" term :
  tactic

syntax (name := rr_bezout_sequence_realrooted_of_pos_def_named)
  "rr_bezout_sequence_realrooted_of_pos_def" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "pos_def" ":=" term :
  tactic

syntax (name := rr_bezout_sequence_no_common_root_of_pos_def_named)
  "rr_bezout_sequence_no_common_root_of_pos_def" " using "
    "size_ne_zero" ":=" term ","
    "left_degree_le" ":=" term ","
    "right_degree_le" ":=" term ","
    "pos_def" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_bezout_strict_prec_same_degree_iff using
        left_pos_lc := $hp_pos:term,
        right_pos_lc := $hq_pos:term,
        left_degree := $hp_deg:term,
        right_degree := $hq_deg:term) =>
      `(tactic|
        exact strictPrecSameDegree_iff_bezoutMatrix_posDef
          $hp_pos $hq_pos $hp_deg $hq_deg)
  | `(tactic|
      rr_bezout_pos_def_of_strict_prec_same_degree using
        left_pos_lc := $hp_pos:term,
        right_pos_lc := $hq_pos:term,
        left_degree := $hp_deg:term,
        right_degree := $hq_deg:term,
        strict_prec_same_degree := $hstrict:term) =>
      `(tactic|
        exact (strictPrecSameDegree_iff_bezoutMatrix_posDef
          $hp_pos $hq_pos $hp_deg $hq_deg).1 $hstrict)
  | `(tactic|
      rr_bezout_strict_prec_same_degree_of_pos_def using
        left_pos_lc := $hp_pos:term,
        right_pos_lc := $hq_pos:term,
        left_degree := $hp_deg:term,
        right_degree := $hq_deg:term,
        pos_def := $hpos:term) =>
      `(tactic|
        exact (strictPrecSameDegree_iff_bezoutMatrix_posDef
          $hp_pos $hq_pos $hp_deg $hq_deg).2 $hpos)
  | `(tactic|
      rr_bezout_prec_of_pos_def using
        left_pos_lc := $hp_pos:term,
        right_pos_lc := $hq_pos:term,
        left_degree := $hp_deg:term,
        right_degree := $hq_deg:term,
        pos_def := $hpos:term) =>
      `(tactic|
        exact ((strictPrecSameDegree_iff_bezoutMatrix_posDef
          $hp_pos $hq_pos $hp_deg $hq_deg).2 $hpos).to_prec)
  | `(tactic|
      rr_bezout_realrooted_of_pos_def using
        left_pos_lc := $hp_pos:term,
        right_pos_lc := $hq_pos:term,
        left_degree := $hp_deg:term,
        right_degree := $hq_deg:term,
        pos_def := $hpos:term) =>
      `(tactic|
        exact RealRooted.Tactic.bezout_realrooted_of_posDef
          $hp_pos $hq_pos $hp_deg $hq_deg $hpos)
  | `(tactic|
      rr_bezout_no_common_root_of_pos_def using
        size_ne_zero := $hn:term,
        left_degree_le := $hp_deg:term,
        right_degree_le := $hq_deg:term,
        pos_def := $hpos:term) =>
      `(tactic|
        exact RealRooted.Tactic.bezout_no_common_root_of_posDef
          $hn $hp_deg $hq_deg $hpos)
  | `(tactic|
      rr_bezout_sequence_pos_def_of_strict_prec_same_degree using
        left_pos_lc := $hP_pos:term,
        right_pos_lc := $hQ_pos:term,
        left_degree := $hP_deg:term,
        right_degree := $hQ_deg:term,
        strict_prec_same_degree := $hstrict:term) =>
      `(tactic|
        exact RealRooted.Tactic.bezout_sequence_posDef_of_strictPrecSameDegree
          $hP_pos $hQ_pos $hP_deg $hQ_deg $hstrict)
  | `(tactic|
      rr_bezout_sequence_strict_prec_same_degree_of_pos_def using
        left_pos_lc := $hP_pos:term,
        right_pos_lc := $hQ_pos:term,
        left_degree := $hP_deg:term,
        right_degree := $hQ_deg:term,
        pos_def := $hpos:term) =>
      `(tactic|
        exact RealRooted.Tactic.bezout_sequence_strictPrecSameDegree_of_posDef
          $hP_pos $hQ_pos $hP_deg $hQ_deg $hpos)
  | `(tactic|
      rr_bezout_sequence_prec_of_pos_def using
        left_pos_lc := $hP_pos:term,
        right_pos_lc := $hQ_pos:term,
        left_degree := $hP_deg:term,
        right_degree := $hQ_deg:term,
        pos_def := $hpos:term) =>
      `(tactic|
        exact RealRooted.Tactic.bezout_sequence_prec_of_posDef
          $hP_pos $hQ_pos $hP_deg $hQ_deg $hpos)
  | `(tactic|
      rr_bezout_sequence_realrooted_of_pos_def using
        left_pos_lc := $hP_pos:term,
        right_pos_lc := $hQ_pos:term,
        left_degree := $hP_deg:term,
        right_degree := $hQ_deg:term,
        pos_def := $hpos:term) =>
      `(tactic|
        exact RealRooted.Tactic.bezout_sequence_realrooted_of_posDef
          $hP_pos $hQ_pos $hP_deg $hQ_deg $hpos)
  | `(tactic|
      rr_bezout_sequence_no_common_root_of_pos_def using
        size_ne_zero := $hd:term,
        left_degree_le := $hP_deg:term,
        right_degree_le := $hQ_deg:term,
        pos_def := $hpos:term) =>
      `(tactic|
        exact RealRooted.Tactic.bezout_sequence_no_common_root_of_posDef
          $hd $hP_deg $hQ_deg $hpos)

end Tactic
end RealRooted
