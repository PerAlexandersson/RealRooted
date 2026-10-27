module

public import RealRooted.Bezoutian.LowDegree

/-!
# Bezoutian tactic frontends

Certificate-driven wrappers around the proved same-degree Bezoutian
characterization.  The orientation is important: `StrictInterlSameDegree p q`
corresponds to positive definiteness of `bezoutMatrix n q p`.

These tactics consume an explicit positive-definiteness certificate; they do
not attempt to prove matrix positive definiteness automatically.  Degree zero
is supported by the characterization, while the no-common-root route requires
a nonzero matrix size.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- If `p` and `q` have positive leading coefficients and common degree `n`, positive
definiteness of `bezoutMatrix n q p` implies that both polynomials are nonzero and split. -/
theorem bezout_realrooted_of_posDef
    {p q : ℝ[X]} {n : Nat}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hpos : (bezoutMatrix n q p).PosDef) :
    (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits) := by
  have hstrict : StrictInterlSameDegree p q :=
    (strictInterlSameDegree_iff_bezoutMatrix_posDef hp_pos hq_pos hp_deg hq_deg).2 hpos
  exact ⟨hstrict.1, hstrict.2.1⟩

/-- A positive-definite Bezout matrix of nonzero size implies that `p` and `q`, whose degrees
are at most the matrix size, have no common real root. -/
theorem bezout_no_common_root_of_posDef
    {p q : ℝ[X]} {n : Nat}
    (hn : n ≠ 0) (hp_deg : p.natDegree ≤ n) (hq_deg : q.natDegree ≤ n)
    (hpos : (bezoutMatrix n q p).PosDef) :
    ∀ r : ℝ, p.IsRoot r → ¬ q.IsRoot r :=
  fun r hp hq => bezoutMatrix.no_common_real_root_of_posDef
    hn hq_deg hp_deg hpos r ⟨hq, hp⟩

/-- Pointwise sequence form of the forward same-degree Bezoutian characterization, assuming
positive leading coefficients and the stated degree equalities at every index. -/
theorem bezout_sequence_posDef_of_strictInterlSameDegree
    {d : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hP_pos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hQ_pos : ∀ i : Nat, HasPosLeadingCoeff (Q i))
    (hP_deg : ∀ i : Nat, (P i).natDegree = d i)
    (hQ_deg : ∀ i : Nat, (Q i).natDegree = d i)
    (hstrict : ∀ i : Nat, StrictInterlSameDegree (P i) (Q i)) :
    ∀ i : Nat, (bezoutMatrix (d i) (Q i) (P i)).PosDef := fun i =>
  (strictInterlSameDegree_iff_bezoutMatrix_posDef
    (hP_pos i) (hQ_pos i) (hP_deg i) (hQ_deg i)).1 (hstrict i)

/-- Pointwise sequence form of the reverse same-degree Bezoutian characterization, assuming
positive leading coefficients, the stated degree equalities, and positive definiteness. -/
theorem bezout_sequence_strictInterlSameDegree_of_posDef
    {d : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hP_pos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hQ_pos : ∀ i : Nat, HasPosLeadingCoeff (Q i))
    (hP_deg : ∀ i : Nat, (P i).natDegree = d i)
    (hQ_deg : ∀ i : Nat, (Q i).natDegree = d i)
    (hpos : ∀ i : Nat, (bezoutMatrix (d i) (Q i) (P i)).PosDef) :
    ∀ i : Nat, StrictInterlSameDegree (P i) (Q i) := fun i =>
  (strictInterlSameDegree_iff_bezoutMatrix_posDef
    (hP_pos i) (hQ_pos i) (hP_deg i) (hQ_deg i)).2 (hpos i)

/-- Positive leading coefficients, the stated degree equalities, and positive-definite
Bezout matrices give pointwise strict interlacing. -/
theorem bezout_sequence_strictInterl_of_posDef
    {d : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hP_pos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hQ_pos : ∀ i : Nat, HasPosLeadingCoeff (Q i))
    (hP_deg : ∀ i : Nat, (P i).natDegree = d i)
    (hQ_deg : ∀ i : Nat, (Q i).natDegree = d i)
    (hpos : ∀ i : Nat, (bezoutMatrix (d i) (Q i) (P i)).PosDef) :
    ∀ i : Nat, StrictInterl (P i) (Q i) := fun i =>
  ((strictInterlSameDegree_iff_bezoutMatrix_posDef
    (hP_pos i) (hQ_pos i) (hP_deg i) (hQ_deg i)).2 (hpos i)).toStrictInterl

/-- Positive leading coefficients, the stated degree equalities, and positive-definite
Bezout matrices make both polynomial sequences pointwise nonzero and splitting. -/
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

/-- Positive-definite Bezout matrices of pointwise nonzero size imply that the two sequences,
whose degrees are bounded by those sizes, have no common real root at any index. -/
theorem bezout_sequence_no_common_root_of_posDef
    {d : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hd : ∀ i : Nat, d i ≠ 0)
    (hP_deg : ∀ i : Nat, (P i).natDegree ≤ d i)
    (hQ_deg : ∀ i : Nat, (Q i).natDegree ≤ d i)
    (hpos : ∀ i : Nat, (bezoutMatrix (d i) (Q i) (P i)).PosDef) :
    ∀ i : Nat, ∀ r : ℝ, (P i).IsRoot r → ¬ (Q i).IsRoot r := fun i =>
  bezout_no_common_root_of_posDef (hd i) (hP_deg i) (hQ_deg i) (hpos i)

end Tactic
end RealRooted

