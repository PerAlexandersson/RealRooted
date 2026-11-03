module

import RealRooted.Bezoutian.WronskianConverse
import RealRooted.Bezoutian.ComplexRoots
import RealRooted.Bezoutian.RootEvaluation
public import RealRooted.Bezoutian.MatrixBasics

/-!
# Strict Bezoutian characterization

The all-degree strict Bezoutian characterization of strict same-degree interlacing.
-/

public section

open Polynomial Matrix

noncomputable section

namespace RealRooted

/-- Positive definiteness of the Bezoutian forces strict same-degree interlacing. -/
lemma StrictInterlSameDegree.of_bezoutMatrix_posDef
    {p q : ℝ[X]} {n : ℕ}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (h : (bezoutMatrix n q p).PosDef) :
    StrictInterlSameDegree p q :=
  let ⟨hp_s, hq_s⟩ := bezoutMatrix.splits_of_posDef hp_pos hq_pos hp_deg hq_deg h
  StrictInterlSameDegree.of_splits_and_posDef hp_pos hq_pos hp_deg hq_deg hp_s hq_s h

/--
Strict same-degree Bezoutian characterization.

The orientation is chosen so that `StrictInterlSameDegree p q` corresponds to
positive definiteness of `bezoutMatrix n q p`.
-/
theorem strictInterlSameDegree_iff_bezoutMatrix_posDef
    {p q : ℝ[X]} {n : ℕ}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n) :
    StrictInterlSameDegree p q ↔ (bezoutMatrix n q p).PosDef :=
  ⟨StrictInterlSameDegree.bezoutMatrix_posDef hp_pos hq_pos hp_deg hq_deg,
    StrictInterlSameDegree.of_bezoutMatrix_posDef hp_pos hq_pos hp_deg hq_deg⟩

@[deprecated strictInterlSameDegree_iff_bezoutMatrix_posDef +typeChanged
  (since := "2026-11-03")]
lemma StrictInterlSameDegree.bezoutMatrix_posDef_iff_natDegree_two
    {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2) :
    StrictInterlSameDegree p q ↔ (bezoutMatrix 2 q p).PosDef :=
  strictInterlSameDegree_iff_bezoutMatrix_posDef hp_pos hq_pos hp_deg hq_deg

end RealRooted
