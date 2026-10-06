import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Energy
import RealRooted.Interlacing.NegativeRoots
import RealRooted.MaWang.Strong

/-!
# Strict insertion step for the A144438 interval-preserver argument

This file isolates the root-location part of the diagonal induction.  Once the
companion strictly interlaces the current transform, the insertion recurrence
forces the next transform to strictly interlace the current one.  This avoids
using the arrowhead matrix for conclusions that already follow from the
project's strict Ma--Wang API; the matrix argument is still needed to construct
the next companion and propagate its residue energy.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The A144438 insertion recurrence gives a strict interlacing successor.

The hypotheses separate the sign argument from the degree and leading-term
bookkeeping used by the diagonal induction. -/
theorem a144438_insertion_strictInterl
    {p h : ℝ[X]} {a : ℝ}
    (hhp : Interlaces h p)
    (hh_pos : HasPosLeadingCoeff h)
    (hnext_pos : HasPosLeadingCoeff ((1 + X + C a) * p + X * h))
    (hnext_deg : ((1 + X + C a) * p + X * h).natDegree =
      p.natDegree + 1)
    (hno : ∀ r, p.IsRoot r → ¬ h.IsRoot r)
    (hp_neg : ∀ r, p.IsRoot r → r < 0) :
    StrictInterl p ((1 + X + C a) * p + X * h) := by
  apply RealRooted.MaWangInternal.strictInterl_of_interlaces_evalCoeff_neg_succ
    hhp hh_pos hnext_pos hnext_deg hno
  intro r hr
  simpa using hp_neg r hr

/-- In addition to strict interlacing, a positive value at zero keeps every
root of the insertion successor strictly negative. -/
theorem a144438_insertion_strictInterl_and_roots_neg
    {p h : ℝ[X]} {a : ℝ}
    (hhp : Interlaces h p)
    (hh_pos : HasPosLeadingCoeff h)
    (hnext_pos : HasPosLeadingCoeff ((1 + X + C a) * p + X * h))
    (hnext_deg : ((1 + X + C a) * p + X * h).natDegree =
      p.natDegree + 1)
    (hno : ∀ r, p.IsRoot r → ¬ h.IsRoot r)
    (hp_neg : ∀ r, p.IsRoot r → r < 0)
    (ha : -1 < a) (hp_zero : 0 < p.eval 0) :
    StrictInterl p ((1 + X + C a) * p + X * h) ∧
      ∀ r, ((1 + X + C a) * p + X * h).IsRoot r → r < 0 := by
  have hstrict := a144438_insertion_strictInterl hhp hh_pos hnext_pos
    hnext_deg hno hp_neg
  have hinter : Interlaces p ((1 + X + C a) * p + X * h) :=
    hstrict.toInterlaces (by rw [hnext_deg])
  have hzero : 0 < ((1 + X + C a) * p + X * h).eval 0 := by
    simp only [eval_add, eval_mul, eval_one, eval_X, eval_C, zero_mul,
      add_zero]
    exact mul_pos (by linarith) hp_zero
  exact ⟨hstrict,
    roots_neg_of_interlaces_of_eval_zero_pos hinter hnext_pos hzero hp_neg⟩

/-- The preceding generic step specialized to the exact diagonal recurrence. -/
theorem a144438Diagonal_strictInterl_succ
    {n : ℕ} {a : ℝ}
    (hhp : Interlaces (a144438DiagonalCompanion n a)
      (a144438Diagonal n a))
    (hh_pos : HasPosLeadingCoeff (a144438DiagonalCompanion n a))
    (hnext_pos : HasPosLeadingCoeff (a144438Diagonal (n + 1) a))
    (hnext_deg : (a144438Diagonal (n + 1) a).natDegree =
      (a144438Diagonal n a).natDegree + 1)
    (hno : ∀ r, (a144438Diagonal n a).IsRoot r →
      ¬ (a144438DiagonalCompanion n a).IsRoot r)
    (hp_neg : ∀ r, (a144438Diagonal n a).IsRoot r → r < 0) :
    StrictInterl (a144438Diagonal n a) (a144438Diagonal (n + 1) a) := by
  rw [a144438Diagonal_succ] at hnext_pos hnext_deg ⊢
  exact a144438_insertion_strictInterl hhp hh_pos hnext_pos hnext_deg hno hp_neg

end RealRooted.Applications.OEIS
