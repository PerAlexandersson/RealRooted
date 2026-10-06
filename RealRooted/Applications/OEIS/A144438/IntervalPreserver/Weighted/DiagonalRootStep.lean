import RealRooted.Applications.OEIS.A144438.IntervalPreserver.WeightedResidueSum
import RealRooted.Interlacing.NegativeRoots
import RealRooted.MaWang.StrictStep
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.ResidueAlgebra

/-! # Root package for one weighted diagonal step -/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

theorem weightedDecoDiagonal_root_step
    {w : ℝ} {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 ≤ a)
    (hsplits : (weightedDecoDiagonal w n a).Splits)
    (hresidue : ∀ r, (weightedDecoDiagonal w n a).IsRoot r →
      0 < (weightedDecoDiagonalCompanion w n a).eval r /
        (weightedDecoDiagonal w n a).derivative.eval r)
    (hneg : ∀ r, (weightedDecoDiagonal w n a).IsRoot r → r < 0) :
    StrictInterl (weightedDecoDiagonal w n a)
        (weightedDecoDiagonal w (n + 1) a) ∧
      HasSimpleRoots (weightedDecoDiagonal w (n + 1) a) ∧
      (∀ r, (weightedDecoDiagonal w (n + 1) a).IsRoot r → r < 0) ∧
      (∀ r, (weightedDecoDiagonal w n a).IsRoot r →
        ¬ (weightedDecoDiagonal w (n + 1) a).IsRoot r) := by
  let p := weightedDecoDiagonal w n a
  let h := weightedDecoDiagonalCompanion w n a
  let q := weightedDecoDiagonal w (n + 1) a
  have hpPos : HasPosLeadingCoeff p := weightedDecoDiagonal_hasPosLeadingCoeff w n a
  have hqPos : HasPosLeadingCoeff q :=
    weightedDecoDiagonal_hasPosLeadingCoeff w (n + 1) a
  have hpdeg : 1 ≤ p.natDegree := by
    simpa only [p, weightedDecoDiagonal_natDegree] using hn
  have hqdeg : q.natDegree = p.natDegree + 1 := by
    simp only [q, p, weightedDecoDiagonal_natDegree]
  have hsign : ∀ r, p.IsRoot r → 0 < h.eval r * p.derivative.eval r := by
    intro r hr
    have hres := hresidue r hr
    have hderivative : p.derivative.eval r ≠ 0 := by
      intro hzero
      rw [hzero, div_zero] at hres
      exact (lt_irrefl 0) hres
    have heq :
        h.eval r * p.derivative.eval r =
          (h.eval r / p.derivative.eval r) * (p.derivative.eval r) ^ 2 := by
      field_simp [hderivative]
    rw [heq]
    exact mul_pos hres (sq_pos_of_ne_zero hderivative)
  have hXneg : ∀ r, p.IsRoot r → X.eval r < 0 := by
    intro r hr
    simpa using hneg r hr
  have hrec : q = (1 + X + C a) * p + X * h :=
    weightedDecoDiagonal_succ w n a
  have hstep := strictInterl_and_hasSimpleRoots_of_auxiliary_sign_succ
    hsplits hpPos hqPos hpdeg hqdeg hrec hsign hXneg
  have hstrict : StrictInterl p q := hstep.1
  have hsimple : HasSimpleRoots q := hstep.2
  have hno : ∀ r, p.IsRoot r → ¬ q.IsRoot r :=
    noCommonRoot_of_auxiliary_sign hrec hsign hXneg
  have hinter : Interlaces p q := hstrict.toInterlaces (by rw [hqdeg])
  have hqzero : 0 < q.eval 0 := by
    change 0 < (weightedDecoDiagonal w (n + 1) a).eval 0
    rw [weightedDecoDiagonal_eval_zero]
    positivity
  have hqneg : ∀ r, q.IsRoot r → r < 0 :=
    roots_neg_of_interlaces_of_eval_zero_pos hinter hqPos hqzero hneg
  exact ⟨hstrict, hsimple, hqneg, hno⟩

end RealRooted.Applications.OEIS
