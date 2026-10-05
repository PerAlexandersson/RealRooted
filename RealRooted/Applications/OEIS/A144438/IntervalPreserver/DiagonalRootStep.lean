import RealRooted.Applications.OEIS.A144438.IntervalPreserver.WeightedResidueSum
import RealRooted.Interlacing.NegativeRoots
import RealRooted.MaWang.StrictStep

/-!
# Root package for one A144438 diagonal step

Positive companion residues at the old roots are enough to obtain strict
successor interlacing, simple successor roots, noncollision, and preservation
of strict negativity.  Companion interlacing itself is not needed as an
induction hypothesis.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- One diagonal insertion step from positive companion residues. -/
theorem a144438Diagonal_root_step
    {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 ≤ a)
    (hsplits : (a144438Diagonal n a).Splits)
    (hresidue : ∀ r, (a144438Diagonal n a).IsRoot r →
      0 < (a144438DiagonalCompanion n a).eval r /
        (a144438Diagonal n a).derivative.eval r)
    (hneg : ∀ r, (a144438Diagonal n a).IsRoot r → r < 0) :
    StrictInterl (a144438Diagonal n a) (a144438Diagonal (n + 1) a) ∧
      HasSimpleRoots (a144438Diagonal (n + 1) a) ∧
      (∀ r, (a144438Diagonal (n + 1) a).IsRoot r → r < 0) ∧
      (∀ r, (a144438Diagonal n a).IsRoot r →
        ¬ (a144438Diagonal (n + 1) a).IsRoot r) := by
  let p := a144438Diagonal n a
  let h := a144438DiagonalCompanion n a
  let q := a144438Diagonal (n + 1) a
  have hp_pos : HasPosLeadingCoeff p := by
    exact a144438Diagonal_hasPosLeadingCoeff n a
  have hq_pos : HasPosLeadingCoeff q := by
    exact a144438Diagonal_hasPosLeadingCoeff (n + 1) a
  have hpdeg : 1 ≤ p.natDegree := by
    simpa only [p, a144438Diagonal_natDegree] using hn
  have hqdeg : q.natDegree = p.natDegree + 1 := by
    simp only [q, p, a144438Diagonal_natDegree]
  have hsign : ∀ r, p.IsRoot r → 0 < h.eval r * p.derivative.eval r := by
    intro r hr
    have hw := hresidue r hr
    have hderivative : p.derivative.eval r ≠ 0 := by
      intro hzero
      rw [hzero, div_zero] at hw
      exact (lt_irrefl 0) hw
    have heq :
        h.eval r * p.derivative.eval r =
          (h.eval r / p.derivative.eval r) * (p.derivative.eval r) ^ 2 := by
      field_simp [hderivative]
    rw [heq]
    exact mul_pos hw (sq_pos_of_ne_zero hderivative)
  have hXneg : ∀ r, p.IsRoot r → X.eval r < 0 := by
    intro r hr
    simpa using hneg r hr
  have hrec : q = (1 + X + C a) * p + X * h := by
    exact a144438Diagonal_succ n a
  have hstep := strictInterl_and_hasSimpleRoots_of_auxiliary_sign_succ
    hsplits hp_pos hq_pos hpdeg hqdeg hrec hsign hXneg
  have hstrict : StrictInterl p q := hstep.1
  have hsimple : HasSimpleRoots q := hstep.2
  have hno : ∀ r, p.IsRoot r → ¬ q.IsRoot r :=
    noCommonRoot_of_auxiliary_sign hrec hsign hXneg
  have hinter : Interlaces p q := hstrict.toInterlaces (by rw [hqdeg])
  have hqzero : 0 < q.eval 0 := by
    change 0 < (a144438Diagonal (n + 1) a).eval 0
    rw [a144438Diagonal_eval_zero]
    positivity
  have hqneg : ∀ r, q.IsRoot r → r < 0 :=
    roots_neg_of_interlaces_of_eval_zero_pos hinter hq_pos hqzero hneg
  exact ⟨hstrict, hsimple, hqneg, hno⟩

end RealRooted.Applications.OEIS
