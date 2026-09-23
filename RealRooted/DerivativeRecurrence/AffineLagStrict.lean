import RealRooted.Derivative.Interlacing
import RealRooted.GeneralizedLiuWang
import RealRooted.SimpleRoots
import RealRooted.WagnerRightSum

/-!
# Strict interlacing for affine-lag recurrences

This module isolates the root-sign argument for second-order recurrences whose
lag multiplier is `aₙ X - bₙ`.  Adjacent degrees may stay fixed or rise by one.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- An affine lag that is strictly negative on the nonpositive half-line gives
strict adjacent proper position when every adjacent degree stays fixed or rises
by one. -/
theorem prec_and_noCommonRoot_of_affine_lag_degree_step
    (P : ℕ → ℝ[X]) (a b : ℕ → ℝ) (A : ℕ → ℝ[X])
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n)
    (hstep : ∀ n, (P (n + 1)).natDegree = (P n).natDegree ∨
      (P (n + 1)).natDegree = (P n).natDegree + 1)
    (hdegreePos : ∀ n, 0 < (P (n + 1)).natDegree)
    (hnonneg : ∀ n, HasNonnegCoeffs (P n))
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hbase : StrictInterl (P 0) (P 1))
    (hbaseNo : ∀ r, (P 1).IsRoot r → ¬ (P 0).IsRoot r)
    (hrec : ∀ n, P (n + 2) =
      A n * P (n + 1) + (C (a n) * X - C (b n)) * P n) :
    ∀ n, StrictInterl (P n) (P (n + 1)) ∧
      ∀ r : ℝ, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r := by
  intro n
  induction n with
  | zero => exact ⟨hbase, hbaseNo⟩
  | succ n ih =>
      obtain ⟨ihprec, ihno⟩ := ih
      have hsimple : HasSimpleRoots (P (n + 1)) :=
        (ihprec.hasSimpleRoots_of_no_common_root fun x hx =>
          ihno x hx.2 hx.1).2
      have hderivInter : Interlaces ((P (n + 1)).derivative) (P (n + 1)) :=
        interlaces_derivative_of_pos_natDegree (hpos (n + 1)).ne_zero
          ihprec.2.1.2 (hpos (n + 1)) (hdegreePos n)
      have hderivPos : HasPosLeadingCoeff ((P (n + 1)).derivative) :=
        (hpos (n + 1)).derivative (hdegreePos n).ne'
      have hrootSign : ∀ r, (P (n + 1)).IsRoot r →
          eval r (P (n + 2)) * eval r ((P (n + 1)).derivative) < 0 := by
        intro r hr
        have hrNonpos : r ≤ 0 :=
          isRoot_nonpos_of_hasNonnegCoeffs (hnonneg (n + 1))
            (hpos (n + 1)).ne_zero hr
        have hprevDeriv :
            0 ≤ eval r (P n) * eval r ((P (n + 1)).derivative) :=
          eval_mul_eval_nonneg_of_strictInterl_right ihprec hderivInter.toStrictInterl
            (hpos n) hderivPos hr
        have hprevNe : eval r (P n) ≠ 0 := by
          intro hzero
          exact ihno r hr (Polynomial.IsRoot.def.mpr hzero)
        have hderivNe : eval r ((P (n + 1)).derivative) ≠ 0 :=
          hsimple.eval_derivative_ne_zero hr
        have hprevDerivPos :
            0 < eval r (P n) * eval r ((P (n + 1)).derivative) := by
          exact lt_of_le_of_ne hprevDeriv (mul_ne_zero hprevNe hderivNe).symm
        have hlagNeg : a n * r - b n < 0 := by
          have har : a n * r ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (ha n) hrNonpos
          linarith [hb n]
        have heval :
            eval r (P (n + 2)) = (a n * r - b n) * eval r (P n) := by
          rw [hrec n]
          rw [Polynomial.IsRoot.def] at hr
          simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]
          rw [hr]
          ring
        rw [heval]
        nlinarith
      have hprec : StrictInterl (P (n + 1)) (P (n + 2)) := by
        rcases hstep (n + 1) with hsame | hsucc
        · exact strictInterl_of_interlaces_eval_mul_neg_same
            hderivInter hderivPos (hpos (n + 2)) hsame hrootSign
        · exact strictInterl_of_interlaces_eval_mul_neg_succ
            hderivInter hderivPos (hpos (n + 2)) hsucc hrootSign
      refine ⟨hprec, ?_⟩
      intro r hr2 hr1
      have hsign := hrootSign r hr1
      rw [Polynomial.IsRoot.def] at hr2
      rw [hr2, zero_mul] at hsign
      exact (lt_irrefl 0 hsign).elim

end RealRooted
