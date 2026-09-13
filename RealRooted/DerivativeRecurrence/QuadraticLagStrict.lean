import RealRooted.Derivative.Interlacing
import RealRooted.GeneralizedLiuWang
import RealRooted.SimpleRoots
import RealRooted.WagnerRightSum

/-!
# Strict interlacing for quadratic derivative recurrences with a lag

This module isolates the root-sign argument for second-order recurrences whose
derivative multiplier is `a X - b X^2` and whose lag multiplier is `c X`.
The middle multiplier is arbitrary because it vanishes at every root used by
the generalized Liu--Wang step.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A quadratic derivative recurrence with an arbitrary middle multiplier has
strict adjacent proper position once its elementary rankwise invariants and
base pair are known. -/
theorem prec_and_noCommonRoot_of_quadratic_lag
    (P : ℕ → ℝ[X]) (a b c : ℝ) (Q : ℕ → ℝ[X])
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hdeg : ∀ n, (P n).natDegree = n)
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hroot : ∀ n r, (P n).IsRoot r → r < 0)
    (hbase : Prec (P 0) (P 1))
    (hbaseNo : ∀ r, (P 1).IsRoot r → ¬ (P 0).IsRoot r)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-b) * X ^ 2) * (P (n + 1)).derivative +
        Q n * P (n + 1) + (C c * X) * P n) :
    ∀ n, Prec (P n) (P (n + 1)) ∧
      ∀ r : ℝ, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r := by
  intro n
  induction n with
  | zero => exact ⟨hbase, hbaseNo⟩
  | succ n ih =>
      obtain ⟨ihprec, ihno⟩ := ih
      have hinter : Interlaces (P n) (P (n + 1)) :=
        ihprec.toInterlaces (by rw [hdeg, hdeg])
      have hderiv_inter : Interlaces ((P (n + 1)).derivative) (P (n + 1)) :=
        interlaces_derivative_of_pos_natDegree (hpos (n + 1)).ne_zero
          ihprec.2.1.2 (hpos (n + 1)) (by rw [hdeg]; lia)
      have hderiv_pos : HasPosLeadingCoeff ((P (n + 1)).derivative) :=
        (hpos (n + 1)).derivative (by rw [hdeg]; lia)
      have hV : ∀ r : ℝ, (P (n + 1)).IsRoot r →
          eval r (C a * X + C (-b) * X ^ 2) ≤ 0 := by
        intro r hr
        have hrneg := hroot (n + 1) r hr
        simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
        nlinarith [sq_nonneg r]
      have hW : ∀ r : ℝ, (P (n + 1)).IsRoot r → eval r (C c * X) ≤ 0 := by
        intro r hr
        simp only [eval_mul, eval_C, eval_X]
        exact mul_nonpos_of_nonneg_of_nonpos hc (hroot (n + 1) r hr).le
      have hsum : P (n + 2) =
          Q n * P (n + 1) +
            polynomialWeightedSum
              ((C c * X, P n) ::
                [(C a * X + C (-b) * X ^ 2, (P (n + 1)).derivative)]) := by
        rw [hrec n]
        simp only [polynomialWeightedSum]
        ring
      have hprec : Prec (P (n + 1)) (P (n + 2)) := by
        rw [hsum]
        refine prec_generalizedLiuWang_of_no_common
          hinter (hpos n) ?_ ?_ ?_ ?_ ?_ ?_ ihno hW
        · intro bg hmem
          rw [List.mem_singleton] at hmem
          subst hmem
          exact hderiv_inter
        · intro bg hmem
          rw [List.mem_singleton] at hmem
          subst hmem
          exact hderiv_pos
        · intro bg hmem r hr
          rw [List.mem_singleton] at hmem
          subst hmem
          exact hV r hr
        · rw [← hsum]
          exact hpos (n + 2)
        · rw [← hsum, hdeg, hdeg]
          lia
        · rw [← hsum, hdeg, hdeg]
      refine ⟨hprec, ?_⟩
      intro r hr2 hr1
      have hrneg : r < 0 := hroot (n + 1) r hr1
      have hkey :
          (a - b * r) * eval r ((P (n + 1)).derivative) +
            c * eval r (P n) = 0 := by
        have h := hr2
        rw [Polynomial.IsRoot.def, hrec n] at h
        simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow] at h
        rw [Polynomial.IsRoot.def] at hr1
        rw [hr1] at h
        have hr0 : r ≠ 0 := ne_of_lt hrneg
        have hfactor :
            r * ((a - b * r) * eval r ((P (n + 1)).derivative) +
              c * eval r (P n)) = 0 := by
          nlinarith [h]
        exact (mul_eq_zero.mp hfactor).resolve_left hr0
      have hne : eval r (P n) ≠ 0 := fun hroot0 => ihno r hr1 hroot0
      have hsign : 0 ≤ eval r (P n) * eval r ((P (n + 1)).derivative) :=
        eval_mul_eval_nonneg_of_prec_right ihprec hderiv_inter.toPrec
          (hpos n) hderiv_pos hr1
      have hpref : 0 < a - b * r := by nlinarith
      have hmul :
          0 ≤ (a - b * r) *
            (eval r (P n) * eval r ((P (n + 1)).derivative)) :=
        mul_nonneg hpref.le hsign
      have hlag_square : 0 ≤ c * (eval r (P n)) ^ 2 :=
        mul_nonneg hc (sq_nonneg _)
      have hsum_zero :
          (a - b * r) *
              (eval r (P n) * eval r ((P (n + 1)).derivative)) +
            c * (eval r (P n)) ^ 2 = 0 := by
        calc
          _ = eval r (P n) *
              ((a - b * r) * eval r ((P (n + 1)).derivative) +
                c * eval r (P n)) := by ring
          _ = 0 := by rw [hkey, mul_zero]
      have hfirst_zero :
          (a - b * r) *
            (eval r (P n) * eval r ((P (n + 1)).derivative)) = 0 := by
        linarith
      have hproduct_zero :
          eval r (P n) * eval r ((P (n + 1)).derivative) = 0 :=
        (mul_eq_zero.mp hfirst_zero).resolve_left hpref.ne'
      have hderiv_zero : eval r ((P (n + 1)).derivative) = 0 :=
        (mul_eq_zero.mp hproduct_zero).resolve_left hne
      have hsimple : HasSimpleRoots (P (n + 1)) :=
        (ihprec.hasSimpleRoots_of_no_common_root fun x hx =>
          ihno x hx.2 hx.1).2
      exact (hsimple.eval_derivative_ne_zero hr1 hderiv_zero).elim

end RealRooted
