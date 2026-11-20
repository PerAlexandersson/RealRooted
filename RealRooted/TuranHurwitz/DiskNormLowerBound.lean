module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic.Linarith

/-!
# A quantitative exterior lower bound

Root factorization gives a lower bound depending only on the leading coefficient,
degree, and distance of the evaluation point from the closed unit disk.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

private theorem pow_card_le_norm_rootProduct (z : ℂ) (hz : 1 < ‖z‖)
    (s : Multiset ℂ) (hs : ∀ r ∈ s, ‖r‖ ≤ 1) :
    (‖z‖ - 1) ^ s.card ≤ ‖(s.map (fun r => z - r)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
      have hr := hs r (Multiset.mem_cons_self r s)
      have hdist : ‖z‖ - 1 ≤ ‖z - r‖ := by linarith [norm_sub_norm_le z r]
      have htail := ih (fun t ht => hs t (Multiset.mem_cons_of_mem ht))
      rw [Multiset.card_cons, pow_succ', Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_mul hdist htail (pow_nonneg (by linarith) _) (norm_nonneg _)

/-- A polynomial with disk roots has a quantitative nonvanishing bound at every exterior point. -/
theorem norm_leadingCoeff_mul_pow_le_norm_eval {p : ℂ[X]}
    (hr : ∀ r ∈ p.roots, ‖r‖ ≤ 1) {z : ℂ} (hz : 1 < ‖z‖) :
    ‖p.leadingCoeff‖ * (‖z‖ - 1) ^ p.natDegree ≤ ‖p.eval z‖ := by
  have hs := IsAlgClosed.splits p
  rw [hs.eval_eq_prod_roots, norm_mul, hs.natDegree_eq_card_roots]
  exact mul_le_mul_of_nonneg_left (pow_card_le_norm_rootProduct z hz p.roots hr)
    (norm_nonneg _)

end RealRooted.TuranHurwitz
