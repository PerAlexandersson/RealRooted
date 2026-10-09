import RealRooted.EulerBidiagonal.Location

/-!
# Lemma B′: `T q ≪ T ((X - ρ) q)`

For a negative-simple `q` of degree `m` and every real `ρ`, the polynomial `T ((X - C ρ) * q)`
strictly interlaces `T q` on the right and shares no root with it, where
`T = generalStep κ a b u v`.  The proof evaluates the identity
`T ((X - ρ) q) = (X - ρ) T q + X · generalComparison q` at the roots of `T q`, where the sign of
the comparison polynomial is given by `generalComparison_sign_at_generalStep_root`.
-/

open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

/-- `T` maps a negative-simple polynomial of degree `m` to a negative-simple polynomial of degree
`m + 1`, for every `m`; the nonnegative-coefficient hypothesis is automatic. -/
theorem isNegativeSimple_generalStep_of_natDegree
    (κ a b u v : ℝ) (q : ℝ[X]) (m : ℕ) (hq : IsNegativeSimple q) (hqdeg : q.natDegree = m)
    (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (hell : ∀ k ≤ m, 0 < u + v * k)
    (hQ : ∀ t ≤ 0, comparisonDefect κ a b u v t < 0) :
    IsNegativeSimple (generalStep κ a b u v q) ∧
      (generalStep κ a b u v q).natDegree = m + 1 := by
  cases m with
  | zero =>
      exact isNegativeSimple_generalStep_zero κ a b u v q hκ ha hb (by simpa using hell 0 le_rfl)
        hq hqdeg
  | succ m =>
      have hqcoeff : HasNonnegCoeffs q :=
        ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hq.2.1).2
          ⟨hq.2.2.2.1, fun r hr => (hq.2.2.2.2 r hr).le⟩).1
      exact isNegativeSimple_generalStep_of_pos κ a b u v q (m + 1) (by lia) hq hqdeg hκ ha hb hell
        hQ hqcoeff

/-- **Lemma B′.** `T ((X - C ρ) * q)` strictly interlaces `T q` on the right, with no common
root, for every real `ρ`. -/
theorem strictInterl_generalStep_mul_X_sub_C
    (κ a b u v ρ : ℝ) (q : ℝ[X]) (m : ℕ) (hq : IsNegativeSimple q) (hqdeg : q.natDegree = m)
    (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (hell : ∀ k ≤ m + 1, 0 < u + v * k)
    (hQ : ∀ t ≤ 0, comparisonDefect κ a b u v t < 0) :
    StrictInterl (generalStep κ a b u v q) (generalStep κ a b u v ((X - C ρ) * q)) ∧
      ∀ x, (generalStep κ a b u v q).IsRoot x →
        ¬ (generalStep κ a b u v ((X - C ρ) * q)).IsRoot x := by
  obtain ⟨hTq, hTdeg⟩ := isNegativeSimple_generalStep_of_natDegree κ a b u v q m hq hqdeg hκ ha hb
    (fun k hk => hell k (by lia)) hQ
  have hqlc : 0 < q.leadingCoeff := hq.2.2.2.1
  have hxq : ((X - C ρ) * q).natDegree = m + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero ρ) hq.1, natDegree_X_sub_C, hqdeg]
    lia
  have hxqlc : HasPosLeadingCoeff ((X - C ρ) * q) := by
    simpa [HasPosLeadingCoeff, leadingCoeff_mul] using hqlc
  obtain ⟨hFdeg, hFlc⟩ := generalStep_natDegree_and_leadingCoeff κ a b u v ((X - C ρ) * q) (m + 1)
    hxq hxqlc hell
  refine strictInterl_of_eval_mul_neg_one_pow_countP_neg hTq.1 hTq.2.1 hTq.2.2.1.roots_nodup
    (by lia) hFlc (by lia) ?_
  intro x hx
  have hA1 := generalComparison_sign_at_generalStep_root κ a b u v q m hq hqdeg hκ ha hb
    (fun k hk => hell k (by lia)) hQ x hx
  have hxneg : x < 0 := hTq.2.2.2.2 x hx
  have hxroot : (generalStep κ a b u v q).eval x = 0 := isRoot_of_mem_roots hx
  have hF : (generalStep κ a b u v ((X - C ρ) * q)).eval x =
      x * (generalComparison κ a b v q).eval x := by
    rw [generalStep_sub]
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, hxroot, mul_zero, zero_add]
  rw [hF, mul_assoc]
  exact mul_neg_of_neg_of_pos hxneg hA1

end RealRooted.EulerBidiagonal
