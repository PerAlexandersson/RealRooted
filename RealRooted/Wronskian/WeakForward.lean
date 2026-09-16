import RealRooted.Interlacing.Multiplicity
import RealRooted.Interlacing.Residue
import RealRooted.Mathlib.RingTheory.Polynomial.Wronskian
import RealRooted.Wronskian.Forward

/-!
# Weak forward Wronskian orientation

This file extends the strict forward Wronskian theorems to proper-position
pairs with common roots.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- Proper position with positive leading coefficients gives global
nonnegativity of the oriented Wronskian.  Common roots are removed
recursively; after they are exhausted, the existing strict same-degree and
successor-degree Wronskian theorems apply. -/
theorem wronskian_eval_nonneg_of_prec {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hprec : Prec q p) (t : ℝ) :
    0 ≤ (Polynomial.wronskian q p).eval t := by
  generalize hn : p.natDegree = n
  induction n using Nat.strong_induction_on generalizing p q with
  | h n ih =>
      subst hn
      by_cases hcommon : ∃ r : ℝ, p.IsRoot r ∧ q.IsRoot r
      · obtain ⟨r, hrp, hrq⟩ := hcommon
        let p₁ := p /ₘ (X - C r)
        let q₁ := q /ₘ (X - C r)
        have hp₁_pos : HasPosLeadingCoeff p₁ :=
          hp_pos.divByMonic_X_sub_C hrp
        have hq₁_pos : HasPosLeadingCoeff q₁ :=
          hq_pos.divByMonic_X_sub_C hrq
        have hprec₁ : Prec q₁ p₁ :=
          prec_cofactor_of_common_root hprec hrp hrq
        have hp₁_deg : p₁.natDegree < p.natDegree := by
          simp only [p₁]
          rw [natDegree_divByMonic_X_sub_C]
          have hpdeg : 0 < p.natDegree := by
            simpa [degree_eq_natDegree hp_pos.ne_zero] using
              degree_pos_of_root hp_pos.ne_zero hrp
          lia
        have hrec := ih p₁.natDegree hp₁_deg hp₁_pos hq₁_pos hprec₁ rfl
        have hp_factor : (X - C r) * p₁ = p :=
          mul_divByMonic_eq_iff_isRoot.mpr hrp
        have hq_factor : (X - C r) * q₁ = q :=
          mul_divByMonic_eq_iff_isRoot.mpr hrq
        rw [← hp_factor, ← hq_factor, wronskian_mul_both, eval_mul,
          eval_pow]
        exact mul_nonneg (sq_nonneg _) hrec
      · push Not at hcommon
        rcases hprec.natDegree_eq_or_eq_succ with hsame | hsucc
        · by_cases hpdeg : p.natDegree = 0
          · have hqdeg : q.natDegree = 0 := by lia
            rw [eq_C_of_natDegree_eq_zero hpdeg,
              eq_C_of_natDegree_eq_zero hqdeg]
            simp [wronskian]
          · have hstrict : StrictPrecSameDegree q p :=
              StrictPrecSameDegree.of_prec_of_no_common hprec hsame.symm
                (fun r hrq hrp => hcommon r hrp hrq)
            have hpos := wronskian_pos_of_strictPrecSameDegree
              hq_pos hp_pos (Nat.pos_of_ne_zero hpdeg) hstrict t
            rw [Polynomial.wronskian, eval_sub, eval_mul, eval_mul]
            nlinarith
        · have hp_nodup : p.roots.Nodup := by
            by_contra hdup
            obtain ⟨r, hrp, hrq⟩ :=
              exists_common_root_of_not_nodup hprec hdup
            exact hcommon r ((mem_roots hp_pos.ne_zero).mp hrp)
              ((mem_roots hq_pos.ne_zero).mp hrq)
          have hq_nodup : q.roots.Nodup := by
            by_contra hdup
            obtain ⟨r, hrp, hrq⟩ :=
              exists_common_root_of_not_nodup_g hprec hdup
            exact hcommon r ((mem_roots hp_pos.ne_zero).mp hrp)
              ((mem_roots hq_pos.ne_zero).mp hrq)
          have hpos := wronskian_pos_of_prec_succ hp_pos hq_pos hsucc
            hprec hp_nodup hq_nodup hcommon t
          rw [Polynomial.wronskian, eval_sub, eval_mul, eval_mul]
          nlinarith

end

end RealRooted
