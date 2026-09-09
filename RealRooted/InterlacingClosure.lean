import RealRooted.ObreschkoffConverse
import RealRooted.RootContinuity

/-!
# Interlacing closure under coefficientwise limits

This file proves that weak interlacing is preserved by coefficientwise limits
when both polynomial degrees stay fixed and all polynomials are monic. The
proof avoids choosing continuously ordered roots: proper position makes every
real linear combination split, and polynomial root continuity passes that
property to the limit one combination at a time.
-/

open Polynomial Filter Topology

noncomputable section

namespace RealRooted

/-- A coefficientwise limit of monic, fixed-degree weakly interlacing pairs
again weakly interlaces. -/
theorem interlaces_of_monic_of_coeff_tendsto
    {p q : ℕ → ℝ[X]} {p₀ q₀ : ℝ[X]} {n : ℕ}
    (hpMonic : ∀ k, (p k).Monic) (hqMonic : ∀ k, (q k).Monic)
    (hp₀Monic : p₀.Monic) (hq₀Monic : q₀.Monic)
    (hpDegree : ∀ k, (p k).natDegree = n)
    (hqDegree : ∀ k, (q k).natDegree = n + 1)
    (hp₀Degree : p₀.natDegree = n) (hq₀Degree : q₀.natDegree = n + 1)
    (hInterlaces : ∀ k, Interlaces (p k) (q k))
    (hpCoeff : ∀ i, Tendsto (fun k => (p k).coeff i) atTop (𝓝 (p₀.coeff i)))
    (hqCoeff : ∀ i, Tendsto (fun k => (q k).coeff i) atTop (𝓝 (q₀.coeff i))) :
    Interlaces p₀ q₀ := by
  have hp₀Splits : p₀.Splits :=
    splits_of_monic_of_coeff_tendsto hp₀Monic hpMonic
      (fun k => (hpDegree k).trans hp₀Degree.symm)
      (fun k => (hInterlaces k).2.1.2) hpCoeff
  have hAll : AllComboRealRooted p₀ q₀ := by
    intro α β
    by_cases hβ : β = 0
    · simpa [hβ] using hp₀Splits.C_mul α
    · let r₀ : ℝ[X] := q₀ + C (α / β) * p₀
      let r : ℕ → ℝ[X] := fun k => q k + C (α / β) * p k
      have hDegreeLt₀ : (C (α / β) * p₀).degree < q₀.degree := by
        by_cases hαβ : α / β = 0
        · rw [hαβ, C_0, zero_mul, degree_zero]
          exact WithBot.bot_lt_iff_ne_bot.mpr
            (degree_ne_bot.mpr hq₀Monic.ne_zero)
        · rw [degree_C_mul hαβ, degree_eq_natDegree hp₀Monic.ne_zero,
            degree_eq_natDegree hq₀Monic.ne_zero, hp₀Degree, hq₀Degree]
          exact_mod_cast Nat.lt_succ_self n
      have hDegreeLt : ∀ k, (C (α / β) * p k).degree < (q k).degree := by
        intro k
        by_cases hαβ : α / β = 0
        · rw [hαβ, C_0, zero_mul, degree_zero]
          exact WithBot.bot_lt_iff_ne_bot.mpr
            (degree_ne_bot.mpr (hqMonic k).ne_zero)
        · rw [degree_C_mul hαβ, degree_eq_natDegree (hpMonic k).ne_zero,
            degree_eq_natDegree (hqMonic k).ne_zero, hpDegree k, hqDegree k]
          exact_mod_cast Nat.lt_succ_self n
      have hr₀Monic : r₀.Monic := hq₀Monic.add_of_left hDegreeLt₀
      have hrMonic : ∀ k, (r k).Monic := fun k =>
        (hqMonic k).add_of_left (hDegreeLt k)
      have hrDegree : ∀ k, (r k).natDegree = r₀.natDegree := by
        intro k
        rw [show (r k).natDegree = (q k).natDegree by
          exact natDegree_add_eq_left_of_degree_lt (hDegreeLt k),
          show r₀.natDegree = q₀.natDegree by
            exact natDegree_add_eq_left_of_degree_lt hDegreeLt₀,
          hqDegree k, hq₀Degree]
      have hrSplits : ∀ k, (r k).Splits := by
        intro k
        have hall := allComboRealRooted_of_prec (hInterlaces k).toPrec
        simpa [r, add_comm] using hall (α / β) 1
      have hrCoeff : ∀ i, Tendsto (fun k => (r k).coeff i) atTop
          (𝓝 (r₀.coeff i)) := by
        intro i
        simp only [r, r₀, coeff_add, coeff_C_mul]
        exact (hqCoeff i).add (tendsto_const_nhds.mul (hpCoeff i))
      have hr₀Splits : r₀.Splits :=
        splits_of_monic_of_coeff_tendsto hr₀Monic hrMonic hrDegree hrSplits hrCoeff
      have hscaled := hr₀Splits.C_mul β
      have heq : C β * r₀ = C α * p₀ + C β * q₀ := by
        dsimp only [r₀]
        rw [mul_add, ← mul_assoc, ← C_mul]
        have hcancel : β * (α / β) = α := by field_simp
        rw [hcancel, add_comm]
      rw [← heq]
      exact hscaled
  have hsucc : q₀.natDegree = p₀.natDegree + 1 := by
    rw [hp₀Degree, hq₀Degree]
  have hor : Prec p₀ q₀ ∨ Prec q₀ p₀ :=
    prec_of_allComboRealRooted hp₀Monic.ne_zero hp₀Splits
      hq₀Monic.ne_zero hAll.right_splits hAll (Or.inl hsucc.symm)
  exact (prec_forward_of_orientation_of_succDegree hsucc hor).toInterlaces hsucc.symm

end RealRooted
