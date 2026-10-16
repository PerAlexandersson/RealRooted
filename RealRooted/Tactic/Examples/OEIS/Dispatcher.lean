module

public import RealRooted.Tactic.OEIS

/-!
# OEIS dispatcher regressions

Literal downstream row statements exercise the target dispatcher. Small certificate goals
exercise each named frontend.
-/

@[expose] public noncomputable section

open Polynomial

namespace RealRooted.Tactic.Examples.OEIS.Dispatcher

/-- The downstream A111006 recurrence, with its original generated presentation. -/
def A111006 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => (X) * A111006 (n + 1) + ((X + (X) ^ (2))) * A111006 n

/-- The literal downstream A111006 interlacing statement. -/
theorem A111006_interlaces (n : ℕ) :
    RealRooted.Interlaces (A111006 n) (A111006 (n + 1)) := by
  rr_oeis

/-- The literal downstream A111006 splitting statement. -/
theorem A111006_splits (n : ℕ) : (A111006 n).Splits := by
  rr_oeis

example (n : ℕ) : RealRooted.Interlaces (A111006 n) (A111006 (n + 1)) := by
  rr_oeis liu_wang

example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : RealRooted.HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : RealRooted.HasPosLeadingCoeff f)
    (hroot_sign : ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    RealRooted.StrictInterl f (u * f + v * f.derivative) := by
  rr_oeis ma_wang

example {P : ℕ → ℝ[X]} {α β : ℕ → ℝ}
    (hrec : RealRooted.SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : ℕ, 0 < β (n + 1)) :
    ∀ n : ℕ, RealRooted.StrictInterl (P n) (P (n + 1)) := by
  rr_oeis favard

example {n : ℕ} (hn : 0 < n) (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, RealRooted.HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      RealRooted.Has2x2InterlacingProperty
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : RealRooted.IsInterlacingSeqNonneg fs) :
    RealRooted.IsInterlacingSeqNonneg (RealRooted.matPolyAction G fs) := by
  rr_oeis matrix

end RealRooted.Tactic.Examples.OEIS.Dispatcher
