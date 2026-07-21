import RealRooted.AllCombo
import RealRooted.Derivative
import RealRooted.MagnitudeDominated
import RealRooted.ObreschkoffConverse
import RealRooted.WagnerRightSum

/-!
# Upper-derivative and magnitude reducers

Reusable reductions for recurrence steps where the remaining certificate is a
pointwise sign statement at the roots of the current row.  The lemmas here do
not assert a generic upper-derivative interlacer; the needed `Prec d f`
hypothesis is supplied by the concrete family.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Derivative sign-agreement at a root, reduced to a supplied `Prec d f`. -/
theorem prec_deriv_eval_mul_deriv_nonneg
    {f d : ℝ[X]}
    (hf_splits : f.Splits) (hf_deg : 2 ≤ f.natDegree)
    (hfp_pos : HasPosLeadingCoeff f.derivative)
    (hdf : Prec d f) (hd_pos : HasPosLeadingCoeff d)
    {r : ℝ} (hr : f.IsRoot r) :
    0 ≤ d.eval r * f.derivative.eval r := by
  have hfpf : Prec f.derivative f := (derivative_interlaces hf_splits hf_deg).toPrec
  simpa [mul_comm] using
    eval_mul_eval_nonneg_of_prec_right hdf hfpf hd_pos hfp_pos hr

/-- Structural magnitude certificate when the lag polynomial also precedes the current row. -/
theorem magnitude_cert_auto
    {f g₁ g₂ b₁ b₂ : ℝ[X]}
    (hg₁f : Interlaces g₁ f) (hg₁_pos : HasPosLeadingCoeff g₁)
    (hg₂f : Prec g₂ f) (hg₂_pos : HasPosLeadingCoeff g₂)
    (hsimple : ∀ r, f.IsRoot r → g₁.eval r ≠ 0)
    (hb₁ : ∀ r, f.IsRoot r → b₁.eval r < 0)
    (hb₂ : ∀ r, f.IsRoot r → b₂.eval r ≤ 0) :
    ∀ r, f.IsRoot r →
      b₁.eval r * (g₁.eval r) ^ 2 + b₂.eval r * (g₂.eval r * g₁.eval r) < 0 := by
  intro r hr
  have hg₁prec : Prec g₁ f := hg₁f.toPrec
  have hcross : 0 ≤ g₂.eval r * g₁.eval r :=
    eval_mul_eval_nonneg_of_prec_right hg₂f hg₁prec hg₂_pos hg₁_pos hr
  have hg₁sq : 0 < (g₁.eval r) ^ 2 := by
    have hne := hsimple r hr
    positivity
  have hhead : b₁.eval r * (g₁.eval r) ^ 2 < 0 :=
    mul_neg_of_neg_of_pos (hb₁ r hr) hg₁sq
  have hlag : b₂.eval r * (g₂.eval r * g₁.eval r) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (hb₂ r hr) hcross
  linarith

/-- Drop-in composition of `magnitude_cert_auto` with the successor-degree criterion. -/
theorem prec_of_magnitude_dominated_auto
    {f g₁ g₂ a b₁ b₂ : ℝ[X]}
    (hg₁f : Interlaces g₁ f) (hg₁_pos : HasPosLeadingCoeff g₁)
    (hg₂f : Prec g₂ f) (hg₂_pos : HasPosLeadingCoeff g₂)
    (hsimple : ∀ r, f.IsRoot r → g₁.eval r ≠ 0)
    (hb₁ : ∀ r, f.IsRoot r → b₁.eval r < 0)
    (hb₂ : ∀ r, f.IsRoot r → b₂.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + b₁ * g₁ + b₂ * g₂))
    (hdeg : (a * f + b₁ * g₁ + b₂ * g₂).natDegree = f.natDegree + 1) :
    Prec f (a * f + b₁ * g₁ + b₂ * g₂) :=
  prec_of_magnitude_dominated_succ hg₁f hg₁_pos hF_pos hdeg
    (magnitude_cert_auto hg₁f hg₁_pos hg₂f hg₂_pos hsimple hb₁ hb₂)

/-- Orient an all-combinations real-rooted pair in the successor-degree case. -/
theorem interlaces_of_allComboRealRooted_succDegree
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hall : AllComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    Interlaces f g := by
  have hf_splits : f.Splits := (hall.isRealRooted_left hf_ne).2
  have hg_splits : g.Splits := (hall.isRealRooted_right hg_ne).2
  have hor : Prec f g ∨ Prec g f :=
    prec_of_allComboRealRooted hf_ne hf_splits hg_ne hg_splits hall (Or.inl hsucc.symm)
  exact (prec_forward_of_orientation_of_succDegree hsucc hor).toInterlaces hsucc.symm

end RealRooted
