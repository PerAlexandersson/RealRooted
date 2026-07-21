import RealRooted.GeneralizedLiuWang
import RealRooted.MaWang

/-!
# Magnitude-dominated lag certificates

Small wrappers for recurrence steps where a dominant negative term at the
roots of the current row gives the sign condition needed by the Ma-Wang /
generalized Liu-Wang interlacing criteria.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Magnitude-dominated lag interlacing criterion in the successor-degree case. -/
theorem prec_of_magnitude_dominated_succ
    {f g₁ g₂ a b₁ b₂ : ℝ[X]}
    (hg₁f : Interlaces g₁ f) (hg₁_pos : HasPosLeadingCoeff g₁)
    (hF_pos : HasPosLeadingCoeff (a * f + b₁ * g₁ + b₂ * g₂))
    (hdeg : (a * f + b₁ * g₁ + b₂ * g₂).natDegree = f.natDegree + 1)
    (hcert : ∀ r, f.IsRoot r →
      b₁.eval r * (g₁.eval r) ^ 2 + b₂.eval r * (g₂.eval r * g₁.eval r) < 0) :
    Prec f (a * f + b₁ * g₁ + b₂ * g₂) := by
  refine prec_of_interlaces_eval_mul_neg_succ hg₁f hg₁_pos hF_pos hdeg ?_
  intro r hr
  have hf0 : f.eval r = 0 := hr
  have hcert_r := hcert r hr
  calc
    (a * f + b₁ * g₁ + b₂ * g₂).eval r * g₁.eval r
        = b₁.eval r * (g₁.eval r) ^ 2 +
            b₂.eval r * (g₂.eval r * g₁.eval r) := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, hf0]
          ring
    _ < 0 := hcert_r

/-- Magnitude-dominated lag interlacing criterion in the same-degree case. -/
theorem prec_of_magnitude_dominated_same
    {f g₁ g₂ a b₁ b₂ : ℝ[X]}
    (hg₁f : Interlaces g₁ f) (hg₁_pos : HasPosLeadingCoeff g₁)
    (hF_pos : HasPosLeadingCoeff (a * f + b₁ * g₁ + b₂ * g₂))
    (hdeg : (a * f + b₁ * g₁ + b₂ * g₂).natDegree = f.natDegree)
    (hcert : ∀ r, f.IsRoot r →
      b₁.eval r * (g₁.eval r) ^ 2 + b₂.eval r * (g₂.eval r * g₁.eval r) < 0) :
    Prec f (a * f + b₁ * g₁ + b₂ * g₂) := by
  refine prec_of_interlaces_eval_mul_neg_same hg₁f hg₁_pos hF_pos hdeg ?_
  intro r hr
  have hf0 : f.eval r = 0 := hr
  have hcert_r := hcert r hr
  calc
    (a * f + b₁ * g₁ + b₂ * g₂).eval r * g₁.eval r
        = b₁.eval r * (g₁.eval r) ^ 2 +
            b₂.eval r * (g₂.eval r * g₁.eval r) := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, hf0]
          ring
    _ < 0 := hcert_r

/-- Degree-bounded magnitude-dominated criterion. -/
theorem prec_of_magnitude_dominated
    {f g₁ g₂ a b₁ b₂ : ℝ[X]}
    (hg₁f : Interlaces g₁ f) (hg₁_pos : HasPosLeadingCoeff g₁)
    (hF_pos : HasPosLeadingCoeff (a * f + b₁ * g₁ + b₂ * g₂))
    (hdeg_lo : f.natDegree ≤ (a * f + b₁ * g₁ + b₂ * g₂).natDegree)
    (hdeg_hi : (a * f + b₁ * g₁ + b₂ * g₂).natDegree ≤ f.natDegree + 1)
    (hcert : ∀ r, f.IsRoot r →
      b₁.eval r * (g₁.eval r) ^ 2 + b₂.eval r * (g₂.eval r * g₁.eval r) < 0) :
    Prec f (a * f + b₁ * g₁ + b₂ * g₂) := by
  rcases (by
      lia : (a * f + b₁ * g₁ + b₂ * g₂).natDegree = f.natDegree ∨
        (a * f + b₁ * g₁ + b₂ * g₂).natDegree = f.natDegree + 1) with hsame | hsucc
  · exact prec_of_magnitude_dominated_same hg₁f hg₁_pos hF_pos hsame hcert
  · exact prec_of_magnitude_dominated_succ hg₁f hg₁_pos hF_pos hsucc hcert

/-- Build the pointwise magnitude certificate from an absolute-value domination bound. -/
theorem magnitude_cert_of_abs_dominated
    {b₁ g₁ b₂ g₂ : ℝ[X]} {r : ℝ}
    (hhead : b₁.eval r * (g₁.eval r) ^ 2 < 0)
    (hdom : |b₂.eval r * (g₂.eval r * g₁.eval r)| <
      |b₁.eval r * (g₁.eval r) ^ 2|) :
    b₁.eval r * (g₁.eval r) ^ 2 + b₂.eval r * (g₂.eval r * g₁.eval r) < 0 := by
  have h₁ : |b₁.eval r * (g₁.eval r) ^ 2| = -(b₁.eval r * (g₁.eval r) ^ 2) :=
    abs_of_neg hhead
  have h₂ : b₂.eval r * (g₂.eval r * g₁.eval r) ≤
      |b₂.eval r * (g₂.eval r * g₁.eval r)| :=
    le_abs_self _
  linarith [h₂, hdom, h₁]

end RealRooted
