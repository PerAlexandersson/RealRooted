module

public import RealRooted.LiuWang.CombinedFlux

/-!
# The Liu--Wang criterion in full generality

Liu and Wang (2007, Theorem 2.1): let `g ≪ f`, where `g` has positive leading coefficient, and
put `F = a f + b g` with `deg f ≤ deg F ≤ deg f + 1` and positive leading coefficient.  If `b`
is nonpositive at the roots of `f`, then `f ≪ F`.

Here `g ≪ f` may have either shape (`deg g = deg f` or `deg g + 1 = deg f`), and `f`, `g` may
have common and repeated roots. This is the singleton case of the combined-flux criterion.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.LiuWang

/-- The Liu--Wang criterion when `f` also has positive leading coefficient. -/
private theorem strictInterl_mul_add_mul_of_eval_nonpos_of_pos {f g a b : ℝ[X]}
    (hgf : StrictInterl g f) (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hb : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    StrictInterl f (a * f + b * g) := by
  have h := strictInterl_mul_add_sum_mul_of_combined_flux_of_pos hf_pos hgf.2.1.2
    (s := ({0} : Finset Unit)) (b := fun _ : Unit ↦ b) (g := fun _ : Unit ↦ g)
    (fun i hi ↦ by simpa using hgf)
    (fun i hi ↦ by simpa using hg_pos)
    (fun r hr ↦ by
      simp only [Finset.sum_singleton, eval_mul]
      simpa [mul_assoc] using mul_nonpos_of_nonpos_of_nonneg (hb r hr)
        (hgf.eval_mul_eval_derivative_nonneg hg_pos hf_pos hr))
    (fun i hi r hr _ ↦ by simpa using hb r hr)
    (by simpa using hF_pos) (by simpa using hdeg_lo) (by simpa using hdeg_hi)
  simpa using h

/-- **Liu--Wang criterion** (Liu--Wang 2007, Theorem 2.1).  Let `g ≪ f` (`StrictInterl g f`,
of either degree shape) with `g` of positive leading coefficient, and let
`F = a f + b g` have positive leading coefficient and degree `deg f` or `deg f + 1`.  If `b` is
nonpositive at every root of `f`, then `f ≪ F`.

Common and repeated roots of `f` and `g` are allowed, and the sign of the leading coefficient
of `f` is arbitrary. -/
theorem strictInterl_mul_add_mul_of_eval_nonpos {f g a b : ℝ[X]}
    (hgf : StrictInterl g f) (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hb : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    StrictInterl f (a * f + b * g) := by
  have hf_ne : f ≠ 0 := hgf.2.1.1
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hf_ne) with hneg | hpos
  · have hF_eq : a * f + b * g = -a * -f + b * g := by ring
    have hnf_pos : HasPosLeadingCoeff (-f) := by
      simpa [HasPosLeadingCoeff, leadingCoeff_neg] using hneg
    have hgnf : StrictInterl g (-f) := by
      simpa using hgf.C_mul_right (a := -1) (by norm_num)
    rw [hF_eq] at hF_pos hdeg_lo hdeg_hi ⊢
    have h := strictInterl_mul_add_mul_of_eval_nonpos_of_pos hgnf hnf_pos hg_pos hF_pos
      (by rwa [natDegree_neg]) (by rwa [natDegree_neg])
      (fun r hr ↦ hb r (by simpa using hr))
    simpa using h.C_mul_left (a := -1) (by norm_num)
  · exact strictInterl_mul_add_mul_of_eval_nonpos_of_pos
      hgf hpos hg_pos hF_pos hdeg_lo hdeg_hi hb

end RealRooted.LiuWang
