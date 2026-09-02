module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Complex.Polynomial.Basic

public section

noncomputable section

namespace Polynomial

/-- A real polynomial splits if every root of its complexification is real. -/
lemma splits_of_all_roots_real {p : ℝ[X]}
    (hall : ∀ z : ℂ, (p.map Complex.ofRealHom).eval z = 0 → z.im = 0) :
    p.Splits := by
  refine Splits.of_splits_map Complex.ofRealHom (IsAlgClosed.splits _) ?_
  intro z hz
  refine ⟨z.re, ?_⟩
  rw [← Complex.re_add_im z, hall z (isRoot_of_mem_roots hz)]
  simp

end Polynomial
