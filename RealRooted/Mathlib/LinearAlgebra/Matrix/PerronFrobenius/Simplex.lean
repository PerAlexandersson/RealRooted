import Mathlib.Analysis.Convex.StdSimplex

/-!
# The standard simplex as a set of vectors

The Perron-Frobenius API uses membership in a set of vectors, rather than the
new bundled `Convexity.StdSimplex`. This definition preserves that interface
without depending on Mathlib's deprecated set-valued `stdSimplex` API.
-/

namespace RealRooted

open Set

/-- Nonnegative vectors whose coordinates sum to one. -/
def standardSimplex (R ι : Type*) [Semiring R] [PartialOrder R] [Fintype ι] :
    Set (ι → R) :=
  {f | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1}

theorem isCompact_standardSimplex (ι : Type*) [Fintype ι] :
    IsCompact (standardSimplex ℝ ι) := by
  apply (isCompact_Icc : IsCompact (Icc (0 : ι → ℝ) 1)).of_isClosed_subset
  · have hnonneg : IsClosed {f : ι → ℝ | ∀ i, 0 ≤ f i} := by
      simpa only [Set.setOf_forall] using
        (isClosed_iInter fun i : ι =>
          isClosed_le (continuous_const (y := (0 : ℝ))) (continuous_apply i))
    have hsum : IsClosed {f : ι → ℝ | ∑ i, f i = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    exact hnonneg.inter hsum
  · intro f hf
    refine ⟨hf.1, fun i => ?_⟩
    change f i ≤ 1
    simpa only [hf.2] using
      Finset.single_le_sum (fun j _ => hf.1 j) (Finset.mem_univ i)

instance (ι : Type*) [Fintype ι] : CompactSpace (standardSimplex ℝ ι) :=
  isCompact_iff_compactSpace.mp (isCompact_standardSimplex ι)

theorem convex_standardSimplex (ι : Type*) [Fintype ι] :
    Convex ℝ (standardSimplex ℝ ι) := by
  intro f hf g hg a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hf.1 i)) (mul_nonneg hb (hg.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hf.2, hg.2, mul_one, hab]

end RealRooted
