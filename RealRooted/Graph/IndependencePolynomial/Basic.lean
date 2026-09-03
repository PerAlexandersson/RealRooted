import RealRooted.Compatibility.Pair
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Independence polynomials of finite graphs

This file defines unweighted and vertex-weighted independence polynomials,
both globally and on a finite vertex support. It provides their elementary
coefficient, nonvanishing, positivity, empty-support, and compatibility API.

Graph-specific recurrences and claw-free arguments belong in higher modules.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

/-- Independence-generating polynomial of a finite simple graph. -/
def indepPoly {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact ∑ s ∈ (Finset.univ.powerset.filter fun s : Finset V =>
      G.IsIndepSet (s : Set V)),
    (X : ℝ[X]) ^ s.card

/-- Independent subsets of a fixed finite vertex support. -/
def indepSetsOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Finset V) :=
  S.powerset.filter fun s : Finset V => G.IsIndepSet (s : Set V)

/-- Support-restricted independence polynomial. -/
def indepPolyOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℝ[X] :=
  ∑ s ∈ indepSetsOn G S, (X : ℝ[X]) ^ s.card

/-- Weighted support-restricted independence polynomial. The unweighted
version is the specialization where every vertex has weight `1`. -/
def weightedIndepPolyOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (wt : V → ℝ) : ℝ[X] :=
  ∑ s ∈ indepSetsOn G S, (∏ v ∈ s, C (wt v)) * (X : ℝ[X]) ^ s.card

/-- Weighted independence polynomial of a finite graph. -/
def weightedIndepPoly {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (wt : V → ℝ) : ℝ[X] :=
  weightedIndepPolyOn G Finset.univ wt

/-- The weighted support-restricted definition recovers the global weighted
independence polynomial on the full vertex set. -/
theorem weightedIndepPoly_eq_weightedIndepPolyOn_univ
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ) :
    weightedIndepPoly G wt = weightedIndepPolyOn G Finset.univ wt := by
  rfl

/-- The weighted support-restricted independence polynomial with all weights
equal to `1` is the unweighted support-restricted independence polynomial. -/
theorem weightedIndepPolyOn_one {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    weightedIndepPolyOn G S (fun _ ↦ 1) = indepPolyOn G S := by
  unfold weightedIndepPolyOn indepPolyOn
  simp

/-- The empty independent set gives the constant coefficient of the weighted
support-restricted independence polynomial. -/
theorem weightedIndepPolyOn_coeff_zero {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (wt : V → ℝ) :
    (weightedIndepPolyOn G S wt).coeff 0 = 1 := by
  classical
  rw [weightedIndepPolyOn, Polynomial.finsetSum_coeff, Finset.sum_eq_single ∅]
  · simp
  · intro s hs hne
    have : s.card ≠ 0 := by simp_all
    have hnot : ¬ s.card ≤ 0 := by simp_all
    rw [Polynomial.coeff_mul_X_pow', if_neg hnot]
  · intro hnot
    simp [indepSetsOn] at hnot

/-- Weighted support-restricted independence polynomials are nonzero. -/
theorem weightedIndepPolyOn_ne_zero {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (wt : V → ℝ) :
    weightedIndepPolyOn G S wt ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) h
  simp [weightedIndepPolyOn_coeff_zero] at hcoeff

/-- Weighted support-restricted independence polynomials have nonnegative
coefficients when all vertex weights on the support are nonnegative. -/
theorem weightedIndepPolyOn_hasNonnegCoeffs {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {wt : V → ℝ}
    (hwt : ∀ v ∈ S, 0 ≤ wt v) :
    HasNonnegCoeffs (weightedIndepPolyOn G S wt) := by
  classical
  have hprod :
      ∀ t : Finset V, t ⊆ S → HasNonnegCoeffs (∏ v ∈ t, C (wt v)) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro _hsub
      simp [hasNonnegCoeffs_one]
    · intro v t hv ih hsub
      rw [Finset.prod_insert hv]
      have hv_nonneg : HasNonnegCoeffs (C (wt v)) := by
        simpa using nonnegCoeffs_C_mul (hwt v (hsub (Finset.mem_insert_self v t)))
          hasNonnegCoeffs_one
      have hsub_t : t ⊆ S := fun w hw => hsub (Finset.mem_insert.mpr (Or.inr hw))
      exact hv_nonneg.mul (ih hsub_t)
  intro n
  rw [weightedIndepPolyOn, Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun t ht => by
    have hsub : t ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    have hXpow : HasNonnegCoeffs ((X : ℝ[X]) ^ t.card) := by
      intro m
      rw [coeff_X_pow]
      split <;> norm_num
    exact ((hprod t hsub).mul hXpow) n

/-- Weighted support-restricted independence polynomials have positive leading
coefficient under nonnegative weights on the support. -/
theorem weightedIndepPolyOn_hasPosLeadingCoeff {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {wt : V → ℝ}
    (hwt : ∀ v ∈ S, 0 ≤ wt v) :
    HasPosLeadingCoeff (weightedIndepPolyOn G S wt) :=
  (weightedIndepPolyOn_hasNonnegCoeffs G hwt).pos_leadingCoeff
    (weightedIndepPolyOn_ne_zero G S wt)

/-- The weighted independence polynomial on the empty support is `1`. -/
theorem weightedIndepPolyOn_empty {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ) :
    weightedIndepPolyOn G (∅ : Finset V) wt = 1 := by
  rw [weightedIndepPolyOn]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro s hs hne
    have hs' : s = ∅ ∧ G.IsIndepSet (s : Set V) := by simpa [indepSetsOn] using hs
    simp_all
  · intro hnot
    simp [indepSetsOn] at hnot

/-- The weighted independence polynomial on the empty support splits. -/
theorem weightedIndepPolyOn_empty_splits {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ) :
    (weightedIndepPolyOn G (∅ : Finset V) wt).Splits := by
  rw [weightedIndepPolyOn_empty]
  simp

/-- Support-restricted independence polynomials are nonzero. -/
theorem indepPolyOn_ne_zero {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    indepPolyOn G S ≠ 0 := by
  simpa [weightedIndepPolyOn_one] using
    (weightedIndepPolyOn_ne_zero G S fun _ => 1)

/-- Support-restricted independence polynomials have nonnegative coefficients. -/
theorem indepPolyOn_hasNonnegCoeffs {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    HasNonnegCoeffs (indepPolyOn G S) := by
  simpa [weightedIndepPolyOn_one] using
    (weightedIndepPolyOn_hasNonnegCoeffs (G := G) (S := S) (wt := fun _ ↦ 1)
      (by simp))

/-- Support-restricted independence polynomials have positive leading coefficient. -/
theorem indepPolyOn_hasPosLeadingCoeff {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    HasPosLeadingCoeff (indepPolyOn G S) :=
  (indepPolyOn_hasNonnegCoeffs G S).pos_leadingCoeff (indepPolyOn_ne_zero G S)

/-- The empty support has independence polynomial `1`. -/
theorem indepPolyOn_empty {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    indepPolyOn G (∅ : Finset V) = 1 := by
  have h := weightedIndepPolyOn_empty G (fun _ : V => (1 : ℝ))
  rw [weightedIndepPolyOn] at h
  simpa [indepPolyOn] using h

/-- The empty support independence polynomial splits. -/
theorem indepPolyOn_empty_splits {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    (indepPolyOn G (∅ : Finset V)).Splits := by
  rw [indepPolyOn_empty]
  simp

/-- If a weighted support-restricted independence polynomial is real-rooted,
then it is compatible with its `X`-multiple. -/
theorem compatible_weightedIndepPolyOn_X_mul_self_of_splits
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (wt : V → ℝ) (hS : (weightedIndepPolyOn G S wt).Splits) :
    Compatible (weightedIndepPolyOn G S wt)
      (X * weightedIndepPolyOn G S wt) :=
  Compatible.self_X_mul_of_splits hS

/-- If a support-restricted independence polynomial is real-rooted, then it is
compatible with its `X`-multiple. -/
theorem compatible_indepPolyOn_X_mul_self_of_splits {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hS : (indepPolyOn G S).Splits) :
    Compatible (indepPolyOn G S) (X * indepPolyOn G S) :=
  Compatible.self_X_mul_of_splits hS

/-- The support-restricted definition recovers `indepPoly` on the full vertex set. -/
theorem indepPoly_eq_indepPolyOn_univ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    indepPoly G = indepPolyOn G Finset.univ := by
  unfold indepPoly indepPolyOn indepSetsOn
  grind

end Graph
end RealRooted
