import RealRooted.CubicDiscriminant
import RealRooted.Graph.IndependencePolynomial.Multivariate
import RealRooted.Graph.IndependencePolynomial.Recurrence

/-!
# The Leake--Ryder claw-free characterization

The multivariate independence polynomial of a finite graph is same-phase
stable exactly when the graph is claw-free.  For the converse, zero coordinate
weights isolate an induced claw.  Its univariate independence polynomial is
`1 + 4 * X + 3 * X ^ 2 + X ^ 3`, whose cubic discriminant is negative.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

/-- Terms supported outside `T` vanish when all their extra vertex weights
are zero. -/
theorem weightedIndepPolyOn_eq_of_subset_of_eq_zero
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {T S : Finset V} {wt : V → ℝ} (hTS : T ⊆ S)
    (hzero : ∀ v ∈ S, v ∉ T → wt v = 0) :
    weightedIndepPolyOn G S wt = weightedIndepPolyOn G T wt := by
  unfold weightedIndepPolyOn
  symm
  apply Finset.sum_subset
  · intro t ht
    simp only [indepSetsOn, Finset.mem_filter, Finset.mem_powerset] at ht ⊢
    exact ⟨fun v hv => hTS (ht.1 hv), ht.2⟩
  · intro t htS htT
    have ht_not_sub : ¬ t ⊆ T := by
      intro ht_sub
      apply htT
      simp only [indepSetsOn, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨ht_sub, (Finset.mem_filter.mp htS).2⟩
    obtain ⟨v, hvt, hvT⟩ := Finset.not_subset.mp ht_not_sub
    have ht_sub_S : t ⊆ S :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp htS).1
    have hv_zero : wt v = 0 := hzero v (ht_sub_S hvt) hvT
    have hprod : (∏ w ∈ t, C (wt w)) = 0 :=
      Finset.prod_eq_zero hvt (by simp [hv_zero])
    rw [hprod, zero_mul]

/-- Indicator weights restrict the global weighted polynomial to a specified
vertex support. -/
theorem weightedIndepPoly_eq_indepPolyOn_indicator
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) :
    weightedIndepPoly G (fun v => if v ∈ T then 1 else 0) =
      indepPolyOn G T := by
  rw [weightedIndepPoly_eq_weightedIndepPolyOn_univ]
  calc
    weightedIndepPolyOn G Finset.univ
        (fun v => if v ∈ T then 1 else 0) =
        weightedIndepPolyOn G T
          (fun v => if v ∈ T then 1 else 0) := by
      apply weightedIndepPolyOn_eq_of_subset_of_eq_zero G
      · simp
      · simp
    _ = weightedIndepPolyOn G T (fun _ => 1) := by
      apply weightedIndepPolyOn_congr G
      simp
    _ = indepPolyOn G T := weightedIndepPolyOn_one G T

/-- The independence polynomial on an independent support is a binomial
power. -/
theorem indepPolyOn_eq_one_add_X_pow_of_isIndepSet
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : G.IsIndepSet (S : Set V)) :
    indepPolyOn G S = (1 + X) ^ S.card := by
  have hsets : indepSetsOn G S = S.powerset := by
    ext t
    simp only [indepSetsOn, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · exact fun h => h.1
    · intro ht
      exact ⟨ht, hS.mono (by exact_mod_cast ht)⟩
  rw [indepPolyOn, hsets]
  ext k
  rw [Polynomial.finsetSum_coeff, Polynomial.coeff_one_add_X_pow]
  simp only [Polynomial.coeff_X_pow]
  rw [Finset.sum_boole]
  norm_cast
  simpa [Finset.powersetCard_eq_filter, eq_comm] using
    (Finset.card_powersetCard k S)

/-- The support consisting of a claw center and three independent neighbors
has the universal claw obstruction polynomial. -/
theorem indepPolyOn_claw_obstruction
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {v : V} {s : Finset V} (hneigh : ∀ w ∈ s, G.Adj v w)
    (hind : G.IsNIndepSet 3 s) :
    indepPolyOn G (insert v s) =
      1 + 4 * X + 3 * X ^ 2 + X ^ 3 := by
  have hv : v ∉ s := by
    intro hvs
    exact (G.loopless.irrefl v) (hneigh v hvs)
  have hfilter : s.filter (fun w => ¬ G.Adj v w) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro w hw
    simp [hneigh w hw]
  rw [indepPolyOn_insert G hv,
    indepPolyOn_eq_one_add_X_pow_of_isIndepSet G s hind.isIndepSet,
    hind.card_eq, hfilter, indepPolyOn_empty]
  ring

/-- If every nonnegative weighting has a split independence polynomial, then
the graph is claw-free. -/
theorem clawFree_of_weightedIndepPoly_splits
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (hall : ∀ wt : V → ℝ, (∀ v, 0 ≤ wt v) →
      (weightedIndepPoly G wt).Splits) :
    ClawFree G := by
  intro v s hneigh hind
  let T := insert v s
  let wt : V → ℝ := fun w => if w ∈ T then 1 else 0
  have hwt : ∀ w, 0 ≤ wt w := by
    intro w
    simp only [wt]
    split <;> norm_num
  have hsplits := hall wt hwt
  rw [show wt = fun w => if w ∈ T then 1 else 0 by rfl,
    weightedIndepPoly_eq_indepPolyOn_indicator G T,
    show T = insert v s by rfl,
    indepPolyOn_claw_obstruction G hneigh hind] at hsplits
  apply (not_splits_of_cubicDiscr_neg_of_natDegree_le_three
    (p := 1 + 4 * X + 3 * X ^ 2 + X ^ 3)
    (by compute_degree) ?_) hsplits
  norm_num [cubicDiscr, coeff_add, coeff_mul, Finset.antidiagonal,
    coeff_X, coeff_C, coeff_one]

/-- Same-phase stability of the multivariate independence polynomial forces
claw-freeness. -/
theorem clawFree_of_multivariateIndepPoly_samePhaseStable
    {V : Type u} [Fintype V] (G : _root_.SimpleGraph V)
    (h : SamePhaseStable (multivariateIndepPoly G)) : ClawFree G := by
  classical
  apply clawFree_of_weightedIndepPoly_splits G
  intro wt hwt
  rw [← commonPhaseRestriction_multivariateIndepPoly G wt]
  exact h wt hwt

/-- Leake--Ryder: the multivariate independence polynomial is same-phase
stable exactly for claw-free graphs. -/
theorem multivariateIndepPoly_samePhaseStable_iff_clawFree
    {V : Type u} [Fintype V] (G : _root_.SimpleGraph V) :
    SamePhaseStable (multivariateIndepPoly G) ↔ ClawFree G := by
  constructor
  · exact clawFree_of_multivariateIndepPoly_samePhaseStable G
  · exact ClawFree.multivariateIndepPoly_samePhaseStable

end Graph
end RealRooted
