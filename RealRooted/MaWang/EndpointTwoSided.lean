module

public import RealRooted.MaWang.EndpointMultiplicity
import RealRooted.BasisTransform.DifferentialOperatorMaps

/-!
# Closed endpoint derivative steps

We prove the two-endpoint criterion for
`(a X + c) f + X (X + 1) f'`, including roots and multiplicities at both
closed endpoints.  This is the instance `L = -1`, `U = 0` of the closed-window step for
interval differential operators, `intervalDifferentialStep_closed` and its companions in
`RealRooted.BasisTransform.DifferentialOperatorMaps`.
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- The Ma--Wang endpoint step is the interval step for the window `[-1, 0]`. -/
private lemma endpointStep_one_eq_intervalDifferentialStep (a c : ℝ) (p : ℝ[X]) :
    MaWang.endpointStep 1 a c p = intervalDifferentialStep a c 1 1 (-1) 0 0 p := by
  simp only [MaWang.endpointStep, intervalDifferentialStep, map_one, map_neg, map_zero, one_mul,
    sub_zero, sub_neg_eq_add, mul_one]
  ring

/-- A positive affine coefficient gives a successor-degree interlacing step
even when the input has roots at either endpoint of `[-1, 0]`. -/
theorem affineEndpointStep_strictInterl {a c : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) :
    (MaWang.endpointStep 1 a c p).natDegree = p.natDegree + 1 ∧
      HasPosLeadingCoeff (MaWang.endpointStep 1 a c p) ∧
      StrictInterl p (MaWang.endpointStep 1 a c p) := by
  rw [endpointStep_one_eq_intervalDifferentialStep]
  exact intervalDifferentialStep_strictInterl one_pos one_pos (by positivity) hp hs hroots

/-- At zero, the endpoint step preserves multiplicity unless the affine
threshold vanishes, in which case the multiplicity increases by one. -/
theorem affineEndpointStep_rootMultiplicity_zero {a c : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) :
    (MaWang.endpointStep 1 a c p).rootMultiplicity 0 =
      if c + p.rootMultiplicity 0 = 0 then p.rootMultiplicity 0 + 1
      else p.rootMultiplicity 0 := by
  rw [endpointStep_one_eq_intervalDifferentialStep,
    (intervalDifferentialStep_rootMultiplicity (alpha := a) (beta := c) (xi := 0) one_pos one_pos
      (by positivity) hp hs hroots).2]
  exact if_congr (by constructor <;> intro h <;> linarith) rfl rfl

/-- At `-1`, the endpoint step preserves multiplicity unless the affine
threshold is an equality, in which case the multiplicity increases by one. -/
theorem affineEndpointStep_rootMultiplicity_neg_one {a c : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) :
    (MaWang.endpointStep 1 a c p).rootMultiplicity (-1) =
      if c = a + p.rootMultiplicity (-1) then p.rootMultiplicity (-1) + 1
      else p.rootMultiplicity (-1) := by
  rw [endpointStep_one_eq_intervalDifferentialStep,
    (intervalDifferentialStep_rootMultiplicity (alpha := a) (beta := c) (xi := 0) one_pos one_pos
      (by positivity) hp hs hroots).1]
  exact if_congr (by constructor <;> intro h <;> linarith) rfl rfl

/-- The Ma--Wang affine derivative step has all roots in `[-1, 0]` exactly
when its two endpoint thresholds are nonnegative. -/
theorem affineEndpointStep_roots_mem_Icc_iff {a c : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) :
    (∀ r ∈ (MaWang.endpointStep 1 a c p).roots, r ∈ Icc (-1 : ℝ) 0) ↔
      0 ≤ c + p.rootMultiplicity 0 ∧
        0 ≤ a + p.rootMultiplicity (-1) - c := by
  rw [endpointStep_one_eq_intervalDifferentialStep,
    (intervalDifferentialStep_closed (alpha := a) (beta := c) (xi := 0) one_pos
      one_pos (by positivity) hp hs hroots).2.2.2.2.1]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- The complete two-endpoint Ma--Wang step: degree, leading coefficient,
real-rootedness, directed weak interlacing, the closed-window criterion, and
both endpoint multiplicity updates. -/
theorem affineEndpointStep_closed {a c : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) :
    (MaWang.endpointStep 1 a c p).natDegree = p.natDegree + 1 ∧
      HasPosLeadingCoeff (MaWang.endpointStep 1 a c p) ∧
      (MaWang.endpointStep 1 a c p).Splits ∧
      Interlaces p (MaWang.endpointStep 1 a c p) ∧
      ((∀ r ∈ (MaWang.endpointStep 1 a c p).roots, r ∈ Icc (-1 : ℝ) 0) ↔
        0 ≤ c + p.rootMultiplicity 0 ∧
          0 ≤ a + p.rootMultiplicity (-1) - c) ∧
      ((MaWang.endpointStep 1 a c p).rootMultiplicity 0 =
        if c + p.rootMultiplicity 0 = 0 then p.rootMultiplicity 0 + 1
        else p.rootMultiplicity 0) ∧
      (MaWang.endpointStep 1 a c p).rootMultiplicity (-1) =
        if c = a + p.rootMultiplicity (-1) then p.rootMultiplicity (-1) + 1
        else p.rootMultiplicity (-1) := by
  have hstep := affineEndpointStep_strictInterl (c := c) ha hp hs hroots
  refine ⟨hstep.1, hstep.2.1, hstep.2.2.2.1.2,
    hstep.2.2.toInterlaces hstep.1.symm, ?_, ?_, ?_⟩
  · exact affineEndpointStep_roots_mem_Icc_iff (c := c) ha hp hs hroots
  · exact affineEndpointStep_rootMultiplicity_zero (c := c) ha hp hs hroots
  · exact affineEndpointStep_rootMultiplicity_neg_one (c := c) ha hp hs hroots

end RealRooted
