module

public import RealRooted.RootLocation.Basic
public import RealRooted.BorceaBranden.UnivariateFiniteSymbol
public import RealRooted.OperatorPreservesInterlacing

/-!
# Bridges between the preservation predicates

`MapsRealRootedIn T n univ univ` says that `T` sends every real-rooted polynomial of degree at most
`n` to `0` or to a real-rooted polynomial.  This is the degree-bounded predicate
`BorceaBranden.PreservesRealRootedUpTo n T`, and `PreservesRealRootedOrZero T` is the same
statement in all degrees.
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- `MapsRealRootedIn T d univ univ` is `BorceaBranden.PreservesRealRootedUpTo d T`. -/
theorem mapsRealRootedIn_univ_iff_preservesRealRootedUpTo (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (d : ℕ) :
    MapsRealRootedIn T d univ univ ↔ BorceaBranden.PreservesRealRootedUpTo d T := by
  refine ⟨fun h p hp hs => ?_, fun h p hp hr => ?_⟩
  · rcases eq_or_ne p 0 with rfl | hp0
    · exact Or.inl (map_zero T)
    · exact (h p hp (IsRealRootedIn.univ_iff.2 ⟨hp0, hs⟩)).imp_right (·.splits)
  · rcases eq_or_ne (T p) 0 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (IsRealRootedIn.univ_iff.2 ⟨h0, (h hp hr.splits).resolve_left h0⟩)

/-- `PreservesRealRootedOrZero T` says that `T` maps real-rooted polynomials of every degree to
`0` or to real-rooted polynomials. -/
theorem preservesRealRootedOrZero_iff_forall_mapsRealRootedIn_univ (T : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    PreservesRealRootedOrZero T ↔ ∀ n, MapsRealRootedIn T n univ univ := by
  refine ⟨fun h n p _ hr => ?_, fun h p hp => ?_⟩
  · rcases eq_or_ne (T p) 0 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (IsRealRootedIn.univ_iff.2 ⟨h0, (h p ⟨hr.ne_zero, hr.splits⟩).resolve_left h0⟩)
  · exact (mapsRealRootedIn_univ_iff_preservesRealRootedUpTo T p.natDegree).1 (h _)
      le_rfl hp.2

end RealRooted
