import RealRooted.ObreschkoffConverse

open Polynomial

noncomputable section

namespace RealRooted

/-- A linear operator preserves real-rootedness up to the natural zero escape
that can occur for non-injective operators. -/
abbrev PreservesRealRootedOrZero (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ p : ℝ[X], (p ≠ 0 ∧ p.Splits) → T p = 0 ∨ (T p).Splits

/-- Order-insensitive version of interlacing preservation. This is the honest
Obreschkoff-level consequence of preserving real-rootedness for all linear
combinations. -/
abbrev PreservesInterlacingPairsUpToOrder0 (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ ⦃f g : ℝ[X]⦄, Prec f g → Prec0 (T f) (T g) ∨ Prec0 (T g) (T f)

/-- A linear operator preserves the full all-combinations real-rootedness plane
attached to a pair. -/
abbrev PreservesAllComboPairs (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ ⦃f g : ℝ[X]⦄, AllComboRealRooted f g → AllComboRealRooted (T f) (T g)

/-- Any linear operator that preserves real-rootedness (up to the natural zero
escape) preserves the full Obreschkoff plane of a pair. -/
theorem preservesAllComboPairs_of_preservesRealRootedOrZero
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hT : PreservesRealRootedOrZero T) :
    PreservesAllComboPairs T := fun ⦃f g⦄ hall α β => by
  have hmap : C α * T f + C β * T g = T (C α * f + C β * g) := by
    simp only [← Polynomial.smul_eq_C_mul]
    rw [T.map_add, T.map_smul, T.map_smul]
  by_cases hzero : C α * f + C β * g = 0
  · simp [hmap, hzero]
  · rcases hT (C α * f + C β * g) ⟨hzero, hall α β⟩ with hTzero | hrr
    · simp [hmap, hTzero]
    · simpa [hmap] using hrr

/-- Real-rootedness-preserving linear operators preserve interlacing up to the
order ambiguity built into the current oriented `Prec` predicate. Zero images
are absorbed by `Prec0`. -/
theorem preservesInterlacingPairsUpToOrder0_of_preservesRealRootedOrZero
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hT : PreservesRealRootedOrZero T) :
    PreservesInterlacingPairsUpToOrder0 T := fun ⦃f g⦄ hfg => by
  have hallT : AllComboRealRooted (T f) (T g) :=
    preservesAllComboPairs_of_preservesRealRootedOrZero hT
      (allComboRealRooted_of_prec hfg)
  by_cases hfT0 : T f = 0
  · exact Or.inl (hfT0 ▸ prec0_zero_left (T g))
  by_cases hgT0 : T g = 0
  · exact Or.inl (hgT0 ▸ prec0_zero_right (T f))
  have hfT : ((T f) ≠ 0 ∧ (T f).Splits) :=
    ⟨hfT0, by simpa using hallT 1 0⟩
  have hgT : ((T g) ≠ 0 ∧ (T g).Splits) :=
    ⟨hgT0, by simpa using hallT 0 1⟩
  rcases natDegree_eq_or_succ_or_revSucc_of_allComboRealRooted hallT hfT0 hgT0 with
    hsame | hsucc | hrevsucc
  · exact (prec_of_allComboRealRooted hfT.1 hfT.2 hgT.1 hgT.2 hallT
      (Or.inr hsame)).imp (·.toPrec0) (·.toPrec0)
  · exact (prec_of_allComboRealRooted hfT.1 hfT.2 hgT.1 hgT.2 hallT
      (Or.inl hsucc)).imp (·.toPrec0) (·.toPrec0)
  · exact ((prec_of_allComboRealRooted hgT.1 hgT.2 hfT.1 hfT.2
      (allComboRealRooted_comm hallT) (Or.inl hrevsucc)).imp
        (·.toPrec0) (·.toPrec0)).symm

/-- Real-rootedness-preserving linear operators preserve interlacing pairs up
to order.

Proof route: use Obreschkoff/all-combinations to show that if `T` preserves
real-rootedness on each polynomial, then it preserves real-rootedness of every
real linear combination of an interlacing pair, and hence preserves the
interlacing relation itself. -/
theorem operatorPreservesInterlacingPairsUpToOrder
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (hT : PreservesRealRootedOrZero T) :
    PreservesInterlacingPairsUpToOrder0 T :=
  preservesInterlacingPairsUpToOrder0_of_preservesRealRootedOrZero hT

end RealRooted
