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

/-- Pencil-local version of all-combinations transport through a linear map.

The hypothesis only asks for real-rootedness preservation on the specific
pencil spanned by `f` and `g`, which is the form needed by normalized
operator-factorization backends. -/
theorem allComboRealRooted_map_of_pencil
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hT : ∀ α β : ℝ,
      (C α * f + C β * g ≠ 0 ∧ (C α * f + C β * g).Splits) →
        T (C α * f + C β * g) = 0 ∨
          (T (C α * f + C β * g)).Splits) :
    AllComboRealRooted (T f) (T g) := by
  intro α β
  have hmap : C α * T f + C β * T g = T (C α * f + C β * g) := by
    simp only [← Polynomial.smul_eq_C_mul]
    rw [T.map_add, T.map_smul, T.map_smul]
  by_cases hzero : C α * f + C β * g = 0
  · simp [hmap, hzero]
  · rcases hT α β ⟨hzero, hall α β⟩ with hTzero | hrr
    · simp [hmap, hTzero]
    · simpa [hmap] using hrr

/-- Any linear operator that preserves real-rootedness (up to the natural zero
escape) preserves the full Obreschkoff plane of a pair. -/
theorem preservesAllComboPairs_of_preservesRealRootedOrZero
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hT : PreservesRealRootedOrZero T) :
    PreservesAllComboPairs T := fun ⦃f g⦄ hall =>
  allComboRealRooted_map_of_pencil hall fun α β hrr =>
    hT (C α * f + C β * g) hrr

/-- Order-insensitive Obreschkoff consequence, with zero polynomials absorbed
by `Prec0`. -/
theorem prec0_or_revPrec0_of_allComboRealRooted {f g : ℝ[X]}
    (hall : AllComboRealRooted f g) :
    Prec0 f g ∨ Prec0 g f := by
  by_cases hf0 : f = 0
  · exact Or.inl (hf0 ▸ prec0_zero_left g)
  by_cases hg0 : g = 0
  · exact Or.inl (hg0 ▸ prec0_zero_right f)
  have hf : f ≠ 0 ∧ f.Splits := hall.isRealRooted_left hf0
  have hg : g ≠ 0 ∧ g.Splits := hall.isRealRooted_right hg0
  rcases natDegree_eq_or_succ_or_revSucc_of_allComboRealRooted hall hf0 hg0 with
    hsame | hsucc | hrevsucc
  · exact (prec_of_allComboRealRooted hf.1 hf.2 hg.1 hg.2 hall
      (Or.inr hsame)).imp (·.toPrec0) (·.toPrec0)
  · exact (prec_of_allComboRealRooted hf.1 hf.2 hg.1 hg.2 hall
      (Or.inl hsucc)).imp (·.toPrec0) (·.toPrec0)
  · exact ((prec_of_allComboRealRooted hg.1 hg.2 hf.1 hf.2
      (allComboRealRooted_comm hall) (Or.inl hrevsucc)).imp
        (·.toPrec0) (·.toPrec0)).symm

/-- Pencil-local version of the operator-preserver consequence.  If a linear
map preserves real-rootedness on the pencil spanned by an all-combinations
real-rooted pair, then the images interlace up to the orientation ambiguity
encoded by `Prec0`. -/
theorem prec0_or_revPrec0_map_of_pencil
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hT : ∀ α β : ℝ,
      (C α * f + C β * g ≠ 0 ∧ (C α * f + C β * g).Splits) →
        T (C α * f + C β * g) = 0 ∨
          (T (C α * f + C β * g)).Splits) :
    Prec0 (T f) (T g) ∨ Prec0 (T g) (T f) :=
  prec0_or_revPrec0_of_allComboRealRooted
    (allComboRealRooted_map_of_pencil hall hT)

/-- Real-rootedness-preserving linear operators preserve interlacing up to the
order ambiguity built into the current oriented `Prec` predicate. Zero images
are absorbed by `Prec0`. -/
theorem preservesInterlacingPairsUpToOrder0_of_preservesRealRootedOrZero
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hT : PreservesRealRootedOrZero T) :
    PreservesInterlacingPairsUpToOrder0 T := fun ⦃f g⦄ hfg =>
  prec0_or_revPrec0_map_of_pencil (allComboRealRooted_of_prec hfg) fun α β hrr =>
    hT (C α * f + C β * g) hrr

/-- Planning stub for the operator theorem mentioned in `INTERLACING.md`.

Expected proof route: use Obreschkoff/all-combinations to show that if `T`
preserves real-rootedness on each polynomial, then it preserves real-rootedness
of every real linear combination of an interlacing pair, and hence preserves the
interlacing relation itself. -/
abbrev operatorPreservesInterlacingPairsUpToOrderStatement : Prop :=
  ∀ T : ℝ[X] →ₗ[ℝ] ℝ[X],
    PreservesRealRootedOrZero T →
    PreservesInterlacingPairsUpToOrder0 T

theorem operatorPreservesInterlacingPairsUpToOrder :
    operatorPreservesInterlacingPairsUpToOrderStatement :=
  @preservesInterlacingPairsUpToOrder0_of_preservesRealRootedOrZero

end RealRooted
