import RealRooted.ObreschkoffConverse

open Polynomial

noncomputable section

namespace RealRooted

/-- A linear operator preserves real-rootedness up to the natural zero escape
that can occur for non-injective operators. -/
def PreservesRealRootedOrZero (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ p : ℝ[X], (p ≠ 0 ∧ p.Splits) → T p = 0 ∨ (T p).Splits

/-- Strong oriented target notion for interlacing preservation by a linear
operator. This is intentionally stronger than the theorem proved below: with the
current oriented `Prec`, operators such as `p(x) ↦ p(-x)` preserve
real-rootedness but reverse same-degree order. -/
def PreservesInterlacingPairs0 (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ ⦃f g : ℝ[X]⦄, Prec f g → Prec0 (T f) (T g)

/-- Order-insensitive version of interlacing preservation. This is the honest
Obreschkoff-level consequence of preserving real-rootedness for all linear
combinations. -/
def PreservesInterlacingPairsUpToOrder0 (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ ⦃f g : ℝ[X]⦄, Prec f g → Prec0 (T f) (T g) ∨ Prec0 (T g) (T f)

/-- A linear operator preserves the full all-combinations real-rootedness plane
attached to a pair. -/
def PreservesAllComboPairs (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ ⦃f g : ℝ[X]⦄, AllComboRealRooted f g → AllComboRealRooted (T f) (T g)

/-- Any linear operator that preserves real-rootedness (up to the natural zero
escape) preserves the full Obreschkoff plane of a pair. -/
theorem preservesAllComboPairs_of_preservesRealRootedOrZero
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hT : PreservesRealRootedOrZero T) :
    PreservesAllComboPairs T := by
  intro f g hall α β
  have hmap : C α * T f + C β * T g = T (C α * f + C β * g) := by
    calc
      C α * T f + C β * T g
          = α • T f + β • T g := by simp [Polynomial.smul_eq_C_mul]
      _ = T (α • f) + T (β • g) := by
            simp
      _ = T (α • f + β • g) := by
            simp
      _ = T (C α * f + C β * g) := by
            simp [Polynomial.smul_eq_C_mul]
  by_cases hzero : C α * f + C β * g = 0
  · rw [hmap, hzero]
    simp
  · rcases hT (C α * f + C β * g) ⟨hzero, hall α β⟩ with hTzero | hrr
    · rw [hmap, hTzero]
      simp
    · simpa [hmap] using hrr

/-- Real-rootedness-preserving linear operators preserve interlacing up to the
order ambiguity built into the current oriented `Prec` predicate. Zero images
are absorbed by `Prec0`. -/
theorem preservesInterlacingPairsUpToOrder0_of_preservesRealRootedOrZero
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hT : PreservesRealRootedOrZero T) :
    PreservesInterlacingPairsUpToOrder0 T := by
  intro f g hfg
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
  · rcases prec_of_allComboRealRooted hfT.1 hfT.2 hgT.1 hgT.2 hallT
      (Or.inr hsame) with hprec | hprec
    · exact Or.inl hprec.toPrec0
    · exact Or.inr hprec.toPrec0
  · rcases prec_of_allComboRealRooted hfT.1 hfT.2 hgT.1 hgT.2 hallT
      (Or.inl hsucc) with hprec | hprec
    · exact Or.inl hprec.toPrec0
    · exact Or.inr hprec.toPrec0
  · have hallT' : AllComboRealRooted (T g) (T f) := allComboRealRooted_comm hallT
    rcases prec_of_allComboRealRooted hgT.1 hgT.2 hfT.1 hfT.2 hallT'
      (Or.inl hrevsucc) with hprec | hprec
    · exact Or.inr hprec.toPrec0
    · exact Or.inl hprec.toPrec0

/-- Planning stub for the operator theorem mentioned in `INTERLACING.md`.

Expected proof route: use Obreschkoff/all-combinations to show that if `T`
preserves real-rootedness on each polynomial, then it preserves real-rootedness
of every real linear combination of an interlacing pair, and hence preserves the
interlacing relation itself. -/
def operatorPreservesInterlacingPairsUpToOrderStatement : Prop :=
  ∀ T : ℝ[X] →ₗ[ℝ] ℝ[X],
    PreservesRealRootedOrZero T →
    PreservesInterlacingPairsUpToOrder0 T

theorem operatorPreservesInterlacingPairsUpToOrder :
    operatorPreservesInterlacingPairsUpToOrderStatement := by
  intro T hT
  exact preservesInterlacingPairsUpToOrder0_of_preservesRealRootedOrZero hT

end RealRooted
