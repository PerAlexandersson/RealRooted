import RealRooted.Basic

/-!
# Pair compatibility

This module owns the Chudnovsky--Seymour compatibility predicate for one pair,
its symmetry, and the degree-bounded transport through a real-linear map. It is
independent of the finite-family, root-reflection, and affine-family machinery
in `Compatibility.Basic`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Chudnovsky--Seymour compatibility for a pair: every nonnegative linear
combination is real-rooted, allowing the zero polynomial in the degenerate
`α = β = 0` case. -/
def Compatible (f g : ℝ[X]) : Prop :=
  ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
    C α * f + C β * g = 0 ∨
      ((C α * f + C β * g) ≠ 0 ∧ (C α * f + C β * g).Splits)

namespace Compatible

lemma comm {f g : ℝ[X]} (h : Compatible f g) : Compatible g f := by
  intro α β hα hβ
  simpa [Compatible, add_comm, mul_comm, mul_left_comm, mul_assoc] using
    h β α hβ hα

/-- A linear map that preserves nonzero real-rootedness on nonnegative inputs
up to degree `d` transports compatibility inside that degree box. -/
theorem map_linearMap_of_nonneg
    {f g : ℝ[X]} {d : ℕ} (hfg : Compatible f g)
    (T : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hfdeg : f.natDegree ≤ d) (hgdeg : g.natDegree ≤ d)
    (hT : ∀ ⦃p : ℝ[X]⦄, HasNonnegCoeffs p → p.natDegree ≤ d →
      p ≠ 0 ∧ p.Splits → T p ≠ 0 ∧ (T p).Splits) :
    Compatible (T f) (T g) := by
  intro α β hα hβ
  let p := C α * f + C β * g
  have hp : HasNonnegCoeffs p := by
    dsimp [p]
    exact (nonnegCoeffs_C_mul hα hf).add (nonnegCoeffs_C_mul hβ hg)
  have hpdeg : p.natDegree ≤ d :=
    (natDegree_add_le _ _).trans <|
      max_le ((natDegree_C_mul_le α f).trans hfdeg)
        ((natDegree_C_mul_le β g).trans hgdeg)
  have hmap : C α * T f + C β * T g = T p := by
    dsimp [p]
    simp only [← smul_eq_C_mul, T.map_add, T.map_smul]
  rw [hmap]
  rcases hfg α β hα hβ with hp_zero | hp_rr
  · left
    simp [p, hp_zero]
  · exact Or.inr (hT hp hpdeg hp_rr)

end Compatible
end RealRooted
