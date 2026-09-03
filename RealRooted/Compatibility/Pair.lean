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

/-- A split polynomial is compatible with its `X`-multiple. -/
theorem self_X_mul_of_splits {p : ℝ[X]} (hp : p.Splits) :
    Compatible p (X * p) := by
  intro α β _hα _hβ
  have hlin : (C α + C β * X : ℝ[X]).Splits := by
    by_cases hβ0 : β = 0
    · simp [hβ0]
    · have hβα : β * (α / β) = α := by grind
      have : (C α + C β * X : ℝ[X]) = C β * (X + C (α / β)) := by grind
      simp_all
  have hsum : C α * p + C β * (X * p) = (C α + C β * X) * p := by ring
  have : (C α * p + C β * (X * p)).Splits := by simp_all
  grind

/-- A split polynomial is compatible with itself. -/
theorem self_of_splits {p : ℝ[X]} (hp : p.Splits) : Compatible p p := by
  intro α β _hα _hβ
  have hsum : C α * p + C β * p = C (α + β) * p := by grind
  by_cases hzero : C α * p + C β * p = 0
  · exact Or.inl hzero
  · right
    rw [hsum]
    exact ⟨hsum ▸ hzero, hp.C_mul (α + β)⟩

/-- Multiplication by `X` preserves compatibility. -/
theorem X_mul {f g : ℝ[X]} (h : Compatible f g) :
    Compatible (X * f) (X * g) := by
  intro α β hα hβ
  have hsum : C α * (X * f) + C β * (X * g) =
      X * (C α * f + C β * g) := by
    ring
  rcases h α β hα hβ with hzero | hrr <;> simp_all

/-- A nonzero sum of compatible polynomials splits. -/
theorem splits_add {p q : ℝ[X]} (h : Compatible p q)
    (hadd : p + q ≠ 0) : (p + q).Splits := by
  have hcombo := h 1 1 zero_le_one zero_le_one
  simp_all

/-- A nonnegative scalar multiple can be added to the left member of a
compatible pair without losing splitness, provided the sum is nonzero. -/
theorem splits_add_C_mul {p q : ℝ[X]} (h : Compatible p q)
    {r : ℝ} (hr : 0 ≤ r) (hadd : p + C r * q ≠ 0) :
    (p + C r * q).Splits := by
  have hcombo := h 1 r zero_le_one hr
  simp_all

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
