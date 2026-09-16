import RealRooted.MultivariateStability

/-!
# All-real-combination multivariate stability

This module packages the zero-aware linear-span condition used by induction
arguments for multivariate real stability.
-/

namespace RealRooted

noncomputable section

/-- Every real linear combination of `F` and `G` is real stable or zero. -/
def AllComboMvRealStableOrZero {σ : Type*}
    (F G : MvPolynomial σ ℝ) : Prop :=
  ∀ α β : ℝ,
    MvRealStableOrZero
      (MvPolynomial.C α * F + MvPolynomial.C β * G)

namespace AllComboMvRealStableOrZero

/-- The left endpoint of a weakly real-stable linear span is weakly stable. -/
theorem left {σ : Type*} {F G : MvPolynomial σ ℝ}
    (hall : AllComboMvRealStableOrZero F G) :
    MvRealStableOrZero F := by
  simpa using hall 1 0

/-- The right endpoint of a weakly real-stable linear span is weakly stable. -/
theorem right {σ : Type*} {F G : MvPolynomial σ ℝ}
    (hall : AllComboMvRealStableOrZero F G) :
    MvRealStableOrZero G := by
  simpa using hall 0 1

/-- The all-combinations condition is symmetric in its two generators. -/
theorem comm {σ : Type*} {F G : MvPolynomial σ ℝ}
    (hall : AllComboMvRealStableOrZero F G) :
    AllComboMvRealStableOrZero G F := by
  intro α β
  simpa [add_comm] using hall β α

/-- Renaming variables preserves an all-combinations stability certificate. -/
theorem rename {σ τ : Type*} {F G : MvPolynomial σ ℝ}
    (hall : AllComboMvRealStableOrZero F G) (f : σ → τ) :
    AllComboMvRealStableOrZero
      (MvPolynomial.rename f F) (MvPolynomial.rename f G) := by
  intro α β
  simpa only [map_add, map_mul, MvPolynomial.rename_C] using
    (hall α β).rename f

/-- An all-combinations stability certificate is reflected through an
injective variable renaming. -/
theorem of_rename {σ τ : Type*} {F G : MvPolynomial σ ℝ}
    {f : σ → τ}
    (hall : AllComboMvRealStableOrZero
      (MvPolynomial.rename f F) (MvPolynomial.rename f G))
    (hf : Function.Injective f) :
    AllComboMvRealStableOrZero F G := by
  intro α β
  have h := hall α β
  have hrename : MvRealStableOrZero
      (MvPolynomial.rename f
        (MvPolynomial.C α * F + MvPolynomial.C β * G)) := by
    simpa only [map_add, map_mul, MvPolynomial.rename_C] using h
  exact hrename.of_rename hf

/-- Every linear recombination of a weakly stable span remains in that span. -/
theorem linearRecombination
    {σ : Type*} {F G P Q : MvPolynomial σ ℝ} {a b c d : ℝ}
    (hall : AllComboMvRealStableOrZero F G)
    (hP : P = MvPolynomial.C a * F + MvPolynomial.C b * G)
    (hQ : Q = MvPolynomial.C c * F + MvPolynomial.C d * G) :
    AllComboMvRealStableOrZero P Q := by
  intro α β
  rw [hP, hQ]
  convert hall (α * a + β * c) (α * b + β * d) using 1
  grind

end AllComboMvRealStableOrZero

/-- It suffices to check the affine family `F + tG`, together with its limiting
direction `G`, to obtain every real linear combination. -/
theorem allComboMvRealStableOrZero_of_affine
    {σ : Type*} {F G : MvPolynomial σ ℝ}
    (hG : MvRealStableOrZero G)
    (haffine : ∀ t : ℝ,
      MvRealStableOrZero (F + MvPolynomial.C t * G)) :
    AllComboMvRealStableOrZero F G := by
  intro α β
  by_cases hα : α = 0
  · subst α
    simpa using hG.C_mul β
  · have hscaled := (haffine (β / α)).C_mul α
    have hcoeff : α * (β / α) = β := by field_simp
    rw [mul_add, ← mul_assoc, ← MvPolynomial.C_mul, hcoeff] at hscaled
    exact hscaled

end

end RealRooted
