import RealRooted.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Multiset.Sort
import RealRooted.Derivative.Algebra
import RealRooted.Derivative.Interlacing

open Polynomial Set

noncomputable section

namespace RealRooted

/-- Splitting is preserved by differentiation in the zero-aware convention. -/
theorem eq_zero_or_splits_derivative {p : ℝ[X]}
    (hp : p = 0 ∨ p.Splits) :
    p.derivative = 0 ∨ p.derivative.Splits := by
  rcases hp with rfl | hp
  · simp
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hdeg0 : p.natDegree = 0
  · exact Or.inl (derivative_eq_zero_of_natDegree_eq_zero hdeg0)
  by_cases hdeg1 : p.natDegree = 1
  · exact Or.inr (splits_of_natDegree_eq_zero (by rw [p.natDegree_derivative, hdeg1]))
  · have hdeg2 : 2 ≤ p.natDegree := by lia
    exact Or.inr (derivative_interlaces hp hdeg2).2.1.2

/-- Strict real-rootedness is preserved by differentiation unless the
derivative vanishes. -/
theorem derivative_eq_zero_or_ne_zero_and_splits {p : ℝ[X]}
    (hp_splits : p.Splits) :
    p.derivative = 0 ∨ (p.derivative ≠ 0 ∧ p.derivative.Splits) := by
  by_cases hdeg0 : p.natDegree = 0
  · left
    exact derivative_eq_zero_of_natDegree_eq_zero hdeg0
  by_cases hdeg1 : p.natDegree = 1
  · right
    have hder_ne : p.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr hdeg0
    have hder_splits : p.derivative.Splits :=
      splits_of_natDegree_eq_zero (by rw [p.natDegree_derivative, hdeg1])
    exact ⟨hder_ne, hder_splits⟩
  · have hdeg2 : 2 ≤ p.natDegree := by lia
    exact Or.inr (derivative_interlaces hp_splits hdeg2).2.1

/-- A closed segment of real-rooted polynomials has a zero-aware real-rooted
derivative segment. -/
theorem closedSegment_derivative_eq_zero_or_ne_zero_and_splits
    {f g : ℝ[X]}
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧
        (C (1 - β) * f + C β * g).Splits))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (C (1 - β) * f.derivative + C β * g.derivative = 0) ∨
      ((C (1 - β) * f.derivative + C β * g.derivative) ≠ 0 ∧
        (C (1 - β) * f.derivative + C β * g.derivative).Splits) := by
  simpa using
    (derivative_eq_zero_or_ne_zero_and_splits
      (p := C (1 - β) * f + C β * g) (hseg hβ0 hβ1).2)

/-- Nonzero members of the derivative segment of a closed real-rooted segment
are real-rooted. -/
theorem closedSegment_derivative_splits_of_ne
    {f g : ℝ[X]}
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧
        (C (1 - β) * f + C β * g).Splits))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hder_ne : C (1 - β) * f.derivative + C β * g.derivative ≠ 0) :
    (C (1 - β) * f.derivative + C β * g.derivative).Splits := by
  rcases closedSegment_derivative_eq_zero_or_ne_zero_and_splits
      hseg hβ0 hβ1 with hzero | hsplit
  · exact False.elim (hder_ne hzero)
  · exact hsplit.2

/-- Nonzero-and-splits wrapper for a derivative of a closed real-rooted
segment.  This packages `closedSegment_derivative_splits_of_ne` in the
`≠ 0 ∧ Splits` shape used by positive-combination arguments. -/
theorem closedSegment_derivative_ne_zero_and_splits_of_ne
    {f g : ℝ[X]}
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧
        (C (1 - β) * f + C β * g).Splits))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hder_ne : C (1 - β) * f.derivative + C β * g.derivative ≠ 0) :
    C (1 - β) * f.derivative + C β * g.derivative ≠ 0 ∧
      (C (1 - β) * f.derivative + C β * g.derivative).Splits :=
  ⟨hder_ne, closedSegment_derivative_splits_of_ne hseg hβ0 hβ1 hder_ne⟩

/-- Right positive family, zero-aware: for each `μ > 0`, the derivative member
`f' + C μ * g'` is either zero or real-rooted. -/
theorem posFamily_derivative_eq_zero_or_ne_zero_and_splits
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    {μ : ℝ} (hμ : 0 < μ) :
    (f.derivative + C μ * g.derivative = 0) ∨
      ((f.derivative + C μ * g.derivative) ≠ 0 ∧
        (f.derivative + C μ * g.derivative).Splits) := by
  simpa using
    (derivative_eq_zero_or_ne_zero_and_splits
      (p := f + C μ * g) (hfam hμ).2)

/-- Explicit-binder variant of `posFamily_derivative_eq_zero_or_ne_zero_and_splits`. -/
theorem posFamily_derivative_eq_zero_or_ne_zero_and_splits_explicit
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits)) :
    ∀ μ : ℝ, 0 < μ →
      (f.derivative + C μ * g.derivative = 0) ∨
        ((f.derivative + C μ * g.derivative) ≠ 0 ∧
          (f.derivative + C μ * g.derivative).Splits) :=
  fun _ hμ => posFamily_derivative_eq_zero_or_ne_zero_and_splits hfam hμ

/-- Zero-or-splits projection for a derivative member of a positive right
family. -/
theorem posFamily_derivative_eq_zero_or_splits
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    {μ : ℝ} (hμ : 0 < μ) :
    (f.derivative + C μ * g.derivative = 0) ∨
      (f.derivative + C μ * g.derivative).Splits := by
  rcases posFamily_derivative_eq_zero_or_ne_zero_and_splits hfam hμ with hzero | hsplit
  · exact Or.inl hzero
  · exact Or.inr hsplit.2

/-- Explicit-binder zero-or-splits projection for derivative members of a
positive right family. -/
theorem posFamily_derivative_eq_zero_or_splits_explicit
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits)) :
    ∀ μ : ℝ, 0 < μ →
      (f.derivative + C μ * g.derivative = 0) ∨
        (f.derivative + C μ * g.derivative).Splits :=
  fun _ hμ => posFamily_derivative_eq_zero_or_splits hfam hμ

/-- Nonzero members of the derivative of a real-rooted right family
`f + C μ * g`, for `μ > 0`, are real-rooted. -/
theorem posFamily_derivative_splits_of_ne
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    {μ : ℝ} (hμ : 0 < μ)
    (hder_ne : f.derivative + C μ * g.derivative ≠ 0) :
    (f.derivative + C μ * g.derivative).Splits := by
  rcases posFamily_derivative_eq_zero_or_ne_zero_and_splits hfam hμ with
    hzero | hsplit
  · exact absurd hzero hder_ne
  · exact hsplit.2

/-- Nonzero-and-splits packaging for a derivative member of a positive right
family. -/
theorem posFamily_derivative_ne_zero_and_splits
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    {μ : ℝ} (hμ : 0 < μ)
    (hder_ne : f.derivative + C μ * g.derivative ≠ 0) :
    f.derivative + C μ * g.derivative ≠ 0 ∧
      (f.derivative + C μ * g.derivative).Splits :=
  ⟨hder_ne, posFamily_derivative_splits_of_ne hfam hμ hder_ne⟩

/-- If every derivative member of a positive right family is nonzero, then the
derivative family has the same `≠ 0 ∧ Splits` positive-family shape. -/
theorem posFamily_derivative_family_of_ne
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hder_ne : ∀ {μ : ℝ}, 0 < μ → f.derivative + C μ * g.derivative ≠ 0) :
    ∀ {μ : ℝ}, 0 < μ →
      (f.derivative + C μ * g.derivative ≠ 0 ∧
        (f.derivative + C μ * g.derivative).Splits) :=
  fun hμ => posFamily_derivative_ne_zero_and_splits hfam hμ (hder_ne hμ)

/-- Explicit-binder variant of `posFamily_derivative_family_of_ne`. -/
theorem posFamily_derivative_family_explicit_of_ne
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hder_ne : ∀ μ : ℝ, 0 < μ → f.derivative + C μ * g.derivative ≠ 0) :
    ∀ μ : ℝ, 0 < μ →
      (f.derivative + C μ * g.derivative ≠ 0 ∧
        (f.derivative + C μ * g.derivative).Splits) :=
  fun μ hμ => posFamily_derivative_ne_zero_and_splits hfam hμ (hder_ne μ hμ)

/-- Splitting projection from the implicit derivative-family wrapper. -/
theorem posFamily_derivative_family_splits_of_ne
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hder_ne : ∀ {μ : ℝ}, 0 < μ → f.derivative + C μ * g.derivative ≠ 0) :
    ∀ {μ : ℝ}, 0 < μ → (f.derivative + C μ * g.derivative).Splits :=
  fun hμ => (posFamily_derivative_family_of_ne hfam hder_ne hμ).2

/-- Nonzero projection from the implicit derivative-family wrapper. -/
theorem posFamily_derivative_family_ne_zero_of_ne
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hder_ne : ∀ {μ : ℝ}, 0 < μ → f.derivative + C μ * g.derivative ≠ 0) :
    ∀ {μ : ℝ}, 0 < μ → f.derivative + C μ * g.derivative ≠ 0 :=
  fun hμ => (posFamily_derivative_family_of_ne hfam hder_ne hμ).1

/-- Splitting projection from the explicit derivative-family wrapper. -/
theorem posFamily_derivative_splits_explicit_of_ne
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hder_ne : ∀ μ : ℝ, 0 < μ → f.derivative + C μ * g.derivative ≠ 0) :
    ∀ μ : ℝ, 0 < μ → (f.derivative + C μ * g.derivative).Splits :=
  fun μ hμ => (posFamily_derivative_family_explicit_of_ne hfam hder_ne μ hμ).2

/-- Nonzero projection from the explicit derivative-family wrapper. -/
theorem posFamily_derivative_ne_zero_explicit_of_ne
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hder_ne : ∀ μ : ℝ, 0 < μ → f.derivative + C μ * g.derivative ≠ 0) :
    ∀ μ : ℝ, 0 < μ → f.derivative + C μ * g.derivative ≠ 0 :=
  fun μ hμ => (posFamily_derivative_family_explicit_of_ne hfam hder_ne μ hμ).1

/-- If all roots of a real-rooted polynomial are nonpositive, then all roots of
its derivative are nonpositive. -/
theorem roots_nonpos_derivative_of_roots_nonpos {p : ℝ[X]}
    (hp_splits : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    ∀ r ∈ p.derivative.roots, r ≤ 0 := by
  by_cases hdeg0 : p.natDegree = 0
  · simp [derivative_eq_zero_of_natDegree_eq_zero hdeg0]
  by_cases hdeg1 : p.natDegree = 1
  · have hderdeg : p.derivative.natDegree = 0 := by rw [p.natDegree_derivative, hdeg1]
    have hderC : p.derivative = C (p.derivative.coeff 0) :=
      eq_C_of_natDegree_eq_zero hderdeg
    rw [hderC]
    simp
  · have hdeg2 : 2 ≤ p.natDegree := by lia
    exact roots_le_of_prec_right (derivative_interlaces hp_splits hdeg2).toPrec hroots

/-- Standard Rolle--Obreschkoff input: differentiation preserves weak proper
position in the oriented, zero-aware `Prec0` convention. -/
def derivativePreservesPrec0Statement : Prop :=
  ∀ {p q : ℝ[X]}, Prec0 p q → Prec0 p.derivative q.derivative

end RealRooted
