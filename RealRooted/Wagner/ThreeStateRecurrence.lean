module

public import RealRooted.Recurrence.CubicTransition
import RealRooted.OperatorMatrix.Directed

/-!
# A three-state Wagner-cone recurrence

We prove preservation of `C ≼ B`, `C ≼ F`, and `B ≼ F` under
`B⁺ = B + F`, `C⁺ = C + w (B + F)`, and `F⁺ = F + X (C + w B)`.
Here `≼` is the zero-aware weak oriented relation `Interl`, and every state is
PF: it has nonnegative coefficients and splits with nonpositive roots.
Every nonzero state consequently has positive leading coefficient. Shared and
repeated roots are allowed; no assertion of distinct roots is made.

The recurrence comes from nesting-free marked matchings with positive mark
weights (unpublished manuscript, section "Theorem: no nested arcs"). We formalize
only the recurrence and its invariant, independently of that combinatorial model.
-/

@[expose] public section

open Polynomial

namespace RealRooted
namespace Wagner

/-- A positive weighted step preserves the three-state cone and interlaces
consecutive return states, including when some input states vanish. -/
theorem isOrderedPFTriple_threeState_step {F B C : ℝ[X]} (h : IsOrderedPFTriple C B F)
    {w : ℝ} (hw : 0 < w) :
    IsOrderedPFTriple (C + Polynomial.C w * (B + F)) (B + F)
      (F + X * (C + Polynomial.C w * B)) ∧
    Interl F (F + X * (C + Polynomial.C w * B)) := by
  rcases h with ⟨hC, hB, hF, hCB, hCF, hBF⟩
  let D := B + F
  let K := C + Polynomial.C w * B
  have hD : IsPFPolynomial D := hB.add_of_interl hF hBF
  have hwB := hB.const_mul hw
  have hwF := hF.const_mul hw
  have hK : IsPFPolynomial K :=
    hC.add_of_interl hwB (hCB.C_mul_right_of_nonneg hw.le)
  have hKB : Interl K B :=
    interl_add_left_of_common_right_of_nonneg hCB
      (hB.interl_self.C_mul_left_of_nonneg hw.le)
      hC.hasNonnegCoeffs hwB.hasNonnegCoeffs
  have hKF : Interl K F :=
    interl_add_left_of_common_right_of_nonneg hCF
      (hBF.C_mul_left_of_nonneg hw.le)
      hC.hasNonnegCoeffs hwB.hasNonnegCoeffs
  have hKD : Interl K D :=
    interl_add_right_of_common_left_of_nonneg hKB hKF
      hB.hasNonnegCoeffs hF.hasNonnegCoeffs
  have hDF : Interl D F :=
    interl_add_left_of_common_right_of_nonneg hBF hF.interl_self
      hB.hasNonnegCoeffs hF.hasNonnegCoeffs
  have hCD : Interl C D :=
    interl_add_right_of_common_left_of_nonneg hCB hCF
      hB.hasNonnegCoeffs hF.hasNonnegCoeffs
  have hnextC : IsPFPolynomial (C + Polynomial.C w * D) :=
    hC.add_of_interl (hD.const_mul hw) (hCD.C_mul_right_of_nonneg hw.le)
  have hnextCD : Interl (C + Polynomial.C w * D) D :=
    interl_add_left_of_common_right_of_nonneg hCD
      (hD.interl_self.C_mul_left_of_nonneg hw.le)
      hC.hasNonnegCoeffs (hD.const_mul hw).hasNonnegCoeffs
  have hnextCF : Interl (C + Polynomial.C w * D) F :=
    interl_add_left_of_common_right_of_nonneg hCF
      (hDF.C_mul_left_of_nonneg hw.le)
      hC.hasNonnegCoeffs (hD.const_mul hw).hasNonnegCoeffs
  have hform : C + Polynomial.C w * D = K + Polynomial.C w * F := by
    dsimp [D, K]
    ring
  have hKnextC : Interl K (C + Polynomial.C w * D) := by
    rw [hform]
    exact interl_add_right_of_common_left_of_nonneg hK.interl_self
      (hKF.C_mul_right_of_nonneg hw.le) hK.hasNonnegCoeffs hwF.hasNonnegCoeffs
  have hDXK : Interl D (X * K) :=
    interl_mul_X_of_interl hKD hK.hasNonnegCoeffs hD.hasNonnegCoeffs
  have hnextCXK : Interl (C + Polynomial.C w * D) (X * K) :=
    interl_mul_X_of_interl hKnextC hK.hasNonnegCoeffs hnextC.hasNonnegCoeffs
  have hFXK : Interl F (X * K) :=
    interl_mul_X_of_interl hKF hK.hasNonnegCoeffs hF.hasNonnegCoeffs
  have hnextF := hF.add_of_interl hK.X_mul hFXK
  refine ⟨⟨hnextC, hD, hnextF, hnextCD, ?_, ?_⟩, ?_⟩
  · exact interl_add_right_of_common_left_of_nonneg hnextCF hnextCXK
      hF.hasNonnegCoeffs hK.X_mul.hasNonnegCoeffs
  · exact interl_add_right_of_common_left_of_nonneg hDF hDXK
      hF.hasNonnegCoeffs hK.X_mul.hasNonnegCoeffs
  · exact interl_add_right_of_common_left_of_nonneg hF.interl_self hFXK
      hF.hasNonnegCoeffs hK.X_mul.hasNonnegCoeffs

/-- A three-state recurrence with rank-zero data `(1, 0, 0)`.
The arbitrary weights are required to be positive by the theorems below. -/
structure ThreeStateRecurrence (w : ℕ → ℝ) (F B C : ℕ → ℝ[X]) : Prop where
  /-- The initial return state. -/
  F_zero : F 0 = 1
  /-- The initial unmarked state. -/
  B_zero : B 0 = 0
  /-- The initial marked state. -/
  C_zero : C 0 = 0
  /-- The return-state update. -/
  F_succ : ∀ n, F (n + 1) = F n + X * (C n + Polynomial.C (w n) * B n)
  /-- The unmarked-state update. -/
  B_succ : ∀ n, B (n + 1) = B n + F n
  /-- The marked-state update. -/
  C_succ : ∀ n, C (n + 1) = C n + Polynomial.C (w n) * (B n + F n)

/-- A recurrence with positive weights preserves the cone from any initial rank. -/
theorem isOrderedPFTriple_of_threeState_recurrence {w : ℕ → ℝ} {F B C : ℕ → ℝ[X]}
    (hw : ∀ n, 0 < w n) (h₀ : IsOrderedPFTriple (C 0) (B 0) (F 0))
    (hF : ∀ n, F (n + 1) = F n + X * (C n + Polynomial.C (w n) * B n))
    (hB : ∀ n, B (n + 1) = B n + F n)
    (hC : ∀ n, C (n + 1) = C n + Polynomial.C (w n) * (B n + F n))
    (n : ℕ) : IsOrderedPFTriple (C n) (B n) (F n) := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
    rw [hF n, hB n, hC n]
    exact (isOrderedPFTriple_threeState_step ih (hw n)).1

/-- Every rank of the recurrence satisfies the zero-aware interlacing invariant. -/
theorem ThreeStateRecurrence.isOrderedPFTriple {w : ℕ → ℝ} {F B C : ℕ → ℝ[X]}
    (h : ThreeStateRecurrence w F B C) (hw : ∀ n, 0 < w n) (n : ℕ) :
    IsOrderedPFTriple (C n) (B n) (F n) := by
  apply isOrderedPFTriple_of_threeState_recurrence hw ?_ h.F_succ h.B_succ h.C_succ n
  rw [h.F_zero, h.B_zero, h.C_zero]
  exact ⟨IsPFPolynomial.zero, IsPFPolynomial.zero, IsPFPolynomial.one,
    interl_zero_left 0, interl_zero_left 1, interl_zero_left 1⟩

/-- Consecutive return states weakly interlace in the zero-aware convention. -/
theorem ThreeStateRecurrence.interl_succ {w : ℕ → ℝ} {F B C : ℕ → ℝ[X]}
    (h : ThreeStateRecurrence w F B C) (hw : ∀ n, 0 < w n) (n : ℕ) :
    Interl (F n) (F (n + 1)) := by
  rw [h.F_succ n]
  exact (isOrderedPFTriple_threeState_step (h.isOrderedPFTriple hw n) (hw n)).2

/-- Every return state retains constant coefficient one. -/
theorem ThreeStateRecurrence.coeff_zero {w : ℕ → ℝ} {F B C : ℕ → ℝ[X]}
    (h : ThreeStateRecurrence w F B C) (n : ℕ) : (F n).coeff 0 = 1 := by
  induction n with
  | zero => simp [h.F_zero]
  | succ n ih => simp [h.F_succ n, ih]

/-- Return states are nonzero, so their interlacing is also expressed by `StrictInterl`.
Despite its name, this predicate allows shared and repeated roots. -/
theorem ThreeStateRecurrence.strictInterl_succ {w : ℕ → ℝ} {F B C : ℕ → ℝ[X]}
    (h : ThreeStateRecurrence w F B C) (hw : ∀ n, 0 < w n) (n : ℕ) :
    StrictInterl (F n) (F (n + 1)) := by
  have hne (k : ℕ) : F k ≠ 0 := by
    intro hk
    have := h.coeff_zero k
    simp [hk] at this
  exact (h.interl_succ hw n).toStrictInterl_of_ne (hne n) (hne (n + 1))

/-- Every return state splits with nonpositive roots and positive leading coefficient. -/
theorem ThreeStateRecurrence.splits_roots_nonpos_posLeadingCoeff
    {w : ℕ → ℝ} {F B C : ℕ → ℝ[X]}
    (h : ThreeStateRecurrence w F B C) (hw : ∀ n, 0 < w n) (n : ℕ) :
    (F n).Splits ∧ (∀ r ∈ (F n).roots, r ≤ 0) ∧ HasPosLeadingCoeff (F n) := by
  have hp := (h.isOrderedPFTriple hw n).2.2.1
  refine ⟨hp.splits, hp.roots_nonpos, hp.hasNonnegCoeffs.pos_leadingCoeff ?_⟩
  intro hn
  have := h.coeff_zero n
  simp [hn] at this

end Wagner
end RealRooted
