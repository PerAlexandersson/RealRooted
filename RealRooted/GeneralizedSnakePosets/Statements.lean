import RealRooted.Basic
import RealRooted.GeneralizedSnakePosets.SquarecaseModel
import RealRooted.Mathlib.Algebra.Polynomial.Roots

/-!
# Braun--Jal generalized snake poset predicates

This module contains the predicates on abstract polynomial families `P`, `G`
and snake-word models `M` used by the snake-interlacing induction of
Braun--Jal, *Order polytopes of generalized snake posets are
h^*-real-rooted*, arXiv:2607.00922v1, together with the generic assembly of
the shifted difference interlacing claim.  The concrete instances are proved
for `modifiedNarayanaPolynomial`, `FiniteSkewBoard.auxiliaryG`, and
`generalizedSnakeRookModel`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

universe u

/-- The snake interlacing theorem, abstracted over the polynomial model.

The source theorem concerns the concrete non-nesting rook polynomial `M_w`: it
asserts real-rootedness and that deleting the final letter gives
`M_{w'} << M_w`. This interface is only an abstract package for arbitrary `M`.
A source-facing theorem must instantiate `generalizedSnakeRookModel` and prove
the degree and model-identification bridges needed to use local `Interlaces`. -/
def NonNestingRookInterlacing (M : SnakeWord → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord}, 1 ≤ w.length →
    (M w ≠ 0 ∧ (M w).Splits) ∧
      Interlaces (M w.deleteFinal) (M w)

/-! ## Narayana and recurrence interfaces from the combinatorial inputs -/

/-- The auxiliary recurrence of Braun--Jal: `X * G_{n-1} = P_n - (1 + X) * P_{n-1}`. -/
def NarayanaAuxiliaryGRecurrence
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → X * G (n - 1) = P n - (1 + X) * P (n - 1)

/-- Affine-Narayana statement for the modified Narayana family. -/
def AffineModifiedNarayanaInterlacing
    (P : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
    StrictInterl ((C lam * X + C nu) * P (m - 1) + P m)
      ((C lam * X + C nu) * P m + P (m + 1))

/-- Difference `Q_n = P_n - P_{n-1}` used in the snake-interlacing matrix step. -/
def narayanaDifference (P : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  P n - P (n - 1)

/-- Difference `H_n = G_n - G_{n-1}` used in the snake-interlacing matrix step. -/
def auxiliaryDifference (G : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  G n - G (n - 1)

/-- The difference interlacing claim in Braun--Jal's proof of the snake interlacing theorem. -/
def SnakeDifferenceInterlacing
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam mu : ℝ}, 2 ≤ m → 0 ≤ lam → 0 ≤ mu →
    StrictInterl ((C lam * X + C mu) * G (m - 1) + auxiliaryDifference G m)
      ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m)

/-- The shifted difference interlacing claim in Braun--Jal's proof of the snake interlacing
theorem. -/
def ShiftedDifferenceInterlacing
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
    StrictInterl ((C lam * X + C nu) * G (m - 1) + G m)
      ((C lam * X + C nu) * P (m - 1) + P m)

/-- Side conditions for the shifted difference interlacing claim.

A uniform strict negative upper bound on the roots of `U` fails at the
zero-root endpoint `ν = -1`
(`shiftedDifferenceInterlacing_modified_left_boundary_not_strictRootBound`).
This bundle instead records nonpositivity of the roots
of `U` explicitly and orients the same-degree Obreschkoff alternative by the
root-sum comparison between `U` and `V`. -/
structure ShiftedDifferenceInterlacingRootSumSideConditions
    (P G : ℕ → ℝ[X]) : Prop where
  w_pos :
    ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
      HasPosLeadingCoeff ((C lam * X + C nu) * P m + P (m + 1))
  wu_lc :
    ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
      ((C lam * X + C nu) * P m + P (m + 1)).leadingCoeff =
        ((C lam * X + C nu) * P (m - 1) + P m).leadingCoeff
  deg_uw :
    ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
      ((C lam * X + C nu) * P (m - 1) + P m).natDegree + 1 =
        ((C lam * X + C nu) * P m + P (m + 1)).natDegree
  w_nonpos :
    ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
      ∀ r ∈ (((C lam * X + C nu) * P m + P (m + 1)).roots), r ≤ 0
  u_nonpos :
    ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
      ∀ r ∈ (((C lam * X + C nu) * P (m - 1) + P m).roots), r ≤ 0
  mid_pos :
    ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
      HasPosLeadingCoeff
        (((C lam * X + C nu) * P (m - 1) + P m) +
          X * ((C lam * X + C nu) * G (m - 1) + G m))
  v_pos :
    ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
      HasPosLeadingCoeff ((C lam * X + C nu) * G (m - 1) + G m)
  v_nonpos :
    ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
      ∀ r ∈ (((C lam * X + C nu) * G (m - 1) + G m).roots), r ≤ 0
  deg_vu :
    ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
      ((C lam * X + C nu) * G (m - 1) + G m).natDegree + 1 =
        ((C lam * X + C nu) * P (m - 1) + P m).natDegree
  u_v_roots_sum :
    ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
      ((C lam * X + C nu) * P (m - 1) + P m).roots.sum ≤
        ((C lam * X + C nu) * G (m - 1) + G m).roots.sum

/-- Auxiliary-recurrence rewrites the next modified Narayana combination in the
form used in Braun--Jal's proof of shifted difference interlacing claim. -/
theorem shiftedDifferenceInterlacing_next_eq_of_narayanaAuxiliaryGRecurrence
    {P G : ℕ → ℝ[X]} (hrec : NarayanaAuxiliaryGRecurrence P G)
    {m : ℕ} (hm : 2 ≤ m) (lam nu : ℝ) :
    (C lam * X + C nu) * P m + P (m + 1) =
      (1 + X) * ((C lam * X + C nu) * P (m - 1) + P m) +
        X * ((C lam * X + C nu) * G (m - 1) + G m) := by
  have hrec_m : X * G (m - 1) = P m - (1 + X) * P (m - 1) :=
    hrec (n := m) (by linarith)
  have hrec_succ : X * G m = P (m + 1) - (1 + X) * P m := by
    simpa using hrec (n := m + 1) (by linarith)
  rw [show
      (1 + X) * ((C lam * X + C nu) * P (m - 1) + P m) +
          X * ((C lam * X + C nu) * G (m - 1) + G m) =
        (C lam * X + C nu) * ((1 + X) * P (m - 1) + X * G (m - 1)) +
          ((1 + X) * P m + X * G m) by ring]
  rw [hrec_m, hrec_succ]
  ring

/-- Bundled root-sum assembly theorem for the shifted difference interlacing claim.

The root-sum side conditions only require the roots of `U` to be nonpositive,
so this route remains applicable when `U` has a root at zero. -/
theorem shiftedDifferenceInterlacing_of_combinatorial_rootSumSideConditions
    {P G : ℕ → ℝ[X]}
    (hrec : NarayanaAuxiliaryGRecurrence P G)
    (h34 : AffineModifiedNarayanaInterlacing P)
    (hside : ShiftedDifferenceInterlacingRootSumSideConditions P G) :
    ShiftedDifferenceInterlacing P G := by
  intro m lam nu hm hlam hnu
  let U : ℝ[X] := (C lam * X + C nu) * P (m - 1) + P m
  let V : ℝ[X] := (C lam * X + C nu) * G (m - 1) + G m
  let W : ℝ[X] := (C lam * X + C nu) * P m + P (m + 1)
  have hUW : StrictInterl U W := by
    simpa [U, W] using h34 (m := m) (lam := lam) (nu := nu) hm hlam hnu
  have hW_eq : W = (1 + X) * U + X * V := by
    simpa [U, V, W] using
      shiftedDifferenceInterlacing_next_eq_of_narayanaAuxiliaryGRecurrence hrec hm lam nu
  exact
    strictInterl_component_of_strictInterl_next_eq_add_X_mul_of_roots_sum_le hUW hW_eq
      (by simpa [W] using hside.w_pos hm hlam hnu)
      (by simpa [U, W] using hside.wu_lc hm hlam hnu)
      (by simpa [U, W] using hside.deg_uw hm hlam hnu)
      (by simpa [W] using hside.w_nonpos hm hlam hnu)
      (by simpa [U] using hside.u_nonpos hm hlam hnu)
      (by simpa [U, V] using hside.mid_pos hm hlam hnu)
      (by simpa [V] using hside.v_pos hm hlam hnu)
      (by simpa [V] using hside.v_nonpos hm hlam hnu)
      (by simpa [U, V] using hside.deg_vu hm hlam hnu)
      (by simpa [U, V] using hside.u_v_roots_sum hm hlam hnu)

/-- The matrix difference interlacing claim and the shifted difference interlacing claim in
Braun--Jal's
proof of the snake interlacing theorem are the same statement after writing `nu = mu - 1`. -/
theorem snakeDifferenceInterlacing_iff_shiftedDifferenceInterlacing (P G : ℕ → ℝ[X]) :
    SnakeDifferenceInterlacing P G ↔ ShiftedDifferenceInterlacing P G := by
  constructor
  · intro hclaim m lam nu hm hlam hnu
    have hmu : 0 ≤ nu + 1 := by linarith
    have hbase := hclaim (m := m) (lam := lam) (mu := nu + 1) hm hlam hmu
    have hC : (C (nu + 1) : ℝ[X]) = C nu + 1 := by simp
    have hleft :
        ((C lam * X + C (nu + 1)) * G (m - 1) + auxiliaryDifference G m) =
          ((C lam * X + C nu) * G (m - 1) + G m) := by
      rw [auxiliaryDifference, hC]
      ring_nf
    have hright :
        ((C lam * X + C (nu + 1)) * P (m - 1) + narayanaDifference P m) =
          ((C lam * X + C nu) * P (m - 1) + P m) := by
      rw [narayanaDifference, hC]
      ring_nf
    rwa [hleft, hright] at hbase
  · intro hclaim m lam mu hm hlam hmu
    have hnu : -1 ≤ mu - 1 := by linarith
    have hbase := hclaim (m := m) (lam := lam) (nu := mu - 1) hm hlam hnu
    have hC : (C (mu - 1) : ℝ[X]) = C mu - 1 := by simp
    have hleft :
        ((C lam * X + C (mu - 1)) * G (m - 1) + G m) =
          ((C lam * X + C mu) * G (m - 1) + auxiliaryDifference G m) := by
      rw [auxiliaryDifference, hC]
      ring_nf
    have hright :
        ((C lam * X + C (mu - 1)) * P (m - 1) + P m) =
          ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m) := by
      rw [narayanaDifference, hC]
      ring_nf
    rwa [hleft, hright] at hbase

/-- The generalized snake recurrence, the snake recurrence, in zero-based list
coordinates.  If `k` is the last position where `w` differs from its final
letter, then paper notation `w[:k+1]` and `w[:k]` become `takePrefix (k+1)`
and `takePrefix k` for the list of letters following `epsilon`. -/
def GeneralizedSnakeRecurrence
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord} {k : ℕ}, ¬ w.IsConstant → w.IsLastChangeIndex k →
    M w = M (w.takePrefix (k + 1)) * P (w.length - (k + 1)) +
      X * M (w.takePrefix k) * G (w.length - (k + 1))

end GeneralizedSnakePosets
end RealRooted
