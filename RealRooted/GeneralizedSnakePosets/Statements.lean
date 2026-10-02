import RealRooted.Basic
import RealRooted.GeneralizedSnakePosets.SquarecaseModel
import RealRooted.Mathlib.Algebra.Polynomial.Roots

/-!
# Braun--Jal generalized snake poset statement interfaces

This module contains the paper-facing theorem statements and the combinatorial-input
interfaces for Braun--Jal, *Order polytopes of generalized snake posets are
h^*-real-rooted*, arXiv:2607.00922v1.

The declarations here are deliberately abstract in the polynomial model.  The
concrete finite-board and squarecase geometry modules can construct these
interfaces without importing the higher-level package wrappers.
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
def NonNestingRookInterlacingStatement (M : SnakeWord → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord}, 1 ≤ w.length →
    (M w ≠ 0 ∧ (M w).Splits) ∧
      Interlaces (M w.deleteFinal) (M w)

/-- Snake-interlacing expressed for an abstract squarecase/non-nesting rook model. -/
abbrev SquarecaseRookModelSnakeInterlacingStatement
    (model : SquarecaseRookModel) : Prop :=
  NonNestingRookInterlacingStatement model.snakePolynomial

/-- The real-rootedness part of the snake interlacing theorem. -/
theorem nonNestingRook_ne_zero_and_splits_of_snakeInterlacing
    {M : SnakeWord → ℝ[X]}
    (hBJ : NonNestingRookInterlacingStatement M)
    {w : SnakeWord} (hw : 1 ≤ w.length) :
    M w ≠ 0 ∧ (M w).Splits :=
  (hBJ (w := w) hw).1

/-- The final-letter-deletion interlacing part of the snake interlacing theorem. -/
theorem nonNestingRook_deleteFinal_interlaces_of_snakeInterlacing
    {M : SnakeWord → ℝ[X]}
    (hBJ : NonNestingRookInterlacingStatement M)
    {w : SnakeWord} (hw : 1 ≤ w.length) :
    Interlaces (M w.deleteFinal) (M w) :=
  (hBJ (w := w) hw).2

/-! ## Narayana and recurrence interfaces from the combinatorial inputs -/

/-- A family `P` is the modified Narayana family attached to Narayana
polynomials `N` when `N_{n+1} = X * P_n`, i.e. `P_n(t) = t^{-1} N_{n+1}(t)`.
-/
def ModifiedNarayanaFamilyStatement
    (N P : ℕ → ℝ[X]) : Prop :=
  P 0 = 1 ∧ ∀ n : ℕ, N (n + 1) = X * P n

/-- The auxiliary polynomial `G_n` as the sum of non-nesting rook polynomials
of truncated staircases `mu_{n,i}` for `i = 0, ..., n - 1`. -/
def AuxiliaryGMatchesTruncatedStaircasesStatement
    (Mtrunc : ℕ → ℕ → ℝ[X]) (G : ℕ → ℝ[X]) : Prop :=
  ∀ n : ℕ, G n = ((List.range n).map fun i => Mtrunc n i).sum

/-- The auxiliary recurrence of Braun--Jal: `X * G_{n-1} = P_n - (1 + X) * P_{n-1}`. -/
def NarayanaAuxiliaryGRecurrenceStatement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → X * G (n - 1) = P n - (1 + X) * P (n - 1)

/-- Auxiliary-interlacing statement: the auxiliary `G_n` interlaces modified Narayana
polynomial `P_n`. -/
def AuxiliaryGInterlacesStatement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → StrictInterl (G n) (P n)

/-- Affine-Narayana statement for the modified Narayana family. -/
def AffineModifiedNarayanaInterlacingStatement
    (P : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
    StrictInterl ((C lam * X + C nu) * P (m - 1) + P m)
      ((C lam * X + C nu) * P m + P (m + 1))

/-- Difference `Q_n = P_n - P_{n-1}` used in the snake-interlacing matrix step. -/
def narayanaDifference (P : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  P n - P (n - 1)

/-- Shifted nonnegative-parameter form of the affine Narayana interlacing lemma, obtained from
the paper statement by writing `mu = nu + 1`.  This is the form that matches
the nonnegative matrix parameters in the snake-interlacing induction step. -/
def AffineModifiedNarayanaShiftedInterlacingStatement
    (P : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam mu : ℝ}, 2 ≤ m → 0 ≤ lam → 0 ≤ mu →
    StrictInterl ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m)
      ((C lam * X + C mu) * P m + narayanaDifference P (m + 1))

/-- The shifted nonnegative-parameter affine-Narayana form implies the paper's
`nu ≥ -1` form. -/
theorem affineModifiedNarayanaInterlacing_of_shifted
    {P : ℕ → ℝ[X]}
    (h : AffineModifiedNarayanaShiftedInterlacingStatement P) :
    AffineModifiedNarayanaInterlacingStatement P := by
  intro m lam nu hm hlam hnu
  have hmu : 0 ≤ nu + 1 := by linarith
  have hbase := h (m := m) (lam := lam) (mu := nu + 1) hm hlam hmu
  have hC : (C (nu + 1) : ℝ[X]) = C nu + 1 := by simp
  have hleft :
      ((C lam * X + C (nu + 1)) * P (m - 1) + narayanaDifference P m) =
        ((C lam * X + C nu) * P (m - 1) + P m) := by
    rw [narayanaDifference, hC]
    ring_nf
  have hright :
      ((C lam * X + C (nu + 1)) * P m + narayanaDifference P (m + 1)) =
        ((C lam * X + C nu) * P m + P (m + 1)) := by
    rw [narayanaDifference, hC]
    simp only [Nat.add_sub_cancel]
    ring_nf
  rwa [hleft, hright] at hbase

/-- The paper's `nu ≥ -1` affine-Narayana form implies shifted
nonnegative-parameter form. -/
theorem affineModifiedNarayanaShiftedInterlacing_of_affineNarayana
    {P : ℕ → ℝ[X]}
    (h : AffineModifiedNarayanaInterlacingStatement P) :
    AffineModifiedNarayanaShiftedInterlacingStatement P := by
  intro m lam mu hm hlam hmu
  have hnu : -1 ≤ mu - 1 := by linarith
  have hbase := h (m := m) (lam := lam) (nu := mu - 1) hm hlam hnu
  have hC : (C (mu - 1) : ℝ[X]) = C mu - 1 := by simp
  have hleft :
      ((C lam * X + C (mu - 1)) * P (m - 1) + P m) =
        ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m) := by
    rw [narayanaDifference, hC]
    ring_nf
  have hright :
      ((C lam * X + C (mu - 1)) * P m + P (m + 1)) =
        ((C lam * X + C mu) * P m + narayanaDifference P (m + 1)) := by
    rw [narayanaDifference, hC]
    simp only [Nat.add_sub_cancel]
    ring_nf
  rwa [hleft, hright] at hbase

/-- Equivalence between the paper's affine-Narayana statement and the shifted
nonnegative-parameter form. -/
theorem affineModifiedNarayanaShiftedInterlacing_iff_affineNarayana
    (P : ℕ → ℝ[X]) :
    AffineModifiedNarayanaShiftedInterlacingStatement P ↔
      AffineModifiedNarayanaInterlacingStatement P :=
  ⟨affineModifiedNarayanaInterlacing_of_shifted,
    affineModifiedNarayanaShiftedInterlacing_of_affineNarayana⟩

/-- Bounded form of the auxiliary recurrence, useful while finite initial
cases are being formalized before the all-`n` recurrence is available. -/
def NarayanaAuxiliaryGRecurrenceUpToStatement
    (P G : ℕ → ℝ[X]) (N : ℕ) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → n ≤ N →
    X * G (n - 1) = P n - (1 + X) * P (n - 1)

/-- Bounded form of the auxiliary interlacing lemma. -/
def AuxiliaryGInterlacesUpToStatement
    (P G : ℕ → ℝ[X]) (N : ℕ) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → n ≤ N → StrictInterl (G n) (P n)

/-- Bounded form of the affine Narayana interlacing lemma. -/
def AffineModifiedNarayanaInterlacingUpToStatement
    (P : ℕ → ℝ[X]) (N : ℕ) : Prop :=
  ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → m ≤ N → 0 ≤ lam → -1 ≤ nu →
    StrictInterl ((C lam * X + C nu) * P (m - 1) + P m)
      ((C lam * X + C nu) * P m + P (m + 1))

/-- Bounded shifted nonnegative-parameter form of the affine Narayana interlacing lemma. -/
def AffineModifiedNarayanaShiftedInterlacingUpToStatement
    (P : ℕ → ℝ[X]) (N : ℕ) : Prop :=
  ∀ {m : ℕ} {lam mu : ℝ}, 2 ≤ m → m ≤ N → 0 ≤ lam → 0 ≤ mu →
    StrictInterl ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m)
      ((C lam * X + C mu) * P m + narayanaDifference P (m + 1))

/-- The all-`n` auxiliary-interlacing statement implies every bounded auxiliary-interlacing
package. -/
theorem auxiliaryGInterlacesUpTo_of_statement
    {P G : ℕ → ℝ[X]} (h : AuxiliaryGInterlacesStatement P G)
    (N : ℕ) :
    AuxiliaryGInterlacesUpToStatement P G N := by
  intro n hn _hnN
  exact h hn

/-- The all-`n` affine-Narayana statement implies every bounded affine-Narayana package. -/
theorem affineModifiedNarayanaInterlacingUpTo_of_statement
    {P : ℕ → ℝ[X]} (h : AffineModifiedNarayanaInterlacingStatement P)
    (N : ℕ) :
    AffineModifiedNarayanaInterlacingUpToStatement P N := by
  intro m lam nu hm _hmN hlam hnu
  exact h hm hlam hnu

/-- The all-`n` shifted affine-Narayana statement implies every bounded shifted
the affine-Narayana package. -/
theorem affineModifiedNarayanaShiftedInterlacingUpTo_of_statement
    {P : ℕ → ℝ[X]}
    (h : AffineModifiedNarayanaShiftedInterlacingStatement P) (N : ℕ) :
    AffineModifiedNarayanaShiftedInterlacingUpToStatement P N := by
  intro m lam mu hm _hmN hlam hmu
  exact h hm hlam hmu

/-- A bounded shifted affine-Narayana package implies the bounded paper-shaped
`nu ≥ -1` package. -/
theorem affineModifiedNarayanaInterlacingUpTo_of_shifted
    {P : ℕ → ℝ[X]} {N : ℕ}
    (h : AffineModifiedNarayanaShiftedInterlacingUpToStatement P N) :
    AffineModifiedNarayanaInterlacingUpToStatement P N := by
  intro m lam nu hm hmN hlam hnu
  have hmu : 0 ≤ nu + 1 := by linarith
  have hbase := h (m := m) (lam := lam) (mu := nu + 1) hm hmN hlam hmu
  have hC : (C (nu + 1) : ℝ[X]) = C nu + 1 := by simp
  have hleft :
      ((C lam * X + C (nu + 1)) * P (m - 1) + narayanaDifference P m) =
        ((C lam * X + C nu) * P (m - 1) + P m) := by
    rw [narayanaDifference, hC]
    ring_nf
  have hright :
      ((C lam * X + C (nu + 1)) * P m + narayanaDifference P (m + 1)) =
        ((C lam * X + C nu) * P m + P (m + 1)) := by
    rw [narayanaDifference, hC]
    simp only [Nat.add_sub_cancel]
    ring_nf
  rwa [hleft, hright] at hbase

/-- A bounded paper-shaped affine-Narayana package implies the bounded shifted
nonnegative-parameter package. -/
theorem affineModifiedNarayanaShiftedInterlacingUpTo_of_affineNarayana
    {P : ℕ → ℝ[X]} {N : ℕ}
    (h : AffineModifiedNarayanaInterlacingUpToStatement P N) :
    AffineModifiedNarayanaShiftedInterlacingUpToStatement P N := by
  intro m lam mu hm hmN hlam hmu
  have hnu : -1 ≤ mu - 1 := by linarith
  have hbase := h (m := m) (lam := lam) (nu := mu - 1) hm hmN hlam hnu
  have hC : (C (mu - 1) : ℝ[X]) = C mu - 1 := by simp
  have hleft :
      ((C lam * X + C (mu - 1)) * P (m - 1) + P m) =
        ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m) := by
    rw [narayanaDifference, hC]
    ring_nf
  have hright :
      ((C lam * X + C (mu - 1)) * P m + P (m + 1)) =
        ((C lam * X + C mu) * P m + narayanaDifference P (m + 1)) := by
    rw [narayanaDifference, hC]
    simp only [Nat.add_sub_cancel]
    ring_nf
  rwa [hleft, hright] at hbase

/-- Bounded equivalence between the paper-shaped affine-Narayana statement and the
shifted nonnegative-parameter form. -/
theorem affineModifiedNarayanaShiftedInterlacingUpTo_iff_affineNarayana
    (P : ℕ → ℝ[X]) (N : ℕ) :
    AffineModifiedNarayanaShiftedInterlacingUpToStatement P N ↔
      AffineModifiedNarayanaInterlacingUpToStatement P N :=
  ⟨affineModifiedNarayanaInterlacingUpTo_of_shifted,
    affineModifiedNarayanaShiftedInterlacingUpTo_of_affineNarayana⟩

/-- Difference `H_n = G_n - G_{n-1}` used in the snake-interlacing matrix step. -/
def auxiliaryDifference (G : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  G n - G (n - 1)

/-- The difference interlacing claim in Braun--Jal's proof of the snake interlacing theorem. -/
def SnakeDifferenceInterlacingStatement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam mu : ℝ}, 2 ≤ m → 0 ≤ lam → 0 ≤ mu →
    StrictInterl ((C lam * X + C mu) * G (m - 1) + auxiliaryDifference G m)
      ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m)

/-- The shifted difference interlacing claim in Braun--Jal's proof of the snake interlacing
theorem. -/
def ShiftedDifferenceInterlacingStatement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
    StrictInterl ((C lam * X + C nu) * G (m - 1) + G m)
      ((C lam * X + C nu) * P (m - 1) + P m)

/-- Leading-coefficient, degree, and root-location side conditions used by
the univariate conversion step in the proof of shifted difference interlacing claim.

The bundle intentionally does not include the auxiliary recurrence or the affine Narayana
interlacing lemma: those
are the structural combinatorial inputs, while these are the local facts about the
three windows `U`, `V`, and `W` consumed by the conversion theorem. -/
structure ShiftedDifferenceInterlacingSideConditions
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
  u_bound :
    ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
      ∃ c : ℝ,
        (∀ s ∈ (((C lam * X + C nu) * P (m - 1) + P m).roots), s ≤ c) ∧
          c < 0

/-- Root-sum replacement for `ShiftedDifferenceInterlacingSideConditions`.

The strict negative upper bound in the older bundle fails at legitimate
zero-root endpoints.  This bundle instead records nonpositivity of the roots
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
    {P G : ℕ → ℝ[X]} (hrec : NarayanaAuxiliaryGRecurrenceStatement P G)
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

/-- Assembly theorem for the shifted difference interlacing claim from the auxiliary recurrence,
Lemma
3.4, and the local side conditions used by the univariate conversion step.

The auxiliary interlacing lemma is not hidden in this theorem: the remaining `G`-side root and
degree
facts are passed explicitly so later concrete work can discharge them without
changing the assembly proof. -/
theorem shiftedDifferenceInterlacing_of_combinatorial
    {P G : ℕ → ℝ[X]}
    (hrec : NarayanaAuxiliaryGRecurrenceStatement P G)
    (h34 : AffineModifiedNarayanaInterlacingStatement P)
    (hW_pos :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        HasPosLeadingCoeff ((C lam * X + C nu) * P m + P (m + 1)))
    (hWU_lc :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ((C lam * X + C nu) * P m + P (m + 1)).leadingCoeff =
          ((C lam * X + C nu) * P (m - 1) + P m).leadingCoeff)
    (hdeg_UW :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ((C lam * X + C nu) * P (m - 1) + P m).natDegree + 1 =
          ((C lam * X + C nu) * P m + P (m + 1)).natDegree)
    (hW_nonpos :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ∀ r ∈ (((C lam * X + C nu) * P m + P (m + 1)).roots), r ≤ 0)
    (hmid_pos :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        HasPosLeadingCoeff
          (((C lam * X + C nu) * P (m - 1) + P m) +
            X * ((C lam * X + C nu) * G (m - 1) + G m)))
    (hV_pos :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        HasPosLeadingCoeff ((C lam * X + C nu) * G (m - 1) + G m))
    (hV_nonpos :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ∀ r ∈ (((C lam * X + C nu) * G (m - 1) + G m).roots), r ≤ 0)
    (hdeg_VU :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ((C lam * X + C nu) * G (m - 1) + G m).natDegree + 1 =
          ((C lam * X + C nu) * P (m - 1) + P m).natDegree)
    (hU_bound :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ∃ c : ℝ,
          (∀ s ∈ (((C lam * X + C nu) * P (m - 1) + P m).roots), s ≤ c) ∧
            c < 0) :
    ShiftedDifferenceInterlacingStatement P G := by
  intro m lam nu hm hlam hnu
  let U : ℝ[X] := (C lam * X + C nu) * P (m - 1) + P m
  let V : ℝ[X] := (C lam * X + C nu) * G (m - 1) + G m
  let W : ℝ[X] := (C lam * X + C nu) * P m + P (m + 1)
  have hUW : StrictInterl U W := by
    simpa [U, W] using h34 (m := m) (lam := lam) (nu := nu) hm hlam hnu
  have hW_eq : W = (1 + X) * U + X * V := by
    simpa [U, V, W] using
      shiftedDifferenceInterlacing_next_eq_of_narayanaAuxiliaryGRecurrence hrec hm lam nu
  have hU_nonpos : ∀ r ∈ U.roots, r ≤ 0 := by
    rcases hU_bound hm hlam hnu with ⟨c, hU_le, hc_lt⟩
    intro r hr
    exact le_trans (hU_le r (by simpa [U] using hr)) (le_of_lt hc_lt)
  exact
    strictInterl_component_of_strictInterl_next_eq_add_X_mul hUW hW_eq
      (by simpa [W] using hW_pos hm hlam hnu)
      (by simpa [U, W] using hWU_lc hm hlam hnu)
      (by simpa [U, W] using hdeg_UW hm hlam hnu)
      (by simpa [W] using hW_nonpos hm hlam hnu)
      hU_nonpos
      (by simpa [U, V] using hmid_pos hm hlam hnu)
      (by simpa [V] using hV_pos hm hlam hnu)
      (by simpa [V] using hV_nonpos hm hlam hnu)
      (by simpa [U, V] using hdeg_VU hm hlam hnu)
      (by simpa [U] using hU_bound hm hlam hnu)

/-- Bundled-side-condition form of `shiftedDifferenceInterlacing_of_combinatorial`. -/
theorem shiftedDifferenceInterlacing_of_combinatorial_sideConditions
    {P G : ℕ → ℝ[X]}
    (hrec : NarayanaAuxiliaryGRecurrenceStatement P G)
    (h34 : AffineModifiedNarayanaInterlacingStatement P)
    (hside : ShiftedDifferenceInterlacingSideConditions P G) :
    ShiftedDifferenceInterlacingStatement P G :=
  shiftedDifferenceInterlacing_of_combinatorial hrec h34
    hside.w_pos hside.wu_lc hside.deg_uw hside.w_nonpos hside.mid_pos
    hside.v_pos hside.v_nonpos hside.deg_vu hside.u_bound

/-- Bundled root-sum assembly theorem for the shifted difference interlacing claim.

Unlike `shiftedDifferenceInterlacing_of_combinatorial_sideConditions`, this route remains
applicable when `U` has a root at zero. -/
theorem shiftedDifferenceInterlacing_of_combinatorial_rootSumSideConditions
    {P G : ℕ → ℝ[X]}
    (hrec : NarayanaAuxiliaryGRecurrenceStatement P G)
    (h34 : AffineModifiedNarayanaInterlacingStatement P)
    (hside : ShiftedDifferenceInterlacingRootSumSideConditions P G) :
    ShiftedDifferenceInterlacingStatement P G := by
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
    SnakeDifferenceInterlacingStatement P G ↔ ShiftedDifferenceInterlacingStatement P G := by
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
def GeneralizedSnakeRecurrenceStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord} {k : ℕ}, ¬ w.IsConstant → w.IsLastChangeIndex k →
    M w = M (w.takePrefix (k + 1)) * P (w.length - (k + 1)) +
      X * M (w.takePrefix k) * G (w.length - (k + 1))

/-- Computable form of the snake recurrence, using `lastChangeIndex?` instead of a
separate predicate-form witness. -/
def GeneralizedSnakeRecurrenceComputableStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord} {k : ℕ}, w.lastChangeIndex? = some k →
    M w = M (w.takePrefix (k + 1)) * P (w.length - (k + 1)) +
      X * M (w.takePrefix k) * G (w.length - (k + 1))

/-- The predicate-form recurrence implies the computable `lastChangeIndex?`
form. -/
theorem snakeRecurrenceComputable_of_snakeRecurrence
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : GeneralizedSnakeRecurrenceStatement M P G) :
    GeneralizedSnakeRecurrenceComputableStatement M P G := by
  intro w k hlast
  exact hrec (SnakeWord.not_isConstant_of_lastChangeIndex?_eq_some hlast)
    (SnakeWord.isLastChangeIndex_of_lastChangeIndex?_eq_some hlast)

/-- The computable `lastChangeIndex?` recurrence implies the predicate-form
recurrence. -/
theorem snakeRecurrence_of_snakeRecurrenceComputable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : GeneralizedSnakeRecurrenceComputableStatement M P G) :
    GeneralizedSnakeRecurrenceStatement M P G := by
  intro w k _hconst hlast
  exact hrec (SnakeWord.lastChangeIndex?_eq_some_of_isLastChangeIndex hlast)

/-- The predicate-form and computable forms of the generalized snake
recurrence are equivalent. -/
theorem snakeRecurrenceComputable_iff_snakeRecurrence
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) :
    GeneralizedSnakeRecurrenceComputableStatement M P G ↔
      GeneralizedSnakeRecurrenceStatement M P G :=
  ⟨snakeRecurrence_of_snakeRecurrenceComputable, snakeRecurrenceComputable_of_snakeRecurrence⟩

/-- Statement-level package for the induction route from the combinatorial inputs
Narayana and recurrence ingredients to the snake interlacing theorem. -/
def SnakeInterlacingInductionRouteStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  AuxiliaryGInterlacesStatement P G →
    AffineModifiedNarayanaInterlacingStatement P →
    GeneralizedSnakeRecurrenceStatement M P G →
      NonNestingRookInterlacingStatement M

/-- Computable-recursion variant of the current snake-interlacing induction route. -/
def SnakeInterlacingInductionRouteComputableStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  AuxiliaryGInterlacesStatement P G →
    AffineModifiedNarayanaInterlacingStatement P →
    GeneralizedSnakeRecurrenceComputableStatement M P G →
      NonNestingRookInterlacingStatement M

/-- The predicate-form induction route also accepts a computable recurrence
input. -/
theorem snakeInterlacingInductionRouteComputable_of_snakeInterlacingInductionRoute
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : SnakeInterlacingInductionRouteStatement M P G) :
    SnakeInterlacingInductionRouteComputableStatement M P G := by
  intro h33 h34 hrec
  exact hroute h33 h34 (snakeRecurrence_of_snakeRecurrenceComputable hrec)

/-- The computable-recursion induction route implies the predicate-form route. -/
theorem snakeInterlacingInductionRoute_of_snakeInterlacingInductionRouteComputable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : SnakeInterlacingInductionRouteComputableStatement M P G) :
    SnakeInterlacingInductionRouteStatement M P G := by
  intro h33 h34 hrec
  exact hroute h33 h34 (snakeRecurrenceComputable_of_snakeRecurrence hrec)

/-- Predicate and computable forms of the snake-interlacing induction route are
equivalent. -/
theorem snakeInterlacingInductionRouteComputable_iff_snakeInterlacingInductionRoute
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) :
    SnakeInterlacingInductionRouteComputableStatement M P G ↔
      SnakeInterlacingInductionRouteStatement M P G :=
  ⟨snakeInterlacingInductionRoute_of_snakeInterlacingInductionRouteComputable,
    snakeInterlacingInductionRouteComputable_of_snakeInterlacingInductionRoute⟩

/-- Bundled the combinatorial ingredients needed by the current snake-interlacing induction
interface. -/
structure SnakeInterlacingInputs
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop where
  auxiliaryGInterlacing : AuxiliaryGInterlacesStatement P G
  affineNarayana : AffineModifiedNarayanaInterlacingStatement P
  recurrence : GeneralizedSnakeRecurrenceStatement M P G

/-- Bundled the combinatorial ingredients using the computable recurrence form. -/
structure SnakeInterlacingComputableInputs
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop where
  auxiliaryGInterlacing : AuxiliaryGInterlacesStatement P G
  affineNarayana : AffineModifiedNarayanaInterlacingStatement P
  recurrence : GeneralizedSnakeRecurrenceComputableStatement M P G

/-- Bundled the combinatorial ingredients using shifted nonnegative-parameter
the affine-Narayana form. -/
structure SnakeInterlacingShiftedInputs
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop where
  auxiliaryGInterlacing : AuxiliaryGInterlacesStatement P G
  affineNarayana : AffineModifiedNarayanaShiftedInterlacingStatement P
  recurrence : GeneralizedSnakeRecurrenceStatement M P G

/-- Bundled the combinatorial ingredients using shifted the affine-Narayana form and the
computable recurrence form. -/
structure SnakeInterlacingComputableShiftedInputs
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop where
  auxiliaryGInterlacing : AuxiliaryGInterlacesStatement P G
  affineNarayana : AffineModifiedNarayanaShiftedInterlacingStatement P
  recurrence : GeneralizedSnakeRecurrenceComputableStatement M P G

/-- Convert computable combinatorial inputs into the predicate-form bundle. -/
theorem snakeInterlacingInputs_of_computable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hinputs : SnakeInterlacingComputableInputs M P G) :
    SnakeInterlacingInputs M P G where
  auxiliaryGInterlacing := hinputs.auxiliaryGInterlacing
  affineNarayana := hinputs.affineNarayana
  recurrence := snakeRecurrence_of_snakeRecurrenceComputable hinputs.recurrence

/-- Convert shifted combinatorial inputs into the paper-shaped bundle. -/
theorem snakeInterlacingInputs_of_shifted
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hinputs : SnakeInterlacingShiftedInputs M P G) :
    SnakeInterlacingInputs M P G where
  auxiliaryGInterlacing := hinputs.auxiliaryGInterlacing
  affineNarayana := affineModifiedNarayanaInterlacing_of_shifted hinputs.affineNarayana
  recurrence := hinputs.recurrence

/-- Convert computable shifted combinatorial inputs into the paper-shaped
computable bundle. -/
theorem snakeInterlacingComputableInputs_of_shifted
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hinputs : SnakeInterlacingComputableShiftedInputs M P G) :
    SnakeInterlacingComputableInputs M P G where
  auxiliaryGInterlacing := hinputs.auxiliaryGInterlacing
  affineNarayana := affineModifiedNarayanaInterlacing_of_shifted hinputs.affineNarayana
  recurrence := hinputs.recurrence

/-- Convert computable shifted combinatorial inputs into the predicate-recurrence
shifted bundle. -/
theorem snakeInterlacingShiftedInputs_of_computable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hinputs : SnakeInterlacingComputableShiftedInputs M P G) :
    SnakeInterlacingShiftedInputs M P G where
  auxiliaryGInterlacing := hinputs.auxiliaryGInterlacing
  affineNarayana := hinputs.affineNarayana
  recurrence := snakeRecurrence_of_snakeRecurrenceComputable hinputs.recurrence

/-- Feed the bundled combinatorial ingredients into the abstract snake-interlacing
induction route. -/
theorem snakeInterlacing_of_combinatorialInputs
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : SnakeInterlacingInductionRouteStatement M P G)
    (hinputs : SnakeInterlacingInputs M P G) :
    NonNestingRookInterlacingStatement M :=
  hroute hinputs.auxiliaryGInterlacing hinputs.affineNarayana hinputs.recurrence

/-- Feed computable combinatorial ingredients into the abstract snake-interlacing
induction route. -/
theorem snakeInterlacing_of_combinatorialComputableInputs
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : SnakeInterlacingInductionRouteStatement M P G)
    (hinputs : SnakeInterlacingComputableInputs M P G) :
    NonNestingRookInterlacingStatement M :=
  snakeInterlacing_of_combinatorialInputs hroute
    (snakeInterlacingInputs_of_computable hinputs)

/-- Feed shifted combinatorial ingredients into the abstract snake-interlacing induction
route. -/
theorem snakeInterlacing_of_combinatorialShiftedInputs
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : SnakeInterlacingInductionRouteStatement M P G)
    (hinputs : SnakeInterlacingShiftedInputs M P G) :
    NonNestingRookInterlacingStatement M :=
  snakeInterlacing_of_combinatorialInputs hroute
    (snakeInterlacingInputs_of_shifted hinputs)

/-- Feed computable shifted combinatorial ingredients into the abstract Theorem
4.1 induction route. -/
theorem snakeInterlacing_of_combinatorialComputableShiftedInputs
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : SnakeInterlacingInductionRouteStatement M P G)
    (hinputs : SnakeInterlacingComputableShiftedInputs M P G) :
    NonNestingRookInterlacingStatement M :=
  snakeInterlacing_of_combinatorialComputableInputs hroute
    (snakeInterlacingComputableInputs_of_shifted hinputs)

end GeneralizedSnakePosets
end RealRooted
