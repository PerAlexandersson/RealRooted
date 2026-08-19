import RealRooted.Basic
import RealRooted.GeneralizedSnakePosets.SquarecaseModel
import RealRooted.Mathlib.Algebra.Polynomial.Roots

/-!
# Braun--Jal generalized snake poset statement interfaces

This module contains the paper-facing theorem statements and Section 3 input
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

/-- Braun--Jal Theorem 4.1, abstracted over the polynomial model.

The source theorem concerns the concrete non-nesting rook polynomial `M_w`: it
asserts real-rootedness and that deleting the final letter gives
`M_{w'} << M_w`. This interface is only an abstract package for arbitrary `M`.
A source-facing theorem must instantiate `generalizedSnakeRookModel` and prove
the degree and model-identification bridges needed to use local `Interlaces`. -/
def Theorem41NonNestingRookStatement (M : SnakeWord → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord}, 1 ≤ w.length →
    (M w ≠ 0 ∧ (M w).Splits) ∧
      Interlaces (M w.deleteFinal) (M w)

/-- Theorem 4.1 expressed for an abstract squarecase/non-nesting rook model. -/
abbrev SquarecaseRookModelTheorem41Statement
    (model : SquarecaseRookModel) : Prop :=
  Theorem41NonNestingRookStatement model.snakePolynomial

/-- The real-rootedness part of Braun--Jal Theorem 4.1. -/
theorem nonNestingRook_ne_zero_and_splits_of_theorem41
    {M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    {w : SnakeWord} (hw : 1 ≤ w.length) :
    M w ≠ 0 ∧ (M w).Splits :=
  (hBJ (w := w) hw).1

/-- The final-letter-deletion interlacing part of Braun--Jal Theorem 4.1. -/
theorem nonNestingRook_deleteFinal_interlaces_of_theorem41
    {M : SnakeWord → ℝ[X]}
    (hBJ : Theorem41NonNestingRookStatement M)
    {w : SnakeWord} (hw : 1 ≤ w.length) :
    Interlaces (M w.deleteFinal) (M w) :=
  (hBJ (w := w) hw).2

/-! ## Narayana and recurrence interfaces from Section 3 -/

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

/-- Equation (2) of Braun--Jal: `X * G_{n-1} = P_n - (1 + X) * P_{n-1}`. -/
def NarayanaAuxiliaryGRecurrenceStatement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → X * G (n - 1) = P n - (1 + X) * P (n - 1)

/-- Lemma 3.3 statement: the auxiliary `G_n` interlaces the modified Narayana
polynomial `P_n`. -/
def Lemma33AuxiliaryGInterlacesStatement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → Prec (G n) (P n)

/-- Lemma 3.4 statement for the modified Narayana family. -/
def Lemma34ModifiedNarayanaInterlacingStatement
    (P : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
    Prec ((C lam * X + C nu) * P (m - 1) + P m)
      ((C lam * X + C nu) * P m + P (m + 1))

/-- Difference `Q_n = P_n - P_{n-1}` used in the Theorem 4.1 matrix step. -/
def narayanaDifference (P : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  P n - P (n - 1)

/-- Shifted nonnegative-parameter form of Braun--Jal Lemma 3.4, obtained from
the paper statement by writing `mu = nu + 1`.  This is the form that matches
the nonnegative matrix parameters in the Theorem 4.1 induction step. -/
def Lemma34ModifiedNarayanaShiftedInterlacingStatement
    (P : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam mu : ℝ}, 2 ≤ m → 0 ≤ lam → 0 ≤ mu →
    Prec ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m)
      ((C lam * X + C mu) * P m + narayanaDifference P (m + 1))

/-- The shifted nonnegative-parameter Lemma 3.4 form implies the paper's
`nu ≥ -1` form. -/
theorem lemma34ModifiedNarayanaInterlacing_of_shifted
    {P : ℕ → ℝ[X]}
    (h : Lemma34ModifiedNarayanaShiftedInterlacingStatement P) :
    Lemma34ModifiedNarayanaInterlacingStatement P := by
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

/-- The paper's `nu ≥ -1` Lemma 3.4 form implies the shifted
nonnegative-parameter form. -/
theorem lemma34ModifiedNarayanaShiftedInterlacing_of_lemma34
    {P : ℕ → ℝ[X]}
    (h : Lemma34ModifiedNarayanaInterlacingStatement P) :
    Lemma34ModifiedNarayanaShiftedInterlacingStatement P := by
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

/-- Equivalence between the paper's Lemma 3.4 statement and the shifted
nonnegative-parameter form. -/
theorem lemma34ModifiedNarayanaShiftedInterlacing_iff_lemma34
    (P : ℕ → ℝ[X]) :
    Lemma34ModifiedNarayanaShiftedInterlacingStatement P ↔
      Lemma34ModifiedNarayanaInterlacingStatement P :=
  ⟨lemma34ModifiedNarayanaInterlacing_of_shifted,
    lemma34ModifiedNarayanaShiftedInterlacing_of_lemma34⟩

/-- Bounded form of Braun--Jal equation (2), useful while finite initial
cases are being formalized before the all-`n` recurrence is available. -/
def NarayanaAuxiliaryGRecurrenceUpToStatement
    (P G : ℕ → ℝ[X]) (N : ℕ) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → n ≤ N →
    X * G (n - 1) = P n - (1 + X) * P (n - 1)

/-- Bounded form of Braun--Jal Lemma 3.3. -/
def Lemma33AuxiliaryGInterlacesUpToStatement
    (P G : ℕ → ℝ[X]) (N : ℕ) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → n ≤ N → Prec (G n) (P n)

/-- Bounded form of Braun--Jal Lemma 3.4. -/
def Lemma34ModifiedNarayanaInterlacingUpToStatement
    (P : ℕ → ℝ[X]) (N : ℕ) : Prop :=
  ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → m ≤ N → 0 ≤ lam → -1 ≤ nu →
    Prec ((C lam * X + C nu) * P (m - 1) + P m)
      ((C lam * X + C nu) * P m + P (m + 1))

/-- Bounded shifted nonnegative-parameter form of Braun--Jal Lemma 3.4. -/
def Lemma34ModifiedNarayanaShiftedInterlacingUpToStatement
    (P : ℕ → ℝ[X]) (N : ℕ) : Prop :=
  ∀ {m : ℕ} {lam mu : ℝ}, 2 ≤ m → m ≤ N → 0 ≤ lam → 0 ≤ mu →
    Prec ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m)
      ((C lam * X + C mu) * P m + narayanaDifference P (m + 1))

/-- The all-`n` recurrence implies every bounded recurrence package. -/
theorem narayanaAuxiliaryGRecurrenceUpTo_of_statement
    {P G : ℕ → ℝ[X]} (h : NarayanaAuxiliaryGRecurrenceStatement P G)
    (N : ℕ) :
    NarayanaAuxiliaryGRecurrenceUpToStatement P G N := by
  intro n hn _hnN
  exact h hn

/-- The all-`n` Lemma 3.3 statement implies every bounded Lemma 3.3 package. -/
theorem lemma33AuxiliaryGInterlacesUpTo_of_statement
    {P G : ℕ → ℝ[X]} (h : Lemma33AuxiliaryGInterlacesStatement P G)
    (N : ℕ) :
    Lemma33AuxiliaryGInterlacesUpToStatement P G N := by
  intro n hn _hnN
  exact h hn

/-- The all-`n` Lemma 3.4 statement implies every bounded Lemma 3.4 package. -/
theorem lemma34ModifiedNarayanaInterlacingUpTo_of_statement
    {P : ℕ → ℝ[X]} (h : Lemma34ModifiedNarayanaInterlacingStatement P)
    (N : ℕ) :
    Lemma34ModifiedNarayanaInterlacingUpToStatement P N := by
  intro m lam nu hm _hmN hlam hnu
  exact h hm hlam hnu

/-- The all-`n` shifted Lemma 3.4 statement implies every bounded shifted
Lemma 3.4 package. -/
theorem lemma34ModifiedNarayanaShiftedInterlacingUpTo_of_statement
    {P : ℕ → ℝ[X]}
    (h : Lemma34ModifiedNarayanaShiftedInterlacingStatement P) (N : ℕ) :
    Lemma34ModifiedNarayanaShiftedInterlacingUpToStatement P N := by
  intro m lam mu hm _hmN hlam hmu
  exact h hm hlam hmu

/-- A bounded shifted Lemma 3.4 package implies the bounded paper-shaped
`nu ≥ -1` package. -/
theorem lemma34ModifiedNarayanaInterlacingUpTo_of_shifted
    {P : ℕ → ℝ[X]} {N : ℕ}
    (h : Lemma34ModifiedNarayanaShiftedInterlacingUpToStatement P N) :
    Lemma34ModifiedNarayanaInterlacingUpToStatement P N := by
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

/-- A bounded paper-shaped Lemma 3.4 package implies the bounded shifted
nonnegative-parameter package. -/
theorem lemma34ModifiedNarayanaShiftedInterlacingUpTo_of_lemma34
    {P : ℕ → ℝ[X]} {N : ℕ}
    (h : Lemma34ModifiedNarayanaInterlacingUpToStatement P N) :
    Lemma34ModifiedNarayanaShiftedInterlacingUpToStatement P N := by
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

/-- Bounded equivalence between the paper-shaped Lemma 3.4 statement and the
shifted nonnegative-parameter form. -/
theorem lemma34ModifiedNarayanaShiftedInterlacingUpTo_iff_lemma34
    (P : ℕ → ℝ[X]) (N : ℕ) :
    Lemma34ModifiedNarayanaShiftedInterlacingUpToStatement P N ↔
      Lemma34ModifiedNarayanaInterlacingUpToStatement P N :=
  ⟨lemma34ModifiedNarayanaInterlacingUpTo_of_shifted,
    lemma34ModifiedNarayanaShiftedInterlacingUpTo_of_lemma34⟩

/-- Difference `H_n = G_n - G_{n-1}` used in the Theorem 4.1 matrix step. -/
def auxiliaryDifference (G : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  G n - G (n - 1)

/-- The claim labeled `(6)` in Braun--Jal's proof of Theorem 4.1. -/
def Theorem41MatrixClaimStatement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam mu : ℝ}, 2 ≤ m → 0 ≤ lam → 0 ≤ mu →
    Prec ((C lam * X + C mu) * G (m - 1) + auxiliaryDifference G m)
      ((C lam * X + C mu) * P (m - 1) + narayanaDifference P m)

/-- The reindexed claim labeled `(7)` in Braun--Jal's proof of Theorem 4.1. -/
def Theorem41Claim7Statement
    (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
    Prec ((C lam * X + C nu) * G (m - 1) + G m)
      ((C lam * X + C nu) * P (m - 1) + P m)

/-- Leading-coefficient, degree, and root-location side conditions used by
the univariate conversion step in the proof of Braun--Jal Claim `(7)`.

The bundle intentionally does not include equation `(2)` or Lemma 3.4: those
are the structural Section 3 inputs, while these are the local facts about the
three windows `U`, `V`, and `W` consumed by the conversion theorem. -/
structure Theorem41Claim7SideConditions
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

/-- Root-sum replacement for `Theorem41Claim7SideConditions`.

The strict negative upper bound in the older bundle fails at legitimate
zero-root endpoints.  This bundle instead records nonpositivity of the roots
of `U` explicitly and orients the same-degree Obreschkoff alternative by the
root-sum comparison between `U` and `V`. -/
structure Theorem41Claim7RootSumSideConditions
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

/-- Equation `(2)` rewrites the next modified Narayana combination in the
form used in Braun--Jal's proof of Claim `(7)`. -/
theorem theorem41Claim7_next_eq_of_narayanaAuxiliaryGRecurrence
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

/-- Assembly theorem for Braun--Jal Claim `(7)` from equation `(2)`, Lemma
3.4, and the local side conditions used by the univariate conversion step.

Lemma 3.3 is not hidden in this theorem: the remaining `G`-side root and degree
facts are passed explicitly so later concrete work can discharge them without
changing the assembly proof. -/
theorem theorem41Claim7_of_section3
    {P G : ℕ → ℝ[X]}
    (hrec : NarayanaAuxiliaryGRecurrenceStatement P G)
    (h34 : Lemma34ModifiedNarayanaInterlacingStatement P)
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
    Theorem41Claim7Statement P G := by
  intro m lam nu hm hlam hnu
  let U : ℝ[X] := (C lam * X + C nu) * P (m - 1) + P m
  let V : ℝ[X] := (C lam * X + C nu) * G (m - 1) + G m
  let W : ℝ[X] := (C lam * X + C nu) * P m + P (m + 1)
  have hUW : Prec U W := by simpa [U, W] using h34 (m := m) (lam := lam) (nu := nu) hm hlam hnu
  have hW_eq : W = (1 + X) * U + X * V := by
    simpa [U, V, W] using
      theorem41Claim7_next_eq_of_narayanaAuxiliaryGRecurrence hrec hm lam nu
  have hU_nonpos : ∀ r ∈ U.roots, r ≤ 0 := by
    rcases hU_bound hm hlam hnu with ⟨c, hU_le, hc_lt⟩
    intro r hr
    exact le_trans (hU_le r (by simpa [U] using hr)) (le_of_lt hc_lt)
  exact
    prec_component_of_prec_next_eq_add_X_mul hUW hW_eq
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

/-- Bundled-side-condition form of `theorem41Claim7_of_section3`. -/
theorem theorem41Claim7_of_section3_sideConditions
    {P G : ℕ → ℝ[X]}
    (hrec : NarayanaAuxiliaryGRecurrenceStatement P G)
    (h34 : Lemma34ModifiedNarayanaInterlacingStatement P)
    (hside : Theorem41Claim7SideConditions P G) :
    Theorem41Claim7Statement P G :=
  theorem41Claim7_of_section3 hrec h34
    hside.w_pos hside.wu_lc hside.deg_uw hside.w_nonpos hside.mid_pos
    hside.v_pos hside.v_nonpos hside.deg_vu hside.u_bound

/-- Bundled root-sum assembly theorem for Braun--Jal Claim `(7)`.

Unlike `theorem41Claim7_of_section3_sideConditions`, this route remains
applicable when `U` has a root at zero. -/
theorem theorem41Claim7_of_section3_rootSumSideConditions
    {P G : ℕ → ℝ[X]}
    (hrec : NarayanaAuxiliaryGRecurrenceStatement P G)
    (h34 : Lemma34ModifiedNarayanaInterlacingStatement P)
    (hside : Theorem41Claim7RootSumSideConditions P G) :
    Theorem41Claim7Statement P G := by
  intro m lam nu hm hlam hnu
  let U : ℝ[X] := (C lam * X + C nu) * P (m - 1) + P m
  let V : ℝ[X] := (C lam * X + C nu) * G (m - 1) + G m
  let W : ℝ[X] := (C lam * X + C nu) * P m + P (m + 1)
  have hUW : Prec U W := by simpa [U, W] using h34 (m := m) (lam := lam) (nu := nu) hm hlam hnu
  have hW_eq : W = (1 + X) * U + X * V := by
    simpa [U, V, W] using
      theorem41Claim7_next_eq_of_narayanaAuxiliaryGRecurrence hrec hm lam nu
  exact
    prec_component_of_prec_next_eq_add_X_mul_of_roots_sum_le hUW hW_eq
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

/-- The matrix claim `(6)` and the reindexed claim `(7)` in Braun--Jal's
proof of Theorem 4.1 are the same statement after writing `nu = mu - 1`. -/
theorem theorem41MatrixClaim_iff_claim7 (P G : ℕ → ℝ[X]) :
    Theorem41MatrixClaimStatement P G ↔ Theorem41Claim7Statement P G := by
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

/-- The generalized snake recurrence, Theorem 3.5, in zero-based list
coordinates.  If `k` is the last position where `w` differs from its final
letter, then paper notation `w[:k+1]` and `w[:k]` become `takePrefix (k+1)`
and `takePrefix k` for the list of letters following `epsilon`. -/
def Theorem35GeneralizedSnakeRecurrenceStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord} {k : ℕ}, ¬ w.IsConstant → w.IsLastChangeIndex k →
    M w = M (w.takePrefix (k + 1)) * P (w.length - (k + 1)) +
      X * M (w.takePrefix k) * G (w.length - (k + 1))

/-- Computable form of Theorem 3.5, using `lastChangeIndex?` instead of a
separate predicate-form witness. -/
def Theorem35GeneralizedSnakeRecurrenceComputableStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  ∀ {w : SnakeWord} {k : ℕ}, w.lastChangeIndex? = some k →
    M w = M (w.takePrefix (k + 1)) * P (w.length - (k + 1)) +
      X * M (w.takePrefix k) * G (w.length - (k + 1))

/-- The predicate-form recurrence implies the computable `lastChangeIndex?`
form. -/
theorem theorem35Computable_of_theorem35
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : Theorem35GeneralizedSnakeRecurrenceStatement M P G) :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G := by
  intro w k hlast
  exact hrec (SnakeWord.not_isConstant_of_lastChangeIndex?_eq_some hlast)
    (SnakeWord.isLastChangeIndex_of_lastChangeIndex?_eq_some hlast)

/-- The computable `lastChangeIndex?` recurrence implies the predicate-form
recurrence. -/
theorem theorem35_of_theorem35Computable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hrec : Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G) :
    Theorem35GeneralizedSnakeRecurrenceStatement M P G := by
  intro w k _hconst hlast
  exact hrec (SnakeWord.lastChangeIndex?_eq_some_of_isLastChangeIndex hlast)

/-- The predicate-form and computable forms of the generalized snake
recurrence are equivalent. -/
theorem theorem35Computable_iff_theorem35
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) :
    Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G ↔
      Theorem35GeneralizedSnakeRecurrenceStatement M P G :=
  ⟨theorem35_of_theorem35Computable, theorem35Computable_of_theorem35⟩

/-- Statement-level package for the induction route from the Section 3
Narayana and recurrence ingredients to Theorem 4.1. -/
def Theorem41InductionRouteStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  Lemma33AuxiliaryGInterlacesStatement P G →
    Lemma34ModifiedNarayanaInterlacingStatement P →
    Theorem35GeneralizedSnakeRecurrenceStatement M P G →
      Theorem41NonNestingRookStatement M

/-- Computable-recursion variant of the current Theorem 4.1 induction route. -/
def Theorem41InductionRouteComputableStatement
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop :=
  Lemma33AuxiliaryGInterlacesStatement P G →
    Lemma34ModifiedNarayanaInterlacingStatement P →
    Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G →
      Theorem41NonNestingRookStatement M

/-- The predicate-form induction route also accepts a computable recurrence
input. -/
theorem theorem41InductionRouteComputable_of_theorem41InductionRoute
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteStatement M P G) :
    Theorem41InductionRouteComputableStatement M P G := by
  intro h33 h34 hrec
  exact hroute h33 h34 (theorem35_of_theorem35Computable hrec)

/-- The computable-recursion induction route implies the predicate-form route. -/
theorem theorem41InductionRoute_of_theorem41InductionRouteComputable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteComputableStatement M P G) :
    Theorem41InductionRouteStatement M P G := by
  intro h33 h34 hrec
  exact hroute h33 h34 (theorem35Computable_of_theorem35 hrec)

/-- Predicate and computable forms of the Theorem 4.1 induction route are
equivalent. -/
theorem theorem41InductionRouteComputable_iff_theorem41InductionRoute
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) :
    Theorem41InductionRouteComputableStatement M P G ↔
      Theorem41InductionRouteStatement M P G :=
  ⟨theorem41InductionRoute_of_theorem41InductionRouteComputable,
    theorem41InductionRouteComputable_of_theorem41InductionRoute⟩

/-- Bundled Section 3 ingredients needed by the current Theorem 4.1 induction
interface. -/
structure Theorem41Section3Inputs
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop where
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaInterlacingStatement P
  recurrence : Theorem35GeneralizedSnakeRecurrenceStatement M P G

/-- Bundled Section 3 ingredients using the computable recurrence form. -/
structure Theorem41Section3ComputableInputs
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop where
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaInterlacingStatement P
  recurrence : Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G

/-- Bundled Section 3 ingredients using the shifted nonnegative-parameter
Lemma 3.4 form. -/
structure Theorem41Section3ShiftedInputs
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop where
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaShiftedInterlacingStatement P
  recurrence : Theorem35GeneralizedSnakeRecurrenceStatement M P G

/-- Bundled Section 3 ingredients using the shifted Lemma 3.4 form and the
computable recurrence form. -/
structure Theorem41Section3ComputableShiftedInputs
    (M : SnakeWord → ℝ[X]) (P G : ℕ → ℝ[X]) : Prop where
  lemma33 : Lemma33AuxiliaryGInterlacesStatement P G
  lemma34 : Lemma34ModifiedNarayanaShiftedInterlacingStatement P
  recurrence : Theorem35GeneralizedSnakeRecurrenceComputableStatement M P G

/-- Convert computable Section 3 inputs into the predicate-form bundle. -/
theorem theorem41Section3Inputs_of_computable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hinputs : Theorem41Section3ComputableInputs M P G) :
    Theorem41Section3Inputs M P G where
  lemma33 := hinputs.lemma33
  lemma34 := hinputs.lemma34
  recurrence := theorem35_of_theorem35Computable hinputs.recurrence

/-- Convert shifted Section 3 inputs into the paper-shaped bundle. -/
theorem theorem41Section3Inputs_of_shifted
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hinputs : Theorem41Section3ShiftedInputs M P G) :
    Theorem41Section3Inputs M P G where
  lemma33 := hinputs.lemma33
  lemma34 := lemma34ModifiedNarayanaInterlacing_of_shifted hinputs.lemma34
  recurrence := hinputs.recurrence

/-- Convert computable shifted Section 3 inputs into the paper-shaped
computable bundle. -/
theorem theorem41Section3ComputableInputs_of_shifted
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hinputs : Theorem41Section3ComputableShiftedInputs M P G) :
    Theorem41Section3ComputableInputs M P G where
  lemma33 := hinputs.lemma33
  lemma34 := lemma34ModifiedNarayanaInterlacing_of_shifted hinputs.lemma34
  recurrence := hinputs.recurrence

/-- Convert computable shifted Section 3 inputs into the predicate-recurrence
shifted bundle. -/
theorem theorem41Section3ShiftedInputs_of_computable
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hinputs : Theorem41Section3ComputableShiftedInputs M P G) :
    Theorem41Section3ShiftedInputs M P G where
  lemma33 := hinputs.lemma33
  lemma34 := hinputs.lemma34
  recurrence := theorem35_of_theorem35Computable hinputs.recurrence

/-- Feed the bundled Section 3 ingredients into the abstract Theorem 4.1
induction route. -/
theorem theorem41_of_section3Inputs
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteStatement M P G)
    (hinputs : Theorem41Section3Inputs M P G) :
    Theorem41NonNestingRookStatement M :=
  hroute hinputs.lemma33 hinputs.lemma34 hinputs.recurrence

/-- Feed computable Section 3 ingredients into the abstract Theorem 4.1
induction route. -/
theorem theorem41_of_section3ComputableInputs
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteStatement M P G)
    (hinputs : Theorem41Section3ComputableInputs M P G) :
    Theorem41NonNestingRookStatement M :=
  theorem41_of_section3Inputs hroute
    (theorem41Section3Inputs_of_computable hinputs)

/-- Feed shifted Section 3 ingredients into the abstract Theorem 4.1 induction
route. -/
theorem theorem41_of_section3ShiftedInputs
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteStatement M P G)
    (hinputs : Theorem41Section3ShiftedInputs M P G) :
    Theorem41NonNestingRookStatement M :=
  theorem41_of_section3Inputs hroute
    (theorem41Section3Inputs_of_shifted hinputs)

/-- Feed computable shifted Section 3 ingredients into the abstract Theorem
4.1 induction route. -/
theorem theorem41_of_section3ComputableShiftedInputs
    {M : SnakeWord → ℝ[X]} {P G : ℕ → ℝ[X]}
    (hroute : Theorem41InductionRouteStatement M P G)
    (hinputs : Theorem41Section3ComputableShiftedInputs M P G) :
    Theorem41NonNestingRookStatement M :=
  theorem41_of_section3ComputableInputs hroute
    (theorem41Section3ComputableInputs_of_shifted hinputs)

end GeneralizedSnakePosets
end RealRooted
