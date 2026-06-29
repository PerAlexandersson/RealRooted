import Mathlib

/-!
# Challenge: human-auditable theorem statements

Imports only Mathlib. To audit: read this file and check that each statement
says what it claims. A passing comparator run then guarantees the RealRooted
library proves these statements using only `{propext, Quot.sound, Classical.choice}`.
-/

open Polynomial

section

namespace List

variable {α : Type*} (r : α → α → Prop)

/-- `l₁` `r`-interleaves `l₂` if the elements of `l₁` are sandwiched between
consecutive elements of `l₂` under `r`. -/
inductive Interleaves : List α → List α → Prop
  | nil_nil : Interleaves [] []
  | nil_singleton (a : α) : Interleaves [] [a]
  | cons_symm ⦃l₁ l₂ : List α⦄ ⦃b : α⦄ (hl : Interleaves l₁ (b :: l₂)) ⦃a : α⦄ (hab : r a b) :
      Interleaves (b :: l₂) (a :: l₁)

end List

end

noncomputable section

namespace Comparator

/-! ## Auxiliary list predicates (used by `Prec`) -/

/-- Differ-by-1 root interleaving of sorted lists. -/
def ListInterlaces : List ℝ → List ℝ → Prop
  | [], []           => True
  | [], [_]          => True
  | s :: ss, r₁ :: r₂ :: rs => r₁ ≤ s ∧ s ≤ r₂ ∧ ListInterlaces ss (r₂ :: rs)
  | _, _             => False

/-- Same-degree root interleaving of sorted lists. -/
def ListAlternates : List ℝ → List ℝ → Prop
  | [], []       => True
  | s :: ss, r :: rs => s ≤ r ∧ ListInterlaces ss (r :: rs)
  | _, _         => False

/-! ## Core polynomial predicates -/

/-- Non-negative coefficients. -/
def HasNonnegCoeffs (p : ℝ[X]) : Prop := ∀ n, 0 ≤ p.coeff n

/-- Positive leading coefficient. -/
def HasPosLeadingCoeff (p : ℝ[X]) : Prop := 0 < p.leadingCoeff

/-- `Prec f g` ("f precedes g", written f ≪ g): both are nonzero and
real-rooted, and the roots of `f` interleave into those of `g` (either
differ-by-1 or same-degree). -/
def Prec (f g : ℝ[X]) : Prop :=
  (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits) ∧
  ∃ (ss rs : List ℝ),
    ss.Pairwise (· ≤ ·) ∧ rs.Pairwise (· ≤ ·) ∧
    (↑ss : Multiset ℝ) = f.roots ∧ (↑rs : Multiset ℝ) = g.roots ∧
    ((ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
     (ss.length = rs.length ∧ ListAlternates ss rs))

/-- Strict same-degree interlacing: both polynomials are nonzero and
real-rooted with the same degree, and the roots of `p` strictly interleave
those of `q`. -/
def StrictPrecSameDegree (p q : ℝ[X]) : Prop :=
  (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits) ∧ p.natDegree = q.natDegree ∧
    List.Interleaves (· > ·) (p.roots.sort (· ≤ ·)).reverse (q.roots.sort (· ≤ ·)).reverse

/-! ## 1. Brändén–Solus Theorem 2.6 -/

/-- Brändén–Solus I_d-transform: `I_d(p)(x) = x^d · p(1/x)`, i.e. `p.reflect d`. -/
def IdTransform (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  p.reflect d

/-- Brändén–Solus R_d-transform: `R_d(p)(x) = (-1)^d · p(-1 - x)`. -/
def RdTransform (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C (((-1 : ℝ) ^ d)) * p.comp (-X - 1)

/-- The f-polynomial transform from Brändén–Solus (2.2):
`f_d(h)(x) = Σ_{k=0}^{d} h_k x^k (x+1)^{d-k}`. -/
def fPolynomial (d : ℕ) (h : ℝ[X]) : ℝ[X] :=
  Finset.sum (Finset.range (d + 1))
    (fun k => C (h.coeff k) * X ^ k * (X + 1) ^ (d - k))

/-- Predicate for the I_d-decomposition `p = a + X·b` with palindrome conditions. -/
def IsIdDecomposition (d : ℕ) (p a b : ℝ[X]) : Prop :=
  p = a + X * b ∧
  a.natDegree ≤ d ∧
  b.natDegree ≤ d - 1 ∧
  IdTransform d a = a ∧
  IdTransform (d - 1) b = b

/-- Brändén–Solus Theorem 2.6: four equivalent characterisations of interlacing
for a polynomial with a nonneg-coefficient I_d-decomposition. -/
theorem brandenSolusTheorem26 :
    ∀ {d : ℕ} {p a b : ℝ[X]},
      p.natDegree ≤ d →
      IsIdDecomposition d p a b →
      HasNonnegCoeffs a →
      HasNonnegCoeffs b →
      a ≠ 0 →
      b ≠ 0 →
      (Prec b a ↔ Prec a p) ∧
      (Prec a p ↔ Prec b p) ∧
      (Prec b p ↔ Prec (IdTransform d p) p) ∧
      (Prec (IdTransform d p) p ↔
        Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p)) := by
  sorry

/-! ## 2. Aissen–Schoenberg–Whitney (reverse direction) -/

/-- Lower-triangular Toeplitz matrix of a sequence. -/
def toeplitz (a : ℕ → ℝ) : Matrix ℕ ℕ ℝ :=
  .of fun i j ↦ if j ≤ i then a (i - j) else 0

/-- A matrix is totally nonnegative if all finite minors have nonnegative
determinant. -/
def matIsTotallyNonneg (M : Matrix ℕ ℕ ℝ) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃rows cols : Fin n → ℕ⦄,
    StrictMono rows → StrictMono cols → 0 ≤ (M.submatrix rows cols).det

/-- A sequence is Pólya-frequency if all finite minors of its Toeplitz matrix
are nonnegative. -/
def IsPolyaFreqSeq (a : ℕ → ℝ) : Prop :=
  matIsTotallyNonneg (toeplitz a)

/-- ASW reverse: a real-rooted polynomial with nonneg coefficients and
nonpositive roots has a Pólya-frequency coefficient sequence. -/
theorem aissenSchoenbergWhitney_reverse {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p)
    (hsplits : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    IsPolyaFreqSeq (fun n ↦ p.coeff n) := by
  sorry

/-! ## 3. Bezoutian characterisation of strict same-degree interlacing -/

/-- The `(i,j)` coefficient of the Bezoutian
`(p(X) q(Y) - p(Y) q(X)) / (X - Y)`. -/
def bezoutEntry (p q : ℝ[X]) (i j : ℕ) : ℝ :=
  Finset.sum (Finset.range (min i j + 1)) fun k ↦
    p.coeff (i + j + 1 - k) * q.coeff k -
      q.coeff (i + j + 1 - k) * p.coeff k

/-- The `n × n` Bezout matrix attached to two polynomials. -/
def bezoutMatrix (n : ℕ) (p q : ℝ[X]) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ bezoutEntry p q i.1 j.1

/-- Strict same-degree interlacing is equivalent to positive definiteness of
the Bezout matrix (with arguments swapped: `bezoutMatrix n q p`). -/
theorem strictPrecSameDegree_iff_bezoutMatrix_posDef
    {p q : ℝ[X]} {n : ℕ}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n) :
    StrictPrecSameDegree p q ↔ (bezoutMatrix n q p).PosDef := by
  sorry

end Comparator

end
