import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort

/-!
# Real-rootedness and interlacing of polynomials

This file contains the foundational definitions for real-rootedness,
interlacing, proper position, and Sturm sequences of univariate real
polynomials.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A nonzero polynomial `p ∈ ℝ[X]` is **real-rooted** if
    the number of real roots (counted with multiplicity) equals its degree. -/
def IsRealRooted (p : ℝ[X]) : Prop :=
  p ≠ 0 ∧ p.roots.card = p.natDegree

/-- Zero-aware real-rootedness.  This is the convention often used for
closure statements, while `IsRealRooted` remains the strict nonzero predicate
used by root-list and interlacing proofs. -/
def IsRealRootedOrZero (p : ℝ[X]) : Prop :=
  p = 0 ∨ IsRealRooted p

lemma IsRealRooted.toOrZero {p : ℝ[X]} (hp : IsRealRooted p) :
    IsRealRootedOrZero p :=
  Or.inr hp

lemma isRealRootedOrZero_zero : IsRealRootedOrZero (0 : ℝ[X]) :=
  Or.inl rfl

lemma IsRealRootedOrZero.of_ne_zero {p : ℝ[X]}
    (hp : IsRealRootedOrZero p) (hp0 : p ≠ 0) :
    IsRealRooted p := by
  rcases hp with hzero | hrr
  · exact False.elim (hp0 hzero)
  · exact hrr

/-! ## Root interleaving predicates on sorted lists -/

/-- **Differ-by-1 interleaving**: `ss` (length n−1) interleaves into `rs` (length n).
    Pattern: r₁ ≤ s₁ ≤ r₂ ≤ s₂ ≤ … ≤ sₙ₋₁ ≤ rₙ.
    The last element of `rs` is the rightmost root. -/
def ListInterlaces : List ℝ → List ℝ → Prop
  | [], [] => True
  | [], [_] => True
  | s :: ss, r₁ :: r₂ :: rs => r₁ ≤ s ∧ s ≤ r₂ ∧ ListInterlaces ss (r₂ :: rs)
  | _, _ => False

/-- **Same-degree interleaving**: `ss` (length n) alternates with `rs` (length n).
    Pattern: s₁ ≤ r₁ ≤ s₂ ≤ r₂ ≤ … ≤ sₙ ≤ rₙ.
    The last element of `rs` is the rightmost root. -/
def ListAlternates : List ℝ → List ℝ → Prop
  | [], [] => True
  | s :: ss, r :: rs => s ≤ r ∧ ListInterlaces ss (r :: rs)
  | _, _ => False

/-! ## Polynomial interlacing -/

/-- `f ≪ g` (**f is interlaced by g**): both real-rooted, `g` has the rightmost root,
    and either:
    - **differ-by-1**: `deg f + 1 = deg g`, roots satisfy `ListInterlaces`
    - **same-degree**: `deg f = deg g`, roots satisfy `ListAlternates`

    Notation: we write `Prec f g` for `f ≪ g`. -/
def Prec (f g : ℝ[X]) : Prop :=
  IsRealRooted f ∧ IsRealRooted g ∧
  ∃ (ss rs : List ℝ),
    ss.Pairwise (· ≤ ·) ∧ rs.Pairwise (· ≤ ·) ∧
    (↑ss : Multiset ℝ) = f.roots ∧ (↑rs : Multiset ℝ) = g.roots ∧
    ((ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
     (ss.length = rs.length ∧ ListAlternates ss rs))

/-- Relaxed interlacing convention used in some recursive arguments:
`Prec0 f g` holds if either side is zero, or if `Prec f g` holds in the
strict nonzero sense. -/
def Prec0 (f g : ℝ[X]) : Prop :=
  f = 0 ∨ g = 0 ∨ Prec f g

/-- Backward-compatible alias: differ-by-1 interlacing. -/
def Interlaces (g f : ℝ[X]) : Prop :=
  IsRealRooted f ∧ IsRealRooted g ∧
  g.natDegree + 1 = f.natDegree ∧
  ∃ (rs ss : List ℝ),
    rs.Pairwise (· ≤ ·) ∧ ss.Pairwise (· ≤ ·) ∧
    (↑rs : Multiset ℝ) = f.roots ∧
    (↑ss : Multiset ℝ) = g.roots ∧
    ListInterlaces ss rs

/-- A **Sturm sequence** is a list of polynomials where each consecutive
    pair interlaces (differ-by-1). -/
def IsSturmSeq : List ℝ[X] → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => Interlaces q p ∧ IsSturmSeq (q :: rest)

/-- A **generalized Sturm sequence** is a list of polynomials where each
    consecutive pair satisfies the weak interlacing relation `≪`, i.e. `Prec`.

    This allows either differ-by-1 interlacing or same-degree alternation at
    each step. -/
def IsGeneralizedSturmSeq : List ℝ[X] → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => Prec q p ∧ IsGeneralizedSturmSeq (q :: rest)

/-! ## Interlaces → Prec -/

lemma Interlaces.toPrec {g f : ℝ[X]} (h : Interlaces g f) : Prec g f := by
  obtain ⟨hf, hg, hdeg, rs, ss, hrs, hss, hrs_eq, hss_eq, hint⟩ := h
  refine ⟨hg, hf, ss, rs, hss, hrs, hss_eq, hrs_eq, Or.inl ⟨?_, hint⟩⟩
  have : ss.length = g.natDegree := by
    rw [← Multiset.coe_card, hss_eq, hg.2]
  have : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  omega

lemma Prec.toInterlaces {g f : ℝ[X]} (h : Prec g f)
    (hdeg : g.natDegree + 1 = f.natDegree) : Interlaces g f := by
  rcases h with ⟨hg, hf, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  refine ⟨hf, hg, hdeg, rs, ss, hrs, hss, hrs_eq, hss_eq, ?_⟩
  have hss_len : ss.length = g.natDegree := by
    rw [← Multiset.coe_card, hss_eq, hg.2]
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  rcases hshape with ⟨_, hint⟩ | ⟨hlen, _⟩
  · exact hint
  · exfalso
    omega

lemma IsSturmSeq.toGeneralizedSturmSeq {ps : List ℝ[X]} (h : IsSturmSeq ps) :
    IsGeneralizedSturmSeq ps := by
  induction ps with
  | nil =>
      simp [IsGeneralizedSturmSeq]
  | cons p ps ih =>
      cases ps with
      | nil =>
          simp [IsGeneralizedSturmSeq]
      | cons q rest =>
          rcases h with ⟨hpq, hrest⟩
          exact ⟨hpq.toPrec, ih hrest⟩

-- ============================================================
-- Basic lemmas
-- ============================================================

lemma isRealRooted_of_deg_zero {p : ℝ[X]} (hp : p ≠ 0) (hdeg : p.natDegree = 0) :
    IsRealRooted p := by
  refine ⟨hp, ?_⟩
  have : p.roots.card ≤ p.natDegree := card_roots' p
  omega

lemma Prec.toPrec0 {f g : ℝ[X]} (h : Prec f g) : Prec0 f g :=
  Or.inr (Or.inr h)

lemma Prec0.toPrec_of_ne {f g : ℝ[X]} (h : Prec0 f g)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    Prec f g := by
  rcases h with hf0 | hg0 | hprec
  · exact (hf hf0).elim
  · exact (hg hg0).elim
  · exact hprec

lemma prec0_zero_left (f : ℝ[X]) : Prec0 0 f :=
  Or.inl rfl

lemma prec0_zero_right (f : ℝ[X]) : Prec0 f 0 :=
  Or.inr (Or.inl rfl)

lemma prec0_zero_zero : Prec0 (0 : ℝ[X]) 0 :=
  prec0_zero_left 0

/-- The product of two real-rooted polynomials is real-rooted. -/
lemma isRealRooted_mul {p q : ℝ[X]} (hp : IsRealRooted p) (hq : IsRealRooted q) :
    IsRealRooted (p * q) := by
  refine ⟨mul_ne_zero hp.1 hq.1, ?_⟩
  rw [natDegree_mul hp.1 hq.1, roots_mul (mul_ne_zero hp.1 hq.1), Multiset.card_add]
  exact congr_arg₂ (· + ·) hp.2 hq.2

/-- Non-negative coefficients. -/
def HasNonnegCoeffs (p : ℝ[X]) : Prop := ∀ n, 0 ≤ p.coeff n

/-- Positive leading coefficient. -/
def HasPosLeadingCoeff (p : ℝ[X]) : Prop := 0 < p.leadingCoeff

/-! ## Elementary interval inequalities -/

lemma quadratic_nonneg_on_unit_interval_of_coeffs_nonneg
    {A B C β : ℝ}
    (hβ0 : 0 ≤ β) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ A + B * β + C * β ^ 2 := by
  have hBβ : 0 ≤ B * β := mul_nonneg hB hβ0
  have hβ2 : 0 ≤ β ^ 2 := sq_nonneg β
  have hCβ2 : 0 ≤ C * β ^ 2 := mul_nonneg hC hβ2
  nlinarith

lemma quadratic_nonneg_on_unit_interval_of_endpoint_nonneg_of_c_nonneg
    {A B C β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hA : 0 ≤ A) (hEnd : 0 ≤ A + B + C)
    (hC : 0 ≤ C) (hBneg : B < 0 → C = 0) :
    0 ≤ A + B * β + C * β ^ 2 := by
  by_cases hB : 0 ≤ B
  · exact quadratic_nonneg_on_unit_interval_of_coeffs_nonneg hβ0 hA hB hC
  · have hBlt : B < 0 := lt_of_not_ge hB
    have hC0 : C = 0 := hBneg hBlt
    have hEnd' : 0 ≤ A + B := by simpa [hC0] using hEnd
    have hlin : 0 ≤ (1 - β) * A + β * (A + B) := by
      exact add_nonneg (mul_nonneg (by linarith) hA) (mul_nonneg hβ0 hEnd')
    have hEq : A + B * β + C * β ^ 2 = (1 - β) * A + β * (A + B) := by
      rw [hC0]
      ring
    simpa [hEq]

lemma quadratic_nonneg_on_unit_interval_of_endpoint_nonneg_of_vertex_or_discriminant
    {A B C β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hA : 0 ≤ A) (hEnd : 0 ≤ A + B + C)
    (hC : 0 ≤ C)
    (hBneg : B < 0 → 2 * C ≤ -B ∨ B ^ 2 ≤ 4 * C * A) :
    0 ≤ A + B * β + C * β ^ 2 := by
  by_cases hB : 0 ≤ B
  · exact quadratic_nonneg_on_unit_interval_of_coeffs_nonneg hβ0 hA hB hC
  · have hBlt : B < 0 := lt_of_not_ge hB
    rcases hBneg hBlt with hvertex | hdisc
    · have hβm1 : β - 1 ≤ 0 := by linarith
      have hβp1 : β + 1 ≤ 2 := by linarith
      have hCβp1 : C * (β + 1) ≤ C * 2 :=
        mul_le_mul_of_nonneg_left hβp1 hC
      have hfactor : B + C * (β + 1) ≤ 0 := by
        nlinarith
      have hprod : 0 ≤ (β - 1) * (B + C * (β + 1)) :=
        mul_nonneg_of_nonpos_of_nonpos hβm1 hfactor
      have hEq :
          A + B * β + C * β ^ 2 =
            (A + B + C) + (β - 1) * (B + C * (β + 1)) := by
        ring
      rw [hEq]
      exact add_nonneg hEnd hprod
    · have hCpos : 0 < C := by
        refine lt_of_le_of_ne hC ?_
        intro hC0
        have hBsq_nonpos : B ^ 2 ≤ 0 := by
          nlinarith
        have hBne : B ≠ 0 := ne_of_lt hBlt
        have hBsq_pos : 0 < B ^ 2 := sq_pos_of_ne_zero hBne
        nlinarith
      have hdisc_nonneg : 0 ≤ 4 * C * A - B ^ 2 := by
        nlinarith
      have hsquare : 0 ≤ (2 * C * β + B) ^ 2 := sq_nonneg _
      have hmul : 0 ≤ 4 * C * (A + B * β + C * β ^ 2) := by
        nlinarith
      nlinarith [hCpos, hmul]

end RealRooted
