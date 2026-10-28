module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.BandedHessenberg
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-!
# Tetradiagonal factorization criteria

This file formalizes the zero-aware canonical split used in the nonnegative
bidiagonal factorization of a tetradiagonal Hessenberg matrix.  It also gives
the four-term polynomial recurrence and identifies it with the characteristic
polynomial of the corresponding matrix.

The split criterion follows Branquinho--Foulquie-Moreno--Manas, with the zero
branches made explicit as required by RealRooted issue #2102.
-/

@[expose] public section

namespace RealRooted

noncomputable section

/-- The second factor in the canonical split.  Index zero represents the
paper's index one.  A zero denominator starts a new block. -/
def canonicalSecondFactor (ell m : ℕ → ℝ) : ℕ → ℝ
  | 0 => ell 0
  | n + 1 =>
      if canonicalSecondFactor ell m n = 0 then ell (n + 1)
      else ell (n + 1) - m (n + 1) / canonicalSecondFactor ell m n

/-- The first factor paired with `canonicalSecondFactor`. -/
def canonicalFirstFactor (ell m : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      if canonicalSecondFactor ell m n = 0 then 0
      else m (n + 1) / canonicalSecondFactor ell m n

/-- Nonnegative solutions of the scalar equations for splitting a unit lower
matrix with two subdiagonals into two unit lower-bidiagonal matrices. -/
def IsNonnegativeLowerSplit (ell m a b : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ a n) ∧
    (∀ n, 0 ≤ b n) ∧
      (∀ n, a n + b n = ell n) ∧
        ∀ n, a (n + 1) * b n = m (n + 1)

/-- The canonical lower split succeeds exactly when its second-factor entries
are nonnegative and a zero entry is never followed by a positive second
subdiagonal entry. -/
def CanonicalLowerSplitSucceeds (ell m : ℕ → ℝ) : Prop :=
  ∀ n, 0 ≤ canonicalSecondFactor ell m n ∧
    (canonicalSecondFactor ell m n = 0 → m (n + 1) = 0)

@[simp] theorem canonicalSecondFactor_zero (ell m : ℕ → ℝ) :
    canonicalSecondFactor ell m 0 = ell 0 :=
  rfl

@[simp] theorem canonicalSecondFactor_succ (ell m : ℕ → ℝ) (n : ℕ) :
    canonicalSecondFactor ell m (n + 1) =
      if canonicalSecondFactor ell m n = 0 then ell (n + 1)
      else ell (n + 1) - m (n + 1) / canonicalSecondFactor ell m n :=
  rfl

@[simp] theorem canonicalFirstFactor_zero (ell m : ℕ → ℝ) :
    canonicalFirstFactor ell m 0 = 0 :=
  rfl

@[simp] theorem canonicalFirstFactor_succ (ell m : ℕ → ℝ) (n : ℕ) :
    canonicalFirstFactor ell m (n + 1) =
      if canonicalSecondFactor ell m n = 0 then 0
      else m (n + 1) / canonicalSecondFactor ell m n :=
  rfl


private theorem canonicalSecondFactor_properties_of_split
    {ell m a b : ℕ → ℝ} (hm : ∀ n, 0 ≤ m n)
    (h : IsNonnegativeLowerSplit ell m a b) (n : ℕ) :
    0 ≤ canonicalSecondFactor ell m n ∧
      b n ≤ canonicalSecondFactor ell m n ∧
        (canonicalSecondFactor ell m n = 0 → m (n + 1) = 0) := by
  rcases h with ⟨ha, hb, hsum, hprod⟩
  induction n with
  | zero =>
      rw [canonicalSecondFactor_zero, ← hsum 0]
      refine ⟨add_nonneg (ha 0) (hb 0), le_add_of_nonneg_left (ha 0), ?_⟩
      intro hz
      have hb0 : b 0 = 0 := by nlinarith [ha 0, hb 0]
      rw [← hprod 0, hb0, mul_zero]
  | succ n ih =>
      rcases ih with ⟨hcanon, hmax, hcompat⟩
      rw [canonicalSecondFactor_succ]
      by_cases hzero : canonicalSecondFactor ell m n = 0
      · simp only [hzero, ↓reduceIte]
        have hmzero : m (n + 1) = 0 := hcompat hzero
        have hbzero : b n = 0 := by
          have := hb n
          nlinarith
        refine ⟨?_, ?_, ?_⟩
        · rw [← hsum (n + 1)]
          exact add_nonneg (ha (n + 1)) (hb (n + 1))
        · rw [← hsum (n + 1)]
          exact le_add_of_nonneg_left (ha (n + 1))
        · intro hell
          have hbnext : b (n + 1) = 0 := by
            rw [← hsum (n + 1)] at hell
            nlinarith [ha (n + 1), hb (n + 1)]
          rw [← hprod (n + 1), hbnext, mul_zero]
      · simp only [hzero, ↓reduceIte]
        have hcanonpos : 0 < canonicalSecondFactor ell m n :=
          lt_of_le_of_ne hcanon (Ne.symm hzero)
        by_cases hbzero : b n = 0
        · have hmzero : m (n + 1) = 0 := by
            rw [← hprod n, hbzero, mul_zero]
          rw [hmzero, zero_div, sub_zero]
          refine ⟨?_, ?_, ?_⟩
          · rw [← hsum (n + 1)]
            exact add_nonneg (ha (n + 1)) (hb (n + 1))
          · rw [← hsum (n + 1)]
            exact le_add_of_nonneg_left (ha (n + 1))
          · intro hell
            have hbnext : b (n + 1) = 0 := by
              rw [← hsum (n + 1)] at hell
              nlinarith [ha (n + 1), hb (n + 1)]
            rw [← hprod (n + 1), hbnext, mul_zero]
        · have hbpos : 0 < b n := lt_of_le_of_ne (hb n) (Ne.symm hbzero)
          have haeq : a (n + 1) = m (n + 1) / b n := by
            apply (eq_div_iff hbzero).2
            exact hprod n
          have hdiv :
              m (n + 1) / canonicalSecondFactor ell m n ≤ m (n + 1) / b n :=
            div_le_div_of_nonneg_left (hm (n + 1)) hbpos hmax
          have hbform : b (n + 1) = ell (n + 1) - m (n + 1) / b n := by
            rw [← haeq, ← hsum (n + 1)]
            ring
          have hnextmax :
              b (n + 1) ≤
                ell (n + 1) - m (n + 1) / canonicalSecondFactor ell m n := by
            rw [hbform]
            linarith
          refine ⟨le_trans (hb (n + 1)) hnextmax, hnextmax, ?_⟩
          intro hnextzero
          have hbnext : b (n + 1) = 0 := by
            nlinarith [hb (n + 1)]
          rw [← hprod (n + 1), hbnext, mul_zero]

/-- Whenever any nonnegative lower split exists, the canonical second factor
is coordinatewise maximal.  This includes all zero-denominator branches. -/
theorem canonicalSecondFactor_maximal {ell m a b : ℕ → ℝ}
    (hm : ∀ n, 0 ≤ m n) (h : IsNonnegativeLowerSplit ell m a b) (n : ℕ) :
    b n ≤ canonicalSecondFactor ell m n :=
  (canonicalSecondFactor_properties_of_split hm h n).2.1

/-- A successful canonical construction supplies a nonnegative lower split. -/
theorem isNonnegativeLowerSplit_canonical {ell m : ℕ → ℝ}
    (hm : ∀ n, 0 ≤ m n) (hsuccess : CanonicalLowerSplitSucceeds ell m) :
    IsNonnegativeLowerSplit ell m
      (canonicalFirstFactor ell m) (canonicalSecondFactor ell m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => simp
    | succ n =>
        rw [canonicalFirstFactor_succ]
        by_cases hzero : canonicalSecondFactor ell m n = 0
        · simp [hzero]
        · simp only [hzero, ↓reduceIte]
          exact div_nonneg (hm (n + 1)) (hsuccess n).1
  · exact fun n => (hsuccess n).1
  · intro n
    cases n with
    | zero => simp
    | succ n =>
        rw [canonicalFirstFactor_succ, canonicalSecondFactor_succ]
        split_ifs <;> ring
  · intro n
    rw [canonicalFirstFactor_succ]
    by_cases hzero : canonicalSecondFactor ell m n = 0
    · simp only [hzero, ↓reduceIte, zero_mul, (hsuccess n).2 hzero]
    · simp only [hzero, ↓reduceIte, div_mul_cancel₀ _ hzero]

/-- The zero-aware canonical algorithm succeeds if and only if a nonnegative
split exists.  This is the exact scalar criterion behind issue #2102. -/
theorem canonicalLowerSplitSucceeds_iff {ell m : ℕ → ℝ}
    (hm : ∀ n, 0 ≤ m n) :
    CanonicalLowerSplitSucceeds ell m ↔
      ∃ a b, IsNonnegativeLowerSplit ell m a b := by
  constructor
  · intro h
    exact ⟨canonicalFirstFactor ell m, canonicalSecondFactor ell m,
      isNonnegativeLowerSplit_canonical hm h⟩
  · rintro ⟨a, b, h⟩ n
    exact ⟨(canonicalSecondFactor_properties_of_split hm h n).1,
      (canonicalSecondFactor_properties_of_split hm h n).2.2⟩

/-- A positive lower bound satisfying the continued-fraction inequality forces
the canonical split to succeed and keeps every canonical pivot above that
bound. -/
theorem canonicalLowerSplitSucceeds_of_lower_bound {ell m v : ℕ → ℝ}
    (hm : ∀ n, 0 ≤ m n) (hv : ∀ n, 0 < v n) (hzero : v 0 ≤ ell 0)
    (hsucc : ∀ n, v (n + 1) + m (n + 1) / v n ≤ ell (n + 1)) :
    CanonicalLowerSplitSucceeds ell m ∧
      ∀ n, v n ≤ canonicalSecondFactor ell m n := by
  have hbound : ∀ n, v n ≤ canonicalSecondFactor ell m n := by
    intro n
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
        have hcanonpos : 0 < canonicalSecondFactor ell m n :=
          lt_of_lt_of_le (hv n) ih
        simp only [canonicalSecondFactor_succ, hcanonpos.ne', ↓reduceIte]
        have hdiv :
            m (n + 1) / canonicalSecondFactor ell m n ≤ m (n + 1) / v n :=
          div_le_div_of_nonneg_left (hm (n + 1)) (hv n) ih
        linarith [hsucc n]
  refine ⟨?_, hbound⟩
  intro n
  refine ⟨le_trans (hv n).le (hbound n), ?_⟩
  intro hzero'
  have := hv n
  have := hbound n
  linarith

/-- The positive-pivot elimination data for a tetradiagonal recurrence.
Indices of `ell` and `m` are shifted down by one: `ell 0` is the paper's
`ell_1`, and `m 0 = 0` is its `m_1`. -/
def IsPositivePivotReconstruction (d s t ell m u : ℕ → ℝ) : Prop :=
  (∀ n, 0 < u n) ∧
    u 0 = d 0 ∧
      m 0 = 0 ∧
        (∀ n, m (n + 1) = t (n + 2) / u n) ∧
          (∀ n, ell n = (s (n + 1) - m n) / u n) ∧
            ∀ n, u (n + 1) = d (n + 1) - ell n

/-- Positive-pivot reconstruction gives the coefficient equations for the
lower-two-band times upper-bidiagonal factorization. -/
theorem positivePivotReconstruction_coefficients {d s t ell m u : ℕ → ℝ}
    (h : IsPositivePivotReconstruction d s t ell m u) :
    d 0 = u 0 ∧
      m 0 = 0 ∧
        (∀ n, d (n + 1) = u (n + 1) + ell n) ∧
          (∀ n, s (n + 1) = ell n * u n + m n) ∧
            ∀ n, t (n + 2) = m (n + 1) * u n := by
  rcases h with ⟨hpos, hu0, hm0, hm, hell, hu⟩
  refine ⟨hu0.symm, hm0, ?_, ?_, ?_⟩
  · intro n
    rw [hu n]
    ring
  · intro n
    have hmul := (eq_div_iff (hpos n).ne').mp (hell n)
    linarith
  · intro n
    have hmul := (eq_div_iff (hpos n).ne').mp (hm n)
    exact hmul.symm

/-- Positive-pivot reconstruction is unique whenever it exists.  Thus the
coefficient test does not depend on guessed factor weights. -/
theorem positivePivotReconstruction_unique {d s t ell m u ell' m' u' : ℕ → ℝ}
    (h : IsPositivePivotReconstruction d s t ell m u)
    (h' : IsPositivePivotReconstruction d s t ell' m' u') :
    u = u' ∧ ell = ell' ∧ m = m' := by
  rcases h with ⟨hpos, hu0, hm0, hm, hell, hu⟩
  rcases h' with ⟨hpos', hu0', hm0', hm', hell', hu'⟩
  have hall : ∀ n, u n = u' n ∧ ell n = ell' n ∧ m n = m' n := by
    intro n
    induction n with
    | zero =>
        have heu : u 0 = u' 0 := hu0.trans hu0'.symm
        have hem : m 0 = m' 0 := hm0.trans hm0'.symm
        refine ⟨heu, ?_, hem⟩
        rw [hell 0, hell' 0, heu, hem]
    | succ n ih =>
        have hem : m (n + 1) = m' (n + 1) := by
          rw [hm n, hm' n, ih.1]
        have heu : u (n + 1) = u' (n + 1) := by
          rw [hu n, hu' n, ih.2.1]
        refine ⟨heu, ?_, hem⟩
        rw [hell (n + 1), hell' (n + 1), heu, hem]
  refine ⟨funext fun n => (hall n).1, ?_, funext fun n => (hall n).2.2⟩
  exact funext fun n => (hall n).2.1

/-- The tetradiagonal lower-Hessenberg matrix attached to three coefficient
sequences.  Its superdiagonal entries are one. -/
def tetradiagonalMatrix (d s t : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.bandedLowerHessenberg d s t 1 n

/-- The monic polynomial sequence defined by the four-term recurrence from
RealRooted issue #2102. -/
def tetradiagonalPolynomial (d s t : ℕ → ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X - Polynomial.C (d 0)
  | 2 =>
      (Polynomial.X - Polynomial.C (d 1)) *
          (Polynomial.X - Polynomial.C (d 0)) -
        Polynomial.C (s 1)
  | n + 3 =>
      (Polynomial.X - Polynomial.C (d (n + 2))) *
          tetradiagonalPolynomial d s t (n + 2) -
        Polynomial.C (s (n + 2)) * tetradiagonalPolynomial d s t (n + 1) -
          Polynomial.C (t (n + 2)) * tetradiagonalPolynomial d s t n

private theorem tetradiagonalMatrix_charmatrix (d s t : ℕ → ℝ) (n : ℕ) :
    (tetradiagonalMatrix d s t n).charmatrix =
      Matrix.bandedLowerHessenberg
        (fun i => Polynomial.X - Polynomial.C (d i))
        (fun i => -Polynomial.C (s i))
        (fun i => -Polynomial.C (t i)) (-1) n := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [tetradiagonalMatrix]
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [tetradiagonalMatrix, Matrix.charmatrix_apply,
      Matrix.bandedLowerHessenberg_apply, hval, ↓reduceIte]
    split_ifs <;> simp_all

/-- Characteristic polynomials of leading tetradiagonal sections satisfy the
four-term recurrence, including all coefficient signs. -/
theorem tetradiagonalMatrix_charpoly_add_three (d s t : ℕ → ℝ) (n : ℕ) :
    (tetradiagonalMatrix d s t (n + 3)).charpoly =
      (Polynomial.X - Polynomial.C (d (n + 2))) *
          (tetradiagonalMatrix d s t (n + 2)).charpoly -
        Polynomial.C (s (n + 2)) *
          (tetradiagonalMatrix d s t (n + 1)).charpoly -
            Polynomial.C (t (n + 2)) *
              (tetradiagonalMatrix d s t n).charpoly := by
  simp only [Matrix.charpoly]
  rw [tetradiagonalMatrix_charmatrix d s t (n + 3),
    tetradiagonalMatrix_charmatrix d s t (n + 2),
    tetradiagonalMatrix_charmatrix d s t (n + 1),
    tetradiagonalMatrix_charmatrix d s t n]
  rw [Matrix.det_bandedLowerHessenberg_add_three]
  ring

/-- The four-term recurrence is the characteristic polynomial of the
corresponding tetradiagonal Hessenberg section, in dimensions zero, one, two,
and uniformly thereafter. -/
theorem tetradiagonalPolynomial_eq_charpoly (d s t : ℕ → ℝ) (n : ℕ) :
    tetradiagonalPolynomial d s t n = (tetradiagonalMatrix d s t n).charpoly := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 =>
          rw [tetradiagonalPolynomial, Matrix.charpoly,
            tetradiagonalMatrix_charmatrix]
          simp [Matrix.bandedLowerHessenberg]
      | 1 =>
          rw [tetradiagonalPolynomial, Matrix.charpoly,
            tetradiagonalMatrix_charmatrix]
          simp [Matrix.bandedLowerHessenberg]
      | 2 =>
          rw [tetradiagonalPolynomial, Matrix.charpoly,
            tetradiagonalMatrix_charmatrix]
          simp [Matrix.bandedLowerHessenberg, Matrix.det_fin_two]
          ring
      | n + 3 =>
          rw [tetradiagonalPolynomial, tetradiagonalMatrix_charpoly_add_three]
          rw [ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia)]

/-- A positive second-subdiagonal entry after a zero canonical pivot is
rejected. -/
theorem canonicalLowerSplit_rejects_positive_after_zero :
    ¬ CanonicalLowerSplitSucceeds (fun _ => 0)
      (fun n => if n = 1 then 1 else 0) := by
  intro h
  have hzero := (h 0).2 (by simp)
  norm_num at hzero

/-- A zero second-subdiagonal entry after a zero canonical pivot restarts the
construction successfully. -/
theorem canonicalLowerSplit_accepts_zero_restart :
    CanonicalLowerSplitSucceeds (fun _ => 0) (fun _ => 0) := by
  have hfactor : ∀ n, canonicalSecondFactor (fun _ => 0) (fun _ => 0) n = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [canonicalSecondFactor_succ, ih]
  intro n
  rw [hfactor n]
  exact ⟨le_refl 0, fun _ => rfl⟩

end

end RealRooted
