module

public import RealRooted.DerivativeRecurrence.RootWindow
public import RealRooted.Interlacing.OuterDifference
public import RealRooted.MaWang.StrictStep
public import RealRooted.Recurrence.RowModel
public import RealRooted.Recurrence.Uniqueness
import RealRooted.Tactic.RowInterlacing

set_option rr.row.explain true
set_option linter.style.longLine false

/-!
# Harmonic-factor derivative rows

Interlacing for a derivative image of the partial products
`∏ j, (1 + j X)`, together with its lag-three recurrence transfer.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The partial product with roots `-1, -1/2, ..., -1/(n-1)`. -/
def harmonicFactorProduct : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + C (n : ℝ) * X) * harmonicFactorProduct n

/-- The derivative image of a harmonic-factor product. -/
def harmonicDerivativeRow (n : ℕ) : ℝ[X] :=
  let N : ℝ := n + 2
  (C (N - 1) + C (N ^ 2) * X) * harmonicFactorProduct (n + 2) -
    X * (1 + C N * X) * (harmonicFactorProduct (n + 2)).derivative

/-- The derivative image with its integer parameter expanded. -/
theorem harmonicDerivativeRow_eq (n : ℕ) :
    harmonicDerivativeRow n =
      (C ((n : ℝ) + 1) + C (((n : ℝ) + 2) ^ 2) * X) *
          harmonicFactorProduct (n + 2) -
        X * (1 + C ((n : ℝ) + 2) * X) *
          (harmonicFactorProduct (n + 2)).derivative := by
  simp only [harmonicDerivativeRow]
  ring

/-- The defining recursion for the harmonic-factor partial products. -/
@[simp] theorem harmonicFactorProduct_succ (n : ℕ) :
    harmonicFactorProduct (n + 1) =
      (1 + C (n : ℝ) * X) * harmonicFactorProduct n := rfl

/-- Harmonic-factor partial products have nonnegative coefficients. -/
theorem harmonicFactorProduct_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (harmonicFactorProduct n) := by
  rr_row_nonneg_coeffs

/-- Harmonic-factor partial products split over the reals. -/
theorem harmonicFactorProduct_splits (n : ℕ) :
    (harmonicFactorProduct n).Splits := by
  rr_row_splits

private theorem harmonicFactorProduct_coeff_zero (n : ℕ) :
    (harmonicFactorProduct n).coeff 0 = 1 := by
  induction n with
  | zero => simp [harmonicFactorProduct]
  | succ n ih =>
      rw [harmonicFactorProduct_succ, coeff_mul]
      simp [ih]

/-- Harmonic-factor partial products are nonzero. -/
theorem harmonicFactorProduct_ne_zero (n : ℕ) :
    harmonicFactorProduct n ≠ 0 := by
  rr_row_ne_zero

/-- The degree of the `n`-th harmonic-factor partial product is `n - 1`. -/
theorem harmonicFactorProduct_natDegree (n : ℕ) :
    (harmonicFactorProduct n).natDegree = n - 1 := by
  rr_row_natDegree

/-- Every root lies strictly left of the next unused harmonic node. -/
theorem harmonicFactorProduct_root_lt : ∀ {n : ℕ} {r : ℝ},
    (harmonicFactorProduct n).IsRoot r → r < 0 ∧ 1 + (n : ℝ) * r < 0
  | 0, r, hr => by
      simp [harmonicFactorProduct, Polynomial.IsRoot] at hr
  | n + 1, r, hr => by
      rw [harmonicFactorProduct_succ, Polynomial.IsRoot, eval_mul, mul_eq_zero] at hr
      rcases hr with hnew | hold
      · rw [eval_add, eval_one, eval_mul, eval_C, eval_X] at hnew
        by_cases hn : n = 0
        · simp_all
        · have hnpos : (0 : ℝ) < n := by positivity
          constructor
          · nlinarith
          · push_cast
            nlinarith
      · have hb := harmonicFactorProduct_root_lt hold
        constructor
        · exact hb.1
        · push_cast
          nlinarith

/-- The harmonic-factor products have no repeated roots. -/
theorem harmonicFactorProduct_hasSimpleRoots (n : ℕ) :
    HasSimpleRoots (harmonicFactorProduct n) := by
  induction n with
  | zero =>
      intro r hr
      simp [harmonicFactorProduct, Polynomial.IsRoot] at hr
  | succ n ih =>
      have hne := harmonicFactorProduct_ne_zero (n + 1)
      intro r hr
      apply le_antisymm
      · by_contra hnot
        have hmult : 1 < (harmonicFactorProduct (n + 1)).rootMultiplicity r := by
          have hpos := (Polynomial.rootMultiplicity_pos hne).mpr hr
          lia
        have hderRoot :=
          ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hne).mp hmult).2
        rw [harmonicFactorProduct_succ, derivative_mul, derivative_add,
          derivative_one, derivative_mul, derivative_C, derivative_X] at hderRoot
        simp only [zero_mul, zero_add] at hderRoot
        rw [Polynomial.IsRoot.def] at hderRoot
        simp only [eval_add, eval_mul, eval_C, eval_X, eval_one] at hderRoot
        rw [harmonicFactorProduct_succ, Polynomial.IsRoot, eval_mul,
          mul_eq_zero] at hr
        rcases hr with hlinear | hold
        · have hnotOld : ¬(harmonicFactorProduct n).IsRoot r := by
            intro hold'
            have hb := harmonicFactorProduct_root_lt hold'
            rw [eval_add, eval_one, eval_mul, eval_C, eval_X] at hlinear
            nlinarith
          have holdEval : (harmonicFactorProduct n).eval r ≠ 0 := by
            simpa [Polynomial.IsRoot.def] using hnotOld
          simp only [eval_add, eval_one, eval_mul, eval_C, eval_X] at hlinear
          have hn : (n : ℝ) ≠ 0 := by
            intro hn
            rw [hn, zero_mul, add_zero] at hlinear
            norm_num at hlinear
          rw [hlinear, zero_mul] at hderRoot
          simp only [add_zero] at hderRoot
          exact holdEval
            (mul_eq_zero.mp hderRoot |>.resolve_left (mul_ne_zero hn one_ne_zero))
        · have hlinear : (1 + C (n : ℝ) * X : ℝ[X]).eval r ≠ 0 := by
            have hb := harmonicFactorProduct_root_lt hold
            simp only [eval_add, eval_one, eval_mul, eval_C, eval_X]
            nlinarith
          simp only [eval_add, eval_one, eval_mul, eval_C, eval_X] at hlinear
          have hderOld : (harmonicFactorProduct n).derivative.eval r ≠ 0 :=
            ih.eval_derivative_ne_zero hold
          rw [hold, mul_zero] at hderRoot
          simp only [zero_add] at hderRoot
          exact hderOld (mul_eq_zero.mp hderRoot |>.resolve_left hlinear)
      · exact Polynomial.rootMultiplicity_pos hne |>.mpr hr

private theorem harmonicDerivativeForm_coeff_top (n : ℕ) (p : ℝ[X])
    (hdeg : p.natDegree = n + 1) :
    ((C ((n : ℝ) + 1) + C (((n : ℝ) + 2) ^ 2) * X) * p -
      X * (1 + C ((n : ℝ) + 2) * X) * p.derivative).coeff (n + 2) =
        ((n : ℝ) + 2) * p.coeff (n + 1) := by
  have habove : p.coeff (n + 2) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hdeg]
    lia
  have heq :
      (C ((n : ℝ) + 1) + C (((n : ℝ) + 2) ^ 2) * X) * p -
          X * (1 + C ((n : ℝ) + 2) * X) * p.derivative =
        C ((n : ℝ) + 1) * p + C (((n : ℝ) + 2) ^ 2) * (X * p) -
          (X * p.derivative + C ((n : ℝ) + 2) * (X ^ 2 * p.derivative)) := by
    ring
  rw [heq, coeff_sub, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul,
    coeff_C_mul, coeff_X_mul, coeff_X_mul, coeff_X_pow_mul, coeff_derivative,
    coeff_derivative, habove]
  push_cast
  ring

private theorem harmonicDerivativeForm_natDegree_le (n : ℕ) (p : ℝ[X])
    (hdeg : p.natDegree = n + 1) :
    ((C ((n : ℝ) + 1) + C (((n : ℝ) + 2) ^ 2) * X) * p -
      X * (1 + C ((n : ℝ) + 2) * X) * p.derivative).natDegree ≤ n + 2 := by
  have hleft :
      (C ((n : ℝ) + 1) + C (((n : ℝ) + 2) ^ 2) * X).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact (natDegree_C_mul_le _ X).trans natDegree_X_le
  have hright :
      (X * (1 + C ((n : ℝ) + 2) * X) : ℝ[X]).natDegree ≤ 2 := by
    have hinner : (1 + C ((n : ℝ) + 2) * X : ℝ[X]).natDegree ≤ 1 := by
      refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
      exact (natDegree_C_mul_le _ X).trans natDegree_X_le
    exact natDegree_mul_le.trans (by
      have hX : (X : ℝ[X]).natDegree ≤ 1 := natDegree_X_le
      lia)
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · calc
      ((C ((n : ℝ) + 1) + C (((n : ℝ) + 2) ^ 2) * X) * p).natDegree ≤
          (C ((n : ℝ) + 1) + C (((n : ℝ) + 2) ^ 2) * X).natDegree +
            p.natDegree := Polynomial.natDegree_mul_le
      _ ≤ n + 2 := by rw [hdeg]; lia
  · calc
      (X * (1 + C ((n : ℝ) + 2) * X) * p.derivative).natDegree ≤
          (X * (1 + C ((n : ℝ) + 2) * X)).natDegree +
            p.derivative.natDegree := Polynomial.natDegree_mul_le
      _ ≤ n + 2 := by
        have hder := Polynomial.natDegree_derivative_le p
        rw [hdeg] at hder
        lia

/-- The derivative-image rows have the expected degree. -/
theorem harmonicDerivativeRow_natDegree (n : ℕ) :
    (harmonicDerivativeRow n).natDegree = n + 2 := by
  rw [harmonicDerivativeRow_eq]
  have hGdeg : (harmonicFactorProduct (n + 2)).natDegree = n + 1 := by
    rw [harmonicFactorProduct_natDegree]; lia
  have hG0 : harmonicFactorProduct (n + 2) ≠ 0 :=
    harmonicFactorProduct_ne_zero (n + 2)
  have hGlc : 0 < (harmonicFactorProduct (n + 2)).leadingCoeff :=
    (harmonicFactorProduct_hasNonnegCoeffs (n + 2)).pos_leadingCoeff hG0
  rw [leadingCoeff, hGdeg] at hGlc
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact harmonicDerivativeForm_natDegree_le n _ hGdeg
  · rw [harmonicDerivativeForm_coeff_top n _ hGdeg]
    positivity

/-- The derivative-image rows have positive leading coefficient. -/
theorem harmonicDerivativeRow_hasPosLeadingCoeff (n : ℕ) :
    HasPosLeadingCoeff (harmonicDerivativeRow n) := by
  rw [HasPosLeadingCoeff, leadingCoeff, harmonicDerivativeRow_natDegree]
  rw [harmonicDerivativeRow_eq]
  have hGdeg : (harmonicFactorProduct (n + 2)).natDegree = n + 1 := by
    rw [harmonicFactorProduct_natDegree]; lia
  have hG0 : harmonicFactorProduct (n + 2) ≠ 0 :=
    harmonicFactorProduct_ne_zero (n + 2)
  have hGlc : 0 < (harmonicFactorProduct (n + 2)).leadingCoeff :=
    (harmonicFactorProduct_hasNonnegCoeffs (n + 2)).pos_leadingCoeff hG0
  rw [leadingCoeff, hGdeg] at hGlc
  rw [harmonicDerivativeForm_coeff_top n _ hGdeg]
  positivity

private theorem harmonicDerivativeRow_expanded (n : ℕ) :
    harmonicDerivativeRow n =
      C ((n : ℝ) + 1) * harmonicFactorProduct (n + 2) +
        C (((n : ℝ) + 2) ^ 2) * (X * harmonicFactorProduct (n + 2)) -
        (X * (harmonicFactorProduct (n + 2)).derivative +
          C ((n : ℝ) + 2) *
            (X ^ 2 * (harmonicFactorProduct (n + 2)).derivative)) := by
  rw [harmonicDerivativeRow_eq]
  ring

private theorem harmonicDerivativeRow_coeff_zero (n : ℕ) :
    (harmonicDerivativeRow n).coeff 0 =
      ((n : ℝ) + 1) * (harmonicFactorProduct (n + 2)).coeff 0 := by
  simp [harmonicDerivativeRow_expanded]

private theorem harmonicDerivativeRow_coeff_one (n : ℕ) :
    (harmonicDerivativeRow n).coeff 1 =
      (n : ℝ) * (harmonicFactorProduct (n + 2)).coeff 1 +
        ((n : ℝ) + 2) ^ 2 *
          (harmonicFactorProduct (n + 2)).coeff 0 := by
  rw [harmonicDerivativeRow_expanded, coeff_sub, coeff_add, coeff_add,
    coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_mul, coeff_X_mul]
  have hx2 :
      (X ^ 2 * (harmonicFactorProduct (n + 2)).derivative).coeff 1 = 0 := by
    rw [coeff_X_pow_mul', ite_eq_right (by norm_num)]
  rw [hx2, coeff_derivative]
  norm_num
  ring

private theorem harmonicDerivativeRow_coeff_add_two (n k : ℕ) :
    (harmonicDerivativeRow n).coeff (k + 2) =
      ((n : ℝ) - k - 1) *
          (harmonicFactorProduct (n + 2)).coeff (k + 2) +
        ((n : ℝ) + 2) * ((n : ℝ) + 1 - k) *
          (harmonicFactorProduct (n + 2)).coeff (k + 1) := by
  rw [harmonicDerivativeRow_expanded, coeff_sub, coeff_add, coeff_add,
    coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_mul, coeff_X_mul,
    coeff_X_pow_mul, coeff_derivative, coeff_derivative]
  push_cast
  ring

/-- The derivative-image rows have nonnegative coefficients. -/
theorem harmonicDerivativeRow_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (harmonicDerivativeRow n) := by
  intro k
  rcases k with _ | _ | k
  · rw [harmonicDerivativeRow_coeff_zero]
    exact mul_nonneg (by positivity) (harmonicFactorProduct_hasNonnegCoeffs (n + 2) 0)
  · rw [harmonicDerivativeRow_coeff_one]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (harmonicFactorProduct_hasNonnegCoeffs (n + 2) 1))
      (mul_nonneg (sq_nonneg _) (harmonicFactorProduct_hasNonnegCoeffs (n + 2) 0))
  rw [harmonicDerivativeRow_coeff_add_two]
  rcases le_or_gt (k + 2) (n + 1) with hk | hk
  · have hknNat : k + 1 ≤ n := by lia
    have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hknNat
    have hnn := harmonicFactorProduct_hasNonnegCoeffs (n + 2)
    exact add_nonneg
      (mul_nonneg (by linarith) (hnn (k + 2)))
      (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (hnn (k + 1)))
  · have hzero2 : (harmonicFactorProduct (n + 2)).coeff (k + 2) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [harmonicFactorProduct_natDegree]
      lia
    by_cases hkn : k + 1 = n + 1
    · have hkEq : k = n := by lia
      subst k
      rw [hzero2]
      have hfactor :
          ((n : ℝ) + 2) * ((n : ℝ) + 1 - (n : ℝ)) = (n : ℝ) + 2 := by
        ring
      rw [hfactor]
      simp only [mul_zero, zero_add]
      have hn2 : 0 ≤ (n : ℝ) + 2 := by positivity
      exact mul_nonneg hn2
        (harmonicFactorProduct_hasNonnegCoeffs (n + 2) (n + 1))
    · have hzero1 : (harmonicFactorProduct (n + 2)).coeff (k + 1) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [harmonicFactorProduct_natDegree]
        lia
      rw [hzero2, hzero1]
      norm_num

/-- A harmonic-factor product strictly interlaces its derivative image, which
also has simple roots. -/
theorem harmonicFactorProduct_strictInterl_harmonicDerivativeRow (n : ℕ) :
    StrictInterl (harmonicFactorProduct (n + 2)) (harmonicDerivativeRow n) ∧
      HasSimpleRoots (harmonicDerivativeRow n) := by
  let f := harmonicFactorProduct (n + 2)
  let u := C ((n : ℝ) + 1) + C (((n : ℝ) + 2) ^ 2) * X
  let v := -X * (1 + C ((n : ℝ) + 2) * X)
  have hfdeg : f.natDegree = n + 1 := by
    dsimp only [f]; rw [harmonicFactorProduct_natDegree]; lia
  have hfpos : HasPosLeadingCoeff f :=
    (harmonicFactorProduct_hasNonnegCoeffs (n + 2)).pos_leadingCoeff
      (harmonicFactorProduct_ne_zero (n + 2))
  have hrec : harmonicDerivativeRow n = u * f + v * f.derivative := by
    dsimp only [u, v, f]
    rw [harmonicDerivativeRow_eq]
    ring
  apply strictInterl_and_hasSimpleRoots_of_interlaces_eval_mul_neg_succ
    (harmonicFactorProduct_splits (n + 2)) hfpos (harmonicDerivativeRow_hasPosLeadingCoeff n)
    (by rw [hfdeg]; lia)
    (by rw [harmonicDerivativeRow_natDegree, hfdeg])
    (harmonicFactorProduct_hasSimpleRoots (n + 2)) hrec
  intro r hr
  have hb := harmonicFactorProduct_root_lt hr
  push_cast at hb
  dsimp only [v]
  simp only [eval_mul, eval_neg, eval_X, eval_add, eval_one, eval_C]
  exact mul_neg_of_pos_of_neg (neg_pos.mpr hb.1) hb.2

private theorem harmonicFactorProduct_no_common_harmonicDerivativeRow (n : ℕ) :
    ∀ r, (harmonicFactorProduct (n + 2)).IsRoot r →
      ¬(harmonicDerivativeRow n).IsRoot r := by
  intro r hG hP
  have hsimple := harmonicFactorProduct_hasSimpleRoots (n + 2)
  have hder_ne := hsimple.eval_derivative_ne_zero hG
  have hb := harmonicFactorProduct_root_lt hG
  have hval := congrArg (Polynomial.eval r) (harmonicDerivativeRow_eq n)
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_one] at hval
  rw [hG.eq_zero, hP.eq_zero] at hval
  simp only [mul_zero, zero_sub] at hval
  push_cast at hb
  have hco : r * (1 + ((n : ℝ) + 2) * r) ≠ 0 := by
    exact mul_ne_zero (by linarith) (by nlinarith)
  have hprod : r * (1 + ((n : ℝ) + 2) * r) *
      (harmonicFactorProduct (n + 2)).derivative.eval r = 0 := by
    linarith
  exact hder_ne (mul_eq_zero.mp hprod |>.resolve_left hco)

/-- Every zero of a derivative-image row lies strictly left of the next
unused harmonic node. -/
theorem harmonicDerivativeRow_root_lt (n : ℕ) {r : ℝ}
    (hr : (harmonicDerivativeRow n).IsRoot r) :
    1 + ((n : ℝ) + 4) * r < 0 := by
  have hPneg : r < 0 := by
    have hrnonpos := isRoot_nonpos_of_hasNonnegCoeffs
      (harmonicDerivativeRow_hasNonnegCoeffs n)
      (harmonicDerivativeRow_hasPosLeadingCoeff n).ne_zero hr
    refine lt_of_le_of_ne hrnonpos fun hrzero => ?_
    have hrEval : (harmonicDerivativeRow n).eval r = 0 := hr
    rw [hrzero, ← coeff_zero_eq_eval_zero, harmonicDerivativeRow_coeff_zero,
      harmonicFactorProduct_coeff_zero] at hrEval
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    linarith
  by_contra hnot
  have hbarrier : 0 ≤ 1 + ((n : ℝ) + 4) * r := by linarith
  let f := harmonicFactorProduct (n + 2)
  have hfdeg : f.natDegree = n + 1 := by
    dsimp only [f]; rw [harmonicFactorProduct_natDegree]; lia
  have hfpos : HasPosLeadingCoeff f :=
    (harmonicFactorProduct_hasNonnegCoeffs (n + 2)).pos_leadingCoeff
      (harmonicFactorProduct_ne_zero (n + 2))
  have hroot : ∀ t ∈ f.roots, t < r := by
    intro t ht
    have htroot : f.IsRoot t :=
      (mem_roots (harmonicFactorProduct_ne_zero (n + 2))).mp ht
    have htbound := harmonicFactorProduct_root_lt htroot
    push_cast at htbound
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hn4 : (0 : ℝ) < (n : ℝ) + 4 := by positivity
    have htFrac : t < (-1 : ℝ) / ((n : ℝ) + 2) :=
      (lt_div_iff₀ hn2).mpr (by nlinarith)
    have hfrac : (-1 : ℝ) / ((n : ℝ) + 2) < (-1 : ℝ) / ((n : ℝ) + 4) :=
      (div_lt_div_iff₀ hn2 hn4).mpr (by nlinarith)
    have hrFrac : (-1 : ℝ) / ((n : ℝ) + 4) ≤ r :=
      (div_le_iff₀ hn4).mpr (by nlinarith)
    exact htFrac.trans (hfrac.trans_le hrFrac)
  have hfeval : 0 < f.eval r :=
    eval_pos_of_all_roots_lt hfpos.ne_zero (harmonicFactorProduct_splits (n + 2))
      hfpos hroot
  have hbound : ∀ t ∈ f.roots, t ≤ -(1 / ((n : ℝ) + 2)) := by
    intro t ht
    have htroot : f.IsRoot t :=
      (mem_roots (harmonicFactorProduct_ne_zero (n + 2))).mp ht
    have htbound := harmonicFactorProduct_root_lt htroot
    push_cast at htbound
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    rw [← neg_div]
    exact le_of_lt ((lt_div_iff₀ hn2).mpr (by nlinarith))
  have hUr : -(1 / ((n : ℝ) + 2)) < r := by
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hn4 : (0 : ℝ) < (n : ℝ) + 4 := by positivity
    have hfrac : (-1 : ℝ) / ((n : ℝ) + 2) < (-1 : ℝ) / ((n : ℝ) + 4) :=
      (div_lt_div_iff₀ hn2 hn4).mpr (by nlinarith)
    have hrFrac : (-1 : ℝ) / ((n : ℝ) + 4) ≤ r :=
      (div_le_iff₀ hn4).mpr (by nlinarith)
    calc
      -(1 / ((n : ℝ) + 2)) = (-1 : ℝ) / ((n : ℝ) + 2) := by ring
      _ < (-1 : ℝ) / ((n : ℝ) + 4) := hfrac
      _ ≤ r := hrFrac
  have hfder : 0 < f.derivative.eval r :=
    derivative_eval_pos_of_roots_le (harmonicFactorProduct_splits (n + 2))
      hfpos (by rw [hfdeg]; lia) hbound hUr
  have hval := congrArg (Polynomial.eval r) (harmonicDerivativeRow_eq n)
  rw [hr.eq_zero] at hval
  dsimp only [f] at hfeval hfder
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_one] at hval
  have ha : 0 ≤ (n : ℝ) + 1 + ((n : ℝ) + 2) ^ 2 * r := by
    nlinarith
  have hb : 0 < -r * (1 + ((n : ℝ) + 2) * r) := by
    have : 0 < 1 + ((n : ℝ) + 2) * r := by nlinarith
    exact mul_pos (neg_pos.mpr hPneg) this
  nlinarith

private theorem harmonicDerivativeRow_succ_eval_root (n : ℕ) {r : ℝ}
    (hr : (harmonicDerivativeRow n).IsRoot r) :
    (harmonicDerivativeRow (n + 1)).eval r =
      (1 + ((n : ℝ) + 4) * r) * (harmonicFactorProduct (n + 2)).eval r := by
  have hroot := hr
  rw [Polynomial.IsRoot.def, harmonicDerivativeRow_eq] at hroot
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_one] at hroot
  rw [harmonicDerivativeRow_eq, harmonicFactorProduct_succ]
  simp only [derivative_mul, derivative_add, derivative_one, derivative_mul,
    derivative_C, derivative_X, zero_mul, zero_add, eval_sub,
    eval_add, eval_mul, eval_C, eval_X, eval_one]
  push_cast at hroot ⊢
  have hmul := congrArg (fun x : ℝ =>
    (1 + ((n : ℝ) + 3) * r) * x) hroot
  ring_nf at hmul ⊢
  linarith

/-- Consecutive derivative images of harmonic-factor products strictly interlace. -/
theorem harmonicDerivativeRow_strictInterl_succ (n : ℕ) :
    StrictInterl (harmonicDerivativeRow n) (harmonicDerivativeRow (n + 1)) := by
  have hpair := harmonicFactorProduct_strictInterl_harmonicDerivativeRow n
  have hder : Interlaces (harmonicDerivativeRow n).derivative
      (harmonicDerivativeRow n) :=
    derivative_interlaces_of_natDegree_ne_zero hpair.1.2.1.2
      (by rw [harmonicDerivativeRow_natDegree]; lia)
  have hderpos := (harmonicDerivativeRow_hasPosLeadingCoeff n).derivative
    (by rw [harmonicDerivativeRow_natDegree]; lia)
  apply strictInterl_of_interlaces_eval_mul_neg_succ hder hderpos
    (harmonicDerivativeRow_hasPosLeadingCoeff (n + 1))
    (by rw [harmonicDerivativeRow_natDegree, harmonicDerivativeRow_natDegree])
  intro r hr
  rw [harmonicDerivativeRow_succ_eval_root n hr]
  have hprod : 0 < (harmonicFactorProduct (n + 2)).eval r *
      (harmonicDerivativeRow n).derivative.eval r :=
    hpair.1.eval_mul_derivative_pos_of_right_root_of_no_common
      ((harmonicFactorProduct_hasNonnegCoeffs (n + 2)).pos_leadingCoeff
        (harmonicFactorProduct_ne_zero (n + 2)))
      (harmonicDerivativeRow_hasPosLeadingCoeff n)
      (harmonicFactorProduct_no_common_harmonicDerivativeRow n) hr
  have hfactor := harmonicDerivativeRow_root_lt n hr
  nlinarith

/-- Consecutive derivative images of harmonic-factor products interlace. -/
theorem harmonicDerivativeRow_interlaces (n : ℕ) :
    Interlaces (harmonicDerivativeRow n) (harmonicDerivativeRow (n + 1)) := by
  apply (harmonicDerivativeRow_strictInterl_succ n).toInterlaces
  rw [harmonicDerivativeRow_natDegree, harmonicDerivativeRow_natDegree]

end RealRooted

namespace RealRooted.HarmonicDerivativeRows

/-- The lag-three update satisfied by `harmonicDerivativeRow`. -/
def nextRow (n : ℕ) (p₂ p₁ p₀ : ℝ[X]) : ℝ[X] :=
  (C 2 + C (7 + 2 * (n : ℝ)) * X) * p₂ +
    (C (-1) + C (-4 + -2 * (n : ℝ)) * X +
      C (12 + -1 * (4 + (n : ℝ)) ^ 2 + 4 * (n : ℝ)) * X ^ 2) * p₁ +
    (C (-2) * X + C (-10 + -4 * (n : ℝ)) * X ^ 2 +
      C (20 + -2 * (4 + (n : ℝ)) ^ 2 + 6 * (n : ℝ)) * X ^ 3) * p₀

private theorem harmonicDerivativeRow_zero :
    harmonicDerivativeRow 0 = 1 + 4 * X + 2 * X ^ 2 := by
  norm_num [harmonicDerivativeRow, harmonicFactorProduct, map_ofNat]
  ring

private theorem harmonicDerivativeRow_one :
    harmonicDerivativeRow 1 = 2 + 12 * X + 18 * X ^ 2 + 6 * X ^ 3 := by
  norm_num [harmonicDerivativeRow, harmonicFactorProduct, derivative_mul, map_ofNat]
  ring

private theorem harmonicDerivativeRow_two :
    harmonicDerivativeRow 2 =
      3 + 28 * X + 83 * X ^ 2 + 88 * X ^ 3 + 24 * X ^ 4 := by
  norm_num [harmonicDerivativeRow, harmonicFactorProduct, derivative_mul, map_ofNat]
  ring

private theorem harmonicDerivativeRow_recurrence (n : ℕ) :
    harmonicDerivativeRow (n + 3) =
      nextRow n (harmonicDerivativeRow (n + 2))
        (harmonicDerivativeRow (n + 1)) (harmonicDerivativeRow n) := by
  simp only [harmonicDerivativeRow]
  have hthree : n + 3 + 2 = ((n + 2) + 2) + 1 := by lia
  have htwo : n + 2 + 2 = ((n + 1) + 2) + 1 := by lia
  have hone : n + 1 + 2 = (n + 2) + 1 := by lia
  rw [hthree, harmonicFactorProduct_succ, htwo, harmonicFactorProduct_succ,
    hone, harmonicFactorProduct_succ]
  simp only [derivative_mul, derivative_add, derivative_C, derivative_X,
    derivative_one]
  push_cast
  simp only [nextRow, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
    map_one]
  ring

/-- A sequence with the harmonic derivative-image initial rows and lag-three
update has interlacing consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1 + 4 * X + 2 * X ^ 2)
    (hone : P 1 = 2 + 12 * X + 18 * X ^ 2 + 6 * X ^ 3)
    (htwo : P 2 = 3 + 28 * X + 83 * X ^ 2 + 88 * X ^ 3 + 24 * X ^ 4)
    (hrec : ∀ n : ℕ,
      P (n + 3) = nextRow n (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_three_recurrence nextRow
    (hzero.trans harmonicDerivativeRow_zero.symm)
    (hone.trans harmonicDerivativeRow_one.symm)
    (htwo.trans harmonicDerivativeRow_two.symm)
    hrec harmonicDerivativeRow_recurrence
  rw [heq n, heq (n + 1)]
  exact harmonicDerivativeRow_interlaces n

end RealRooted.HarmonicDerivativeRows
