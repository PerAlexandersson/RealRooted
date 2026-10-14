import RealRooted.Legendre.Roots
import RealRooted.MaWang.Weak.Endpoint
import RealRooted.Recurrence.RowModel
import RealRooted.Recurrence.Uniqueness

/-!
# The row polynomials of OEIS A080721

The type-`D` cluster-complex rows are quasi-Legendre polynomials.  Rewriting two
successive quasi-Legendre rows in the Legendre basis gives a Liu--Wang step
whose coefficient of the interlacer is negative on the whole real line.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A080721

/-- Reflected shifted Legendre polynomials, normalized to have constant
coefficient one and positive leading coefficient. -/
def legendre : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 2 * X
  | n + 2 =>
      C ((2 * (n : ℝ) + 3) / ((n : ℝ) + 2)) *
          (1 + 2 * X) * legendre (n + 1) -
        C (((n : ℝ) + 1) / ((n : ℝ) + 2)) * legendre n

theorem legendre_succ_succ (n : ℕ) :
    legendre (n + 2) =
      C ((2 * (n : ℝ) + 3) / ((n : ℝ) + 2)) *
          (1 + 2 * X) * legendre (n + 1) -
        C (((n : ℝ) + 1) / ((n : ℝ) + 2)) * legendre n := by
  rfl

private theorem reflected_shiftedLegendre_succ_succ (n : ℕ) :
    (shiftedLegendreReal (n + 2)).comp (-X) =
      C ((2 * (n : ℝ) + 3) / ((n : ℝ) + 2)) *
          (1 + 2 * X) * (shiftedLegendreReal (n + 1)).comp (-X) -
        C (((n : ℝ) + 1) / ((n : ℝ) + 2)) *
          (shiftedLegendreReal n).comp (-X) := by
  by_cases hn : n = 0
  · subst n
    apply Polynomial.funext
    intro x
    simp
    ring
  · apply Polynomial.funext
    intro x
    simp only [shiftedLegendreReal_eq_shiftedJacobi,
      eval_sub, eval_mul, eval_C, eval_add, eval_one, eval_ofNat,
      eval_X, eval_comp, eval_neg]
    have hraw := Polynomial.shiftedJacobi_recurrence_raw
      (n + 1) 0 0 (by lia) (by norm_num) (by norm_num)
    have heval := congrArg (fun p : ℝ[X] => p.eval (-x)) hraw
    simp only [eval_mul, eval_C, eval_add, eval_sub, eval_X] at heval
    norm_num only [Nat.add_assoc, Nat.add_sub_cancel] at heval
    push_cast at heval
    norm_num at heval
    simp only [← Polynomial.shiftedJacobi_zero_zero_eq_map_shiftedLegendre]
      at heval
    have hscale : 4 * ((n : ℝ) + 1) * ((n : ℝ) + 2) ≠ 0 := by
      positivity
    have hnormalized :
        ((n : ℝ) + 2) *
            (Polynomial.shiftedJacobi (n + 2) 0 0).eval (-x) =
          (2 * (n : ℝ) + 3) * (1 + 2 * x) *
              (Polynomial.shiftedJacobi (n + 1) 0 0).eval (-x) -
            ((n : ℝ) + 1) *
              (Polynomial.shiftedJacobi n 0 0).eval (-x) := by
      apply mul_left_cancel₀ hscale
      linear_combination heval
    have hden : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hden]
    linear_combination hnormalized

/-- The recursive Legendre model is Mathlib's reflected shifted Legendre
polynomial. -/
theorem legendre_eq_shiftedLegendreReal_comp_neg_X (n : ℕ) :
    legendre n = (shiftedLegendreReal n).comp (-X) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [legendre]
  | one => simp [legendre]
  | more n ih0 ih1 =>
      rw [legendre_succ_succ, reflected_shiftedLegendre_succ_succ,
        ih0, ih1]

@[simp] theorem legendre_natDegree (n : ℕ) :
    (legendre n).natDegree = n := by
  rw [legendre_eq_shiftedLegendreReal_comp_neg_X]
  exact shiftedLegendreReal_comp_neg_X_natDegree n

theorem legendre_posLeadingCoeff (n : ℕ) :
    HasPosLeadingCoeff (legendre n) := by
  rw [legendre_eq_shiftedLegendreReal_comp_neg_X]
  exact shiftedLegendreReal_comp_neg_X_hasPosLeadingCoeff n

theorem legendre_strictInterl_succ (n : ℕ) :
    StrictInterl (legendre n) (legendre (n + 1)) := by
  rw [legendre_eq_shiftedLegendreReal_comp_neg_X,
    legendre_eq_shiftedLegendreReal_comp_neg_X]
  exact shiftedLegendreReal_comp_neg_X_strictInterl_succ n

/-- The type-`D` quasi-Legendre polynomial of ambient dimension `d`. -/
def polynomial (d : ℕ) : ℝ[X] :=
  C ((3 * (d : ℝ) - 2) / (4 * (d : ℝ) - 2)) * legendre d +
    C ((d : ℝ) / (4 * (d : ℝ) - 2)) * legendre (d - 2)

private theorem polynomial_succ_succ (n : ℕ) :
    polynomial (n + 2) =
      C ((3 * ((n : ℝ) + 2) - 2) / (2 * ((n : ℝ) + 2))) *
          (1 + 2 * X) * legendre (n + 1) +
        C (-((n : ℝ) / (2 * ((n : ℝ) + 2)))) * legendre n := by
  rw [polynomial, legendre_succ_succ]
  apply Polynomial.funext
  intro r
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_one, eval_ofNat,
    eval_X]
  grind

/-- The preceding Legendre polynomial strictly interlaces a type-`D` row. -/
theorem legendre_strictInterl_polynomial (n : ℕ) :
    StrictInterl (legendre (n + 1)) (polynomial (n + 2)) := by
  let a : ℝ[X] :=
    C ((3 * ((n : ℝ) + 2) - 2) / (2 * ((n : ℝ) + 2))) * (1 + 2 * X)
  let b : ℝ[X] := C (-((n : ℝ) / (2 * ((n : ℝ) + 2))))
  have ha_scalar :
      0 < (3 * ((n : ℝ) + 2) - 2) / (2 * ((n : ℝ) + 2)) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    apply div_pos <;> nlinarith
  have hlinear_pos : HasPosLeadingCoeff (1 + 2 * X : ℝ[X]) := by
    rw [show (1 + 2 * X : ℝ[X]) =
        C 2 * (X + C (1 / 2 : ℝ)) by
          simp only [one_div]
          rw [show (2 : ℝ[X]) = C (2 : ℝ) from
            (map_ofNat C 2).symm, mul_add, ← map_mul]
          grind]
    exact hasPosLeadingCoeff_C_mul (by norm_num)
      (hasPosLeadingCoeff_X_add_C (1 / 2))
  have ha_pos : HasPosLeadingCoeff a :=
    hasPosLeadingCoeff_C_mul ha_scalar hlinear_pos
  have hf_pos := legendre_posLeadingCoeff (n + 1)
  have hg_pos := legendre_posLeadingCoeff n
  have haf_pos : HasPosLeadingCoeff (a * legendre (n + 1)) :=
    ha_pos.mul hf_pos
  have ha_deg : a.natDegree = 1 := by
    change
      (C ((3 * ((n : ℝ) + 2) - 2) / (2 * ((n : ℝ) + 2))) *
        (1 + 2 * X)).natDegree = 1
    rw [natDegree_C_mul ha_scalar.ne']
    compute_degree!
  have hdeg_af :
      (a * legendre (n + 1)).natDegree = n + 2 := by
    rw [natDegree_mul ha_pos.ne_zero hf_pos.ne_zero, ha_deg,
      legendre_natDegree]
    lia
  have hdeg_bg : (b * legendre n).natDegree ≤ n := by
    exact Polynomial.natDegree_mul_le.trans (by
      have hbdeg : b.natDegree ≤ 0 := by simp [b]
      rw [legendre_natDegree]
      lia)
  have hsum_pos :
      HasPosLeadingCoeff
        (a * legendre (n + 1) + b * legendre n) :=
    hasPosLeadingCoeff_add_of_natDegree_lt_left (by grind) haf_pos
  have hsum_deg :
      (a * legendre (n + 1) + b * legendre n).natDegree = n + 2 :=
    (natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff
      (by grind) haf_pos).trans hdeg_af
  have hb_nonpos :
      ∀ r : ℝ, (legendre (n + 1)).IsRoot r → b.eval r ≤ 0 := by
    intro r _
    simp only [b, eval_C]
    exact neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg n) (by positivity))
  have hprec :
      StrictInterl (legendre (n + 1))
        (a * legendre (n + 1) + b * legendre n) :=
    strictInterl_of_interlaces_evalCoeff_nonpos
      ((legendre_strictInterl_succ n).toInterlaces (by simp))
      hg_pos hsum_pos (by simp [hsum_deg]) (by simp [hsum_deg]) hb_nonpos
  rw [polynomial_succ_succ]
  exact hprec

@[simp] theorem polynomial_natDegree (n : ℕ) :
    (polynomial (n + 2)).natDegree = n + 2 := by
  rw [polynomial_succ_succ]
  let a : ℝ[X] :=
    C ((3 * ((n : ℝ) + 2) - 2) / (2 * ((n : ℝ) + 2))) * (1 + 2 * X)
  let b : ℝ[X] := C (-((n : ℝ) / (2 * ((n : ℝ) + 2))))
  have ha_scalar :
      0 < (3 * ((n : ℝ) + 2) - 2) / (2 * ((n : ℝ) + 2)) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    apply div_pos <;> nlinarith
  have ha_ne : a ≠ 0 := by
    apply mul_ne_zero (C_ne_zero.mpr ha_scalar.ne')
    intro hzero
    have hdegree : (1 + 2 * X : ℝ[X]).natDegree = 1 := by compute_degree!
    rw [hzero] at hdegree
    simp at hdegree
  have hleft : (a * legendre (n + 1)).natDegree = n + 2 := by
    rw [natDegree_mul ha_ne (legendre_posLeadingCoeff (n + 1)).ne_zero,
      show a.natDegree = 1 by
        simp only [a]
        rw [natDegree_C_mul ha_scalar.ne']
        compute_degree!,
      legendre_natDegree]
    lia
  have hright : (b * legendre n).natDegree < n + 2 :=
    lt_of_le_of_lt Polynomial.natDegree_mul_le (by simp [b])
  have hdegree : (b * legendre n).natDegree <
      (a * legendre (n + 1)).natDegree := by
    rw [hleft]
    exact hright
  exact (natDegree_add_eq_left_of_natDegree_lt hdegree).trans hleft

theorem polynomial_posLeadingCoeff (n : ℕ) :
    HasPosLeadingCoeff (polynomial (n + 2)) := by
  rw [polynomial_succ_succ]
  let a : ℝ[X] :=
    C ((3 * ((n : ℝ) + 2) - 2) / (2 * ((n : ℝ) + 2))) * (1 + 2 * X)
  let b : ℝ[X] := C (-((n : ℝ) / (2 * ((n : ℝ) + 2))))
  have ha_scalar :
      0 < (3 * ((n : ℝ) + 2) - 2) / (2 * ((n : ℝ) + 2)) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    apply div_pos <;> nlinarith
  have hlinear_pos : HasPosLeadingCoeff (1 + 2 * X : ℝ[X]) := by
    rw [show (1 + 2 * X : ℝ[X]) = C 2 * (X + C (1 / 2 : ℝ)) by
      simp only [one_div]
      rw [show (2 : ℝ[X]) = C (2 : ℝ) from (map_ofNat C 2).symm,
        mul_add, ← map_mul]
      grind]
    exact
      hasPosLeadingCoeff_C_mul (by norm_num)
        (hasPosLeadingCoeff_X_add_C (1 / 2))
  have ha_pos : HasPosLeadingCoeff a :=
    hasPosLeadingCoeff_C_mul ha_scalar hlinear_pos
  have hf_pos := legendre_posLeadingCoeff (n + 1)
  have haf_pos : HasPosLeadingCoeff (a * legendre (n + 1)) :=
    ha_pos.mul hf_pos
  have hdeg_right : (b * legendre n).natDegree <
      (a * legendre (n + 1)).natDegree := by
    have ha_deg : a.natDegree = 1 := by
      simp only [a]
      rw [natDegree_C_mul ha_scalar.ne']
      compute_degree!
    rw [natDegree_mul ha_pos.ne_zero hf_pos.ne_zero, ha_deg,
      legendre_natDegree]
    exact lt_of_le_of_lt Polynomial.natDegree_mul_le (by simp [b]; lia)
  exact hasPosLeadingCoeff_add_of_natDegree_lt_left hdeg_right haf_pos

private theorem polynomial_three_from_two :
    polynomial 3 =
      C (7 / 4 : ℝ) * (1 + 2 * X) * polynomial 2 +
        C (-3 / 4 : ℝ) * legendre 1 := by
  apply Polynomial.funext
  intro r
  simp [polynomial, legendre]
  ring

private theorem polynomial_basis (n : ℕ) :
    polynomial (n + 2) =
      C ((n : ℝ) / (2 * ((n : ℝ) + 1))) * legendre (n + 2) +
        C (((n : ℝ) + 2) / (2 * ((n : ℝ) + 1))) *
          (1 + 2 * X) * legendre (n + 1) := by
  rw [polynomial_succ_succ, legendre_succ_succ]
  apply Polynomial.funext
  intro r
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_one, eval_ofNat,
    eval_X]
  field_simp
  ring

private theorem polynomial_succ_decomposition (n : ℕ) (hn : 0 < n) :
    polynomial (n + 3) =
      C (((3 * (n : ℝ) + 7) * ((n : ℝ) + 1)) /
          ((n : ℝ) * ((n : ℝ) + 3))) * (1 + 2 * X) *
          polynomial (n + 2) +
        (C (-((n : ℝ) + 1) / (2 * ((n : ℝ) + 3))) -
          C (((3 * (n : ℝ) + 7) * ((n : ℝ) + 2)) /
            (2 * (n : ℝ) * ((n : ℝ) + 3))) * (1 + 2 * X) ^ 2) *
          legendre (n + 1) := by
  rw [polynomial_succ_succ (n + 1), polynomial_basis n]
  apply Polynomial.funext
  intro r
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_one, eval_ofNat,
    eval_X, eval_pow]
  have hnreal : (n : ℝ) ≠ 0 := by positivity
  field_simp [hnreal]
  push_cast
  ring

/-- Consecutive type-`D` quasi-Legendre rows strictly interlace. -/
theorem polynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (polynomial (n + 2)) (polynomial (n + 3)) := by
  have hinter := legendre_strictInterl_polynomial n
  have hg_pos := legendre_posLeadingCoeff (n + 1)
  have hQ_pos := polynomial_posLeadingCoeff (n + 1)
  have hdegree :
      (legendre (n + 1)).natDegree + 1 = (polynomial (n + 2)).natDegree := by
    rw [legendre_natDegree, polynomial_natDegree]
  have hdeg_lo :
      (polynomial (n + 2)).natDegree ≤ (polynomial (n + 3)).natDegree := by
    rw [polynomial_natDegree, polynomial_natDegree]
    lia
  have hdeg_hi :
      (polynomial (n + 3)).natDegree ≤ (polynomial (n + 2)).natDegree + 1 := by
    rw [polynomial_natDegree, polynomial_natDegree]
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [polynomial_three_from_two] at hQ_pos hdeg_lo hdeg_hi ⊢
    apply strictInterl_of_interlaces_evalCoeff_nonpos
      (f := polynomial 2) (g := legendre 1)
      (a := C (7 / 4 : ℝ) * (1 + 2 * X)) (b := C (-3 / 4 : ℝ))
      (hinter.toInterlaces hdegree) hg_pos hQ_pos hdeg_lo hdeg_hi
    intro r _
    simp only [eval_C]
    norm_num
  · rw [polynomial_succ_decomposition n hn] at hQ_pos hdeg_lo hdeg_hi ⊢
    apply strictInterl_of_interlaces_evalCoeff_nonpos
      (f := polynomial (n + 2)) (g := legendre (n + 1))
      (a := C (((3 * (n : ℝ) + 7) * ((n : ℝ) + 1)) /
          ((n : ℝ) * ((n : ℝ) + 3))) * (1 + 2 * X))
      (b := C (-((n : ℝ) + 1) / (2 * ((n : ℝ) + 3))) -
        C (((3 * (n : ℝ) + 7) * ((n : ℝ) + 2)) /
          (2 * (n : ℝ) * ((n : ℝ) + 3))) * (1 + 2 * X) ^ 2)
      (hinter.toInterlaces hdegree) hg_pos hQ_pos hdeg_lo hdeg_hi
    intro r _
    simp only [eval_sub, eval_C, eval_mul, eval_pow, eval_add, eval_one,
      eval_ofNat, eval_X]
    have hsecond :
        0 < ((3 * (n : ℝ) + 7) * ((n : ℝ) + 2)) /
          (2 * (n : ℝ) * ((n : ℝ) + 3)) := by positivity
    have hnegative :
        -((n : ℝ) + 1) / (2 * ((n : ℝ) + 3)) < 0 := by
      have hnum : -((n : ℝ) + 1) < 0 := by
        have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hden : 0 < 2 * ((n : ℝ) + 3) := by positivity
      exact div_neg_of_neg_of_pos hnum hden
    have hproduct :
        0 ≤ ((3 * (n : ℝ) + 7) * ((n : ℝ) + 2)) /
          (2 * (n : ℝ) * ((n : ℝ) + 3)) * (1 + 2 * r) ^ 2 :=
      mul_nonneg hsecond.le (sq_nonneg _)
    linarith

/-- Consecutive type-`D` quasi-Legendre rows interlace. -/
theorem polynomial_interlaces_succ (n : ℕ) :
    Interlaces (polynomial (n + 2)) (polynomial (n + 3)) :=
  (polynomial_strictInterl_succ n).toInterlaces (by
    rw [polynomial_natDegree, polynomial_natDegree])

private theorem X_mul_legendre_succ (n : ℕ) :
    X * legendre (n + 1) =
      C (((n : ℝ) + 2) / (2 * (2 * (n : ℝ) + 3))) * legendre (n + 2) -
        C (1 / 2 : ℝ) * legendre (n + 1) +
      C (((n : ℝ) + 1) / (2 * (2 * (n : ℝ) + 3))) * legendre n := by
  rw [legendre_succ_succ]
  apply Polynomial.funext
  intro r
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one,
    eval_ofNat]
  grind

private theorem X_sq_mul_legendre_succ_succ (n : ℕ) :
    X ^ 2 * legendre (n + 2) =
      C (((n : ℝ) + 3) / (2 * (2 * (n : ℝ) + 5))) *
          (X * legendre (n + 3)) -
        C (1 / 2 : ℝ) * (X * legendre (n + 2)) +
      C (((n : ℝ) + 2) / (2 * (2 * (n : ℝ) + 5))) *
          (X * legendre (n + 1)) := by
  have hmul := congrArg (fun p : ℝ[X] ↦ X * p) (X_mul_legendre_succ (n + 1))
  grind

private theorem X_mul_polynomial_succ_three (n : ℕ) :
    X * polynomial (n + 3) =
      C ((3 * ((n : ℝ) + 3) - 2) / (4 * ((n : ℝ) + 3) - 2)) *
          (X * legendre (n + 3)) +
        C (((n : ℝ) + 3) / (4 * ((n : ℝ) + 3) - 2)) *
          (X * legendre (n + 1)) := by
  rw [polynomial, show n + 3 - 2 = n + 1 by lia]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  ring

private theorem X_sq_mul_polynomial_succ_four (n : ℕ) :
    X ^ 2 * polynomial (n + 4) =
      C ((3 * ((n : ℝ) + 4) - 2) / (4 * ((n : ℝ) + 4) - 2)) *
          (X ^ 2 * legendre (n + 4)) +
        C (((n : ℝ) + 4) / (4 * ((n : ℝ) + 4) - 2)) *
          (X ^ 2 * legendre (n + 2)) := by
  rw [polynomial, show n + 4 - 2 = n + 2 by lia]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  ring

/-- The literal order-four update appearing in the generated OEIS file. -/
def nextRow (n : ℕ) (p3 p2 p1 p0 : ℝ[X]) : ℝ[X] :=
  (C ((13 + (5 / 2) * (n : ℝ)) / (6 + (n : ℝ))) +
      C ((26 + 5 * (n : ℝ)) / (6 + (n : ℝ))) * X) * p3 +
    (C ((-19 / 2 - (5 / 2) * (n : ℝ)) / (6 + (n : ℝ))) +
        C ((-14 - 4 * (n : ℝ)) / (6 + (n : ℝ))) * X +
        C ((-14 - 4 * (n : ℝ)) / (6 + (n : ℝ))) * X ^ 2) * p2 +
    (C ((3 + (3 / 2) * (n : ℝ)) / (6 + (n : ℝ))) +
        C ((6 + 3 * (n : ℝ)) / (6 + (n : ℝ))) * X) * p1 +
    C ((-1 / 2 - (1 / 2) * (n : ℝ)) / (6 + (n : ℝ))) * p0

/-- The quasi-Legendre model obeys the generated order-four recurrence. -/
theorem polynomial_recurrence (n : ℕ) :
    polynomial (n + 6) =
      nextRow n (polynomial (n + 5)) (polynomial (n + 4))
        (polynomial (n + 3)) (polynomial (n + 2)) := by
  let q2 := polynomial (n + 2)
  let q3 := polynomial (n + 3)
  let q4 := polynomial (n + 4)
  let q5 := polynomial (n + 5)
  have h5 :
      (C ((13 + (5 / 2) * (n : ℝ)) / (6 + (n : ℝ))) +
          C ((26 + 5 * (n : ℝ)) / (6 + (n : ℝ))) * X) * q5 =
        C ((13 + (5 / 2) * (n : ℝ)) / (6 + (n : ℝ))) * q5 +
          C ((26 + 5 * (n : ℝ)) / (6 + (n : ℝ))) * (X * q5) := by
    ring
  have h4 :
      (C ((-19 / 2 - (5 / 2) * (n : ℝ)) / (6 + (n : ℝ))) +
          C ((-14 - 4 * (n : ℝ)) / (6 + (n : ℝ))) * X +
          C ((-14 - 4 * (n : ℝ)) / (6 + (n : ℝ))) * X ^ 2) * q4 =
        C ((-19 / 2 - (5 / 2) * (n : ℝ)) / (6 + (n : ℝ))) * q4 +
          C ((-14 - 4 * (n : ℝ)) / (6 + (n : ℝ))) * (X * q4) +
          C ((-14 - 4 * (n : ℝ)) / (6 + (n : ℝ))) * (X ^ 2 * q4) := by
    ring
  have h3 :
      (C ((3 + (3 / 2) * (n : ℝ)) / (6 + (n : ℝ))) +
          C ((6 + 3 * (n : ℝ)) / (6 + (n : ℝ))) * X) * q3 =
        C ((3 + (3 / 2) * (n : ℝ)) / (6 + (n : ℝ))) * q3 +
          C ((6 + 3 * (n : ℝ)) / (6 + (n : ℝ))) * (X * q3) := by
    ring
  change polynomial (n + 6) =
    (C ((13 + (5 / 2) * (n : ℝ)) / (6 + (n : ℝ))) +
      C ((26 + 5 * (n : ℝ)) / (6 + (n : ℝ))) * X) * q5 +
    (C ((-19 / 2 - (5 / 2) * (n : ℝ)) / (6 + (n : ℝ))) +
      C ((-14 - 4 * (n : ℝ)) / (6 + (n : ℝ))) * X +
      C ((-14 - 4 * (n : ℝ)) / (6 + (n : ℝ))) * X ^ 2) * q4 +
    (C ((3 + (3 / 2) * (n : ℝ)) / (6 + (n : ℝ))) +
      C ((6 + 3 * (n : ℝ)) / (6 + (n : ℝ))) * X) * q3 +
    C ((-1 / 2 - (1 / 2) * (n : ℝ)) / (6 + (n : ℝ))) * q2
  rw [h5, h4, h3]
  dsimp [q2, q3, q4, q5]
  rw [X_mul_polynomial_succ_three (n + 2),
    X_mul_polynomial_succ_three (n + 1),
    X_sq_mul_polynomial_succ_four n,
    X_mul_polynomial_succ_three n]
  rw [X_sq_mul_legendre_succ_succ (n + 2),
    X_sq_mul_legendre_succ_succ n]
  rw [X_mul_legendre_succ (n + 4), X_mul_legendre_succ (n + 3),
    X_mul_legendre_succ (n + 2), X_mul_legendre_succ (n + 1),
    X_mul_legendre_succ n]
  simp only [polynomial, show n + 6 - 2 = n + 4 by lia,
    show n + 5 - 2 = n + 3 by lia, show n + 4 - 2 = n + 2 by lia,
    show n + 3 - 2 = n + 1 by lia, show n + 2 - 2 = n by lia,
    Nat.cast_add, Nat.cast_ofNat, one_div, Nat.cast_one]
  apply Polynomial.funext
  intro r
  simp only [eval_add, eval_sub, eval_mul, eval_C]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  ring_nf
  field_simp
  ring

private theorem polynomial_two :
    polynomial 2 = 1 + 4 * X + 4 * X ^ 2 := by
  apply Polynomial.funext
  intro r
  simp only [polynomial, legendre, eval_add, eval_sub, eval_mul, eval_C,
    eval_X, eval_one, eval_pow, eval_ofNat]
  norm_num [legendre]
  ring

private theorem polynomial_three :
    polynomial 3 = 1 + 9 * X + 21 * X ^ 2 + 14 * X ^ 3 := by
  apply Polynomial.funext
  intro r
  simp only [polynomial, legendre, eval_add, eval_sub, eval_mul, eval_C,
    eval_X, eval_one, eval_pow, eval_ofNat]
  norm_num [legendre]
  ring

private theorem polynomial_four :
    polynomial 4 = 1 + 16 * X + 66 * X ^ 2 + 100 * X ^ 3 + 50 * X ^ 4 := by
  apply Polynomial.funext
  intro r
  simp only [polynomial, legendre, eval_add, eval_sub, eval_mul, eval_C,
    eval_X, eval_one, eval_pow, eval_ofNat]
  norm_num [legendre]
  ring

private theorem polynomial_five :
    polynomial 5 =
      1 + 25 * X + 160 * X ^ 2 + 410 * X ^ 3 + 455 * X ^ 4 + 182 * X ^ 5 := by
  apply Polynomial.funext
  intro r
  simp only [polynomial, legendre, eval_add, eval_sub, eval_mul, eval_C,
    eval_X, eval_one, eval_pow, eval_ofNat]
  norm_num [legendre]
  ring

/-- A sequence with the generated A080721 initial rows and order-four update
has split rows. -/
@[rr_row_model]
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1 + 4 * X + 4 * X ^ 2)
    (hone : P 1 = 1 + 9 * X + 21 * X ^ 2 + 14 * X ^ 3)
    (htwo : P 2 = 1 + 16 * X + 66 * X ^ 2 + 100 * X ^ 3 + 50 * X ^ 4)
    (hthree : P 3 =
      1 + 25 * X + 160 * X ^ 2 + 410 * X ^ 3 + 455 * X ^ 4 + 182 * X ^ 5)
    (hrec : ∀ n : ℕ,
      P (n + 4) = nextRow n (P (n + 3)) (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_four_recurrence
    (P := P) (Q := fun m => polynomial (m + 2)) nextRow
    (hzero.trans polynomial_two.symm) (hone.trans polynomial_three.symm)
    (htwo.trans polynomial_four.symm) (hthree.trans polynomial_five.symm)
    hrec (fun m => by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      polynomial_recurrence m)
  rw [heq n]
  exact (polynomial_strictInterl_succ n).1.2

/-- Consecutive rows of a sequence with the generated A080721 initial rows and
order-four update interlace. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1 + 4 * X + 4 * X ^ 2)
    (hone : P 1 = 1 + 9 * X + 21 * X ^ 2 + 14 * X ^ 3)
    (htwo : P 2 = 1 + 16 * X + 66 * X ^ 2 + 100 * X ^ 3 + 50 * X ^ 4)
    (hthree : P 3 =
      1 + 25 * X + 160 * X ^ 2 + 410 * X ^ 3 + 455 * X ^ 4 + 182 * X ^ 5)
    (hrec : ∀ n : ℕ,
      P (n + 4) = nextRow n (P (n + 3)) (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_four_recurrence
    (P := P) (Q := fun m => polynomial (m + 2)) nextRow
    (hzero.trans polynomial_two.symm) (hone.trans polynomial_three.symm)
    (htwo.trans polynomial_four.symm) (hthree.trans polynomial_five.symm)
    hrec (fun m => by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      polynomial_recurrence m)
  rw [heq n, heq (n + 1)]
  exact polynomial_interlaces_succ n

end RealRooted.Applications.OEIS.A080721
