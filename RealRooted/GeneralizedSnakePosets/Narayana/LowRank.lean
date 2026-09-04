import RealRooted.GeneralizedSnakePosets.Narayana.RankSix

/-!
# Low-rank modified-Narayana interlacing certificates

This module contains the explicit ranks-three-through-five root certificates
and assembles the checked rank-at-most-six Braun--Jal Lemma 3.3 interface.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- The `n = 3` case of Braun--Jal Lemma 3.3, in the stricter differ-by-one
interlacing form. -/
theorem lemma33AuxiliaryGInterlaces_modified_three_interlaces :
    Interlaces (FiniteSkewBoard.auxiliaryG 3) (modifiedNarayanaPolynomial 3) := by
  let a : ℝ := (-(5 : ℝ) - Real.sqrt (21 : ℝ)) / 2
  let b : ℝ := -(1 : ℝ)
  let c : ℝ := (-(5 : ℝ) + Real.sqrt (21 : ℝ)) / 2
  let u : ℝ := (-(8 : ℝ) - Real.sqrt (28 : ℝ)) / 6
  let v : ℝ := (-(8 : ℝ) + Real.sqrt (28 : ℝ)) / 6
  have hGform :
      FiniteSkewBoard.auxiliaryG 3 =
        C (3 : ℝ) * X ^ 2 + C (8 : ℝ) * X + C (3 : ℝ) := by
    rw [FiniteSkewBoard.auxiliaryG_three]
    have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
    have hC8 : (C (8 : ℝ) : ℝ[X]) = 8 := Polynomial.C_eq_natCast (R := ℝ) 8
    rw [hC3, hC8]
    ring_nf
  have hGdeg : (FiniteSkewBoard.auxiliaryG 3).natDegree = 2 := by
    rw [FiniteSkewBoard.auxiliaryG_three]
    compute_degree!
  have hG_ne : FiniteSkewBoard.auxiliaryG 3 ≠ 0 := by
    intro hzero
    rw [hzero] at hGdeg
    norm_num at hGdeg
  have hG_splits : (FiniteSkewBoard.auxiliaryG 3).Splits := by
    rw [hGform]
    exact quadraticPoly_splits_of_discrim_nonneg (by norm_num) (by norm_num [discrim])
  have hG_roots : (FiniteSkewBoard.auxiliaryG 3).roots = (↑[u, v] : Multiset ℝ) := by
    rw [hGform]
    rw [roots_quadratic_posLead (a := (3 : ℝ)) (b := (8 : ℝ))
      (c := (3 : ℝ)) (by norm_num) (by norm_num)]
    dsimp [u, v]
    norm_num
    rfl
  have hPfactor :
      modifiedNarayanaPolynomial 3 =
        (X - C (-(1 : ℝ))) *
          (C (1 : ℝ) * X ^ 2 + C (5 : ℝ) * X + C (1 : ℝ)) := by
    rw [modifiedNarayanaPolynomial_three]
    have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
    have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
    have hCneg1 : (C (-(1 : ℝ)) : ℝ[X]) = -1 := by simp
    rw [hC5, hC6, hCneg1]
    norm_num
    ring_nf
  have hquad_deg :
      (C (1 : ℝ) * X ^ 2 + C (5 : ℝ) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquad_ne :
      (C (1 : ℝ) * X ^ 2 + C (5 : ℝ) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquad_deg
    norm_num at hquad_deg
  have hP_roots :
      (modifiedNarayanaPolynomial 3).roots = (↑[a, b, c] : Multiset ℝ) := by
    rw [hPfactor]
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero (-(1 : ℝ))) hquad_ne)]
    rw [roots_X_sub_C]
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := (5 : ℝ))
      (c := (1 : ℝ)) (by norm_num) (by norm_num)]
    dsimp [a, b, c]
    norm_num
    rw [Multiset.cons_swap]
    rfl
  have hP_ne : modifiedNarayanaPolynomial 3 ≠ 0 := modifiedNarayanaPolynomial_ne_zero 3
  have hP_splits : (modifiedNarayanaPolynomial 3).Splits :=
    modifiedNarayanaPolynomial_splits 3
  have hPdeg : (modifiedNarayanaPolynomial 3).natDegree = 3 := by
    rw [modifiedNarayanaPolynomial_natDegree]
  have h21 : Real.sqrt (21 : ℝ) ^ 2 = (21 : ℝ) := Real.sq_sqrt (by norm_num)
  have h28 : Real.sqrt (28 : ℝ) ^ 2 = (28 : ℝ) := Real.sq_sqrt (by norm_num)
  have h21nonneg : 0 ≤ Real.sqrt (21 : ℝ) := Real.sqrt_nonneg _
  have h28nonneg : 0 ≤ Real.sqrt (28 : ℝ) := Real.sqrt_nonneg _
  have h3le21 : (3 : ℝ) ≤ Real.sqrt (21 : ℝ) := by nlinarith
  have h2le28 : (2 : ℝ) ≤ Real.sqrt (28 : ℝ) := by nlinarith
  have hab : a ≤ b := by
    dsimp [a, b]
    nlinarith
  have hbc : b ≤ c := by
    dsimp [b, c]
    nlinarith
  have huv : u ≤ v := by
    dsimp [u, v]
    nlinarith
  have hau : a ≤ u := by
    dsimp [a, u]
    nlinarith
  have hub : u ≤ b := by
    dsimp [u, b]
    nlinarith
  have hbv : b ≤ v := by
    dsimp [b, v]
    nlinarith
  have hvc : v ≤ c := by
    dsimp [v, c]
    nlinarith [sq_nonneg (3 * Real.sqrt (21 : ℝ) - (7 + Real.sqrt (28 : ℝ)))]
  exact interlaces_of_quadratic_cubic_root_lists hP_ne hP_splits hG_ne hG_splits
    hPdeg hGdeg hP_roots hG_roots hab hbc huv hau hub hbv hvc

/-- The `n = 3` case of Braun--Jal Lemma 3.3, for the concrete modified
Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_three :
    Prec (FiniteSkewBoard.auxiliaryG 3) (modifiedNarayanaPolynomial 3) := by
  exact lemma33AuxiliaryGInterlaces_modified_three_interlaces.toPrec

/-- The checked initial cases `n = 1, 2, 3` of Braun--Jal Lemma 3.3, for the
concrete modified Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_of_le_three
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₃ : n ≤ 3) :
    Prec (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) := by
  interval_cases n
  · exact lemma33AuxiliaryGInterlaces_modified_base
  · exact lemma33AuxiliaryGInterlaces_modified_two
  · exact lemma33AuxiliaryGInterlaces_modified_three

/-- The `n = 4` case of Braun--Jal Lemma 3.3, in the stricter differ-by-one
interlacing form. -/
theorem lemma33AuxiliaryGInterlaces_modified_four_interlaces :
    Interlaces (FiniteSkewBoard.auxiliaryG 4) (modifiedNarayanaPolynomial 4) := by
  let s : ℝ := Real.sqrt (7 : ℝ)
  let α : ℝ := Real.sqrt ((28 : ℝ) + 10 * s)
  let β : ℝ := Real.sqrt ((28 : ℝ) - 10 * s)
  let γ : ℝ := Real.sqrt (12 : ℝ)
  let a : ℝ := (-(5 : ℝ) - s - α) / 2
  let b : ℝ := (-(5 : ℝ) + s - β) / 2
  let c : ℝ := (-(5 : ℝ) + s + β) / 2
  let d : ℝ := (-(5 : ℝ) - s + α) / 2
  let u : ℝ := (-(4 : ℝ) - γ) / 2
  let v : ℝ := -(1 : ℝ)
  let w : ℝ := (-(4 : ℝ) + γ) / 2
  have hGfactor :
      FiniteSkewBoard.auxiliaryG 4 =
        C (4 : ℝ) * (X - C v) *
          (C (1 : ℝ) * X ^ 2 + C (4 : ℝ) * X + C (1 : ℝ)) := by
    rw [FiniteSkewBoard.auxiliaryG_four]
    dsimp [v]
    have hC1 : (C (1 : ℝ) : ℝ[X]) = 1 := by simp
    have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
    have hC20 : (C (20 : ℝ) : ℝ[X]) = 20 :=
      Polynomial.C_eq_natCast (R := ℝ) 20
    have hCneg1 : (C (-(1 : ℝ)) : ℝ[X]) = -1 := by simp
    rw [hC1, hC4, hC20, hCneg1]
    ring_nf
  have hGdeg : (FiniteSkewBoard.auxiliaryG 4).natDegree = 3 := by
    rw [FiniteSkewBoard.auxiliaryG_four]
    compute_degree!
  have hG_ne : FiniteSkewBoard.auxiliaryG 4 ≠ 0 := by
    intro hzero
    rw [hzero] at hGdeg
    norm_num at hGdeg
  have hquadG_deg :
      (C (1 : ℝ) * X ^ 2 + C (4 : ℝ) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquadG_ne :
      (C (1 : ℝ) * X ^ 2 + C (4 : ℝ) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquadG_deg
    norm_num at hquadG_deg
  have hXv_ne : X - C v ≠ 0 := X_sub_C_ne_zero v
  have hG_splits : (FiniteSkewBoard.auxiliaryG 4).Splits := by
    rw [hGfactor]
    exact
      ((Polynomial.Splits.C (4 : ℝ)).mul (Polynomial.Splits.X_sub_C v)).mul
        (quadraticPoly_splits_of_discrim_nonneg (by norm_num)
          (by norm_num [discrim]))
  have hG_roots :
      (FiniteSkewBoard.auxiliaryG 4).roots = (↑[u, v, w] : Multiset ℝ) := by
    rw [hGfactor]
    rw [roots_mul
      (mul_ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num)) hXv_ne)
        hquadG_ne)]
    rw [roots_mul (mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num)) hXv_ne)]
    rw [roots_C, roots_X_sub_C]
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := (4 : ℝ))
      (c := (1 : ℝ)) (by norm_num) (by norm_num)]
    dsimp [u, v, w, γ]
    norm_num
    rfl
  have hPfactor :
      modifiedNarayanaPolynomial 4 =
        (C (1 : ℝ) * X ^ 2 + C ((5 : ℝ) + s) * X + C (1 : ℝ)) *
          (C (1 : ℝ) * X ^ 2 + C ((5 : ℝ) - s) * X + C (1 : ℝ)) := by
    rw [modifiedNarayanaPolynomial_four]
    dsimp [s]
    have hs_sq' : Real.sqrt (7 : ℝ) ^ 2 = (7 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hCsq : (C (Real.sqrt (7 : ℝ)) : ℝ[X]) ^ 2 = C (7 : ℝ) := by rw [← map_pow, hs_sq']
    have hC1 : (C (1 : ℝ) : ℝ[X]) = 1 := by simp
    have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
    have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
    have hC10 : (C (10 : ℝ) : ℝ[X]) = 10 :=
      Polynomial.C_eq_natCast (R := ℝ) 10
    have hC20 : (C (20 : ℝ) : ℝ[X]) = 20 :=
      Polynomial.C_eq_natCast (R := ℝ) 20
    rw [hC1, hC10, hC20]
    norm_num
    ring_nf
    rw [hCsq, hC5, hC7]
    ring_nf
  have hquadA_deg :
      (C (1 : ℝ) * X ^ 2 + C ((5 : ℝ) + s) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquadA_ne :
      (C (1 : ℝ) * X ^ 2 + C ((5 : ℝ) + s) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquadA_deg
    norm_num at hquadA_deg
  have hquadB_deg :
      (C (1 : ℝ) * X ^ 2 + C ((5 : ℝ) - s) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquadB_ne :
      (C (1 : ℝ) * X ^ 2 + C ((5 : ℝ) - s) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquadB_deg
    norm_num at hquadB_deg
  have hs_sq : s ^ 2 = (7 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hdiscA :
      ((5 : ℝ) + s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) = (28 : ℝ) + 10 * s := by
    nlinarith [hs_sq]
  have hdiscB :
      ((5 : ℝ) - s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) = (28 : ℝ) - 10 * s := by
    nlinarith [hs_sq]
  have hdiscA_nonneg :
      0 ≤ ((5 : ℝ) + s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) := by
    rw [hdiscA]
    positivity
  have hdiscB_nonneg :
      0 ≤ ((5 : ℝ) - s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) := by
    rw [hdiscB]
    apply sub_nonneg.mpr
    nlinarith [sq_nonneg (s - 5)]
  have hP_roots :
      (modifiedNarayanaPolynomial 4).roots = (↑[a, b, c, d] : Multiset ℝ) := by
    rw [hPfactor]
    rw [roots_mul (mul_ne_zero hquadA_ne hquadB_ne)]
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := ((5 : ℝ) + s))
      (c := (1 : ℝ)) (by norm_num) hdiscA_nonneg]
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := ((5 : ℝ) - s))
      (c := (1 : ℝ)) (by norm_num) hdiscB_nonneg]
    rw [hdiscA, hdiscB]
    norm_num
    dsimp [a, b, c, d, α, β]
    ring_nf
    change
      (↑[-5 / 2 + s * (1 / 2) + Real.sqrt (28 - s * 10) * (-1 / 2),
        -5 / 2 + s * (-1 / 2) + Real.sqrt (28 + s * 10) * (-1 / 2),
        -5 / 2 + s * (-1 / 2) + Real.sqrt (28 + s * 10) * (1 / 2),
        -5 / 2 + s * (1 / 2) + Real.sqrt (28 - s * 10) * (1 / 2)] :
        Multiset ℝ) = _
    rw [Multiset.coe_eq_coe]
    exact
      List.Perm.trans (List.Perm.swap _ _ _)
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _)))
  have hP_ne : modifiedNarayanaPolynomial 4 ≠ 0 := modifiedNarayanaPolynomial_ne_zero 4
  have hP_splits : (modifiedNarayanaPolynomial 4).Splits :=
    modifiedNarayanaPolynomial_splits 4
  have hPdeg : (modifiedNarayanaPolynomial 4).natDegree = 4 := by
    rw [modifiedNarayanaPolynomial_natDegree]
  have hα_sq : α ^ 2 = (28 : ℝ) + 10 * s := by
    dsimp [α]
    exact Real.sq_sqrt (by positivity)
  have hβ_sq : β ^ 2 = (28 : ℝ) - 10 * s := by
    dsimp [β]
    apply Real.sq_sqrt
    nlinarith [sq_nonneg (s - 5)]
  have hγ_sq : γ ^ 2 = (12 : ℝ) := by
    dsimp [γ]
    exact Real.sq_sqrt (by norm_num)
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact Real.sqrt_nonneg _
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    exact Real.sqrt_nonneg _
  have hγ_nonneg : 0 ≤ γ := by
    dsimp [γ]
    exact Real.sqrt_nonneg _
  have hs_ge2 : (2 : ℝ) ≤ s := by
    dsimp [s]
    exact Real.le_sqrt_of_sq_le (by norm_num)
  have hs_ge5div2 : (5 / 2 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hs_le3 : s ≤ (3 : ℝ) := by
    dsimp [s]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hs_le8div3 : s ≤ (8 / 3 : ℝ) := by
    dsimp [s]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hβ_le2 : β ≤ (2 : ℝ) := by
    dsimp [β]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [hs_ge5div2]
  have hβ_ge1 : (1 : ℝ) ≤ β := by
    dsimp [β]
    apply Real.le_sqrt_of_sq_le
    nlinarith [hs_le8div3]
  have hγ_ge1 : (1 : ℝ) ≤ γ := by
    dsimp [γ]
    exact Real.le_sqrt_of_sq_le (by norm_num)
  have hγ_ge2 : (2 : ℝ) ≤ γ := by
    dsimp [γ]
    exact Real.le_sqrt_of_sq_le (by norm_num)
  have hγ_le4 : γ ≤ (4 : ℝ) := by
    dsimp [γ]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hα_ge1 : (1 : ℝ) ≤ α := by
    dsimp [α]
    apply Real.le_sqrt_of_sq_le
    nlinarith [hs_nonneg]
  have h2s2_leα : 2 * s + 2 ≤ α := by
    dsimp [α]
    apply Real.le_sqrt_of_sq_le
    nlinarith [hs_sq, hs_ge2]
  have hsumβ_leα : 2 * s + β ≤ α := by linarith
  have hsumβγ_le : s + β - 1 ≤ γ := by
    dsimp [γ]
    apply Real.le_sqrt_of_sq_le
    have hs1_nonneg : 0 ≤ s - 1 := by linarith
    have hmul : β * (s - 1) ≤ 2 * (s - 1) :=
      mul_le_mul_of_nonneg_right hβ_le2 hs1_nonneg
    nlinarith [hs_sq, hβ_sq, hmul, hs_ge5div2]
  have hsumγα_le : γ + s + 1 ≤ α := by
    dsimp [α]
    apply Real.le_sqrt_of_sq_le
    have hsp1_nonneg : 0 ≤ s + 1 := by positivity
    have hmul : γ * (s + 1) ≤ 4 * (s + 1) :=
      mul_le_mul_of_nonneg_right hγ_le4 hsp1_nonneg
    nlinarith [hs_sq, hγ_sq, hmul]
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hbc : b ≤ c := by
    dsimp [b, c]
    linarith
  have hcd : c ≤ d := by
    dsimp [c, d]
    linarith
  have huv : u ≤ v := by
    dsimp [u, v]
    linarith
  have hvw : v ≤ w := by
    dsimp [v, w]
    linarith
  have hau : a ≤ u := by
    dsimp [a, u]
    linarith
  have hub : u ≤ b := by
    dsimp [u, b]
    linarith
  have hbv : b ≤ v := by
    dsimp [b, v]
    linarith
  have hvc : v ≤ c := by
    dsimp [v, c]
    linarith
  have hcw : c ≤ w := by
    dsimp [c, w]
    linarith
  have hwd : w ≤ d := by
    dsimp [w, d]
    linarith
  exact interlaces_of_cubic_quartic_root_lists hP_ne hP_splits hG_ne hG_splits
    hPdeg hGdeg hP_roots hG_roots hab hbc hcd huv hvw hau hub hbv hvc hcw hwd

/-- The `n = 4` case of Braun--Jal Lemma 3.3, for the concrete modified
Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_four :
    Prec (FiniteSkewBoard.auxiliaryG 4) (modifiedNarayanaPolynomial 4) := by
  exact lemma33AuxiliaryGInterlaces_modified_four_interlaces.toPrec

/-- The checked initial cases `n = 1, 2, 3, 4` of Braun--Jal Lemma 3.3, for the
concrete modified Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_of_le_four
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₄ : n ≤ 4) :
    Prec (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) := by
  interval_cases n
  · exact lemma33AuxiliaryGInterlaces_modified_base
  · exact lemma33AuxiliaryGInterlaces_modified_two
  · exact lemma33AuxiliaryGInterlaces_modified_three
  · exact lemma33AuxiliaryGInterlaces_modified_four

/-- The `n = 5` case of Braun--Jal Lemma 3.3, in the stricter differ-by-one
interlacing form. -/
theorem lemma33AuxiliaryGInterlaces_modified_five_interlaces :
    Interlaces (FiniteSkewBoard.auxiliaryG 5) (modifiedNarayanaPolynomial 5) := by
  let s : ℝ := Real.sqrt (3 : ℝ)
  let t : ℝ := Real.sqrt (15 : ℝ)
  let α : ℝ := Real.sqrt ((15 : ℝ) + 8 * s)
  let β : ℝ := Real.sqrt ((15 : ℝ) - 8 * s)
  let γ : ℝ := Real.sqrt ((60 : ℝ) + 14 * t)
  let δ : ℝ := Real.sqrt ((60 : ℝ) - 14 * t)
  let a : ℝ := (-(7 : ℝ) - t - γ) / 2
  let b : ℝ := (-(7 : ℝ) + t - δ) / 2
  let c : ℝ := -(1 : ℝ)
  let d : ℝ := (-(7 : ℝ) + t + δ) / 2
  let e : ℝ := (-(7 : ℝ) - t + γ) / 2
  let u : ℝ := (-(4 : ℝ) - s - α) / 2
  let v : ℝ := (-(4 : ℝ) + s - β) / 2
  let w : ℝ := (-(4 : ℝ) + s + β) / 2
  let z : ℝ := (-(4 : ℝ) - s + α) / 2
  have hGfactor :
      FiniteSkewBoard.auxiliaryG 5 =
        C (5 : ℝ) *
          ((C (1 : ℝ) * X ^ 2 + C ((4 : ℝ) + s) * X + C (1 : ℝ)) *
            (C (1 : ℝ) * X ^ 2 + C ((4 : ℝ) - s) * X + C (1 : ℝ))) := by
    rw [FiniteSkewBoard.auxiliaryG_five]
    dsimp [s]
    have hs_sq' : Real.sqrt (3 : ℝ) ^ 2 = (3 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hCsq : (C (Real.sqrt (3 : ℝ)) : ℝ[X]) ^ 2 = C (3 : ℝ) := by rw [← map_pow, hs_sq']
    have hC1 : (C (1 : ℝ) : ℝ[X]) = 1 := by simp
    have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
    have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
    have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
    have hC40 : (C (40 : ℝ) : ℝ[X]) = 40 :=
      Polynomial.C_eq_natCast (R := ℝ) 40
    have hC75 : (C (75 : ℝ) : ℝ[X]) = 75 :=
      Polynomial.C_eq_natCast (R := ℝ) 75
    rw [hC1, hC5, hC40, hC75]
    norm_num
    ring_nf
    rw [hCsq, hC3, hC4]
    ring_nf
  have hPfactor :
      modifiedNarayanaPolynomial 5 =
        (C (1 : ℝ) * X ^ 2 + C ((7 : ℝ) + t) * X + C (1 : ℝ)) *
          (C (1 : ℝ) * X ^ 2 + C ((7 : ℝ) - t) * X + C (1 : ℝ)) *
            (X - C c) := by
    rw [modifiedNarayanaPolynomial_five]
    dsimp [t, c]
    have ht_sq' : Real.sqrt (15 : ℝ) ^ 2 = (15 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hCsq : (C (Real.sqrt (15 : ℝ)) : ℝ[X]) ^ 2 = C (15 : ℝ) := by
      rw [← map_pow, ht_sq']
    have hC1 : (C (1 : ℝ) : ℝ[X]) = 1 := by simp
    have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
    have hC15 : (C (15 : ℝ) : ℝ[X]) = 15 :=
      Polynomial.C_eq_natCast (R := ℝ) 15
    have hC50 : (C (50 : ℝ) : ℝ[X]) = 50 :=
      Polynomial.C_eq_natCast (R := ℝ) 50
    have hCneg1 : (C (-(1 : ℝ)) : ℝ[X]) = -1 := by simp
    rw [hC1, hC50, hCneg1]
    norm_num
    ring_nf
    rw [hCsq, hC7, hC15]
    ring_nf
  have hGdeg : (FiniteSkewBoard.auxiliaryG 5).natDegree = 4 := by
    rw [FiniteSkewBoard.auxiliaryG_five]
    compute_degree!
  have hG_ne : FiniteSkewBoard.auxiliaryG 5 ≠ 0 := by
    intro hzero
    rw [hzero] at hGdeg
    norm_num at hGdeg
  have hquadGA_deg :
      (C (1 : ℝ) * X ^ 2 + C ((4 : ℝ) + s) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquadGA_ne :
      (C (1 : ℝ) * X ^ 2 + C ((4 : ℝ) + s) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquadGA_deg
    norm_num at hquadGA_deg
  have hquadGB_deg :
      (C (1 : ℝ) * X ^ 2 + C ((4 : ℝ) - s) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquadGB_ne :
      (C (1 : ℝ) * X ^ 2 + C ((4 : ℝ) - s) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquadGB_deg
    norm_num at hquadGB_deg
  have hquadPA_deg :
      (C (1 : ℝ) * X ^ 2 + C ((7 : ℝ) + t) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquadPA_ne :
      (C (1 : ℝ) * X ^ 2 + C ((7 : ℝ) + t) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquadPA_deg
    norm_num at hquadPA_deg
  have hquadPB_deg :
      (C (1 : ℝ) * X ^ 2 + C ((7 : ℝ) - t) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquadPB_ne :
      (C (1 : ℝ) * X ^ 2 + C ((7 : ℝ) - t) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquadPB_deg
    norm_num at hquadPB_deg
  have hXc_ne : X - C c ≠ 0 := X_sub_C_ne_zero c
  have hs_sq : s ^ 2 = (3 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have ht_sq : t ^ 2 = (15 : ℝ) := by
    dsimp [t]
    exact Real.sq_sqrt (by norm_num)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact Real.sqrt_nonneg _
  have hs_ge6div5 : (6 / 5 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hs_ge8div5 : (8 / 5 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hs_ge69div40 : (69 / 40 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hs_le7div4 : s ≤ (7 / 4 : ℝ) := by
    dsimp [s]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hs_le2 : s ≤ (2 : ℝ) := by linarith
  have ht_ge1 : (1 : ℝ) ≤ t := by
    dsimp [t]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have ht_ge15div4 : (15 / 4 : ℝ) ≤ t := by
    dsimp [t]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have ht_ge77div20 : (77 / 20 : ℝ) ≤ t := by
    dsimp [t]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have ht_le31div8 : t ≤ (31 / 8 : ℝ) := by
    dsimp [t]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have ht_le4 : t ≤ (4 : ℝ) := by linarith
  have h15_sub_8s_nonneg : 0 ≤ (15 : ℝ) - 8 * s := by nlinarith only [hs_le7div4]
  have h60_sub_14t_nonneg : 0 ≤ (60 : ℝ) - 14 * t := by nlinarith only [ht_le4]
  have hα_sq : α ^ 2 = (15 : ℝ) + 8 * s := by
    dsimp [α]
    exact Real.sq_sqrt (by positivity)
  have hβ_sq : β ^ 2 = (15 : ℝ) - 8 * s := by
    dsimp [β]
    exact Real.sq_sqrt h15_sub_8s_nonneg
  have hγ_sq : γ ^ 2 = (60 : ℝ) + 14 * t := by
    dsimp [γ]
    exact Real.sq_sqrt (by positivity)
  have hδ_sq : δ ^ 2 = (60 : ℝ) - 14 * t := by
    dsimp [δ]
    exact Real.sq_sqrt h60_sub_14t_nonneg
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact Real.sqrt_nonneg _
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    exact Real.sqrt_nonneg _
  have hγ_nonneg : 0 ≤ γ := by
    dsimp [γ]
    exact Real.sqrt_nonneg _
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    exact Real.sqrt_nonneg _
  have hα_ge5 : (5 : ℝ) ≤ α := by
    dsimp [α]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hs_ge8div5]
  have hα_ge21div4 : (21 / 4 : ℝ) ≤ α := by
    dsimp [α]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hs_ge8div5]
  have hα_le6 : α ≤ (6 : ℝ) := by
    dsimp [α]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [hs_le7div4]
  have hα_le27div5 : α ≤ (27 / 5 : ℝ) := by
    dsimp [α]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [hs_le7div4]
  have hβ_le3div2 : β ≤ (3 / 2 : ℝ) := by
    dsimp [β]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [hs_ge8div5]
  have hβ_le11div10 : β ≤ (11 / 10 : ℝ) := by
    dsimp [β]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [hs_ge69div40]
  have hβ_ge1 : (1 : ℝ) ≤ β := by
    dsimp [β]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hs_le7div4]
  have hγ_ge3 : (3 : ℝ) ≤ γ := by
    dsimp [γ]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [ht_nonneg]
  have hγ_ge6 : (6 : ℝ) ≤ γ := by
    dsimp [γ]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [ht_nonneg]
  have hγ_ge533div50 : (533 / 50 : ℝ) ≤ γ := by
    dsimp [γ]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [ht_ge77div20]
  have hδ_ge2 : (2 : ℝ) ≤ δ := by
    dsimp [δ]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [ht_le4]
  have hδ_le5div2 : δ ≤ (5 / 2 : ℝ) := by
    dsimp [δ]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [ht_ge77div20]
  have hδ_le3 : δ ≤ (3 : ℝ) := by
    dsimp [δ]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [ht_ge15div4]
  have h2sβ_leα : 2 * s + β ≤ α := by linarith
  have h2tδ_leγ : 2 * t + δ ≤ γ := by linarith
  have htwo_sub_s_leβ : 2 - s ≤ β := by linarith only [hs_ge6div5, hβ_ge1]
  have hG_splits : (FiniteSkewBoard.auxiliaryG 5).Splits := by
    rw [hGfactor]
    refine (Polynomial.Splits.C (5 : ℝ)).mul ?_
    refine
      (quadraticPoly_splits_of_discrim_nonneg (by norm_num) ?_).mul
        (quadraticPoly_splits_of_discrim_nonneg (by norm_num) ?_)
    · norm_num [discrim]
      nlinarith only [hs_sq, hs_nonneg]
    · norm_num [discrim]
      nlinarith only [hs_sq, h15_sub_8s_nonneg]
  have hG_roots :
      (FiniteSkewBoard.auxiliaryG 5).roots = (↑[u, v, w, z] : Multiset ℝ) := by
    rw [hGfactor]
    rw [roots_mul
      (mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num))
        (mul_ne_zero hquadGA_ne hquadGB_ne))]
    rw [roots_C, roots_mul (mul_ne_zero hquadGA_ne hquadGB_ne)]
    have hdiscA : ((4 : ℝ) + s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) =
        (15 : ℝ) + 8 * s := by
      nlinarith only [hs_sq]
    have hdiscA_nonneg :
        0 ≤ ((4 : ℝ) + s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) := by
      rw [hdiscA]
      positivity
    have hdiscB : ((4 : ℝ) - s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) =
        (15 : ℝ) - 8 * s := by
      nlinarith only [hs_sq]
    have hdiscB_nonneg :
        0 ≤ ((4 : ℝ) - s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) := by
      rw [hdiscB]
      exact h15_sub_8s_nonneg
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := ((4 : ℝ) + s))
      (c := (1 : ℝ)) (by norm_num) hdiscA_nonneg]
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := ((4 : ℝ) - s))
      (c := (1 : ℝ)) (by norm_num) hdiscB_nonneg]
    rw [hdiscA, hdiscB]
    dsimp [u, v, w, z, α, β]
    norm_num
    change
      (↑[(s - 4 - Real.sqrt (15 - 8 * s)) / 2,
          (-s + -4 - Real.sqrt (15 + 8 * s)) / 2,
          (-s + -4 + Real.sqrt (15 + 8 * s)) / 2,
          (s - 4 + Real.sqrt (15 - 8 * s)) / 2] : Multiset ℝ) =
        ↑[(-4 - s - Real.sqrt (15 + 8 * s)) / 2,
          (-4 + s - Real.sqrt (15 - 8 * s)) / 2,
          (-4 + s + Real.sqrt (15 - 8 * s)) / 2,
          (-4 - s + Real.sqrt (15 + 8 * s)) / 2]
    rw [Multiset.coe_eq_coe]
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
      (List.Perm.trans (List.Perm.swap _ _ _)
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))))
  have hP_roots :
      (modifiedNarayanaPolynomial 5).roots = (↑[a, b, c, d, e] : Multiset ℝ) := by
    rw [hPfactor]
    rw [roots_mul (mul_ne_zero (mul_ne_zero hquadPA_ne hquadPB_ne) hXc_ne)]
    rw [roots_mul (mul_ne_zero hquadPA_ne hquadPB_ne)]
    have hdiscA : ((7 : ℝ) + t) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) =
        (60 : ℝ) + 14 * t := by
      nlinarith only [ht_sq]
    have hdiscA_nonneg :
        0 ≤ ((7 : ℝ) + t) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) := by
      rw [hdiscA]
      positivity
    have hdiscB : ((7 : ℝ) - t) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) =
        (60 : ℝ) - 14 * t := by
      nlinarith only [ht_sq]
    have hdiscB_nonneg :
        0 ≤ ((7 : ℝ) - t) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) := by
      rw [hdiscB]
      exact h60_sub_14t_nonneg
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := ((7 : ℝ) + t))
      (c := (1 : ℝ)) (by norm_num) hdiscA_nonneg]
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := ((7 : ℝ) - t))
      (c := (1 : ℝ)) (by norm_num) hdiscB_nonneg]
    rw [roots_X_sub_C]
    rw [hdiscA, hdiscB]
    dsimp [a, b, c, d, e, γ, δ]
    norm_num
    change
      (↑[(t - 7 - Real.sqrt (60 - 14 * t)) / 2,
          (-t + -7 - Real.sqrt (60 + 14 * t)) / 2,
          (-t + -7 + Real.sqrt (60 + 14 * t)) / 2,
          (t - 7 + Real.sqrt (60 - 14 * t)) / 2,
          -1] : Multiset ℝ) =
        ↑[(-7 - t - Real.sqrt (60 + 14 * t)) / 2,
          (-7 + t - Real.sqrt (60 - 14 * t)) / 2,
          -1,
          (-7 + t + Real.sqrt (60 - 14 * t)) / 2,
          (-7 - t + Real.sqrt (60 + 14 * t)) / 2]
    rw [Multiset.coe_eq_coe]
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
      (List.Perm.trans (List.Perm.swap _ _ _)
        (List.Perm.cons _ (List.Perm.cons _ <|
          List.Perm.trans (List.Perm.swap _ _ _)
            (List.Perm.trans (List.Perm.cons _ (List.Perm.swap _ _ _))
              (List.Perm.swap _ _ _)))))
  have hP_ne : modifiedNarayanaPolynomial 5 ≠ 0 := modifiedNarayanaPolynomial_ne_zero 5
  have hP_splits : (modifiedNarayanaPolynomial 5).Splits :=
    modifiedNarayanaPolynomial_splits 5
  have hPdeg : (modifiedNarayanaPolynomial 5).natDegree = 5 := by
    rw [modifiedNarayanaPolynomial_natDegree]
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hbc : b ≤ c := by
    dsimp [b, c]
    linarith
  have hcd : c ≤ d := by
    dsimp [c, d]
    linarith
  have hde : d ≤ e := by
    dsimp [d, e]
    linarith
  have huv : u ≤ v := by
    dsimp [u, v]
    linarith
  have hvw : v ≤ w := by
    dsimp [v, w]
    linarith
  have hwz : w ≤ z := by
    dsimp [w, z]
    linarith
  have hau : a ≤ u := by
    dsimp [a, u]
    linarith
  have hub : u ≤ b := by
    dsimp [u, b]
    linarith
  have hbv : b ≤ v := by
    dsimp [b, v]
    linarith
  have hvc : v ≤ c := by
    dsimp [v, c]
    linarith
  have hcw : c ≤ w := by
    dsimp [c, w]
    linarith
  have hwd : w ≤ d := by
    dsimp [w, d]
    linarith
  have hdz : d ≤ z := by
    dsimp [d, z]
    linarith
  have hze : z ≤ e := by
    dsimp [z, e]
    linarith
  exact interlaces_of_quartic_quintic_root_lists hP_ne hP_splits hG_ne hG_splits
    hPdeg hGdeg hP_roots hG_roots hab hbc hcd hde huv hvw hwz hau hub hbv hvc
    hcw hwd hdz hze

/-- The `n = 5` case of Braun--Jal Lemma 3.3, for the concrete modified
Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_five :
    Prec (FiniteSkewBoard.auxiliaryG 5) (modifiedNarayanaPolynomial 5) := by
  exact lemma33AuxiliaryGInterlaces_modified_five_interlaces.toPrec

/-- The checked initial cases `n = 1, 2, 3, 4, 5` of Braun--Jal Lemma 3.3, for
the concrete modified Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_of_le_five
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₅ : n ≤ 5) :
    Prec (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) := by
  interval_cases n
  · exact lemma33AuxiliaryGInterlaces_modified_base
  · exact lemma33AuxiliaryGInterlaces_modified_two
  · exact lemma33AuxiliaryGInterlaces_modified_three
  · exact lemma33AuxiliaryGInterlaces_modified_four
  · exact lemma33AuxiliaryGInterlaces_modified_five

/-- Conditional checked initial cases `n = 1, 2, 3, 4, 5, 6` of Braun--Jal
Lemma 3.3.  The only remaining input is the `P_6`/`G_6` cross-root
inequality package. -/
theorem lemma33AuxiliaryGInterlaces_modified_of_le_six_of_crosses
    (hcross :
      ∀ {a b c d e r : ℝ},
        (modifiedNarayanaPolynomial 6).roots =
          (↑[a, b, c, d, e, r] : Multiset ℝ) →
        a ≤ b → b ≤ c → c ≤ d → d ≤ e → e ≤ r →
        ModifiedNarayanaSixAuxiliaryGCrossInequalities a b c d e r)
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₆ : n ≤ 6) :
    Prec (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) := by
  interval_cases n
  · exact lemma33AuxiliaryGInterlaces_modified_base
  · exact lemma33AuxiliaryGInterlaces_modified_two
  · exact lemma33AuxiliaryGInterlaces_modified_three
  · exact lemma33AuxiliaryGInterlaces_modified_four
  · exact lemma33AuxiliaryGInterlaces_modified_five
  · exact lemma33AuxiliaryGInterlaces_modified_six_of_crosses hcross

/-- Conditional checked initial cases `n = 1, 2, 3, 4, 5, 6` of Braun--Jal
Lemma 3.3 from the single `P_6`/`G_6` sign certificate. -/
theorem lemma33AuxiliaryGInterlaces_modified_of_le_six_of_eval_signs
    (hsign : ModifiedNarayanaSixAuxiliaryGSignCertificate)
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₆ : n ≤ 6) :
    Prec (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) :=
  lemma33AuxiliaryGInterlaces_modified_of_le_six_of_crosses
    (fun {a b c d e r} hP_roots hab hbc hcd hde her =>
      ModifiedNarayanaSixAuxiliaryGCrossInequalities.of_eval_signs
        (by simpa [modifiedNarayanaPolynomialSix] using hP_roots)
        hab hbc hcd hde her hsign)
    hn₁ hn₆

/-- The checked initial cases `n = 1, 2, 3, 4, 5, 6` of Braun--Jal
Lemma 3.3, for the concrete modified Narayana family and the finite-board
auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_of_le_six
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₆ : n ≤ 6) :
    Prec (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) :=
  lemma33AuxiliaryGInterlaces_modified_of_le_six_of_eval_signs
    modifiedNarayanaPolynomial_six_auxiliaryG_signCertificate hn₁ hn₆

/-- The checked initial cases `n = 1, ..., 6` of Braun--Jal Lemma 3.3,
packaged in the generic bounded interlacing interface. -/
theorem lemma33AuxiliaryGInterlaces_modified_upTo_six :
    Lemma33AuxiliaryGInterlacesUpToStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG 6 := by
  intro n hn₁ hn₆
  exact lemma33AuxiliaryGInterlaces_modified_of_le_six hn₁ hn₆

end GeneralizedSnakePosets
end RealRooted
