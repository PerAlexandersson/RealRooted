import RealRooted.GeneralizedSnakePosets.Narayana.PFFacts

/-!
# Rank-six modified-Narayana certificate

This module contains fixed-length root-list bridges and the explicit root,
sign, interval, and cross-inequality certificate proving the rank-six instance
of Braun--Jal Lemma 3.3.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- Differ-by-one interlacing for a quadratic whose roots lie between the
ordered roots of a cubic. -/
theorem interlaces_of_quadratic_cubic_root_lists
    {g f : ℝ[X]} {a b c u v : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 2)
    (hf_roots : f.roots = (↑[a, b, c] : Multiset ℝ))
    (hg_roots : g.roots = (↑[u, v] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v) (hvc : v ≤ c) :
    Interlaces g f :=
  Interlaces.of_quadratic_cubic_root_lists
    hf_ne hf_splits hg_ne hg_splits hfdeg hgdeg hf_roots hg_roots
    hab hbc huv hau hub hbv hvc

/-- Differ-by-one interlacing for a cubic whose roots lie between the ordered
roots of a quartic. -/
theorem interlaces_of_cubic_quartic_root_lists
    {g f : ℝ[X]} {a b c d u v w : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfdeg : f.natDegree = 4) (hgdeg : g.natDegree = 3)
    (hf_roots : f.roots = (↑[a, b, c, d] : Multiset ℝ))
    (hg_roots : g.roots = (↑[u, v, w] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (huv : u ≤ v) (hvw : v ≤ w)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hwd : w ≤ d) :
    Interlaces g f :=
  Interlaces.of_cubic_quartic_root_lists
    hf_ne hf_splits hg_ne hg_splits hfdeg hgdeg hf_roots hg_roots
    hab hbc hcd huv hvw hau hub hbv hvc hcw hwd

/-- Differ-by-one interlacing for a quartic whose roots lie between the
ordered roots of a quintic. -/
theorem interlaces_of_quartic_quintic_root_lists
    {g f : ℝ[X]} {a b c d e u v w z : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfdeg : f.natDegree = 5) (hgdeg : g.natDegree = 4)
    (hf_roots : f.roots = (↑[a, b, c, d, e] : Multiset ℝ))
    (hg_roots : g.roots = (↑[u, v, w, z] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (huv : u ≤ v) (hvw : v ≤ w) (hwz : w ≤ z)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hwd : w ≤ d)
    (hdz : d ≤ z) (hze : z ≤ e) :
    Interlaces g f :=
  Interlaces.of_quartic_quintic_root_lists
    hf_ne hf_splits hg_ne hg_splits hfdeg hgdeg hf_roots hg_roots
    hab hbc hcd hde huv hvw hwz hau hub hbv hvc hcw hwd hdz hze

/-- Differ-by-one interlacing for a quintic whose roots lie between the ordered
roots of a sextic. -/
theorem interlaces_of_quintic_sextic_root_lists
    {g f : ℝ[X]} {a b c d e r u v w z y : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfdeg : f.natDegree = 6) (hgdeg : g.natDegree = 5)
    (hf_roots : f.roots = (↑[a, b, c, d, e, r] : Multiset ℝ))
    (hg_roots : g.roots = (↑[u, v, w, z, y] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (her : e ≤ r)
    (huv : u ≤ v) (hvw : v ≤ w) (hwz : w ≤ z) (hzy : z ≤ y)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hwd : w ≤ d)
    (hdz : d ≤ z) (hze : z ≤ e) (hey : e ≤ y) (hyr : y ≤ r) :
    Interlaces g f :=
  Interlaces.of_quintic_sextic_root_lists
    hf_ne hf_splits hg_ne hg_splits hfdeg hgdeg hf_roots hg_roots
    hab hbc hcd hde her huv hvw hwz hzy hau hub hbv hvc hcw hwd hdz hze hey hyr

/-- Exact factorization of the `G_6` auxiliary polynomial. -/
theorem auxiliaryG_six_factor :
    FiniteSkewBoard.auxiliaryG 6 =
      C (2 : ℝ) * (X + 1) *
        (C (3 : ℝ) * X ^ 4 + C (32 : ℝ) * X ^ 3 +
          C (73 : ℝ) * X ^ 2 + C (32 : ℝ) * X + C (3 : ℝ)) := by
  rw [FiniteSkewBoard.auxiliaryG_six]
  have hC2 : (C (2 : ℝ) : ℝ[X]) = 2 := Polynomial.C_eq_natCast (R := ℝ) 2
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC32 : (C (32 : ℝ) : ℝ[X]) = 32 := Polynomial.C_eq_natCast (R := ℝ) 32
  have hC70 : (C (70 : ℝ) : ℝ[X]) = 70 := Polynomial.C_eq_natCast (R := ℝ) 70
  have hC73 : (C (73 : ℝ) : ℝ[X]) = 73 := Polynomial.C_eq_natCast (R := ℝ) 73
  have hC210 : (C (210 : ℝ) : ℝ[X]) = 210 :=
    Polynomial.C_eq_natCast (R := ℝ) 210
  rw [hC2, hC3, hC6, hC32, hC70, hC73, hC210]
  ring

/-- Scaled real-quadratic factorization of the quartic factor in `G_6`. -/
theorem auxiliaryG_six_quartic_scaled_factor :
    C (3 : ℝ) *
        (C (3 : ℝ) * X ^ 4 + C (32 : ℝ) * X ^ 3 +
          C (73 : ℝ) * X ^ 2 + C (32 : ℝ) * X + C (3 : ℝ)) =
      (C (3 : ℝ) * X ^ 2 + C ((16 : ℝ) + Real.sqrt (55 : ℝ)) * X +
          C (3 : ℝ)) *
        (C (3 : ℝ) * X ^ 2 + C ((16 : ℝ) - Real.sqrt (55 : ℝ)) * X +
          C (3 : ℝ)) := by
  have hs_sq' : Real.sqrt (55 : ℝ) ^ 2 = (55 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hCsq : (C (Real.sqrt (55 : ℝ)) : ℝ[X]) ^ 2 = C (55 : ℝ) := by rw [← map_pow, hs_sq']
  have hCplus :
      (C ((16 : ℝ) + Real.sqrt (55 : ℝ)) : ℝ[X]) =
        C (16 : ℝ) + C (Real.sqrt (55 : ℝ)) := by
    rw [map_add]
  have hCminus :
      (C ((16 : ℝ) - Real.sqrt (55 : ℝ)) : ℝ[X]) =
        C (16 : ℝ) - C (Real.sqrt (55 : ℝ)) := by
    rw [map_sub]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC16 : (C (16 : ℝ) : ℝ[X]) = 16 := Polynomial.C_eq_natCast (R := ℝ) 16
  have hC32 : (C (32 : ℝ) : ℝ[X]) = 32 := Polynomial.C_eq_natCast (R := ℝ) 32
  have hC55 : (C (55 : ℝ) : ℝ[X]) = 55 := Polynomial.C_eq_natCast (R := ℝ) 55
  have hC73 : (C (73 : ℝ) : ℝ[X]) = 73 := Polynomial.C_eq_natCast (R := ℝ) 73
  rw [hCplus, hCminus]
  rw [hC3, hC16, hC32, hC73]
  ring_nf
  rw [hCsq, hC55]
  ring_nf

/-- Root multiset of the `G_6` auxiliary polynomial. -/
theorem auxiliaryG_six_roots :
    let s : ℝ := Real.sqrt (55 : ℝ)
    let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
    let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
    let u : ℝ := (-s + -16 - α) / 6
    let v : ℝ := (s - 16 - β) / 6
    let w : ℝ := -(1 : ℝ)
    let z : ℝ := (s - 16 + β) / 6
    let y : ℝ := (-s + -16 + α) / 6
    (FiniteSkewBoard.auxiliaryG 6).roots = (↑[u, v, w, z, y] : Multiset ℝ) := by
  dsimp
  let s : ℝ := Real.sqrt (55 : ℝ)
  let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
  let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
  let u : ℝ := (-s + -16 - α) / 6
  let v : ℝ := (s - 16 - β) / 6
  let w : ℝ := -(1 : ℝ)
  let z : ℝ := (s - 16 + β) / 6
  let y : ℝ := (-s + -16 + α) / 6
  let quartic : ℝ[X] :=
    C (3 : ℝ) * X ^ 4 + C (32 : ℝ) * X ^ 3 +
      C (73 : ℝ) * X ^ 2 + C (32 : ℝ) * X + C (3 : ℝ)
  let qPlus : ℝ[X] :=
    C (3 : ℝ) * X ^ 2 + C ((16 : ℝ) + s) * X + C (3 : ℝ)
  let qMinus : ℝ[X] :=
    C (3 : ℝ) * X ^ 2 + C ((16 : ℝ) - s) * X + C (3 : ℝ)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hqPlus_deg : qPlus.natDegree = 2 := by
    dsimp [qPlus]
    compute_degree!
  have hqPlus_ne : qPlus ≠ 0 := by
    intro hzero
    rw [hzero] at hqPlus_deg
    norm_num at hqPlus_deg
  have hqMinus_deg : qMinus.natDegree = 2 := by
    dsimp [qMinus]
    compute_degree!
  have hqMinus_ne : qMinus ≠ 0 := by
    intro hzero
    rw [hzero] at hqMinus_deg
    norm_num at hqMinus_deg
  have hquartic_deg : quartic.natDegree = 4 := by
    dsimp [quartic]
    compute_degree!
  have hquartic_ne : quartic ≠ 0 := by
    intro hzero
    rw [hzero] at hquartic_deg
    norm_num at hquartic_deg
  have hquartic_scaled : C (3 : ℝ) * quartic = qPlus * qMinus := by
    dsimp [quartic, qPlus, qMinus, s]
    exact auxiliaryG_six_quartic_scaled_factor
  have hdiscPlus : ((16 : ℝ) + s) ^ 2 - 4 * (3 : ℝ) * (3 : ℝ) =
      (275 : ℝ) + 32 * s := by
    nlinarith only [hs_sq]
  have hdiscMinus : ((16 : ℝ) - s) ^ 2 - 4 * (3 : ℝ) * (3 : ℝ) =
      (275 : ℝ) - 32 * s := by
    nlinarith only [hs_sq]
  have hdiscPlus_nonneg :
      0 ≤ ((16 : ℝ) + s) ^ 2 - 4 * (3 : ℝ) * (3 : ℝ) := by
    rw [hdiscPlus]
    positivity
  have hdiscMinus_nonneg :
      0 ≤ ((16 : ℝ) - s) ^ 2 - 4 * (3 : ℝ) * (3 : ℝ) := by
    rw [hdiscMinus]
    nlinarith [hs_sq, sq_nonneg (s - 8)]
  have hquartic_roots : quartic.roots = (↑[u, y, v, z] : Multiset ℝ) := by
    rw [← roots_C_mul quartic (show (3 : ℝ) ≠ 0 by norm_num)]
    rw [hquartic_scaled]
    rw [roots_mul (mul_ne_zero hqPlus_ne hqMinus_ne)]
    rw [roots_quadratic_posLead (a := (3 : ℝ)) (b := ((16 : ℝ) + s))
      (c := (3 : ℝ)) (by norm_num) hdiscPlus_nonneg]
    rw [roots_quadratic_posLead (a := (3 : ℝ)) (b := ((16 : ℝ) - s))
      (c := (3 : ℝ)) (by norm_num) hdiscMinus_nonneg]
    rw [hdiscPlus, hdiscMinus]
    dsimp [u, y, v, z, α, β]
    norm_num
    change (↑[v, u, y, z] : Multiset ℝ) = ↑[u, y, v, z]
    rw [Multiset.coe_eq_coe]
    exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ _))
  have hGfactor :
      FiniteSkewBoard.auxiliaryG 6 = C (2 : ℝ) * (X - C w) * quartic := by
    rw [auxiliaryG_six_factor]
    dsimp [quartic, w]
    have hCneg1 : (C (-(1 : ℝ)) : ℝ[X]) = -1 := by simp
    rw [hCneg1]
    ring_nf
  rw [hGfactor]
  rw [roots_mul
    (mul_ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num))
      (X_sub_C_ne_zero w)) hquartic_ne)]
  rw [roots_mul (mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num))
    (X_sub_C_ne_zero w))]
  rw [roots_C, roots_X_sub_C, hquartic_roots]
  dsimp [w]
  change (↑[-1, u, y, v, z] : Multiset ℝ) = ↑[u, v, -1, z, y]
  rw [Multiset.coe_eq_coe]
  exact List.Perm.trans (List.Perm.swap _ _ _)
    (List.Perm.cons _ <|
      List.Perm.trans
        (List.Perm.cons _ (List.Perm.swap _ _ _))
        (List.Perm.trans (List.Perm.swap _ _ _)
          (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _)))))

/-- The displayed roots in `auxiliaryG_six_roots` are ordered increasingly. -/
theorem auxiliaryG_six_root_order :
    let s : ℝ := Real.sqrt (55 : ℝ)
    let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
    let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
    let u : ℝ := (-s + -16 - α) / 6
    let v : ℝ := (s - 16 - β) / 6
    let w : ℝ := -(1 : ℝ)
    let z : ℝ := (s - 16 + β) / 6
    let y : ℝ := (-s + -16 + α) / 6
    u ≤ v ∧ v ≤ w ∧ w ≤ z ∧ z ≤ y := by
  dsimp
  let s : ℝ := Real.sqrt (55 : ℝ)
  let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
  let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
  let u : ℝ := (-s + -16 - α) / 6
  let v : ℝ := (s - 16 - β) / 6
  let w : ℝ := -(1 : ℝ)
  let z : ℝ := (s - 16 + β) / 6
  let y : ℝ := (-s + -16 + α) / 6
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hs_ge7 : (7 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hs_le8 : s ≤ (8 : ℝ) := by
    dsimp [s]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hβ_arg_nonneg : 0 ≤ (275 : ℝ) - 32 * s := by nlinarith [hs_sq, sq_nonneg (s - 8)]
  have hα_sq : α ^ 2 = (275 : ℝ) + 32 * s := by
    dsimp [α]
    exact Real.sq_sqrt (by positivity)
  have hβ_sq : β ^ 2 = (275 : ℝ) - 32 * s := by
    dsimp [β]
    exact Real.sq_sqrt hβ_arg_nonneg
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact Real.sqrt_nonneg _
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    exact Real.sqrt_nonneg _
  have hβ_le8 : β ≤ (8 : ℝ) := by
    dsimp [β]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [hs_ge7]
  have hβ_le_2sα : β ≤ 2 * s + α := by nlinarith [hβ_nonneg, hs_nonneg, hα_nonneg]
  have hten_minus_s_leβ : (10 : ℝ) - s ≤ β := by
    dsimp [β]
    apply Real.le_sqrt_of_sq_le
    nlinarith [hs_sq, hs_le8]
  have h2sβ_leα : 2 * s + β ≤ α := by
    have hmul : 4 * s * β ≤ 4 * s * 8 := by
      exact mul_le_mul_of_nonneg_left hβ_le8 (by positivity)
    have hsq_le : (2 * s + β) ^ 2 ≤ α ^ 2 := by nlinarith [hs_sq, hβ_sq, hα_sq, hmul, hs_ge7]
    nlinarith [sq_nonneg (α - (2 * s + β)), hsq_le, hα_nonneg, hs_nonneg,
      hβ_nonneg]
  constructor
  · nlinarith [hβ_le_2sα]
  constructor
  · nlinarith [hs_le8, hβ_nonneg]
  constructor
  · nlinarith [hten_minus_s_leβ]
  · nlinarith [h2sβ_leα]

/-- The first displayed root of the `G_6` auxiliary polynomial. -/
def auxiliaryG_six_root0 : ℝ :=
  (-Real.sqrt (55 : ℝ) + -16 -
    Real.sqrt ((275 : ℝ) + 32 * Real.sqrt (55 : ℝ))) / 6

/-- The second displayed root of the `G_6` auxiliary polynomial. -/
def auxiliaryG_six_root1 : ℝ :=
  (Real.sqrt (55 : ℝ) - 16 -
    Real.sqrt ((275 : ℝ) - 32 * Real.sqrt (55 : ℝ))) / 6

/-- The middle displayed root of the `G_6` auxiliary polynomial. -/
def auxiliaryG_six_root2 : ℝ :=
  -(1 : ℝ)

/-- The fourth displayed root of the `G_6` auxiliary polynomial. -/
def auxiliaryG_six_root3 : ℝ :=
  (Real.sqrt (55 : ℝ) - 16 +
    Real.sqrt ((275 : ℝ) - 32 * Real.sqrt (55 : ℝ))) / 6

/-- The fifth displayed root of the `G_6` auxiliary polynomial. -/
def auxiliaryG_six_root4 : ℝ :=
  (-Real.sqrt (55 : ℝ) + -16 +
    Real.sqrt ((275 : ℝ) + 32 * Real.sqrt (55 : ℝ))) / 6

/-- Root multiset of `G_6`, stated using named roots. -/
theorem auxiliaryG_six_roots_named :
    (FiniteSkewBoard.auxiliaryG 6).roots =
      (↑[auxiliaryG_six_root0, auxiliaryG_six_root1, auxiliaryG_six_root2,
        auxiliaryG_six_root3, auxiliaryG_six_root4] : Multiset ℝ) := by
  simpa [auxiliaryG_six_root0, auxiliaryG_six_root1, auxiliaryG_six_root2,
    auxiliaryG_six_root3, auxiliaryG_six_root4] using auxiliaryG_six_roots

/-- The named roots of `G_6` are ordered increasingly. -/
theorem auxiliaryG_six_root_order_named :
    auxiliaryG_six_root0 ≤ auxiliaryG_six_root1 ∧
      auxiliaryG_six_root1 ≤ auxiliaryG_six_root2 ∧
        auxiliaryG_six_root2 ≤ auxiliaryG_six_root3 ∧
          auxiliaryG_six_root3 ≤ auxiliaryG_six_root4 := by
  simpa [auxiliaryG_six_root0, auxiliaryG_six_root1, auxiliaryG_six_root2,
    auxiliaryG_six_root3, auxiliaryG_six_root4] using auxiliaryG_six_root_order

/-- Degree of the `G_6` auxiliary polynomial. -/
theorem auxiliaryG_six_natDegree :
    (FiniteSkewBoard.auxiliaryG 6).natDegree = 5 := by
  rw [FiniteSkewBoard.auxiliaryG_six]
  compute_degree!

/-- The `G_6` auxiliary polynomial is nonzero. -/
theorem auxiliaryG_six_ne_zero : FiniteSkewBoard.auxiliaryG 6 ≠ 0 := by
  intro hzero
  have hdeg := auxiliaryG_six_natDegree
  rw [hzero] at hdeg
  norm_num at hdeg

/-- The `G_6` auxiliary polynomial splits over `ℝ`. -/
theorem auxiliaryG_six_splits : (FiniteSkewBoard.auxiliaryG 6).Splits := by
  rw [Polynomial.splits_iff_card_roots]
  rw [auxiliaryG_six_roots]
  rw [auxiliaryG_six_natDegree]
  norm_num

/-- Shorthand for the modified Narayana polynomial `P_6`. -/
abbrev modifiedNarayanaPolynomialSix : ℝ[X] :=
  modifiedNarayanaPolynomial 6

/-- Evaluation of `P_6` at a root of the `+ sqrt 55` quadratic factor of
`G_6`. -/
theorem modifiedNarayanaPolynomial_six_eval_of_qPlus_root {s x : ℝ}
    (hs : s ^ 2 = (55 : ℝ))
    (hx : (3 : ℝ) * x ^ 2 + ((16 : ℝ) + s) * x + 3 = 0) :
    243 * modifiedNarayanaPolynomialSix.eval x =
      139370 * s * x + 18480 * s + 1015520 * x + 129855 := by
  rw [modifiedNarayanaPolynomialSix, modifiedNarayanaPolynomial_six]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_one]
  have hs0 : s ^ 2 - 55 = 0 := by nlinarith [hs]
  linear_combination
    (81 * x ^ 4 + 1269 * x ^ 3 + 1656 * x ^ 2 + 4074 * x - 14879
      - 27 * s * x ^ 3 - 279 * s * x ^ 2 + 963 * s * x - 6215 * s
      + 9 * s ^ 2 * x ^ 2 + 45 * s ^ 2 * x - 570 * s ^ 2
      - 3 * s ^ 3 * x + s ^ 3 + s ^ 4) * hx
    - (s ^ 3 * x + 17 * s ^ 2 * x + 3 * s ^ 2 - 508 * s * x + 3 * s
      - 14265 * x - 1545) * hs0

/-- Evaluation of `P_6` at a root of the `- sqrt 55` quadratic factor of
`G_6`. -/
theorem modifiedNarayanaPolynomial_six_eval_of_qMinus_root {s x : ℝ}
    (hs : s ^ 2 = (55 : ℝ))
    (hx : (3 : ℝ) * x ^ 2 + ((16 : ℝ) - s) * x + 3 = 0) :
    243 * modifiedNarayanaPolynomialSix.eval x =
      -139370 * s * x - 18480 * s + 1015520 * x + 129855 := by
  rw [modifiedNarayanaPolynomialSix, modifiedNarayanaPolynomial_six]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_one]
  have hs0 : s ^ 2 - 55 = 0 := by nlinarith [hs]
  linear_combination
    (81 * x ^ 4 + 1269 * x ^ 3 + 1656 * x ^ 2 + 4074 * x - 14879
      + 27 * s * x ^ 3 + 279 * s * x ^ 2 - 963 * s * x + 6215 * s
      + 9 * s ^ 2 * x ^ 2 + 45 * s ^ 2 * x - 570 * s ^ 2
      + 3 * s ^ 3 * x - s ^ 3 + s ^ 4) * hx
    + (s ^ 3 * x - 17 * s ^ 2 * x - 3 * s ^ 2 - 508 * s * x + 3 * s
      + 14265 * x + 1545) * hs0

/-- The first named `G_6` root lies on the `+ sqrt 55` quadratic factor. -/
theorem auxiliaryG_six_root0_qPlus :
    (3 : ℝ) * auxiliaryG_six_root0 ^ 2 +
      ((16 : ℝ) + Real.sqrt (55 : ℝ)) * auxiliaryG_six_root0 + 3 = 0 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hα_sq : α ^ 2 = (275 : ℝ) + 32 * s := by
    dsimp [α]
    exact Real.sq_sqrt (by positivity)
  dsimp [auxiliaryG_six_root0, s, α] at *
  nlinarith

/-- The second named `G_6` root lies on the `- sqrt 55` quadratic factor. -/
theorem auxiliaryG_six_root1_qMinus :
    (3 : ℝ) * auxiliaryG_six_root1 ^ 2 +
      ((16 : ℝ) - Real.sqrt (55 : ℝ)) * auxiliaryG_six_root1 + 3 = 0 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hβ_arg_nonneg : 0 ≤ (275 : ℝ) - 32 * s := by nlinarith [hs_sq, sq_nonneg (s - 8)]
  have hβ_sq : β ^ 2 = (275 : ℝ) - 32 * s := by
    dsimp [β]
    exact Real.sq_sqrt hβ_arg_nonneg
  dsimp [auxiliaryG_six_root1, s, β] at *
  nlinarith

/-- The fourth named `G_6` root lies on the `- sqrt 55` quadratic factor. -/
theorem auxiliaryG_six_root3_qMinus :
    (3 : ℝ) * auxiliaryG_six_root3 ^ 2 +
      ((16 : ℝ) - Real.sqrt (55 : ℝ)) * auxiliaryG_six_root3 + 3 = 0 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hβ_arg_nonneg : 0 ≤ (275 : ℝ) - 32 * s := by nlinarith [hs_sq, sq_nonneg (s - 8)]
  have hβ_sq : β ^ 2 = (275 : ℝ) - 32 * s := by
    dsimp [β]
    exact Real.sq_sqrt hβ_arg_nonneg
  dsimp [auxiliaryG_six_root3, s, β] at *
  nlinarith

/-- The fifth named `G_6` root lies on the `+ sqrt 55` quadratic factor. -/
theorem auxiliaryG_six_root4_qPlus :
    (3 : ℝ) * auxiliaryG_six_root4 ^ 2 +
      ((16 : ℝ) + Real.sqrt (55 : ℝ)) * auxiliaryG_six_root4 + 3 = 0 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hα_sq : α ^ 2 = (275 : ℝ) + 32 * s := by
    dsimp [α]
    exact Real.sq_sqrt (by positivity)
  dsimp [auxiliaryG_six_root4, s, α] at *
  nlinarith

/-- The sign pattern of `P_6` at the named `G_6` roots. -/
def ModifiedNarayanaSixAuxiliaryGSignCertificate : Prop :=
  modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root0 < 0 ∧
    0 < modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root1 ∧
      modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root2 < 0 ∧
        0 < modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root3 ∧
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root4 < 0

/-- `P_6` is negative at the first named `G_6` root. -/
theorem modifiedNarayanaPolynomial_six_eval_root0_neg :
    modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root0 < 0 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hα_sq : α ^ 2 = (275 : ℝ) + 32 * s := by
    dsimp [α]
    exact Real.sq_sqrt (by positivity)
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact Real.sqrt_nonneg _
  have hroot0 :
      (3 : ℝ) * auxiliaryG_six_root0 ^ 2 +
        ((16 : ℝ) + s) * auxiliaryG_six_root0 + 3 = 0 := by
    dsimp [s]
    exact auxiliaryG_six_root0_qPlus
  have h0_num :
      139370 * s * auxiliaryG_six_root0 + 18480 * s +
          1015520 * auxiliaryG_six_root0 + 129855 < 0 := by
    dsimp [auxiliaryG_six_root0, s, α] at *
    nlinarith
  have h0_scaled :
      243 * modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root0 < 0 := by
    rwa [modifiedNarayanaPolynomial_six_eval_of_qPlus_root hs_sq hroot0]
  nlinarith

/-- `P_6` is positive at the second named `G_6` root. -/
theorem modifiedNarayanaPolynomial_six_eval_root1_pos :
    0 < modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root1 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_ge37div5 : (37 / 5 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    exact Real.sqrt_nonneg _
  have hroot1 :
      (3 : ℝ) * auxiliaryG_six_root1 ^ 2 +
        ((16 : ℝ) - s) * auxiliaryG_six_root1 + 3 = 0 := by
    dsimp [s]
    exact auxiliaryG_six_root1_qMinus
  have h1_num :
      0 < -139370 * s * auxiliaryG_six_root1 - 18480 * s +
        1015520 * auxiliaryG_six_root1 + 129855 := by
    dsimp [auxiliaryG_six_root1, s, β] at *
    nlinarith
  have h1_scaled :
      0 < 243 * modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root1 := by
    rwa [modifiedNarayanaPolynomial_six_eval_of_qMinus_root hs_sq hroot1]
  nlinarith

/-- `P_6` is negative at the middle named `G_6` root. -/
theorem modifiedNarayanaPolynomial_six_eval_root2_neg :
    modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root2 < 0 := by
  norm_num [modifiedNarayanaPolynomialSix, auxiliaryG_six_root2]

/-- `P_6` is positive at the fourth named `G_6` root. -/
theorem modifiedNarayanaPolynomial_six_eval_root3_pos :
    0 < modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root3 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_ge37div5 : (37 / 5 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hs_le149div20 : s ≤ (149 / 20 : ℝ) := by
    dsimp [s]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hβ_arg_nonneg : 0 ≤ (275 : ℝ) - 32 * s := by nlinarith [hs_sq, sq_nonneg (s - 8)]
  have hβ_sq : β ^ 2 = (275 : ℝ) - 32 * s := by
    dsimp [β]
    exact Real.sq_sqrt hβ_arg_nonneg
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    exact Real.sqrt_nonneg _
  have hroot3 :
      (3 : ℝ) * auxiliaryG_six_root3 ^ 2 +
        ((16 : ℝ) - s) * auxiliaryG_six_root3 + 3 = 0 := by
    dsimp [s]
    exact auxiliaryG_six_root3_qMinus
  have h3_num :
      0 < -139370 * s * auxiliaryG_six_root3 - 18480 * s +
        1015520 * auxiliaryG_six_root3 + 129855 := by
    have hcoeff_nonneg : 0 ≤ (1267 : ℝ) * s - 9232 := by nlinarith
    have hA_nonneg : 0 ≤ ((1267 : ℝ) * s - 9232) * β :=
      mul_nonneg hcoeff_nonneg hβ_nonneg
    have hB_nonneg : 0 ≤ (28496 : ℝ) * s - 210314 := by nlinarith
    have hsq :
        (((1267 : ℝ) * s - 9232) * β) ^ 2 <
          ((28496 : ℝ) * s - 210314) ^ 2 := by
      have hdiff :
          0 < ((28496 : ℝ) * s - 210314) ^ 2 -
            (((1267 : ℝ) * s - 9232) * β) ^ 2 := by
        nlinarith [hs_sq, hβ_sq, hs_le149div20]
      nlinarith
    have hlt : ((1267 : ℝ) * s - 9232) * β < (28496 : ℝ) * s - 210314 := by
      have h_abs := (sq_lt_sq.mp hsq)
      simpa [abs_of_nonneg hA_nonneg, abs_of_nonneg hB_nonneg] using h_abs
    dsimp [auxiliaryG_six_root3, s, β] at *
    nlinarith
  have h3_scaled :
      0 < 243 * modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root3 := by
    rwa [modifiedNarayanaPolynomial_six_eval_of_qMinus_root hs_sq hroot3]
  nlinarith

/-- `P_6` is negative at the fifth named `G_6` root. -/
theorem modifiedNarayanaPolynomial_six_eval_root4_neg :
    modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root4 < 0 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hα_sq : α ^ 2 = (275 : ℝ) + 32 * s := by
    dsimp [α]
    exact Real.sq_sqrt (by positivity)
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact Real.sqrt_nonneg _
  have hroot4 :
      (3 : ℝ) * auxiliaryG_six_root4 ^ 2 +
        ((16 : ℝ) + s) * auxiliaryG_six_root4 + 3 = 0 := by
    dsimp [s]
    exact auxiliaryG_six_root4_qPlus
  have h4_num :
      139370 * s * auxiliaryG_six_root4 + 18480 * s +
          1015520 * auxiliaryG_six_root4 + 129855 < 0 := by
    have hA_nonneg : 0 ≤ ((9232 : ℝ) + 1267 * s) * α := by positivity
    have hB_nonneg : 0 ≤ (210314 : ℝ) + 28496 * s := by positivity
    have hsq :
        (((9232 : ℝ) + 1267 * s) * α) ^ 2 <
          ((210314 : ℝ) + 28496 * s) ^ 2 := by
      have hdiff :
          0 < ((210314 : ℝ) + 28496 * s) ^ 2 -
            (((9232 : ℝ) + 1267 * s) * α) ^ 2 := by
        nlinarith [hs_sq, hα_sq, hs_nonneg]
      nlinarith
    have hlt : ((9232 : ℝ) + 1267 * s) * α < (210314 : ℝ) + 28496 * s := by
      have h_abs := (sq_lt_sq.mp hsq)
      simpa [abs_of_nonneg hA_nonneg, abs_of_nonneg hB_nonneg] using h_abs
    dsimp [auxiliaryG_six_root4, s, α] at *
    nlinarith
  have h4_scaled :
      243 * modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root4 < 0 := by
    rwa [modifiedNarayanaPolynomial_six_eval_of_qPlus_root hs_sq hroot4]
  nlinarith

/-- The concrete sign pattern of `P_6` at the five named `G_6` roots. -/
theorem modifiedNarayanaPolynomial_six_auxiliaryG_signCertificate :
    ModifiedNarayanaSixAuxiliaryGSignCertificate :=
  ⟨modifiedNarayanaPolynomial_six_eval_root0_neg,
    modifiedNarayanaPolynomial_six_eval_root1_pos,
    modifiedNarayanaPolynomial_six_eval_root2_neg,
    modifiedNarayanaPolynomial_six_eval_root3_pos,
    modifiedNarayanaPolynomial_six_eval_root4_neg⟩

/-- The roots of `P_6` are isolated across the five named `G_6` roots. -/
def ModifiedNarayanaSixAuxiliaryGRootIntervalCertificate : Prop :=
  ∃ x0 x1 x2 x3 x4 x5 : ℝ,
    modifiedNarayanaPolynomialSix.IsRoot x0 ∧
      x0 < auxiliaryG_six_root0 ∧
        modifiedNarayanaPolynomialSix.IsRoot x1 ∧
          auxiliaryG_six_root0 < x1 ∧ x1 < auxiliaryG_six_root1 ∧
            modifiedNarayanaPolynomialSix.IsRoot x2 ∧
              auxiliaryG_six_root1 < x2 ∧ x2 < auxiliaryG_six_root2 ∧
                modifiedNarayanaPolynomialSix.IsRoot x3 ∧
                  auxiliaryG_six_root2 < x3 ∧ x3 < auxiliaryG_six_root3 ∧
                    modifiedNarayanaPolynomialSix.IsRoot x4 ∧
                      auxiliaryG_six_root3 < x4 ∧ x4 < auxiliaryG_six_root4 ∧
                        modifiedNarayanaPolynomialSix.IsRoot x5 ∧
                          auxiliaryG_six_root4 < x5

/-- Sign alternation of `P_6` across the named `G_6` roots gives one `P_6`
root in each complementary interval. -/
theorem modifiedNarayanaPolynomial_six_rootIntervals_of_eval_signs
    (hsign : ModifiedNarayanaSixAuxiliaryGSignCertificate) :
    ModifiedNarayanaSixAuxiliaryGRootIntervalCertificate := by
  rcases hsign with ⟨h0, h1, h2, h3, h4⟩
  rcases auxiliaryG_six_root_order_named with ⟨h01, h12, h23, h34⟩
  have hP_pos : HasPosLeadingCoeff modifiedNarayanaPolynomialSix := by
    simpa [modifiedNarayanaPolynomialSix] using modifiedNarayanaPolynomial_posLeadingCoeff 6
  have hP_natdeg_pos : 0 < modifiedNarayanaPolynomialSix.natDegree := by
    rw [modifiedNarayanaPolynomialSix, modifiedNarayanaPolynomial_six_natDegree]
    norm_num
  have hP_deg_pos : 0 < modifiedNarayanaPolynomialSix.degree :=
    natDegree_pos_iff_degree_pos.mp hP_natdeg_pos
  have hP_even : Even modifiedNarayanaPolynomialSix.natDegree := by
    rw [modifiedNarayanaPolynomialSix, modifiedNarayanaPolynomial_six_natDegree]
    norm_num
  have ht_bot : Tendsto (fun x => modifiedNarayanaPolynomialSix.eval x) atBot atTop :=
    tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hP_pos hP_deg_pos hP_even
  have ht_top : Tendsto (fun x => modifiedNarayanaPolynomialSix.eval x) atTop atTop :=
    modifiedNarayanaPolynomialSix.tendsto_atTop_of_leadingCoeff_nonneg
      hP_deg_pos hP_pos.le
  obtain ⟨x0, hx0_le, hx0_root⟩ :=
    exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop h0 ht_bot
  have hx0_lt : x0 < auxiliaryG_six_root0 := by
    refine lt_of_le_of_ne hx0_le ?_
    intro hx0_eq
    have hx0_eval : modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root0 = 0 := by
      simpa [Polynomial.IsRoot.def, hx0_eq] using hx0_root
    linarith
  have h01_strict : auxiliaryG_six_root0 < auxiliaryG_six_root1 := by
    refine lt_of_le_of_ne h01 ?_
    intro h_eq
    have heq_eval :
        modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root0 =
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root1 := by
      rw [h_eq]
    linarith
  have h12_strict : auxiliaryG_six_root1 < auxiliaryG_six_root2 := by
    refine lt_of_le_of_ne h12 ?_
    intro h_eq
    have heq_eval :
        modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root1 =
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root2 := by
      rw [h_eq]
    linarith
  have h23_strict : auxiliaryG_six_root2 < auxiliaryG_six_root3 := by
    refine lt_of_le_of_ne h23 ?_
    intro h_eq
    have heq_eval :
        modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root2 =
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root3 := by
      rw [h_eq]
    linarith
  have h34_strict : auxiliaryG_six_root3 < auxiliaryG_six_root4 := by
    refine lt_of_le_of_ne h34 ?_
    intro h_eq
    have heq_eval :
        modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root3 =
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root4 := by
      rw [h_eq]
    linarith
  have h01_sign :
      modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root0 *
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root1 < 0 := by
    nlinarith
  have h12_sign :
      modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root1 *
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root2 < 0 := by
    nlinarith
  have h23_sign :
      modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root2 *
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root3 < 0 := by
    nlinarith
  have h34_sign :
      modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root3 *
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root4 < 0 := by
    nlinarith
  obtain ⟨x1, hx1_left, hx1_right, hx1_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg h01_strict h01_sign
  obtain ⟨x2, hx2_left, hx2_right, hx2_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg h12_strict h12_sign
  obtain ⟨x3, hx3_left, hx3_right, hx3_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg h23_strict h23_sign
  obtain ⟨x4, hx4_left, hx4_right, hx4_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg h34_strict h34_sign
  obtain ⟨x5, hx5_ge, hx5_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop (le_of_lt h4) ht_top
  have hx5_lt : auxiliaryG_six_root4 < x5 := by
    refine lt_of_le_of_ne hx5_ge ?_
    intro hx5_eq
    have hx5_eval : modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root4 = 0 := by
      simpa [Polynomial.IsRoot.def, hx5_eq] using hx5_root
    linarith
  exact ⟨x0, x1, x2, x3, x4, x5, hx0_root, hx0_lt, hx1_root, hx1_left,
    hx1_right, hx2_root, hx2_left, hx2_right, hx3_root, hx3_left, hx3_right,
    hx4_root, hx4_left, hx4_right, hx5_root, hx5_lt⟩

/-- Cross-root inequalities between an ordered `P_6` root list and the named
`G_6` roots. -/
def ModifiedNarayanaSixAuxiliaryGCrossInequalities
    (a b c d e r : ℝ) : Prop :=
  a ≤ auxiliaryG_six_root0 ∧ auxiliaryG_six_root0 ≤ b ∧
    b ≤ auxiliaryG_six_root1 ∧ auxiliaryG_six_root1 ≤ c ∧
      c ≤ auxiliaryG_six_root2 ∧ auxiliaryG_six_root2 ≤ d ∧
        d ≤ auxiliaryG_six_root3 ∧ auxiliaryG_six_root3 ≤ e ∧
          e ≤ auxiliaryG_six_root4 ∧ auxiliaryG_six_root4 ≤ r

/-- Six interval-isolated `P_6` roots determine the cross-root inequalities
against any sorted `P_6` root list. -/
theorem ModifiedNarayanaSixAuxiliaryGCrossInequalities.of_rootIntervals
    {a b c d e r : ℝ}
    (hP_roots :
      modifiedNarayanaPolynomialSix.roots =
        (↑[a, b, c, d, e, r] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (her : e ≤ r)
    (hintervals : ModifiedNarayanaSixAuxiliaryGRootIntervalCertificate) :
    ModifiedNarayanaSixAuxiliaryGCrossInequalities a b c d e r := by
  rcases hintervals with
    ⟨x0, x1, x2, x3, x4, x5, hx0_root, hx0_lt, hx1_root,
      hx01, hx1_lt, hx2_root, hx12, hx2_lt, hx3_root, hx23,
      hx3_lt, hx4_root, hx34, hx4_lt, hx5_root, hx45⟩
  have hx0x1 : x0 < x1 := lt_trans hx0_lt hx01
  have hx1x2 : x1 < x2 := lt_trans hx1_lt hx12
  have hx2x3 : x2 < x3 := lt_trans hx2_lt hx23
  have hx3x4 : x3 < x4 := lt_trans hx3_lt hx34
  have hx4x5 : x4 < x5 := lt_trans hx4_lt hx45
  have hxs_sorted_lt : ([x0, x1, x2, x3, x4, x5] : List ℝ).Pairwise (· < ·) := by
    simp [List.pairwise_cons]
    grind
  have hxs_sorted : ([x0, x1, x2, x3, x4, x5] : List ℝ).Pairwise (· ≤ ·) :=
    hxs_sorted_lt.imp (by intro _ _ h; exact le_of_lt h)
  have hxs_nodup_list : ([x0, x1, x2, x3, x4, x5] : List ℝ).Nodup :=
    hxs_sorted_lt.imp (by intro _ _ h; exact ne_of_lt h)
  have hxs_nodup : (↑[x0, x1, x2, x3, x4, x5] : Multiset ℝ).Nodup := by
    simpa using hxs_nodup_list
  have hP_ne : modifiedNarayanaPolynomialSix ≠ 0 := by
    simpa [modifiedNarayanaPolynomialSix] using modifiedNarayanaPolynomial_six_ne_zero
  have hx0_mem : x0 ∈ modifiedNarayanaPolynomialSix.roots :=
    (Polynomial.mem_roots hP_ne).mpr hx0_root
  have hx1_mem : x1 ∈ modifiedNarayanaPolynomialSix.roots :=
    (Polynomial.mem_roots hP_ne).mpr hx1_root
  have hx2_mem : x2 ∈ modifiedNarayanaPolynomialSix.roots :=
    (Polynomial.mem_roots hP_ne).mpr hx2_root
  have hx3_mem : x3 ∈ modifiedNarayanaPolynomialSix.roots :=
    (Polynomial.mem_roots hP_ne).mpr hx3_root
  have hx4_mem : x4 ∈ modifiedNarayanaPolynomialSix.roots :=
    (Polynomial.mem_roots hP_ne).mpr hx4_root
  have hx5_mem : x5 ∈ modifiedNarayanaPolynomialSix.roots :=
    (Polynomial.mem_roots hP_ne).mpr hx5_root
  have hxs_subset :
      (↑[x0, x1, x2, x3, x4, x5] : Multiset ℝ) ⊆
        modifiedNarayanaPolynomialSix.roots := by
    intro y hy
    have hy' : y = x0 ∨ y = x1 ∨ y = x2 ∨ y = x3 ∨ y = x4 ∨ y = x5 := by
      simpa only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] using hy
    rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hx0_mem
    · exact hx1_mem
    · exact hx2_mem
    · exact hx3_mem
    · exact hx4_mem
    · exact hx5_mem
  have hxs_le :
      (↑[x0, x1, x2, x3, x4, x5] : Multiset ℝ) ≤
        modifiedNarayanaPolynomialSix.roots :=
    (Multiset.le_iff_subset hxs_nodup).2 hxs_subset
  have hcard_le :
      modifiedNarayanaPolynomialSix.roots.card ≤
        (↑[x0, x1, x2, x3, x4, x5] : Multiset ℝ).card := by
    rw [hP_roots]
    norm_num
  have hxs_roots :
      (↑[x0, x1, x2, x3, x4, x5] : Multiset ℝ) =
        modifiedNarayanaPolynomialSix.roots :=
    Multiset.eq_of_le_of_card_le hxs_le hcard_le
  have hperm : ([x0, x1, x2, x3, x4, x5] : List ℝ).Perm [a, b, c, d, e, r] := by
    apply Multiset.coe_eq_coe.mp
    calc
      (↑[x0, x1, x2, x3, x4, x5] : Multiset ℝ) =
          modifiedNarayanaPolynomialSix.roots := hxs_roots
      _ = (↑[a, b, c, d, e, r] : Multiset ℝ) := hP_roots
  have habs_sorted : ([a, b, c, d, e, r] : List ℝ).Pairwise (· ≤ ·) := by
    simp [hab, hbc, hcd, hde, her, hab.trans hbc, hbc.trans hcd,
      hcd.trans hde, hde.trans her, hab.trans (hbc.trans hcd),
      hbc.trans (hcd.trans hde), hcd.trans (hde.trans her),
      hab.trans (hbc.trans (hcd.trans hde)),
      hbc.trans (hcd.trans (hde.trans her)),
      hab.trans (hbc.trans (hcd.trans (hde.trans her)))]
  have hlist_eq : [x0, x1, x2, x3, x4, x5] = [a, b, c, d, e, r] :=
    List.Perm.eq_of_pairwise' hxs_sorted habs_sorted hperm
  have hcoords : x0 = a ∧ x1 = b ∧ x2 = c ∧ x3 = d ∧ x4 = e ∧ x5 = r := by
    simpa using hlist_eq
  rcases hcoords with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨le_of_lt hx0_lt, le_of_lt hx01, le_of_lt hx1_lt, le_of_lt hx12,
    le_of_lt hx2_lt, le_of_lt hx23, le_of_lt hx3_lt, le_of_lt hx34,
    le_of_lt hx4_lt, le_of_lt hx45⟩

/-- The `P_6`/`G_6` sign certificate gives the cross-root inequalities against
any sorted `P_6` root list. -/
theorem ModifiedNarayanaSixAuxiliaryGCrossInequalities.of_eval_signs
    {a b c d e r : ℝ}
    (hP_roots :
      modifiedNarayanaPolynomialSix.roots =
        (↑[a, b, c, d, e, r] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (her : e ≤ r)
    (hsign : ModifiedNarayanaSixAuxiliaryGSignCertificate) :
    ModifiedNarayanaSixAuxiliaryGCrossInequalities a b c d e r :=
  ModifiedNarayanaSixAuxiliaryGCrossInequalities.of_rootIntervals
    hP_roots hab hbc hcd hde her
    (modifiedNarayanaPolynomial_six_rootIntervals_of_eval_signs hsign)

/-- Conditional `n = 6` Lemma 3.3 certificate, reducing the remaining work to
the `P_6` root list and cross inequalities. -/
theorem lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_roots
    {a b c d e r : ℝ}
    (hP_roots :
      (modifiedNarayanaPolynomial 6).roots =
        (↑[a, b, c, d, e, r] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (her : e ≤ r)
    (hau : a ≤ auxiliaryG_six_root0) (hub : auxiliaryG_six_root0 ≤ b)
    (hbv : b ≤ auxiliaryG_six_root1) (hvc : auxiliaryG_six_root1 ≤ c)
    (hcw : c ≤ auxiliaryG_six_root2) (hwd : auxiliaryG_six_root2 ≤ d)
    (hdz : d ≤ auxiliaryG_six_root3) (hze : auxiliaryG_six_root3 ≤ e)
    (hey : e ≤ auxiliaryG_six_root4) (hyr : auxiliaryG_six_root4 ≤ r) :
    Interlaces (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) := by
  rcases auxiliaryG_six_root_order_named with ⟨huv, hvw, hwz, hzy⟩
  exact interlaces_of_quintic_sextic_root_lists
    modifiedNarayanaPolynomial_six_ne_zero modifiedNarayanaPolynomial_six_splits
    auxiliaryG_six_ne_zero auxiliaryG_six_splits
    modifiedNarayanaPolynomial_six_natDegree auxiliaryG_six_natDegree
    hP_roots auxiliaryG_six_roots_named hab hbc hcd hde her huv hvw hwz hzy hau
    hub hbv hvc hcw hwd hdz hze hey hyr

/-- Conditional `n = 6` Lemma 3.3 certificate, with the cross inequalities
bundled as a single predicate. -/
theorem lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_root_crosses
    {a b c d e r : ℝ}
    (hP_roots :
      (modifiedNarayanaPolynomial 6).roots =
        (↑[a, b, c, d, e, r] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (her : e ≤ r)
    (hcross :
      ModifiedNarayanaSixAuxiliaryGCrossInequalities a b c d e r) :
    Interlaces (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) := by
  rcases hcross with ⟨hau, hub, hbv, hvc, hcw, hwd, hdz, hze, hey, hyr⟩
  exact lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_roots hP_roots
    hab hbc hcd hde her hau hub hbv hvc hcw hwd hdz hze hey hyr

/-- The `n = 6` Braun--Jal Lemma 3.3 interlacing follows from proving the
cross inequalities for any sorted `P_6` root list. -/
theorem lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_crosses
    (hcross :
      ∀ {a b c d e r : ℝ},
        (modifiedNarayanaPolynomial 6).roots =
          (↑[a, b, c, d, e, r] : Multiset ℝ) →
        a ≤ b → b ≤ c → c ≤ d → d ≤ e → e ≤ r →
        ModifiedNarayanaSixAuxiliaryGCrossInequalities a b c d e r) :
    Interlaces (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) := by
  obtain ⟨a, b, c, d, e, r, hP_roots, hab, hbc, hcd, hde, her⟩ :=
    modifiedNarayanaPolynomial_six_exists_ordered_roots
  exact lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_root_crosses
    hP_roots hab hbc hcd hde her (hcross hP_roots hab hbc hcd hde her)

/-- The `n = 6` Braun--Jal Lemma 3.3 proper-position form follows from proving
the cross inequalities for any sorted `P_6` root list. -/
theorem lemma33AuxiliaryGInterlaces_modified_six_of_crosses
    (hcross :
      ∀ {a b c d e r : ℝ},
        (modifiedNarayanaPolynomial 6).roots =
          (↑[a, b, c, d, e, r] : Multiset ℝ) →
        a ≤ b → b ≤ c → c ≤ d → d ≤ e → e ≤ r →
        ModifiedNarayanaSixAuxiliaryGCrossInequalities a b c d e r) :
    Prec (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) := by
  exact (lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_crosses hcross).toPrec

/-- The `n = 6` Braun--Jal Lemma 3.3 interlacing follows from the
`P_6`/`G_6` sign certificate. -/
theorem lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_eval_signs
    (hsign : ModifiedNarayanaSixAuxiliaryGSignCertificate) :
    Interlaces (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) := by
  apply lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_crosses
  intro a b c d e r hP_roots hab hbc hcd hde her
  exact ModifiedNarayanaSixAuxiliaryGCrossInequalities.of_eval_signs
    (by simpa [modifiedNarayanaPolynomialSix] using hP_roots)
    hab hbc hcd hde her hsign

/-- The `n = 6` Braun--Jal Lemma 3.3 proper-position form follows from the
`P_6`/`G_6` sign certificate. -/
theorem lemma33AuxiliaryGInterlaces_modified_six_of_eval_signs
    (hsign : ModifiedNarayanaSixAuxiliaryGSignCertificate) :
    Prec (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) :=
  (lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_eval_signs hsign).toPrec

/-- The checked `n = 6` Braun--Jal Lemma 3.3 interlacing case. -/
theorem lemma33AuxiliaryGInterlaces_modified_six_interlaces :
    Interlaces (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) :=
  lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_eval_signs
    modifiedNarayanaPolynomial_six_auxiliaryG_signCertificate

/-- The checked `n = 6` Braun--Jal Lemma 3.3 proper-position case. -/
theorem lemma33AuxiliaryGInterlaces_modified_six :
    Prec (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) :=
  lemma33AuxiliaryGInterlaces_modified_six_interlaces.toPrec

end GeneralizedSnakePosets
end RealRooted
