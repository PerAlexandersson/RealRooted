import RealRooted.Interlacing.WindowInduction
import RealRooted.Applications.OEIS.A275442.Bridge.Sign
import RealRooted.AffineProperPosition
import RealRooted.Interlacing.Multiplicity
import RealRooted.Interlacing.Residue
import RealRooted.LinearPowerFamily
import RealRooted.MaWang.Strong

/-!
# The real-rootedness recurrence for OEIS A275442

Target module: `RealRooted.Applications.OEIS.A275442`.

After the affine change `X ↦ (X + 1) / 2`, the recurrence has three
positive summands.  A four-row window with five strict-interlacing edges
is closed under this recurrence; the edge between the final two rows is
deliberately absent because the induction does not need it.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A275442

/-- The polynomial recurrence whose coefficient triangle is OEIS A275442. -/
def row : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | n + 4 => row (n + 3) + row (n + 2) + (-1 + 2 * X) * row n

/-- Coefficient form of the A275442 recurrence. -/
lemma coeff_succ (n m : ℕ) :
    (row (n + 4)).coeff m =
      (row (n + 3)).coeff m + (row (n + 2)).coeff m - (row n).coeff m +
        (if 1 ≤ m then 2 * (row n).coeff (m - 1) else 0) := by
  rw [row]
  rw [show (-1 + 2 * X : ℝ[X]) * row n =
      -row n + C (2 : ℝ) * (X * row n) by
    rw [show (2 : ℝ[X]) = C (2 : ℝ) from (map_ofNat C 2).symm]
    ring]
  simp only [coeff_add, coeff_neg, coeff_C_mul]
  have hx : (X * row n).coeff m =
      if 1 ≤ m then (row n).coeff (m - 1) else 0 := by
    rw [show X * row n = X ^ 1 * row n by ring, coeff_X_pow_mul']
  grind

private theorem top_and_above :
    ∀ k : ℕ, 0 < (row k).coeff (k / 4) ∧
      ∀ m > k / 4, (row k).coeff m = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      match k with
      | 0 =>
          constructor
          · norm_num [row]
          · intro m hm
            simp [row, coeff_one, Nat.ne_of_gt hm]
      | 1 =>
          constructor
          · norm_num [row]
          · intro m hm
            simp [row, coeff_one, Nat.ne_of_gt hm]
      | 2 =>
          constructor
          · norm_num [row]
          · intro m hm
            simp [row, coeff_one, Nat.ne_of_gt hm]
      | 3 =>
          constructor
          · norm_num [row]
          · intro m hm
            rw [row]
            change (2 : ℝ[X]).coeff m = 0
            simp [show (2 : ℝ[X]) = C (2 : ℝ) from (map_ofNat C 2).symm,
              coeff_C, Nat.ne_of_gt hm]
      | n + 4 =>
          have h3 := ih (n + 3) (by lia)
          have h2 := ih (n + 2) (by lia)
          have h0 := ih n (by lia)
          have htarget : (n + 4) / 4 = n / 4 + 1 := by lia
          constructor
          · rw [htarget, coeff_succ]
            grind
          · intro m hm
            rw [htarget] at hm
            rw [coeff_succ]
            grind

/-- The degree of the `n`th A275442 row is `n / 4`. -/
theorem natDegree_row (n : ℕ) : (row n).natDegree = n / 4 := by
  rcases top_and_above n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)) htop.ne'

/-- The affine shift which changes the lag coefficient to `X`. -/
def shiftedRow (n : ℕ) : ℝ[X] :=
  (row n).comp (C (1 / 2 : ℝ) * X + C (1 / 2 : ℝ))

@[simp] lemma shiftedRow_zero : shiftedRow 0 = 1 := by
  simp [shiftedRow, row]

@[simp] lemma shiftedRow_one : shiftedRow 1 = 1 := by
  simp [shiftedRow, row]

@[simp] lemma shiftedRow_two : shiftedRow 2 = 1 := by
  simp [shiftedRow, row]

@[simp] lemma shiftedRow_three : shiftedRow 3 = 2 := by
  simp [shiftedRow, row]

/-- Recurrence for the affinely shifted rows. -/
lemma shiftedRow_succ (n : ℕ) :
    shiftedRow (n + 4) =
      shiftedRow (n + 3) + shiftedRow (n + 2) + X * shiftedRow n := by
  unfold shiftedRow
  rw [row]
  simp only [add_comp, mul_comp, X_comp]
  apply Polynomial.funext
  intro r
  simp only [eval_add, eval_mul, eval_comp, eval_C, eval_X, eval_one,
    eval_ofNat, eval_neg]
  ring

/-- The shifted rows agree with the scalar-certificate bridge family. -/
lemma shiftedRow_eq_bridge_p : ∀ n : ℕ, shiftedRow n = Bridge.p n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => simp
      | 1 => simp
      | 2 => simp
      | 3 => simp
      | n + 4 =>
          rw [shiftedRow_succ, Bridge.p_rec,
            ih (n + 3) (by lia), ih (n + 2) (by lia), ih n (by lia)]

/-- The shifted bridge agrees with the bridge used by the scalar certificate. -/
lemma shiftedBridge_eq_bridge_b (n : ℕ) :
    shiftedRow (n + 2) + X * shiftedRow n = Bridge.b n := by
  rw [Bridge.b, shiftedRow_eq_bridge_p, shiftedRow_eq_bridge_p]

/-- Every shifted row has nonnegative coefficients. -/
lemma shiftedRow_hasNonnegCoeffs : ∀ n : ℕ, HasNonnegCoeffs (shiftedRow n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | _ | n
      · rw [shiftedRow_zero]
        exact hasNonnegCoeffs_one
      · rw [shiftedRow_one]
        exact hasNonnegCoeffs_one
      · rw [shiftedRow_two]
        exact hasNonnegCoeffs_one
      · rw [shiftedRow_three]
        simpa only [map_ofNat] using
          (hasNonnegCoeffs_C (by norm_num : (0 : ℝ) ≤ 2))
      · rw [shiftedRow_succ]
        exact ((ih (n + 3) (by lia)).add (ih (n + 2) (by lia))).add
          (ih n (by lia)).X_mul

/-- Every original row has positive leading coefficient. -/
lemma row_hasPosLeadingCoeff (n : ℕ) : HasPosLeadingCoeff (row n) := by
  unfold HasPosLeadingCoeff
  rw [leadingCoeff, natDegree_row]
  exact (top_and_above n).1

/-- The affine shift preserves the degree formula. -/
lemma natDegree_shiftedRow (n : ℕ) : (shiftedRow n).natDegree = n / 4 := by
  unfold shiftedRow
  rw [Polynomial.natDegree_comp, natDegree_row]
  simp

/-- Every shifted row has positive leading coefficient. -/
lemma shiftedRow_hasPosLeadingCoeff (n : ℕ) :
    HasPosLeadingCoeff (shiftedRow n) := by
  unfold shiftedRow HasPosLeadingCoeff
  rw [Polynomial.leadingCoeff_comp (by simp)]
  have hinner :
      (C (1 / 2 : ℝ) * X + C (1 / 2 : ℝ)).leadingCoeff = 1 / 2 := by
    simp
  rw [hinner]
  exact mul_pos (row_hasPosLeadingCoeff n) (by positivity)

/-- A common strict left interleaver remains below the next shifted row. -/
lemma strictInterl_shiftedRow_succ
    (n : ℕ) (L : ℝ[X])
    (hL3 : StrictInterl L (shiftedRow (n + 3)))
    (hL2 : StrictInterl L (shiftedRow (n + 2)))
    (hLX0 : StrictInterl L (X * shiftedRow n)) :
    StrictInterl L (shiftedRow (n + 4)) := by
  have hsum : StrictInterl L
      ([shiftedRow (n + 3), shiftedRow (n + 2), X * shiftedRow n] :
        List ℝ[X]).sum := by
    apply StrictInterl.sum_left_of_common_left_signed
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact hL3
      · exact hL2
      · exact hLX0
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact shiftedRow_hasPosLeadingCoeff (n + 3)
      · exact shiftedRow_hasPosLeadingCoeff (n + 2)
      · exact (shiftedRow_hasPosLeadingCoeff n).X_mul
    · simp
  rw [shiftedRow_succ]
  simpa only [List.sum_cons, List.sum_nil, add_zero, add_assoc] using hsum

/-- The five strict edges needed by the next four-row window propagate. -/
lemma strictInterl_shiftedRow_partial_step
    (n : ℕ)
    (h01 : StrictInterl (shiftedRow n) (shiftedRow (n + 1)))
    (h02 : StrictInterl (shiftedRow n) (shiftedRow (n + 2)))
    (h12 : StrictInterl (shiftedRow (n + 1)) (shiftedRow (n + 2)))
    (h13 : StrictInterl (shiftedRow (n + 1)) (shiftedRow (n + 3)))
    (h23 : StrictInterl (shiftedRow (n + 2)) (shiftedRow (n + 3))) :
    StrictInterl (shiftedRow (n + 1)) (shiftedRow (n + 4)) ∧
      StrictInterl (shiftedRow (n + 2)) (shiftedRow (n + 4)) := by
  constructor
  · apply strictInterl_shiftedRow_succ n
    · exact h13
    · exact h12
    · exact strictInterl_mul_X_of_strictInterl_of_nonneg h01
        (shiftedRow_hasNonnegCoeffs n) (shiftedRow_hasNonnegCoeffs (n + 1))
  · apply strictInterl_shiftedRow_succ n
    · exact h23
    · exact StrictInterl.refl
        (shiftedRow_hasPosLeadingCoeff (n + 2)).ne_zero h23.1.2
    · exact strictInterl_mul_X_of_strictInterl_of_nonneg h02
        (shiftedRow_hasNonnegCoeffs n) (shiftedRow_hasNonnegCoeffs (n + 2))

/-- The bridge has the degree of the next shifted row. -/
lemma natDegree_shiftedBridge (n : ℕ) :
    (shiftedRow (n + 2) + X * shiftedRow n).natDegree = (n + 4) / 4 := by
  have hleft : (shiftedRow (n + 2)).natDegree = (n + 2) / 4 :=
    natDegree_shiftedRow (n + 2)
  have hright : (X * shiftedRow n).natDegree = n / 4 + 1 := by
    rw [natDegree_X_mul (shiftedRow_hasPosLeadingCoeff n).ne_zero,
      natDegree_shiftedRow]
  rcases lt_trichotomy (shiftedRow (n + 2)).natDegree
      (X * shiftedRow n).natDegree with hlt | heq | hgt
  · rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt, hright]
    lia
  · rw [natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff heq
      (shiftedRow_hasPosLeadingCoeff (n + 2))
      (shiftedRow_hasPosLeadingCoeff n).X_mul, hleft]
    lia
  · rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hgt, hleft]
    lia

/-- The two positive bridge summands give it positive leading coefficient. -/
lemma shiftedBridge_hasPosLeadingCoeff (n : ℕ) :
    HasPosLeadingCoeff (shiftedRow (n + 2) + X * shiftedRow n) := by
  rcases lt_trichotomy (shiftedRow (n + 2)).natDegree
      (X * shiftedRow n).natDegree with hlt | heq | hgt
  · exact hasPosLeadingCoeff_add_of_natDegree_lt_right hlt
      (shiftedRow_hasPosLeadingCoeff n).X_mul
  · exact hasPosLeadingCoeff_add_of_same_natDegree heq
      (shiftedRow_hasPosLeadingCoeff (n + 2))
      (shiftedRow_hasPosLeadingCoeff n).X_mul
  · exact hasPosLeadingCoeff_add_of_natDegree_lt_left hgt
      (shiftedRow_hasPosLeadingCoeff (n + 2))

private lemma strictInterl_of_derivative_root_sign
    {f F : ℝ[X]} (hf : f.Splits)
    (hfpos : HasPosLeadingCoeff f) (hFpos : HasPosLeadingCoeff F)
    (hfdeg : 2 ≤ f.natDegree)
    (hdeg : F.natDegree = f.natDegree ∨ F.natDegree = f.natDegree + 1)
    (hsign : ∀ r, f.IsRoot r → F.eval r * f.derivative.eval r < 0) :
    StrictInterl f F := by
  have hder : Interlaces f.derivative f :=
    derivative_interlaces_of_natDegree_ne_zero hf (by lia)
  have hderpos : HasPosLeadingCoeff f.derivative := hfpos.derivative (by lia)
  rcases hdeg with hsame | hsucc
  · exact strictInterl_of_interlaces_eval_mul_neg_same hder hderpos hFpos
      hsame hsign
  · exact strictInterl_of_interlaces_eval_mul_neg_succ hder hderpos hFpos
      hsucc hsign

/-- A preceding consecutive comparison and the scalar certificate orient the bridge. -/
lemma strictInterl_shiftedBridge_of_prev
    (n : ℕ) (hn : 5 ≤ n)
    (hprev : StrictInterl (shiftedRow (n + 2)) (shiftedRow (n + 3))) :
    StrictInterl (shiftedRow (n + 3))
      (shiftedRow (n + 2) + X * shiftedRow n) := by
  apply strictInterl_of_derivative_root_sign hprev.2.1.2
    (shiftedRow_hasPosLeadingCoeff (n + 3))
    (shiftedBridge_hasPosLeadingCoeff n)
  · rw [natDegree_shiftedRow]
    lia
  · rw [natDegree_shiftedBridge, natDegree_shiftedRow]
    lia
  · intro r hr
    have hnoCommon (s : ℝ)
        (hsPrev : (shiftedRow (n + 2)).IsRoot s)
        (hsCurr : (shiftedRow (n + 3)).IsRoot s) : False := by
      apply Bridge.no_common_root (n + 2) s
      · rwa [← shiftedRow_eq_bridge_p]
      · rw [show n + 2 + 1 = n + 3 by lia]
        rwa [← shiftedRow_eq_bridge_p]
    have hcurrNodup : (shiftedRow (n + 3)).roots.Nodup := by
      by_contra hnd
      obtain ⟨s, hsCurr, hsPrev⟩ := exists_common_root_of_not_nodup hprev hnd
      exact hnoCommon s ((mem_roots hprev.1.1).mp hsPrev)
        ((mem_roots hprev.2.1.1).mp hsCurr)
    have hprevNodup : (shiftedRow (n + 2)).roots.Nodup := by
      by_contra hnd
      obtain ⟨s, hsCurr, hsPrev⟩ := exists_common_root_of_not_nodup_g hprev hnd
      exact hnoCommon s ((mem_roots hprev.1.1).mp hsPrev)
        ((mem_roots hprev.2.1.1).mp hsCurr)
    have hrmem : r ∈ (shiftedRow (n + 3)).roots :=
      (mem_roots hprev.2.1.1).mpr hr
    have hrnot : r ∉ (shiftedRow (n + 2)).roots := by
      intro hrPrev
      exact hnoCommon r ((mem_roots hprev.1.1).mp hrPrev) hr
    have hresidue :
        0 < (shiftedRow (n + 2)).eval r *
          (shiftedRow (n + 3)).derivative.eval r :=
      residue_sign_pos hprev (shiftedRow_hasPosLeadingCoeff (n + 3))
        (shiftedRow_hasPosLeadingCoeff (n + 2)) hcurrNodup hprevNodup r
        hrmem hrnot
    have hrBridge : (Bridge.p (n + 3)).IsRoot r := by
      rwa [← shiftedRow_eq_bridge_p]
    have hpair := Bridge.bridge_pair_sign n (by lia) r hrBridge
    rw [← shiftedRow_eq_bridge_p, ← shiftedBridge_eq_bridge_b] at hpair
    have hproduct := mul_neg_of_pos_of_neg hresidue hpair
    nlinarith [sq_nonneg ((shiftedRow (n + 2)).eval r)]

/-- The bridge orientation at the five initial ranks is explicit. -/
lemma strictInterl_shiftedBridge_small (n : ℕ) (hn : n < 5) :
    StrictInterl (shiftedRow (n + 3))
      (shiftedRow (n + 2) + X * shiftedRow n) := by
  interval_cases n
  · rw [shiftedRow_zero, shiftedRow_two, shiftedRow_three]
    have honeLinear : StrictInterl (1 : ℝ[X]) (X + C 1) :=
      (interlaces_one_linear (p := X + C 1) (by simp)).toStrictInterl
    have h := StrictInterl.C_mul_left honeLinear
      (a := (2 : ℝ)) (by norm_num)
    convert h using 1
    · norm_num [map_ofNat]
    · grind
  · have h4 : shiftedRow 4 = 3 + X := by
      rw [show 4 = 0 + 4 by lia, shiftedRow_succ, shiftedRow_zero,
        shiftedRow_two, shiftedRow_three]
      ring
    rw [shiftedRow_one, shiftedRow_three, h4]
    convert
      (strictInterl_affine_linear_affine_linear_of_cross
        (u := (1 : ℝ)) (v := 3) (U := 1) (V := 2)
        (by norm_num) (by norm_num) (by norm_num)) using 1 <;>
      norm_num [map_ofNat] <;> ring
  · have h4 : shiftedRow 4 = 3 + X := by
      rw [show 4 = 0 + 4 by lia, shiftedRow_succ, shiftedRow_zero,
        shiftedRow_two, shiftedRow_three]
      ring
    have h5 : shiftedRow 5 = 5 + 2 * X := by
      rw [show 5 = 1 + 4 by lia, shiftedRow_succ, shiftedRow_one,
        shiftedRow_three, h4]
      ring
    rw [shiftedRow_two, h4, h5]
    convert
      (strictInterl_affine_linear_affine_linear_of_cross
        (u := (2 : ℝ)) (v := 5) (U := 2) (V := 3)
        (by norm_num) (by norm_num) (by norm_num)) using 1 <;>
      norm_num [map_ofNat] <;> ring
  · have h4 : shiftedRow 4 = 3 + X := by
      rw [show 4 = 0 + 4 by lia, shiftedRow_succ, shiftedRow_zero,
        shiftedRow_two, shiftedRow_three]
      ring
    have h5 : shiftedRow 5 = 5 + 2 * X := by
      rw [show 5 = 1 + 4 by lia, shiftedRow_succ, shiftedRow_one,
        shiftedRow_three, h4]
      ring
    have h6 : shiftedRow 6 = 8 + 4 * X := by
      calc
        shiftedRow 6 = shiftedRow 5 + shiftedRow 4 + X * shiftedRow 2 := by
          simpa only using shiftedRow_succ 2
        _ = 8 + 4 * X := by
          rw [shiftedRow_two, h4, h5]
          ring
    rw [shiftedRow_three, h5, h6]
    convert
      (strictInterl_affine_linear_affine_linear_of_cross
        (u := (4 : ℝ)) (v := 8) (U := 4) (V := 5)
        (by norm_num) (by norm_num) (by norm_num)) using 1 <;>
      norm_num [map_ofNat] <;> ring
  · have h4 : shiftedRow 4 = 3 + X := by
      rw [show 4 = 0 + 4 by lia, shiftedRow_succ, shiftedRow_zero,
        shiftedRow_two, shiftedRow_three]
      ring
    have h5 : shiftedRow 5 = 5 + 2 * X := by
      rw [show 5 = 1 + 4 by lia, shiftedRow_succ, shiftedRow_one,
        shiftedRow_three, h4]
      ring
    have h6 : shiftedRow 6 = 8 + 4 * X := by
      calc
        shiftedRow 6 = shiftedRow 5 + shiftedRow 4 + X * shiftedRow 2 := by
          simpa only using shiftedRow_succ 2
        _ = 8 + 4 * X := by
          rw [shiftedRow_two, h4, h5]
          ring
    have h7 : shiftedRow 7 = 13 + 8 * X := by
      calc
        shiftedRow 7 = shiftedRow 6 + shiftedRow 5 + X * shiftedRow 3 := by
          simpa only using shiftedRow_succ 3
        _ = 13 + 8 * X := by
          rw [shiftedRow_three, h5, h6]
          ring
    rw [h7, h6, h4]
    have hsqrt : (0 : ℝ) ≤ Real.sqrt 17 := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt 17 : ℝ) ^ 2 = 17 := by norm_num
    have hsqrt_lb : (15 / 4 : ℝ) ≤ Real.sqrt 17 := by nlinarith
    have hinter : Interlaces
        (X - C (-(13 / 8 : ℝ)))
        (C (1 : ℝ) *
          ((X - C ((-7 - Real.sqrt 17) / 2)) *
            (X - C ((-7 + Real.sqrt 17) / 2)))) := by
      apply interlaces_linear_quadratic_of_roots_between (c := (1 : ℝ))
      · norm_num
      · nlinarith
      · nlinarith
    have hscaled := StrictInterl.C_mul_left hinter.toStrictInterl
      (by norm_num : (8 : ℝ) ≠ 0)
    convert hscaled using 1
    · apply Polynomial.funext
      intro r
      simp only [eval_add, eval_mul, eval_C, eval_X]
      norm_num
      ring
    · apply Polynomial.funext
      intro r
      simp only [eval_mul, eval_C, eval_sub, eval_X, eval_add]
      norm_num [map_ofNat]
      grind

/-- An oriented bridge gives the missing final consecutive comparison. -/
lemma strictInterl_shiftedRow_last_new_of_bridge
    (n : ℕ)
    (hbridge : StrictInterl (shiftedRow (n + 3))
      (shiftedRow (n + 2) + X * shiftedRow n)) :
    StrictInterl (shiftedRow (n + 3)) (shiftedRow (n + 4)) := by
  let h := shiftedRow (n + 3)
  let p := shiftedRow (n + 2) + X * shiftedRow n
  have hpnonneg : HasNonnegCoeffs p :=
    (shiftedRow_hasNonnegCoeffs (n + 2)).add
      (shiftedRow_hasNonnegCoeffs n).X_mul
  have hppos : HasPosLeadingCoeff p :=
    hpnonneg.pos_leadingCoeff hbridge.2.1.1
  have hsum : StrictInterl h ([h, p] : List ℝ[X]).sum := by
    apply StrictInterl.sum_left_of_common_left
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact StrictInterl.refl hbridge.1.1 hbridge.1.2
      · exact hbridge
    · exact shiftedRow_hasPosLeadingCoeff (n + 3)
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact shiftedRow_hasPosLeadingCoeff (n + 3)
      · exact hppos
    · simp
  have hsum_eq : ([h, p] : List ℝ[X]).sum = shiftedRow (n + 4) := by
    simp only [List.sum_cons, List.sum_nil, add_zero, h, p]
    rw [shiftedRow_succ]
    ring
  rw [← hsum_eq]
  exact hsum

/-- Every shifted bridge has the orientation needed by the recurrence. -/
lemma strictInterl_shiftedBridge_all : ∀ n : ℕ,
    StrictInterl (shiftedRow (n + 3))
      (shiftedRow (n + 2) + X * shiftedRow n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 5
      · exact strictInterl_shiftedBridge_small n hn
      · have hprev := ih (n - 1) (by lia)
        have hconsecutive :=
          strictInterl_shiftedRow_last_new_of_bridge (n - 1) hprev
        have hidxPrev : n - 1 + 3 = n + 2 := by lia
        have hidxCurr : n - 1 + 4 = n + 3 := by lia
        rw [hidxPrev, hidxCurr] at hconsecutive
        exact strictInterl_shiftedBridge_of_prev n (by lia) hconsecutive

/-- The six directed edges in the complete four-row shifted window. -/
def cliqueEdges : Finset WindowEdge :=
  {⟨0, 1, .strictInterl⟩, ⟨0, 2, .strictInterl⟩,
    ⟨0, 3, .strictInterl⟩, ⟨1, 2, .strictInterl⟩,
    ⟨1, 3, .strictInterl⟩,
    ⟨2, 3, .strictInterl⟩}

private theorem cliqueEdges_source_lt : ∀ e ∈ cliqueEdges, e.source < 4 := by
  decide

private theorem cliqueEdges_target_lt : ∀ e ∈ cliqueEdges, e.target < 4 := by
  decide

private lemma strictInterl_one_one : StrictInterl (1 : ℝ[X]) 1 := by
  exact StrictInterl.refl one_ne_zero (Polynomial.Splits.of_natDegree_eq_zero natDegree_one)

private lemma strictInterl_one_two : StrictInterl (1 : ℝ[X]) 2 := by
  rw [show (2 : ℝ[X]) = C (2 : ℝ) from (map_ofNat C 2).symm]
  simpa only [one_mul, mul_one] using
    StrictInterl.C_mul_right strictInterl_one_one (a := 2) (by norm_num)

private lemma cliqueEdges_base_edge :
    ∀ e ∈ cliqueEdges, e.Holds shiftedRow 0 := by
  intro e he
  simp only [cliqueEdges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [WindowEdge.Holds, Nat.zero_add, shiftedRow_zero,
      shiftedRow_one] using
      strictInterl_one_one
  · simpa only [WindowEdge.Holds, Nat.zero_add, shiftedRow_zero,
      shiftedRow_two] using
      strictInterl_one_one
  · simpa only [WindowEdge.Holds, Nat.zero_add, shiftedRow_zero,
      shiftedRow_three] using
      strictInterl_one_two
  · simpa only [WindowEdge.Holds, Nat.zero_add, shiftedRow_one,
      shiftedRow_two] using
      strictInterl_one_one
  · simpa only [WindowEdge.Holds, Nat.zero_add, shiftedRow_one,
      shiftedRow_three] using
      strictInterl_one_two
  · simpa only [WindowEdge.Holds, Nat.zero_add, shiftedRow_two,
      shiftedRow_three] using
      strictInterl_one_two

private lemma cliqueEdges_base :
    WindowInvariant shiftedRow (fun n ↦ n / 4) cliqueEdges 0 4 := by
  refine ⟨?_, ?_, ?_, ?_, cliqueEdges_source_lt, cliqueEdges_target_lt,
    cliqueEdges_base_edge⟩
  · intro i hi
    interval_cases i <;> norm_num
  · intro i hi
    interval_cases i
    · simpa only [Nat.zero_add, shiftedRow_zero] using Polynomial.Splits.one
    · simpa only [Nat.zero_add, shiftedRow_one] using Polynomial.Splits.one
    · simpa only [Nat.zero_add, shiftedRow_two] using Polynomial.Splits.one
    · rw [Nat.zero_add, shiftedRow_three]
      apply Polynomial.Splits.of_natDegree_le_one
      · simp
  · intro i hi
    exact natDegree_shiftedRow (0 + i)
  · intro i hi
    exact shiftedRow_hasPosLeadingCoeff (0 + i)

private lemma cliqueEdges_step (n : ℕ)
    (h : WindowInvariant shiftedRow (fun k ↦ k / 4) cliqueEdges n 4) :
    WindowInvariant shiftedRow (fun k ↦ k / 4) cliqueEdges (n + 1) 4 := by
  have h01 := h.strictInterl_of_strictInterl_edge
    (i := 0) (j := 1) (by simp [cliqueEdges])
  have h02 := h.strictInterl_of_strictInterl_edge
    (i := 0) (j := 2) (by simp [cliqueEdges])
  have h12 := h.strictInterl_of_strictInterl_edge
    (i := 1) (j := 2) (by simp [cliqueEdges])
  have h13 := h.strictInterl_of_strictInterl_edge
    (i := 1) (j := 3) (by simp [cliqueEdges])
  have h23 := h.strictInterl_of_strictInterl_edge
    (i := 2) (j := 3) (by simp [cliqueEdges])
  have hnew := strictInterl_shiftedRow_partial_step n h01 h02 h12 h13 h23
  have h34 := strictInterl_shiftedRow_last_new_of_bridge n
    (strictInterl_shiftedBridge_all n)
  refine ⟨?_, ?_, ?_, ?_, cliqueEdges_source_lt, cliqueEdges_target_lt, ?_⟩
  · intro i hi
    exact (shiftedRow_hasPosLeadingCoeff (n + 1 + i)).ne_zero
  · intro i hi
    interval_cases i
    · simpa only [Nat.add_zero, Nat.add_assoc] using h.splits 1 (by norm_num)
    · simpa only [Nat.add_assoc] using h.splits 2 (by norm_num)
    · simpa only [Nat.add_assoc] using h.splits 3 (by norm_num)
    · simpa only [Nat.add_assoc] using h34.2.1.2
  · intro i hi
    exact natDegree_shiftedRow (n + 1 + i)
  · intro i hi
    exact shiftedRow_hasPosLeadingCoeff (n + 1 + i)
  · intro e he
    simp only [cliqueEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [WindowEdge.Holds, Nat.add_zero, Nat.add_assoc] using h12
    · simpa only [WindowEdge.Holds, Nat.add_zero, Nat.add_assoc] using h13
    · simpa only [WindowEdge.Holds, Nat.add_assoc] using hnew.1
    · simpa only [WindowEdge.Holds, Nat.add_assoc] using h23
    · simpa only [WindowEdge.Holds, Nat.add_assoc] using hnew.2
    · simpa only [WindowEdge.Holds, Nat.add_assoc] using h34

/-- Every four-row shifted window satisfies the complete six-edge invariant. -/
theorem shiftedRow_windowInvariant (n : ℕ) :
    WindowInvariant shiftedRow (fun k ↦ k / 4) cliqueEdges n 4 := by
  exact WindowInvariant.induction cliqueEdges_base cliqueEdges_step n

/-- All six strict-interlacing relations hold in every four-row window. -/
theorem shiftedRow_six_strictInterl (n : ℕ) :
    StrictInterl (shiftedRow n) (shiftedRow (n + 1)) ∧
    StrictInterl (shiftedRow n) (shiftedRow (n + 2)) ∧
    StrictInterl (shiftedRow n) (shiftedRow (n + 3)) ∧
    StrictInterl (shiftedRow (n + 1)) (shiftedRow (n + 2)) ∧
    StrictInterl (shiftedRow (n + 1)) (shiftedRow (n + 3)) ∧
    StrictInterl (shiftedRow (n + 2)) (shiftedRow (n + 3)) := by
  have h := shiftedRow_windowInvariant n
  exact ⟨h.strictInterl_of_strictInterl_edge
      (i := 0) (j := 1) (by simp [cliqueEdges]),
    h.strictInterl_of_strictInterl_edge
      (i := 0) (j := 2) (by simp [cliqueEdges]),
    h.strictInterl_of_strictInterl_edge
      (i := 0) (j := 3) (by simp [cliqueEdges]),
    h.strictInterl_of_strictInterl_edge
      (i := 1) (j := 2) (by simp [cliqueEdges]),
    h.strictInterl_of_strictInterl_edge
      (i := 1) (j := 3) (by simp [cliqueEdges]),
    h.strictInterl_of_strictInterl_edge
      (i := 2) (j := 3) (by simp [cliqueEdges])⟩

/-- Every affinely shifted A275442 row splits over the reals. -/
theorem shiftedRow_splits (n : ℕ) : (shiftedRow n).Splits := by
  simpa only [Nat.add_zero] using (shiftedRow_windowInvariant n).splits 0 (by norm_num)

/-- The inverse affine substitution recovers the original row. -/
lemma row_eq_shiftedRow_comp (n : ℕ) :
    row n = (shiftedRow n).comp (C (2 : ℝ) * X - 1) := by
  unfold shiftedRow
  rw [Polynomial.comp_assoc]
  have hinner :
      (C (1 / 2 : ℝ) * X + C (1 / 2 : ℝ)).comp
          (C (2 : ℝ) * X - 1) = X := by
    apply Polynomial.funext
    intro r
    simp
    ring
  rw [hinner, Polynomial.comp_X]

/-- Every A275442 row splits over the reals. -/
theorem row_splits (n : ℕ) : (row n).Splits := by
  rw [row_eq_shiftedRow_comp]
  exact (shiftedRow_splits n).comp_of_natDegree_le_one (by compute_degree!)

/-- Every A275442 row is nonzero. -/
theorem row_ne_zero (n : ℕ) : row n ≠ 0 :=
  (row_hasPosLeadingCoeff n).ne_zero

end RealRooted.Applications.OEIS.A275442
