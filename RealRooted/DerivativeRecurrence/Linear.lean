import RealRooted.MaWang

open Polynomial

noncomputable section

namespace RealRooted

/-- Coefficient recurrence induced by a first-order polynomial recurrence whose
derivative coefficient and multiplier are linear. -/
lemma derivative_linear_coeff_succ
    (P : ℕ → ℝ[X]) (a b c : ℝ)
    (hrec : ∀ n, P (n + 1) = (C b * X) * (P n).derivative + (C a + C c * X) * P n)
    (n k : ℕ) :
    coeff (P (n + 1)) (k + 1) =
      (b * (k + 1 : ℝ) + a) * coeff (P n) (k + 1) + c * coeff (P n) k := by
  rw [hrec n]
  rw [show (C b * X) * (P n).derivative = C b * (X * (P n).derivative) by ring]
  rw [show (C a + C c * X) * P n = C a * P n + C c * (X * P n) by ring]
  simp only [coeff_add, coeff_X_mul, coeff_derivative, coeff_C_mul]
  ring

/-- Constant-coefficient recurrence induced by a first-order linear derivative
recurrence. -/
lemma derivative_linear_coeff_zero
    (P : ℕ → ℝ[X]) (a b c : ℝ)
    (hrec : ∀ n, P (n + 1) = (C b * X) * (P n).derivative + (C a + C c * X) * P n)
    (n : ℕ) :
    coeff (P (n + 1)) 0 = a * coeff (P n) 0 := by
  simp_all

/-- A first-order linear derivative recurrence starting from a positive
constant has degree equal to its index when the degree-raising coefficient is
positive. -/
theorem natDegree_of_derivative_linear_pos_const
    (P : ℕ → ℝ[X]) (a b c d : ℝ)
    (h0 : P 0 = C d)
    (hrec : ∀ n, P (n + 1) = (C b * X) * (P n).derivative + (C a + C c * X) * P n)
    (hd_pos : 0 < d) (hc_pos : 0 < c)
    (n : ℕ) :
    (P n).natDegree = n := by
  have hcoeff := derivative_linear_coeff_succ P a b c hrec
  have habove : ∀ n N : ℕ, n < N → coeff (P n) N = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro N hN
        match n with
        | 0 =>
            rw [h0, coeff_C]
            grind
        | k + 1 =>
            rcases N with _ | j
            · lia
            · grind
  have htop_pos : ∀ n : ℕ, 0 < coeff (P n) n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        match n with
        | 0 => simp_all
        | k + 1 => simp_all
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun N hN ↦ habove n N hN))
    (ne_of_gt (htop_pos n))

/-- Unit-seed specialization of `natDegree_of_derivative_linear_pos_const`. -/
theorem natDegree_of_derivative_linear
    (P : ℕ → ℝ[X]) (a b c : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) = (C b * X) * (P n).derivative + (C a + C c * X) * P n)
    (hc_pos : 0 < c)
    (n : ℕ) :
    (P n).natDegree = n := by
  exact natDegree_of_derivative_linear_pos_const P a b c 1 (by grind) hrec
    (by norm_num) hc_pos n

/-- Consecutive polynomials in a positive first-order linear derivative
recurrence interlace. -/
theorem interlaces_of_derivative_linear_pos_const
    (P : ℕ → ℝ[X]) (a b c d : ℝ)
    (h0 : P 0 = C d)
    (hrec : ∀ n, P (n + 1) = (C b * X) * (P n).derivative + (C a + C c * X) * P n)
    (hdeg : ∀ n, (P n).natDegree = n)
    (hd_pos : 0 < d) (ha_nonneg : 0 ≤ a) (hb_pos : 0 < b) (hc_pos : 0 < c)
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have hcoeff := derivative_linear_coeff_succ P a b c hrec
  have hcoeff0 := derivative_linear_coeff_zero P a b c hrec
  have hnn : ∀ n, HasNonnegCoeffs (P n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        match n with
        | 0 =>
            intro m
            cases m with
            | zero =>
                rw [h0, coeff_C_zero]
                grind
            | succ m => simp_all
        | k + 1 =>
            intro m
            cases m with
            | zero =>
                rw [hcoeff0 k]
                have h0n := ih k (by lia) 0
                positivity
            | succ j =>
                rw [hcoeff k j]
                have hj := ih k (by lia) j
                have hj1 := ih k (by lia) (j + 1)
                positivity
  have htop_pos : ∀ n : ℕ, 0 < coeff (P n) n := by
    intro n
    rw [show coeff (P n) n = (P n).leadingCoeff by rw [leadingCoeff, hdeg n]]
    exact (hnn n).pos_leadingCoeff (by grind)
  have hpos (n : ℕ) : HasPosLeadingCoeff (P n) := by
    rw [HasPosLeadingCoeff, leadingCoeff, hdeg]
    simp_all
  have hne (n : ℕ) : P n ≠ 0 := (hpos n).ne_zero
  have hP1 : P 1 = (C a + C c * X) * C d := by simp_all
  have hprec : ∀ n, Prec (P n) (P (n + 1)) := by
    intro n
    induction n with
    | zero =>
        have hInter : Interlaces (P 0) (P 1) := by
          rw [h0]
          exact interlaces_C_linear (ne_of_gt hd_pos) (p := P 1) (by grind)
        exact hInter.toPrec
    | succ n ih =>
        have hsp : (P (n + 1)).Splits := ih.2.1.2
        have hroots_nonpos : ∀ r, (P (n + 1)).IsRoot r → r ≤ 0 := fun r hr =>
          roots_nonpos_of_hasNonnegCoeffs (hnn (n + 1)) r
            ((mem_roots (hne (n + 1))).mpr hr)
        have hInter : Interlaces (P (n + 1)).derivative (P (n + 1)) := by
          by_cases hdeg1 : n + 1 = 1
          · have hn0 : n = 0 := by lia
            subst n
            change Interlaces (P 1).derivative (P 1)
            rw [hP1]
            have hder :
                ((C a + C c * X) * C d : ℝ[X]).derivative = C (c * d) := by
              simp
            rw [hder]
            exact interlaces_C_linear (mul_ne_zero (ne_of_gt hc_pos) (ne_of_gt hd_pos))
              (p := (C a + C c * X) * C d) (by grind)
          · exact derivative_interlaces hsp (by grind)
        have hg_pos : HasPosLeadingCoeff (P (n + 1)).derivative := by
          by_cases hdeg1 : n + 1 = 1
          · have hn0 : n = 0 := by lia
            subst n
            change HasPosLeadingCoeff (P 1).derivative
            rw [hP1]
            have hder :
                ((C a + C c * X) * C d : ℝ[X]).derivative = C (c * d) := by
              simp
            rw [hder]
            rw [HasPosLeadingCoeff, leadingCoeff, natDegree_C]
            simpa using mul_pos hc_pos hd_pos
          · exact (hpos (n + 1)).derivative (by grind)
        have hF_eq :
            (C a + C c * X) * P (n + 1) +
                (C b * X) * (P (n + 1)).derivative = P (n + 2) := by
          grind
        have hF_pos : HasPosLeadingCoeff
            ((C a + C c * X) * P (n + 1) +
              (C b * X) * (P (n + 1)).derivative) := by
          grind
        have hdeg_lo :
            (P (n + 1)).natDegree ≤
              ((C a + C c * X) * P (n + 1) +
                (C b * X) * (P (n + 1)).derivative).natDegree := by
          grind
        have hdeg_hi :
            ((C a + C c * X) * P (n + 1) +
                (C b * X) * (P (n + 1)).derivative).natDegree ≤
              (P (n + 1)).natDegree + 1 := by
          grind
        have hb_nonpos : ∀ r, (P (n + 1)).IsRoot r → (C b * X : ℝ[X]).eval r ≤ 0 := by
          intro r hr
          have := hroots_nonpos r hr
          simp only [eval_mul, eval_C, eval_X]
          nlinarith [le_of_lt hb_pos, this]
        have := prec_of_interlaces_evalCoeff_nonpos
          (f := P (n + 1)) (g := (P (n + 1)).derivative)
          (a := C a + C c * X) (b := C b * X)
          hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
        simp_all
  exact (hprec n).toInterlaces (by grind)

/-- Unit-seed specialization of
`interlaces_of_derivative_linear_pos_const`. -/
theorem interlaces_of_derivative_linear
    (P : ℕ → ℝ[X]) (a b c : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) = (C b * X) * (P n).derivative + (C a + C c * X) * P n)
    (hdeg : ∀ n, (P n).natDegree = n)
    (ha_nonneg : 0 ≤ a) (hb_pos : 0 < b) (hc_pos : 0 < c)
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  exact interlaces_of_derivative_linear_pos_const P a b c 1 (by grind) hrec hdeg
    (by norm_num) ha_nonneg hb_pos hc_pos n

end RealRooted
