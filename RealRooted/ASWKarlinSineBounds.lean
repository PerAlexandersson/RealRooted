import RealRooted.ASWKarlinThreshold
import RealRooted.ASWKarlinVectors
import RealRooted.Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Sign-variation bounds for Karlin sine vectors

This file contains elementary sign-variation estimates for the sampled sine
vectors used in Karlin's finite-order sector proof.
-/

noncomputable section

namespace RealRooted

/-- If the last sampled angle is at most `π`, every sampled sine is
nonnegative, so the sine vector has no sign variations. -/
lemma signVariations_sin_mul_eq_zero_of_last_le_pi
    {N : ℕ} {θ : ℝ} (hθ : 0 ≤ θ)
    (hlast : (N : ℝ) * θ ≤ Real.pi) :
    Fin.signVariations (fun j : Fin (N + 1) => Real.sin ((j : ℕ) * θ)) = 0 := by
  apply Fin.signVariations_eq_zero_of_forall_nonneg
  intro j
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · exact mul_nonneg (Nat.cast_nonneg _) hθ
  · have hj : (j : ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
    have hj_cast : ((j : ℕ) : ℝ) ≤ N := by exact_mod_cast hj
    exact (mul_le_mul_of_nonneg_right hj_cast hθ).trans hlast

/-- If the last sampled Karlin angle is at most `π`, every sampled sine is
nonnegative, so the sine vector has no sign variations. -/
lemma signVariations_aswKarlinSineVector_eq_zero_of_last_le_pi
    {θ : ℝ} {degree order blocks : ℕ} (hθ : 0 ≤ θ)
    (hlast : ((blocks * (degree + order - 1) : ℕ) : ℝ) * θ ≤ Real.pi) :
    Fin.signVariations (aswKarlinSineVector θ degree order blocks) = 0 := by
  have h := signVariations_sin_mul_eq_zero_of_last_le_pi
    (N := blocks * (degree + order - 1)) hθ hlast
  change Fin.signVariations
      (fun j : Fin (blocks * (degree + order - 1) + 1) =>
        Real.sin ((j : ℕ) * θ)) = 0
  exact h

/-- If an explicit cut separates nonnegative sampled sine entries from
nonpositive sampled sine entries, then there is at most one sign variation. -/
lemma signVariations_sin_mul_le_one_of_cut {θ : ℝ} {m n : ℕ}
    (hθ0 : 0 ≤ θ)
    (hleft : ∀ i : Fin m, ((i : ℕ) : ℝ) * θ ≤ Real.pi)
    (hright_low : ∀ i : Fin n,
      Real.pi ≤ ((m + (i : ℕ) : ℕ) : ℝ) * θ)
    (hright_high : ∀ i : Fin n,
      ((m + (i : ℕ) : ℕ) : ℝ) * θ ≤ 2 * Real.pi) :
    Fin.signVariations (fun j : Fin (m + n) => Real.sin ((j : ℕ) * θ)) ≤ 1 := by
  apply Fin.signVariations_le_one_of_castAdd_nonneg_natAdd_nonpos
  · intro i
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact mul_nonneg (Nat.cast_nonneg _) hθ0
    · simpa using hleft i
  · intro i
    apply Real.sin_nonpos_of_pi_le_of_le_two_pi
    · simpa using hright_low i
    · simpa using hright_high i

/-- If the last sampled angle is at most `2π`, then the sampled sine vector
has at most one sign variation. -/
lemma signVariations_sin_mul_le_one_of_last_le_two_pi
    {N : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hlast : (N : ℝ) * θ ≤ 2 * Real.pi) :
    Fin.signVariations (fun j : Fin (N + 1) => Real.sin ((j : ℕ) * θ)) ≤ 1 := by
  by_cases hθ : θ = 0
  · have hzero := signVariations_sin_mul_eq_zero_of_last_le_pi
      (N := N) hθ0 (by simp [hθ, Real.pi_pos.le])
    rw [hzero]
    norm_num
  have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθ)
  let q : ℕ := ⌊Real.pi / θ⌋₊
  by_cases hcut : q + 1 ≤ N + 1
  · have hle := signVariations_sin_mul_le_one_of_cut
      (θ := θ) (m := q + 1) (n := N + 1 - (q + 1)) hθ0
      (by
        intro i
        have hiq : (i : ℕ) ≤ q := Nat.lt_succ_iff.mp i.isLt
        have hi_le_q : ((i : ℕ) : ℝ) ≤ q := by exact_mod_cast hiq
        have hq_le : (q : ℝ) ≤ Real.pi / θ := by
          exact Nat.floor_le (show 0 ≤ Real.pi / θ by positivity)
        have hi_le : ((i : ℕ) : ℝ) ≤ Real.pi / θ := hi_le_q.trans hq_le
        nlinarith [mul_div_cancel₀ Real.pi hθpos.ne'])
      (by
        intro i
        have hq_lt : Real.pi / θ < ((q + 1 : ℕ) : ℝ) := by
          simpa [q, Nat.cast_add, Nat.cast_one] using
            Nat.lt_floor_add_one (Real.pi / θ)
        have hbase : Real.pi < ((q + 1 : ℕ) : ℝ) * θ := by
          nlinarith [mul_div_cancel₀ Real.pi hθpos.ne']
        have hbase_le :
            ((q + 1 : ℕ) : ℝ) ≤ ((q + 1 + (i : ℕ) : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_add_right (q + 1) (i : ℕ)
        exact hbase.le.trans (mul_le_mul_of_nonneg_right hbase_le hθ0))
      (by
        intro i
        have hindex : q + 1 + (i : ℕ) ≤ N := by
          have hi := i.isLt
          lia
        have hindex_cast : ((q + 1 + (i : ℕ) : ℕ) : ℝ) ≤ N := by
          exact_mod_cast hindex
        exact (mul_le_mul_of_nonneg_right hindex_cast hθ0).trans hlast)
    have hsum : q + 1 + (N + 1 - (q + 1)) = N + 1 := Nat.add_sub_of_le hcut
    rw [hsum] at hle
    exact hle
  · have hNq : N ≤ q := by lia
    have hlast_pi : (N : ℝ) * θ ≤ Real.pi := by
      have hN_le_q : (N : ℝ) ≤ q := by exact_mod_cast hNq
      have hq_le : (q : ℝ) ≤ Real.pi / θ := by
        exact Nat.floor_le (show 0 ≤ Real.pi / θ by positivity)
      have hN_le : (N : ℝ) ≤ Real.pi / θ := hN_le_q.trans hq_le
      nlinarith [mul_div_cancel₀ Real.pi hθpos.ne']
    have hzero := signVariations_sin_mul_eq_zero_of_last_le_pi
      (N := N) hθ0 hlast_pi
    rw [hzero]
    norm_num

/-- If the sampled angles stay below `order * π`, then sampled sine has fewer
than `order` sign variations. -/
lemma signVariations_sin_mul_lt_of_last_le_nat_mul_pi
    {N order : ℕ} {θ : ℝ} (horder : 0 < order) (hθ0 : 0 ≤ θ)
    (hlast : (N : ℝ) * θ ≤ (order : ℝ) * Real.pi) :
    Fin.signVariations (fun j : Fin (N + 1) => Real.sin ((j : ℕ) * θ)) <
      order := by
  induction order generalizing N θ with
  | zero => exact (Nat.not_lt_zero _ horder).elim
  | succ order ih =>
      cases order with
      | zero =>
          have hlast_pi : (N : ℝ) * θ ≤ Real.pi := by simpa using hlast
          have hzero := signVariations_sin_mul_eq_zero_of_last_le_pi
            (N := N) hθ0 hlast_pi
          rw [hzero]
          norm_num
      | succ prev =>
          by_cases hθ : θ = 0
          · have hzero := signVariations_sin_mul_eq_zero_of_last_le_pi
              (N := N) hθ0 (by simp [hθ, Real.pi_pos.le])
            rw [hzero]
            simp
          have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθ)
          let k : ℕ := prev + 1
          let q : ℕ := ⌊((k : ℝ) * Real.pi) / θ⌋₊
          have hk_pos : 0 < k := by positivity
          by_cases hcut : q + 1 ≤ N + 1
          · have hinit_last : (q : ℝ) * θ ≤ (k : ℝ) * Real.pi := by
              have hq_le : (q : ℝ) ≤ ((k : ℝ) * Real.pi) / θ := by
                exact Nat.floor_le (show 0 ≤ ((k : ℝ) * Real.pi) / θ by positivity)
              nlinarith [mul_div_cancel₀ ((k : ℝ) * Real.pi) hθpos.ne']
            have hinit_lt := ih (N := q) (θ := θ) hk_pos hθ0 hinit_last
            have happend :
                Fin.signVariations
                    (fun j : Fin (q + 1 + (N + 1 - (q + 1))) =>
                      Real.sin ((j : ℕ) * θ)) ≤
                  Fin.signVariations
                    (fun j : Fin (q + 1) => Real.sin ((j : ℕ) * θ)) + 1 := by
              rcases Nat.even_or_odd k with hk_even | hk_odd
              · apply Fin.signVariations_le_succ_of_natAdd_nonneg
                intro i
                apply Real.sin_nonneg_of_even_nat_mul_pi_le_of_le_succ_nat_mul_pi
                  hk_even
                · have hq_lt :
                      ((k : ℝ) * Real.pi) / θ < ((q + 1 : ℕ) : ℝ) := by
                    simpa [q, Nat.cast_add, Nat.cast_one] using
                      Nat.lt_floor_add_one (((k : ℝ) * Real.pi) / θ)
                  have hbase : (k : ℝ) * Real.pi < ((q + 1 : ℕ) : ℝ) * θ := by
                    nlinarith [mul_div_cancel₀ ((k : ℝ) * Real.pi) hθpos.ne']
                  have hbase_le :
                      ((q + 1 : ℕ) : ℝ) ≤ ((q + 1 + (i : ℕ) : ℕ) : ℝ) := by
                    exact_mod_cast Nat.le_add_right (q + 1) (i : ℕ)
                  exact hbase.le.trans (mul_le_mul_of_nonneg_right hbase_le hθ0)
                · have hindex : (Fin.natAdd (q + 1) i : ℕ) ≤ N := by
                    have hi := i.isLt
                    dsimp [Fin.natAdd]
                    lia
                  have hindex_cast : ((Fin.natAdd (q + 1) i : ℕ) : ℝ) ≤ N := by
                    exact_mod_cast hindex
                  exact (mul_le_mul_of_nonneg_right hindex_cast hθ0).trans hlast
              · apply Fin.signVariations_le_succ_of_natAdd_nonpos
                intro i
                apply Real.sin_nonpos_of_odd_nat_mul_pi_le_of_le_succ_nat_mul_pi
                  hk_odd
                · have hq_lt :
                      ((k : ℝ) * Real.pi) / θ < ((q + 1 : ℕ) : ℝ) := by
                    simpa [q, Nat.cast_add, Nat.cast_one] using
                      Nat.lt_floor_add_one (((k : ℝ) * Real.pi) / θ)
                  have hbase : (k : ℝ) * Real.pi < ((q + 1 : ℕ) : ℝ) * θ := by
                    nlinarith [mul_div_cancel₀ ((k : ℝ) * Real.pi) hθpos.ne']
                  have hbase_le :
                      ((q + 1 : ℕ) : ℝ) ≤ ((q + 1 + (i : ℕ) : ℕ) : ℝ) := by
                    exact_mod_cast Nat.le_add_right (q + 1) (i : ℕ)
                  exact hbase.le.trans (mul_le_mul_of_nonneg_right hbase_le hθ0)
                · have hindex : (Fin.natAdd (q + 1) i : ℕ) ≤ N := by
                    have hi := i.isLt
                    dsimp [Fin.natAdd]
                    lia
                  have hindex_cast : ((Fin.natAdd (q + 1) i : ℕ) : ℝ) ≤ N := by
                    exact_mod_cast hindex
                  exact (mul_le_mul_of_nonneg_right hindex_cast hθ0).trans hlast
            have hsum : q + 1 + (N + 1 - (q + 1)) = N + 1 :=
              Nat.add_sub_of_le hcut
            rw [hsum] at happend
            have hinit_le :
                Fin.signVariations
                    (fun j : Fin (q + 1) => Real.sin ((j : ℕ) * θ)) + 1 ≤ k :=
              Nat.succ_le_of_lt hinit_lt
            have hle :
                Fin.signVariations
                    (fun j : Fin (N + 1) => Real.sin ((j : ℕ) * θ)) ≤ k :=
              happend.trans hinit_le
            have hk_lt : k < Nat.succ (Nat.succ prev) := by
              simp [k]
            exact lt_of_le_of_lt hle hk_lt
          · have hNq : N ≤ q := by lia
            have hlast_prev : (N : ℝ) * θ ≤ (k : ℝ) * Real.pi := by
              have hN_le_q : (N : ℝ) ≤ q := by exact_mod_cast hNq
              have hq_le : (q : ℝ) ≤ ((k : ℝ) * Real.pi) / θ := by
                exact Nat.floor_le (show 0 ≤ ((k : ℝ) * Real.pi) / θ by positivity)
              have hN_le : (N : ℝ) ≤ ((k : ℝ) * Real.pi) / θ := hN_le_q.trans hq_le
              nlinarith [mul_div_cancel₀ ((k : ℝ) * Real.pi) hθpos.ne']
            have hlt := ih (N := N) (θ := θ) hk_pos hθ0 hlast_prev
            have hk_lt : k < Nat.succ (Nat.succ prev) := by
              simp [k]
            exact lt_trans hlt hk_lt

/-- The sampled sine vector has at most the number of completed half-turns in
its final angle. -/
lemma signVariations_sin_mul_le_floor_div_pi
    {N : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) :
    Fin.signVariations
        (fun j : Fin (N + 1) => Real.sin ((j : ℕ) * θ)) ≤
      ⌊((N : ℝ) * θ) / Real.pi⌋₊ := by
  let r : ℕ := ⌊((N : ℝ) * θ) / Real.pi⌋₊
  have hquot :
      ((N : ℝ) * θ) / Real.pi < ((r + 1 : ℕ) : ℝ) := by
    simpa only [r, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (((N : ℝ) * θ) / Real.pi)
  have hlast :
      (N : ℝ) * θ ≤ ((r + 1 : ℕ) : ℝ) * Real.pi := by
    have hmul := mul_lt_mul_of_pos_right hquot Real.pi_pos
    rw [div_mul_cancel₀ _ Real.pi_ne_zero] at hmul
    exact hmul.le
  have hlt :=
    signVariations_sin_mul_lt_of_last_le_nat_mul_pi
      (N := N) (order := r + 1) (by positivity) hθ0 hlast
  exact Nat.lt_succ_iff.mp
    (by simpa only [Nat.succ_eq_add_one] using hlt)

/-- Absolute-angle form of the sampled-sine floor bound for Karlin's repeated
vector. -/
lemma signVariations_aswKarlinSineVector_le_floor_div_pi_abs
    (θ : ℝ) (degree order blocks : ℕ) :
    Fin.signVariations (aswKarlinSineVector θ degree order blocks) ≤
      ⌊(((blocks * (degree + order - 1) : ℕ) : ℝ) * |θ|) /
        Real.pi⌋₊ := by
  by_cases hθ : 0 ≤ θ
  · rw [abs_of_nonneg hθ]
    change Fin.signVariations
        (fun j : Fin (blocks * (degree + order - 1) + 1) =>
          Real.sin ((j : ℕ) * θ)) ≤ _
    exact signVariations_sin_mul_le_floor_div_pi hθ
  · have hθneg : θ < 0 := lt_of_not_ge hθ
    rw [← signVariations_aswKarlinSineVector_neg θ degree order blocks,
      abs_of_neg hθneg]
    change Fin.signVariations
        (fun j : Fin (blocks * (degree + order - 1) + 1) =>
          Real.sin ((j : ℕ) * -θ)) ≤ _
    exact signVariations_sin_mul_le_floor_div_pi (neg_nonneg.mpr hθneg.le)

/-- One-block Karlin sine vectors inherit the general sampled-sine
sign-variation bound from a last-angle estimate. -/
lemma signVariations_aswKarlinSineVector_lt_of_last_le_order_pi
    {θ : ℝ} {degree order : ℕ} (horder : 0 < order) (hθ0 : 0 ≤ θ)
    (hlast : ((1 * (degree + order - 1) : ℕ) : ℝ) * θ ≤
      (order : ℝ) * Real.pi) :
    Fin.signVariations (aswKarlinSineVector θ degree order 1) < order := by
  have h := signVariations_sin_mul_lt_of_last_le_nat_mul_pi
    (N := 1 * (degree + order - 1)) horder hθ0 hlast
  change Fin.signVariations
      (fun j : Fin (1 * (degree + order - 1) + 1) => Real.sin ((j : ℕ) * θ)) <
    order
  exact h

/-- Below Karlin's sector threshold, the one-block Karlin sine vector has
fewer than `order` sign variations. -/
lemma signVariations_aswKarlinSineVector_lt_of_lt_threshold
    {θ : ℝ} {degree order : ℕ} (hdegree : 0 < degree) (horder : 0 < order)
    (hθ0 : 0 ≤ θ) (hθ : θ < aswSectorThreshold degree order) :
    Fin.signVariations (aswKarlinSineVector θ degree order 1) < order := by
  apply signVariations_aswKarlinSineVector_lt_of_last_le_order_pi horder hθ0
  have hden_pos := aswSectorThreshold_denom_pos degree order hdegree horder
  have hθ_le :
      θ ≤ (order : ℝ) / ((order : ℝ) + degree - 1) * Real.pi := by
    simpa [aswSectorThreshold] using hθ.le
  have hN_eq :
      ((1 * (degree + order - 1) : ℕ) : ℝ) = (order : ℝ) + degree - 1 := by
    have hsum : 1 ≤ degree + order := by lia
    calc
      ((1 * (degree + order - 1) : ℕ) : ℝ) =
          ((degree + order - 1 : ℕ) : ℝ) := by norm_num
      _ = (degree : ℝ) + order - 1 := by
          rw [Nat.cast_sub hsum, Nat.cast_add]
          norm_num
      _ = (order : ℝ) + degree - 1 := by ring
  rw [hN_eq]
  calc
    ((order : ℝ) + degree - 1) * θ ≤
        ((order : ℝ) + degree - 1) *
          ((order : ℝ) / ((order : ℝ) + degree - 1) * Real.pi) :=
      mul_le_mul_of_nonneg_left hθ_le hden_pos.le
    _ = (order : ℝ) * Real.pi := by
      field_simp [hden_pos.ne']

/-- For order one, the one-block Karlin sine vector has no sign variations
through the sector threshold. -/
lemma signVariations_aswKarlinSineVector_order_one_eq_zero_of_le_threshold
    {θ : ℝ} {degree : ℕ} (hdegree : 0 < degree) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ aswSectorThreshold degree 1) :
    Fin.signVariations (aswKarlinSineVector θ degree 1 1) = 0 := by
  apply signVariations_aswKarlinSineVector_eq_zero_of_last_le_pi hθ0
  have hdegree_pos : (0 : ℝ) < degree := by exact_mod_cast hdegree
  have hθ_le : θ ≤ Real.pi / degree := by
    have hthreshold : aswSectorThreshold degree 1 = Real.pi / degree :=
      aswSectorThreshold_order_one degree hdegree
    simpa [hthreshold] using hθ
  have hlast : (degree : ℝ) * θ ≤ Real.pi := by
    calc
      (degree : ℝ) * θ ≤ (degree : ℝ) * (Real.pi / degree) :=
        mul_le_mul_of_nonneg_left hθ_le hdegree_pos.le
      _ = Real.pi := by field_simp [hdegree_pos.ne']
  have hN : 1 * (degree + 1 - 1) = degree := by lia
  simpa [hN] using hlast

/-- Strict upper-bound form of the order-one sine estimate. -/
lemma signVariations_aswKarlinSineVector_order_one_lt
    {θ : ℝ} {degree : ℕ} (hdegree : 0 < degree) (hθ0 : 0 ≤ θ)
    (hθ : θ < aswSectorThreshold degree 1) :
    Fin.signVariations (aswKarlinSineVector θ degree 1 1) < 1 := by
  rw [signVariations_aswKarlinSineVector_order_one_eq_zero_of_le_threshold
    hdegree hθ0 hθ.le]
  norm_num

/-- Strict upper-bound form of the order-two sine estimate. -/
lemma signVariations_aswKarlinSineVector_order_two_lt
    {θ : ℝ} {degree : ℕ} (hθ0 : 0 ≤ θ)
    (hθ : θ < aswSectorThreshold degree 2) :
    Fin.signVariations (aswKarlinSineVector θ degree 2 1) < 2 := by
  have hden_pos : (0 : ℝ) < (degree + 1 : ℕ) := by positivity
  have hθ_le : θ ≤ 2 * Real.pi / ((degree + 1 : ℕ) : ℝ) := by
    have hthreshold := aswSectorThreshold_order_two degree
    simpa [hthreshold] using hθ.le
  have hlast_degree : ((degree + 1 : ℕ) : ℝ) * θ ≤ 2 * Real.pi := by
    calc
      ((degree + 1 : ℕ) : ℝ) * θ ≤
          ((degree + 1 : ℕ) : ℝ) * (2 * Real.pi / ((degree + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hθ_le (by positivity)
      _ = 2 * Real.pi := by
        field_simp [hden_pos.ne']
  have hlast : ((1 * (degree + 2 - 1) : ℕ) : ℝ) * θ ≤ 2 * Real.pi := by
    have hcoeff : 1 * (degree + 2 - 1) = degree + 1 := by lia
    simpa [hcoeff] using hlast_degree
  have hle := signVariations_sin_mul_le_one_of_last_le_two_pi
    (N := 1 * (degree + 2 - 1)) hθ0 hlast
  have hle' :
      Fin.signVariations (aswKarlinSineVector θ degree 2 1) ≤ 1 := by
    change Fin.signVariations
      (fun j : Fin (1 * (degree + 2 - 1) + 1) => Real.sin ((j : ℕ) * θ)) ≤ 1
    exact hle
  exact Nat.lt_of_le_of_lt hle' (by norm_num)

/-- In degree one, the one-block Karlin sine vector always has fewer than
`order` sign variations.  The first sampled sine is zero, leaving at most
`order` nonzero entries and hence at most `order - 1` variations. -/
lemma signVariations_aswKarlinSineVector_degree_one_lt
    (θ : ℝ) {order : ℕ} (horder : 0 < order) :
    Fin.signVariations (aswKarlinSineVector θ 1 order 1) < order := by
  have hzero : aswKarlinSineVector θ 1 order 1 0 = 0 := by
    simp [aswKarlinSineVector]
  have hle := Fin.signVariations_le_card_sub_two_of_zero_first
    (aswKarlinSineVector θ 1 order 1) hzero
  have hle' :
      Fin.signVariations (aswKarlinSineVector θ 1 order 1) ≤ order - 1 := by
    exact hle.trans (by lia)
  exact Nat.lt_of_le_pred horder hle'

/-- Threshold-shaped wrapper for the degree-one sine upper bound. -/
lemma signVariations_aswKarlinSineVector_degree_one_lt_of_lt_threshold
    {θ : ℝ} {order : ℕ} (horder : 0 < order) (_hθ0 : 0 ≤ θ)
    (_hθ : θ < aswSectorThreshold 1 order) :
    Fin.signVariations (aswKarlinSineVector θ 1 order 1) < order :=
  signVariations_aswKarlinSineVector_degree_one_lt θ horder

end RealRooted
