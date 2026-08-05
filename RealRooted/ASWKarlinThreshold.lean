import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.Field

/-!
# Karlin sector threshold

This file contains the elementary threshold notation used in Karlin's
finite-order sector theorem for Pólya-frequency sequences.
-/

noncomputable section

open Filter

namespace RealRooted

/-- The zero-free sector threshold in Karlin, *Total Positivity*, Vol. I,
Chapter 8, Theorem 3.1, for a polynomial of degree `degree` whose coefficient
sequence is PF of order `order`. -/
def aswSectorThreshold (degree order : ℕ) : ℝ :=
  (order : ℝ) / ((order : ℝ) + degree - 1) * Real.pi

/-- The denominator in Karlin's sector threshold is positive. -/
lemma aswSectorThreshold_denom_pos (degree order : ℕ) (hdegree : 0 < degree)
    (horder : 0 < order) : 0 < (order : ℝ) + degree - 1 := by
  have hdegree' : (1 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have horder' : (0 : ℝ) < order := by exact_mod_cast horder
  nlinarith

/-- Karlin's finite-order threshold is positive. -/
lemma aswSectorThreshold_pos (degree order : ℕ) (hdegree : 0 < degree)
    (horder : 0 < order) :
    0 < aswSectorThreshold degree order := by
  have hden_pos := aswSectorThreshold_denom_pos degree order hdegree horder
  have horder_pos : (0 : ℝ) < order := by exact_mod_cast horder
  have hratio_pos : 0 < (order : ℝ) / ((order : ℝ) + degree - 1) :=
    div_pos horder_pos hden_pos
  simpa [aswSectorThreshold] using mul_pos hratio_pos Real.pi_pos

/-- For order one, Karlin's sector threshold is `π / degree`. -/
lemma aswSectorThreshold_order_one (degree : ℕ) (hdegree : 0 < degree) :
    aswSectorThreshold degree 1 = Real.pi / degree := by
  have hdegree_pos : (0 : ℝ) < degree := by exact_mod_cast hdegree
  rw [aswSectorThreshold]
  field_simp [hdegree_pos.ne']
  ring

/-- For order two, Karlin's sector threshold is `2π / (degree + 1)`. -/
lemma aswSectorThreshold_order_two (degree : ℕ) :
    aswSectorThreshold degree 2 = 2 * Real.pi / ((degree + 1 : ℕ) : ℝ) := by
  rw [aswSectorThreshold]
  norm_num [Nat.cast_add]
  ring_nf

/-- In degree one, Karlin's sector threshold is `π`. -/
lemma aswSectorThreshold_degree_one (order : ℕ) (horder : 0 < order) :
    aswSectorThreshold 1 order = Real.pi := by
  have horder_pos : (0 : ℝ) < order := by exact_mod_cast horder
  rw [aswSectorThreshold]
  field_simp [horder_pos.ne']
  ring

/-- Karlin's finite-order threshold is at most `π`. -/
lemma aswSectorThreshold_le_pi (degree order : ℕ) (hdegree : 0 < degree)
    (horder : 0 < order) :
    aswSectorThreshold degree order ≤ Real.pi := by
  have hden_pos := aswSectorThreshold_denom_pos degree order hdegree horder
  have horder_le_den : (order : ℝ) ≤ (order : ℝ) + degree - 1 := by
    have hdegree' : (1 : ℝ) ≤ degree := by exact_mod_cast hdegree
    nlinarith
  have hratio : (order : ℝ) / ((order : ℝ) + degree - 1) ≤ 1 := by
    rw [div_le_one hden_pos]
    exact horder_le_den
  have hmain :
      (order : ℝ) / ((order : ℝ) + degree - 1) * Real.pi ≤ Real.pi := by
    nlinarith [Real.pi_pos, hratio]
  simpa [aswSectorThreshold] using hmain

/-- If the degree is at least two, Karlin's finite-order threshold is
strictly below `π`. -/
lemma aswSectorThreshold_lt_pi (degree order : ℕ) (hdegree : 1 < degree)
    (horder : 0 < order) :
    aswSectorThreshold degree order < Real.pi := by
  have hden_pos : 0 < (order : ℝ) + degree - 1 :=
    aswSectorThreshold_denom_pos degree order (by lia) horder
  have horder_lt_den : (order : ℝ) < (order : ℝ) + degree - 1 := by
    have hdegree' : (1 : ℝ) < degree := by exact_mod_cast hdegree
    nlinarith
  have hratio : (order : ℝ) / ((order : ℝ) + degree - 1) < 1 := by
    rw [div_lt_one hden_pos]
    exact horder_lt_den
  have hratio_nonneg : 0 ≤ (order : ℝ) / ((order : ℝ) + degree - 1) :=
    div_nonneg (by positivity) hden_pos.le
  have hmain :
      (order : ℝ) / ((order : ℝ) + degree - 1) * Real.pi < Real.pi := by
    nlinarith [Real.pi_pos, hratio, hratio_nonneg]
  simpa [aswSectorThreshold] using hmain

/-- Below Karlin's sector threshold, every repeated sampled final angle is
strictly below the corresponding integral multiple of `π`. -/
lemma aswSectorThreshold_repeated_last_angle_lt_order_pi
    {θ : ℝ} {degree order blocks : ℕ}
    (hdegree : 0 < degree) (horder : 0 < order) (hblocks : 0 < blocks)
    (hθ : θ < aswSectorThreshold degree order) :
    ((blocks * (degree + order - 1) : ℕ) : ℝ) * θ <
      ((blocks * order : ℕ) : ℝ) * Real.pi := by
  have hden_pos := aswSectorThreshold_denom_pos degree order hdegree horder
  have hblocks_pos : (0 : ℝ) < blocks := by exact_mod_cast hblocks
  have hθ_lt :
      θ < (order : ℝ) / ((order : ℝ) + degree - 1) * Real.pi := by
    simpa [aswSectorThreshold] using hθ
  have hsum : 1 ≤ degree + order := by lia
  have hlast_cast :
      ((blocks * (degree + order - 1) : ℕ) : ℝ) =
        (blocks : ℝ) * ((order : ℝ) + degree - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hsum, Nat.cast_add]
    ring
  have htarget_cast :
      ((blocks * order : ℕ) : ℝ) * Real.pi =
        (blocks : ℝ) * (order : ℝ) * Real.pi := by
    rw [Nat.cast_mul]
  rw [hlast_cast, htarget_cast]
  have hmul_pos : 0 < (blocks : ℝ) * ((order : ℝ) + degree - 1) :=
    mul_pos hblocks_pos hden_pos
  calc
    (blocks : ℝ) * ((order : ℝ) + degree - 1) * θ <
        (blocks : ℝ) * ((order : ℝ) + degree - 1) *
          ((order : ℝ) / ((order : ℝ) + degree - 1) * Real.pi) :=
      mul_lt_mul_of_pos_left hθ_lt hmul_pos
    _ = (blocks : ℝ) * (order : ℝ) * Real.pi := by
      field_simp [hden_pos.ne']

/-- For fixed degree, Karlin's finite-order sector threshold tends to `π` as
the PF order tends to infinity. -/
lemma tendsto_aswSectorThreshold (degree : ℕ) :
    Tendsto (aswSectorThreshold degree) atTop (nhds Real.pi) := by
  have hlim :=
    (tendsto_natCast_div_add_atTop ((degree : ℝ) - 1)).mul_const Real.pi
  convert hlim using 1
  · funext n
    simp only [aswSectorThreshold]
    congr 2
    ring
  · simp

end RealRooted
