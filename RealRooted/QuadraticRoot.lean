import Mathlib

/-!
# Real roots of quadratics with nonnegative discriminant

This file records the elementary fact that a real quadratic with nonnegative
discriminant has a real root.
-/

open Polynomial

namespace RealRooted

/-- A real quadratic `a x^2 + b x + c` with `a ≠ 0` and nonnegative
discriminant has a real root. -/
lemma exists_root_of_disc_nonneg {a b c : ℝ} (ha : a ≠ 0)
    (h : 0 ≤ b ^ 2 - 4 * a * c) :
    ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by
  set s := Real.sqrt (b ^ 2 - 4 * a * c) with hsdef
  have hs : s ^ 2 = b ^ 2 - 4 * a * c := Real.sq_sqrt h
  refine ⟨(-b + s) / (2 * a), ?_⟩
  have h2a : (2 * a) ≠ 0 := mul_ne_zero two_ne_zero ha
  field_simp
  linear_combination hs

/-- Completing the square for a quadratic in discriminant form. -/
lemma four_mul_quadratic_eq (a b c x : ℝ) :
    4 * a * (a * x ^ 2 + b * x + c) = (2 * a * x + b) ^ 2 - discrim a b c := by
  rw [discrim]
  ring

/-- The discriminant scales quadratically under common coefficient scaling. -/
lemma discrim_smul (t a b c : ℝ) :
    discrim (t * a) (t * b) (t * c) = t ^ 2 * discrim a b c := by
  unfold discrim
  ring

/-- For a genuine quadratic, a real root exists iff the discriminant is
nonnegative. -/
lemma exists_root_iff_discrim_nonneg {a b c : ℝ} (ha : a ≠ 0) :
    (∃ x : ℝ, a * x ^ 2 + b * x + c = 0) ↔ 0 ≤ discrim a b c := by
  constructor
  · rintro ⟨x, hx⟩
    have hdisc : discrim a b c = (2 * a * x + b) ^ 2 := by
      have hsq := four_mul_quadratic_eq a b c x
      rw [hx] at hsq
      nlinarith
    rw [hdisc]
    exact sq_nonneg _
  · intro h
    exact exists_root_of_disc_nonneg ha h

/-- A real quadratic polynomial with nonzero leading coefficient and
nonnegative discriminant splits over `ℝ`. -/
lemma quadraticPoly_splits_of_discrim_nonneg {a b c : ℝ} (ha : a ≠ 0)
    (hdisc : 0 ≤ discrim a b c) :
    ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits := by
  obtain ⟨x, hx⟩ := (exists_root_iff_discrim_nonneg ha).mpr hdisc
  have hdeg : ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).natDegree = 2 :=
    natDegree_quadratic ha
  have heval : ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).eval x = 0 := by
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
    linear_combination hx
  exact Polynomial.Splits.of_natDegree_eq_two hdeg heval

/-- A real polynomial written in quadratic form splits when its discriminant
is nonnegative; if the quadratic coefficient is zero, this is the linear case.
-/
lemma quadraticPoly_splits_of_discrim_nonneg_or_linear {a b c : ℝ}
    (hdisc : 0 ≤ discrim a b c) :
    ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits := by
  by_cases ha : a = 0
  · have hlinear : ((C b * X + C c) : ℝ[X]).Splits :=
      Polynomial.Splits.of_natDegree_le_one (by compute_degree)
    simpa [ha] using hlinear
  · exact quadraticPoly_splits_of_discrim_nonneg ha hdisc

/-- A real quadratic polynomial with nonzero leading coefficient and negative
discriminant does not split over `ℝ`. -/
lemma quadraticPoly_not_splits_of_discrim_neg {a b c : ℝ} (ha : a ≠ 0)
    (hdisc : discrim a b c < 0) :
    ¬ ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits := by
  set p : ℝ[X] := C a * X ^ 2 + C b * X + C c with hp
  have hdeg : p.natDegree = 2 := natDegree_quadratic ha
  have hne : ∀ s : ℝ, discrim a b c ≠ s ^ 2 := fun s h => by
    nlinarith [sq_nonneg s]
  have hnoroot : ∀ x : ℝ, ¬ p.IsRoot x := by
    intro x hx
    have hxeval : a * (x * x) + b * x + c = 0 := by
      have hpx : p.eval x = 0 := hx
      rw [hp] at hpx
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow] at hpx
      nlinarith [hpx]
    exact quadratic_ne_zero_of_discrim_ne_sq hne x hxeval
  intro hsplit
  have hcard : p.roots.card = p.natDegree := Polynomial.splits_iff_card_roots.1 hsplit
  rw [hdeg] at hcard
  have hpos : 0 < p.roots.card := by
    rw [hcard]
    norm_num
  obtain ⟨x, hxmem⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
  have hp0 : p ≠ 0 := fun h => by
    rw [h] at hdeg
    simp at hdeg
  exact hnoroot x ((mem_roots hp0).1 hxmem)

/-- Splitting criterion for a real quadratic polynomial. -/
lemma quadraticPoly_splits_iff_discrim_nonneg {a b c : ℝ} (ha : a ≠ 0) :
    ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔ 0 ≤ discrim a b c := by
  refine ⟨fun hsplit => ?_, quadraticPoly_splits_of_discrim_nonneg ha⟩
  by_contra hneg
  exact quadraticPoly_not_splits_of_discrim_neg ha (lt_of_not_ge hneg) hsplit

/-- Non-splitting criterion for a real quadratic polynomial: a genuine real
quadratic fails to split over `ℝ` iff its discriminant is negative. -/
lemma quadraticPoly_not_splits_iff_discrim_neg {a b c : ℝ} (ha : a ≠ 0) :
    ¬ ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔ discrim a b c < 0 := by
  rw [quadraticPoly_splits_iff_discrim_nonneg ha, not_le]

/-- Splitting is invariant under common nonzero scaling of quadratic
coefficients. -/
lemma quadraticPoly_smul_splits_iff {a b c t : ℝ} (ha : a ≠ 0) (ht : t ≠ 0) :
    ((C (t * a) * X ^ 2 + C (t * b) * X + C (t * c)) : ℝ[X]).Splits ↔
      ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits := by
  rw [quadraticPoly_splits_iff_discrim_nonneg (mul_ne_zero ht ha),
    quadraticPoly_splits_iff_discrim_nonneg ha, discrim_smul]
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  constructor
  · intro h
    nlinarith [h, ht2]
  · intro h
    nlinarith [h, ht2]

/-- Splitting criterion for a normalized monic real quadratic, phrased with
the explicit discriminant `b ^ 2 - 4 * c`. -/
lemma monicQuadraticPoly_splits_iff_discrim_nonneg {b c : ℝ} :
    ((X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔ 0 ≤ b ^ 2 - 4 * c := by
  have h1 :
      ((C (1 : ℝ) * X ^ 2 + C b * X + C c) : ℝ[X]) =
        X ^ 2 + C b * X + C c := by
    simp
  have hd : discrim (1 : ℝ) b c = b ^ 2 - 4 * c := by
    unfold discrim
    ring
  rw [← h1, quadraticPoly_splits_iff_discrim_nonneg (one_ne_zero), hd]

/-- Non-splitting criterion for a normalized monic real quadratic. -/
lemma monicQuadraticPoly_not_splits_iff_discrim_neg {b c : ℝ} :
    ¬ ((X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔ b ^ 2 - 4 * c < 0 := by
  rw [monicQuadraticPoly_splits_iff_discrim_nonneg, not_le]

/-- Normalization to monic form preserves splitting for genuine quadratics. -/
lemma quadraticPoly_splits_iff_monic_splits {a b c : ℝ} (ha : a ≠ 0) :
    ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔
      ((X ^ 2 + C (b / a) * X + C (c / a)) : ℝ[X]).Splits := by
  rw [quadraticPoly_splits_iff_discrim_nonneg ha,
    monicQuadraticPoly_splits_iff_discrim_nonneg]
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have hrel : discrim a b c = a ^ 2 * ((b / a) ^ 2 - 4 * (c / a)) := by
    rw [discrim]
    field_simp
  rw [hrel, mul_nonneg_iff_of_pos_left ha2]

/-- Obstruction form for a monic real quadratic, phrased as `b ^ 2 < 4 * c`. -/
lemma monicQuadraticPoly_not_splits_iff_lt {b c : ℝ} :
    ¬ ((X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔ b ^ 2 < 4 * c := by
  rw [monicQuadraticPoly_not_splits_iff_discrim_neg]
  constructor <;> intro h <;> linarith

/-- Splitting criterion for a monic real quadratic, phrased as `4 * c ≤ b ^ 2`. -/
lemma monicQuadraticPoly_splits_iff_le {b c : ℝ} :
    ((X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔ 4 * c ≤ b ^ 2 := by
  rw [monicQuadraticPoly_splits_iff_discrim_nonneg]
  constructor <;> intro h <;> linarith

/-- Non-splitting criterion after normalizing a genuine quadratic to monic form. -/
lemma quadraticPoly_not_splits_iff_monic_discrim_neg {a b c : ℝ} (ha : a ≠ 0) :
    ¬ ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔
      (b / a) ^ 2 - 4 * (c / a) < 0 := by
  rw [quadraticPoly_splits_iff_monic_splits ha,
    monicQuadraticPoly_not_splits_iff_discrim_neg]

/-- Strict-comparison form of the normalized quadratic obstruction. -/
lemma quadraticPoly_not_splits_iff_monic_lt {a b c : ℝ} (ha : a ≠ 0) :
    ¬ ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔
      (b / a) ^ 2 < 4 * (c / a) := by
  rw [quadraticPoly_not_splits_iff_monic_discrim_neg ha]
  constructor <;> intro h <;> linarith

/-- Splitting criterion after normalizing a genuine quadratic to monic form. -/
lemma quadraticPoly_splits_iff_monic_le {a b c : ℝ} (ha : a ≠ 0) :
    ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔
      4 * (c / a) ≤ (b / a) ^ 2 := by
  rw [quadraticPoly_splits_iff_monic_splits ha, monicQuadraticPoly_splits_iff_le]

/-- One-directional normalized obstruction for a genuine quadratic. -/
lemma quadraticPoly_not_splits_of_monic_lt {a b c : ℝ} (ha : a ≠ 0)
    (h : (b / a) ^ 2 < 4 * (c / a)) :
    ¬ ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits :=
  (quadraticPoly_not_splits_iff_monic_lt ha).mpr h

/-- One-directional normalized splitting criterion for a genuine quadratic. -/
lemma quadraticPoly_splits_of_monic_le {a b c : ℝ} (ha : a ≠ 0)
    (h : 4 * (c / a) ≤ (b / a) ^ 2) :
    ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits :=
  (quadraticPoly_splits_iff_monic_le ha).mpr h

/-- Strict-comparison obstruction for a quadratic with positive leading coefficient. -/
lemma quadraticPoly_not_splits_iff_lt {a b c : ℝ} (ha : 0 < a) :
    ¬ ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔ b ^ 2 < 4 * a * c := by
  rw [quadraticPoly_not_splits_iff_discrim_neg ha.ne']
  rw [discrim]
  constructor <;> intro h <;> linarith

/-- Splitting criterion for a quadratic with positive leading coefficient. -/
lemma quadraticPoly_splits_iff_le {a b c : ℝ} (ha : 0 < a) :
    ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔ 4 * a * c ≤ b ^ 2 := by
  rw [quadraticPoly_splits_iff_discrim_nonneg ha.ne']
  rw [discrim]
  constructor <;> intro h <;> linarith

/-- One-directional obstruction for a quadratic with positive leading
coefficient. -/
lemma quadraticPoly_not_splits_of_lt {a b c : ℝ} (ha : 0 < a)
    (h : b ^ 2 < 4 * a * c) :
    ¬ ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits :=
  (quadraticPoly_not_splits_iff_lt ha).mpr h

/-- One-directional splitting criterion for a quadratic with positive leading
coefficient. -/
lemma quadraticPoly_splits_of_le {a b c : ℝ} (ha : 0 < a)
    (h : 4 * a * c ≤ b ^ 2) :
    ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits :=
  (quadraticPoly_splits_iff_le ha).mpr h

/-- A splitting real quadratic has nonnegative discriminant, expressed in
coefficient form. -/
theorem quadratic_disc_coeff_le_of_splits_natDegree_two
    {p : ℝ[X]} (hdeg : p.natDegree = 2) (hs : p.Splits) :
    4 * (p.coeff 0 * p.coeff 2) ≤ p.coeff 1 ^ 2 := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hdeg
  obtain ⟨x, hxmem⟩ : ∃ x, x ∈ p.roots := by
    apply Multiset.card_pos_iff_exists_mem.mp
    rw [← hs.natDegree_eq_card_roots, hdeg]
    norm_num
  have hxroot : p.IsRoot x := (Polynomial.mem_roots hp0).mp hxmem
  have hxquad : p.coeff 2 * (x * x) + p.coeff 1 * x + p.coeff 0 = 0 := by
    rw [Polynomial.IsRoot.def] at hxroot
    rw [Polynomial.eval_eq_sum_range, hdeg] at hxroot
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hxroot
    linear_combination hxroot
  have hdisc_sq := discrim_eq_sq_of_quadratic_eq_zero hxquad
  unfold discrim at hdisc_sq
  nlinarith [sq_nonneg (2 * p.coeff 2 * x + p.coeff 1)]

/-- A splitting real polynomial of degree at most two has nonnegative
quadratic discriminant, expressed in coefficient form. -/
theorem quadratic_disc_coeff_le_of_splits_natDegree_le_two
    {p : ℝ[X]} (hdeg : p.natDegree ≤ 2) (hs : p.Splits) :
    4 * (p.coeff 0 * p.coeff 2) ≤ p.coeff 1 ^ 2 := by
  by_cases h2 : p.natDegree = 2
  · exact quadratic_disc_coeff_le_of_splits_natDegree_two h2 hs
  · have hle1 : p.natDegree ≤ 1 := Nat.lt_succ_iff.mp (lt_of_le_of_ne hdeg h2)
    have hc2 : p.coeff 2 = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hle1 (by norm_num))
    rw [hc2]
    nlinarith [sq_nonneg (p.coeff 1)]

end RealRooted
