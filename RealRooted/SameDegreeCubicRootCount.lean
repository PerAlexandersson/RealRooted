import RealRooted.SameDegreeDerivative
import RealRooted.SameDegreeQuadraticRootCount
import RealRooted.CubicDiscriminant

/-!
# Degree-three same-degree root-count helpers

This module records elementary cubic and quartic root-list helpers for
low-degree root-count routes.
-/

open Polynomial

namespace RealRooted

/-- A split real cubic factors through an ordered triple of real roots. -/
theorem exists_roots_triple_of_splits_natDegree_three {f : ℝ[X]}
    (hf : f.Splits) (hdeg : f.natDegree = 3) :
    ∃ a b c : ℝ, a ≤ b ∧ b ≤ c ∧ f.roots = {a, b, c} ∧
      f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) := by
  let rs := f.roots.sort (· ≤ ·)
  have hrs_len : rs.length = 3 := by
    simp [rs, card_roots_of_splits hf, hdeg]
  obtain ⟨a, b, c, hrs⟩ := List.length_eq_three.mp hrs_len
  have hrs_sorted : rs.Pairwise (· ≤ ·) := by
    simp [rs]
  have hsorted : ([a, b, c] : List ℝ).Pairwise (· ≤ ·) := by simp_all
  have hab : a ≤ b := by grind
  have hbc : b ≤ c := by simp_all
  have hcoe : f.roots = {a, b, c} := by
    have hse : (↑rs : Multiset ℝ) = f.roots := by
      simp [rs]
    rw [hrs] at hse
    rw [← hse]
    rfl
  refine ⟨a, b, c, hab, hbc, hcoe, ?_⟩
  rw [Polynomial.Splits.eq_prod_roots hf, hcoe]
  simp [Multiset.map_cons, Multiset.prod_cons, mul_assoc]

/-- Recover the leading-coefficient factorisation of a split cubic from a
specified triple of roots. -/
theorem eq_C_leadingCoeff_mul_prod_three
    {f : ℝ[X]} (hf : f.Splits) (a b c : ℝ) (hr : f.roots = {a, b, c}) :
    f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) := by
  rw [Polynomial.Splits.eq_prod_roots hf, hr]
  simp [Multiset.map_cons, Multiset.prod_cons, mul_assoc]

/-- A split real quartic factors through an ordered quadruple of real roots. -/
theorem exists_roots_quadruple_of_splits_natDegree_four {f : ℝ[X]}
    (hf : f.Splits) (hdeg : f.natDegree = 4) :
    ∃ a b c d : ℝ, a ≤ b ∧ b ≤ c ∧ c ≤ d ∧
      f.roots = {a, b, c, d} ∧
        f = C f.leadingCoeff *
          ((X - C a) * (X - C b) * (X - C c) * (X - C d)) := by
  let rs := f.roots.sort (· ≤ ·)
  have hrs_len : rs.length = 4 := by
    simp [rs, card_roots_of_splits hf, hdeg]
  obtain ⟨a, b, c, d, hrs⟩ := List.length_eq_four.mp hrs_len
  have hrs_sorted : rs.Pairwise (· ≤ ·) := by
    simp [rs]
  have hsorted : ([a, b, c, d] : List ℝ).Pairwise (· ≤ ·) := by
    simpa [hrs] using hrs_sorted
  have hab : a ≤ b := by
    simpa using (List.pairwise_cons.1 hsorted).1 b (by simp)
  have hbc : b ≤ c := by
    have htail := (List.pairwise_cons.1 hsorted).2
    simpa using (List.pairwise_cons.1 htail).1 c (by simp)
  have hcd : c ≤ d := by
    have htail := (List.pairwise_cons.1 hsorted).2
    have htail2 := (List.pairwise_cons.1 htail).2
    simpa using (List.pairwise_cons.1 htail2).1 d (by simp)
  have hcoe : f.roots = {a, b, c, d} := by
    have hse : (↑rs : Multiset ℝ) = f.roots := by
      simp [rs]
    rw [hrs] at hse
    rw [← hse]
    rfl
  refine ⟨a, b, c, d, hab, hbc, hcd, hcoe, ?_⟩
  rw [Polynomial.Splits.eq_prod_roots hf, hcoe]
  simp [Multiset.map_cons, Multiset.prod_cons, mul_assoc]

/-- For a positive-combination real-rooted split cubic pair, the corresponding
monic root pencil has nonnegative cubic discriminant at every positive
parameter.  This packages the easy direction of the discriminant route to the
two open cubic interior leaves. -/
theorem cubicDiscr_monicPencil_nonneg_of_posCombo
    {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hfs : f.Splits) (hgs : g.Splits)
    (hfd : f.natDegree = 3) (hgd : g.natDegree = 3)
    (hpc : PosComboRealRooted f g)
    (a b c p q r : ℝ)
    (hfr : f.roots = {a, b, c}) (hgr : g.roots = {p, q, r}) :
    ∀ s : ℝ, 0 < s →
      0 ≤ cubicDiscr ((X - C a) * (X - C b) * (X - C c)
        + C s * ((X - C p) * (X - C q) * (X - C r))) := by
  intro s hs
  let lf := f.leadingCoeff
  let lg := g.leadingCoeff
  let F : ℝ[X] := (X - C a) * (X - C b) * (X - C c)
  let G : ℝ[X] := (X - C p) * (X - C q) * (X - C r)
  have hlf0 : 0 < lf := by
    change 0 < f.leadingCoeff
    exact hf
  have hlg0 : 0 < lg := by
    change 0 < g.leadingCoeff
    exact hg
  have ht0 : 0 < s * lf / lg := by positivity
  have ht0' : 0 < s * f.leadingCoeff / g.leadingCoeff := by grind
  obtain ⟨_, hsplit⟩ := hpc.isRealRooted_add_right ht0'
  have hfeq : f = C lf * F := by
    simpa [lf, F] using eq_C_leadingCoeff_mul_prod_three hfs a b c hfr
  have hgeq : g = C lg * G := by
    simpa [lg, G] using eq_C_leadingCoeff_mul_prod_three hgs p q r hgr
  have hscalar : (s * lf / lg) * lg = lf * s := by
    field_simp [hlg0.ne']
  have hscaled : C (s * lf / lg) * (C lg * G) = C lf * (C s * G) := by
    calc
      C (s * lf / lg) * (C lg * G)
          = C ((s * lf / lg) * lg) * G := by rw [← mul_assoc, ← C_mul]
      _ = C (lf * s) * G := by simp_all
      _ = C lf * (C s * G) := by
        simp [G, C_mul, mul_assoc, mul_comm, mul_left_comm]
  have hcombo :
      f + C (s * f.leadingCoeff / g.leadingCoeff) * g
        = C f.leadingCoeff *
            ((X - C a) * (X - C b) * (X - C c)
              + C s * ((X - C p) * (X - C q) * (X - C r))) := by
    change f + C (s * lf / lg) * g = C lf * (F + C s * G)
    rw [hfeq, hgeq]
    calc
      C lf * F + C (s * lf / lg) * (C lg * G)
          = C lf * F + C lf * (C s * G) := by simp_all
      _ = C lf * (F + C s * G) := by grind
  have hdeg_le :
      (f + C (s * f.leadingCoeff / g.leadingCoeff) * g).natDegree ≤ 3 := by
    refine (natDegree_add_le _ _).trans ?_
    exact max_le (by simp_all) ((natDegree_C_mul_le _ _).trans (by simp_all))
  have hdisc_nonneg :
      0 ≤ cubicDiscr (f + C (s * f.leadingCoeff / g.leadingCoeff) * g) :=
    cubicDiscr_nonneg_of_splits_natDegree_le_three hdeg_le hsplit
  rw [hcombo, cubicDiscr_C_mul] at hdisc_nonneg
  have h4 : 0 < f.leadingCoeff ^ 4 := by positivity
  simp_all

/-- Evaluation of the monic cubic root pencil `F + sG`. -/
theorem eval_monicCubicPencil (a b c p q r s x : ℝ) :
    ((X - C a) * (X - C b) * (X - C c)
      + C s * ((X - C p) * (X - C q) * (X - C r))).eval x =
      (x - a) * (x - b) * (x - c) + s * ((x - p) * (x - q) * (x - r)) := by
  simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]

/-- Coefficient form of the monic cubic root pencil. -/
theorem monicCubicPencil_eq (a b c p q r s : ℝ) :
    (X - C a) * (X - C b) * (X - C c)
        + C s * ((X - C p) * (X - C q) * (X - C r)) =
      C (1 + s) * X ^ 3
        + C (-((a + b + c) + s * (p + q + r))) * X ^ 2
        + C ((a * b + b * c + c * a) + s * (p * q + q * r + r * p)) * X
        + C (-(a * b * c + s * (p * q * r))) := by grind

/-- Explicit coefficient formula for the cubic discriminant of the monic root
pencil `F + sG`, reducing the negative-discriminant leaves to one-variable
polynomial inequalities in `s`. -/
theorem cubicDiscr_monicCubicPencil_eq (a b c p q r s : ℝ) :
    cubicDiscr ((X - C a) * (X - C b) * (X - C c)
        + C s * ((X - C p) * (X - C q) * (X - C r)))
      = 18 * (1 + s) * (-((a + b + c) + s * (p + q + r)))
            * ((a * b + b * c + c * a) + s * (p * q + q * r + r * p))
            * (-(a * b * c + s * (p * q * r)))
        - 4 * (-((a + b + c) + s * (p + q + r))) ^ 3
            * (-(a * b * c + s * (p * q * r)))
        + (-((a + b + c) + s * (p + q + r))) ^ 2
            * ((a * b + b * c + c * a) + s * (p * q + q * r + r * p)) ^ 2
        - 4 * (1 + s)
            * ((a * b + b * c + c * a) + s * (p * q + q * r + r * p)) ^ 3
        - 27 * (1 + s) ^ 2 * (-(a * b * c + s * (p * q * r))) ^ 2 := by
  rw [monicCubicPencil_eq, cubicDiscr_of_coeffs]

/-- Constant term of the quartic-in-`s` cubic discriminant of the monic root
pencil. -/
theorem cubicDiscr_monicCubicPencil_apply_zero (a b c p q r : ℝ) :
    cubicDiscr ((X - C a) * (X - C b) * (X - C c)
        + C (0 : ℝ) * ((X - C p) * (X - C q) * (X - C r)))
      = ((a - b) * (b - c) * (a - c)) ^ 2 := by
  rw [cubicDiscr_monicCubicPencil_eq]
  ring

/-- The monic cubic root pencil has `natDegree` at most three. -/
theorem natDegree_monicCubicPencil_le (a b c p q r s : ℝ) :
    ((X - C a) * (X - C b) * (X - C c)
      + C s * ((X - C p) * (X - C q) * (X - C r))).natDegree ≤ 3 := by
  rw [monicCubicPencil_eq]
  compute_degree

/-- Discriminant/splitting bridge for the monic cubic root pencil. -/
theorem cubicDiscr_monicCubicPencil_neg_iff_not_splits (a b c p q r s : ℝ) :
    cubicDiscr ((X - C a) * (X - C b) * (X - C c)
        + C s * ((X - C p) * (X - C q) * (X - C r))) < 0 ↔
      ¬ ((X - C a) * (X - C b) * (X - C c)
        + C s * ((X - C p) * (X - C q) * (X - C r))).Splits := by
  rw [← not_le,
    cubicDiscr_nonneg_iff_splits_of_natDegree_le_three
      (natDegree_monicCubicPencil_le a b c p q r s)]

/-- In the strict two-below configuration with `a < r`, the monic pencil is
negative at the least root `a` of the first cubic for every positive
parameter. -/
theorem eval_monicCubicPencil_at_a_neg_twoBelow
    {a b c p q r s : ℝ} (hqa : q < a) (har : a < r) (hs : 0 < s)
    (hpq : p ≤ q) :
    ((X - C a) * (X - C b) * (X - C c)
      + C s * ((X - C p) * (X - C q) * (X - C r))).eval a < 0 := by
  rw [eval_monicCubicPencil]
  have hz : (a - a) * (a - b) * (a - c) = 0 := by ring
  rw [hz, zero_add]
  have hpa : 0 < a - p := by linarith
  have hqa' : 0 < a - q := by linarith
  have har' : a - r < 0 := by linarith
  have hg : (a - p) * (a - q) * (a - r) < 0 := by
    nlinarith [mul_pos hpa hqa']
  nlinarith [mul_neg_of_pos_of_neg hs hg]

/-- In the two-above configuration, the monic pencil is positive at the middle
root `b` of the first cubic for every positive parameter. -/
theorem eval_monicCubicPencil_at_b_pos_twoAbove
    {a b c p q r s : ℝ} (hqr : q ≤ r) (hpq : p ≤ q) (hrb : r < b)
    (hs : 0 < s) :
    0 < ((X - C a) * (X - C b) * (X - C c)
      + C s * ((X - C p) * (X - C q) * (X - C r))).eval b := by
  rw [eval_monicCubicPencil]
  have hz : (b - a) * (b - b) * (b - c) = 0 := by ring
  rw [hz, zero_add]
  have hpb : 0 < b - p := by linarith
  have hqb : 0 < b - q := by linarith
  simp_all

/-- No-real-critical-point criterion for a negative cubic discriminant.

If `a₃ X³ + a₂ X² + a₁ X + a₀` has positive leading coefficient and its
derivative has negative discriminant, then the cubic discriminant is negative. -/
theorem cubicDiscr_neg_of_deriv_disc_neg (a3 a2 a1 a0 : ℝ)
    (h3 : 0 < a3) (hderiv : a2 ^ 2 < 3 * a3 * a1) :
    cubicDiscr (C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0) < 0 := by
  rw [cubicDiscr_of_coeffs]
  have hpos : 0 < 3 * a3 * a1 - a2 ^ 2 := by linarith
  have ha3sq : 0 < a3 ^ 2 := by positivity
  nlinarith [sq_nonneg (54 * a3 ^ 2 * a0 - 2 * a2 * (9 * a3 * a1 - 2 * a2 ^ 2)),
    pow_pos hpos 3, ha3sq, mul_pos ha3sq (pow_pos hpos 3)]

/-- Specialization of `cubicDiscr_neg_of_deriv_disc_neg` to the monic cubic
root pencil `F + s G`. -/
theorem cubicDiscr_monicCubicPencil_neg_of_deriv_disc_neg
    (a b c p q r s : ℝ)
    (hlead : 0 < 1 + s)
    (hderiv : (-((a + b + c) + s * (p + q + r))) ^ 2 <
      3 * (1 + s) * ((a * b + b * c + c * a) + s * (p * q + q * r + r * p))) :
    cubicDiscr ((X - C a) * (X - C b) * (X - C c)
        + C s * ((X - C p) * (X - C q) * (X - C r))) < 0 := by
  rw [monicCubicPencil_eq]
  exact cubicDiscr_neg_of_deriv_disc_neg _ _ _ _ hlead hderiv

/-- Pure algebraic negative-discriminant leaf for the `2`-below cubic
configuration.  Together with `cubicDiscr_monicPencil_nonneg_of_posCombo`, this
rules out the corresponding positive-combination real-rooted configuration. -/
def CubicDiscrMonicPencilNegTwoBelowStatement : Prop :=
  ∀ a b c p q r : ℝ,
    a ≤ b →
    b ≤ c →
    p ≤ q →
    q ≤ r →
    q < a →
    a ≤ r →
    ∃ s : ℝ, 0 < s ∧
      cubicDiscr ((X - C a) * (X - C b) * (X - C c)
        + C s * ((X - C p) * (X - C q) * (X - C r))) < 0

/-- Affine normalization of the two-below negative-discriminant leaf.

It suffices to prove the normalized case with `a = 1` and `q = 0`; the
orientation-preserving affine map `x ↦ (x - q) / (a - q)` transports a
normalized negative-discriminant witness back to the original configuration. -/
theorem cubicDiscrMonicPencilNegTwoBelow_of_normalized
    (H : ∀ b c p r : ℝ, 1 ≤ b → b ≤ c → p ≤ 0 → 1 ≤ r →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C (1 : ℝ)) * (X - C b) * (X - C c)
          + C s * ((X - C p) * (X - C (0 : ℝ)) * (X - C r))) < 0) :
    CubicDiscrMonicPencilNegTwoBelowStatement := by
  intro a b c p q r hab hbc hpq hqr hqa har
  have haqpos : 0 < a - q := by linarith
  have haqne : a - q ≠ 0 := ne_of_gt haqpos
  obtain ⟨s, hs, hneg⟩ :=
    H ((b - q) / (a - q)) ((c - q) / (a - q))
      ((p - q) / (a - q)) ((r - q) / (a - q))
      (by rw [le_div_iff₀ haqpos]; linarith)
      (by gcongr)
      (by rw [div_nonpos_iff]; grind)
      (by rw [le_div_iff₀ haqpos]; linarith)
  refine ⟨s, hs, ?_⟩
  have key : cubicDiscr ((X - C a) * (X - C b) * (X - C c)
        + C s * ((X - C p) * (X - C q) * (X - C r)))
      = (a - q) ^ 6 * cubicDiscr ((X - C (1 : ℝ))
          * (X - C ((b - q) / (a - q)))
          * (X - C ((c - q) / (a - q)))
          + C s * ((X - C ((p - q) / (a - q))) * (X - C (0 : ℝ))
            * (X - C ((r - q) / (a - q))))) := by
    rw [cubicDiscr_monicCubicPencil_eq, cubicDiscr_monicCubicPencil_eq]
    field_simp
    ring
  rw [key]
  exact mul_neg_of_pos_of_neg (by positivity) hneg

/-- Pure algebraic negative-discriminant leaf for the `2`-above cubic
configuration. -/
def CubicDiscrMonicPencilNegTwoAboveStatement : Prop :=
  ∀ a b c p q r : ℝ,
    a ≤ b →
    b ≤ c →
    p ≤ q →
    q ≤ r →
    a ≤ r →
    r < b →
    ∃ s : ℝ, 0 < s ∧
      cubicDiscr ((X - C a) * (X - C b) * (X - C c)
        + C s * ((X - C p) * (X - C q) * (X - C r))) < 0

/-- Affine normalization of the two-above negative-discriminant leaf. -/
theorem cubicDiscrMonicPencilNegTwoAbove_of_normalized
    (H : ∀ a c p q : ℝ, a ≤ 0 → 1 ≤ c → p ≤ q → q ≤ 0 →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C a) * (X - C (1 : ℝ)) * (X - C c)
          + C s * ((X - C p) * (X - C q) * (X - C (0 : ℝ)))) < 0) :
    CubicDiscrMonicPencilNegTwoAboveStatement := by
  intro a b c p q r hab hbc hpq hqr har hrb
  have hbrpos : 0 < b - r := by linarith
  have hbrne : b - r ≠ 0 := ne_of_gt hbrpos
  obtain ⟨s, hs, hneg⟩ := H ((a - r) / (b - r)) ((c - r) / (b - r))
    ((p - r) / (b - r)) ((q - r) / (b - r))
    (by rw [div_nonpos_iff]; grind)
    (by rw [le_div_iff₀ hbrpos]; linarith)
    (by gcongr)
    (by rw [div_nonpos_iff]; grind)
  refine ⟨s, hs, ?_⟩
  have key : cubicDiscr ((X - C a) * (X - C b) * (X - C c)
        + C s * ((X - C p) * (X - C q) * (X - C r)))
      = (b - r) ^ 6 * cubicDiscr ((X - C ((a - r) / (b - r))) * (X - C (1 : ℝ))
          * (X - C ((c - r) / (b - r)))
          + C s * ((X - C ((p - r) / (b - r))) * (X - C ((q - r) / (b - r)))
            * (X - C (0 : ℝ)))) := by
    rw [cubicDiscr_monicCubicPencil_eq, cubicDiscr_monicCubicPencil_eq]
    field_simp
    ring
  rw [key]
  exact mul_neg_of_pos_of_neg (by positivity) hneg

/- The following derivative-discriminant helpers are #41-only cubic support,
not the direct #42 route. -/

/-- An upward parabola with positive discriminant and negative linear
coefficient is negative at some positive point. -/
theorem exists_pos_of_quadratic_neg (A B Cc : ℝ)
    (hA : 0 < A) (hB : B < 0) (hdisc : 4 * A * Cc < B ^ 2) :
    ∃ s : ℝ, 0 < s ∧ A * s ^ 2 + B * s + Cc < 0 := by
  have h2A : (0 : ℝ) < 2 * A := by positivity
  refine ⟨-B / (2 * A), div_pos (by linarith) h2A, ?_⟩
  have hval : A * (-B / (2 * A)) ^ 2 + B * (-B / (2 * A)) + Cc =
      (4 * A * Cc - B ^ 2) / (4 * A) := by grind
  rw [hval]
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- Per-tuple sufficient condition for a positive parameter where the monic
cubic pencil's derivative has negative discriminant. -/
theorem exists_deriv_disc_neg_of_coeffs (a b c p q r : ℝ)
    (hA : 0 < (p + q + r) ^ 2 - 3 * (p * q + q * r + r * p))
    (hB : 2 * (a + b + c) * (p + q + r) - 3 * (a * b + b * c + c * a) -
        3 * (p * q + q * r + r * p) < 0)
    (hdisc : 4 * ((p + q + r) ^ 2 - 3 * (p * q + q * r + r * p)) *
          ((a + b + c) ^ 2 - 3 * (a * b + b * c + c * a)) <
        (2 * (a + b + c) * (p + q + r) - 3 * (a * b + b * c + c * a) -
          3 * (p * q + q * r + r * p)) ^ 2) :
    ∃ s : ℝ, 0 < s ∧
      (-((a + b + c) + s * (p + q + r))) ^ 2 <
        3 * (1 + s) * ((a * b + b * c + c * a) + s * (p * q + q * r + r * p)) := by
  obtain ⟨s, hs, hlt⟩ := exists_pos_of_quadratic_neg _ _ _ hA hB hdisc
  grind

/-- #41-only sufficient condition feeding
`CubicDiscrMonicPencilNegTwoBelowStatement`: it is enough to find a positive
parameter where the monic cubic pencil's derivative has negative discriminant. -/
theorem cubicDiscrMonicPencilNegTwoBelow_of_deriv_disc
    (H : ∀ a b c p q r : ℝ, a ≤ b → b ≤ c → p ≤ q → q ≤ r → q < a → a ≤ r →
      ∃ s : ℝ, 0 < s ∧
        (-((a + b + c) + s * (p + q + r))) ^ 2 <
          3 * (1 + s) * ((a * b + b * c + c * a) + s * (p * q + q * r + r * p))) :
    CubicDiscrMonicPencilNegTwoBelowStatement := by
  intro a b c p q r hab hbc hpq hqr hqa har
  obtain ⟨s, hs, hderiv⟩ := H a b c p q r hab hbc hpq hqr hqa har
  exact ⟨s, hs,
    cubicDiscr_monicCubicPencil_neg_of_deriv_disc_neg a b c p q r s (by linarith)
      hderiv⟩

/-- #41-only sufficient condition feeding
`CubicDiscrMonicPencilNegTwoAboveStatement`: it is enough to find a positive
parameter where the monic cubic pencil's derivative has negative discriminant. -/
theorem cubicDiscrMonicPencilNegTwoAbove_of_deriv_disc
    (H : ∀ a b c p q r : ℝ, a ≤ b → b ≤ c → p ≤ q → q ≤ r → a ≤ r → r < b →
      ∃ s : ℝ, 0 < s ∧
        (-((a + b + c) + s * (p + q + r))) ^ 2 <
          3 * (1 + s) * ((a * b + b * c + c * a) + s * (p * q + q * r + r * p))) :
    CubicDiscrMonicPencilNegTwoAboveStatement := by
  intro a b c p q r hab hbc hpq hqr har hrb
  obtain ⟨s, hs, hderiv⟩ := H a b c p q r hab hbc hpq hqr har hrb
  exact ⟨s, hs,
    cubicDiscr_monicCubicPencil_neg_of_deriv_disc_neg a b c p q r s (by linarith)
      hderiv⟩

/-- #41-only: in the two-below cubic configuration the leading coefficient of
the derivative-discriminant quadratic in the pencil parameter is strictly
positive. -/
theorem derivDiscA_pos_of_lt {p q r : ℝ} (hqr : q < r) :
    0 < (p + q + r) ^ 2 - 3 * (p * q + q * r + r * p) := by
  nlinarith [mul_pos (sub_pos.mpr hqr) (sub_pos.mpr hqr),
    sq_nonneg (p - q), sq_nonneg (p - r)]

/-- #41-only wrapper reducing `CubicDiscrMonicPencilNegTwoBelowStatement` to
compact ordered-root coefficient inequalities. -/
theorem cubicDiscrMonicPencilNegTwoBelow_of_coeff_ineqs
    (H : ∀ a b c p q r : ℝ, a ≤ b → b ≤ c → p ≤ q → q ≤ r →
      q < a → a ≤ r →
        0 < (p + q + r) ^ 2 - 3 * (p * q + q * r + r * p) ∧
        2 * (a + b + c) * (p + q + r) -
            3 * (a * b + b * c + c * a) -
            3 * (p * q + q * r + r * p) < 0 ∧
        4 * ((p + q + r) ^ 2 - 3 * (p * q + q * r + r * p)) *
            ((a + b + c) ^ 2 - 3 * (a * b + b * c + c * a)) <
          (2 * (a + b + c) * (p + q + r) -
              3 * (a * b + b * c + c * a) -
              3 * (p * q + q * r + r * p)) ^ 2) :
    CubicDiscrMonicPencilNegTwoBelowStatement :=
  cubicDiscrMonicPencilNegTwoBelow_of_deriv_disc
    (fun a b c p q r hab hbc hpq hqr hqa har =>
      let ⟨hA, hB, hdisc⟩ := H a b c p q r hab hbc hpq hqr hqa har
      exists_deriv_disc_neg_of_coeffs a b c p q r hA hB hdisc)

/-- #41-only refined two-below wrapper.  Since `q < a ≤ r` forces `q < r`,
`derivDiscA_pos_of_lt` supplies the leading-coefficient inequality. -/
theorem cubicDiscrMonicPencilNegTwoBelow_of_coeff_ineqs'
    (H : ∀ a b c p q r : ℝ, a ≤ b → b ≤ c → p ≤ q → q ≤ r →
      q < a → a ≤ r →
        2 * (a + b + c) * (p + q + r) -
            3 * (a * b + b * c + c * a) -
            3 * (p * q + q * r + r * p) < 0 ∧
        4 * ((p + q + r) ^ 2 - 3 * (p * q + q * r + r * p)) *
            ((a + b + c) ^ 2 - 3 * (a * b + b * c + c * a)) <
          (2 * (a + b + c) * (p + q + r) -
              3 * (a * b + b * c + c * a) -
              3 * (p * q + q * r + r * p)) ^ 2) :
    CubicDiscrMonicPencilNegTwoBelowStatement :=
  cubicDiscrMonicPencilNegTwoBelow_of_coeff_ineqs
    (fun a b c p q r hab hbc hpq hqr hqa har =>
      let ⟨hB, hdisc⟩ := H a b c p q r hab hbc hpq hqr hqa har
      ⟨derivDiscA_pos_of_lt (lt_of_lt_of_le hqa har), hB, hdisc⟩)

/-- #41-only wrapper reducing `CubicDiscrMonicPencilNegTwoAboveStatement` to
compact ordered-root coefficient inequalities. -/
theorem cubicDiscrMonicPencilNegTwoAbove_of_coeff_ineqs
    (H : ∀ a b c p q r : ℝ, a ≤ b → b ≤ c → p ≤ q → q ≤ r →
      a ≤ r → r < b →
        0 < (p + q + r) ^ 2 - 3 * (p * q + q * r + r * p) ∧
        2 * (a + b + c) * (p + q + r) -
            3 * (a * b + b * c + c * a) -
            3 * (p * q + q * r + r * p) < 0 ∧
        4 * ((p + q + r) ^ 2 - 3 * (p * q + q * r + r * p)) *
            ((a + b + c) ^ 2 - 3 * (a * b + b * c + c * a)) <
          (2 * (a + b + c) * (p + q + r) -
              3 * (a * b + b * c + c * a) -
              3 * (p * q + q * r + r * p)) ^ 2) :
    CubicDiscrMonicPencilNegTwoAboveStatement :=
  cubicDiscrMonicPencilNegTwoAbove_of_deriv_disc
    (fun a b c p q r hab hbc hpq hqr har hrb =>
      let ⟨hA, hB, hdisc⟩ := H a b c p q r hab hbc hpq hqr har hrb
      exists_deriv_disc_neg_of_coeffs a b c p q r hA hB hdisc)

/-- Non-splitting reformulation of the `2`-below negative-discriminant leaf. -/
def CubicMonicPencilNotSplitsTwoBelowStatement : Prop :=
  ∀ a b c p q r : ℝ,
    a ≤ b →
    b ≤ c →
    p ≤ q →
    q ≤ r →
    q < a →
    a ≤ r →
    ∃ s : ℝ, 0 < s ∧
      ¬ ((X - C a) * (X - C b) * (X - C c)
        + C s * ((X - C p) * (X - C q) * (X - C r))).Splits

/-- Non-splitting reformulation of the `2`-above negative-discriminant leaf. -/
def CubicMonicPencilNotSplitsTwoAboveStatement : Prop :=
  ∀ a b c p q r : ℝ,
    a ≤ b →
    b ≤ c →
    p ≤ q →
    q ≤ r →
    a ≤ r →
    r < b →
    ∃ s : ℝ, 0 < s ∧
      ¬ ((X - C a) * (X - C b) * (X - C c)
        + C s * ((X - C p) * (X - C q) * (X - C r))).Splits

/-- The `2`-below negative-discriminant leaf is equivalent to non-splitting. -/
theorem cubicDiscrMonicPencilNegTwoBelow_iff_notSplits :
    CubicDiscrMonicPencilNegTwoBelowStatement ↔
      CubicMonicPencilNotSplitsTwoBelowStatement := by
  constructor
  · intro h a b c p q r hab hbc hpq hqr hqa har
    obtain ⟨s, hs, hd⟩ := h a b c p q r hab hbc hpq hqr hqa har
    exact ⟨s, hs,
      (cubicDiscr_monicCubicPencil_neg_iff_not_splits a b c p q r s).mp hd⟩
  · intro h a b c p q r hab hbc hpq hqr hqa har
    obtain ⟨s, hs, hd⟩ := h a b c p q r hab hbc hpq hqr hqa har
    exact ⟨s, hs,
      (cubicDiscr_monicCubicPencil_neg_iff_not_splits a b c p q r s).mpr hd⟩

/-- The `2`-above negative-discriminant leaf is equivalent to non-splitting. -/
theorem cubicDiscrMonicPencilNegTwoAbove_iff_notSplits :
    CubicDiscrMonicPencilNegTwoAboveStatement ↔
      CubicMonicPencilNotSplitsTwoAboveStatement := by
  constructor
  · intro h a b c p q r hab hbc hpq hqr har hrb
    obtain ⟨s, hs, hd⟩ := h a b c p q r hab hbc hpq hqr har hrb
    exact ⟨s, hs,
      (cubicDiscr_monicCubicPencil_neg_iff_not_splits a b c p q r s).mp hd⟩
  · intro h a b c p q r hab hbc hpq hqr har hrb
    obtain ⟨s, hs, hd⟩ := h a b c p q r hab hbc hpq hqr har hrb
    exact ⟨s, hs,
      (cubicDiscr_monicCubicPencil_neg_iff_not_splits a b c p q r s).mpr hd⟩

/-- Root count of a three-element multiset below a threshold, as a sum of
indicators. -/
theorem card_filter_le_triple (a b c x : ℝ) :
    (({a, b, c} : Multiset ℝ).filter (· ≤ x)).card =
      (if a ≤ x then 1 else 0) + (if b ≤ x then 1 else 0) +
        (if c ≤ x then 1 else 0) := by
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton]
  split_ifs <;> simp_all [Multiset.card_cons]

/-- Two split quadratics with positive leading coefficients whose roots are
separated by a gap cannot form a positive-combination real-rooted pair. -/
theorem not_posComboRealRooted_quadratic_separated
    {q1 q2 : ℝ[X]} (h1 : HasPosLeadingCoeff q1) (h2 : HasPosLeadingCoeff q2)
    (hd1 : q1.natDegree = 2) (hd2 : q2.natDegree = 2)
    (hs1 : q1.Splits) (hs2 : q2.Splits)
    (z1 z2 : ℝ) (hz : z1 < z2)
    (hq2le : ∀ r ∈ q2.roots, r ≤ z1) (hq1ge : ∀ r ∈ q1.roots, z2 ≤ r) :
    ¬ PosComboRealRooted q1 q2 := by
  intro hpc
  obtain ⟨a, b, hab, hq1roots, hq1fac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hs1 hd1
  obtain ⟨c, d, hcd, hq2roots, hq2fac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hs2 hd2
  have ha : z2 ≤ a := hq1ge a (by rw [hq1roots]; simp)
  have hd : d ≤ z1 := hq2le d (by rw [hq2roots]; simp)
  have hsep : d < a := lt_of_le_of_lt hd (lt_of_lt_of_le hz ha)
  rw [hq1fac, hq2fac] at hpc
  exact not_posComboRealRooted_pos_scaled_quadratic_roots_separated
    h1 h2 hab hcd hsep hpc

/-- A positive-combination real-rooted same-degree cubic pair with positive
leading coefficients cannot be fully separated by a strict gap. -/
theorem not_posComboRealRooted_cubic_separated
    {f g : ℝ[X]} (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hfs : f.Splits) (hgs : g.Splits)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 3)
    (hfg : PosComboRealRooted f g)
    (z1 z2 : ℝ) (hz : z1 < z2)
    (hgle : ∀ r ∈ g.roots, r ≤ z1) (hfge : ∀ r ∈ f.roots, z2 ≤ r) :
    False := by
  have hderpc : PosComboRealRooted f.derivative g.derivative :=
    posComboRealRooted_derivative hf hg (by simp_all)
      (by simp_all) hfg
  have hf'deg : f.derivative.natDegree = 2 := by simp_all
  have hg'deg : g.derivative.natDegree = 2 := by simp_all
  have hf'splits : f.derivative.Splits := by
    rcases derivative_eq_zero_or_ne_zero_and_splits hfs with h | h <;> simp_all
  have hg'splits : g.derivative.Splits := by
    rcases derivative_eq_zero_or_ne_zero_and_splits hgs with h | h <;> simp_all
  have hf'pos : HasPosLeadingCoeff f.derivative :=
    hf.derivative (by simp_all)
  have hg'pos : HasPosLeadingCoeff g.derivative :=
    hg.derivative (by simp_all)
  have hg'le : ∀ r ∈ g.derivative.roots, r ≤ z1 :=
    roots_le_of_prec_right
      (derivative_interlaces hgs (by simp_all)).toPrec hgle
  have hf'ge : ∀ r ∈ f.derivative.roots, z2 ≤ r :=
    le_roots_derivative_of_le_roots hfs (by simp_all) hfge
  exact not_posComboRealRooted_quadratic_separated
    hf'pos hg'pos hf'deg hg'deg hf'splits hg'splits z1 z2 hz hg'le hf'ge hderpc

/-- Degree-three same-degree root-count bound.

For two split real cubics with positive leading coefficients forming a
positive-combination real-rooted pair, the two lower-threshold root-count
functions differ by at most two at every threshold. -/
theorem sameDegree_cubic_rootCount_le_two
    {f g : ℝ[X]}
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 3)
    (hf : f.Splits) (hg : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hpc : PosComboRealRooted f g) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 2 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 := by
  intro x
  obtain ⟨a, b, c, hab, hbc, hfroots, _⟩ :=
    exists_roots_triple_of_splits_natDegree_three hf hfdeg
  obtain ⟨p, q, r, hpq, hqr, hgroots, _⟩ :=
    exists_roots_triple_of_splits_natDegree_three hg hgdeg
  have hfmem : ∀ s ∈ f.roots, s = a ∨ s = b ∨ s = c := by
    intro s hs
    rw [hfroots] at hs
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hs
    grind
  have hgmem : ∀ s ∈ g.roots, s = p ∨ s = q ∨ s = r := by
    intro s hs
    rw [hgroots] at hs
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hs
    grind
  have hno1 : ¬ (c ≤ x ∧ x < p) := by
    rintro ⟨hcx, hxp⟩
    exact not_posComboRealRooted_cubic_separated (f := g) (g := f)
      hg_pos hf_pos hg hf hgdeg hfdeg hpc.comm x p hxp
      (fun s hs ↦ by grind)
      (fun s hs ↦ by grind)
  have hno2 : ¬ (r ≤ x ∧ x < a) := by
    rintro ⟨hrx, hxa⟩
    exact not_posComboRealRooted_cubic_separated (f := f) (g := g)
      hf_pos hg_pos hf hg hfdeg hgdeg hpc x a hxa
      (fun s hs ↦ by grind)
      (fun s hs ↦ by grind)
  rw [hfroots, hgroots, card_filter_le_triple, card_filter_le_triple]
  grind

/-- Finite indicator-level core for the cubic same-degree root-count bound of
`1`.  For ordered triples `a ≤ b ≤ c` and `p ≤ q ≤ r` satisfying the four
interleaving inequalities `p ≤ b`, `q ≤ c`, `a ≤ q`, `b ≤ r`, the two
threshold indicator counts differ by at most one, in both directions.  This is
the degree-three analogue of `count_pair_diff_le_one`. -/
theorem card_filter_triple_diff_le_one
    (a b c p q r x : ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) (hpq : p ≤ q) (hqr : q ≤ r)
    (hpb : p ≤ b) (hqc : q ≤ c) (haq : a ≤ q) (hbr : b ≤ r) :
    (((if a ≤ x then 1 else 0) + (if b ≤ x then 1 else 0) +
          (if c ≤ x then 1 else 0) : ℤ) -
        ((if p ≤ x then 1 else 0) + (if q ≤ x then 1 else 0) +
          (if r ≤ x then 1 else 0)) ≤ 1) ∧
    (((if p ≤ x then 1 else 0) + (if q ≤ x then 1 else 0) +
          (if r ≤ x then 1 else 0) : ℤ) -
        ((if a ≤ x then 1 else 0) + (if b ≤ x then 1 else 0) +
          (if c ≤ x then 1 else 0)) ≤ 1) := by grind

/-- Partial-separation-free leaf for the cubic same-degree root count.

For a split cubic positive-combination pair with positive leading coefficients,
and roots listed in ascending order (`a ≤ b ≤ c` for `f`, `p ≤ q ≤ r` for
`g`), the smallest root of `f` lies at or below the middle root of `g`, and the
middle root of `f` lies at or below the largest root of `g`.

Equivalently: `g` has at most one root strictly below every root of `f`, and
`f` has at most one root strictly above every root of `g`.  This is exactly the
remaining analytic content needed to upgrade the cubic root-count bound from
`≤ 2` (`sameDegree_cubic_rootCount_le_two`) to `≤ 1`: the full-separation
obstruction `not_posComboRealRooted_cubic_separated` already rules out the case
where all three roots of `g` lie below all of `f`, so what remains is the
`2`-below / `2`-above partial-separation obstruction. -/
def CubicSecondRootBoundStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    f.Splits →
    g.Splits →
    f.natDegree = 3 →
    g.natDegree = 3 →
    PosComboRealRooted f g →
    ∀ a b c p q r : ℝ,
      a ≤ b →
      b ≤ c →
      p ≤ q →
      q ≤ r →
      f.roots = {a, b, c} →
      g.roots = {p, q, r} →
      a ≤ q ∧ b ≤ r

/-- Interior `2`-below partial-separation obstruction for split cubic pairs.

For ordered cubic roots `a ≤ b ≤ c` of `f` and `p ≤ q ≤ r` of `g`, this rules
out the case where `q < a` but `a ≤ r`.  The complementary case `r < a` is the
full-separation obstruction already handled by
`not_posComboRealRooted_cubic_separated`. -/
def CubicInteriorTwoBelowStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    f.Splits →
    g.Splits →
    f.natDegree = 3 →
    g.natDegree = 3 →
    PosComboRealRooted f g →
    ∀ a b c p q r : ℝ,
      a ≤ b →
      b ≤ c →
      p ≤ q →
      q ≤ r →
      f.roots = {a, b, c} →
      g.roots = {p, q, r} →
      q < a →
      a ≤ r →
      False

/-- Interior `2`-above partial-separation obstruction for split cubic pairs. -/
def CubicInteriorTwoAboveStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    f.Splits →
    g.Splits →
    f.natDegree = 3 →
    g.natDegree = 3 →
    PosComboRealRooted f g →
    ∀ a b c p q r : ℝ,
      a ≤ b →
      b ≤ c →
      p ≤ q →
      q ≤ r →
      f.roots = {a, b, c} →
      g.roots = {p, q, r} →
      a ≤ r →
      r < b →
      False

/-- The negative-discriminant monic-pencil leaf implies the interior `2`-below
obstruction. -/
theorem cubicInteriorTwoBelow_of_discr_monicPencil_neg
    (hneg : CubicDiscrMonicPencilNegTwoBelowStatement) :
    CubicInteriorTwoBelowStatement := by
  intro f g hf hg hfs hgs hfd hgd hpc a b c p q r hab hbc hpq hqr hfr hgr hqa har
  have hnonneg :=
    cubicDiscr_monicPencil_nonneg_of_posCombo
      hf hg hfs hgs hfd hgd hpc a b c p q r hfr hgr
  obtain ⟨s, hs, hlt⟩ := hneg a b c p q r hab hbc hpq hqr hqa har
  grind

/-- The negative-discriminant monic-pencil leaf implies the interior `2`-above
obstruction. -/
theorem cubicInteriorTwoAbove_of_discr_monicPencil_neg
    (hneg : CubicDiscrMonicPencilNegTwoAboveStatement) :
    CubicInteriorTwoAboveStatement := by
  intro f g hf hg hfs hgs hfd hgd hpc a b c p q r hab hbc hpq hqr hfr hgr har hrb
  have hnonneg :=
    cubicDiscr_monicPencil_nonneg_of_posCombo
      hf hg hfs hgs hfd hgd hpc a b c p q r hfr hgr
  obtain ⟨s, hs, hlt⟩ := hneg a b c p q r hab hbc hpq hqr har hrb
  grind

/-- Normalized two-above negative-discriminant data implies the interior
two-above obstruction. -/
theorem cubicInteriorTwoAbove_of_normalized
    (H : ∀ a c p q : ℝ, a ≤ 0 → 1 ≤ c → p ≤ q → q ≤ 0 →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C a) * (X - C (1 : ℝ)) * (X - C c)
          + C s * ((X - C p) * (X - C q) * (X - C (0 : ℝ)))) < 0) :
    CubicInteriorTwoAboveStatement :=
  cubicInteriorTwoAbove_of_discr_monicPencil_neg
    (cubicDiscrMonicPencilNegTwoAbove_of_normalized H)

/-- The two interior cubic obstructions imply the second-root bound leaf. -/
theorem cubicSecondRootBound_of_interior
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement) :
    CubicSecondRootBoundStatement := by
  intro f g hf hg hfs hgs hfd hgd hpc a b c p q r hab hbc hpq hqr hfr hgr
  have hfmem : ∀ x ∈ f.roots, x = a ∨ x = b ∨ x = c := by
    simp_all
  have hgmem : ∀ x ∈ g.roots, x = p ∨ x = q ∨ x = r := by simp_all
  refine ⟨?_, ?_⟩
  · by_contra hnot
    have hcon : q < a := not_le.mp hnot
    rcases lt_or_ge r a with hra | har
    · exact not_posComboRealRooted_cubic_separated hf hg hfs hgs hfd hgd hpc r a hra
        (fun x hx ↦ by grind)
        (fun x hx ↦ by grind)
    · exact hbelow hf hg hfs hgs hfd hgd hpc a b c p q r
        hab hbc hpq hqr hfr hgr hcon har
  · by_contra hnot
    have hcon : r < b := not_le.mp hnot
    rcases lt_or_ge r a with hra | har
    · exact not_posComboRealRooted_cubic_separated hf hg hfs hgs hfd hgd hpc r a hra
        (fun x hx ↦ by grind)
        (fun x hx ↦ by grind)
    · exact habove hf hg hfs hgs hfd hgd hpc a b c p q r
        hab hbc hpq hqr hfr hgr har hcon

/-- The two negative-discriminant monic-pencil leaves imply the cubic
second-root bound. -/
theorem cubicSecondRootBound_of_discr_monicPencil_neg
    (hbelow : CubicDiscrMonicPencilNegTwoBelowStatement)
    (habove : CubicDiscrMonicPencilNegTwoAboveStatement) :
    CubicSecondRootBoundStatement :=
  cubicSecondRootBound_of_interior
    (cubicInteriorTwoBelow_of_discr_monicPencil_neg hbelow)
    (cubicInteriorTwoAbove_of_discr_monicPencil_neg habove)

/-- Normalized negative-discriminant leaves imply the cubic second-root bound. -/
theorem cubicSecondRootBound_of_normalized
    (hbelow : ∀ b c p r : ℝ, 1 ≤ b → b ≤ c → p ≤ 0 → 1 ≤ r →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C (1 : ℝ)) * (X - C b) * (X - C c)
          + C s * ((X - C p) * (X - C (0 : ℝ)) * (X - C r))) < 0)
    (habove : ∀ a c p q : ℝ, a ≤ 0 → 1 ≤ c → p ≤ q → q ≤ 0 →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C a) * (X - C (1 : ℝ)) * (X - C c)
          + C s * ((X - C p) * (X - C q) * (X - C (0 : ℝ)))) < 0) :
    CubicSecondRootBoundStatement :=
  cubicSecondRootBound_of_discr_monicPencil_neg
    (cubicDiscrMonicPencilNegTwoBelow_of_normalized hbelow)
    (cubicDiscrMonicPencilNegTwoAbove_of_normalized habove)

/-- Non-splitting formulation implies the `2`-below interior obstruction. -/
theorem cubicInteriorTwoBelow_of_notSplits
    (h : CubicMonicPencilNotSplitsTwoBelowStatement) :
    CubicInteriorTwoBelowStatement :=
  cubicInteriorTwoBelow_of_discr_monicPencil_neg
    (cubicDiscrMonicPencilNegTwoBelow_iff_notSplits.mpr h)

/-- Non-splitting formulation implies the `2`-above interior obstruction. -/
theorem cubicInteriorTwoAbove_of_notSplits
    (h : CubicMonicPencilNotSplitsTwoAboveStatement) :
    CubicInteriorTwoAboveStatement :=
  cubicInteriorTwoAbove_of_discr_monicPencil_neg
    (cubicDiscrMonicPencilNegTwoAbove_iff_notSplits.mpr h)

/-- Checked reduction of the cubic same-degree root-count target to the
partial-separation leaf.

Given the `CubicSecondRootBoundStatement` leaf, two split cubics with positive
leading coefficients forming a positive-combination real-rooted pair have
threshold root-count functions differing by at most one at every threshold.
This strengthens `sameDegree_cubic_rootCount_le_two` from `≤ 2` to `≤ 1`,
modulo the single analytic leaf `hbound`, and matches the degree-three case of
the milestone-B1 root-count target
`PosComboNoCommonSameDegreeRootCountNonnegStatement`. -/
theorem sameDegree_cubic_rootCount_le_one_of_secondRootBound
    (hbound : CubicSecondRootBoundStatement)
    {f g : ℝ[X]}
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 3)
    (hf : f.Splits) (hg : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hpc : PosComboRealRooted f g) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 1 := by
  intro x
  obtain ⟨a, b, c, hab, hbc, hfroots, _⟩ :=
    exists_roots_triple_of_splits_natDegree_three hf hfdeg
  obtain ⟨p, q, r, hpq, hqr, hgroots, _⟩ :=
    exists_roots_triple_of_splits_natDegree_three hg hgdeg
  obtain ⟨haq, hbr⟩ :=
    hbound hf_pos hg_pos hf hg hfdeg hgdeg hpc a b c p q r
      hab hbc hpq hqr hfroots hgroots
  obtain ⟨hpb, hqc⟩ :=
    hbound hg_pos hf_pos hg hf hgdeg hfdeg hpc.comm p q r a b c
      hpq hqr hab hbc hgroots hfroots
  rw [hfroots, hgroots, card_filter_le_triple, card_filter_le_triple]
  grind

/-- End-to-end reduction of the cubic root-count bound to the interior leaves. -/
theorem sameDegree_cubic_rootCount_le_one_of_interior
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    {f g : ℝ[X]}
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 3)
    (hf : f.Splits) (hg : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hpc : PosComboRealRooted f g) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 1 :=
  sameDegree_cubic_rootCount_le_one_of_secondRootBound
    (cubicSecondRootBound_of_interior hbelow habove)
    hfdeg hgdeg hf hg hf_pos hg_pos hpc

/-- End-to-end reduction of the cubic root-count bound to the
negative-discriminant monic-pencil leaves. -/
theorem sameDegree_cubic_rootCount_le_one_of_discr_monicPencil_neg
    (hbelow : CubicDiscrMonicPencilNegTwoBelowStatement)
    (habove : CubicDiscrMonicPencilNegTwoAboveStatement)
    {f g : ℝ[X]}
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 3)
    (hf : f.Splits) (hg : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hpc : PosComboRealRooted f g) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 1 :=
  sameDegree_cubic_rootCount_le_one_of_secondRootBound
    (cubicSecondRootBound_of_discr_monicPencil_neg hbelow habove)
    hfdeg hgdeg hf hg hf_pos hg_pos hpc

/-- End-to-end reduction of the cubic root-count bound to the normalized
negative-discriminant monic-pencil leaves. -/
theorem sameDegree_cubic_rootCount_le_one_of_normalized
    (hbelow : ∀ b c p r : ℝ, 1 ≤ b → b ≤ c → p ≤ 0 → 1 ≤ r →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C (1 : ℝ)) * (X - C b) * (X - C c)
          + C s * ((X - C p) * (X - C (0 : ℝ)) * (X - C r))) < 0)
    (habove : ∀ a c p q : ℝ, a ≤ 0 → 1 ≤ c → p ≤ q → q ≤ 0 →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C a) * (X - C (1 : ℝ)) * (X - C c)
          + C s * ((X - C p) * (X - C q) * (X - C (0 : ℝ)))) < 0)
    {f g : ℝ[X]}
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 3)
    (hf : f.Splits) (hg : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hpc : PosComboRealRooted f g) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 1 :=
  sameDegree_cubic_rootCount_le_one_of_discr_monicPencil_neg
    (cubicDiscrMonicPencilNegTwoBelow_of_normalized hbelow)
    (cubicDiscrMonicPencilNegTwoAbove_of_normalized habove)
    hfdeg hgdeg hf hg hf_pos hg_pos hpc

/-- Same-degree positive-combination cubic root-count wrapper from the
normalized negative-discriminant leaves. -/
theorem sameDegree_cubic_rootCount_le_one_of_normalized_posCombo
    (hbelow : ∀ b c p r : ℝ, 1 ≤ b → b ≤ c → p ≤ 0 → 1 ≤ r →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C (1 : ℝ)) * (X - C b) * (X - C c)
          + C s * ((X - C p) * (X - C (0 : ℝ)) * (X - C r))) < 0)
    (habove : ∀ a c p q : ℝ, a ≤ 0 → 1 ≤ c → p ≤ q → q ≤ 0 →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C a) * (X - C (1 : ℝ)) * (X - C c)
          + C s * ((X - C p) * (X - C q) * (X - C (0 : ℝ)))) < 0)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hpc : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hfdeg : f.natDegree = 3) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 1 := by
  have hf : f.Splits := hpc.left_splits_of_sameDegree hf_pos hg_pos hdeg
  have hg : g.Splits := hpc.right_splits_of_sameDegree hf_pos hg_pos hdeg
  have hgdeg : g.natDegree = 3 := by simp_all
  exact sameDegree_cubic_rootCount_le_one_of_normalized
    hbelow habove hfdeg hgdeg hf hg hf_pos hg_pos hpc

/-- Bundled-degree all-threshold version of
`sameDegree_cubic_rootCount_le_one_of_normalized_posCombo`. -/
theorem sameDegree_cubic_rootCount_le_one_of_normalized_posCombo_forall
    (hbelow : ∀ b c p r : ℝ, 1 ≤ b → b ≤ c → p ≤ 0 → 1 ≤ r →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C (1 : ℝ)) * (X - C b) * (X - C c)
          + C s * ((X - C p) * (X - C (0 : ℝ)) * (X - C r))) < 0)
    (habove : ∀ a c p q : ℝ, a ≤ 0 → 1 ≤ c → p ≤ q → q ≤ 0 →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C a) * (X - C (1 : ℝ)) * (X - C c)
          + C s * ((X - C p) * (X - C q) * (X - C (0 : ℝ)))) < 0)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hpc : PosComboRealRooted f g)
    (hdeg : f.natDegree = 3 ∧ g.natDegree = 3) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 1 := by
  have hsame : g.natDegree = f.natDegree := by simp_all
  exact sameDegree_cubic_rootCount_le_one_of_normalized_posCombo
    hbelow habove hf_pos hg_pos hpc hsame hdeg.1

/-- Same-degree positive-combination cubic root-count wrapper from the
negative-discriminant monic-pencil leaves. -/
theorem sameDegree_cubic_rootCount_le_one_of_discr_monicPencil_neg_posCombo
    (hbelow : CubicDiscrMonicPencilNegTwoBelowStatement)
    (habove : CubicDiscrMonicPencilNegTwoAboveStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hpc : PosComboRealRooted f g)
    (hdeg : f.natDegree = 3 ∧ g.natDegree = 3) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 1 := by
  have hsame : g.natDegree = f.natDegree := by simp_all
  have hf : f.Splits := hpc.left_splits_of_sameDegree hf_pos hg_pos hsame
  have hg : g.Splits := hpc.right_splits_of_sameDegree hf_pos hg_pos hsame
  exact
    sameDegree_cubic_rootCount_le_one_of_discr_monicPencil_neg
      hbelow habove hdeg.1 hdeg.2 hf hg hf_pos hg_pos hpc x

/-- Bundled-degree all-threshold version of
`sameDegree_cubic_rootCount_le_one_of_discr_monicPencil_neg_posCombo`. -/
theorem sameDegree_cubic_rootCount_le_one_of_discr_monicPencil_neg_posCombo_forall
    (hbelow : CubicDiscrMonicPencilNegTwoBelowStatement)
    (habove : CubicDiscrMonicPencilNegTwoAboveStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hpc : PosComboRealRooted f g)
    (hdeg : f.natDegree = 3 ∧ g.natDegree = 3) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 1 :=
  fun x =>
    sameDegree_cubic_rootCount_le_one_of_discr_monicPencil_neg_posCombo
      hbelow habove hf_pos hg_pos hpc hdeg x

/-- End-to-end reduction of the cubic root-count bound to the non-splitting
monic-pencil leaves. -/
theorem sameDegree_cubic_rootCount_le_one_of_notSplits
    (hbelow : CubicMonicPencilNotSplitsTwoBelowStatement)
    (habove : CubicMonicPencilNotSplitsTwoAboveStatement)
    {f g : ℝ[X]}
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 3)
    (hf : f.Splits) (hg : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hpc : PosComboRealRooted f g) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 1 :=
  sameDegree_cubic_rootCount_le_one_of_interior
    (cubicInteriorTwoBelow_of_notSplits hbelow)
    (cubicInteriorTwoAbove_of_notSplits habove)
    hfdeg hgdeg hf hg hf_pos hg_pos hpc

/-- End-to-end positive-combination cubic root-count wrapper from the
negative-discriminant monic-pencil leaves through the non-splitting bridge. -/
theorem sameDegree_cubic_rootCount_le_one_of_discr_monicPencil_neg_via_notSplits
    (hbelow : CubicDiscrMonicPencilNegTwoBelowStatement)
    (habove : CubicDiscrMonicPencilNegTwoAboveStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hpc : PosComboRealRooted f g)
    (hdeg : f.natDegree = 3 ∧ g.natDegree = 3) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 1 := by
  have hsame : g.natDegree = f.natDegree := by simp_all
  have hf : f.Splits := hpc.left_splits_of_sameDegree hf_pos hg_pos hsame
  have hg : g.Splits := hpc.right_splits_of_sameDegree hf_pos hg_pos hsame
  exact
    sameDegree_cubic_rootCount_le_one_of_notSplits
      (cubicDiscrMonicPencilNegTwoBelow_iff_notSplits.mp hbelow)
      (cubicDiscrMonicPencilNegTwoAbove_iff_notSplits.mp habove)
      hdeg.1 hdeg.2 hf hg hf_pos hg_pos hpc

/-- Same-degree positive-combination cubic root-count wrapper from the
non-splitting monic-pencil leaves. -/
theorem sameDegree_cubic_rootCount_le_one_of_notSplits_posCombo
    (hbelow : CubicMonicPencilNotSplitsTwoBelowStatement)
    (habove : CubicMonicPencilNotSplitsTwoAboveStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hpc : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hfdeg : f.natDegree = 3) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 1 := by
  have hf : f.Splits := hpc.left_splits_of_sameDegree hf_pos hg_pos hdeg
  have hg : g.Splits := hpc.right_splits_of_sameDegree hf_pos hg_pos hdeg
  have hgdeg : g.natDegree = 3 := by simp_all
  exact sameDegree_cubic_rootCount_le_one_of_notSplits
    hbelow habove hfdeg hgdeg hf hg hf_pos hg_pos hpc

/-- Bundled-degree all-threshold version of
`sameDegree_cubic_rootCount_le_one_of_notSplits_posCombo`. -/
theorem sameDegree_cubic_rootCount_le_one_of_notSplits_posCombo_forall
    (hbelow : CubicMonicPencilNotSplitsTwoBelowStatement)
    (habove : CubicMonicPencilNotSplitsTwoAboveStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hpc : PosComboRealRooted f g)
    (hdeg : f.natDegree = 3 ∧ g.natDegree = 3) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 1 := by
  have hsame : g.natDegree = f.natDegree := by simp_all
  exact sameDegree_cubic_rootCount_le_one_of_notSplits_posCombo
    hbelow habove hf_pos hg_pos hpc hsame hdeg.1

end RealRooted
