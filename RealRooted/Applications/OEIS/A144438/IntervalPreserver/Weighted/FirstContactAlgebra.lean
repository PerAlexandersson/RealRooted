import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.DiagonalInduction

/-!
# Algebra at an unequal-parameter first contact

This file isolates the two scalar facts used after a companion residue first
vanishes.  The first identifies its parameter derivative.  The second shows
that the one-sided minimum conditions on a box force every input-root
parameter to coincide.
-/

noncomputable section

namespace RealRooted.Applications.OEIS

/-- At a vanishing companion residue, the quotient-rule numerator factors
through the positive old-polynomial residue. -/
theorem weightedDeco_contact_residue_derivative
    {a r P H d hderivative : ℝ} (hr : r ≠ 0) (hd : d ≠ 0)
    (hinsertion : (1 + r + a) * P + r * H = 0) :
    (H * d - hderivative * P) / d ^ 2 =
      (P / d) * (-(1 + r + a) / r - hderivative / d) := by
  field_simp [hr, hd]
  linear_combination d * hinsertion

/-- The affine factor in the contact derivative is strictly increasing in
the input-root parameter when the output root is negative. -/
theorem weightedDeco_contact_factor_strictMono {r μ : ℝ} (hr : r < 0) :
    StrictMono (fun a : ℝ ↦ -(1 + r + a) / r - μ) := by
  intro a b hab
  have hrne : r ≠ 0 := hr.ne
  have hslope : 0 < -(1 / r) :=
    neg_pos.mpr (div_neg_of_pos_of_neg zero_lt_one hr)
  have hdiff :
      (-(1 + r + b) / r - μ) - (-(1 + r + a) / r - μ) =
        -(1 / r) * (b - a) := by
    field_simp [hrne]
    ring
  nlinarith [mul_pos hslope (sub_pos.mpr hab)]

/-- If the contact derivative satisfies the one-sided minimum conditions in
a parameter box, then all coordinates coincide. -/
theorem weightedDeco_box_first_contact_coordinates_eq
    {I : Type*} (a α g : I → ℝ) (m M r μ : ℝ)
    (hr : r < 0) (hα : ∀ i, 0 < α i)
    (hg : ∀ i, g i = α i * (-(1 + r + a i) / r - μ))
    (hlower : ∀ i, m ≤ a i) (hupper : ∀ i, a i ≤ M)
    (hatLower : ∀ i, a i = m → 0 ≤ g i)
    (hatUpper : ∀ i, a i = M → g i ≤ 0)
    (hinterior : ∀ i, m < a i → a i < M → g i = 0) :
    ∀ i j, a i = a j := by
  intro i j
  apply le_antisymm
  · by_contra hnot
    have hji : a j < a i := lt_of_not_ge hnot
    have hgjNonneg : 0 ≤ g j := by
      rcases (hlower j).eq_or_lt with hjLower | hjLower
      · exact hatLower j hjLower.symm
      · have hjUpper : a j < M := hji.trans_le (hupper i)
        rw [hinterior j hjLower hjUpper]
    have hgiNonpos : g i ≤ 0 := by
      rcases (hupper i).eq_or_lt with hiUpper | hiUpper
      · exact hatUpper i hiUpper
      · have hiLower : m < a i := (hlower j).trans_lt hji
        rw [hinterior i hiLower hiUpper]
    have hfactorJ : 0 ≤ -(1 + r + a j) / r - μ := by
      rw [hg j] at hgjNonneg
      nlinarith [hα j]
    have hfactorI : -(1 + r + a i) / r - μ ≤ 0 := by
      rw [hg i] at hgiNonpos
      nlinarith [hα i]
    have hstrict := weightedDeco_contact_factor_strictMono (r := r) (μ := μ) hr hji
    linarith
  · by_contra hnot
    have hij : a i < a j := lt_of_not_ge hnot
    have hgiNonneg : 0 ≤ g i := by
      rcases (hlower i).eq_or_lt with hiLower | hiLower
      · exact hatLower i hiLower.symm
      · have hiUpper : a i < M := hij.trans_le (hupper j)
        rw [hinterior i hiLower hiUpper]
    have hgjNonpos : g j ≤ 0 := by
      rcases (hupper j).eq_or_lt with hjUpper | hjUpper
      · exact hatUpper j hjUpper
      · have hjLower : m < a j := (hlower i).trans_lt hij
        rw [hinterior j hjLower hjUpper]
    have hfactorI : 0 ≤ -(1 + r + a i) / r - μ := by
      rw [hg i] at hgiNonneg
      nlinarith [hα i]
    have hfactorJ : -(1 + r + a j) / r - μ ≤ 0 := by
      rw [hg j] at hgjNonpos
      nlinarith [hα j]
    have hstrict := weightedDeco_contact_factor_strictMono (r := r) (μ := μ) hr hij
    linarith

end RealRooted.Applications.OEIS
