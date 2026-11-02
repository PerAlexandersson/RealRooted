module

public import RealRooted.PFPolynomial
public import RealRooted.Basic.Coefficients
public import Mathlib.Algebra.Polynomial.Basic
public import RealRooted.SimpleRoots
public import RealRooted.Interlacing.QuadraticPFPreservers
import RealRooted.Interlacing.SecondOrderClassification
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
import RealRooted.Interlacing.SecondOrderPreservation
import RealRooted.DerivativeRecurrence.Degree
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import RealRooted.PFPolynomial.Closure
import RealRooted.PFPolynomial.PreserverClosure
import RealRooted.RootCounting.SignChanges

/-!
# The indexed criterion for second-order ray operators

Scalar optimization, integer index selection, and the closure step in the
classification of second-order operators preserving PF polynomials.
-/

public section

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-! ## The three indexed thresholds -/

/-- The optimized threshold in the gap with `j` roots to its right. -/
def secondOrderGapThreshold
    (a b d f delta : ℝ) (j : ℕ) : ℝ :=
  if a ^ 2 > (j : ℝ) ^ 2 * delta + 4 * b * f * j then
    a * (d + Real.sqrt (delta + 4 * b * f / j)) / (2 * b)
  else if |(j : ℝ) ^ 2 * delta - a ^ 2| ≤ 4 * b * f * j then
    f + a * d / (2 * b) + j * delta / (4 * b) +
      a ^ 2 / (4 * b * j)
  else
    (a * d + Real.sqrt (delta * (a ^ 2 + 4 * b * f * j))) / (2 * b)

/-- Formula for the indexed threshold in the lower branch. -/
theorem secondOrderGapThreshold_eq_lower
    {a b d f delta : ℝ} {j : ℕ}
    (h : a ^ 2 > (j : ℝ) ^ 2 * delta + 4 * b * f * j) :
    secondOrderGapThreshold a b d f delta j =
      a * (d + Real.sqrt (delta + 4 * b * f / j)) / (2 * b) := by
  simp [secondOrderGapThreshold, h]

/-- Formula for the indexed threshold in the middle branch. -/
theorem secondOrderGapThreshold_eq_middle
    {a b d f delta : ℝ} {j : ℕ}
    (hlower : ¬a ^ 2 > (j : ℝ) ^ 2 * delta + 4 * b * f * j)
    (hmiddle : |(j : ℝ) ^ 2 * delta - a ^ 2| ≤ 4 * b * f * j) :
    secondOrderGapThreshold a b d f delta j =
      f + a * d / (2 * b) + j * delta / (4 * b) +
        a ^ 2 / (4 * b * j) := by
  simp [secondOrderGapThreshold, hlower, hmiddle]

/-- Formula for the indexed threshold in the upper branch. -/
theorem secondOrderGapThreshold_eq_upper
    {a b d f delta : ℝ} {j : ℕ}
    (hlower : ¬a ^ 2 > (j : ℝ) ^ 2 * delta + 4 * b * f * j)
    (hmiddle : ¬|(j : ℝ) ^ 2 * delta - a ^ 2| ≤ 4 * b * f * j) :
    secondOrderGapThreshold a b d f delta j =
      (a * d + Real.sqrt (delta * (a ^ 2 + 4 * b * f * j))) /
        (2 * b) := by
  simp [secondOrderGapThreshold, hlower, hmiddle]

/-- Every indexed threshold is positive in the genuine positive-discriminant
second-order range. -/
theorem secondOrderGapThreshold_pos
    {a b d f delta : ℝ} {j : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hj : 1 ≤ j) :
    0 < secondOrderGapThreshold a b d f delta j := by
  have hjr : (0 : ℝ) < j := by positivity
  by_cases hlower : a ^ 2 > (j : ℝ) ^ 2 * delta + 4 * b * f * j
  · rw [secondOrderGapThreshold_eq_lower hlower]
    have hapos : 0 < a := by
      have : 0 < a ^ 2 := by
        nlinarith [mul_pos hdelta (sq_pos_of_pos hjr), mul_pos hb hf]
      nlinarith [sq_nonneg a]
    positivity
  · by_cases hmiddle :
        |(j : ℝ) ^ 2 * delta - a ^ 2| ≤ 4 * b * f * j
    · rw [secondOrderGapThreshold_eq_middle hlower hmiddle]
      have had : 0 ≤ a * d / (2 * b) := by positivity
      have hjdelta : 0 ≤ (j : ℝ) * delta / (4 * b) := by positivity
      have hasq : 0 ≤ a ^ 2 / (4 * b * j) := by positivity
      linarith
    · rw [secondOrderGapThreshold_eq_upper hlower hmiddle]
      have hL : 0 < a ^ 2 + 4 * b * f * (j : ℝ) := by positivity
      have hsqrt : 0 < Real.sqrt (delta * (a ^ 2 + 4 * b * f * j)) :=
        Real.sqrt_pos.2 (mul_pos hdelta hL)
      positivity

/-! ## Scalar optimization in one root gap -/

/-- The middle scalar regime is minimized at `s = j`. -/
theorem secondOrder_middle_scalar_lower_bound
    {f v H s q j : ℝ}
    (hf : 0 ≤ f) (hv : 0 < v) (hj : 0 < j) (hs : 0 < s)
    (hqj : j ≤ q) (hqs : s ^ 2 ≤ j * q)
    (hHlow : -(f * v ^ 2 / j) ≤ H)
    (hHhigh : H ≤ f * v ^ 2 / j) :
    j * H / v + f * v ≤ H * s / v + f * v / s * q := by
  have hv0 : v ≠ 0 := hv.ne'
  have hj0 : j ≠ 0 := hj.ne'
  have hs0 : s ≠ 0 := hs.ne'
  by_cases hsj : s ≤ j
  · have hmul : H * (s - j) / v ≥
        (f * v ^ 2 / j) * (s - j) / v := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonpos_right hHhigh (sub_nonpos.mpr hsj)) hv.le
    have hqdiv : j / s ≤ q / s := div_le_div_of_nonneg_right hqj hs.le
    have hamgm : 2 ≤ s / j + j / s := by
      have hsq : 0 ≤ (s - j) ^ 2 := sq_nonneg (s - j)
      field_simp
      nlinarith
    field_simp at hmul hqdiv ⊢
    have hmul' := mul_le_mul_of_nonneg_left hmul hs.le
    have hq' := mul_le_mul_of_nonneg_left hqdiv hj.le
    have hfvsq : 0 ≤ f * v ^ 2 := mul_nonneg hf (sq_nonneg v)
    have hq'' := mul_le_mul_of_nonneg_left hq' hfvsq
    have hsq : 0 ≤ (s - j) ^ 2 := sq_nonneg (s - j)
    nlinarith
  · have hjs : j ≤ s := le_of_not_ge hsj
    have hmul : -(f * v ^ 2 / j) * (s - j) / v ≤
        H * (s - j) / v := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hHlow (sub_nonneg.mpr hjs)) hv.le
    have hqdiv : s / j ≤ q / s := by
      apply (div_le_div_iff₀ hj hs).2
      nlinarith
    field_simp at hmul hqdiv ⊢
    have hmul' := mul_le_mul_of_nonneg_left hmul hs.le
    have hfvsq : 0 ≤ f * v ^ 2 := mul_nonneg hf (sq_nonneg v)
    have hq' := mul_le_mul_of_nonneg_left hqdiv hfvsq
    nlinarith

/-- In the lower scalar regime, the square-sum bound cancels the adverse
linear term exactly. -/
theorem secondOrder_lower_scalar_lower_bound
    {f v s q j : ℝ}
    (hf : 0 ≤ f) (hv : 0 < v) (hj : 0 < j) (hs : 0 < s)
    (hqs : s ^ 2 ≤ j * q) :
    0 ≤ -(f * v ^ 2 / j) * s / v + f * v / s * q := by
  have hqdiv : s / j ≤ q / s := by
    apply (div_le_div_iff₀ hj hs).2
    nlinarith
  have hvn : 0 ≤ f * v := mul_nonneg hf hv.le
  have hscaled := mul_le_mul_of_nonneg_left hqdiv hvn
  field_simp at hscaled ⊢
  nlinarith

/-- In the upper scalar regime, AM--GM gives the interior minimum. -/
theorem secondOrder_upper_scalar_lower_bound
    {f v H s q j z : ℝ}
    (hf : 0 < f) (hv : 0 < v) (hH : 0 < H)
    (hj : 0 < j) (hs : 0 < s) (hqj : j ≤ q)
    (_hz : 0 ≤ z) (hzsq : z ^ 2 = f * j * H) :
    2 * z ≤ H * s / v + f * v / s * q := by
  have hqdiv : j / s ≤ q / s := div_le_div_of_nonneg_right hqj hs.le
  have hscale : f * v * (j / s) ≤ f * v * (q / s) :=
    mul_le_mul_of_nonneg_left hqdiv (mul_pos hf hv).le
  have hleft : 0 ≤ H * s / v := div_nonneg (mul_nonneg hH.le hs.le) hv.le
  have hright : 0 ≤ f * v * (j / s) :=
    mul_nonneg (mul_pos hf hv).le (div_nonneg hj.le hs.le)
  have hprod : (H * s / v) * (f * v * (j / s)) = z ^ 2 := by
    rw [hzsq]
    field_simp
  have hsquare : 0 ≤ (H * s / v - f * v * (j / s)) ^ 2 := sq_nonneg _
  have hamgm : 2 * z ≤ H * s / v + f * v * (j / s) := by
    nlinarith
  calc
    2 * z ≤ H * s / v + f * v * (j / s) := hamgm
    _ ≤ H * s / v + f * v / s * q := by
      rw [show f * v / s * q = f * v * (q / s) by ring]
      linarith

/-! ## The minimizing integer -/

/-- The issue's index condition selects the integer minimum of
`j * delta + a^2 / j`. -/
theorem secondOrder_index_minimizes_delta_mul_add_div
    {a delta : ℝ} {m j : ℕ}
    (hdelta : 0 < delta) (hm : 1 ≤ m) (hj : 1 ≤ j)
    (hmlo : delta * (m : ℝ) * ((m : ℝ) - 1) ≤ a ^ 2)
    (hmhi : a ^ 2 ≤ delta * (m : ℝ) * ((m : ℝ) + 1)) :
    delta * (m : ℝ) + a ^ 2 / (m : ℝ) ≤
      delta * (j : ℝ) + a ^ 2 / (j : ℝ) := by
  have hmpos : (0 : ℝ) < m := by positivity
  have hjpos : (0 : ℝ) < j := by positivity
  have hmform : delta * (m : ℝ) + a ^ 2 / (m : ℝ) =
      (delta * (m : ℝ) ^ 2 + a ^ 2) / (m : ℝ) := by
    field_simp
  have hjform : delta * (j : ℝ) + a ^ 2 / (j : ℝ) =
      (delta * (j : ℝ) ^ 2 + a ^ 2) / (j : ℝ) := by
    field_simp
  rw [hmform, hjform]
  by_cases hjm : j ≤ m
  · by_cases heq : j = m
    · subst j
      rfl
    · have hjlt : j ≤ m - 1 := by lia
      have hcast : (j : ℝ) ≤ (m : ℝ) - 1 := by exact_mod_cast hjlt
      have hprod : delta * (j : ℝ) * (m : ℝ) ≤ a ^ 2 := by
        calc
          delta * (j : ℝ) * (m : ℝ) ≤
              delta * ((m : ℝ) - 1) * (m : ℝ) := by
            nlinarith
          _ = delta * (m : ℝ) * ((m : ℝ) - 1) := by ring
          _ ≤ a ^ 2 := hmlo
      apply (div_le_div_iff₀ hmpos hjpos).2
      nlinarith
  · have hmj : m + 1 ≤ j := by lia
    have hcast : (m : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hmj
    have hprod : a ^ 2 ≤ delta * (m : ℝ) * (j : ℝ) := by
      calc
        a ^ 2 ≤ delta * (m : ℝ) * ((m : ℝ) + 1) := hmhi
        _ ≤ delta * (m : ℝ) * (j : ℝ) := by nlinarith
    apply (div_le_div_iff₀ hmpos hjpos).2
    nlinarith

/-! ## Comparing the indexed thresholds -/

/-- A threshold core is either on the linear middle bridge or on one of the
two radical branches, expressed using the larger coordinate of a fixed-product pair. -/
private def SecondOrderThresholdDatum
    (K P u v w : ℝ) : Prop :=
  (|u - v| ≤ K ∧ w = (K + u + v) / 2) ∨
    (K < |u - v| ∧ 0 ≤ w ∧ w ^ 2 = P + K * max u v)

/-- For nonnegative pairs with fixed product, the threshold core is
nondecreasing in the sum of the pair. -/
private theorem secondOrderThresholdDatum_mono
    {K P u₁ v₁ w₁ u₂ v₂ w₂ : ℝ}
    (hK : 0 < K) (hu₁ : 0 ≤ u₁) (hv₁ : 0 ≤ v₁)
    (hu₂ : 0 ≤ u₂) (hv₂ : 0 ≤ v₂)
    (hp₁ : u₁ * v₁ = P) (hp₂ : u₂ * v₂ = P)
    (hsum : u₁ + v₁ ≤ u₂ + v₂)
    (h₁ : SecondOrderThresholdDatum K P u₁ v₁ w₁)
    (h₂ : SecondOrderThresholdDatum K P u₂ v₂ w₂) :
    w₁ ≤ w₂ := by
  have hdiffsq : (u₁ - v₁) ^ 2 ≤ (u₂ - v₂) ^ 2 := by
    nlinarith [sq_nonneg (u₁ + v₁), sq_nonneg (u₂ + v₂)]
  have habs : |u₁ - v₁| ≤ |u₂ - v₂| := by
    nlinarith [sq_abs (u₁ - v₁), sq_abs (u₂ - v₂),
      abs_nonneg (u₁ - v₁), abs_nonneg (u₂ - v₂)]
  have hsumprod₁ : (u₁ + v₁) ^ 2 = (u₁ - v₁) ^ 2 + 4 * P := by
    nlinarith
  have hsumprod₂ : (u₂ + v₂) ^ 2 = (u₂ - v₂) ^ 2 + 4 * P := by
    nlinarith
  have hmax₁ : 2 * max u₁ v₁ = u₁ + v₁ + |u₁ - v₁| := by
    rcases le_total u₁ v₁ with huv | hvu
    · rw [max_eq_right huv, abs_of_nonpos (sub_nonpos.mpr huv)]
      ring
    · rw [max_eq_left hvu, abs_of_nonneg (sub_nonneg.mpr hvu)]
      ring
  have hmax₂ : 2 * max u₂ v₂ = u₂ + v₂ + |u₂ - v₂| := by
    rcases le_total u₂ v₂ with huv | hvu
    · rw [max_eq_right huv, abs_of_nonpos (sub_nonpos.mpr huv)]
      ring
    · rw [max_eq_left hvu, abs_of_nonneg (sub_nonneg.mpr hvu)]
      ring
  have hmax : max u₁ v₁ ≤ max u₂ v₂ := by nlinarith
  rcases h₁ with hmiddle₁ | houtside₁ <;>
    rcases h₂ with hmiddle₂ | houtside₂
  · nlinarith
  · rcases hmiddle₁ with ⟨hdiff₁, rfl⟩
    rcases houtside₂ with ⟨hdiff₂, hw₂, hsq₂⟩
    have hsumdiff₁ : (u₁ + v₁) ^ 2 ≤ K ^ 2 + 4 * P := by
      have := (sq_le_sq₀ (abs_nonneg (u₁ - v₁)) hK.le).2 hdiff₁
      nlinarith [sq_abs (u₁ - v₁)]
    have hmaxlarge : K + u₁ + v₁ ≤ 2 * max u₂ v₂ := by
      nlinarith [abs_nonneg (u₂ - v₂)]
    nlinarith [sq_nonneg (K + u₁ + v₁)]
  · rcases houtside₁ with ⟨_, hw₁, hsq₁⟩
    rcases hmiddle₂ with ⟨_, rfl⟩
    have hsquare : 4 * w₁ ^ 2 ≤ (K + u₁ + v₁) ^ 2 := by
      nlinarith [sq_nonneg (|u₁ - v₁| - K), sq_abs (u₁ - v₁)]
    nlinarith
  · rcases houtside₁ with ⟨_, hw₁, hsq₁⟩
    rcases houtside₂ with ⟨_, hw₂, hsq₂⟩
    nlinarith

/-- Each indexed threshold has the fixed-product core used by the monotonicity
argument. -/
private theorem secondOrderGapThreshold_datum
    {a b d f delta : ℝ} {j : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hf : 0 < f) (hdelta : 0 < delta)
    (hj : 1 ≤ j) :
    SecondOrderThresholdDatum (4 * b * f) (delta * a ^ 2)
      (delta * j) (a ^ 2 / j)
      (2 * b * secondOrderGapThreshold a b d f delta j - a * d) := by
  have hjr : (0 : ℝ) < j := by positivity
  have habsid : |delta * j - a ^ 2 / j| * j =
      |(j : ℝ) ^ 2 * delta - a ^ 2| := by
    calc
      |delta * j - a ^ 2 / j| * j =
          |delta * j - a ^ 2 / j| * |(j : ℝ)| := by rw [abs_of_pos hjr]
      _ = |(delta * j - a ^ 2 / j) * j| := by rw [abs_mul]
      _ = |(j : ℝ) ^ 2 * delta - a ^ 2| := by
        congr 1
        field_simp
  by_cases hlower : a ^ 2 > (j : ℝ) ^ 2 * delta + 4 * b * f * j
  · right
    have hdiff : 4 * b * f < |delta * j - a ^ 2 / j| := by
      have horig : 4 * b * f * j < |(j : ℝ) ^ 2 * delta - a ^ 2| := by
        rw [abs_of_neg (by nlinarith [mul_pos hb hf])]
        nlinarith
      nlinarith
    refine ⟨hdiff, ?_, ?_⟩
    · rw [secondOrderGapThreshold_eq_lower hlower]
      have hapos : 0 < a := by nlinarith [sq_nonneg a, mul_pos hb hf]
      rw [show 2 * b * (a * (d + Real.sqrt
        (delta + 4 * b * f / j)) / (2 * b)) - a * d =
          a * Real.sqrt (delta + 4 * b * f / j) by field_simp; ring]
      positivity
    · rw [secondOrderGapThreshold_eq_lower hlower]
      have hrad : 0 ≤ delta + 4 * b * f / (j : ℝ) := by positivity
      have hmax : max (delta * j) (a ^ 2 / j) = a ^ 2 / j := by
        apply max_eq_right
        apply (le_div_iff₀ hjr).2
        nlinarith [mul_pos hb hf]
      rw [hmax]
      rw [show 2 * b * (a * (d + Real.sqrt
        (delta + 4 * b * f / j)) / (2 * b)) - a * d =
          a * Real.sqrt (delta + 4 * b * f / j) by field_simp; ring]
      rw [mul_pow, Real.sq_sqrt hrad]
      field_simp
  · by_cases hmiddle :
        |(j : ℝ) ^ 2 * delta - a ^ 2| ≤ 4 * b * f * j
    · left
      refine ⟨?_, ?_⟩
      · nlinarith
      · rw [secondOrderGapThreshold_eq_middle hlower hmiddle]
        field_simp
        ring
    · right
      have hdiff : 4 * b * f < |delta * j - a ^ 2 / j| := by
        have horig : 4 * b * f * j <
            |(j : ℝ) ^ 2 * delta - a ^ 2| := lt_of_not_ge hmiddle
        nlinarith
      have hdir : a ^ 2 / j < delta * j := by
        have hle := le_of_not_gt hlower
        have horig : 4 * b * f * j <
            |(j : ℝ) ^ 2 * delta - a ^ 2| := lt_of_not_ge hmiddle
        have hsigned : a ^ 2 < (j : ℝ) ^ 2 * delta := by
          by_contra h
          rw [abs_of_nonpos (by linarith)] at horig
          nlinarith
        apply (div_lt_iff₀ hjr).2
        nlinarith
      refine ⟨hdiff, ?_, ?_⟩
      · rw [secondOrderGapThreshold_eq_upper hlower hmiddle]
        rw [show 2 * b * ((a * d + Real.sqrt
          (delta * (a ^ 2 + 4 * b * f * j))) / (2 * b)) - a * d =
            Real.sqrt (delta * (a ^ 2 + 4 * b * f * j)) by field_simp; ring]
        exact Real.sqrt_nonneg _
      · rw [secondOrderGapThreshold_eq_upper hlower hmiddle]
        have hrad : 0 ≤ delta * (a ^ 2 + 4 * b * f * j) := by positivity
        rw [max_eq_left hdir.le]
        rw [show 2 * b * ((a * d + Real.sqrt
          (delta * (a ^ 2 + 4 * b * f * j))) / (2 * b)) - a * d =
            Real.sqrt (delta * (a ^ 2 + 4 * b * f * j)) by field_simp; ring]
        rw [Real.sq_sqrt hrad]
        ring

/-- The issue's index inequalities make the threshold at `m` no larger than
the threshold at any positive integer `j`. -/
theorem secondOrderGapThreshold_minimized_at_index
    {a b d f delta : ℝ} {m j : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hf : 0 < f) (hdelta : 0 < delta)
    (hm : 1 ≤ m) (hj : 1 ≤ j)
    (hmlo : delta * (m : ℝ) * ((m : ℝ) - 1) ≤ a ^ 2)
    (hmhi : a ^ 2 ≤ delta * (m : ℝ) * ((m : ℝ) + 1)) :
    secondOrderGapThreshold a b d f delta m ≤
      secondOrderGapThreshold a b d f delta j := by
  have hsum := secondOrder_index_minimizes_delta_mul_add_div
    hdelta hm hj hmlo hmhi
  have hmdata := secondOrderGapThreshold_datum (d := d) ha hb hf hdelta hm
  have hjdata := secondOrderGapThreshold_datum (d := d) ha hb hf hdelta hj
  have hcore := secondOrderThresholdDatum_mono
    (show 0 < 4 * b * f by positivity)
    (show 0 ≤ delta * (m : ℝ) by positivity)
    (show 0 ≤ a ^ 2 / (m : ℝ) by positivity)
    (show 0 ≤ delta * (j : ℝ) by positivity)
    (show 0 ≤ a ^ 2 / (j : ℝ) by positivity)
    (P := delta * a ^ 2) (by field_simp) (by field_simp) hsum hmdata hjdata
  nlinarith

/-! ## Closed-form scalar certificates -/

/-- The lower-branch radical gives a positive gap parameter, makes the
linear coefficient equal to the lower scalar boundary, and yields the first
displayed threshold formula. -/
theorem secondOrder_lower_formula_certificate
    {a b d f delta j : ℝ}
    (hb : 0 < b) (hd : 0 ≤ d) (hf : 0 < f) (hdelta : 0 ≤ delta)
    (hj : 0 < j) (hdisc : delta = d ^ 2 - 4 * b * f) :
    let k := Real.sqrt (delta + 4 * b * f / j)
    let v := 2 * b / (d + k)
    0 < v ∧
      d * v - b - f * v ^ 2 = -(f * v ^ 2 / j) ∧
      a / v = a * (d + k) / (2 * b) := by
  dsimp only
  let k := Real.sqrt (delta + 4 * b * f / j)
  change 0 < 2 * b / (d + k) ∧
    d * (2 * b / (d + k)) - b - f * (2 * b / (d + k)) ^ 2 =
      -(f * (2 * b / (d + k)) ^ 2 / j) ∧
    a / (2 * b / (d + k)) = a * (d + k) / (2 * b)
  have hrad : 0 < delta + 4 * b * f / j := by positivity
  have hkpos : 0 < k := Real.sqrt_pos.2 hrad
  have hden : 0 < d + k := by positivity
  have hv : 0 < 2 * b / (d + k) := by positivity
  have hksq : k ^ 2 = delta + 4 * b * f / j := Real.sq_sqrt hrad.le
  have hksq' : j * k ^ 2 = j * delta + 4 * b * f := by
    rw [hksq]
    field_simp
  refine ⟨hv, ?_, ?_⟩
  · field_simp
    nlinarith [hksq']
  · field_simp

/-- At the middle-branch gap parameter, the value at `s = j` is the
second displayed threshold formula. -/
theorem secondOrder_middle_formula_certificate
    {a b d f delta j : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hd : 0 < d) (hj : 0 < j)
    (hdisc : delta = d ^ 2 - 4 * b * f) :
    let v := 2 * b * j / (a + d * j)
    0 < v ∧
      (a + j * (d * v - b - f * v ^ 2) / v + f * v) / v =
        f + a * d / (2 * b) + j * delta / (4 * b) +
          a ^ 2 / (4 * b * j) := by
  dsimp only
  have hden : 0 < a + d * j := by positivity
  have hv : 0 < 2 * b * j / (a + d * j) := by positivity
  refine ⟨hv, ?_⟩
  field_simp
  nlinarith

/-- The polynomial middle-branch comparison is exactly strong enough to
place its gap parameter in the middle scalar regime. -/
theorem secondOrder_middle_formula_regime
    {a b d f delta j : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hd : 0 < d) (_hf : 0 ≤ f) (hj : 0 < j)
    (hdisc : delta = d ^ 2 - 4 * b * f)
    (hbranch : |j ^ 2 * delta - a ^ 2| ≤ 4 * b * f * j) :
    let v := 2 * b * j / (a + d * j)
    (-(f * v ^ 2 / j) ≤ d * v - b - f * v ^ 2 ∧
      d * v - b - f * v ^ 2 ≤ f * v ^ 2 / j) := by
  dsimp only
  have hden : 0 < a + d * j := by positivity
  obtain ⟨hbranchlo, hbranchhi⟩ := abs_le.mp hbranch
  constructor <;> field_simp <;> nlinarith

/-- The upper-branch radical realizes the AM--GM interior minimum and the
third displayed threshold formula. -/
theorem secondOrder_upper_formula_certificate
    {a b d f delta j : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hj : 0 < j)
    (hdisc : delta = d ^ 2 - 4 * b * f) :
    let L := a ^ 2 + 4 * b * f * j
    let k := Real.sqrt (delta * L)
    let v := 2 * b * L / (d * L + a * k)
    let z := 2 * b * f * j * k / (d * L + a * k)
    0 < v ∧ 0 < z ∧ 0 < d * v - b - f * v ^ 2 ∧
      z ^ 2 = f * j * (d * v - b - f * v ^ 2) ∧
      (a + 2 * z) / v =
        (a * d + Real.sqrt (delta * (a ^ 2 + 4 * b * f * j))) /
          (2 * b) := by
  dsimp only
  let L := a ^ 2 + 4 * b * f * j
  have hL : 0 < L := by dsimp [L]; positivity
  have hrad : 0 < delta * L := mul_pos hdelta hL
  have hk : 0 < Real.sqrt (delta * L) := Real.sqrt_pos.2 hrad
  have hdpos : 0 < d := by
    have : 0 < d ^ 2 := by
      nlinarith [mul_pos hb hf]
    nlinarith [sq_nonneg d]
  have hden : 0 < d * L + a * Real.sqrt (delta * L) := by positivity
  have hv : 0 < 2 * b * L / (d * L + a * Real.sqrt (delta * L)) := by
    positivity
  have hz : 0 < 2 * b * f * j * Real.sqrt (delta * L) /
      (d * L + a * Real.sqrt (delta * L)) := by positivity
  have hksq : Real.sqrt (delta * L) ^ 2 = delta * L :=
    Real.sq_sqrt hrad.le
  have hzsq :
      (2 * b * f * j * Real.sqrt (delta * L) /
          (d * L + a * Real.sqrt (delta * L))) ^ 2 =
        f * j *
          (d * (2 * b * L / (d * L + a * Real.sqrt (delta * L))) - b -
            f * (2 * b * L / (d * L + a * Real.sqrt (delta * L))) ^ 2) := by
    field_simp
    dsimp [L] at hksq ⊢
    nlinarith [hksq]
  have hH : 0 <
      d * (2 * b * L / (d * L + a * Real.sqrt (delta * L))) - b -
        f * (2 * b * L / (d * L + a * Real.sqrt (delta * L))) ^ 2 := by
    nlinarith [sq_pos_of_pos hz, mul_pos hf hj]
  refine ⟨hv, hz, hH, hzsq, ?_⟩
  field_simp
  ring

/-! ## Direct gap bounds and preservation -/

/-- Splitting a list by a predicate preserves a mapped sum. -/
private theorem sum_filter_map_add_sum_filter_not
    (l : List ℝ) (g : ℝ → ℝ) (P : ℝ → Prop) [DecidablePred P] :
    ((l.filter P).map g).sum +
        ((l.filter fun x ↦ !decide (P x)).map g).sum =
      (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : P x
      · rw [List.filter_cons_of_pos (by simp [hx]),
          List.filter_cons_of_neg (by simp [hx])]
        simp only [List.map_cons, List.sum_cons]
        linarith
      · rw [List.filter_cons_of_neg (by simp [hx]),
          List.filter_cons_of_pos (by simp [hx])]
        simp only [List.map_cons, List.sum_cons]
        linarith

/-- The Round-4 gap estimate, rewritten using the multiset sums occurring
in the exact operator quotient. -/
private theorem secondOrder_gap_squareSum_bound_multiset
    {p : ℝ[X]} {x v : ℝ} {j : ℕ}
    (hp : p.Splits) (hp_neg : ∀ r ∈ p.roots, r < 0)
    (hx : x < 0) (hxroot : ¬p.IsRoot x) (hv : 0 < v)
    (hratio : p.derivative.eval x / p.eval x = -v)
    (hcount : p.roots.countP (fun r ↦ x < r) = j) :
    let terms := p.roots.map fun r ↦ x / (x - r)
    let s := terms.sum
    let q := (terms.map fun y ↦ y ^ 2).sum
    s = -v * x ∧ (j : ℝ) ≤ q ∧ s ^ 2 ≤ (j : ℝ) * q := by
  dsimp only
  have h := secondOrder_gap_squareSum_bound hp hp_neg hx hxroot hv hratio hcount
  dsimp only at h
  let roots := p.roots.sort (· ≤ ·)
  have hroots : (↑roots : Multiset ℝ) = p.roots := Multiset.sort_eq ..
  have hsum :
      (((roots.filter fun r ↦ x < r).map fun r ↦ x / (x - r)).sum +
        ((roots.filter fun r ↦ ¬x < r).map fun r ↦ x / (x - r)).sum) =
        (p.roots.map fun r ↦ x / (x - r)).sum := by
    change (((roots.filter fun r ↦ x < r).map fun r ↦ x / (x - r)).sum +
      ((roots.filter fun r ↦ !decide (x < r)).map fun r ↦ x / (x - r)).sum) = _
    rw [sum_filter_map_add_sum_filter_not]
    have := congrArg
      (fun s : Multiset ℝ ↦ (s.map fun r ↦ x / (x - r)).sum) hroots
    simpa using this
  have hsquare :
      ((((roots.filter fun r ↦ x < r).map fun r ↦ x / (x - r)).map
          fun y ↦ y ^ 2).sum +
        (((roots.filter fun r ↦ ¬x < r).map fun r ↦ x / (x - r)).map
          fun y ↦ y ^ 2).sum) =
        ((p.roots.map fun r ↦ x / (x - r)).map fun y ↦ y ^ 2).sum := by
    simp only [List.map_map]
    change (((roots.filter fun r ↦ x < r).map
        fun r ↦ (x / (x - r)) ^ 2).sum +
      ((roots.filter fun r ↦ !decide (x < r)).map
        fun r ↦ (x / (x - r)) ^ 2).sum) = _
    rw [sum_filter_map_add_sum_filter_not]
    rw [Multiset.map_map]
    have := congrArg
      (fun s : Multiset ℝ ↦
        (s.map fun r ↦ (x / (x - r)) ^ 2).sum) hroots
    simpa using this
  rw [← hsum, ← hsquare]
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

/-- The three ways in which a gap parameter can certify positivity. -/
private def SecondOrderGapCertificate
    (a b c d f j v : ℝ) : Prop :=
  0 < v ∧
    let H := d * v - b - f * v ^ 2
    (H = -(f * v ^ 2 / j) ∧ c * v < a) ∨
    (-(f * v ^ 2 / j) ≤ H ∧ H ≤ f * v ^ 2 / j ∧
      c * v < a + j * H / v + f * v) ∨
    ∃ z, 0 ≤ z ∧ 0 < H ∧ z ^ 2 = f * j * H ∧
      c * v < a + 2 * z

/-- Every strict indexed threshold supplies one of the three scalar gap
certificates. -/
private theorem exists_secondOrderGapCertificate_of_lt_threshold
    {a b c d f delta : ℝ} {j : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hj : 1 ≤ j)
    (hdisc : delta = d ^ 2 - 4 * b * f)
    (hc : c < secondOrderGapThreshold a b d f delta j) :
    ∃ v, SecondOrderGapCertificate a b c d f j v := by
  have hjr : (0 : ℝ) < j := by positivity
  by_cases hlower : a ^ 2 > (j : ℝ) ^ 2 * delta + 4 * b * f * j
  · obtain ⟨hv, hH, hvalue⟩ :=
      secondOrder_lower_formula_certificate (a := a) hb hd hf hdelta.le hjr hdisc
    refine ⟨2 * b / (d + Real.sqrt (delta + 4 * b * f / j)), hv, ?_⟩
    left
    refine ⟨hH, ?_⟩
    have hc' := hc
    rw [secondOrderGapThreshold_eq_lower hlower, ← hvalue] at hc'
    exact (lt_div_iff₀ hv).mp hc'
  · by_cases hmiddle :
        |(j : ℝ) ^ 2 * delta - a ^ 2| ≤ 4 * b * f * j
    · have hdpos : 0 < d := by
        have : 0 < d ^ 2 := by nlinarith [mul_pos hb hf]
        nlinarith [sq_nonneg d]
      obtain ⟨hv, hvalue⟩ :=
        secondOrder_middle_formula_certificate ha hb hdpos hjr hdisc
      obtain ⟨hHlow, hHhigh⟩ :=
        secondOrder_middle_formula_regime ha hb hdpos hf.le hjr hdisc hmiddle
      refine ⟨2 * b * j / (a + d * j), hv, ?_⟩
      right
      left
      refine ⟨hHlow, hHhigh, ?_⟩
      have hc' := hc
      rw [secondOrderGapThreshold_eq_middle hlower hmiddle, ← hvalue] at hc'
      exact (lt_div_iff₀ hv).mp hc'
    · obtain ⟨hv, hz, hH, hzsq, hvalue⟩ :=
        secondOrder_upper_formula_certificate ha hb hd hf hdelta hjr hdisc
      let L := a ^ 2 + 4 * b * f * j
      let k := Real.sqrt (delta * L)
      let v := 2 * b * L / (d * L + a * k)
      let z := 2 * b * f * j * k / (d * L + a * k)
      refine ⟨v, hv, ?_⟩
      right
      right
      refine ⟨z, hz.le, hH, hzsq, ?_⟩
      have hc' := hc
      rw [secondOrderGapThreshold_eq_upper hlower hmiddle, ← hvalue] at hc'
      have hc'' := (lt_div_iff₀ hv).mp hc'
      simpa [v, z, L, k] using hc''

/-- A strict gap certificate makes the exact operator quotient positive. -/
private theorem secondOrderRayOperator_eval_div_pos_of_gapCertificate
    {a b c d f j v s q : ℝ}
    (hf : 0 < f) (hj : 0 < j) (hs : 0 < s)
    (hqj : j ≤ q) (hqs : s ^ 2 ≤ j * q)
    (hcert : SecondOrderGapCertificate a b c d f j v) :
    0 < a - c * v + (d * v - b - f * v ^ 2) * s / v +
      f * v / s * q := by
  rcases hcert with ⟨hv, hcert⟩
  dsimp only at hcert
  rcases hcert with hlower | hmiddle | hupper
  · rcases hlower with ⟨hH, hc⟩
    have hbound := secondOrder_lower_scalar_lower_bound
      hf.le hv hj hs hqs
    rw [← hH] at hbound
    nlinarith
  · rcases hmiddle with ⟨hHlow, hHhigh, hc⟩
    have hbound := secondOrder_middle_scalar_lower_bound
      hf.le hv hj hs hqj hqs hHlow hHhigh
    nlinarith
  · obtain ⟨z, hz, hH, hzsq, hc⟩ := hupper
    have hbound := secondOrder_upper_scalar_lower_bound
      hf hv hH hj hs hqj hz hzsq
    nlinarith

/-- Below the strict indexed threshold, the selected point in the `j`-th
gap has positive operator quotient. -/
theorem secondOrder_exists_gapPoint_eval_div_pos
    {a b c d f delta : ℝ} {p : ℝ[X]}
    (ha : 0 ≤ a) (hb : 0 < b) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hp : p.Splits) (hp_pos : HasPosLeadingCoeff p)
    (hp_simple : HasSimpleRoots p)
    (hp_neg : ∀ r ∈ p.roots, r < 0)
    {j : ℕ} (hj : 1 ≤ j) (hjdeg : j ≤ p.natDegree)
    (hc : c < secondOrderGapThreshold a b d f delta j) :
    ∃ x : ℝ,
      x < 0 ∧ ¬p.IsRoot x ∧
      p.roots.countP (fun r ↦ x < r) = j ∧
      0 < (secondOrderRayOperator a b c d f p).eval x / p.eval x := by
  obtain ⟨v, hcert⟩ := exists_secondOrderGapCertificate_of_lt_threshold
    ha hb hd hf hdelta hj hdisc hc
  have hv : 0 < v := hcert.1
  obtain ⟨x, hx, _, hxroot, hcount, hratio⟩ :=
    secondOrder_exists_gapPoint hp hp_pos hp_simple hp_neg hv hj hjdeg
  let terms := p.roots.map fun r ↦ x / (x - r)
  let s := terms.sum
  let q := (terms.map fun y ↦ y ^ 2).sum
  obtain ⟨hs, hqj, hqs⟩ :=
    secondOrder_gap_squareSum_bound_multiset hp hp_neg hx hxroot hv hratio hcount
  have hspos : 0 < s := by
    dsimp only [s] at hs ⊢
    rw [hs]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos hv) hx
  have heval := secondOrderRayOperator_eval_div_at_gapPoint
    a b c d f hp hx.ne hv.ne' hxroot hratio
  dsimp only at heval
  change (secondOrderRayOperator a b c d f p).eval x / p.eval x =
    a - c * v + (d * v - b - f * v ^ 2) * s / v + f * v / s * q at heval
  have hpos := secondOrderRayOperator_eval_div_pos_of_gapCertificate
    hf (show (0 : ℝ) < j by positivity) hspos hqj hqs hcert
  exact ⟨x, hx, hxroot, hcount, heval.symm ▸ hpos⟩

/-- A positive `X p` coefficient raises the degree by one and determines
the leading coefficient of the second-order ray operator. -/
private theorem secondOrderRayOperator_degree_and_leadingCoeff
    {a b c d f : ℝ} {p : ℝ[X]}
    (hb : 0 < b) (hp_pos : HasPosLeadingCoeff p) :
    (secondOrderRayOperator a b c d f p).natDegree = p.natDegree + 1 ∧
      (secondOrderRayOperator a b c d f p).leadingCoeff =
        b * p.leadingCoeff := by
  let r := C c * p.derivative + C f * X * p.derivative.derivative
  have hcdeg : (C c : ℝ[X]).natDegree ≤ 1 := by
    rw [natDegree_C]
    lia
  have hfdeg : (C f * X : ℝ[X]).natDegree ≤ 2 := by
    calc
      (C f * X : ℝ[X]).natDegree ≤ (C f).natDegree + X.natDegree :=
        natDegree_mul_le
      _ ≤ 2 := by rw [natDegree_C, natDegree_X]; lia
  have hr₁ : (C c * p.derivative).natDegree ≤ p.natDegree := by
    simpa only [Function.iterate_one, Nat.add_zero] using
      (natDegree_mul_iterate_derivative_le
        (A := C c) (p := p) (d := 0) (j := 1) (D := p.natDegree)
        hcdeg le_rfl)
  have hr₂ : (C f * X * p.derivative.derivative).natDegree ≤ p.natDegree := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply,
      Nat.add_zero] using
      (natDegree_mul_iterate_derivative_le
        (A := C f * X) (p := p) (d := 0) (j := 2) (D := p.natDegree)
        hfdeg le_rfl)
  have hr : r.natDegree ≤ p.natDegree := by
    exact (natDegree_add_le _ _).trans (max_le hr₁ hr₂)
  have htop : ((0 : ℝ) * p.natDegree + b) * p.leadingCoeff ≠ 0 := by
    simpa using mul_ne_zero hb.ne' hp_pos.ne'
  have hdata :=
    Polynomial.natDegree_and_leadingCoeff_quadratic_derivative_add_linear_mul_add
      p r d 0 a b hr htop
  have hform : secondOrderRayOperator a b c d f p =
      (C d * X + C 0 * X ^ 2) * p.derivative +
        (C a + C b * X) * p + r := by
    rw [secondOrderRayOperator_eq_formula]
    dsimp only [r]
    simp only [map_zero, zero_mul, add_zero]
    ring
  rw [hform]
  simpa using hdata

/-- Nonnegative parameters make every coefficient of the operator image
nonnegative on a polynomial with nonnegative coefficients. -/
private theorem secondOrderRayOperator_hasNonnegCoeffs
    {a b c d f : ℝ} {p : ℝ[X]}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 ≤ f)
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (secondOrderRayOperator a b c d f p) := by
  rw [secondOrderRayOperator_eq_formula]
  exact ((hasNonnegCoeffs_C ha).add
      ((hasNonnegCoeffs_C_mul hb hasNonnegCoeffs_X))).mul hp |>.add
    (((hasNonnegCoeffs_C hc).add
      ((hasNonnegCoeffs_C_mul hd hasNonnegCoeffs_X))).mul hp.derivative) |>.add
    ((hasNonnegCoeffs_C_mul hf hasNonnegCoeffs_X).mul
      hp.derivative.derivative)

/-- Moving a test point to the right cannot increase the number of multiset
entries strictly to its right. -/
private theorem countP_lt_anti {s : Multiset ℝ} {x y : ℝ} (hxy : y ≤ x) :
    s.countP (fun r ↦ x < r) ≤ s.countP (fun r ↦ y < r) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons r s ih =>
      by_cases hxr : x < r
      · have hyr : y < r := hxy.trans_lt hxr
        simp [hxr, hyr, ih]
      · by_cases hyr : y < r
        · rw [Multiset.countP_cons_of_neg _ hxr,
            Multiset.countP_cons_of_pos _ hyr]
          exact ih.trans (Nat.le_succ _)
        · simpa [hxr, hyr] using ih

/-- Appending a strict upper endpoint to a strictly increasing finite family
preserves strict monotonicity. -/
private theorem strictMono_lastCases_of_lt {n : ℕ} {x : Fin n → ℝ}
    (hx : StrictMono x) {R : ℝ} (hR : ∀ i, x i < R) :
    StrictMono (Fin.lastCases R x) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last => exact (not_lt_of_ge (Fin.le_last _) hij).elim
  | cast i =>
      cases j using Fin.lastCases with
      | last => simpa using hR i
      | cast j => simpa using hx (Fin.castSucc_lt_castSucc_iff.mp hij)

/-- Strict indexed inequalities supply an ordered negative point in every
input-root gap, with the alternating output sign prescribed by that gap. -/
private theorem secondOrderRayOperator_exists_ordered_gap_signs
    {a b c d f delta : ℝ} {p : ℝ[X]}
    (ha : 0 ≤ a) (hb : 0 < b) (_hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hp : IsNegativeSimple p)
    (hthreshold : ∀ j, 1 ≤ j → j ≤ p.natDegree →
      c < secondOrderGapThreshold a b d f delta j) :
    ∃ x : Fin p.natDegree → ℝ,
      StrictMono x ∧ (∀ i, x i < 0) ∧
        ∀ i, 0 < (secondOrderRayOperator a b c d f p).eval (x i) *
          (-1 : ℝ) ^ (p.natDegree - i.1) := by
  let F := secondOrderRayOperator a b c d f p
  let n := p.natDegree
  have hpoints : ∀ i : Fin n, ∃ x : ℝ,
      x < 0 ∧ ¬p.IsRoot x ∧
      p.roots.countP (fun r ↦ x < r) = n - i.1 ∧
      0 < F.eval x / p.eval x := by
    intro i
    have hj : 1 ≤ n - i.1 := by dsimp [n] at i ⊢; lia
    have hjdeg : n - i.1 ≤ p.natDegree := by dsimp [n]; lia
    simpa only [F] using secondOrder_exists_gapPoint_eval_div_pos
      ha hb hd hf hdelta hdisc hp.2.1 hp.2.2.2.1 hp.2.2.1 hp.2.2.2.2
        hj hjdeg (hthreshold _ hj hjdeg)
  choose x hxneg hxroot hcount hquot using hpoints
  have hxmono : StrictMono x := by
    intro i k hik
    apply lt_of_not_ge
    intro hbad
    have hle := countP_lt_anti (s := p.roots) hbad
    rw [hcount i, hcount k] at hle
    have hik' : i.1 < k.1 := hik
    dsimp only [n] at i k hik' hle
    lia
  have hgapSign : ∀ i : Fin n,
      0 < F.eval (x i) * (-1 : ℝ) ^ (n - i.1) := by
    intro i
    have hpsign := hp.2.1.eval_mul_leadingCoeff_neg_one_pow_pos
      hp.1 (hxroot i)
    rw [← Multiset.countP_eq_card_filter] at hpsign
    rw [hcount i] at hpsign
    have hsame : 0 < F.eval (x i) * p.eval (x i) := by
      rcases (div_pos_iff.mp (hquot i)) with hpos | hneg <;> nlinarith
    rcases neg_one_pow_eq_or ℝ (n - i.1) with he | he
    · rw [he] at hpsign ⊢
      have hpval : 0 < p.eval (x i) := by
        have hpProd : 0 < p.eval (x i) * p.leadingCoeff := by
          simpa using hpsign
        rcases mul_pos_iff.mp hpProd with hpos | hneg
        · exact hpos.1
        · exact (not_lt_of_ge hp.2.2.2.1.le hneg.2).elim
      rcases mul_pos_iff.mp hsame with hpos | hneg
      · simpa using hpos.1
      · exact (not_lt_of_ge hpval.le hneg.2).elim
    · rw [he] at hpsign ⊢
      have hpval : p.eval (x i) < 0 := by
        apply neg_of_mul_neg_left (b := p.leadingCoeff)
          (show p.eval (x i) * p.leadingCoeff < 0 by nlinarith)
          hp.2.2.2.1.le
      have hFval : F.eval (x i) < 0 := neg_of_mul_pos_left hsame hpval.le
      nlinarith
  exact ⟨x, hxmono, hxneg, by simpa only [F, n] using hgapSign⟩

/-- Ordered alternating signs in all negative gaps, together with a positive
right exterior value, force all roots of the degree-raised output to be real. -/
private theorem splits_of_ordered_negative_gap_signs
    {F : ℝ[X]} {n : ℕ}
    (hFdeg : F.natDegree = n + 1) (hFpos : HasPosLeadingCoeff F)
    (hFnn : HasNonnegCoeffs F)
    (x : Fin n → ℝ) (hxmono : StrictMono x) (hxneg : ∀ i, x i < 0)
    (hgapSign : ∀ i : Fin n,
      0 < F.eval (x i) * (-1 : ℝ) ^ (n - i.1)) :
    F.Splits := by
  by_cases hn : n = 0
  · exact Polynomial.Splits.of_natDegree_le_one (by rw [hFdeg, hn])
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let r : Fin (n + 1) → ℝ := Fin.lastCases 1 x
  have hrmono : StrictMono r :=
    strictMono_lastCases_of_lt hxmono fun i ↦ (hxneg i).trans zero_lt_one
  have hFone : 0 < F.eval 1 :=
    eval_pos_of_hasNonnegCoeffs hFnn hFpos.ne_zero one_pos
  apply splits_of_sign_changes_with_left_endpoint
    (d := n + 1) (by lia) hFpos.ne_zero (by simpa using hFdeg)
      hFpos r (fun i j hij ↦ hrmono hij)
  · have hzero : (⟨0, by lia⟩ : Fin (n + 1)) = (⟨0, hnpos⟩ : Fin n).castSucc := by
      ext
      rfl
    rw [hzero]
    simp only [r, Fin.lastCases_castSucc]
    have hs := hgapSign ⟨0, hnpos⟩
    have hs' : 0 < F.eval (x ⟨0, hnpos⟩) * (-1 : ℝ) ^ n := by
      simpa using hs
    rw [pow_succ]
    calc
      (-1 : ℝ) ^ n * -1 * F.eval (x ⟨0, hnpos⟩) =
          -(F.eval (x ⟨0, hnpos⟩) * (-1 : ℝ) ^ n) := by ring
      _ < 0 := neg_lt_zero.mpr hs'
  · intro k hk
    by_cases hnext : k + 1 < n
    · have hs₁ := hgapSign ⟨k, by lia⟩
      have hs₂ := hgapSign ⟨k + 1, hnext⟩
      have hidx₁ : (⟨k, by lia⟩ : Fin (n + 1)) =
          (⟨k, by lia⟩ : Fin n).castSucc := by ext; rfl
      have hidx₂ : (⟨k + 1, hk⟩ : Fin (n + 1)) =
          (⟨k + 1, hnext⟩ : Fin n).castSucc := by ext; rfl
      rw [hidx₁, hidx₂]
      simp only [r, Fin.lastCases_castSucc]
      have hpow : (-1 : ℝ) ^ (n - k) =
          -((-1 : ℝ) ^ (n - (k + 1))) := by
        rw [show n - k = (n - (k + 1)) + 1 by lia, pow_succ]
        ring
      rcases neg_one_pow_eq_or ℝ (n - (k + 1)) with he | he <;>
        rw [he] at hpow hs₂ <;> rw [hpow] at hs₁ <;> nlinarith
    · have hkn : k + 1 = n := by lia
      have hs := hgapSign ⟨k, by lia⟩
      have hidx₁ : (⟨k, by lia⟩ : Fin (n + 1)) =
          (⟨k, by lia⟩ : Fin n).castSucc := by ext; rfl
      have hidx₂ : (⟨k + 1, hk⟩ : Fin (n + 1)) = Fin.last n := by
        ext
        simp [hkn]
      rw [hidx₁, hidx₂]
      simp only [r, Fin.lastCases_castSucc, Fin.lastCases_last]
      have hsub : n - k = 1 := by lia
      rw [hsub, pow_one] at hs
      nlinarith

/-- A negative-simple input is preserved under strict inequalities at every
indexed threshold. -/
private theorem secondOrderRayOperator_isPFPolynomial_of_isNegativeSimple
    {a b c d f delta : ℝ} {p : ℝ[X]}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hp : IsNegativeSimple p)
    (hthreshold : ∀ j, 1 ≤ j → j ≤ p.natDegree →
      c < secondOrderGapThreshold a b d f delta j) :
    IsPFPolynomial (secondOrderRayOperator a b c d f p) := by
  let F := secondOrderRayOperator a b c d f p
  have hdegree := secondOrderRayOperator_degree_and_leadingCoeff
    (a := a) (b := b) (c := c) (d := d) (f := f) hb hp.2.2.2.1
  have hFpos : HasPosLeadingCoeff F := by
    dsimp only [F]
    rw [HasPosLeadingCoeff, hdegree.2]
    exact mul_pos hb hp.2.2.2.1
  have hFnn : HasNonnegCoeffs F :=
    secondOrderRayOperator_hasNonnegCoeffs ha hb.le hc hd hf.le
      hp.isPFPolynomial.hasNonnegCoeffs
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hFnn
  right
  obtain ⟨x, hxmono, hxneg, hgapSign⟩ :=
    secondOrderRayOperator_exists_ordered_gap_signs
      ha hb hc hd hf hdelta hdisc hp hthreshold
  exact splits_of_ordered_negative_gap_signs hdegree.1 hFpos hFnn
    x hxmono hxneg hgapSign

/-- Weak indexed inequalities preserve a negative-simple input, including
equality, by approaching the constant-derivative coefficient from below. -/
private theorem secondOrderRayOperator_isPFPolynomial_of_isNegativeSimple_le
    {a b c d f delta : ℝ} {p : ℝ[X]}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hp : IsNegativeSimple p)
    (hthreshold : ∀ j, 1 ≤ j → j ≤ p.natDegree →
      c ≤ secondOrderGapThreshold a b d f delta j) :
    IsPFPolynomial (secondOrderRayOperator a b c d f p) := by
  let eps : ℕ → ℝ := fun k ↦ 1 / (k + 1 : ℝ)
  let cseq : ℕ → ℝ := fun k ↦ (1 - eps k) * c
  have heps_pos (k : ℕ) : 0 < eps k := by dsimp [eps]; positivity
  have heps_le (k : ℕ) : eps k ≤ 1 := by
    dsimp [eps]
    apply (div_le_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)).2
    norm_num
  have hcseq_nonneg (k : ℕ) : 0 ≤ cseq k := by
    dsimp [cseq]
    exact mul_nonneg (sub_nonneg.mpr (heps_le k)) hc
  have hcseq_lt (k : ℕ) (j : ℕ) (hj : 1 ≤ j)
      (hjdeg : j ≤ p.natDegree) :
      cseq k < secondOrderGapThreshold a b d f delta j := by
    by_cases hc0 : c = 0
    · subst c
      dsimp [cseq]
      simp only [mul_zero]
      exact secondOrderGapThreshold_pos ha hb hd hf hdelta hj
    · exact lt_of_lt_of_le
        (by
          dsimp [cseq]
          nlinarith [mul_pos (heps_pos k) (lt_of_le_of_ne hc (Ne.symm hc0))])
        (hthreshold j hj hjdeg)
  have hPF (k : ℕ) :
      IsPFPolynomial (secondOrderRayOperator a b (cseq k) d f p) :=
    secondOrderRayOperator_isPFPolynomial_of_isNegativeSimple
      ha hb (hcseq_nonneg k) hd hf hdelta hdisc hp (hcseq_lt k)
  have heps : Tendsto eps atTop (𝓝 0) := by
    simpa [eps, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcseq : Tendsto cseq atTop (𝓝 c) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    simpa [cseq] using (hone.sub heps).mul_const c
  apply IsPFPolynomial.of_coeff_tendsto hPF
  intro i
  have hid (k : ℕ) :
      secondOrderRayOperator a b (cseq k) d f p =
        secondOrderRayOperator a b c d f p + C (cseq k - c) * p.derivative := by
    rw [secondOrderRayOperator_eq_formula, secondOrderRayOperator_eq_formula]
    rw [map_sub]
    ring
  simp_rw [hid, coeff_add, coeff_C_mul]
  have hconst : Tendsto
      (fun _ : ℕ ↦ (secondOrderRayOperator a b c d f p).coeff i)
      atTop (𝓝 ((secondOrderRayOperator a b c d f p).coeff i)) :=
    tendsto_const_nhds
  have hcconst : Tendsto (fun _ : ℕ ↦ c) atTop (𝓝 c) := tendsto_const_nhds
  simpa using hconst.add
    ((hcseq.sub hcconst).mul_const (p.derivative.coeff i))

/-- If every indexed gap threshold dominates `c`, then the second-order ray
operator preserves every PF polynomial. This theorem includes weak equality,
repeated roots, roots at zero, and the zero polynomial. -/
theorem secondOrderRayPreserving_of_forall_le_gapThreshold
    {a b c d f delta : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hthreshold : ∀ j, 1 ≤ j →
      c ≤ secondOrderGapThreshold a b d f delta j) :
    ∀ p, IsPFPolynomial p →
      IsPFPolynomial (secondOrderRayOperator a b c d f p) := by
  intro p hp
  have hout := isPFPolynomial_map_of_isNegativeSimple
    (secondOrderRayOperatorₗ a b c d f) (p := p) (hp := hp) (fun {q} hq ↦ by
      simpa only [secondOrderRayOperatorₗ_apply] using
        secondOrderRayOperator_isPFPolynomial_of_isNegativeSimple_le
          ha hb hc hd hf hdelta hdisc hq fun j hj hjdeg ↦ hthreshold j hj)
  simpa only [secondOrderRayOperatorₗ_apply] using hout

/-- It suffices to check the indexed threshold only at an integer selected by
the issue's two neighboring-product inequalities. -/
theorem secondOrderRayPreserving_of_le_gapThreshold_at_index
    {a b c d f delta : ℝ} {m : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hm : 1 ≤ m)
    (hmlo : delta * (m : ℝ) * ((m : ℝ) - 1) ≤ a ^ 2)
    (hmhi : a ^ 2 ≤ delta * (m : ℝ) * ((m : ℝ) + 1))
    (hcm : c ≤ secondOrderGapThreshold a b d f delta m) :
    ∀ p, IsPFPolynomial p →
      IsPFPolynomial (secondOrderRayOperator a b c d f p) := by
  apply secondOrderRayPreserving_of_forall_le_gapThreshold
    ha hb hc hd hf hdelta hdisc
  intro j hj
  exact hcm.trans
    (secondOrderGapThreshold_minimized_at_index
      ha hb hf hdelta hm hj hmlo hmhi)

/-- The explicit lower, middle, and upper formulas at the minimizing index
each imply preservation of every PF polynomial. -/
theorem secondOrderRayPreserving_of_three_branch_at_index
    {a b c d f delta : ℝ} {m : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 0 < delta) (hdisc : delta = d ^ 2 - 4 * b * f)
    (hm : 1 ≤ m)
    (hmlo : delta * (m : ℝ) * ((m : ℝ) - 1) ≤ a ^ 2)
    (hmhi : a ^ 2 ≤ delta * (m : ℝ) * ((m : ℝ) + 1))
    (hbranch :
      (a ^ 2 > (m : ℝ) ^ 2 * delta + 4 * b * f * m ∧
        c ≤ a * (d + Real.sqrt (delta + 4 * b * f / m)) / (2 * b)) ∨
      (¬a ^ 2 > (m : ℝ) ^ 2 * delta + 4 * b * f * m ∧
        |(m : ℝ) ^ 2 * delta - a ^ 2| ≤ 4 * b * f * m ∧
        c ≤ f + a * d / (2 * b) + m * delta / (4 * b) +
          a ^ 2 / (4 * b * m)) ∨
      (¬a ^ 2 > (m : ℝ) ^ 2 * delta + 4 * b * f * m ∧
        ¬|(m : ℝ) ^ 2 * delta - a ^ 2| ≤ 4 * b * f * m ∧
        c ≤ (a * d + Real.sqrt (delta * (a ^ 2 + 4 * b * f * m))) /
          (2 * b))) :
    ∀ p, IsPFPolynomial p →
      IsPFPolynomial (secondOrderRayOperator a b c d f p) := by
  apply secondOrderRayPreserving_of_le_gapThreshold_at_index
    ha hb hc hd hf hdelta hdisc hm hmlo hmhi
  rcases hbranch with ⟨hlower, hbound⟩ | ⟨hlower, hmiddle, hbound⟩ |
      ⟨hlower, hmiddle, hbound⟩
  · simpa only [secondOrderGapThreshold_eq_lower hlower] using hbound
  · simpa only [secondOrderGapThreshold_eq_middle hlower hmiddle] using hbound
  · simpa only [secondOrderGapThreshold_eq_upper hlower hmiddle] using hbound

end RealRooted
