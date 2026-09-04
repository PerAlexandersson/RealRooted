import RealRooted.AffineDerivative
import RealRooted.ParkingFunctions.ToricContribution.ExceptionalOffset.BaseAndMoments
import RealRooted.SuccDegreeLeftEndpoint

/-!
# Exceptional-offset pencil splitting

This layer proves real-rootedness for every signed member of the exceptional
Euler-inverse pencil.
-/

open Polynomial
open MeasureTheory Set

noncomputable section

namespace RealRooted
namespace ParkingFunctions
namespace ToricContribution

/-- Exterior density associated with a signed pencil member. -/
def exceptionalPencilExteriorDensity
    (m ε : ℕ) (γ₁ γ₂ a b x : ℝ) : ℝ :=
  a * (exceptionalEulerInverse m ε γ₁).eval 1 *
      x ^ ((ε : ℝ) + 1 / 2 - γ₁ - 1) +
    b * (exceptionalEulerInverse m ε γ₂).eval 1 *
      x ^ ((ε : ℝ) + 1 / 2 - γ₂ - 1)

@[simp]
theorem exceptionalPencilExteriorDensity_one
    (m ε : ℕ) (γ₁ γ₂ a b : ℝ) :
    exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b 1 =
      (C a * exceptionalEulerInverse m ε γ₁ +
        C b * exceptionalEulerInverse m ε γ₂).eval 1 := by
  simp [exceptionalPencilExteriorDensity]

private theorem continuousAt_exceptionalPencilExteriorDensity
    (m ε : ℕ) (γ₁ γ₂ a b : ℝ) {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt
      (exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b) x := by
  unfold exceptionalPencilExteriorDensity
  exact
    ((continuousAt_const.mul continuousAt_const).mul
      (continuousAt_id.rpow_const (Or.inl hx))).add
    ((continuousAt_const.mul continuousAt_const).mul
      (continuousAt_id.rpow_const (Or.inl hx)))

private theorem mul_pos_of_continuousOn_of_ne_zero
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hno : ∀ x, a ≤ x → x ≤ b → f x ≠ 0) :
    0 < f a * f b := by
  have ha : f a ≠ 0 := hno a le_rfl hab
  have hb : f b ≠ 0 := hno b hab le_rfl
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · have hbNeg : f b < 0 := by
      rcases lt_or_gt_of_ne hb with hbNeg | hbPos
      · exact hbNeg
      · have hzero : (0 : ℝ) ∈ Set.Icc (f a) (f b) :=
          ⟨haNeg.le, hbPos.le⟩
        obtain ⟨x, hx, hfx⟩ :=
          intermediate_value_Icc hab hf hzero
        exact ((hno x hx.1 hx.2) hfx).elim
    exact mul_pos_of_neg_of_neg haNeg hbNeg
  · have hbPos : 0 < f b := by
      rcases lt_or_gt_of_ne hb with hbNeg | hbPos
      · have hzero : (0 : ℝ) ∈ Set.Icc (f b) (f a) :=
          ⟨hbNeg.le, haPos.le⟩
        obtain ⟨x, hx, hfx⟩ :=
          intermediate_value_Icc' hab hf hzero
        exact ((hno x hx.1 hx.2) hfx).elim
      · exact hbPos
    exact mul_pos haPos hbPos

/-- A nonzero two-power exterior density has at most one zero on `(1, ∞)`.
This is the analytic core of P6. -/
theorem exceptionalPencilExteriorDensity_ne_zero_of_lt
    (m ε : ℕ) {γ₁ γ₂ a b x y : ℝ}
    (hγ : γ₁ < γ₂) (hx : 1 < x) (hxy : x < y)
    (hcoeff :
      a * (exceptionalEulerInverse m ε γ₁).eval 1 ≠ 0 ∨
        b * (exceptionalEulerInverse m ε γ₂).eval 1 ≠ 0)
    (hxzero : exceptionalPencilExteriorDensity
      m ε γ₁ γ₂ a b x = 0) :
    exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b y ≠ 0 := by
  let A := a * (exceptionalEulerInverse m ε γ₁).eval 1
  let B := b * (exceptionalEulerInverse m ε γ₂).eval 1
  let e := (ε : ℝ) + 1 / 2 - γ₂ - 1
  let d := γ₂ - γ₁
  have hxpos : 0 < x := lt_trans one_pos hx
  have hypos : 0 < y := lt_trans hxpos hxy
  have hd : 0 < d := by
    dsimp only [d]
    linarith
  have hxFactor :
      exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b x =
        x ^ e * (A * x ^ d + B) := by
    rw [exceptionalPencilExteriorDensity]
    dsimp only [A, B, e, d]
    have hxpow :
        x ^ ((ε : ℝ) + 1 / 2 - γ₁ - 1) =
          x ^ ((ε : ℝ) + 1 / 2 - γ₂ - 1) * x ^ (γ₂ - γ₁) := by
      calc
        x ^ ((ε : ℝ) + 1 / 2 - γ₁ - 1) =
            x ^ (((ε : ℝ) + 1 / 2 - γ₂ - 1) + (γ₂ - γ₁)) := by
          congr 1
          ring
        _ = _ := Real.rpow_add hxpos _ _
    rw [hxpow]
    ring
  have hyFactor :
      exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b y =
        y ^ e * (A * y ^ d + B) := by
    rw [exceptionalPencilExteriorDensity]
    dsimp only [A, B, e, d]
    have hypow :
        y ^ ((ε : ℝ) + 1 / 2 - γ₁ - 1) =
          y ^ ((ε : ℝ) + 1 / 2 - γ₂ - 1) * y ^ (γ₂ - γ₁) := by
      calc
        y ^ ((ε : ℝ) + 1 / 2 - γ₁ - 1) =
            y ^ (((ε : ℝ) + 1 / 2 - γ₂ - 1) + (γ₂ - γ₁)) := by
          congr 1
          ring
        _ = _ := Real.rpow_add hypos _ _
    rw [hypow]
    ring
  have hxLinear : A * x ^ d + B = 0 := by
    rw [hxFactor] at hxzero
    exact (mul_eq_zero.mp hxzero).resolve_left
      (Real.rpow_pos_of_pos hxpos e).ne'
  intro hyzero
  have hyLinear : A * y ^ d + B = 0 := by
    rw [hyFactor] at hyzero
    exact (mul_eq_zero.mp hyzero).resolve_left
      (Real.rpow_pos_of_pos hypos e).ne'
  have hA : A ≠ 0 := by
    intro hAzero
    have hBzero : B = 0 := by simpa only [hAzero, zero_mul, zero_add] using hxLinear
    rcases hcoeff with hcoeff | hcoeff
    · exact hcoeff hAzero
    · exact hcoeff hBzero
  have hpowers : x ^ d = y ^ d := by
    apply mul_left_cancel₀ hA
    linarith
  have hpowlt : x ^ d < y ^ d :=
    Real.rpow_lt_rpow hxpos.le hxy hd
  linarith

private theorem exceptionalPencilExteriorDensity_crossing_pos
    (m ε : ℕ) {γ₁ γ₂ a b κ x : ℝ}
    (hγ : γ₁ < γ₂) (hκ : 1 < κ) (hx : 1 < x) (hxκ : x ≠ κ)
    (hcoeff :
      a * (exceptionalEulerInverse m ε γ₁).eval 1 ≠ 0 ∨
        b * (exceptionalEulerInverse m ε γ₂).eval 1 ≠ 0)
    (hκzero : exceptionalPencilExteriorDensity
      m ε γ₁ γ₂ a b κ = 0) :
    0 < exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b 1 *
      ((κ - x) *
        exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b x) := by
  let A := a * (exceptionalEulerInverse m ε γ₁).eval 1
  let B := b * (exceptionalEulerInverse m ε γ₂).eval 1
  let e := (ε : ℝ) + 1 / 2 - γ₂ - 1
  let d := γ₂ - γ₁
  have hκpos : 0 < κ := one_pos.trans hκ
  have hxpos : 0 < x := one_pos.trans hx
  have hd : 0 < d := by
    dsimp only [d]
    linarith
  have hfactor : ∀ {z : ℝ}, 0 < z →
      exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b z =
        z ^ e * (A * z ^ d + B) := by
    intro z hz
    rw [exceptionalPencilExteriorDensity]
    dsimp only [A, B, e, d]
    have hzpow :
        z ^ ((ε : ℝ) + 1 / 2 - γ₁ - 1) =
          z ^ ((ε : ℝ) + 1 / 2 - γ₂ - 1) *
            z ^ (γ₂ - γ₁) := by
      calc
        z ^ ((ε : ℝ) + 1 / 2 - γ₁ - 1) =
            z ^ (((ε : ℝ) + 1 / 2 - γ₂ - 1) +
              (γ₂ - γ₁)) := by
          congr 1
          ring
        _ = _ := Real.rpow_add hz _ _
    rw [hzpow]
    ring
  have hκLinear : A * κ ^ d + B = 0 := by
    rw [hfactor hκpos] at hκzero
    exact (mul_eq_zero.mp hκzero).resolve_left
      (Real.rpow_pos_of_pos hκpos e).ne'
  have hA : A ≠ 0 := by
    intro hAzero
    have hBzero : B = 0 := by
      simpa only [hAzero, zero_mul, zero_add] using hκLinear
    rcases hcoeff with hcoeff | hcoeff
    · exact hcoeff hAzero
    · exact hcoeff hBzero
  have hOne :
      exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b 1 =
        A * (1 - κ ^ d) := by
    calc
      exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b 1 =
          A + B := by simp [exceptionalPencilExteriorDensity, A, B]
      _ = A * (1 - κ ^ d) := by linarith
  have hX :
      exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b x =
        x ^ e * A * (x ^ d - κ ^ d) := by
    rw [hfactor hxpos]
    have hB : B = -(A * κ ^ d) := by linarith
    rw [hB]
    ring
  have hκpow : 1 < κ ^ d := by
    simpa only [Real.one_rpow] using
      Real.rpow_lt_rpow one_pos.le hκ hd
  have hpair : (κ - x) * (x ^ d - κ ^ d) < 0 := by
    rcases lt_or_gt_of_ne hxκ with hxκ | hκx
    · have hpow := Real.rpow_lt_rpow hxpos.le hxκ hd
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hxκ)
        (sub_neg.mpr hpow)
    · have hpow := Real.rpow_lt_rpow hκpos.le hκx hd
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hκx)
        (sub_pos.mpr hpow)
  have hxpow : 0 < x ^ e := Real.rpow_pos_of_pos hxpos e
  rw [hOne, hX]
  calc
    A * (1 - κ ^ d) *
        ((κ - x) * (x ^ e * A * (x ^ d - κ ^ d))) =
      A ^ 2 * x ^ e * (κ ^ d - 1) *
        (-((κ - x) * (x ^ d - κ ^ d))) := by ring
    _ > 0 :=
      mul_pos
        (mul_pos
          (mul_pos (sq_pos_of_ne_zero hA) hxpow)
          (sub_pos.mpr hκpow))
        (neg_pos.mpr hpair)

/-- Algebraic P6 identity for an arbitrary signed pencil member. -/
theorem jacobiBetaZeroFunctional_exceptionalPencil_mul_eq
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (p : ℝ[X])
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hp : p.natDegree < m) :
    jacobiBetaZeroFunctional ((ε : ℝ) - 1 / 2)
        ((C a * exceptionalEulerInverse m ε γ₁ +
          C b * exceptionalEulerInverse m ε γ₂) * p) =
      -(a * (exceptionalEulerInverse m ε γ₁).eval 1) *
          exceptionalExteriorFunctional
            ((ε : ℝ) + 1 / 2) γ₁ p -
        (b * (exceptionalEulerInverse m ε γ₂).eval 1) *
          exceptionalExteriorFunctional
            ((ε : ℝ) + 1 / 2) γ₂ p := by
  rw [add_mul, jacobiBetaZeroFunctional_add]
  rw [show C a * exceptionalEulerInverse m ε γ₁ * p =
      C a * (exceptionalEulerInverse m ε γ₁ * p) by ring,
    show C b * exceptionalEulerInverse m ε γ₂ * p =
      C b * (exceptionalEulerInverse m ε γ₂ * p) by ring,
    jacobiBetaZeroFunctional_C_mul,
    jacobiBetaZeroFunctional_C_mul,
    jacobiBetaZeroFunctional_exceptionalEulerInverse_mul_eq
      m ε p hγ₁ hp,
    jacobiBetaZeroFunctional_exceptionalEulerInverse_mul_eq
      m ε p hγ₂ hp]
  ring

private theorem integrableOn_exceptionalExteriorIntegrand
    (c γ : ℝ) (p : ℝ[X]) (hγ : c + p.natDegree < γ) :
    IntegrableOn (fun x : ℝ => p.eval x * x ^ (c - γ - 1))
      (Ioi 1) volume := by
  have hexponent : ∀ j ∈ Finset.range (p.natDegree + 1),
      c - γ - 1 + (j : ℝ) < -1 := by
    intro j hj
    have hjle : j ≤ p.natDegree := by
      have hjlt := Finset.mem_range.mp hj
      lia
    have hjleCast : (j : ℝ) ≤ p.natDegree := by exact_mod_cast hjle
    linarith
  have hsum : IntegrableOn
      (fun x : ℝ => ∑ j ∈ Finset.range (p.natDegree + 1),
        p.coeff j * x ^ (c - γ - 1 + (j : ℝ)))
      (Ioi 1) volume := by
    apply integrable_finsetSum
    intro j hj
    exact (integrableOn_Ioi_rpow_of_lt
      (hexponent j hj) one_pos).const_mul _
  exact hsum.congr_fun (fun x hx => by
    have hxpos : 0 < x := lt_trans one_pos hx
    rw [Polynomial.eval_eq_sum_range]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.rpow_add hxpos, Real.rpow_natCast]
    ring) measurableSet_Ioi

private theorem integrableOn_mul_exceptionalPencilExteriorDensity
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (p : ℝ[X])
    (hγ₁ : (ε : ℝ) + 1 / 2 + p.natDegree < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + p.natDegree < γ₂) :
    IntegrableOn
      (fun x : ℝ => p.eval x *
        exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b x)
      (Ioi 1) volume := by
  let c : ℝ := ε + 1 / 2
  let A := a * (exceptionalEulerInverse m ε γ₁).eval 1
  let B := b * (exceptionalEulerInverse m ε γ₂).eval 1
  have h₁ := integrableOn_exceptionalExteriorIntegrand
    c γ₁ p (by simpa only [c] using hγ₁)
  have h₂ := integrableOn_exceptionalExteriorIntegrand
    c γ₂ p (by simpa only [c] using hγ₂)
  have hsum : IntegrableOn
      (fun x : ℝ =>
        A * (p.eval x * x ^ (c - γ₁ - 1)) +
          B * (p.eval x * x ^ (c - γ₂ - 1)))
      (Ioi 1) volume :=
    (h₁.const_mul A).add (h₂.const_mul B)
  exact hsum.congr_fun (fun x hx => by
    unfold exceptionalPencilExteriorDensity
    dsimp only [A, B, c]
    ring) measurableSet_Ioi

private theorem setIntegral_pos_of_pos_Ioi
    {f : ℝ → ℝ} (hfInt : IntegrableOn f (Ioi 1) volume)
    (hfPos : ∀ x : ℝ, 1 < x → 0 < f x) :
    0 < ∫ x in Ioi (1 : ℝ), f x := by
  have hfNonneg : 0 ≤ᵐ[volume.restrict (Ioi 1)] f := by
    rw [Filter.EventuallyLE,
      MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    exact (hfPos x hx).le
  apply (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
    hfNonneg hfInt).mpr
  have hsubset : Ioo (1 : ℝ) 2 ⊆
      Function.support f ∩ Ioi 1 := by
    intro x hx
    exact ⟨Function.mem_support.mpr (hfPos x hx.1).ne', hx.1⟩
  exact ((MeasureTheory.Measure.measure_Ioo_pos _).mpr
    (show (1 : ℝ) < 2 by norm_num)).trans_le
      (MeasureTheory.measure_mono hsubset)

/-- Integral form of P6 for an arbitrary signed pencil member. -/
theorem exceptionalEulerInverse_pencil_signedMomentIdentity
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (p : ℝ[X])
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hp : p.natDegree < m) :
    (∫ x : ℝ in 0..1,
        ((C a * exceptionalEulerInverse m ε γ₁ +
          C b * exceptionalEulerInverse m ε γ₂) * p).eval x *
            x ^ ((ε : ℝ) - 1 / 2)) =
      -∫ x in Ioi (1 : ℝ),
        p.eval x * exceptionalPencilExteriorDensity
          m ε γ₁ γ₂ a b x := by
  let c : ℝ := ε + 1 / 2
  let A := a * (exceptionalEulerInverse m ε γ₁).eval 1
  let B := b * (exceptionalEulerInverse m ε γ₂).eval 1
  have hε : 0 ≤ (ε : ℝ) := by positivity
  have hα : -1 < (ε : ℝ) - 1 / 2 := by linarith
  have hpCast : (p.natDegree : ℝ) ≤ m - 1 := by
    have hpOne : p.natDegree + 1 ≤ m := by lia
    have hpOneCast : (p.natDegree : ℝ) + 1 ≤ m := by
      exact_mod_cast hpOne
    linarith
  have hγ₁p : c + p.natDegree < γ₁ := by
    dsimp only [c]
    linarith
  have hγ₂p : c + p.natDegree < γ₂ := by
    dsimp only [c]
    linarith
  have hint₁ := integrableOn_exceptionalExteriorIntegrand
    c γ₁ p hγ₁p
  have hint₂ := integrableOn_exceptionalExteriorIntegrand
    c γ₂ p hγ₂p
  rw [← jacobiBetaZeroFunctional_eq_integral hα]
  rw [jacobiBetaZeroFunctional_exceptionalPencil_mul_eq
    m ε p hγ₁ hγ₂ hp]
  rw [exceptionalExteriorFunctional_eq_integral c γ₁ p hγ₁p,
    exceptionalExteriorFunctional_eq_integral c γ₂ p hγ₂p]
  change
    -A * (∫ x in Ioi (1 : ℝ), p.eval x * x ^ (c - γ₁ - 1)) -
        B * (∫ x in Ioi (1 : ℝ), p.eval x * x ^ (c - γ₂ - 1)) = _
  rw [show -A * (∫ x in Ioi (1 : ℝ),
          p.eval x * x ^ (c - γ₁ - 1)) -
        B * (∫ x in Ioi (1 : ℝ),
          p.eval x * x ^ (c - γ₂ - 1)) =
      -(A * (∫ x in Ioi (1 : ℝ),
          p.eval x * x ^ (c - γ₁ - 1)) +
        B * (∫ x in Ioi (1 : ℝ),
          p.eval x * x ^ (c - γ₂ - 1))) by ring]
  congr 1
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hint₁.const_mul A) (hint₂.const_mul B)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  unfold exceptionalPencilExteriorDensity
  dsimp only [A, B, c]
  ring

private def interiorRootProduct (q : ℝ[X]) : ℝ[X] :=
  ((q.roots.filter fun r => 0 < r ∧ r < 1).map
    fun r => X - C r).prod

private theorem natDegree_interiorRootProduct (q : ℝ[X]) :
    (interiorRootProduct q).natDegree =
      (q.roots.filter fun r => 0 < r ∧ r < 1).card := by
  exact Polynomial.natDegree_multiset_prod_X_sub_C_eq_card _

private theorem interiorRootProduct_eval_pos_of_one_le
    (q : ℝ[X]) {x : ℝ} (hx : 1 ≤ x) :
    0 < (interiorRootProduct q).eval x := by
  rw [interiorRootProduct, Polynomial.eval_multiset_prod,
    Multiset.map_map]
  apply Multiset.prod_pos
  intro y hy
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
  have hrOne : r < 1 := (Multiset.mem_filter.mp hr).2.2
  simpa using sub_pos.mpr (hrOne.trans_le hx)

private theorem exists_interiorRootComplement
    {q : ℝ[X]} (hq : q ≠ 0) :
    ∃ s : ℝ[X], interiorRootProduct q * s = q ∧
      ∀ x : ℝ, 0 < x → x < 1 → s.eval x ≠ 0 := by
  let rootsI := q.roots.filter fun r => 0 < r ∧ r < 1
  let P := (rootsI.map fun r => X - C r).prod
  have hPle : rootsI ≤ q.roots := Multiset.filter_le _ _
  have hPdvd : P ∣ q :=
    (Multiset.prod_X_sub_C_dvd_iff_le_roots hq rootsI).mpr hPle
  obtain ⟨s, hs⟩ := hPdvd
  have hP : P ≠ 0 :=
    (Polynomial.monic_multisetProd_X_sub_C rootsI).ne_zero
  have hs0 : s ≠ 0 := by
    intro hszero
    rw [hszero, mul_zero] at hs
    exact hq hs
  refine ⟨s, ?_, ?_⟩
  · simpa only [interiorRootProduct, P, rootsI] using hs.symm
  · intro x hx0 hx1 hsx
    have hsroot : s.IsRoot x := by
      simpa only [Polynomial.IsRoot.def] using hsx
    have hsMem : x ∈ s.roots :=
      (Polynomial.mem_roots hs0).mpr hsroot
    have hroots : q.roots = rootsI + s.roots := by
      rw [hs, Polynomial.roots_mul (mul_ne_zero hP hs0),
        Polynomial.roots_multiset_prod_X_sub_C]
    have hcount := congrArg (fun u : Multiset ℝ => u.count x) hroots
    have hfilter : rootsI.count x = q.roots.count x := by
      simp [rootsI, hx0, hx1]
    have hsCount : 0 < s.roots.count x :=
      Multiset.count_pos.mpr hsMem
    simp only [Multiset.count_add] at hcount
    lia

private theorem interiorRootProduct_signedIntegral_pos
    {q : ℝ[X]} (hq : q ≠ 0) (hqOne : q.eval 1 ≠ 0)
    {α : ℝ} (hα : -1 < α) (t : ℝ[X])
    (ht : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < t.eval x) :
    0 < q.eval 1 *
      (∫ x : ℝ in 0..1,
        (q * (interiorRootProduct q * t)).eval x * x ^ α) := by
  let P := interiorRootProduct q
  obtain ⟨s, hfactor, hsNo⟩ :=
    (show ∃ s : ℝ[X], P * s = q ∧
        ∀ x : ℝ, 0 < x → x < 1 → s.eval x ≠ 0 by
      simpa only [P] using exists_interiorRootComplement hq)
  have hP : P ≠ 0 := by
    dsimp only [P, interiorRootProduct]
    exact (Polynomial.monic_multisetProd_X_sub_C _).ne_zero
  have hPone : 0 < P.eval 1 := by
    dsimp only [P]
    exact interiorRootProduct_eval_pos_of_one_le q le_rfl
  have hfactorEval : ∀ x : ℝ, P.eval x * s.eval x = q.eval x := by
    intro x
    simpa only [eval_mul] using
      congrArg (Polynomial.eval x) hfactor
  have hsOne : s.eval 1 ≠ 0 := by
    intro hsOne
    have h := hfactorEval 1
    rw [hsOne, mul_zero] at h
    exact hqOne h.symm
  have hsSame : ∀ x : ℝ, 0 < x → x ≤ 1 →
      0 < s.eval x * s.eval 1 := by
    intro x hx0 hx1
    apply eval_same_sign_of_no_roots hx1
    intro z hxz hz1
    by_cases hz : z = 1
    · simpa only [hz] using hsOne
    · exact hsNo z (hx0.trans_le hxz) (lt_of_le_of_ne hz1 hz)
  let f : ℝ → ℝ := fun x =>
    q.eval 1 * ((q * (P * t)).eval x * x ^ α)
  have hfInt : IntervalIntegrable f volume 0 1 := by
    have h := intervalIntegrable_jacobiBetaZeroIntegrand hα
      (C (q.eval 1) * (q * (P * t)))
    convert h using 1
    ext x
    simp only [f, eval_mul, eval_C]
    ring
  have hfNonneg : 0 ≤ᵐ[volume.restrict (Set.uIoc 0 1)] f := by
    rw [Set.uIoc_of_le zero_le_one, Filter.EventuallyLE,
      MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    have hsPos := hsSame x hx.1 hx.2
    have hxpow : 0 < x ^ α := Real.rpow_pos_of_pos hx.1 α
    have htPos := ht x hx.1 hx.2
    have hfactorX := hfactorEval x
    have hfactorOne := hfactorEval 1
    dsimp only [f]
    simp only [eval_mul]
    calc
      q.eval 1 * (q.eval x * (P.eval x * t.eval x) * x ^ α) =
          P.eval 1 * P.eval x ^ 2 *
            (s.eval x * s.eval 1) * t.eval x * x ^ α := by
        rw [← hfactorX, ← hfactorOne]
        ring
      _ ≥ 0 := by positivity
  obtain ⟨x, hx, havoid⟩ :=
    (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finset
      P.roots.toFinset
  have hPx : P.eval x ≠ 0 := by
    intro hPx
    apply havoid
    have hroot : P.IsRoot x := by
      simpa only [Polynomial.IsRoot.def] using hPx
    exact Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hP).mpr hroot)
  have hfx : 0 < f x := by
    have hsPos := hsSame x hx.1 hx.2.le
    have hxpow : 0 < x ^ α := Real.rpow_pos_of_pos hx.1 α
    have htPos := ht x hx.1 hx.2.le
    have hfactorX := hfactorEval x
    have hfactorOne := hfactorEval 1
    dsimp only [f]
    simp only [eval_mul]
    calc
      q.eval 1 * (q.eval x * (P.eval x * t.eval x) * x ^ α) =
          P.eval 1 * P.eval x ^ 2 *
            (s.eval x * s.eval 1) * t.eval x * x ^ α := by
        rw [← hfactorX, ← hfactorOne]
        ring
      _ > 0 := by positivity
  have hfCont : ContinuousAt f x := by
    have hx0 : x ≠ 0 := hx.1.ne'
    dsimp only [f]
    exact continuousAt_const.mul
      ((q * (P * t)).continuousAt.mul
        (continuousAt_id.rpow_const (Or.inl hx0)))
  have hevent : ∀ᶠ y in nhds x, f y ≠ 0 :=
    hfCont.eventually_ne hfx.ne'
  obtain ⟨a, b, hxab, hab⟩ := hevent.exists_Ioo_subset
  let a' := max a 0
  let b' := min b 1
  have ha'x : a' < x := max_lt hxab.1 hx.1
  have hxb' : x < b' := lt_min hxab.2 hx.2
  have ha'b' : a' < b' := ha'x.trans hxb'
  have hsubset : Set.Ioo a' b' ⊆
      Function.support f ∩ Set.Ioc 0 1 := by
    intro y hy
    have hay : a < y := (le_max_left a 0).trans_lt hy.1
    have hyb : y < b := hy.2.trans_le (min_le_left b 1)
    refine ⟨Function.mem_support.mpr (hab ⟨hay, hyb⟩), ?_⟩
    exact ⟨(le_max_right a 0).trans_lt hy.1,
      (hy.2.trans_le (min_le_right b 1)).le⟩
  have hmeasure : 0 < volume
      (Function.support f ∩ Set.Ioc 0 1) :=
    ((MeasureTheory.Measure.measure_Ioo_pos _).mpr ha'b').trans_le
      (MeasureTheory.measure_mono hsubset)
  rw [← intervalIntegral.integral_const_mul]
  exact (intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    hfNonneg hfInt).mpr ⟨zero_lt_one, hmeasure⟩

/-- A generic nonzero exceptional pencil member has at least `m - 1` roots,
counted with multiplicity, in the open unit interval. -/
theorem exceptionalEulerInverse_pencil_card_roots_Ioo_ge_sub_one
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (hm : 0 < m)
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hγ : γ₁ < γ₂) (hab : a ≠ 0 ∨ b ≠ 0)
    (hOne :
      (C a * exceptionalEulerInverse m ε γ₁ +
        C b * exceptionalEulerInverse m ε γ₂).eval 1 ≠ 0) :
    m - 1 ≤
      ((C a * exceptionalEulerInverse m ε γ₁ +
        C b * exceptionalEulerInverse m ε γ₂).roots.filter
          fun r => 0 < r ∧ r < 1).card := by
  let Q := C a * exceptionalEulerInverse m ε γ₁ +
    C b * exceptionalEulerInverse m ε γ₂
  let P := interiorRootProduct Q
  let K := exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b
  have hQOne : Q.eval 1 ≠ 0 := by
    simpa only [Q] using hOne
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hQOne
    rw [hzero]
    simp
  have hR₁One :
      (exceptionalEulerInverse m ε γ₁).eval 1 ≠ 0 := by
    have hsign :=
      negOnePow_mul_exceptionalEulerInverse_eval_one_pos
        m ε hm hγ₁
    intro hzero
    rw [hzero, mul_zero] at hsign
    linarith
  have hR₂One :
      (exceptionalEulerInverse m ε γ₂).eval 1 ≠ 0 := by
    have hsign :=
      negOnePow_mul_exceptionalEulerInverse_eval_one_pos
        m ε hm hγ₂
    intro hzero
    rw [hzero, mul_zero] at hsign
    linarith
  have hcoeff :
      a * (exceptionalEulerInverse m ε γ₁).eval 1 ≠ 0 ∨
        b * (exceptionalEulerInverse m ε γ₂).eval 1 ≠ 0 := by
    rcases hab with ha | hb
    · exact Or.inl (mul_ne_zero ha hR₁One)
    · exact Or.inr (mul_ne_zero hb hR₂One)
  have hKOne : K 1 = Q.eval 1 := by
    simpa only [K, Q] using
      exceptionalPencilExteriorDensity_one m ε γ₁ γ₂ a b
  have hα : -1 < (ε : ℝ) - 1 / 2 := by
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  have hparameterBound : ∀ {p : ℝ[X]}, p.natDegree < m →
      (ε : ℝ) + 1 / 2 + p.natDegree < γ₁ ∧
        (ε : ℝ) + 1 / 2 + p.natDegree < γ₂ := by
    intro p hp
    have hpOne : p.natDegree + 1 ≤ m := by lia
    have hpCast : (p.natDegree : ℝ) + 1 ≤ m := by
      exact_mod_cast hpOne
    constructor <;> linarith
  by_contra hcount
  have hcard :
      (Q.roots.filter fun r => 0 < r ∧ r < 1).card < m - 1 := by
    simpa only [Q] using Nat.lt_of_not_ge hcount
  have hPdeg : P.natDegree < m := by
    rw [show P = interiorRootProduct Q by rfl,
      natDegree_interiorRootProduct]
    lia
  have hPdegSucc : P.natDegree + 1 < m := by
    rw [show P = interiorRootProduct Q by rfl,
      natDegree_interiorRootProduct]
    lia
  have hPpos : ∀ x : ℝ, 1 < x → 0 < P.eval x := by
    intro x hx
    exact interiorRootProduct_eval_pos_of_one_le Q hx.le
  by_cases hzero : ∃ κ : ℝ, 1 < κ ∧ K κ = 0
  · obtain ⟨κ, hκ, hκzero⟩ := hzero
    let T : ℝ[X] := C κ - X
    let test := P * T
    have hTdeg : T.natDegree ≤ 1 := by
      dsimp only [T]
      simpa using natDegree_sub_le (C κ) X
    have htestDeg : test.natDegree < m := by
      calc
        test.natDegree ≤ P.natDegree + T.natDegree :=
          natDegree_mul_le
        _ ≤ P.natDegree + 1 := Nat.add_le_add_left hTdeg _
        _ < m := hPdegSucc
    have hTpos : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < T.eval x := by
      intro x hx0 hx1
      dsimp only [T]
      simp only [eval_sub, eval_C, eval_X]
      linarith
    have hInterior :
        0 < Q.eval 1 *
          (∫ x : ℝ in 0..1,
            (Q * test).eval x * x ^ ((ε : ℝ) - 1 / 2)) := by
      simpa only [test, T, P] using
        interiorRootProduct_signedIntegral_pos
          hQ hQOne hα (C κ - X) hTpos
    have hmoment :=
      exceptionalEulerInverse_pencil_signedMomentIdentity
        m ε (a := a) (b := b) test hγ₁ hγ₂ htestDeg
    have hbounds := hparameterBound htestDeg
    have hExtInt :=
      integrableOn_mul_exceptionalPencilExteriorDensity
        m ε (a := a) (b := b) test hbounds.1 hbounds.2
    let f : ℝ → ℝ := fun x =>
      Q.eval 1 * (test.eval x * K x)
    have hfNonneg : 0 ≤ᵐ[volume.restrict (Ioi 1)] f := by
      rw [Filter.EventuallyLE,
        MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with x hx
      by_cases hxκ : x = κ
      · subst x
        change 0 ≤ f κ
        dsimp only [f]
        rw [hκzero]
        simp
      · have hcross :=
          exceptionalPencilExteriorDensity_crossing_pos
            m ε hγ hκ hx hxκ hcoeff hκzero
        have hP := hPpos x hx
        dsimp only [f, test, T]
        simp only [eval_mul, eval_sub, eval_C, eval_X]
        rw [← hKOne]
        calc
          K 1 * (P.eval x * (κ - x) * K x) =
              P.eval x * (K 1 * ((κ - x) * K x)) := by ring
          _ ≥ 0 := (mul_pos hP hcross).le
    have hfInt : IntegrableOn f (Ioi 1) volume := by
      exact hExtInt.const_mul (Q.eval 1)
    have hsubset : Ioo (1 : ℝ) κ ⊆
        Function.support f ∩ Ioi 1 := by
      intro x hx
      have hxκ : x ≠ κ := ne_of_lt hx.2
      have hcross :=
        exceptionalPencilExteriorDensity_crossing_pos
          m ε hγ hκ hx.1 hxκ hcoeff hκzero
      have hP := hPpos x hx.1
      refine ⟨Function.mem_support.mpr ?_, hx.1⟩
      dsimp only [f, test, T]
      simp only [eval_mul, eval_sub, eval_C, eval_X]
      rw [← hKOne]
      have hpos :
          0 < K 1 * (P.eval x * (κ - x) * K x) := by
        calc
          K 1 * (P.eval x * (κ - x) * K x) =
              P.eval x * (K 1 * ((κ - x) * K x)) := by ring
          _ > 0 := mul_pos hP hcross
      exact hpos.ne'
    have hExterior :
        0 < Q.eval 1 *
          (∫ x in Ioi (1 : ℝ), test.eval x * K x) := by
      rw [← MeasureTheory.integral_const_mul]
      apply (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
        hfNonneg hfInt).mpr
      exact ((MeasureTheory.Measure.measure_Ioo_pos _).mpr hκ).trans_le
        (MeasureTheory.measure_mono hsubset)
    have hEq := congrArg (fun z : ℝ => Q.eval 1 * z) hmoment
    dsimp only [Q, K] at hmoment hEq
    nlinarith
  · have hKNo : ∀ x : ℝ, 1 < x → K x ≠ 0 := by
      intro x hx hKx
      exact hzero ⟨x, hx, hKx⟩
    let test : ℝ[X] := P
    have hInterior :
        0 < Q.eval 1 *
          (∫ x : ℝ in 0..1,
            (Q * test).eval x * x ^ ((ε : ℝ) - 1 / 2)) := by
      simpa only [test, P, mul_one] using
        interiorRootProduct_signedIntegral_pos
          hQ hQOne hα 1 (by simp)
    have hmoment :=
      exceptionalEulerInverse_pencil_signedMomentIdentity
        m ε (a := a) (b := b) test hγ₁ hγ₂ hPdeg
    have hbounds := hparameterBound hPdeg
    have hExtInt :=
      integrableOn_mul_exceptionalPencilExteriorDensity
        m ε (a := a) (b := b) test hbounds.1 hbounds.2
    have hKsame : ∀ x : ℝ, 1 < x → 0 < K 1 * K x := by
      intro x hx
      apply mul_pos_of_continuousOn_of_ne_zero hx.le
      · intro z hz
        exact (continuousAt_exceptionalPencilExteriorDensity
          m ε γ₁ γ₂ a b
            (one_pos.trans_le hz.1).ne').continuousWithinAt
      · intro z hz1 hzx
        by_cases hz : z = 1
        · simpa only [hz, hKOne] using hQOne
        · exact hKNo z (lt_of_le_of_ne hz1 (Ne.symm hz))
    have hExterior :
        0 < Q.eval 1 *
          (∫ x in Ioi (1 : ℝ), test.eval x * K x) := by
      rw [← MeasureTheory.integral_const_mul]
      apply setIntegral_pos_of_pos_Ioi
        (hExtInt.const_mul (Q.eval 1))
      intro x hx
      have hP := hPpos x hx
      have hsame := hKsame x hx
      dsimp only [test]
      rw [← hKOne]
      nlinarith
    have hEq := congrArg (fun z : ℝ => Q.eval 1 * z) hmoment
    dsimp only [Q, K] at hmoment hEq
    nlinarith

/-- A generic exceptional pencil member splits over `ℝ`.  The interior-root
product leaves a quotient of degree at most one. -/
theorem exceptionalEulerInverse_pencil_splits_of_eval_one_ne_zero
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (hm : 0 < m)
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hγ : γ₁ < γ₂) (hab : a ≠ 0 ∨ b ≠ 0)
    (hOne :
      (C a * exceptionalEulerInverse m ε γ₁ +
        C b * exceptionalEulerInverse m ε γ₂).eval 1 ≠ 0) :
    (C a * exceptionalEulerInverse m ε γ₁ +
      C b * exceptionalEulerInverse m ε γ₂).Splits := by
  let Q := C a * exceptionalEulerInverse m ε γ₁ +
    C b * exceptionalEulerInverse m ε γ₂
  let P := interiorRootProduct Q
  have hQOne : Q.eval 1 ≠ 0 := by
    simpa only [Q] using hOne
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hQOne
    rw [hzero]
    simp
  have hPdeg : m - 1 ≤ P.natDegree := by
    rw [show P = interiorRootProduct Q by rfl,
      natDegree_interiorRootProduct]
    simpa only [Q] using
      exceptionalEulerInverse_pencil_card_roots_Ioo_ge_sub_one
        m ε hm hγ₁ hγ₂ hγ hab hOne
  have hQdeg : Q.natDegree ≤ m := by
    dsimp only [Q]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le
        ((Polynomial.natDegree_C_mul_le a _).trans
          (natDegree_exceptionalEulerInverse_le m ε γ₁))
        ((Polynomial.natDegree_C_mul_le b _).trans
          (natDegree_exceptionalEulerInverse_le m ε γ₂)))
  obtain ⟨s, hfactor, -⟩ := exists_interiorRootComplement hQ
  have hP : P ≠ 0 := by
    dsimp only [P, interiorRootProduct]
    exact (Polynomial.monic_multisetProd_X_sub_C _).ne_zero
  have hs : s ≠ 0 := by
    apply right_ne_zero_of_mul
    rw [hfactor]
    exact hQ
  have hPsplit : P.Splits := by
    apply splits_of_card_roots
    rw [show P = interiorRootProduct Q by rfl, interiorRootProduct,
      Polynomial.roots_multiset_prod_X_sub_C,
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
  have hdegMul := Polynomial.natDegree_mul hP hs
  rw [hfactor] at hdegMul
  have hsdeg : s.natDegree ≤ 1 := by lia
  have hssplit : s.Splits :=
    (isRealRooted_of_natDegree_le_one hs hsdeg).2
  change Q.Splits
  rw [← hfactor]
  simpa only [P] using hPsplit.mul hssplit

private theorem exceptionalEulerInverse_pencil_splits_of_eval_one_eq_zero
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (hm : 0 < m)
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hγ : γ₁ < γ₂)
    (hOne :
      (C a * exceptionalEulerInverse m ε γ₁ +
        C b * exceptionalEulerInverse m ε γ₂).eval 1 = 0) :
    (C a * exceptionalEulerInverse m ε γ₁ +
      C b * exceptionalEulerInverse m ε γ₂).Splits := by
  let R := exceptionalEulerInverse m ε γ₁
  let Q := C a * R + C b * exceptionalEulerInverse m ε γ₂
  change Q.Splits
  by_cases hQ : Q = 0
  · rw [hQ]
    exact Polynomial.Splits.zero
  have hQOne : Q.eval 1 = 0 := by
    simpa only [Q, R] using hOne
  have hmCast : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hε : 0 ≤ (ε : ℝ) := by positivity
  have hγ₁pos : 0 < γ₁ := by linarith
  have hγ₂pos : 0 < γ₂ := by linarith
  have hQdegLower : m - 1 ≤ Q.natDegree := by
    simpa only [Q, R] using
      exceptionalEulerInverse_pencil_natDegree_ge_sub_one
        m ε hm hγ₁pos hγ₂pos hγ.ne hQ
  have hQdegUpper : Q.natDegree ≤ m := by
    dsimp only [Q, R]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le
        ((Polynomial.natDegree_C_mul_le a _).trans
          (natDegree_exceptionalEulerInverse_le m ε γ₁))
        ((Polynomial.natDegree_C_mul_le b _).trans
          (natDegree_exceptionalEulerInverse_le m ε γ₂)))
  have hR : R ≠ 0 := by
    intro hzero
    have hdegree := natDegree_exceptionalEulerInverse m ε hγ₁pos
    dsimp only [R] at hzero
    rw [hzero] at hdegree
    simp at hdegree
    lia
  have hQlc : Q.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hRlc : R.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hR
  let f := C Q.leadingCoeff⁻¹ * Q
  let g := C R.leadingCoeff⁻¹ * R
  have hfPos : HasPosLeadingCoeff f := by
    apply hasPosLeadingCoeff_of_monic
    dsimp only [f]
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ hQlc
  have hgPos : HasPosLeadingCoeff g := by
    apply hasPosLeadingCoeff_of_monic
    dsimp only [g]
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ hRlc
  have hfdeg : f.natDegree = Q.natDegree := by
    dsimp only [f]
    exact Polynomial.natDegree_C_mul (inv_ne_zero hQlc)
  have hgdeg : g.natDegree = m := by
    dsimp only [g, R]
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hRlc),
      natDegree_exceptionalEulerInverse m ε hγ₁pos]
  have hROne : R.eval 1 ≠ 0 := by
    have hsign :=
      negOnePow_mul_exceptionalEulerInverse_eval_one_pos
        m ε hm hγ₁
    dsimp only [R]
    intro hzero
    rw [hzero, mul_zero] at hsign
    linarith
  have hfamily : ∀ {μ : ℝ}, 0 < μ →
      ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits) := by
    intro μ hμ
    let a' := Q.leadingCoeff⁻¹ * a +
      μ * R.leadingCoeff⁻¹
    let b' := Q.leadingCoeff⁻¹ * b
    have hrewrite :
        f + C μ * g =
          C a' * exceptionalEulerInverse m ε γ₁ +
            C b' * exceptionalEulerInverse m ε γ₂ := by
      dsimp only [f, g, Q, R, a', b']
      ext k
      simp only [coeff_add, coeff_C_mul]
      ring
    have heval : (f + C μ * g).eval 1 =
        μ * R.leadingCoeff⁻¹ * R.eval 1 := by
      dsimp only [f, g]
      simp only [eval_add, eval_mul, eval_C]
      rw [hQOne]
      ring
    have hevalNe : (f + C μ * g).eval 1 ≠ 0 := by
      rw [heval]
      exact mul_ne_zero (mul_ne_zero hμ.ne' (inv_ne_zero hRlc)) hROne
    have hab' : a' ≠ 0 ∨ b' ≠ 0 := by
      by_contra hz
      simp only [not_or, not_ne_iff] at hz
      apply hevalNe
      rw [hrewrite, hz.1, hz.2]
      simp
    refine ⟨?_, ?_⟩
    · intro hzero
      apply hevalNe
      rw [hzero]
      simp
    · rw [hrewrite]
      apply exceptionalEulerInverse_pencil_splits_of_eval_one_ne_zero
        m ε hm hγ₁ hγ₂ hγ hab'
      simpa only [← hrewrite] using hevalNe
  have hfSplit : f.Splits := by
    by_cases hdegree : Q.natDegree = m
    · have hpos : PosComboRealRooted f g :=
        PosComboRealRooted.of_add_right hfamily
      exact (hpos.isRealRooted_left_of_sameDegree hfPos hgPos
        (by rw [hgdeg, hfdeg, hdegree])).2
    · apply splits_of_add_C_mul_family_of_succDegree hfamily hfPos hgPos
      rw [hgdeg, hfdeg]
      lia
  have hscaled := hfSplit.C_mul Q.leadingCoeff
  simpa only [f, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hQlc,
    C_1, one_mul] using hscaled

/-- Every exceptional signed-pencil member splits, including the zero member,
the endpoint-value boundary, and the unique possible degree drop. -/
theorem exceptionalEulerInverse_pencil_splits
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (hm : 0 < m)
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hγ : γ₁ < γ₂) :
    (C a * exceptionalEulerInverse m ε γ₁ +
      C b * exceptionalEulerInverse m ε γ₂).Splits := by
  by_cases hOne :
      (C a * exceptionalEulerInverse m ε γ₁ +
        C b * exceptionalEulerInverse m ε γ₂).eval 1 = 0
  · exact exceptionalEulerInverse_pencil_splits_of_eval_one_eq_zero
      m ε hm hγ₁ hγ₂ hγ hOne
  · have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra hz
      simp only [not_or, not_ne_iff] at hz
      apply hOne
      rw [hz.1, hz.2]
      simp
    exact exceptionalEulerInverse_pencil_splits_of_eval_one_ne_zero
      m ε hm hγ₁ hγ₂ hγ hab hOne

end ToricContribution
end ParkingFunctions
end RealRooted
