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

private theorem exceptionalPencilExteriorDensity_factor
    (m ε : ℕ) (γ₁ γ₂ a b : ℝ) {x : ℝ} (hx : 0 < x) :
    exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b x =
      x ^ ((ε : ℝ) + 1 / 2 - γ₂ - 1) *
        (a * (exceptionalEulerInverse m ε γ₁).eval 1 * x ^ (γ₂ - γ₁) +
          b * (exceptionalEulerInverse m ε γ₂).eval 1) := by
  rw [exceptionalPencilExteriorDensity,
    show (ε : ℝ) + 1 / 2 - γ₁ - 1 =
      ((ε : ℝ) + 1 / 2 - γ₂ - 1) + (γ₂ - γ₁) by ring,
    Real.rpow_add hx]
  ring

private theorem exceptionalEulerInverse_eval_one_ne_zero
    (m ε : ℕ) {γ : ℝ} (hm : 0 < m)
    (hγ : (ε : ℝ) + 1 / 2 + m - 1 < γ) :
    (exceptionalEulerInverse m ε γ).eval 1 ≠ 0 :=
  right_ne_zero_of_mul
    (negOnePow_mul_exceptionalEulerInverse_eval_one_pos m ε hm hγ).ne'

private theorem exceptionalPencil_natDegree_le
    (m ε : ℕ) (γ₁ γ₂ a b : ℝ) :
    (C a * exceptionalEulerInverse m ε γ₁ +
      C b * exceptionalEulerInverse m ε γ₂).natDegree ≤ m :=
  (Polynomial.natDegree_add_le _ _).trans
    (max_le
      ((Polynomial.natDegree_C_mul_le a _).trans
        (natDegree_exceptionalEulerInverse_le m ε γ₁))
      ((Polynomial.natDegree_C_mul_le b _).trans
        (natDegree_exceptionalEulerInverse_le m ε γ₂)))

private theorem left_ne_zero_of_mul_add_eq_zero
    {A B z : ℝ} (hcoeff : A ≠ 0 ∨ B ≠ 0) (hzero : A * z + B = 0) :
    A ≠ 0 := by
  grind

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
    simpa only [A, B, e, d] using
      exceptionalPencilExteriorDensity_factor m ε γ₁ γ₂ a b hxpos
  have hyFactor :
      exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b y =
        y ^ e * (A * y ^ d + B) := by
    simpa only [A, B, e, d] using
      exceptionalPencilExteriorDensity_factor m ε γ₁ γ₂ a b hypos
  have hxLinear : A * x ^ d + B = 0 := by
    rw [hxFactor] at hxzero
    exact (mul_eq_zero.mp hxzero).resolve_left
      (Real.rpow_pos_of_pos hxpos e).ne'
  intro hyzero
  have hyLinear : A * y ^ d + B = 0 := by
    rw [hyFactor] at hyzero
    exact (mul_eq_zero.mp hyzero).resolve_left
      (Real.rpow_pos_of_pos hypos e).ne'
  have hA : A ≠ 0 := left_ne_zero_of_mul_add_eq_zero hcoeff hxLinear
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
    simpa only [A, B, e, d] using
      exceptionalPencilExteriorDensity_factor m ε γ₁ γ₂ a b hz
  have hκLinear : A * κ ^ d + B = 0 := by
    rw [hfactor hκpos] at hκzero
    exact (mul_eq_zero.mp hκzero).resolve_left
      (Real.rpow_pos_of_pos hκpos e).ne'
  have hA : A ≠ 0 := left_ne_zero_of_mul_add_eq_zero hcoeff hκLinear
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
theorem shiftedJacobiFunctional_exceptionalPencil_mul_eq
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (p : ℝ[X])
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hp : p.natDegree < m) :
    shiftedJacobiFunctional ((ε : ℝ) - 1 / 2) 0
        ((C a * exceptionalEulerInverse m ε γ₁ +
          C b * exceptionalEulerInverse m ε γ₂) * p) =
      -(a * (exceptionalEulerInverse m ε γ₁).eval 1) *
          exceptionalExteriorFunctional
            ((ε : ℝ) + 1 / 2) γ₁ p -
        (b * (exceptionalEulerInverse m ε γ₂).eval 1) *
          exceptionalExteriorFunctional
            ((ε : ℝ) + 1 / 2) γ₂ p := by
  rw [add_mul, shiftedJacobiFunctional_add]
  rw [show C a * exceptionalEulerInverse m ε γ₁ * p =
      C a * (exceptionalEulerInverse m ε γ₁ * p) by ring,
    show C b * exceptionalEulerInverse m ε γ₂ * p =
      C b * (exceptionalEulerInverse m ε γ₂ * p) by ring,
    shiftedJacobiFunctional_C_mul,
    shiftedJacobiFunctional_C_mul,
    shiftedJacobiFunctional_exceptionalEulerInverse_mul_eq
      m ε p hγ₁ hp,
    shiftedJacobiFunctional_exceptionalEulerInverse_mul_eq
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
  have hfun : ∀ q : ℝ[X], (∫ x : ℝ in 0..1, q.eval x * x ^ ((ε : ℝ) - 1 / 2)) =
      shiftedJacobiFunctional ((ε : ℝ) - 1 / 2) 0 q := fun q => by
    rw [shiftedJacobiFunctional_eq_integral hα (by norm_num)]
    simp [shiftedJacobiIntegrand, shiftedJacobiWeight]
  rw [hfun]
  rw [shiftedJacobiFunctional_exceptionalPencil_mul_eq
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
      (q.roots.filter fun r => 0 < r ∧ r < 1).card :=
  Polynomial.natDegree_multiset_prod_X_sub_C_eq_card _

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
  have hs0 : s ≠ 0 := by grind
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
    simp [rootsI, hx0, hx1] at hcount
    have hsCount := Multiset.count_pos.mpr hsMem
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
  have hfactorEval (x : ℝ) : P.eval x * s.eval x = q.eval x := by
    simpa only [eval_mul] using
      congrArg (Polynomial.eval x) hfactor
  have hsOne : s.eval 1 ≠ 0 := by
    intro hsOne
    apply hqOne
    simpa only [hsOne, mul_zero] using (hfactorEval 1).symm
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
  have hf_eq : ∀ x, f x = P.eval 1 * P.eval x ^ 2 *
      (s.eval x * s.eval 1) * t.eval x * x ^ α := by
    intro x
    dsimp only [f]
    simp only [eval_mul]
    rw [← hfactorEval x, ← hfactorEval 1]
    ring
  have hfInt : IntervalIntegrable f volume 0 1 := by
    have h := intervalIntegrable_shiftedJacobiIntegrand hα (by norm_num : (-1 : ℝ) < 0)
      (C (q.eval 1) * (q * (P * t)))
    convert h using 1
    ext x
    simp only [f, shiftedJacobiIntegrand, shiftedJacobiWeight, eval_mul, eval_C,
      Real.rpow_zero, mul_one]
    ring
  have hfNonneg : 0 ≤ᵐ[volume.restrict (Set.uIoc 0 1)] f := by
    rw [Set.uIoc_of_le zero_le_one, Filter.EventuallyLE,
      MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    have hsPos := hsSame x hx.1 hx.2
    have hxpow : 0 < x ^ α := Real.rpow_pos_of_pos hx.1 α
    have htPos := ht x hx.1 hx.2
    rw [hf_eq]
    positivity
  obtain ⟨x, hx, havoid⟩ :=
    (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finset
      P.roots.toFinset
  have hPx : P.eval x ≠ 0 := by
    intro hPx
    apply havoid
    exact Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hP).mpr (by simpa only [Polynomial.IsRoot.def] using hPx))
  have hfx : 0 < f x := by
    have hsPos := hsSame x hx.1 hx.2.le
    have hxpow : 0 < x ^ α := Real.rpow_pos_of_pos hx.1 α
    have htPos := ht x hx.1 hx.2.le
    rw [hf_eq]
    positivity
  have hfCont : ContinuousAt f x := by
    dsimp only [f]
    exact continuousAt_const.mul
      ((q * (P * t)).continuousAt.mul
        (continuousAt_id.rpow_const (Or.inl hx.1.ne')))
  obtain ⟨a, b, hxab, hab⟩ := (hfCont.eventually_ne hfx.ne').exists_Ioo_subset
  let a' := max a 0
  let b' := min b 1
  have ha'x : a' < x := max_lt hxab.1 hx.1
  have hxb' : x < b' := lt_min hxab.2 hx.2
  have ha'b' : a' < b' := ha'x.trans hxb'
  have hsubset : Set.Ioo a' b' ⊆
      Function.support f ∩ Set.Ioc 0 1 := by
    intro y hy
    refine ⟨Function.mem_support.mpr (hab
      ⟨(le_max_left a 0).trans_lt hy.1, hy.2.trans_le (min_le_left b 1)⟩), ?_⟩
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
  have hQ : Q ≠ 0 := fun hzero => hQOne (by simp [hzero])
  have hR₁One := exceptionalEulerInverse_eval_one_ne_zero m ε hm hγ₁
  have hR₂One := exceptionalEulerInverse_eval_one_ne_zero m ε hm hγ₂
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
    have hpCast : (p.natDegree : ℝ) + 1 ≤ m := by
      exact_mod_cast (show p.natDegree + 1 ≤ m by lia)
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
  have hPpos : ∀ x : ℝ, 1 < x → 0 < P.eval x :=
    fun _ hx => interiorRootProduct_eval_pos_of_one_le Q hx.le
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
      simp only [T, eval_sub, eval_C, eval_X]
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
        simp [f, hκzero]
      · have hcross :=
          exceptionalPencilExteriorDensity_crossing_pos
            m ε hγ hκ hx hxκ hcoeff hκzero
        have hP := hPpos x hx
        dsimp only [f, test, T]
        simp only [eval_mul, eval_sub, eval_C, eval_X]
        rw [← hKOne]
        have hprod := mul_pos hP hcross
        dsimp only [K] at hprod ⊢
        ring_nf at hprod ⊢
        exact hprod.le
    have hfInt : IntegrableOn f (Ioi 1) volume :=
      hExtInt.const_mul (Q.eval 1)
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
      have hprod := mul_pos hP hcross
      dsimp only [K] at hprod ⊢
      ring_nf at hprod ⊢
      exact hprod.ne'
    have hExterior :
        0 < Q.eval 1 *
          (∫ x in Ioi (1 : ℝ), test.eval x * K x) := by
      rw [← MeasureTheory.integral_const_mul]
      apply (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
        hfNonneg hfInt).mpr
      exact ((MeasureTheory.Measure.measure_Ioo_pos _).mpr hκ).trans_le
        (MeasureTheory.measure_mono hsubset)
    have hEq := congrArg (fun z : ℝ => Q.eval 1 * z) hmoment
    dsimp only [Q, K] at hEq
    nlinarith
  · have hKNo : ∀ x : ℝ, 1 < x → K x ≠ 0 :=
      fun x hx hKx => hzero ⟨x, hx, hKx⟩
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
      apply mul_pos_of_forall_ne_zero_Icc hx.le
      · intro z hz
        exact (continuousAt_exceptionalPencilExteriorDensity
          m ε γ₁ γ₂ a b
            (one_pos.trans_le hz.1).ne').continuousWithinAt
      · intro z hzmem
        by_cases hz : z = 1
        · simpa only [hz, hKOne] using hQOne
        · exact hKNo z (lt_of_le_of_ne hzmem.1 (Ne.symm hz))
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
    dsimp only [Q, K] at hEq
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
  have hQ : Q ≠ 0 := fun hzero => hQOne (by simp [hzero])
  have hPdeg : m - 1 ≤ P.natDegree := by
    rw [show P = interiorRootProduct Q by rfl,
      natDegree_interiorRootProduct]
    simpa only [Q] using
      exceptionalEulerInverse_pencil_card_roots_Ioo_ge_sub_one
        m ε hm hγ₁ hγ₂ hγ hab hOne
  have hQdeg : Q.natDegree ≤ m := by
    simpa only [Q] using exceptionalPencil_natDegree_le m ε γ₁ γ₂ a b
  obtain ⟨s, hfactor, -⟩ := exists_interiorRootComplement hQ
  have hP : P ≠ 0 := by
    exact (Polynomial.monic_multisetProd_X_sub_C _).ne_zero
  have hs : s ≠ 0 := by
    apply right_ne_zero_of_mul
    rw [hfactor]
    exact hQ
  have hPsplit : P.Splits := by
    apply Polynomial.splits_iff_card_roots.mpr
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
    simpa only [Q, R] using exceptionalPencil_natDegree_le m ε γ₁ γ₂ a b
  have hROne : R.eval 1 ≠ 0 := by
    simpa only [R] using exceptionalEulerInverse_eval_one_ne_zero m ε hm hγ₁
  have hR : R ≠ 0 := fun hzero => hROne (by simp [hzero])
  have hQlc : Q.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hRlc : R.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hR
  let f := C Q.leadingCoeff⁻¹ * Q
  let g := C R.leadingCoeff⁻¹ * R
  have hfPos : HasPosLeadingCoeff f := by
    apply hasPosLeadingCoeff_of_monic
    dsimp only [f]
    exact monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hQlc)
  have hgPos : HasPosLeadingCoeff g := by
    apply hasPosLeadingCoeff_of_monic
    dsimp only [g]
    exact monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hRlc)
  have hfdeg : f.natDegree = Q.natDegree := by
    dsimp only [f]
    exact Polynomial.natDegree_C_mul (inv_ne_zero hQlc)
  have hgdeg : g.natDegree = m := by
    dsimp only [g, R]
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hRlc),
      natDegree_exceptionalEulerInverse m ε hγ₁pos]
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
    refine ⟨fun hzero => hevalNe (by simp [hzero]), ?_⟩
    rw [hrewrite]
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
