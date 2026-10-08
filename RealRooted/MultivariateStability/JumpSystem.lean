import RealRooted.MultivariateStability
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Analysis.Complex.AbsMax

/-!
# Supports of real stable polynomials are jump systems

P. Brändén, "Polynomials with the half-plane property and matroid theory", Adv. Math. 216
(2007), Theorem 3.2: the support of a real stable polynomial is a jump system
(`RealRooted.MvRealStable.isJumpSystem_supportInt`), in the sense of the Bouchet–Cunningham
two-step axiom (`RealRooted.IsJumpSystem`).

The proof uses that stability is preserved under partial derivatives (Gauss–Lucas), under
the inversion `z_j ↦ -1 / z_j` combined with multiplication by `z_j ^ D`, under truncation
in one variable, and under passing to the lowest weighted-homogeneous part (a Hurwitz-type
step proved by scaling).  These reduce the two-step axiom to a box between the two support
points, where a homogeneous part of degree at least three would have a zero in the product of
upper half-planes.

The proof was found with the Aristotle prover and adapted to the current Mathlib API.
-/

/-!
## Basic facts about real stable polynomials
-/


open MvPolynomial

namespace RealRooted.JumpSystem

variable {n : ℕ}

/-- Real stability (same as `JumpSystem.IsRealStable`). -/
def Stable (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ z : Fin n → ℂ, (∀ i, 0 < (z i).im) → eval z (map (algebraMap ℝ ℂ) p) ≠ 0

lemma eval_map_eq_sum (z : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ) :
    eval z (map (algebraMap ℝ ℂ) p) = ∑ d ∈ p.support, ((p.coeff d : ℝ) : ℂ) * ∏ i, z i ^ d i := by
  rw [eval_map, eval₂_eq']
  rfl

lemma eval_map_eq_sum_of_subset (z : Fin n → ℂ) {q : MvPolynomial (Fin n) ℝ}
    {S : Finset (Fin n →₀ ℕ)} (hS : q.support ⊆ S) :
    eval z (map (algebraMap ℝ ℂ) q) = ∑ d ∈ S, ((q.coeff d : ℝ) : ℂ) * ∏ i, z i ^ d i := by
  rw [eval_map_eq_sum]
  refine Finset.sum_subset hS fun d _ hd => ?_
  rw [notMem_support_iff.mp hd]
  simp

lemma Stable.ne_zero {p : MvPolynomial (Fin n) ℝ} (hp : Stable p) : p ≠ 0 := by
  rintro rfl
  exact hp (fun _ => Complex.I) (fun _ => by simp) (by simp)

lemma exists_pos_eval_ne_zero {p : MvPolynomial (Fin n) ℝ} (hp : p ≠ 0) :
    ∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ eval x p ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hp
  apply funext_set (fun _ => Set.Ioi (0:ℝ)) (fun _ => Set.Ioi_infinite 0)
  intro x hx
  simp only [map_zero]
  exact hcon x (fun i => hx i (Set.mem_univ i))

lemma exists_upper_root (N : ℕ) (hN : 3 ≤ N) (w : ℝ) (hw : w ≠ 0) :
    ∃ ζ : ℂ, 0 < ζ.im ∧ ζ ^ N = w := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hNpos : (0 : ℝ) < N := by positivity
  have key : ∀ (r θ : ℝ), 0 < r → 0 < θ → θ < Real.pi →
      0 < (((r ^ ((N : ℝ)⁻¹) : ℝ) : ℂ) * Complex.exp (θ * Complex.I)).im := by
    intro r θ hr h1 h2
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    exact mul_pos (Real.rpow_pos_of_pos hr _) (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  have hpow : ∀ (r θ : ℝ), 0 ≤ r →
      ((((r ^ ((N : ℝ)⁻¹) : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) ^ N
        = (r : ℂ) * Complex.exp ((N * θ : ℝ) * Complex.I)) := by
    intro r θ hr
    rw [mul_pow, ← Complex.ofReal_pow, Real.rpow_inv_natCast_pow hr (by lia),
      ← Complex.exp_nat_mul]
    congr 2
    push_cast; ring
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · refine ⟨_, key (-w) (Real.pi / N) (by linarith) (by positivity) ?_, ?_⟩
    · rw [div_lt_iff₀ hNpos]; nlinarith [Real.pi_pos]
    · rw [hpow _ _ (by linarith)]
      have : ((N : ℝ) * (Real.pi / N) : ℝ) = Real.pi := by field_simp
      rw [this, Complex.exp_pi_mul_I]; push_cast; ring
  · refine ⟨_, key w (2 * Real.pi / N) hpos (by positivity) ?_, ?_⟩
    · rw [div_lt_iff₀ hNpos]; nlinarith [Real.pi_pos]
    · rw [hpow _ _ hpos.le]
      have : ((N : ℝ) * (2 * Real.pi / N) : ℝ) = 2 * Real.pi := by field_simp
      rw [this]; push_cast; rw [Complex.exp_two_pi_mul_I]; ring

end RealRooted.JumpSystem



/-!
## Initial forms of stable polynomials are stable (Hurwitz-type argument)
-/


open MvPolynomial

namespace RealRooted.JumpSystem

variable {n : ℕ}

lemma prod_zpow_eq_zpow_sum {t : ℂ} (ht : t ≠ 0) {ι : Type*} (s : Finset ι) (a : ι → ℤ) :
    ∏ j ∈ s, t ^ a j = t ^ (∑ j ∈ s, a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add₀ ht]

lemma weight_eq_sum (w : Fin n → ℤ) (d : Fin n →₀ ℕ) :
    Finsupp.weight w d = ∑ j, (d j : ℤ) * w j := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp

/-- The lowest weighted-homogeneous part (initial form) of a stable polynomial with respect to an
integer weight vector is stable. -/
theorem Stable.weightedHomogeneousComponent {p : MvPolynomial (Fin n) ℝ} (hp : Stable p)
    (w : Fin n → ℤ) (m : ℤ) (hmin : ∀ d ∈ p.support, m ≤ Finsupp.weight w d)
    (hex : ∃ d ∈ p.support, Finsupp.weight w d = m) :
    Stable (weightedHomogeneousComponent w m p) := by
  classical
  intro z0 hz0 hzero
  set F := MvPolynomial.weightedHomogeneousComponent w m p with hFdef
  have hcoeffF : ∀ d, F.coeff d = if Finsupp.weight w d = m then p.coeff d else 0 := by
    intro d; rw [hFdef, coeff_weightedHomogeneousComponent]
  have hsubF : F.support ⊆ p.support := by
    intro d hd
    rw [mem_support_iff, hcoeffF] at hd
    split_ifs at hd
    · exact mem_support_iff.mpr hd
    · exact absurd rfl hd
  obtain ⟨d0, hd0, hd0w⟩ := hex
  have hF0 : map (algebraMap ℝ ℂ) F ≠ 0 := by
    intro h
    have := congrArg (fun q => q.coeff d0) h
    simp only [coeff_map, hcoeffF, ite_eq_left hd0w, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] at this
    exact mem_support_iff.mp hd0 (by simpa using this)
  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℂ, eval y (map (algebraMap ℝ ℂ) F) ≠ 0 := by
    by_contra h
    push Not at h
    exact hF0 (MvPolynomial.funext fun x => by simp [h x])
  set v : Fin n → ℂ := y - z0 with hv
  -- the deformation `H t u = t ^ (-m) * p (t ^ w * (z0 + u v))`
  set e : (Fin n →₀ ℕ) → ℕ := fun d => (Finsupp.weight w d - m).toNat with he
  set H : ℝ → ℂ → ℂ := fun t u => ∑ d ∈ p.support,
    ((p.coeff d : ℝ) : ℂ) * (t : ℂ) ^ e d * ∏ j, (z0 j + u * v j) ^ d j with hH
  set g : ℂ → ℂ := fun u => eval (fun j => z0 j + u * v j) (map (algebraMap ℝ ℂ) F) with hg
  have hH0 : ∀ u, H 0 u = g u := by
    intro u
    simp only [hH, hg]
    rw [eval_map_eq_sum_of_subset _ hsubF]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [hcoeffF]
    have hmd := hmin d hd
    by_cases hdw : Finsupp.weight w d = m
    · have : e d = 0 := by simp [he, hdw]
      rw [ite_eq_left hdw, this]; simp
    · have : e d ≠ 0 := by simp only [he]; lia
      rw [ite_eq_right hdw]
      simp [zero_pow this]
  have hHpos : ∀ t : ℝ, 0 < t → ∀ u, ((t : ℂ) ^ m) * H t u =
      eval (fun j => (t : ℂ) ^ w j * (z0 j + u * v j)) (map (algebraMap ℝ ℂ) p) := by
    intro t ht u
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    simp only [hH]
    rw [eval_map_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hmd := hmin d hd
    have hpow : (t : ℂ) ^ m * (t : ℂ) ^ e d = ∏ j, ((t : ℂ) ^ w j) ^ d j := by
      rw [← zpow_natCast, ← zpow_add₀ ht0]
      simp_rw [← zpow_natCast, ← zpow_mul]
      rw [prod_zpow_eq_zpow_sum ht0]
      congr 1
      rw [show ∑ j, w j * (d j : ℤ) = Finsupp.weight w d by
        rw [weight_eq_sum]; simp only [mul_comm]]
      simp only [he]
      rw [Int.toNat_of_nonneg (by lia)]
      ring
    rw [show ∏ j, ((t : ℂ) ^ w j * (z0 j + u * v j)) ^ d j =
        (∏ j, ((t : ℂ) ^ w j) ^ d j) * ∏ j, (z0 j + u * v j) ^ d j by
      rw [← Finset.prod_mul_distrib]; simp [mul_pow], ← hpow]
    ring
  have hcont : Continuous fun q : ℝ × ℂ => H q.1 q.2 := by
    simp only [hH]
    fun_prop
  have hdiff : ∀ t, Differentiable ℂ (H t) := by
    intro t
    simp only [hH]
    fun_prop
  -- isolated zeros of `g`
  have hg0 : g 0 = 0 := by simpa [hg] using hzero
  have hg1 : g 1 ≠ 0 := by
    simp only [hg, one_mul, hv, Pi.sub_apply, add_sub_cancel]
    exact hy
  have hgan : AnalyticAt ℂ g 0 := by
    have : g = H 0 := by funext u; exact (hH0 u).symm
    rw [this]
    exact (hdiff 0).analyticAt 0
  obtain ⟨r0, hr0, hr0g⟩ : ∃ r0 > 0, ∀ u : ℂ, u ≠ 0 → ‖u‖ < r0 → g u ≠ 0 := by
    rcases hgan.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have hgA : AnalyticOnNhd ℂ g Set.univ := by
        have : g = H 0 := by funext u; exact (hH0 u).symm
        rw [this]
        exact fun u _ => (hdiff 0).analyticAt u
      have := hgA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (Set.mem_univ 0) h (Set.mem_univ 1)
      exact hg1 this
    · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
      obtain ⟨ε, hε, hεg⟩ := h
      exact ⟨ε, hε, fun u hu hu' => hεg (by simpa using hu') hu⟩
  -- a neighbourhood of `0` where `z0 + u v` stays in the upper half-plane
  obtain ⟨r1, hr1, hr1U⟩ : ∃ r1 > 0, ∀ u : ℂ, ‖u‖ < r1 → ∀ j, 0 < (z0 j + u * v j).im := by
    have hopen : IsOpen {u : ℂ | ∀ j, 0 < (z0 j + u * v j).im} := by
      rw [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun j =>
        isOpen_lt continuous_const (by fun_prop)
    have hmem : (0 : ℂ) ∈ {u : ℂ | ∀ j, 0 < (z0 j + u * v j).im} := by simpa using hz0
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
    exact ⟨ε, hε, fun u hu => hball (by simpa using hu)⟩
  set r := min r0 r1 / 2 with hr
  have hrpos : 0 < r := by positivity
  have hrr0 : r < r0 := by rw [hr]; have := min_le_left r0 r1; linarith
  have hrr1 : r < r1 := by rw [hr]; have := min_le_right r0 r1; linarith
  -- uniform control on the sphere for small `t`
  have htube : ∀ᶠ t in nhds (0 : ℝ), ∀ u ∈ Metric.sphere (0 : ℂ) r,
      2 * ‖H t 0‖ < ‖H t u‖ := by
    apply (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually
    intro u0 hu0
    have hu0' : ‖u0‖ = r := by simpa using hu0
    have hlt : 2 * ‖H 0 0‖ < ‖H 0 u0‖ := by
      rw [hH0, hH0, hg0, norm_zero, mul_zero, norm_pos_iff]
      exact hr0g u0 (by intro h; rw [h, norm_zero] at hu0'; linarith) (by linarith)
    have c1 : Continuous fun q : ℝ × ℂ => 2 * ‖H q.1 0‖ :=
      continuous_const.mul (hcont.comp (continuous_fst.prodMk continuous_const)).norm
    have c2 : Continuous fun q : ℝ × ℂ => ‖H q.1 q.2‖ := hcont.norm
    exact c1.continuousAt.eventually_lt c2.continuousAt hlt
  obtain ⟨δ, hδ, hδt⟩ := Metric.eventually_nhds_iff.mp htube
  set t := δ / 2 with ht
  have htpos : 0 < t := by positivity
  have hts := hδt (show dist t 0 < δ by rw [Real.dist_eq, sub_zero, abs_of_pos htpos]; linarith)
  -- `H t` has no zeros on the closed ball
  have hHne : ∀ u ∈ Metric.closedBall (0 : ℂ) r, H t u ≠ 0 := by
    intro u hu h
    have hu' : ‖u‖ < r1 := by
      have : ‖u‖ ≤ r := by simpa using hu
      linarith
    have := hHpos t htpos u
    rw [h, mul_zero] at this
    refine hp _ (fun j => ?_) this.symm
    rw [← Complex.ofReal_zpow, Complex.im_ofReal_mul]
    exact mul_pos (zpow_pos htpos _) (hr1U u hu' j)
  have hH0ne : H t 0 ≠ 0 := hHne 0 (Metric.mem_closedBall_self hrpos.le)
  -- maximum modulus principle for `1 / H t`
  have hdcc : DiffContOnCl ℂ (fun u => (H t u)⁻¹) (Metric.ball (0 : ℂ) r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hrpos.ne']
    exact ((hdiff t).differentiableOn).inv hHne
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdcc
    (C := (2 * ‖H t 0‖)⁻¹) (fun u hu => by
      rw [frontier_ball _ hrpos.ne'] at hu
      rw [norm_inv]
      have hpos : 0 < 2 * ‖H t 0‖ := by positivity
      exact (inv_le_inv₀ (lt_trans hpos (hts u hu)) hpos).mpr (hts u hu).le)
    (subset_closure (Metric.mem_ball_self hrpos))
  rw [norm_inv] at hmax
  have hpos : 0 < ‖H t 0‖ := norm_pos_iff.mpr hH0ne
  rw [inv_le_inv₀ hpos (by positivity)] at hmax
  linarith

end RealRooted.JumpSystem



/-!
## Partial derivatives of stable polynomials are stable
-/


open MvPolynomial

namespace RealRooted.JumpSystem

variable {n : ℕ}

lemma coeff_pderiv' (j : Fin n) (p : MvPolynomial (Fin n) ℝ) (e : Fin n →₀ ℕ) :
    (pderiv j p).coeff e = p.coeff (e + Finsupp.single j 1) * (e j + 1) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases hs : s = e + Finsupp.single j 1
    · subst hs
      simp
    · rw [ite_eq_right hs, zero_mul]
      split_ifs with h
      · have : s j = 0 := by
          by_contra hsj
          apply hs
          rw [← h]
          ext l
          by_cases hl : l = j
          · subst hl; simp; lia
          · simp [Finsupp.single_eq_of_ne hl]
        simp [this]
      · rfl
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, add_mul]

lemma mem_support_pderiv (j : Fin n) (p : MvPolynomial (Fin n) ℝ) (e : Fin n →₀ ℕ) :
    e ∈ (pderiv j p).support ↔ e + Finsupp.single j 1 ∈ p.support := by
  rw [mem_support_iff, mem_support_iff, coeff_pderiv']
  have : ((e j : ℝ) + 1) ≠ 0 := by positivity
  constructor
  · intro h h'; exact h (by rw [h', zero_mul])
  · intro h h'; exact h ((mul_eq_zero.mp h').resolve_right this)

lemma prod_ite_factor (j : Fin n) (x : ℂ) (y : Fin n → ℂ) :
    ∏ l, (if l = j then x else y l) = x * ∏ l, (if l = j then 1 else y l) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ (fun l => if l = j then 1 else y l) (Finset.mem_univ j)]
  simp only [ite_eq_left, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [ite_eq_right (Finset.ne_of_mem_erase hl), ite_eq_right (Finset.ne_of_mem_erase hl)]

/-- The univariate polynomial `t ↦ q(z₁, …, t, …, zₙ)` (with `t` in slot `j`). -/
noncomputable def univPoly (z : Fin n → ℂ) (j : Fin n) (q : MvPolynomial (Fin n) ℝ) :
    Polynomial ℂ :=
  ∑ d ∈ q.support, Polynomial.C (((q.coeff d : ℝ) : ℂ) *
    ∏ l, (if l = j then 1 else z l ^ d l)) * Polynomial.X ^ (d j)

lemma prod_update_pow (z : Fin n → ℂ) (j : Fin n) (t : ℂ) (d : Fin n →₀ ℕ) :
    ∏ l, Function.update z j t l ^ d l = t ^ d j * ∏ l, (if l = j then 1 else z l ^ d l) := by
  rw [← prod_ite_factor]
  refine Finset.prod_congr rfl fun l _ => ?_
  by_cases hl : l = j
  · subst hl; simp
  · simp [hl]

lemma eval_univPoly (z : Fin n → ℂ) (j : Fin n) (q : MvPolynomial (Fin n) ℝ) (t : ℂ) :
    (univPoly z j q).eval t = eval (Function.update z j t) (map (algebraMap ℝ ℂ) q) := by
  rw [univPoly, Polynomial.eval_finsetSum, eval_map_eq_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    prod_update_pow]
  ring

lemma eval_derivative_univPoly (z : Fin n → ℂ) (j : Fin n) (q : MvPolynomial (Fin n) ℝ) :
    (Polynomial.derivative (univPoly z j q)).eval (z j) =
      eval z (map (algebraMap ℝ ℂ) (pderiv j q)) := by
  conv_rhs => rw [q.as_sum]
  rw [univPoly, map_sum, map_sum, map_sum, map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Polynomial.derivative_C_mul_X_pow, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, pderiv_monomial, map_monomial, eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => by simp)]
  have : ∏ l, z l ^ ((d - Finsupp.single j 1 : Fin n →₀ ℕ) l) =
      z j ^ (d j - 1) * ∏ l, (if l = j then 1 else z l ^ d l) := by
    rw [← prod_ite_factor]
    refine Finset.prod_congr rfl fun l _ => ?_
    by_cases hl : l = j
    · subst hl; simp
    · simp [hl, Finsupp.single_eq_of_ne hl]
  rw [this]
  simp only [map_mul, map_natCast, Complex.coe_algebraMap]
  ring

theorem Stable.pderiv {p : MvPolynomial (Fin n) ℝ} (hp : Stable p) (j : Fin n)
    (hne : pderiv j p ≠ 0) : Stable (pderiv j p) := by
  classical
  intro z hz hzero
  have hp0 := hp.ne_zero
  -- the degree of `p` in `z_j`
  set D := p.support.sup (fun d => d j) with hD
  have hDle : ∀ d ∈ p.support, d j ≤ D := fun d hd => Finset.le_sup (f := fun d => d j) hd
  obtain ⟨dmax, hdmax, hdmaxD⟩ := Finset.exists_mem_eq_sup p.support
    (Finset.nonempty_iff_ne_empty.mpr (support_eq_empty.not.mpr hp0)) (fun d => d j)
  have hD1 : 1 ≤ D := by
    obtain ⟨e, he⟩ : (MvPolynomial.pderiv j p).support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (support_eq_empty.not.mpr hne)
    have := hDle _ ((mem_support_pderiv j p e).1 he)
    simp at this
    lia
  -- the top part in `z_j` is stable
  set w : Fin n → ℤ := fun l => if l = j then -1 else 0 with hw
  have hweight : ∀ d : Fin n →₀ ℕ, Finsupp.weight w d = -(d j : ℤ) := by
    intro d
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
    simp [hw]
  have hPtop := hp.weightedHomogeneousComponent w (-(D : ℤ))
    (fun d hd => by rw [hweight]; have := hDle d hd; lia)
    ⟨dmax, hdmax, by rw [hweight, hD, hdmaxD]⟩
  set Ptop := MvPolynomial.weightedHomogeneousComponent w (-(D : ℤ)) p with hPtopdef
  -- the top coefficient of the univariate restriction is nonzero
  set f := univPoly z j p with hf
  have hcoeffD : f.coeff D ≠ 0 := by
    have hzI : ∀ l, 0 < (Function.update z j Complex.I l).im := by
      intro l
      by_cases hl : l = j
      · subst hl; simp
      · simpa [hl] using hz l
    have h1 := hPtop _ hzI
    have hsub : Ptop.support ⊆ p.support := by
      intro d hd
      rw [mem_support_iff, hPtopdef, coeff_weightedHomogeneousComponent] at hd
      split_ifs at hd
      · exact mem_support_iff.mpr hd
      · exact absurd rfl hd
    rw [eval_map_eq_sum_of_subset _ hsub] at h1
    have h2 : ∑ d ∈ p.support, ((Ptop.coeff d : ℝ) : ℂ) *
        ∏ i, Function.update z j Complex.I i ^ d i = Complex.I ^ D * f.coeff D := by
      rw [hf, univPoly, Polynomial.finsetSum_coeff, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Polynomial.coeff_C_mul_X_pow, hPtopdef, coeff_weightedHomogeneousComponent,
        hweight, prod_update_pow]
      by_cases hdj : d j = D
      · rw [ite_eq_left (by lia), ite_eq_left hdj.symm, hdj]; ring
      · rw [ite_eq_right (by lia), ite_eq_right (Ne.symm hdj)]; simp
    rw [h2] at h1
    exact right_ne_zero_of_mul h1
  have hdeg : D ≤ f.natDegree := Polynomial.le_natDegree_of_ne_zero hcoeffD
  have hdegpos : 0 < f.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos]; lia
  -- Gauss–Lucas
  have hderiv0 : Polynomial.derivative f ≠ 0 := by
    intro h
    have := Polynomial.derivative_eq_zero.mp h
    lia
  have hroot : z j ∈ (Polynomial.derivative f).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    refine ⟨hderiv0, ?_⟩
    rw [Polynomial.coe_aeval_eq_eval, hf, eval_derivative_univPoly]
    exact hzero
  have hGL := Polynomial.rootSet_derivative_subset_convexHull_rootSet hdegpos hroot
  have hroots : f.rootSet ℂ ⊆ {w : ℂ | w.im ≤ 0} := by
    intro r hr
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval, hf, eval_univPoly] at hr
    by_contra hcon
    simp only [Set.mem_ofPred_eq, not_le] at hcon
    apply hp _ _ hr.2
    intro l
    by_cases hl : l = j
    · subst hl; simpa using hcon
    · simpa [hl] using hz l
  have hconv : Convex ℝ {w : ℂ | w.im ≤ 0} :=
    convex_halfSpace_le Complex.imLm.isLinear 0
  have := convexHull_min hroots hconv hGL
  simp only [Set.mem_ofPred_eq] at this
  linarith [hz j]

theorem exists_shift {p : MvPolynomial (Fin n) ℝ} (hp : Stable p) (j : Fin n) (k : ℕ)
    (hne : ∃ d ∈ p.support, k ≤ d j) :
    ∃ q : MvPolynomial (Fin n) ℝ, Stable q ∧
      ∀ e, e ∈ q.support ↔ e + Finsupp.single j k ∈ p.support := by
  induction k with
  | zero => exact ⟨p, hp, fun e => by simp⟩
  | succ k ih =>
    obtain ⟨d, hd, hkd⟩ := hne
    obtain ⟨q, hq, hqs⟩ := ih ⟨d, hd, by lia⟩
    have hsupp : ∀ e, e ∈ (pderiv j q).support ↔ e + Finsupp.single j (k + 1) ∈ p.support := by
      intro e
      rw [mem_support_pderiv, hqs, add_assoc, ← Finsupp.single_add, add_comm 1 k]
    refine ⟨pderiv j q, hq.pderiv j ?_, hsupp⟩
    intro h0
    have hmem := (hsupp (d - Finsupp.single j (k + 1))).2 (by
      rwa [tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hkd)])
    rw [h0] at hmem
    simp at hmem

end RealRooted.JumpSystem



/-!
## Inversion `z_j ↦ -1/z_j` and truncation
-/


open MvPolynomial

namespace RealRooted.JumpSystem

variable {n : ℕ}

/-- `z_j ^ D * p(z_1, …, -1/z_j, …, z_n)`. -/
noncomputable def invertAt (j : Fin n) (D : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ d ∈ p.support, monomial (Finsupp.update d j (D - d j)) ((-1) ^ (d j) * p.coeff d)

lemma update_update_reflect {d : Fin n →₀ ℕ} {j : Fin n} {D : ℕ} (h : d j ≤ D) :
    Finsupp.update (Finsupp.update d j (D - d j)) j (D - (Finsupp.update d j (D - d j)) j) = d := by
  ext l
  by_cases hl : l = j
  · subst hl; simp; lia
  · simp [Finsupp.update_apply, hl]

lemma coeff_invert {p : MvPolynomial (Fin n) ℝ} {j : Fin n} {D : ℕ}
    (hD : ∀ d ∈ p.support, d j ≤ D) (e : Fin n →₀ ℕ) :
    (invertAt j D p).coeff e = if e j ≤ D then
      (-1) ^ (D - e j) * p.coeff (Finsupp.update e j (D - e j)) else 0 := by
  classical
  unfold invertAt
  rw [coeff_sum]
  simp only [coeff_monomial]
  have key : ∀ d ∈ p.support, (Finsupp.update d j (D - d j) = e ↔
      (e j ≤ D ∧ Finsupp.update e j (D - e j) = d)) := by
    intro d hd
    constructor
    · rintro rfl
      refine ⟨by simp, update_update_reflect (hD d hd)⟩
    · rintro ⟨he, rfl⟩
      exact update_update_reflect he
  by_cases he : e j ≤ D
  · rw [ite_eq_left he]
    rw [Finset.sum_congr rfl (fun d hd => by rw [if_congr (key d hd) rfl rfl])]
    simp only [he, true_and]
    rw [Finset.sum_ite_eq]
    split_ifs with hmem
    · simp
    · rw [notMem_support_iff.mp hmem, mul_zero]
  · rw [ite_eq_right he]
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [ite_eq_right]
    rw [key d hd]
    exact fun h => he h.1

lemma mem_support_invert {p : MvPolynomial (Fin n) ℝ} {j : Fin n} {D : ℕ}
    (hD : ∀ d ∈ p.support, d j ≤ D) (e : Fin n →₀ ℕ) :
    e ∈ (invertAt j D p).support ↔ e j ≤ D ∧ Finsupp.update e j (D - e j) ∈ p.support := by
  rw [mem_support_iff, coeff_invert hD]
  split_ifs with he
  · simp [he, mem_support_iff]
  · simp [he]

theorem Stable.invert {p : MvPolynomial (Fin n) ℝ} (hp : Stable p) {j : Fin n} {D : ℕ}
    (hD : ∀ d ∈ p.support, d j ≤ D) : Stable (invertAt j D p) := by
  intro z hz
  have hzj : z j ≠ 0 := fun h => by have := hz j; rw [h] at this; simp at this
  set w : ℂ := -1 / z j with hw
  have hwim : 0 < w.im := by
    rw [hw, neg_div, Complex.neg_im, Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, zero_mul, one_mul, zero_div]
    rw [zero_sub, neg_neg]
    exact div_pos (hz j) (Complex.normSq_pos.mpr hzj)
  have hz' : ∀ l, 0 < (Function.update z j w l).im := by
    intro l
    by_cases hl : l = j
    · subst hl; simpa using hwim
    · simpa [Function.update_apply, hl] using hz l
  have heval : eval z (map (algebraMap ℝ ℂ) (invertAt j D p)) =
      z j ^ D * eval (Function.update z j w) (map (algebraMap ℝ ℂ) p) := by
    rw [eval_map_eq_sum _ p, Finset.mul_sum]
    unfold invertAt
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [map_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp)]
    have hdj := hD d hd
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    have hrest : ∏ x ∈ Finset.univ.erase j, z x ^ (Finsupp.update d j (D - d j)) x =
        ∏ x ∈ Finset.univ.erase j, Function.update z j w x ^ d x := by
      refine Finset.prod_congr rfl fun l hl => ?_
      have hl' := Finset.ne_of_mem_erase hl
      simp [Finsupp.update_apply, hl']
    rw [hrest]
    simp only [Finsupp.update_apply, ite_eq_left, Function.update_self, map_mul, map_pow, map_neg,
      map_one]
    rw [hw, div_pow, neg_one_pow_eq_pow_mod_two]
    have : z j ^ D = z j ^ (D - d j) * z j ^ d j := by rw [← pow_add]; congr 1; lia
    rw [this]
    field_simp
    rw [mul_comm]
    rfl
  rw [heval]
  exact mul_ne_zero (pow_ne_zero _ hzj) (hp _ hz')

theorem exists_reflect {p : MvPolynomial (Fin n) ℝ} (hp : Stable p) (j : Fin n) (D : ℕ)
    (hD : ∀ d ∈ p.support, d j ≤ D) :
    ∃ q : MvPolynomial (Fin n) ℝ, Stable q ∧
      ∀ e, e ∈ q.support ↔ e j ≤ D ∧ Finsupp.update e j (D - e j) ∈ p.support :=
  ⟨_, hp.invert hD, mem_support_invert hD⟩

theorem exists_trunc {p : MvPolynomial (Fin n) ℝ} (hp : Stable p) (j : Fin n) (h : ℕ)
    (hne : ∃ d ∈ p.support, d j ≤ h) :
    ∃ q : MvPolynomial (Fin n) ℝ, Stable q ∧ ∀ e, e ∈ q.support ↔ e j ≤ h ∧ e ∈ p.support := by
  classical
  obtain ⟨d0, hd0, hd0h⟩ := hne
  set D := max h (p.support.sup fun d => d j) with hDdef
  have hD : ∀ d ∈ p.support, d j ≤ D := fun d hd =>
    le_max_of_le_right (Finset.le_sup (f := fun d => d j) hd)
  have hhD : h ≤ D := le_max_left _ _
  obtain ⟨q1, hq1, hq1s⟩ := exists_reflect hp j D hD
  obtain ⟨q2, hq2, hq2s⟩ := exists_shift hq1 j (D - h) ⟨Finsupp.update d0 j (D - d0 j), by
    rw [hq1s]
    refine ⟨by simp, ?_⟩
    rwa [update_update_reflect (hD d0 hd0)], by simp; lia⟩
  have hq2s' : ∀ e, e ∈ q2.support ↔ e j ≤ h ∧ Finsupp.update e j (h - e j) ∈ p.support := by
    intro e
    rw [hq2s, hq1s]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by lia, ?_⟩
      convert h2 using 1
      ext l
      by_cases hl : l = j
      · subst hl; simp; lia
      · simp [Finsupp.update_apply, hl, Finsupp.single_eq_of_ne hl]
    · rintro ⟨h1, h2⟩
      refine ⟨by lia, ?_⟩
      convert h2 using 1
      ext l
      by_cases hl : l = j
      · subst hl; simp; lia
      · simp [Finsupp.update_apply, hl, Finsupp.single_eq_of_ne hl]
  have hD2 : ∀ d ∈ q2.support, d j ≤ h := fun d hd => ((hq2s' d).1 hd).1
  obtain ⟨q3, hq3, hq3s⟩ := exists_reflect hq2 j h hD2
  refine ⟨q3, hq3, fun e => ?_⟩
  rw [hq3s, hq2s']
  constructor
  · rintro ⟨h1, _, h3⟩
    exact ⟨h1, by rwa [update_update_reflect h1] at h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by simp, by rwa [update_update_reflect h1]⟩

end RealRooted.JumpSystem



/-!
## Localizing a stable polynomial to a box
-/


open MvPolynomial

namespace RealRooted.JumpSystem

variable {n : ℕ}

/-- The box localization, processing only the coordinates in `S`. -/
theorem exists_localize_aux {p : MvPolynomial (Fin n) ℝ} (hp : Stable p) (l h : Fin n → ℕ)
    (σ : Fin n → Bool) (α : Fin n →₀ ℕ) (hα : α ∈ p.support) (hl : ∀ j, l j ≤ α j)
    (hh : ∀ j, α j ≤ h j) (S : Finset (Fin n)) :
    ∃ q : MvPolynomial (Fin n) ℝ, Stable q ∧ ∀ e : Fin n →₀ ℕ, e ∈ q.support ↔
      (∀ j ∈ S, e j ≤ h j - l j) ∧
        Finsupp.equivFunOnFinite.symm (fun j => if j ∈ S then
          (if σ j then e j + l j else h j - e j) else e j) ∈ p.support := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨p, hp, fun e => ?_⟩
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, ite_false, true_and]
    rw [Finsupp.equivFunOnFinite_symm_coe]
  | insert a S haS ih =>
    obtain ⟨q, hq, hqs⟩ := ih
    -- the image of `α`
    set αS : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => if j ∈ S then
      (if σ j then α j - l j else h j - α j) else α j) with hαS
    have hαSmem : αS ∈ q.support := by
      rw [hqs]
      refine ⟨fun j hj => ?_, ?_⟩
      · have := hl j; have := hh j
        simp only [hαS, Finsupp.equivFunOnFinite_symm_apply_apply, hj, ite_true]
        split_ifs <;> lia
      · convert hα using 1
        ext j
        have := hl j; have := hh j
        simp only [hαS, Finsupp.equivFunOnFinite_symm_apply_apply]
        split_ifs <;> lia
    have hαSa : αS a = α a := by simp [hαS, haS]
    have hla := hl a
    have hha := hh a
    obtain ⟨q1, hq1, hq1s⟩ := exists_trunc hq a (h a) ⟨αS, hαSmem, by lia⟩
    obtain ⟨q2, hq2, hq2s⟩ := exists_shift hq1 a (l a) ⟨αS, (hq1s αS).2 ⟨by lia, hαSmem⟩,
      by lia⟩
    have hq2s' : ∀ e, e ∈ q2.support ↔ e a + l a ≤ h a ∧ e + Finsupp.single a (l a) ∈ q.support :=
      fun e => by rw [hq2s, hq1s]; simp
    cases hσa : σ a with
    | true =>
      refine ⟨q2, hq2, fun e => ?_⟩
      rw [hq2s', hqs]
      have hpt : (Finsupp.equivFunOnFinite.symm (fun j => if j ∈ S then
          (if σ j then (e + Finsupp.single a (l a)) j + l j else
            h j - (e + Finsupp.single a (l a)) j) else (e + Finsupp.single a (l a)) j)) =
          Finsupp.equivFunOnFinite.symm (fun j => if j ∈ insert a S then
          (if σ j then e j + l j else h j - e j) else e j) := by
        ext j
        simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.coe_add, Pi.add_apply,
          Finset.mem_insert]
        by_cases hja : j = a
        · subst hja; simp [haS, hσa]
        · simp [hja, Finsupp.single_eq_of_ne hja]
      rw [hpt]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨fun j hj => ?_, h3⟩
        rcases Finset.mem_insert.mp hj with rfl | hj
        · lia
        · have := h2 j hj
          have hja : j ≠ a := fun h => haS (h ▸ hj)
          simpa [Finsupp.single_eq_of_ne hja] using this
      · rintro ⟨h1, h3⟩
        refine ⟨by have := h1 a (Finset.mem_insert_self a S); lia, fun j hj => ?_, h3⟩
        have hja : j ≠ a := fun h => haS (h ▸ hj)
        simpa [Finsupp.single_eq_of_ne hja] using h1 j (Finset.mem_insert_of_mem hj)
    | false =>
      have hD : ∀ d ∈ q2.support, d a ≤ h a - l a := fun d hd => by
        have := ((hq2s' d).1 hd).1; lia
      obtain ⟨q3, hq3, hq3s⟩ := exists_reflect hq2 a (h a - l a) hD
      refine ⟨q3, hq3, fun e => ?_⟩
      rw [hq3s, hq2s', hqs]
      constructor
      · rintro ⟨h0, h1, h2, h3⟩
        refine ⟨fun j hj => ?_, ?_⟩
        · rcases Finset.mem_insert.mp hj with rfl | hj
          · exact h0
          · have := h2 j hj
            have hja : j ≠ a := fun h => haS (h ▸ hj)
            simpa [Finsupp.single_eq_of_ne hja, Finsupp.update_apply, hja] using this
        · convert h3 using 1
          ext j
          simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.coe_add, Pi.add_apply,
            Finset.mem_insert]
          by_cases hja : j = a
          · subst hja; simp [haS, hσa]; lia
          · simp [hja, Finsupp.single_eq_of_ne hja, Finsupp.update_apply]
      · rintro ⟨h1, h3⟩
        have h0 := h1 a (Finset.mem_insert_self a S)
        refine ⟨h0, by simp; lia, fun j hj => ?_, ?_⟩
        · have hja : j ≠ a := fun h => haS (h ▸ hj)
          simpa [Finsupp.single_eq_of_ne hja, Finsupp.update_apply, hja] using
            h1 j (Finset.mem_insert_of_mem hj)
        · convert h3 using 1
          ext j
          simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.coe_add, Pi.add_apply,
            Finset.mem_insert]
          by_cases hja : j = a
          · subst hja; simp [haS, hσa]; lia
          · simp [hja, Finsupp.single_eq_of_ne hja, Finsupp.update_apply]

theorem exists_localize {p : MvPolynomial (Fin n) ℝ} (hp : Stable p) (l h : Fin n → ℕ)
    (σ : Fin n → Bool) (α : Fin n →₀ ℕ) (hα : α ∈ p.support) (hl : ∀ j, l j ≤ α j)
    (hh : ∀ j, α j ≤ h j) :
    ∃ q : MvPolynomial (Fin n) ℝ, Stable q ∧ ∀ e : Fin n →₀ ℕ, e ∈ q.support ↔
      (∀ j, e j ≤ h j - l j) ∧
        Finsupp.equivFunOnFinite.symm (fun j => if σ j then e j + l j else h j - e j)
          ∈ p.support := by
  obtain ⟨q, hq, hqs⟩ := exists_localize_aux hp l h σ α hα hl hh Finset.univ
  exact ⟨q, hq, fun e => by simpa using hqs e⟩

end RealRooted.JumpSystem



/-!
## The base case
-/


open MvPolynomial

namespace RealRooted.JumpSystem

variable {n : ℕ}

theorem not_stable_two_term {F : MvPolynomial (Fin n) ℝ} (hF : Stable F) (h0 : F.coeff 0 ≠ 0)
    (N : ℕ) (hN : 3 ≤ N) (hdeg : ∀ γ ∈ F.support, γ ≠ 0 → ∑ i, γ i = N)
    (hex : ∃ γ ∈ F.support, γ ≠ 0) : False := by
  classical
  set c := F.coeff 0 with hc
  set G := F - C c with hG
  have hcoeffG : ∀ γ, G.coeff γ = if γ = 0 then 0 else F.coeff γ := by
    intro γ
    rw [hG, coeff_sub, coeff_C]
    split_ifs with h1 h2 h2
    · subst h2; simp [hc]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  have hsuppG : ∀ γ ∈ G.support, γ ≠ 0 ∧ γ ∈ F.support := by
    intro γ hγ
    rw [mem_support_iff, hcoeffG] at hγ
    split_ifs at hγ with h
    · exact absurd rfl hγ
    · exact ⟨h, mem_support_iff.mpr hγ⟩
  have hG0 : G ≠ 0 := by
    obtain ⟨γ, hγ, hγ0⟩ := hex
    intro h
    have := congrArg (fun q => q.coeff γ) h
    rw [hcoeffG, ite_eq_right hγ0, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    exact mem_support_iff.mp hγ this
  obtain ⟨x, hxpos, hκ⟩ := exists_pos_eval_ne_zero hG0
  set κ := eval x G with hκdef
  obtain ⟨ζ, hζim, hζN⟩ := exists_upper_root N hN (-c / κ) (div_ne_zero (neg_ne_zero.mpr h0) hκ)
  set z : Fin n → ℂ := fun j => ζ * (x j : ℂ) with hz
  have hzim : ∀ j, 0 < (z j).im := by
    intro j
    simp only [hz, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
    exact mul_pos hζim (hxpos j)
  apply hF z hzim
  have hFG : F = C c + G := by rw [hG]; ring
  have hevalG : eval z (map (algebraMap ℝ ℂ) G) = ζ ^ N * (κ : ℂ) := by
    rw [eval_map_eq_sum, hκdef, eval_eq', Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    obtain ⟨hγ0, hγF⟩ := hsuppG γ hγ
    have hdeg := hdeg γ hγF hγ0
    simp only [hz, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg,
      Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_pow]
    ring
  rw [hFG, map_add, map_C, eval_add, eval_C, hevalG, hζN]
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  push_cast
  field_simp
  simp

theorem base_case {q : MvPolynomial (Fin n) ℝ} (hq : Stable q) (i : Fin n)
    (h0 : (0 : Fin n →₀ ℕ) ∈ q.support) (hγ : ∃ γ ∈ q.support, 1 ≤ γ i) :
    ∃ γ ∈ q.support, γ = Finsupp.single i 1 ∨ γ = Finsupp.single i 2 ∨
      ∃ j, j ≠ i ∧ γ = Finsupp.single i 1 + Finsupp.single j 1 := by
  classical
  -- `b γ` is the total degree outside coordinate `i`
  obtain ⟨b, hb⟩ : ∃ b : (Fin n →₀ ℕ) → ℕ, ∀ γ, b γ = ∑ j ∈ Finset.univ.erase i, γ j :=
    ⟨_, fun _ => rfl⟩
  have hsum : ∀ γ : Fin n →₀ ℕ, ∑ j, γ j = γ i + b γ := fun γ => by
    rw [hb, Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hle_b : ∀ γ : Fin n →₀ ℕ, ∀ j, j ≠ i → γ j ≤ b γ := fun γ j hj => by
    rw [hb]
    exact Finset.single_le_sum (f := fun j => γ j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  set Cset := q.support.filter (fun γ => 1 ≤ γ i) with hCset
  have hCne : Cset.Nonempty := by
    obtain ⟨γ, hγ, hγi⟩ := hγ
    exact ⟨γ, Finset.mem_filter.mpr ⟨hγ, hγi⟩⟩
  obtain ⟨f, hf⟩ : ∃ f : (Fin n →₀ ℕ) → ℚ, ∀ γ, f γ = (b γ : ℚ) / γ i := ⟨_, fun _ => rfl⟩
  obtain ⟨γ1, hγ1C, hγ1min⟩ := Finset.exists_min_image Cset f hCne
  set C' := Cset.filter (fun γ => f γ = f γ1) with hC'
  have hC'ne : C'.Nonempty := ⟨γ1, Finset.mem_filter.mpr ⟨hγ1C, rfl⟩⟩
  obtain ⟨γs, hγsC', hγsmin⟩ := Finset.exists_min_image C' (fun γ => γ i) hC'ne
  obtain ⟨hγsC, hγsf⟩ := Finset.mem_filter.mp hγsC'
  obtain ⟨hγsq, hγsi⟩ := Finset.mem_filter.mp hγsC
  -- key inequality: slopes are at least `b γs / γs i`, with ties only for larger `γ i`
  have hslope : ∀ γ ∈ q.support, 1 ≤ γ i → b γs * γ i ≤ b γ * γs i ∧
      (b γs * γ i = b γ * γs i → γs i ≤ γ i) := by
    intro γ hγ hγi
    have hγC : γ ∈ Cset := Finset.mem_filter.mpr ⟨hγ, hγi⟩
    have h1 : f γs ≤ f γ := hγsf ▸ hγ1min γ hγC
    have hpos1 : (0 : ℚ) < γ i := by exact_mod_cast hγi
    have hpos2 : (0 : ℚ) < γs i := by exact_mod_cast hγsi
    rw [hf, hf, div_le_div_iff₀ hpos2 hpos1] at h1
    refine ⟨by exact_mod_cast h1, fun heq => ?_⟩
    have hfeq : f γ = f γ1 := by
      rw [← hγsf, hf, hf, div_eq_div_iff hpos1.ne' hpos2.ne']
      exact_mod_cast heq.symm
    exact hγsmin γ (Finset.mem_filter.mpr ⟨hγC, hfeq⟩)
  -- truncate in coordinate `i`
  obtain ⟨q2, hq2, hq2s⟩ := exists_trunc hq i (γs i) ⟨0, h0, Nat.zero_le _⟩
  set w : Fin n → ℤ := fun j => if j = i then -(b γs : ℤ) else (γs i : ℤ) with hw
  have hweight : ∀ γ : Fin n →₀ ℕ, Finsupp.weight w γ = γs i * b γ - b γs * γ i := by
    intro γ
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hb γ]
    simp only [hw, ite_eq_left, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun j hj => by rw [ite_eq_right (Finset.ne_of_mem_erase hj)]),
      ← Finset.sum_mul]
    push_cast
    ring
  have hwnonneg : ∀ γ ∈ q2.support, 0 ≤ Finsupp.weight w γ := by
    intro γ hγ
    obtain ⟨hγi, hγq⟩ := (hq2s γ).1 hγ
    rw [hweight]
    rcases Nat.eq_zero_or_pos (γ i) with h | h
    · rw [h]; simp only [Nat.cast_zero, mul_zero, sub_zero]; positivity
    · have := (hslope γ hγq h).1
      have : (b γs : ℤ) * γ i ≤ b γ * γs i := by exact_mod_cast this
      linarith
  have hwzero : ∀ γ ∈ q2.support, Finsupp.weight w γ = 0 →
      γ = 0 ∨ (γ i = γs i ∧ b γ = b γs) := by
    intro γ hγ h
    obtain ⟨hγi, hγq⟩ := (hq2s γ).1 hγ
    rw [hweight] at h
    rcases Nat.eq_zero_or_pos (γ i) with h' | h'
    · left
      rw [h'] at h
      have hbz : b γ = 0 := by
        have : (γs i : ℤ) * b γ = 0 := by simpa using h
        rcases mul_eq_zero.mp this with h1 | h1
        · lia
        · exact_mod_cast h1
      ext j
      by_cases hj : j = i
      · subst hj; simpa using h'
      · have := hle_b γ j hj
        simp only [Finsupp.coe_zero, Pi.zero_apply]
        lia
    · right
      have heq : b γs * γ i = b γ * γs i := by
        have : (b γs : ℤ) * γ i = b γ * γs i := by linarith
        exact_mod_cast this
      have := (hslope γ hγq h').2 heq
      have hγia : γ i = γs i := le_antisymm hγi this
      refine ⟨hγia, ?_⟩
      rw [hγia] at heq
      exact (Nat.eq_of_mul_eq_mul_right hγsi heq).symm
  have h0q2 : (0 : Fin n →₀ ℕ) ∈ q2.support := (hq2s 0).2 ⟨Nat.zero_le _, h0⟩
  have hγsq2 : γs ∈ q2.support := (hq2s γs).2 ⟨le_rfl, hγsq⟩
  have hwγs : Finsupp.weight w γs = 0 := by rw [hweight]; ring
  set F := weightedHomogeneousComponent w 0 q2 with hF
  have hFst : Stable F := hq2.weightedHomogeneousComponent w 0 hwnonneg
    ⟨0, h0q2, by simp⟩
  have hcoeffF : ∀ γ, F.coeff γ = if Finsupp.weight w γ = 0 then q2.coeff γ else 0 := by
    intro γ; rw [hF, coeff_weightedHomogeneousComponent]
  have hγsne : γs ≠ 0 := by
    intro h
    have : γs i = 0 := by rw [h]; rfl
    lia
  by_contra hcon
  have hsmall : γs i + b γs ≥ 3 := by
    by_contra hlt
    push Not at hlt
    apply hcon
    refine ⟨γs, hγsq, ?_⟩
    rcases Nat.lt_or_ge (b γs) 1 with hb0' | hb0'
    · have hz : ∀ j, j ≠ i → γs j = 0 := fun j hj => by have := hle_b γs j hj; lia
      have ha : γs i = 1 ∨ γs i = 2 := by lia
      rcases ha with ha | ha
      · left
        ext j
        by_cases hj : j = i
        · subst hj; simp [ha]
        · simp [Finsupp.single_eq_of_ne hj, hz j hj]
      · right; left
        ext j
        by_cases hj : j = i
        · subst hj; simp [ha]
        · simp [Finsupp.single_eq_of_ne hj, hz j hj]
    · have ha : γs i = 1 := by lia
      have hb1 : b γs = 1 := by lia
      right; right
      have hne : ∑ j ∈ Finset.univ.erase i, γs j ≠ 0 := by rw [← hb]; lia
      obtain ⟨j, hj, hγj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      refine ⟨j, hji, ?_⟩
      have hγj1 : γs j = 1 := by have := hle_b γs j hji; lia
      have hothers : ∀ k, k ≠ i → k ≠ j → γs k = 0 := by
        intro k hki hkj
        have hsub : ({j, k} : Finset (Fin n)) ⊆ Finset.univ.erase i := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
          · exact Finset.mem_erase.mpr ⟨hki, Finset.mem_univ _⟩
        have := Finset.sum_le_sum_of_subset (f := fun j => γs j) hsub
        rw [Finset.sum_pair (Ne.symm hkj), ← hb] at this
        lia
      ext k
      by_cases hk : k = i
      · subst hk
        simp [Finsupp.single_eq_of_ne hji.symm, ha]
      · by_cases hkj : k = j
        · subst hkj; simp [Finsupp.single_eq_of_ne hk, hγj1]
        · simp [Finsupp.single_eq_of_ne hk, Finsupp.single_eq_of_ne hkj, hothers k hk hkj]
  refine not_stable_two_term hFst ?_ (γs i + b γs) hsmall ?_ ⟨γs, ?_, hγsne⟩
  · rw [hcoeffF, ite_eq_left (by simp)]
    exact mem_support_iff.mp h0q2
  · intro γ hγ hγ0
    rw [mem_support_iff, hcoeffF] at hγ
    split_ifs at hγ with hwt
    · have hγq2 : γ ∈ q2.support := mem_support_iff.mpr hγ
      rcases hwzero γ hγq2 hwt with h | ⟨h1, h2⟩
      · exact absurd h hγ0
      · rw [hsum, h1, h2]
    · exact absurd rfl hγ
  · rw [mem_support_iff, hcoeffF, ite_eq_left hwγs]
    exact mem_support_iff.mp hγsq2

end RealRooted.JumpSystem


/-!
## Supports of real stable polynomials are jump systems (Brändén 2007)

P. Brändén, "Polynomials with the half-plane property and matroid theory", Adv. Math. 216
(2007), Theorem 3.2: the support of a multivariate polynomial with the half-plane property
(nonvanishing when all variables lie in the open upper half-plane) is a jump system.
-/

open MvPolynomial

namespace RealRooted

open JumpSystem

variable {n : ℕ}

/-- The `ℓ¹` distance on `ℤⁿ`. -/
def JumpSystem.dist1 (α β : Fin n → ℤ) : ℤ := ∑ i, |α i - β i|

/-- `s` is an `(α, β)`-step: a unit vector `± eᵢ` with `‖α + s - β‖₁ < ‖α - β‖₁`. -/
def JumpSystem.IsStep (α β s : Fin n → ℤ) : Prop :=
  (∃ i, s = Pi.single i 1 ∨ s = Pi.single i (-1)) ∧ dist1 (α + s) β < dist1 α β

/-- Bouchet–Cunningham two-step axiom: `J ⊆ ℤⁿ` is a *jump system* if for all `α, β ∈ J` and
every `(α, β)`-step `s`, either `α + s ∈ J` or there is an `(α + s, β)`-step `t` with
`α + s + t ∈ J`. -/
def IsJumpSystem (J : Set (Fin n → ℤ)) : Prop :=
  ∀ α ∈ J, ∀ β ∈ J, ∀ s, IsStep α β s →
    α + s ∈ J ∨ ∃ t, IsStep (α + s) β t ∧ α + s + t ∈ J

/-- The support of `p` as a subset of `ℤⁿ`. -/
def JumpSystem.supportInt (p : MvPolynomial (Fin n) ℝ) : Set (Fin n → ℤ) :=
  {α | ∃ m ∈ p.support, ∀ i, α i = (m i : ℤ)}

/-- Changing a vector in coordinate `k` changes the `ℓ¹` distance only in that coordinate. -/
lemma JumpSystem.dist1_add_single (x b : Fin n → ℤ) (k : Fin n) (c : ℤ) :
    dist1 (x + Pi.single k c) b = dist1 x b - |x k - b k| + |x k + c - b k| := by
  unfold dist1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have : ∑ j ∈ Finset.univ.erase k, |(x + (Pi.single k c : Fin n → ℤ)) j - b j| =
      ∑ j ∈ Finset.univ.erase k, |x j - b j| := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj), add_zero]
  rw [this]
  simp only [Pi.add_apply, Pi.single_eq_same]
  ring

lemma JumpSystem.isStep_single (x b : Fin n → ℤ) (k : Fin n) (c : ℤ) (hc : c = 1 ∨ c = -1)
    (h : |x k + c - b k| < |x k - b k|) : IsStep x b (Pi.single k c) := by
  refine ⟨⟨k, by rcases hc with rfl | rfl <;> simp⟩, ?_⟩
  rw [dist1_add_single]
  linarith

/-- Brändén: the support of a real stable polynomial is a jump system. -/
theorem MvRealStable.isJumpSystem_supportInt {p : MvPolynomial (Fin n) ℝ}
    (hp : MvRealStable p) : IsJumpSystem (JumpSystem.supportInt p) := by
  have hs : Stable p := hp
  rintro α ⟨mα, hmα, hα⟩ β ⟨mβ, hmβ, hβ⟩ s ⟨⟨i, hsi⟩, hdist⟩
  have hαeq : α = fun k => (mα k : ℤ) := funext hα
  have hβeq : β = fun k => (mβ k : ℤ) := funext hβ
  subst hαeq hβeq
  set σ : Fin n → Bool := fun k => decide (mα k ≤ mβ k) with hσ
  set l : Fin n → ℕ := fun k => min (mα k) (mβ k) with hl
  set h : Fin n → ℕ := fun k => max (mα k) (mβ k) with hh
  set sg : Fin n → ℤ := fun k => if σ k then 1 else -1 with hsg
  obtain ⟨q, hq, hqsupp⟩ := exists_localize hs l h σ mα hmα
    (fun k => min_le_left _ _) (fun k => le_max_left _ _)
  set ψ : (Fin n →₀ ℕ) → (Fin n →₀ ℕ) := fun e =>
    Finsupp.equivFunOnFinite.symm (fun j => if σ j then e j + l j else h j - e j) with hψ
  have decode : ∀ e : Fin n →₀ ℕ, (∀ j, e j ≤ h j - l j) → ∀ k,
      ((ψ e k : ℕ) : ℤ) = mα k + sg k * e k := by
    intro e he k
    have hek := he k
    simp only [hψ, hsg, hσ, hl, hh, Finsupp.equivFunOnFinite_symm_apply_apply] at hek ⊢
    by_cases hk : mα k ≤ mβ k
    · simp only [hk, decide_true, ite_true] at hek ⊢
      push_cast
      lia
    · simp only [hk, decide_false, Bool.false_eq_true, ite_false] at hek ⊢
      lia
  -- the step `s` points in direction `sg i`
  have hsdir : s = Pi.single i (sg i) ∧ mα i ≠ mβ i := by
    rcases hsi with rfl | rfl
    · have := hdist
      rw [dist1_add_single] at this
      have hlt : mα i < mβ i := by
        by_contra hc
        push Not at hc
        have h1 : (mβ i : ℤ) ≤ mα i := by exact_mod_cast hc
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at this
        linarith
      refine ⟨?_, hlt.ne⟩
      simp [hsg, hσ, hlt.le]
    · have := hdist
      rw [dist1_add_single] at this
      have hlt : mβ i < mα i := by
        by_contra hc
        push Not at hc
        have h1 : (mα i : ℤ) ≤ mβ i := by exact_mod_cast hc
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at this
        linarith
      refine ⟨?_, hlt.ne'⟩
      simp [hsg, hσ, not_le.mpr hlt]
  obtain ⟨rfl, hne_i⟩ := hsdir
  have h0 : (0 : Fin n →₀ ℕ) ∈ q.support := by
    rw [hqsupp]
    refine ⟨fun j => Nat.zero_le _, ?_⟩
    convert hmα using 1
    ext k
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.coe_zero, Pi.zero_apply,
      hσ, hl, hh]
    by_cases hk : mα k ≤ mβ k
    · simp [hk]
    · simp only [hk, decide_false, Bool.false_eq_true, ite_false]
      lia
  have hγβ : ∃ γ ∈ q.support, 1 ≤ γ i := by
    refine ⟨Finsupp.equivFunOnFinite.symm (fun j => h j - l j), ?_, ?_⟩
    · rw [hqsupp]
      refine ⟨fun j => le_rfl, ?_⟩
      convert hmβ using 1
      ext k
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply, hσ, hl, hh]
      by_cases hk : mα k ≤ mβ k
      · simp only [hk, decide_true, ite_true]
        lia
      · simp only [hk, decide_false, Bool.false_eq_true, ite_false]
        lia
    · simp only [Finsupp.equivFunOnFinite_symm_apply_apply, hl, hh]
      lia
  have hsgi : sg i = 1 ∨ sg i = -1 := by
    simp only [hsg]; split_ifs <;> simp
  obtain ⟨γ, hγ, hγcases⟩ := base_case hq i h0 hγβ
  have hγ' := (hqsupp γ).1 hγ
  have hdec := decode γ hγ'.1
  have hmem : ∀ v : Fin n → ℤ, (∀ k, v k = mα k + sg k * γ k) → v ∈ supportInt p :=
    fun v hv => ⟨ψ γ, hγ'.2, fun k => by rw [hv k, hdec k]⟩
  rcases hγcases with rfl | rfl | ⟨j, hji, rfl⟩
  · left
    refine hmem _ fun k => ?_
    by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk, Finsupp.single_eq_of_ne hk]
  · right
    have hbd := hγ'.1 i
    simp only [Finsupp.single_eq_same, hl, hh] at hbd
    refine ⟨Pi.single i (sg i), isStep_single _ _ _ _ hsgi ?_, hmem _ fun k => ?_⟩
    · simp only [Pi.add_apply, Pi.single_eq_same]
      simp only [hsg, hσ]
      by_cases hi : mα i ≤ mβ i
      · simp only [hi, decide_true, ite_true] at hbd ⊢
        rw [abs_lt]; constructor <;>
          rcases abs_cases ((mα i : ℤ) + 1 - mβ i) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
          lia
      · simp only [hi, decide_false, Bool.false_eq_true, ite_false] at hbd ⊢
        rw [abs_lt]; constructor <;>
          rcases abs_cases ((mα i : ℤ) + -1 - mβ i) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
          lia
    · by_cases hk : k = i
      · subst hk; simp; ring
      · simp [Pi.single_eq_of_ne hk, Finsupp.single_eq_of_ne hk]
  · right
    have hbd := hγ'.1 j
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hji, hl, hh]
      at hbd
    have hsgj : sg j = 1 ∨ sg j = -1 := by
      simp only [hsg]; split_ifs <;> simp
    refine ⟨Pi.single j (sg j), isStep_single _ _ _ _ hsgj ?_, hmem _ fun k => ?_⟩
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hji, add_zero]
      simp only [hsg, hσ]
      by_cases hj : mα j ≤ mβ j
      · simp only [hj, decide_true, ite_true]
        rw [abs_lt]; constructor <;> rcases abs_cases ((mα j : ℤ) - mβ j) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
          lia
      · simp only [hj, decide_false, Bool.false_eq_true, ite_false]
        rw [abs_lt]; constructor <;> rcases abs_cases ((mα j : ℤ) - mβ j) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
          lia
    · by_cases hk : k = i
      · subst hk; simp [Pi.single_eq_of_ne hji.symm, Finsupp.single_eq_of_ne hji.symm]
      · by_cases hkj : k = j
        · subst hkj; simp [Pi.single_eq_of_ne hk, Finsupp.single_eq_of_ne hk]
        · simp [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hkj, Finsupp.single_eq_of_ne hk,
            Finsupp.single_eq_of_ne hkj]

end RealRooted
