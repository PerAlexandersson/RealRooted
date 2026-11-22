module

public import RealRooted.BasisTransform.LimitingAppell
public import RealRooted.Mathlib.RingTheory.PowerSeries.NewtonSums
public import Mathlib.LinearAlgebra.Matrix.PosDef
import RealRooted.Mathlib.RingTheory.Polynomial.Vieta
import RealRooted.Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Tactic.Ring

/-!
# Hankel positivity for limiting Appell coefficients

The normalized squared-root multisets of the even limiting Appell rows have
elementary symmetric coefficients tending to `d`. Newton's identities then
pass their positive power sums to the limit. Every shifted Hankel matrix of
these limiting power sums is positive semidefinite. This is the algebraic
moment assertion of the unpublished manuscript behind RealRooted issue #2181;
no entire-function factorization is used.
-/

@[expose] public section

open Finset Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- Newton moments of the limiting Appell coefficient series. Positive
indices correspond to the power sums of the normalized squared roots. -/
def limitingAppellMoment (d : ℕ → ℝ) (k : ℕ) : ℝ :=
  PowerSeries.newtonSum (PowerSeries.mk d) k

private def normalizedSquareRoots (d : ℕ → ℝ) (n : ℕ) : Multiset ℝ :=
  (limitingAppellSquarePolynomial d n).roots.map
    (fun x => (((2 * n : ℕ) : ℝ)⁻¹ ^ 2) * x)

private theorem normalizedSquareRoots_nonneg {d : ℕ → ℝ}
    (hs : ∀ N, (limitingAppellPolynomial d N).Splits) (n : ℕ) :
    ∀ x ∈ normalizedSquareRoots d n, 0 ≤ x := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
  exact mul_nonneg (sq_nonneg _)
    ((limitingAppellSquarePolynomial_splits_and_roots_nonneg (hs (2 * n))).2 r hr)

private theorem tendsto_esymm_normalizedSquareRoots
    {d : ℕ → ℝ} (hd : d 0 = 1)
    (hs : ∀ N, (limitingAppellPolynomial d N).Splits) (j : ℕ) :
    Tendsto (fun n => (normalizedSquareRoots d n).esymm j) atTop (𝓝 (d j)) := by
  have htwo : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    lia
  have hlim := ((Nat.tendsto_descFactorial_div_pow_atTop (2 * j)).comp htwo).mul_const (d j)
  simp only [one_mul] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop j] with n hn
  rw [normalizedSquareRoots]
  have he := Multiset.pow_smul_esymm (((2 * n : ℕ) : ℝ)⁻¹ ^ 2) j
    (limitingAppellSquarePolynomial d n).roots
  simp only [smul_eq_mul] at he
  rw [← he, esymm_roots_limitingAppellSquarePolynomial hd hn (hs (2 * n))]
  dsimp only [Function.comp_apply]
  rw [← pow_mul, inv_pow, div_eq_mul_inv]
  ring

private theorem tendsto_powerSum_normalizedSquareRoots
    {d : ℕ → ℝ} (hd : d 0 = 1)
    (hs : ∀ N, (limitingAppellPolynomial d N).Splits) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n => ((normalizedSquareRoots d n).map (· ^ k)).sum)
      atTop (𝓝 (limitingAppellMoment d k)) := by
  have ht := PowerSeries.tendsto_newtonSum_of_coeff_tendsto
    (a := fun n => PowerSeries.mk (normalizedSquareRoots d n).esymm)
    (b := PowerSeries.mk d)
    (fun j => by simpa using tendsto_esymm_normalizedSquareRoots hd hs j) k
  simpa only [PowerSeries.newtonSum_mk_esymm _ hk, limitingAppellMoment] using ht

private theorem powerSum_hankel_nonneg
    (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) (n r : ℕ) (v : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      v i * ((s.map (· ^ (i.val + j.val + r))).sum * v j) := by
  have heq : (∑ i : Fin n, ∑ j : Fin n,
      v i * ((s.map (· ^ (i.val + j.val + r))).sum * v j)) =
      (s.map (fun x => x ^ r * (∑ i : Fin n, v i * x ^ i.val) ^ 2)).sum := by
    clear hs
    induction s using Multiset.induction_on with
    | empty => simp
    | cons x s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      simp_rw [add_mul, mul_add, sum_add_distrib]
      rw [ih]
      congr 1
      simp only [pow_two, pow_add, mul_sum, sum_mul]
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      ring
  rw [heq]
  apply Multiset.sum_nonneg
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
  exact mul_nonneg (pow_nonneg (hs x hx) r) (sq_nonneg _)

/-- Every positive shift of the Hankel matrix of the limiting Newton
moments is positive semidefinite. In particular shifts one and two give the
two moment matrices in the limiting Appell theorem. -/
theorem posSemidef_limitingAppellMoment
    {d : ℕ → ℝ} (hd : d 0 = 1)
    (hs : ∀ N, (limitingAppellPolynomial d N).Splits) (n r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin n =>
      limitingAppellMoment d (i.val + j.val + (r + 1))) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    change star (limitingAppellMoment d (j.val + i.val + (r + 1))) = _
    simp [Nat.add_comm]
  · intro v
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, mul_sum]
    apply ge_of_tendsto (x := atTop)
      (tendsto_finsetSum univ (fun i _ => tendsto_finsetSum univ (fun j _ =>
        ((tendsto_powerSum_normalizedSquareRoots hd hs
          (k := i.val + j.val + (r + 1)) (by lia)).mul_const (v j)).const_mul
          (v i))))
    exact .of_forall fun m => powerSum_hankel_nonneg (normalizedSquareRoots d m)
      (normalizedSquareRoots_nonneg hs m) n (r + 1) v

/-- The limiting Newton moments are precisely the signed coefficients of
`log A` in the limiting Appell theorem. -/
theorem limitingAppellMoment_eq_signed_coeff_logOf
    {d : ℕ → ℝ} (hd : d 0 = 1)
    (hs : ∀ N, (limitingAppellPolynomial d N).Splits) {k : ℕ} (hk : 0 < k) :
    limitingAppellMoment d k = (-1 : ℝ) ^ (k + 1) * k *
      PowerSeries.coeff k (PowerSeries.logOf (PowerSeries.mk d)) := by
  have ht := PowerSeries.tendsto_coeff_logOf_of_coeff_tendsto
    (a := fun n => PowerSeries.mk (normalizedSquareRoots d n).esymm)
    (b := PowerSeries.mk d) (fun _ => by simp) (by simpa using hd)
    (fun j => by simpa using tendsto_esymm_normalizedSquareRoots hd hs j) k
  have ht' := ht.const_mul ((-1 : ℝ) ^ (k + 1) * k)
  simp_rw [PowerSeries.signed_coeff_logOf_mk_esymm _ hk] at ht'
  exact tendsto_nhds_unique (tendsto_powerSum_normalizedSquareRoots hd hs hk) ht'

/-- Both Hankel matrices of the signed logarithmic coefficients of `A`
are positive semidefinite, as are all their positive shifts. -/
theorem posSemidef_signed_coeff_logOf_limitingAppell
    {d : ℕ → ℝ} (hd : d 0 = 1)
    (hs : ∀ N, (limitingAppellPolynomial d N).Splits) (n r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin n =>
      let k := i.val + j.val + (r + 1)
      (-1 : ℝ) ^ (k + 1) * k *
        PowerSeries.coeff k (PowerSeries.logOf (PowerSeries.mk d))) := by
  have h := posSemidef_limitingAppellMoment hd hs n r
  have heq : (fun i j : Fin n => limitingAppellMoment d (i.val + j.val + (r + 1))) =
      (fun i j : Fin n =>
        let k := i.val + j.val + (r + 1)
        (-1 : ℝ) ^ (k + 1) * k *
          PowerSeries.coeff k (PowerSeries.logOf (PowerSeries.mk d))) := by
    funext i j
    exact limitingAppellMoment_eq_signed_coeff_logOf hd hs (by lia)
  rwa [heq] at h

/-- The first limiting Newton moment is the first coefficient. -/
@[simp] theorem limitingAppellMoment_one (d : ℕ → ℝ) :
    limitingAppellMoment d 1 = d 1 := by
  unfold limitingAppellMoment
  rw [PowerSeries.newtonSum_of_pos _ (by decide)]
  have ha : HasAntidiagonal.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
  rw [ha]
  norm_num [Finset.filter_insert, Finset.filter_singleton, Finset.sum_insert]

/-- The second limiting Newton moment is `d₁² - 2d₂`. -/
@[simp] theorem limitingAppellMoment_two (d : ℕ → ℝ) :
    limitingAppellMoment d 2 = d 1 ^ 2 - 2 * d 2 := by
  unfold limitingAppellMoment
  rw [PowerSeries.newtonSum_of_pos _ (by decide)]
  have ha : HasAntidiagonal.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
  rw [ha]
  norm_num [Finset.filter_insert, Finset.filter_singleton, Finset.sum_insert]
  rw [show PowerSeries.newtonSum (PowerSeries.mk d) 1 = d 1 from
    limitingAppellMoment_one d]
  ring

/-- The third limiting Newton moment is `d₁³ - 3d₁d₂ + 3d₃`. -/
@[simp] theorem limitingAppellMoment_three (d : ℕ → ℝ) :
    limitingAppellMoment d 3 = d 1 ^ 3 - 3 * d 1 * d 2 + 3 * d 3 := by
  unfold limitingAppellMoment
  rw [PowerSeries.newtonSum_of_pos _ (by decide)]
  have ha : HasAntidiagonal.antidiagonal 3 = {(0, 3), (1, 2), (2, 1), (3, 0)} := by decide
  rw [ha]
  norm_num [Finset.filter_insert, Finset.filter_singleton, Finset.sum_insert]
  rw [show PowerSeries.newtonSum (PowerSeries.mk d) 1 = d 1 from
    limitingAppellMoment_one d,
    show PowerSeries.newtonSum (PowerSeries.mk d) 2 = d 1 ^ 2 - 2 * d 2 from
      limitingAppellMoment_two d]
  ring

/-- Every positive limiting Newton moment is nonnegative. -/
theorem limitingAppellMoment_nonneg
    {d : ℕ → ℝ} (hd : d 0 = 1)
    (hs : ∀ N, (limitingAppellPolynomial d N).Splits) {k : ℕ} (hk : 0 < k) :
    0 ≤ limitingAppellMoment d k := by
  have h := (posSemidef_limitingAppellMoment hd hs 1 (k - 1)).diag_nonneg (i := 0)
  simpa [Nat.sub_add_cancel hk] using h

/-- The first nontrivial Hankel determinant inequality for the limiting
Appell coefficients. -/
theorem limitingAppellMoment_two_sq_le_one_mul_three
    {d : ℕ → ℝ} (hd : d 0 = 1)
    (hs : ∀ N, (limitingAppellPolynomial d N).Splits) :
    (d 1 ^ 2 - 2 * d 2) ^ 2 ≤ d 1 * (d 1 ^ 3 - 3 * d 1 * d 2 + 3 * d 3) := by
  have hfinite (n : ℕ) :
      (((normalizedSquareRoots d n).map (· ^ 2)).sum) ^ 2 ≤
        ((normalizedSquareRoots d n).map (· ^ 1)).sum *
          ((normalizedSquareRoots d n).map (· ^ 3)).sum := by
    let s := normalizedSquareRoots d n
    have heq (k : ℕ) : (s.map (· ^ k)).sum = ∑ x : s.ToType, (x : ℝ) ^ k := by
      rw [← Multiset.map_univ_comp_coe, Finset.sum_map_val]
      rfl
    change ((s.map (· ^ 2)).sum) ^ 2 ≤
      (s.map (· ^ 1)).sum * (s.map (· ^ 3)).sum
    rw [heq 2, heq 1, heq 3]
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    · intro x hx
      exact pow_nonneg (normalizedSquareRoots_nonneg hs n x Multiset.coe_mem) 1
    · intro x hx
      exact pow_nonneg (normalizedSquareRoots_nonneg hs n x Multiset.coe_mem) 3
    · intro x hx
      exact le_of_eq (by ring)
  have h := le_of_tendsto_of_tendsto
    ((tendsto_powerSum_normalizedSquareRoots hd hs (by decide : 0 < 2)).pow 2)
    ((tendsto_powerSum_normalizedSquareRoots hd hs (by decide : 0 < 1)).mul
      (tendsto_powerSum_normalizedSquareRoots hd hs (by decide : 0 < 3)))
    (.of_forall hfinite)
  simpa only [limitingAppellMoment_one, limitingAppellMoment_two,
    limitingAppellMoment_three] using h

/-- The logarithmic moment matrices forced by a monic degree-preserving
basis transform that preserves polynomials with nonpositive roots. -/
theorem posSemidef_signed_coeff_logOf_appellCoefficient
    {P : ℕ → ℝ[X]} (hdeg : ∀ n, (P n).natDegree = n)
    (hmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits) (n r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin n =>
      let k := i.val + j.val + (r + 1)
      (-1 : ℝ) ^ (k + 1) * k * PowerSeries.coeff k
        (PowerSeries.logOf (PowerSeries.mk
          (fun j => (appellCoefficient P (2 * j)).coeff j)))) := by
  apply posSemidef_signed_coeff_logOf_limitingAppell
  · exact coeff_zero_appellCoefficient_zero_eq_one hdeg hmonic hpres
  · exact limitingAppellPolynomial_splits_of_basisTransform hdeg hmonic hpres

end RealRooted
