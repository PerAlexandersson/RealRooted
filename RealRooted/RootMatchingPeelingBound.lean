import RealRooted.RootMatchingPeeling
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Root-Matching Peeling: coefficient-difference bound

This file harvests the two synthetic-division recurrences from
`RealRooted.RootMatchingPeeling` into a genuine coefficient-control bound for the
issue #42 multiplicity-preserving root-matching route.

After peeling one nearby monic linear factor from each of `f = (X - C r) * fTail`
and `p = (X - C q) * pTail`, the recurrence

`pTail.coeff k - fTail.coeff k
  = (p.coeff (k+1) - f.coeff (k+1))
      + q * (pTail.coeff (k+1) - fTail.coeff (k+1))
      + (q - r) * fTail.coeff (k+1)`

lets us propagate a per-coefficient perturbation bound `εc` and a coefficient
size bound `M` on the target tail into an explicit geometric bound on the
quotient-difference coefficients.  This is precisely the analytic estimate needed
to control root clusters as the peel proceeds.
-/

open Polynomial

namespace RealRooted
namespace RootMatchingPeeling

private theorem geom_sum_abs_pow_le_card_mul_max_of_abs_le
    {q R : ℝ} {d k : ℕ} (hR : |q| ≤ R) :
    (∑ i ∈ Finset.range (d + 1 - k), |q| ^ i) ≤
      (d + 1 : ℝ) * max 1 (R ^ d) := by
  have hterm : ∀ i ∈ Finset.range (d + 1 - k), |q| ^ i ≤ max 1 (R ^ d) := by
    intro i hi
    have hi_le_d : i ≤ d := by
      exact Nat.lt_succ_iff.mp <| by
        simpa [Nat.succ_eq_add_one] using
          lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.sub_le (d + 1) k)
    by_cases hR1 : R ≤ 1
    · have hq1 : |q| ≤ 1 := le_trans hR hR1
      exact (pow_le_one₀ (abs_nonneg q) hq1).trans (le_max_left _ _)
    · have h1R : 1 ≤ R := (lt_of_not_ge hR1).le
      exact ((pow_le_pow_left₀ (abs_nonneg q) hR i).trans
        (pow_le_pow_right₀ h1R hi_le_d)).trans (le_max_right _ _)
  calc
    (∑ i ∈ Finset.range (d + 1 - k), |q| ^ i)
        ≤ ∑ _i ∈ Finset.range (d + 1 - k), max 1 (R ^ d) :=
      Finset.sum_le_sum hterm
    _ = ((d + 1 - k : ℕ) : ℝ) * max 1 (R ^ d) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (d + 1 : ℝ) * max 1 (R ^ d) := by
      have hcard : ((d + 1 - k : ℕ) : ℝ) ≤ d + 1 := by
        exact_mod_cast Nat.sub_le (d + 1) k
      exact mul_le_mul_of_nonneg_right hcard (by positivity)

/--
Coefficient-difference bound after peeling one monic linear factor from each of
`f = (X - C r) * fTail` and `p = (X - C q) * pTail`.

If every coefficient of `p` differs from that of `f` by at most `εc`, and every
coefficient of the target tail `fTail` is bounded by `M`, and both tails have
degree at most `d`, then the quotient-difference coefficients obey the geometric
bound

`|pTail.coeff k - fTail.coeff k|
    ≤ (εc + |q - r| * M) * ∑ i ∈ range (d + 1 - k), |q| ^ i`.

The proof is a downward induction over the coefficient index driven by
`coeff_sub_recursion`, with the geometric factor supplied by `geom_sum_succ`.
-/
theorem coeff_sub_div_linear_bound {f fTail p pTail : ℝ[X]} {r q : ℝ} {d : ℕ}
    {εc M : ℝ}
    (hf : f = (X - C r) * fTail) (hp : p = (X - C q) * pTail)
    (hfd : fTail.natDegree ≤ d) (hpd : pTail.natDegree ≤ d)
    (hcoeff : ∀ k, |p.coeff k - f.coeff k| ≤ εc)
    (hM : ∀ k, |fTail.coeff k| ≤ M) :
    ∀ k, |pTail.coeff k - fTail.coeff k| ≤
      (εc + |q - r| * M) * ∑ i ∈ Finset.range (d + 1 - k), |q| ^ i := by
  have H : ∀ n k, d + 1 ≤ k + n →
      |pTail.coeff k - fTail.coeff k| ≤
        (εc + |q - r| * M) *
          ∑ i ∈ Finset.range (d + 1 - k), |q| ^ i := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have hdk : d < k := hk
      have hfk : fTail.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hfd hdk)
      have hpk : pTail.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpd hdk)
      have hzero : d + 1 - k = 0 := Nat.sub_eq_zero_of_le hk
      rw [hfk, hpk, hzero]
      simp
    | succ n ih =>
      intro k hk
      by_cases hkd : k ≤ d
      · have hkn : d + 1 ≤ (k + 1) + n := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk
        have ihk := ih (k + 1) hkn
        have hsub : d + 1 - k = (d + 1 - (k + 1)) + 1 := by
          simpa using Nat.succ_sub hkd
        rw [hsub, geom_sum_succ]
        set Sn := ∑ i ∈ Finset.range (d + 1 - (k + 1)), |q| ^ i with hSn
        have hrec := coeff_sub_recursion hf hp k
        set A := p.coeff (k + 1) - f.coeff (k + 1) with hA
        set Dk1 := pTail.coeff (k + 1) - fTail.coeff (k + 1) with hDk1
        set Fk1 := fTail.coeff (k + 1) with hFk1
        calc |pTail.coeff k - fTail.coeff k|
            = |A + q * Dk1 + (q - r) * Fk1| := by rw [hrec]
          _ ≤ |A + q * Dk1| + |(q - r) * Fk1| := abs_add_le _ _
          _ ≤ (|A| + |q * Dk1|) + |(q - r) * Fk1| :=
                add_le_add (abs_add_le _ _) (le_refl _)
          _ = |A| + |q| * |Dk1| + |q - r| * |Fk1| := by rw [abs_mul, abs_mul]
          _ ≤ εc + |q| * ((εc + |q - r| * M) * Sn) + |q - r| * M := by
                gcongr <;>
                  first
                    | exact hcoeff (k + 1)
                    | exact ihk
                    | exact hM (k + 1)
          _ = (εc + |q - r| * M) * (|q| * Sn + 1) := by ring
      · have hk' : d + 1 ≤ k := lt_of_not_ge hkd
        exact ih k (le_trans hk' (Nat.le_add_right k n))
  intro k
  exact H (d + 1) k (Nat.le_add_left (d + 1) k)

/--
Uniform coefficient-difference bound after one peeling step.

This packages `coeff_sub_div_linear_bound` into the form needed for an
epsilon-delta argument: when the selected root `q` stays in a fixed bounded
region `|q| ≤ R`, the geometric factor is controlled by the single finite
constant `(d + 1) * max 1 (R ^ d)`.
-/
theorem coeff_sub_div_linear_bound_uniform
    {f fTail p pTail : ℝ[X]} {r q R : ℝ} {d : ℕ} {εc M : ℝ}
    (hf : f = (X - C r) * fTail) (hp : p = (X - C q) * pTail)
    (hfd : fTail.natDegree ≤ d) (hpd : pTail.natDegree ≤ d)
    (hcoeff : ∀ k, |p.coeff k - f.coeff k| ≤ εc)
    (hM : ∀ k, |fTail.coeff k| ≤ M) (hqR : |q| ≤ R) :
    ∀ k, |pTail.coeff k - fTail.coeff k| ≤
      (εc + |q - r| * M) * ((d + 1 : ℝ) * max 1 (R ^ d)) := by
  have hεc_nonneg : 0 ≤ εc :=
    le_trans (abs_nonneg (p.coeff 0 - f.coeff 0)) (hcoeff 0)
  have hM_nonneg : 0 ≤ M :=
    le_trans (abs_nonneg (fTail.coeff 0)) (hM 0)
  have hfactor_nonneg : 0 ≤ εc + |q - r| * M :=
    add_nonneg hεc_nonneg (mul_nonneg (abs_nonneg (q - r)) hM_nonneg)
  intro k
  exact (coeff_sub_div_linear_bound hf hp hfd hpd hcoeff hM k).trans
    (mul_le_mul_of_nonneg_left
      (geom_sum_abs_pow_le_card_mul_max_of_abs_le (q := q) (R := R) (d := d)
        (k := k) hqR)
      hfactor_nonneg)

/--
Single-parameter uniform coefficient-difference bound after one peeling step.

If the coefficient error of `p` from `f` and the selected root error `|q - r|`
are both bounded by the same small parameter `η`, then the quotient coefficient
error is bounded by `η` times a fixed constant.  This is the form needed for the
inductive small-parameter peeling argument for repeated root clusters.
-/
theorem coeff_sub_div_linear_bound_uniform_single_eps
    {f fTail p pTail : ℝ[X]} {r q R : ℝ} {d : ℕ} {η M : ℝ}
    (hf : f = (X - C r) * fTail) (hp : p = (X - C q) * pTail)
    (hfd : fTail.natDegree ≤ d) (hpd : pTail.natDegree ≤ d)
    (hcoeff : ∀ k, |p.coeff k - f.coeff k| ≤ η)
    (hq : |q - r| ≤ η) (hM : ∀ k, |fTail.coeff k| ≤ M)
    (hqR : |q| ≤ R) :
    ∀ k, |pTail.coeff k - fTail.coeff k| ≤
      η * (1 + M) * ((d + 1 : ℝ) * max 1 (R ^ d)) := by
  have hM_nonneg : 0 ≤ M :=
    le_trans (abs_nonneg (fTail.coeff 0)) (hM 0)
  have hfactor : η + |q - r| * M ≤ η * (1 + M) := by
    linarith [mul_le_mul_of_nonneg_right hq hM_nonneg]
  intro k
  exact (coeff_sub_div_linear_bound_uniform hf hp hfd hpd hcoeff hM hqR k).trans
    (mul_le_mul_of_nonneg_right hfactor (by positivity))

/--
Epsilon form of the uniform one-step peeling estimate.

For any target coefficient tolerance `ε > 0`, there is a positive tolerance
`η` such that coefficient closeness of `p` to `f` by `η`, together with
`|q - r| ≤ η`, forces the peeled quotient coefficients to be `ε`-close.  This
is the local continuity input needed to iterate the peeling argument.
-/
theorem exists_pos_eta_coeff_sub_div_linear_bound_uniform
    {f fTail : ℝ[X]} {r R : ℝ} {d : ℕ} {ε M : ℝ}
    (hf : f = (X - C r) * fTail) (hfd : fTail.natDegree ≤ d)
    (hM : ∀ k, |fTail.coeff k| ≤ M) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ {p pTail : ℝ[X]} {q : ℝ},
      (p = (X - C q) * pTail) → pTail.natDegree ≤ d →
      (∀ k, |p.coeff k - f.coeff k| ≤ η) → |q - r| ≤ η → |q| ≤ R →
      ∀ k, |pTail.coeff k - fTail.coeff k| ≤ ε := by
  let C₀ : ℝ := (1 + M) * ((d + 1 : ℝ) * max 1 (R ^ d))
  have hM_nonneg : 0 ≤ M :=
    le_trans (abs_nonneg (fTail.coeff 0)) (hM 0)
  have hC₀_nonneg : 0 ≤ C₀ := by positivity
  let η : ℝ := ε / (C₀ + 1)
  have hden_pos : 0 < C₀ + 1 := by linarith
  have hη_pos : 0 < η := div_pos hε hden_pos
  have hηC₀ : η * C₀ ≤ ε := by
    have hleft : η * C₀ ≤ η * (C₀ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hη_pos.le
    have hright : η * (C₀ + 1) = ε := by
      dsimp [η]
      field_simp [ne_of_gt hden_pos]
    linarith
  refine ⟨η, hη_pos, ?_⟩
  intro p pTail q hp hpd hcoeff hq hqR k
  have hbound :=
    coeff_sub_div_linear_bound_uniform_single_eps
      (fTail := fTail) hf hp hfd hpd hcoeff hq hM hqR k
  have hboundC : |pTail.coeff k - fTail.coeff k| ≤ η * C₀ := by
    simpa [C₀, mul_assoc] using hbound
  exact hboundC.trans hηC₀

/--
Coefficientwise continuity of the peeled tail under one matched linear peel.

This is the first direct continuity consequence of the explicit peeling
estimate.  If the original polynomials converge uniformly coefficientwise to
`f`, the selected roots `q i` converge to `r`, the quotient degrees stay bounded
by `d`, and the selected roots stay in a fixed bounded region, then every
coefficient of the peeled quotient converges to the corresponding coefficient
of `fTail`.
-/
theorem tendsto_coeff_tail_of_uniform_coeff_and_root
    {ι : Type*} {l : Filter ι} {f fTail : ℝ[X]} {r R : ℝ} {d : ℕ} {M : ℝ}
    (hf : f = (X - C r) * fTail) (hfd : fTail.natDegree ≤ d)
    (hM : ∀ k, |fTail.coeff k| ≤ M)
    {p pTail : ι → ℝ[X]} {q : ι → ℝ}
    (hp : ∀ᶠ i in l, p i = (X - C (q i)) * pTail i)
    (hpd : ∀ᶠ i in l, (pTail i).natDegree ≤ d)
    (hcoeff : ∀ ε > 0, ∀ᶠ i in l, ∀ k,
      |(p i).coeff k - f.coeff k| ≤ ε)
    (hq : Filter.Tendsto q l (nhds r))
    (hqR : ∀ᶠ i in l, |q i| ≤ R) :
    ∀ k, Filter.Tendsto (fun i => (pTail i).coeff k) l (nhds (fTail.coeff k)) := by
  intro k
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη_pos, hη⟩ :=
    exists_pos_eta_coeff_sub_div_linear_bound_uniform
      (fTail := fTail) hf hfd hM (half_pos hε)
  have hqη : ∀ᶠ i in l, |q i - r| ≤ η := by
    exact ((Metric.tendsto_nhds.mp hq) η hη_pos).mono fun i hi => by
      simpa [Real.dist_eq] using hi.le
  filter_upwards [hp, hpd, hcoeff η hη_pos, hqη, hqR] with i hpi hpdi hcoeffi hqi hqRi
  have hclose : |(pTail i).coeff k - fTail.coeff k| ≤ ε / 2 :=
    hη hpi hpdi hcoeffi hqi hqRi k
  rw [Real.dist_eq]
  linarith

/--
Coefficientwise continuity of the peeled tail from a single perturbation
modulus.

This is the modulus form used in a peeling induction: if one function `η i`
controls both coefficient errors and selected-root errors, and `η i → 0`, then
the peeled quotient coefficients converge to the target tail coefficients.
-/
theorem tendsto_coeff_tail_of_modulus
    {ι : Type*} {l : Filter ι} {f fTail : ℝ[X]} {r R : ℝ} {d : ℕ} {M : ℝ}
    (hf : f = (X - C r) * fTail) (hfd : fTail.natDegree ≤ d)
    (hM : ∀ k, |fTail.coeff k| ≤ M)
    {p pTail : ι → ℝ[X]} {q η : ι → ℝ}
    (hp : ∀ᶠ i in l, p i = (X - C (q i)) * pTail i)
    (hpd : ∀ᶠ i in l, (pTail i).natDegree ≤ d)
    (hcoeff : ∀ᶠ i in l, ∀ k, |(p i).coeff k - f.coeff k| ≤ η i)
    (hq : ∀ᶠ i in l, |q i - r| ≤ η i)
    (hqR : ∀ᶠ i in l, |q i| ≤ R)
    (hη : Filter.Tendsto η l (nhds 0)) :
    ∀ k, Filter.Tendsto (fun i => (pTail i).coeff k) l (nhds (fTail.coeff k)) := by
  intro k
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    exists_pos_eta_coeff_sub_div_linear_bound_uniform
      (fTail := fTail) hf hfd hM (half_pos hε)
  have hηδ : ∀ᶠ i in l, η i ≤ δ := by
    exact ((Metric.tendsto_nhds.mp hη) δ hδ_pos).mono fun i hi => by
      exact le_of_lt <| (abs_lt.mp (by simpa [Real.dist_eq] using hi)).2
  filter_upwards [hp, hpd, hcoeff, hq, hqR, hηδ] with
    i hpi hpdi hcoeffi hqi hqRi hηi
  have hcoeffδ : ∀ j, |(p i).coeff j - f.coeff j| ≤ δ :=
    fun j => le_trans (hcoeffi j) hηi
  have hqδ : |q i - r| ≤ δ := le_trans hqi hηi
  have hclose : |(pTail i).coeff k - fTail.coeff k| ≤ ε / 2 :=
    hδ hpi hpdi hcoeffδ hqδ hqRi k
  rw [Real.dist_eq]
  linarith

/--
Uniform coefficient closeness of peeled tails from a single perturbation modulus.

Since both peeled tails have degree at most `d`, coefficientwise convergence on
the finite set `range (d + 1)` upgrades to eventual `∀ k` coefficient closeness.
This is the form needed to feed the next induction step in the repeated-root
peeling route.
-/
theorem eventually_forall_coeff_tail_close_of_modulus
    {ι : Type*} {l : Filter ι} {f fTail : ℝ[X]} {r R : ℝ} {d : ℕ} {M : ℝ}
    (hf : f = (X - C r) * fTail) (hfd : fTail.natDegree ≤ d)
    (hM : ∀ k, |fTail.coeff k| ≤ M)
    {p pTail : ι → ℝ[X]} {q η : ι → ℝ}
    (hp : ∀ᶠ i in l, p i = (X - C (q i)) * pTail i)
    (hpd : ∀ᶠ i in l, (pTail i).natDegree ≤ d)
    (hcoeff : ∀ᶠ i in l, ∀ k, |(p i).coeff k - f.coeff k| ≤ η i)
    (hq : ∀ᶠ i in l, |q i - r| ≤ η i)
    (hqR : ∀ᶠ i in l, |q i| ≤ R)
    (hη : Filter.Tendsto η l (nhds 0)) :
    ∀ ε > 0, ∀ᶠ i in l, ∀ k, |(pTail i).coeff k - fTail.coeff k| ≤ ε := by
  intro ε hε
  have hcoeff_tendsto :=
    tendsto_coeff_tail_of_modulus hf hfd hM hp hpd hcoeff hq hqR hη
  have hfinite : ∀ᶠ i in l, ∀ k ∈ Finset.range (d + 1),
      |(pTail i).coeff k - fTail.coeff k| ≤ ε := by
    rw [Filter.eventually_all_finset]
    intro k hk
    exact ((Metric.tendsto_nhds.mp (hcoeff_tendsto k)) ε hε).mono fun i hi => by
      simpa [Real.dist_eq] using hi.le
  filter_upwards [hfinite, hpd] with i hfinite_i hpdi k
  by_cases hk : k ≤ d
  · exact hfinite_i k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · have hdk : d < k := lt_of_not_ge hk
    have hfk : fTail.coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hfd hdk)
    have hpk : (pTail i).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdi hdk)
    simp [hfk, hpk, hε.le]

end RootMatchingPeeling
end RealRooted
