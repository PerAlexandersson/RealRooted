import RealRooted.Kurtz
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure

/-!
# Hutchinson's theorem

Hutchinson (1923): if `a k > 0` and `4 a_k a_{k+2} ≤ a_{k+1}^2` for all `k`, then the entire
function `∑ a_k z^k` lies in the Laguerre–Pólya class.

We approximate `∑ a_k z^k` on a disc by a partial sum `∑_{k<N} a_k z^k`, and that partial sum
by `∑_{k<N} a_k q^{k^2} z^k` with `q < 1` close to `1`.  The perturbed coefficients satisfy
the strict inequalities of Kurtz's theorem (`Kurtz.coefficient_criterion`), so these
polynomials are real-rooted.

## References

* J. I. Hutchinson, *On a remarkable class of entire functions*, Trans. Amer. Math. Soc. 25
  (1923), 325–332.
* D. C. Kurtz, *A sufficient condition for all the roots of a polynomial to be real*, Amer.
  Math. Monthly 99 (1992), 259–263.
-/

open Polynomial Filter

namespace RealRooted

/-- Coefficients of the truncated series `∑_{k<N} b_k X^k`. -/
private theorem coeff_sum_range_C_mul_X_pow (b : ℕ → ℝ) (N i : ℕ) :
    (∑ k ∈ Finset.range N, C (b k) * X ^ k).coeff i = if i < N then b i else 0 := by
  simp

/-- By Kurtz's theorem, a polynomial `∑_{k<N} b_k X^k` with positive coefficients satisfying
the strict inequalities `4 b_k b_{k+2} < b_{k+1}^2` is zero or splits over `ℝ`. -/
theorem sum_range_C_mul_X_pow_eq_zero_or_splits
    {b : ℕ → ℝ} (hb : ∀ k, 0 < b k) (hs : ∀ k, 4 * b k * b (k + 2) < b (k + 1) ^ 2) (N : ℕ) :
    (∑ k ∈ Finset.range N, C (b k) * X ^ k) = 0 ∨
      (∑ k ∈ Finset.range N, C (b k) * X ^ k).Splits := by
  set T := ∑ k ∈ Finset.range N, C (b k) * X ^ k
  have hc : ∀ i, T.coeff i = if i < N then b i else 0 := coeff_sum_range_C_mul_X_pow b N
  right
  rcases le_or_gt T.natDegree 1 with h1 | h2
  · exact Splits.of_natDegree_le_one h1
  have hT0 : T ≠ 0 := by
    rintro h
    rw [h, natDegree_zero] at h2
    lia
  have hdeg : T.natDegree < N := by
    by_contra hge
    have := hc T.natDegree
    rw [ite_eq_right hge] at this
    exact hT0 (leadingCoeff_eq_zero.mp this)
  have hci : ∀ i ≤ T.natDegree, T.coeff i = b i := fun i hi => by
    rw [hc, ite_eq_left (by lia)]
  refine Kurtz.coefficient_criterion h2 (fun i hi => (hci i hi).symm ▸ hb i) ?_
  intro i hi0 hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by lia⟩
  rw [hci _ (by lia), hci _ (by lia), hci _ (by lia), Nat.add_sub_cancel]
  exact hs j

namespace Hutchinson

open Topology

variable {a : ℕ → ℝ}

/-- The ratio bound `a_{k+1} / a_k ≤ (a_1 / a_0) / 4^k`, in multiplied-out form. -/
theorem mul_pow_le (ha : ∀ k, 0 < a k) (h : ∀ k, 4 * a k * a (k + 2) ≤ a (k + 1) ^ 2)
    (k : ℕ) : a (k + 1) * a 0 * 4 ^ k ≤ a 1 * a k := by
  induction k with
  | zero => rw [pow_zero, mul_one, mul_comm]
  | succ k ih =>
    have hk := ha k
    have h1 := ha (k + 1)
    have h0 := ha 0
    have key : a k * (a (k + 2) * a 0 * 4 ^ (k + 1)) ≤ a k * (a 1 * a (k + 1)) :=
      calc a k * (a (k + 2) * a 0 * 4 ^ (k + 1)) = (4 * a k * a (k + 2)) * (a 0 * 4 ^ k) := by
            ring
        _ ≤ a (k + 1) ^ 2 * (a 0 * 4 ^ k) := mul_le_mul_of_nonneg_right (h k) (by positivity)
        _ = a (k + 1) * (a (k + 1) * a 0 * 4 ^ k) := by ring
        _ ≤ a (k + 1) * (a 1 * a k) := mul_le_mul_of_nonneg_left ih h1.le
        _ = a k * (a 1 * a (k + 1)) := by ring
    exact le_of_mul_le_mul_left key hk

/-- Under Hutchinson's inequalities, `∑ a_k ρ^k` converges for every `ρ ≥ 0`. -/
theorem summable_mul_pow (ha : ∀ k, 0 < a k) (h : ∀ k, 4 * a k * a (k + 2) ≤ a (k + 1) ^ 2)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : Summable fun k => a k * ρ ^ k := by
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  have ht : Tendsto (fun k : ℕ => (4 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [ht.eventually_ge_atTop (2 * a 1 * ρ / a 0)] with k hk
  have h0 := ha 0
  have h1 := ha 1
  have hk0 := ha k
  have hk1 := ha (k + 1)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have hk' : 2 * a 1 * ρ ≤ a 0 * 4 ^ k := by
    rw [div_le_iff₀ h0] at hk
    linarith
  have key : (a 0 * 4 ^ k) * (a (k + 1) * ρ ^ (k + 1)) ≤ (a 0 * 4 ^ k) * (1 / 2 * (a k * ρ ^ k)) :=
    calc (a 0 * 4 ^ k) * (a (k + 1) * ρ ^ (k + 1)) = (a (k + 1) * a 0 * 4 ^ k) * (ρ * ρ ^ k) := by
          ring
      _ ≤ (a 1 * a k) * (ρ * ρ ^ k) :=
          mul_le_mul_of_nonneg_right (mul_pow_le ha h k) (by positivity)
      _ = (2 * a 1 * ρ) * (1 / 2 * (a k * ρ ^ k)) := by ring
      _ ≤ (a 0 * 4 ^ k) * (1 / 2 * (a k * ρ ^ k)) :=
          mul_le_mul_of_nonneg_right hk' (by positivity)
  exact le_of_mul_le_mul_left key (by positivity)

/-- **Hutchinson's theorem** (1923).  If `a k > 0` and `4 a_k a_{k+2} ≤ a_{k+1}^2` for all `k`,
then `∑ a_k z^k` is an entire function in the Laguerre–Pólya class.  Kurtz's theorem on real
polynomials with strict coefficient inequalities supplies the real-rooted approximants. -/
theorem isLaguerrePolya_tsum
    (ha : ∀ k, 0 < a k) (h : ∀ k, 4 * a k * a (k + 2) ≤ a (k + 1) ^ 2) :
    IsLaguerrePolya fun z : ℂ => ∑' k, (a k : ℂ) * z ^ k := by
  refine IsLaguerrePolya.of_forall_approx fun R ε hε => ?_
  set ρ := max R 0
  have hρ0 : 0 ≤ ρ := le_max_right R 0
  have hzρ : ∀ z : ℂ, ‖z‖ ≤ R → ∀ k : ℕ, ‖z‖ ^ k ≤ ρ ^ k := fun z hz k =>
    pow_le_pow_left₀ (norm_nonneg z) (hz.trans (le_max_left R 0)) k
  have hU : TendstoUniformlyOn (fun N z => ∑ k ∈ Finset.range N, (a k : ℂ) * z ^ k)
      (fun z => ∑' k, (a k : ℂ) * z ^ k) atTop (Metric.closedBall 0 R) := by
    refine tendstoUniformlyOn_tsum_nat (summable_mul_pow ha h hρ0) fun k z hz => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (ha k).le]
    exact mul_le_mul_of_nonneg_left (hzρ z (mem_closedBall_zero_iff.mp hz) k) (ha k).le
  rw [Metric.tendstoUniformlyOn_iff] at hU
  obtain ⟨N, hN⟩ := (hU (ε / 2) (half_pos hε)).exists
  set g : ℝ → ℝ := fun q => ∑ k ∈ Finset.range N, (a k - a k * q ^ (k ^ 2)) * ρ ^ k
  have hgt : Tendsto g (𝓝[<] 1) (𝓝 0) := by
    have hc : Continuous g := by fun_prop
    have h1 : g 1 = 0 := by simp [g]
    rw [← h1]
    exact (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  obtain ⟨q, hgq, hq⟩ := ((hgt.eventually (gt_mem_nhds (half_pos hε))).and
    (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num))).exists
  set b : ℕ → ℝ := fun k => a k * q ^ (k ^ 2)
  have hbpos : ∀ k, 0 < b k := fun k => mul_pos (ha k) (pow_pos hq.1 _)
  have hs : ∀ k, 4 * b k * b (k + 2) < b (k + 1) ^ 2 := by
    intro k
    have hlt : q ^ (k ^ 2 + (k + 2) ^ 2) < q ^ (2 * (k + 1) ^ 2) :=
      pow_lt_pow_right_of_lt_one₀ hq.1 hq.2 (by nlinarith)
    have hq0 := hq.1
    have hk1 := ha (k + 1)
    calc 4 * b k * b (k + 2) = (4 * a k * a (k + 2)) * q ^ (k ^ 2 + (k + 2) ^ 2) := by
          simp only [b]
          ring
      _ ≤ a (k + 1) ^ 2 * q ^ (k ^ 2 + (k + 2) ^ 2) :=
          mul_le_mul_of_nonneg_right (h k) (by positivity)
      _ < a (k + 1) ^ 2 * q ^ (2 * (k + 1) ^ 2) := mul_lt_mul_of_pos_left hlt (by positivity)
      _ = b (k + 1) ^ 2 := by
          simp only [b]
          ring
  refine ⟨∑ k ∈ Finset.range N, C (b k) * X ^ k,
    sum_range_C_mul_X_pow_eq_zero_or_splits hbpos hs N, fun z hz => ?_⟩
  have heval : ((∑ k ∈ Finset.range N, C (b k) * X ^ k).map Complex.ofRealHom).eval z =
      ∑ k ∈ Finset.range N, (b k : ℂ) * z ^ k := by
    rw [Polynomial.map_sum, eval_finsetSum]
    simp
  rw [heval]
  have hfin : dist (∑ k ∈ Finset.range N, (a k : ℂ) * z ^ k)
      (∑ k ∈ Finset.range N, (b k : ℂ) * z ^ k) ≤ g q := by
    rw [dist_eq_norm, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have hqk : q ^ (k ^ 2) ≤ 1 := pow_le_one₀ hq.1.le hq.2.le
    have hnn : 0 ≤ a k - a k * q ^ (k ^ 2) := by
      nlinarith [ha k]
    have hcast : (a k : ℂ) * z ^ k - (b k : ℂ) * z ^ k =
        ((a k - a k * q ^ (k ^ 2) : ℝ) : ℂ) * z ^ k := by
      simp only [b]
      push_cast
      ring
    rw [hcast, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left (hzρ z hz k) hnn
  calc dist (∑' k, (a k : ℂ) * z ^ k) (∑ k ∈ Finset.range N, (b k : ℂ) * z ^ k)
      ≤ dist (∑' k, (a k : ℂ) * z ^ k) (∑ k ∈ Finset.range N, (a k : ℂ) * z ^ k) +
        dist (∑ k ∈ Finset.range N, (a k : ℂ) * z ^ k)
          (∑ k ∈ Finset.range N, (b k : ℂ) * z ^ k) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 :=
        add_lt_add_of_lt_of_le (hN z (mem_closedBall_zero_iff.mpr hz)) (hfin.trans hgq.le)
    _ = ε := add_halves ε

end Hutchinson

end RealRooted
