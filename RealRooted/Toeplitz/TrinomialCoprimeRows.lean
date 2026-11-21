module

public import RealRooted.Toeplitz.TrinomialRows
public import RealRooted.Toeplitz.TrinomialBinomialRay
public import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Nat.ModEq
import Mathlib.Analysis.Complex.Polynomial.Basic
import RealRooted.Mathlib.Algebra.Polynomial.Splits.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Coprime-lag rows and binomial rays

We identify the coefficients of `1 / (1 - X t^ℓ - t^k)` with a binomial ray.
The reduction is the proof of Bøgvad--Ndikubwayo--Shapiro,
*Generalizing Tran's Conjecture*, arXiv:2001.09248v2, Theorem 1.2.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted.Trinomial

/-- The universal two-lag rows are the literal two-kernel coefficient rows. -/
theorem row_eq_twoKernelRow {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hk : k ≠ 0) (n : ℕ) :
    row ℓ k (-1 : ℝ[X]) (-X) n = BrandenLeite.twoKernelRow
      (PowerSeries.expand k hk (PowerSeries.mk (1 : ℕ → ℝ)))
      (PowerSeries.X ^ ℓ) n := by
  let g : PowerSeries ℝ := PowerSeries.expand k hk (PowerSeries.mk (1 : ℕ → ℝ))
  let h : PowerSeries ℝ := PowerSeries.X ^ ℓ
  let F := BrandenLeite.twoKernelGeneratingSeries g h
  have hg : (1 - PowerSeries.X ^ k) * g = 1 := by
    have he := congrArg (PowerSeries.expand k hk)
      (PowerSeries.mk_one_mul_one_sub_eq_one ℝ)
    simpa [g, map_sub, PowerSeries.expand_X, mul_comm] using he
  have hg' : BrandenLeite.polynomialLift (1 - PowerSeries.X ^ k) *
      BrandenLeite.polynomialLift g = 1 := by
    rw [← BrandenLeite.polynomialLift_mul, hg, BrandenLeite.polynomialLift_one]
  have heq : BrandenLeite.polynomialLift (1 - PowerSeries.X ^ k) *
      (1 - PowerSeries.C X * BrandenLeite.polynomialLift (g * h)) =
      denominator ℓ k (-1 : ℝ[X]) (-X) := by
    rw [BrandenLeite.polynomialLift_mul]
    calc
      _ = BrandenLeite.polynomialLift (1 - PowerSeries.X ^ k) - PowerSeries.C X *
          (BrandenLeite.polynomialLift (1 - PowerSeries.X ^ k) *
            BrandenLeite.polynomialLift g) * BrandenLeite.polynomialLift h := by ring
      _ = BrandenLeite.polynomialLift (1 - PowerSeries.X ^ k) -
          PowerSeries.C X * BrandenLeite.polynomialLift h := by rw [hg']; ring
      _ = _ := by
        have hXL (m : ℕ) : BrandenLeite.polynomialLift ((PowerSeries.X : PowerSeries ℝ) ^ m) =
            (PowerSeries.X : PowerSeries ℝ[X]) ^ m := by
          ext d
          simp [BrandenLeite.coeff_polynomialLift, PowerSeries.coeff_X_pow]
        dsimp [h]
        rw [BrandenLeite.polynomialLift_sub, BrandenLeite.polynomialLift_one, hXL, hXL]
        simp only [denominator, map_neg, map_one]
        ring
  have hF : denominator ℓ k (-1 : ℝ[X]) (-X) * F = 1 := by
    rw [← heq, mul_assoc, BrandenLeite.one_sub_mul_twoKernelGeneratingSeries
      (by simp [h, hℓ])]
    exact hg'
  have hs := rowSeries_eq_of_mul_eq_one hℓ hk (-1 : ℝ[X]) (-X) hF
  have hc := congrArg (PowerSeries.coeff n) hs
  simpa [row, F, g, h, BrandenLeite.coeff_twoKernelGeneratingSeries] using hc.symm

/-- A universal row coefficient counts the solutions with the given number of short steps. -/
theorem coeff_row {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hk : k ≠ 0) (n i : ℕ) :
    (row ℓ k (-1 : ℝ[X]) (-X) n).coeff i =
      if ℓ * i ≤ n ∧ k ∣ n - ℓ * i then
        (((i + (n - ℓ * i) / k).choose i : ℕ) : ℝ) else 0 := by
  rw [row_eq_twoKernelRow hℓ hk, BrandenLeite.coeff_twoKernelRow (by simp [hℓ])]
  rw [← pow_mul, mul_comm, PowerSeries.coeff_X_pow_mul']
  by_cases h : ℓ * i ≤ n
  · rw [ite_eq_left h, ← map_pow, PowerSeries.coeff_expand,
      PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_mk]
    simp [h]
  · simp [h]

private theorem shortIndex_of_decomposition {ℓ k i₀ j₀ i j : ℕ}
    (hk : k ≠ 0) (hcop : ℓ.Coprime k) (hi₀ : i₀ < k)
    (hn : ℓ * i + k * j = ℓ * i₀ + k * j₀) :
    ∃ u, i = i₀ + k * u ∧ j₀ = j + ℓ * u := by
  have hmod : ℓ * i ≡ ℓ * i₀ [MOD k] := by
    have h := congrArg (fun m ↦ m % k) hn
    simpa [Nat.ModEq, Nat.add_mod, Nat.mul_mod] using h
  have himod : i % k = i₀ := by
    have h := Nat.ModEq.cancel_left_of_coprime hcop.symm hmod
    change i % k = i₀ % k at h
    exact h.trans (Nat.mod_eq_of_lt hi₀)
  have hi : i = i₀ + k * (i / k) := by
    have h := Nat.mod_add_div i k
    rw [himod] at h
    exact h.symm
  refine ⟨i / k, hi, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (show 0 < k by lia)
  rw [hi] at hn
  nlinarith

private theorem coeff_expand_mul_X_pow (k i u : ℕ) (hk : 0 < k) (p : ℝ[X]) :
    (X ^ i * expand ℝ k p).coeff (i + k * u) = p.coeff u := by
  rw [add_comm i, coeff_X_pow_mul, coeff_expand_mul' hk]

/-- The universal row is a monomial times a binomial ray evaluated at the `k`th power.
The indices enumerate all nonnegative solutions of `ℓ i + k j = n`. -/
theorem row_eq_X_pow_mul_expand_binomialRay {ℓ k i₀ j₀ : ℕ}
    (hℓ : ℓ ≠ 0) (hℓk : ℓ < k) (hcop : ℓ.Coprime k) (hi₀ : i₀ < k) :
    row ℓ k (-1 : ℝ[X]) (-X) (ℓ * i₀ + k * j₀) =
      X ^ i₀ * expand ℝ k (binomialRay (i₀ + j₀) i₀ (k - ℓ) k) := by
  have hk : k ≠ 0 := by lia
  have hdiff : k - ℓ + ℓ = k := Nat.sub_add_cancel hℓk.le
  have hcoeff (u : ℕ) := coeff_binomialRay (by lia : i₀ ≤ i₀ + j₀)
    (by lia : k - ℓ < k) hi₀ u
  ext m
  rw [coeff_row hℓ hk]
  split_ifs with hcond
  · let j := (ℓ * i₀ + k * j₀ - ℓ * m) / k
    have hdecomp : ℓ * m + k * j = ℓ * i₀ + k * j₀ := by
      dsimp [j]
      rw [Nat.mul_div_cancel' hcond.2]
      exact Nat.add_sub_of_le hcond.1
    obtain ⟨u, hm, hj⟩ := shortIndex_of_decomposition hk hcop hi₀ hdecomp
    change ((m + j).choose m : ℝ) = _
    rw [hm, coeff_expand_mul_X_pow k i₀ u (by lia), hcoeff]
    have htop : i₀ + k * u + j = i₀ + j₀ + (k - ℓ) * u := by nlinarith
    rw [htop]
  · rw [coeff_X_pow_mul']
    split_ifs with hm
    · rw [coeff_expand (by lia : 0 < k)]
      split_ifs with hdiv
      · let u := (m - i₀) / k
        have hmul : k * u = m - i₀ := Nat.mul_div_cancel' hdiv
        have hmu : m = i₀ + k * u := by lia
        have hju : j₀ < ℓ * u := by
          by_contra hju
          have hsub : j₀ - ℓ * u + ℓ * u = j₀ := Nat.sub_add_cancel (by lia)
          have heq : ℓ * i₀ + k * j₀ = ℓ * m + k * (j₀ - ℓ * u) := by
            rw [hmu]
            nlinarith
          apply hcond
          refine ⟨by nlinarith, ?_⟩
          rw [heq, Nat.add_sub_cancel_left]
          exact dvd_mul_right k _
        rw [hcoeff]
        have hlt : i₀ + j₀ + (k - ℓ) * u < i₀ + k * u := by nlinarith
        rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
      · rfl
    · rfl

private theorem pow_normalized_coefficient {ℓ k : ℕ} (hℓk : ℓ ≤ k)
    {a b c : ℂ} (hc : c ^ k = -a⁻¹) :
    (-b * c ^ ℓ) ^ k = (-1 : ℂ) ^ (k - ℓ) * b ^ k / a ^ ℓ := by
  have hcpow : (c ^ ℓ) ^ k = (c ^ k) ^ ℓ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hnb : (-b) ^ k = (-1 : ℂ) ^ k * b ^ k := by rw [← mul_pow, neg_one_mul]
  have hna : (-a⁻¹) ^ ℓ = (-1 : ℂ) ^ ℓ * (a ^ ℓ)⁻¹ := by
    rw [← inv_pow, ← mul_pow, neg_one_mul]
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ ℓ = (-1 : ℂ) ^ (k - ℓ) := by
    rw [← pow_add]
    have he : k + ℓ = (k - ℓ) + 2 * ℓ := by lia
    rw [he, pow_add, pow_mul]
    norm_num
  rw [mul_pow, hcpow, hc, hnb, hna]
  calc
    _ = ((-1 : ℂ) ^ k * (-1 : ℂ) ^ ℓ) * b ^ k / a ^ ℓ := by ring
    _ = _ := by rw [hsign]

/-- Every scalar zero at a representable index, away from both coefficients' zeros,
has negative real signed invariant. Representability excludes the identically zero rows
that occur at gaps in the two-lag semigroup. -/
theorem row_zero_signedInvariant_neg {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hℓk : ℓ < k)
    (hcop : ℓ.Coprime k) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) {n : ℕ}
    (hindex : ∃ i j : ℕ, n = ℓ * i + k * j) (hrow : row ℓ k a b n = 0) :
    ∃ w : ℝ, w < 0 ∧ (-1 : ℂ) ^ (k - ℓ) * b ^ k / a ^ ℓ = (w : ℂ) := by
  have hk : k ≠ 0 := by lia
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (-a⁻¹) (by lia : 0 < k)
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow hk] at hc
    exact (neg_ne_zero.mpr (inv_ne_zero ha)) hc.symm
  let x : ℂ := -b * c ^ ℓ
  have hx : x ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hb) (pow_ne_zero ℓ hc0)
  have hA : a * c ^ k = -1 := by rw [hc]; field_simp
  have hscalar : row ℓ k (-1 : ℂ) (-x) n = 0 := by
    have h := row_rescale hℓ hk a b c n
    have hB : b * c ^ ℓ = -x := by simp [x]
    rw [hA, hB, hrow, mul_zero] at h
    exact h
  have huni : (row ℓ k (-1 : ℝ[X]) (-X) n).eval₂ Complex.ofRealHom x = 0 := by
    have hm := map_row (eval₂RingHom Complex.ofRealHom x) hℓ hk (-1 : ℝ[X]) (-X) n
    have hm' : (row ℓ k (-1 : ℝ[X]) (-X) n).eval₂ Complex.ofRealHom x =
        row ℓ k (-1 : ℂ) (-x) n := by simpa using hm
    exact hm'.trans hscalar
  obtain ⟨i, j, hn⟩ := hindex
  have hn' : n = ℓ * (i % k) + k * (j + ℓ * (i / k)) := by
    rw [hn]
    nth_rw 1 [← Nat.mod_add_div i k]
    ring
  rw [hn', row_eq_X_pow_mul_expand_binomialRay hℓ hℓk hcop (Nat.mod_lt i (by lia)),
    eval₂_mul, eval₂_pow, eval₂_X, expand_eq_comp_X_pow, eval₂_comp, eval₂_pow,
    eval₂_X] at huni
  have hG := (mul_eq_zero.mp huni).resolve_left (pow_ne_zero (i % k) hx)
  obtain ⟨w, hw, heq⟩ := eval₂_binomialRay_eq_zero
    (by lia : i % k ≤ i % k + (j + ℓ * (i / k)))
    (by lia : k - ℓ < k) (Nat.mod_lt i (by lia)) hG
  refine ⟨w, hw, ?_⟩
  exact (pow_normalized_coefficient hℓk.le hc).symm.trans heq.symm

/-- **Finite two-lag signed-curve containment.** At every zero of a nonzero polynomial row
away from `A B = 0`, the signed invariant is a negative real number. -/
theorem eval₂_row_zero_signedInvariant_neg {R : Type*} [CommRing R]
    (f : R →+* ℂ) {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hℓk : ℓ < k)
    (hcop : ℓ.Coprime k) (A B : R[X]) {n : ℕ} (hne : row ℓ k A B n ≠ 0)
    {z : ℂ} (ha : A.eval₂ f z ≠ 0)
    (hb : B.eval₂ f z ≠ 0)
    (hz : (row ℓ k A B n).eval₂ f z = 0) :
    ∃ w : ℝ, w < 0 ∧ (-1 : ℂ) ^ (k - ℓ) * (B.eval₂ f z) ^ k /
      (A.eval₂ f z) ^ ℓ = (w : ℂ) := by
  have hindex := exists_decomposition_of_row_ne_zero hℓ (by lia : k ≠ 0) A B hne
  have hm := map_row (eval₂RingHom f z) hℓ (by lia : k ≠ 0) A B n
  exact row_zero_signedInvariant_neg hℓ hℓk hcop ha hb hindex (hm.symm.trans hz)

/-- Real two-lag rows are real-rooted when the negative signed inverse image is real and
all row zeros on either exceptional coefficient locus are real. -/
theorem coprime_row_isRealRooted {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hℓk : ℓ < k)
    (hcop : ℓ.Coprime k) (A B : ℝ[X]) (n : ℕ) (hne : row ℓ k A B n ≠ 0)
    (hcurve : ∀ (z : ℂ) (w : ℝ), w < 0 →
      A.eval₂ Complex.ofRealHom z ≠ 0 → B.eval₂ Complex.ofRealHom z ≠ 0 →
      (-1 : ℂ) ^ (k - ℓ) * (B.eval₂ Complex.ofRealHom z) ^ k /
        (A.eval₂ Complex.ofRealHom z) ^ ℓ = (w : ℂ) → z.im = 0)
    (hexception : ∀ z : ℂ,
      (A.eval₂ Complex.ofRealHom z = 0 ∨ B.eval₂ Complex.ofRealHom z = 0) →
      (row ℓ k A B n).eval₂ Complex.ofRealHom z = 0 → z.im = 0) :
    row ℓ k A B n ≠ 0 ∧ (row ℓ k A B n).Splits := by
  refine ⟨hne, Polynomial.splits_of_all_roots_real ?_⟩
  intro z hz
  have hzeval : (row ℓ k A B n).eval₂ Complex.ofRealHom z = 0 := by
    simpa [eval_map] using hz
  by_cases ha : A.eval₂ Complex.ofRealHom z = 0
  · exact hexception z (Or.inl ha) hzeval
  · by_cases hb : B.eval₂ Complex.ofRealHom z = 0
    · exact hexception z (Or.inr hb) hzeval
    · obtain ⟨w, hw, heq⟩ := eval₂_row_zero_signedInvariant_neg Complex.ofRealHom
        hℓ hℓk hcop A B hne ha hb hzeval
      exact hcurve z w hw ha hb heq

end RealRooted.Trinomial
