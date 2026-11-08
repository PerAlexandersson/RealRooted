module

public import RealRooted.PFPolynomial
import RealRooted.Gurvits.Univariate
import RealRooted.Mathlib.Algebra.Polynomial.Coeff
import RealRooted.Mathlib.Algebra.Order.BigOperators.Ring.Multiset
import RealRooted.RootAmplitude.Polynomial
import RealRooted.RootAmplitude.SmallestRoot
import RealRooted.RootVieta

/-!
# Consequences of the lowest coefficients of a Pólya-frequency polynomial

A Pólya-frequency (PF) polynomial `p` with positive constant coefficient `c₀` factors as
`c₀ ∏ᵢ (1 + λᵢ X)` where `λᵢ = -1 / rᵢ > 0` runs over the roots `rᵢ` of `p`, with multiplicity,
and `∑ᵢ λᵢ = c₁ / c₀`.  This module records the following consequences, using only the
coefficients `c₀`, `c₁` (and `c₂`).

* `IsPFPolynomial.coeff_zero_sub_mul_coeff_one_le_eval_neg`: the linear lower bound
  `c₀ - t c₁ ≤ p(-t)` for `t ≥ 0` with `t c₁ ≤ c₀`, and its positivity corollary.
* `IsPFPolynomial.mul_coeff_one_le_neg_coeff_zero_of_mem_roots`: `r c₁ ≤ -c₀` for each root `r`.
* `IsPFPolynomial.succ_mul_coeff_zero_mul_coeff_succ_le`: `(j + 1) c₀ c_{j+1} ≤ c₁ c_j`.
* `IsPFPolynomial.card_filter_roots_lt_pow_mul_sum`: if the interval `(-R, 0)` contains a root,
  then the number `ν` of roots in it (with multiplicity) satisfies `ν < Rˡ ∑ᵢ λᵢˡ`;
  its coefficient forms bound `ν` by `c₁` and by `c₁, c₂`.
* `IsPFPolynomial.exists_largest_root_of_coeff_one_pos`: if `c₀ = 1`, `c₁ > 0` and
  `2 c₂ = ε c₁²` with `ε < 1/2`, then the largest root `-v` is simple, `v` is close to `1 / c₁`,
  and `v p'(-v)` lies in `[(1 - 2 ε) / (1 - ε), 1]`.
-/

public section

open Polynomial

namespace RealRooted

namespace IsPFPolynomial

section Factorization

variable {p : ℝ[X]}

/-- The positive reciprocal magnitudes `-1 / r` of the roots. -/
private theorem neg_inv_pos_of_mem_roots (hp : IsPFPolynomial p) (h0 : 0 < p.coeff 0) {r : ℝ}
    (hr : r ∈ p.roots) : 0 < -r⁻¹ := by
  simpa using inv_lt_zero.2
    (roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hp.hasNonnegCoeffs h0.ne' r hr)

/-- The factorization `p = c₀ ∏ (1 + λᵢ X)`. -/
private theorem eq_C_mul_prod_one_add (hp : IsPFPolynomial p) (h0 : 0 < p.coeff 0) :
    p = C (p.coeff 0) *
      ((p.roots.map fun r => -r⁻¹).map fun c => 1 + C c * X).prod :=
  (Gurvits.eq_C_mul_prod_of_splits (hp.splits) hp.hasNonnegCoeffs h0).2

/-- Evaluation through the factorization `p = c₀ ∏ (1 + λᵢ X)`. -/
private theorem eval_eq_coeff_zero_mul_prod (hp : IsPFPolynomial p) (h0 : 0 < p.coeff 0)
    (x : ℝ) :
    p.eval x = p.coeff 0 * (p.roots.map fun r => 1 + -r⁻¹ * x).prod := by
  conv_lhs => rw [eq_C_mul_prod_one_add hp h0]
  simp [eval_multiset_prod, Multiset.map_map]

/-- The linear coefficient is `c₀ ∑ᵢ λᵢ`. -/
private theorem coeff_one_eq_coeff_zero_mul_sum (hp : IsPFPolynomial p) (h0 : 0 < p.coeff 0) :
    p.coeff 1 = p.coeff 0 * (p.roots.map fun r => -r⁻¹).sum := by
  conv_lhs => rw [eq_C_mul_prod_one_add hp h0]
  rw [coeff_C_mul, (Gurvits.coeff_prod_one_add_C_mul_X _).2]

end Factorization

/-- **Linear lower bound near zero.**  A PF polynomial with positive constant coefficient `c₀`
satisfies `c₀ - t c₁ ≤ p(-t)` for `t ≥ 0` with `t c₁ ≤ c₀`. -/
theorem coeff_zero_sub_mul_coeff_one_le_eval_neg {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : 0 < p.coeff 0) {t : ℝ} (ht : 0 ≤ t) (htc : t * p.coeff 1 ≤ p.coeff 0) :
    p.coeff 0 - t * p.coeff 1 ≤ p.eval (-t) := by
  set Z : Multiset ℝ := p.roots.map fun r => t * -r⁻¹ with hZ
  have hnn : ∀ z ∈ Z, 0 ≤ z := by
    simp only [hZ, Multiset.mem_map]
    rintro _ ⟨r, hr, rfl⟩
    exact mul_nonneg ht (neg_inv_pos_of_mem_roots hp h0 hr).le
  have hsum : p.coeff 0 * Z.sum = t * p.coeff 1 := by
    rw [hZ, Multiset.sum_map_mul_left, coeff_one_eq_coeff_zero_mul_sum hp h0]
    ring
  have hle : Z.sum ≤ 1 := by
    by_contra! h
    nlinarith
  have hprod : p.eval (-t) = p.coeff 0 * (Z.map fun z => 1 - z).prod := by
    rw [eval_eq_coeff_zero_mul_prod hp h0, hZ, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun r _ => ?_
    simp only [Function.comp_apply]
    ring
  have key := Multiset.one_sub_sum_le_prod_one_sub Z hnn fun z hz =>
    (Multiset.single_le_sum hnn z hz).trans hle
  rw [hprod]
  nlinarith

/-- **Positivity near zero.**  A PF polynomial with positive constant coefficient `c₀` is
positive at `-t` for `t ≥ 0` with `t c₁ < c₀`. -/
theorem eval_neg_pos_of_mul_coeff_one_lt {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : 0 < p.coeff 0) {t : ℝ} (ht : 0 ≤ t) (htc : t * p.coeff 1 < p.coeff 0) :
    0 < p.eval (-t) := by
  have := coeff_zero_sub_mul_coeff_one_le_eval_neg hp h0 ht htc.le
  linarith

/-- **Division-free root bound.**  Every root `r` of a PF polynomial with positive constant
coefficient satisfies `r c₁ ≤ -c₀`; for `c₁ > 0` this says `r ≤ -c₀ / c₁`. -/
theorem mul_coeff_one_le_neg_coeff_zero_of_mem_roots {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : 0 < p.coeff 0) {r : ℝ} (hr : r ∈ p.roots) : r * p.coeff 1 ≤ -p.coeff 0 := by
  have hrneg := roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hp.hasNonnegCoeffs h0.ne' r hr
  have hmem : -r⁻¹ ≤ (p.roots.map fun r => -r⁻¹).sum :=
    Multiset.single_le_sum (fun x hx => by
      obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hx
      exact (neg_inv_pos_of_mem_roots hp h0 hs).le) _ (Multiset.mem_map_of_mem _ hr)
  rw [coeff_one_eq_coeff_zero_mul_sum hp h0]
  have := mul_le_mul_of_nonneg_left hmem h0.le
  have hr0 : r ≠ 0 := hrneg.ne
  have hr' : r * (p.coeff 0 * -r⁻¹) = -p.coeff 0 := by
    field_simp
  nlinarith

section Coefficients

/-- The coefficients of `∏ (1 + λᵢ X)` are nonnegative and satisfy
`(j + 1) q_{j+1} ≤ (∑ λᵢ) q_j`. -/
private theorem succ_mul_coeff_succ_le_sum_mul_coeff (L : Multiset ℝ) (hL : ∀ l ∈ L, 0 ≤ l) :
    (∀ j, 0 ≤ ((L.map fun c => 1 + C c * X).prod).coeff j) ∧
      ∀ j : ℕ, ((j : ℝ) + 1) * ((L.map fun c => 1 + C c * X).prod).coeff (j + 1) ≤
        L.sum * ((L.map fun c => 1 + C c * X).prod).coeff j := by
  induction L using Multiset.induction_on with
  | empty =>
    refine ⟨fun j => ?_, by simp [coeff_one]⟩
    simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one]
    split_ifs <;> norm_num
  | cons a L ih =>
    have ha : 0 ≤ a := hL a (Multiset.mem_cons_self a L)
    obtain ⟨hnn, hle⟩ := ih fun l hl => hL l (Multiset.mem_cons_of_mem hl)
    have hS : 0 ≤ L.sum := Multiset.sum_nonneg fun l hl => hL l (Multiset.mem_cons_of_mem hl)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    generalize (L.map fun c => 1 + C c * X).prod = Q at hnn hle ⊢
    refine ⟨?_, ?_⟩
    · rintro (_ | j)
      · simpa using hnn 0
      · rw [coeff_one_add_C_mul_X_mul_succ]
        exact add_nonneg (hnn _) (mul_nonneg ha (hnn _))
    · rintro (_ | j)
      · have := hle 0
        simp only [Nat.cast_zero, zero_add, one_mul] at this ⊢
        rw [coeff_one_add_C_mul_X_mul_succ]
        simp only [add_mul, one_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul_zero]
        nlinarith [hnn 0]
      · rw [coeff_one_add_C_mul_X_mul_succ a Q (j + 1), coeff_one_add_C_mul_X_mul_succ a Q j]
        have h1 := hle (j + 1)
        have h2 := mul_le_mul_of_nonneg_left (hle j) ha
        push_cast at h1 ⊢
        nlinarith [hnn j, mul_nonneg ha (hnn j), mul_nonneg ha hS, mul_nonneg ha (hnn (j + 1)),
          mul_nonneg (mul_nonneg ha ha) (hnn j)]

end Coefficients

/-- **Coefficient inequality.**  A PF polynomial with positive constant coefficient satisfies
`(j + 1) c₀ c_{j+1} ≤ c₁ c_j`. -/
theorem succ_mul_coeff_zero_mul_coeff_succ_le {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : 0 < p.coeff 0) (j : ℕ) :
    ((j : ℝ) + 1) * p.coeff 0 * p.coeff (j + 1) ≤ p.coeff 1 * p.coeff j := by
  have hL : ∀ l ∈ p.roots.map (fun r => -r⁻¹), 0 ≤ l := by
    intro l hl
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hl
    exact (neg_inv_pos_of_mem_roots hp h0 hs).le
  have key := (succ_mul_coeff_succ_le_sum_mul_coeff _ hL).2 j
  have hp' := eq_C_mul_prod_one_add hp h0
  have hc : ∀ n, p.coeff n = p.coeff 0 *
      ((p.roots.map fun r => -r⁻¹).map fun c => 1 + C c * X).prod.coeff n := fun n => by
    conv_lhs => rw [hp']
    rw [coeff_C_mul]
  rw [hc (j + 1), hc j, coeff_one_eq_coeff_zero_mul_sum hp h0]
  nlinarith [mul_le_mul_of_nonneg_left key (sq_nonneg (p.coeff 0))]

section RootCount

/-- A root in `(-R, 0)` has `R * (-1 / r) > 1`. -/
private theorem one_lt_mul_neg_inv {R r : ℝ} (hr : r < 0) (hR : -R < r) : 1 < R * -r⁻¹ := by
  have h1 := mul_inv_cancel₀ hr.ne
  nlinarith [mul_pos_of_neg_of_neg (by linarith : -R - r < 0) (inv_lt_zero.2 hr)]

/-- **Root count from reciprocal power sums.**  Let `p` be a PF polynomial with positive
constant coefficient, whose roots are `-1 / λᵢ` with `λᵢ > 0`.  If the interval `(-R, 0)` contains
a root, then the number `ν` of roots in it, counted with multiplicity, satisfies
`ν < Rˡ ∑ᵢ λᵢˡ` for every `ℓ ≥ 1`. -/
theorem card_filter_roots_lt_pow_mul_sum {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : 0 < p.coeff 0) {R : ℝ} (hR : 0 < R) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (hν : 0 < (p.roots.filter fun r => -R < r).card) :
    ((p.roots.filter fun r => -R < r).card : ℝ) <
      R ^ ℓ * (p.roots.map fun r => (-r⁻¹) ^ ℓ).sum := by
  set F := p.roots.filter fun r => -R < r with hF
  set g : ℝ → ℝ := fun r => (R * -r⁻¹) ^ ℓ with hg
  have hg0 : ∀ r ∈ p.roots, 0 ≤ g r := fun r hr =>
    pow_nonneg (mul_nonneg hR.le (neg_inv_pos_of_mem_roots hp h0 hr).le) _
  have hgt : ∀ r ∈ F, 1 < g r := by
    intro r hr
    rw [hF, Multiset.mem_filter] at hr
    have hrneg :=
      roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hp.hasNonnegCoeffs h0.ne' _ hr.1
    exact one_lt_pow₀ (one_lt_mul_neg_inv hrneg hr.2) hℓ
  have hlt : (F.map fun _ => (1 : ℝ)).sum < (F.map g).sum :=
    Multiset.sum_lt_sum_of_nonempty (Multiset.card_pos.1 hν) hgt
  have hcard : (F.map fun _ => (1 : ℝ)).sum = F.card := by simp
  have hsplit : (p.roots.map g).sum =
      (F.map g).sum + ((p.roots.filter fun r => ¬ -R < r).map g).sum := by
    conv_lhs => rw [← Multiset.filter_add_not (fun r => -R < r) p.roots]
    rw [Multiset.map_add, Multiset.sum_add]
  have hrest : 0 ≤ ((p.roots.filter fun r => ¬ -R < r).map g).sum :=
    Multiset.sum_nonneg fun x hx => by
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
      exact hg0 r (Multiset.mem_of_mem_filter hr)
  have hmul : R ^ ℓ * (p.roots.map fun r => (-r⁻¹) ^ ℓ).sum = (p.roots.map g).sum := by
    rw [← Multiset.sum_map_mul_left]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r _ => ?_)
    simp only [hg]
    rw [mul_pow]
  rw [hmul]
  linarith

/-- **Number of roots near zero from `c₁`.**  If `R c₁ ≤ j c₀` for a positive integer `j`, then
the interval `(-R, 0)` contains at most `j - 1` roots of `p`, counted with multiplicity. -/
theorem card_filter_roots_lt_of_mul_coeff_one_le {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : 0 < p.coeff 0) {R : ℝ} (hR : 0 < R) {j : ℕ} (hj : j ≠ 0)
    (h : R * p.coeff 1 ≤ j * p.coeff 0) :
    (p.roots.filter fun r => -R < r).card < j := by
  by_contra! hcard
  have hν : 0 < (p.roots.filter fun r => -R < r).card :=
    lt_of_lt_of_le (Nat.pos_of_ne_zero hj) hcard
  have hlt := card_filter_roots_lt_pow_mul_sum hp h0 hR one_ne_zero hν
  simp only [pow_one] at hlt
  rw [coeff_one_eq_coeff_zero_mul_sum hp h0] at h
  have hle : R * (p.roots.map fun r => -r⁻¹).sum ≤ j := by
    refine le_of_mul_le_mul_left ?_ h0
    linarith
  have : (j : ℝ) ≤ (p.roots.filter fun r => -R < r).card := by exact_mod_cast hcard
  linarith

/-- **Number of roots near zero from `c₀, c₁, c₂`.**  If `R² (c₁² - 2 c₀ c₂) ≤ j c₀²` for a
positive integer `j`, then the interval `(-R, 0)` contains at most `j - 1` roots of `p`, counted
with multiplicity.  This is the case `ℓ = 2` of `card_filter_roots_lt_pow_mul_sum`. -/
theorem card_filter_roots_lt_of_sq_mul_le {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : 0 < p.coeff 0) {R : ℝ} (hR : 0 < R) {j : ℕ} (hj : j ≠ 0)
    (h : R ^ 2 * (p.coeff 1 ^ 2 - 2 * p.coeff 0 * p.coeff 2) ≤ j * p.coeff 0 ^ 2) :
    (p.roots.filter fun r => -R < r).card < j := by
  by_contra! hcard
  have hν : 0 < (p.roots.filter fun r => -R < r).card :=
    lt_of_lt_of_le (Nat.pos_of_ne_zero hj) hcard
  have hlt := card_filter_roots_lt_pow_mul_sum hp h0 hR (ℓ := 2) two_ne_zero hν
  have hs := hp.splits
  have hp0 : p ≠ 0 := fun h' => by simp [h'] at h0
  have hvieta := RootVieta.poly_sum_sq p hs.natDegree_eq_card_roots.symm
    (leadingCoeff_ne_zero.2 hp0) fun r hr =>
      (roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hp.hasNonnegCoeffs h0.ne' r hr).ne
  have hS : (p.roots.map fun ξ => -(1 / ξ)).sum = (p.roots.map fun r => -r⁻¹).sum := by
    simp
  have hQ : (p.roots.map fun ξ => (1 / ξ) ^ 2).sum = (p.roots.map fun r => (-r⁻¹) ^ 2).sum := by
    simp
  rw [hS, hQ] at hvieta
  have hc1 := coeff_one_eq_coeff_zero_mul_sum hp h0
  set Q := (p.roots.map fun r => (-r⁻¹) ^ 2).sum
  set S := (p.roots.map fun r => -r⁻¹).sum
  have hc0 : p.coeff 0 ^ 2 * Q = p.coeff 1 ^ 2 - 2 * p.coeff 0 * p.coeff 2 := by
    have : Q = S ^ 2 - 2 * (p.coeff 2 / p.coeff 0) := by linarith
    rw [this, hc1]
    field_simp
  have hle : R ^ 2 * Q ≤ j := by
    refine le_of_mul_le_mul_left ?_ (pow_pos h0 2)
    nlinarith
  have : (j : ℝ) ≤ (p.roots.filter fun r => -R < r).card := by exact_mod_cast hcard
  linarith

/-- At most one root of a PF polynomial lies in `(-R, 0)` when `R c₁ ≤ 2 c₀`: two roots in this
interval coincide. -/
theorem eq_of_mem_roots_of_neg_lt {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : 0 < p.coeff 0) {R : ℝ} (hR : 0 < R) (h : R * p.coeff 1 ≤ 2 * p.coeff 0) {r s : ℝ}
    (hr : r ∈ p.roots) (hs : s ∈ p.roots) (hrR : -R < r) (hsR : -R < s) : r = s := by
  have hcard := card_filter_roots_lt_of_mul_coeff_one_le hp h0 hR (j := 2) two_ne_zero
    (by exact_mod_cast h)
  by_contra hne
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem (Multiset.mem_filter.2 ⟨hr, hrR⟩)
  have hst : s ∈ t := by
    have : s ∈ r ::ₘ t := ht ▸ Multiset.mem_filter.2 ⟨hs, hsR⟩
    exact (Multiset.mem_cons.1 this).resolve_left fun h' => hne h'.symm
  have := Multiset.card_pos_iff_exists_mem.2 ⟨s, hst⟩
  rw [ht, Multiset.card_cons] at hcard
  lia

/-- A root of a PF polynomial lying in `(-R, 0)` with `R c₁ ≤ 2 c₀` is simple. -/
theorem count_roots_eq_one_of_neg_lt {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : 0 < p.coeff 0) {R : ℝ} (hR : 0 < R) (h : R * p.coeff 1 ≤ 2 * p.coeff 0) {r : ℝ}
    (hr : r ∈ p.roots) (hrR : -R < r) : p.roots.count r = 1 := by
  have hcard := card_filter_roots_lt_of_mul_coeff_one_le hp h0 hR (j := 2) two_ne_zero
    (by exact_mod_cast h)
  have hc : p.roots.count r ≤ (p.roots.filter fun r => -R < r).card := by
    rw [← Multiset.count_filter_of_pos hrR]
    exact Multiset.count_le_card _ _
  have := Multiset.count_pos.2 hr
  lia

end RootCount

section LargestRoot

/-- The sum of the reciprocal magnitudes `λᵢ = -1 / rᵢ` of the roots is `c₁` when `c₀ = 1`. -/
private theorem sum_neg_inv_roots_eq {p : ℝ[X]} (hp : IsPFPolynomial p) (h0 : p.coeff 0 = 1) :
    (p.roots.map fun r => -r⁻¹).sum = p.coeff 1 := by
  have h0' : 0 < p.coeff 0 := by rw [h0]; exact one_pos
  rw [coeff_one_eq_coeff_zero_mul_sum hp h0', h0, one_mul]

/-- **Vieta step.**  If `c₀ = 1` and `2 c₂ = ε c₁²`, then `∑ᵢ λᵢ² = (1 - ε) c₁²`. -/
private theorem sum_sq_neg_inv_roots_eq {p : ℝ[X]} (hp : IsPFPolynomial p) (h0 : p.coeff 0 = 1)
    {ε : ℝ} (hε : 2 * p.coeff 2 = ε * p.coeff 1 ^ 2) :
    ((p.roots.map fun r => -r⁻¹).map fun x => x ^ 2).sum = (1 - ε) * p.coeff 1 ^ 2 := by
  have h0' : 0 < p.coeff 0 := by rw [h0]; exact one_pos
  have hs := hp.splits
  have hp0 : p ≠ 0 := fun h' => by simp [h'] at h0'
  have hneg := roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hp.hasNonnegCoeffs h0'.ne'
  have hvieta := RootVieta.poly_sum_sq p hs.natDegree_eq_card_roots.symm
    (leadingCoeff_ne_zero.2 hp0) fun r hr => (hneg r hr).ne
  have hQ : ((p.roots.map fun r => -r⁻¹).map fun x => x ^ 2).sum =
      (p.roots.map fun ξ => (1 / ξ) ^ 2).sum := by
    simp
  have hS : (p.roots.map fun ξ => -(1 / ξ)).sum = p.coeff 1 := by
    rw [← sum_neg_inv_roots_eq hp h0]
    simp
  rw [hS, h0, div_one] at hvieta
  rw [hQ]
  linarith

/-- **Largest root and its multiplicity.**  Under the hypotheses of
`exists_largest_root_of_coeff_one_pos`, the largest root `s` of `p` is simple, and
`(1 - ε) c₁ ≤ -1 / s ≤ c₁`. -/
private theorem exists_largest_root_count_eq_one {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : p.coeff 0 = 1) (ha : 0 < p.coeff 1) {ε : ℝ}
    (hε : 2 * p.coeff 2 = ε * p.coeff 1 ^ 2) (hε2 : ε < 1 / 2) :
    ∃ s ∈ p.roots, (∀ r ∈ p.roots, r ≤ s) ∧ p.roots.count s = 1 ∧
      (1 - ε) * p.coeff 1 ≤ -s⁻¹ ∧ -s⁻¹ ≤ p.coeff 1 := by
  have h0' : 0 < p.coeff 0 := by rw [h0]; exact one_pos
  have hneg := roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hp.hasNonnegCoeffs h0'.ne'
  have hL : ∀ x ∈ p.roots.map (fun r => -r⁻¹), 0 < x := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    exact neg_inv_pos_of_mem_roots hp h0' hr
  have hSa := sum_neg_inv_roots_eq hp h0
  have hQeq := sum_sq_neg_inv_roots_eq hp h0 hε
  rw [← hSa] at hQeq
  have hroots_ne : p.roots ≠ 0 := by
    intro h
    simp only [h, Multiset.map_zero, Multiset.sum_zero] at hSa
    exact ha.ne' hSa.symm
  obtain ⟨s, hsmem, hsmax⟩ := Multiset.exists_max_image id hroots_ne
  simp only [id] at hsmax
  have hmmem : -s⁻¹ ∈ p.roots.map (fun r => -r⁻¹) := Multiset.mem_map_of_mem _ hsmem
  have hmmax : ∀ x ∈ p.roots.map (fun r => -r⁻¹), x ≤ -s⁻¹ := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    rw [neg_le_neg_iff]
    exact (inv_le_inv_of_neg (hneg s hsmem) (hneg r hr)).2 (hsmax r hr)
  have hc : 1 / 2 < 1 - ε := by linarith
  have hmge : (1 - ε) * (p.roots.map fun r => -r⁻¹).sum ≤ -s⁻¹ :=
    RootAmplitude.mul_sum_le_max_of_sq_sum_ge hL hmmem hmmax hQeq.ge
  have hmle : -s⁻¹ ≤ (p.roots.map fun r => -r⁻¹).sum :=
    Multiset.single_le_sum (fun x hx => (hL x hx).le) _ hmmem
  have hcount : p.roots.count s = 1 := by
    by_contra hne
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hsmem
    have hst : s ∈ t := by
      rw [← Multiset.count_pos]
      have := Multiset.count_cons_self s t
      rw [← ht] at this
      have hpos : 0 < p.roots.count s := Multiset.count_pos.2 hsmem
      lia
    obtain ⟨u, hu⟩ := Multiset.exists_cons_of_mem hst
    have hsum : (p.roots.map fun r => -r⁻¹).sum = -s⁻¹ + (-s⁻¹ + (u.map fun r => -r⁻¹).sum) := by
      rw [ht, hu]
      simp
    have hu0 : 0 ≤ (u.map fun r => -r⁻¹).sum := by
      refine Multiset.sum_nonneg fun x hx => ?_
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
      refine (neg_inv_pos_of_mem_roots hp h0' ?_).le
      rw [ht, hu]
      simp [hr]
    nlinarith
  rw [hSa] at hmge hmle
  exact ⟨s, hsmem, hsmax, hcount, hmge, hmle⟩

/-- **Bounds for `c₁ v`.**  If `-1 / s` lies between `(1 - ε) c₁` and `c₁` for a negative `s`,
then `v = -s` satisfies `1 ≤ c₁ v ≤ 1 / (1 - ε)` and `|c₁ v - 1| ≤ ε / (1 - ε)`. -/
private theorem coeff_one_mul_neg_bounds {c s ε : ℝ} (hsneg : s < 0) (hε1 : 0 < 1 - ε)
    (hmge : (1 - ε) * c ≤ -s⁻¹) (hmle : -s⁻¹ ≤ c) :
    1 ≤ c * -s ∧ c * -s ≤ 1 / (1 - ε) ∧ |c * -s - 1| ≤ ε / (1 - ε) := by
  have hs0 := hsneg.ne
  have hvm : (-s) * (-s⁻¹) = 1 := by field_simp
  have hpos := (neg_pos.2 hsneg).le
  have hav1 : 1 ≤ c * -s := by nlinarith [mul_le_mul_of_nonneg_left hmle hpos]
  have hav2 : c * -s ≤ 1 / (1 - ε) := by
    rw [le_div_iff₀ hε1]
    nlinarith [mul_le_mul_of_nonneg_left hmge hpos]
  refine ⟨hav1, hav2, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.2 hav1)]
  have : ε / (1 - ε) = 1 / (1 - ε) - 1 := by field_simp; ring
  linarith

/-- **Derivative amplitude at the largest root.**  If `s` is the largest, simple root of `p`
and `c₀ = 1`, `2 c₂ = ε c₁²` with `ε < 1/2`, then `-s p'(s)` lies in
`[(1 - 2 ε) / (1 - ε), 1]`. -/
private theorem neg_mul_derivative_eval_bounds {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : p.coeff 0 = 1) {ε : ℝ} (hε : 2 * p.coeff 2 = ε * p.coeff 1 ^ 2) (hε2 : ε < 1 / 2)
    {s : ℝ} (hsmem : s ∈ p.roots) (hsmax : ∀ r ∈ p.roots, r ≤ s) (hcount : p.roots.count s = 1) :
    (1 - 2 * ε) / (1 - ε) ≤ -s * p.derivative.eval s ∧ -s * p.derivative.eval s ≤ 1 := by
  have h0' : 0 < p.coeff 0 := by rw [h0]; exact one_pos
  have hs := hp.splits
  have hneg := roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hp.hasNonnegCoeffs h0'.ne'
  have hzero : p.eval 0 = 1 := by rw [← coeff_zero_eq_eval_zero, h0]
  have hsneg := hneg s hsmem
  have hQeq : ((p.roots.map fun r => -r⁻¹).map fun x => x ^ 2).sum =
      (1 - ε) * (p.roots.map fun r => -r⁻¹).sum ^ 2 := by
    rw [sum_sq_neg_inv_roots_eq hp h0 hε, sum_neg_inv_roots_eq hp h0]
  have hfac : ∀ x ∈ (p.roots.erase s).map (fun r : ℝ => 1 - s / r), 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    have hrneg := hneg r (Multiset.mem_of_mem_erase hr)
    have hq : 0 ≤ s / r := (div_pos_of_neg_of_neg hsneg hrneg).le
    have hq1 : s / r ≤ 1 := by
      rw [div_le_one_of_neg hrneg]
      exact hsmax r (Multiset.mem_of_mem_erase hr)
    constructor <;> linarith
  have hder := RootAmplitude.eval_deriv_root_div_eval_zero hs hsmem hcount
    (by rw [hzero]; exact one_ne_zero)
  rw [hzero, div_one] at hder
  set P := ((p.roots.erase s).map fun r : ℝ => 1 - s / r).prod with hP
  have hvP : -s * p.derivative.eval s = P := by linarith
  have hP0 : 0 ≤ P := Multiset.prod_nonneg fun x hx => (hfac x hx).1
  have hP1 : P ≤ 1 := by
    have := Multiset.prod_map_le_prod_map₀ (s := p.roots.erase s) (fun r : ℝ => 1 - s / r)
      (fun _ => (1 : ℝ)) (fun r hr => (hfac _ (Multiset.mem_map_of_mem _ hr)).1)
      (fun r hr => (hfac _ (Multiset.mem_map_of_mem _ hr)).2)
    simpa using this
  have hamp := RootAmplitude.amplitude_at_smallest_root_of_sq_ratio hs
    (by rw [hzero]; exact one_pos) hneg (show 1 / 2 < 1 - ε by linarith) hQeq.ge hsmem hcount
    fun r hr => neg_le_neg (hsmax r hr)
  rw [hzero, show s * p.derivative.eval s = -P by linarith, abs_neg, abs_of_nonneg hP0,
    show 2 * (1 - ε) - 1 = 1 - 2 * ε by ring, one_mul] at hamp
  rw [hvP]
  exact ⟨hamp, hP1⟩

/-- **Largest root from the three lowest coefficients.**  Let `p` be a PF polynomial with
`p(0) = 1`, `a = [x] p > 0`, and `2 [x²] p = ε a²` with `ε < 1/2`.  Then `p` has a largest root
`-v`, which is simple, and `1 ≤ a v ≤ 1 / (1 - ε)`, `|a v - 1| ≤ ε / (1 - ε)`, and
`(1 - 2 ε) / (1 - ε) ≤ v p'(-v) ≤ 1`. -/
theorem exists_largest_root_of_coeff_one_pos {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : p.coeff 0 = 1) (ha : 0 < p.coeff 1) {ε : ℝ}
    (hε : 2 * p.coeff 2 = ε * p.coeff 1 ^ 2) (hε2 : ε < 1 / 2) :
    ∃ v : ℝ, 0 < v ∧ -v ∈ p.roots ∧ p.roots.count (-v) = 1 ∧ (∀ r ∈ p.roots, r ≤ -v) ∧
      1 ≤ p.coeff 1 * v ∧ p.coeff 1 * v ≤ 1 / (1 - ε) ∧
      |p.coeff 1 * v - 1| ≤ ε / (1 - ε) ∧
      (1 - 2 * ε) / (1 - ε) ≤ v * p.derivative.eval (-v) ∧ v * p.derivative.eval (-v) ≤ 1 := by
  obtain ⟨s, hsmem, hsmax, hcount, hmge, hmle⟩ :=
    exists_largest_root_count_eq_one hp h0 ha hε hε2
  have hsneg := roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hp.hasNonnegCoeffs
    (by rw [h0]; exact one_ne_zero) s hsmem
  obtain ⟨hav1, hav2, hav3⟩ := coeff_one_mul_neg_bounds hsneg (by linarith) hmge hmle
  obtain ⟨hlo, hhi⟩ := neg_mul_derivative_eval_bounds hp h0 hε hε2 hsmem hsmax hcount
  exact ⟨-s, neg_pos.2 hsneg, by rwa [neg_neg], by rwa [neg_neg],
    fun r hr => by rw [neg_neg]; exact hsmax r hr, hav1, hav2, hav3, by rwa [neg_neg],
    by rwa [neg_neg]⟩

/-- **Largest root, simplified bounds.**  Under the hypotheses of
`exists_largest_root_of_coeff_one_pos`, the largest root `-v` is simple, `1 / a ≤ v < 2 / a`,
`|a v - 1| ≤ 2 ε`, and `1 - 2 ε ≤ v p'(-v) ≤ 1`. -/
theorem exists_largest_root_lt_two_div_coeff_one {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : p.coeff 0 = 1) (ha : 0 < p.coeff 1) {ε : ℝ}
    (hε : 2 * p.coeff 2 = ε * p.coeff 1 ^ 2) (hε2 : ε < 1 / 2) :
    ∃ v : ℝ, 0 < v ∧ -v ∈ p.roots ∧ p.roots.count (-v) = 1 ∧ (∀ r ∈ p.roots, r ≤ -v) ∧
      1 / p.coeff 1 ≤ v ∧ v < 2 / p.coeff 1 ∧ |p.coeff 1 * v - 1| ≤ 2 * ε ∧
      1 - 2 * ε ≤ v * p.derivative.eval (-v) ∧ v * p.derivative.eval (-v) ≤ 1 := by
  obtain ⟨v, hv, hr, hc, hmax, h1, h2, h3, h4, h5⟩ :=
    exists_largest_root_of_coeff_one_pos hp h0 ha hε hε2
  have hε0 : 0 ≤ ε := by
    by_contra! h
    have := hp.hasNonnegCoeffs 2
    nlinarith [sq_pos_of_pos ha]
  have hε1 : 0 < 1 - ε := by linarith
  have hlt : 1 / (1 - ε) < 2 := by
    rw [div_lt_iff₀ hε1]
    linarith
  refine ⟨v, hv, hr, hc, hmax, ?_, ?_, ?_, ?_, h5⟩
  · rw [div_le_iff₀ ha]
    linarith
  · rw [lt_div_iff₀ ha]
    linarith
  · refine h3.trans ?_
    rw [div_le_iff₀ hε1]
    nlinarith
  · refine le_trans ?_ h4
    rw [le_div_iff₀ hε1]
    nlinarith

end LargestRoot

end IsPFPolynomial

end RealRooted
