module

public import RealRooted.MultiplierSequence.InvPochhammer
public import RealRooted.MultiplierSequence.TwoSidedJensen

/-!
# Real-rootedness from a hypergeometric coefficient ratio

A polynomial with the coefficient ratio
`(d-k) * (β+d-k-1) / ((k+1) * (α+k))`, where `α, β > 0`, is a positive
multiple of a two-sided reciprocal-Pochhammer Jensen polynomial.
This supplies a coefficient certificate without a special-function identity.
It is the one-upper-parameter case of Martínez-Finkelshtein--Morales--Perales,
*Real roots of hypergeometric polynomials via finite free convolution*, Theorem 4.6.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

private def reciprocalPochhammer (a : ℝ) (k : ℕ) : ℝ :=
  ((ascPochhammer ℝ k).eval a)⁻¹

private lemma reciprocalPochhammer_pos {a : ℝ} (ha : 0 < a) (k : ℕ) :
    0 < reciprocalPochhammer a k :=
  inv_pos.mpr (ascPochhammer_pos k a ha)

private lemma reciprocalPochhammer_step {a : ℝ} (ha : 0 < a) (k : ℕ) :
    (a + k) * reciprocalPochhammer a (k + 1) = reciprocalPochhammer a k := by
  have h : a + k ≠ 0 := ne_of_gt (by positivity)
  simp [reciprocalPochhammer, ascPochhammer_succ_eval, mul_inv_rev, h]

private def pochhammerModel (d : ℕ) (a b : ℝ) : ℝ[X] :=
  twoSidedJensenPolynomial d (reciprocalPochhammer a) (reciprocalPochhammer b)

private lemma pochhammerModel_isPF {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (d : ℕ) :
    IsPFPolynomial (pochhammerModel d a b) := by
  apply (isPFMultiplierSequence_inv_ascPochhammer ha).diagonalOperator_isPF
  exact (isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence
    (isPFMultiplierSequence_inv_ascPochhammer hb) d).reverse

private lemma pochhammerModel_coeff_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {d k : ℕ} (hk : k ≤ d) : 0 < (pochhammerModel d a b).coeff k := by
  rw [pochhammerModel, coeff_twoSidedJensenPolynomial (reciprocalPochhammer_pos hb)]
  simp only [hk, ite_true]
  exact mul_pos (mul_pos (by exact_mod_cast Nat.choose_pos hk)
    (reciprocalPochhammer_pos ha k)) (reciprocalPochhammer_pos hb (d - k))

private lemma pochhammerModel_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {d k : ℕ} (hk : k < d) :
    ((k : ℝ) + 1) * (a + k) * (pochhammerModel d a b).coeff (k + 1) =
      ((d : ℝ) - k) * (b + d - k - 1) * (pochhammerModel d a b).coeff k := by
  have hchoose : (d.choose (k + 1) : ℝ) * (k + 1) =
      (d.choose k : ℝ) * (d - k : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq d k
  rw [Nat.cast_sub hk.le] at hchoose
  have hleft := reciprocalPochhammer_step ha k
  have hright := reciprocalPochhammer_step hb (d - (k + 1))
  rw [show d - (k + 1) + 1 = d - k by lia] at hright
  have hcast : ((d - (k + 1) : ℕ) : ℝ) = (d : ℝ) - k - 1 := by
    rw [Nat.cast_sub (by lia : k + 1 ≤ d)]
    push_cast
    ring
  rw [hcast] at hright
  simp only [pochhammerModel,
    coeff_twoSidedJensenPolynomial (reciprocalPochhammer_pos hb),
    ite_eq_left hk.le, ite_eq_left (by lia : k + 1 ≤ d)]
  linear_combination
    (reciprocalPochhammer a (k + 1) * reciprocalPochhammer b (d - (k + 1)) *
      (a + k)) * hchoose +
    ((d.choose k : ℝ) * ((d : ℝ) - k) *
      reciprocalPochhammer b (d - (k + 1))) * hleft -
    ((d.choose k : ℝ) * ((d : ℝ) - k) * reciprocalPochhammer a k) * hright

/-- A positive constant coefficient and the hypergeometric coefficient ratio
with positive parameters certify the polynomial PF property. The degree bound
and ratio are all-index certificates, not a fit to finitely many rows. -/
theorem isPFPolynomial_of_pochhammer_coeff_ratio
    {p : ℝ[X]} {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hdegree : p.natDegree ≤ d)
    (hzero : 0 < p.coeff 0)
    (hratio : ∀ k < d,
      ((k : ℝ) + 1) * (a + k) * p.coeff (k + 1) =
        ((d : ℝ) - k) * (b + d - k - 1) * p.coeff k) :
    IsPFPolynomial p := by
  let q := pochhammerModel d a b
  have hqzero : 0 < q.coeff 0 := pochhammerModel_coeff_pos ha hb (Nat.zero_le d)
  let c := p.coeff 0 / q.coeff 0
  have hc : 0 < c := div_pos hzero hqzero
  have heq : ∀ k ≤ d, p.coeff k = c * q.coeff k := by
    intro k hk
    induction k with
    | zero => exact (div_mul_cancel₀ _ hqzero.ne').symm
    | succ k ih =>
        have hprev := ih (by lia)
        have hp := hratio k (by lia)
        have hq := pochhammerModel_ratio ha hb (d := d) (k := k) (by lia)
        have hnonzero : ((k : ℝ) + 1) * (a + k) ≠ 0 := by positivity
        apply mul_left_cancel₀ hnonzero
        rw [hp, hprev]
        change _ = ((k : ℝ) + 1) * (a + k) * (c * (pochhammerModel d a b).coeff (k + 1))
        linear_combination -c * hq
  have hpq : p = C c * q := by
    ext k
    rw [coeff_C_mul]
    by_cases hk : k ≤ d
    · exact heq k hk
    · have hqd : q.natDegree = d := natDegree_twoSidedJensenPolynomial
        (reciprocalPochhammer_pos ha) (reciprocalPochhammer_pos hb) d
      rw [coeff_eq_zero_of_natDegree_lt (by lia : p.natDegree < k),
        coeff_eq_zero_of_natDegree_lt (by lia : q.natDegree < k), mul_zero]
  rw [hpq]
  exact IsPFPolynomial.const_mul hc (pochhammerModel_isPF ha hb d)

end RealRooted
