module

public import RealRooted.MultiplierSequence.InvPochhammer
public import RealRooted.MultiplierSequence.TwoSidedJensen

/-!
# Real-rootedness from a hypergeometric coefficient ratio

A polynomial with the coefficient ratio
`(d-k) * (β+d-k-1) / ((k+1) * (α+k))`, where `α, β > 0`, is a positive
multiple of a two-sided reciprocal-Pochhammer Jensen polynomial.
This supplies a coefficient certificate without a special-function identity.
The list form allows any number of numerator and denominator parameters,
including empty lists and repetitions. A right parameter `β > 0` corresponds
to a falling-factorial parameter `A = d + β - 1 > d - 1`. The two lists
may have different lengths. This implements the parameter region of
Martínez-Finkelshtein--Morales--Perales,
*Real roots of hypergeometric polynomials via finite free convolution*, Theorem 4.6.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- A product of reciprocal rising-factorial weights. Empty parameter lists
have weight one; repetitions record repeated factors. -/
def invPochhammerProduct (parameters : List ℝ) (k : ℕ) : ℝ :=
  (parameters.map fun a => ((ascPochhammer ℝ k).eval a)⁻¹).prod

/-- Positive parameters give positive reciprocal-Pochhammer product weights. -/
theorem invPochhammerProduct_pos {parameters : List ℝ}
    (h : ∀ a ∈ parameters, 0 < a) (k : ℕ) :
    0 < invPochhammerProduct parameters k := by
  induction parameters with
  | nil => simp [invPochhammerProduct]
  | cons a parameters ih =>
      simp only [invPochhammerProduct, List.map_cons, List.prod_cons]
      exact mul_pos (inv_pos.mpr (ascPochhammer_pos k a (h a (by simp))))
        (ih (fun b hb => h b (by simp [hb])))

/-- Reciprocal-Pochhammer product weights are PF multiplier sequences. -/
theorem isPFMultiplierSequence_invPochhammerProduct {parameters : List ℝ}
    (h : ∀ a ∈ parameters, 0 < a) :
    IsPFMultiplierSequence (invPochhammerProduct parameters) := by
  induction parameters with
  | nil => simpa [invPochhammerProduct] using isPFMultiplierSequence_one_sequence
  | cons a parameters ih =>
      exact (isPFMultiplierSequence_inv_ascPochhammer (h a (by simp))).mul
        (ih (fun b hb => h b (by simp [hb])))

/-- Consecutive reciprocal-Pochhammer product weights satisfy a polynomial
identity, avoiding division in coefficient-ratio certificates. -/
theorem invPochhammerProduct_step {parameters : List ℝ}
    (h : ∀ a ∈ parameters, 0 < a) (k : ℕ) :
    (parameters.map (fun a => a + k)).prod * invPochhammerProduct parameters (k + 1) =
      invPochhammerProduct parameters k := by
  induction parameters with
  | nil => simp [invPochhammerProduct]
  | cons a parameters ih =>
      have hstep : (a + k) * ((ascPochhammer ℝ (k + 1)).eval a)⁻¹ =
          ((ascPochhammer ℝ k).eval a)⁻¹ := by
        have hne : a + k ≠ 0 := ne_of_gt (by have := h a (by simp); positivity)
        simp [ascPochhammer_succ_eval, mul_inv_rev, hne]
      have hrest := ih (fun b hb => h b (by simp [hb]))
      simp only [invPochhammerProduct, List.map_cons, List.prod_cons] at *
      calc
        _ = ((a + k) * ((ascPochhammer ℝ (k + 1)).eval a)⁻¹) *
            ((parameters.map (fun b => b + k)).prod *
              (parameters.map (fun b => ((ascPochhammer ℝ (k + 1)).eval b)⁻¹)).prod) := by
                ring
        _ = _ := by rw [hstep, hrest]

/-- A two-sided Jensen polynomial with reciprocal-Pochhammer product weights. -/
def pochhammerJensenPolynomial (d : ℕ) (left right : List ℝ) : ℝ[X] :=
  twoSidedJensenPolynomial d (invPochhammerProduct left) (invPochhammerProduct right)

/-- Positive parameter lists give PF two-sided Pochhammer Jensen polynomials. -/
theorem pochhammerJensenPolynomial_isPF {left right : List ℝ}
    (hl : ∀ a ∈ left, 0 < a) (hr : ∀ b ∈ right, 0 < b) (d : ℕ) :
    IsPFPolynomial (pochhammerJensenPolynomial d left right) := by
  apply (isPFMultiplierSequence_invPochhammerProduct hl).diagonalOperator_isPF
  exact (isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence
    (isPFMultiplierSequence_invPochhammerProduct hr) d).reverse

/-- Every coefficient in the degree range of a Pochhammer Jensen polynomial is positive. -/
theorem pochhammerJensenPolynomial_coeff_pos {left right : List ℝ}
    (hl : ∀ a ∈ left, 0 < a) (hr : ∀ b ∈ right, 0 < b)
    {d k : ℕ} (hk : k ≤ d) : 0 < (pochhammerJensenPolynomial d left right).coeff k := by
  rw [pochhammerJensenPolynomial, coeff_twoSidedJensenPolynomial (invPochhammerProduct_pos hr)]
  simp only [hk, ite_true]
  exact mul_pos (mul_pos (by exact_mod_cast Nat.choose_pos hk)
    (invPochhammerProduct_pos hl k)) (invPochhammerProduct_pos hr (d - k))

/-- The division-free coefficient ratio for arbitrary Pochhammer parameter lists. -/
theorem pochhammerJensenPolynomial_coeff_ratio {left right : List ℝ}
    (hl : ∀ a ∈ left, 0 < a) (hr : ∀ b ∈ right, 0 < b)
    {d k : ℕ} (hk : k < d) :
    ((k : ℝ) + 1) * (left.map (fun a => a + k)).prod *
        (pochhammerJensenPolynomial d left right).coeff (k + 1) =
      ((d : ℝ) - k) * (right.map (fun b => b + d - k - 1)).prod *
        (pochhammerJensenPolynomial d left right).coeff k := by
  have hchoose : (d.choose (k + 1) : ℝ) * (k + 1) =
      (d.choose k : ℝ) * (d - k : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq d k
  rw [Nat.cast_sub hk.le] at hchoose
  have hleft := invPochhammerProduct_step hl k
  have hright := invPochhammerProduct_step hr (d - (k + 1))
  rw [show d - (k + 1) + 1 = d - k by lia] at hright
  have hcast : ((d - (k + 1) : ℕ) : ℝ) = (d : ℝ) - k - 1 := by
    rw [Nat.cast_sub (by lia : k + 1 ≤ d)]
    push_cast
    ring
  rw [hcast] at hright
  simp_rw [show ∀ b : ℝ, b + ((d : ℝ) - k - 1) = b + d - k - 1 by
    intro b; ring] at hright
  simp only [pochhammerJensenPolynomial,
    coeff_twoSidedJensenPolynomial (invPochhammerProduct_pos hr),
    ite_eq_left hk.le, ite_eq_left (by lia : k + 1 ≤ d)]
  linear_combination
    (invPochhammerProduct left (k + 1) * invPochhammerProduct right (d - (k + 1)) *
      (left.map (fun a => a + k)).prod) * hchoose +
    ((d.choose k : ℝ) * ((d : ℝ) - k) *
      invPochhammerProduct right (d - (k + 1))) * hleft -
    ((d.choose k : ℝ) * ((d : ℝ) - k) * invPochhammerProduct left k) * hright

/-- A positive constant coefficient and the hypergeometric coefficient ratio
with positive parameters certify the polynomial PF property. The degree bound
and ratio are all-index certificates, not a fit to finitely many rows. -/
theorem isPFPolynomial_of_pochhammer_list_coeff_ratio
    {p : ℝ[X]} {d : ℕ} {left right : List ℝ}
    (hl : ∀ a ∈ left, 0 < a) (hr : ∀ b ∈ right, 0 < b) (hdegree : p.natDegree ≤ d)
    (hzero : 0 < p.coeff 0)
    (hratio : ∀ k < d,
      ((k : ℝ) + 1) * (left.map (fun a => a + k)).prod * p.coeff (k + 1) =
        ((d : ℝ) - k) * (right.map (fun b => b + d - k - 1)).prod * p.coeff k) :
    IsPFPolynomial p := by
  let q := pochhammerJensenPolynomial d left right
  have hqzero : 0 < q.coeff 0 := pochhammerJensenPolynomial_coeff_pos hl hr (Nat.zero_le d)
  let c := p.coeff 0 / q.coeff 0
  have hc : 0 < c := div_pos hzero hqzero
  have heq : ∀ k ≤ d, p.coeff k = c * q.coeff k := by
    intro k hk
    induction k with
    | zero => exact (div_mul_cancel₀ _ hqzero.ne').symm
    | succ k ih =>
        have hprev := ih (by lia)
        have hp := hratio k (by lia)
        have hq := pochhammerJensenPolynomial_coeff_ratio hl hr (d := d) (k := k) (by lia)
        have hprod : 0 < (left.map (fun a => a + k)).prod := by
          apply List.prod_pos
          intro x hx
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
          have := hl a ha
          positivity
        have hnonzero : ((k : ℝ) + 1) * (left.map (fun a => a + k)).prod ≠ 0 := by positivity
        apply mul_left_cancel₀ hnonzero
        rw [hp, hprev]
        change _ = ((k : ℝ) + 1) * (left.map (fun a => a + k)).prod *
          (c * (pochhammerJensenPolynomial d left right).coeff (k + 1))
        linear_combination -c * hq
  have hpq : p = C c * q := by
    ext k
    rw [coeff_C_mul]
    by_cases hk : k ≤ d
    · exact heq k hk
    · have hqd : q.natDegree = d := natDegree_twoSidedJensenPolynomial
        (invPochhammerProduct_pos hl) (invPochhammerProduct_pos hr) d
      rw [coeff_eq_zero_of_natDegree_lt (by lia : p.natDegree < k),
        coeff_eq_zero_of_natDegree_lt (by lia : q.natDegree < k), mul_zero]
  rw [hpq]
  exact IsPFPolynomial.const_mul hc (pochhammerJensenPolynomial_isPF hl hr d)

/-- The one-element-list specialization of the Pochhammer coefficient-ratio criterion. -/
theorem isPFPolynomial_of_pochhammer_coeff_ratio
    {p : ℝ[X]} {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hdegree : p.natDegree ≤ d)
    (hzero : 0 < p.coeff 0)
    (hratio : ∀ k < d,
      ((k : ℝ) + 1) * (a + k) * p.coeff (k + 1) =
        ((d : ℝ) - k) * (b + d - k - 1) * p.coeff k) :
    IsPFPolynomial p := by
  apply isPFPolynomial_of_pochhammer_list_coeff_ratio
    (left := [a]) (right := [b]) (by simpa using ha) (by simpa using hb) hdegree hzero
  simpa using hratio

end RealRooted
