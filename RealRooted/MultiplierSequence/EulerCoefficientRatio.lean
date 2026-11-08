module

public import RealRooted.MultiplierSequence.CoefficientRatio
import RealRooted.MultiplierSequence.Laguerre

/-!
# Euler factors in hypergeometric coefficient certificates

We allow the extra coefficient weight
`h(k) = ∏ (r + k) ∏ (s + d - k)` for positive parameter lists `r` and `s`.
Thus the descending factors have their zeros strictly above the ambient degree.
The division-free ratio acquires `h(k)` on the left and `h(k+1)` on the right.
The proof uses shifted Euler PF multipliers and two-sided Jensen polynomials.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Product of shifted Euler diagonals. -/
def eulerProduct (parameters : List ℝ) (k : ℕ) : ℝ :=
  (parameters.map (fun r : ℝ => (k : ℝ) + r)).prod

/-- Positive shifts give positive Euler product weights. -/
theorem eulerProduct_pos {parameters : List ℝ}
    (h : ∀ r ∈ parameters, 0 < r) (k : ℕ) : 0 < eulerProduct parameters k := by
  apply List.prod_pos
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  have := h r hr
  positivity

/-- Products of shifted Euler diagonals are PF multipliers. -/
theorem isPFMultiplierSequence_eulerProduct {parameters : List ℝ}
    (h : ∀ r ∈ parameters, 0 ≤ r) : IsPFMultiplierSequence (eulerProduct parameters) := by
  induction parameters with
  | nil =>
      change IsPFMultiplierSequence (fun _ => 1)
      exact isPFMultiplierSequence_one_sequence
  | cons r parameters ih =>
      exact (isPFMultiplierSequence_natCast_add (h r (by simp))).mul
        (ih (fun s hs => h s (by simp [hs])))

/-- Two-sided Euler weight on the degree range `0 ≤ k ≤ d`. A descending
shift `s > 0` corresponds to the factor `s + d - k`. -/
def eulerWeight (d : ℕ) (rising falling : List ℝ) (k : ℕ) : ℝ :=
  eulerProduct rising k * eulerProduct falling (d - k)

/-- Positive Euler parameters give positive two-sided weights. -/
theorem eulerWeight_pos {rising falling : List ℝ}
    (hr : ∀ r ∈ rising, 0 < r) (hs : ∀ s ∈ falling, 0 < s) (d k : ℕ) :
    0 < eulerWeight d rising falling k :=
  mul_pos (eulerProduct_pos hr k) (eulerProduct_pos hs (d - k))

/-- The Pochhammer Jensen model with additional two-sided Euler factors. -/
def eulerPochhammerPolynomial (d : ℕ) (lower upper rising falling : List ℝ) : ℝ[X] :=
  twoSidedJensenPolynomial d
    (fun k => eulerProduct rising k * invPochhammerProduct lower k)
    (fun k => eulerProduct falling k * invPochhammerProduct upper k)

/-- Euler factors preserve the PF property of the Pochhammer Jensen model. -/
theorem eulerPochhammerPolynomial_isPF {lower upper rising falling : List ℝ}
    (hl : ∀ a ∈ lower, 0 < a) (hu : ∀ b ∈ upper, 0 < b)
    (hr : ∀ r ∈ rising, 0 < r) (hs : ∀ s ∈ falling, 0 < s) (d : ℕ) :
    IsPFPolynomial (eulerPochhammerPolynomial d lower upper rising falling) := by
  apply ((isPFMultiplierSequence_eulerProduct (fun r h => (hr r h).le)).mul
    (isPFMultiplierSequence_invPochhammerProduct hl)).diagonalOperator_isPF
  exact (isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence
    ((isPFMultiplierSequence_eulerProduct (fun s h => (hs s h).le)).mul
      (isPFMultiplierSequence_invPochhammerProduct hu)) d).reverse

/-- Euler factors multiply the coefficients of the unweighted model. -/
theorem eulerPochhammerPolynomial_coeff {lower upper rising falling : List ℝ}
    (hu : ∀ b ∈ upper, 0 < b) (hs : ∀ s ∈ falling, 0 < s) (d k : ℕ) :
    (eulerPochhammerPolynomial d lower upper rising falling).coeff k =
      eulerWeight d rising falling k * (pochhammerJensenPolynomial d lower upper).coeff k := by
  rw [eulerPochhammerPolynomial, pochhammerJensenPolynomial,
    coeff_twoSidedJensenPolynomial (fun k =>
      mul_pos (eulerProduct_pos hs k) (invPochhammerProduct_pos hu k)),
    coeff_twoSidedJensenPolynomial (invPochhammerProduct_pos hu)]
  split_ifs <;> simp only [eulerWeight] <;> ring

/-- The Euler-weighted model has a division-free coefficient-ratio certificate. -/
theorem eulerPochhammerPolynomial_coeff_ratio {lower upper rising falling : List ℝ}
    (hl : ∀ a ∈ lower, 0 < a) (hu : ∀ b ∈ upper, 0 < b)
    (hs : ∀ s ∈ falling, 0 < s) {d k : ℕ} (hk : k < d) :
    ((k : ℝ) + 1) * (lower.map (fun a : ℝ => a + k)).prod *
        eulerWeight d rising falling k *
        (eulerPochhammerPolynomial d lower upper rising falling).coeff (k + 1) =
      ((d : ℝ) - k) * (upper.map (fun b : ℝ => b + d - k - 1)).prod *
        eulerWeight d rising falling (k + 1) *
        (eulerPochhammerPolynomial d lower upper rising falling).coeff k := by
  rw [eulerPochhammerPolynomial_coeff hu hs, eulerPochhammerPolynomial_coeff hu hs]
  linear_combination
    eulerWeight d rising falling k * eulerWeight d rising falling (k + 1) *
      pochhammerJensenPolynomial_coeff_ratio hl hu hk

/-- A coefficient-ratio certificate with arbitrary positive Pochhammer and
Euler parameter lists implies the PF property. Empty and repeated lists are allowed. -/
theorem isPFPolynomial_of_euler_pochhammer_coeff_ratio
    {p : ℝ[X]} {d : ℕ} {lower upper rising falling : List ℝ}
    (hl : ∀ a ∈ lower, 0 < a) (hu : ∀ b ∈ upper, 0 < b)
    (hr : ∀ r ∈ rising, 0 < r) (hs : ∀ s ∈ falling, 0 < s)
    (hdegree : p.natDegree ≤ d) (hzero : 0 < p.coeff 0)
    (hratio : ∀ k < d,
      ((k : ℝ) + 1) * (lower.map (fun a : ℝ => a + k)).prod *
          eulerWeight d rising falling k * p.coeff (k + 1) =
        ((d : ℝ) - k) * (upper.map (fun b : ℝ => b + d - k - 1)).prod *
          eulerWeight d rising falling (k + 1) * p.coeff k) : IsPFPolynomial p := by
  have hqd := natDegree_twoSidedJensenPolynomial
    (fun k => mul_pos (eulerProduct_pos hr k) (invPochhammerProduct_pos hl k))
    (fun k => mul_pos (eulerProduct_pos hs k) (invPochhammerProduct_pos hu k)) d
  have hqzero : 0 < (eulerPochhammerPolynomial d lower upper rising falling).coeff 0 := by
    rw [eulerPochhammerPolynomial_coeff hu hs]
    exact mul_pos (eulerWeight_pos hr hs d 0)
      (pochhammerJensenPolynomial_coeff_pos hl hu (Nat.zero_le d))
  have hpq := eq_C_mul_of_coeff_ratio (d := d)
    (A := fun k => ((k : ℝ) + 1) * (lower.map (fun a : ℝ => a + k)).prod *
      eulerWeight d rising falling k)
    (B := fun k => ((d : ℝ) - k) * (upper.map (fun b : ℝ => b + d - k - 1)).prod *
      eulerWeight d rising falling (k + 1))
    (fun k _ => by
      have := prod_map_add_natCast_pos hl k
      have := eulerWeight_pos hr hs d k
      positivity) hdegree hqd.le hqzero.ne' hratio
    fun k hk => eulerPochhammerPolynomial_coeff_ratio hl hu hs hk
  rw [hpq]
  exact IsPFPolynomial.const_mul (div_pos hzero hqzero)
    (eulerPochhammerPolynomial_isPF hl hu hr hs d)

end RealRooted
