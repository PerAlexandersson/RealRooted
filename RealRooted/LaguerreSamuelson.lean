import Mathlib

/-!
# The Laguerre–Samuelson inequality

For real numbers `x₁, …, xₙ` with mean `μ = (∑ xᵢ) / n`, every `xⱼ` satisfies
`(xⱼ - μ) ^ 2 ≤ (n - 1) / n * ∑ (xᵢ - μ) ^ 2`, that is `|xⱼ - μ| ≤ √(n - 1) · s` where
`s ^ 2 = ∑ (xᵢ - μ) ^ 2 / n` is the population variance.

Applied to the roots of a monic real-rooted polynomial
`p = X ^ n + a X ^ (n - 1) + b X ^ (n - 2) + ⋯`, Newton's identities `∑ rᵢ = -a` and
`∑ rᵢ ^ 2 = a ^ 2 - 2 b` turn this into Laguerre's root bound
`(r + a / n) ^ 2 ≤ (n - 1) / n * ((n - 1) / n * a ^ 2 - 2 b)`.

## Main results

* `Samuelson.sq_sub_mean_le`: the multiset form.
* `Samuelson.abs_sub_mean_le`: the form `|xⱼ - μ| ≤ √(n - 1) * s`.
* `Samuelson.sq_sub_mean_le_finset`: the `Finset`-indexed form.
* `Samuelson.sq_add_coeff_div_le`: Laguerre's coefficient form for monic real-rooted
  polynomials.

## References

* E. Laguerre, *Sur une méthode pour obtenir par approximation les racines d'une équation
  algébrique qui a toutes ses racines réelles*, Nouv. Ann. Math. (2) 19 (1880), 161–171.
* P. A. Samuelson, *How deviant can you be?*, J. Amer. Statist. Assoc. 63 (1968), 1522–1525.
* J. M. Steele, *The Cauchy–Schwarz Master Class*, Exercise 5.5.
-/

open Polynomial

namespace RealRooted.Samuelson

/-- Cauchy–Schwarz for a multiset of reals: `(∑ x) ^ 2 ≤ card · ∑ x ^ 2`. -/
theorem sq_sum_le_card_mul_sum_sq (s : Multiset ℝ) :
    s.sum ^ 2 ≤ Multiset.card s * (s.map (· ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.sum_cons, Multiset.map_cons, Multiset.card_cons]
    push_cast
    rcases (Nat.cast_nonneg (Multiset.card s) : (0 : ℝ) ≤ _).eq_or_lt with hc | hc
    · obtain rfl : s = 0 := Multiset.card_eq_zero.mp (by exact_mod_cast hc.symm)
      simp
    · nlinarith [sq_nonneg (Multiset.card s * a - s.sum),
        mul_nonneg (by linarith : (0 : ℝ) ≤ Multiset.card s + 1) (sub_nonneg.mpr ih)]

/-- Summing `x - c` over a multiset. -/
theorem sum_map_sub_const (t : Multiset ℝ) (c : ℝ) :
    (t.map fun x => x - c).sum = t.sum - Multiset.card t * c := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring

/-- Summing `(x - c) ^ 2` over a multiset. -/
theorem sum_map_sub_sq (t : Multiset ℝ) (c : ℝ) :
    (t.map fun x => (x - c) ^ 2).sum =
      (t.map (· ^ 2)).sum - 2 * c * t.sum + Multiset.card t * c ^ 2 := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring

/-- **Samuelson's inequality** (Laguerre 1880, Samuelson 1968), multiset form: every element
`r` of a multiset `t` of reals with mean `μ` satisfies
`(r - μ) ^ 2 ≤ (card t - 1) / card t * ∑ (x - μ) ^ 2`. -/
theorem sq_sub_mean_le (t : Multiset ℝ) {r : ℝ} (hr : r ∈ t) :
    (r - t.sum / Multiset.card t) ^ 2 ≤
      (Multiset.card t - 1) / Multiset.card t *
        (t.map fun x => (x - t.sum / Multiset.card t) ^ 2).sum := by
  obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem hr
  set μ := (r ::ₘ s).sum / Multiset.card (r ::ₘ s)
  have hc : ((Multiset.card (r ::ₘ s) : ℕ) : ℝ) = Multiset.card s + 1 := by simp
  have hμ : r + s.sum = (Multiset.card s + 1) * μ := by
    simp only [μ, hc, Multiset.sum_cons]
    field_simp
  have hCS := sq_sum_le_card_mul_sum_sq (s.map fun x => x - μ)
  rw [sum_map_sub_const, Multiset.card_map, Multiset.map_map] at hCS
  have hS : s.sum - Multiset.card s * μ = μ - r := by linarith
  rw [hS] at hCS
  rw [hc, Multiset.map_cons, Multiset.sum_cons, add_sub_cancel_right, div_mul_eq_mul_div,
    le_div_iff₀ (by positivity)]
  have hQ : (Multiset.map ((fun x => x ^ 2) ∘ fun x => x - μ) s).sum =
      (s.map fun x => (x - μ) ^ 2).sum := rfl
  nlinarith [hCS, hQ]

/-- **Samuelson's inequality**, standard-deviation form: with `n = card t`, mean `μ` and
population standard deviation `σ = √(∑ (x - μ) ^ 2 / n)`, every `r ∈ t` satisfies
`|r - μ| ≤ √(n - 1) * σ`. -/
theorem abs_sub_mean_le (t : Multiset ℝ) {r : ℝ} (hr : r ∈ t) :
    |r - t.sum / Multiset.card t| ≤
      √(Multiset.card t - 1) *
        √((t.map fun x => (x - t.sum / Multiset.card t) ^ 2).sum / Multiset.card t) := by
  have h1 : (1 : ℝ) ≤ Multiset.card t := by
    exact_mod_cast Multiset.card_pos_iff_exists_mem.mpr ⟨r, hr⟩
  rw [← Real.sqrt_mul (by linarith)]
  refine Real.abs_le_sqrt ((sq_sub_mean_le t hr).trans_eq ?_)
  ring

/-- **Samuelson's inequality** for a `Finset`-indexed family of reals. -/
theorem sq_sub_mean_le_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ) {j : ι} (hj : j ∈ s) :
    (f j - (∑ i ∈ s, f i) / s.card) ^ 2 ≤
      (s.card - 1) / s.card * ∑ i ∈ s, (f i - (∑ i ∈ s, f i) / s.card) ^ 2 := by
  simpa [Multiset.map_map, Function.comp_def, Finset.sum_map_val] using
    sq_sub_mean_le (s.val.map f) (Multiset.mem_map_of_mem f hj)

/-- `e₁` is the sum. -/
theorem esymm_one (t : Multiset ℝ) : t.esymm 1 = t.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]

/-- Newton's identity `p₂ = e₁ ^ 2 - 2 e₂`. -/
theorem sum_map_sq_eq (t : Multiset ℝ) : (t.map (· ^ 2)).sum = t.sum ^ 2 - 2 * t.esymm 2 := by
  induction t using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    have h2 : (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.sum := by
      rw [← esymm_one]
      simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map,
        Multiset.sum_map_mul_left]
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons, h2, ih]
    ring

/-- **Laguerre's root bound.**  Let `p = X ^ n + a X ^ (n - 1) + b X ^ (n - 2) + ⋯` be a monic
real polynomial of degree `n ≥ 2` with all roots real.  Then every root `r` satisfies
`(r + a / n) ^ 2 ≤ (n - 1) / n * ((n - 1) / n * a ^ 2 - 2 * b)`, i.e. all roots lie in
`-a / n ± (n - 1) / n * √(a ^ 2 - 2 n b / (n - 1))`. -/
theorem sq_add_coeff_div_le {p : ℝ[X]} {n : ℕ} (hmon : p.Monic) (hdeg : p.natDegree = n)
    (hn : 2 ≤ n) (hroots : Multiset.card p.roots = n) {r : ℝ} (hr : r ∈ p.roots) :
    (r + p.coeff (n - 1) / n) ^ 2 ≤
      (n - 1) / n * ((n - 1) / n * p.coeff (n - 1) ^ 2 - 2 * p.coeff (n - 2)) := by
  have hcard : Multiset.card p.roots = p.natDegree := hroots.trans hdeg.symm
  have ha : p.coeff (n - 1) = -p.roots.sum := by
    rw [coeff_eq_esymm_roots_of_card hcard (by lia), hmon.leadingCoeff, hdeg,
      show n - (n - 1) = 1 by lia, esymm_one]
    ring
  have hb : p.coeff (n - 2) = p.roots.esymm 2 := by
    rw [coeff_eq_esymm_roots_of_card hcard (by lia), hmon.leadingCoeff, hdeg,
      show n - (n - 2) = 2 by lia]
    ring
  have h := sq_sub_mean_le p.roots hr
  rw [sum_map_sub_sq, sum_map_sq_eq, hroots] at h
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [ha, hb]
  calc (r + -p.roots.sum / n) ^ 2 = (r - p.roots.sum / n) ^ 2 := by ring
    _ ≤ _ := h
    _ = _ := by
      field_simp
      ring

end RealRooted.Samuelson
