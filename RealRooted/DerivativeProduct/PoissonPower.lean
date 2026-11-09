module

public import RealRooted.DerivativeProduct.Poisson
public import RealRooted.DerivativeProduct.ProductPower
public import RealRooted.RootLocation.Basic
import RealRooted.DerivativeProduct.ProductPowerRoots
import RealRooted.BorceaBranden.Applications.PoissonStarGeneral
import RealRooted.BorceaBranden.Applications.PoissonStarTransport
import RealRooted.Chebyshev.Levels
import RealRooted.WagnerX.NonnegativeRoots
import Mathlib.Tactic

/-!
# Poisson powers on source intervals

For the Poisson product `f ⋆ g = starC c f g = ∑ k, c ^ k / k! * X ^ k * f ^ (k) * g ^ (k)`
with `c ≥ 0`, the product-power map `S_g` (`RealRooted.Poisson.starCPowMap`) sends `X ^ n` to the
`n`th Poisson power `g^{⋆n}`.  We prove: for a nonconstant `g` and `a ≤ b`, the map `S_g` sends
every polynomial rooted in `[a, b]` to a polynomial rooted in `(-∞, 0]` if and only if
`g - a` and `g - b` are rooted in `(-∞, 0]`
(`forall_isRealRootedIn_starCPowMap_Icc_iff`).

The ingredients are the functional calculus `S_g (A ∏ (X - r_i)) = A ((g - r_1) ⋆ ⋯ ⋆ (g - r_m))`
(`RealRooted.derivProductPowMap_X_sub_C_mul`), closure of the class of polynomials rooted in
`(-∞, 0]` under the Poisson product (`isRealRootedIn_Iic_starC`, from Brändén's theorem that
Poisson multiplication by a PF polynomial preserves PF polynomials), and the fact that if two
constant levels of `g` are real-rooted, so are all intermediate levels
(`RealRooted.splits_sub_C_of_mem_Icc`).
-/

@[expose] public section

open Polynomial Set

noncomputable section

namespace RealRooted.Poisson

/-- The product-power map `S_g` of the Poisson product `starC c`: the linear map sending `X ^ n`
to the Poisson power `g^{⋆n}` (with `g^{⋆0} = 1`). -/
abbrev starCPowMap (c : ℝ) (g : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  derivProductPowMap X (fun k : ℕ ↦ c ^ k / (k.factorial : ℝ)) g

private theorem coeff_zero_eq_one (c : ℝ) : (fun k : ℕ ↦ c ^ k / (k.factorial : ℝ)) 0 = 1 := by
  simp

private theorem natDegree_X_le_two : (X : ℝ[X]).natDegree ≤ 2 :=
  natDegree_X_le.trans (by norm_num)

private theorem coeff_two_X : (X : ℝ[X]).coeff 2 = 0 := by simp [coeff_X]

/-- A polynomial rooted in `(-∞, 0]` is a nonzero constant multiple of a nonzero PF polynomial. -/
theorem exists_isPFPolynomial_of_isRealRootedIn_Iic {p : ℝ[X]} (hp : IsRealRootedIn (Iic 0) p) :
    ∃ a : ℝ, a ≠ 0 ∧ ∃ q : ℝ[X], IsPFPolynomial q ∧ q ≠ 0 ∧ p = C a * q := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp.ne_zero
  have hq : IsRealRootedIn (Iic 0) (C p.leadingCoeff⁻¹ * p) :=
    hp.C_mul (inv_ne_zero hlc)
  have hlc1 : (C p.leadingCoeff⁻¹ * p).leadingCoeff = 1 := by
    rw [leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hlc]
  have hnn := (hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hq.splits).2
    ⟨by rw [HasPosLeadingCoeff, hlc1]; exact one_pos, fun r hr ↦ hq.mem_of_mem_roots hr⟩
  refine ⟨p.leadingCoeff, hlc, C p.leadingCoeff⁻¹ * p,
    IsPFPolynomial.of_realRooted_nonneg hnn.1 hq.splits, hq.ne_zero, ?_⟩
  rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]

/-- **Closure under the Poisson product.**  For `c ≥ 0`, the Poisson product of two polynomials
rooted in `(-∞, 0]` is rooted in `(-∞, 0]`. -/
theorem isRealRootedIn_Iic_starC {c : ℝ} (hc : 0 ≤ c) {f g : ℝ[X]}
    (hf : IsRealRootedIn (Iic 0) f) (hg : IsRealRootedIn (Iic 0) g) :
    IsRealRootedIn (Iic 0) (starC c f g) := by
  obtain ⟨a, ha, f₁, hf₁, hf₁0, rfl⟩ := exists_isPFPolynomial_of_isRealRootedIn_Iic hf
  obtain ⟨b, hb, g₁, hg₁, hg₁0, rfl⟩ := exists_isPFPolynomial_of_isRealRootedIn_Iic hg
  have hpf := (IsPFPolynomial.preservesPF hc hf₁) g₁ hg₁
  rw [starC_C_mul_left, starC_C_mul_right, ← mul_assoc, ← C_mul]
  refine IsRealRootedIn.C_mul (mul_ne_zero ha hb) ⟨starC_ne_zero hf₁0 hg₁0, hpf.splits, ?_⟩
  exact fun r hr ↦ hpf.roots_nonpos r hr

/-- For `p` rooted in `(-∞, 0]` and `x > 0`, the leading coefficient and the value at `x` have
the same sign. -/
theorem leadingCoeff_mul_eval_pos {p : ℝ[X]} (hp : IsRealRootedIn (Iic 0) p) {x : ℝ}
    (hx : 0 < x) : 0 < p.leadingCoeff * p.eval x := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp.ne_zero
  rw [hp.splits.eval_eq_prod_roots x]
  have hprod : 0 < (p.roots.map fun a ↦ x - a).prod := by
    refine Multiset.prod_pos fun t ht ↦ ?_
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 ht
    linarith [hp.mem_of_mem_roots hs, show s ≤ 0 from hp.mem_of_mem_roots hs]
  have := sq_pos_of_ne_zero hlc
  calc 0 < p.leadingCoeff ^ 2 * (p.roots.map fun a ↦ x - a).prod := by positivity
    _ = _ := by ring

/-- **Intermediate levels.**  If `g` is nonconstant and `g - a`, `g - b` are rooted in
`(-∞, 0]`, then so is `g - r` for every `r ∈ [a, b]`. -/
theorem isRealRootedIn_Iic_sub_C_of_mem_Icc {g : ℝ[X]} (hg : g.natDegree ≠ 0) {a b r : ℝ}
    (hr : r ∈ Icc a b) (ha : IsRealRootedIn (Iic 0) (g - C a))
    (hb : IsRealRootedIn (Iic 0) (g - C b)) : IsRealRootedIn (Iic 0) (g - C r) := by
  have hne : g - C r ≠ 0 := by
    intro h
    apply hg
    have := congrArg natDegree h
    rwa [natDegree_sub_C, natDegree_zero] at this
  refine ⟨hne, splits_sub_C_of_mem_Icc hg hr ha.splits hb.splits, fun t ht ↦ ?_⟩
  by_contra hpos
  have ht0 : 0 < t := lt_of_not_ge hpos
  have hroot : g.eval t = r := by
    have := (mem_roots hne).1 ht
    simpa [sub_eq_zero] using this
  have hlc : ∀ s : ℝ, (g - C s).leadingCoeff = g.leadingCoeff := fun s ↦ by
    refine leadingCoeff_sub_of_degree_lt ?_
    exact degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp (by lia))
  have h1 := leadingCoeff_mul_eval_pos ha ht0
  have h2 := leadingCoeff_mul_eval_pos hb ht0
  rw [hlc, eval_sub, eval_C, hroot] at h1 h2
  rcases lt_trichotomy g.leadingCoeff 0 with h | h | h
  · nlinarith [hr.1]
  · simp [h] at h1
  · nlinarith [hr.2]

/-- **Degree bookkeeping.**  For a nonconstant `g` and a real-rooted input `p`, the image `S_g p`
is nonzero, `deg S_g p = deg p * deg g` and `lc S_g p = lc p * lc g ^ deg p`. -/
theorem natDegree_leadingCoeff_starCPowMap {c : ℝ} (hc : 0 ≤ c) {g : ℝ[X]}
    (hg : g.natDegree ≠ 0) {S : Set ℝ} {p : ℝ[X]} (hp : IsRealRootedIn S p) :
    starCPowMap c g p ≠ 0 ∧ (starCPowMap c g p).natDegree = p.natDegree * g.natDegree ∧
      (starCPowMap c g p).leadingCoeff = p.leadingCoeff * g.leadingCoeff ^ p.natDegree := by
  have hnn : ∀ k : ℕ, 0 ≤ c ^ k / (k.factorial : ℝ) := fun k ↦ by positivity
  have h := natDegree_derivProductPowMap natDegree_X_le_two (by rw [coeff_two_X])
    (coeff_zero_eq_one c) hnn hg hp
  exact ⟨h.1, h.2, leadingCoeff_derivProductPowMap natDegree_X_le_two (by rw [coeff_two_X])
    (coeff_zero_eq_one c) hnn hg coeff_two_X hp⟩

/-- **Poisson powers on a source interval.**  For `c ≥ 0`, a nonconstant `g` and `a ≤ b`, the map
`S_g` sends every polynomial rooted in `[a, b]` to a polynomial rooted in `(-∞, 0]` if and only if
`g - a` and `g - b` are rooted in `(-∞, 0]`. -/
theorem forall_isRealRootedIn_starCPowMap_Icc_iff {c : ℝ} (hc : 0 ≤ c) {g : ℝ[X]}
    (hg : g.natDegree ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    (∀ p : ℝ[X], IsRealRootedIn (Icc a b) p → IsRealRootedIn (Iic 0) (starCPowMap c g p)) ↔
      IsRealRootedIn (Iic 0) (g - C a) ∧ IsRealRootedIn (Iic 0) (g - C b) := by
  have hclosed : ∀ f q : ℝ[X], IsRealRootedIn (Iic 0) f → IsRealRootedIn (Iic 0) q →
      IsRealRootedIn (Iic 0) (derivProduct X (fun k : ℕ ↦ c ^ k / (k.factorial : ℝ)) f q) :=
    fun f q hf hq ↦ isRealRootedIn_Iic_starC hc hf hq
  rw [forall_isRealRootedIn_derivProductPowMap_iff (coeff_zero_eq_one c) hclosed]
  exact ⟨fun h ↦ ⟨h a ⟨le_rfl, hab⟩, h b ⟨hab, le_rfl⟩⟩, fun h r hr ↦
    isRealRootedIn_Iic_sub_C_of_mem_Icc hg hr h.1 h.2⟩

/-- **Poisson powers on a source interval, with the output convention of `MapsRealRootedIn`.**
The same criterion for the sequence map to send `[a, b]`-rooted inputs of every degree to zero or
`(-∞, 0]`-rooted polynomials. -/
theorem forall_mapsRealRootedIn_starCPowMap_Icc_iff {c : ℝ} (hc : 0 ≤ c) {g : ℝ[X]}
    (hg : g.natDegree ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    (∀ n, MapsRealRootedIn (starCPowMap c g) n (Icc a b) (Iic 0)) ↔
      IsRealRootedIn (Iic 0) (g - C a) ∧ IsRealRootedIn (Iic 0) (g - C b) := by
  rw [← forall_isRealRootedIn_starCPowMap_Icc_iff hc hg hab]
  refine ⟨fun h p hp ↦ ?_, fun h n p _ hp ↦ Or.inr (h p hp)⟩
  rcases h p.natDegree p le_rfl hp with h0 | h1
  · exact absurd h0 (natDegree_leadingCoeff_starCPowMap hc hg hp).1
  · exact h1

end RealRooted.Poisson
