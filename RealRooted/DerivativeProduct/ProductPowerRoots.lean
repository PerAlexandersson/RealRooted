module

public import RealRooted.DerivativeProduct.ProductPower
public import RealRooted.RootLocation.Basic
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

/-!
# Root location for product-power maps

For an associative derivative product `⋆` and a polynomial `g`, the product-power map `S_g`
(`RealRooted.derivProductPowMap`) sends a polynomial `A * ∏ (X - r_i)` to
`A * ((g - r_1) ⋆ ⋯ ⋆ (g - r_m))`.  Consequently, if a root class `T` is closed under `⋆`,
then `S_g` sends polynomials rooted in a source set `J` to polynomials rooted in `T` if and only
if every level `g - r`, `r ∈ J`, is rooted in `T` (`forall_isRealRootedIn_derivProductPowMap_iff`).
This reduces the source-interval tests for product powers to one-factor tests.  We also record
the degree and leading-coefficient bookkeeping of `S_g` on real-rooted inputs.
-/

public section

open Polynomial Set

namespace RealRooted

noncomputable section

/-- **Induction on linear factors.**  A property of polynomials rooted in `S` holds for all of
them if it holds for nonzero constants and is preserved by multiplication with `X - r`, `r ∈ S`. -/
theorem IsRealRootedIn.induction_on_X_sub_C {S : Set ℝ} {P : ℝ[X] → Prop}
    (hC : ∀ a : ℝ, a ≠ 0 → P (C a))
    (hstep : ∀ r ∈ S, ∀ q : ℝ[X], IsRealRootedIn S q → P q → P ((X - C r) * q))
    {p : ℝ[X]} (hp : IsRealRootedIn S p) : P p := by
  suffices h : ∀ n : ℕ, ∀ p : ℝ[X], p.natDegree = n → IsRealRootedIn S p → P p from
    h _ p rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hn hp
    by_cases h0 : p.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero h0]
      refine hC _ fun h => hp.ne_zero ?_
      rw [eq_C_of_natDegree_eq_zero h0, h, map_zero]
    · obtain ⟨r, hr⟩ := hp.splits.exists_eval_eq_zero
        (degree_ne_of_natDegree_ne h0)
      have hfact : (X - C r) * (p /ₘ (X - C r)) = p := mul_divByMonic_eq_iff_isRoot.mpr hr
      have hq : IsRealRootedIn S (p /ₘ (X - C r)) := by
        rw [← hfact] at hp
        exact (IsRealRootedIn.mul_iff.mp hp).2
      have hdeg : (p /ₘ (X - C r)).natDegree < n := by
        rw [natDegree_divByMonic_X_sub_C]
        lia
      rw [← hfact]
      exact hstep r (hp.mem_of_isRoot hr) _ hq (ih _ hdeg _ rfl hq)

/-- A polynomial rooted in the singleton `{r}` is a nonzero constant multiple of a power of
`X - r`. -/
theorem exists_eq_C_mul_X_sub_C_pow_of_isRealRootedIn_singleton {r : ℝ} {p : ℝ[X]}
    (hp : IsRealRootedIn {r} p) : ∃ a : ℝ, a ≠ 0 ∧ ∃ n : ℕ, p = C a * (X - C r) ^ n := by
  refine IsRealRootedIn.induction_on_X_sub_C (P := fun p ↦
    ∃ a : ℝ, a ≠ 0 ∧ ∃ n : ℕ, p = C a * (X - C r) ^ n) (fun a ha ↦ ⟨a, ha, 0, by simp⟩)
    (fun t ht q _ ⟨a, ha, n, hq⟩ ↦ ⟨a, ha, n + 1, ?_⟩) hp
  rw [mem_singleton_iff.mp ht, hq, pow_succ']
  ring

variable {w : ℝ[X]} {c : ℕ → ℝ} {g : ℝ[X]}

/-- If a root class `T` is closed under the product `⋆` and every level `g - r`, `r ∈ J`, is
rooted in `T`, then `S_g` sends polynomials rooted in `J` to polynomials rooted in `T`. -/
theorem isRealRootedIn_derivProductPowMap (hc0 : c 0 = 1) {T J : Set ℝ}
    (hclosed : ∀ f q : ℝ[X], IsRealRootedIn T f → IsRealRootedIn T q →
      IsRealRootedIn T (derivProduct w c f q))
    (hg : ∀ r ∈ J, IsRealRootedIn T (g - C r)) {p : ℝ[X]} (hp : IsRealRootedIn J p) :
    IsRealRootedIn T (derivProductPowMap w c g p) := by
  refine IsRealRootedIn.induction_on_X_sub_C (P := fun p ↦
    IsRealRootedIn T (derivProductPowMap w c g p)) (fun a ha ↦ ?_) (fun r hr q _ ih ↦ ?_) hp
  · rw [derivProductPowMap_C]
    exact IsRealRootedIn.C ha
  · rw [derivProductPowMap_X_sub_C_mul hc0]
    exact hclosed _ _ (hg r hr) ih

/-- `S_g` sends the linear polynomial `X - r` to the level `g - r`. -/
theorem derivProductPowMap_X_sub_C (hc0 : c 0 = 1) (r : ℝ) :
    derivProductPowMap w c g (X - C r) = g - C r := by
  have h := derivProductPowMap_X_pow (w := w) (c := c) (g := g) 1
  rw [pow_one, derivProductPow_one hc0] at h
  rw [map_sub, h, derivProductPowMap_C]

/-- **Source-interval reduction.**  If `T` is closed under the product `⋆`, then `S_g` sends every
polynomial rooted in `J` to a polynomial rooted in `T` if and only if every level `g - r`,
`r ∈ J`, is rooted in `T`. -/
theorem forall_isRealRootedIn_derivProductPowMap_iff (hc0 : c 0 = 1) {T J : Set ℝ}
    (hclosed : ∀ f q : ℝ[X], IsRealRootedIn T f → IsRealRootedIn T q →
      IsRealRootedIn T (derivProduct w c f q)) :
    (∀ p : ℝ[X], IsRealRootedIn J p → IsRealRootedIn T (derivProductPowMap w c g p)) ↔
      ∀ r ∈ J, IsRealRootedIn T (g - C r) :=
  ⟨fun h r hr ↦ by
    simpa [derivProductPowMap_X_sub_C hc0] using h _ (IsRealRootedIn.X_sub_C hr),
    fun h _ hp ↦ isRealRootedIn_derivProductPowMap hc0 hclosed h hp⟩

/-- Sufficiency in the vocabulary of `MapsRealRootedIn`: for every degree bound at once. -/
theorem mapsRealRootedIn_derivProductPowMap (hc0 : c 0 = 1) {T J : Set ℝ}
    (hclosed : ∀ f q : ℝ[X], IsRealRootedIn T f → IsRealRootedIn T q →
      IsRealRootedIn T (derivProduct w c f q))
    (hg : ∀ r ∈ J, IsRealRootedIn T (g - C r)) (n : ℕ) :
    MapsRealRootedIn (derivProductPowMap w c g) n J T :=
  fun _ _ hp ↦ Or.inr (isRealRootedIn_derivProductPowMap hc0 hclosed hg hp)

private theorem sub_C_ne_zero_of_natDegree_ne_zero (hg : g.natDegree ≠ 0) (r : ℝ) :
    g - C r ≠ 0 := by
  intro h
  apply hg
  have := congrArg natDegree h
  rwa [natDegree_sub_C, natDegree_zero] at this

/-! ### Degree and leading coefficient on real-rooted inputs -/

section Degree

variable (hw : w.natDegree ≤ 2) (hA : 0 ≤ w.coeff 2) (hc0 : c 0 = 1) (hc : ∀ k, 0 ≤ c k)
include hw hA hc0 hc

/-- On a real-rooted input `p`, the product-power map of a nonconstant `g` is nonzero of degree
`deg p * deg g`. -/
theorem natDegree_derivProductPowMap (hg : g.natDegree ≠ 0) {S : Set ℝ} {p : ℝ[X]}
    (hp : IsRealRootedIn S p) :
    derivProductPowMap w c g p ≠ 0 ∧
      (derivProductPowMap w c g p).natDegree = p.natDegree * g.natDegree := by
  refine IsRealRootedIn.induction_on_X_sub_C (P := fun p ↦ derivProductPowMap w c g p ≠ 0 ∧
    (derivProductPowMap w c g p).natDegree = p.natDegree * g.natDegree) (fun a ha ↦ ?_)
    (fun r _ q hq ih ↦ ?_) hp
  · simp [ha]
  · have hq0 : q ≠ 0 := hq.ne_zero
    rw [derivProductPowMap_X_sub_C_mul hc0, natDegree_mul (X_sub_C_ne_zero r) hq0,
      natDegree_X_sub_C, add_comm]
    refine ⟨derivProduct_ne_zero hw hA hc0 hc (sub_C_ne_zero_of_natDegree_ne_zero hg r) ih.1, ?_⟩
    rw [natDegree_derivProduct hw hA hc0 hc (sub_C_ne_zero_of_natDegree_ne_zero hg r) ih.1,
      ih.2, natDegree_sub_C]
    ring

/-- For a weight with vanishing `X ^ 2`-coefficient, the product-power map of a nonconstant `g`
multiplies the leading coefficient of a real-rooted input `p` by `lc(g) ^ deg p`. -/
theorem leadingCoeff_derivProductPowMap (hg : g.natDegree ≠ 0) (hA0 : w.coeff 2 = 0)
    {S : Set ℝ} {p : ℝ[X]} (hp : IsRealRootedIn S p) :
    (derivProductPowMap w c g p).leadingCoeff = p.leadingCoeff * g.leadingCoeff ^ p.natDegree := by
  refine IsRealRootedIn.induction_on_X_sub_C (P := fun p ↦
    (derivProductPowMap w c g p).leadingCoeff = p.leadingCoeff * g.leadingCoeff ^ p.natDegree)
    (fun a ha ↦ ?_) (fun r _ q hq ih ↦ ?_) hp
  · simp
  · have hq0 : q ≠ 0 := hq.ne_zero
    have hlc : (g - C r).leadingCoeff = g.leadingCoeff := by
      refine leadingCoeff_sub_of_degree_lt ?_
      exact (degree_C_le).trans_lt (natDegree_pos_iff_degree_pos.mp (by lia))
    rw [derivProductPowMap_X_sub_C_mul hc0,
      leadingCoeff_derivProduct hw hA hc0 hc (sub_C_ne_zero_of_natDegree_ne_zero hg r)
        (natDegree_derivProductPowMap hw hA hc0 hc hg hq).1, hA0,
      derivProductLeadingFactor_zero_left hc0, mul_one, hlc, ih,
      natDegree_mul (X_sub_C_ne_zero r) hq0, natDegree_X_sub_C, add_comm, leadingCoeff_mul,
      leadingCoeff_X_sub_C, one_mul]
    ring

end Degree

end

end RealRooted
