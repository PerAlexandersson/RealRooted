module

public import RealRooted.Hermite.Heat
public import RealRooted.Applications.BipartiteHeatSeed
import RealRooted.ExponentialRows.HalfPlaneTransport
import Mathlib.Tactic

/-!
# Bipartite clustering with edges and balanced four-vertex pieces

We define the rows by the finite heat formula
`Rₙ(t) = [exp(c t Dᵥ²) Mₙ(v)]ᵥ₌ₜ`, where
`Mₙ(v) = ∑ₖ binom(n,k)² k! vᵏ`.
This is the balanced diagonal of `exp(x + y + t xy + c t x²y²)`.
Thus `c = 1` retains single edges and all four three-edge paths on a fixed
`K₂,₂` support. This formula specifies the model; no finite graph enumeration
identity is assumed. The full cap-three model also includes unbalanced
pieces and is outside this specialization.

Frozen backward heat excludes common roots using `Mₙ₊₁' = (n+1)² Mₙ`.
Connected deformation from `c = 0` then gives strict consecutive interlacing
and simple negative roots at every nonnegative parameter.

Source: Proposition 1 of the unpublished manuscript attached to
https://github.com/PerAlexandersson/RealRooted/issues/2646,
comment https://github.com/PerAlexandersson/RealRooted/issues/2646#issuecomment-7188203431.
-/

@[expose] public section

open Polynomial Set

noncomputable section

namespace RealRooted.BipartiteHeat

/-- The bipartite packing row with edge pieces and weight `c` on balanced four-vertex pieces. -/
def polynomial (c : ℝ) (n : ℕ) : ℝ[X] := heatDiagonal c (matchingSeed n)

/-- The explicit finite heat formula defining the bipartite specialization. -/
theorem polynomial_eq_sum (c : ℝ) (n : ℕ) :
    polynomial c n = ∑ j ∈ Finset.range (n + 1),
      C (c ^ j / j.factorial) * X ^ j * (derivative^[2 * j]) (matchingSeed n) := by
  rw [polynomial, heatDiagonal_eq_sum_even, matchingSeed_natDegree]

/-- The defining finite heat identity, evaluated at the frozen parameter. -/
theorem eval_polynomial (c t : ℝ) (n : ℕ) :
    (polynomial c n).eval t = (gaussianHeat (c * t) (matchingSeed n)).eval t :=
  eval_heatDiagonal c t (matchingSeed n)

/-- The degree of the bipartite heat row is its index at every real parameter. -/
@[simp] theorem polynomial_natDegree (c : ℝ) (n : ℕ) :
    (polynomial c n).natDegree = n := by
  rw [polynomial, heatDiagonal_natDegree, matchingSeed_natDegree]

/-- Every bipartite heat row has constant coefficient one. -/
@[simp] theorem polynomial_coeff_zero (c : ℝ) (n : ℕ) :
    (polynomial c n).coeff 0 = 1 := by
  rw [polynomial, heatDiagonal_coeff_zero, matchingSeed_coeff_zero]

/-- The leading coefficient of the bipartite heat row is `n!`. -/
@[simp] theorem polynomial_leadingCoeff (c : ℝ) (n : ℕ) :
    (polynomial c n).leadingCoeff = n.factorial := by
  rw [polynomial, heatDiagonal_leadingCoeff, leadingCoeff, matchingSeed_natDegree,
    coeff_matchingSeed, Nat.choose_self, Nat.cast_one, one_pow, one_mul]

/-- At nonnegative parameters every coefficient of the packing row is nonnegative. -/
theorem polynomial_hasNonnegCoeffs {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    HasNonnegCoeffs (polynomial c n) :=
  (matchingSeed_hasNonnegCoeffs n).heatDiagonal hc

/-- Adjacent heat rows have no common real zero at any nonnegative parameter. -/
theorem polynomial_no_common_root {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (t : ℝ) :
    ¬ ((polynomial c n).IsRoot t ∧ (polynomial c (n + 1)).IsRoot t) := by
  exact heatDiagonal_no_common_root_of_derivative (matchingSeed_isSimpleRealRooted (n + 1))
    (derivative_matchingSeed n) (matchingSeed_hasNonnegCoeffs n)
    (by rw [matchingSeed_coeff_zero]; exact one_ne_zero) hc t

/-- Nonnegative bipartite heat rows strictly interlace in the oriented order. -/
theorem polynomial_strictInterl {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    StrictInterl (polynomial c n) (polynomial c (n + 1)) := by
  let B := Icc (0 : ℝ) c
  let left : B := ⟨0, le_rfl, hc⟩
  let right : B := ⟨c, hc, le_rfl⟩
  have : PreconnectedSpace B := Subtype.preconnectedSpace isPreconnected_Icc
  have hpos (x : B) (j : ℕ) : HasPosLeadingCoeff (polynomial x j) := by
    rw [HasPosLeadingCoeff, polynomial_leadingCoeff]
    exact_mod_cast Nat.factorial_pos j
  have hco (j i : ℕ) : Continuous fun x : B => (polynomial x j).coeff i :=
    (continuous_coeff_heatDiagonal (matchingSeed j) i).comp continuous_subtype_val
  apply strictInterl_of_no_common_root_family (f := fun x : B => polynomial x (n + 1))
    (g := fun x : B => polynomial x n) (d := n + 1) (by lia)
    (hco _) (hco _) (fun x => hpos x _) (fun x => hpos x _)
    (fun x => polynomial_natDegree x _) (fun x => by rw [polynomial_natDegree]; lia)
    (fun x => polynomial_no_common_root x.2.1 n) (x₀ := left) _ right
  simpa only [polynomial, left, heatDiagonal_zero] using (matchingSeed_interlaces n).toStrictInterl

/-- Consecutive bipartite heat rows interlace with degree gap one. -/
theorem polynomial_interlaces {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    Interlaces (polynomial c n) (polynomial c (n + 1)) :=
  (polynomial_strictInterl hc n).toInterlaces (by simp only [polynomial_natDegree])

/-- Each row has exactly `n` simple negative zeros, and consecutive rows are strictly
interlacing with no common root. This includes both the matching endpoint and `c = 1`. -/
theorem polynomial_roots {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    IsSimpleRealRooted (polynomial c n) ∧ (polynomial c n).natDegree = n ∧
      (∀ r ∈ (polynomial c n).roots, r < 0) ∧
      Interlaces (polynomial c n) (polynomial c (n + 1)) ∧
      ∀ r, ¬ ((polynomial c n).IsRoot r ∧ (polynomial c (n + 1)).IsRoot r) := by
  have hi := polynomial_strictInterl hc n
  have hd := polynomial_no_common_root hc n
  refine ⟨⟨hi.1.1, hi.1.2, (hi.hasSimpleRoots_of_no_common_root hd).1⟩,
    polynomial_natDegree c n, ?_, polynomial_interlaces hc n, hd⟩
  exact roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne (polynomial_hasNonnegCoeffs hc n)
    (by rw [polynomial_coeff_zero]; exact one_ne_zero)

/-- Counting real roots with multiplicities gives exactly the row index. -/
@[simp] theorem polynomial_card_roots {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    (polynomial c n).roots.card = n := by
  rw [splits_iff_card_roots.mp (polynomial_roots hc n).1.2.1, polynomial_natDegree]

end RealRooted.BipartiteHeat
