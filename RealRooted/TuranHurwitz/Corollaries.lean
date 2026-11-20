module

public import RealRooted.TuranHurwitz.Main

/-!
# The Bell and Table 1 corollaries

The families are defined by their differential recurrences. We make no
combinatorial identification with independently defined polynomial sequences.
Every result holds at all natural indices, including the harmless square case `n = 0`.
-/

public section

namespace RealRooted.TuranHurwitz

/-- The all-index Bell conclusion, with the Bell family defined by its recurrence. -/
theorem bell_turan_stable (m n : ℕ) :
    turan m n bell ≠ 0 ∧
      ∀ z : ℂ, 0 < z.re → Polynomial.aeval z (turan m n bell) ≠ 0 := by
  simpa only [bell, neg_zero] using family_turan_stable bell_admissible m n

/-- The Stirling–Whitney–Riordan recurrence under the admissible parameter conditions. -/
theorem stirlingWhitneyRiordan_turan_stable (a₁ a₂ b₁ b₂ lam : ℝ)
    (hc : (Parameters.mk a₁ a₂ b₁ b₂ lam 0).Admissible) (m n : ℕ) :
    turan m n (stirlingWhitneyRiordan a₁ a₂ b₁ b₂ lam) ≠ 0 ∧
      ∀ z : ℂ, -lam < z.re → Polynomial.aeval z
        (turan m n (stirlingWhitneyRiordan a₁ a₂ b₁ b₂ lam)) ≠ 0 := by
  exact family_turan_stable hc m n

/-- The all-index ordinary Eulerian conclusion. -/
theorem eulerian_turan_stable (m n : ℕ) :
    turan m n eulerian ≠ 0 ∧
      ∀ z : ℂ, 0 < z.re → Polynomial.aeval z (turan m n eulerian) ≠ 0 := by
  simpa only [eulerian, neg_zero] using family_turan_stable eulerian_admissible m n

/-- The all-index type B Eulerian conclusion. -/
theorem typeBEulerian_turan_stable (m n : ℕ) :
    turan m n typeBEulerian ≠ 0 ∧
      ∀ z : ℂ, 0 < z.re → Polynomial.aeval z (turan m n typeBEulerian) ≠ 0 := by
  simpa only [typeBEulerian, neg_zero] using family_turan_stable typeBEulerian_admissible m n

/-- The all-index colored Eulerian conclusion for at least one color. -/
theorem coloredEulerian_turan_stable {ell : ℕ} (hell : 1 ≤ ell) (m n : ℕ) :
    turan m n (coloredEulerian ell) ≠ 0 ∧
      ∀ z : ℂ, 0 < z.re → Polynomial.aeval z (turan m n (coloredEulerian ell)) ≠ 0 := by
  simpa only [coloredEulerian, neg_zero] using
    family_turan_stable (coloredEulerian_admissible hell) m n

/-- The all-index cycle-weighted Eulerian conclusion for positive weight. -/
theorem cycleWeightedEulerian_turan_stable {theta : ℝ} (htheta : 0 < theta) (m n : ℕ) :
    turan m n (cycleWeightedEulerian theta) ≠ 0 ∧
      ∀ z : ℂ, 0 < z.re →
        Polynomial.aeval z (turan m n (cycleWeightedEulerian theta)) ≠ 0 := by
  simpa only [cycleWeightedEulerian, neg_zero] using
    family_turan_stable (cycleWeightedEulerian_admissible htheta) m n

/-- The all-index type A reciprocal Eulerian conclusion for `k > 0`. -/
theorem reciprocalEulerian_turan_stable {k : ℝ} (hk : 0 < k) (m n : ℕ) :
    turan m n (reciprocalEulerian k) ≠ 0 ∧
      ∀ z : ℂ, 0 < z.re → Polynomial.aeval z (turan m n (reciprocalEulerian k)) ≠ 0 := by
  simpa only [reciprocalEulerian, neg_zero] using
    family_turan_stable (reciprocalEulerian_admissible hk) m n

/-- The all-index type B reciprocal Eulerian conclusion for `k > 0`. -/
theorem reciprocalTypeBEulerian_turan_stable {k : ℝ} (hk : 0 < k) (m n : ℕ) :
    turan m n (reciprocalTypeBEulerian k) ≠ 0 ∧
      ∀ z : ℂ, 0 < z.re → Polynomial.aeval z (turan m n (reciprocalTypeBEulerian k)) ≠ 0 := by
  simpa only [reciprocalTypeBEulerian, neg_zero] using
    family_turan_stable (reciprocalTypeBEulerian_admissible hk) m n

/-- The all-index `r` Bell conclusion for every natural `r`. -/
theorem rBell_turan_stable (r m n : ℕ) :
    turan m n (rBell r) ≠ 0 ∧
      ∀ z : ℂ, 0 < z.re → Polynomial.aeval z (turan m n (rBell r)) ≠ 0 := by
  simpa only [rBell, neg_zero] using family_turan_stable (rBell_admissible r) m n

/-- The all-index geometric conclusion. -/
theorem geometric_turan_stable (m n : ℕ) :
    turan m n geometric ≠ 0 ∧
      ∀ z : ℂ, 0 < z.re → Polynomial.aeval z (turan m n geometric) ≠ 0 := by
  simpa only [geometric, neg_zero] using family_turan_stable geometric_admissible m n

/-- The all-index Dowling conclusion for `r > 0`. -/
theorem dowling_turan_stable {r : ℝ} (hr : 0 < r) (m n : ℕ) :
    turan m n (dowling r) ≠ 0 ∧
      ∀ z : ℂ, 0 < z.re → Polynomial.aeval z (turan m n (dowling r)) ≠ 0 := by
  simpa only [dowling, neg_zero] using family_turan_stable (dowling_admissible hr) m n

/-- The all-index Tanny–geometric conclusion for `r ≥ 1`. -/
theorem tannyGeometric_turan_stable {r : ℝ} (hr : 1 ≤ r) (m n : ℕ) :
    turan m n (tannyGeometric r) ≠ 0 ∧
      ∀ z : ℂ, 0 < z.re → Polynomial.aeval z (turan m n (tannyGeometric r)) ≠ 0 := by
  simpa only [tannyGeometric, neg_zero] using
    family_turan_stable (tannyGeometric_admissible hr) m n

/-- The all-index Riordan conclusion with its shifted boundary at `-1`. -/
theorem riordan_turan_stable (m n : ℕ) :
    turan m n riordan ≠ 0 ∧
      ∀ z : ℂ, -1 < z.re → Polynomial.aeval z (turan m n riordan) ≠ 0 := by
  exact family_turan_stable riordan_admissible m n

end RealRooted.TuranHurwitz
