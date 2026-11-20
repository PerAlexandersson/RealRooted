module

public import RealRooted.TuranHurwitz.BoundaryLimit

/-!
# Shi's Theorem 1.1(i)

Every extended Turán expression of the admissible recurrence is nonzero and
has no zero in `Re z > -lambda`. The proof also covers the zeroth Turán
order, where the expression is the square of a recurrence row.
-/

public section

namespace RealRooted.TuranHurwitz

/-- The complete nonzero and half-plane exclusion conclusion of Theorem 1.1(i). -/
theorem family_turan_stable {c : Parameters} (hc : c.Admissible) (m n : ℕ) :
    turan m n (family c) ≠ 0 ∧
      ∀ z : ℂ, -c.lam < z.re → Polynomial.aeval z (turan m n (family c)) ≠ 0 := by
  by_cases hcase : c.a₁ = 0 ∨ 0 < c.b₁ + c.tau * c.a₁
  · exact family_turan_stable_of_nondegenerate hc hcase m n
  · obtain ⟨ha, hb, ht, hb₂⟩ := exponential_boundary_of_not_nondegenerate hc hcase
    exact family_turan_stable_boundary hc ha hb ht hb₂ m n

/-- Every admissible extended Turán polynomial is nonzero. -/
theorem family_turan_ne_zero {c : Parameters} (hc : c.Admissible) (m n : ℕ) :
    turan m n (family c) ≠ 0 := (family_turan_stable hc m n).1

/-- Every admissible extended Turán polynomial excludes the required open half-plane. -/
theorem aeval_family_turan_ne_zero {c : Parameters} (hc : c.Admissible) (m n : ℕ)
    (z : ℂ) (hz : -c.lam < z.re) :
    Polynomial.aeval z (turan m n (family c)) ≠ 0 := (family_turan_stable hc m n).2 z hz

end RealRooted.TuranHurwitz
