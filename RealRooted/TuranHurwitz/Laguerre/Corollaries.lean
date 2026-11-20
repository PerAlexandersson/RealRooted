module

public import RealRooted.TuranHurwitz.Laguerre.Stability

/-!
# Reflected Laguerre Turán stability

The families are defined by their differential recurrences. The ordinary
case is the recurrence form of CGV Conjecture 4.4.
-/

public section

namespace RealRooted.TuranHurwitz

/-- All extended Turán expressions of the reflected Table 1 Laguerre recurrence are stable. -/
theorem reflectedLaguerre_turan_stable (N : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) (m n : ℕ) :
    turan m n (reflectedLaguerre N lam) ≠ 0 ∧
      ∀ z : ℂ, -lam < z.re →
        Polynomial.aeval z (turan m n (reflectedLaguerre N lam)) ≠ 0 := by
  exact laguerreFamily_turan_stable (reflectedLaguerre_admissible N hlam) m n

/-- CGV Conjecture 4.4 for the ordinary reflected Laguerre recurrence, at all indices. -/
theorem reflectedOrdinaryLaguerre_turan_stable (m n : ℕ) :
    turan m n reflectedOrdinaryLaguerre ≠ 0 ∧
      ∀ z : ℂ, 0 < z.re →
        Polynomial.aeval z (turan m n reflectedOrdinaryLaguerre) ≠ 0 := by
  simpa only [reflectedOrdinaryLaguerre, neg_zero] using
    reflectedLaguerre_turan_stable 0 (le_refl (0 : ℝ)) m n

end RealRooted.TuranHurwitz
