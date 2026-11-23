module

public import RealRooted.LaguerreInequalities.Analytic

/-!
# Real translations of generalized Laguerre inequalities

Translation of the entire function by a real number simply translates the real
point at which its generalized Laguerre coefficient is evaluated.
-/

public section

open Complex

namespace RealRooted

/-- Translating a function by a real number translates its Laguerre product's base point. -/
theorem laguerreProduct_comp_add_real (f : ℂ → ℂ) (a x : ℝ) (z : ℂ) :
    laguerreProduct (fun w => f (w + a)) x z = laguerreProduct f (x + a) z := by
  unfold laguerreProduct
  push_cast
  congr 2 <;> ring

/-- Translating a function by a real number translates each generalized Laguerre coefficient. -/
theorem laguerreCoefficient_comp_add_real (f : ℂ → ℂ) (a x : ℝ) (n : ℕ) :
    laguerreCoefficient (fun w => f (w + a)) x n = laguerreCoefficient f (x + a) n := by
  have heq : laguerreProduct (fun w => f (w + a)) x = laguerreProduct f (x + a) :=
    funext (laguerreProduct_comp_add_real f a x)
  simp only [laguerreCoefficient, heq]

end RealRooted
