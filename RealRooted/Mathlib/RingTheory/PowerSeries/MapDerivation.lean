import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Applying a derivation of the coefficients to a power series

For a derivation `D : Derivation R A A` of a commutative ring `A`, `PowerSeries.mapDerivation D`
applies `D` to every coefficient of a power series over `A`. It satisfies the Leibniz rule,
so it is again a derivation; for example, with `A = K[v]` and `D = d/dv` it is the partial
derivative in `v` of a power series in a second variable.
-/

namespace PowerSeries

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- Apply a derivation of the coefficient ring to every coefficient. -/
noncomputable def mapDerivation (D : Derivation R A A) (f : A⟦X⟧) : A⟦X⟧ :=
  mk fun n ↦ D (coeff n f)

@[simp]
theorem coeff_mapDerivation (D : Derivation R A A) (f : A⟦X⟧) (n : ℕ) :
    coeff n (mapDerivation D f) = D (coeff n f) := by
  simp [mapDerivation]

theorem mapDerivation_add (D : Derivation R A A) (f g : A⟦X⟧) :
    mapDerivation D (f + g) = mapDerivation D f + mapDerivation D g := by
  ext n; simp

theorem mapDerivation_sub (D : Derivation R A A) (f g : A⟦X⟧) :
    mapDerivation D (f - g) = mapDerivation D f - mapDerivation D g := by
  ext n; simp

/-- The Leibniz rule. -/
theorem mapDerivation_mul (D : Derivation R A A) (f g : A⟦X⟧) :
    mapDerivation D (f * g) = mapDerivation D f * g + f * mapDerivation D g := by
  ext n
  rw [coeff_mapDerivation, map_add, coeff_mul, coeff_mul, coeff_mul, map_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [coeff_mapDerivation, Derivation.leibniz, smul_eq_mul]
  ring

@[simp]
theorem mapDerivation_C (D : Derivation R A A) (a : A) :
    mapDerivation D (C a) = C (D a) := by
  ext n; simp [coeff_C]; split_ifs <;> simp

@[simp]
theorem mapDerivation_X (D : Derivation R A A) : mapDerivation D (X : A⟦X⟧) = 0 := by
  ext n; simp [coeff_X]; split_ifs <;> simp

@[simp]
theorem mapDerivation_one (D : Derivation R A A) : mapDerivation D (1 : A⟦X⟧) = 0 := by
  ext n; simp [coeff_one]; split_ifs <;> simp

theorem mapDerivation_X_pow (D : Derivation R A A) (k : ℕ) :
    mapDerivation D ((X : A⟦X⟧) ^ k) = 0 := by
  ext n; simp [coeff_X_pow]; split_ifs <;> simp

end PowerSeries
