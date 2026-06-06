module

public import Mathlib.Algebra.Polynomial.Splits

public section

namespace Polynomial
variable {R : Type*} [CommRing R] [IsDomain R] {f g : R[X]}

lemma Splits.of_dvd' (hg : Splits g) (hgf : g = 0 → f = 0) (hfg : f ∣ g) : Splits f := by
  obtain rfl | hg₀ := eq_or_ne g 0
  · simp_all
  · exact .of_dvd hg hg₀ hfg

@[simp] lemma splits_mul' : (f * g).Splits ↔ (f.Splits ∨ g = 0) ∧ (g.Splits ∨ f = 0) where
  mp hpq := by
    obtain rfl | hf₀ := eq_or_ne f 0
    · simp
    obtain rfl | hg₀ := eq_or_ne g 0
    · simp
    simp_all [or_false, splits_mul_iff]
  mpr := by rintro ⟨hp | rfl, hq | rfl⟩ <;> simp [*]

@[simp high] lemma splits_X_mul : (X * f).Splits ↔ f.Splits := by simp
@[simp high] lemma splits_mul_X : (f * X).Splits ↔ f.Splits := by simp [mul_comm f]

alias Splits.of_natDegree_eq_zero := splits_of_natDegree_eq_zero

end Polynomial
