module

public import RealRooted.Mathlib.RingTheory.PowerSeries.MapDerivation
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Derivation

/-!
# Coefficientwise derivations and formal substitution

We package the existing coefficientwise operation as a derivation, then prove
the chain rule for a scalar formal series substituted into a series with zero
constant coefficient. Truncation makes the proof entirely finite.
-/

public section

namespace RealRooted.TuranHurwitz

/-- Formal differentiation commutes with mapping the coefficient ring. -/
theorem derivative_map {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A)
    (p : PowerSeries R) :
    PowerSeries.derivative (p.map f) = (PowerSeries.derivative p).map f := by
  ext n
  simp [PowerSeries.coeff_derivative, PowerSeries.coeff_map]

/-- Mapping scalar coefficients into an algebra before substitution has no effect. -/
theorem subst_map_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (f : PowerSeries R) (g : PowerSeries A) (hg : PowerSeries.HasSubst g) :
    (f.map (algebraMap R A)).subst g = f.subst g := by
  ext n
  rw [PowerSeries.coeff_subst' hg, PowerSeries.coeff_subst' hg]
  apply finsum_congr
  intro k
  simp [PowerSeries.coeff_map, Algebra.smul_def]

/-- Mapping coefficients along an algebra homomorphism commutes with scalar substitution. -/
theorem map_subst_algebraHom {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (f : PowerSeries R)
    (g : PowerSeries A) (hg : PowerSeries.HasSubst g) :
    PowerSeries.map φ.toRingHom (f.subst g) = f.subst (g.map φ.toRingHom) := by
  change MvPowerSeries.map φ.toRingHom (f.subst g) = _
  rw [← subst_map_algebraMap f g hg, PowerSeries.map_subst hg]
  have hφ : (f.map (algebraMap R A)).map φ.toRingHom =
      f.map (algebraMap R B) := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_map]
    exact φ.commutes _
  rw [hφ, subst_map_algebraMap _ _ (hg.map φ.toRingHom)]
  rfl

/-- The formal substitution chain rule when the inner and outer coefficient rings differ. -/
theorem derivative_subst_algebra {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (f : PowerSeries R) (g : PowerSeries A) (hg : PowerSeries.HasSubst g) :
    PowerSeries.derivative (f.subst g) =
      (PowerSeries.derivative f).subst g * PowerSeries.derivative g := by
  rw [← subst_map_algebraMap f g hg, PowerSeries.derivative_subst hg, derivative_map,
    subst_map_algebraMap _ _ hg]

/-- A constant scalar series substitutes to the corresponding constant in the target algebra. -/
theorem subst_C_algebra {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (r : R) (g : PowerSeries A) (hg : PowerSeries.HasSubst g) :
    (PowerSeries.C r).subst g = PowerSeries.C (algebraMap R A r) := by
  rw [← subst_map_algebraMap _ g hg, PowerSeries.map_C, PowerSeries.subst_C]
  rfl

/-- The existing coefficientwise operation, packaged as a derivation of the power-series algebra. -/
@[expose] noncomputable def coefficientDerivation {R A : Type*} [CommSemiring R]
    [CommRing A] [Algebra R A] (D : Derivation R A A) :
    Derivation R (PowerSeries A) (PowerSeries A) where
  toFun := PowerSeries.mapDerivation D
  map_add' := PowerSeries.mapDerivation_add D
  map_smul' r f := by ext n; simp
  map_one_eq_zero' := PowerSeries.mapDerivation_one D
  leibniz' f g := by
    change PowerSeries.mapDerivation D (f * g) =
      f • PowerSeries.mapDerivation D g + g • PowerSeries.mapDerivation D f
    rw [PowerSeries.mapDerivation_mul]
    simp only [smul_eq_mul]
    ring

/-- A substitution coefficient depends only on outer coefficients through the same degree. -/
theorem coeff_subst_congr_of_le {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {g : PowerSeries A} (hg : PowerSeries.constantCoeff g = 0)
    {f h : PowerSeries R} (n : ℕ)
    (heq : ∀ k ≤ n, PowerSeries.coeff k f = PowerSeries.coeff k h) :
    PowerSeries.coeff n (f.subst g) = PowerSeries.coeff n (h.subst g) := by
  have hsubst := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  rw [PowerSeries.coeff_subst' hsubst, PowerSeries.coeff_subst' hsubst]
  apply finsum_congr
  intro k
  by_cases hk : k ≤ n
  · rw [heq k hk]
  · have hzero : PowerSeries.coeff n (g ^ k) = 0 := by
      apply PowerSeries.coeff_of_lt_order
      exact lt_of_lt_of_le (by exact_mod_cast (lt_of_not_ge hk))
        (PowerSeries.le_order_pow_of_constantCoeff_eq_zero k hg)
    simp only [hzero, smul_zero]

/-- Coefficientwise differentiation commutes with scalar formal substitution by the chain rule. -/
theorem mapDerivation_subst {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (f : PowerSeries R) (g : PowerSeries A)
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.mapDerivation D (f.subst g) =
      (PowerSeries.derivative f).subst g * PowerSeries.mapDerivation D g := by
  have hsubst := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  ext n
  let p := PowerSeries.trunc (n + 2) f
  have hleft : PowerSeries.coeff n (f.subst g) =
      PowerSeries.coeff n ((p : PowerSeries R).subst g) := by
    apply coeff_subst_congr_of_le hg
    intro k hk
    exact (PowerSeries.coeff_coe_trunc_of_lt (by lia)).symm
  have hright : PowerSeries.coeff n
      ((PowerSeries.derivative f).subst g * PowerSeries.mapDerivation D g) =
      PowerSeries.coeff n
        ((p.derivative : PowerSeries R).subst g * PowerSeries.mapDerivation D g) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    congr 1
    apply coeff_subst_congr_of_le hg
    intro k hk
    have hijsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
    dsimp [p]
    rw [← PowerSeries.derivative_coe, PowerSeries.coeff_derivative,
      PowerSeries.coeff_derivative, PowerSeries.coeff_coe_trunc_of_lt (by lia)]
  rw [PowerSeries.coeff_mapDerivation, hleft, hright,
    PowerSeries.subst_coe hsubst, PowerSeries.subst_coe hsubst]
  have hchain := Derivation.comp_aeval_eq (a := g) (coefficientDerivation D) p
  change PowerSeries.mapDerivation D (Polynomial.aeval g p) =
    Polynomial.aeval g p.derivative • PowerSeries.mapDerivation D g at hchain
  simpa only [PowerSeries.coeff_mapDerivation, smul_eq_mul] using
    congrArg (PowerSeries.coeff n) hchain

end RealRooted.TuranHurwitz
