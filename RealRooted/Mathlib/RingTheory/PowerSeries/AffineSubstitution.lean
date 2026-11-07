/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-! Extracting a polynomial parameter from a bivariate formal substitution. -/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- Lifting coefficients along the algebra map does not affect evaluation
at a valid substitution in the target coefficient algebra. -/
theorem subst_map_algebraMap {S : Type*} [CommRing S] [Algebra R S]
    (b : PowerSeries S) (hb : HasSubst b) (F : PowerSeries R) :
    subst (R := S) b (map (algebraMap R S) F) = subst (R := R) b F := by
  rw [map_algebraMap_eq_subst_X,
    subst_comp_subst_apply HasSubst.X' hb, subst_X hb]

/-- A monomial in the parameter stays concentrated in its original
parameter degree after the other variable is expanded. -/
theorem coeff_coeff_affine_monomial (U V : PowerSeries R) (a b n k : ℕ) :
    (coeff n ((C Polynomial.X * map Polynomial.C V) ^ a *
      (map Polynomial.C U) ^ b)).coeff k =
        if k = a then coeff n (V ^ a * U ^ b) else 0 := by
  have hseries : (C Polynomial.X * map Polynomial.C V) ^ a *
      (map Polynomial.C U) ^ b =
      C (Polynomial.X ^ a) * map Polynomial.C (V ^ a * U ^ b) := by
    simp only [mul_pow, map_mul, map_pow]
    ring
  rw [hseries, coeff_C_mul, coeff_map, mul_comm,
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
  simp only [eq_comm]

/-- A finitely supported exponent vector on two variables is uniquely
determined by one fixed exponent and the other arbitrary exponent. -/
theorem finsum_fin_two_ite (k : ℕ) (f : (Fin 2 →₀ ℕ) → R) :
    (∑ᶠ e, if e 0 = k then f e else 0) =
      ∑ᶠ m : ℕ, f (Finsupp.single 0 k + Finsupp.single 1 m) := by
  classical
  let g : ℕ → Fin 2 →₀ ℕ := fun m => Finsupp.single 0 k + Finsupp.single 1 m
  have hg : Function.Injective g := by
    intro m m' h
    have hh := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
    simpa [g] using hh
  have hrange : Set.range g = {e | e 0 = k} := by
    ext e
    constructor
    · rintro ⟨m, rfl⟩
      simp [g]
    · intro he
      change e 0 = k at he
      refine ⟨e 1, ?_⟩
      ext i
      fin_cases i <;> simp [g, he]
  calc
    _ = ∑ᶠ e ∈ Set.range g, f e := by
      rw [finsum_mem_def]
      apply finsum_congr
      intro e
      simp [hrange, Set.indicator]
    _ = _ := finsum_mem_range hg

/-- Substituting `tV(u)` for the first variable and `U(u)` for the
second variable extracts the first-variable exponent exactly. The
constant-term assumptions make both substitutions valid in the `u`-adic
topology. -/
theorem coeff_coeff_subst_affine
    (U V : PowerSeries R) (hU : constantCoeff U = 0) (hV : constantCoeff V = 0)
    (F : MvPowerSeries (Fin 2) R) (n k : ℕ) :
    (coeff n (MvPowerSeries.subst
      (fun s : Fin 2 => if s = 0 then C Polynomial.X * map Polynomial.C V
        else map Polynomial.C U) F)).coeff k =
      ∑ᶠ m : ℕ, MvPowerSeries.coeff
        (Finsupp.single 0 k + Finsupp.single 1 m) F * coeff n (V ^ k * U ^ m) := by
  classical
  let a : Fin 2 → PowerSeries (Polynomial R) := fun s =>
    if s = 0 then C Polynomial.X * map Polynomial.C V else map Polynomial.C U
  have ha : MvPowerSeries.HasSubst a := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s
    change constantCoeff (a s) = 0
    rw [← coeff_zero_eq_constantCoeff_apply]
    fin_cases s
    · change coeff 0 (C Polynomial.X * map Polynomial.C V) = 0
      rw [coeff_C_mul, coeff_map, coeff_zero_eq_constantCoeff_apply,
        hV, map_zero, mul_zero]
    · change coeff 0 (map Polynomial.C U) = 0
      rw [coeff_map, coeff_zero_eq_constantCoeff_apply, hU, map_zero]
  have hterm (e : Fin 2 →₀ ℕ) :
      (Polynomial.lcoeff R k)
        (MvPowerSeries.coeff e F •
          coeff n (e.prod fun s d => (a s) ^ d)) =
        if e 0 = k then MvPowerSeries.coeff e F *
          coeff n (V ^ (e 0) * U ^ (e 1)) else 0 := by
    have hp : (e.prod fun s d => (a s) ^ d) =
        (C Polynomial.X * map Polynomial.C V) ^ (e 0) *
          (map Polynomial.C U) ^ (e 1) := by
      rw [e.prod_fintype _ (fun s => pow_zero _), Fin.prod_univ_two]
      simp [a]
    rw [LinearMap.map_smul, Polynomial.lcoeff_apply, hp,
      coeff_coeff_affine_monomial]
    simp only [smul_eq_mul]
    by_cases he : e 0 = k
    · rw [ite_eq_left he.symm, ite_eq_left he]
    · rw [ite_eq_right (Ne.symm he), ite_eq_right he, mul_zero]
  change (Polynomial.lcoeff R k)
    (MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.subst a F)) = _
  rw [MvPowerSeries.coeff_subst ha]
  have hmap := (Polynomial.lcoeff R k).toAddMonoidHom.map_finsum
    (MvPowerSeries.coeff_subst_finite ha F (Finsupp.single () n))
  simp only [LinearMap.toAddMonoidHom_coe] at hmap
  rw [hmap]
  change (∑ᶠ e, (Polynomial.lcoeff R k)
    (MvPowerSeries.coeff e F • coeff n (e.prod fun s d => (a s) ^ d))) = _
  simp_rw [hterm]
  rw [finsum_fin_two_ite]
  apply finsum_congr
  intro m
  simp

end PowerSeries
