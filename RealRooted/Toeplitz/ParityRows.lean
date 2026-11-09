module

import Mathlib.Tactic.Ring
public import Mathlib.RingTheory.PowerSeries.Expand
public import RealRooted.Toeplitz.HessenbergRows
public import RealRooted.Toeplitz.ParityBlock

/-!
# The parity-lifted rows `1 / (G(z²) + γ z - t z)`

For a square matrix `A` with `A i j = A j j` for `i ≤ j` and `G(z) = det (I + z A)`
(`hessenbergDet A`), the rows `P_n^γ(t)` are the coefficients of `zⁿ` in
`1 / (G(z²) + γ z - t z)` (`parityRow A γ n`).

Even/odd extraction, using `(G(z²) - t z)(G(z²) + t z) = G(z²)² - t² z²`, gives
`P_{2m}^0(t) = V_m(t²)` and `P_{2m+1}^0(t) = t U_m(t²)` where
`∑ U_m(u) wᵐ = 1 / (G(w)² - u w)` and `∑ V_m(u) wᵐ = G(w) / (G(w)² - u w)`
(`parityRow_zero_two_mul`, `parityRow_zero_two_mul_add_one`). The first is the Hessenberg row of
the block matrix `parityBlock A` (whose determinant polynomial is `G²`), and `V_m` is, up to the
reflection `u ↦ -u` and a sign, the first coordinate of its second block of the vector
recursion (`hessenbergSeries_parityBlock_natAdd_zero`). A shift `t ↦ t - γ` gives general `γ`
(`parityRow_eq_comp`).
-/

@[expose] public section

open Polynomial Matrix

noncomputable section

namespace RealRooted

variable {n : ℕ}

/-! ### The second block coordinate of the vector recursion -/

/-- The index of the first coordinate of the second block of the block matrix. -/
def parityIndex (n : ℕ) : Fin (n + 1 + (n + 1)) := Fin.natAdd (n + 1) (0 : Fin (n + 1))

/-- The series of the first coordinate of the second block of the block matrix is `G(z)` times
the series of the first coordinate:
`S_{q+1} = det (I + z A) · S_1`, where `S_i = ∑ₖ (-1)ᵏ f_{k,i}(-t) zᵏ`. -/
theorem hessenbergSeries_parityBlock_natAdd_zero (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) :
    hessenbergSeries (n := n + 1 + n) (parityBlock A) (parityIndex n) =
      hessenbergCoeffs (hessenbergDet A) * hessenbergSeries (n := n + 1 + n) (parityBlock A) 0 := by
  have hrowB : ∀ ⦃i j : Fin (n + 1 + (n + 1))⦄, i ≤ j →
      parityBlock A i j = parityBlock A j j :=
    fun i j h => parityBlock_row_eq hrow h
  set S := hessenbergSeries (n := n + 1 + n) (parityBlock A) with hS
  have hmul := hessenbergSeries_mulVec (n := n + 1 + n) (parityBlock A) hrowB
  -- the row relation, split into the two blocks of columns
  have hsplit : ∀ i, S i + PowerSeries.X *
      (∑ j : Fin (n + 1), hessenbergEmbed (parityBlock A i (Fin.castAdd (n + 1) j) -
          parityBlock A (Fin.castAdd (n + 1) j) (Fin.castAdd (n + 1) j)) *
        S (Fin.castAdd (n + 1) j) +
      ∑ j : Fin (n + 1), hessenbergEmbed (parityBlock A i (Fin.natAdd (n + 1) j) -
          parityBlock A (Fin.natAdd (n + 1) j) (Fin.natAdd (n + 1) j)) *
        S (Fin.natAdd (n + 1) j)) = S 0 := fun i => by
    rw [← Fin.sum_univ_add (fun j =>
      hessenbergEmbed (parityBlock A i j - parityBlock A j j) * S j)]
    exact hmul i
  -- the second block of columns does not contribute
  have hbot : ∀ (i' : Fin (n + 1)) (j : Fin (n + 1)),
      hessenbergEmbed (parityBlock A (Fin.castAdd (n + 1) i') (Fin.natAdd (n + 1) j) -
        parityBlock A (Fin.natAdd (n + 1) j) (Fin.natAdd (n + 1) j)) *
          S (Fin.natAdd (n + 1) j) = 0 := fun i' j => by
    rw [parityBlock_castAdd_natAdd, parityBlock_natAdd_natAdd, hrow (Fin.zero_le j), sub_self,
      map_zero, zero_mul]
  have hbot' : ∀ j : Fin (n + 1),
      hessenbergEmbed (parityBlock A (Fin.natAdd (n + 1) (0 : Fin (n + 1)))
          (Fin.natAdd (n + 1) j) - parityBlock A (Fin.natAdd (n + 1) j) (Fin.natAdd (n + 1) j)) *
        S (Fin.natAdd (n + 1) j) = 0 := fun j => by
    rw [parityBlock_natAdd_natAdd, parityBlock_natAdd_natAdd, hrow (Fin.zero_le j), sub_self,
      map_zero, zero_mul]
  -- the top block solves the triangular system of `A`
  have hT : ∀ i, (fun j => S (Fin.castAdd (n + 1) j)) i + PowerSeries.X *
      ∑ j, hessenbergEmbed (A i j - A j j) * (fun j => S (Fin.castAdd (n + 1) j)) j =
        (fun j => S (Fin.castAdd (n + 1) j)) 0 := fun i => by
    have h := hsplit (Fin.castAdd (n + 1) i)
    simp only [parityBlock_castAdd_castAdd, hbot i, Finset.sum_const_zero, add_zero] at h
    exact h
  have hkey := X_mul_sum_diag_mul_eq A hrow (fun j => S (Fin.castAdd (n + 1) j)) hT
  have h := hsplit (Fin.natAdd (n + 1) (0 : Fin (n + 1)))
  have hneg : ∑ j : Fin (n + 1), hessenbergEmbed (parityBlock A
        (Fin.natAdd (n + 1) (0 : Fin (n + 1))) (Fin.castAdd (n + 1) j) -
        parityBlock A (Fin.castAdd (n + 1) j) (Fin.castAdd (n + 1) j)) *
      S (Fin.castAdd (n + 1) j) =
        -∑ j, hessenbergEmbed (A j j) * S (Fin.castAdd (n + 1) j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [parityBlock_natAdd_castAdd, parityBlock_castAdd_castAdd, zero_sub, map_neg, neg_mul]
  rw [Finset.sum_eq_zero fun j _ => hbot' j, hneg, add_zero] at h
  have hc : S (Fin.castAdd (n + 1) (0 : Fin (n + 1))) = S 0 := rfl
  rw [hc] at hkey
  change S (Fin.natAdd (n + 1) (0 : Fin (n + 1))) = _
  linear_combination h + hkey

/-! ### The rows -/

@[simp] lemma coeff_hessenbergCoeffs (F : ℝ[X]) (k : ℕ) :
    PowerSeries.coeff k (hessenbergCoeffs F) = C (F.coeff k) := by
  simp [hessenbergCoeffs]

/-- The denominator `G(z²) + γ z - t z` of the parity-lifted generating function, with
`G(z) = det (I + z A)`. -/
def parityDenominator (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (γ : ℝ) : PowerSeries ℝ[X] :=
  PowerSeries.expand 2 two_ne_zero (hessenbergCoeffs (hessenbergDet A)) +
    PowerSeries.C (C γ) * PowerSeries.X - PowerSeries.C X * PowerSeries.X

lemma constantCoeff_parityDenominator (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (γ : ℝ) :
    PowerSeries.constantCoeff (parityDenominator A γ) = ((1 : (ℝ[X])ˣ) : ℝ[X]) := by
  rw [parityDenominator, map_sub, map_add, map_mul, map_mul, PowerSeries.constantCoeff_X,
    mul_zero, mul_zero, add_zero, sub_zero, PowerSeries.constantCoeff_expand,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [hessenbergDet_coeff_zero]

/-- The power series `1 / (G(z²) + γ z - t z)` in `z` over `ℝ[t]`. -/
def parityRowSeries (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (γ : ℝ) : PowerSeries ℝ[X] :=
  PowerSeries.invOfUnit (parityDenominator A γ) 1

/-- The row `P_k^γ(t)`: the coefficient of `zᵏ` in `1 / (G(z²) + γ z - t z)`,
`G(z) = det (I + z A)`. -/
def parityRow (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (γ : ℝ) (k : ℕ) : ℝ[X] :=
  PowerSeries.coeff k (parityRowSeries A γ)

lemma parityDenominator_mul_parityRowSeries (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (γ : ℝ) :
    parityDenominator A γ * parityRowSeries A γ = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simpa using constantCoeff_parityDenominator A γ)

/-- The rows form the generating function of `1 / (G(z²) + γ z - t z)`. -/
theorem parityDenominator_mul_mk_parityRow (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (γ : ℝ) :
    parityDenominator A γ * PowerSeries.mk (parityRow A γ) = 1 := by
  have : PowerSeries.mk (parityRow A γ) = parityRowSeries A γ := by
    ext k; simp [parityRow]
  rw [this]
  exact parityDenominator_mul_parityRowSeries A γ

/-! ### Even/odd extraction -/

/-- The substitution `t ↦ t²` on coefficients, as a ring homomorphism. -/
abbrev sqSubst : ℝ[X] →+* ℝ[X] := (Polynomial.expand ℝ 2).toRingHom

lemma map_sqSubst_hessenbergCoeffs (F : ℝ[X]) :
    PowerSeries.map sqSubst (hessenbergCoeffs F) = hessenbergCoeffs F := by
  ext k
  simp [sqSubst]

/-- The row series of the block matrix, the series `∑ U_m(u) wᵐ = 1 / (G(w)² - u w)`. -/
abbrev parityU (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : PowerSeries ℝ[X] :=
  hessenbergRowSeries (n := n + 1 + n) (parityBlock A)

/-- The series `∑ V_m(u) wᵐ = G(w) / (G(w)² - u w)`. -/
def parityV (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : PowerSeries ℝ[X] :=
  hessenbergCoeffs (hessenbergDet A) * parityU A

/-- **Even/odd decomposition of the generating function** (`γ = 0`):
`1 / (G(z²) - t z) = (G(z²) + t z) · U(z², t²)` where `U` is the row series of the block
matrix. -/
theorem parityRowSeries_zero_eq (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    parityRowSeries A 0 =
      (PowerSeries.expand 2 two_ne_zero (hessenbergCoeffs (hessenbergDet A)) +
        PowerSeries.C X * PowerSeries.X) *
      PowerSeries.expand 2 two_ne_zero (PowerSeries.map sqSubst (parityU A)) := by
  set D := hessenbergCoeffs (hessenbergDet A) with hD
  have hB : hessenbergDenominator (n := n + 1 + n) (parityBlock A) * parityU A = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simpa using
      constantCoeff_hessenbergDenominator (n := n + 1 + n) (parityBlock A))
  have hmapDen : PowerSeries.map sqSubst (hessenbergDenominator (n := n + 1 + n)
      (parityBlock A)) = D ^ 2 - PowerSeries.C (X ^ 2) * PowerSeries.X := by
    rw [hessenbergDenominator, hessenbergDet_parityBlock, map_pow hessenbergCoeffs, map_sub,
      map_mul, map_pow,
      map_sqSubst_hessenbergCoeffs, PowerSeries.map_C, PowerSeries.map_X]
    simp [hD, sqSubst]
  have h1 : PowerSeries.expand 2 two_ne_zero (PowerSeries.map sqSubst
      (hessenbergDenominator (n := n + 1 + n) (parityBlock A) * parityU A)) = 1 := by
    rw [hB]; simp
  rw [map_mul, map_mul, hmapDen, map_sub, map_pow, map_mul, PowerSeries.expand_C,
    PowerSeries.expand_X] at h1
  have hC : PowerSeries.C (X ^ 2 : ℝ[X]) = PowerSeries.C X * PowerSeries.C X := by
    rw [← map_mul, sq]
  have key : parityDenominator A 0 * ((PowerSeries.expand 2 two_ne_zero D +
      PowerSeries.C X * PowerSeries.X) *
      PowerSeries.expand 2 two_ne_zero (PowerSeries.map sqSubst (parityU A))) = 1 := by
    rw [hC] at h1
    simp only [parityDenominator, ← hD, map_zero, zero_mul, add_zero]
    linear_combination h1
  calc parityRowSeries A 0 = parityRowSeries A 0 * 1 := (mul_one _).symm
    _ = parityRowSeries A 0 * (parityDenominator A 0 * ((PowerSeries.expand 2 two_ne_zero D +
          PowerSeries.C X * PowerSeries.X) * PowerSeries.expand 2 two_ne_zero
            (PowerSeries.map sqSubst (parityU A)))) := by rw [key]
    _ = _ := by
      rw [← mul_assoc, mul_comm (parityRowSeries A 0), parityDenominator_mul_parityRowSeries,
        one_mul]

lemma coeff_map_sqSubst_parityU (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.map sqSubst (parityU A)) =
      Polynomial.expand ℝ 2 (hessenbergRow (n := n + 1 + n) (parityBlock A) m) := by
  rw [PowerSeries.coeff_map]
  rfl

private lemma not_two_dvd_two_mul_add_one (m : ℕ) : ¬ 2 ∣ 2 * m + 1 := by lia

/-- **Odd rows**: `P_{2m+1}^0(t) = t U_m(t²)`, with `U_m` the Hessenberg rows of the block matrix
(`∑ U_m(u) wᵐ = 1 / (G(w)² - u w)`). -/
theorem parityRow_zero_two_mul_add_one (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (m : ℕ) :
    parityRow A 0 (2 * m + 1) =
      X * Polynomial.expand ℝ 2 (hessenbergRow (n := n + 1 + n) (parityBlock A) m) := by
  rw [parityRow, parityRowSeries_zero_eq, add_mul, ← map_mul, map_add, mul_assoc,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_expand_of_not_dvd _ _ _
      (not_two_dvd_two_mul_add_one m),
    zero_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand_mul,
    coeff_map_sqSubst_parityU]

/-- **Even rows**: `P_{2m}^0(t) = V_m(t²)`, with `∑ V_m(u) wᵐ = G(w) / (G(w)² - u w)`. -/
theorem parityRow_zero_two_mul (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (m : ℕ) :
    parityRow A 0 (2 * m) = Polynomial.expand ℝ 2 (PowerSeries.coeff m (parityV A)) := by
  have hodd : PowerSeries.coeff (2 * m) (PowerSeries.C X * (PowerSeries.X *
      PowerSeries.expand 2 two_ne_zero (PowerSeries.map sqSubst (parityU A)))) = 0 := by
    rw [PowerSeries.coeff_C_mul]
    rcases m with _ | m
    · simp
    · rw [show 2 * (m + 1) = (2 * m + 1) + 1 by lia, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_expand_of_not_dvd _ _ _ (not_two_dvd_two_mul_add_one m), mul_zero]
  have hmap : PowerSeries.map sqSubst (parityV A) = hessenbergCoeffs (hessenbergDet A) *
      PowerSeries.map sqSubst (parityU A) := by
    rw [parityV, map_mul, map_sqSubst_hessenbergCoeffs]
  rw [parityRow, parityRowSeries_zero_eq, add_mul, ← map_mul, map_add, mul_assoc, hodd, add_zero,
    PowerSeries.coeff_expand_mul, ← hmap, PowerSeries.coeff_map]
  rfl

/-! ### Identification with the vector recursion of the block matrix -/

/-- `U_m = (-1)ᵐ f_{m,1}(-u)` for the vector recursion of the block matrix. -/
theorem hessenbergRow_parityBlock_eq (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (m : ℕ) :
    hessenbergRow (n := n + 1 + n) (parityBlock A) m =
      C ((-1 : ℝ) ^ m) * (hessenbergVector (n := n + 1 + n) (parityBlock A) m 0).comp (-X) :=
  hessenbergRow_eq (n := n + 1 + n) (parityBlock A) (fun _ _ h => parityBlock_row_eq hrow h) m

/-- `V_m = (-1)ᵐ f_{m,q+1}(-u)` for the vector recursion of the block matrix. -/
theorem coeff_parityV_eq (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (m : ℕ) :
    PowerSeries.coeff m (parityV A) = C ((-1 : ℝ) ^ m) *
      (hessenbergVector (n := n + 1 + n) (parityBlock A) m (parityIndex n)).comp (-X) := by
  have hrowB : ∀ ⦃i j : Fin (n + 1 + (n + 1))⦄, i ≤ j → parityBlock A i j = parityBlock A j j :=
    fun _ _ h => parityBlock_row_eq hrow h
  have h : parityV A = hessenbergSeries (n := n + 1 + n) (parityBlock A) (parityIndex n) := by
    rw [parityV, parityU, hessenbergRowSeries_eq_hessenbergSeries_zero (n := n + 1 + n)
      (parityBlock A) hrowB, hessenbergSeries_parityBlock_natAdd_zero A hrow]
  rw [h, hessenbergSeries, PowerSeries.coeff_mk, hessenbergSignedVector]

/-! ### The shift `t ↦ t - γ` -/

/-- **Arbitrary `γ`**: `P_k^γ(t) = P_k^0(t - γ)`. -/
theorem parityRow_eq_comp (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (γ : ℝ) (k : ℕ) :
    parityRow A γ k = (parityRow A 0 k).comp (X - C γ) := by
  set ψ : ℝ[X] →+* ℝ[X] := Polynomial.compRingHom (X - C γ) with hψ
  have hD : PowerSeries.map ψ (hessenbergCoeffs (hessenbergDet A)) =
      hessenbergCoeffs (hessenbergDet A) := by
    ext k
    simp [hψ]
  have hden : PowerSeries.map ψ (parityDenominator A 0) = parityDenominator A γ := by
    simp only [parityDenominator, map_sub, map_add, map_mul, PowerSeries.map_C,
      PowerSeries.map_X, PowerSeries.map_expand, hD]
    simp only [hψ, Polynomial.coe_compRingHom_apply, map_zero, zero_mul,
      add_zero, X_comp, map_sub]
    ring
  have key : parityDenominator A γ * PowerSeries.map ψ (parityRowSeries A 0) = 1 := by
    rw [← hden, ← map_mul, parityDenominator_mul_parityRowSeries, map_one]
  have hser : parityRowSeries A γ = PowerSeries.map ψ (parityRowSeries A 0) := by
    calc parityRowSeries A γ = parityRowSeries A γ * 1 := (mul_one _).symm
      _ = parityRowSeries A γ * (parityDenominator A γ *
          PowerSeries.map ψ (parityRowSeries A 0)) := by rw [key]
      _ = _ := by
        rw [← mul_assoc, mul_comm (parityRowSeries A γ), parityDenominator_mul_parityRowSeries,
          one_mul]
  rw [parityRow, hser, PowerSeries.coeff_map]
  rfl

end RealRooted
