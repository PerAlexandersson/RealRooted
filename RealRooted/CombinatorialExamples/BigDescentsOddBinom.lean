import RealRooted.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Order.Interval.Finset.Nat

open Polynomial
open scoped BigOperators

noncomputable section

namespace BigDescents

noncomputable def oddBinomAuxReal (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range ((n + 1) / 2),
    C ((Nat.choose n (2 * k + 1) : ℝ)) * X ^ (2 * k)

lemma coeff_one_sub_X_pow (n k : ℕ) :
    (((1 : ℝ[X]) - X) ^ n).coeff k =
      (-1 : ℝ) ^ k * (n.choose k : ℝ) := by
  rw [show (1 : ℝ[X]) - X = -(X + C (-1 : ℝ)) by
    rw [sub_eq_add_neg]
    rw [map_neg, C_1]
    abel]
  rw [neg_pow]
  rw [show ((-1 : ℝ[X]) ^ n) = C ((-1 : ℝ) ^ n) by simp]
  rw [coeff_C_mul]
  rw [Polynomial.coeff_X_add_C_pow]
  by_cases hk : k ≤ n
  · have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ (n - k) = (-1 : ℝ) ^ k := by
      nth_rw 1 [← Nat.add_sub_of_le hk]
      rw [pow_add]
      rw [mul_assoc]
      rw [← pow_add]
      have hEven : Even ((n - k) + (n - k)) := ⟨n - k, by omega⟩
      rw [hEven.neg_one_pow]
      simp
    rw [← mul_assoc, hsign]
  · have hchoose : n.choose k = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)
    simp [hchoose]

lemma coeff_oddBinomAuxReal_even (n k : ℕ) :
    (oddBinomAuxReal n).coeff (2 * k) =
      (n.choose (2 * k + 1) : ℝ) := by
  simp [oddBinomAuxReal]
  intro h
  rw [Nat.choose_eq_zero_of_lt]
  · simp
  · omega

lemma coeff_oddBinomAuxReal_odd (n k : ℕ) :
    (oddBinomAuxReal n).coeff (2 * k + 1) = 0 := by
  simp [oddBinomAuxReal]
  apply Finset.sum_eq_zero
  intro x _hx
  have hne : 2 * k + 1 ≠ 2 * x := by omega
  simp [hne]

theorem oddBinomAuxReal_identity (n : ℕ) :
    (2 : ℝ[X]) * X * oddBinomAuxReal n =
      ((1 : ℝ[X]) + X) ^ n - ((1 : ℝ[X]) - X) ^ n := by
  classical
  ext m
  rw [coeff_sub]
  cases m with
  | zero =>
      -- Target:
      --   (2 * X * oddBinomAuxReal n).coeff 0
      --     = ((1 + X) ^ n).coeff 0 - ((1 - X) ^ n).coeff 0
      simp [Polynomial.coeff_zero_eq_eval_zero]
  | succ d =>
      rw [mul_assoc]
      change (C (2 : ℝ) * (X * oddBinomAuxReal n)).coeff (d + 1) = _
      rw [coeff_C_mul, coeff_X_mul]
      rw [Polynomial.coeff_one_add_X_pow]
      rw [coeff_one_sub_X_pow]
      -- Target:
      --   2 * (oddBinomAuxReal n).coeff d
      --     = ↑(n.choose (d + 1))
      --       - (-1) ^ (d + 1) * ↑(n.choose (d + 1))
      rcases Nat.even_or_odd d with hd | hd
      · rcases hd with ⟨k, hk⟩
        have hd2 : d = 2 * k := by omega
        rw [hd2, coeff_oddBinomAuxReal_even]
        have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
        rw [hodd.neg_one_pow]
        ring
      · rcases hd with ⟨k, hk⟩
        rw [hk, coeff_oddBinomAuxReal_odd]
        have heven : Even (2 * k + 1 + 1) := ⟨k + 1, by omega⟩
        rw [heven.neg_one_pow]
        ring

noncomputable def oddBinomAux (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range ((n + 1) / 2),
    C ((Nat.choose n (2 * k + 1) : ℂ)) * X ^ (2 * k)

noncomputable def oddBinomPoly (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range ((n + 1) / 2),
    C ((Nat.choose n (2 * k + 1) : ℂ)) * X ^ k

noncomputable def oddBinomPolyReal (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range ((n + 1) / 2),
    C ((Nat.choose n (2 * k + 1) : ℝ)) * X ^ k

noncomputable def tangentRoot (n j : ℕ) : ℝ :=
  - (Real.tan (Real.pi * (j : ℝ) / (n : ℝ))) ^ 2

lemma map_oddBinomAuxReal (n : ℕ) :
    (oddBinomAuxReal n).map (algebraMap ℝ ℂ) = oddBinomAux n := by
  rw [oddBinomAuxReal, oddBinomAux, Polynomial.map_sum]
  simp

theorem oddBinomAux_identity (n : ℕ) :
    (2 : ℂ[X]) * X * oddBinomAux n =
      ((1 : ℂ[X]) + X) ^ n - ((1 : ℂ[X]) - X) ^ n := by
  have h := congrArg (Polynomial.map (algebraMap ℝ ℂ))
    (oddBinomAuxReal_identity n)
  simpa [map_oddBinomAuxReal] using h

lemma map_oddBinomPolyReal (n : ℕ) :
    (oddBinomPolyReal n).map (algebraMap ℝ ℂ) = oddBinomPoly n := by
  rw [oddBinomPolyReal, oddBinomPoly, Polynomial.map_sum]
  simp

lemma coeff_oddBinomPolyReal (n k : ℕ) :
    (oddBinomPolyReal n).coeff k = (n.choose (2 * k + 1) : ℝ) := by
  simp [oddBinomPolyReal]
  intro h
  rw [Nat.choose_eq_zero_of_lt]
  · simp
  · omega

lemma oddBinomPolyReal_natDegree (n : ℕ) (hn : 0 < n) :
    (oddBinomPolyReal n).natDegree = (n - 1) / 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => by
      rw [coeff_oddBinomPolyReal]
      rw [Nat.choose_eq_zero_of_lt]
      · simp
      · omega)
  · rw [coeff_oddBinomPolyReal]
    exact_mod_cast Nat.choose_ne_zero (by omega :
      2 * ((n - 1) / 2) + 1 ≤ n)

lemma oddBinomPolyReal_ne_zero (n : ℕ) (hn : 0 < n) :
    oddBinomPolyReal n ≠ 0 := by
  intro hp
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff ((n - 1) / 2)) hp
  change (oddBinomPolyReal n).coeff ((n - 1) / 2) = 0 at hcoeff
  rw [coeff_oddBinomPolyReal] at hcoeff
  simp at hcoeff
  exact Nat.choose_ne_zero (by omega :
    2 * ((n - 1) / 2) + 1 ≤ n) (by exact_mod_cast hcoeff)

lemma oddBinom_eval_sq_eq_aux (n : ℕ) (y : ℂ) :
    (oddBinomPoly n).eval (y ^ 2) = (oddBinomAux n).eval y := by
  rw [oddBinomPoly, oddBinomAux,
    Polynomial.eval_finset_sum, Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  simp [pow_mul]

lemma oddBinom_eval_sq_identity (n : ℕ) (y : ℂ) :
    (2 : ℂ) * y * (oddBinomPoly n).eval (y ^ 2) =
      (1 + y) ^ n - (1 - y) ^ n := by
  have h := congrArg (fun p : ℂ[X] => p.eval y) (oddBinomAux_identity n)
  simpa [oddBinom_eval_sq_eq_aux] using h

lemma oddBinom_eval_sq_eq_zero_iff_pow_eq (n : ℕ) {y : ℂ} (hy : y ≠ 0) :
    (oddBinomPoly n).eval (y ^ 2) = 0 ↔ (1 + y) ^ n = (1 - y) ^ n := by
  constructor
  · intro hzero
    have hleft : (2 : ℂ) * y * (oddBinomPoly n).eval (y ^ 2) = 0 := by
      simp [hzero]
    rw [oddBinom_eval_sq_identity] at hleft
    exact sub_eq_zero.mp hleft
  · intro hpow
    have hleft : (2 : ℂ) * y * (oddBinomPoly n).eval (y ^ 2) = 0 := by
      rw [oddBinom_eval_sq_identity, hpow, sub_self]
    have hcoeff : (2 : ℂ) * y ≠ 0 := by
      exact mul_ne_zero (by norm_num) hy
    have hleft' : ((2 : ℂ) * y) * (oddBinomPoly n).eval (y ^ 2) = 0 := by
      simpa [mul_assoc] using hleft
    exact (mul_eq_zero.mp hleft').resolve_left hcoeff

lemma div_pow_eq_one_iff_pow_eq (n : ℕ) {a b : ℂ} (hb : b ≠ 0) :
    (a / b) ^ n = 1 ↔ a ^ n = b ^ n := by
  rw [div_pow]
  exact div_eq_one_iff_eq (pow_ne_zero n hb)

lemma oddBinom_root_sq_iff_cayley_pow_eq_one
    (n : ℕ) {y : ℂ} (hy0 : y ≠ 0) (hy1 : 1 - y ≠ 0) :
    (oddBinomPoly n).eval (y ^ 2) = 0 ↔ ((1 + y) / (1 - y)) ^ n = 1 := by
  rw [oddBinom_eval_sq_eq_zero_iff_pow_eq n hy0]
  exact (div_pow_eq_one_iff_pow_eq n hy1).symm

lemma angle_mem_Ioo_zero_pi_div_two (n j : ℕ) (hj0 : 0 < j) (hjn : 2 * j < n) :
    Real.pi * (j : ℝ) / (n : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  constructor
  · have hnpos_nat : 0 < n := by omega
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnpos_nat
    positivity
  · have hnpos_nat : 0 < n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnpos_nat
    have hratio : (j : ℝ) / (n : ℝ) < 1 / 2 := by
      rw [div_lt_iff₀ hnpos]
      norm_num
      have hjn_real : (2 * j : ℝ) < n := by exact_mod_cast hjn
      nlinarith
    have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
    calc
      Real.pi * (j : ℝ) / (n : ℝ) =
          Real.pi * ((j : ℝ) / (n : ℝ)) := by ring
      _ < Real.pi * (1 / 2 : ℝ) := mul_lt_mul_of_pos_left hratio hpi_pos
      _ = Real.pi / 2 := by ring

lemma exp_two_mul_arctan_mul_I (z : ℂ) (h₁ : 1 + z * Complex.I ≠ 0)
    (h₂ : 1 - z * Complex.I ≠ 0) :
    Complex.exp (2 * (Complex.arctan z * Complex.I)) =
      (1 + z * Complex.I) / (1 - z * Complex.I) := by
  rw [Complex.arctan, ← mul_rotate, ← mul_assoc,
    show 2 * (Complex.I * (-Complex.I / 2)) = 1 by simp [field], one_mul,
    Complex.exp_log]
  exact div_ne_zero h₁ h₂

lemma one_add_tan_mul_I_ne_zero (theta : ℝ) :
    1 + (Real.tan theta : ℂ) * Complex.I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre

lemma one_sub_tan_mul_I_ne_zero (theta : ℝ) :
    1 - (Real.tan theta : ℂ) * Complex.I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre

lemma cayley_I_tan_eq_exp_two_mul_I (theta : ℝ)
    (hθ0 : 0 < theta) (hθlt : theta < Real.pi / 2) :
    (1 + Complex.I * (Real.tan theta : ℂ)) /
        (1 - Complex.I * (Real.tan theta : ℂ)) =
      Complex.exp ((2 * theta : ℝ) * Complex.I) := by
  have hkey := exp_two_mul_arctan_mul_I (Real.tan theta : ℂ)
    (one_add_tan_mul_I_ne_zero theta) (one_sub_tan_mul_I_ne_zero theta)
  have harctan : Complex.arctan (Real.tan theta : ℂ) = (theta : ℂ) := by
    have h0 : (theta : ℂ) ≠ (Real.pi : ℂ) / 2 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have h1 : -(↑Real.pi / 2) < (theta : ℂ).re := by
      simp
      have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
      linarith
    have h2 : (theta : ℂ).re ≤ ↑Real.pi / 2 := by
      simp
      exact le_of_lt hθlt
    have h := Complex.arctan_tan h0 h1 h2
    simpa [Complex.ofReal_tan] using h
  rw [harctan] at hkey
  rw [show 2 * ((theta : ℂ) * Complex.I) =
      ((2 * theta : ℝ) : ℂ) * Complex.I by norm_num; ring] at hkey
  simpa [mul_comm, mul_left_comm, mul_assoc] using hkey.symm

lemma exp_two_pi_mul_nat_div_pow_eq_one (n j : ℕ) (hn : 0 < n) :
    (Complex.exp (((2 * (Real.pi * (j : ℝ) / (n : ℝ)) : ℝ) : ℂ) *
      Complex.I)) ^ n = 1 := by
  rw [← Complex.exp_nat_mul]
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have harg : (n : ℂ) *
      (((2 * (Real.pi * (j : ℝ) / (n : ℝ)) : ℝ) : ℂ) * Complex.I) =
      (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    norm_num
    field_simp [hnreal, hnC]
  rw [harg]
  exact Complex.exp_nat_mul_two_pi_mul_I j

lemma one_sub_I_mul_tan_ne_zero (theta : ℝ) :
    1 - Complex.I * (Real.tan theta : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre

lemma I_mul_tan_ne_zero {theta : ℝ} (hθ0 : 0 < theta) (hθlt : theta < Real.pi / 2) :
    Complex.I * (Real.tan theta : ℂ) ≠ 0 := by
  have htan_pos : 0 < Real.tan theta :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθlt
  exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (ne_of_gt htan_pos))

lemma oddBinom_tangent_eval_eq_zero (n j : ℕ) (hj0 : 0 < j) (hjn : 2 * j < n) :
    (oddBinomPoly n).eval
      (-((Real.tan (Real.pi * (j : ℝ) / (n : ℝ)) : ℂ) ^ 2)) = 0 := by
  let theta : ℝ := Real.pi * (j : ℝ) / (n : ℝ)
  let y : ℂ := Complex.I * (Real.tan theta : ℂ)
  have htheta := angle_mem_Ioo_zero_pi_div_two n j hj0 hjn
  have hnpos : 0 < n := by omega
  have hy0 : y ≠ 0 := I_mul_tan_ne_zero htheta.1 htheta.2
  have hy1 : 1 - y ≠ 0 := one_sub_I_mul_tan_ne_zero theta
  have hpow : ((1 + y) / (1 - y)) ^ n = 1 := by
    have hcayley := cayley_I_tan_eq_exp_two_mul_I theta htheta.1 htheta.2
    have hexp := exp_two_pi_mul_nat_div_pow_eq_one n j hnpos
    change ((1 + Complex.I * (Real.tan theta : ℂ)) /
      (1 - Complex.I * (Real.tan theta : ℂ))) ^ n = 1
    rw [hcayley]
    simpa [theta] using hexp
  have hroot : (oddBinomPoly n).eval (y ^ 2) = 0 :=
    (oddBinom_root_sq_iff_cayley_pow_eq_one n hy0 hy1).mpr hpow
  have hy_sq : y ^ 2 = -((Real.tan theta : ℂ) ^ 2) := by
    change (Complex.I * (Real.tan theta : ℂ)) ^ 2 =
      -((Real.tan theta : ℂ) ^ 2)
    rw [show (Complex.I * (Real.tan theta : ℂ)) ^ 2 =
        Complex.I ^ 2 * (Real.tan theta : ℂ) ^ 2 by ring]
    rw [show Complex.I ^ 2 = (-1 : ℂ) by simp [pow_two, Complex.I_mul_I]]
    ring
  rw [hy_sq] at hroot
  simpa [theta] using hroot

lemma two_mul_lt_of_pos_le_pred_div_two {n j : ℕ} (hj0 : 0 < j)
    (hjle : j ≤ (n - 1) / 2) :
    2 * j < n := by
  omega

lemma oddBinom_tangent_eval_eq_zero_of_le_pred_div_two
    (n j : ℕ) (hj0 : 0 < j) (hjle : j ≤ (n - 1) / 2) :
    (oddBinomPoly n).eval
      (-((Real.tan (Real.pi * (j : ℝ) / (n : ℝ)) : ℂ) ^ 2)) = 0 :=
  oddBinom_tangent_eval_eq_zero n j hj0
    (two_mul_lt_of_pos_le_pred_div_two hj0 hjle)

lemma oddBinom_tangentRoot_eval_eq_zero
    (n j : ℕ) (hj0 : 0 < j) (hjle : j ≤ (n - 1) / 2) :
    (oddBinomPoly n).eval (tangentRoot n j : ℂ) = 0 := by
  simpa [tangentRoot] using
    oddBinom_tangent_eval_eq_zero_of_le_pred_div_two n j hj0 hjle

lemma tangentRoot_neg (n j : ℕ) (hj0 : 0 < j) (hjn : 2 * j < n) :
    tangentRoot n j < 0 := by
  have htheta := angle_mem_Ioo_zero_pi_div_two n j hj0 hjn
  have htan_pos : 0 < Real.tan (Real.pi * (j : ℝ) / (n : ℝ)) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two htheta.1 htheta.2
  rw [tangentRoot]
  exact neg_neg_of_pos (sq_pos_of_pos htan_pos)

lemma tangentRoot_strictAnti {n i j : ℕ} (hi0 : 0 < i) (hij : i < j)
    (hjn : 2 * j < n) :
    tangentRoot n j < tangentRoot n i := by
  have hijn : 2 * i < n := by omega
  have hj0 : 0 < j := by omega
  have hthetai := angle_mem_Ioo_zero_pi_div_two n i hi0 hijn
  have hthetaj := angle_mem_Ioo_zero_pi_div_two n j hj0 hjn
  have hnpos_nat : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnpos_nat
  have hijR : (i : ℝ) < j := by exact_mod_cast hij
  have hratio : (i : ℝ) / (n : ℝ) < (j : ℝ) / (n : ℝ) :=
    div_lt_div_of_pos_right hijR hnpos
  have htheta_lt :
      Real.pi * (i : ℝ) / (n : ℝ) < Real.pi * (j : ℝ) / (n : ℝ) := by
    calc
      Real.pi * (i : ℝ) / (n : ℝ) =
          Real.pi * ((i : ℝ) / (n : ℝ)) := by ring
      _ < Real.pi * ((j : ℝ) / (n : ℝ)) :=
          mul_lt_mul_of_pos_left hratio Real.pi_pos
      _ = Real.pi * (j : ℝ) / (n : ℝ) := by ring
  have htan_lt :
      Real.tan (Real.pi * (i : ℝ) / (n : ℝ)) <
        Real.tan (Real.pi * (j : ℝ) / (n : ℝ)) :=
    Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two
      (le_of_lt hthetai.1) hthetaj.2 htheta_lt
  have htan_i_nonneg : 0 ≤ Real.tan (Real.pi * (i : ℝ) / (n : ℝ)) :=
    le_of_lt (Real.tan_pos_of_pos_of_lt_pi_div_two hthetai.1 hthetai.2)
  have hsquare :
      (Real.tan (Real.pi * (i : ℝ) / (n : ℝ))) ^ 2 <
        (Real.tan (Real.pi * (j : ℝ) / (n : ℝ))) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_lt_mul_self htan_i_nonneg htan_lt
  rw [tangentRoot]
  exact neg_lt_neg hsquare

lemma oddBinomPolyReal_tangentRoot_eval_eq_zero
    (n j : ℕ) (hj0 : 0 < j) (hjle : j ≤ (n - 1) / 2) :
    (oddBinomPolyReal n).eval (tangentRoot n j) = 0 := by
  have hc : (oddBinomPoly n).eval (tangentRoot n j : ℂ) = 0 :=
    oddBinom_tangentRoot_eval_eq_zero n j hj0 hjle
  have hmap :
      ((oddBinomPolyReal n).map (algebraMap ℝ ℂ)).eval (tangentRoot n j : ℂ) = 0 := by
    simpa [map_oddBinomPolyReal] using hc
  have hcast :
      algebraMap ℝ ℂ ((oddBinomPolyReal n).eval (tangentRoot n j)) = 0 := by
    change ((oddBinomPolyReal n).map (algebraMap ℝ ℂ)).eval
      ((algebraMap ℝ ℂ) (tangentRoot n j)) = 0 at hmap
    rw [Polynomial.eval_map_apply] at hmap
    exact hmap
  exact Complex.ofReal_eq_zero.mp hcast

noncomputable def tangentRootFinset (n : ℕ) : Finset ℝ :=
  (Finset.Icc 1 ((n - 1) / 2)).image (tangentRoot n)

lemma tangentRoot_injOn_Icc (n : ℕ) :
    Set.InjOn (tangentRoot n) (↑(Finset.Icc 1 ((n - 1) / 2)) : Set ℕ) := by
  intro i hi j hj hroot
  rw [Finset.mem_coe, Finset.mem_Icc] at hi hj
  by_cases hij : i < j
  · have hlt := tangentRoot_strictAnti (by omega : 0 < i) hij
      (two_mul_lt_of_pos_le_pred_div_two (by omega : 0 < j) (by omega : j ≤ (n - 1) / 2))
    rw [hroot] at hlt
    linarith
  · by_cases hji : j < i
    · have hlt := tangentRoot_strictAnti (by omega : 0 < j) hji
        (two_mul_lt_of_pos_le_pred_div_two (by omega : 0 < i)
          (by omega : i ≤ (n - 1) / 2))
      rw [hroot] at hlt
      linarith
    · omega

lemma tangentRootFinset_card (n : ℕ) :
    (tangentRootFinset n).card = (n - 1) / 2 := by
  rw [tangentRootFinset, Finset.card_image_of_injOn (tangentRoot_injOn_Icc n)]
  simp

lemma oddBinomPolyReal_eval_eq_zero_of_mem_tangentRootFinset (n : ℕ) :
    ∀ x ∈ tangentRootFinset n, (oddBinomPolyReal n).eval x = 0 := by
  intro x hx
  rw [tangentRootFinset] at hx
  rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
  rw [Finset.mem_Icc] at hj
  exact oddBinomPolyReal_tangentRoot_eval_eq_zero n j (by omega) (by omega)

lemma oddBinomPolyReal_roots_eq_tangentRootFinset (n : ℕ) (hn : 0 < n) :
    (oddBinomPolyReal n).roots = (tangentRootFinset n).val := by
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · exact oddBinomPolyReal_eval_eq_zero_of_mem_tangentRootFinset n
  · rw [oddBinomPolyReal_natDegree n hn, tangentRootFinset_card n]
  · exact oddBinomPolyReal_ne_zero n hn

theorem oddBinomPolyReal_isRealRooted (n : ℕ) (hn : 0 < n) :
    (oddBinomPolyReal n) ≠ 0 ∧ (oddBinomPolyReal n).Splits := by
  refine ⟨oddBinomPolyReal_ne_zero n hn, ?_⟩
  rw [Polynomial.splits_iff_card_roots, oddBinomPolyReal_roots_eq_tangentRootFinset n hn]
  simp [tangentRootFinset_card n, oddBinomPolyReal_natDegree n hn]

end BigDescents
