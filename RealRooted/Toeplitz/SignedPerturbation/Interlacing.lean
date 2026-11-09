module

public import RealRooted.Basic.ProperPosition
public import RealRooted.SimpleRoots
public import RealRooted.Toeplitz.SignedPerturbation.Curve
public import RealRooted.Toeplitz.SignedPerturbation.Factorization
public import RealRooted.Toeplitz.SignedPerturbation.Rows
import RealRooted.Toeplitz.SignedPerturbation.AlternatingRoots
import RealRooted.Toeplitz.SignedPerturbation.Chebyshev
import RealRooted.Toeplitz.SignedPerturbation.CofactorBounds

/-!
# Interlacing of the signed Toeplitz perturbation rows

Let `A(R) ≤ R² - 1` and `B(R) ≤ 1`.  At every `θ ∈ (0, π)` the rescaled denominator factors as
`(1 - 2 cos θ z + z²) · C_θ(z)` with `‖C_θ - 1‖₁ ≤ 1/2`, so the rescaled rows are
`∑ g_k(θ) U_{n-k}(cos θ)` with `∑_{k=1}^n |g_k| ≤ 1 - 2⁻ⁿ`.  At the grid angles
`(2 j + 1) π / (2 (n + 1))` the row `P_n(λ(θ))` alternates in sign, which with the strictly
decreasing `λ` of `Curve` gives `n` simple real roots, and at those roots `P_{n-1}` alternates
as well.
-/

@[expose] public section

open Polynomial Filter Topology

noncomputable section


namespace RealRooted.ToeplitzPerturbation

section Core

variable {s : ℕ} {c : ℕ → ℝ} {R : ℝ}

/-- `λ(θ) = Re b(ρ(θ) e^{iθ})`. -/
abbrev lam (s : ℕ) (c : ℕ → ℝ) (R θ : ℝ) : ℝ := reB s c θ (rho s c R θ)

/-- The `k`th coefficient of the reciprocal of the cofactor at `(ρ(θ), cos θ)`. -/
abbrev invCoeff (s : ℕ) (c : ℕ → ℝ) (R θ : ℝ) (k : ℕ) : ℝ :=
  cofactorInvCoeff s c (rho s c R θ) (Real.cos θ) k

theorem perturbationB_mono {ρ : ℝ} (h : 0 ≤ ρ) (hρR : ρ ≤ R) :
    perturbationB s c ρ ≤ perturbationB s c R := by
  unfold perturbationB
  refine Finset.sum_le_sum fun j hj => ?_
  have : (0 : ℝ) ≤ j * (j - 1) * |c j| := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast (by have := (Finset.mem_Icc.mp hj).1; lia : 1 ≤ j)
    have := abs_nonneg (c j)
    positivity
  gcongr

theorem sin_mul_row_eval {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) (hR : 0 ≤ R)
    (hA : perturbationA s c R ≤ R ^ 2 - 1) (m : ℕ) :
    Real.sin θ * (rho s c R θ ^ m * (row s c m).eval (lam s c R θ)) =
      ∑ k ∈ Finset.range (m + 1), invCoeff s c R θ k * Real.sin (((m : ℝ) + 1 - k) * θ) := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  obtain ⟨hρ0, hρR, hphi⟩ := rho_spec (s := s) (c := c) (θ := θ) hR hA
  have h2 := reB_mul_eq (s := s) (c := c) θ _ hρ0.ne' hsin.ne' hphi
  rw [row_eval_eq_sum s c (rho s c R θ) (Real.cos θ) (lam s c R θ) hphi h2 m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hk
  rw [mul_left_comm, mul_comm (Real.sin θ), chebU_mul_sin, Nat.cast_sub hk']
  congr 2
  ring

theorem invCoeff_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) (hR : 0 ≤ R)
    (hA : perturbationA s c R ≤ R ^ 2 - 1) : invCoeff s c R θ 0 = 1 := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  obtain ⟨hρ0, hρR, hphi⟩ := rho_spec (s := s) (c := c) (θ := θ) hR hA
  have h0 := coeff_zero_cofactor s c (rho s c R θ) (Real.cos θ) hphi
  have h0' : PowerSeries.constantCoeff (cofactor s c (rho s c R θ) (Real.cos θ) :
      PowerSeries ℝ) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, h0]
  unfold invCoeff cofactorInvCoeff
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv, h0', inv_one]

theorem sum_abs_invCoeff_le {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) (hR : 0 ≤ R)
    (hA : perturbationA s c R ≤ R ^ 2 - 1) (hB : perturbationB s c R ≤ 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), |invCoeff s c R θ k| ≤ 2 - (1 / 2) ^ n := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  obtain ⟨hρ0, hρR, hphi⟩ := rho_spec (s := s) (c := c) (θ := θ) hR hA
  have hB' : perturbationB s c (rho s c R θ) ≤ 1 :=
    (perturbationB_mono hρ0.le hρR).trans hB
  have h0 := coeff_zero_cofactor s c (rho s c R θ) (Real.cos θ) hphi
  have h0' : PowerSeries.constantCoeff (cofactor s c (rho s c R θ) (Real.cos θ) :
      PowerSeries ℝ) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, h0]
  have hH : ∀ N, ∑ ℓ ∈ Finset.range N, |PowerSeries.coeff (ℓ + 1)
      (cofactor s c (rho s c R θ) (Real.cos θ) : PowerSeries ℝ)| ≤ 1 / 2 := fun N => by
    simpa only [Polynomial.coeff_coe] using
      sum_abs_coeff_cofactor_le s c (rho s c R θ) (Real.cos θ) hρ0.le
        (abs_chebU_le (Real.abs_cos_le_one θ)) hB' N
  exact sum_abs_coeff_inv_le h0' hH n

theorem half_pow_le_sum_cos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) (hR : 0 ≤ R)
    (hA : perturbationA s c R ≤ R ^ 2 - 1) (hB : perturbationB s c R ≤ 1) (n : ℕ) (φ : ℝ) :
    (1 / 2) ^ n ≤ ∑ k ∈ Finset.range (n + 1), invCoeff s c R θ k * Real.cos (k * φ) := by
  have h := sum_abs_invCoeff_le hθ hR hA hB n
  rw [Finset.sum_range_succ', invCoeff_zero hθ hR hA, abs_one] at h
  rw [Finset.sum_range_succ', invCoeff_zero hθ hR hA]
  have : -∑ k ∈ Finset.range n, |invCoeff s c R θ (k + 1)| ≤
      ∑ k ∈ Finset.range n, invCoeff s c R θ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * φ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 := abs_le.mp (Real.abs_cos_le_one (((k + 1 : ℕ) : ℝ) * φ))
    have h2 : |invCoeff s c R θ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * φ)| ≤
        |invCoeff s c R θ (k + 1)| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    exact (neg_le_neg h2).trans (neg_abs_le _)
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
  linarith

end Core

section Trig

variable (g : ℕ → ℝ) (θ : ℝ) (m : ℕ)

theorem sum_sin_eq : ∑ k ∈ Finset.range (m + 2), g k * Real.sin (((m : ℝ) + 2 - k) * θ) =
    Real.sin (((m : ℝ) + 2) * θ) * ∑ k ∈ Finset.range (m + 2), g k * Real.cos (k * θ) -
      Real.cos (((m : ℝ) + 2) * θ) * ∑ k ∈ Finset.range (m + 2), g k * Real.sin (k * θ) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sub_mul, Real.sin_sub]; ring

theorem sum_cos_eq : ∑ k ∈ Finset.range (m + 2), g k * Real.cos (((m : ℝ) + 2 - k) * θ) =
    Real.cos (((m : ℝ) + 2) * θ) * ∑ k ∈ Finset.range (m + 2), g k * Real.cos (k * θ) +
      Real.sin (((m : ℝ) + 2) * θ) * ∑ k ∈ Finset.range (m + 2), g k * Real.sin (k * θ) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sub_mul, Real.cos_sub]; ring

theorem sum_sin_lower : ∑ k ∈ Finset.range (m + 1), g k * Real.sin (((m : ℝ) + 1 - k) * θ) =
    Real.cos θ * ∑ k ∈ Finset.range (m + 2), g k * Real.sin (((m : ℝ) + 2 - k) * θ) -
      Real.sin θ * ∑ k ∈ Finset.range (m + 2), g k * Real.cos (((m : ℝ) + 2 - k) * θ) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_range_succ _ (m + 1)]
  have e : ((m : ℝ) + 2 - ((m + 1 : ℕ) : ℝ)) = 1 := by push_cast; ring
  have : Real.cos θ * (g (m + 1) * Real.sin (((m : ℝ) + 2 - ((m + 1 : ℕ) : ℝ)) * θ)) -
      Real.sin θ * (g (m + 1) * Real.cos (((m : ℝ) + 2 - ((m + 1 : ℕ) : ℝ)) * θ)) = 0 := by
    rw [e, one_mul]; ring
  rw [this, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : ((m : ℝ) + 1 - k) * θ = ((m : ℝ) + 2 - k) * θ - θ := by ring
  rw [this, Real.sin_sub]; ring

end Trig

section Signs

variable {s : ℕ} {c : ℕ → ℝ} {R : ℝ}

/-- The grid angles `(2 j + 1) π / (2 (m + 2))`, `0 ≤ j ≤ m + 1`. -/
def gridAngle (m j : ℕ) : ℝ := (2 * j + 1) * Real.pi / (2 * (m + 2))

theorem gridAngle_mem {m j : ℕ} (hj : j ≤ m + 1) : gridAngle m j ∈ Set.Ioo 0 Real.pi := by
  have hm : (0 : ℝ) < 2 * (m + 2) := by positivity
  have hj' : (j : ℝ) ≤ m + 1 := by exact_mod_cast hj
  constructor
  · unfold gridAngle; positivity
  · unfold gridAngle
    rw [div_lt_iff₀ hm]
    nlinarith [Real.pi_pos]

theorem mul_gridAngle (m j : ℕ) : ((m : ℝ) + 2) * gridAngle m j = j * Real.pi + Real.pi / 2 := by
  unfold gridAngle
  field_simp

theorem sin_nat_mul_pi_add_half (j : ℕ) : Real.sin (j * Real.pi + Real.pi / 2) = (-1) ^ j := by
  rw [Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]

theorem cos_nat_mul_pi_add_half (j : ℕ) : Real.cos (j * Real.pi + Real.pi / 2) = 0 := by
  rw [Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]

theorem grid_sign (hR : 0 ≤ R) (hA : perturbationA s c R ≤ R ^ 2 - 1)
    (hB : perturbationB s c R ≤ 1) (m j : ℕ) (hj : j ≤ m + 1) :
    0 < (-1 : ℝ) ^ j * (row s c (m + 1)).eval (lam s c R (gridAngle m j)) := by
  have hθ := gridAngle_mem (m := m) hj
  have hsin : 0 < Real.sin (gridAngle m j) := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  obtain ⟨hρ0, hρR, hphi⟩ := rho_spec (s := s) (c := c) (θ := gridAngle m j) hR hA
  have h := sin_mul_row_eval hθ hR hA (m + 1)
  have e : ∀ k : ℕ, (((m + 1 : ℕ) : ℝ) + 1 - k) = (m : ℝ) + 2 - k := fun k => by
    push_cast; ring
  simp only [e] at h
  rw [sum_sin_eq, mul_gridAngle, sin_nat_mul_pi_add_half, cos_nat_mul_pi_add_half, zero_mul,
    sub_zero] at h
  have hRr := half_pow_le_sum_cos hθ hR hA hB (m + 1) (gridAngle m j)
  have hpos : 0 < Real.sin (gridAngle m j) * rho s c R (gridAngle m j) ^ (m + 1) :=
    mul_pos hsin (pow_pos hρ0 _)
  have h2 : Real.sin (gridAngle m j) * rho s c R (gridAngle m j) ^ (m + 1) *
      ((-1 : ℝ) ^ j * (row s c (m + 1)).eval (lam s c R (gridAngle m j))) =
      ∑ k ∈ Finset.range (m + 2), invCoeff s c R (gridAngle m j) k *
        Real.cos (k * gridAngle m j) := by
    have hsq : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; simp
    calc _ = (-1 : ℝ) ^ j * (Real.sin (gridAngle m j) * (rho s c R (gridAngle m j) ^ (m + 1) *
          (row s c (m + 1)).eval (lam s c R (gridAngle m j)))) := by ring
      _ = _ := by rw [h]; linear_combination (∑ k ∈ Finset.range (m + 2),
          invCoeff s c R (gridAngle m j) k * Real.cos (k * gridAngle m j)) * hsq
  refine (mul_pos_iff_of_pos_left hpos).mp ?_
  rw [h2]
  exact lt_of_lt_of_le (by positivity) hRr

theorem neg_one_pow_mul_cos_pos {x : ℝ} (j : ℕ) (hlo : (j : ℝ) * Real.pi - Real.pi / 2 < x)
    (hhi : x < j * Real.pi + Real.pi / 2) : 0 < (-1 : ℝ) ^ j * Real.cos x := by
  have h : x = (x - j * Real.pi) + j * Real.pi := by ring
  have hy := Real.cos_pos_of_mem_Ioo (x := x - j * Real.pi) ⟨by linarith, by linarith⟩
  have hsq : (-1 : ℝ) ^ j * (-1) ^ j = 1 := by rw [← mul_pow]; simp
  rw [h, Real.cos_add_nat_mul_pi, ← mul_assoc, hsq, one_mul]
  exact hy

theorem sign_lower_at_root (hR : 0 ≤ R) (hA : perturbationA s c R ≤ R ^ 2 - 1)
    (hB : perturbationB s c R ≤ 1) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) (m j : ℕ)
    (hroot : (row s c (m + 1)).eval (lam s c R θ) = 0)
    (hlo : (j : ℝ) * Real.pi - Real.pi / 2 < ((m : ℝ) + 2) * θ)
    (hhi : ((m : ℝ) + 2) * θ < j * Real.pi + Real.pi / 2) :
    (-1 : ℝ) ^ j * (row s c m).eval (lam s c R θ) < 0 := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  obtain ⟨hρ0, hρR, hphi⟩ := rho_spec (s := s) (c := c) (θ := θ) hR hA
  have h1 := sin_mul_row_eval hθ hR hA (m + 1)
  have e : ∀ k : ℕ, (((m + 1 : ℕ) : ℝ) + 1 - k) = (m : ℝ) + 2 - k := fun k => by
    push_cast; ring
  simp only [e, hroot, mul_zero] at h1
  have h0 := sum_sin_eq (invCoeff s c R θ) θ m
  rw [← h1] at h0
  have h2 := sin_mul_row_eval hθ hR hA m
  rw [sum_sin_lower, ← h1, mul_zero, zero_sub] at h2
  have hRr : (1 / 2 : ℝ) ^ (m + 1) ≤
      ∑ k ∈ Finset.range (m + 2), invCoeff s c R θ k * Real.cos (k * θ) :=
    half_pow_le_sum_cos hθ hR hA hB (m + 1) θ
  have hZ := sum_cos_eq (invCoeff s c R θ) θ m
  generalize ∑ k ∈ Finset.range (m + 2), invCoeff s c R θ k * Real.cos (k * θ) = Rr at h0 hRr hZ
  generalize ∑ k ∈ Finset.range (m + 2), invCoeff s c R θ k * Real.sin (k * θ) = Ri at h0 hZ
  generalize ∑ k ∈ Finset.range (m + 2),
    invCoeff s c R θ k * Real.cos (((m : ℝ) + 2 - k) * θ) = Z at h2 hZ
  generalize hadef : ((m : ℝ) + 2) * θ = a at h0 hZ hlo hhi
  have hZc : Z * Real.cos a = Rr := by
    rw [hZ]
    linear_combination (-Real.sin a) * h0.symm + Rr * Real.sin_sq_add_cos_sq a
  have hcos := neg_one_pow_mul_cos_pos j hlo hhi
  have hsq : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; simp
  have hRr0 : 0 < Rr := lt_of_lt_of_le (by positivity) hRr
  have hZ' : 0 < (-1 : ℝ) ^ j * Z := by
    have : ((-1 : ℝ) ^ j * Z) * ((-1 : ℝ) ^ j * Real.cos a) = Rr := by
      calc _ = ((-1 : ℝ) ^ j * (-1) ^ j) * (Z * Real.cos a) := by ring
        _ = Rr := by rw [hsq, hZc, one_mul]
    exact (mul_pos_iff_of_pos_right hcos).mp (this ▸ hRr0)
  have h3 : (Real.sin θ * rho s c R θ ^ m) *
      ((-1 : ℝ) ^ j * (row s c m).eval (lam s c R θ)) =
      -(Real.sin θ * ((-1 : ℝ) ^ j * Z)) := by
    linear_combination (-1 : ℝ) ^ j * h2
  have hlt : (Real.sin θ * rho s c R θ ^ m) *
      ((-1 : ℝ) ^ j * (row s c m).eval (lam s c R θ)) < 0 := by
    rw [h3]; exact neg_neg_of_pos (mul_pos hsin hZ')
  by_contra h
  push Not at h
  exact absurd (mul_nonneg (mul_pos hsin (pow_pos hρ0 m)).le h) (not_le.mpr hlt)

end Signs



section Assembly

variable {s : ℕ} {c : ℕ → ℝ} {R : ℝ}

private theorem exists_zero_Ioo_of_mul_neg {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (h : f a * f b < 0) : ∃ x ∈ Set.Ioo a b, f x = 0 := by
  rcases mul_neg_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact intermediate_value_Ioo' hab hf ⟨h2, h1⟩ |>.imp fun x hx => ⟨hx.1, hx.2⟩
  · exact intermediate_value_Ioo hab hf ⟨h1, h2⟩ |>.imp fun x hx => ⟨hx.1, hx.2⟩

theorem gridAngle_lt {m i j : ℕ} (h : i < j) : gridAngle m i < gridAngle m j := by
  unfold gridAngle
  have hm : (0 : ℝ) < 2 * (m + 2) := by positivity
  have : (i : ℝ) < j := by exact_mod_cast h
  gcongr

theorem gridAngle_le {m i j : ℕ} (h : i ≤ j) : gridAngle m i ≤ gridAngle m j := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact (gridAngle_lt h).le

theorem exists_roots_between (hR : 0 < R) (hA : perturbationA s c R ≤ R ^ 2 - 1)
    (hB : perturbationB s c R ≤ 1) (m j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ m + 1) :
    ∃ t ∈ Set.Ioo (gridAngle m (j - 1)) (gridAngle m j),
      (row s c (m + 1)).eval (lam s c R t) = 0 := by
  have hsub : Set.Icc (gridAngle m (j - 1)) (gridAngle m j) ⊆ Set.Ioo 0 Real.pi :=
    fun x hx => ⟨lt_of_lt_of_le (gridAngle_mem (m := m) (by lia)).1 hx.1,
      lt_of_le_of_lt hx.2 (gridAngle_mem (m := m) hj).2⟩
  have hcont : ContinuousOn (fun θ => (row s c (m + 1)).eval (lam s c R θ))
      (Set.Icc (gridAngle m (j - 1)) (gridAngle m j)) :=
    (row s c (m + 1)).continuous.comp_continuousOn
      ((continuousOn_reB_rho (s := s) (c := c) (R := R) hR hA hB).mono hsub)
  refine exists_zero_Ioo_of_mul_neg (gridAngle_lt (by lia : j - 1 < j)).le hcont ?_
  have h1 := grid_sign hR.le hA hB m (j - 1) (by lia)
  have h2 := grid_sign hR.le hA hB m j hj
  have hj' : (-1 : ℝ) ^ (j - 1) * (-1) ^ j = -1 := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by lia⟩
    rw [Nat.add_sub_cancel, pow_succ, ← mul_assoc, ← mul_pow]; simp
  have h3 := mul_pos h1 h2
  have e : ((-1 : ℝ) ^ (j - 1) * (row s c (m + 1)).eval (lam s c R (gridAngle m (j - 1)))) *
      ((-1 : ℝ) ^ j * (row s c (m + 1)).eval (lam s c R (gridAngle m j))) =
      -((row s c (m + 1)).eval (lam s c R (gridAngle m (j - 1))) *
        (row s c (m + 1)).eval (lam s c R (gridAngle m j))) := by
    linear_combination ((row s c (m + 1)).eval (lam s c R (gridAngle m (j - 1))) *
        (row s c (m + 1)).eval (lam s c R (gridAngle m j))) * hj'
  rw [e] at h3
  linarith

theorem row_succ_splits_strictInterl (hR : 0 < R) (hA : perturbationA s c R ≤ R ^ 2 - 1)
    (hB : perturbationB s c R ≤ 1) (m : ℕ) :
    (row s c (m + 1)).Splits ∧ HasSimpleRoots (row s c (m + 1)) ∧
      StrictInterl (row s c m) (row s c (m + 1)) ∧
      ∀ x, (row s c (m + 1)).IsRoot x → (row s c m).eval x ≠ 0 := by
  have hex : ∀ j : ℕ, ∃ t : ℝ, 1 ≤ j → j ≤ m + 1 →
      t ∈ Set.Ioo (gridAngle m (j - 1)) (gridAngle m j) ∧
        (row s c (m + 1)).eval (lam s c R t) = 0 := fun j => by
    by_cases h : 1 ≤ j ∧ j ≤ m + 1
    · obtain ⟨t, ht, hr⟩ := exists_roots_between hR hA hB m j h.1 h.2
      exact ⟨t, fun _ _ => ⟨ht, hr⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose t ht using hex
  have hmem : ∀ j, 1 ≤ j → j ≤ m + 1 → t j ∈ Set.Ioo 0 Real.pi := fun j h1 h2 =>
    ⟨lt_trans (gridAngle_mem (m := m) (by lia : j - 1 ≤ m + 1)).1 (ht j h1 h2).1.1,
      lt_trans (ht j h1 h2).1.2 (gridAngle_mem (m := m) h2).2⟩
  have hlow : ∀ j, 1 ≤ j → j ≤ m + 1 →
      (-1 : ℝ) ^ j * (row s c m).eval (lam s c R (t j)) < 0 := by
    intro j h1 h2
    have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    refine sign_lower_at_root hR.le hA hB (hmem j h1 h2) m j (ht j h1 h2).2 ?_ ?_
    · have := mul_lt_mul_of_pos_left (ht j h1 h2).1.1 hm2
      rw [mul_gridAngle, Nat.cast_sub h1] at this
      push_cast at this
      linarith
    · have := mul_lt_mul_of_pos_left (ht j h1 h2).1.2 hm2
      rwa [mul_gridAngle] at this
  have hanti : ∀ i j, 1 ≤ i → i < j → j ≤ m + 1 →
      lam s c R (t j) < lam s c R (t i) := by
    intro i j hi hij hj
    refine strictAntiOn_reB_rho hR hA hB (hmem i hi (by lia)) (hmem j (by lia) hj) ?_
    calc t i < gridAngle m i := (ht i hi (by lia)).1.2
      _ ≤ gridAngle m (j - 1) := gridAngle_le (by lia)
      _ < t j := (ht j (by lia) hj).1.1
  have hFdeg : (row s c m).natDegree < m + 1 := by
    rw [(isMonicOfDegree_row s c m).natDegree_eq]; lia
  refine splits_and_strictInterl_of_alternating (isMonicOfDegree_row s c (m + 1)) hFdeg
    (isMonicOfDegree_row s c m).ne_zero (fun j => lam s c R (t j)) hanti
    (fun j h1 h2 => (ht j h1 h2).2) ?_ ?_
  · intro j h1 h2
    have e1 := hlow j h1 (by lia)
    have e2 := hlow (j + 1) (by lia) h2
    have hj : (-1 : ℝ) ^ j * (-1) ^ (j + 1) = -1 := by
      rw [pow_succ, ← mul_assoc, ← mul_pow]; simp
    have h3 := mul_pos_of_neg_of_neg e1 e2
    have e : ((-1 : ℝ) ^ j * (row s c m).eval (lam s c R (t j))) *
        ((-1 : ℝ) ^ (j + 1) * (row s c m).eval (lam s c R (t (j + 1)))) =
        -((row s c m).eval (lam s c R (t j)) * (row s c m).eval (lam s c R (t (j + 1)))) := by
      linear_combination ((row s c m).eval (lam s c R (t j)) *
        (row s c m).eval (lam s c R (t (j + 1)))) * hj
    rw [e] at h3
    linarith
  · intro j h1 h2 h0
    have := hlow j h1 h2
    rw [h0, mul_zero] at this
    exact lt_irrefl _ this

end Assembly

end RealRooted.ToeplitzPerturbation
