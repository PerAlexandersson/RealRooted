module

public import RealRooted.Toeplitz.SignedPerturbation.Chebyshev
public import RealRooted.Toeplitz.SignedPerturbation.Rows
public import RealRooted.Toeplitz.SignedPerturbation.TrigFamily
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The real parametrization of the signed Toeplitz perturbation

Write `b(z) = z⁻¹ + z + ∑_{j=2}^s c_j z^j` and `Φ(θ, ρ) = ρ² - 1 + ∑ c_j ρ^(j+1) U_{j-1}(cos θ)`,
so that `Im b(ρ e^{iθ}) = sin θ Φ(θ, ρ) / ρ`.  Assume `A(R) ≤ R² - 1` and `B(R) ≤ 1`.  For every
`θ ∈ (0, π)` there is a unique root `ρ(θ) ∈ (0, R]` of `Φ(θ, ·)`, and
`λ(θ) = Re b(ρ(θ) e^{iθ})` is a continuous, strictly decreasing function on `(0, π)`
(`strictAntiOn_reB_rho`).  The monotonicity is the computation `λ' = -ρ (a² + b₁²) / b₁ < 0`
with `b₁ = Im ∂_ρ b > 0`, using the implicit function theorem for `ρ(θ)`.
-/

@[expose] public section

open Polynomial Filter Topology

noncomputable section


namespace RealRooted.ToeplitzPerturbation

section Curve

variable (s : ℕ) (c : ℕ → ℝ)

/-- `Φ(θ, ρ) = ρ² - 1 + ∑ c_j ρ^(j+1) U_{j-1}(cos θ)`. -/
def phi (θ ρ : ℝ) : ℝ :=
  ρ ^ 2 - 1 + ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebUPred (Real.cos θ) j

/-- `∂Φ/∂ρ`. -/
def phiρ (θ ρ : ℝ) : ℝ :=
  2 * ρ + ∑ j ∈ Finset.Icc 2 s, c j * ((j + 1) * ρ ^ j) * chebUPred (Real.cos θ) j

/-- `Im (ρ b(ρ e^{iθ})) / ρ`. -/
abbrev imB (θ ρ : ℝ) : ℝ := trigFamily s c (-1) Real.sin θ ρ

/-- `Re b(ρ e^{iθ})`. -/
abbrev reB (θ ρ : ℝ) : ℝ := trigFamily s c 1 Real.cos θ ρ

/-- `W(ρ) = ∑ (j+1) j |c_j| ρ^(j-1)`: `ρ (2 - W ρ)` bounds `Φ_ρ` from below. -/
def phiW (ρ : ℝ) : ℝ := ∑ j ∈ Finset.Icc 2 s, ((j : ℝ) + 1) * j * |c j| * ρ ^ (j - 1)

variable {s c}

theorem mul_imB_eq (θ ρ : ℝ) (hρ : ρ ≠ 0) : ρ * imB s c θ ρ = Real.sin θ * phi s c θ ρ := by
  simp only [imB, trigFamily, phi]
  rw [mul_add, Finset.mul_sum, mul_add, Finset.mul_sum]
  have : ∀ j ∈ Finset.Icc 2 s, ρ * (c j * ρ ^ j * Real.sin (j * θ)) =
      Real.sin θ * (c j * ρ ^ (j + 1) * chebUPred (Real.cos θ) j) := by
    intro j _
    rw [← chebUPred_mul_sin θ j]; ring
  rw [Finset.sum_congr rfl this]
  field_simp
  ring

theorem reB_mul_eq (θ ρ : ℝ) (hρ : ρ ≠ 0) (hsin : Real.sin θ ≠ 0) (h : phi s c θ ρ = 0) :
    reB s c θ ρ * ρ = 2 * Real.cos θ * ρ ^ 2 +
      ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebU (Real.cos θ) j := by
  have hU : ∀ j : ℕ, chebU (Real.cos θ) j =
      Real.cos θ * chebUPred (Real.cos θ) j + Real.cos (j * θ) := by
    intro j
    apply mul_right_cancel₀ hsin
    have h1 : Real.sin (((j : ℝ) + 1) * θ) =
        Real.sin (j * θ) * Real.cos θ + Real.cos (j * θ) * Real.sin θ := by
      rw [add_mul, one_mul, Real.sin_add]
    rw [chebU_mul_sin, h1]
    linear_combination (-Real.cos θ) * chebUPred_mul_sin θ j
  simp only [reB, trigFamily, hU]
  simp only [phi] at h
  have h' : ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebUPred (Real.cos θ) j = 1 - ρ ^ 2 := by
    linarith
  have e : ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) *
      (Real.cos θ * chebUPred (Real.cos θ) j + Real.cos (j * θ)) =
      Real.cos θ * (1 - ρ ^ 2) +
        ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * Real.cos (j * θ) := by
    rw [← h', Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, add_mul, Finset.sum_mul]
  have : ∀ j ∈ Finset.Icc 2 s, c j * ρ ^ j * Real.cos (j * θ) * ρ =
      c j * ρ ^ (j + 1) * Real.cos (j * θ) := fun j _ => by ring
  rw [Finset.sum_congr rfl this]
  have hρρ : (ρ + 1 * ρ⁻¹) * Real.cos θ * ρ = (ρ ^ 2 + 1) * Real.cos θ := by field_simp
  rw [hρρ]
  ring

/-- Cauchy–Riemann: `∂_θ Im = ρ ∂_ρ Re`. -/
theorem trigFamilyθ_sin_eq (θ ρ : ℝ) (hρ : ρ ≠ 0) :
    trigFamilyθ s c (-1) Real.cos θ ρ = ρ * trigFamilyρ s c 1 Real.cos θ ρ := by
  simp only [trigFamilyθ, trigFamilyρ]
  rw [mul_add, Finset.mul_sum]
  have : ∀ j ∈ Finset.Icc 2 s, c j * ρ ^ j * (j * Real.cos (j * θ)) =
      ρ * (c j * (j * ρ ^ (j - 1)) * Real.cos (j * θ)) := by
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by have := (Finset.mem_Icc.mp hj).1; lia⟩
    simp only [Nat.add_sub_cancel]; ring
  rw [Finset.sum_congr rfl this]
  congr 1
  field_simp
  ring

/-- Cauchy–Riemann: `∂_θ Re = -ρ ∂_ρ Im`. -/
theorem trigFamilyθ_cos_eq (θ ρ : ℝ) (hρ : ρ ≠ 0) :
    trigFamilyθ s c 1 (fun t => -Real.sin t) θ ρ = -ρ * trigFamilyρ s c (-1) Real.sin θ ρ := by
  simp only [trigFamilyθ, trigFamilyρ]
  rw [mul_add, Finset.mul_sum]
  have : ∀ j ∈ Finset.Icc 2 s, c j * ρ ^ j * (j * -Real.sin (j * θ)) =
      -ρ * (c j * (j * ρ ^ (j - 1)) * Real.sin (j * θ)) := by
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by have := (Finset.mem_Icc.mp hj).1; lia⟩
    simp only [Nat.add_sub_cancel]; ring
  rw [Finset.sum_congr rfl this]
  congr 1
  field_simp
  ring

/-- `ρ² ∂_ρ Im = sin θ (ρ Φ_ρ - Φ)`. -/
theorem sq_mul_trigFamilyρ_eq (θ ρ : ℝ) (hρ : ρ ≠ 0) :
    ρ ^ 2 * trigFamilyρ s c (-1) Real.sin θ ρ =
      Real.sin θ * (ρ * phiρ s c θ ρ - phi s c θ ρ) := by
  simp only [trigFamilyρ, phiρ, phi]
  have hL : ρ ^ 2 * ∑ j ∈ Finset.Icc 2 s, c j * (j * ρ ^ (j - 1)) * Real.sin (j * θ) =
      ∑ j ∈ Finset.Icc 2 s, c j * j * ρ ^ (j + 1) * Real.sin (j * θ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by have := (Finset.mem_Icc.mp hj).1; lia⟩
    simp only [Nat.add_sub_cancel]; ring
  have hR : Real.sin θ * (ρ * ∑ j ∈ Finset.Icc 2 s,
        c j * ((j + 1) * ρ ^ j) * chebUPred (Real.cos θ) j -
      ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebUPred (Real.cos θ) j) =
      ∑ j ∈ Finset.Icc 2 s, c j * j * ρ ^ (j + 1) * Real.sin (j * θ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← chebUPred_mul_sin θ j]; ring
  have e : Real.sin θ * (ρ * (2 * ρ + ∑ j ∈ Finset.Icc 2 s,
        c j * ((j + 1) * ρ ^ j) * chebUPred (Real.cos θ) j) -
      (ρ ^ 2 - 1 + ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebUPred (Real.cos θ) j)) =
      Real.sin θ * (ρ ^ 2 + 1) + Real.sin θ * (ρ * ∑ j ∈ Finset.Icc 2 s,
        c j * ((j + 1) * ρ ^ j) * chebUPred (Real.cos θ) j -
      ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ (j + 1) * chebUPred (Real.cos θ) j) := by ring
  have h0 : ρ ^ 2 * ((1 - -1 * (ρ ^ 2)⁻¹) * Real.sin θ) = Real.sin θ * (ρ ^ 2 + 1) := by
    field_simp
    ring
  rw [e, hR, mul_add, hL, h0]


theorem phiρ_ge {θ : ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ρ * (2 - phiW s c ρ) ≤ phiρ s c θ ρ := by
  have hterm : ∀ j ∈ Finset.Icc 2 s, -(ρ * (((j : ℝ) + 1) * j * |c j| * ρ ^ (j - 1))) ≤
      c j * (((j : ℝ) + 1) * ρ ^ j) * chebUPred (Real.cos θ) j := by
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by have := (Finset.mem_Icc.mp hj).1; lia⟩
    have hu := abs_chebUPred_le (Real.abs_cos_le_one θ) (k + 1)
    have h1 : -(|c (k + 1)| * (((k + 1 : ℕ) : ℝ) + 1) * ρ ^ (k + 1) * ((k + 1 : ℕ) : ℝ)) ≤
        c (k + 1) * ((((k + 1 : ℕ) : ℝ) + 1) * ρ ^ (k + 1)) * chebUPred (Real.cos θ) (k + 1) := by
      have h2 : |c (k + 1) * ((((k + 1 : ℕ) : ℝ) + 1) * ρ ^ (k + 1)) *
          chebUPred (Real.cos θ) (k + 1)| ≤
          |c (k + 1)| * (((k + 1 : ℕ) : ℝ) + 1) * ρ ^ (k + 1) * ((k + 1 : ℕ) : ℝ) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hρ _),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1)]
        have := abs_nonneg (c (k + 1))
        have : 0 ≤ ((((k + 1 : ℕ) : ℝ) + 1) * ρ ^ (k + 1)) := by positivity
        calc _ ≤ |c (k + 1)| * ((((k + 1 : ℕ) : ℝ) + 1) * ρ ^ (k + 1)) * ((k + 1 : ℕ) : ℝ) := by
              gcongr
          _ = _ := by ring
      exact (neg_le_neg h2).trans (neg_abs_le _)
    simp only [Nat.add_sub_cancel]
    calc _ = -(|c (k + 1)| * (((k + 1 : ℕ) : ℝ) + 1) * ρ ^ (k + 1) * ((k + 1 : ℕ) : ℝ)) := by
          rw [show ρ ^ (k + 1) = ρ * ρ ^ k by ring]; ring
      _ ≤ _ := h1
  have := Finset.sum_le_sum hterm
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at this
  simp only [phiρ, phiW]
  linarith


section Roots

variable {R : ℝ}

theorem sq_mul_phiW (R : ℝ) :
    R ^ 2 * phiW s c R = perturbationB s c R + 2 * perturbationA s c R := by
  unfold phiW perturbationA perturbationB
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by have := (Finset.mem_Icc.mp hj).1; lia⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

theorem phiW_lt_two (hA : perturbationA s c R ≤ R ^ 2 - 1)
    (hB : perturbationB s c R ≤ 1) : phiW s c R < 2 := by
  have h := sq_mul_phiW (s := s) (c := c) R
  by_contra h'
  push Not at h'
  nlinarith

theorem continuous_phiW : Continuous (phiW s c) := by
  unfold phiW; fun_prop

theorem phiW_mono {ρ₁ ρ₂ : ℝ} (h₁ : 0 ≤ ρ₁) (h : ρ₁ ≤ ρ₂) : phiW s c ρ₁ ≤ phiW s c ρ₂ := by
  unfold phiW
  exact Finset.sum_le_sum fun j _ => by gcongr

theorem exists_gt_forall_phiW_lt (hA : perturbationA s c R ≤ R ^ 2 - 1)
    (hB : perturbationB s c R ≤ 1) :
    ∃ R₁, R < R₁ ∧ ∀ ρ, 0 < ρ → ρ < R₁ → phiW s c ρ < 2 := by
  have hev : ∀ᶠ ρ in 𝓝 R, phiW s c ρ < 2 :=
    (continuous_phiW (s := s) (c := c)).continuousAt.eventually_lt continuousAt_const
      (phiW_lt_two hA hB)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨R + ε, by linarith, fun ρ hρ hρ1 => ?_⟩
  by_cases hle : ρ ≤ R
  · exact (phiW_mono hρ.le hle).trans_lt (phiW_lt_two hA hB)
  · refine hball ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [not_le.mp hle]

theorem phi_zero (θ : ℝ) : phi s c θ 0 = -1 := by simp [phi]

theorem phi_nonneg_of_perturbationA_le {θ : ℝ} (hR : 0 ≤ R)
    (hA : perturbationA s c R ≤ R ^ 2 - 1) : 0 ≤ phi s c θ R := by
  have hterm : ∀ j ∈ Finset.Icc 2 s,
      -(j * |c j| * R ^ (j + 1)) ≤ c j * R ^ (j + 1) * chebUPred (Real.cos θ) j := by
    intro j _
    have hu := abs_chebUPred_le (Real.abs_cos_le_one θ) j
    have h2 : |c j * R ^ (j + 1) * chebUPred (Real.cos θ) j| ≤ j * |c j| * R ^ (j + 1) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hR _)]
      calc _ ≤ |c j| * R ^ (j + 1) * j := by gcongr
        _ = _ := by ring
    exact (neg_le_neg h2).trans (neg_abs_le _)
  have := Finset.sum_le_sum hterm
  rw [Finset.sum_neg_distrib] at this
  simp only [phi]
  unfold perturbationA at hA
  linarith

theorem hasDerivAt_phi (θ ρ : ℝ) : HasDerivAt (phi s c θ) (phiρ s c θ ρ) ρ := by
  have h := ((hasDerivAt_pow 2 ρ).sub_const 1).add
    (HasDerivAt.fun_sum fun j (_ : j ∈ Finset.Icc 2 s) =>
      ((hasDerivAt_pow (j + 1) ρ).const_mul (c j)).mul_const (chebUPred (Real.cos θ) j))
  refine h.congr_deriv ?_
  simp only [phiρ]
  congr 1
  · simp
  · exact Finset.sum_congr rfl fun j _ => by simp

theorem continuous_phi (θ : ℝ) : Continuous (phi s c θ) := by
  unfold phi; fun_prop

theorem strictMonoOn_phi {R₁ : ℝ} (hR1 : ∀ ρ, 0 < ρ → ρ < R₁ → phiW s c ρ < 2) {θ : ℝ}
    : StrictMonoOn (phi s c θ) (Set.Icc 0 R₁) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 R₁) (continuous_phi θ).continuousOn fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hasDerivAt_phi θ x).deriv]
  have h1 := phiρ_ge (s := s) (c := c) (θ := θ) hx.1.le
  have h2 : 0 < x * (2 - phiW s c x) := mul_pos hx.1 (by linarith [hR1 x hx.1 hx.2])
  linarith

theorem exists_root_Ioc {θ : ℝ} (hR : 0 ≤ R)
    (hA : perturbationA s c R ≤ R ^ 2 - 1) : ∃ ρ, 0 < ρ ∧ ρ ≤ R ∧ phi s c θ ρ = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Icc (phi s c θ 0) (phi s c θ R) :=
    ⟨by rw [phi_zero]; norm_num, phi_nonneg_of_perturbationA_le hR hA⟩
  obtain ⟨ρ, ⟨hρ0, hρR⟩, hρ⟩ :=
    intermediate_value_Icc hR (continuous_phi (s := s) (c := c) θ).continuousOn hmem
  refine ⟨ρ, lt_of_le_of_ne hρ0 ?_, hρR, hρ⟩
  rintro rfl
  rw [phi_zero] at hρ
  norm_num at hρ

open scoped Classical in
/-- The positive root `ρ(θ) ≤ R` of `Φ(θ, ·)`. -/
def rho (s : ℕ) (c : ℕ → ℝ) (R θ : ℝ) : ℝ :=
  if h : ∃ ρ, 0 < ρ ∧ ρ ≤ R ∧ phi s c θ ρ = 0 then Classical.choose h else 1

theorem rho_spec {θ : ℝ} (hR : 0 ≤ R)
    (hA : perturbationA s c R ≤ R ^ 2 - 1) :
    0 < rho s c R θ ∧ rho s c R θ ≤ R ∧ phi s c θ (rho s c R θ) = 0 := by
  have h := exists_root_Ioc (θ := θ) hR hA
  simp only [rho, h, ↓reduceDIte]
  exact Classical.choose_spec h

end Roots

section Derivative

variable {R R₁ : ℝ}

theorem phiρ_pos (hR1 : ∀ ρ, 0 < ρ → ρ < R₁ → phiW s c ρ < 2) {θ ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < R₁) : 0 < phiρ s c θ ρ := by
  have h1 := phiρ_ge (s := s) (c := c) (θ := θ) hρ0.le
  have h2 : 0 < ρ * (2 - phiW s c ρ) := mul_pos hρ0 (by linarith [hR1 ρ hρ0 hρ1])
  linarith

theorem trigFamilyρ_sin_pos (hR1 : ∀ ρ, 0 < ρ → ρ < R₁ → phiW s c ρ < 2) {θ ρ : ℝ}
    (hsin : 0 < Real.sin θ) (hρ0 : 0 < ρ) (hρ1 : ρ < R₁) (hphi : phi s c θ ρ = 0) :
    0 < trigFamilyρ s c (-1) Real.sin θ ρ := by
  have h := sq_mul_trigFamilyρ_eq (s := s) (c := c) θ ρ hρ0.ne'
  rw [hphi, sub_zero] at h
  have : 0 < ρ ^ 2 * trigFamilyρ s c (-1) Real.sin θ ρ := by
    rw [h]; exact mul_pos hsin (mul_pos hρ0 (phiρ_pos hR1 hρ0 hρ1))
  exact (mul_pos_iff_of_pos_left (pow_pos hρ0 2)).mp this

theorem imB_eq_zero_of_phi {θ ρ : ℝ} (hρ : ρ ≠ 0) (h : phi s c θ ρ = 0) : imB s c θ ρ = 0 := by
  have := mul_imB_eq (s := s) (c := c) θ ρ hρ
  rw [h, mul_zero] at this
  exact (mul_eq_zero.mp this).resolve_left hρ

theorem phi_eq_zero_of_imB {θ ρ : ℝ} (hsin : 0 < Real.sin θ) (hρ : ρ ≠ 0)
    (h : imB s c θ ρ = 0) : phi s c θ ρ = 0 := by
  have := mul_imB_eq (s := s) (c := c) θ ρ hρ
  rw [h, mul_zero] at this
  exact (mul_eq_zero.mp this.symm).resolve_left hsin.ne'

theorem exists_hasDerivAt_reB_rho (hR : 0 < R) (hA : perturbationA s c R ≤ R ^ 2 - 1)
    (hRR1 : R < R₁) (hR1 : ∀ ρ, 0 < ρ → ρ < R₁ → phiW s c ρ < 2) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Set.Ioo 0 Real.pi) :
    ∃ d : ℝ, d < 0 ∧ HasDerivAt (fun θ => reB s c θ (rho s c R θ)) d θ₀ := by
  have hsin0 : 0 < Real.sin θ₀ := Real.sin_pos_of_pos_of_lt_pi hθ₀.1 hθ₀.2
  obtain ⟨hρ0, hρR, hphi0⟩ := rho_spec (s := s) (c := c) (θ := θ₀) hR.le hA
  set ρ₀ := rho s c R θ₀ with hρ₀
  have hne0 : ρ₀ ≠ 0 := hρ0.ne'
  have hFρ : 0 < trigFamilyρ s c (-1) Real.sin θ₀ ρ₀ :=
    trigFamilyρ_sin_pos hR1 hsin0 hρ0 (hρR.trans_lt hRR1) hphi0
  have hev : ∀ᶠ v : ℝ × ℝ in 𝓝 (θ₀, ρ₀), v.2 ≠ 0 :=
    continuousAt_snd.eventually_ne hne0
  obtain ⟨ψ, hψd, hψt, hψe⟩ := exists_differentiableAt_implicit (F := imB s c)
    (Fθ := trigFamilyθ s c (-1) Real.cos) (Fρ := trigFamilyρ s c (-1) Real.sin)
    (hev.mono fun v hv => hasDerivAt_trigFamily_left Real.hasDerivAt_sin hv v.1)
    (hev.mono fun v hv => hasDerivAt_trigFamily_right Real.hasDerivAt_sin v.1 hv)
    (continuousAt_trigFamilyθ Real.continuous_cos hne0)
    (continuousAt_trigFamilyρ Real.continuous_sin hne0) hFρ.ne'
  have hF0 : imB s c θ₀ ρ₀ = 0 := imB_eq_zero_of_phi hne0 hphi0
  have heq : ψ =ᶠ[𝓝 θ₀] rho s c R := by
    have h1 : ∀ᶠ θ in 𝓝 θ₀, θ ∈ Set.Ioo 0 Real.pi := Ioo_mem_nhds hθ₀.1 hθ₀.2
    have h2 : ∀ᶠ θ in 𝓝 θ₀, ψ θ ∈ Set.Ioo 0 R₁ :=
      hψt.eventually (Ioo_mem_nhds hρ0 (hρR.trans_lt hRR1))
    filter_upwards [h1, h2, hψe] with θ hθ hψmem hψθ
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    obtain ⟨hr0, hrR, hphi⟩ := rho_spec (s := s) (c := c) (θ := θ) hR.le hA
    have hphiψ : phi s c θ (ψ θ) = 0 := phi_eq_zero_of_imB hsin hψmem.1.ne' (hψθ.trans hF0)
    exact (strictMonoOn_phi hR1).injOn ⟨hψmem.1.le, hψmem.2.le⟩
      ⟨hr0.le, hrR.trans hRR1.le⟩ (hphiψ.trans hphi.symm)
  have hρd : DifferentiableAt ℝ (rho s c R) θ₀ := hψd.congr_of_eventuallyEq heq.symm
  obtain ⟨ρ', hρ⟩ : ∃ ρ', HasDerivAt (rho s c R) ρ' θ₀ := ⟨_, hρd.hasDerivAt⟩
  have hi := hasDerivAt_trigFamily (s := s) (c := c) (σ := -1) Real.hasDerivAt_sin
    (hasDerivAt_id' θ₀) hρ hne0
  have hi0 : HasDerivAt (fun θ => imB s c θ (rho s c R θ)) 0 θ₀ := by
    refine (hasDerivAt_const θ₀ (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hθ₀.1 hθ₀.2] with θ hθ
    obtain ⟨hr0, _, hphi⟩ := rho_spec (s := s) (c := c) (θ := θ) hR.le hA
    exact imB_eq_zero_of_phi hr0.ne' hphi
  have key1 := hi.unique hi0
  have hii := hasDerivAt_trigFamily (s := s) (c := c) (σ := 1) (T := Real.cos)
    (T' := fun t => -Real.sin t) Real.hasDerivAt_cos (hasDerivAt_id' θ₀) hρ hne0
  have cr1 := trigFamilyθ_sin_eq (s := s) (c := c) θ₀ ρ₀ hne0
  have cr2 := trigFamilyθ_cos_eq (s := s) (c := c) θ₀ ρ₀ hne0
  refine ⟨_, ?_, hii⟩
  rw [← hρ₀] at key1 ⊢
  simp only [cr1, cr2] at key1 ⊢
  set a := trigFamilyρ s c 1 Real.cos θ₀ ρ₀
  set b := trigFamilyρ s c (-1) Real.sin θ₀ ρ₀
  have h3 : b * (-ρ₀ * b * 1 + a * ρ') = -ρ₀ * (a ^ 2 + b ^ 2) := by linear_combination a * key1
  by_contra h
  push Not at h
  nlinarith [mul_nonneg hFρ.le h, mul_pos hρ0 (add_pos_of_nonneg_of_pos (sq_nonneg a)
    (pow_pos hFρ 2))]

theorem continuousOn_reB_rho (hR : 0 < R) (hA : perturbationA s c R ≤ R ^ 2 - 1)
    (hB : perturbationB s c R ≤ 1) :
    ContinuousOn (fun θ => reB s c θ (rho s c R θ)) (Set.Ioo 0 Real.pi) := by
  obtain ⟨R₁, hRR1, hR1⟩ := exists_gt_forall_phiW_lt hA hB
  intro θ hθ
  obtain ⟨d, _, hd⟩ := exists_hasDerivAt_reB_rho hR hA hRR1 hR1 hθ
  exact hd.continuousAt.continuousWithinAt

theorem strictAntiOn_reB_rho (hR : 0 < R) (hA : perturbationA s c R ≤ R ^ 2 - 1)
    (hB : perturbationB s c R ≤ 1) :
    StrictAntiOn (fun θ => reB s c θ (rho s c R θ)) (Set.Ioo 0 Real.pi) := by
  obtain ⟨R₁, hRR1, hR1⟩ := exists_gt_forall_phiW_lt hA hB
  refine strictAntiOn_of_deriv_neg (convex_Ioo 0 Real.pi) (continuousOn_reB_rho hR hA hB) ?_
  intro θ hθ
  rw [interior_Ioo] at hθ
  obtain ⟨d, hd, hderiv⟩ := exists_hasDerivAt_reB_rho hR hA hRR1 hR1 hθ
  rw [hderiv.deriv]
  exact hd

end Derivative

end Curve

end RealRooted.ToeplitzPerturbation
