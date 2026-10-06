import RealRooted.CombinatorialExamples.BigDescents321.Kernel
import Mathlib.Tactic.FieldSimp

/-!
# The kernel moments as weighted finite sums

For `r ≥ 2` the kernel coefficients `c_r(J) = -m(r, J)` have the positive-weight form

`c_r(J) = 2^(1 - 2r) ∑_(k ≤ r) W_(r,k)(J) F(r, J, k)`,

`W_(r,k)(J) = (r+k-2)! (2J+r+k+1)! (J+k+1)! / (k! (r-k)! (2J+2k+3)! (J+k+r+1)!)`,
`F(r, J, k) = k(4J + 3k + 2r + 5) - r(r - 1)`.

Both sides satisfy the recurrence
`2(r+1) m(r+1, J) = (1 - 2r)(m(r, J+2) - 2 m(r, J+1)) - ((r - 2)/2) m(r-1, J+1)`,
which for the moments comes from the differential equation of `√D` in `y`, and for the sums
from an explicit telescoping certificate in `k`.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted.BigDescents321

/-- The weights `W_(r,k)(J)`. -/
def kernelWeight (r k J : ℕ) : ℚ :=
  ((r + k - 2).factorial * (2 * J + r + k + 1).factorial * (J + k + 1).factorial : ℚ) /
    ((k.factorial * (r - k).factorial * (2 * J + 2 * k + 3).factorial *
      (J + k + r + 1).factorial : ℕ) : ℚ)

/-- `F(r, J, k) = k(4J + 3k + 2r + 5) - r(r - 1)`. -/
def kernelF (r J k : ℕ) : ℚ := k * (4 * J + 3 * k + 2 * r + 5) - r * (r - 1 : ℚ)

theorem kernelWeight_pos (r k J : ℕ) : 0 < kernelWeight r k J := by
  unfold kernelWeight
  apply div_pos
  · positivity
  · have : 0 < k.factorial * (r - k).factorial * (2 * J + 2 * k + 3).factorial *
        (J + k + r + 1).factorial := by positivity
    exact_mod_cast this

/-- `W_(r+1,k+1)(J) / W_(r+1,k)(J)`. -/
theorem kernelWeight_succ_right {r k J : ℕ} (hr : 2 ≤ r) (hk : k ≤ r) :
    kernelWeight (r + 1) (k + 1) J = kernelWeight (r + 1) k J *
      ((r + k) * (2 * J + r + k + 3) * (J + k + 2) * (r + 1 - k) /
        ((k + 1) * (2 * J + 2 * k + 4) * (2 * J + 2 * k + 5) * (J + k + r + 3)) : ℚ) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = k + s := ⟨r - k, by lia⟩
  obtain ⟨u, hu⟩ : ∃ u, k + s + 1 + k - 2 = u := ⟨_, rfl⟩
  simp only [kernelWeight]
  rw [show k + s + 1 + (k + 1) - 2 = u + 1 by lia, hu,
    show k + s + 1 - (k + 1) = s by lia, show k + s + 1 - k = s + 1 by lia,
    show 2 * J + (k + s + 1) + (k + 1) + 1 = 2 * J + (k + s + 1) + k + 1 + 1 by ring,
    show J + (k + 1) + 1 = J + k + 1 + 1 by ring,
    show 2 * J + 2 * (k + 1) + 3 = 2 * J + 2 * k + 3 + 1 + 1 by ring,
    show J + (k + 1) + (k + s + 1) + 1 = J + k + (k + s + 1) + 1 + 1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  have hu' : (u : ℚ) = 2 * k + s - 1 := by
    have : u + 1 = 2 * k + s := by lia
    rw [eq_sub_iff_add_eq]; exact_mod_cast this
  rw [hu']
  field_simp
  ring

/-- `W_(r,k)(J+2) / W_(r+1,k)(J)`. -/
theorem kernelWeight_two {r k J : ℕ} (hr : 2 ≤ r) (hk : k ≤ r) :
    kernelWeight r k (J + 2) = kernelWeight (r + 1) k J *
      ((2 * J + r + k + 3) * (2 * J + r + k + 4) * (2 * J + r + k + 5) * (J + k + 2) *
        (J + k + 3) * (r + 1 - k) / ((r + k - 1) * (2 * J + 2 * k + 4) * (2 * J + 2 * k + 5) *
        (2 * J + 2 * k + 6) * (2 * J + 2 * k + 7) * (J + k + r + 3)) : ℚ) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = k + s := ⟨r - k, by lia⟩
  simp only [kernelWeight]
  rw [show k + s + 1 + k - 2 = (k + s + k - 2) + 1 by lia, show k + s - k = s by lia,
    show k + s + 1 - k = s + 1 by lia,
    show 2 * (J + 2) + (k + s) + k + 1 = (2 * J + (k + s + 1) + k + 1) + 1 + 1 + 1 by ring,
    show J + 2 + k + 1 = (J + k + 1) + 1 + 1 by ring,
    show 2 * (J + 2) + 2 * k + 3 = (2 * J + 2 * k + 3) + 1 + 1 + 1 + 1 by ring,
    show J + 2 + k + (k + s) + 1 = (J + k + (k + s + 1) + 1) + 1 by ring]
  generalize hu : k + s + k - 2 = u
  generalize hA : 2 * J + (k + s + 1) + k + 1 = A
  generalize hB : J + k + 1 = B
  generalize hC : 2 * J + 2 * k + 3 = Cc
  generalize hE : J + k + (k + s + 1) + 1 = E
  simp only [Nat.factorial_succ]
  push_cast
  have hu' : (u : ℚ) = 2 * k + s - 2 := by
    have : u + 2 = 2 * k + s := by lia
    rw [eq_sub_iff_add_eq]; exact_mod_cast this
  have h2 : (2 : ℚ) ≤ k + s := by exact_mod_cast hr
  have hk0 : (0 : ℚ) ≤ k := k.cast_nonneg
  have hn1 : ((k : ℚ) + s + k - 1) ≠ 0 := by intro h; linarith
  have hn2 : ((k : ℚ) + s + k + 1) ≠ 0 := by intro h; linarith
  have hn3 : ((k : ℚ) + s + k) ≠ 0 := by intro h; linarith
  have hn4 : (2 * (k : ℚ) + s - 2 + 1) ≠ 0 := by intro h; linarith
  have hA' : (A : ℚ) = 2 * J + 2 * k + s + 2 := by rw [← hA]; push_cast; ring
  have hB' : (B : ℚ) = J + k + 1 := by rw [← hB]; push_cast; ring
  have hC' : (Cc : ℚ) = 2 * J + 2 * k + 3 := by rw [← hC]; push_cast; ring
  have hE' : (E : ℚ) = J + 2 * k + s + 2 := by rw [← hE]; push_cast; ring
  rw [hu', hA', hB', hC', hE']
  field_simp
  ring

/-- `W_(r,k)(J+1) / W_(r+1,k)(J)`. -/
theorem kernelWeight_one {r k J : ℕ} (hr : 2 ≤ r) (hk : k ≤ r) :
    kernelWeight r k (J + 1) = kernelWeight (r + 1) k J *
      ((2 * J + r + k + 3) * (J + k + 2) * (r + 1 - k) /
        ((r + k - 1) * (2 * J + 2 * k + 4) * (2 * J + 2 * k + 5)) : ℚ) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = k + s := ⟨r - k, by lia⟩
  simp only [kernelWeight]
  rw [show k + s + 1 + k - 2 = (k + s + k - 2) + 1 by lia, show k + s - k = s by lia,
    show k + s + 1 - k = s + 1 by lia,
    show 2 * (J + 1) + (k + s) + k + 1 = (2 * J + (k + s + 1) + k + 1) + 1 by ring,
    show J + 1 + k + 1 = (J + k + 1) + 1 by ring,
    show 2 * (J + 1) + 2 * k + 3 = (2 * J + 2 * k + 3) + 1 + 1 by ring,
    show J + 1 + k + (k + s) + 1 = J + k + (k + s + 1) + 1 by ring]
  generalize hu : k + s + k - 2 = u
  generalize hA : 2 * J + (k + s + 1) + k + 1 = A
  generalize hB : J + k + 1 = B
  generalize hC : 2 * J + 2 * k + 3 = Cc
  generalize hE : J + k + (k + s + 1) + 1 = E
  simp only [Nat.factorial_succ]
  push_cast
  have hu' : (u : ℚ) = 2 * k + s - 2 := by
    have : u + 2 = 2 * k + s := by lia
    rw [eq_sub_iff_add_eq]; exact_mod_cast this
  have h2 : (2 : ℚ) ≤ k + s := by exact_mod_cast hr
  have hk0 : (0 : ℚ) ≤ k := k.cast_nonneg
  have hn1 : ((k : ℚ) + s + k - 1) ≠ 0 := by intro h; linarith
  have hn2 : ((k : ℚ) + s + k + 1) ≠ 0 := by intro h; linarith
  have hn3 : ((k : ℚ) + s + k) ≠ 0 := by intro h; linarith
  have hn4 : (2 * (k : ℚ) + s - 2 + 1) ≠ 0 := by intro h; linarith
  have hA' : (A : ℚ) = 2 * J + 2 * k + s + 2 := by rw [← hA]; push_cast; ring
  have hB' : (B : ℚ) = J + k + 1 := by rw [← hB]; push_cast; ring
  have hC' : (Cc : ℚ) = 2 * J + 2 * k + 3 := by rw [← hC]; push_cast; ring
  have hE' : (E : ℚ) = J + 2 * k + s + 2 := by rw [← hE]; push_cast; ring
  rw [hu', hA', hB', hC']
  field_simp
  ring

/-- `W_(r,k)(J+1) / W_(r+2,k)(J)`, the lower neighbour in the recurrence. -/
theorem kernelWeight_lower {r k J : ℕ} (hr : 2 ≤ r) (hk : k ≤ r) :
    kernelWeight r k (J + 1) = kernelWeight (r + 2) k J *
      ((r + 2 - k) * (r + 1 - k) * (J + k + 2) * (J + k + r + 3) /
        ((r + k) * (r + k - 1) * (2 * J + 2 * k + 4) * (2 * J + 2 * k + 5)) : ℚ) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = k + s := ⟨r - k, by lia⟩
  simp only [kernelWeight]
  rw [show k + s + 2 + k - 2 = (k + s + k - 2) + 1 + 1 by lia, show k + s - k = s by lia,
    show k + s + 2 - k = s + 1 + 1 by lia,
    show 2 * (J + 1) + (k + s) + k + 1 = 2 * J + (k + s + 2) + k + 1 by ring,
    show J + 1 + k + 1 = (J + k + 1) + 1 by ring,
    show 2 * (J + 1) + 2 * k + 3 = (2 * J + 2 * k + 3) + 1 + 1 by ring,
    show J + k + (k + s + 2) + 1 = (J + 1 + k + (k + s) + 1) + 1 by ring]
  generalize hu : k + s + k - 2 = u
  generalize hA : 2 * J + (k + s + 2) + k + 1 = A
  generalize hB : J + k + 1 = B
  generalize hC : 2 * J + 2 * k + 3 = Cc
  generalize hE : J + 1 + k + (k + s) + 1 = E
  simp only [Nat.factorial_succ]
  push_cast
  have hu' : (u : ℚ) = 2 * k + s - 2 := by
    have : u + 2 = 2 * k + s := by lia
    rw [eq_sub_iff_add_eq]; exact_mod_cast this
  have h2 : (2 : ℚ) ≤ k + s := by exact_mod_cast hr
  have hk0 : (0 : ℚ) ≤ k := k.cast_nonneg
  have hn1 : ((k : ℚ) + s + k - 1) ≠ 0 := by intro h; linarith
  have hn2 : ((k : ℚ) + s + k + 1) ≠ 0 := by intro h; linarith
  have hn3 : ((k : ℚ) + s + k) ≠ 0 := by intro h; linarith
  have hn4 : (2 * (k : ℚ) + s - 2 + 1) ≠ 0 := by intro h; linarith
  have hA' : (A : ℚ) = 2 * J + 2 * k + s + 3 := by rw [← hA]; push_cast; ring
  have hB' : (B : ℚ) = J + k + 1 := by rw [← hB]; push_cast; ring
  have hC' : (Cc : ℚ) = 2 * J + 2 * k + 3 := by rw [← hC]; push_cast; ring
  have hE' : (E : ℚ) = J + 2 * k + s + 2 := by rw [← hE]; push_cast; ring
  rw [hu', hB', hC', hE']
  field_simp
  ring

/-! ### The recurrence in `r` -/

private theorem coeff_derivative_kernelSqrt (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.derivative kernelSqrt) =
      (m + 1 : ℚ[X]) * kernelPoly (m + 1) := by
  rw [PowerSeries.coeff_derivative, kernelPoly]
  ring

private theorem kernel_ode (t : ℕ) :
    2 * PowerSeries.coeff (t + 1) (kernelDisc * PowerSeries.derivative kernelSqrt) =
      PowerSeries.coeff (t + 1) (PowerSeries.derivative kernelDisc * kernelSqrt) := by
  have h := congrArg (PowerSeries.coeff (t + 1))
    (PowerSeries.two_mul_mul_derivative_sqrt constantCoeff_kernelDisc)
  rw [mul_assoc, show (2 : PowerSeries ℚ[X]) = PowerSeries.C 2 from (map_ofNat _ 2).symm,
    PowerSeries.coeff_C_mul] at h
  exact h

/-- `2(t + 2) d_(t+2) = (2t + 1) v(2 - v) d_(t+1) - ((t - 1)/2) v d_t`. -/
theorem kernelPoly_rec (t : ℕ) :
    (2 * (t : ℚ[X]) + 4) * kernelPoly (t + 2) =
      (2 * (t : ℚ[X]) + 1) * (X * (2 - X)) * kernelPoly (t + 1) -
        C (((t : ℚ) - 1) / 2) * X * kernelPoly t := by
  have h := kernel_ode t
  have hD : PowerSeries.derivative kernelDisc =
      -PowerSeries.C (X * (2 - X) : ℚ[X]) + 2 * PowerSeries.C (C (1 / 4) * X : ℚ[X]) *
        PowerSeries.X := by
    simp [kernelDisc, Derivation.leibniz_pow]
    ring
  rw [hD] at h
  simp only [kernelDisc, sub_mul, add_mul, neg_mul, map_add, map_sub, map_neg, one_mul,
    mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    show (2 : PowerSeries ℚ[X]) = PowerSeries.C 2 from (map_ofNat _ 2).symm,
    PowerSeries.coeff_X_pow_mul', coeff_derivative_kernelSqrt] at h
  simp only [show ∀ m, PowerSeries.coeff m kernelSqrt = kernelPoly m from fun _ ↦ rfl] at h
  have hc : C (((t : ℚ) - 1) / 2) = C (1 / 4) * (2 * (t : ℚ[X]) - 2) := by
    rw [show (2 * (t : ℚ[X]) - 2) = C (2 * (t : ℚ) - 2) by simp [map_ofNat], ← C_mul]
    congr 1
    ring
  rw [hc]
  rcases t with _ | t
  · simp only [show ¬ (2 ≤ 0 + 1) by norm_num, ↓reduceIte, mul_zero, add_zero] at h
    push_cast at h ⊢
    linear_combination h
  · simp only [show 2 ≤ t + 1 + 1 by lia, ↓reduceIte, show t + 1 + 1 - 2 = t by lia] at h
    push_cast at h ⊢
    linear_combination h

theorem kernelMoment_natCast (r J : ℕ) :
    kernelMoment r J = integral 0 1 (X ^ J * kernelPoly r) := by
  simp only [kernelMoment, kernelPolyZ, show ¬ ((r : ℤ) < 0) by lia, ↓reduceIte, Int.toNat_natCast]

/-- The moment recurrence
`(2t + 4) m(t+2, J) = (2t + 1)(2 m(t+1, J+1) - m(t+1, J+2)) - ((t - 1)/2) m(t, J+1)`. -/
theorem kernelMoment_rec (t J : ℕ) :
    (2 * t + 4) * kernelMoment (t + 2 : ℕ) J =
      (2 * t + 1) * (2 * kernelMoment (t + 1 : ℕ) (J + 1) - kernelMoment (t + 1 : ℕ) (J + 2)) -
        ((t - 1) / 2) * kernelMoment t (J + 1) := by
  have h := congrArg (fun p ↦ integral (0 : ℚ) 1 (X ^ J * p)) (kernelPoly_rec t)
  have e1 : X ^ J * ((2 * (t : ℚ[X]) + 4) * kernelPoly (t + 2)) =
      C (2 * (t : ℚ) + 4) * (X ^ J * kernelPoly (t + 2)) := by
    rw [show (2 * (t : ℚ[X]) + 4) = C (2 * (t : ℚ) + 4) by simp [map_ofNat]]; ring
  have e2 : X ^ J * ((2 * (t : ℚ[X]) + 1) * (X * (2 - X)) * kernelPoly (t + 1) -
      C (((t : ℚ) - 1) / 2) * X * kernelPoly t) =
      C (2 * (2 * (t : ℚ) + 1)) * (X ^ (J + 1) * kernelPoly (t + 1)) -
        C (2 * (t : ℚ) + 1) * (X ^ (J + 2) * kernelPoly (t + 1)) -
        C (((t : ℚ) - 1) / 2) * (X ^ (J + 1) * kernelPoly t) := by
    rw [show (2 * (t : ℚ[X]) + 1) = C (2 * (t : ℚ) + 1) by simp [map_ofNat],
      show C (2 * (2 * (t : ℚ) + 1)) = 2 * C (2 * (t : ℚ) + 1) by simp [map_ofNat]]
    ring
  rw [e1, e2] at h
  simp only [LinearMap.map_sub, integral_C_mul] at h
  simp only [kernelMoment_natCast]
  linarith

/-! ### The telescoping certificate -/

section Certificate

variable (r J k : ℚ)

/-- `F(r, J, k)`, over any commutative ring. -/
def certF {α : Type*} [CommRing α] (r J k : α) : α :=
  k * (4 * J + 3 * k + 2 * r + 5) - r * (r - 1)

/-- `W_(r+1,k+1)(J) / W_(r+1,k)(J)`. -/
def certBq : ℚ := (r + k) * (2 * J + r + k + 3) * (J + k + 2) * (r + 1 - k) /
  ((k + 1) * (2 * J + 2 * k + 4) * (2 * J + 2 * k + 5) * (J + k + r + 3))

/-- `W_(r,k)(J+2) / W_(r+1,k)(J)`. -/
def certR2 : ℚ := (2 * J + r + k + 3) * (2 * J + r + k + 4) * (2 * J + r + k + 5) * (J + k + 2) *
  (J + k + 3) * (r + 1 - k) / ((r + k - 1) * (2 * J + 2 * k + 4) * (2 * J + 2 * k + 5) *
  (2 * J + 2 * k + 6) * (2 * J + 2 * k + 7) * (J + k + r + 3))

/-- `W_(r,k)(J+1) / W_(r+1,k)(J)`. -/
def certR1 : ℚ := (2 * J + r + k + 3) * (J + k + 2) * (r + 1 - k) /
  ((r + k - 1) * (2 * J + 2 * k + 4) * (2 * J + 2 * k + 5))

/-- `W_(r-1,k)(J+1) / W_(r+1,k)(J)`. -/
def certR0 : ℚ := (r + 1 - k) * (r - k) * (J + k + 2) * (J + k + r + 2) /
  ((r + k - 1) * (r + k - 2) * (2 * J + 2 * k + 4) * (2 * J + 2 * k + 5))

/-- The summand of the recurrence, divided by `W_(r+1,k)(J)`. -/
def certRho : ℚ := 2 * (r + 1) * certF (r + 1) J k - 4 * (1 - 2 * r) * certR2 r J k *
  certF r (J + 2) k + 8 * (1 - 2 * r) * certR1 r J k * certF r (J + 1) k +
  8 * (r - 2) * certR0 r J k * certF (r - 1) (J + 1) k

/-- The telescoping certificate `σ(k)`. -/
def certSigma : ℚ := -2 * k * (2 * r - 1) * (16 * J ^ 2 * k ^ 2 - 16 * J ^ 2 * k +
  24 * J * k ^ 3 + 16 * J * k ^ 2 * r + 40 * J * k ^ 2 - 8 * J * k * r ^ 2 - 8 * J * k * r -
  64 * J * k + 9 * k ^ 4 + 12 * k ^ 3 * r + 38 * k ^ 3 - 2 * k ^ 2 * r ^ 2 + 26 * k ^ 2 * r +
  15 * k ^ 2 - 4 * k * r ^ 3 - 14 * k * r ^ 2 - 18 * k * r - 62 * k + r ^ 4 - 2 * r ^ 3 -
  r ^ 2 + 2 * r) / ((k + r - 2) * (k + r - 1) * (2 * J + 2 * k + 5))

theorem certRho_eq {r J k : ℚ} (hr : 3 ≤ r) (hJ : 0 ≤ J) (hk : 0 ≤ k) :
    certRho r J k = certBq r J k * certSigma r J (k + 1) - certSigma r J k := by
  unfold certRho certF certBq certR2 certR1 certR0 certSigma
  have h1 : r + k - 1 ≠ 0 := by intro h; linarith
  have h2 : r + k - 2 ≠ 0 := by intro h; linarith
  have h3 : k + r - 2 ≠ 0 := by intro h; linarith
  have h4 : k + r - 1 ≠ 0 := by intro h; linarith
  have h5 : k + 1 + r - 2 ≠ 0 := by intro h; linarith
  have h6 : k + 1 + r - 1 ≠ 0 := by intro h; linarith
  have h7 : 2 * J + 2 * k + 4 ≠ 0 := by intro h; linarith
  have h8 : 2 * J + 2 * k + 5 ≠ 0 := by intro h; linarith
  have h9 : 2 * J + 2 * k + 6 ≠ 0 := by intro h; linarith
  have h10 : 2 * J + 2 * k + 7 ≠ 0 := by intro h; linarith
  have h11 : 2 * J + 2 * (k + 1) + 5 ≠ 0 := by intro h; linarith
  have h12 : J + k + r + 3 ≠ 0 := by intro h; linarith
  have h13 : k + 1 ≠ 0 := by intro h; linarith
  field_simp
  ring

end Certificate

/-! ### The sums satisfy the moment recurrence -/

/-- `∑_(k ≤ r+1) W_(r+1,k)(J) ρ(k) = 0`, by telescoping. -/
theorem sum_kernelWeight_mul_certRho {r J : ℕ} (hr : 3 ≤ r) :
    ∑ k ∈ range (r + 2), kernelWeight (r + 1) k J * certRho r J k = 0 := by
  have hr' : (3 : ℚ) ≤ r := by exact_mod_cast hr
  have hsum : ∀ k ∈ range (r + 2), kernelWeight (r + 1) k J * certRho r J k =
      kernelWeight (r + 1) k J * certBq r J k * certSigma r J ((k : ℚ) + 1) -
        kernelWeight (r + 1) k J * certSigma r J k := fun k _ ↦ by
    rw [certRho_eq hr' (by positivity) (by positivity)]; ring
  rw [sum_congr rfl hsum, sum_sub_distrib, sum_range_succ, sum_range_succ' _ (r + 1)]
  have htop : certBq r J ((r + 1 : ℕ) : ℚ) = 0 := by
    simp [certBq]
  have hzero : certSigma r J ((0 : ℕ) : ℚ) = 0 := by simp [certSigma]
  rw [htop, hzero, mul_zero, zero_mul, mul_zero, add_zero, add_zero, sub_eq_zero]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk' := mem_range.mp hk
  rw [kernelWeight_succ_right (by lia) (by lia)]
  push_cast
  rfl

/-- The weighted sum `2^(1-2r) ∑_(k ≤ r) W_(r,k)(J) F(r, J, k)`. -/
def kernelSum (r J : ℕ) : ℚ :=
  2 * (1 / 4) ^ r * ∑ k ∈ range (r + 1), kernelWeight r k J * kernelF r J k

/-- The sums satisfy the recurrence of the moments. -/
theorem kernelSum_rec {t : ℕ} (ht : 2 ≤ t) (J : ℕ) :
    (2 * t + 4) * kernelSum (t + 2) J =
      (2 * t + 1) * (2 * kernelSum (t + 1) (J + 1) - kernelSum (t + 1) (J + 2)) -
        ((t - 1) / 2) * kernelSum t (J + 1) := by
  have hT := sum_kernelWeight_mul_certRho (r := t + 1) (J := J) (by lia)
  have h2 : ∑ k ∈ range (t + 1 + 1), kernelWeight (t + 1) k (J + 2) * kernelF (t + 1) (J + 2) k =
      ∑ k ∈ range (t + 1 + 2), kernelWeight (t + 1 + 1) k J *
        (certR2 (t + 1 : ℕ) J k * certF ((t + 1 : ℕ) : ℚ) ((J : ℚ) + 2) k) := by
    rw [sum_range_succ _ (t + 1 + 1)]
    have h0 : certR2 (t + 1 : ℕ) J ((t + 1 + 1 : ℕ) : ℚ) = 0 := by simp [certR2]
    rw [h0, zero_mul, mul_zero, add_zero]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [kernelWeight_two (by lia) (by have := mem_range.mp hk; lia)]
    simp only [kernelF, certF, certR2]
    push_cast
    ring
  have h1 : ∑ k ∈ range (t + 1 + 1), kernelWeight (t + 1) k (J + 1) * kernelF (t + 1) (J + 1) k =
      ∑ k ∈ range (t + 1 + 2), kernelWeight (t + 1 + 1) k J *
        (certR1 (t + 1 : ℕ) J k * certF ((t + 1 : ℕ) : ℚ) ((J : ℚ) + 1) k) := by
    rw [sum_range_succ _ (t + 1 + 1)]
    have h0 : certR1 (t + 1 : ℕ) J ((t + 1 + 1 : ℕ) : ℚ) = 0 := by simp [certR1]
    rw [h0, zero_mul, mul_zero, add_zero]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [kernelWeight_one (by lia) (by have := mem_range.mp hk; lia)]
    simp only [kernelF, certF, certR1]
    push_cast
    ring
  have h0' : ∑ k ∈ range (t + 1), kernelWeight t k (J + 1) * kernelF t (J + 1) k =
      ∑ k ∈ range (t + 1 + 2), kernelWeight (t + 1 + 1) k J *
        (certR0 (t + 1 : ℕ) J k * certF (((t + 1 : ℕ) : ℚ) - 1) ((J : ℚ) + 1) k) := by
    rw [sum_range_succ _ (t + 1 + 1), sum_range_succ _ (t + 1)]
    have e1 : certR0 (t + 1 : ℕ) J ((t + 1 + 1 : ℕ) : ℚ) = 0 := by simp [certR0]
    have e2 : certR0 (t + 1 : ℕ) J ((t + 1 : ℕ) : ℚ) = 0 := by simp [certR0]
    rw [e1, e2, zero_mul, mul_zero, add_zero, zero_mul, mul_zero, add_zero]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [show t + 1 + 1 = t + 2 by ring,
      kernelWeight_lower (by lia) (by have := mem_range.mp hk; lia)]
    simp only [kernelF, certF, certR0]
    push_cast
    ring
  simp only [kernelSum]
  rw [show t + 2 = t + 1 + 1 by ring, h2, h1, h0']
  have hexp : ∑ k ∈ range (t + 1 + 2), kernelWeight (t + 1 + 1) k J * certRho (t + 1 : ℕ) J k =
      2 * ((t + 1 : ℕ) + 1 : ℚ) * ∑ k ∈ range (t + 1 + 2), kernelWeight (t + 1 + 1) k J *
        kernelF (t + 1 + 1) J k -
      4 * (1 - 2 * ((t + 1 : ℕ) : ℚ)) * ∑ k ∈ range (t + 1 + 2), kernelWeight (t + 1 + 1) k J *
        (certR2 (t + 1 : ℕ) J k * certF ((t + 1 : ℕ) : ℚ) ((J : ℚ) + 2) k) +
      8 * (1 - 2 * ((t + 1 : ℕ) : ℚ)) * ∑ k ∈ range (t + 1 + 2), kernelWeight (t + 1 + 1) k J *
        (certR1 (t + 1 : ℕ) J k * certF ((t + 1 : ℕ) : ℚ) ((J : ℚ) + 1) k) +
      8 * (((t + 1 : ℕ) : ℚ) - 2) * ∑ k ∈ range (t + 1 + 2), kernelWeight (t + 1 + 1) k J *
        (certR0 (t + 1 : ℕ) J k * certF (((t + 1 : ℕ) : ℚ) - 1) ((J : ℚ) + 1) k) := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [certRho, kernelF, certF]
    push_cast
    ring
  rw [hexp] at hT
  push_cast at hT ⊢
  linear_combination (2 * (1 / 4 : ℚ) ^ (t + 1 + 1)) * hT

/-! ### The base rows `r = 2, 3` and the identity -/

theorem kernelMoment_one (J : ℕ) :
    kernelMoment (1 : ℕ) J = 1 / (2 * (J + 3)) - 1 / (J + 2) := by
  rw [kernelMoment_natCast, kernelPoly_one, mul_sub, map_sub, ← mul_assoc, mul_comm (X ^ J),
    mul_assoc, ← pow_add, integral_C_mul, ← pow_succ, integral_X_pow, integral_X_pow]
  simp only [invSucc, Algebra.algebraMap_self, RingHom.id_apply, one_pow,
    zero_pow (Nat.succ_ne_zero _), sub_zero, mul_one]
  push_cast
  field_simp
  ring

theorem kernelMoment_two (J : ℕ) :
    kernelMoment (2 : ℕ) J = (2 * kernelMoment (1 : ℕ) (J + 1) - kernelMoment (1 : ℕ) (J + 2) +
      kernelMoment (0 : ℕ) (J + 1) / 2) / 4 := by
  have h := kernelMoment_rec 0 J
  norm_num at h
  linarith

theorem kernelMoment_three (J : ℕ) :
    kernelMoment (3 : ℕ) J = kernelMoment (2 : ℕ) (J + 1) - kernelMoment (2 : ℕ) (J + 2) / 2 := by
  have h := kernelMoment_rec 1 J
  norm_num at h
  linarith

theorem kernelSum_two (J : ℕ) : kernelSum 2 J = -kernelMoment (2 : ℕ) J := by
  rw [kernelMoment_two, kernelMoment_one, kernelMoment_one, Nat.cast_zero, kernelMoment_zero]
  simp only [kernelSum, sum_range_succ, sum_range_zero, zero_add, kernelWeight, kernelF]
  norm_num [Nat.factorial_succ]
  have ha : ((2 * J).factorial : ℚ) ≠ 0 := by positivity
  have hb : (J.factorial : ℚ) ≠ 0 := by positivity
  generalize ((2 * J).factorial : ℚ) = a at *
  generalize (J.factorial : ℚ) = b at *
  field_simp
  ring

theorem kernelSum_three (J : ℕ) : kernelSum 3 J = -kernelMoment (3 : ℕ) J := by
  simp only [kernelMoment_three, kernelMoment_two, kernelMoment_one, Nat.cast_zero,
    kernelMoment_zero]
  simp only [kernelSum, sum_range_succ, sum_range_zero, zero_add, kernelWeight, kernelF]
  norm_num [Nat.factorial_succ]
  have ha : ((2 * J).factorial : ℚ) ≠ 0 := by positivity
  have hb : (J.factorial : ℚ) ≠ 0 := by positivity
  generalize ((2 * J).factorial : ℚ) = a at *
  generalize (J.factorial : ℚ) = b at *
  field_simp
  ring

/-- The `W`-sum formula (4.3): for `r ≥ 2` the moment `m(r, J)` is minus the explicit sum. -/
theorem kernelMoment_eq_neg_kernelSum {r : ℕ} (hr : 2 ≤ r) (J : ℕ) :
    kernelMoment r J = -kernelSum r J := by
  induction r using Nat.strong_induction_on generalizing J with
  | _ r ih =>
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 2 := ⟨r - 2, by lia⟩
  rcases Nat.lt_or_ge t 2 with ht | ht
  · obtain rfl | rfl : t = 0 ∨ t = 1 := by lia
    · have h := kernelSum_two J
      norm_num at h ⊢
      linarith
    · have h := kernelSum_three J
      norm_num at h ⊢
      linarith
  have hm := kernelMoment_rec t J
  rw [ih (t + 1) (by lia) (by lia) (J + 1), ih (t + 1) (by lia) (by lia) (J + 2),
    ih t (by lia) ht (J + 1)] at hm
  have hpos : (2 * (t : ℚ) + 4) ≠ 0 := by positivity
  apply mul_left_cancel₀ hpos
  linear_combination hm + kernelSum_rec ht J

end RealRooted.BigDescents321
