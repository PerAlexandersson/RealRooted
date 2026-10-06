import RealRooted.CombinatorialExamples.BigDescents321.GeneratingFunction
import RealRooted.CombinatorialExamples.BigDescents321.Kernel

/-!
# Gegenbauer coordinates of the transformed polynomials

We expand `Q_n = ∑_j q_(n,j) G_j` explicitly. For `j ≤ n` with `n - j = 2r`,

`q_(n,j) = (2j + 3)(c_r(j) - c_(r-1)(j)/2) + corr(r, j)`,

where `c_r(j) = -m(r, j)` are the kernel moments and the correction `corr` is nonzero only
for `r ≤ 2`. The proof checks the recurrence (1.9) coordinatewise: multiplication by `c`
acts on coordinates by `G_j ↦ ((j+1) G_(j+1) + (j+2) G_(j-1))/(2j + 3)`, and the kernel
moment identity reduces each coordinate equation to a finite identity.
-/

open Polynomial

noncomputable section

namespace RealRooted.BigDescents321

/-- `∑_(j ≤ N) φ_j G_j`. -/
def gsum (φ : ℕ → ℚ) (N : ℕ) : ℚ[X] := ∑ j ∈ Finset.range (N + 1), C (φ j) * gegen j

theorem gsum_succ (φ : ℕ → ℚ) (N : ℕ) :
    gsum φ (N + 1) = gsum φ N + C (φ (N + 1)) * gegen (N + 1) := by
  rw [gsum, Finset.sum_range_succ]; rfl

theorem gsum_eq_of_le {φ : ℕ → ℚ} {N : ℕ} (hφ : ∀ j, N < j → φ j = 0) {M : ℕ} (h : N ≤ M) :
    gsum φ M = gsum φ N := by
  induction M, h using Nat.le_induction with
  | base => rfl
  | succ M hNM ih => rw [gsum_succ, ih, hφ _ (by lia), map_zero, zero_mul, add_zero]

theorem gsum_add (φ ψ : ℕ → ℚ) (N : ℕ) : gsum (φ + ψ) N = gsum φ N + gsum ψ N := by
  simp only [gsum, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem gsum_smul (a : ℚ) (φ : ℕ → ℚ) (N : ℕ) : gsum (a • φ) N = C a * gsum φ N := by
  simp only [gsum, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem gsum_congr {φ ψ : ℕ → ℚ} {N : ℕ} (h : ∀ j ≤ N, φ j = ψ j) : gsum φ N = gsum ψ N :=
  Finset.sum_congr rfl fun j hj ↦ by rw [h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]

theorem X_mul_gegen_zero : X * gegen 0 = C (1 / 3) * gegen 1 := by
  rw [gegen_zero, gegen_one, ← mul_assoc, show (3 : ℚ[X]) = C 3 from (map_ofNat C 3).symm,
    ← C_mul]
  norm_num

theorem X_mul_gegen_succ (j : ℕ) :
    X * gegen (j + 1) = C (((j : ℚ) + 2) / (2 * j + 5)) * gegen (j + 2) +
      C (((j : ℚ) + 3) / (2 * j + 5)) * gegen j := by
  have h := gegen_rec j
  have hpos : (0 : ℚ) < 2 * j + 5 := by positivity
  have hc : (2 * (j : ℚ[X]) + 5) = C ((2 * j + 5 : ℚ)) := by
    rw [map_add, map_mul, map_natCast, map_ofNat C, map_ofNat C]
  have e1 : (2 * (j : ℚ[X]) + 5) * C (((j : ℚ) + 2) / (2 * j + 5)) = (j : ℚ[X]) + 2 := by
    rw [hc, ← C_mul, mul_div_cancel₀ _ hpos.ne', map_add, map_natCast, map_ofNat C]
  have e2 : (2 * (j : ℚ[X]) + 5) * C (((j : ℚ) + 3) / (2 * j + 5)) = (j : ℚ[X]) + 3 := by
    rw [hc, ← C_mul, mul_div_cancel₀ _ hpos.ne', map_add, map_natCast, map_ofNat C]
  apply mul_left_cancel₀ (show (2 * (j : ℚ[X]) + 5) ≠ 0 by rw [hc]; exact C_ne_zero.mpr hpos.ne')
  linear_combination -h - gegen (j + 2) * e1 - gegen j * e2

/-- Multiplication by `c` on Gegenbauer coordinates:
`(c φ)_i = φ_(i-1) i/(2i + 1) + φ_(i+1) (i + 3)/(2i + 5)`. -/
def xShift (φ : ℕ → ℚ) (i : ℕ) : ℚ :=
  (if i = 0 then 0 else φ (i - 1) * i / (2 * i + 1)) + φ (i + 1) * (i + 3) / (2 * i + 5)

/-- `xShift` with the second term cut off above `N`. -/
private def xShiftTrunc (φ : ℕ → ℚ) (N i : ℕ) : ℚ :=
  (if i = 0 then 0 else φ (i - 1) * i / (2 * i + 1)) +
    (if i + 1 ≤ N then φ (i + 1) * (i + 3) / (2 * i + 5) else 0)

theorem gsum_single (N k : ℕ) (hk : k ≤ N) (a : ℚ) :
    gsum (fun i ↦ if i = k then a else 0) N = C a * gegen k := by
  rw [gsum, Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) h

private theorem X_mul_gsum_trunc (φ : ℕ → ℚ) (N : ℕ) :
    X * gsum φ N = gsum (xShiftTrunc φ N) (N + 1) := by
  induction N with
  | zero =>
    simp only [gsum, zero_add, Finset.sum_range_succ, Finset.sum_range_zero, xShiftTrunc,
      gegen_zero, gegen_one]
    norm_num
    rw [show (3 : ℚ[X]) = C 3 from (map_ofNat C 3).symm, ← mul_assoc, ← C_mul,
      div_mul_cancel₀ _ (by norm_num : (3 : ℚ) ≠ 0)]
  | succ N ih =>
    rw [gsum_succ, mul_add, ih, mul_left_comm, X_mul_gegen_succ,
      gsum_succ (xShiftTrunc φ (N + 1)) (N + 1)]
    have h1 : gsum (xShiftTrunc φ (N + 1)) (N + 1) = gsum (xShiftTrunc φ N) (N + 1) +
        gsum (fun i ↦ if i = N then φ (N + 1) * (N + 3) / (2 * N + 5) else 0) (N + 1) := by
      rw [← gsum_add]
      refine gsum_congr fun i hi ↦ ?_
      simp only [xShiftTrunc, Pi.add_apply]
      by_cases hiN : i = N
      · subst hiN; simp
      · have : (i + 1 ≤ N + 1 ↔ i + 1 ≤ N) := by lia
        simp [hiN, this]
    rw [h1, gsum_single (N + 1) N (by lia)]
    simp only [xShiftTrunc, show N + 1 + 1 ≠ 0 by lia, ↓reduceIte, Nat.add_sub_cancel,
      show ¬ (N + 1 + 1 + 1 ≤ N + 1) by lia, add_zero]
    push_cast
    simp only [mul_add, ← mul_assoc, ← C_mul]
    ring_nf

theorem X_mul_gsum {φ : ℕ → ℚ} {N : ℕ} (hφ : ∀ j, N < j → φ j = 0) :
    X * gsum φ N = gsum (xShift φ) (N + 1) := by
  rw [X_mul_gsum_trunc]
  refine gsum_congr fun i _ ↦ ?_
  simp only [xShiftTrunc, xShift]
  by_cases h : i + 1 ≤ N
  · simp [h]
  · simp [h, hφ (i + 1) (by lia)]

/-! ### The coordinates -/

/-- The corrections to the kernel formula in the top three diagonals. -/
def corrCoord : ℕ → ℕ → ℚ
  | 0, J => 2 / (2 * J + 1) + 2
  | 1, J => -(2 / (2 * J + 5)) - 2
  | 2, _ => 1 / 2
  | _, _ => 0

/-- `e(r, J) = -(2J + 3)(m(r, J) - m(r - 1, J)/2) + corr(r, J)`, and `0` for `r < 0`. -/
def kernelCoord (r : ℤ) (J : ℕ) : ℚ :=
  if r < 0 then 0 else
    -(2 * J + 3) * (kernelMoment r J - kernelMoment (r - 1) J / 2) + corrCoord r.toNat J

/-- The Gegenbauer coordinates `q_(n,j)` of `Q_n`. -/
def transformedCoord (n j : ℕ) : ℚ :=
  if j ≤ n ∧ Even (n - j) then kernelCoord ((n - j) / 2 : ℕ) j else 0

theorem transformedCoord_of_lt {n j : ℕ} (h : n < j) : transformedCoord n j = 0 := by
  simp [transformedCoord, show ¬ j ≤ n by lia]

/-- The Gegenbauer coordinates of `((c² - 1)/(n(n + 1))) G_(n-1)`. -/
def extraCoord (n i : ℕ) : ℚ :=
  if i = n + 1 then 1 / ((2 * n + 1) * (2 * n + 3))
  else if i + 1 = n then
    (((n + 1) * (n - 1)) / ((2 * n + 1) * (2 * n - 1)) + n * (n + 2) / ((2 * n + 1) * (2 * n + 3))
      - 1) / (n * (n + 1))
  else if i + 3 = n then 1 / ((2 * n + 1) * (2 * n - 1))
  else 0

theorem refHom_eq_C_mul (k : ℕ) :
    refHom k = C ((2 : ℚ) / ((k + 1) * (k + 2))) * gegen k := by
  have h := refHom_eq k
  have hk : ((k : ℚ) + 1) * (k + 2) ≠ 0 := by positivity
  have hc : ((k + 1) * (k + 2) : ℚ[X]) = C (((k : ℚ) + 1) * (k + 2)) := by
    rw [map_mul, map_add, map_add, map_natCast, map_one, map_ofNat C]
  rw [hc] at h
  rw [show (2 : ℚ[X]) = C 2 from (map_ofNat C 2).symm] at h
  apply mul_left_cancel₀ (C_ne_zero.mpr hk)
  rw [h, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ hk]

private theorem gsum_three (n a b c : ℕ) (hab : b < a) (hbc : c < b) (han : a ≤ n)
    (φ : ℕ → ℚ) (hφ : ∀ i, i ≠ a → i ≠ b → i ≠ c → φ i = 0) :
    gsum φ n = C (φ a) * gegen a + C (φ b) * gegen b + C (φ c) * gegen c := by
  have : φ = (fun i ↦ if i = a then φ a else 0) + (fun i ↦ if i = b then φ b else 0) +
      (fun i ↦ if i = c then φ c else 0) := by
    funext i
    simp only [Pi.add_apply]
    by_cases ha : i = a
    · subst ha; simp [show i ≠ b by lia, show i ≠ c by lia]
    by_cases hb : i = b
    · subst hb; simp [ha, show i ≠ c by lia]
    by_cases hc : i = c
    · subst hc; simp [ha, hb]
    simp [ha, hb, hc, hφ i ha hb hc]
  have h2 := congrArg (gsum · n) this
  rw [h2, gsum_add, gsum_add, gsum_single _ _ han, gsum_single _ _ (by lia),
    gsum_single _ _ (by lia)]

/-- `((c² - 1)/2) μ_(m+2) = ∑ extraCoord_(m+3)(i) G_i`. -/
theorem extra_eq_gsum (m : ℕ) :
    C (1 / 2) * (X ^ 2 - 1) * refHom (m + 2) = gsum (extraCoord (m + 3)) (m + 4) := by
  rw [gsum_three (m + 4) (m + 4) (m + 2) m (by lia) (by lia) le_rfl]
  swap
  · intro i ha hb hc
    simp only [extraCoord, show ¬ (i = m + 3 + 1) by lia, show ¬ (i + 1 = m + 3) by lia,
      show ¬ (i + 3 = m + 3) by lia, ↓reduceIte]
  have hX1 : X * gegen (m + 2) = C (((m + 1 : ℕ) + 2 : ℚ) / (2 * (m + 1 : ℕ) + 5)) *
      gegen (m + 3) + C (((m + 1 : ℕ) + 3 : ℚ) / (2 * (m + 1 : ℕ) + 5)) * gegen (m + 1) :=
    X_mul_gegen_succ (m + 1)
  have hX2 : X * gegen (m + 3) = C (((m + 2 : ℕ) + 2 : ℚ) / (2 * (m + 2 : ℕ) + 5)) *
      gegen (m + 4) + C (((m + 2 : ℕ) + 3 : ℚ) / (2 * (m + 2 : ℕ) + 5)) * gegen (m + 2) :=
    X_mul_gegen_succ (m + 2)
  have hX0 := X_mul_gegen_succ m
  have ex1 : extraCoord (m + 3) (m + 4) = 1 / ((2 * (m + 3 : ℕ) + 1) * (2 * (m + 3 : ℕ) + 3)) := by
    simp [extraCoord]
  have ex2 : extraCoord (m + 3) (m + 2) = ((((m + 3 : ℕ) : ℚ) + 1) * ((m + 3 : ℕ) - 1) /
      ((2 * (m + 3 : ℕ) + 1) * (2 * (m + 3 : ℕ) - 1)) + (m + 3 : ℕ) * ((m + 3 : ℕ) + 2) /
      ((2 * (m + 3 : ℕ) + 1) * (2 * (m + 3 : ℕ) + 3)) - 1) / ((m + 3 : ℕ) * ((m + 3 : ℕ) + 1)) := by
    simp [extraCoord]
  have ex3 : extraCoord (m + 3) m = 1 / ((2 * (m + 3 : ℕ) + 1) * (2 * (m + 3 : ℕ) - 1)) := by
    simp [extraCoord, show m ≠ m + 3 + 1 by lia]
  rw [ex1, ex2, ex3, refHom_eq_C_mul]
  push_cast at hX1 hX2 hX0 ⊢
  set a1 : ℚ := ((m : ℚ) + 1 + 2) / (2 * (m + 1) + 5)
  set b1 : ℚ := ((m : ℚ) + 1 + 3) / (2 * (m + 1) + 5)
  set a2 : ℚ := ((m : ℚ) + 2 + 2) / (2 * (m + 2) + 5)
  set b2 : ℚ := ((m : ℚ) + 2 + 3) / (2 * (m + 2) + 5)
  set a0 : ℚ := ((m : ℚ) + 2) / (2 * m + 5)
  set b0 : ℚ := ((m : ℚ) + 3) / (2 * m + 5)
  have hm5 : (2 * (m : ℚ) + 5) ≠ 0 := by positivity
  have hm7 : (2 * ((m : ℚ) + 1) + 5) ≠ 0 := by positivity
  have hm9 : (2 * ((m : ℚ) + 2) + 5) ≠ 0 := by positivity
  have hmm : ((m : ℚ) + 2 + 1) * ((m : ℚ) + 2 + 2) ≠ 0 := by positivity
  have s4 : C (1 / 2 : ℚ) * C (2 / (((m : ℚ) + 2 + 1) * ((m : ℚ) + 2 + 2))) * C a1 * C a2 =
      C (1 / ((2 * ((m : ℚ) + 3) + 1) * (2 * ((m : ℚ) + 3) + 3))) := by
    simp only [← C_mul]
    congr 1
    simp only [a1, a2]
    field_simp
    ring
  have s2 : C (1 / 2 : ℚ) * C (2 / (((m : ℚ) + 2 + 1) * ((m : ℚ) + 2 + 2))) *
      (C a1 * C b2 + C b1 * C a0 - 1) =
      C ((((m : ℚ) + 3 + 1) * ((m : ℚ) + 3 - 1) / ((2 * ((m : ℚ) + 3) + 1) *
        (2 * ((m : ℚ) + 3) - 1)) + ((m : ℚ) + 3) * ((m : ℚ) + 3 + 2) /
        ((2 * ((m : ℚ) + 3) + 1) * (2 * ((m : ℚ) + 3) + 3)) - 1) /
        (((m : ℚ) + 3) * ((m : ℚ) + 3 + 1))) := by
    rw [← map_one C]
    simp only [← C_mul, ← C_add, ← C_sub]
    congr 1
    simp only [a1, b2, b1, a0]
    have h1 : (2 * ((m : ℚ) + 3) - 1) ≠ 0 := by
      intro h; linarith [(m.cast_nonneg : (0 : ℚ) ≤ m)]
    field_simp
    ring
  have s0 : C (1 / 2 : ℚ) * C (2 / (((m : ℚ) + 2 + 1) * ((m : ℚ) + 2 + 2))) * C b1 * C b0 =
      C (1 / ((2 * ((m : ℚ) + 3) + 1) * (2 * ((m : ℚ) + 3) - 1))) := by
    simp only [← C_mul]
    congr 1
    simp only [b1, b0]
    have h1 : (2 * ((m : ℚ) + 3) - 1) ≠ 0 := by
      intro h; linarith [(m.cast_nonneg : (0 : ℚ) ≤ m)]
    field_simp
    ring
  set κ : ℚ[X] := C (2 / (((m : ℚ) + 2 + 1) * ((m : ℚ) + 2 + 2)))
  linear_combination (C (1 / 2 : ℚ) * κ * X) * hX1 + (C (1 / 2 : ℚ) * κ * C a1) * hX2 +
    (C (1 / 2 : ℚ) * κ * C b1) * hX0 + gegen (m + 4) * s4 + gegen (m + 2) * s2 + gegen m * s0

/-! ### The coordinate recurrence -/

/-- The correction for `r : ℤ`, zero for `r < 0`. -/
def corrCoordZ (r : ℤ) (J : ℕ) : ℚ := if r < 0 then 0 else corrCoord r.toNat J

theorem corrCoordZ_of_three_le {r : ℤ} (h : 3 ≤ r) (J : ℕ) : corrCoordZ r J = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = k + 3 := ⟨(r - 3).toNat, by lia⟩
  simp only [corrCoordZ, show ¬ ((k : ℤ) + 3 < 0) by lia, ↓reduceIte,
    show ((k : ℤ) + 3).toNat = k + 3 by lia, corrCoord]

theorem kernelCoord_eq (r : ℤ) (J : ℕ) :
    kernelCoord r J = -(2 * J + 3) * (kernelMoment r J - kernelMoment (r - 1) J / 2) +
      corrCoordZ r J := by
  unfold kernelCoord corrCoordZ
  split_ifs with h
  · simp [kernelMoment_of_neg h, kernelMoment_of_neg (show r - 1 < 0 by lia)]
  · rfl

theorem kernelK_eval_one (t : ℕ) : (kernelK t).eval 1 =
    if t = 0 then 1 else if t = 1 then -2 else if t = 2 then 3 / 2 else if t = 3 then -1 / 2
    else if t = 4 then 1 / 16 else 0 := by
  rw [eval_one_kernelK, halfQ_pow_four]
  simp only [map_add, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X, show (2 : PowerSeries ℚ) = PowerSeries.C 2
      from (map_ofNat _ 2).symm]
  rcases t with _ | _ | _ | _ | _ | t <;> norm_num

/-- The coordinate recurrence at `i = j + 1`, with `n = j + 2t`. -/
theorem kernelCoord_rec_succ (t j : ℕ) :
    kernelCoord t j * ((j + 1 : ℕ) : ℚ) / (2 * ((j + 1 : ℕ) : ℚ) + 1) +
      kernelCoord ((t : ℤ) - 1) (j + 2) * (((j + 1 : ℕ) : ℚ) + 3) / (2 * ((j + 1 : ℕ) : ℚ) + 5) =
      kernelCoord ((t : ℤ) - 1) (j + 1) - kernelCoord ((t : ℤ) - 2) (j + 1) / 8 +
        extraCoord (j + 2 * t) (j + 1) := by
  have hid := kernelMoment_identity t j
  rw [kernelK_eval_one] at hid
  have h1 : (2 * (j : ℚ) + 1) ≠ 0 := by positivity
  have h3 : (2 * (j : ℚ) + 3) ≠ 0 := by positivity
  have h5 : (2 * (j : ℚ) + 5) ≠ 0 := by positivity
  have h7 : (2 * (j : ℚ) + 7) ≠ 0 := by positivity
  have h9 : (2 * (j : ℚ) + 9) ≠ 0 := by positivity
  have h11 : (2 * (j : ℚ) + 11) ≠ 0 := by positivity
  have hj1 : ((j : ℚ) + 1) ≠ 0 := by positivity
  have hj2 : ((j : ℚ) + 2) ≠ 0 := by positivity
  have hj3 : ((j : ℚ) + 3) ≠ 0 := by positivity
  have hj4 : ((j : ℚ) + 4) ≠ 0 := by positivity
  have hj5 : ((j : ℚ) + 5) ≠ 0 := by positivity
  have hs2 : (2 * ((j : ℚ) + 2) - 1) ≠ 0 := by
    intro h; linarith [(j.cast_nonneg : (0 : ℚ) ≤ j)]
  have hs4 : (2 * ((j : ℚ) + 4) - 1) ≠ 0 := by
    intro h; linarith [(j.cast_nonneg : (0 : ℚ) ≤ j)]
  simp only [kernelCoord_eq]
  rw [show (t : ℤ) - 1 - 1 = t - 2 by ring, show (t : ℤ) - 2 - 1 = t - 3 by ring]
  rcases t with _ | _ | _ | _ | _ | t
  · simp only [corrCoordZ, extraCoord, corrCoord] at hid ⊢
    norm_num at hid ⊢
    linear_combination (norm := skip) (-1 / 16 : ℚ) * hid
    field_simp
    ring
  · simp only [corrCoordZ, extraCoord, corrCoord, show ¬ (j + 1 = j + 2 * (1 : ℕ) + 1) by lia,
      show j + 1 + 1 = j + 2 * (1 : ℕ) by lia, ↓reduceIte] at hid ⊢
    norm_num at hid ⊢
    linear_combination (norm := skip) (-1 / 16 : ℚ) * hid
    field_simp
    ring
  · simp only [corrCoordZ, extraCoord, corrCoord, show ¬ (j + 1 = j + 2 * (2 : ℕ) + 1) by lia,
      show ¬ (j + 1 + 1 = j + 2 * (2 : ℕ)) by lia, show j + 1 + 3 = j + 2 * (2 : ℕ) by lia,
      ↓reduceIte] at hid ⊢
    norm_num at hid ⊢
    linear_combination (norm := skip) (-1 / 16 : ℚ) * hid
    field_simp
    ring
  · simp only [corrCoordZ, extraCoord, corrCoord, show ¬ (j + 1 = j + 2 * (3 : ℕ) + 1) by lia,
      show ¬ (j + 1 + 1 = j + 2 * (3 : ℕ)) by lia, show ¬ (j + 1 + 3 = j + 2 * (3 : ℕ)) by lia,
      ↓reduceIte] at hid ⊢
    norm_num at hid ⊢
    linear_combination (norm := skip) (-1 / 16 : ℚ) * hid
    field_simp
    ring
  · simp only [corrCoordZ, extraCoord, corrCoord, show ¬ (j + 1 = j + 2 * (4 : ℕ) + 1) by lia,
      show ¬ (j + 1 + 1 = j + 2 * (4 : ℕ)) by lia, show ¬ (j + 1 + 3 = j + 2 * (4 : ℕ)) by lia,
      ↓reduceIte] at hid ⊢
    norm_num at hid ⊢
    linear_combination (norm := skip) (-1 / 16 : ℚ) * hid
    field_simp
    ring
  · simp (disch := lia) only [corrCoordZ_of_three_le]
    simp only [extraCoord, show ¬ (j + 1 = j + 2 * (t + 5) + 1) by lia,
      show ¬ (j + 1 + 1 = j + 2 * (t + 5)) by lia, show ¬ (j + 1 + 3 = j + 2 * (t + 5)) by lia,
      ↓reduceIte] at hid ⊢
    norm_num at hid ⊢
    ring_nf at hid ⊢
    linear_combination (norm := skip) (-1 / 16 : ℚ) * hid
    field_simp
    ring

theorem eval_zero_kernelK_add_two (s : ℕ) : (kernelK (s + 2)).eval 0 = 0 := by
  rw [eval_zero_kernelK, halfQ]
  simp

/-- The coordinate recurrence at `i = 0`, with `n = 2s + 3`. -/
theorem kernelCoord_rec_zero (s : ℕ) :
    kernelCoord ((s : ℤ) + 1) 1 * 3 / 5 =
      kernelCoord ((s : ℤ) + 1) 0 - kernelCoord s 0 / 8 + extraCoord (2 * s + 3) 0 := by
  have hid := kernelMoment_identity_zero (s + 2)
  rw [kernelK_eval_one, eval_zero_kernelK_add_two] at hid
  simp only [kernelCoord_eq]
  push_cast at hid
  rw [show (s : ℤ) + 2 - 1 = s + 1 by ring, show (s : ℤ) + 2 - 2 = s by ring,
    show (s : ℤ) + 2 - 3 = s - 1 by ring] at hid
  rw [show (s : ℤ) + 1 - 1 = s by ring]
  rcases s with _ | _ | _ | s
  · simp only [corrCoordZ, extraCoord, corrCoord] at hid ⊢
    norm_num at hid ⊢
    linear_combination (norm := skip) (-1 / 16 : ℚ) * hid
    norm_num
    ring
  · simp only [corrCoordZ, extraCoord, corrCoord] at hid ⊢
    norm_num at hid ⊢
    linear_combination (norm := skip) (-1 / 16 : ℚ) * hid
    norm_num
    ring
  · simp only [corrCoordZ, extraCoord, corrCoord] at hid ⊢
    norm_num at hid ⊢
    linear_combination (norm := skip) (-1 / 16 : ℚ) * hid
    norm_num
    ring
  · simp (disch := lia) only [corrCoordZ_of_three_le]
    simp only [extraCoord] at hid ⊢
    norm_num at hid ⊢
    ring_nf at hid ⊢
    linear_combination (norm := skip) (-1 / 16 : ℚ) * hid
    ring

theorem transformedCoord_eq {n j : ℕ} {r : ℤ} (h : (n : ℤ) = j + 2 * r) :
    transformedCoord n j = kernelCoord r j := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [transformedCoord_of_lt (by lia)]
    simp [kernelCoord, hr]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = k := ⟨r.toNat, by lia⟩
    have hn : n = j + 2 * k := by lia
    simp only [transformedCoord, show j ≤ n by lia, show n - j = 2 * k by lia, even_two_mul,
      and_self, ↓reduceIte, show 2 * k / 2 = k by lia]

theorem transformedCoord_of_odd {n j : ℕ} {r : ℤ} (h : (n : ℤ) = j + 2 * r + 1) :
    transformedCoord n j = 0 := by
  unfold transformedCoord
  split_ifs with hc
  · obtain ⟨hjn, k, hk⟩ := hc
    lia
  · rfl

/-- Coordinatewise form of the recurrence (1.9). -/
theorem xShift_transformedCoord (m i : ℕ) :
    xShift (transformedCoord (m + 3)) i =
      transformedCoord (m + 2) i - transformedCoord m i / 8 + extraCoord (m + 3) i := by
  rcases lt_or_ge (m + 4) i with hi | hi
  · simp only [xShift, transformedCoord_of_lt (show m + 3 < i - 1 by lia),
      transformedCoord_of_lt (show m + 3 < i + 1 by lia), transformedCoord_of_lt
      (show m + 2 < i by lia), transformedCoord_of_lt (show m < i by lia), extraCoord,
      show ¬ (i = m + 3 + 1) by lia, show ¬ (i + 1 = m + 3) by lia,
      show ¬ (i + 3 = m + 3) by lia, ↓reduceIte]
    simp
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (m + 4 - i)
  · rcases Nat.eq_zero_or_pos i with rfl | hipos
    · obtain ⟨s, rfl⟩ : ∃ s, k = s + 2 := ⟨k - 2, by lia⟩
      have hm : m = 2 * s := by lia
      subst hm
      have h := kernelCoord_rec_zero s
      rw [transformedCoord_eq (r := (s : ℤ) + 1) (by push_cast; ring),
        transformedCoord_eq (n := 2 * s) (r := s) (by push_cast; ring),
        show 2 * s + 3 = 2 * s + 3 from rfl] at *
      simp only [xShift, ↓reduceIte, zero_add, CharP.cast_eq_zero, mul_zero]
      rw [transformedCoord_eq (n := 2 * s + 3) (r := (s : ℤ) + 1) (by push_cast; ring)]
      linarith
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by lia⟩
      have h := kernelCoord_rec_succ k j
      have hn : m + 3 = j + 2 * k := by lia
      simp only [xShift, show j + 1 ≠ 0 by lia, ↓reduceIte, Nat.add_sub_cancel]
      rw [transformedCoord_eq (r := k) (by push_cast; lia),
        transformedCoord_eq (n := m + 3) (j := j + 1 + 1) (r := (k : ℤ) - 1) (by push_cast; lia),
        transformedCoord_eq (n := m + 2) (r := (k : ℤ) - 1) (by push_cast; lia),
        transformedCoord_eq (n := m) (r := (k : ℤ) - 2) (by push_cast; lia), hn,
        show j + 1 + 1 = j + 2 by ring]
      push_cast at h ⊢
      linarith
  · have h1 := (show m + 4 - i = 2 * k + 1 from hk)
    simp only [xShift]
    rw [transformedCoord_of_odd (n := m + 3) (j := i + 1) (r := (k : ℤ) - 1) (by push_cast; lia),
      transformedCoord_of_odd (n := m + 2) (r := (k : ℤ) - 1) (by push_cast; lia),
      transformedCoord_of_odd (n := m) (r := (k : ℤ) - 2) (by lia)]
    have hext : extraCoord (m + 3) i = 0 := by
      simp only [extraCoord, show ¬ (i = m + 3 + 1) by lia, show ¬ (i + 1 = m + 3) by lia,
        show ¬ (i + 3 = m + 3) by lia, ↓reduceIte]
    rw [hext]
    split_ifs with h0
    · simp
    · rw [transformedCoord_of_odd (n := m + 3) (j := i - 1) (r := (k : ℤ)) (by push_cast; lia)]
      simp

theorem kernelMoment_one_zero : kernelMoment 1 0 = -1 / 3 := by
  simp only [kernelMoment, kernelPolyZ, show ¬ ((1 : ℤ) < 0) by norm_num, ↓reduceIte,
    show (1 : ℤ).toNat = 1 by rfl, kernelPoly_one, pow_zero, one_mul, map_sub,
    integral_C_mul, integral_X_pow, invSucc]
  rw [← pow_one (X : ℚ[X]), integral_X_pow]
  simp [invSucc]
  norm_num

theorem transformed_one : transformed 1 = C (1 / 2) * X := by
  simp [transformed_succ, firstReturnHom]

theorem transformed_two : transformed 2 = C (1 / 2) * X ^ 2 := by
  simp only [transformed_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    firstReturnHom, Nat.sub_zero, Nat.sub_self, transformed_zero, mul_one]
  have h : (C (1 / 2 : ℚ)) * C (1 / 2) + C (1 / 4) = C (1 / 2) := by
    rw [← C_mul, ← C_add]; norm_num
  linear_combination X ^ 2 * h

/-- The Gegenbauer expansion `Q_n = ∑_(j ≤ n) q_(n,j) G_j`. -/
theorem transformed_eq_gsum (n : ℕ) : transformed n = gsum (transformedCoord n) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      simp only [gsum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, transformed_zero,
        gegen_zero, mul_one]
      rw [transformedCoord_eq (n := 0) (j := 0) (r := 0) (by norm_num)]
      simp only [kernelCoord, kernelMoment_zero, corrCoord, show ¬ ((0 : ℤ) < 0) by norm_num,
        ↓reduceIte, kernelMoment_of_neg (show (0 : ℤ) - 1 < 0 by norm_num), Int.toNat_zero]
      norm_num
    | 1, _ =>
      simp only [gsum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        transformed_one, gegen_zero, gegen_one]
      rw [transformedCoord_of_odd (n := 1) (j := 0) (r := 0) (by norm_num),
        transformedCoord_eq (n := 1) (j := 1) (r := 0) (by norm_num)]
      simp only [kernelCoord, kernelMoment_zero, corrCoord, show ¬ ((0 : ℤ) < 0) by norm_num,
        ↓reduceIte, kernelMoment_of_neg (show (0 : ℤ) - 1 < 0 by norm_num), Int.toNat_zero]
      norm_num
      rw [show (3 : ℚ[X]) = C 3 from (map_ofNat C 3).symm, ← mul_assoc, ← C_mul]
      norm_num
    | 2, _ =>
      simp only [gsum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, transformed_two]
      rw [transformedCoord_eq (n := 2) (j := 0) (r := 1) (by norm_num),
        transformedCoord_of_odd (n := 2) (j := 1) (r := 0) (by norm_num),
        transformedCoord_eq (n := 2) (j := 2) (r := 0) (by norm_num)]
      simp only [kernelCoord, kernelMoment_zero, kernelMoment_one_zero, corrCoord,
        show ¬ ((0 : ℤ) < 0) by norm_num, show ¬ ((1 : ℤ) < 0) by norm_num, ↓reduceIte,
        kernelMoment_of_neg (show (0 : ℤ) - 1 < 0 by norm_num), Int.toNat_zero,
        show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ).toNat = 1 by rfl]
      have hg := gegen_rec 0
      apply Polynomial.funext
      intro x
      have h := congrArg (eval x) hg
      simp only [gegen_zero, eval_mul, eval_sub, eval_add, eval_X, eval_ofNat, eval_one,
        CharP.cast_eq_zero] at h
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, gegen_zero, gegen_one, eval_one,
        map_zero, zero_mul, add_zero]
      norm_num at h ⊢
      linear_combination (-1 / 30 : ℚ) * h
    | m + 3, ih =>
      have h19 := X_mul_transformed_add_three m
      rw [ih (m + 2) (by lia), ih m (by lia), extra_eq_gsum m] at h19
      apply mul_left_cancel₀ (X_ne_zero : (X : ℚ[X]) ≠ 0)
      rw [h19, X_mul_gsum (φ := transformedCoord (m + 3)) fun j hj ↦ transformedCoord_of_lt hj,
        ← gsum_eq_of_le (φ := transformedCoord (m + 2)) (fun j hj ↦ transformedCoord_of_lt hj)
          (show m + 2 ≤ m + 4 by lia),
        ← gsum_eq_of_le (φ := transformedCoord m) (fun j hj ↦ transformedCoord_of_lt hj)
          (show m ≤ m + 4 by lia)]
      have hpt : xShift (transformedCoord (m + 3)) = transformedCoord (m + 2) +
          (-1 / 8 : ℚ) • transformedCoord m + extraCoord (m + 3) := by
        funext i
        rw [xShift_transformedCoord]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [show m + 3 + 1 = m + 4 by ring, hpt, gsum_add, gsum_add, gsum_smul]
      rw [show (C (1 / 8 : ℚ)) = -C (-1 / 8) by rw [← map_neg]; norm_num]
      ring

end RealRooted.BigDescents321
