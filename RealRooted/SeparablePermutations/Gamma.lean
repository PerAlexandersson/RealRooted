import RealRooted.SeparablePermutations.Basic
import RealRooted.FactorialCompression.Basic
import RealRooted.GammaTransform.Basic

/-!
# Gamma-polynomials and descent polynomials of separable permutations

Zhang (SSRN 7510941, Proposition 3.3) represents the gamma-polynomial of the descent
enumerator of the separable permutations of `[n]` (those avoiding `2413` and `3142`) as a
factorial compression of the auxiliary polynomial `B_{n-2}`:
`Γ_{N+2} = (2 ^ N / N!) * compression N 1 B_N`.
Here `gammaPolynomial` is *defined* by this representation, and `descentPolynomial n` is the
gamma transform `(1 + t) ^ (n - 1) Γ_n (t / (1 + t) ^ 2)` of `Γ_n`.

These are algebraically defined families.  That `descentPolynomial n` is the descent
enumerator of `Av_n(2413, 3142)` is the combinatorial identity of Fu--Lin--Zeng combined with
Zhang's Proposition 3.3; it is not proved here (see
`RealRooted/SeparablePermutations/Enumerator.lean` for the precise conditional statement and
the finite checks).  We prove degrees, nonnegativity, positivity of the relevant coefficients,
and the first values.
-/

open Polynomial

noncomputable section

namespace RealRooted.SeparablePermutations

open FactorialCompression

/-- Zhang's representation of the gamma-polynomial `Γ_n` of the descent enumerator of the
separable permutations of `[n]` (SSRN 7510941, Proposition 3.3): `Γ_0 = 0`, `Γ_1 = 1`, and
`Γ_{N+2} = (2 ^ N / N!) * compression N 1 B_N`. -/
def gammaPolynomial : ℕ → ℝ[X]
  | 0 => 0
  | 1 => 1
  | N + 2 => C ((2 : ℝ) ^ N / (N.factorial : ℝ)) * compression N 1 (auxPolynomial N)

@[simp] theorem gammaPolynomial_zero : gammaPolynomial 0 = 0 := rfl

@[simp] theorem gammaPolynomial_one : gammaPolynomial 1 = 1 := rfl

theorem gammaPolynomial_add_two (N : ℕ) :
    gammaPolynomial (N + 2) =
      C ((2 : ℝ) ^ N / (N.factorial : ℝ)) * compression N 1 (auxPolynomial N) := rfl

/-- The descent polynomial `S_n = (1 + t) ^ (n - 1) Γ_n (t / (1 + t) ^ 2)` attached to the
gamma-polynomial `Γ_n` (Zhang, SSRN 7510941).  The identification with the descent enumerator
of the separable permutations is a separate, combinatorial statement. -/
def descentPolynomial (n : ℕ) : ℝ[X] :=
  RealRooted.gammaTransform (n - 1) (gammaPolynomial n)

/-! ### Coefficients and degree of `Γ_n` -/

/-- The coefficients of `Γ_{N+2}`. -/
theorem coeff_gammaPolynomial_add_two (N k : ℕ) :
    (gammaPolynomial (N + 2)).coeff k =
      if 2 * k ≤ N + 1 then
        (2 : ℝ) ^ N / (N.factorial : ℝ) *
          (((N - k).factorial : ℝ) / ((N + 1 - 2 * k).factorial : ℝ) *
            (auxPolynomial N).coeff k)
      else 0 := by
  rw [gammaPolynomial_add_two, coeff_C_mul, coeff_compression]
  by_cases h : 2 * k ≤ N + 1
  · rw [ite_eq_left h, ite_eq_left (by lia), multiplier, ite_eq_left (by lia)]
  · rw [ite_eq_right h]
    by_cases hk : k ≤ N
    · rw [ite_eq_left hk, multiplier, ite_eq_right (by lia)]
      simp
    · rw [ite_eq_right hk]
      simp

/-- The coefficients of `Γ_{N+2}` of index `k` with `2 k ≤ N + 1` are positive. -/
theorem coeff_gammaPolynomial_add_two_pos {N k : ℕ} (hk : 2 * k ≤ N + 1) :
    0 < (gammaPolynomial (N + 2)).coeff k := by
  rw [coeff_gammaPolynomial_add_two, ite_eq_left hk]
  have := coeff_auxPolynomial_pos (N := N) (k := k) (by lia)
  positivity

/-- The coefficients of `Γ_{N+2}` of index `k` with `N + 1 < 2 k` vanish. -/
theorem coeff_gammaPolynomial_add_two_eq_zero {N k : ℕ} (hk : N + 1 < 2 * k) :
    (gammaPolynomial (N + 2)).coeff k = 0 := by
  rw [coeff_gammaPolynomial_add_two, ite_eq_right (by lia)]

/-- All coefficients of `Γ_n` are nonnegative. -/
theorem hasNonnegCoeffs_gammaPolynomial (n : ℕ) :
    RealRooted.HasNonnegCoeffs (gammaPolynomial n) := by
  intro k
  match n with
  | 0 => simp
  | 1 =>
    rw [gammaPolynomial_one, coeff_one]
    split_ifs <;> norm_num
  | N + 2 =>
    by_cases hk : 2 * k ≤ N + 1
    · exact (coeff_gammaPolynomial_add_two_pos hk).le
    · rw [coeff_gammaPolynomial_add_two_eq_zero (by lia)]

/-- The constant term of `Γ_n` is positive for `n ≥ 1`. -/
theorem coeff_zero_gammaPolynomial_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < (gammaPolynomial n).coeff 0 := by
  match n, hn with
  | 1, _ => simp
  | N + 2, _ => exact coeff_gammaPolynomial_add_two_pos (by lia)

/-- `Γ_n` has degree `⌊(n - 1) / 2⌋` for `n ≥ 2`. -/
theorem natDegree_gammaPolynomial {n : ℕ} (hn : 2 ≤ n) :
    (gammaPolynomial n).natDegree = (n - 1) / 2 := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by lia⟩
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_
    (coeff_gammaPolynomial_add_two_pos (N := N) (k := (N + 2 - 1) / 2) (by lia)).ne'
  refine natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
  exact coeff_gammaPolynomial_add_two_eq_zero (by lia)

/-- `Γ_n` has a positive leading coefficient for `n ≥ 2`. -/
theorem hasPosLeadingCoeff_gammaPolynomial {n : ℕ} (hn : 2 ≤ n) :
    RealRooted.HasPosLeadingCoeff (gammaPolynomial n) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by lia⟩
  unfold RealRooted.HasPosLeadingCoeff
  rw [leadingCoeff, natDegree_gammaPolynomial hn]
  exact coeff_gammaPolynomial_add_two_pos (by lia)

/-! ### The descent polynomials `S_n` -/

/-- All coefficients of `S_n` are nonnegative. -/
theorem hasNonnegCoeffs_descentPolynomial (n : ℕ) :
    RealRooted.HasNonnegCoeffs (descentPolynomial n) :=
  RealRooted.hasNonnegCoeffs_gammaTransform (hasNonnegCoeffs_gammaPolynomial n)

/-- The coefficients `0, …, n - 1` of `S_n` are positive for `n ≥ 1`. -/
theorem coeff_descentPolynomial_pos {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n - 1) :
    0 < (descentPolynomial n).coeff k :=
  RealRooted.coeff_gammaTransform_pos_of_nonneg_of_coeff_zero_pos
    (hasNonnegCoeffs_gammaPolynomial n) (coeff_zero_gammaPolynomial_pos hn) hk

/-- `S_n` has degree `n - 1` for `n ≥ 1`. -/
theorem natDegree_descentPolynomial {n : ℕ} (hn : 1 ≤ n) :
    (descentPolynomial n).natDegree = n - 1 :=
  le_antisymm (RealRooted.natDegree_gammaTransform_le _ _)
    (le_natDegree_of_ne_zero (coeff_descentPolynomial_pos hn le_rfl).ne')

/-! ### First values -/

theorem gammaPolynomial_two : gammaPolynomial 2 = 1 := by
  simp [gammaPolynomial_add_two, compression, multiplier]

theorem gammaPolynomial_three : gammaPolynomial 3 = 1 + 2 * X := by
  ext k
  rcases k with _ | _ | k
  · norm_num [coeff_gammaPolynomial_add_two, coeff_one]
  · norm_num [coeff_gammaPolynomial_add_two, coeff_one]
  · rw [coeff_gammaPolynomial_add_two_eq_zero (N := 1) (by lia)]
    simp [coeff_X, coeff_one]

theorem gammaPolynomial_four : gammaPolynomial 4 = 1 + 7 * X := by
  ext k
  rcases k with _ | _ | k
  · norm_num [coeff_gammaPolynomial_add_two, Nat.factorial, auxPolynomial_succ, add_mul, coeff_one]
  · norm_num [coeff_gammaPolynomial_add_two, Nat.factorial, auxPolynomial_succ, add_mul, coeff_one]
  · rw [coeff_gammaPolynomial_add_two_eq_zero (N := 2) (by lia)]
    simp [coeff_X, coeff_one]

theorem descentPolynomial_one : descentPolynomial 1 = 1 := by
  simp [descentPolynomial, RealRooted.gammaTransform]

theorem descentPolynomial_two : descentPolynomial 2 = 1 + X := by
  simp [descentPolynomial, gammaPolynomial_two, RealRooted.gammaTransform,
    RealRooted.gammaBasisTerm, add_comm]

theorem descentPolynomial_three : descentPolynomial 3 = 1 + 4 * X + X ^ 2 := by
  rw [show descentPolynomial 3 = (X + 1) ^ 2 + C 2 * X by
    simp [descentPolynomial, gammaPolynomial_three, RealRooted.gammaTransform,
      RealRooted.gammaBasisTerm, Finset.sum_range_succ, coeff_X, coeff_one]]
  rw [map_ofNat C 2]
  ring

theorem descentPolynomial_four : descentPolynomial 4 = 1 + 10 * X + 10 * X ^ 2 + X ^ 3 := by
  rw [show descentPolynomial 4 = (X + 1) ^ 3 + C 7 * (X * (X + 1)) by
    simp [descentPolynomial, gammaPolynomial_four, RealRooted.gammaTransform,
      RealRooted.gammaBasisTerm, Finset.sum_range_succ, coeff_X, coeff_one]]
  rw [map_ofNat C 7]
  ring

end RealRooted.SeparablePermutations
