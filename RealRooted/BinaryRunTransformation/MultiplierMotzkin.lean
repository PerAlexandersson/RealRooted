import RealRooted.BinaryRunTransformation.CrossLength
import RealRooted.MultiplierSequence.Infinite
import RealRooted.MultiplierSequence.InvPochhammer
import RealRooted.Transforms.ReverseHermite.Preservation

/-!
# Multiplier-weighted Motzkin polynomials

For a sequence `γ`, put

```text
G_n^γ(t) = sum_m n! γ_m / (m! (n-2m)!) t^m,     R_n^γ = J_n(G_n^γ),
```

where `J_n` is the binary-run transform.  The unweighted polynomial
`G_n^1(t) = Q_n(2t)` is a rescaled matching polynomial of the complete graph:
`Q_n` is the reflection of the reverse-Hermite basis polynomial, so it has
only real nonpositive zeros.  If `γ` is a PF multiplier sequence with
positive entries, every `G_n^γ` is PF, and the polar identity

```text
(N - 2Θ) G_N^γ = N G_n^γ,        N = n + 1,
```

together with the binary-run cross-length theorem gives the Sturm chain
`R_n^γ ≪ R_{n+1}^γ`.  The Motzkin-ascent polynomials are the case
`γ_m = 1 / (m+1)!`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-! ### The matching polynomial of the complete graph -/

/-- The number of `m`-matchings of the complete graph on `n` vertices, as a
real number: `n! / (m! (n-2m)! 2^m)` when `2m ≤ n`, and `0` otherwise. -/
def completeMatchingCount (n m : ℕ) : ℝ :=
  if 2 * m ≤ n then
    (n.factorial : ℝ) / ((m.factorial : ℝ) * ((n - 2 * m).factorial : ℝ) * 2 ^ m)
  else 0

/-- The matching polynomial `sum_m completeMatchingCount n m t^m` of the
complete graph, as the reflection of the reverse-Hermite basis. -/
def completeMatchingPolynomial (n : ℕ) : ℝ[X] :=
  (reverseHermiteBasis (R := ℝ) n).reflect n

theorem natDegree_reverseHermiteBasis_le (n : ℕ) :
    (reverseHermiteBasis (R := ℝ) n).natDegree ≤ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      rw [reverseHermiteBasis_succ_succ]
      refine (natDegree_mul_le).trans ?_
      rw [natDegree_X]
      have h := natDegree_add_le (reverseHermiteBasis (R := ℝ) (n + 1))
        (C ((n : ℝ) + 1) * reverseHermiteBasis n)
      have h2 := natDegree_C_mul_le ((n : ℝ) + 1) (reverseHermiteBasis (R := ℝ) n)
      lia

private theorem reflect_one_X : (X : ℝ[X]).reflect 1 = 1 := by
  simp

private theorem reflect_succ_of_natDegree_le {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    p.reflect (n + 1) = X * p.reflect n := by
  have h := reflect_mul (1 : ℝ[X]) p (F := 1) (G := n) (by simp) hp
  rw [one_mul, reflect_one, pow_one, add_comm] at h
  exact h

theorem completeMatchingPolynomial_zero : completeMatchingPolynomial 0 = 1 := by
  simp [completeMatchingPolynomial]

theorem completeMatchingPolynomial_one : completeMatchingPolynomial 1 = 1 := by
  simp [completeMatchingPolynomial]

/-- The matching recurrence `Q_{n+2} = Q_{n+1} + (n+1) X Q_n`. -/
theorem completeMatchingPolynomial_succ_succ (n : ℕ) :
    completeMatchingPolynomial (n + 2) =
      completeMatchingPolynomial (n + 1) +
        C ((n : ℝ) + 1) * X * completeMatchingPolynomial n := by
  have hs : (reverseHermiteBasis (R := ℝ) (n + 1) +
      C ((n : ℝ) + 1) * reverseHermiteBasis n).natDegree ≤ n + 1 :=
    (natDegree_add_le _ _).trans (max_le (natDegree_reverseHermiteBasis_le _)
      ((natDegree_C_mul_le _ _).trans ((natDegree_reverseHermiteBasis_le n).trans
        (Nat.le_succ n))))
  have hmul := reflect_mul (X : ℝ[X]) _ (F := 1) (G := n + 1) (by simp) hs
  rw [show 1 + (n + 1) = n + 2 by lia, reflect_one_X, one_mul] at hmul
  rw [completeMatchingPolynomial, reverseHermiteBasis_succ_succ, hmul, reflect_add,
    reflect_C_mul, reflect_succ_of_natDegree_le (natDegree_reverseHermiteBasis_le n),
    completeMatchingPolynomial, completeMatchingPolynomial]
  ring

theorem completeMatchingCount_zero_right (n : ℕ) : completeMatchingCount n 0 = 1 := by
  simp [completeMatchingCount, Nat.factorial_ne_zero]

theorem completeMatchingCount_eq_zero {n m : ℕ} (h : n < 2 * m) :
    completeMatchingCount n m = 0 := by
  simp [completeMatchingCount, Nat.not_le.mpr h]

theorem completeMatchingCount_of_le {n m : ℕ} (h : 2 * m ≤ n) :
    completeMatchingCount n m =
      (n.factorial : ℝ) / ((m.factorial : ℝ) * ((n - 2 * m).factorial : ℝ) * 2 ^ m) := by
  simp [completeMatchingCount, h]

theorem completeMatchingCount_pos {n m : ℕ} (h : 2 * m ≤ n) :
    0 < completeMatchingCount n m := by
  rw [completeMatchingCount_of_le h]
  positivity

private theorem cast_factorial_succ_succ (n : ℕ) :
    ((n + 2).factorial : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) * (n.factorial : ℝ) := by
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

private theorem cast_factorial_succ' (n : ℕ) :
    ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- The matching recurrence on counts: the last vertex of `K_{n+2}` is either
unmatched or matched to one of the other `n + 1` vertices. -/
theorem completeMatchingCount_succ_succ (n k : ℕ) :
    completeMatchingCount (n + 2) (k + 1) =
      completeMatchingCount (n + 1) (k + 1) + ((n : ℝ) + 1) * completeMatchingCount n k := by
  have hf (a : ℕ) : (a.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
  rcases lt_trichotomy (2 * (k + 1)) (n + 2) with h | h | h
  · obtain ⟨e, rfl⟩ : ∃ e, n = 2 * k + e + 1 := ⟨n - 2 * k - 1, by lia⟩
    rw [completeMatchingCount_of_le (by lia), completeMatchingCount_of_le (by lia),
      completeMatchingCount_of_le (by lia),
      show 2 * k + e + 1 + 2 - 2 * (k + 1) = e + 1 by lia,
      show 2 * k + e + 1 + 1 - 2 * (k + 1) = e by lia,
      show 2 * k + e + 1 - 2 * k = e + 1 by lia,
      cast_factorial_succ_succ, cast_factorial_succ' (2 * k + e + 1), cast_factorial_succ' e,
      cast_factorial_succ' k]
    have hF := hf (2 * k + e + 1)
    have hE := hf e
    have hK := hf k
    generalize ((2 * k + e + 1).factorial : ℝ) = F at hF ⊢
    generalize (e.factorial : ℝ) = E at hE ⊢
    generalize (k.factorial : ℝ) = K at hK ⊢
    push_cast
    field_simp
    ring
  · obtain rfl : n = 2 * k := by lia
    rw [completeMatchingCount_of_le (by lia), completeMatchingCount_eq_zero (by lia),
      completeMatchingCount_of_le (by lia),
      show 2 * k + 2 - 2 * (k + 1) = 0 by lia, show 2 * k - 2 * k = 0 by lia,
      cast_factorial_succ_succ, cast_factorial_succ' k]
    have hF := hf (2 * k)
    have hK := hf k
    generalize ((2 * k).factorial : ℝ) = F at hF ⊢
    generalize (k.factorial : ℝ) = K at hK ⊢
    push_cast
    field_simp
    ring
  · rw [completeMatchingCount_eq_zero h, completeMatchingCount_eq_zero (by lia),
      completeMatchingCount_eq_zero (by lia)]
    ring

/-- The coefficients of the complete-graph matching polynomial. -/
theorem coeff_completeMatchingPolynomial (n m : ℕ) :
    (completeMatchingPolynomial n).coeff m = completeMatchingCount n m := by
  induction n using Nat.twoStepInduction generalizing m with
  | zero =>
      rw [completeMatchingPolynomial_zero, coeff_one]
      rcases m with _ | m
      · simp [completeMatchingCount]
      · simp [completeMatchingCount_eq_zero (by lia : 0 < 2 * (m + 1))]
  | one =>
      rw [completeMatchingPolynomial_one, coeff_one]
      rcases m with _ | m
      · simp [completeMatchingCount]
      · simp [completeMatchingCount_eq_zero (by lia : 1 < 2 * (m + 1))]
  | more n ih0 ih1 =>
      rw [completeMatchingPolynomial_succ_succ, coeff_add, mul_assoc, coeff_C_mul]
      rcases m with _ | k
      · simp [ih1, completeMatchingCount_zero_right]
      · rw [coeff_X_mul, ih1, ih0, completeMatchingCount_succ_succ]

theorem completeMatchingPolynomial_isPFPolynomial (n : ℕ) :
    IsPFPolynomial (completeMatchingPolynomial n) := by
  have hB : IsPFPolynomial (reverseHermiteBasis (R := ℝ) n) := by
    simpa using reverseHermiteTransform_preserves_pf (isPFPolynomial_X_pow n)
  exact reciprocalShift_preserves_pf hB (natDegree_reverseHermiteBasis_le n)

/-- The polar relation `(N - 2m) · #M_m(K_N) = N · #M_m(K_n)` with `N = n + 1`. -/
theorem completeMatchingCount_polar (n m : ℕ) :
    ((n : ℝ) + 1 - 2 * m) * completeMatchingCount (n + 1) m =
      ((n : ℝ) + 1) * completeMatchingCount n m := by
  have hf (a : ℕ) : (a.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
  rcases lt_trichotomy (2 * m) (n + 1) with h | h | h
  · obtain ⟨d, rfl⟩ : ∃ d, n = 2 * m + d := ⟨n - 2 * m, by lia⟩
    rw [completeMatchingCount_of_le (by lia), completeMatchingCount_of_le (by lia),
      show 2 * m + d + 1 - 2 * m = d + 1 by lia, show 2 * m + d - 2 * m = d by lia,
      cast_factorial_succ' (2 * m + d), cast_factorial_succ' d]
    have hN := hf (2 * m + d)
    have hD := hf d
    have hM := hf m
    generalize ((2 * m + d).factorial : ℝ) = F at hN ⊢
    generalize (d.factorial : ℝ) = E at hD ⊢
    generalize (m.factorial : ℝ) = K at hM ⊢
    push_cast
    field_simp
    ring
  · have h' : ((n : ℝ) + 1 - 2 * m) = 0 := by
      have : ((2 * m : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by rw [h]
      push_cast at this
      linarith
    rw [h', zero_mul, completeMatchingCount_eq_zero (by lia), mul_zero]
  · rw [completeMatchingCount_eq_zero h, completeMatchingCount_eq_zero (by lia)]
    ring

private theorem coeff_comp_C_mul_X (p : ℝ[X]) (a : ℝ) (n : ℕ) :
    (p.comp (C a * X)).coeff n = a ^ n * p.coeff n := by
  rw [comp, eval₂_eq_sum_range, finsetSum_coeff]
  simp only [mul_pow, ← C_pow, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · ring
  · rw [coeff_eq_zero_of_natDegree_lt (by lia)]
    ring

/-! ### The weighted inputs `G_n^γ` -/

/-- The multiplier-weighted Motzkin input
`G_n^γ(t) = sum_m n! γ_m / (m! (n-2m)!) t^m`. -/
def motzkinWeightedInput (γ : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  diagonalOperator γ ((completeMatchingPolynomial n).comp (C 2 * X))

theorem coeff_motzkinWeightedInput (γ : ℕ → ℝ) (n m : ℕ) :
    (motzkinWeightedInput γ n).coeff m = γ m * 2 ^ m * completeMatchingCount n m := by
  rw [motzkinWeightedInput, coeff_diagonalOperator, coeff_comp_C_mul_X,
    coeff_completeMatchingPolynomial]
  ring

theorem motzkinWeightedInput_isPFPolynomial {γ : ℕ → ℝ} (hγ : IsPFMultiplierSequence γ)
    (n : ℕ) : IsPFPolynomial (motzkinWeightedInput γ n) := by
  have hcomp := IsPFPolynomial.comp_C_mul_X_add_C (a := 2) (d := 0) (by norm_num) le_rfl
    (completeMatchingPolynomial_isPFPolynomial n)
  rw [C_0, add_zero] at hcomp
  exact hγ.diagonalOperator_isPF hcomp

theorem coeff_zero_motzkinWeightedInput (γ : ℕ → ℝ) (n : ℕ) :
    (motzkinWeightedInput γ n).coeff 0 = γ 0 := by
  rw [coeff_motzkinWeightedInput, completeMatchingCount_zero_right]
  ring

theorem natDegree_motzkinWeightedInput {γ : ℕ → ℝ} (hpos : ∀ m, 0 < γ m) (n : ℕ) :
    (motzkinWeightedInput γ n).natDegree = n / 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [coeff_motzkinWeightedInput, completeMatchingCount_eq_zero (by lia), mul_zero]
  · rw [coeff_motzkinWeightedInput]
    have := completeMatchingCount_pos (n := n) (m := n / 2) (by lia)
    have := hpos (n / 2)
    positivity

/-- The polar identity `(N - 2Θ) G_N^γ = N G_n^γ` with `N = n + 1`. -/
theorem motzkinWeightedInput_polar (γ : ℕ → ℝ) (n : ℕ) :
    C ((n : ℝ) + 1) * motzkinWeightedInput γ (n + 1) -
        C 2 * theta (motzkinWeightedInput γ (n + 1)) =
      C ((n : ℝ) + 1) * motzkinWeightedInput γ n := by
  ext m
  rw [coeff_sub, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_theta,
    coeff_motzkinWeightedInput, coeff_motzkinWeightedInput]
  have h := completeMatchingCount_polar n m
  linear_combination γ m * 2 ^ m * h

/-! ### The rows `R_n^γ` and their Sturm chain -/

/-- The multiplier-weighted Motzkin row `R_n^γ = J_n(G_n^γ)`. -/
def motzkinWeightedRow (γ : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  binaryRunTransform n (motzkinWeightedInput γ n)

private theorem binaryRunTransform_C_mul' (n : ℕ) (a : ℝ) (p : ℝ[X]) :
    binaryRunTransform n (C a * p) = C a * binaryRunTransform n p := by
  rw [← smul_eq_C_mul, binaryRunTransform_smul]

/-- For large `n`, consecutive weighted rows interlace. -/
theorem motzkinWeightedRow_strictInterl_succ_of_three_le {γ : ℕ → ℝ}
    (hγ : IsPFMultiplierSequence γ) (hpos : ∀ m, 0 < γ m) {n : ℕ} (hn : 3 ≤ n) :
    StrictInterl (motzkinWeightedRow γ n) (motzkinWeightedRow γ (n + 1)) := by
  have hdeg := natDegree_motzkinWeightedInput hpos (n + 1)
  have h := strictInterl_binaryRunTransform_succ (n := n)
    (motzkinWeightedInput_isPFPolynomial hγ (n + 1))
    (by rw [coeff_zero_motzkinWeightedInput]; exact (hpos 0).ne')
    (by rw [hdeg]; lia) (by rw [hdeg]; lia)
  rw [motzkinWeightedInput_polar, binaryRunTransform_C_mul'] at h
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h' := h.C_mul_left (a := ((n : ℝ) + 1)⁻¹) (inv_ne_zero hn1)
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hn1, C_1, one_mul] at h'

/-- The low rows are affine: `G_n^γ = γ_0 + 2 γ_1 #M_1(K_n) t` for `n ≤ 3`. -/
private theorem motzkinWeightedInput_of_le_three (γ : ℕ → ℝ) {n : ℕ} (hn : n ≤ 3) :
    motzkinWeightedInput γ n =
      C (γ 0) + C (2 * γ 1 * completeMatchingCount n 1) * X := by
  ext m
  rw [coeff_motzkinWeightedInput, coeff_add, coeff_C, coeff_C_mul, coeff_X]
  rcases m with _ | _ | m
  · simp [completeMatchingCount_zero_right]
  · simp only [one_ne_zero, ↓reduceIte, pow_one, zero_add, mul_one]
    ring
  · rw [completeMatchingCount_eq_zero (by lia)]
    simp

private theorem motzkinWeightedRow_of_le_three (γ : ℕ → ℝ) {n : ℕ} (hn0 : 0 < n)
    (hn : n ≤ 3) :
    motzkinWeightedRow γ n =
      C (γ 0) + C (2 * γ 1 * completeMatchingCount n 1) * X := by
  rw [motzkinWeightedRow, motzkinWeightedInput_of_le_three γ hn, binaryRunTransform_add,
    ← mul_one (C (γ 0)), binaryRunTransform_C_mul', binaryRunTransform_one,
    binaryRunTransform_C_mul', ← pow_one X, binaryRunTransform_X_pow,
    binaryRunPolynomial_one n hn0, mul_one, pow_one]

/-- **Sturm chain for multiplier-weighted Motzkin rows.**  If `γ` is a PF
multiplier sequence with positive entries, then `R_n^γ ≪ R_{n+1}^γ` for
every `n`. -/
theorem motzkinWeightedRow_strictInterl_succ {γ : ℕ → ℝ}
    (hγ : IsPFMultiplierSequence γ) (hpos : ∀ m, 0 < γ m) (n : ℕ) :
    StrictInterl (motzkinWeightedRow γ n) (motzkinWeightedRow γ (n + 1)) := by
  rcases lt_or_ge n 3 with hn | hn
  · have h0 := hpos 0
    have h1 := hpos 1
    have hc2 : completeMatchingCount 2 1 = 1 := by
      rw [completeMatchingCount_of_le (by norm_num)]; norm_num [Nat.factorial]
    have hc3 : completeMatchingCount 3 1 = 3 := by
      rw [completeMatchingCount_of_le (by norm_num)]; norm_num [Nat.factorial]
    have hc1 : completeMatchingCount 1 1 = 0 := completeMatchingCount_eq_zero (by norm_num)
    have hR0 : motzkinWeightedRow γ 0 = C (γ 0) := by
      rw [motzkinWeightedRow, motzkinWeightedInput_of_le_three γ (by norm_num),
        completeMatchingCount_eq_zero (by norm_num)]
      simp only [mul_zero, C_0, zero_mul, add_zero]
      rw [← mul_one (C (γ 0)), binaryRunTransform_C_mul', binaryRunTransform_one, mul_one]
    interval_cases n
    · rw [hR0, motzkinWeightedRow_of_le_three γ (by norm_num) (by norm_num), hc1]
      simpa using StrictInterl.refl (C_ne_zero.mpr h0.ne') (Splits.C (γ 0))
    · rw [motzkinWeightedRow_of_le_three γ (by norm_num) (by norm_num), hc1,
        motzkinWeightedRow_of_le_three γ (by norm_num) (by norm_num), hc2]
      have hlin : (C (γ 0) + C (2 * γ 1 * 1) * X : ℝ[X]).natDegree = 1 := by
        rw [add_comm]; exact natDegree_linear (by positivity)
      simpa using (interlaces_one_linear hlin).toStrictInterl.C_mul_left h0.ne'
    · rw [motzkinWeightedRow_of_le_three γ (by norm_num) (by norm_num), hc2,
        motzkinWeightedRow_of_le_three γ (by norm_num) (by norm_num), hc3]
      set g : ℝ[X] := C (γ 0) + C (2 * γ 1 * 1) * X
      set f : ℝ[X] := C (γ 0) + C (2 * γ 1 * 3) * X
      have hg : g.natDegree = 1 := by
        simp only [g]; rw [add_comm]; exact natDegree_linear (by positivity)
      have hf : f.natDegree = 1 := by
        simp only [f]; rw [add_comm]; exact natDegree_linear (by positivity)
      refine PosComboRealRooted.strictInterl_of_strictInterl_or_reverse_of_root_asymmetry
        (PosComboRealRooted.strictInterl_or_reverse_of_same_degree_one (hg.trans hf.symm) hf)
        (c := -(γ 0) / (2 * γ 1)) (r := -(γ 0) / (6 * γ 1)) ?_ ?_ ?_
      · intro x hx
        have hg0 : g ≠ 0 := fun h => by simp [h] at hg
        have hroot := (mem_roots hg0).mp hx
        simp only [g, IsRoot, eval_add, eval_C, eval_mul, eval_X] at hroot
        field_simp
        linarith
      · simp only [f, IsRoot, eval_add, eval_C, eval_mul, eval_X]
        field_simp
        ring
      · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  · exact motzkinWeightedRow_strictInterl_succ_of_three_le hγ hpos hn

/-- **The continuous family.**  For real `α > 0` and `γ_m = 1 / (α)_m`,
consecutive rows interlace.  The Motzkin-ascent polynomials are `α = 2`,
where `γ_m = 1 / (m+1)!`. -/
theorem motzkinWeightedRow_inv_ascPochhammer_strictInterl_succ {α : ℝ} (hα : 0 < α)
    (n : ℕ) :
    StrictInterl
      (motzkinWeightedRow (fun m => ((ascPochhammer ℝ m).eval α)⁻¹) n)
      (motzkinWeightedRow (fun m => ((ascPochhammer ℝ m).eval α)⁻¹) (n + 1)) :=
  motzkinWeightedRow_strictInterl_succ (isPFMultiplierSequence_inv_ascPochhammer hα)
    (fun m => inv_pos.mpr (ascPochhammer_pos m α hα)) n

end RealRooted
