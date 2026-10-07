import RealRooted.Favard.PathEnvelope
import RealRooted.CombinatorialExamples.BigDescents321.Reference

/-!
# The backward recurrence at the zeros of `G_k`

Fix `k`. At a zero `a` of the Gegenbauer polynomial `G_k`, the lower polynomials are multiples of
`G_(k-1)(a)`: `G_(k-1-j)(a) = H_j(a) G_(k-1)(a)`, where `H_j` satisfies the backward recurrence
`H_j = (2k - 2j + 3)/(k - j + 2) c H_(j-1) - (k - j + 1)/(k - j + 2) H_(j-2)` (issue #1143, §8).

We write `H_j = μ_j d_j`, where the normalized values `d_j` satisfy the Favard-type recurrence
`d_(j+2) = c d_(j+1) - η_(j+1) d_j` with the reversed edges `η_e = γ_(k-e)` of the reference
family, so that the weighted-path envelope applies to them.

## Main statements

* `aeval_gegen_eq_backH`: `G_(k-1-j)(a) = H_j(a) G_(k-1)(a)` at a zero `a` of `G_k`.
* `abs_backH_le`: `|H_(2l)(c)| ≤ (1 - c²) + H_(2l)(1) c²` for `|c| ≤ 1` and `2l ≤ k - 1`.
-/

open Polynomial Finset

namespace RealRooted.BigDescents321

/-- The squared edges `γ_m = m(m + 2)/((2m + 1)(2m + 3))` of the reference family. -/
noncomputable def gammaR (m : ℕ) : ℝ := m * ((m : ℝ) + 2) / ((2 * m + 1) * (2 * m + 3))

theorem gammaR_nonneg (m : ℕ) : 0 ≤ gammaR m := by
  unfold gammaR
  positivity

theorem gammaR_le_quarter (m : ℕ) : gammaR m ≤ 1 / 4 := by
  unfold gammaR
  rw [div_le_iff₀ (by positivity)]
  nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

/-- The reversed edges `η_e = γ_(k-e)` for `e < k`, and `0` beyond. -/
noncomputable def etaBack (k e : ℕ) : ℝ := if e < k then gammaR (k - e) else 0

/-- The normalized backward values `d_j(x)`. -/
noncomputable def dBack (k : ℕ) (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => x
  | n + 2 => x * dBack k x (n + 1) - etaBack k (n + 1) * dBack k x n

theorem etaBack_nonneg (k e : ℕ) : 0 ≤ etaBack k e := by
  unfold etaBack
  split_ifs
  · exact gammaR_nonneg _
  · exact le_rfl

theorem etaBack_le_quarter (k e : ℕ) : etaBack k e ≤ 1 / 4 := by
  unfold etaBack
  split_ifs
  · exact gammaR_le_quarter _
  · norm_num

/-- The envelope for the normalized backward values. -/
theorem abs_dBack_le (k l : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |dBack k x (2 * l)| ≤
      PathEnvelope.envConst (etaBack k) l * (1 - x ^ 2) + dBack k 1 (2 * l) * x ^ 2 :=
  PathEnvelope.abs_le_of_even (d := dBack k) (fun e ↦ etaBack_le_quarter k (e + 1))
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) l hx

/-- The normalizations `μ_j = ∏_(i < j) (2k - 2i + 1)/(k - i + 1)`. -/
noncomputable def muBack (k j : ℕ) : ℝ :=
  ∏ i ∈ range j, (2 * (k : ℝ) - 2 * i + 1) / ((k : ℝ) - i + 1)

/-- The backward values `H_j(x) = μ_j d_j(x)`. -/
noncomputable def backH (k : ℕ) (x : ℝ) (j : ℕ) : ℝ := muBack k j * dBack k x j

theorem backH_zero (k : ℕ) (x : ℝ) : backH k x 0 = 1 := by
  simp [backH, muBack, dBack]

theorem backH_one (k : ℕ) (x : ℝ) : backH k x 1 = (2 * k + 1) / (k + 1) * x := by
  simp [backH, muBack, dBack]

/-- The backward recurrence `H_(j+2) = (2k - 2j - 1)/(k - j) c H_(j+1) - (k - j - 1)/(k - j) H_j`,
for `j + 3 ≤ k`. -/
theorem backH_rec {k j : ℕ} (h : j + 3 ≤ k) (x : ℝ) :
    backH k x (j + 2) = (2 * (k : ℝ) - 2 * j - 1) / ((k : ℝ) - j) * x * backH k x (j + 1) -
      ((k : ℝ) - j - 1) / ((k : ℝ) - j) * backH k x j := by
  obtain ⟨p, rfl⟩ : ∃ p, k = j + 3 + p := ⟨k - j - 3, by lia⟩
  simp only [backH, muBack, prod_range_succ]
  generalize (∏ i ∈ range j, (2 * ((j + 3 + p : ℕ) : ℝ) - 2 * i + 1) /
    (((j + 3 + p : ℕ) : ℝ) - i + 1)) = M
  simp only [dBack, etaBack, show j + 1 < j + 3 + p by lia, ↓reduceIte, gammaR,
    show j + 3 + p - (j + 1) = p + 2 by lia]
  push_cast
  have h1 : ((j : ℝ) + 3 + p) - j ≠ 0 := by
    have := (p.cast_nonneg : (0 : ℝ) ≤ p); intro h; linarith
  have h2 : ((j : ℝ) + 3 + p) - (j + 1) + 1 ≠ 0 := by
    have := (p.cast_nonneg : (0 : ℝ) ≤ p); intro h; linarith
  have h3 : 2 * ((p : ℝ) + 2) + 1 ≠ 0 := by positivity
  have h4 : 2 * ((p : ℝ) + 2) + 3 ≠ 0 := by positivity
  have h5 : ((j : ℝ) + 3 + p) - j + 1 ≠ 0 := by
    have := (p.cast_nonneg : (0 : ℝ) ≤ p); intro h; linarith
  field_simp
  ring

/-- `G_(p+2)(a) (p+2) = (2p + 5) a G_(p+1)(a) - (p + 3) G_p(a)` for real `a`. -/
theorem aeval_gegen_rec (p : ℕ) (a : ℝ) :
    ((p : ℝ) + 2) * aeval a (gegen (p + 2)) =
      (2 * (p : ℝ) + 5) * a * aeval a (gegen (p + 1)) - ((p : ℝ) + 3) * aeval a (gegen p) := by
  have h := congrArg (aeval a) (gegen_rec p)
  simp only [map_mul, map_add, map_sub, map_natCast, map_ofNat, aeval_X] at h
  exact h

/-- At a zero `a` of `G_k`: `G_(k-1-j)(a) = H_j(a) G_(k-1)(a)` for `j < k`. -/
theorem aeval_gegen_eq_backH {k : ℕ} {a : ℝ} (ha : aeval a (gegen k) = 0) :
    ∀ j, j + 1 ≤ k → aeval a (gegen (k - 1 - j)) = backH k a j * aeval a (gegen (k - 1))
  | 0, _ => by simp [backH_zero]
  | 1, h => by
    obtain ⟨p, rfl⟩ : ∃ p, k = p + 2 := ⟨k - 2, by lia⟩
    have hr := aeval_gegen_rec p a
    rw [ha, mul_zero] at hr
    rw [backH_one, show p + 2 - 1 - 1 = p by lia, show p + 2 - 1 = p + 1 by lia]
    have : ((p : ℝ) + 3) ≠ 0 := by positivity
    push_cast
    field_simp
    linear_combination hr
  | j + 2, h => by
    have ih0 := aeval_gegen_eq_backH ha j (by lia)
    have ih1 := aeval_gegen_eq_backH ha (j + 1) (by lia)
    rw [backH_rec (by lia)]
    obtain ⟨p, rfl⟩ : ∃ p, k = j + 3 + p := ⟨k - j - 3, by lia⟩
    have hr := aeval_gegen_rec p a
    rw [show j + 3 + p - 1 - j = p + 2 by lia] at ih0
    rw [show j + 3 + p - 1 - (j + 1) = p + 1 by lia] at ih1
    rw [show j + 3 + p - 1 - (j + 2) = p by lia, ih0, ih1] at *
    push_cast
    have : ((j : ℝ) + 3 + p) - j ≠ 0 := by
      have := (p.cast_nonneg : (0 : ℝ) ≤ p); intro h; linarith
    have : ((p : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    linear_combination hr

/-- `H_j(1) = (j + 1)(2k + 2 - j)/(2k + 2)` for `j < k`. -/
theorem backH_eval_one {k : ℕ} : ∀ j, j + 1 ≤ k →
    backH k 1 j = ((j : ℝ) + 1) * (2 * k + 2 - j) / (2 * k + 2)
  | 0, _ => by
    rw [backH_zero]
    have : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring
  | 1, _ => by
    rw [backH_one]
    have : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  | j + 2, h => by
    rw [backH_rec (by lia), backH_eval_one (j + 1) (by lia), backH_eval_one j (by lia)]
    obtain ⟨p, rfl⟩ : ∃ p, k = j + 3 + p := ⟨k - j - 3, by lia⟩
    push_cast
    have : ((j : ℝ) + 3 + p) - j ≠ 0 := by
      have := (p.cast_nonneg : (0 : ℝ) ≤ p); intro h; linarith
    have : 2 * ((j : ℝ) + 3 + p) + 2 ≠ 0 := by positivity
    field_simp
    ring

theorem muBack_pos {k j : ℕ} (h : j ≤ k) : 0 < muBack k j := by
  apply prod_pos
  intro i hi
  have hi' : (i : ℝ) < k := by exact_mod_cast (mem_range.mp hi).trans_le h
  apply div_pos <;> linarith

/-- `H_2(c) = (4k² - 1)/(k(k + 1)) c² - (k - 1)/k`. -/
theorem backH_two {k : ℕ} (hk : 2 ≤ k) (x : ℝ) :
    backH k x 2 = (2 * (k : ℝ) + 1) * (2 * k - 1) / (k * (k + 1)) * x ^ 2 - ((k : ℝ) - 1) / k := by
  obtain ⟨p, rfl⟩ : ∃ p, k = p + 2 := ⟨k - 2, by lia⟩
  simp only [backH, muBack, prod_range_succ, prod_range_zero, one_mul, dBack, etaBack,
    show 1 < p + 2 by lia, ↓reduceIte, gammaR, show p + 2 - 1 = p + 1 by lia]
  push_cast
  simp only [mul_zero, sub_zero]
  have : ((p : ℝ) + 2) - 1 + 1 ≠ 0 := by
    have := (p.cast_nonneg : (0 : ℝ) ≤ p); intro h; linarith
  have : 2 * ((p : ℝ) + 1) + 1 ≠ 0 := by positivity
  have : 2 * ((p : ℝ) + 1) + 3 ≠ 0 := by positivity
  have : ((p : ℝ) + 2) ≠ 0 := by positivity
  have : ((p : ℝ) + 2) + 1 ≠ 0 := by positivity
  have : 2 * ((p : ℝ) + 2) - 1 ≠ 0 := by
    have := (p.cast_nonneg : (0 : ℝ) ≤ p); intro h; linarith
  field_simp
  ring

/-- `S_(k,l) = μ_(2l) B_l ∈ [0, 1]`, where `B_l` is the envelope constant of the `d_j`. -/
theorem muBack_mul_envConst_mem {k : ℕ} : ∀ l, 2 * l + 1 ≤ k →
    0 ≤ muBack k (2 * l) * PathEnvelope.envConst (etaBack k) l ∧
      muBack k (2 * l) * PathEnvelope.envConst (etaBack k) l ≤ 1
  | 0, _ => by simp [muBack, PathEnvelope.envConst]
  | l + 1, h => by
    obtain ⟨h0, h1⟩ := muBack_mul_envConst_mem (k := k) l (by lia)
    obtain ⟨p, rfl⟩ : ∃ p, k = 2 * l + 3 + p := ⟨k - 2 * l - 3, by lia⟩
    have hf : (2 * ((2 * l + 3 + p : ℕ) : ℝ) - 2 * ((2 * l : ℕ) : ℝ) + 1) /
          (((2 * l + 3 + p : ℕ) : ℝ) - ((2 * l : ℕ) : ℝ) + 1) *
        ((2 * ((2 * l + 3 + p : ℕ) : ℝ) - 2 * ((2 * l + 1 : ℕ) : ℝ) + 1) /
          (((2 * l + 3 + p : ℕ) : ℝ) - ((2 * l + 1 : ℕ) : ℝ) + 1)) *
        (1 / 2 - etaBack (2 * l + 3 + p) (2 * l + 1)) =
          (2 * ((p : ℝ) + 2) ^ 2 + 4 * ((p : ℝ) + 2) + 3) /
            (2 * (((p : ℝ) + 2) + 1) * (((p : ℝ) + 2) + 2)) := by
      simp only [etaBack, show 2 * l + 1 < 2 * l + 3 + p by lia, ↓reduceIte, gammaR,
        show 2 * l + 3 + p - (2 * l + 1) = p + 2 by lia]
      push_cast
      have : (2 * ((p : ℝ) + 2) + 1) ≠ 0 := by positivity
      have : (2 * ((p : ℝ) + 2) + 3) ≠ 0 := by positivity
      have : ((2 * (l : ℝ) + 3 + p) - 2 * l + 1) ≠ 0 := by
        have := (p.cast_nonneg : (0 : ℝ) ≤ p); intro h; linarith
      have : ((2 * (l : ℝ) + 3 + p) - (2 * l + 1) + 1) ≠ 0 := by
        have := (p.cast_nonneg : (0 : ℝ) ≤ p); intro h; linarith
      field_simp
      ring
    have e : muBack (2 * l + 3 + p) (2 * (l + 1)) *
        PathEnvelope.envConst (etaBack (2 * l + 3 + p)) (l + 1) =
        muBack (2 * l + 3 + p) (2 * l) * PathEnvelope.envConst (etaBack (2 * l + 3 + p)) l *
          ((2 * ((p : ℝ) + 2) ^ 2 + 4 * ((p : ℝ) + 2) + 3) /
            (2 * (((p : ℝ) + 2) + 1) * (((p : ℝ) + 2) + 2))) := by
      rw [← hf, show 2 * (l + 1) = 2 * l + 1 + 1 by ring, muBack, prod_range_succ,
        prod_range_succ, PathEnvelope.envConst, prod_range_succ, ← muBack,
        ← PathEnvelope.envConst]
      push_cast
      ring
    have hp : (0 : ℝ) ≤ p := p.cast_nonneg
    have fpos : 0 ≤ (2 * ((p : ℝ) + 2) ^ 2 + 4 * ((p : ℝ) + 2) + 3) /
        (2 * (((p : ℝ) + 2) + 1) * (((p : ℝ) + 2) + 2)) := by positivity
    have fle : (2 * ((p : ℝ) + 2) ^ 2 + 4 * ((p : ℝ) + 2) + 3) /
        (2 * (((p : ℝ) + 2) + 1) * (((p : ℝ) + 2) + 2)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    rw [e]
    exact ⟨mul_nonneg h0 fpos, by nlinarith⟩

/-- The envelope `|H_(2l)(c)| ≤ (1 - c²) + H_(2l)(1) c²` for `|c| ≤ 1` and `2l < k`. -/
theorem abs_backH_le {k l : ℕ} (h : 2 * l + 1 ≤ k) {x : ℝ} (hx : |x| ≤ 1) :
    |backH k x (2 * l)| ≤ (1 - x ^ 2) + backH k 1 (2 * l) * x ^ 2 := by
  have hμ := muBack_pos (k := k) (j := 2 * l) (by lia)
  obtain ⟨-, hS⟩ := muBack_mul_envConst_mem l h
  have hd := abs_dBack_le k l hx
  have hx2 : 0 ≤ 1 - x ^ 2 := by
    have : x ^ 2 ≤ 1 := by
      rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg x) hx
    linarith
  rw [backH, abs_mul, abs_of_pos hμ, backH]
  calc muBack k (2 * l) * |dBack k x (2 * l)|
      ≤ muBack k (2 * l) * (PathEnvelope.envConst (etaBack k) l * (1 - x ^ 2) +
          dBack k 1 (2 * l) * x ^ 2) := by gcongr
    _ = muBack k (2 * l) * PathEnvelope.envConst (etaBack k) l * (1 - x ^ 2) +
          muBack k (2 * l) * dBack k 1 (2 * l) * x ^ 2 := by ring
    _ ≤ 1 * (1 - x ^ 2) + muBack k (2 * l) * dBack k 1 (2 * l) * x ^ 2 := by gcongr
    _ = (1 - x ^ 2) + muBack k (2 * l) * dBack k 1 (2 * l) * x ^ 2 := by ring

/-- The signed coefficient criterion (issue #1143, §8): if `c_j = 0` for odd `j` and `c_j ≤ 0`
for even `j ≥ 4`, then on `[-1, 1]`
`∑_(j<k) c_j H_j(x) ≥ (c_0 - (k-1)/k c_2 + ∑_(4 ≤ j < k) c_j)(1 - x²) + (∑_(j<k) c_j H_j(1)) x²`.
The coefficient `c_2` keeps the exact `H_2`, with no sign condition. -/
theorem backward_criterion {k : ℕ} (hk : 4 ≤ k) (c : ℕ → ℝ) (hodd : ∀ j, j % 2 = 1 → c j = 0)
    (hneg : ∀ j, 4 ≤ j → j < k → c j ≤ 0) {x : ℝ} (hx : |x| ≤ 1) :
    (c 0 - ((k : ℝ) - 1) / k * c 2 + ∑ j ∈ Ico 4 k, c j) * (1 - x ^ 2) +
        (∑ j ∈ range k, c j * backH k 1 j) * x ^ 2 ≤
      ∑ j ∈ range k, c j * backH k x j := by
  have split : ∀ f : ℕ → ℝ, ∑ j ∈ range k, f j = f 0 + f 1 + f 2 + f 3 + ∑ j ∈ Ico 4 k, f j :=
    fun f ↦ by
      rw [range_eq_Ico, ← sum_Ico_consecutive _ (show 0 ≤ 4 by norm_num) hk]
      simp [sum_Ico_eq_sum_range, sum_range_succ]
  rw [split, split]
  have hc1 := hodd 1 rfl
  have hc3 := hodd 3 rfl
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by lia)
  have hH2 := backH_two (k := k) (by lia) x
  have hH21 := backH_two (k := k) (by lia) 1
  have term : ∀ j ∈ Ico 4 k, c j * (1 - x ^ 2) + c j * backH k 1 j * x ^ 2 ≤
      c j * backH k x j := fun j hj ↦ by
    obtain ⟨hj4, hjk⟩ := mem_Ico.mp hj
    rcases Nat.even_or_odd' j with ⟨l, rfl | rfl⟩
    · have hb := abs_backH_le (k := k) (l := l) (by lia) hx
      have hcj := hneg (2 * l) hj4 hjk
      have : backH k x (2 * l) ≤ (1 - x ^ 2) + backH k 1 (2 * l) * x ^ 2 :=
        (le_abs_self _).trans hb
      nlinarith
    · rw [hodd (2 * l + 1) (by lia)]
      simp
  have hsum := sum_le_sum term
  rw [sum_add_distrib, ← sum_mul, ← sum_mul] at hsum
  rw [backH_zero, backH_zero, hc1, hc3, hH2, hH21]
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have e : c 2 * ((2 * (k : ℝ) + 1) * (2 * k - 1) / (k * (k + 1)) * x ^ 2 - ((k : ℝ) - 1) / k) =
      -(((k : ℝ) - 1) / k * c 2) * (1 - x ^ 2) +
        c 2 * ((2 * (k : ℝ) + 1) * (2 * k - 1) / (k * (k + 1)) * 1 ^ 2 - ((k : ℝ) - 1) / k) *
          x ^ 2 := by
    field_simp
    ring
  rw [e]
  nlinarith [hsum]

end RealRooted.BigDescents321
