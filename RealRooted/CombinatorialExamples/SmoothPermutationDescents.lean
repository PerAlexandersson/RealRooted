module

public import RealRooted.NarayanaTransformation.Coefficients
public import RealRooted.SimpleRoots
import RealRooted.NarayanaTransformation.SimpleRoots
import RealRooted.NarayanaTransformation.Endpoints
import RealRooted.NarayanaTransformation.Recurrences.Interlacing
import RealRooted.NarayanaTransformation.Recurrences.Identities
import RealRooted.NarayanaTransformation.Rectangular.Narayana
import RealRooted.NarayanaTransformation.Rectangular.Preservation
import RealRooted.Mathlib.Algebra.Polynomial.Reverse

/-!
# The recurrence for descents in smooth permutations

We formalize the recurrence-defined family in the unpublished manuscript
*Descents in smooth permutations*, equations (Q), (rec), and Corollary (coeff).
The auxiliary polynomial is `(k + 4) * narayanaPolynomial 2 k`, so its root
properties follow from the existing generalized Narayana theory.

`row n` denotes the manuscript's `P_{n+1}`. We do not formalize the
identification with pattern-avoiding permutations. Real-rootedness of these
rows is the manuscript's open conjecture, and is not asserted here.
-/

@[expose] public section

open Polynomial Finset

noncomputable section

namespace RealRooted.SmoothPermutationDescents

/-- The auxiliary polynomial `A_k = -Q_{k+5}/t²` of the unpublished manuscript,
expressed using the existing generalized Narayana family. -/
def auxiliary (k : ℕ) : ℝ[X] := C (k + 4 : ℝ) * narayanaPolynomial 2 k

/-- The normalization identifying the auxiliary family with generalized Narayana polynomials. -/
theorem auxiliary_eq_narayanaPolynomial (k : ℕ) :
    auxiliary k = C (k + 4 : ℝ) * narayanaPolynomial 2 k := rfl

/-- The degree of the manuscript's auxiliary polynomial. -/
@[simp] theorem natDegree_auxiliary (k : ℕ) : (auxiliary k).natDegree = k := by
  rw [auxiliary, natDegree_C_mul (by positivity : (k + 4 : ℝ) ≠ 0),
    natDegree_narayanaPolynomial]

/-- The auxiliary polynomials split over the reals. -/
theorem auxiliary_splits (k : ℕ) : (auxiliary k).Splits :=
  (splits_narayanaPolynomial 2 k).C_mul _

/-- Every auxiliary polynomial has simple roots. -/
theorem auxiliary_hasSimpleRoots (k : ℕ) : HasSimpleRoots (auxiliary k) :=
  (narayanaPolynomial_hasSimpleRoots 2 k).C_mul (by positivity)

/-- Every root of an auxiliary polynomial is strictly negative. -/
theorem auxiliary_isRoot_neg {k : ℕ} {r : ℝ} (hr : (auxiliary k).IsRoot r) : r < 0 := by
  have hscale : (k + 4 : ℝ) ≠ 0 := by positivity
  have hroot : (narayanaPolynomial 2 k).IsRoot r := by
    simpa [auxiliary, Polynomial.IsRoot.def, hscale] using hr
  by_contra h
  exact (narayanaPolynomial_eval_pos_of_nonneg (by linarith) 2 k).ne' hroot

/-- Consecutive positive-degree auxiliary polynomials interlace. The separate
no-common-root theorem below makes this interlacing strict in the usual sense. -/
theorem auxiliary_interlaces_succ (k : ℕ) (hk : k ≠ 0) :
    Interlaces (auxiliary k) (auxiliary (k + 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  dsimp only [auxiliary]
  push_cast
  apply (((strictInterl_narayanaPolynomial_succ 2 n).C_mul_left
    (by positivity : (n + 1 + 4 : ℝ) ≠ 0)).C_mul_right
    (by positivity : (n + 1 + 1 + 4 : ℝ) ≠ 0)).toInterlaces
  simp only [natDegree_C_mul (by positivity : (n + 1 + 4 : ℝ) ≠ 0),
    natDegree_C_mul (by positivity : (n + 1 + 1 + 4 : ℝ) ≠ 0),
    natDegree_narayanaPolynomial]

/-- Consecutive auxiliary polynomials have no common real root. -/
theorem auxiliary_no_common_root (k : ℕ) (r : ℝ)
    (hr : (auxiliary (k + 1)).IsRoot r) : ¬ (auxiliary k).IsRoot r := by
  have hroot : (narayanaPolynomial 2 (k + 1)).IsRoot r := by
    simpa [auxiliary, Polynomial.IsRoot.def,
      (by positivity : (k + 1 + 4 : ℝ) ≠ 0)] using hr
  intro hprev
  apply narayanaPolynomial_no_common_root 2 k r hroot
  simpa [auxiliary, Polynomial.IsRoot.def,
    (by positivity : (k + 4 : ℝ) ≠ 0)] using hprev

/-- Corollary (coeff): the explicit binomial coefficient formula. -/
theorem coeff_auxiliary (k j : ℕ) (hj : j ≤ k) :
    (auxiliary k).coeff j =
      (k + 4 : ℝ) / (Nat.choose (k + 2) 2 : ℝ) *
        (Nat.choose (k + 2) j : ℝ) * (Nat.choose (k + 2) (k - j) : ℝ) := by
  rw [auxiliary, coeff_C_mul, coeff_narayanaPolynomial_of_le hj,
    narayanaTransformCoeff_eq_factorial 2 k j hj]
  rw [Nat.cast_choose ℝ (by lia : 2 ≤ k + 2),
    Nat.cast_choose ℝ (by lia : j ≤ k + 2),
    Nat.cast_choose ℝ (by lia : k - j ≤ k + 2)]
  rw [show k + 2 - 2 = k by lia, show k + 2 - (k - j) = 2 + j by lia]
  field_simp

/-- The three-term recurrence for the normalized auxiliary polynomials. -/
theorem auxiliary_recurrence (k : ℕ) :
    C ((k + 5 : ℝ) * (k + 4)) * auxiliary (k + 2) =
      C ((2 * k + 7 : ℝ) * (k + 4)) * ((1 + X) * auxiliary (k + 1)) -
        C ((k + 1 : ℝ) * (k + 5)) * ((1 - X) ^ 2 * auxiliary k) := by
  have h := narayanaPolynomial_pure_rec 2 k
  norm_num only [Nat.cast_ofNat] at h
  simp only [auxiliary, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, map_mul, map_add,
    C_ofNat, C_1] at h ⊢
  linear_combination ((C (k : ℝ) + 5) * (C (k : ℝ) + 4)) * h

/-- Palindromicity of the auxiliary polynomials, with the degree specified explicitly. -/
theorem reflect_auxiliary (k : ℕ) : (auxiliary k).reflect k = auxiliary k := by
  ext j
  rw [coeff_reflect]
  by_cases hj : j ≤ k
  · rw [revAt_le hj]
    simp only [auxiliary, coeff_C_mul]
    rw [coeff_narayanaPolynomial_sub 2 k j hj, coeff_narayanaPolynomial_of_le hj]
  · rw [revAt_eq_self_of_lt (by lia)]

/-- The recurrence-defined row `P_{n+1}` from the unpublished manuscript. The six
initial rows are prescribed explicitly. Later rows solve equation (Q), using
the auxiliary family whose recurrence is equation (rec). -/
def row : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 4 * X + X ^ 2
  | 3 => 1 + 10 * X + 10 * X ^ 2 + X ^ 3
  | 4 => 1 + 20 * X + 46 * X ^ 2 + 20 * X ^ 3 + X ^ 4
  | 5 => 1 + 35 * X + 147 * X ^ 2 + 147 * X ^ 3 + 35 * X ^ 4 + X ^ 5
  | n + 6 =>
      (3 * (1 + X)) * row (n + 5) +
        (4 * X - 3 * (1 + X) ^ 2) * row (n + 4) +
        ((1 + X) ^ 3 - 2 * X * (1 + X)) * row (n + 3) -
        (X * (1 - X) ^ 2) * row (n + 2) - X ^ 2 * auxiliary (n + 2)

/-- The manuscript's five-row combination `Q_{k+5}` for a row sequence. -/
def combination (p : ℕ → ℝ[X]) (k : ℕ) : ℝ[X] :=
  p (k + 4) - 3 * (1 + X) * p (k + 3) +
    (3 * (1 + X) ^ 2 - 4 * X) * p (k + 2) +
    (2 * X * (1 + X) - (1 + X) ^ 3) * p (k + 1) +
    X * (1 - X) ^ 2 * p k

/-- Equation (Q), identifying the auxiliary polynomial without division by `t²`. -/
theorem combination_eq (k : ℕ) : combination row k = -(X ^ 2 * auxiliary k) := by
  rcases k with _ | _ | k
  · simp [combination, row, auxiliary, narayanaPolynomial_zero_right, C_ofNat]
    ring
  · simp [combination, row, auxiliary, narayanaPolynomial_one, C_ofNat]
    ring
  · simp only [combination, row]
    ring

/-- Equation (rec) of the unpublished manuscript, with `n = k + 7`. -/
theorem combination_recurrence (k : ℕ) :
    C ((k + 5 : ℝ) * (k + 4)) * combination row (k + 2) =
      C ((2 * k + 7 : ℝ) * (k + 4)) * ((1 + X) * combination row (k + 1)) -
        C ((k + 1 : ℝ) * (k + 5)) * ((1 - X) ^ 2 * combination row k) := by
  simp only [combination_eq]
  linear_combination -(X ^ 2) * auxiliary_recurrence k

/-- The six prescribed initial rows, in ascending coefficient order. -/
theorem row_initial :
    row 0 = 1 ∧ row 1 = 1 + X ∧ row 2 = 1 + 4 * X + X ^ 2 ∧
      row 3 = 1 + 10 * X + 10 * X ^ 2 + X ^ 3 ∧
      row 4 = 1 + 20 * X + 46 * X ^ 2 + 20 * X ^ 3 + X ^ 4 ∧
      row 5 = 1 + 35 * X + 147 * X ^ 2 + 147 * X ^ 3 + 35 * X ^ 4 + X ^ 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The six initial rows and equations (Q), (rec) uniquely determine the family.
Thus the construction through generalized Narayana polynomials defines exactly
the recurrence family of the unpublished manuscript. -/
theorem eq_row_of_recurrence (p : ℕ → ℝ[X])
    (hinit : ∀ n < 6, p n = row n)
    (hrec : ∀ k : ℕ,
      C ((k + 5 : ℝ) * (k + 4)) * combination p (k + 2) =
        C ((2 * k + 7 : ℝ) * (k + 4)) * ((1 + X) * combination p (k + 1)) -
          C ((k + 1 : ℝ) * (k + 5)) * ((1 - X) ^ 2 * combination p k)) :
    p = row := by
  funext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      by_cases hn : n < 6
      · exact hinit n hn
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by lia⟩
        have hprev (j : ℕ) (hj : j ≤ k + 1) : combination p j = combination row j := by
          simp only [combination]
          rw [ih (j + 4) (by lia), ih (j + 3) (by lia), ih (j + 2) (by lia),
            ih (j + 1) (by lia), ih j (by lia)]
        have h := hrec k
        rw [hprev (k + 1) le_rfl, hprev k (by lia)] at h
        have hq : combination p (k + 2) = combination row (k + 2) :=
          mul_left_cancel₀ (C_ne_zero.mpr (by positivity))
            (h.trans (combination_recurrence k).symm)
        simp only [combination] at hq
        rw [ih (k + 2 + 3) (by lia), ih (k + 2 + 2) (by lia),
          ih (k + 2 + 1) (by lia), ih (k + 2) (by lia)] at hq
        linear_combination hq

/-- The reciprocal-variable form of palindromicity for the auxiliary polynomial. -/
theorem auxiliary_palindromic (k : ℕ) (t : ℝ) (ht : t ≠ 0) :
    (auxiliary k).eval t = t ^ k * (auxiliary k).eval (1 / t) := by
  let : Invertible t := invertibleOfNonzero ht
  have h := eval₂_reflect_mul_pow (RingHom.id ℝ) t k (auxiliary k) (by simp)
  simpa [reflect_auxiliary, invOf_eq_inv, mul_comm] using h.symm

/-- The manuscript's palindromicity identity: `P_{n+1}(t) = t^n P_{n+1}(1/t)`.
The nonzero condition is the domain condition for the reciprocal substitution. -/
theorem row_palindromic (n : ℕ) (t : ℝ) (ht : t ≠ 0) :
    (row n).eval t = t ^ n * (row n).eval (1 / t) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      by_cases hn : n < 6
      · interval_cases n <;> norm_num [row] <;> field_simp <;> ring
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by lia⟩
        simp only [row, eval_sub, eval_add, eval_mul, eval_pow, eval_ofNat, eval_one, eval_X]
        rw [ih (k + 5) (by lia), ih (k + 4) (by lia), ih (k + 3) (by lia),
          ih (k + 2) (by lia), auxiliary_palindromic (k + 2) t ht]
        simp only [pow_add]
        field_simp
        ring

/-- The recurrence row `P_{n+1}` has no coefficient above degree `n`. -/
theorem natDegree_row_le (n : ℕ) : (row n).natDegree ≤ n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      by_cases hn : n < 6
      · interval_cases n <;> simp only [row] <;> compute_degree
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by lia⟩
        rw [row]
        refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
          · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
            · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
              · exact (natDegree_mul_le_of_le (by compute_degree :
                  (3 * (1 + X) : ℝ[X]).natDegree ≤ 1) (ih (k + 5) (by lia))).trans
                    (by lia)
              · exact (natDegree_mul_le_of_le (by compute_degree :
                  (4 * X - 3 * (1 + X) ^ 2 : ℝ[X]).natDegree ≤ 2)
                    (ih (k + 4) (by lia))).trans (by lia)
            · exact (natDegree_mul_le_of_le (by compute_degree :
                ((1 + X) ^ 3 - 2 * X * (1 + X) : ℝ[X]).natDegree ≤ 3)
                  (ih (k + 3) (by lia))).trans (by lia)
          · exact (natDegree_mul_le_of_le (by compute_degree :
              (X * (1 - X) ^ 2 : ℝ[X]).natDegree ≤ 3)
                (ih (k + 2) (by lia))).trans (by lia)
        · exact (natDegree_mul_le_of_le (natDegree_X_pow_le 2)
            (le_of_eq (natDegree_auxiliary (k + 2)))).trans (by lia)

/-- Polynomial palindromicity of `P_{n+1}`, including its degree bound. -/
theorem reflect_row (n : ℕ) : (row n).reflect n = row n := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (a := (0 : ℝ))).mono
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  let : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht0)
  have h := eval₂_reflect_mul_pow (RingHom.id ℝ) t⁻¹ n (row n) (natDegree_row_le n)
  have hp := row_palindromic n t⁻¹ (inv_ne_zero ht0)
  simp only [eval₂_id, invOf_eq_inv, inv_inv, one_div] at h hp
  exact mul_right_cancel₀ (pow_ne_zero n (inv_ne_zero ht0))
    (by simpa only [mul_comm] using h.trans hp)

/-- Coefficients of `P_{n+1}` are symmetric about `n/2`. -/
theorem coeff_row_symm (n j : ℕ) (hj : j ≤ n) :
    (row n).coeff j = (row n).coeff (n - j) := by
  have h := congrArg (fun p : ℝ[X] => p.coeff j) (reflect_row n)
  simpa only [coeff_reflect, revAt_le hj] using h.symm

/-- Corollary (coeff), root part: exactly `k` simple negative roots. -/
theorem auxiliary_roots (k : ℕ) :
    (auxiliary k).roots.card = k ∧ (auxiliary k).roots.Nodup ∧
      ∀ r ∈ (auxiliary k).roots, r < 0 := by
  refine ⟨?_, (auxiliary_hasSimpleRoots k).roots_nodup, ?_⟩
  · rw [← (auxiliary_splits k).natDegree_eq_card_roots, natDegree_auxiliary]
  · intro r hr
    exact auxiliary_isRoot_neg (isRoot_of_mem_roots hr)

/-- Corollary (coeff), strict interlacing part. `Interlaces` together with
absence of common roots expresses strict, rather than weak, interlacing. -/
theorem auxiliary_strict_interlacing (k : ℕ) (hk : k ≠ 0) :
    Interlaces (auxiliary k) (auxiliary (k + 1)) ∧
      ∀ r : ℝ, ¬ ((auxiliary k).IsRoot r ∧ (auxiliary (k + 1)).IsRoot r) := by
  exact ⟨auxiliary_interlaces_succ k hk,
    fun r hr => auxiliary_no_common_root k r hr.2 hr.1⟩

end RealRooted.SmoothPermutationDescents
