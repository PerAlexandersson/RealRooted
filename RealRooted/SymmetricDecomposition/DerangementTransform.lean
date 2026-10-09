import RealRooted.BrandenVecchi.ChowResolutionInterlacing
import RealRooted.CombinatorialExamples.SturmDerangementsExc
import RealRooted.GeneralizedEulerian
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform

/-!
# The deranged transform on the magic basis

The deranged map `D : X ^ j ↦ d_j` of Brändén--Solus, Section 3.2, where `d_j` is the
excedance derangement polynomial, is the Chow-deranged transform of the Pascal matrix.
The magic basis `X ^ k * (1 + X) ^ (d - k)` is the Pascal resolution, so the
Brändén--Vecchi Chow resolution theorems give Brändén--Solus, Corollary 3.7, for
nonnegative magic-basis coordinates.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted
namespace DerangementTransform

/-- The excedance derangement polynomial sequence, with `d 0 = 1`. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => sturmDerangementsExc (n + 1)

/-- `d_0 = 1`. -/
@[simp]
theorem polynomial_zero : polynomial 0 = 1 := rfl

/-- `d_1 = 0`. -/
@[simp]
theorem polynomial_one : polynomial 1 = 0 := rfl

/-- `d_2 = X`. -/
@[simp]
theorem polynomial_two : polynomial 2 = X := by
  simp [polynomial]

/-- The recurrence for the derangement excedance polynomials. -/
theorem polynomial_recurrence (n : ℕ) :
    polynomial (n + 3) =
      X * (((n + 2 : ℝ[X])) * polynomial (n + 1) +
        ((n + 2 : ℝ[X])) * polynomial (n + 2) +
        (1 - X) * (polynomial (n + 2)).derivative) := by
  simpa [polynomial] using sturmDerangementsExc_recurrence n

/-- The derangement recurrence in a form valid for every index. -/
theorem polynomial_succ (j : ℕ) :
    polynomial (j + 1) =
      X * (C (j : ℝ) * (polynomial (j - 1) + polynomial j) +
        (1 - X) * (polynomial j).derivative) := by
  rcases j with _ | _ | n
  · simp
  · simp
  · change polynomial (n + 3) = X * (C ((n + 2 : ℕ) : ℝ) *
      (polynomial (n + 1) + polynomial (n + 2)) + (1 - X) * (polynomial (n + 2)).derivative)
    rw [polynomial_recurrence n]
    simp only [Nat.cast_add, Nat.cast_ofNat, map_add, map_natCast, map_ofNat]
    ring

/-- The linear deranged map, characterized by `X ^ n ↦ d n`. -/
def transform : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := Polynomial.basisTransform polynomial
  map_add' := Polynomial.basisTransform_add polynomial
  map_smul' a p := by
    simpa [Polynomial.smul_eq_C_mul] using
      Polynomial.basisTransform_smul polynomial a p

/-- The deranged map sends `X ^ n` to `d_n`. -/
@[simp]
theorem transform_X_pow (n : ℕ) : transform (X ^ n) = polynomial n := by
  simp [transform]

/-- The deranged map commutes with constant multiples. -/
@[simp]
theorem transform_C_mul (a : ℝ) (p : ℝ[X]) :
    transform (C a * p) = C a * transform p := by
  rw [← Polynomial.smul_eq_C_mul, LinearMap.map_smul,
    Polynomial.smul_eq_C_mul]

/-- The operator identity `D (X p) = X (D ((1 + X) p') + (1 - X) (D p)')`. -/
theorem transform_X_mul (p : ℝ[X]) :
    transform (X * p) =
      X * (transform ((1 + X) * p.derivative) + (1 - X) * (transform p).derivative) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [mul_add, map_add, hp, hq]
    ring
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, derivative_C_mul_X_pow]
    rcases n with _ | m
    · have h0 : X * (C a * X ^ 0) = C a * X ^ 1 := by ring
      rw [h0, transform_C_mul, transform_C_mul, transform_X_pow, transform_X_pow]
      simp
    · have h1 : X * (C a * X ^ (m + 1)) = C a * X ^ (m + 2) := by ring
      have h2 : (1 + X) * (C (a * ((m + 1 : ℕ) : ℝ)) * X ^ (m + 1 - 1)) =
          C (a * ((m + 1 : ℕ) : ℝ)) * (X ^ m + X ^ (m + 1)) := by
        simp only [Nat.add_sub_cancel]
        ring
      rw [h1, h2, transform_C_mul, transform_C_mul, transform_C_mul, map_add]
      simp only [transform_X_pow, derivative_mul, derivative_C, zero_mul, zero_add]
      rw [show m + 2 = (m + 1) + 1 by rfl, polynomial_succ (m + 1)]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, map_mul, map_add, map_one]
      ring

/-- The deranged map fixes `1`. -/
@[simp]
theorem transform_one : transform 1 = 1 := by
  simpa using transform_X_pow 0

private theorem one_add_X_mul_derivative_pow (m : ℕ) :
    (1 + X : ℝ[X]) * ((1 + X) ^ m).derivative = C (m : ℝ) * (1 + X) ^ m := by
  rcases m with _ | m
  · simp
  · simp only [derivative_pow, derivative_one, derivative_X, zero_add, mul_one,
      Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, map_add, map_one, map_natCast]
    ring

/-- The Eulerian recurrence for the deranged image of a power of `1 + X`. -/
theorem transform_one_add_X_pow_succ (m : ℕ) :
    transform ((1 + X) ^ (m + 1)) =
      (1 + C (m : ℝ) * X) * transform ((1 + X) ^ m) +
        X * (1 - X) * (transform ((1 + X) ^ m)).derivative := by
  have h : (1 + X : ℝ[X]) ^ (m + 1) = (1 + X) ^ m + X * (1 + X) ^ m := by ring
  rw [h, map_add, transform_X_mul, one_add_X_mul_derivative_pow, transform_C_mul]
  ring

/-- The deranged image of `(1 + X) ^ (n + 1)` is the Eulerian polynomial. -/
theorem transform_one_add_X_pow_succ_eq (n : ℕ) :
    transform ((1 + X) ^ (n + 1)) = generalizedEulerian 1 n := by
  induction n with
  | zero =>
    rw [transform_one_add_X_pow_succ, pow_zero, transform_one]
    simp [generalizedEulerian]
  | succ n ih =>
    rw [transform_one_add_X_pow_succ, ih, generalizedEulerian_succ]
    simp only [map_add, map_natCast, Nat.cast_add, Nat.cast_one, one_mul, map_one]

/-- The Pascal matrix. -/
def pascal : LowerTriangularMatrix ℝ := fun n k => (n.choose k : ℝ)

private theorem one_add_X_pow_eq_sum (n : ℕ) :
    (1 + X : ℝ[X]) ^ n = ∑ k ∈ Finset.range (n + 1), C (pascal n k) * X ^ k := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [pascal, mul_comm]

/-- The Chow-derangement sequence of the Pascal matrix is the excedance derangement sequence. -/
theorem chowDerangement_pascal :
    BrandenVecchi.chowDerangement pascal = polynomial := by
  symm
  refine (BrandenVecchi.chowDerangement_chowPolynomial_unique pascal
    (fun n => by simp [pascal]) polynomial (fun n => transform ((1 + X) ^ n))
    rfl ?_ ?_ ?_ ?_).1
  · intro n
    cases n with
    | zero => simp [polynomial]
    | succ n => simpa [polynomial] using reflect_sturmDerangementsExc (n + 1)
  · intro n
    change (transform ((1 + X) ^ (n + 1))).reflect (n + 1) = X * transform ((1 + X) ^ (n + 1))
    rw [transform_one_add_X_pow_succ_eq,
      reflect_add_right_of_reflect 1 (generalizedEulerian_natDegree 1 n).le
        (generalizedEulerian_one_reflect n)]
    ring
  · intro n
    rw [one_add_X_pow_eq_sum, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [transform_C_mul, transform_X_pow]
  · intro n
    cases n with
    | zero => simp [polynomial]
    | succ n => simpa [polynomial] using natDegree_le_sturmDerangementsExc (n + 1)

/-- The Chow-deranged transform of the Pascal matrix is the deranged map. -/
theorem chowDerangedTransform_pascal :
    BrandenVecchi.chowDerangedTransform pascal = transform := by
  refine LinearMap.ext fun p => ?_
  change basisTransform (BrandenVecchi.chowDerangement pascal) p = basisTransform polynomial p
  rw [chowDerangement_pascal]

/-- The magic basis `X ^ k * (1 + X) ^ (d - k)` of degree `d` is a resolution of the Pascal
matrix, with all weights equal to one. -/
def pascalResolution : BrandenLeite.Resolution pascal where
  lowerUnitriangular :=
    ⟨fun {i j} h => by simp [pascal, Nat.choose_eq_zero_of_lt h], fun n => by simp [pascal]⟩
  lambda := fun _ _ => 1
  polynomial := fun n k => X ^ k * (1 + X) ^ (n - k)
  lambda_nonneg := fun _ _ _ => zero_le_one
  monic := fun n k _ => by
    have h : (1 + X : ℝ[X]).Monic := by
      rw [add_comm]
      exact monic_X_add_C 1
    exact (monic_X_pow k).mul (h.pow _)
  row_zero := fun n => by
    simpa [LowerTriangularMatrix.rowPolynomial] using one_add_X_pow_eq_sum n
  diagonal := fun n => by simp
  dvd_X_pow := fun n k _ => dvd_mul_right _ _
  recurrence := fun n k hk => by
    simp only [map_one, one_mul]
    rw [show n + 1 - k = (n - k) + 1 by lia, show n + 1 - (k + 1) = n - k by lia]
    ring

/-- The degree-`d` magic-basis expansion with coefficients `c`. -/
def magicExpansion (d : ℕ) (c : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1), C (c k) * (X ^ k * (1 + X) ^ (d - k))

/-- **Brändén--Solus, Corollary 3.7** (Pólya frequency part): the deranged image of a
nonnegative combination `∑ c_k X^k (1 + X)^(d-k)` is zero or real-rooted with nonnegative
coefficients and only nonpositive roots. The zero case happens only for `d = 1` or when all
`c_k` vanish, see `transform_magicExpansion_ne_zero`. -/
theorem transform_magicExpansion_isPF {d : ℕ} {c : ℕ → ℝ}
    (hc : ∀ k, k ≤ d → 0 ≤ c k) :
    IsPFPolynomial (transform (magicExpansion d c)) := by
  have h := BrandenVecchi.chowDerangedTransform_resolvingRowCombination_isPF
    pascalResolution hc
  rwa [chowDerangedTransform_pascal] at h

/-- **Brändén--Solus, Corollary 3.7** (endpoint interlacing): `A_d ≺ D f ≺ d_d` in the
zero-aware interlacing order, where `A_d = D ((1 + X) ^ d)` is the Eulerian polynomial. -/
theorem transform_magicExpansion_interl {d : ℕ} {c : ℕ → ℝ}
    (hc : ∀ k, k ≤ d → 0 ≤ c k) :
    Interl (transform ((1 + X) ^ d)) (transform (magicExpansion d c)) ∧
      Interl (transform (magicExpansion d c)) (polynomial d) := by
  have h := BrandenVecchi.chowPolynomial_resolvingRowCombination_endpoint_interl
    pascalResolution hc
  have hrow : BrandenVecchi.chowPolynomial pascal d = transform ((1 + X) ^ d) := by
    rw [← BrandenVecchi.chowDerangedTransform_rowPolynomial, chowDerangedTransform_pascal]
    congr 1
    simpa [LowerTriangularMatrix.rowPolynomial] using (one_add_X_pow_eq_sum d).symm
  rw [hrow, chowDerangedTransform_pascal, chowDerangement_pascal] at h
  exact h

/-- The deranged map fixes constants. -/
@[simp]
theorem transform_C (a : ℝ) : transform (C a) = C a := by
  simpa using transform_C_mul a 1

/-- The deranged map kills `X`. -/
@[simp]
theorem transform_X : transform X = 0 := by
  simpa using transform_X_pow 1

/-- For `d ≤ 1` the deranged image of a magic-basis expansion is the constant `c 0`. -/
theorem transform_magicExpansion_of_le_one {d : ℕ} (hd : d ≤ 1) (c : ℕ → ℝ) :
    transform (magicExpansion d c) = C (c 0) := by
  interval_cases d
  · simp [magicExpansion]
  · simp [magicExpansion, Finset.sum_range_succ]

private theorem hasNonnegCoeffs_polynomial (n : ℕ) : HasNonnegCoeffs (polynomial n) := by
  cases n with
  | zero => simpa [polynomial] using hasNonnegCoeffs_one
  | succ n => simpa [polynomial] using sturmDerangementsExc_nonnegCoeffs (n + 1)

private theorem eval_one_nonneg_of_nonnegCoeffs {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    0 ≤ p.eval 1 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact (eval_pos_of_hasNonnegCoeffs hp hp0 one_pos).le

private theorem transform_X_pow_mul_one_add_X_pow (k m : ℕ) :
    transform (X ^ k * (1 + X) ^ m) =
      ∑ i ∈ Finset.range (m + 1), C (m.choose i : ℝ) * polynomial (k + i) := by
  have h := one_add_X_pow_eq_sum m
  rw [h, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, ← pow_add, transform_C_mul, transform_X_pow]
  simp [pascal]

private theorem polynomial_eval_one_le_transform {d : ℕ} {k : ℕ} (hk : k ≤ d) :
    (polynomial d).eval 1 ≤ (transform (X ^ k * (1 + X) ^ (d - k))).eval 1 := by
  rw [transform_X_pow_mul_one_add_X_pow, eval_finsetSum]
  have hmem : d - k ∈ Finset.range (d - k + 1) := Finset.self_mem_range_succ _
  have hterm := Finset.single_le_sum (f := fun i => (C ((d - k).choose i : ℝ) *
      polynomial (k + i)).eval 1) (fun i _ => by
        rw [eval_mul, eval_C]
        exact mul_nonneg (Nat.cast_nonneg _)
          (eval_one_nonneg_of_nonnegCoeffs (hasNonnegCoeffs_polynomial _))) hmem
  simpa [show k + (d - k) = d by lia] using hterm

/-- For `2 ≤ d`, a nonnegative magic-basis combination with some positive coordinate has a
nonzero deranged image. For `d ≤ 1` see `transform_magicExpansion_of_le_one`. -/
theorem transform_magicExpansion_ne_zero {d : ℕ} (hd : 2 ≤ d) {c : ℕ → ℝ}
    (hc : ∀ k, k ≤ d → 0 ≤ c k) (hpos : ∃ k, k ≤ d ∧ 0 < c k) :
    transform (magicExpansion d c) ≠ 0 := by
  obtain ⟨k₀, hk₀, hck₀⟩ := hpos
  have hdne : polynomial d ≠ 0 := by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by lia⟩
    simpa [polynomial] using (monic_sturmDerangementsExc (n := n + 2) (by lia)).ne_zero
  have hdpos : 0 < (polynomial d).eval 1 :=
    eval_pos_of_hasNonnegCoeffs (hasNonnegCoeffs_polynomial d) hdne one_pos
  intro h0
  have h1 : (transform (magicExpansion d c)).eval 1 = 0 := by simp [h0]
  have h2 : (transform (magicExpansion d c)).eval 1 =
      ∑ k ∈ Finset.range (d + 1), c k * (transform (X ^ k * (1 + X) ^ (d - k))).eval 1 := by
    simp [magicExpansion, map_sum, eval_finsetSum]
  have hnn : ∀ k ∈ Finset.range (d + 1),
      0 ≤ c k * (transform (X ^ k * (1 + X) ^ (d - k))).eval 1 := by
    intro k hk
    have hkd : k ≤ d := by simpa [Nat.lt_succ_iff] using hk
    exact mul_nonneg (hc k hkd) (hdpos.le.trans (polynomial_eval_one_le_transform hkd))
  have hle := Finset.single_le_sum hnn (Finset.mem_range_succ_iff.mpr hk₀)
  have hlt : 0 < c k₀ * (transform (X ^ k₀ * (1 + X) ^ (d - k₀))).eval 1 :=
    mul_pos hck₀ (hdpos.trans_le (polynomial_eval_one_le_transform hk₀))
  rw [← h2, h1] at hle
  exact absurd hlt (not_lt.mpr hle)

/-- **Brändén--Solus, Corollary 3.7**, strict form: for `2 ≤ d` and a nonnegative magic-basis
combination `f` with some positive coordinate, `A_d ≺ D f ≺ d_d` strictly, where
`A_d = D ((1 + X) ^ d)`. -/
theorem transform_magicExpansion_strictInterl {d : ℕ} (hd : 2 ≤ d) {c : ℕ → ℝ}
    (hc : ∀ k, k ≤ d → 0 ≤ c k) (hpos : ∃ k, k ≤ d ∧ 0 < c k) :
    StrictInterl (transform ((1 + X) ^ d)) (transform (magicExpansion d c)) ∧
      StrictInterl (transform (magicExpansion d c)) (polynomial d) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by lia⟩
  have hA : transform ((1 + X) ^ (n + 1)) ≠ 0 := by
    rw [transform_one_add_X_pow_succ_eq]
    exact (generalizedEulerian_degree_and_monic 1 n).2.ne_zero
  have hdne : polynomial (n + 1) ≠ 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
    simpa [polynomial] using (monic_sturmDerangementsExc (n := m + 2) (by lia)).ne_zero
  have hf := transform_magicExpansion_ne_zero hd hc hpos
  have h := transform_magicExpansion_interl hc
  exact ⟨h.1.toStrictInterl_of_ne hA hf, h.2.toStrictInterl_of_ne hf hdne⟩

end DerangementTransform
end RealRooted
