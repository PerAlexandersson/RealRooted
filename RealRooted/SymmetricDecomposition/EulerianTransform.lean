import RealRooted.BrandenVecchi.ChowResolutionInterlacing
import RealRooted.Derivative.Interlacing
import RealRooted.GeneralizedEulerian
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform

/-!
# The Eulerian transformation on the magic basis

The Eulerian transformation `A°` of Brändén--Jochemko sends `1 ↦ 1` and
`X ^ n ↦ X * A_n` for `n ≥ 1`, where `A_n = generalizedEulerian 1 (n - 1)` is the Eulerian
polynomial (descent and excedance convention). Athanasiadis, *On the real-rootedness of the
Eulerian transformation*, Theorem 1.1, shows that `A°` sends every nonnegative combination of
the magic basis `X ^ k * (1 + X) ^ (d - k)` to a real-rooted polynomial interlaced by
`A°((1 + X) ^ d)` and `X * A_d`.

We prove this with the Chow row transform of Brändén--Vecchi (Theorem 4.13): the image row
`A°(X ^ k * (1 + X) ^ (n - k))` is reflection-interlacing with respect to `n + 1`, and the next
row is the staircase transform of the previous one with reflection bound `n + 1`.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted
namespace EulerianTransform

/-- The images `A°(X ^ n)`: `1` for `n = 0` and `X * A_n` otherwise, where
`A_n = generalizedEulerian 1 (n - 1)`. -/
def image : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X * generalizedEulerian 1 n

/-- The Eulerian transformation `A°`, the linear map with `A°(X ^ n) = image n`. -/
def transform : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := Polynomial.basisTransform image
  map_add' := Polynomial.basisTransform_add image
  map_smul' a p := by
    simpa [Polynomial.smul_eq_C_mul] using Polynomial.basisTransform_smul image a p

/-- `A°(X ^ n) = image n`. -/
@[simp]
theorem transform_X_pow (n : ℕ) : transform (X ^ n) = image n := by
  simp [transform]

/-- `A°` commutes with constant multiples. -/
@[simp]
theorem transform_C_mul (a : ℝ) (p : ℝ[X]) :
    transform (C a * p) = C a * transform p := by
  rw [← Polynomial.smul_eq_C_mul, LinearMap.map_smul, Polynomial.smul_eq_C_mul]

/-- `A°(1) = 1`. -/
@[simp]
theorem transform_one : transform 1 = 1 := by
  simpa [image] using transform_X_pow 0

/-- `A°(C a) = C a`. -/
@[simp]
theorem transform_C (a : ℝ) : transform (C a) = C a := by
  simpa using transform_C_mul a 1

/-- `A°(X) = X`. -/
@[simp]
theorem transform_X : transform X = X := by
  simpa [image, generalizedEulerian] using transform_X_pow 1

/-- The operator identity `A°(X p) = X (A° p + (1 - X) (A° p)' + A°(X p'))`. -/
theorem transform_X_mul (p : ℝ[X]) :
    transform (X * p) =
      X * (transform p + (1 - X) * (transform p).derivative + transform (X * p.derivative)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [mul_add, map_add, hp, hq]
    ring
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, derivative_C_mul_X_pow]
    rcases n with _ | m
    · have h0 : X * (C a * X ^ 0) = C a * X ^ 1 := by ring
      rw [h0]
      simp
    · have h1 : X * (C a * X ^ (m + 1)) = C a * X ^ (m + 2) := by ring
      have h2 : X * (C (a * ((m + 1 : ℕ) : ℝ)) * X ^ (m + 1 - 1)) =
          C (a * ((m + 1 : ℕ) : ℝ)) * X ^ (m + 1) := by
        simp only [Nat.add_sub_cancel]
        ring
      rw [h1, h2, transform_C_mul, transform_C_mul, transform_C_mul]
      simp only [transform_X_pow, image, derivative_mul, derivative_C, zero_mul, zero_add,
        derivative_X, one_mul, generalizedEulerian_succ]
      simp only [Nat.cast_add, Nat.cast_one, map_mul, map_add, map_one, map_natCast, one_mul,
        ]
      ring

/-- The binomial Eulerian polynomial `A°((1 + X) ^ N)`. -/
def binomial (N : ℕ) : ℝ[X] := transform ((1 + X) ^ N)

/-- `A°(1) = 1`. -/
@[simp]
theorem binomial_zero : binomial 0 = 1 := by simp [binomial]

/-- `A°(1 + X) = 1 + X`. -/
@[simp]
theorem binomial_one : binomial 1 = 1 + X := by simp [binomial]

/-- The three-term recurrence of the binomial Eulerian polynomials. -/
theorem binomial_succ_succ (N : ℕ) :
    binomial (N + 2) =
      (1 + X) * binomial (N + 1) + X * (1 - X) * (binomial (N + 1)).derivative +
        C ((N + 1 : ℕ) : ℝ) * X * (binomial (N + 1) - binomial N) := by
  have h : (1 + X : ℝ[X]) ^ (N + 2) = (1 + X) ^ (N + 1) + X * (1 + X) ^ (N + 1) := by ring
  have h' : X * derivative ((1 + X : ℝ[X]) ^ (N + 1)) =
      C ((N + 1 : ℕ) : ℝ) * ((1 + X) ^ (N + 1) - (1 + X) ^ N) := by
    rw [derivative_pow]
    simp only [Nat.add_sub_cancel, derivative_add, derivative_one, derivative_X, zero_add,
      mul_one]
    ring
  unfold binomial
  rw [h, map_add, transform_X_mul, h', transform_C_mul, map_sub]
  ring

/-- For a polynomial that is symmetric with respect to `N + 1`, the reflection of its
derivative at `N` is `(N + 1) p - X p'`. -/
theorem reflect_derivative_of_reflect_eq {p : ℝ[X]} {N : ℕ} (hdeg : p.natDegree ≤ N + 1)
    (hrefl : p.reflect (N + 1) = p) :
    p.derivative.reflect N = C ((N + 1 : ℕ) : ℝ) * p - X * p.derivative := by
  have hsym : ∀ i, i ≤ N + 1 → p.coeff (N + 1 - i) = p.coeff i := by
    intro i hi
    have := congrArg (fun q => q.coeff i) hrefl
    simpa [coeff_reflect, revAt_le hi] using this
  ext j
  rw [coeff_reflect, coeff_sub, coeff_C_mul]
  have hX : (X * p.derivative).coeff j = j * p.coeff j := by
    rcases j with _ | j
    · simp
    · rw [coeff_X_mul, coeff_derivative]
      push_cast
      ring
  rw [hX]
  by_cases hj : j ≤ N
  · rw [revAt_le hj, coeff_derivative]
    have h1 : N - j + 1 = N + 1 - j := by lia
    rw [h1, hsym j (by lia)]
    rw [Nat.cast_sub hj]
    push_cast
    ring
  · rw [revAt_eq_self_of_lt (by lia), coeff_derivative]
    by_cases hj' : j = N + 1
    · subst hj'
      rw [coeff_eq_zero_of_natDegree_lt (by lia : p.natDegree < N + 1 + 1)]
      simp
    · rw [coeff_eq_zero_of_natDegree_lt (by lia : p.natDegree < j + 1),
        coeff_eq_zero_of_natDegree_lt (by lia : p.natDegree < j)]
      simp

private theorem reflect_one_one_add_X : reflect 1 (1 + X : ℝ[X]) = 1 + X := by
  rw [reflect_add, add_comm]
  simp

private theorem reflect_one_X : reflect 1 (X : ℝ[X]) = 1 := by
  simp

private theorem reflect_two_X_mul_one_sub_X : reflect 2 (X * (1 - X) : ℝ[X]) = X - 1 := by
  have h : reflect 2 (X : ℝ[X]) = X := by
    have := reflect_monomial (R := ℝ) 2 1
    rw [pow_one, revAt_le (by norm_num : 1 ≤ 2)] at this
    simpa using this
  rw [show (X * (1 - X) : ℝ[X]) = X - X ^ 2 by ring, reflect_sub, h]
  simp

private theorem natDegree_one_add_X_le : (1 + X : ℝ[X]).natDegree ≤ 1 := by compute_degree

private theorem natDegree_X_mul_one_sub_X_le : (X * (1 - X) : ℝ[X]).natDegree ≤ 2 := by
  compute_degree

/-- The binomial Eulerian polynomial `A°((1 + X) ^ N)` has degree at most `N` and is
symmetric with respect to `N`. -/
theorem natDegree_binomial_le_and_reflect (N : ℕ) :
    ((binomial N).natDegree ≤ N ∧ (binomial N).reflect N = binomial N) ∧
      ((binomial (N + 1)).natDegree ≤ N + 1 ∧
        (binomial (N + 1)).reflect (N + 1) = binomial (N + 1)) := by
  induction N with
  | zero =>
    refine ⟨⟨by simp, by simp⟩, ?_, ?_⟩
    · rw [binomial_one]
      exact natDegree_one_add_X_le
    · rw [binomial_one]
      exact reflect_one_one_add_X
  | succ N ih =>
    obtain ⟨⟨hHd, hHr⟩, ⟨hGd, hGr⟩⟩ := ih
    refine ⟨⟨hGd, hGr⟩, ?_, ?_⟩
    · rw [binomial_succ_succ]
      have h1 : ((1 + X) * binomial (N + 1)).natDegree ≤ N + 2 :=
        natDegree_mul_le.trans (by have := natDegree_one_add_X_le; lia)
      have h2 : (X * (1 - X) * (binomial (N + 1)).derivative).natDegree ≤ N + 2 := by
        refine natDegree_mul_le.trans ?_
        have := natDegree_derivative_le (binomial (N + 1))
        have := natDegree_X_mul_one_sub_X_le
        lia
      have h3 : (C ((N + 1 : ℕ) : ℝ) * X * (binomial (N + 1) - binomial N)).natDegree ≤
          N + 2 := by
        refine natDegree_mul_le.trans ?_
        have h4 : (binomial (N + 1) - binomial N).natDegree ≤ N + 1 :=
          (natDegree_sub_le _ _).trans (max_le hGd (by lia))
        have h5 : (C ((N + 1 : ℕ) : ℝ) * X).natDegree ≤ 1 := by compute_degree
        lia
      exact (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans
        (max_le h1 h2)) h3)
    · rw [binomial_succ_succ]
      generalize binomial (N + 1) = g at *
      generalize binomial N = h at *
      have hg' : g.derivative.reflect N =
          C ((N + 1 : ℕ) : ℝ) * g - X * g.derivative :=
        reflect_derivative_of_reflect_eq hGd hGr
      have hdg' : g.derivative.natDegree ≤ N := by
        have := natDegree_derivative_le g
        lia
      have e1 : reflect (N + 2) ((1 + X) * g) = (1 + X) * g := by
        have := reflect_mul (1 + X) g (F := 1) (G := N + 1) natDegree_one_add_X_le hGd
        rw [show 1 + (N + 1) = N + 2 by lia, reflect_one_one_add_X, hGr] at this
        exact this
      have e2 : reflect (N + 2) (X * (1 - X) * g.derivative) =
          (X - 1) * (C ((N + 1 : ℕ) : ℝ) * g - X * g.derivative) := by
        have := reflect_mul (X * (1 - X)) g.derivative (F := 2) (G := N)
          natDegree_X_mul_one_sub_X_le hdg'
        rw [show 2 + N = N + 2 by lia, reflect_two_X_mul_one_sub_X, hg'] at this
        exact this
      have e3a : reflect (N + 2) (X * g) = g := by
        have := reflect_mul X g (F := 1) (G := N + 1) natDegree_X_le hGd
        rw [show 1 + (N + 1) = N + 2 by lia, reflect_one_X, hGr, one_mul] at this
        exact this
      have e3b : reflect (N + 2) (X * h) = X * h := by
        have := reflect_mul X h (F := 1) (G := N + 1) natDegree_X_le (hHd.trans (by lia))
        rw [show 1 + (N + 1) = N + 2 by lia, reflect_one_X, one_mul,
          reflect_add_right_of_reflect 1 hHd hHr] at this
        rw [this]
        ring
      have e3 : reflect (N + 2) (C ((N + 1 : ℕ) : ℝ) * X * (g - h)) =
          C ((N + 1 : ℕ) : ℝ) * (g - X * h) := by
        rw [show C ((N + 1 : ℕ) : ℝ) * X * (g - h) =
          C ((N + 1 : ℕ) : ℝ) * (X * g - X * h) by ring, reflect_C_mul, reflect_sub, e3a, e3b]
      rw [reflect_add, reflect_add, e1, e2, e3]
      ring

/-- The telescoping expansion of the magic basis. -/
theorem pascal_telescope (n : ℕ) {k : ℕ} (hk : k ≤ n + 1) :
    (X : ℝ[X]) ^ k * (1 + X) ^ (n + 1 - k) =
      X ^ (n + 1) + ∑ j ∈ Finset.Ico k (n + 1), X ^ j * (1 + X) ^ (n - j) := by
  induction hk using Nat.decreasingInduction with
  | self => simp
  | of_succ k hk ih =>
    have hkn : k ≤ n := by lia
    rw [Finset.sum_eq_sum_Ico_succ_bot hk, ← add_assoc, add_comm (X ^ (n + 1)), add_assoc, ← ih,
      show n + 1 - k = (n - k) + 1 by lia, show n + 1 - (k + 1) = n - k by lia]
    ring

/-- The image of the `j`-th magic basis element of degree `n`. -/
def basisImage (n j : ℕ) : ℝ[X] := transform (X ^ j * (1 + X) ^ (n - j))

/-- The row of images of the degree-`n` magic basis. -/
def row (n : ℕ) : List ℝ[X] := (List.range (n + 1)).map (basisImage n)

/-- The recurrence for the images of the magic basis. -/
theorem basisImage_succ {n k : ℕ} (hk : k ≤ n + 1) :
    basisImage (n + 1) k =
      image (n + 1) + ∑ j ∈ Finset.Ico k (n + 1), basisImage n j := by
  unfold basisImage
  rw [pascal_telescope n hk, map_add, map_sum, transform_X_pow]

/-- The total of the degree-`n` row. -/
theorem sum_basisImage (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), basisImage n j = binomial (n + 1) - image (n + 1) := by
  have h := basisImage_succ (n := n) (k := 0) (by lia)
  rw [← Finset.range_eq_Ico] at h
  have h0 : basisImage (n + 1) 0 = binomial (n + 1) := by simp [basisImage, binomial]
  rw [h0] at h
  rw [h]
  ring

private theorem natDegree_image_succ_le (n : ℕ) : (image (n + 1)).natDegree ≤ n + 1 := by
  rw [image]
  refine natDegree_mul_le.trans ?_
  have h1 : (X : ℝ[X]).natDegree ≤ 1 := natDegree_X_le
  rw [(generalizedEulerian_natDegree 1 n)]
  lia

private theorem reflect_image_succ (n : ℕ) : (image (n + 1)).reflect (n + 1) =
    generalizedEulerian 1 n := by
  rw [image]
  have := reflect_mul X (generalizedEulerian 1 n) (F := 1) (G := n) natDegree_X_le
    (generalizedEulerian_natDegree 1 n).le
  rw [show 1 + n = n + 1 by lia, reflect_one_X, generalizedEulerian_one_reflect, one_mul] at this
  exact this

/-- The Eulerian polynomial is the Chow operator of the row total, with reflection bound
`n + 1`. -/
theorem chowS_sum_basisImage (n : ℕ) :
    chowS (n + 1) (∑ j ∈ Finset.range (n + 1), basisImage n j) = generalizedEulerian 1 n := by
  rw [sum_basisImage]
  have hdeg : (binomial (n + 1) - image (n + 1)).natDegree ≤ n + 1 :=
    (natDegree_sub_le _ _).trans
      (max_le (natDegree_binomial_le_and_reflect (n + 1)).1.1 (natDegree_image_succ_le n))
  apply (monic_X_sub_C (1 : ℝ)).isRegular.left
  change (X - 1) * _ = (X - 1) * _
  rw [X_sub_one_mul_chowS _ _ hdeg, reflect_sub, (natDegree_binomial_le_and_reflect (n + 1)).1.2,
    reflect_image_succ]
  rw [image]
  ring

private theorem sum_map_range'_eq_finset_sum_Ico (f : ℕ → ℝ[X]) (k q : ℕ) :
    ((List.range' k (q - k)).map f).sum = ∑ j ∈ Finset.Ico k q, f j := by
  rw [Finset.sum_Ico_eq_sum_range, List.range'_eq_map_range, List.map_map, List.sum_map_range]
  simp [Function.comp_apply]

private theorem sum_drop_map_range_eq_finset_sum_Ico (f : ℕ → ℝ[X]) (k q : ℕ) :
    (((List.range q).map f).drop k).sum = ∑ j ∈ Finset.Ico k q, f j := by
  rw [← List.map_drop, show List.range q = List.range' 0 q from List.range_eq_range',
    List.drop_range']
  simpa using sum_map_range'_eq_finset_sum_Ico f k q

/-- The next row is the Chow staircase transform of the previous one, with bound `n + 1`. -/
theorem row_succ (n : ℕ) :
    row (n + 1) = BrandenVecchi.chowRowTransform (n + 1) (row n) := by
  apply List.ext_get
  · simp [row, BrandenVecchi.length_chowRowTransform]
  · intro k hkl hkr
    have hk : k ≤ n + 1 := by simpa [row] using hkl
    have hk' : k < (row n).length + 1 := by simpa [row] using Nat.lt_succ_of_le hk
    rw [BrandenVecchi.getElem_chowRowTransform hk']
    have hsum : (row n).sum = ∑ j ∈ Finset.range (n + 1), basisImage n j := by
      rw [row, List.sum_map_range]
    have hdrop : ((row n).drop k).sum = ∑ j ∈ Finset.Ico k (n + 1), basisImage n j := by
      exact sum_drop_map_range_eq_finset_sum_Ico _ k (n + 1)
    rw [hsum, hdrop, chowS_sum_basisImage]
    rw [show (row (n + 1)).get ⟨k, hkl⟩ = basisImage (n + 1) k by simp [row],
      basisImage_succ hk, image]

private theorem reflectionInterlacing_one_one :
    BrandenVecchi.IsReflectionInterlacingSeq 1 [(1 : ℝ[X])] := by
  have hX : StrictInterl (1 : ℝ[X]) X :=
    StrictInterl.of_degree_zero_right_of_degree_one one_ne_zero Polynomial.Splits.one
      X_ne_zero Polynomial.Splits.X (by simp) (by simp)
  refine ⟨?_, ?_⟩
  · intro p hp
    have hp_one : p = 1 := by simpa using hp
    subst p
    simp
  · have hclosure : BrandenVecchi.reflectionClosure 1 [(1 : ℝ[X])] = [1, X] := by
      simp [BrandenVecchi.reflectionClosure]
    rw [hclosure]
    refine ⟨⟨isInterlacingSeq0_iff_pairwise.mpr ?_, ?_⟩, ?_⟩
    · exact List.pairwise_pair.mpr hX.toInterl
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hasNonnegCoeffs_one
      · exact hasNonnegCoeffs_X
    · intro p hp hp_ne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨one_ne_zero, Polynomial.Splits.one⟩
      · exact ⟨X_ne_zero, Polynomial.Splits.X⟩

/-- Every image row of the magic basis is reflection-interlacing with respect to `n + 1`. -/
theorem row_reflectionInterlacing :
    ∀ n : ℕ, BrandenVecchi.IsReflectionInterlacingSeq (n + 1) (row n)
  | 0 => by
    have h : row 0 = [1] := by simp [row, basisImage]
    rw [h]
    exact reflectionInterlacing_one_one
  | n + 1 => by
    rw [row_succ]
    exact (row_reflectionInterlacing n).chowRowTransform

/-- The degree-`d` magic-basis expansion with coefficients `c`. -/
def magicExpansion (d : ℕ) (c : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1), C (c k) * (X ^ k * (1 + X) ^ (d - k))

/-- The Eulerian transformation of a magic-basis expansion is the corresponding combination
of the image row. -/
theorem transform_magicExpansion (d : ℕ) (c : ℕ → ℝ) :
    transform (magicExpansion d c) = ∑ k ∈ Finset.range (d + 1), C (c k) * basisImage d k := by
  simp [magicExpansion, basisImage, map_sum]

private def scaledRow (d : ℕ) (c : ℕ → ℝ) : List ℝ[X] :=
  (List.range (d + 1)).map fun k => C (c k) * basisImage d k

private theorem scaledRow_sum (d : ℕ) (c : ℕ → ℝ) :
    (scaledRow d c).sum = ∑ k ∈ Finset.range (d + 1), C (c k) * basisImage d k := by
  rw [scaledRow, List.sum_map_range]

private theorem row_forall₂_scaled {d : ℕ} {c : ℕ → ℝ}
    (hc : ∀ k, k ≤ d → 0 ≤ c k) :
    List.Forall₂ IsNonnegScalarMultiple (row d) (scaledRow d c) := by
  rw [row, scaledRow, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun j hj =>
    IsNonnegScalarMultiple.C_mul _ (hc j (by simpa [Nat.lt_succ_iff] using hj))

/-- **Athanasiadis, Theorem 1.1** (Pólya frequency part): the Eulerian transformation sends a
nonnegative combination of the magic basis `X ^ k * (1 + X) ^ (d - k)` to a polynomial with
nonnegative coefficients that is zero or real-rooted with nonpositive roots. -/
theorem transform_magicExpansion_isPF {d : ℕ} {c : ℕ → ℝ}
    (hc : ∀ k, k ≤ d → 0 ≤ c k) :
    IsPFPolynomial (transform (magicExpansion d c)) := by
  have hscaled := (row_reflectionInterlacing d).nonnegScalarMultiples (row_forall₂_scaled hc)
  have hsingle : BrandenVecchi.IsReflectionInterlacingSeq (d + 1)
      [transform (magicExpansion d c)] := by
    have hcollapsed := BrandenVecchi.IsReflectionInterlacingSeq.collapseBlock
      (left := []) (block := scaledRow d c) (right := []) (by simpa using hscaled)
    simpa [scaledRow_sum, transform_magicExpansion] using hcollapsed
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
  · exact hsingle.closedSequence.nonnegCoeffs _ (by simp [BrandenVecchi.reflectionClosure])
  · by_cases hzero : transform (magicExpansion d c) = 0
    · exact Or.inl hzero
    · exact Or.inr <| hsingle.closedSequence.splits (by
        simp [BrandenVecchi.reflectionClosure]) hzero

/-- **Athanasiadis, Theorem 1.1** (interlacing part): for a nonnegative combination `f` of the
magic basis of degree `d`, `A°((1 + X) ^ d) ≺ A° f ≺ image d`, where `image d = X * A_d`
for `d ≥ 1`. -/
theorem transform_magicExpansion_interl {d : ℕ} {c : ℕ → ℝ}
    (hc : ∀ k, k ≤ d → 0 ≤ c k) :
    Interl (binomial d) (transform (magicExpansion d c)) ∧
      Interl (transform (magicExpansion d c)) (image d) := by
  have hrow := row_reflectionInterlacing d
  have hdirect : IsInterlacingSeq0NonnegRealRooted (row d) :=
    hrow.closedSequence.sublist (by simp [BrandenVecchi.reflectionClosure])
  have hmem : ∀ j, j ≤ d → basisImage d j ∈ row d :=
    fun j hj => List.mem_map.mpr ⟨j, by simpa [Nat.lt_succ_iff] using hj, rfl⟩
  have hleft : ∀ j, j ≤ d → Interl (basisImage d 0) (basisImage d j) := by
    intro j hj
    rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hjpos
    · exact Interl.refl (hdirect.splits (hmem 0 (Nat.zero_le d)))
    · let first : Fin (row d).length := ⟨0, by simp [row]⟩
      let current : Fin (row d).length := ⟨j, by simpa [row, Nat.lt_succ_iff] using hj⟩
      simpa [first, current, row] using
        hdirect.interlacingSeq0.interl (i := first) (j := current) hjpos
  have hright : ∀ j, j ≤ d → Interl (basisImage d j) (basisImage d d) := by
    intro j hj
    by_cases hEq : j = d
    · subst j
      exact Interl.refl (hdirect.splits (hmem d le_rfl))
    · have hjlt : j < d := Nat.lt_of_le_of_ne hj hEq
      let current : Fin (row d).length := ⟨j, by simpa [row, Nat.lt_succ_iff] using hj⟩
      let last : Fin (row d).length := ⟨d, by simp [row]⟩
      simpa [current, last, row] using
        hdirect.interlacingSeq0.interl (i := current) (j := last) hjlt
  have hfirst : basisImage d 0 = binomial d := by simp [basisImage, binomial]
  have hlast : basisImage d d = image d := by simp [basisImage]
  rw [transform_magicExpansion, ← hfirst, ← hlast]
  constructor
  · apply Interl.finsetSum_left_of_nonneg
    · intro j hj
      have hjn : j ≤ d := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
      exact Interl.C_mul_right_of_nonneg (hleft j hjn) (hc j hjn)
    · intro j hj
      have hjn : j ≤ d := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
      exact nonnegCoeffs_C_mul (hc j hjn) (hdirect.nonnegCoeffs _ (hmem j hjn))
  · apply Interl.finsetSum_right_of_nonneg
    · intro j hj
      have hjn : j ≤ d := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
      exact Interl.C_mul_left_of_nonneg (hright j hjn) (hc j hjn)
    · intro j hj
      have hjn : j ≤ d := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
      exact nonnegCoeffs_C_mul (hc j hjn) (hdirect.nonnegCoeffs _ (hmem j hjn))

end EulerianTransform
end RealRooted
