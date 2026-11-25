module

public import RealRooted.MatrixInterlacing.Converse
import RealRooted.AffineProperPosition
import RealRooted.AffineFamily

/-!
# Weighted three-state interlacing

The three-state matrix used for the weighted rational family in issue #2088 is

`[[1, b, d], [0, 1, 1], [X, alpha * X, 1]]`.

We prove its Brändén pencil criterion, including zero parameters and repeated
row or column indices, and package the resulting iteration.  The source is
Brändén, *Unimodality, log-concavity, real-rootedness and beyond*, Section 8,
Theorem 8.5.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The normalized transition matrix for the weighted three-state recurrence. -/
def weightedThreeStateMatrix (b alpha d : ℝ) : List (List ℝ[X]) :=
  [[1, C b, C d], [0, 1, 1], [X, C alpha * X, 1]]

private lemma interl_affine_affine_of_cross_nonneg
    {u v U V : ℝ} (hu : 0 ≤ u) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hcross : u * V ≤ U * v) :
    Interl (C u * X + C v) (C U * X + C V) := by
  rcases hu.eq_or_lt with rfl | hu
  · simp only [C_0, zero_mul, zero_add]
    rcases hU.eq_or_lt with rfl | hU
    · simpa using interl_C_C v V
    · exact interl_C_affine_linear hU
  · rcases hU.eq_or_lt with rfl | hU
    · have hV0 : V = 0 := by nlinarith
      simp [hV0, interl_zero_right]
    · exact interl_affine_linear_affine_linear_of_cross hu hU hcross

/-- For affine polynomials, interlacing reduces to a coefficient cross inequality,
including vanishing slopes. -/
private lemma interl_of_affine_coeff {p q : ℝ[X]}
    (hp : p.natDegree ≤ 1) (hq : q.natDegree ≤ 1)
    (hp1 : 0 ≤ p.coeff 1) (hq1 : 0 ≤ q.coeff 1) (hq0 : 0 ≤ q.coeff 0)
    (hcross : p.coeff 1 * q.coeff 0 ≤ q.coeff 1 * p.coeff 0) : Interl p q := by
  convert interl_affine_affine_of_cross_nonneg hp1 hq1 hq0 hcross using 1
  · exact eq_X_add_C_of_natDegree_le_one hp
  · exact eq_X_add_C_of_natDegree_le_one hq

/-- Every row of the weighted three-state matrix has length three. -/
theorem weightedThreeStateMatrix_rect (b alpha d : ℝ) :
    ∀ row ∈ weightedThreeStateMatrix b alpha d, row.length = 3 := by
  intro row hrow
  simp only [weightedThreeStateMatrix, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl <;> simp

private lemma weightedThreeStateMatrix_nonneg
    {b alpha d : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ alpha) (hd : 0 ≤ d) :
    ∀ row ∈ weightedThreeStateMatrix b alpha d, ∀ p ∈ row, HasNonnegCoeffs p := by
  intro row hrow p hp
  simp only [weightedThreeStateMatrix, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  · rcases hp with rfl | rfl | rfl
    · exact hasNonnegCoeffs_one
    · exact hasNonnegCoeffs_C hb
    · exact hasNonnegCoeffs_C hd
  · rcases hp with rfl | rfl | rfl
    · exact hasNonnegCoeffs_zero
    · exact hasNonnegCoeffs_one
    · exact hasNonnegCoeffs_one
  · rcases hp with rfl | rfl | rfl
    · exact hasNonnegCoeffs_X
    · exact (hasNonnegCoeffs_C ha).mul hasNonnegCoeffs_X
    · exact hasNonnegCoeffs_one

private lemma weightedThreeStateMatrix_affine
    {b alpha d : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ alpha) (hd : 0 ≤ d)
    (hbd : d ≤ b) (hba : alpha ≤ b) :
    ∀ (i₁ i₂ : Fin (weightedThreeStateMatrix b alpha d).length)
      (j₁ j₂ : Fin 3), i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (((weightedThreeStateMatrix b alpha d).get i₁).get
          ⟨j₁, by
            rw [weightedThreeStateMatrix_rect b alpha d _ (List.get_mem _ i₁)]
            exact j₁.isLt⟩)
        (((weightedThreeStateMatrix b alpha d).get i₁).get
          ⟨j₂, by
            rw [weightedThreeStateMatrix_rect b alpha d _ (List.get_mem _ i₁)]
            exact j₂.isLt⟩)
        (((weightedThreeStateMatrix b alpha d).get i₂).get
          ⟨j₁, by
            rw [weightedThreeStateMatrix_rect b alpha d _ (List.get_mem _ i₂)]
            exact j₁.isLt⟩)
        (((weightedThreeStateMatrix b alpha d).get i₂).get
          ⟨j₂, by
            rw [weightedThreeStateMatrix_rect b alpha d _ (List.get_mem _ i₂)]
            exact j₂.isLt⟩) := by
  intro i₁ i₂ j₁ j₂ hi hj
  change Fin 3 at i₁ i₂
  by_cases hdiag : i₁ = 2 ∧ i₂ = 2
  · fin_cases i₁ <;> fin_cases i₂ <;> norm_num at hdiag
    fin_cases j₁ <;> fin_cases j₂ <;> norm_num at hj <;>
      simp only [weightedThreeStateMatrix, List.get_eq_getElem,
        List.getElem_cons_zero, List.getElem_cons_succ] <;>
      intro s t hs ht
    · exact interl_affine_mul_X_add_X_self hs
    · have h := (interl_affine_mul_X_add_X_self (s := s) (t := t) hs)
          |>.C_mul_left_of_nonneg ha
      convert h using 1; grind
    · convert interl_affine_add_one_affine_mul_X_add_X hs ht using 1; grind
    · have h := interl_affine_mul_X_add_X_self (s := s) (t := t) hs
      convert (h.C_mul_left_of_nonneg ha).C_mul_right_of_nonneg ha using 1 <;> grind
    · have h := (interl_affine_add_one_affine_mul_X_add_X hs ht)
          |>.C_mul_right_of_nonneg ha
      convert h using 1 <;> grind
    · convert interl_affine_add_one_self (t := t) hs using 1 <;> grind

  · fin_cases i₁ <;> fin_cases i₂ <;> norm_num at hi <;> norm_num at hdiag <;>
      fin_cases j₁ <;> fin_cases j₂ <;> norm_num at hj <;>
      simp only [weightedThreeStateMatrix, List.get_eq_getElem,
        List.getElem_cons_zero, List.getElem_cons_succ] <;>
      intro s t hs ht <;>
      apply interl_of_affine_coeff (by compute_degree) (by compute_degree) <;>
      norm_num [coeff_add, coeff_C_mul, coeff_mul_C, coeff_C, coeff_X, coeff_one] <;>
      first
      | positivity
      | nlinarith [mul_nonneg ha (mul_nonneg ht.le hd)]

/-- Under `b ≥ d` and `b ≥ alpha`, the weighted three-state matrix preserves
zero-aware nonnegative real-rooted interlacing triples. -/
theorem weightedThreeStateMatrix_preserves
    {b alpha d : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ alpha) (hd : 0 ≤ d)
    (hbd : d ≤ b) (hba : alpha ≤ b) :
    PreservesInterlacingSeq0 3 (weightedThreeStateMatrix b alpha d) := by
  rw [PreservesInterlacingSeq0.iff_nonneg_and_2x2]
  · exact ⟨weightedThreeStateMatrix_nonneg hb ha hd,
      weightedThreeStateMatrix_affine hb ha hd hbd hba⟩
  · exact weightedThreeStateMatrix_rect b alpha d

/-- A state for the normalized weighted recurrence, ordered as `R, P, D`. -/
structure WeightedThreeState where
  /-- The auxiliary cumulative coordinate, updated by `R + b P + d D`. -/
  R : ℝ[X]
  /-- The row polynomial of the recurrence, updated by `P + D`. -/
  P : ℝ[X]
  /-- The difference coordinate, updated by `X R + α X P + D`. -/
  D : ℝ[X]

/-- The list representation used by the matrix-interlacing API. -/
def WeightedThreeState.toList (S : WeightedThreeState) : List ℝ[X] :=
  [S.R, S.P, S.D]

/-- One normalized weighted three-state transition. -/
def weightedThreeStateStep (b alpha d : ℝ)
    (S : WeightedThreeState) : WeightedThreeState where
  R := S.R + C b * S.P + C d * S.D
  P := S.P + S.D
  D := X * S.R + (C alpha * X) * S.P + S.D

/-- The state sequence with seed `(d - eta, 1, 0)`. -/
def weightedThreeState (b alpha d eta : ℝ) : ℕ → WeightedThreeState
  | 0 => ⟨C (d - eta), 1, 0⟩
  | n + 1 => weightedThreeStateStep b alpha d (weightedThreeState b alpha d eta n)

/-- The typed transition agrees exactly with polynomial matrix action. -/
theorem weightedThreeStateStep_toList (b alpha d : ℝ) (S : WeightedThreeState) :
    (weightedThreeStateStep b alpha d S).toList =
      matPolyAction (weightedThreeStateMatrix b alpha d) S.toList := by
  simp [weightedThreeStateStep, WeightedThreeState.toList, matPolyAction,
    weightedThreeStateMatrix]
  constructor <;> ring

private lemma constant_triple_interlacing {r : ℝ} (hr : 0 ≤ r) :
    IsInterlacingSeq0NonnegRealRooted [C r, 1, 0] := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise]
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases hp with rfl | rfl
      · simpa using interl_C_C r 1
      · exact interl_zero_right (C r)
    · refine ⟨?_, ?_, List.Pairwise.nil⟩
      · intro p hp
        rcases hp with rfl
        exact interl_zero_right 1
      · intro p hp
        exact hp.elim
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact hasNonnegCoeffs_C hr
    · exact hasNonnegCoeffs_one
    · exact hasNonnegCoeffs_zero
  · intro p hp hp0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨hp0, Splits.C r⟩
    · exact ⟨one_ne_zero, Splits.one⟩
    · exact (hp0 rfl).elim

/-- Every iterate of the weighted state recurrence is a zero-aware
nonnegative real-rooted interlacing triple. -/
theorem weightedThreeState_interlacing
    {b alpha d eta : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ alpha) (hd : 0 ≤ d)
    (heta : eta ≤ d) (hbd : d ≤ b) (hba : alpha ≤ b) (n : ℕ) :
    IsInterlacingSeq0NonnegRealRooted
      (weightedThreeState b alpha d eta n).toList := by
  induction n with
  | zero =>
      simpa [weightedThreeState, WeightedThreeState.toList] using
        constant_triple_interlacing (sub_nonneg.mpr heta)
  | succ n ih =>
      rw [weightedThreeState, weightedThreeStateStep_toList]
      exact weightedThreeStateMatrix_preserves hb ha hd hbd hba
        _ (by simp [WeightedThreeState.toList]) ih

/-- The middle coordinate of the normalized state satisfies the scalar
third-order recurrence from issue #2088. -/
theorem weightedThreeState_P_add_three
    (b alpha d eta : ℝ) (n : ℕ) :
    (weightedThreeState b alpha d eta (n + 3)).P =
      3 * (weightedThreeState b alpha d eta (n + 2)).P +
        ((C (alpha + d) * X - 3) *
          (weightedThreeState b alpha d eta (n + 1)).P) +
        ((1 + C (b - (alpha + d)) * X) *
          (weightedThreeState b alpha d eta n).P) := by
  simp only [weightedThreeState, weightedThreeStateStep]
  simp only [map_add, map_sub]
  ring

/-- The first three middle-coordinate polynomials are
`1`, `1`, and `1 + (alpha + d - eta) X`. -/
theorem weightedThreeState_P_initial (b alpha d eta : ℝ) :
    (weightedThreeState b alpha d eta 0).P = 1 ∧
      (weightedThreeState b alpha d eta 1).P = 1 ∧
      (weightedThreeState b alpha d eta 2).P =
        1 + C (alpha + d - eta) * X := by
  simp [weightedThreeState, weightedThreeStateStep]
  ring

end RealRooted
