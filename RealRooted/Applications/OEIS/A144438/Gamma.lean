import RealRooted.Applications.OEIS.A144438.Weighted
import RealRooted.GammaPencil.Intertwining

/-!
# Gamma expansion of the weighted deco Eulerian family

The gamma coefficients are first defined as polynomials in a formal weight
variable with natural coefficients. Their real specialization satisfies the
lagged gamma-operator recurrence and gives the gamma expansion of
`weightedDecoEulerian`.
-/

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The gamma coefficient at rank `n` and gamma index `j`, as a polynomial
in the formal weight variable with natural coefficients. -/
def weightedDecoGammaCoeff : ℕ → ℕ → ℕ[X]
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | 1, 0 => 1
  | 1, _ + 1 => 0
  | _ + 2, 0 => 1
  | n + 2, j + 1 =>
      if j + 1 ≤ (n + 2) / 2 then
        C (j + 2) * weightedDecoGammaCoeff (n + 1) (j + 1) +
          C (2 * (n + 1 - 2 * j)) * weightedDecoGammaCoeff (n + 1) j +
            X * weightedDecoGammaCoeff n j
      else 0

@[simp]
theorem weightedDecoGammaCoeff_zero_zero : weightedDecoGammaCoeff 0 0 = 1 := rfl

@[simp]
theorem weightedDecoGammaCoeff_one_zero : weightedDecoGammaCoeff 1 0 = 1 := rfl

@[simp]
theorem weightedDecoGammaCoeff_add_two_zero (n : ℕ) :
    weightedDecoGammaCoeff (n + 2) 0 = 1 := rfl

@[simp]
theorem weightedDecoGammaCoeff_zero (n : ℕ) :
    weightedDecoGammaCoeff n 0 = 1 := by
  rcases n with _ | n
  · rfl
  · rcases n with _ | n <;> rfl

/-- The subtraction-free coefficient recurrence on its natural support. -/
theorem weightedDecoGammaCoeff_succ_succ (n j : ℕ)
    (hj : j + 1 ≤ (n + 2) / 2) :
    weightedDecoGammaCoeff (n + 2) (j + 1) =
      C (j + 2) * weightedDecoGammaCoeff (n + 1) (j + 1) +
        C (2 * (n + 1 - 2 * j)) * weightedDecoGammaCoeff (n + 1) j +
          X * weightedDecoGammaCoeff n j := by
  rw [weightedDecoGammaCoeff]
  rw [if_pos hj]

/-- Gamma coefficients vanish above half the ambient degree. -/
theorem weightedDecoGammaCoeff_eq_zero_of_half_lt (n j : ℕ)
    (hj : n / 2 < j) : weightedDecoGammaCoeff n j = 0 := by
  rcases n with _ | n
  · rcases j with _ | j
    · simp at hj
    · rfl
  · rcases n with _ | n
    · rcases j with _ | j
      · simp at hj
      · rfl
    · rcases j with _ | j
      · simp at hj
      · rw [weightedDecoGammaCoeff]
        rw [if_neg (by lia : ¬j + 1 ≤ (n + 2) / 2)]

/-- Every formal weight coefficient is a natural number. -/
theorem weightedDecoGammaCoeff_coeff_nonneg (n j k : ℕ) :
    0 ≤ (weightedDecoGammaCoeff n j).coeff k :=
  Nat.zero_le _

/-- The universal gamma polynomial in the gamma variable, with coefficients
in `ℕ[W]`. -/
def weightedDecoGammaNat (n : ℕ) : Polynomial ℕ[X] :=
  ∑ j ∈ range (n / 2 + 1), monomial j (weightedDecoGammaCoeff n j)

/-- Coefficients of the universal gamma polynomial are the formal-weight
coefficient polynomials. -/
theorem weightedDecoGammaNat_coeff (n j : ℕ) :
    (weightedDecoGammaNat n).coeff j = weightedDecoGammaCoeff n j := by
  classical
  unfold weightedDecoGammaNat
  rw [Polynomial.finsetSum_coeff]
  by_cases hj : j ≤ n / 2
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      simp [coeff_monomial, hkj]
    · simp_all
  · have hzero := weightedDecoGammaCoeff_eq_zero_of_half_lt n j (by lia)
    rw [hzero]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hkj : k ≠ j := by lia
    simp [coeff_monomial, hkj]

/-- The universal gamma polynomial has the expected half-degree support. -/
theorem weightedDecoGammaNat_natDegree_le (n : ℕ) :
    (weightedDecoGammaNat n).natDegree ≤ n / 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [weightedDecoGammaNat_coeff,
    weightedDecoGammaCoeff_eq_zero_of_half_lt n j hj]

/-- Evaluation of a natural-coefficient polynomial at a real weight. -/
def evalNatWeight (w : ℝ) : ℕ[X] →+* ℝ :=
  Polynomial.eval₂RingHom (Nat.castRingHom ℝ) w

/-- Natural-coefficient polynomials evaluate nonnegatively at nonnegative
real weights. -/
theorem evalNatWeight_nonneg {w : ℝ} (hw : 0 ≤ w) (p : ℕ[X]) :
    0 ≤ evalNatWeight w p := by
  rw [show evalNatWeight w p = p.eval₂ (Nat.castRingHom ℝ) w by rfl,
    Polynomial.eval₂_eq_sum_range]
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hw _)

/-- The real gamma polynomial, defined by its lagged gamma-operator
recurrence. -/
def weightedDecoGamma (w : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 =>
      gammaOperator (n + 1) (weightedDecoGamma w (n + 1)) +
        C w * (X * weightedDecoGamma w n)

@[simp]
theorem weightedDecoGamma_zero (w : ℝ) : weightedDecoGamma w 0 = 1 := rfl

@[simp]
theorem weightedDecoGamma_one (w : ℝ) : weightedDecoGamma w 1 = 1 := rfl

/-- The weighted lagged gamma recurrence. -/
theorem weightedDecoGamma_recurrence (w : ℝ) (n : ℕ) :
    weightedDecoGamma w (n + 2) =
      gammaOperator (n + 1) (weightedDecoGamma w (n + 1)) +
        C w * (X * weightedDecoGamma w n) := rfl

/-- The first nontrivial weighted gamma polynomial. -/
theorem weightedDecoGamma_two (w : ℝ) :
    weightedDecoGamma w 2 = 1 + C (2 + w) * X := by
  norm_num [weightedDecoGamma, gammaOperator, map_ofNat]
  ring_nf

/-- Differential form of the weighted gamma recurrence. -/
theorem weightedDecoGamma_recurrence_expanded (w : ℝ) (n : ℕ) :
    weightedDecoGamma w (n + 2) =
      X * (1 - C 4 * X) * (weightedDecoGamma w (n + 1)).derivative +
        (1 + C (2 * (n + 1) : ℝ) * X) * weightedDecoGamma w (n + 1) +
          C w * X * weightedDecoGamma w n := by
  rw [weightedDecoGamma_recurrence, gammaOperator_apply]
  push_cast
  norm_num [map_ofNat, map_add, map_mul, map_natCast]
  ring_nf

/-- Coefficient form of the weighted gamma recurrence. -/
theorem weightedDecoGamma_coeff_succ_succ (w : ℝ) (n j : ℕ) :
    (weightedDecoGamma w (n + 2)).coeff (j + 1) =
      ((j : ℝ) + 2) * (weightedDecoGamma w (n + 1)).coeff (j + 1) +
        (2 * ((n : ℝ) + 1) - 4 * j) *
          (weightedDecoGamma w (n + 1)).coeff j +
            w * (weightedDecoGamma w n).coeff j := by
  rw [weightedDecoGamma_recurrence, coeff_add, gammaOperator_coeff]
  rw [coeff_C_mul, coeff_X_mul]
  push_cast
  norm_num [map_ofNat, map_add, map_mul, map_natCast]

/-- Real gamma polynomials remain in the half-degree box. -/
theorem weightedDecoGamma_natDegree_le (w : ℝ) :
    ∀ n : ℕ, (weightedDecoGamma w n).natDegree ≤ n / 2 := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      rw [weightedDecoGamma_recurrence]
      refine le_trans
        (natDegree_add_le
          (gammaOperator (n + 1) (weightedDecoGamma w (n + 1)))
          (C w * (X * weightedDecoGamma w n))) (max_le ?_ ?_)
      · exact gammaOperator_natDegree_le_of_natDegree_le ih1
      · calc
          (C w * (X * weightedDecoGamma w n)).natDegree ≤
              X.natDegree + (weightedDecoGamma w n).natDegree := by
                exact (natDegree_C_mul_le w _).trans natDegree_mul_le
          _ ≤ 1 + n / 2 := by simpa using Nat.add_le_add_left ih0 1
          _ ≤ (n + 2) / 2 := by lia

/-- Coefficients of the real gamma recurrence are evaluations of the
universal `ℕ[W]` coefficients. -/
theorem weightedDecoGamma_coeff_eq_evalNatWeight (w : ℝ) :
    ∀ n j : ℕ,
      (weightedDecoGamma w n).coeff j = evalNatWeight w (weightedDecoGammaCoeff n j) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro j
      rcases j with _ | j <;>
        simp [weightedDecoGammaCoeff, evalNatWeight, coeff_one]
  | one =>
      intro j
      rcases j with _ | j <;>
        simp [weightedDecoGammaCoeff, evalNatWeight, coeff_one]
  | more n ih0 ih1 =>
      intro j
      rcases j with _ | j
      · simpa [weightedDecoGamma_recurrence, weightedDecoGammaCoeff,
          evalNatWeight] using ih1 0
      · by_cases hj : j + 1 ≤ (n + 2) / 2
        · rw [weightedDecoGamma_coeff_succ_succ, ih1, ih1, ih0,
            weightedDecoGammaCoeff_succ_succ n j hj]
          simp only [map_add, map_mul]
          have hjle : 2 * j ≤ n + 1 := by lia
          simp only [evalNatWeight, coe_eval₂RingHom, eval₂_C, eval₂_X]
          push_cast [Nat.cast_sub hjle]
          ring
        · have hleft :
              (weightedDecoGamma w (n + 2)).coeff (j + 1) = 0 :=
            coeff_eq_zero_of_natDegree_lt (by
              have hdeg := weightedDecoGamma_natDegree_le w (n + 2)
              lia)
          rw [hleft]
          simp [weightedDecoGammaCoeff, show ¬j ≤ n / 2 by lia, evalNatWeight]

/-- The real gamma polynomial is the evaluation of the universal
natural-coefficient gamma polynomial. -/
theorem weightedDecoGamma_coeff_eq_eval_universal (w : ℝ) (n j : ℕ) :
    (weightedDecoGamma w n).coeff j =
      evalNatWeight w ((weightedDecoGammaNat n).coeff j) := by
  rw [weightedDecoGammaNat_coeff,
    weightedDecoGamma_coeff_eq_evalNatWeight]

/-- Nonnegative weights give nonnegative real gamma coefficients. -/
theorem weightedDecoGamma_hasNonnegCoeffs {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    HasNonnegCoeffs (weightedDecoGamma w n) := by
  intro j
  rw [weightedDecoGamma_coeff_eq_evalNatWeight]
  exact evalNatWeight_nonneg hw _

/-- The gamma polynomial of the unweighted deco Eulerian/A144438 family. -/
abbrev decoEulerianGamma : ℕ → ℝ[X] := weightedDecoGamma 1

@[simp]
theorem decoEulerianGamma_zero : decoEulerianGamma 0 = 1 :=
  weightedDecoGamma_zero 1

@[simp]
theorem decoEulerianGamma_one : decoEulerianGamma 1 = 1 :=
  weightedDecoGamma_one 1

/-- The unweighted lagged gamma recurrence in differential form. -/
theorem decoEulerianGamma_recurrence (n : ℕ) :
    decoEulerianGamma (n + 2) =
      X * (1 - C 4 * X) * (decoEulerianGamma (n + 1)).derivative +
        (1 + C (2 * (n + 1) : ℝ) * X) * decoEulerianGamma (n + 1) +
          X * decoEulerianGamma n := by
  change weightedDecoGamma 1 (n + 2) =
    X * (1 - C 4 * X) * (weightedDecoGamma 1 (n + 1)).derivative +
      (1 + C (2 * (n + 1) : ℝ) * X) * weightedDecoGamma 1 (n + 1) +
        X * weightedDecoGamma 1 n
  rw [weightedDecoGamma_recurrence_expanded]
  simp

/-- The unweighted A144438 gamma polynomials have nonnegative coefficients.
-/
theorem decoEulerianGamma_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (decoEulerianGamma n) :=
  weightedDecoGamma_hasNonnegCoeffs (by norm_num) n

/-- The weighted deco Eulerian polynomial has the asserted gamma expansion.
-/
theorem weightedDecoEulerian_isGammaExpansion (w : ℝ) :
    ∀ n : ℕ,
      IsGammaExpansion n (weightedDecoEulerian w n) (weightedDecoGamma w n) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp [IsGammaExpansion, gammaTransform, weightedDecoEulerian]
  | one =>
      simp [IsGammaExpansion, gammaTransform, gammaBasisTerm,
        weightedDecoEulerian]
      ring
  | more n ih0 ih1 =>
      unfold IsGammaExpansion at ih0 ih1 ⊢
      rw [weightedDecoEulerian_recurrence, weightedDecoGamma_recurrence,
        gammaTransform_add, gammaTransform_C_mul, gammaTransform_X_mul_two]
      rw [← gammaEulerianStep_gammaTransform (n + 1)
        (weightedDecoGamma w (n + 1)) (weightedDecoGamma_natDegree_le w (n + 1))]
      rw [gammaEulerianStep_apply, ← ih0, ← ih1]
      push_cast
      norm_num [map_ofNat, map_add, map_mul, map_natCast]
      ring_nf

/-- The weighted deco Eulerian family is palindromic in its ambient degree.
-/
theorem weightedDecoEulerian_reflect (w : ℝ) (n : ℕ) :
    (weightedDecoEulerian w n).reflect n = weightedDecoEulerian w n := by
  have hexp := weightedDecoEulerian_isGammaExpansion w n
  unfold IsGammaExpansion at hexp
  rw [hexp]
  exact gammaTransform_fixed n (weightedDecoGamma w n)

/-- The unweighted deco Eulerian polynomial has gamma polynomial
`decoEulerianGamma`. -/
theorem decoEulerian_isGammaExpansion (n : ℕ) :
    IsGammaExpansion n (decoEulerian n) (decoEulerianGamma n) := by
  have hexp := weightedDecoEulerian_isGammaExpansion 1 n
  rw [weightedDecoEulerian_one_weight n] at hexp
  exact hexp

/-- The unweighted deco Eulerian/A144438 family is palindromic. -/
theorem decoEulerian_reflect (n : ℕ) :
    (decoEulerian n).reflect n = decoEulerian n := by
  have hreflect := weightedDecoEulerian_reflect 1 n
  simpa only [weightedDecoEulerian_one_weight] using hreflect

/-- Odd-rank weighted deco Eulerian polynomials vanish at `-1`. -/
@[simp]
theorem weightedDecoEulerian_odd_eval_neg_one (w : ℝ) (m : ℕ) :
    (weightedDecoEulerian w (2 * m + 1)).eval (-1) = 0 := by
  rw [(weightedDecoEulerian_isGammaExpansion w (2 * m + 1))]
  exact gammaTransform_odd_eval_neg_one m (weightedDecoGamma w (2 * m + 1))

/-- Even-rank evaluation at `-1` selects the top gamma coefficient. -/
theorem weightedDecoEulerian_even_eval_neg_one (w : ℝ) (m : ℕ) :
    (weightedDecoEulerian w (2 * m)).eval (-1) =
      (weightedDecoGamma w (2 * m)).coeff m * (-1) ^ m := by
  rw [(weightedDecoEulerian_isGammaExpansion w (2 * m))]
  exact gammaTransform_even_eval_neg_one m (weightedDecoGamma w (2 * m))

end RealRooted.Applications.OEIS
