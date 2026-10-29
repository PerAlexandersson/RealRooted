module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Sequences
import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.TraceSq
import RealRooted.Mathlib.LinearAlgebra.Matrix.SpectrumClosed

/-!
# Closed range of symmetric characteristic pencils

We represent the bivariate polynomial `det(T I - X U - V)` by the coefficients in `T`
after evaluating `X` at `0, 1, ..., d`.  Since every coefficient has degree at most `d`
in `X`, this evaluation array is a finite-dimensional coordinate model for the polynomial.
-/

public section

open Filter Polynomial Set Topology

namespace RealRooted

/-- The finite evaluation-coordinate array of the characteristic pencil
`det(T I - X U - V)`.  The first coordinate evaluates `X` at an integer from `0` to `d`,
and the second coordinate selects a coefficient in `T`. -/
@[expose] noncomputable def symmetricPencilEvaluation (d : ℕ)
    (U V : Matrix (Fin d) (Fin d) ℝ) : Fin (d + 1) → Fin (d + 1) → ℝ :=
  fun x j ↦ (((x : ℕ) : ℝ) • U + V).charpoly.coeff j

/-- The set of finite evaluation arrays represented by symmetric real characteristic pencils. -/
def symmetricPencilEvaluationRange (d : ℕ) :
    Set (Fin (d + 1) → Fin (d + 1) → ℝ) :=
  {a | ∃ U V : Matrix (Fin d) (Fin d) ℝ,
    U.IsSymm ∧ V.IsSymm ∧ a = symmetricPencilEvaluation d U V}

private lemma sum_sq_entries_eq_trace_mul_self {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsSymm) :
    (∑ p : Fin d × Fin d, M p.1 p.2 ^ 2) = Matrix.trace (M * M) := by
  rw [Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pow_two]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hM.apply i j]

private lemma abs_charpolyRev_coeff_two_le {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ j : Fin (d + 1), |M.charpoly.coeff j| ≤ C) :
    |M.charpolyRev.coeff 2| ≤ C := by
  rw [← Matrix.reverse_charpoly, coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
    Fintype.card_fin]
  by_cases hd : 2 ≤ d
  · rw [revAt_le hd]
    exact hcoeff ⟨d - 2, by lia⟩
  · rw [revAt_eq_self_of_lt (by lia), coeff_eq_zero_of_natDegree_lt]
    · simpa using hC
    · rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      lia

private lemma abs_entry_le_of_charpoly_coeff_le {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsSymm) {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ j : Fin (d + 1), |M.charpoly.coeff j| ≤ C) (i j : Fin d) :
    |M i j| ≤ C ^ 2 + 2 * C + 1 := by
  have hd : 0 < d := Fin.pos i
  let _ : Nonempty (Fin d) := ⟨i⟩
  have htrace : |Matrix.trace M| ≤ C := by
    rw [Matrix.trace_eq_neg_charpoly_coeff, abs_neg, Fintype.card_fin]
    exact hcoeff ⟨d - 1, by lia⟩
  have hc2 := abs_charpolyRev_coeff_two_le M hC hcoeff
  have hentry : M i j ^ 2 ≤ Matrix.trace (M * M) := by
    rw [← sum_sq_entries_eq_trace_mul_self M hM]
    exact Finset.single_le_sum (fun p _ ↦ sq_nonneg (M p.1 p.2)) (Finset.mem_univ (i, j))
  rw [Matrix.trace_mul_self_eq] at hentry
  have htrsq : Matrix.trace M ^ 2 ≤ C ^ 2 := by
    calc
      Matrix.trace M ^ 2 = |Matrix.trace M| ^ 2 := (sq_abs _).symm
      _ ≤ C ^ 2 := (sq_le_sq₀ (abs_nonneg _) hC).2 htrace
  have hc2lower : -C ≤ M.charpolyRev.coeff 2 := neg_le_of_abs_le hc2
  have habs : |M i j| ≤ M i j ^ 2 + 1 := by
    nlinarith [sq_nonneg (|M i j| - 1), sq_abs (M i j)]
  linarith

private lemma tendsto_symmetricPencilEvaluation {d : ℕ}
    {U V : ℕ → Matrix (Fin d) (Fin d) ℝ} {U₀ V₀ : Matrix (Fin d) (Fin d) ℝ}
    (hU : Tendsto U atTop (nhds U₀)) (hV : Tendsto V atTop (nhds V₀)) :
    Tendsto (fun n ↦ symmetricPencilEvaluation d (U n) (V n)) atTop
      (nhds (symmetricPencilEvaluation d U₀ V₀)) := by
  rw [tendsto_pi_nhds]
  intro x
  rw [tendsto_pi_nhds]
  intro j
  apply Matrix.tendsto_charpoly_coeff
  intro i l
  have hu := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hU i) l
  have hv := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hV i) l
  simpa [Matrix.smul_apply, Matrix.add_apply] using
    (tendsto_const_nhds.mul hu).add hv

private lemma isSymm_of_tendsto {d : ℕ}
    {M : ℕ → Matrix (Fin d) (Fin d) ℝ} {M₀ : Matrix (Fin d) (Fin d) ℝ}
    (hM : ∀ n, (M n).IsSymm) (hlim : Tendsto M atTop (nhds M₀)) : M₀.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  apply tendsto_nhds_unique (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim j) i)
  exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim i) j).congr'
    (Filter.Eventually.of_forall fun n ↦ ((hM n).apply i j).symm)

/-- For every matrix size, the finite-dimensional image of symmetric pairs under
`(U,V) ↦ det(T I - X U - V)` is closed. -/
theorem isClosed_symmetricPencilEvaluationRange (d : ℕ) :
    IsClosed (symmetricPencilEvaluationRange d) := by
  rcases d with _ | d
  · have hzero : ∀ U V : Matrix (Fin 0) (Fin 0) ℝ,
        symmetricPencilEvaluation 0 U V = fun _ _ ↦ 1 := by
      intro U V
      funext x j
      change ((((x : ℕ) : ℝ) • U + V).charpoly.coeff j) = 1
      rw [Matrix.charpoly_isEmpty]
      simp
    have hrange : symmetricPencilEvaluationRange 0 = {fun _ _ ↦ 1} := by
      ext a
      constructor
      · rintro ⟨U, V, -, -, rfl⟩
        exact hzero U V
      · intro ha
        rw [Set.mem_singleton_iff] at ha
        exact ⟨0, 0, Matrix.isSymm_zero, Matrix.isSymm_zero, ha.trans (hzero 0 0).symm⟩
    rw [hrange]
    exact isClosed_singleton
  · refine isClosed_of_closure_subset fun a ha ↦ ?_
    obtain ⟨q, hqrange, hq⟩ := mem_closure_iff_seq_limit.mp ha
    choose U V hUsymm hVsymm hqeval using hqrange
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto q hq)
    have hC0 : 0 ≤ C := le_trans (norm_nonneg (q 0)) (hC (q 0) ⟨0, rfl⟩)
    let B : ℝ := C ^ 2 + 2 * C + 1
    have hB0 : 0 ≤ B := by dsimp [B]; positivity
    have hcoord : ∀ n x j, |q n x j| ≤ C := by
      intro n x j
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (q n x) j).trans
        ((norm_le_pi_norm (q n) x).trans (hC (q n) ⟨n, rfl⟩))
    have hVbound : ∀ n i j, |V n i j| ≤ B := by
      intro n i j
      apply abs_entry_le_of_charpoly_coeff_le (V n) (hVsymm n) hC0
      intro k
      simpa [hqeval n, symmetricPencilEvaluation] using hcoord n ⟨0, by simp⟩ k
    have hUVbound : ∀ n i j, |(U n + V n) i j| ≤ B := by
      intro n i j
      apply abs_entry_le_of_charpoly_coeff_le (U n + V n) ((hUsymm n).add (hVsymm n)) hC0
      intro k
      simpa [hqeval n, symmetricPencilEvaluation] using hcoord n ⟨1, by simp⟩ k
    let P : ℕ → Fin 2 → Fin (d + 1) → Fin (d + 1) → ℝ :=
      fun n s ↦ if s = 0 then U n else V n
    have hPbound : ∀ n, P n ∈ Metric.closedBall 0 (2 * B) := by
      intro n
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
      intro s
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro j
      rw [Real.norm_eq_abs]
      by_cases hs : s = 0
      · simp only [P, hs]
        calc
          |U n i j| = |(U n + V n) i j - V n i j| := by
            simp only [Matrix.add_apply, add_sub_cancel_right]
          _ ≤ |(U n + V n) i j| + |V n i j| := abs_sub _ _
          _ ≤ B + B := add_le_add (hUVbound n i j) (hVbound n i j)
          _ = 2 * B := by ring
      · have hs1 : s = 1 := Fin.eq_one_of_ne_zero s hs
        subst s
        change |V n i j| ≤ 2 * B
        refine (hVbound n i j).trans ?_
        calc
          B ≤ B + B := le_add_of_nonneg_right hB0
          _ = 2 * B := by ring
    obtain ⟨P₀, -, φ, hφ, hP⟩ := tendsto_subseq_of_bounded
      (Metric.isBounded_closedBall (x :=
        (0 : Fin 2 → Fin (d + 1) → Fin (d + 1) → ℝ)) (r := 2 * B)) hPbound
    let U₀ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := fun i j ↦ P₀ 0 i j
    let V₀ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := fun i j ↦ P₀ 1 i j
    have hU : Tendsto (fun n ↦ U (φ n)) atTop (nhds U₀) := by
      change Tendsto (fun n i j ↦ U (φ n) i j) atTop (nhds fun i j ↦ U₀ i j)
      rw [tendsto_pi_nhds]
      intro i
      rw [tendsto_pi_nhds]
      intro j
      simpa [Function.comp_apply, P, U₀] using tendsto_pi_nhds.mp
        (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hP 0) i) j
    have hV : Tendsto (fun n ↦ V (φ n)) atTop (nhds V₀) := by
      change Tendsto (fun n i j ↦ V (φ n) i j) atTop (nhds fun i j ↦ V₀ i j)
      rw [tendsto_pi_nhds]
      intro i
      rw [tendsto_pi_nhds]
      intro j
      simpa [Function.comp_apply, P, V₀] using tendsto_pi_nhds.mp
        (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hP 1) i) j
    refine ⟨U₀, V₀, isSymm_of_tendsto (fun n ↦ hUsymm (φ n)) hU,
      isSymm_of_tendsto (fun n ↦ hVsymm (φ n)) hV, ?_⟩
    apply tendsto_nhds_unique (hq.comp hφ.tendsto_atTop)
    have heq : q ∘ φ = fun n ↦ symmetricPencilEvaluation (d + 1) (U (φ n)) (V (φ n)) := by
      funext n
      exact hqeval (φ n)
    rw [heq]
    exact tendsto_symmetricPencilEvaluation hU hV

end RealRooted
