module

public import RealRooted.EffectiveBKW.PathCube.Basic
public import RealRooted.EffectiveBKW.PathCube.CertificateData
import RealRooted.EffectiveBKW.PathCube.BranchGeometry
import RealRooted.EffectiveBKW.PathCube.PairFormula
import RealRooted.EffectiveBKW.PathCube.Exterior
import RealRooted.EffectiveBKW.PathCube.FiniteRows
import RealRooted.EffectiveBKW.Phase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Closing the path-cube sign count from a normalized sine estimate

The exact rational-to-sine estimate is an explicit hypothesis of this implication.
It is independent of the root-counting conclusion and must be discharged by the
instance interpretation before using this theorem as an unconditional result.
-/

public section

namespace RealRooted.EffectiveBKW.PathCube

open Set

/-- The verified finite prefix and a continuous sine approximation give all rows.
The phase only needs the lower-semicircle endpoint bounds; its exact winding
values are stronger than the inequalities used in this sign count. -/
theorem row_splits_nodup_of_sine_error {l u : ℝ} (hlu : l < u)
    (θ δ R M : ℝ → ℝ) (hθ : ContinuousOn θ (Icc l u))
    (hδ : ContinuousOn δ (Icc l u)) (hθl : θ l = Real.pi) (hθu : θ u = 0)
    (hδl : -Real.pi ≤ δ l) (hδu : δ u ≤ 0)
    (hR : ∀ t ∈ Ioo l u, 0 < R t) (hsin : ∀ t ∈ Ioo l u, 0 < Real.sin (θ t))
    (herr : ∀ n, 59 ≤ n → ∀ t ∈ Ioo l u,
      |Real.sin (θ t) * (R t)⁻¹ ^ n * (row n).eval t -
        M t * Real.sin (((n : ℝ) + 1) * θ t + δ t)| < M t) (r : ℕ) :
    (row r).natDegree = r ∧ (row r).Splits ∧ (row r).roots.Nodup ∧
      ∀ x ∈ (row r).roots, x < 0 := by
  by_cases hr : r < 59
  · exact row_splits_nodup_of_lt hr
  have hr59 : 59 ≤ r := by lia
  cases r with
  | zero => lia
  | succ n =>
    let φ : ℝ → ℝ := fun t ↦ ((n + 1 : ℕ) + 1 : ℝ) * θ t + δ t
    let levels : Fin (n + 1) → ℝ := fun j ↦ ((j.val : ℝ) + 1 / 2) * Real.pi
    have hφ : ContinuousOn φ (Icc l u) := (hθ.const_mul _).add hδ
    have hlevels : StrictMono levels := by
      intro i j hij
      apply mul_lt_mul_of_pos_right _ Real.pi_pos
      have hval : (i.val : ℝ) < j.val := by exact_mod_cast hij
      linarith
    have hlow (j : Fin (n + 1)) : φ u < levels j := by
      dsimp [φ, levels]
      rw [hθu]
      have hj : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
      nlinarith [Real.pi_pos]
    have hhigh (j : Fin (n + 1)) : levels j < φ l := by
      dsimp [φ, levels]
      rw [hθl]
      have hj : (j.val : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
      push_cast
      nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right hj Real.pi_pos.le]
    obtain ⟨s, hs, hspec⟩ := exists_strictAnti_eq_of_continuousOn hlu hφ levels hlevels
      hlow hhigh
    apply row_splits_nodup_of_alternating s hs
    intro j
    have ht := (hspec j).1
    have he := herr (n + 1) hr59 (s j) ht
    have hphase := (hspec j).2
    change (((n + 1 : ℕ) + 1 : ℝ) * θ (s j) + δ (s j)) =
      ((j.val : ℝ) + 1 / 2) * Real.pi at hphase
    rw [hphase] at he
    have hcos : Real.sin (((j.val : ℝ) + 1 / 2) * Real.pi) =
        (-1 : ℝ) ^ (j.val : ℤ) := by
      rw [add_mul, show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring,
        Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
      simp
    rw [hcos] at he
    have hscale : 0 < Real.sin (θ (s j)) * (R (s j))⁻¹ ^ (n + 1) :=
      mul_pos (hsin _ ht) (pow_pos (inv_pos.mpr (hR _ ht)) _)
    have hsign : (-1 : ℝ) ^ (j.val : ℤ) = 1 ∨ (-1 : ℝ) ^ (j.val : ℤ) = -1 := by
      rw [neg_one_zpow_eq_ite]
      split <;> simp
    have he' := abs_lt.mp he
    rcases hsign with hsign | hsign
    · rw [hsign, one_mul]
      rw [hsign] at he'
      have hp : 0 < (Real.sin (θ (s j)) * (R (s j))⁻¹ ^ (n + 1)) *
          (row (n + 1)).eval (s j) := by nlinarith [he'.1]
      exact (mul_pos_iff_of_pos_left hscale).mp hp
    · rw [hsign, neg_one_mul]
      rw [hsign] at he'
      have hp : 0 < (Real.sin (θ (s j)) * (R (s j))⁻¹ ^ (n + 1)) *
          (-(row (n + 1)).eval (s j)) := by nlinarith [he'.2]
      exact (mul_pos_iff_of_pos_left hscale).mp hp

private theorem continuousOn_phaseAmplitude {S : Set ℝ} {B : ℝ → ℝ}
    (hB : ContinuousOn B S) (hpos : ∀ t ∈ S, 0 < B t)
    (hne : ∀ t ∈ S, amplitudeDenominator t (B t) ≠ 0) :
    ContinuousOn (fun t ↦ phaseAmplitude t (B t)) S := by
  have ha : ContinuousOn (fun t ↦ scalarA t (B t)) S := by
    dsimp [scalarA, scalarS, scalarC]
    fun_prop
  have hd : ContinuousOn (fun t ↦ scalarD t (B t)) S := by
    dsimp [scalarD, scalarPi]
    fun_prop
  have hp : ContinuousOn (fun t ↦ pairReal t (B t)) S :=
    ha.div hd (fun t ht ↦ (scalarD_pos (t := t) (hpos t ht)).ne')
  have hi : ContinuousOn (fun t ↦ Real.sqrt (B t - pairReal t (B t) ^ 2)) S :=
    (hB.sub (hp.pow 2)).sqrt
  have hLam : ContinuousOn (fun t ↦ pairLambda t (B t)) S := by
    have he : (fun t ↦ pairLambda t (B t)) =
        fun t ↦ (pairReal t (B t) : ℂ) + Real.sqrt (B t - pairReal t (B t) ^ 2) *
          Complex.I := by
      funext t
      apply Complex.ext <;> simp [pairLambda]
    rw [he]
    exact (Complex.continuous_ofReal.comp_continuousOn hp).add
      ((Complex.continuous_ofReal.comp_continuousOn hi).mul continuousOn_const)
  have hnum : ContinuousOn (fun t ↦ amplitudeNumerator t (B t)) S := by
    dsimp [amplitudeNumerator, scalarU, scalarV, scalarD, scalarA, scalarS, scalarC, scalarPi]
    fun_prop
  have hden : ContinuousOn (fun t ↦ amplitudeDenominator t (B t)) S := by
    dsimp [amplitudeDenominator, scalarL, scalarH, scalarK, scalarD, scalarA, scalarS,
      scalarC, scalarPi]
    fun_prop
  exact hnum.div hden hne

private theorem pair_sq_le_of_ratio_sq_eq_one {t b : ℝ} (hb : 0 < b)
    (he : (pairReal t b / Real.sqrt b) ^ 2 = 1) : pairReal t b ^ 2 ≤ b := by
  rw [div_pow, Real.sq_sqrt hb.le] at he
  exact ((div_eq_one_iff_eq hb.ne').mp he).le

private theorem pair_sq_le_on_collision_interval (hbranch : branch.check = true)
    {l u : ℝ} (hsub : Icc l u ⊆ Icc branch.lo.val branch.hi.val)
    (hl : normalizedReal l (branch.y l) = -1) (hu : normalizedReal u (branch.y u) = 1)
    (hi : ∀ t ∈ Ioo l u, pairReal t (branch.y t) ^ 2 < branch.y t)
    {t : ℝ} (ht : t ∈ Icc l u) : pairReal t (branch.y t) ^ 2 ≤ branch.y t := by
  have hb := branch_pos_of_check hbranch (hsub ht)
  rcases lt_or_eq_of_le ht.1 with hlt | heq
  · rcases lt_or_eq_of_le ht.2 with htu | heu
    · exact (hi t ⟨hlt, htu⟩).le
    · subst t
      apply pair_sq_le_of_ratio_sq_eq_one hb
      change normalizedReal u (branch.y u) ^ 2 = 1
      rw [hu]
      norm_num
  · subst t
    apply pair_sq_le_of_ratio_sq_eq_one hb
    change normalizedReal l (branch.y l) ^ 2 = 1
    rw [hl]
    norm_num

/-- Interpreting the checked branch and its seven signs discharges the sine-error
hypothesis and gives the all-row conclusion. The separate Boolean witnesses are
supplied by `BranchFacts` in the unconditional instance theorem. -/
theorem row_splits_nodup_of_check (hbranch : branch.check = true)
    (hG₁ : ∀ t ∈ Icc branch.lo.val branch.hi.val, 0 < conditionG1.eval t (branch.y t))
    (hG₂ : ∀ t ∈ Icc branch.lo.val branch.hi.val, 0 < conditionG2.eval t (branch.y t))
    (hAMP : ∀ t ∈ Icc branch.lo.val branch.hi.val, 0 < conditionAMP.eval t (branch.y t))
    (hW₁ : ∀ t ∈ Icc branch.lo.val branch.hi.val, 0 < conditionW1.eval t (branch.y t))
    (hW₂ : ∀ t ∈ Icc branch.lo.val branch.hi.val, 0 < conditionW2.eval t (branch.y t))
    (hW₃ : ∀ t ∈ Icc branch.lo.val branch.hi.val, 0 < conditionW3.eval t (branch.y t))
    (hWIND : ∀ t ∈ Icc branch.lo.val branch.hi.val, 0 < conditionWIND.eval t (branch.y t))
    (r : ℕ) : (row r).natDegree = r ∧ (row r).Splits ∧ (row r).roots.Nodup ∧
      ∀ x ∈ (row r).roots, x < 0 := by
  obtain ⟨l, u, hlu, hsub, hl, hu, hi⟩ := exists_collision_interval_of_check hbranch
  have hpos (t : ℝ) (ht : t ∈ Icc l u) := branch_pos_of_check hbranch (hsub ht)
  have hneg (t : ℝ) (ht : t ∈ Icc l u) := parameter_neg (hsub ht)
  have hcurve (t : ℝ) (ht : t ∈ Icc l u) := (Branch.check_sound hbranch).2.1 t (hsub ht)
  have hclosed (t : ℝ) (ht : t ∈ Icc l u) : pairReal t (branch.y t) ^ 2 ≤ branch.y t :=
    pair_sq_le_on_collision_interval hbranch hsub hl hu hi ht
  have hden (t : ℝ) (ht : t ∈ Icc l u) : amplitudeDenominator t (branch.y t) ≠ 0 :=
    amplitudeDenominator_ne_zero (hneg t ht) (hpos t ht) (hclosed t ht) (hcurve t ht)
      (hG₁ t (hsub ht)) (hG₂ t (hsub ht))
  have hM (t : ℝ) (ht : t ∈ Icc l u) : 1 / 10 ≤ ‖phaseAmplitude t (branch.y t)‖ :=
    phaseAmplitude_norm_ge (hneg t ht) (hpos t ht) (hclosed t ht) (hcurve t ht)
      (hden t ht) (hAMP t (hsub ht))
  have hF : ContinuousOn (fun t ↦ phaseAmplitude t (branch.y t)) (Icc l u) :=
    continuousOn_phaseAmplitude ((Branch.check_sound hbranch).1.mono hsub) hpos hden
  have hδ : ContinuousOn (fun t ↦ lowerPhase (phaseAmplitude t (branch.y t))) (Icc l u) := by
    apply continuousOn_lowerPhase hF
    intro t ht he
    have hm := hM t ht
    rw [he, norm_zero] at hm
    norm_num at hm
  refine row_splits_nodup_of_sine_error hlu
    (fun t ↦ Real.arccos (normalizedReal t (branch.y t)))
    (fun t ↦ lowerPhase (phaseAmplitude t (branch.y t)))
    (fun t ↦ Real.sqrt (branch.y t)) (fun t ↦ ‖phaseAmplitude t (branch.y t)‖)
    ((continuousOn_branch_ratio hbranch).mono hsub).arccos hδ
    (by simp only [normalizedReal, hl, Real.arccos_neg_one])
    (by simp only [normalizedReal, hu, Real.arccos_one])
    (lowerPhase_mem _).1 (lowerPhase_mem _).2 ?_ ?_ ?_ r
  · intro t ht
    exact Real.sqrt_pos.mpr (hpos t (Ioo_subset_Icc_self ht))
  · intro t ht
    rw [sin_arccos_normalizedReal (hpos t (Ioo_subset_Icc_self ht)) (hi t ht).le]
    exact normalizedImag_pos (hpos t (Ioo_subset_Icc_self ht)) (hi t ht)
  · intro n hn t ht
    have hcc := Ioo_subset_Icc_self ht
    have hh := hsub hcc
    exact sine_error_lt (hneg t hcc) (hpos t hcc) (hi t ht) (hcurve t hcc)
      (hG₁ t hh) (hG₂ t hh) (hAMP t hh) (hWIND t hh)
      (hW₁ t hh) (hW₂ t hh) (hW₃ t hh) hn

end RealRooted.EffectiveBKW.PathCube
