import Mathlib.Analysis.Convex.Deriv
import RealRooted.MultivariateStability.BarrierPick
import RealRooted.MultivariateStability.PickRatio

/-!
# The MSS barrier along a coordinate line

For a real stable `p` and a point `z` above its roots, the barrier `Φ_i p` restricted to the line
`t ↦ z + t e_j` is nonincreasing and convex on `t ≥ 0`, for every pair of coordinates `i, j`
(Marcus–Spielman–Srivastava, *Interlacing families II*, Lemma 5.7).  Along the line,
`Φ_i p = G / F` with `F` the restriction of `p` and `G` that of `∂_i p`; `G / F` maps the upper
half-plane into the closed lower half-plane (`MvRealStable.cross_coordinate_ratio_nonpos`), so
the Pick-type lemma `PickRatio.deriv_nonpos_and_second_deriv_nonneg` gives the derivative signs.
This replaces the Helton–Vinnikov route of the original proof.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- The coordinate barrier restricted to the affine line in coordinate `j`. -/
def barrierLine {m : ℕ} (i j : Fin m) (p : MvPolynomial (Fin m) ℝ)
    (z : Fin m → ℝ) : ℝ → ℝ :=
  fun t => barrier i p (z + t • Function.update (0 : Fin m → ℝ) j 1)

private theorem barrierLine_eq_ratio {m : ℕ} (i j : Fin m)
    (p : MvPolynomial (Fin m) ℝ) (z : Fin m → ℝ) (t : ℝ) :
    barrierLine i j p z t =
      (coordinateRestriction z j (MvPolynomial.pderiv i p)).eval t /
        (coordinateRestriction z j p).eval t := by
  unfold barrierLine barrier
  rw [eval_coordinateRestriction, eval_coordinateRestriction]
  congr 1
  · apply congrArg (fun f : Fin m → ℝ => MvPolynomial.eval f (MvPolynomial.pderiv i p))
    funext k
    by_cases hkj : k = j
    · subst k
      simp
    · simp [hkj]
  · apply congrArg (fun f : Fin m → ℝ => MvPolynomial.eval f p)
    funext k
    by_cases hkj : k = j
    · subst k
      simp
    · simp [hkj]

private def ratioDerivative (F G : ℝ[X]) (t : ℝ) : ℝ :=
  (G.derivative.eval t * F.eval t - G.eval t * F.derivative.eval t) / (F.eval t) ^ 2

private theorem ratio_has_deriv (F G : ℝ[X]) {t : ℝ} (hF : F.eval t ≠ 0) :
    HasDerivAt (fun s => G.eval s / F.eval s) (ratioDerivative F G t) t := by
  have h := (G.hasDerivAt t).mul ((F.hasDerivAt t).inv hF)
  convert h using 1
  · rfl
  · dsimp [ratioDerivative]
    field_simp
    ring_nf

private theorem ratioDerivative_differentiableAt (F G : ℝ[X]) {t : ℝ}
    (hF : F.eval t ≠ 0) : DifferentiableAt ℝ (ratioDerivative F G) t := by
  have hnum := (G.derivative.hasDerivAt t).mul (F.hasDerivAt t)
  have hnum' := (G.hasDerivAt t).mul (F.derivative.hasDerivAt t)
  have hnum'' := hnum.sub hnum'
  have hden := (F.hasDerivAt t).pow 2
  have h := hnum''.mul (hden.inv (pow_ne_zero 2 hF))
  change DifferentiableAt ℝ (fun s =>
    (G.derivative.eval s * F.eval s - G.eval s * F.derivative.eval s) /
      (F.eval s) ^ 2) t
  have hd := h.differentiableAt
  convert hd using 1
  funext s
  rfl
private theorem barrierLine_data {m : ℕ} {p : MvPolynomial (Fin m) ℝ}
    {z : Fin m → ℝ} (hstable : MvRealStable p) (habove : AboveRoots p z)
    (i j : Fin m) :
    let F := coordinateRestriction z j p
    let G := coordinateRestriction z j (MvPolynomial.pderiv i p)
    F ≠ 0 ∧ F.Splits ∧
      (∀ w : ℂ, 0 < w.im →
        (F.map (algebraMap ℝ ℂ)).eval w ≠ 0 ∧
          ((G.map (algebraMap ℝ ℂ)).eval w /
            (F.map (algebraMap ℝ ℂ)).eval w).im ≤ 0) := by
  let F := coordinateRestriction z j p
  let G := coordinateRestriction z j (MvPolynomial.pderiv i p)
  have hFpos : 0 < F.eval 0 := by
    dsimp [F]
    exact coordinateRestriction_eval_pos_of_aboveRoots j habove 0 (by positivity)
  have hFne : F ≠ 0 := by
    intro hzero
    rw [hzero] at hFpos
    simp at hFpos
  have hFsplit : F.Splits := by
    rcases hstable.orZero.coordinateRestriction_zero_or_splits z j with hzero | hsplits
    · exact False.elim (hFne hzero)
    · exact hsplits
  refine ⟨hFne, hFsplit, ?_⟩
  intro w hw
  simpa [F, G] using hstable.cross_coordinate_ratio_nonpos habove i j hw

private theorem barrierLine_deriv_signs {m : ℕ} {p : MvPolynomial (Fin m) ℝ}
    {z : Fin m → ℝ} (hstable : MvRealStable p) (habove : AboveRoots p z)
    (i j : Fin m) {t : ℝ} (ht : 0 ≤ t) :
    deriv (barrierLine i j p z) t ≤ 0 ∧
      deriv (deriv (barrierLine i j p z)) t ≥ 0 := by
  let F := coordinateRestriction z j p
  let G := coordinateRestriction z j (MvPolynomial.pderiv i p)
  have hdata := barrierLine_data hstable habove i j
  have hroot := coordinateRestriction_roots_lt_of_aboveRoots habove j ht
  have hpick := PickRatio.deriv_nonpos_and_second_deriv_nonneg F G hdata.1 hdata.2.1
    hdata.2.2 t hroot
  have hfun : barrierLine i j p z = fun s => G.eval s / F.eval s := by
    funext s
    exact barrierLine_eq_ratio i j p z s
  rw [hfun]
  exact hpick

/-- The MSS barrier is antitone along every nonnegative coordinate direction. -/
theorem barrierLine_antitoneOn_of_aboveRoots {m : ℕ}
    {p : MvPolynomial (Fin m) ℝ} {z : Fin m → ℝ}
    (hstable : MvRealStable p) (habove : AboveRoots p z) (i j : Fin m) :
    AntitoneOn (barrierLine i j p z) (Set.Ici 0) := by
  let F := coordinateRestriction z j p
  let G := coordinateRestriction z j (MvPolynomial.pderiv i p)
  have hdata := barrierLine_data hstable habove i j
  have hFpos : ∀ t, t ∈ Set.Ici 0 → 0 < F.eval t := by
    intro t ht
    exact coordinateRestriction_eval_pos_of_aboveRoots j habove t ht
  have hcont : ContinuousOn (barrierLine i j p z) (Set.Ici 0) := by
    rw [show barrierLine i j p z = fun t => G.eval t / F.eval t by
      funext t
      exact barrierLine_eq_ratio i j p z t]
    apply ContinuousOn.div
    · exact (G.continuous_aeval.continuousOn)
    · exact (F.continuous_aeval.continuousOn)
    · intro t ht
      exact (hFpos t ht).ne'
  have hdiff : DifferentiableOn ℝ (barrierLine i j p z) (Set.Ioi 0) := by
    intro t ht
    rw [show barrierLine i j p z = fun s => G.eval s / F.eval s by
      funext s
      exact barrierLine_eq_ratio i j p z s]
    exact (ratio_has_deriv F G
      (hFpos t (Set.mem_Ici.mpr (le_of_lt ht))).ne').differentiableAt.differentiableWithinAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont
    (by simpa only [interior_Ici] using hdiff)
  intro t ht
  have ht' : t ∈ Set.Ioi (0 : ℝ) := by
    simpa only [interior_Ici] using ht
  exact (barrierLine_deriv_signs hstable habove i j ht'.le).1

/-- The MSS barrier is convex along every nonnegative coordinate direction. -/
theorem barrierLine_convexOn_of_aboveRoots {m : ℕ}
    {p : MvPolynomial (Fin m) ℝ} {z : Fin m → ℝ}
    (hstable : MvRealStable p) (habove : AboveRoots p z) (i j : Fin m) :
    ConvexOn ℝ (Set.Ici 0) (barrierLine i j p z) := by
  let F := coordinateRestriction z j p
  let G := coordinateRestriction z j (MvPolynomial.pderiv i p)
  let R : ℝ → ℝ := fun t => G.eval t / F.eval t
  have hFpos : ∀ t, t ∈ Set.Ici 0 → 0 < F.eval t := by
    intro t ht
    exact coordinateRestriction_eval_pos_of_aboveRoots j habove t ht
  have hline : barrierLine i j p z = R := by
    funext t
    exact barrierLine_eq_ratio i j p z t
  have hcont : ContinuousOn R (Set.Ici 0) := by
    apply ContinuousOn.div
    · exact G.continuous_aeval.continuousOn
    · exact F.continuous_aeval.continuousOn
    · intro t ht
      exact (hFpos t ht).ne'
  have hdiff : DifferentiableOn ℝ R (Set.Ioi 0) := by
    intro t ht
    have h := ratio_has_deriv F G
      (hFpos t (Set.mem_Ici.mpr (le_of_lt ht))).ne'
    simpa [R] using h.differentiableAt.differentiableWithinAt
  have hdiff2 : DifferentiableOn ℝ (deriv R) (Set.Ioi 0) := by
    intro t ht
    have hR' := ratioDerivative_differentiableAt F G
      (hFpos t (Set.mem_Ici.mpr (le_of_lt ht))).ne'
    have heq : ratioDerivative F G =ᶠ[nhds t] deriv R := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact (ratio_has_deriv F G
        (hFpos s (Set.mem_Ici.mpr (le_of_lt hs))).ne').deriv.symm
    exact hR'.congr_of_eventuallyEq heq.symm |>.differentiableWithinAt
  rw [hline]
  apply convexOn_of_deriv2_nonneg (convex_Ici 0) hcont
    (by simpa only [interior_Ici] using hdiff)
    (by simpa only [interior_Ici] using hdiff2)
  intro t ht
  have ht' : t ∈ Set.Ioi (0 : ℝ) := by
    simpa only [interior_Ici] using ht
  have hsign := barrierLine_deriv_signs hstable habove i j ht'.le
  have hfun : deriv R = deriv (barrierLine i j p z) := by rw [hline]
  change 0 ≤ deriv (deriv R) t
  rw [hfun]
  simpa only [Function.iterate_succ_apply, Function.comp_apply] using hsign.2

/-- Increasing one coordinate above an above-roots point does not increase the barrier. -/
theorem barrierLine_le_of_nonneg {m : ℕ} {p : MvPolynomial (Fin m) ℝ}
    {z : Fin m → ℝ} (hstable : MvRealStable p) (habove : AboveRoots p z)
    (i j : Fin m) {δ : ℝ} (hδ : 0 ≤ δ) :
    barrier i p (z + δ • Function.update (0 : Fin m → ℝ) j 1) ≤ barrier i p z := by
  have hmono := barrierLine_antitoneOn_of_aboveRoots hstable habove i j
  have h := hmono (show (0 : ℝ) ∈ Set.Ici 0 by exact Set.mem_Ici.mpr le_rfl)
    (show δ ∈ Set.Ici 0 by exact Set.mem_Ici.mpr hδ) hδ
  simpa [barrierLine] using h

end

end RealRooted
