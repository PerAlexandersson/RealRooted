module

public import RealRooted.MultivariateStability.Barrier
import RealRooted.HermiteBiehler.Basic
import RealRooted.LiebSokalPointwise
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# The cross-coordinate barrier ratio is a Pick-type function

`MvRealStable.cross_coordinate_ratio_nonpos`: along a coordinate line above the roots of a real
stable polynomial, the ratio `(∂_i p) / p` has nonpositive imaginary part on the upper half-plane.
-/

public section

namespace RealRooted

noncomputable section

/-- Complex evaluation of a coordinate restriction is evaluation on its complex coordinate line. -/
private lemma eval_complexify_coordinateRestriction {m : ℕ} (z : Fin m → ℝ)
    (j : Fin m) (Q : MvPolynomial (Fin m) ℝ) (w : ℂ) :
    ((coordinateRestriction z j Q).map (algebraMap ℝ ℂ)).eval w =
      MvPolynomial.eval (fun k => if k = j then (z k : ℂ) + w else (z k : ℂ))
        (complexifyMv Q) := by
  dsimp [coordinateRestriction]
  rw [eval_complexify_realAffineLineRestriction]
  apply congrArg (fun f : Fin m → ℂ => MvPolynomial.eval f (complexifyMv Q))
  funext k
  by_cases hkj : k = j
  · subst k
    simp
  · simp [hkj]

/-- Imaginary parts of multivariate evaluation quotients converge away from a zero denominator. -/
private lemma tendsto_im_eval_div_eval {m : ℕ} (P Q : MvPolynomial (Fin m) ℂ)
    {U : ℕ → Fin m → ℂ} {U₀ : Fin m → ℂ}
    (hU : Filter.Tendsto U Filter.atTop (nhds U₀))
    (hden : MvPolynomial.eval U₀ Q ≠ 0) :
    Filter.Tendsto
      (fun n => (MvPolynomial.eval (U n) P / MvPolynomial.eval (U n) Q).im)
      Filter.atTop (nhds (MvPolynomial.eval U₀ P / MvPolynomial.eval U₀ Q).im) := by
  have hnum : Filter.Tendsto (fun n => MvPolynomial.eval (U n) P)
      Filter.atTop (nhds (MvPolynomial.eval U₀ P)) :=
    (MvPolynomial.continuous_eval P).continuousAt.tendsto.comp hU
  have hden' : Filter.Tendsto (fun n => MvPolynomial.eval (U n) Q)
      Filter.atTop (nhds (MvPolynomial.eval U₀ Q)) :=
    (MvPolynomial.continuous_eval Q).continuousAt.tendsto.comp hU
  exact Complex.continuous_im.continuousAt.tendsto.comp (hnum.div hden' hden)

/-- For `p` real stable and `z` above its roots, restrict `p` and `∂_i p` to the line `z + t e_j`
(`F` and `G`).  Then `F` has no zeros in the open upper half-plane and `Im (G / F) ≤ 0` there.
This is Lemma Q of the Pick-function route to the Marcus–Spielman–Srivastava barrier
convexity (issue #950); together with the Pick lemma it gives monotonicity and convexity of
`Φ_i` in `z_j`. -/
theorem MvRealStable.cross_coordinate_ratio_nonpos
    {m : ℕ} {p : MvPolynomial (Fin m) ℝ} {z : Fin m → ℝ}
    (hstable : MvRealStable p) (habove : AboveRoots p z)
    (i j : Fin m) {w : ℂ} (hw : 0 < w.im) :
    let F := coordinateRestriction z j p
    let G := coordinateRestriction z j (MvPolynomial.pderiv i p)
    ((F.map (algebraMap ℝ ℂ)).eval w ≠ 0 ∧
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
  have hFw : (F.map (algebraMap ℝ ℂ)).eval w ≠ 0 := by
    change (F.map Complex.ofRealHom).eval w ≠ 0
    exact eval_complexify_ne_zero_of_splits_of_im_pos hFsplit hFne hw
  refine ⟨hFw, ?_⟩
  let η : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let U : ℕ → Fin m → ℂ := fun n k =>
    if k = j then (z k : ℂ) + w else (z k : ℂ) + (η n : ℂ) * Complex.I
  let U₀ : Fin m → ℂ := fun k =>
    if k = j then (z k : ℂ) + w else (z k : ℂ)
  have hη : Filter.Tendsto (fun n => (η n : ℂ) * Complex.I)
      Filter.atTop (nhds 0) := by
    have hη' : Filter.Tendsto η Filter.atTop (nhds 0) := by
      simpa [η] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using ((Complex.continuous_ofReal.tendsto 0).comp hη').mul_const Complex.I
  have hU : Filter.Tendsto U Filter.atTop (nhds U₀) := by
    rw [tendsto_pi_nhds]
    intro k
    by_cases hkj : k = j
    · simp [U, U₀, hkj]
    · simpa [U, U₀, hkj] using hη.const_add (z k : ℂ)
  have hline (Q : MvPolynomial (Fin m) ℝ) :
      ((coordinateRestriction z j Q).map (algebraMap ℝ ℂ)).eval w =
        MvPolynomial.eval U₀ (complexifyMv Q) := by
    simpa only [U₀] using eval_complexify_coordinateRestriction z j Q w
  have hden : (MvPolynomial.eval U₀ (complexifyMv p)) ≠ 0 := by
    have hF_eval : (F.map (algebraMap ℝ ℂ)).eval w =
        MvPolynomial.eval U₀ (complexifyMv p) := by
      exact hline p
    rw [← hF_eval]
    exact hFw
  let R : ℕ → ℝ := fun n =>
    (MvPolynomial.eval (U n) (MvPolynomial.pderiv i (complexifyMv p)) /
      MvPolynomial.eval (U n) (complexifyMv p)).im
  have hR : ∀ n, R n ≤ 0 := by
    intro n
    apply hstable.eval_pderiv_div_eval_im_nonpos i (U n)
    intro k
    by_cases hkj : k = j
    · subst k
      simp [U, hw]
    · have hηpos : 0 < η n := by
        dsimp [η]
        positivity
      simp only [U, hkj]
      simpa [Complex.mul_im] using hηpos
  have hRlim : Filter.Tendsto R Filter.atTop
      (nhds ((MvPolynomial.eval U₀ (MvPolynomial.pderiv i (complexifyMv p)) /
        MvPolynomial.eval U₀ (complexifyMv p)).im)) := by
    simpa only [R] using tendsto_im_eval_div_eval
      (MvPolynomial.pderiv i (complexifyMv p)) (complexifyMv p) hU hden
  have hlimit := le_of_tendsto hRlim (Filter.Eventually.of_forall hR)
  have hF_eval : (F.map (algebraMap ℝ ℂ)).eval w =
      MvPolynomial.eval U₀ (complexifyMv p) := hline p
  have hG_eval : (G.map (algebraMap ℝ ℂ)).eval w =
      MvPolynomial.eval U₀ (MvPolynomial.pderiv i (complexifyMv p)) := by
    have hpderiv : complexifyMv (MvPolynomial.pderiv i p) =
        MvPolynomial.pderiv i (complexifyMv p) := by
      exact (MvPolynomial.pderiv_map).symm
    rw [← hpderiv]
    exact hline (MvPolynomial.pderiv i p)
  rw [← hG_eval, ← hF_eval] at hlimit
  exact hlimit

/-- Every root of the cross-coordinate denominator lies strictly below any
nonnegative evaluation parameter. -/
theorem coordinateRestriction_roots_lt_of_aboveRoots
    {m : ℕ} {p : MvPolynomial (Fin m) ℝ} {z : Fin m → ℝ}
    (habove : AboveRoots p z) (j : Fin m) {t : ℝ} (ht : 0 ≤ t) :
    ∀ r ∈ (coordinateRestriction z j p).roots, r < t := by
  intro r hr
  exact lt_of_lt_of_le (coordinateRestriction_roots_lt_zero_of_aboveRoots j habove r hr) ht

end

end RealRooted
