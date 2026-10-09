import RealRooted.MultivariateStability.BarrierCross

/-!
# The MSS barrier update lemma

Marcus–Spielman–Srivastava, *Interlacing families II*, Lemma 5.11: if `p` is real stable, `z` is
above its roots, `δ > 0` and `Φ_j p z ≤ 1 − 1/δ`, then `z + δ e_j` is above the roots of
`p − ∂_j p` (`aboveRoots_sub_pderiv_of_barrier_le`) and no barrier increases:
`Φ_i (p − ∂_j p) (z + δ e_j) ≤ Φ_i p z` (`barrier_sub_pderiv_le_of_barrier_le`).  The proof uses
the monotonicity and convexity of the barriers along coordinate lines (`BarrierCross`).
-/

namespace RealRooted

noncomputable section

open scoped BigOperators

private theorem aboveRoots_add_nonneg {m : ℕ} {p : MvPolynomial (Fin m) ℝ}
    {z w : Fin m → ℝ} (hp : AboveRoots p z) (hw : ∀ i, 0 ≤ w i) :
    AboveRoots p (z + w) := by
  intro v hv
  simpa only [Pi.add_apply, add_assoc] using hp (w + v) (fun i => add_nonneg (hw i) (hv i))

private theorem barrier_le_of_nonneg {m : ℕ} {p : MvPolynomial (Fin m) ℝ}
    {z w : Fin m → ℝ} (hstable : MvRealStable p) (habove : AboveRoots p z)
    (i : Fin m) (hw : ∀ k, 0 ≤ w k) :
    barrier i p (z + w) ≤ barrier i p z := by
  classical
  have haux : ∀ (s : Finset (Fin m)),
      barrier i p (z + (∑ k ∈ s, w k • Function.update (0 : Fin m → ℝ) k 1)) ≤
        barrier i p z := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        have hs_nonneg : ∀ k, 0 ≤ ∑ j ∈ s, w j • Function.update
            (0 : Fin m → ℝ) j 1 k := by
          intro k
          apply Finset.sum_nonneg
          intro j hj
          apply smul_nonneg (hw j)
          by_cases hkj : k = j
          · subst k
            simp
          · simp [Function.update, hkj]
        have habove_s := aboveRoots_add_nonneg habove hs_nonneg
        have hstep := barrierLine_le_of_nonneg hstable habove_s i a (hw a)
        have hs_sum : (∑ k ∈ s, w k • Function.update (0 : Fin m → ℝ) k 1) =
            (fun i => ∑ k ∈ s, w k • Function.update (0 : Fin m → ℝ) k 1 i) := by
          funext k
          simp only [Finset.sum_apply, Pi.smul_apply]
        have hstep' : barrier i p ((z + (∑ k ∈ s, w k •
            Function.update (0 : Fin m → ℝ) k 1)) +
            w a • Function.update (0 : Fin m → ℝ) a 1) ≤
              barrier i p (z + (∑ k ∈ s, w k •
              Function.update (0 : Fin m → ℝ) k 1)) := by
          rw [hs_sum]
          exact hstep
        rw [Finset.sum_insert ha]
        simpa only [Finset.sum_apply, Pi.add_apply, add_assoc, add_comm, add_left_comm] using
          hstep'.trans ih
  have hsum : (∑ k : Fin m, w k • Function.update (0 : Fin m → ℝ) k 1) = w := by
    funext k
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b hb hbk
      simp [Function.update, Ne.symm hbk]
    · simp
  simpa only [hsum] using haux Finset.univ

private theorem eval_derivative_coordinateRestriction_at {m : ℕ}
    (z : Fin m → ℝ) (i : Fin m) (p : MvPolynomial (Fin m) ℝ) (t : ℝ) :
    (coordinateRestriction z i p).derivative.eval t =
      MvPolynomial.eval (Function.update z i (z i + t)) (MvPolynomial.pderiv i p) := by
  have hder := congrArg (fun q : Polynomial ℝ => q.eval t)
    (show (coordinateRestriction z i p).derivative =
      realAffineLineRestriction z (Function.update (0 : Fin m → ℝ) i 1)
        (MvPolynomial.pderiv i p) by
      unfold coordinateRestriction
      let phi : MvPolynomial (Fin m) ℝ →+* Polynomial ℝ :=
        MvPolynomial.eval₂Hom Polynomial.C
          (fun j => Polynomial.C (z j) +
            Polynomial.C (Function.update (0 : Fin m → ℝ) i 1 j) * Polynomial.X)
      change (phi p).derivative = phi (MvPolynomial.pderiv i p)
      induction p using MvPolynomial.induction_on with
      | C c => simp [phi]
      | add p q hp hq =>
          simpa only [map_add, MvPolynomial.eval₂_add, Polynomial.derivative_add] using
            congrArg₂ (· + ·) hp hq
      | mul_X p j hp =>
          by_cases hji : j = i
          · subst j
            have hphiX : phi (MvPolynomial.X i) = Polynomial.C (z i) + Polynomial.X := by
              simp [phi]
            rw [MvPolynomial.pderiv_mul]
            simp only [map_mul, map_add, Polynomial.derivative_mul, hp]
            rw [hphiX, MvPolynomial.pderiv_X_self, map_one, Polynomial.derivative_add,
              Polynomial.derivative_C, Polynomial.derivative_X]
            ring
          · have hphiX : phi (MvPolynomial.X j) = Polynomial.C (z j) := by
              simp [phi, hji]
            rw [MvPolynomial.pderiv_mul]
            simp only [map_mul, map_add, Polynomial.derivative_mul, hp]
            rw [hphiX, MvPolynomial.pderiv_X_of_ne hji, map_zero,
              Polynomial.derivative_C])
  rw [hder, eval_realAffineLineRestriction]
  apply congrArg (fun f : Fin m → ℝ => MvPolynomial.eval f (MvPolynomial.pderiv i p))
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

private theorem barrierLine_ratio {m : ℕ} (i j : Fin m)
    (p : MvPolynomial (Fin m) ℝ) (z : Fin m → ℝ) :
    barrierLine i j p z = fun t =>
      (coordinateRestriction z j (MvPolynomial.pderiv i p)).eval t /
        (coordinateRestriction z j p).eval t := by
  funext t
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

private def ratioDerivativeLocal (F G : Polynomial ℝ) (t : ℝ) : ℝ :=
  (G.derivative.eval t * F.eval t - G.eval t * F.derivative.eval t) /
    (F.eval t) ^ 2

private theorem ratio_has_deriv_local (F G : Polynomial ℝ) {t : ℝ}
    (hF : F.eval t ≠ 0) :
    HasDerivAt (fun s => G.eval s / F.eval s) (ratioDerivativeLocal F G t) t := by
  have h := (G.hasDerivAt t).mul ((F.hasDerivAt t).inv hF)
  convert h using 1
  · rfl
  · dsimp [ratioDerivativeLocal]
    field_simp
    ring_nf

/-- The MSS update point lies above the roots after one derivative subtraction. -/
theorem aboveRoots_sub_pderiv_of_barrier_le {m : ℕ}
    {p : MvPolynomial (Fin m) ℝ} {z : Fin m → ℝ} {δ : ℝ} {j : Fin m}
    (hstable : MvRealStable p) (habove : AboveRoots p z) (hδ : 0 < δ)
    (hbarrier : barrier j p z ≤ 1 - 1 / δ) :
    AboveRoots (p - MvPolynomial.pderiv j p)
      (z + δ • Function.update (0 : Fin m → ℝ) j 1) := by
  intro v hv
  let w := z + v
  have hw : AboveRoots p w := aboveRoots_add_nonneg habove hv
  have hbarrier_w : barrier j p w < 1 := by
    have hle := barrier_le_of_nonneg hstable habove j hv
    calc
      barrier j p w ≤ barrier j p z := hle
      _ ≤ 1 - 1 / δ := hbarrier
      _ < 1 := by
        have : 0 < 1 / δ := one_div_pos.mpr hδ
        linarith
  let q := coordinateRestriction w j p
  have hqpos : ∀ t, 0 ≤ t → 0 < q.eval t := by
    intro t ht
    exact coordinateRestriction_eval_pos_of_aboveRoots j hw t ht
  have hqroots : ∀ r ∈ q.roots, r < 0 := by
    exact coordinateRestriction_roots_lt_zero_of_aboveRoots j hw
  have hqsplit : q.Splits := by
    rcases hstable.orZero.coordinateRestriction_zero_or_splits w j with hzero | hsplits
    · have hzero_pos := hqpos 0 (by positivity)
      have hzero' : q = 0 := by simpa [q] using hzero
      rw [hzero'] at hzero_pos
      simp at hzero_pos
    · exact hsplits
  have hqbarrier : univariateBarrier q 0 < 1 := by
    rw [← barrier_eq_coordinateRestriction w j p]
    exact hbarrier_w
  have hpositive := sub_derivative_eval_pos_of_univariateBarrier_lt_one
    hqsplit hqpos hqroots hqbarrier (δ) hδ.le
  have hpoly : coordinateRestriction w j (p - MvPolynomial.pderiv j p) = q - q.derivative := by
    apply Polynomial.funext
    intro t
    simp only [q, eval_coordinateRestriction, MvPolynomial.eval_sub, Polynomial.eval_sub]
    rw [eval_derivative_coordinateRestriction_at]
  rw [← hpoly] at hpositive
  have heval : (coordinateRestriction w j (p - MvPolynomial.pderiv j p)).eval δ =
      MvPolynomial.eval (w + δ • Function.update (0 : Fin m → ℝ) j 1)
        (p - MvPolynomial.pderiv j p) := by
    rw [eval_coordinateRestriction]
    apply congrArg (fun f : Fin m → ℝ =>
      MvPolynomial.eval f (p - MvPolynomial.pderiv j p))
    funext k
    by_cases hkj : k = j
    · subst k
      simp [w, Function.update, add_comm]
    · simp [w, hkj]
  have hpoint : z + δ • Function.update (0 : Fin m → ℝ) j 1 + v =
      w + δ • Function.update (0 : Fin m → ℝ) j 1 := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply]
    dsimp [w]
    ring
  rw [hpoint, ← heval]
  exact hpositive

/-- The MSS barrier does not increase under one derivative update. -/
theorem barrier_sub_pderiv_le_of_barrier_le {m : ℕ}
    {p : MvPolynomial (Fin m) ℝ} {z : Fin m → ℝ} {δ : ℝ} {i j : Fin m}
    (hstable : MvRealStable p) (habove : AboveRoots p z) (hδ : 0 < δ)
    (hbarrier : barrier j p z ≤ 1 - 1 / δ) :
    barrier i (p - MvPolynomial.pderiv j p)
        (z + δ • Function.update (0 : Fin m → ℝ) j 1) ≤ barrier i p z := by
  let y := z + δ • Function.update (0 : Fin m → ℝ) j 1
  let F := coordinateRestriction z j p
  let G := coordinateRestriction z j (MvPolynomial.pderiv i p)
  have hpoint : Function.update z j (z j + δ) = y := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [y]
    · simp [y, hkj]
  have hFpos : 0 < F.eval δ := by
    dsimp [F]
    exact coordinateRestriction_eval_pos_of_aboveRoots j habove δ hδ.le
  have hFne : F.eval δ ≠ 0 := hFpos.ne'
  have hline : barrierLine i j p z = fun t => G.eval t / F.eval t := by
    exact barrierLine_ratio i j p z
  have hratio : HasDerivAt (barrierLine i j p z)
      (ratioDerivativeLocal F G δ) δ := by
    rw [hline]
    exact ratio_has_deriv_local F G hFne
  have hFeval : F.eval δ = MvPolynomial.eval y p := by
    change (coordinateRestriction z j p).eval δ = MvPolynomial.eval y p
    rw [eval_coordinateRestriction, hpoint]
  have hGeval : G.eval δ = MvPolynomial.eval y (MvPolynomial.pderiv i p) := by
    change (coordinateRestriction z j (MvPolynomial.pderiv i p)).eval δ =
      MvPolynomial.eval y (MvPolynomial.pderiv i p)
    rw [eval_coordinateRestriction, hpoint]
  have hFderiv : F.derivative.eval δ = MvPolynomial.eval y (MvPolynomial.pderiv j p) := by
    change (coordinateRestriction z j p).derivative.eval δ =
      MvPolynomial.eval y (MvPolynomial.pderiv j p)
    rw [eval_derivative_coordinateRestriction_at, hpoint]
  have hGderiv : G.derivative.eval δ =
      MvPolynomial.eval y (MvPolynomial.pderiv j (MvPolynomial.pderiv i p)) := by
    change (coordinateRestriction z j (MvPolynomial.pderiv i p)).derivative.eval δ =
      MvPolynomial.eval y (MvPolynomial.pderiv j (MvPolynomial.pderiv i p))
    rw [eval_derivative_coordinateRestriction_at, hpoint]
  have hqabove := aboveRoots_sub_pderiv_of_barrier_le hstable habove hδ hbarrier
  have hqpos : 0 < MvPolynomial.eval y (p - MvPolynomial.pderiv j p) := by
    have := hqabove (0 : Fin m → ℝ) (fun _ => le_rfl)
    simpa [y] using this
  have hp_pos : 0 < MvPolynomial.eval y p := by
    exact habove (δ • Function.update (0 : Fin m → ℝ) j 1) (fun k => by
      by_cases hkj : k = j
      · subst k
        simpa using hδ.le
      · simp [Function.update, hkj])
  have hidentity : barrier i (p - MvPolynomial.pderiv j p) y =
      barrier i p y - deriv (barrierLine i j p z) δ /
        (1 - barrier j p y) := by
    have hcomm : MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
        MvPolynomial.pderiv j (MvPolynomial.pderiv i p) :=
      MvPolynomial.pderiv_comm i j p
    rw [barrier, barrier, barrier, map_sub, MvPolynomial.eval_sub, MvPolynomial.eval_sub,
      hcomm]
    rw [hratio.deriv]
    unfold ratioDerivativeLocal
    rw [hFeval, hGeval, hFderiv, hGderiv]
    have hqne :
        MvPolynomial.eval y p - MvPolynomial.eval y (MvPolynomial.pderiv j p) ≠ 0 := by
      simpa only [MvPolynomial.eval_sub] using hqpos.ne'
    field_simp [hp_pos.ne', hqne]
    ring
  have hderiv_nonpos : deriv (barrierLine i j p z) δ ≤ 0 := by
    have hanti := barrierLine_antitoneOn_of_aboveRoots hstable habove i j
    have hanti' : AntitoneOn (barrierLine i j p z) (Set.Ioi 0) := by
      intro a ha b hb hab
      exact hanti (Set.mem_Ici.mpr ha.le) (Set.mem_Ici.mpr hb.le) hab
    have hacc : AccPt δ (Filter.principal (Set.Ioi 0)) := by
      exact isOpen_Ioi.preperfect δ hδ
    have hratio' : HasDerivWithinAt (barrierLine i j p z)
        (deriv (barrierLine i j p z) δ) (Set.Ioi 0) δ := by
      rw [hratio.deriv]
      exact hratio.hasDerivWithinAt
    exact hratio'.nonpos_of_antitoneOn hacc hanti'
  have hconv := barrierLine_convexOn_of_aboveRoots hstable habove i j
  have hslope := hconv.slope_le_deriv (Set.mem_Ici.mpr le_rfl)
    (Set.mem_Ici.mpr hδ.le) hδ hratio.differentiableAt
  have hsecant : δ * (-deriv (barrierLine i j p z) δ) ≤
      barrier i p z - barrier i p y := by
    have hzero : barrierLine i j p z 0 = barrier i p z := by
      simp [barrierLine]
    have hdelta : barrierLine i j p z δ = barrier i p y := by
      rfl
    rw [slope_def_field] at hslope
    rw [hzero, hdelta] at hslope
    simp only [sub_zero] at hslope
    field_simp [ne_of_gt hδ] at hslope
    nlinarith
  have hbarrier_y : barrier j p y ≤ 1 - 1 / δ := by
    have hshift := barrierLine_le_of_nonneg hstable habove j j hδ.le
    change barrier j p y ≤ 1 - 1 / δ
    simpa [y] using hshift.trans hbarrier
  have hden : 0 < 1 - barrier j p y := by
    have hone : 0 < 1 / δ := one_div_pos.mpr hδ
    linarith
  have hden_lower : 1 / δ ≤ 1 - barrier j p y := by
    linarith
  have hquot : -deriv (barrierLine i j p z) δ / (1 - barrier j p y) ≤
      δ * (-deriv (barrierLine i j p z) δ) := by
    apply (div_le_iff₀ hden).2
    have hprod : 1 ≤ δ * (1 - barrier j p y) := by
      have hmul := mul_le_mul_of_nonneg_left hden_lower hδ.le
      calc
        1 = δ * (1 / δ) := by field_simp
        _ ≤ δ * (1 - barrier j p y) := hmul
    nlinarith [mul_nonneg (neg_nonneg.mpr hderiv_nonpos) (sub_nonneg.mpr hprod)]
  change barrier i (p - MvPolynomial.pderiv j p) y ≤ barrier i p z
  calc
    barrier i (p - MvPolynomial.pderiv j p) y =
        barrier i p y - deriv (barrierLine i j p z) δ /
          (1 - barrier j p y) := hidentity
    _ ≤ barrier i p y + δ * (-deriv (barrierLine i j p z) δ) := by
      simpa only [sub_eq_add_neg, neg_div, add_comm] using
        add_le_add_left hquot (barrier i p y)
    _ ≤ barrier i p z := by linarith

end

end RealRooted
