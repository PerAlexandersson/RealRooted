import RealRooted.MultivariateStability.Specialization
import RealRooted.Multiaffine.TwoCoordinateSlice
import RealRooted.LiebSokalPointwise
import RealRooted.AffineLineRestriction
import RealRooted.HermiteBiehler.Basic

/-!
# Barrier functions of real stable polynomials

Toward the Marcus–Spielman–Srivastava bound (issue #950).  For a real polynomial `p` in `m`
variables, `AboveRoots p z` says `p (z + v) > 0` for every componentwise nonnegative `v`, and
`barrier i p z = (∂_i p)(z) / p(z)`.  For real stable `p`, every coordinate restriction is zero or
real-rooted (`MvRealStableOrZero.coordinateRestriction_zero_or_splits`); hence above the roots the
barrier in its own coordinate is `Σ_k 1 / (z_i - λ_k) ≥ 0` and nonincreasing along that coordinate,
and `Φ < 1` gives positivity of `q - q'` in one variable.  Two-coordinate restrictions stay real
stable or zero.  The cross-coordinate monotonicity/convexity (MSS's bivariate lemma) is not here.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- The MSS above-roots condition, using componentwise nonnegative shifts. -/
def AboveRoots {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (z : Fin m → ℝ) : Prop :=
  ∀ v : Fin m → ℝ, (∀ i, 0 ≤ v i) → 0 < MvPolynomial.eval (z + v) p

/-- The coordinate barrier is the logarithmic derivative at a real point. -/
def barrier {m : ℕ} (i : Fin m) (p : MvPolynomial (Fin m) ℝ) (z : Fin m → ℝ) : ℝ :=
  MvPolynomial.eval z (MvPolynomial.pderiv i p) / MvPolynomial.eval z p

/-- The univariate logarithmic derivative used by the barrier function. -/
def univariateBarrier (q : Polynomial ℝ) (t : ℝ) : ℝ :=
  q.derivative.eval t / q.eval t


private theorem multiset_map_sum_le {s : Multiset ℝ} {f g : ℝ → ℝ}
    (h : ∀ x ∈ s, f x ≤ g x) : (s.map f).sum ≤ (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact add_le_add (h a (Multiset.mem_cons_self a s))
        (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

/-- At a root-free point, a split polynomial's barrier is the reciprocal-root sum. -/
theorem univariateBarrier_eq_sum_inv_sub_root {q : Polynomial ℝ} {t : ℝ}
    (hq : q.Splits) (ht : q.eval t ≠ 0) :
    univariateBarrier q t = (q.roots.map (fun r => 1 / (t - r))).sum := by
  exact hq.eval_derivative_div_eval_of_ne_zero ht

/-- A positive evaluation to the right of every real root has nonnegative barrier. -/
theorem univariateBarrier_nonneg {q : Polynomial ℝ} {t : ℝ}
    (hq : q.Splits) (ht : 0 < q.eval t)
    (hroots : ∀ r ∈ q.roots, r < t) :
    0 ≤ univariateBarrier q t := by
  rw [univariateBarrier_eq_sum_inv_sub_root hq ht.ne']
  apply Multiset.sum_nonneg
  intro r hr
  obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hr
  have hspos : 0 < t - s := by linarith [hroots s hs]
  exact one_div_nonneg.mpr hspos.le

/-- The univariate barrier decreases to the right of all roots. -/
theorem univariateBarrier_antitone {q : Polynomial ℝ}
    (hq : q.Splits) (hpositive : ∀ t, 0 ≤ t → 0 < q.eval t)
    (hroots : ∀ r ∈ q.roots, r < 0) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    univariateBarrier q b ≤ univariateBarrier q a := by
  have hqa : q.eval a ≠ 0 := by
    exact (hpositive a ha).ne'
  have hqb : q.eval b ≠ 0 := by
    exact (hpositive b hb).ne'
  rw [univariateBarrier_eq_sum_inv_sub_root hq hqb,
    univariateBarrier_eq_sum_inv_sub_root hq hqa]
  apply multiset_map_sum_le
  intro r hr
  apply one_div_le_one_div_of_le (by linarith [hroots r hr])
  linarith

/-- If the barrier is below one at zero, subtracting the derivative is positive
on the nonnegative half-line. -/
theorem sub_derivative_eval_pos_of_univariateBarrier_lt_one {q : Polynomial ℝ}
    (hq : q.Splits) (hpositive : ∀ t, 0 ≤ t → 0 < q.eval t)
    (hroots : ∀ r ∈ q.roots, r < 0)
    (hbarrier : univariateBarrier q 0 < 1) :
    ∀ t, 0 ≤ t → 0 < (q - q.derivative).eval t := by
  intro t ht
  have hmono := univariateBarrier_antitone hq hpositive hroots
    (a := 0) (b := t) (by positivity) ht
    ht
  have hqeval : 0 < q.eval t := hpositive t ht
  have hqne : q.eval t ≠ 0 := hqeval.ne'
  have hderiv : q.derivative.eval t = univariateBarrier q t * q.eval t := by
    unfold univariateBarrier
    field_simp
  rw [Polynomial.eval_sub, hderiv]
  nlinarith

/-- The one-coordinate affine restriction through a real point. -/
def coordinateRestriction {m : ℕ} (z : Fin m → ℝ) (i : Fin m)
    (p : MvPolynomial (Fin m) ℝ) : Polynomial ℝ :=
  realAffineLineRestriction z (Function.update (0 : Fin m → ℝ) i 1) p

private def coordinateSpectators {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (i : Fin m) :
    List (Fin m) := (p.vars.erase i).toList

private theorem eval_specializeAtList_coordinate_real {m : ℕ}
    (z : Fin m → ℝ) (i : Fin m) (p : MvPolynomial (Fin m) ℝ) (t : ℝ) :
    MvPolynomial.eval (Function.update (0 : Fin m → ℝ) i (z i + t))
        (MvPolynomial.specializeAtList z (coordinateSpectators p i) p) =
      MvPolynomial.eval (Function.update z i (z i + t)) p := by
  rw [MvPolynomial.eval_specializeAtList]
  apply MvPolynomial.eval_eq_of_eq_on_vars
  intro k hk
  by_cases hki : k = i
  · subst k
    rw [MvPolynomial.specializeAtListAssignment_eq_of_not_mem]
    · simp
    · simp [coordinateSpectators]
  · rw [MvPolynomial.specializeAtListAssignment_eq_of_mem]
    · simp [hki]
    · simpa [coordinateSpectators] using
        (Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hki, hk⟩))

private theorem eval_specializeAtList_coordinate_complex {m : ℕ}
    (z : Fin m → ℝ) (i : Fin m) (p : MvPolynomial (Fin m) ℝ) (t : ℂ) :
    MvPolynomial.eval (fun k => if k = i then (z i : ℂ) + t else Complex.I)
        (complexifyMv (MvPolynomial.specializeAtList z (coordinateSpectators p i) p)) =
      MvPolynomial.eval
        (fun k => (z k : ℂ) + (Function.update (0 : Fin m → ℂ) i 1 k) * t)
        (complexifyMv p) := by
  rw [complexifyMv_specializeAtList, MvPolynomial.eval_specializeAtList]
  apply MvPolynomial.eval_eq_of_eq_on_vars
  intro k hk
  have hk' : k ∈ p.vars := by
    simpa [complexifyMv, MvPolynomial.vars_map_of_injective p
      Complex.ofRealHom.injective] using hk
  by_cases hki : k = i
  · subst k
    rw [MvPolynomial.specializeAtListAssignment_eq_of_not_mem]
    · simp
    · simp [coordinateSpectators]
  · rw [MvPolynomial.specializeAtListAssignment_eq_of_mem]
    · simp [hki]
    · simpa [coordinateSpectators] using
        (Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hki, hk'⟩))

/-- A real-stable polynomial has a zero or split one-coordinate restriction. -/
theorem MvRealStableOrZero.coordinateRestriction_zero_or_splits
    {m : ℕ} {p : MvPolynomial (Fin m) ℝ} (hp : MvRealStableOrZero p)
    (z : Fin m → ℝ) (i : Fin m) :
    coordinateRestriction z i p = 0 ∨ (coordinateRestriction z i p).Splits := by
  rcases hp with rfl | hp
  · left
    unfold coordinateRestriction realAffineLineRestriction
    simp
  rcases hp.specializeAtList_zero_or_general z (coordinateSpectators p i) with hzero | hstable
  · left
    apply Polynomial.funext
    intro t
    have h := eval_specializeAtList_coordinate_real z i p t
    rw [hzero] at h
    rw [coordinateRestriction, eval_realAffineLineRestriction]
    have hzt :
        (fun k => z k + Function.update (0 : Fin m → ℝ) i 1 k * t) =
          Function.update z i (z i + t) := by
      funext k
      by_cases hki : k = i
      · subst k
        simp
      · simp [hki]
    rw [hzt]
    simpa using h.symm
  · right
    apply IsUpperHalfPlaneStable.splits_complexify
    intro t ht
    have hsource := eval_specializeAtList_coordinate_complex z i p t
    let u : Fin m → ℂ := fun k =>
      if k = i then (z i : ℂ) + t else Complex.I
    have hu : ∀ k, 0 < (u k).im := by
      intro k
      by_cases hki : k = i
      · subst k
        simpa [u] using ht
      · simp [u, hki]
    change ((realAffineLineRestriction z
      (Function.update (0 : Fin m → ℝ) i 1) p).map (algebraMap ℝ ℂ)).eval t ≠ 0
    rw [eval_complexify_realAffineLineRestriction]
    have hassign :
        (fun k => (z k : ℂ) + (Function.update (0 : Fin m → ℝ) i 1 k : ℂ) * t) =
          (fun k => (z k : ℂ) + Function.update (0 : Fin m → ℂ) i 1 k * t) := by
      funext k
      by_cases hki : k = i
      · subst k
        simp
      · simp [hki]
    rw [hassign]
    rw [← hsource]
    exact hstable u hu


private theorem realAffineLineRestriction_derivative_coordinate
    {m : ℕ} (z : Fin m → ℝ) (i : Fin m) (p : MvPolynomial (Fin m) ℝ) :
    (coordinateRestriction z i p).derivative =
      realAffineLineRestriction z (Function.update (0 : Fin m → ℝ) i 1)
        (MvPolynomial.pderiv i p) := by
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
        rw [hphiX, MvPolynomial.pderiv_X_of_ne hji, map_zero, Polynomial.derivative_C]

/-- Evaluation of a coordinate restriction is evaluation after shifting one coordinate. -/
@[simp] theorem eval_coordinateRestriction {m : ℕ} (z : Fin m → ℝ) (i : Fin m)
    (p : MvPolynomial (Fin m) ℝ) (t : ℝ) :
    (coordinateRestriction z i p).eval t =
      MvPolynomial.eval (Function.update z i (z i + t)) p := by
  rw [coordinateRestriction, eval_realAffineLineRestriction]
  apply congrArg (fun f : Fin m → ℝ => MvPolynomial.eval f p)
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- The derivative of a coordinate restriction evaluates the corresponding partial derivative. -/
theorem eval_derivative_coordinateRestriction {m : ℕ} (z : Fin m → ℝ) (i : Fin m)
    (p : MvPolynomial (Fin m) ℝ) :
    (coordinateRestriction z i p).derivative.eval 0 =
      MvPolynomial.eval z (MvPolynomial.pderiv i p) := by
  rw [realAffineLineRestriction_derivative_coordinate]
  rw [eval_realAffineLineRestriction]
  apply congrArg (fun f : Fin m → ℝ => MvPolynomial.eval f (MvPolynomial.pderiv i p))
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- The multivariate barrier equals the univariate barrier of the coordinate restriction. -/
theorem barrier_eq_coordinateRestriction {m : ℕ} (z : Fin m → ℝ) (i : Fin m)
    (p : MvPolynomial (Fin m) ℝ) :
    barrier i p z = univariateBarrier (coordinateRestriction z i p) 0 := by
  unfold barrier univariateBarrier
  rw [eval_derivative_coordinateRestriction, eval_coordinateRestriction]
  simp

/-- Above-roots positivity gives positivity on the nonnegative coordinate ray. -/
theorem coordinateRestriction_eval_pos_of_aboveRoots {m : ℕ}
    {p : MvPolynomial (Fin m) ℝ} {z : Fin m → ℝ} (i : Fin m)
    (hp : AboveRoots p z) :
    ∀ t, 0 ≤ t → 0 < (coordinateRestriction z i p).eval t := by
  intro t ht
  let v : Fin m → ℝ := Function.update 0 i t
  have hv : ∀ j, 0 ≤ v j := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [v] using ht
    · simp [v, hji]
  have harg : z + v = Function.update z i (z i + t) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [v]
    · simp [v, hji]
  rw [eval_coordinateRestriction]
  rw [← harg]
  exact hp v hv

/-- Every root of a coordinate restriction is strictly negative under `AboveRoots`. -/
theorem coordinateRestriction_roots_lt_zero_of_aboveRoots {m : ℕ}
    {p : MvPolynomial (Fin m) ℝ} {z : Fin m → ℝ} (i : Fin m)
    (hp : AboveRoots p z) :
    ∀ r ∈ (coordinateRestriction z i p).roots, r < 0 := by
  let q := coordinateRestriction z i p
  have hqpos : 0 < q.eval 0 :=
    coordinateRestriction_eval_pos_of_aboveRoots i hp 0 (by positivity)
  have hqne : q ≠ 0 := by
    intro hzero
    simp [hzero] at hqpos
  intro r hr
  by_contra hnot
  have hrnonneg : 0 ≤ r := le_of_not_gt hnot
  have hrpos := coordinateRestriction_eval_pos_of_aboveRoots i hp r hrnonneg
  have hrzero : q.eval r = 0 := (Polynomial.mem_roots hqne).mp hr
  linarith

private theorem coordinateRestriction_splits_of_realStable_of_aboveRoots {m : ℕ}
    {p : MvPolynomial (Fin m) ℝ} {z : Fin m → ℝ}
    (hstable : MvRealStableOrZero p) (hp : AboveRoots p z) (i : Fin m) :
    (coordinateRestriction z i p).Splits := by
  rcases hstable.coordinateRestriction_zero_or_splits z i with hzero | hsplits
  · have hpos := coordinateRestriction_eval_pos_of_aboveRoots i hp 0 (by positivity)
    rw [hzero] at hpos
    simp at hpos
  · exact hsplits

/-- A real-stable polynomial has nonnegative barrier above its roots. -/
theorem barrier_nonneg_of_aboveRoots_of_realStable {m : ℕ}
    {p : MvPolynomial (Fin m) ℝ} {z : Fin m → ℝ}
    (hstable : MvRealStableOrZero p) (i : Fin m) (hp : AboveRoots p z) :
    0 ≤ barrier i p z := by
  have hqpos := coordinateRestriction_eval_pos_of_aboveRoots i hp 0 (by positivity)
  have hroots := coordinateRestriction_roots_lt_zero_of_aboveRoots i hp
  have hsplits := coordinateRestriction_splits_of_realStable_of_aboveRoots hstable hp i
  rw [barrier_eq_coordinateRestriction]
  exact univariateBarrier_nonneg hsplits hqpos hroots

/-- The barrier along a coordinate ray is the corresponding univariate barrier. -/
theorem barrier_eq_coordinateRestriction_at {m : ℕ} (z : Fin m → ℝ) (i : Fin m)
    (p : MvPolynomial (Fin m) ℝ) (t : ℝ) :
    barrier i p (Function.update z i (z i + t)) =
      univariateBarrier (coordinateRestriction z i p) t := by
  have hder :
      (coordinateRestriction z i p).derivative.eval t =
        MvPolynomial.eval (Function.update z i (z i + t))
          (MvPolynomial.pderiv i p) := by
    rw [realAffineLineRestriction_derivative_coordinate,
      eval_realAffineLineRestriction]
    apply congrArg
      (fun f : Fin m → ℝ => MvPolynomial.eval f (MvPolynomial.pderiv i p))
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  unfold barrier univariateBarrier
  rw [hder, eval_coordinateRestriction]

/-- The barrier decreases along a coordinate ray above the roots. -/
theorem barrier_antitone_of_aboveRoots_of_realStable {m : ℕ}
    {p : MvPolynomial (Fin m) ℝ} {z : Fin m → ℝ}
    (hstable : MvRealStableOrZero p) (i : Fin m) (hp : AboveRoots p z) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    barrier i p (Function.update z i (z i + b)) ≤
      barrier i p (Function.update z i (z i + a)) := by
  have hpositive := coordinateRestriction_eval_pos_of_aboveRoots i hp
  have hroots := coordinateRestriction_roots_lt_zero_of_aboveRoots i hp
  have hsplits := coordinateRestriction_splits_of_realStable_of_aboveRoots hstable hp i
  rw [barrier_eq_coordinateRestriction_at, barrier_eq_coordinateRestriction_at]
  exact univariateBarrier_antitone hsplits hpositive hroots ha hb hab

/-- A bivariate restriction obtained by fixing all coordinates except `i,j`. -/
def twoCoordinateRestriction {m : ℕ} (c : Fin m → ℝ) (i j : Fin m)
    (p : MvPolynomial (Fin m) ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.twoCoordinateAffineSlice
    (Function.update (Function.update c i 0) j 0) i j p

/-- Evaluation of a two-coordinate restriction updates exactly its two coordinates. -/
@[simp] theorem eval_twoCoordinateRestriction {m : ℕ} (c : Fin m → ℝ)
    (i j : Fin m) (hij : i ≠ j) (p : MvPolynomial (Fin m) ℝ) (w : Fin 2 → ℝ) :
    MvPolynomial.eval w (twoCoordinateRestriction c i j p) =
      MvPolynomial.eval (Function.update (Function.update c i (w 0)) j (w 1)) p := by
  unfold twoCoordinateRestriction
  rw [MvPolynomial.eval_twoCoordinateAffineSlice
    (x := Function.update (Function.update c i 0) j 0) (i := i) (j := j)
    (hij := hij)]
  apply congrArg (fun f : Fin m → ℝ => MvPolynomial.eval f p)
  funext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp
    · simp [hki, hkj]

/-- Fixing all coordinates except two preserves weak real stability. -/
theorem MvRealStableOrZero.twoCoordinateRestriction
    {m : ℕ} {p : MvPolynomial (Fin m) ℝ} (hp : MvRealStableOrZero p)
    (c : Fin m → ℝ) (i j : Fin m) (hij : i ≠ j) :
    MvRealStableOrZero (twoCoordinateRestriction c i j p) := by
  rcases hp with rfl | hp
  · change MvRealStableOrZero (0 : MvPolynomial (Fin 2) ℝ)
    exact MvRealStableOrZero.zero
  let l := MvPolynomial.twoCoordinateSpectators p i j
  rcases hp.specializeAtList_zero_or_general c l with hq | hq
  · left
    apply MvPolynomial.funext
    intro w
    rw [eval_twoCoordinateRestriction c i j hij]
    have heval := MvPolynomial.eval_specializeAtList_twoCoordinateSpectators
      c (fun k => if k = i then w 0 else if k = j then w 1 else 0) i j hij p
    rw [hq] at heval
    simpa [l, Function.update, hij, Ne.symm hij] using heval.symm
  · right
    unfold MvRealStable at hq ⊢
    intro w hw hzero
    let u : Fin m → ℂ := fun k =>
      if k = i then w 0 else if k = j then w 1 else Complex.I
    have hu : ∀ k, 0 < (u k).im := by
      intro k
      by_cases hki : k = i
      · subst k
        simpa [u] using hw 0
      · by_cases hkj : k = j
        · subst k
          simpa [u, hki] using hw 1
        · simp [u, hki, hkj]
    have hne := hq u hu
    apply hne
    have heval := MvPolynomial.eval_specializeAtList_twoCoordinateSpectators
      (fun k => (c k : ℂ)) u i j hij (complexifyMv p)
    have hspectators :
        MvPolynomial.twoCoordinateSpectators (complexifyMv p) i j = l := by
      dsimp [l]
      simp [MvPolynomial.twoCoordinateSpectators, complexifyMv,
        MvPolynomial.vars_map_of_injective p Complex.ofRealHom.injective]
    have hsource :
        MvPolynomial.eval u (complexifyMv (MvPolynomial.specializeAtList c l p)) =
          MvPolynomial.eval
            (Function.update (Function.update (fun k => (c k : ℂ)) i (w 0)) j (w 1))
            (complexifyMv p) := by
      rw [complexifyMv_specializeAtList]
      rw [← hspectators]
      simpa [l, u, Function.update, hij, Ne.symm hij] using heval
    have hslice :
        MvPolynomial.eval w (complexifyMv (RealRooted.twoCoordinateRestriction c i j p)) =
          MvPolynomial.eval
            (Function.update (Function.update (fun k => (c k : ℂ)) i (w 0)) j (w 1))
            (complexifyMv p) := by
      rw [show complexifyMv (RealRooted.twoCoordinateRestriction c i j p) =
          MvPolynomial.map Complex.ofRealHom
            (MvPolynomial.twoCoordinateAffineSlice
              (Function.update (Function.update c i 0) j 0) i j p) by
        rfl]
      rw [MvPolynomial.map_twoCoordinateAffineSlice,
        MvPolynomial.eval_twoCoordinateAffineSlice
          (x := fun k => Complex.ofRealHom (Function.update (Function.update c i 0) j 0 k))
          (i := i) (j := j) (hij := hij)]
      apply congrArg (fun f : Fin m → ℂ => MvPolynomial.eval f (complexifyMv p))
      funext k
      by_cases hki : k = i
      · subst k
        simp [hij]
      · by_cases hkj : k = j
        · subst k
          simp
        · simp [hki, hkj]
    rw [hsource, ← hslice]
    exact hzero

end

end RealRooted
