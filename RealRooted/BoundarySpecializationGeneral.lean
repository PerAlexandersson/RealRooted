import RealRooted.BorceaBranden.BoundarySpecialization
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots
import RealRooted.Mathlib.Algebra.MvPolynomial.Specialize
import RealRooted.Mathlib.RingTheory.MvPolynomial.Hyperbolic
import RealRooted.Mathlib.Algebra.MvPolynomial.EvalOnVars
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# General boundary specialization

This module proves that specializing finitely many coordinates of a stable
polynomial to real boundary values preserves upper-half-plane stability up to
the zero polynomial, without coordinate-degree restrictions.
-/

open Complex

namespace RealRooted

noncomputable section

/-- Specializing one coordinate to zero preserves upper-half-plane stability
up to the zero polynomial, with no coordinate-degree restriction. -/
theorem MvUpperHalfPlaneStable.specializeZero_zero_or_general
    {alpha : Type*} {P : MvPolynomial alpha ℂ}
    (hP : MvUpperHalfPlaneStable P) (i : alpha) :
    MvUpperHalfPlaneStableOrZero (MvPolynomial.specializeZero i P) := by
  classical
  let Q := MvPolynomial.specializeZero i P
  by_cases hQ : Q = 0
  · exact Or.inl hQ
  right
  intro z hz hQz
  obtain ⟨u, _, hQu⟩ := exists_upperHalfPlane_eval_ne_zero hQ
  let z₁ : alpha → ℂ := fun j => if j ∈ Q.vars then u j else z j
  have hQz₁ : MvPolynomial.eval z₁ Q ≠ 0 := by
    have heval : MvPolynomial.eval z₁ Q = MvPolynomial.eval u Q :=
      MvPolynomial.eval_eq_of_eq_on_vars Q z₁ u (by
        intro j hj
        simp [z₁, hj])
    rw [heval]
    exact hQu
  let v : alpha → ℂ := fun j => z₁ j - z j
  let A : Polynomial ℂ := MvPolynomial.affineLineRestriction z v Q
  have hA0 : A.eval 0 = 0 := by
    simp only [A, MvPolynomial.eval_affineLineRestriction, mul_zero, add_zero]
    exact hQz
  have hA1 : A.eval 1 ≠ 0 := by simpa [A, v] using hQz₁
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.eval_zero] at hA1
    exact hA1 rfl
  let U : Set ℂ := {t | ∀ j ∈ Q.vars, 0 < (z j + v j * t).im}
  have hUopen : IsOpen U := by
    rw [show U = ⋂ j ∈ Q.vars, {t : ℂ | 0 < (z j + v j * t).im} by
      ext t
      simp [U]]
    exact isOpen_biInter_finset fun _ _ =>
      isOpen_lt continuous_const (by fun_prop)
  have hzeroU : (0 : ℂ) ∈ U := by
    intro j _
    simpa using hz j
  let delta : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let base : ℕ → alpha → ℂ := fun k =>
    Function.update z i ((delta k : ℂ) * I)
  let direction : alpha → ℂ := Function.update v i 0
  let p : ℕ → Polynomial ℂ := fun k =>
    MvPolynomial.affineLineRestriction (base k) direction P
  have hpdeg (k : ℕ) : (p k).natDegree ≤ P.totalDegree :=
    MvPolynomial.natDegree_affineLineRestriction_le (base k) direction P
  have hproots (k : ℕ) (r : ℂ) (hr : r ∈ (p k).roots) : r ∈ Uᶜ := by
    intro hrU
    have hevalzero : (p k).eval r = 0 := (Polynomial.mem_roots'.mp hr).2
    have hassign : ∀ j, 0 < (base k j + direction j * r).im := by
      intro j
      by_cases hji : j = i
      · subst j
        have hdeltaPos : 0 < delta k := by
          dsimp [delta]
          positivity
        simpa [base, direction] using hdeltaPos
      · simp only [base, direction, Function.update_of_ne hji]
        by_cases hjQ : j ∈ Q.vars
        · exact hrU j hjQ
        · simpa [v, z₁, hjQ] using hz j
    have hnonzero := hP (fun j => base k j + direction j * r) hassign
    apply hnonzero
    rw [← MvPolynomial.eval_affineLineRestriction]
    exact hevalzero
  have hdelta : Filter.Tendsto delta Filter.atTop (nhds 0) := by
    simpa [delta] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdeltaI : Filter.Tendsto (fun k => (delta k : ℂ) * I)
      Filter.atTop (nhds 0) := by
    simpa using ((Complex.continuous_ofReal.tendsto 0).comp hdelta).mul_const I
  have hpeval (t : ℂ) : Filter.Tendsto (fun k => (p k).eval t)
      Filter.atTop (nhds (A.eval t)) := by
    have hbase : Filter.Tendsto base Filter.atTop
        (nhds (Function.update z i 0)) := by
      rw [tendsto_pi_nhds]
      intro j
      by_cases hji : j = i
      · subst j
        simpa [base] using hdeltaI
      · simp [base, hji]
    have hassign : Filter.Tendsto
        (fun k j => base k j + direction j * t) Filter.atTop
        (nhds fun j => Function.update z i 0 j + direction j * t) := by
      rw [tendsto_pi_nhds]
      intro j
      exact (tendsto_pi_nhds.mp hbase j).add_const _
    have heval := (MvPolynomial.continuous_eval P).continuousAt.tendsto.comp hassign
    have hsource : (fun k => (p k).eval t) =
        (fun k => MvPolynomial.eval
          (fun j => base k j + direction j * t) P) := by
      funext k
      dsimp [p]
      rw [MvPolynomial.eval_affineLineRestriction]
    have htarget : A.eval t = MvPolynomial.eval
        (fun j => Function.update z i 0 j + direction j * t) P := by
      dsimp [A]
      rw [MvPolynomial.eval_affineLineRestriction,
        MvPolynomial.eval_specializeZero]
      apply congrArg (fun w : alpha → ℂ => MvPolynomial.eval w P)
      funext j
      by_cases hji : j = i
      · subst j
        simp [direction]
      · simp [direction, hji]
    rw [hsource, htarget]
    exact heval
  have hroot : (0 : ℂ) ∈ A.roots :=
    Polynomial.mem_roots'.mpr ⟨hA, hA0⟩
  have hclosed := Polynomial.roots_mem_of_tendsto_eval_of_natDegree_le
    hUopen.isClosed_compl hpdeg hproots hpeval 0 hroot
  exact hclosed hzeroU

/-- Repeatedly specializing an ordered finite list of coordinates to zero
preserves upper-half-plane stability up to the zero polynomial, with no degree
restriction. -/
theorem MvUpperHalfPlaneStable.specializeZeroList_zero_or_general
    {alpha : Type*} {P : MvPolynomial alpha ℂ}
    (hP : MvUpperHalfPlaneStable P) (l : List alpha) :
    MvUpperHalfPlaneStableOrZero (specializeZeroList l P) := by
  induction l generalizing P with
  | nil => exact hP.orZero
  | cons i l ih =>
      rcases hP.specializeZero_zero_or_general i with hzero | hstable
      · simpa [specializeZeroList_cons, hzero] using
          (MvUpperHalfPlaneStableOrZero.zero (sigma := alpha))
      · exact ih hstable

/-- Specializing after translating one coordinate by a real scalar is direct
specialization at that scalar. -/
theorem _root_.MvPolynomial.specializeZero_translate_single_eq_specializeAt_real
    {alpha : Type*} [DecidableEq alpha]
    (P : MvPolynomial alpha ℂ) (i : alpha) (c : ℝ) :
    MvPolynomial.specializeZero i
        (MvPolynomial.aeval
          (fun j => MvPolynomial.C
            ((Function.update (0 : alpha → ℝ) i c j : ℝ) : ℂ) +
            MvPolynomial.X j) P) =
      MvPolynomial.specializeAt i (c : ℂ) P := by
  classical
  apply MvPolynomial.funext
  intro z
  simp only [MvPolynomial.eval_specializeZero,
    MvPolynomial.eval_specializeAt, ← MvPolynomial.aeval_eq_eval,
    MvPolynomial.comp_aeval_apply]
  congr 1
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- Specializing one coordinate at a real boundary value preserves
upper-half-plane stability up to the zero polynomial, with no coordinate-degree
restriction. -/
theorem MvUpperHalfPlaneStable.specializeAt_real_zero_or_general
    {alpha : Type*} {P : MvPolynomial alpha ℂ}
    (hP : MvUpperHalfPlaneStable P) (i : alpha) (c : ℝ) :
    MvUpperHalfPlaneStableOrZero
      (MvPolynomial.specializeAt i (c : ℂ) P) := by
  classical
  let a : alpha → ℝ := Function.update 0 i c
  have htranslated := (hP.translate_add_real a).specializeZero_zero_or_general i
  simpa only [a,
    MvPolynomial.specializeZero_translate_single_eq_specializeAt_real] using
      htranslated

/-- Weak stability is preserved when one coordinate is specialized at a real
boundary value. -/
theorem MvUpperHalfPlaneStableOrZero.specializeAt_real_general
    {alpha : Type*} {P : MvPolynomial alpha ℂ}
    (hP : MvUpperHalfPlaneStableOrZero P) (i : alpha) (c : ℝ) :
    MvUpperHalfPlaneStableOrZero
      (MvPolynomial.specializeAt i (c : ℂ) P) := by
  rcases hP with rfl | hP
  · simpa using (MvUpperHalfPlaneStableOrZero.zero (sigma := alpha))
  · exact hP.specializeAt_real_zero_or_general i c

/-- Repeated specialization at real boundary values preserves weak stability.
Coordinates are processed in list order and may be repeated. -/
theorem MvUpperHalfPlaneStableOrZero.specializeAtList_real_general
    {alpha : Type*} {P : MvPolynomial alpha ℂ}
    (hP : MvUpperHalfPlaneStableOrZero P) (c : alpha → ℝ) (l : List alpha) :
    MvUpperHalfPlaneStableOrZero
      (MvPolynomial.specializeAtList (fun i => (c i : ℂ)) l P) := by
  induction l generalizing P with
  | nil => exact hP
  | cons i l ih => exact ih (hP.specializeAt_real_general i (c i))

/-- Specializing an entire finite right block at zero preserves
upper-half-plane stability up to the zero polynomial, with no coordinate-degree
restriction. The left block may have arbitrary cardinality and degrees. -/
theorem MvUpperHalfPlaneStable.specializeRight_zero_or_general
    {tau sigma : Type*} [Finite sigma]
    {P : MvPolynomial (Sum tau sigma) ℂ}
    (hP : MvUpperHalfPlaneStable P) :
    MvUpperHalfPlaneStableOrZero
      (_root_.RealRooted.specializeRight (fun _ : sigma => 0) P) := by
  classical
  letI := Fintype.ofFinite sigma
  let l : List (Sum tau sigma) :=
    Finset.univ.toList.map (Sum.inr : sigma → Sum tau sigma)
  let Q : MvPolynomial (Sum tau sigma) ℂ := specializeZeroList l P
  have hQeval (x : tau → ℂ) (y : sigma → ℂ) :
      MvPolynomial.eval (Sum.elim x y) Q =
        MvPolynomial.eval (Sum.elim x (fun _ => 0)) P := by
    change
      MvPolynomial.eval (Sum.elim x y) (specializeZeroList l P) =
        MvPolynomial.eval (Sum.elim x (fun _ => 0)) P
    rw [eval_specializeZeroList]
    apply congrArg (fun w : Sum tau sigma → ℂ => MvPolynomial.eval w P)
    funext j
    cases j <;> simp [l]
  have hQzero_or : MvUpperHalfPlaneStableOrZero Q :=
    hP.specializeZeroList_zero_or_general l
  by_cases hzero :
      _root_.RealRooted.specializeRight (fun _ : sigma => 0) P = 0
  · exact Or.inl hzero
  have hQne : Q ≠ 0 := by
    intro hQzero
    obtain ⟨x, _hx, heval⟩ := exists_upperHalfPlane_eval_ne_zero hzero
    apply heval
    rw [eval_specializeRight, ← hQeval x (fun _ => I), hQzero]
    simp
  right
  have hQstable : MvUpperHalfPlaneStable Q :=
    hQzero_or.resolve_left hQne
  intro x hx
  rw [eval_specializeRight, ← hQeval x (fun _ => I)]
  exact hQstable (Sum.elim x (fun _ => I)) fun j => by
    cases j with
    | inl i => exact hx i
    | inr _ => simp

end

end RealRooted
