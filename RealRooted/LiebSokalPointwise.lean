import RealRooted.Multiaffine
import RealRooted.MultivariateStability
import RealRooted.LiebSokalOperator
import RealRooted.Mathlib.Algebra.MvPolynomial.EvalOnVars
import RealRooted.Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Polynomial.GaussLucas

/-!
# Pointwise input for the Lieb--Sokal theorem

This file isolates the complex inequality used in the nonconstant affine case
of the one-variable Lieb--Sokal argument.
-/

namespace RealRooted

open Filter Metric
open scoped BigOperators Topology

/-- The logarithmic derivative of a nonconstant polynomial with no roots in
the open upper half-plane has strictly negative imaginary part there. -/
theorem _root_.Polynomial.derivative_eval_div_eval_im_neg
    (p : Polynomial ℂ)
    (hp : ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0)
    (hdegree : p.natDegree ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    (p.derivative.eval z / p.eval z).im < 0 := by
  have hpz : p.eval z ≠ 0 := hp z hz
  have hpne : p ≠ 0 := by
    intro hzero
    simp [hzero] at hpz
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hroots_ne : p.roots ≠ 0 := hsplits.roots_ne_zero hdegree
  have hroots_im : ∀ r ∈ p.roots, r.im ≤ 0 := by
    intro r hr
    exact le_of_not_gt fun hrpos =>
      hp r hrpos ((Polynomial.mem_roots hpne).mp hr)
  let S : Multiset ℂ := p.roots.map fun r => 1 / (z - r)
  have hS_ne : S ≠ 0 := by simp [S, hroots_ne]
  have hS_im (u : ℂ) (hu : u ∈ S) : u.im < 0 := by
    dsimp [S] at hu
    rw [Multiset.mem_map] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    exact Complex.one_div_sub_im_neg ((hroots_im r hr).trans_lt hz)
  have hsum_im : S.sum.im < 0 := by
    have hmap : S.sum.im = (S.map fun u => u.im).sum := by
      simpa using map_multiset_sum Complex.imAddGroupHom S
    rw [hmap]
    have hlt : (S.map fun u => u.im).sum <
        (S.map fun _ : ℂ => (0 : ℝ)).sum :=
      Multiset.sum_lt_sum_of_nonempty hS_ne hS_im
    simpa using hlt
  rw [hsplits.eval_derivative_div_eval_of_ne_zero hpz]
  exact hsum_im

/-- The logarithmic derivative of a polynomial with no roots in the open
upper half-plane has nonpositive imaginary part there. -/
theorem _root_.Polynomial.derivative_eval_div_eval_im_nonpos
    (p : Polynomial ℂ)
    (hp : ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0)
    {z : ℂ} (hz : 0 < z.im) :
    (p.derivative.eval z / p.eval z).im ≤ 0 := by
  by_cases hdegree : p.natDegree = 0
  · rw [Polynomial.derivative_of_natDegree_zero hdegree]
    simp
  exact (p.derivative_eval_div_eval_im_neg hp hdegree hz).le

/-- A complex polynomial with no roots in the open upper half-plane has zero
derivative or a derivative with the same property. -/
theorem _root_.Polynomial.derivative_zero_or_upperHalfPlaneStable (p : Polynomial ℂ)
    (hp : ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0) :
    p.derivative = 0 ∨ (∀ z : ℂ, 0 < z.im → p.derivative.eval z ≠ 0) := by
  by_cases hd : p.derivative = 0
  · exact Or.inl hd
  right
  intro z hz hzero
  have hpdeg : 0 < p.degree := by
    by_contra h
    push Not at h
    have ha := Polynomial.degree_le_zero_iff.mp h
    rw [ha] at hd
    simp at hd
  have hzmem : z ∈ p.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    exact ⟨hd, by simpa using hzero⟩
  have hsub := Polynomial.rootSet_derivative_subset_convexHull_rootSet (P := p) hpdeg hzmem
  have hconv : convexHull ℝ (p.rootSet ℂ) ⊆ {w : ℂ | Complex.imLm w ≤ 0} := by
    apply convexHull_min
    · intro w hw
      rw [Polynomial.mem_rootSet] at hw
      simp only [Set.mem_ofPred_eq, Complex.imLm, LinearMap.coe_mk, AddHom.coe_mk]
      by_contra hcon
      exact hp w (not_le.mp hcon) (by simpa using hw.2)
    · exact convex_halfSpace_le Complex.imLm.isLinear 0
  have hmem := hconv hsub
  simp only [Set.mem_ofPred_eq, Complex.imLm, LinearMap.coe_mk, AddHom.coe_mk] at hmem
  linarith

/-- Subtracting the derivative preserves absence of roots in the open upper
half-plane. -/
theorem _root_.Polynomial.sub_derivative_upperHalfPlaneStable
    (p : Polynomial ℂ) (hp : ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0) :
    ∀ z : ℂ, 0 < z.im → (p - p.derivative).eval z ≠ 0 := by
  intro z hz
  have hpz : p.eval z ≠ 0 := hp z hz
  by_cases hdegree : p.natDegree = 0
  · rw [Polynomial.derivative_of_natDegree_zero hdegree]
    simpa using hpz
  have hratio_im := p.derivative_eval_div_eval_im_neg hp hdegree hz
  intro hzero
  have heval : p.eval z = p.derivative.eval z := by
    apply sub_eq_zero.mp
    simpa only [Polynomial.eval_sub] using hzero
  have hratio : p.derivative.eval z / p.eval z = 1 :=
    (div_eq_one_iff_eq hpz).mpr heval.symm
  rw [hratio] at hratio_im
  simp at hratio_im

/-- Each coordinate logarithmic derivative of a stable multivariate
polynomial has nonpositive imaginary part in the upper half-plane. -/
theorem MvUpperHalfPlaneStable.eval_pderiv_div_eval_im_nonpos
    {σ : Type*} {P : MvPolynomial σ ℂ}
    (hP : MvUpperHalfPlaneStable P) (i : σ)
    (z : σ → ℂ) (hz : ∀ j, 0 < (z j).im) :
    (MvPolynomial.eval z (MvPolynomial.pderiv i P) /
      MvPolynomial.eval z P).im ≤ 0 := by
  classical
  let p : Polynomial ℂ := affineLineRestriction
    (Function.update z i 0) (Function.update (0 : σ → ℂ) i 1) P
  have hp (t : ℂ) (ht : 0 < t.im) : p.eval t ≠ 0 := by
    dsimp [p]
    rw [eval_affineLineRestriction_coordinate]
    apply hP
    intro j
    by_cases hji : j = i
    · subst j
      simpa using ht
    · simp [hji, hz j]
  have hratio := Polynomial.derivative_eval_div_eval_im_nonpos p hp (hz i)
  dsimp [p] at hratio
  rw [affineLineRestriction_derivative_coordinate,
    eval_affineLineRestriction_coordinate,
    eval_affineLineRestriction_coordinate] at hratio
  simpa using hratio

/-- Adjoining a fresh variable times a nonnegative real directional derivative
preserves upper-half-plane stability. -/
theorem MvUpperHalfPlaneStable.directionalPDeriv_pencil
    {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℂ}
    (hP : MvUpperHalfPlaneStable P) (c : σ → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    MvUpperHalfPlaneStable
      (MvPolynomial.rename some P + MvPolynomial.X none *
        MvPolynomial.rename some
          (directionalPDeriv (fun i => (c i : ℂ)) P)) := by
  classical
  intro z hz
  let x : σ → ℂ := fun i => z (some i)
  let q : ℂ := MvPolynomial.eval x P
  let d : ℂ := ∑ i : σ,
    (c i : ℂ) * MvPolynomial.eval x (MvPolynomial.pderiv i P)
  have hq : q ≠ 0 := hP x fun i => hz (some i)
  have hratio : (d / q).im ≤ 0 := by
    have heq : d / q = ∑ i : σ, (c i : ℂ) *
        (MvPolynomial.eval x (MvPolynomial.pderiv i P) / q) := by
      simp only [d]
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq, Complex.im_sum]
    apply Finset.sum_nonpos
    intro i _
    rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (hc i)
      (hP.eval_pderiv_div_eval_im_nonpos i x fun j => hz (some j))
  have hw : 0 < (-1 / z none).im := by
    have hzne : z none ≠ 0 := by
      intro h
      have him : (z none).im = 0 := by
        simpa only [Complex.zero_im] using congrArg Complex.im h
      exact (ne_of_gt (hz none)) him
    rw [neg_div, one_div, Complex.neg_im, Complex.inv_im]
    exact neg_pos.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos (hz none))
      (Complex.normSq_pos.mpr hzne))
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_rename, directionalPDeriv,
    map_sum, MvPolynomial.eval_C]
  change q + z none * d ≠ 0
  intro hzero
  have hzne : z none ≠ 0 := by
    intro h
    have him : (z none).im = 0 := by
      simpa only [Complex.zero_im] using congrArg Complex.im h
    exact (ne_of_gt (hz none)) him
  have heq : d / q = -1 / z none := by
    apply (div_eq_iff hq).2
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hzne).2
    calc
      d * z none = z none * d := mul_comm _ _
      _ = -q := eq_neg_of_add_eq_zero_right hzero
      _ = -1 * q := by ring
  rw [heq] at hratio
  linarith

/-- The all-ones directional-derivative pencil is stable. -/
theorem MvUpperHalfPlaneStable.sum_pderiv_pencil
    {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℂ}
    (hP : MvUpperHalfPlaneStable P) :
    MvUpperHalfPlaneStable
      (MvPolynomial.rename some P + MvPolynomial.X none *
        MvPolynomial.rename some (∑ i : σ, MvPolynomial.pderiv i P)) := by
  simpa [directionalPDeriv] using
    hP.directionalPDeriv_pencil (fun _ => (1 : ℝ)) fun _ => zero_le_one

/-- A nonnegative directional-derivative pencil over a real stable polynomial
is real stable. -/
theorem MvRealStable.directionalPDeriv_pencil
    {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℝ}
    (hP : MvRealStable P) (c : σ → ℝ) (hc : ∀ i, 0 ≤ c i) :
    MvRealStable
      (MvPolynomial.rename some P + MvPolynomial.X none *
        MvPolynomial.rename some (directionalPDeriv c P)) := by
  unfold MvRealStable at hP ⊢
  have h := hP.directionalPDeriv_pencil c hc
  simpa [complexifyMv, directionalPDeriv, MvPolynomial.map_rename,
    MvPolynomial.pderiv_map] using h

/-- The real all-ones directional-derivative pencil is stable. -/
theorem MvRealStable.sum_pderiv_pencil
    {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℝ}
    (hP : MvRealStable P) :
    MvRealStable
      (MvPolynomial.rename some P + MvPolynomial.X none *
        MvPolynomial.rename some (∑ i : σ, MvPolynomial.pderiv i P)) := by
  simpa [directionalPDeriv] using
    hP.directionalPDeriv_pencil (fun _ => (1 : ℝ)) fun _ => zero_le_one

/-- Renaming a nonnegative directional-derivative pencil into any target
coordinates preserves upper-half-plane stability. Coordinate identification is
allowed; neither injectivity nor freshness is needed. -/
theorem MvUpperHalfPlaneStable.directionalPDeriv_pencil_rename
    {σ τ : Type*} [Fintype σ] {P : MvPolynomial σ ℂ}
    (hP : MvUpperHalfPlaneStable P) (c : σ → ℝ)
    (hc : ∀ i, 0 ≤ c i) (f : σ → τ) (z : τ) :
    MvUpperHalfPlaneStable
      (MvPolynomial.rename f P + MvPolynomial.X z *
        MvPolynomial.rename f
          (directionalPDeriv (fun i => (c i : ℂ)) P)) := by
  let g : Option σ → τ := fun o => o.elim z f
  have h := (hP.directionalPDeriv_pencil c hc).rename (f := g)
  simpa [g, MvPolynomial.rename_rename, Function.comp_def] using h

/-- The target-coordinate version of the all-ones directional-derivative
pencil. -/
theorem MvUpperHalfPlaneStable.sum_pderiv_pencil_rename
    {σ τ : Type*} [Fintype σ] {P : MvPolynomial σ ℂ}
    (hP : MvUpperHalfPlaneStable P) (f : σ → τ) (z : τ) :
    MvUpperHalfPlaneStable
      (MvPolynomial.rename f P + MvPolynomial.X z *
        MvPolynomial.rename f (∑ i : σ, MvPolynomial.pderiv i P)) := by
  simpa [directionalPDeriv] using
    hP.directionalPDeriv_pencil_rename (fun _ => (1 : ℝ))
      (fun _ => zero_le_one) f z

/-- The real target-coordinate version of a nonnegative
directional-derivative pencil. -/
theorem MvRealStable.directionalPDeriv_pencil_rename
    {σ τ : Type*} [Fintype σ] {P : MvPolynomial σ ℝ}
    (hP : MvRealStable P) (c : σ → ℝ) (hc : ∀ i, 0 ≤ c i)
    (f : σ → τ) (z : τ) :
    MvRealStable
      (MvPolynomial.rename f P + MvPolynomial.X z *
        MvPolynomial.rename f (directionalPDeriv c P)) := by
  unfold MvRealStable at hP ⊢
  have h := hP.directionalPDeriv_pencil_rename c hc f z
  simpa [complexifyMv, directionalPDeriv, MvPolynomial.map_rename,
    MvPolynomial.pderiv_map] using h

/-- The real target-coordinate version of the all-ones
directional-derivative pencil. -/
theorem MvRealStable.sum_pderiv_pencil_rename
    {σ τ : Type*} [Fintype σ] {P : MvPolynomial σ ℝ}
    (hP : MvRealStable P) (f : σ → τ) (z : τ) :
    MvRealStable
      (MvPolynomial.rename f P + MvPolynomial.X z *
        MvPolynomial.rename f (∑ i : σ, MvPolynomial.pderiv i P)) := by
  simpa [directionalPDeriv] using
    hP.directionalPDeriv_pencil_rename (fun _ => (1 : ℝ))
      (fun _ => zero_le_one) f z

/-- A partial derivative of a coordinatewise affine stable polynomial is zero
or stable. -/
theorem MvUpperHalfPlaneStable.pderiv_zero_or_of_degreeOf_le_one
    {sigma : Type*}
    {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P)
    (i : sigma) (hi : P.degreeOf i ≤ 1) :
    MvPolynomial.pderiv i P = 0 ∨
      MvUpperHalfPlaneStable (MvPolynomial.pderiv i P) := by
  classical
  by_cases hQ : MvPolynomial.pderiv i P = 0
  · exact Or.inl hQ
  right
  intro z hz hQz
  obtain ⟨u, _, hQu⟩ := exists_upperHalfPlane_eval_ne_zero hQ
  let z₁ : sigma → ℂ := fun j =>
    if j ∈ (MvPolynomial.pderiv i P).vars then u j else z j
  have hQz₁ : MvPolynomial.eval z₁ (MvPolynomial.pderiv i P) ≠ 0 := by
    have heval := MvPolynomial.eval_eq_of_eq_on_vars
      (MvPolynomial.pderiv i P) z₁ u (by
      intro j hj
      simp [z₁, hj])
    rw [heval]
    exact hQu
  let v : sigma → ℂ := fun j => z₁ j - z j
  let A : Polynomial ℂ := affineLineRestriction z v (MvPolynomial.pderiv i P)
  let B : Polynomial ℂ := affineLineRestriction
    (Function.update z i 0) (Function.update v i 0) P
  have hA0 : A.eval 0 = 0 := by simp [A, hQz]
  have hA1 : A.eval 1 ≠ 0 := by simpa [A, v] using hQz₁
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.eval_zero] at hA1
    exact hA1 rfl
  have hB_eval (t : ℂ) :
      B.eval t = MvPolynomial.eval
        (Function.update (fun j => z j + v j * t) i 0) P := by
    change (affineLineRestriction
      (Function.update z i 0) (Function.update v i 0) P).eval t = _
    rw [eval_affineLineRestriction]
    apply congrArg (fun u : sigma → ℂ => MvPolynomial.eval u P)
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp only [Function.update_of_ne hji]
  have hPz : MvPolynomial.eval z P ≠ 0 := hP z hz
  have hconst :
      MvPolynomial.eval (Function.update z i 0) P = MvPolynomial.eval z P := by
    have h := MvPolynomial.eval_update_eq_eval_pderiv_mul_add_of_degreeOf_le_one
      hi z (z i)
    rw [hQz] at h
    simpa only [Function.update_eq_self, zero_mul, zero_add] using h.symm
  have hB0 : B.eval 0 ≠ 0 := by
    rw [hB_eval]
    simpa [hconst] using hPz
  let U : Set ℂ :=
    {t | ∀ j ∈ (MvPolynomial.pderiv i P).vars,
      0 < (z j + v j * t).im}
  have hUopen : IsOpen U := by
    rw [show U = ⋂ j ∈ (MvPolynomial.pderiv i P).vars,
        {t : ℂ | 0 < (z j + v j * t).im} by
      ext t
      simp [U]]
    exact isOpen_biInter_finset fun _ _ =>
      isOpen_lt continuous_const (by fun_prop)
  have hzeroU : (0 : ℂ) ∈ U := by
    intro j _
    simpa using hz j
  have hUnhds : U ∈ 𝓝 0 := hUopen.mem_nhds hzeroU
  obtain ⟨t, htU, hAt, _, hroot⟩ :=
    Polynomial.exists_neg_div_im_pos_of_mem_nhds A B hA hA0 hB0 U hUnhds
  let zt : sigma → ℂ := fun j => z j + v j * t
  let r : ℂ := -B.eval t / A.eval t
  have hr : 0 < r.im := hroot
  have hzroot : ∀ j, 0 < (Function.update zt i r j).im := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hr
    · rw [Function.update_of_ne hji]
      by_cases hjQ : j ∈ (MvPolynomial.pderiv i P).vars
      · exact htU j hjQ
      · simpa [zt, v, z₁, hjQ] using hz j
  apply hP (Function.update zt i r) hzroot
  rw [MvPolynomial.eval_update_eq_eval_pderiv_mul_add_of_degreeOf_le_one hi]
  have hAeval : MvPolynomial.eval zt (MvPolynomial.pderiv i P) = A.eval t := by simp [A, zt]
  have hBeval : MvPolynomial.eval (Function.update zt i 0) P = B.eval t := by rw [hB_eval]
  rw [hAeval, hBeval]
  dsimp [r]
  field_simp
  ring

/-- A partial derivative of a multiaffine stable polynomial is zero or stable. -/
theorem MvUpperHalfPlaneStable.pderiv_zero_or
    {sigma : Type*}
    {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P)
    (hPma : MvPolynomial.IsMultiaffine P) (i : sigma) :
    MvPolynomial.pderiv i P = 0 ∨
      MvUpperHalfPlaneStable (MvPolynomial.pderiv i P) := by
  exact hP.pderiv_zero_or_of_degreeOf_le_one i (hPma i)

/-- A partial derivative of a real stable polynomial is either zero or real
stable when the polynomial is affine in that coordinate. -/
theorem MvRealStable.pderiv_zero_or_of_degreeOf_le_one
    {sigma : Type*} {P : MvPolynomial sigma ℝ} (hP : MvRealStable P)
    (i : sigma) (hi : P.degreeOf i ≤ 1) :
    MvRealStableOrZero (MvPolynomial.pderiv i P) := by
  classical
  rw [mvRealStableOrZero_iff_complexifyMv]
  unfold MvRealStable at hP
  have hdegree : (complexifyMv P).degreeOf i = P.degreeOf i := by
    unfold complexifyMv
    rw [MvPolynomial.degreeOf_eq_sup, MvPolynomial.degreeOf_eq_sup,
      MvPolynomial.support_map_of_injective _ Complex.ofRealHom.injective]
  have h := hP.pderiv_zero_or_of_degreeOf_le_one i (by
    rw [hdegree]
    exact hi)
  change MvUpperHalfPlaneStableOrZero
    (complexifyMv (MvPolynomial.pderiv i P))
  rw [complexifyMv, ← MvPolynomial.pderiv_map]
  exact h

/-- A partial derivative of a multiaffine real stable polynomial is either
zero or real stable. -/
theorem MvRealStable.pderiv_zero_or
    {sigma : Type*} {P : MvPolynomial sigma ℝ} (hP : MvRealStable P)
    (hPma : MvPolynomial.IsMultiaffine P) (i : sigma) :
    MvRealStableOrZero (MvPolynomial.pderiv i P) :=
  hP.pderiv_zero_or_of_degreeOf_le_one i (hPma i)

/-- Specializing one affine coordinate at zero preserves stability up to zero. -/
theorem MvUpperHalfPlaneStable.specializeZero_zero_or_of_degreeOf_le_one
    {sigma : Type*}
    {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P)
    (i : sigma) (hi : P.degreeOf i ≤ 1) :
    MvPolynomial.specializeZero i P = 0 ∨
      MvUpperHalfPlaneStable (MvPolynomial.specializeZero i P) := by
  classical
  let Q := MvPolynomial.specializeZero i P
  by_cases hQ : Q = 0
  · exact Or.inl hQ
  right
  intro z hz hQz
  obtain ⟨u, _, hQu⟩ := exists_upperHalfPlane_eval_ne_zero hQ
  let z₁ : sigma → ℂ := fun j => if j ∈ Q.vars then u j else z j
  have hQz₁ : MvPolynomial.eval z₁ Q ≠ 0 := by
    have heval := MvPolynomial.eval_eq_of_eq_on_vars Q z₁ u (by
      intro j hj
      simp [z₁, hj])
    rw [heval]
    exact hQu
  let v : sigma → ℂ := fun j => z₁ j - z j
  let A : Polynomial ℂ := affineLineRestriction z v Q
  let B : Polynomial ℂ := affineLineRestriction z v (MvPolynomial.pderiv i P)
  have hA0 : A.eval 0 = 0 := by
    simp only [A, eval_affineLineRestriction, mul_zero, add_zero]
    simpa [Q] using hQz
  have hA1 : A.eval 1 ≠ 0 := by simpa [A, v] using hQz₁
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.eval_zero] at hA1
    exact hA1 rfl
  have hPz : MvPolynomial.eval z P ≠ 0 := hP z hz
  have hPaff := MvPolynomial.eval_update_eq_eval_pderiv_mul_add_of_degreeOf_le_one
    hi z (z i)
  have hQeval : MvPolynomial.eval z Q =
      MvPolynomial.eval (Function.update z i 0) P := by
    exact MvPolynomial.eval_specializeZero i P z
  have hB0 : B.eval 0 ≠ 0 := by
    simp only [B, eval_affineLineRestriction, mul_zero, add_zero]
    intro hzero
    rw [Function.update_eq_self] at hPaff
    rw [hzero, zero_mul, zero_add, ← hQeval, hQz] at hPaff
    exact hPz hPaff
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
  have hUnhds : U ∈ 𝓝 0 := hUopen.mem_nhds hzeroU
  obtain ⟨t, htU, _, hBt, hroot⟩ :=
    Polynomial.exists_neg_self_div_im_pos_of_mem_nhds A B hA hA0 hB0 U hUnhds
  let zt : sigma → ℂ := fun j => z j + v j * t
  let r : ℂ := -A.eval t / B.eval t
  have hr : 0 < r.im := hroot
  have hzroot : ∀ j, 0 < (Function.update zt i r j).im := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hr
    · rw [Function.update_of_ne hji]
      by_cases hjQ : j ∈ Q.vars
      · exact htU j hjQ
      · simpa [zt, v, z₁, hjQ] using hz j
  apply hP (Function.update zt i r) hzroot
  rw [MvPolynomial.eval_update_eq_eval_pderiv_mul_add_of_degreeOf_le_one hi]
  have hBeval :
      MvPolynomial.eval zt (MvPolynomial.pderiv i P) = B.eval t := by
    simp [B, zt]
  have hAeval : MvPolynomial.eval (Function.update zt i 0) P = A.eval t := by
    rw [← MvPolynomial.eval_specializeZero i P zt]
    simp [A, zt, Q]
  rw [hBeval, hAeval]
  dsimp [r]
  field_simp
  ring

/-- Specializing one coordinate of a multiaffine stable polynomial at zero
preserves stability up to zero. -/
theorem MvUpperHalfPlaneStable.specializeZero_zero_or
    {sigma : Type*}
    {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P)
    (hPma : MvPolynomial.IsMultiaffine P) (i : sigma) :
    MvPolynomial.specializeZero i P = 0 ∨
      MvUpperHalfPlaneStable (MvPolynomial.specializeZero i P) := by
  exact hP.specializeZero_zero_or_of_degreeOf_le_one i (hPma i)

/-- Suppose the affine function `a * z + b` has no zero in the open upper half
plane and `f + w * (a * z + b)` is nonzero for every upper-half-plane `w`.
When `a` is nonzero, `f` cannot equal its derivative coefficient `a`. -/
theorem liebSokalPointwise_of_ne
    (a b f z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im)
    (hroot : (-b / a).im ≤ 0)
    (hw : ∀ w : ℂ, 0 < w.im → f + w * (a * z + b) ≠ 0) :
    f - a ≠ 0 := by
  intro hfa
  have hfeq : f = a := sub_eq_zero.mp hfa
  have hg : a * z + b ≠ 0 := by
    intro hg
    have hzroot : z = -b / a := by
      apply (eq_div_iff ha).2
      rw [mul_comm]
      exact eq_neg_of_add_eq_zero_left hg
    have := congrArg Complex.im hzroot
    nlinarith
  have hratio : 0 ≤ (f / (a * z + b)).im := by
    by_contra hnonneg
    have hlt : (f / (a * z + b)).im < 0 := lt_of_not_ge hnonneg
    have hwim : 0 < (-f / (a * z + b)).im := by
      rw [neg_div, Complex.neg_im]
      exact neg_pos.mpr hlt
    have hne := hw (-f / (a * z + b)) hwim
    apply hne
    field_simp
    ring
  have hbim : 0 ≤ (b / a).im := by
    rw [neg_div, Complex.neg_im] at hroot
    linarith
  let u : ℂ := z + b / a
  have huim : 0 < u.im := by
    simp only [u, Complex.add_im]
    linarith
  have hune : u ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    have hzero : u.im = 0 := by simpa using this
    linarith
  have hratioeq : a / (a * z + b) = 1 / u := by
    dsimp [u]
    field_simp
  have hratio_neg : (f / (a * z + b)).im < 0 := by
    rw [hfeq, hratioeq, one_div, Complex.inv_im]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos huim) (Complex.normSq_pos.mpr hune)
  exact (not_lt_of_ge hratio) hratio_neg

/-- The root of an affine slice of a stable multiaffine polynomial is outside
the open upper half-plane. -/
theorem MvUpperHalfPlaneStable.affineRoot_im_nonpos_of_degreeOf_le_one
    {sigma : Type*} [DecidableEq sigma] {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P) (i : sigma) (hi : P.degreeOf i ≤ 1)
    (z : sigma → ℂ) (hz : ∀ j, 0 < (z j).im)
    (ha : MvPolynomial.eval z (MvPolynomial.pderiv i P) ≠ 0) :
    (-MvPolynomial.eval (Function.update z i 0) P /
        MvPolynomial.eval z (MvPolynomial.pderiv i P)).im ≤ 0 := by
  by_contra hnonpos
  have hpos :
      0 < (-MvPolynomial.eval (Function.update z i 0) P /
        MvPolynomial.eval z (MvPolynomial.pderiv i P)).im :=
    lt_of_not_ge hnonpos
  let t : ℂ := -MvPolynomial.eval (Function.update z i 0) P /
    MvPolynomial.eval z (MvPolynomial.pderiv i P)
  let zroot : sigma → ℂ := Function.update z i t
  have hzroot : ∀ j, 0 < (zroot j).im := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [zroot] using hpos
    · simp [zroot, hji, hz j]
  apply hP zroot hzroot
  rw [show zroot = Function.update z i t by rfl,
    MvPolynomial.eval_update_eq_eval_pderiv_mul_add_of_degreeOf_le_one hi]
  dsimp [t]
  field_simp
  ring

/-- The root of an affine slice of a stable multiaffine polynomial is outside
the open upper half-plane. -/
theorem MvUpperHalfPlaneStable.affineRoot_im_nonpos
    {sigma : Type*} [DecidableEq sigma] {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P) (hPma : MvPolynomial.IsMultiaffine P)
    (i : sigma) (z : sigma → ℂ) (hz : ∀ j, 0 < (z j).im)
    (ha : MvPolynomial.eval z (MvPolynomial.pderiv i P) ≠ 0) :
    (-MvPolynomial.eval (Function.update z i 0) P /
        MvPolynomial.eval z (MvPolynomial.pderiv i P)).im ≤ 0 := by
  exact hP.affineRoot_im_nonpos_of_degreeOf_le_one i (hPma i) z hz ha

/-- One-variable Lieb--Sokal step under an explicit stable-pencil hypothesis. -/
theorem MvUpperHalfPlaneStable.sub_pderiv_of_stable_pencil_of_degreeOf_le_one
    {sigma : Type*} {F G : MvPolynomial sigma ℂ}
    (hF : MvUpperHalfPlaneStable F) (hG : MvUpperHalfPlaneStable G)
    (i : sigma) (hi : G.degreeOf i ≤ 1)
    (hFG : ∀ z : sigma → ℂ, (∀ j, 0 < (z j).im) →
      ∀ w : ℂ, 0 < w.im →
        MvPolynomial.eval z F + w * MvPolynomial.eval z G ≠ 0) :
    MvUpperHalfPlaneStable (F - MvPolynomial.pderiv i G) := by
  classical
  intro z hz
  rw [MvPolynomial.eval_sub]
  by_cases ha : MvPolynomial.eval z (MvPolynomial.pderiv i G) = 0
  · simpa [ha] using hF z hz
  · apply liebSokalPointwise_of_ne
      (MvPolynomial.eval z (MvPolynomial.pderiv i G))
      (MvPolynomial.eval (Function.update z i 0) G)
      (MvPolynomial.eval z F) (z i) ha (hz i)
      (hG.affineRoot_im_nonpos_of_degreeOf_le_one i hi z hz ha)
    intro w hw
    have hne := hFG z hz w hw
    have haff :
        MvPolynomial.eval z G =
          MvPolynomial.eval z (MvPolynomial.pderiv i G) * z i +
            MvPolynomial.eval (Function.update z i 0) G := by
      simpa using MvPolynomial.eval_update_eq_eval_pderiv_mul_add_of_degreeOf_le_one
        hi z (z i)
    rwa [haff] at hne

/-- One-variable Lieb--Sokal step under an explicit stable-pencil hypothesis. -/
theorem MvUpperHalfPlaneStable.sub_pderiv_of_stable_pencil
    {sigma : Type*} {F G : MvPolynomial sigma ℂ}
    (hF : MvUpperHalfPlaneStable F) (hG : MvUpperHalfPlaneStable G)
    (hGma : MvPolynomial.IsMultiaffine G) (i : sigma)
    (hFG : ∀ z : sigma → ℂ, (∀ j, 0 < (z j).im) →
      ∀ w : ℂ, 0 < w.im →
        MvPolynomial.eval z F + w * MvPolynomial.eval z G ≠ 0) :
    MvUpperHalfPlaneStable (F - MvPolynomial.pderiv i G) := by
  exact hF.sub_pderiv_of_stable_pencil_of_degreeOf_le_one hG i (hGma i) hFG

/-! ## The one-minus-partial-derivative operator -/

/-- Apply `1 - ∂ᵢ` to a multivariate polynomial. -/
noncomputable def oneSubPderiv {R sigma : Type*} [CommRing R] (i : sigma)
    (P : MvPolynomial sigma R) : MvPolynomial sigma R :=
  P - MvPolynomial.pderiv i P

/-- Apply an ordered list of one-minus-partial-derivative operators. -/
noncomputable def oneSubPderivList {R sigma : Type*} [CommRing R] (l : List sigma)
    (P : MvPolynomial sigma R) : MvPolynomial sigma R :=
  l.foldl (fun Q i => oneSubPderiv i Q) P

@[simp] theorem oneSubPderivList_nil {R sigma : Type*} [CommRing R]
    (P : MvPolynomial sigma R) : oneSubPderivList [] P = P :=
  rfl

@[simp] theorem oneSubPderivList_cons {R sigma : Type*} [CommRing R]
    (i : sigma) (l : List sigma) (P : MvPolynomial sigma R) :
    oneSubPderivList (i :: l) P = oneSubPderivList l (oneSubPderiv i P) :=
  rfl

/-- Applying `1 - ∂ᵢ` preserves multiaffineness. -/
theorem _root_.MvPolynomial.IsMultiaffine.oneSubPderiv
    {R sigma : Type*} [CommRing R] {P : MvPolynomial sigma R}
    (hP : P.IsMultiaffine) (i : sigma) :
    (oneSubPderiv i P).IsMultiaffine :=
  hP.sub (hP.pderiv i)

/-- Iterating `1 - ∂ᵢ` along a finite ordered list preserves multiaffineness. -/
theorem _root_.MvPolynomial.IsMultiaffine.oneSubPderivList
    {R sigma : Type*} [CommRing R] {P : MvPolynomial sigma R}
    (hP : P.IsMultiaffine) (l : List sigma) :
    (oneSubPderivList l P).IsMultiaffine := by
  induction l generalizing P with
  | nil => exact hP
  | cons i l ih => exact ih (hP.oneSubPderiv i)

/-- Applying `1 - ∂ᵢ` preserves upper-half-plane stability in arbitrary
coordinate degree. -/
theorem MvUpperHalfPlaneStable.oneSubPderiv
    {sigma : Type*} {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P) (i : sigma) :
    MvUpperHalfPlaneStable (oneSubPderiv i P) := by
  classical
  intro z hz
  let q : Polynomial ℂ :=
    affineLineRestriction (Function.update z i 0)
      (Function.update (0 : sigma → ℂ) i 1) P
  have hqstable : ∀ w : ℂ, 0 < w.im → q.eval w ≠ 0 := by
    intro w hw
    rw [show q.eval w = MvPolynomial.eval (Function.update z i w) P by
      exact eval_affineLineRestriction_coordinate z i P w]
    apply hP
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hw
    · rw [Function.update_of_ne hji]
      exact hz j
  have hq := Polynomial.sub_derivative_upperHalfPlaneStable q hqstable (z i) (hz i)
  have hqeval : q.eval (z i) = MvPolynomial.eval z P := by
    rw [show q.eval (z i) = MvPolynomial.eval (Function.update z i (z i)) P by
      exact eval_affineLineRestriction_coordinate z i P (z i)]
    simp
  have hqderiv : q.derivative.eval (z i) =
      MvPolynomial.eval z (MvPolynomial.pderiv i P) := by
    have hderiv := congrArg (fun p : Polynomial ℂ => p.eval (z i))
      (affineLineRestriction_derivative_coordinate z i P)
    change q.derivative.eval (z i) = _
    rw [hderiv, eval_affineLineRestriction_coordinate]
    simp
  change MvPolynomial.eval z (P - MvPolynomial.pderiv i P) ≠ 0
  rw [MvPolynomial.eval_sub]
  simpa only [Polynomial.eval_sub, hqeval, hqderiv] using hq

/-- Applying `1 - ∂ᵢ` preserves weak upper-half-plane stability in arbitrary
coordinate degree. -/
theorem MvUpperHalfPlaneStableOrZero.oneSubPderiv
    {sigma : Type*} {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStableOrZero P) (i : sigma) :
    MvUpperHalfPlaneStableOrZero (oneSubPderiv i P) := by
  rcases hP with rfl | hP
  · simpa [_root_.RealRooted.oneSubPderiv] using
      (MvUpperHalfPlaneStableOrZero.zero (sigma := sigma))
  exact (hP.oneSubPderiv i).orZero

/-- Iterating `1 - ∂ᵢ` along a finite ordered list preserves weak
upper-half-plane stability in arbitrary coordinate degrees. -/
theorem MvUpperHalfPlaneStableOrZero.oneSubPderivList
    {sigma : Type*} {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStableOrZero P)
    (l : List sigma) :
    MvUpperHalfPlaneStableOrZero (oneSubPderivList l P) := by
  induction l generalizing P with
  | nil => exact hP
  | cons i l ih => exact ih (hP.oneSubPderiv i)

/-- The polynomial `F(z) + w * G(z)` with `w` represented by one additional
variable. -/
noncomputable def mvPencil {R sigma : Type*} [CommSemiring R]
    (F G : MvPolynomial sigma R) : MvPolynomial (Sum sigma Unit) R :=
  MvPolynomial.rename Sum.inl F +
    MvPolynomial.X (Sum.inr ()) * MvPolynomial.rename Sum.inl G

@[simp] theorem eval_mvPencil {R sigma : Type*} [CommSemiring R]
    (F G : MvPolynomial sigma R) (z : sigma → R) (w : R) :
    MvPolynomial.eval (Sum.elim z fun _ => w) (mvPencil F G) =
      MvPolynomial.eval z F + w * MvPolynomial.eval z G := by
  simp only [mvPencil, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_rename]
  rfl

theorem MvUpperHalfPlaneStable.pencil_nonzero
    {sigma : Type*} {F G : MvPolynomial sigma ℂ}
    (hFG : MvUpperHalfPlaneStable (mvPencil F G))
    (z : sigma → ℂ) (hz : ∀ i, 0 < (z i).im)
    (w : ℂ) (hw : 0 < w.im) :
    MvPolynomial.eval z F + w * MvPolynomial.eval z G ≠ 0 := by
  rw [← eval_mvPencil]
  apply hFG (Sum.elim z fun _ => w)
  intro i
  cases i with
  | inl i => exact hz i
  | inr i => exact hw

/-- One-variable Lieb--Sokal step stated using a stable polynomial pencil on
an added variable. -/
theorem MvUpperHalfPlaneStable.sub_pderiv_of_stable_mvPencil_of_degreeOf_le_one
    {sigma : Type*} {F G : MvPolynomial sigma ℂ}
    (hF : MvUpperHalfPlaneStable F) (hG : MvUpperHalfPlaneStable G)
    (i : sigma) (hi : G.degreeOf i ≤ 1)
    (hFG : MvUpperHalfPlaneStable (mvPencil F G)) :
    MvUpperHalfPlaneStable (F - MvPolynomial.pderiv i G) := by
  apply hF.sub_pderiv_of_stable_pencil_of_degreeOf_le_one hG i hi
  intro z hz w hw
  exact hFG.pencil_nonzero z hz w hw

/-- One-variable Lieb--Sokal step stated using a stable polynomial pencil on
an added variable. -/
theorem MvUpperHalfPlaneStable.sub_pderiv_of_stable_mvPencil
    {sigma : Type*} {F G : MvPolynomial sigma ℂ}
    (hF : MvUpperHalfPlaneStable F) (hG : MvUpperHalfPlaneStable G)
    (hGma : MvPolynomial.IsMultiaffine G) (i : sigma)
    (hFG : MvUpperHalfPlaneStable (mvPencil F G)) :
    MvUpperHalfPlaneStable (F - MvPolynomial.pderiv i G) := by
  exact hF.sub_pderiv_of_stable_mvPencil_of_degreeOf_le_one hG i (hGma i) hFG

/-- Eliminating one variable by replacing it with negative partial
differentiation in another variable preserves stability, up to zero. -/
theorem MvUpperHalfPlaneStable.contractVariables_zero_or_of_degreeOf_le_one
    {sigma : Type*}
    {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P)
    (i j : sigma) (hi : P.degreeOf i ≤ 1) (hj : P.degreeOf j ≤ 1) :
    contractVariables i j P = 0 ∨
      MvUpperHalfPlaneStable (contractVariables i j P) := by
  classical
  let F := MvPolynomial.specializeZero i P
  let G := MvPolynomial.pderiv i P
  have hGj : (MvPolynomial.pderiv i P).degreeOf j ≤ 1 :=
    (MvPolynomial.degreeOf_pderiv_le P i j).trans hj
  have hFzero : F = 0 ∨ MvUpperHalfPlaneStable F := by
    simpa [F] using hP.specializeZero_zero_or_of_degreeOf_le_one i hi
  have hGzero : G = 0 ∨ MvUpperHalfPlaneStable G := by
    simpa [G] using hP.pderiv_zero_or_of_degreeOf_le_one i hi
  change F - MvPolynomial.pderiv j G = 0 ∨
    MvUpperHalfPlaneStable (F - MvPolynomial.pderiv j G)
  rcases hFzero with hF | hF <;> rcases hGzero with hG | hG
  · left
    simp [hF, hG]
  · rcases hG.pderiv_zero_or_of_degreeOf_le_one j hGj with hD | hD
    · left
      simp [hF, hD]
    · right
      rw [hF, zero_sub]
      intro z hz
      rw [MvPolynomial.eval_neg]
      exact neg_ne_zero.mpr (hD z hz)
  · right
    simpa [hG] using hF
  · right
    apply hF.sub_pderiv_of_stable_pencil_of_degreeOf_le_one hG j hGj
    intro z hz w hw
    have hzupdate : ∀ k, 0 < (Function.update z i w k).im := by
      intro k
      by_cases hki : k = i
      · subst k
        simpa using hw
      · rw [Function.update_of_ne hki]
        exact hz k
    have hne := hP (Function.update z i w) hzupdate
    rw [MvPolynomial.eval_update_eq_eval_pderiv_mul_add_of_degreeOf_le_one hi]
      at hne
    change MvPolynomial.eval z F + w * MvPolynomial.eval z G ≠ 0
    rw [show MvPolynomial.eval z F =
      MvPolynomial.eval (Function.update z i 0) P by
        exact MvPolynomial.eval_specializeZero i P z]
    simpa only [G, add_comm, mul_comm] using hne

/-- Eliminating one variable by replacing it with negative partial
differentiation in another variable preserves stability, up to zero. -/
theorem MvUpperHalfPlaneStable.contractVariables_zero_or
    {sigma : Type*}
    {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P)
    (hPma : MvPolynomial.IsMultiaffine P) (i j : sigma) :
    contractVariables i j P = 0 ∨
      MvUpperHalfPlaneStable (contractVariables i j P) := by
  exact hP.contractVariables_zero_or_of_degreeOf_le_one i j (hPma i) (hPma j)

/-- A finite sequence of mapped contractions preserves stability, up to zero,
provided only the listed contracted coordinates are affine. -/
theorem MvUpperHalfPlaneStable.contractMappedVariablePairs_zero_or_of_degreeOf_le_one
    {sigma omega : Type*}
    {P : MvPolynomial omega ℂ}
    (hP : MvUpperHalfPlaneStable P)
    (left right : sigma → omega) (l : List sigma)
    (hPaffine : ∀ i ∈ l,
      P.degreeOf (left i) ≤ 1 ∧ P.degreeOf (right i) ≤ 1) :
    contractMappedVariablePairs left right l P = 0 ∨
      MvUpperHalfPlaneStable (contractMappedVariablePairs left right l P) := by
  induction l generalizing P with
  | nil => exact Or.inr hP
  | cons i l ih =>
      rw [contractMappedVariablePairs_cons]
      have hi := hPaffine i (List.mem_cons_self)
      rcases hP.contractVariables_zero_or_of_degreeOf_le_one
          (left i) (right i) hi.1 hi.2 with hQ | hQ
      · left
        simp [hQ]
      · apply ih hQ
        intro k hk
        have hkP := hPaffine k (List.mem_cons_of_mem i hk)
        exact ⟨
          (degreeOf_contractVariables_le P
            (left i) (right i) (left k)).trans hkP.1,
          (degreeOf_contractVariables_le P
            (left i) (right i) (right k)).trans hkP.2⟩

/-- A product of stable polynomials in disjoint left and right variable blocks
is stable. -/
theorem MvUpperHalfPlaneStable.pairedProduct
    {sigma : Type*} {F G : MvPolynomial sigma ℂ}
    (hF : MvUpperHalfPlaneStable F) (hG : MvUpperHalfPlaneStable G) :
    MvUpperHalfPlaneStable (RealRooted.pairedProduct F G) := by
  exact hF.rename.mul hG.rename

/-- A finite sequence of paired contractions preserves stability, up to
zero. -/
theorem MvUpperHalfPlaneStable.contractVariablePairs_zero_or
    {sigma : Type*} [Finite sigma]
    {P : MvPolynomial (Sum sigma sigma) ℂ}
    (hP : MvUpperHalfPlaneStable P)
    (hPma : MvPolynomial.IsMultiaffine P) (l : List sigma) :
    contractVariablePairs l P = 0 ∨
      MvUpperHalfPlaneStable (contractVariablePairs l P) := by
  unfold contractVariablePairs
  induction l generalizing P with
  | nil => exact Or.inr hP
  | cons i l ih =>
      rw [List.foldl_cons]
      rcases hP.contractVariables_zero_or hPma (Sum.inl i) (Sum.inr i) with hQ | hQ
      · left
        change contractVariablePairs l
          (contractVariables (Sum.inl i) (Sum.inr i) P) = 0
        rw [hQ]
        exact contractVariablePairs_zero l
      · exact ih hQ (isMultiaffine_contractVariables hPma (Sum.inl i) (Sum.inr i))

end RealRooted
