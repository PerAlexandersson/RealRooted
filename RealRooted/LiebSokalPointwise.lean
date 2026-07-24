import RealRooted.Multiaffine
import RealRooted.MultivariateStability
import RealRooted.LiebSokalOperator
import RealRooted.Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Polynomial.GaussLucas

/-!
# Pointwise input for the Lieb--Sokal theorem

This file isolates the complex inequality used in the nonconstant affine case
of the one-variable Lieb--Sokal argument.
-/

namespace RealRooted

open Filter Metric
open scoped Topology

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
      simp only [Set.mem_setOf_eq, Complex.imLm, LinearMap.coe_mk, AddHom.coe_mk]
      by_contra hcon
      exact hp w (not_le.mp hcon) (by simpa using hw.2)
    · exact convex_halfSpace_le Complex.imLm.isLinear 0
  have hmem := hconv hsub
  simp only [Set.mem_setOf_eq, Complex.imLm, LinearMap.coe_mk, AddHom.coe_mk] at hmem
  linarith

/-- A partial derivative of a finite-variable multiaffine stable polynomial is
zero or stable. -/
theorem MvUpperHalfPlaneStable.pderiv_zero_or
    {sigma : Type*} [Finite sigma]
    {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P)
    (hPma : MvPolynomial.IsMultiaffine P) (i : sigma) :
    MvPolynomial.pderiv i P = 0 ∨
      MvUpperHalfPlaneStable (MvPolynomial.pderiv i P) := by
  classical
  by_cases hQ : MvPolynomial.pderiv i P = 0
  · exact Or.inl hQ
  right
  intro z hz hQz
  obtain ⟨z₁, _, hQz₁⟩ := exists_upperHalfPlane_eval_ne_zero hQ
  let v : sigma → ℂ := fun j => z₁ j - z j
  let A : Polynomial ℂ := affineLineRestriction z v (MvPolynomial.pderiv i P)
  let B : Polynomial ℂ := affineLineRestriction
    (Function.update z i 0) (Function.update v i 0) P
  have hA0 : A.eval 0 = 0 := by
    simp [A, hQz]
  have hA1 : A.eval 1 ≠ 0 := by
    simpa [A, v] using hQz₁
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
    have h := hPma.eval_update_eq_eval_pderiv_mul_add i z (z i)
    rw [hQz] at h
    simpa only [Function.update_eq_self, zero_mul, zero_add] using h.symm
  have hB0 : B.eval 0 ≠ 0 := by
    rw [hB_eval]
    simpa [hconst] using hPz
  let U : Set ℂ := {t | ∀ j, 0 < (z j + v j * t).im}
  have hUopen : IsOpen U := by
    rw [show U = ⋂ j, {t : ℂ | 0 < (z j + v j * t).im} by
      ext t
      simp [U]]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt continuous_const (by fun_prop)
  have hzeroU : (0 : ℂ) ∈ U := by
    intro j
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
      exact htU j
  apply hP (Function.update zt i r) hzroot
  rw [hPma.eval_update_eq_eval_pderiv_mul_add]
  have hAeval : MvPolynomial.eval zt (MvPolynomial.pderiv i P) = A.eval t := by
    simp [A, zt]
  have hBeval : MvPolynomial.eval (Function.update zt i 0) P = B.eval t := by
    rw [hB_eval]
  rw [hAeval, hBeval]
  dsimp [r]
  field_simp
  ring

/-- Specializing a variable of a finite-variable multiaffine stable polynomial
at zero gives zero or another stable polynomial. -/
theorem MvUpperHalfPlaneStable.specializeZero_zero_or
    {sigma : Type*} [Finite sigma]
    {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P)
    (hPma : MvPolynomial.IsMultiaffine P) (i : sigma) :
    MvPolynomial.specializeZero i P = 0 ∨
      MvUpperHalfPlaneStable (MvPolynomial.specializeZero i P) := by
  classical
  let Q := MvPolynomial.specializeZero i P
  by_cases hQ : Q = 0
  · exact Or.inl hQ
  right
  intro z hz hQz
  obtain ⟨z₁, _, hQz₁⟩ := exists_upperHalfPlane_eval_ne_zero hQ
  let v : sigma → ℂ := fun j => z₁ j - z j
  let A : Polynomial ℂ := affineLineRestriction z v Q
  let B : Polynomial ℂ := affineLineRestriction z v (MvPolynomial.pderiv i P)
  have hA0 : A.eval 0 = 0 := by
    simp only [A, eval_affineLineRestriction, mul_zero, add_zero]
    simpa [Q] using hQz
  have hA1 : A.eval 1 ≠ 0 := by
    simpa [A, v] using hQz₁
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.eval_zero] at hA1
    exact hA1 rfl
  have hPz : MvPolynomial.eval z P ≠ 0 := hP z hz
  have hPaff := hPma.eval_update_eq_eval_pderiv_mul_add i z (z i)
  have hQeval : MvPolynomial.eval z Q =
      MvPolynomial.eval (Function.update z i 0) P := by
    exact MvPolynomial.eval_specializeZero i P z
  have hB0 : B.eval 0 ≠ 0 := by
    simp only [B, eval_affineLineRestriction, mul_zero, add_zero]
    intro hzero
    rw [Function.update_eq_self] at hPaff
    rw [hzero, zero_mul, zero_add, ← hQeval, hQz] at hPaff
    exact hPz hPaff
  let U : Set ℂ := {t | ∀ j, 0 < (z j + v j * t).im}
  have hUopen : IsOpen U := by
    rw [show U = ⋂ j, {t : ℂ | 0 < (z j + v j * t).im} by
      ext t
      simp [U]]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt continuous_const (by fun_prop)
  have hzeroU : (0 : ℂ) ∈ U := by
    intro j
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
      exact htU j
  apply hP (Function.update zt i r) hzroot
  rw [hPma.eval_update_eq_eval_pderiv_mul_add]
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
theorem MvUpperHalfPlaneStable.affineRoot_im_nonpos
    {sigma : Type*} [DecidableEq sigma] {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P) (hPma : MvPolynomial.IsMultiaffine P)
    (i : sigma) (z : sigma → ℂ) (hz : ∀ j, 0 < (z j).im)
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
    hPma.eval_update_eq_eval_pderiv_mul_add]
  dsimp [t]
  field_simp
  ring

/-- One-variable Lieb--Sokal step under an explicit stable-pencil hypothesis. -/
theorem MvUpperHalfPlaneStable.sub_pderiv_of_stable_pencil
    {sigma : Type*} {F G : MvPolynomial sigma ℂ}
    (hF : MvUpperHalfPlaneStable F) (hG : MvUpperHalfPlaneStable G)
    (hGma : MvPolynomial.IsMultiaffine G) (i : sigma)
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
      (hG.affineRoot_im_nonpos hGma i z hz ha)
    intro w hw
    have hne := hFG z hz w hw
    have haff :
        MvPolynomial.eval z G =
          MvPolynomial.eval z (MvPolynomial.pderiv i G) * z i +
            MvPolynomial.eval (Function.update z i 0) G := by
      simpa using hGma.eval_update_eq_eval_pderiv_mul_add i z (z i)
    rwa [haff] at hne

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
theorem MvUpperHalfPlaneStable.sub_pderiv_of_stable_mvPencil
    {sigma : Type*} {F G : MvPolynomial sigma ℂ}
    (hF : MvUpperHalfPlaneStable F) (hG : MvUpperHalfPlaneStable G)
    (hGma : MvPolynomial.IsMultiaffine G) (i : sigma)
    (hFG : MvUpperHalfPlaneStable (mvPencil F G)) :
    MvUpperHalfPlaneStable (F - MvPolynomial.pderiv i G) := by
  apply hF.sub_pderiv_of_stable_pencil hG hGma i
  intro z hz w hw
  exact hFG.pencil_nonzero z hz w hw

/-- Eliminating one variable by replacing it with negative partial
differentiation in another variable preserves stability, up to zero. -/
theorem MvUpperHalfPlaneStable.contractVariables_zero_or
    {sigma : Type*} [Finite sigma]
    {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P)
    (hPma : MvPolynomial.IsMultiaffine P) (i j : sigma) :
    contractVariables i j P = 0 ∨
      MvUpperHalfPlaneStable (contractVariables i j P) := by
  classical
  let F := MvPolynomial.specializeZero i P
  let G := MvPolynomial.pderiv i P
  have hGma : MvPolynomial.IsMultiaffine G := hPma.pderiv i
  have hFzero : F = 0 ∨ MvUpperHalfPlaneStable F := by
    simpa [F] using hP.specializeZero_zero_or hPma i
  have hGzero : G = 0 ∨ MvUpperHalfPlaneStable G := by
    simpa [G] using hP.pderiv_zero_or hPma i
  change F - MvPolynomial.pderiv j G = 0 ∨
    MvUpperHalfPlaneStable (F - MvPolynomial.pderiv j G)
  rcases hFzero with hF | hF <;> rcases hGzero with hG | hG
  · left
    simp [hF, hG]
  · rcases hG.pderiv_zero_or hGma j with hD | hD
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
    apply hF.sub_pderiv_of_stable_pencil hG hGma j
    intro z hz w hw
    have hzupdate : ∀ k, 0 < (Function.update z i w k).im := by
      intro k
      by_cases hki : k = i
      · subst k
        simpa using hw
      · rw [Function.update_of_ne hki]
        exact hz k
    have hne := hP (Function.update z i w) hzupdate
    rw [hPma.eval_update_eq_eval_pderiv_mul_add] at hne
    change MvPolynomial.eval z F + w * MvPolynomial.eval z G ≠ 0
    rw [show MvPolynomial.eval z F =
      MvPolynomial.eval (Function.update z i 0) P by
        exact MvPolynomial.eval_specializeZero i P z]
    simpa only [G, add_comm, mul_comm] using hne

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
