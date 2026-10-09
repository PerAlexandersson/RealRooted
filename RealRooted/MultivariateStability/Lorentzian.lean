import RealRooted.MultivariateStability.JumpSystem
import RealRooted.MultivariateStability.LinearForm
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Homogeneous real stable polynomials are Lorentzian

P. Brändén and J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), Proposition 2.2
(every homogeneous real stable polynomial with nonnegative coefficients is Lorentzian), proved
here through the characterization of their Theorem 2.25 (and the sentence following it).

**Convention.**  A polynomial `f ∈ ℝ[w₁, …, wₙ]` is `RealRooted.Lorentzian.IsLorentzian d f` if it
is homogeneous of degree `d`, has nonnegative coefficients, has M-convex support
(`IsMConvex`, the exchange property for `α, β ∈ supp f`), and for every `α ∈ ℕⁿ` with `|α| = d - 2`
the Hessian of the quadratic form `∂^α f` has at most one positive eigenvalue
(`HasAtMostOnePositiveEigenvalue`).  The paper defines Lorentzian polynomials as limits of
strictly Lorentzian ones (Definition 2.1); Theorem 2.25 shows this is equivalent.  For `d ∈ {0, 1}`
there is no Hessian condition; the zero polynomial is admitted.

`HasAtMostOnePositiveEigenvalue H` is expressed without eigenvalues, as the absence of a
positive definite plane for the form `v ↦ vᵀ H v`;
`card_positive_eigenvalues_le_one` recovers the eigenvalue count for Hermitian matrices.

**Pieces.**
* `isMConvex_support_of_stable`: the support of a homogeneous real stable polynomial is
  M-convex (from the jump-system theorem of `JumpSystem.lean`).
* `partialDeriv`, `hessian`: iterated partial derivatives (zero or stable by
  `JumpSystem.Stable.pderiv`, homogeneous, nonnegative coefficients), and Hessians.
* `hasAtMostOnePositiveEigenvalue_of_stable`: the quadratic core: a real symmetric matrix with
  nonnegative entries whose quadratic form is real stable has at most one positive eigenvalue.
* `isLorentzian_of_stable`: Proposition 2.2.
-/

open MvPolynomial Matrix

namespace RealRooted.Lorentzian

variable {n : ℕ}

/-- The real symmetric matrix `H` has at most one positive eigenvalue.  Concretely: there are no
vectors `x, y` such that the quadratic form `v ↦ vᵀ H v` is positive definite on the plane
spanned by `x` and `y`.  The Gram matrix of `x, y` is positive definite iff `Q x > 0` and
`Q x * Q y > B(x,y) ^ 2`, where `Q x = xᵀ H x` and `B(x,y) = xᵀ H y`; so the condition reads
`Q x > 0 → Q x * Q y ≤ B(x,y) ^ 2` (a reverse Cauchy–Schwarz inequality).  By Sylvester's law
of inertia this is equivalent to having at most one positive eigenvalue. -/
def HasAtMostOnePositiveEigenvalue (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, 0 < x ⬝ᵥ H *ᵥ x → (x ⬝ᵥ H *ᵥ x) * (y ⬝ᵥ H *ᵥ y) ≤ (x ⬝ᵥ H *ᵥ y) ^ 2

/-- The quadratic polynomial `∑ i j, H i j * X i * X j`. -/
noncomputable def quadPoly (H : Matrix (Fin n) (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, ∑ j, C (H i j) * (X i * X j)

private lemma eval_quadPoly (H : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℂ) :
    eval z (map (algebraMap ℝ ℂ) (quadPoly H)) = ∑ i, ∑ j, (H i j : ℂ) * (z i * z j) := by
  simp [quadPoly, map_sum]

private lemma dot_mulVec_eq (H : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    x ⬝ᵥ H *ᵥ y = ∑ i, ∑ j, H i j * (x i * y j) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma dot_mulVec_comm {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) (x y : Fin n → ℝ) :
    x ⬝ᵥ H *ᵥ y = y ⬝ᵥ H *ᵥ x := by
  rw [dot_mulVec_eq, dot_mulVec_eq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply i j]
  ring

/-- Stability of the quadratic form forces the reverse Cauchy–Schwarz inequality against every
vector `a` with positive coordinates and `Q a > 0`. -/
private lemma form_le_sq_of_stable {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (hst : JumpSystem.Stable (quadPoly H)) {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    (hQa : 0 < a ⬝ᵥ H *ᵥ a) (b : Fin n → ℝ) :
    (a ⬝ᵥ H *ᵥ a) * (b ⬝ᵥ H *ᵥ b) ≤ (a ⬝ᵥ H *ᵥ b) ^ 2 := by
  by_contra hlt
  push Not at hlt
  set A := a ⬝ᵥ H *ᵥ a with hA
  set B := a ⬝ᵥ H *ᵥ b with hB
  set C := b ⬝ᵥ H *ᵥ b with hC
  set r := Real.sqrt (A * C - B ^ 2) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hr2 : r ^ 2 = A * C - B ^ 2 := Real.sq_sqrt (by linarith)
  set s : ℂ := ⟨-B / A, r / A⟩ with hs
  apply hst (fun i => (b i : ℂ) + s * a i)
  · intro i
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, hs]
    simp only [zero_add, mul_zero]
    exact mul_pos (div_pos hrpos hQa) (ha i)
  · rw [eval_quadPoly]
    have hba : b ⬝ᵥ H *ᵥ a = B := by rw [dot_mulVec_comm hH, hB]
    have e1 : ∑ i, ∑ j, (H i j : ℂ) * (((b i : ℂ) + s * a i) * ((b j : ℂ) + s * a j)) =
        (C : ℂ) + s * ((B + B : ℝ) : ℂ) + s ^ 2 * A := by
      have hAc : (A : ℂ) = ∑ i, ∑ j, (H i j : ℂ) * (a i * a j) := by
        rw [hA, dot_mulVec_eq]; push_cast; rfl
      have hBc : (B : ℂ) = ∑ i, ∑ j, (H i j : ℂ) * (a i * b j) := by
        rw [hB, dot_mulVec_eq]; push_cast; rfl
      have hBc' : (B : ℂ) = ∑ i, ∑ j, (H i j : ℂ) * (b i * a j) := by
        rw [← hba, dot_mulVec_eq]; push_cast; rfl
      have hCc : (C : ℂ) = ∑ i, ∑ j, (H i j : ℂ) * (b i * b j) := by
        rw [hC, dot_mulVec_eq]; push_cast; rfl
      rw [hAc, hCc, Complex.ofReal_add]
      nth_rewrite 1 [hBc]
      nth_rewrite 1 [hBc']
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1]
    apply Complex.ext
    · have hA0 : A ≠ 0 := hQa.ne'
      simp only [hs, pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.zero_re]
      field_simp
      nlinarith [hr2]
    · have hA0 : A ≠ 0 := hQa.ne'
      simp only [hs, pow_two, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.zero_im]
      field_simp
      ring

/-- **Quadratic core.**  A real symmetric matrix with nonnegative entries whose quadratic form
`z ↦ ∑ H i j * z i * z j` is real stable has at most one positive eigenvalue. -/
theorem hasAtMostOnePositiveEigenvalue_of_stable {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (hnn : ∀ i j, 0 ≤ H i j) (hst : JumpSystem.Stable (quadPoly H)) :
    HasAtMostOnePositiveEigenvalue H := by
  intro x y hx
  by_contra hlt
  push Not at hlt
  set a : Fin n → ℝ := fun i => |x i| + 1 with ha_def
  have ha : ∀ i, 0 < a i := fun i => by simp only [ha_def]; positivity
  have hxa : x ⬝ᵥ H *ᵥ x ≤ a ⬝ᵥ H *ᵥ a := by
    rw [dot_mulVec_eq, dot_mulVec_eq]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hnn i j)
    have h1 := le_abs_self (x i * x j)
    rw [abs_mul] at h1
    simp only [ha_def]
    nlinarith [abs_nonneg (x i), abs_nonneg (x j)]
  have hQa : 0 < a ⬝ᵥ H *ᵥ a := lt_of_lt_of_le hx hxa
  have hrev := form_le_sq_of_stable hH hst ha hQa
  set c1 : ℝ := a ⬝ᵥ H *ᵥ y with hc1
  set c2 : ℝ := -(a ⬝ᵥ H *ᵥ x) with hc2
  have hyx : y ⬝ᵥ H *ᵥ x = x ⬝ᵥ H *ᵥ y := dot_mulVec_comm hH y x
  have hw : ∃ w : Fin n → ℝ, a ⬝ᵥ H *ᵥ w = 0 ∧ 0 < w ⬝ᵥ H *ᵥ w := by
    by_cases h0 : c1 = 0 ∧ c2 = 0
    · refine ⟨x, ?_, hx⟩
      have := h0.2
      rw [hc2] at this
      linarith
    · refine ⟨c1 • x + c2 • y, ?_, ?_⟩
      · simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hc1,
          hc2]
        ring
      · simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, add_dotProduct,
          smul_dotProduct, smul_eq_mul, hyx]
        set X := x ⬝ᵥ H *ᵥ x
        set Y := y ⬝ᵥ H *ᵥ y
        set Z := x ⬝ᵥ H *ᵥ y
        have hid : X * (c1 * (c1 * X + c2 * Z) + c2 * (c1 * Z + c2 * Y)) =
            (c1 * X + c2 * Z) ^ 2 + c2 ^ 2 * (X * Y - Z ^ 2) := by ring
        have hpos : 0 < X * (c1 * (c1 * X + c2 * Z) + c2 * (c1 * Z + c2 * Y)) := by
          rw [hid]
          by_cases hc : c2 = 0
          · have hc1' : c1 ≠ 0 := fun h => h0 ⟨h, hc⟩
            have : 0 < (c1 * X + c2 * Z) ^ 2 := by
              rw [hc]; simp only [zero_mul, add_zero]; positivity
            have : 0 ≤ c2 ^ 2 * (X * Y - Z ^ 2) := by
              rw [hc]; simp
            linarith
          · have : 0 < c2 ^ 2 * (X * Y - Z ^ 2) := mul_pos (by positivity) (by linarith)
            have := sq_nonneg (c1 * X + c2 * Z)
            linarith
        exact pos_of_mul_pos_right hpos hx.le
  obtain ⟨w, hw0, hwpos⟩ := hw
  have := hrev w
  rw [hw0] at this
  nlinarith [mul_pos hQa hwpos]

/-! ### M-convexity of the support -/

/-- A set `S ⊆ ℕⁿ` is *M-convex* (Brändén–Huh, Section 2.3, exchange property): for all
`α, β ∈ S` and every index `i` with `β i < α i` there is an index `j` with `α j < β j` such that
`α - eᵢ + eⱼ ∈ S`. -/
def IsMConvex (S : Set (Fin n →₀ ℕ)) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, ∀ i, β i < α i →
    ∃ j, α j < β j ∧ α - Finsupp.single i 1 + Finsupp.single j 1 ∈ S

/-- The support of a homogeneous real stable polynomial is M-convex: it is a jump system
(`RealRooted.MvRealStable.isJumpSystem_supportInt`) of constant coordinate sum. -/
theorem isMConvex_support_of_stable {p : MvPolynomial (Fin n) ℝ} (hp : JumpSystem.Stable p)
    {d : ℕ} (hhom : p.IsHomogeneous d) : IsMConvex (p.support : Set (Fin n →₀ ℕ)) := by
  classical
  have hJ := MvRealStable.isJumpSystem_supportInt (p := p) hp
  have hsum : ∀ γ ∈ JumpSystem.supportInt p, ∑ k, γ k = (d : ℤ) := by
    rintro γ ⟨m, hm, hγ⟩
    have hw := hhom (mem_support_iff.mp hm)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)] at hw
    simp only [hγ]
    simp only [Pi.one_apply, smul_eq_mul, mul_one] at hw
    exact_mod_cast hw
  intro α hα β hβ i hi
  have hαJ : (fun k => (α k : ℤ)) ∈ JumpSystem.supportInt p := ⟨α, hα, fun _ => rfl⟩
  have hβJ : (fun k => (β k : ℤ)) ∈ JumpSystem.supportInt p := ⟨β, hβ, fun _ => rfl⟩
  have hstep : JumpSystem.IsStep (fun k => (α k : ℤ)) (fun k => (β k : ℤ)) (Pi.single i (-1)) := by
    refine JumpSystem.isStep_single _ _ i (-1) (Or.inr rfl) ?_
    rw [abs_of_nonneg (by lia), abs_of_pos (by lia)]
    lia
  rcases hJ _ hαJ _ hβJ _ hstep with h | ⟨t, ⟨⟨j, hj⟩, hdist⟩, ht⟩
  · exfalso
    have h1 := hsum _ h
    have h2 := hsum _ hαJ
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single'] at h1
    simp at h1
    lia
  · have hsα := hsum _ hαJ
    have hst := hsum _ ht
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single'] at hst
    have htj : t = Pi.single j 1 := by
      rcases hj with rfl | rfl
      · rfl
      · simp at hst; lia
    subst htj
    rw [JumpSystem.dist1_add_single] at hdist
    simp only [Pi.add_apply] at hdist
    have hjα : α j < β j := by
      by_cases hji : j = i
      · subst hji
        simp only [Pi.single_eq_same] at hdist
        rw [abs_of_nonneg (by lia), abs_of_nonneg (by lia)] at hdist
        lia
      · simp only [Pi.single_eq_of_ne hji, add_zero] at hdist
        by_contra hnot
        rw [abs_of_nonneg (by lia), abs_of_nonneg (by lia)] at hdist
        lia
    obtain ⟨m, hm, hmk⟩ := ht
    refine ⟨j, hjα, ?_⟩
    have hmeq : α - Finsupp.single i 1 + Finsupp.single j 1 = m := by
      ext k
      have := hmk k
      simp only [Pi.add_apply, Pi.single_apply] at this
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      by_cases hki : k = i <;> by_cases hkj : k = j <;> simp only [hki, hkj] at this ⊢ <;> lia
    rw [hmeq]
    exact Finset.mem_coe.mpr hm

/-! ### Iterated partial derivatives and the Hessian -/

/-- The iterated partial derivative `∂^α f = ∂₁^{α₁} ⋯ ∂ₙ^{αₙ} f`. -/
noncomputable def partialDeriv (α : Fin n →₀ ℕ) (f : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  (List.finRange n).foldr (fun i g => (pderiv i)^[α i] g) f

/-- The Hessian matrix `(∂ᵢ ∂ⱼ g)(0)` of a polynomial `g`; for a quadratic form this is the
(constant) Hessian of `g`. -/
noncomputable def hessian (g : MvPolynomial (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => constantCoeff (pderiv i (pderiv j g))

/-- Zero or stable, homogeneous of degree `d`, with nonnegative coefficients. -/
private def Good (d : ℕ) (g : MvPolynomial (Fin n) ℝ) : Prop :=
  (g = 0 ∨ JumpSystem.Stable g) ∧ g.IsHomogeneous d ∧ ∀ m, 0 ≤ g.coeff m

private lemma Good.derivative {d : ℕ} {g : MvPolynomial (Fin n) ℝ} (h : Good d g) (j : Fin n) :
    Good (d - 1) (pderiv j g) := by
  obtain ⟨hs, hh, hc⟩ := h
  refine ⟨?_, MvPolynomial.IsHomogeneous.pderiv hh, fun m => ?_⟩
  · by_cases h0 : pderiv j g = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      rcases hs with rfl | hs
      · simp at h0
      · exact hs.pderiv j h0
  · rw [JumpSystem.coeff_pderiv']
    exact mul_nonneg (hc _) (by positivity)

private lemma Good.iterate {d : ℕ} {g : MvPolynomial (Fin n) ℝ} (h : Good d g) (j : Fin n)
    (k : ℕ) : Good (d - k) ((pderiv j)^[k] g) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := ih.derivative j
    rwa [Nat.sub_sub] at this

private lemma Good.foldr {d : ℕ} {f : MvPolynomial (Fin n) ℝ} (h : Good d f)
    (α : Fin n →₀ ℕ) (l : List (Fin n)) :
    Good (d - (l.map α).sum) (l.foldr (fun i g => (pderiv i)^[α i] g) f) := by
  induction l with
  | nil => simpa using h
  | cons a l ih =>
    have := ih.iterate a (α a)
    rw [Nat.sub_sub] at this
    simpa [add_comm] using this

private lemma Good.partialDeriv {d : ℕ} {f : MvPolynomial (Fin n) ℝ} (h : Good d f)
    (α : Fin n →₀ ℕ) : Good (d - ∑ i, α i) (partialDeriv α f) := by
  rw [Fin.sum_univ_def]
  exact h.foldr α _

private lemma hessian_isSymm (g : MvPolynomial (Fin n) ℝ) : (hessian g).IsSymm := by
  ext i j
  simp only [hessian, Matrix.transpose_apply, constantCoeff_eq, JumpSystem.coeff_pderiv']
  by_cases hij : i = j
  · rw [hij]
  · simp only [Finsupp.single_apply, hij, Ne.symm hij, ite_false, zero_add, Finsupp.coe_zero,
      Pi.zero_apply, mul_one, Nat.cast_zero, add_comm (Finsupp.single j 1)]

private lemma hessian_nonneg {d : ℕ} {g : MvPolynomial (Fin n) ℝ} (h : Good d g) (i j : Fin n) :
    0 ≤ hessian g i j := by
  have := ((h.derivative j).derivative i).2.2 0
  simpa [hessian, constantCoeff_eq] using this

private lemma quadPoly_hessian {g : MvPolynomial (Fin n) ℝ} (hg : g.IsHomogeneous 2) :
    quadPoly (hessian g) = C 2 * g := by
  have e := MvPolynomial.IsHomogeneous.sum_X_mul_pderiv hg
  have e1 : ∀ i, pderiv i g = ∑ j, X j * C (hessian g j i) := by
    intro i
    have h1 := MvPolynomial.IsHomogeneous.sum_X_mul_pderiv
      (MvPolynomial.IsHomogeneous.pderiv (i := i) hg)
    have h2 : ∀ j, pderiv j (pderiv i g) = C (hessian g j i) := by
      intro j
      have h3 : (pderiv j (pderiv i g)).IsHomogeneous 0 :=
        MvPolynomial.IsHomogeneous.pderiv (MvPolynomial.IsHomogeneous.pderiv hg)
      rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h3
      rw [h3]
      rfl
    simp only [h2] at h1
    simpa using h1.symm
  simp only [e1, Finset.mul_sum] at e
  have e2 : C 2 * g = 2 • g := by
    rw [show (C 2 : MvPolynomial (Fin n) ℝ) = 2 from map_ofNat C 2, two_mul, two_smul]
  rw [e2, ← e, quadPoly, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma stable_C_mul {g : MvPolynomial (Fin n) ℝ} (hg : JumpSystem.Stable g) {c : ℝ}
    (hc : c ≠ 0) : JumpSystem.Stable (C c * g) := by
  intro z hz h
  simp only [map_mul, MvPolynomial.map_C, eval_C] at h
  exact (mul_ne_zero (by simpa using hc) (hg z hz)) h

/-! ### Lorentzian polynomials and the stable case -/

/-- A real polynomial `f` in `n` variables is *Lorentzian of degree `d`* if it is homogeneous of
degree `d` with nonnegative coefficients, its support is M-convex, and for every
`α ∈ ℕⁿ` with `|α| = d - 2` the Hessian of the quadratic form `∂^α f` has at most one positive
eigenvalue.

This is the characterization of Brändén–Huh, *Lorentzian polynomials*, Ann. of Math. 192
(2020), Theorem 2.25 and the sentence following it: the closure of the strictly Lorentzian
polynomials (their Definition 2.1) consists exactly of these polynomials.  For `d = 0, 1`
there is no Hessian condition, and the zero polynomial is admitted. -/
def IsLorentzian (d : ℕ) (f : MvPolynomial (Fin n) ℝ) : Prop :=
  f.IsHomogeneous d ∧ (∀ m, 0 ≤ f.coeff m) ∧ IsMConvex (f.support : Set (Fin n →₀ ℕ)) ∧
    ∀ α : Fin n →₀ ℕ, ∑ i, α i + 2 = d →
      HasAtMostOnePositiveEigenvalue (hessian (partialDeriv α f))

/-- **Brändén–Huh, Proposition 2.2.**  A homogeneous real stable polynomial with nonnegative
coefficients is Lorentzian. -/
theorem isLorentzian_of_stable {p : MvPolynomial (Fin n) ℝ} (hp : JumpSystem.Stable p)
    {d : ℕ} (hhom : p.IsHomogeneous d) (hnn : ∀ m, 0 ≤ p.coeff m) : IsLorentzian d p := by
  refine ⟨hhom, hnn, isMConvex_support_of_stable hp hhom, fun α hα => ?_⟩
  have hg := (Good.partialDeriv ⟨Or.inr hp, hhom, hnn⟩ α : Good (d - ∑ i, α i) _)
  have hd : d - ∑ i, α i = 2 := by lia
  rw [hd] at hg
  obtain ⟨hs, hh, hc⟩ := hg
  rcases hs with h0 | hst
  · rw [h0]
    intro x y hx
    have h00 : hessian (0 : MvPolynomial (Fin n) ℝ) = 0 := by
      ext i j
      simp [hessian]
    rw [h00] at hx
    simp at hx
  · refine hasAtMostOnePositiveEigenvalue_of_stable (hessian_isSymm _)
      (hessian_nonneg (show Good 2 (partialDeriv α p) from ?_)) ?_
    · exact ⟨Or.inr hst, hh, hc⟩
    · rw [quadPoly_hessian hh]
      exact stable_C_mul hst (by norm_num)

/-- The condition `HasAtMostOnePositiveEigenvalue` implies that a Hermitian (real symmetric)
matrix has at most one positive eigenvalue, counted with multiplicity. -/
theorem card_positive_eigenvalues_le_one {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian)
    (h : HasAtMostOnePositiveEigenvalue H) :
    (Finset.univ.filter fun i => 0 < hH.eigenvalues i).card ≤ 1 := by
  by_contra hcard
  push Not at hcard
  obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.mp hcard
  rw [Finset.mem_filter] at hk hl
  have hon := orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal
  have hxx : (hH.eigenvectorBasis k).ofLp ⬝ᵥ (hH.eigenvectorBasis k).ofLp = 1 := by
    have h1 := hon k k
    simp only [PiLp.inner_apply, ↓reduceIte] at h1
    simpa [dotProduct, ← sq, mul_comm] using h1
  have hxy : (hH.eigenvectorBasis k).ofLp ⬝ᵥ (hH.eigenvectorBasis l).ofLp = 0 := by
    have h1 := hon k l
    simp only [PiLp.inner_apply, hkl, ↓reduceIte] at h1
    simpa [dotProduct, mul_comm] using h1
  have hyy : (hH.eigenvectorBasis l).ofLp ⬝ᵥ (hH.eigenvectorBasis l).ofLp = 1 := by
    have h1 := hon l l
    simp only [PiLp.inner_apply, ↓reduceIte] at h1
    simpa [dotProduct, ← sq, mul_comm] using h1
  have hmk := hH.mulVec_eigenvectorBasis k
  have hml := hH.mulVec_eigenvectorBasis l
  have hq := h (hH.eigenvectorBasis k).ofLp (hH.eigenvectorBasis l).ofLp
  rw [hmk, hml] at hq
  simp only [dotProduct_smul, smul_eq_mul, hxx, hxy, hyy] at hq
  have hkl' := mul_pos hk.2 hl.2
  rw [mul_one, mul_one, mul_zero] at hq
  nlinarith [hq hk.2]

/-! ### Examples -/

private lemma coeff_nonneg_mul {f g : MvPolynomial (Fin n) ℝ} (hf : ∀ m, 0 ≤ f.coeff m)
    (hg : ∀ m, 0 ≤ g.coeff m) (m : Fin n →₀ ℕ) : 0 ≤ (f * g).coeff m := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hf _) (hg _)

private lemma coeff_nonneg_X_add_X (i j : Fin n) (m : Fin n →₀ ℕ) :
    0 ≤ (X i + X j : MvPolynomial (Fin n) ℝ).coeff m := by
  classical
  have hadd : (X i + X j : MvPolynomial (Fin n) ℝ).coeff m =
      (X i : MvPolynomial (Fin n) ℝ).coeff m + (X j : MvPolynomial (Fin n) ℝ).coeff m := rfl
  rw [hadd]
  have h := coeff_X (R := ℝ) i m
  have h' := coeff_X (R := ℝ) j m
  rw [h, h']
  split_ifs <;> norm_num

/-- The product `(w₀ + w₁)(w₁ + w₂)` of two stable linear forms is a Lorentzian quadratic
polynomial in three variables. -/
example : IsLorentzian 2 ((X 0 + X 1) * (X 1 + X 2) : MvPolynomial (Fin 3) ℝ) := by
  have h1 : MvRealStable (X 0 + X 1 : MvPolynomial (Fin 3) ℝ) := by
    simpa using MvRealStable.C_mul_X_add_C_mul_X (0 : Fin 3) 1 (a := 1) (b := 1)
      zero_le_one zero_le_one (Or.inl one_pos)
  have h2 : MvRealStable (X 1 + X 2 : MvPolynomial (Fin 3) ℝ) := by
    simpa using MvRealStable.C_mul_X_add_C_mul_X (1 : Fin 3) 2 (a := 1) (b := 1)
      zero_le_one zero_le_one (Or.inl one_pos)
  have hh : ((X 0 + X 1) * (X 1 + X 2) : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 := by
    have := ((isHomogeneous_X ℝ (0 : Fin 3)).add (isHomogeneous_X ℝ 1)).mul
      ((isHomogeneous_X ℝ (1 : Fin 3)).add (isHomogeneous_X ℝ 2))
    simpa using this
  exact isLorentzian_of_stable (h1.mul h2) hh
    (coeff_nonneg_mul (coeff_nonneg_X_add_X 0 1) (coeff_nonneg_X_add_X 1 2))

end RealRooted.Lorentzian

namespace RealRooted

/-- Brändén–Huh, Proposition 2.2: a homogeneous real stable polynomial with nonnegative
coefficients is Lorentzian. -/
theorem MvRealStable.isLorentzian {n : ℕ} {p : MvPolynomial (Fin n) ℝ} (hp : MvRealStable p)
    {d : ℕ} (hhom : p.IsHomogeneous d) (hnn : ∀ m, 0 ≤ p.coeff m) :
    Lorentzian.IsLorentzian d p :=
  Lorentzian.isLorentzian_of_stable hp hhom hnn

/-- The support of a homogeneous real stable polynomial is M-convex. -/
theorem MvRealStable.isMConvex_support {n : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : MvRealStable p) {d : ℕ} (hhom : p.IsHomogeneous d) :
    Lorentzian.IsMConvex (p.support : Set (Fin n →₀ ℕ)) :=
  Lorentzian.isMConvex_support_of_stable hp hhom

end RealRooted
