import Mathlib.Analysis.Convex.PathConnected
import RealRooted.BorceaBranden.Applications.HomogenizeStable
import RealRooted.HomogeneousComponentStability
import RealRooted.HomogeneousStability
import RealRooted.Mathlib.Analysis.Normed.Field.Approximation
import RealRooted.Mathlib.RingTheory.MvPolynomial.Hyperbolic

/-!
# Hyperbolicity and multivariate real stability

This file relates Gårding hyperbolicity to multivariate real stability and
proves boundary hyperbolicity of ordinary homogenization.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- The project-local real affine-line restriction is the real specialization
of the generic upstream-shaped definition. -/
theorem realAffineLineRestriction_eq_affineLineRestriction
    {σ : Type*} (x e : σ → ℝ) (P : MvPolynomial σ ℝ) :
    realAffineLineRestriction x e P =
      MvPolynomial.affineLineRestriction x e P := rfl

/-- Evaluating the complexification of a real linear-plane restriction is
the same as evaluating the complexified polynomial on that plane. -/
@[simp] theorem eval_complexifyMv_linearPlaneRestriction
    {σ : Type*} (e u : σ → ℝ) (P : MvPolynomial σ ℝ)
    (z : Fin 2 → ℂ) :
    MvPolynomial.eval z
        (complexifyMv (MvPolynomial.linearPlaneRestriction e u P)) =
      MvPolynomial.eval
        (fun i => (e i : ℂ) * z 0 + (u i : ℂ) * z 1)
        (complexifyMv P) := by
  simp only [complexifyMv, MvPolynomial.eval_map]
  change MvPolynomial.aeval z
      (MvPolynomial.linearPlaneRestriction e u P) =
    MvPolynomial.aeval
      (fun i => (e i : ℂ) * z 0 + (u i : ℂ) * z 1) P
  unfold MvPolynomial.linearPlaneRestriction
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun w : σ → ℂ => MvPolynomial.aeval w P)
  funext i
  simp

/-- Coefficients of an affine-line restriction vary continuously when its
base point varies continuously. -/
theorem continuous_coeff_affineLineRestriction_comp
    {T σ K : Type*} [TopologicalSpace T] [NormedField K]
    (P : MvPolynomial σ K) (a : T → σ → K)
    (ha : ∀ i, Continuous fun t => a t i) (b : σ → K) (k : ℕ) :
    Continuous fun t =>
      (MvPolynomial.affineLineRestriction (a t) b P).coeff k := by
  induction P using MvPolynomial.induction_on generalizing k with
  | C r =>
      simpa [MvPolynomial.affineLineRestriction] using
        (continuous_const : Continuous fun _ : T =>
          (Polynomial.C r).coeff k)
  | add P Q hP hQ =>
      have hP' : Continuous fun t =>
          ((MvPolynomial.eval₂Hom Polynomial.C
            (fun i => Polynomial.C (a t i) +
              Polynomial.C (b i) * Polynomial.X) P)).coeff k := by
        simpa [MvPolynomial.affineLineRestriction] using hP k
      have hQ' : Continuous fun t =>
          ((MvPolynomial.eval₂Hom Polynomial.C
            (fun i => Polynomial.C (a t i) +
              Polynomial.C (b i) * Polynomial.X) Q)).coeff k := by
        simpa [MvPolynomial.affineLineRestriction] using hQ k
      change Continuous fun t =>
        ((MvPolynomial.eval₂Hom Polynomial.C
          (fun i => Polynomial.C (a t i) +
            Polynomial.C (b i) * Polynomial.X) (P + Q))).coeff k
      simp_rw [map_add, coeff_add]
      fun_prop
  | mul_X P i hP =>
      have hP' (j : ℕ) : Continuous fun t =>
          ((MvPolynomial.eval₂Hom Polynomial.C
            (fun i => Polynomial.C (a t i) +
              Polynomial.C (b i) * Polynomial.X) P)).coeff j := by
        simpa [MvPolynomial.affineLineRestriction] using hP j
      change Continuous fun t =>
        ((MvPolynomial.eval₂Hom Polynomial.C
          (fun j => Polynomial.C (a t j) +
            Polynomial.C (b j) * Polynomial.X)
          (P * MvPolynomial.X i))).coeff k
      simp_rw [map_mul, MvPolynomial.eval₂Hom_X',
        Polynomial.coeff_mul, coeff_add, coeff_C, coeff_C_mul_X]
      apply continuous_finsetSum
      intro x hx
      by_cases hx0 : x.2 = 0
      · simp only [hx0, if_pos, Nat.zero_ne_one, if_false, add_zero]
        exact (hP' x.1).mul (ha i)
      · by_cases hx1 : x.2 = 1
        · simp only [hx1, Nat.one_ne_zero, if_false, if_pos, zero_add]
          exact (hP' x.1).mul continuous_const
        · simp only [hx0, hx1, if_false, zero_add, mul_zero]
          exact continuous_const

/-- Restricting a homogeneous polynomial to a line through zero produces a
monomial whose coefficient is its value at the direction vector. -/
theorem MvPolynomial.IsHomogeneous.affineLineRestriction_zero
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d) (e : σ → ℝ) :
    MvPolynomial.affineLineRestriction (fun _ => 0) e P =
      Polynomial.C (MvPolynomial.eval e P) * Polynomial.X ^ d := by
  apply Polynomial.funext
  intro t
  rw [MvPolynomial.eval_affineLineRestriction]
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  simpa [mul_comm] using hP.eval_smul t e

/-- The linear-plane restriction of a homogeneous polynomial is the
bivariate homogenization of its affine-line restriction through `u` in
direction `e`. -/
theorem MvPolynomial.IsHomogeneous.linearPlaneRestriction_eq_homogenize
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d) (e u : σ → ℝ) :
    MvPolynomial.linearPlaneRestriction e u P =
      homogenizeBivariate d
        (MvPolynomial.affineLineRestriction u e P) := by
  have hplane :
      (MvPolynomial.linearPlaneRestriction e u P).IsHomogeneous d := by
    unfold MvPolynomial.linearPlaneRestriction
    simpa using hP.aeval
      (fun i => MvPolynomial.C (e i) * MvPolynomial.X 0 +
        MvPolynomial.C (u i) * MvPolynomial.X 1)
      (fun i => (MvPolynomial.isHomogeneous_C_mul_X (e i) 0).add
        (MvPolynomial.isHomogeneous_C_mul_X (u i) 1))
  apply Eq.symm
  rw [BorceaBranden.homogenizeBivariate_eq_homogenize]
  apply Polynomial.homogenize_eq_of_isHomogeneous hplane
  unfold MvPolynomial.linearPlaneRestriction
  change MvPolynomial.aeval ![Polynomial.X, 1]
      (MvPolynomial.aeval
        (fun i => MvPolynomial.C (e i) * MvPolynomial.X 0 +
          MvPolynomial.C (u i) * MvPolynomial.X 1) P) = _
  rw [MvPolynomial.comp_aeval_apply]
  unfold MvPolynomial.affineLineRestriction
  apply MvPolynomial.eval₂Hom_congr rfl
  · funext i
    simp
    ring
  · rfl

/-- For a homogeneous polynomial, hyperbolicity gives split and nonzero
affine-line restrictions in the hyperbolic direction. -/
theorem MvPolynomial.HyperbolicAt.affineLineRestriction_splits_ne_zero
    {σ : Type*} {P : MvPolynomial σ ℝ} {e : σ → ℝ}
    (hP : P.HyperbolicAt e) {d : ℕ} (hhom : P.IsHomogeneous d)
    (x : σ → ℝ) :
    (MvPolynomial.affineLineRestriction x e P).Splits ∧
      MvPolynomial.affineLineRestriction x e P ≠ 0 := by
  refine ⟨hP.2 x, ?_⟩
  intro hzero
  have hcoeff :=
    MvPolynomial.IsHomogeneous.coeff_realAffineLineRestriction hhom x e
  apply hP.1
  rw [realAffineLineRestriction_eq_affineLineRestriction, hzero] at hcoeff
  simpa using hcoeff.symm

/-- If every root of the affine restriction from `u` in direction `e` is
strictly negative, then the multivariate polynomial does not vanish at `u`. -/
theorem MvPolynomial.eval_ne_zero_of_affineLineRestriction_isRoot_neg
    {σ : Type*} {P : MvPolynomial σ ℝ} {u e : σ → ℝ}
    (hneg : ∀ r, (MvPolynomial.affineLineRestriction u e P).IsRoot r → r < 0) :
    MvPolynomial.eval u P ≠ 0 := by
  intro hu
  have hroot : (MvPolynomial.affineLineRestriction u e P).IsRoot 0 := by
    rw [Polynomial.IsRoot, MvPolynomial.eval_affineLineRestriction]
    simpa using hu
  exact (lt_irrefl 0) (hneg 0 hroot)

/-- Along a path in the nonvanishing locus from a hyperbolic direction, the
roots of the affine restriction in that direction stay strictly negative. -/
theorem MvPolynomial.HyperbolicAt.affineLineRestriction_isRoot_neg_of_joinedIn
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ} {e u : σ → ℝ}
    (he : P.HyperbolicAt e) (hhom : P.IsHomogeneous d) (hd : d ≠ 0)
    (hjoin : JoinedIn {x | MvPolynomial.eval x P ≠ 0} e u) :
    ∀ r, (MvPolynomial.affineLineRestriction u e P).IsRoot r → r < 0 := by
  let γ : Path e u := hjoin.somePath
  let c : ℝ := (MvPolynomial.eval e P)⁻¹
  let q : unitInterval → ℝ[X] := fun t => Polynomial.C c *
    MvPolynomial.affineLineRestriction (γ t) e P
  have hrestrictionDegree (t : unitInterval) :
      (MvPolynomial.affineLineRestriction (γ t) e P).natDegree = d := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · simpa [← realAffineLineRestriction_eq_affineLineRestriction] using
        MvPolynomial.IsHomogeneous.natDegree_realAffineLineRestriction_le
          hhom (γ t) e
    · simpa [← realAffineLineRestriction_eq_affineLineRestriction] using
        (MvPolynomial.IsHomogeneous.coeff_realAffineLineRestriction
          hhom (γ t) e).trans_ne he.1
  have hdegree (t : unitInterval) : (q t).natDegree = d := by
    rw [show q t = Polynomial.C c *
      MvPolynomial.affineLineRestriction (γ t) e P by rfl,
      Polynomial.natDegree_C_mul (inv_ne_zero he.1),
      hrestrictionDegree]
  have hmonic (t : unitInterval) : (q t).Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [Polynomial.leadingCoeff, hrestrictionDegree]
    simp only [c]
    rw [show (MvPolynomial.affineLineRestriction (γ t) e P).coeff d =
        MvPolynomial.eval e P by
      simpa [← realAffineLineRestriction_eq_affineLineRestriction] using
        MvPolynomial.IsHomogeneous.coeff_realAffineLineRestriction
          hhom (γ t) e]
    exact inv_mul_cancel₀ he.1
  have hsplits (t : unitInterval) : (q t).Splits := by
    exact (he.2 (γ t)).C_mul c
  have hcoeff (k : ℕ) : Continuous fun t => (q t).coeff k := by
    have hγi (i : σ) : Continuous fun t => γ t i :=
      (continuous_apply i).comp γ.continuous
    have hrestriction := continuous_coeff_affineLineRestriction_comp
      P γ hγi e k
    simpa [q, c, Polynomial.coeff_C_mul] using
      hrestriction.const_mul c
  have hcover (t : unitInterval) (r : ℝ) (hr : (q t).IsRoot r) :
      r ∈ Set.Iio 0 ∪ Set.Ioi 0 := by
    have hqzero : (q t).eval 0 ≠ 0 := by
      have hpath : MvPolynomial.eval (γ t) P ≠ 0 := hjoin.somePath_mem t
      dsimp only [q]
      rw [Polynomial.eval_mul, Polynomial.eval_C,
        MvPolynomial.eval_affineLineRestriction]
      simpa [c] using mul_ne_zero (inv_ne_zero he.1) hpath
    have hr0 : r ≠ 0 := by
      intro hrzero
      subst r
      exact hqzero hr
    exact lt_or_gt_of_ne hr0
  have hstart : ∀ r, (q (0 : unitInterval)).IsRoot r → r ∈ Set.Iio 0 := by
    intro r hr
    have hγ0 : γ (0 : unitInterval) = e := γ.source'
    have hrpow : (1 + r) ^ d = 0 := by
      have hreval :
          MvPolynomial.eval (fun i => e i + e i * r) P = 0 := by
        simpa [q, c, hγ0, Polynomial.IsRoot, he.1] using hr
      have hvec : (fun i => e i + e i * r) = fun i => (1 + r) * e i := by
        funext i
        ring
      rw [hvec, hhom.eval_smul] at hreval
      exact (mul_eq_zero.mp hreval).resolve_right he.1
    have hrneg : r = -1 := by
      have : 1 + r = 0 := (pow_eq_zero_iff hd).mp hrpow
      linarith
    rw [hrneg]
    norm_num
  have htransport : ∀ r, (q (1 : unitInterval)).IsRoot r → r ∈ Set.Iio 0 := by
    apply Polynomial.forall_isRoot_mem_of_isPreconnected
      q hmonic hdegree hd hcoeff hsplits isOpen_Iio isOpen_Ioi
    · exact Set.disjoint_left.mpr (by
        intro r hrneg hrpos
        change r < 0 at hrneg
        change 0 < r at hrpos
        exact (not_lt_of_ge hrpos.le) hrneg)
    · exact hcover
    · exact isPreconnected_univ
    · exact Set.mem_univ (0 : unitInterval)
    · exact Set.mem_univ (1 : unitInterval)
    · exact hstart
  intro r hr
  apply htransport r
  have hγ1 : γ (1 : unitInterval) = u := γ.target'
  dsimp only [q]
  rw [hγ1, Polynomial.IsRoot, Polynomial.eval_mul,
    Polynomial.eval_C, hr, mul_zero]

/-- If the roots seen from one hyperbolic direction are nonpositive, then the
homogeneous restriction to that direction and the base vector is bivariate
real stable. -/
theorem MvPolynomial.HyperbolicAt.linearPlaneRestriction_mvRealStable
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ} {e u : σ → ℝ}
    (he : P.HyperbolicAt e) (hhom : P.IsHomogeneous d)
    (hroots : ∀ r ∈ (MvPolynomial.affineLineRestriction u e P).roots,
      r ≤ 0) :
    MvRealStable (MvPolynomial.linearPlaneRestriction e u P) := by
  let q := MvPolynomial.affineLineRestriction u e P
  have hq0 : q ≠ 0 :=
    (MvPolynomial.HyperbolicAt.affineLineRestriction_splits_ne_zero
      he hhom u).2
  have hqle : q.natDegree ≤ d := by
    simpa [q, realAffineLineRestriction_eq_affineLineRestriction] using
      MvPolynomial.IsHomogeneous.natDegree_realAffineLineRestriction_le
        hhom u e
  have hqcoeff : q.coeff d = MvPolynomial.eval e P := by
    simpa [q, realAffineLineRestriction_eq_affineLineRestriction] using
      MvPolynomial.IsHomogeneous.coeff_realAffineLineRestriction hhom u e
  have hqd : q.natDegree = d :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hqle
      (hqcoeff.trans_ne he.1)
  rw [MvPolynomial.IsHomogeneous.linearPlaneRestriction_eq_homogenize
    hhom e u, ← hqd]
  exact BorceaBranden.homogenizeBivariate_stable_of_splits_nonpos
    hq0 (he.2 u) hroots

/-- If the affine restriction from `u` in the hyperbolic direction `e` has
strictly negative roots, then shifting any real base point a positive
imaginary distance in direction `e` makes every root in direction `u` lie in
the open lower half-plane. -/
theorem MvPolynomial.HyperbolicAt.complex_affineLineRestriction_isRoot_im_neg
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ} {e u x : σ → ℝ}
    (he : P.HyperbolicAt e) (hhom : P.IsHomogeneous d) (hd : d ≠ 0)
    (hneg : ∀ r,
      (MvPolynomial.affineLineRestriction u e P).IsRoot r → r < 0)
    {α : ℝ} (hα : 0 < α) :
    ∀ z,
      (MvPolynomial.affineLineRestriction
        (fun i => Complex.I * (α : ℂ) * (e i : ℂ) + (x i : ℂ))
        (fun i => (u i : ℂ)) (complexifyMv P)).IsRoot z →
      z.im < 0 := by
  have hu : MvPolynomial.eval u P ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_affineLineRestriction_isRoot_neg hneg
  let eC : σ → ℂ := fun i => (e i : ℂ)
  let uC : σ → ℂ := fun i => (u i : ℂ)
  let c : ℂ := (MvPolynomial.eval u P : ℂ)⁻¹
  let a : ℝ → σ → ℂ := fun γ i =>
    Complex.I * (α : ℂ) * eC i + (γ : ℂ) * (x i : ℂ)
  let q : ℝ → ℂ[X] := fun γ => Polynomial.C c *
    MvPolynomial.affineLineRestriction (a γ) uC (complexifyMv P)
  have hhomC : (complexifyMv P).IsHomogeneous d :=
    hhom.map Complex.ofRealHom
  have hueval : MvPolynomial.eval uC (complexifyMv P) =
      (MvPolynomial.eval u P : ℂ) := by
    unfold uC complexifyMv
    change MvPolynomial.eval (Complex.ofRealHom ∘ u)
      (MvPolynomial.map Complex.ofRealHom P) =
        Complex.ofRealHom (MvPolynomial.eval u P)
    exact (MvPolynomial.map_eval Complex.ofRealHom u P).symm
  have hueval0 : MvPolynomial.eval uC (complexifyMv P) ≠ 0 := by
    rw [hueval]
    exact Complex.ofReal_ne_zero.mpr hu
  have hrestrictionDegree (γ : ℝ) :
      (MvPolynomial.affineLineRestriction
        (a γ) uC (complexifyMv P)).natDegree = d :=
    hhomC.natDegree_affineLineRestriction_eq (a γ) uC hueval0
  have hdegree (γ : ℝ) : (q γ).natDegree = d := by
    rw [show q γ = Polynomial.C c *
      MvPolynomial.affineLineRestriction (a γ) uC (complexifyMv P) by rfl,
      Polynomial.natDegree_C_mul (inv_ne_zero (Complex.ofReal_ne_zero.mpr hu)),
      hrestrictionDegree]
  have hmonic (γ : ℝ) : (q γ).Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [Polynomial.leadingCoeff, hrestrictionDegree,
      hhomC.coeff_affineLineRestriction, hueval]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hu)
  have hcoeff (k : ℕ) : Continuous fun γ => (q γ).coeff k := by
    have ha (i : σ) : Continuous fun γ : ℝ => a γ i := by
      dsimp only [a, eC]
      fun_prop
    have hrestriction := continuous_coeff_affineLineRestriction_comp
      (complexifyMv P) a ha uC k
    simpa [q, c, Polynomial.coeff_C_mul] using hrestriction.const_mul c
  have havoid (γ : ℝ) (z : ℂ) (hz : (q γ).IsRoot z) : z.im ≠ 0 := by
    intro hzim
    have hbaseeval : MvPolynomial.eval
        (fun i => a γ i + uC i * z) (complexifyMv P) = 0 := by
      rw [Polynomial.IsRoot] at hz
      dsimp only [q] at hz
      rw [Polynomial.eval_mul, Polynomial.eval_C,
        MvPolynomial.eval_affineLineRestriction] at hz
      exact (mul_eq_zero.mp hz).resolve_left
        (inv_ne_zero (Complex.ofReal_ne_zero.mpr hu))
    let y : σ → ℝ := fun i => γ * x i + z.re * u i
    have hreval : (realAffineLineRestriction y e P).aeval
        (Complex.I * (α : ℂ)) = 0 := by
      rw [aeval_realAffineLineRestriction]
      convert hbaseeval using 1
      apply congrArg (fun w : σ → ℂ =>
        MvPolynomial.eval w (complexifyMv P))
      funext i
      dsimp only [a, eC, uC, y]
      apply Complex.ext
      · simp [hzim]
        ring
      · simp [hzim]
        ring
    have hy :=
      MvPolynomial.HyperbolicAt.affineLineRestriction_splits_ne_zero
        he hhom y
    have him := im_eq_zero_of_aeval_eq_zero hy.2 hy.1 hreval
    exact hα.ne' (by simpa using him)
  have hplane : MvRealStable
      (MvPolynomial.linearPlaneRestriction e u P) := by
    apply MvPolynomial.HyperbolicAt.linearPlaneRestriction_mvRealStable
      he hhom
    intro r hr
    exact (hneg r ((Polynomial.mem_roots
      (MvPolynomial.HyperbolicAt.affineLineRestriction_splits_ne_zero
        he hhom u).2).mp hr)).le
  have hstart : ∀ z, (q 0).IsRoot z → z.im < 0 := by
    intro z hz
    rcases lt_or_gt_of_ne (havoid 0 z hz) with hzneg | hzpos
    · exact hzneg
    · have hstable : MvPolynomial.eval
          ![Complex.I * (α : ℂ), z]
          (complexifyMv (MvPolynomial.linearPlaneRestriction e u P)) ≠ 0 := by
        apply hplane
        intro i
        fin_cases i
        · simpa using hα
        · simpa using hzpos
      exfalso
      apply hstable
      rw [eval_complexifyMv_linearPlaneRestriction]
      have hbaseeval : MvPolynomial.eval
          (fun i => a 0 i + uC i * z) (complexifyMv P) = 0 := by
        rw [Polynomial.IsRoot] at hz
        dsimp only [q] at hz
        rw [Polynomial.eval_mul, Polynomial.eval_C,
          MvPolynomial.eval_affineLineRestriction] at hz
        exact (mul_eq_zero.mp hz).resolve_left
          (inv_ne_zero (Complex.ofReal_ne_zero.mpr hu))
      convert hbaseeval using 1
      apply congrArg (fun w : σ → ℂ =>
        MvPolynomial.eval w (complexifyMv P))
      funext i
      dsimp only [a, eC, uC, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp [mul_comm]
  have htransport : ∀ z, (q 1).IsRoot z → z.im < 0 := by
    apply Polynomial.forall_isRoot_im_neg_of_isPreconnected
      (s := Set.Icc (0 : ℝ) 1) (a := 0) (b := 1)
        q hmonic hdegree hd hcoeff havoid
        (convex_Icc (0 : ℝ) 1).isPreconnected
    · simp
    · simp
    · exact hstart
  intro z hz
  apply htransport z
  rw [Polynomial.IsRoot]
  dsimp only [q]
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    MvPolynomial.eval_affineLineRestriction]
  apply mul_eq_zero_of_right
  rw [Polynomial.IsRoot, MvPolynomial.eval_affineLineRestriction] at hz
  convert hz using 1
  apply congrArg (fun w : σ → ℂ =>
    MvPolynomial.eval w (complexifyMv P))
  funext i
  dsimp only [a, eC, uC]
  norm_num

/-- Hyperbolicity transports from `e` to `u` when the affine restriction from
`u` in direction `e` has strictly negative roots. -/
theorem MvPolynomial.HyperbolicAt.of_affineLineRestriction_isRoot_neg
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ} {e u : σ → ℝ}
    (he : P.HyperbolicAt e) (hhom : P.IsHomogeneous d) (hd : d ≠ 0)
    (hneg : ∀ r,
      (MvPolynomial.affineLineRestriction u e P).IsRoot r → r < 0) :
    P.HyperbolicAt u := by
  have hu : MvPolynomial.eval u P ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_affineLineRestriction_isRoot_neg hneg
  refine ⟨hu, ?_⟩
  intro x
  apply splits_of_forall_aeval_im_eq_zero
  intro z hz
  let eC : σ → ℂ := fun i => (e i : ℂ)
  let uC : σ → ℂ := fun i => (u i : ℂ)
  let c : ℂ := (MvPolynomial.eval u P : ℂ)⁻¹
  let a : ℝ → σ → ℂ := fun α i =>
    Complex.I * (α : ℂ) * eC i + (x i : ℂ)
  let q : ℝ → ℂ[X] := fun α => Polynomial.C c *
    MvPolynomial.affineLineRestriction (a α) uC (complexifyMv P)
  have hhomC : (complexifyMv P).IsHomogeneous d :=
    hhom.map Complex.ofRealHom
  have hueval : MvPolynomial.eval uC (complexifyMv P) =
      (MvPolynomial.eval u P : ℂ) := by
    unfold uC complexifyMv
    change MvPolynomial.eval (Complex.ofRealHom ∘ u)
      (MvPolynomial.map Complex.ofRealHom P) =
        Complex.ofRealHom (MvPolynomial.eval u P)
    exact (MvPolynomial.map_eval Complex.ofRealHom u P).symm
  have hueval0 : MvPolynomial.eval uC (complexifyMv P) ≠ 0 := by
    rw [hueval]
    exact Complex.ofReal_ne_zero.mpr hu
  have hrestrictionDegree (α : ℝ) :
      (MvPolynomial.affineLineRestriction
        (a α) uC (complexifyMv P)).natDegree = d :=
    hhomC.natDegree_affineLineRestriction_eq (a α) uC hueval0
  have hdegree (α : ℝ) : (q α).natDegree = d := by
    rw [show q α = Polynomial.C c *
      MvPolynomial.affineLineRestriction (a α) uC (complexifyMv P) by rfl,
      Polynomial.natDegree_C_mul (inv_ne_zero (Complex.ofReal_ne_zero.mpr hu)),
      hrestrictionDegree]
  have hmonic (α : ℝ) : (q α).Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [Polynomial.leadingCoeff, hrestrictionDegree,
      hhomC.coeff_affineLineRestriction, hueval]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hu)
  have hcoeff (k : ℕ) : Continuous fun α => (q α).coeff k := by
    have ha (i : σ) : Continuous fun α : ℝ => a α i := by
      dsimp only [a, eC]
      fun_prop
    have hrestriction := continuous_coeff_affineLineRestriction_comp
      (complexifyMv P) a ha uC k
    simpa [q, c, Polynomial.coeff_C_mul] using hrestriction.const_mul c
  have hnoUpper (w : ℂ)
      (hw : (MvPolynomial.affineLineRestriction x u P).aeval w = 0)
      (hwpos : 0 < w.im) : False := by
    have hwq : (q 0).IsRoot w := by
      rw [Polynomial.IsRoot]
      dsimp only [q]
      rw [Polynomial.eval_mul, Polynomial.eval_C,
        MvPolynomial.eval_affineLineRestriction]
      apply mul_eq_zero_of_right
      have hweval : MvPolynomial.eval
          (fun i => (x i : ℂ) + (u i : ℂ) * w) (complexifyMv P) = 0 := by
        have hw' : (realAffineLineRestriction x u P).aeval w = 0 := by
          simpa [realAffineLineRestriction_eq_affineLineRestriction] using hw
        rwa [aeval_realAffineLineRestriction] at hw'
      simpa [a, eC, uC] using hweval
    obtain ⟨δ, hδ, hpersist⟩ :=
      Polynomial.exists_coeff_radius_root_near (hmonic 0)
        (by simpa [hdegree 0] using hd) hwq hwpos
    have hcloseNhds : ∀ᶠ α in nhds (0 : ℝ),
        ∀ i : ℕ, ‖(q α).coeff i - (q 0).coeff i‖ < δ :=
      Polynomial.eventually_forall_norm_coeff_sub_lt
        q hdegree hcoeff 0 hδ
    have hcloseTop : ∀ᶠ n : ℕ in Filter.atTop,
        ∀ i : ℕ,
          ‖(q (1 / ((n : ℝ) + 1))).coeff i - (q 0).coeff i‖ < δ :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually hcloseNhds
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hcloseTop
    let α : ℝ := 1 / ((N : ℝ) + 1)
    have hα : 0 < α := by
      dsimp only [α]
      positivity
    have hclose : ∀ i : ℕ,
        ‖(q α).coeff i - (q 0).coeff i‖ < δ := by
      exact hN N le_rfl
    obtain ⟨v, hv, hwv⟩ := hpersist (q α) (hmonic α)
      (by rw [hdegree α, hdegree 0]) hclose (IsAlgClosed.splits (q α))
    have hvraw : (MvPolynomial.affineLineRestriction
        (fun i => Complex.I * (α : ℂ) * (e i : ℂ) + (x i : ℂ))
        (fun i => (u i : ℂ)) (complexifyMv P)).IsRoot v := by
      rw [Polynomial.IsRoot] at hv ⊢
      dsimp only [q] at hv
      rw [Polynomial.eval_mul, Polynomial.eval_C] at hv
      exact (mul_eq_zero.mp hv).resolve_left
        (inv_ne_zero (Complex.ofReal_ne_zero.mpr hu))
    have hvneg :=
      MvPolynomial.HyperbolicAt.complex_affineLineRestriction_isRoot_im_neg
        he hhom hd hneg hα v hvraw
    have himle : |w.im - v.im| ≤ ‖w - v‖ := by
      have := Complex.abs_im_le_norm (w - v)
      simpa [Complex.sub_im] using this
    have hvpos : 0 < v.im := by
      have : w.im - v.im < w.im :=
        lt_of_le_of_lt (le_trans (le_abs_self (w.im - v.im)) himle) hwv
      linarith
    exact (not_lt_of_ge hvpos.le) hvneg
  by_cases hzim : z.im = 0
  · exact hzim
  rcases lt_or_gt_of_ne hzim with hzneg | hzpos
  · have hzconj : (MvPolynomial.affineLineRestriction x u P).aeval
        (starRingEnd ℂ z) = 0 := by
      rw [Polynomial.aeval_conj, hz, map_zero]
    have hzconjpos : 0 < (starRingEnd ℂ z).im := by
      simp
      linarith
    exact (hnoUpper (starRingEnd ℂ z) hzconj hzconjpos).elim
  · exact (hnoUpper z hz hzpos).elim

/-- Directions joined inside the nonvanishing locus to a positive-degree
hyperbolic direction span a bivariate real-stable restriction with it. -/
theorem MvPolynomial.HyperbolicAt.linearPlaneRestriction_mvRealStable_of_joinedIn
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ} {e u : σ → ℝ}
    (he : P.HyperbolicAt e) (hhom : P.IsHomogeneous d) (hd : d ≠ 0)
    (hjoin : JoinedIn {x | MvPolynomial.eval x P ≠ 0} e u) :
    MvRealStable (MvPolynomial.linearPlaneRestriction e u P) := by
  apply MvPolynomial.HyperbolicAt.linearPlaneRestriction_mvRealStable
    he hhom
  intro r hr
  apply (MvPolynomial.HyperbolicAt.affineLineRestriction_isRoot_neg_of_joinedIn
    he hhom hd hjoin r ?_).le
  exact (Polynomial.mem_roots
    (MvPolynomial.HyperbolicAt.affineLineRestriction_splits_ne_zero
      he hhom u).2).mp hr

/-- Hyperbolicity is constant on a path component of the nonvanishing locus
of a homogeneous polynomial. -/
theorem MvPolynomial.HyperbolicAt.of_joinedIn
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ} {e u : σ → ℝ}
    (he : P.HyperbolicAt e) (hhom : P.IsHomogeneous d)
    (hjoin : JoinedIn {x | MvPolynomial.eval x P ≠ 0} e u) :
    P.HyperbolicAt u := by
  by_cases hd : d = 0
  · subst d
    have hP0 : P ≠ 0 := by
      intro hzero
      apply he.1
      simp [hzero]
    have hconst : P = MvPolynomial.C (P.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (hhom.totalDegree hP0)
    rw [hconst] at he ⊢
    simpa [MvPolynomial.HyperbolicAt,
      MvPolynomial.affineLineRestriction] using he
  · apply MvPolynomial.HyperbolicAt.of_affineLineRestriction_isRoot_neg
      he hhom hd
    exact MvPolynomial.HyperbolicAt.affineLineRestriction_isRoot_neg_of_joinedIn
      he hhom hd hjoin

/-- A homogeneous real stable polynomial is hyperbolic in every strictly
positive direction. -/
theorem MvRealStable.hyperbolicAt_of_pos
    {σ : Type*} {P : MvPolynomial σ ℝ} (hst : MvRealStable P)
    {d : ℕ} (hhom : P.IsHomogeneous d) {e : σ → ℝ}
    (he : ∀ i, 0 < e i) :
    P.HyperbolicAt e := by
  have hline := hst.realAffineLineRestriction_splits_ne_zero
    (fun _ => 0) e he
  refine ⟨?_, fun x => ?_⟩
  · intro heval
    apply hline.2
    rw [realAffineLineRestriction_eq_affineLineRestriction,
      MvPolynomial.IsHomogeneous.affineLineRestriction_zero hhom e, heval]
    simp
  · simpa [← realAffineLineRestriction_eq_affineLineRestriction] using
      (hst.realAffineLineRestriction_splits_ne_zero x e he).1

/-- If a homogeneous polynomial is hyperbolic in every strictly positive
direction, then it is multivariate real stable. -/
theorem mvRealStable_of_forall_hyperbolicAt_pos
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ}
    (hhom : P.IsHomogeneous d)
    (hP : ∀ e : σ → ℝ, (∀ i, 0 < e i) → P.HyperbolicAt e) :
    MvRealStable P := by
  apply mvRealStable_of_forall_realAffineLineRestriction
  intro a b hb
  have hh := hP b hb
  simpa [realAffineLineRestriction_eq_affineLineRestriction] using
    MvPolynomial.HyperbolicAt.affineLineRestriction_splits_ne_zero
      hh hhom a

/-- A homogeneous polynomial is real stable exactly when it is hyperbolic in
every strictly positive direction. -/
theorem MvPolynomial.IsHomogeneous.mvRealStable_iff_forall_hyperbolicAt_pos
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ}
    (hhom : P.IsHomogeneous d) :
    MvRealStable P ↔
      ∀ e : σ → ℝ, (∀ i, 0 < e i) → P.HyperbolicAt e := by
  exact ⟨fun hst e he => hst.hyperbolicAt_of_pos hhom he,
    mvRealStable_of_forall_hyperbolicAt_pos hhom⟩

private theorem restriction_ordinaryHomogenization_eq_of_none_ne_zero
    {σ : Type*} (P : MvPolynomial σ ℝ) (x : Option σ → ℝ)
    (b : σ → ℝ) (hx : x none ≠ 0) :
    realAffineLineRestriction x (fun o => Option.elim o 0 b)
        (MvPolynomial.ordinaryHomogenization P P.totalDegree) =
      Polynomial.C ((x none) ^ P.totalDegree) *
        realAffineLineRestriction (fun i => x (some i) / x none)
          (fun i => b i / x none) P := by
  apply Polynomial.funext
  intro t
  rw [eval_realAffineLineRestriction, Polynomial.eval_mul,
    Polynomial.eval_C, eval_realAffineLineRestriction]
  have hvec :
      (fun o => x o + Option.elim o 0 b * t) =
        fun o => Option.elim o (x none)
          (fun i => x (some i) + b i * t) := by
    funext o
    cases o <;> simp
  rw [hvec,
    MvPolynomial.eval_ordinaryHomogenization_eq_pow_mul_eval_div
      P le_rfl hx]
  congr 1
  apply congrArg (fun z => MvPolynomial.eval z P)
  funext i
  field_simp

private theorem restriction_ordinaryHomogenization_eq_of_none_eq_zero
    {σ : Type*} (P : MvPolynomial σ ℝ) (x : Option σ → ℝ)
    (b : σ → ℝ) (hx : x none = 0) :
    realAffineLineRestriction x (fun o => Option.elim o 0 b)
        (MvPolynomial.ordinaryHomogenization P P.totalDegree) =
      realAffineLineRestriction (fun i => x (some i)) b
        (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  apply Polynomial.funext
  intro t
  rw [eval_realAffineLineRestriction, eval_realAffineLineRestriction]
  have hvec :
      (fun o => x o + Option.elim o 0 b * t) =
        fun o => Option.elim o 0 (fun i => x (some i) + b i * t) := by
    funext o
    cases o <;> simp [hx]
  rw [hvec, MvPolynomial.eval_ordinaryHomogenization_zero]

private theorem realAffineLineRestriction_neg_direction
    {σ : Type*} (P : MvPolynomial σ ℝ) (a b : σ → ℝ) :
    realAffineLineRestriction a (fun i => -b i) P =
      (realAffineLineRestriction a b P).comp (-Polynomial.X) := by
  apply Polynomial.funext
  intro t
  simp [eval_realAffineLineRestriction, Polynomial.eval_comp]

/-- Ordinary homogenization is hyperbolic in every direction that is positive
on the original coordinates and zero on the homogenizing coordinate. This is
the boundary-direction part of the stability--hyperbolicity bridge. -/
theorem MvRealStable.ordinaryHomogenization_hyperbolicAt_boundary
    {σ : Type*} {P : MvPolynomial σ ℝ} (hst : MvRealStable P)
    (hnn : MvPolynomial.HasNonnegCoeffs P) (hP : P ≠ 0)
    (b : σ → ℝ) (hb : ∀ i, 0 < b i) :
    (MvPolynomial.ordinaryHomogenization P P.totalDegree).HyperbolicAt
      (fun o => Option.elim o 0 b) := by
  let H := MvPolynomial.ordinaryHomogenization P P.totalDegree
  let e : Option σ → ℝ := fun o => Option.elim o 0 b
  let Htop := MvPolynomial.homogeneousComponent P.totalDegree P
  have hHtopNe : Htop ≠ 0 := by
    exact MvPolynomial.homogeneousComponent_totalDegree_ne_zero hP
  have hHtopNN : MvPolynomial.HasNonnegCoeffs Htop := by
    exact hnn.homogeneousComponent P.totalDegree
  have hEvalTopPos : 0 < MvPolynomial.eval b Htop :=
    hHtopNN.eval_pos hHtopNe hb
  have hEval : MvPolynomial.eval e H = MvPolynomial.eval b Htop := by
    simpa [e, H, Htop] using
      MvPolynomial.eval_ordinaryHomogenization_zero P P.totalDegree b
  refine ⟨hEval.trans_ne hEvalTopPos.ne', ?_⟩
  intro x
  change (realAffineLineRestriction x e H).Splits
  by_cases hx : x none = 0
  · rw [restriction_ordinaryHomogenization_eq_of_none_eq_zero P x b hx]
    exact (MvRealStable.realAffineLineRestriction_splits_ne_zero
      (MvRealStable.homogeneousComponent_totalDegree hst hnn hP)
        (fun i => x (some i)) b hb).1
  · rw [restriction_ordinaryHomogenization_eq_of_none_ne_zero P x b hx]
    rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · let a : σ → ℝ := fun i => x (some i) / x none
      let c : σ → ℝ := fun i => -(b i / x none)
      have hc : ∀ i, 0 < c i := by
        intro i
        exact neg_pos.mpr (div_neg_of_pos_of_neg (hb i) hxneg)
      have hsplits :=
        (hst.realAffineLineRestriction_splits_ne_zero a c hc).1
      have hreflect :
          realAffineLineRestriction (fun i => x (some i) / x none)
              (fun i => b i / x none) P =
            (realAffineLineRestriction a c P).comp (-Polynomial.X) := by
        simpa [a, c] using
          realAffineLineRestriction_neg_direction P a c
      rw [hreflect]
      exact hsplits.comp_neg_X.C_mul _
    · exact ((hst.realAffineLineRestriction_splits_ne_zero
        (fun i => x (some i) / x none) (fun i => b i / x none)
        (fun i => div_pos (hb i) hxpos)).1).C_mul _

/-- Every positive original-coordinate boundary direction is joined to every
strictly positive direction inside the nonvanishing locus of a nonzero
ordinary homogenization with nonnegative coefficients. -/
theorem MvPolynomial.HasNonnegCoeffs.ordinaryHomogenization_boundary_joinedIn_positive
    {σ : Type*} {P : MvPolynomial σ ℝ}
    (hnn : MvPolynomial.HasNonnegCoeffs P) (hP : P ≠ 0)
    (b : σ → ℝ) (hb : ∀ i, 0 < b i)
    (u : Option σ → ℝ) (hu : ∀ o, 0 < u o) :
    JoinedIn
      {x | MvPolynomial.eval x
        (MvPolynomial.ordinaryHomogenization P P.totalDegree) ≠ 0}
      (fun o => Option.elim o 0 b) u := by
  let Q := MvPolynomial.ordinaryHomogenization P P.totalDegree
  let e : Option σ → ℝ := fun o => Option.elim o 0 b
  let Htop := MvPolynomial.homogeneousComponent P.totalDegree P
  have hQnn : MvPolynomial.HasNonnegCoeffs Q := by
    exact hnn.ordinaryHomogenization P.totalDegree
  have hQne : Q ≠ 0 := MvPolynomial.ordinaryHomogenization_ne_zero hP
  have hHtopNe : Htop ≠ 0 :=
    MvPolynomial.homogeneousComponent_totalDegree_ne_zero hP
  have hboundaryPos : 0 < MvPolynomial.eval e Q := by
    rw [show MvPolynomial.eval e Q = MvPolynomial.eval b Htop by
      simpa [e, Q, Htop] using
        MvPolynomial.eval_ordinaryHomogenization_zero P P.totalDegree b]
    exact (hnn.homogeneousComponent P.totalDegree).eval_pos hHtopNe hb
  apply JoinedIn.of_segment_subset
  rw [segment_eq_image]
  rintro x ⟨t, ht, rfl⟩
  rcases ht with ⟨ht0, ht1⟩
  by_cases htzero : t = 0
  · subst t
    simpa [e] using hboundaryPos.ne'
  · apply (hQnn.eval_pos hQne ?_).ne'
    intro o
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
    cases o with
    | none =>
        simpa [e] using mul_pos htpos (hu none)
    | some i =>
        exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr ht1) (hb i).le)
          (mul_pos htpos (hu (some i)))

/-- The exact total-degree ordinary homogenization of a nonzero real-stable
polynomial with nonnegative coefficients is real stable. -/
theorem MvRealStable.ordinaryHomogenization
    {σ : Type*} {P : MvPolynomial σ ℝ} (hst : MvRealStable P)
    (hnn : MvPolynomial.HasNonnegCoeffs P) (hP : P ≠ 0) :
    MvRealStable
      (MvPolynomial.ordinaryHomogenization P P.totalDegree) := by
  let H := MvPolynomial.ordinaryHomogenization P P.totalDegree
  have hhom : H.IsHomogeneous P.totalDegree :=
    MvPolynomial.ordinaryHomogenization_isHomogeneous P P.totalDegree
  apply mvRealStable_of_forall_hyperbolicAt_pos hhom
  intro u hu
  let b : σ → ℝ := fun i => u (some i)
  have hb : ∀ i, 0 < b i := fun i => hu (some i)
  have he : H.HyperbolicAt (fun o => Option.elim o 0 b) := by
    exact hst.ordinaryHomogenization_hyperbolicAt_boundary hnn hP b hb
  apply MvPolynomial.HyperbolicAt.of_joinedIn he hhom
  exact MvPolynomial.HasNonnegCoeffs.ordinaryHomogenization_boundary_joinedIn_positive
    hnn hP b hb u hu

/-- Ordinary homogenization in any degree at least the total degree preserves
real stability for nonzero polynomials with nonnegative coefficients. -/
theorem MvRealStable.ordinaryHomogenization_of_totalDegree_le
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ}
    (hst : MvRealStable P) (hnn : MvPolynomial.HasNonnegCoeffs P)
    (hP : P ≠ 0) (hdeg : P.totalDegree ≤ d) :
    MvRealStable (MvPolynomial.ordinaryHomogenization P d) := by
  have hexact := hst.ordinaryHomogenization hnn hP
  unfold MvRealStable complexifyMv at hexact ⊢
  rw [MvPolynomial.map_ordinaryHomogenization] at hexact ⊢
  have htotal : (MvPolynomial.map Complex.ofRealHom P).totalDegree =
      P.totalDegree := by
    unfold MvPolynomial.totalDegree
    rw [MvPolynomial.support_map_of_injective _ Complex.ofRealHom.injective]
  exact (mvUpperHalfPlaneStable_ordinaryHomogenization_congr_degree
    (p := MvPolynomial.map Complex.ofRealHom P)
    (by rw [htotal]) (by rw [htotal]; exact hdeg)).mp hexact

/-- Zero-aware ordinary homogenization theorem: in every admissible degree,
the complexification is either zero or upper-half-plane stable. -/
theorem mvUpperHalfPlaneStableOrZero_complexify_ordinaryHomogenization
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ}
    (hst : MvRealStable P) (hnn : MvPolynomial.HasNonnegCoeffs P)
    (hdeg : P.totalDegree ≤ d) :
    MvUpperHalfPlaneStableOrZero
      (complexifyMv (MvPolynomial.ordinaryHomogenization P d)) := by
  by_cases hP : P = 0
  · left
    rw [hP]
    simp [complexifyMv, MvPolynomial.ordinaryHomogenization]
  · right
    exact hst.ordinaryHomogenization_of_totalDegree_le hnn hP hdeg

end

end RealRooted
