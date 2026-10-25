module

public import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization.Derivative
public import RealRooted.AffineLineRestriction
public import RealRooted.HermiteBiehler.Converse.RootGeometry
public import RealRooted.HermiteBiehler.StablePencil
public import RealRooted.MultivariateStability.AllCombo
public import RealRooted.MultivariateStability.Specialization

/-!
# A multivariate stable-pencil implication

This file proves the multivariate Hermite--Biehler equivalence between proper
position (`G + i F` stable) and stability of the affine pencil `G + w F`.
Consequently, proper position makes every real linear combination stable or
zero.  This is the "if" direction of multivariate
Hermite--Kakeya--Obreschkoff.  The converse orientation dichotomy for an
arbitrary stable two-dimensional real span is not asserted here.
-/

@[expose] public section

open Polynomial

namespace RealRooted

noncomputable section

/-- A stable complex polynomial is no smaller in norm above the real axis
than at the conjugate point below it. -/
private theorem IsUpperHalfPlaneStable.norm_eval_conj_le
    {p : ℂ[X]} (hp : IsUpperHalfPlaneStable p)
    {z : ℂ} (hz : 0 < z.im) :
    ‖p.eval (starRingEnd ℂ z)‖ ≤ ‖p.eval z‖ := by
  rw [eval_eq_prod_roots_complex, eval_eq_prod_roots_complex,
    norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg p.leadingCoeff)
  exact multiset_prod_norm_conj_le hz p.roots fun w hw =>
    im_nonpos_of_stable_root hp (Polynomial.isRoot_of_mem_roots hw)

/-- Reflection across the real axis moves `-w + i` strictly farther from the
origin when `w` is in the open upper half-plane. -/
private theorem norm_neg_conj_add_I_gt {w : ℂ} (hw : 0 < w.im) :
    ‖-w + Complex.I‖ < ‖-starRingEnd ℂ w + Complex.I‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_lt_sqrt (by positivity)
  simp only [Complex.add_re, Complex.neg_re, Complex.I_re,
    Complex.add_im, Complex.neg_im, Complex.I_im, Complex.conj_re,
    Complex.conj_im]
  nlinarith

/-- A stable Hermite--Biehler polynomial `f + i g` produces the stable real
pencil `f + w g`.  This is the univariate analytic step in Lemma 1.8. -/
private theorem IsUpperHalfPlaneStable.isUpperHalfPlaneStablePencil_hermiteBiehler
    {f g : ℝ[X]}
    (h : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    IsUpperHalfPlaneStablePencil f g := by
  intro z w hz hw hzero
  let F := (complexify f).eval z
  let G := (complexify g).eval z
  have hG : G ≠ 0 := by
    intro hGzero
    have hFzero : F = 0 := by
      dsimp only [F, G] at hzero hGzero ⊢
      rw [hGzero, mul_zero, add_zero] at hzero
      exact hzero
    apply h z hz
    simp [eval_hermiteBiehlerPolynomial, F, G, hFzero, hGzero]
  have hF : F = -w * G := by
    dsimp only [F, G] at hzero ⊢
    linear_combination hzero
  have hnorm := h.norm_eval_conj_le hz
  have hnorm' : ‖(-starRingEnd ℂ w + Complex.I) * starRingEnd ℂ G‖ ≤
      ‖(-w + Complex.I) * G‖ := by
    rw [eval_hermiteBiehlerPolynomial,
      eval_hermiteBiehlerPolynomial, eval_complexify_conj,
      eval_complexify_conj] at hnorm
    have hFconj : starRingEnd ℂ F =
        -(starRingEnd ℂ w) * starRingEnd ℂ G := by
      rw [hF, map_mul, map_neg]
    change ‖starRingEnd ℂ F + Complex.I * starRingEnd ℂ G‖ ≤
      ‖F + Complex.I * G‖ at hnorm
    rw [hFconj, hF] at hnorm
    simpa only [neg_mul, add_mul] using hnorm
  rw [norm_mul, norm_mul, Complex.norm_conj] at hnorm'
  have hGnorm : 0 < ‖G‖ := norm_pos_iff.mpr hG
  have hfactor : ‖-starRingEnd ℂ w + Complex.I‖ ≤ ‖-w + Complex.I‖ :=
    le_of_mul_le_mul_right hnorm' hGnorm
  exact (not_lt_of_ge hfactor) (norm_neg_conj_add_I_gt hw)

/-- Evaluation of a complexified real affine-line restriction, using the
project's `complexify` normalization. -/
private theorem eval_complexify_realAffineLineRestriction'
    {σ : Type*} (a b : σ → ℝ) (P : MvPolynomial σ ℝ) (t : ℂ) :
    (complexify (realAffineLineRestriction a b P)).eval t =
      MvPolynomial.eval (fun i => (a i : ℂ) + (b i : ℂ) * t)
        (complexifyMv P) := by
  unfold complexify
  have hmap : Complex.ofRealHom = algebraMap ℝ ℂ := by
    ext r
    rfl
  rw [hmap]
  exact eval_complexify_realAffineLineRestriction a b P t

/-- The source-faithful proper-position predicate `F \ll G`: the complex
polynomial `G + i F` is upper-half-plane stable. -/
def MvProperPosition {σ : Type*} (F G : MvPolynomial σ ℝ) : Prop :=
  MvUpperHalfPlaneStable
    (complexifyMv G + MvPolynomial.C Complex.I * complexifyMv F)

/-- The affine pencil `G + w F` is real stable in the old variables and the
fresh parameter `w`. -/
def MvStablePencil {σ : Type*} (F G : MvPolynomial σ ℝ) : Prop :=
  MvRealStable
    (MvPolynomial.rename some G + MvPolynomial.X none *
      MvPolynomial.rename some F)

/-- Proper position makes the corresponding real affine pencil stable.  The
proof restricts to every positive real affine line and applies the univariate
Hermite--Biehler norm argument above. -/
theorem MvProperPosition.mvStablePencil
    {σ : Type*} {F G : MvPolynomial σ ℝ}
    (h : MvProperPosition F G) : MvStablePencil F G := by
  intro u hu
  let z : σ → ℂ := u ∘ some
  let a : σ → ℝ := fun i => (z i).re
  let b : σ → ℝ := fun i => (z i).im
  have hb : ∀ i, 0 < b i := by
    intro i
    exact hu (some i)
  let f := realAffineLineRestriction a b G
  let g := realAffineLineRestriction a b F
  have hline : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) := by
    intro t ht
    have hpoint : ∀ i, 0 < ((a i : ℂ) + (b i : ℂ) * t).im := by
      intro i
      simpa using mul_pos (hb i) ht
    have heval := h (fun i => (a i : ℂ) + (b i : ℂ) * t) hpoint
    rw [eval_hermiteBiehlerPolynomial,
      eval_complexify_realAffineLineRestriction',
      eval_complexify_realAffineLineRestriction']
    simpa only [MvPolynomial.eval_add, MvPolynomial.eval_mul,
      MvPolynomial.eval_C] using heval
  have hpencil :=
    hline.isUpperHalfPlaneStablePencil_hermiteBiehler
  have heval := hpencil Complex.I (u none) (by simp) (hu none)
  have hz : (fun i => (a i : ℂ) + (b i : ℂ) * Complex.I) = z := by
    funext i
    exact Complex.ext (by simp [a, b]) (by simp [a, b])
  have hcomp : u ∘ some = z := rfl
  rw [eval_complexify_realAffineLineRestriction',
    eval_complexify_realAffineLineRestriction', hz] at heval
  simpa [MvStablePencil, complexifyMv, MvPolynomial.eval₂_rename,
    hcomp, Function.comp_def] using heval

/-- A stable real affine pencil specializes at `w = i` to the proper-position
polynomial `G + i F`. -/
theorem MvStablePencil.mvProperPosition
    {σ : Type*} {F G : MvPolynomial σ ℝ}
    (h : MvStablePencil F G) : MvProperPosition F G := by
  intro z hz
  let u : Option σ → ℂ := fun o => o.elim Complex.I z
  have hu : ∀ o, 0 < (u o).im := by
    intro o
    cases o with
    | none => simp [u]
    | some i => simpa [u] using hz i
  have heval := h u hu
  simpa [MvStablePencil, MvProperPosition, complexifyMv,
    MvPolynomial.eval₂_rename, u, Function.comp_def] using heval

/-- Multivariate proper position is equivalent to stability of the associated
fresh-variable affine pencil. -/
theorem mvProperPosition_iff_mvStablePencil
    {σ : Type*} {F G : MvPolynomial σ ℝ} :
    MvProperPosition F G ↔ MvStablePencil F G :=
  ⟨MvProperPosition.mvStablePencil, MvStablePencil.mvProperPosition⟩

/-- The direction polynomial of a stable real affine pencil is real stable or
zero. -/
theorem MvStablePencil.left
    {σ : Type*} [Finite σ] {F G : MvPolynomial σ ℝ}
    (h : MvStablePencil F G) : MvRealStableOrZero F := by
  rw [mvRealStableOrZero_iff_complexifyMv]
  let P : MvPolynomial (Option σ) ℝ :=
    MvPolynomial.rename some G + MvPolynomial.X none *
      MvPolynomial.rename some F
  have hderiv :=
    (show MvUpperHalfPlaneStable (complexifyMv P) from h).pderiv_zero_or_of_finite none
  have hGnone : none ∉ (MvPolynomial.rename some G).vars := by
    intro hnone
    obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename some G hnone
    exact (Option.some_ne_none i) hi
  have hFnone : none ∉ (MvPolynomial.rename some F).vars := by
    intro hnone
    obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename some F hnone
    exact (Option.some_ne_none i) hi
  have hPderiv : MvPolynomial.pderiv none P =
      MvPolynomial.rename some F := by
    simp [P, MvPolynomial.pderiv_eq_zero_of_notMem_vars hGnone,
      MvPolynomial.pderiv_eq_zero_of_notMem_vars hFnone]
  have hderivEq : MvPolynomial.pderiv none (complexifyMv P) =
      MvPolynomial.rename some (complexifyMv F) := by
    rw [complexifyMv, MvPolynomial.pderiv_map, hPderiv,
      MvPolynomial.map_rename]
    rfl
  rw [hderivEq] at hderiv
  exact MvUpperHalfPlaneStableOrZero.of_rename hderiv
    (Option.some_injective σ)

/-- The base polynomial of a stable real affine pencil is real stable or
zero. -/
theorem MvStablePencil.right
    {σ : Type*} {F G : MvPolynomial σ ℝ}
    (h : MvStablePencil F G) : MvRealStableOrZero G := by
  simpa using h.affineExtension_specialize_zero_or 0

/-- A stable real affine pencil has a real-stable-or-zero span.  This is the
easy implication in the multivariate Hermite--Kakeya--Obreschkoff theorem. -/
theorem MvStablePencil.allComboMvRealStableOrZero
    {σ : Type*} [Finite σ] {F G : MvPolynomial σ ℝ}
    (h : MvStablePencil F G) : AllComboMvRealStableOrZero F G := by
  intro α β
  by_cases hβ : β = 0
  · subst β
    simpa using h.left.C_mul α
  · have hslope := h.affineExtension_specialize_zero_or (α / β)
    have hscaled := hslope.C_mul β
    have hcoeff : β * (α / β) = α := by field_simp
    simpa only [mul_add, ← mul_assoc, ← MvPolynomial.C_mul, hcoeff,
      add_comm] using hscaled

/-- Proper position implies that every real linear combination is real stable
or zero.  This is the forward implication in the multivariate
Hermite--Kakeya--Obreschkoff theorem. -/
theorem MvProperPosition.allComboMvRealStableOrZero
    {σ : Type*} [Finite σ] {F G : MvPolynomial σ ℝ}
    (h : MvProperPosition F G) : AllComboMvRealStableOrZero F G :=
  h.mvStablePencil.allComboMvRealStableOrZero

end

end RealRooted
