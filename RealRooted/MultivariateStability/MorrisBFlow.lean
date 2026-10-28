module

public import RealRooted.MultivariateStability.MorrisOperator
import RealRooted.BorceaBranden.Applications.ComplexDiagonalRootLocation
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Eval
public import RealRooted.MultiplierSequence.QuadraticExponential
import RealRooted.Polarization
public import RealRooted.MultivariateStability

/-!
# The flow of the Liu--Zhang Morris `B` operator

This file constructs the algebraic flow dictated by Liu--Zhang,
`arXiv:2609.15201v2`, equations (4.20)--(4.22).
-/

@[expose] public section

open MvPolynomial Polynomial

namespace RealRooted.LiuZhang

open Finset

noncomputable section

/-- The factor by which `exp(t B_q)` scales the `k`-th elementary symmetric
polynomial. The index is zero-based, so it represents `e_(k+1)`. -/
def morrisBScale (q : ℕ) (t : ℝ) (k : Fin q) : ℝ :=
  Real.exp (t * ((k + 1) * (2 * q - (k + 1) - 1) : ℕ))

/-- The exponent identity behind the root lift in Liu--Zhang, equation
(4.22). -/
theorem morrisBScale_eq_multiplier (q : ℕ) (t : ℝ) (k : Fin q) :
    morrisBScale q t k =
      Real.exp (t * (q * (q - 1) : ℕ)) *
        quadraticExponentialMultiplier t (q - (k + 1)) := by
  have hle : k + 1 ≤ q := Nat.succ_le_iff.mpr k.isLt
  rcases hle.eq_or_lt with heq | hlt
  · have hw : (k + 1) * (2 * q - (k + 1) - 1) = q * (q - 1) := by
      simp [heq, two_mul]
    have hzero : q - (k + 1) = 0 := Nat.sub_eq_zero_of_le heq.ge
    rw [morrisBScale, quadraticExponentialMultiplier, hw]
    simp [hzero]
  · rw [morrisBScale, quadraticExponentialMultiplier,
      ← Real.exp_add]
    congr 1
    have hq : 1 ≤ q := (Nat.zero_lt_succ k).trans_le hlt.le
    have hd : 1 ≤ q - (k + 1) := Nat.one_le_iff_ne_zero.mpr
      (Nat.sub_ne_zero_iff_lt.mpr hlt)
    have hn2 : k + 1 ≤ 2 * q :=
      hlt.le.trans (Nat.le_mul_of_pos_left q (by norm_num))
    have hn2sub : 1 ≤ 2 * q - (k + 1) := Nat.one_le_iff_ne_zero.mpr
      (Nat.sub_ne_zero_iff_lt.mpr
        (hlt.trans_le (Nat.le_mul_of_pos_left q (by norm_num))))
    push_cast [Nat.cast_sub hlt.le, Nat.cast_sub hq,
      Nat.cast_sub hd, Nat.cast_sub hn2, Nat.cast_sub hn2sub]
    ring

private theorem exists_fin_map_eq_of_card_eq {α : Type*}
    (s : Multiset α) {q : ℕ} (hs : s.card = q) :
    ∃ y : Fin q → α, Finset.univ.val.map y = s := by
  let l := s.toList
  have hl : l.length = q := by simp [l, hs]
  let y : Fin q → α := fun i => l.get (Fin.cast hl.symm i)
  refine ⟨y, ?_⟩
  rw [Fin.univ_val_map, ← Multiset.coe_toList s]
  congr 1
  rw [List.ext_get_iff]
  refine ⟨by simp [l, hl], ?_⟩
  intro n hn₁ hn₂
  simp [y, l]

private theorem coeff_polarizationRootPolynomial {q : ℕ}
    (x : Fin q → ℂ) {m : ℕ} (hm : m ≤ q) :
    (polarizationRootPolynomial x).coeff (q - m) =
      (-1 : ℂ) ^ m * (Finset.univ.val.map x).esymm m := by
  unfold polarizationRootPolynomial
  rw [Multiset.prod_X_sub_C_coeff]
  · rw [Multiset.card_map]
    simp [Nat.sub_sub_self hm]
  · simp

private theorem monic_polarizationRootPolynomial {q : ℕ}
    (x : Fin q → ℂ) : (polarizationRootPolynomial x).Monic := by
  unfold polarizationRootPolynomial
  exact Polynomial.monic_multiset_prod_of_monic _ _
    fun z _ => monic_X_sub_C z

private theorem scaled_complexDiagonal_monic_and_natDegree {q : ℕ} {t : ℝ}
    (x : Fin q → ℂ) :
    (Polynomial.C (Real.exp (t * (q * (q - 1) : ℕ)) : ℂ) *
      BorceaBranden.realDiagonalOperator
        (quadraticExponentialMultiplier t)
        (polarizationRootPolynomial x)).Monic ∧
      (Polynomial.C (Real.exp (t * (q * (q - 1) : ℕ)) : ℂ) *
        BorceaBranden.realDiagonalOperator
          (quadraticExponentialMultiplier t)
          (polarizationRootPolynomial x)).natDegree = q := by
  let a : ℝ := Real.exp (t * (q * (q - 1) : ℕ))
  let f := polarizationRootPolynomial x
  let g := Polynomial.C (a : ℂ) * BorceaBranden.realDiagonalOperator
    (quadraticExponentialMultiplier t) f
  have hfcoeff : f.coeff q = 1 := by
    rw [← (monic_polarizationRootPolynomial x).leadingCoeff,
      leadingCoeff, natDegree_polarizationRootPolynomial]
  have hgcoeff : g.coeff q = 1 := by
    rw [Polynomial.coeff_C_mul,
      BorceaBranden.coeff_realDiagonalOperator, hfcoeff]
    dsimp only [a]
    rw [quadraticExponentialMultiplier]
    simp only [mul_one]
    rw [← Complex.ofReal_mul]
    norm_cast
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hgle : g.natDegree ≤ q := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((BorceaBranden.natDegree_realDiagonalOperator_le _ f).trans
        (natDegree_polarizationRootPolynomial x).le)
  have hgdeg : g.natDegree = q :=
    le_antisymm hgle (le_natDegree_of_ne_zero (hgcoeff.symm ▸ one_ne_zero))
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one q hgle hgcoeff, hgdeg⟩

private theorem scaledDiagonal_coeff {q : ℕ} (t : ℝ)
    (x : Fin q → ℂ) (k : Fin q) :
    (Polynomial.C
        (Real.exp (t * (q * (q - 1) : ℕ)) : ℂ) *
      BorceaBranden.realDiagonalOperator
        (quadraticExponentialMultiplier t)
        (polarizationRootPolynomial x)).coeff (q - ((k : ℕ) + 1)) =
      (morrisBScale q t k : ℂ) * (-1 : ℂ) ^ ((k : ℕ) + 1) *
        (Finset.univ.val.map x).esymm ((k : ℕ) + 1) := by
  rw [Polynomial.coeff_C_mul,
    BorceaBranden.coeff_realDiagonalOperator,
    coeff_polarizationRootPolynomial x
      (Nat.succ_le_iff.mpr k.isLt)]
  have hscale :
      (Real.exp (t * (q * (q - 1) : ℕ)) : ℂ) *
        quadraticExponentialMultiplier t (q - ((k : ℕ) + 1)) =
          morrisBScale q t k := by
    rw [← Complex.ofReal_mul]
    exact_mod_cast (morrisBScale_eq_multiplier q t k).symm
  rw [← mul_assoc, hscale]
  simp only [Nat.succ_eq_add_one, mul_assoc]

/-- The strict upper-half-plane root lift in Liu--Zhang equation (4.22). -/
theorem exists_morrisBRootLift {q : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (x : Fin q → ℂ) (hx : ∀ i, 0 < (x i).im) :
    ∃ y : Fin q → ℂ, (∀ i, 0 < (y i).im) ∧
      ∀ k : Fin q,
        (Finset.univ.val.map y).esymm ((k : ℕ) + 1) =
          morrisBScale q t k *
            (Finset.univ.val.map x).esymm ((k : ℕ) + 1) := by
  let f : ℂ[X] := polarizationRootPolynomial x
  let a : ℝ := Real.exp (t * (q * (q - 1) : ℕ))
  let Tf : ℂ[X] := BorceaBranden.realDiagonalOperator
    (quadraticExponentialMultiplier t) f
  let g : ℂ[X] := Polynomial.C (a : ℂ) * Tf
  have hfmonic : f.Monic := monic_polarizationRootPolynomial x
  have hf0 : f ≠ 0 := hfmonic.ne_zero
  have hfroots : ∀ z ∈ f.roots, 0 < z.im := by
    intro z hz
    obtain ⟨i, rfl⟩ := exists_eq_of_isRoot_polarizationRootPolynomial
      (Polynomial.isRoot_of_mem_roots hz)
    exact hx i
  have hTfroots : ∀ z ∈ Tf.roots, 0 < z.im := by
    exact BorceaBranden.IsPFMultiplierSequence.roots_im_pos_complexDiagonal
      (isPFMultiplierSequence_quadraticExponentialMultiplier ht)
      (fun _ => Real.exp_ne_zero _) hf0 hfroots
  obtain ⟨hgmonic, hgdeg⟩ := scaled_complexDiagonal_monic_and_natDegree x
  have hgcard : g.roots.card = q := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hgdeg]
  obtain ⟨y, hyroots⟩ := exists_fin_map_eq_of_card_eq g.roots hgcard
  refine ⟨y, ?_, ?_⟩
  · intro i
    have hyroot : y i ∈ g.roots := by
      rw [← hyroots]
      simp
    have ha0 : (a : ℂ) ≠ 0 := by simp [a]
    have : y i ∈ Tf.roots := by
      rw [← Polynomial.roots_C_mul Tf ha0]
      exact hyroot
    exact hTfroots (y i) this
  · have hpoly : polarizationRootPolynomial y = g := by
      unfold polarizationRootPolynomial
      rw [hyroots]
      exact (IsAlgClosed.splits g).eq_prod_roots_of_monic hgmonic |>.symm
    intro k
    have hcoeff := congrArg
      (fun p : ℂ[X] => p.coeff (q - ((k : ℕ) + 1))) hpoly
    rw [coeff_polarizationRootPolynomial y
      (Nat.succ_le_iff.mpr k.isLt)] at hcoeff
    rw [scaledDiagonal_coeff t x k] at hcoeff
    have hsign : (-1 : ℂ) ^ ((k : ℕ) + 1) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    apply mul_left_cancel₀ hsign
    rw [Nat.succ_eq_add_one] at hcoeff
    rw [hcoeff]
    ring

/-- The algebra isomorphism from `MvPolynomial (Fin q) ℝ` onto the symmetric polynomials in `q`
variables, given by the elementary symmetric polynomials. -/
def morrisElementaryEquiv (q : ℕ) :
    MvPolynomial (Fin q) ℝ ≃ₐ[ℝ]
      symmetricSubalgebra (Fin q) ℝ :=
  esymmAlgEquiv (Fin q) ℝ (by simp)

private theorem morrisElementaryEquiv_apply (q : ℕ)
    (G : MvPolynomial (Fin q) ℝ) :
    morrisElementaryEquiv q G = esymmAlgHom (Fin q) ℝ q G :=
  esymmAlgEquiv_apply (Fin q) ℝ (by simp) G

/-- The algebraic flow from Liu--Zhang, equation (4.21), applied to an
elementary-coordinate polynomial. -/
def morrisBFlowCoordinates (q : ℕ) (t : ℝ) :
    MvPolynomial (Fin q) ℝ →ₐ[ℝ]
      symmetricSubalgebra (Fin q) ℝ :=
  (esymmAlgHom (Fin q) ℝ q).comp
    (aeval fun k : Fin q =>
      MvPolynomial.C (morrisBScale q t k) * MvPolynomial.X k)

/-- The algebraic `B_q` flow on the symmetric polynomial ring. -/
def morrisBFlow (q : ℕ) (t : ℝ) :
    symmetricSubalgebra (Fin q) ℝ →ₐ[ℝ]
      symmetricSubalgebra (Fin q) ℝ :=
  (morrisBFlowCoordinates q t).comp
    (morrisElementaryEquiv q).symm.toAlgHom

@[simp]
theorem morrisBFlow_esymm (q : ℕ) (t : ℝ) (k : Fin q) :
    morrisBFlow q t
        ⟨esymm (Fin q) ℝ (k + 1), esymm_isSymmetric (Fin q) ℝ _⟩ =
      morrisBScale q t k •
        ⟨esymm (Fin q) ℝ (k + 1), esymm_isSymmetric (Fin q) ℝ _⟩ := by
  apply Subtype.ext
  simp [morrisBFlow, morrisBFlowCoordinates, morrisElementaryEquiv,
    esymmAlgEquiv_symm_apply, esymmAlgHom_apply,
    MvPolynomial.smul_eq_C_mul]

@[simp]
theorem morrisBFlowCoordinates_zero (q : ℕ)
    (G : MvPolynomial (Fin q) ℝ) :
    morrisBFlowCoordinates q 0 G = esymmAlgHom (Fin q) ℝ q G := by
  apply Subtype.ext
  simp [morrisBFlowCoordinates, morrisBScale, esymmAlgHom_apply]

@[simp]
theorem morrisBFlow_zero (q : ℕ)
    (P : symmetricSubalgebra (Fin q) ℝ) : morrisBFlow q 0 P = P := by
  change morrisBFlowCoordinates q 0 ((morrisElementaryEquiv q).symm P) = P
  rw [morrisBFlowCoordinates_zero]
  rw [← morrisElementaryEquiv_apply]
  exact (morrisElementaryEquiv q).apply_symm_apply P

private theorem aeval_complex_eq_eval_complexifyMv {q : ℕ}
    (x : Fin q → ℂ) (P : MvPolynomial (Fin q) ℝ) :
    aeval x P = eval x (complexifyMv P) := by
  rw [MvPolynomial.aeval_def, complexifyMv, MvPolynomial.eval_map]
  rfl

private theorem aeval_morrisBFlow {q : ℕ} (t : ℝ)
    (x y : Fin q → ℂ)
    (hxy : ∀ k : Fin q,
      (univ.val.map y).esymm (k + 1) =
        morrisBScale q t k * (univ.val.map x).esymm (k + 1))
    (G : MvPolynomial (Fin q) ℝ) :
    aeval x ((morrisBFlowCoordinates q t G :
        symmetricSubalgebra (Fin q) ℝ) :
        MvPolynomial (Fin q) ℝ) =
      aeval y ((esymmAlgHom (Fin q) ℝ q G :
        symmetricSubalgebra (Fin q) ℝ) : MvPolynomial (Fin q) ℝ) := by
  simp only [morrisBFlowCoordinates, AlgHom.comp_apply, esymmAlgHom_apply]
  let e : Fin q → MvPolynomial (Fin q) ℝ :=
    fun k => esymm (Fin q) ℝ (k + 1)
  let s : Fin q → MvPolynomial (Fin q) ℝ :=
    fun k => MvPolynomial.C (morrisBScale q t k) * MvPolynomial.X k
  let ex : Fin q → ℂ := fun k => aeval x (e k)
  let ey : Fin q → ℂ := fun k => aeval y (e k)
  have heval : (fun k => aeval ex (s k)) = ey := by
    funext k
    simp only [s, ex, ey, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X]
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm,
      MvPolynomial.aeval_esymm_eq_multiset_esymm, hxy k]
    rfl
  calc
    aeval x (aeval e (aeval s G)) = aeval ex (aeval s G) := by
      exact DFunLike.congr_fun (comp_aeval e (aeval x)) _
    _ = aeval (fun k => aeval ex (s k)) G := by
      exact DFunLike.congr_fun (comp_aeval s (aeval ex)) _
    _ = aeval ey G := by rw [heval]
    _ = aeval y (aeval e G) := by
      exact (DFunLike.congr_fun (comp_aeval e (aeval y)) _).symm

/-- The Liu--Zhang `B_q` flow preserves real stability. -/
theorem MvRealStable.morrisBFlow {q : ℕ} {t : ℝ} (ht : 0 ≤ t)
    {P : symmetricSubalgebra (Fin q) ℝ}
    (hP : MvRealStable (P : MvPolynomial (Fin q) ℝ)) :
    MvRealStable (morrisBFlow q t P : MvPolynomial (Fin q) ℝ) := by
  let G := (morrisElementaryEquiv q).symm P
  have hG : MvRealStable ((esymmAlgHom (Fin q) ℝ q G :
      symmetricSubalgebra (Fin q) ℝ) : MvPolynomial (Fin q) ℝ) := by
    rw [← morrisElementaryEquiv_apply, (morrisElementaryEquiv q).apply_symm_apply]
    exact hP
  intro x hx
  obtain ⟨y, hy, hxy⟩ := exists_morrisBRootLift ht x hx
  have hflow := aeval_morrisBFlow t x y hxy G
  rw [← aeval_complex_eq_eval_complexifyMv] at ⊢
  change aeval x ((morrisBFlowCoordinates q t G :
    symmetricSubalgebra (Fin q) ℝ) : MvPolynomial (Fin q) ℝ) ≠ 0
  rw [hflow, aeval_complex_eq_eval_complexifyMv]
  exact hG y hy

end

end RealRooted.LiuZhang
