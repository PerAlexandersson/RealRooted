module

public import RealRooted.ExponentialRows.HermiteAuxiliary
public import RealRooted.ExponentialRows.ProductInsertion
public import RealRooted.Hermite.Gaussian
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import RealRooted.ExponentialRows.GaussianIdentity
public import RealRooted.HermiteBiehler.Basic
import RealRooted.ExponentialRows.HermiteSeeds
import RealRooted.ExponentialRows.QuarticCoefficients
import RealRooted.Hermite.Grace
import RealRooted.HermiteBiehler.Converse.Wronskian
import RealRooted.HermiteBiehler.Forward
import RealRooted.ExponentialRows.QuarticGrace
import Mathlib.Tactic

/-!
# Disjoint consecutive roots under finite Gaussian evaluation

We translate the strictly interlacing Hermite seeds to the auxiliary variable.
The Hermite–Biehler polynomial has all its roots strictly below the real line.
Grace's Gaussian nonvanishing theorem therefore excludes a shared row root.

Source: the unpublished quartic-row argument in RealRooted issue #2649,
https://github.com/PerAlexandersson/RealRooted/issues/2649.
-/

public section

open Polynomial

namespace RealRooted

/-- The Taylor derivatives of the Gaussian symbol are its homogeneous Hermite moments. -/
theorem iteratedDeriv_exp_mul_sq_zero (s : ℂ) (j : ℕ) :
    iteratedDeriv j (fun z : ℂ => Complex.exp (s * z ^ 2)) 0 = hermiteHomogeneous 0 s j := by
  let f (z : ℂ) := Complex.exp (s * z ^ 2)
  have hd : deriv f = fun z => (2 * s) * (z * f z) := by
    funext z
    refine (((hasDerivAt_pow 2 z).const_mul s).cexp.deriv).trans ?_
    change _ = 2 * s * (z * Complex.exp (s * z ^ 2))
    rw [show ((2 : ℕ) : ℂ) * z ^ (2 - 1) = 2 * z by norm_num]
    ring
  change iteratedDeriv j f 0 = _
  induction j using Nat.twoStepInduction with
  | zero => simp [f]
  | one => simp [iteratedDeriv_succ', hd]
  | more j ih _ =>
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field]
    have hprod := iteratedDeriv_fun_mul (n := j + 1) (x := (0 : ℂ))
      (f := fun z : ℂ => z) (g := f) (by fun_prop) (by dsimp [f]; fun_prop)
    rw [hprod, Finset.sum_eq_single 1]
    · simp [ih, hermiteHomogeneous_add_two]
      ring
    · intro i _ hi
      simp [iteratedDeriv_fun_id_zero, hi]
    · simp

/-- Evaluating the finite Taylor differential operator at a real point is the
Gaussian moment functional on the translated polynomial. -/
theorem eval_taylorDifferentialOperator_exp_mul_sq (p : ℝ[X]) (s x : ℝ) :
    (taylorDifferentialOperator (fun z => Complex.exp ((s : ℂ) * z ^ 2)) p).eval x =
      (gaussianEval (s : ℂ) ((complexify p).comp (X + C (x : ℂ)))).re := by
  have hmap : (complexify p).comp (X + C (x : ℂ)) = complexify (taylor x p) := by
    simp [complexify, taylor_apply, Polynomial.map_comp]
  have hsupp : (complexify (taylor x p)).support ⊆ Finset.range (p.natDegree + 1) := by
    intro j hj
    exact Finset.mem_range_succ_iff.mpr ((le_natDegree_of_mem_supp j hj).trans
      (natDegree_map_le.trans (natDegree_taylor p x).le))
  rw [hmap, gaussianEval, Polynomial.sum_eq_of_subset _ (by simp) hsupp, Complex.re_sum]
  simp only [taylorDifferentialOperator, eval_finsetSum, eval_mul, eval_C, complexify,
    coeff_map, Complex.ofRealHom_eq_coe, Complex.re_ofReal_mul, iteratedDeriv_exp_mul_sq_zero]
  apply Finset.sum_congr rfl
  intro j _
  have hder : (derivative^[j] p).eval x = (j.factorial : ℝ) * (taylor x p).coeff j := by
    rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, taylor_coeff]
    simp [nsmul_eq_mul]
  rw [hder, Complex.div_natCast_re]
  field_simp

/-- A strictly separated Hermite–Biehler pair stays disjoint after real translation
and backward Gaussian evaluation. -/
theorem gaussianEval_comp_ne_zero_of_strictInterl {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (hgf : StrictInterl g f)
    (hdis : ∀ x, ¬ (g.IsRoot x ∧ f.IsRoot x)) {h : ℝ} (hh : 0 ≤ h) (q : ℝ) :
    ¬ (gaussianEval (-(h : ℂ)) ((complexify g).comp (X + C (q : ℂ))) = 0 ∧
      gaussianEval (-(h : ℂ)) ((complexify f).comp (X + C (q : ℂ))) = 0) := by
  let P := (hermiteBiehlerPolynomial f g).comp (X + C (q : ℂ))
  have hbelow (z : ℂ) (hz : P.IsRoot z) : z.im < 0 := by
    change ((hermiteBiehlerPolynomial f g).comp _).IsRoot z at hz
    simp only [isRoot_comp, eval_add, eval_X, eval_C] at hz
    rcases lt_trichotomy z.im 0 with hn | he | hp
    · exact hn
    · have heq : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using he)
      rw [heq, ← Complex.ofReal_add] at hz
      exact (hnoreal_of_no_common_real_root (f := f) (g := g)
        (fun ⟨r, hfr, hgr⟩ => hdis r ⟨hgr, hfr⟩) _ hz).elim
    · exact (hermiteBiehlerForwardPos hf hg hgf _ (by simpa using hp) hz).elim
  have hn := gaussianEval_ne_zero_of_roots_im_pos hh
    (p := P.comp (C (-1) * X)) (by
      intro z hz
      have hneg := hbelow (-z) (by simpa [isRoot_comp] using hz)
      simpa using hneg)
  rw [gaussianEval_comp_C_mul_X] at hn
  simp only [neg_one_sq, one_mul] at hn
  rintro ⟨hg0, hf0⟩
  apply hn
  simp [P, hermiteBiehlerPolynomial, add_comp, mul_comp, hg0, hf0]

namespace ExponentialRows

/-- Translation by the quadratic shift identifies an affine seed with the auxiliary row. -/
theorem complexify_hermiteHomogeneous_comp_add (β q : ℝ) (n : ℕ) :
    (complexify (hermiteHomogeneous (C (1 - β * q) + C β * X) X n)).comp
      (X + C (q : ℂ)) = hermiteAuxiliary β q n := by
  let F := (compRingHom (X + C (q : ℂ))).comp (mapRingHom Complex.ofRealHom)
  change F (hermiteHomogeneous _ _ n) = _
  rw [map_hermiteHomogeneous]
  unfold hermiteAuxiliary
  congr 1
  · simp [F, add_comp, mul_comp]
    ring
  · simp [F]

/-- The finite Gaussian evaluation of the translated real seed is the quartic row. -/
theorem gaussianEval_affine_eq_insertionRow (β γ c t : ℝ) (n : ℕ) :
    gaussianEval ((c * t : ℝ) : ℂ)
      ((complexify (hermiteHomogeneous (C (1 - β * (γ * t)) + C β * X) X n)).comp
        (X + C ((γ * t : ℝ) : ℂ))) =
      (((insertionRow (markedBlockWeights
        (C (γ + c * β ^ 2) * X ^ 2 + C (2 * c * β) * X ^ 3 + C c * X ^ 4)) n).eval t : ℝ) : ℂ) := by
  rw [complexify_hermiteHomogeneous_comp_add]
  push_cast
  convert gaussianEval_hermiteAuxiliary_eq_insertionRow β γ c t n using 1
  exact (eval₂_at_apply Complex.ofRealHom t).symm

/-- The backward heat operator on the real Hermite seed, evaluated at the frozen
shift, gives the canonical quartic insertion row at the same parameter. -/
theorem eval_heat_hermiteHomogeneous_eq_insertionRow (β γ c t : ℝ) (n : ℕ) :
    (taylorDifferentialOperator (fun z => Complex.exp (((c * t : ℝ) : ℂ) * z ^ 2))
      (hermiteHomogeneous (C (1 - β * (γ * t)) + C β * X) X n)).eval (γ * t) =
      (insertionRow (markedBlockWeights
        (C (γ + c * β ^ 2) * X ^ 2 + C (2 * c * β) * X ^ 3 + C c * X ^ 4)) n).eval t := by
  rw [eval_taylorDifferentialOperator_exp_mul_sq, gaussianEval_affine_eq_insertionRow]
  rfl

/-- Completed-square quartic insertion rows have disjoint consecutive real roots. -/
theorem insertionRow_no_common_root_quartic_square {β γ c : ℝ}
    (hβ : 0 < β) (hγ : 0 ≤ γ) (hc : 0 < c) (n : ℕ) :
    let w := markedBlockWeights
      (C (γ + c * β ^ 2) * X ^ 2 + C (2 * c * β) * X ^ 3 + C c * X ^ 4)
    ∀ t, ¬ ((insertionRow w n).IsRoot t ∧ (insertionRow w (n + 1)).IsRoot t) := by
  dsimp only
  intro t ht
  have hne := (insertionRow_isRealRooted_quartic_of_nonneg
    (add_nonneg hγ (by positivity : 0 ≤ c * β ^ 2))
    (show 0 ≤ 2 * c * β by positivity) hc.le n).1
  have htneg := roots_insertionRow_quartic_neg (add_nonneg hγ (by positivity))
    (show 0 ≤ 2 * c * β by positivity) hc.le n t ((mem_roots hne).mpr ht.1)
  have hκ : 0 < 1 - β * (γ * t) :=
    sub_pos.mpr (lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos hβ.le
      (mul_nonpos_of_nonneg_of_nonpos hγ htneg.le)) zero_lt_one)
  have hs := hermiteHomogeneous_strictInterl_affine hκ hβ n
  have hn := hasNonnegCoeffs_hermiteHomogeneous_affine hκ.le hβ.le
  apply gaussianEval_comp_ne_zero_of_strictInterl
    ((hn (n + 1)).pos_leadingCoeff hs.1.2.1.1) ((hn n).pos_leadingCoeff hs.1.1.1)
    hs.1 hs.2 (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hc.le htneg.le)) (γ * t)
  rw [← Complex.ofReal_neg, neg_neg, gaussianEval_affine_eq_insertionRow,
    gaussianEval_affine_eq_insertionRow, ht.1.eq_zero, ht.2.eq_zero]
  simp

/-- Adjacent positive quartic rows in the discriminant-complement regime have no common root. -/
theorem insertionRow_no_common_root_quartic {a b c : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hdisc : b ^ 2 ≤ 4 * a * c) (n : ℕ) :
    let w := markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)
    ∀ t, ¬ ((insertionRow w n).IsRoot t ∧ (insertionRow w (n + 1)).IsRoot t) := by
  let β := b / (2 * c)
  let γ := a - b ^ 2 / (4 * c)
  have hβ : 0 < β := div_pos hb (by positivity)
  have hγ : 0 ≤ γ := by
    dsimp [γ]
    rw [sub_nonneg, div_le_iff₀ (by positivity : 0 < 4 * c)]
    nlinarith
  have ha : γ + c * β ^ 2 = a := by dsimp [γ, β]; field_simp; ring
  have he : 2 * c * β = b := by dsimp [β]; field_simp
  simpa only [ha, he] using insertionRow_no_common_root_quartic_square hβ hγ hc n

end ExponentialRows
end RealRooted
