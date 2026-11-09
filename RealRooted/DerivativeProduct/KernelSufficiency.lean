module

public import RealRooted.DerivativeProduct.Associative
public import RealRooted.RootLocation.Basic
public import RealRooted.MultiplierSequence.Infinite
import RealRooted.BorceaBranden.Applications.ComplexDiagonalRootLocation
import RealRooted.DerivativeProduct.KernelWeyl
import RealRooted.MultiplierSequence.InvPochhammer
import Mathlib.Tactic

/-!
# Sufficiency in the fixed-factor criterion for derivative products

Let `w` be a quadratic weight with nonnegative `X ^ 2`-coefficient `A` and let `γ` be a positive
PF multiplier sequence with `γ 0 = 1`.  For a nonzero real-rooted `f` all of whose roots `r`
satisfy `w r ≤ 0`, the map `g ↦ ∑ k, γ k / k! * w ^ k * f ^ (k) * g ^ (k)` sends nonzero
real-rooted polynomials to real-rooted polynomials.

The proof applies the finite-order Weyl-symbol theorem
(`RealRooted.sum_mul_iterate_derivative_eq_zero_or_splits`).  The signed symbol is
`∑ j, γ j * (hasseDeriv j f) (x) * (-w (x) y) ^ j`, which is the PF multiplier `γ` applied to the
Taylor polynomial `s ↦ f (x + w x * s)`.  Its roots `s = (r - x) / w x` lie in the closed upper
half-plane exactly when `w r ≤ 0` (this uses `A ≥ 0`), and a PF multiplier preserves that root
location (`IsPFMultiplierSequence.roots_im_nonneg_complexDiagonal`).

For the associative family `assocProduct` and the diamond family `betaProduct` the sequence is
`1 / (β)_k` up to a geometric factor, a PF multiplier sequence whose Jensen polynomials are
Laguerre polynomials.  This is the sufficiency direction of Theorem 2 in issue #2369 and of the
kernel characterization in issue #2363, after P. Brändén, *On linear transformations preserving
the Pólya frequency property*, Theorem 3.11 (arXiv:math/0403364).
-/

public section

open Polynomial Set

namespace RealRooted

noncomputable section

namespace DerivativeProduct

set_option linter.flexible false in
/-- The root location behind the sufficiency criterion: if `w r ≤ 0` for a real `r`, `w` is a
quadratic with nonnegative leading coefficient, `x` lies in the open upper half-plane and
`w x * z = r - x`, then `z` lies in the closed upper half-plane. -/
private theorem im_nonneg_of_weight_mul_eq {W : ℝ[X]} (hW : W.natDegree ≤ 2)
    (hA : 0 ≤ W.coeff 2) {r : ℝ} (hr : W.eval r ≤ 0) {x z : ℂ} (hx : 0 < x.im)
    (hz : (complexify W).eval x * z = (r : ℂ) - x) : 0 ≤ z.im := by
  have hWx : (complexify W).eval x =
      (W.coeff 0 : ℂ) + (W.coeff 1 : ℂ) * x + (W.coeff 2 : ℂ) * x ^ 2 := by
    rw [complexify, eval_map, eval₂_eq_sum_range' _ (show W.natDegree < 3 by lia)]
    simp [Finset.sum_range_succ]
  have hWr : W.eval r = W.coeff 0 + W.coeff 1 * r + W.coeff 2 * r ^ 2 := by
    rw [eval_eq_sum_range' (show W.natDegree < 3 by lia)]
    simp [Finset.sum_range_succ]
  rw [hWx] at hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp [pow_two] at hre him
  set a := x.re
  set b := x.im
  set c0 := W.coeff 0
  set c1 := W.coeff 1
  set c2 := W.coeff 2
  set p := z.re
  set s := z.im
  set X1 := c0 + c1 * a + c2 * (a * a - b * b) with hX1
  set Y1 := c1 * b + c2 * (a * b + b * a) with hY1
  have h1 : X1 * p - Y1 * s = r - a := by rw [hX1, hY1]; linear_combination hre
  have h2 : X1 * s + Y1 * p = -b := by rw [hX1, hY1]; linear_combination him
  have hkey : s * (X1 ^ 2 + Y1 ^ 2) = -b * X1 - Y1 * (r - a) := by
    linear_combination X1 * h2 - Y1 * h1
  have hpos : 0 < X1 ^ 2 + Y1 ^ 2 := by
    by_contra hnot
    have hX : X1 = 0 := by nlinarith [sq_nonneg X1, sq_nonneg Y1]
    have hY : Y1 = 0 := by nlinarith [sq_nonneg X1, sq_nonneg Y1]
    rw [hX, hY] at h2
    linarith
  have hrhs : 0 ≤ -b * X1 - Y1 * (r - a) := by
    have : -b * X1 - Y1 * (r - a) =
        b * (-(c0 + c1 * r + c2 * r ^ 2) + c2 * ((a - r) ^ 2 + b ^ 2)) := by
      rw [hX1, hY1]; ring
    rw [this]
    have hb : 0 < b := hx
    have h3 : 0 ≤ -(c0 + c1 * r + c2 * r ^ 2) := by linarith
    positivity
  by_contra hneg
  push Not at hneg
  nlinarith [mul_neg_of_neg_of_pos hneg hpos]

open BorceaBranden in
/-- The signed Weyl symbol of the fixed-factor operator of a derivative product does not vanish in
the product of two open upper half-planes. -/
private theorem symbol_ne_zero {γ : ℕ → ℝ} (hγ : IsPFMultiplierSequence γ) (hγ0 : ∀ n, 0 < γ n)
    {W : ℝ[X]} (hW : W.natDegree ≤ 2) (hA : 0 ≤ W.coeff 2) {f : ℝ[X]}
    (hf : IsRealRootedIn {r | W.eval r ≤ 0} f) {x y : ℂ} (hx : 0 < x.im) (hy : 0 < y.im) :
    ∑ j : Fin (f.natDegree + 1),
      (complexify (C (γ j / ((j : ℕ).factorial : ℝ)) * W ^ (j : ℕ) * (derivative^[j]) f)).eval x *
        (-y) ^ (j : ℕ) ≠ 0 := by
  have hγne : ∀ n, γ n ≠ 0 := fun n ↦ (hγ0 n).ne'
  set F := complexify f with hF
  set Wx := (complexify W).eval x with hWx
  set P : ℂ[X] := (taylor x F).comp (C Wx * X) with hP
  have hFx : F.eval x ≠ 0 :=
    eval_complexify_ne_zero_of_splits_of_im_pos hf.splits hf.ne_zero hx
  have hP0 : P ≠ 0 := by
    intro h
    have h0 : P.eval 0 = F.eval x := by simp [hP, taylor_eval]
    rw [h, eval_zero] at h0
    exact hFx h0.symm
  have hFnat : F.natDegree = f.natDegree :=
    natDegree_map_eq_of_injective Complex.ofRealHom.injective f
  have hPnat : P.natDegree ≤ f.natDegree := by
    have h1 : (C Wx * X).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
    calc P.natDegree ≤ (taylor x F).natDegree * (C Wx * X).natDegree := natDegree_comp_le
      _ ≤ f.natDegree * 1 := by rw [natDegree_taylor, hFnat]; exact Nat.mul_le_mul_left _ h1
      _ = f.natDegree := mul_one _
  have hroots : ∀ z ∈ P.roots, 0 ≤ z.im := by
    intro z hz
    have hroot : P.eval z = 0 := (mem_roots hP0).mp hz
    rw [hP, eval_comp, eval_mul, eval_C, eval_X, taylor_eval, hF,
      eval_complexify_eq_prod hf.splits] at hroot
    rcases mul_eq_zero.mp hroot with h | h
    · exact absurd (by simpa using h) (leadingCoeff_ne_zero.mpr hf.ne_zero)
    · obtain ⟨r, hr, hrz⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h)
      refine im_nonneg_of_weight_mul_eq hW hA (hf.mem_of_mem_roots hr) hx ?_
      linear_combination hrz
  have hD := IsPFMultiplierSequence.roots_im_nonneg_complexDiagonal hγ hγne hP0 hroots
  have hD0 := realDiagonalOperator_ne_zero hγne hP0
  have hDnat : (realDiagonalOperator γ P).natDegree < f.natDegree + 1 :=
    Nat.lt_succ_of_le ((natDegree_realDiagonalOperator_le γ P).trans hPnat)
  have hterm : ∀ j : ℕ,
      (complexify (C (γ j / (j.factorial : ℝ)) * W ^ j * (derivative^[j]) f)).eval x *
        (-y) ^ j = (realDiagonalOperator γ P).coeff j * (-y) ^ j := by
    intro j
    have hd : (derivative^[j]) F = C (j.factorial : ℂ) * hasseDeriv j F := by
      have := congrFun (factorial_smul_hasseDeriv (R := ℂ) (k := j)) F
      rw [LinearMap.smul_apply, nsmul_eq_mul] at this
      rw [← this]
      simp
    have hfact : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hc : complexify (C (γ j / (j.factorial : ℝ)) * W ^ j * (derivative^[j]) f) =
        C ((γ j : ℂ) / (j.factorial : ℂ)) * (complexify W) ^ j * (derivative^[j]) F := by
      rw [hF, ← complexify_iterate_derivative]
      simp [complexify]
    rw [hc, coeff_realDiagonalOperator, hP, comp_C_mul_X_coeff, taylor_coeff, hd]
    simp only [eval_mul, eval_C, eval_pow, hWx]
    field_simp
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ (complexify (C (γ j / (j.factorial : ℝ)) * W ^ j *
    (derivative^[j]) f)).eval x * (-y) ^ j) (f.natDegree + 1)]
  simp only [hterm]
  rw [← eval_eq_sum_range' hDnat]
  intro h
  have hmem : -y ∈ (realDiagonalOperator γ P).roots := (mem_roots hD0).mpr h
  have := hD _ hmem
  simp only [Complex.neg_im] at this
  linarith

end DerivativeProduct

open DerivativeProduct

/-- **Fixed-factor sufficiency for derivative products.**  Let `w` be a quadratic weight with
nonnegative `X ^ 2`-coefficient and `γ` a positive PF multiplier sequence with `γ 0 = 1`.  If `f`
is real-rooted with every root in `{r | w r ≤ 0}`, then
`g ↦ ∑ k, γ k / k! * w ^ k * f ^ (k) * g ^ (k)` sends nonzero real-rooted polynomials to nonzero
real-rooted polynomials.  (Brändén, *On linear transformations preserving the Pólya frequency
property*, Thm 3.11; the Weyl-symbol proof is the finite-order case of Borcea–Brändén.) -/
theorem derivProduct_isRealRootedIn_univ {γ : ℕ → ℝ} (hγ : IsPFMultiplierSequence γ)
    (hγ0 : ∀ n, 0 < γ n) (hγ1 : γ 0 = 1) {W : ℝ[X]} (hW : W.natDegree ≤ 2)
    (hA : 0 ≤ W.coeff 2) {f g : ℝ[X]} (hf : IsRealRootedIn {r | W.eval r ≤ 0} f)
    (hg : IsRealRootedIn univ g) :
    IsRealRootedIn univ (derivProduct W (fun k ↦ γ k / (k.factorial : ℝ)) f g) := by
  have hc0 : (fun k ↦ γ k / (k.factorial : ℝ)) 0 = 1 := by simp [hγ1]
  have hc : ∀ k, 0 ≤ (fun k ↦ γ k / (k.factorial : ℝ)) k := fun k ↦ by
    have := hγ0 k
    positivity
  rw [IsRealRootedIn.univ_iff] at hg ⊢
  have hne := derivProduct_ne_zero hW hA hc0 hc hf.ne_zero hg.1
  refine ⟨hne, ?_⟩
  have hout := sum_mul_iterate_derivative_eq_zero_or_splits (m := f.natDegree)
    (fun j ↦ C (γ j / ((j : ℕ).factorial : ℝ)) * W ^ (j : ℕ) * (derivative^[j]) f)
    (fun x y hx hy ↦ symbol_ne_zero hγ hγ0 hW hA hf hx hy) hg.1 hg.2
  have hsum : ∑ j : Fin (f.natDegree + 1),
      C (γ j / ((j : ℕ).factorial : ℝ)) * W ^ (j : ℕ) * (derivative^[j]) f *
        (derivative^[j]) g = derivProduct W (fun k ↦ γ k / (k.factorial : ℝ)) f g := by
    rw [derivProduct]
    exact Fin.sum_univ_eq_sum_range (fun k ↦ C (γ k / (k.factorial : ℝ)) * W ^ k *
      (derivative^[k]) f * (derivative^[k]) g) (f.natDegree + 1)
  rw [hsum] at hout
  exact hout.resolve_left hne

/-- The roots of the diamond weight `X * (X + 1)` where it is nonpositive form `[-1, 0]`. -/
theorem setOf_eval_X_mul_X_add_one_nonpos :
    {r : ℝ | (X * (X + 1) : ℝ[X]).eval r ≤ 0} = Icc (-1) 0 := by
  ext r
  simp only [mem_ofPred_eq, eval_mul, eval_X, eval_add, eval_one, mem_Icc]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (r + 1 / 2)]
  · rintro ⟨h1, h2⟩
    nlinarith

/-- **Diamond family, sufficiency.**  For `β > 0`, a kernel `f` rooted in `[-1, 0]` acts on
nonzero real-rooted polynomials by `g ↦ f *_β g`, producing real-rooted polynomials.  The case
`β = 1` is the diamond product.  The proof uses that `1 / (β)_k` is a PF multiplier sequence
(its Jensen polynomials are Laguerre polynomials). -/
theorem betaProduct_isRealRootedIn_univ {β : ℝ} (hβ : 0 < β) {f g : ℝ[X]}
    (hf : IsRealRootedIn (Icc (-1) 0) f) (hg : IsRealRootedIn univ g) :
    IsRealRootedIn univ (betaProduct β f g) := by
  have hcoeff : betaCoeff β = fun k ↦ ((ascPochhammer ℝ k).eval β)⁻¹ / (k.factorial : ℝ) := by
    funext k
    rw [betaCoeff, one_div, mul_inv, mul_comm, div_eq_mul_inv]
  rw [betaProduct, hcoeff]
  refine derivProduct_isRealRootedIn_univ (isPFMultiplierSequence_inv_ascPochhammer hβ)
    (fun n ↦ inv_pos.mpr (ascPochhammer_pos n β hβ)) (by simp) natDegree_X_mul_X_add_one_le
    (by rw [coeff_two_X_mul_X_add_one]; exact zero_le_one) ?_ hg
  rwa [setOf_eval_X_mul_X_add_one_nonpos]

/-- **Associative family, sufficiency.**  For `a > 0` and a quadratic weight `w` with nonnegative
`X ^ 2`-coefficient, a kernel `f` real-rooted with `w ≤ 0` at all its roots acts on nonzero
real-rooted polynomials by `g ↦ assocProduct a w f g`, producing real-rooted polynomials.  This is
the sufficiency direction of Theorem 2 of issue #2369. -/
theorem assocProduct_isRealRootedIn_univ {a : ℝ} (ha : 0 < a) {w : ℝ[X]} (hw : w.natDegree ≤ 2)
    (hA : 0 ≤ w.coeff 2) {f g : ℝ[X]} (hf : IsRealRootedIn {r | w.eval r ≤ 0} f)
    (hg : IsRealRootedIn univ g) :
    IsRealRootedIn univ (assocProduct a w f g) := by
  rcases hA.eq_or_lt with hA0 | hApos
  · -- `A = 0`: the product is `derivProduct (C a * w)` with the coefficients `1 / k!`
    have hcoeff : assocCoeff a (w.coeff 2) = fun k ↦ a ^ k * ((1 : ℝ) / (k.factorial : ℝ)) := by
      funext k
      simp [assocCoeff, ← hA0, div_eq_mul_inv]
    rw [assocProduct, hcoeff, ← derivProduct_C_mul_weight]
    refine derivProduct_isRealRootedIn_univ (γ := fun _ ↦ 1) isPFMultiplierSequence_one_sequence
      (fun _ ↦ one_pos) rfl ((natDegree_C_mul_le _ _).trans hw)
      (by rw [coeff_C_mul, ← hA0, mul_zero]) ?_ hg
    refine hf.mono fun r hr ↦ ?_
    simp only [mem_ofPred_eq, eval_mul, eval_C] at hr ⊢
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hr
  · -- `A > 0`: the product is `derivProduct (A⁻¹ • w)` with the coefficients `1 / (k! * (β)_k)`
    have hAne : w.coeff 2 ≠ 0 := hApos.ne'
    have hβ : 0 < (a * w.coeff 2)⁻¹ := inv_pos.mpr (mul_pos ha hApos)
    have hcoeff : assocCoeff a (w.coeff 2) = fun k ↦ (w.coeff 2)⁻¹ ^ k *
        (((ascPochhammer ℝ k).eval (a * w.coeff 2)⁻¹)⁻¹ / (k.factorial : ℝ)) := by
      funext k
      have h1 := pow_mul_assocCoeff a (w.coeff 2) k
      rw [assocCoeff_one_eq_betaCoeff (mul_pos ha hApos), betaCoeff] at h1
      have hk : w.coeff 2 ^ k ≠ 0 := pow_ne_zero _ hAne
      have h2 : assocCoeff a (w.coeff 2) k =
          (w.coeff 2 ^ k)⁻¹ * (w.coeff 2 ^ k * assocCoeff a (w.coeff 2) k) := by field_simp
      rw [h2, h1, inv_pow, one_div, mul_inv, div_eq_mul_inv, mul_comm ((k.factorial : ℝ)⁻¹)]
    rw [assocProduct, hcoeff, ← derivProduct_C_mul_weight]
    refine derivProduct_isRealRootedIn_univ (isPFMultiplierSequence_inv_ascPochhammer hβ)
      (fun n ↦ inv_pos.mpr (ascPochhammer_pos n _ hβ)) (by simp)
      ((natDegree_C_mul_le _ _).trans hw)
      (by rw [coeff_C_mul, inv_mul_cancel₀ hAne]; exact zero_le_one) ?_ hg
    refine hf.mono fun r hr ↦ ?_
    simp only [mem_ofPred_eq, eval_mul, eval_C] at hr ⊢
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hApos.le) hr


end

end RealRooted
