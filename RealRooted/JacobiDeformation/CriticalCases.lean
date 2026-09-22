import RealRooted.JacobiDeformation.BaseProduct
import RealRooted.JacobiDeformation.CriticalBoundaryCondition
import RealRooted.JacobiDeformation.CriticalKernelBridge
import RealRooted.JacobiDeformation.ExceptionalKernelSign
import RealRooted.JacobiDeformation.ImageProductDoubleNodes
import RealRooted.JacobiDeformation.ImageProductDoubleRoot
import RealRooted.JacobiDeformation.OrdinaryKernelSign
import RealRooted.JacobiDeformation.RootKernelSign

/-!
# Critical signs for the actual Jacobi deformation

The two cases here are exhaustive at a root of the derivative of the
delta-zero image product: either the image product is nonzero, or the critical
point is a double image root.  Both branches retain the complete Jacobi node
family and all finite-kernel summands.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

private lemma mul_pos_of_div_pos {a b : ℝ} (h : 0 < a / b) : 0 < a * b := by
  rcases (div_pos_iff.mp h) with h | h
  · exact mul_pos h.1 h.2
  · exact mul_pos_of_neg_of_neg h.1 h.2

private lemma mul_pos_of_two_reference_products {a b c : ℝ}
    (hab : 0 < a * b) (hbc : 0 < b * c) : 0 < a * c := by
  rcases (mul_pos_iff.mp hab) with h | h <;>
    rcases (mul_pos_iff.mp hbc) with h' | h' <;> nlinarith

private lemma mul_neg_of_reference_products {a b c : ℝ}
    (hab : 0 < a * b) (hcb : c * b < 0) : a * c < 0 := by
  rcases (mul_pos_iff.mp hab) with h | h <;>
    rcases (mul_neg_iff.mp hcb) with h' | h' <;> nlinarith

private theorem eval_shiftedJacobiMonic_eq_node_product
    {m : ℕ} {α β x : ℝ} (t : Fin m → ℝ)
    (hnodes : shiftedJacobiMonic m α β =
      Finset.univ.prod (fun i : Fin m => (X : ℝ[X]) - C (t i))) :
    (shiftedJacobiMonic m α β).eval x =
      Finset.univ.prod (fun i : Fin m => x - t i) := by
  rw [hnodes, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp

/-- At a nonroot critical point of the delta-zero image product, the actual
positive-`δ` deformation has sign opposite to the second derivative. -/
theorem polynomial_eval_mul_imageProduct_secondDerivative_neg_of_nonroot
    {m : ℕ} (hm : 2 ≤ m) {δ c d U V xi : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (t : Fin m → ℝ) (ht : ∀ i, 0 < t i ∧ t i < 1)
    (hnodes : shiftedJacobiMonic m (c - 1) (d - 1) =
      Finset.univ.prod (fun i : Fin m => (X : ℝ[X]) - C (t i)))
    (hxi : xi < -(Real.sqrt U + Real.sqrt V) ^ 2)
    (himage : (imageProduct U V t).eval xi ≠ 0)
    (hderivative : (imageProduct U V t).derivative.eval xi = 0) :
    (polynomial m δ c d U V).eval xi *
        (imageProduct U V t).derivative.derivative.eval xi < 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by lia⟩
  let α := c - 1
  let β := d - 1
  let K := rawJacobiKernel (n + 2) δ α β
  obtain ⟨r, z, hr, hrz, hz, hprod, hcomp⟩ :=
    exists_interior_coordinates_of_lt_neg_sqrt_threshold hU hV hxi
  have hα : -1 < α := by dsimp only [α]; linarith
  have hβ : -1 < β := by dsimp only [β]; linarith
  have hboundary := imageProduct_critical_boundary_condition (n + 1) hα hβ
    (t := t) ht (by simpa [α, β] using hnodes)
    hprod hcomp himage hderivative
  have hkernel : 0 < K r z /
      ((shiftedJacobiMonic (n + 2) α β).eval r *
        (shiftedJacobiMonic (n + 2) α β).eval z) := by
    obtain ⟨hpr, hpz, hratio⟩ := by
      simpa [α, β] using hboundary
    by_cases hratio_ne :
        (shiftedJacobiMonic (n + 1) α β).eval r /
            (shiftedJacobiMonic (n + 2) α β).eval r ≠ 0
    · simpa only [K, rawJacobiKernel] using
        ordinaryJacobi_kernelWeight_sum_div_eval_top_pos hm hα hβ hδ hδ1
          hpr hpz hratio hratio_ne
    · have hprevr : (shiftedJacobiMonic (n + 1) α β).eval r = 0 := by
        calc
          _ = ((shiftedJacobiMonic (n + 1) α β).eval r /
              (shiftedJacobiMonic (n + 2) α β).eval r) *
                (shiftedJacobiMonic (n + 2) α β).eval r := by
                  exact (div_mul_cancel₀ _ hpr).symm
          _ = 0 := by rw [not_ne_iff.mp hratio_ne, zero_mul]
      have hratio_z :
          (shiftedJacobiMonic (n + 1) α β).eval z /
              (shiftedJacobiMonic (n + 2) α β).eval z = 0 := by
        rw [← hratio]
        exact not_ne_iff.mp hratio_ne
      have hprevz : (shiftedJacobiMonic (n + 1) α β).eval z = 0 := by
        calc
          _ = ((shiftedJacobiMonic (n + 1) α β).eval z /
              (shiftedJacobiMonic (n + 2) α β).eval z) *
                (shiftedJacobiMonic (n + 2) α β).eval z := by
                  exact (div_mul_cancel₀ _ hpz).symm
          _ = 0 := by rw [hratio_z, zero_mul]
      have hm3 : 3 ≤ n + 2 :=
        shiftedJacobiMonic_prev_two_roots_force_three hm hα hβ
        (by simpa only [Polynomial.IsRoot.def, show n + 2 - 1 = n + 1 by lia]
          using hprevr)
        (by simpa only [Polynomial.IsRoot.def, show n + 2 - 1 = n + 1 by lia]
          using hprevz) hrz.ne
      exact (by
        simpa only [K, rawJacobiKernel] using
          (exceptional_prev_root_kernel_sign hm3 hα hβ hδ hδ1
            (by simpa only [Polynomial.IsRoot.def, show n + 2 - 1 = n + 1 by lia]
              using hprevr)
            (by simpa only [Polynomial.IsRoot.def, show n + 2 - 1 = n + 1 by lia]
              using hprevz)).2.2)
  have hKtop : 0 < K r z *
      ((shiftedJacobiMonic (n + 2) α β).eval r *
        (shiftedJacobiMonic (n + 2) α β).eval z) :=
    mul_pos_of_div_pos hkernel
  have hcoord := imageProduct_coordinate_identity t ht hprod hcomp
  have hreval := eval_shiftedJacobiMonic_eq_node_product t hnodes (x := r)
  have hzeval := eval_shiftedJacobiMonic_eq_node_product t hnodes (x := z)
  change shiftedJacobiMonic (n + 2) α β = _ at hnodes
  change (shiftedJacobiMonic (n + 2) α β).eval r = _ at hreval
  change (shiftedJacobiMonic (n + 2) α β).eval z = _ at hzeval
  rw [← hreval, ← hzeval] at hcoord
  have hsign : (-1 : ℝ) ^ (n + 2) * (-1 : ℝ) ^ (n + 2) = 1 := by
    rw [← pow_add, show (n + 2) + (n + 2) = 2 * (n + 2) by lia, pow_mul]
    norm_num
  let P := Finset.univ.prod (fun i : Fin (n + 2) => t i * (1 - t i))
  have hxiNeg : xi < 0 := by
    nlinarith [sq_nonneg (Real.sqrt U + Real.sqrt V)]
  have hscale : 0 < (-1 : ℝ) ^ (n + 2) * xi ^ (n + 2) := by
    rw [← mul_pow]
    exact pow_pos (by linarith) (n + 2)
  have hP : 0 < P := by
    simpa only [P] using prod_node_mul_one_sub_pos t ht
  have hcoord' :
      ((-1 : ℝ) ^ (n + 2) * xi ^ (n + 2)) *
          ((shiftedJacobiMonic (n + 2) α β).eval r *
            (shiftedJacobiMonic (n + 2) α β).eval z) =
        P * (imageProduct U V t).eval xi := by
    calc
      _ = (-1 : ℝ) ^ (n + 2) *
          (xi ^ (n + 2) * (shiftedJacobiMonic (n + 2) α β).eval r *
            (shiftedJacobiMonic (n + 2) α β).eval z) := by ring
      _ = (-1 : ℝ) ^ (n + 2) *
          ((-1 : ℝ) ^ (n + 2) * P * (imageProduct U V t).eval xi) := by
            rw [hcoord]
      _ = _ := by rw [show (-1 : ℝ) ^ (n + 2) * ((-1 : ℝ) ^ (n + 2) * P *
          (imageProduct U V t).eval xi) =
            ((-1 : ℝ) ^ (n + 2) * (-1 : ℝ) ^ (n + 2)) * P *
              (imageProduct U V t).eval xi by ring, hsign, one_mul]
  have htopImage : 0 <
      ((shiftedJacobiMonic (n + 2) α β).eval r *
          (shiftedJacobiMonic (n + 2) α β).eval z) *
        (imageProduct U V t).eval xi := by
    have hright : 0 < P * ((imageProduct U V t).eval xi) ^ 2 :=
      mul_pos hP (sq_pos_of_ne_zero himage)
    have hleft : 0 < ((-1 : ℝ) ^ (n + 2) * xi ^ (n + 2)) *
        (((shiftedJacobiMonic (n + 2) α β).eval r *
            (shiftedJacobiMonic (n + 2) α β).eval z) *
          (imageProduct U V t).eval xi) := by
      calc
        _ = (((-1 : ℝ) ^ (n + 2) * xi ^ (n + 2)) *
              ((shiftedJacobiMonic (n + 2) α β).eval r *
                (shiftedJacobiMonic (n + 2) α β).eval z)) *
            (imageProduct U V t).eval xi := by ring
        _ = (P * (imageProduct U V t).eval xi) *
            (imageProduct U V t).eval xi := by rw [hcoord']
        _ = P * ((imageProduct U V t).eval xi) ^ 2 := by ring
        _ > 0 := hright
    exact pos_of_mul_pos_right hleft hscale.le
  have hKImage : 0 < K r z * (imageProduct U V t).eval xi :=
    mul_pos_of_two_reference_products hKtop htopImage
  have himageSecond :
      (imageProduct U V t).derivative.derivative.eval xi *
        (imageProduct U V t).eval xi < 0 := by
    have hstrict := deriv2_mul_lt_deriv_sq_at_non_root
      (imageProduct_splits U V t) (by rw [imageProduct_natDegree]; lia) himage
    rw [hderivative] at hstrict
    simpa using hstrict
  have hKSecond : K r z *
      (imageProduct U V t).derivative.derivative.eval xi < 0 :=
    mul_neg_of_reference_products hKImage himageSecond
  rw [polynomial_eval_eq_coordinateFactor_mul_rawJacobiKernel
    (n + 2) hc hd hprod hcomp]
  calc
    (((-1 : ℝ) ^ (n + 2) * xi ^ (n + 2) *
        shiftedJacobiMoment (c - 1) (d - 1) 0) * K r z) *
          (imageProduct U V t).derivative.derivative.eval xi =
      ((-1 : ℝ) ^ (n + 2) * xi ^ (n + 2) *
        shiftedJacobiMoment (c - 1) (d - 1) 0) *
          (K r z * (imageProduct U V t).derivative.derivative.eval xi) := by ring
    _ < 0 := mul_neg_of_pos_of_neg
      (coordinateFactor_pos (n + 2) hc hd hxiNeg) hKSecond

/-- At an inherited double root of the delta-zero image product, the actual
positive-`δ` deformation again has sign opposite to the second derivative. -/
theorem polynomial_eval_mul_imageProduct_secondDerivative_neg_of_doubleRoot
    {m : ℕ} (hm : 2 ≤ m) {δ c d U V xi : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (t : Fin m → ℝ) (htinj : Function.Injective t)
    (ht : ∀ i, 0 < t i ∧ t i < 1)
    (hnodes : shiftedJacobiMonic m (c - 1) (d - 1) =
      Finset.univ.prod (fun i : Fin m => (X : ℝ[X]) - C (t i)))
    (hroot : (imageProduct U V t).IsRoot xi)
    (hderivative : (imageProduct U V t).derivative.IsRoot xi) :
    (polynomial m δ c d U V).eval xi *
        (imageProduct U V t).derivative.derivative.eval xi < 0 := by
  let α := c - 1
  let β := d - 1
  let K := rawJacobiKernel m δ α β
  have hα : -1 < α := by dsimp only [α]; linarith
  have hβ : -1 < β := by dsimp only [β]; linarith
  obtain ⟨a, b, hab, hxi, hprod, hcomp⟩ :=
    exists_imageProduct_double_nodes hU hV t htinj ht hroot hderivative
  have hnodeRoot (i : Fin m) : (shiftedJacobiMonic m α β).IsRoot (t i) := by
    rw [Polynomial.IsRoot.def]
    change (shiftedJacobiMonic m (c - 1) (d - 1)).eval (t i) = 0
    rw [hnodes, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hkernel := rootJacobi_kernelWeight_sum_div_eval_prev_pos hm hα hβ hδ hδ1
    (hnodeRoot a) (hnodeRoot b)
  have hKprev : 0 < K (t a) (t b) *
      ((shiftedJacobiMonic (m - 1) α β).eval (t a) *
        (shiftedJacobiMonic (m - 1) α β).eval (t b)) := by
    apply mul_pos_of_div_pos
    simpa only [K, rawJacobiKernel] using hkernel
  have hlowering := shiftedJacobiMonic_lowering m (by lia) hα hβ
  have hBpos := shiftedJacobiMonic_lowering_subdiag_pos m (by lia) hα hβ
  have hsame (i : Fin m) : 0 <
      (shiftedJacobiMonic m α β).derivative.eval (t i) *
        (shiftedJacobiMonic (m - 1) α β).eval (t i) := by
    have heval := congrArg (fun p : ℝ[X] => p.eval (t i)) hlowering
    have hqzero : (shiftedJacobiMonic m α β).eval (t i) = 0 :=
      hnodeRoot i
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_neg,
      Polynomial.eval_C, hqzero, mul_zero] at heval
    have heval' : t i * (1 - t i) *
        (shiftedJacobiMonic m α β).derivative.eval (t i) =
      ((2 * (m : ℝ) + (α + β + 2) - 1) * shiftedJacobiSubdiag m α β) *
        (shiftedJacobiMonic (m - 1) α β).eval (t i) := by
      simpa only [zero_add] using heval
    have hderne := (shiftedJacobiMonic_hasSimpleRoots m hα hβ).eval_derivative_ne_zero
      (hnodeRoot i)
    have hleft : 0 < t i * (1 - t i) *
        (shiftedJacobiMonic m α β).derivative.eval (t i) ^ 2 := by
      exact mul_pos (mul_pos (ht i).1 (sub_pos.mpr (ht i).2))
        (sq_pos_of_ne_zero hderne)
    have hright : 0 <
        ((2 * (m : ℝ) + (α + β + 2) - 1) * shiftedJacobiSubdiag m α β) *
          ((shiftedJacobiMonic m α β).derivative.eval (t i) *
            (shiftedJacobiMonic (m - 1) α β).eval (t i)) := by
      rw [show
        ((2 * (m : ℝ) + (α + β + 2) - 1) * shiftedJacobiSubdiag m α β) *
            ((shiftedJacobiMonic m α β).derivative.eval (t i) *
              (shiftedJacobiMonic (m - 1) α β).eval (t i)) =
          (t i * (1 - t i) *
              (shiftedJacobiMonic m α β).derivative.eval (t i)) *
            (shiftedJacobiMonic m α β).derivative.eval (t i) by
        rw [heval']
        ring]
      simpa [pow_two, mul_assoc] using hleft
    exact pos_of_mul_pos_right hright hBpos.le
  have hprevDer : 0 <
      ((shiftedJacobiMonic (m - 1) α β).eval (t a) *
          (shiftedJacobiMonic (m - 1) α β).eval (t b)) *
        ((shiftedJacobiMonic m α β).derivative.eval (t a) *
          (shiftedJacobiMonic m α β).derivative.eval (t b)) := by
    have := mul_pos (hsame a) (hsame b)
    nlinarith
  have hdouble := imageProduct_double_root_sign t U V xi htinj
    (fun i => (ht i).1) (fun i => (ht i).2) a b hab hxi hprod hcomp
  change shiftedJacobiMonic m α β = _ at hnodes
  rw [← hnodes] at hdouble
  have hKDer : 0 < K (t a) (t b) *
      ((shiftedJacobiMonic m α β).derivative.eval (t a) *
        (shiftedJacobiMonic m α β).derivative.eval (t b)) :=
    mul_pos_of_two_reference_products hKprev hprevDer
  have hKSecond : K (t a) (t b) *
      (imageProduct U V t).derivative.derivative.eval xi < 0 := by
    apply mul_neg_of_reference_products hKDer
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hdouble
  have heval := polynomial_eval_eq_coordinateFactor_mul_rawJacobiKernel
    (δ := δ) m hc hd hprod hcomp
  rw [heval]
  calc
    (((-1 : ℝ) ^ m * xi ^ m *
        shiftedJacobiMoment (c - 1) (d - 1) 0) * K (t a) (t b)) *
          (imageProduct U V t).derivative.derivative.eval xi =
      ((-1 : ℝ) ^ m * xi ^ m *
        shiftedJacobiMoment (c - 1) (d - 1) 0) *
          (K (t a) (t b) *
            (imageProduct U V t).derivative.derivative.eval xi) := by ring
    _ < 0 := mul_neg_of_pos_of_neg (coordinateFactor_pos m hc hd hxi) hKSecond

/-- The complete actual critical sign, with the nonroot and inherited-double
branches discharged internally. -/
theorem polynomial_eval_mul_imageProduct_secondDerivative_neg
    {m : ℕ} (hm : 2 ≤ m) {δ c d U V xi : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (t : Fin m → ℝ) (htinj : Function.Injective t)
    (ht : ∀ i, 0 < t i ∧ t i < 1)
    (hnodes : shiftedJacobiMonic m (c - 1) (d - 1) =
      Finset.univ.prod (fun i : Fin m => (X : ℝ[X]) - C (t i)))
    (hxi : xi < -(Real.sqrt U + Real.sqrt V) ^ 2)
    (hderivative : (imageProduct U V t).derivative.IsRoot xi) :
    (polynomial m δ c d U V).eval xi *
        (imageProduct U V t).derivative.derivative.eval xi < 0 := by
  by_cases himage : (imageProduct U V t).eval xi = 0
  · exact polynomial_eval_mul_imageProduct_secondDerivative_neg_of_doubleRoot
      hm hc hd hU hV hδ hδ1 t htinj ht hnodes
        (by simpa only [Polynomial.IsRoot.def] using himage) hderivative
  · apply polynomial_eval_mul_imageProduct_secondDerivative_neg_of_nonroot
      hm hc hd hU hV hδ hδ1 t ht hnodes hxi himage
    simpa only [Polynomial.IsRoot.def] using hderivative

end RealRooted.JacobiDeformation
