import RealRooted.FactorialCompression.Compression
import RealRooted.FactorialCompression.KernelGeometry
import RealRooted.FactorialCompression.SchurSzego

/-!
# Degree-changing factorial compression

The main factorial-compression step, including the constant/linear boundary.
The public theorem is stated with RealRooted's native `StrictInterl` API and
records exact degrees, simple strictly negative roots, and exclusion of common
roots.
-/

open Polynomial RealRooted

noncomputable section

namespace RealRooted.FactorialCompression

private theorem ratio_sum_neg {r u v w : ℝ} (hr : r < 0)
    (hv : 0 < v / u) (hw : w / u < 0) :
    (w + r * v) / u < 0 := by
  rw [add_div, mul_div_assoc]
  exact add_neg hw (mul_neg_of_neg_of_pos hr hv)

/-- The explicit positive constant/negative linear root convention in (1.2). -/
private theorem constant_linear_geometry {c b d : ℝ} (hc : 0 < c)
    (hb : 0 < b) (hd : 0 < d) :
    (C c : ℝ[X]).natDegree = 0 ∧
    (C b + C d * X : ℝ[X]).natDegree = 1 ∧
    SimpleNegativeRoots (C c) ∧
    SimpleNegativeRoots (C b + C d * X) ∧
    StrictRootInterl (C c) (C b + C d * X) := by
  let g : ℝ[X] := C b + C d * X
  have hfactor : g = C d * (X - C (-b / d)) := by
    dsimp [g]
    simp only [mul_sub, ← C_mul]
    rw [show d * (-b / d) = -b by field_simp]
    simp
    ring
  have hgdegree : g.natDegree = 1 := by
    rw [hfactor, natDegree_C_mul hd.ne', natDegree_X_sub_C]
  have hgroots : g.roots = {-b / d} := by
    rw [hfactor, roots_C_mul _ hd.ne', roots_X_sub_C]
  have hgpos : 0 < g.leadingCoeff := by
    rw [← coeff_natDegree, hgdegree]
    simpa [g] using hd
  have hg : SimpleNegativeRoots g := by
    refine ⟨?_, Splits.of_natDegree_eq_one hgdegree, ?_, ?_⟩
    · intro hz
      simp [hz] at hgdegree
    · simp [hgroots]
    · intro r hr
      simp only [hgroots, Multiset.mem_singleton] at hr
      subst r
      exact div_neg_of_neg_of_pos (neg_neg_of_pos hb) hd
  have hf : SimpleNegativeRoots (C c : ℝ[X]) := by
    refine ⟨?_, Splits.C c, ?_, ?_⟩
    · simpa using hc.ne'
    · simp
    · simp
  refine ⟨by simp, hgdegree, hf, hg, ?_⟩
  refine ⟨by simpa using hc, hgpos, hf.2.1, hg.2.1,
    [], [-b / d], by simp, by simp, by simp, ?_,
    Or.inl ⟨by simp, True.intro⟩⟩
  simpa [g] using hgroots.symm

/-- Exact coefficient computation in the N=1, ell=0 boundary case.
No information about a numerical instance is used. -/
private theorem boundary_compressions (a : ℝ) (p : ℝ[X]) :
    compression 1 0 p = C (p.coeff 0) ∧
    compression 2 0 (nextPolynomial a p) =
      C (a * p.coeff 0) + C (p.coeff 0 + (a + 1) * p.coeff 1) * X := by
  constructor
  · simp [compression, mu, Finset.sum_range_succ]
  · simp [compression, mu, Finset.sum_range_succ, nextPolynomial,
      add_mul, coeff_derivative]
    ring

/-- The m=1 case of Theorem 1.1, for every real a>0 and degree-one p. -/
private theorem factorial_compression_boundary {a : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hpdegree : p.natDegree = 1) (hpsplit : p.Splits)
    (hppos : 0 < p.leadingCoeff) (hproots : ∀ r ∈ p.roots, r < 0) :
    (compression 1 0 p).natDegree = 0 ∧
    (compression 2 0 (nextPolynomial a p)).natDegree = 1 ∧
    SimpleNegativeRoots (compression 1 0 p) ∧
    SimpleNegativeRoots (compression 2 0 (nextPolynomial a p)) ∧
    StrictRootInterl (compression 1 0 p)
      (compression 2 0 (nextPolynomial a p)) := by
  have hp0 := coeff_zero_pos_of_negativeRoots hpsplit hppos hproots
  have hp1 : 0 < p.coeff 1 := by
    simpa only [← hpdegree, coeff_natDegree] using hppos
  rw [(boundary_compressions a p).1, (boundary_compressions a p).2]
  exact constant_linear_geometry hp0 (mul_pos ha hp0)
    (add_pos hp0 (mul_pos (by linarith) hp1))

/-- Factorial compression, for arbitrary N >= 1, 0 <= ell <= N and a > 0.
Splits makes "all zeros negative" refer to all N roots, not merely the
possibly empty list of real roots. No simplicity assumption is imposed on p. -/
private theorem compression_nextPolynomial_strictRootGeometry {N ell : ℕ} {a : ℝ} {p : ℝ[X]}
    (hN : 1 ≤ N) (hell : ell ≤ N) (ha : 0 < a)
    (hpdegree : p.natDegree = N) (hpsplit : p.Splits)
    (hppos : 0 < p.leadingCoeff) (hproots : ∀ r ∈ p.roots, r < 0) :
    (compression N ell p).natDegree = (N + ell) / 2 ∧
    (compression (N + 1) ell (nextPolynomial a p)).natDegree = (N + ell + 1) / 2 ∧
    SimpleNegativeRoots (compression N ell p) ∧
    SimpleNegativeRoots (compression (N + 1) ell (nextPolynomial a p)) ∧
    StrictRootInterl (compression N ell p)
      (compression (N + 1) ell (nextPolynomial a p)) := by
  by_cases hmone : N + ell = 1
  · have hN1 : N = 1 := by lia
    have hell0 : ell = 0 := by lia
    have hb := factorial_compression_boundary ha
      (by simpa only [hN1] using hpdegree) hpsplit hppos hproots
    simpa [hN1, hell0] using hb
  have hm : 2 ≤ N + ell := by lia
  let U := schurSzegoComp N p (h (N + ell))
  let V := schurSzegoComp N p (h (N + ell - 1))
  let W := schurSzegoComp N p (kernel N ell a)
  have hUbound : (h (N + ell)).natDegree ≤ N := by rw [h_natDegree]; lia
  have hWbound : (kernel N ell a).natDegree ≤ N := by
    rw [kernel_natDegree N ell a hN hell ha]
    lia
  have hkernel := kernel_strictRootGeometry N ell a hN hell ha hm
  have hU : SimpleNegativeRoots U := schurSzegoComp_simpleNegativeRoots_of_negativeRoots
    hpdegree hpsplit hppos hproots hUbound (h_simple_negative _ hm) (h_pos_leading _)
  have hW : SimpleNegativeRoots W := schurSzegoComp_simpleNegativeRoots_of_negativeRoots
    hpdegree hpsplit hppos hproots hWbound
    hkernel.1 (kernel_pos_leading N ell a hN hell ha)
  have hUW : StrictRootInterl U W := schurSzegoComp_strictRootInterl_of_negativeRoots
    hN hpdegree hpsplit hppos hproots hUbound hWbound
    hkernel.2 (h_simple_negative _ hm).2.2.2 hkernel.1.2.2.2
  have hUd : U.natDegree = (N + ell) / 2 := by
    rw [schurSzegoComp_natDegree_of_negativeRoots hpdegree hpsplit hppos hproots hUbound
      (h_ne_zero _), h_natDegree]
  have hWd : W.natDegree = (N + ell + 1) / 2 := by
    rw [schurSzegoComp_natDegree_of_negativeRoots hpdegree hpsplit hppos hproots hWbound
      (kernel_ne_zero N ell a hN hell ha), kernel_natDegree N ell a hN hell ha]
  have hVd : V.natDegree = (N + ell - 1) / 2 := by
    rw [schurSzegoComp_natDegree_of_negativeRoots hpdegree hpsplit hppos hproots
      (by rw [h_natDegree]; lia) (h_ne_zero _), h_natDegree]
  have hVnonneg : HasNonnegCoeffs V := by
    intro k
    dsimp [V]
    rw [coeff_schurSzegoComp]
    split_ifs with hk
    · exact div_nonneg (mul_nonneg
        ((isPFPolynomial_of_negativeRoots hpsplit hppos hproots).hasNonnegCoeffs k)
        (h_nonneg _ k)) (by positivity)
    · exact le_rfl
  have hWnonneg : HasNonnegCoeffs W :=
    (isPFPolynomial_of_negativeRoots hW.2.1 hUW.2.1 hW.2.2.2).hasNonnegCoeffs
  have hGnonneg : HasNonnegCoeffs (W + X * V) :=
    hWnonneg.add (hasNonnegCoeffs_X.mul hVnonneg)
  have hGzero : 0 < (W + X * V).coeff 0 := by
    simpa [W] using schurSzegoComp_coeff_zero_pos
      (coeff_zero_pos_of_negativeRoots hpsplit hppos hproots)
      (kernel_coeff_pos N ell a 0 hN hell ha (by lia))
  have hGd : (W + X * V).natDegree = (N + ell + 1) / 2 := by
    apply Nat.le_antisymm
    · apply (natDegree_add_le W (X * V)).trans
      apply max_le hWd.le
      have hv : (X * V).natDegree ≤ (X : ℝ[X]).natDegree + V.natDegree :=
        natDegree_mul_le
      rw [natDegree_X, hVd] at hv
      lia
    · apply le_natDegree_of_ne_zero
      apply ne_of_gt
      have hwc : 0 < W.coeff ((N + ell + 1) / 2) := by
        rw [← hWd, coeff_natDegree]
        exact hUW.2.1
      exact lt_of_lt_of_le hwc (by
        rw [coeff_add]
        exact le_add_of_nonneg_right ((hasNonnegCoeffs_X.mul hVnonneg) _))
  have hGpos : 0 < (W + X * V).leadingCoeff :=
    hGnonneg.pos_leadingCoeff (by
      intro hz
      simp [hz] at hGzero)
  have hVidentity : V = U - C (2 / ((N + ell : ℕ) : ℝ)) * (X * U.derivative) :=
    filtered_h_previous_derivative N p (N + ell) (by lia)
  have hresult : SimpleNegativeRoots (W + X * V) ∧
      StrictRootInterl U (W + X * V) := by
    apply root_sign_criterion hU hUW.1 (by rw [hUd]; lia)
      hGnonneg hGzero hGpos (by rw [hGd, hUd]; lia)
    intro r hr
    have hrneg : r < 0 := hU.2.2.2 r ((mem_roots hU.1).mpr hr)
    have hder : U.derivative.eval r ≠ 0 := hU.hasSimpleRoots.eval_derivative_ne_zero hr
    have heval : V.eval r = -(2 / ((N + ell : ℕ) : ℝ)) * r * U.derivative.eval r := by
      rw [hVidentity]
      simp [hr.eq_zero]
      ring
    have hratio : 0 < V.eval r / U.derivative.eval r := by
      rw [heval, mul_div_cancel_right₀ _ hder]
      exact mul_pos_of_neg_of_neg (neg_neg_of_pos (by positivity)) hrneg
    simpa using ratio_sum_neg hrneg hratio (hUW.leftRootRatio_neg hr)
  have hscale1 : 0 < (Nat.factorial N : ℝ) / (Nat.factorial (N + ell) : ℝ) := by
    positivity
  have hscale2 : 0 < (Nat.factorial N : ℝ) / (Nat.factorial (N + ell - 1) : ℝ) := by
    positivity
  rw [compression_common_kernel, compression_nextPolynomial N ell a p hN hpdegree.le]
  refine ⟨?_, ?_, hU.C_mul hscale1.ne', hresult.1.C_mul hscale2.ne', ?_⟩
  · rw [natDegree_C_mul hscale1.ne']
    exact hUd
  · rw [natDegree_C_mul hscale2.ne']
    exact hGd
  · exact hresult.2.C_mul hscale1 hscale2

/-- General factorial compression: exact degrees, positive leading
coefficients, simple strictly negative roots, native strict interlacing, and no
common root.  Repeated roots are allowed in the input polynomial. -/
theorem compression_nextPolynomial_geometry_of_roots_neg {N ell : ℕ} {a : ℝ} {p : ℝ[X]}
    (hN : 1 ≤ N) (hell : ell ≤ N) (ha : 0 < a)
    (hpdegree : p.natDegree = N) (hpsplit : p.Splits)
    (hppos : 0 < p.leadingCoeff) (hproots : ∀ r ∈ p.roots, r < 0) :
    (compression N ell p).natDegree = (N + ell) / 2 ∧
    (compression (N + 1) ell (nextPolynomial a p)).natDegree = (N + ell + 1) / 2 ∧
    HasPosLeadingCoeff (compression N ell p) ∧
    HasPosLeadingCoeff (compression (N + 1) ell (nextPolynomial a p)) ∧
    (compression N ell p).Splits ∧
    HasSimpleRoots (compression N ell p) ∧
    (∀ r ∈ (compression N ell p).roots, r < 0) ∧
    (compression (N + 1) ell (nextPolynomial a p)).Splits ∧
    HasSimpleRoots (compression (N + 1) ell (nextPolynomial a p)) ∧
    (∀ r ∈ (compression (N + 1) ell (nextPolynomial a p)).roots, r < 0) ∧
    StrictInterl (compression N ell p)
      (compression (N + 1) ell (nextPolynomial a p)) ∧
    (∀ r, (compression N ell p).IsRoot r →
      ¬ (compression (N + 1) ell (nextPolynomial a p)).IsRoot r) := by
  obtain ⟨hdeg₁, hdeg₂, hroot₁, hroot₂, hinter⟩ :=
    compression_nextPolynomial_strictRootGeometry hN hell ha hpdegree hpsplit hppos hproots
  exact ⟨hdeg₁, hdeg₂, hinter.1, hinter.2.1,
    hroot₁.2.1, hroot₁.hasSimpleRoots, hroot₁.2.2.2,
    hroot₂.2.1, hroot₂.hasSimpleRoots, hroot₂.2.2.2,
    hinter.toStrictInterl, hinter.noCommonRoot⟩

end RealRooted.FactorialCompression
