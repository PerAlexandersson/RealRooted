import RealRooted.FactorialCompression.Compression
import RealRooted.FactorialCompression.Kernel

/-!
# The degree-changing factorial compression theorem

For `N ≠ 0`, `ℓ ≤ N`, `a > 0` and `p` of degree `N` with positive leading coefficient and only
negative real roots (repeated roots allowed), the compressions `T^{(ℓ)}_N p` and
`T^{(ℓ)}_{N+1} ((x + a) p + x p')` have the stated degrees, positive leading coefficients, simple
strictly negative roots, strictly interlace, and have no common root
(`compression_nextPolynomial_strictInterl`).  The case `ℓ = 1`, `a = (N + 2) / 2` is
`compression_one_nextPolynomial_strictInterl`.

The proof writes the first compression as `U = h_m ∘ₙ p` and the second as
`W + x V` with `W = K_{N,ℓ,a} ∘ₙ p`, `V = h_{m-1} ∘ₙ p` and `m = N + ℓ`.  The pair `U ≺ W`
is the image of `h_m ≺ K_{N,ℓ,a}` under the strict Schur--Szegő endpoint, and
`V = U - 2/m x U'` gives the sign test on `U` versus `W + x V`.  The boundary
`N + ℓ = 1` is a constant/linear pair.

The theorem is due to Zhanhe Zhang (*Factorial compression and strict interlacing*,
SSRN 7510941); the proofs are ported from the draft of Zhang's formalization.
-/

open Polynomial

namespace RealRooted.FactorialCompression

private theorem coeff_zero_pos_of_roots_neg {p : ℝ[X]} (hps : p.Splits)
    (hppos : HasPosLeadingCoeff p) (hneg : ∀ r ∈ p.roots, r < 0) : 0 < p.coeff 0 :=
  (mul_pos_iff_of_pos_left hppos).mp
    (leadingCoeff_mul_coeff_pos_of_roots_neg hps hppos.ne_zero hneg (Nat.zero_le _))

/-- The constant/linear pair `c ≺ b + d x` with `c, b, d > 0`: degrees, leading coefficient,
negative root, and strict interlacing. -/
private theorem constant_linear_geometry {c b d : ℝ} (hc : 0 < c) (hb : 0 < b) (hd : 0 < d) :
    (C b + C d * X : ℝ[X]).natDegree = 1 ∧ HasPosLeadingCoeff (C b + C d * X : ℝ[X]) ∧
      (∀ r ∈ (C b + C d * X : ℝ[X]).roots, r < 0) ∧
      StrictInterl (C c) (C b + C d * X : ℝ[X]) := by
  have hfactor : (C b + C d * X : ℝ[X]) = C d * (X - C (-b / d)) := by
    rw [mul_sub, ← C_mul, show d * (-b / d) = -b by field_simp, C_neg]
    ring
  have hroots : (C b + C d * X : ℝ[X]).roots = {-b / d} := by
    rw [hfactor, roots_C_mul _ hd.ne', roots_X_sub_C]
  have hdegree : (C b + C d * X : ℝ[X]).natDegree = 1 := by
    rw [hfactor, natDegree_C_mul hd.ne', natDegree_X_sub_C]
  refine ⟨hdegree, ?_, ?_, ?_⟩
  · rw [hfactor]
    exact hasPosLeadingCoeff_C_mul hd (hasPosLeadingCoeff_of_monic (monic_X_sub_C _))
  · intro r hr
    rw [hroots, Multiset.mem_singleton] at hr
    rw [hr]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hb) hd
  · refine ⟨⟨C_ne_zero.mpr hc.ne', Splits.C c⟩,
      ⟨fun hz => by simp [hz] at hdegree, Splits.of_natDegree_eq_one hdegree⟩,
      [], [-b / d], by simp, by simp, by simp, by simp [hroots], Or.inl ⟨by simp, trivial⟩⟩

/-- Exact compressions in the boundary case `N = 1`, `ℓ = 0`. -/
private theorem compression_boundary (a : ℝ) (p : ℝ[X]) :
    compression 1 0 p = C (p.coeff 0) ∧
      compression 2 0 (nextPolynomial a p) =
        C (a * p.coeff 0) + C (p.coeff 0 + (a + 1) * p.coeff 1) * X := by
  constructor
  · simp [compression, multiplier, Finset.sum_range_succ]
  · have h0 := coeff_nextPolynomial a p 0
    have h1 := coeff_nextPolynomial a p 1
    simp only [coeff_X_mul_zero, zero_add, Nat.cast_zero, add_zero, coeff_X_mul] at h0 h1
    simp [compression, multiplier, Finset.sum_range_succ, h0, h1]

/-- The boundary case `N = 1`, `ℓ = 0` of the main theorem. -/
private theorem compression_nextPolynomial_core_boundary {a : ℝ} {p : ℝ[X]} (ha : 0 < a)
    (hp : p.natDegree = 1) (hps : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hneg : ∀ r ∈ p.roots, r < 0) :
    (compression 1 0 p).natDegree = (1 + 0) / 2 ∧
      (compression (1 + 1) 0 (nextPolynomial a p)).natDegree = (1 + 0 + 1) / 2 ∧
      HasPosLeadingCoeff (compression 1 0 p) ∧
      HasPosLeadingCoeff (compression (1 + 1) 0 (nextPolynomial a p)) ∧
      (∀ r ∈ (compression 1 0 p).roots, r < 0) ∧
      (∀ r ∈ (compression (1 + 1) 0 (nextPolynomial a p)).roots, r < 0) ∧
      StrictInterl (compression 1 0 p) (compression (1 + 1) 0 (nextPolynomial a p)) ∧
      ∀ r, (compression 1 0 p).IsRoot r →
        ¬ (compression (1 + 1) 0 (nextPolynomial a p)).IsRoot r := by
  have hp0 := coeff_zero_pos_of_roots_neg hps hppos hneg
  have hp1 : 0 < p.coeff 1 := by
    have h : 0 < p.leadingCoeff := hppos
    rwa [leadingCoeff, hp] at h
  have hb : 0 < a * p.coeff 0 := mul_pos ha hp0
  have hd : 0 < p.coeff 0 + (a + 1) * p.coeff 1 := add_pos hp0 (mul_pos (by linarith) hp1)
  obtain ⟨h1, h2⟩ := compression_boundary a p
  obtain ⟨hdeg, hpos, hroots, hint⟩ := constant_linear_geometry hp0 hb hd
  rw [h1, h2]
  refine ⟨by simp, by simpa using hdeg, by simpa [HasPosLeadingCoeff] using hp0, hpos,
    by simp, hroots, hint, fun r hr => ?_⟩
  simp [hp0.ne'] at hr

/-- The general case `N + ℓ ≥ 2` of the main theorem, before the simple roots are extracted. -/
private theorem compression_nextPolynomial_core_general {N ℓ : ℕ} {a : ℝ} {p : ℝ[X]}
    (hN : N ≠ 0) (hℓ : ℓ ≤ N) (ha : 0 < a) (hm : 2 ≤ N + ℓ)
    (hp : p.natDegree = N) (hps : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hneg : ∀ r ∈ p.roots, r < 0) :
    (compression N ℓ p).natDegree = (N + ℓ) / 2 ∧
      (compression (N + 1) ℓ (nextPolynomial a p)).natDegree = (N + ℓ + 1) / 2 ∧
      HasPosLeadingCoeff (compression N ℓ p) ∧
      HasPosLeadingCoeff (compression (N + 1) ℓ (nextPolynomial a p)) ∧
      (∀ r ∈ (compression N ℓ p).roots, r < 0) ∧
      (∀ r ∈ (compression (N + 1) ℓ (nextPolynomial a p)).roots, r < 0) ∧
      StrictInterl (compression N ℓ p) (compression (N + 1) ℓ (nextPolynomial a p)) ∧
      ∀ r, (compression N ℓ p).IsRoot r →
        ¬ (compression (N + 1) ℓ (nextPolynomial a p)).IsRoot r := by
  have hpnonneg : HasNonnegCoeffs p :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hps).mpr
      ⟨hppos, fun r hr => (hneg r hr).le⟩).1
  have hkernel := strictInterl_commonKernel_kernel hN hℓ ha hm
  have hhneg : ∀ r ∈ (commonKernel (N + ℓ)).roots, r < 0 := fun r hr =>
    lt_zero_of_isRoot_commonKernel ((mem_roots (commonKernel_ne_zero _)).mp hr)
  have hdegH : (commonKernel (N + ℓ)).natDegree ≤ N := by
    rw [natDegree_commonKernel]
    lia
  have hdegPrev : (commonKernel (N + ℓ - 1)).natDegree ≤ N := by
    rw [natDegree_commonKernel]
    lia
  have hdegK : (kernel N ℓ a).natDegree ≤ N := by
    rw [natDegree_kernel hN hℓ ha]
    lia
  have hKpos := hasPosLeadingCoeff_kernel hN hℓ ha
  have hHpos := hasPosLeadingCoeff_commonKernel (N + ℓ)
  have hUW := strictInterl_schurSzegoComp_of_roots_neg hN hdegH hdegK hHpos hKpos hkernel.1
    hkernel.2.1 hp hps hppos hneg
  set U := schurSzegoComp N (commonKernel (N + ℓ)) p with hU
  set W := schurSzegoComp N (kernel N ℓ a) p with hW
  set V := schurSzegoComp N (commonKernel (N + ℓ - 1)) p with hV
  have hUpos : HasPosLeadingCoeff U :=
    hasPosLeadingCoeff_schurSzegoComp_of_roots_neg hdegH hHpos hp hps hppos hneg
  have hWpos : HasPosLeadingCoeff W :=
    hasPosLeadingCoeff_schurSzegoComp_of_roots_neg hdegK hKpos hp hps hppos hneg
  have hUd : U.natDegree = (N + ℓ) / 2 := by
    rw [hU, natDegree_schurSzegoComp_of_roots_neg hdegH hp hps hppos hneg,
      natDegree_commonKernel]
  have hWd : W.natDegree = (N + ℓ + 1) / 2 := by
    rw [hW, natDegree_schurSzegoComp_of_roots_neg hdegK hp hps hppos hneg,
      natDegree_kernel hN hℓ ha]
  have hVd : V.natDegree = (N + ℓ - 1) / 2 := by
    rw [hV, natDegree_schurSzegoComp_of_roots_neg hdegPrev hp hps hppos hneg,
      natDegree_commonKernel]
  have hUneg : ∀ r ∈ U.roots, r < 0 :=
    roots_schurSzegoComp_neg_of_roots_neg (splits_commonKernel hm) hHpos hhneg hps hppos hneg
  have hVnonneg : HasNonnegCoeffs V := (hasNonnegCoeffs_commonKernel _).schurSzegoComp hpnonneg
  have hWnonneg : HasNonnegCoeffs W :=
    (hasNonnegCoeffs_kernel hN hℓ ha).schurSzegoComp hpnonneg
  have hGnonneg : HasNonnegCoeffs (W + X * V) := hWnonneg.add (hasNonnegCoeffs_X.mul hVnonneg)
  have hGzero : 0 < (W + X * V).coeff 0 := by
    rw [coeff_add, coeff_X_mul_zero, add_zero, hW, coeff_zero_schurSzegoComp]
    exact mul_pos (coeff_kernel_pos (k := 0) hN hℓ ha (by lia))
      (coeff_zero_pos_of_roots_neg hps hppos hneg)
  have hGd : (W + X * V).natDegree = (N + ℓ + 1) / 2 := by
    apply Nat.le_antisymm
    · refine (natDegree_add_le W (X * V)).trans (max_le hWd.le ?_)
      have hv : (X * V).natDegree ≤ (X : ℝ[X]).natDegree + V.natDegree := natDegree_mul_le
      rw [natDegree_X, hVd] at hv
      lia
    · apply le_natDegree_of_ne_zero
      have hwc : 0 < W.coeff ((N + ℓ + 1) / 2) := by
        rw [← hWd, coeff_natDegree]
        exact hWpos
      exact (lt_of_lt_of_le hwc (by
        rw [coeff_add]
        exact le_add_of_nonneg_right ((hasNonnegCoeffs_X.mul hVnonneg) _))).ne'
  have hVid : V = U - C (2 / ((N + ℓ : ℕ) : ℝ)) * (X * U.derivative) := by
    have h := schurSzegoComp_commonKernel_eq_sub_derivative N (N + ℓ - 1) p
    rw [show N + ℓ - 1 + 1 = N + ℓ by lia] at h
    have hcast : ((N + ℓ - 1 : ℕ) : ℝ) + 1 = ((N + ℓ : ℕ) : ℝ) := by
      exact_mod_cast (show N + ℓ - 1 + 1 = N + ℓ by lia)
    rwa [hcast] at h
  have hsign : ∀ r, U.IsRoot r → (W + X * V).eval r * U.derivative.eval r < 0 := by
    intro r hr
    have hWU := hUW.1.eval_mul_derivative_neg_of_left_root_of_no_common hUpos hWpos hUW.2 hr
    have hVeval : V.eval r = -(2 / ((N + ℓ : ℕ) : ℝ)) * r * U.derivative.eval r := by
      rw [hVid]
      simp only [eval_sub, eval_mul, eval_C, eval_X, hr.eq_zero]
      ring
    have hc : 0 < 2 / ((N + ℓ : ℕ) : ℝ) := by positivity
    have hsq : 0 ≤ 2 / ((N + ℓ : ℕ) : ℝ) * (r * U.derivative.eval r) ^ 2 := by positivity
    have hexp : (W + X * V).eval r * U.derivative.eval r =
        W.eval r * U.derivative.eval r -
          2 / ((N + ℓ : ℕ) : ℝ) * (r * U.derivative.eval r) ^ 2 := by
      simp only [eval_add, eval_mul, eval_X, hVeval]
      ring
    rw [hexp]
    linarith
  obtain ⟨hGint, hGno, hGneg⟩ :=
    strictInterl_and_noCommonRoot_of_eval_mul_derivative_neg hUW.1.1.2 hUpos
      (by rw [hUd]; lia) hGnonneg hGzero (by rw [hGd, hUd]; lia) hsign
  have hGpos : HasPosLeadingCoeff (W + X * V) :=
    hGnonneg.pos_leadingCoeff (fun hz => by simp [hz] at hGzero)
  have hscale1 : 0 < (N.factorial : ℝ) / ((N + ℓ).factorial : ℝ) := by positivity
  have hscale2 : 0 < (N.factorial : ℝ) / ((N + ℓ - 1).factorial : ℝ) := by positivity
  rw [compression_eq_schurSzegoComp, compression_nextPolynomial N ℓ a p hN hp.le]
  refine ⟨?_, ?_, hasPosLeadingCoeff_C_mul hscale1 hUpos, hasPosLeadingCoeff_C_mul hscale2 hGpos,
    ?_, ?_, ?_, ?_⟩
  · rw [natDegree_C_mul hscale1.ne']
    exact hUd
  · rw [natDegree_C_mul hscale2.ne']
    exact hGd
  · rw [roots_C_mul _ hscale1.ne']
    exact hUneg
  · rw [roots_C_mul _ hscale2.ne']
    exact hGneg
  · exact (hGint.C_mul_left hscale1.ne').C_mul_right hscale2.ne'
  · intro r hr hr'
    rw [IsRoot.def, eval_mul, eval_C] at hr hr'
    exact hGno r ((mul_eq_zero.mp hr).resolve_left hscale1.ne')
      ((mul_eq_zero.mp hr').resolve_left hscale2.ne')

/-- **Degree-changing factorial compression** (Theorem 4.1 of Zhang, SSRN 7510941, in the general
level-`ℓ`, shift-`a` form).  Let `N ≠ 0`, `ℓ ≤ N`, `a > 0`, and let `p` have degree `N`, positive
leading coefficient and only negative real roots (repeated roots allowed).  Then the level-`ℓ`
compressions `T_N p` and `T_{N+1} ((x + a) p + x p')` have degrees `⌊(N + ℓ) / 2⌋` and
`⌊(N + ℓ + 1) / 2⌋`, positive leading coefficients, simple strictly negative roots, strictly
interlace, and have no common root.  The case `N = 1`, `ℓ = 0` is the constant/linear boundary. -/
theorem compression_nextPolynomial_strictInterl {N ℓ : ℕ} {a : ℝ} {p : ℝ[X]}
    (hN : N ≠ 0) (hℓ : ℓ ≤ N) (ha : 0 < a)
    (hp : p.natDegree = N) (hps : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hneg : ∀ r ∈ p.roots, r < 0) :
    (compression N ℓ p).natDegree = (N + ℓ) / 2 ∧
      (compression (N + 1) ℓ (nextPolynomial a p)).natDegree = (N + ℓ + 1) / 2 ∧
      HasPosLeadingCoeff (compression N ℓ p) ∧
      HasPosLeadingCoeff (compression (N + 1) ℓ (nextPolynomial a p)) ∧
      HasSimpleRoots (compression N ℓ p) ∧
      HasSimpleRoots (compression (N + 1) ℓ (nextPolynomial a p)) ∧
      (∀ r ∈ (compression N ℓ p).roots, r < 0) ∧
      (∀ r ∈ (compression (N + 1) ℓ (nextPolynomial a p)).roots, r < 0) ∧
      StrictInterl (compression N ℓ p) (compression (N + 1) ℓ (nextPolynomial a p)) ∧
      ∀ r, (compression N ℓ p).IsRoot r →
        ¬ (compression (N + 1) ℓ (nextPolynomial a p)).IsRoot r := by
  have hcore : (compression N ℓ p).natDegree = (N + ℓ) / 2 ∧
      (compression (N + 1) ℓ (nextPolynomial a p)).natDegree = (N + ℓ + 1) / 2 ∧
      HasPosLeadingCoeff (compression N ℓ p) ∧
      HasPosLeadingCoeff (compression (N + 1) ℓ (nextPolynomial a p)) ∧
      (∀ r ∈ (compression N ℓ p).roots, r < 0) ∧
      (∀ r ∈ (compression (N + 1) ℓ (nextPolynomial a p)).roots, r < 0) ∧
      StrictInterl (compression N ℓ p) (compression (N + 1) ℓ (nextPolynomial a p)) ∧
      ∀ r, (compression N ℓ p).IsRoot r →
        ¬ (compression (N + 1) ℓ (nextPolynomial a p)).IsRoot r := by
    by_cases hmone : N + ℓ = 1
    · obtain ⟨rfl, rfl⟩ : N = 1 ∧ ℓ = 0 := by lia
      exact compression_nextPolynomial_core_boundary ha hp hps hppos hneg
    · exact compression_nextPolynomial_core_general hN hℓ ha (by lia) hp hps hppos hneg
  obtain ⟨hd1, hd2, hpos1, hpos2, hneg1, hneg2, hint, hno⟩ := hcore
  have hsimple := hint.hasSimpleRoots_of_no_common_root fun r hr => hno r hr.1 hr.2
  exact ⟨hd1, hd2, hpos1, hpos2, hsimple.1, hsimple.2, hneg1, hneg2, hint, hno⟩

/-- **The `ℓ = 1` compression theorem** in the normalization of the separable-permutation
application: for `N ≠ 0` and `p` of degree `N` with positive leading coefficient and only negative
real roots, let `q = (x + (N + 2) / 2) p + x p'`.  Then `T_N p` and `T_{N+1} q` have degrees
`⌊(N + 1) / 2⌋` and `⌊(N + 2) / 2⌋`, positive leading coefficients, simple strictly negative roots,
strictly interlace and have no common root (Zhang, SSRN 7510941). -/
theorem compression_one_nextPolynomial_strictInterl {N : ℕ} {p : ℝ[X]} (hN : N ≠ 0)
    (hp : p.natDegree = N) (hps : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hneg : ∀ r ∈ p.roots, r < 0) :
    (compression N 1 p).natDegree = (N + 1) / 2 ∧
      (compression (N + 1) 1 (nextPolynomial (((N : ℝ) + 2) / 2) p)).natDegree = (N + 2) / 2 ∧
      HasPosLeadingCoeff (compression N 1 p) ∧
      HasPosLeadingCoeff (compression (N + 1) 1 (nextPolynomial (((N : ℝ) + 2) / 2) p)) ∧
      HasSimpleRoots (compression N 1 p) ∧
      HasSimpleRoots (compression (N + 1) 1 (nextPolynomial (((N : ℝ) + 2) / 2) p)) ∧
      (∀ r ∈ (compression N 1 p).roots, r < 0) ∧
      (∀ r ∈ (compression (N + 1) 1 (nextPolynomial (((N : ℝ) + 2) / 2) p)).roots, r < 0) ∧
      StrictInterl (compression N 1 p)
        (compression (N + 1) 1 (nextPolynomial (((N : ℝ) + 2) / 2) p)) ∧
      ∀ r, (compression N 1 p).IsRoot r →
        ¬ (compression (N + 1) 1 (nextPolynomial (((N : ℝ) + 2) / 2) p)).IsRoot r :=
  compression_nextPolynomial_strictInterl hN (Nat.one_le_iff_ne_zero.mpr hN) (by positivity) hp
    hps hppos hneg

end RealRooted.FactorialCompression
