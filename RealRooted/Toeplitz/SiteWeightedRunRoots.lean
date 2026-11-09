module

public import RealRooted.Toeplitz.AffineVector
public import RealRooted.Toeplitz.SiteWeightedRuns
public import RealRooted.RootLocation.Basic
import RealRooted.ReciprocalShift.ProperPosition
import RealRooted.Wagner.NonpositiveRoots

/-!
# Real-rootedness of site-weighted run polynomials

For a real sequence `u` and nonnegative site weights `a₀, a₁, …`, the *site-weighted run
polynomial* is `B_N(t) = Z_N(a₀ t, …, a_{N-1} t)` (`siteWeightedRunPolynomial`), where `Z_N` is
the site-weighted run sum of `RealRooted.Toeplitz.SiteWeightedRuns`.

Assume `u_k = e₁ᵀ Aᵏ 𝟙` for a finite nonempty matrix `A` with nonnegative entries and
nonnegative ordered `2 × 2` minors (`Matrix.IsTP2`) whose columns weakly decrease. Then every
`B_N` has constant coefficient `1`, nonnegative coefficients and degree at most `N`, only
negative real roots, and consecutive `B_N`, `B_{N+1}` are in oriented weak interlacing position
(`StrictInterl (B_N) (B_{N+1})`). Zero site weights are allowed.

The proof reverses the transfer identity. With `h_N = (a_{N-1} A + X J) ⋯ (a₀ A + X J) 𝟙`
(the vector recursion of `RealRooted.affineVector` for the matrices `a_k A`, which are again
`TP2` with decreasing columns), one has `Y_N = reflect N h_N` for the transfer vector `Y_N`, hence
`B_N = reflect N h_{N,1}`. The reversal of interlacing sequences with nonpositive roots
(`reciprocalShift_reverses_strictInterl`) and Wagner's `X`-multiplication transport finish.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The site-weighted run polynomial `B_N(t) = Z_N(a₀ t, …, a_{N-1} t)` with run weights `u`
and site weights `a`. -/
def siteWeightedRunPolynomial (u a : ℕ → ℝ) (N : ℕ) : ℝ[X] :=
  siteWeightedRuns (fun k => C (u k)) fun i : Fin N => C (a i) * X

/-- A nonnegative multiple of a `TP2` matrix is `TP2`. -/
lemma _root_.Matrix.IsTP2.smul_nonneg {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTP2) {c : ℝ} (hc : 0 ≤ c) : (c • A).IsTP2 := by
  refine ⟨fun i j => by simpa using mul_nonneg hc (hA.nonneg i j), fun i₁ i₂ j₁ j₂ hi hj => ?_⟩
  have := mul_nonneg (mul_nonneg hc hc) (hA.minor_nonneg hi hj)
  simp only [Matrix.smul_apply, smul_eq_mul]
  nlinarith

variable {n : ℕ}

/-- The run polynomial is the first coordinate of the transfer vector of the polynomial matrix
`A.map C`, when `u_k = e₁ᵀ Aᵏ 𝟙`. -/
theorem siteWeightedRunPolynomial_eq_runVector {u : ℕ → ℝ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hu : ∀ k, u k = runKernel A k) (a : ℕ → ℝ)
    (N : ℕ) :
    siteWeightedRunPolynomial u a N = runVector (A.map C) N (fun i : Fin N => C (a i) * X) 0 := by
  have : (fun k => C (u k)) = runKernel (A.map C) := by
    funext k
    rw [runKernel_map, hu]
  rw [siteWeightedRunPolynomial, this, siteWeightedRuns_runKernel]

private lemma reflect_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) (N : ℕ) :
    reflect N (∑ i ∈ s, f i) = ∑ i ∈ s, reflect N (f i) :=
  map_sum (AddMonoidHom.mk' (reflect N) fun p q => reflect_add p q N) f s

/-- **Reversal of the transfer vector.** The transfer vector of the polynomial matrix is the
degree-`N` reflection of the affine vector for the matrices `a_k A`:
`(J + a_{N-1} X A) ⋯ (J + a₀ X A) 𝟙 = reflect N ((a_{N-1} A + X J) ⋯ (a₀ A + X J) 𝟙)`. -/
theorem runVector_eq_reflect_affineVector (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a : ℕ → ℝ) (N : ℕ) (j : Fin (n + 1)) :
    runVector (A.map C) N (fun i : Fin N => C (a i) * X) j =
      reflect N (affineVector (fun k => a k • A) N j) := by
  induction N generalizing j with
  | zero => simp [runVector, affineVector, reflect_one]
  | succ N ih =>
    have hinit : Fin.init (fun i : Fin (N + 1) => C (a i) * X) =
        fun i : Fin N => C (a i) * X := rfl
    rw [runVector_succ_apply, hinit]
    simp only [ih]
    have hdeg := fun i => (affineVector_monic_natDegree (fun k => a k • A) N i).2.le
    have hstep : affineVector (fun k => a k • A) (N + 1) j =
        ∑ i, C (a N * A j i) * affineVector (fun k => a k • A) N i +
          X ^ 1 * affineVector (fun k => a k • A) N 0 := by
      simp [affineVector, tp2AffineStep, Polynomial.smul_eq_C_mul]
    rw [hstep, reflect_add, reflect_sum, reflect_X_pow_mul _ 1 (hdeg 0), Finset.mul_sum]
    simp_rw [reflect_C_mul, reflect_succ _ (hdeg _)]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.map_apply, C_mul, Fin.val_last]
    ring

/-! ### The certificate -/

section Certificate

variable {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {u a : ℕ → ℝ}

/-- The matrices `a_k A` are `TP2` with decreasing columns when `A` is and `a_k ≥ 0`. -/
private lemma tp2_smul_family (hA : A.IsTP2)
    (hcol : ∀ ⦃i i' j : Fin (n + 1)⦄, i ≤ i' → A i' j ≤ A i j) (ha : ∀ k, 0 ≤ a k) :
    (∀ k, (a k • A).IsTP2) ∧
      ∀ k ⦃i i' j : Fin (n + 1)⦄, i ≤ i' → (a k • A) i' j ≤ (a k • A) i j :=
  ⟨fun k => hA.smul_nonneg (ha k), fun k i i' j hi => by
    simpa using mul_le_mul_of_nonneg_left (hcol hi (j := j)) (ha k)⟩

/-- `B_N = reflect N h_N`, with `h_N` the first coordinate of the affine vector for the
matrices `a_k A`. -/
theorem siteWeightedRunPolynomial_eq_reflect (hu : ∀ k, u k = runKernel A k) (N : ℕ) :
    siteWeightedRunPolynomial u a N = reflect N (affineVector (fun k => a k • A) N 0) := by
  rw [siteWeightedRunPolynomial_eq_runVector A hu, runVector_eq_reflect_affineVector]

/-- `B_N` is the reversal of `h_N`, since `h_N` is monic of degree `N`. -/
theorem siteWeightedRunPolynomial_eq_reverse (hu : ∀ k, u k = runKernel A k) (N : ℕ) :
    siteWeightedRunPolynomial u a N = (affineVector (fun k => a k • A) N 0).reverse := by
  rw [siteWeightedRunPolynomial_eq_reflect hu, Polynomial.reverse,
    (affineVector_monic_natDegree _ N 0).2]

/-- The constant coefficient of `B_N` is `1`: `B_N(0) = 1`. -/
theorem coeff_zero_siteWeightedRunPolynomial (hu : ∀ k, u k = runKernel A k) (N : ℕ) :
    (siteWeightedRunPolynomial u a N).coeff 0 = 1 := by
  rw [siteWeightedRunPolynomial_eq_reflect hu, coeff_reflect, revAt_le (Nat.zero_le N),
    Nat.sub_zero]
  have h := (affineVector_monic_natDegree (fun k => a k • A) N 0)
  simpa [h.2] using h.1.coeff_natDegree

/-- The degree of `B_N` is at most `N`. -/
theorem natDegree_siteWeightedRunPolynomial_le (hu : ∀ k, u k = runKernel A k) (N : ℕ) :
    (siteWeightedRunPolynomial u a N).natDegree ≤ N := by
  rw [siteWeightedRunPolynomial_eq_reflect hu]
  exact natDegree_reflect_le.trans (by simp [(affineVector_monic_natDegree _ N 0).2])

/-- `B_N` has nonnegative coefficients. -/
theorem hasNonnegCoeffs_siteWeightedRunPolynomial (hA : A.IsTP2)
    (hcol : ∀ ⦃i i' j : Fin (n + 1)⦄, i ≤ i' → A i' j ≤ A i j) (ha : ∀ k, 0 ≤ a k)
    (hu : ∀ k, u k = runKernel A k) (N : ℕ) :
    HasNonnegCoeffs (siteWeightedRunPolynomial u a N) := by
  obtain ⟨hM, hMcol⟩ := tp2_smul_family hA hcol ha
  have hf := isInterlacingSeqNonneg_affineVector hM hMcol N
  rw [siteWeightedRunPolynomial_eq_reflect hu]
  exact (hf.nonnegCoeffs _ (List.mem_ofFn.mpr ⟨0, rfl⟩)).reflect N

/-- The first coordinate `h_N` of the affine vector is a polynomial with nonpositive real roots
and nonnegative coefficients. -/
private lemma isPFPolynomial_affineVector_zero (hA : A.IsTP2)
    (hcol : ∀ ⦃i i' j : Fin (n + 1)⦄, i ≤ i' → A i' j ≤ A i j) (ha : ∀ k, 0 ≤ a k) (N : ℕ) :
    IsPFPolynomial (affineVector (fun k => a k • A) N 0) := by
  obtain ⟨hM, hMcol⟩ := tp2_smul_family hA hcol ha
  have hf := isInterlacingSeqNonneg_affineVector hM hMcol N
  have hmem : affineVector (fun k => a k • A) N 0 ∈ List.ofFn (affineVector (fun k => a k • A) N) :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  exact ⟨hf.nonnegCoeffs _ hmem, Or.inr (hf.realRooted _ hmem).2,
    roots_nonpos_of_hasNonnegCoeffs (hf.nonnegCoeffs _ hmem)⟩

/-- **Negative real roots.** `B_N` is real-rooted with all roots negative. -/
theorem isRealRootedIn_Iio_siteWeightedRunPolynomial (hA : A.IsTP2)
    (hcol : ∀ ⦃i i' j : Fin (n + 1)⦄, i ≤ i' → A i' j ≤ A i j) (ha : ∀ k, 0 ≤ a k)
    (hu : ∀ k, u k = runKernel A k) (N : ℕ) :
    IsRealRootedIn (Set.Iio 0) (siteWeightedRunPolynomial u a N) := by
  have hpf := isPFPolynomial_affineVector_zero (a := a) hA hcol ha N
  have hroot : IsRealRootedIn (Set.Iic 0) (affineVector (fun k => a k • A) N 0) :=
    ⟨affineVector_ne_zero _ N 0, hpf.2.1.resolve_left (affineVector_ne_zero _ N 0), hpf.2.2⟩
  rw [siteWeightedRunPolynomial_eq_reverse hu]
  refine hroot.reverse.mono ?_
  rintro - ⟨s, ⟨hs, hs0⟩, rfl⟩
  exact inv_lt_zero.mpr (lt_of_le_of_ne hs hs0)

/-- **Consecutive interlacing.** `B_N ≪ B_{N+1}`: the roots of `B_{N+1}` are separated by, and
enclose, the roots of `B_N`, in the oriented weak convention of `StrictInterl` (a root may be
shared, and degrees may agree when a site weight vanishes). -/
theorem strictInterl_siteWeightedRunPolynomial (hA : A.IsTP2)
    (hcol : ∀ ⦃i i' j : Fin (n + 1)⦄, i ≤ i' → A i' j ≤ A i j) (ha : ∀ k, 0 ≤ a k)
    (hu : ∀ k, u k = runKernel A k) (N : ℕ) :
    StrictInterl (siteWeightedRunPolynomial u a N) (siteWeightedRunPolynomial u a (N + 1)) := by
  obtain ⟨hM, hMcol⟩ := tp2_smul_family hA hcol ha
  have hroots := isRealRootedIn_Iio_siteWeightedRunPolynomial hA hcol ha hu
  have hnn := hasNonnegCoeffs_siteWeightedRunPolynomial hA hcol ha hu
  have hpos : ∀ N, Wagner.HasNonposRootsPosLeading (siteWeightedRunPolynomial u a N) := fun N =>
    ⟨(hroots N).splits, fun r hr => (hroots N).mem_of_mem_roots hr |>.le,
      (hnn N).pos_leadingCoeff (hroots N).ne_zero⟩
  have hrev := reciprocalShift_reverses_strictInterl (D := N + 1)
    (isPFPolynomial_affineVector_zero (a := a) hA hcol ha N)
    (isPFPolynomial_affineVector_zero (a := a) hA hcol ha (N + 1))
    (by simp [(affineVector_monic_natDegree _ N 0).2])
    (by simp [(affineVector_monic_natDegree _ (N + 1) 0).2])
    (strictInterl_affineVector_zero hM hMcol N)
  rw [(Wagner.mulX_iff (hpos N) (hpos (N + 1)))]
  have h1 : reciprocalShift (N + 1) (affineVector (fun k => a k • A) N 0) =
      X * siteWeightedRunPolynomial u a N := by
    rw [reciprocalShift, reflect_succ _ (affineVector_monic_natDegree _ N 0).2.le,
      siteWeightedRunPolynomial_eq_reflect hu, mul_comm]
  rw [h1, reciprocalShift, ← siteWeightedRunPolynomial_eq_reflect hu] at hrev
  exact hrev

/-- **Site-weighted run polynomials of a `TP2` kernel** (weak, any nonnegative site weights).
Let `A` be a finite nonempty matrix with nonnegative entries and nonnegative ordered `2 × 2`
minors whose columns weakly decrease, let `u_k = e₁ᵀ Aᵏ 𝟙`, and let `a_i ≥ 0` be site weights
(zero weights allowed). Then `B_N(t) = Z_N(a₀ t, …, a_{N-1} t)` has constant coefficient `1`,
nonnegative coefficients, degree at most `N`, only negative real roots, and `B_N ≪ B_{N+1}`. -/
theorem siteWeightedRunPolynomial_certificate (hA : A.IsTP2)
    (hcol : ∀ ⦃i i' j : Fin (n + 1)⦄, i ≤ i' → A i' j ≤ A i j) (ha : ∀ k, 0 ≤ a k)
    (hu : ∀ k, u k = runKernel A k) (N : ℕ) :
    (siteWeightedRunPolynomial u a N).coeff 0 = 1 ∧
      (siteWeightedRunPolynomial u a N).natDegree ≤ N ∧
      HasNonnegCoeffs (siteWeightedRunPolynomial u a N) ∧
      IsRealRootedIn (Set.Iio 0) (siteWeightedRunPolynomial u a N) ∧
      StrictInterl (siteWeightedRunPolynomial u a N) (siteWeightedRunPolynomial u a (N + 1)) :=
  ⟨coeff_zero_siteWeightedRunPolynomial hu N, natDegree_siteWeightedRunPolynomial_le hu N,
    hasNonnegCoeffs_siteWeightedRunPolynomial hA hcol ha hu N,
    isRealRootedIn_Iio_siteWeightedRunPolynomial hA hcol ha hu N,
    strictInterl_siteWeightedRunPolynomial hA hcol ha hu N⟩

end Certificate

end RealRooted
