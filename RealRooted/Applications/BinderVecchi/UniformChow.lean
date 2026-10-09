import RealRooted.SymmetricDecomposition.DerangementTransform
import RealRooted.SymmetricDecomposition.EulerianTransform
import RealRooted.Applications.BinderVecchi.UniformMatroid
import RealRooted.PFPolynomial

/-!
# Chow and augmented Chow polynomials of uniform matroids

The case `i = 0` of Binder--Vecchi, Theorems 1.4 and 1.6: the refined Hodge--Poincaré
polynomials `\underline H^0_{r,n}` and `\widetilde H^0_{r,n}` of the uniform matroid `U_{r,n}`
are the Chow polynomial and the augmented Chow polynomial.

Write `g_{r,n} = ∑_{s < r} C(n,s) X^s`.  In the formulation of Brändén--Vecchi (Chow polynomials
of totally nonnegative matrices), the Chow polynomial of `U_{r,n}` is
`P + X * S_{r-1}(P)` with `P = D(g_{r,n})` the deranged image, where `S_N` is the Chow operator
`chowS N` (the first entry of the Chow staircase row transform of the weighted deranged row),
and the augmented Chow polynomial is `Q + X * S_r(Q)` with `Q = A°(g_{r,n})` the Eulerian image.
Both are real-rooted because `g_{r,n}` has the nonnegative magic-basis expansion
`g_{r,n} = ∑_p C(n-r+p, p) X^p (1+X)^{r-1-p}` and the corresponding image rows are
reflection-interlacing (Brändén--Vecchi, Theorem 4.13).

`chowUniform_eq` rewrites the Chow polynomial in the closed derangement form
`∑_{k < r} C(n,k) d_k (1 + X + ⋯ + X^(r-k-1))`, and `augChowUniform_mul_sub_one` gives a closed
form for the augmented one.

Boundary: the identification of these polynomials with the Hilbert series of the (augmented)
Chow ring of `U_{r,n}`, i.e. with the Feichtner--Yuzvinsky chain formula (respectively the
flat-contraction formula `∑_{k<r} C(n,k) X^k H_{U_{r-k,n-k}} + X^r`), is not formalized; it was
checked by exact computation for `r ≤ 5`, `r ≤ n ≤ r + 3`.  The real-rootedness proofs do not
assume it: they derive the conclusion from the explicit formulas.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted
namespace UniformChow

/-- The polynomial `g_{r,n} = ∑_{s < r} C(n,s) X^s`. -/
def uniformPolynomial (r n : ℕ) : ℝ[X] :=
  ∑ s ∈ range r, C ((n.choose s : ℕ) : ℝ) * X ^ s

/-- The magic-basis coordinates `C(n-r+p, p)` of `g_{r,n}`. -/
def magicWeight (r n p : ℕ) : ℝ := (((n - r + p).choose p : ℕ) : ℝ)

theorem magicWeight_nonneg (r n p : ℕ) : 0 ≤ magicWeight r n p := by
  unfold magicWeight
  positivity

/-- The nonnegative magic-basis expansion of `g_{r,n}`. -/
theorem uniformPolynomial_eq_magicExpansion {r n : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) :
    uniformPolynomial r n =
      DerangementTransform.magicExpansion (r - 1) (magicWeight r n) := by
  obtain ⟨d, rfl⟩ : ∃ d, r = d + 1 := ⟨r - 1, by lia⟩
  rw [Nat.add_sub_cancel]
  unfold uniformPolynomial DerangementTransform.magicExpansion
  ext s
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_X_pow_mul', mul_ite, mul_one,
    mul_zero]
  have hc : ∀ m k : ℕ, ((1 + X : ℝ[X]) ^ m).coeff k = (m.choose k : ℝ) := by
    intro m k
    rw [add_comm, coeff_X_add_one_pow]
  simp only [hc]
  rw [sum_ite_eq (range (d + 1)) s]
  by_cases hsd : s ≤ d
  · have hs : s ∈ range (d + 1) := by simpa [Nat.lt_succ_iff] using hsd
    simp only [hs, ↓reduceIte]
    have h := BinderVecchi.convSum_eq (n - (d + 1)) (d - s) s
    unfold BinderVecchi.convSum at h
    have h' : ((∑ p ∈ range (s + 1), (n - (d + 1) + p).choose p *
        (d - s + s - p).choose (s - p) : ℕ) : ℝ) = (n.choose s : ℝ) := by
      rw [h]
      congr 2
      lia
    push_cast at h'
    rw [← h']
    have hsub : range (s + 1) ⊆ range (d + 1) := range_subset_range.mpr (by lia)
    rw [← sum_subset hsub (fun p _ hp => by
      have : ¬ p ≤ s := by simpa [Nat.lt_succ_iff] using hp
      simp [this])]
    refine sum_congr rfl fun p hp => ?_
    have hp' : p ≤ s := by simpa [Nat.lt_succ_iff] using hp
    simp only [hp', ↓reduceIte, magicWeight]
    rw [show d - s + s - p = d - p by lia]
  · have hs : s ∉ range (d + 1) := by simpa [Nat.lt_succ_iff] using hsd
    simp only [hs, ↓reduceIte]
    symm
    refine sum_eq_zero fun p hp => ?_
    have hp' : p ≤ d := by simpa [Nat.lt_succ_iff] using hp
    have hps : p ≤ s := by lia
    simp only [hps, ↓reduceIte]
    rw [Nat.choose_eq_zero_of_lt (n := d - p) (k := s - p) (by lia)]
    simp

/-- The first entry of the Chow staircase row transform of a reflection-interlacing sequence
is a Pólya frequency polynomial. -/
theorem isPF_chowS_head {N : ℕ} {fs : List ℝ[X]}
    (h : BrandenVecchi.IsReflectionInterlacingSeq N fs) :
    IsPFPolynomial (X * chowS N fs.sum + fs.sum) := by
  have hT := h.chowRowTransform
  have hmem : X * chowS N fs.sum + fs.sum ∈ BrandenVecchi.chowRowTransform N fs := by
    unfold BrandenVecchi.chowRowTransform
    exact List.mem_map.mpr ⟨0, by simp, by simp⟩
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
  · exact hT.closedSequence.nonnegCoeffs _ (by simp [BrandenVecchi.reflectionClosure, hmem])
  · by_cases hzero : X * chowS N fs.sum + fs.sum = 0
    · exact Or.inl hzero
    · exact Or.inr <| hT.closedSequence.splits (by simp [BrandenVecchi.reflectionClosure, hmem])
        hzero

private def scaledRow (E : ℕ → ℝ[X]) (d : ℕ) (c : ℕ → ℝ) : List ℝ[X] :=
  (List.range (d + 1)).map fun k => C (c k) * E k

private theorem scaledRow_sum (E : ℕ → ℝ[X]) (d : ℕ) (c : ℕ → ℝ) :
    (scaledRow E d c).sum = ∑ k ∈ range (d + 1), C (c k) * E k := by
  rw [scaledRow, List.sum_map_range]

private theorem scaledRow_reflectionInterlacing {E : ℕ → ℝ[X]} {d N : ℕ} {c : ℕ → ℝ}
    (hc : ∀ k, k ≤ d → 0 ≤ c k)
    (h : BrandenVecchi.IsReflectionInterlacingSeq N ((List.range (d + 1)).map E)) :
    BrandenVecchi.IsReflectionInterlacingSeq N (scaledRow E d c) := by
  refine h.nonnegScalarMultiples ?_
  rw [scaledRow, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun j hj =>
    IsNonnegScalarMultiple.C_mul _ (hc j (by simpa [Nat.lt_succ_iff] using hj))

/-- The Chow polynomial of the uniform matroid `U_{r,n}`: `P + X * S_{r-1}(P)` with
`P = D(g_{r,n})`, the Brändén--Vecchi Chow polynomial of the row `(C(n,0), …, C(n,r-1), 1)`. -/
def chowUniform (r n : ℕ) : ℝ[X] :=
  DerangementTransform.transform (uniformPolynomial r n) +
    X * chowS (r - 1) (DerangementTransform.transform (uniformPolynomial r n))

/-- The augmented Chow polynomial of the uniform matroid `U_{r,n}`: `Q + X * S_r(Q)` with
`Q = A°(g_{r,n})`. -/
def augChowUniform (r n : ℕ) : ℝ[X] :=
  EulerianTransform.transform (uniformPolynomial r n) +
    X * chowS r (EulerianTransform.transform (uniformPolynomial r n))

/-- The Chow polynomial of `U_{r,n}` is a Pólya frequency polynomial. -/
theorem isPFPolynomial_chowUniform {r n : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) :
    IsPFPolynomial (chowUniform r n) := by
  obtain ⟨d, rfl⟩ : ∃ d, r = d + 1 := ⟨r - 1, by lia⟩
  have hrow : BrandenVecchi.IsReflectionInterlacingSeq d
      ((List.range (d + 1)).map fun k =>
        DerangementTransform.transform (X ^ k * (1 + X) ^ (d - k))) := by
    have := BrandenVecchi.resolvedChowRow_reflectionInterlacing
      DerangementTransform.pascalResolution d
    unfold BrandenVecchi.resolvedChowRow BrandenVecchi.resolvedChowDerangement at this
    simpa [DerangementTransform.chowDerangedTransform_pascal,
      DerangementTransform.pascalResolution] using this
  have hscaled := scaledRow_reflectionInterlacing
    (c := magicWeight (d + 1) n) (fun k _ => magicWeight_nonneg _ _ _) hrow
  have hsum := scaledRow_sum
    (fun k => DerangementTransform.transform (X ^ k * (1 + X) ^ (d - k))) d
    (magicWeight (d + 1) n)
  have hP : (scaledRow (fun k => DerangementTransform.transform (X ^ k * (1 + X) ^ (d - k))) d
      (magicWeight (d + 1) n)).sum =
        DerangementTransform.transform (uniformPolynomial (d + 1) n) := by
    rw [hsum, uniformPolynomial_eq_magicExpansion hr hrn, Nat.add_sub_cancel,
      DerangementTransform.magicExpansion, map_sum]
    simp [DerangementTransform.transform_C_mul]
  have := isPF_chowS_head hscaled
  rw [hP] at this
  rw [chowUniform, Nat.add_sub_cancel]
  rw [add_comm]
  exact this

/-- The augmented Chow polynomial of `U_{r,n}` is a Pólya frequency polynomial. -/
theorem isPFPolynomial_augChowUniform {r n : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) :
    IsPFPolynomial (augChowUniform r n) := by
  obtain ⟨d, rfl⟩ : ∃ d, r = d + 1 := ⟨r - 1, by lia⟩
  have hrow := EulerianTransform.row_reflectionInterlacing d
  have hscaled := scaledRow_reflectionInterlacing (c := magicWeight (d + 1) n)
    (fun k _ => magicWeight_nonneg _ _ _) (by simpa [EulerianTransform.row] using hrow)
  have hsum := scaledRow_sum (EulerianTransform.basisImage d) d (magicWeight (d + 1) n)
  have hQ : (scaledRow (EulerianTransform.basisImage d) d (magicWeight (d + 1) n)).sum =
      EulerianTransform.transform (uniformPolynomial (d + 1) n) := by
    rw [hsum, uniformPolynomial_eq_magicExpansion hr hrn, Nat.add_sub_cancel,
      show DerangementTransform.magicExpansion d (magicWeight (d + 1) n) =
        EulerianTransform.magicExpansion d (magicWeight (d + 1) n) from rfl,
      EulerianTransform.transform_magicExpansion]
  have := isPF_chowS_head hscaled
  rw [hQ] at this
  rw [augChowUniform, add_comm]
  exact this

private theorem coeff_zero_chowS_term (N : ℕ) (p : ℝ[X]) : (X * chowS N p).coeff 0 = 0 := by
  simp

/-- The constant coefficient of `D(g_{r,n})` is `1`. -/
theorem coeff_zero_transform_uniformPolynomial {r n : ℕ} (hr : 1 ≤ r) :
    (DerangementTransform.transform (uniformPolynomial r n)).coeff 0 = 1 := by
  unfold uniformPolynomial
  rw [map_sum, finsetSum_coeff, sum_eq_single 0]
  · simp
  · intro j _ hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by lia⟩
    have h0 : (sturmDerangementsExc (m + 1)).coeff 0 = 0 :=
      Polynomial.X_dvd_iff.mp (X_dvd_sturmDerangementsExc (m + 1))
    rw [DerangementTransform.transform_C_mul, DerangementTransform.transform_X_pow]
    simp [DerangementTransform.polynomial, h0]
  · intro h
    exact absurd (mem_range.mpr (by lia)) h

/-- The constant coefficient of `A°(g_{r,n})` is `1`. -/
theorem coeff_zero_eulerianTransform_uniformPolynomial {r n : ℕ} (hr : 1 ≤ r) :
    (EulerianTransform.transform (uniformPolynomial r n)).coeff 0 = 1 := by
  unfold uniformPolynomial
  rw [map_sum, finsetSum_coeff, sum_eq_single 0]
  · simp
  · intro j _ hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by lia⟩
    rw [EulerianTransform.transform_C_mul, EulerianTransform.transform_X_pow]
    simp [EulerianTransform.image]
  · intro h
    exact absurd (mem_range.mpr (by lia)) h

theorem chowUniform_ne_zero {r n : ℕ} (hr : 1 ≤ r) : chowUniform r n ≠ 0 := by
  intro h
  have := congrArg (fun p => p.coeff 0) h
  simp only [chowUniform, coeff_add, coeff_zero_chowS_term, add_zero,
    coeff_zero_transform_uniformPolynomial hr, coeff_zero] at this
  exact one_ne_zero this

theorem augChowUniform_ne_zero {r n : ℕ} (hr : 1 ≤ r) : augChowUniform r n ≠ 0 := by
  intro h
  have := congrArg (fun p => p.coeff 0) h
  simp only [augChowUniform, coeff_add, coeff_zero_chowS_term, add_zero,
    coeff_zero_eulerianTransform_uniformPolynomial hr, coeff_zero] at this
  exact one_ne_zero this

/-- **Binder--Vecchi, Theorem 1.4 for `i = 0`**: the Chow polynomial of the uniform matroid
`U_{r,n}` is real-rooted. -/
theorem isRealRooted_chowUniform {r n : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) :
    chowUniform r n ≠ 0 ∧ (chowUniform r n).Splits :=
  ⟨chowUniform_ne_zero hr, ((isPFPolynomial_chowUniform hr hrn).ne_zero_and_splits
    (chowUniform_ne_zero hr)).2⟩

/-- **Binder--Vecchi, Theorem 1.6 for `i = 0`**: the augmented Chow polynomial of the uniform
matroid `U_{r,n}` is real-rooted. -/
theorem isRealRooted_augChowUniform {r n : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) :
    augChowUniform r n ≠ 0 ∧ (augChowUniform r n).Splits :=
  ⟨augChowUniform_ne_zero hr, ((isPFPolynomial_augChowUniform hr hrn).ne_zero_and_splits
    (augChowUniform_ne_zero hr)).2⟩

/-! ## The derangement formula for the Chow polynomial -/

private theorem natDegree_derangement_le (j : ℕ) :
    (DerangementTransform.polynomial j).natDegree ≤ j := by
  cases j with
  | zero => simp
  | succ j => exact natDegree_le_sturmDerangementsExc (j + 1)

private theorem reflect_derangement_of_le {j N : ℕ} (hj : j ≤ N) :
    (DerangementTransform.polynomial j).reflect N =
      DerangementTransform.polynomial j * X ^ (N - j) := by
  have h : (DerangementTransform.polynomial j).reflect j =
      DerangementTransform.polynomial j := by
    cases j with
    | zero => simp
    | succ j => exact reflect_sturmDerangementsExc (j + 1)
  have h2 := reflect_add_right_of_reflect (N - j) (natDegree_derangement_le j) h
  rwa [show j + (N - j) = N by lia] at h2

/-- The deranged image of `g_{r,n}` is `∑_{k<r} C(n,k) d_k`. -/
theorem transform_uniformPolynomial (r n : ℕ) :
    DerangementTransform.transform (uniformPolynomial r n) =
      ∑ k ∈ range r, C ((n.choose k : ℕ) : ℝ) * DerangementTransform.polynomial k := by
  unfold uniformPolynomial
  rw [map_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [DerangementTransform.transform_C_mul, DerangementTransform.transform_X_pow]

/-- **The derangement formula** (Ferroni--Matherne--Stevens--Vecchi): the Chow polynomial of
`U_{r,n}` is `∑_{k<r} C(n,k) d_k (1 + X + ⋯ + X^{r-1-k})`. -/
theorem chowUniform_eq {r n : ℕ} (hr : 1 ≤ r) :
    chowUniform r n =
      ∑ k ∈ range r, C ((n.choose k : ℕ) : ℝ) *
        (DerangementTransform.polynomial k * ∑ j ∈ range (r - k), X ^ j) := by
  set P := DerangementTransform.transform (uniformPolynomial r n) with hPdef
  have hP : P = ∑ k ∈ range r,
      C ((n.choose k : ℕ) : ℝ) * DerangementTransform.polynomial k :=
    transform_uniformPolynomial r n
  have hdeg : P.natDegree ≤ r - 1 := by
    rw [hP]
    refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    have := mem_range.mp hk
    exact (natDegree_C_mul_le _ _).trans ((natDegree_derangement_le k).trans (by lia))
  have hrefl : P.reflect (r - 1) = ∑ k ∈ range r, C ((n.choose k : ℕ) : ℝ) *
      (DerangementTransform.polynomial k * X ^ (r - 1 - k)) := by
    rw [hP, reflect_finset_sum_C_mul]
    exact sum_congr rfl fun k hk => by
      rw [reflect_derangement_of_le (by have := mem_range.mp hk; lia)]
  have hS : chowS (r - 1) P = ∑ k ∈ range r, C ((n.choose k : ℕ) : ℝ) *
      (DerangementTransform.polynomial k * ∑ j ∈ range (r - 1 - k), X ^ j) := by
    apply (monic_X_sub_C (1 : ℝ)).isRegular.left
    change (X - 1) * _ = (X - 1) * _
    rw [X_sub_one_mul_chowS _ _ hdeg, hrefl, hP, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    have := geom_sum_mul (X : ℝ[X]) (r - 1 - k)
    linear_combination (C ((n.choose k : ℕ) : ℝ) * DerangementTransform.polynomial k) * (-this)
  unfold chowUniform
  rw [← hPdef, hS, hP, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  rw [show r - k = (r - 1 - k) + 1 by lia, geom_sum_succ]
  ring

/-! ## The reflection identity for the augmented Chow polynomial -/

private theorem natDegree_eulerian_le (s : ℕ) : (BinderVecchi.eulerian s).natDegree ≤ s := by
  cases s with
  | zero => simp [BinderVecchi.eulerian]
  | succ s => exact (generalizedEulerian_natDegree 1 s).le.trans (Nat.le_succ s)

private theorem reflect_eulerian (s : ℕ) :
    (BinderVecchi.eulerian s).reflect s = EulerianTransform.image s := by
  cases s with
  | zero => simp [BinderVecchi.eulerian, EulerianTransform.image]
  | succ s =>
    simp only [BinderVecchi.eulerian, EulerianTransform.image]
    rw [reflect_add_right_of_reflect 1 (generalizedEulerian_natDegree 1 s).le
      (generalizedEulerian_one_reflect s), pow_one, mul_comm]

private theorem reflect_image {s r : ℕ} (hs : s ≤ r) :
    (EulerianTransform.image s).reflect r = X ^ (r - s) * BinderVecchi.eulerian s := by
  have h := reflect_mul (X ^ (r - s)) (BinderVecchi.eulerian s) (F := r - s) (G := s)
    (natDegree_X_pow_le _) (natDegree_eulerian_le s)
  rw [show r - s + s = r by lia, reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero,
    reflect_eulerian, one_mul] at h
  rw [← h, reflect_reflect]

private theorem natDegree_image_le' (s : ℕ) : (EulerianTransform.image s).natDegree ≤ s := by
  cases s with
  | zero => simp [EulerianTransform.image]
  | succ s =>
    have h1 : (X : ℝ[X]).natDegree ≤ 1 := natDegree_X_le
    have h2 := (generalizedEulerian_natDegree 1 s).le
    rw [EulerianTransform.image]
    exact natDegree_mul_le.trans (by lia)

/-- The Eulerian image of `g_{r,n}` is `1 + ∑_{1 ≤ s < r} C(n,s) X A_s`. -/
theorem transform_eulerian_uniformPolynomial (r n : ℕ) :
    EulerianTransform.transform (uniformPolynomial r n) =
      ∑ s ∈ range r, C ((n.choose s : ℕ) : ℝ) * EulerianTransform.image s := by
  unfold uniformPolynomial
  rw [map_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [EulerianTransform.transform_C_mul, EulerianTransform.transform_X_pow]

/-- With `Q = A°(g_{r,n})` and `R = ∑_{s<r} C(n,s) X^{r-s} A_s` (the reflection of `Q`), the
augmented Chow polynomial `H` satisfies `(X - 1) H = X R - Q`. -/
theorem augChowUniform_mul_sub_one (r n : ℕ) :
    (X - 1) * augChowUniform r n =
      X * (∑ s ∈ range r, C ((n.choose s : ℕ) : ℝ) *
        (X ^ (r - s) * BinderVecchi.eulerian s)) -
        EulerianTransform.transform (uniformPolynomial r n) := by
  set Q := EulerianTransform.transform (uniformPolynomial r n) with hQdef
  have hQ : Q = _ := transform_eulerian_uniformPolynomial r n
  have hdeg : Q.natDegree ≤ r := by
    rw [hQ]
    refine natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
    have := mem_range.mp hs
    exact (natDegree_C_mul_le _ _).trans ((natDegree_image_le' s).trans (by lia))
  have hrefl : Q.reflect r = ∑ s ∈ range r, C ((n.choose s : ℕ) : ℝ) *
      (X ^ (r - s) * BinderVecchi.eulerian s) := by
    rw [hQ, reflect_finset_sum_C_mul]
    exact sum_congr rfl fun s hs => by
      rw [reflect_image (by have := mem_range.mp hs; lia)]
  rw [← hrefl, augChowUniform, ← hQdef]
  have := X_sub_one_mul_chowS r Q hdeg
  linear_combination X * this

end UniformChow
end RealRooted
