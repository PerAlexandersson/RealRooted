import RealRooted.JensenPencilPositiveContraction
import RealRooted.RootContinuity

/-!
# Jensen-pencil contraction

Positive translation regularizes vanishing constant terms.  Compatibility of
the translated Schur--Szegő endpoints follows from the positive contraction,
and coefficientwise closure of the PF cone returns the unshifted pencil.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted

/-! ## Positive translation and PF closure -/

/-- Positive translation preserves a nonzero PF polynomial and makes its
constant coefficient positive. -/
theorem IsPFPolynomial.comp_X_add_C_and_coeff_zero_pos
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : p ≠ 0)
    {eps : ℝ} (heps : 0 < eps) :
    IsPFPolynomial (p.comp (X + C eps)) ∧
      0 < (p.comp (X + C eps)).coeff 0 := by
  constructor
  · simpa using hp.comp_C_mul_X_add_C (a := 1) (d := eps) zero_lt_one heps.le
  · simpa [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp] using
      eval_pos_of_hasNonnegCoeffs hp.hasNonnegCoeffs hp0 heps

/-- Every coefficient of a translated polynomial varies continuously with the
translation parameter. -/
theorem continuous_coeff_comp_X_add_C (p : ℝ[X]) (i : ℕ) :
    Continuous fun eps : ℝ ↦ (p.comp (X + C eps)).coeff i := by
  rw [show (fun eps : ℝ ↦ (p.comp (X + C eps)).coeff i) =
      fun eps : ℝ ↦ ∑ n ∈ p.support,
        (C (p.coeff n) * (X + C eps) ^ n).coeff i by
    funext eps
    rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def,
      Polynomial.finsetSum_coeff]]
  apply continuous_finsetSum p.support
  intro n _hn
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  fun_prop

/-- A coefficientwise continuous curve of PF sequences for positive parameters
has a PF value at zero. -/
theorem IsPolyaFreqSeq.of_continuous_curve
    {a : ℕ → ℝ} {u : ℝ → ℕ → ℝ}
    (hu : ∀ k : ℕ, Continuous (fun eps : ℝ ↦ u eps k))
    (hu0 : ∀ k : ℕ, u 0 k = a k)
    (hpos : ∀ {eps : ℝ}, 0 < eps → IsPolyaFreqSeq (u eps)) :
    IsPolyaFreqSeq a := by
  intro n rows cols hrows hcols
  let D : ℝ → ℝ := fun eps ↦
    ((toeplitz (u eps)).submatrix rows cols).det
  have hD_cont : Continuous D := by
    simp only [D, Matrix.det_apply]
    apply continuous_finsetSum
    intro σ _hσ
    apply Continuous.const_smul
    apply continuous_finsetProd
    intro i _hi
    by_cases hle : cols i ≤ rows (σ i)
    · simp only [Matrix.submatrix_apply, toeplitz_apply, hle, ↓reduceIte]
      exact hu (rows (σ i) - cols i)
    · simp only [Matrix.submatrix_apply, toeplitz_apply, hle, ↓reduceIte]
      change Continuous (fun _ : ℝ ↦ (0 : ℝ))
      exact continuous_const
  have hD_nonneg : ∀ eps : ℝ, 0 < eps → 0 ≤ D eps :=
    fun eps heps ↦ hpos heps hrows hcols
  have hD_lim :
      Tendsto D (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (D 0)) :=
    hD_cont.continuousAt.continuousWithinAt
  have hzero_lim : Tendsto (fun _ : ℝ ↦ (0 : ℝ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_const_nhds
  have hD0 : 0 ≤ D 0 :=
    le_of_tendsto_of_tendsto hzero_lim hD_lim (by
      filter_upwards [self_mem_nhdsWithin] with eps heps
      exact hD_nonneg eps heps)
  simpa [D, toeplitz, hu0] using hD0

/-! ## Translated Jensen pencils -/

private def jensenTranslateCombination (d : ℕ) (A B p : ℝ[X])
    (a b eps : ℝ) : ℝ[X] :=
  C a * schurSzegoComp d (A.comp (X + C eps)) (p.comp (X + C eps)) +
    C b * (X * schurSzegoComp d (B.comp (X + C eps))
      (p.comp (X + C eps)))

@[simp] private theorem jensenTranslateCombination_zero
    (d : ℕ) (A B p : ℝ[X]) (a b : ℝ) :
    jensenTranslateCombination d A B p a b 0 =
      C a * schurSzegoComp d A p +
        C b * (X * schurSzegoComp d B p) := by
  simp [jensenTranslateCombination]

private theorem continuous_coeff_jensenTranslateCombination
    (d : ℕ) (A B p : ℝ[X]) (a b : ℝ) (i : ℕ) :
    Continuous
      (fun eps : ℝ ↦ (jensenTranslateCombination d A B p a b eps).coeff i) := by
  have hschur (f : ℝ[X]) (k : ℕ) :
      Continuous fun eps : ℝ ↦
        (schurSzegoComp d (f.comp (X + C eps))
          (p.comp (X + C eps))).coeff k := by
    simp only [coeff_schurSzegoComp]
    split
    · exact ((continuous_coeff_comp_X_add_C f k).mul
        (continuous_coeff_comp_X_add_C p k)).div_const _
    · change Continuous (fun _ : ℝ ↦ (0 : ℝ))
      exact continuous_const
  simp only [jensenTranslateCombination, coeff_add, coeff_C_mul]
  apply Continuous.add (Continuous.const_mul (hschur A i) a)
  cases i with
  | zero =>
      simpa using (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℝ)))
  | succ i =>
      simpa [coeff_X_mul] using Continuous.const_mul (hschur B i) b

/-- A positive threshold lies strictly above every root of a PF polynomial. -/
theorem IsPFPolynomial.rootCountAtOrAbove_eq_zero_of_pos
    {p : ℝ[X]} (hp : IsPFPolynomial p) {x : ℝ} (hx : 0 < x) :
    LiuOppositeSigns.rootCountAtOrAbove p x = 0 := by
  exact LiuOppositeSigns.rootCountAtOrAbove_eq_zero_of_forall_roots_lt
    (fun r hr ↦ lt_of_le_of_lt (hp.roots_nonpos r hr) hx)

/-- Translating both PF endpoints left by the same positive amount, while
retaining the explicit `X` on the second endpoint, preserves the Jensen
root-count certificate. -/
theorem rootCountCompatible_jensen_translate
    {A B : ℝ[X]} (hA : IsPFPolynomial A) (hB : IsPFPolynomial B)
    (hB0 : B ≠ 0)
    (hcount : LiuOppositeSigns.RootCountCompatible A (X * B))
    {eps : ℝ} (heps : 0 < eps) :
    LiuOppositeSigns.RootCountCompatible
      (A.comp (X + C eps)) (X * B.comp (X + C eps)) := by
  have hTB_const : 0 < (B.comp (X + C eps)).coeff 0 :=
    (hB.comp_X_add_C_and_coeff_zero_pos hB0 heps).2
  have hTB0 : B.comp (X + C eps) ≠ 0 := by
    intro hzero
    exact hTB_const.ne' (by rw [hzero]; simp)
  intro x
  rw [LiuOppositeSigns.rootCountAtOrAbove_X_mul hTB0 x,
    LiuOppositeSigns.rootCountAtOrAbove_comp_X_add_C A eps x,
    LiuOppositeSigns.rootCountAtOrAbove_comp_X_add_C B eps x]
  by_cases hx : x ≤ 0
  · by_cases hs : x + eps ≤ 0
    · have hs_bound := hcount (x + eps)
      rw [LiuOppositeSigns.rootCountAtOrAbove_X_mul hB0 (x + eps),
        if_pos hs] at hs_bound
      simpa [hx] using hs_bound
    · have hs_pos : 0 < x + eps := lt_of_not_ge hs
      rw [hA.rootCountAtOrAbove_eq_zero_of_pos hs_pos,
        hB.rootCountAtOrAbove_eq_zero_of_pos hs_pos]
      simp [hx]
  · have hx_pos : 0 < x := lt_of_not_ge hx
    have hs_pos : 0 < x + eps := by linarith
    rw [hA.rootCountAtOrAbove_eq_zero_of_pos hs_pos,
      hB.rootCountAtOrAbove_eq_zero_of_pos hs_pos]
    simp [hx]

/-- Positive translation preserves Jensen-pencil compatibility. -/
theorem compatible_jensen_translate
    {A B : ℝ[X]} (hA : IsPFPolynomial A) (hB : IsPFPolynomial B)
    (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hcompat : Compatible A (X * B))
    {eps : ℝ} (heps : 0 < eps) :
    Compatible (A.comp (X + C eps)) (X * B.comp (X + C eps)) := by
  have hcount : LiuOppositeSigns.RootCountCompatible A (X * B) :=
    LiuOppositeSigns.RootCountCompatible.of_compatible hcompat
      (hA.hasNonnegCoeffs.pos_leadingCoeff hA0)
      (hB.X_mul.hasNonnegCoeffs.pos_leadingCoeff
        (mul_ne_zero X_ne_zero hB0))
  have hTA := hA.comp_X_add_C_and_coeff_zero_pos hA0 heps
  have hTB := hB.comp_X_add_C_and_coeff_zero_pos hB0 heps
  have hTA_ne : A.comp (X + C eps) ≠ 0 := by
    intro hzero
    exact hTA.2.ne' (by rw [hzero]; simp)
  have hTB_ne : B.comp (X + C eps) ≠ 0 := by
    intro hzero
    exact hTB.2.ne' (by rw [hzero]; simp)
  apply LiuOppositeSigns.RootCountCompatible.compatible_of_pf
    (p := A.comp (X + C eps)) (q := X * B.comp (X + C eps))
    _ hTA.1 hTB.1.X_mul hTA_ne (mul_ne_zero X_ne_zero hTB_ne)
  exact rootCountCompatible_jensen_translate hA hB hB0 hcount heps

/-- Coefficientwise PF closure transfers compatibility of all positive
translations back to the unshifted Jensen pencil. -/
private theorem compatible_jensen_output_of_translate_core
    {d : ℕ} {A B p : ℝ[X]}
    (hA : IsPFPolynomial A) (hB : IsPFPolynomial B)
    (hp : IsPFPolynomial p)
    (hAdeg : A.natDegree ≤ d) (hBdeg : B.natDegree ≤ d)
    (hpdeg : p.natDegree ≤ d)
    (hcore : ∀ {eps : ℝ}, 0 < eps →
      Compatible
        (schurSzegoComp d (A.comp (X + C eps)) (p.comp (X + C eps)))
        (X * schurSzegoComp d (B.comp (X + C eps))
          (p.comp (X + C eps)))) :
    Compatible (schurSzegoComp d A p) (X * schurSzegoComp d B p) := by
  intro a b ha hb
  let out := C a * schurSzegoComp d A p + C b * (X * schurSzegoComp d B p)
  have hout_pf : IsPFPolynomial out := by
    apply IsPFPolynomial.of_polyaFreqSeq
    apply IsPolyaFreqSeq.of_continuous_curve
      (u := fun eps k ↦ (jensenTranslateCombination d A B p a b eps).coeff k)
    · exact continuous_coeff_jensenTranslateCombination d A B p a b
    · intro k
      simp [out]
    · intro eps heps
      have hTA : IsPFPolynomial (A.comp (X + C eps)) := by
        simpa using
          hA.comp_C_mul_X_add_C (a := 1) (d := eps) zero_lt_one heps.le
      have hTB : IsPFPolynomial (B.comp (X + C eps)) := by
        simpa using
          hB.comp_C_mul_X_add_C (a := 1) (d := eps) zero_lt_one heps.le
      have hTp : IsPFPolynomial (p.comp (X + C eps)) := by
        simpa using
          hp.comp_C_mul_X_add_C (a := 1) (d := eps) zero_lt_one heps.le
      have hUA := hTA.schurSzegoComp hTp
        (by simpa [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C]
          using hAdeg)
        (by simpa [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C]
          using hpdeg)
      have hVB := (hTB.schurSzegoComp hTp
        (by simpa [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C]
          using hBdeg)
        (by simpa [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C]
          using hpdeg)).X_mul
      have htranslated : IsPFPolynomial
          (C a * schurSzegoComp d (A.comp (X + C eps))
              (p.comp (X + C eps)) +
            C b * (X * schurSzegoComp d (B.comp (X + C eps))
              (p.comp (X + C eps)))) := by
        apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
          ((nonnegCoeffs_C_mul ha hUA.hasNonnegCoeffs).add
            (nonnegCoeffs_C_mul hb hVB.hasNonnegCoeffs))
        rcases hcore heps a b ha hb with hzero | hsplits
        · exact Or.inl hzero
        · exact Or.inr hsplits.2
      simpa [jensenTranslateCombination] using htranslated.to_sequence
  by_cases hzero : out = 0
  · left
    simpa [out] using hzero
  · right
    refine ⟨?_, hout_pf.eq_zero_or_splits.resolve_left hzero⟩
    simpa [out] using hzero

/-- Simultaneous Schur--Szegő composition by a PF polynomial preserves
Jensen-pencil compatibility. -/
theorem schurSzegoPreservesJensenPencilCompatibility
    {d : ℕ} {A B p : ℝ[X]}
    (hA : IsPFPolynomial A) (hXB : IsPFPolynomial (X * B))
    (hp : IsPFPolynomial p)
    (hAdeg : A.natDegree ≤ d) (hBdeg : B.natDegree ≤ d)
    (hpdeg : p.natDegree ≤ d)
    (hcompat : Compatible A (X * B)) :
    Compatible (schurSzegoComp d A p) (X * schurSzegoComp d B p) := by
  have hB : IsPFPolynomial B := isPFPolynomial_of_X_mul hXB
  by_cases hA0 : A = 0
  · subst A
    simp only [schurSzegoComp_zero_left]
    apply Compatible.zero_left_of_eq_zero_or_splits
    exact (hB.schurSzegoComp hp hBdeg hpdeg).X_mul.eq_zero_or_splits
  by_cases hB0 : B = 0
  · subst B
    simp only [schurSzegoComp_zero_left, mul_zero]
    apply Compatible.zero_right_of_eq_zero_or_splits
    exact (hA.schurSzegoComp hp hAdeg hpdeg).eq_zero_or_splits
  by_cases hp0 : p = 0
  · subst p
    simpa using
      (Compatible.zero_left_of_eq_zero_or_splits (p := (0 : ℝ[X]))
        (Or.inl rfl))
  apply compatible_jensen_output_of_translate_core hA hB hp
    hAdeg hBdeg hpdeg
  intro eps heps
  have hTA := hA.comp_X_add_C_and_coeff_zero_pos hA0 heps
  have hTB := hB.comp_X_add_C_and_coeff_zero_pos hB0 heps
  have hTp := hp.comp_X_add_C_and_coeff_zero_pos hp0 heps
  apply compatible_schurSzego_jensen_of_pos_coeff_zero hTA.1 hTB.1 hTp.1
  · simpa [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C] using hAdeg
  · simpa [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C] using hBdeg
  · simpa [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C] using hpdeg
  · exact hTA.2
  · exact hTB.2
  · exact hTp.2
  · exact compatible_jensen_translate hA hB hA0 hB0 hcompat heps

end RealRooted
