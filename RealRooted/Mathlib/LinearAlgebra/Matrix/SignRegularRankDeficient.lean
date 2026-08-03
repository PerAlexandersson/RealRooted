import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularVariation

/-!
# Rank-deficient sign-consistent matrices

This file develops the rank-deficient induction in Karlin, *Total Positivity*,
Volume I, Chapter V, Section 1, Theorem 1.3. The first lemmas formalize the
selected-row kernel perturbation in equations (1.1) on printed pages 221--222.
-/

/-- A finite matrix of rank `r` has a nonzero `r`-minor with increasingly
ordered row and column selectors. -/
theorem Matrix.exists_ordered_minor_ne_zero_of_rank_eq
    {R : Type*} [Field R] {n m r : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (hrank : A.rank = r) :
    ∃ rows : Fin r → Fin n, ∃ cols : Fin r → Fin m,
      StrictMono rows ∧ StrictMono cols ∧
        (A.submatrix rows cols).det ≠ 0 := by
  obtain ⟨κ, a, ha, hspan, hli⟩ :=
    exists_linearIndependent' R A.col
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = r := by
    calc
      Fintype.card κ =
          Module.finrank R (Submodule.span R (Set.range (A.col ∘ a))) :=
        (finrank_span_eq_card hli).symm
      _ = Module.finrank R (Submodule.span R (Set.range A.col)) := by
        rw [hspan]
      _ = A.rank := (Matrix.rank_eq_finrank_span_cols A).symm
      _ = r := hrank
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let f : Fin r → Fin m := a ∘ e
  have hf : Function.Injective f := ha.comp e.injective
  let B : Matrix (Fin n) (Fin r) R := A.submatrix id f
  have hB : Function.Injective B.mulVec := by
    rw [Matrix.mulVec_injective_iff]
    change LinearIndependent R (A.col ∘ f)
    simpa only [f, Function.comp_assoc] using hli.comp e e.injective
  obtain ⟨rows, hrows, hdet⟩ :=
    Matrix.exists_ordered_minor_ne_zero_of_mulVec_injective
      B hB id strictMono_id
  have hdetf : (A.submatrix rows f).det ≠ 0 := by
    simpa only [B, Matrix.submatrix_submatrix, Function.id_comp,
      Function.comp_id] using hdet
  obtain ⟨s, p, hp⟩ :=
    Set.powersetCard.exists_orderEmb_comp_perm_eq_of_injective f hf
  let cols : Fin r ↪o Fin m := Set.powersetCard.ofFinEmbEquiv.symm s
  refine ⟨rows, cols, hrows, cols.strictMono, ?_⟩
  intro hzero
  apply hdetf
  have hmatrix :
      A.submatrix rows f =
        (A.submatrix rows cols).submatrix id p := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq]
    rw [hp j]
  rw [hmatrix, Matrix.det_permute', hzero, mul_zero]

/-- Karlin's signed row-cofactor vector of a singular square matrix lies in
its kernel. The retained-row equations come from the rectangular alternating
minor identity; Laplace expansion supplies the omitted-row equation. -/
theorem Matrix.mulVec_signedRowCofactor_eq_zero_of_det_eq_zero
    {R : Type*} [CommRing R] {k : ℕ}
    (B : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (i0 : Fin (k + 1)) (hdet : B.det = 0) :
    B.mulVec (fun j => (-1 : R) ^ (i0 + j : ℕ) *
      (B.submatrix i0.succAbove j.succAbove).det) = 0 := by
  let C : Matrix (Fin k) (Fin (k + 1)) R :=
    B.submatrix i0.succAbove id
  have hminor (j : Fin (k + 1)) :
      ((C.transpose).submatrix j.succAbove id).det =
        (B.submatrix i0.succAbove j.succAbove).det := by
    rw [← Matrix.det_transpose]
    rfl
  let z0 : Fin (k + 1) → R := fun j =>
    (-1 : R) ^ (j : ℕ) * (B.submatrix i0.succAbove j.succAbove).det
  let z : Fin (k + 1) → R := fun j =>
    (-1 : R) ^ (i0 + j : ℕ) * (B.submatrix i0.succAbove j.succAbove).det
  have hremoved0 : C.mulVec z0 = 0 := by
    have hkernel :=
      Matrix.transpose_mulVec_alternating_det_submatrix_succAbove C.transpose
    rw [Matrix.transpose_transpose] at hkernel
    simp_rw [hminor] at hkernel
    simpa only [z0] using hkernel
  have hz : z = (-1 : R) ^ (i0 : ℕ) • z0 := by
    funext j
    simp only [z, z0, Pi.smul_apply, smul_eq_mul, pow_add, mul_assoc]
  have hremoved : C.mulVec z = 0 := by
    rw [hz, Matrix.mulVec_smul, hremoved0, smul_zero]
  change B.mulVec z = 0
  apply funext
  refine Fin.succAboveCases i0 ?_ (fun i => ?_)
  · simp only [Matrix.mulVec, dotProduct, z, Pi.zero_apply]
    calc
      ∑ j : Fin (k + 1), B i0 j * ((-1 : R) ^
          ((i0 : ℕ) + (j : ℕ)) *
          (B.submatrix i0.succAbove j.succAbove).det) =
          ∑ j : Fin (k + 1), (-1 : R) ^ ((i0 : ℕ) + (j : ℕ)) *
            B i0 j * (B.submatrix i0.succAbove j.succAbove).det := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = B.det := (Matrix.det_succ_row B i0).symm
      _ = 0 := hdet
  · have hi := congrFun hremoved i
    simpa only [C, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq,
      Pi.zero_apply] using hi

/-- Deleting a column preserves the rank when a maximal nonzero minor avoids
that column. This is the common rank step in Karlin's two deficient-rank
branches; the cofactor and rank-basis kernel constructions remain separate. -/
theorem Matrix.rank_deleteColumn_eq_of_minor_ne_zero
    {R : Type*} [Field R] {n k r : ℕ}
    (A : Matrix (Fin n) (Fin (k + 1)) R)
    (hrank : A.rank = r) (j0 : Fin (k + 1))
    (rows : Fin r → Fin n) (cols : Fin r → Fin k)
    (hminor :
      (A.submatrix rows (j0.succAbove ∘ cols)).det ≠ 0) :
    (A.submatrix id j0.succAbove).rank = r := by
  let A' : Matrix (Fin n) (Fin k) R := A.submatrix id j0.succAbove
  have hdet : (A'.submatrix rows cols).det ≠ 0 := by
    simpa only [A', Matrix.submatrix_submatrix, Function.id_comp] using hminor
  have hunit : IsUnit (A'.submatrix rows cols) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hdet
  apply le_antisymm
  · calc
      A'.rank ≤ A.rank := Matrix.rank_submatrix_le A id j0.succAbove
      _ = r := hrank
  · calc
      r = (A'.submatrix rows cols).rank := by
        simpa using (Matrix.rank_of_isUnit _ hunit).symm
      _ ≤ A'.rank := Matrix.rank_submatrix_le A' rows cols

/-- Karlin's nonzero-cofactor branch for a selected singular square submatrix.
The displayed signed cofactor vector witnesses the selected-row kernel, while
the same cofactor proves both the ambient rank and rank-preserving deletion. -/
theorem Matrix.signedRowCofactor_spec_of_minor_ne_zero
    {R : Type*} [Field R] {n k : ℕ}
    (A : Matrix (Fin n) (Fin (k + 1)) R)
    (rows : Fin (k + 1) → Fin n) (i0 j0 : Fin (k + 1))
    (hrank_lt : A.rank < k + 1)
    (hminor :
      ((A.submatrix rows id).submatrix
        i0.succAbove j0.succAbove).det ≠ 0) :
    let B := A.submatrix rows id
    let z : Fin (k + 1) → R := fun j =>
      (-1 : R) ^ (i0 + j : ℕ) *
        (B.submatrix i0.succAbove j.succAbove).det
    A.rank = k ∧ B.mulVec z = 0 ∧ z j0 ≠ 0 ∧
      (A.submatrix id j0.succAbove).rank = k := by
  let B : Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
    A.submatrix rows id
  let z : Fin (k + 1) → R := fun j =>
    (-1 : R) ^ (i0 + j : ℕ) *
      (B.submatrix i0.succAbove j.succAbove).det
  change A.rank = k ∧ B.mulVec z = 0 ∧ z j0 ≠ 0 ∧
    (A.submatrix id j0.succAbove).rank = k
  have hunit : IsUnit (B.submatrix i0.succAbove j0.succAbove) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    simpa only [B] using hminor
  have hcofactor_rank :
      (B.submatrix i0.succAbove j0.succAbove).rank = k := by
    simpa using Matrix.rank_of_isUnit _ hunit
  have hrank_ge : k ≤ A.rank := by
    calc
      k = (B.submatrix i0.succAbove j0.succAbove).rank :=
        hcofactor_rank.symm
      _ ≤ B.rank :=
        Matrix.rank_submatrix_le B i0.succAbove j0.succAbove
      _ ≤ A.rank := Matrix.rank_submatrix_le A rows id
  have hrank : A.rank = k := by
    lia
  have hdet : B.det = 0 := by
    by_contra hdet
    have hBunit : IsUnit B := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      exact hdet
    have hBrank : B.rank = k + 1 := by
      simpa using Matrix.rank_of_isUnit B hBunit
    have hle : B.rank ≤ A.rank := Matrix.rank_submatrix_le A rows id
    rw [hBrank, hrank] at hle
    lia
  have hkernel : B.mulVec z = 0 := by
    exact B.mulVec_signedRowCofactor_eq_zero_of_det_eq_zero i0 hdet
  have hzj0 : z j0 ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ (by simp)) (by
      simpa only [B] using hminor)
  have hminorA :
      (A.submatrix (rows ∘ i0.succAbove)
        (j0.succAbove ∘ (id : Fin k → Fin k))).det ≠ 0 := by
    simpa only [B, Matrix.submatrix_submatrix, Function.id_comp,
      Function.comp_id] using hminor
  have hdelete :
      (A.submatrix id j0.succAbove).rank = k :=
    A.rank_deleteColumn_eq_of_minor_ne_zero hrank j0
      (rows ∘ i0.succAbove) id hminorA
  exact ⟨hrank, hkernel, hzj0, hdelete⟩

/-- A zero coefficient can be removed together with its matrix column when
forming a matrix-vector product. -/
theorem Matrix.mulVec_eq_deleteColumn_mulVec_removeNth_of_apply_eq_zero
    {R : Type*} [NonUnitalNonAssocSemiring R] {n k : ℕ}
    (A : Matrix (Fin n) (Fin (k + 1)) R)
    (d : Fin (k + 1) → R) (j0 : Fin (k + 1))
    (hd : d j0 = 0) :
    A.mulVec d =
      (A.submatrix id j0.succAbove).mulVec (Fin.removeNth j0 d) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq,
    Fin.removeNth]
  rw [Fin.sum_univ_succAbove (fun j => A i j * d j) j0, hd, mul_zero,
    zero_add]

/-- Karlin's coefficient cancellation: perturb by the unique scalar that
zeros coordinate `j0`, then remove that coordinate and its matrix column. -/
theorem Matrix.mulVec_add_neg_div_smul_eq_deleteColumn_mulVec
    {R : Type*} [DivisionRing R] {n k : ℕ}
    (A : Matrix (Fin n) (Fin (k + 1)) R)
    (c z : Fin (k + 1) → R) (j0 : Fin (k + 1))
    (hz : z j0 ≠ 0) :
    A.mulVec (c + (-c j0 / z j0) • z) =
      (A.submatrix id j0.succAbove).mulVec
        (Fin.removeNth j0 (c + (-c j0 / z j0) • z)) := by
  apply A.mulVec_eq_deleteColumn_mulVec_removeNth_of_apply_eq_zero
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [div_mul_cancel₀ _ hz, add_neg_cancel]

/-- Perturbing coefficients along a vector annihilated by a selected-row
submatrix does not change the selected coordinates of the matrix-vector
product. -/
theorem Matrix.mulVec_add_smul_apply_eq_of_submatrix_mulVec_eq_zero
    {n m k : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (rows : Fin k → Fin n) (c z : Fin m → ℝ)
    (hz : (A.submatrix rows id).mulVec z = 0)
    (t : ℝ) (i : Fin k) :
    A.mulVec (c + t • z) (rows i) = A.mulVec c (rows i) := by
  have hzi : A.mulVec z (rows i) = 0 := by
    have hi := congrFun hz i
    simpa only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq,
      Pi.zero_apply] using hi
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  simp [hzi]

/-- A selected alternating witness survives Karlin's kernel perturbation of
the coefficient vector. -/
theorem Fin.StrictlyAlternates.matrix_mulVec_add_smul
    {n m k : ℕ} {A : Matrix (Fin n) (Fin m) ℝ}
    {rows : Fin (k + 1) → Fin n} {c z : Fin m → ℝ}
    (h : StrictlyAlternates (fun i => A.mulVec c (rows i)))
    (hz : (A.submatrix rows id).mulVec z = 0)
    (t : ℝ) :
    StrictlyAlternates (fun i => A.mulVec (c + t • z) (rows i)) := by
  intro i
  change
    A.mulVec (c + t • z) (rows i.castSucc) *
      A.mulVec (c + t • z) (rows i.succ) < 0
  have heq (j : Fin (k + 1)) :=
    A.mulVec_add_smul_apply_eq_of_submatrix_mulVec_eq_zero rows c z hz t j
  rw [heq i.castSucc, heq i.succ]
  exact h i

/-- Karlin's nonzero-cofactor branch contradicts the full-rank variation
bound after the source-prescribed coefficient cancellation and column
deletion. -/
theorem Matrix.IsSignConsistentOrder.not_strictlyAlternates_mulVec_of_cofactor_ne_zero
    {n k : ℕ} {A : Matrix (Fin n) (Fin (k + 1)) ℝ}
    (hA : A.IsSignConsistentOrder k)
    (hk : 0 < k)
    (rows : Fin (k + 1) → Fin n) (hrows : StrictMono rows)
    (i0 j0 : Fin (k + 1))
    (hrank_lt : A.rank < k + 1)
    (hminor :
      ((A.submatrix rows id).submatrix
        i0.succAbove j0.succAbove).det ≠ 0)
    (c : Fin (k + 1) → ℝ)
    (hAlt : Fin.StrictlyAlternates (fun i => A.mulVec c (rows i))) :
    False := by
  let B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
    A.submatrix rows id
  let z : Fin (k + 1) → ℝ := fun j =>
    (-1 : ℝ) ^ (i0 + j : ℕ) *
      (B.submatrix i0.succAbove j.succAbove).det
  let A' : Matrix (Fin n) (Fin k) ℝ :=
    A.submatrix id j0.succAbove
  have hcase :
      A.rank = k ∧ B.mulVec z = 0 ∧ z j0 ≠ 0 ∧ A'.rank = k := by
    simpa only [B, z, A'] using
      A.signedRowCofactor_spec_of_minor_ne_zero
        rows i0 j0 hrank_lt hminor
  obtain ⟨_hrank, hkernel, hzj0, hdelete⟩ := hcase
  let t0 : ℝ := -c j0 / z j0
  let d : Fin (k + 1) → ℝ := c + t0 • z
  let d' : Fin k → ℝ := Fin.removeNth j0 d
  have hAltPert :
      Fin.StrictlyAlternates (fun i => A.mulVec d (rows i)) := by
    simpa only [d, t0] using
      hAlt.matrix_mulVec_add_smul hkernel t0
  have hreassemble : A.mulVec d = A'.mulVec d' := by
    simpa only [A', d', d, t0] using
      A.mulVec_add_neg_div_smul_eq_deleteColumn_mulVec c z j0 hzj0
  have hAltDeleted :
      Fin.StrictlyAlternates (fun i => A'.mulVec d' (rows i)) := by
    rw [hreassemble] at hAltPert
    exact hAltPert
  have hA' : A'.IsSignConsistentOrder k := by
    exact hA.submatrix strictMono_id (Fin.strictMono_succAbove j0)
  have hk1n : k + 1 ≤ n := by
    simpa using Fintype.card_le_of_injective rows hrows.injective
  have hkn : k ≤ n := (Nat.le_succ k).trans hk1n
  have hA'inj : Function.Injective A'.mulVec := by
    rw [Matrix.mulVec_injective_iff,
      linearIndependent_iff_card_eq_finrank_span]
    simpa only [Fintype.card_fin, Set.finrank] using
      hdelete.symm.trans (Matrix.rank_eq_finrank_span_cols A')
  have hlower : k ≤ Fin.signVariations (A'.mulVec d') :=
    hAltDeleted.le_signVariations_of_strictMono hrows
  have hupper : Fin.signVariations (A'.mulVec d') ≤ k - 1 :=
    hA'.signVariations_mulVec_le_card_sub_one hkn hA'inj d'
  lia

/-- Extending a coefficient vector by zero along an injective column selector
turns the ambient matrix-vector product into the selected-column product. -/
theorem Matrix.mulVec_extend_eq_submatrix_mulVec
    {R : Type*} [NonUnitalNonAssocSemiring R]
    {ι κ κ' : Type*} [Fintype κ] [Fintype κ']
    (A : Matrix ι κ R) (cols : κ' → κ)
    (hcols : Function.Injective cols) (d : κ' → R) :
    A.mulVec (Function.extend cols d 0) =
      (A.submatrix id cols).mulVec d := by
  classical
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq]
  symm
  apply Fintype.sum_of_injective cols hcols
  · intro j hj
    rw [Function.extend_apply' d (0 : κ → R) j hj, Pi.zero_apply,
      mul_zero]
  · intro j
    rw [hcols.extend_apply d (0 : κ → R) j]

/-- Karlin's repaired Case B relation after coordinates of the omitted column
in the retained column basis have been chosen. The relation is explicitly
supported on those basis columns and `j0`; no arbitrary kernel coordinate is
prescribed. -/
theorem Matrix.supportedColumnRelation_spec
    {R : Type*} [Field R] {n m r : ℕ}
    (A : Matrix (Fin n) (Fin (m + 1)) R)
    (j0 : Fin (m + 1))
    (rows : Fin r → Fin n) (cols : Fin r → Fin m)
    (hcols : Function.Injective cols)
    (hrank : A.rank = r)
    (hminor :
      (A.submatrix rows (j0.succAbove ∘ cols)).det ≠ 0)
    (d : Fin r → R)
    (hcombo :
      (A.submatrix id (j0.succAbove ∘ cols)).mulVec d = A.col j0) :
    let selected := j0.succAbove ∘ cols
    let z : Fin (m + 1) → R :=
      Function.extend selected d 0 - Pi.single j0 1
    A.mulVec z = 0 ∧ z j0 = -1 ∧
      (A.submatrix id j0.succAbove).rank = r := by
  let selected : Fin r → Fin (m + 1) := j0.succAbove ∘ cols
  let z : Fin (m + 1) → R :=
    Function.extend selected d 0 - Pi.single j0 1
  change A.mulVec z = 0 ∧ z j0 = -1 ∧
    (A.submatrix id j0.succAbove).rank = r
  have hselected : Function.Injective selected :=
    (Fin.strictMono_succAbove j0).injective.comp hcols
  have hj0 : j0 ∉ Set.range selected := by
    rintro ⟨i, hi⟩
    exact (Fin.succAbove_ne j0 (cols i)) (by
      simpa only [selected, Function.comp_apply] using hi)
  have hkernel : A.mulVec z = 0 := by
    change A.mulVec
      (Function.extend selected d 0 - Pi.single j0 1) = 0
    rw [Matrix.mulVec_sub,
      A.mulVec_extend_eq_submatrix_mulVec selected hselected d,
      Matrix.mulVec_single_one]
    simpa only [selected] using sub_eq_zero.mpr hcombo
  have hzj0 : z j0 = -1 := by
    simp only [z, Pi.sub_apply]
    rw [Function.extend_apply' d (0 : Fin (m + 1) → R) j0 hj0,
      Pi.zero_apply, Pi.single_eq_same, zero_sub]
  exact ⟨hkernel, hzj0,
    A.rank_deleteColumn_eq_of_minor_ne_zero hrank j0 rows cols hminor⟩

/-- A rank-sized minor avoiding `j0` produces Karlin's supported Case B
relation and proves that deleting `j0` preserves rank. The printed source's
arbitrary-coordinate assertion is not used: equality of the retained and
ambient column-space dimensions supplies the omitted column's coordinates. -/
theorem Matrix.exists_supportedColumnRelation_of_minor_ne_zero
    {R : Type*} [Field R] {n m r : ℕ}
    (A : Matrix (Fin n) (Fin (m + 1)) R)
    (j0 : Fin (m + 1))
    (rows : Fin r → Fin n) (cols : Fin r → Fin m)
    (hcols : Function.Injective cols)
    (hrank : A.rank = r)
    (hminor :
      (A.submatrix rows (j0.succAbove ∘ cols)).det ≠ 0) :
    ∃ d : Fin r → R,
      let selected := j0.succAbove ∘ cols
      let z : Fin (m + 1) → R :=
        Function.extend selected d 0 - Pi.single j0 1
      A.mulVec z = 0 ∧ z j0 = -1 ∧
        (A.submatrix id j0.succAbove).rank = r := by
  let selected : Fin r → Fin (m + 1) := j0.succAbove ∘ cols
  let B : Matrix (Fin n) (Fin r) R := A.submatrix id selected
  have hunit : IsUnit (B.submatrix rows id) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    simpa only [B, selected, Matrix.submatrix_submatrix,
      Function.id_comp, Function.comp_id] using hminor
  have hminor_rank : (B.submatrix rows id).rank = r := by
    simpa using Matrix.rank_of_isUnit _ hunit
  have hBge : r ≤ B.rank := by
    calc
      r = (B.submatrix rows id).rank := hminor_rank.symm
      _ ≤ B.rank := Matrix.rank_submatrix_le B rows id
  have hBle : B.rank ≤ r := by
    calc
      B.rank ≤ A.rank := Matrix.rank_submatrix_le A id selected
      _ = r := hrank
  have hBrank : B.rank = r := le_antisymm hBle hBge
  have hrange_le :
      LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin := by
    rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨selected j, rfl⟩
  have hrange :
      LinearMap.range B.mulVecLin = LinearMap.range A.mulVecLin :=
    Submodule.eq_of_le_of_finrank_le hrange_le (by
      change A.rank ≤ B.rank
      rw [hrank, hBrank])
  have hcol : A.col j0 ∈ LinearMap.range B.mulVecLin := by
    rw [hrange]
    refine ⟨Pi.single j0 1, ?_⟩
    simpa only [Matrix.mulVecLin_apply] using A.mulVec_single_one j0
  obtain ⟨d, hd⟩ := hcol
  refine ⟨d, ?_⟩
  have hcombo :
      (A.submatrix id (j0.succAbove ∘ cols)).mulVec d =
        A.col j0 := by
    simpa only [B, selected, Matrix.mulVecLin_apply] using hd
  exact A.supportedColumnRelation_spec j0 rows cols hcols hrank
    hminor d hcombo

/-- Karlin's deficient-rank induction adapter. The printed proof's claim that
an arbitrary kernel coordinate can be prescribed is false in general. Instead,
we choose `j0` outside the columns of a nonzero rank-sized minor. That minor
survives deletion of `j0`, while the selected columns express column `j0`
and produce a kernel relation whose `j0` coordinate is nonzero. -/
theorem Matrix.exists_kernelVector_apply_ne_zero_rank_deleteColumn_eq_of_rank_lt
    {R : Type*} [Field R] {n k r : ℕ}
    (A : Matrix (Fin n) (Fin (k + 1)) R)
    (hrank : A.rank = r) (hrank_lt : r < k + 1) :
    ∃ j0 : Fin (k + 1), ∃ z : Fin (k + 1) → R,
      A.mulVec z = 0 ∧ z j0 ≠ 0 ∧
        (A.submatrix id j0.succAbove).rank = r := by
  classical
  obtain ⟨rows, cols, _, hcols, hminor⟩ :=
    A.exists_ordered_minor_ne_zero_of_rank_eq hrank
  have hcols_not_surj : ¬ Function.Surjective cols := by
    intro hsurj
    apply not_le_of_gt hrank_lt
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_surjective cols hsurj
  obtain ⟨j0, hj0⟩ : ∃ j0, ∀ i, cols i ≠ j0 := by
    simpa only [Function.Surjective, not_forall, not_exists] using
      hcols_not_surj
  choose cols' hcols' using fun i =>
    Fin.exists_succAbove_eq (hj0 i)
  have hcols_factor : j0.succAbove ∘ cols' = cols := by
    funext i
    exact hcols' i
  have hcols'_inj : Function.Injective cols' := by
    intro i j hij
    apply hcols.injective
    rw [← hcols_factor]
    exact congrArg j0.succAbove hij
  have hminor' :
      (A.submatrix rows (j0.succAbove ∘ cols')).det ≠ 0 := by
    simpa only [hcols_factor] using hminor
  obtain ⟨d, hkernel, hzj0, hdelete⟩ :=
    A.exists_supportedColumnRelation_of_minor_ne_zero
      j0 rows cols' hcols'_inj hrank hminor'
  refine ⟨j0,
    Function.extend (j0.succAbove ∘ cols') d 0 - Pi.single j0 1,
    hkernel, ?_, hdelete⟩
  rw [hzj0]
  exact neg_ne_zero.mpr one_ne_zero

/-- Karlin's positive-rank, one-column induction step for the deficient-rank
case. The induction hypothesis handles the rank-preserving matrix obtained by
deleting the column selected by
`exists_kernelVector_apply_ne_zero_rank_deleteColumn_eq_of_rank_lt`. -/
theorem Matrix.IsSignConsistentOrder.signVariations_mulVec_le_rank_sub_one_of_induction
    {n k r : ℕ}
    {A : Matrix (Fin n) (Fin (k + 1)) ℝ}
    (hA : A.IsSignConsistentOrder r)
    (hrank : A.rank = r)
    (hrank_lt : r < k + 1)
    (hr : 0 < r)
    (hind :
      ∀ {B : Matrix (Fin n) (Fin k) ℝ},
        B.IsSignConsistentOrder r →
        B.rank = r →
        ∀ d : Fin k → ℝ,
          Fin.signVariations (B.mulVec d) ≤ r - 1)
    (c : Fin (k + 1) → ℝ) :
    Fin.signVariations (A.mulVec c) ≤ r - 1 := by
  by_contra hle
  have hbad : r ≤ Fin.signVariations (A.mulVec c) := by
    lia
  obtain ⟨rows, hrows, halt⟩ :=
    Fin.exists_strictMono_strictlyAlternates_of_le_signVariations hr hbad
  obtain ⟨j0, z, hkernel, hzj0, hdelete⟩ :=
    A.exists_kernelVector_apply_ne_zero_rank_deleteColumn_eq_of_rank_lt
      hrank hrank_lt
  have hzrows : (A.submatrix rows id).mulVec z = 0 := by
    funext i
    simpa only [Matrix.mulVec, Matrix.submatrix_apply, id_eq,
      Pi.zero_apply] using congrFun hkernel (rows i)
  let t : ℝ := -c j0 / z j0
  let d : Fin (k + 1) → ℝ := c + t • z
  let B : Matrix (Fin n) (Fin k) ℝ :=
    A.submatrix id j0.succAbove
  let d' : Fin k → ℝ := Fin.removeNth j0 d
  have halt_d :
      Fin.StrictlyAlternates (fun i => A.mulVec d (rows i)) := by
    simpa only [d] using halt.matrix_mulVec_add_smul hzrows t
  have hcancel : A.mulVec d = B.mulVec d' := by
    simpa only [d, t, B, d'] using
      A.mulVec_add_neg_div_smul_eq_deleteColumn_mulVec c z j0 hzj0
  have halt_delete :
      Fin.StrictlyAlternates (fun i => B.mulVec d' (rows i)) := by
    rw [← hcancel]
    exact halt_d
  have hB : B.IsSignConsistentOrder r :=
    hA.submatrix strictMono_id (Fin.strictMono_succAbove j0)
  have hupper := hind hB hdelete d'
  have hlower := halt_delete.le_signVariations_of_strictMono hrows
  lia

/-- Karlin's rank-sensitive variation bound, proved by induction on the number
of columns. Rank zero gives the zero linear map, full column rank uses the
injective variation bound, and positive deficient rank uses the
rank-preserving deletion step. -/
theorem Matrix.IsSignConsistentOrder.signVariations_mulVec_le_rank_sub_one
    {n m r : ℕ}
    {A : Matrix (Fin n) (Fin m) ℝ}
    (hA : A.IsSignConsistentOrder r)
    (hrank : A.rank = r)
    (c : Fin m → ℝ) :
    Fin.signVariations (A.mulVec c) ≤ r - 1 := by
  have hzero :
      ∀ {p : ℕ} {B : Matrix (Fin n) (Fin p) ℝ},
        B.rank = 0 →
        ∀ d : Fin p → ℝ,
          Fin.signVariations (B.mulVec d) ≤ 0 := by
    intro p B hBrank d
    have hlin : B.mulVecLin = 0 :=
      LinearMap.range_eq_bot.mp
        (Submodule.finrank_eq_zero.mp hBrank)
    rw [← Matrix.mulVecLin_apply, hlin, LinearMap.zero_apply,
      Fin.signVariations_zero]
  induction m generalizing r with
  | zero =>
      have hrzero : r = 0 := by
        have hrle : r ≤ 0 := hrank ▸ A.rank_le_width
        exact Nat.eq_zero_of_le_zero hrle
      rw [hrzero] at hrank ⊢
      exact hzero hrank c
  | succ k ih =>
      by_cases hrzero : r = 0
      · rw [hrzero] at hrank ⊢
        exact hzero hrank c
      · have hrpos : 0 < r := Nat.pos_of_ne_zero hrzero
        have hrle : r ≤ k + 1 := by
          rw [← hrank]
          exact A.rank_le_width
        by_cases hrfull : r = k + 1
        · rw [hrfull] at hA hrank ⊢
          have hkn : k + 1 ≤ n := hrank ▸ A.rank_le_height
          have hAinj : Function.Injective A.mulVec := by
            rw [Matrix.mulVec_injective_iff,
              linearIndependent_iff_card_eq_finrank_span]
            simpa only [Fintype.card_fin, Set.finrank] using
              hrank.symm.trans (Matrix.rank_eq_finrank_span_cols A)
          exact hA.signVariations_mulVec_le_card_sub_one hkn hAinj c
        · have hrlt : r < k + 1 := lt_of_le_of_ne hrle hrfull
          exact hA.signVariations_mulVec_le_rank_sub_one_of_induction
            hrank hrlt hrpos ih c

/-- Right multiplication by a totally nonnegative rectangular matrix preserves
the common weak sign of ordered minors of a fixed size. Cauchy--Binet expands
the product of two output minors as a double sum; sign consistency controls the
left-minor products and total nonnegativity controls the right-minor products. -/
theorem Matrix.IsSignConsistentOrder.mul_of_right_isTotallyNonnegRect
    {l n m r : ℕ}
    {L : Matrix (Fin l) (Fin n) ℝ}
    {A : Matrix (Fin n) (Fin m) ℝ}
    (hL : L.IsSignConsistentOrder r)
    (hA : A.IsTotallyNonnegRect) :
    (L * A).IsSignConsistentOrder r := by
  classical
  intro rows rows' cols cols' hrows hrows' hcols hcols'
  rw [Matrix.det_submatrix_mul_eq_sum_powersetCard L A rows cols,
    Matrix.det_submatrix_mul_eq_sum_powersetCard L A rows' cols']
  rw [Finset.sum_mul]
  apply Finset.sum_nonneg
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_nonneg
  intro t ht
  let es : Fin r ↪o Fin n :=
    Set.powersetCard.ofFinEmbEquiv.symm s
  let et : Fin r ↪o Fin n :=
    Set.powersetCard.ofFinEmbEquiv.symm t
  have hsign :
      0 ≤
        (L.submatrix rows es).det *
          (L.submatrix rows' et).det :=
    hL hrows hrows' es.strictMono et.strictMono
  have hright :
      0 ≤
        (A.submatrix es cols).det *
          (A.submatrix et cols').det :=
    mul_nonneg
      (hA es.strictMono hcols)
      (hA et.strictMono hcols')
  simpa only [es, et, mul_assoc, mul_left_comm, mul_comm] using
    mul_nonneg hsign hright

/-- The weighted incidence matrix associated with a block map. -/
def Matrix.weightedIncidence
    {n q : ℕ}
    (block : Fin n → Fin q)
    (weight : Fin n → ℝ) :
    Matrix (Fin n) (Fin q) ℝ :=
  fun j s => if block j = s then weight j else 0

@[simp]
theorem Matrix.weightedIncidence_apply
    {n q : ℕ}
    (block : Fin n → Fin q)
    (weight : Fin n → ℝ)
    (j : Fin n)
    (s : Fin q) :
    Matrix.weightedIncidence block weight j s =
      if block j = s then weight j else 0 :=
  rfl

/-- The minor of a monotone weighted incidence matrix is diagonal or singular.

This is the elementary incidence-matrix step in Karlin's proof of Theorem V.1.4:
monotonicity forces every nonzero Leibniz term to use the identity permutation.
Thus no separate combinatorial model is needed for this bridge. -/
theorem Matrix.det_submatrix_monotoneWeightedIncidence
    {n q r : ℕ}
    (block : Fin n → Fin q)
    (hblock : Monotone block)
    (weight : Fin n → ℝ)
    {rows : Fin r → Fin n}
    {cols : Fin r → Fin q}
    (hrows : StrictMono rows)
    (hcols : StrictMono cols) :
    ((Matrix.weightedIncidence block weight).submatrix rows cols).det =
      if ∀ i, block (rows i) = cols i then
        ∏ i, weight (rows i)
      else 0 := by
  classical
  let W := Matrix.weightedIncidence block weight
  change (W.submatrix rows cols).det =
    if ∀ i, block (rows i) = cols i then
      ∏ i, weight (rows i)
    else 0
  by_cases hdiag : ∀ i, block (rows i) = cols i
  · rw [if_pos hdiag]
    have hmatrix :
        W.submatrix rows cols =
          Matrix.diagonal (fun i => weight (rows i)) := by
      ext i j
      simp only [Matrix.submatrix_apply, W,
        Matrix.weightedIncidence_apply]
      rw [hdiag i]
      by_cases hij : i = j
      · subst j
        simp
      · have hc : cols i ≠ cols j := fun h =>
          hij (hcols.injective h)
        simp [hc, hij]
    rw [hmatrix, Matrix.det_diagonal]
  · rw [if_neg hdiag, Matrix.det_apply']
    apply Finset.sum_eq_zero
    intro sigma hsigma
    by_cases hterm : ∀ i, block (rows (sigma i)) = cols i
    · have hsigma_mono : StrictMono sigma := by
        intro i j hij
        by_contra hnot
        have hle : sigma j ≤ sigma i := le_of_not_gt hnot
        have hf :
            block (rows (sigma j)) ≤ block (rows (sigma i)) :=
          (hblock.comp hrows.monotone) hle
        rw [hterm j, hterm i] at hf
        exact (not_le_of_gt (hcols hij)) hf
      have hsigma_eq : ∀ i, sigma i = i := fun i =>
        le_antisymm (hsigma_mono.le_id i) (hsigma_mono.id_le i)
      exfalso
      apply hdiag
      intro i
      simpa only [hsigma_eq i] using hterm i
    · simp only [not_forall] at hterm
      obtain ⟨i, hi⟩ := hterm
      have hprod :
          (∏ j, (W.submatrix rows cols) (sigma j) j) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp only [Matrix.submatrix_apply, W,
          Matrix.weightedIncidence_apply]
        rw [if_neg hi]
      rw [hprod, mul_zero]

/-- A monotone weighted incidence matrix is totally nonnegative when its weights are
nonnegative. -/
theorem Matrix.isTotallyNonnegRect_monotoneWeightedIncidence
    {n q : ℕ}
    (block : Fin n → Fin q)
    (hblock : Monotone block)
    (weight : Fin n → ℝ)
    (hweight : ∀ j, 0 ≤ weight j) :
    Matrix.IsTotallyNonnegRect
      (Matrix.weightedIncidence block weight) := by
  intro r rows cols hrows hcols
  rw [Matrix.det_submatrix_monotoneWeightedIncidence
    block hblock weight hrows hcols]
  split_ifs
  · exact Finset.prod_nonneg fun i _ => hweight (rows i)
  · exact le_rfl

/-- Right multiplication by a weighted incidence matrix forms weighted block sums. -/
theorem Matrix.mul_weightedIncidence_apply
    {l n q : ℕ}
    (L : Matrix (Fin l) (Fin n) ℝ)
    (block : Fin n → Fin q)
    (weight : Fin n → ℝ)
    (i : Fin l)
    (s : Fin q) :
    (L * Matrix.weightedIncidence block weight) i s =
      ∑ j with block j = s, L i j * weight j := by
  rw [Matrix.mul_apply, Finset.sum_filter]
  simp only [Matrix.weightedIncidence_apply, mul_ite, mul_zero]

/-- A weighted incidence matrix sends block coefficients to their weighted
pullback along the block map. -/
@[simp]
theorem Matrix.weightedIncidence_mulVec
    {n q : ℕ}
    (block : Fin n → Fin q)
    (weight : Fin n → ℝ)
    (sign : Fin q → ℝ) :
    (Matrix.weightedIncidence block weight).mulVec sign =
      fun j => weight j * sign (block j) := by
  ext j
  simp [Matrix.mulVec, dotProduct]

/-- Multiplying an aggregated matrix by block coefficients reconstructs the
corresponding coefficient vector before multiplication by the original matrix. -/
theorem Matrix.mul_weightedIncidence_mulVec
    {l n q : ℕ}
    (L : Matrix (Fin l) (Fin n) ℝ)
    (block : Fin n → Fin q)
    (weight : Fin n → ℝ)
    (sign : Fin q → ℝ) :
    (L * Matrix.weightedIncidence block weight).mulVec sign =
      L.mulVec (fun j => weight j * sign (block j)) := by
  rw [← Matrix.mulVec_mulVec sign L
    (Matrix.weightedIncidence block weight),
    Matrix.weightedIncidence_mulVec]

/-- Aggregating consecutive columns with nonnegative weights preserves sign
consistency of every fixed order. -/
theorem Matrix.IsSignConsistentOrder.mul_weightedIncidence
    {l n q r : ℕ}
    {L : Matrix (Fin l) (Fin n) ℝ}
    (hL : L.IsSignConsistentOrder r)
    (block : Fin n → Fin q)
    (hblock : Monotone block)
    (weight : Fin n → ℝ)
    (hweight : ∀ j, 0 ≤ weight j) :
    (L * Matrix.weightedIncidence block weight).IsSignConsistentOrder r :=
  hL.mul_of_right_isTotallyNonnegRect
    (Matrix.isTotallyNonnegRect_monotoneWeightedIncidence
      block hblock weight hweight)

/-- Karlin's V.1.4 inequality from explicit sign-block decomposition data.

The only remaining finite combinatorial step for the general theorem is to
construct `Fin.SignBlockDecomposition c`; all matrix and rank arguments are
discharged here. -/
theorem Matrix.IsSignRegular.signVariations_mulVec_le_of_signBlockDecomposition
    {l n : ℕ}
    {A : Matrix (Fin l) (Fin n) ℝ}
    (hA : A.IsSignRegular)
    (c : Fin n → ℝ)
    (d : Fin.SignBlockDecomposition c) :
    Fin.signVariations (A.mulVec c) ≤ Fin.signVariations c := by
  let B :=
    A * Matrix.weightedIncidence d.block d.weight
  have hBsign : B.IsSignConsistentOrder B.rank := by
    simpa only [B] using
      (hA B.rank).mul_weightedIncidence
        d.block d.block_mono d.weight d.weight_nonneg
  have hbound :
      Fin.signVariations (B.mulVec d.coeff) ≤ B.rank - 1 :=
    hBsign.signVariations_mulVec_le_rank_sub_one rfl d.coeff
  have hmul : B.mulVec d.coeff = A.mulVec c := by
    calc
      B.mulVec d.coeff =
          A.mulVec (fun j => d.weight j * d.coeff (d.block j)) := by
        simpa only [B] using
          Matrix.mul_weightedIncidence_mulVec
            A d.block d.weight d.coeff
      _ = A.mulVec c :=
        congrArg A.mulVec (funext fun j => d.reconstruct j)
  calc
    Fin.signVariations (A.mulVec c) =
        Fin.signVariations (B.mulVec d.coeff) :=
      congrArg Fin.signVariations hmul.symm
    _ ≤ B.rank - 1 := hbound
    _ ≤ d.numBlocks - 1 :=
      (Nat.sub_le_sub_right B.rank_le_width) 1
    _ = Fin.signVariations c := d.numBlocks_sub_one

/-- Karlin's variation-diminishing theorem for sign-regular matrices. -/
theorem Matrix.IsSignRegular.signVariations_mulVec_le
    {l n : ℕ}
    {A : Matrix (Fin l) (Fin n) ℝ}
    (hA : A.IsSignRegular) (c : Fin n → ℝ) :
    Fin.signVariations (A.mulVec c) ≤ Fin.signVariations c :=
  hA.signVariations_mulVec_le_of_signBlockDecomposition
    c (Fin.signBlockDecomposition c)
