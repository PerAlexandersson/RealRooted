import RealRooted.BrandenLeite.Resolvable
import RealRooted.InterlacingConeBounds
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import RealRooted.RowThresholdOne
import RealRooted.SymmetricDecomposition.Theorem26

/-!
# Chain polynomials of a resolvable matrix

Definitions and the conditional Brändén--Saud Leite induction.  The public
theorems in this file assume explicit `Resolution` data; constructing that data
from total nonnegativity remains the separate Whitney-reduction problem #398.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted.BrandenLeite

/-- Brändén--Saud Leite chain polynomials, Definition 3.2. -/
def chainPolynomial (R : LowerTriangularMatrix ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      X * ∑ k : Fin (n + 1), C (R (n + 1) k) * chainPolynomial R k
termination_by n => n
decreasing_by exact k.isLt

@[simp] theorem chainPolynomial_zero (R : LowerTriangularMatrix ℝ) :
    chainPolynomial R 0 = 1 := by
  rw [chainPolynomial]

@[simp] theorem chainPolynomial_succ (R : LowerTriangularMatrix ℝ) (n : ℕ) :
    chainPolynomial R (n + 1) =
      X * ∑ k : Fin (n + 1), C (R (n + 1) k) * chainPolynomial R k := by
  rw [chainPolynomial]

/-- The subdivision operator sending `X ^ n` to the `n`th chain polynomial. -/
def subdivisionOperator (R : LowerTriangularMatrix ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := basisTransform (chainPolynomial R)
  map_add' := basisTransform_add (chainPolynomial R)
  map_smul' := by
    intro a p
    simpa [Polynomial.smul_eq_C_mul] using
      basisTransform_smul (chainPolynomial R) a p

@[simp] theorem subdivisionOperator_apply (R : LowerTriangularMatrix ℝ) (p : ℝ[X]) :
    subdivisionOperator R p = basisTransform (chainPolynomial R) p :=
  rfl

@[simp] theorem subdivisionOperator_X_pow (R : LowerTriangularMatrix ℝ) (n : ℕ) :
    subdivisionOperator R (X ^ n) = chainPolynomial R n := by
  simp [subdivisionOperator]

@[simp] theorem subdivisionOperator_C_mul_X_pow
    (R : LowerTriangularMatrix ℝ) (a : ℝ) (n : ℕ) :
    subdivisionOperator R (C a * X ^ n) = C a * chainPolynomial R n := by
  simp [subdivisionOperator, basisTransform_C_mul_X_pow]

theorem subdivisionOperator_C_mul
    (R : LowerTriangularMatrix ℝ) (a : ℝ) (p : ℝ[X]) :
    subdivisionOperator R (C a * p) = C a * subdivisionOperator R p := by
  simpa [Polynomial.smul_eq_C_mul] using
    (subdivisionOperator R).map_smul a p

private theorem rowPolynomial_sub_top
    {R : LowerTriangularMatrix ℝ}
    (hR : LowerTriangularMatrix.IsLowerUnitriangular R) (n : ℕ) :
    LowerTriangularMatrix.rowPolynomial R (n + 1) - X ^ (n + 1) =
      ∑ k : Fin (n + 1), C (R (n + 1) k) * X ^ (k : ℕ) := by
  unfold LowerTriangularMatrix.rowPolynomial
  rw [Finset.sum_range_succ, hR.diagonal]
  simp only [map_one, one_mul, add_sub_cancel_right]
  exact (Fin.sum_univ_eq_sum_range
    (fun k : ℕ => C (R (n + 1) k) * X ^ k) (n + 1)).symm

/-- Alternative recursion (3.2) for the subdivision operator. -/
theorem subdivisionOperator_X_pow_succ_eq
    {R : LowerTriangularMatrix ℝ}
    (hR : LowerTriangularMatrix.IsLowerUnitriangular R) (n : ℕ) :
    subdivisionOperator R (X ^ (n + 1)) =
      X * subdivisionOperator R
        (LowerTriangularMatrix.rowPolynomial R (n + 1) - X ^ (n + 1)) := by
  rw [subdivisionOperator_X_pow, chainPolynomial_succ,
    rowPolynomial_sub_top hR]
  rw [map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact (subdivisionOperator_C_mul_X_pow R (R (n + 1) k) k).symm

/-- The subdivision recursion written in terms of one resolving row. -/
theorem chainPolynomial_succ_eq_resolution_sum
    {R : LowerTriangularMatrix ℝ} (resolution : Resolution R) (n : ℕ) :
    chainPolynomial R (n + 1) =
      X * ∑ j ∈ Finset.range (n + 1),
        C (resolution.lambda n j) *
          subdivisionOperator R (resolution.polynomial n j) := by
  have hrow :
      LowerTriangularMatrix.rowPolynomial R (n + 1) - X ^ (n + 1) =
        ∑ j ∈ Finset.range (n + 1),
          C (resolution.lambda n j) * resolution.polynomial n j := by
    rw [resolution.rowPolynomial_eq_pow_add_sum]
    ring
  calc
    chainPolynomial R (n + 1) = subdivisionOperator R (X ^ (n + 1)) := by simp
    _ = X * subdivisionOperator R
          (LowerTriangularMatrix.rowPolynomial R (n + 1) - X ^ (n + 1)) :=
      subdivisionOperator_X_pow_succ_eq resolution.lowerUnitriangular n
    _ = X * subdivisionOperator R
          (∑ j ∈ Finset.range (n + 1),
            C (resolution.lambda n j) * resolution.polynomial n j) := by rw [hrow]
    _ = X * ∑ j ∈ Finset.range (n + 1),
          C (resolution.lambda n j) *
            subdivisionOperator R (resolution.polynomial n j) := by
      rw [map_sum]
      apply congrArg (X * ·)
      apply Finset.sum_congr rfl
      intro j hj
      exact subdivisionOperator_C_mul R _ _

/-- The exact generated-family bridge used in the induction for Theorem 3.6. -/
theorem subdivisionOperator_resolution_recurrence
    {R : LowerTriangularMatrix ℝ} (resolution : Resolution R)
    {n k : ℕ} (hk : k ≤ n + 1) :
    subdivisionOperator R (resolution.polynomial (n + 1) k) =
      X * ∑ j ∈ Finset.range k,
          C (resolution.lambda n j) *
            subdivisionOperator R (resolution.polynomial n j) +
        (1 + X) * ∑ j ∈ Finset.Ico k (n + 1),
          C (resolution.lambda n j) *
            subdivisionOperator R (resolution.polynomial n j) := by
  let term : ℕ → ℝ[X] := fun j =>
    C (resolution.lambda n j) * subdivisionOperator R (resolution.polynomial n j)
  have hmap :
      subdivisionOperator R (resolution.polynomial (n + 1) k) =
        chainPolynomial R (n + 1) + ∑ j ∈ Finset.Ico k (n + 1), term j := by
    rw [resolution.polynomial_eq_pow_add_sum hk, map_add, subdivisionOperator_X_pow,
      map_sum]
    apply congrArg (chainPolynomial R (n + 1) + ·)
    apply Finset.sum_congr rfl
    intro j hj
    exact subdivisionOperator_C_mul R _ _
  rw [hmap, chainPolynomial_succ_eq_resolution_sum resolution]
  have hsplit :
      (∑ j ∈ Finset.range (n + 1), term j) =
        (∑ j ∈ Finset.range k, term j) +
          ∑ j ∈ Finset.Ico k (n + 1), term j :=
    (Finset.sum_range_add_sum_Ico term hk).symm
  rw [hsplit]
  dsimp only [term]
  ring

/-! ### Zero-aware `fPolynomial` and finite-row helpers -/

theorem prec0_fPolynomial {d : ℕ} {p q : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpq : Prec0 p q) :
    Prec0 (fPolynomial d p) (fPolynomial d q) := by
  rcases hpq with rfl | rfl | hpq
  · simp [prec0_zero_left]
  · simp [prec0_zero_right]
  · exact (precFPolynomialTransport hpdeg hqdeg hpnn hqnn).2 hpq |>.toPrec0

theorem isInterlacingSeq0NonnegRealRooted_map_fPolynomial
    {d : ℕ} {fs : List ℝ[X]}
    (hfs : IsInterlacingSeq0NonnegRealRooted fs)
    (hdeg : ∀ p ∈ fs, p.natDegree ≤ d) :
    IsInterlacingSeq0NonnegRealRooted (fs.map (fPolynomial d)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise]
    refine List.pairwise_iff_get.2 ?_
    intro i j hij
    let i' : Fin fs.length := ⟨i.1, by simpa using i.2⟩
    let j' : Fin fs.length := ⟨j.1, by simpa using j.2⟩
    have hi : fs.get i' ∈ fs := List.get_mem _ _
    have hj : fs.get j' ∈ fs := List.get_mem _ _
    have hij' : i' < j' := by simpa [i', j'] using hij
    have hpq := hfs.interlacingSeq0.prec0 hij'
    simpa [i', j'] using prec0_fPolynomial (hdeg _ hi) (hdeg _ hj)
      (hfs.nonnegCoeffs _ hi) (hfs.nonnegCoeffs _ hj) hpq
  · intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact hasNonnegCoeffs_fPolynomial (hfs.nonnegCoeffs q hq)
  · intro p hp hp_ne
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    have hq_ne : q ≠ 0 := by
      intro hq0
      simp [hq0] at hp_ne
    exact isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs
      (hdeg q hq) hq_ne (hfs.splits hq hq_ne)
        (hfs.nonnegCoeffs q hq)

theorem roots_fPolynomial_mem_Icc {d : ℕ} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    (hpnn : HasNonnegCoeffs p) :
    ∀ x ∈ (fPolynomial d p).roots, x ∈ Set.Icc (-1) 0 := by
  intro x hx
  rw [roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
    hpdeg hp_ne hp_splits hpnn] at hx
  rcases Multiset.mem_add.mp hx with hx | hx
  · have hx_eq : x = -1 := Multiset.eq_of_mem_replicate hx
    simp [hx_eq]
  · rcases Multiset.mem_map.mp hx with ⟨r, hr, rfl⟩
    have hr0 : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hp_splits hpnn r hr
    exact ⟨(neg_one_lt_transformedRoot hr0).le, transformedRoot_nonpos hr0⟩

private theorem sum_map_range_eq_finset_sum
    (f : ℕ → ℝ[X]) : ∀ n : ℕ,
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ,
        sum_map_range_eq_finset_sum f n]
      simp

private theorem sum_map_range'_eq_finset_sum_Ico
    (f : ℕ → ℝ[X]) (k q : ℕ) :
    ((List.range' k (q - k)).map f).sum = ∑ j ∈ Finset.Ico k q, f j := by
  rw [Finset.sum_Ico_eq_sum_range, List.range'_eq_map_range, List.map_map,
    sum_map_range_eq_finset_sum]
  simp [Function.comp_apply]

private theorem staircaseSum_range_map (f : ℕ → ℝ[X])
    {q k : ℕ} (hk : k ≤ q) :
    staircaseSum ((List.range q).map f) k =
      X * ∑ j ∈ Finset.range k, f j + ∑ j ∈ Finset.Ico k q, f j := by
  unfold staircaseSum
  rw [← List.map_take, List.take_range, min_eq_left hk,
    sum_map_range_eq_finset_sum]
  rw [← List.map_drop]
  rw [show List.range q = List.range' 0 q from List.range_eq_range']
  rw [List.drop_range']
  simpa using sum_map_range'_eq_finset_sum_Ico f k q

private theorem natDegree_list_sum_le {d : ℕ} :
    ∀ {fs : List ℝ[X]}, (∀ p ∈ fs, p.natDegree ≤ d) → fs.sum.natDegree ≤ d
  | [], _ => by simp
  | p :: fs, hdeg => by
      simp only [List.sum_cons]
      exact Polynomial.natDegree_add_le_of_degree_le
        (hdeg p (by simp))
        (natDegree_list_sum_le (fun q hq => hdeg q (by
          exact List.mem_cons_of_mem p hq)))

private theorem natDegree_staircaseSum_le {d : ℕ} {fs : List ℝ[X]}
    (hdeg : ∀ p ∈ fs, p.natDegree ≤ d) (k : ℕ) :
    (staircaseSum fs k).natDegree ≤ d + 1 := by
  have htake : (fs.take k).sum.natDegree ≤ d :=
    natDegree_list_sum_le fun p hp => hdeg p (List.mem_of_mem_take hp)
  have hdrop : (fs.drop k).sum.natDegree ≤ d :=
    natDegree_list_sum_le fun p hp => hdeg p (List.mem_of_mem_drop hp)
  unfold staircaseSum
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (Polynomial.natDegree_mul_le_of_le Polynomial.natDegree_X_le htake).trans (by lia)
  · exact hdrop.trans (by lia)

private theorem fPolynomial_finset_sum {d : ℕ} {s : Finset ℕ}
    (f : ℕ → ℝ[X]) :
    fPolynomial d (∑ j ∈ s, f j) = ∑ j ∈ s, fPolynomial d (f j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp [hj, ih, fPolynomial_add]

private theorem fPolynomial_staircaseSum_range_map
    {d q k : ℕ} (f : ℕ → ℝ[X]) (hk : k ≤ q)
    (hdeg : ∀ j, j < q → (f j).natDegree ≤ d) :
    fPolynomial (d + 1) (staircaseSum ((List.range q).map f) k) =
      X * ∑ j ∈ Finset.range k, fPolynomial d (f j) +
        (1 + X) * ∑ j ∈ Finset.Ico k q, fPolynomial d (f j) := by
  rw [staircaseSum_range_map f hk, fPolynomial_add, fPolynomial_X_mul_succ,
    fPolynomial_finset_sum, fPolynomial_finset_sum]
  apply congrArg (X * (∑ j ∈ Finset.range k, fPolynomial d (f j)) + ·)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fPolynomial_succ_of_natDegree_le]
  · ring
  · exact hdeg j (Finset.mem_Ico.mp hj).2

private theorem scale_range_interlacing
    {q : ℕ} {f : ℕ → ℝ[X]} {a : ℕ → ℝ}
    (hf : IsInterlacingSeq0NonnegRealRooted ((List.range q).map f))
    (ha : ∀ j, j < q → 0 ≤ a j) :
    IsInterlacingSeq0NonnegRealRooted
      ((List.range q).map fun j => C (a j) * f j) := by
  have scaleLeft : ∀ {p r : ℝ[X]} {c : ℝ},
      Prec0 p r → 0 ≤ c → Prec0 (C c * p) r := by
    intro p r c hpr hc
    rcases eq_or_lt_of_le hc with rfl | hc_pos
    · simp [prec0_zero_left]
    rcases hpr with hp | hr | hpr
    · simp [hp, prec0_zero_left]
    · simpa [hr] using prec0_zero_right (C c * p)
    · exact (prec_C_mul_left hpr hc_pos.ne').toPrec0
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise]
    refine List.pairwise_iff_get.2 ?_
    intro i j hij
    let i' : Fin ((List.range q).map f).length := ⟨i.1, by simpa using i.2⟩
    let j' : Fin ((List.range q).map f).length := ⟨j.1, by simpa using j.2⟩
    have hij' : i' < j' := by simpa [i', j'] using hij
    have hprec := hf.interlacingSeq0.prec0 hij'
    have hiq : i.1 < q := by simpa using i.2
    have hjq : j.1 < q := by simpa using j.2
    simpa [i', j'] using scaleLeft
      (prec0_C_mul_right_of_nonneg hprec (ha j.1 hjq)) (ha i.1 hiq)
  · intro p hp
    rcases List.mem_map.mp hp with ⟨j, hj, rfl⟩
    have hjq : j < q := by simpa using hj
    exact nonnegCoeffs_C_mul (ha j hjq)
      (hf.nonnegCoeffs _ (List.mem_map.mpr ⟨j, hj, rfl⟩))
  · intro p hp hp_ne
    rcases List.mem_map.mp hp with ⟨j, hj, rfl⟩
    have ha_ne : a j ≠ 0 := by
      intro h
      simp [h] at hp_ne
    have hf_ne : f j ≠ 0 := by
      intro h
      simp [h] at hp_ne
    exact isRealRooted_C_mul hf_ne
      (hf.splits (List.mem_map.mpr ⟨j, hj, rfl⟩) hf_ne) ha_ne

/-! ### The hidden generated family -/

/-- The image under the subdivision operator of the `n`th resolving row. -/
def subdivisionRow {R : LowerTriangularMatrix ℝ}
    (resolution : Resolution R) (n : ℕ) : List ℝ[X] :=
  (List.range (n + 1)).map fun k =>
    subdivisionOperator R (resolution.polynomial n k)

@[simp] theorem length_subdivisionRow {R : LowerTriangularMatrix ℝ}
    (resolution : Resolution R) (n : ℕ) :
    (subdivisionRow resolution n).length = n + 1 := by
  simp [subdivisionRow]

private theorem exists_fPolynomial_preimage_row
    {R : LowerTriangularMatrix ℝ} (resolution : Resolution R) :
    ∀ n : ℕ, ∃ h : ℕ → ℝ[X],
      (∀ j, j ≤ n → (h j).natDegree ≤ n) ∧
      IsInterlacingSeq0NonnegRealRooted ((List.range (n + 1)).map h) ∧
      (∀ j, j ≤ n →
        subdivisionOperator R (resolution.polynomial n j) = fPolynomial n (h j)) := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun _ => 1, ?_, ?_, ?_⟩
      · intro j hj
        simp
      · refine ⟨⟨by simp [IsInterlacingSeq0], ?_⟩, ?_⟩
        · intro p hp
          have hp1 : p = 1 := by simpa using hp
          subst p
          exact hasNonnegCoeffs_one
        · intro p hp hp_ne
          have hp1 : p = 1 := by simpa using hp
          subst p
          exact ⟨one_ne_zero, Polynomial.Splits.one⟩
      · intro j hj
        have hj0 : j = 0 := by lia
        subst j
        rw [resolution.diagonal, subdivisionOperator_X_pow]
        simp [fPolynomial]
  | succ n ih =>
      rcases ih with ⟨h, hdeg, hrow, heq⟩
      let w : ℕ → ℝ[X] := fun j => C (resolution.lambda n j) * h j
      let h' : ℕ → ℝ[X] := fun k =>
        staircaseSum ((List.range (n + 1)).map w) k
      have hwdeg : ∀ j, j < n + 1 → (w j).natDegree ≤ n := by
        intro j hj
        dsimp only [w]
        exact (Polynomial.natDegree_C_mul_le _ _).trans
          (hdeg j (Nat.le_of_lt_succ hj))
      have hwrow :
          IsInterlacingSeq0NonnegRealRooted ((List.range (n + 1)).map w) := by
        exact scale_range_interlacing hrow fun j hj =>
          resolution.lambda_nonneg n j (Nat.le_of_lt_succ hj)
      have hh'row :
          IsInterlacingSeq0NonnegRealRooted ((List.range (n + 2)).map h') := by
        dsimp only [h']
        rw [← matPolyAction_thresholdOne_eq_staircaseSums]
        exact thresholdOneMatrix_preserves_interlacing_weak
          ((List.range (n + 1)).map w) rfl hwrow
      refine ⟨h', ?_, hh'row, ?_⟩
      · intro k hk
        exact natDegree_staircaseSum_le
          (fun p hp => by
            rcases List.mem_map.mp hp with ⟨j, hj, rfl⟩
            exact hwdeg j (by simpa using hj)) k
      · intro k hk
        rw [subdivisionOperator_resolution_recurrence resolution hk,
          fPolynomial_staircaseSum_range_map w hk hwdeg]
        apply congrArg₂ (· + ·)
        · apply congrArg (X * ·)
          apply Finset.sum_congr rfl
          intro j hj
          dsimp only [w]
          have hjk : j < k := Finset.mem_range.mp hj
          rw [fPolynomial_C_mul, ← heq j (by lia)]
        · apply congrArg ((1 + X) * ·)
          apply Finset.sum_congr rfl
          intro j hj
          dsimp only [w]
          have hjn : j < n + 1 := (Finset.mem_Ico.mp hj).2
          rw [fPolynomial_C_mul, ← heq j (by lia)]

/-- Conditional Brändén--Saud Leite Theorem 3.6: every resolving row,
after applying the subdivision operator, is a weak zero-aware interlacing
family with nonnegative coefficients and real-rooted nonzero members. -/
theorem subdivisionRow_interlacing {R : LowerTriangularMatrix ℝ}
    (resolution : Resolution R) (n : ℕ) :
    IsInterlacingSeq0NonnegRealRooted (subdivisionRow resolution n) := by
  rcases exists_fPolynomial_preimage_row resolution n with ⟨h, hdeg, hrow, heq⟩
  have himage := isInterlacingSeq0NonnegRealRooted_map_fPolynomial hrow
    (fun p hp => by
      rcases List.mem_map.mp hp with ⟨j, hj, rfl⟩
      exact hdeg j (by simpa using hj))
  have hlist :
      (List.range (n + 1)).map
          (fun k => subdivisionOperator R (resolution.polynomial n k)) =
        ((List.range (n + 1)).map h).map (fPolynomial n) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    exact heq j (by simpa using hj)
  rw [subdivisionRow, hlist]
  exact himage

/-- Every root in a transformed resolving row lies in the closed interval
`[-1, 0]`.  The assertion is also valid for a zero output, whose root multiset
is empty. -/
theorem roots_subdivisionOperator_resolutionPolynomial_mem_Icc
    {R : LowerTriangularMatrix ℝ} (resolution : Resolution R)
    {n k : ℕ} (hk : k ≤ n) :
    ∀ x ∈ (subdivisionOperator R (resolution.polynomial n k)).roots,
      x ∈ Set.Icc (-1) 0 := by
  rcases exists_fPolynomial_preimage_row resolution n with ⟨h, hdeg, hrow, heq⟩
  rw [heq k hk]
  by_cases hk0 : h k = 0
  · simp [hk0]
  have hkmem : h k ∈ (List.range (n + 1)).map h :=
    List.mem_map.mpr ⟨k, by simpa using hk, rfl⟩
  exact roots_fPolynomial_mem_Icc (hdeg k hk) hk0
    (hrow.splits hkmem hk0) (hrow.nonnegCoeffs _ hkmem)

/-- The diagonal member of a transformed resolving row is the corresponding
chain polynomial. -/
theorem subdivisionOperator_resolutionPolynomial_diagonal
    {R : LowerTriangularMatrix ℝ} (resolution : Resolution R) (n : ℕ) :
    subdivisionOperator R (resolution.polynomial n n) = chainPolynomial R n := by
  rw [resolution.diagonal, subdivisionOperator_X_pow]

/-- Each chain polynomial is either zero or real-rooted. -/
theorem chainPolynomial_eq_zero_or_splits
    {R : LowerTriangularMatrix ℝ} (resolution : Resolution R) (n : ℕ) :
    chainPolynomial R n = 0 ∨ (chainPolynomial R n).Splits := by
  have hrow := subdivisionRow_interlacing resolution n
  have hmem : subdivisionOperator R (resolution.polynomial n n) ∈
      subdivisionRow resolution n := by
    exact List.mem_map.mpr ⟨n, by simp, rfl⟩
  by_cases h0 : chainPolynomial R n = 0
  · exact Or.inl h0
  · have hmem' : chainPolynomial R n ∈ subdivisionRow resolution n := by
      rw [← subdivisionOperator_resolutionPolynomial_diagonal resolution n]
      exact hmem
    exact Or.inr <| hrow.splits hmem' h0

/-- Chain polynomials have nonnegative coefficients. -/
theorem chainPolynomial_hasNonnegCoeffs
    {R : LowerTriangularMatrix ℝ} (resolution : Resolution R) (n : ℕ) :
    HasNonnegCoeffs (chainPolynomial R n) := by
  have hrow := subdivisionRow_interlacing resolution n
  have hmem : subdivisionOperator R (resolution.polynomial n n) ∈
      subdivisionRow resolution n := List.mem_map.mpr ⟨n, by simp, rfl⟩
  simpa [subdivisionOperator_resolutionPolynomial_diagonal resolution n] using
    hrow.nonnegCoeffs _ hmem

/-- The zeros of every chain polynomial lie in `[-1, 0]`. -/
theorem roots_chainPolynomial_mem_Icc
    {R : LowerTriangularMatrix ℝ} (resolution : Resolution R) (n : ℕ) :
    ∀ x ∈ (chainPolynomial R n).roots, x ∈ Set.Icc (-1) 0 := by
  simpa [subdivisionOperator_resolutionPolynomial_diagonal resolution n] using
    roots_subdivisionOperator_resolutionPolynomial_mem_Icc resolution (le_rfl : n ≤ n)

/-- Zero-aware conditional Brändén--Saud Leite Theorem 3.7.  This is the
correct general statement for nonnegative resolution weights: some weights,
and hence some chain polynomials, may vanish. -/
theorem prec0_chainPolynomial_succ
    {R : LowerTriangularMatrix ℝ} (resolution : Resolution R) (n : ℕ) :
    Prec0 (chainPolynomial R n) (chainPolynomial R (n + 1)) := by
  let F : ℕ → ℝ[X] := fun j =>
    subdivisionOperator R (resolution.polynomial n j)
  let S : ℝ[X] := ∑ j ∈ Finset.range (n + 1), C (resolution.lambda n j) * F j
  have hrow := subdivisionRow_interlacing resolution n
  have hmem : ∀ j, j ≤ n → F j ∈ subdivisionRow resolution n := by
    intro j hj
    exact List.mem_map.mpr ⟨j, by simpa using hj, rfl⟩
  have hbase : ∀ j, j ≤ n → Prec0 (F j) (F n) := by
    intro j hj
    rcases eq_or_lt_of_le hj with hEq | hjn
    · subst j
      by_cases h0 : F n = 0
      · simp [h0, prec0_zero_left]
      · exact prec0_refl_of_realRooted ⟨h0, hrow.splits (hmem n le_rfl) h0⟩
    · let i : Fin (subdivisionRow resolution n).length := ⟨j, by simp; lia⟩
      let last : Fin (subdivisionRow resolution n).length := ⟨n, by simp⟩
      have hprec := hrow.interlacingSeq0.prec0 (i := i) (j := last) (by
        change j < n
        exact hjn)
      simpa [F, subdivisionRow, i, last] using hprec
  have hSprec : Prec0 S (F n) := by
    apply prec0_finsetSum_right_of_nonneg
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact prec0_C_mul_left_of_nonneg (hbase j hjn)
        (resolution.lambda_nonneg n j hjn)
    · intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      exact nonnegCoeffs_C_mul (resolution.lambda_nonneg n j hjn)
        (hrow.nonnegCoeffs _ (hmem j hjn))
  have hSnn : HasNonnegCoeffs S := by
    apply hasNonnegCoeffs_finsetSum
    intro j hj
    have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
    exact nonnegCoeffs_C_mul (resolution.lambda_nonneg n j hjn)
      (hrow.nonnegCoeffs _ (hmem j hjn))
  have hFn : F n = chainPolynomial R n :=
    subdivisionOperator_resolutionPolynomial_diagonal resolution n
  have hstep := prec0_mul_X_of_prec0 hSprec hSnn
    (hrow.nonnegCoeffs _ (hmem n le_rfl))
  rw [hFn] at hstep
  rw [chainPolynomial_succ_eq_resolution_sum resolution]
  simpa [S, F] using hstep

/-- Strict form of Theorem 3.7 when both adjacent chain polynomials are
nonzero. -/
theorem prec_chainPolynomial_succ_of_ne
    {R : LowerTriangularMatrix ℝ} (resolution : Resolution R) (n : ℕ)
    (hn : chainPolynomial R n ≠ 0) (hsucc : chainPolynomial R (n + 1) ≠ 0) :
    Prec (chainPolynomial R n) (chainPolynomial R (n + 1)) :=
  (prec0_chainPolynomial_succ resolution n).toPrec_of_ne hn hsucc

end RealRooted.BrandenLeite
