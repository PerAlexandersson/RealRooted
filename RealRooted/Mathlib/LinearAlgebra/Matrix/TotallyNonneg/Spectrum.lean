import RealRooted.Mathlib.LinearAlgebra.Matrix.GantmacherKrein
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularRankDeficient
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularStrictification
import RealRooted.Mathlib.LinearAlgebra.Matrix.SpectrumClosed
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul

/-!
# Spectrum of totally nonnegative matrices

This file proves the finite-dimensional Gantmacher--Krein theorem: every
complex eigenvalue of a totally nonnegative real matrix is real and
nonnegative.

The proof uses rank-preserving Gaussian smoothing.  Multiplication on both
sides by Karlin's strictly totally positive Gaussian matrix makes every minor
through the rank strictly positive.  Consequently all compounds through the
rank are primitive.  A rank-sensitive version of the compound/Perron argument
then gives positive nonzero eigenvalues and zero remaining eigenvalues.  The
Gaussian matrices tend to the identity, so closedness of real nonnegative
spectrum gives the result for the original matrix.
-/

open Filter Polynomial Finset
open scoped Topology

namespace Matrix

variable {n : ℕ}

private def rankPrefix (n r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => (i : ℕ) < r

private lemma rankPrefix_zero : rankPrefix n 0 = ∅ := by
  simp [rankPrefix]

private lemma rankPrefix_succ {r : ℕ} (hr : r < n) :
    rankPrefix n (r + 1) = insert ⟨r, hr⟩ (rankPrefix n r) ∧
      (⟨r, hr⟩ : Fin n) ∉ rankPrefix n r := by
  constructor
  · ext i
    simp only [rankPrefix, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | hi)
      · exact Nat.lt_succ_self r
      · exact Nat.lt_succ_of_lt hi
  · simp [rankPrefix]

private lemma rankPrefix_card {r : ℕ} (hr : r ≤ n) :
    (rankPrefix n r).card = r := by
  induction r with
  | zero => simp [rankPrefix_zero]
  | succ r ih =>
      have hrn : r < n := Nat.lt_of_succ_le hr
      obtain ⟨hinsert, hnot⟩ := rankPrefix_succ hrn
      rw [hinsert, Finset.card_insert_of_notMem hnot, ih hrn.le]

private lemma rankPrefix_eq_image {r : ℕ} (hr : r ≤ n) :
    rankPrefix n r = Finset.univ.image (Fin.castLE hr) := by
  ext i
  simp only [rankPrefix, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro hi
    exact ⟨⟨(i : ℕ), hi⟩, Fin.ext rfl⟩
  · rintro ⟨k, rfl⟩
    exact k.isLt

private lemma index_le_value_of_strictMono {q : ℕ}
    {f : Fin q → Fin n} (hf : StrictMono f) (k : Fin q) :
    (k : ℕ) ≤ (f k : ℕ) := by
  have h : ∀ m : ℕ, ∀ k : Fin q, (k : ℕ) = m → m ≤ (f k : ℕ) := by
    intro m
    induction m with
    | zero => exact fun _ _ => Nat.zero_le _
    | succ m ih =>
        intro k hk
        have hm : m < q := by
          have := k.isLt
          lia
        have hprev := ih ⟨m, hm⟩ rfl
        have hlt : f ⟨m, hm⟩ < f k := hf (by simp [Fin.lt_def, hk])
        exact Nat.succ_le_of_lt (hprev.trans_lt hlt)
  exact h (k : ℕ) k rfl

/-- A matrix has a nonzero ordered minor of every order at most its rank. -/
theorem exists_ordered_minor_ne_zero_of_le_rank
    {R : Type*} [Field R] {m q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (hq : q ≤ A.rank) :
    ∃ rows : Fin q → Fin n, ∃ cols : Fin q → Fin m,
      StrictMono rows ∧ StrictMono cols ∧
        (A.submatrix rows cols).det ≠ 0 := by
  obtain ⟨rows, cols, hrows, hcols, hminor⟩ :=
    A.exists_ordered_minor_ne_zero_of_rank_eq rfl
  let M : Matrix (Fin A.rank) (Fin A.rank) R := A.submatrix rows cols
  have hMunit : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hminor
  let selected : Fin q → Fin A.rank := Fin.castLE hq
  have hselected : StrictMono selected := Fin.strictMono_castLE hq
  obtain ⟨rows', hrows', hminor'⟩ :=
    Matrix.exists_ordered_minor_ne_zero_of_mulVec_injective M
      (Matrix.mulVec_injective_iff_isUnit.mpr hMunit)
      selected hselected
  refine ⟨rows ∘ rows', cols ∘ selected,
    hrows.comp hrows', hcols.comp hselected, ?_⟩
  simpa only [M, Matrix.submatrix_submatrix, Function.comp_def] using hminor'

/-- Every compound above the rank of a matrix is zero. -/
theorem compound_eq_zero_of_rank_lt
    {R : Type*} [Field R] {m q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (hq : A.rank < q) :
    compound q A = 0 := by
  ext rows cols
  rw [compound_apply]
  by_contra hminor
  have hunit : IsUnit
      (A.submatrix (powersetEnum rows) (powersetEnum cols)) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hminor
  have hrank :
      (A.submatrix (powersetEnum rows) (powersetEnum cols)).rank = q := by
    simpa using Matrix.rank_of_isUnit _ hunit
  have hle := Matrix.rank_submatrix_le A (powersetEnum rows) (powersetEnum cols)
  rw [hrank] at hle
  exact (not_le_of_gt hq) hle

/-- Rank-sensitive Gantmacher--Krein factorization.  If the compounds through
the rank are primitive, all eigenvalues can be enumerated in `ℝ_{≥0}`; the
first `r` are positive and the remainder vanish. -/
theorem exists_charpoly_eq_prod_nonneg_of_rank_eq_of_compounds_primitive
    {A : Matrix (Fin n) (Fin n) ℝ} {r : ℕ}
    (hrank : A.rank = r)
    (hprim : ∀ q, 1 ≤ q → q ≤ r → (compound q A).IsPrimitive) :
    ∃ μ : Fin n → ℝ, (∀ i, 0 ≤ μ i) ∧
      (∀ i : Fin n, (i : ℕ) < r → 0 < μ i) ∧
      (∀ i : Fin n, r ≤ (i : ℕ) → μ i = 0) ∧
      A.charpoly = ∏ i, (X - C (μ i)) := by
  classical
  have hrn : r ≤ n := by
    rw [← hrank]
    exact A.rank_le_width
  obtain ⟨ν, hνchar, hνcomp⟩ :=
    exists_charpoly_compound_eq_prod (A.map (algebraMap ℝ ℂ))
  let σ : Equiv.Perm (Fin n) := Tuple.sort fun i => ‖ν i‖
  let τ : Equiv.Perm (Fin n) := Fin.revPerm.trans σ
  let μC : Fin n → ℂ := ν ∘ τ
  have hanti : ∀ i j : Fin n, i ≤ j → ‖μC j‖ ≤ ‖μC i‖ := by
    intro i j hij
    have hmono := Tuple.monotone_sort fun i => ‖ν i‖
    have hrev : j.rev ≤ i.rev := Fin.rev_le_rev.mpr hij
    simpa [μC, τ, Function.comp_def] using hmono hrev
  have hchar :
      (A.map (algebraMap ℝ ℂ)).charpoly = ∏ i, (X - C (μC i)) := by
    rw [hνchar]
    exact (Equiv.prod_comp τ fun i => (X : ℂ[X]) - C (ν i)).symm
  have hcomp : ∀ q, (compound q A).charpoly.map (algebraMap ℝ ℂ) =
      ∏ s : Set.powersetCard (Fin n) q,
        (X - C (∏ k, μC (powersetEnum s k))) := by
    intro q
    calc
      (compound q A).charpoly.map (algebraMap ℝ ℂ) =
          ((compound q A).map (algebraMap ℝ ℂ)).charpoly :=
        (charpoly_map (compound q A) (algebraMap ℝ ℂ)).symm
      _ = (compound q (A.map (algebraMap ℝ ℂ))).charpoly := by
        rw [compound_map]
      _ = ∏ s : Set.powersetCard (Fin n) q,
          (X - C (∏ k, μC (powersetEnum s k))) := by
        rw [hνcomp q]
        exact (prod_powersetCard_comp_perm τ ν).symm
  have hkey : ∀ q, 1 ≤ q → ∀ hqr : q ≤ r,
      ∏ i ∈ rankPrefix n q, μC i =
        ((CollatzWielandt.perronRoot (compound q A) : ℝ) : ℂ) := by
    intro q hq1 hqr
    have hqn : q ≤ n := hqr.trans hrn
    let B : Matrix (Set.powersetCard (Fin n) q)
        (Set.powersetCard (Fin n) q) ℝ := compound q A
    have hBprim := hprim q hq1 hqr
    have hBnonneg : ∀ s t, 0 ≤ B s t := hBprim.nonneg
    let sTop : Set.powersetCard (Fin n) q :=
      ⟨rankPrefix n q,
        Set.powersetCard.mem_iff.mpr (rankPrefix_card hqn)⟩
    letI : Nonempty (Set.powersetCard (Fin n) q) := ⟨sTop⟩
    have hperron_nonneg : 0 ≤ CollatzWielandt.perronRoot B :=
      CollatzWielandt.perronRoot_nonneg hBnonneg
    obtain ⟨v, -, hvne, hveig⟩ :=
      exists_nonneg_mulVec_eq_perronRoot_smul hBnonneg
    have hroot : B.charpoly.IsRoot (CollatzWielandt.perronRoot B) :=
      mem_spectrum_iff_isRoot_charpoly.mp
        (mem_spectrum_of_eigenvalue hvne hveig)
    have hrootC :
        (B.charpoly.map (algebraMap ℝ ℂ)).eval
          ((CollatzWielandt.perronRoot B : ℝ) : ℂ) = 0 := by
      have heval :
          (B.charpoly.map (algebraMap ℝ ℂ)).eval
              ((algebraMap ℝ ℂ) (CollatzWielandt.perronRoot B)) =
            (algebraMap ℝ ℂ)
              (B.charpoly.eval (CollatzWielandt.perronRoot B)) := by
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
      simpa [hroot.eq_zero] using heval
    obtain ⟨s₀, hs₀⟩ : ∃ s : Set.powersetCard (Fin n) q,
        ∏ k, μC (powersetEnum s k) =
          ((CollatzWielandt.perronRoot B : ℝ) : ℂ) := by
      rw [hcomp q, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hrootC
      obtain ⟨s, -, hs⟩ := hrootC
      refine ⟨s, ?_⟩
      have h := hs
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        sub_eq_zero] at h
      exact h.symm
    have hdom : ∀ s : Set.powersetCard (Fin n) q,
        (∏ k, μC (powersetEnum s k)) ≠
            ((CollatzWielandt.perronRoot B : ℝ) : ℂ) →
          ‖∏ k, μC (powersetEnum s k)‖ <
            CollatzWielandt.perronRoot B := by
      intro s hne
      have heig : (∏ k, μC (powersetEnum s k)) ∈
          spectrum ℂ (B.map (algebraMap ℝ ℂ)) := by
        rw [mem_spectrum_iff_isRoot_charpoly, charpoly_map, IsRoot.def,
          hcomp q, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ s)
          (by simp only [Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C, sub_self])
      exact spectral_dominance_of_primitive'
        hBprim hBnonneg _ heig hne
    have htopProd : ∏ k, μC (powersetEnum sTop k) =
        ∏ i ∈ rankPrefix n q, μC i :=
      prod_powersetEnum sTop μC
    have htopEnum : ∏ i ∈ rankPrefix n q, μC i =
        ∏ k : Fin q, μC (Fin.castLE hqn k) := by
      rw [rankPrefix_eq_image hqn]
      exact Finset.prod_image fun x _ y _ h => Fin.castLE_injective hqn h
    have hmax : ∀ s : Set.powersetCard (Fin n) q,
        ‖∏ k, μC (powersetEnum s k)‖ ≤
          ‖∏ i ∈ rankPrefix n q, μC i‖ := by
      intro s
      rw [htopEnum, norm_prod, norm_prod]
      apply Finset.prod_le_prod fun k _ => norm_nonneg _
      intro k _
      apply hanti
      exact Fin.le_def.mpr
        (index_le_value_of_strictMono (strictMono_powersetEnum s) k)
    by_contra hne
    have hlt : ‖∏ i ∈ rankPrefix n q, μC i‖ <
        CollatzWielandt.perronRoot B := by
      have h := hdom sTop (by rw [htopProd]; exact hne)
      rwa [htopProd] at h
    have hge : CollatzWielandt.perronRoot B ≤
        ‖∏ i ∈ rankPrefix n q, μC i‖ := by
      have h := hmax s₀
      rw [hs₀, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hperron_nonneg] at h
      exact h
    exact (not_le_of_gt hlt) hge
  let R : ℕ → ℝ := fun q =>
    if q = 0 then 1 else CollatzWielandt.perronRoot (compound q A)
  have hRpos : ∀ q, q ≤ r → 0 < R q := by
    intro q hqr
    rcases Nat.eq_zero_or_pos q with rfl | hq1
    · simp [R]
    · have hqn : q ≤ n := hqr.trans hrn
      letI : Nonempty (Set.powersetCard (Fin n) q) :=
        ⟨⟨rankPrefix n q,
          Set.powersetCard.mem_iff.mpr (rankPrefix_card hqn)⟩⟩
      simp only [R, if_neg hq1.ne']
      exact perronRoot_pos_of_irreducible
        (hprim q hq1 hqr).isIrreducible (hprim q hq1 hqr).nonneg
  have hprodR : ∀ q, q ≤ r →
      ∏ i ∈ rankPrefix n q, μC i = ((R q : ℝ) : ℂ) := by
    intro q hqr
    rcases Nat.eq_zero_or_pos q with rfl | hq1
    · simp [rankPrefix_zero, R]
    · rw [hkey q hq1 hqr]
      simp [R, if_neg hq1.ne']
  let μ : Fin n → ℝ := fun i =>
    if hi : (i : ℕ) < r then R ((i : ℕ) + 1) / R (i : ℕ) else 0
  have hμpos : ∀ i : Fin n, (i : ℕ) < r → 0 < μ i := by
    intro i hi
    simp only [μ, dif_pos hi]
    exact div_pos (hRpos _ hi) (hRpos _ hi.le)
  have hμzero : ∀ i : Fin n, r ≤ (i : ℕ) → μ i = 0 := by
    intro i hi
    simp only [μ, dif_neg (Nat.not_lt.mpr hi)]
  have hμChead : ∀ i : Fin n, (i : ℕ) < r → μC i = (μ i : ℂ) := by
    intro i hi
    obtain ⟨hinsert, hnot⟩ := rankPrefix_succ (hi.trans_le hrn)
    have hnext := hprodR ((i : ℕ) + 1) hi
    have hprev := hprodR (i : ℕ) hi.le
    rw [hinsert, Finset.prod_insert hnot, hprev] at hnext
    simp only [μ, dif_pos hi]
    push_cast
    exact (eq_div_iff (Complex.ofReal_ne_zero.mpr (hRpos _ hi.le).ne')).mpr hnext
  have hμCtail : ∀ i : Fin n, r ≤ (i : ℕ) → μC i = 0 := by
    intro i hi
    by_cases hrn' : r = n
    · subst n
      exact absurd (hi.trans_lt i.isLt) (Nat.lt_irrefl r)
    · have hrlt : r < n := lt_of_le_of_ne hrn hrn'
      let support : Finset (Fin n) := insert i (rankPrefix n r)
      have hiNot : i ∉ rankPrefix n r := by simp [rankPrefix, Nat.not_lt.mpr hi]
      have hcard : support.card = r + 1 := by
        simp [support, hiNot, rankPrefix_card hrn]
      let s : Set.powersetCard (Fin n) (r + 1) :=
        ⟨support, Set.powersetCard.mem_iff.mpr hcard⟩
      have hcompound : compound (r + 1) A = 0 := by
        apply compound_eq_zero_of_rank_lt A
        rw [hrank]
        exact Nat.lt_succ_self r
      have hroot :
          ((compound (r + 1) A).charpoly.map (algebraMap ℝ ℂ)).IsRoot
            (∏ k, μC (powersetEnum s k)) := by
        rw [IsRoot.def, hcomp (r + 1), Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ s)
          (by simp only [Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C, sub_self])
      have hproductZero : ∏ k, μC (powersetEnum s k) = 0 := by
        rw [hcompound, Matrix.charpoly_zero, Polynomial.map_pow,
          Polynomial.map_X, Polynomial.IsRoot.def,
          Polynomial.eval_pow, Polynomial.eval_X] at hroot
        have hcardPos : 0 < Fintype.card
            (Set.powersetCard (Fin n) (r + 1)) :=
          Fintype.card_pos_iff.mpr ⟨s⟩
        exact (pow_eq_zero_iff hcardPos.ne').mp hroot
      rw [prod_powersetEnum s μC] at hproductZero
      change ∏ j ∈ support, μC j = 0 at hproductZero
      rw [Finset.prod_insert hiNot, hprodR r le_rfl] at hproductZero
      have hRne : ((R r : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (hRpos r le_rfl).ne'
      exact (mul_eq_zero.mp hproductZero).resolve_right hRne
  have hμC : ∀ i, μC i = (μ i : ℂ) := by
    intro i
    by_cases hi : (i : ℕ) < r
    · exact hμChead i hi
    · rw [hμCtail i (Nat.le_of_not_gt hi), hμzero i (Nat.le_of_not_gt hi)]
      exact map_zero (algebraMap ℝ ℂ)
  have hmapped : A.charpoly.map (algebraMap ℝ ℂ) =
      (∏ i, ((X : ℝ[X]) - C (μ i))).map (algebraMap ℝ ℂ) := by
    rw [← charpoly_map, hchar, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hμC i]
    rfl
  refine ⟨μ, fun i => ?_, hμpos, hμzero,
    Polynomial.map_injective (algebraMap ℝ ℂ)
      (algebraMap ℝ ℂ).injective hmapped⟩
  by_cases hi : (i : ℕ) < r
  · exact (hμpos i hi).le
  · rw [hμzero i (Nat.le_of_not_gt hi)]

/-! ### Rank-preserving Gaussian smoothing -/

/-- Karlin's Gaussian matrix is invertible at every positive parameter. -/
theorem isUnit_gaussianMatrix {a : ℝ} (ha : 0 < a) :
    IsUnit (gaussianMatrix n a) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact (det_gaussianMatrix_submatrix_pos a id id ha strictMono_id
    strictMono_id).ne'

/-- The two-sided Gaussian smoothing used in the rank-sensitive density
argument. -/
noncomputable def gaussianSandwich (A : Matrix (Fin n) (Fin n) ℝ)
    (a : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  gaussianMatrix n a * A * gaussianMatrix n a

/-- Two-sided Gaussian smoothing preserves matrix rank. -/
theorem rank_gaussianSandwich (A : Matrix (Fin n) (Fin n) ℝ)
    {a : ℝ} (ha : 0 < a) :
    (gaussianSandwich A a).rank = A.rank := by
  have hunit : IsUnit (gaussianMatrix n a).det := by
    rw [isUnit_iff_ne_zero]
    exact (det_gaussianMatrix_submatrix_pos a id id ha strictMono_id
      strictMono_id).ne'
  calc
    (gaussianSandwich A a).rank =
        (gaussianMatrix n a * A).rank := by
      exact Matrix.rank_mul_eq_left_of_isUnit_det
        (gaussianMatrix n a) (gaussianMatrix n a * A) hunit
    _ = A.rank := by
      exact Matrix.rank_mul_eq_right_of_isUnit_det
        (gaussianMatrix n a) A hunit

/-- A positive-parameter Gaussian matrix is totally nonnegative. -/
theorem gaussianMatrix_isTotallyNonneg {a : ℝ} (ha : 0 < a) :
    (gaussianMatrix n a).IsTotallyNonneg := by
  intro q rows cols hrows hcols
  exact (det_gaussianMatrix_submatrix_pos a rows cols ha hrows hcols).le

/-- Gaussian smoothing preserves total nonnegativity. -/
theorem IsTotallyNonneg.gaussianSandwich_isTotallyNonneg
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsTotallyNonneg) {a : ℝ} (ha : 0 < a) :
    (Matrix.gaussianSandwich A a).IsTotallyNonneg := by
  have hG : (gaussianMatrix n a).IsTotallyNonneg :=
    gaussianMatrix_isTotallyNonneg ha
  exact (hG.mul hA).mul hG

/-- Two-sided Gaussian smoothing makes every ordered minor through the rank
strictly positive. -/
theorem IsTotallyNonneg.det_gaussianSandwich_pos_of_le_rank
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsTotallyNonneg)
    {a : ℝ} (ha : 0 < a) {q : ℕ} (hq : q ≤ A.rank)
    {rows cols : Fin q → Fin n} (hrows : StrictMono rows)
    (hcols : StrictMono cols) :
    0 < ((Matrix.gaussianSandwich A a).submatrix rows cols).det := by
  classical
  obtain ⟨sourceRows, sourceCols, hsourceRows, hsourceCols, hminorNe⟩ :=
    exists_ordered_minor_ne_zero_of_le_rank A hq
  have hminorPos : 0 < (A.submatrix sourceRows sourceCols).det :=
    lt_of_le_of_ne (hA hsourceRows hsourceCols) hminorNe.symm
  let rowEmbedding : Fin q ↪o Fin n :=
    OrderEmbedding.ofStrictMono sourceRows hsourceRows
  let colEmbedding : Fin q ↪o Fin n :=
    OrderEmbedding.ofStrictMono sourceCols hsourceCols
  let rowSet : Set.powersetCard (Fin n) q :=
    Set.powersetCard.ofFinEmbEquiv rowEmbedding
  let colSet : Set.powersetCard (Fin n) q :=
    Set.powersetCard.ofFinEmbEquiv colEmbedding
  rw [Matrix.gaussianSandwich, det_submatrix_mul_eq_sum_powersetCard]
  apply Finset.sum_pos'
  · intro s _
    exact mul_nonneg
      (((gaussianMatrix_isTotallyNonneg ha).mul hA)
        hrows (strictMono_powersetEnum s))
      ((gaussianMatrix_isTotallyNonneg ha)
        (strictMono_powersetEnum s) hcols)
  · refine ⟨colSet, Finset.mem_univ _, ?_⟩
    apply mul_pos
    · rw [det_submatrix_mul_eq_sum_powersetCard]
      apply Finset.sum_pos'
      · intro s _
        exact mul_nonneg
          ((gaussianMatrix_isTotallyNonneg ha)
            hrows (strictMono_powersetEnum s))
          (hA (strictMono_powersetEnum s)
            (strictMono_powersetEnum colSet))
      · refine ⟨rowSet, Finset.mem_univ _, ?_⟩
        simpa [rowSet, colSet, rowEmbedding, colEmbedding] using
          mul_pos
            (det_gaussianMatrix_submatrix_pos a rows sourceRows ha
              hrows hsourceRows)
            hminorPos
    · exact det_gaussianMatrix_submatrix_pos a
        (powersetEnum colSet) cols ha (strictMono_powersetEnum colSet) hcols

/-- Every compound through the rank of a Gaussian-smoothed totally
nonnegative matrix is primitive. -/
theorem IsTotallyNonneg.compound_gaussianSandwich_isPrimitive
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsTotallyNonneg)
    {a : ℝ} (ha : 0 < a) {q : ℕ} (hq : q ≤ A.rank) :
    (compound q (Matrix.gaussianSandwich A a)).IsPrimitive := by
  have hpos : ∀ s t, 0 < compound q (Matrix.gaussianSandwich A a) s t := by
    intro s t
    rw [compound_apply]
    exact hA.det_gaussianSandwich_pos_of_le_rank ha hq
      (strictMono_powersetEnum s) (strictMono_powersetEnum t)
  refine ⟨fun s t => (hpos s t).le, ⟨1, one_pos, ?_⟩⟩
  intro s t
  simpa using hpos s t

/-- A Gaussian-smoothed totally nonnegative matrix has an explicit
nonnegative real eigenvalue enumeration. -/
theorem IsTotallyNonneg.gaussianSandwich_charpoly_factorization
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsTotallyNonneg)
    {a : ℝ} (ha : 0 < a) :
    ∃ μ : Fin n → ℝ, (∀ i, 0 ≤ μ i) ∧
    (Matrix.gaussianSandwich A a).charpoly = ∏ i, (X - C (μ i)) := by
  obtain ⟨μ, hμ, -, -, hfactor⟩ :=
    exists_charpoly_eq_prod_nonneg_of_rank_eq_of_compounds_primitive
      (rank_gaussianSandwich A ha)
      (fun q _ hq => hA.compound_gaussianSandwich_isPrimitive ha hq)
  exact ⟨μ, hμ, hfactor⟩

/-- A real nonnegative factorization of a real characteristic polynomial
identifies every root of its complexification with a nonnegative real number. -/
theorem complex_charpoly_roots_nonneg_of_factorization
    {A : Matrix (Fin n) (Fin n) ℝ} {μ : Fin n → ℝ}
    (hμ : ∀ i, 0 ≤ μ i)
    (hfactor : A.charpoly = ∏ i, (X - C (μ i))) :
    ∀ z ∈ (A.map (algebraMap ℝ ℂ)).charpoly.roots,
      ∃ r : ℝ, 0 ≤ r ∧ (r : ℂ) = z := by
  have hfactorC : (A.map (algebraMap ℝ ℂ)).charpoly =
      ∏ i, ((X : ℂ[X]) - C (μ i : ℂ)) := by
    rw [Matrix.charpoly_map, hfactor, Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp
  intro z hz
  rw [hfactorC] at hz
  have hmulti :
      (∏ i, ((X : ℂ[X]) - C (μ i : ℂ))) =
        ((Finset.univ.val.map fun i => (μ i : ℂ)).map
          fun x => (X : ℂ[X]) - C x).prod := by
    rw [Finset.prod, Multiset.map_map]
    rfl
  rw [hmulti, Polynomial.roots_multiset_prod_X_sub_C] at hz
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hz
  exact ⟨μ i, hμ i, rfl⟩

/-- Two-sided Gaussian smoothing converges entrywise to the original matrix. -/
theorem tendsto_gaussianSandwich_atTop (A : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (Matrix.gaussianSandwich A) atTop (nhds A) := by
  have hpair : Tendsto
      (fun a => (gaussianMatrix n a * A, gaussianMatrix n a)) atTop
      (nhds (A, (1 : Matrix (Fin n) (Fin n) ℝ))) :=
    (tendsto_gaussianMatrix_mul_atTop A).prodMk_nhds
      (tendsto_gaussianMatrix_atTop n)
  have hmul : Continuous
      (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
        p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  convert hmul.continuousAt.tendsto.comp hpair using 1
  · funext a
    rfl
  · simp

/-! ### Gantmacher--Krein for totally nonnegative matrices -/

/-- **Every complex eigenvalue of a totally nonnegative real matrix is real
and nonnegative.** -/
theorem IsTotallyNonneg.complex_charpoly_roots_nonneg
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsTotallyNonneg) :
    ∀ z ∈ (A.map (algebraMap ℝ ℂ)).charpoly.roots,
      ∃ r : ℝ, 0 ≤ r ∧ (r : ℂ) = z := by
  apply charpoly_roots_nonneg_real_of_tendsto
    (A := fun k => Matrix.gaussianSandwich A ((k : ℝ) + 1)) (A₀ := A)
  · have hparam : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hmatrix := (tendsto_gaussianSandwich_atTop A).comp hparam
    intro i j
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hmatrix i) j
  · intro k z hz
    obtain ⟨μ, hμ, hfactor⟩ :=
      hA.gaussianSandwich_charpoly_factorization
        (a := (k : ℝ) + 1) (by positivity)
    exact complex_charpoly_roots_nonneg_of_factorization hμ hfactor z hz

/-- The characteristic polynomial of a totally nonnegative real matrix splits
over `ℝ`, and all its roots are nonnegative. -/
theorem IsTotallyNonneg.charpoly_factorization_nonneg
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsTotallyNonneg) :
    ∃ μ : Fin n → ℝ, (∀ i, 0 ≤ μ i) ∧
      A.charpoly = ∏ i, (X - C (μ i)) := by
  classical
  obtain ⟨ν, hνchar, -⟩ :=
    exists_charpoly_compound_eq_prod (A.map (algebraMap ℝ ℂ))
  have hνroot : ∀ i, ν i ∈
      (A.map (algebraMap ℝ ℂ)).charpoly.roots := by
    intro i
    apply (Polynomial.mem_roots
      (A.map (algebraMap ℝ ℂ)).charpoly_monic.ne_zero).mpr
    rw [hνchar, Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose μ hμ_nonneg hμ_eq using
    fun i => hA.complex_charpoly_roots_nonneg (ν i) (hνroot i)
  have hmapped : A.charpoly.map (algebraMap ℝ ℂ) =
      (∏ i, ((X : ℝ[X]) - C (μ i))).map (algebraMap ℝ ℂ) := by
    rw [← charpoly_map, hνchar, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ← hμ_eq i]
    rfl
  exact ⟨μ, hμ_nonneg,
    Polynomial.map_injective (algebraMap ℝ ℂ)
      (algebraMap ℝ ℂ).injective hmapped⟩

/-- The complex spectrum of a totally nonnegative real matrix is contained in
the nonnegative real axis. -/
theorem IsTotallyNonneg.complex_spectrum_nonneg
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsTotallyNonneg)
    {z : ℂ} (hz : z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) :
    ∃ r : ℝ, 0 ≤ r ∧ (r : ℂ) = z := by
  have hroot : (A.map (algebraMap ℝ ℂ)).charpoly.IsRoot z :=
    mem_spectrum_iff_isRoot_charpoly.mp hz
  exact hA.complex_charpoly_roots_nonneg z
    ((Polynomial.mem_roots
      (A.map (algebraMap ℝ ℂ)).charpoly_monic.ne_zero).mpr hroot)

end Matrix
