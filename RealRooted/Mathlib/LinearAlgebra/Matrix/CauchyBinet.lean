import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Int.Order.Basic

/-!
# The Cauchy–Binet formula

* `Matrix.det_mul_eq_sum_fun`: `det (A * B) = ∑ p : m → n, det (A.submatrix id p) * ∏ i, B (p i) i`.
* `Matrix.det_mul_eq_sum_minors`: the Cauchy–Binet formula, `det (A * B)` as a sum over
  `|m|`-subsets `S` of `n` of products of maximal minors.
* `Matrix.abs_det_le_one_of_col`: a square integer matrix whose columns have at most one entry
  `1`, at most one entry `-1` and zeros elsewhere has determinant of absolute value at most one.
-/

open Finset Matrix

namespace Matrix

/-- `Fin n`-indexed version of `Matrix.abs_det_le_one_of_col`, proved by induction on `n` via
Laplace expansion along a column with at most one nonzero entry. -/
private theorem abs_det_le_one_of_col_fin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (h1 : ∀ i j, |M i j| ≤ 1)
    (hp : ∀ i i' j, M i j = 1 → M i' j = 1 → i = i')
    (hn : ∀ i i' j, M i j = -1 → M i' j = -1 → i = i') : |M.det| ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases h : ∃ j i₀, ∀ i, i ≠ i₀ → M i j = 0
    · obtain ⟨j, i₀, hi₀⟩ := h
      rw [det_succ_column M j, Finset.sum_eq_single i₀ (fun i _ hi => by simp [hi₀ i hi])
        (by simp)]
      have hminor := ih (M.submatrix i₀.succAbove j.succAbove)
        (fun _ _ => h1 _ _) (fun _ _ _ h h' => Fin.succAbove_right_injective (hp _ _ _ h h'))
        (fun _ _ _ h h' => Fin.succAbove_right_injective (hn _ _ _ h h'))
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      nlinarith [h1 i₀ j, abs_nonneg (M i₀ j),
        abs_nonneg (M.submatrix i₀.succAbove j.succAbove).det]
    · push Not at h
      have hcol : ∀ j, ∑ i, M i j = 0 := by
        intro j
        obtain ⟨i₁, -, h₁⟩ := h j 0
        obtain ⟨i₂, h₂₁, h₂⟩ := h j i₁
        have hv : ∀ i, M i j ≠ 0 → M i j = 1 ∨ M i j = -1 := by
          intro i hi
          have := abs_le.mp (h1 i j)
          lia
        have hpair : (M i₁ j = 1 ∧ M i₂ j = -1) ∨ (M i₁ j = -1 ∧ M i₂ j = 1) := by
          rcases hv i₁ h₁ with ha | ha <;> rcases hv i₂ h₂ with hb | hb
          · exact absurd (hp _ _ _ ha hb) h₂₁.symm
          · exact Or.inl ⟨ha, hb⟩
          · exact Or.inr ⟨ha, hb⟩
          · exact absurd (hn _ _ _ ha hb) h₂₁.symm
        rw [Fintype.sum_eq_add i₁ i₂ h₂₁.symm]
        · rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [ha, hb]
        · intro i ⟨hi₁, hi₂⟩
          by_contra hi
          rcases hv i hi with ha | ha <;> rcases hpair with ⟨hb, hc⟩ | ⟨hb, hc⟩
          · exact hi₁ (hp _ _ _ ha hb)
          · exact hi₂ (hp _ _ _ ha hc)
          · exact hi₂ (hn _ _ _ ha hc)
          · exact hi₁ (hn _ _ _ ha hb)
      have : M.det = 0 := by
        refine exists_vecMul_eq_zero_iff.mp ⟨1, one_ne_zero, funext fun j => ?_⟩
        simpa [vecMul, dotProduct] using hcol j
      simp [this]

end Matrix

namespace Matrix

variable {m n R : Type*} [Fintype m] [DecidableEq m] [CommRing R]

/-- Expansion of `det (A * B)` as a sum over all maps `p : m → n`. -/
theorem det_mul_eq_sum_fun [Fintype n] (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det = ∑ p : m → n, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => sum_congr rfl fun σ _ => ?_
  rw [prod_mul_distrib, mul_assoc]

omit [DecidableEq m] in
private theorem image_equiv_perm [DecidableEq n] (S : Finset n) (e : m ≃ S)
    (τ : Equiv.Perm m) :
    univ.image (fun i => (e (τ i) : n)) = S := by
  ext x
  simp only [mem_image, mem_univ, true_and]
  refine ⟨fun ⟨i, hi⟩ => hi ▸ (e (τ i)).2, fun hx => ⟨τ.symm (e.symm ⟨x, hx⟩), by simp⟩⟩

/-- **Cauchy–Binet formula**: for `A : Matrix m n R` and `B : Matrix n m R`, the determinant
of `A * B` is the sum over all `S : Finset n` with `#S = card m` of the products of the
corresponding maximal minors. The bijections `e S : m ≃ S` used to index the minors are
arbitrary. -/
theorem det_mul_eq_sum_minors [Fintype n] (A : Matrix m n R) (B : Matrix n m R)
    (e : (S : {S : Finset n // S.card = Fintype.card m}) → m ≃ S.1) :
    (A * B).det = ∑ S : {S : Finset n // S.card = Fintype.card m},
      (A.submatrix id (fun i => (e S i : n))).det *
        (B.submatrix (fun i => (e S i : n)) id).det := by
  classical
  rw [det_mul_eq_sum_fun]
  set F : (m → n) → R := fun p => (A.submatrix id p).det * ∏ i, B (p i) i with hF
  have hzero : ∀ p : m → n, ¬ Function.Injective p → F p = 0 := by
    intro p hp
    simp only [Function.Injective, not_forall] at hp
    obtain ⟨i, j, hij, hne⟩ := hp
    simp only [hF]
    rw [det_zero_of_column_eq hne (fun k => by simp [hij]), zero_mul]
  rw [← sum_filter_of_ne (p := Function.Injective)
    (fun p _ h => by_contra fun hp => h (hzero p hp))]
  have hperm : ∀ (S : {S : Finset n // S.card = Fintype.card m}) (τ : Equiv.Perm m),
      F (fun i => (e S (τ i) : n)) =
        (A.submatrix id (fun i => (e S i : n))).det *
          (Equiv.Perm.sign τ * ∏ i, B (e S (τ i)) i) := by
    intro S τ
    simp only [hF]
    have : A.submatrix id (fun i => (e S (τ i) : n)) =
        (A.submatrix id (fun i => (e S i : n))).submatrix id τ := by
      ext; simp
    rw [this, det_permute']
    ring
  have hS : ∀ S : {S : Finset n // S.card = Fintype.card m},
      (A.submatrix id (fun i => (e S i : n))).det * (B.submatrix (fun i => (e S i : n)) id).det
        = ∑ τ : Equiv.Perm m, F (fun i => (e S (τ i) : n)) := by
    intro S
    rw [det_apply' (B.submatrix _ id), mul_sum]
    exact sum_congr rfl fun τ _ => (hperm S τ).symm
  rw [sum_congr rfl fun S _ => hS S, ← Fintype.sum_prod_type']
  refine (sum_bij (fun x _ => fun i => (e x.1 (x.2 i) : n)) ?_ ?_ ?_ ?_).symm
  · intro x _
    simp only [mem_filter, mem_univ, true_and]
    intro i j hij
    exact x.2.injective ((e x.1).injective (Subtype.ext hij))
  · intro x _ y _ hxy
    have hS : x.1 = y.1 := by
      apply Subtype.ext
      rw [← image_equiv_perm x.1.1 (e x.1) x.2, ← image_equiv_perm y.1.1 (e y.1) y.2]
      exact congrArg (fun p => univ.image p) hxy
    obtain ⟨S, τ⟩ := x
    obtain ⟨S', τ'⟩ := y
    simp only at hS
    subst hS
    simp only [Prod.mk.injEq, true_and]
    ext i
    exact (e S).injective (Subtype.ext (congrFun hxy i))
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    have hcard : (univ.image p).card = Fintype.card m := by
      rw [card_image_of_injective _ hp, card_univ]
    let S : {S : Finset n // S.card = Fintype.card m} := ⟨univ.image p, hcard⟩
    let g : m → m := fun i => (e S).symm ⟨p i, mem_image_of_mem p (mem_univ i)⟩
    have hg : Function.Injective g := by
      intro i j hij
      exact hp (congrArg Subtype.val ((e S).symm.injective hij))
    refine ⟨(S, Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)), mem_univ _, ?_⟩
    funext i
    simp [g]
  · exact fun _ _ => rfl

end Matrix

namespace Matrix

/-- A square integer matrix in which every column has entries in `{-1, 0, 1}`, at most one
entry `1` and at most one entry `-1` has determinant in `{-1, 0, 1}`. -/
theorem abs_det_le_one_of_col {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (h1 : ∀ i j, |M i j| ≤ 1)
    (hp : ∀ i i' j, M i j = 1 → M i' j = 1 → i = i')
    (hn : ∀ i i' j, M i j = -1 → M i' j = -1 → i = i') : |M.det| ≤ 1 := by
  rw [← det_reindex_self (Fintype.equivFin ι) M]
  exact abs_det_le_one_of_col_fin _ (fun _ _ => h1 _ _)
    (fun _ _ _ h h' => (Fintype.equivFin ι).symm.injective (hp _ _ _ h h'))
    (fun _ _ _ h h' => (Fintype.equivFin ι).symm.injective (hn _ _ _ h h'))

end Matrix
