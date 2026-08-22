import Mathlib.Combinatorics.Colex
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.CauchyBinet
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Compound matrices

The `q`-th **compound matrix** of `A` collects all `q × q` minors of `A`, indexed
by the increasing `q`-element selections of rows and columns.  Its two basic
properties are:

* multiplicativity, `compound q (L * A) = compound q L * compound q A`, which is
  exactly the Cauchy-Binet expansion re-indexed;
* entrywise nonnegativity for totally nonnegative `A`, which is immediate from
  the definitions.

These are the inputs the Gantmacher-Krein route needs before the spectral step
(that the eigenvalues of `compound q A` are the `q`-fold products of the
eigenvalues of `A`).  The triangular half of that step is also proved here:
`charpoly_compound_of_blockTriangular` computes the characteristic polynomial of
the compound of an upper triangular matrix, and `charpoly_compound_conj` shows
the compound characteristic polynomial is invariant under conjugation.  What
remains for the full spectral statement is triangularization itself
(every matrix over an algebraically closed field is conjugate to an upper
triangular one), which Mathlib currently lacks at the matrix level.
-/

open scoped BigOperators

namespace Matrix

variable {R : Type*} [CommRing R]

/-- The increasing enumeration of a `q`-element selection, as a function. -/
def powersetEnum {n q : ℕ} (s : Set.powersetCard (Fin n) q) : Fin q → Fin n :=
  Set.powersetCard.ofFinEmbEquiv.symm s

theorem strictMono_powersetEnum {n q : ℕ} (s : Set.powersetCard (Fin n) q) :
    StrictMono (powersetEnum s) :=
  (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono

/-- The `q`-th compound matrix: its `(s, t)` entry is the minor of `A` on the
rows selected by `s` and the columns selected by `t`. -/
def compound {m n : ℕ} (q : ℕ) (A : Matrix (Fin m) (Fin n) R) :
    Matrix (Set.powersetCard (Fin m) q) (Set.powersetCard (Fin n) q) R :=
  fun s t => (A.submatrix (powersetEnum s) (powersetEnum t)).det

@[simp] theorem compound_apply {m n q : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (s : Set.powersetCard (Fin m) q) (t : Set.powersetCard (Fin n) q) :
    compound q A s t = (A.submatrix (powersetEnum s) (powersetEnum t)).det := rfl

/-- **Compound matrices are multiplicative.**  This is the Cauchy-Binet
expansion, re-indexed. -/
theorem compound_mul {l n m : ℕ} (q : ℕ)
    (L : Matrix (Fin l) (Fin n) R) (A : Matrix (Fin n) (Fin m) R) :
    compound q (L * A) = compound q L * compound q A := by
  ext s t
  rw [compound_apply, Matrix.mul_apply]
  rw [Matrix.det_submatrix_mul_eq_sum_powersetCard]
  rfl

/-- A totally nonnegative matrix has an entrywise nonnegative compound matrix. -/
theorem compound_nonneg {m n : ℕ} [PartialOrder R] (q : ℕ)
    {A : Matrix (Fin m) (Fin n) R} (hA : A.IsTotallyNonnegRect)
    (s : Set.powersetCard (Fin m) q) (t : Set.powersetCard (Fin n) q) :
    0 ≤ compound q A s t :=
  hA (strictMono_powersetEnum s) (strictMono_powersetEnum t)

/-- The first compound matrix is `A` itself, up to the canonical indexing. -/
theorem compound_one_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (s : Set.powersetCard (Fin m) 1) (t : Set.powersetCard (Fin n) 1) :
    compound 1 A s t = A (powersetEnum s 0) (powersetEnum t 0) := by
  rw [compound_apply, Matrix.det_fin_one]
  rfl

/-! ### Compounds of triangular matrices

For upper triangular `T` the compound matrix is again upper triangular, with
respect to the binary encoding of the selections, and its diagonal entries are
the products of the selected diagonal entries of `T`.  Together these compute
the characteristic polynomial of `compound q T`.
-/

open Polynomial in
/-- A block triangular matrix with an *injective* block map is genuinely
triangular: its determinant is the product of its diagonal.  This is
`Matrix.det_of_upperTriangular` without asking for a linear order on the index
type itself. -/
theorem BlockTriangular.det_of_injective {m α : Type*} [DecidableEq m] [Fintype m]
    [LinearOrder α] {M : Matrix m m R} {b : m → α} (hb : Function.Injective b)
    (h : M.BlockTriangular b) : M.det = ∏ i, M i i := by
  classical
  rw [h.det, Finset.prod_image fun x _ y _ hxy => hb hxy]
  refine Finset.prod_congr rfl fun i _ => ?_
  haveI : Unique {j // b j = b i} := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext (hb j.prop)⟩
  have hd : (default : {j // b j = b i}) = ⟨i, rfl⟩ :=
    Subtype.ext (hb (default : {j // b j = b i}).prop)
  rw [Matrix.det_unique, hd]
  rfl

open Polynomial in
/-- The characteristic polynomial of a block triangular matrix with an
injective block map. -/
theorem BlockTriangular.charpoly_of_injective {m α : Type*} [DecidableEq m] [Fintype m]
    [LinearOrder α] {M : Matrix m m R} {b : m → α} (hb : Function.Injective b)
    (h : M.BlockTriangular b) : M.charpoly = ∏ i, (X - C (M i i)) := by
  rw [Matrix.charpoly, h.charmatrix.det_of_injective hb]
  simp only [charmatrix_apply_eq]

/-- If a permutation matches a monotone selection below another pointwise, the
selections were already pointwise comparable.  The pigeonhole step behind the
triangularity of compound matrices. -/
private theorem forall_le_of_perm_le {q n : ℕ} {u v : Fin q → Fin n}
    (hu : Monotone u) (hv : Monotone v) {σ : Equiv.Perm (Fin q)}
    (h : ∀ k, u (σ k) ≤ v k) (i : Fin q) : u i ≤ v i := by
  obtain ⟨j, hji, hij⟩ : ∃ j, j ≤ i ∧ i ≤ σ j := by
    by_contra hc
    push Not at hc
    have hmaps : ∀ j ∈ Finset.Iic i, σ j ∈ Finset.Iio i := fun j hj =>
      Finset.mem_Iio.2 (hc j (Finset.mem_Iic.1 hj))
    have hcard : (Finset.Iio i).card < (Finset.Iic i).card :=
      Finset.card_lt_card ((Finset.ssubset_iff_of_subset Finset.Iio_subset_Iic_self).2
        ⟨i, Finset.mem_Iic.2 le_rfl, fun hmem => lt_irrefl i (Finset.mem_Iio.1 hmem)⟩)
    obtain ⟨x, _, y, _, hxy, hfxy⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
    exact hxy (σ.injective hfxy)
  exact (hu hij).trans ((h j).trans (hv hji))

/-- The minor of an upper triangular matrix vanishes unless the row selection is
pointwise dominated by the column selection. -/
theorem compound_apply_eq_zero_of_blockTriangular {n q : ℕ}
    {T : Matrix (Fin n) (Fin n) R} (hT : T.BlockTriangular id)
    {s t : Set.powersetCard (Fin n) q}
    (h : ¬ ∀ k, powersetEnum s k ≤ powersetEnum t k) :
    compound q T s t = 0 := by
  rw [compound_apply, Matrix.det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  by_cases hall : ∀ k, powersetEnum s (σ k) ≤ powersetEnum t k
  · exact absurd (forall_le_of_perm_le (strictMono_powersetEnum s).monotone
      (strictMono_powersetEnum t).monotone hall) h
  · push Not at hall
    obtain ⟨k, hk⟩ := hall
    have hprod : ∏ i, T.submatrix (powersetEnum s) (powersetEnum t) (σ i) i = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (hT hk)
    rw [hprod, smul_zero]

/-- The binary encoding of a selection.  It is injective and monotone for
pointwise domination, so it linearizes the triangularity of compound matrices. -/
def powersetCode {n q : ℕ} (s : Set.powersetCard (Fin n) q) : ℕ :=
  ∑ k, 2 ^ (powersetEnum s k : ℕ)

theorem powersetCode_le_of_forall_le {n q : ℕ} {s t : Set.powersetCard (Fin n) q}
    (h : ∀ k, powersetEnum s k ≤ powersetEnum t k) :
    powersetCode s ≤ powersetCode t :=
  Finset.sum_le_sum fun k _ => Nat.pow_le_pow_right (by norm_num) (h k)

theorem powersetCode_injective {n q : ℕ} :
    Function.Injective (powersetCode (n := n) (q := q)) := by
  intro s t hst
  have hsum : ∀ u : Set.powersetCard (Fin n) q,
      powersetCode u = ∑ a ∈ Finset.univ.image fun k => (powersetEnum u k : ℕ), 2 ^ a :=
    fun u => (Finset.sum_image fun x _ y _ hxy =>
      (strictMono_powersetEnum u).injective (Fin.val_injective hxy)).symm
  rw [hsum s, hsum t] at hst
  have himg := Finset.geomSum_injective le_rfl hst
  have hmem : ∀ (u : Set.powersetCard (Fin n) q) (i : Fin n),
      i ∈ u ↔ (i : ℕ) ∈ Finset.univ.image fun k => (powersetEnum u k : ℕ) := by
    intro u i
    rw [← Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem u i]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, by rw [show powersetEnum u k = i from hk]⟩,
      fun ⟨k, hk⟩ => ⟨k, Fin.val_injective hk⟩⟩
  exact SetLike.ext fun i => by rw [hmem s i, hmem t i, himg]

/-- The compound of an upper triangular matrix is upper triangular for the
binary encoding of the selections. -/
theorem blockTriangular_compound {n : ℕ} {T : Matrix (Fin n) (Fin n) R}
    (hT : T.BlockTriangular id) (q : ℕ) :
    (compound q T).BlockTriangular powersetCode := by
  intro s t hlt
  exact compound_apply_eq_zero_of_blockTriangular hT fun hall =>
    absurd (powersetCode_le_of_forall_le hall) (not_le.2 hlt)

/-- The diagonal minors of an upper triangular matrix are the products of the
selected diagonal entries. -/
theorem compound_apply_self_of_blockTriangular {n q : ℕ} {T : Matrix (Fin n) (Fin n) R}
    (hT : T.BlockTriangular id) (s : Set.powersetCard (Fin n) q) :
    compound q T s s = ∏ k, T (powersetEnum s k) (powersetEnum s k) := by
  have hsub : (T.submatrix (powersetEnum s) (powersetEnum s)).BlockTriangular id :=
    fun k l hlk => hT (strictMono_powersetEnum s hlk)
  rw [compound_apply, Matrix.det_of_upperTriangular hsub]
  rfl

open Polynomial in
/-- **The characteristic polynomial of the compound of a triangular matrix.**
Its roots are exactly the `q`-fold products of the diagonal of `T`, over the
increasing selections.  Together with triangularization this is the eigenvalue
statement for compound matrices. -/
theorem charpoly_compound_of_blockTriangular {n : ℕ} {T : Matrix (Fin n) (Fin n) R}
    (hT : T.BlockTriangular id) (q : ℕ) :
    (compound q T).charpoly =
      ∏ s : Set.powersetCard (Fin n) q,
        (X - C (∏ k, T (powersetEnum s k) (powersetEnum s k))) := by
  rw [(blockTriangular_compound hT q).charpoly_of_injective powersetCode_injective]
  exact Finset.prod_congr rfl fun s _ => by
    rw [compound_apply_self_of_blockTriangular hT]

/-! ### Conjugation invariance -/

/-- The compound of the identity is the identity. -/
theorem compound_one {n q : ℕ} : compound q (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext s t
  rcases eq_or_ne s t with rfl | hst
  · rw [compound_apply, Matrix.one_apply_eq,
      show (1 : Matrix (Fin n) (Fin n) R).submatrix (powersetEnum s) (powersetEnum s) = 1 by
        ext k l
        simp [Matrix.one_apply, (strictMono_powersetEnum s).injective.eq_iff],
      Matrix.det_one]
  · rw [compound_apply, Matrix.one_apply_ne hst]
    obtain ⟨k, hk⟩ : ∃ k, ∀ l, powersetEnum t l ≠ powersetEnum s k := by
      by_contra hc
      push Not at hc
      refine hst ?_
      have hsub : ∀ i : Fin n, i ∈ s → i ∈ t := by
        intro i hi
        rw [← Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem] at hi ⊢
        obtain ⟨a, ha⟩ := hi
        obtain ⟨l, hl⟩ := hc a
        exact ⟨l, hl.trans ha⟩
      have hcard : (t : Finset (Fin n)).card ≤ (s : Finset (Fin n)).card := by
        rw [Set.powersetCard.mem_iff.1 s.prop, Set.powersetCard.mem_iff.1 t.prop]
      exact Subtype.ext (Finset.eq_of_subset_of_card_le (fun i hi => hsub i hi) hcard)
    exact Matrix.det_eq_zero_of_row_eq_zero k fun l => Matrix.one_apply_ne (hk l).symm

/-- The characteristic polynomial of a compound matrix is invariant under
conjugation, by multiplicativity. -/
theorem charpoly_compound_conj {n q : ℕ} (P : (Matrix (Fin n) (Fin n) R)ˣ)
    (A : Matrix (Fin n) (Fin n) R) :
    (compound q ((P : Matrix (Fin n) (Fin n) R) * A *
      ((P⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R))).charpoly =
      (compound q A).charpoly := by
  rw [compound_mul, compound_mul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← compound_mul,
    Units.inv_mul, compound_one, Matrix.one_mul]

end Matrix
