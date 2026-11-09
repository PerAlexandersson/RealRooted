module

import RealRooted.Basic.AffineInterlacing
import RealRooted.WagnerX.NonnegativeRoots
public import RealRooted.RootLocation.Basic
public import RealRooted.Toeplitz.HessenbergRows

/-!
# The finite TP2 Hessenberg certificate

Let `A` be a real `d × d` matrix, `d = n + 1 ≥ 1`, such that

1. all entries and all ordered `2 × 2` minors are nonnegative (`Matrix.IsTP2`),
2. every column is weakly decreasing down the rows,
3. `A_{ij} = A_{jj}` whenever `i ≤ j` (so `A_{ij} = c_j` in the upper triangle).

Put `F(z) = det (I + z A)` and let `P_k(t)` be the coefficient of `zᵏ` in `1 / (F(z) - t z)`
(`hessenbergRow`). Then `P_k` is monic of degree `k`, has only real roots, all nonnegative, and
consecutive rows interlace: the `k + 1` roots of `P_{k+1}` are separated by, and enclose, the
`k` roots of `P_k` (`Interlaces`). The matrix may be singular and larger than needed.

The proof iterates the affine step `f ↦ (A + X J) f`, `J = 𝟙 e₁ᵀ`, which preserves ordered
interlacing sequences with nonnegative coefficients by Brändén's constant-matrix theorem
(`Matrix.IsTP2.interlacingSeqNonneg_cons_tp2AffineStep`), and identifies
`P_k(t) = (-1)ᵏ f_{k,1}(-t)` through the generating function (`hessenbergRow_eq`). The
interlacing `f_{k,1} ≪ f_{k+1,1}` comes from the first coordinate `f_{k,1}` being interlaced by
every coordinate of the next vector.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

variable {n : ℕ}

/-! ### The vector recursion preserves monic degree and interlacing -/

/-- Every coordinate of `f_k = (A + X J)ᵏ 𝟙` is monic of degree `k`. -/
lemma hessenbergVector_monic_natDegree (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : ℕ)
    (i : Fin (n + 1)) :
    (hessenbergVector A k i).Monic ∧ (hessenbergVector A k i).natDegree = k := by
  induction k generalizing i with
  | zero => simp [hessenbergVector]
  | succ k ih =>
    have hX : (X * hessenbergVector A k 0).Monic := monic_X.mul (ih 0).1
    have hXdeg : (X * hessenbergVector A k 0).natDegree = k + 1 := by
      rw [natDegree_mul' (by simp [(ih 0).1.leadingCoeff]), natDegree_X, (ih 0).2]
      lia
    have hsum : (∑ j, A i j • hessenbergVector A k j).natDegree ≤ k :=
      natDegree_sum_le_of_forall_le _ _ fun j _ =>
        (natDegree_smul_le _ _).trans (ih j).2.le
    have hlt : (∑ j, A i j • hessenbergVector A k j).degree <
        (X * hessenbergVector A k 0).degree :=
      degree_lt_degree (by lia)
    have hstep : hessenbergVector A (k + 1) i =
        ∑ j, A i j • hessenbergVector A k j + X * hessenbergVector A k 0 := by
      simp [hessenbergVector, tp2AffineStep]
    rw [hstep]
    exact ⟨hX.add_of_right hlt, by rw [natDegree_add_eq_right_of_degree_lt hlt, hXdeg]⟩

lemma hessenbergVector_ne_zero (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : ℕ)
    (i : Fin (n + 1)) : hessenbergVector A k i ≠ 0 :=
  (hessenbergVector_monic_natDegree A k i).1.ne_zero

/-- The invariant of the vector recursion: the stage-`k` vector is an interlacing sequence with
nonnegative coefficients, and its first coordinate is interlaced by every coordinate of the
stage-`k + 1` vector. -/
lemma hessenbergVector_invariant {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsTP2)
    (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j) (k : ℕ) :
    IsInterlacingSeqNonneg (List.ofFn (hessenbergVector A k)) ∧
      IsInterlacingSeqNonneg
        (hessenbergVector A k 0 :: List.ofFn (hessenbergVector A (k + 1))) := by
  have hstep : ∀ k, IsInterlacingSeqNonneg (List.ofFn (hessenbergVector A k)) →
      IsInterlacingSeqNonneg
        (hessenbergVector A k 0 :: List.ofFn (hessenbergVector A (k + 1))) := fun k hk =>
    hA.interlacingSeqNonneg_cons_tp2AffineStep hcol zero_le_one hk fun i => by
      simpa [hessenbergVector] using hessenbergVector_ne_zero A (k + 1) i
  induction k with
  | zero =>
    have h0 : IsInterlacingSeqNonneg (List.ofFn (hessenbergVector A 0)) := by
      refine ⟨fun p hp => ?_, isInterlacingSeq_iff_pairwise.mpr (List.pairwise_ofFn.mpr ?_)⟩
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
        exact ⟨⟨one_ne_zero, Splits.one⟩, hasNonnegCoeffs_one⟩
      · intro i j _
        exact StrictInterl.refl one_ne_zero Splits.one
    exact ⟨h0, hstep 0 h0⟩
  | succ k ih =>
    have h1 : IsInterlacingSeqNonneg (List.ofFn (hessenbergVector A (k + 1))) :=
      ih.2.sublist (List.sublist_cons_self _ _)
    exact ⟨h1, hstep (k + 1) h1⟩

/-- **The vector recursion preserves ordered interlacing**: every stage `(A + X J)ᵏ 𝟙` is an
interlacing sequence with nonnegative coefficients. -/
theorem isInterlacingSeqNonneg_hessenbergVector {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTP2) (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j) (k : ℕ) :
    IsInterlacingSeqNonneg (List.ofFn (hessenbergVector A k)) :=
  (hessenbergVector_invariant hA hcol k).1

/-- The first coordinates of consecutive stages interlace: `f_{k,1} ≪ f_{k+1,1}`. -/
theorem strictInterl_hessenbergVector_zero {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTP2) (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j) (k : ℕ) :
    StrictInterl (hessenbergVector A k 0) (hessenbergVector A (k + 1) 0) := by
  have h := (hessenbergVector_invariant hA hcol k).2.2
  rw [isInterlacingSeq_iff_pairwise, List.pairwise_cons] at h
  exact h.1 _ (List.mem_ofFn.mpr ⟨0, rfl⟩)

/-! ### Transport to the rows `P_k(t) = (-1)ᵏ f_{k,1}(-t)` -/

private lemma signedComp_monic_natDegree {f : ℝ[X]} {k : ℕ} (hf : f.Monic)
    (hdeg : f.natDegree = k) :
    (C ((-1 : ℝ) ^ k) * f.comp (-X)).Monic ∧ (C ((-1 : ℝ) ^ k) * f.comp (-X)).natDegree = k := by
  have hq : (-X : ℝ[X]).natDegree ≠ 0 := by simp
  have hne : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp hq, hf.leadingCoeff, hdeg]
    simp only [leadingCoeff_neg, monic_X, Monic.leadingCoeff, one_mul]
    rw [← mul_pow]
    norm_num
  · rw [natDegree_C_mul hne, natDegree_comp, hdeg]
    simp

/-- **Monic degree.** `P_k` is monic of degree `k`. -/
theorem monic_natDegree_hessenbergRow (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (k : ℕ) :
    (hessenbergRow A k).Monic ∧ (hessenbergRow A k).natDegree = k := by
  rw [hessenbergRow_eq A hrow k]
  exact signedComp_monic_natDegree (hessenbergVector_monic_natDegree A k 0).1
    (hessenbergVector_monic_natDegree A k 0).2

/-- **Nonnegative real roots.** `P_k` is real-rooted with all roots in `[0, ∞)`. -/
theorem isRealRootedIn_Ici_hessenbergRow {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTP2) (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (k : ℕ) :
    IsRealRootedIn (Set.Ici 0) (hessenbergRow A k) := by
  have hf := isInterlacingSeqNonneg_hessenbergVector hA hcol k
  have hmem : hessenbergVector A k 0 ∈ List.ofFn (hessenbergVector A k) :=
    List.mem_ofFn.mpr ⟨0, rfl⟩
  have hroot : IsRealRootedIn (Set.Iic 0) (hessenbergVector A k 0) :=
    ⟨(hf.realRooted _ hmem).1, (hf.realRooted _ hmem).2,
      roots_nonpos_of_hasNonnegCoeffs (hf.nonnegCoeffs _ hmem)⟩
  have hcomp := hroot.comp_C_mul_X_add_C (a := -1) 0 (by norm_num)
  have hne : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [hessenbergRow_eq A hrow k]
  have hneg : (-X : ℝ[X]) = C (-1) * X + C 0 := by simp
  rw [hneg]
  refine IsRealRootedIn.C_mul hne (hcomp.mono fun x hx => ?_)
  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici] at hx ⊢
  linarith

private lemma interlaces_signedComp {f g : ℝ[X]} {k : ℕ} (h : StrictInterl f g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Interlaces (C ((-1 : ℝ) ^ k) * f.comp (-X)) (C ((-1 : ℝ) ^ (k + 1)) * g.comp (-X)) := by
  have hne : ∀ m : ℕ, ((-1 : ℝ) ^ m) ≠ 0 := fun m => pow_ne_zero _ (by norm_num)
  have h1 := interlaces_comp_neg_X (h.toInterlaces hdeg)
  rw [Interlaces.iff_strictInterl_and_natDegree] at h1 ⊢
  refine ⟨(h1.1.C_mul_left (hne k)).C_mul_right (hne (k + 1)), ?_⟩
  rw [natDegree_C_mul (hne _), natDegree_C_mul (hne _)]
  exact h1.2

/-- **Interlacing of consecutive rows.** The roots of `P_{k+1}` interlace those of `P_k`: they
are separated by, and enclose, the `k` roots of `P_k`. -/
theorem interlaces_hessenbergRow {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTP2) (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (k : ℕ) :
    Interlaces (hessenbergRow A k) (hessenbergRow A (k + 1)) := by
  rw [hessenbergRow_eq A hrow k, hessenbergRow_eq A hrow (k + 1)]
  refine interlaces_signedComp (strictInterl_hessenbergVector_zero hA hcol k) ?_
  rw [(hessenbergVector_monic_natDegree A k 0).2, (hessenbergVector_monic_natDegree A _ 0).2]

/-- **Finite TP2 Hessenberg certificate.** Let `A` be a `d × d` matrix (`d ≥ 1`) with
nonnegative entries and ordered `2 × 2` minors, weakly decreasing columns, and
`A_{ij} = A_{jj}` for `i ≤ j`. Then the coefficients `P_k(t)` of `zᵏ` in
`1 / (det (I + z A) - t z)` are monic of degree `k`, have only nonnegative real roots, and
consecutive rows interlace. The matrix may be singular. -/
theorem hessenbergRow_certificate {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTP2) (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (k : ℕ) :
    (hessenbergRow A k).Monic ∧ (hessenbergRow A k).natDegree = k ∧
      IsRealRootedIn (Set.Ici 0) (hessenbergRow A k) ∧
      Interlaces (hessenbergRow A k) (hessenbergRow A (k + 1)) :=
  ⟨(monic_natDegree_hessenbergRow A hrow k).1, (monic_natDegree_hessenbergRow A hrow k).2,
    isRealRootedIn_Ici_hessenbergRow hA hcol hrow k, interlaces_hessenbergRow hA hcol hrow k⟩

end RealRooted
