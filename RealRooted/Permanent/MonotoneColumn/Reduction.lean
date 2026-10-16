module

public import RealRooted.Permanent.Ferrers
public import RealRooted.Permanent.Stability.Cone

/-!
# Reduction from zero-one columns to arbitrary decreasing columns

This file proves the fixed-direction convex-cone reduction in Proposition 2.4
of Brändén--Haglund--Visontai--Wagner, arXiv:1010.2565v2, using the prefix
decomposition `monotonePrefixCombination_eq` of weakly decreasing vectors.
-/

@[expose] public section

open scoped BigOperators

namespace Matrix

/-- The permanent is additive in one selected column. -/
theorem permanent_updateCol_add {n R : Type*} [Fintype n] [DecidableEq n]
    [CommSemiring R] (M : Matrix n n R) (j : n) (u v : n → R) :
    permanent (M.updateCol j (u + v)) =
      permanent (M.updateCol j u) + permanent (M.updateCol j v) := by
  classical
  unfold permanent
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hprod (w : n → R) :
      ∏ k ∈ Finset.univ.erase j, (M.updateCol j w) (σ k) k =
        ∏ k ∈ Finset.univ.erase j, M (σ k) k := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hk)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [updateCol_self, Pi.add_apply, add_mul]
  rw [hprod (u + v), hprod u, hprod v]

end Matrix

namespace RealRooted
namespace Permanent

noncomputable section

/-- The coefficient of the selected column variable after the entries in
that column have been removed. -/
def columnDirection {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    MvPolynomial (Fin n) ℝ :=
  Matrix.permanent
    (Matrix.updateCol
      (fun i k => MvPolynomial.X k + MvPolynomial.C (A i k)) j
      (fun _ => 1))

/-- The constant term in the selected column variable, with the entries of
that column prescribed by `v`. -/
def columnBase {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    (v : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  Matrix.permanent
    (Matrix.updateCol
      (fun i k => MvPolynomial.X k + MvPolynomial.C (A i k)) j
      (fun i => MvPolynomial.C (v i)))

/-- Replacing one matrix column gives an affine polynomial in its column
variable, with direction independent of the replacement vector. -/
theorem columnPermanent_updateCol_eq_base_add_X_mul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) (v : Fin n → ℝ) :
    columnPermanent (A.updateCol j v) =
      columnBase A j v + MvPolynomial.X j * columnDirection A j := by
  classical
  let M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℝ) :=
    fun i k => MvPolynomial.X k + MvPolynomial.C (A i k)
  have hmatrix :
      (fun i k =>
          MvPolynomial.X k + MvPolynomial.C ((A.updateCol j v) i k)) =
        M.updateCol j
          ((fun _ => MvPolynomial.X j) + fun i => MvPolynomial.C (v i)) := by
    funext i k
    by_cases hkj : k = j
    · subst k
      rw [Matrix.updateCol_self, Matrix.updateCol_self]
      rfl
    · rw [Matrix.updateCol_ne hkj, Matrix.updateCol_ne hkj]
  have hx : (fun _ : Fin n => MvPolynomial.X j) =
      (MvPolynomial.X j : MvPolynomial (Fin n) ℝ) •
        (fun _ : Fin n => (1 : MvPolynomial (Fin n) ℝ)) := by
    funext i
    simp
  calc
    columnPermanent (A.updateCol j v) =
        Matrix.permanent
          (M.updateCol j
            ((fun _ => MvPolynomial.X j) +
              fun i => MvPolynomial.C (v i))) := by
      rw [columnPermanent, hmatrix]
    _ = Matrix.permanent (M.updateCol j fun _ => MvPolynomial.X j) +
          Matrix.permanent (M.updateCol j fun i => MvPolynomial.C (v i)) :=
      Matrix.permanent_updateCol_add M j _ _
    _ = MvPolynomial.X j *
          Matrix.permanent (M.updateCol j fun _ => 1) +
          Matrix.permanent (M.updateCol j fun i => MvPolynomial.C (v i)) := by
      rw [hx, Matrix.permanent_updateCol_smul]
    _ = columnBase A j v + MvPolynomial.X j * columnDirection A j := by
      unfold columnBase columnDirection
      dsimp only [M]
      ring

/-- The column base is additive in the replacement vector. -/
theorem columnBase_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) (u v : Fin n → ℝ) :
    columnBase A j (u + v) = columnBase A j u + columnBase A j v := by
  classical
  have hCadd :
      (fun i => (MvPolynomial.C ((u + v) i) : MvPolynomial (Fin n) ℝ)) =
        (fun i => (MvPolynomial.C (u i) : MvPolynomial (Fin n) ℝ)) +
          fun i => (MvPolynomial.C (v i) : MvPolynomial (Fin n) ℝ) := by
    funext i
    simp
  unfold columnBase
  rw [hCadd]
  exact Matrix.permanent_updateCol_add
      (fun i k => MvPolynomial.X k + MvPolynomial.C (A i k)) j
      (fun i => MvPolynomial.C (u i))
      (fun i => MvPolynomial.C (v i))

/-- A scalar on a vector becomes the corresponding constant
polynomial scalar on its column base. -/
theorem columnBase_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) (a : ℝ) (v : Fin n → ℝ) :
    columnBase A j (a • v) = MvPolynomial.C a * columnBase A j v := by
  classical
  have hCsmul :
      (fun i => (MvPolynomial.C ((a • v) i) : MvPolynomial (Fin n) ℝ)) =
        (MvPolynomial.C a : MvPolynomial (Fin n) ℝ) •
          fun i => (MvPolynomial.C (v i) : MvPolynomial (Fin n) ℝ) := by
    funext i
    simp
  unfold columnBase
  rw [hCsmul]
  exact Matrix.permanent_updateCol_smul
      (fun i k => MvPolynomial.X k + MvPolynomial.C (A i k)) j
      (MvPolynomial.C a) (fun i => MvPolynomial.C (v i))

/-- The zero replacement vector has zero column base. -/
@[simp] theorem columnBase_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) : columnBase A j 0 = 0 := by
  rw [show (0 : Fin n → ℝ) = (0 : ℝ) • (fun _ => 1) by simp,
    columnBase_smul]
  simp

/-- Send the selected variable to the fresh pencil coordinate and all other
variables to their corresponding old coordinate. -/
def isolateColumnVariable {n : ℕ} (j : Fin n) : Fin n → Option (Fin n) :=
  fun k => if k = j then none else some k

/-- The column base does not contain the selected variable, so isolating
that variable has the same effect as the ordinary `some` renaming. -/
theorem rename_isolateColumnVariable_columnBase {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) (v : Fin n → ℝ) :
    MvPolynomial.rename (isolateColumnVariable j) (columnBase A j v) =
      MvPolynomial.rename some (columnBase A j v) := by
  classical
  let M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℝ) :=
    fun i k => MvPolynomial.X k + MvPolynomial.C (A i k)
  change MvPolynomial.rename (isolateColumnVariable j)
      (Matrix.permanent (M.updateCol j fun i => MvPolynomial.C (v i))) =
    MvPolynomial.rename some
      (Matrix.permanent (M.updateCol j fun i => MvPolynomial.C (v i)))
  unfold Matrix.permanent
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro k hk
  by_cases hkj : k = j
  · subst k
    simp
  · simp only [Matrix.updateCol_ne hkj]
    dsimp only [M]
    simp [hkj, isolateColumnVariable]

/-- The column direction does not contain the selected variable. -/
theorem rename_isolateColumnVariable_columnDirection {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    MvPolynomial.rename (isolateColumnVariable j) (columnDirection A j) =
      MvPolynomial.rename some (columnDirection A j) := by
  classical
  let M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℝ) :=
    fun i k => MvPolynomial.X k + MvPolynomial.C (A i k)
  change MvPolynomial.rename (isolateColumnVariable j)
      (Matrix.permanent (M.updateCol j fun _ => 1)) =
    MvPolynomial.rename some (Matrix.permanent (M.updateCol j fun _ => 1))
  unfold Matrix.permanent
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro k hk
  by_cases hkj : k = j
  · subst k
    simp
  · simp only [Matrix.updateCol_ne hkj]
    dsimp only [M]
    simp [hkj, isolateColumnVariable]

/-- Isolating the selected column variable turns its permanent into the
fresh-variable affine pencil used by `MvStablePencil`. -/
theorem rename_isolateColumnVariable_columnPermanent_updateCol {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) (v : Fin n → ℝ) :
    MvPolynomial.rename (isolateColumnVariable j)
        (columnPermanent (A.updateCol j v)) =
      MvPolynomial.rename some (columnBase A j v) +
        MvPolynomial.X none *
          MvPolynomial.rename some (columnDirection A j) := by
  rw [columnPermanent_updateCol_eq_base_add_X_mul, map_add, map_mul,
    rename_isolateColumnVariable_columnBase,
    rename_isolateColumnVariable_columnDirection]
  simp [isolateColumnVariable]

/-- Stability of a permanent with a prescribed column produces the stable
pencil with the common column direction. -/
theorem mvStablePencil_columnDirection_columnBase_of_stable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) (v : Fin n → ℝ)
    (h : MvRealStable (columnPermanent (A.updateCol j v))) :
    MvStablePencil (columnDirection A j) (columnBase A j v) := by
  have hrename := h.rename (isolateColumnVariable j)
  rw [rename_isolateColumnVariable_columnPermanent_updateCol] at hrename
  exact hrename

/-- Stability with the zero replacement column makes the common column
direction nonzero and real stable. -/
theorem columnDirection_stable_of_zero_column_stable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    (hzero : MvRealStable (columnPermanent (A.updateCol j 0))) :
    MvRealStable (columnDirection A j) := by
  have hpencil :=
    mvStablePencil_columnDirection_columnBase_of_stable A j 0 hzero
  rcases MvStablePencil.left hpencil with hdirection | hdirection
  · exfalso
    apply (show MvRealStable
      (MvPolynomial.rename some (columnBase A j 0) +
        MvPolynomial.X none *
          MvPolynomial.rename some (columnDirection A j)) from hpencil).ne_zero
    simp [hdirection]
  · exact hdirection

/-- Adding a real constant to every entry of a prescribed column translates
its column variable and therefore preserves stability. -/
theorem columnPermanent_updateCol_add_const_stable_of_mvStablePencil {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) (u : Fin n → ℝ)
    (c : ℝ)
    (h : MvStablePencil (columnDirection A j) (columnBase A j u)) :
    MvRealStable
      (columnPermanent (A.updateCol j fun i => u i + c)) := by
  have hvector : (fun i => u i + c) = u + c • (fun _ : Fin n => 1) := by
    funext i
    simp
  have hbaseOne : columnBase A j (fun _ : Fin n => 1) =
      columnDirection A j := rfl
  have hpoly :
      columnPermanent (A.updateCol j fun i => u i + c) =
        columnBase A j u + MvPolynomial.C c * columnDirection A j +
          MvPolynomial.X j * columnDirection A j := by
    rw [hvector, columnPermanent_updateCol_eq_base_add_X_mul,
      columnBase_add, columnBase_smul, hbaseOne]
  rw [hpoly]
  intro z hz
  let w : Option (Fin n) → ℂ := fun o => o.elim (z j + c) z
  have hw : ∀ o, 0 < (w o).im := by
    intro o
    cases o with
    | none => simpa [w] using hz j
    | some k => simpa [w] using hz k
  have hwSome : w ∘ some = z := by
    funext k
    rfl
  have hwNone : w none = z j + c := rfl
  have hne := h w hw
  simp only [complexifyMv, map_add, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_rename,
    MvPolynomial.eval_rename, MvPolynomial.eval_C, MvPolynomial.eval_X,
    hwSome, hwNone] at hne ⊢
  intro hzero
  apply hne
  linear_combination hzero

/-- If every decreasing zero-one replacement of one column is stable, then
every decreasing real replacement of that column is stable. -/
theorem columnPermanent_updateCol_stable_of_zeroOne_decreasing {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (j : Fin (m + 1))
    (v : Fin (m + 1) → ℝ) (hv : IsWeaklyDecreasingVector v)
    (hstable : ∀ q : Fin (m + 1) → ℝ,
      (∀ i, q i = 0 ∨ q i = 1) → IsWeaklyDecreasingVector q →
        MvRealStable (columnPermanent (A.updateCol j q))) :
    MvRealStable (columnPermanent (A.updateCol j v)) := by
  let F := columnDirection A j
  have hzeroValues : ∀ i, (0 : Fin (m + 1) → ℝ) i = 0 ∨
      (0 : Fin (m + 1) → ℝ) i = 1 := by
    intro i
    left
    rfl
  have hzeroDecreasing :
      IsWeaklyDecreasingVector (0 : Fin (m + 1) → ℝ) := by
    intro i k hik
    rfl
  have hzero := hstable 0 hzeroValues hzeroDecreasing
  have hF : MvRealStable F :=
    columnDirection_stable_of_zero_column_stable A j hzero
  have hzeroPencil : MvStablePencil F (columnBase A j 0) :=
    mvStablePencil_columnDirection_columnBase_of_stable A j 0 hzero
  let d : Fin m → ℝ := fun r => v r.castSucc - v r.succ
  let q : Fin m → Fin (m + 1) → ℝ := prefixIndicator
  have hterm : ∀ r : Fin m,
      MvStablePencil F (columnBase A j (d r • q r)) := by
    intro r
    have hq := hstable (q r)
      (fun i => prefixIndicator_zero_or_one r i)
      (prefixIndicator_isWeaklyDecreasingVector r)
    have hqPencil :=
      mvStablePencil_columnDirection_columnBase_of_stable A j (q r) hq
    have hscaled := hqPencil.nonneg_C_mul_right_of_left_stable hF
      (d r) (adjacentDifference_nonneg hv r)
    rw [← columnBase_smul] at hscaled
    exact hscaled
  have hsum : ∀ s : Finset (Fin m),
      MvStablePencil F (columnBase A j (∑ r ∈ s, d r • q r)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzeroPencil
    | @insert r s hrs ih =>
        rw [Finset.sum_insert hrs, columnBase_add]
        exact (hterm r).add_right_of_left_stable hF ih
  let u : Fin (m + 1) → ℝ := ∑ r : Fin m, d r • q r
  have huPencil : MvStablePencil F (columnBase A j u) := by
    simpa [u] using hsum Finset.univ
  have hvEq : (fun i => u i + v (Fin.last m)) = v := by
    funext i
    have hdecomp := monotonePrefixCombination_eq v i
    unfold monotonePrefixCombination at hdecomp
    rw [max_zero_sub_max_neg_zero_eq_self] at hdecomp
    simpa [u, d, q, add_comm, smul_eq_mul] using hdecomp
  rw [← hvEq]
  exact columnPermanent_updateCol_add_const_stable_of_mvStablePencil
    A j u (v (Fin.last m)) huPencil

/-- The fixed-direction cone and prefix decomposition reduce arbitrary real
decreasing columns to decreasing zero-one columns. -/
theorem columnPermanent_mvRealStable_of_decreasingColumns_from_zeroOne
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hcols : Matrix.HasWeaklyDecreasingColumns A)
    (hzeroOne : ∀ B : Matrix (Fin n) (Fin n) ℝ,
      Matrix.IsZeroOne B → Matrix.HasWeaklyDecreasingColumns B →
        MvRealStable (columnPermanent B)) :
    MvRealStable (columnPermanent A) := by
  let Good : Finset (Fin n) → Prop := fun s =>
    ∀ B : Matrix (Fin n) (Fin n) ℝ,
      Matrix.HasWeaklyDecreasingColumns B →
      (∀ j, j ∉ s → ∀ i, B i j = 0 ∨ B i j = 1) →
      MvRealStable (columnPermanent B)
  have hGood : ∀ s : Finset (Fin n), Good s := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro B hBcols hBzeroOne
        apply hzeroOne B
        · intro i j
          exact hBzeroOne j (by simp) i
        · exact hBcols
    | @insert j s hjs ih =>
        intro B hBcols hBzeroOne
        cases n with
        | zero => exact Fin.elim0 j
        | succ m =>
            have hv : IsWeaklyDecreasingVector (fun i => B i j) := by
              exact (hasWeaklyDecreasingColumns_iff_columns B).1 hBcols j
            have hreplacement : ∀ q : Fin (m + 1) → ℝ,
                (∀ i, q i = 0 ∨ q i = 1) →
                IsWeaklyDecreasingVector q →
                MvRealStable (columnPermanent (B.updateCol j q)) := by
              intro q hqZeroOne hqDecreasing
              apply ih (B.updateCol j q)
              · rw [hasWeaklyDecreasingColumns_iff_columns]
                intro k
                by_cases hkj : k = j
                · subst k
                  simpa only [Matrix.updateCol_self] using hqDecreasing
                · intro i l hil
                  simpa only [Matrix.updateCol_ne hkj] using
                    hBcols k i l hil
              · intro k hks i
                by_cases hkj : k = j
                · subst k
                  rw [Matrix.updateCol_self]
                  exact hqZeroOne i
                · rw [Matrix.updateCol_ne hkj]
                  exact hBzeroOne k (by simp [hkj, hks]) i
            have hstable :=
              columnPermanent_updateCol_stable_of_zeroOne_decreasing
                B j (fun i => B i j) hv hreplacement
            simpa only [Matrix.updateCol_eq_self] using hstable
  exact hGood Finset.univ A hcols (by simp)

end

end Permanent
end RealRooted
