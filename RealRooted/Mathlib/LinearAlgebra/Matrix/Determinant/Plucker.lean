import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Ordered deleted-column Plücker identity

This leaf proves the canonical ordered deleted-column identity used by the
finite Cryer route.  Its `Field` and nonzero middle-pivot hypotheses are
explicit sufficient assumptions for the vector-span witnesses; it does not
yet prove the full Cryer criterion.
-/

namespace Matrix

private theorem plucker_ordered_rectangle_vecMul
    {R : Type*} [Field R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R)
    (hpivot : (M.submatrix Fin.castSucc
      (fun j : Fin (q + 1) => j.castSucc.succ)).det ≠ 0) :
    let middle : Fin (q + 1) → Fin (q + 3) :=
      fun j => j.castSucc.succ
    let P := (M.submatrix Fin.castSucc middle).transpose
    let x : Fin (q + 1) → R := fun j => M j.castSucc 0
    let y : Fin (q + 1) → R := fun j => M j.castSucc (Fin.last (q + 2))
    ∃ c d : Fin (q + 1) → R, c ᵥ* P = x ∧ d ᵥ* P = y := by
  dsimp
  let P : Matrix (Fin (q + 1)) (Fin (q + 1)) R :=
    (M.submatrix Fin.castSucc (fun j : Fin (q + 1) => j.castSucc.succ)).transpose
  have hdet : P.det ≠ 0 := by
    have htranspose :
        ((M.submatrix Fin.castSucc
          (fun j : Fin (q + 1) => j.castSucc.succ)).transpose).det ≠ 0 := by
      rwa [Matrix.det_transpose]
    exact htranspose
  have hsurj : Function.Surjective P.vecMul := by
    apply Matrix.vecMul_surjective_iff_isUnit.2
    exact (Matrix.isUnit_iff_isUnit_det P).2 (isUnit_iff_ne_zero.2 hdet)
  obtain ⟨c, hc⟩ := hsurj (fun j => M j.castSucc 0)
  obtain ⟨d, hd⟩ := hsurj (fun j => M j.castSucc (Fin.last (q + 2)))
  exact ⟨c, d, hc, hd⟩

private theorem plucker_border_last_eq_delete_zero
    {R : Type*} [CommRing R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) :
    let middle : Fin (q + 1) → Fin (q + 3) :=
      fun j => j.castSucc.succ
    let P := (M.submatrix Fin.castSucc middle).transpose
    let b : Fin (q + 1) → R := fun j => M (Fin.last (q + 1)) (middle j)
    let y : Fin (q + 1) → R := fun j => M j.castSucc (Fin.last (q + 2))
    let beta := M (Fin.last (q + 1)) (Fin.last (q + 2))
    (border P b y beta).transpose = M.submatrix id Fin.succ := by
  dsimp
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [border]
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [border]

private theorem plucker_border_zero_eq_delete_last_permuted
    {R : Type*} [CommRing R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) :
    let middle : Fin (q + 1) → Fin (q + 3) :=
      fun j => j.castSucc.succ
    let P := (M.submatrix Fin.castSucc middle).transpose
    let b : Fin (q + 1) → R := fun j => M (Fin.last (q + 1)) (middle j)
    let x : Fin (q + 1) → R := fun j => M j.castSucc 0
    let alpha := M (Fin.last (q + 1)) 0
    let e : Equiv.Perm (Fin (q + 2)) := Fin.cycleIcc 0 (Fin.last (q + 1))
    (border P b x alpha).transpose =
      (M.submatrix id Fin.castSucc).submatrix id e := by
  dsimp
  have hlast :
      (Fin.cycleIcc (0 : Fin (q + 2)) (Fin.last (q + 1)))
          (Fin.last (q + 1)) = 0 :=
    Fin.cycleIcc_of_last (Fin.zero_le _)
  have hcast (j : Fin (q + 1)) :
      (Fin.cycleIcc (0 : Fin (q + 2)) (Fin.last (q + 1))) j.castSucc = j.succ :=
    Fin.ext <| by
      simpa using congrArg Fin.val
        (Fin.cycleIcc_of_ge_of_lt (Fin.zero_le _) (Fin.castSucc_lt_last j))
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [transpose_apply, border_last_last, submatrix_apply]
      rw [hlast]
      simp
    · simp only [transpose_apply, border_castSucc_last, submatrix_apply]
      rw [hcast]
      simp
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [transpose_apply, border_last_castSucc, submatrix_apply]
      rw [hlast]
      simp
    · simp only [transpose_apply, border_castSucc_castSucc, submatrix_apply]
      rw [hcast]
      simp

private theorem plucker_det_border_zero_eq_delete_last
    {R : Type*} [CommRing R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) :
    let middle : Fin (q + 1) → Fin (q + 3) :=
      fun j => j.castSucc.succ
    let P := (M.submatrix Fin.castSucc middle).transpose
    let b : Fin (q + 1) → R := fun j => M (Fin.last (q + 1)) (middle j)
    let x : Fin (q + 1) → R := fun j => M j.castSucc 0
    let alpha := M (Fin.last (q + 1)) 0
    (border P b x alpha).det =
      (-1 : R) ^ (q + 1) * (M.submatrix id Fin.castSucc).det := by
  dsimp
  let e : Equiv.Perm (Fin (q + 2)) := Fin.cycleIcc 0 (Fin.last (q + 1))
  have hmatrix : (border
      (M.submatrix Fin.castSucc (fun j : Fin (q + 1) => j.castSucc.succ)).transpose
      (fun j => M (Fin.last (q + 1)) j.castSucc.succ)
      (fun j => M j.castSucc 0) (M (Fin.last (q + 1)) 0)).transpose =
      (M.submatrix id Fin.castSucc).submatrix id e := by
    simpa [e] using plucker_border_zero_eq_delete_last_permuted M
  rw [← Matrix.det_transpose, hmatrix, Matrix.det_permute']
  have hsign : Equiv.Perm.sign e = (-1 : R) ^ (q + 1) := by
    rw [show e = Fin.cycleIcc 0 (Fin.last (q + 1)) by rfl,
      Fin.sign_cycleIcc_of_le (Fin.zero_le _)]
    simp
  rw [hsign]

private theorem plucker_det_border_last_eq_delete_zero
    {R : Type*} [CommRing R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) :
    let middle : Fin (q + 1) → Fin (q + 3) :=
      fun j => j.castSucc.succ
    let P := (M.submatrix Fin.castSucc middle).transpose
    let b : Fin (q + 1) → R := fun j => M (Fin.last (q + 1)) (middle j)
    let y : Fin (q + 1) → R := fun j => M j.castSucc (Fin.last (q + 2))
    let beta := M (Fin.last (q + 1)) (Fin.last (q + 2))
    (border P b y beta).det = (M.submatrix id Fin.succ).det := by
  dsimp
  rw [← Matrix.det_transpose]
  simpa using congrArg Matrix.det (plucker_border_last_eq_delete_zero M)

private theorem plucker_update_zero_selector
    {R : Type*} [CommRing R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) (b : Fin (q + 1)) :
    let middle : Fin (q + 1) → Fin (q + 3) :=
      fun j => j.castSucc.succ
    let P := (M.submatrix Fin.castSucc middle).transpose
    let x : Fin (q + 1) → R := fun j => M j.castSucc 0
    let sorted : Fin (q + 1) → Fin (q + 3) :=
      fun j => (b.succ.succAbove j).castSucc
    (P.updateRow b x).transpose =
      (M.submatrix Fin.castSucc sorted).submatrix id b.cycleRange := by
  dsimp
  ext i j
  simp only [transpose_apply, Matrix.updateRow_apply, submatrix_apply]
  by_cases hj : j = b
  · subst j
    simp [Fin.cycleRange_self]
  · rcases lt_or_gt_of_ne hj with hj | hj
    · simp only [if_neg (Fin.ne_of_lt hj)]
      rw [Fin.cycleRange_of_lt hj]
      congr 2
      apply Fin.ext
      have hlt : (j + 1).castSucc < b.succ := by
        apply Fin.lt_def.mpr
        rw [Fin.val_castSucc, Fin.val_add_one_of_lt (lt_of_lt_of_le hj b.le_last),
          Fin.val_succ]
        exact Nat.succ_lt_succ hj
      rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
      simp only [Fin.val_succ, Fin.val_castSucc]
      rw [Fin.val_add_one_of_lt (lt_of_lt_of_le hj b.le_last)]
    · simp only [if_neg (Fin.ne_of_lt hj).symm]
      rw [Fin.cycleRange_of_gt hj]
      congr 2
      apply Fin.ext
      have hle : b.succ ≤ j.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [Fin.val_succ, Fin.val_castSucc]
        exact Nat.succ_le_iff.mpr hj
      rw [Fin.succAbove_of_le_castSucc _ _ hle]
      rfl

private theorem plucker_update_last_selector
    {R : Type*} [CommRing R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) (b : Fin (q + 1)) :
    let middle : Fin (q + 1) → Fin (q + 3) :=
      fun j => j.castSucc.succ
    let P := (M.submatrix Fin.castSucc middle).transpose
    let y : Fin (q + 1) → R := fun j => M j.castSucc (Fin.last (q + 2))
    let sorted : Fin (q + 1) → Fin (q + 3) :=
      fun j => (b.castSucc.succAbove j).succ
    (P.updateRow b y).transpose =
      (M.submatrix Fin.castSucc sorted).submatrix id
        (Fin.cycleIcc b (Fin.last q)).symm := by
  dsimp
  let e : Equiv.Perm (Fin (q + 1)) := Fin.cycleIcc b (Fin.last q)
  have hbase : e.symm b = Fin.last q := by
    apply e.injective
    rw [e.apply_symm_apply, Fin.cycleIcc_of_last b.le_last]
  have hsucc (t : Fin q) : e.symm (b.succAbove t) = t.castSucc := by
    apply e.injective
    rw [e.apply_symm_apply]
    simpa [e] using (congrFun
      (Fin.cycleIcc_comp_succAbove b (Fin.last q) b.le_last) t).symm
  have hbase' : (Fin.cycleIcc b (Fin.last q)).symm b = Fin.last q := by
    simpa [e] using hbase
  have hsucc' (t : Fin q) :
      (Fin.cycleIcc b (Fin.last q)).symm (b.succAbove t) = t.castSucc := by
    simpa [e] using hsucc t
  ext i j
  refine Fin.succAboveCases b ?_ (fun t => ?_) j
  · simp only [transpose_apply, Matrix.updateRow_apply, submatrix_apply]
    rw [hbase']
    simp only [if_pos]
    congr 2
    apply Fin.ext
    simp
  · simp only [transpose_apply, Matrix.updateRow_apply, submatrix_apply]
    rw [hsucc']
    simp only [if_neg (Fin.succAbove_ne _ _)]
    congr 2
    apply Fin.ext
    simp

private theorem plucker_det_update_zero
    {R : Type*} [CommRing R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) (b : Fin (q + 1)) :
    let middle : Fin (q + 1) → Fin (q + 3) :=
      fun j => j.castSucc.succ
    let P := (M.submatrix Fin.castSucc middle).transpose
    let x : Fin (q + 1) → R := fun j => M j.castSucc 0
    let sorted : Fin (q + 1) → Fin (q + 3) :=
      fun j => (b.succ.succAbove j).castSucc
    (P.updateRow b x).det =
      (-1 : R) ^ (b : Nat) * (M.submatrix Fin.castSucc sorted).det := by
  dsimp
  rw [← Matrix.det_transpose]
  have h := congrArg Matrix.det (plucker_update_zero_selector M b)
  rw [Matrix.det_permute', Fin.sign_cycleRange] at h
  simpa using h

private theorem plucker_det_update_last
    {R : Type*} [CommRing R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) (b : Fin (q + 1)) :
    let middle : Fin (q + 1) → Fin (q + 3) :=
      fun j => j.castSucc.succ
    let P := (M.submatrix Fin.castSucc middle).transpose
    let y : Fin (q + 1) → R := fun j => M j.castSucc (Fin.last (q + 2))
    let sorted : Fin (q + 1) → Fin (q + 3) :=
      fun j => (b.castSucc.succAbove j).succ
    (P.updateRow b y).det =
      (-1 : R) ^ (q - (b : Nat)) * (M.submatrix Fin.castSucc sorted).det := by
  dsimp
  rw [← Matrix.det_transpose]
  have h := congrArg Matrix.det (plucker_update_last_selector M b)
  rw [Matrix.det_permute', Equiv.Perm.sign_symm,
    Fin.sign_cycleIcc_of_le b.le_last] at h
  simpa using h

private theorem plucker_left_big_selector
    {R : Type*} [CommRing R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) (b : Fin (q + 1)) :
    let middle : Fin (q + 1) → Fin (q + 3) := fun j => j.castSucc.succ
    let P := (M.submatrix Fin.castSucc middle).transpose
    let br : Fin (q + 1) → R := fun j => M (Fin.last (q + 1)) (middle j)
    let x : Fin (q + 1) → R := fun j => M j.castSucc 0
    let y : Fin (q + 1) → R := fun j => M j.castSucc (Fin.last (q + 2))
    let alpha := M (Fin.last (q + 1)) 0
    let beta := M (Fin.last (q + 1)) (Fin.last (q + 2))
    let sorted : Fin (q + 2) → Fin (q + 3) := b.castSucc.succ.succAbove
    ((border P br y beta).updateRow b.castSucc (Fin.snoc x alpha)).transpose =
      (M.submatrix id sorted).submatrix id b.castSucc.cycleRange := by
  dsimp
  rw [← Matrix.updateCol_transpose]
  have hborder := plucker_border_last_eq_delete_zero M
  dsimp at hborder
  rw [hborder]
  have hcol : Fin.snoc (fun j : Fin (q + 1) => M j.castSucc 0)
      (M (Fin.last (q + 1)) 0) = fun i => M i 0 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [hcol]
  ext i j
  refine Fin.succAboveCases b.castSucc ?_ (fun t => ?_) j
  · simp [Fin.cycleRange_self]
  · simp [Fin.cycleRange_succAbove,
      Fin.succ_succAbove_succ]

private theorem plucker_det_left_big
    {R : Type*} [CommRing R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) (b : Fin (q + 1)) :
    let middle : Fin (q + 1) → Fin (q + 3) := fun j => j.castSucc.succ
    let P := (M.submatrix Fin.castSucc middle).transpose
    let br : Fin (q + 1) → R := fun j => M (Fin.last (q + 1)) (middle j)
    let x : Fin (q + 1) → R := fun j => M j.castSucc 0
    let y : Fin (q + 1) → R := fun j => M j.castSucc (Fin.last (q + 2))
    let alpha := M (Fin.last (q + 1)) 0
    let beta := M (Fin.last (q + 1)) (Fin.last (q + 2))
    let sorted : Fin (q + 2) → Fin (q + 3) := b.castSucc.succ.succAbove
    ((border P br y beta).updateRow b.castSucc (Fin.snoc x alpha)).det =
      (-1 : R) ^ (b : Nat) * (M.submatrix id sorted).det := by
  dsimp
  rw [← Matrix.det_transpose]
  have h := congrArg Matrix.det (plucker_left_big_selector M b)
  rw [Matrix.det_permute', Fin.sign_cycleRange] at h
  simpa using h

private theorem plucker_det_border_plucker_plus
    {R : Type*} [CommRing R] {q : ℕ} (P : Matrix (Fin q) (Fin q) R)
    (r : Fin q) (b x y c d : Fin q → R) (alpha beta : R)
    (hx : c ᵥ* P = x) (hy : d ᵥ* P = y)
    (deltaB deltaA deltaC deltaAC deltaBC deltaAB : R)
    (hP : P.det = deltaB)
    (hleft : ((border P b y beta).updateRow r.castSucc
      (Fin.snoc x alpha)).det = (-1 : R) ^ (r : ℕ) * deltaAC)
    (hupdateX : (P.updateRow r x).det = (-1 : R) ^ (r : ℕ) * deltaA)
    (hupdateY : (P.updateRow r y).det =
      (-1 : R) ^ (q - 1 - (r : ℕ)) * deltaC)
    (hborderY : (border P b y beta).det = deltaBC)
    (hborderX : (border P b x alpha).det = (-1 : R) ^ q * deltaAB) :
    deltaB * deltaAC = deltaA * deltaBC + deltaC * deltaAB := by
  let s : R := (-1 : R) ^ (r : ℕ)
  have hr : (r : ℕ) < q := r.isLt
  have hsum : (q - 1 - (r : ℕ)) + q =
      (r : ℕ) + 1 + 2 * (q - (r : ℕ) - 1) := by
    lia
  have hprod : (-1 : R) ^ (q - 1 - (r : ℕ)) * (-1 : R) ^ q = -s := by
    rw [← pow_add, hsum, pow_add, pow_mul]
    simp [s, pow_succ]
  have hsq : s * s = 1 := by
    dsimp [s]
    rw [← pow_add]
    simp
  have h := det_border_plucker P r b x y c d alpha beta hx hy
  rw [hP, hleft, hupdateX, hupdateY, hborderY, hborderX] at h
  have hh : s * (deltaB * deltaAC) =
      s * (deltaA * deltaBC + deltaC * deltaAB) := by
    calc
      s * (deltaB * deltaAC) = deltaB * (s * deltaAC) := by ring
      _ = (s * deltaA) * deltaBC -
          (((-1 : R) ^ (q - 1 - (r : ℕ)) * deltaC) *
            ((-1 : R) ^ q * deltaAB)) := h
      _ = s * (deltaA * deltaBC + deltaC * deltaAB) := by
        calc
          (s * deltaA) * deltaBC -
              ((-1 : R) ^ (q - 1 - (r : ℕ)) * deltaC) *
                ((-1 : R) ^ q * deltaAB) =
              s * (deltaA * deltaBC) -
                (((-1 : R) ^ (q - 1 - (r : ℕ)) * (-1 : R) ^ q) *
                  (deltaC * deltaAB)) := by ring
          _ = s * (deltaA * deltaBC + deltaC * deltaAB) := by
            rw [hprod]
            ring
  calc
    deltaB * deltaAC = (s * s) * (deltaB * deltaAC) := by rw [hsq]; ring
    _ = s * (s * (deltaB * deltaAC)) := by ring
    _ = s * (s * (deltaA * deltaBC + deltaC * deltaAB)) := by rw [hh]
    _ = (s * s) * (deltaA * deltaBC + deltaC * deltaAB) := by ring
    _ = deltaA * deltaBC + deltaC * deltaAB := by rw [hsq]; ring

/-- The canonical deleted-column Plücker relation for a rectangular matrix.

The nonzero middle minor supplies the two vector-span witnesses used by the
bordered determinant identity. -/
theorem det_ordered_delete_column_plucker
    {R : Type*} [Field R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) (b : Fin (q + 1))
    (hpivot : (M.submatrix Fin.castSucc
      (fun j : Fin (q + 1) => j.castSucc.succ)).det ≠ 0) :
    let d : Fin (q + 3) → R := fun j => (M.submatrix id j.succAbove).det
    let deltaAC := (M.submatrix Fin.castSucc
      (fun j : Fin (q + 1) => j.castSucc.succ)).det
    let deltaAB := (M.submatrix Fin.castSucc
      (fun j : Fin (q + 1) => (b.castSucc.succAbove j).succ)).det
    let deltaBC := (M.submatrix Fin.castSucc
      (fun j : Fin (q + 1) => (b.succ.succAbove j).castSucc)).det
    d b.castSucc.succ * deltaAC =
      d (Fin.last (q + 2)) * deltaAB + d 0 * deltaBC := by
  dsimp
  let middle : Fin (q + 1) → Fin (q + 3) := fun j => j.castSucc.succ
  let P : Matrix (Fin (q + 1)) (Fin (q + 1)) R :=
    (M.submatrix Fin.castSucc middle).transpose
  let br : Fin (q + 1) → R := fun j => M (Fin.last (q + 1)) (middle j)
  let x : Fin (q + 1) → R := fun j => M j.castSucc 0
  let y : Fin (q + 1) → R := fun j => M j.castSucc (Fin.last (q + 2))
  let alpha : R := M (Fin.last (q + 1)) 0
  let beta : R := M (Fin.last (q + 1)) (Fin.last (q + 2))
  obtain ⟨c, e, hx, hy⟩ := plucker_ordered_rectangle_vecMul M hpivot
  have h := plucker_det_border_plucker_plus P b br x y c e alpha beta hx hy
    ((M.submatrix Fin.castSucc middle).det)
    ((M.submatrix Fin.castSucc (fun j => (b.succ.succAbove j).castSucc)).det)
    ((M.submatrix Fin.castSucc (fun j => (b.castSucc.succAbove j).succ)).det)
    ((M.submatrix id b.castSucc.succ.succAbove).det)
    ((M.submatrix id Fin.succ).det)
    ((M.submatrix id Fin.castSucc).det)
    (by
      change ((M.submatrix Fin.castSucc middle).transpose).det =
        (M.submatrix Fin.castSucc middle).det
      exact Matrix.det_transpose _)
    (by simpa [middle, P, br, x, y, alpha, beta] using plucker_det_left_big M b)
    (by simpa [middle, P, x] using plucker_det_update_zero M b)
    (by simpa [middle, P, y] using plucker_det_update_last M b)
    (by simpa [middle, P, br, y, beta] using plucker_det_border_last_eq_delete_zero M)
    (by simpa [middle, P, br, x, alpha] using plucker_det_border_zero_eq_delete_last M)
  simpa [middle, P, br, x, y, alpha, beta, mul_comm, mul_left_comm, mul_assoc,
    add_comm]
    using h

end Matrix
