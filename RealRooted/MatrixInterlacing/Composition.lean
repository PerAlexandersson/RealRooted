module

public import RealRooted.MatrixInterlacing.Converse

/-!
# Composition of interlacing-preserving polynomial matrices

This module packages composition for the zero-aware matrix criterion of
Brändén, *Unimodality, log-concavity, real-rootedness and beyond*,
Handbook of Enumerative Combinatorics (2015), Theorem 7.8.5.
-/

@[expose] public noncomputable section

open Polynomial

namespace RealRooted

namespace PreservesInterlacingSeq0

variable {n m : ℕ}
variable {G : List (List ℝ[X])} {H : List (List ℝ[X])}

/-- The composite action of two zero-aware interlacing preservers. -/
theorem comp_action (hG : PreservesInterlacingSeq0 n G)
    (hH : PreservesInterlacingSeq0 m H) (hG_len : G.length = m)
    {fs : List ℝ[X]} (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeq0NonnegRealRooted fs) :
    IsInterlacingSeq0NonnegRealRooted (matPolyAction H (matPolyAction G fs)) := by
  apply hH
  · simpa using hG_len
  · exact hG fs hfs_len hfs

end PreservesInterlacingSeq0

/-- The `n` by `n` identity matrix of polynomial entries. -/
def matPolyIdentity (n : ℕ) : List (List ℝ[X]) :=
  List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => if i = j then 1 else 0

/-- The identity matrix acts as the identity on length-`n` polynomial sequences. -/
theorem matPolyAction_identity (n : ℕ) (fs : List ℝ[X]) (hfs_len : fs.length = n) :
    matPolyAction (matPolyIdentity n) fs = fs := by
  induction fs generalizing n with
  | nil => simp_all [matPolyIdentity, matPolyAction]
  | cons f fs ih =>
    cases n with
    | zero => simp at hfs_len
    | succ n =>
      simp_all only [matPolyAction, matPolyIdentity, List.map_ofFn, forall_eq', List.length_cons,
        Nat.add_right_cancel_iff, List.ofFn_succ, ↓reduceIte, Fin.succ_ne_zero, Fin.succ_inj,
        List.map_cons, List.zipWith_cons_cons, one_mul, List.sum_cons, List.cons.injEq, add_eq_left,
        Function.comp_apply, Fin.cast_inj]
      have hzero : ∀ (xs : List ℝ[X]) (k : ℕ),
          ((List.replicate k (0 : ℝ[X])).zipWith (· * ·) xs).sum = 0 := by
        intro xs k
        induction xs generalizing k with
        | nil => simp
        | cons x xs ih =>
          cases k with
          | zero => simp
          | succ k => simp [List.replicate_succ, ih]
      constructor
      · have hfn :
            (fun i : Fin n => if (0 : Fin (n + 1)) = i.succ then (1 : ℝ[X]) else 0) =
              (fun _ => 0) := by
          funext i
          simp [eq_comm, Fin.succ_ne_zero]
        rw [hfn, List.ofFn_const]
        exact hzero fs n
      · change List.ofFn (fun i : Fin n =>
          ((0 :: List.ofFn (fun j : Fin n => if i = j then 1 else 0)).zipWith
            (· * ·) (f :: fs)).sum) = fs
        simpa [List.zipWith_cons_cons, matPolyAction, matPolyIdentity] using ih

private lemma zipWith_ofFn_ofFn {α β γ : Type} (op : α → β → γ) (n : ℕ)
    (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zipWith op (List.ofFn g) = List.ofFn (fun i => op (f i) (g i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ' f, List.ofFn_succ' g, List.ofFn_succ']
    simp only [List.concat_eq_append]
    rw [List.zipWith_append (by simp)]
    simp [ih]

private lemma sum_zipWith_ofFn_get (row : List ℝ[X]) (n : ℕ)
    (hrow : row.length = n) (f : Fin n → ℝ[X]) :
    (row.zipWith (· * ·) (List.ofFn f)).sum =
      ∑ j : Fin n, row.getD j 0 * f j := by
  have hrow_eq : List.ofFn (fun j : Fin n =>
      row[↑j]'(by simp [hrow])) = row := by
    simpa [hrow] using (List.ofFn_getElem (xs := row))
  rw [← hrow_eq]
  rw [zipWith_ofFn_ofFn]
  simp only [List.sum_ofFn]
  simp [List.getD_eq_getElem?_getD]

/-- The shape-aware product of polynomial list matrices, with exactly `n` columns. -/
def matPolyMul (n : ℕ) (H G : List (List ℝ[X])) : List (List ℝ[X]) :=
  H.map fun row => List.ofFn fun j : Fin n =>
    ∑ r : Fin G.length, row.getD r 0 * (G.get r).getD j 0

/-- Every row of a shape-aware matrix product has its prescribed length. -/
theorem matPolyMul_row_length (n : ℕ) (H G : List (List ℝ[X]))
    (row : List ℝ[X]) (hrow : row ∈ matPolyMul n H G) : row.length = n := by
  rcases List.mem_map.mp hrow with ⟨r, hr, rfl⟩
  simp

/-- Matrix action agrees with the explicit product of two polynomial matrices. -/
theorem matPolyAction_matPolyMul (n : ℕ) (H G : List (List ℝ[X])) (fs : List ℝ[X])
    (hH_rect : ∀ row ∈ H, row.length = G.length)
    (hG_rect : ∀ row ∈ G, row.length = n) (hfs_len : fs.length = n) :
    matPolyAction (matPolyMul n H G) fs =
      matPolyAction H (matPolyAction G fs) := by
  classical
  subst n
  simp only [matPolyAction, matPolyMul, List.map_map]
  apply List.map_congr_left
  intro a ha
  have ha_eq : List.ofFn (fun i : Fin G.length =>
      a[↑i]'(by simp [hH_rect a ha])) = a := by
    simpa [hH_rect a ha] using (List.ofFn_getElem (xs := a))
  have hfs_eq : List.ofFn fs.get = fs := List.ofFn_get fs
  have hmap_eq : List.ofFn (fun i : Fin G.length =>
      (G.map (fun row : List ℝ[X] => (row.zipWith (· * ·) fs).sum)).get
        ⟨i, by simp⟩) =
      G.map (fun row : List ℝ[X] => (row.zipWith (· * ·) fs).sum) := by
    convert List.ofFn_getElem
      (xs := G.map (fun row : List ℝ[X] => (row.zipWith (· * ·) fs).sum)) using 1
    simp
  rw [← ha_eq, ← hmap_eq, ← hfs_eq]
  have houter (q : Fin fs.length → ℝ[X]) :
      ((List.ofFn q).zipWith (· * ·) (List.ofFn fs.get)).sum =
        ∑ j : Fin fs.length, q j * fs.get j := by
    rw [zipWith_ofFn_ofFn]
    rw [List.sum_ofFn]
  let q : Fin fs.length → ℝ[X] := fun j => ∑ x : Fin G.length,
    (List.ofFn (fun i : Fin G.length =>
      a[↑i]'(by simp [hH_rect a ha]))).getD x 0 * (G.get x).getD j 0
  have hmap_get (r : Fin G.length) :
      (G.map (fun row : List ℝ[X] =>
        (row.zipWith (· * ·) (List.ofFn fs.get)).sum)).get ⟨r, by simp⟩ =
          ((G.get r).zipWith (· * ·) (List.ofFn fs.get)).sum := by
    simp
  have hrow_action (r : Fin G.length) :
      ((G.get r).zipWith (· * ·) (List.ofFn fs.get)).sum =
        ∑ j : Fin fs.length, (G.get r).getD j 0 * fs.get j := by
    simpa using sum_zipWith_ofFn_get (G.get r) fs.length
      (hG_rect (G.get r) (List.get_mem _ _)) fs.get
  calc
    _ = ∑ j : Fin fs.length, q j * fs.get j := by
      simpa [q, Function.comp_apply] using houter q
    _ = _ := by
      simp only [q]
      simp_rw [hmap_get, hrow_action]
      conv_rhs =>
        rw [zipWith_ofFn_ofFn]
        rw [List.sum_ofFn]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp [mul_assoc]

/-- A composite of preserving matrices preserves the zero-aware interlacing cone. -/
theorem matPolyMul_preservesInterlacingSeq0 (n : ℕ) (H G : List (List ℝ[X]))
    (hH_rect : ∀ row ∈ H, row.length = G.length)
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG : PreservesInterlacingSeq0 n G)
    (hH : PreservesInterlacingSeq0 G.length H) :
    PreservesInterlacingSeq0 n (matPolyMul n H G) := by
  intro fs hfs_len hfs
  rw [matPolyAction_matPolyMul n H G fs hH_rect hG_rect hfs_len]
  exact hG.comp_action hH rfl hfs_len hfs

/-- The product of two rectangular preservers has nonnegative entries. -/
theorem matPolyMul_hasNonnegCoeffs (n : ℕ) (H G : List (List ℝ[X]))
    (hH_rect : ∀ row ∈ H, row.length = G.length)
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG : PreservesInterlacingSeq0 n G)
    (hH : PreservesInterlacingSeq0 G.length H) :
    ∀ row ∈ matPolyMul n H G, ∀ p ∈ row, HasNonnegCoeffs p := by
  exact (preservesInterlacingSeq0_iff (matPolyMul n H G)
    (fun row hrow => matPolyMul_row_length n H G row hrow)).mp
    (matPolyMul_preservesInterlacingSeq0 n H G hH_rect hG_rect hG hH) |>.1

/-- The product of two rectangular preservers satisfies every ordered pencil test. -/
theorem matPolyMul_has2x2InterlacingProperty0 (n : ℕ) (H G : List (List ℝ[X]))
    (hH_rect : ∀ row ∈ H, row.length = G.length)
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG : PreservesInterlacingSeq0 n G)
    (hH : PreservesInterlacingSeq0 G.length H) :
    ∀ (i₁ i₂ : Fin (matPolyMul n H G).length) (j₁ j₂ : Fin n),
        i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (((matPolyMul n H G).get i₁).get ⟨j₁, by
          have hrow := matPolyMul_row_length n H G
            ((matPolyMul n H G).get i₁) (List.get_mem _ _)
          rw [hrow]
          exact j₁.isLt⟩)
        (((matPolyMul n H G).get i₁).get ⟨j₂, by
          have hrow := matPolyMul_row_length n H G
            ((matPolyMul n H G).get i₁) (List.get_mem _ _)
          rw [hrow]
          exact j₂.isLt⟩)
        (((matPolyMul n H G).get i₂).get ⟨j₁, by
          have hrow := matPolyMul_row_length n H G
            ((matPolyMul n H G).get i₂) (List.get_mem _ _)
          rw [hrow]
          exact j₁.isLt⟩)
        (((matPolyMul n H G).get i₂).get ⟨j₂, by
          have hrow := matPolyMul_row_length n H G
            ((matPolyMul n H G).get i₂) (List.get_mem _ _)
          rw [hrow]
          exact j₂.isLt⟩) := by
  exact (preservesInterlacingSeq0_iff (matPolyMul n H G)
    (fun row hrow => matPolyMul_row_length n H G row hrow)).mp
    (matPolyMul_preservesInterlacingSeq0 n H G hH_rect hG_rect hG hH) |>.2

example :
    matPolyMul 2
      ([[1, 1], [0, 1]] : List (List ℝ[X]))
      ([[1, 0], [X, 1]] : List (List ℝ[X])) =
      ([[1 + X, 1], [X, 1]] : List (List ℝ[X])) := by
  simp [matPolyMul, Fin.sum_univ_succ, List.getD_eq_getElem?_getD]

end RealRooted
