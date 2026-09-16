import RealRooted.CoefficientDominance.Symmetric.Finite

/-!
# Jacobi--Stirling numbers of the first kind

This file defines the first-kind Jacobi--Stirling triangle over a commutative
semiring and identifies it with the elementary symmetric functions evaluated
at `i * (i + z)` for `1 ≤ i < n`.
-/

namespace RealRooted.JacobiStirling

open RealRooted.CoefficientDominance.Symmetric

noncomputable section

variable {R : Type*} [CommSemiring R]

/-- The weight `i * (i + z)`, indexed from `i = 1`. -/
def firstKindWeight (z : R) (i : ℕ) : R :=
  (i + 1 : R) * ((i + 1 : R) + z)

/-- The first-kind Jacobi--Stirling triangle, in subtraction-free successor
form. -/
def firstKind (z : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      firstKind z n k + (n : R) * ((n : R) + z) * firstKind z n (k + 1)

@[simp]
theorem firstKind_zero_zero (z : R) : firstKind z 0 0 = 1 := rfl

@[simp]
theorem firstKind_zero_succ (z : R) (k : ℕ) : firstKind z 0 (k + 1) = 0 := rfl

@[simp]
theorem firstKind_succ_zero (z : R) (n : ℕ) : firstKind z (n + 1) 0 = 0 := rfl

/-- The defining Jacobi--Stirling recurrence. -/
theorem firstKind_succ_succ (z : R) (n k : ℕ) :
    firstKind z (n + 1) (k + 1) =
      firstKind z n k +
        (n : R) * ((n : R) + z) * firstKind z n (k + 1) := rfl

/-- Entries above the diagonal vanish. -/
@[simp]
theorem firstKind_eq_zero_of_lt (z : R) {n k : ℕ} (h : n < k) :
    firstKind z n k = 0 := by
  induction n generalizing k with
  | zero =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : k ≠ 0)
      exact firstKind_zero_succ z k
  | succ n ih =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : k ≠ 0)
      rw [firstKind_succ_succ]
      rw [ih (by lia), ih (by lia)]
      simp

@[simp]
theorem firstKind_diag (z : R) (n : ℕ) : firstKind z n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [firstKind_succ_succ, ih, firstKind_eq_zero_of_lt z (by lia)]
      simp

/-- The first-kind Jacobi--Stirling value is the corresponding elementary
symmetric evaluation on `1, ..., n - 1`. -/
theorem firstKind_eq_esym_of_le (z : R) {n k : ℕ} (hk : k ≤ n) :
    firstKind z n k = esym (firstKindWeight z) (n - 1) (n - k) := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := by lia
      subst k
      simp [esym_zero]
  | succ n ih =>
      cases k with
      | zero =>
          rw [firstKind_succ_zero]
          unfold esym Multiset.esymm
          simp only [Nat.sub_zero, Nat.add_sub_cancel]
          rw [Multiset.powersetCard_eq_empty (n + 1) (by simp)]
          simp
      | succ k =>
          have hkn : k ≤ n := by lia
          by_cases hdiag : k = n
          · subst k
            simp [esym_zero]
          · have hklt : k < n := by lia
            have hk1n : k + 1 ≤ n := by lia
            rw [firstKind_succ_succ, ih hkn, ih hk1n]
            have hnpos : 0 < n := by lia
            have hdegree : (n - (k + 1)) + 1 = n - k := by lia
            have hcast : ((n - 1 : ℕ) : R) + 1 = n := by
              calc
                ((n - 1 : ℕ) : R) + 1 = ((n - 1 + 1 : ℕ) : R) := by
                  rw [Nat.cast_add, Nat.cast_one]
                _ = n := by rw [Nat.sub_add_cancel hnpos]
            have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
            simpa [firstKindWeight, hcast, hnsub, hdegree] using
              (esym_succ (firstKindWeight z) (n - 1) (n - (k + 1))).symm

/-- The elementary-symmetric formula with its above-diagonal zero convention
made explicit. -/
theorem firstKind_eq_ite_esym (z : R) (n k : ℕ) :
    firstKind z n k =
      if k ≤ n then esym (firstKindWeight z) (n - 1) (n - k) else 0 := by
  split_ifs with hk
  · exact firstKind_eq_esym_of_le z hk
  · exact firstKind_eq_zero_of_lt z (Nat.lt_of_not_ge hk)

/-- Equivalent `MvPolynomial.esymm` evaluation form of
`firstKind_eq_esym_of_le`. -/
theorem firstKind_eq_aeval_esymm_of_le (z : R) {n k : ℕ} (hk : k ≤ n) :
    firstKind z n k =
      MvPolynomial.aeval (fun i : Fin (n - 1) => firstKindWeight z i)
        (MvPolynomial.esymm (Fin (n - 1)) R (n - k)) := by
  rw [firstKind_eq_esym_of_le z hk,
    MvPolynomial.aeval_esymm_eq_multiset_esymm]
  unfold esym
  congr 1
  let e : Fin (n - 1) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have hfin : (Finset.univ : Finset (Fin (n - 1))).map e =
      Finset.range (n - 1) := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_range, e]
    constructor
    · rintro ⟨a, rfl⟩
      exact a.isLt
    · intro hi
      exact ⟨⟨i, hi⟩, rfl⟩
  have hval := congrArg Finset.val hfin
  rw [Finset.map_val] at hval
  calc
    Multiset.map (firstKindWeight z) (Finset.range (n - 1)).val =
        Multiset.map (firstKindWeight z)
          ((Finset.univ : Finset (Fin (n - 1))).val.map e) := by
      rw [hval]
    _ = Multiset.map (fun i : Fin (n - 1) => firstKindWeight z i)
        Finset.univ.val := by
      rw [Multiset.map_map]
      rfl

end

end RealRooted.JacobiStirling
