import RealRooted.Mathlib.RingTheory.MvPolynomial.Symmetric.CompleteHomogeneous

/-!
# Jacobi--Stirling numbers of the second kind

This file defines the second-kind Jacobi--Stirling triangle over a commutative
semiring and identifies it with complete homogeneous symmetric polynomials
evaluated at `i * (i + z)` for `1 ≤ i ≤ k`.
-/

namespace RealRooted.JacobiStirling

noncomputable section

variable {R : Type*} [CommSemiring R]

/-- The second-kind weight `i * (i + z)`, indexed from `i = 1`. -/
def secondKindWeight (z : R) (i : ℕ) : R :=
  (i + 1 : R) * ((i + 1 : R) + z)

/-- The second-kind Jacobi--Stirling triangle, in subtraction-free successor
form. -/
def secondKind (z : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      secondKind z n k + secondKindWeight z k * secondKind z n (k + 1)

@[simp]
theorem secondKind_zero_zero (z : R) : secondKind z 0 0 = 1 := rfl

@[simp]
theorem secondKind_zero_succ (z : R) (k : ℕ) : secondKind z 0 (k + 1) = 0 := rfl

@[simp]
theorem secondKind_succ_zero (z : R) (n : ℕ) : secondKind z (n + 1) 0 = 0 := rfl

/-- The defining second-kind Jacobi--Stirling recurrence. -/
theorem secondKind_succ_succ (z : R) (n k : ℕ) :
    secondKind z (n + 1) (k + 1) =
      secondKind z n k + secondKindWeight z k * secondKind z n (k + 1) := rfl

/-- Entries above the diagonal vanish. -/
@[simp]
theorem secondKind_eq_zero_of_lt (z : R) {n k : ℕ} (h : n < k) :
    secondKind z n k = 0 := by
  induction n generalizing k with
  | zero =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : k ≠ 0)
      exact secondKind_zero_succ z k
  | succ n ih =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : k ≠ 0)
      rw [secondKind_succ_succ]
      rw [ih (by lia), ih (by lia)]
      simp

@[simp]
theorem secondKind_diag (z : R) (n : ℕ) : secondKind z n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [secondKind_succ_succ, ih, secondKind_eq_zero_of_lt z (by lia)]
      simp

/-- The second-kind value is the corresponding complete homogeneous
evaluation on `1, ..., k`. -/
theorem secondKind_eq_aeval_hsymm_of_le (z : R) {n k : ℕ} (hk : k ≤ n) :
    secondKind z n k =
      MvPolynomial.aeval (fun i : Fin k => secondKindWeight z i)
        (MvPolynomial.hsymm (Fin k) R (n - k)) := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := by lia
      subst k
      simp
  | succ n ih =>
      cases k with
      | zero =>
          rw [secondKind_succ_zero]
          symm
          rw [Nat.sub_zero]
          exact
            (MvPolynomial.aeval_hsymm_fin_zero_succ (R := R) n
              (fun i : Fin 0 => secondKindWeight z i))
      | succ k =>
          have hkn : k ≤ n := by lia
          by_cases hdiag : k = n
          · subst k
            simp
          · have hklt : k < n := by lia
            have hk1n : k + 1 ≤ n := by lia
            rw [secondKind_succ_succ, ih hkn, ih hk1n]
            have hdegree : (n - (k + 1)) + 1 = n - k := by lia
            simpa [hdegree] using
              (MvPolynomial.aeval_hsymm_fin_succ (R := R) k
                (n - (k + 1))
                (fun i : Fin (k + 1) => secondKindWeight z i)).symm

/-- The complete-homogeneous formula with the above-diagonal zero convention
made explicit. -/
theorem secondKind_eq_ite_aeval_hsymm (z : R) (n k : ℕ) :
    secondKind z n k =
      if k ≤ n then
        MvPolynomial.aeval (fun i : Fin k => secondKindWeight z i)
          (MvPolynomial.hsymm (Fin k) R (n - k))
      else 0 := by
  split_ifs with hk
  · exact secondKind_eq_aeval_hsymm_of_le z hk
  · exact secondKind_eq_zero_of_lt z (Nat.lt_of_not_ge hk)

end

end RealRooted.JacobiStirling
