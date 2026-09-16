import RealRooted.CombinatorialExamples.JacobiStirling.FirstKind
import RealRooted.CombinatorialExamples.JacobiStirling.SecondKind
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Jacobi--Stirling inverse relations

The signed first-kind and second-kind Jacobi--Stirling triangles are mutually
inverse. Both finite convolution orders are proved with their exact lower-
triangular support and zero-row endpoints.
-/

namespace RealRooted.JacobiStirling

noncomputable section

variable {R : Type*} [CommRing R]

/-- The standard signed first-kind Jacobi--Stirling kernel. -/
def signedFirstKind (z : R) (n k : ℕ) : R :=
  (-1 : R) ^ (n + k) * firstKind z n k

@[simp]
theorem signedFirstKind_zero_zero (z : R) : signedFirstKind z 0 0 = 1 := by
  simp [signedFirstKind]

@[simp]
theorem signedFirstKind_zero_succ (z : R) (k : ℕ) :
    signedFirstKind z 0 (k + 1) = 0 := by
  simp [signedFirstKind]

@[simp]
theorem signedFirstKind_succ_zero (z : R) (n : ℕ) :
    signedFirstKind z (n + 1) 0 = 0 := by
  simp [signedFirstKind]

@[simp]
theorem signedFirstKind_eq_zero_of_lt (z : R) {n k : ℕ} (h : n < k) :
    signedFirstKind z n k = 0 := by
  simp [signedFirstKind, firstKind_eq_zero_of_lt z h]

@[simp]
theorem signedFirstKind_diag (z : R) (n : ℕ) :
    signedFirstKind z n n = 1 := by
  rw [signedFirstKind, firstKind_diag]
  rw [show n + n = 2 * n by lia, pow_mul]
  simp

/-- Signed form of the first-kind successor recurrence. -/
theorem signedFirstKind_succ_succ (z : R) (n k : ℕ) :
    signedFirstKind z (n + 1) (k + 1) =
      signedFirstKind z n k -
        (n : R) * ((n : R) + z) * signedFirstKind z n (k + 1) := by
  have hpow : (-1 : R) ^ (n + 1 + (k + 1)) = (-1 : R) ^ (n + k) := by
    rw [show n + 1 + (k + 1) = n + k + 2 by lia, pow_add]
    simp
  have hpow' : (-1 : R) ^ (n + (k + 1)) = -(-1 : R) ^ (n + k) := by
    rw [show n + (k + 1) = n + k + 1 by lia, pow_succ]
    ring
  rw [signedFirstKind, signedFirstKind, signedFirstKind,
    firstKind_succ_succ, hpow, hpow']
  ring

/-- Second-kind followed by signed first-kind convolution. -/
theorem secondKind_mul_signedFirstKind_sum (z : R) (n j : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        secondKind z n k * signedFirstKind z k j =
      if n = j then 1 else 0 := by
  induction n generalizing j with
  | zero =>
      cases j with
      | zero => simp
      | succ j => simp
  | succ n ih =>
      cases j with
      | zero =>
          rw [if_neg (by lia)]
          apply Finset.sum_eq_zero
          intro k hk
          cases k with
          | zero => simp
          | succ k => simp
      | succ j =>
          let g : ℕ → R := fun k =>
            (k : R) * ((k : R) + z) * secondKind z n k *
              signedFirstKind z k (j + 1)
          have hg0 : g 0 = 0 := by simp [g]
          have hglast : g (n + 1) = 0 := by
            have hzero : secondKind z n (n + 1) = 0 :=
              secondKind_eq_zero_of_lt z (Nat.lt_succ_self n)
            unfold g
            rw [hzero]
            simp
          have hshift :
              ∑ k ∈ Finset.range (n + 1), g (k + 1) =
                ∑ k ∈ Finset.range (n + 1), g k := by
            calc
              (∑ k ∈ Finset.range (n + 1), g (k + 1)) =
                  (∑ k ∈ Finset.range (n + 1), g (k + 1)) + g 0 := by
                rw [hg0, add_zero]
              _ = ∑ k ∈ Finset.range (n + 2), g k :=
                (Finset.sum_range_succ' g (n + 1)).symm
              _ = (∑ k ∈ Finset.range (n + 1), g k) + g (n + 1) :=
                Finset.sum_range_succ g (n + 1)
              _ = ∑ k ∈ Finset.range (n + 1), g k := by
                rw [hglast, add_zero]
          rw [Finset.sum_range_succ']
          simp only [secondKind_succ_succ, secondKind_succ_zero, zero_mul,
            add_zero, Finset.sum_add_distrib, add_mul]
          have hrec :
              ∑ k ∈ Finset.range (n + 1),
                  secondKind z n k * signedFirstKind z (k + 1) (j + 1) =
                (∑ k ∈ Finset.range (n + 1),
                  secondKind z n k * signedFirstKind z k j) -
                  ∑ k ∈ Finset.range (n + 1), g k := by
            calc
              (∑ k ∈ Finset.range (n + 1),
                  secondKind z n k * signedFirstKind z (k + 1) (j + 1)) =
                  ∑ k ∈ Finset.range (n + 1),
                    (secondKind z n k * signedFirstKind z k j - g k) := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [signedFirstKind_succ_succ]
                simp [g, mul_sub, mul_assoc]
                ring
              _ = _ := Finset.sum_sub_distrib
                (fun k => secondKind z n k * signedFirstKind z k j) g
          rw [hrec]
          have hweighted :
              ∑ k ∈ Finset.range (n + 1),
                  secondKindWeight z k * secondKind z n (k + 1) *
                    signedFirstKind z (k + 1) (j + 1) =
                ∑ k ∈ Finset.range (n + 1), g (k + 1) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp [g, secondKindWeight, mul_assoc]
          rw [hweighted, hshift, sub_add_cancel]
          simpa using ih j

private def secondKindTruncation (z : R) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  fun i j => secondKind z i j

private def signedFirstKindTruncation (z : R) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  fun i j => signedFirstKind z i j

private theorem secondKindTruncation_mul_signedFirstKindTruncation
    (z : R) (N : ℕ) :
    secondKindTruncation z N * signedFirstKindTruncation z N = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  change (∑ k : Fin (N + 1),
      secondKind z i.val k.val * signedFirstKind z k.val j.val) =
    if i = j then 1 else 0
  have hsubset : Finset.range (i + 1) ⊆ Finset.range (N + 1) :=
    Finset.range_mono (by lia)
  have hsum :
      ∑ k ∈ Finset.range (i.val + 1),
          secondKind z i.val k * signedFirstKind z k j.val =
        ∑ k ∈ Finset.range (N + 1),
          secondKind z i.val k * signedFirstKind z k j.val :=
    Finset.sum_subset hsubset (fun k hkN hki => by
      have hik : i < k := by
        simp only [Finset.mem_range] at hki
        lia
      rw [secondKind_eq_zero_of_lt z hik]
      simp)
  calc
    (∑ k : Fin (N + 1),
        secondKind z i.val k.val * signedFirstKind z k.val j.val) =
        ∑ k ∈ Finset.range (N + 1),
          secondKind z i.val k * signedFirstKind z k j.val :=
      Fin.sum_univ_eq_sum_range
        (fun k => secondKind z i.val k * signedFirstKind z k j.val) (N + 1)
    _ = ∑ k ∈ Finset.range (i.val + 1),
        secondKind z i.val k * signedFirstKind z k j.val := hsum.symm
    _ = (if i.val = j.val then 1 else 0) :=
      secondKind_mul_signedFirstKind_sum z i.val j.val
    _ = if i = j then 1 else 0 := by simp [Fin.ext_iff]

private theorem signedFirstKindTruncation_mul_secondKindTruncation
    (z : R) (N : ℕ) :
    signedFirstKindTruncation z N * secondKindTruncation z N = 1 :=
  mul_eq_one_comm.mp
    (secondKindTruncation_mul_signedFirstKindTruncation z N)

/-- Signed first-kind followed by second-kind convolution. -/
theorem signedFirstKind_mul_secondKind_sum (z : R) (n j : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        signedFirstKind z n k * secondKind z k j =
      if n = j then 1 else 0 := by
  by_cases hj : j ≤ n
  · let i : Fin (n + 1) := Fin.last n
    let q : Fin (n + 1) := ⟨j, by lia⟩
    have hentry := congr_fun
      (congr_fun (signedFirstKindTruncation_mul_secondKindTruncation z n) i) q
    rw [Matrix.mul_apply] at hentry
    change (∑ k : Fin (n + 1),
        signedFirstKind z i.val k.val * secondKind z k.val q.val) =
      if i = q then 1 else 0 at hentry
    have hentry' :
        ∑ k ∈ Finset.range (n + 1),
            signedFirstKind z i.val k * secondKind z k q.val =
          if i = q then 1 else 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact hentry
    simpa [Fin.ext_iff, i, q] using hentry'
  · rw [if_neg (by lia)]
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k ≤ n := by simp only [Finset.mem_range] at hk; lia
    have hkj : k < j := lt_of_le_of_lt hkn (by lia)
    simp [secondKind_eq_zero_of_lt z hkj]

end

end RealRooted.JacobiStirling
