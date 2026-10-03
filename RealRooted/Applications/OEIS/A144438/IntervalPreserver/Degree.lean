import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Basic
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Degree bookkeeping for the A144438 basis transform

The A144438 basis is degree triangular and monic.  We first record the two
generic basis-transform facts needed here, then specialize them to the
diagonal family.
-/

open Polynomial Finset

noncomputable section

namespace Polynomial

/-- A supportwise degree bound on the basis elements bounds the entire basis
transform. -/
theorem basisTransform_natDegree_le_of_support
    {R : Type*} [CommRing R] {B : ℕ → R[X]} {p : R[X]} {N : ℕ}
    (hB : ∀ n ∈ p.support, (B n).natDegree ≤ N) :
    (basisTransform B p).natDegree ≤ N := by
  rw [basisTransform, Polynomial.sum_def]
  exact natDegree_sum_le_of_forall_le _ _ fun n hn ↦
    (natDegree_C_mul_le (p.coeff n) (B n)).trans (hB n hn)

/-- A basis transform does not raise degree when its `n`th basis element has
degree at most `n`. -/
theorem basisTransform_natDegree_le_of_natDegree_le
    {R : Type*} [CommRing R] {B : ℕ → R[X]}
    (hB : ∀ n, (B n).natDegree ≤ n) (p : R[X]) :
    (basisTransform B p).natDegree ≤ p.natDegree := by
  rw [basisTransform, Polynomial.sum_def]
  apply natDegree_sum_le_of_forall_le
  intro n hn
  calc
    (C (p.coeff n) * B n).natDegree ≤ (B n).natDegree :=
      natDegree_C_mul_le _ _
    _ ≤ n := hB n
    _ ≤ p.natDegree :=
      le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)

/-- The top input coefficient stays equal to one under a degree-exact monic
triangular basis transform. -/
theorem coeff_basisTransform_natDegree_eq_one_of_monic
    {R : Type*} [CommRing R] [Nontrivial R] {B : ℕ → R[X]}
    (hBdeg : ∀ n, (B n).natDegree = n)
    (hBmonic : ∀ n, (B n).Monic) {p : R[X]} (hp : p.Monic) :
    (basisTransform B p).coeff p.natDegree = 1 := by
  rw [coeff_basisTransform, Polynomial.sum_def]
  have hnmem : p.natDegree ∈ p.support :=
    natDegree_mem_support_of_nonzero hp.ne_zero
  rw [Finset.sum_eq_single_of_mem p.natDegree hnmem]
  · rw [hp.coeff_natDegree]
    have hcoeff : (B p.natDegree).coeff p.natDegree = 1 := by
      have htop := (hBmonic p.natDegree).coeff_natDegree
      rw [hBdeg p.natDegree] at htop
      exact htop
    simp [hcoeff]
  · intro n hn hne
    have hnle : n ≤ p.natDegree :=
      le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)
    have hnlt : n < p.natDegree := lt_of_le_of_ne hnle hne
    have hzero : (B n).coeff p.natDegree = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hBdeg n]
      exact hnlt
    simp [hzero]

/-- A degree-exact monic triangular basis sends monic polynomials to monic
polynomials. -/
theorem basisTransform_monic_of_monic
    {R : Type*} [CommRing R] [Nontrivial R] {B : ℕ → R[X]}
    (hBdeg : ∀ n, (B n).natDegree = n)
    (hBmonic : ∀ n, (B n).Monic) {p : R[X]} (hp : p.Monic) :
    (basisTransform B p).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one p.natDegree
  · exact basisTransform_natDegree_le_of_natDegree_le
      (fun n ↦ (hBdeg n).le) p
  · exact coeff_basisTransform_natDegree_eq_one_of_monic hBdeg hBmonic hp

end Polynomial

namespace RealRooted.Applications.OEIS

/-- The A144438 transform preserves monicity. -/
theorem a144438Transform_monic {p : ℝ[X]} (hp : p.Monic) :
    (a144438Transform p).Monic := by
  exact Polynomial.basisTransform_monic_of_monic
    decoEulerian_natDegree decoEulerian_monic hp

/-- The repeated-root input is monic. -/
theorem a144438Diagonal_monic (n : ℕ) (a : ℝ) :
    (a144438Diagonal n a).Monic := by
  apply a144438Transform_monic
  exact (monic_X_add_C a).pow n

/-- The diagonal transform has exactly the input degree. -/
theorem a144438Diagonal_natDegree (n : ℕ) (a : ℝ) :
    (a144438Diagonal n a).natDegree = n := by
  have hle : (a144438Diagonal n a).natDegree ≤ n := by
    unfold a144438Diagonal a144438Transform
    calc
      (Polynomial.basisTransform decoEulerian ((X + C a) ^ n)).natDegree ≤
          ((X + C a) ^ n).natDegree :=
        Polynomial.basisTransform_natDegree_le_of_natDegree_le
          (fun m ↦ (decoEulerian_natDegree m).le) ((X + C a) ^ n)
      _ = n := by
        rw [(monic_X_add_C a).natDegree_pow, natDegree_X_add_C]
        simp
  have hcoeff : (a144438Diagonal n a).coeff n = 1 := by
    have hinput : ((X + C a) ^ n).Monic := (monic_X_add_C a).pow n
    have hdegInput : ((X + C a) ^ n).natDegree = n := by
      rw [(monic_X_add_C a).natDegree_pow, natDegree_X_add_C]
      simp
    rw [← hdegInput]
    simpa [a144438Diagonal, a144438Transform] using
      (Polynomial.coeff_basisTransform_natDegree_eq_one_of_monic
        decoEulerian_natDegree decoEulerian_monic hinput)
  exact natDegree_eq_of_le_of_coeff_ne_zero hle (by norm_num [hcoeff])

/-- In particular, every diagonal transform has positive leading
coefficient. -/
theorem a144438Diagonal_hasPosLeadingCoeff (n : ℕ) (a : ℝ) :
    HasPosLeadingCoeff (a144438Diagonal n a) :=
  hasPosLeadingCoeff_of_monic (a144438Diagonal_monic n a)

/-- The lag basis element at index `n` has degree `n-1`. -/
theorem a144438LagBasis_natDegree (n : ℕ) :
    (a144438LagBasis n).natDegree = n - 1 := by
  cases n with
  | zero => simp [a144438LagBasis]
  | succ n => simp [a144438LagBasis, decoEulerian_natDegree]

/-- At positive rank the diagonal lag has degree strictly below the diagonal
transform. -/
theorem a144438DiagonalLag_natDegree_lt {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    (a144438DiagonalLag n a).natDegree < n := by
  have hinputDegree : ((X + C a) ^ n).natDegree = n := by
    rw [(monic_X_add_C a).natDegree_pow, natDegree_X_add_C]
    simp
  unfold a144438DiagonalLag a144438LagTransform
  refine lt_of_le_of_lt
    (Polynomial.basisTransform_natDegree_le_of_support ?_) (Nat.sub_lt hn zero_lt_one)
  intro m hm
  rw [a144438LagBasis_natDegree]
  have hmle : m ≤ n := by
    rw [← hinputDegree]
    exact le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hm)
  exact Nat.sub_le_sub_right hmle 1

/-- Degree form of `a144438DiagonalLag_natDegree_lt`, ready for the residue
expansion API. -/
theorem a144438DiagonalLag_degree_lt {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    (a144438DiagonalLag n a).degree < n := by
  calc
    (a144438DiagonalLag n a).degree ≤
        ((a144438DiagonalLag n a).natDegree : WithBot ℕ) := degree_le_natDegree
    _ < n := by exact_mod_cast a144438DiagonalLag_natDegree_lt hn a

end RealRooted.Applications.OEIS
