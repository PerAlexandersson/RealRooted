import RealRooted.Basic
import RealRooted.CauchyInterlacing

/-!
# Cauchy interlacing challenge entry point

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#cauchyInterlacingTheorem

References used by the catalog:

* C. D. Godsil, "Algebraic Combinatorics", Routledge, 2017.
* S. Fisk, "A very short proof of Cauchy's interlace theorem for eigenvalues
  of Hermitian matrices", Amer. Math. Monthly 112 (2005), 118.

This module exposes the completed eigenvalue form of Cauchy's interlacing
theorem for Hermitian matrices.  The Courant--Fischer proof and spectral API
remain in `RealRooted.CauchyInterlacing`.
-/

open Matrix Polynomial

namespace RealRooted
namespace Challenges
namespace CauchyInterlacing

/-- Challenge-facing name for interlacing of ordered eigenvalue lists. -/
abbrev EigenvalueInterlaces {n : ℕ} (μ : Fin n → ℝ) (lam : Fin (n + 1) → ℝ) :
    Prop :=
  RealRooted.Interlace μ lam

/-- Challenge-facing name for the sorted eigenvalues of a Hermitian matrix. -/
noncomputable abbrev OrderedEigenvalues {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜) (hA : A.IsHermitian) : Fin N → ℝ :=
  RealRooted.sortedEigenvalues A hA

/-- Challenge-facing name for deleting one row and column from a matrix. -/
noncomputable abbrev PrincipalSubmatrix {𝕜 : Type*} {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (i : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  A.submatrix i.succAbove i.succAbove

/-- Cauchy's eigenvalue interlacing theorem for Hermitian matrices. -/
theorem theoremStatement :
    ∀ (𝕜 : Type*) [RCLike 𝕜], RealRooted.CauchyInterlacingStatement 𝕜 :=
  RealRooted.cauchy_interlacing

/-- Cauchy's interlacing theorem in principal-submatrix form: the eigenvalues
of the one-index principal submatrix interlace the eigenvalues of the original
Hermitian matrix. -/
theorem principalSubmatrix_eigenvalues_interlace
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜)
    (hA : A.IsHermitian) (i : Fin (n + 1)) :
    EigenvalueInterlaces
      (OrderedEigenvalues
        (PrincipalSubmatrix A i) (hA.submatrix i.succAbove))
      (OrderedEigenvalues A hA) :=
  theoremStatement 𝕜 A hA i

private lemma coe_ofFn_id_eq_univ_val {n : ℕ} :
    (↑(List.ofFn fun k : Fin n => k) : Multiset (Fin n)) =
      (Finset.univ : Finset (Fin n)).val := by
  apply Multiset.ext'
  intro a
  have hnodup_left :
      (↑(List.ofFn fun k : Fin n => k) : Multiset (Fin n)).Nodup := by
    simpa using ((List.nodup_ofFn).2 (fun _ _ h => h))
  have hnodup_right : (Finset.univ : Finset (Fin n)).val.Nodup := by
    exact (Finset.univ : Finset (Fin n)).nodup
  have hmem_left : a ∈ (↑(List.ofFn fun k : Fin n => k) : Multiset (Fin n)) := by
    simp [List.mem_ofFn]
  have hmem_right : a ∈ (Finset.univ : Finset (Fin n)).val := by simp
  rw [Multiset.count_eq_one_of_mem hnodup_left hmem_left,
    Multiset.count_eq_one_of_mem hnodup_right hmem_right]

private lemma coe_ofFn_eq_univ_val_map {n : ℕ} {α : Type*} (f : Fin n → α) :
    (↑(List.ofFn f) : Multiset α) =
      (Finset.univ : Finset (Fin n)).val.map f := by
  rw [List.ofFn_eq_map]
  exact congrArg (Multiset.map f) (coe_ofFn_id_eq_univ_val (n := n))

private lemma coe_ofFn_rev_eq_univ_val_map {n : ℕ} {α : Type*} (f : Fin n → α) :
    (↑(List.ofFn fun k : Fin n => f k.rev) : Multiset α) =
      (Finset.univ : Finset (Fin n)).val.map f := by
  rw [coe_ofFn_eq_univ_val_map]
  refine Multiset.map_eq_map_of_bij_of_nodup
    (fun k : Fin n => f k.rev) f
    (s := (Finset.univ : Finset (Fin n)).val)
    (t := (Finset.univ : Finset (Fin n)).val)
    (by exact (Finset.univ : Finset (Fin n)).nodup)
    (by exact (Finset.univ : Finset (Fin n)).nodup)
    (fun a _ => a.rev) ?_ ?_ ?_ ?_
  · intro a ha
    simp
  · intro a ha b hb h
    simpa using congrArg Fin.rev h
  · intro b hb
    exact ⟨b.rev, by simp, by simp⟩
  · intro a ha
    simp

private lemma pairwise_le_of_antitone_rev_ofFn {n : ℕ} {f : Fin n → ℝ}
    (hf : Antitone f) :
    (List.ofFn fun k : Fin n => f k.rev).Pairwise (· ≤ ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [List.getElem_ofFn, List.getElem_ofFn]
  apply hf
  rw [Fin.rev_le_rev]
  exact Nat.le_of_lt hij

private lemma listInterlaces_of_interlace_rev :
    ∀ {n : ℕ} {μ : Fin n → ℝ} {lam : Fin (n + 1) → ℝ},
      Interlace μ lam →
        ListInterlaces
          (List.ofFn fun k : Fin n => μ k.rev)
          (List.ofFn fun k : Fin (n + 1) => lam k.rev)
  | 0, _, _, _ => by
      simp [ListInterlaces]
  | n + 1, μ, lam, h => by
      rw [List.ofFn_succ]
      rw [List.ofFn_succ]
      rw [List.ofFn_succ]
      simp only [Fin.rev_zero, ListInterlaces]
      have hrev_one : (Fin.rev (1 : Fin (n + 2))) = (Fin.last n).castSucc := by
        ext
        simp [Fin.rev]
      refine ⟨?_, ?_, ?_⟩
      · simpa using (h (Fin.last n)).1
      · simpa [hrev_one] using (h (Fin.last n)).2
      · have htail : Interlace
            (fun k : Fin n => μ k.castSucc)
            (fun k : Fin (n + 1) => lam k.castSucc) := by
          intro k
          simpa [Interlace] using h k.castSucc
        simpa [Fin.rev_succ, hrev_one] using listInterlaces_of_interlace_rev htail

/-- Cauchy's interlacing theorem in characteristic-polynomial form for real
Hermitian matrices: the characteristic polynomial of a one-index principal
submatrix interlaces the characteristic polynomial of the original matrix. -/
theorem principalSubmatrix_charpoly_interlaces {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.IsHermitian) (i : Fin (n + 1)) :
    Interlaces (PrincipalSubmatrix A i).charpoly A.charpoly := by
  let B : Matrix (Fin n) (Fin n) ℝ := PrincipalSubmatrix A i
  let lam : Fin (n + 1) → ℝ := OrderedEigenvalues A hA
  let μ : Fin n → ℝ := OrderedEigenvalues B (hA.submatrix i.succAbove)
  let rs : List ℝ := List.ofFn fun k : Fin (n + 1) => lam k.rev
  let ss : List ℝ := List.ofFn fun k : Fin n => μ k.rev
  have hInter : Interlace μ lam := by
    simpa [B, μ, lam] using principalSubmatrix_eigenvalues_interlace A hA i
  have hA_ne : A.charpoly ≠ 0 := (Matrix.charpoly_monic A).ne_zero
  have hB_ne : B.charpoly ≠ 0 := (Matrix.charpoly_monic B).ne_zero
  have hA_nat : A.charpoly.natDegree = n + 1 := by
    have hdeg := Matrix.charpoly_degree_eq_dim A
    rw [Fintype.card_fin] at hdeg
    exact Polynomial.natDegree_eq_of_degree_eq_some hdeg
  have hB_nat : B.charpoly.natDegree = n := by
    have hdeg := Matrix.charpoly_degree_eq_dim B
    rw [Fintype.card_fin] at hdeg
    exact Polynomial.natDegree_eq_of_degree_eq_some hdeg
  have hrs_eq : (↑rs : Multiset ℝ) = A.charpoly.roots := by
    dsimp [rs, lam]
    rw [coe_ofFn_rev_eq_univ_val_map]
    exact (sortedEigenvalues_charpoly_roots A hA).symm
  have hss_eq : (↑ss : Multiset ℝ) = B.charpoly.roots := by
    dsimp [ss, μ, B]
    rw [coe_ofFn_rev_eq_univ_val_map]
    exact (sortedEigenvalues_charpoly_roots
      (A.submatrix i.succAbove i.succAbove) (hA.submatrix i.succAbove)).symm
  have hA_splits : A.charpoly.Splits := by
    apply splits_of_card_roots
    rw [← hrs_eq, Multiset.coe_card]
    simp [rs, hA_nat]
  have hB_splits : B.charpoly.Splits := by
    apply splits_of_card_roots
    rw [← hss_eq, Multiset.coe_card]
    simp [ss, hB_nat]
  refine
    ⟨⟨hA_ne, hA_splits⟩, ⟨hB_ne, hB_splits⟩, ?_,
      rs, ss, ?_, ?_, hrs_eq, hss_eq, ?_⟩
  · rw [hA_nat, hB_nat]
  · exact pairwise_le_of_antitone_rev_ofFn (sortedEigenvalues_antitone A hA)
  · exact pairwise_le_of_antitone_rev_ofFn
      (sortedEigenvalues_antitone B (hA.submatrix i.succAbove))
  · exact listInterlaces_of_interlace_rev hInter

end CauchyInterlacing
end Challenges
end RealRooted
