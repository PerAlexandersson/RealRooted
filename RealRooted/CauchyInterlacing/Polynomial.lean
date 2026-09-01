import RealRooted.Basic
import RealRooted.CauchyInterlacing

/-!
# Polynomial Cauchy interlacing

This module transports Cauchy's ordered-eigenvalue theorem to the library's
sorted-root `Interlaces` predicate for characteristic polynomials. Challenge
entry points remain in `RealRooted.Challenges.CauchyInterlacing`.
-/

open Matrix Polynomial

namespace RealRooted

private lemma coe_ofFn_rev_eq_univ_val_map {n : ℕ} {α : Type*} (f : Fin n → α) :
    (↑(List.ofFn fun k : Fin n => f k.rev) : Multiset α) =
      (Finset.univ : Finset (Fin n)).val.map f := by
  rw [← Fin.univ_val_map]
  change Multiset.map (f ∘ Fin.revPerm.toEmbedding) Finset.univ.val = _
  rw [← Multiset.map_map, ← Finset.map_val, Finset.map_univ_equiv]

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
    Interlaces (A.submatrix i.succAbove i.succAbove).charpoly A.charpoly := by
  let B : Matrix (Fin n) (Fin n) ℝ := A.submatrix i.succAbove i.succAbove
  let lam : Fin (n + 1) → ℝ := sortedEigenvalues A hA
  let μ : Fin n → ℝ := sortedEigenvalues B (hA.submatrix i.succAbove)
  let rs : List ℝ := List.ofFn fun k : Fin (n + 1) => lam k.rev
  let ss : List ℝ := List.ofFn fun k : Fin n => μ k.rev
  have hInter : Interlace μ lam := by
    simpa [B, μ, lam] using cauchy_interlacing ℝ A hA i
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

end RealRooted
