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

/-- Cauchy's interlacing theorem in characteristic-polynomial form for real
Hermitian matrices: the characteristic polynomial of a one-index principal
submatrix interlaces the characteristic polynomial of the original matrix. -/
theorem principalSubmatrix_charpoly_interlaces {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.IsHermitian) (i : Fin (n + 1)) :
    Interlaces (A.submatrix i.succAbove i.succAbove).charpoly A.charpoly := by
  have hroots : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.IsHermitian),
      (↑(List.ofFn fun k : Fin m => sortedEigenvalues M hM k.rev) : Multiset ℝ) =
        M.charpoly.roots := by
    intro m M hM
    rw [sortedEigenvalues_charpoly_roots M hM, ← Fin.univ_val_map]
    conv_rhs =>
      rw [← Finset.map_univ_equiv (Fin.revPerm (n := m)), Finset.map_val,
        Multiset.map_map]
    rfl
  have hpair : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.IsHermitian),
      (List.ofFn fun k : Fin m => sortedEigenvalues M hM k.rev).Pairwise (· ≤ ·) :=
    fun M hM => List.pairwise_ofFn.2 fun _ _ hab =>
      sortedEigenvalues_antitone M hM (Fin.rev_le_rev.2 hab.le)
  have hdeg : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ),
      M.charpoly.natDegree = m := fun M =>
    natDegree_eq_of_degree_eq_some (by simp [M.charpoly_degree_eq_dim])
  have hsplits : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.IsHermitian),
      M.charpoly.Splits := by
    intro m M hM
    exact splits_of_card_roots (by rw [← hroots M hM]; simp [hdeg])
  set B := A.submatrix i.succAbove i.succAbove
  have hB : B.IsHermitian := hA.submatrix i.succAbove
  have hint := cauchy_interlacing ℝ A hA i
  exact
    ⟨⟨A.charpoly_monic.ne_zero, hsplits A hA⟩,
      ⟨B.charpoly_monic.ne_zero, hsplits B hB⟩,
      by rw [hdeg, hdeg],
      List.ofFn fun k : Fin (n + 1) => sortedEigenvalues A hA k.rev,
      List.ofFn fun k : Fin n => sortedEigenvalues B hB k.rev,
      hpair A hA, hpair B hB, hroots A hA, hroots B hB,
      listInterlaces_of_interleaves_of_length (by simp)
        (List.interleaves_ofFn'.2
          ⟨fun k => by simpa [Fin.rev_succ] using (hint k.rev).2,
            fun k => by simpa [Fin.rev_castSucc] using (hint k.rev).1⟩)⟩

end RealRooted
