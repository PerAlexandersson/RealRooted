import RealRooted.Basic.ProperPosition
import RealRooted.CauchyInterlacing

/-!
# Polynomial Cauchy interlacing

This module transports Cauchy's ordered-eigenvalue theorem to the library's
sorted-root `Interlaces` predicate for characteristic polynomials. Challenge
entry points remain in `RealRooted.Challenges.CauchyInterlacing`.
-/

open Matrix Polynomial

namespace RealRooted

/-- The sorted eigenvalues of a Hermitian matrix, listed in increasing order, are the roots of
its characteristic polynomial. -/
theorem coe_ofFn_sortedEigenvalues_rev {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : M.IsHermitian) :
    (↑(List.ofFn fun k : Fin m => sortedEigenvalues M hM k.rev) : Multiset ℝ) =
      M.charpoly.roots := by
  rw [sortedEigenvalues_charpoly_roots M hM, ← Fin.univ_val_map]
  conv_rhs =>
    rw [← Finset.map_univ_equiv (Fin.revPerm (n := m)), Finset.map_val,
      Multiset.map_map]
  rfl

/-- The sorted eigenvalues listed in increasing order form a sorted list. -/
theorem pairwise_ofFn_sortedEigenvalues_rev {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : M.IsHermitian) :
    (List.ofFn fun k : Fin m => sortedEigenvalues M hM k.rev).Pairwise (· ≤ ·) :=
  List.pairwise_ofFn.2 fun _ _ hab =>
    sortedEigenvalues_antitone M hM (Fin.rev_le_rev.2 hab.le)

/-- Cauchy's interlacing theorem in characteristic-polynomial form for real
Hermitian matrices: the characteristic polynomial of a one-index principal
submatrix interlaces the characteristic polynomial of the original matrix. -/
theorem principalSubmatrix_charpoly_interlaces {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.IsHermitian) (i : Fin (n + 1)) :
    Interlaces (A.submatrix i.succAbove i.succAbove).charpoly A.charpoly := by
  set B := A.submatrix i.succAbove i.succAbove
  have hB : B.IsHermitian := hA.submatrix i.succAbove
  have hint := cauchy_interlacing ℝ A hA i
  exact
    ⟨⟨A.charpoly_monic.ne_zero, hA.splits_charpoly⟩,
      ⟨B.charpoly_monic.ne_zero, hB.splits_charpoly⟩,
      by simp [charpoly_natDegree_eq_dim],
      List.ofFn fun k : Fin (n + 1) => sortedEigenvalues A hA k.rev,
      List.ofFn fun k : Fin n => sortedEigenvalues B hB k.rev,
      pairwise_ofFn_sortedEigenvalues_rev A hA, pairwise_ofFn_sortedEigenvalues_rev B hB,
      coe_ofFn_sortedEigenvalues_rev A hA, coe_ofFn_sortedEigenvalues_rev B hB,
      listInterlaces_of_interleaves_of_length (by simp)
        (List.interleaves_ofFn'.2
          ⟨fun k => by simpa [Fin.rev_succ] using (hint k.rev).2,
            fun k => by simpa [Fin.rev_castSucc] using (hint k.rev).1⟩)⟩

end RealRooted
