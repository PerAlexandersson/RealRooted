module

public import RealRooted.Hadamard.KostovMap
public import RealRooted.Hadamard.Kostov.Tangent

@[expose] public noncomputable section

open Polynomial

namespace RealRooted
namespace Kostov

/-! ## Main results -/

/-- The monic reduced polynomial in the eigendirection indexed by `j + 1`.
It is set to zero outside the natural range `j + 3 ≤ n`. -/
noncomputable def eigenpolynomial (n j : ℕ) : ℝ[X] :=
  if h : j + 3 ≤ n then Classical.choose (exists_reduced_eigenpolynomial n j h) else 0

private theorem eigenpolynomial_spec (n j : ℕ) (hj : j + 3 ≤ n) :
    (eigenpolynomial n j).Monic ∧ (eigenpolynomial n j).natDegree = j ∧
      (eigenpolynomial n j).eval 0 ≠ 0 ∧
      (eigenpolynomial n j).reverse = C ((-1 : ℝ) ^ j) * eigenpolynomial n j ∧
      (Odd j → (eigenpolynomial n j).eval 1 = 0) ∧
      ∃ v : Fin (n - 1) → ℝ, v ≠ 0 ∧
        monicPolynomial n v - monicPolynomial n 0 =
          X * (X + 1) ^ (n - j - 2) * eigenpolynomial n j ∧
        linearPart n v = eigenvalue n (j + 1) • v := by
  rw [eigenpolynomial, dite_eq_left hj]
  exact Classical.choose_spec (exists_reduced_eigenpolynomial n j hj)

/-- **Every eigenvalue candidate is an eigenvalue, with explicit nonzero eigenvector.** -/
theorem linearPart_hasEigenvector (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : k < n - 1) :
    ∃ v : Fin (n - 1) → ℝ, v ≠ 0 ∧ linearPart n v = eigenvalue n k • v := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · obtain ⟨v, hv, -, h⟩ := exists_first_eigenvector n hn
    exact ⟨v, hv, h⟩
  · obtain ⟨Q, -, -, -, -, -, v, hv, -, h⟩ :=
      exists_reduced_eigenpolynomial n (k - 1) (by lia)
    rw [show k - 1 + 1 = k by lia] at h
    exact ⟨v, hv, h⟩

/-- **The eigenspaces are lines**: eigenvectors for the same candidate eigenvalue are
proportional. -/
theorem linearPart_eigenspace_line (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : k < n - 1)
    (u v : Fin (n - 1) → ℝ) (hu : u ≠ 0) (hu' : linearPart n u = eigenvalue n k • u)
    (hv' : linearPart n v = eigenvalue n k • v) : ∃ c : ℝ, v = c • u := by
  obtain ⟨hne, hinv⟩ := eigenvalue_spec n k hk
  have hBu := bern_of_linearPart_eigen n hn u _ hne hu'
  have hBv := bern_of_linearPart_eigen n hn v _ hne hv'
  rw [hinv] at hBu hBv
  have hGu : Gv n u ≠ 0 := fun h => hu (Gv_injective n hn u h)
  have hdu := (Gv_natDegree n hn u).trans (show n - 1 ≤ n by lia)
  have hdv := (Gv_natDegree n hn v).trans (show n - 1 ≤ n by lia)
  have hc : ∃ c : ℝ, Gv n v = c • Gv n u := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [zero_add, mu_one n (by lia)] at hBu hBv
      have fu := eigen_one_form n (by lia) (Gv n u) hdu hBu (Gv_eval_one n u)
      have fv := eigen_one_form n (by lia) (Gv n v) hdv hBv (Gv_eval_one n v)
      have ha : (Gv n u).coeff 0 ≠ 0 := by
        intro h; rw [h, map_zero, zero_mul] at fu; exact hGu fu
      refine ⟨(Gv n v).coeff 0 / (Gv n u).coeff 0, ?_⟩
      calc Gv n v = C ((Gv n v).coeff 0) * (1 - X) := fv
        _ = ((Gv n v).coeff 0 / (Gv n u).coeff 0) • (C ((Gv n u).coeff 0) * (1 - X)) := by
          rw [smul_eq_C_mul, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ ha]
        _ = _ := by rw [← fu]
    · exact eigen_unique n (k + 1) (by lia) (by lia) (Gv n u) (Gv n v) hGu hdu hdv hBu hBv
  obtain ⟨c, hc⟩ := hc
  refine ⟨c, ?_⟩
  have : Gv n (v - c • u) = 0 := by rw [Gv_sub_smul, hc, sub_self]
  exact sub_eq_zero.mp (Gv_injective n hn _ this)

/-- The reduced eigenpolynomial is monic in its natural range. -/
theorem eigenpolynomial_monic (n j : ℕ) (hj : j + 3 ≤ n) :
    (eigenpolynomial n j).Monic :=
  (eigenpolynomial_spec n j hj).1

/-- The reduced eigenpolynomial has degree `j`. -/
theorem natDegree_eigenpolynomial (n j : ℕ) (hj : j + 3 ≤ n) :
    (eigenpolynomial n j).natDegree = j :=
  (eigenpolynomial_spec n j hj).2.1

/-- The reduced eigenpolynomial has nonzero constant coefficient. -/
theorem eval_zero_eigenpolynomial_ne_zero (n j : ℕ) (hj : j + 3 ≤ n) :
    (eigenpolynomial n j).eval 0 ≠ 0 :=
  (eigenpolynomial_spec n j hj).2.2.1

/-- The reduced eigenpolynomial is reciprocal up to the sign `(-1)^j`. -/
theorem reverse_eigenpolynomial (n j : ℕ) (hj : j + 3 ≤ n) :
    (eigenpolynomial n j).reverse =
      C ((-1 : ℝ) ^ j) * eigenpolynomial n j :=
  (eigenpolynomial_spec n j hj).2.2.2.1

/-- A reduced eigenpolynomial of odd degree vanishes at one. -/
theorem eval_one_eigenpolynomial_of_odd (n j : ℕ) (hj : j + 3 ≤ n)
    (hodd : Odd j) : (eigenpolynomial n j).eval 1 = 0 :=
  (eigenpolynomial_spec n j hj).2.2.2.2.1 hodd

/-- The reduced polynomial gives the actual eigendirection of the coefficient map. -/
theorem eigenpolynomial_hasEigenvector (n j : ℕ) (hj : j + 3 ≤ n) :
    ∃ v : Fin (n - 1) → ℝ, v ≠ 0 ∧
      monicPolynomial n v - monicPolynomial n 0 =
        X * (X + 1) ^ (n - j - 2) * eigenpolynomial n j ∧
      linearPart n v = eigenvalue n (j + 1) • v :=
  (eigenpolynomial_spec n j hj).2.2.2.2.2

/-- The first eigendirection has tangent polynomial `(X + 1)^(n - 1)`. -/
theorem linearPart_hasEigenvector_zero (n : ℕ) (hn : 2 ≤ n) :
    ∃ v : Fin (n - 1) → ℝ, v ≠ 0 ∧
      monicPolynomial n v - monicPolynomial n 0 = (X + 1) ^ (n - 1) ∧
      linearPart n v = eigenvalue n 0 • v :=
  exists_first_eigenvector n hn

/-- `Q_{n,1} = X - 1`. -/
theorem eigenpolynomial_one (n : ℕ) (hn : 4 ≤ n) :
    eigenpolynomial n 1 = X - 1 := by
  have h1 := (eigenpolynomial_monic n 1 (by lia)).eq_X_add_C
    (natDegree_eigenpolynomial n 1 (by lia))
  have h2 := eval_one_eigenpolynomial_of_odd n 1 (by lia) odd_one
  rw [h1] at h2
  simp only [eval_add, eval_X, eval_C] at h2
  rw [h1, show (eigenpolynomial n 1).coeff 0 = -1 by linarith]
  simp [sub_eq_add_neg]

end Kostov
end RealRooted
