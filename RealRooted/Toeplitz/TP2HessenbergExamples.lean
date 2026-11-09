module

public import RealRooted.Toeplitz.TP2Hessenberg

/-!
# Examples for the finite TP2 Hessenberg certificate

* The zero `1 × 1` matrix is singular, and its rows are `P_k = tᵏ`.
* For `A = [[1, 1], [0, 1]]`, `det (I + z A) = (1 + z)²`, the rows begin
  `1, t - 2, (t - 1) (t - 3)`, and the certificate applies.
-/

@[expose] public section

open Polynomial

namespace RealRooted

/-- The zero `1 × 1` matrix (singular) satisfies the hypotheses of the certificate. -/
example (k : ℕ) :
    (hessenbergRow (0 : Matrix (Fin 1) (Fin 1) ℝ) k).Monic ∧
      IsRealRootedIn (Set.Ici 0) (hessenbergRow (0 : Matrix (Fin 1) (Fin 1) ℝ) k) :=
  have hA : (0 : Matrix (Fin 1) (Fin 1) ℝ).IsTP2 :=
    ⟨fun _ _ => le_rfl, fun i₁ i₂ _ _ hi => absurd hi (by simp [Subsingleton.elim i₁ i₂])⟩
  ⟨(monic_natDegree_hessenbergRow _ (fun i j _ => by simp) k).1,
    isRealRootedIn_Ici_hessenbergRow hA (fun i k j _ => le_rfl)
      (fun i j _ => by simp) k⟩

/-- The rows of the zero `1 × 1` matrix are the powers of `t`. -/
theorem hessenbergRow_zero_one_by_one (k : ℕ) :
    hessenbergRow (0 : Matrix (Fin 1) (Fin 1) ℝ) k = X ^ k := by
  have hvec : ∀ k, hessenbergVector (0 : Matrix (Fin 1) (Fin 1) ℝ) k 0 = X ^ k := by
    intro k
    induction k with
    | zero => simp [hessenbergVector]
    | succ k ih => simp [hessenbergVector, tp2AffineStep, ih, pow_succ, mul_comm]
  rw [hessenbergRow_eq _ (fun i j _ => by simp) k, hvec]
  simp only [pow_comp, X_comp, map_pow, map_neg, map_one]
  rw [neg_pow (X : ℝ[X]), ← mul_assoc, ← mul_pow]
  norm_num

/-- The `2 × 2` matrix `[[1, 1], [0, 1]]`: nonsingular, `det (I + z A) = (1 + z)²`. -/
def hessenbergExampleTwo : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

lemma hessenbergExampleTwo_isTP2 : hessenbergExampleTwo.IsTP2 := by
  refine ⟨fun i j => ?_, fun i₁ i₂ j₁ j₂ hi hj => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [hessenbergExampleTwo]
  · fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      simp_all [hessenbergExampleTwo]

/-- The rows `P_0, P_1, P_2` of `[[1, 1], [0, 1]]` are `1`, `t - 2`, `(t - 1) (t - 3)`. -/
theorem hessenbergRow_exampleTwo :
    hessenbergRow hessenbergExampleTwo 0 = 1 ∧ hessenbergRow hessenbergExampleTwo 1 = X - 2 ∧
      hessenbergRow hessenbergExampleTwo 2 = (X - 1) * (X - 3) := by
  have hrow : ∀ ⦃i j : Fin 2⦄, i ≤ j → hessenbergExampleTwo i j = hessenbergExampleTwo j j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hessenbergExampleTwo]
  refine ⟨?_, ?_, ?_⟩ <;> rw [hessenbergRow_eq _ hrow] <;>
    simp [hessenbergVector, tp2AffineStep, hessenbergExampleTwo, Fin.sum_univ_two] <;> ring_nf

end RealRooted
