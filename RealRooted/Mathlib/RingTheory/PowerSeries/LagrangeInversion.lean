import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.LinearCombination

/-!
# Lagrange–Bürmann inversion for formal power series

Let `A` be a commutative domain of characteristic zero and let `ρ φ : A⟦X⟧` with `ρ * φ = 1`.
Suppose `S : A⟦X⟧` has zero constant coefficient and is the compositional inverse of
`X * ρ`, that is, `(X * ρ) ∘ S = X`.  Equivalently, `S = X * φ ∘ S`, so that `S` is the
solution of a Lagrange-type fixed-point equation.  Then for every power series `H`
and every `m` we have
`(m + 1) [X ^ (m + 1)] (H ∘ S) = [X ^ m] (H' φ ^ (m + 1))`.

## Main results

* `PowerSeries.succ_mul_coeff_succ_subst`: the Lagrange–Bürmann inversion formula, in the form
  above.  This is the classical Lagrange inversion theorem; see for example Stanley,
  *Enumerative Combinatorics*, vol. 2, Theorem 5.4.2, or Gessel, *Lagrange inversion*,
  J. Combin. Theory Ser. A 144 (2016).
* `PowerSeries.exists_constantCoeff_eq_zero_apply_eq_self`: existence of a fixed point with zero
  constant coefficient for a map `T` on power series that is `X`-adically contracting.  This is
  the usual way to construct the series `S` above.

The proofs were found by Aristotle (Harmonic) and then ported and cleaned up by hand.
-/

namespace PowerSeries

variable {A : Type*} [CommRing A]

private lemma hasSubst_X_mul (ρ : A⟦X⟧) : HasSubst (X * ρ) :=
  HasSubst.of_constantCoeff_zero' (by simp)

private lemma coeff_pred_X_mul_pow_mul_derivative [IsDomain A] [CharZero A] (ρ φ : A⟦X⟧)
    (h : ρ * φ = 1) (i n : ℕ) (hi : i < n) :
    coeff (n - 1) ((X * ρ) ^ i * d⁄dX (X * ρ) * φ ^ n) = if i = n - 1 then 1 else 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = i + j + 1 := ⟨n - i - 1, by lia⟩
  have hd : d⁄dX (X * ρ) = ρ + X * d⁄dX ρ := by
    rw [Derivation.leibniz, derivative_X, smul_eq_mul, smul_eq_mul]
    ring
  have e1 : (X * ρ) ^ i * d⁄dX (X * ρ) * φ ^ (i + j + 1) =
      X ^ i * (φ ^ j + X * d⁄dX ρ * φ ^ (j + 1)) := by
    rw [hd]
    calc _ = X ^ i * (ρ * φ) ^ i * (ρ * φ * φ ^ j + X * d⁄dX ρ * φ ^ (j + 1)) := by ring
    _ = _ := by rw [h]; ring
  rw [e1, coeff_X_pow_mul', ite_eq_left (by lia), show i + j + 1 - 1 - i = j by lia]
  rcases j with _ | j
  · simp
  · rw [ite_eq_right (by lia)]
    have hρ' : d⁄dX ρ * φ = - (ρ * d⁄dX φ) := by
      have := congrArg (fun f : A⟦X⟧ => d⁄dX f) h
      rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at this
      linear_combination this
    have e2 : X * d⁄dX ρ * φ ^ (j + 1 + 1) = - (X * (d⁄dX φ * φ ^ j)) := by
      calc _ = X * (d⁄dX ρ * φ) * φ ^ (j + 1) := by ring
      _ = - (X * (d⁄dX φ * φ ^ j) * (ρ * φ)) := by rw [hρ']; ring
      _ = _ := by rw [h, mul_one]
    rw [e2, map_add, map_neg]
    rw [show (coeff (j + 1)) (X * (d⁄dX φ * φ ^ j)) = coeff j (d⁄dX φ * φ ^ j) by
      rw [coeff_succ_X_mul]]
    have e3 := coeff_derivative (φ ^ (j + 1)) j
    rw [derivative_pow] at e3
    rw [show ((↑(j + 1) : A⟦X⟧) * φ ^ (j + 1 - 1) * d⁄dX φ) =
        C ((j : A) + 1) * (d⁄dX φ * φ ^ j) by
      rw [show j + 1 - 1 = j by lia, show ((↑(j + 1) : A⟦X⟧)) = C ((j : A) + 1) by simp]
      ring, coeff_C_mul] at e3
    have hj : ((j : A) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have : coeff j (d⁄dX φ * φ ^ j) = coeff (j + 1) (φ ^ (j + 1)) := by
      apply mul_left_cancel₀ hj
      rw [e3]
      ring
    rw [this]
    ring

private lemma coeff_derivative_subst_X_mul_mul_pow [IsDomain A] [CharZero A]
    (ρ φ F : A⟦X⟧) (h : ρ * φ = 1) (m : ℕ) :
    coeff m (d⁄dX (subst (X * ρ) F) * φ ^ (m + 1)) = (m + 1 : A) * coeff (m + 1) F := by
  have hψ := hasSubst_X_mul ρ
  rw [derivative_subst hψ]
  set D := d⁄dX F with hD
  rw [eq_X_pow_mul_shift_add_trunc (m + 1) D, subst_add hψ, subst_mul hψ, subst_pow hψ,
    subst_X hψ, subst_coe hψ, Polynomial.aeval_eq_sum_range' (natDegree_trunc_lt D m)]
  rw [add_mul, add_mul, map_add]
  have h2 : coeff m ((X * ρ) ^ (m + 1) * subst (X * ρ) (mk fun i ↦ coeff (i + (m + 1)) D) *
      d⁄dX (X * ρ) * φ ^ (m + 1)) = 0 := by
    rw [show (X * ρ) ^ (m + 1) * subst (X * ρ) (mk fun i ↦ coeff (i + (m + 1)) D) *
      d⁄dX (X * ρ) * φ ^ (m + 1) = X ^ (m + 1) * (ρ ^ (m + 1) *
        subst (X * ρ) (mk fun i ↦ coeff (i + (m + 1)) D) * d⁄dX (X * ρ) * φ ^ (m + 1)) by ring,
      coeff_X_pow_mul', ite_eq_right (by lia)]
  rw [h2, zero_add, Finset.sum_mul, Finset.sum_mul, map_sum]
  have h3 : ∀ i ∈ Finset.range (m + 1), coeff m ((trunc (m + 1) D).coeff i • (X * ρ) ^ i *
      d⁄dX (X * ρ) * φ ^ (m + 1)) =
      (trunc (m + 1) D).coeff i * (if i = m then 1 else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have := coeff_pred_X_mul_pow_mul_derivative ρ φ h i (m + 1) hi
    simp only [add_tsub_cancel_right] at this
    rw [smul_mul_assoc, smul_mul_assoc, coeff_smul, this, smul_eq_mul]
  rw [Finset.sum_congr rfl h3]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range,
    lt_add_iff_pos_right, Nat.lt_add_one, ite_true]
  rw [coeff_trunc, ite_eq_left (by lia), hD, coeff_derivative]
  ring

private lemma subst_eq_zero_imp [IsDomain A] (S F : A⟦X⟧) (hS0 : constantCoeff S = 0)
    (hS1 : coeff 1 S ≠ 0) (h : subst S F = 0) : F = 0 := by
  have hS : HasSubst S := HasSubst.of_constantCoeff_zero' hS0
  by_contra hF
  have hco := coeff_order hF
  obtain ⟨F1, hF1⟩ := X_pow_order_dvd (φ := F)
  generalize F.order.toNat = k at hco hF1
  have hc : constantCoeff F1 ≠ 0 := by
    rw [hF1, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff] at hco
    exact hco
  have hSne : S ≠ 0 := by
    rintro rfl
    simp at hS1
  have hsub : subst S F1 ≠ 0 := by
    intro h0
    apply hc
    have := constantCoeff_subst_of_constantCoeff_zero hS0 F1
    rw [h0] at this
    simpa using this.symm
  rw [hF1, subst_mul hS, subst_pow hS, subst_X hS] at h
  exact mul_ne_zero (pow_ne_zero _ hSne) hsub h

/-- **Lagrange–Bürmann inversion.**  Let `ρ * φ = 1` and let `S` have zero constant coefficient
and satisfy `(X * ρ) ∘ S = X`.  Then for every power series `H` and every `m`,
`(m + 1) [X ^ (m + 1)] (H ∘ S) = [X ^ m] (H' φ ^ (m + 1))`. -/
theorem succ_mul_coeff_succ_subst [IsDomain A] [CharZero A] (ρ φ S H : A⟦X⟧) (h : ρ * φ = 1)
    (hS0 : constantCoeff S = 0) (hS : subst S (X * ρ) = X) (m : ℕ) :
    (m + 1 : A) * coeff (m + 1) (subst S H) = coeff m (d⁄dX H * φ ^ (m + 1)) := by
  have hSs : HasSubst S := HasSubst.of_constantCoeff_zero' hS0
  have hψ := hasSubst_X_mul ρ
  have hS1 : coeff 1 S ≠ 0 := by
    intro h0
    have := congrArg (coeff 1) hS
    rw [subst_mul hSs, subst_X hSs, coeff_X, ite_eq_left rfl, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
    simp [Finset.sum_range_succ, h0, hS0] at this
  have hU : subst (X * ρ) S = X := by
    have h0 : subst S (subst (X * ρ) S - X) = 0 := by
      rw [← coe_substAlgHom hSs, map_sub, coe_substAlgHom hSs,
        subst_comp_subst_apply hψ hSs, hS, X_subst, subst_X hSs, sub_self]
    exact sub_eq_zero.1 (subst_eq_zero_imp S _ hS0 hS1 h0)
  have := coeff_derivative_subst_X_mul_mul_pow ρ φ (subst S H) h m
  rw [subst_comp_subst_apply hSs hψ, hU, X_subst] at this
  exact this.symm

/-- Existence of a fixed point with zero constant coefficient for a map `T` on power series
that preserves series with zero constant coefficient and is contracting for the `X`-adic
topology: if `X ^ j` divides `a - b`, then `X ^ (j + 1)` divides `T a - T b`.  The fixed point is
the limit of the iterates `T^[k] 0`. -/
theorem exists_constantCoeff_eq_zero_apply_eq_self (T : A⟦X⟧ → A⟦X⟧)
    (hT0 : ∀ a, constantCoeff a = 0 → constantCoeff (T a) = 0)
    (hT : ∀ a b (j : ℕ), constantCoeff a = 0 → constantCoeff b = 0 → X ^ j ∣ a - b →
      X ^ (j + 1) ∣ T a - T b) :
    ∃ V, constantCoeff V = 0 ∧ T V = V := by
  let v : ℕ → A⟦X⟧ := fun k ↦ T^[k] 0
  have hv0 : ∀ k, constantCoeff (v k) = 0 := by
    intro k
    induction k with
    | zero => simp [v]
    | succ k ih =>
      simp only [v, Function.iterate_succ_apply'] at ih ⊢
      exact hT0 _ ih
  have hstep : ∀ k, X ^ k ∣ v (k + 1) - v k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hT _ _ k (hv0 _) (hv0 _) ih
      simpa only [v, Function.iterate_succ_apply'] using this
  have hfar : ∀ k l, X ^ k ∣ v (k + l) - v k := by
    intro k l
    induction l with
    | zero => simp
    | succ l ih =>
      have h1 : X ^ k ∣ v (k + l + 1) - v (k + l) :=
        (pow_dvd_pow X (by lia)).trans (hstep (k + l))
      have := dvd_add h1 ih
      rwa [sub_add_sub_cancel] at this
  let V : A⟦X⟧ := mk fun n ↦ coeff n (v (n + 1))
  have hV : ∀ n, X ^ (n + 1) ∣ V - v (n + 1) := by
    intro n
    rw [X_pow_dvd_iff]
    intro i hi
    rw [map_sub, coeff_mk, sub_eq_zero]
    obtain ⟨l, hl⟩ : ∃ l, n + 1 = (i + 1) + l := ⟨n - i, by lia⟩
    have := X_pow_dvd_iff.1 (hfar (i + 1) l) i (by lia)
    rw [← hl] at this
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  have hV0 : constantCoeff V = 0 := by
    have := X_pow_dvd_iff.1 (hV 0) 0 (by lia)
    rw [map_sub, sub_eq_zero, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply] at this
    rw [this, hv0]
  refine ⟨V, hV0, ?_⟩
  ext n
  have h1 := X_pow_dvd_iff.1 (hT _ _ _ hV0 (hv0 _) (hV n)) n (by lia)
  have h2 := X_pow_dvd_iff.1 (hstep (n + 1)) n (by lia)
  rw [map_sub, sub_eq_zero] at h1 h2
  have h3 : v (n + 2) = T (v (n + 1)) := by
    simp only [v, Function.iterate_succ_apply']
  rw [h1, ← h3, h2, coeff_mk]

end PowerSeries
