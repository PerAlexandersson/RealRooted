module

public import RealRooted.Mesh.FiniteDifference

/-!
# The discrete Hermite--Poulain theorem

Brändén, Krasikov, and Shapiro, *Elements of Pólya--Schur theory in the finite
difference setting*, Proc. AMS 144 (2016), Theorem 3: the operator
`p ↦ a₀ p(x) + a₁ p(x - α) + ⋯ + a_k p(x - kα)` preserves mesh at least `β ≥ α`
whenever all zeros of its symbol `a₀ + a₁ t + ⋯ + a_k t^k` are real and
nonnegative.  This module proves that sufficiency direction from the one-step
case, BKS Theorem 2 (`RealRooted.meshDifference_meshGE`).  See RealRooted issue #2070.
-/

@[expose] public section

open Polynomial

namespace RealRooted

noncomputable section

/-- The constant-coefficient finite-difference operator with symbol `Q` and step `α`:
`p ↦ ∑ₖ Q.coeff k • p(X - k α)`. -/
def finiteDifferenceOp (α : ℝ) (Q p : ℝ[X]) : ℝ[X] :=
  Q.sum fun k a => C a * p.comp (X - C ((k : ℝ) * α))

variable {α : ℝ} {Q Q₁ Q₂ p : ℝ[X]}

@[simp]
theorem finiteDifferenceOp_monomial (n : ℕ) (a : ℝ) :
    finiteDifferenceOp α (monomial n a) p = C a * p.comp (X - C ((n : ℝ) * α)) := by
  simp [finiteDifferenceOp, sum_monomial_index]

@[simp]
theorem finiteDifferenceOp_zero : finiteDifferenceOp α 0 p = 0 := by
  simp [finiteDifferenceOp]

/-- The operator is additive in its symbol. -/
theorem finiteDifferenceOp_add :
    finiteDifferenceOp α (Q₁ + Q₂) p =
      finiteDifferenceOp α Q₁ p + finiteDifferenceOp α Q₂ p := by
  unfold finiteDifferenceOp
  exact sum_add_index _ _ _ (by simp) (by intros; simp [C_add, add_mul])

/-- A constant symbol acts by scalar multiplication. -/
@[simp]
theorem finiteDifferenceOp_C (a : ℝ) : finiteDifferenceOp α (C a) p = C a * p := by
  simp [← monomial_zero_left]

/-- The symbol `X` acts as the translation `p(x) ↦ p(x - α)`. -/
@[simp]
theorem finiteDifferenceOp_X : finiteDifferenceOp α X p = p.comp (X - C α) := by
  conv_lhs => rw [← monomial_one_one_eq_X]
  rw [finiteDifferenceOp_monomial]
  simp

@[simp]
theorem finiteDifferenceOp_one : finiteDifferenceOp α 1 p = p := by
  simpa using finiteDifferenceOp_C (α := α) (p := p) 1

/-- Operators with product symbols compose, since translations commute. -/
theorem finiteDifferenceOp_mul :
    finiteDifferenceOp α (Q₁ * Q₂) p =
      finiteDifferenceOp α Q₁ (finiteDifferenceOp α Q₂ p) := by
  induction Q₁ using Polynomial.induction_on' with
  | add q r hq hr => rw [add_mul, finiteDifferenceOp_add, hq, hr, finiteDifferenceOp_add]
  | monomial n a =>
    induction Q₂ using Polynomial.induction_on' with
    | add q r hq hr =>
      rw [mul_add, finiteDifferenceOp_add, hq, hr, finiteDifferenceOp_add,
        finiteDifferenceOp_monomial, finiteDifferenceOp_monomial, finiteDifferenceOp_monomial,
        add_comp, mul_add]
    | monomial m b =>
      have hcomp : (X - C ((m : ℝ) * α)).comp (X - C ((n : ℝ) * α)) =
          X - C (((n + m : ℕ) : ℝ) * α) := by
        simp only [sub_comp, X_comp, C_comp, Nat.cast_add, add_mul, C_add]
        ring
      simp only [monomial_mul_monomial, finiteDifferenceOp_monomial, mul_comp, C_comp,
        comp_assoc, hcomp]
      rw [C_mul, mul_assoc]

/-- The symbol `X - C r` gives `p(x - α) - r p(x)`. -/
theorem finiteDifferenceOp_X_sub_C (r : ℝ) :
    finiteDifferenceOp α (X - C r) p = p.comp (X - C α) - C r * p := by
  rw [sub_eq_add_neg, ← C_neg, finiteDifferenceOp_add, finiteDifferenceOp_X,
    finiteDifferenceOp_C, C_neg]
  ring

/-- For `r > 0`, the symbol `X - C r` is `-r` times the one-step operator
`meshDifference α r⁻¹` of BKS Theorem 2. -/
theorem finiteDifferenceOp_X_sub_C_eq_meshDifference {r : ℝ} (hr : 0 < r) :
    finiteDifferenceOp α (X - C r) p = C (-r) * meshDifference α r⁻¹ p := by
  rw [finiteDifferenceOp_X_sub_C, meshDifference, mul_sub, ← mul_assoc, ← C_mul, neg_mul,
    mul_inv_cancel₀ hr.ne']
  simp [sub_eq_add_neg, add_comm]

private theorem meshGE_finiteDifferenceOp_X_sub_C {r β : ℝ} (hα : 0 < α) (hr : 0 ≤ r)
    (hp : p.MeshGE β) (hαβ : α ≤ β) : (finiteDifferenceOp α (X - C r) p).MeshGE β := by
  rcases hr.eq_or_lt with rfl | hr
  · have h := (Polynomial.MeshGE.comp_X_add_C_iff p β (-α)).2 hp
    simpa [finiteDifferenceOp_X_sub_C, sub_eq_add_neg] using h
  · rw [finiteDifferenceOp_X_sub_C_eq_meshDifference hr]
    exact (Polynomial.MeshGE.C_mul_iff _ _ (neg_ne_zero.2 hr.ne')).2
      (meshDifference_meshGE hα (inv_pos.2 hr) hp hαβ)

private theorem meshGE_finiteDifferenceOp_prod {β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (s : Multiset ℝ) (hs : ∀ r ∈ s, 0 ≤ r) (hp : p.MeshGE β) :
    (finiteDifferenceOp α (s.map (X - C ·)).prod p).MeshGE β := by
  induction s using Multiset.induction_on with
  | empty => simpa using hp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, finiteDifferenceOp_mul]
    exact meshGE_finiteDifferenceOp_X_sub_C hα (hs a (Multiset.mem_cons_self a s))
      (ih fun r hr => hs r (Multiset.mem_cons_of_mem hr)) hαβ

/-- **Discrete Hermite--Poulain theorem, sufficiency** (BKS Theorem 3).  If every zero of
the symbol `Q` is real and nonnegative, the operator `∑ₖ aₖ p(x - kα)` preserves mesh at
least `β` for every `β ≥ α > 0`. -/
theorem finiteDifferenceOp_meshGE {β : ℝ} (hα : 0 < α)
    (hQ : HasOnlyNonnegRoots Q) (hp : p.MeshGE β) (hαβ : α ≤ β) :
    (finiteDifferenceOp α Q p).MeshGE β := by
  by_cases hQ0 : Q = 0
  · subst Q
    exact Polynomial.MeshGE.of_natDegree_le_one (by simp) (by simp) hp.2.1
  obtain ⟨hs, hr⟩ := hQ.resolve_left hQ0
  have hQeq := hs.eq_prod_roots
  have hlc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hQ0
  rw [hQeq, finiteDifferenceOp_mul, finiteDifferenceOp_C]
  exact (Polynomial.MeshGE.C_mul_iff _ _ hlc).2
    (meshGE_finiteDifferenceOp_prod hα hαβ _ hr hp)

end

end RealRooted
