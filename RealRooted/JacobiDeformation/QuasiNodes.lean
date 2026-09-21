import RealRooted.Bezoutian.WronskianConverse
import RealRooted.Jacobi
import RealRooted.JacobiDeformation.Quadrature
import RealRooted.ObreschkoffConverse

/-!
# Nodes of quasi-Jacobi polynomials

The quasi-Jacobi polynomial is a real linear combination of consecutive monic
Favard polynomials.  Its nodes need not all be interior to the Jacobi interval.
-/

open Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- A nonconstant quasi-Jacobi polynomial is nonzero, split, and has simple
real roots. -/
theorem quasiJacobiPolynomial_ne_zero_splits_hasSimpleRoots
    {q : ℕ} (hq : 1 ≤ q) {α β τ : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    (quasiJacobiPolynomial q α β τ) ≠ 0 ∧
      (quasiJacobiPolynomial q α β τ).Splits ∧
        HasSimpleRoots (quasiJacobiPolynomial q α β τ) := by
  have hmonic : (quasiJacobiPolynomial q α β τ).IsMonicOfDegree q :=
    quasiJacobiPolynomial_isMonicOfDegree hq hα hβ
  have hq_ne : quasiJacobiPolynomial q α β τ ≠ 0 := hmonic.ne_zero
  have hprev_ne : shiftedJacobiMonic (q - 1) α β ≠ 0 :=
    shiftedJacobiMonic_ne_zero (q - 1) hα hβ
  have hprev_splits : (shiftedJacobiMonic (q - 1) α β).Splits :=
    shiftedJacobiMonic_splits (q - 1) hα hβ
  have hpair : StrictInterl (shiftedJacobiMonic (q - 1) α β)
      (shiftedJacobiMonic q α β) :=
    by
      simpa [Nat.sub_add_cancel hq] using
        shiftedJacobiMonic_prec_succ (q - 1) hα hβ
  have hall : AllComboRealRooted (shiftedJacobiMonic (q - 1) α β)
      (shiftedJacobiMonic q α β) :=
    allComboRealRooted_of_prec hpair
  have hquasi_eq : quasiJacobiPolynomial q α β τ =
      C (-τ) * shiftedJacobiMonic (q - 1) α β +
        C 1 * shiftedJacobiMonic q α β := by
    simp [quasiJacobiPolynomial]
    ring
  have hquasi_splits : (quasiJacobiPolynomial q α β τ).Splits := by
    rw [hquasi_eq]
    exact hall (-τ) 1
  have hall_prev_quasi : AllComboRealRooted (shiftedJacobiMonic (q - 1) α β)
      (quasiJacobiPolynomial q α β τ) :=
    allComboRealRooted_linear_recombination
      (a := 1) (b := 0) (c := -τ) (d := 1) (by simp) hquasi_eq hall
  have hdegree : (shiftedJacobiMonic (q - 1) α β).natDegree + 1 =
      (quasiJacobiPolynomial q α β τ).natDegree := by
    rw [natDegree_shiftedJacobiMonic (q - 1) hα hβ, hmonic.natDegree_eq]
    exact Nat.sub_add_cancel hq
  have hprec : StrictInterl (shiftedJacobiMonic (q - 1) α β)
      (quasiJacobiPolynomial q α β τ) :=
    StrictInterl.forward_of_orientation_of_succDegree hdegree.symm <|
      prec_of_allComboRealRooted hprev_ne hprev_splits hq_ne hquasi_splits
        hall_prev_quasi (Or.inl hdegree)
  have hno : ∀ r : ℝ, ¬ ((shiftedJacobiMonic (q - 1) α β).IsRoot r ∧
      (quasiJacobiPolynomial q α β τ).IsRoot r) := by
    intro r hr
    have hnext : (shiftedJacobiMonic q α β).IsRoot r := by
      have hprev_eval : (shiftedJacobiMonic (q - 1) α β).eval r = 0 := hr.1
      simpa [quasiJacobiPolynomial, Polynomial.IsRoot.def, hprev_eval] using hr.2
    have hno_succ := noCommonRoot_succ_of_favard
      (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ)
      (fun n => shiftedJacobiSubdiag_pos (n + 1) (by lia) hα hβ)
      (q - 1) r hr.1
    apply hno_succ
    simpa [Nat.sub_add_cancel hq] using hnext
  exact ⟨hq_ne, hquasi_splits,
    (hprec.hasSimpleRoots_of_no_common_root hno).2⟩

/-- Quasi-Jacobi polynomials admit an injective increasing enumeration of all
their roots.  No interval membership is asserted: an exterior node is allowed. -/
theorem exists_quasiJacobiPolynomial_orderedRoots
    {q : ℕ} (hq : 1 ≤ q) {α β τ : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    ∃ x : Fin q → ℝ, StrictMono x ∧ Function.Injective x ∧
      (∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i)) ∧
        ∀ r, (quasiJacobiPolynomial q α β τ).IsRoot r → ∃ i, x i = r := by
  obtain ⟨hquasi_ne, hquasi_splits, hquasi_simple⟩ :=
    quasiJacobiPolynomial_ne_zero_splits_hasSimpleRoots hq hα hβ
  have hdegree : (quasiJacobiPolynomial q α β τ).natDegree = q :=
    (quasiJacobiPolynomial_isMonicOfDegree hq hα hβ).natDegree_eq
  obtain ⟨x, hxmono, hxroots⟩ := Polynomial.exists_strictMono_roots
    hquasi_splits hdegree hquasi_simple.roots_nodup
  refine ⟨x, hxmono, hxmono.injective, hxroots, ?_⟩
  intro r hr
  exact exists_index_eq_of_mem_roots x hxmono hxroots hquasi_ne hdegree.le r
    ((mem_roots hquasi_ne).mpr hr)

end RealRooted.JacobiDeformation
