import RealRooted.Jacobi.Orthogonality
import RealRooted.Mathlib.LinearAlgebra.Lagrange.Quadrature

/-!
# Quasi-Jacobi quadrature

For `q ≥ 1` and real `τ`, the quasi-Jacobi polynomial
`v = p_q - τ p_{q-1}` (`quasiJacobiPolynomial`) combines two consecutive monic
shifted-Jacobi polynomials.  It is orthogonal to every polynomial of degree at
most `q - 2`, so the Lagrange quadrature of
`RealRooted.Mathlib.LinearAlgebra.Lagrange.Quadrature` at its roots is exact
through degree `2q - 2` and has positive weights.  We also prove the
derivative-weight identity at each node, that `p_{q-1}` does not vanish at a
node, and that the ratio `η_i = v'(t_i) / p_{q-1}(t_i)` (`quasiJacobiEta`) is
strictly positive.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The normalized monic shifted-Jacobi polynomial is orthogonal to every
strictly lower-degree polynomial for the classical finite moment pairing. -/
theorem shiftedJacobiMonicInner_eq_zero {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (g : ℝ[X])
    (hg : g.natDegree < n) :
    shiftedJacobiInner α β (shiftedJacobiMonic n α β) g = 0 := by
  rw [shiftedJacobiMonic, shiftedJacobiInner_C_mul_left,
    shiftedJacobiInner_eq_zero hα hβ g]
  · ring
  · simpa using hg

/-- The monic quasi-Jacobi nodal polynomial `p_q - τ p_{q-1}`. -/
def quasiJacobiPolynomial (q : ℕ) (α β τ : ℝ) : ℝ[X] :=
  shiftedJacobiMonic q α β - C τ * shiftedJacobiMonic (q - 1) α β

theorem quasiJacobiPolynomial_isMonicOfDegree {q : ℕ} (hq : 1 ≤ q)
    {α β τ : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    (quasiJacobiPolynomial q α β τ).IsMonicOfDegree q := by
  have hrec := shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ
  apply (hrec.isMonicOfDegree q).sub
  calc
    (C τ * shiftedJacobiMonic (q - 1) α β).natDegree ≤
        (shiftedJacobiMonic (q - 1) α β).natDegree := natDegree_C_mul_le _ _
    _ = q - 1 := hrec.natDegree_eq (q - 1)
    _ < q := by lia

/-- Distinct explicit roots determine the monic quasi-Jacobi polynomial and
therefore supply the nodal identity required by quadrature. -/
theorem nodal_eq_quasiJacobiPolynomial {q : ℕ} (hq : 1 ≤ q)
    {α β τ : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i)) :
    Lagrange.nodal Finset.univ x = quasiJacobiPolynomial q α β τ := by
  let v := Lagrange.nodal Finset.univ x
  let p := quasiJacobiPolynomial q α β τ
  have hvmonic : v.Monic :=
    Lagrange.nodal_monic
  have hvdeg : v.degree = q := by
    rw [degree_eq_natDegree hvmonic.ne_zero]
    simp [v]
  have hpdata : p.IsMonicOfDegree q :=
    quasiJacobiPolynomial_isMonicOfDegree hq hα hβ
  have hpdeg : p.degree = q := by
    rw [degree_eq_natDegree hpdata.ne_zero, hpdata.natDegree_eq]
  apply Polynomial.eq_of_degree_le_of_eval_index_eq Finset.univ hx.injOn
  · rw [hvdeg]
    simp
  · exact hvdeg.trans hpdeg.symm
  · rw [hvmonic.leadingCoeff, hpdata.monic.leadingCoeff]
  · intro i _
    rw [Lagrange.eval_nodal_at_node (mem_univ i), hroot i]

/-- The quasi-Jacobi polynomial is orthogonal to every polynomial of degree at
most `q - 2`. -/
theorem shiftedJacobiInner_quasiJacobiPolynomial_eq_zero
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (g : ℝ[X])
    (hg : g.natDegree ≤ q - 2) :
    shiftedJacobiInner α β (quasiJacobiPolynomial q α β τ) g = 0 := by
  have hgq : g.natDegree < q := by lia
  have hgprev : g.natDegree < q - 1 := by lia
  rw [shiftedJacobiInner_comm, quasiJacobiPolynomial,
    shiftedJacobiInner_sub_right, shiftedJacobiInner_C_mul_right,
    shiftedJacobiInner_comm α β g (shiftedJacobiMonic q α β),
    shiftedJacobiMonicInner_eq_zero hα hβ g hgq,
    shiftedJacobiInner_comm α β g (shiftedJacobiMonic (q - 1) α β),
    shiftedJacobiMonicInner_eq_zero hα hβ g hgprev]
  ring

/-- Exact quadrature at any explicit simple enumeration of the roots of a
quasi-Jacobi polynomial. -/
theorem shiftedJacobi_quadrature_exact {q : ℕ} (hq : 2 ≤ q)
    {α β τ : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hnodal : Lagrange.nodal Finset.univ x =
      quasiJacobiPolynomial q α β τ)
    {f : ℝ[X]} (hf : f.natDegree ≤ 2 * q - 2) :
    shiftedJacobiFunctional α β f =
      ∑ i : Fin q,
        Lagrange.quadratureWeight
          (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i *
            f.eval (x i) := by
  let L := Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)
  apply Lagrange.quadrature_exact hq L x hx
  · intro g hg
    change shiftedJacobiInner α β (Lagrange.nodal Finset.univ x) g = 0
    rw [hnodal]
    exact shiftedJacobiInner_quasiJacobiPolynomial_eq_zero hq hα hβ g hg
  · exact hf

/-- Every quadrature weight at explicit distinct quasi-Jacobi nodes is
strictly positive. -/
theorem shiftedJacobi_quadratureWeight_pos {q : ℕ} (hq : 2 ≤ q)
    {α β τ : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hnodal : Lagrange.nodal Finset.univ x =
      quasiJacobiPolynomial q α β τ) (i : Fin q) :
    0 < Lagrange.quadratureWeight
      (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i := by
  let L := Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)
  apply Lagrange.quadratureWeight_pos hq L x hx
  · intro g hg
    change shiftedJacobiInner α β (Lagrange.nodal Finset.univ x) g = 0
    rw [hnodal]
    exact shiftedJacobiInner_quasiJacobiPolynomial_eq_zero hq hα hβ g hg
  · intro p hp _
    have hpos := shiftedJacobiMomentPairingBilinForm_posDef hα hβ p hp
    have hpos' : 0 < shiftedJacobiInner α β p p := by
      simpa only [LinearMap.BilinMap.toQuadraticMap_apply,
        Polynomial.momentPairingBilinForm_apply, shiftedJacobiInner] using hpos
    change 0 < shiftedJacobiFunctional α β (p * p)
    simpa only [shiftedJacobiInner, shiftedJacobiFunctional,
      Polynomial.momentPairing] using hpos'

/-- Root-data form of exact quasi-Jacobi quadrature. -/
theorem shiftedJacobi_quadrature_exact_of_roots {q : ℕ} (hq : 2 ≤ q)
    {α β τ : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    {f : ℝ[X]} (hf : f.natDegree ≤ 2 * q - 2) :
    shiftedJacobiFunctional α β f =
      ∑ i : Fin q,
        Lagrange.quadratureWeight
          (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i *
            f.eval (x i) := by
  apply shiftedJacobi_quadrature_exact hq hα hβ x hx
  · exact nodal_eq_quasiJacobiPolynomial (by lia) hα hβ x hx hroot
  · exact hf

/-- Root-data form of strict positivity of quasi-Jacobi quadrature weights. -/
theorem shiftedJacobi_quadratureWeight_pos_of_roots {q : ℕ} (hq : 2 ≤ q)
    {α β τ : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    (i : Fin q) :
    0 < Lagrange.quadratureWeight
      (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i := by
  apply shiftedJacobi_quadratureWeight_pos hq hα hβ x hx
  exact nodal_eq_quasiJacobiPolynomial (by lia) hα hβ x hx hroot

/-- Orthogonality identifies the cardinal pairing after multiplication by the
nodal derivative. -/
theorem shiftedJacobi_eval_derivative_nodal_mul_inner_basis
    {q : ℕ} (hq : 2 ≤ q) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x) (i : Fin q) :
    (Lagrange.nodal Finset.univ x).derivative.eval (x i) *
        shiftedJacobiInner α β (Lagrange.basis Finset.univ x i)
          (shiftedJacobiMonic (q - 1) α β) =
      shiftedJacobiInner α β (shiftedJacobiMonic (q - 1) α β)
        (shiftedJacobiMonic (q - 1) α β) := by
  let v := Lagrange.nodal Finset.univ x
  let b := Lagrange.basis Finset.univ x i
  let p := shiftedJacobiMonic (q - 1) α β
  let d := v.derivative.eval (x i)
  have hpmono : p.IsMonicOfDegree (q - 1) :=
    (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ).isMonicOfDegree _
  have hbdeg : b.natDegree = q - 1 := by
    simpa [b] using Lagrange.natDegree_basis hx.injOn (mem_univ i)
  have hdne : d ≠ 0 :=
    Lagrange.eval_derivative_nodal_ne_zero x hx i
  have hblc : b.leadingCoeff = d⁻¹ :=
    Lagrange.leadingCoeff_basis_eq_inv_eval_derivative_nodal x hx i
  have hdbmono : (C d * b).IsMonicOfDegree (q - 1) := by
    refine ⟨?_, ?_⟩
    · rw [natDegree_C_mul hdne, hbdeg]
    · rw [Monic.def, leadingCoeff_mul, leadingCoeff_C, hblc]
      field_simp
  have hremdeg : (C d * b - p).natDegree < q - 1 :=
    hdbmono.natDegree_sub_lt (by lia) hpmono
  have horthrem := shiftedJacobiMonicInner_eq_zero hα hβ
    (C d * b - p) hremdeg
  change shiftedJacobiInner α β p (C d * b - p) = 0 at horthrem
  have hinner' :
      d * shiftedJacobiInner α β p b = shiftedJacobiInner α β p p := by
    simpa [shiftedJacobiInner_sub_right, shiftedJacobiInner_C_mul_right,
      sub_eq_zero] using horthrem
  have hinner :
      d * shiftedJacobiInner α β b p = shiftedJacobiInner α β p p := by
    rw [shiftedJacobiInner_comm α β b p]
    exact hinner'
  exact hinner

/-- Exact quadrature identifies a quasi-Jacobi weight times the preceding
Jacobi value with its cardinal pairing. -/
theorem shiftedJacobi_quadratureWeight_mul_eval_prev
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    (i : Fin q) :
    Lagrange.quadratureWeight
        (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i *
        (shiftedJacobiMonic (q - 1) α β).eval (x i) =
      shiftedJacobiInner α β (Lagrange.basis Finset.univ x i)
        (shiftedJacobiMonic (q - 1) α β) := by
  let L := Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)
  let v := Lagrange.nodal Finset.univ x
  let b := Lagrange.basis Finset.univ x i
  let p := shiftedJacobiMonic (q - 1) α β
  have hv : v = quasiJacobiPolynomial q α β τ :=
    nodal_eq_quasiJacobiPolynomial (by lia) hα hβ x hx hroot
  have hpdeg : p.natDegree < q := by
    rw [show p.natDegree = q - 1 by
      exact (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ).natDegree_eq _]
    lia
  have hquad :
      Lagrange.quadratureWeight L x i * p.eval (x i) =
        shiftedJacobiInner α β b p := by
    change Lagrange.quadratureWeight L x i * p.eval (x i) = L (b * p)
    apply Lagrange.quadratureWeight_mul_eval hq L x hx
    · intro g hg
      change shiftedJacobiInner α β v g = 0
      rw [hv]
      exact shiftedJacobiInner_quasiJacobiPolynomial_eq_zero hq hα hβ g hg
    · exact hpdeg
  exact hquad

/-- Exact Christoffel-weight identity at explicit quasi-Jacobi nodes.  It is
stated without division: the nodal derivative, the quadrature weight, and the
value of the preceding monic Jacobi polynomial multiply to its squared norm. -/
theorem shiftedJacobi_derivative_mul_quadratureWeight_mul_eval_prev
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    (i : Fin q) :
    (quasiJacobiPolynomial q α β τ).derivative.eval (x i) *
        Lagrange.quadratureWeight
          (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i *
        (shiftedJacobiMonic (q - 1) α β).eval (x i) =
      shiftedJacobiInner α β (shiftedJacobiMonic (q - 1) α β)
        (shiftedJacobiMonic (q - 1) α β) := by
  have hv := nodal_eq_quasiJacobiPolynomial (by lia) hα hβ x hx hroot
  rw [← hv, mul_assoc,
    shiftedJacobi_quadratureWeight_mul_eval_prev hq hα hβ x hx hroot i]
  exact shiftedJacobi_eval_derivative_nodal_mul_inner_basis hq hα hβ x hx i

/-- The preceding monic Jacobi polynomial cannot vanish at a simple root of
the quasi-Jacobi nodal polynomial. -/
theorem shiftedJacobiMonic_eval_prev_ne_zero_of_roots
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    (i : Fin q) :
    (shiftedJacobiMonic (q - 1) α β).eval (x i) ≠ 0 := by
  have hpmono :=
    (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ).isMonicOfDegree (q - 1)
  have hnorm := shiftedJacobiMomentPairingBilinForm_posDef hα hβ
    (shiftedJacobiMonic (q - 1) α β) hpmono.monic.ne_zero
  have hnormpos :
      0 < shiftedJacobiInner α β (shiftedJacobiMonic (q - 1) α β)
        (shiftedJacobiMonic (q - 1) α β) := by
    simpa only [LinearMap.BilinMap.toQuadraticMap_apply,
      Polynomial.momentPairingBilinForm_apply, shiftedJacobiInner] using hnorm
  intro heval
  have hid := shiftedJacobi_derivative_mul_quadratureWeight_mul_eval_prev
    hq hα hβ x hx hroot i
  rw [heval, mul_zero] at hid
  linarith

/-- The positive ratio `v'(x_i) / p_{q-1}(x_i)` used to normalize the
quasi-Jacobi collocation matrix. -/
def quasiJacobiEta (q : ℕ) (α β τ : ℝ) (x : Fin q → ℝ)
    (i : Fin q) : ℝ :=
  (quasiJacobiPolynomial q α β τ).derivative.eval (x i) /
    (shiftedJacobiMonic (q - 1) α β).eval (x i)

theorem quasiJacobiEta_pos_of_roots
    {q : ℕ} (hq : 2 ≤ q) {α β τ : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial q α β τ).IsRoot (x i))
    (i : Fin q) :
    0 < quasiJacobiEta q α β τ x i := by
  let d := (quasiJacobiPolynomial q α β τ).derivative.eval (x i)
  let p := (shiftedJacobiMonic (q - 1) α β).eval (x i)
  let w := Lagrange.quadratureWeight
    (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i
  have hw : 0 < w := shiftedJacobi_quadratureWeight_pos_of_roots
    hq hα hβ x hx hroot i
  have hpmono :=
    (shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ).isMonicOfDegree (q - 1)
  have hnorm := shiftedJacobiMomentPairingBilinForm_posDef hα hβ
    (shiftedJacobiMonic (q - 1) α β) hpmono.monic.ne_zero
  have hnormpos :
      0 < shiftedJacobiInner α β (shiftedJacobiMonic (q - 1) α β)
        (shiftedJacobiMonic (q - 1) α β) := by
    simpa only [LinearMap.BilinMap.toQuadraticMap_apply,
      Polynomial.momentPairingBilinForm_apply, shiftedJacobiInner] using hnorm
  have hid := shiftedJacobi_derivative_mul_quadratureWeight_mul_eval_prev
    hq hα hβ x hx hroot i
  have hdpw : 0 < (d * p) * w := by
    rw [mul_assoc, mul_comm p w, ← mul_assoc]
    rw [hid]
    exact hnormpos
  have hdp : 0 < d * p := by
    rcases (mul_pos_iff.mp hdpw) with h | h
    · exact h.1
    · exact (not_lt_of_ge hw.le h.2).elim
  change 0 < d / p
  rcases (mul_pos_iff.mp hdp) with h | h
  · exact div_pos h.1 h.2
  · exact div_pos_of_neg_of_neg h.1 h.2

end RealRooted.JacobiDeformation
