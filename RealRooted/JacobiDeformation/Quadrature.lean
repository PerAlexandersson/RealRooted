import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic
import RealRooted.Jacobi.Orthogonality

/-!
# Finite exact quadrature from polynomial orthogonality

This file isolates the algebraic quadrature argument used by the Jacobi
deformation proof.  No integral representation is needed: a linear functional
which annihilates a monic nodal polynomial times every sufficiently low-degree
polynomial is exactly a weighted sum of evaluations through degree `2q - 2`.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The quadrature weight obtained by applying a linear functional to a
Lagrange cardinal polynomial. -/
def quadratureWeight {q : ℕ} (L : ℝ[X] →ₗ[ℝ] ℝ) (x : Fin q → ℝ)
    (i : Fin q) : ℝ :=
  L (Lagrange.basis Finset.univ x i)

/-- Algebraic exact quadrature through degree `2q - 2`.

The hypothesis on `L` is precisely the orthogonality needed after division by
the monic nodal polynomial.  The restriction `q ≥ 2` is the range used for
the quasi-Jacobi argument; the one-node boundary is handled directly there. -/
theorem quadrature_exact {q : ℕ} (hq : 2 ≤ q)
    (L : ℝ[X] →ₗ[ℝ] ℝ) (x : Fin q → ℝ) (hx : Function.Injective x)
    (horth : ∀ g : ℝ[X], g.natDegree ≤ q - 2 →
      L (Lagrange.nodal Finset.univ x * g) = 0)
    {f : ℝ[X]} (hf : f.natDegree ≤ 2 * q - 2) :
    L f = ∑ i : Fin q, quadratureWeight L x i * f.eval (x i) := by
  let n : ℝ[X] := Lagrange.nodal Finset.univ x
  let g : ℝ[X] := f /ₘ n
  let r : ℝ[X] := f %ₘ n
  have hn : n.Monic := by
    simpa [n] using Lagrange.nodal_monic (s := Finset.univ) (v := x)
  have hndeg : n.natDegree = q := by
    simp [n]
  have hg : g.natDegree ≤ q - 2 := by
    dsimp only [g]
    rw [natDegree_divByMonic f hn, hndeg]
    lia
  have hrdeg : r.degree < (q : WithBot ℕ) := by
    simpa [r, n] using degree_modByMonic_lt f hn
  have hinterp : r = Lagrange.interpolate Finset.univ x (fun i => r.eval (x i)) := by
    apply Lagrange.eq_interpolate hx.injOn
    simpa using hrdeg
  have hrem_eval (i : Fin q) : r.eval (x i) = f.eval (x i) := by
    have hnode : n.eval (x i) = 0 := by
      exact Lagrange.eval_nodal_at_node (s := Finset.univ) (v := x) (mem_univ i)
    have hdecomp := congrArg (Polynomial.eval (x i)) (modByMonic_add_div f n)
    simpa only [r, g, eval_add, eval_mul, hnode, zero_mul, add_zero] using hdecomp
  have hdecomp : f = r + n * g := (modByMonic_add_div f n).symm
  calc
    L f = L r := by rw [hdecomp, map_add, horth g hg, add_zero]
    _ = L (Lagrange.interpolate Finset.univ x (fun i => r.eval (x i))) := congrArg L hinterp
    _ = ∑ i : Fin q, quadratureWeight L x i * f.eval (x i) := by
      rw [Lagrange.interpolate_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← smul_eq_C_mul, map_smul]
      simp only [smul_eq_mul, quadratureWeight]
      rw [hrem_eval]
      ring

/-- Positivity of every quadrature weight follows by applying exactness to the
square of its cardinal polynomial. -/
theorem quadratureWeight_pos {q : ℕ} (hq : 2 ≤ q)
    (L : ℝ[X] →ₗ[ℝ] ℝ) (x : Fin q → ℝ) (hx : Function.Injective x)
    (horth : ∀ g : ℝ[X], g.natDegree ≤ q - 2 →
      L (Lagrange.nodal Finset.univ x * g) = 0)
    (hpos : ∀ p : ℝ[X], p ≠ 0 → p.natDegree < q → 0 < L (p * p))
    (i : Fin q) :
    0 < quadratureWeight L x i := by
  let b : ℝ[X] := Lagrange.basis Finset.univ x i
  have hbne : b ≠ 0 := by
    exact Lagrange.basis_ne_zero hx.injOn (mem_univ i)
  have hbdeg : b.natDegree = q - 1 := by
    simpa [b] using Lagrange.natDegree_basis hx.injOn (mem_univ i)
  have hbdeglt : b.natDegree < q := by lia
  have hsqdeg : (b * b).natDegree ≤ 2 * q - 2 := by
    calc
      (b * b).natDegree ≤ b.natDegree + b.natDegree := natDegree_mul_le
      _ = 2 * q - 2 := by rw [hbdeg]; lia
  have hexact := quadrature_exact hq L x hx horth hsqdeg
  have hpositive := hpos b hbne hbdeglt
  rw [hexact] at hpositive
  have hsum :
      (∑ j : Fin q, quadratureWeight L x j * (b * b).eval (x j)) =
        quadratureWeight L x i := by
    calc
      (∑ j : Fin q, quadratureWeight L x j * (b * b).eval (x j)) =
          quadratureWeight L x i * (b * b).eval (x i) := by
        apply Fintype.sum_eq_single i
        intro j hji
        rw [eval_mul, show b.eval (x j) = 0 by
          exact Lagrange.eval_basis_of_ne hji.symm (mem_univ j), zero_mul, mul_zero]
      _ = quadratureWeight L x i := by
        rw [eval_mul, show b.eval (x i) = 1 by
          exact Lagrange.eval_basis_self hx.injOn (mem_univ i)]
        ring
  rwa [hsum] at hpositive

/-! ## Shifted-Jacobi specialization -/

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
  have hvmonic : v.Monic := by
    exact Lagrange.nodal_monic
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
        quadratureWeight
          (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i *
            f.eval (x i) := by
  let L := Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)
  apply quadrature_exact hq L x hx
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
    0 < quadratureWeight
      (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i := by
  let L := Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)
  apply quadratureWeight_pos hq L x hx
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
        quadratureWeight
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
    0 < quadratureWeight
      (Polynomial.momentFunctionalLinearMap (shiftedJacobiMoment α β)) x i := by
  apply shiftedJacobi_quadratureWeight_pos hq hα hβ x hx
  exact nodal_eq_quasiJacobiPolynomial (by lia) hα hβ x hx hroot

end RealRooted.JacobiDeformation
