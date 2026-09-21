import Mathlib.LinearAlgebra.Lagrange
import RealRooted.Favard.Orthogonality

/-!
# Algebraic Gaussian quadrature

This file isolates the finite algebra behind the quadrature step in the Jacobi
deformation argument.  The nodes are not assumed to lie in any interval.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The cardinal polynomial at a node of a finite family of distinct real
nodes. -/
def cardinalPolynomial {q : ℕ} (nodes : Fin q → ℝ) (i : Fin q) : ℝ[X] :=
  Lagrange.basis Finset.univ nodes i

/-- The weight attached to a cardinal polynomial by a linear functional. -/
def cardinalWeight {q : ℕ} (ell : ℝ[X] →ₗ[ℝ] ℝ)
    (nodes : Fin q → ℝ) (i : Fin q) : ℝ :=
  ell (cardinalPolynomial nodes i)

/-- The finite quadrature rule associated with a linear functional and a
family of nodes. -/
def quadrature {q : ℕ} (ell : ℝ[X] →ₗ[ℝ] ℝ)
    (nodes : Fin q → ℝ) (f : ℝ[X]) : ℝ :=
  ∑ i, cardinalWeight ell nodes i * f.eval (nodes i)

/-- The normalized Favard functional is strictly positive on nonzero squares. -/
theorem favardFunctional_mul_self_pos
    {P : ℕ → ℝ[X]} {α β : ℕ → ℝ} (hrec : SatisfiesFavardRecurrence P α β)
    (hβ : ∀ n, 0 < β (n + 1)) {f : ℝ[X]} (hf : f ≠ 0) :
    0 < hrec.functional (f * f) :=
  hrec.functional_mul_self_pos hβ hf

/-- Cardinal polynomials are nonzero at distinct finite nodes. -/
theorem cardinalPolynomial_ne_zero {q : ℕ} {nodes : Fin q → ℝ}
    (hnodes : Function.Injective nodes) (i : Fin q) :
    cardinalPolynomial nodes i ≠ 0 := by
  apply Lagrange.basis_ne_zero
  · intro j _ k _ hjk
    exact hnodes hjk
  · simp

/-- A cardinal polynomial evaluates to one at its own node. -/
theorem eval_cardinalPolynomial_self {q : ℕ} {nodes : Fin q → ℝ}
    (hnodes : Function.Injective nodes) (i : Fin q) :
    (cardinalPolynomial nodes i).eval (nodes i) = 1 := by
  apply Lagrange.eval_basis_self
  · intro j _ k _ hjk
    exact hnodes hjk
  · simp [cardinalPolynomial]

/-- A cardinal polynomial vanishes at every other node. -/
theorem eval_cardinalPolynomial_of_ne {q : ℕ} {nodes : Fin q → ℝ}
    (i j : Fin q) (hij : i ≠ j) :
    (cardinalPolynomial nodes i).eval (nodes j) = 0 := by
  exact Lagrange.eval_basis_of_ne hij (by simp [cardinalPolynomial])

/-- At distinct `q` nodes, every cardinal polynomial has degree `q - 1`. -/
theorem natDegree_cardinalPolynomial {q : ℕ} {nodes : Fin q → ℝ}
    (hnodes : Function.Injective nodes) (i : Fin q) :
    (cardinalPolynomial nodes i).natDegree = q - 1 := by
  simpa [cardinalPolynomial] using
    Lagrange.natDegree_basis
      (s := (Finset.univ : Finset (Fin q)))
      (fun j _ k _ hjk ↦ hnodes hjk) (Finset.mem_univ i)

/-- Monic division and interpolation give exact quadrature through degree
`2q - 2`.  The annihilation hypothesis is the orthogonality consequence of
the consecutive pair used to construct `v`; it is not a quadrature hypothesis. -/
theorem quadrature_exact_of_monic_annihilates
    {q : ℕ} (hq : 2 ≤ q) (ell : ℝ[X] →ₗ[ℝ] ℝ) {v : ℝ[X]}
    (hmonic : v.Monic) (hvdegree : v.natDegree = q)
    (hannihilates : ∀ g : ℝ[X], g.natDegree ≤ q - 2 → ell (v * g) = 0)
    (nodes : Fin q → ℝ) (hnodes : Function.Injective nodes)
    (hroot : ∀ i, v.eval (nodes i) = 0) {f : ℝ[X]}
    (hfdegree : f.natDegree ≤ 2 * q - 2) :
    ell f = quadrature ell nodes f := by
  classical
  let r : ℝ[X] := f %ₘ v
  let d : ℝ[X] := f /ₘ v
  have hddegree : d.natDegree ≤ q - 2 := by
    dsimp [d]
    rw [natDegree_divByMonic f hmonic, hvdegree]
    lia
  have hsplit : r + v * d = f := by
    simpa only [r, d] using modByMonic_add_div f v
  have hremdegree : r.degree < ↑((Finset.univ : Finset (Fin q)).card) := by
    calc
      r.degree < v.degree := by
        simpa only [r] using degree_modByMonic_lt f hmonic
      _ = ↑q := by rw [degree_eq_natDegree hmonic.ne_zero, hvdegree]
      _ = ↑((Finset.univ : Finset (Fin q)).card) := by simp
  have hinj : Set.InjOn nodes (Finset.univ : Finset (Fin q)) := by
    intro i _ j _ hij
    exact hnodes hij
  have hinterpolate : r = Lagrange.interpolate Finset.univ nodes fun i => r.eval (nodes i) :=
    Lagrange.eq_interpolate hinj hremdegree
  have heval (i : Fin q) : r.eval (nodes i) = f.eval (nodes i) := by
    dsimp [r]
    simpa using
      (eval₂_modByMonic_eq_self_of_root (f := RingHom.id ℝ) (p := f) (q := v)
        (x := nodes i) (by simpa using hroot i))
  calc
    ell f = ell (r + v * d) := congrArg ell hsplit.symm
    _ = ell r + ell (v * d) := ell.map_add _ _
    _ = ell r := by rw [hannihilates d hddegree, add_zero]
    _ = ∑ i : Fin q, r.eval (nodes i) * ell (cardinalPolynomial nodes i) := by
      rw [hinterpolate, Lagrange.interpolate_apply, ell.map_sum]
      simp_rw [← Polynomial.smul_eq_C_mul, ell.map_smul]
      simp only [RingHom.id_apply, smul_eq_mul]
    _ = ∑ i : Fin q, cardinalWeight ell nodes i * f.eval (nodes i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [heval]
      simp only [cardinalWeight]
      ring
    _ = quadrature ell nodes f := rfl

/-- The cardinal weight equals the functional applied to the square of its
cardinal polynomial. -/
theorem cardinalWeight_eq_functional_square
    {q : ℕ} (hq : 2 ≤ q) (ell : ℝ[X] →ₗ[ℝ] ℝ) {v : ℝ[X]}
    (hmonic : v.Monic) (hvdegree : v.natDegree = q)
    (hannihilates : ∀ g : ℝ[X], g.natDegree ≤ q - 2 → ell (v * g) = 0)
    (nodes : Fin q → ℝ) (hnodes : Function.Injective nodes)
    (hroot : ∀ i, v.eval (nodes i) = 0) (i : Fin q) :
    cardinalWeight ell nodes i =
      ell (cardinalPolynomial nodes i * cardinalPolynomial nodes i) := by
  have hdegree :
      (cardinalPolynomial nodes i * cardinalPolynomial nodes i).natDegree ≤ 2 * q - 2 := by
    rw [natDegree_mul (cardinalPolynomial_ne_zero hnodes i)
      (cardinalPolynomial_ne_zero hnodes i), natDegree_cardinalPolynomial hnodes i]
    lia
  have hquadrature := quadrature_exact_of_monic_annihilates hq ell hmonic hvdegree
    hannihilates nodes hnodes hroot hdegree
  have hsingle :
      quadrature ell nodes (cardinalPolynomial nodes i * cardinalPolynomial nodes i) =
        cardinalWeight ell nodes i := by
    rw [quadrature, Finset.sum_eq_single i]
    · simp [eval_cardinalPolynomial_self hnodes]
    · intro j _ hji
      rw [eval_cardinalPolynomial_of_ne i j (Ne.symm hji)]
      ring
    · simp
  rw [hsingle] at hquadrature
  exact hquadrature.symm

/-- Positive functionals give strictly positive cardinal weights. -/
theorem cardinalWeight_pos
    {q : ℕ} (hq : 2 ≤ q) (ell : ℝ[X] →ₗ[ℝ] ℝ)
    (hpositive : ∀ g : ℝ[X], g ≠ 0 → 0 < ell (g * g)) {v : ℝ[X]}
    (hmonic : v.Monic) (hvdegree : v.natDegree = q)
    (hannihilates : ∀ g : ℝ[X], g.natDegree ≤ q - 2 → ell (v * g) = 0)
    (nodes : Fin q → ℝ) (hnodes : Function.Injective nodes)
    (hroot : ∀ i, v.eval (nodes i) = 0) (i : Fin q) :
    0 < cardinalWeight ell nodes i := by
  rw [cardinalWeight_eq_functional_square hq ell hmonic hvdegree hannihilates nodes hnodes hroot]
  exact hpositive _ (cardinalPolynomial_ne_zero hnodes i)

end RealRooted.JacobiDeformation
