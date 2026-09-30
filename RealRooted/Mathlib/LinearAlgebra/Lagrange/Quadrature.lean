import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic

/-!
# Finite exact quadrature and collocation in Lagrange coordinates

A linear functional `L` on `ℝ[X]` which annihilates the monic nodal polynomial
of `q` distinct nodes times every polynomial of degree at most `q - 2` is
exactly a weighted sum of point evaluations through degree `2q - 2`
(`Lagrange.quadrature_exact`).  The weights are the values of `L` on the
Lagrange cardinal polynomials, and they are positive when `L` is positive on
squares of low degree (`Lagrange.quadratureWeight_pos`).  No integral
representation of `L` is needed.

The second half records the matrix `Lagrange.collocationMatrix D x` of a linear
polynomial operator `D` in Lagrange evaluation coordinates.  Exact quadrature
turns self-adjointness of a degree-preserving `D` into weighted symmetry of its
collocation matrix, and a positive diagonal similarity then gives an honest
symmetric matrix.  We also record the first and second derivatives of a
cardinal polynomial at the other nodes.
-/

open Finset Polynomial

noncomputable section

namespace Lagrange

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
    have hnode : n.eval (x i) = 0 :=
      Lagrange.eval_nodal_at_node (s := Finset.univ) (v := x) (mem_univ i)
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
  have hbne : b ≠ 0 :=
    Lagrange.basis_ne_zero hx.injOn (mem_univ i)
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

/-- Exact quadrature isolates a single weight when one factor is a Lagrange
cardinal polynomial. -/
theorem quadratureWeight_mul_eval {q : ℕ} (hq : 2 ≤ q)
    (L : ℝ[X] →ₗ[ℝ] ℝ) (x : Fin q → ℝ) (hx : Function.Injective x)
    (horth : ∀ g : ℝ[X], g.natDegree ≤ q - 2 →
      L (Lagrange.nodal Finset.univ x * g) = 0)
    (p : ℝ[X]) (hp : p.natDegree < q) (i : Fin q) :
    quadratureWeight L x i * p.eval (x i) =
      L (Lagrange.basis Finset.univ x i * p) := by
  let b := Lagrange.basis Finset.univ x i
  have hbdeg : b.natDegree = q - 1 := by
    simpa [b] using Lagrange.natDegree_basis hx.injOn (mem_univ i)
  have hproddeg : (b * p).natDegree ≤ 2 * q - 2 := by
    calc
      (b * p).natDegree ≤ b.natDegree + p.natDegree := natDegree_mul_le
      _ ≤ (q - 1) + (q - 1) := by rw [hbdeg]; lia
      _ = 2 * q - 2 := by lia
  rw [quadrature_exact hq L x hx horth hproddeg]
  symm
  calc
    (∑ j : Fin q, quadratureWeight L x j * (b * p).eval (x j)) =
        quadratureWeight L x i * (b * p).eval (x i) := by
      apply Fintype.sum_eq_single i
      intro j hji
      rw [eval_mul, show b.eval (x j) = 0 by
        exact Lagrange.eval_basis_of_ne hji.symm (mem_univ j), zero_mul, mul_zero]
    _ = quadratureWeight L x i * p.eval (x i) := by
      rw [eval_mul, show b.eval (x i) = 1 by
        exact Lagrange.eval_basis_self hx.injOn (mem_univ i)]
      ring

/-- The leading coefficient of a Lagrange cardinal polynomial is the inverse
derivative of the monic nodal polynomial at its node. -/
theorem leadingCoeff_basis_eq_inv_eval_derivative_nodal {q : ℕ}
    (x : Fin q → ℝ) (hx : Function.Injective x) (i : Fin q) :
    (Lagrange.basis Finset.univ x i).leadingCoeff =
      ((Lagrange.nodal Finset.univ x).derivative.eval (x i))⁻¹ := by
  rw [Lagrange.leadingCoeff_basis hx.injOn (mem_univ i)]
  rw [← Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ i)]
  simp [Lagrange.nodalWeight, Finset.prod_inv_distrib]

/-- Multiplying a cardinal polynomial by its missing nodal factor recovers
the monic nodal polynomial, scaled by the inverse nodal derivative. -/
theorem X_sub_C_mul_basis {q : ℕ}
    (x : Fin q → ℝ) (i : Fin q) :
    (X - C (x i)) * Lagrange.basis Finset.univ x i =
      C ((Lagrange.nodal Finset.univ x).derivative.eval (x i))⁻¹ *
        Lagrange.nodal Finset.univ x := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (mem_univ i),
    ← Lagrange.nodal_erase_eq_nodal_div (mem_univ i),
    Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ i),
    Lagrange.nodal_eq_mul_nodal_erase (mem_univ i)]
  ring

/-- Multiplication by `X` in cardinal coordinates is its nodal value plus a
multiple of the monic nodal polynomial. -/
theorem X_mul_basis {q : ℕ}
    (x : Fin q → ℝ) (i : Fin q) :
    X * Lagrange.basis Finset.univ x i =
      C (x i) * Lagrange.basis Finset.univ x i +
        C ((Lagrange.nodal Finset.univ x).derivative.eval (x i))⁻¹ *
          Lagrange.nodal Finset.univ x := by
  calc
    X * Lagrange.basis Finset.univ x i =
        C (x i) * Lagrange.basis Finset.univ x i +
          (X - C (x i)) * Lagrange.basis Finset.univ x i := by ring
    _ = _ := by rw [X_sub_C_mul_basis]

/-- Distinct nodes make the derivative of their monic nodal polynomial
nonzero at every node. -/
theorem eval_derivative_nodal_ne_zero {q : ℕ}
    (x : Fin q → ℝ) (hx : Function.Injective x) (i : Fin q) :
    (Lagrange.nodal Finset.univ x).derivative.eval (x i) ≠ 0 := by
  have hweight := Lagrange.nodalWeight_ne_zero hx.injOn (mem_univ i)
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ i)] at hweight
  simpa using hweight

/-- Matrix of a polynomial endomorphism in Lagrange evaluation coordinates. -/
def collocationMatrix {q : ℕ} (D : ℝ[X] →ₗ[ℝ] ℝ[X])
    (x : Fin q → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => (D (Lagrange.basis Finset.univ x j)).eval (x i)

/-- Exact quadrature isolates one row of the collocation matrix when paired
with a Lagrange cardinal polynomial. -/
theorem quadrature_basis_mul_apply {q : ℕ} (hq : 2 ≤ q)
    (L : ℝ[X] →ₗ[ℝ] ℝ) (D : ℝ[X] →ₗ[ℝ] ℝ[X])
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (horth : ∀ g : ℝ[X], g.natDegree ≤ q - 2 →
      L (Lagrange.nodal Finset.univ x * g) = 0)
    (hD : ∀ p : ℝ[X], p.natDegree < q → (D p).natDegree < q)
    (i j : Fin q) :
    L (Lagrange.basis Finset.univ x i *
        D (Lagrange.basis Finset.univ x j)) =
      quadratureWeight L x i * collocationMatrix D x i j := by
  let bi := Lagrange.basis Finset.univ x i
  let bj := Lagrange.basis Finset.univ x j
  have hbideg : bi.natDegree = q - 1 := by
    simpa [bi] using Lagrange.natDegree_basis hx.injOn (mem_univ i)
  have hbjdeg : bj.natDegree = q - 1 := by
    simpa [bj] using Lagrange.natDegree_basis hx.injOn (mem_univ j)
  have hDjdeg : (D bj).natDegree < q := hD bj (by lia)
  have hproddeg : (bi * D bj).natDegree ≤ 2 * q - 2 := by
    calc
      (bi * D bj).natDegree ≤ bi.natDegree + (D bj).natDegree := natDegree_mul_le
      _ ≤ (q - 1) + (q - 1) := by rw [hbideg]; lia
      _ = 2 * q - 2 := by lia
  rw [quadrature_exact hq L x hx horth hproddeg]
  calc
    (∑ k : Fin q,
        quadratureWeight L x k * (bi * D bj).eval (x k)) =
        quadratureWeight L x i * (bi * D bj).eval (x i) := by
      apply Fintype.sum_eq_single i
      intro k hki
      rw [eval_mul, show bi.eval (x k) = 0 by
        exact Lagrange.eval_basis_of_ne hki.symm (mem_univ k), zero_mul, mul_zero]
    _ = quadratureWeight L x i * collocationMatrix D x i j := by
      rw [eval_mul, show bi.eval (x i) = 1 by
        exact Lagrange.eval_basis_self hx.injOn (mem_univ i)]
      simp [bj, collocationMatrix]

/-- Self-adjointness of the polynomial operator becomes weighted symmetry of
its collocation matrix. -/
theorem quadratureWeight_mul_collocationMatrix_comm {q : ℕ} (hq : 2 ≤ q)
    (L : ℝ[X] →ₗ[ℝ] ℝ) (D : ℝ[X] →ₗ[ℝ] ℝ[X])
    (x : Fin q → ℝ) (hx : Function.Injective x)
    (horth : ∀ g : ℝ[X], g.natDegree ≤ q - 2 →
      L (Lagrange.nodal Finset.univ x * g) = 0)
    (hD : ∀ p : ℝ[X], p.natDegree < q → (D p).natDegree < q)
    (hadj : ∀ p r : ℝ[X], L (p * D r) = L (D p * r))
    (i j : Fin q) :
    quadratureWeight L x i * collocationMatrix D x i j =
      quadratureWeight L x j * collocationMatrix D x j i := by
  rw [← quadrature_basis_mul_apply hq L D x hx horth hD i j,
    ← quadrature_basis_mul_apply hq L D x hx horth hD j i,
    hadj, mul_comm]

/-- Positive diagonal similarity which removes the quadrature weights from a
weighted-self-adjoint collocation matrix. -/
def symmetrizedCollocationMatrix {q : ℕ} (L : ℝ[X] →ₗ[ℝ] ℝ)
    (D : ℝ[X] →ₗ[ℝ] ℝ[X]) (x : Fin q → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => Real.sqrt (quadratureWeight L x i) /
    Real.sqrt (quadratureWeight L x j) * collocationMatrix D x i j

theorem symmetrizedCollocationMatrix_isSymm {q : ℕ}
    (L : ℝ[X] →ₗ[ℝ] ℝ) (D : ℝ[X] →ₗ[ℝ] ℝ[X])
    (x : Fin q → ℝ)
    (hweight : ∀ i, 0 < quadratureWeight L x i)
    (hweighted : ∀ i j,
      quadratureWeight L x i * collocationMatrix D x i j =
        quadratureWeight L x j * collocationMatrix D x j i) :
    (symmetrizedCollocationMatrix L D x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  have hi := hweight i
  have hj := hweight j
  have hsqrti : Real.sqrt (quadratureWeight L x i) ≠ 0 :=
    (Real.sqrt_pos.2 hi).ne'
  have hsqrtj : Real.sqrt (quadratureWeight L x j) ≠ 0 :=
    (Real.sqrt_pos.2 hj).ne'
  rw [symmetrizedCollocationMatrix, symmetrizedCollocationMatrix]
  field_simp [hsqrti, hsqrtj]
  rw [Real.sq_sqrt hi.le, Real.sq_sqrt hj.le]
  exact (hweighted i j).symm

/-- Evaluation vectors intertwine a polynomial operator with its collocation
matrix on degrees below the number of nodes. -/
theorem collocationMatrix_mulVec_eval {q : ℕ}
    (D : ℝ[X] →ₗ[ℝ] ℝ[X]) (x : Fin q → ℝ)
    (hx : Function.Injective x) (p : ℝ[X]) (hp : p.natDegree < q) :
    (collocationMatrix D x).mulVec (fun j => p.eval (x j)) =
      fun i => (D p).eval (x i) := by
  funext i
  have hpdeg : p.degree < (#(Finset.univ : Finset (Fin q)) : WithBot ℕ) := by
    apply lt_of_le_of_lt degree_le_natDegree
    simpa using hp
  have hinterp := Lagrange.eq_interpolate hx.injOn
    (f := p) hpdeg
  have heval := congrArg (fun r : ℝ[X] => (D r).eval (x i)) hinterp
  rw [Lagrange.interpolate_apply, map_sum, eval_finsetSum] at heval
  rw [Matrix.mulVec]
  change (∑ j, (D (Lagrange.basis Finset.univ x j)).eval (x i) *
    p.eval (x j)) = (D p).eval (x i)
  rw [heval]
  apply Finset.sum_congr rfl
  intro j _
  rw [← smul_eq_C_mul, map_smul]
  simp only [eval_smul, smul_eq_mul]
  ring

/-- At a different node, the first derivative of a Lagrange cardinal
polynomial is the quotient of the two nodal derivatives. -/
theorem eval_derivative_basis_of_ne {q : ℕ}
    (x : Fin q → ℝ) (hx : Function.Injective x)
    {i j : Fin q} (hij : i ≠ j) :
    (Lagrange.basis Finset.univ x j).derivative.eval (x i) =
      (Lagrange.nodal Finset.univ x).derivative.eval (x i) /
        ((x i - x j) *
          (Lagrange.nodal Finset.univ x).derivative.eval (x j)) := by
  let v := Lagrange.nodal Finset.univ x
  let r := Lagrange.nodal (Finset.univ.erase j) x
  let b := Lagrange.basis Finset.univ x j
  let di := v.derivative.eval (x i)
  let dj := v.derivative.eval (x j)
  have hsub : x i - x j ≠ 0 := sub_ne_zero.mpr (fun h ↦ hij (hx h))
  have hdj : dj ≠ 0 := eval_derivative_nodal_ne_zero x hx j
  have hri : r.eval (x i) = 0 := by
    apply Lagrange.eval_nodal_at_node
    exact Finset.mem_erase.mpr ⟨hij, mem_univ i⟩
  have hv : v = (X - C (x j)) * r :=
    Lagrange.nodal_eq_mul_nodal_erase (mem_univ j)
  have hdi : di = (x i - x j) * r.derivative.eval (x i) := by
    dsimp only [di]
    rw [hv, derivative_mul]
    simp only [eval_add, eval_mul, derivative_sub, derivative_X,
      derivative_C, sub_zero, eval_sub, eval_X, eval_C, hri,
      one_mul, zero_add]
  have hb : b = C dj⁻¹ * r := by
    rw [show b = C (Lagrange.nodalWeight Finset.univ x j) * r by
      dsimp only [b, r]
      rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (mem_univ j),
        ← Lagrange.nodal_erase_eq_nodal_div (mem_univ j)]]
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ j)]
  rw [show (Lagrange.basis Finset.univ x j).derivative.eval (x i) =
      dj⁻¹ * r.derivative.eval (x i) by
    change b.derivative.eval (x i) = _
    rw [hb, derivative_C_mul, eval_mul, eval_C]]
  change dj⁻¹ * r.derivative.eval (x i) = di / ((x i - x j) * dj)
  field_simp [hsub, hdj]
  linarith [hdi]

/-- At a different node, the second cardinal derivative is determined by the
first and second derivatives of the nodal polynomial. -/
theorem eval_derivative_derivative_basis_of_ne {q : ℕ}
    (x : Fin q → ℝ) (hx : Function.Injective x)
    {i j : Fin q} (hij : i ≠ j) :
    (Lagrange.basis Finset.univ x j).derivative.derivative.eval (x i) =
      ((Lagrange.nodal Finset.univ x).derivative.derivative.eval (x i) -
          2 * (Lagrange.nodal Finset.univ x).derivative.eval (x i) /
            (x i - x j)) /
        ((x i - x j) *
          (Lagrange.nodal Finset.univ x).derivative.eval (x j)) := by
  let v := Lagrange.nodal Finset.univ x
  let r := Lagrange.nodal (Finset.univ.erase j) x
  let b := Lagrange.basis Finset.univ x j
  let di := v.derivative.eval (x i)
  let dj := v.derivative.eval (x j)
  have hsub : x i - x j ≠ 0 := sub_ne_zero.mpr (fun h ↦ hij (hx h))
  have hdj : dj ≠ 0 := eval_derivative_nodal_ne_zero x hx j
  have hri : r.eval (x i) = 0 := by
    apply Lagrange.eval_nodal_at_node
    exact Finset.mem_erase.mpr ⟨hij, mem_univ i⟩
  have hv : v = (X - C (x j)) * r :=
    Lagrange.nodal_eq_mul_nodal_erase (mem_univ j)
  have hdi : di = (x i - x j) * r.derivative.eval (x i) := by
    dsimp only [di]
    rw [hv, derivative_mul]
    simp only [eval_add, eval_mul, derivative_sub, derivative_X,
      derivative_C, sub_zero, eval_sub, eval_X, eval_C, hri,
      one_mul, zero_add]
  have hddi : v.derivative.derivative.eval (x i) =
      2 * r.derivative.eval (x i) +
        (x i - x j) * r.derivative.derivative.eval (x i) := by
    rw [hv, derivative_mul, derivative_add, derivative_mul, derivative_mul]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero,
      derivative_one, zero_mul, zero_add, eval_add, eval_mul, eval_one,
      eval_sub, eval_X, eval_C]
    ring
  have hsecond : r.derivative.derivative.eval (x i) * (x i - x j) ^ 2 =
      v.derivative.derivative.eval (x i) * (x i - x j) - 2 * di := by
    linear_combination -(x i - x j) * hddi + 2 * hdi
  have hb : b = C dj⁻¹ * r := by
    rw [show b = C (Lagrange.nodalWeight Finset.univ x j) * r by
      dsimp only [b, r]
      rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (mem_univ j),
        ← Lagrange.nodal_erase_eq_nodal_div (mem_univ j)]]
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ j)]
  rw [show (Lagrange.basis Finset.univ x j).derivative.derivative.eval (x i) =
      dj⁻¹ * r.derivative.derivative.eval (x i) by
    change b.derivative.derivative.eval (x i) = _
    rw [hb, derivative_C_mul, derivative_C_mul, eval_mul, eval_C]]
  change dj⁻¹ * r.derivative.derivative.eval (x i) =
    (v.derivative.derivative.eval (x i) - 2 * di / (x i - x j)) /
      ((x i - x j) * dj)
  field_simp [hsub, hdj]
  linarith [hsecond]

end Lagrange
