module

public import RealRooted.DistinctValues.Marked
public import RealRooted.Mathlib.Algebra.MvPolynomial.Diagonal
public import RealRooted.PFPolynomial
public import RealRooted.EulerOperator
import RealRooted.AffineLineRestriction
import RealRooted.Multiaffine.AffineLineRestriction
public import Mathlib.Data.Multiset.Sort
import RealRooted.ReciprocalShift.ProperPosition
import RealRooted.EulerOperator.Polar
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Diagonal distinct-value polynomials

Setting every value marker equal to `X` in the marked recurrence gives
`T_{h,a} f = (a + h X) f + X (1-X) f'`. Real-rootedness is derived from
multivariate stability, and coefficient nonnegativity locates the roots in
`(-∞,0]`. The case `a = 1` gives the distinct-value polynomials of a multiset
of bounds, including the staircase Eulerian and square partial-transformation
models. Source: unpublished manuscript, ferrers-dist, Sections 2 and 4;
chordal-dist, Section 1; RealRooted issue #2640.
-/

@[expose] public section

open Polynomial
open scoped BigOperators

namespace RealRooted.DistinctValues

noncomputable section

/-- The binomial moment operator, with height `h` and null weight `a`. -/
def binomialStep (h : ℕ) (a : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (C a + C (h : ℝ) * X) * p + X * (1 - X) * p.derivative

/-- At null weight one, the binomial step is the Euler/polar-theta step. -/
theorem binomialStep_one (h : ℕ) (p : ℝ[X]) :
    binomialStep h 1 p = thetaPlusOne p + X * polarTheta h p := by
  simp only [binomialStep, thetaPlusOne, polarTheta, theta, map_one]
  ring

/-- Diagonal restriction of a nonnegative multivariate polynomial has nonnegative coefficients. -/
theorem diagonal_hasNonnegCoeffs {σ : Type*} {P : MvPolynomial σ ℝ}
    (hnn : P.HasNonnegCoeffs) : HasNonnegCoeffs (MvPolynomial.diagonal P) := by
  classical
  rw [MvPolynomial.as_sum P]
  simp only [MvPolynomial.diagonal, map_sum]
  apply hasNonnegCoeffs_finsetSum
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial]
  apply (hasNonnegCoeffs_C (hnn d)).mul
  exact hasNonnegCoeffs_finsetProd d.support _ fun i _ => hasNonnegCoeffs_X.pow _

/-- A zero-aware real-stable polynomial has a split diagonal. -/
theorem diagonal_splits {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : MvRealStableOrZero P) : (MvPolynomial.diagonal P).Splits := by
  rcases hP with rfl | hP
  · simp
  · have h := (hP.realAffineLineRestriction_splits_ne_zero
      (fun _ => 0) (fun _ => 1) (fun _ => zero_lt_one)).1
    simpa only [realAffineLineRestriction, map_zero, map_one, one_mul, zero_add,
      MvPolynomial.diagonal] using h

/-- The full marked step restricts to the binomial moment operator on the diagonal. -/
theorem diagonal_fullStep {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℝ}
    (hma : P.IsMultiaffine) (a : ℝ) :
    MvPolynomial.diagonal (fullStep a P) =
      binomialStep (Fintype.card σ) a (MvPolynomial.diagonal P) := by
  classical
  have hsection (i : σ) : MvPolynomial.specializeAt i 1 P =
      P + (1 - MvPolynomial.X i) * MvPolynomial.pderiv i P := by
    rw [RealRooted.MvPolynomial.IsMultiaffine.specializeAt_one_eq_specializeZero_add_pderiv
      hma i]
    have h := hma.eq_specializeZero_add_X_mul_pderiv i
    linear_combination -h
  simp only [fullStep, MvPolynomial.diagonal_add, MvPolynomial.diagonal_mul,
    MvPolynomial.diagonal_C, MvPolynomial.diagonal_sum, MvPolynomial.diagonal_X]
  simp_rw [hsection, MvPolynomial.diagonal_add, MvPolynomial.diagonal_mul,
    MvPolynomial.diagonal_sub, MvPolynomial.diagonal_one, MvPolynomial.diagonal_X]
  simp only [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    ← Finset.mul_sum, ← Finset.mul_sum, ← MvPolynomial.derivative_diagonal]
  simp only [binomialStep, nsmul_eq_mul, map_natCast]
  ring

/-- A supported finite-height marked step restricts to the binomial operator. -/
theorem diagonal_step {P : MvPolynomial ℕ ℝ} {h : ℕ}
    (hma : P.IsMultiaffine) (hvars : P.vars ⊆ Finset.range h) (a : ℝ) :
    MvPolynomial.diagonal (step h a P) = binomialStep h a (MvPolynomial.diagonal P) := by
  obtain ⟨Q, hQ⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range P
    Fin.val Fin.val_injective (by
      intro i hi
      exact ⟨⟨i, Finset.mem_range.mp (hvars hi)⟩, rfl⟩)
  subst P
  rw [step_rename, MvPolynomial.diagonal_rename, MvPolynomial.diagonal_rename,
    diagonal_fullStep (hma.of_rename Fin.val_injective), Fintype.card_fin]

/-- The distinct-value polynomial is the diagonal of its marked refinement. -/
def polynomial (columns : List (ℕ × ℝ)) : ℝ[X] :=
  MvPolynomial.diagonal (markedPolynomial columns)

/-- The empty list of columns has distinct-value polynomial one. -/
@[simp] theorem polynomial_nil : polynomial [] = 1 := by simp [polynomial]

/-- The diagonal distinct-value polynomial is PF: it splits and all its roots are nonpositive. -/
theorem polynomial_isPFPolynomial (columns : List (ℕ × ℝ))
    (hsorted : columns.Pairwise (fun c d => c.1 ≤ d.1))
    (ha : ∀ c ∈ columns, 0 ≤ c.2) : IsPFPolynomial (polynomial columns) := by
  obtain ⟨_, hnn, hstable, _⟩ := markedPolynomial_properties columns hsorted ha
  exact IsPFPolynomial.of_realRooted_nonneg (diagonal_hasNonnegCoeffs hnn)
    (diagonal_splits hstable)

/-- Increasing-height distinct-value polynomials split over the reals. -/
theorem polynomial_splits (columns : List (ℕ × ℝ))
    (hsorted : columns.Pairwise (fun c d => c.1 ≤ d.1))
    (ha : ∀ c ∈ columns, 0 ≤ c.2) : (polynomial columns).Splits :=
  (polynomial_isPFPolynomial columns hsorted ha).splits

/-- Every root of an increasing-height distinct-value polynomial is nonpositive. -/
theorem polynomial_roots_nonpos (columns : List (ℕ × ℝ))
    (hsorted : columns.Pairwise (fun c d => c.1 ≤ d.1))
    (ha : ∀ c ∈ columns, 0 ≤ c.2) :
    ∀ r ∈ (polynomial columns).roots, r ≤ 0 :=
  (polynomial_isPFPolynomial columns hsorted ha).roots_nonpos

/-- Appending an admissible column gives the scalar derivative recurrence. -/
theorem polynomial_append_singleton (columns : List (ℕ × ℝ)) (c : ℕ × ℝ)
    (hsorted : columns.Pairwise (fun c d => c.1 ≤ d.1))
    (ha : ∀ d ∈ columns, 0 ≤ d.2) (hbound : ∀ d ∈ columns, d.1 ≤ c.1) :
    polynomial (columns ++ [c]) = binomialStep c.1 c.2 (polynomial columns) := by
  obtain ⟨hma, _, _, hvars⟩ := markedPolynomial_properties columns hsorted ha
  exact (congrArg MvPolynomial.diagonal (markedPolynomial_append_singleton columns c)).trans
    (diagonal_step hma (hvars c.1 hbound) c.2)

/-- Null weight one gives the distinct-value polynomial for a list of bounds. -/
def distinctPolynomial (heights : List ℕ) : ℝ[X] :=
  polynomial (heights.map fun h => (h, 1))

/-- Distinct-value polynomials for increasing bounds are PF. -/
theorem distinctPolynomial_isPFPolynomial (heights : List ℕ)
    (hsorted : heights.Pairwise (· ≤ ·)) : IsPFPolynomial (distinctPolynomial heights) := by
  apply polynomial_isPFPolynomial
  · simpa only [List.pairwise_map] using hsorted
  · intro c hc
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hc
    exact zero_le_one

/-- The distinct-value polynomial of a multiset uses its increasing ordering of bounds. -/
def multisetPolynomial (bounds : Multiset ℕ) : ℝ[X] :=
  distinctPolynomial (bounds.sort (· ≤ ·))

/-- The distinct-value polynomial of every multiset of bounds is PF. -/
theorem multisetPolynomial_isPFPolynomial (bounds : Multiset ℕ) :
    IsPFPolynomial (multisetPolynomial bounds) :=
  distinctPolynomial_isPFPolynomial _ (Multiset.pairwise_sort _ _)

/-- The distinct-value polynomial of every multiset of bounds splits over the reals. -/
theorem multisetPolynomial_splits (bounds : Multiset ℕ) :
    (multisetPolynomial bounds).Splits := (multisetPolynomial_isPFPolynomial bounds).splits

/-- All roots of the distinct-value polynomial of a multiset of bounds are nonpositive. -/
theorem multisetPolynomial_roots_nonpos (bounds : Multiset ℕ) :
    ∀ r ∈ (multisetPolynomial bounds).roots, r ≤ 0 :=
  (multisetPolynomial_isPFPolynomial bounds).roots_nonpos

/-- Reflect the Euler derivative comparison to obtain the weak polar comparison. -/
private theorem interl_polarTheta_self {p : ℝ[X]} (hp : IsPFPolynomial p)
    {h : ℕ} (hd : p.natDegree ≤ h) : Interl (polarTheta h p) p := by
  let q := reciprocalShift h p
  have hq : IsPFPolynomial q := hp.reciprocalShift hd
  have hqd : q.natDegree ≤ h := by
    exact (natDegree_reflect_le).trans (max_le le_rfl hd)
  have htheta : Interl q (theta q) := by
    exact interl_mul_X_of_interl hq.derivative_interl_self
      hq.hasNonnegCoeffs.derivative hq.hasNonnegCoeffs
  have hswap := reciprocalShift_reverses_interl hq (theta_preserves_pf hq)
    hqd ((natDegree_theta_le q).trans hqd) htheta
  change Interl (reciprocalShift h (theta (reciprocalShift h p)))
    (reciprocalShift h (reciprocalShift h p)) at hswap
  rw [← polarTheta_eq_reciprocalShift_theta_reciprocalShift h p hd] at hswap
  simpa only [reciprocalShift, reflect_reflect] using hswap

/-- A degree-bounded PF input precedes its nonnegative binomial step. -/
theorem interl_binomialStep {p : ℝ[X]} (hp : IsPFPolynomial p)
    {h : ℕ} (hd : p.natDegree ≤ h) {a : ℝ} (ha : 0 ≤ a) :
    Interl p (binomialStep h a p) := by
  have hnn := hp.hasNonnegCoeffs
  have htheta : Interl p (theta p) :=
    interl_mul_X_of_interl hp.derivative_interl_self hnn.derivative hnn
  have hpolar : Interl p (X * polarTheta h p) :=
    interl_mul_X_of_interl (interl_polarTheta_self hp hd) (hnn.polarTheta hd) hnn
  have hsum := interl_add_right_of_common_left_of_nonneg
    (interl_add_right_of_common_left_of_nonneg
      (Interl.C_mul_right_of_nonneg hp.interl_self ha) htheta
      (hasNonnegCoeffs_C_mul ha hnn) hnn.derivative.X_mul)
    hpolar ((hasNonnegCoeffs_C_mul ha hnn).add hnn.derivative.X_mul)
    (hnn.polarTheta hd).X_mul
  have heq : C a * p + theta p + X * polarTheta h p = binomialStep h a p := by
    simp only [binomialStep, theta, polarTheta]
    ring
  rwa [heq] at hsum

/-- Identifying all markers cannot increase the total degree. -/
private theorem natDegree_diagonal_le_totalDegree {σ : Type*} (P : MvPolynomial σ ℝ) :
    (MvPolynomial.diagonal P).natDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P]
  simp only [MvPolynomial.diagonal, map_sum]
  apply natDegree_sum_le_of_forall_le
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial]
  apply (natDegree_C_mul_le _ _).trans
  calc
    (d.prod fun _ n => (X : ℝ[X]) ^ n).natDegree ≤
        ∑ i ∈ d.support, ((X : ℝ[X]) ^ d i).natDegree := natDegree_prod_le _ _
    _ = d.sum (fun _ n => n) := by simp [Finsupp.sum]
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hd

/-- A common height bound is a degree bound for the diagonal polynomial. -/
theorem polynomial_natDegree_le (columns : List (ℕ × ℝ))
    (hsorted : columns.Pairwise (fun c d => c.1 ≤ d.1))
    (ha : ∀ c ∈ columns, 0 ≤ c.2) {h : ℕ} (hbound : ∀ c ∈ columns, c.1 ≤ h) :
    (polynomial columns).natDegree ≤ h := by
  obtain ⟨hma, _, _, hvars⟩ := markedPolynomial_properties columns hsorted ha
  obtain ⟨Q, hQ⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    (markedPolynomial columns) Fin.val Fin.val_injective (by
      intro i hi
      exact ⟨⟨i, Finset.mem_range.mp (hvars h hbound hi)⟩, rfl⟩)
  have hmaQ : Q.IsMultiaffine := by
    apply MvPolynomial.IsMultiaffine.of_rename (f := Fin.val) _ Fin.val_injective
    rwa [hQ]
  unfold polynomial
  rw [← hQ, MvPolynomial.diagonal_rename]
  exact (natDegree_diagonal_le_totalDegree Q).trans
    (by simpa using totalDegree_le_card hmaQ)

/-- Consecutive increasing-height prefixes interlace, including zero-weight boundaries. -/
theorem polynomial_interl_append_singleton (columns : List (ℕ × ℝ)) (c : ℕ × ℝ)
    (hsorted : columns.Pairwise (fun c d => c.1 ≤ d.1))
    (ha : ∀ d ∈ columns, 0 ≤ d.2) (hc : 0 ≤ c.2)
    (hbound : ∀ d ∈ columns, d.1 ≤ c.1) :
    Interl (polynomial columns) (polynomial (columns ++ [c])) := by
  rw [polynomial_append_singleton columns c hsorted ha hbound]
  exact interl_binomialStep (polynomial_isPFPolynomial columns hsorted ha)
    (polynomial_natDegree_le columns hsorted ha hbound) hc

/-- The diagonal polynomial is nonzero when each column has nonzero total weight. -/
theorem polynomial_ne_zero (columns : List (ℕ × ℝ))
    (h : ∀ c ∈ columns, c.2 + (c.1 : ℝ) ≠ 0) : polynomial columns ≠ 0 := by
  intro hzero
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) hzero
  simp only [polynomial, MvPolynomial.eval_diagonal, eval_zero,
    eval_one_markedPolynomial] at heval
  have hn : (columns.map fun c => c.2 + (c.1 : ℝ)).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hx
    obtain ⟨c, hc, heq⟩ := List.mem_map.mp hx
    exact h c hc heq
  exact hn heval

/-- With positive total column weights, consecutive prefixes satisfy nonzero proper position. -/
theorem polynomial_strictInterl_append_singleton (columns : List (ℕ × ℝ)) (c : ℕ × ℝ)
    (hsorted : columns.Pairwise (fun c d => c.1 ≤ d.1))
    (ha : ∀ d ∈ columns, 0 ≤ d.2) (hc : 0 ≤ c.2)
    (hbound : ∀ d ∈ columns, d.1 ≤ c.1)
    (hprev : ∀ d ∈ columns, d.2 + (d.1 : ℝ) ≠ 0) (hnext : c.2 + (c.1 : ℝ) ≠ 0) :
    StrictInterl (polynomial columns) (polynomial (columns ++ [c])) := by
  apply (polynomial_interl_append_singleton columns c hsorted ha hc hbound).toStrictInterl_of_ne
    (polynomial_ne_zero columns hprev)
  apply polynomial_ne_zero
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact hprev d hd
  · have hdc : d = c := by simpa using hd
    simpa [hdc] using hnext

end

end RealRooted.DistinctValues
