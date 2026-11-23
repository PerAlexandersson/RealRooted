module

public import RealRooted.PFPolynomial
public import RealRooted.Touchard
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.Derivative.Algebra

/-!
# Poisson moment polynomials

The commuting operators `S_a f = (a + X) f + X f'` define
`P_ℓ(t) = E ∏ (ℓ_i + Y)` for `Y ~ Poisson(t)`. Nonnegative offsets give
nonnegative coefficients and only real nonpositive roots. Zero offsets
recover the Touchard polynomials; constant offsets give the `r`-Bell family.
For complements of clique coronas these supply the non-monomial factor of
the sigma polynomial. Source: unpublished manuscript, ferrers-dist,
Sections 4 and 5; RealRooted issue #2640.

The root theorem follows from the library's derivative interlacing and Wagner
`X` transport, with the input as common left interleaver of the three summands.
-/

@[expose] public section

open Polynomial

namespace RealRooted.DistinctValues

noncomputable section

/-- The Poisson moment operator with null offset `a`. -/
def poissonStep (a : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (C a + X) * p + X * p.derivative

/-- Nonnegative offsets preserve nonnegative coefficients under the Poisson step. -/
theorem poissonStep_hasNonnegCoeffs {p : ℝ[X]} (hp : HasNonnegCoeffs p)
    {a : ℝ} (ha : 0 ≤ a) : HasNonnegCoeffs (poissonStep a p) :=
  (((hasNonnegCoeffs_C ha).add hasNonnegCoeffs_X).mul hp).add hp.derivative.X_mul

/-- A PF polynomial precedes its Poisson step, including zero and constant inputs. -/
theorem interl_poissonStep {p : ℝ[X]} (hp : IsPFPolynomial p)
    {a : ℝ} (ha : 0 ≤ a) : Interl p (poissonStep a p) := by
  have hnn := hp.hasNonnegCoeffs
  have htheta : Interl p (X * p.derivative) :=
    interl_mul_X_of_interl hp.derivative_interl_self hnn.derivative hnn
  have hX : Interl p (X * p) := interl_mul_X_of_interl hp.interl_self hnn hnn
  have hsum := interl_add_right_of_common_left_of_nonneg
    (interl_add_right_of_common_left_of_nonneg
      (Interl.C_mul_right_of_nonneg hp.interl_self ha) hX
      (hasNonnegCoeffs_C_mul ha hnn) hnn.X_mul)
    htheta ((hasNonnegCoeffs_C_mul ha hnn).add hnn.X_mul) hnn.derivative.X_mul
  simpa only [poissonStep, add_mul] using hsum

/-- Poisson moment steps preserve the PF cone for all nonnegative real offsets. -/
theorem poissonStep_isPFPolynomial {p : ℝ[X]} (hp : IsPFPolynomial p)
    {a : ℝ} (ha : 0 ≤ a) : IsPFPolynomial (poissonStep a p) := by
  by_cases hp0 : p = 0
  · subst p
    simpa [poissonStep] using IsPFPolynomial.zero
  · have hnn := poissonStep_hasNonnegCoeffs hp.hasNonnegCoeffs ha
    rcases interl_poissonStep hp ha with hzero | hzero | hstrict
    · exact (hp0 hzero).elim
    · rw [hzero]
      exact IsPFPolynomial.zero
    · exact IsPFPolynomial.of_realRooted_nonneg hnn hstrict.2.1.2

/-- Poisson operators with arbitrary real offsets commute. -/
theorem poissonStep_commute (a b : ℝ) (p : ℝ[X]) :
    poissonStep a (poissonStep b p) = poissonStep b (poissonStep a p) := by
  simp only [poissonStep, derivative_add, derivative_mul, derivative_C, derivative_X,
    zero_add, one_mul]
  ring

/-- The Poisson moment polynomial, defined by iterating its commuting steps. -/
def poissonPolynomial (offsets : List ℝ) : ℝ[X] := offsets.foldr poissonStep 1

/-- The empty Poisson product is one. -/
@[simp] theorem poissonPolynomial_nil : poissonPolynomial [] = 1 := rfl

/-- Adjoining an offset applies the corresponding Poisson step. -/
@[simp] theorem poissonPolynomial_cons (a : ℝ) (offsets : List ℝ) :
    poissonPolynomial (a :: offsets) = poissonStep a (poissonPolynomial offsets) := rfl

/-- Poisson moment polynomials with nonnegative offsets are PF. -/
theorem poissonPolynomial_isPFPolynomial (offsets : List ℝ)
    (ha : ∀ a ∈ offsets, 0 ≤ a) : IsPFPolynomial (poissonPolynomial offsets) := by
  induction offsets with
  | nil => exact IsPFPolynomial.one
  | cons a offsets ih =>
      exact poissonStep_isPFPolynomial (ih fun b hb => ha b (by simp [hb])) (ha a (by simp))

/-- Poisson moment polynomials with nonnegative offsets split over the reals. -/
theorem poissonPolynomial_splits (offsets : List ℝ)
    (ha : ∀ a ∈ offsets, 0 ≤ a) : (poissonPolynomial offsets).Splits :=
  (poissonPolynomial_isPFPolynomial offsets ha).splits

/-- Every root of a nonnegative-offset Poisson moment polynomial is nonpositive. -/
theorem poissonPolynomial_roots_nonpos (offsets : List ℝ)
    (ha : ∀ a ∈ offsets, 0 ≤ a) :
    ∀ r ∈ (poissonPolynomial offsets).roots, r ≤ 0 :=
  (poissonPolynomial_isPFPolynomial offsets ha).roots_nonpos

/-- Zero offsets recover the existing Touchard polynomial sequence. -/
theorem poissonPolynomial_replicate_zero (n : ℕ) :
    poissonPolynomial (List.replicate n 0) = touchard n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, poissonPolynomial_cons, ih, poissonStep,
        map_zero, zero_add, touchard_succ]

/-- The Poisson moment polynomial is independent of the order of its offsets. -/
theorem poissonPolynomial_eq_of_perm {l k : List ℝ} (h : l.Perm k) :
    poissonPolynomial l = poissonPolynomial k := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [poissonPolynomial_cons, ih]
  | swap a b l => exact poissonStep_commute b a (poissonPolynomial l)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

end

end RealRooted.DistinctValues
