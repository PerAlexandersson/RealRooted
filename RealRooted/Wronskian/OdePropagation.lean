module

public import RealRooted.Basic.Coefficients
public import RealRooted.SimpleRoots
import RealRooted.MaWang.DerivativeStep
import RealRooted.MaWang.StrictStep
import RealRooted.Wronskian.OdeRootBound

/-!
# Propagation of second-order ODEs and real-rootedness

An intertwining identity propagates a second-order differential equation through
a first-order differential recurrence.  The ODE discriminant then forces the
derivative coefficient in the recurrence to be negative at every root, so the
strict Ma--Wang criterion propagates simple negative roots and interlacing.
-/

public section

open Polynomial

namespace RealRooted

/-- A second-order polynomial ODE propagates through a first-order recurrence
when the two differential operators satisfy the displayed intertwining identity. -/
theorem second_order_ode_family_of_recurrence
    (F : ℕ → ℝ[X]) (a b c p q : ℕ → ℝ[X]) (K : ℕ → ℝ)
    (U : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X])
    (hK : ∀ n, K n ≠ 0)
    (hrec : ∀ n,
      C (K n) * F (n + 1) = p n * F n + q n * (F n).derivative)
    (hbase :
      a 0 * (F 0).derivative.derivative + b 0 * (F 0).derivative + c 0 * F 0 = 0)
    (hintertwine : ∀ n g,
      a (n + 1) * (p n * g + q n * g.derivative).derivative.derivative +
          b (n + 1) * (p n * g + q n * g.derivative).derivative +
          c (n + 1) * (p n * g + q n * g.derivative) =
        U n (a n * g.derivative.derivative + b n * g.derivative + c n * g)) :
    ∀ n, a n * (F n).derivative.derivative + b n * (F n).derivative + c n * F n = 0 := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
      have hinter := hintertwine n (F n)
      rw [ih, map_zero] at hinter
      have hrec₀ := hrec n
      have hrec₁ := congrArg derivative hrec₀
      have hrec₂ := congrArg derivative hrec₁
      simp only [derivative_mul, derivative_C, zero_mul, zero_add] at hrec₁ hrec₂
      have hscaled :
          C (K n) *
              (a (n + 1) * (F (n + 1)).derivative.derivative +
                b (n + 1) * (F (n + 1)).derivative + c (n + 1) * F (n + 1)) = 0 := by
        linear_combination
          a (n + 1) * hrec₂ + b (n + 1) * hrec₁ + c (n + 1) * hrec₀ + hinter
      exact (mul_eq_zero.mp hscaled).resolve_left (C_ne_zero.mpr (hK n))

/-- A positive-coefficient family satisfying an intertwined second-order ODE
and a degree-raising first-order recurrence has simple negative roots, and each
row strictly interlaces its successor. -/
theorem splits_simple_roots_neg_and_strictInterl_succ_of_ode_recurrence
    (F : ℕ → ℝ[X]) (a b c p q : ℕ → ℝ[X]) (K : ℕ → ℝ) (d : ℕ)
    (U : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X])
    (hdegree : ∀ n, (F n).natDegree = d + n)
    (hpos : ∀ n, HasPosLeadingCoeff (F n))
    (hnonneg : ∀ n, HasNonnegCoeffs (F n))
    (hconst : ∀ n, 0 < (F n).coeff 0)
    (hsplits₀ : (F 0).Splits)
    (hK : ∀ n, 0 < K n)
    (hrec : ∀ n,
      C (K n) * F (n + 1) = p n * F n + q n * (F n).derivative)
    (hode₀ :
      a 0 * (F 0).derivative.derivative + b 0 * (F 0).derivative + c 0 * F 0 = 0)
    (hintertwine : ∀ n g,
      a (n + 1) * (p n * g + q n * g.derivative).derivative.derivative +
          b (n + 1) * (p n * g + q n * g.derivative).derivative +
          c (n + 1) * (p n * g + q n * g.derivative) =
        U n (a n * g.derivative.derivative + b n * g.derivative + c n * g))
    (ha : ∀ n x, x < 0 → (a n).eval x ≠ 0)
    (hdisc : ∀ n x, x < 0 → 0 ≤ (q n).eval x →
      0 < (b n ^ 2 + 4 * (a n).derivative * b n -
        4 * a n * ((b n).derivative + c n)).eval x) :
    (∀ n, (F n).Splits ∧ HasSimpleRoots (F n) ∧
      ∀ r, (F n).IsRoot r → r < 0) ∧
      ∀ n, StrictInterl (F n) (F (n + 1)) := by
  have hode := second_order_ode_family_of_recurrence F a b c p q K U
    (fun n => (hK n).ne') hrec hode₀ hintertwine
  have hroots : ∀ n r, (F n).IsRoot r → r < 0 := by
    intro n r hr
    have hrle := isRoot_nonpos_of_hasNonnegCoeffs (hnonneg n) (hpos n).ne_zero hr
    have hrne : r ≠ 0 := by
      rintro rfl
      rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero] at hr
      linarith [hconst n]
    exact lt_of_le_of_ne hrle hrne
  have hsimple : ∀ n, HasSimpleRoots (F n) := by
    intro n r hr
    have hder : (F n).derivative.eval r ≠ 0 :=
      eval_derivative_ne_zero_of_ode (hpos n).ne_zero (hode n) hr
        (ha n r (hroots n r hr))
    have hmult_pos : 0 < (F n).rootMultiplicity r :=
      (rootMultiplicity_pos (hpos n).ne_zero).2 hr
    have hmult_le : (F n).rootMultiplicity r ≤ 1 := by
      by_contra hnot
      have hlarge : 1 < (F n).rootMultiplicity r := by lia
      have hderroot := (one_lt_rootMultiplicity_iff_isRoot (hpos n).ne_zero).1 hlarge
      exact hder hderroot.2
    lia
  have hrec' : ∀ n,
      F (n + 1) =
        (C ((K n)⁻¹) * p n) * F n +
          (C ((K n)⁻¹) * q n) * (F n).derivative := by
    intro n
    calc
      F (n + 1) = C ((K n)⁻¹) * (C (K n) * F (n + 1)) := by
        rw [← mul_assoc, ← C_mul]
        simp [(hK n).ne']
      _ = C ((K n)⁻¹) *
          (p n * F n + q n * (F n).derivative) := by rw [hrec n]
      _ = (C ((K n)⁻¹) * p n) * F n +
          (C ((K n)⁻¹) * q n) * (F n).derivative := by ring
  have hstep : ∀ n, (F n).Splits → StrictInterl (F n) (F (n + 1)) := by
    intro n hsplits
    have hqneg : ∀ r, (F n).IsRoot r → (q n).eval r < 0 := by
      intro r hr
      apply lt_of_not_ge
      intro hq
      have hpositive := hdisc n r (hroots n r hr) hq
      have hnonpositive := ode_discriminant_eval_nonpos_of_isRoot
        (hpos n).ne_zero hsplits (hode n) hr (ha n r (hroots n r hr))
      linarith
    have hdeg : (F (n + 1)).natDegree = (F n).natDegree + 1 := by
      rw [hdegree (n + 1), hdegree n]
      lia
    have hvneg : ∀ r, (F n).IsRoot r →
        (C ((K n)⁻¹) * q n).eval r < 0 := by
      intro r hr
      simp only [eval_mul, eval_C]
      exact mul_neg_of_pos_of_neg (inv_pos.mpr (hK n)) (hqneg r hr)
    by_cases hdegn : (F n).natDegree = 0
    · rw [hrec' n]
      exact MaWang.strictInterl_derivative_of_nonpos_of_splits hsplits
        (by rw [← hrec' n, hdeg, hdegn]; simp) (by rw [← hrec' n, hdeg])
        (by rw [← hrec' n]; exact hpos (n + 1)) (hpos n) (fun r hr => (hvneg r hr).le)
    · exact
        (strictInterl_and_hasSimpleRoots_of_interlaces_eval_mul_neg_succ hsplits (hpos n)
          (hpos (n + 1)) (Nat.one_le_iff_ne_zero.mpr hdegn) hdeg (hsimple n) (hrec' n) hvneg).1
  have hsplits : ∀ n, (F n).Splits := by
    intro n
    induction n with
    | zero => exact hsplits₀
    | succ n ih => exact (hstep n ih).2.1.2
  constructor
  · exact fun n => ⟨hsplits n, hsimple n, hroots n⟩
  · exact fun n => hstep n (hsplits n)

end RealRooted
