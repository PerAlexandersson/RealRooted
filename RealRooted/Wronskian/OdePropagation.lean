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

/-- A polynomial with nonnegative coefficients, positive leading coefficient and positive
constant term has only negative roots. -/
private lemma roots_neg_of_hasNonnegCoeffs_of_coeff_zero_pos {p : ℝ[X]}
    (hnonneg : HasNonnegCoeffs p) (hpos : HasPosLeadingCoeff p) (hconst : 0 < p.coeff 0) :
    ∀ r, p.IsRoot r → r < 0 := by
  intro r hr
  have hrle := isRoot_nonpos_of_hasNonnegCoeffs hnonneg hpos.ne_zero hr
  have hrne : r ≠ 0 := by
    rintro rfl
    rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero] at hr
    linarith
  exact lt_of_le_of_ne hrle hrne

/-- A nonzero solution of a second-order ODE has simple roots at the points where the leading
coefficient `a` does not vanish. -/
private lemma hasSimpleRoots_of_ode {p a b c : ℝ[X]} (hp : p ≠ 0)
    (hode : a * p.derivative.derivative + b * p.derivative + c * p = 0)
    (ha : ∀ r, p.IsRoot r → a.eval r ≠ 0) :
    HasSimpleRoots p := by
  intro r hr
  have hder : p.derivative.eval r ≠ 0 := eval_derivative_ne_zero_of_ode hp hode hr (ha r hr)
  have hmult_pos : 0 < p.rootMultiplicity r := (rootMultiplicity_pos hp).2 hr
  have hmult_le : p.rootMultiplicity r ≤ 1 := by
    by_contra hnot
    have hlarge : 1 < p.rootMultiplicity r := by lia
    exact hder ((one_lt_rootMultiplicity_iff_isRoot hp).1 hlarge).2
  lia

/-- Solving the scaled first-order recurrence for the successor row. -/
private lemma eq_mul_add_mul_derivative_of_C_mul_eq {f g p q : ℝ[X]} {K : ℝ} (hK : K ≠ 0)
    (hrec : C K * g = p * f + q * f.derivative) :
    g = (C K⁻¹ * p) * f + (C K⁻¹ * q) * f.derivative := by
  calc
    g = C K⁻¹ * (C K * g) := by
      rw [← mul_assoc, ← C_mul]
      simp [hK]
    _ = C K⁻¹ * (p * f + q * f.derivative) := by rw [hrec]
    _ = (C K⁻¹ * p) * f + (C K⁻¹ * q) * f.derivative := by ring

/-- One step of the propagation: the ODE discriminant makes the derivative coefficient of the
recurrence negative at every root of `f`, so `f` strictly interlaces its successor `g`. -/
private lemma strictInterl_of_ode_step {f g a b c p q : ℝ[X]} {K : ℝ} (hK : 0 < K)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) (hsplits : f.Splits)
    (hsimple : HasSimpleRoots f)
    (hode : a * f.derivative.derivative + b * f.derivative + c * f = 0)
    (ha : ∀ r, f.IsRoot r → a.eval r ≠ 0)
    (hdisc : ∀ r, f.IsRoot r → 0 ≤ q.eval r →
      0 < (b ^ 2 + 4 * a.derivative * b - 4 * a * (b.derivative + c)).eval r)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hrec' : g = (C K⁻¹ * p) * f + (C K⁻¹ * q) * f.derivative) :
    StrictInterl f g := by
  have hqneg : ∀ r, f.IsRoot r → q.eval r < 0 := by
    intro r hr
    apply lt_of_not_ge
    intro hq
    have hpositive := hdisc r hr hq
    have hnonpositive := ode_discriminant_eval_nonpos_of_isRoot
      hf_pos.ne_zero hsplits hode hr (ha r hr)
    linarith
  have hvneg : ∀ r, f.IsRoot r → (C K⁻¹ * q).eval r < 0 := by
    intro r hr
    simp only [eval_mul, eval_C]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hK) (hqneg r hr)
  by_cases hdegn : f.natDegree = 0
  · rw [hrec']
    exact MaWang.strictInterl_derivative_of_nonpos_of_splits hsplits
      (by rw [← hrec', hdeg, hdegn]; simp) (by rw [← hrec', hdeg])
      (by rw [← hrec']; exact hg_pos) hf_pos (fun r hr => (hvneg r hr).le)
  · exact
      (strictInterl_and_hasSimpleRoots_of_interlaces_eval_mul_neg_succ hsplits hf_pos
        hg_pos (Nat.one_le_iff_ne_zero.mpr hdegn) hdeg hsimple hrec' hvneg).1

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
  have hroots : ∀ n r, (F n).IsRoot r → r < 0 := fun n =>
    roots_neg_of_hasNonnegCoeffs_of_coeff_zero_pos (hnonneg n) (hpos n) (hconst n)
  have hsimple : ∀ n, HasSimpleRoots (F n) := fun n =>
    hasSimpleRoots_of_ode (hpos n).ne_zero (hode n) fun r hr ↦ ha n r (hroots n r hr)
  have hstep : ∀ n, (F n).Splits → StrictInterl (F n) (F (n + 1)) := fun n hsplits =>
    strictInterl_of_ode_step (hK n) (hpos n) (hpos (n + 1)) hsplits (hsimple n)
      (hode n) (fun r hr ↦ ha n r (hroots n r hr))
      (fun r hr ↦ hdisc n r (hroots n r hr))
      (by rw [hdegree (n + 1), hdegree n]; lia)
      (eq_mul_add_mul_derivative_of_C_mul_eq (hK n).ne' (hrec n))
  have hsplits : ∀ n, (F n).Splits := by
    intro n
    induction n with
    | zero => exact hsplits₀
    | succ n ih => exact (hstep n ih).2.1.2
  exact ⟨fun n => ⟨hsplits n, hsimple n, hroots n⟩, fun n => hstep n (hsplits n)⟩

end RealRooted
