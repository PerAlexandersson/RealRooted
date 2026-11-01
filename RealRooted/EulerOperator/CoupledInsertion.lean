module

public import RealRooted.SimpleRoots
import RealRooted.DerivativeRecurrence.QuadraticLagStrict
import RealRooted.Interlacing.OuterDifference
import RealRooted.MaWang.CriticalSign

/-!
# Coupled Euler recurrences

This module eliminates an auxiliary polynomial family from two coupled Euler
derivative recurrences.  The resulting second-order recurrence has a signed
lag term, so the existing critical-sign criterion gives adjacent interlacing.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Euler's derivative step with an arbitrary real coefficient of `X`. -/
@[expose] def realEulerInsertionStep (c a : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (C c + C a * X) * p + (X - X ^ 2) * p.derivative

/-- The constant coefficient of a real-slope Euler insertion step. -/
@[simp] theorem coeff_realEulerInsertionStep_zero (c a : ℝ) (p : ℝ[X]) :
    (realEulerInsertionStep c a p).coeff 0 = c * p.coeff 0 := by
  simp [realEulerInsertionStep]

/-- A real-slope Euler insertion step has the expected coefficient recurrence. -/
@[simp] theorem coeff_realEulerInsertionStep_succ (c a : ℝ) (p : ℝ[X]) (k : ℕ) :
    (realEulerInsertionStep c a p).coeff (k + 1) =
      (c + k + 1) * p.coeff (k + 1) + (a - k) * p.coeff k := by
  rw [realEulerInsertionStep]
  have h := Polynomial.coeff_quadratic_derivative_add_linear_mul_succ
    p (1 : ℝ) (-1) c a k
  rw [show (C c + C a * X) * p + (X - X ^ 2) * p.derivative =
    (C (1 : ℝ) * X + C (-1 : ℝ) * X ^ 2) * p.derivative +
      (C c + C a * X) * p by simp; ring]
  rw [h]
  ring

/-- A slope above the input degree makes a real-slope Euler insertion raise
the degree by one and preserve a positive leading coefficient. -/
theorem realEulerInsertionStep_degree_pos
    {c a : ℝ} {p : ℝ[X]} (ha : (p.natDegree : ℝ) < a)
    (hp : HasPosLeadingCoeff p) :
    (realEulerInsertionStep c a p).natDegree = p.natDegree + 1 ∧
      HasPosLeadingCoeff (realEulerInsertionStep c a p) := by
  have hform : realEulerInsertionStep c a p =
      (C (1 : ℝ) * X + C (-1 : ℝ) * X ^ 2) * p.derivative +
        (C c + C a * X) * p + 0 := by
    simp [realEulerInsertionStep]
    ring
  have htop :
      ((-1 : ℝ) * p.natDegree + a) * p.leadingCoeff ≠ 0 := by
    apply mul_ne_zero
    · linarith
    · exact hp.ne'
  have hpack := Polynomial.natDegree_and_leadingCoeff_quadratic_derivative_add_linear_mul_add
    p 0 (1 : ℝ) (-1) c a (by simp) htop
  rw [hform]
  refine ⟨hpack.1, ?_⟩
  rw [HasPosLeadingCoeff, hpack.2]
  exact mul_pos (by linarith) hp

/-- Nonnegative coefficients are preserved when the constant weight is
nonnegative and the slope is above the input degree. -/
theorem HasNonnegCoeffs.realEulerInsertionStep
    {c a : ℝ} {p : ℝ[X]} (hp : HasNonnegCoeffs p)
    (hc : 0 ≤ c) (ha : (p.natDegree : ℝ) < a) :
    HasNonnegCoeffs (realEulerInsertionStep c a p) := by
  intro k
  cases k with
  | zero =>
      rw [coeff_realEulerInsertionStep_zero]
      exact mul_nonneg hc (hp 0)
  | succ k =>
      rw [coeff_realEulerInsertionStep_succ]
      by_cases hk : k ≤ p.natDegree
      · have hka : (k : ℝ) < a := lt_of_le_of_lt (Nat.cast_le.mpr hk) ha
        exact add_nonneg
          (mul_nonneg (by positivity) (hp (k + 1)))
          (mul_nonneg (by linarith) (hp k))
      · have hpk : p.coeff k = 0 :=
          coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hk)
        have hpks : p.coeff (k + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by lia)
        simp [hpk, hpks]

/-- A positive real-slope Euler insertion propagates split simple negative
roots and gives a coprime successor-degree interlacing pair. -/
theorem realEulerInsertionStep_simple_roots_strictInterl
    {c a : ℝ} {p : ℝ[X]}
    (hc : 0 < c) (ha : (p.natDegree : ℝ) < a)
    (hp_pos : HasPosLeadingCoeff p) (hp_nn : HasNonnegCoeffs p)
    (hp_splits : p.Splits) (hp_simple : HasSimpleRoots p)
    (hp_zero : 0 < p.eval 0) :
    let q := realEulerInsertionStep c a p
    q.natDegree = p.natDegree + 1 ∧ HasPosLeadingCoeff q ∧
      HasNonnegCoeffs q ∧ q.Splits ∧ HasSimpleRoots q ∧
      (∀ r, q.IsRoot r → r < 0) ∧ StrictInterl p q ∧
      (∀ r, p.IsRoot r → ¬ q.IsRoot r) ∧ 0 < q.eval 0 := by
  dsimp only
  obtain ⟨hq_degree, hq_pos⟩ := realEulerInsertionStep_degree_pos ha hp_pos
  have hq_nn := hp_nn.realEulerInsertionStep hc.le ha
  have hp_neg : ∀ r, p.IsRoot r → r < 0 := by
    intro r hr
    have hr_le := isRoot_nonpos_of_hasNonnegCoeffs hp_nn hp_pos.ne_zero hr
    refine lt_of_le_of_ne hr_le fun hre ↦ ?_
    subst r
    rw [Polynomial.IsRoot.def.mp hr] at hp_zero
    exact (lt_irrefl 0 hp_zero).elim
  have hsign : ∀ r, p.IsRoot r →
      (realEulerInsertionStep c a p).eval r * p.derivative.eval r < 0 := by
    intro r hr
    have hrneg := hp_neg r hr
    have hderiv := hp_simple.eval_derivative_ne_zero hr
    simp [realEulerInsertionStep, Polynomial.IsRoot.def.mp hr]
    nlinarith [sq_pos_of_ne_zero hderiv, sq_nonneg r]
  have hstrict := strictInterl_package_of_eval_mul_derivative_neg_succ
    hp_splits hp_pos hq_pos rfl hq_degree hsign
  have hq_zero : 0 < (realEulerInsertionStep c a p).eval 0 := by
    simpa [realEulerInsertionStep] using mul_pos hc hp_zero
  have hq_neg : ∀ r, (realEulerInsertionStep c a p).IsRoot r → r < 0 := by
    intro r hr
    have hr_le := isRoot_nonpos_of_hasNonnegCoeffs hq_nn hq_pos.ne_zero hr
    refine lt_of_le_of_ne hr_le fun hre ↦ ?_
    subst r
    rw [Polynomial.IsRoot.def.mp hr] at hq_zero
    exact (lt_irrefl 0 hq_zero).elim
  exact ⟨hq_degree, hq_pos, hq_nn, hstrict.2.2.1, hstrict.2.2.2.2.1,
    hq_neg, hstrict.1, hstrict.2.2.2.2.2, hq_zero⟩

/-- Two coupled first-order Euler recurrences imply a second-order recurrence
for the second family. -/
theorem coupledEuler_secondOrder
    {P Q : ℕ → ℝ[X]} {c : ℝ} {lam b t : ℕ → ℝ}
    (ht : ∀ n, t n = b n + lam n)
    (hP : ∀ n, P (n + 1) =
      (C (c + lam n) + C (b n) * X) * P n +
        (X - X ^ 2) * (P n).derivative)
    (hQ : ∀ n, Q (n + 1) =
      (C c + C (t n) * X) * P n +
        (X - X ^ 2) * (P n).derivative) :
    ∀ n, Q (n + 2) =
      (C (c + lam n) + C (b n + (t (n + 1) - t n)) * X) * Q (n + 1) +
        (X - X ^ 2) * (Q (n + 1)).derivative +
          C (lam n * (t (n + 1) - t n - 1)) * (X - X ^ 2) * P n := by
  intro n
  rw [hQ (n + 1), hP n, hQ n, ht n]
  simp [derivative_mul, map_add, map_sub, map_mul]
  ring

/-- Under the natural sign and row-invariant hypotheses, the second family in
a coupled Euler recurrence has strict adjacent interlacing. -/
theorem coupledEuler_strictInterl
    {P Q : ℕ → ℝ[X]} {c : ℝ} {lam b t : ℕ → ℝ}
    (ht : ∀ n, t n = b n + lam n)
    (hP : ∀ n, P (n + 1) =
      (C (c + lam n) + C (b n) * X) * P n +
        (X - X ^ 2) * (P n).derivative)
    (hQ : ∀ n, Q (n + 1) =
      (C c + C (t n) * X) * P n +
        (X - X ^ 2) * (P n).derivative)
    (hlam : ∀ n, 0 ≤ lam n)
    (ht_step : ∀ n, 1 ≤ t (n + 1) - t n)
    (hdeg : ∀ n, (Q n).natDegree = n)
    (hPpos : ∀ n, HasPosLeadingCoeff (P n))
    (hQpos : ∀ n, HasPosLeadingCoeff (Q n))
    (hnn : ∀ n, HasNonnegCoeffs (Q n))
    (he0 : ∀ n, 0 < (Q n).eval 0)
    (hcross : ∀ n, StrictInterl (P n) (Q (n + 1)))
    (hcrossNo : ∀ n r, (P n).IsRoot r → ¬ (Q (n + 1)).IsRoot r)
    (hbase : StrictInterl (Q 0) (Q 1)) :
    ∀ n, StrictInterl (Q n) (Q (n + 1)) := by
  intro n
  cases n with
  | zero => exact hbase
  | succ n =>
      have hrec := coupledEuler_secondOrder ht hP hQ n
      have hroots : ∀ k r, (Q k).IsRoot r → r < 0 :=
        derivLag_roots_neg (fun k ↦ hQpos k) hnn he0
      have hsign : ∀ r, (Q (n + 1)).IsRoot r →
          (Q (n + 2)).eval r * (Q (n + 1)).derivative.eval r < 0 := by
        intro r hr
        have hrneg := hroots (n + 1) r hr
        have hprod : 0 < (P n).eval r * (Q (n + 1)).derivative.eval r :=
          (hcross n).eval_mul_derivative_pos_of_right_root_of_no_common
            (hPpos n) (hQpos (n + 1)) (hcrossNo n) hr
        have hderiv_ne : (Q (n + 1)).derivative.eval r ≠ 0 := by
          intro hz
          rw [hz, mul_zero] at hprod
          exact (lt_irrefl 0 hprod).elim
        have hfactor : 0 ≤ lam n * (t (n + 1) - t n - 1) :=
          mul_nonneg (hlam n) (by linarith [ht_step n])
        have heval : (Q (n + 2)).eval r =
            (r - r ^ 2) * ((Q (n + 1)).derivative.eval r +
              lam n * (t (n + 1) - t n - 1) * (P n).eval r) := by
          rw [hrec]
          simp [Polynomial.IsRoot.def.mp hr]
          ring
        rw [heval]
        nlinarith [sq_pos_of_ne_zero hderiv_ne, mul_nonneg hfactor hprod.le,
          sq_nonneg r]
      exact (strictInterl_package_of_eval_mul_derivative_neg_succ
        (hcross n).2.1.2 (hQpos (n + 1)) (hQpos (n + 2))
        (hdeg (n + 1)) (by simpa [Nat.add_assoc] using hdeg (n + 2)) hsign).1

/-- The first coupled recurrence propagates all row invariants needed by the
strict insertion step. -/
private lemma coupledEuler_p_row_data
    {P : ℕ → ℝ[X]} {c : ℝ} {lam b : ℕ → ℝ}
    (hc : 0 < c) (hlam : ∀ n, 0 ≤ lam n)
    (hb : ∀ n : ℕ, (n : ℝ) < b n) (hP0 : P 0 = 1)
    (hP : ∀ n, P (n + 1) =
      (C (c + lam n) + C (b n) * X) * P n +
        (X - X ^ 2) * (P n).derivative) :
    ∀ n, (P n).natDegree = n ∧ HasPosLeadingCoeff (P n) ∧
      HasNonnegCoeffs (P n) ∧ (P n).Splits ∧ HasSimpleRoots (P n) ∧
      0 < (P n).eval 0 ∧ (∀ r, (P n).IsRoot r → r < 0) := by
  intro n
  induction n with
  | zero =>
      rw [hP0]
      refine ⟨by simp, hasPosLeadingCoeff_one, hasNonnegCoeffs_one,
        Polynomial.Splits.one, ?_, by simp, ?_⟩
      · intro r hr
        simp [Polynomial.IsRoot.def] at hr
      · intro r hr
        simp [Polynomial.IsRoot.def] at hr
  | succ n ih =>
      obtain ⟨hdeg, hpos, hnn, hsplits, hsimple, hzero, _⟩ := ih
      have ha : ((P n).natDegree : ℝ) < b n := by rw [hdeg]; exact hb n
      have hpack := realEulerInsertionStep_simple_roots_strictInterl
        (c := c + lam n) (a := b n) (by linarith [hlam n]) ha
        hpos hnn hsplits hsimple hzero
      obtain ⟨hnextdeg, hnextpos, hnextnn, hnextsplits, hnextsimple,
        hnextneg, _, _, hnextzero⟩ := hpack
      have heq : P (n + 1) = realEulerInsertionStep (c + lam n) (b n) (P n) := by
        simpa [realEulerInsertionStep] using hP n
      rw [heq]
      exact ⟨by rw [hnextdeg, hdeg], hnextpos, hnextnn, hnextsplits,
        hnextsimple, hnextzero, hnextneg⟩

/-- Each row of the second family inherits its invariants from the preceding
row of the first family. -/
private lemma coupledEuler_q_row_data
    {P Q : ℕ → ℝ[X]} {c : ℝ} {lam b t : ℕ → ℝ}
    (hc : 0 < c) (hlam : ∀ n, 0 ≤ lam n)
    (hb : ∀ n : ℕ, (n : ℝ) < b n) (ht : ∀ n, t n = b n + lam n)
    (hQ0 : Q 0 = 1)
    (hQ : ∀ n, Q (n + 1) =
      (C c + C (t n) * X) * P n +
        (X - X ^ 2) * (P n).derivative)
    (hPdata : ∀ n, (P n).natDegree = n ∧ HasPosLeadingCoeff (P n) ∧
      HasNonnegCoeffs (P n) ∧ (P n).Splits ∧ HasSimpleRoots (P n) ∧
      0 < (P n).eval 0 ∧ (∀ r, (P n).IsRoot r → r < 0)) :
    ∀ n, (Q n).natDegree = n ∧ HasPosLeadingCoeff (Q n) ∧
      HasNonnegCoeffs (Q n) ∧ (Q n).Splits ∧ HasSimpleRoots (Q n) ∧
      0 < (Q n).eval 0 ∧ (∀ r, (Q n).IsRoot r → r < 0) := by
  intro n
  cases n with
  | zero =>
      rw [hQ0]
      refine ⟨by simp, hasPosLeadingCoeff_one, hasNonnegCoeffs_one,
        Polynomial.Splits.one, ?_, by simp, ?_⟩
      · intro r hr
        simp [Polynomial.IsRoot.def] at hr
      · intro r hr
        simp [Polynomial.IsRoot.def] at hr
  | succ n =>
      obtain ⟨hdeg, hpos, hnn, hsplits, hsimple, hzero, _⟩ := hPdata n
      have ha : ((P n).natDegree : ℝ) < t n := by
        rw [hdeg, ht n]
        linarith [hb n, hlam n]
      have hpack := realEulerInsertionStep_simple_roots_strictInterl
        (c := c) (a := t n) hc ha hpos hnn hsplits hsimple hzero
      obtain ⟨hnextdeg, hnextpos, hnextnn, hnextsplits, hnextsimple,
        hnextneg, _, _, hnextzero⟩ := hpack
      have heq : Q (n + 1) = realEulerInsertionStep c (t n) (P n) := by
        simpa [realEulerInsertionStep] using hQ n
      rw [heq]
      exact ⟨by rw [hnextdeg, hdeg], hnextpos, hnextnn, hnextsplits,
        hnextsimple, hnextzero, hnextneg⟩

/-- The first-family insertion step gives its adjacent strict interlacing. -/
private lemma coupledEuler_p_strictInterl
    {P : ℕ → ℝ[X]} {c : ℝ} {lam b : ℕ → ℝ}
    (hc : 0 < c) (hlam : ∀ n, 0 ≤ lam n)
    (hb : ∀ n : ℕ, (n : ℝ) < b n)
    (hP : ∀ n, P (n + 1) =
      (C (c + lam n) + C (b n) * X) * P n +
        (X - X ^ 2) * (P n).derivative)
    (hPdata : ∀ n, (P n).natDegree = n ∧ HasPosLeadingCoeff (P n) ∧
      HasNonnegCoeffs (P n) ∧ (P n).Splits ∧ HasSimpleRoots (P n) ∧
      0 < (P n).eval 0 ∧ (∀ r, (P n).IsRoot r → r < 0)) :
    ∀ n, StrictInterl (P n) (P (n + 1)) := by
  intro n
  obtain ⟨hdeg, hpos, hnn, hsplits, hsimple, hzero, _⟩ := hPdata n
  have ha : ((P n).natDegree : ℝ) < b n := by rw [hdeg]; exact hb n
  have hpack := realEulerInsertionStep_simple_roots_strictInterl
    (c := c + lam n) (a := b n) (by linarith [hlam n]) ha
    hpos hnn hsplits hsimple hzero
  have heq : P (n + 1) = realEulerInsertionStep (c + lam n) (b n) (P n) := by
    simpa [realEulerInsertionStep] using hP n
  rw [heq]
  exact hpack.2.2.2.2.2.2.1

/-- The second-family insertion step gives cross-family strict interlacing
and excludes common real roots. -/
private lemma coupledEuler_cross_strictInterl
    {P Q : ℕ → ℝ[X]} {c : ℝ} {lam b t : ℕ → ℝ}
    (hc : 0 < c) (hlam : ∀ n, 0 ≤ lam n)
    (hb : ∀ n : ℕ, (n : ℝ) < b n) (ht : ∀ n, t n = b n + lam n)
    (hQ : ∀ n, Q (n + 1) =
      (C c + C (t n) * X) * P n +
        (X - X ^ 2) * (P n).derivative)
    (hPdata : ∀ n, (P n).natDegree = n ∧ HasPosLeadingCoeff (P n) ∧
      HasNonnegCoeffs (P n) ∧ (P n).Splits ∧ HasSimpleRoots (P n) ∧
      0 < (P n).eval 0 ∧ (∀ r, (P n).IsRoot r → r < 0)) :
    ∀ n, StrictInterl (P n) (Q (n + 1)) ∧
      ∀ r, (P n).IsRoot r → ¬ (Q (n + 1)).IsRoot r := by
  intro n
  obtain ⟨hdeg, hpos, hnn, hsplits, hsimple, hzero, _⟩ := hPdata n
  have ha : ((P n).natDegree : ℝ) < t n := by
    rw [hdeg, ht n]
    linarith [hb n, hlam n]
  have hpack := realEulerInsertionStep_simple_roots_strictInterl
    (c := c) (a := t n) hc ha hpos hnn hsplits hsimple hzero
  have heq : Q (n + 1) = realEulerInsertionStep c (t n) (P n) := by
    simpa [realEulerInsertionStep] using hQ n
  rw [heq]
  exact ⟨hpack.2.2.2.2.2.2.1, hpack.2.2.2.2.2.2.2.1⟩

/-- Coupled positive Euler recurrences have degree-indexed simple negative
rows; both families interlace adjacently, and each `P n` interlaces
`Q (n + 1)`. -/
theorem coupledEuler_simple_roots_strictInterl
    {P Q : ℕ → ℝ[X]} {c : ℝ} {lam b t : ℕ → ℝ}
    (hc : 0 < c) (hlam : ∀ n, 0 ≤ lam n)
    (hb : ∀ n : ℕ, (n : ℝ) < b n)
    (ht : ∀ n, t n = b n + lam n)
    (ht_step : ∀ n, 1 ≤ t (n + 1) - t n)
    (hP0 : P 0 = 1) (hQ0 : Q 0 = 1)
    (hP : ∀ n, P (n + 1) =
      (C (c + lam n) + C (b n) * X) * P n +
        (X - X ^ 2) * (P n).derivative)
    (hQ : ∀ n, Q (n + 1) =
      (C c + C (t n) * X) * P n +
        (X - X ^ 2) * (P n).derivative) :
    (∀ n, (P n).natDegree = n ∧ HasPosLeadingCoeff (P n) ∧
      HasNonnegCoeffs (P n) ∧ (P n).Splits ∧ HasSimpleRoots (P n) ∧
      (∀ r, (P n).IsRoot r → r < 0)) ∧
    (∀ n, (Q n).natDegree = n ∧ HasPosLeadingCoeff (Q n) ∧
      HasNonnegCoeffs (Q n) ∧ (Q n).Splits ∧ HasSimpleRoots (Q n) ∧
      (∀ r, (Q n).IsRoot r → r < 0)) ∧
    (∀ n, StrictInterl (P n) (P (n + 1))) ∧
    (∀ n, StrictInterl (P n) (Q (n + 1))) ∧
    (∀ n, StrictInterl (Q n) (Q (n + 1))) := by
  have hPdata := coupledEuler_p_row_data hc hlam hb hP0 hP
  have hQdata := coupledEuler_q_row_data hc hlam hb ht hQ0 hQ hPdata
  have hPadj := coupledEuler_p_strictInterl hc hlam hb hP hPdata
  have hcrossData := coupledEuler_cross_strictInterl hc hlam hb ht hQ hPdata
  have hcross : ∀ n, StrictInterl (P n) (Q (n + 1)) := fun n ↦ (hcrossData n).1
  have hcrossNo : ∀ n r, (P n).IsRoot r → ¬ (Q (n + 1)).IsRoot r :=
    fun n ↦ (hcrossData n).2
  have hQadj : ∀ n, StrictInterl (Q n) (Q (n + 1)) := by
    apply coupledEuler_strictInterl ht hP hQ hlam ht_step
      (fun n ↦ (hQdata n).1) (fun n ↦ (hPdata n).2.1)
      (fun n ↦ (hQdata n).2.1) (fun n ↦ (hQdata n).2.2.1)
      (fun n ↦ (hQdata n).2.2.2.2.2.1) hcross hcrossNo
    simpa [hP0, hQ0] using hcross 0
  refine ⟨?_, ?_, hPadj, hcross, hQadj⟩
  · intro n
    obtain ⟨hdeg, hpos, hnn, hsplits, hsimple, _, hneg⟩ := hPdata n
    exact ⟨hdeg, hpos, hnn, hsplits, hsimple, hneg⟩
  · intro n
    obtain ⟨hdeg, hpos, hnn, hsplits, hsimple, _, hneg⟩ := hQdata n
    exact ⟨hdeg, hpos, hnn, hsplits, hsimple, hneg⟩

end RealRooted
