module

import RealRooted.DerivativeRecurrence.EndpointWindow
public import RealRooted.MaWang.DerivativeStep
import RealRooted.DerivativeRecurrence.Degree
import RealRooted.Interlacing.Residue
import RealRooted.IteratedDerivativeShift
import RealRooted.Linear
import RealRooted.Mathlib.Algebra.Polynomial.FieldDivision
import RealRooted.WagnerRightSum.Sign
public import Mathlib.Algebra.Order.Floor.Div

/-!
# Endpoint multiplicity for Ma--Wang steps

We prove the endpoint criterion for the differential step
`((a X + b) p) + X (X + c) p'`.  The proof factors the full multiplicity at
`-c`, cancels that common factor from the Ma--Wang interlacing relation, and
uses the endpoint-sign criterion on the remaining pair.

The argument follows Ma and Wang, *q-Eulerian polynomials and polynomials with
only real zeros*, Theorem 2 and Corollary 3
([arXiv:math/0611826](https://arxiv.org/abs/math/0611826)).
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.MaWang

/-- The quadratic differential step used in the endpoint-multiplicity criterion. -/
def endpointStep (c a b : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (C a * X + C b) * p + X * (X + C c) * p.derivative

private lemma natDegree_affine_le (a b : ℝ) :
    (C a * X + C b : ℝ[X]).natDegree ≤ 1 := by
  apply natDegree_add_le_of_degree_le
  · calc
      (C a * X : ℝ[X]).natDegree ≤ (C a).natDegree + X.natDegree := natDegree_mul_le
      _ ≤ 0 + 1 := Nat.add_le_add (by rw [natDegree_C]) (by simp)
      _ = 1 := by simp
  · rw [natDegree_C]
    simp

private lemma natDegree_endpointQuadratic_le (c : ℝ) :
    (X * (X + C c) : ℝ[X]).natDegree ≤ 2 := by
  calc
    (X * (X + C c) : ℝ[X]).natDegree ≤ X.natDegree + (X + C c).natDegree :=
      natDegree_mul_le
    _ ≤ 1 + 1 := Nat.add_le_add (by simp)
      (natDegree_add_le_of_degree_le (by simp) (by rw [natDegree_C]; simp))
    _ = 2 := by simp

private lemma endpointStep_degree_le (c a b : ℝ) (p : ℝ[X]) :
    (endpointStep c a b p).natDegree ≤ p.natDegree + 1 := by
  apply natDegree_add_le_of_degree_le
  · exact natDegree_mul_iterate_derivative_le (d := 1) (j := 0)
      (natDegree_affine_le a b) le_rfl
  · exact natDegree_mul_iterate_derivative_le (d := 1) (j := 1)
      (natDegree_endpointQuadratic_le c) le_rfl

private lemma endpointStep_coeff_succ (c a b : ℝ) (p : ℝ[X]) :
    (endpointStep c a b p).coeff (p.natDegree + 1) =
      (a + p.natDegree) * p.leadingCoeff := by
  rw [endpointStep, coeff_add]
  have h0 := coeff_mul_iterate_derivative_of_natDegree_le
    (A := C a * X + C b) (p := p) (d := 1) (j := 0) (D := p.natDegree)
    (natDegree_affine_le a b) le_rfl
  have h1 := coeff_mul_iterate_derivative_of_natDegree_le
    (A := X * (X + C c)) (p := p) (d := 1) (j := 1) (D := p.natDegree)
    (natDegree_endpointQuadratic_le c) le_rfl
  simp only [Function.iterate_zero, id_eq, Nat.descFactorial_zero, Nat.cast_one,
    mul_one, Function.iterate_one, Nat.descFactorial_one] at h0 h1
  rw [h0, h1, leadingCoeff]
  simp
  ring

/-- A positive affine coefficient makes the endpoint step grow by one degree and
preserves positivity of the leading coefficient. -/
theorem endpointStep_natDegree_eq_and_leadingCoeff_pos {c a b : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) :
    (endpointStep c a b p).natDegree = p.natDegree + 1 ∧
      HasPosLeadingCoeff (endpointStep c a b p) := by
  have hcoeff : 0 < (endpointStep c a b p).coeff (p.natDegree + 1) := by
    rw [endpointStep_coeff_succ]
    exact mul_pos (by positivity) hp
  have hdeg := natDegree_eq_of_le_of_coeff_ne_zero
    (endpointStep_degree_le c a b p) hcoeff.ne'
  refine ⟨hdeg, ?_⟩
  rw [HasPosLeadingCoeff, leadingCoeff, hdeg]
  exact hcoeff

/-- Evaluation of the endpoint step at zero. -/
@[simp] theorem endpointStep_eval_zero (c a b : ℝ) (p : ℝ[X]) :
    (endpointStep c a b p).eval 0 = b * p.eval 0 := by
  simp [endpointStep]

/-- Under the Ma--Wang root-sign hypothesis supplied by `[-c,0)`, the input is
in proper position with its endpoint step. -/
theorem endpointStep_strictInterl {c a b : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, -c ≤ r ∧ r < 0) :
    StrictInterl p (endpointStep c a b p) := by
  have hpack := endpointStep_natDegree_eq_and_leadingCoeff_pos (c := c) (b := b) ha hp
  apply strictInterl_derivative_of_nonpos_of_splits hs
  · change p.natDegree ≤ (endpointStep c a b p).natDegree
    rw [hpack.1]
    lia
  · change (endpointStep c a b p).natDegree ≤ p.natDegree + 1
    rw [hpack.1]
  · exact hpack.2
  · exact hp
  · intro r hr
    have hrmem := (mem_roots hp.ne_zero).mpr hr
    have hb := hroots r hrmem
    simp only [eval_mul, eval_add, eval_X, eval_C]
    nlinarith

private lemma endpointStep_interlaces {c a b : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, -c ≤ r ∧ r < 0) :
    Interlaces p (endpointStep c a b p) := by
  exact (endpointStep_strictInterl ha hp hs hroots).toInterlaces
    (endpointStep_natDegree_eq_and_leadingCoeff_pos (c := c) (b := b) ha hp).1.symm

/-- Every root of the endpoint step is strictly negative. -/
theorem endpointStep_roots_lt_zero {c a b : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hb : 0 < b) (hp : HasPosLeadingCoeff p)
    (hs : p.Splits) (hroots : ∀ r ∈ p.roots, -c ≤ r ∧ r < 0) :
    ∀ r ∈ (endpointStep c a b p).roots, r < 0 := by
  have hinter := endpointStep_interlaces (b := b) ha hp hs hroots
  apply (roots_lt_iff_eval_pos_of_interlaces hinter
    (endpointStep_natDegree_eq_and_leadingCoeff_pos (c := c) (b := b) ha hp).2
    (fun r hr => (hroots r hr).2)).mpr
  rw [endpointStep_eval_zero]
  exact mul_pos hb (eval_pos_of_all_roots_lt hp.ne_zero hs hp fun r hr => (hroots r hr).2)

private lemma endpointFactor_eq (c : ℝ) :
    (X + C c : ℝ[X]) = X - C (-c) := by
  simp

private lemma endpointStep_factorization (c a b : ℝ) (p q : ℝ[X]) (m : ℕ)
    (hpq : (X + C c) ^ m * q = p) :
    endpointStep c a b p = (X + C c) ^ m *
      (((C a + C (m : ℝ)) * X + C b) * q + X * (X + C c) * q.derivative) := by
  rw [endpointStep, ← hpq, endpointFactor_eq]
  cases m with
  | zero => simp
  | succ m =>
      rw [derivative_mul, derivative_X_sub_C_pow]
      simp only [Nat.succ_sub_one, Nat.cast_succ]
      ring

private lemma endpointCofactor_eval (c a b : ℝ) (q : ℝ[X]) (m : ℕ) :
    (((C a + C (m : ℝ)) * X + C b) * q +
      X * (X + C c) * q.derivative).eval (-c) =
      (b - c * (a + m)) * q.eval (-c) := by
  simp only [eval_add, eval_mul, eval_C, eval_X]
  ring

private lemma roots_gt_of_endpoint_factor {c : ℝ} {p q : ℝ[X]} {m : ℕ}
    (hq : q ≠ 0) (hfactor : (X + C c) ^ m * q = p)
    (hqeval : q.eval (-c) ≠ 0) (hroots : ∀ r ∈ p.roots, -c ≤ r) :
    ∀ r ∈ q.roots, -c < r := by
  intro r hr
  have hrq : q.IsRoot r := (mem_roots hq).mp hr
  have hrp : r ∈ p.roots := by
    have hlinear : (X + C c : ℝ[X]) ≠ 0 := by
      rw [endpointFactor_eq]
      exact X_sub_C_ne_zero (-c)
    rw [← hfactor, roots_mul (mul_ne_zero (pow_ne_zero _ hlinear) hq), Multiset.mem_add]
    exact Or.inr hr
  exact lt_of_le_of_ne (hroots r hrp) fun heq => hqeval (by simpa [heq] using hrq)

private lemma signed_eval_pos_at_endpoint {c : ℝ} {q : ℝ[X]}
    (hq : q.Splits) (hqpos : HasPosLeadingCoeff q)
    (hroots : ∀ r ∈ q.roots, -c < r) :
    0 < (-1 : ℝ) ^ q.natDegree * q.eval (-c) := by
  rw [Polynomial.Splits.eval_eq_prod_roots hq (-c),
    ← Polynomial.splits_iff_card_roots.mp hq, mul_left_comm,
    show q.roots.card = (q.roots.map (-c - ·)).card by simp,
    ← Multiset.prod_map_neg]
  refine mul_pos hqpos (Multiset.prod_pos fun y hy => ?_)
  obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hy
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hs
  linarith [hroots r hr]

/-- The endpoint multiplicity stays fixed except at the affine threshold, where
it increases by exactly one. -/
theorem endpointStep_rootMultiplicity {c a b : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, -c ≤ r ∧ r < 0) :
    (endpointStep c a b p).rootMultiplicity (-c) =
      if b = c * (a + p.rootMultiplicity (-c))
      then p.rootMultiplicity (-c) + 1 else p.rootMultiplicity (-c) := by
  let m := p.rootMultiplicity (-c)
  let q := p /ₘ (X + C c) ^ m
  let H := ((C a + C (m : ℝ)) * X + C b) * q +
    X * (X + C c) * q.derivative
  have hfactor : (X + C c) ^ m * q = p := by
    dsimp [q, m]
    rw [endpointFactor_eq]
    exact p.pow_mul_divByMonic_rootMultiplicity_eq (-c)
  have hqeval : q.eval (-c) ≠ 0 := by
    dsimp [q, m]
    rw [endpointFactor_eq]
    exact eval_divByMonic_pow_rootMultiplicity_ne_zero (-c) hp.ne_zero
  have hq : q ≠ 0 := fun hq => hqeval (by rw [hq, eval_zero])
  have hFfactor : endpointStep c a b p = (X + C c) ^ m * H := by
    dsimp [H]
    exact endpointStep_factorization c a b p q m hfactor
  have hFne : endpointStep c a b p ≠ 0 :=
    (endpointStep_natDegree_eq_and_leadingCoeff_pos (c := c) (b := b) ha hp).2.ne_zero
  have hH : H ≠ 0 := by
    intro hzero
    apply hFne
    rw [hFfactor, hzero, mul_zero]
  have hmult : (endpointStep c a b p).rootMultiplicity (-c) =
      m + H.rootMultiplicity (-c) := by
    rw [hFfactor, endpointFactor_eq,
      rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) hH),
      rootMultiplicity_X_sub_C_pow]
  have hinter := endpointStep_strictInterl (b := b) ha hp hs hroots
  have hupper : (endpointStep c a b p).rootMultiplicity (-c) ≤ m + 1 := by
    have hbound := (hinter.rootMultiplicity_bounds (-c)).2
    dsimp [m]
    lia
  have hHeval : H.eval (-c) = (b - c * (a + m)) * q.eval (-c) := by
    dsimp [H]
    exact endpointCofactor_eval c a b q m
  split_ifs with heq
  · have hHroot : H.IsRoot (-c) := by
      rw [Polynomial.IsRoot.def, hHeval, heq, sub_self, zero_mul]
    have hpos : 0 < H.rootMultiplicity (-c) := (rootMultiplicity_pos hH).2 hHroot
    lia
  · have hscalar : b - c * (a + m) ≠ 0 := sub_ne_zero.mpr heq
    have hHnotroot : ¬H.IsRoot (-c) := by
      rw [Polynomial.IsRoot.def, hHeval]
      exact mul_ne_zero hscalar hqeval
    rw [hmult, rootMultiplicity_eq_zero hHnotroot, add_zero]

/-- The endpoint step has no root below `-c` exactly up to the affine
multiplicity threshold. -/
theorem endpointStep_roots_ge_neg_iff {c a b : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, -c ≤ r ∧ r < 0) :
    (∀ r ∈ (endpointStep c a b p).roots, -c ≤ r) ↔
      b ≤ c * (a + p.rootMultiplicity (-c)) := by
  let m := p.rootMultiplicity (-c)
  let q := p /ₘ (X + C c) ^ m
  let H := ((C a + C (m : ℝ)) * X + C b) * q +
    X * (X + C c) * q.derivative
  have hfactor : (X + C c) ^ m * q = p := by
    dsimp [q, m]
    rw [endpointFactor_eq]
    exact p.pow_mul_divByMonic_rootMultiplicity_eq (-c)
  have hqeval : q.eval (-c) ≠ 0 := by
    dsimp [q, m]
    rw [endpointFactor_eq]
    exact eval_divByMonic_pow_rootMultiplicity_ne_zero (-c) hp.ne_zero
  have hq : q ≠ 0 := fun hq => hqeval (by rw [hq, eval_zero])
  have hlinear : (X + C c : ℝ[X]) ≠ 0 := by
    rw [endpointFactor_eq]
    exact X_sub_C_ne_zero (-c)
  have hFfactor : endpointStep c a b p = (X + C c) ^ m * H := by
    dsimp [H]
    exact endpointStep_factorization c a b p q m hfactor
  have hFpos :=
    (endpointStep_natDegree_eq_and_leadingCoeff_pos (c := c) (b := b) ha hp).2
  have hH : H ≠ 0 := by
    intro hzero
    apply hFpos.ne_zero
    rw [hFfactor, hzero, mul_zero]
  have hqrr : q ≠ 0 ∧ q.Splits :=
    isRealRooted_of_dvd hp.ne_zero hs hq
      ⟨(X + C c) ^ m, by rw [mul_comm, hfactor]⟩
  have hqpos : HasPosLeadingCoeff q := by
    apply hasPosLeadingCoeff_of_pow_X_sub_C_mul (r := -c) (m := m)
    rw [← endpointFactor_eq, hfactor]
    exact hp
  have hHpos : HasPosLeadingCoeff H := by
    apply hasPosLeadingCoeff_of_pow_X_sub_C_mul (r := -c) (m := m)
    rw [← endpointFactor_eq, ← hFfactor]
    exact hFpos
  have hcommon : StrictInterl ((X - C (-c)) ^ m * q) ((X - C (-c)) ^ m * H) := by
    rw [← endpointFactor_eq, hfactor, ← hFfactor]
    exact endpointStep_strictInterl (b := b) ha hp hs hroots
  have hqH : StrictInterl q H :=
    strictInterl_of_strictInterl_mul_pow_X_sub_C_both (-c) m hcommon
  have hqdeg_factor : m + q.natDegree = p.natDegree := by
    calc
      m + q.natDegree = ((X + C c) ^ m).natDegree + q.natDegree := by
        rw [endpointFactor_eq, (monic_X_sub_C (-c)).natDegree_pow, natDegree_X_sub_C]
        simp
      _ = ((X + C c) ^ m * q).natDegree :=
        (natDegree_mul (pow_ne_zero _ hlinear) hq).symm
      _ = p.natDegree := congrArg natDegree hfactor
  have hHdeg_factor : m + H.natDegree = (endpointStep c a b p).natDegree := by
    calc
      m + H.natDegree = ((X + C c) ^ m).natDegree + H.natDegree := by
        rw [endpointFactor_eq, (monic_X_sub_C (-c)).natDegree_pow, natDegree_X_sub_C]
        simp
      _ = ((X + C c) ^ m * H).natDegree :=
        (natDegree_mul (pow_ne_zero _ hlinear) hH).symm
      _ = (endpointStep c a b p).natDegree := congrArg natDegree hFfactor.symm
  have hHdeg : H.natDegree = q.natDegree + 1 := by
    have hFdeg :=
      (endpointStep_natDegree_eq_and_leadingCoeff_pos (c := c) (b := b) ha hp).1
    lia
  have hinter : Interlaces q H := hqH.toInterlaces hHdeg.symm
  have hqroots : ∀ r ∈ q.roots, -c < r :=
    roots_gt_of_endpoint_factor hq hfactor hqeval fun r hr => (hroots r hr).1
  have hqsign : 0 < (-1 : ℝ) ^ q.natDegree * q.eval (-c) :=
    signed_eval_pos_at_endpoint hqrr.2 hqpos hqroots
  have hHeval : H.eval (-c) = (b - c * (a + m)) * q.eval (-c) := by
    dsimp [H]
    exact endpointCofactor_eval c a b q m
  have hsigned : (-1 : ℝ) ^ H.natDegree * H.eval (-c) =
      (c * (a + m) - b) * ((-1 : ℝ) ^ q.natDegree * q.eval (-c)) := by
    rw [hHdeg, pow_succ, hHeval]
    ring
  have hHroots : (∀ r ∈ H.roots, -c ≤ r) ↔ b ≤ c * (a + m) := by
    rw [roots_ge_iff_neg_one_pow_mul_eval_nonneg_of_interlaces hinter hHpos hqroots,
      hsigned]
    constructor <;> intro h
    · nlinarith
    · exact mul_nonneg (sub_nonneg.mpr h) hqsign.le
  have hprod : (X + C c) ^ m * H ≠ 0 := mul_ne_zero (pow_ne_zero _ hlinear) hH
  have htransfer : (∀ r ∈ (endpointStep c a b p).roots, -c ≤ r) ↔
      ∀ r ∈ H.roots, -c ≤ r := by
    constructor
    · intro h r hr
      apply h r
      rw [hFfactor, roots_mul hprod, Multiset.mem_add]
      exact Or.inr hr
    · intro h r hr
      rw [hFfactor, roots_mul hprod, Multiset.mem_add] at hr
      rcases hr with hr | hr
      · rw [endpointFactor_eq] at hr
        have hre : r = -c := by
          have hm : m ≠ 0 ∧ r = -c := by
            simpa only [roots_pow, roots_X_sub_C, Multiset.mem_nsmul,
              Multiset.mem_singleton] using hr
          exact hm.2
        rw [hre]
      · exact h r hr
  rw [htransfer, hHroots]

/-- Complete interval criterion: all roots of the endpoint step lie in
`[-c,0)` exactly up to the affine multiplicity threshold. -/
theorem endpointStep_roots_mem_Ico_iff {c a b : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hb : 0 < b) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, -c ≤ r ∧ r < 0) :
    (∀ r ∈ (endpointStep c a b p).roots, -c ≤ r ∧ r < 0) ↔
      b ≤ c * (a + p.rootMultiplicity (-c)) := by
  rw [← endpointStep_roots_ge_neg_iff ha hp hs hroots]
  constructor
  · exact fun h r hr => (h r hr).1
  · intro hlo r hr
    exact ⟨hlo r hr, endpointStep_roots_lt_zero ha hb hp hs hroots r hr⟩

/-- One normalized sequence step, including proper position, the interval
criterion, and the exact endpoint-multiplicity update. -/
theorem endpointSequence_step {P : ℕ → ℝ[X]} {c : ℝ} {a b ρ : ℕ → ℝ} {n : ℕ}
    (hrec : P (n + 1) = C (ρ n) * endpointStep c (a n) (b n) (P n))
    (ha : 0 < a n) (hb : 0 < b n) (hρ : 0 < ρ n)
    (hpos : HasPosLeadingCoeff (P n)) (hs : (P n).Splits)
    (hroots : ∀ r ∈ (P n).roots, -c ≤ r ∧ r < 0) :
    HasPosLeadingCoeff (P (n + 1)) ∧ (P (n + 1)).Splits ∧
      StrictInterl (P n) (P (n + 1)) ∧
      ((∀ r ∈ (P (n + 1)).roots, -c ≤ r ∧ r < 0) ↔
        b n ≤ c * (a n + (P n).rootMultiplicity (-c))) ∧
      (P (n + 1)).rootMultiplicity (-c) =
        if b n = c * (a n + (P n).rootMultiplicity (-c))
        then (P n).rootMultiplicity (-c) + 1 else (P n).rootMultiplicity (-c) := by
  have hρne : ρ n ≠ 0 := hρ.ne'
  have hstepPos :=
    (endpointStep_natDegree_eq_and_leadingCoeff_pos (c := c) (b := b n) ha hpos).2
  have hstepInterl := endpointStep_strictInterl (b := b n) ha hpos hs hroots
  have hnextPos : HasPosLeadingCoeff (P (n + 1)) := by
    rw [hrec]
    exact hasPosLeadingCoeff_C_mul hρ hstepPos
  have hnextSplits : (P (n + 1)).Splits := by
    rw [hrec]
    exact hstepInterl.2.1.2.C_mul (ρ n)
  have hnextInterl : StrictInterl (P n) (P (n + 1)) := by
    rw [hrec]
    exact hstepInterl.C_mul_right hρne
  refine ⟨hnextPos, hnextSplits, hnextInterl, ?_, ?_⟩
  · rw [hrec, roots_C_mul _ hρne]
    exact endpointStep_roots_mem_Ico_iff ha hb hpos hs hroots
  · rw [hrec, rootMultiplicity_mul
      (mul_ne_zero (C_ne_zero.mpr hρne) hstepPos.ne_zero), rootMultiplicity_C, zero_add]
    exact endpointStep_rootMultiplicity ha hpos hs hroots

private theorem endpointSequence_of_thresholds {P : ℕ → ℝ[X]} {c : ℝ}
    {a b ρ : ℕ → ℝ}
    (hrec : ∀ n, P (n + 1) = C (ρ n) * endpointStep c (a n) (b n) (P n))
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) (hρ : ∀ n, 0 < ρ n)
    (h0pos : HasPosLeadingCoeff (P 0)) (h0s : (P 0).Splits)
    (h0roots : ∀ r ∈ (P 0).roots, -c ≤ r ∧ r < 0)
    (hthreshold : ∀ n, b n ≤ c * (a n + (P n).rootMultiplicity (-c))) :
    ∀ n, HasPosLeadingCoeff (P n) ∧ (P n).Splits ∧
      ∀ r ∈ (P n).roots, -c ≤ r ∧ r < 0 := by
  intro n
  induction n with
  | zero => exact ⟨h0pos, h0s, h0roots⟩
  | succ n ih =>
      have hstep := endpointSequence_step (hrec n) (ha n) (hb n) (hρ n)
        ih.1 ih.2.1 ih.2.2
      exact ⟨hstep.1, hstep.2.1, hstep.2.2.2.1.mpr (hthreshold n)⟩

/-- A normalized variable-parameter sequence stays in `[-c,0)` at every index
if and only if every affine threshold is met. -/
theorem endpointSequence_roots_mem_Ico_iff {P : ℕ → ℝ[X]} {c : ℝ}
    {a b ρ : ℕ → ℝ}
    (hrec : ∀ n, P (n + 1) = C (ρ n) * endpointStep c (a n) (b n) (P n))
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) (hρ : ∀ n, 0 < ρ n)
    (h0pos : HasPosLeadingCoeff (P 0)) (h0s : (P 0).Splits)
    (h0roots : ∀ r ∈ (P 0).roots, -c ≤ r ∧ r < 0) :
    (∀ n r, r ∈ (P n).roots → -c ≤ r ∧ r < 0) ↔
      ∀ n, b n ≤ c * (a n + (P n).rootMultiplicity (-c)) := by
  constructor
  · intro hall
    have hcert : ∀ n, HasPosLeadingCoeff (P n) ∧ (P n).Splits := by
      intro n
      induction n with
      | zero => exact ⟨h0pos, h0s⟩
      | succ n ih =>
          have hstep := endpointSequence_step (hrec n) (ha n) (hb n) (hρ n)
            ih.1 ih.2 (fun r hr => hall n r hr)
          exact ⟨hstep.1, hstep.2.1⟩
    intro n
    have hstep := endpointSequence_step (hrec n) (ha n) (hb n) (hρ n)
      (hcert n).1 (hcert n).2 (fun r hr => hall n r hr)
    exact hstep.2.2.2.1.mp fun r hr => hall (n + 1) r hr
  · intro hthreshold n r hr
    exact (endpointSequence_of_thresholds hrec ha hb hρ h0pos h0s h0roots hthreshold n).2.2 r hr

/-- Along a confined normalized sequence, the endpoint multiplicity increments
at exactly the equality indices. -/
theorem endpointSequence_rootMultiplicity {P : ℕ → ℝ[X]} {c : ℝ}
    {a b ρ : ℕ → ℝ}
    (hrec : ∀ n, P (n + 1) = C (ρ n) * endpointStep c (a n) (b n) (P n))
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) (hρ : ∀ n, 0 < ρ n)
    (h0pos : HasPosLeadingCoeff (P 0)) (h0s : (P 0).Splits)
    (h0roots : ∀ r ∈ (P 0).roots, -c ≤ r ∧ r < 0)
    (hthreshold : ∀ n, b n ≤ c * (a n + (P n).rootMultiplicity (-c))) (n : ℕ) :
    (P (n + 1)).rootMultiplicity (-c) =
      if b n = c * (a n + (P n).rootMultiplicity (-c))
      then (P n).rootMultiplicity (-c) + 1 else (P n).rootMultiplicity (-c) := by
  have hcert := endpointSequence_of_thresholds hrec ha hb hρ h0pos h0s h0roots hthreshold n
  exact (endpointSequence_step (hrec n) (ha n) (hb n) (hρ n)
    hcert.1 hcert.2.1 hcert.2.2).2.2.2.2

/-- Number of affine threshold hits `r + jL` strictly before row `n`. -/
def affineEndpointMultiplicity (L r n : ℕ) : ℕ := (n - r) ⌈/⌉ L

private lemma ceilDiv_succ (L k : ℕ) (hL : 0 < L) :
    (k + 1) ⌈/⌉ L = if k = L * (k ⌈/⌉ L) then k ⌈/⌉ L + 1 else k ⌈/⌉ L := by
  let m := k ⌈/⌉ L
  have hkm : k ≤ L * m := le_smul_ceilDiv hL
  split_ifs with heq
  · apply le_antisymm
    · rw [ceilDiv_le_iff_le_mul hL]
      nlinarith
    · rw [Nat.succ_le_iff, ← not_le, ceilDiv_le_iff_le_mul hL]
      nlinarith
  · have hlt : k < L * m := lt_of_le_of_ne hkm heq
    apply le_antisymm
    · rw [ceilDiv_le_iff_le_mul hL]
      lia
    · exact (gc_mul_ceilDiv hL).monotone_l (Nat.le_add_right k 1)

private lemma affineEndpointMultiplicity_threshold (L r n : ℕ) (hL : 0 < L) :
    ((n : ℝ) / L - (r : ℝ) / L) ≤ affineEndpointMultiplicity L r n := by
  by_cases hrn : r ≤ n
  · have hceil : n - r ≤ L * affineEndpointMultiplicity L r n := by
      exact (ceilDiv_le_iff_le_mul hL).mp le_rfl
    have hcast : ((n - r : ℕ) : ℝ) = (n : ℝ) - r := by
      exact Nat.cast_sub hrn
    rw [div_sub_div_same, ← hcast, div_le_iff₀ (by positivity)]
    exact_mod_cast (show n - r ≤ affineEndpointMultiplicity L r n * L by
      simpa [mul_comm] using hceil)
  · have hnr : (n : ℝ) < r := by exact_mod_cast (Nat.lt_of_not_ge hrn)
    rw [div_sub_div_same]
    have hneg : ((n : ℝ) - r) / L < 0 :=
      div_neg_of_neg_of_pos (sub_neg.mpr hnr) (by positivity)
    exact hneg.le.trans (by positivity)

private lemma affineEndpointMultiplicity_eq_iff (L r n : ℕ) (hL : 0 < L) :
    ((n : ℝ) / L - (r : ℝ) / L) = affineEndpointMultiplicity L r n ↔
      r ≤ n ∧ n - r = L * affineEndpointMultiplicity L r n := by
  constructor
  · intro heq
    have hrn : r ≤ n := by
      by_contra h
      have hneg : (n : ℝ) / L - (r : ℝ) / L < 0 := by
        rw [div_sub_div_same]
        exact div_neg_of_neg_of_pos (sub_neg.mpr (by exact_mod_cast Nat.lt_of_not_ge h))
          (by positivity)
      have hm : 0 ≤ (affineEndpointMultiplicity L r n : ℝ) := by positivity
      linarith
    refine ⟨hrn, ?_⟩
    rw [div_sub_div_same] at heq
    have hne : (L : ℝ) ≠ 0 := by positivity
    have heq' : (n : ℝ) - r = (L : ℝ) * affineEndpointMultiplicity L r n := by
      apply (div_eq_iff hne).mp at heq
      nlinarith
    have hcast : ((n - r : ℕ) : ℝ) = (n : ℝ) - r := by
      exact Nat.cast_sub hrn
    rw [← hcast] at heq'
    exact_mod_cast heq'
  · rintro ⟨hrn, heq⟩
    rw [div_sub_div_same]
    have hcast : ((n - r : ℕ) : ℝ) = (n : ℝ) - r := Nat.cast_sub hrn
    rw [← hcast, heq]
    norm_num
    field_simp

private lemma affineEndpointMultiplicity_succ (L r n : ℕ) (hL : 0 < L) :
    affineEndpointMultiplicity L r (n + 1) =
      if ((n : ℝ) / L - (r : ℝ) / L) = affineEndpointMultiplicity L r n
      then affineEndpointMultiplicity L r n + 1 else affineEndpointMultiplicity L r n := by
  by_cases hrn : r ≤ n
  · have hsub : n + 1 - r = (n - r) + 1 := by lia
    by_cases heq : ((n : ℝ) / L - (r : ℝ) / L) = affineEndpointMultiplicity L r n
    · have hnateq : n - r = L * affineEndpointMultiplicity L r n :=
        ((affineEndpointMultiplicity_eq_iff L r n hL).mp heq).2
      have hnateq' : n - r = L * ((n - r) ⌈/⌉ L) := by
        simpa [affineEndpointMultiplicity] using hnateq
      simp only [heq, reduceIte]
      rw [affineEndpointMultiplicity, affineEndpointMultiplicity, hsub,
        ceilDiv_succ L (n - r) hL]
      rw [ite_eq_left hnateq']
    · have hnatne : n - r ≠ L * affineEndpointMultiplicity L r n := fun h =>
        heq ((affineEndpointMultiplicity_eq_iff L r n hL).mpr ⟨hrn, h⟩)
      have hnatne' : n - r ≠ L * ((n - r) ⌈/⌉ L) := by
        simpa [affineEndpointMultiplicity] using hnatne
      simp only [heq, reduceIte]
      rw [affineEndpointMultiplicity, affineEndpointMultiplicity, hsub,
        ceilDiv_succ L (n - r) hL]
      rw [ite_eq_right hnatne']
  · have hle : n + 1 ≤ r := by lia
    have hne : ¬((n : ℝ) / L - (r : ℝ) / L) = affineEndpointMultiplicity L r n :=
      (affineEndpointMultiplicity_eq_iff L r n hL).not.mpr fun h => hrn h.1
    have hsub : n - r = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hrn))
    have hsub' : n + 1 - r = 0 := Nat.sub_eq_zero_of_le hle
    have hne' : ¬((n : ℝ) / L - (r : ℝ) / L) = (0 : ℕ) := by
      simpa [affineEndpointMultiplicity, hsub] using hne
    rw [affineEndpointMultiplicity, hsub', zero_ceilDiv,
      affineEndpointMultiplicity, hsub, zero_ceilDiv]
    simp only [hne', reduceIte]

/-- Affine steps with slope `1 / L` and intercept `r / L` stay confined,
have the ceiling-division endpoint multiplicity, and strictly interlace.
This is the sufficiency direction of the affine classification in issue #2087. -/
theorem affineEndpointSequence {P : ℕ → ℝ[X]} {c a : ℝ} {rho : ℕ → ℝ}
    (L r : ℕ) (hc : 0 < c) (hL : 0 < L) (ha : (r : ℝ) / L < a)
    (hrec : ∀ n, P (n + 1) = C (rho n) *
      endpointStep c a (c * (a + (n : ℝ) / L - (r : ℝ) / L)) (P n))
    (hrho : ∀ n, 0 < rho n)
    (h0pos : HasPosLeadingCoeff (P 0)) (h0s : (P 0).Splits)
    (h0roots : ∀ z ∈ (P 0).roots, -c < z ∧ z < 0) :
    ∀ n, HasPosLeadingCoeff (P n) ∧ (P n).Splits ∧
      (∀ z ∈ (P n).roots, -c ≤ z ∧ z < 0) ∧
      (P n).rootMultiplicity (-c) = affineEndpointMultiplicity L r n ∧
      StrictInterl (P n) (P (n + 1)) := by
  have ha0 : 0 < a :=
    lt_of_le_of_lt (div_nonneg (by positivity) (by positivity)) ha
  have hb : ∀ n : ℕ, 0 < c * (a + (n : ℝ) / L - (r : ℝ) / L) := by
    intro n
    have hn : 0 ≤ (n : ℝ) / L := div_nonneg (by positivity) (by positivity)
    apply mul_pos hc
    linarith
  have hcert : ∀ n, HasPosLeadingCoeff (P n) ∧ (P n).Splits ∧
      (∀ z ∈ (P n).roots, -c ≤ z ∧ z < 0) ∧
      (P n).rootMultiplicity (-c) = affineEndpointMultiplicity L r n := by
    intro n
    induction n with
    | zero =>
        refine ⟨h0pos, h0s, fun z hz => ⟨(h0roots z hz).1.le, (h0roots z hz).2⟩, ?_⟩
        rw [affineEndpointMultiplicity, Nat.zero_sub, zero_ceilDiv]
        apply rootMultiplicity_eq_zero
        intro hroot
        have hz : -c ∈ (P 0).roots := (mem_roots h0pos.ne_zero).2 hroot
        exact (lt_irrefl (-c)) (h0roots (-c) hz).1
    | succ n ih =>
        have hstep := endpointSequence_step (P := P) (c := c) (a := fun _ => a)
          (b := fun k => c * (a + (k : ℝ) / L - (r : ℝ) / L)) (ρ := rho)
          (hrec n) ha0 (hb n) (hrho n) ih.1 ih.2.1 ih.2.2.1
        have hslope := affineEndpointMultiplicity_threshold L r n hL
        have hthreshold :
            c * (a + (n : ℝ) / L - (r : ℝ) / L) ≤
              c * (a + (P n).rootMultiplicity (-c)) := by
          rw [ih.2.2.2]
          exact mul_le_mul_of_nonneg_left (by linarith) hc.le
        have hmult := hstep.2.2.2.2
        rw [ih.2.2.2] at hmult
        have heq :
            c * (a + (n : ℝ) / L - (r : ℝ) / L) =
                c * (a + affineEndpointMultiplicity L r n) ↔
              (n : ℝ) / L - (r : ℝ) / L =
                affineEndpointMultiplicity L r n := by
          constructor <;> intro h
          · nlinarith
          · nlinarith
        simp only [heq] at hmult
        refine ⟨hstep.1, hstep.2.1, hstep.2.2.2.1.mpr hthreshold, ?_⟩
        exact hmult.trans (affineEndpointMultiplicity_succ L r n hL).symm
  intro n
  have hn := hcert n
  have hstep := endpointSequence_step (P := P) (c := c) (a := fun _ => a)
    (b := fun k => c * (a + (k : ℝ) / L - (r : ℝ) / L)) (ρ := rho)
    (hrec n) ha0 (hb n) (hrho n) hn.1 hn.2.1 hn.2.2.1
  exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, hstep.2.2.1⟩

/-- The ceiling-division formula is the number of indices `j` for which
`r + jL < n`. -/
theorem affineEndpointMultiplicity_eq_card_filter (L r n : ℕ) (hL : 0 < L) :
    affineEndpointMultiplicity L r n =
      ((Finset.range n).filter fun j => r + j * L < n).card := by
  have hfin : (Finset.range n).filter (fun j => r + j * L < n) =
      Finset.range (affineEndpointMultiplicity L r n) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    by_cases hrn : r < n
    · have hiff : j < affineEndpointMultiplicity L r n ↔ L * j < n - r := by
        rw [affineEndpointMultiplicity, ← not_le, ceilDiv_le_iff_le_mul hL, not_le]
      rw [hiff]
      rw [Nat.lt_sub_iff_add_lt']
      constructor
      · rintro ⟨-, hsum⟩
        simpa [mul_comm] using hsum
      · intro hsum
        have hjprod : j ≤ L * j := by
          simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hL
        have hjn : j < n :=
          hjprod.trans_lt ((Nat.le_add_left (L * j) r).trans_lt hsum)
        exact ⟨hjn, by simpa [mul_comm] using hsum⟩
    · have hzero : affineEndpointMultiplicity L r n = 0 := by
        simp [affineEndpointMultiplicity, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hrn)]
      rw [hzero]
      constructor <;> intro h
      · lia
      · lia
  rw [hfin, Finset.card_range]

end RealRooted.MaWang
