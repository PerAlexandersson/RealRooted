import RealRooted.PosCombo
import RealRooted.IteratedDerivativeShift
import RealRooted.ObreschkoffContinuity

/-!
# All-real-combination real-rootedness

This file defines `AllComboRealRooted` and packages common-root reduction,
derivative, and `iterateTDeriv` algebra used in the Obreschkoff converse proof.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- All real linear combinations of `f` and `g` are real-rooted (or zero). -/
def AllComboRealRooted (f g : ℝ[X]) : Prop :=
  ∀ α β : ℝ, IsRealRootedOrZero (C α * f + C β * g)

lemma allComboRealRooted_comm {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    AllComboRealRooted g f := by
  intro α β
  simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hall β α

lemma allComboRealRooted_common_root_reduction
    {f g qf qg : ℝ[X]} {r : ℝ}
    (hf_def : f = (X - C r) * qf)
    (hg_def : g = (X - C r) * qg)
    (hall : AllComboRealRooted f g) :
    AllComboRealRooted qf qg := by
  intro α β
  by_cases hq : C α * qf + C β * qg = 0
  · exact Or.inl hq
  · right
    have hcomb :
        C α * f + C β * g = (X - C r) * (C α * qf + C β * qg) := by
      rw [hf_def, hg_def, mul_add]
      congr 1
      · rw [← mul_assoc, mul_comm (C α) (X - C r), mul_assoc]
      · rw [← mul_assoc, mul_comm (C β) (X - C r), mul_assoc]
    have hsum_ne : C α * f + C β * g ≠ 0 := by
      rw [hcomb]
      exact mul_ne_zero (X_sub_C_ne_zero r) hq
    rcases hall α β with hzero | hrr
    · exact False.elim (hsum_ne hzero)
    · exact
        isRealRooted_of_dvd hrr hq
          ⟨X - C r, by
            rw [hcomb]
            ring⟩

lemma allComboRealRooted_C_mul_left
    {f g : ℝ[X]} {c : ℝ} (hall : AllComboRealRooted f g) :
    AllComboRealRooted (C c * f) g := by
  intro α β
  simpa [C_mul, mul_assoc, mul_left_comm, mul_comm] using hall (α * c) β

lemma allComboRealRooted_C_mul_right
    {f g : ℝ[X]} {c : ℝ} (hall : AllComboRealRooted f g) :
    AllComboRealRooted f (C c * g) := by
  intro α β
  simpa [C_mul, mul_assoc, mul_left_comm, mul_comm] using hall α (β * c)

/-- Multiplying both polynomials by the same real-rooted factor preserves
`AllComboRealRooted`. This is the multiplication-back step for common-root
reductions in Obreschkoff-style arguments. -/
lemma allComboRealRooted_mul_common_factor
    {d f g : ℝ[X]} (hd : d ≠ 0 ∧ d.Splits) (hall : AllComboRealRooted f g) :
    AllComboRealRooted (d * f) (d * g) := by
  intro α β
  have hcomb :
      C α * (d * f) + C β * (d * g) =
        d * (C α * f + C β * g) := by
    calc
      C α * (d * f) + C β * (d * g)
          = (C α * d) * f + (C β * d) * g := by
              simp [mul_assoc]
      _ = (d * C α) * f + (d * C β) * g := by
            rw [mul_comm (C α) d, mul_comm (C β) d]
      _ = d * (C α * f) + d * (C β * g) := by
            simp [mul_assoc]
      _ = d * (C α * f + C β * g) := by
            rw [mul_add]
  rcases hall α β with hzero | hrr
  · left
    rw [hcomb, hzero, mul_zero]
  · right
    rw [hcomb]
    exact isRealRooted_mul hd hrr

lemma derivative_eq_zero_or_isRealRooted {p : ℝ[X]}
    (hp : p ≠ 0 ∧ p.Splits) :
    p.derivative = 0 ∨ (p.derivative ≠ 0 ∧ p.derivative.Splits) := by
  by_cases hdeg0 : p.natDegree = 0
  · left
    rw [eq_C_of_natDegree_eq_zero hdeg0, derivative_C]
  · by_cases hdeg1 : p.natDegree = 1
    · right
      have hder_deg0 : p.derivative.natDegree = 0 := by
        rw [natDegree_derivative_eq (by lia), hdeg1]
      have hder_ne : p.derivative ≠ 0 := by
        intro h0
        have hcoeff : p.derivative.coeff 0 = p.leadingCoeff := by
          rw [coeff_derivative]
          simp [Polynomial.leadingCoeff, hdeg1]
        have hlc0 : p.leadingCoeff = 0 := by
          have hcoeff0 : p.derivative.coeff 0 = 0 := by
            simp [h0]
          rw [hcoeff] at hcoeff0
          simpa using hcoeff0
        exact (leadingCoeff_ne_zero.mpr hp.1) hlc0
      exact isRealRooted_of_deg_zero hder_ne hder_deg0
    · right
      exact (derivative_interlaces hp (by lia)).2.1

lemma allComboRealRooted_derivative
    {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    AllComboRealRooted f.derivative g.derivative := by
  intro α β
  rcases hall α β with hzero | hrr
  · left
    simpa [derivative_add, derivative_C_mul] using congrArg derivative hzero
  · rcases derivative_eq_zero_or_isRealRooted hrr with hder_zero | hder_rr
    · left
      simpa [derivative_add, derivative_C_mul] using hder_zero
    · right
      simpa [derivative_add, derivative_C_mul] using hder_rr

lemma allComboRealRooted_iterate_derivative
    {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    ∀ n : ℕ, AllComboRealRooted ((derivative^[n]) f) ((derivative^[n]) g)
  | 0 => by simpa using hall
  | n + 1 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact allComboRealRooted_derivative
        (allComboRealRooted_iterate_derivative hall n)

lemma TDeriv_add (eps : ℝ) (p q : ℝ[X]) :
    TDeriv eps (p + q) = TDeriv eps p + TDeriv eps q := by
  ext n
  simp [TDeriv, sub_eq_add_neg, left_distrib]
  ring

lemma TDeriv_C_mul (eps c : ℝ) (p : ℝ[X]) :
    TDeriv eps (C c * p) = C c * TDeriv eps p := by
  ext n
  simp [TDeriv, sub_eq_add_neg]
  ring

@[simp] lemma iterateTDeriv_zero_poly (eps : ℝ) :
    ∀ n : ℕ, iterateTDeriv eps n (0 : ℝ[X]) = 0
  | 0 => rfl
  | n + 1 => by
      rw [iterateTDeriv_succ, iterateTDeriv_zero_poly]
      simp [TDeriv]

lemma iterateTDeriv_add (eps : ℝ) :
    ∀ (n : ℕ) (p q : ℝ[X]),
      iterateTDeriv eps n (p + q) = iterateTDeriv eps n p + iterateTDeriv eps n q
  | 0, p, q => by simp [iterateTDeriv]
  | n + 1, p, q => by
      rw [iterateTDeriv_succ, iterateTDeriv_succ, iterateTDeriv_succ, iterateTDeriv_add]
      exact TDeriv_add eps _ _

lemma iterateTDeriv_C_mul (eps c : ℝ) :
    ∀ (n : ℕ) (p : ℝ[X]),
      iterateTDeriv eps n (C c * p) = C c * iterateTDeriv eps n p
  | 0, p => by simp [iterateTDeriv]
  | n + 1, p => by
      rw [iterateTDeriv_succ, iterateTDeriv_succ, iterateTDeriv_C_mul]
      exact TDeriv_C_mul eps c _

lemma iterateTDeriv_eq_of_natDegree_zero (eps : ℝ) {p : ℝ[X]}
    (hdeg : p.natDegree = 0) :
    ∀ n : ℕ, iterateTDeriv eps n p = p
  | 0 => rfl
  | n + 1 => by
      rw [iterateTDeriv_succ, iterateTDeriv_eq_of_natDegree_zero eps hdeg n]
      rw [eq_C_of_natDegree_eq_zero hdeg, TDeriv, derivative_C]
      ring

lemma natDegree_iterateTDeriv_of_isRealRooted
    {eps : ℝ} {p : ℝ[X]} {n : ℕ}
    (hp : p ≠ 0 ∧ p.Splits) :
    (iterateTDeriv eps n p).natDegree = p.natDegree := by
  by_cases hdeg0 : p.natDegree = 0
  · rw [iterateTDeriv_eq_of_natDegree_zero eps hdeg0, hdeg0]
  · exact
      natDegree_iterateTDeriv hp.1
        (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hdeg0))

lemma iterateTDeriv_linear_combo (eps α β : ℝ) (n : ℕ) (f g : ℝ[X]) :
    iterateTDeriv eps n (C α * f + C β * g) =
      C α * iterateTDeriv eps n f + C β * iterateTDeriv eps n g := by
  rw [iterateTDeriv_add, iterateTDeriv_C_mul, iterateTDeriv_C_mul]

lemma TDeriv_eq_zero_iff (eps : ℝ) {p : ℝ[X]} :
    TDeriv eps p = 0 ↔ p = 0 := by
  constructor
  · intro hT
    by_cases hp0 : p = 0
    · exact hp0
    · by_cases hdeg0 : p.natDegree = 0
      · have hconst : TDeriv eps p = p := by
          rw [eq_C_of_natDegree_eq_zero hdeg0, TDeriv, derivative_C]
          ring
        rw [hconst] at hT
        exact hT
      · exact False.elim <|
          TDeriv_ne_zero hp0 (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hdeg0)) hT
  · intro hp0
    simp [hp0, TDeriv]

lemma TDeriv_injective (eps : ℝ) : Function.Injective (TDeriv eps) := by
  intro p q hpq
  have hsub : TDeriv eps (p - q) = 0 := by
    rw [sub_eq_add_neg, show -q = C (-1) * q by simp, TDeriv_add, TDeriv_C_mul, hpq]
    simp
  exact sub_eq_zero.mp ((TDeriv_eq_zero_iff eps).1 hsub)

lemma iterateTDeriv_injective (eps : ℝ) :
    ∀ n : ℕ, Function.Injective (iterateTDeriv eps n)
  | 0 => by
      intro p q hpq
      simpa using hpq
  | n + 1 => by
      intro p q hpq
      rw [iterateTDeriv_succ, iterateTDeriv_succ] at hpq
      exact iterateTDeriv_injective eps n ((TDeriv_injective eps) hpq)

lemma allComboRealRooted_iterateTDeriv
    {f g : ℝ[X]} (hall : AllComboRealRooted f g)
    {eps : ℝ} (heps : 0 < eps) (n : ℕ) :
    AllComboRealRooted (iterateTDeriv eps n f) (iterateTDeriv eps n g) := by
  intro α β
  rcases hall α β with hzero | hrr
  · left
    have hiter := congrArg (iterateTDeriv eps n) hzero
    simpa [iterateTDeriv_linear_combo] using hiter
  · right
    simpa [iterateTDeriv_linear_combo] using
      (isRealRooted_iterateTDeriv (eps := eps) (k := n) heps hrr)

lemma hasSimpleRoots_TDeriv_of_hasSimpleRoots
    {eps : ℝ} {p : ℝ[X]}
    (heps : 0 < eps)
    (hp : p ≠ 0 ∧ p.Splits)
    (hsimple : HasSimpleRoots p) :
    HasSimpleRoots (TDeriv eps p) := by
  intro a ha
  have hdeg : 1 ≤ p.natDegree := by
    by_cases h0 : p.natDegree = 0
    · have hp_eq : p = C (p.coeff 0) := by
        simpa using eq_C_of_natDegree_eq_zero h0
      have hT_eq : TDeriv eps p = p := by
        rw [hp_eq, TDeriv, derivative_C]
        ring
      have hp_root : p.IsRoot a := by
        simpa [hT_eq] using ha
      have hcoeff0 : p.coeff 0 = 0 := by
        rw [hp_eq, Polynomial.IsRoot.def, eval_C] at hp_root
        exact hp_root
      have hp_zero : p = 0 := by
        rw [hp_eq, hcoeff0]
        simp
      exact False.elim (hp.1 hp_zero)
    · exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0)
  have hp_not_root : ¬ p.IsRoot a := by
    intro hp_root
    exact
      not_isRoot_TDeriv_of_simple_root
        (ne_of_gt heps) hp.1 hp_root (hsimple a hp_root) ha
  have hT_rr : ((TDeriv eps p) ≠ 0 ∧
    (TDeriv eps p).Splits) := isRealRooted_TDeriv heps hp
  have hmult_pos : 1 ≤ (TDeriv eps p).rootMultiplicity a := by
    exact (rootMultiplicity_pos hT_rr.1).mpr ha
  have hmult_le : (TDeriv eps p).rootMultiplicity a ≤ 1 :=
    rootMultiplicity_TDeriv_le_one_of_not_isRoot heps hp hdeg hp_not_root
  lia

lemma hasSimpleRoots_iterateTDeriv_of_hasSimpleRoots
    {eps : ℝ} {p : ℝ[X]} {n : ℕ}
    (heps : 0 < eps)
    (hp : p ≠ 0 ∧ p.Splits)
    (hsimple : HasSimpleRoots p) :
    HasSimpleRoots (iterateTDeriv eps n p) := by
  induction n generalizing p with
  | zero =>
      simpa using hsimple
  | succ n ih =>
      rw [iterateTDeriv_succ]
      exact
        hasSimpleRoots_TDeriv_of_hasSimpleRoots heps
          (isRealRooted_iterateTDeriv (eps := eps) (k := n) heps hp)
          (ih hp hsimple)

lemma iterateTDeriv_add_index (eps : ℝ) (m n : ℕ) (p : ℝ[X]) :
    iterateTDeriv eps (m + n) p = iterateTDeriv eps m (iterateTDeriv eps n p) := by
  simpa [iterateTDeriv] using Function.iterate_add_apply (TDeriv eps) m n p

lemma hasSimpleRoots_iterateTDeriv_of_natDegree_le
    {eps : ℝ} {p : ℝ[X]} {n : ℕ}
    (heps : 0 < eps)
    (hp : p ≠ 0 ∧ p.Splits)
    (hdeg : p.natDegree ≤ n) :
    HasSimpleRoots (iterateTDeriv eps n p) := by
  let m := n - p.natDegree
  have hm : n = m + p.natDegree := by
    unfold m
    lia
  obtain ⟨hp_cut_rr, hp_cut_simple⟩ :=
    isRealRooted_and_hasSimpleRoots_iterateTDeriv
      (eps := eps) (f := p) (n := p.natDegree) heps hp rfl
  rw [hm, iterateTDeriv_add_index]
  exact hasSimpleRoots_iterateTDeriv_of_hasSimpleRoots heps hp_cut_rr hp_cut_simple

lemma simple_pair_of_allComboRealRooted_iterateTDeriv
    {f g : ℝ[X]}
    (hf : f ≠ 0 ∧ f.Splits) (hg : g ≠ 0 ∧ g.Splits)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree)
    {eps : ℝ} (heps : 0 < eps) :
    let n := max f.natDegree g.natDegree
    AllComboRealRooted (iterateTDeriv eps n f) (iterateTDeriv eps n g) ∧
      ((iterateTDeriv eps n f) ≠ 0 ∧
        (iterateTDeriv eps n f).Splits) ∧
      ((iterateTDeriv eps n g) ≠ 0 ∧
        (iterateTDeriv eps n g).Splits) ∧
      HasSimpleRoots (iterateTDeriv eps n f) ∧
      HasSimpleRoots (iterateTDeriv eps n g) ∧
      ((iterateTDeriv eps n f).natDegree + 1 = (iterateTDeriv eps n g).natDegree ∨
        (iterateTDeriv eps n f).natDegree = (iterateTDeriv eps n g).natDegree) := by
  dsimp
  refine ⟨allComboRealRooted_iterateTDeriv hall heps _, ?_, ?_, ?_, ?_, ?_⟩
  · exact isRealRooted_iterateTDeriv (eps := eps) (k := max f.natDegree g.natDegree) heps hf
  · exact isRealRooted_iterateTDeriv (eps := eps) (k := max f.natDegree g.natDegree) heps hg
  · exact
      hasSimpleRoots_iterateTDeriv_of_natDegree_le
        (eps := eps) (n := max f.natDegree g.natDegree) heps hf (Nat.le_max_left _ _)
  · exact
      hasSimpleRoots_iterateTDeriv_of_natDegree_le
        (eps := eps) (n := max f.natDegree g.natDegree) heps hg (Nat.le_max_right _ _)
  · simpa [natDegree_iterateTDeriv_of_isRealRooted
      (eps := eps) (n := max f.natDegree g.natDegree) hf,
      natDegree_iterateTDeriv_of_isRealRooted
        (eps := eps) (n := max f.natDegree g.natDegree) hg] using hdeg

lemma allComboRealRooted_eq_zero_or_isRealRooted_and_hasSimpleRoots_iterateTDeriv
    {f g : ℝ[X]} (hall : AllComboRealRooted f g)
    {eps : ℝ} (heps : 0 < eps) :
    let n := max f.natDegree g.natDegree
    ∀ α β : ℝ,
      C α * iterateTDeriv eps n f + C β * iterateTDeriv eps n g = 0 ∨
        (((C α * iterateTDeriv eps n f + C β * iterateTDeriv eps n g) ≠ 0 ∧
          (C α * iterateTDeriv eps n f + C β * iterateTDeriv eps n g).Splits) ∧
          HasSimpleRoots (C α * iterateTDeriv eps n f + C β * iterateTDeriv eps n g)) := by
  dsimp
  intro α β
  let p : ℝ[X] := C α * f + C β * g
  have hpdeg : p.natDegree ≤ max f.natDegree g.natDegree := by
    calc
      p.natDegree ≤ max (C α * f).natDegree (C β * g).natDegree := natDegree_add_le _ _
      _ ≤ max f.natDegree g.natDegree := by
        exact max_le_max (natDegree_C_mul_le _ _) (natDegree_C_mul_le _ _)
  rcases hall α β with hp0 | hp_rr
  · left
    have hiter := congrArg (iterateTDeriv eps (max f.natDegree g.natDegree)) hp0
    simpa [p, iterateTDeriv_linear_combo] using hiter
  · right
    refine ⟨?_, ?_⟩
    · simpa [p, iterateTDeriv_linear_combo] using
        (isRealRooted_iterateTDeriv
          (eps := eps) (k := max f.natDegree g.natDegree) heps hp_rr)
    · simpa [p, iterateTDeriv_linear_combo] using
        (hasSimpleRoots_iterateTDeriv_of_natDegree_le
          (eps := eps) (p := p) (n := max f.natDegree g.natDegree) heps hp_rr hpdeg)


end RealRooted
