import RealRooted.IteratedDerivativeShift
import RealRooted.Mathlib.Algebra.Polynomial.Basic
import RealRooted.ObreschkoffContinuity
import RealRooted.PosCombo

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
  ∀ α β : ℝ, (C α * f + C β * g).Splits

lemma allComboRealRooted_comm {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    AllComboRealRooted g f := by
  intro α β
  simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hall β α

lemma allComboRealRooted_common_root_reduction
    {f g qf qg : ℝ[X]} {r : ℝ}
    (hf_def : f = (X - C r) * qf)
    (hg_def : g = (X - C r) * qg)
    (hall : AllComboRealRooted f g) :
    AllComboRealRooted qf qg :=
  fun α β ↦ .of_dvd' (hall α β) (by simp_all [mul_left_comm (C _), ← mul_add, sub_eq_zero])
    ⟨X - C r, by grind⟩

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
    {d f g : ℝ[X]} (hd : d.Splits) (hall : AllComboRealRooted f g) :
    AllComboRealRooted (d * f) (d * g) :=
  fun α β ↦ by simp [mul_left_comm, ← mul_add, hd, hall α β]

lemma splits_derivative {p : ℝ[X]} (hp : p.Splits) : p.derivative.Splits := by
  by_cases hdeg0 : p.natDegree = 0
  · simp_all [derivative_eq_zero.2]
  by_cases hdeg1 : p.natDegree = 1
  · exact .of_natDegree_eq_zero (by simp [hdeg1])
  · exact (derivative_interlaces hp (by lia)).2.1.2

lemma allComboRealRooted_derivative
    {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    AllComboRealRooted f.derivative g.derivative :=
  fun α β ↦ by simpa using splits_derivative <| hall α β

lemma allComboRealRooted_iterate_derivative
    {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    ∀ n : ℕ, AllComboRealRooted ((derivative^[n]) f) ((derivative^[n]) g)
  | 0 => by simp_all
  | n + 1 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact allComboRealRooted_derivative
        (allComboRealRooted_iterate_derivative hall n)

lemma iterateTDeriv_linear_combo (eps α β : ℝ) (n : ℕ) (f g : ℝ[X]) :
    iterateTDeriv eps n (C α * f + C β * g) =
      C α * iterateTDeriv eps n f + C β * iterateTDeriv eps n g := by
  rw [iterateTDeriv_add, iterateTDeriv_C_mul, iterateTDeriv_C_mul]

lemma TDeriv_eq_zero_iff (eps : ℝ) {p : ℝ[X]} :
    TDeriv eps p = 0 ↔ p = 0 := by
  constructor
  · intro hT
    by_cases hp0 : p = 0
    · lia
    · by_cases hdeg0 : p.natDegree = 0
      · have hconst : TDeriv eps p = p := by
          rw [eq_C_of_natDegree_eq_zero hdeg0, TDeriv, derivative_C]
          simp
        lia
      · cases TDeriv_ne_zero hp0 hT
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
      simp_all
  | n + 1 => by
      intro p q hpq
      rw [iterateTDeriv_succ, iterateTDeriv_succ] at hpq
      exact iterateTDeriv_injective eps n ((TDeriv_injective eps) hpq)

lemma allComboRealRooted_iterateTDeriv
    {f g : ℝ[X]} (hall : AllComboRealRooted f g)
    {eps : ℝ} (heps : 0 < eps) (n : ℕ) :
    AllComboRealRooted (iterateTDeriv eps n f) (iterateTDeriv eps n g) :=
  fun α β ↦ by simpa [iterateTDeriv_linear_combo] using splits_iterateTDeriv heps <| hall α β

lemma hasSimpleRoots_tderiv
    {eps : ℝ} {p : ℝ[X]}
    (heps : 0 < eps)
    (hp : p.Splits)
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
        lia
      have hcoeff0 : p.coeff 0 = 0 := by
        rw [hp_eq, Polynomial.IsRoot.def, eval_C] at hp_root
        lia
      have := hsimple.ne_zero
      grind
    · lia
  have hp_not_root : ¬ p.IsRoot a := by
    intro hp_root
    exact
      not_isRoot_TDeriv_of_simple_root
        (ne_of_gt heps) hsimple.ne_zero hp_root (hsimple a hp_root) ha
  have hmult_pos : 1 ≤ (TDeriv eps p).rootMultiplicity a := by
    exact (rootMultiplicity_pos <| TDeriv_ne_zero hsimple.ne_zero).mpr ha
  have hmult_le : (TDeriv eps p).rootMultiplicity a ≤ 1 :=
    rootMultiplicity_TDeriv_le_one_of_not_isRoot heps hp hp_not_root
  lia

lemma hasSimpleRoots_iterateTDeriv
    {eps : ℝ} {p : ℝ[X]} {n : ℕ}
    (heps : 0 < eps)
    (hp : p.Splits)
    (hsimple : HasSimpleRoots p) :
    HasSimpleRoots (iterateTDeriv eps n p) := by
  induction n generalizing p with
  | zero => simp_all
  | succ n ih =>
    rw [iterateTDeriv_succ]
    exact hasSimpleRoots_tderiv heps (splits_iterateTDeriv heps hp) (ih hp hsimple)

lemma iterateTDeriv_add_index (eps : ℝ) (m n : ℕ) (p : ℝ[X]) :
    iterateTDeriv eps (m + n) p = iterateTDeriv eps m (iterateTDeriv eps n p) := by
  simpa [iterateTDeriv] using Function.iterate_add_apply (TDeriv eps) m n p

lemma hasSimpleRoots_iterateTDeriv_of_natDegree_le
    {eps : ℝ} {p : ℝ[X]} {n : ℕ}
    (heps : 0 < eps) (hp₀ : p ≠ 0)
    (hp : p.Splits)
    (hdeg : p.natDegree ≤ n) :
    HasSimpleRoots (iterateTDeriv eps n p) := by
  let m := n - p.natDegree
  have hm : n = m + p.natDegree := by lia
  rw [hm, iterateTDeriv_add_index]
  exact hasSimpleRoots_iterateTDeriv heps (splits_iterateTDeriv heps hp) <|
    hasSimpleRoots_iterateTDeriv_of_natDegree heps hp₀ hp rfl

lemma simple_pair_of_allComboRealRooted_iterateTDeriv
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0)
    (hf : f.Splits) (hg : g.Splits)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree)
    {eps : ℝ} (heps : 0 < eps) :
    let n := max f.natDegree g.natDegree
    AllComboRealRooted (iterateTDeriv eps n f) (iterateTDeriv eps n g) ∧
      ((iterateTDeriv eps n f) ≠ 0 ∧ (iterateTDeriv eps n f).Splits) ∧
      ((iterateTDeriv eps n g) ≠ 0 ∧ (iterateTDeriv eps n g).Splits) ∧
      HasSimpleRoots (iterateTDeriv eps n f) ∧
      HasSimpleRoots (iterateTDeriv eps n g) ∧
      ((iterateTDeriv eps n f).natDegree + 1 = (iterateTDeriv eps n g).natDegree ∨
        (iterateTDeriv eps n f).natDegree = (iterateTDeriv eps n g).natDegree) := by
  dsimp
  refine ⟨allComboRealRooted_iterateTDeriv hall heps _, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨iterateTDeriv_ne_zero hf₀, splits_iterateTDeriv heps hf⟩
  · exact ⟨iterateTDeriv_ne_zero hg₀, splits_iterateTDeriv heps hg⟩
  · exact
      hasSimpleRoots_iterateTDeriv_of_natDegree_le
        (eps := eps) (n := max f.natDegree g.natDegree) heps hf₀ hf (Nat.le_max_left _ _)
  · exact
      hasSimpleRoots_iterateTDeriv_of_natDegree_le
        (eps := eps) (n := max f.natDegree g.natDegree) heps hg₀ hg (Nat.le_max_right _ _)
  · simpa using hdeg

lemma allComboRealRooted_eq_zero_or_isRealRooted_and_hasSimpleRoots_iterateTDeriv
    {f g : ℝ[X]} (hall : AllComboRealRooted f g)
    {eps : ℝ} (heps : 0 < eps) :
    let n := max f.natDegree g.natDegree
    ∀ α β : ℝ,
        (C α * iterateTDeriv eps n f + C β * iterateTDeriv eps n g).Splits ∧
          (C α * iterateTDeriv eps n f + C β * iterateTDeriv eps n g ≠ 0 →
            HasSimpleRoots (C α * iterateTDeriv eps n f + C β * iterateTDeriv eps n g)) := by
  dsimp
  intro α β
  have hpdeg : (C α * f + C β * g).natDegree ≤ max f.natDegree g.natDegree := by
    calc
      (C α * f + C β * g).natDegree ≤ max (C α * f).natDegree (C β * g).natDegree :=
        natDegree_add_le ..
      _ ≤ max f.natDegree g.natDegree := by
        exact max_le_max (natDegree_C_mul_le _ _) (natDegree_C_mul_le _ _)
  refine ⟨?_, ?_⟩
  · simpa [iterateTDeriv_linear_combo] using
      (splits_iterateTDeriv
        (eps := eps) (k := max f.natDegree g.natDegree) heps (hall α β))
  by_cases hp : C α * f + C β * g = 0
  · simp [← iterateTDeriv_linear_combo, hp]
  rintro -
  simpa [iterateTDeriv_linear_combo] using
    hasSimpleRoots_iterateTDeriv_of_natDegree_le heps hp (hall α β) hpdeg


end RealRooted
