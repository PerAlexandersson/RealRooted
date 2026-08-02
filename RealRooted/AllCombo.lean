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

namespace AllComboRealRooted

lemma isRealRooted_left {f g : ℝ[X]} (hall : AllComboRealRooted f g) (hf0 : f ≠ 0) :
    f ≠ 0 ∧ f.Splits :=
  ⟨hf0, by simpa using hall 1 0⟩

lemma isRealRooted_right {f g : ℝ[X]} (hall : AllComboRealRooted f g) (hg0 : g ≠ 0) :
    g ≠ 0 ∧ g.Splits :=
  ⟨hg0, by simpa using hall 0 1⟩

end AllComboRealRooted

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
  fun α β ↦ by simpa [hf_def, hg_def, mul_left_comm (C _), ← mul_add,
    splits_mul_iff_right (X_sub_C_ne_zero _) (.X_sub_C _)] using hall α β

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
  | 0 => hall
  | n + 1 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact allComboRealRooted_derivative
        (allComboRealRooted_iterate_derivative hall n)

lemma TDeriv_eq_zero_iff (eps : ℝ) {p : ℝ[X]} :
    TDeriv eps p = 0 ↔ p = 0 := by
  constructor
  · intro hT
    by_cases hp0 : p = 0
    · simp_all
    · by_cases hdeg0 : p.natDegree = 0
      · have hconst : TDeriv eps p = p := by
          rw [eq_C_of_natDegree_eq_zero hdeg0, TDeriv, derivative_C]
          simp
        simp_all
      · cases TDeriv_ne_zero hp0 hT
  · simp_all

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
    · have hp_eq : p = C (p.coeff 0) := by simpa using eq_C_of_natDegree_eq_zero h0
      have hT_eq : TDeriv eps p = p := by
        rw [hp_eq, TDeriv, derivative_C]
        ring
      have hp_root : p.IsRoot a := by lia
      have hcoeff0 : p.coeff 0 = 0 := by
        rw [hp_eq, Polynomial.IsRoot.def, eval_C] at hp_root
        lia
      grind
    · lia
  have hp_not_root : ¬ p.IsRoot a :=
    fun hp_root ↦
      not_isRoot_TDeriv_of_simple_root
        (ne_of_gt heps) hsimple.ne_zero hp_root (hsimple a hp_root) ha
  have hmult_pos : 1 ≤ (TDeriv eps p).rootMultiplicity a :=
    (rootMultiplicity_pos <| TDeriv_ne_zero hsimple.ne_zero).mpr ha
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
  | zero => exact hsimple
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
      _ ≤ max f.natDegree g.natDegree :=
        max_le_max (natDegree_C_mul_le _ _) (natDegree_C_mul_le _ _)
  refine ⟨?_, ?_⟩
  · simpa [iterateTDeriv_linear_combo] using
      (splits_iterateTDeriv
        (eps := eps) (k := max f.natDegree g.natDegree) heps (hall α β))
  by_cases hp : C α * f + C β * g = 0
  · simp [← iterateTDeriv_linear_combo, hp]
  rintro -
  simpa [iterateTDeriv_linear_combo] using
    hasSimpleRoots_iterateTDeriv_of_natDegree_le heps hp (hall α β) hpdeg

namespace AllComboRealRooted

lemma splits {f g : ℝ[X]} (hall : AllComboRealRooted f g) (α β : ℝ) :
    (C α * f + C β * g).Splits :=
  hall α β

lemma comm {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    AllComboRealRooted g f :=
  allComboRealRooted_comm hall

lemma C_mul_left {f g : ℝ[X]} {c : ℝ} (hall : AllComboRealRooted f g) :
    AllComboRealRooted (C c * f) g :=
  allComboRealRooted_C_mul_left hall

lemma C_mul_right {f g : ℝ[X]} {c : ℝ} (hall : AllComboRealRooted f g) :
    AllComboRealRooted f (C c * g) :=
  allComboRealRooted_C_mul_right hall

lemma mul_common_factor {d f g : ℝ[X]} (hall : AllComboRealRooted f g)
    (hd : d.Splits) :
    AllComboRealRooted (d * f) (d * g) :=
  allComboRealRooted_mul_common_factor hd hall

lemma derivative {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    AllComboRealRooted f.derivative g.derivative :=
  allComboRealRooted_derivative hall

lemma iterate_derivative {f g : ℝ[X]} (hall : AllComboRealRooted f g) (n : ℕ) :
    AllComboRealRooted ((Polynomial.derivative^[n]) f) ((Polynomial.derivative^[n]) g) :=
  allComboRealRooted_iterate_derivative hall n

lemma iterateTDeriv {f g : ℝ[X]} (hall : AllComboRealRooted f g)
    {eps : ℝ} (heps : 0 < eps) (n : ℕ) :
    AllComboRealRooted (iterateTDeriv eps n f) (iterateTDeriv eps n g) :=
  allComboRealRooted_iterateTDeriv hall heps n

/-- Convert all-combination real-rootedness to the positive-combination
hypothesis once nonvanishing of positive combinations has been supplied. -/
lemma toPosComboRealRooted_of_pos_combos_ne_zero {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hne : ∀ {lam μ : ℝ}, 0 < lam → 0 < μ → C lam * f + C μ * g ≠ 0) :
    PosComboRealRooted f g := by
  intro lam μ hlam hμ
  exact ⟨hne hlam hμ, hall lam μ⟩

/-- Negating the left member preserves `AllComboRealRooted`. -/
lemma neg_left {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    AllComboRealRooted (-f) g := by
  intro α β
  have h := hall (-α) β
  simp_all

/-- Negating the right member preserves `AllComboRealRooted`. -/
lemma neg_right {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    AllComboRealRooted f (-g) := by
  intro α β
  have h := hall α (-β)
  simp_all

/-- Two positive-leading polynomials of the same degree whose real linear
combinations all split give a `PosComboRealRooted` pair: any strictly positive
combination is nonzero because its top coefficient is a strictly positive
combination of the two (equal-degree) leading coefficients. -/
lemma toPosComboRealRooted_of_sameDegree {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : f.natDegree = g.natDegree) :
    PosComboRealRooted f g := by
  have hf' : 0 < f.leadingCoeff := hf
  have hg' : 0 < g.leadingCoeff := hg
  intro lam μ hlam hμ
  refine ⟨?_, hall lam μ⟩
  intro hzero
  have hpos : 0 < lam * f.leadingCoeff + μ * g.leadingCoeff :=
    add_pos (mul_pos hlam hf') (mul_pos hμ hg')
  have hg2 : g.coeff f.natDegree = g.leadingCoeff := by simp_all
  have hcoeff : (C lam * f + C μ * g).coeff f.natDegree
      = lam * f.leadingCoeff + μ * g.leadingCoeff := by
    rw [coeff_add, coeff_C_mul, coeff_C_mul, hg2]
    simp
  simp_all

/-- If the right member has strictly larger degree and positive leading
coefficient, all-combination real-rootedness upgrades to
`PosComboRealRooted`: the top coefficient of any strictly positive combination
is `μ` times the leading coefficient of `g`, hence nonzero. This is the
succ-degree endpoint conversion. -/
lemma toPosComboRealRooted_of_natDegree_lt {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hg : HasPosLeadingCoeff g)
    (hdeg : f.natDegree < g.natDegree) :
    PosComboRealRooted f g := by
  have hg' : 0 < g.leadingCoeff := hg
  intro lam μ hlam hμ
  refine ⟨?_, hall lam μ⟩
  intro hzero
  have hpos : 0 < μ * g.leadingCoeff := mul_pos hμ hg'
  have hf0 : f.coeff g.natDegree = 0 := coeff_eq_zero_of_natDegree_lt hdeg
  have hcoeff : (C lam * f + C μ * g).coeff g.natDegree = μ * g.leadingCoeff := by
    rw [coeff_add, coeff_C_mul, coeff_C_mul, hf0, mul_zero, zero_add]
    simp
  have hzc : (C lam * f + C μ * g).coeff g.natDegree = 0 := by
    simp_all
  grind

/-- Symmetric to `toPosComboRealRooted_of_natDegree_lt`: if the left member has
strictly larger degree and positive leading coefficient, all-combination
real-rootedness upgrades to `PosComboRealRooted`. -/
lemma toPosComboRealRooted_of_natDegree_gt {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hf : HasPosLeadingCoeff f)
    (hdeg : g.natDegree < f.natDegree) :
    PosComboRealRooted f g := by
  have hf' : 0 < f.leadingCoeff := hf
  intro lam μ hlam hμ
  refine ⟨?_, hall lam μ⟩
  intro hzero
  have hpos : 0 < lam * f.leadingCoeff := mul_pos hlam hf'
  have hg0 : g.coeff f.natDegree = 0 := coeff_eq_zero_of_natDegree_lt hdeg
  have hcoeff : (C lam * f + C μ * g).coeff f.natDegree = lam * f.leadingCoeff := by
    rw [coeff_add, coeff_C_mul, coeff_C_mul, hg0, mul_zero, add_zero]
    simp
  have hzc : (C lam * f + C μ * g).coeff f.natDegree = 0 := by
    simp_all
  grind

end AllComboRealRooted

end RealRooted
