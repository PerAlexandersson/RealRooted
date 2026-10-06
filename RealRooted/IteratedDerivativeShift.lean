import RealRooted.SimpleRoots
import RealRooted.Derivative
import RealRooted.MaWang
import RealRooted.RootContinuity

/-!
# Iterated derivative shifts

This file studies the operator `T_ε p = p - ε p'` and its iterates, including
real-rootedness preservation, interlacing, and continuity facts used in the
Obreschkoff converse route.
-/

open Polynomial

noncomputable section

namespace RealRooted
variable {p : ℝ[X]}

/-- `T_ε p = p - ε p'`. -/
def tDeriv (eps : ℝ) (p : ℝ[X]) : ℝ[X] :=
  p - C eps * p.derivative

/-- `n`-fold iterate of `T_ε`. -/
def iterateTDeriv (eps : ℝ) (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (tDeriv eps)^[n] p

@[simp] lemma iterateTDeriv_zero (eps : ℝ) (p : ℝ[X]) :
    iterateTDeriv eps 0 p = p :=
  rfl

@[simp] lemma iterateTDeriv_succ (eps : ℝ) (n : ℕ) (p : ℝ[X]) :
    iterateTDeriv eps (n + 1) p = tDeriv eps (iterateTDeriv eps n p) := by
  simpa [iterateTDeriv] using (Function.iterate_succ_apply' (tDeriv eps) n p)

@[simp] lemma tDeriv_zero_poly (eps : ℝ) : tDeriv eps (0 : ℝ[X]) = 0 := by simp [tDeriv]

@[simp] lemma iterateTDeriv_zero_poly (eps : ℝ) :
    ∀ n : ℕ, iterateTDeriv eps n (0 : ℝ[X]) = 0
  | 0 => by simp
  | n + 1 => by simp [iterateTDeriv_succ, iterateTDeriv_zero_poly eps n]

@[simp] lemma tDeriv_zero_eps (p : ℝ[X]) :
    tDeriv 0 p = p := by
  simp [tDeriv]

@[simp] lemma iterateTDeriv_zero_eps (n : ℕ) (p : ℝ[X]) :
    iterateTDeriv 0 n p = p := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp_all

lemma tDeriv_of_natDegree_eq_zero (hdeg : p.natDegree = 0) (eps : ℝ) : tDeriv eps p = p := by
  simp [tDeriv, derivative_eq_zero.2 hdeg]

lemma iterateTDeriv_eq_of_natDegree_zero (eps : ℝ) {p : ℝ[X]}
    (hdeg : p.natDegree = 0) :
    ∀ n : ℕ, iterateTDeriv eps n p = p
  | 0 => by simp
  | n + 1 => by
      rw [iterateTDeriv_succ, iterateTDeriv_eq_of_natDegree_zero eps hdeg n]
      have hp_eq : p = C (p.coeff 0) := by simpa using eq_C_of_natDegree_eq_zero hdeg
      rw [hp_eq, tDeriv, derivative_C]
      ring

/-- Coefficient formula for `T_ε`. This is the entry point for the
`ε → 0` coefficientwise continuity used in the Obreschkoff converse. -/
lemma coeff_tDeriv (eps : ℝ) (p : ℝ[X]) (i : ℕ) :
    (tDeriv eps p).coeff i =
      p.coeff i - eps * ((i + 1 : ℕ) : ℝ) * p.coeff (i + 1) := by
  simp [tDeriv, coeff_sub, coeff_C_mul, coeff_derivative]
  ring

/-! ## Multiplicity bounds -/

/-- Multiplicity can drop by at most `1` under `T_ε`. -/
lemma rootMultiplicity_sub_one_le_rootMultiplicity_tDeriv
    {eps : ℝ} {p : ℝ[X]} (a : ℝ)
    (hT_ne : tDeriv eps p ≠ 0) :
    p.rootMultiplicity a - 1 ≤ (tDeriv eps p).rootMultiplicity a := by
  set m := p.rootMultiplicity a
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · lia
  have hp_ne : p ≠ 0 := by
    intro hp0
    simp_all
  have hdvd_p : (X - C a) ^ m ∣ p :=
    (le_rootMultiplicity_iff hp_ne).mp le_rfl
  have hdvd_p' : (X - C a) ^ (m - 1) ∣ p.derivative :=
    pow_sub_one_dvd_derivative_of_pow_dvd hdvd_p
  have hdvd_p_weakened : (X - C a) ^ (m - 1) ∣ p :=
    (pow_dvd_pow _ (Nat.sub_le m 1)).trans hdvd_p
  have hdvd_cmul : (X - C a) ^ (m - 1) ∣ C eps * p.derivative :=
    dvd_mul_of_dvd_right hdvd_p' _
  have hdvd_T : (X - C a) ^ (m - 1) ∣ tDeriv eps p := by
    simpa [tDeriv] using dvd_sub hdvd_p_weakened hdvd_cmul
  exact (le_rootMultiplicity_iff hT_ne).mpr hdvd_T

/-- If `p` has a root of multiplicity `m ≥ 2` at `a`, and `ε ≠ 0`,
    then `(X - C a)^m` does NOT divide `T_ε(p)`.

    The argument: if (X-a)^m ∣ T_ε(p), then since (X-a)^m ∣ p,
    we get (X-a)^m ∣ ε·p'. Since ε ≠ 0, (X-a)^m ∣ p'.
    But the derivative drops multiplicity by exactly 1 (in char 0),
    so rootMultiplicity a p' = m - 1, contradicting (X-a)^m ∣ p'. -/
lemma not_pow_dvd_tDeriv_of_multiple
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (heps : eps ≠ 0)
    (hp_ne : p ≠ 0)
    (hm2 : 2 ≤ p.rootMultiplicity a) :
    ¬ (X - C a) ^ (p.rootMultiplicity a) ∣ tDeriv eps p := by
  set m := p.rootMultiplicity a with hm_def
  intro hdvd_T
  -- (X-a)^m ∣ p (definition of rootMultiplicity)
  have hdvd_p : (X - C a) ^ m ∣ p := pow_rootMultiplicity_dvd p a
  -- (X-a)^m ∣ p - T_ε(p) = ε·p'
  have hdiff_eq : p - tDeriv eps p = C eps * p.derivative := by unfold tDeriv; simp
  have hdvd_eps_p' : (X - C a) ^ m ∣ C eps * p.derivative :=
    hdiff_eq ▸ dvd_sub hdvd_p hdvd_T
  -- ε ≠ 0 ⟹ C ε is a unit ⟹ (X-a)^m ∣ p'
  have hdvd_p' : (X - C a) ^ m ∣ p.derivative := by
    -- C ε is a unit, so (X-a)^m ∣ C ε * p' implies (X-a)^m ∣ p'
    simp_all
  -- p' ≠ 0 (since rootMultiplicity ≥ 2 implies natDegree ≥ 2)
  have hm_le : m ≤ p.natDegree := by
    calc m = p.roots.count a := (count_roots p).symm
    _ ≤ p.roots.card := p.roots.count_le_card a
    _ ≤ p.natDegree := card_roots' p
  have hp'_ne : p.derivative ≠ 0 := by simp; lia
  -- (X-a)^{m} ∤ p' since rootMultiplicity a p' = m - 1 (exact, in char 0)
  have hroot : p.IsRoot a := (rootMultiplicity_pos hp_ne).mp (by lia)
  -- In char 0: (m : ℝ) ≠ 0, so it's in nonZeroDivisors
  have hm_nzd : (↑m : ℝ) ∈ nonZeroDivisors ℝ :=
    IsRegular.mem_nonZeroDivisors
      (IsRegular.of_ne_zero (Nat.cast_ne_zero_of_pos (R := ℝ) (by lia)))
  have hp'_mult : p.derivative.rootMultiplicity a = m - 1 :=
    derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hroot hm_nzd
  -- (X-a)^m ∣ p' means m ≤ rootMultiplicity a p' = m - 1. Contradiction.
  have : m ≤ p.derivative.rootMultiplicity a :=
    (le_rootMultiplicity_iff hp'_ne).mpr hdvd_p'
  lia

/-- Exact multiplicity of T_ε at a multiple root. -/
lemma rootMultiplicity_tDeriv_of_multiple
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (heps : eps ≠ 0)
    (hp_ne : p ≠ 0)
    (hm2 : 2 ≤ p.rootMultiplicity a)
    (hT_ne : tDeriv eps p ≠ 0) :
    (tDeriv eps p).rootMultiplicity a = p.rootMultiplicity a - 1 := by
  set m := p.rootMultiplicity a
  apply le_antisymm
  · -- rootMultiplicity ≤ m - 1 means ¬ (X-a)^{m-1+1} ∣ T_ε(p)
    rw [Polynomial.rootMultiplicity_le_iff hT_ne]
    -- m - 1 + 1 = m since m ≥ 2
    have hm_eq : m - 1 + 1 = m := by lia
    rw [hm_eq]
    exact not_pow_dvd_tDeriv_of_multiple heps hp_ne hm2
  · exact rootMultiplicity_sub_one_le_rootMultiplicity_tDeriv a hT_ne

/-! ## Degree and real-rootedness preservation -/

/-- T_ε preserves the degree (the ε·p' term has strictly lower degree). -/
@[simp] lemma natDegree_tDeriv (eps : ℝ) (p : ℝ[X]) :
    (tDeriv eps p).natDegree = p.natDegree := by
  obtain hp | hp := eq_zero_or_pos p.natDegree
  · simp [tDeriv_of_natDegree_eq_zero hp]
  unfold tDeriv
  have hp'_deg : (C eps * p.derivative).natDegree < p.natDegree := by
    calc (C eps * p.derivative).natDegree
      _ ≤ (C eps).natDegree + p.derivative.natDegree := natDegree_mul_le
      _ = p.derivative.natDegree := by simp [natDegree_C]
      _ = p.natDegree - 1 := p.natDegree_derivative
      _ < p.natDegree := Nat.sub_lt (by lia) one_pos
  rw [natDegree_sub_eq_left_of_natDegree_lt hp'_deg]

/-- `T_ε` keeps the top coefficient unchanged because the derivative term has
strictly smaller degree. This is the key normalization fact behind the
`ε → 0` route in the Obreschkoff converse: after sign-normalizing once, the
regularized family stays sign-normalized without any ε-dependent rescaling. -/
@[simp]
lemma leadingCoeff_tDeriv (eps : ℝ) (p : ℝ[X]) :
    (tDeriv eps p).leadingCoeff = p.leadingCoeff := by
  obtain hp | hp := eq_zero_or_pos p.natDegree
  · simp [tDeriv_of_natDegree_eq_zero hp]
  rw [Polynomial.leadingCoeff, natDegree_tDeriv, tDeriv, coeff_sub]
  have hp'_deg : (C eps * p.derivative).natDegree < p.natDegree := by
    calc
      (C eps * p.derivative).natDegree
          ≤ (C eps).natDegree + p.derivative.natDegree := natDegree_mul_le
      _ = p.derivative.natDegree := by simp [natDegree_C]
      _ = p.natDegree - 1 := p.natDegree_derivative
      _ < p.natDegree := Nat.sub_lt (by lia) one_pos
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hp'_deg, sub_zero, Polynomial.leadingCoeff]

/-- `T_ε` changes the coefficient below the leading term by the expected
multiple of the leading coefficient. -/
lemma nextCoeff_tDeriv (eps : ℝ) (p : ℝ[X]) :
    (tDeriv eps p).nextCoeff =
      p.nextCoeff - eps * (p.natDegree : ℝ) * p.leadingCoeff := by
  by_cases hdeg : p.natDegree = 0
  · simp [hdeg, tDeriv_of_natDegree_eq_zero hdeg]
  · have hpos : 0 < p.natDegree := Nat.pos_of_ne_zero hdeg
    rw [Polynomial.nextCoeff_of_natDegree_pos (by simpa),
      Polynomial.nextCoeff_of_natDegree_pos hpos, natDegree_tDeriv,
      coeff_tDeriv]
    have hsucc : p.natDegree - 1 + 1 = p.natDegree := by lia
    rw [hsucc, Polynomial.coeff_natDegree]

lemma HasPosLeadingCoeff.tDeriv {eps : ℝ} {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (tDeriv eps p) := by
  simpa [HasPosLeadingCoeff] using hp

/-- T_ε of a nonzero polynomial with degree ≥ 1 is nonzero. -/
lemma tDeriv_ne_zero {eps : ℝ} {p : ℝ[X]} (hp : p ≠ 0) :
    tDeriv eps p ≠ 0 := by
  obtain hp | hp := eq_zero_or_pos p.natDegree
  · simpa [tDeriv_of_natDegree_eq_zero hp]
  intro h
  have := natDegree_tDeriv eps p
  simp_all

/-- T_ε preserves real-rootedness when ε > 0.
    Proof: T_ε(p) = 1·p + (-C ε)·p'. Since p' interlaces p (derivative interlacing)
    and (-C ε) evaluates to -ε ≤ 0 at every point, the Ma-Wang theorem gives
    `StrictInterl p (T_ε(p))`, which implies T_ε(p) is real-rooted. -/
private lemma isRealRooted_tDeriv_pos {eps : ℝ} {p : ℝ[X]}
    (heps : 0 < eps)
    (hp : p.Splits)
    (hp_pos : HasPosLeadingCoeff p)
    (hdeg2 : 2 ≤ p.natDegree) : ((tDeriv eps p) ≠ 0 ∧ (tDeriv eps p).Splits) := by
  -- Write T_ε(p) = C 1 * p + C (-eps) * p'
  have hrewrite : tDeriv eps p = C 1 * p + C (-eps) * p.derivative := by simp [tDeriv]; grind
  -- derivative interlaces p
  have hder : Interlaces p.derivative p := derivative_interlaces_of_natDegree_ne_zero hp (by lia)
  -- HasPosLeadingCoeff of p'
  have hp'_pos : HasPosLeadingCoeff p.derivative :=
    hp_pos.derivative (by lia)
  -- HasPosLeadingCoeff of T_ε(p) (same leading coeff as p)
  have hT_pos : HasPosLeadingCoeff (C 1 * p + C (-eps) * p.derivative) := by
    rw [← hrewrite]
    exact hp_pos.tDeriv
  -- degree bounds
  have hdeg_lo : p.natDegree ≤ (C 1 * p + C (-eps) * p.derivative).natDegree := by
    rw [← hrewrite, natDegree_tDeriv eps p]
  have hdeg_hi : (C 1 * p + C (-eps) * p.derivative).natDegree ≤ p.natDegree + 1 := by
    rw [← hrewrite, natDegree_tDeriv eps p]; lia
  -- sign condition: b = C(-eps), b.eval r = -eps ≤ 0 for all r
  have hb_nonpos : ∀ r, p.IsRoot r → (C (-eps)).eval r ≤ 0 := by
    intro r _
    simp [eval_C]
    grind
  -- Apply Ma-Wang
  rw [hrewrite]
  exact
    (strictInterl_of_interlaces_evalCoeff_nonpos
      hder hp'_pos hT_pos hdeg_lo hdeg_hi hb_nonpos).2.1

/-- T_ε is additive. -/
lemma tDeriv_add (eps : ℝ) (p q : ℝ[X]) :
    tDeriv eps (p + q) = tDeriv eps p + tDeriv eps q := by
  ext n
  simp [tDeriv, sub_eq_add_neg, left_distrib]
  ring

/-- T_ε is linear: T_ε(c·p) = c·T_ε(p). -/
lemma tDeriv_C_mul (eps c : ℝ) (p : ℝ[X]) :
    tDeriv eps (C c * p) = C c * tDeriv eps p := by
  simp [tDeriv, mul_sub, mul_left_comm]

lemma iterateTDeriv_add (eps : ℝ) :
    ∀ (n : ℕ) (p q : ℝ[X]),
      iterateTDeriv eps n (p + q) = iterateTDeriv eps n p + iterateTDeriv eps n q
  | 0, p, q => by simp
  | n + 1, p, q => by
      rw [iterateTDeriv_succ, iterateTDeriv_succ, iterateTDeriv_succ, iterateTDeriv_add]
      exact tDeriv_add eps _ _

lemma iterateTDeriv_C_mul (eps c : ℝ) :
    ∀ (n : ℕ) (p : ℝ[X]),
      iterateTDeriv eps n (C c * p) = C c * iterateTDeriv eps n p
  | 0, p => by simp
  | n + 1, p => by
      rw [iterateTDeriv_succ, iterateTDeriv_succ, iterateTDeriv_C_mul]
      exact tDeriv_C_mul eps c _

lemma iterateTDeriv_linear_combo (eps α β : ℝ) (n : ℕ) (f g : ℝ[X]) :
    iterateTDeriv eps n (C α * f + C β * g) =
      C α * iterateTDeriv eps n f + C β * iterateTDeriv eps n g := by
  rw [iterateTDeriv_add, iterateTDeriv_C_mul, iterateTDeriv_C_mul]

private lemma tDeriv_X_sub_C (eps r : ℝ) :
    tDeriv eps (X - C r) = X - C (r + eps) := by
  simp [tDeriv]
  ring

/-- `T_ε` commutes with one derivative step. This is the algebraic reason the
`ε → 0` regularization can be combined with derivative-tower multiplicity
arguments in the Obreschkoff converse. -/
lemma derivative_tDeriv (eps : ℝ) (p : ℝ[X]) :
    (tDeriv eps p).derivative = tDeriv eps p.derivative := by
  simp [tDeriv, derivative_sub]

/-- `T_ε` commutes with every iterated derivative. -/
lemma iterate_derivative_tDeriv (eps : ℝ) (k : ℕ) (p : ℝ[X]) :
    (derivative^[k]) (tDeriv eps p) = tDeriv eps ((derivative^[k]) p) := by
  induction k generalizing p with
  | zero =>
      simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact derivative_tDeriv eps ((derivative^[k]) p)

/-- `iterateTDeriv` commutes with the whole derivative tower. -/
lemma iterate_derivative_iterateTDeriv (eps : ℝ) (n k : ℕ) (p : ℝ[X]) :
    (derivative^[k]) (iterateTDeriv eps n p) =
      iterateTDeriv eps n ((derivative^[k]) p) := by
  induction n generalizing p with
  | zero =>
      simp
  | succ n ih =>
      rw [iterateTDeriv_succ, iterateTDeriv_succ, iterate_derivative_tDeriv, ih]

theorem splits_tDeriv {eps : ℝ} {p : ℝ[X]} (heps : 0 < eps) (hp : p.Splits) :
    (tDeriv eps p).Splits := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  by_cases hdeg2 : 2 ≤ p.natDegree
  · -- degree ≥ 2: use Ma-Wang
    rcases lt_or_gt_of_ne (fun h ↦ hp₀ (leadingCoeff_eq_zero.mp h))
      with hneg | hpos
    · -- negative leading coefficient: T_ε(-p) = -T_ε(p)
      have hneg_pos : HasPosLeadingCoeff (-p) := hasPosLeadingCoeff_neg hneg
      have hT_neg := isRealRooted_tDeriv_pos heps (by simp_all) hneg_pos (by simp_all)
      -- T_ε(-p) = -T_ε(p) since T_ε is linear
      have hlin : tDeriv eps (-p) = -tDeriv eps p := by simp [tDeriv, derivative_neg]; grind
      simp_all
    · exact (isRealRooted_tDeriv_pos heps hp hpos hdeg2).2
  · -- degree ≤ 1: T_ε(p) has same degree as p
    push Not at hdeg2
    -- p.natDegree < 2, so natDegree is 0 or 1
    have hdeg01 : p.natDegree = 0 ∨ p.natDegree = 1 := by lia
    rcases hdeg01 with h0 | h1
    · -- degree 0: p is constant, derivative is 0, tDeriv eps p = p
      have hpc := eq_C_of_natDegree_eq_zero h0
      have : tDeriv eps p = p := by unfold tDeriv; rw [hpc, derivative_C]; simp
      lia
    · -- degree 1: tDeriv preserves degree, so result has degree 1
      exact .of_natDegree_eq_one (by simp_all)

theorem splits_tDeriv_all {eps : ℝ} {p : ℝ[X]} (hp : p.Splits) :
    (tDeriv eps p).Splits := by
  rcases lt_trichotomy eps 0 with heps | heps | heps
  · have hT : (tDeriv (-eps) (p.comp (-X))).Splits :=
      splits_tDeriv (neg_pos.mpr heps) hp.comp_neg_X
    have hcomp : ((tDeriv (-eps) (p.comp (-X))).comp (-X)).Splits :=
      hT.comp_neg_X
    convert hcomp using 1
    simp [tDeriv, Polynomial.derivative_comp, comp_assoc]
  · subst eps
    simpa [tDeriv] using hp
  · exact splits_tDeriv heps hp

/-- A derivative shift translates the sum of the roots by `ε · deg p`.
This orientation invariant is useful when an all-real-combination argument
determines an interlacing pair only up to reversal. -/
lemma roots_sum_tDeriv (eps : ℝ) {p : ℝ[X]} (hp_ne : p ≠ 0)
    (hp_splits : p.Splits) :
    (tDeriv eps p).roots.sum =
      p.roots.sum + eps * (p.natDegree : ℝ) := by
  have hT_splits : (tDeriv eps p).Splits := splits_tDeriv_all hp_splits
  have hp_vieta := hp_splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hT_vieta := hT_splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [nextCoeff_tDeriv, leadingCoeff_tDeriv, hp_vieta] at hT_vieta
  apply mul_left_cancel₀ (leadingCoeff_ne_zero.mpr hp_ne)
  nlinarith

theorem derivative_strictInterl_tDeriv_of_natDegree_one {eps : ℝ} {p : ℝ[X]}
    (hdeg : p.natDegree = 1) :
    StrictInterl p.derivative (tDeriv eps p) := by
  have hTdeg : (tDeriv eps p).natDegree = 1 := by rw [natDegree_tDeriv, hdeg]
  have hbase : StrictInterl (1 : ℝ[X]) (tDeriv eps p) :=
    (interlaces_one_linear hTdeg).toStrictInterl
  have hder_deg : p.derivative.natDegree = 0 := by rw [p.natDegree_derivative, hdeg]
  have hder_C : p.derivative = C (p.derivative.coeff 0) := by
    exact eq_C_of_natDegree_eq_zero hder_deg
  have hder_ne : p.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by rw [hdeg]; norm_num)
  have hcoeff_ne : p.derivative.coeff 0 ≠ 0 := by
    intro hcoeff
    exact hder_ne (by rw [hder_C, hcoeff]; simp)
  have hscaled : StrictInterl (C (p.derivative.coeff 0) * (1 : ℝ[X])) (tDeriv eps p) :=
    StrictInterl.C_mul_left hbase hcoeff_ne
  have hleft : C (p.derivative.coeff 0) * (1 : ℝ[X]) = p.derivative := by
    rw [hder_C]
    simp
  simpa [hleft] using hscaled

/-- Common-left Wagner form for `T_ε`: if `ε ≤ 0`, then `p'` precedes
`p - ε p'`.  This is the Garloff--Wagner Theorem 11 induction step; no
simple-root or coprimeness hypothesis is needed. -/
theorem derivative_strictInterl_tDeriv_of_nonpos {eps : ℝ} {p : ℝ[X]}
    (heps : eps ≤ 0) (hp : p.Splits)
    (hp_pos : HasPosLeadingCoeff p) (hdeg : 1 ≤ p.natDegree) :
    StrictInterl p.derivative (tDeriv eps p) := by
  by_cases hdeg1 : p.natDegree = 1
  · exact derivative_strictInterl_tDeriv_of_natDegree_one hdeg1
  have hdeg2 : 2 ≤ p.natDegree := by lia
  rcases lt_or_eq_of_le heps with heps_neg | heps_zero
  · have hder : Interlaces p.derivative p := derivative_interlaces_of_natDegree_ne_zero hp (by lia)
    have hder_rr : p.derivative ≠ 0 ∧ p.derivative.Splits := hder.2.1
    have hcoef_pos : 0 < -eps := neg_pos.mpr heps_neg
    have hT_eq : tDeriv eps p = p + C (-eps) * p.derivative := by simp [tDeriv, sub_eq_add_neg]
    have hscaled_strictInterl : StrictInterl p.derivative (C (-eps) * p.derivative) :=
      StrictInterl.C_mul_right (StrictInterl.refl hder_rr.1 hder_rr.2) hcoef_pos.ne'
    have hscaled_pos : HasPosLeadingCoeff (C (-eps) * p.derivative) :=
      hasPosLeadingCoeff_C_mul hcoef_pos (hp_pos.derivative (by lia))
    rw [hT_eq]
    exact hder.toStrictInterl.add_of_left hscaled_strictInterl hp_pos hscaled_pos
  · subst eps
    simpa [tDeriv] using (derivative_interlaces_of_natDegree_ne_zero hp (by lia)).toStrictInterl

/-- Common-factor version of the left derivative-shift step.  If
`p = d * q` and `p' = d * r`, then `p' ≪ T_ε p` follows from Wagner (2) for
the quotient pair `r ≪ q` and `r ≪ -ε r`.  Unlike
`derivative_strictInterl_tDeriv_of_nonpos`, no sign condition on the leading
coefficient of `p` is needed. -/
theorem derivative_strictInterl_tDeriv_of_nonpos_of_common_factor {eps : ℝ} {p d q r : ℝ[X]}
    (heps : eps ≤ 0) (hp : p.Splits) (hdeg : 1 ≤ p.natDegree)
    (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    (hp_def : p = d * q) (hder_def : p.derivative = d * r)
    (hrq : StrictInterl r q) (hq_pos : HasPosLeadingCoeff q)
    (hr_pos : HasPosLeadingCoeff r) :
    StrictInterl p.derivative (tDeriv eps p) := by
  by_cases hdeg1 : p.natDegree = 1
  · exact derivative_strictInterl_tDeriv_of_natDegree_one hdeg1
  have hdeg2 : 2 ≤ p.natDegree := by lia
  rcases lt_or_eq_of_le heps with heps_neg | heps_zero
  · have hcoef_pos : 0 < -eps := neg_pos.mpr heps_neg
    have hT_factor : tDeriv eps p = d * (q + C (-eps) * r) := by
      rw [show tDeriv eps p = p + C (-eps) * p.derivative by simp [tDeriv, sub_eq_add_neg],
        hder_def, hp_def]
      ring
    have hscaled_strictInterl : StrictInterl r (C (-eps) * r) :=
      StrictInterl.C_mul_right (StrictInterl.refl hrq.1.1 hrq.1.2) hcoef_pos.ne'
    have hscaled_pos : HasPosLeadingCoeff (C (-eps) * r) :=
      hasPosLeadingCoeff_C_mul hcoef_pos hr_pos
    rw [hT_factor, hder_def]
    exact (hrq.add_of_left hscaled_strictInterl hq_pos hscaled_pos).mul_common_factor
      hd_ne hd_splits
  · subst eps
    simpa [tDeriv] using (derivative_interlaces_of_natDegree_ne_zero hp (by lia)).toStrictInterl

/-- Derivative of an exact power of a linear factor times a quotient. -/
lemma derivative_pow_X_sub_C_mul (a : ℝ) (m : ℕ) (q : ℝ[X]) :
    (((X - C a) ^ m) * q).derivative =
      C (m : ℝ) * (X - C a) ^ (m - 1) * q +
        (X - C a) ^ m * q.derivative := by
  simp [derivative_mul, derivative_pow, derivative_sub]

/-- Remove a shared power of a real linear factor from a `StrictInterl` relation. -/
lemma strictInterl_of_strictInterl_mul_pow_X_sub_C_both (a : ℝ) :
    ∀ n : ℕ, ∀ {f g : ℝ[X]},
      StrictInterl ((X - C a) ^ n * f) ((X - C a) ^ n * g) → StrictInterl f g
  | 0, _f, _g, h => by simpa using h
  | n + 1, f, g, h => by
      have hlin : StrictInterl ((X - C a) * ((X - C a) ^ n * f))
          ((X - C a) * ((X - C a) ^ n * g)) := by
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h
      exact
        strictInterl_of_strictInterl_mul_pow_X_sub_C_both a n
          hlin.of_mul_X_sub_C_both

/-- At the peeled root `a`, the derivative quotient
`m q + (X - a) q'` is nonzero if the remaining quotient is not divisible by
`X - a`. -/
lemma derivative_common_factor_quotient_not_isRoot_of_not_dvd_X_sub_C
    {a : ℝ} {m : ℕ} {q : ℝ[X]}
    (hm : 1 ≤ m) (hq : ¬ (X - C a) ∣ q) :
    ¬ (C (m : ℝ) * q + (X - C a) * q.derivative).IsRoot a := by
  intro hroot
  have hq_eval : q.eval a ≠ 0 := fun hroot => hq ((dvd_iff_isRoot).2 hroot)
  have hm_ne : (m : ℝ) ≠ 0 := by positivity
  have heval :
      (C (m : ℝ) * q + (X - C a) * q.derivative).eval a =
        (m : ℝ) * q.eval a := by
    simp
  have hzero : (m : ℝ) * q.eval a = 0 := by
    rw [← heval]
    exact hroot
  exact hq_eval ((mul_eq_zero.mp hzero).resolve_left hm_ne)

/-- If the remaining quotient `q` has simple roots and is not still divisible
by `X - C a`, then the exact-root quotient pair has no common real root. -/
lemma derivative_common_factor_quotient_no_common_of_hasSimpleRoots
    {a : ℝ} {m : ℕ} {q : ℝ[X]}
    (hm : 1 ≤ m) (hq_nodvd : ¬ (X - C a) ∣ q)
    (hq_simple : HasSimpleRoots q) :
    ∀ x : ℝ, ((X - C a) * q).IsRoot x →
      ¬ (C (m : ℝ) * q + (X - C a) * q.derivative).IsRoot x := by
  intro x hx hquot
  have hx_eval : (x - a) * q.eval x = 0 := by simpa [Polynomial.IsRoot.def] using hx
  rcases mul_eq_zero.mp hx_eval with hxa | hqeval
  · have hxeq : x = a := by linarith
    subst x
    exact derivative_common_factor_quotient_not_isRoot_of_not_dvd_X_sub_C
      hm hq_nodvd hquot
  · have hqroot : q.IsRoot x := hqeval
    have hx_ne : x ≠ a := by
      intro hxa
      subst x
      exact hq_nodvd ((dvd_iff_isRoot).2 hqroot)
    have hder_ne : q.derivative.eval x ≠ 0 :=
      hq_simple.eval_derivative_ne_zero hqroot
    have hquot_eval :
        (C (m : ℝ) * q + (X - C a) * q.derivative).eval x =
          (x - a) * q.derivative.eval x := by
      simp [Polynomial.IsRoot.def] at hqroot
      simp [hqroot]
    have hquot_zero : (x - a) * q.derivative.eval x = 0 := by
      rw [← hquot_eval]
      simpa [Polynomial.IsRoot.def] using hquot
    exact (mul_ne_zero (sub_ne_zero.mpr hx_ne) hder_ne) hquot_zero

/-- Deleting one real linear factor preserves simple roots away from the same
exceptional point. -/
lemma hasSimpleRootsExcept_of_X_sub_C_mul
    {a u : ℝ} {p q : ℝ[X]}
    (hp_factor : p = (X - C u) * q)
    (hp_simple : HasSimpleRootsExcept p a) :
    HasSimpleRootsExcept q a := by
  intro x hx_ne hx_root
  have hp0 : p ≠ 0 := hp_simple.ne_zero
  have hq0 : q ≠ 0 := by
    intro hq0
    exact hp0 (by rw [hp_factor, hq0, mul_zero])
  have hmul_ne : (X - C u : ℝ[X]) * q ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero u) hq0
  have hp_root : p.IsRoot x := by
    rw [hp_factor, Polynomial.IsRoot.def, eval_mul]
    simp [Polynomial.IsRoot.def] at hx_root
    simp [hx_root]
  have hp_mult : p.rootMultiplicity x = 1 :=
    hp_simple x hx_ne hp_root
  have hmul_mult :
      ((X - C u : ℝ[X]) * q).rootMultiplicity x =
        (X - C u : ℝ[X]).rootMultiplicity x + q.rootMultiplicity x :=
    rootMultiplicity_mul hmul_ne
  have hp_mult' : ((X - C u : ℝ[X]) * q).rootMultiplicity x = 1 := by
    simpa [hp_factor] using hp_mult
  rw [hmul_mult, rootMultiplicity_X_sub_C] at hp_mult'
  by_cases hxu : x = u
  · have hq_mult_pos : 0 < q.rootMultiplicity x :=
      (rootMultiplicity_pos hq0).mpr hx_root
    simp [hxu] at hp_mult'
    lia
  · simpa [hxu] using hp_mult'

/-- For positive `eps`, `T_ε p` sits immediately to the right of `p` in the
strict interlacing order. This is the interlacing content hidden inside the
Ma--Wang proof of `isRealRooted_tDeriv`. Keeping it explicit is useful for the
`iterateTDeriv` transport route in the Obreschkoff converse. -/
theorem strictInterl_tDeriv {eps : ℝ} {p : ℝ[X]}
    (heps : 0 < eps) (hp₀ : p ≠ 0)
    (hp : p.Splits) :
    StrictInterl p (tDeriv eps p) := by
  by_cases hdeg2 : 2 ≤ p.natDegree
  · rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp₀) with hneg |
      (hpos : HasPosLeadingCoeff p)
    · have hneg_rr : ((-p) ≠ 0 ∧ (-p).Splits) :=
        ⟨neg_ne_zero.mpr hp₀, by simp_all⟩
      have hneg_pos : HasPosLeadingCoeff (-p) := hasPosLeadingCoeff_neg hneg
      have hrewrite : tDeriv eps (-p) = -tDeriv eps p := by
        simp [tDeriv]
        ring
      have hstrictInterl_neg :
          StrictInterl (-p) (tDeriv eps (-p)) := by
        have hder : Interlaces (-p).derivative (-p) := by
          simpa using
            derivative_interlaces_of_natDegree_ne_zero (f := -p) (by simp_all) (by simp_all; lia)
        have hp'_pos : HasPosLeadingCoeff (-p).derivative := by
          simpa using hneg_pos.derivative (by rw [natDegree_neg]; lia)
        have hrewrite_neg : tDeriv eps (-p) = C 1 * (-p) + C (-eps) * (-p).derivative := by
          simp [tDeriv]
        have hT_pos : HasPosLeadingCoeff (C 1 * (-p) + C (-eps) * (-p).derivative) := by
          rw [← hrewrite_neg]
          exact hneg_pos.tDeriv
        have hdeg_lo : (-p).natDegree ≤ (C 1 * (-p) + C (-eps) * (-p).derivative).natDegree := by
          simp_all
        have hdeg_hi :
            (C 1 * (-p) + C (-eps) * (-p).derivative).natDegree ≤
              (-p).natDegree + 1 := by
          simp_all
        have hb_nonpos : ∀ r, (-p).IsRoot r → (C (-eps)).eval r ≤ 0 := by
          intro r _
          simp [eval_C]
          linarith
        rw [hrewrite_neg]
        exact
          strictInterl_of_interlaces_evalCoeff_nonpos
            hder hp'_pos hT_pos hdeg_lo hdeg_hi hb_nonpos
      have hleft : StrictInterl p (tDeriv eps (-p)) := by
        simpa using StrictInterl.C_mul_left hstrictInterl_neg (by simp : (-1 : ℝ) ≠ 0)
      have hboth : StrictInterl p (tDeriv eps p) := by
        simpa [hrewrite] using StrictInterl.C_mul_right hleft (by simp : (-1 : ℝ) ≠ 0)
      lia
    · have hder : Interlaces p.derivative p :=
        derivative_interlaces_of_natDegree_ne_zero hp (by lia)
      have hp'_pos : HasPosLeadingCoeff p.derivative := hpos.derivative (by lia)
      have hrewrite : tDeriv eps p = C 1 * p + C (-eps) * p.derivative := by
        simp [tDeriv]
        ring
      have hT_pos : HasPosLeadingCoeff (C 1 * p + C (-eps) * p.derivative) := by
        rw [← hrewrite]
        exact hpos.tDeriv
      have hdeg_lo : p.natDegree ≤ (C 1 * p + C (-eps) * p.derivative).natDegree := by
        rw [← hrewrite, natDegree_tDeriv]
      have hdeg_hi : (C 1 * p + C (-eps) * p.derivative).natDegree ≤ p.natDegree + 1 := by
        rw [← hrewrite, natDegree_tDeriv]
        lia
      have hb_nonpos : ∀ r, p.IsRoot r → (C (-eps)).eval r ≤ 0 := by
        intro r _
        simp [eval_C]
        linarith
      rw [hrewrite]
      exact
        strictInterl_of_interlaces_evalCoeff_nonpos
          hder hp'_pos hT_pos hdeg_lo hdeg_hi hb_nonpos
  · push Not at hdeg2
    have hdeg01 : p.natDegree = 0 ∨ p.natDegree = 1 := by lia
    rcases hdeg01 with h0 | h1
    · have hconst : tDeriv eps p = p := by
        rw [eq_C_of_natDegree_eq_zero h0, tDeriv, derivative_C]
        ring
      simpa [hconst] using StrictInterl.refl hp₀ hp
    · obtain ⟨a, b, hp_eq⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one h1.le
      have ha_ne : a ≠ 0 := by
        intro ha0
        simp [hp_eq, ha0] at h1
      let r : ℝ := -b / a
      have hp_factor : p = C a * (X - C r) := by
        ext i
        rcases i with _ | i
        · simp [hp_eq, r]
          grind
        · rcases i with _ | i
          · simp [hp_eq, r]
          · simp [hp_eq, r, Polynomial.coeff_X]
      have hbase : StrictInterl (X - C r) (X - C (r + eps)) := by
        refine
          ⟨isRealRooted_X_sub_C r, isRealRooted_X_sub_C (r + eps), [r],
            [r + eps], ?_, ?_, ?_, ?_, ?_⟩
        · simp
        · simp
        · simp [roots_X_sub_C]
        · simpa [C_add] using (roots_X_sub_C (r + eps)).symm
        · right
          refine ⟨by simp, ?_⟩
          simp [ListAlternates, ListInterlaces]
          linarith
      have hbase' : StrictInterl (X - C r) (tDeriv eps (X - C r)) :=
        by simpa [tDeriv_X_sub_C] using hbase
      have hscaled :
          StrictInterl (C a * (X - C r)) (C a * tDeriv eps (X - C r)) :=
        StrictInterl.C_mul_right (StrictInterl.C_mul_left hbase' ha_ne) ha_ne
      simpa [hp_factor, tDeriv_C_mul] using hscaled

/-! ## Helper: simple roots vanish under T_ε -/

/-- If `a` is a simple root of `p` (multiplicity 1) and `ε ≠ 0`, then `a` is NOT a root
    of `T_ε(p)`. This is because `T_ε(p)(a) = p(a) - ε·p'(a) = -ε·p'(a)`, and a simple
    root means `p'(a) ≠ 0`. -/
lemma not_isRoot_tDeriv_of_simple_root
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (heps : eps ≠ 0)
    (hp_ne : p ≠ 0)
    (hroot : p.IsRoot a)
    (hsimple : p.rootMultiplicity a = 1) :
    ¬ (tDeriv eps p).IsRoot a := by
  -- Factor p = (X - C a) * q with q(a) ≠ 0
  obtain ⟨q, hpq⟩ := dvd_iff_isRoot.mpr hroot
  have hqa : q.eval a ≠ 0 := by
    intro hqa0
    have h2 : (X - C a) ^ 2 ∣ p := by
      rw [hpq, sq]
      exact mul_dvd_mul_left _ (dvd_iff_isRoot.mpr hqa0)
    linarith [(le_rootMultiplicity_iff hp_ne).mpr h2]
  -- p' = q + (X - a) * q' via product rule, so p'(a) = q(a) ≠ 0
  have hp' : p.derivative = q + (X - C a) * q.derivative := by simp_all
  have hp'a : p.derivative.eval a = q.eval a := by simp_all
  -- T_ε(p)(a) = p(a) - ε·p'(a) = 0 - ε·q(a) = -ε·q(a) ≠ 0
  intro hT
  have hT0 : (tDeriv eps p).eval a = 0 := hT
  simp only [tDeriv, eval_sub, eval_mul, eval_C] at hT0
  simp_all

/-- Real-rootedness is preserved by iterating T_ε. -/
lemma iterateTDeriv_ne_zero {eps : ℝ} {p : ℝ[X]} {k : ℕ} (hp : p ≠ 0) :
    iterateTDeriv eps k p ≠ 0 := by
  induction k with
  | zero => simp_all
  | succ n ih =>
    rw [iterateTDeriv_succ]
    exact tDeriv_ne_zero ih

/-- Real-rootedness is preserved by iterating T_ε. -/
lemma splits_iterateTDeriv {eps : ℝ} {p : ℝ[X]} {k : ℕ} (heps : 0 < eps)
    (hp : p.Splits) : (iterateTDeriv eps k p).Splits := by
  induction k with
  | zero => simp_all
  | succ n ih =>
    rw [iterateTDeriv_succ]
    exact splits_tDeriv heps ih

/-- Every real derivative shift preserves splitness under iteration. -/
lemma splits_iterateTDeriv_all {eps : ℝ} {p : ℝ[X]} (hp : p.Splits) :
    ∀ k : ℕ, (iterateTDeriv eps k p).Splits
  | 0 => by simpa
  | k + 1 => by
      rw [iterateTDeriv_succ]
      exact splits_tDeriv_all (splits_iterateTDeriv_all hp k)

/-- The nonnegative derivative regularization `p ↦ p + eps * p'` preserves
coefficientwise nonnegativity under iteration. -/
lemma HasNonnegCoeffs.iterateTDeriv_neg
    {eps : ℝ} (heps : 0 ≤ eps) {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    ∀ k : ℕ, HasNonnegCoeffs (iterateTDeriv (-eps) k p)
  | 0 => by simpa
  | k + 1 => by
      rw [iterateTDeriv_succ]
      intro i
      simp only [tDeriv, coeff_sub, coeff_C_mul, coeff_derivative]
      have hi := hp.iterateTDeriv_neg heps k i
      have hisucc := hp.iterateTDeriv_neg heps k (i + 1)
      simp only [neg_mul, sub_neg_eq_add]
      exact add_nonneg hi (mul_nonneg heps (mul_nonneg hisucc (by positivity)))

/-- Once the number of negative derivative shifts dominates the degree, a
nonzero polynomial with nonnegative coefficients has positive constant term.
Equivalently, the regularization has no zero root. -/
theorem coeff_zero_iterateTDeriv_neg_pos_of_natDegree_le
    {eps : ℝ} (heps : 0 < eps) {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hpne : p ≠ 0) :
    ∀ {k : ℕ}, p.natDegree ≤ k →
      0 < (iterateTDeriv (-eps) k p).coeff 0 := by
  intro k
  induction k generalizing p with
  | zero =>
      intro hdeg
      have hpdeg : p.natDegree = 0 := by lia
      have hlead := hp.pos_leadingCoeff hpne
      rw [iterateTDeriv_eq_of_natDegree_zero (-eps) hpdeg]
      simpa [HasPosLeadingCoeff, leadingCoeff, hpdeg] using hlead
  | succ k ih =>
      intro hdeg
      by_cases hpdeg : p.natDegree = 0
      · have hlead := hp.pos_leadingCoeff hpne
        rw [iterateTDeriv_eq_of_natDegree_zero (-eps) hpdeg]
        simpa [HasPosLeadingCoeff, leadingCoeff, hpdeg] using hlead
      · have hpderne : p.derivative ≠ 0 :=
          (p.derivative_ne_zero).2 hpdeg
        have hpderdeg : p.derivative.natDegree ≤ k := by
          rw [p.natDegree_derivative]
          lia
        have hderpos := ih hp.derivative hpderne hpderdeg
        have hcoeffOne : 0 < (iterateTDeriv (-eps) k p).coeff 1 := by
          have hcomm := iterate_derivative_iterateTDeriv (-eps) k 1 p
          simp only [Function.iterate_one] at hcomm
          have hcoeff := congrArg (fun q : ℝ[X] => q.coeff 0) hcomm
          simp only [coeff_derivative] at hcoeff
          norm_num at hcoeff
          rwa [hcoeff]
        have hcoeffZero : 0 ≤ (iterateTDeriv (-eps) k p).coeff 0 :=
          hp.iterateTDeriv_neg heps.le k 0
        rw [iterateTDeriv_succ, coeff_tDeriv]
        norm_num
        nlinarith

/-- Consecutive `iterateTDeriv` iterates form a generalized Sturm chain: every
step strictly interlaces into the next one. This packages repeated applications
of `strictInterl_tDeriv` in the exact form needed for chain arguments. -/
lemma strictInterl_iterateTDeriv_succ {eps : ℝ} {p : ℝ[X]} {n : ℕ}
    (heps : 0 < eps) (hp₀ : p ≠ 0)
    (hp : p.Splits) :
    StrictInterl (iterateTDeriv eps n p) (iterateTDeriv eps (n + 1) p) := by
  simpa [iterateTDeriv_succ] using
    strictInterl_tDeriv heps (iterateTDeriv_ne_zero hp₀) (splits_iterateTDeriv heps hp)

/-! ## Main theorem -/

/-- Degree is preserved by iterating T_ε. -/
@[simp] lemma natDegree_iterateTDeriv (eps : ℝ) (p : ℝ[X]) (k : ℕ) :
    (iterateTDeriv eps k p).natDegree = p.natDegree := by induction k <;> simp [*]

/-- Iterating `T_ε` preserves the leading coefficient as well. -/
@[simp] lemma leadingCoeff_iterateTDeriv (eps : ℝ) (p : ℝ[X]) (k : ℕ) :
    (iterateTDeriv eps k p).leadingCoeff = p.leadingCoeff := by induction k <;> simp [*]

/-- Positive-leading normalization is preserved exactly along `iterateTDeriv`.
This is the form most useful in converse/continuity arguments. -/
@[simp]
lemma hasPosLeadingCoeff_iterateTDeriv {eps : ℝ} {p : ℝ[X]} {k : ℕ} :
    HasPosLeadingCoeff (iterateTDeriv eps k p) ↔ HasPosLeadingCoeff p := by
  simp [HasPosLeadingCoeff]

lemma monic_iterateTDeriv {eps : ℝ} {p : ℝ[X]} {k : ℕ} (hp_monic : p.Monic) :
    (iterateTDeriv eps k p).Monic := by
  rw [Monic, leadingCoeff_iterateTDeriv, hp_monic.leadingCoeff]

/-- Monic normalization is compatible with `iterateTDeriv`: because the leading
coefficient is preserved exactly, one can scale by the inverse of the original
leading coefficient before applying root-continuity arguments. This is the
normalization package needed by the current Obreschkoff closure route. -/
lemma monic_normalization_iterateTDeriv {eps : ℝ} {p : ℝ[X]} {k : ℕ} (hp : p ≠ 0) :
    (C p.leadingCoeff⁻¹ * iterateTDeriv eps k p).Monic := by
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  simp_all

/-- For fixed `n`, `p`, and `i`, the `i`th coefficient of `iterateTDeriv eps n p`
depends continuously on `eps`. This packages the purely algebraic recursion in a
form that can be fed directly into root-continuity arguments. -/
lemma continuous_coeff_iterateTDeriv (n : ℕ) (p : ℝ[X]) (i : ℕ) :
    Continuous fun eps : ℝ => (iterateTDeriv eps n p).coeff i := by
  induction n generalizing i with
  | zero =>
      simpa using continuous_const
  | succ n ih =>
      have hrewrite :
          (fun eps : ℝ => (iterateTDeriv eps (n + 1) p).coeff i) =
            fun eps : ℝ =>
              (iterateTDeriv eps n p).coeff i -
                eps * ((i + 1 : ℕ) : ℝ) * (iterateTDeriv eps n p).coeff (i + 1) := by
        funext eps
        rw [iterateTDeriv_succ, coeff_tDeriv]
      rw [hrewrite]
      exact (ih i).sub
        ((continuous_id.mul continuous_const).mul (ih (i + 1)))

/-- Coefficientwise continuity of `iterateTDeriv` at `eps = 0`. Since
`iterateTDeriv 0 n = id`, every fixed coefficient approaches the original
coefficient as `eps → 0`. We record this as a `ContinuousAt` fact to keep the
API lightweight for later root-continuity arguments. -/
lemma continuousAt_coeff_iterateTDeriv_zero (n : ℕ) (p : ℝ[X]) (i : ℕ) :
    ContinuousAt (fun eps : ℝ => (iterateTDeriv eps n p).coeff i) 0 := by
  have hcont0 : ContinuousAt (fun eps : ℝ => (iterateTDeriv eps n p).coeff i) 0 :=
    (continuous_coeff_iterateTDeriv n p i).continuousAt
  lia

/-- For fixed `n`, `p`, and `x`, the evaluation
`(iterateTDeriv eps n p).eval x` depends continuously on `eps`. This is the
fixed-point analogue of coefficientwise continuity, and it is the exact local
input needed to keep root evaluations away from `0` for small `eps`. -/
lemma continuous_eval_iterateTDeriv (n : ℕ) (p : ℝ[X]) (x : ℝ) :
    Continuous fun eps : ℝ => (iterateTDeriv eps n p).eval x := by
  simp only [eval_eq_sum_range, natDegree_iterateTDeriv]
  exact continuous_finsetSum _ fun i _ =>
    (continuous_coeff_iterateTDeriv n p i).mul continuous_const

/-- Evaluation at a fixed real point is continuous at `eps = 0` along the
`iterateTDeriv` family. -/
lemma continuousAt_eval_iterateTDeriv_zero (n : ℕ) (p : ℝ[X]) (x : ℝ) :
    ContinuousAt (fun eps : ℝ => (iterateTDeriv eps n p).eval x) 0 := by
  have hcont0 : ContinuousAt (fun eps : ℝ => (iterateTDeriv eps n p).eval x) 0 :=
    (continuous_eval_iterateTDeriv n p x).continuousAt
  lia

/-- Joint continuity of the `iterateTDeriv` evaluation map in both the shift
parameter `eps` and the evaluation point `x`. This is the local form needed to
exclude perturbed roots from a whole neighborhood of a fixed non-root. -/
lemma continuous_eval_iterateTDeriv_joint (n : ℕ) (p : ℝ[X]) :
    Continuous fun z : ℝ × ℝ => (iterateTDeriv z.1 n p).eval z.2 := by
  simp only [eval_eq_sum_range, natDegree_iterateTDeriv]
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_coeff_iterateTDeriv n p i).comp continuous_fst).mul
      (continuous_snd.pow i)

/-- Joint continuity of `eval (iterateTDeriv eps n p)` at the base point
`(0, x)`. -/
lemma continuousAt_eval_iterateTDeriv_joint_zero (n : ℕ) (p : ℝ[X]) (x : ℝ) :
    ContinuousAt (fun z : ℝ × ℝ => (iterateTDeriv z.1 n p).eval z.2) (0, x) := by
  have hcont0 :
      ContinuousAt (fun z : ℝ × ℝ => (iterateTDeriv z.1 n p).eval z.2) (0, x) :=
    (continuous_eval_iterateTDeriv_joint n p).continuousAt
  lia

/-- Epsilon-delta form of evaluation continuity at `eps = 0` for the
`iterateTDeriv` family. -/
lemma exists_delta_for_eval_iterateTDeriv_at_zero
    (n : ℕ) (p : ℝ[X]) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, ‖eps‖ < δ →
      ‖(iterateTDeriv eps n p).eval x - p.eval x‖ < ε := by
  have hcont := continuousAt_eval_iterateTDeriv_zero n p x
  rw [Metric.continuousAt_iff] at hcont
  rcases hcont ε hε with ⟨δ, hδ, hclose⟩
  refine ⟨δ, hδ, ?_⟩
  intro eps heps
  have heps' : dist eps 0 < δ := by simp_all
  simpa [dist_eq_norm, iterateTDeriv_zero_eps] using hclose heps'

/-- Epsilon-delta form of the joint continuity statement at `(0, x)`. -/
lemma exists_delta_for_eval_iterateTDeriv_joint_at_zero
    (n : ℕ) (p : ℝ[X]) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃z : ℝ × ℝ⦄, dist z (0, x) < δ →
      ‖(iterateTDeriv z.1 n p).eval z.2 - p.eval x‖ < ε := by
  have hcont := continuousAt_eval_iterateTDeriv_joint_zero n p x
  rw [Metric.continuousAt_iff] at hcont
  rcases hcont ε hε with ⟨δ, hδ, hclose⟩
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  simpa [dist_eq_norm, iterateTDeriv_zero_eps] using hclose hz

lemma pos_of_norm_sub_lt_half_of_pos {a b : ℝ}
    (ha : 0 < a) (hab : ‖b - a‖ < a / 2) :
    0 < b := by
  have hab' : -(a / 2) < b - a ∧ b - a < a / 2 := by
    simpa [Real.norm_eq_abs] using (abs_lt.mp hab)
  linarith

/-- If `p.eval x ≠ 0`, then for sufficiently small `eps`, the value of
`(iterateTDeriv eps n p).eval x` has the same sign as `p.eval x`. This is the
local nonvanishing/sign-stability theorem used in the `ε → 0` closure route. -/
lemma exists_delta_eval_mul_pos_iterateTDeriv_at_zero
    (n : ℕ) {p : ℝ[X]} {x : ℝ}
    (hx : p.eval x ≠ 0) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, ‖eps‖ < δ →
      0 < (iterateTDeriv eps n p).eval x * p.eval x := by
  have hnorm_pos : 0 < ‖p.eval x‖ := norm_pos_iff.mpr hx
  obtain ⟨δ, hδ, hclose⟩ :=
    exists_delta_for_eval_iterateTDeriv_at_zero n p x (show 0 < ‖p.eval x‖ / 2 by simp_all)
  refine ⟨δ, hδ, ?_⟩
  intro eps heps
  have hclose' :
      ‖(iterateTDeriv eps n p).eval x - p.eval x‖ < ‖p.eval x‖ / 2 :=
    hclose heps
  rcases lt_or_gt_of_ne hx with hx_neg | hx_pos
  · have hneg_iter : (iterateTDeriv eps n p).eval x < 0 := by
      have hneg_norm :
          ‖-(iterateTDeriv eps n p).eval x - (-p.eval x)‖ =
            ‖(iterateTDeriv eps n p).eval x - p.eval x‖ := by
        rw [sub_eq_add_neg, neg_neg]
        have hEq :
            -(iterateTDeriv eps n p).eval x + p.eval x =
              -((iterateTDeriv eps n p).eval x - p.eval x) := by
          ring
        rw [hEq, norm_neg]
      have hclose_neg0 :
          ‖-(iterateTDeriv eps n p).eval x - (-p.eval x)‖ < ‖p.eval x‖ / 2 := by
        lia
      have hclose_neg :
          ‖-(iterateTDeriv eps n p).eval x - (-p.eval x)‖ < (-p.eval x) / 2 := by
        simpa [Real.norm_eq_abs, abs_of_neg hx_neg] using hclose_neg0
      have hpos_neg_iter : 0 < -(iterateTDeriv eps n p).eval x :=
        pos_of_norm_sub_lt_half_of_pos (by simp_all) hclose_neg
      linarith
    exact mul_pos_of_neg_of_neg hneg_iter hx_neg
  · have hpos_iter : 0 < (iterateTDeriv eps n p).eval x :=
      pos_of_norm_sub_lt_half_of_pos hx_pos
        (by simpa [Real.norm_eq_abs, abs_of_pos hx_pos] using hclose')
    simp_all

/-- Two-variable sign stability near `(eps, x) = (0, x₀)`: if `p(x₀) ≠ 0`, then
for all sufficiently small joint perturbations of the shift parameter and the
evaluation point, the value of `iterateTDeriv eps n p` keeps the sign of
`p(x₀)`. -/
lemma exists_delta_eval_mul_pos_iterateTDeriv_joint_at_zero
    (n : ℕ) {p : ℝ[X]} {x : ℝ}
    (hx : p.eval x ≠ 0) :
    ∃ δ > 0, ∀ ⦃z : ℝ × ℝ⦄, dist z (0, x) < δ →
      0 < (iterateTDeriv z.1 n p).eval z.2 * p.eval x := by
  have hnorm_pos : 0 < ‖p.eval x‖ := norm_pos_iff.mpr hx
  obtain ⟨δ, hδ, hclose⟩ :=
    exists_delta_for_eval_iterateTDeriv_joint_at_zero n p x
      (show 0 < ‖p.eval x‖ / 2 by simp_all)
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have hclose' :
      ‖(iterateTDeriv z.1 n p).eval z.2 - p.eval x‖ < ‖p.eval x‖ / 2 :=
    hclose hz
  rcases lt_or_gt_of_ne hx with hx_neg | hx_pos
  · have hneg_iter : (iterateTDeriv z.1 n p).eval z.2 < 0 := by
      have hneg_norm :
          ‖-(iterateTDeriv z.1 n p).eval z.2 - (-p.eval x)‖ =
            ‖(iterateTDeriv z.1 n p).eval z.2 - p.eval x‖ := by
        rw [sub_eq_add_neg, neg_neg]
        have hEq :
            -(iterateTDeriv z.1 n p).eval z.2 + p.eval x =
              -((iterateTDeriv z.1 n p).eval z.2 - p.eval x) := by
          ring
        rw [hEq, norm_neg]
      have hclose_neg0 :
          ‖-(iterateTDeriv z.1 n p).eval z.2 - (-p.eval x)‖ < ‖p.eval x‖ / 2 := by
        lia
      have hclose_neg :
          ‖-(iterateTDeriv z.1 n p).eval z.2 - (-p.eval x)‖ < (-p.eval x) / 2 := by
        simpa [Real.norm_eq_abs, abs_of_neg hx_neg] using hclose_neg0
      have hpos_neg_iter : 0 < -(iterateTDeriv z.1 n p).eval z.2 :=
        pos_of_norm_sub_lt_half_of_pos (by simp_all) hclose_neg
      linarith
    exact mul_pos_of_neg_of_neg hneg_iter hx_neg
  · have hpos_iter : 0 < (iterateTDeriv z.1 n p).eval z.2 :=
      pos_of_norm_sub_lt_half_of_pos hx_pos
        (by simpa [Real.norm_eq_abs, abs_of_pos hx_pos] using hclose')
    simp_all

/-- If `x` is not a root of `p`, then `x` stays away from the roots of the
`iterateTDeriv` regularizations for all sufficiently small `eps`. -/
lemma exists_delta_not_isRoot_iterateTDeriv_at_point
    (n : ℕ) {p : ℝ[X]} {x : ℝ}
    (hx : ¬ p.IsRoot x) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, ‖eps‖ < δ →
      ¬ (iterateTDeriv eps n p).IsRoot x := by
  obtain ⟨δ, hδ, hsign⟩ :=
    exists_delta_eval_mul_pos_iterateTDeriv_at_zero n
      (show p.eval x ≠ 0 by simp_all)
  refine ⟨δ, hδ, ?_⟩
  intro eps heps hroot
  have hprod : 0 < (iterateTDeriv eps n p).eval x * p.eval x := hsign heps
  simp_all

/-- Local neighborhood version of `exists_delta_not_isRoot_iterateTDeriv_at_point`:
if `x` is not a root of `p`, then no sufficiently small joint perturbation of
the shift parameter and the evaluation point can hit a root of the regularized
polynomial. -/
lemma exists_delta_not_isRoot_iterateTDeriv_near_point
    (n : ℕ) {p : ℝ[X]} {x : ℝ}
    (hx : ¬ p.IsRoot x) :
    ∃ δ > 0, ∀ ⦃z : ℝ × ℝ⦄, dist z (0, x) < δ →
      ¬ (iterateTDeriv z.1 n p).IsRoot z.2 := by
  obtain ⟨δ, hδ, hsign⟩ :=
    exists_delta_eval_mul_pos_iterateTDeriv_joint_at_zero n
      (show p.eval x ≠ 0 by simp_all)
  refine ⟨δ, hδ, ?_⟩
  intro z hz hroot
  have hprod : 0 < (iterateTDeriv z.1 n p).eval z.2 * p.eval x := hsign hz
  simp_all

/-- Epsilon-delta form of coefficientwise continuity at `eps = 0` for a single
coefficient of `iterateTDeriv`. -/
lemma exists_delta_for_coeff_iterateTDeriv_at_zero
    (n : ℕ) (p : ℝ[X]) (i : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, ‖eps‖ < δ →
      ‖(iterateTDeriv eps n p).coeff i - p.coeff i‖ < ε := by
  have hcont := continuousAt_coeff_iterateTDeriv_zero n p i
  rw [Metric.continuousAt_iff] at hcont
  rcases hcont ε hε with ⟨δ, hδ, hclose⟩
  refine ⟨δ, hδ, ?_⟩
  intro eps heps
  have heps' : dist eps 0 < δ := by simp_all
  simpa [dist_eq_norm, iterateTDeriv_zero_eps] using hclose heps'

private lemma exists_delta_for_coeffs_lt_iterateTDeriv_at_zero
    (n : ℕ) (p : ℝ[X]) :
    ∀ m : ℕ, ∀ {ε : ℝ}, 0 < ε →
      ∃ δ > 0, ∀ ⦃eps : ℝ⦄, ‖eps‖ < δ →
        ∀ i : ℕ, i < m →
          ‖(iterateTDeriv eps n p).coeff i - p.coeff i‖ < ε
  | 0, ε, hε => by
      grind
  | m + 1, ε, hε => by
      obtain ⟨δtail, hδtail, htail⟩ :=
        exists_delta_for_coeffs_lt_iterateTDeriv_at_zero n p m hε
      obtain ⟨δlast, hδlast, hlast⟩ :=
        exists_delta_for_coeff_iterateTDeriv_at_zero n p m hε
      grind

/-- Uniform finite-range coefficient closeness for `iterateTDeriv eps n p`
when `eps` is small. This is the exact format needed before invoking the
generic root-continuity lemmas. -/
lemma exists_delta_for_coeffs_iterateTDeriv_at_zero
    (n : ℕ) (p : ℝ[X]) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, ‖eps‖ < δ →
      ∀ i : ℕ, i < p.natDegree + 1 →
        ‖(iterateTDeriv eps n p).coeff i - p.coeff i‖ < ε := by
  simpa using
    exists_delta_for_coeffs_lt_iterateTDeriv_at_zero n p (p.natDegree + 1) hε

/-- All coefficients of `iterateTDeriv eps n p` are uniformly close to those of
`p` once `eps` is small enough. Above `natDegree p`, both sides are identically
zero because `iterateTDeriv` preserves `natDegree`. -/
lemma exists_delta_for_all_coeffs_iterateTDeriv_at_zero
    (n : ℕ) (p : ℝ[X]) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, ‖eps‖ < δ →
      ∀ i : ℕ, ‖(iterateTDeriv eps n p).coeff i - p.coeff i‖ < ε := by
  obtain ⟨δ, hδ, hclose⟩ := exists_delta_for_coeffs_iterateTDeriv_at_zero n p hε
  refine ⟨δ, hδ, ?_⟩
  intro eps heps i
  by_cases hi : i < p.natDegree + 1
  · simp_all
  · have hdeg_lt : p.natDegree < i := Nat.lt_of_not_ge (by lia)
    have hp_coeff : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt hdeg_lt
    have hiter_coeff : (iterateTDeriv eps n p).coeff i = 0 := by
      rw [coeff_eq_zero_of_natDegree_lt]
      simpa using hdeg_lt
    simp_all

/-- For sufficiently small positive `eps`, every prescribed real root of a
monic real-rooted polynomial persists as a nearby real root of the
`iterateTDeriv` regularization. This is the concrete continuity bridge needed
for the `ε → 0` Obreschkoff transport route. -/
theorem exists_delta_and_real_root_near_iterateTDeriv
    (n : ℕ) {p : ℝ[X]} {a ε : ℝ}
    (ha : p.IsRoot a)
    (hp : p.Splits) (hp_monic : p.Monic)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, 0 < eps → ‖eps‖ < δ →
      ∃ b ∈ (iterateTDeriv eps n p).roots,
        ‖a - b‖ < ((p.natDegree + 1) * ε) ^ ((p.natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  obtain ⟨δ, hδ, hcoeff⟩ := exists_delta_for_all_coeffs_iterateTDeriv_at_zero n p hε
  refine ⟨δ, hδ, ?_⟩
  intro eps heps_pos heps_small
  exact exists_roots_norm_sub_lt_of_norm_coeff_sub_lt hε ha hp_monic (monic_iterateTDeriv hp_monic)
    (natDegree_iterateTDeriv ..)
    (hcoeff heps_small)
    (splits_iterateTDeriv heps_pos hp)

/-- Monic normalization is only a proof artifact in the `iterateTDeriv`
continuity route: for any nonzero real-rooted polynomial, each prescribed real
root persists under sufficiently small positive `iterateTDeriv` regularization.
This repackages the monic theorem above so the Obreschkoff converse can use it
after a single sign-normalization step, without having to rebuild the monic
scaling argument at each call site. -/
theorem exists_delta_and_real_root_near_iterateTDeriv_of_isRealRooted
    (n : ℕ) {p : ℝ[X]} {a ε : ℝ}
    (ha : p.IsRoot a)
    (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, 0 < eps → ‖eps‖ < δ →
      ∃ b : ℝ, (iterateTDeriv eps n p).IsRoot b ∧
        ‖a - b‖ < ((p.natDegree + 1) * ε) ^ ((p.natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  let c : ℝ := p.leadingCoeff⁻¹
  let p₀ : ℝ[X] := C c * p
  have hc_ne : c ≠ 0 :=
    inv_ne_zero (leadingCoeff_ne_zero.mpr hp_ne)
  have hp₀_monic : p₀.Monic := by
    unfold p₀ c
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hp₀_deg : p₀.natDegree = p.natDegree := by
    unfold p₀ c
    rw [natDegree_C_mul hc_ne]
  have ha₀ : p₀.IsRoot a := by
    have ha_eval : p.eval a = 0 := by simp_all
    have hp₀_eval : p₀.eval a = 0 := by simp [p₀, ha_eval]
    simp_all
  obtain ⟨δ, hδ, hnear⟩ :=
    exists_delta_and_real_root_near_iterateTDeriv n ha₀ (by simp_all [p₀]) hp₀_monic hε
  refine ⟨δ, hδ, ?_⟩
  intro eps heps_pos heps_small
  obtain ⟨b, hb_root₀, hb_dist⟩ := hnear heps_pos heps_small
  have hb_eval₀ : (iterateTDeriv eps n p₀).eval b = 0 := by simp_all
  have hb_eval_scaled : (C c * iterateTDeriv eps n p).eval b = 0 := by
    simpa [p₀, iterateTDeriv_C_mul] using hb_eval₀
  rw [Polynomial.eval_mul, Polynomial.eval_C] at hb_eval_scaled
  have hb_eval : (iterateTDeriv eps n p).eval b = 0 := by simp_all
  refine ⟨b, by simp_all, ?_⟩
  lia

/-- The nearby-root theorem is stable under passing to any iterated derivative,
because `iterateTDeriv` commutes with the derivative tower. This is the form
needed for multiplicity-cluster arguments: every original derivative root of
order `k` persists as a nearby derivative root of the regularized family. -/
theorem exists_delta_and_real_root_near_iterateTDeriv_of_isRealRooted_iterate_derivative
    (n k : ℕ) {p : ℝ[X]} {a ε : ℝ}
    (ha : ((derivative^[k]) p).IsRoot a)
    (hp_ne : ((derivative^[k]) p) ≠ 0) (hp_splits : ((derivative^[k]) p).Splits)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, 0 < eps → ‖eps‖ < δ →
      ∃ b : ℝ, ((derivative^[k]) (iterateTDeriv eps n p)).IsRoot b ∧
        ‖a - b‖ <
          ((((derivative^[k]) p).natDegree + 1) * ε) ^
            ((((derivative^[k]) p).natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  obtain ⟨δ, hδ, hnear⟩ :=
    exists_delta_and_real_root_near_iterateTDeriv_of_isRealRooted
      (n := n) (p := (derivative^[k]) p) ha hp_ne hp_splits hε
  refine ⟨δ, hδ, ?_⟩
  intro eps heps_pos heps_small
  obtain ⟨b, hb_root, hb_dist⟩ := hnear heps_pos heps_small
  refine ⟨b, ?_, hb_dist⟩
  simpa [iterate_derivative_iterateTDeriv] using hb_root

/-- Root-multiplicity wrapper for the iterated-derivative nearby-root theorem.
If `k < rootMultiplicity a p`, then the `k`-th derivative already vanishes at
`a`, so the regularized family has a nearby root in the same derivative level. -/
theorem exists_delta_and_real_root_near_iterateTDeriv_of_lt_rootMultiplicity
    (n k : ℕ) {p : ℝ[X]} {a ε : ℝ}
    (ha : k < p.rootMultiplicity a)
    (hp_ne : ((derivative^[k]) p) ≠ 0) (hp_splits : ((derivative^[k]) p).Splits)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, 0 < eps → ‖eps‖ < δ →
      ∃ b : ℝ, ((derivative^[k]) (iterateTDeriv eps n p)).IsRoot b ∧
        ‖a - b‖ <
          ((((derivative^[k]) p).natDegree + 1) * ε) ^
            ((((derivative^[k]) p).natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  apply exists_delta_and_real_root_near_iterateTDeriv_of_isRealRooted_iterate_derivative
    (n := n) (k := k) (p := p) (a := a) (ε := ε)
  · exact isRoot_iterate_derivative_of_lt_rootMultiplicity ha
  · simp_all
  · grind
  · grind

/-- If `rootMultiplicity a p ≥ 1` and `rootMultiplicity a (T_ε p) ≥ 2`, then
    `rootMultiplicity a p ≥ 2` and the exact formula applies. In other words,
    a simple root can't produce a double root (it vanishes instead). -/
lemma rootMultiplicity_ge_two_of_tDeriv_ge_two
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (heps : 0 < eps) (hp_ne : p ≠ 0)
    (hroot : 1 ≤ p.rootMultiplicity a)
    (hm : 2 ≤ (tDeriv eps p).rootMultiplicity a) :
    2 ≤ p.rootMultiplicity a := by
  by_contra h
  push Not at h
  have h1 : p.rootMultiplicity a = 1 := by lia
  have hroot_a : p.IsRoot a := (rootMultiplicity_pos hp_ne).mp (by lia)
  have hnotroot := not_isRoot_tDeriv_of_simple_root (ne_of_gt heps) hp_ne hroot_a h1
  have hroot2 : (tDeriv eps p).IsRoot a :=
    (rootMultiplicity_pos (tDeriv_ne_zero hp_ne)).mp (by lia)
  lia

lemma deriv2_mul_lt_deriv_sq_at_non_root {p : ℝ[X]} {a : ℝ} (hp : p.Splits)
    (hdeg : 1 ≤ p.natDegree)
    (ha : p.eval a ≠ 0) :
    p.derivative.derivative.eval a * p.eval a < p.derivative.eval a ^ 2 := by
  -- Strong induction on degree
  suffices ∀ (n : ℕ) (q : ℝ[X]), q.natDegree = n → q.Splits → 1 ≤ n →
      q.eval a ≠ 0 →
      q.derivative.derivative.eval a * q.eval a < q.derivative.eval a ^ 2 from
    this p.natDegree p rfl hp hdeg ha
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro q hq_deg hq_rr hq_deg_pos hq_eval
    have hq₀ : q ≠ 0 := by rintro rfl; simp_all
  -- Get a root r of q (exists since degree ≥ 1 and real-rooted)
    have hroots_pos : 0 < q.roots.card := by
      rw [card_roots_of_splits hq_rr]
      lia
    obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
    have hr_root : q.IsRoot r := (mem_roots hq₀).mp hr
    -- Factor: q = (X - C r) * t
    obtain ⟨t, hqt⟩ := dvd_iff_isRoot.mpr hr_root
    have ht_ne : t ≠ 0 := right_ne_zero_of_mul (hqt ▸ hq₀)
    have ht_deg : t.natDegree = n - 1 := by
      have := congr_arg natDegree hqt
      rw [natDegree_mul (X_sub_C_ne_zero r) ht_ne, natDegree_X_sub_C] at this
      lia
    -- t is real-rooted
    have ht_rr : t.Splits := by
      simpa [hqt, splits_mul_iff_right (X_sub_C_ne_zero _) (.X_sub_C _)] using hq_rr
    -- a ≠ r (since q(a) ≠ 0 but q(r) = 0)
    have har : a - r ≠ 0 := by simp_all
    -- t(a) ≠ 0
    have ht_eval : t.eval a ≠ 0 := by simp_all
    -- Derivatives of q in terms of t
    -- q = (X - C r) * t, so q' = t + (X - C r) * t'
    have hq' : q.derivative = t + (X - C r) * t.derivative := by simp_all
    -- q'' = t' + t' + (X - C r) * t'' (from differentiating q')
    have hq'' : q.derivative.derivative =
        t.derivative + t.derivative + (X - C r) * t.derivative.derivative := by
      rw [hq']
      simp only [derivative_add, derivative_mul, derivative_sub, derivative_X, derivative_C,
        sub_zero, one_mul]
      ring
    -- Evaluate at a
    set ar := a - r
    set ta := t.eval a
    set t'a := t.derivative.eval a
    set t''a := t.derivative.derivative.eval a
    have hqa : q.eval a = ar * ta := by rw [hqt, eval_mul, eval_sub, eval_X, eval_C]
    have hq'a : q.derivative.eval a = ta + ar * t'a := by
      rw [hq', eval_add, eval_mul, eval_sub, eval_X, eval_C]
    have hq''a : q.derivative.derivative.eval a = t'a + t'a + ar * t''a := by
      rw [hq'', eval_add, eval_add, eval_mul, eval_sub, eval_X, eval_C]
    -- Key algebraic identity:
    -- q''(a) * q(a) - q'(a)² = ar² * (t''a * ta - t'a²) - ta²
    have hident : q.derivative.derivative.eval a * q.eval a -
        q.derivative.eval a ^ 2 =
        ar ^ 2 * (t''a * ta - t'a ^ 2) - ta ^ 2 := by
      grind
    -- Show the RHS is negative
    rw [show q.derivative.derivative.eval a * q.eval a <
        q.derivative.eval a ^ 2 ↔
        q.derivative.derivative.eval a * q.eval a -
        q.derivative.eval a ^ 2 < 0 from by simp]
    rw [hident]
    -- Two cases: n = 1 (t is constant) or n ≥ 2 (use IH)
    by_cases hn1 : n = 1
    · -- n = 1: t has degree 0, t' = t'' = 0
      have ht_deg0 : t.natDegree = 0 := by lia
      have ht'_zero : t.derivative = 0 := by simp_all
      have ht'a_zero : t'a = 0 := by grind
      have ht''a_zero : t''a = 0 := by simp_all
      rw [ht'a_zero, ht''a_zero]
      simp only [zero_mul, zero_sub]
      linarith [sq_pos_of_ne_zero ht_eval]
    · -- n ≥ 2: use IH on t
      have ht_ih := ih (n - 1) (by lia) t ht_deg ht_rr (by lia) ht_eval
      have h_neg : t''a * ta - t'a ^ 2 < 0 := by grind
      have h1 : ar ^ 2 * (t''a * ta - t'a ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ar) (le_of_lt h_neg)
      linarith [sq_pos_of_ne_zero ht_eval]

/-- `T_ε` cannot create double roots at non-roots of a real-rooted polynomial.

If `p` is real-rooted with `p(a) ≠ 0`, then `rootMultiplicity a (T_ε p) ≤ 1`.

Proof: if `T_ε p` had a double root at `a`, then `p(a) = ε·p'(a)` and `p'(a) = ε·p''(a)`,
giving `p''(a)·p(a) = p'(a)²`. But `deriv2_mul_lt_deriv_sq_at_non_root` says
`p''(a)·p(a) < p'(a)²`. Contradiction. -/
lemma rootMultiplicity_tDeriv_le_one_of_not_isRoot
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (heps : 0 < eps) (hp : p.Splits)
    (ha : ¬ p.IsRoot a) :
    (tDeriv eps p).rootMultiplicity a ≤ 1 := by
  obtain hp₀ | hp₀ := eq_zero_or_pos p.natDegree
  · simp [tDeriv_of_natDegree_eq_zero, rootMultiplicity_eq_zero ha, *]
  by_contra h
  push Not at h
  -- rootMultiplicity ≥ 2 means (tDeriv eps p)(a) = 0 and (tDeriv eps p)'(a) = 0
  have hT_ne : tDeriv eps p ≠ 0 := tDeriv_ne_zero <| by rintro rfl; simp at hp₀
  have hT_root : (tDeriv eps p).IsRoot a :=
    (rootMultiplicity_pos hT_ne).mp (by lia)
  have hT_deriv_root : (tDeriv eps p).derivative.IsRoot a := by
    have h2 : 2 ≤ (tDeriv eps p).rootMultiplicity a := by lia
    have hdvd := pow_rootMultiplicity_dvd (tDeriv eps p) a
    have hdvd2 : (X - C a) ^ 2 ∣ tDeriv eps p := (pow_dvd_pow _ h2).trans hdvd
    have hdvd1 : X - C a ∣ (tDeriv eps p).derivative := by
      simpa only [Nat.reduceSub, pow_one] using
        pow_sub_one_dvd_derivative_of_pow_dvd hdvd2
    exact dvd_iff_isRoot.mp hdvd1
  -- Extract the two conditions
  have hpa : p.eval a ≠ 0 := ha
  have hcond1 : p.eval a = eps * p.derivative.eval a := by
    have := hT_root
    simp only [tDeriv, Polynomial.IsRoot, eval_sub, eval_mul, eval_C] at this
    linarith
  have hcond2 : p.derivative.eval a = eps * p.derivative.derivative.eval a := by
    have := hT_deriv_root
    have hT_deriv : (tDeriv eps p).derivative = p.derivative - C eps * p.derivative.derivative := by
      simp [tDeriv, derivative_sub]
    rw [hT_deriv] at this
    simp only [Polynomial.IsRoot, eval_sub, eval_mul, eval_C] at this
    linarith
  -- From these: p''(a) · p(a) = p'(a)²
  have heps_ne : eps ≠ 0 := ne_of_gt heps
  have heq : p.derivative.derivative.eval a * p.eval a = p.derivative.eval a ^ 2 := by grind
  -- But for real-rooted p at non-roots: p''(a) · p(a) < p'(a)²
  have hlt := deriv2_mul_lt_deriv_sq_at_non_root hp hp₀ hpa
  linarith

/-- Backward chain: if `rootMultiplicity a (tDeriv eps p) ≥ 2` and `p` is real-rooted with
    `deg ≥ 1`, then `rootMultiplicity a p ≥ 2` and in fact equals
    `rootMultiplicity a (tDeriv eps p) + 1`. -/
lemma rootMultiplicity_eq_succ_of_tDeriv_ge_two
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (heps : 0 < eps) (hp : p.Splits)
    (hm : 2 ≤ (tDeriv eps p).rootMultiplicity a) :
    p.rootMultiplicity a = (tDeriv eps p).rootMultiplicity a + 1 := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp at hm
  -- rootMultiplicity a p can't be 0 (non-root → tDeriv mult ≤ 1)
  have hroot : p.IsRoot a := by
    by_contra ha
    have := rootMultiplicity_tDeriv_le_one_of_not_isRoot heps hp ha
    lia
  -- rootMultiplicity a p can't be 1 (simple root vanishes)
  have h2 : 2 ≤ p.rootMultiplicity a := by
    have h1 := (rootMultiplicity_pos hp₀).mpr hroot
    by_contra hlt; push Not at hlt
    have h1eq : p.rootMultiplicity a = 1 := by lia
    have := not_isRoot_tDeriv_of_simple_root (ne_of_gt heps) hp₀ hroot h1eq
    exact this ((rootMultiplicity_pos (tDeriv_ne_zero hp₀)).mp (by lia))
  -- Exact formula from rootMultiplicity_tDeriv_of_multiple
  rw [rootMultiplicity_tDeriv_of_multiple (ne_of_gt heps) hp₀ h2 (tDeriv_ne_zero hp₀)]
  lia

/-- `T_ε` cannot create double roots at non-roots of a real-rooted polynomial,
for arbitrary real `ε`. -/
lemma rootMultiplicity_tDeriv_le_one_of_not_isRoot_all
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (hp : p.Splits) (ha : ¬ p.IsRoot a) :
    (tDeriv eps p).rootMultiplicity a ≤ 1 := by
  obtain hp₀ | hp₀ := eq_zero_or_pos p.natDegree
  · simp [tDeriv_of_natDegree_eq_zero, rootMultiplicity_eq_zero ha, *]
  by_contra h
  push Not at h
  have hT_ne : tDeriv eps p ≠ 0 := tDeriv_ne_zero <| by rintro rfl; simp at hp₀
  have hT_root : (tDeriv eps p).IsRoot a :=
    (rootMultiplicity_pos hT_ne).mp (by lia)
  have hT_deriv_root : (tDeriv eps p).derivative.IsRoot a := by
    have h2 : 2 ≤ (tDeriv eps p).rootMultiplicity a := by lia
    have hdvd := pow_rootMultiplicity_dvd (tDeriv eps p) a
    have hdvd2 : (X - C a) ^ 2 ∣ tDeriv eps p := (pow_dvd_pow _ h2).trans hdvd
    have hdvd1 : X - C a ∣ (tDeriv eps p).derivative := by
      simpa only [Nat.reduceSub, pow_one] using
        pow_sub_one_dvd_derivative_of_pow_dvd hdvd2
    exact dvd_iff_isRoot.mp hdvd1
  have hpa : p.eval a ≠ 0 := ha
  have hcond1 : p.eval a = eps * p.derivative.eval a := by
    have := hT_root
    simp only [tDeriv, Polynomial.IsRoot, eval_sub, eval_mul, eval_C] at this
    linarith
  have hcond2 : p.derivative.eval a = eps * p.derivative.derivative.eval a := by
    have := hT_deriv_root
    have hT_deriv :
        (tDeriv eps p).derivative = p.derivative - C eps * p.derivative.derivative := by
      simp [tDeriv, derivative_sub]
    rw [hT_deriv] at this
    simp only [Polynomial.IsRoot, eval_sub, eval_mul, eval_C] at this
    linarith
  have heq : p.derivative.derivative.eval a * p.eval a = p.derivative.eval a ^ 2 := by grind
  have hlt := deriv2_mul_lt_deriv_sq_at_non_root hp hp₀ hpa
  linarith

/-- Backward chain for an arbitrary nonzero derivative shift. -/
lemma rootMultiplicity_eq_succ_of_tDeriv_ge_two_of_ne
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (heps : eps ≠ 0) (hp : p.Splits)
    (hm : 2 ≤ (tDeriv eps p).rootMultiplicity a) :
    p.rootMultiplicity a = (tDeriv eps p).rootMultiplicity a + 1 := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp at hm
  have hroot : p.IsRoot a := by
    by_contra ha
    have := rootMultiplicity_tDeriv_le_one_of_not_isRoot_all (eps := eps) hp ha
    lia
  have h2 : 2 ≤ p.rootMultiplicity a := by
    have h1 := (rootMultiplicity_pos hp₀).mpr hroot
    by_contra hlt
    push Not at hlt
    have h1eq : p.rootMultiplicity a = 1 := by lia
    have := not_isRoot_tDeriv_of_simple_root heps hp₀ hroot h1eq
    exact this ((rootMultiplicity_pos (tDeriv_ne_zero hp₀)).mp (by lia))
  rw [rootMultiplicity_tDeriv_of_multiple heps hp₀ h2 (tDeriv_ne_zero hp₀)]
  lia

/-- A nonzero derivative shift preserves simple roots away from one exceptional
point. Multiple roots of `T_ε p` can only come from multiple roots of `p`,
with multiplicity lowered by one. -/
lemma hasSimpleRootsExcept_tDeriv
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (hsimple : HasSimpleRootsExcept p a)
    (heps : eps ≠ 0) (hp0 : p ≠ 0) (hp : p.Splits) :
    HasSimpleRootsExcept (tDeriv eps p) a := by
  intro x hx_ne hx_root
  have hT0 : tDeriv eps p ≠ 0 := tDeriv_ne_zero hp0
  have hx_mult_pos : 1 ≤ (tDeriv eps p).rootMultiplicity x :=
    (rootMultiplicity_pos hT0).mpr hx_root
  by_contra hx_mult_ne
  have hx_mult_ge : 2 ≤ (tDeriv eps p).rootMultiplicity x := by lia
  have hsucc := rootMultiplicity_eq_succ_of_tDeriv_ge_two_of_ne heps hp hx_mult_ge
  have hp_root : p.IsRoot x :=
    (rootMultiplicity_pos hp0).mp (by lia)
  have hp_mult : p.rootMultiplicity x = 1 := hsimple x hx_ne hp_root
  lia

/-- Exact multiplicity transport along the `iterateTDeriv` chain as long as the
root has not yet vanished. This is the algebraic core behind the
double-root reduction in the Obreschkoff converse: iterating `T_ε` simply
subtracts one from the multiplicity at each step until the root disappears. -/
lemma rootMultiplicity_iterateTDeriv_eq_tsub
    {eps : ℝ} {p : ℝ[X]} {a : ℝ} {n : ℕ}
    (heps : 0 < eps) (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    (hn : n ≤ p.rootMultiplicity a) :
    (iterateTDeriv eps n p).rootMultiplicity a = p.rootMultiplicity a - n := by
  induction n generalizing p with
  | zero =>
      simp
  | succ n ih =>
      rw [iterateTDeriv_succ]
      have hn' : n ≤ p.rootMultiplicity a := le_trans (Nat.le_succ n) hn
      set q : ℝ[X] := iterateTDeriv eps n p
      have hq_mult : q.rootMultiplicity a = p.rootMultiplicity a - n := by grind
      have hq_mult_pos : 1 ≤ q.rootMultiplicity a := by lia
      have hq_root : q.IsRoot a :=
        (rootMultiplicity_pos <| iterateTDeriv_ne_zero hp_ne).mp (by lia)
      by_cases hq_simple : q.rootMultiplicity a = 1
      · have hnot_root : ¬ (tDeriv eps q).IsRoot a :=
          not_isRoot_tDeriv_of_simple_root
            (ne_of_gt heps) (iterateTDeriv_ne_zero hp_ne) hq_root hq_simple
        simp_all
      · have hq_mult_ge2 : 2 ≤ q.rootMultiplicity a := by lia
        have hq_deg : 1 ≤ q.natDegree := by
          calc
            1 ≤ q.rootMultiplicity a := hq_mult_pos
            _ = q.roots.count a := (count_roots q).symm
            _ ≤ q.roots.card := q.roots.count_le_card a
            _ ≤ q.natDegree := card_roots' q
        have hT_ne : tDeriv eps q ≠ 0 := tDeriv_ne_zero (iterateTDeriv_ne_zero hp_ne)
        rw [rootMultiplicity_tDeriv_of_multiple (ne_of_gt heps) (iterateTDeriv_ne_zero hp_ne)
          hq_mult_ge2 hT_ne, hq_mult]
        lia

/--
Chudnovsky--Seymour style iterate (Ryder, Lemma 6.4): for `ε > 0` and `deg f = n`,
the polynomial `(T_ε)^[n] f` is real-rooted and has simple roots.

Proof by contradiction: if the iterate has a root `a` with mult `M ≥ 2`, trace backward.
At each step, mult can't drop below 2 (simple roots vanish, non-roots stay ≤ 1).
So `rootMultiplicity a f ≥ M + n ≥ n + 2`, contradicting `rootMultiplicity ≤ natDegree = n`.
-/
theorem hasSimpleRoots_iterateTDeriv_of_natDegree
    {f : ℝ[X]} {n : ℕ} {eps : ℝ}
    (heps : 0 < eps) (hf₀ : f ≠ 0)
    (hf : f.Splits)
    (hdeg : f.natDegree = n) :
    HasSimpleRoots (iterateTDeriv eps n f) := by
  intro a ha
  by_contra hmult; push Not at hmult
  have hge2 : 2 ≤ (iterateTDeriv eps n f).rootMultiplicity a := by
    have := (rootMultiplicity_pos <| iterateTDeriv_ne_zero hf₀).mpr ha; lia
  -- Backward induction: mult at step k ≥ 2 + (n - k)
  -- We prove this by induction on j = n - k (distance from the end)
  have step : ∀ j, j ≤ n →
      2 + j ≤ (iterateTDeriv eps (n - j) f).rootMultiplicity a := by
    intro j
    induction j with
    | zero => lia
    | succ j ih =>
      intro hj
      have hprev := ih (by lia)
      -- At step n - j: mult ≥ 2 + j ≥ 2
      -- iterateTDeriv eps (n - j) f = tDeriv eps (iterateTDeriv eps (n - j - 1) f)
      have hstep : n - j = (n - (j + 1)) + 1 := by lia
      rw [hstep, iterateTDeriv_succ] at hprev
      have hp_deg : 1 ≤ (iterateTDeriv eps (n - (j + 1)) f).natDegree := by
        rw [natDegree_iterateTDeriv]; lia
      have := rootMultiplicity_eq_succ_of_tDeriv_ge_two heps (splits_iterateTDeriv heps hf)
        (by linarith)
      lia
  -- At j = n (step 0): rootMultiplicity a f ≥ 2 + n
  have h0 := step n le_rfl
  simp at h0
  -- But rootMultiplicity ≤ natDegree = n
  have : f.rootMultiplicity a ≤ n := by
    calc f.rootMultiplicity a
      _ = f.roots.count a := (count_roots f).symm
      _ ≤ f.roots.card := f.roots.count_le_card a
      _ ≤ f.natDegree := card_roots' f
      _ = n := hdeg
  lia

/-- Iterating the nonnegative derivative regularization `p ↦ p + eps * p'`
at least `natDegree p` times makes every root simple. -/
theorem hasSimpleRoots_iterateTDeriv_neg_of_natDegree_le
    {eps : ℝ} (heps : 0 < eps) {p : ℝ[X]} (hp_ne : p ≠ 0)
    (hp_splits : p.Splits) {k : ℕ} (hdeg : p.natDegree ≤ k) :
    HasSimpleRoots (iterateTDeriv (-eps) k p) := by
  intro a ha
  by_contra hmult
  push Not at hmult
  have hge2 : 2 ≤ (iterateTDeriv (-eps) k p).rootMultiplicity a := by
    have hpos := (rootMultiplicity_pos (iterateTDeriv_ne_zero hp_ne)).mpr ha
    lia
  have hsteps : ∀ j, j ≤ k →
      2 + j ≤ (iterateTDeriv (-eps) (k - j) p).rootMultiplicity a := by
    intro j
    induction j with
    | zero => simpa using hge2
    | succ j ih =>
        intro hj
        have hprev := ih (by lia)
        have hstep : k - j = (k - (j + 1)) + 1 := by lia
        rw [hstep, iterateTDeriv_succ] at hprev
        have hback := rootMultiplicity_eq_succ_of_tDeriv_ge_two_of_ne
          (neg_ne_zero.mpr heps.ne')
          (splits_iterateTDeriv_all hp_splits (k - (j + 1)))
          (by linarith :
            2 ≤ (tDeriv (-eps)
              (iterateTDeriv (-eps) (k - (j + 1)) p)).rootMultiplicity a)
        lia
  have hzero := hsteps k le_rfl
  simp only [Nat.sub_self, iterateTDeriv_zero] at hzero
  have hmult_le : p.rootMultiplicity a ≤ p.natDegree := by
    calc
      p.rootMultiplicity a = p.roots.count a := (count_roots p).symm
      _ ≤ p.roots.card := p.roots.count_le_card a
      _ ≤ p.natDegree := card_roots' p
  lia

@[deprecated (since := "2026-10-05")]
alias TDeriv := tDeriv

@[deprecated (since := "2026-10-05")]
alias natDegree_TDeriv := natDegree_tDeriv

@[deprecated (since := "2026-10-05")]
alias HasPosLeadingCoeff.TDeriv := HasPosLeadingCoeff.tDeriv

@[deprecated (since := "2026-10-05")]
alias TDeriv_ne_zero := tDeriv_ne_zero

@[deprecated (since := "2026-10-05")]
alias TDeriv_add := tDeriv_add

@[deprecated (since := "2026-10-05")]
alias TDeriv_C_mul := tDeriv_C_mul

@[deprecated (since := "2026-10-05")]
alias splits_tderiv := splits_tDeriv

@[deprecated (since := "2026-10-05")]
alias splits_tderiv_all := splits_tDeriv_all

end RealRooted
