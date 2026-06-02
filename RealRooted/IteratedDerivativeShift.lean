import RealRooted.Basic
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

/-- `T_ε p = p - ε p'`. -/
def TDeriv (eps : ℝ) (p : ℝ[X]) : ℝ[X] :=
  p - C eps * p.derivative

/-- `n`-fold iterate of `T_ε`. -/
def iterateTDeriv (eps : ℝ) (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (TDeriv eps)^[n] p

/-- A polynomial has simple roots if every real root has multiplicity `1`. -/
def HasSimpleRoots (p : ℝ[X]) : Prop :=
  ∀ r : ℝ, p.IsRoot r → p.rootMultiplicity r = 1

@[simp] lemma iterateTDeriv_zero (eps : ℝ) (p : ℝ[X]) :
    iterateTDeriv eps 0 p = p := by
  rfl

@[simp] lemma iterateTDeriv_succ (eps : ℝ) (n : ℕ) (p : ℝ[X]) :
    iterateTDeriv eps (n + 1) p = TDeriv eps (iterateTDeriv eps n p) := by
  simpa [iterateTDeriv] using (Function.iterate_succ_apply' (TDeriv eps) n p)

@[simp] private lemma iterateTDeriv_zero_poly_local (eps : ℝ) :
    ∀ n : ℕ, iterateTDeriv eps n (0 : ℝ[X]) = 0
  | 0 => by simp
  | n + 1 => by
      rw [iterateTDeriv_succ, iterateTDeriv_zero_poly_local eps n, TDeriv]
      simp

@[simp] lemma TDeriv_zero_eps (p : ℝ[X]) :
    TDeriv 0 p = p := by
  simp [TDeriv]

@[simp] lemma iterateTDeriv_zero_eps (n : ℕ) (p : ℝ[X]) :
    iterateTDeriv 0 n p = p := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [iterateTDeriv_succ, ih, TDeriv_zero_eps]

private lemma iterateTDeriv_eq_of_natDegree_zero_local (eps : ℝ) {p : ℝ[X]}
    (hdeg : p.natDegree = 0) :
    ∀ n : ℕ, iterateTDeriv eps n p = p
  | 0 => by simp
  | n + 1 => by
      rw [iterateTDeriv_succ, iterateTDeriv_eq_of_natDegree_zero_local eps hdeg n]
      have hp_eq : p = C (p.coeff 0) := by
        simpa using eq_C_of_natDegree_eq_zero hdeg
      rw [hp_eq, TDeriv, derivative_C]
      ring

/-- Coefficient formula for `T_ε`. This is the entry point for the
`ε → 0` coefficientwise continuity used in the Obreschkoff converse. -/
lemma coeff_TDeriv (eps : ℝ) (p : ℝ[X]) (i : ℕ) :
    (TDeriv eps p).coeff i =
      p.coeff i - eps * ((i + 1 : ℕ) : ℝ) * p.coeff (i + 1) := by
  simp [TDeriv, coeff_sub, coeff_C_mul, coeff_derivative]
  ring

/-! ## Multiplicity bounds -/

/-- Multiplicity can drop by at most `1` under `T_ε`. -/
lemma rootMultiplicity_sub_one_le_rootMultiplicity_TDeriv
    {eps : ℝ} {p : ℝ[X]} (a : ℝ)
    (hT_ne : TDeriv eps p ≠ 0) :
    p.rootMultiplicity a - 1 ≤ (TDeriv eps p).rootMultiplicity a := by
  set m := p.rootMultiplicity a
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · simp [hm0, TDeriv]
  have hp_ne : p ≠ 0 := by
    intro hp0
    change 0 < p.rootMultiplicity a at hm_pos
    rw [hp0, rootMultiplicity_zero] at hm_pos
    exact Nat.lt_irrefl 0 hm_pos
  have hdvd_p : (X - C a) ^ m ∣ p :=
    (le_rootMultiplicity_iff hp_ne).mp le_rfl
  have hdvd_p' : (X - C a) ^ (m - 1) ∣ p.derivative :=
    pow_sub_one_dvd_derivative_of_pow_dvd hdvd_p
  have hdvd_p_weakened : (X - C a) ^ (m - 1) ∣ p :=
    (pow_dvd_pow _ (Nat.sub_le m 1)).trans hdvd_p
  have hdvd_cmul : (X - C a) ^ (m - 1) ∣ C eps * p.derivative := by
    exact dvd_mul_of_dvd_right hdvd_p' _
  have hdvd_T : (X - C a) ^ (m - 1) ∣ TDeriv eps p := by
    simpa [TDeriv] using dvd_sub hdvd_p_weakened hdvd_cmul
  exact (le_rootMultiplicity_iff hT_ne).mpr hdvd_T

/-- If `p` has a root of multiplicity `m ≥ 2` at `a`, and `ε ≠ 0`,
    then `(X - C a)^m` does NOT divide `T_ε(p)`.

    The argument: if (X-a)^m ∣ T_ε(p), then since (X-a)^m ∣ p,
    we get (X-a)^m ∣ ε·p'. Since ε ≠ 0, (X-a)^m ∣ p'.
    But the derivative drops multiplicity by exactly 1 (in char 0),
    so rootMultiplicity a p' = m - 1, contradicting (X-a)^m ∣ p'. -/
lemma not_pow_dvd_TDeriv_of_multiple
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (heps : eps ≠ 0)
    (hp_ne : p ≠ 0)
    (hm2 : 2 ≤ p.rootMultiplicity a) :
    ¬ (X - C a) ^ (p.rootMultiplicity a) ∣ TDeriv eps p := by
  set m := p.rootMultiplicity a with hm_def
  intro hdvd_T
  -- (X-a)^m ∣ p (definition of rootMultiplicity)
  have hdvd_p : (X - C a) ^ m ∣ p := pow_rootMultiplicity_dvd p a
  -- (X-a)^m ∣ p - T_ε(p) = ε·p'
  have hdiff_eq : p - TDeriv eps p = C eps * p.derivative := by
    unfold TDeriv; ring
  have hdvd_eps_p' : (X - C a) ^ m ∣ C eps * p.derivative :=
    hdiff_eq ▸ dvd_sub hdvd_p hdvd_T
  -- ε ≠ 0 ⟹ C ε is a unit ⟹ (X-a)^m ∣ p'
  have hdvd_p' : (X - C a) ^ m ∣ p.derivative := by
    -- C ε is a unit, so (X-a)^m ∣ C ε * p' implies (X-a)^m ∣ p'
    have hu : IsUnit (C eps : ℝ[X]) := isUnit_C.mpr (IsUnit.mk0 eps heps)
    rwa [hu.dvd_mul_left] at hdvd_eps_p'
  -- p' ≠ 0 (since rootMultiplicity ≥ 2 implies natDegree ≥ 2)
  have hm_le : m ≤ p.natDegree := by
    calc m = p.roots.count a := (count_roots p).symm
    _ ≤ p.roots.card := p.roots.count_le_card a
    _ ≤ p.natDegree := card_roots' p
  have hp'_ne : p.derivative ≠ 0 := derivative_ne_zero (by lia)
  -- (X-a)^{m} ∤ p' since rootMultiplicity a p' = m - 1 (exact, in char 0)
  have hroot : p.IsRoot a := (rootMultiplicity_pos hp_ne).mp (by lia)
  -- In char 0: (m : ℝ) ≠ 0, so it's in nonZeroDivisors
  have hm_nzd : (↑m : ℝ) ∈ nonZeroDivisors ℝ :=
    IsRegular.mem_nonZeroDivisors
      (IsRegular.of_ne_zero (Nat.cast_ne_zero.mpr (by lia)))
  have hp'_mult : p.derivative.rootMultiplicity a = m - 1 :=
    derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hroot hm_nzd
  -- (X-a)^m ∣ p' means m ≤ rootMultiplicity a p' = m - 1. Contradiction.
  have : m ≤ p.derivative.rootMultiplicity a :=
    (le_rootMultiplicity_iff hp'_ne).mpr hdvd_p'
  lia

/-- Exact multiplicity of T_ε at a multiple root. -/
lemma rootMultiplicity_TDeriv_of_multiple
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (heps : eps ≠ 0)
    (hp_ne : p ≠ 0)
    (hm2 : 2 ≤ p.rootMultiplicity a)
    (hT_ne : TDeriv eps p ≠ 0) :
    (TDeriv eps p).rootMultiplicity a = p.rootMultiplicity a - 1 := by
  set m := p.rootMultiplicity a
  apply le_antisymm
  · -- rootMultiplicity ≤ m - 1 means ¬ (X-a)^{m-1+1} ∣ T_ε(p)
    rw [Polynomial.rootMultiplicity_le_iff hT_ne]
    -- m - 1 + 1 = m since m ≥ 2
    have hm_eq : m - 1 + 1 = m := by lia
    rw [hm_eq]
    exact not_pow_dvd_TDeriv_of_multiple heps hp_ne hm2
  · exact rootMultiplicity_sub_one_le_rootMultiplicity_TDeriv a hT_ne

/-! ## Degree and real-rootedness preservation -/

/-- T_ε preserves the degree (the ε·p' term has strictly lower degree). -/
lemma natDegree_TDeriv {eps : ℝ} {p : ℝ[X]} (_hp : p ≠ 0) (hdeg : 1 ≤ p.natDegree) :
    (TDeriv eps p).natDegree = p.natDegree := by
  unfold TDeriv
  have hp'_deg : (C eps * p.derivative).natDegree < p.natDegree := by
    calc (C eps * p.derivative).natDegree
      _ ≤ (C eps).natDegree + p.derivative.natDegree := natDegree_mul_le
      _ = p.derivative.natDegree := by simp [natDegree_C]
      _ = p.natDegree - 1 := natDegree_derivative_eq (by lia)
      _ < p.natDegree := Nat.sub_lt (by lia) one_pos
  rw [natDegree_sub_eq_left_of_natDegree_lt hp'_deg]

/-- `T_ε` keeps the top coefficient unchanged because the derivative term has
strictly smaller degree. This is the key normalization fact behind the
`ε → 0` route in the Obreschkoff converse: after sign-normalizing once, the
regularized family stays sign-normalized without any ε-dependent rescaling. -/
lemma leadingCoeff_TDeriv {eps : ℝ} {p : ℝ[X]} (hp : p ≠ 0) (hdeg : 1 ≤ p.natDegree) :
    (TDeriv eps p).leadingCoeff = p.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_TDeriv hp hdeg, TDeriv, coeff_sub]
  have hp'_deg : (C eps * p.derivative).natDegree < p.natDegree := by
    calc
      (C eps * p.derivative).natDegree
          ≤ (C eps).natDegree + p.derivative.natDegree := natDegree_mul_le
      _ = p.derivative.natDegree := by simp [natDegree_C]
      _ = p.natDegree - 1 := natDegree_derivative_eq hdeg
      _ < p.natDegree := Nat.sub_lt (by lia) one_pos
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hp'_deg, sub_zero, Polynomial.leadingCoeff]

/-- T_ε of a nonzero polynomial with degree ≥ 1 is nonzero. -/
lemma TDeriv_ne_zero {eps : ℝ} {p : ℝ[X]} (hp : p ≠ 0) (hdeg : 1 ≤ p.natDegree) :
    TDeriv eps p ≠ 0 := by
  intro h
  have := @natDegree_TDeriv eps p hp hdeg
  rw [h, natDegree_zero] at this
  lia

private lemma hasPosLeadingCoeff_derivative_of_pos
    {p : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hdeg : 1 ≤ p.natDegree) :
    HasPosLeadingCoeff p.derivative := by
  unfold HasPosLeadingCoeff at hp_pos ⊢
  rw [leadingCoeff, natDegree_derivative_eq hdeg, coeff_derivative]
  rw [Nat.sub_add_cancel hdeg, coeff_natDegree] at *
  have hdeg_pos : 0 < (p.natDegree : ℝ) := by
    exact_mod_cast hdeg
  nlinarith

/-- T_ε preserves real-rootedness when ε > 0.
    Proof: T_ε(p) = 1·p + (-C ε)·p'. Since p' interlaces p (derivative interlacing)
    and (-C ε) evaluates to -ε ≤ 0 at every point, the Ma-Wang theorem gives
    `Prec p (T_ε(p))`, which implies T_ε(p) is real-rooted. -/
private lemma isRealRooted_TDeriv_pos {eps : ℝ} {p : ℝ[X]}
    (heps : 0 < eps)
    (hp : IsRealRooted p)
    (hp_pos : HasPosLeadingCoeff p)
    (hdeg2 : 2 ≤ p.natDegree) :
    IsRealRooted (TDeriv eps p) := by
  -- Write T_ε(p) = C 1 * p + C (-eps) * p'
  have hrewrite : TDeriv eps p = C 1 * p + C (-eps) * p.derivative := by
    simp [TDeriv]; ring
  -- derivative interlaces p
  have hder : Interlaces p.derivative p := derivative_interlaces hp hdeg2
  -- HasPosLeadingCoeff of p'
  have hp'_pos : HasPosLeadingCoeff p.derivative := by
    exact hasPosLeadingCoeff_derivative_of_pos hp_pos (by lia)
  -- HasPosLeadingCoeff of T_ε(p) (same leading coeff as p)
  have hT_pos : HasPosLeadingCoeff (C 1 * p + C (-eps) * p.derivative) := by
    rw [← hrewrite]
    unfold HasPosLeadingCoeff
    rw [leadingCoeff_TDeriv hp.1 (by lia)]
    exact hp_pos
  -- degree bounds
  have hdeg_lo : p.natDegree ≤ (C 1 * p + C (-eps) * p.derivative).natDegree := by
    rw [← hrewrite, @natDegree_TDeriv eps p hp.1 (by lia)]
  have hdeg_hi : (C 1 * p + C (-eps) * p.derivative).natDegree ≤ p.natDegree + 1 := by
    rw [← hrewrite, @natDegree_TDeriv eps p hp.1 (by lia)]; lia
  -- sign condition: b = C(-eps), b.eval r = -eps ≤ 0 for all r
  have hb_nonpos : ∀ r, p.IsRoot r → (C (-eps)).eval r ≤ 0 := by
    intro r _; simp [eval_C]; linarith
  -- Apply Ma-Wang
  rw [hrewrite]
  exact (prec_of_interlaces_evalCoeff_nonpos hder hp'_pos hT_pos hdeg_lo hdeg_hi hb_nonpos).2.1

/-- T_ε is linear: T_ε(c·p) = c·T_ε(p). -/
private lemma TDeriv_C_mul (eps c : ℝ) (p : ℝ[X]) :
    TDeriv eps (C c * p) = C c * TDeriv eps p := by
  simp [TDeriv, mul_sub, mul_left_comm]

private lemma iterateTDeriv_C_mul_local (eps c : ℝ) :
    ∀ (n : ℕ) (p : ℝ[X]),
      iterateTDeriv eps n (C c * p) = C c * iterateTDeriv eps n p
  | 0, p => by simp [iterateTDeriv]
  | n + 1, p => by
      rw [iterateTDeriv_succ, iterateTDeriv_succ, iterateTDeriv_C_mul_local]
      exact TDeriv_C_mul eps c _

private lemma TDeriv_X_sub_C (eps r : ℝ) :
    TDeriv eps (X - C r) = X - C (r + eps) := by
  simp [TDeriv]
  ring

/-- `T_ε` commutes with one derivative step. This is the algebraic reason the
`ε → 0` regularization can be combined with derivative-tower multiplicity
arguments in the Obreschkoff converse. -/
lemma derivative_TDeriv (eps : ℝ) (p : ℝ[X]) :
    (TDeriv eps p).derivative = TDeriv eps p.derivative := by
  simp [TDeriv, derivative_sub]

/-- `T_ε` commutes with every iterated derivative. -/
lemma iterate_derivative_TDeriv (eps : ℝ) (k : ℕ) (p : ℝ[X]) :
    (derivative^[k]) (TDeriv eps p) = TDeriv eps ((derivative^[k]) p) := by
  induction k generalizing p with
  | zero =>
      simp [TDeriv]
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact derivative_TDeriv eps ((derivative^[k]) p)

/-- `iterateTDeriv` commutes with the whole derivative tower. -/
lemma iterate_derivative_iterateTDeriv (eps : ℝ) (n k : ℕ) (p : ℝ[X]) :
    (derivative^[k]) (iterateTDeriv eps n p) =
      iterateTDeriv eps n ((derivative^[k]) p) := by
  induction n generalizing p with
  | zero =>
      simp [iterateTDeriv]
  | succ n ih =>
      rw [iterateTDeriv_succ, iterateTDeriv_succ, iterate_derivative_TDeriv, ih]

theorem isRealRooted_TDeriv {eps : ℝ} {p : ℝ[X]}
    (heps : 0 < eps)
    (hp : IsRealRooted p) :
    IsRealRooted (TDeriv eps p) := by
  by_cases hdeg2 : 2 ≤ p.natDegree
  · -- degree ≥ 2: use Ma-Wang
    rcases lt_or_gt_of_ne (fun h => hp.1 (leadingCoeff_eq_zero.mp h))
      with hneg | hpos
    · -- negative leading coefficient: T_ε(-p) = -T_ε(p)
      have hneg_rr : IsRealRooted (-p) :=
        ⟨neg_ne_zero.mpr hp.1, by rw [Polynomial.roots_neg, natDegree_neg]; exact hp.2⟩
      have hneg_pos : HasPosLeadingCoeff (-p) := by
        unfold HasPosLeadingCoeff; rw [leadingCoeff_neg]; linarith
      have hT_neg :=
        isRealRooted_TDeriv_pos heps hneg_rr hneg_pos (by
          rw [natDegree_neg]
          exact hdeg2)
      -- T_ε(-p) = -T_ε(p) since T_ε is linear
      have hlin : TDeriv eps (-p) = -TDeriv eps p := by
        simp [TDeriv, derivative_neg]; ring
      rw [hlin] at hT_neg
      -- hT_neg : IsRealRooted (-(TDeriv eps p))
      -- i.e., -(TDeriv eps p) ≠ 0 ∧ (-(TDeriv eps p)).roots.card = (-(TDeriv eps p)).natDegree
      have hne : TDeriv eps p ≠ 0 := by
        intro h; exact hT_neg.1 (by rw [h, neg_zero])
      refine ⟨hne, ?_⟩
      have := hT_neg.2
      rwa [Polynomial.roots_neg, natDegree_neg] at this
    · exact isRealRooted_TDeriv_pos heps hp hpos hdeg2
  · -- degree ≤ 1: T_ε(p) has same degree as p
    push Not at hdeg2
    -- p.natDegree < 2, so natDegree is 0 or 1
    have hdeg01 : p.natDegree = 0 ∨ p.natDegree = 1 := by lia
    rcases hdeg01 with h0 | h1
    · -- degree 0: p is constant, derivative is 0, TDeriv eps p = p
      have hpc := eq_C_of_natDegree_eq_zero h0
      have : TDeriv eps p = p := by unfold TDeriv; rw [hpc, derivative_C]; ring
      rw [this]; exact hp
    · -- degree 1: TDeriv preserves degree, so result has degree 1
      exact isRealRooted_of_degree_one (by rw [natDegree_TDeriv hp.1 (by lia)]; exact h1)

/-- For positive `eps`, `T_ε p` sits immediately to the right of `p` in the
weak interlacing order. This is the interlacing content hidden inside the
Ma--Wang proof of `isRealRooted_TDeriv`. Keeping it explicit is useful for the
`iterateTDeriv` transport route in the Obreschkoff converse. -/
theorem prec_TDeriv {eps : ℝ} {p : ℝ[X]}
    (heps : 0 < eps)
    (hp : IsRealRooted p) :
    Prec p (TDeriv eps p) := by
  by_cases hdeg2 : 2 ≤ p.natDegree
  · rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp.1) with hneg | hpos
    · have hneg_rr : IsRealRooted (-p) :=
        ⟨neg_ne_zero.mpr hp.1, by rw [Polynomial.roots_neg, natDegree_neg]; exact hp.2⟩
      have hneg_pos : HasPosLeadingCoeff (-p) := by
        unfold HasPosLeadingCoeff
        rw [leadingCoeff_neg]
        linarith
      have hrewrite : TDeriv eps (-p) = -TDeriv eps p := by
        simp [TDeriv, derivative_neg]
        ring
      have hprec_neg :
          Prec (-p) (TDeriv eps (-p)) := by
        have hder : Interlaces (-p).derivative (-p) := by
          simpa [derivative_neg] using
            derivative_interlaces hneg_rr (by
              rw [natDegree_neg]
              exact hdeg2)
        have hp'_pos : HasPosLeadingCoeff (-p).derivative := by
          simpa [derivative_neg, natDegree_neg] using
            hasPosLeadingCoeff_derivative_of_pos hneg_pos (by rw [natDegree_neg]; lia)
        have hrewrite_neg : TDeriv eps (-p) = C 1 * (-p) + C (-eps) * (-p).derivative := by
          simp [TDeriv]
        have hT_pos : HasPosLeadingCoeff (C 1 * (-p) + C (-eps) * (-p).derivative) := by
          rw [← hrewrite_neg]
          unfold HasPosLeadingCoeff
          rw [leadingCoeff_TDeriv hneg_rr.1 (by rw [natDegree_neg]; lia)]
          exact hneg_pos
        have hdeg_lo : (-p).natDegree ≤ (C 1 * (-p) + C (-eps) * (-p).derivative).natDegree := by
          rw [← hrewrite_neg, @natDegree_TDeriv eps (-p) hneg_rr.1 (by rw [natDegree_neg]; lia)]
        have hdeg_hi :
            (C 1 * (-p) + C (-eps) * (-p).derivative).natDegree ≤ (-p).natDegree + 1 := by
          rw [← hrewrite_neg, @natDegree_TDeriv eps (-p) hneg_rr.1 (by rw [natDegree_neg]; lia)]
          lia
        have hb_nonpos : ∀ r, (-p).IsRoot r → (C (-eps)).eval r ≤ 0 := by
          intro r _
          simp [eval_C]
          linarith
        rw [hrewrite_neg]
        exact prec_of_interlaces_evalCoeff_nonpos hder hp'_pos hT_pos hdeg_lo hdeg_hi hb_nonpos
      have hleft : Prec p (TDeriv eps (-p)) := by
        simpa using prec_C_mul_left hprec_neg (by norm_num : (-1 : ℝ) ≠ 0)
      have hboth : Prec p (TDeriv eps p) := by
        simpa [hrewrite] using prec_C_mul_right hleft (by norm_num : (-1 : ℝ) ≠ 0)
      exact hboth
    · have hder : Interlaces p.derivative p := derivative_interlaces hp hdeg2
      have hp'_pos : HasPosLeadingCoeff p.derivative := by
        exact hasPosLeadingCoeff_derivative_of_pos hpos (by lia)
      have hrewrite : TDeriv eps p = C 1 * p + C (-eps) * p.derivative := by
        simp [TDeriv]
        ring
      have hT_pos : HasPosLeadingCoeff (C 1 * p + C (-eps) * p.derivative) := by
        rw [← hrewrite]
        unfold HasPosLeadingCoeff
        rw [leadingCoeff_TDeriv hp.1 (by lia)]
        exact hpos
      have hdeg_lo : p.natDegree ≤ (C 1 * p + C (-eps) * p.derivative).natDegree := by
        rw [← hrewrite, @natDegree_TDeriv eps p hp.1 (by lia)]
      have hdeg_hi : (C 1 * p + C (-eps) * p.derivative).natDegree ≤ p.natDegree + 1 := by
        rw [← hrewrite, @natDegree_TDeriv eps p hp.1 (by lia)]
        lia
      have hb_nonpos : ∀ r, p.IsRoot r → (C (-eps)).eval r ≤ 0 := by
        intro r _
        simp [eval_C]
        linarith
      rw [hrewrite]
      exact prec_of_interlaces_evalCoeff_nonpos hder hp'_pos hT_pos hdeg_lo hdeg_hi hb_nonpos
  · push Not at hdeg2
    have hdeg01 : p.natDegree = 0 ∨ p.natDegree = 1 := by
      lia
    rcases hdeg01 with h0 | h1
    · have hconst : TDeriv eps p = p := by
        rw [eq_C_of_natDegree_eq_zero h0, TDeriv, derivative_C]
        ring
      simpa [hconst] using prec_refl hp
    · obtain ⟨a, b, hp_eq⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one h1.le
      have ha_ne : a ≠ 0 := by
        intro ha0
        simp [hp_eq, ha0] at h1
      let r : ℝ := -b / a
      have hp_factor : p = C a * (X - C r) := by
        ext i
        rcases i with _ | i
        · simp [hp_eq, r]
          field_simp [ha_ne]
        · rcases i with _ | i
          · simp [hp_eq, r]
          · simp [hp_eq, r, Polynomial.coeff_X]
      have hbase : Prec (X - C r) (X - C (r + eps)) := by
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
      have hbase' : Prec (X - C r) (TDeriv eps (X - C r)) := by
        simpa [TDeriv_X_sub_C] using hbase
      have hscaled :
          Prec (C a * (X - C r)) (C a * TDeriv eps (X - C r)) := by
        exact prec_C_mul_right (prec_C_mul_left hbase' ha_ne) ha_ne
      simpa [hp_factor, TDeriv_C_mul] using hscaled

/-! ## Helper: simple roots vanish under T_ε -/

/-- If `a` is a simple root of `p` (multiplicity 1) and `ε ≠ 0`, then `a` is NOT a root
    of `T_ε(p)`. This is because `T_ε(p)(a) = p(a) - ε·p'(a) = -ε·p'(a)`, and a simple
    root means `p'(a) ≠ 0`. -/
lemma not_isRoot_TDeriv_of_simple_root
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (heps : eps ≠ 0)
    (hp_ne : p ≠ 0)
    (hroot : p.IsRoot a)
    (hsimple : p.rootMultiplicity a = 1) :
    ¬ (TDeriv eps p).IsRoot a := by
  -- Factor p = (X - C a) * q with q(a) ≠ 0
  obtain ⟨q, hpq⟩ := dvd_iff_isRoot.mpr hroot
  have hqa : q.eval a ≠ 0 := by
    intro hqa0
    have h2 : (X - C a) ^ 2 ∣ p := by
      rw [hpq, sq]
      exact mul_dvd_mul_left _ (dvd_iff_isRoot.mpr hqa0)
    linarith [(le_rootMultiplicity_iff hp_ne).mpr h2]
  -- p' = q + (X - a) * q' via product rule, so p'(a) = q(a) ≠ 0
  have hp' : p.derivative = q + (X - C a) * q.derivative := by
    rw [hpq, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  have hp'a : p.derivative.eval a = q.eval a := by
    rw [hp', eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  -- T_ε(p)(a) = p(a) - ε·p'(a) = 0 - ε·q(a) = -ε·q(a) ≠ 0
  intro hT
  have hT0 : (TDeriv eps p).eval a = 0 := hT
  simp only [TDeriv, eval_sub, eval_mul, eval_C] at hT0
  rw [show p.eval a = 0 from hroot, hp'a, zero_sub, neg_eq_zero] at hT0
  exact hqa ((mul_eq_zero.mp hT0).resolve_left heps)

/-- Real-rootedness is preserved by iterating T_ε. -/
lemma isRealRooted_iterateTDeriv {eps : ℝ} {p : ℝ[X]} {k : ℕ}
    (heps : 0 < eps)
    (hp : IsRealRooted p) :
    IsRealRooted (iterateTDeriv eps k p) := by
  induction k with
  | zero => simpa using hp
  | succ n ih =>
    rw [iterateTDeriv_succ]
    exact isRealRooted_TDeriv heps ih

/-- Consecutive `iterateTDeriv` iterates form a generalized Sturm chain: every
step weakly interlaces into the next one. This packages repeated applications
of `prec_TDeriv` in the exact form needed for chain arguments. -/
lemma prec_iterateTDeriv_succ {eps : ℝ} {p : ℝ[X]} {n : ℕ}
    (heps : 0 < eps)
    (hp : IsRealRooted p) :
    Prec (iterateTDeriv eps n p) (iterateTDeriv eps (n + 1) p) := by
  rw [iterateTDeriv_succ]
  exact prec_TDeriv heps (isRealRooted_iterateTDeriv heps hp)

/-! ## Main theorem -/

/-- Degree is preserved by iterating T_ε. -/
lemma natDegree_iterateTDeriv {eps : ℝ} {p : ℝ[X]} {k : ℕ}
    (_hp : p ≠ 0) (hdeg : 1 ≤ p.natDegree) :
    (iterateTDeriv eps k p).natDegree = p.natDegree := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [iterateTDeriv_succ]
    have hne : iterateTDeriv eps n p ≠ 0 := by
      intro h; have := ih; rw [h, natDegree_zero] at this; lia
    rw [natDegree_TDeriv hne (by lia), ih]

/-- The iterate T_ε^[k] of a nonzero polynomial with degree ≥ 1 is nonzero. -/
lemma iterateTDeriv_ne_zero {eps : ℝ} {p : ℝ[X]} {k : ℕ}
    (hp : p ≠ 0) (hdeg : 1 ≤ p.natDegree) :
    iterateTDeriv eps k p ≠ 0 := by
  intro h
  have := natDegree_iterateTDeriv hp hdeg (eps := eps) (k := k)
  rw [h, natDegree_zero] at this; lia

/-- Iterating `T_ε` preserves the leading coefficient as well. -/
lemma leadingCoeff_iterateTDeriv {eps : ℝ} {p : ℝ[X]} {k : ℕ}
    (hp : p ≠ 0) (hdeg : 1 ≤ p.natDegree) :
    (iterateTDeriv eps k p).leadingCoeff = p.leadingCoeff := by
  induction k with
  | zero =>
      simp
  | succ n ih =>
      rw [iterateTDeriv_succ, leadingCoeff_TDeriv]
      · exact ih
      · exact iterateTDeriv_ne_zero hp hdeg
      · rw [natDegree_iterateTDeriv hp hdeg]
        exact hdeg

/-- `iterateTDeriv` preserves `natDegree` for every polynomial, including the
degenerate cases `p = 0` and `p.natDegree = 0`. This is the form convenient for
coefficientwise limit arguments. -/
lemma natDegree_iterateTDeriv_eq (eps : ℝ) (n : ℕ) (p : ℝ[X]) :
    (iterateTDeriv eps n p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · subst hp
    simp [iterateTDeriv_zero_poly_local]
  by_cases hdeg0 : p.natDegree = 0
  · rw [iterateTDeriv_eq_of_natDegree_zero_local eps hdeg0 n]
  · exact natDegree_iterateTDeriv hp (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hdeg0))

/-- In particular, a real-rooted polynomial and all of its `iterateTDeriv`
regularizations have the same leading coefficient, even in degree `0`. -/
lemma leadingCoeff_iterateTDeriv_of_isRealRooted {eps : ℝ} {p : ℝ[X]} {k : ℕ}
    (hp : IsRealRooted p) :
    (iterateTDeriv eps k p).leadingCoeff = p.leadingCoeff := by
  by_cases hdeg0 : p.natDegree = 0
  · have hp_eq : p = C (p.coeff 0) := by
      simpa using eq_C_of_natDegree_eq_zero hdeg0
    have hiter_eq : ∀ n : ℕ, iterateTDeriv eps n p = p := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          rw [iterateTDeriv_succ, ih, hp_eq, TDeriv, derivative_C]
          ring
    rw [hiter_eq k]
  · exact
      leadingCoeff_iterateTDeriv hp.1
        (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hdeg0))

/-- Positive-leading normalization is preserved exactly along `iterateTDeriv`.
This is the form most useful in converse/continuity arguments. -/
lemma hasPosLeadingCoeff_iterateTDeriv_of_isRealRooted {eps : ℝ} {p : ℝ[X]} {k : ℕ}
    (hp : IsRealRooted p) :
    HasPosLeadingCoeff (iterateTDeriv eps k p) ↔ HasPosLeadingCoeff p := by
  rw [HasPosLeadingCoeff, HasPosLeadingCoeff,
    leadingCoeff_iterateTDeriv_of_isRealRooted hp]

lemma monic_iterateTDeriv_of_isRealRooted {eps : ℝ} {p : ℝ[X]} {k : ℕ}
    (hp : IsRealRooted p) (hp_monic : p.Monic) :
    (iterateTDeriv eps k p).Monic := by
  rw [Monic, leadingCoeff_iterateTDeriv_of_isRealRooted hp, hp_monic.leadingCoeff]

/-- Monic normalization is compatible with `iterateTDeriv`: because the leading
coefficient is preserved exactly, one can scale by the inverse of the original
leading coefficient before applying root-continuity arguments. This is the
normalization package needed by the current Obreschkoff closure route. -/
lemma monic_normalization_iterateTDeriv_of_isRealRooted {eps : ℝ} {p : ℝ[X]} {k : ℕ}
    (hp : IsRealRooted p) :
    (C p.leadingCoeff⁻¹ * iterateTDeriv eps k p).Monic := by
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [leadingCoeff_iterateTDeriv_of_isRealRooted hp]
  field_simp [leadingCoeff_ne_zero.mpr hp.1]

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
        rw [iterateTDeriv_succ, coeff_TDeriv]
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
  simpa [iterateTDeriv_zero_eps] using hcont0

/-- For fixed `n`, `p`, and `x`, the evaluation
`(iterateTDeriv eps n p).eval x` depends continuously on `eps`. This is the
fixed-point analogue of coefficientwise continuity, and it is the exact local
input needed to keep root evaluations away from `0` for small `eps`. -/
lemma continuous_eval_iterateTDeriv (n : ℕ) (p : ℝ[X]) (x : ℝ) :
    Continuous fun eps : ℝ => (iterateTDeriv eps n p).eval x := by
  have hrewrite :
      (fun eps : ℝ => (iterateTDeriv eps n p).eval x) =
        fun eps : ℝ =>
          Finset.sum (Finset.range (p.natDegree + 1)) fun i =>
            (iterateTDeriv eps n p).coeff i * x ^ i := by
    funext eps
    rw [Polynomial.eval_eq_sum_range]
    rw [natDegree_iterateTDeriv_eq eps n p]
  rw [hrewrite]
  exact continuous_finset_sum _ fun i _ =>
    (continuous_coeff_iterateTDeriv n p i).mul continuous_const

/-- Evaluation at a fixed real point is continuous at `eps = 0` along the
`iterateTDeriv` family. -/
lemma continuousAt_eval_iterateTDeriv_zero (n : ℕ) (p : ℝ[X]) (x : ℝ) :
    ContinuousAt (fun eps : ℝ => (iterateTDeriv eps n p).eval x) 0 := by
  have hcont0 : ContinuousAt (fun eps : ℝ => (iterateTDeriv eps n p).eval x) 0 :=
    (continuous_eval_iterateTDeriv n p x).continuousAt
  simpa [iterateTDeriv_zero_eps] using hcont0

/-- Joint continuity of the `iterateTDeriv` evaluation map in both the shift
parameter `eps` and the evaluation point `x`. This is the local form needed to
exclude perturbed roots from a whole neighborhood of a fixed non-root. -/
lemma continuous_eval_iterateTDeriv_joint (n : ℕ) (p : ℝ[X]) :
    Continuous fun z : ℝ × ℝ => (iterateTDeriv z.1 n p).eval z.2 := by
  have hrewrite :
      (fun z : ℝ × ℝ => (iterateTDeriv z.1 n p).eval z.2) =
        fun z : ℝ × ℝ =>
          Finset.sum (Finset.range (p.natDegree + 1)) fun i =>
            (iterateTDeriv z.1 n p).coeff i * z.2 ^ i := by
    funext z
    rw [Polynomial.eval_eq_sum_range]
    rw [natDegree_iterateTDeriv_eq z.1 n p]
  rw [hrewrite]
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_coeff_iterateTDeriv n p i).comp continuous_fst).mul
      (continuous_snd.pow i)

/-- Joint continuity of `eval (iterateTDeriv eps n p)` at the base point
`(0, x)`. -/
lemma continuousAt_eval_iterateTDeriv_joint_zero (n : ℕ) (p : ℝ[X]) (x : ℝ) :
    ContinuousAt (fun z : ℝ × ℝ => (iterateTDeriv z.1 n p).eval z.2) (0, x) := by
  have hcont0 :
      ContinuousAt (fun z : ℝ × ℝ => (iterateTDeriv z.1 n p).eval z.2) (0, x) :=
    (continuous_eval_iterateTDeriv_joint n p).continuousAt
  simpa [iterateTDeriv_zero_eps] using hcont0

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
  have heps' : dist eps 0 < δ := by
    simpa [dist_eq_norm] using heps
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

private lemma pos_of_norm_sub_lt_half_of_pos {a b : ℝ}
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
    exists_delta_for_eval_iterateTDeriv_at_zero n p x (show 0 < ‖p.eval x‖ / 2 by positivity)
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
        rw [hneg_norm]
        exact hclose'
      have hclose_neg :
          ‖-(iterateTDeriv eps n p).eval x - (-p.eval x)‖ < (-p.eval x) / 2 := by
        simpa [Real.norm_eq_abs, abs_of_neg hx_neg] using hclose_neg0
      have hpos_neg_iter : 0 < -(iterateTDeriv eps n p).eval x :=
        pos_of_norm_sub_lt_half_of_pos (by linarith) hclose_neg
      linarith
    exact mul_pos_of_neg_of_neg hneg_iter hx_neg
  · have hpos_iter : 0 < (iterateTDeriv eps n p).eval x :=
      pos_of_norm_sub_lt_half_of_pos hx_pos
        (by simpa [Real.norm_eq_abs, abs_of_pos hx_pos] using hclose')
    exact mul_pos hpos_iter hx_pos

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
      (show 0 < ‖p.eval x‖ / 2 by positivity)
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
        rw [hneg_norm]
        exact hclose'
      have hclose_neg :
          ‖-(iterateTDeriv z.1 n p).eval z.2 - (-p.eval x)‖ < (-p.eval x) / 2 := by
        simpa [Real.norm_eq_abs, abs_of_neg hx_neg] using hclose_neg0
      have hpos_neg_iter : 0 < -(iterateTDeriv z.1 n p).eval z.2 :=
        pos_of_norm_sub_lt_half_of_pos (by linarith) hclose_neg
      linarith
    exact mul_pos_of_neg_of_neg hneg_iter hx_neg
  · have hpos_iter : 0 < (iterateTDeriv z.1 n p).eval z.2 :=
      pos_of_norm_sub_lt_half_of_pos hx_pos
        (by simpa [Real.norm_eq_abs, abs_of_pos hx_pos] using hclose')
    exact mul_pos hpos_iter hx_pos

/-- If `x` is not a root of `p`, then `x` stays away from the roots of the
`iterateTDeriv` regularizations for all sufficiently small `eps`. -/
lemma exists_delta_not_isRoot_iterateTDeriv_at_point
    (n : ℕ) {p : ℝ[X]} {x : ℝ}
    (hx : ¬ p.IsRoot x) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, ‖eps‖ < δ →
      ¬ (iterateTDeriv eps n p).IsRoot x := by
  have hx_eval : p.eval x ≠ 0 := by
    simpa [Polynomial.IsRoot.def] using hx
  obtain ⟨δ, hδ, hsign⟩ := exists_delta_eval_mul_pos_iterateTDeriv_at_zero n hx_eval
  refine ⟨δ, hδ, ?_⟩
  intro eps heps hroot
  have hprod : 0 < (iterateTDeriv eps n p).eval x * p.eval x := hsign heps
  have hroot_eval : (iterateTDeriv eps n p).eval x = 0 := by
    simpa [Polynomial.IsRoot.def] using hroot
  rw [hroot_eval, zero_mul] at hprod
  exact (lt_irrefl 0 hprod).elim

/-- Local neighborhood version of `exists_delta_not_isRoot_iterateTDeriv_at_point`:
if `x` is not a root of `p`, then no sufficiently small joint perturbation of
the shift parameter and the evaluation point can hit a root of the regularized
polynomial. -/
lemma exists_delta_not_isRoot_iterateTDeriv_near_point
    (n : ℕ) {p : ℝ[X]} {x : ℝ}
    (hx : ¬ p.IsRoot x) :
    ∃ δ > 0, ∀ ⦃z : ℝ × ℝ⦄, dist z (0, x) < δ →
      ¬ (iterateTDeriv z.1 n p).IsRoot z.2 := by
  have hx_eval : p.eval x ≠ 0 := by
    simpa [Polynomial.IsRoot.def] using hx
  obtain ⟨δ, hδ, hsign⟩ :=
    exists_delta_eval_mul_pos_iterateTDeriv_joint_at_zero n hx_eval
  refine ⟨δ, hδ, ?_⟩
  intro z hz hroot
  have hprod : 0 < (iterateTDeriv z.1 n p).eval z.2 * p.eval x := hsign hz
  have hroot_eval : (iterateTDeriv z.1 n p).eval z.2 = 0 := by
    simpa [Polynomial.IsRoot.def] using hroot
  rw [hroot_eval, zero_mul] at hprod
  exact (lt_irrefl 0 hprod).elim

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
  have heps' : dist eps 0 < δ := by
    simpa [dist_eq_norm] using heps
  simpa [dist_eq_norm, iterateTDeriv_zero_eps] using hclose heps'

private lemma exists_delta_for_coeffs_lt_iterateTDeriv_at_zero
    (n : ℕ) (p : ℝ[X]) :
    ∀ m : ℕ, ∀ {ε : ℝ}, 0 < ε →
      ∃ δ > 0, ∀ ⦃eps : ℝ⦄, ‖eps‖ < δ →
        ∀ i : ℕ, i < m →
          ‖(iterateTDeriv eps n p).coeff i - p.coeff i‖ < ε
  | 0, ε, hε => by
      refine ⟨1, zero_lt_one, ?_⟩
      intro eps heps i hi
      exact (Nat.not_lt_zero _ hi).elim
  | m + 1, ε, hε => by
      obtain ⟨δtail, hδtail, htail⟩ :=
        exists_delta_for_coeffs_lt_iterateTDeriv_at_zero n p m hε
      obtain ⟨δlast, hδlast, hlast⟩ :=
        exists_delta_for_coeff_iterateTDeriv_at_zero n p m hε
      refine ⟨min δtail δlast, lt_min hδtail hδlast, ?_⟩
      intro eps heps i hi
      have heps_tail : ‖eps‖ < δtail := lt_of_lt_of_le heps (min_le_left _ _)
      have heps_last : ‖eps‖ < δlast := lt_of_lt_of_le heps (min_le_right _ _)
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with him | rfl
      · exact htail heps_tail i him
      · exact hlast heps_last

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
  · exact hclose heps i hi
  · have hdeg_lt : p.natDegree < i := Nat.lt_of_not_ge (by simpa using hi)
    have hp_coeff : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt hdeg_lt
    have hiter_coeff : (iterateTDeriv eps n p).coeff i = 0 := by
      rw [coeff_eq_zero_of_natDegree_lt]
      simpa [natDegree_iterateTDeriv_eq eps n p] using hdeg_lt
    simpa [hiter_coeff, hp_coeff] using hε

/-- For sufficiently small positive `eps`, every prescribed real root of a
monic real-rooted polynomial persists as a nearby real root of the
`iterateTDeriv` regularization. This is the concrete continuity bridge needed
for the `ε → 0` Obreschkoff transport route. -/
theorem exists_delta_and_real_root_near_iterateTDeriv
    (n : ℕ) {p : ℝ[X]} {a ε : ℝ}
    (ha : p.IsRoot a)
    (hp : IsRealRooted p) (hp_monic : p.Monic)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, 0 < eps → ‖eps‖ < δ →
      ∃ b : ℝ, (iterateTDeriv eps n p).IsRoot b ∧
        ‖a - b‖ < ((p.natDegree + 1) * ε) ^ ((p.natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  obtain ⟨δ, hδ, hcoeff⟩ := exists_delta_for_all_coeffs_iterateTDeriv_at_zero n p hε
  refine ⟨δ, hδ, ?_⟩
  intro eps heps_pos heps_small
  exact
    exists_real_root_near_of_isRealRooted_of_monic_of_coeff_close
      (f := p) (g := iterateTDeriv eps n p) (a := a) (ε := ε)
      hε ha hp_monic
      (monic_iterateTDeriv_of_isRealRooted hp hp_monic)
      (natDegree_iterateTDeriv_eq eps n p)
      (fun i => hcoeff heps_small i)
      (isRealRooted_iterateTDeriv heps_pos hp)

/-- Monic normalization is only a proof artifact in the `iterateTDeriv`
continuity route: for any nonzero real-rooted polynomial, each prescribed real
root persists under sufficiently small positive `iterateTDeriv` regularization.
This repackages the monic theorem above so the Obreschkoff converse can use it
after a single sign-normalization step, without having to rebuild the monic
scaling argument at each call site. -/
theorem exists_delta_and_real_root_near_iterateTDeriv_of_isRealRooted
    (n : ℕ) {p : ℝ[X]} {a ε : ℝ}
    (ha : p.IsRoot a)
    (hp : IsRealRooted p)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, 0 < eps → ‖eps‖ < δ →
      ∃ b : ℝ, (iterateTDeriv eps n p).IsRoot b ∧
        ‖a - b‖ < ((p.natDegree + 1) * ε) ^ ((p.natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  let c : ℝ := p.leadingCoeff⁻¹
  let p₀ : ℝ[X] := C c * p
  have hc_ne : c ≠ 0 := by
    exact inv_ne_zero (leadingCoeff_ne_zero.mpr hp.1)
  have hp₀_monic : p₀.Monic := by
    unfold p₀ c
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    field_simp [leadingCoeff_ne_zero.mpr hp.1]
  have hp₀_rr : IsRealRooted p₀ := by
    unfold p₀ c
    exact isRealRooted_C_mul hp (inv_ne_zero (leadingCoeff_ne_zero.mpr hp.1))
  have hp₀_deg : p₀.natDegree = p.natDegree := by
    unfold p₀ c
    rw [natDegree_C_mul hc_ne]
  have ha₀ : p₀.IsRoot a := by
    have ha_eval : p.eval a = 0 := by
      simpa [Polynomial.IsRoot.def] using ha
    have hp₀_eval : p₀.eval a = 0 := by
      simp [p₀, ha_eval]
    simpa [Polynomial.IsRoot.def] using hp₀_eval
  obtain ⟨δ, hδ, hnear⟩ :=
    exists_delta_and_real_root_near_iterateTDeriv n ha₀ hp₀_rr hp₀_monic hε
  refine ⟨δ, hδ, ?_⟩
  intro eps heps_pos heps_small
  obtain ⟨b, hb_root₀, hb_dist⟩ := hnear heps_pos heps_small
  have hb_eval₀ : (iterateTDeriv eps n p₀).eval b = 0 := by
    simpa [Polynomial.IsRoot.def] using hb_root₀
  have hb_eval_scaled : (C c * iterateTDeriv eps n p).eval b = 0 := by
    simpa [p₀, iterateTDeriv_C_mul_local] using hb_eval₀
  rw [Polynomial.eval_mul, Polynomial.eval_C] at hb_eval_scaled
  have hb_eval : (iterateTDeriv eps n p).eval b = 0 := by
    rcases mul_eq_zero.mp hb_eval_scaled with hc | hb
    · exact (hc_ne hc).elim
    · exact hb
  refine ⟨b, by simpa [Polynomial.IsRoot.def] using hb_eval, ?_⟩
  simpa [hp₀_deg] using hb_dist

/-- The nearby-root theorem is stable under passing to any iterated derivative,
because `iterateTDeriv` commutes with the derivative tower. This is the form
needed for multiplicity-cluster arguments: every original derivative root of
order `k` persists as a nearby derivative root of the regularized family. -/
theorem exists_delta_and_real_root_near_iterateTDeriv_of_isRealRooted_iterate_derivative
    (n k : ℕ) {p : ℝ[X]} {a ε : ℝ}
    (ha : ((derivative^[k]) p).IsRoot a)
    (hp : IsRealRooted ((derivative^[k]) p))
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, 0 < eps → ‖eps‖ < δ →
      ∃ b : ℝ, ((derivative^[k]) (iterateTDeriv eps n p)).IsRoot b ∧
        ‖a - b‖ <
          ((((derivative^[k]) p).natDegree + 1) * ε) ^
            ((((derivative^[k]) p).natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  obtain ⟨δ, hδ, hnear⟩ :=
    exists_delta_and_real_root_near_iterateTDeriv_of_isRealRooted
      (n := n) (p := (derivative^[k]) p) ha hp hε
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
    (hp : IsRealRooted ((derivative^[k]) p))
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, 0 < eps → ‖eps‖ < δ →
      ∃ b : ℝ, ((derivative^[k]) (iterateTDeriv eps n p)).IsRoot b ∧
        ‖a - b‖ <
          ((((derivative^[k]) p).natDegree + 1) * ε) ^
            ((((derivative^[k]) p).natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  apply exists_delta_and_real_root_near_iterateTDeriv_of_isRealRooted_iterate_derivative
    (n := n) (k := k) (p := p) (a := a) (ε := ε)
  · exact isRoot_iterate_derivative_of_lt_rootMultiplicity ha
  · exact hp
  · exact hε

/-- If `rootMultiplicity a p ≥ 1` and `rootMultiplicity a (T_ε p) ≥ 2`, then
    `rootMultiplicity a p ≥ 2` and the exact formula applies. In other words,
    a simple root can't produce a double root (it vanishes instead). -/
lemma rootMultiplicity_ge_two_of_TDeriv_ge_two
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (heps : 0 < eps) (hp_ne : p ≠ 0)
    (hdeg : 1 ≤ p.natDegree)
    (hroot : 1 ≤ p.rootMultiplicity a)
    (hm : 2 ≤ (TDeriv eps p).rootMultiplicity a) :
    2 ≤ p.rootMultiplicity a := by
  by_contra h
  push Not at h
  have h1 : p.rootMultiplicity a = 1 := by lia
  have hroot_a : p.IsRoot a := (rootMultiplicity_pos hp_ne).mp (by lia)
  have hnotroot := not_isRoot_TDeriv_of_simple_root (ne_of_gt heps) hp_ne hroot_a h1
  have hroot2 : (TDeriv eps p).IsRoot a :=
    (rootMultiplicity_pos (TDeriv_ne_zero hp_ne hdeg)).mp (by lia)
  exact hnotroot hroot2

/-- Factoring out a root of a real-rooted polynomial gives a real-rooted quotient. -/
private lemma isRealRooted_div_X_sub_C {p : ℝ[X]} {r : ℝ}
    (hp : IsRealRooted p) (_hr : p.IsRoot r)
    {t : ℝ[X]} (hpt : p = (X - C r) * t) :
    IsRealRooted t := by
  have hp_ne := hp.1
  have ht_ne : t ≠ 0 := right_ne_zero_of_mul (hpt ▸ hp_ne)
  refine ⟨ht_ne, ?_⟩
  have hXr_ne : (X : ℝ[X]) - C r ≠ 0 := X_sub_C_ne_zero r
  have hprod_ne : (X - C r) * t ≠ 0 := mul_ne_zero hXr_ne ht_ne
  have hdeg_p : p.natDegree = 1 + t.natDegree := by
    rw [hpt, natDegree_mul hXr_ne ht_ne, natDegree_X_sub_C]
  have hroots_eq : p.roots = (X - C r).roots + t.roots := by
    rw [hpt]; exact roots_mul hprod_ne
  have hcard : p.roots.card = 1 + t.roots.card := by
    rw [hroots_eq, Multiset.card_add, roots_X_sub_C]
    simp
  have hle : t.roots.card ≤ t.natDegree := card_roots' t
  have := hp.2
  lia

lemma deriv2_mul_lt_deriv_sq_at_non_root
    {p : ℝ[X]} {a : ℝ}
    (hp : IsRealRooted p) (hdeg : 1 ≤ p.natDegree) (ha : p.eval a ≠ 0) :
    p.derivative.derivative.eval a * p.eval a < p.derivative.eval a ^ 2 := by
  -- Strong induction on degree
  suffices ∀ (n : ℕ) (q : ℝ[X]), q.natDegree = n → IsRealRooted q → 1 ≤ n →
      q.eval a ≠ 0 →
      q.derivative.derivative.eval a * q.eval a < q.derivative.eval a ^ 2 from
    this p.natDegree p rfl hp hdeg ha
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro q hq_deg hq_rr hq_deg_pos hq_eval
    -- Get a root r of q (exists since degree ≥ 1 and real-rooted)
    have hq_ne := hq_rr.1
    have hroots_pos : 0 < q.roots.card := by rw [hq_rr.2]; lia
    obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
    have hr_root : q.IsRoot r := (mem_roots hq_ne).mp hr
    -- Factor: q = (X - C r) * t
    obtain ⟨t, hqt⟩ := dvd_iff_isRoot.mpr hr_root
    have ht_ne : t ≠ 0 := right_ne_zero_of_mul (hqt ▸ hq_ne)
    have ht_deg : t.natDegree = n - 1 := by
      have := congr_arg natDegree hqt
      rw [natDegree_mul (X_sub_C_ne_zero r) ht_ne, natDegree_X_sub_C] at this
      lia
    -- t is real-rooted
    have ht_rr : IsRealRooted t := isRealRooted_div_X_sub_C hq_rr hr_root hqt
    -- a ≠ r (since q(a) ≠ 0 but q(r) = 0)
    have har : a - r ≠ 0 := by
      intro h
      have : a = r := by linarith
      subst this; exact hq_eval hr_root
    -- t(a) ≠ 0
    have ht_eval : t.eval a ≠ 0 := by
      intro h
      have : q.eval a = (a - r) * t.eval a := by
        rw [hqt, eval_mul, eval_sub, eval_X, eval_C]
      rw [h, mul_zero] at this
      exact hq_eval this
    -- Derivatives of q in terms of t
    -- q = (X - C r) * t, so q' = t + (X - C r) * t'
    have hq' : q.derivative = t + (X - C r) * t.derivative := by
      rw [hqt, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
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
    have hqa : q.eval a = ar * ta := by
      rw [hqt, eval_mul, eval_sub, eval_X, eval_C]
    have hq'a : q.derivative.eval a = ta + ar * t'a := by
      rw [hq', eval_add, eval_mul, eval_sub, eval_X, eval_C]
    have hq''a : q.derivative.derivative.eval a = t'a + t'a + ar * t''a := by
      rw [hq'', eval_add, eval_add, eval_mul, eval_sub, eval_X, eval_C]
    -- Key algebraic identity:
    -- q''(a) * q(a) - q'(a)² = ar² * (t''a * ta - t'a²) - ta²
    have hident : q.derivative.derivative.eval a * q.eval a -
        q.derivative.eval a ^ 2 =
        ar ^ 2 * (t''a * ta - t'a ^ 2) - ta ^ 2 := by
      rw [hqa, hq'a, hq''a]; ring
    -- Show the RHS is negative
    rw [show q.derivative.derivative.eval a * q.eval a <
        q.derivative.eval a ^ 2 ↔
        q.derivative.derivative.eval a * q.eval a -
        q.derivative.eval a ^ 2 < 0 from by constructor <;> intro h <;> linarith]
    rw [hident]
    -- Two cases: n = 1 (t is constant) or n ≥ 2 (use IH)
    by_cases hn1 : n = 1
    · -- n = 1: t has degree 0, t' = t'' = 0
      have ht_deg0 : t.natDegree = 0 := by lia
      have ht'_zero : t.derivative = 0 := by
        have := eq_C_of_natDegree_eq_zero ht_deg0; rw [this]; simp
      have ht'a_zero : t'a = 0 := by
        change t.derivative.eval a = 0
        rw [ht'_zero, eval_zero]
      have ht''a_zero : t''a = 0 := by
        change t.derivative.derivative.eval a = 0
        rw [ht'_zero, derivative_zero, eval_zero]
      rw [ht'a_zero, ht''a_zero]
      simp only [zero_mul, zero_sub]
      linarith [sq_pos_of_ne_zero ht_eval]
    · -- n ≥ 2: use IH on t
      have ht_ih := ih (n - 1) (by lia) t ht_deg ht_rr (by lia) ht_eval
      have h_neg : t''a * ta - t'a ^ 2 < 0 := by linarith
      have h1 : ar ^ 2 * (t''a * ta - t'a ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ar) (le_of_lt h_neg)
      linarith [sq_pos_of_ne_zero ht_eval]

/-- `T_ε` cannot create double roots at non-roots of a real-rooted polynomial.

If `p` is real-rooted with `p(a) ≠ 0`, then `rootMultiplicity a (T_ε p) ≤ 1`.

Proof: if `T_ε p` had a double root at `a`, then `p(a) = ε·p'(a)` and `p'(a) = ε·p''(a)`,
giving `p''(a)·p(a) = p'(a)²`. But `deriv2_mul_lt_deriv_sq_at_non_root` says
`p''(a)·p(a) < p'(a)²`. Contradiction. -/
lemma rootMultiplicity_TDeriv_le_one_of_not_isRoot
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (heps : 0 < eps) (hp : IsRealRooted p)
    (hdeg : 1 ≤ p.natDegree)
    (ha : ¬ p.IsRoot a) :
    (TDeriv eps p).rootMultiplicity a ≤ 1 := by
  by_contra h
  push Not at h
  -- rootMultiplicity ≥ 2 means (TDeriv eps p)(a) = 0 and (TDeriv eps p)'(a) = 0
  have hT_ne : TDeriv eps p ≠ 0 := TDeriv_ne_zero hp.1 hdeg
  have hT_root : (TDeriv eps p).IsRoot a :=
    (rootMultiplicity_pos hT_ne).mp (by lia)
  have hT_deriv_root : (TDeriv eps p).derivative.IsRoot a := by
    have h2 : 2 ≤ (TDeriv eps p).rootMultiplicity a := by lia
    have hdvd := pow_rootMultiplicity_dvd (TDeriv eps p) a
    have hdvd2 : (X - C a) ^ 2 ∣ TDeriv eps p := (pow_dvd_pow _ h2).trans hdvd
    have hdvd1 : (X - C a) ^ 1 ∣ (TDeriv eps p).derivative :=
      pow_one (X - C a) ▸ pow_sub_one_dvd_derivative_of_pow_dvd hdvd2
    rw [pow_one] at hdvd1
    exact dvd_iff_isRoot.mp hdvd1
  -- Extract the two conditions
  have hpa : p.eval a ≠ 0 := ha
  have hcond1 : p.eval a = eps * p.derivative.eval a := by
    have := hT_root
    simp only [TDeriv, Polynomial.IsRoot, eval_sub, eval_mul, eval_C] at this
    linarith
  have hcond2 : p.derivative.eval a = eps * p.derivative.derivative.eval a := by
    have := hT_deriv_root
    have hT_deriv : (TDeriv eps p).derivative = p.derivative - C eps * p.derivative.derivative := by
      simp [TDeriv, derivative_sub]
    rw [hT_deriv] at this
    simp only [Polynomial.IsRoot, eval_sub, eval_mul, eval_C] at this
    linarith
  -- From these: p''(a) · p(a) = p'(a)²
  have heps_ne : eps ≠ 0 := ne_of_gt heps
  have heq : p.derivative.derivative.eval a * p.eval a = p.derivative.eval a ^ 2 := by
    rw [hcond1, hcond2]; ring
  -- But for real-rooted p at non-roots: p''(a) · p(a) < p'(a)²
  have hlt := deriv2_mul_lt_deriv_sq_at_non_root hp hdeg hpa
  linarith

/-- Backward chain: if `rootMultiplicity a (TDeriv eps p) ≥ 2` and `p` is real-rooted with
    `deg ≥ 1`, then `rootMultiplicity a p ≥ 2` and in fact equals
    `rootMultiplicity a (TDeriv eps p) + 1`. -/
lemma rootMultiplicity_eq_succ_of_TDeriv_ge_two
    {eps : ℝ} {p : ℝ[X]} {a : ℝ}
    (heps : 0 < eps) (hp : IsRealRooted p)
    (hdeg : 1 ≤ p.natDegree)
    (hm : 2 ≤ (TDeriv eps p).rootMultiplicity a) :
    p.rootMultiplicity a = (TDeriv eps p).rootMultiplicity a + 1 := by
  -- rootMultiplicity a p can't be 0 (non-root → TDeriv mult ≤ 1)
  have hroot : p.IsRoot a := by
    by_contra ha
    have := rootMultiplicity_TDeriv_le_one_of_not_isRoot heps hp hdeg ha
    lia
  -- rootMultiplicity a p can't be 1 (simple root vanishes)
  have h2 : 2 ≤ p.rootMultiplicity a := by
    have h1 := (rootMultiplicity_pos hp.1).mpr hroot
    by_contra hlt; push Not at hlt
    have h1eq : p.rootMultiplicity a = 1 := by lia
    have := not_isRoot_TDeriv_of_simple_root (ne_of_gt heps) hp.1 hroot h1eq
    exact this ((rootMultiplicity_pos (TDeriv_ne_zero hp.1 hdeg)).mp (by lia))
  -- Exact formula from rootMultiplicity_TDeriv_of_multiple
  rw [rootMultiplicity_TDeriv_of_multiple (ne_of_gt heps) hp.1 h2
      (TDeriv_ne_zero hp.1 hdeg)]
  lia

/-- Exact multiplicity transport along the `iterateTDeriv` chain as long as the
root has not yet vanished. This is the algebraic core behind the
double-root reduction in the Obreschkoff converse: iterating `T_ε` simply
subtracts one from the multiplicity at each step until the root disappears. -/
lemma rootMultiplicity_iterateTDeriv_eq_tsub
    {eps : ℝ} {p : ℝ[X]} {a : ℝ} {n : ℕ}
    (heps : 0 < eps) (hp : IsRealRooted p)
    (hn : n ≤ p.rootMultiplicity a) :
    (iterateTDeriv eps n p).rootMultiplicity a = p.rootMultiplicity a - n := by
  induction n generalizing p with
  | zero =>
      simp [iterateTDeriv]
  | succ n ih =>
      rw [iterateTDeriv_succ]
      have hn' : n ≤ p.rootMultiplicity a := le_trans (Nat.le_succ n) hn
      set q : ℝ[X] := iterateTDeriv eps n p
      have hq_rr : IsRealRooted q := by
        dsimp [q]
        exact isRealRooted_iterateTDeriv (eps := eps) (k := n) heps hp
      have hq_mult : q.rootMultiplicity a = p.rootMultiplicity a - n := by
        simpa [q] using ih hp hn'
      have hq_mult_pos : 1 ≤ q.rootMultiplicity a := by
        rw [hq_mult]
        lia
      have hq_root : q.IsRoot a := by
        exact (rootMultiplicity_pos hq_rr.1).mp (by lia)
      by_cases hq_simple : q.rootMultiplicity a = 1
      · have hnot_root : ¬ (TDeriv eps q).IsRoot a :=
          not_isRoot_TDeriv_of_simple_root
            (ne_of_gt heps) hq_rr.1 hq_root hq_simple
        have hrootmult_zero : (TDeriv eps q).rootMultiplicity a = 0 := by
          exact rootMultiplicity_eq_zero hnot_root
        have hmult_eq_one : p.rootMultiplicity a - n = 1 := by
          simpa [hq_mult] using hq_simple
        rw [hrootmult_zero]
        lia
      · have hq_mult_ge2 : 2 ≤ q.rootMultiplicity a := by lia
        have hq_deg : 1 ≤ q.natDegree := by
          calc
            1 ≤ q.rootMultiplicity a := hq_mult_pos
            _ = q.roots.count a := (count_roots q).symm
            _ ≤ q.roots.card := q.roots.count_le_card a
            _ ≤ q.natDegree := card_roots' q
        have hT_ne : TDeriv eps q ≠ 0 := TDeriv_ne_zero hq_rr.1 hq_deg
        rw [rootMultiplicity_TDeriv_of_multiple (ne_of_gt heps) hq_rr.1 hq_mult_ge2 hT_ne,
          hq_mult]
        lia

/--
Chudnovsky--Seymour style iterate (Ryder, Lemma 6.4): for `ε > 0` and `deg f = n`,
the polynomial `(T_ε)^[n] f` is real-rooted and has simple roots.

Proof by contradiction: if the iterate has a root `a` with mult `M ≥ 2`, trace backward.
At each step, mult can't drop below 2 (simple roots vanish, non-roots stay ≤ 1).
So `rootMultiplicity a f ≥ M + n ≥ n + 2`, contradicting `rootMultiplicity ≤ natDegree = n`.
-/
theorem isRealRooted_and_hasSimpleRoots_iterateTDeriv
    {f : ℝ[X]} {n : ℕ} {eps : ℝ}
    (heps : 0 < eps)
    (hf : IsRealRooted f)
    (hdeg : f.natDegree = n) :
    IsRealRooted (iterateTDeriv eps n f) ∧ HasSimpleRoots (iterateTDeriv eps n f) := by
  refine ⟨isRealRooted_iterateTDeriv heps hf, ?_⟩
  intro a ha
  by_contra hmult; push Not at hmult
  have hne : iterateTDeriv eps n f ≠ 0 := (isRealRooted_iterateTDeriv heps hf).1
  have hge2 : 2 ≤ (iterateTDeriv eps n f).rootMultiplicity a := by
    have := (rootMultiplicity_pos hne).mpr ha; lia
  -- Backward induction: mult at step k ≥ 2 + (n - k)
  -- We prove this by induction on j = n - k (distance from the end)
  have step : ∀ j, j ≤ n →
      2 + j ≤ (iterateTDeriv eps (n - j) f).rootMultiplicity a := by
    intro j
    induction j with
    | zero => intro _; simpa using hge2
    | succ j ih =>
      intro hj
      have hprev := ih (by lia)
      -- At step n - j: mult ≥ 2 + j ≥ 2
      -- iterateTDeriv eps (n - j) f = TDeriv eps (iterateTDeriv eps (n - j - 1) f)
      have hstep : n - j = (n - (j + 1)) + 1 := by lia
      rw [hstep, iterateTDeriv_succ] at hprev
      have hp_rr := isRealRooted_iterateTDeriv (eps := eps) (k := n - (j + 1)) heps hf
      have hp_deg : 1 ≤ (iterateTDeriv eps (n - (j + 1)) f).natDegree := by
        rw [natDegree_iterateTDeriv hf.1 (by lia)]; lia
      have := rootMultiplicity_eq_succ_of_TDeriv_ge_two heps hp_rr hp_deg
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

end RealRooted
