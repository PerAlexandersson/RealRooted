module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Computability.DFA
public import Mathlib.Data.Nat.ModEq
public import Mathlib.NumberTheory.FrobeniusNumber
public import RealRooted.Basic.Coefficients

/-!
# Degree defects for positive finite-memory symbols

This file develops the finite algebraic part of the positive finite-memory symbol
construction.  It records the two no-cancellation lemmas needed for highest and lowest
polynomial degree, defines the symbol generating series, and extracts its fundamental
recurrence.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-! ## No cancellation at the two ends of a polynomial -/

/-- The degree of a sum of two nonzero polynomials with nonnegative coefficients is the
maximum of their degrees. -/
theorem HasNonnegCoeffs.natDegree_add_eq_max {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    (p + q).natDegree = max p.natDegree q.natDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · simpa only [max_comm] using Polynomial.natDegree_add_le p q
  · rw [Polynomial.coeff_add]
    rcases le_total p.natDegree q.natDegree with hpq | hqp
    · rw [max_eq_right hpq]
      exact (add_pos_of_nonneg_of_pos (hp q.natDegree)
        (lt_of_le_of_ne (hq q.natDegree)
          (Ne.symm (Polynomial.leadingCoeff_ne_zero.mpr hq0)))).ne'
    · rw [max_eq_left hqp]
      exact (add_pos_of_pos_of_nonneg
        (lt_of_le_of_ne (hp p.natDegree)
          (Ne.symm (Polynomial.leadingCoeff_ne_zero.mpr hp0)))
        (hq p.natDegree)).ne'

/-- The trailing degree of a sum of two nonzero polynomials with nonnegative coefficients is
the minimum of their trailing degrees. -/
theorem HasNonnegCoeffs.natTrailingDegree_add_eq_min {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    (p + q).natTrailingDegree = min p.natTrailingDegree q.natTrailingDegree := by
  have hpq0 : p + q ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hp hq hq0
  apply le_antisymm
  · apply Polynomial.natTrailingDegree_le_of_ne_zero
    rw [Polynomial.coeff_add]
    rcases le_total p.natTrailingDegree q.natTrailingDegree with hpq | hqp
    · rw [min_eq_left hpq]
      exact (add_pos_of_pos_of_nonneg
        (lt_of_le_of_ne (hp p.natTrailingDegree)
          (Ne.symm (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp0)))
        (hq p.natTrailingDegree)).ne'
    · rw [min_eq_right hqp]
      exact (add_pos_of_nonneg_of_pos (hp q.natTrailingDegree)
        (lt_of_le_of_ne (hq q.natTrailingDegree)
          (Ne.symm (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hq0)))).ne'
  · apply Polynomial.le_natTrailingDegree hpq0
    intro n hn
    rw [Polynomial.coeff_add]
    have hnp : n < p.natTrailingDegree := lt_of_lt_of_le hn (min_le_left _ _)
    have hnq : n < q.natTrailingDegree := lt_of_lt_of_le hn (min_le_right _ _)
    rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hnp,
      Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hnq, add_zero]

namespace FiniteMemory

/-! ## The fundamental symbol series -/

/-- The lag polynomial of a finite-memory symbol, viewed as a power series in the row
index.  The coefficient indexed by `i : Fin r` occurs at the positive lag `i + 1`. -/
def lagSeries {r : ℕ} (p : Fin r → ℝ[X]) : PowerSeries ℝ[X] :=
  ∑ i, PowerSeries.monomial (i.1 + 1) (p i)

/-- The generating series of the fundamental rows of a finite-memory symbol. -/
def symbolSeries {r : ℕ} (p : Fin r → ℝ[X]) : PowerSeries ℝ[X] :=
  PowerSeries.invOfUnit (1 - lagSeries p) 1

/-- The `n`th fundamental row of a finite-memory symbol. -/
def symbolRow {r : ℕ} (p : Fin r → ℝ[X]) (n : ℕ) : ℝ[X] :=
  PowerSeries.coeff n (symbolSeries p)

/-- A lag series has zero constant coefficient. -/
@[simp] theorem constantCoeff_lagSeries {r : ℕ} (p : Fin r → ℝ[X]) :
    PowerSeries.constantCoeff (lagSeries p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [lagSeries, map_sum, PowerSeries.coeff_monomial, Nat.zero_ne_add_one,
    ↓reduceIte, Finset.sum_const_zero]

/-- The symbol series is the inverse of `1 - lagSeries`. -/
theorem symbolSeries_mul_one_sub_lagSeries {r : ℕ} (p : Fin r → ℝ[X]) :
    symbolSeries p * (1 - lagSeries p) = 1 := by
  apply PowerSeries.invOfUnit_mul
  simp

/-- The zeroth fundamental row is one. -/
@[simp] theorem symbolRow_zero {r : ℕ} (p : Fin r → ℝ[X]) :
    symbolRow p 0 = 1 := by
  simp [symbolRow, symbolSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- Positive convolution form of the fundamental recurrence away from the initial row. -/
theorem symbolRow_eq_sum_mul_coeff_lagSeries {r : ℕ} (p : Fin r → ℝ[X])
    {n : ℕ} (hn : n ≠ 0) :
    symbolRow p n = ∑ x ∈ Finset.antidiagonal n,
      symbolRow p x.1 * PowerSeries.coeff x.2 (lagSeries p) := by
  have hcoeff := congrArg (PowerSeries.coeff n)
    (symbolSeries_mul_one_sub_lagSeries p)
  simp only [mul_sub, mul_one] at hcoeff
  rw [map_sub, PowerSeries.coeff_mul, PowerSeries.coeff_one, ite_eq_right hn] at hcoeff
  change symbolRow p n - ∑ x ∈ Finset.antidiagonal n,
    symbolRow p x.1 * PowerSeries.coeff x.2 (lagSeries p) = 0 at hcoeff
  exact sub_eq_zero.mp hcoeff

/-- Coefficients of the lag series are finite sums over lags of the requested size. -/
theorem coeff_lagSeries {r : ℕ} (p : Fin r → ℝ[X]) (n : ℕ) :
    PowerSeries.coeff n (lagSeries p) = ∑ i, if n = i.1 + 1 then p i else 0 := by
  simp only [lagSeries, map_sum, PowerSeries.coeff_monomial]

/-- Coefficientwise nonnegative symbol coefficients give coefficientwise nonnegative
coefficients of the lag series. -/
theorem hasNonnegCoeffs_coeff_lagSeries {r : ℕ} {p : Fin r → ℝ[X]}
    (hp : ∀ i, HasNonnegCoeffs (p i)) (n : ℕ) :
    HasNonnegCoeffs (PowerSeries.coeff n (lagSeries p)) := by
  rw [coeff_lagSeries]
  apply hasNonnegCoeffs_finsetSum
  intro i _
  split <;> simp_all only [hasNonnegCoeffs_zero]

/-- Every fundamental row has nonnegative coefficients when all symbol coefficients do. -/
theorem symbolRow_hasNonnegCoeffs {r : ℕ} {p : Fin r → ℝ[X]}
    (hp : ∀ i, HasNonnegCoeffs (p i)) (n : ℕ) :
    HasNonnegCoeffs (symbolRow p n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simpa only [symbolRow_zero] using hasNonnegCoeffs_one
      · rw [symbolRow_eq_sum_mul_coeff_lagSeries p hn]
        apply hasNonnegCoeffs_finsetSum
        intro x hx
        by_cases hx2 : x.2 = 0
        · rw [hx2, PowerSeries.coeff_zero_eq_constantCoeff_apply,
            constantCoeff_lagSeries, mul_zero]
          exact hasNonnegCoeffs_zero
        · apply (ih x.1 ?_).mul (hasNonnegCoeffs_coeff_lagSeries hp x.2)
          rw [Finset.mem_antidiagonal] at hx
          lia

/-! ## Finite residue bridges -/

/-- The total lag of a word in the lag alphabet. -/
def wordLag (w : List ℕ) : ℕ := w.sum

/-- The additive cost of a lag word. -/
def wordCost (δ : ℕ → ℕ) (w : List ℕ) : ℕ := (w.map δ).sum

/-- A word uses only active positive lags bounded by the memory `r`. -/
def IsLagWord (r : ℕ) (active : Set ℕ) (w : List ℕ) : Prop :=
  ∀ l ∈ w, l ∈ active ∧ 1 ≤ l ∧ l ≤ r

/-- Finite bridge data that certifies the sharp eventual defect formula.

The bridge for a residue modulo the chosen critical lag `p` realizes the globally minimal
cost of its residue modulo `q`.  The last field is exactly the numerical estimate supplied
by a simple path in the residue graph. -/
structure SharpDefectBridges (r p q : ℕ) (active : Set ℕ) (δ K : ℕ → ℕ) where
  p_pos : 0 < p
  critical_active : p ∈ active
  critical_le : p ≤ r
  critical_cost : δ p = 0
  q_dvd_p : q ∣ p
  /-- For each residue `a` modulo `p`, a lag word whose total lag is congruent to `a`. -/
  bridge : Fin p → List ℕ
  valid : ∀ a, IsLagWord r active (bridge a)
  congruent : ∀ a, Nat.ModEq p (wordLag (bridge a)) a.1
  realizes : ∀ a, wordCost δ (bridge a) = K (wordLag (bridge a) % q)
  minimal : ∀ w, IsLagWord r active w → K (wordLag w % q) ≤ wordCost δ w
  sharp : ∀ a, wordLag (bridge a) + 1 ≤ (r - 1) * (r - 2) + p

/-- A sharp bridge can be padded by the critical lag to give an exact-length minimum-cost
word at every index beyond `(r - 1) * (r - 2)`. -/
theorem SharpDefectBridges.exists_exact_minimizer
    {r p q : ℕ} {active : Set ℕ} {δ K : ℕ → ℕ}
    (h : SharpDefectBridges r p q active δ K) {n : ℕ}
    (hn : (r - 1) * (r - 2) ≤ n) :
    ∃ w, IsLagWord r active w ∧ wordLag w = n ∧
      wordCost δ w = K (n % q) ∧
      ∀ v, IsLagWord r active v → wordLag v = n → K (n % q) ≤ wordCost δ v := by
  let a : Fin p := ⟨n % p, Nat.mod_lt n h.p_pos⟩
  let b := h.bridge a
  have ha_mod : Nat.ModEq p a.1 n := by
    simp only [a, Nat.ModEq, Nat.mod_mod]
  have hb_mod : Nat.ModEq p (wordLag b) n := (h.congruent a).trans ha_mod
  have hb_lt : wordLag b < n + p := by
    have hsharp := h.sharp a
    dsimp only [b] at hsharp ⊢
    lia
  have hb_le : wordLag b ≤ n := hb_mod.le_of_lt_add hb_lt
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add hb_le).mp hb_mod
  let w := b ++ List.replicate t p
  have hw_lag : wordLag w = n := by
    simp only [w, wordLag, List.sum_append, List.sum_replicate]
    calc
      b.sum + t * p = b.sum + p * t := by rw [mul_comm t p]
      _ = n := ht.symm
  have hw_valid : IsLagWord r active w := by
    intro l hl
    simp only [w, List.mem_append, List.mem_replicate] at hl
    rcases hl with hl | ⟨_, rfl⟩
    · exact h.valid a l hl
    · exact ⟨h.critical_active, h.p_pos, h.critical_le⟩
  have hb_mod_q : wordLag b % q = n % q := hb_mod.of_dvd h.q_dvd_p
  have hw_cost : wordCost δ w = K (n % q) := by
    simp only [w, wordCost, List.map_append, List.sum_append, List.map_replicate,
      List.sum_replicate, h.critical_cost, nsmul_zero, add_zero]
    change wordCost δ b = K (n % q)
    rw [h.realizes a, hb_mod_q]
  refine ⟨w, hw_valid, hw_lag, hw_cost, ?_⟩
  intro v hv hv_lag
  simpa only [hv_lag] using h.minimal v hv

/-- The active lags of zero defect. -/
def criticalLags (active : Set ℕ) (δ : ℕ → ℕ) : Set ℕ :=
  {l | l ∈ active ∧ δ l = 0}

/-- The least cost of an active lag word in a prescribed residue class. -/
def residueDefect (r q : ℕ) (active : Set ℕ) (δ : ℕ → ℕ) (a : ℕ) : ℕ :=
  sInf {c | ∃ w, IsLagWord r active w ∧ wordLag w % q = a % q ∧ wordCost δ w = c}

/-- The residue defect is no larger than the cost of any word in that residue class. -/
theorem residueDefect_le_wordCost {r q : ℕ} {active : Set ℕ} {δ : ℕ → ℕ}
    {a : ℕ} {w : List ℕ} (hw : IsLagWord r active w)
    (hres : wordLag w % q = a % q) :
    residueDefect r q active δ a ≤ wordCost δ w := by
  exact Nat.sInf_le ⟨w, hw, hres, rfl⟩

/-- A nonempty residue class contains a word whose cost is its residue defect. -/
theorem exists_wordCost_eq_residueDefect {r q : ℕ} {active : Set ℕ} {δ : ℕ → ℕ}
    {a : ℕ} (h : ∃ w, IsLagWord r active w ∧ wordLag w % q = a % q) :
    ∃ w, IsLagWord r active w ∧ wordLag w % q = a % q ∧
      wordCost δ w = residueDefect r q active δ a := by
  change sInf {c | ∃ w, IsLagWord r active w ∧ wordLag w % q = a % q ∧
    wordCost δ w = c} ∈
      {c | ∃ w, IsLagWord r active w ∧ wordLag w % q = a % q ∧ wordCost δ w = c}
  apply Nat.sInf_mem
  obtain ⟨w, hw, hres⟩ := h
  exact ⟨wordCost δ w, w, hw, hres, rfl⟩

/-- Residue defects agree when their indices agree modulo the residue modulus. -/
theorem residueDefect_eq_of_modEq {r q : ℕ} {active : Set ℕ} {δ : ℕ → ℕ}
    {a b : ℕ} (h : Nat.ModEq q a b) :
    residueDefect r q active δ a = residueDefect r q active δ b := by
  rw [residueDefect, residueDefect, h]

private def residueDFA (p : ℕ) (hp : 0 < p) : DFA ℕ (Fin p) where
  step a l := ⟨(a.1 + l) % p, Nat.mod_lt _ hp⟩
  start := ⟨0, hp⟩
  accept := Set.univ

private theorem residueDFA_evalFrom_val (p : ℕ) (hp : 0 < p) (a : Fin p)
    (w : List ℕ) :
    ((residueDFA p hp).evalFrom a w).1 = (a.1 + wordLag w) % p := by
  induction w generalizing a with
  | nil => simp [wordLag, Nat.mod_eq_of_lt a.isLt]
  | cons l w ih =>
      rw [DFA.evalFrom_cons, ih]
      change Nat.ModEq p (((a.1 + l) % p) + wordLag w) (a.1 + (l + wordLag w))
      simpa only [Nat.add_assoc] using
        (Nat.mod_modEq (a.1 + l) p).add (Nat.ModEq.refl (wordLag w))

private theorem residueDFA_eval_val (p : ℕ) (hp : 0 < p) (w : List ℕ) :
    ((residueDFA p hp).eval w).1 = wordLag w % p := by
  simpa only [DFA.eval, residueDFA, zero_add] using
    residueDFA_evalFrom_val p hp (residueDFA p hp).start w

private theorem exists_lagWord_modEq (r p : ℕ) (active : Set ℕ)
    (hp : 0 < p) (hsetGcd : Nat.setGcd active = 1)
    (hpos : ∀ l ∈ active, 1 ≤ l) (hle : ∀ l ∈ active, l ≤ r) (a : Fin p) :
    ∃ w, IsLagWord r active w ∧ Nat.ModEq p (wordLag w) a.1 := by
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge active
  let m := a.1 + p * N
  have hNm : N ≤ m := by dsimp only [m]; nlinarith
  have hm : m ∈ AddSubmonoid.closure active := by
    apply hN m hNm
    rw [hsetGcd]
    exact one_dvd m
  obtain ⟨w, hw, hsum⟩ := AddSubmonoid.exists_list_of_mem_closure hm
  refine ⟨w, ?_, ?_⟩
  · exact fun l hl ↦ ⟨hw l hl, hpos l (hw l hl), hle l (hw l hl)⟩
  · rw [wordLag, hsum]
    simp [m, Nat.ModEq, Nat.add_mod, Nat.mod_eq_of_lt a.isLt]

private theorem exists_short_lagWord {r p : ℕ} {active : Set ℕ} {δ : ℕ → ℕ}
    (hp : 0 < p) (w : List ℕ) (hw : IsLagWord r active w) :
    ∃ v, IsLagWord r active v ∧ Nat.ModEq p (wordLag v) (wordLag w) ∧
      wordCost δ v ≤ wordCost δ w ∧ v.length < p := by
  by_cases hlength : w.length < p
  · exact ⟨w, hw, Nat.ModEq.refl _, le_rfl, hlength⟩
  · let M := residueDFA p hp
    obtain ⟨s, u, v, z, hw_decomp, _, hv, hu, _, hz⟩ :=
      M.evalFrom_split (s := M.start) (t := M.eval w)
        (by simpa only [Fintype.card_fin] using Nat.le_of_not_gt hlength) rfl
    let w' := u ++ z
    have hw'_valid : IsLagWord r active w' := by
      intro l hl
      apply hw l
      rw [hw_decomp]
      simp only [w', List.mem_append] at hl ⊢
      exact hl.elim (fun hlu ↦ Or.inl (Or.inl hlu)) Or.inr
    have heval : M.eval w' = M.eval w := by
      simp only [w', DFA.eval, M.evalFrom_of_append, hu, hz]
    have hw'_mod : Nat.ModEq p (wordLag w') (wordLag w) := by
      change wordLag w' % p = wordLag w % p
      rw [← residueDFA_eval_val p hp w', ← residueDFA_eval_val p hp w, heval]
    have hw'_cost : wordCost δ w' ≤ wordCost δ w := by
      simp only [w', hw_decomp, wordCost, List.map_append, List.sum_append]
      lia
    have hw'_length : w'.length < w.length := by
      simp only [w', hw_decomp, List.length_append]
      have := List.length_pos_of_ne_nil hv
      lia
    obtain ⟨x, hx, hxmod, hxcost, hxlength⟩ :=
      exists_short_lagWord hp w' hw'_valid
    exact ⟨x, hx, hxmod.trans hw'_mod, hxcost.trans hw'_cost, hxlength⟩
termination_by w.length
decreasing_by exact hw'_length

private def eraseLag (p : ℕ) : List ℕ → List ℕ
  | [] => []
  | l :: w => if l = p then eraseLag p w else l :: eraseLag p w

private theorem eraseLag_isLagWord {r p : ℕ} {active : Set ℕ} {w : List ℕ}
    (hw : IsLagWord r active w) : IsLagWord r active (eraseLag p w) := by
  induction w with
  | nil => simp [eraseLag, IsLagWord]
  | cons l w ih =>
      by_cases h : l = p <;> simp_all [eraseLag, IsLagWord]

private theorem wordLag_eraseLag_modEq (p : ℕ) (w : List ℕ) :
    Nat.ModEq p (wordLag (eraseLag p w)) (wordLag w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
      rw [eraseLag]
      split
      · rename_i hl
        subst l
        simpa only [wordLag, List.sum_cons, zero_add] using
          (Nat.modulus_modEq_zero (n := p)).symm.add ih
      · simpa only [wordLag, List.sum_cons] using
          (Nat.ModEq.refl l).add ih

private theorem wordCost_eraseLag_eq {p : ℕ} {δ : ℕ → ℕ} (hp : δ p = 0)
    (w : List ℕ) : wordCost δ (eraseLag p w) = wordCost δ w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
      rw [eraseLag]
      split
      · rename_i hl
        subst l
        simpa only [wordCost, List.map_cons, List.sum_cons, hp, zero_add] using ih
      · simpa only [wordCost, List.map_cons, List.sum_cons] using congrArg (δ l + ·) ih

private theorem not_mem_eraseLag (p : ℕ) (w : List ℕ) : p ∉ eraseLag p w := by
  induction w with
  | nil => simp [eraseLag]
  | cons l w ih =>
      rw [eraseLag]
      split
      · exact ih
      · rename_i h
        simpa only [List.mem_cons, not_or] using ⟨Ne.symm h, ih⟩

private theorem length_eraseLag_le (p : ℕ) (w : List ℕ) :
    (eraseLag p w).length ≤ w.length := by
  induction w with
  | nil => simp [eraseLag]
  | cons l w ih =>
      rw [eraseLag]
      split
      · exact ih.trans (Nat.le_succ _)
      · exact Nat.succ_le_succ ih

theorem wordLag_le_length_mul {r : ℕ} {active : Set ℕ} {w : List ℕ}
    (hw : IsLagWord r active w) : wordLag w ≤ w.length * r := by
  induction w with
  | nil => simp [wordLag]
  | cons l w ih =>
      have hl := (hw l (by simp)).2.2
      specialize ih (fun x hx ↦ hw x (by simp [hx]))
      simp only [wordLag, List.sum_cons, List.length_cons]
      calc
        l + w.sum ≤ r + w.length * r := Nat.add_le_add hl ih
        _ = (w.length + 1) * r := by ring

private theorem wordCost_eq_zero_of_mem {active : Set ℕ} {δ : ℕ → ℕ} {w : List ℕ}
    (hw : ∀ l ∈ w, l ∈ criticalLags active δ) : wordCost δ w = 0 := by
  induction w <;> simp_all [wordCost, criticalLags]

private theorem exists_zeroCost_adjustment {r p q x y : ℕ} {active : Set ℕ}
    {δ : ℕ → ℕ} (hp : 0 < p) (hp_active : p ∈ active) (hp_cost : δ p = 0)
    (hq : Nat.setGcd (criticalLags active δ) = q)
    (hpos : ∀ l ∈ active, 1 ≤ l) (hle : ∀ l ∈ active, l ≤ r)
    (hxy : Nat.ModEq q x y) :
    ∃ z, IsLagWord r active z ∧ wordCost δ z = 0 ∧
      Nat.ModEq p (x + wordLag z) y := by
  have hqp : q ∣ p := by
    rw [← hq]
    exact Nat.setGcd_dvd_of_mem ⟨hp_active, hp_cost⟩
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge (criticalLags active δ)
  let m := y + p * (x + N + 1)
  have hxle : x ≤ m := by dsimp only [m]; nlinarith
  have hNle : N ≤ m - x := by
    apply Nat.le_sub_of_add_le
    have hmul := Nat.mul_le_mul_right (x + N + 1) (Nat.succ_le_iff.mpr hp)
    dsimp only [m]
    nlinarith
  have hym : Nat.ModEq q y m := by
    simpa only [m, add_zero] using
      (Nat.ModEq.refl y).add (dvd_mul_of_dvd_left hqp _).zero_modEq_nat
  have hdiv : q ∣ m - x := (hxy.trans hym).dvd'
  have hmem : m - x ∈ AddSubmonoid.closure (criticalLags active δ) :=
    hN (m - x) hNle (hq ▸ hdiv)
  obtain ⟨z, hz, hsum⟩ := AddSubmonoid.exists_list_of_mem_closure hmem
  refine ⟨z, fun l hl ↦ ⟨(hz l hl).1, hpos l (hz l hl).1, hle l (hz l hl).1⟩,
    wordCost_eq_zero_of_mem hz, ?_⟩
  change (x + wordLag z) % p = y % p
  rw [wordLag, hsum, Nat.add_sub_of_le hxle]
  simp [m, Nat.add_mod]

theorem exists_bounded_residue_minimizer {r p q : ℕ} {active : Set ℕ}
    {δ : ℕ → ℕ} (hp : 0 < p) (hq_pos : 0 < q) (hp_active : p ∈ active)
    (hp_cost : δ p = 0) (hq : Nat.setGcd (criticalLags active δ) = q)
    (hsetGcd : Nat.setGcd active = 1) (hpos : ∀ l ∈ active, 1 ≤ l)
    (hle : ∀ l ∈ active, l ≤ r) (a : Fin p) :
    ∃ w, IsLagWord r active w ∧ Nat.ModEq p (wordLag w) a.1 ∧
      wordCost δ w = residueDefect r q active δ a.1 ∧ w.length < p ∧ p ∉ w := by
  let aq : Fin q := ⟨a.1 % q, Nat.mod_lt _ hq_pos⟩
  obtain ⟨v, hv, hvmod⟩ := exists_lagWord_modEq r q active hq_pos hsetGcd hpos hle aq
  have hvres : wordLag v % q = a.1 % q := by
    exact hvmod.trans (Nat.mod_modEq a.1 q)
  obtain ⟨v, hv, hvres, hvcost⟩ :=
    exists_wordCost_eq_residueDefect (active := active) (δ := δ) ⟨v, hv, hvres⟩
  have hvmod : Nat.ModEq q (wordLag v) a.1 := hvres
  obtain ⟨z, hz, hzcost, hzmod⟩ := exists_zeroCost_adjustment hp hp_active hp_cost hq
    hpos hle hvmod
  have hvz_valid : IsLagWord r active (v ++ z) := by
    intro l hl
    exact (List.mem_append.mp hl).elim (hv l) (hz l)
  obtain ⟨u, hu, humod, hucost, hulength⟩ :=
    exists_short_lagWord hp (v ++ z) hvz_valid
  let w := eraseLag p u
  have hw : IsLagWord r active w := eraseLag_isLagWord hu
  have hwpmod : Nat.ModEq p (wordLag w) a.1 :=
    (wordLag_eraseLag_modEq p u).trans (humod.trans (by
      simpa only [wordLag, List.sum_append] using hzmod))
  have hqp : q ∣ p := by
    rw [← hq]
    exact Nat.setGcd_dvd_of_mem ⟨hp_active, hp_cost⟩
  have hwqmod : wordLag w % q = a.1 % q := hwpmod.of_dvd hqp
  have hwcost_le : wordCost δ w ≤ residueDefect r q active δ a.1 := by
    rw [wordCost_eraseLag_eq hp_cost]
    calc
      wordCost δ u ≤ wordCost δ (v ++ z) := hucost
      _ = wordCost δ v + wordCost δ z := by
        simp only [wordCost, List.map_append, List.sum_append]
      _ = residueDefect r q active δ a.1 := by rw [hvcost, hzcost, add_zero]
  have hwcost : wordCost δ w = residueDefect r q active δ a.1 :=
    le_antisymm hwcost_le (residueDefect_le_wordCost (δ := δ) hw hwqmod)
  exact ⟨w, hw, hwpmod, hwcost, (length_eraseLag_le p u).trans_lt hulength,
    not_mem_eraseLag p u⟩


/-- Coprime active lags and a chosen zero-cost lag produce sharp residue bridges. -/
def sharpDefectBridges_residueDefect_of_setGcd_eq_one
    {r p : ℕ} {active : Set ℕ} {δ : ℕ → ℕ}
    (hp : 0 < p) (hp_active : p ∈ active) (hp_le : p ≤ r)
    (hp_cost : δ p = 0) (hsetGcd : Nat.setGcd active = 1)
    (hpos : ∀ l ∈ active, 1 ≤ l) (hle : ∀ l ∈ active, l ≤ r) :
    SharpDefectBridges r p (Nat.setGcd (criticalLags active δ)) active δ
      (residueDefect r (Nat.setGcd (criticalLags active δ)) active δ) := by
  let q := Nat.setGcd (criticalLags active δ)
  have hp_critical : p ∈ criticalLags active δ := ⟨hp_active, hp_cost⟩
  have hq_dvd_p : q ∣ p := Nat.setGcd_dvd_of_mem hp_critical
  have hq_pos : 0 < q := by
    apply Nat.pos_of_ne_zero
    exact fun hq_zero ↦ hp.ne' (Set.mem_singleton_iff.mp
      (Nat.setGcd_eq_zero_iff.mp hq_zero hp_critical))
  have hbridge (a : Fin p) :=
    exists_bounded_residue_minimizer hp hq_pos hp_active hp_cost rfl
      hsetGcd hpos hle a
  let bridge : Fin p → List ℕ := fun a ↦ Classical.choose (hbridge a)
  have bridge_spec (a : Fin p) :
      IsLagWord r active (bridge a) ∧ Nat.ModEq p (wordLag (bridge a)) a.1 ∧
        wordCost δ (bridge a) = residueDefect r q active δ a.1 ∧
        (bridge a).length < p ∧ p ∉ bridge a := Classical.choose_spec (hbridge a)
  refine
    { p_pos := hp
      critical_active := hp_active
      critical_le := hp_le
      critical_cost := hp_cost
      q_dvd_p := hq_dvd_p
      bridge := bridge
      valid := fun a ↦ (bridge_spec a).1
      congruent := fun a ↦ (bridge_spec a).2.1
      realizes := ?_
      minimal := ?_
      sharp := ?_ }
  · intro a
    have hres : Nat.ModEq q (wordLag (bridge a)) a.1 :=
      (bridge_spec a).2.1.of_dvd hq_dvd_p
    rw [(bridge_spec a).2.2.1]
    exact residueDefect_eq_of_modEq
      (hres.symm.trans (Nat.mod_modEq (wordLag (bridge a)) q).symm)
  · intro w hw
    exact residueDefect_le_wordCost hw (by simp only [Nat.mod_mod])
  · intro a
    have hlength := (bridge_spec a).2.2.2.1
    have hnotmem := (bridge_spec a).2.2.2.2
    by_cases hpr : p < r
    · have hlag := wordLag_le_length_mul (bridge_spec a).1
      have hlength_le : (bridge a).length ≤ p - 1 := Nat.le_sub_one_of_lt hlength
      have hlength_mul := Nat.mul_le_mul_right r hlength_le
      nlinarith [Nat.sub_add_cancel hp, Nat.sub_add_cancel (n := r) (by lia : 1 ≤ r),
        Nat.sub_add_cancel (n := r) (by lia : 2 ≤ r)]
    · have hpr_eq : p = r := le_antisymm hp_le (Nat.le_of_not_gt hpr)
      have hvalid : IsLagWord (r - 1) active (bridge a) := by
        intro l hl
        have hl_data := (bridge_spec a).1 l hl
        refine ⟨hl_data.1, hl_data.2.1, ?_⟩
        have hl_ne : l ≠ r := by
          intro hlr
          apply hnotmem
          simpa only [hpr_eq] using hlr ▸ hl
        lia
      have hlag := wordLag_le_length_mul hvalid
      have hlength_le : (bridge a).length ≤ p - 1 := Nat.le_sub_one_of_lt hlength
      have hlength_mul := Nat.mul_le_mul_right (r - 1) hlength_le
      by_cases hr_one : r = 1
      · subst r
        subst p
        norm_num at hlag ⊢
        exact hlag
      · nlinarith [Nat.sub_add_cancel hp,
          Nat.sub_add_cancel (n := r) (by lia : 1 ≤ r),
          Nat.sub_add_cancel (n := r) (by lia : 2 ≤ r)]

/-! ## Scaled upper and lower word degrees -/

/-- Summing the defining upper defects over a lag word gives the scaled word-degree
identity. -/
theorem wordCost_add_scaledDegree_eq
    {A B : ℕ} {degree δ : ℕ → ℕ} {w : List ℕ}
    (hδ : ∀ l ∈ w, δ l + B * degree l = A * l) :
    wordCost δ w + B * (w.map degree).sum = A * wordLag w := by
  induction w with
  | nil => simp [wordCost, wordLag]
  | cons l w ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hδ
      have hi := ih hδ.2
      simp only [wordCost, wordLag] at hi
      simp only [wordCost, wordLag, List.map_cons, List.sum_cons]
      rw [Nat.mul_add]
      lia

/-- Summing the defining lower excesses over a lag word gives the scaled trailing-degree
identity. -/
theorem wordCost_add_scaledTrailingDegree_eq
    {C D : ℕ} {trailingDegree excess : ℕ → ℕ} {w : List ℕ}
    (hexcess : ∀ l ∈ w, excess l + C * l = D * trailingDegree l) :
    wordCost excess w + C * wordLag w = D * (w.map trailingDegree).sum := by
  induction w with
  | nil => simp [wordCost, wordLag]
  | cons l w ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hexcess
      have hi := ih hexcess.2
      simp only [wordCost, wordLag] at hi
      simp only [wordCost, wordLag, List.map_cons, List.sum_cons]
      rw [Nat.mul_add, Nat.mul_add]
      lia

/-- The upper bridge theorem in the subtraction-free scaled form
`B * degree + K = A * n`. -/
theorem SharpDefectBridges.exists_upper_degree_word
    {r p q A B : ℕ} {active : Set ℕ} {degree δ K : ℕ → ℕ}
    (h : SharpDefectBridges r p q active δ K)
    (hδ : ∀ l ∈ active, δ l + B * degree l = A * l) {n : ℕ}
    (hn : (r - 1) * (r - 2) ≤ n) :
    ∃ w, IsLagWord r active w ∧ wordLag w = n ∧
      B * (w.map degree).sum + K (n % q) = A * n := by
  obtain ⟨w, hw, hlag, hcost, _⟩ := h.exists_exact_minimizer hn
  refine ⟨w, hw, hlag, ?_⟩
  have hsum := wordCost_add_scaledDegree_eq
    (w := w) (fun l hl ↦ hδ l (hw l hl).1)
  rw [hcost, hlag] at hsum
  lia

/-- The lower bridge theorem in the scaled form
`D * trailingDegree = C * n + K`. -/
theorem SharpDefectBridges.exists_lower_degree_word
    {r p q C D : ℕ} {active : Set ℕ} {trailingDegree excess K : ℕ → ℕ}
    (h : SharpDefectBridges r p q active excess K)
    (hexcess : ∀ l ∈ active, excess l + C * l = D * trailingDegree l) {n : ℕ}
    (hn : (r - 1) * (r - 2) ≤ n) :
    ∃ w, IsLagWord r active w ∧ wordLag w = n ∧
      D * (w.map trailingDegree).sum = C * n + K (n % q) := by
  obtain ⟨w, hw, hlag, hcost, _⟩ := h.exists_exact_minimizer hn
  refine ⟨w, hw, hlag, ?_⟩
  have hsum := wordCost_add_scaledTrailingDegree_eq
    (w := w) (fun l hl ↦ hexcess l (hw l hl).1)
  rw [hcost, hlag] at hsum
  simpa only [add_comm] using hsum.symm

/-! ## The fractional `(2, 3)` example -/

/-- The active lags in the example `p₂ = ξ`, `p₃ = ξ²`. -/
def fractionalActiveLags : Set ℕ := {2, 3}

/-- The upper scaled defect in the fractional example: lag two costs one and lag three
is critical. -/
def fractionalUpperDefect (l : ℕ) : ℕ := if l = 2 then 1 else 0

/-- The upper residue defect `(K₀, K₁, K₂) = (0, 2, 1)` in the fractional example. -/
def fractionalUpperResidueDefect (n : ℕ) : ℕ :=
  if n % 3 = 0 then 0 else if n % 3 = 1 then 2 else 1

/-- Short minimum-cost bridges for the three residues in the fractional example. -/
def fractionalUpperBridge (a : Fin 3) : List ℕ :=
  if a.1 = 0 then [] else if a.1 = 1 then [2, 2] else [2]

/-- Every valid word in the fractional example has cost at least its residue defect. -/
theorem fractionalUpperResidueDefect_le_wordCost (w : List ℕ)
    (hw : IsLagWord 3 fractionalActiveLags w) :
    fractionalUpperResidueDefect (wordLag w % 3) ≤ wordCost fractionalUpperDefect w := by
  induction w with
  | nil => norm_num [fractionalUpperResidueDefect, wordLag, wordCost]
  | cons l w ih =>
      have hl := hw l (by simp)
      have htail : IsLagWord 3 fractionalActiveLags w := by
        intro x hx
        exact hw x (by simp [hx])
      have hi := ih htail
      simp only [fractionalActiveLags, Set.mem_insert_iff, Set.mem_singleton_iff] at hl
      rcases hl.1 with rfl | rfl
      · have hmod : w.sum % 3 < 3 := Nat.mod_lt _ (by norm_num)
        interval_cases hval : w.sum % 3 <;>
          norm_num [fractionalUpperResidueDefect, fractionalUpperDefect, wordLag,
            wordCost, Nat.add_mod, hval] at hi ⊢;
          lia
      · simpa [fractionalUpperResidueDefect, fractionalUpperDefect, wordLag,
          wordCost, Nat.add_mod, Nat.mod_mod] using hi

/-- The bridges `[]`, `[2,2]`, and `[2]` certify the sharp upper defect formula for
the fractional example. -/
def fractionalUpperBridges :
    SharpDefectBridges 3 3 3 fractionalActiveLags fractionalUpperDefect
      fractionalUpperResidueDefect := by
  refine
    { p_pos := by norm_num
      critical_active := by simp [fractionalActiveLags]
      critical_le := by norm_num
      critical_cost := by simp [fractionalUpperDefect]
      q_dvd_p := by norm_num
      bridge := fractionalUpperBridge
      valid := ?_
      congruent := ?_
      realizes := ?_
      minimal := fractionalUpperResidueDefect_le_wordCost
      sharp := ?_ }
  · intro a
    fin_cases a <;> simp [fractionalUpperBridge, IsLagWord, fractionalActiveLags]
  · intro a
    fin_cases a <;> norm_num [fractionalUpperBridge, wordLag, Nat.ModEq]
  · intro a
    fin_cases a <;>
      norm_num [fractionalUpperBridge, fractionalUpperResidueDefect,
        fractionalUpperDefect, wordLag, wordCost]
  · intro a
    fin_cases a <;> norm_num [fractionalUpperBridge, wordLag]

/-- In the fractional example, every `n ≥ 2` has a lag word whose scaled upper degree
satisfies `3 * degree + K_(n mod 3) = 2 * n`. -/
theorem exists_fractional_upper_degree_word {n : ℕ} (hn : 2 ≤ n) :
    ∃ w, IsLagWord 3 fractionalActiveLags w ∧ wordLag w = n ∧
      3 * (w.map fun l ↦ if l = 2 then 1 else 2).sum +
        fractionalUpperResidueDefect (n % 3) = 2 * n := by
  apply fractionalUpperBridges.exists_upper_degree_word
  · intro l hl
    simp only [fractionalActiveLags, Set.mem_insert_iff, Set.mem_singleton_iff] at hl
    rcases hl with rfl | rfl <;> norm_num [fractionalUpperDefect]
  · simpa only [Nat.reduceSub, Nat.reduceMul] using hn

end FiniteMemory

end RealRooted
