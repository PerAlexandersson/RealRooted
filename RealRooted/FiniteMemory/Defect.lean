import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Data.Nat.ModEq
import RealRooted.Basic.Coefficients

/-!
# Degree defects for positive finite-memory symbols

This file develops the finite algebraic part of the positive finite-memory symbol
construction.  It records the two no-cancellation lemmas needed for highest and lowest
polynomial degree, defines the symbol generating series, and extracts its fundamental
recurrence.
-/

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
  rw [map_sub, PowerSeries.coeff_mul] at hcoeff
  have hone : PowerSeries.coeff n (1 : PowerSeries ℝ[X]) = 0 := by
    rw [PowerSeries.coeff_one, ite_eq_right hn]
  rw [hone] at hcoeff
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
  split
  · exact hp i
  · exact hasNonnegCoeffs_zero

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
  bridge : Fin p → List ℕ
  valid : ∀ a, IsLagWord r active (bridge a)
  congruent : ∀ a, Nat.ModEq p (wordLag (bridge a)) a.1
  realizes : ∀ a, wordCost δ (bridge a) = K (wordLag (bridge a) % q)
  minimal : ∀ w, IsLagWord r active w → K (wordLag w % q) ≤ wordCost δ w
  sharp : ∀ a, wordLag (bridge a) - p + 1 ≤ (r - 1) * (r - 2)

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
  have hb_mod_q : wordLag b % q = n % q := by
    exact hb_mod.of_dvd h.q_dvd_p
  have hw_cost : wordCost δ w = K (n % q) := by
    simp only [w, wordCost, List.map_append, List.sum_append, List.map_replicate,
      List.sum_replicate, h.critical_cost, nsmul_zero, add_zero]
    change wordCost δ b = K (n % q)
    rw [h.realizes a, hb_mod_q]
  refine ⟨w, hw_valid, hw_lag, hw_cost, ?_⟩
  intro v hv hv_lag
  simpa only [hv_lag] using h.minimal v hv

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
      have hl := hδ l (by simp)
      have htail : ∀ x ∈ w, δ x + B * degree x = A * x := by
        intro x hx
        exact hδ x (by simp [hx])
      have hi := ih htail
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
      have hl := hexcess l (by simp)
      have htail : ∀ x ∈ w, excess x + C * x = D * trailingDegree x := by
        intro x hx
        exact hexcess x (by simp [hx])
      have hi := ih htail
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
