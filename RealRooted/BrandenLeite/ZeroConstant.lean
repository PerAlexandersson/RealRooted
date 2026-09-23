import RealRooted.AissenSchoenbergWhitney
import RealRooted.BrandenLeite.CompositionRowClosure
import RealRooted.BrandenLeite.Regularization
import RealRooted.PFPolynomial.Closure

/-!
# Zero-constant PF composition rows

This file proves the zero-constant specialization of Brändén--Saud Leite
Theorem 4.4. A PF sequence is split at its first nonzero entry, regularized by
the finite coefficient sequence of `(X + ε)^r`, and recovered as `ε` tends to
zero. The bounded composition-row limits preserve both the PF property and
zero-aware proper position.
-/

open Filter Polynomial Topology

noncomputable section

namespace RealRooted.BrandenLeite

@[simp]
theorem positivePartSeries_zero {R : Type*} [Semiring R] :
    positivePartSeries (0 : ℕ → R) = 0 := by
  ext n
  simp [coeff_positivePartSeries]

/-- Every positive-index composition row of the zero power series vanishes. -/
theorem compositionRow_zero_series_of_ne_zero
    {R : Type*} [CommSemiring R] {n : ℕ} (hn : n ≠ 0) :
    compositionRow (0 : PowerSeries R) n = 0 := by
  ext k
  rw [coeff_compositionRow (by simp) n k]
  cases k with
  | zero => simp [hn]
  | succ k => simp

/-- If a sequence has zero zeroth entry, deleting that entry from its formal
power series changes nothing. -/
theorem positivePartSeries_eq_mk_of_zero
    {R : Type*} [Semiring R] (f : ℕ → R) (hf0 : f 0 = 0) :
    positivePartSeries f = PowerSeries.mk f := by
  ext n
  rw [coeff_positivePartSeries, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst n
    simp [hf0]
  · simp [hn]

/-- Every nonzero PF sequence is a coefficientwise limit of PF sequences with
positive zeroth coefficient.  The construction removes the finite initial
zero block and regularizes it by the coefficients of `(X + ε)^r`. -/
theorem exists_pf_pos_zero_approximation
    {f : ℕ → ℝ} (hf : IsPolyaFreqSeq f) (hfn : f ≠ 0) :
    ∃ a : ℕ → ℕ → ℝ,
      (∀ k, IsPolyaFreqSeq (a k)) ∧
      (∀ k, 0 < a k 0) ∧
      ∀ n, Tendsto (fun k => a k n) atTop (𝓝 (f n)) := by
  have hexists : ∃ n, f n ≠ 0 := by
    by_contra h
    apply hfn
    funext n
    exact not_ne_iff.mp ((not_exists.mp h) n)
  let r : ℕ := Nat.find hexists
  let u : ℕ → ℝ := fun n => f (n + r)
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let a : ℕ → ℕ → ℝ := fun k => regularizedSequence r u (ε k)
  have hrne : f r ≠ 0 := Nat.find_spec hexists
  have hrpos : 0 < f r :=
    lt_of_le_of_ne (hf.nonneg r) (Ne.symm hrne)
  have hzero : ∀ k < r, f k = 0 := by
    intro k hk
    by_contra hk0
    exact (Nat.not_lt_of_ge (Nat.find_min' hexists hk0)) hk
  have hu_pf : IsPolyaFreqSeq u := hf.tail_of_zeros r hzero
  have hu0pos : 0 < u 0 := by
    simpa [u] using hrpos
  have hf_eq : f = fun n => if r ≤ n then u (n - r) else 0 := by
    funext n
    by_cases hrn : r ≤ n
    · rw [ite_eq_left hrn]
      simp [u, Nat.sub_add_cancel hrn]
    · rw [ite_eq_right hrn]
      exact hzero n (Nat.lt_of_not_ge hrn)
  have hεpos : ∀ k, 0 < ε k := by
    intro k
    dsimp [ε]
    positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ha_pf : ∀ k, IsPolyaFreqSeq (a k) := by
    intro k
    exact regularizedSequence_isPolyaFreqSeq hu_pf r (le_of_lt (hεpos k))
  have ha0pos : ∀ k, 0 < a k 0 := by
    intro k
    exact regularizedSequence_zero_pos (hεpos k) hu0pos
  have halim : ∀ n, Tendsto (fun k => a k n) atTop (𝓝 (f n)) := by
    intro n
    rw [hf_eq]
    simpa [a] using tendsto_regularizedSequence hεlim r u n
  exact ⟨a, ha_pf, ha0pos, halim⟩

/-- Every PF sequence, including the zero sequence, is a coefficientwise limit
of PF sequences with positive zeroth coefficient. -/
theorem exists_pf_pos_zero_approximation_of_pf
    {f : ℕ → ℝ} (hf : IsPolyaFreqSeq f) :
    ∃ a : ℕ → ℕ → ℝ,
      (∀ k, IsPolyaFreqSeq (a k)) ∧
      (∀ k, 0 < a k 0) ∧
      ∀ n, Tendsto (fun k => a k n) atTop (𝓝 (f n)) := by
  by_cases hfn : f = 0
  · subst f
    let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    let a : ℕ → ℕ → ℝ := fun k => (C (ε k) : ℝ[X]).coeff
    have hεpos : ∀ k, 0 < ε k := by
      intro k
      dsimp [ε]
      positivity
    have hεlim : Tendsto ε atTop (𝓝 0) := by
      simpa [ε] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    refine ⟨a, ?_, ?_, ?_⟩
    · intro k
      exact (IsPFPolynomial.of_C_nonneg (hεpos k).le).to_sequence
    · intro k
      simpa [a] using hεpos k
    · intro n
      cases n with
      | zero => simpa [a] using hεlim
      | succ n => simp [a]
  · exact exists_pf_pos_zero_approximation hf hfn

/-- Composition rows of the positive-order part of any PF sequence are PF,
and consecutive rows are in zero-aware proper position. -/
theorem compositionRows_positivePartSeries_pf_and_prec0
    {f : ℕ → ℝ} (hf : IsPolyaFreqSeq f) :
    (∀ n, IsPFPolynomial (compositionRow (positivePartSeries f) n)) ∧
      ∀ n, Interl (compositionRow (positivePartSeries f) n)
        (compositionRow (positivePartSeries f) (n + 1)) := by
  by_cases hfn : f = 0
  · subst f
    constructor
    · intro n
      by_cases hn : n = 0
      · subst n
        simpa using IsPFPolynomial.one
      · rw [positivePartSeries_zero,
          compositionRow_zero_series_of_ne_zero hn]
        exact IsPFPolynomial.zero
    · intro n
      rw [positivePartSeries_zero,
        compositionRow_zero_series_of_ne_zero (Nat.succ_ne_zero n)]
      exact interl_zero_right _
  · obtain ⟨a, ha_pf, ha0pos, halim⟩ :=
      exists_pf_pos_zero_approximation hf hfn
    constructor
    · intro n
      apply IsPFPolynomial.of_coeff_tendsto
        (fun k => compositionRow_positivePartSeries_isPFPolynomial
          (ha_pf k) (ha0pos k) n)
      exact tendsto_coeff_compositionRow_positivePartSeries halim n
    · intro n
      apply interl_of_pf_coeff_tendsto_of_natDegree_le
        (fun k => compositionRow_positivePartSeries_isPFPolynomial
          (ha_pf k) (ha0pos k) n)
        (fun k => compositionRow_positivePartSeries_isPFPolynomial
          (ha_pf k) (ha0pos k) (n + 1))
        (fun k => prec0_compositionRow_positivePartSeries_succ
          (ha_pf k) (ha0pos k) n)
        (fun k => (natDegree_compositionRow_le _ n).trans (Nat.le_succ n))
        (fun k => natDegree_compositionRow_le _ (n + 1))
        (tendsto_coeff_compositionRow_positivePartSeries halim n)
        (tendsto_coeff_compositionRow_positivePartSeries halim (n + 1))

/-- Zero-constant specialization of Brändén--Saud Leite Theorem 4.4 for the
literal power series generated by a PF sequence. -/
theorem compositionRows_mk_pf_and_prec0_of_zero
    {f : ℕ → ℝ} (hf : IsPolyaFreqSeq f) (hf0 : f 0 = 0) :
    (∀ n, IsPFPolynomial (compositionRow (PowerSeries.mk f) n)) ∧
      ∀ n, Interl (compositionRow (PowerSeries.mk f) n)
        (compositionRow (PowerSeries.mk f) (n + 1)) := by
  rw [← positivePartSeries_eq_mk_of_zero f hf0]
  exact compositionRows_positivePartSeries_pf_and_prec0 hf

/-- Every composition row of a zero-constant PF sequence is a PF polynomial. -/
theorem compositionRow_mk_isPFPolynomial_of_zero
    {f : ℕ → ℝ} (hf : IsPolyaFreqSeq f) (hf0 : f 0 = 0) (n : ℕ) :
    IsPFPolynomial (compositionRow (PowerSeries.mk f) n) :=
  (compositionRows_mk_pf_and_prec0_of_zero hf hf0).1 n

/-- Consecutive composition rows of a zero-constant PF sequence are in
zero-aware proper position. -/
theorem prec0_compositionRow_mk_succ_of_zero
    {f : ℕ → ℝ} (hf : IsPolyaFreqSeq f) (hf0 : f 0 = 0) (n : ℕ) :
    Interl (compositionRow (PowerSeries.mk f) n)
      (compositionRow (PowerSeries.mk f) (n + 1)) :=
  (compositionRows_mk_pf_and_prec0_of_zero hf hf0).2 n

end RealRooted.BrandenLeite
