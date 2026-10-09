import RealRooted.EulerBidiagonal.PairTheorem

/-!
# Rows of the general Euler recurrence

`generalRows κ a b u v n` is `P n` for `P 0 = 1`, `P (n + 1) = generalStep κ a b u v (P n)`.
If `κ, a, b > 0`, `u + v k > 0` for all `k`, and the comparison defect is negative on `(-∞, 0]`
(for instance `2 u ≥ (a + b + 1) v`), then every row is negative-simple of degree `n` and
consecutive rows strictly interlace without common roots.  This covers A156289
(`κ = a = b = 1`, `u = 3`, `v = 2`).
-/

open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

/-- The rows `P 0 = 1`, `P (n + 1) = generalStep κ a b u v (P n)`. -/
def generalRows (κ a b u v : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => generalStep κ a b u v (generalRows κ a b u v n)

/-- `1 ≪ p` strictly for a polynomial `p` that splits and has degree one. -/
theorem strictInterl_one_of_natDegree_eq_one {p : ℝ[X]} (hp : p ≠ 0) (hps : p.Splits)
    (hdeg : p.natDegree = 1) : StrictInterl (1 : ℝ[X]) p := by
  have hcard : Multiset.card p.roots = 1 := by
    rw [card_roots_of_splits hps, hdeg]
  obtain ⟨r, hr⟩ := Multiset.card_eq_one.mp hcard
  refine ⟨⟨one_ne_zero, Splits.one⟩, ⟨hp, hps⟩, [], [r], by simp, by simp, ?_, ?_, ?_⟩
  · simp
  · rw [hr]
    simp
  · exact Or.inl ⟨by simp, by simp [ListInterlaces]⟩

/-- Every row is negative-simple of degree `n`, and consecutive rows strictly interlace with no
common root. -/
theorem generalRows_spec (κ a b u v : ℝ) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hell : ∀ k : ℕ, 0 < u + v * k) (hQ : ∀ t ≤ 0, comparisonDefect κ a b u v t < 0) :
    ∀ n : ℕ, IsNegativeSimple (generalRows κ a b u v n) ∧
      (generalRows κ a b u v n).natDegree = n ∧
      StrictInterl (generalRows κ a b u v n) (generalRows κ a b u v (n + 1)) ∧
      ∀ r, ¬ ((generalRows κ a b u v n).IsRoot r ∧ (generalRows κ a b u v (n + 1)).IsRoot r) := by
  have hone : IsNegativeSimple (1 : ℝ[X]) := by
    refine ⟨by norm_num, Splits.one, ?_, hasPosLeadingCoeff_one, ?_⟩
    · exact fun r hr => absurd hr (by simp)
    · intro r hr
      exact absurd hr (by simp)
  have hnext : ∀ n : ℕ, IsNegativeSimple (generalRows κ a b u v n) →
      (generalRows κ a b u v n).natDegree = n →
      IsNegativeSimple (generalRows κ a b u v (n + 1)) ∧
        (generalRows κ a b u v (n + 1)).natDegree = n + 1 := by
    intro n h1 h2
    exact isNegativeSimple_generalStep_of_natDegree κ a b u v _ n h1 h2 hκ ha hb
      (fun k _ => hell k) hQ
  intro n
  induction n with
  | zero =>
      have h1 := hnext 0 hone (by simp [generalRows])
      refine ⟨by simpa [generalRows] using hone, by simp [generalRows], ?_, ?_⟩
      · exact strictInterl_one_of_natDegree_eq_one h1.1.1 h1.1.2.1 h1.2
      · intro r hr
        have hzero : (1 : ℝ[X]).eval r = 0 := by
          simpa [generalRows, Polynomial.IsRoot.def] using hr.1
        norm_num at hzero
  | succ n ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      obtain ⟨h5, h6⟩ := hnext n h1 h2
      have hstep := strictInterl_generalStep_of_strictInterl κ a b u v _ _ n h1 h5 h2 h6 h3
        (fun s hs hs' => h4 s ⟨hs, hs'⟩) hκ ha hb (fun k _ => hell k) hQ
      refine ⟨h5, h6, hstep.1, ?_⟩
      intro r hr
      exact hstep.2 r hr.1 hr.2

/-- Consecutive rows strictly interlace and have no common root. -/
theorem strictInterl_generalRows (κ a b u v : ℝ) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hell : ∀ k : ℕ, 0 < u + v * k) (hQ : ∀ t ≤ 0, comparisonDefect κ a b u v t < 0) (n : ℕ) :
    StrictInterl (generalRows κ a b u v n) (generalRows κ a b u v (n + 1)) ∧
      ∀ r, ¬ ((generalRows κ a b u v n).IsRoot r ∧ (generalRows κ a b u v (n + 1)).IsRoot r) :=
  ⟨(generalRows_spec κ a b u v hκ ha hb hell hQ n).2.2.1,
    (generalRows_spec κ a b u v hκ ha hb hell hQ n).2.2.2⟩

/-- Every row is negative-simple of degree `n`. -/
theorem isNegativeSimple_generalRows (κ a b u v : ℝ) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hell : ∀ k : ℕ, 0 < u + v * k) (hQ : ∀ t ≤ 0, comparisonDefect κ a b u v t < 0) (n : ℕ) :
    IsNegativeSimple (generalRows κ a b u v n) ∧ (generalRows κ a b u v n).natDegree = n :=
  ⟨(generalRows_spec κ a b u v hκ ha hb hell hQ n).1,
    (generalRows_spec κ a b u v hκ ha hb hell hQ n).2.1⟩

end RealRooted.EulerBidiagonal
