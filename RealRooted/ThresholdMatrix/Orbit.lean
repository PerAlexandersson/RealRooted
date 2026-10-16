module

public import RealRooted.ThresholdMatrix.HaglundZhang
public import RealRooted.ThresholdMatrix.GustafssonSolus

/-!
# Orbits of threshold matrices

For a Haglund–Zhang threshold matrix `G = HaglundZhang.matrix q rows` with `RowData rows`
(markers `1` or `1 + X`), or a Gustafsson–Solus one (markers `0` or `1`), the orbit
`S n = G^n S₀` of an interlacing input stays an interlacing sequence of real-rooted
polynomials, so every orbit sum is real-rooted.  Sequences defined by a scalar recurrence
whose rows are such orbit sums (for instance OEIS A120987, A330509 and A304429) are real-rooted.
-/

@[expose] public section

open Polynomial

/-- Unfolding lemmas for explicit threshold-matrix orbits, used by the `rr_row_splits`
threshold-orbit route. -/
register_simp_attr rr_threshold_unfold

namespace RealRooted.HaglundZhang

/-- The orbit `S n = G^n S₀` of the threshold matrix `matrix q rows` on the input `S₀`. -/
noncomputable def orbit (q : ℕ) (rows : List (ℕ × ℝ[X])) (S₀ : List ℝ[X]) : ℕ → List ℝ[X]
  | 0 => S₀
  | n + 1 => matPolyAction (matrix q rows) (orbit q rows S₀ n)

@[simp] theorem orbit_zero (q : ℕ) (rows : List (ℕ × ℝ[X])) (S₀ : List ℝ[X]) :
    orbit q rows S₀ 0 = S₀ := rfl

theorem orbit_succ (q : ℕ) (rows : List (ℕ × ℝ[X])) (S₀ : List ℝ[X]) (n : ℕ) :
    orbit q rows S₀ (n + 1) = matPolyAction (matrix q rows) (orbit q rows S₀ n) := rfl

/-- Every orbit of a square threshold matrix on an interlacing input of real-rooted
polynomials consists of interlacing real-rooted polynomials. -/
theorem orbit_certificate {q : ℕ} {rows : List (ℕ × ℝ[X])} (hrows : RowData rows)
    (hq : rows.length = q) {S₀ : List ℝ[X]} (hlen : S₀.length = q)
    (h0 : IsInterlacingSeq0Nonneg S₀) (h0r : ∀ f ∈ S₀, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    ∀ n, (orbit q rows S₀ n).length = q ∧ IsInterlacingSeq0Nonneg (orbit q rows S₀ n) ∧
      ∀ f ∈ orbit q rows S₀ n, f ≠ 0 → (f ≠ 0 ∧ f.Splits)
  | 0 => ⟨hlen, h0, h0r⟩
  | n + 1 => by
    obtain ⟨hl, hi, hr⟩ := orbit_certificate hrows hq hlen h0 h0r n
    have h := isInterlacingSeq0Nonneg_matPolyAction_and_realRooted rows hrows _ hl hi hr
    refine ⟨?_, h⟩
    simp [orbit_succ, matrix, hq]

/-- A nonzero orbit sum of a square threshold matrix is real-rooted. -/
theorem splits_orbit_sum {q : ℕ} {rows : List (ℕ × ℝ[X])} (hrows : RowData rows)
    (hq : rows.length = q) {S₀ : List ℝ[X]} (hlen : S₀.length = q)
    (h0 : IsInterlacingSeq0Nonneg S₀) (h0r : ∀ f ∈ S₀, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) (n : ℕ)
    (hne : (orbit q rows S₀ n).sum ≠ 0) : (orbit q rows S₀ n).sum.Splits := by
  obtain ⟨-, hi, hr⟩ := orbit_certificate hrows hq hlen h0 h0r n
  exact (isRealRooted_sum_of_isInterlacingSeq0Nonneg hi hr hne).2

end RealRooted.HaglundZhang

namespace RealRooted.GustafssonSolus

/-- The orbit `S n = G^n S₀` of the threshold matrix `thresholdMatrix q rows` on the input `S₀`. -/
noncomputable def orbit (q : ℕ) (rows : List (ℕ × ℝ[X])) (S₀ : List ℝ[X]) : ℕ → List ℝ[X]
  | 0 => S₀
  | n + 1 => matPolyAction (thresholdMatrix q rows) (orbit q rows S₀ n)

@[simp] theorem orbit_zero (q : ℕ) (rows : List (ℕ × ℝ[X])) (S₀ : List ℝ[X]) :
    orbit q rows S₀ 0 = S₀ := rfl

theorem orbit_succ (q : ℕ) (rows : List (ℕ × ℝ[X])) (S₀ : List ℝ[X]) (n : ℕ) :
    orbit q rows S₀ (n + 1) = matPolyAction (thresholdMatrix q rows) (orbit q rows S₀ n) := rfl

/-- Every orbit of a square threshold matrix on an interlacing input of real-rooted
polynomials consists of interlacing real-rooted polynomials. -/
theorem orbit_certificate {q : ℕ} {rows : List (ℕ × ℝ[X])} (hrows : RowData rows)
    (hq : rows.length = q) {S₀ : List ℝ[X]} (hlen : S₀.length = q)
    (h0 : IsInterlacingSeq0Nonneg S₀) (h0r : ∀ f ∈ S₀, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    ∀ n, (orbit q rows S₀ n).length = q ∧ IsInterlacingSeq0Nonneg (orbit q rows S₀ n) ∧
      ∀ f ∈ orbit q rows S₀ n, f ≠ 0 → (f ≠ 0 ∧ f.Splits)
  | 0 => ⟨hlen, h0, h0r⟩
  | n + 1 => by
    obtain ⟨hl, hi, hr⟩ := orbit_certificate hrows hq hlen h0 h0r n
    have h := isInterlacingSeq0Nonneg_matPolyAction_and_realRooted rows hrows _ hl hi hr
    refine ⟨?_, h⟩
    simp [orbit_succ, hq]

/-- A nonzero orbit sum of a square threshold matrix is real-rooted. -/
theorem splits_orbit_sum {q : ℕ} {rows : List (ℕ × ℝ[X])} (hrows : RowData rows)
    (hq : rows.length = q) {S₀ : List ℝ[X]} (hlen : S₀.length = q)
    (h0 : IsInterlacingSeq0Nonneg S₀) (h0r : ∀ f ∈ S₀, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) (n : ℕ)
    (hne : (orbit q rows S₀ n).sum ≠ 0) : (orbit q rows S₀ n).sum.Splits := by
  obtain ⟨-, hi, hr⟩ := orbit_certificate hrows hq hlen h0 h0r n
  exact (isRealRooted_sum_of_isInterlacingSeq0Nonneg hi hr hne).2

end RealRooted.GustafssonSolus
