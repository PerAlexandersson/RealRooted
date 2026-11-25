module

public import RealRooted.ExponentialRows.ProductInsertion
public import RealRooted.SimpleRoots
import RealRooted.ExponentialRows.Clustering
import RealRooted.ExponentialRows.HalfPlaneTransport
import RealRooted.ExponentialRows.QuarticGaussian
import RealRooted.ExponentialRows.QuarticInsertion
import RealRooted.ExponentialRows.QuarticRecurrence
import RealRooted.ExponentialRows.QuarticCoefficients
import RealRooted.ExponentialRows.QuarticWindow
import RealRooted.ExponentialRows.ProductStrict
import Mathlib.Tactic

/-!
# Strict interlacing for the completed-square quartic rows

We transport the oriented order from the real-factor endpoint by applying
half-plane transport to the Hermite–Biehler polynomial of two consecutive rows.
Its real-axis nonvanishing is exactly the disjointness obtained by Gaussian evaluation.

Source: the unpublished manuscript, RealRooted #2649 and #2415 (round two),
https://github.com/PerAlexandersson/RealRooted/issues/2649.
-/

public section

open Polynomial Set

namespace RealRooted.ExponentialRows

private noncomputable abbrev row (a b c : ℝ) := insertionRow (markedBlockWeights
  (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4))

/-- The sparse insertion recurrence gives continuity in the fourth block coefficient. -/
private theorem continuous_coeff_row (a b : ℝ) (n k : ℕ) :
    Continuous fun c => (row a b c n).coeff k := by
  induction n using Nat.strong_induction_on generalizing k with
  | ind n ih =>
    rcases n with _ | _ | _ | _ | n
    · show Continuous fun c : ℝ => (row a b c 0).coeff k
      simp only [row, insertionRow_zero]
      exact continuous_const
    · change Continuous fun c : ℝ => (row a b c 1).coeff k
      have h (c : ℝ) : row a b c 1 = 1 := by simp [row, insertionRow_succ]
      simp only [h]
      exact continuous_const
    · change Continuous fun c : ℝ => (row a b c 2).coeff k
      simp only [row, insertionRow_quartic_two]
      exact continuous_const
    · change Continuous fun c : ℝ => (row a b c 3).coeff k
      simp only [row, insertionRow_quartic_three]
      exact continuous_const
    · have h3 := ih (n + 3) (by lia)
      have h2 := ih (n + 2) (by lia)
      have h1 := ih (n + 1) (by lia)
      have h0 := ih n (by lia)
      simp only [row] at h3 h2 h1 h0 ⊢
      simp only [insertionRow_quartic_add_four, coeff_add, mul_assoc, coeff_C_mul]
      cases k with
      | zero =>
        simp only [coeff_X_mul_zero, mul_zero, add_zero]
        exact h3 0
      | succ k =>
        simp only [coeff_X_mul]
        have := h3 (k + 1)
        have := h2 k
        have := h1 k
        have := h0 k
        fun_prop

/-- The real-factor endpoint orients the entire discriminant-complement interval. -/
private theorem strictInterl_quartic_interval {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hdisc : b ^ 2 ≤ 4 * a * c) (n : ℕ) (hd : (n + 1) / 2 ≠ 0) :
    StrictInterl (row a b c n) (row a b c (n + 1)) := by
  let l := b ^ 2 / (4 * a)
  have hl : 0 < l := div_pos (sq_pos_of_pos hb) (by positivity)
  have hlc : l ≤ c := (div_le_iff₀ (by positivity : 0 < 4 * a)).mpr (by linarith)
  let B := Icc l c
  let left : B := ⟨l, le_rfl, hlc⟩
  let right : B := ⟨c, hlc, le_rfl⟩
  have : PreconnectedSpace B := Subtype.preconnectedSpace isPreconnected_Icc
  have hpos (x : B) (j : ℕ) : HasPosLeadingCoeff (row a b x j) := by
    apply (hasNonnegCoeffs_insertionRow_quartic ha.le hb.le (hl.le.trans x.2.1) j).pos_leadingCoeff
    intro he
    have hh := insertionRow_quartic_coeff_zero a b x j
    rw [he, coeff_zero] at hh
    exact zero_ne_one hh
  have hc' (j i : ℕ) : Continuous fun x : B => (row a b x j).coeff i :=
    (continuous_coeff_row a b j i).comp continuous_subtype_val
  apply strictInterl_of_no_common_root_family (f := fun x : B => row a b x (n + 1))
    (g := fun x : B => row a b x n) hd (hc' _) (hc' _) (fun x => hpos x _)
    (fun x => hpos x _) (fun x => natDegree_insertionRow_quartic ha hb.le (hl.le.trans x.2.1) _)
    _ _ (x₀ := left) _ right
  · intro x
    rw [show (row a b x n).natDegree = n / 2 from
      natDegree_insertionRow_quartic ha hb.le (hl.le.trans x.2.1) _]
    lia
  · intro x
    apply insertionRow_no_common_root_quartic hb (hl.trans_le x.2.1)
    have hx := (div_le_iff₀ (by positivity : 0 < 4 * a)).mp x.2.1
    linarith
  · apply insertionRow_strictInterl_quartic_succ ha.le hb.le hl
    apply le_of_eq
    dsimp [l]
    field_simp

/-- Positive quartic rows with nonpositive quadratic discriminant alternate in the
oriented order, and consecutive rows have disjoint real roots. -/
theorem insertionRow_strictInterl_quartic_of_disc_le {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hdisc : b ^ 2 ≤ 4 * a * c) (n : ℕ) :
    let w := markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)
    StrictInterl (insertionRow w n) (insertionRow w (n + 1)) ∧
      ∀ t, ¬ ((insertionRow w n).IsRoot t ∧ (insertionRow w (n + 1)).IsRoot t) := by
  refine ⟨?_, insertionRow_no_common_root_quartic hb hc hdisc n⟩
  cases n with
  | zero =>
    simpa [insertionRow_succ] using
      (insertionRow_strictInterl_cubic ha hb.le 0).1
  | succ n => exact strictInterl_quartic_interval ha hb hdisc _ (by lia)

/-- The quartic rows have exactly the indicated degree, simple negative roots,
and genuine distance-two alternation. -/
theorem insertionRow_quartic_simple_roots_of_disc_le {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hdisc : b ^ 2 ≤ 4 * a * c) (n : ℕ) :
    let w := markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)
    IsSimpleRealRooted (insertionRow w n) ∧ (insertionRow w n).natDegree = n / 2 ∧
      (∀ r ∈ (insertionRow w n).roots, r < 0) ∧
      StrictInterl (insertionRow w n) (insertionRow w (n + 2)) ∧
      ∀ t, ¬ ((insertionRow w n).IsRoot t ∧ (insertionRow w (n + 2)).IsRoot t) := by
  have adj := insertionRow_strictInterl_quartic_of_disc_le ha hb hc hdisc
  exact ⟨⟨(adj n).1.1.1, (adj n).1.1.2, ((adj n).1.hasSimpleRoots_of_no_common_root (adj n).2).1⟩,
    natDegree_insertionRow_quartic ha hb.le hc.le n,
    roots_insertionRow_quartic_neg ha.le hb.le hc.le n,
    insertionRow_strictInterl_quartic_add_two_of_succ ha hb.le hc.le adj n⟩

/-- The complete-graph cap-three recurrence has simple negative roots and genuine
oriented interlacing at both distances one and two. -/
theorem insertionRow_cap_three_strictInterl (n : ℕ) :
    let w := markedBlockWeights
      (C (1 / 2 : ℝ) * X ^ 2 + C (2 / 3 : ℝ) * X ^ 3 + C (2 / 3 : ℝ) * X ^ 4)
    IsSimpleRealRooted (insertionRow w n) ∧ (insertionRow w n).natDegree = n / 2 ∧
      (∀ r ∈ (insertionRow w n).roots, r < 0) ∧
      ∀ k ∈ ({1, 2} : Finset ℕ), StrictInterl (insertionRow w n) (insertionRow w (n + k)) ∧
        ∀ t, ¬ ((insertionRow w n).IsRoot t ∧ (insertionRow w (n + k)).IsRoot t) := by
  have hs := insertionRow_quartic_simple_roots_of_disc_le (a := 1 / 2) (b := 2 / 3)
    (c := 2 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) n
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_⟩
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact insertionRow_strictInterl_quartic_of_disc_le (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) n
  · exact hs.2.2.2

/-- The support-weight insertion recurrence alone gives cap-three strictness for a
clustering polynomial sequence. A finite graph model supplies this recurrence. -/
theorem clusteringRow_cap_three_strictInterl {R : ℕ → ℝ[X]} (hzero : R 0 = 1)
    (hsucc : ∀ n, R (n + 1) = ∑ k ∈ Finset.range (n + 1), C (n.choose k : ℝ) *
      (if k + 1 = 1 then 1 else if k + 1 = 2 then C (1 : ℝ) * X
        else if k + 1 = 3 then C (4 : ℝ) * X else if k + 1 = 4 then C (16 : ℝ) * X
        else 0) * R (n - k)) (n : ℕ) :
    IsSimpleRealRooted (R n) ∧ (R n).natDegree = n / 2 ∧ (∀ r ∈ (R n).roots, r < 0) ∧
      ∀ k ∈ ({1, 2} : Finset ℕ), StrictInterl (R n) (R (n + k)) ∧
        ∀ t, ¬ ((R n).IsRoot t ∧ (R (n + k)).IsRoot t) := by
  have he := clusteringRow_eq_insertionRow 1 4 16 hzero hsucc
  norm_num at he
  simpa only [he] using insertionRow_cap_three_strictInterl n

end RealRooted.ExponentialRows
