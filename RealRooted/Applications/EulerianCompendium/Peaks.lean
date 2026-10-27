module

public import RealRooted.Applications.EulerianCompendium.Definitions
import RealRooted.CombinatorialExamples.PeakValues.Canonical
import RealRooted.CombinatorialExamples.PeakValues.Sharpness
public import RealRooted.Mathlib.Combinatorics.Enumerative.EulerianPeak
import RealRooted.Mathlib.Algebra.Polynomial.Derivative

/-!
# Peak counts in the Eulerian compendium

The all-one diagonal of the peak-value polynomial is identified here with
the actual interior-peak statistic on permutations. This also supplies the
exact degree and strict negativity assertions in `thm:permutationPeaks`.
-/

public section

open Polynomial RealRooted
open scoped BigOperators

noncomputable section

namespace RealRooted.EulerianCompendium

/-- The weighted diagonal at unit weights counts actual interior peaks. -/
theorem peakPolynomial_eq_sum_peakCount (n : ℕ) :
    peakPolynomial n =
      ∑ π : Equiv.Perm (Fin n), X ^ π.peakCount := by
  classical
  unfold peakPolynomial
  change commonPhaseRestriction (fun _ : Fin n => 1)
    (RealRooted.peakValuePolynomial n) = _
  simp [commonPhaseRestriction, RealRooted.peakValuePolynomial,
    RealRooted.peakValueMonomial, Finset.prod_const,
    RealRooted.peakValues_card_eq_peakCount]

/-- The coefficients are the canonical peak numbers of permutations. -/
theorem peakPolynomial_coeff (n k : ℕ) :
    (peakPolynomial n).coeff k = (Equiv.Perm.peakNumber n k : ℝ) := by
  classical
  have hfilter :
      (Finset.univ.filter fun π : Equiv.Perm (Fin n) => k = π.peakCount) =
        Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π.peakCount = k) := by
    ext π
    simp [eq_comm]
  rw [peakPolynomial_eq_sum_peakCount]
  simp [Equiv.Perm.peakNumber, finsetSum_coeff, coeff_X_pow, hfilter]

/-- The degree of the peak enumerator is exactly the largest possible number
of interior peaks; this is the degree assertion in `thm:permutationPeaks`. -/
theorem peakPolynomial_natDegree (n : ℕ) :
    (peakPolynomial n).natDegree = (n - 1) / 2 := by
  classical
  let d := (n - 1) / 2
  have hzero : ∀ k, d < k → (peakPolynomial n).coeff k = 0 := by
    intro k hk
    rw [peakPolynomial_coeff]
    have hempty :
        (Finset.univ.filter fun π : Equiv.Perm (Fin n) => π.peakCount = k) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro π hπ
      have hcard := RealRooted.card_peakValues_le π
      have hcount := RealRooted.peakValues_card_eq_peakCount π
      rw [Finset.mem_filter] at hπ
      have hbound : π.peakCount ≤ d := by
        rw [← hcount]
        exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
          (by simpa [Nat.mul_comm] using hcard)
      exact (not_lt_of_ge hbound) (hπ.2 ▸ hk)
    simp [Equiv.Perm.peakNumber, hempty]
  have htop : 0 < (peakPolynomial n).coeff d := by
    rw [peakPolynomial_coeff]
    obtain ⟨π, hπ⟩ := RealRooted.exists_card_peakValues_eq n
    have hmem : π ∈
        Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.peakCount = d) := by
      simp [← RealRooted.peakValues_card_eq_peakCount, hπ, d]
    have hc : 0 < Equiv.Perm.peakNumber n d := by
      rw [Equiv.Perm.peakNumber]
      exact Finset.card_pos.mpr ⟨π, hmem⟩
    exact_mod_cast hc
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr hzero) htop.ne'

/-- Every coefficient of the actual peak enumerator is nonnegative. -/
theorem peakPolynomial_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (peakPolynomial n) := by
  intro k
  rw [peakPolynomial_coeff]
  positivity

/-- Every nonempty permutation rank has positive constant coefficient. -/
theorem peakPolynomial_coeff_zero_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < (peakPolynomial n).coeff 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  rw [peakPolynomial_coeff, Equiv.Perm.peakNumber_succ_zero]
  positivity

/-- The zeros of the actual peak enumerator are strictly negative; this is
the root-sign assertion in `thm:permutationPeaks`. -/
theorem peakPolynomial_roots_neg (n : ℕ) (hn : 1 ≤ n) :
    ∀ r ∈ (peakPolynomial n).roots, r < 0 := by
  intro r hr
  have hle : r ≤ 0 :=
    roots_nonpos_of_hasNonnegCoeffs (peakPolynomial_hasNonnegCoeffs n) r hr
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · subst r
    have hpos := peakPolynomial_coeff_zero_pos n hn
    have hne : peakPolynomial n ≠ 0 := by
      intro hz
      rw [hz] at hpos
      simp at hpos
    have hroot : (peakPolynomial n).IsRoot 0 := (mem_roots hne).mp hr
    rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero] at hroot
    linarith

private theorem peakNumber_eq_zero_of_gt (n k : ℕ)
    (hk : (n - 1) / 2 < k) : Equiv.Perm.peakNumber n k = 0 := by
  have hcoeff : (peakPolynomial n).coeff k = 0 := by
    exact coeff_eq_zero_of_natDegree_lt
      (by rw [peakPolynomial_natDegree]; exact hk)
  rw [peakPolynomial_coeff] at hcoeff
  exact_mod_cast hcoeff

/-- The Warren--Seneta differential recurrence, connected to the actual
permutation peak enumerator by the canonical insertion count. Paper
`eq:peakRecurrence`. -/
theorem peakPolynomial_succ (n : ℕ) (hn : 1 ≤ n) :
    peakPolynomial (n + 1) =
      (C 2 * X + C (-2) * X ^ 2) * (peakPolynomial n).derivative +
        (C 2 + C ((n - 1 : ℕ) : ℝ) * X) * peakPolynomial n := by
  classical
  apply Polynomial.ext
  intro k
  cases k with
  | zero =>
      have hcount : Equiv.Perm.peakNumber (n + 1) 0 =
          2 * Equiv.Perm.peakNumber n 0 := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
        rw [Equiv.Perm.peakNumber_succ_zero,
          Equiv.Perm.peakNumber_succ_zero, pow_succ]
        ring
      rw [peakPolynomial_coeff, hcount]
      simp [coeff_add, peakPolynomial_coeff]
  | succ k =>
      rw [peakPolynomial_coeff]
      have hcoeff := Polynomial.coeff_quadratic_derivative_add_linear_mul_succ
        (peakPolynomial n) (2 : ℝ) (-2) 2 (((n - 1 : ℕ) : ℝ)) k
      simp only [coeff_add] at hcoeff ⊢
      rw [hcoeff]
      simp only [peakPolynomial_coeff]
      rw [Equiv.Perm.peakNumber_succ_succ]
      by_cases hk : 2 * k ≤ n - 1
      · have hcast : ((n - 1 - 2 * k : ℕ) : ℝ) =
            ((n - 1 : ℕ) : ℝ) - 2 * (k : ℝ) := by
          rw [Nat.cast_sub hk]
          push_cast
          ring
        push_cast
        rw [hcast]
        ring
      · have hzero : Equiv.Perm.peakNumber n k = 0 :=
          peakNumber_eq_zero_of_gt n k (by
            apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
            lia)
        rw [hzero]
        simp only [mul_zero, add_zero, Nat.cast_mul, Nat.cast_add,
          Nat.cast_ofNat, neg_mul, CharP.cast_eq_zero, mul_eq_mul_right_iff,
          Nat.cast_eq_zero]
        left
        ring

/-- Consecutive actual peak enumerators have the weak interlacing relation
provided by stability of the peak-value refinement. -/
theorem peakPolynomial_weakInterl (n : ℕ) (hn : 1 ≤ n) :
    StrictInterl (peakPolynomial n) (peakPolynomial (n + 1)) := by
  simpa [peakPolynomial] using
    RealRooted.peakValueWeightedDiagonal_consecutive_strictInterl n hn
      (fun _ : Fin (n + 1) => 1) (by intro j; norm_num)

private theorem peakPolynomial_noCommonRoot_of_simple (n : ℕ) (hn : 1 ≤ n)
    (hsimple : HasSimpleRoots (peakPolynomial n)) :
    ∀ r : ℝ, ¬ ((peakPolynomial n).IsRoot r ∧
      (peakPolynomial (n + 1)).IsRoot r) := by
  intro r hroot
  obtain ⟨hr, hnext⟩ := hroot
  have hrmem : r ∈ (peakPolynomial n).roots :=
    (mem_roots hsimple.ne_zero).mpr hr
  have hneg : r < 0 := peakPolynomial_roots_neg n hn r hrmem
  have hder : (peakPolynomial n).derivative.eval r ≠ 0 :=
    hsimple.eval_derivative_ne_zero hr
  have hrec : (peakPolynomial (n + 1)).eval r =
      (2 * r * (1 - r)) * (peakPolynomial n).derivative.eval r +
        (2 + (((n - 1 : ℕ) : ℝ)) * r) * (peakPolynomial n).eval r := by
    rw [peakPolynomial_succ n hn]
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
    ring
  rw [show (peakPolynomial n).eval r = 0 from hr,
    show (peakPolynomial (n + 1)).eval r = 0 from hnext] at hrec
  simp only [mul_zero, add_zero] at hrec
  have hfac : 2 * r * (1 - r) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (ne_of_lt hneg)
    · linarith
  exact (mul_ne_zero hfac hder) hrec.symm

/-- Every actual peak enumerator has only simple roots. Paper
`thm:permutationPeaks`. -/
theorem peakPolynomial_hasSimpleRoots (n : ℕ) (hn : 1 ≤ n) :
    HasSimpleRoots (peakPolynomial n) := by
  induction n with
  | zero => lia
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        have hbase : peakPolynomial 1 = 1 := by
          simpa [peakPolynomial] using
            RealRooted.peakValueWeightedDiagonal_one (fun _ : Fin 1 => 1)
        rw [hbase]
        intro r hr
        simp [Polynomial.IsRoot.def] at hr
      · have hn1 : 1 ≤ n := by lia
        have hprev : HasSimpleRoots (peakPolynomial n) := ih hn1
        have hweak := peakPolynomial_weakInterl n hn1
        exact (hweak.hasSimpleRoots_of_no_common_root
          (peakPolynomial_noCommonRoot_of_simple n hn1 hprev)).2

/-- Consecutive actual peak enumerators have disjoint, simple real roots,
so their interlacing is strict in the ordinary sense. Paper
`thm:permutationPeaks`. -/
theorem peakPolynomial_strictlyAlternating (n : ℕ) (hn : 1 ≤ n) :
    StrictlyAlternatingRoots (peakPolynomial n) (peakPolynomial (n + 1)) := by
  have hsimple := peakPolynomial_hasSimpleRoots n hn
  have hnext := peakPolynomial_hasSimpleRoots (n + 1) (by lia)
  have hweak := peakPolynomial_weakInterl n hn
  have hno := peakPolynomial_noCommonRoot_of_simple n hn hsimple
  refine ⟨Or.inl hweak, hsimple, hnext, ?_⟩
  intro r hr hrnext
  exact hno r ⟨(mem_roots hsimple.ne_zero).mp hr,
    (mem_roots hnext.ne_zero).mp hrnext⟩

end RealRooted.EulerianCompendium
