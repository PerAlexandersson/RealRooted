import RealRooted.HosterStump.FlagF
import RealRooted.HosterStump.HVector
import RealRooted.HosterStump.DesMobius
import RealRooted.HosterStump.DescentLe

/-!
# Chow polynomials of graded simplicial posets

Identity (1.3) of Hoster and Stump (arXiv:2508.15538), after Stanley: for a graded simplicial
poset `P` of rank `n` with `h`-vector `h`, the flag `h`-vector of `P̂` is
`β(S) = ∑ k, h_k · #{w ∈ 𝔖_{n+1} | w 1 = k + 1, Des w = n + 1 - S}`
(`isSimplicialFlagH_flagH`).  Together with `RealRooted.HosterStump.isRealRooted_chowOfFlagH`
and its companions this gives Theorems 1.1 and 1.2 for posets: if `P` has a nonnegative
`h`-vector, then the Chow, dual Chow and augmented Chow polynomials of `P̂` are real-rooted,
and the dual Chow polynomial interlaces the augmented one.

The proof: a chain with ranks `T + 1` is a top element of rank `max T + 1` and a chain in its
Boolean lower interval (`flagF_eq_fVec_mul`); the `f`-vector is `f_i = ∑ k, h_k C(n - k, n - i)`
(`fVec_eq_sum_hVec`); the permutations with `w 0 = k` and descents in `n + 1 - T` are counted
by the same product (`desLeCount_reflectSet`); inclusion–exclusion on both sides
(`desCount_reflectSet_eq_sum`) gives (1.3).
-/

open Polynomial Finset

namespace RealRooted.HosterStump

variable {P : Type*} [PartialOrder P] [Fintype P] {n : ℕ} {rk : P → ℕ}

omit [Fintype P] in
/-- In a simplicial poset with a bottom element, the elements of rank `0` are exactly `⊥`. -/
theorem IsSimplicialPoset.rk_eq_zero_iff [OrderBot P] (hP : IsSimplicialPoset P n rk) {x : P} :
    rk x = 0 ↔ x = ⊥ := by
  constructor
  · intro hx
    have hcard : Nat.card (Set.Iic x) = 1 := by rw [hP.natCard_Iic, hx, pow_zero]
    obtain ⟨a, ha⟩ := Nat.card_eq_one_iff_exists.mp hcard
    have h1 := ha ⟨x, Set.mem_Iic.mpr le_rfl⟩
    have h2 := ha ⟨⊥, Set.mem_Iic.mpr bot_le⟩
    exact congrArg Subtype.val (h1.trans h2.symm)
  · rintro rfl
    have hcard : Nat.card (Set.Iic (⊥ : P)) = 1 := by
      rw [Set.Iic_bot, Nat.card_unique]
    rw [hP.natCard_Iic] at hcard
    exact (Nat.pow_eq_one.mp hcard).resolve_left (by norm_num)

/-- A simplicial poset with a bottom element has exactly one element of rank `0`. -/
theorem fVec_zero [OrderBot P] (hP : IsSimplicialPoset P n rk) : fVec rk 0 = 1 := by
  classical
  rw [fVec, Finset.card_eq_one]
  refine ⟨⊥, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  convert hP.rk_eq_zero_iff

/-- The first entry of the `h`-vector of a simplicial poset with a bottom element is `1`. -/
theorem hVec_zero [OrderBot P] (hP : IsSimplicialPoset P n rk) : hVec n rk 0 = 1 := by
  have h := fVec_eq_sum_hVec n rk 0 (Nat.zero_le n)
  rw [fVec_zero hP, Finset.sum_eq_single 0] at h
  · simpa using h.symm
  · intro k hk hk0
    rw [Nat.choose_eq_zero_of_lt (by have := Finset.mem_range.mp hk; lia), Nat.cast_zero,
      mul_zero]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0

/-- The flag `f`-vector of a simplicial poset in terms of its `h`-vector and the permutations
with descents in the reflected positions. -/
theorem flagF_eq_sum_hVec_mul_desLeCount [OrderBot P] (hP : IsSimplicialPoset P n rk)
    {T : Finset ℕ} (hT : T ⊆ range n) :
    (flagF rk T : ℝ) =
      ∑ k ∈ range (n + 1), hVec n rk k * (desLeCount n k (reflectSet n T) : ℝ) := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · have hr : reflectSet n ∅ = ∅ := by simp [reflectSet]
    rw [flagF_empty, hr, Finset.sum_eq_single 0]
    · simp [desLeCount_empty, hVec_zero hP]
    · intro k _ hk
      simp [desLeCount_empty, hk]
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0
  · have hm : T.max' hne < n := Finset.mem_range.mp (hT (T.max'_mem hne))
    rw [flagF_eq_fVec_mul hP T hne, Nat.cast_mul, fVec_eq_sum_hVec n rk _ (by lia),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [desLeCount_reflectSet hT hne (by have := Finset.mem_range.mp hk; lia), Nat.cast_mul,
      show n - (T.max' hne + 1) = n - T.max' hne - 1 by lia]
    ring

/-- Identity (1.3) of Hoster--Stump (Stanley): the flag `h`-vector of a graded simplicial poset
with a bottom element is `∑ k, h_k · desCount n k (n + 1 - S)`. -/
theorem isSimplicialFlagH_flagH [OrderBot P] (hP : IsSimplicialPoset P n rk) :
    IsSimplicialFlagH n (hVec n rk) (flagH rk) := by
  intro S hS
  calc flagH rk S
      = ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card *
          ∑ k ∈ range (n + 1), hVec n rk k * (desLeCount n k (reflectSet n T) : ℝ) :=
        Finset.sum_congr rfl fun T hT => by
          rw [flagF_eq_sum_hVec_mul_desLeCount hP ((Finset.mem_powerset.mp hT).trans hS)]
    _ = ∑ k ∈ range (n + 1), hVec n rk k * ∑ T ∈ S.powerset,
          (-1 : ℝ) ^ (S \ T).card * (desLeCount n k (reflectSet n T) : ℝ) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun T _ => by ring
    _ = ∑ k ∈ range (n + 1), hVec n rk k * (desCount n k (reflectSet n S) : ℝ) :=
        Finset.sum_congr rfl fun k _ => by rw [desCount_reflectSet_eq_sum n k hS]

/-- Hoster--Stump, Theorem 1.1: a graded simplicial poset with nonnegative `h`-vector has a
real-rooted Chow polynomial `H_{P̂}`. -/
theorem isRealRooted_chowOfFlagH_flagH [OrderBot P] (hP : IsSimplicialPoset P n rk)
    (hh : ∀ k, 0 ≤ hVec n rk k) :
    chowOfFlagH n (flagH rk) ≠ 0 ∧ (chowOfFlagH n (flagH rk)).Splits :=
  isRealRooted_chowOfFlagH hh (by rw [hVec_zero hP]; norm_num) (isSimplicialFlagH_flagH hP)

/-- Hoster--Stump, Theorem 1.1: a graded simplicial poset with nonnegative `h`-vector has a
real-rooted augmented Chow polynomial `H^aug_{P̂}`. -/
theorem isRealRooted_augChowOfFlagH_flagH [OrderBot P] (hP : IsSimplicialPoset P n rk)
    (hh : ∀ k, 0 ≤ hVec n rk k) :
    augChowOfFlagH n (flagH rk) ≠ 0 ∧ (augChowOfFlagH n (flagH rk)).Splits :=
  isRealRooted_augChowOfFlagH hh (by rw [hVec_zero hP]; norm_num) (isSimplicialFlagH_flagH hP)

/-- Hoster--Stump, Theorem 1.2: a graded simplicial poset with nonnegative `h`-vector has a
real-rooted dual Chow polynomial `H_{P̂*}`. -/
theorem isRealRooted_chowOfFlagH_dualFlagH_flagH [OrderBot P] (hP : IsSimplicialPoset P n rk)
    (hh : ∀ k, 0 ≤ hVec n rk k) :
    chowOfFlagH n (dualFlagH n (flagH rk)) ≠ 0 ∧
      (chowOfFlagH n (dualFlagH n (flagH rk))).Splits :=
  isRealRooted_chowOfFlagH_dualFlagH hh (by rw [hVec_zero hP]; norm_num)
    (isSimplicialFlagH_flagH hP)

/-- Hoster--Stump, Theorem 1.2: for a graded simplicial poset of rank `n ≥ 1` with nonnegative
`h`-vector, the dual Chow polynomial interlaces the augmented Chow polynomial. -/
theorem strictInterl_chowOfFlagH_dualFlagH_augChowOfFlagH_flagH [OrderBot P]
    (hP : IsSimplicialPoset P n rk) (hn : 1 ≤ n) (hh : ∀ k, 0 ≤ hVec n rk k) :
    StrictInterl (chowOfFlagH n (dualFlagH n (flagH rk))) (augChowOfFlagH n (flagH rk)) :=
  strictInterl_chowOfFlagH_dualFlagH_augChowOfFlagH hn hh (by rw [hVec_zero hP]; norm_num)
    (isSimplicialFlagH_flagH hP)

end RealRooted.HosterStump
