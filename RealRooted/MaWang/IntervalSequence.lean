module

public import RealRooted.BasisTransform.DifferentialOperatorMaps

/-!
# Closed-interval sequences from arbitrary seeds

We iterate the exact two-endpoint test for interval differential operators, including negative
linear slopes and arbitrary endpoint multiplicities in the seed. The criterion concerns every
row of a prefix: a final row alone does not determine whether earlier rows left the interval.

Source: the unpublished manuscript in RealRooted issue #2192, consolidation comment,
and Ma--Wang, *q-Eulerian polynomials and polynomials with only real zeros*, Theorem 2 and
Corollary 3 (arXiv:math/0611826v2).
-/

public section

open Polynomial Set

namespace RealRooted

/-- Every row through `N` stays in the closed interval exactly when each preceding step
satisfies both endpoint inequalities. The seed may have arbitrary endpoint multiplicities,
and the linear slope may be negative under the exact degree-growth hypothesis. -/
theorem intervalSequence_prefix_iff
    {P : ℕ → ℝ[X]} {alpha beta rho kappa : ℕ → ℝ} {L U : ℝ}
    (hrec : ∀ n, P (n + 1) =
      intervalDifferentialStep (alpha n) (beta n) (rho n) (kappa n) L U 0 (P n))
    (hrho : ∀ n, 0 < rho n) (hkappa : ∀ n, 0 < kappa n)
    (htop : ∀ n, 0 < alpha n + kappa n * ((P 0).natDegree + n : ℕ))
    (hpos : HasPosLeadingCoeff (P 0)) (hseed : IsRealRootedIn (Icc L U) (P 0))
    (N : ℕ) :
    (∀ n ≤ N, IsRealRootedIn (Icc L U) (P n)) ↔
      ∀ n < N,
        alpha n * L + beta n - kappa n * (U - L) * (P n).rootMultiplicity L ≤ 0 ∧
        0 ≤ alpha n * U + beta n + kappa n * (U - L) * (P n).rootMultiplicity U := by
  have step {n : ℕ} (hp : HasPosLeadingCoeff (P n))
      (hs : IsRealRootedIn (Icc L U) (P n))
      (hd : (P n).natDegree = (P 0).natDegree + n) :=
    intervalDifferentialStep_closed (beta := beta n) (xi := 0) (hrho n) (hkappa n)
      (hd ▸ htop n) hp hs.splits (fun _ hr => hs.mem_of_mem_roots hr)
  have scaled (n : ℕ) (x : ℝ) : rho n * x ≤ 0 ↔ x ≤ 0 :=
    by constructor <;> intro h <;> nlinarith [hrho n]
  have scaled' (n : ℕ) (x : ℝ) : 0 ≤ rho n * x ↔ 0 ≤ x :=
    mul_nonneg_iff_of_pos_left (hrho n)
  constructor
  · intro hall
    have hinv : ∀ n ≤ N, HasPosLeadingCoeff (P n) ∧
        (P n).natDegree = (P 0).natDegree + n := by
      intro n hn
      induction n with
      | zero => exact ⟨hpos, by simp⟩
      | succ n ih =>
        have hi := ih (by lia)
        have ht := step hi.1 (hall n (by lia)) hi.2
        rw [← hrec n] at ht
        exact ⟨ht.2.1, by rw [ht.1, hi.2]; lia⟩
    intro n hn
    have ht := step (hinv n (by lia)).1 (hall n (by lia)) (hinv n (by lia)).2
    rw [← hrec n] at ht
    have hb := ht.2.2.2.2.1.mp (fun _ hr => (hall (n + 1) (by lia)).mem_of_mem_roots hr)
    exact ⟨(scaled n _).mp hb.1, (scaled' n _).mp hb.2⟩
  · intro hb
    have hinv : ∀ n ≤ N, HasPosLeadingCoeff (P n) ∧
        IsRealRootedIn (Icc L U) (P n) ∧
        (P n).natDegree = (P 0).natDegree + n := by
      intro n hn
      induction n with
      | zero => exact ⟨hpos, hseed, by simp⟩
      | succ n ih =>
        have hi := ih (by lia)
        have ht := step hi.1 hi.2.1 hi.2.2
        rw [← hrec n] at ht
        have hroots := ht.2.2.2.2.1.mpr
          ⟨(scaled n _).mpr (hb n (by lia)).1, (scaled' n _).mpr (hb n (by lia)).2⟩
        exact ⟨ht.2.1, ⟨ht.2.1.ne_zero, ht.2.2.1, hroots⟩,
          by rw [ht.1, hi.2.2]; lia⟩
    exact fun n hn => (hinv n hn).2.1

/-- Under the endpoint inequalities, every row remains standard in the interval, has the
expected degree, interlaces its successor, and obeys the exact two endpoint multiplicity
updates. Both endpoint multiplicities may increase in the same step. -/
theorem intervalSequence_degree_interlaces_multiplicity
    {P : ℕ → ℝ[X]} {alpha beta rho kappa : ℕ → ℝ} {L U : ℝ}
    (hrec : ∀ n, P (n + 1) =
      intervalDifferentialStep (alpha n) (beta n) (rho n) (kappa n) L U 0 (P n))
    (hrho : ∀ n, 0 < rho n) (hkappa : ∀ n, 0 < kappa n)
    (htop : ∀ n, 0 < alpha n + kappa n * ((P 0).natDegree + n : ℕ))
    (hpos : HasPosLeadingCoeff (P 0)) (hseed : IsRealRootedIn (Icc L U) (P 0))
    (hb : ∀ n,
      alpha n * L + beta n - kappa n * (U - L) * (P n).rootMultiplicity L ≤ 0 ∧
      0 ≤ alpha n * U + beta n + kappa n * (U - L) * (P n).rootMultiplicity U) :
    ∀ n, HasPosLeadingCoeff (P n) ∧ IsRealRootedIn (Icc L U) (P n) ∧
      (P n).natDegree = (P 0).natDegree + n ∧ Interlaces (P n) (P (n + 1)) ∧
      (P (n + 1)).rootMultiplicity L =
        (if alpha n * L + beta n - kappa n * (U - L) * (P n).rootMultiplicity L = 0
          then (P n).rootMultiplicity L + 1 else (P n).rootMultiplicity L) ∧
      (P (n + 1)).rootMultiplicity U =
        if alpha n * U + beta n + kappa n * (U - L) * (P n).rootMultiplicity U = 0
          then (P n).rootMultiplicity U + 1 else (P n).rootMultiplicity U := by
  have hall (n : ℕ) : IsRealRootedIn (Icc L U) (P n) :=
    ((intervalSequence_prefix_iff hrec hrho hkappa htop hpos hseed n).mpr
      (fun j _ => hb j)) n le_rfl
  have hinv (n : ℕ) : HasPosLeadingCoeff (P n) ∧
      (P n).natDegree = (P 0).natDegree + n := by
    induction n with
    | zero => exact ⟨hpos, by simp⟩
    | succ n ih =>
      have ht := intervalDifferentialStep_strictInterl (beta := beta n) (xi := 0)
        (hrho n) (hkappa n) (ih.2 ▸ htop n) ih.1 (hall n).splits
        (fun _ hr => (hall n).mem_of_mem_roots hr)
      rw [← hrec n] at ht
      exact ⟨ht.2.1, by rw [ht.1, ih.2]; lia⟩
  intro n
  have ht := intervalDifferentialStep_closed (beta := beta n) (xi := 0)
    (hrho n) (hkappa n) ((hinv n).2 ▸ htop n) (hinv n).1
    (hall n).splits (fun _ hr => (hall n).mem_of_mem_roots hr)
  have hm := intervalDifferentialStep_rootMultiplicity (beta := beta n) (xi := 0)
    (hrho n) (hkappa n) ((hinv n).2 ▸ htop n) (hinv n).1
    (hall n).splits (fun _ hr => (hall n).mem_of_mem_roots hr)
  rw [← hrec n] at ht hm
  refine ⟨(hinv n).1, hall n, (hinv n).2, ht.2.2.2.1, ?_, ?_⟩
  · rw [hm.1]
    apply if_congr _ rfl rfl
    rw [eq_comm, mul_eq_zero, or_iff_right (hrho n).ne']
  · rw [hm.2]
    apply if_congr _ rfl rfl
    rw [eq_comm, mul_eq_zero, or_iff_right (hrho n).ne']

/-- Endpoint multiplicity predicted from the coefficients and the seed multiplicity alone.
It can be computed without constructing any polynomial row. -/
@[expose] noncomputable def intervalEndpointMultiplicity
    (alpha beta kappa : ℕ → ℝ) (e o : ℝ) (m₀ : ℕ) : ℕ → ℕ
  | 0 => m₀
  | n + 1 =>
    let m := intervalEndpointMultiplicity alpha beta kappa e o m₀ n
    if alpha n * e + beta n + kappa n * (e - o) * m = 0 then m + 1 else m

/-- A confined prefix has the multiplicities predicted by the scalar endpoint counters. -/
theorem intervalSequence_prefix_multiplicity
    {P : ℕ → ℝ[X]} {alpha beta rho kappa : ℕ → ℝ} {L U : ℝ}
    (hrec : ∀ n, P (n + 1) =
      intervalDifferentialStep (alpha n) (beta n) (rho n) (kappa n) L U 0 (P n))
    (hrho : ∀ n, 0 < rho n) (hkappa : ∀ n, 0 < kappa n)
    (htop : ∀ n, 0 < alpha n + kappa n * ((P 0).natDegree + n : ℕ))
    (hpos : HasPosLeadingCoeff (P 0)) {N : ℕ}
    (hall : ∀ n ≤ N, IsRealRootedIn (Icc L U) (P n)) :
    ∀ n ≤ N, HasPosLeadingCoeff (P n) ∧ (P n).natDegree = (P 0).natDegree + n ∧
      (P n).rootMultiplicity L =
        intervalEndpointMultiplicity alpha beta kappa L U ((P 0).rootMultiplicity L) n ∧
      (P n).rootMultiplicity U =
        intervalEndpointMultiplicity alpha beta kappa U L ((P 0).rootMultiplicity U) n := by
  intro n hn
  induction n with
  | zero => exact ⟨hpos, by simp, rfl, rfl⟩
  | succ n ih =>
    have hi := ih (by lia)
    have ht := intervalDifferentialStep_strictInterl (beta := beta n) (xi := 0)
      (hrho n) (hkappa n) (hi.2.1 ▸ htop n) hi.1 (hall n (by lia)).splits
      (fun _ hr => (hall n (by lia)).mem_of_mem_roots hr)
    have hm := intervalDifferentialStep_rootMultiplicity (beta := beta n) (xi := 0)
      (hrho n) (hkappa n) (hi.2.1 ▸ htop n) hi.1 (hall n (by lia)).splits
      (fun _ hr => (hall n (by lia)).mem_of_mem_roots hr)
    rw [← hrec n] at ht hm
    refine ⟨ht.2.1, by rw [ht.1, hi.2.1]; lia, ?_, ?_⟩
    · rw [hm.1, intervalEndpointMultiplicity, hi.2.2.1]
      apply if_congr _ rfl rfl
      rw [eq_comm, mul_eq_zero, or_iff_right (hrho n).ne']
      constructor <;> intro h <;> nlinarith
    · rw [hm.2, intervalEndpointMultiplicity, hi.2.2.2]
      apply if_congr _ rfl rfl
      rw [eq_comm, mul_eq_zero, or_iff_right (hrho n).ne']

/-- Scalar multiplicity-counter iff for every prefix from an arbitrary seed. Unlike a test
using the actual polynomial multiplicities, its right side depends only on the coefficient
sequences, the window, and the seed's two endpoint multiplicities. -/
theorem intervalSequence_prefix_iff_multiplicity
    {P : ℕ → ℝ[X]} {alpha beta rho kappa : ℕ → ℝ} {L U : ℝ}
    (hrec : ∀ n, P (n + 1) =
      intervalDifferentialStep (alpha n) (beta n) (rho n) (kappa n) L U 0 (P n))
    (hrho : ∀ n, 0 < rho n) (hkappa : ∀ n, 0 < kappa n)
    (htop : ∀ n, 0 < alpha n + kappa n * ((P 0).natDegree + n : ℕ))
    (hpos : HasPosLeadingCoeff (P 0)) (hseed : IsRealRootedIn (Icc L U) (P 0))
    (N : ℕ) :
    (∀ n ≤ N, IsRealRootedIn (Icc L U) (P n)) ↔
      ∀ n < N,
        alpha n * L + beta n - kappa n * (U - L) *
          intervalEndpointMultiplicity alpha beta kappa L U ((P 0).rootMultiplicity L) n ≤ 0 ∧
        0 ≤ alpha n * U + beta n + kappa n * (U - L) *
          intervalEndpointMultiplicity alpha beta kappa U L ((P 0).rootMultiplicity U) n := by
  constructor
  · intro hall n hn
    have hm := intervalSequence_prefix_multiplicity hrec hrho hkappa htop hpos hall n (by lia)
    have hb := (intervalSequence_prefix_iff hrec hrho hkappa htop hpos hseed N).mp hall n hn
    simpa only [hm.2.2.1, hm.2.2.2] using hb
  · induction N with
    | zero =>
      intro _ n hn
      have hn0 : n = 0 := by lia
      simpa only [hn0] using hseed
    | succ N ih =>
      intro hb
      have hprev := ih (fun n hn => hb n (by lia))
      apply (intervalSequence_prefix_iff hrec hrho hkappa htop hpos hseed (N + 1)).mpr
      intro n hn
      have hle : n ≤ N := by lia
      have hm := intervalSequence_prefix_multiplicity hrec hrho hkappa htop hpos hprev n hle
      simpa only [hm.2.2.1, hm.2.2.2] using hb n hn

/-- All rows from an arbitrary seed are confined exactly when both scalar endpoint counters
satisfy their inequalities at every step. -/
theorem intervalSequence_iff_multiplicity
    {P : ℕ → ℝ[X]} {alpha beta rho kappa : ℕ → ℝ} {L U : ℝ}
    (hrec : ∀ n, P (n + 1) =
      intervalDifferentialStep (alpha n) (beta n) (rho n) (kappa n) L U 0 (P n))
    (hrho : ∀ n, 0 < rho n) (hkappa : ∀ n, 0 < kappa n)
    (htop : ∀ n, 0 < alpha n + kappa n * ((P 0).natDegree + n : ℕ))
    (hpos : HasPosLeadingCoeff (P 0)) (hseed : IsRealRootedIn (Icc L U) (P 0)) :
    (∀ n, IsRealRootedIn (Icc L U) (P n)) ↔
      ∀ n,
        alpha n * L + beta n - kappa n * (U - L) *
          intervalEndpointMultiplicity alpha beta kappa L U ((P 0).rootMultiplicity L) n ≤ 0 ∧
        0 ≤ alpha n * U + beta n + kappa n * (U - L) *
          intervalEndpointMultiplicity alpha beta kappa U L ((P 0).rootMultiplicity U) n := by
  constructor
  · intro hall n
    exact (intervalSequence_prefix_iff_multiplicity hrec hrho hkappa htop hpos hseed
      (n + 1)).mp (fun j _ => hall j) n (by lia)
  · intro hb n
    exact ((intervalSequence_prefix_iff_multiplicity hrec hrho hkappa htop hpos hseed n).mpr
      (fun j _ => hb j)) n le_rfl

end RealRooted
