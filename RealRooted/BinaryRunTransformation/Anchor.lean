import RealRooted.BinaryRunTransformation.Deformation
import RealRooted.CriticalValueContinuation
import RealRooted.DegreeDropReversal
import RealRooted.Favard
import RealRooted.Hadamard.Grace
import RealRooted.IteratedDerivativeShift
import RealRooted.SimpleRoots

/-!
# The small-scale anchor of the binary-run deformation

This file packages the path-matching polynomial

`F_N(X) = ∑_k choose (N-k) k X^k`

and the polynomial family obtained by applying the binary-run deformation and
rescaling `X` by the deformation parameter.  At parameter zero, the rescaled
family is exactly a fixed-degree Schur--Szegő composition with `F_(n+1)`.
-/

open Polynomial Finset
open scoped ContDiff

noncomputable section

namespace RealRooted

/-- The matching-generating polynomial of a path on `N` vertices. -/
def pathMatchingPolynomial (N : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (N / 2 + 1),
    monomial k (Nat.choose (N - k) k : ℝ)

@[simp] theorem coeff_pathMatchingPolynomial_of_le {N k : ℕ}
    (hk : k ≤ N / 2) :
    (pathMatchingPolynomial N).coeff k = (Nat.choose (N - k) k : ℝ) := by
  rw [pathMatchingPolynomial, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single_of_mem k (by simpa using hk)]
  · simp
  · intro j hj hjk
    simp [Polynomial.coeff_monomial, hjk]

@[simp] theorem coeff_pathMatchingPolynomial_of_lt {N k : ℕ}
    (hk : N / 2 < k) :
    (pathMatchingPolynomial N).coeff k = 0 := by
  rw [pathMatchingPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  have hjk : j ≠ k := by
    have hjle : j ≤ N / 2 := by simpa using hj
    lia
  simp [Polynomial.coeff_monomial, hjk]

@[simp] theorem coeff_pathMatchingPolynomial (N k : ℕ) :
    (pathMatchingPolynomial N).coeff k = (Nat.choose (N - k) k : ℝ) := by
  by_cases hk : k ≤ N / 2
  · exact coeff_pathMatchingPolynomial_of_le hk
  · rw [coeff_pathMatchingPolynomial_of_lt (Nat.lt_of_not_ge hk),
      Nat.choose_eq_zero_of_lt (by lia)]
    norm_num

@[simp] theorem coeff_zero_pathMatchingPolynomial (N : ℕ) :
    (pathMatchingPolynomial N).coeff 0 = 1 := by
  rw [coeff_pathMatchingPolynomial_of_le (Nat.zero_le _)]
  simp

theorem pathMatchingPolynomial_ne_zero (N : ℕ) :
    pathMatchingPolynomial N ≠ 0 := by
  intro hzero
  have := congrArg (fun p : ℝ[X] => p.coeff 0) hzero
  simp at this

theorem natDegree_pathMatchingPolynomial_le (N : ℕ) :
    (pathMatchingPolynomial N).natDegree ≤ N / 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  exact coeff_pathMatchingPolynomial_of_lt hk

theorem natDegree_pathMatchingPolynomial (N : ℕ) :
    (pathMatchingPolynomial N).natDegree = N / 2 := by
  apply le_antisymm (natDegree_pathMatchingPolynomial_le N)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [coeff_pathMatchingPolynomial]
  exact_mod_cast (Nat.choose_pos (by lia : N / 2 ≤ N - N / 2)).ne'

theorem hasNonnegCoeffs_pathMatchingPolynomial (N : ℕ) :
    HasNonnegCoeffs (pathMatchingPolynomial N) := by
  intro k
  by_cases hk : k ≤ N / 2
  · rw [coeff_pathMatchingPolynomial_of_le hk]
    positivity
  · rw [coeff_pathMatchingPolynomial_of_lt (Nat.lt_of_not_ge hk)]

/-- Deleting the first vertex of a path gives the standard matching
recurrence. -/
theorem pathMatchingPolynomial_add_two (N : ℕ) :
    pathMatchingPolynomial (N + 2) =
      pathMatchingPolynomial (N + 1) + X * pathMatchingPolynomial N := by
  ext k
  rcases k with _ | k
  · simp
  rw [coeff_add, coeff_X_mul, coeff_pathMatchingPolynomial,
    coeff_pathMatchingPolynomial, coeff_pathMatchingPolynomial]
  by_cases hk : k ≤ N
  · have hpascal := Nat.choose_succ_succ' (N - k) k
    rw [show N + 2 - (k + 1) = N - k + 1 by lia,
      show N + 1 - (k + 1) = N - k by lia,
      hpascal]
    push_cast
    ring
  · have hkN : N < k := Nat.lt_of_not_ge hk
    rw [Nat.choose_eq_zero_of_lt (by lia : N + 2 - (k + 1) < k + 1),
      Nat.choose_eq_zero_of_lt (by lia : N + 1 - (k + 1) < k + 1),
      Nat.choose_eq_zero_of_lt (by lia : N - k < k)]
    simp

/-- The parity subsequences satisfy a two-step recurrence whose reversals are
in monic Favard form. -/
theorem pathMatchingPolynomial_add_four (N : ℕ) :
    pathMatchingPolynomial (N + 4) =
      (1 + 2 * X) * pathMatchingPolynomial (N + 2) -
        X ^ 2 * pathMatchingPolynomial N := by
  have hback : pathMatchingPolynomial (N + 1) =
      pathMatchingPolynomial (N + 2) - X * pathMatchingPolynomial N := by
    rw [pathMatchingPolynomial_add_two]
    ring
  rw [show N + 4 = (N + 2) + 2 by lia,
    pathMatchingPolynomial_add_two,
    show N + 3 = (N + 1) + 2 by lia,
    pathMatchingPolynomial_add_two, hback]
  ring

/-- Degree-normalized reversal of the even path subsequence. -/
def evenPathReverse (d : ℕ) : ℝ[X] :=
  (pathMatchingPolynomial (2 * d)).reflect d

/-- Degree-normalized reversal of the odd path subsequence. -/
def oddPathReverse (d : ℕ) : ℝ[X] :=
  (pathMatchingPolynomial (2 * d + 1)).reflect d

@[simp] theorem evenPathReverse_zero : evenPathReverse 0 = 1 := by
  simp [evenPathReverse, pathMatchingPolynomial]

@[simp] theorem evenPathReverse_one : evenPathReverse 1 = X + 1 := by
  ext k
  rw [evenPathReverse, Polynomial.coeff_reflect,
    coeff_pathMatchingPolynomial]
  rcases k with _ | k
  · rw [Polynomial.revAt_le (by lia)]
    norm_num
  · rcases k with _ | k
    · rw [Polynomial.revAt_le (by lia)]
      norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
    · rw [Polynomial.revAt_eq_self_of_lt (by lia)]
      simp [Polynomial.coeff_one, Polynomial.coeff_X]

@[simp] theorem oddPathReverse_zero : oddPathReverse 0 = 1 := by
  simp [oddPathReverse, pathMatchingPolynomial]

@[simp] theorem oddPathReverse_one : oddPathReverse 1 = X + 2 := by
  ext k
  rw [oddPathReverse, Polynomial.coeff_reflect,
    coeff_pathMatchingPolynomial]
  rcases k with _ | k
  · rw [Polynomial.revAt_le (by lia)]
    norm_num
  · rcases k with _ | k
    · rw [Polynomial.revAt_le (by lia)]
      norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
    · rw [Polynomial.revAt_eq_self_of_lt (by lia)]
      rw [Nat.choose_eq_zero_of_lt (by lia : 3 - (k + 2) < k + 2)]
      simp [Polynomial.coeff_X]

private theorem reflect_one_add_two_mul_X :
    (1 + 2 * X : ℝ[X]).reflect 1 = X + 2 := by
  ext k
  rw [Polynomial.coeff_reflect]
  rcases k with _ | k
  · rw [Polynomial.revAt_le (by lia)]
    norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  · rcases k with _ | k
    · rw [Polynomial.revAt_le (by lia)]
      norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
    · rw [Polynomial.revAt_eq_self_of_lt (by lia)]
      simp [Polynomial.coeff_one, Polynomial.coeff_X]

private theorem reflect_X_sq :
    (X ^ 2 : ℝ[X]).reflect 2 = 1 := by
  ext k
  rw [Polynomial.coeff_reflect]
  rcases k with _ | k
  · rw [Polynomial.revAt_le (by lia)]
    norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  · rcases k with _ | k
    · rw [Polynomial.revAt_le (by lia)]
      norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
    · rcases k with _ | k
      · rw [Polynomial.revAt_le (by lia)]
        norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
      · rw [Polynomial.revAt_eq_self_of_lt (by lia)]
        simp [Polynomial.coeff_one]

theorem evenPathReverse_add_two (d : ℕ) :
    evenPathReverse (d + 2) =
      (X + 2) * evenPathReverse (d + 1) - evenPathReverse d := by
  have hmain := congrArg (fun p : ℝ[X] => p.reflect (d + 2))
    (pathMatchingPolynomial_add_four (2 * d))
  have hlin : (1 + 2 * X : ℝ[X]).natDegree ≤ 1 := by
    norm_num
  have hnext : (pathMatchingPolynomial (2 * d + 2)).natDegree ≤ d + 1 := by
    rw [natDegree_pathMatchingPolynomial]
    norm_num [Nat.add_div]
  have hbase : (pathMatchingPolynomial (2 * d)).natDegree ≤ d := by
    rw [natDegree_pathMatchingPolynomial]
    norm_num
  have hprodNext := Polynomial.reflect_mul
    (F := 1) (G := d + 1) (1 + 2 * X : ℝ[X])
      (pathMatchingPolynomial (2 * d + 2)) hlin hnext
  have hprodBase := Polynomial.reflect_mul
    (F := 2) (G := d) (X ^ 2 : ℝ[X])
      (pathMatchingPolynomial (2 * d)) (by simp) hbase
  rw [Polynomial.reflect_sub] at hmain
  have hprodNext' :
      ((1 + 2 * X) * pathMatchingPolynomial (2 * d + 2)).reflect (d + 2) =
        (1 + 2 * X : ℝ[X]).reflect 1 *
          (pathMatchingPolynomial (2 * d + 2)).reflect (d + 1) := by
    simpa only [show d + 2 = 1 + (d + 1) by lia] using hprodNext
  have hprodBase' :
      (X ^ 2 * pathMatchingPolynomial (2 * d)).reflect (d + 2) =
        (X ^ 2 : ℝ[X]).reflect 2 *
          (pathMatchingPolynomial (2 * d)).reflect d := by
    simpa only [show d + 2 = 2 + d by lia] using hprodBase
  rw [hprodNext', hprodBase', reflect_one_add_two_mul_X,
    reflect_X_sq, one_mul] at hmain
  simpa only [evenPathReverse,
    show 2 * (d + 2) = 2 * d + 4 by ring,
    show 2 * (d + 1) = 2 * d + 2 by ring] using hmain

theorem oddPathReverse_add_two (d : ℕ) :
    oddPathReverse (d + 2) =
      (X + 2) * oddPathReverse (d + 1) - oddPathReverse d := by
  have hmain := congrArg (fun p : ℝ[X] => p.reflect (d + 2))
    (pathMatchingPolynomial_add_four (2 * d + 1))
  have hlin : (1 + 2 * X : ℝ[X]).natDegree ≤ 1 := by
    norm_num
  have hnext :
      (pathMatchingPolynomial (2 * d + 3)).natDegree ≤ d + 1 := by
    rw [natDegree_pathMatchingPolynomial]
    norm_num [Nat.add_div]
  have hbase :
      (pathMatchingPolynomial (2 * d + 1)).natDegree ≤ d := by
    rw [natDegree_pathMatchingPolynomial]
    norm_num [Nat.add_div]
  have hprodNext := Polynomial.reflect_mul
    (F := 1) (G := d + 1) (1 + 2 * X : ℝ[X])
      (pathMatchingPolynomial (2 * d + 3)) hlin hnext
  have hprodBase := Polynomial.reflect_mul
    (F := 2) (G := d) (X ^ 2 : ℝ[X])
      (pathMatchingPolynomial (2 * d + 1)) (by simp) hbase
  rw [Polynomial.reflect_sub] at hmain
  have hprodNext' :
      ((1 + 2 * X) * pathMatchingPolynomial (2 * d + 3)).reflect (d + 2) =
        (1 + 2 * X : ℝ[X]).reflect 1 *
          (pathMatchingPolynomial (2 * d + 3)).reflect (d + 1) := by
    simpa only [show d + 2 = 1 + (d + 1) by lia] using hprodNext
  have hprodBase' :
      (X ^ 2 * pathMatchingPolynomial (2 * d + 1)).reflect (d + 2) =
        (X ^ 2 : ℝ[X]).reflect 2 *
          (pathMatchingPolynomial (2 * d + 1)).reflect d := by
    simpa only [show d + 2 = 2 + d by lia] using hprodBase
  rw [show 2 * d + 1 + 2 = 2 * d + 3 by ring] at hmain
  rw [hprodNext', hprodBase', reflect_one_add_two_mul_X,
    reflect_X_sq, one_mul] at hmain
  simpa only [oddPathReverse,
    show 2 * (d + 2) + 1 = 2 * d + 1 + 4 by ring,
    show 2 * (d + 1) + 1 = 2 * d + 3 by ring] using hmain

private def evenPathAlpha (d : ℕ) : ℝ :=
  if d = 0 then -1 else -2

private def pathBeta (_d : ℕ) : ℝ :=
  1

theorem evenPathReverse_satisfiesFavardRecurrence :
    SatisfiesFavardRecurrence evenPathReverse evenPathAlpha pathBeta := by
  refine ⟨evenPathReverse_zero, ?_, ?_⟩
  · simp [evenPathAlpha]
  · intro d
    rw [evenPathReverse_add_two]
    norm_num [evenPathAlpha, pathBeta, Polynomial.C_ofNat]

theorem oddPathReverse_satisfiesFavardRecurrence :
    SatisfiesFavardRecurrence oddPathReverse (fun _ ↦ -2) pathBeta := by
  refine ⟨oddPathReverse_zero, ?_, ?_⟩
  · simp [Polynomial.C_ofNat]
  · intro d
    rw [oddPathReverse_add_two]
    norm_num [pathBeta, Polynomial.C_ofNat]

theorem evenPathReverse_splits (d : ℕ) :
    (evenPathReverse d).Splits :=
  (isRealRooted_of_favard evenPathReverse_satisfiesFavardRecurrence
    (by simp [pathBeta]) d).2

theorem oddPathReverse_splits (d : ℕ) :
    (oddPathReverse d).Splits :=
  (isRealRooted_of_favard oddPathReverse_satisfiesFavardRecurrence
    (by simp [pathBeta]) d).2

theorem evenPathReverse_roots_nodup (d : ℕ) :
    (evenPathReverse d).roots.Nodup :=
  roots_nodup_of_favard evenPathReverse_satisfiesFavardRecurrence
    (by simp [pathBeta]) d

theorem oddPathReverse_roots_nodup (d : ℕ) :
    (oddPathReverse d).roots.Nodup :=
  roots_nodup_of_favard oddPathReverse_satisfiesFavardRecurrence
    (by simp [pathBeta]) d

theorem pathMatchingPolynomial_splits (N : ℕ) :
    (pathMatchingPolynomial N).Splits := by
  obtain ⟨d, rfl | rfl⟩ := Nat.even_or_odd' N
  · apply (DegreeDropReversal.splits_reflect_iff (N := d) (by
      rw [natDegree_pathMatchingPolynomial]
      norm_num)).mp
    exact evenPathReverse_splits d
  · apply (DegreeDropReversal.splits_reflect_iff (N := d) (by
      rw [natDegree_pathMatchingPolynomial]
      norm_num [Nat.add_div])).mp
    exact oddPathReverse_splits d

theorem pathMatchingPolynomial_hasSimpleRoots (N : ℕ) :
    HasSimpleRoots (pathMatchingPolynomial N) := by
  obtain ⟨d, rfl | rfl⟩ := Nat.even_or_odd' N
  · have hreverse :
        (pathMatchingPolynomial (2 * d)).reverse = evenPathReverse d := by
      rw [evenPathReverse,
        DegreeDropReversal.reflect_eq_X_pow_mul_reverse
          _ (N := d) (by
            rw [natDegree_pathMatchingPolynomial]
            norm_num),
        natDegree_pathMatchingPolynomial]
      norm_num
    have hmap := evenPathReverse_roots_nodup d
    rw [← hreverse,
      DegreeDropReversal.roots_reverse_eq_map_inv_of_splits_coeff_zero_ne
        (pathMatchingPolynomial_splits (2 * d)) (by simp)] at hmap
    exact HasSimpleRoots.of_roots_nodup (pathMatchingPolynomial_ne_zero _)
      ((Multiset.nodup_map_iff_of_injective inv_injective).mp hmap)
  · have hreverse :
        (pathMatchingPolynomial (2 * d + 1)).reverse = oddPathReverse d := by
      rw [oddPathReverse,
        DegreeDropReversal.reflect_eq_X_pow_mul_reverse
          _ (N := d) (by
            rw [natDegree_pathMatchingPolynomial]
            norm_num [Nat.add_div]),
        natDegree_pathMatchingPolynomial]
      norm_num [Nat.add_div]
    have hmap := oddPathReverse_roots_nodup d
    rw [← hreverse,
      DegreeDropReversal.roots_reverse_eq_map_inv_of_splits_coeff_zero_ne
        (pathMatchingPolynomial_splits (2 * d + 1)) (by simp)] at hmap
    exact HasSimpleRoots.of_roots_nodup (pathMatchingPolynomial_ne_zero _)
      ((Multiset.nodup_map_iff_of_injective inv_injective).mp hmap)

theorem isPFPolynomial_pathMatchingPolynomial (N : ℕ) :
    IsPFPolynomial (pathMatchingPolynomial N) :=
  IsPFPolynomial.of_realRooted_nonneg
    (hasNonnegCoeffs_pathMatchingPolynomial N)
    (pathMatchingPolynomial_splits N)

theorem HasNonnegCoeffs.coeff_comp_X_add_C_pos
    {p : ℝ[X]} (hp : HasNonnegCoeffs p) (hp0 : p ≠ 0)
    {u : ℝ} (hu : 0 < u) {k : ℕ} (hk : k ≤ p.natDegree) :
    0 < (p.comp (X + C u)).coeff k := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def,
    Polynomial.finsetSum_coeff]
  apply Finset.sum_pos'
  · intro m hm
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
    exact mul_nonneg (hp m) <| mul_nonneg (pow_nonneg hu.le _)
      (Nat.cast_nonneg _)
  · refine ⟨p.natDegree, ?_, ?_⟩
    · rw [Polynomial.mem_support_iff, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp0
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
      have hlead : 0 < p.coeff p.natDegree := by
        rw [Polynomial.coeff_natDegree]
        exact hp.pos_leadingCoeff hp0
      have hchoose : 0 < (Nat.choose p.natDegree k : ℝ) := by
        exact_mod_cast Nat.choose_pos hk
      positivity

/-- A path-matching polynomial of positive degree admits small positive and
negative constant perturbations that still split over `ℝ`. -/
theorem exists_pos_pathMatchingPolynomial_add_C_splits {N : ℕ}
    (hN : (pathMatchingPolynomial N).natDegree ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      (pathMatchingPolynomial N + C ε).Splits ∧
        (pathMatchingPolynomial N + C (-ε)).Splits := by
  let q : ℝ → ℝ[X] := fun u ↦ pathMatchingPolynomial N + C u
  obtain ⟨ξ, _hξbase, hlocal⟩ :=
    exists_eventually_polynomial_root_branches q (t := 0)
      (D := (pathMatchingPolynomial N).natDegree) hN
      (Filter.Eventually.of_forall fun u : ℝ ↦ by simp [q])
      (by simpa [q] using pathMatchingPolynomial_splits N)
      (by simpa [q] using pathMatchingPolynomial_hasSimpleRoots N)
      (by
        intro x hx
        have heval : (fun z : ℝ × ℝ ↦ (q z.1).eval z.2) =
            fun z ↦ (pathMatchingPolynomial N).eval z.2 + z.1 := by
          funext z
          simp [q]
        rw [heval]
        exact (((Polynomial.contDiff_aeval (pathMatchingPolynomial N) 1).comp
          contDiff_snd).add contDiff_fst).contDiffAt)
  have hsplits : ∀ᶠ u in nhds (0 : ℝ), (q u).Splits :=
    hlocal.mono fun u hu ↦ hu.1
  rcases Metric.mem_nhds_iff.mp hsplits with ⟨δ, hδ, hball⟩
  let ε : ℝ := min (δ / 2) (1 / 2)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hεδ : ε < δ := by
    dsimp [ε]
    exact (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hε1 : ε < 1 := by
    dsimp [ε]
    linarith [min_le_right (δ / 2) (1 / 2 : ℝ)]
  refine ⟨ε, hε, hε1, ?_, ?_⟩
  · apply hball
    simpa [Real.dist_eq, abs_of_pos hε] using hεδ
  · apply hball
    simpa [Real.dist_eq, abs_of_pos hε] using hεδ

/-- The limiting polynomial in the small-scale binary-run deformation. -/
def binaryRunAnchor (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  schurSzegoComp n (pathMatchingPolynomial (n + 1)) p

private theorem schurSzegoComp_add_C_left (n : ℕ)
    (f p : ℝ[X]) (u : ℝ) :
    schurSzegoComp n (f + C u) p =
      schurSzegoComp n f p + C (u * p.coeff 0) := by
  ext k
  rcases k with _ | k
  · simp [coeff_zero_schurSzegoComp]
    ring
  · simp [coeff_schurSzegoComp]

theorem isPFPolynomial_binaryRunAnchor {n : ℕ} {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree ≤ n) :
    IsPFPolynomial (binaryRunAnchor n p) := by
  apply (isPFPolynomial_pathMatchingPolynomial (n + 1)).schurSzegoComp hp
  · rw [natDegree_pathMatchingPolynomial]
    cases n with
    | zero => simp
    | succ n =>
        have hlt : (n + 1 + 1) / 2 < n + 1 + 1 :=
          Nat.div_lt_self (by lia) (by norm_num)
        lia
  · exact hpdeg

/-- If the input has positive constant coefficient, then the Schur--Szegő
anchor has only simple roots.  The proof perturbs the simple path polynomial
in both constant directions and applies the strict Laguerre inequality to the
two resulting split compositions. -/
theorem binaryRunAnchor_hasSimpleRoots {n : ℕ} {p : ℝ[X]}
    (hn : 1 ≤ n) (hp : IsPFPolynomial p) (hpdeg : p.natDegree ≤ n)
    (hp0 : 0 < p.coeff 0) :
    HasSimpleRoots (binaryRunAnchor n p) := by
  let f := pathMatchingPolynomial (n + 1)
  let h := binaryRunAnchor n p
  have hfdeg : f.natDegree ≤ n := by
    dsimp [f]
    rw [natDegree_pathMatchingPolynomial]
    have hlt : (n + 1) / 2 < n + 1 :=
      Nat.div_lt_self (by lia) (by norm_num)
    lia
  have hfdeg0 : f.natDegree ≠ 0 := by
    dsimp [f]
    rw [natDegree_pathMatchingPolynomial]
    have : 1 ≤ (n + 1) / 2 := by lia
    lia
  obtain ⟨ε, hε, hε1, hfplus, hfminus⟩ :=
    exists_pos_pathMatchingPolynomial_add_C_splits hfdeg0
  let c := ε * p.coeff 0
  have hc : 0 < c := mul_pos hε hp0
  have hplusComp : (schurSzegoComp n (f + C ε) p).Splits := by
    rw [schurSzegoComp_comm]
    exact (schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial hp hpdeg
      (by simpa [f] using hfdeg) (by simpa [f] using hfplus)).resolve_left (by
        intro hz
        have hz0 : p.coeff 0 * (1 + ε) = 0 := by
          simpa only [f, coeff_zero_schurSzegoComp, coeff_add, coeff_C,
            coeff_zero_pathMatchingPolynomial, one_mul, coeff_zero, ite_true]
            using congrArg (fun q : ℝ[X] ↦ q.coeff 0) hz
        rcases mul_eq_zero.mp hz0 with hpzero | heq
        · exact hp0.ne' hpzero
        · linarith)
  have hminusComp : (schurSzegoComp n (f + C (-ε)) p).Splits := by
    rw [schurSzegoComp_comm]
    exact (schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial hp hpdeg
      (by
        rw [Polynomial.natDegree_add_C]
        exact hfdeg)
      (by simpa [f] using hfminus)).resolve_left (by
        intro hz
        have hz0 : p.coeff 0 * (1 + -ε) = 0 := by
          simpa only [f, coeff_zero_schurSzegoComp, coeff_add, coeff_C,
            coeff_zero_pathMatchingPolynomial, one_mul, coeff_zero, ite_true]
            using congrArg (fun q : ℝ[X] ↦ q.coeff 0) hz
        rcases mul_eq_zero.mp hz0 with hpzero | heq
        · exact hp0.ne' hpzero
        · linarith)
  have hplus : (h + C c).Splits := by
    rw [schurSzegoComp_add_C_left] at hplusComp
    simpa [h, f, c, binaryRunAnchor] using hplusComp
  have hminus : (h + C (-c)).Splits := by
    rw [schurSzegoComp_add_C_left] at hminusComp
    simpa [h, f, c, binaryRunAnchor] using hminusComp
  have hh0 : h.coeff 0 = p.coeff 0 := by
    simp [h, binaryRunAnchor, coeff_zero_schurSzegoComp]
  have hhne : h ≠ 0 := by
    intro hz
    have := congrArg (fun q : ℝ[X] ↦ q.coeff 0) hz
    rw [hh0] at this
    simp_all
  by_cases hhdeg : h.natDegree ≤ 1
  · exact hasSimpleRoots_of_natDegree_le_one hhne hhdeg
  intro r hr
  have hrh : h.eval r = 0 := by
    simpa [h, Polynomial.IsRoot.def] using hr
  have hmultpos : 0 < h.rootMultiplicity r :=
    (Polynomial.rootMultiplicity_pos hhne).2 hr
  by_contra hmult
  have hmultTwo : 1 < h.rootMultiplicity r := by lia
  have hderRoot : h.derivative.IsRoot r :=
    ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hhne).1 hmultTwo).2
  have hplusEval : (h + C c).eval r ≠ 0 := by
    simp [hrh, hc.ne']
  have hminusEval : (h + C (-c)).eval r ≠ 0 := by
    simp [hrh, hc.ne']
  have hplusStrict := deriv2_mul_lt_deriv_sq_at_non_root hplus
    (by simpa using (lt_of_not_ge hhdeg).le) hplusEval
  have hminusStrict := deriv2_mul_lt_deriv_sq_at_non_root hminus
    (by rw [Polynomial.natDegree_add_C]; exact (lt_of_not_ge hhdeg).le)
    hminusEval
  simp [Polynomial.IsRoot.def] at hderRoot
  simp [hrh, hderRoot] at hplusStrict hminusStrict
  linarith

theorem coeff_binaryRunAnchor_of_le {n k : ℕ} (p : ℝ[X]) (hk : k ≤ n) :
    (binaryRunAnchor n p).coeff k =
      (Nat.choose (n + 1 - k) k : ℝ) * p.coeff k /
        (Nat.choose n k : ℝ) := by
  rw [binaryRunAnchor, coeff_schurSzegoComp_of_le hk]
  by_cases hmid : k ≤ (n + 1) / 2
  · rw [coeff_pathMatchingPolynomial_of_le hmid]
  · rw [coeff_pathMatchingPolynomial_of_lt (Nat.lt_of_not_ge hmid)]
    have hchoose : Nat.choose (n + 1 - k) k = 0 :=
      Nat.choose_eq_zero_of_lt (by lia)
    simp [hchoose]

/-- Polynomial extension to scale zero of
`binaryRunTransform n (p(tX))` after replacing `X` by `X/t`.

The exponent is a natural subtraction; terms with `m < k` vanish because
`J_{n,m}` has degree at most `m`. -/
def rescaledBinaryRunDeformation (n : ℕ) (p : ℝ[X]) (t : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range ((n + 1) / 2 + 1),
    monomial k
      (∑ m ∈ Finset.range (n + 1),
        p.coeff m * (binaryRunPolynomial n m).coeff k * t ^ (m - k))

theorem coeff_rescaledBinaryRunDeformation_of_le
    {n k : ℕ} (p : ℝ[X]) (t : ℝ) (hk : k ≤ (n + 1) / 2) :
    (rescaledBinaryRunDeformation n p t).coeff k =
      ∑ m ∈ Finset.range (n + 1),
        p.coeff m * (binaryRunPolynomial n m).coeff k * t ^ (m - k) := by
  rw [rescaledBinaryRunDeformation, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single_of_mem k (by simpa using hk)]
  · simp
  · intro j hj hjk
    simp [Polynomial.coeff_monomial, hjk]

theorem coeff_rescaledBinaryRunDeformation_of_lt
    {n k : ℕ} (p : ℝ[X]) (t : ℝ) (hk : (n + 1) / 2 < k) :
    (rescaledBinaryRunDeformation n p t).coeff k = 0 := by
  rw [rescaledBinaryRunDeformation, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  have hjk : j ≠ k := by
    have hjle : j ≤ (n + 1) / 2 := by simpa using hj
    lia
  simp [Polynomial.coeff_monomial, hjk]

theorem natDegree_rescaledBinaryRunDeformation_le
    (n : ℕ) (p : ℝ[X]) (t : ℝ) :
    (rescaledBinaryRunDeformation n p t).natDegree ≤ (n + 1) / 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  exact coeff_rescaledBinaryRunDeformation_of_lt p t hk

theorem HasNonnegCoeffs.rescaledBinaryRunDeformation
    {n : ℕ} {p : ℝ[X]} (hp : HasNonnegCoeffs p) {t : ℝ}
    (ht : 0 ≤ t) :
    HasNonnegCoeffs (rescaledBinaryRunDeformation n p t) := by
  intro k
  by_cases hk : k ≤ (n + 1) / 2
  · rw [coeff_rescaledBinaryRunDeformation_of_le p t hk]
    apply Finset.sum_nonneg
    intro m hm
    exact mul_nonneg
      (mul_nonneg (hp m) (hasNonnegCoeffs_binaryRunPolynomial n m k))
      (pow_nonneg ht _)
  · rw [coeff_rescaledBinaryRunDeformation_of_lt p t
      (Nat.lt_of_not_ge hk)]

theorem natDegree_rescaledBinaryRunDeformation_eq
    {n : ℕ} (hn : 1 ≤ n) {p : ℝ[X]} (hp : HasNonnegCoeffs p)
    (hpTop : 0 < p.coeff ((n + 1) / 2)) {t : ℝ} (ht : 0 ≤ t) :
    (rescaledBinaryRunDeformation n p t).natDegree = (n + 1) / 2 := by
  apply le_antisymm (natDegree_rescaledBinaryRunDeformation_le n p t)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [coeff_rescaledBinaryRunDeformation_of_le p t le_rfl]
  apply ne_of_gt
  apply Finset.sum_pos'
  · intro m hm
    exact mul_nonneg
      (mul_nonneg (hp m) (hasNonnegCoeffs_binaryRunPolynomial n m _))
      (pow_nonneg ht _)
  · refine ⟨(n + 1) / 2, by simp; lia, ?_⟩
    rw [coeff_binaryRunPolynomial_self n ((n + 1) / 2) (by lia)]
    have hnum : 0 < (Nat.choose
        (n + 1 - (n + 1) / 2) ((n + 1) / 2) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by lia)
    have hden : 0 < (Nat.choose n ((n + 1) / 2) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by lia)
    simpa using mul_pos hpTop (div_pos hnum hden)

/-- Every coefficient of the rescaled family is a polynomial function of the
scale, including at scale zero. -/
theorem contDiff_coeff_rescaledBinaryRunDeformation
    (n : ℕ) (p : ℝ[X]) (k : ℕ) :
    ContDiff ℝ ∞ (fun t => (rescaledBinaryRunDeformation n p t).coeff k) := by
  by_cases hk : k ≤ (n + 1) / 2
  · simp_rw [coeff_rescaledBinaryRunDeformation_of_le p _ hk]
    fun_prop
  · simp_rw [coeff_rescaledBinaryRunDeformation_of_lt p _
      (Nat.lt_of_not_ge hk)]
    fun_prop

theorem contDiff_rescaledBinaryRunDeformation_eval_prod
    (n : ℕ) (p : ℝ[X]) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦
      (rescaledBinaryRunDeformation n p z.1).eval z.2) := by
  rw [show (fun z : ℝ × ℝ ↦
      (rescaledBinaryRunDeformation n p z.1).eval z.2) =
      fun z ↦ ∑ k ∈ Finset.range ((n + 1) / 2 + 1),
        (∑ m ∈ Finset.range (n + 1),
          p.coeff m * (binaryRunPolynomial n m).coeff k *
            z.1 ^ (m - k)) * z.2 ^ k by
    funext z
    rw [rescaledBinaryRunDeformation, Polynomial.eval_finsetSum]
    simp only [eval_monomial, Finset.sum_mul]]
  fun_prop

/-- Rescaling back by `X ↦ tX` recovers the ordinary binary-run deformation.
This identity is valid at `t = 0`; invertibility is only needed in the reverse
direction. -/
theorem rescaledBinaryRunDeformation_comp_scale
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ) :
    (rescaledBinaryRunDeformation n p t).comp (C t * X) =
      binaryRunTransform n (scalePolynomial t p) := by
  ext k
  rw [Polynomial.comp_C_mul_X_coeff]
  by_cases hk : k ≤ (n + 1) / 2
  · rw [coeff_rescaledBinaryRunDeformation_of_le p t hk,
      coeff_binaryRunTransform_eq_sum_range
        ((natDegree_scalePolynomial_le t p).trans hp), Finset.sum_mul]
    simp_rw [coeff_scalePolynomial]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hmk : m < k
    · rw [coeff_binaryRunPolynomial_eq_zero_of_lt hmk]
      simp
    · have hkm : k ≤ m := Nat.le_of_not_gt hmk
      calc
        p.coeff m * (binaryRunPolynomial n m).coeff k * t ^ (m - k) * t ^ k =
            p.coeff m * (binaryRunPolynomial n m).coeff k *
              (t ^ (m - k) * t ^ k) := by ring
        _ = p.coeff m * (binaryRunPolynomial n m).coeff k * t ^ m := by
          rw [← pow_add, Nat.sub_add_cancel hkm]
        _ = p.coeff m * t ^ m *
              (binaryRunPolynomial n m).coeff k := by ring
  · have hklt : (n + 1) / 2 < k := Nat.lt_of_not_ge hk
    rw [coeff_rescaledBinaryRunDeformation_of_lt p t hklt, zero_mul]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt <|
      lt_of_le_of_lt
        (natDegree_binaryRunTransform_le
          ((natDegree_scalePolynomial_le t p).trans hp)) hklt).symm

theorem natDegree_shiftedBinaryRunDeformation_eq
    {n : ℕ} (hn : 1 ≤ n) {p : ℝ[X]} (hp : HasNonnegCoeffs p)
    (hpdeg : p.natDegree ≤ n)
    (hpTop : 0 < p.coeff ((n + 1) / 2)) {t : ℝ} (ht : 0 < t) :
    (shiftedBinaryRunDeformation n p t).natDegree = (n + 1) / 2 := by
  have hrescaled := natDegree_rescaledBinaryRunDeformation_eq
    hn hp hpTop ht.le
  have hscale := rescaledBinaryRunDeformation_comp_scale hpdeg t
  have hordinary :
      (binaryRunTransform n (scalePolynomial t p)).natDegree =
        (n + 1) / 2 := by
    rw [← hscale, Polynomial.natDegree_comp, hrescaled]
    simp [ht.ne']
  rw [shiftedBinaryRunDeformation, Polynomial.natDegree_comp]
  simpa using hordinary

/-- The rescaled family specializes at zero to the Schur--Szegő anchor. -/
theorem rescaledBinaryRunDeformation_zero (n : ℕ) (p : ℝ[X]) :
    rescaledBinaryRunDeformation n p 0 = binaryRunAnchor n p := by
  ext k
  by_cases hk : k ≤ (n + 1) / 2
  · rw [coeff_rescaledBinaryRunDeformation_of_le p 0 hk]
    by_cases hk0 : k = 0
    · subst k
      rw [coeff_binaryRunAnchor_of_le p (Nat.zero_le n)]
      rw [Finset.sum_eq_single_of_mem 0 (by simp)]
      · simp
      · intro m hm hm0
        simp [coeff_zero_binaryRunPolynomial_of_pos n m
          (Nat.pos_of_ne_zero hm0)]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hkn : k ≤ n := by lia
      rw [coeff_binaryRunAnchor_of_le p hkn]
      rw [Finset.sum_eq_single_of_mem k (by simpa using hkn)]
      · rw [coeff_binaryRunPolynomial_self n k hkpos]
        simp
        ring
      · intro m hm hmk
        rcases lt_or_gt_of_ne hmk with hmklt | hmkgt
        · rw [coeff_binaryRunPolynomial_eq_zero_of_lt hmklt]
          simp
        · have hpow : m - k ≠ 0 := by lia
          rw [zero_pow hpow]
          ring
  · have hklt : (n + 1) / 2 < k := Nat.lt_of_not_ge hk
    rw [coeff_rescaledBinaryRunDeformation_of_lt p 0 hklt]
    by_cases hkn : k ≤ n
    · rw [binaryRunAnchor, coeff_schurSzegoComp_of_le hkn,
        coeff_pathMatchingPolynomial_of_lt (by simpa using hklt)]
      simp
    · rw [binaryRunAnchor,
        coeff_schurSzegoComp_eq_zero_of_lt (Nat.lt_of_not_ge hkn)]

end RealRooted
