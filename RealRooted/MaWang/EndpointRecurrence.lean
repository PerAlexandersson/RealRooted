module

public import RealRooted.MaWang.EndpointTwoSided
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Pure-lag recurrences for endpoint derivative families

We extract homogeneous pure-lag recurrences from polynomial-denominator
identities.  The coefficient theorem below is the algebraic projection used
by the rational endpoint derivative families.
-/

public section

open Finset Polynomial

noncomputable section

namespace RealRooted

/-- A polynomial-denominator generating-function identity gives the
corresponding pure-lag recurrence after the numerator coefficients vanish. -/
theorem pureLag_eq_of_mul_generatingSeries_eq {R : Type*} [CommRing R]
    (P : ℕ → R) (D N : R[X]) (q n : ℕ)
    (hD0 : D.coeff 0 = 1) (hDdeg : D.natDegree = q)
    (hNdeg : N.natDegree < n + q)
    (hgen : (D : PowerSeries R) * PowerSeries.mk P = (N : PowerSeries R)) :
    P (n + q) =
      -∑ j ∈ range q, D.coeff (j + 1) * P (n + q - (j + 1)) := by
  have hcoeff := congrArg (PowerSeries.coeff (n + q)) hgen
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff
  simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk] at hcoeff
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hNdeg] at hcoeff
  have hsubset :
      (∑ j ∈ range (q + 1), D.coeff j * P (n + q - j)) =
        ∑ j ∈ range (n + q + 1), D.coeff j * P (n + q - j) := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by lia))
    intro j hjbig hjsmall
    have hj : q < j := by
      rw [Finset.mem_range] at hjbig
      rw [Finset.mem_range, not_lt] at hjsmall
      lia
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hDdeg.symm ▸ hj), zero_mul]
  rw [← hsubset, Finset.sum_range_succ'] at hcoeff
  rw [hD0, one_mul] at hcoeff
  linear_combination hcoeff

/-- Before the numerator vanishes, coefficient extraction gives its exact
defect from the homogeneous denominator recurrence. -/
theorem pureLag_add_sum_eq_coeff_of_mul_generatingSeries_eq
    {R : Type*} [CommRing R] (P : ℕ → R) (D N : R[X]) (q n : ℕ)
    (hD0 : D.coeff 0 = 1) (hDdeg : D.natDegree = q)
    (hgen : (D : PowerSeries R) * PowerSeries.mk P = (N : PowerSeries R)) :
    P (n + q) +
        ∑ j ∈ range q, D.coeff (j + 1) * P (n + q - (j + 1)) =
      N.coeff (n + q) := by
  have hcoeff := congrArg (PowerSeries.coeff (n + q)) hgen
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff
  simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk] at hcoeff
  have hsubset :
      (∑ j ∈ range (q + 1), D.coeff j * P (n + q - j)) =
        ∑ j ∈ range (n + q + 1), D.coeff j * P (n + q - j) := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by lia))
    intro j hjbig hjsmall
    have hj : q < j := by
      rw [Finset.mem_range] at hjbig
      rw [Finset.mem_range, not_lt] at hjsmall
      lia
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hDdeg.symm ▸ hj), zero_mul]
  rw [← hsubset, Finset.sum_range_succ'] at hcoeff
  rw [hD0, one_mul] at hcoeff
  simpa [add_comm] using hcoeff

/-- A numerator of degree below the denominator order gives the homogeneous
pure-lag recurrence from index zero. -/
theorem pureLag_all_of_mul_generatingSeries_eq {R : Type*} [CommRing R]
    (P : ℕ → R) (D N : R[X]) (q : ℕ)
    (hD0 : D.coeff 0 = 1) (hDdeg : D.natDegree = q)
    (hNdeg : N.natDegree < q)
    (hgen : (D : PowerSeries R) * PowerSeries.mk P = (N : PowerSeries R)) :
    ∀ n, P (n + q) =
      -∑ j ∈ range q, D.coeff (j + 1) * P (n + q - (j + 1)) := by
  intro n
  exact pureLag_eq_of_mul_generatingSeries_eq P D N q n hD0 hDdeg
    (hNdeg.trans_le (Nat.le_add_left q n)) hgen

/-- A numerator of degree at most the denominator order gives the homogeneous
pure-lag recurrence after discarding row zero. -/
theorem pureLag_tail_of_mul_generatingSeries_eq {R : Type*} [CommRing R]
    (P : ℕ → R) (D N : R[X]) (q : ℕ)
    (hD0 : D.coeff 0 = 1) (hDdeg : D.natDegree = q)
    (hNdeg : N.natDegree ≤ q)
    (hgen : (D : PowerSeries R) * PowerSeries.mk P = (N : PowerSeries R)) :
    ∀ n, P (n + 1 + q) =
      -∑ j ∈ range q,
        D.coeff (j + 1) * P (n + 1 + q - (j + 1)) := by
  intro n
  exact pureLag_eq_of_mul_generatingSeries_eq P D N q (n + 1) hD0 hDdeg
    (by lia) hgen

/-- If the numerator degree reaches the denominator order, shifting once gives
an all-index recurrence of declared order one larger. -/
theorem pureLag_succ_all_of_mul_generatingSeries_eq {R : Type*} [CommRing R]
    (P : ℕ → R) (D N : R[X]) (q : ℕ)
    (hD0 : D.coeff 0 = 1) (hDdeg : D.natDegree = q)
    (hNdeg : N.natDegree ≤ q)
    (hgen : (D : PowerSeries R) * PowerSeries.mk P = (N : PowerSeries R)) :
    ∀ n, P (n + (q + 1)) =
      -∑ j ∈ range (q + 1),
        D.coeff (j + 1) * P (n + (q + 1) - (j + 1)) := by
  intro n
  have htail := pureLag_tail_of_mul_generatingSeries_eq
    P D N q hD0 hDdeg hNdeg hgen n
  have htop : D.coeff (q + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (hDdeg.symm ▸ Nat.lt_succ_self q)
  rw [Finset.sum_range_succ, htop, zero_mul, add_zero]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- When numerator and denominator have the same degree and the numerator has
nonzero leading coefficient, the denominator recurrence fails at index zero. -/
theorem pureLag_zero_ne_of_mul_generatingSeries_eq {R : Type*} [CommRing R]
    (P : ℕ → R) (D N : R[X]) (q : ℕ)
    (hD0 : D.coeff 0 = 1) (hDdeg : D.natDegree = q)
    (hNdeg : N.natDegree = q) (hNlead : N.leadingCoeff ≠ 0)
    (hgen : (D : PowerSeries R) * PowerSeries.mk P = (N : PowerSeries R)) :
    P q ≠ -∑ j ∈ range q, D.coeff (j + 1) * P (q - (j + 1)) := by
  have hdefect := pureLag_add_sum_eq_coeff_of_mul_generatingSeries_eq
    P D N q 0 hD0 hDdeg hgen
  simp only [zero_add] at hdefect
  have hcoeff : N.coeff q = N.leadingCoeff := by
    rw [leadingCoeff, hNdeg]
  rw [hcoeff] at hdefect
  intro heq
  apply hNlead
  rw [heq] at hdefect
  simpa using hdefect.symm

/-- An all-index pure-lag recurrence gives a polynomial-denominator identity
whose numerator has degree strictly below the declared recurrence order. -/
theorem exists_natDegree_lt_and_mul_generatingSeries_eq_of_pureLag
    {R : Type*} [CommRing R] (P : ℕ → R) (Q : R[X]) (q : ℕ)
    (hq : 0 < q) (hQ0 : Q.coeff 0 = 1) (hQdeg : Q.natDegree ≤ q)
    (hrec : ∀ n, P (n + q) =
      -∑ j ∈ range q, Q.coeff (j + 1) * P (n + q - (j + 1))) :
    ∃ M : R[X], M.natDegree < q ∧
      (Q : PowerSeries R) * PowerSeries.mk P = (M : PowerSeries R) := by
  let F := (Q : PowerSeries R) * PowerSeries.mk P
  let M := PowerSeries.trunc q F
  have hdegree : M.natDegree < q := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hq
    simpa [M, Nat.add_comm] using PowerSeries.natDegree_trunc_lt F r
  refine ⟨M, hdegree, ?_⟩
  change F = (M : PowerSeries R)
  ext i
  by_cases hi : i < q
  · exact (PowerSeries.coeff_coe_trunc_of_lt (f := F) hi).symm
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
    have hcoeff : PowerSeries.coeff (q + n) F = 0 := by
      change PowerSeries.coeff (q + n)
        ((Q : PowerSeries R) * PowerSeries.mk P) = 0
      rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk]
      have hsubset :
          (∑ j ∈ range (q + 1), Q.coeff j * P (q + n - j)) =
            ∑ j ∈ range (q + n + 1), Q.coeff j * P (q + n - j) := by
        apply Finset.sum_subset (Finset.range_subset_range.mpr (by lia))
        intro j hjbig hjsmall
        have hj : q < j := by
          rw [Finset.mem_range] at hjbig
          rw [Finset.mem_range, not_lt] at hjsmall
          lia
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hQdeg.trans_lt hj), zero_mul]
      rw [← hsubset, Finset.sum_range_succ', hQ0, one_mul]
      rw [add_comm q n]
      simp only [Nat.sub_zero]
      rw [hrec n]
      simp
    rw [hcoeff]
    simp [M, PowerSeries.coeff_trunc, Nat.not_lt.mpr (Nat.le_add_right q n)]

/-- An eventual pure-lag recurrence gives a polynomial-denominator identity;
the numerator is supported before the recurrence's first output index. -/
theorem exists_natDegree_lt_add_and_mul_generatingSeries_eq_of_pureLag_from
    {R : Type*} [CommRing R] (P : ℕ → R) (Q : R[X]) (q n₀ : ℕ)
    (hq : 0 < q) (hQ0 : Q.coeff 0 = 1) (hQdeg : Q.natDegree ≤ q)
    (hrec : ∀ n, P (n₀ + n + q) =
      -∑ j ∈ range q, Q.coeff (j + 1) * P (n₀ + n + q - (j + 1))) :
    ∃ M : R[X], M.natDegree < n₀ + q ∧
      (Q : PowerSeries R) * PowerSeries.mk P = (M : PowerSeries R) := by
  let F := (Q : PowerSeries R) * PowerSeries.mk P
  let M := PowerSeries.trunc (n₀ + q) F
  have hcut : 0 < n₀ + q := by lia
  have hdegree : M.natDegree < n₀ + q := by
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hcut
    rw [hr]
    simpa [M, hr, Nat.add_comm] using PowerSeries.natDegree_trunc_lt F r
  refine ⟨M, hdegree, ?_⟩
  change F = (M : PowerSeries R)
  ext i
  by_cases hi : i < n₀ + q
  · exact (PowerSeries.coeff_coe_trunc_of_lt (f := F) hi).symm
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
    have hcoeff : PowerSeries.coeff (n₀ + q + n) F = 0 := by
      change PowerSeries.coeff (n₀ + q + n)
        ((Q : PowerSeries R) * PowerSeries.mk P) = 0
      rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk]
      have hsubset :
          (∑ j ∈ range (q + 1), Q.coeff j * P (n₀ + q + n - j)) =
            ∑ j ∈ range (n₀ + q + n + 1),
              Q.coeff j * P (n₀ + q + n - j) := by
        apply Finset.sum_subset (Finset.range_subset_range.mpr (by lia))
        intro j hjbig hjsmall
        have hj : q < j := by
          rw [Finset.mem_range] at hjbig
          rw [Finset.mem_range, not_lt] at hjsmall
          lia
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hQdeg.trans_lt hj), zero_mul]
      rw [← hsubset, Finset.sum_range_succ', hQ0, one_mul]
      have hindex : n₀ + q + n = n₀ + n + q := by lia
      rw [hindex]
      simp only [Nat.sub_zero]
      rw [hrec n]
      simp
    rw [hcoeff]
    simp [M, PowerSeries.coeff_trunc,
      Nat.not_lt.mpr (Nat.le_add_right (n₀ + q) n)]

private theorem denominator_dvd_of_coprime_mul_generatingSeries_eq
    {K : Type*} [Field K] (P : ℕ → K) (D N Q M : K[X])
    (hcoprime : IsCoprime D N)
    (hDgen : (D : PowerSeries K) * PowerSeries.mk P = (N : PowerSeries K))
    (hQgen : (Q : PowerSeries K) * PowerSeries.mk P = (M : PowerSeries K)) : D ∣ Q := by
  have hcrossPowerSeries :
      ((D * M : K[X]) : PowerSeries K) = ((Q * N : K[X]) : PowerSeries K) := by
    calc
      ((D * M : K[X]) : PowerSeries K) =
          (D : PowerSeries K) * (M : PowerSeries K) := by simp
      _ = (D : PowerSeries K) *
          ((Q : PowerSeries K) * PowerSeries.mk P) := by rw [hQgen]
      _ = (Q : PowerSeries K) *
          ((D : PowerSeries K) * PowerSeries.mk P) := by ring
      _ = (Q : PowerSeries K) * (N : PowerSeries K) := by rw [hDgen]
      _ = ((Q * N : K[X]) : PowerSeries K) := by simp
  have hcross : D * M = Q * N :=
    Polynomial.coe_injective K hcrossPowerSeries
  have hDdvd : D ∣ Q * N := ⟨M, hcross.symm⟩
  exact hcoprime.dvd_of_dvd_mul_right hDdvd

/-- In a coprime polynomial-denominator identity, every other polynomial
denominator has at least the degree of the reduced denominator. -/
theorem natDegree_le_of_coprime_mul_generatingSeries_eq
    {K : Type*} [Field K] (P : ℕ → K) (D N Q M : K[X])
    (hcoprime : IsCoprime D N) (hQ0 : Q.coeff 0 = 1)
    (hDgen : (D : PowerSeries K) * PowerSeries.mk P = (N : PowerSeries K))
    (hQgen : (Q : PowerSeries K) * PowerSeries.mk P = (M : PowerSeries K)) :
    D.natDegree ≤ Q.natDegree := by
  have hDdvdQ := denominator_dvd_of_coprime_mul_generatingSeries_eq
    P D N Q M hcoprime hDgen hQgen
  have hQne : Q ≠ 0 := by
    intro hQ
    rw [hQ, coeff_zero] at hQ0
    exact zero_ne_one hQ0
  exact Polynomial.natDegree_le_of_dvd hDdvdQ hQne

/-- If the reduced numerator has full denominator degree, every normalized
denominator making the generating series proper has strictly larger degree. -/
theorem natDegree_lt_of_full_coprime_mul_generatingSeries_eq
    {K : Type*} [Field K] (P : ℕ → K) (D N Q M : K[X]) (q : ℕ)
    (hcoprime : IsCoprime D N) (hD0 : D.coeff 0 = 1)
    (hQ0 : Q.coeff 0 = 1) (hDdeg : D.natDegree = q)
    (hNdeg : N.natDegree = q) (hMdeg : M.natDegree < Q.natDegree)
    (hDgen : (D : PowerSeries K) * PowerSeries.mk P = (N : PowerSeries K))
    (hQgen : (Q : PowerSeries K) * PowerSeries.mk P = (M : PowerSeries K)) :
    q < Q.natDegree := by
  have hle : q ≤ Q.natDegree := by
    rw [← hDdeg]
    exact natDegree_le_of_coprime_mul_generatingSeries_eq
      P D N Q M hcoprime hQ0 hDgen hQgen
  apply hle.lt_of_ne
  intro hdegree
  have hQdeg : Q.natDegree = q := hdegree.symm
  have hDdvdQ := denominator_dvd_of_coprime_mul_generatingSeries_eq
    P D N Q M hcoprime hDgen hQgen
  obtain ⟨C, hQC⟩ := hDdvdQ
  have hDne : D ≠ 0 := by
    intro hD
    rw [hD, coeff_zero] at hD0
    exact zero_ne_one hD0
  have hQne : Q ≠ 0 := by
    intro hQ
    rw [hQ, coeff_zero] at hQ0
    exact zero_ne_one hQ0
  have hCne : C ≠ 0 := by
    intro hC
    apply hQne
    rw [hQC, hC, mul_zero]
  have hCdeg : C.natDegree = 0 := by
    have hmul := Polynomial.natDegree_mul hDne hCne
    rw [← hQC, hQdeg, hDdeg] at hmul
    lia
  have hC0 : C.coeff 0 = 1 := by
    have hcoeff := congrArg (fun f : K[X] => f.coeff 0) hQC
    rw [mul_coeff_zero, hQ0, hD0, one_mul] at hcoeff
    exact hcoeff.symm
  have hC : C = 1 := by
    rw [eq_C_of_natDegree_eq_zero hCdeg, hC0, C_1]
  have hQD : Q = D := by
    rw [hQC, hC, mul_one]
  rw [hQD] at hQgen
  have hMNPowerSeries : (M : PowerSeries K) = (N : PowerSeries K) :=
    hQgen.symm.trans hDgen
  have hMN : M = N := Polynomial.coe_injective K hMNPowerSeries
  rw [hMN, hNdeg, ← hdegree] at hMdeg
  exact Nat.lt_irrefl q hMdeg

/-- A coprime polynomial-denominator identity gives a lower bound on every
all-index pure-lag recurrence order. -/
theorem le_order_of_coprime_mul_generatingSeries_eq_of_pureLag
    {K : Type*} [Field K] (P : ℕ → K) (D N Q : K[X]) (q m : ℕ)
    (hm : 0 < m) (hcoprime : IsCoprime D N) (hDdeg : D.natDegree = q)
    (hQ0 : Q.coeff 0 = 1) (hQdeg : Q.natDegree ≤ m)
    (hDgen : (D : PowerSeries K) * PowerSeries.mk P = (N : PowerSeries K))
    (hrec : ∀ n, P (n + m) =
      -∑ j ∈ range m, Q.coeff (j + 1) * P (n + m - (j + 1))) :
    q ≤ m := by
  obtain ⟨M, _, hQgen⟩ :=
    exists_natDegree_lt_and_mul_generatingSeries_eq_of_pureLag
      P Q m hm hQ0 hQdeg hrec
  rw [← hDdeg]
  exact (natDegree_le_of_coprime_mul_generatingSeries_eq
    P D N Q M hcoprime hQ0 hDgen hQgen).trans hQdeg

/-- A coprime full-degree numerator rules out every all-index pure-lag
recurrence whose declared order is the reduced denominator degree. -/
theorem not_exists_pureLag_of_full_coprime_mul_generatingSeries_eq
    {K : Type*} [Field K] (P : ℕ → K) (D N : K[X]) (q : ℕ)
    (hq : 0 < q) (hcoprime : IsCoprime D N) (hD0 : D.coeff 0 = 1)
    (hDdeg : D.natDegree = q) (hNdeg : N.natDegree = q)
    (hDgen : (D : PowerSeries K) * PowerSeries.mk P = (N : PowerSeries K)) :
    ¬∃ Q : K[X], Q.coeff 0 = 1 ∧ Q.natDegree ≤ q ∧
      ∀ n, P (n + q) =
        -∑ j ∈ range q, Q.coeff (j + 1) * P (n + q - (j + 1)) := by
  rintro ⟨Q, hQ0, hQdeg, hrec⟩
  obtain ⟨M, hMdeg, hQgen⟩ :=
    exists_natDegree_lt_and_mul_generatingSeries_eq_of_pureLag
      P Q q hq hQ0 hQdeg hrec
  have hQeq : Q.natDegree = q := by
    apply le_antisymm hQdeg
    rw [← hDdeg]
    exact natDegree_le_of_coprime_mul_generatingSeries_eq
      P D N Q M hcoprime hQ0 hDgen hQgen
  have hMdegQ : M.natDegree < Q.natDegree := by
    rw [hQeq]
    exact hMdeg
  have hlt := natDegree_lt_of_full_coprime_mul_generatingSeries_eq
    P D N Q M q hcoprime hD0 hQ0 hDdeg hNdeg hMdegQ hDgen hQgen
  exact (Nat.not_lt_of_ge hQdeg) hlt

end RealRooted
