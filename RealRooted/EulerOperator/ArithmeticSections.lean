module

public import RealRooted.EulerOperator.RootCounting
public import Mathlib.Algebra.Polynomial.Expand
import RealRooted.Mathlib.Algebra.Polynomial.Expand.PositiveRoots
import RealRooted.Mathlib.Algebra.Polynomial.Expand.Contract
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Finite arithmetic-section approximants

Applying polar Euler factors at the positive integers not divisible by a
stride annihilates the unwanted coefficients. The positive-root estimate
then proves that the compressed polynomial splits. This is the finite
root-counting stage of Pólya's arithmetic-section argument.
-/

@[expose] public section

open Polynomial Finset

namespace RealRooted

/-- Positive integers through `N` which are not divisible by the stride. -/
def arithmeticPolarParameters (r N : ℕ) : Multiset ℕ :=
  ((Ioc 0 N).filter fun a => ¬r ∣ a).val

@[simp] theorem mem_arithmeticPolarParameters (r N a : ℕ) :
    a ∈ arithmeticPolarParameters r N ↔ 0 < a ∧ a ≤ N ∧ ¬r ∣ a := by
  simp [arithmeticPolarParameters, and_assoc]

theorem zero_notMem_arithmeticPolarParameters (r N : ℕ) :
    0 ∉ arithmeticPolarParameters r N := by simp

/-- Among the first `N` positive integers, precisely `N - N / r` are not
multiples of `r`. This also covers `r = 0`. -/
theorem card_arithmeticPolarParameters (r N : ℕ) :
    (arithmeticPolarParameters r N).card = N - N / r := by
  have h := (Ioc 0 N).card_filter_add_card_filter_not (fun a => r ∣ a)
  rw [Nat.Ioc_filter_dvd_card_eq_div] at h
  simp only [Nat.card_Ioc, Nat.sub_zero] at h
  change ((Ioc 0 N).filter fun a => ¬r ∣ a).card = N - N / r
  lia

/-- Truncating the arithmetic parameter multiset truncates its upper bound. -/
theorem filter_arithmeticPolarParameters_le (r : ℕ) {m N : ℕ} (hm : m ≤ N) :
    (arithmeticPolarParameters r N).filter (· ≤ m) = arithmeticPolarParameters r m := by
  change (((Ioc 0 N).filter (fun a => ¬r ∣ a)).filter (· ≤ m)).val =
    ((Ioc 0 m).filter (fun a => ¬r ∣ a)).val
  congr 1
  ext a
  simp only [mem_filter, mem_Ioc]
  exact ⟨fun h => ⟨⟨h.1.1.1, h.2⟩, h.1.2⟩,
    fun h => ⟨⟨⟨h.1.1, h.1.2.trans hm⟩, h.2⟩, h.1.2⟩⟩

/-- A parameter equal to the coefficient index annihilates that coefficient. -/
theorem coeff_polarThetaProduct_eq_zero_of_mem {s : Multiset ℕ} {p : ℝ[X]} {k : ℕ}
    (hk : k ∈ s) : (polarThetaProduct s p).coeff k = 0 := by
  rw [coeff_polarThetaProduct]
  have hz : (s.map fun a : ℕ => (a : ℝ) - k).prod = 0 := by
    rw [Multiset.prod_eq_zero_iff, Multiset.mem_map]
    exact ⟨k, hk, sub_self _⟩
  rw [hz, zero_mul]

/-- Enough arithmetic polar factors leave only coefficient indices divisible
by the stride. -/
theorem coeff_arithmetic_polarThetaProduct_eq_zero {p : ℝ[X]} (r : ℕ) {N : ℕ}
    (hp : p.natDegree ≤ N) (k : ℕ) (hk : ¬r ∣ k) :
    (polarThetaProduct (arithmeticPolarParameters r N) p).coeff k = 0 := by
  by_cases hkn : k ≤ N
  · apply coeff_polarThetaProduct_eq_zero_of_mem
    exact (mem_arithmeticPolarParameters r N k).mpr
      ⟨Nat.pos_of_ne_zero (fun h => hk (h ▸ dvd_zero r)), hkn, hk⟩
  · apply coeff_eq_zero_of_natDegree_lt
    exact (natDegree_polarThetaProduct_le _ _).trans_lt (hp.trans_lt (Nat.lt_of_not_ge hkn))

/-- Compressing a reflected PF polynomial after applying the arithmetic
polar factors gives a polynomial which splits over the reals. -/
theorem IsPFPolynomial.contract_arithmetic_polarThetaProduct_splits
    {p : ℝ[X]} (hp : IsPFPolynomial p) (h0 : p.coeff 0 ≠ 0)
    {r N : ℕ} (hr : r ≠ 0) (hN : p.natDegree ≤ N) :
    (contract r (RealRooted.polarThetaProduct
      (arithmeticPolarParameters r N) (p.comp (-X)))).Splits := by
  let q := RealRooted.polarThetaProduct (arithmeticPolarParameters r N) (p.comp (-X))
  have he : expand ℝ r (contract r q) = q :=
    expand_contract_of_coeff_eq_zero hr
      (coeff_arithmetic_polarThetaProduct_eq_zero r (by simpa using hN))
  have hbound := hp.natDegree_le_card_pos_roots_polarThetaProduct h0
    (zero_notMem_arithmeticPolarParameters r N)
  rw [filter_arithmeticPolarParameters_le r hN, card_arithmeticPolarParameters] at hbound
  have hdiv : p.natDegree / r ≤ p.natDegree := Nat.div_le_self _ _
  have hcount : p.natDegree / r ≤ (q.roots.filter (0 < ·)).card := by
    change p.natDegree ≤ (q.roots.filter (0 < ·)).card +
      (p.natDegree - p.natDegree / r) at hbound
    lia
  apply splits_of_natDegree_le_card_pos_roots_expand hr
  rw [he]
  exact (natDegree_contract_le_div q hr).trans
    ((Nat.div_le_div_right (by
      simpa [q] using natDegree_polarThetaProduct_le (arithmeticPolarParameters r N)
        (p.comp (-X)))).trans hcount)

end RealRooted
