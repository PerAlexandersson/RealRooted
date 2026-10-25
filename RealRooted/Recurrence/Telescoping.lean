module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

/-!
# Checked finite-sum certificates

This file isolates the finite telescoping step in a hypergeometric certificate proof.  The
certificate identity and its two boundary values remain ordinary Lean proof obligations.
-/

@[expose] public section

namespace RealRooted

open scoped BigOperators

/-- A pointwise forward-difference certificate with zero boundary values proves that a finite
sum vanishes. -/
theorem sum_range_eq_zero_of_certificate {A : Type*} [AddCommGroup A]
    (summand certificate : ℕ → A) (N : ℕ)
    (step : ∀ k < N, summand k = certificate (k + 1) - certificate k)
    (certificate_zero : certificate 0 = 0) (certificate_end : certificate N = 0) :
    ∑ k ∈ Finset.range N, summand k = 0 := by
  have telescope := Finset.sum_range_sub certificate N
  calc
    ∑ k ∈ Finset.range N, summand k =
        ∑ k ∈ Finset.range N, (certificate (k + 1) - certificate k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      exact step k (Finset.mem_range.mp hk)
    _ = certificate N - certificate 0 := telescope
    _ = 0 := by rw [certificate_zero, certificate_end, sub_self]

/-- A checked certificate proves that a finite linear combination of finite sums vanishes.

The hypothesis `step` is the Zeilberger identity.  In applications it is discharged from a
supplied rational certificate by kernel-checked normalization (`field_simp` and `ring`), while
`certificate_zero` and `certificate_end` explicitly check the support boundary.
-/
theorem sum_mul_sum_range_eq_zero_of_certificate {A : Type*} [CommRing A] {r N : ℕ}
    (coeff : Fin r → A) (summand : Fin r → ℕ → A) (certificate : ℕ → A)
    (step : ∀ k < N,
      ∑ i : Fin r, coeff i * summand i k = certificate (k + 1) - certificate k)
    (certificate_zero : certificate 0 = 0) (certificate_end : certificate N = 0) :
    ∑ i : Fin r, coeff i * ∑ k ∈ Finset.range N, summand i k = 0 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact sum_range_eq_zero_of_certificate
    (fun k ↦ ∑ i : Fin r, coeff i * summand i k) certificate N step
      certificate_zero certificate_end

end RealRooted
