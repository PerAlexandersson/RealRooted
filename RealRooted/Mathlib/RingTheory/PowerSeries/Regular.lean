import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Regular formal power series

This Mathlib-shaped shim records a coefficientwise regularity criterion for
formal power series over a commutative ring.
-/

open BigOperators

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- A formal power series is regular when its constant coefficient is
regular.  No domain hypothesis on the coefficient ring is needed. -/
theorem isRegular_of_isRegular_constantCoeff {f : PowerSeries R}
    (hf : IsRegular (constantCoeff f)) : IsRegular f := by
  have hleft : IsLeftRegular f := by
    intro g h hfg
    apply PowerSeries.ext
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hcoeff := congrArg (PowerSeries.coeff n) hfg
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff
      have hreflectg :
          (∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff k f * PowerSeries.coeff (n - k) g) =
            ∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff (n - k) f * PowerSeries.coeff k g := by
        rw [← Finset.sum_range_reflect
          (fun k => PowerSeries.coeff k f *
            PowerSeries.coeff (n - k) g) (n + 1)]
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        simp [hkn, Nat.sub_sub_self]
      have hreflecth :
          (∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff k f * PowerSeries.coeff (n - k) h) =
            ∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff (n - k) f * PowerSeries.coeff k h := by
        rw [← Finset.sum_range_reflect
          (fun k => PowerSeries.coeff k f *
            PowerSeries.coeff (n - k) h) (n + 1)]
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        simp [hkn, Nat.sub_sub_self]
      rw [hreflectg, hreflecth,
        Finset.sum_range_succ, Finset.sum_range_succ] at hcoeff
      have hprevious :
          (∑ k ∈ Finset.range n,
              PowerSeries.coeff (n - k) f * PowerSeries.coeff k g) =
            ∑ k ∈ Finset.range n,
              PowerSeries.coeff (n - k) f * PowerSeries.coeff k h := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k (Finset.mem_range.mp hk)]
      rw [hprevious] at hcoeff
      apply hf.left
      simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hcoeff
  exact ⟨hleft, fun g h hgf => hleft (by simpa [mul_comm] using hgf)⟩

end PowerSeries
