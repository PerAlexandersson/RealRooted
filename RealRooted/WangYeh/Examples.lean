import RealRooted.WangYeh.TriangularMatrix
import Mathlib.Data.Nat.Choose.Basic

/-!
# Wang--Yeh recurrence examples

This module checks concrete coefficient recurrences against the generic
Wang--Yeh triangular-array criterion.
-/

namespace RealRooted

/-- Pascal's triangle satisfies the Wang--Yeh criterion with parameters
`(r,s,t,a,b,c) = (0,0,1,0,0,1)`, so every binomial row is a PF sequence. -/
theorem isPolyaFreqSeq_choose_row :
    ∀ n : ℕ, IsPolyaFreqSeq (fun k => (Nat.choose n k : ℝ)) := by
  intro n
  have hpf :=
    wangYeh_triangularMatrix_rows_pf
      (A := fun n k => (Nat.choose n k : ℝ))
      (r := 0) (s := 0) (t := 1)
      (a := 0) (b := 0) (c := 1)
      (hlower := by
        intro i j hij
        change (Nat.choose i j : ℝ) = 0
        exact_mod_cast Nat.choose_eq_zero_of_lt hij)
      (hbase := by norm_num)
      (hzero := by
        intro m
        simp)
      (hsucc := by
        intro m k
        simpa using
          congrArg (fun z : ℕ => (z : ℝ))
            (Nat.choose_succ_succ' m k))
      (hnonneg := by
        intro m k
        exact Nat.cast_nonneg (Nat.choose m k))
      (hrb := by norm_num)
      (hboundary := by norm_num)
      n
  simpa using hpf

end RealRooted
