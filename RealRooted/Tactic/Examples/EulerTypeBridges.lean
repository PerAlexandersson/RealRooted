module

public import RealRooted.Applications.OEIS.A286785
public import RealRooted.Tactic.RowInterlacing

/-!
# Exact downstream presentations of Euler-type bridges

These definitions and theorem statements reproduce the downstream OEIS files. In particular,
their recurrence coefficients have not been hand-normalized before calling the row tactic.
-/

@[expose] public section

open RealRooted Polynomial

noncomputable section

namespace A186370Downstream

/-- The exact downstream recurrence presentation of A186370. -/
def A186370 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C (1) * X + C (-1) * X ^ 3) * (A186370 n).derivative +
        (C (1) + C (1) * X + C (n : ℝ) * X ^ 2) * A186370 n

/-- The exact downstream adjacent-interlacing statement for A186370. -/
theorem A186370_interlaces (n : ℕ) :
    RealRooted.Interlaces (A186370 n) (A186370 (n + 1)) := by
  rr_row_interlaces

/-- The exact downstream strict-interlacing statement for A186370. -/
theorem A186370_prec (n : ℕ) :
    RealRooted.StrictInterl (A186370 n) (A186370 (n + 1)) := by
  exact (A186370_interlaces n).toStrictInterl

end A186370Downstream

namespace A286785Downstream

/-- The exact downstream recurrence presentation of A286785. -/
def A286785 : ℕ → ℝ[X]
  | 0 => 14 + 14 * X + 2 * X ^ 2
  | n + 1 =>
      (C ((1 / ((37 / 15) + (2 / 15) * (2 + (n : ℝ)) ^ 2 +
          (11 / 15) * (n : ℝ))) * ((1 / 10) + (1 / 30) * (n : ℝ))) +
        C ((1 / ((37 / 15) + (2 / 15) * (2 + (n : ℝ)) ^ 2 +
          (11 / 15) * (n : ℝ))) * ((11 / 10) + (7 / 30) * (n : ℝ))) * X +
        C ((1 / ((37 / 15) + (2 / 15) * (2 + (n : ℝ)) ^ 2 +
          (11 / 15) * (n : ℝ))) * ((-6 / 5) + (-4 / 15) * (n : ℝ))) * X ^ 2) *
        (A286785 n).derivative +
      (C ((1 / ((37 / 15) + (2 / 15) * (2 + (n : ℝ)) ^ 2 +
          (11 / 15) * (n : ℝ))) *
            ((69 / 10) + (1 / 2) * (2 + (n : ℝ)) ^ 2 + (11 / 5) * (n : ℝ))) +
        C ((1 / ((37 / 15) + (2 / 15) * (2 + (n : ℝ)) ^ 2 +
          (11 / 15) * (n : ℝ))) *
            ((19 / 5) + (2 / 5) * (2 + (n : ℝ)) ^ 2 + (7 / 5) * (n : ℝ))) * X) *
        A286785 n

/-- The exact downstream adjacent-interlacing statement for A286785. -/
theorem A286785_interlaces (n : ℕ) :
    RealRooted.Interlaces (A286785 n) (A286785 (n + 1)) := by
  rr_row_interlaces

/-- The exact downstream strict-interlacing statement for A286785. -/
theorem A286785_prec (n : ℕ) :
    RealRooted.StrictInterl (A286785 n) (A286785 (n + 1)) := by
  exact (A286785_interlaces n).toStrictInterl

end A286785Downstream
