module

public import RealRooted.Applications.OEIS.A286785
public import RealRooted.Tactic.RowInterlacing

set_option rr.row.explain true
set_option linter.style.longLine false

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

namespace A357613Downstream

/-- The exact downstream recurrence presentation of A357613. -/
def A357613 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C ((1 / ((-7 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (2 + (n : ℝ)) ^ 2)) * (-1 + (-3 / 2) * (n : ℝ))) * X +
        C ((1 / ((-7 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (2 + (n : ℝ)) ^ 2)) *
            ((-7 / 6) + (-5 / 3) * (n : ℝ))) * X ^ 2 +
        C ((1 / ((-7 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (2 + (n : ℝ)) ^ 2)) *
            ((-1 / 6) + (-1 / 6) * (n : ℝ))) * X ^ 3) *
        (A357613 n).derivative +
      (C ((1 / ((-7 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (2 + (n : ℝ)) ^ 2)) *
            (-17 + (-27 / 2) * (n : ℝ) + (9 / 2) * (2 + (n : ℝ)) ^ 2)) +
        C ((1 / ((-7 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (2 + (n : ℝ)) ^ 2)) *
            ((-46 / 3) + 4 * (2 + (n : ℝ)) ^ 2 + (-37 / 3) * (n : ℝ))) * X +
        C ((1 / ((-7 / 3) + (-5 / 3) * (n : ℝ) +
          (2 / 3) * (2 + (n : ℝ)) ^ 2)) *
            ((-2 / 3) + (-1 / 2) * (n : ℝ) + (1 / 6) * (2 + (n : ℝ)) ^ 2)) *
          X ^ 2) * A357613 n

/-- The exact downstream adjacent-interlacing statement for A357613. -/
theorem A357613_interlaces (n : ℕ) :
    RealRooted.Interlaces (A357613 n) (A357613 (n + 1)) := by
  rr_row_interlaces

/-- The exact downstream strict-interlacing statement for A357613. -/
theorem A357613_prec (n : ℕ) :
    RealRooted.StrictInterl (A357613 n) (A357613 (n + 1)) := by
  exact (A357613_interlaces n).toStrictInterl

end A357613Downstream

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

namespace A104978Downstream

/-- The exact downstream recurrence presentation of A104978. -/
def A104978 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C ((1 / 2) * (n : ℝ) *
          (1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2))) +
        C ((1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2)) *
            (3 + 5 * (n : ℝ))) * X +
        C ((1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2)) *
            (3 + (9 / 2) * (n : ℝ))) * X ^ 2) * (A104978 n).derivative +
      (C ((1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2)) *
          (-25 + 7 * (2 + (n : ℝ)) ^ 2 + (-37 / 2) * (n : ℝ))) +
        C ((1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2)) *
            (-33 + 9 * (2 + (n : ℝ)) ^ 2 + (-51 / 2) * (n : ℝ))) * X) *
        A104978 n

/-- The exact downstream adjacent-interlacing statement for A104978. -/
theorem A104978_interlaces (n : ℕ) :
    RealRooted.Interlaces (A104978 n) (A104978 (n + 1)) := by
  rr_row_interlaces

/-- The exact downstream strict-interlacing statement for A104978. -/
theorem A104978_prec (n : ℕ) :
    RealRooted.StrictInterl (A104978 n) (A104978 (n + 1)) := by
  exact (A104978_interlaces n).toStrictInterl

end A104978Downstream

namespace A108426Downstream

/-- The exact downstream recurrence presentation of A108426. -/
def A108426 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C ((1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2)) *
          (-3 + (-9 / 2) * (n : ℝ))) * X +
        C ((1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2)) *
            (-3 + -5 * (n : ℝ))) * X ^ 2 +
        C ((-1 / 2) * (n : ℝ) *
            (1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2))) * X ^ 3) *
        (A108426 n).derivative +
      (C ((1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2)) *
          (-51 + (-81 / 2) * (n : ℝ) + (27 / 2) * (2 + (n : ℝ)) ^ 2)) +
        C ((1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2)) *
            (-45 + 12 * (2 + (n : ℝ)) ^ 2 + (-71 / 2) * (n : ℝ))) * X +
        C ((1 / (-5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2)) *
            (-2 + (1 / 2) * (2 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) * X ^ 2) *
        A108426 n

/-- The exact downstream adjacent-interlacing statement for A108426. -/
theorem A108426_interlaces (n : ℕ) :
    RealRooted.Interlaces (A108426 n) (A108426 (n + 1)) := by
  rr_row_interlaces

/-- The exact downstream strict-interlacing statement for A108426. -/
theorem A108426_prec (n : ℕ) :
    RealRooted.StrictInterl (A108426 n) (A108426 (n + 1)) := by
  exact (A108426_interlaces n).toStrictInterl

end A108426Downstream
