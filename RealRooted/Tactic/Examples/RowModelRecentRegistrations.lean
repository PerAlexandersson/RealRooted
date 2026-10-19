import RealRooted.Applications.OEIS.A330798
import RealRooted.Tactic.Examples.EulerTypeBridges
import RealRooted.Tactic.Examples.OEIS.DegreeTwoGamma
import RealRooted.Tactic.Examples.OEIS.DegreeTwoSplits
import RealRooted.Tactic.Examples.RowParityFactorization

/-!
# Regression examples for recently registered row models

These are the literal downstream recurrence presentations.  Each proof uses
the default row tactic, so the examples test registry dispatch and its exact-row filter.
-/

open RealRooted Polynomial

noncomputable section

namespace RowModelRecentRegistrations

namespace A104978Model

/-- Consecutive-row transfer for the literal downstream A104978 presentation.
The third advertised row keeps the registry filter ahead of models sharing `1, 1 + X`. -/
@[rr_row_model]
theorem a104978_interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (_hone : P 1 = 1 + X)
    (_htwo : P 2 = 2 + 5 * X + 3 * X ^ 2)
    (hrec : ∀ n : ℕ, P (n + 1) =
      ((C (((1 / 2) * (n : ℝ) *
          (1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))))) +
        C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (3 + (5 * (n : ℝ))))) * X +
        C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (3 + ((9 / 2) * (n : ℝ))))) * X ^ 2)) * (P n).derivative +
      ((C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (-25 + (7 * ((2 + (n : ℝ))) ^ (2)) + ((-37 / 2) * (n : ℝ))))) +
        C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (-33 + (9 * ((2 + (n : ℝ))) ^ (2)) + ((-51 / 2) * (n : ℝ))))) * X)) *
        P n)
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_one_recurrence
    (fun (n : ℕ) (p : ℝ[X]) =>
      ((C (((1 / 2) * (n : ℝ) *
          (1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))))) +
        C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (3 + (5 * (n : ℝ))))) * X +
        C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (3 + ((9 / 2) * (n : ℝ))))) * X ^ 2)) * p.derivative +
      ((C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (-25 + (7 * ((2 + (n : ℝ))) ^ (2)) + ((-37 / 2) * (n : ℝ))))) +
        C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (-33 + (9 * ((2 + (n : ℝ))) ^ (2)) + ((-51 / 2) * (n : ℝ))))) * X)) *
        p)
    (hzero.trans (show (1 : ℝ[X]) = A104978Downstream.A104978 0 by rfl)) hrec (fun _ => rfl)
  rw [heq n, heq (n + 1)]
  exact A104978Downstream.A104978_interlaces n

end A104978Model

namespace HA049325

/-- The OEIS A049325 polynomial sequence, given by a literal fourth-order recurrence. -/
def A049325 : ℕ → ℝ[X]
  | 0 => 16 + 12 * X + X ^ 2
  | 1 => 16 + 68 * X + 18 * X ^ 2 + X ^ 3
  | 2 => 224 * X + 156 * X ^ 2 + 24 * X ^ 3 + X ^ 4
  | 3 => 448 * X + 840 * X ^ 2 + 280 * X ^ 3 + 30 * X ^ 4 + X ^ 5
  | n + 4 => (X) * A049325 (n + 3) + ((6 * X)) * A049325 (n + 2) +
      ((16 * X)) * A049325 (n + 1) + ((16 * X)) * A049325 n

theorem A049325_splits (n : ℕ) : (A049325 n).Splits := by
  rr_row_splits

theorem A049325_interlaces (n : ℕ) :
    RealRooted.Interlaces (A049325 n) (A049325 (n + 1)) := by
  rr_row_interlaces

end HA049325

namespace HA082649

/-- The OEIS A082649 polynomial sequence, given by a literal third-order recurrence. -/
def A082649 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 4 + 4 * X
  | 2 => 16 + 24 * X + 9 * X ^ 2
  | n + 3 => ((4 + (3 * X))) * A082649 (n + 2) +
      (((-4 * X) + (-3 * (X) ^ (2)))) * A082649 (n + 1) +
      ((X) ^ (3)) * A082649 n

theorem A082649_splits (n : ℕ) : (A082649 n).Splits := by
  rr_row_splits

end HA082649

namespace HA099605

/-- The OEIS A099605 polynomial sequence, given by a literal fourth-order recurrence. -/
def A099605 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + 2 * X
  | 2 => 1 + 5 * X + 4 * X ^ 2
  | 3 => 4 + 16 * X + 20 * X ^ 2 + 8 * X ^ 3
  | n + 4 => ((2 + (4 * (X) ^ (2)) + (6 * X))) * A099605 (n + 2) +
      ((-1 + (-1 * (X) ^ (2)) + (-2 * X))) * A099605 n

theorem A099605_splits (n : ℕ) : (A099605 n).Splits := by
  rr_row_splits

end HA099605

namespace HA101842

/-- The OEIS A101842 polynomial sequence, given by a literal first-order derivative recurrence. -/
def A101842 : ℕ → ℝ[X]
  | 0 => 1 + X
  | n + 1 => ((C (1) * X + C (-1) * X ^ 3)) * (A101842 n).derivative +
      ((C (1) + C (1) * X + C ((2 + (2 * (n : ℝ)))) * X ^ 2)) * A101842 n

theorem A101842_splits (n : ℕ) : (A101842 n).Splits := by
  rr_row_splits

end HA101842

namespace HA104978

/-- The OEIS A104978 polynomial sequence, given by a literal first-order derivative recurrence. -/
def A104978 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      ((C (((1 / 2) * (n : ℝ) *
          (1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))))) +
        C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (3 + (5 * (n : ℝ))))) * X +
        C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (3 + ((9 / 2) * (n : ℝ))))) * X ^ 2)) * (A104978 n).derivative +
      ((C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (-25 + (7 * ((2 + (n : ℝ))) ^ (2)) + ((-37 / 2) * (n : ℝ))))) +
        C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (-33 + (9 * ((2 + (n : ℝ))) ^ (2)) + ((-51 / 2) * (n : ℝ))))) * X)) *
        A104978 n

theorem A104978_splits (n : ℕ) : (A104978 n).Splits := by
  rr_row_splits

theorem A104978_interlaces (n : ℕ) :
    RealRooted.Interlaces (A104978 n) (A104978 (n + 1)) := by
  rr_row_interlaces

end HA104978

namespace HA156308

/-- The OEIS A156308 polynomial sequence, given by a literal third-order recurrence. -/
def A156308 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 4 + X
  | 2 => 9 + 6 * X + X ^ 2
  | n + 3 => ((3 + X)) * A156308 (n + 2) +
      ((-3 + (-1 * X))) * A156308 (n + 1) + (1) * A156308 n

theorem A156308_splits (n : ℕ) : (A156308 n).Splits := by
  rr_row_splits

end HA156308

namespace HA165891

/-- The OEIS A165891 polynomial sequence, given by a literal first-order derivative recurrence. -/
def A165891 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => ((C (1) * X + C (-1) * X ^ 3)) * (A165891 n).derivative +
      ((C (1) + C (2) * X + C ((1 + (2 * (n : ℝ)))) * X ^ 2)) * A165891 n

theorem A165891_splits (n : ℕ) : (A165891 n).Splits := by
  rr_row_splits

end HA165891

namespace HA266326

/-- The OEIS A266326 polynomial sequence, given by a literal first-order derivative recurrence. -/
def A266326 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => ((C (1) * X ^ 2 + C (2) * X ^ 3)) * (A266326 n).derivative +
      ((C ((1 + (-2 * (n : ℝ)))) * X + C ((1 + (-4 * (n : ℝ)))) * X ^ 2)) *
        A266326 n

theorem A266326_splits (n : ℕ) : (A266326 n).Splits := by
  rr_row_splits

end HA266326

namespace HA268647

/-- The OEIS A268647 polynomial sequence, given by a literal second-order recurrence. -/
def A268647 : ℕ → ℝ[X]
  | 0 => X
  | 1 => 2 + 5 * X + 4 * X ^ 2 + X ^ 3
  | n + 2 =>
      ((C ((-12 + (-6 * (n : ℝ)) + (4 * ((3 + (n : ℝ))) ^ (2)))) +
        C ((4 + (3 * (n : ℝ)))) * X + C (1) * X ^ 2)) * A268647 (n + 1) +
      ((C ((68 + (-8 * ((3 + (n : ℝ))) ^ (2)) + (36 * (n : ℝ)))) +
        C ((20 + (-14 * ((3 + (n : ℝ))) ^ (2)) + (-6 * (n : ℝ)) +
          (4 * ((3 + (n : ℝ))) ^ (3)))) * X +
        C ((-26 + (-5 * (n : ℝ)) + (4 * ((3 + (n : ℝ))) ^ (2)))) * X ^ 2 +
        C ((4 + (n : ℝ))) * X ^ 3)) * A268647 n

theorem A268647_splits (n : ℕ) : (A268647 n).Splits := by
  rr_row_splits

end HA268647

namespace HA297191

/-- The OEIS A297191 polynomial sequence, given by a literal second-order recurrence. -/
def A297191 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X + X ^ 2
  | n + 2 => ((1 + (X) ^ (2) + (4 * X))) * A297191 (n + 1) +
      ((-1 * (X) ^ (2))) * A297191 n

theorem A297191_splits (n : ℕ) : (A297191 n).Splits := by
  rr_row_splits

end HA297191

namespace HA334009

/-- The OEIS A334009 polynomial sequence, given by a literal third-order recurrence. -/
def A334009 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 4 + 4 * X
  | 2 => 9 + 24 * X + 16 * X ^ 2
  | n + 3 => ((3 + (4 * X))) * A334009 (n + 2) +
      ((-3 + (-4 * X))) * A334009 (n + 1) + (1) * A334009 n

theorem A334009_splits (n : ℕ) : (A334009 n).Splits := by
  rr_row_splits

end HA334009

namespace HA394446

/-- The OEIS A394446 polynomial sequence, given by a literal second-order derivative recurrence. -/
def A394446 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X + X ^ 2
  | n + 2 =>
      ((C ((-4 * (1 / ((4 + (n : ℝ)))))) * X +
        C ((-6 * (1 / ((4 + (n : ℝ)))))) * X ^ 2 +
        C ((-2 * (1 / ((4 + (n : ℝ)))))) * X ^ 3)) *
          (A394446 (n + 1)).derivative +
      ((C (((1 / ((4 + (n : ℝ)))) * (7 + (4 * (n : ℝ))))) +
        C (((1 / ((4 + (n : ℝ)))) * (22 + (13 * (n : ℝ))))) * X +
        C (((1 / ((4 + (n : ℝ)))) * (8 + (5 * (n : ℝ))))) * X ^ 2)) *
          A394446 (n + 1) +
      ((C (((1 / ((4 + (n : ℝ)))) * (-3 + (-3 * (n : ℝ))))) +
        C (((1 / ((4 + (n : ℝ)))) * (-3 + (-3 * (n : ℝ))))) * X +
        C (((1 / ((4 + (n : ℝ)))) * (-3 + (-3 * (n : ℝ))))) * X ^ 2)) *
          A394446 n

theorem A394446_splits (n : ℕ) : (A394446 n).Splits := by
  rr_row_splits

end HA394446

namespace HA330798

/-- The OEIS A330798 polynomial sequence, given by a literal second-order derivative recurrence. -/
def A330798 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + 2 * X
  | n + 2 =>
      ((C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
          ((25 / 8) + ((7 / 8) * (n : ℝ))))) * X +
        C (((9 / 8) *
          (1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
          (3 + (n : ℝ)))) * X ^ 2)) * ((A330798 (n + 1)).derivative).derivative +
      ((C (((1 / 4) * (n : ℝ) *
          (1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))))) +
        C (((-1 / 2) *
          (1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))))) * X)) *
        ((A330798 n).derivative).derivative +
      ((C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
          ((21 / 2) + ((-1 / 8) * ((3 + (n : ℝ))) ^ (2)) +
            ((11 / 2) * (n : ℝ))))) +
        C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
          ((99 / 4) + ((-9 / 8) * ((3 + (n : ℝ))) ^ (2)) +
            ((39 / 4) * (n : ℝ))))) * X +
        C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
          ((-75 / 4) + ((-99 / 4) * (n : ℝ))))) * X ^ 2 +
        C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
          (-36 + (-36 * (n : ℝ))))) * X ^ 3)) * (A330798 (n + 1)).derivative +
      ((C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
          (-1 + (-2 * (n : ℝ))))) +
        C ((18 *
          (1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))))) * X +
        C ((33 *
          (1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))))) * X ^ 2 +
        C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
          (-9 + ((-27 / 2) * (n : ℝ))))) * X ^ 3)) * (A330798 n).derivative +
      ((C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
          ((57 / 2) + (15 * (n : ℝ)) +
            ((-15 / 8) * ((3 + (n : ℝ))) ^ (2))))) +
        C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
          (-150 + (-75 * (n : ℝ)) +
            ((81 / 4) * ((3 + (n : ℝ))) ^ (2))))) * X +
        C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
          (-288 + (-144 * (n : ℝ)) +
            (36 * ((3 + (n : ℝ))) ^ (2))))) * X ^ 2)) * A330798 (n + 1) +
      ((C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
          (-63 + (9 * ((3 + (n : ℝ))) ^ (2)) + ((-27 / 2) * (n : ℝ))))) +
        C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
          (-48 + (9 * ((3 + (n : ℝ))) ^ (2)) + ((33 / 2) * (n : ℝ))))) * X +
        C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
          (234 + (-27 * ((3 + (n : ℝ))) ^ (2)) +
            ((261 / 2) * (n : ℝ))))) * X ^ 2)) * A330798 n

theorem A330798_natDegree (n : ℕ) : (A330798 n).natDegree = n := by
  rr_row_natDegree

end HA330798

end RowModelRecentRegistrations
