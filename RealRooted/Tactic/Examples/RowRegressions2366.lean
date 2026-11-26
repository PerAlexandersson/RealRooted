module

public import RealRooted.Basic
public import Mathlib.Algebra.Polynomial.Derivative
import RealRooted.PFPolynomial
import RealRooted.Hadamard.Basic
import RealRooted.Tactic.RowInterlacing

/-!
# Remaining original row calls from #2366

Definitions and goals come from `sqrt-of-2/real-rooted-oeis-proofs`, revision `97fb3191`.
The unbounded calls below remain unsupported: the negative tests record the original goals
and calls, and do not claim those goals are proved. Each failed `have` is rolled back by
`fail_if_success`; the surrounding proposition is only `True`.
A079508's explicitly bounded goal and A184883's splitting goal are positive regressions.
The original A181543 certificate context is tested in `RowRegressions2366Certificates`.
-/

@[expose] public section

open RealRooted Polynomial

namespace RealRooted.Tactic.Examples.RowRegressions2366

noncomputable section

/-- The original downstream recurrence for A079508. -/
def A079508 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | 2 => 2 * X + X ^ 2
  | n + 3 => ((C (((1 / ((3 + ((1 / 2) * (n : ℝ))))) * (-3 + ((-1 / 2) * (n : ℝ))))) + C (((1 /
      ((3 + ((1 / 2) * (n : ℝ))))) * ((9 / 2) + (n : ℝ)))) * X)) * A079508 (n + 2) + ((C (((1 /
      ((3 + ((1 / 2) * (n : ℝ))))) * ((21 / 2) + (3 * (n : ℝ))))) * X + C (((1 / ((3 + ((1 / 2)
      * (n : ℝ))))) * ((-3 / 2) + ((-1 / 2) * (n : ℝ))))) * X ^ 2)) * A079508 (n + 1) + ((C (((1
      / ((3 + ((1 / 2) * (n : ℝ))))) * (6 + (2 * (n : ℝ))))) * X + C (((1 / ((3 + ((1 / 2) * (n
      : ℝ))))) * ((-3 / 2) + ((-1 / 2) * (n : ℝ))))) * X ^ 2)) * A079508 n

/-- The original bounded goal is proved by checking every permitted index. -/
theorem A079508_splits_small (n : ℕ) (hn : n ≤ 4) : (A079508 n).Splits := by
  rr_row_splits

example : True := by
  fail_if_success
    have : ∀ n : ℕ, Interlaces (A079508 n) (A079508 (n + 1)) := by
      intro n
      rr_row_interlaces
  trivial

example : True := by
  fail_if_success
    have : ∀ n : ℕ, (A079508 n).Splits := by
      intro n
      rr_row_splits
  trivial

/-- The left factor from the original conditional endpoint. -/
def A079508SchurLeft (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    monomial k (Nat.choose (k + 1) (n + 1 - k) : ℝ)

/-- The right factor from the original conditional endpoint. -/
def A079508SchurRight (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    monomial k
      ((Nat.choose n k : ℝ) * (Nat.choose (n + 2) (k + 2) : ℝ) / (k + 1))

/-- The closed model from the original conditional endpoint. -/
def A079508Closed (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    monomial k
      ((Nat.choose (k + 1) (n + 1 - k) : ℝ) *
        (Nat.choose (n + 2) (k + 2) : ℝ) / (k + 1))

private lemma A079508SchurLeft_coeff (n k : ℕ) :
    (A079508SchurLeft n).coeff k =
      if k ≤ n then (Nat.choose (k + 1) (n + 1 - k) : ℝ) else 0 := by
  simp [A079508SchurLeft, coeff_monomial, Finsupp.single_apply]

private lemma A079508SchurRight_coeff (n k : ℕ) :
    (A079508SchurRight n).coeff k =
      if k ≤ n then
        (Nat.choose n k : ℝ) * (Nat.choose (n + 2) (k + 2) : ℝ) / (k + 1)
      else 0 := by
  simp [A079508SchurRight, coeff_monomial, Finsupp.single_apply]

private lemma A079508Closed_coeff (n k : ℕ) :
    (A079508Closed n).coeff k =
      if k ≤ n then
        (Nat.choose (k + 1) (n + 1 - k) : ℝ) *
          (Nat.choose (n + 2) (k + 2) : ℝ) / (k + 1)
      else 0 := by
  simp [A079508Closed, coeff_monomial, Finsupp.single_apply]

private lemma A079508Closed_eq_schurSzegoComp (n : ℕ) :
    A079508Closed n =
      schurSzegoComp n (A079508SchurLeft n) (A079508SchurRight n) := by
  ext k
  rw [A079508Closed_coeff, coeff_schurSzegoComp]
  by_cases hk : k ≤ n
  · rw [ite_eq_left hk, ite_eq_left hk, A079508SchurLeft_coeff,
      A079508SchurRight_coeff, ite_eq_left hk, ite_eq_left hk]
    have hchoose : (Nat.choose n k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk).ne'
    grind
  · grind

-- The original conditional goal is still unsupported, even with its model hypotheses.
example : True := by
  fail_if_success
    have : ∀
        (hmodel : ∀ n : ℕ, A079508 n = A079508Closed n)
        (hleft : ∀ n : ℕ, IsPFPolynomial (A079508SchurLeft n))
        (hleft0 : ∀ n : ℕ, A079508SchurLeft n ≠ 0)
        (hright : ∀ n : ℕ, (A079508SchurRight n).Splits)
        (hright0 : ∀ n : ℕ, A079508SchurRight n ≠ 0)
        (n : ℕ), (A079508 n).Splits := by
      intro hmodel hleft hleft0 hright hright0 n
      rr_row_splits
  trivial

/-- The original downstream recurrence for A155495. -/
def A155495 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 12 * X + X ^ 2
  | n + 3 => ((C (((1 / (((-17 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((4 + (n : ℝ))) ^
      (2))))) * (-20 + (-18 * (n : ℝ))))) * X + C (((1 / (((-17 / 3) + ((-5 / 3) * (n : ℝ)) +
      ((2 / 3) * ((4 + (n : ℝ))) ^ (2))))) * (20 + (18 * (n : ℝ))))) * X ^ 2)) * (A155495 (n +
      2)).derivative + ((C ((-16 * (1 / (((-17 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((4 + (n
      : ℝ))) ^ (2))))))) * X + C ((16 * (1 / (((-17 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((4
      + (n : ℝ))) ^ (2))))))) * X ^ 3)) * (A155495 (n + 1)).derivative + ((C (((1 / (((-17 / 3)
      + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((4 + (n : ℝ))) ^ (2))))) * (-127 + (10 * ((4 + (n :
      ℝ))) ^ (2)) + ((-131 / 3) * (n : ℝ))))) + C (((1 / (((-17 / 3) + ((-5 / 3) * (n : ℝ)) +
      ((2 / 3) * ((4 + (n : ℝ))) ^ (2))))) * (121 + (-8 * ((4 + (n : ℝ))) ^ (2)) + ((133 / 3) *
      (n : ℝ))))) * X)) * A155495 (n + 2) + ((C (((1 / (((-17 / 3) + ((-5 / 3) * (n : ℝ)) + ((2
      / 3) * ((4 + (n : ℝ))) ^ (2))))) * ((488 / 3) + (-12 * ((4 + (n : ℝ))) ^ (2)) + ((178 / 3)
      * (n : ℝ))))) + C (((1 / (((-17 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((4 + (n : ℝ))) ^
      (2))))) * ((-1952 / 3) + (48 * ((4 + (n : ℝ))) ^ (2)) + ((-700 / 3) * (n : ℝ))))) * X + C
      (((1 / (((-17 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((4 + (n : ℝ))) ^ (2))))) * ((440 /
      3) + (-12 * ((4 + (n : ℝ))) ^ (2)) + ((130 / 3) * (n : ℝ))))) * X ^ 2)) * A155495 (n + 1)
      + ((C (((1 / (((-17 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((4 + (n : ℝ))) ^ (2))))) *
      ((-124 / 3) + ((-52 / 3) * (n : ℝ)) + ((8 / 3) * ((4 + (n : ℝ))) ^ (2))))) + C (((1 /
      (((-17 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((4 + (n : ℝ))) ^ (2))))) * (-124 + (-52 *
      (n : ℝ)) + (8 * ((4 + (n : ℝ))) ^ (2))))) * X + C (((1 / (((-17 / 3) + ((-5 / 3) * (n :
      ℝ)) + ((2 / 3) * ((4 + (n : ℝ))) ^ (2))))) * (-124 + (-52 * (n : ℝ)) + (8 * ((4 + (n :
      ℝ))) ^ (2))))) * X ^ 2 + C (((1 / (((-17 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((4 + (n
      : ℝ))) ^ (2))))) * ((-124 / 3) + ((-52 / 3) * (n : ℝ)) + ((8 / 3) * ((4 + (n : ℝ))) ^
      (2))))) * X ^ 3)) * A155495 n

example : True := by
  fail_if_success
    have : ∀ n : ℕ, Interlaces (A155495 n) (A155495 (n + 1)) := by
      intro n
      rr_row_interlaces
  trivial

example : True := by
  fail_if_success
    have : ∀ n : ℕ, (A155495 n).Splits := by
      intro n
      rr_row_splits
  trivial

/-- The original downstream recurrence for A111910. -/
def A111910 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => ((C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (42 + (18 * (n :
      ℝ))))) * X + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (-42 + (-18
      * (n : ℝ))))) * X ^ 2)) * (A111910 (n + 1)).derivative + ((C (((1 / ((10 + (2 * ((3 + (n :
      ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (40 + (-2 * ((3 + (n : ℝ))) ^ (2)) + (17 * (n : ℝ))))) +
      C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (-80 + (-31 * (n : ℝ)) +
      (16 * ((3 + (n : ℝ))) ^ (2))))) * X)) * A111910 (n + 1) + ((C (((1 / ((10 + (2 * ((3 + (n
      : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (-30 + (-14 * (n : ℝ)) + (4 * ((3 + (n : ℝ))) ^ (2)))))
      + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 * (n : ℝ))))) * (-60 + (-28 * (n : ℝ))
      + (8 * ((3 + (n : ℝ))) ^ (2))))) * X + C (((1 / ((10 + (2 * ((3 + (n : ℝ))) ^ (2)) + (3 *
      (n : ℝ))))) * (-30 + (-14 * (n : ℝ)) + (4 * ((3 + (n : ℝ))) ^ (2))))) * X ^ 2)) * A111910
      n

example : True := by
  fail_if_success
    have : ∀ n : ℕ, Interlaces (A111910 n) (A111910 (n + 1)) := by
      intro n
      rr_row_interlaces
  trivial

example : True := by
  fail_if_success
    have : ∀ n : ℕ, (A111910 n).Splits := by
      intro n
      rr_row_splits
  trivial

/-- The original downstream recurrence for A184883. -/
def A184883 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 5 * X + X ^ 2
  | n + 3 => ((1 + (2 * X))) * A184883 (n + 2) + (((-1 * (X) ^ (2)) + (2 * X))) * A184883 (n +
      1) + ((X) ^ (2)) * A184883 n

/-- The splitting call is already restored; interlacing is audited separately below. -/
theorem A184883_splits (n : ℕ) : (A184883 n).Splits := by rr_row_splits

-- The original interlacing endpoint had a handwritten proof. This audits its plain tactic.
example : True := by
  fail_if_success
    have : ∀ n : ℕ, Interlaces (A184883 n) (A184883 (n + 1)) := by
      intro n
      rr_row_interlaces
  trivial

/-- The original downstream recurrence for A262226. -/
def A262226 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => ((C (2) * X + C (-2) * X ^ 2)) * (A262226 (n + 1)).derivative + ((C (-2) * X + C
      (4) * X ^ 2 + C (-2) * X ^ 3)) * (A262226 n).derivative + ((C (2) + C ((2 + (2 * (n :
      ℝ)))) * X)) * A262226 (n + 1) + ((C (-1) + C ((-2 * (n : ℝ))) * X + C ((1 + (2 * (n :
      ℝ)))) * X ^ 2)) * A262226 n

example : True := by
  fail_if_success
    have : ∀ n : ℕ, (A262226 n).Splits := by
      intro n
      rr_row_splits
  trivial

/-- The original downstream recurrence for A318107. -/
def A318107 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 6 + X
  | n + 2 => ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-30 + (-18 * (n :
      ℝ))))) * X + C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * ((-15 / 2) + ((-9
      / 2) * (n : ℝ))))) * X ^ 2)) * (A318107 (n + 1)).derivative + ((C (((1 / ((-5 + ((3 + (n :
      ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-183 + (-81 * (n : ℝ)) + (27 * ((3 + (n : ℝ))) ^ (2)))))
      + C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-34 + (-15 * (n : ℝ)) + (5
      * ((3 + (n : ℝ))) ^ (2))))) * X)) * A318107 (n + 1) + (C (((1 / ((-5 + ((3 + (n : ℝ))) ^
      (2) + (-2 * (n : ℝ))))) * (-4 + ((1 / 2) * ((3 + (n : ℝ))) ^ (2)) + (-2 * (n : ℝ))))) * X
      ^ 2) * A318107 n

example : True := by
  fail_if_success
    have : ∀ n : ℕ, Interlaces (A318107 n) (A318107 (n + 1)) := by
      intro n
      rr_row_interlaces
  trivial

/-- The original downstream recurrence for A318397. -/
def A318397 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + X
  | n + 2 => ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (10 + (8 * (n :
      ℝ))))) * X + C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-10 + (-8 * (n :
      ℝ))))) * X ^ 2)) * (A318397 (n + 1)).derivative + ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2)
      + (-2 * (n : ℝ))))) * (-24 + (-10 * (n : ℝ)) + (4 * ((3 + (n : ℝ))) ^ (2))))) + C (((1 /
      ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-43 + (-20 * (n : ℝ)) + (6 * ((3 + (n
      : ℝ))) ^ (2))))) * X)) * A318397 (n + 1) + ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 *
      (n : ℝ))))) * (96 + (-12 * ((3 + (n : ℝ))) ^ (2)) + (48 * (n : ℝ))))) * X + C (((1 / ((-5
      + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-24 + (-12 * (n : ℝ)) + (3 * ((3 + (n :
      ℝ))) ^ (2))))) * X ^ 2)) * A318397 n

example : True := by
  fail_if_success
    have : ∀ n : ℕ, (A318397 n).Splits := by
      intro n
      rr_row_splits
  trivial

/-- The original downstream recurrence for A330798. -/
def A330798 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + 2 * X
  | n + 2 => ((C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) * ((25 / 8) + ((7
      / 8) * (n : ℝ))))) * X + C (((9 / 8) * (1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^
      (2))))) * (3 + (n : ℝ)))) * X ^ 2)) * ((A330798 (n + 1)).derivative).derivative + ((C (((1
      / 4) * (n : ℝ) * (1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))))) + C (((-1 /
      2) * (1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))))) * X)) * ((A330798
      n).derivative).derivative + ((C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^
      (2))))) * ((21 / 2) + ((-1 / 8) * ((3 + (n : ℝ))) ^ (2)) + ((11 / 2) * (n : ℝ))))) + C
      (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) * ((99 / 4) + ((-9 / 8) *
      ((3 + (n : ℝ))) ^ (2)) + ((39 / 4) * (n : ℝ))))) * X + C (((1 / ((-8 + (-3 * (n : ℝ)) + (2
      * ((3 + (n : ℝ))) ^ (2))))) * ((-75 / 4) + ((-99 / 4) * (n : ℝ))))) * X ^ 2 + C (((1 /
      ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) * (-36 + (-36 * (n : ℝ))))) * X ^
      3)) * (A330798 (n + 1)).derivative + ((C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n :
      ℝ))) ^ (2))))) * (-1 + (-2 * (n : ℝ))))) + C ((18 * (1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3
      + (n : ℝ))) ^ (2))))))) * X + C ((33 * (1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^
      (2))))))) * X ^ 2 + C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) * (-9
      + ((-27 / 2) * (n : ℝ))))) * X ^ 3)) * (A330798 n).derivative + ((C (((1 / ((-8 + (-3 * (n
      : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) * ((57 / 2) + (15 * (n : ℝ)) + ((-15 / 8) * ((3 +
      (n : ℝ))) ^ (2))))) + C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) *
      (-150 + (-75 * (n : ℝ)) + ((81 / 4) * ((3 + (n : ℝ))) ^ (2))))) * X + C (((1 / ((-8 + (-3
      * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) * (-288 + (-144 * (n : ℝ)) + (36 * ((3 + (n :
      ℝ))) ^ (2))))) * X ^ 2)) * A330798 (n + 1) + ((C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 +
      (n : ℝ))) ^ (2))))) * (-63 + (9 * ((3 + (n : ℝ))) ^ (2)) + ((-27 / 2) * (n : ℝ))))) + C
      (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n : ℝ))) ^ (2))))) * (-48 + (9 * ((3 + (n :
      ℝ))) ^ (2)) + ((33 / 2) * (n : ℝ))))) * X + C (((1 / ((-8 + (-3 * (n : ℝ)) + (2 * ((3 + (n
      : ℝ))) ^ (2))))) * (234 + (-27 * ((3 + (n : ℝ))) ^ (2)) + ((261 / 2) * (n : ℝ))))) * X ^
      2)) * A330798 n

example : True := by
  fail_if_success
    have : ∀ n : ℕ, (A330798 n).natDegree = n := by
      intro n
      rr_row_natDegree
  trivial

/-- The original downstream recurrence for A367177. -/
def A367177 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 2 * X
  | n + 2 => ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (10 + (8 * (n :
      ℝ))))) * X + C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-10 + (-8 * (n :
      ℝ))))) * X ^ 2)) * (A367177 (n + 1)).derivative + ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2)
      + (-2 * (n : ℝ))))) * (19 + (-2 * ((3 + (n : ℝ))) ^ (2)) + (10 * (n : ℝ))))) + C (((1 /
      ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (-86 + (-40 * (n : ℝ)) + (12 * ((3 + (n
      : ℝ))) ^ (2))))) * X)) * A367177 (n + 1) + ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 *
      (n : ℝ))))) * (-24 + (-12 * (n : ℝ)) + (3 * ((3 + (n : ℝ))) ^ (2))))) + C (((1 / ((-5 +
      ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) * (96 + (-12 * ((3 + (n : ℝ))) ^ (2)) + (48 * (n
      : ℝ))))) * X)) * A367177 n

example : True := by
  fail_if_success
    have : ∀ n : ℕ, Interlaces (A367177 n) (A367177 (n + 1)) := by
      intro n
      rr_row_interlaces
  trivial

example : True := by
  fail_if_success
    have : ∀ n : ℕ, (A367177 n).Splits := by
      intro n
      rr_row_splits
  trivial

/-- The original downstream recurrence for A394446. -/
def A394446 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X + X ^ 2
  | n + 2 => ((C ((-4 * (1 / ((4 + (n : ℝ)))))) * X + C ((-6 * (1 / ((4 + (n : ℝ)))))) * X ^ 2 +
      C ((-2 * (1 / ((4 + (n : ℝ)))))) * X ^ 3)) * (A394446 (n + 1)).derivative + ((C (((1 / ((4
      + (n : ℝ)))) * (7 + (4 * (n : ℝ))))) + C (((1 / ((4 + (n : ℝ)))) * (22 + (13 * (n : ℝ)))))
      * X + C (((1 / ((4 + (n : ℝ)))) * (8 + (5 * (n : ℝ))))) * X ^ 2)) * A394446 (n + 1) + ((C
      (((1 / ((4 + (n : ℝ)))) * (-3 + (-3 * (n : ℝ))))) + C (((1 / ((4 + (n : ℝ)))) * (-3 + (-3
      * (n : ℝ))))) * X + C (((1 / ((4 + (n : ℝ)))) * (-3 + (-3 * (n : ℝ))))) * X ^ 2)) *
      A394446 n

example : True := by
  fail_if_success
    have : ∀ n : ℕ, (A394446 n).Splits := by
      intro n
      rr_row_splits
  trivial

end

end RealRooted.Tactic.Examples.RowRegressions2366
