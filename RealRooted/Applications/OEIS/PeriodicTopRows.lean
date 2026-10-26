module

public import RealRooted.Applications.OEIS.A330798
public import RealRooted.Recurrence.RowModel

/-!
# Remaining periodic-top-coefficient rows

This file closes the A177040 degree problem; the A114580 and A390883 degrees are proved in
the downstream oeis-proofs repository.  The A177040 proof uses its exact parity-split
coefficient vectors as the two states of the multi-lag top-window law.
-/

@[expose] public section

open Polynomial

namespace RealRooted.Tactic.RowParityDegree

noncomputable section

private lemma A177040_coeff_succ (n k : ℕ) :
    Polynomial.coeff (A177040 (n + 4)) (k + 2) =
      ((2 / 5) * ((k : ℝ) +2) * Polynomial.coeff (A177040 (n + 3)) (k + 2)
        + (-2 / 5) * ((k : ℝ) +1) * Polynomial.coeff (A177040 (n + 3)) (k + 1))
      + ((-4 / 5) * ((k : ℝ) +2) * Polynomial.coeff (A177040 (n + 2)) (k + 2)
        + (4 / 5) * ((k : ℝ) +1) * Polynomial.coeff (A177040 (n + 2)) (k + 1))
      + ((2 / 5) * ((k : ℝ) +2) * Polynomial.coeff (A177040 (n + 1)) (k + 2)
        + (-2 / 5) * ((k : ℝ) +1) * Polynomial.coeff (A177040 (n + 1)) (k + 1))
      + ((-4 / 5) * ((k : ℝ) +2) * Polynomial.coeff (A177040 n) (k + 2)
        + (4 / 5) * ((k : ℝ) +1) * Polynomial.coeff (A177040 n) (k + 1))
      + (((2 / 5) + (-1 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 (n + 3)) (k + 2)
        + ((3 / 5) + (1 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 (n + 3)) (k + 1))
      + ((2 + (2 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 (n + 2)) (k + 2)
        + ((-2 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 (n + 2)) (k + 1))
      + (((2 / 5) + (1 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 (n + 1)) (k + 2)
        + ((-7 / 5) + (-1 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 (n + 1)) (k + 1))
      + (((-13 / 5) + (-2 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 n) (k + 2)
        + ((8 / 5) + (2 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 n) (k + 1)) := by
  conv_lhs => rw [A177040]
  rw [show ((C ((2 / 5)) * X + C ((-2 / 5)) * X ^ 2)) * (A177040 (n + 3)).derivative
    + ((C ((-4 / 5)) * X + C ((4 / 5)) * X ^ 2)) * (A177040 (n + 2)).derivative
    + ((C ((2 / 5)) * X + C ((-2 / 5)) * X ^ 2)) * (A177040 (n + 1)).derivative
    + ((C ((-4 / 5)) * X + C ((4 / 5)) * X ^ 2)) * (A177040 n).derivative
    + ((C (((2 / 5) - ((1 / 5) * (n : ℝ)))) + C (((3 / 5) + ((1 / 5) * (n : ℝ)))) * X))
    * A177040 (n + 3) + ((C ((2 + ((2 / 5) * (n : ℝ)))) + C (((-2 / 5) * (n : ℝ))) * X))
    * A177040 (n + 2) + ((C (((2 / 5) + ((1 / 5) * (n : ℝ)))) + C (((-7 / 5) - ((1 / 5)
    * (n : ℝ)))) * X)) * A177040 (n + 1) + ((C (((-13 / 5) - ((2 / 5) * (n : ℝ))))
    + C (((8 / 5) + ((2 / 5) * (n : ℝ)))) * X))
    * A177040 n
      = C (2 / 5) * (X * (A177040 (n + 3)).derivative) + C (-2 / 5) * (X ^ 2 * (A177040 (n
        + 3)).derivative)
      + C (-4 / 5) * (X * (A177040 (n + 2)).derivative) + C (4 / 5) * (X ^ 2 * (A177040 (n
        + 2)).derivative)
      + C (2 / 5) * (X * (A177040 (n + 1)).derivative) + C (-2 / 5) * (X ^ 2 * (A177040 (n
        + 1)).derivative)
      + C (-4 / 5) * (X * (A177040 n).derivative) + C (4 / 5) * (X ^ 2 * (A177040 n).derivative)
      + C ((2 / 5) + (-1 / 5) * (n : ℝ)) * A177040 (n + 3) + C ((3 / 5) + (1 / 5) * (n : ℝ))
        * (X * A177040 (n
        + 3))
      + C (2 + (2 / 5) * (n : ℝ)) * A177040 (n + 2) + C ((-2 / 5) * (n : ℝ)) * (X * A177040 (n
        + 2))
      + C ((2 / 5) + (1 / 5) * (n : ℝ)) * A177040 (n + 1) + C ((-7 / 5) + (-1 / 5) * (n : ℝ))
        * (X * A177040 (n
        + 1))
      + C ((-13 / 5) + (-2 / 5) * (n : ℝ)) * A177040 n + C ((8 / 5) + (2 / 5) * (n : ℝ)) * (X
        * A177040 n) by ring_nf]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_X_pow_mul', coeff_derivative,
    show (2 ≤ k + 2) = True by simp, ↓reduceIte, show k + 2 - 2 = k by lia]
  grind

private lemma A177040_rewrite (n : ℕ) :
    A177040 (n + 4) =
      C (2 / 5) * (X * (A177040 (n + 3)).derivative) + C (-2 / 5) * (X ^ 2 * (A177040 (n
        + 3)).derivative)
      + C (-4 / 5) * (X * (A177040 (n + 2)).derivative) + C (4 / 5) * (X ^ 2 * (A177040 (n
        + 2)).derivative)
      + C (2 / 5) * (X * (A177040 (n + 1)).derivative) + C (-2 / 5) * (X ^ 2 * (A177040 (n
        + 1)).derivative)
      + C (-4 / 5) * (X * (A177040 n).derivative) + C (4 / 5) * (X ^ 2 * (A177040 n).derivative)
      + C ((2 / 5) + (-1 / 5) * (n : ℝ)) * A177040 (n + 3) + C ((3 / 5) + (1 / 5) * (n : ℝ))
        * (X * A177040 (n
        + 3))
      + C (2 + (2 / 5) * (n : ℝ)) * A177040 (n + 2) + C ((-2 / 5) * (n : ℝ)) * (X * A177040 (n
        + 2))
      + C ((2 / 5) + (1 / 5) * (n : ℝ)) * A177040 (n + 1) + C ((-7 / 5) + (-1 / 5) * (n : ℝ))
        * (X * A177040 (n
        + 1))
      + C ((-13 / 5) + (-2 / 5) * (n : ℝ)) * A177040 n + C ((8 / 5) + (2 / 5) * (n : ℝ)) * (X
        * A177040 n)
        := by
  conv_lhs => rw [A177040]
  ring_nf

-- i = 0
private lemma A177040_coeff_zero (n : ℕ) :
    Polynomial.coeff (A177040 (n + 4)) 0 =
        ((2 / 5) + (-1 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 (n + 3)) 0
      + (2 + (2 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 (n + 2)) 0
      + ((2 / 5) + (1 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 (n + 1)) 0
      + ((-13 / 5) + (-2 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 n) 0 := by
  rw [A177040_rewrite]
  simp

-- i = 1
private lemma A177040_coeff_one (n : ℕ) :
    Polynomial.coeff (A177040 (n + 4)) 1 =
        ((2 / 5) * Polynomial.coeff (A177040 (n + 3)) 1)
      + ((-4 / 5) * Polynomial.coeff (A177040 (n + 2)) 1)
      + ((2 / 5) * Polynomial.coeff (A177040 (n + 1)) 1)
      + ((-4 / 5) * Polynomial.coeff (A177040 n) 1)
      + (((2 / 5) + (-1 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 (n + 3)) 1 + ((3 / 5)
        + (1 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 (n
        + 3)) 0)
      + ((2 + (2 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 (n + 2)) 1 + ((-2 / 5) * (n : ℝ))
        * Polynomial.coeff (A177040 (n
        + 2)) 0)
      + (((2 / 5) + (1 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 (n + 1)) 1 + ((-7 / 5)
        + (-1 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 (n
        + 1)) 0)
      + (((-13 / 5) + (-2 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 n) 1 + ((8 / 5)
        + (2 / 5) * (n : ℝ)) * Polynomial.coeff (A177040 n) 0)
        := by
  have hXd : ∀ p : ℝ[X], Polynomial.coeff (X * derivative p) 1 = Polynomial.coeff p 1 := by
    intro p; rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul, coeff_derivative]; simp
  have hX2d : ∀ p : ℝ[X], Polynomial.coeff (X ^ 2 * derivative p) 1 = 0 := by
    intro p; rw [coeff_X_pow_mul']; simp
  have hXp : ∀ p : ℝ[X], Polynomial.coeff (X * p) 1 = Polynomial.coeff p 0 := by simp
  rw [A177040_rewrite]
  simp only [coeff_add, coeff_C_mul, hXd, hX2d, hXp]
  ring_nf

private lemma fac1 (n : ℕ) : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
  rw [Nat.factorial_succ]
  simp
private lemma fac2 (n : ℕ) : ((n + 2).factorial : ℝ) = (n + 2) * (n + 1) * n.factorial := by
  norm_num [Nat.factorial_succ]
  ring
private lemma fac3 (n : ℕ) : ((n + 3).factorial : ℝ) = (n + 3) * (n + 2) * (n + 1) * n.factorial
  := by
  norm_num [Nat.factorial_succ]
  ring
private lemma fac4 (n : ℕ) : ((n + 4).factorial : ℝ) = (n + 4) * (n + 3) * (n + 2) * (n + 1)
  * n.factorial
  := by
  norm_num [Nat.factorial_succ]
  ring
private lemma fac5 (n : ℕ) : ((n + 5).factorial : ℝ) = (n + 5) * (n + 4) * (n + 3) * (n + 2)
  * (n + 1) * n.factorial
  := by
  norm_num [Nat.factorial_succ]
  ring
private lemma fac6 (n : ℕ) : ((n + 6).factorial : ℝ) = (n + 6) * (n + 5) * (n + 4) * (n + 3)
  * (n + 2) * (n + 1) * n.factorial
  := by
  norm_num [Nat.factorial_succ]
  ring
private lemma choose_ratio (x y : ℕ) (h : y ≤ x) :
    (x.choose y : ℝ) = x.factorial / (y.factorial * (x - y).factorial) := by
  have hne : (y.factorial : ℝ) * (x - y).factorial ≠ 0 := by
    have := Nat.factorial_pos y; have := Nat.factorial_pos (x - y); positivity
  rw [eq_div_iff hne]
  have h2 : (x.choose y : ℝ) * (y.factorial * (x - y).factorial) = x.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial h]
    grind
  assumption
private def Bcoef (n i : ℕ) : ℝ := if i ≤ n / 2 then (Nat.choose (n - n / 2 + i
  + 1) (n / 2 - i) : ℝ) else 0
private lemma Bred (n i U Ln : ℕ) (hle : i ≤ n / 2) (hU : n - n / 2 + i + 1 = U) (hL : n / 2 - i
  = Ln) :
    Bcoef n i = (Nat.choose U Ln : ℝ) := by unfold Bcoef; simp_all
private lemma Bred0 (n i : ℕ) (hle : ¬ i ≤ n / 2) : Bcoef n i = 0 := by unfold Bcoef; simp_all

private lemma even_interior (a k : ℕ) :
    (Nat.choose (2 * k + a + 7) (a + 2) : ℝ) =
    (2 / 5) * ((k : ℝ) +2) * (Nat.choose (2 * k + a + 7) (a + 1) : ℝ) + (-2 / 5)
      * ((k : ℝ) +1) * (Nat.choose (2 * k + a + 6) (a + 2) : ℝ) + (-4 / 5) * ((k : ℝ) +2)
      * (Nat.choose (2 * k + a + 6) (a + 1) : ℝ) + (4 / 5) * ((k : ℝ) +1) * (Nat.choose (2 * k
      + a + 5) (a + 2) : ℝ) + (2 / 5) * ((k : ℝ) +2) * (Nat.choose (2 * k + a + 6) a : ℝ)
      + (-2 / 5) * ((k : ℝ) +1) * (Nat.choose (2 * k + a + 5) (a + 1) : ℝ) + (-4 / 5)
      * ((k : ℝ) +2) * (Nat.choose (2 * k + a + 5) a : ℝ) + (4 / 5) * ((k : ℝ) +1)
      * (Nat.choose (2 * k + a + 4) (a + 1) : ℝ) + ((2 / 5) +(-1 / 5) * (2 * ((k : ℝ) +2
      + a))) * (Nat.choose (2 * k + a + 7) (a + 1) : ℝ) + ((3 / 5) +(1 / 5) * (2 * ((k : ℝ) +2
      + a))) * (Nat.choose (2 * k + a + 6) (a + 2) : ℝ) + (2 + (2 / 5) * (2 * ((k : ℝ) +2
      + a))) * (Nat.choose (2 * k + a + 6) (a + 1) : ℝ) + ((-2 / 5) * (2 * ((k : ℝ) +2 + a)))
      * (Nat.choose (2 * k + a + 5) (a + 2) : ℝ) + ((2 / 5) +(1 / 5) * (2 * ((k : ℝ) +2 + a)))
      * (Nat.choose (2 * k + a + 6) a : ℝ) + ((-7 / 5) +(-1 / 5) * (2 * ((k : ℝ) +2 + a)))
      * (Nat.choose (2 * k + a + 5) (a + 1) : ℝ) + ((-13 / 5) +(-2 / 5) * (2 * ((k : ℝ) +2
      + a))) * (Nat.choose (2 * k + a + 5) a : ℝ) + ((8 / 5) +(2 / 5) * (2 * ((k : ℝ) +2
      + a))) * (Nat.choose (2 * k + a + 4) (a + 1) : ℝ)
      := by
  rw [choose_ratio (2 * k + a + 7) (a + 2) (by lia), choose_ratio (2 * k + a + 7) (a + 1) (by lia),
      choose_ratio (2 * k + a + 6) (a + 2) (by lia), choose_ratio (2 * k + a + 6) (a + 1) (by lia),
      choose_ratio (2 * k + a + 6) a (by lia), choose_ratio (2 * k + a + 5) (a + 2) (by lia),
      choose_ratio (2 * k + a + 5) (a + 1) (by lia), choose_ratio (2 * k + a + 5) a (by lia),
      choose_ratio (2 * k + a + 4) (a + 1) (by lia)]
  rw [show 2 * k + a + 7 - (a + 2) = 2 * k + 5 by lia, show 2 * k + a + 7 - (a + 1) = 2 * k
    + 6 by lia,
      show 2 * k + a + 6 - (a + 2) = 2 * k + 4 by lia, show 2 * k + a + 6 - (a + 1) = 2 * k
        + 5 by lia,
      show 2 * k + a + 6 - a = 2 * k + 6 by lia, show 2 * k + a + 5 - (a + 2) = 2 * k + 3 by lia,
      show 2 * k + a + 5 - (a + 1) = 2 * k + 4 by lia, show 2 * k + a + 5 - a = 2 * k + 5 by lia,
      show 2 * k + a + 4 - (a + 1) = 2 * k + 3 by lia]
  rw [show (2 * k + a + 7) = (2 * k + a + 4) +3 by lia, show (2 * k + a + 6) = (2 * k + a
    + 4) +2 by lia,
      show (2 * k + a + 5) = (2 * k + a + 4) +1 by lia,
      show (2 * k + 6) = (2 * k + 3) +3 by lia, show (2 * k + 5) = (2 * k + 3) +2 by lia,
      show (2 * k + 4) = (2 * k + 3) +1 by lia]
  rw [fac3 (2 * k + a + 4), fac2 (2 * k + a + 4), fac1 (2 * k + a + 4),
      fac3 (2 * k + 3), fac2 (2 * k + 3), fac1 (2 * k + 3), fac2 a, fac1 a]
  push_cast
  have hp1 : ((2 * k + a + 4).factorial : ℝ) ≠ 0 := by positivity
  have hp2 : (a.factorial : ℝ) ≠ 0 := by positivity
  have hp3 : ((2 * k + 3).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring_nf

private lemma odd_interior (a k : ℕ) :
    (Nat.choose (2 * k + a + 8) (a + 2) : ℝ) =
    (2 / 5) * ((k : ℝ) +2) * (Nat.choose (2 * k + a + 7) (a + 2) : ℝ) + (-2 / 5)
      * ((k : ℝ) +1) * (Nat.choose (2 * k + a + 6) (a + 3) : ℝ) + (-4 / 5) * ((k : ℝ) +2)
      * (Nat.choose (2 * k + a + 7) (a + 1) : ℝ) + (4 / 5) * ((k : ℝ) +1) * (Nat.choose (2 * k
      + a + 6) (a + 2) : ℝ) + (2 / 5) * ((k : ℝ) +2) * (Nat.choose (2 * k + a + 6) (a
      + 1) : ℝ) + (-2 / 5) * ((k : ℝ) +1) * (Nat.choose (2 * k + a + 5) (a + 2) : ℝ)
      + (-4 / 5) * ((k : ℝ) +2) * (Nat.choose (2 * k + a + 6) a : ℝ) + (4 / 5) * ((k : ℝ) +1)
      * (Nat.choose (2 * k + a + 5) (a + 1) : ℝ) + ((2 / 5) +(-1 / 5) * (2 * ((k : ℝ) +2
      + a) +1)) * (Nat.choose (2 * k + a + 7) (a + 2) : ℝ) + ((3 / 5) +(1 / 5) * (2
      * ((k : ℝ) +2 + a) +1)) * (Nat.choose (2 * k + a + 6) (a + 3) : ℝ) + (2 + (2 / 5) * (2
      * ((k : ℝ) +2 + a) +1)) * (Nat.choose (2 * k + a + 7) (a + 1) : ℝ) + ((-2 / 5) * (2
      * ((k : ℝ) +2 + a) +1)) * (Nat.choose (2 * k + a + 6) (a + 2) : ℝ) + ((2 / 5) +(1 / 5)
      * (2 * ((k : ℝ) +2 + a) +1)) * (Nat.choose (2 * k + a + 6) (a + 1) : ℝ)
      + ((-7 / 5) +(-1 / 5) * (2 * ((k : ℝ) +2 + a) +1)) * (Nat.choose (2 * k + a + 5) (a
      + 2) : ℝ) + ((-13 / 5) +(-2 / 5) * (2 * ((k : ℝ) +2 + a) +1)) * (Nat.choose (2 * k + a
      + 6) a : ℝ) + ((8 / 5) +(2 / 5) * (2 * ((k : ℝ) +2 + a) +1)) * (Nat.choose (2 * k + a
      + 5) (a + 1) : ℝ)
      := by
  rw [choose_ratio (2 * k + a + 8) (a + 2) (by lia), choose_ratio (2 * k + a + 7) (a + 2) (by lia),
      choose_ratio (2 * k + a + 6) (a + 3) (by lia), choose_ratio (2 * k + a + 7) (a + 1) (by lia),
      choose_ratio (2 * k + a + 6) (a + 2) (by lia), choose_ratio (2 * k + a + 6) (a + 1) (by lia),
      choose_ratio (2 * k + a + 5) (a + 2) (by lia), choose_ratio (2 * k + a + 6) a (by lia),
      choose_ratio (2 * k + a + 5) (a + 1) (by lia)]
  rw [show 2 * k + a + 8 - (a + 2) = 2 * k + 6 by lia, show 2 * k + a + 7 - (a + 2) = 2 * k
    + 5 by lia,
      show 2 * k + a + 6 - (a + 3) = 2 * k + 3 by lia, show 2 * k + a + 7 - (a + 1) = 2 * k
        + 6 by lia,
      show 2 * k + a + 6 - (a + 2) = 2 * k + 4 by lia, show 2 * k + a + 6 - (a + 1) = 2 * k
        + 5 by lia,
      show 2 * k + a + 5 - (a + 2) = 2 * k + 3 by lia, show 2 * k + a + 6 - a = 2 * k + 6 by lia,
      show 2 * k + a + 5 - (a + 1) = 2 * k + 4 by lia]
  rw [show (2 * k + a + 8) = (2 * k + a + 5) +3 by lia, show (2 * k + a + 7) = (2 * k + a
    + 5) +2 by lia,
      show (2 * k + a + 6) = (2 * k + a + 5) +1 by lia,
      show (2 * k + 6) = (2 * k + 3) +3 by lia, show (2 * k + 5) = (2 * k + 3) +2 by lia,
      show (2 * k + 4) = (2 * k + 3) +1 by lia]
  rw [fac3 (2 * k + a + 5), fac2 (2 * k + a + 5), fac1 (2 * k + a + 5),
      fac3 (2 * k + 3), fac2 (2 * k + 3), fac1 (2 * k + 3), fac3 a, fac2 a, fac1 a]
  push_cast
  have hp1 : ((2 * k + a + 5).factorial : ℝ) ≠ 0 := by positivity
  have hp2 : (a.factorial : ℝ) ≠ 0 := by positivity
  have hp3 : ((2 * k + 3).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring_nf
private lemma even_km1 (k : ℕ) :
    (Nat.choose (2 * k + 6) 1 : ℝ) = ((4 / 5) + (2 / 5) * (k : ℝ)) * (Nat.choose (2 * k
      + 6) 0 : ℝ) + ((-2 / 5) + (-2 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 5) 1 : ℝ)
      + ((-8 / 5) + (-4 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 5) 0 : ℝ) + ((4 / 5) + (4 / 5)
      * (k : ℝ)) * (Nat.choose (2 * k + 4) 1 : ℝ) + ((-2 / 5) + (-2 / 5) * (k : ℝ))
      * (Nat.choose (2 * k + 4) 0 : ℝ) + ((4 / 5) + (4 / 5) * (k : ℝ)) * (Nat.choose (2 * k
      + 3) 0 : ℝ) + ((0) + (-2 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 6) 0 : ℝ) + ((1)
      + (2 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 5) 1 : ℝ) + ((14 / 5) + (4 / 5) * (k : ℝ))
      * (Nat.choose (2 * k + 5) 0 : ℝ) + ((-4 / 5) + (-4 / 5) * (k : ℝ)) * (Nat.choose (2 * k
      + 4) 1 : ℝ) + ((-9 / 5) + (-2 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 4) 0 : ℝ)
      + ((12 / 5) + (4 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 3) 0 : ℝ)
      := by
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one]
  grind

private lemma even_keqj (k : ℕ) :
    (Nat.choose (2 * k + 5) 0 : ℝ) = ((-2 / 5) + (-2 / 5) * (k : ℝ)) * (Nat.choose (2 * k
      + 4) 0 : ℝ) + ((4 / 5) + (4 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 3) 0 : ℝ) + ((3 / 5)
      + (2 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 4) 0 : ℝ) + ((0) + (-4 / 5) * (k : ℝ))
      * (Nat.choose (2 * k + 3) 0 : ℝ)
      := by
  grind

private lemma odd_keqj (k : ℕ) :
    (Nat.choose (2 * k + 6) 0 : ℝ) = ((4 / 5) + (2 / 5) * (k : ℝ)) * (Nat.choose (2 * k
      + 5) 0 : ℝ) + ((-2 / 5) + (-2 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 4) 1 : ℝ)
      + ((4 / 5) + (4 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 4) 0 : ℝ) + ((-2 / 5) + (-2 / 5)
      * (k : ℝ)) * (Nat.choose (2 * k + 3) 0 : ℝ) + ((1 / 5) + (-2 / 5) * (k : ℝ))
      * (Nat.choose (2 * k + 5) 0 : ℝ) + ((4 / 5) + (2 / 5) * (k : ℝ)) * (Nat.choose (2 * k
      + 4) 1 : ℝ) + ((-2 / 5) + (-4 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 4) 0 : ℝ)
      + ((-8 / 5) + (-2 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 3) 0 : ℝ)
      := by
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one]
  grind

private lemma odd_km1 (k : ℕ) :
    (Nat.choose (2 * k + 7) 1 : ℝ) = ((4 / 5) + (2 / 5) * (k : ℝ)) * (Nat.choose (2 * k
      + 6) 1 : ℝ) + ((-2 / 5) + (-2 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 5) 2 : ℝ)
      + ((-8 / 5) + (-4 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 6) 0 : ℝ) + ((4 / 5) + (4 / 5)
      * (k : ℝ)) * (Nat.choose (2 * k + 5) 1 : ℝ) + ((4 / 5) + (2 / 5) * (k : ℝ))
      * (Nat.choose (2 * k + 5) 0 : ℝ) + ((-2 / 5) + (-2 / 5) * (k : ℝ)) * (Nat.choose (2 * k
      + 4) 1 : ℝ) + ((4 / 5) + (4 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 4) 0 : ℝ) + ((-1 / 5)
      + (-2 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 6) 1 : ℝ) + ((6 / 5) + (2 / 5) * (k : ℝ))
      * (Nat.choose (2 * k + 5) 2 : ℝ) + ((16 / 5) + (4 / 5) * (k : ℝ)) * (Nat.choose (2 * k
      + 6) 0 : ℝ) + ((-6 / 5) + (-4 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 5) 1 : ℝ) + ((1)
      + (2 / 5) * (k : ℝ)) * (Nat.choose (2 * k + 5) 0 : ℝ) + ((-2) + (-2 / 5) * (k : ℝ))
      * (Nat.choose (2 * k + 4) 1 : ℝ) + ((14 / 5) + (4 / 5) * (k : ℝ)) * (Nat.choose (2 * k
      + 4) 0 : ℝ)
      := by
  rw [choose_ratio (2 * k + 5) 2 (by lia), choose_ratio (2 * k + 7) 1 (by lia),
      choose_ratio (2 * k + 6) 1 (by lia), choose_ratio (2 * k + 5) 1 (by lia),
      choose_ratio (2 * k + 4) 1 (by lia)]
  simp only [Nat.choose_zero_right, Nat.cast_one]
  rw [show 2 * k + 5 - 2 = 2 * k + 3 by lia, show 2 * k + 7 - 1 = 2 * k + 6 by lia,
      show 2 * k + 6 - 1 = 2 * k + 5 by lia, show 2 * k + 5 - 1 = 2 * k + 4 by lia,
      show 2 * k + 4 - 1 = 2 * k + 3 by lia]
  rw [show (2 * k + 7) = (2 * k + 3) +4 by lia, show (2 * k + 6) = (2 * k + 3) +3 by lia,
      show (2 * k + 5) = (2 * k + 3) +2 by lia, show (2 * k + 4) = (2 * k + 3) +1 by lia]
  rw [fac4 (2 * k + 3), fac3 (2 * k + 3), fac2 (2 * k + 3), fac1 (2 * k + 3)]
  simp only [Nat.factorial_one, Nat.factorial_two]
  push_cast
  have hp : ((2 * k + 3).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring_nf

private lemma i0_even (j : ℕ) :
    (Nat.choose (j + 3) (j + 2) : ℝ) = ((2 / 5) + (-2 / 5) * (j : ℝ)) * (Nat.choose (j + 3) (j
      + 1) : ℝ) + ((2) + (4 / 5) * (j : ℝ)) * (Nat.choose (j + 2) (j + 1) : ℝ) + ((2 / 5)
      + (2 / 5) * (j : ℝ)) * (Nat.choose (j + 2) j : ℝ) + ((-13 / 5) + (-4 / 5) * (j : ℝ))
      * (Nat.choose (j + 1) j : ℝ)
      := by
  rw [choose_ratio (j + 1) j (by lia), choose_ratio (j + 2) j (by lia), choose_ratio (j
    + 2) (j + 1) (by lia), choose_ratio (j + 3) (j + 1) (by lia), choose_ratio (j + 3) (j
    + 2) (by lia)]
  rw [show (j + 1)-j = 1 by lia, show (j + 2)-j = 2 by lia, show (j + 2)-(j + 1) = 1 by lia,
    show (j + 3)-(j + 1) = 2 by lia, show (j + 3)-(j + 2)
    = 1 by lia]
  rw [fac3 j, fac2 j, fac1 j]
  simp only [Nat.factorial_one, Nat.factorial_two]
  push_cast
  have hp : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring_nf

private lemma i0_odd (j : ℕ) :
    (Nat.choose (j + 4) (j + 2) : ℝ) = ((1 / 5) + (-2 / 5) * (j : ℝ)) * (Nat.choose (j + 3) (j
      + 2) : ℝ) + ((12 / 5) + (4 / 5) * (j : ℝ)) * (Nat.choose (j + 3) (j + 1) : ℝ) + ((3 / 5)
      + (2 / 5) * (j : ℝ)) * (Nat.choose (j + 2) (j + 1) : ℝ) + ((-3) + (-4 / 5) * (j : ℝ))
      * (Nat.choose (j + 2) j : ℝ)
      := by
  rw [choose_ratio (j + 2) j (by lia), choose_ratio (j + 2) (j + 1) (by lia), choose_ratio (j
    + 3) (j + 1) (by lia), choose_ratio (j + 3) (j + 2) (by lia), choose_ratio (j + 4) (j
    + 2) (by lia)]
  rw [show (j + 2)-j = 2 by lia, show (j + 2)-(j + 1) = 1 by lia, show (j + 3)-(j + 1)
    = 2 by lia, show (j + 3)-(j + 2) = 1 by lia, show (j + 4)-(j + 2)
    = 2 by lia]
  rw [fac4 j, fac3 j, fac2 j, fac1 j]
  simp only [Nat.factorial_one, Nat.factorial_two]
  push_cast
  have hp : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring_nf

private lemma i1_even (j : ℕ) (hj : 1 ≤ j) :
    (Nat.choose (j + 4) (j + 1) : ℝ) = ((2 / 5) + (0) * (j : ℝ)) * (Nat.choose (j + 4) j : ℝ)
      + ((-4 / 5) + (0) * (j : ℝ)) * (Nat.choose (j + 3) j : ℝ) + ((2 / 5) + (0) * (j : ℝ))
      * (Nat.choose (j + 3) (j - 1) : ℝ) + ((-4 / 5) + (0) * (j : ℝ)) * (Nat.choose (j
      + 2) (j - 1) : ℝ) + ((2 / 5) + (-2 / 5) * (j : ℝ)) * (Nat.choose (j + 4) j : ℝ)
      + ((3 / 5) + (2 / 5) * (j : ℝ)) * (Nat.choose (j + 3) (j + 1) : ℝ) + ((2) + (4 / 5)
      * (j : ℝ)) * (Nat.choose (j + 3) j : ℝ) + ((0) + (-4 / 5) * (j : ℝ)) * (Nat.choose (j
      + 2) (j + 1) : ℝ) + ((2 / 5) + (2 / 5) * (j : ℝ)) * (Nat.choose (j + 3) (j - 1) : ℝ)
      + ((-7 / 5) + (-2 / 5) * (j : ℝ)) * (Nat.choose (j + 2) j : ℝ) + ((-13 / 5) + (-4 / 5)
      * (j : ℝ)) * (Nat.choose (j + 2) (j - 1) : ℝ) + ((8 / 5) + (4 / 5) * (j : ℝ))
      * (Nat.choose (j + 1) j : ℝ)
      := by
  obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by lia⟩
  rw [show Nat.choose (b + 1 + 1) (b + 1) = Nat.choose (b + 2) (b + 1) by simp,
    show Nat.choose (b + 1 + 2) (b + 1 - 1) = Nat.choose (b + 3) b by simp, show Nat.choose (b
    + 1 + 2) (b + 1) = Nat.choose (b + 3) (b + 1) by simp, show Nat.choose (b + 1 + 2) (b + 1
    + 1) = Nat.choose (b + 3) (b + 2) by simp, show Nat.choose (b + 1 + 3) (b + 1 - 1)
    = Nat.choose (b + 4) b by simp, show Nat.choose (b + 1 + 3) (b + 1) = Nat.choose (b
    + 4) (b + 1) by simp, show Nat.choose (b + 1 + 3) (b + 1 + 1) = Nat.choose (b + 4) (b
    + 2) by simp, show Nat.choose (b + 1 + 4) (b + 1) = Nat.choose (b + 5) (b + 1) by simp,
    show Nat.choose (b + 1 + 4) (b + 1 + 1) = Nat.choose (b + 5) (b
    + 2) by simp]
  rw [choose_ratio (b + 2) (b + 1) (by lia), choose_ratio (b + 3) b (by lia), choose_ratio (b
    + 3) (b + 1) (by lia), choose_ratio (b + 3) (b + 2) (by lia), choose_ratio (b
    + 4) b (by lia), choose_ratio (b + 4) (b + 1) (by lia), choose_ratio (b + 4) (b
    + 2) (by lia), choose_ratio (b + 5) (b + 1) (by lia), choose_ratio (b + 5) (b
    + 2) (by lia)]
  rw [show (b + 2)-(b + 1) = 1 by lia, show (b + 3)-b = 3 by lia, show (b + 3)-(b + 1)
    = 2 by lia, show (b + 3)-(b + 2) = 1 by lia, show (b + 4)-b = 4 by lia, show (b + 4)-(b
    + 1) = 3 by lia, show (b + 4)-(b + 2) = 2 by lia, show (b + 5)-(b + 1) = 4 by lia, show (b
    + 5)-(b + 2)
    = 3 by lia]
  rw [fac5 b, fac4 b, fac3 b, fac2 b, fac1 b]
  simp only [Nat.factorial_one, Nat.factorial_two]
  push_cast
  have hp : (b.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring_nf

private lemma i1_odd (j : ℕ) (hj : 1 ≤ j) :
    (Nat.choose (j + 5) (j + 1) : ℝ) = ((2 / 5) + (0) * (j : ℝ)) * (Nat.choose (j + 4) (j
      + 1) : ℝ) + ((-4 / 5) + (0) * (j : ℝ)) * (Nat.choose (j + 4) j : ℝ) + ((2 / 5) + (0)
      * (j : ℝ)) * (Nat.choose (j + 3) j : ℝ) + ((-4 / 5) + (0) * (j : ℝ)) * (Nat.choose (j
      + 3) (j - 1) : ℝ) + ((1 / 5) + (-2 / 5) * (j : ℝ)) * (Nat.choose (j + 4) (j + 1) : ℝ)
      + ((4 / 5) + (2 / 5) * (j : ℝ)) * (Nat.choose (j + 3) (j + 2) : ℝ) + ((12 / 5) + (4 / 5)
      * (j : ℝ)) * (Nat.choose (j + 4) j : ℝ) + ((-2 / 5) + (-4 / 5) * (j : ℝ))
      * (Nat.choose (j + 3) (j + 1) : ℝ) + ((3 / 5) + (2 / 5) * (j : ℝ)) * (Nat.choose (j
      + 3) j : ℝ) + ((-8 / 5) + (-2 / 5) * (j : ℝ)) * (Nat.choose (j + 2) (j + 1) : ℝ) + ((-3)
      + (-4 / 5) * (j : ℝ)) * (Nat.choose (j + 3) (j - 1) : ℝ) + ((2) + (4 / 5) * (j : ℝ))
      * (Nat.choose (j + 2) j : ℝ)
      := by
  obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by lia⟩
  rw [show Nat.choose (b + 1 + 2) (b + 1) = Nat.choose (b + 3) (b + 1) by simp,
    show Nat.choose (b + 1 + 2) (b + 1 + 1) = Nat.choose (b + 3) (b + 2) by simp,
    show Nat.choose (b + 1 + 3) (b + 1 - 1) = Nat.choose (b + 4) b by simp, show Nat.choose (b
    + 1 + 3) (b + 1) = Nat.choose (b + 4) (b + 1) by simp, show Nat.choose (b + 1 + 3) (b + 1
    + 1) = Nat.choose (b + 4) (b + 2) by simp, show Nat.choose (b + 1 + 3) (b + 1 + 2)
    = Nat.choose (b + 4) (b + 3) by simp, show Nat.choose (b + 1 + 4) (b + 1) = Nat.choose (b
    + 5) (b + 1) by simp, show Nat.choose (b + 1 + 4) (b + 1 + 1) = Nat.choose (b + 5) (b
    + 2) by simp, show Nat.choose (b + 1 + 5) (b + 1 + 1) = Nat.choose (b + 6) (b
    + 2) by simp]
  rw [choose_ratio (b + 3) (b + 1) (by lia), choose_ratio (b + 3) (b + 2) (by lia),
    choose_ratio (b + 4) b (by lia), choose_ratio (b + 4) (b + 1) (by lia), choose_ratio (b
    + 4) (b + 2) (by lia), choose_ratio (b + 4) (b + 3) (by lia), choose_ratio (b + 5) (b
    + 1) (by lia), choose_ratio (b + 5) (b + 2) (by lia), choose_ratio (b + 6) (b
    + 2) (by lia)]
  rw [show (b + 3)-(b + 1) = 2 by lia, show (b + 3)-(b + 2) = 1 by lia, show (b + 4)-b
    = 4 by lia, show (b + 4)-(b + 1) = 3 by lia, show (b + 4)-(b + 2) = 2 by lia, show (b
    + 4)-(b + 3) = 1 by lia, show (b + 5)-(b + 1) = 4 by lia, show (b + 5)-(b + 2) = 3 by lia,
    show (b + 6)-(b + 2)
    = 4 by lia]
  rw [fac6 b, fac5 b, fac4 b, fac3 b, fac2 b, fac1 b]
  simp only [Nat.factorial_one, Nat.factorial_two]
  push_cast
  have hp : (b.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring_nf

private lemma even_step (j0 k : ℕ) :
    Bcoef (2 * j0 + 4) (k + 2) = (2 / 5) * ((k : ℝ) +2) * Bcoef (2 * j0 + 3) (k + 2)
      + (-2 / 5) * ((k : ℝ) +1) * Bcoef (2 * j0 + 3) (k + 1) + (-4 / 5) * ((k : ℝ) +2)
      * Bcoef (2 * j0 + 2) (k + 2) + (4 / 5) * ((k : ℝ) +1) * Bcoef (2 * j0 + 2) (k + 1)
      + (2 / 5) * ((k : ℝ) +2) * Bcoef (2 * j0 + 1) (k + 2) + (-2 / 5) * ((k : ℝ) +1)
      * Bcoef (2 * j0 + 1) (k + 1) + (-4 / 5) * ((k : ℝ) +2) * Bcoef (2 * j0) (k + 2)
      + (4 / 5) * ((k : ℝ) +1) * Bcoef (2 * j0) (k + 1) + ((2 / 5) + (-1 / 5) * ((2
      * j0) : ℝ)) * Bcoef (2 * j0 + 3) (k + 2) + ((3 / 5) + (1 / 5) * ((2 * j0) : ℝ))
      * Bcoef (2 * j0 + 3) (k + 1) + ((2 : ℝ) + (2 / 5) * ((2 * j0) : ℝ)) * Bcoef (2 * j0
      + 2) (k + 2) + ((-2 / 5) * ((2 * j0) : ℝ)) * Bcoef (2 * j0 + 2) (k + 1) + ((2 / 5)
      + (1 / 5) * ((2 * j0) : ℝ)) * Bcoef (2 * j0 + 1) (k + 2) + ((-7 / 5) + (-1 / 5) * ((2
      * j0) : ℝ)) * Bcoef (2 * j0 + 1) (k + 1) + ((-13 / 5) + (-2 / 5) * ((2 * j0) : ℝ))
      * Bcoef (2 * j0) (k + 2) + ((8 / 5) + (2 / 5) * ((2 * j0) : ℝ)) * Bcoef (2 * j0) (k + 1)
      := by
  rcases lt_or_ge (k + 1) j0 with hk | hk
  · obtain ⟨a, rfl⟩ : ∃ a, j0 = k + 2 + a := ⟨j0 - (k + 2), by lia⟩
    rw [Bred (2 * (k + 2 + a) +4) (k + 2) (2 * k + a + 7) (a + 2) (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a) +3) (k + 2) (2 * k + a + 7) (a + 1) (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a) +3) (k + 1) (2 * k + a + 6) (a + 2) (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a) +2) (k + 2) (2 * k + a + 6) (a + 1) (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a) +2) (k + 1) (2 * k + a + 5) (a + 2) (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a) +1) (k + 2) (2 * k + a + 6) a (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a) +1) (k + 1) (2 * k + a + 5) (a + 1) (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a)) (k + 2) (2 * k + a + 5) a (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a)) (k + 1) (2 * k + a + 4) (a + 1) (by lia) (by lia) (by lia)]
    have H := even_interior a k
    simp_all
  · rcases lt_or_ge k j0 with hk2 | hk2
    · have hj0 : j0 = k + 1 := by lia
      subst j0
      rw [Bred (2 * (k + 1) +4) (k + 2) (2 * k + 6) 1 (by lia) (by lia) (by lia)]
      rw [Bred (2 * (k + 1) +3) (k + 2) (2 * k + 6) 0 (by lia) (by lia) (by lia)]
      rw [Bred (2 * (k + 1) +3) (k + 1) (2 * k + 5) 1 (by lia) (by lia) (by lia)]
      rw [Bred (2 * (k + 1) +2) (k + 2) (2 * k + 5) 0 (by lia) (by lia) (by lia)]
      rw [Bred (2 * (k + 1) +2) (k + 1) (2 * k + 4) 1 (by lia) (by lia) (by lia)]
      rw [Bred0 (2 * (k + 1) +1) (k + 2) (by lia)]
      rw [Bred (2 * (k + 1) +1) (k + 1) (2 * k + 4) 0 (by lia) (by lia) (by lia)]
      rw [Bred0 (2 * (k + 1)) (k + 2) (by lia)]
      rw [Bred (2 * (k + 1)) (k + 1) (2 * k + 3) 0 (by lia) (by lia) (by lia)]
      have H := even_km1 k
      grind
    · rcases lt_or_ge k (j0 + 1) with hk3 | hk3
      · have hj0 : j0 = k := by lia
        subst j0
        rw [Bred (2 * k + 4) (k + 2) (2 * k + 5) 0 (by lia) (by lia) (by lia)]
        rw [Bred0 (2 * k + 3) (k + 2) (by lia)]
        rw [Bred (2 * k + 3) (k + 1) (2 * k + 4) 0 (by lia) (by lia) (by lia)]
        rw [Bred0 (2 * k + 2) (k + 2) (by lia)]
        rw [Bred (2 * k + 2) (k + 1) (2 * k + 3) 0 (by lia) (by lia) (by lia)]
        rw [Bred0 (2 * k + 1) (k + 2) (by lia)]
        rw [Bred0 (2 * k + 1) (k + 1) (by lia)]
        rw [Bred0 (2 * k) (k + 2) (by lia)]
        rw [Bred0 (2 * k) (k + 1) (by lia)]
        grind
      · -- k >= j0+1, everything vanishes
        rw [Bred0 (2 * j0 + 4) (k + 2) (by lia)]
        rw [Bred0 (2 * j0 + 3) (k + 2) (by lia)]
        rw [Bred0 (2 * j0 + 3) (k + 1) (by lia)]
        rw [Bred0 (2 * j0 + 2) (k + 2) (by lia)]
        rw [Bred0 (2 * j0 + 2) (k + 1) (by lia)]
        rw [Bred0 (2 * j0 + 1) (k + 2) (by lia)]
        rw [Bred0 (2 * j0 + 1) (k + 1) (by lia)]
        rw [Bred0 (2 * j0) (k + 2) (by lia)]
        rw [Bred0 (2 * j0) (k + 1) (by lia)]
        ring_nf

private lemma odd_step (j0 k : ℕ) :
    Bcoef (2 * j0 + 1 + 4) (k + 2) = (2 / 5) * ((k : ℝ) +2) * Bcoef (2 * j0 + 1 + 3) (k + 2)
      + (-2 / 5) * ((k : ℝ) +1) * Bcoef (2 * j0 + 1 + 3) (k + 1) + (-4 / 5) * ((k : ℝ) +2)
      * Bcoef (2 * j0 + 1 + 2) (k + 2) + (4 / 5) * ((k : ℝ) +1) * Bcoef (2 * j0 + 1 + 2) (k
      + 1) + (2 / 5) * ((k : ℝ) +2) * Bcoef (2 * j0 + 1 + 1) (k + 2) + (-2 / 5) * ((k : ℝ) +1)
      * Bcoef (2 * j0 + 1 + 1) (k + 1) + (-4 / 5) * ((k : ℝ) +2) * Bcoef (2 * j0 + 1) (k + 2)
      + (4 / 5) * ((k : ℝ) +1) * Bcoef (2 * j0 + 1) (k + 1) + ((2 / 5) + (-1 / 5) * ((2 * j0
      + 1) : ℝ)) * Bcoef (2 * j0 + 1 + 3) (k + 2) + ((3 / 5) + (1 / 5) * ((2 * j0 + 1) : ℝ))
      * Bcoef (2 * j0 + 1 + 3) (k + 1) + ((2 : ℝ) + (2 / 5) * ((2 * j0 + 1) : ℝ)) * Bcoef (2
      * j0 + 1 + 2) (k + 2) + ((-2 / 5) * ((2 * j0 + 1) : ℝ)) * Bcoef (2 * j0 + 1 + 2) (k + 1)
      + ((2 / 5) + (1 / 5) * ((2 * j0 + 1) : ℝ)) * Bcoef (2 * j0 + 1 + 1) (k + 2) + ((-7 / 5)
      + (-1 / 5) * ((2 * j0 + 1) : ℝ)) * Bcoef (2 * j0 + 1 + 1) (k + 1) + ((-13 / 5)
      + (-2 / 5) * ((2 * j0 + 1) : ℝ)) * Bcoef (2 * j0 + 1) (k + 2) + ((8 / 5) + (2 / 5) * ((2
      * j0 + 1) : ℝ)) * Bcoef (2 * j0 + 1) (k + 1)
      := by
  rcases lt_or_ge (k + 1) j0 with hk | hk
  · obtain ⟨a, rfl⟩ : ∃ a, j0 = k + 2 + a := ⟨j0 - (k + 2), by lia⟩
    rw [Bred (2 * (k + 2 + a) +1 + 4) (k + 2) (2 * k + a + 8) (a + 2) (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a) +1 + 3) (k + 2) (2 * k + a + 7) (a + 2) (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a) +1 + 3) (k + 1) (2 * k + a + 6) (a + 3) (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a) +1 + 2) (k + 2) (2 * k + a + 7) (a + 1) (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a) +1 + 2) (k + 1) (2 * k + a + 6) (a + 2) (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a) +1 + 1) (k + 2) (2 * k + a + 6) (a + 1) (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a) +1 + 1) (k + 1) (2 * k + a + 5) (a + 2) (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a) +1 + 0) (k + 2) (2 * k + a + 6) a (by lia) (by lia) (by lia)]
    rw [Bred (2 * (k + 2 + a) +1 + 0) (k + 1) (2 * k + a + 5) (a + 1) (by lia) (by lia) (by lia)]
    have H := odd_interior a k
    simp_all
  · rcases lt_or_ge k j0 with hk2 | hk2
    · have hj0 : j0 = k + 1 := by lia
      subst j0
      rw [Bred (2 * (k + 1) +1 + 4) (k + 2) (2 * k + 7) 1 (by lia) (by lia) (by lia)]
      rw [Bred (2 * (k + 1) +1 + 3) (k + 2) (2 * k + 6) 1 (by lia) (by lia) (by lia)]
      rw [Bred (2 * (k + 1) +1 + 3) (k + 1) (2 * k + 5) 2 (by lia) (by lia) (by lia)]
      rw [Bred (2 * (k + 1) +1 + 2) (k + 2) (2 * k + 6) 0 (by lia) (by lia) (by lia)]
      rw [Bred (2 * (k + 1) +1 + 2) (k + 1) (2 * k + 5) 1 (by lia) (by lia) (by lia)]
      rw [Bred (2 * (k + 1) +1 + 1) (k + 2) (2 * k + 5) 0 (by lia) (by lia) (by lia)]
      rw [Bred (2 * (k + 1) +1 + 1) (k + 1) (2 * k + 4) 1 (by lia) (by lia) (by lia)]
      rw [Bred0 (2 * (k + 1) +1 + 0) (k + 2) (by lia)]
      rw [Bred (2 * (k + 1) +1 + 0) (k + 1) (2 * k + 4) 0 (by lia) (by lia) (by lia)]
      have H := odd_km1 k
      grind
    · rcases lt_or_ge k (j0 + 1) with hk3 | hk3
      · have hj0 : j0 = k := by lia
        subst j0
        rw [Bred (2 * k + 1 + 4) (k + 2) (2 * k + 6) 0 (by lia) (by lia) (by lia)]
        rw [Bred (2 * k + 1 + 3) (k + 2) (2 * k + 5) 0 (by lia) (by lia) (by lia)]
        rw [Bred (2 * k + 1 + 3) (k + 1) (2 * k + 4) 1 (by lia) (by lia) (by lia)]
        rw [Bred0 (2 * k + 1 + 2) (k + 2) (by lia)]
        rw [Bred (2 * k + 1 + 2) (k + 1) (2 * k + 4) 0 (by lia) (by lia) (by lia)]
        rw [Bred0 (2 * k + 1 + 1) (k + 2) (by lia)]
        rw [Bred (2 * k + 1 + 1) (k + 1) (2 * k + 3) 0 (by lia) (by lia) (by lia)]
        rw [Bred0 (2 * k + 1) (k + 2) (by lia)]
        rw [Bred0 (2 * k + 1) (k + 1) (by lia)]
        have H := odd_keqj k
        grind
      · rcases lt_or_ge k (j0 + 2) with hk4 | hk4
        · have hj0 : j0 = k - 1 := by lia
          subst j0
          rw [Bred0 (2 * (k - 1) +1 + 4) (k + 2) (by lia)]
          rw [Bred0 (2 * (k - 1) +1 + 3) (k + 2) (by lia)]
          rw [Bred0 (2 * (k - 1) +1 + 2) (k + 2) (by lia)]
          rw [Bred0 (2 * (k - 1) +1 + 2) (k + 1) (by lia)]
          rw [Bred0 (2 * (k - 1) +1 + 1) (k + 2) (by lia)]
          rw [Bred0 (2 * (k - 1) +1 + 1) (k + 1) (by lia)]
          rw [Bred0 (2 * (k - 1) +1) (k + 2) (by lia)]
          rw [Bred0 (2 * (k - 1) +1) (k + 1) (by lia)]
          rw [Bred (2 * (k - 1) +1 + 3) (k + 1) (2 * k + 3) 0 (by lia) (by lia) (by lia)]
          simp only [Nat.choose_zero_right, Nat.cast_one]
          have hk1 : 1 ≤ k := by lia
          rw [Nat.cast_sub hk1]
          grind
        · rw [Bred0 (2 * j0 + 1 + 4) (k + 2) (by lia)]
          rw [Bred0 (2 * j0 + 1 + 3) (k + 2) (by lia)]
          rw [Bred0 (2 * j0 + 1 + 3) (k + 1) (by lia)]
          rw [Bred0 (2 * j0 + 1 + 2) (k + 2) (by lia)]
          rw [Bred0 (2 * j0 + 1 + 2) (k + 1) (by lia)]
          rw [Bred0 (2 * j0 + 1 + 1) (k + 2) (by lia)]
          rw [Bred0 (2 * j0 + 1 + 1) (k + 1) (by lia)]
          rw [Bred0 (2 * j0 + 1) (k + 2) (by lia)]
          rw [Bred0 (2 * j0 + 1) (k + 1) (by lia)]
          ring_nf

private lemma i0_step (m : ℕ) :
    Bcoef (m + 4) 0 = ((2 / 5) + (-1 / 5) * (m : ℝ)) * Bcoef (m + 3) 0 + ((2 : ℝ) + (2 / 5)
      * (m : ℝ)) * Bcoef (m + 2) 0 + ((2 / 5) + (1 / 5) * (m : ℝ)) * Bcoef (m + 1) 0
      + ((-13 / 5) + (-2 / 5) * (m : ℝ)) * Bcoef m 0
      := by
  rcases Nat.even_or_odd m with ⟨j0, hj0⟩ | ⟨j0, hj0⟩
  · obtain rfl : m = 2 * j0 := by lia
    rw [Bred (2 * j0 + 4) 0 (j0 + 3) (j0 + 2) (by lia) (by lia) (by lia)]
    rw [Bred (2 * j0 + 3) 0 (j0 + 3) (j0 + 1) (by lia) (by lia) (by lia)]
    rw [Bred (2 * j0 + 2) 0 (j0 + 2) (j0 + 1) (by lia) (by lia) (by lia)]
    rw [Bred (2 * j0 + 1) 0 (j0 + 2) j0 (by lia) (by lia) (by lia)]
    rw [Bred (2 * j0) 0 (j0 + 1) j0 (by lia) (by lia) (by lia)]
    have H := i0_even j0
    grind
  · obtain rfl : m = 2 * j0 + 1 := by assumption
    rw [Bred (2 * j0 + 1 + 4) 0 (j0 + 4) (j0 + 2) (by lia) (by lia) (by lia)]
    rw [Bred (2 * j0 + 1 + 3) 0 (j0 + 3) (j0 + 2) (by lia) (by lia) (by lia)]
    rw [Bred (2 * j0 + 1 + 2) 0 (j0 + 3) (j0 + 1) (by lia) (by lia) (by lia)]
    rw [Bred (2 * j0 + 1 + 1) 0 (j0 + 2) (j0 + 1) (by lia) (by lia) (by lia)]
    rw [Bred (2 * j0 + 1) 0 (j0 + 2) j0 (by lia) (by lia) (by lia)]
    have H := i0_odd j0
    grind

private lemma i1_step (m : ℕ) :
    Bcoef (m + 4) 1 = (2 / 5) * Bcoef (m + 3) 1 + (-4 / 5) * Bcoef (m + 2) 1 + (2 / 5)
      * Bcoef (m + 1) 1 + (-4 / 5) * Bcoef m 1 + ((2 / 5) + (-1 / 5) * (m : ℝ)) * Bcoef (m
      + 3) 1 + ((3 / 5) + (1 / 5) * (m : ℝ)) * Bcoef (m + 3) 0 + ((2 : ℝ) + (2 / 5) * (m : ℝ))
      * Bcoef (m + 2) 1 + ((-2 / 5) * (m : ℝ)) * Bcoef (m + 2) 0 + ((2 / 5) + (1 / 5)
      * (m : ℝ)) * Bcoef (m + 1) 1 + ((-7 / 5) + (-1 / 5) * (m : ℝ)) * Bcoef (m + 1) 0
      + ((-13 / 5) + (-2 / 5) * (m : ℝ)) * Bcoef m 1 + ((8 / 5) + (2 / 5) * (m : ℝ)) * Bcoef m 0
      := by
  rcases Nat.even_or_odd m with ⟨j0, hj0⟩ | ⟨j0, hj0⟩
  · obtain rfl : m = 2 * j0 := by lia
    rcases Nat.eq_zero_or_pos j0 with hj | hj
    · subst hj
      simp only [Bcoef]; norm_num
    · rw [Bred (2 * j0 + 4) 1 (j0 + 4) (j0 + 1) (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0 + 3) 1 (j0 + 4) j0 (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0 + 2) 1 (j0 + 3) j0 (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0 + 1) 1 (j0 + 3) (j0 - 1) (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0) 1 (j0 + 2) (j0 - 1) (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0 + 3) 0 (j0 + 3) (j0 + 1) (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0 + 2) 0 (j0 + 2) (j0 + 1) (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0 + 1) 0 (j0 + 2) j0 (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0) 0 (j0 + 1) j0 (by lia) (by lia) (by lia)]
      have H := i1_even j0 (by lia)
      grind
  · obtain rfl : m = 2 * j0 + 1 := by assumption
    rcases Nat.eq_zero_or_pos j0 with hj | hj
    · subst hj
      simp only [Bcoef]; norm_num
    · rw [Bred (2 * j0 + 1 + 4) 1 (j0 + 5) (j0 + 1) (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0 + 1 + 3) 1 (j0 + 4) (j0 + 1) (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0 + 1 + 2) 1 (j0 + 4) j0 (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0 + 1 + 1) 1 (j0 + 3) j0 (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0 + 1) 1 (j0 + 3) (j0 - 1) (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0 + 1 + 3) 0 (j0 + 3) (j0 + 2) (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0 + 1 + 2) 0 (j0 + 3) (j0 + 1) (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0 + 1 + 1) 0 (j0 + 2) (j0 + 1) (by lia) (by lia) (by lia)]
      rw [Bred (2 * j0 + 1) 0 (j0 + 2) j0 (by lia) (by lia) (by lia)]
      have H := i1_odd j0 (by lia)
      grind

private lemma A177040_coeff (n i : ℕ) :
    Polynomial.coeff (A177040 n) i = if i ≤ n / 2 then (Nat.choose (n - n / 2 + i
      + 1) (n / 2 - i) : ℝ) else 0
      := by
  induction n using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    match n with
    | 0 =>
      rcases i with _ | i
      · norm_num [A177040]
      · simp [A177040, coeff_one]
    | 1 =>
      rcases i with _ | i
      · norm_num [A177040]
      · simp [A177040, coeff_one]
    | 2 =>
      rcases i with _ | i | i
      · norm_num [A177040, coeff_add, coeff_X]
      · norm_num [A177040, coeff_add, coeff_X]
      · rw [ite_eq_right (by lia)]
        simp [A177040, coeff_add, coeff_X]
    | 3 =>
      rcases i with _ | i | i
      · norm_num [A177040, coeff_add, coeff_X]
      · norm_num [A177040, coeff_add, coeff_X]
      · rw [ite_eq_right (by lia)]
        simp [A177040, coeff_add, coeff_X]
    | (m + 4) =>
      -- change goal to Bcoef form
      change Polynomial.coeff (A177040 (m + 4)) i = Bcoef (m + 4) i
      rcases i with _ | _ | k
      · -- i = 0
        rw [A177040_coeff_zero m, i0_step m]
        have e3 := ih (m + 3) (by lia) 0
        have e2 := ih (m + 2) (by lia) 0
        have e1 := ih (m + 1) (by lia) 0
        have e0 := ih m (by lia) 0
        rw [show Bcoef (m + 3) 0 = Polynomial.coeff (A177040 (m + 3)) 0 from by rw [e3]; rfl,
            show Bcoef (m + 2) 0 = Polynomial.coeff (A177040 (m + 2)) 0 from by rw [e2]; rfl,
            show Bcoef (m + 1) 0 = Polynomial.coeff (A177040 (m + 1)) 0 from by rw [e1]; rfl,
            show Bcoef m 0 = Polynomial.coeff (A177040 m) 0 from by rw [e0]; rfl]
      · -- i = 1
        rw [A177040_coeff_one m, i1_step m]
        have e3a := ih (m + 3) (by lia) 1
        have e3b := ih (m + 3) (by lia) 0
        have e2a := ih (m + 2) (by lia) 1
        have e2b := ih (m + 2) (by lia) 0
        have e1a := ih (m + 1) (by lia) 1
        have e1b := ih (m + 1) (by lia) 0
        have e0a := ih m (by lia) 1
        have e0b := ih m (by lia) 0
        rw [show Bcoef (m + 3) 1 = Polynomial.coeff (A177040 (m + 3)) 1 from by rw [e3a]; rfl,
            show Bcoef (m + 3) 0 = Polynomial.coeff (A177040 (m + 3)) 0 from by rw [e3b]; rfl,
            show Bcoef (m + 2) 1 = Polynomial.coeff (A177040 (m + 2)) 1 from by rw [e2a]; rfl,
            show Bcoef (m + 2) 0 = Polynomial.coeff (A177040 (m + 2)) 0 from by rw [e2b]; rfl,
            show Bcoef (m + 1) 1 = Polynomial.coeff (A177040 (m + 1)) 1 from by rw [e1a]; rfl,
            show Bcoef (m + 1) 0 = Polynomial.coeff (A177040 (m + 1)) 0 from by rw [e1b]; rfl,
            show Bcoef m 1 = Polynomial.coeff (A177040 m) 1 from by rw [e0a]; rfl,
            show Bcoef m 0 = Polynomial.coeff (A177040 m) 0 from by rw [e0b]; rfl]
        ring_nf
      · -- i = k+2
        rcases Nat.even_or_odd m with ⟨j0, hj0⟩ | ⟨j0, hj0⟩
        · obtain rfl : m = 2 * j0 := by lia
          rw [A177040_coeff_succ (2 * j0) k, even_step j0 k]
          have e3a := ih (2 * j0 + 3) (by lia) (k + 2)
          have e3b := ih (2 * j0 + 3) (by lia) (k + 1)
          have e2a := ih (2 * j0 + 2) (by lia) (k + 2)
          have e2b := ih (2 * j0 + 2) (by lia) (k + 1)
          have e1a := ih (2 * j0 + 1) (by lia) (k + 2)
          have e1b := ih (2 * j0 + 1) (by lia) (k + 1)
          have e0a := ih (2 * j0) (by lia) (k + 2)
          have e0b := ih (2 * j0) (by lia) (k + 1)
          rw [show Bcoef (2 * j0 + 3) (k + 2) = Polynomial.coeff (A177040 (2 * j0 + 3)) (k + 2)
            from by rw [e3a]; rfl,
              show Bcoef (2 * j0 + 3) (k + 1) = Polynomial.coeff (A177040 (2 * j0 + 3)) (k + 1)
                from by rw [e3b]; rfl,
              show Bcoef (2 * j0 + 2) (k + 2) = Polynomial.coeff (A177040 (2 * j0 + 2)) (k + 2)
                from by rw [e2a]; rfl,
              show Bcoef (2 * j0 + 2) (k + 1) = Polynomial.coeff (A177040 (2 * j0 + 2)) (k + 1)
                from by rw [e2b]; rfl,
              show Bcoef (2 * j0 + 1) (k + 2) = Polynomial.coeff (A177040 (2 * j0 + 1)) (k + 2)
                from by rw [e1a]; rfl,
              show Bcoef (2 * j0 + 1) (k + 1) = Polynomial.coeff (A177040 (2 * j0 + 1)) (k + 1)
                from by rw [e1b]; rfl,
              show Bcoef (2 * j0) (k + 2) = Polynomial.coeff (A177040 (2 * j0)) (k + 2)
                from by rw [e0a]; rfl,
              show Bcoef (2 * j0) (k + 1) = Polynomial.coeff (A177040 (2 * j0)) (k + 1)
                from by rw [e0b]; rfl]
          grind
        · obtain rfl : m = 2 * j0 + 1 := by assumption
          rw [A177040_coeff_succ (2 * j0 + 1) k, odd_step j0 k]
          have e3a := ih (2 * j0 + 1 + 3) (by lia) (k + 2)
          have e3b := ih (2 * j0 + 1 + 3) (by lia) (k + 1)
          have e2a := ih (2 * j0 + 1 + 2) (by lia) (k + 2)
          have e2b := ih (2 * j0 + 1 + 2) (by lia) (k + 1)
          have e1a := ih (2 * j0 + 1 + 1) (by lia) (k + 2)
          have e1b := ih (2 * j0 + 1 + 1) (by lia) (k + 1)
          have e0a := ih (2 * j0 + 1) (by lia) (k + 2)
          have e0b := ih (2 * j0 + 1) (by lia) (k + 1)
          rw [show Bcoef (2 * j0 + 1 + 3) (k + 2) = Polynomial.coeff (A177040 (2 * j0 + 1
            + 3)) (k + 2)
            from by rw [e3a]; rfl,
              show Bcoef (2 * j0 + 1 + 3) (k + 1) = Polynomial.coeff (A177040 (2 * j0 + 1
                + 3)) (k + 1)
                from by rw [e3b]; rfl,
              show Bcoef (2 * j0 + 1 + 2) (k + 2) = Polynomial.coeff (A177040 (2 * j0 + 1
                + 2)) (k + 2)
                from by rw [e2a]; rfl,
              show Bcoef (2 * j0 + 1 + 2) (k + 1) = Polynomial.coeff (A177040 (2 * j0 + 1
                + 2)) (k + 1)
                from by rw [e2b]; rfl,
              show Bcoef (2 * j0 + 1 + 1) (k + 2) = Polynomial.coeff (A177040 (2 * j0 + 1
                + 1)) (k + 2)
                from by rw [e1a]; rfl,
              show Bcoef (2 * j0 + 1 + 1) (k + 1) = Polynomial.coeff (A177040 (2 * j0 + 1
                + 1)) (k + 1)
                from by rw [e1b]; rfl,
              show Bcoef (2 * j0 + 1) (k + 2) = Polynomial.coeff (A177040 (2 * j0 + 1)) (k + 2)
                from by rw [e0a]; rfl,
              show Bcoef (2 * j0 + 1) (k + 1) = Polynomial.coeff (A177040 (2 * j0 + 1)) (k + 1)
                from by rw [e0b]; rfl]
          grind

private lemma A177040_natDegree_raw (n : ℕ) : (A177040 n).natDegree = n / 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    rw [A177040_coeff n m, ite_eq_right (by lia)]
  · rw [A177040_coeff n (n / 2), ite_eq_left (le_refl _)]
    simp

/-- The A177040 row indexed by `n` has degree `n / 2` and positive leading
coefficient.  The proof carries the exact even and odd coefficient vectors as two separate
states of the parity top-window law. -/
theorem A177040_natDegree_eq_and_leadingCoeff_pos (n : ℕ) :
    (A177040 n).natDegree = n / 2 ∧ 0 < (A177040 n).leadingCoeff := by
  refine ⟨A177040_natDegree_raw n, ?_⟩
  rw [leadingCoeff, A177040_natDegree_raw, A177040_coeff,
    ite_eq_left (le_refl (n / 2))]
  simp

/-- The natural degree of the A177040 row indexed by `n` is `n / 2`. -/
theorem A177040_natDegree (n : ℕ) : (A177040 n).natDegree = n / 2 :=
  (A177040_natDegree_eq_and_leadingCoeff_pos n).1

/-- Every A177040 row has leading coefficient one. -/
theorem A177040_leadingCoeff (n : ℕ) : (A177040 n).leadingCoeff = 1 := by
  rw [leadingCoeff, A177040_natDegree n, A177040_coeff,
    ite_eq_left (le_refl (n / 2))]
  simp

/-- The A177040 row indexed by `n` has positive leading coefficient. -/
theorem A177040_leadingCoeff_pos (n : ℕ) : 0 < (A177040 n).leadingCoeff := by
  rw [A177040_leadingCoeff]
  norm_num

/-- The order-four update of the A177040 rows. -/
def A177040Next (n : ℕ) (p₃ p₂ p₁ p₀ : ℝ[X]) : ℝ[X] :=
  (C (2 / 5) * X + C (-2 / 5) * X ^ 2) * p₃.derivative
    + (C (-4 / 5) * X + C (4 / 5) * X ^ 2) * p₂.derivative
    + (C (2 / 5) * X + C (-2 / 5) * X ^ 2) * p₁.derivative
    + (C (-4 / 5) * X + C (4 / 5) * X ^ 2) * p₀.derivative
    + (C (2 / 5 + (-1 / 5) * (n : ℝ)) +
        C (3 / 5 + (1 / 5) * (n : ℝ)) * X) * p₃
    + (C (2 + (2 / 5) * (n : ℝ)) + C ((-2 / 5) * (n : ℝ)) * X) * p₂
    + (C (2 / 5 + (1 / 5) * (n : ℝ)) +
        C (-7 / 5 + (-1 / 5) * (n : ℝ)) * X) * p₁
    + (C (-13 / 5 + (-2 / 5) * (n : ℝ)) +
        C (8 / 5 + (2 / 5) * (n : ℝ)) * X) * p₀

private theorem A177040_step (n : ℕ) :
    A177040 (n + 4) = A177040Next n (A177040 (n + 3))
      (A177040 (n + 2)) (A177040 (n + 1)) (A177040 n) := by
  rw [A177040]
  dsimp only [A177040Next]
  ring

/-- Any sequence satisfying the A177040 initial window and update has degree `n / 2`. -/
@[rr_row_model]
theorem A177040_natDegree_of_recurrence
    {P : ℕ → ℝ[X]}
    (hinit : ∀ i < 4, P i = A177040 i)
    (hrec : ∀ n, P (n + 4) =
      A177040Next n (P (n + 3)) (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).natDegree = n / 2 := by
  have heq : ∀ m, P m = A177040 m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        by_cases hm : m < 4
        · exact hinit m hm
        · obtain ⟨q, rfl⟩ : ∃ q, m = q + 4 := ⟨m - 4, by lia⟩
          rw [hrec, A177040_step, ih (q + 3) (by lia),
            ih (q + 2) (by lia), ih (q + 1) (by lia), ih q (by lia)]
  rw [heq n]
  exact A177040_natDegree n

end

end RealRooted.Tactic.RowParityDegree
