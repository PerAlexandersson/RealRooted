import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Chow polynomial operator

This module packages the quotient operator occurring in the defining recursion
for Chow and Chow-derangement polynomials.  It is stated over a commutative
ring, independently of any matrix or positivity assumptions.
-/

open Polynomial

namespace Polynomial

noncomputable section

/-- The Chow operator `Sₙ(p) = (reflect n p - p) / (X - 1)`.

For `p.natDegree ≤ n`, the numerator vanishes at one, so the quotient is exact;
see `X_sub_one_mul_chowS`. -/
def chowS {R : Type*} [CommRing R] (n : ℕ) (p : R[X]) : R[X] :=
  (p.reflect n - p) /ₘ (X - 1)

/-- The defining quotient for `chowS` is exact at every reflection bound at
least the degree of the input. -/
theorem X_sub_one_mul_chowS {R : Type*} [CommRing R]
    (n : ℕ) (p : R[X]) (hdegree : p.natDegree ≤ n) :
    (X - 1) * chowS n p = p.reflect n - p := by
  let _ := invertibleOne (α := R)
  have heval : (p.reflect n).eval 1 = p.eval 1 := by
    simpa using eval₂_reflect_mul_pow (RingHom.id R) (1 : R) n p hdegree
  have hmod : (p.reflect n - p) %ₘ (X - 1) = 0 := by
    change (p.reflect n - p) %ₘ (X - C (1 : R)) = 0
    rw [modByMonic_X_sub_C_eq_C_eval]
    simp [heval]
  change (X - 1) * ((p.reflect n - p) /ₘ (X - 1)) = p.reflect n - p
  calc
    (X - 1) * ((p.reflect n - p) /ₘ (X - 1)) =
        (p.reflect n - p) %ₘ (X - 1) + (X - 1) * ((p.reflect n - p) /ₘ (X - 1)) := by
      rw [hmod, zero_add]
    _ = p.reflect n - p := modByMonic_add_div _ _

/-- The Chow operator at a degree bound has degree at most that bound. -/
theorem natDegree_chowS_le {R : Type*} [CommRing R]
    (n : ℕ) (p : R[X]) (hdegree : p.natDegree ≤ n) :
    (chowS n p).natDegree ≤ n := by
  change ((p.reflect n - p).divByMonic (X - 1)).natDegree ≤ n
  refine (natDegree_le_natDegree (degree_divByMonic_le _ _)).trans ?_
  refine (natDegree_sub_le _ _).trans (max_le ?_ hdegree)
  simpa [max_eq_left hdegree] using (natDegree_reflect_le (N := n) (p := p))

/-- The Chow operator is anti-reciprocal before multiplication by `X`: after
reflection at the same bound it acquires precisely that factor. -/
theorem reflect_chowS {R : Type*} [CommRing R]
    (n : ℕ) (p : R[X]) (hdegree : p.natDegree ≤ n) :
    (chowS n p).reflect n = X * chowS n p := by
  have hreflect_succ (q : R[X]) (hqdeg : q.natDegree ≤ n) :
      q.reflect (n + 1) = q.reflect n * X := by
    simpa [Nat.add_comm] using
      (reflect_mul q (1 : R[X]) (F := n) (G := 1) hqdeg (by simp))
  have hrdeg : (p.reflect n).natDegree ≤ n :=
    by simpa [max_eq_left hdegree] using (natDegree_reflect_le (N := n) (p := p))
  have hqdeg : (p.reflect n - p).natDegree ≤ n :=
    (natDegree_sub_le _ _).trans (max_le hrdeg hdegree)
  have hq : (p.reflect n - p).reflect (n + 1) = -X * (p.reflect n - p) := by
    rw [reflect_sub, hreflect_succ (p.reflect n) hrdeg, hreflect_succ p hdegree,
      reflect_reflect]
    ring
  have hs := X_sub_one_mul_chowS n p hdegree
  have hsdeg : (chowS n p).natDegree ≤ n := natDegree_chowS_le n p hdegree
  have hreflect : ((X - 1) * chowS n p).reflect (n + 1) =
      (1 - X) * (chowS n p).reflect n := by
    rw [show n + 1 = 1 + n by lia,
      reflect_mul _ _ (by
        calc
          (X - 1 : R[X]).natDegree ≤ max X.natDegree (1 : R[X]).natDegree := natDegree_sub_le _ _
          _ ≤ 1 := by
            apply max_le
            · exact natDegree_X_le
            · simp) hsdeg]
    congr 1
    ext k
    simp
  have htrans := congrArg (fun q : R[X] => q.reflect (n + 1)) hs
  rw [hreflect, hq] at htrans
  have hmul : (X - 1) * (chowS n p).reflect n = (X - 1) * (X * chowS n p) := by
    calc
      (X - 1) * (chowS n p).reflect n = -((1 - X) * (chowS n p).reflect n) := by ring
      _ = -(-X * (p.reflect n - p)) := by rw [htrans]
      _ = -(-X * ((X - 1) * chowS n p)) := by rw [← hs]
      _ = (X - 1) * (X * chowS n p) := by ring
  exact (monic_X_sub_C (1 : R)).isRegular.left hmul

end

end Polynomial
