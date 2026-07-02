import RealRooted.Tactic.Favard
import RealRooted.Tactic.Sign

/-!
# OEIS recurrence test bed

Executable side-condition tests for selected OEIS recurrences from the
`real-rooted-oeis` project.  These are not full sequence formalizations yet:
they record the certificate fragments that the tactic layer should dispatch
once each OEIS family exposes its recurrence identity, degree data, root
interval, and base cases.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-! ## Ma--Wang Family A: Eulerian one-step differential factors -/

-- `A008517`: `v_n(t)=t(1-t)`.
example {r : ℝ} (hr : r ≤ 0) :
    (C (1 : ℝ) * X * (1 - X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A120434`: permutations by big descents, again `v_n(t)=t(1-t)`.
example {r : ℝ} (hr : r ≤ 0) :
    (C (1 : ℝ) * X * (1 - X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A156919`: Dirichlet-eta related table, `v_n(t)=2t(1-t)`.
example {r : ℝ} (hr : r ≤ 0) :
    (C (2 : ℝ) * X * (1 - X) : ℝ[X]).eval r ≤ 0 := by
  rr_sign

/-! ## Ma--Wang Family B: half-line first-derivative factors -/

-- `A321966`: OEIS-stated conjecture target, `v_n(t)=2t`.
example {r : ℝ} (hr : r ≤ 0) :
    (C (2 : ℝ) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A322944`: OEIS-stated conjecture target, `v_n(t)=3t`.
example {r : ℝ} (hr : r ≤ 0) :
    (C (3 : ℝ) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

/-! ## Liu--Wang Family E: positive `t`-lag factors -/

-- `A049403`: `B_n(t)=(n-1)t`.
example {n : Nat} (hn : 1 ≤ n) {r : ℝ} (hr : r ≤ 0) :
    (C ((n : ℝ) - 1) * X : ℝ[X]).eval r ≤ 0 := by
  have hc : 0 ≤ (n : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast hn)
  rr_sign

-- `A061896`: Lucas-polynomial coefficient triangle, `B_n(t)=t`.
example {r : ℝ} (hr : r ≤ 0) :
    (C (1 : ℝ) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A100862`: matching polynomial triangle, `B_n(t)=(n-2)t`.
example {n : Nat} (hn : 2 ≤ n) {r : ℝ} (hr : r ≤ 0) :
    (C ((n : ℝ) - 2) * X : ℝ[X]).eval r ≤ 0 := by
  have hc : 0 ≤ (n : ℝ) - 2 := by
    exact sub_nonneg.mpr (by exact_mod_cast hn)
  rr_sign

-- `A154227`: triangular-number lag coefficient, `B_n(t)=n(n+1)t/2`.
example {n : Nat} {r : ℝ} (hr : r ≤ 0) :
    (C (((n : ℝ) * ((n : ℝ) + 1)) / 2) * X : ℝ[X]).eval r ≤ 0 := by
  have hc : 0 ≤ ((n : ℝ) * ((n : ℝ) + 1)) / 2 := by
    positivity
  rr_sign

-- `A249248`: shifted positive lag coefficient, `B_n(t)=(n+2)t`.
example {n : Nat} {r : ℝ} (hr : r ≤ 0) :
    (C ((n : ℝ) + 2) * X : ℝ[X]).eval r ≤ 0 := by
  have hc : 0 ≤ (n : ℝ) + 2 := by
    positivity
  rr_sign

/-! ## Liu--Wang Family G: Narayana/Jacobi negative-square lag factors -/

-- `A001263`: Narayana/Catalan rows, `B_n(t)=-(n/(n+3))(1-t)^2`.
example {n : Nat} {r : ℝ} :
    (-(C ((n : ℝ) / ((n : ℝ) + 3))) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hc : 0 ≤ (n : ℝ) / ((n : ℝ) + 3) := by
    positivity
  rr_sign

-- `A091044`: Pascal odd-entry triangle, `B_n(t)=-(1-t)^2`.
example {r : ℝ} :
    (-(C (1 : ℝ)) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A145596`: generalized Narayana rows, `B_n(t)=-(n/(n+3))(1-t)^2`.
example {n : Nat} {r : ℝ} :
    (-(C ((n : ℝ) / ((n : ℝ) + 3))) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hc : 0 ≤ (n : ℝ) / ((n : ℝ) + 3) := by
    positivity
  rr_sign

-- `A178343`: beta-binomial rows, `B_n(t)=-(n/(n-1))(1-t)^2`, active for `n>=2`.
example {n : Nat} (hn : 2 ≤ n) {r : ℝ} :
    (-(C ((n : ℝ) / ((n : ℝ) - 1))) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hden : 0 < (n : ℝ) - 1 := by
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hc : 0 ≤ (n : ℝ) / ((n : ℝ) - 1) := by
    positivity
  rr_sign

/-! ## Favard/Chebyshev Family F dispatcher skeleton -/

-- `A049310`: Chebyshev `S(n,x)=U(n,x/2)` coefficient triangle.
example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hbeta : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_favard using hrec, hbeta

end Tactic
end RealRooted
