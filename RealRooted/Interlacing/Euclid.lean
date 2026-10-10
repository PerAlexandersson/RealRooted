import RealRooted.MaWang.Weak.Endpoint
import RealRooted.ThreeTermRecurrence.Interlacing
import RealRooted.ThreeTermRecurrence.Degree
import RealRooted.WagnerX.AffineFactors

/-!
# Interlacing certificates for explicit polynomials

**Euclidean step.** If `h` interlaces `g` and `f = q * g - h`, where `h` and `f` have
positive leading coefficients and `deg f = deg g + 1`, then `g` interlaces `f`.
Applied along the Euclidean remainder sequence, this proves `g ≪ f` for explicit
polynomials: divide `f` by `g`, check that the remainder has a negative leading
coefficient, and recurse, down to a constant interlacing a linear polynomial.

**Common factors.** Multiplying both members of an interlacing pair by a nonzero
real-rooted polynomial preserves interlacing.  Hence, for `P (n + 2) = q * P n`, all
consecutive rows interlace once `P 0 ≪ P 1` and `P 1 ≪ q * P 0`
(`twoStepProduct_interlaces`).
-/

open Polynomial

namespace RealRooted

/-- A polynomial whose coefficient in its degree is positive has positive leading
coefficient. -/
theorem hasPosLeadingCoeff_of_natDegree_eq {p : ℝ[X]} {n : ℕ} (hdeg : p.natDegree = n)
    (hc : 0 < p.coeff n) : HasPosLeadingCoeff p := by
  unfold HasPosLeadingCoeff Polynomial.leadingCoeff
  rwa [hdeg]

/-- One Euclidean step: `h ≪ g` and `f = q g - h` give `g ≪ f`. -/
theorem interlaces_of_euclid_step {f g h q : ℝ[X]} (hrec : Interlaces h g)
    (hf : f = q * g - h) (hh_pos : HasPosLeadingCoeff h) (hf_pos : HasPosLeadingCoeff f)
    (hdeg : g.natDegree + 1 = f.natDegree) : Interlaces g f := by
  have hF : q * g + (-1) * h = f := by rw [hf]; ring
  have hstep := strictInterl_of_interlaces_evalCoeff_nonpos (f := g) (g := h) (a := q)
    (b := -1) hrec hh_pos (by rwa [hF]) (by rw [hF]; lia) (by rw [hF]; lia)
    (fun r _ => by simp)
  rw [hF] at hstep
  exact hstep.toInterlaces hdeg

/-- The Euclidean step with explicit degrees and top coefficients, as a tactic
consumes it: `deg h = m`, `deg g = m + 1`, `deg f = m + 2`. -/
theorem interlaces_of_euclid_step_of_natDegree {f g h q : ℝ[X]} {m : ℕ}
    (hrec : Interlaces h g) (hf : f = q * g - h) (hh_deg : h.natDegree = m)
    (hh_c : 0 < h.coeff m) (hg_deg : g.natDegree = m + 1) (hf_deg : f.natDegree = m + 2)
    (hf_c : 0 < f.coeff (m + 2)) : Interlaces g f :=
  interlaces_of_euclid_step hrec hf (hasPosLeadingCoeff_of_natDegree_eq hh_deg hh_c)
    (hasPosLeadingCoeff_of_natDegree_eq hf_deg hf_c) (by rw [hg_deg, hf_deg])

/-- Multiplying both members by `∏ (X - r)` preserves strict interlacing. -/
theorem StrictInterl.mul_prod_X_sub_C_both {f g : ℝ[X]} (h : StrictInterl f g)
    (s : Multiset ℝ) :
    StrictInterl ((s.map (X - C ·)).prod * f) ((s.map (X - C ·)).prod * g) := by
  induction s using Multiset.induction_on with
  | empty => simpa using h
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, mul_assoc]
      exact ih.mul_X_sub_C_both a

/-- Multiplying both members by a nonzero real-rooted polynomial preserves strict
interlacing. -/
theorem StrictInterl.mul_both_of_splits {f g q : ℝ[X]} (h : StrictInterl f g)
    (hq : q.Splits) (hq0 : q ≠ 0) : StrictInterl (q * f) (q * g) := by
  have hlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
  rw [hq.eq_prod_roots, mul_assoc, mul_assoc]
  exact ((h.mul_prod_X_sub_C_both q.roots).C_mul_left hlc).C_mul_right hlc

/-- Multiplying both members by a nonzero real-rooted polynomial preserves
interlacing. -/
theorem Interlaces.mul_both_of_splits {g f q : ℝ[X]} (h : Interlaces g f)
    (hq : q.Splits) (hq0 : q ≠ 0) : Interlaces (q * g) (q * f) := by
  have hg0 : g ≠ 0 := h.2.1.1
  have hf0 : f ≠ 0 := h.1.1
  refine (h.toStrictInterl.mul_both_of_splits hq hq0).toInterlaces ?_
  rw [natDegree_mul hq0 hg0, natDegree_mul hq0 hf0, ← h.2.2.1]
  ring

/-- Consecutive rows of a two-step product `P (n + 2) = q * P n` interlace, given
`P 0 ≪ P 1` and `P 1 ≪ q * P 0`, for a nonzero real-rooted `q`. -/
theorem twoStepProduct_interlaces {P : ℕ → ℝ[X]} {q : ℝ[X]}
    (hrec : ∀ n, P (n + 2) = q * P n) (hq : q.Splits) (hq0 : q ≠ 0)
    (h01 : Interlaces (P 0) (P 1)) (h12 : Interlaces (P 1) (q * P 0)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have hqm : ∀ m, (q ^ m).Splits ∧ q ^ m ≠ 0 := fun m => ⟨hq.pow m, pow_ne_zero m hq0⟩
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨h0, h1⟩ := twoStepProduct_rows hrec m
    rw [h0, h1]
    exact h01.mul_both_of_splits (hqm m).1 (hqm m).2
  · obtain ⟨-, h1⟩ := twoStepProduct_rows hrec m
    obtain ⟨h0', -⟩ := twoStepProduct_rows hrec (m + 1)
    rw [h1, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, h0', pow_succ, mul_assoc]
    exact h12.mul_both_of_splits (hqm m).1 (hqm m).2

end RealRooted

/-!
## Splitting of two-step products

If `P (n + 2) = q n * P n` and all the factors `q n` split, then every row `P n` splits
as soon as `P 0` and `P 1` do.
-/

open Polynomial

namespace RealRooted

/-- Rows of a product sequence `P (n + 1) = q n * P n` split when every factor and the first row
split (no degree condition on the factors). -/
theorem productSequence_splits {P q : ℕ → ℝ[X]} (hrec : ∀ n, P (n + 1) = q n * P n)
    (hq : ∀ n, (q n).Splits) (h0 : (P 0).Splits) (n : ℕ) : (P n).Splits := by
  induction n with
  | zero => exact h0
  | succ n ih => rw [hrec]; exact (hq n).mul ih

/-- Rows of a two-step product recurrence `P (n + 2) = q n * P n` split when `P 0`, `P 1`
and every factor `q n` split. -/
theorem twoStepProduct_splits {P q : ℕ → ℝ[X]} (hrec : ∀ n, P (n + 2) = q n * P n)
    (hq : ∀ n, (q n).Splits) (h0 : (P 0).Splits) (h1 : (P 1).Splits) (n : ℕ) :
    (P n).Splits := by
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih _ => rw [hrec]; exact (hq n).mul ih

example {P : ℕ → ℝ[X]} (hrec : ∀ n, P (n + 2) = (1 + X) * P n) (h0 : P 0 = 1)
    (h1 : P 1 = 1 + X) (n : ℕ) : (P n).Splits := by
  have hX : (1 + X : ℝ[X]).Splits := by
    simpa [add_comm] using Splits.X_sub_C (-1 : ℝ)
  refine twoStepProduct_splits (q := fun _ => 1 + X) hrec (fun _ => hX) ?_ ?_ n
  · rw [h0]; exact Splits.one
  · rw [h1]; exact hX

end RealRooted
