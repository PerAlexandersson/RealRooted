/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CenteredEulerian.FormalArcsin
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.Algebra.Order.Algebra
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.Positivity.Finset

/-!
# Parity of the basic formal series

We express parity through `rescale (-1)`, i.e. `g(-X) = ± g(X)`.
Adapted from Aristotle's centered-disk proof, `RequestProject/Parity.lean` (2026-10-23).
-/

@[expose] public section

open PowerSeries

namespace RealRooted.CenteredEulerian

/-- Even formal power series. -/
def IsEvenPS (g : ℝ⟦X⟧) : Prop := rescale (-1 : ℝ) g = g
/-- Odd formal power series. -/
def IsOddPS (g : ℝ⟦X⟧) : Prop := rescale (-1 : ℝ) g = -g

lemma IsEvenPS.coeff_odd {g : ℝ⟦X⟧} (h : IsEvenPS g) {n : ℕ} (hn : Odd n) :
    coeff n g = 0 := by
  have := congrArg (coeff n) h
  rw [coeff_rescale, hn.neg_one_pow] at this
  linarith

lemma IsOddPS.coeff_even {g : ℝ⟦X⟧} (h : IsOddPS g) {n : ℕ} (hn : Even n) :
    coeff n g = 0 := by
  have := congrArg (coeff n) h
  rw [coeff_rescale, hn.neg_one_pow, map_neg] at this
  linarith

lemma isEvenPS_of_coeff {g : ℝ⟦X⟧} (h : ∀ n, Odd n → coeff n g = 0) : IsEvenPS g := by
  ext n
  rw [coeff_rescale]
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_one_pow, one_mul]
  · rw [h n hn, mul_zero]

lemma isOddPS_of_coeff {g : ℝ⟦X⟧} (h : ∀ n, Even n → coeff n g = 0) : IsOddPS g := by
  ext n
  rw [coeff_rescale, map_neg]
  rcases Nat.even_or_odd n with hn | hn
  · rw [h n hn, mul_zero, neg_zero]
  · rw [hn.neg_one_pow]; ring

lemma IsEvenPS.mul {f g : ℝ⟦X⟧} (hf : IsEvenPS f) (hg : IsEvenPS g) : IsEvenPS (f * g) := by
  unfold IsEvenPS at *; rw [map_mul, hf, hg]

lemma IsOddPS.mul_odd {f g : ℝ⟦X⟧} (hf : IsOddPS f) (hg : IsOddPS g) : IsEvenPS (f * g) := by
  unfold IsEvenPS IsOddPS at *; rw [map_mul, hf, hg]; ring

lemma IsEvenPS.mul_odd {f g : ℝ⟦X⟧} (hf : IsEvenPS f) (hg : IsOddPS g) : IsOddPS (f * g) := by
  unfold IsEvenPS IsOddPS at *; rw [map_mul, hf, hg]; ring

lemma rescale_neg_one_pow_odd {f : ℝ⟦X⟧} (hf : IsOddPS f) (k : ℕ) :
    rescale (-1 : ℝ) (f ^ k) = (-1) ^ k * f ^ k := by
  rw [map_pow, hf, neg_pow]

lemma IsEvenPS.inv {g : ℝ⟦X⟧} (hg : IsEvenPS g) (h0 : constantCoeff g ≠ 0) :
    IsEvenPS g⁻¹ := by
  unfold IsEvenPS at *
  have h1 : g * g⁻¹ = 1 := PowerSeries.mul_inv_cancel _ h0
  have h2 : rescale (-1 : ℝ) g * rescale (-1 : ℝ) g⁻¹ = 1 := by rw [← map_mul, h1, map_one]
  rw [hg] at h2
  have hne : g ≠ 0 := by intro h; rw [h, map_zero] at h0; exact h0 rfl
  exact mul_left_cancel₀ hne (h2.trans h1.symm)

lemma isOddPS_sinS : IsOddPS sinS :=
  isOddPS_of_coeff (fun n hn => by rw [coeff_sinS, ite_eq_left hn])

lemma isEvenPS_cosS : IsEvenPS cosS := isEvenPS_of_coeff (fun n hn => by
  rw [coeff_cosS, ite_eq_right (Nat.not_even_iff_odd.mpr hn)])

lemma isEvenPS_secS : IsEvenPS secS :=
  isEvenPS_cosS.inv (by rw [constantCoeff_cosS]; norm_num)

lemma qc_odd (r : ℕ) : qc (2 * r + 1) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by ring, qc, ih, mul_zero]

lemma isEvenPS_qS : IsEvenPS qS := isEvenPS_of_coeff (fun n hn => by
  obtain ⟨r, rfl⟩ := hn; rw [qS, coeff_mk, qc_odd])

lemma isEvenPS_invqS : IsEvenPS invqS :=
  isEvenPS_qS.inv (by rw [constantCoeff_qS]; norm_num)

lemma isOddPS_fS : IsOddPS fS := isOddPS_of_coeff (fun n hn => by
  rw [fS, coeff_mk]
  rcases n with _ | n
  · rfl
  · rw [fc, isEvenPS_invqS.coeff_odd (by
      rcases hn with ⟨r, hr⟩; exact ⟨r - 1, by lia⟩), zero_div])

lemma pow_parity_odd {f : ℝ⟦X⟧} (hf : IsOddPS f) (k : ℕ) :
    (Even k → IsEvenPS (f ^ k)) ∧ (Odd k → IsOddPS (f ^ k)) := by
  constructor
  · intro hk; unfold IsEvenPS; rw [rescale_neg_one_pow_odd hf, hk.neg_one_pow, one_mul]
  · intro hk; unfold IsOddPS; rw [rescale_neg_one_pow_odd hf, hk.neg_one_pow]; ring

/-- Parity of a product of an even series with the `k`-th power of an odd series. -/
lemma coeff_even_mul_odd_pow_eq_zero {e f : ℝ⟦X⟧} (he : IsEvenPS e) (hf : IsOddPS f)
    {n k : ℕ} (h : ¬ (Even n ↔ Even k)) : coeff n (e * f ^ k) = 0 := by
  rcases Nat.even_or_odd k with hk | hk
  · have := he.mul ((pow_parity_odd hf k).1 hk)
    have hn : Odd n := by
      rw [← Nat.not_even_iff_odd]; intro hn; exact h ⟨fun _ => hk, fun _ => hn⟩
    exact this.coeff_odd hn
  · have := he.mul_odd ((pow_parity_odd hf k).2 hk)
    have hn : Even n := by
      by_contra hn; apply h
      exact ⟨fun h' => absurd h' hn, fun h' => absurd h' (Nat.not_even_iff_odd.mpr hk)⟩
    exact this.coeff_even hn

end RealRooted.CenteredEulerian
