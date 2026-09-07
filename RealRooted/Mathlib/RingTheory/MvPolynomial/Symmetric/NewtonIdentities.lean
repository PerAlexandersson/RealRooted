/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

import Mathlib.Data.Multiset.Fintype

/-!
# Evaluated Newton identities

This file evaluates Mathlib's multivariate power sums on a finite family and
packages the result as a multiplicity-preserving multiset API.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ R S : Type*} [Fintype σ] [CommSemiring R] [CommSemiring S]
  [Algebra R S]

/-- Evaluating a multivariate power sum gives the sum of the corresponding
powers of the values. -/
theorem aeval_psum (f : σ → S) (n : ℕ) :
    aeval f (psum σ R n) = ∑ i, f i ^ n := by
  simp [psum]

end MvPolynomial

namespace Multiset

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The sum of the `k`th powers of the elements of a multiset. -/
def powerSum (s : Multiset R) (k : ℕ) : R :=
  (s.map fun x => x ^ k).sum

@[simp] theorem zero_powerSum (k : ℕ) : (0 : Multiset R).powerSum k = 0 := by
  simp [powerSum]

@[simp] theorem powerSum_zero (s : Multiset R) : s.powerSum 0 = s.card := by
  simp [powerSum]

@[simp] theorem powerSum_one (s : Multiset R) : s.powerSum 1 = s.sum := by
  simp [powerSum]

@[simp] theorem powerSum_cons (x : R) (s : Multiset R) (k : ℕ) :
    (x ::ₘ s).powerSum k = x ^ k + s.powerSum k := by
  simp [powerSum]

@[simp] theorem powerSum_add (s t : Multiset R) (k : ℕ) :
    (s + t).powerSum k = s.powerSum k + t.powerSum k := by
  simp [powerSum]

end CommSemiring

@[simp] theorem map_powerSum {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (s : Multiset R) (k : ℕ) :
    f (s.powerSum k) = (s.map f).powerSum k := by
  rw [powerSum]
  calc
    f (s.map fun x => x ^ k).sum =
        ((s.map fun x => x ^ k).map f).sum :=
      f.toAddMonoidHom.map_multiset_sum _
    _ = _ := by simp [powerSum]

section CommRing

variable {R : Type*} [CommRing R]

/-- Newton's recurrence for the power sums of a multiset, obtained by
evaluating `MvPolynomial.psum_eq_mul_esymm_sub_sum`. Multiplicities are
preserved by using the occurrence type of `s`, rather than `s.toFinset`. -/
theorem powerSum_eq_mul_esymm_sub_sum
    (s : Multiset R) (k : ℕ) (hk : 0 < k) :
    s.powerSum k = (-1) ^ (k + 1) * k * s.esymm k -
      ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
        (-1) ^ a.1 * s.esymm a.1 * s.powerSum a.2 := by
  classical
  let f : s → R := fun x => x
  have h := MvPolynomial.psum_eq_mul_esymm_sub_sum s R k hk
  have h' := congrArg (MvPolynomial.aeval f) h
  have hpower (n : ℕ) : (∑ x : s, (x : R) ^ n) = s.powerSum n := by
    calc
      _ = (((Finset.univ : Finset s).val.map
          fun x : s => (x : R) ^ n).sum) := rfl
      _ = (s.map fun x : R => x ^ n).sum :=
        congrArg Multiset.sum (Multiset.map_univ s fun x : R => x ^ n)
      _ = _ := rfl
  have hesymm (n : ℕ) :
      MvPolynomial.aeval f (MvPolynomial.esymm s R n) = s.esymm n := by
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
    exact congrArg (fun t : Multiset R => t.esymm n) <| by
      simpa only [f, Multiset.map_id'] using
        (Multiset.map_univ s fun x : R => x)
  have hpsum (n : ℕ) :
      MvPolynomial.aeval f (MvPolynomial.psum s R n) = s.powerSum n := by
    rw [MvPolynomial.aeval_psum]
    exact hpower n
  simpa only [map_sub, map_mul, map_pow, map_natCast, map_neg, map_one,
    map_sum, hpsum, hesymm] using h'

end CommRing

end Multiset
