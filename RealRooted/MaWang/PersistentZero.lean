/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.PFPolynomial
public import RealRooted.SimpleRoots
import RealRooted.MaWang.RootSignSuccessor
import RealRooted.MaWang.Weak.DerivativeSign
import RealRooted.MaWang.Strong
import RealRooted.WagnerX.ListInterlacing
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.Interlacing.Residue
import RealRooted.Linear
import Mathlib.Tactic

/-!
# Persistent zero roots in first-order derivative-lag recurrences

Multiplication by `X^s` conjugates `U I + X W D` to `(U + s W) I + X W D`.
All identities are division-free. The common zero is transported with its exact
multiplicity, while genuine strict negative-root separation is recorded on the
quotients. The project predicate `StrictInterl` itself allows common roots;
the products satisfy zero-aware directed interlacing.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.PersistentZero

/-- Division-free conjugation of the first-order left action by `X^s`.
No polynomial is cancelled and the formula includes `s = 0`. -/
theorem weyl_mul_X_pow {R : Type*} [CommRing R] (s : ℕ) (U W q : R[X]) :
    U * (X ^ s * q) + X * W * (X ^ s * q).derivative =
      X ^ s * ((U + C (s : R) * W) * q + X * W * q.derivative) := by
  cases s with
  | zero => simp
  | succ s =>
      rw [derivative_mul, derivative_X_pow_succ, pow_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- The lag multiplier is unchanged by the common-power conjugation.
The predecessor may be zero. -/
theorem weylLag_mul_X_pow {R : Type*} [CommRing R]
    (s : ℕ) (U W L p q : R[X]) :
    U * (X ^ s * q) + X * W * (X ^ s * q).derivative + L * (X ^ s * p) =
      X ^ s * (((U + C (s : R) * W) * q + X * W * q.derivative) + L * p) := by
  rw [weyl_mul_X_pow]
  ring

/-- A PF polynomial remains PF after adjoining any number of zero roots.
The quotient may itself be zero. -/
theorem isPFPolynomial_mul_X_pow {q : ℝ[X]} (hq : IsPFPolynomial q) (s : ℕ) :
    IsPFPolynomial (X ^ s * q) :=
  (isPFPolynomial_X_pow s).mul hq

/-- Simultaneous multiplication by `X^s` preserves zero-aware directed order,
including either zero input. -/
theorem interl_mul_X_pow {q r : ℝ[X]} (hqr : Interl q r) (s : ℕ) :
    Interl (X ^ s * q) (X ^ s * r) := by
  induction s with
  | zero => simpa using hqr
  | succ s ih =>
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using ih.mul_X_sub_C_both 0

/-- The complete multiset of roots, with multiplicities, after adjoining zeros. -/
theorem roots_mul_X_pow {q : ℝ[X]} (hq : q ≠ 0) (s : ℕ) :
    (X ^ s * q).roots = s • ({0} : Multiset ℝ) + q.roots := by
  rw [roots_mul (mul_ne_zero (pow_ne_zero s X_ne_zero) hq), roots_X_pow]

/-- A nonvanishing quotient constant gives exact zero multiplicity, including
constant quotients and `s = 0`. -/
theorem rootMultiplicity_zero_mul_X_pow {q : ℝ[X]} (hq : q.eval 0 ≠ 0) (s : ℕ) :
    (X ^ s * q).rootMultiplicity 0 = s := by
  have hq_ne : q ≠ 0 := by intro hz; simp [hz] at hq
  have hpow : (X ^ s : ℝ[X]).rootMultiplicity 0 = s := by
    simpa using (rootMultiplicity_X_sub_C_pow (0 : ℝ) s)
  rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero s X_ne_zero) hq_ne), hpow,
    rootMultiplicity_eq_zero (show ¬q.IsRoot 0 from hq), add_zero]

/-- Every nonzero root retains its exact multiplicity after adjoining zeros. -/
theorem rootMultiplicity_mul_X_pow_of_ne_zero {q : ℝ[X]} (hq : q ≠ 0)
    (s : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (X ^ s * q).rootMultiplicity x = q.rootMultiplicity x := by
  have hnot : ¬ (X ^ s : ℝ[X]).IsRoot x := by
    simp only [IsRoot.def, eval_pow, eval_X]
    exact pow_ne_zero s hx
  rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero s X_ne_zero) hq),
    rootMultiplicity_eq_zero hnot, zero_add]

/-- At every nonzero point, the products and quotients have precisely the
same roots. Unlike multiplicity formulas, this also includes the zero quotient. -/
theorem isRoot_mul_X_pow_iff (q : ℝ[X]) (s : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (X ^ s * q).IsRoot x ↔ q.IsRoot x := by
  simp only [IsRoot.def, eval_mul, eval_pow, eval_X, mul_eq_zero]
  simp [pow_ne_zero s hx]

/-- The negative-root multiset is unchanged, so all its positions and
multiplicities are retained. No simplicity or splitness hypothesis is needed. -/
theorem negative_roots_mul_X_pow {q : ℝ[X]} (hq : q ≠ 0) (s : ℕ) :
    (X ^ s * q).roots.filter (fun x ↦ x < 0) = q.roots.filter (fun x ↦ x < 0) := by
  rw [roots_mul_X_pow hq, Multiset.filter_add]
  simp

/-- Positive powers really give a common zero; no claim of disjoint roots
is made for the products. -/
theorem common_zero_mul_X_pow (q r : ℝ[X]) {s : ℕ} (hs : s ≠ 0) :
    (X ^ s * q).IsRoot 0 ∧ (X ^ s * r).IsRoot 0 := by
  simp [IsRoot.def, hs]

/-- Transport of a PF ordered quotient pair with positive constants.
Together with `negative_roots_mul_X_pow` and `rootMultiplicity_mul_X_pow_of_ne_zero`,
this preserves the full negative-root geometry, without claiming simplicity at zero. -/
theorem transport {q r : ℝ[X]} (hq : IsPFPolynomial q) (hr : IsPFPolynomial r)
    (hq0 : 0 < q.eval 0) (hr0 : 0 < r.eval 0) (hqr : Interl q r) (s : ℕ) :
    IsPFPolynomial (X ^ s * q) ∧ IsPFPolynomial (X ^ s * r) ∧
      (X ^ s * q).rootMultiplicity 0 = s ∧ (X ^ s * r).rootMultiplicity 0 = s ∧
      Interl (X ^ s * q) (X ^ s * r) :=
  ⟨isPFPolynomial_mul_X_pow hq s, isPFPolynomial_mul_X_pow hr s,
    rootMultiplicity_zero_mul_X_pow hq0.ne' s,
    rootMultiplicity_zero_mul_X_pow hr0.ne' s, interl_mul_X_pow hqr s⟩

/-- Simple quotient roots stay simple away from the common zero. -/
theorem hasSimpleRootsExcept_mul_X_pow {q : ℝ[X]} (hq : HasSimpleRoots q) (s : ℕ) :
    HasSimpleRootsExcept (X ^ s * q) 0 := by
  intro x hx hroot
  rw [rootMultiplicity_mul_X_pow_of_ne_zero hq.ne_zero s hx]
  exact hq x ((isRoot_mul_X_pow_iff q s hx).mp hroot)

/-- Disjoint quotient roots remain disjoint away from zero. Combined with
directed quotient order, this records genuine strict negative-root separation. -/
theorem no_common_root_mul_X_pow {q r : ℝ[X]}
    (hno : ∀ x : ℝ, ¬ (q.IsRoot x ∧ r.IsRoot x)) (s : ℕ) :
    ∀ x : ℝ, x ≠ 0 → ¬ ((X ^ s * q).IsRoot x ∧ (X ^ s * r).IsRoot x) := by
  intro x hx hroot
  exact hno x ⟨(isRoot_mul_X_pow_iff q s hx).mp hroot.1,
    (isRoot_mul_X_pow_iff r s hx).mp hroot.2⟩

/-- Transport of a genuinely separated PF quotient pair, independently of any
recurrence. All negative-root positions and multiplicities are unchanged, the
products are ordered, and zero has exactly the prescribed multiplicity. -/
theorem transport_of_no_common_root {q r : ℝ[X]}
    (hq : IsPFPolynomial q) (hr : IsPFPolynomial r)
    (hq0 : 0 < q.eval 0) (hr0 : 0 < r.eval 0) (hqr : StrictInterl q r)
    (hno : ∀ x : ℝ, ¬ (q.IsRoot x ∧ r.IsRoot x)) (s : ℕ) :
    IsPFPolynomial (X ^ s * q) ∧ IsPFPolynomial (X ^ s * r) ∧
      (X ^ s * q).rootMultiplicity 0 = s ∧ (X ^ s * r).rootMultiplicity 0 = s ∧
      Interl (X ^ s * q) (X ^ s * r) ∧
      HasSimpleRootsExcept (X ^ s * q) 0 ∧ HasSimpleRootsExcept (X ^ s * r) 0 ∧
      (∀ x : ℝ, x ≠ 0 → ¬ ((X ^ s * q).IsRoot x ∧ (X ^ s * r).IsRoot x)) ∧
      (X ^ s * q).roots.filter (fun x ↦ x < 0) = q.roots.filter (fun x ↦ x < 0) ∧
      (X ^ s * r).roots.filter (fun x ↦ x < 0) = r.roots.filter (fun x ↦ x < 0) := by
  have hPR : Interl (X ^ s * q) (X ^ s * r) := by
    cases s with
    | zero => simpa using hqr.toInterl
    | succ s =>
        have hcross := strictInterl_mul_X_of_strictInterl_of_nonneg hqr
          hq.hasNonnegCoeffs hr.hasNonnegCoeffs
        have hshift := interl_mul_X_of_interl hcross.toInterl
          hr.hasNonnegCoeffs hq.X_mul.hasNonnegCoeffs
        simpa only [pow_succ, mul_assoc] using interl_mul_X_pow hshift s
  have hs := hqr.hasSimpleRoots_of_no_common_root hno
  exact ⟨isPFPolynomial_mul_X_pow hq s, isPFPolynomial_mul_X_pow hr s,
    rootMultiplicity_zero_mul_X_pow hq0.ne' s,
    rootMultiplicity_zero_mul_X_pow hr0.ne' s, hPR,
    hasSimpleRootsExcept_mul_X_pow hs.1 s, hasSimpleRootsExcept_mul_X_pow hs.2 s,
    no_common_root_mul_X_pow hno s, negative_roots_mul_X_pow hqr.1.1 s,
    negative_roots_mul_X_pow hqr.2.1.1 s⟩

/-- At a current root the current scalar term vanishes. This is the
division-free root-sign identity for the polynomial lag, including zero predecessor. -/
theorem eval_mul_derivative_eq {U V L p q r : ℝ[X]}
    (hrec : r = U * q + V * q.derivative + L * p) {x : ℝ} (hx : q.IsRoot x) :
    r.eval x * q.derivative.eval x =
      V.eval x * (q.derivative.eval x) ^ 2 +
        L.eval x * (p.eval x * q.derivative.eval x) := by
  rw [hrec, eval_add, add_mul, MaWang.eval_mul_derivative_eq_of_isRoot hx, eval_mul]
  ring

/-- Pointwise signed-lag strictness from a zero-aware PF input pair.
Either the derivative summand or the lag summand supplies strictness at each
root; weak order alone is never used as a strict comparison. -/
theorem eval_mul_derivative_neg {U V L p q r : ℝ[X]}
    (hrec : r = U * q + V * q.derivative + L * p)
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hsimple : HasSimpleRoots q)
    (hpq : Interl p q)
    (hV : ∀ x, q.IsRoot x → V.eval x ≤ 0)
    (hL : ∀ x, q.IsRoot x → L.eval x ≤ 0)
    (hstrict : ∀ x, q.IsRoot x → V.eval x < 0 ∨
      (L.eval x < 0 ∧ 0 < p.eval x * q.derivative.eval x)) :
    ∀ x, q.IsRoot x → r.eval x * q.derivative.eval x < 0 := by
  intro x hx
  have hqpos := hq.hasNonnegCoeffs.pos_leadingCoeff hsimple.ne_zero
  have hlag : 0 ≤ p.eval x * q.derivative.eval x := by
    rcases hpq with hpzero | hqzero | hpq
    · simp [hpzero]
    · exact (hsimple.ne_zero hqzero).elim
    · exact hpq.eval_mul_eval_derivative_nonneg
        (hp.hasNonnegCoeffs.pos_leadingCoeff hpq.1.1) hqpos hx
  have hder : 0 < (q.derivative.eval x) ^ 2 :=
    sq_pos_iff.mpr (hsimple.eval_derivative_ne_zero hx)
  rw [eval_mul_derivative_eq hrec hx]
  rcases hstrict x hx with hVstrict | ⟨hLstrict, hlagstrict⟩
  · exact add_neg_of_neg_of_nonpos (mul_neg_of_neg_of_pos hVstrict hder)
      (mul_nonpos_of_nonpos_of_nonneg (hL x hx) hlag)
  · exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonpos_of_nonneg (hV x hx) hder.le)
      (mul_neg_of_neg_of_pos hLstrict hlagstrict)

/-- The strictly negative derivative multiplier mode permits weak input order,
shared input roots, and a zero predecessor. -/
theorem eval_mul_derivative_neg_of_derivative {U V L p q r : ℝ[X]}
    (hrec : r = U * q + V * q.derivative + L * p)
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hsimple : HasSimpleRoots q)
    (hpq : Interl p q) (hV : ∀ x, q.IsRoot x → V.eval x < 0)
    (hL : ∀ x, q.IsRoot x → L.eval x ≤ 0) :
    ∀ x, q.IsRoot x → r.eval x * q.derivative.eval x < 0 :=
  eval_mul_derivative_neg hrec hp hq hsimple hpq (fun x hx ↦ (hV x hx).le)
    hL (fun x hx ↦ Or.inl (hV x hx))

/-- The strictly negative lag mode uses disjoint input roots explicitly.
Disjoint input roots make `p q'` strictly positive at every root of `q`. -/
theorem eval_mul_derivative_neg_of_lag {U V L p q r : ℝ[X]}
    (hrec : r = U * q + V * q.derivative + L * p)
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : StrictInterl p q)
    (hno : ∀ x : ℝ, ¬ (p.IsRoot x ∧ q.IsRoot x))
    (hV : ∀ x, q.IsRoot x → V.eval x ≤ 0)
    (hL : ∀ x, q.IsRoot x → L.eval x < 0) :
    ∀ x, q.IsRoot x → r.eval x * q.derivative.eval x < 0 := by
  have hs := hpq.hasSimpleRoots_of_no_common_root hno
  apply eval_mul_derivative_neg hrec hp hq hs.2 hpq.toInterl hV
    (fun x hx ↦ (hL x hx).le)
  intro x hx
  refine Or.inr ⟨hL x hx, ?_⟩
  exact residue_sign_pos hpq (hq.hasNonnegCoeffs.pos_leadingCoeff hpq.2.1.1)
    (hp.hasNonnegCoeffs.pos_leadingCoeff hpq.1.1) hs.2.roots_nodup hs.1.roots_nodup
    x ((mem_roots hpq.2.1.1).mpr hx)
    (fun hxmem ↦ hno x ⟨(mem_roots hpq.1.1).mp hxmem, hx⟩)

/-- Strict critical signs, a positive constant and a nonnegative prospective top
coefficient give an equal- or successor-degree quotient with simple negative roots.
The constant-current case is included; output coefficient positivity follows. -/
theorem rootSign_step {q r : ℝ[X]}
    (hq : IsPFPolynomial q) (hsimple : HasSimpleRoots q) (hq0 : 0 < q.eval 0)
    (hcap : r.natDegree ≤ q.natDegree + 1) (hr0 : 0 < r.eval 0)
    (hsign : ∀ x, q.IsRoot x → r.eval x * q.derivative.eval x < 0)
    (htop : 0 ≤ r.coeff (q.natDegree + 1)) :
    r.natDegree = (if r.coeff (q.natDegree + 1) = 0 then q.natDegree
      else q.natDegree + 1) ∧ HasPosLeadingCoeff r ∧ StrictInterl q r ∧
      IsPFPolynomial r ∧ HasSimpleRoots r ∧ (∀ x ∈ r.roots, x < 0) ∧
      (∀ x : ℝ, ¬ (q.IsRoot x ∧ r.IsRoot x)) ∧
      ∀ k ≤ r.natDegree, 0 < r.coeff k := by
  have hqpos := hq.hasNonnegCoeffs.pos_leadingCoeff hsimple.ne_zero
  have hqneg := roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hq.hasNonnegCoeffs
    (by simpa only [coeff_zero_eq_eval_zero] using hq0.ne')
  have hout : r.natDegree = (if r.coeff (q.natDegree + 1) = 0 then q.natDegree
      else q.natDegree + 1) ∧ HasPosLeadingCoeff r ∧ StrictInterl q r ∧
      r.Splits ∧ HasSimpleRoots r ∧ (∀ x ∈ r.roots, x < 0) ∧
      ∀ k ≤ r.natDegree, 0 < r.coeff k := by
    by_cases hz : r.coeff (q.natDegree + 1) = 0
    · simpa only [hz, ↓reduceIte] using rootSignSameDegree_of_coeff_eq_zero hq.splits
        hqpos rfl hsimple.roots_nodup hqneg hcap hr0 hsign hz
    · simpa only [hz, ↓reduceIte] using rootSignSuccessor_of_coeff_pos hq.splits
        hqpos rfl hsimple.roots_nodup hqneg hcap hr0 hsign (lt_of_le_of_ne htop (Ne.symm hz))
  obtain ⟨hdeg, hpos, hqr, hrsplits, hrsimple, hrneg, hrcoeff⟩ := hout
  refine ⟨hdeg, hpos, hqr, IsPFPolynomial.of_realRooted_nonneg
    (hasNonnegCoeffs_of_forall_coeff_pos hrcoeff) hrsplits,
    hrsimple, hrneg, ?_, hrcoeff⟩
  intro x hx
  have h := hsign x hx.1
  simp [hx.2.eq_zero] at h

/-- The root-sign successor transported back to the common-zero rows.
The quotient carries genuine strict separation; the products carry weak order,
simple roots away from zero, and exact zero multiplicity. -/
theorem rootSign_transport {q r : ℝ[X]} (s : ℕ)
    (hq : IsPFPolynomial q) (hsimple : HasSimpleRoots q) (hq0 : 0 < q.eval 0)
    (hcap : r.natDegree ≤ q.natDegree + 1) (hr0 : 0 < r.eval 0)
    (hsign : ∀ x, q.IsRoot x → r.eval x * q.derivative.eval x < 0)
    (htop : 0 ≤ r.coeff (q.natDegree + 1)) :
    IsPFPolynomial (X ^ s * q) ∧ IsPFPolynomial (X ^ s * r) ∧
      (X ^ s * q).rootMultiplicity 0 = s ∧ (X ^ s * r).rootMultiplicity 0 = s ∧
      Interl (X ^ s * q) (X ^ s * r) ∧ StrictInterl q r ∧
      HasSimpleRootsExcept (X ^ s * q) 0 ∧ HasSimpleRootsExcept (X ^ s * r) 0 ∧
      ∀ x : ℝ, x ≠ 0 → ¬ ((X ^ s * q).IsRoot x ∧ (X ^ s * r).IsRoot x) := by
  obtain ⟨_, _, hqr, hr, hrsimple, _, hno, _⟩ :=
    rootSign_step hq hsimple hq0 hcap hr0 hsign htop
  obtain ⟨hP, hR, hPmult, hRmult, hPR⟩ := transport hq hr hq0 hr0 hqr.toInterl s
  exact ⟨hP, hR, hPmult, hRmult, hPR, hqr,
    hasSimpleRootsExcept_mul_X_pow hsimple s, hasSimpleRootsExcept_mul_X_pow hrsimple s,
    no_common_root_mul_X_pow hno s⟩

/-- A common-power factorization propagates along the nonautonomous recurrence,
provided the quotients obey the explicitly conjugated recurrence. -/
theorem sequence_eq_mul_X_pow {P Q U W L : ℕ → ℝ[X]} (s : ℕ)
    (hP : ∀ n, P (n + 2) = U n * P (n + 1) +
      X * W n * (P (n + 1)).derivative + L n * P n)
    (hQ : ∀ n, Q (n + 2) = (U n + C (s : ℝ) * W n) * Q (n + 1) +
      X * W n * (Q (n + 1)).derivative + L n * Q n)
    (h0 : P 0 = X ^ s * Q 0) (h1 : P 1 = X ^ s * Q 1) :
    ∀ n, P n = X ^ s * Q n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih0 ih1 =>
      rw [hP n, ih0, ih1, weylLag_mul_X_pow, ← hQ n]

/-- The quotient orbit of the conjugated nonautonomous first-order recurrence. -/
def quotientSequence (s : ℕ) (U W L : ℕ → ℝ[X]) (q0 q1 : ℝ[X]) : ℕ → ℝ[X]
  | 0 => q0
  | 1 => q1
  | n + 2 => (U n + C (s : ℝ) * W n) * quotientSequence s U W L q0 q1 (n + 1) +
      X * W n * (quotientSequence s U W L q0 q1 (n + 1)).derivative +
      L n * quotientSequence s U W L q0 q1 n

/-- The conjugated quotient recurrence exists for every pair of factored seed
rows; it is constructed recursively, without division or cancellation. -/
theorem exists_quotient_sequence {P U W L : ℕ → ℝ[X]} (s : ℕ) (q0 q1 : ℝ[X])
    (hP : ∀ n, P (n + 2) = U n * P (n + 1) +
      X * W n * (P (n + 1)).derivative + L n * P n)
    (h0 : P 0 = X ^ s * q0) (h1 : P 1 = X ^ s * q1) :
    ∃ Q : ℕ → ℝ[X], Q 0 = q0 ∧ Q 1 = q1 ∧
      (∀ n, Q (n + 2) = (U n + C (s : ℝ) * W n) * Q (n + 1) +
        X * W n * (Q (n + 1)).derivative + L n * Q n) ∧
      ∀ n, P n = X ^ s * Q n := by
  let Q := quotientSequence s U W L q0 q1
  have hQ : ∀ n, Q (n + 2) = (U n + C (s : ℝ) * W n) * Q (n + 1) +
      X * W n * (Q (n + 1)).derivative + L n * Q n := fun _ ↦ rfl
  exact ⟨Q, rfl, rfl, hQ, sequence_eq_mul_X_pow s hP hQ h0 h1⟩

/-- Persistent-zero orbit theorem for the explicitly conjugated recurrence.
Each rank supplies its actual output cap, constant, prospective top coefficient,
and pointwise strict-sign mode. The predecessor seed may be zero; every nonzero
row has exact zero multiplicity `s`. Negative roots separate after each transition.
This is an orbit theorem with quotient hypotheses, not a universal matrix preserver. -/
theorem rootSign_sequence {P Q U W L : ℕ → ℝ[X]} (s : ℕ)
    (hP : ∀ n, P (n + 2) = U n * P (n + 1) +
      X * W n * (P (n + 1)).derivative + L n * P n)
    (hQ : ∀ n, Q (n + 2) = (U n + C (s : ℝ) * W n) * Q (n + 1) +
      X * W n * (Q (n + 1)).derivative + L n * Q n)
    (h0 : P 0 = X ^ s * Q 0) (h1 : P 1 = X ^ s * Q 1)
    (hpf0 : IsPFPolynomial (Q 0)) (hpf1 : IsPFPolynomial (Q 1))
    (h01 : Interl (Q 0) (Q 1)) (hsimple1 : HasSimpleRoots (Q 1))
    (hz0 : Q 0 = 0 ∨ 0 < (Q 0).eval 0) (hzero : ∀ n, 0 < (Q (n + 1)).eval 0)
    (hcap : ∀ n, (Q (n + 2)).natDegree ≤ (Q (n + 1)).natDegree + 1)
    (htop : ∀ n, 0 ≤ (Q (n + 2)).coeff ((Q (n + 1)).natDegree + 1))
    (hV : ∀ n x, (Q (n + 1)).IsRoot x → (X * W n).eval x ≤ 0)
    (hL : ∀ n x, (Q (n + 1)).IsRoot x → (L n).eval x ≤ 0)
    (hstrict : ∀ n x, (Q (n + 1)).IsRoot x → (X * W n).eval x < 0 ∨
      ((L n).eval x < 0 ∧ 0 < (Q n).eval x * (Q (n + 1)).derivative.eval x)) :
    (∀ n, P n = X ^ s * Q n ∧ IsPFPolynomial (P n) ∧ Interl (P n) (P (n + 1)) ∧
      (P n ≠ 0 → (P n).rootMultiplicity 0 = s)) ∧
    ∀ n, StrictInterl (Q (n + 1)) (Q (n + 2)) ∧
      HasSimpleRoots (Q (n + 2)) ∧ (∀ x ∈ (Q (n + 2)).roots, x < 0) ∧
      HasSimpleRootsExcept (P (n + 2)) 0 ∧
      (∀ x : ℝ, x ≠ 0 → ¬ ((P (n + 1)).IsRoot x ∧ (P (n + 2)).IsRoot x)) ∧
      (Q (n + 2)).natDegree =
        (if (Q (n + 2)).coeff ((Q (n + 1)).natDegree + 1) = 0
          then (Q (n + 1)).natDegree else (Q (n + 1)).natDegree + 1) := by
  have hfactor := sequence_eq_mul_X_pow s hP hQ h0 h1
  have hstate : ∀ n, IsPFPolynomial (Q n) ∧ IsPFPolynomial (Q (n + 1)) ∧
      Interl (Q n) (Q (n + 1)) ∧ HasSimpleRoots (Q (n + 1)) := by
    intro n
    induction n with
    | zero => exact ⟨hpf0, hpf1, h01, hsimple1⟩
    | succ n ih =>
        have hsign := eval_mul_derivative_neg (hQ n) ih.1 ih.2.1 ih.2.2.2 ih.2.2.1
          (hV n) (hL n) (hstrict n)
        obtain ⟨_, _, hqr, hr, hrsimple, _, _, _⟩ := rootSign_step ih.2.1 ih.2.2.2
          (hzero n) (hcap n) (hzero (n + 1)) hsign (htop n)
        exact ⟨ih.2.1, hr, hqr.toInterl, hrsimple⟩
  constructor
  · intro n
    refine ⟨hfactor n, ?_, ?_, ?_⟩
    · rw [hfactor n]
      exact isPFPolynomial_mul_X_pow (hstate n).1 s
    · rw [hfactor n, hfactor (n + 1)]
      exact interl_mul_X_pow (hstate n).2.2.1 s
    · intro hne
      rw [hfactor n]
      cases n with
      | zero =>
          rcases hz0 with hz0 | hz0
          · exact (hne (by rw [hfactor 0, hz0, mul_zero])).elim
          · exact rootMultiplicity_zero_mul_X_pow hz0.ne' s
      | succ n => exact rootMultiplicity_zero_mul_X_pow (hzero n).ne' s
  · intro n
    have h := hstate n
    have hsign := eval_mul_derivative_neg (hQ n) h.1 h.2.1 h.2.2.2 h.2.2.1
      (hV n) (hL n) (hstrict n)
    obtain ⟨hdeg, _, hqr, _, hrsimple, hrneg, hno, _⟩ := rootSign_step h.2.1 h.2.2.2
      (hzero n) (hcap n) (hzero (n + 1)) hsign (htop n)
    refine ⟨hqr, hrsimple, hrneg, ?_, ?_, hdeg⟩
    · rw [hfactor (n + 2)]
      exact hasSimpleRootsExcept_mul_X_pow hrsimple s
    · rw [hfactor (n + 1), hfactor (n + 2)]
      exact no_common_root_mul_X_pow hno s

/-! Boundary examples: no zeros added, a constant quotient, a zero predecessor,
and equal- and successor-degree quotient pairs. -/

example {q r : ℝ[X]} (h : Interl q r) : Interl (X ^ 0 * q) (X ^ 0 * r) :=
  interl_mul_X_pow h 0

example (s : ℕ) : (X ^ s * C (1 : ℝ)).rootMultiplicity 0 = s :=
  rootMultiplicity_zero_mul_X_pow (by simp) s

example (s : ℕ) (U W L q : ℝ[X]) :
    U * (X ^ s * q) + X * W * (X ^ s * q).derivative + L * (X ^ s * 0) =
      X ^ s * ((U + C (s : ℝ) * W) * q + X * W * q.derivative) := by
  simpa only [mul_zero, add_zero] using weylLag_mul_X_pow s U W L 0 q

example (s : ℕ) : Interl (X ^ s * (X + C (2 : ℝ))) (X ^ s * (X + C (1 : ℝ))) :=
  interl_mul_X_pow ((StrictInterl.X_add_C_iff.mpr (by norm_num)).toInterl) s

example (s : ℕ) : Interl (X ^ s * (1 : ℝ[X])) (X ^ s * (X + C (1 : ℝ))) :=
  interl_mul_X_pow (StrictInterl.of_natDegree_eq_zero_left one_ne_zero
    (by simp) (monic_X_add_C (1 : ℝ)).ne_zero (by simp)).toInterl s

end RealRooted.PersistentZero
