import RealRooted.Basic
import RealRooted.DegreeDropReversal

/-!
# Sequence closure theorems

Reusable induction and closure theorems for polynomial sequences carrying
`Prec`, real-rootedness, splitness, and product certificates.
-/

open Polynomial

namespace RealRooted

/-- Generic sequence induction from one base case and a successor step. -/
theorem sequence_of_base_and_step {Q : Nat → Prop}
    (hbase : Q 0)
    (hstep : ∀ n : Nat, Q n → Q (n + 1)) :
    ∀ n : Nat, Q n :=
  Nat.rec hbase hstep

/-- Generic sequence induction from a finite base interval and a successor
step that starts at the cutoff row. -/
theorem sequence_of_base_interval_and_step_from {Q : Nat → Prop}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → Q n)
    (hstep : ∀ n : Nat, N ≤ n → Q n → Q (n + 1)) :
    ∀ n : Nat, Q n := fun n =>
  Nat.strong_induction_on n fun n ih => by
    by_cases hn : n ≤ N
    · exact hbase n hn
    · cases n with
      | zero =>
          exact False.elim (hn (Nat.zero_le N))
      | succ m =>
          have hNm : N ≤ m := by lia
          exact hstep m hNm (ih m (Nat.lt_succ_self m))

/-- Generic period-two sequence induction from the two base parities and a
step advancing by two. -/
theorem sequence_of_base_pair_and_step_two {Q : Nat → Prop}
    (hzero : Q 0)
    (hone : Q 1)
    (hstep : ∀ n : Nat, Q n → Q (n + 2)) :
    ∀ n : Nat, Q n := fun n =>
  Nat.strong_induction_on n fun n ih => by
    cases n with
    | zero =>
        exact hzero
    | succ n =>
        cases n with
        | zero =>
            exact hone
        | succ n =>
            exact hstep n (ih n (Nat.lt_succ_of_lt (Nat.lt_succ_self n)))

/-- Generic period-two sequence induction from a finite base interval and a
step advancing by two that starts at the cutoff row. -/
theorem sequence_of_base_interval_and_step_two_from {Q : Nat → Prop}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N + 1 → Q n)
    (hstep : ∀ n : Nat, N ≤ n → Q n → Q (n + 2)) :
    ∀ n : Nat, Q n := fun n =>
  Nat.strong_induction_on n fun n ih => by
    by_cases hn : n ≤ N + 1
    · exact hbase n hn
    · cases n with
      | zero =>
          exact False.elim (hn (by lia))
      | succ m =>
          cases m with
          | zero =>
              exact False.elim (hn (by lia))
          | succ k =>
              have hNk : N ≤ k := by lia
              exact hstep k hNk (ih k (Nat.lt_succ_of_lt (Nat.lt_succ_self k)))

/-- Generic `Prec`-chain induction from one base case and a successor step.

This is the plateau-safe sequence shell: the step only needs the previous
`Prec` certificate, not a degree-increasing `Interlaces` certificate. -/
theorem prec_sequence_of_base_and_step {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hstep : ∀ n : Nat, Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  sequence_of_base_and_step hbase hstep

/-- Real-rootedness corollary of a generic `Prec`-chain induction. -/
theorem isRealRooted_of_prec_sequence {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hstep : ∀ n : Nat, Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  fun n => (prec_sequence_of_base_and_step hbase hstep n).1

/-- A consecutive `Prec` chain gives rowwise nonzero real-rootedness. -/
theorem isRealRooted_of_prec_chain {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hprec : ∀ n : Nat, Prec (P n) (P (n + 1))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_sequence hbase (fun n _ => hprec (n + 1))

/-- A consecutive `Prec` chain gives rowwise nonzero real-rootedness, using
the first step as the base certificate. -/
theorem isRealRooted_of_prec_chain_from_step {P : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, Prec (P n) (P (n + 1))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain (hprec 0) hprec

/-- A consecutive `Interlaces` chain gives rowwise nonzero real-rootedness. -/
theorem isRealRooted_of_interlaces_chain {P : Nat → ℝ[X]}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step fun n => (hinter n).toPrec

/-- A consecutive `Prec` chain gives consecutive interlacing once the degree
increments are supplied. -/
theorem interlaces_of_prec_chain {P : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, Prec (P n) (P (n + 1)))
    (hdegree : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) :=
  fun n => (hprec n).toInterlaces (hdegree n)

/-- Generic `Prec`-chain induction with a same-degree/successor-degree branch.

This wraps plateau recurrences such as degree patterns `1,1,2,2,3,3,...`.
The theorem does not prove either branch; it carries the induction hypothesis
and dispatches to the sequence-specific same-degree or successor-degree step. -/
theorem prec_sequence_of_base_and_degree_branches {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hbranch : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hsame : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2)))
    (hsucc : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1 →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine prec_sequence_of_base_and_step hbase ?_
  intro n hprev
  rcases hbranch n with hsame_degree | hsucc_degree
  · exact hsame n hsame_degree hprev
  · exact hsucc n hsucc_degree hprev

/-- Real-rootedness corollary of a branched generic `Prec`-chain induction. -/
theorem isRealRooted_of_prec_sequence_degree_branches {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hbranch : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hsame : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2)))
    (hsucc : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1 →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := fun n =>
  (prec_sequence_of_base_and_degree_branches hbase hbranch hsame hsucc n).1

/-- Project the nonvanishing half of a real-rootedness certificate. -/
theorem ne_zero_of_isRealRooted {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    p ≠ 0 :=
  hp.1

/-- Project the splitting half of a real-rootedness certificate. -/
theorem splits_of_isRealRooted {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    p.Splits :=
  hp.2

/-- Project zero-aware splitting from a real-rootedness certificate. -/
theorem eq_zero_or_splits_of_isRealRooted {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    p = 0 ∨ p.Splits :=
  Or.inr hp.2

/-- Product transport for nonzero real-rootedness certificates. -/
theorem isRealRooted_mul_of_isRealRooted {p q : ℝ[X]}
    (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits) :
    p * q ≠ 0 ∧ (p * q).Splits :=
  isRealRooted_mul hp.1 hp.2 hq.1 hq.2

/-- Power transport for nonzero real-rootedness certificates. -/
theorem isRealRooted_pow_of_isRealRooted {p : ℝ[X]}
    (hp : p ≠ 0 ∧ p.Splits) (n : Nat) :
    p ^ n ≠ 0 ∧ (p ^ n).Splits :=
  ⟨pow_ne_zero n hp.1, hp.2.pow n⟩

/-- Power transport from nonzero real-rootedness to splitting. -/
theorem splits_pow_of_isRealRooted {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) (n : Nat) :
    (p ^ n).Splits :=
  (isRealRooted_pow_of_isRealRooted hp n).2

/-- Product transport for zero-aware real-rootedness certificates. -/
theorem mul_eq_zero_or_splits {p q : ℝ[X]}
    (hp : p = 0 ∨ p.Splits) (hq : q = 0 ∨ q.Splits) :
    p * q = 0 ∨ (p * q).Splits := by
  rcases hp with rfl | hp
  · left
    simp
  rcases hq with rfl | hq
  · left
    simp
  · exact Or.inr (hp.mul hq)

/-- Power transport for zero-aware real-rootedness certificates. -/
theorem pow_eq_zero_or_splits {p : ℝ[X]} (hp : p = 0 ∨ p.Splits) (n : Nat) :
    p ^ n = 0 ∨ (p ^ n).Splits := by
  rcases hp with rfl | hp
  · cases n with
    | zero =>
        right
        simp
    | succ n =>
        left
        simp
  · exact Or.inr (hp.pow n)

/-- Power transport from nonzero real-rootedness to zero-aware real-rootedness. -/
theorem pow_eq_zero_or_splits_of_isRealRooted {p : ℝ[X]}
    (hp : p ≠ 0 ∧ p.Splits) (n : Nat) :
    p ^ n = 0 ∨ (p ^ n).Splits :=
  eq_zero_or_splits_of_isRealRooted (isRealRooted_pow_of_isRealRooted hp n)

/-- Project the left zero-aware certificate from a pair certificate. -/
theorem left_eq_zero_or_splits_of_eq_zero_or_splits_pair {p q : ℝ[X]}
    (hpq : (p = 0 ∨ p.Splits) ∧ (q = 0 ∨ q.Splits)) :
    p = 0 ∨ p.Splits :=
  hpq.1

/-- Project the right zero-aware certificate from a pair certificate. -/
theorem right_eq_zero_or_splits_of_eq_zero_or_splits_pair {p q : ℝ[X]}
    (hpq : (p = 0 ∨ p.Splits) ∧ (q = 0 ∨ q.Splits)) :
    q = 0 ∨ q.Splits :=
  hpq.2

/-- Reverse transport for zero-aware real-rootedness certificates. -/
theorem reverse_eq_zero_or_splits {p : ℝ[X]} (hp : p = 0 ∨ p.Splits) :
    p.reverse = 0 ∨ p.reverse.Splits := by
  rcases hp with hp | hp
  · left
    simp [hp]
  · exact Or.inr (DegreeDropReversal.splits_reverse hp)

/-- Consume a reverse zero-aware real-rootedness certificate. -/
theorem eq_zero_or_splits_of_reverse {p : ℝ[X]}
    (hp : p.reverse = 0 ∨ p.reverse.Splits) :
    p = 0 ∨ p.Splits := by
  rcases hp with hp | hp
  · exact Or.inl (Polynomial.reverse_eq_zero.mp hp)
  · exact Or.inr (DegreeDropReversal.splits_of_reverse hp)

/-- Reflect transport for zero-aware real-rootedness certificates. -/
theorem reflect_eq_zero_or_splits {p : ℝ[X]} (hp : p = 0 ∨ p.Splits) {N : ℕ}
    (hN : p.natDegree ≤ N) :
    reflect N p = 0 ∨ (reflect N p).Splits := by
  rcases hp with hp | hp
  · left
    simp [hp]
  · exact Or.inr (DegreeDropReversal.splits_reflect_of_splits hp hN)

/-- Degree-padded reverse transport for zero-aware real-rootedness certificates. -/
theorem X_pow_mul_reverse_eq_zero_or_splits {p : ℝ[X]} (hp : p = 0 ∨ p.Splits)
    (N : ℕ) :
    X ^ (N - p.natDegree) * p.reverse = 0 ∨
      (X ^ (N - p.natDegree) * p.reverse).Splits := by
  rcases hp with hp | hp
  · left
    simp [hp]
  · exact Or.inr (DegreeDropReversal.splits_X_pow_mul_reverse hp N)

/-- Divide out a zero root in a zero-aware real-rootedness certificate. -/
theorem divX_eq_zero_or_splits_of_coeff_zero {p : ℝ[X]} (h0 : p.coeff 0 = 0)
    (hp : p = 0 ∨ p.Splits) :
    p.divX = 0 ∨ p.divX.Splits := by
  rcases hp with hp | hp
  · left
    simp [hp]
  · exact Or.inr ((DegreeDropReversal.splits_iff_divX_splits_of_coeff_zero h0).1 hp)

/-- Lift a zero-aware real-rootedness certificate after dividing out a zero root. -/
theorem eq_zero_or_splits_of_divX {p : ℝ[X]} (h0 : p.coeff 0 = 0)
    (hp : p.divX = 0 ∨ p.divX.Splits) :
    p = 0 ∨ p.Splits := by
  rcases hp with hp | hp
  · left
    rw [DegreeDropReversal.eq_X_mul_divX_of_coeff_zero h0, hp, mul_zero]
  · exact Or.inr (DegreeDropReversal.splits_of_divX_splits_of_coeff_zero h0 hp)

/-- Reverse transport for nonzero real-rootedness certificates. -/
theorem reverse_isRealRooted {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    p.reverse ≠ 0 ∧ p.reverse.Splits :=
  ⟨fun h => hp.1 (Polynomial.reverse_eq_zero.mp h),
    DegreeDropReversal.splits_reverse hp.2⟩

/-- Consume a reverse nonzero real-rootedness certificate. -/
theorem isRealRooted_of_reverse {p : ℝ[X]} (hp : p.reverse ≠ 0 ∧ p.reverse.Splits) :
    p ≠ 0 ∧ p.Splits :=
  ⟨fun h => hp.1 (by simp [h]), DegreeDropReversal.splits_of_reverse hp.2⟩

/-- Reflect transport for nonzero real-rootedness certificates. -/
theorem reflect_isRealRooted {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) {N : ℕ}
    (hN : p.natDegree ≤ N) :
    (reflect N p) ≠ 0 ∧ (reflect N p).Splits :=
  ⟨fun h => hp.1 (Polynomial.reflect_eq_zero_iff.mp h),
    DegreeDropReversal.splits_reflect_of_splits hp.2 hN⟩

/-- Degree-padded reverse transport for nonzero real-rootedness certificates. -/
theorem X_pow_mul_reverse_isRealRooted {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits)
    (N : ℕ) :
    (X ^ (N - p.natDegree) * p.reverse) ≠ 0 ∧
      (X ^ (N - p.natDegree) * p.reverse).Splits :=
  ⟨mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (fun h => hp.1 (Polynomial.reverse_eq_zero.mp h)),
    DegreeDropReversal.splits_X_pow_mul_reverse hp.2 N⟩

/-- Divide out a zero root in a nonzero real-rootedness certificate. -/
theorem divX_isRealRooted_of_coeff_zero {p : ℝ[X]} (h0 : p.coeff 0 = 0)
    (hp : p ≠ 0 ∧ p.Splits) :
    p.divX ≠ 0 ∧ p.divX.Splits :=
  ⟨fun h => hp.1 (by rw [DegreeDropReversal.eq_X_mul_divX_of_coeff_zero h0, h, mul_zero]),
    (DegreeDropReversal.splits_iff_divX_splits_of_coeff_zero h0).1 hp.2⟩

/-- Lift a nonzero real-rootedness certificate after dividing out a zero root. -/
theorem isRealRooted_of_divX {p : ℝ[X]} (h0 : p.coeff 0 = 0)
    (hp : p.divX ≠ 0 ∧ p.divX.Splits) :
    p ≠ 0 ∧ p.Splits :=
  ⟨by
      rw [DegreeDropReversal.eq_X_mul_divX_of_coeff_zero h0]
      exact mul_ne_zero Polynomial.X_ne_zero hp.1,
    DegreeDropReversal.splits_of_divX_splits_of_coeff_zero h0 hp.2⟩

/-- A polynomial with natural degree one is nonzero. -/
theorem ne_zero_of_natDegree_eq_one {p : ℝ[X]} (hdeg : p.natDegree = 1) :
    p ≠ 0 := by
  intro hp
  simp [hp] at hdeg

/-- Project real-rootedness of the left argument from a pair certificate. -/
theorem left_isRealRooted_of_isRealRooted_pair {p q : ℝ[X]}
    (hpq : (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits)) :
    p ≠ 0 ∧ p.Splits :=
  hpq.1

/-- Project real-rootedness of the right argument from a pair certificate. -/
theorem right_isRealRooted_of_isRealRooted_pair {p q : ℝ[X]}
    (hpq : (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits)) :
    q ≠ 0 ∧ q.Splits :=
  hpq.2

/-- Product splitting transport from a bundled nonzero real-rooted pair. -/
theorem mul_splits_of_isRealRooted_pair {p q : ℝ[X]}
    (hpq : (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits)) :
    (p * q).Splits :=
  (isRealRooted_mul_of_isRealRooted hpq.1 hpq.2).2

/-- Swapped product splitting transport from a bundled nonzero real-rooted pair. -/
theorem swap_mul_splits_of_isRealRooted_pair {p q : ℝ[X]}
    (hpq : (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits)) :
    (q * p).Splits :=
  (isRealRooted_mul_of_isRealRooted hpq.2 hpq.1).2

/-- Product zero-aware transport from a bundled nonzero real-rooted pair. -/
theorem mul_eq_zero_or_splits_of_isRealRooted_pair {p q : ℝ[X]}
    (hpq : (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits)) :
    p * q = 0 ∨ (p * q).Splits :=
  eq_zero_or_splits_of_isRealRooted (isRealRooted_mul_of_isRealRooted hpq.1 hpq.2)

/-- Swapped product zero-aware transport from a bundled nonzero real-rooted pair. -/
theorem swap_mul_eq_zero_or_splits_of_isRealRooted_pair {p q : ℝ[X]}
    (hpq : (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits)) :
    q * p = 0 ∨ (q * p).Splits :=
  eq_zero_or_splits_of_isRealRooted (isRealRooted_mul_of_isRealRooted hpq.2 hpq.1)

/-- Project left-argument nonvanishing from a pair certificate. -/
theorem left_ne_zero_of_isRealRooted_pair {p q : ℝ[X]}
    (hpq : (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits)) :
    p ≠ 0 :=
  (left_isRealRooted_of_isRealRooted_pair hpq).1

/-- Project left-argument splitting from a pair certificate. -/
theorem left_splits_of_isRealRooted_pair {p q : ℝ[X]}
    (hpq : (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits)) :
    p.Splits :=
  (left_isRealRooted_of_isRealRooted_pair hpq).2

/-- Project left-argument zero-aware splitting from a pair certificate. -/
theorem left_eq_zero_or_splits_of_isRealRooted_pair {p q : ℝ[X]}
    (hpq : (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits)) :
    p = 0 ∨ p.Splits :=
  eq_zero_or_splits_of_isRealRooted (left_isRealRooted_of_isRealRooted_pair hpq)

/-- Project right-argument nonvanishing from a pair certificate. -/
theorem right_ne_zero_of_isRealRooted_pair {p q : ℝ[X]}
    (hpq : (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits)) :
    q ≠ 0 :=
  (right_isRealRooted_of_isRealRooted_pair hpq).1

/-- Project right-argument splitting from a pair certificate. -/
theorem right_splits_of_isRealRooted_pair {p q : ℝ[X]}
    (hpq : (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits)) :
    q.Splits :=
  (right_isRealRooted_of_isRealRooted_pair hpq).2

/-- Project right-argument zero-aware splitting from a pair certificate. -/
theorem right_eq_zero_or_splits_of_isRealRooted_pair {p q : ℝ[X]}
    (hpq : (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits)) :
    q = 0 ∨ q.Splits :=
  eq_zero_or_splits_of_isRealRooted (right_isRealRooted_of_isRealRooted_pair hpq)

/-- Project real-rootedness of the left argument from a `Prec` certificate. -/
theorem left_isRealRooted_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    f ≠ 0 ∧ f.Splits :=
  hfg.1

/-- Project real-rootedness of the right argument from a `Prec` certificate. -/
theorem right_isRealRooted_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    g ≠ 0 ∧ g.Splits :=
  hfg.2.1

/-- Project left-argument nonvanishing from a `Prec` certificate. -/
theorem left_ne_zero_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    f ≠ 0 :=
  (left_isRealRooted_of_prec hfg).1

/-- Project left-argument splitting from a `Prec` certificate. -/
theorem left_splits_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    f.Splits :=
  (left_isRealRooted_of_prec hfg).2

/-- Project left-argument zero-aware splitting from a `Prec` certificate. -/
theorem left_eq_zero_or_splits_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    f = 0 ∨ f.Splits :=
  eq_zero_or_splits_of_isRealRooted (left_isRealRooted_of_prec hfg)

/-- Project right-argument nonvanishing from a `Prec` certificate. -/
theorem right_ne_zero_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    g ≠ 0 :=
  (right_isRealRooted_of_prec hfg).1

/-- Project right-argument splitting from a `Prec` certificate. -/
theorem right_splits_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    g.Splits :=
  (right_isRealRooted_of_prec hfg).2

/-- Project right-argument zero-aware splitting from a `Prec` certificate. -/
theorem right_eq_zero_or_splits_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    g = 0 ∨ g.Splits :=
  eq_zero_or_splits_of_isRealRooted (right_isRealRooted_of_prec hfg)

/-- Project real-rootedness of the right argument from an `Interlaces` certificate. -/
theorem right_isRealRooted_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    f ≠ 0 ∧ f.Splits :=
  hgf.1

/-- Project real-rootedness of the left argument from an `Interlaces` certificate. -/
theorem left_isRealRooted_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    g ≠ 0 ∧ g.Splits :=
  hgf.2.1

/-- Project right-argument nonvanishing from an `Interlaces` certificate. -/
theorem right_ne_zero_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    f ≠ 0 :=
  (right_isRealRooted_of_interlaces hgf).1

/-- Project right-argument splitting from an `Interlaces` certificate. -/
theorem right_splits_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    f.Splits :=
  (right_isRealRooted_of_interlaces hgf).2

/-- Project right-argument zero-aware splitting from an `Interlaces` certificate. -/
theorem right_eq_zero_or_splits_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    f = 0 ∨ f.Splits :=
  eq_zero_or_splits_of_isRealRooted (right_isRealRooted_of_interlaces hgf)

/-- Project left-argument nonvanishing from an `Interlaces` certificate. -/
theorem left_ne_zero_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    g ≠ 0 :=
  (left_isRealRooted_of_interlaces hgf).1

/-- Project left-argument splitting from an `Interlaces` certificate. -/
theorem left_splits_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    g.Splits :=
  (left_isRealRooted_of_interlaces hgf).2

/-- Project left-argument zero-aware splitting from an `Interlaces` certificate. -/
theorem left_eq_zero_or_splits_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    g = 0 ∨ g.Splits :=
  eq_zero_or_splits_of_isRealRooted (left_isRealRooted_of_interlaces hgf)

/-- Project the successor-degree equality from an `Interlaces` certificate. -/
theorem natDegree_succ_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    g.natDegree + 1 = f.natDegree :=
  hgf.2.2.1

/-- Project row-wise nonvanishing from a sequence real-rootedness certificate. -/
theorem ne_zero_of_isRealRooted_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, P n ≠ 0 :=
  fun n => (hP n).1

/-- Project row-wise splitting from a sequence real-rootedness certificate. -/
theorem splits_of_isRealRooted_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, (P n).Splits :=
  fun n => (hP n).2

/-- Project row-wise zero-aware splitting from a sequence real-rootedness certificate. -/
theorem eq_zero_or_splits_of_isRealRooted_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits :=
  fun n => Or.inr (hP n).2

/-- Project a single row from a sequence real-rootedness certificate. -/
theorem at_of_isRealRooted_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) (n : Nat) :
    P n ≠ 0 ∧ (P n).Splits :=
  hP n

/-- Project a single row from a pair-sequence real-rootedness certificate. -/
theorem at_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) (n : Nat) :
    (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) :=
  hP n

/-- Project row-wise pair real-rootedness from a `Prec` sequence. -/
theorem isRealRooted_pair_sequence_of_prec_sequence {A B : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, Prec (A n) (B n)) :
    ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits) :=
  fun n =>
    ⟨left_isRealRooted_of_prec (hprec n), right_isRealRooted_of_prec (hprec n)⟩

/-- Project left row-wise real-rootedness from a `Prec` sequence. -/
theorem left_isRealRooted_of_prec_sequence {A B : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, Prec (A n) (B n)) :
    ∀ n : Nat, A n ≠ 0 ∧ (A n).Splits :=
  fun n => left_isRealRooted_of_prec (hprec n)

/-- Project right row-wise real-rootedness from a `Prec` sequence. -/
theorem right_isRealRooted_of_prec_sequence {A B : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, Prec (A n) (B n)) :
    ∀ n : Nat, B n ≠ 0 ∧ (B n).Splits :=
  fun n => right_isRealRooted_of_prec (hprec n)

/-- Project left row-wise real-rootedness from a pair-sequence certificate. -/
theorem left_isRealRooted_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, A n ≠ 0 ∧ (A n).Splits :=
  fun n => (hP n).1

/-- Project right row-wise real-rootedness from a pair-sequence certificate. -/
theorem right_isRealRooted_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, B n ≠ 0 ∧ (B n).Splits :=
  fun n => (hP n).2

/-- Project left row-wise nonvanishing from a pair-sequence certificate. -/
theorem left_ne_zero_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, A n ≠ 0 :=
  fun n => (hP n).1.1

/-- Project left row-wise splitting from a pair-sequence certificate. -/
theorem left_splits_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, (A n).Splits :=
  fun n => (hP n).1.2

/-- Project left row-wise zero-aware splitting from a pair-sequence certificate. -/
theorem left_eq_zero_or_splits_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, A n = 0 ∨ (A n).Splits :=
  fun n => Or.inr (hP n).1.2

/-- Project right row-wise nonvanishing from a pair-sequence certificate. -/
theorem right_ne_zero_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, B n ≠ 0 :=
  fun n => (hP n).2.1

/-- Project right row-wise splitting from a pair-sequence certificate. -/
theorem right_splits_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, (B n).Splits :=
  fun n => (hP n).2.2

/-- Project right row-wise zero-aware splitting from a pair-sequence certificate. -/
theorem right_eq_zero_or_splits_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, B n = 0 ∨ (B n).Splits :=
  fun n => Or.inr (hP n).2.2

/-- Project left row-wise zero-aware splitting from a zero-aware pair-sequence. -/
theorem left_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence
    {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n = 0 ∨ (A n).Splits) ∧
      (B n = 0 ∨ (B n).Splits)) :
    ∀ n : Nat, A n = 0 ∨ (A n).Splits :=
  fun n => (hP n).1

/-- Project right row-wise zero-aware splitting from a zero-aware pair-sequence. -/
theorem right_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence
    {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n = 0 ∨ (A n).Splits) ∧
      (B n = 0 ∨ (B n).Splits)) :
    ∀ n : Nat, B n = 0 ∨ (B n).Splits :=
  fun n => (hP n).2

/-- Project a single row from a zero-aware pair-sequence certificate. -/
theorem at_of_eq_zero_or_splits_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n = 0 ∨ (A n).Splits) ∧
      (B n = 0 ∨ (B n).Splits)) (n : Nat) :
    (A n = 0 ∨ (A n).Splits) ∧ (B n = 0 ∨ (B n).Splits) :=
  hP n

/-- Row-wise product transport for nonzero real-rooted pair-sequences. -/
theorem isRealRooted_mul_sequence_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, A n * B n ≠ 0 ∧ (A n * B n).Splits :=
  fun n => isRealRooted_mul_of_isRealRooted (hP n).1 (hP n).2

/-- Row-wise swapped product transport for nonzero real-rooted pair-sequences. -/
theorem isRealRooted_swap_mul_sequence_of_isRealRooted_pair_sequence
    {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, B n * A n ≠ 0 ∧ (B n * A n).Splits :=
  fun n => isRealRooted_mul_of_isRealRooted (hP n).2 (hP n).1

/-- Row-wise product splitting transport for nonzero real-rooted pair-sequences. -/
theorem splits_mul_sequence_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, (A n * B n).Splits :=
  splits_of_isRealRooted_sequence <|
    isRealRooted_mul_sequence_of_isRealRooted_pair_sequence hP

/-- Row-wise swapped product splitting transport for nonzero real-rooted pair-sequences. -/
theorem splits_swap_mul_sequence_of_isRealRooted_pair_sequence
    {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, (B n * A n).Splits :=
  splits_of_isRealRooted_sequence <|
    isRealRooted_swap_mul_sequence_of_isRealRooted_pair_sequence hP

/-- Row-wise product zero-aware transport for nonzero real-rooted pair-sequences. -/
theorem mul_eq_zero_or_splits_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, A n * B n = 0 ∨ (A n * B n).Splits :=
  eq_zero_or_splits_of_isRealRooted_sequence <|
    isRealRooted_mul_sequence_of_isRealRooted_pair_sequence hP

/-- Row-wise swapped product zero-aware transport for nonzero real-rooted pair-sequences. -/
theorem swap_mul_eq_zero_or_splits_of_isRealRooted_pair_sequence
    {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, B n * A n = 0 ∨ (B n * A n).Splits :=
  eq_zero_or_splits_of_isRealRooted_sequence <|
    isRealRooted_swap_mul_sequence_of_isRealRooted_pair_sequence hP

/-- Row-wise product transport for zero-aware pair-sequences. -/
theorem mul_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence
    {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n = 0 ∨ (A n).Splits) ∧
      (B n = 0 ∨ (B n).Splits)) :
    ∀ n : Nat, A n * B n = 0 ∨ (A n * B n).Splits :=
  fun n => mul_eq_zero_or_splits (hP n).1 (hP n).2

/-- Row-wise swapped product transport for zero-aware pair-sequences. -/
theorem swap_mul_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence
    {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n = 0 ∨ (A n).Splits) ∧
      (B n = 0 ∨ (B n).Splits)) :
    ∀ n : Nat, B n * A n = 0 ∨ (B n * A n).Splits :=
  fun n => mul_eq_zero_or_splits (hP n).2 (hP n).1

end RealRooted
