import RealRooted.Basic
import RealRooted.DegreeDropReversal
import RealRooted.Tactic.Lookup
import RealRooted.Tactic.Sign
import RealRooted.Tactic.SideGoals

/-!
# Finish tactics

Small dispatchers for the proof tails that follow once an engine has produced a
`Prec` certificate.
-/

open Polynomial

namespace RealRooted

/-- Generic sequence induction from one base case and a successor step. -/
theorem sequence_of_base_and_step {Q : Nat → Prop}
    (hbase : Q 0)
    (hstep : ∀ n : Nat, Q n → Q (n + 1)) :
    ∀ n : Nat, Q n := by
  intro n
  induction n with
  | zero =>
      exact hbase
  | succ n ih =>
      exact hstep n ih

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
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  apply isRealRooted_of_prec_sequence hbase
  intro n hprev
  rcases hbranch n with hsame_degree | hsucc_degree
  · exact hsame n hsame_degree hprev
  · exact hsucc n hsucc_degree hprev

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

namespace Tactic

syntax (name := rr_lookup_term) "rr_lookup_term" : term
syntax (name := rr_realrooted_term) "rr_realrooted_term" : term
syntax (name := rr_lookup_interlaces_term) "rr_lookup_interlaces_term" : term
syntax (name := rr_degree_eq_one) "rr_degree_eq_one" : tactic
syntax (name := rr_degree_le_one) "rr_degree_le_one" : tactic
syntax (name := rr_natDegree_from_top_above)
  "rr_natDegree_from_top_above" " using "
    "top_ne" ":=" term ","
    "above" ":=" term :
  tactic

syntax (name := rr_natDegree_from_top_eq_above)
  "rr_natDegree_from_top_above" " using "
    "top_eq" ":=" term ","
    "above" ":=" term :
  tactic

syntax (name := rr_natDegree_from_top_pos_above)
  "rr_natDegree_from_top_above" " using "
    "top_pos" ":=" term ","
    "above" ":=" term :
  tactic

syntax (name := rr_exact_realrooted_or_projection)
  "rr_exact_realrooted_or_projection" term :
  tactic

syntax (name := rr_exact_realrooted_sequence_or_projection)
  "rr_exact_realrooted_sequence_or_projection" term :
  tactic

syntax (name := rr_exact_realrooted_refine_then)
  "rr_exact_realrooted_refine_then " term " with " tactic :
  tactic

syntax (name := rr_exact_realrooted_pair_sequence_or_projection)
  "rr_exact_realrooted_pair_sequence_or_projection" term :
  tactic

syntax (name := rr_first_exact)
  "rr_first_exact" term,* :
  tactic

syntax (name := rr_first_exact_or_simpa)
  "rr_first_exact_or_simpa" term ", " term :
  tactic

syntax (name := rr_first_exact_or_simpa_mul_assoc)
  "rr_first_exact_or_simpa_mul_assoc" term ", " term :
  tactic

syntax (name := rr_first_exact_or_simpa_mul_add_assoc)
  "rr_first_exact_or_simpa_mul_add_assoc" term ", " term :
  tactic

syntax (name := rr_first_realrooted_or_projection)
  "rr_first_realrooted_or_projection" term,* :
  tactic

syntax (name := rr_first_realrooted_sequence_or_projection)
  "rr_first_realrooted_sequence_or_projection" term,* :
  tactic

syntax (name := rr_first_exact_then_realrooted_sequence_or_projection)
  "rr_first_exact_then_realrooted_sequence_or_projection" term,* :
  tactic

syntax (name := rr_nonzero) "rr_nonzero" " using " term : tactic
syntax (name := rr_splits) "rr_splits" " using " term : tactic
syntax (name := rr_splits_mul)
  "rr_splits_mul" " using "
    "left" ":=" term ","
    "right" ":=" term :
  tactic
syntax (name := rr_splits_pow)
  "rr_splits_pow" " using "
    "splits" ":=" term ","
    "exponent" ":=" term :
  tactic
syntax (name := rr_splits_reverse)
  "rr_splits_reverse" " using "
    "splits" ":=" term :
  tactic
syntax (name := rr_splits_of_reverse)
  "rr_splits_of_reverse" " using "
    "reverse_splits" ":=" term :
  tactic
syntax (name := rr_splits_reflect)
  "rr_splits_reflect" " using "
    "splits" ":=" term ","
    "degree_bound" ":=" term :
  tactic
syntax (name := rr_splits_X_pow_mul_reverse)
  "rr_splits_X_pow_mul_reverse" " using "
    "splits" ":=" term :
  tactic
syntax (name := rr_splits_divX)
  "rr_splits_divX" " using "
    "coeff_zero" ":=" term ","
    "splits" ":=" term :
  tactic
syntax (name := rr_splits_of_divX)
  "rr_splits_of_divX" " using "
    "coeff_zero" ":=" term ","
    "divX_splits" ":=" term :
  tactic
syntax (name := rr_zero_or_splits)
  "rr_zero_or_splits" " using " term :
  tactic
syntax (name := rr_zero_or_splits_mul)
  "rr_zero_or_splits_mul" " using "
    "left" ":=" term ","
    "right" ":=" term :
  tactic
syntax (name := rr_zero_or_splits_pow)
  "rr_zero_or_splits_pow" " using "
    "zero_or_splits" ":=" term ","
    "exponent" ":=" term :
  tactic
syntax (name := rr_zero_or_splits_reverse)
  "rr_zero_or_splits_reverse" " using "
    "zero_or_splits" ":=" term :
  tactic
syntax (name := rr_zero_or_splits_of_reverse)
  "rr_zero_or_splits_of_reverse" " using "
    "reverse_zero_or_splits" ":=" term :
  tactic
syntax (name := rr_zero_or_splits_reflect)
  "rr_zero_or_splits_reflect" " using "
    "zero_or_splits" ":=" term ","
    "degree_bound" ":=" term :
  tactic
syntax (name := rr_zero_or_splits_X_pow_mul_reverse)
  "rr_zero_or_splits_X_pow_mul_reverse" " using "
    "zero_or_splits" ":=" term :
  tactic
syntax (name := rr_zero_or_splits_divX)
  "rr_zero_or_splits_divX" " using "
    "coeff_zero" ":=" term ","
    "zero_or_splits" ":=" term :
  tactic
syntax (name := rr_zero_or_splits_of_divX)
  "rr_zero_or_splits_of_divX" " using "
    "coeff_zero" ":=" term ","
    "divX_zero_or_splits" ":=" term :
  tactic
syntax (name := rr_realrooted) "rr_realrooted" " using " term : tactic
syntax (name := rr_mul_realrooted)
  "rr_mul_realrooted" " using " term ", " term :
  tactic
syntax (name := rr_mul_realrooted_named)
  "rr_mul_realrooted" " using "
    "left" ":=" term ","
    "right" ":=" term :
  tactic
syntax (name := rr_pow_realrooted)
  "rr_pow_realrooted" " using "
    "realrooted" ":=" term ","
    "exponent" ":=" term :
  tactic
syntax (name := rr_realrooted_reverse)
  "rr_realrooted_reverse" " using "
    "realrooted" ":=" term :
  tactic
syntax (name := rr_realrooted_of_reverse)
  "rr_realrooted_of_reverse" " using "
    "reverse_realrooted" ":=" term :
  tactic
syntax (name := rr_realrooted_reflect)
  "rr_realrooted_reflect" " using "
    "realrooted" ":=" term ","
    "degree_bound" ":=" term :
  tactic
syntax (name := rr_realrooted_X_pow_mul_reverse)
  "rr_realrooted_X_pow_mul_reverse" " using "
    "realrooted" ":=" term :
  tactic
syntax (name := rr_realrooted_divX)
  "rr_realrooted_divX" " using "
    "coeff_zero" ":=" term ","
    "realrooted" ":=" term :
  tactic
syntax (name := rr_realrooted_of_divX)
  "rr_realrooted_of_divX" " using "
    "coeff_zero" ":=" term ","
    "divX_realrooted" ":=" term :
  tactic
syntax (name := rr_nonzero_auto) "rr_nonzero" : tactic
syntax (name := rr_splits_auto) "rr_splits" : tactic
syntax (name := rr_zero_or_splits_auto) "rr_zero_or_splits" : tactic
syntax (name := rr_realrooted_auto) "rr_realrooted" : tactic

syntax (name := rr_interlaces_with_degree)
  "rr_interlaces" " using " term ", " term : tactic

syntax (name := rr_interlaces_auto_degree)
  "rr_interlaces" " using " term : tactic

syntax (name := rr_prec0) "rr_prec0" " using " term : tactic

syntax (name := rr_prec_of_interlaces)
  "rr_prec" " using " term :
  tactic

syntax (name := rr_prec_of_prec0)
  "rr_prec" " using " term ", " term ", " term : tactic

syntax (name := rr_gsturm_cons)
  "rr_gsturm_cons" " using " term ", " term : tactic

syntax (name := rr_sturm_cons)
  "rr_sturm_cons" " using " term ", " term : tactic

syntax (name := rr_sturm_base) "rr_sturm_base" : tactic

syntax (name := rr_prec_sequence)
  "rr_prec_sequence" " using "
    "base" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_prec_sequence_realrooted)
  "rr_prec_sequence_realrooted" " using "
    "base" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_finish_sequence_base_step)
  "rr_finish_sequence" " using "
    "base" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_finish_sequence_prec)
  "rr_finish_sequence" " using "
    "prec" ":=" term :
  tactic

syntax (name := rr_finish_sequence_prec_degree)
  "rr_finish_sequence" " using "
    "prec" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches)
  "rr_prec_sequence_branches" " using "
    "base" ":=" term ","
    "degree" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches_degree_branch)
  "rr_prec_sequence_branches" " using "
    "base" ":=" term ","
    "degree_branch" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches_realrooted)
  "rr_prec_sequence_branches_realrooted" " using "
    "base" ":=" term ","
    "degree" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches_realrooted_degree_branch)
  "rr_prec_sequence_branches_realrooted" " using "
    "base" ":=" term ","
    "degree_branch" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_finish_sequence_branches)
  "rr_finish_sequence_branches" " using "
    "base" ":=" term ","
    "degree" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_finish_sequence_branches_degree_branch)
  "rr_finish_sequence_branches" " using "
    "base" ":=" term ","
    "degree_branch" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_finish_using) "rr_finish" " using " term : tactic

syntax (name := rr_finish_using_interlaces_degree)
  "rr_finish" " using " term ", " term : tactic

syntax (name := rr_finish_using_prec0)
  "rr_finish" " using " term ", " term ", " term : tactic

syntax (name := rr_finish_using_sequence_branches)
  "rr_finish" " using " term ", " term ", " term ", " term : tactic

syntax (name := rr_finish) "rr_finish" : tactic

macro_rules
  | `(rr_lookup_term) =>
      `(by rr_lookup)
  | `(rr_realrooted_term) =>
      `(by rr_realrooted)
  | `(rr_lookup_interlaces_term) =>
      `(by
        first
          | exact RealRooted.Prec.toInterlaces rr_lookup_term rr_lookup_term
          | exact RealRooted.Prec.toInterlaces rr_lookup_term (by
              symm
              rr_lookup))
  | `(tactic| rr_degree_eq_one) =>
      `(tactic|
        first
          | rr_lookup [rr_degree]
          | (symm; rr_lookup [rr_degree]))
  | `(tactic| rr_degree_le_one) =>
      `(tactic|
        first
          | assumption
          | rr_lookup [rr_degree]
          | exact le_of_eq (by rr_lookup [rr_degree])
          | exact le_of_eq (by
              symm
              rr_lookup [rr_degree]))
  | `(tactic|
      rr_natDegree_from_top_above using
        top_ne := $htop:term,
        above := $habove:term) =>
      `(tactic|
        exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
          (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
            (fun m hm => by exact $habove m hm))
          $htop)
  | `(tactic|
      rr_natDegree_from_top_above using
        top_pos := $htop:term,
        above := $habove:term) =>
      `(tactic|
        exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
          (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
            (fun m hm => by exact $habove m hm))
          (ne_of_gt $htop))
  | `(tactic|
      rr_natDegree_from_top_above using
        top_eq := $htop:term,
        above := $habove:term) =>
      `(tactic|
        exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
          (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
            (fun m hm => by exact $habove m hm))
          (by
            have htop' := $htop
            simp [htop']))
  | `(tactic| rr_exact_realrooted_or_projection $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          RealRooted.ne_zero_of_isRealRooted $h,
          RealRooted.splits_of_isRealRooted $h,
          RealRooted.eq_zero_or_splits_of_isRealRooted $h,
          RealRooted.left_isRealRooted_of_isRealRooted_pair $h,
          RealRooted.right_isRealRooted_of_isRealRooted_pair $h,
          RealRooted.left_ne_zero_of_isRealRooted_pair $h,
          RealRooted.right_ne_zero_of_isRealRooted_pair $h,
          RealRooted.left_splits_of_isRealRooted_pair $h,
          RealRooted.right_splits_of_isRealRooted_pair $h,
          RealRooted.left_eq_zero_or_splits_of_isRealRooted_pair $h,
          RealRooted.right_eq_zero_or_splits_of_isRealRooted_pair $h,
          (RealRooted.isRealRooted_mul_of_isRealRooted
            (RealRooted.left_isRealRooted_of_isRealRooted_pair $h)
            (RealRooted.right_isRealRooted_of_isRealRooted_pair $h)),
          (RealRooted.isRealRooted_mul_of_isRealRooted
            (RealRooted.right_isRealRooted_of_isRealRooted_pair $h)
            (RealRooted.left_isRealRooted_of_isRealRooted_pair $h)),
          RealRooted.left_isRealRooted_of_prec $h,
          RealRooted.right_isRealRooted_of_prec $h,
          RealRooted.left_ne_zero_of_prec $h,
          RealRooted.right_ne_zero_of_prec $h,
          RealRooted.left_splits_of_prec $h,
          RealRooted.right_splits_of_prec $h,
          RealRooted.left_eq_zero_or_splits_of_prec $h,
          RealRooted.right_eq_zero_or_splits_of_prec $h,
          RealRooted.right_isRealRooted_of_interlaces $h,
          RealRooted.left_isRealRooted_of_interlaces $h,
          RealRooted.right_ne_zero_of_interlaces $h,
          RealRooted.left_ne_zero_of_interlaces $h,
          RealRooted.right_splits_of_interlaces $h,
          RealRooted.left_splits_of_interlaces $h,
          RealRooted.right_eq_zero_or_splits_of_interlaces $h,
          RealRooted.left_eq_zero_or_splits_of_interlaces $h)
  | `(tactic| rr_exact_realrooted_sequence_or_projection $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (RealRooted.at_of_isRealRooted_sequence $h _),
          RealRooted.ne_zero_of_isRealRooted_sequence $h,
          (RealRooted.ne_zero_of_isRealRooted_sequence $h _),
          RealRooted.splits_of_isRealRooted_sequence $h,
          (RealRooted.splits_of_isRealRooted_sequence $h _),
          RealRooted.eq_zero_or_splits_of_isRealRooted_sequence $h,
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence $h _))
  | `(tactic| rr_exact_realrooted_refine_then $h:term with $tac:tactic) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (by
            rr_refine_then $h with $tac))
  | `(tactic| rr_exact_realrooted_pair_sequence_or_projection $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (RealRooted.at_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_isRealRooted_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_isRealRooted_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_isRealRooted_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_isRealRooted_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_ne_zero_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_ne_zero_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_ne_zero_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_ne_zero_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_eq_zero_or_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_eq_zero_or_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_eq_zero_or_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_eq_zero_or_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.isRealRooted_mul_sequence_of_isRealRooted_pair_sequence $h,
          (RealRooted.isRealRooted_mul_sequence_of_isRealRooted_pair_sequence $h _),
          RealRooted.isRealRooted_swap_mul_sequence_of_isRealRooted_pair_sequence $h,
          (RealRooted.isRealRooted_swap_mul_sequence_of_isRealRooted_pair_sequence $h _))
  | `(tactic| rr_first_exact $[$hs:term],*) =>
      `(tactic|
        first
          $[ | exact $hs]*)
  | `(tactic| rr_first_exact_or_simpa $hdirect:term, $hnormalized:term) =>
      `(tactic|
        first
          | exact $hdirect
          | simpa using $hnormalized)
  | `(tactic| rr_first_exact_or_simpa_mul_assoc $hdirect:term, $hnormalized:term) =>
      `(tactic|
        first
          | exact $hdirect
          | simpa [mul_assoc] using $hnormalized)
  | `(tactic| rr_first_exact_or_simpa_mul_add_assoc $hdirect:term, $hnormalized:term) =>
      `(tactic|
        first
          | exact $hdirect
          | simpa [mul_assoc, add_assoc] using $hnormalized)
  | `(tactic| rr_first_realrooted_or_projection $[$hs:term],*) =>
      `(tactic|
        first
          $[ | rr_exact_realrooted_or_projection $hs]*)
  | `(tactic| rr_first_realrooted_sequence_or_projection $[$hs:term],*) =>
      `(tactic|
        first
          $[ | rr_exact_realrooted_sequence_or_projection $hs]*)
  | `(tactic| rr_first_exact_then_realrooted_sequence_or_projection $[$hs:term],*) =>
      `(tactic|
        first
          $[ | exact $hs]*
          $[ | rr_exact_realrooted_sequence_or_projection $hs]*)
  | `(tactic| rr_nonzero using $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (RealRooted.ne_zero_of_isRealRooted_sequence
            (RealRooted.isRealRooted_of_prec_chain_from_step $h)),
          (RealRooted.ne_zero_of_isRealRooted_sequence
            (RealRooted.isRealRooted_of_prec_chain_from_step $h) _),
          RealRooted.ne_zero_of_isRealRooted_sequence $h,
          (RealRooted.ne_zero_of_isRealRooted_sequence $h _),
          RealRooted.left_ne_zero_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_ne_zero_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_ne_zero_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_ne_zero_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_ne_zero_of_prec $h,
          RealRooted.right_ne_zero_of_prec $h,
          RealRooted.right_ne_zero_of_interlaces $h,
          RealRooted.left_ne_zero_of_interlaces $h,
          RealRooted.ne_zero_of_isRealRooted $h,
          RealRooted.left_ne_zero_of_isRealRooted_pair $h,
          RealRooted.right_ne_zero_of_isRealRooted_pair $h)
  | `(tactic| rr_nonzero) =>
      `(tactic|
        first
          | rr_lookup
          | rr_nonzero using rr_lookup_term
          | assumption
          | (apply RealRooted.ne_zero_of_natDegree_eq_one <;> rr_degree_eq_one)
          | exact Polynomial.X_ne_zero
          | exact Polynomial.X_add_C_ne_zero _
          | exact Polynomial.X_sub_C_ne_zero _
          | (rw [add_comm]; exact Polynomial.X_add_C_ne_zero _)
          | (apply Polynomial.C_ne_zero.mpr <;> rr_side_ne)
          | exact RealRooted.HasPosLeadingCoeff.ne_zero (by assumption)
          | (apply mul_ne_zero <;> rr_nonzero)
          | (apply pow_ne_zero <;> rr_nonzero)
          | (rw [Ne, Polynomial.reverse_eq_zero] <;> rr_nonzero)
          | exact Polynomial.derivative_ne_zero.mpr (by rr_close_side)
          | (intro hzero; simp_all [RealRooted.Prec, RealRooted.Interlaces])
          | simp_all [RealRooted.Prec, RealRooted.Interlaces])
  | `(tactic| rr_splits using $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (RealRooted.splits_of_isRealRooted_sequence
            (RealRooted.isRealRooted_of_prec_chain_from_step $h)),
          (RealRooted.splits_of_isRealRooted_sequence
            (RealRooted.isRealRooted_of_prec_chain_from_step $h) _),
          RealRooted.splits_of_isRealRooted_sequence $h,
          (RealRooted.splits_of_isRealRooted_sequence $h _),
          RealRooted.left_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.splits_mul_sequence_of_isRealRooted_pair_sequence $h,
          (RealRooted.splits_mul_sequence_of_isRealRooted_pair_sequence $h _),
          RealRooted.splits_swap_mul_sequence_of_isRealRooted_pair_sequence $h,
          (RealRooted.splits_swap_mul_sequence_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_splits_of_prec $h,
          RealRooted.right_splits_of_prec $h,
          RealRooted.right_splits_of_interlaces $h,
          RealRooted.left_splits_of_interlaces $h,
          RealRooted.splits_of_isRealRooted $h,
          RealRooted.left_splits_of_isRealRooted_pair $h,
          RealRooted.right_splits_of_isRealRooted_pair $h,
          RealRooted.mul_splits_of_isRealRooted_pair $h,
          RealRooted.swap_mul_splits_of_isRealRooted_pair $h,
          RealRooted.splits_pow_of_isRealRooted $h _,
          Polynomial.Splits.pow $h _,
          RealRooted.DegreeDropReversal.splits_reverse $h,
          RealRooted.DegreeDropReversal.splits_of_reverse $h,
          RealRooted.DegreeDropReversal.splits_X_pow_mul_reverse $h _,
          (RealRooted.DegreeDropReversal.splits_X_pow_mul_iff _).mpr $h,
          (RealRooted.DegreeDropReversal.splits_X_pow_mul_iff _).mp $h)
  | `(tactic|
      rr_splits_mul using
        left := $hleft:term,
        right := $hright:term) =>
      `(tactic|
        rr_first_exact
          Polynomial.Splits.mul $hleft $hright,
          (by
            simpa [mul_comm] using Polynomial.Splits.mul $hright $hleft))
  | `(tactic|
      rr_splits_pow using
        splits := $h:term,
        exponent := $n:term) =>
      `(tactic|
        exact Polynomial.Splits.pow $h $n)
  | `(tactic|
      rr_splits_reverse using
        splits := $h:term) =>
      `(tactic|
        exact RealRooted.DegreeDropReversal.splits_reverse $h)
  | `(tactic|
      rr_splits_of_reverse using
        reverse_splits := $h:term) =>
      `(tactic|
        exact RealRooted.DegreeDropReversal.splits_of_reverse $h)
  | `(tactic|
      rr_splits_reflect using
        splits := $h:term,
        degree_bound := $hN:term) =>
      `(tactic|
        exact RealRooted.DegreeDropReversal.splits_reflect_of_splits $h $hN)
  | `(tactic|
      rr_splits_X_pow_mul_reverse using
        splits := $h:term) =>
      `(tactic|
        exact RealRooted.DegreeDropReversal.splits_X_pow_mul_reverse $h _)
  | `(tactic|
      rr_splits_divX using
        coeff_zero := $h0:term,
        splits := $h:term) =>
      `(tactic|
        exact (RealRooted.DegreeDropReversal.splits_iff_divX_splits_of_coeff_zero
          $h0).1 $h)
  | `(tactic|
      rr_splits_of_divX using
        coeff_zero := $h0:term,
        divX_splits := $h:term) =>
      `(tactic|
        exact RealRooted.DegreeDropReversal.splits_of_divX_splits_of_coeff_zero
          $h0 $h)
  | `(tactic| rr_splits) =>
      `(tactic|
        first
          | rr_lookup
          | rr_splits using rr_lookup_term
          | assumption
          | exact Polynomial.Splits.C _
          | exact Polynomial.Splits.X
          | exact Polynomial.Splits.X_add_C _
          | exact Polynomial.Splits.X_sub_C _
          | exact Polynomial.Splits.X_pow _
          | exact Polynomial.Splits.C_mul_X_pow _ _
          | exact RealRooted.left_splits_of_interlaces
              (RealRooted.derivative_interlaces (by assumption) (by rr_close_side))
          | (apply Polynomial.Splits.mul <;> rr_splits)
          | (apply Polynomial.Splits.pow <;> rr_splits)
          | simp [add_comm]
          | (apply Polynomial.Splits.of_natDegree_le_one <;> rr_degree_le_one)
          | simp_all [RealRooted.Prec, RealRooted.Interlaces])
  | `(tactic| rr_zero_or_splits using $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence
            (RealRooted.isRealRooted_of_prec_chain_from_step $h)),
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence
            (RealRooted.isRealRooted_of_prec_chain_from_step $h) _),
          RealRooted.eq_zero_or_splits_of_isRealRooted $h,
          RealRooted.left_eq_zero_or_splits_of_eq_zero_or_splits_pair $h,
          RealRooted.right_eq_zero_or_splits_of_eq_zero_or_splits_pair $h,
          (RealRooted.mul_eq_zero_or_splits
            (RealRooted.left_eq_zero_or_splits_of_eq_zero_or_splits_pair $h)
            (RealRooted.right_eq_zero_or_splits_of_eq_zero_or_splits_pair $h)),
          (RealRooted.mul_eq_zero_or_splits
            (RealRooted.right_eq_zero_or_splits_of_eq_zero_or_splits_pair $h)
            (RealRooted.left_eq_zero_or_splits_of_eq_zero_or_splits_pair $h)),
          RealRooted.left_eq_zero_or_splits_of_isRealRooted_pair $h,
          RealRooted.right_eq_zero_or_splits_of_isRealRooted_pair $h,
          RealRooted.mul_eq_zero_or_splits_of_isRealRooted_pair $h,
          RealRooted.swap_mul_eq_zero_or_splits_of_isRealRooted_pair $h,
          RealRooted.left_eq_zero_or_splits_of_prec $h,
          RealRooted.right_eq_zero_or_splits_of_prec $h,
          RealRooted.right_eq_zero_or_splits_of_interlaces $h,
          RealRooted.left_eq_zero_or_splits_of_interlaces $h,
          RealRooted.eq_zero_or_splits_of_isRealRooted_sequence $h,
          (RealRooted.eq_zero_or_splits_of_isRealRooted_sequence $h _),
          RealRooted.left_eq_zero_or_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_eq_zero_or_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_eq_zero_or_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_eq_zero_or_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.mul_eq_zero_or_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.mul_eq_zero_or_splits_of_isRealRooted_pair_sequence $h _),
          RealRooted.swap_mul_eq_zero_or_splits_of_isRealRooted_pair_sequence $h,
          (RealRooted.swap_mul_eq_zero_or_splits_of_isRealRooted_pair_sequence
            $h _),
          RealRooted.left_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence $h,
          (RealRooted.left_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence $h _),
          RealRooted.right_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence $h,
          (RealRooted.right_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence $h _),
          (RealRooted.at_of_eq_zero_or_splits_pair_sequence $h _),
          RealRooted.mul_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence $h,
          (RealRooted.mul_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence $h _),
          RealRooted.swap_mul_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence $h,
          (RealRooted.swap_mul_eq_zero_or_splits_of_eq_zero_or_splits_pair_sequence
            $h _),
          Or.inr $h,
          Or.inr (Polynomial.Splits.pow $h _),
          Or.inr (RealRooted.DegreeDropReversal.splits_reverse $h),
          Or.inr (RealRooted.DegreeDropReversal.splits_of_reverse $h),
          Or.inr (RealRooted.DegreeDropReversal.splits_X_pow_mul_reverse $h _),
          Or.inr ((RealRooted.DegreeDropReversal.splits_X_pow_mul_iff _).mpr $h),
          Or.inr ((RealRooted.DegreeDropReversal.splits_X_pow_mul_iff _).mp $h),
          RealRooted.pow_eq_zero_or_splits $h _,
          RealRooted.pow_eq_zero_or_splits_of_isRealRooted $h _,
          RealRooted.reverse_eq_zero_or_splits $h,
          RealRooted.eq_zero_or_splits_of_reverse $h,
          RealRooted.X_pow_mul_reverse_eq_zero_or_splits $h _)
  | `(tactic|
      rr_zero_or_splits_mul using
        left := $hp:term,
        right := $hq:term) =>
      `(tactic|
        rr_first_exact
          RealRooted.mul_eq_zero_or_splits $hp $hq,
          RealRooted.mul_eq_zero_or_splits $hq $hp)
  | `(tactic|
      rr_zero_or_splits_pow using
        zero_or_splits := $h:term,
        exponent := $n:term) =>
      `(tactic|
        exact RealRooted.pow_eq_zero_or_splits $h $n)
  | `(tactic|
      rr_zero_or_splits_reverse using
        zero_or_splits := $h:term) =>
      `(tactic|
        exact RealRooted.reverse_eq_zero_or_splits $h)
  | `(tactic|
      rr_zero_or_splits_of_reverse using
        reverse_zero_or_splits := $h:term) =>
      `(tactic|
        exact RealRooted.eq_zero_or_splits_of_reverse $h)
  | `(tactic|
      rr_zero_or_splits_reflect using
        zero_or_splits := $h:term,
        degree_bound := $hN:term) =>
      `(tactic|
        exact RealRooted.reflect_eq_zero_or_splits $h $hN)
  | `(tactic|
      rr_zero_or_splits_X_pow_mul_reverse using
        zero_or_splits := $h:term) =>
      `(tactic|
        exact RealRooted.X_pow_mul_reverse_eq_zero_or_splits $h _)
  | `(tactic|
      rr_zero_or_splits_divX using
        coeff_zero := $h0:term,
        zero_or_splits := $h:term) =>
      `(tactic|
        exact RealRooted.divX_eq_zero_or_splits_of_coeff_zero $h0 $h)
  | `(tactic|
      rr_zero_or_splits_of_divX using
        coeff_zero := $h0:term,
        divX_zero_or_splits := $h:term) =>
      `(tactic|
        exact RealRooted.eq_zero_or_splits_of_divX $h0 $h)
  | `(tactic| rr_zero_or_splits) =>
      `(tactic|
        first
          | rr_lookup
          | rr_zero_or_splits using rr_lookup_term
          | assumption
          | (apply RealRooted.mul_eq_zero_or_splits <;> rr_zero_or_splits)
          | (apply RealRooted.pow_eq_zero_or_splits <;> rr_zero_or_splits)
          | exact Or.inr (by rr_splits)
          | simp_all [RealRooted.Prec, RealRooted.Interlaces])
  | `(tactic| rr_realrooted using $h:term) =>
      `(tactic|
        rr_first_exact
          $h,
          (RealRooted.isRealRooted_of_prec_chain_from_step $h),
          (RealRooted.isRealRooted_of_prec_chain_from_step $h _),
          (RealRooted.at_of_isRealRooted_sequence $h _),
          (RealRooted.at_of_isRealRooted_pair_sequence $h _),
          RealRooted.left_isRealRooted_of_isRealRooted_pair_sequence $h,
          (RealRooted.left_isRealRooted_of_isRealRooted_pair_sequence $h _),
          RealRooted.right_isRealRooted_of_isRealRooted_pair_sequence $h,
          (RealRooted.right_isRealRooted_of_isRealRooted_pair_sequence $h _),
          RealRooted.isRealRooted_mul_sequence_of_isRealRooted_pair_sequence $h,
          (RealRooted.isRealRooted_mul_sequence_of_isRealRooted_pair_sequence $h _),
          RealRooted.isRealRooted_swap_mul_sequence_of_isRealRooted_pair_sequence $h,
          (RealRooted.isRealRooted_swap_mul_sequence_of_isRealRooted_pair_sequence
            $h _),
          RealRooted.left_isRealRooted_of_prec $h,
          RealRooted.right_isRealRooted_of_prec $h,
          RealRooted.right_isRealRooted_of_interlaces $h,
          RealRooted.left_isRealRooted_of_interlaces $h,
          RealRooted.left_isRealRooted_of_isRealRooted_pair $h,
          RealRooted.right_isRealRooted_of_isRealRooted_pair $h,
          (RealRooted.isRealRooted_mul_of_isRealRooted
            (RealRooted.left_isRealRooted_of_isRealRooted_pair $h)
            (RealRooted.right_isRealRooted_of_isRealRooted_pair $h)),
          (RealRooted.isRealRooted_mul_of_isRealRooted
            (RealRooted.right_isRealRooted_of_isRealRooted_pair $h)
            (RealRooted.left_isRealRooted_of_isRealRooted_pair $h)),
          RealRooted.isRealRooted_pow_of_isRealRooted $h _,
          RealRooted.reverse_isRealRooted $h,
          RealRooted.isRealRooted_of_reverse $h,
          RealRooted.X_pow_mul_reverse_isRealRooted $h _)
  | `(tactic| rr_mul_realrooted using $hp:term, $hq:term) =>
      `(tactic|
        rr_first_realrooted_or_projection
          (RealRooted.isRealRooted_mul_of_isRealRooted $hp $hq),
          (RealRooted.isRealRooted_mul_of_isRealRooted $hq $hp))
  | `(tactic|
      rr_mul_realrooted using
        left := $hp:term,
        right := $hq:term) =>
      `(tactic|
        rr_mul_realrooted using $hp, $hq)
  | `(tactic|
      rr_pow_realrooted using
        realrooted := $hp:term,
        exponent := $n:term) =>
      `(tactic|
        rr_first_realrooted_or_projection
          (RealRooted.isRealRooted_pow_of_isRealRooted $hp $n))
  | `(tactic|
      rr_realrooted_reverse using
        realrooted := $h:term) =>
      `(tactic|
        exact RealRooted.reverse_isRealRooted $h)
  | `(tactic|
      rr_realrooted_of_reverse using
        reverse_realrooted := $h:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_of_reverse $h)
  | `(tactic|
      rr_realrooted_reflect using
        realrooted := $h:term,
        degree_bound := $hN:term) =>
      `(tactic|
        exact RealRooted.reflect_isRealRooted $h $hN)
  | `(tactic|
      rr_realrooted_X_pow_mul_reverse using
        realrooted := $h:term) =>
      `(tactic|
        exact RealRooted.X_pow_mul_reverse_isRealRooted $h _)
  | `(tactic|
      rr_realrooted_divX using
        coeff_zero := $h0:term,
        realrooted := $h:term) =>
      `(tactic|
        exact RealRooted.divX_isRealRooted_of_coeff_zero $h0 $h)
  | `(tactic|
      rr_realrooted_of_divX using
        coeff_zero := $h0:term,
        divX_realrooted := $h:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_of_divX $h0 $h)
  | `(tactic| rr_realrooted) =>
      `(tactic|
        first
          | rr_lookup
          | rr_realrooted using rr_lookup_term
          | assumption
          | (exact ⟨by rr_nonzero, by rr_splits⟩ <;> done)
          | simp_all [RealRooted.Prec, RealRooted.Interlaces])
  | `(tactic| rr_interlaces using $hprec:term, $hdeg:term) =>
      `(tactic|
        rr_first_exact
          RealRooted.Prec.toInterlaces $hprec $hdeg,
          RealRooted.Prec.toInterlaces $hprec ($hdeg).symm)
  | `(tactic| rr_interlaces using $hprec:term) =>
      `(tactic|
        exact RealRooted.Prec.toInterlaces $hprec (by rr_close_side))
  | `(tactic| rr_prec0 using $hprec:term) =>
      `(tactic|
        rr_first_exact
          $hprec,
          RealRooted.Prec.toPrec0 $hprec,
          RealRooted.Prec.toPrec0 (RealRooted.Interlaces.toPrec $hprec))
  | `(tactic| rr_prec using $hinter:term) =>
      `(tactic|
        rr_first_exact
          $hinter,
          RealRooted.Interlaces.toPrec $hinter)
  | `(tactic| rr_prec using $hprec0:term, $hf:term, $hg:term) =>
      `(tactic|
        exact RealRooted.Prec0.toPrec_of_ne $hprec0 $hf $hg)
  | `(tactic| rr_gsturm_cons using $hprec:term, $htail:term) =>
      `(tactic|
        simpa [RealRooted.IsGeneralizedSturmSeq] using And.intro $hprec $htail)
  | `(tactic| rr_sturm_cons using $hinter:term, $htail:term) =>
      `(tactic|
        simpa [RealRooted.IsSturmSeq] using And.intro $hinter $htail)
  | `(tactic| rr_sturm_base) =>
      `(tactic|
        simp [RealRooted.IsSturmSeq, RealRooted.IsGeneralizedSturmSeq])
  | `(tactic|
      rr_prec_sequence using
        base := $hbase:term,
        step := $hstep:term) =>
      `(tactic|
        exact RealRooted.prec_sequence_of_base_and_step $hbase $hstep)
  | `(tactic|
      rr_prec_sequence_realrooted using
        base := $hbase:term,
        step := $hstep:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_sequence $hbase $hstep))
  | `(tactic|
      rr_finish_sequence using
        base := $hbase:term,
        step := $hstep:term) =>
      `(tactic|
        rr_prec_sequence_realrooted using
          base := $hbase,
          step := $hstep)
  | `(tactic|
      rr_finish_sequence using
        prec := $hprec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_chain_from_step $hprec))
  | `(tactic|
      rr_finish_sequence using
        prec := $hprec:term,
        degree := $hdegree:term) =>
      `(tactic|
        first
          | exact RealRooted.interlaces_of_prec_chain $hprec $hdegree
          | exact RealRooted.interlaces_of_prec_chain $hprec (fun n => ($hdegree n).symm)
          | exact (RealRooted.interlaces_of_prec_chain $hprec $hdegree _)
          | exact (RealRooted.interlaces_of_prec_chain
              $hprec (fun n => ($hdegree n).symm) _)
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_prec_chain_from_step $hprec))
  | `(tactic|
      rr_prec_sequence_branches using
        base := $hbase:term,
        degree := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        exact RealRooted.prec_sequence_of_base_and_degree_branches
          $hbase $hbranch $hsame $hsucc)
  | `(tactic|
      rr_prec_sequence_branches using
        base := $hbase:term,
        degree_branch := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        exact RealRooted.prec_sequence_of_base_and_degree_branches
          $hbase $hbranch $hsame $hsucc)
  | `(tactic|
      rr_prec_sequence_branches_realrooted using
        base := $hbase:term,
        degree := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_sequence_degree_branches
            $hbase $hbranch $hsame $hsucc))
  | `(tactic|
      rr_prec_sequence_branches_realrooted using
        base := $hbase:term,
        degree_branch := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_sequence_degree_branches
            $hbase $hbranch $hsame $hsucc))
  | `(tactic|
      rr_finish_sequence_branches using
        base := $hbase:term,
        degree := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        rr_prec_sequence_branches_realrooted using
          base := $hbase,
          degree := $hbranch,
          same := $hsame,
          successor := $hsucc)
  | `(tactic|
      rr_finish_sequence_branches using
        base := $hbase:term,
        degree_branch := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        rr_prec_sequence_branches_realrooted using
          base := $hbase,
          degree_branch := $hbranch,
          same := $hsame,
          successor := $hsucc)
  | `(tactic| rr_finish using $h:term) =>
      `(tactic|
        first
          | exact $h
          | exact RealRooted.derivative_interlaces $h (by rr_close_side)
          | exact (RealRooted.derivative_interlaces $h (by rr_close_side)).toPrec
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_prec_chain_from_step $h)
          | rr_exact_realrooted_sequence_or_projection $h
          | rr_exact_realrooted_pair_sequence_or_projection $h
          | rr_exact_realrooted_or_projection $h
          | rr_zero_or_splits using $h
          | exact RealRooted.natDegree_succ_of_interlaces $h
          | exact (RealRooted.natDegree_succ_of_interlaces $h).symm
          | exact RealRooted.Prec.toInterlaces $h (by rr_close_side)
          | exact RealRooted.Interlaces.toPrec $h
          | exact RealRooted.Prec.toPrec0 $h
          | exact RealRooted.Prec.toPrec0 (RealRooted.Interlaces.toPrec $h)
          | rr_close_side)
  | `(tactic| rr_finish using $hprec:term, $hdeg:term) =>
      `(tactic|
        first
          | exact RealRooted.interlaces_of_prec_chain $hprec $hdeg
          | exact RealRooted.interlaces_of_prec_chain $hprec (fun n => ($hdeg n).symm)
          | exact (RealRooted.interlaces_of_prec_chain $hprec $hdeg _)
          | exact (RealRooted.interlaces_of_prec_chain
              $hprec (fun n => ($hdeg n).symm) _)
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_prec_chain_from_step $hprec)
          | exact RealRooted.Prec.toInterlaces $hprec $hdeg
          | exact RealRooted.Prec.toInterlaces $hprec ($hdeg).symm
          | exact RealRooted.prec_sequence_of_base_and_step $hprec $hdeg
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_prec_sequence $hprec $hdeg)
          | simpa [RealRooted.IsGeneralizedSturmSeq] using
              And.intro $hprec $hdeg
          | simpa [RealRooted.IsSturmSeq] using And.intro $hprec $hdeg)
  | `(tactic| rr_finish using $hprec0:term, $hf:term, $hg:term) =>
      `(tactic| exact RealRooted.Prec0.toPrec_of_ne $hprec0 $hf $hg)
  | `(tactic| rr_finish using $hbase:term, $hbranch:term, $hsame:term, $hsucc:term) =>
      `(tactic|
        first
          | exact RealRooted.prec_sequence_of_base_and_degree_branches
              $hbase $hbranch $hsame $hsucc
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_prec_sequence_degree_branches
                $hbase $hbranch $hsame $hsucc))
  | `(tactic| rr_finish) =>
      `(tactic|
        first
          | rr_lookup
          | assumption
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_prec_chain_from_step rr_lookup_term)
          | exact RealRooted.interlaces_of_prec_chain rr_lookup_term rr_lookup_term
          | exact RealRooted.interlaces_of_prec_chain
              rr_lookup_term (fun n => (rr_lookup_term n).symm)
          | rr_exact_realrooted_sequence_or_projection rr_lookup_term
          | rr_exact_realrooted_pair_sequence_or_projection rr_lookup_term
          | rr_exact_realrooted_or_projection rr_lookup_term
          | exact RealRooted.natDegree_succ_of_interlaces rr_lookup_term
          | exact (RealRooted.natDegree_succ_of_interlaces rr_lookup_term).symm
          | exact rr_lookup_interlaces_term
          | exact RealRooted.derivative_interlaces (by rr_splits) (by rr_close_side)
          | exact (RealRooted.derivative_interlaces (by rr_splits) (by rr_close_side)).toPrec
          | exact RealRooted.Interlaces.toPrec rr_lookup_term
          | exact RealRooted.ne_zero_of_natDegree_eq_one (by rr_degree_eq_one)
          | (apply Polynomial.Splits.of_natDegree_le_one <;> rr_degree_le_one)
          | exact RealRooted.Prec.toPrec0 (RealRooted.Interlaces.toPrec rr_lookup_term)
          | (exact ⟨by rr_nonzero, by rr_splits⟩ <;> done)
          | rr_zero_or_splits
          | rr_sign
          | simp_all [
              RealRooted.Prec,
              RealRooted.Prec0,
              RealRooted.Interlaces,
              RealRooted.IsSturmSeq,
              RealRooted.IsGeneralizedSturmSeq]
          | rr_close_side)

end Tactic
end RealRooted
