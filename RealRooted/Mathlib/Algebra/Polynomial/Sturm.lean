import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.List.GetD

/-!
# Signed polynomial remainder sequences

This file defines the finite signed Euclidean remainder sequence used by
Sturm's theorem.  Starting from `p, q`, each later entry is the negative
remainder of the preceding pair.  The zero remainder is not included.
-/

open scoped Polynomial

namespace Polynomial

noncomputable section

variable {K : Type*} [Field K]

local instance instDecidableEqSturm : DecidableEq K := Classical.decEq K

/-- The signed Euclidean remainder sequence beginning with `p, q`.

If `q = 0`, the sequence is the singleton `[p]`.  Otherwise its tail is the
sequence beginning with `q` and `-(p % q)`.  Strict degree descent of the
second argument proves termination. -/
def signedRemainderSequence (p q : K[X]) : List K[X] :=
  if _hq : q = 0 then [p]
  else p :: signedRemainderSequence q (-(p % q))
termination_by q.degree
decreasing_by
  simpa only [degree_neg] using degree_mod_lt p _hq

@[simp]
theorem signedRemainderSequence_zero_right (p : K[X]) :
    signedRemainderSequence p 0 = [p] := by
  rw [signedRemainderSequence]
  simp

theorem signedRemainderSequence_ne_zero_right (p : K[X]) {q : K[X]}
    (hq : q ≠ 0) :
    signedRemainderSequence p q =
      p :: signedRemainderSequence q (-(p % q)) := by
  rw [signedRemainderSequence]
  simp [hq]

@[simp]
theorem signedRemainderSequence_ne_nil (p q : K[X]) :
    signedRemainderSequence p q ≠ [] := by
  rw [signedRemainderSequence]
  split <;> simp

@[simp]
theorem head?_signedRemainderSequence (p q : K[X]) :
    (signedRemainderSequence p q).head? = some p := by
  rw [signedRemainderSequence]
  split <;> simp

theorem exists_tail_signedRemainderSequence (p q : K[X]) :
    ∃ l : List K[X], signedRemainderSequence p q = p :: l := by
  rw [signedRemainderSequence]
  split
  · exact ⟨[], rfl⟩
  · exact ⟨signedRemainderSequence q (-(p % q)), rfl⟩

theorem signedRemainderSequence_length_pos (p q : K[X]) :
    0 < (signedRemainderSequence p q).length :=
  List.length_pos_iff.mpr (signedRemainderSequence_ne_nil p q)

theorem one_lt_length_signedRemainderSequence {p q : K[X]} (hq : q ≠ 0) :
    1 < (signedRemainderSequence p q).length := by
  rw [signedRemainderSequence_ne_zero_right p hq]
  simp [signedRemainderSequence_length_pos]

/-- The defining signed-remainder identity. -/
theorem div_mul_sub_neg_mod (p q : K[X]) :
    p = (p / q) * q - (-(p % q)) := by
  rw [sub_neg_eq_add, mul_comm]
  exact (EuclideanDomain.div_add_mod p q).symm

/-- Consecutive signed remainders strictly decrease in degree while the next
remainder is nonzero. -/
theorem degree_neg_mod_lt (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    (-(p % q)).degree < q.degree := by
  simpa only [degree_neg] using degree_mod_lt p hq

/-- Two polynomials have no common root in the coefficient field. -/
def NoCommonRoot (p q : K[X]) : Prop :=
  ∀ x : K, ¬ (p.IsRoot x ∧ q.IsRoot x)

theorem NoCommonRoot.symm {p q : K[X]} (h : NoCommonRoot p q) :
    NoCommonRoot q p := by
  intro x hx
  exact h x hx.symm

theorem noCommonRoot_zero_right_iff {p : K[X]} :
    NoCommonRoot p 0 ↔ ∀ x : K, ¬ p.IsRoot x := by
  simp [NoCommonRoot]

/-- The no-common-root invariant passes to the next Euclidean pair. -/
theorem NoCommonRoot.next {p q : K[X]} (h : NoCommonRoot p q) :
    NoCommonRoot q (-(p % q)) := by
  intro x hx
  apply h x
  refine ⟨?_, hx.1⟩
  rw [IsRoot, ← EuclideanDomain.div_add_mod p q, eval_add, eval_mul]
  have hqeval : q.eval x = 0 := by simpa [IsRoot] using hx.1
  have hmodeval : (p % q).eval x = 0 := by
    simpa [IsRoot] using hx.2
  simp [hqeval, hmodeval]

/-- Structural signed-remainder identities for every three consecutive
entries of a list. -/
def IsSignedRemainderChain : List K[X] → Prop
  | p :: q :: r :: l =>
      (∃ s : K[X], p = s * q - r) ∧ IsSignedRemainderChain (q :: r :: l)
  | _ => True

/-- The canonical sequence satisfies all consecutive signed-remainder
identities. -/
theorem isSignedRemainderChain_signedRemainderSequence (p q : K[X]) :
    IsSignedRemainderChain (signedRemainderSequence p q) := by
  by_cases hq : q = 0
  · subst q
    simp [IsSignedRemainderChain]
  · rw [signedRemainderSequence_ne_zero_right p hq]
    by_cases hr : -(p % q) = 0
    · rw [hr, signedRemainderSequence_zero_right]
      simp [IsSignedRemainderChain]
    · have htail :=
        signedRemainderSequence_ne_zero_right q hr
      rw [htail]
      obtain ⟨t, ht⟩ := exists_tail_signedRemainderSequence
        (-(p % q)) (-(q % (-(p % q))))
      rw [ht]
      change (∃ s : K[X], p = s * q - (-(p % q))) ∧
        IsSignedRemainderChain (q :: -(p % q) :: t)
      refine ⟨⟨p / q, div_mul_sub_neg_mod p q⟩, ?_⟩
      have hrec := isSignedRemainderChain_signedRemainderSequence q (-(p % q))
      rw [htail, ht] at hrec
      exact hrec
termination_by q.degree
decreasing_by
  simpa only [degree_neg] using degree_mod_lt p hq

/-- Adjacent entries in the canonical sequence have no common root whenever
the initial pair has none. -/
theorem isChain_noCommonRoot_signedRemainderSequence {p q : K[X]}
    (h : NoCommonRoot p q) :
    (signedRemainderSequence p q).IsChain NoCommonRoot := by
  by_cases hq : q = 0
  · subst q
    simp
  · rw [signedRemainderSequence_ne_zero_right p hq]
    have hnext : NoCommonRoot q (-(p % q)) := h.next
    have htail := isChain_noCommonRoot_signedRemainderSequence hnext
    rw [List.isChain_cons]
    refine ⟨?_, htail⟩
    simpa using h
termination_by q.degree
decreasing_by
  simpa only [degree_neg] using degree_mod_lt p hq

/-- An interior zero in a signed remainder chain is nodal: its two neighboring
values are nonzero and have opposite signs. -/
theorem eval_neighbors_mul_neg_of_isSignedRemainderChain
    {l : List K[X]} (hrem : IsSignedRemainderChain l)
    (hcop : l.IsChain NoCommonRoot) (x : K) (i : ℕ)
    (hi : i + 2 < l.length) (hzero : l[i + 1].eval x = 0) :
    l[i].eval x * l[i + 2].eval x ≠ 0 := by
  induction l generalizing i with
  | nil => simp at hi
  | cons p l ih =>
      cases l with
      | nil => simp at hi
      | cons q l =>
          cases l with
          | nil => simp at hi
          | cons r l =>
              cases i with
              | zero =>
                  simp only [zero_add, List.getElem_cons_zero,
                    List.getElem_cons_succ] at hzero ⊢
                  rcases hrem.1 with ⟨s, hs⟩
                  have hqr : NoCommonRoot q r :=
                    List.IsChain.rel (List.IsChain.of_cons hcop)
                  have hrne : r.eval x ≠ 0 := by
                    intro hrzero
                    exact hqr x ⟨by simpa [IsRoot] using hzero,
                      by simpa [IsRoot] using hrzero⟩
                  have hpval : p.eval x = -r.eval x := by
                    rw [hs, eval_sub, eval_mul, hzero, mul_zero, zero_sub]
                  rw [hpval]
                  exact mul_ne_zero (neg_ne_zero.mpr hrne) hrne
              | succ i =>
                  have hi' : i + 2 < (q :: r :: l).length := by
                    simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hi
                  have hzero' : (q :: r :: l)[i + 1].eval x = 0 := by
                    simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hzero
                  simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
                    ih hrem.2 (List.IsChain.of_cons hcop) i hi' hzero'

/-- At an interior zero, the left neighboring value is the negative of the
right neighboring value. -/
theorem eval_left_eq_neg_right_of_isSignedRemainderChain
    {l : List K[X]} (hrem : IsSignedRemainderChain l) (x : K) (i : ℕ)
    (hi : i + 2 < l.length) (hzero : l[i + 1].eval x = 0) :
    l[i].eval x = -l[i + 2].eval x := by
  induction l generalizing i with
  | nil => simp at hi
  | cons p l ih =>
      cases l with
      | nil => simp at hi
      | cons q l =>
          cases l with
          | nil => simp at hi
          | cons r l =>
              cases i with
              | zero =>
                  simp only [zero_add, List.getElem_cons_zero,
                    List.getElem_cons_succ] at hzero ⊢
                  rcases hrem.1 with ⟨s, hs⟩
                  rw [hs, eval_sub, eval_mul, hzero, mul_zero, zero_sub]
              | succ i =>
                  have hi' : i + 2 < (q :: r :: l).length := by
                    simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hi
                  have hzero' : (q :: r :: l)[i + 1].eval x = 0 := by
                    simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hzero
                  simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
                    ih hrem.2 i hi' hzero'

/-- Over an ordered field, the nodal neighbors in a signed remainder chain
have strictly negative product. -/
theorem eval_neighbors_mul_neg_of_isSignedRemainderChain_of_linearOrder
    {l : List K[X]} [LinearOrder K] [IsStrictOrderedRing K]
    (hrem : IsSignedRemainderChain l) (hcop : l.IsChain NoCommonRoot)
    (x : K) (i : ℕ) (hi : i + 2 < l.length)
    (hzero : l[i + 1].eval x = 0) :
    l[i].eval x * l[i + 2].eval x < 0 := by
  have hne := eval_neighbors_mul_neg_of_isSignedRemainderChain
    hrem hcop x i hi hzero
  have hpval := eval_left_eq_neg_right_of_isSignedRemainderChain
    hrem x i hi hzero
  have hrne : l[i + 2].eval x ≠ 0 := by
    intro hr
    apply hne
    simp [hr]
  rw [hpval]
  linarith [sq_pos_of_ne_zero hrne]

/-- The final entry of a no-common-root signed remainder sequence has no root.
Equivalently, it is the real-root-free terminal gcd factor relevant to Sturm's
theorem. -/
theorem eval_getLast_signedRemainderSequence_ne_zero {p q : K[X]}
    (h : NoCommonRoot p q) (x : K) :
    ((signedRemainderSequence p q).getLast
        (signedRemainderSequence_ne_nil p q)).eval x ≠ 0 := by
  by_cases hq : q = 0
  · subst q
    simp only [signedRemainderSequence_zero_right, List.getLast_singleton]
    intro hp
    exact h x ⟨by simpa [IsRoot] using hp, by simp⟩
  · have hnext : NoCommonRoot q (-(p % q)) := h.next
    simpa [signedRemainderSequence_ne_zero_right p hq] using
      eval_getLast_signedRemainderSequence_ne_zero hnext x
termination_by q.degree
decreasing_by
  simpa only [degree_neg] using degree_mod_lt p hq

end

end Polynomial
