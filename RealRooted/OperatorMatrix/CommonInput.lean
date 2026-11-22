module

public import RealRooted.OperatorMatrix.Bounded
import RealRooted.OperatorMatrix.RowCommonInput
import RealRooted.AffineFamily.PF
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Three common-input tests for arbitrary operator blocks

The column, proportional-input and successor-input tests characterize ordered-PF preservation
for arbitrary real-linear entries. Output degrees are unrestricted; entries need not commute.
The successor test is restricted to degrees below the input cap, and is vacuous at cap zero.

Source: unpublished manuscript, `full-operator-block-common-input-reduction.md`, general block
reduction, and `shifted-operator-row-reduction.md`; RealRooted issue #1781.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.OperatorMatrix

/-- Test (C) through input degree `N`: both columns give ordered PF pairs on a common input. -/
def CommonInputColumnsUpTo (N : ℕ) (A B C D : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ h, IsPFPolynomial h → h.natDegree ≤ N →
    (IsPFPolynomial (A h) ∧ IsPFPolynomial (C h) ∧ Interl (A h) (C h)) ∧
    (IsPFPolynomial (B h) ∧ IsPFPolynomial (D h) ∧ Interl (B h) (D h))

/-- Test (P) through input degree `N`: every positive proportional-input ray is ordered PF. -/
def CommonInputProportionalUpTo (N : ℕ) (A B C D : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ h, IsPFPolynomial h → h.natDegree ≤ N → ∀ r : ℝ, 0 < r →
    IsPFPolynomial (A h + Polynomial.C r * B h) ∧
      IsPFPolynomial (C h + Polynomial.C r * D h) ∧
      Interl (A h + Polynomial.C r * B h) (C h + Polynomial.C r * D h)

/-- Test (X) below input degree `N`: the ordered input is `(r h, X h)`. The strict degree
inequality is exactly `deg h ≤ N - 1` when `N ≠ 0`, and omits this test when `N = 0`. -/
def CommonInputSuccessorUpTo (N : ℕ) (A B C D : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ h, IsPFPolynomial h → h.natDegree < N → ∀ r : ℝ, 0 < r →
    IsPFPolynomial (Polynomial.C r * A h + B (X * h)) ∧
      IsPFPolynomial (Polynomial.C r * C h + D (X * h)) ∧
      Interl (Polynomial.C r * A h + B (X * h))
        (Polynomial.C r * C h + D (X * h))

/-- Test (C) on PF inputs of arbitrary degree. -/
def CommonInputColumns (A B C D : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ h, IsPFPolynomial h →
    (IsPFPolynomial (A h) ∧ IsPFPolynomial (C h) ∧ Interl (A h) (C h)) ∧
    (IsPFPolynomial (B h) ∧ IsPFPolynomial (D h) ∧ Interl (B h) (D h))

/-- Test (P) on PF inputs of arbitrary degree. -/
def CommonInputProportional (A B C D : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ h, IsPFPolynomial h → ∀ r : ℝ, 0 < r →
    IsPFPolynomial (A h + Polynomial.C r * B h) ∧
      IsPFPolynomial (C h + Polynomial.C r * D h) ∧
      Interl (A h + Polynomial.C r * B h) (C h + Polynomial.C r * D h)

/-- Test (X) on PF inputs of arbitrary degree. -/
def CommonInputSuccessor (A B C D : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ h, IsPFPolynomial h → ∀ r : ℝ, 0 < r →
    IsPFPolynomial (Polynomial.C r * A h + B (X * h)) ∧
      IsPFPolynomial (Polynomial.C r * C h + D (X * h)) ∧
      Interl (Polynomial.C r * A h + B (X * h))
        (Polynomial.C r * C h + D (X * h))

private lemma map_const_mul (A : ℝ[X] →ₗ[ℝ] ℝ[X]) (r : ℝ) (h : ℝ[X]) :
    A (Polynomial.C r * h) = Polynomial.C r * A h := by
  rw [← smul_eq_C_mul, A.map_smul, smul_eq_C_mul]

/-- Necessity uses the zero columns, proportional inputs and successor inputs separately. -/
private lemma tests_of_preservesUpTo {N : ℕ} {A B C D : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hpres : PreservesOrderedPFPairUpTo N A B C D) :
    CommonInputColumnsUpTo N A B C D ∧ CommonInputProportionalUpTo N A B C D ∧
      CommonInputSuccessorUpTo N A B C D := by
  refine ⟨?_, ?_, ?_⟩
  · intro h hh hhN
    constructor
    · simpa using hpres h 0 hh IsPFPolynomial.zero (interl_zero_right h) hhN (by simp)
    · simpa using hpres 0 h IsPFPolynomial.zero hh (interl_zero_left h) (by simp) hhN
  · intro h hh hhN r hr
    simpa only [map_const_mul] using hpres h (Polynomial.C r * h) hh (hh.const_mul hr)
      (hh.interl_self.C_mul_right_of_nonneg hr.le) hhN
      ((natDegree_C_mul_le _ _).trans hhN)
  · intro h hh hhN r hr
    have hXh : (X * h).natDegree ≤ N :=
      natDegree_mul_le.trans (by simp only [natDegree_X]; lia)
    have hself := interl_mul_X_of_interl hh.interl_self
      hh.hasNonnegCoeffs hh.hasNonnegCoeffs
    simpa only [map_const_mul] using hpres (Polynomial.C r * h) (X * h)
      (hh.const_mul hr) hh.X_mul (hself.C_mul_left_of_nonneg hr.le)
      ((natDegree_C_mul_le _ _).trans hhN.le) hXh

/-- Apply the row theorem with the proportional test in its `A h + r B h` normalization. -/
private lemma row_of_tests {N : ℕ} (A B : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hA : ∀ h, IsPFPolynomial h → h.natDegree ≤ N → IsPFPolynomial (A h))
    (hB : ∀ h, IsPFPolynomial h → h.natDegree ≤ N → IsPFPolynomial (B h))
    (hP : ∀ h, IsPFPolynomial h → h.natDegree ≤ N → ∀ r : ℝ, 0 < r →
      IsPFPolynomial (A h + Polynomial.C r * B h))
    (hX : ∀ h, IsPFPolynomial h → h.natDegree < N → ∀ r : ℝ, 0 < r →
      IsPFPolynomial (Polynomial.C r * A h + B (X * h))) :
    ∀ p q, IsPFPolynomial p → IsPFPolynomial q → Interl p q →
      p.natDegree ≤ N → q.natDegree ≤ N → IsPFPolynomial (A p + B q) := by
  apply (row_preserves_iff_commonInputUpTo N A B hA hB _).mpr hX
  intro h hh hhN
  apply Compatible.comm
  apply (compatible_iff_isPFPolynomial_pos (hB h hh hhN) (hA h hh hhN)).mpr
  intro r hr
  simpa only [add_comm] using hP h hh hhN r hr

/-- Apply the row reduction to an affine pencil of the two output coordinates. Multiplication
is postcomposition on each entry, so no entries are commuted. -/
private lemma affine_row_of_tests {N : ℕ} {A B C D : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hC : CommonInputColumnsUpTo N A B C D)
    (hP : CommonInputProportionalUpTo N A B C D)
    (hX : CommonInputSuccessorUpTo N A B C D)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Interl p q)
    (hpN : p.natDegree ≤ N) (hqN : q.natDegree ≤ N) :
    IsPFPolynomial ((Polynomial.C s * X + Polynomial.C t) * (A p + B q) +
      (C p + D q)) := by
  let L : ℝ[X] := Polynomial.C s * X + Polynomial.C t
  let U := (LinearMap.mulLeft ℝ L).comp A + C
  let V := (LinearMap.mulLeft ℝ L).comp B + D
  have hU (h : ℝ[X]) : U h = L * A h + C h := rfl
  have hV (h : ℝ[X]) : V h = L * B h + D h := rfl
  have hout : IsPFPolynomial (U p + V q) := by
    apply row_of_tests U V
    · intro h hh hhN
      exact (hC h hh hhN).1.2.2.isPFPolynomial_affine
        (hC h hh hhN).1.1 (hC h hh hhN).1.2.1 hs ht
    · intro h hh hhN
      exact (hC h hh hhN).2.2.2.isPFPolynomial_affine
        (hC h hh hhN).2.1 (hC h hh hhN).2.2.1 hs ht
    · intro h hh hhN r hr
      obtain ⟨hf, hg, hfg⟩ := hP h hh hhN r hr
      have hpf := hfg.isPFPolynomial_affine hf hg hs ht
      have heq : U h + Polynomial.C r * V h =
          L * (A h + Polynomial.C r * B h) + (C h + Polynomial.C r * D h) := by
        rw [hU, hV]
        ring
      rwa [heq]
    · intro h hh hhN r hr
      obtain ⟨hf, hg, hfg⟩ := hX h hh hhN r hr
      have hpf := hfg.isPFPolynomial_affine hf hg hs ht
      have heq : Polynomial.C r * U h + V (X * h) =
          L * (Polynomial.C r * A h + B (X * h)) +
            (Polynomial.C r * C h + D (X * h)) := by
        rw [hU, hV]
        ring
      rwa [heq]
    · exact hp
    · exact hq
    · exact hpq
    · exact hpN
    · exact hqN
  have heq : U p + V q = L * (A p + B q) + (C p + D q) := by
    rw [hU, hV]
    ring
  rwa [heq] at hout

/-- Three common-input tests characterize bounded block preservation, including cap zero.
Both output PF conditions remain explicit throughout the equivalence. -/
theorem PreservesOrderedPFPairUpTo.iff_commonInput (N : ℕ)
    (A B C D : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    PreservesOrderedPFPairUpTo N A B C D ↔
      CommonInputColumnsUpTo N A B C D ∧ CommonInputProportionalUpTo N A B C D ∧
        CommonInputSuccessorUpTo N A B C D := by
  refine ⟨tests_of_preservesUpTo, ?_⟩
  rintro ⟨hC, hP, hX⟩
  rw [PreservesOrderedPFPairUpTo.iff_affine]
  intro p q hp hq hpq hpN hqN
  have htop : IsPFPolynomial (A p + B q) := row_of_tests A B
    (fun h hh hhN => (hC h hh hhN).1.1)
    (fun h hh hhN => (hC h hh hhN).2.1)
    (fun h hh hhN r hr => (hP h hh hhN r hr).1)
    (fun h hh hhN r hr => (hX h hh hhN r hr).1) p q hp hq hpq hpN hqN
  have hbot : IsPFPolynomial (C p + D q) := row_of_tests C D
    (fun h hh hhN => (hC h hh hhN).1.2.1)
    (fun h hh hhN => (hC h hh hhN).2.2.1)
    (fun h hh hhN r hr => (hP h hh hhN r hr).2.1)
    (fun h hh hhN r hr => (hX h hh hhN r hr).2.1) p q hp hq hpq hpN hqN
  exact ⟨htop, hbot, fun _ _ hs ht => affine_row_of_tests hC hP hX hs ht hp hq hpq hpN hqN⟩

/-- At cap zero the successor-input test is omitted altogether. -/
theorem PreservesOrderedPFPairUpTo.iff_commonInput_zero
    (A B C D : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    PreservesOrderedPFPairUpTo 0 A B C D ↔
      CommonInputColumnsUpTo 0 A B C D ∧ CommonInputProportionalUpTo 0 A B C D := by
  rw [PreservesOrderedPFPairUpTo.iff_commonInput]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨hC, hP⟩
    refine ⟨hC, hP, ?_⟩
    intro h _ hhN
    exact (Nat.not_lt_zero _ hhN).elim

/-- For a nonzero cap the successor-input test uses exactly degree `N - 1`. -/
theorem commonInputSuccessorUpTo_iff {N : ℕ} (hN : N ≠ 0)
    (A B C D : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    CommonInputSuccessorUpTo N A B C D ↔
      ∀ h, IsPFPolynomial h → h.natDegree ≤ N - 1 → ∀ r : ℝ, 0 < r →
        IsPFPolynomial (Polynomial.C r * A h + B (X * h)) ∧
          IsPFPolynomial (Polynomial.C r * C h + D (X * h)) ∧
          Interl (Polynomial.C r * A h + B (X * h))
            (Polynomial.C r * C h + D (X * h)) := by
  constructor
  · intro hX h hh hhN
    exact hX h hh (by lia)
  · intro hX h hh hhN
    exact hX h hh (by lia)

/-- The unrestricted three-test equivalence for arbitrary, possibly noncommuting entries. -/
theorem PreservesOrderedPFPair.iff_commonInput (A B C D : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    PreservesOrderedPFPair A B C D ↔
      CommonInputColumns A B C D ∧ CommonInputProportional A B C D ∧
        CommonInputSuccessor A B C D := by
  constructor
  · intro hpres
    have htests (N : ℕ) :=
      (PreservesOrderedPFPairUpTo.iff_commonInput N A B C D).mp (hpres.upTo N)
    refine ⟨fun h hh => (htests h.natDegree).1 h hh le_rfl,
      fun h hh => (htests h.natDegree).2.1 h hh le_rfl,
      fun h hh => (htests (h.natDegree + 1)).2.2 h hh (by lia)⟩
  · rintro ⟨hC, hP, hX⟩
    rw [preservesOrderedPFPair_iff_forall_upTo]
    intro N
    exact (PreservesOrderedPFPairUpTo.iff_commonInput N A B C D).mpr
      ⟨fun h hh _ => hC h hh, fun h hh _ => hP h hh, fun h hh _ => hX h hh⟩

/-- For at least two rows and columns the three tests on every ordered rectangle characterize
matrix preservation. Empty and singleton dimensions retain their existing separate interfaces. -/
theorem PreservesOrderedPF.iff_commonInput {m n : ℕ}
    (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X]) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    PreservesOrderedPF M ↔ ∀ i k j l, i < k → j < l →
      CommonInputColumns (M i j) (M i l) (M k j) (M k l) ∧
        CommonInputProportional (M i j) (M i l) (M k j) (M k l) ∧
        CommonInputSuccessor (M i j) (M i l) (M k j) (M k l) := by
  rw [PreservesOrderedPF.iff_forall_blocks_of_two_le M hm hn]
  simp only [PreservesBlock, PreservesOrderedPFPair.iff_commonInput]

/-- The rectangular common-input equivalence also holds at every bounded input cap, including
zero, and checks all ordered row and column pairs, not just adjacent ones. -/
theorem PreservesOrderedPFUpTo.iff_commonInput {m n : ℕ} (N : ℕ)
    (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X]) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    PreservesOrderedPFUpTo N M ↔ ∀ i k j l, i < k → j < l →
      CommonInputColumnsUpTo N (M i j) (M i l) (M k j) (M k l) ∧
        CommonInputProportionalUpTo N (M i j) (M i l) (M k j) (M k l) ∧
        CommonInputSuccessorUpTo N (M i j) (M i l) (M k j) (M k l) := by
  rw [PreservesOrderedPFUpTo.iff_forall_blocks_of_two_le N M hm hn]
  simp only [PreservesOrderedPFPairUpTo.iff_commonInput]

end RealRooted.OperatorMatrix
