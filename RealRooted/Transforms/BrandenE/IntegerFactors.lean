module

public import RealRooted.Transforms.BrandenE.Basic
import RealRooted.MaWang.EndpointTwoSided
import Mathlib.Tactic

/-!
# E transforms of integer linear factors

The endpoint-multiplicity criterion gives a convenient algebraic route to
Haglund--Ono--Wagner (1999), Theorem 1. A product of integer linear factors
has an E image rooted in `[-1, 0]` if it contains one copy of every factor
between its extreme parameters and the interval `[0, 1]`.

We start with a consecutive block of factors, then insert the remaining
factors. The endpoint multiplicities make every insertion admissible.
-/

@[expose] public section

open Polynomial

namespace RealRooted

noncomputable section

/-- The product of the affine factors `X + c` in an integer multiset. -/
def integerFactorProduct (s : Multiset ℤ) : ℝ[X] :=
  (s.map fun c : ℤ => X + C (c : ℝ)).prod

/-- One copy of the integer parameters `1 - m, …, 0, 1, …, b`. -/
def integerFactorInterval (m b : ℕ) : Multiset ℤ :=
  ((Multiset.range m).map fun i : ℕ => -(i : ℤ)) +
    ((Multiset.range b).map fun i : ℕ => (i : ℤ) + 1)

private def EndpointData (m b : ℕ) (p : ℝ[X]) : Prop :=
  HasPosLeadingCoeff p ∧ p.Splits ∧
    (∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) ∧
    p.rootMultiplicity 0 = m ∧ p.rootMultiplicity (-1) = b

private theorem integerFactorProduct_cons (c : ℤ) (s : Multiset ℤ) :
    integerFactorProduct (c ::ₘ s) = (X + C (c : ℝ)) * integerFactorProduct s := by
  simp [integerFactorProduct]

private theorem brandenE_integerFactorProduct_cons (c : ℤ) (s : Multiset ℤ) :
    brandenE (integerFactorProduct (c ::ₘ s)) =
      MaWang.endpointStep 1 1 (c : ℝ) (brandenE (integerFactorProduct s)) := by
  rw [integerFactorProduct_cons, brandenE_mul_X_add_C]
  simp [MaWang.endpointStep, add_comm]

private theorem endpointData_one : EndpointData 0 0 1 := by
  refine ⟨hasPosLeadingCoeff_one, Splits.one, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp

private theorem EndpointData.step {m b : ℕ} {p : ℝ[X]}
    (hp : EndpointData m b p) (c : ℝ) (hlo : 0 ≤ c + m) (hhi : c ≤ 1 + b) :
    EndpointData (if c + m = 0 then m + 1 else m)
      (if c = 1 + b then b + 1 else b) (MaWang.endpointStep 1 1 c p) := by
  obtain ⟨hlc, hs, hr, hm, hb⟩ := hp
  obtain ⟨-, hlc', hs', -, hroots, hzero, hneg⟩ :=
    affineEndpointStep_closed (c := c) one_pos hlc hs hr
  refine ⟨hlc', hs', hroots.mpr ?_, ?_, ?_⟩
  · rw [hm, hb]
    exact ⟨hlo, by linarith⟩
  · simpa [hm] using hzero
  · simpa [hb] using hneg

private theorem integerFactorInterval_succ_left (m : ℕ) :
    integerFactorInterval (m + 1) 0 = -(m : ℤ) ::ₘ integerFactorInterval m 0 := by
  simp [integerFactorInterval, Multiset.range_succ]

private theorem integerFactorInterval_succ_right (m b : ℕ) :
    integerFactorInterval m (b + 1) =
      ((b : ℤ) + 1) ::ₘ integerFactorInterval m b := by
  simp [integerFactorInterval, Multiset.range_succ, Multiset.add_cons]

private theorem endpointData_interval (m b : ℕ) :
    EndpointData m b (brandenE (integerFactorProduct (integerFactorInterval m b))) := by
  have hbase : ∀ m : ℕ,
      EndpointData m 0 (brandenE (integerFactorProduct (integerFactorInterval m 0))) := by
    intro m
    induction m with
    | zero =>
        have hEone : brandenE (1 : ℝ[X]) = 1 := by
          simpa only [pow_zero, orderedBellPolynomial_zero] using
            (brandenE_X_pow (R := ℝ) 0)
        simpa [integerFactorInterval, integerFactorProduct, hEone] using endpointData_one
    | succ m ih =>
        rw [integerFactorInterval_succ_left, brandenE_integerFactorProduct_cons]
        have hm0 : (0 : ℝ) ≤ m := by positivity
        have hne : -(m : ℝ) ≠ 1 := by linarith
        simpa [hne] using ih.step (-(m : ℝ)) (by linarith) (by linarith)
  induction b with
  | zero => exact hbase m
  | succ b ih =>
      rw [integerFactorInterval_succ_right, brandenE_integerFactorProduct_cons]
      have hne : (1 : ℝ) + b + m ≠ 0 := by positivity
      have hc : (((b : ℤ) + 1 : ℤ) : ℝ) = 1 + (b : ℝ) := by push_cast; ring
      rw [hc]
      simpa [hne] using ih.step (1 + (b : ℝ)) (by positivity) le_rfl

private theorem endpointData_interval_add (m b : ℕ) (s : Multiset ℤ)
    (hs : ∀ c ∈ s, 1 - (m : ℤ) ≤ c ∧ c ≤ b) :
    EndpointData m b
      (brandenE (integerFactorProduct (integerFactorInterval m b + s))) := by
  induction s using Multiset.induction_on with
  | empty => simpa using endpointData_interval m b
  | @cons c s ih =>
      have hc := hs c (Multiset.mem_cons_self c s)
      have ih' := ih fun d hd => hs d (Multiset.mem_cons_of_mem hd)
      rw [Multiset.add_cons, brandenE_integerFactorProduct_cons]
      have hlo : 0 < (c : ℝ) + m := by exact_mod_cast (show 0 < c + (m : ℤ) by lia)
      have hhi : (c : ℝ) < 1 + b := by exact_mod_cast (show c < 1 + (b : ℤ) by lia)
      simpa [ne_of_gt hlo, ne_of_lt hhi] using
        ih'.step (c : ℝ) hlo.le hhi.le

/-- An integer-factor product containing the complete consecutive block
between its extreme parameters and `[0, 1]` has an E image rooted in `[-1, 0]`.
Repeated factors are allowed. -/
theorem brandenE_integerFactorProduct_roots_mem_Icc
    (s : Multiset ℤ) (m b : ℕ) (hblock : integerFactorInterval m b ≤ s)
    (hbound : ∀ c ∈ s, 1 - (m : ℤ) ≤ c ∧ c ≤ b) :
    HasPosLeadingCoeff (brandenE (integerFactorProduct s)) ∧
      (brandenE (integerFactorProduct s)).Splits ∧
      ∀ r ∈ (brandenE (integerFactorProduct s)).roots, r ∈ Set.Icc (-1 : ℝ) 0 := by
  obtain ⟨t, rfl⟩ := le_iff_exists_add.mp hblock
  have ht : ∀ c ∈ t, 1 - (m : ℤ) ≤ c ∧ c ≤ b :=
    fun c hc => hbound c (Multiset.mem_add.mpr (Or.inr hc))
  obtain ⟨hlc, hs, hr, -, -⟩ := endpointData_interval_add m b t ht
  exact ⟨hlc, hs, hr⟩

end

end RealRooted
