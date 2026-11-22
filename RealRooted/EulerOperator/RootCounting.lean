module

public import RealRooted.EulerOperator
public import RealRooted.MultiplierSequence
import RealRooted.EulerOperator.Polar.RealParameter
import RealRooted.Mathlib.Analysis.Calculus.LocalExtr.PolynomialEuler
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Products of polar Euler operators

A finite product of the operators `a - X D` can lose at most one positive
root for each factor. On a reflected PF polynomial, factors whose parameter
exceeds the original degree lose no positive roots. This is the root-count
step in Pólya's arithmetic-section argument.
-/

@[expose] public section

open Polynomial

namespace RealRooted

/-- The commuting product of the polar Euler operators with natural parameters
listed in a multiset. Repeated parameters are retained. -/
noncomputable def polarThetaProduct (s : Multiset ℕ) (p : ℝ[X]) : ℝ[X] :=
  diagonalOperator (fun k => (s.map fun a : ℕ => (a : ℝ) - k).prod) p

@[simp] theorem coeff_polarThetaProduct (s : Multiset ℕ) (p : ℝ[X]) (k : ℕ) :
    (polarThetaProduct s p).coeff k = (s.map fun a : ℕ => (a : ℝ) - k).prod * p.coeff k :=
  coeff_diagonalOperator _ _ _

@[simp] theorem polarThetaProduct_zero (p : ℝ[X]) : polarThetaProduct 0 p = p := by
  ext k
  simp

@[simp] theorem polarThetaProduct_cons (a : ℕ) (s : Multiset ℕ) (p : ℝ[X]) :
    polarThetaProduct (a ::ₘ s) p = polarTheta a (polarThetaProduct s p) := by
  ext k
  simp [polarTheta, sub_mul, mul_assoc]

theorem polarThetaProduct_add (s t : Multiset ℕ) (p : ℝ[X]) :
    polarThetaProduct (s + t) p = polarThetaProduct s (polarThetaProduct t p) := by
  ext k
  simp [mul_assoc]

theorem natDegree_polarThetaProduct_le (s : Multiset ℕ) (p : ℝ[X]) :
    (polarThetaProduct s p).natDegree ≤ p.natDegree :=
  natDegree_diagonalOperator_le _ _

/-- A product of polar Euler operators preserves every coefficient whose
index is absent from its parameter multiset. -/
theorem coeff_polarThetaProduct_ne_zero {s : Multiset ℕ} {p : ℝ[X]} {k : ℕ}
    (hk : k ∉ s) (hp : p.coeff k ≠ 0) : (polarThetaProduct s p).coeff k ≠ 0 := by
  classical
  induction s using Multiset.induction with
  | empty => simpa using hp
  | cons a s ih =>
    rw [polarThetaProduct_cons]
    simp only [polarTheta, coeff_sub, coeff_C_mul, coeff_theta, ← sub_mul]
    apply mul_ne_zero _ (ih fun h => hk (Multiset.mem_cons_of_mem h))
    exact sub_ne_zero.mpr (by
      intro h
      have he : a = k := Nat.cast_inj.mp h
      exact hk (he ▸ Multiset.mem_cons_self a s))

/-- When the leading index is not a parameter, no degree is lost. -/
theorem natDegree_polarThetaProduct {s : Multiset ℕ} {p : ℝ[X]}
    (hs : p.natDegree ∉ s) : (polarThetaProduct s p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp [hp, polarThetaProduct]
  apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_polarThetaProduct_le s p)
  exact coeff_polarThetaProduct_ne_zero hs (leadingCoeff_ne_zero.mpr hp)

/-- Parameters strictly beyond the degree preserve the PF property. -/
theorem IsPFPolynomial.polarThetaProduct {p : ℝ[X]} (hp : IsPFPolynomial p)
    {s : Multiset ℕ} (hs : ∀ a ∈ s, p.natDegree < a) :
    IsPFPolynomial (polarThetaProduct s p) := by
  induction s using Multiset.induction with
  | empty => simpa using hp
  | cons a s ih =>
    rw [polarThetaProduct_cons]
    apply isPFPolynomial_C_mul_sub_theta
      (n := p.natDegree) (by exact_mod_cast hs a (Multiset.mem_cons_self _ _))
      (ih fun b hb => hs b (Multiset.mem_cons_of_mem hb))
      (natDegree_polarThetaProduct_le s p)

/-- Products with nonzero natural parameters lose at most their number of
positive roots. A nonzero constant coefficient rules out zero intermediate outputs. -/
theorem card_pos_roots_le_polarThetaProduct_add_card {p : ℝ[X]}
    (hp : p.coeff 0 ≠ 0) {s : Multiset ℕ} (hs : 0 ∉ s) :
    (p.roots.filter (0 < ·)).card ≤
      ((polarThetaProduct s p).roots.filter (0 < ·)).card + s.card := by
  classical
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have hs0 : 0 ∉ s := fun h => hs (Multiset.mem_cons_of_mem h)
    have hq : polarThetaProduct (a ::ₘ s) p ≠ 0 := by
      intro h
      exact coeff_polarThetaProduct_ne_zero hs hp (by rw [h, coeff_zero])
    have heuler : X * (polarThetaProduct s p).derivative -
        C (a : ℝ) * polarThetaProduct s p = -polarThetaProduct (a ::ₘ s) p := by
      rw [polarThetaProduct_cons]
      simp only [polarTheta, theta, neg_sub]
    have hb := (polarThetaProduct s p).card_pos_roots_le_euler_sub_add_one a
      (by rw [heuler]; exact neg_ne_zero.mpr hq)
    rw [heuler, roots_neg] at hb
    have hi := ih hs0
    simpa only [Multiset.card_cons, Nat.add_assoc, Nat.add_comm 1 s.card]
      using hi.trans (Nat.add_le_add_right hb s.card)

/-- Reflecting a PF polynomial with nonzero constant coefficient puts every
root strictly on the positive real axis. -/
theorem IsPFPolynomial.card_pos_roots_comp_neg_X {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : p.coeff 0 ≠ 0) : ((p.comp (-X)).roots.filter (0 < ·)).card = p.natDegree := by
  classical
  rw [roots_comp_neg_X, Multiset.filter_map]
  have hf : p.roots.filter (fun x => 0 < -x) = p.roots := by
    apply Multiset.filter_eq_self.mpr
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact h0 (by simpa only [← coeff_zero_eq_eval_zero] using (isRoot_of_mem_roots hx).eq_zero)
    exact neg_pos.mpr (lt_of_le_of_ne (hp.roots_nonpos x hx) hx0)
  simp only [Function.comp_def] at *
  rw [hf, Multiset.card_map]
  exact splits_iff_card_roots.mp hp.splits

/-- Polar Euler products commute with reflection of their polynomial input. -/
theorem polarThetaProduct_comp_neg_X (s : Multiset ℕ) (p : ℝ[X]) :
    polarThetaProduct s (p.comp (-X)) = (polarThetaProduct s p).comp (-X) := by
  ext k
  simp only [coeff_polarThetaProduct, coeff_comp_neg_X]
  ring

/-- Only parameters at or below the original degree can reduce the positive
root count of a reflected PF polynomial. -/
theorem IsPFPolynomial.natDegree_le_card_pos_roots_polarThetaProduct
    {p : ℝ[X]} (hp : IsPFPolynomial p) (h0 : p.coeff 0 ≠ 0)
    {s : Multiset ℕ} (hs : 0 ∉ s) :
    p.natDegree ≤ ((RealRooted.polarThetaProduct s (p.comp (-X))).roots.filter (0 < ·)).card +
      (s.filter (· ≤ p.natDegree)).card := by
  classical
  let small := s.filter (· ≤ p.natDegree)
  let large := s.filter (fun a => ¬a ≤ p.natDegree)
  have hsplit : s = small + large := (Multiset.filter_add_not _ s).symm
  have hlarge : ∀ a ∈ large, p.natDegree < a := by
    intro a ha
    exact Nat.lt_of_not_ge (Multiset.mem_filter.mp ha).2
  have hl0 : 0 ∉ large := fun h => hs (Multiset.mem_filter.mp h).1
  have hp0 := coeff_polarThetaProduct_ne_zero hl0 h0
  have hpdegree : (RealRooted.polarThetaProduct large p).natDegree = p.natDegree :=
    natDegree_polarThetaProduct (fun h => (hlarge _ h).false)
  have hcount := (hp.polarThetaProduct hlarge).card_pos_roots_comp_neg_X hp0
  have hbound := card_pos_roots_le_polarThetaProduct_add_card
    (p := (RealRooted.polarThetaProduct large p).comp (-X))
    (by simpa only [coeff_comp_neg_X, pow_zero, mul_one] using hp0)
    (s := small) (fun h => hs (Multiset.mem_filter.mp h).1)
  rw [hcount, hpdegree] at hbound
  nth_rw 1 [hsplit]
  rw [polarThetaProduct_add, polarThetaProduct_comp_neg_X]
  exact hbound

end RealRooted
