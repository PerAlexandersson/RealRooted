import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Multiaffine multivariate polynomials

This file defines multiaffineness by a degree bound in each variable and
provides the elementary closure properties needed for polarization and the
multiaffine Lieb--Sokal theorem.
-/

open BigOperators

namespace MvPolynomial

/-- A multivariate polynomial has degree at most one in every variable. -/
def IsMultiaffine {R σ : Type*} [CommSemiring R] (p : MvPolynomial σ R) : Prop :=
  ∀ i, p.degreeOf i ≤ 1

namespace IsMultiaffine

variable {R σ τ : Type*} [CommSemiring R]

theorem zero : IsMultiaffine (0 : MvPolynomial σ R) := by
  intro i
  simp [MvPolynomial.degreeOf_zero]

theorem C (r : R) : IsMultiaffine (MvPolynomial.C r : MvPolynomial σ R) := by
  intro i
  simp [MvPolynomial.degreeOf_C]

theorem X [Nontrivial R] (i : σ) :
    IsMultiaffine (MvPolynomial.X i : MvPolynomial σ R) := by
  intro j
  classical
  rw [MvPolynomial.degreeOf_X]
  split <;> simp_all

theorem add {p q : MvPolynomial σ R} (hp : IsMultiaffine p)
    (hq : IsMultiaffine q) : IsMultiaffine (p + q) := by
  intro i
  exact (MvPolynomial.degreeOf_add_le i p q).trans (max_le (hp i) (hq i))

theorem neg {S : Type*} [CommRing S] {p : MvPolynomial σ S}
    (hp : IsMultiaffine p) : IsMultiaffine (-p) := by
  intro i
  rw [MvPolynomial.degreeOf_neg]
  exact hp i

theorem sub {S : Type*} [CommRing S] {p q : MvPolynomial σ S}
    (hp : IsMultiaffine p) (hq : IsMultiaffine q) : IsMultiaffine (p - q) := by
  rw [sub_eq_add_neg]
  exact hp.add hq.neg

theorem sum {I : Type*} {s : Finset I} {p : I → MvPolynomial σ R}
    (hp : ∀ i ∈ s, IsMultiaffine (p i)) :
    IsMultiaffine (∑ i ∈ s, p i) := by
  intro j
  exact (MvPolynomial.degreeOf_sum_le j s p).trans
    (Finset.sup_le fun i hi => hp i hi j)

theorem C_mul {p : MvPolynomial σ R} (hp : IsMultiaffine p) (r : R) :
    IsMultiaffine (MvPolynomial.C r * p) := by
  intro i
  exact (MvPolynomial.degreeOf_C_mul_le p i r).trans (hp i)

/-- Partial differentiation preserves multiaffineness. -/
theorem pderiv {p : MvPolynomial σ R} (hp : IsMultiaffine p) (i : σ) :
    IsMultiaffine (MvPolynomial.pderiv i p) := by
  intro j
  rw [MvPolynomial.as_sum p]
  simp only [map_sum]
  refine (MvPolynomial.degreeOf_sum_le j p.support fun d =>
    MvPolynomial.pderiv i (MvPolynomial.monomial d (p.coeff d))).trans ?_
  apply Finset.sup_le
  intro d hd
  rw [MvPolynomial.pderiv_monomial]
  by_cases hc : p.coeff d * d i = 0
  · simp [hc]
  · rw [MvPolynomial.degreeOf_monomial_eq _ j hc]
    exact (Nat.sub_le _ _).trans
      (MvPolynomial.degreeOf_le_iff.mp (hp j) d hd)

private theorem eval_update_monomial_affine
    {S : Type*} [CommRing S] [DecidableEq σ]
    (i : σ) (z : σ → S) (t : S) (d : σ →₀ ℕ) (c : S)
    (hdi : d i ≤ 1) :
    MvPolynomial.eval (Function.update z i t) (MvPolynomial.monomial d c) =
      MvPolynomial.eval z
          (MvPolynomial.pderiv i (MvPolynomial.monomial d c)) * t +
        MvPolynomial.eval (Function.update z i 0) (MvPolynomial.monomial d c) := by
  rw [MvPolynomial.eval_monomial, MvPolynomial.pderiv_monomial,
    MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  have hcases : d i = 0 ∨ d i = 1 := by lia
  rcases hcases with h | h
  · have hi : i ∉ d.support := by simpa [Finsupp.mem_support_iff] using h
    have hupdate (u : S) :
        d.prod (fun j e => Function.update z i u j ^ e) =
          d.prod (fun j e => z j ^ e) := by
      apply Finsupp.prod_congr
      intro j hj
      have hji : j ≠ i := by
        intro hji
        subst j
        exact hi hj
      simp [hji]
    rw [hupdate t, hupdate 0]
    simp [h]
  · have hi : i ∈ d.support := by simp [Finsupp.mem_support_iff, h]
    have herase : d - Finsupp.single i 1 = d.erase i := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [h]
      · simp [Finsupp.single_eq_of_ne hji, Finsupp.erase, hji]
    rw [herase]
    have hleft := Finsupp.mul_prod_erase d i
      (fun j e => Function.update z i t j ^ e) hi
    have hzero := Finsupp.mul_prod_erase d i
      (fun j e => Function.update z i 0 j ^ e) hi
    have hzprod :
        (d.erase i).prod (fun j e => z j ^ e) =
          (d.erase i).prod (fun j e => Function.update z i t j ^ e) := by
      apply Finsupp.prod_congr
      intro j hj
      have hji : j ≠ i := by
        intro hji
        subst j
        simp at hj
      simp [hji]
    rw [← hleft, ← hzero]
    simp [h, hzprod]
    ring

/-- Evaluation of a multiaffine polynomial is affine in each coordinate, with
linear coefficient given by the corresponding partial derivative. -/
theorem eval_update_eq_eval_pderiv_mul_add
    {S : Type*} [CommRing S] [DecidableEq σ]
    {p : MvPolynomial σ S} (hp : IsMultiaffine p)
    (i : σ) (z : σ → S) (t : S) :
    MvPolynomial.eval (Function.update z i t) p =
      MvPolynomial.eval z (MvPolynomial.pderiv i p) * t +
        MvPolynomial.eval (Function.update z i 0) p := by
  rw [MvPolynomial.as_sum p]
  simp only [map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  exact eval_update_monomial_affine i z t d (p.coeff d)
    (MvPolynomial.degreeOf_le_iff.mp (hp i) d hd)

theorem rename {p : MvPolynomial σ R} (hp : IsMultiaffine p)
    {f : σ → τ} (hf : Function.Injective f) :
    IsMultiaffine (MvPolynomial.rename f p) := by
  intro j
  classical
  by_cases hj : j ∈ (MvPolynomial.rename f p).vars
  · obtain ⟨i, hi, rfl⟩ := MvPolynomial.mem_vars_rename f p hj
    rw [MvPolynomial.degreeOf_rename_of_injective hf]
    exact hp i
  · have hzero : (MvPolynomial.rename f p).degreeOf j = 0 := by
      exact not_ne_iff.mp
        ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero).not.mp hj)
    simp [hzero]

/-- A product of multiaffine polynomials in disjoint variable sets is
multiaffine. -/
theorem mul_of_disjoint_vars {p q : MvPolynomial σ R}
    (hp : IsMultiaffine p) (hq : IsMultiaffine q)
    (hdisj : Disjoint p.vars q.vars) : IsMultiaffine (p * q) := by
  intro i
  refine (MvPolynomial.degreeOf_mul_le i p q).trans ?_
  by_cases hi : i ∈ p.vars
  · have hqi : i ∉ q.vars := Finset.disjoint_left.mp hdisj hi
    have hqzero : q.degreeOf i = 0 := by
      exact not_ne_iff.mp
        ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero).not.mp hqi)
    simpa [hqzero] using hp i
  · have hpzero : p.degreeOf i = 0 := by
      exact not_ne_iff.mp
        ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero).not.mp hi)
    simpa [hpzero] using hq i

theorem prod_X [Nontrivial R] (s : Finset σ) :
    IsMultiaffine (∏ i ∈ s, (MvPolynomial.X i : MvPolynomial σ R)) := by
  classical
  intro i
  refine (MvPolynomial.degreeOf_prod_le i s fun j => MvPolynomial.X j).trans ?_
  simp only [MvPolynomial.degreeOf_X]
  by_cases hi : i ∈ s
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [hji.symm]
    · exact fun h => (h hi).elim
  · simp [Finset.sum_eq_zero, hi]

theorem esymm [Fintype σ] [Nontrivial R] (n : ℕ) :
    IsMultiaffine (MvPolynomial.esymm σ R n) := by
  classical
  rw [MvPolynomial.esymm]
  exact sum fun s hs => prod_X s

end IsMultiaffine

end MvPolynomial
