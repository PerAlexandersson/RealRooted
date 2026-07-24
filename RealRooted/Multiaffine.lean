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
