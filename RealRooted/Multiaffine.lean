import RealRooted.Mathlib.RingTheory.MvPolynomial.Symmetric
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

/-- Partial differentiation does not increase the degree in any coordinate. -/
theorem degreeOf_pderiv_le {R σ : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (i j : σ) :
    (MvPolynomial.pderiv i p).degreeOf j ≤ p.degreeOf j := by
  conv_lhs => rw [MvPolynomial.as_sum p]
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
      (MvPolynomial.degreeOf_le_iff.mp le_rfl d hd)

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
  exact (MvPolynomial.degreeOf_pderiv_le p i j).trans (hp j)

/-- Differentiating a multiaffine polynomial twice in the same variable gives
zero. -/
theorem pderiv_pderiv_self_eq_zero {p : MvPolynomial σ R}
    (hp : IsMultiaffine p) (i : σ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv i p) = 0 := by
  rw [MvPolynomial.as_sum p]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.pderiv_monomial]
  have hdi : d i ≤ 1 := MvPolynomial.degreeOf_le_iff.mp (hp i) d hd
  have hcases : d i = 0 ∨ d i = 1 := by lia
  rcases hcases with h | h <;> simp [h]

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

/-- Evaluation is affine in a coordinate whose degree is at most one, with
linear coefficient given by the corresponding partial derivative. -/
theorem _root_.MvPolynomial.eval_update_eq_eval_pderiv_mul_add_of_degreeOf_le_one
    {S : Type*} [CommRing S] [DecidableEq σ]
    {p : MvPolynomial σ S} {i : σ} (hi : p.degreeOf i ≤ 1)
    (z : σ → S) (t : S) :
    MvPolynomial.eval (Function.update z i t) p =
      MvPolynomial.eval z (MvPolynomial.pderiv i p) * t +
        MvPolynomial.eval (Function.update z i 0) p := by
  rw [MvPolynomial.as_sum p]
  simp only [map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  exact eval_update_monomial_affine i z t d (p.coeff d)
    (MvPolynomial.degreeOf_le_iff.mp hi d hd)

/-- Evaluation of a multiaffine polynomial is affine in each coordinate, with
linear coefficient given by the corresponding partial derivative. -/
theorem eval_update_eq_eval_pderiv_mul_add
    {S : Type*} [CommRing S] [DecidableEq σ]
    {p : MvPolynomial σ S} (hp : IsMultiaffine p)
    (i : σ) (z : σ → S) (t : S) :
    MvPolynomial.eval (Function.update z i t) p =
      MvPolynomial.eval z (MvPolynomial.pderiv i p) * t +
        MvPolynomial.eval (Function.update z i 0) p := by
  exact MvPolynomial.eval_update_eq_eval_pderiv_mul_add_of_degreeOf_le_one
    (hp i) z t

/-- The partial derivative of a multiaffine polynomial is independent of the
differentiated coordinate. -/
theorem eval_update_pderiv_eq
    {S : Type*} [CommRing S] [DecidableEq σ]
    {p : MvPolynomial σ S} (hp : IsMultiaffine p)
    (i : σ) (z : σ → S) (t : S) :
    MvPolynomial.eval (Function.update z i t) (MvPolynomial.pderiv i p) =
      MvPolynomial.eval z (MvPolynomial.pderiv i p) := by
  rw [(hp.pderiv i).eval_update_eq_eval_pderiv_mul_add]
  rw [hp.pderiv_pderiv_self_eq_zero i]
  simp only [map_zero, zero_mul, zero_add]
  have h := (hp.pderiv i).eval_update_eq_eval_pderiv_mul_add i z (z i)
  rw [hp.pderiv_pderiv_self_eq_zero i] at h
  simpa only [Function.update_eq_self, map_zero, zero_mul, zero_add] using h.symm

end IsMultiaffine

/-- Set one variable to zero while retaining the ambient variable type. -/
noncomputable def specializeZero {S : Type*} [CommRing S]
    (i : σ) (p : MvPolynomial σ S) : MvPolynomial σ S :=
  ∑ d ∈ p.support.filter fun d => d i = 0,
    MvPolynomial.monomial d (p.coeff d)

@[simp] theorem coeff_specializeZero
    {S : Type*} [CommRing S]
    (i : σ) (p : MvPolynomial σ S) (d : σ →₀ ℕ) :
    coeff d (specializeZero i p) = if d i = 0 then coeff d p else 0 := by
  classical
  rw [specializeZero, coeff_sum]
  by_cases hd : d i = 0
  · rw [if_pos hd]
    by_cases hp : d ∈ p.support
    · rw [Finset.sum_eq_single d]
      · simp
      · intro e he hed
        simp [hed]
      · simp [hp, hd]
    · rw [Finset.sum_eq_zero]
      · exact (notMem_support_iff.mp hp).symm
      · intro e he
        have hed : e ≠ d := by
          intro hed
          subst e
          exact hp (Finset.mem_filter.mp he).1
        simp [hed]
  · rw [if_neg hd, Finset.sum_eq_zero]
    intro e he
    have hei : e i = 0 := (Finset.mem_filter.mp he).2
    have hed : e ≠ d := by
      intro hed
      subst e
      exact hd hei
    simp [hed]

@[simp] theorem specializeZero_zero
    {S : Type*} [CommRing S] (i : σ) :
    specializeZero i (0 : MvPolynomial σ S) = 0 := by
  simp [specializeZero]

theorem specializeZero_monomial
    {S : Type*} [CommRing S] (i : σ) (d : σ →₀ ℕ) (c : S) :
    specializeZero i (MvPolynomial.monomial d c) =
      if d i = 0 then MvPolynomial.monomial d c else 0 := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  rw [specializeZero, MvPolynomial.support_monomial, if_neg hc]
  simp only [Finset.sum_filter]
  by_cases hdi : d i = 0 <;> simp [hdi]

@[simp] theorem eval_specializeZero
    {S : Type*} [CommRing S] [DecidableEq σ]
    (i : σ) (p : MvPolynomial σ S) (z : σ → S) :
    MvPolynomial.eval z (specializeZero i p) =
      MvPolynomial.eval (Function.update z i 0) p := by
  rw [specializeZero]
  simp only [map_sum, Finset.sum_filter]
  conv_rhs => rw [MvPolynomial.as_sum p]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdi : d i = 0
  · simp only [if_pos hdi]
    rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
    congr 1
    apply Finsupp.prod_congr
    intro j hj
    have hji : j ≠ i := by
      intro h
      subst j
      exact (Finsupp.mem_support_iff.mp hj) hdi
    simp [hji]
  · rw [if_neg hdi, MvPolynomial.eval_monomial]
    have hi : i ∈ d.support := by simpa [Finsupp.mem_support_iff]
    have hprod : d.prod (fun j e => Function.update z i 0 j ^ e) = 0 := by
      rw [Finsupp.prod]
      apply Finset.prod_eq_zero hi
      rw [Function.update_self]
      exact zero_pow hdi
    rw [hprod]
    simp

theorem specializeZero_add
    {S : Type*} [CommRing S]
    (i : σ) (p q : MvPolynomial σ S) :
    specializeZero i (p + q) = specializeZero i p + specializeZero i q := by
  ext d
  simp only [coeff_specializeZero, coeff_add]
  split <;> simp

theorem specializeZero_mul
    {S : Type*} [CommRing S]
    (i : σ) (p q : MvPolynomial σ S) :
    specializeZero i (p * q) = specializeZero i p * specializeZero i q := by
  classical
  ext d
  rw [coeff_specializeZero, coeff_mul, coeff_mul]
  simp only [coeff_specializeZero]
  by_cases hd : d i = 0
  · simp only [hd, if_pos]
    apply Finset.sum_congr rfl
    intro x hx
    have hxy : x.1 i + x.2 i = 0 := by
      have hsum : x.1 + x.2 = d := Finset.mem_antidiagonal.mp hx
      rw [← Finsupp.add_apply, hsum, hd]
    have hx0 : x.1 i = 0 := (Nat.add_eq_zero_iff.mp hxy).1
    have hy0 : x.2 i = 0 := (Nat.add_eq_zero_iff.mp hxy).2
    simp [hx0, hy0]
  · simp only [hd, if_false]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hx0 : x.1 i = 0
    · have hy0 : x.2 i ≠ 0 := by
        intro hy0
        apply hd
        have hsum : x.1 + x.2 = d := Finset.mem_antidiagonal.mp hx
        rw [← hsum, Finsupp.add_apply, hx0, hy0]
      simp [hx0, hy0]
    · simp [hx0]

@[simp] theorem specializeZero_C
    {S : Type*} [CommRing S] (i : σ) (c : S) :
    specializeZero i (C c : MvPolynomial σ S) = C c := by
  classical
  ext d
  rw [coeff_specializeZero]
  by_cases hd0 : d = 0
  · subst d
    simp
  · have hzero : (0 : σ →₀ ℕ) ≠ d := Ne.symm hd0
    simp [hzero]

theorem specializeZero_rename
    {S τ : Type*} [CommRing S]
    (f : σ → τ) (hf : Function.Injective f)
    (i : σ) (p : MvPolynomial σ S) :
    specializeZero (f i) (rename f p) = rename f (specializeZero i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      simp only [map_add, specializeZero_add, hp, hq]
  | mul_X p j hp =>
      rw [map_mul, specializeZero_mul, hp, specializeZero_mul, map_mul]
      simp only [MvPolynomial.X]
      rw [MvPolynomial.rename_monomial, specializeZero_monomial,
        specializeZero_monomial]
      by_cases hji : j = i
      · subst j
        simp
      · have hfji : f j ≠ f i := fun h => hji (hf h)
        have hmap :
            (Finsupp.mapDomain f (Finsupp.single j 1)) (f i) = 0 := by
          rw [Finsupp.mapDomain_apply hf]
          simp [hji]
        have hsingle : (Finsupp.single j 1) i = 0 := by simp [hji]
        rw [if_pos hmap, if_pos hsingle, MvPolynomial.rename_monomial,
          Finsupp.mapDomain_single]

theorem specializeZero_eq_self_of_notMem_vars
    {S : Type*} [CommRing S]
    (i : σ) (p : MvPolynomial σ S) (hi : i ∉ p.vars) :
    specializeZero i p = p := by
  ext d
  rw [coeff_specializeZero]
  by_cases hdi : d i = 0
  · simp [hdi]
  · have hcoeff : coeff d p = 0 := by
      by_cases hd : d ∈ p.support
      · exact (hdi (MvPolynomial.mem_support_notMem_vars_zero hd hi)).elim
      · exact notMem_support_iff.mp hd
    simp [hdi, hcoeff]

/-- Specializing a coordinate to zero does not increase the degree in any
coordinate. -/
theorem degreeOf_specializeZero_le
    {S σ : Type*} [CommRing S]
    (p : MvPolynomial σ S) (i j : σ) :
    (MvPolynomial.specializeZero i p).degreeOf j ≤ p.degreeOf j := by
  classical
  refine (MvPolynomial.degreeOf_sum_le j
    (p.support.filter fun d => d i = 0)
    fun d => MvPolynomial.monomial d (p.coeff d)).trans ?_
  apply Finset.sup_le
  intro d hd
  rw [Finset.mem_filter] at hd
  have hc : p.coeff d ≠ 0 := by
    simpa [Finsupp.mem_support_iff] using hd.1
  rw [MvPolynomial.degreeOf_monomial_eq _ j hc]
  exact MvPolynomial.degreeOf_le_iff.mp le_rfl d hd.1

namespace IsMultiaffine

variable {R σ τ : Type*} [CommSemiring R]

/-- Specializing one variable of a multiaffine polynomial at zero preserves
multiaffineness. -/
theorem specializeZero_preserves {S : Type*} [CommRing S]
    {p : MvPolynomial σ S} (hp : IsMultiaffine p) (i : σ) :
    IsMultiaffine (MvPolynomial.specializeZero i p) := by
  intro j
  exact (MvPolynomial.degreeOf_specializeZero_le p i j).trans (hp j)

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

namespace MvPolynomial

/-- Partial symmetrization by a permutation preserves multiaffineness. -/
theorem IsMultiaffine.partialSymmetrization
    {σ R : Type*} [CommRing R]
    {p : MvPolynomial σ R} (hp : IsMultiaffine p)
    (t : R) (e : Equiv.Perm σ) :
    IsMultiaffine (MvPolynomial.partialSymmetrization t e p) := by
  exact (hp.C_mul t).add
    ((hp.rename e.injective).C_mul (1 - t))

end MvPolynomial
