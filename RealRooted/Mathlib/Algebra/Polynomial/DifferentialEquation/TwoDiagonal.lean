/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Two-diagonal coefficient systems

We solve `a k * c (k+1) = b k * c k` by descending substitution, dividing only
by the nonzero diagonal entries. The admissible degrees describe all solutions,
including arbitrary zero patterns and empty intervals.
Source: unpublished proof notes, RealRooted issue #2345, Proposition 1 and its
arbitrary-zero extension.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- Polynomial solutions of a two-diagonal coefficient system. A polynomial
encodes a finitely supported coefficient vector, with a zero boundary at infinity. -/
@[expose] def twoDiagonalSolutions (a b : ℕ → K) : Submodule K K[X] where
  carrier := {p | ∀ k, a k * p.coeff (k + 1) = b k * p.coeff k}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq k
    simp only [coeff_add]
    linear_combination hp k + hq k
  smul_mem' := by
    intro c p hp k
    simp only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    linear_combination c * hp k

/-- An index supports a solution precisely when it is a zero of the diagonal
and every preceding zero is separated from it by a zero interval product. -/
@[expose] def TwoDiagonalDegree (a b : ℕ → K) (n : ℕ) : Prop :=
  b n = 0 ∧ ∀ k < n, b k = 0 → ∏ j ∈ Finset.Ico k n, a j = 0

/-- Telescoping the coefficient equations over an interval requires no division. -/
theorem prod_mul_coeff_eq_prod_mul_coeff {a b : ℕ → K} {p : K[X]}
    (hp : p ∈ twoDiagonalSolutions a b) {k n : ℕ} (hkn : k ≤ n) :
    (∏ j ∈ Finset.Ico k n, a j) * p.coeff n =
      (∏ j ∈ Finset.Ico k n, b j) * p.coeff k := by
  induction n, hkn using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
      rw [Finset.prod_Ico_succ_top hkn, Finset.prod_Ico_succ_top hkn]
      calc
        _ = (∏ j ∈ Finset.Ico k n, a j) * (b n * p.coeff n) := by
          rw [mul_assoc, hp n]
        _ = b n * ((∏ j ∈ Finset.Ico k n, a j) * p.coeff n) := by ring
        _ = _ := by rw [ih]; ring

/-- Every nonzero solution has an admissible degree. -/
theorem twoDiagonalDegree_natDegree {a b : ℕ → K} {p : K[X]}
    (hp : p ∈ twoDiagonalSolutions a b) (hne : p ≠ 0) :
    TwoDiagonalDegree a b p.natDegree := by
  have hlc := leadingCoeff_ne_zero.mpr hne
  constructor
  · have h := hp p.natDegree
    rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), mul_zero,
      coeff_natDegree] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hlc
  · intro k hkn hbk
    have h := prod_mul_coeff_eq_prod_mul_coeff hp hkn.le
    have hz : ∏ j ∈ Finset.Ico k p.natDegree, b j = 0 :=
      Finset.prod_eq_zero (Finset.mem_Ico.mpr ⟨le_rfl, hkn⟩) hbk
    rw [hz, zero_mul, coeff_natDegree] at h
    exact (mul_eq_zero.mp h).resolve_right hlc

open Classical in
/-- The canonical monic solution candidate with degree `n`. Its coefficients at
all other zeros of `b` vanish. Division by zero truncates a descending block. -/
@[expose] noncomputable def twoDiagonalPolynomial (a b : ℕ → K) (n : ℕ) : K[X] :=
  ∑ k ∈ Finset.range (n + 1), monomial k (∏ j ∈ Finset.Ico k n, a j / b j)

/-- Coefficients of the descending solution candidate. -/
theorem coeff_twoDiagonalPolynomial (a b : ℕ → K) (n k : ℕ) :
    (twoDiagonalPolynomial a b n).coeff k =
      if k ≤ n then ∏ j ∈ Finset.Ico k n, a j / b j else 0 := by
  classical
  rw [twoDiagonalPolynomial, finsetSum_coeff]
  simp only [coeff_monomial, Finsupp.single_apply]
  simp [Finset.sum_ite_eq']

/-- The canonical candidate has top coefficient one. -/
@[simp] theorem coeff_twoDiagonalPolynomial_self (a b : ℕ → K) (n : ℕ) :
    (twoDiagonalPolynomial a b n).coeff n = 1 := by
  simp [coeff_twoDiagonalPolynomial]

/-- The canonical candidate has exactly the prescribed degree. -/
@[simp] theorem natDegree_twoDiagonalPolynomial (a b : ℕ → K) (n : ℕ) :
    (twoDiagonalPolynomial a b n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    simp [coeff_twoDiagonalPolynomial, not_le.mpr hk]
  · simp

/-- Coefficients at diagonal zeros give Kronecker coordinates for the candidates. -/
theorem coeff_twoDiagonalPolynomial_of_eq_zero (a b : ℕ → K) (n k : ℕ)
    (hk : b k = 0) :
    (twoDiagonalPolynomial a b n).coeff k = if k = n then 1 else 0 := by
  classical
  by_cases heq : k = n
  · subst k
    simp
  by_cases hkn : k ≤ n
  · rw [coeff_twoDiagonalPolynomial, ite_eq_left hkn, ite_eq_right heq]
    exact Finset.prod_eq_zero (Finset.mem_Ico.mpr ⟨le_rfl, by lia⟩) (by simp [hk])
  · simp [coeff_twoDiagonalPolynomial, hkn, heq]

/-- Every admissible degree has a canonical monic solution. -/
theorem twoDiagonalPolynomial_mem {a b : ℕ → K} {n : ℕ}
    (hn : TwoDiagonalDegree a b n) :
    twoDiagonalPolynomial a b n ∈ twoDiagonalSolutions a b := by
  intro k
  by_cases hkn : k < n
  · rw [coeff_twoDiagonalPolynomial, coeff_twoDiagonalPolynomial,
      ite_eq_left (by lia : k + 1 ≤ n), ite_eq_left hkn.le]
    rw [Finset.prod_eq_prod_Ico_succ_bot hkn]
    by_cases hb : b k = 0
    · have hz := hn.2 k hkn hb
      have hprod : a k * (∏ j ∈ Finset.Ico (k + 1) n, a j / b j) = 0 := by
        rw [Finset.prod_div_distrib, ← mul_div_assoc, ←
          Finset.prod_eq_prod_Ico_succ_bot hkn, hz, zero_div]
      simpa [hb] using hprod
    · field_simp
  · by_cases heq : k = n
    · subst k
      simp [coeff_twoDiagonalPolynomial, hn.1]
    · simp [coeff_twoDiagonalPolynomial, show ¬ k ≤ n by lia,
        show ¬ k + 1 ≤ n by lia]

/-- Possible nonzero degrees of a two-diagonal system, with no restrictions on
its diagonal zero pattern. -/
theorem exists_twoDiagonalSolution_natDegree_iff (a b : ℕ → K) (n : ℕ) :
    (∃ p ∈ twoDiagonalSolutions a b, p ≠ 0 ∧ p.natDegree = n) ↔
      TwoDiagonalDegree a b n := by
  constructor
  · rintro ⟨p, hp, hne, rfl⟩
    exact twoDiagonalDegree_natDegree hp hne
  · intro hn
    refine ⟨twoDiagonalPolynomial a b n, twoDiagonalPolynomial_mem hn, ?_, by simp⟩
    intro hz
    have := congrArg (fun p : K[X] => p.coeff n) hz
    simp at this

/-- Coefficients at all admissible degrees determine a solution uniquely. -/
theorem eq_of_mem_twoDiagonalSolutions_of_coeff_eq {a b : ℕ → K}
    {p q : K[X]} (hp : p ∈ twoDiagonalSolutions a b)
    (hq : q ∈ twoDiagonalSolutions a b)
    (hc : ∀ n, TwoDiagonalDegree a b n → p.coeff n = q.coeff n) : p = q := by
  by_contra hne
  have hr : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hmem := (twoDiagonalSolutions a b).sub_mem hp hq
  have hn := twoDiagonalDegree_natDegree hmem hr
  exact (leadingCoeff_ne_zero.mpr hr) (by
    rw [leadingCoeff, coeff_sub, hc _ hn, sub_self])

open Classical in
/-- The admissible indices in a finite set of diagonal zeros. -/
@[expose] noncomputable def twoDiagonalDegrees (a b : ℕ → K) (E : Finset ℕ) : Finset ℕ :=
  E.filter (TwoDiagonalDegree a b)

/-- Exact free coordinates for an arbitrary finite zero pattern. This is the
finite coefficient-system theorem, including the no-zero and one-zero cases. -/
@[expose] noncomputable def twoDiagonalEquiv (a b : ℕ → K) (E : Finset ℕ)
    (hE : ∀ n, b n = 0 → n ∈ E) :
    twoDiagonalSolutions a b ≃ₗ[K] (twoDiagonalDegrees a b E → K) := by
  classical
  exact {
    toFun p n := (p : K[X]).coeff n
    invFun c := ⟨∑ n : twoDiagonalDegrees a b E, c n • twoDiagonalPolynomial a b n,
      (twoDiagonalSolutions a b).sum_mem fun n _ =>
        (twoDiagonalSolutions a b).smul_mem _
          (twoDiagonalPolynomial_mem (Finset.mem_filter.mp n.property).2)⟩
    left_inv p := by
      classical
      apply Subtype.ext
      apply eq_of_mem_twoDiagonalSolutions_of_coeff_eq
      · exact (twoDiagonalSolutions a b).sum_mem fun n _ =>
          (twoDiagonalSolutions a b).smul_mem _
            (twoDiagonalPolynomial_mem (Finset.mem_filter.mp n.property).2)
      · exact p.property
      · intro k hk
        have hkE : k ∈ twoDiagonalDegrees a b E := Finset.mem_filter.mpr ⟨hE k hk.1, hk⟩
        simp only [finsetSum_coeff, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul,
          coeff_twoDiagonalPolynomial_of_eq_zero _ _ _ _ hk.1]
        rw [Finset.sum_eq_single ⟨k, hkE⟩]
        · simp
        · intro j _ hj
          have hjk : k ≠ (j : ℕ) := by
            intro heq
            apply hj
            exact Subtype.ext heq.symm
          simp [hjk]
        · simp
    right_inv c := by
      classical
      ext k
      simp only [finsetSum_coeff, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul,
        coeff_twoDiagonalPolynomial_of_eq_zero _ _ _ _
          (Finset.mem_filter.mp k.property).2.1]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hj
        have hjk : (k : ℕ) ≠ (j : ℕ) := by
          intro heq
          exact hj (Subtype.ext heq.symm)
        simp [hjk]
      · simp
    map_add' p q := by ext n; simp
    map_smul' c p := by ext n; simp }

/-- The dimension is exactly the number of admissible degrees. -/
theorem finrank_twoDiagonalSolutions (a b : ℕ → K) (E : Finset ℕ)
    (hE : ∀ n, b n = 0 → n ∈ E) :
    Module.finrank K (twoDiagonalSolutions a b) = (twoDiagonalDegrees a b E).card := by
  simpa using (twoDiagonalEquiv a b E hE).finrank_eq

/-- A basis with one canonical monic polynomial for every admissible degree. -/
noncomputable def twoDiagonalBasis (a b : ℕ → K) (E : Finset ℕ)
    (hE : ∀ n, b n = 0 → n ∈ E) :
    Module.Basis (twoDiagonalDegrees a b E) K (twoDiagonalSolutions a b) :=
  (Pi.basisFun K (twoDiagonalDegrees a b E)).map (twoDiagonalEquiv a b E hE).symm

/-- With a single diagonal zero, exactly that degree is admissible. -/
theorem twoDiagonalDegree_iff_of_one_zero {a b : ℕ → K} {u n : ℕ}
    (hb : ∀ k, b k = 0 ↔ k = u) : TwoDiagonalDegree a b n ↔ n = u := by
  constructor
  · intro hn
    exact (hb n).mp hn.1
  · intro hn
    subst n
    refine ⟨(hb u).mpr rfl, ?_⟩
    intro k hku hk
    have := (hb k).mp hk
    lia

/-- Two diagonal zeros give exactly the interval-product obstruction. -/
theorem twoDiagonalDegree_iff_of_two_zeros {a b : ℕ → K} {ℓ u n : ℕ}
    (hℓu : ℓ < u) (hb : ∀ k, b k = 0 ↔ k = ℓ ∨ k = u) :
    TwoDiagonalDegree a b n ↔ n = ℓ ∨ n = u ∧ ∏ k ∈ Finset.Ico ℓ u, a k = 0 := by
  constructor
  · intro hn
    rcases (hb n).mp hn.1 with h | h
    · exact Or.inl h
    · subst n
      exact Or.inr ⟨rfl, hn.2 ℓ hℓu ((hb ℓ).mpr (Or.inl rfl))⟩
  · rintro (h | ⟨h, hprod⟩)
    · subst n
      refine ⟨(hb ℓ).mpr (Or.inl rfl), ?_⟩
      intro k hk hbk
      rcases (hb k).mp hbk with h | h <;> lia
    · subst n
      refine ⟨(hb u).mpr (Or.inr rfl), ?_⟩
      intro k hk hbk
      rcases (hb k).mp hbk with rfl | rfl
      · exact hprod
      · lia

open Classical in
/-- The two-zero dimension dichotomy, without assumptions on the upper diagonal. -/
theorem finrank_twoDiagonalSolutions_of_two_zeros {a b : ℕ → K} {ℓ u : ℕ}
    (hℓu : ℓ < u) (hb : ∀ k, b k = 0 ↔ k = ℓ ∨ k = u) :
    Module.finrank K (twoDiagonalSolutions a b) =
      if ∏ k ∈ Finset.Ico ℓ u, a k = 0 then 2 else 1 := by
  classical
  rw [finrank_twoDiagonalSolutions a b {ℓ, u}
    (fun k hk => by simpa using (hb k).mp hk)]
  have hne : ℓ ≠ u := hℓu.ne
  by_cases hprod : ∏ k ∈ Finset.Ico ℓ u, a k = 0
  · have hset : twoDiagonalDegrees a b {ℓ, u} = {ℓ, u} := by
      ext k
      simp [twoDiagonalDegrees, twoDiagonalDegree_iff_of_two_zeros hℓu hb, hprod]
    simp [hset, hprod, hne]
  · have hset : twoDiagonalDegrees a b {ℓ, u} = {ℓ} := by
      ext k
      simp only [twoDiagonalDegrees, Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton, twoDiagonalDegree_iff_of_two_zeros hℓu hb, hprod]
      tauto
    simp [hset, hprod]

/-- A system with exactly one diagonal zero has dimension one. -/
theorem finrank_twoDiagonalSolutions_of_one_zero {a b : ℕ → K} {u : ℕ}
    (hb : ∀ k, b k = 0 ↔ k = u) :
    Module.finrank K (twoDiagonalSolutions a b) = 1 := by
  classical
  rw [finrank_twoDiagonalSolutions a b {u} (fun k hk => by simp [(hb k).mp hk])]
  have hset : twoDiagonalDegrees a b {u} = {u} := by
    ext k
    simp [twoDiagonalDegrees, twoDiagonalDegree_iff_of_one_zero hb]
  simp [hset]

/-- The basis vectors are the canonical monic descending polynomials. -/
theorem coe_twoDiagonalBasis (a b : ℕ → K) (E : Finset ℕ)
    (hE : ∀ n, b n = 0 → n ∈ E) (i : twoDiagonalDegrees a b E) :
    (twoDiagonalBasis a b E hE i : K[X]) = twoDiagonalPolynomial a b i := by
  classical
  have h : twoDiagonalBasis a b E hE i =
      ⟨twoDiagonalPolynomial a b i,
        twoDiagonalPolynomial_mem (Finset.mem_filter.mp i.property).2⟩ := by
    apply (twoDiagonalEquiv a b E hE).injective
    ext j
    change (twoDiagonalEquiv a b E hE)
      ((twoDiagonalEquiv a b E hE).symm (Pi.basisFun K _ i)) j = _
    rw [LinearEquiv.apply_symm_apply]
    change Pi.basisFun K _ i j = (twoDiagonalPolynomial a b i).coeff j
    rw [coeff_twoDiagonalPolynomial_of_eq_zero _ _ _ _
      (Finset.mem_filter.mp j.property).2.1]
    simp [Pi.basisFun_apply, Pi.single_apply]
  exact congrArg Subtype.val h

/-- Checking the nearest preceding diagonal zero suffices for admissibility. -/
theorem twoDiagonalDegree_iff_of_previous_zero {a b : ℕ → K} {ℓ n : ℕ}
    (hℓn : ℓ < n) (hℓ : b ℓ = 0) (hn : b n = 0)
    (hprev : ∀ k < n, b k = 0 → k ≤ ℓ) :
    TwoDiagonalDegree a b n ↔ ∏ k ∈ Finset.Ico ℓ n, a k = 0 := by
  constructor
  · intro h
    exact h.2 ℓ hℓn hℓ
  · intro hprod
    refine ⟨hn, ?_⟩
    intro k hkn hk
    rw [← Finset.prod_Ico_consecutive a (hprev k hkn hk) hℓn.le, hprod, mul_zero]

/-- Each canonical solution candidate is monic. -/
theorem monic_twoDiagonalPolynomial (a b : ℕ → K) (n : ℕ) :
    (twoDiagonalPolynomial a b n).Monic := by
  simp [Monic, leadingCoeff]

open Classical in
/-- A finite system with the zero upper boundary is exactly the polynomial
system obtained by setting the unused diagonal entries to one. Thus the general
coordinate and dimension theorems apply to finite coefficient vectors verbatim. -/
theorem mem_twoDiagonalSolutions_truncate_iff (a b : ℕ → K) (u : ℕ) (p : K[X]) :
    p ∈ twoDiagonalSolutions a (fun k => if k ≤ u then b k else 1) ↔
      p.natDegree ≤ u ∧ ∀ k ≤ u, a k * p.coeff (k + 1) = b k * p.coeff k := by
  constructor
  · intro hp
    refine ⟨?_, ?_⟩
    · by_cases hz : p = 0
      · simp [hz]
      · have h := (twoDiagonalDegree_natDegree hp hz).1
        by_contra hle
        simp [hle] at h
    · intro k hk
      simpa only [ite_eq_left hk] using hp k
  · rintro ⟨hdeg, hp⟩ k
    by_cases hk : k ≤ u
    · simpa only [ite_eq_left hk] using hp k hk
    · rw [coeff_eq_zero_of_natDegree_lt (by lia : p.natDegree < k + 1),
        coeff_eq_zero_of_natDegree_lt (by lia : p.natDegree < k)]
      simp

/-- Exact compatibility for the two prescribed coordinates. In the
nonvanishing-product case the upper coordinate is zero; otherwise both are free. -/
theorem exists_twoDiagonalSolution_coeff_eq_iff {a b : ℕ → K} {ℓ u : ℕ}
    (hℓu : ℓ < u) (hb : ∀ k, b k = 0 ↔ k = ℓ ∨ k = u) (c d : K) :
    (∃ p ∈ twoDiagonalSolutions a b, p.coeff ℓ = c ∧ p.coeff u = d) ↔
      d * ∏ k ∈ Finset.Ico ℓ u, a k = 0 := by
  have hℓ : b ℓ = 0 := (hb ℓ).mpr (Or.inl rfl)
  have hu : b u = 0 := (hb u).mpr (Or.inr rfl)
  constructor
  · rintro ⟨p, hp, _, hpu⟩
    have h := prod_mul_coeff_eq_prod_mul_coeff hp hℓu.le
    have hz : ∏ k ∈ Finset.Ico ℓ u, b k = 0 :=
      Finset.prod_eq_zero (Finset.mem_Ico.mpr ⟨le_rfl, hℓu⟩) hℓ
    rw [hz, zero_mul, hpu, mul_comm] at h
    exact h
  · intro hcd
    have hlow : twoDiagonalPolynomial a b ℓ ∈ twoDiagonalSolutions a b :=
      twoDiagonalPolynomial_mem
        ((twoDiagonalDegree_iff_of_two_zeros hℓu hb).mpr (Or.inl rfl))
    have hhigh : d • twoDiagonalPolynomial a b u ∈ twoDiagonalSolutions a b := by
      rcases mul_eq_zero.mp hcd with hd | hprod
      · simp [hd]
      · exact (twoDiagonalSolutions a b).smul_mem _ (twoDiagonalPolynomial_mem
          ((twoDiagonalDegree_iff_of_two_zeros hℓu hb).mpr (Or.inr ⟨rfl, hprod⟩)))
    refine ⟨c • twoDiagonalPolynomial a b ℓ + d • twoDiagonalPolynomial a b u,
      (twoDiagonalSolutions a b).add_mem
        ((twoDiagonalSolutions a b).smul_mem _ hlow) hhigh, ?_, ?_⟩
    · simp [coeff_twoDiagonalPolynomial_of_eq_zero _ _ _ _ hℓ, hℓu.ne]
    · simp [coeff_twoDiagonalPolynomial_of_eq_zero _ _ _ _ hu, hℓu.ne']

end Polynomial
