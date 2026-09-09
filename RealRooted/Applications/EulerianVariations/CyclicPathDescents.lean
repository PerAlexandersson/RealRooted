import RealRooted.NarayanaTransformation.Endpoints
import RealRooted.NarayanaTransformation.SimpleRoots

/-!
# Cyclic descents of northeast lattice paths

This file formalizes the cyclic-path family from Section `sec:cyclic` and
Theorem `thm:cyclicDescents` of
[arXiv:2609.07325](https://arxiv.org/abs/2609.07325). For `n ≥ 1`, its
coefficient of `X ^ k` is
`2 * choose n k * choose (n - 1) (k - 1)` for `1 ≤ k ≤ n`.

The proof is written independently from the historical OEIS implementation.
It identifies the family with a positive multiple of `X` times the derivative
of the type-B Narayana polynomial `narayanaPolynomial 0 n`.

The value at `n = 0` is a dummy zero polynomial used only to totalize the Lean
definition; it is not the enumerator of the unique empty path. The paper's
coefficient formula supplies the combinatorial identification, which is cited
rather than formalized here. Every paper-facing theorem below assumes `n > 0`.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted.Applications.EulerianVariations

/-- The cyclic-descent polynomial for northeast paths from `(0, 0)` to
`(n, n)`, in the coefficient form of the paper. -/
def cyclicPathDescentPolynomial (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.Icc 1 n,
    monomial k (2 * (Nat.choose n k : ℝ) * Nat.choose (n - 1) (k - 1))

@[simp] theorem coeff_cyclicPathDescentPolynomial (n k : ℕ) :
    (cyclicPathDescentPolynomial n).coeff k =
      if k ∈ Finset.Icc 1 n then
        2 * (Nat.choose n k : ℝ) * Nat.choose (n - 1) (k - 1)
      else 0 := by
  rw [cyclicPathDescentPolynomial, Polynomial.finsetSum_coeff]
  by_cases hk : k ∈ Finset.Icc 1 n
  · rw [if_pos hk, Finset.sum_eq_single k]
    · simp
    · intro b hb hbk
      simp [Polynomial.coeff_monomial, hbk]
    · exact fun h ↦ (h hk).elim
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro b hb
    have hbk : b ≠ k := by
      rintro rfl
      exact hk hb
    simp [Polynomial.coeff_monomial, hbk]

/-- The coefficient formula is `X` times the derivative of the type-B
Narayana polynomial, with the paper's normalization. -/
theorem cyclicPathDescentPolynomial_eq_derivative (n : ℕ) (hn : 0 < n) :
    cyclicPathDescentPolynomial n =
      C (2 / (n : ℝ)) * X * (narayanaPolynomial 0 n).derivative := by
  ext k
  cases k with
  | zero => simp
  | succ k =>
      by_cases hk : k + 1 ≤ n
      · have hchoose := Nat.choose_mul (n := n) (k := k + 1) (s := 1) (by lia)
        have hchooseReal := congrArg (fun x : ℕ ↦ (x : ℝ)) hchoose
        simp only [Nat.cast_mul] at hchooseReal
        rw [coeff_cyclicPathDescentPolynomial, if_pos (by simp [hk]),
          show C (2 / (n : ℝ)) * X * (narayanaPolynomial 0 n).derivative =
            C (2 / (n : ℝ)) * (X * (narayanaPolynomial 0 n).derivative) by ring,
          Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
          Polynomial.coeff_derivative,
          coeff_narayanaPolynomial_of_le hk]
        simp only [narayanaTransformCoeff, Nat.zero_add, Nat.choose_self,
          Nat.cast_one, div_one]
        field_simp
        norm_num at hchooseReal ⊢
        nlinarith
      · have hkn : n < k + 1 := Nat.lt_of_not_ge hk
        rw [coeff_cyclicPathDescentPolynomial,
          if_neg (by
            intro hmem
            rw [Finset.mem_Icc] at hmem
            exact hk hmem.2),
          show C (2 / (n : ℝ)) * X * (narayanaPolynomial 0 n).derivative =
            C (2 / (n : ℝ)) * (X * (narayanaPolynomial 0 n).derivative) by ring,
          Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
          Polynomial.coeff_derivative,
          coeff_narayanaPolynomial_of_lt hkn]
        simp

/-- The cyclic-path polynomial is a Pólya-frequency polynomial. -/
theorem cyclicPathDescentPolynomial_isPF (n : ℕ) (hn : 0 < n) :
    IsPFPolynomial (cyclicPathDescentPolynomial n) := by
  rw [cyclicPathDescentPolynomial_eq_derivative n hn]
  simpa [mul_assoc] using
    ((narayanaPolynomialRootLocation 0 n).derivative.X_mul.const_mul
      (by positivity : 0 < 2 / (n : ℝ)))

private theorem narayanaPolynomial_derivative_eval_zero_ne_zero
    (n : ℕ) (hn : 0 < n) :
    (narayanaPolynomial 0 n).derivative.eval 0 ≠ 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
    coeff_narayanaPolynomial_of_le (by lia : 1 ≤ n)]
  simp [narayanaTransformCoeff, hn.ne']

/-- The cyclic-path polynomial has degree `n` at every paper rank `n > 0`. -/
theorem natDegree_cyclicPathDescentPolynomial (n : ℕ) (hn : 0 < n) :
    (cyclicPathDescentPolynomial n).natDegree = n := by
  have hscale : 2 / (n : ℝ) ≠ 0 := by positivity
  have hder : (narayanaPolynomial 0 n).derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by
      rw [natDegree_narayanaPolynomial]
      lia)
  rw [cyclicPathDescentPolynomial_eq_derivative n hn,
    show C (2 / (n : ℝ)) * X * (narayanaPolynomial 0 n).derivative =
      C (2 / (n : ℝ)) * (X * (narayanaPolynomial 0 n).derivative) by ring,
    Polynomial.natDegree_C_mul hscale,
    Polynomial.natDegree_mul Polynomial.X_ne_zero hder,
    Polynomial.natDegree_X, Polynomial.natDegree_derivative,
    natDegree_narayanaPolynomial]
  lia

/-- The cyclic-path polynomial has no repeated real roots. -/
theorem cyclicPathDescentPolynomial_hasSimpleRoots (n : ℕ) (hn : 0 < n) :
    HasSimpleRoots (cyclicPathDescentPolynomial n) := by
  let q := (narayanaPolynomial 0 n).derivative
  have hqSimple : HasSimpleRoots q :=
    narayanaPolynomial_derivative_hasSimpleRoots 0 n hn
  have hq0 : ¬ q.IsRoot 0 := by
    exact narayanaPolynomial_derivative_eval_zero_ne_zero n hn
  have hscale : 2 / (n : ℝ) ≠ 0 := by positivity
  have hXq : X * q ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hqSimple.ne_zero
  have hpoly : C (2 / (n : ℝ)) * (X * q) ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hscale) hXq
  rw [cyclicPathDescentPolynomial_eq_derivative n hn,
    show C (2 / (n : ℝ)) * X * q = C (2 / (n : ℝ)) * (X * q) by ring]
  apply HasSimpleRoots.of_roots_nodup hpoly
  rw [Polynomial.roots_C_mul _ hscale, Polynomial.roots_mul hXq,
    Polynomial.roots_X]
  refine Multiset.nodup_add.mpr ⟨by simp, hqSimple.roots_nodup, ?_⟩
  rw [Multiset.singleton_disjoint]
  intro hzero
  exact hq0 ((Polynomial.mem_roots hqSimple.ne_zero).mp hzero)

/-- Paper theorem `thm:cyclicDescents`: after removing its simple zero at the
origin, the cyclic-path polynomial has exactly `n - 1` roots, all negative. -/
theorem cyclicPathDescentPolynomial_simple_root_description
    (n : ℕ) (hn : 0 < n) :
    HasSimpleRoots (cyclicPathDescentPolynomial n) ∧
      (cyclicPathDescentPolynomial n).IsRoot 0 ∧
      (∀ r ∈ (cyclicPathDescentPolynomial n).roots.erase 0, r < 0) ∧
      ((cyclicPathDescentPolynomial n).roots.erase 0).card = n - 1 := by
  have hsimple := cyclicPathDescentPolynomial_hasSimpleRoots n hn
  have hzero : (cyclicPathDescentPolynomial n).IsRoot 0 := by
    rw [cyclicPathDescentPolynomial_eq_derivative n hn, Polynomial.IsRoot.def]
    simp
  have hzeroMem : 0 ∈ (cyclicPathDescentPolynomial n).roots :=
    (Polynomial.mem_roots hsimple.ne_zero).mpr hzero
  have hpf := cyclicPathDescentPolynomial_isPF n hn
  have hsplits := (hpf.ne_zero_and_splits hsimple.ne_zero).2
  refine ⟨hsimple, hzero, ?_, ?_⟩
  · intro r hr
    have hrRoot : r ∈ (cyclicPathDescentPolynomial n).roots :=
      Multiset.mem_of_mem_erase hr
    have hrne : r ≠ 0 := by
      intro hre
      subst r
      exact hsimple.roots_nodup.notMem_erase hr
    exact lt_of_le_of_ne (hpf.roots_nonpos r hrRoot) hrne
  · rw [Multiset.card_erase_of_mem hzeroMem,
      card_roots_of_splits hsplits,
      natDegree_cyclicPathDescentPolynomial n hn]
    rfl

end RealRooted.Applications.EulerianVariations
