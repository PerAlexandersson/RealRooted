module

public import RealRooted.Interlacing.PencilPreserver
public import RealRooted.IteratedDerivativeShift
public import RealRooted.PFPolynomial.Closure

/-!
# Strict-to-weak closure for Pólya-frequency preservers

This module proves the finite-polynomial strict-to-weak transfer behind
Brändén, *Linear transformations preserving the Pólya frequency property*,
Corollary 3.5, arXiv:math/0403364.  Iterated nonnegative derivative shifts
approximate every Pólya-frequency polynomial by negative-simple polynomials,
so a linear map preserving the latter class preserves the former as well.
-/

@[expose] public section

open Polynomial Filter Topology

noncomputable section

namespace RealRooted

/-- A linear map carries coefficientwise-convergent, uniformly degree-bounded
polynomial sequences to coefficientwise-convergent sequences. -/
theorem tendsto_coeff_linearMap_apply_of_coeff_tendsto
    (T : ℝ[X] →ₗ[ℝ] ℝ[X])
    {p : ℕ → ℝ[X]} {p₀ : ℝ[X]} {d : ℕ}
    (hdeg : ∀ n, (p n).natDegree ≤ d)
    (hcoeff : ∀ i, Tendsto (fun n => (p n).coeff i) atTop
      (𝓝 (p₀.coeff i))) :
    ∀ j, Tendsto (fun n => (T (p n)).coeff j) atTop (𝓝 ((T p₀).coeff j)) := by
  have hdeg₀ : p₀.natDegree ≤ d := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have hzero : ∀ n, (p n).coeff i = 0 := by
      intro n
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (hdeg n) hi)
    exact tendsto_nhds_unique (hcoeff i) (by simp [hzero])
  have hexpand {q : ℝ[X]} (hq : q.natDegree ≤ d) :
      q = ∑ i ∈ Finset.range (d + 1), C (q.coeff i) * X ^ i := by
    exact q.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hq)
  have hterm (i j : ℕ) :
      Tendsto (fun n => (T (C ((p n).coeff i) * X ^ i)).coeff j) atTop
        (𝓝 ((T (C (p₀.coeff i) * X ^ i)).coeff j)) := by
    have hrewrite :
        (fun n => (T (C ((p n).coeff i) * X ^ i)).coeff j) =
          fun n => (p n).coeff i * (T (X ^ i)).coeff j := by
      funext n
      rw [← Polynomial.smul_eq_C_mul, T.map_smul]
      simp
    have hrewrite₀ :
        (T (C (p₀.coeff i) * X ^ i)).coeff j =
          p₀.coeff i * (T (X ^ i)).coeff j := by
      rw [← Polynomial.smul_eq_C_mul, T.map_smul]
      simp
    rw [hrewrite, hrewrite₀]
    exact (hcoeff i).mul_const _
  intro j
  have hsum :
      Tendsto
        (fun n => ∑ i ∈ Finset.range (d + 1),
          (T (C ((p n).coeff i) * X ^ i)).coeff j) atTop
        (𝓝 (∑ i ∈ Finset.range (d + 1),
          (T (C (p₀.coeff i) * X ^ i)).coeff j)) := by
    exact tendsto_finsetSum _ fun i _ => hterm i j
  rw [show (fun n => (T (p n)).coeff j) =
      fun n => ∑ i ∈ Finset.range (d + 1),
        (T (C ((p n).coeff i) * X ^ i)).coeff j by
    funext n
    calc
      (T (p n)).coeff j =
          (T (∑ i ∈ Finset.range (d + 1),
            C ((p n).coeff i) * X ^ i)).coeff j :=
        congrArg (fun r => (T r).coeff j) (hexpand (q := p n) (hdeg n))
      _ = ∑ i ∈ Finset.range (d + 1),
          (T (C ((p n).coeff i) * X ^ i)).coeff j := by
        rw [map_sum]
        let f : ℕ → ℝ[X] := fun i => T (C ((p n).coeff i) * X ^ i)
        exact Polynomial.finsetSum_coeff (Finset.range (d + 1)) f j]
  rw [show (T p₀).coeff j =
      ∑ i ∈ Finset.range (d + 1), (T (C (p₀.coeff i) * X ^ i)).coeff j by
    calc
      (T p₀).coeff j =
          (T (∑ i ∈ Finset.range (d + 1), C (p₀.coeff i) * X ^ i)).coeff j :=
        congrArg (fun r => (T r).coeff j) (hexpand (q := p₀) hdeg₀)
      _ = ∑ i ∈ Finset.range (d + 1),
          (T (C (p₀.coeff i) * X ^ i)).coeff j := by
        rw [map_sum]
        let f : ℕ → ℝ[X] := fun i => T (C (p₀.coeff i) * X ^ i)
        exact Polynomial.finsetSum_coeff (Finset.range (d + 1)) f j]
  exact hsum

/-- A negative-simple polynomial is Pólya-frequency. -/
theorem IsNegativeSimple.isPFPolynomial {p : ℝ[X]}
    (hp : IsNegativeSimple p) : IsPFPolynomial p := by
  have hnn : HasNonnegCoeffs p :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hp.2.1).2
      ⟨hp.2.2.2.1, fun r hr => (hp.2.2.2.2 r hr).le⟩).1
  exact IsPFPolynomial.of_realRooted_nonneg hnn hp.2.1

/-- A linear map preserving negative-simple polynomials through a fixed degree
also preserves Pólya-frequency polynomials through that degree. -/
theorem isPFPolynomial_map_of_isNegativeSimple_of_natDegree_le
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {d : ℕ}
    (hT : ∀ {q : ℝ[X]}, IsNegativeSimple q ->
      q.natDegree ≤ d -> IsPFPolynomial (T q))
    {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hpdeg : p.natDegree ≤ d) :
    IsPFPolynomial (T p) := by
  by_cases hp₀ : p = 0
  · simpa [hp₀] using IsPFPolynomial.zero
  have hp_splits : p.Splits := hp.ne_zero_and_splits hp₀ |>.2
  let n : ℕ := p.natDegree
  let eps : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  let q : ℕ → ℝ[X] := fun k => iterateTDeriv (-(eps k)) n p
  have heps_pos (n : ℕ) : 0 < eps n := by
    dsimp [eps]
    positivity
  have hq_negative (n : ℕ) : IsNegativeSimple (q n) := by
    have hq_nonneg : HasNonnegCoeffs (q n) := by
      dsimp [q]
      exact hp.hasNonnegCoeffs.iterateTDeriv_neg (heps_pos n).le _
    have hq_ne : q n ≠ 0 := by
      dsimp [q]
      exact iterateTDeriv_ne_zero hp₀
    have hq_splits : (q n).Splits := by
      dsimp [q]
      exact splits_iterateTDeriv_all hp_splits _
    have hq_simple : HasSimpleRoots (q n) := by
      dsimp [q]
      exact hasSimpleRoots_iterateTDeriv_neg_of_natDegree_le
        (heps_pos n) hp₀ hp_splits le_rfl
    have hq_pos : HasPosLeadingCoeff (q n) := by
      dsimp [q]
      exact hasPosLeadingCoeff_iterateTDeriv.mpr
        (hp.hasNonnegCoeffs.pos_leadingCoeff hp₀)
    have hq_coeff_zero : 0 < (q n).coeff 0 := by
      dsimp [q]
      exact coeff_zero_iterateTDeriv_neg_pos_of_natDegree_le
        (heps_pos n) hp.hasNonnegCoeffs hp₀ le_rfl
    refine ⟨hq_ne, hq_splits, hq_simple, hq_pos, ?_⟩
    intro r hr
    have hr_nonpos : r ≤ 0 := roots_nonpos_of_hasNonnegCoeffs hq_nonneg r hr
    have hr_ne : r ≠ 0 := by
      intro hr_zero
      have hr_root : (q n).IsRoot 0 := by
        rw [← hr_zero]
        exact isRoot_of_mem_roots hr
      have hcoeff_zero : (q n).coeff 0 = 0 := by
        simpa [Polynomial.IsRoot.def, Polynomial.coeff_zero_eq_eval_zero] using hr_root
      linarith
    exact lt_of_le_of_ne hr_nonpos hr_ne
  have hq_degree : ∀ n, (q n).natDegree ≤ d := by
    intro n
    simpa [q] using hpdeg
  have hneg_eps : Tendsto (fun n => -(eps n)) atTop (𝓝 0) := by
    have heps : Tendsto eps atTop (𝓝 0) := by
      simpa [eps, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using heps.neg
  have hq_coeff : ∀ i, Tendsto (fun n => (q n).coeff i) atTop
      (𝓝 (p.coeff i)) := by
    intro i
    dsimp [q]
    simpa [Function.comp_def, iterateTDeriv_zero_eps] using
      (continuousAt_coeff_iterateTDeriv_zero n p i).tendsto.comp hneg_eps
  apply IsPFPolynomial.of_coeff_tendsto (fun n => hT (hq_negative n) (hq_degree n))
  exact tendsto_coeff_linearMap_apply_of_coeff_tendsto T hq_degree hq_coeff

/-- A linear operator preserving every negative-simple polynomial preserves
every Pólya-frequency polynomial. -/
theorem isPFPolynomial_map_of_isNegativeSimple
    (T : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hT : ∀ {q : ℝ[X]}, IsNegativeSimple q → IsPFPolynomial (T q)) {p : ℝ[X]}
    (hp : IsPFPolynomial p) : IsPFPolynomial (T p) :=
  isPFPolynomial_map_of_isNegativeSimple_of_natDegree_le T
    (fun hq _ => hT hq) hp le_rfl

end RealRooted
