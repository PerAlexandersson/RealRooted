import RealRooted.SeparablePermutations.Enumerator
import RealRooted.FactorialCompression.DegreeChanging
import RealRooted.GammaTransform.StrictLifting

/-!
# Strict interlacing for the descent polynomials of separable permutations

Zhang (SSRN 7510941) proves that the gamma-polynomials `Γ_n` of the descent enumerators of the
separable permutations strictly interlace, and that the strict interlacing lifts to the descent
polynomials `S_n = (1 + t) ^ (n - 1) Γ_n (t / (1 + t) ^ 2)`.  We prove both statements for the
algebraically defined families `gammaPolynomial` and `descentPolynomial` of
`RealRooted/SeparablePermutations/Gamma.lean`:

* `strictInterl_gammaPolynomial`: for `n ≥ 2`, `Γ_n` and `Γ_{n+1}` strictly interlace and have no
  common root.  The case `n = 2` is the explicit pair `1`, `1 + 2 X`; for `n ≥ 3` the pair is a
  scalar multiple of the pair of `compression_one_nextPolynomial_strictInterl` for the
  auxiliary polynomial `B_{n-2}`.
* `strictInterl_descentPolynomial`: for `n ≥ 2`, `S_n` and `S_{n+1}` have simple negative roots,
  strictly interlace and have no common root; this is the strict lifting
  `strictInterl_gammaTransform_succ_of_strictInterl_of_no_common` applied to `Γ_n`, `Γ_{n+1}`.
* `strictInterl_descentEnumerator_of_eq_descentPolynomial`: the conditional transfer to the
  descent enumerators of the separable permutations.  The identification
  `descentEnumerator n = descentPolynomial (n + 1)` is a documented hypothesis (checked for
  `n ≤ 3`, that is, permutations of at most four letters, in `Enumerator.lean`); it combines the
  results of Fu--Lin--Zeng with Zhang's Proposition 3.3 and is not formalized here.
-/

open Polynomial

noncomputable section

namespace RealRooted.SeparablePermutations

open FactorialCompression

/-! ### The gamma-polynomials -/

private theorem gammaPolynomial_ne_zero {n : ℕ} (hn : 1 ≤ n) : gammaPolynomial n ≠ 0 := by
  intro h
  have := coeff_zero_gammaPolynomial_pos hn
  rw [h] at this
  simp at this

/-- All roots of `Γ_n` are negative for `n ≥ 1`. -/
theorem roots_gammaPolynomial_neg {n : ℕ} (hn : 1 ≤ n) :
    ∀ r ∈ (gammaPolynomial n).roots, r < 0 := by
  intro r hr
  refine lt_of_le_of_ne
    (RealRooted.roots_nonpos_of_hasNonnegCoeffs (hasNonnegCoeffs_gammaPolynomial n) r hr) ?_
  rintro rfl
  have h0 := (coeff_zero_gammaPolynomial_pos hn).ne'
  exact h0 (by rw [coeff_zero_eq_eval_zero]; exact isRoot_of_mem_roots hr)

/-- The strict interlacing of `Γ_{N+2}` and `Γ_{N+3}` for `N ≠ 0`. -/
private theorem strictInterl_gammaPolynomial_add_two {N : ℕ} (hN : N ≠ 0) :
    RealRooted.StrictInterl (gammaPolynomial (N + 2)) (gammaPolynomial (N + 3)) ∧
      ∀ r : ℝ, ¬ ((gammaPolynomial (N + 2)).IsRoot r ∧ (gammaPolynomial (N + 3)).IsRoot r) := by
  have hB := strictInterl_auxPolynomial N
  obtain ⟨-, -, -, -, -, -, -, -, hint, hno⟩ :=
    compression_one_nextPolynomial_strictInterl hN (natDegree_auxPolynomial N) hB.1.1.2
      (hasPosLeadingCoeff_auxPolynomial N) (roots_auxPolynomial_neg N)
  have hc : ∀ M : ℕ, (2 : ℝ) ^ M / (M.factorial : ℝ) ≠ 0 := fun M => by positivity
  have hnext : auxPolynomial (N + 1) =
      nextPolynomial (((N : ℝ) + 2) / 2) (auxPolynomial N) := rfl
  rw [← hnext] at hint hno
  rw [show N + 3 = (N + 1) + 2 by lia, gammaPolynomial_add_two, gammaPolynomial_add_two]
  refine ⟨(hint.C_mul_left (hc N)).C_mul_right (hc (N + 1)), ?_⟩
  rintro r ⟨h1, h2⟩
  rw [IsRoot, eval_mul, eval_C, mul_eq_zero] at h1 h2
  exact hno r (h1.resolve_left (hc N)) (h2.resolve_left (hc (N + 1)))

/-- Consecutive gamma-polynomials `Γ_n`, `Γ_{n+1}` (`n ≥ 2`) strictly interlace and have no
common root (Zhang, SSRN 7510941). -/
theorem strictInterl_gammaPolynomial {n : ℕ} (hn : 2 ≤ n) :
    RealRooted.StrictInterl (gammaPolynomial n) (gammaPolynomial (n + 1)) ∧
      ∀ r : ℝ, ¬ ((gammaPolynomial n).IsRoot r ∧ (gammaPolynomial (n + 1)).IsRoot r) := by
  by_cases h2 : n = 2
  · subst h2
    rw [gammaPolynomial_two, show (2 + 1 : ℕ) = 3 from rfl, gammaPolynomial_three]
    have hdeg : (1 + 2 * X : ℝ[X]).natDegree = 1 := by
      compute_degree!
    refine ⟨(RealRooted.interlaces_one_linear hdeg).toStrictInterl, ?_⟩
    rintro r ⟨h1, -⟩
    simp at h1
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by lia⟩
    exact strictInterl_gammaPolynomial_add_two (N := N) (by lia)

/-- The gamma-polynomials `Γ_n` have simple roots for `n ≥ 2`. -/
theorem hasSimpleRoots_gammaPolynomial {n : ℕ} (hn : 2 ≤ n) :
    RealRooted.HasSimpleRoots (gammaPolynomial n) :=
  ((strictInterl_gammaPolynomial hn).1.hasSimpleRoots_of_no_common_root
    fun r hr => (strictInterl_gammaPolynomial hn).2 r hr).1

/-! ### The descent polynomials -/

/-- The strict lifting statement for `S_n`, `S_{n+1}` with `n ≥ 2`, with all its conclusions. -/
private theorem lifting_descentPolynomial {n : ℕ} (hn : 2 ≤ n) :
    (descentPolynomial n).natDegree = n - 1 ∧ (descentPolynomial (n + 1)).natDegree = n ∧
    RealRooted.HasSimpleRoots (descentPolynomial n) ∧
    RealRooted.HasSimpleRoots (descentPolynomial (n + 1)) ∧
    (∀ r ∈ (descentPolynomial n).roots, r < 0) ∧
    (∀ r ∈ (descentPolynomial (n + 1)).roots, r < 0) ∧
    RealRooted.StrictInterl (descentPolynomial n) (descentPolynomial (n + 1)) ∧
    ∀ r : ℝ, ¬ ((descentPolynomial n).IsRoot r ∧ (descentPolynomial (n + 1)).IsRoot r) := by
  have h := RealRooted.strictInterl_gammaTransform_succ_of_strictInterl_of_no_common hn
    (A := gammaPolynomial n) (B := gammaPolynomial (n + 1))
    (by rw [natDegree_gammaPolynomial hn])
    (by rw [natDegree_gammaPolynomial (by lia)]; rfl)
    (hasPosLeadingCoeff_gammaPolynomial hn) (hasPosLeadingCoeff_gammaPolynomial (by lia))
    (roots_gammaPolynomial_neg (by lia)) (roots_gammaPolynomial_neg (by lia))
    (strictInterl_gammaPolynomial hn).1 (strictInterl_gammaPolynomial hn).2
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    fun r hr => h.2.2.2.2.2.2.2 r hr.1 hr.2⟩

/-- The descent polynomials `S_n` have simple roots for `n ≥ 2`. -/
theorem hasSimpleRoots_descentPolynomial {n : ℕ} (hn : 2 ≤ n) :
    RealRooted.HasSimpleRoots (descentPolynomial n) :=
  (lifting_descentPolynomial hn).2.2.1

/-- All roots of `S_n` are negative for `n ≥ 2`. -/
theorem roots_descentPolynomial_neg {n : ℕ} (hn : 2 ≤ n) :
    ∀ r ∈ (descentPolynomial n).roots, r < 0 :=
  (lifting_descentPolynomial hn).2.2.2.2.1

/-- Consecutive descent polynomials `S_n`, `S_{n+1}` (`n ≥ 2`) strictly interlace and have no
common root.  This is the strict lifting of the interlacing of `Γ_n`, `Γ_{n+1}`
(Zhang, SSRN 7510941, Section 4). -/
theorem strictInterl_descentPolynomial {n : ℕ} (hn : 2 ≤ n) :
    RealRooted.StrictInterl (descentPolynomial n) (descentPolynomial (n + 1)) ∧
      ∀ r : ℝ, ¬ ((descentPolynomial n).IsRoot r ∧ (descentPolynomial (n + 1)).IsRoot r) :=
  ⟨(lifting_descentPolynomial hn).2.2.2.2.2.2.1, (lifting_descentPolynomial hn).2.2.2.2.2.2.2⟩

/-! ### Conditional transfer to the separable permutations -/

/-- If the descent enumerator of the separable permutations is `descentPolynomial`
(Fu--Lin--Zeng together with Zhang, Proposition 3.3; a documented hypothesis, verified for
permutations of at most four letters in `Enumerator.lean`), then consecutive enumerators strictly
interlace and have no common root. -/
theorem strictInterl_descentEnumerator_of_eq_descentPolynomial
    (h : ∀ n, descentEnumerator n = descentPolynomial (n + 1)) {n : ℕ} (hn : 1 ≤ n) :
    RealRooted.StrictInterl (descentEnumerator n) (descentEnumerator (n + 1)) ∧
      ∀ r : ℝ, ¬ ((descentEnumerator n).IsRoot r ∧ (descentEnumerator (n + 1)).IsRoot r) := by
  rw [h, h]
  exact strictInterl_descentPolynomial (n := n + 1) (by lia)

end RealRooted.SeparablePermutations
