import RealRooted.CombinatorialExamples.Eulerian
import RealRooted.Derivative.Interlacing
import RealRooted.EulerOperator
import RealRooted.EulerOperator.Darboux.NegativeRoots
import RealRooted.EulerOperator.Pencil
import RealRooted.EulerOperator.Polar.Pencil
import RealRooted.GammaTransform.Preservation
import RealRooted.Hadamard.Consequences
import RealRooted.Interlacing.OuterDifference
import RealRooted.OrderedRoots
import RealRooted.ReciprocalShift.ProperPosition
import RealRooted.SimpleRoots
import RealRooted.SymmetricDecomposition.Decomposition
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Super-Eulerian (powered Eulerian) polynomials

Fix an exponent `l`.  The *super-Eulerian triangle* is `E_{1,0} = 1` and
`E_{n,k} = (k+1)^l E_{n-1,k} + (n-k)^l E_{n-1,k-1}` (entries outside `0 ≤ k ≤ n-1` vanish); the
corresponding row polynomial is `E_n^{(l)}(t) = ∑_{k<n} E_{n,k} t^k`.  For `l = 1` these are the
Eulerian polynomials.  The family is the `r = 1` case of the `(l, r)`-Eulerian numbers of
U. Shankar, *Multivariate stability of powered triangular recurrences and parametrised
Eulerian polynomials* (arXiv:2609.15651), Theorem C.  Real-rootedness, gamma-positivity and weak
interlacing follow P. Alexandersson, *Real-rooted Eulerian polynomials from permutations,
words, and paths* (arXiv:2609.07325), Theorem on super-Eulerian polynomials; the simple zeros
and strict interlacing follow the root-movement argument of Shankar, Theorem C(ii), with the
stable-pencil input replaced by the Garloff--Wagner theorem.

* `superEulerianNumber`, `superEulerian`: the triangle and its row polynomials (`E_0 = 0`).
* `superEulerianNumber_symm`, `reflect_superEulerian`: palindromicity.
* `natDegree_superEulerian`, `hasNonnegCoeffs_superEulerian`: `deg E_{n+1} = n`, nonnegative
  coefficients.
* `eulerianTilde_eq_X_mul_superEulerian_one`: for `l = 1` the rows are the Eulerian polynomials
  (`eulerianTilde n = X * E_{n+1}^{(1)}`).
* `isPFPolynomial_superEulerian`, `isRealRooted_superEulerian`: for `l ≥ 1` every row has
  nonnegative coefficients and only nonpositive real zeros.
* `interl_superEulerian_succ`: `E_n ⪯ E_{n+1}` (in the repository convention `Interl`, the
  right polynomial has the rightmost zero).
* `exists_gamma_superEulerian`, `isRealRooted_gamma_superEulerian`: the gamma-polynomial is
  real-rooted with nonpositive zeros and has nonnegative coefficients; this uses the general
  gamma criterion `IsGammaExpansion.isRealRooted_and_hasRootsNonpos_iff` and the existence
  theorem `exists_isGammaExpansion_of_idTransform_eq` for palindromic polynomials.
* `simpleNegRooted_superEulerian`, `hasSimpleRoots_superEulerian`: the zeros of `E_{n+1}` are
  simple and negative.
* `strictInterl_superEulerian_succ`: `E_{n+1}` and `E_{n+2}` strictly interlace and have no
  common zero.

The weak route is that of the paper.  The normalized rows
`Ẽ_n = ∑_k E_{n,k} / C(n-1,k)^l t^k` satisfy `Ẽ_{n+1} = (1+t) ((θ+1)(n-θ)/n)^l Ẽ_n`; both
operators preserve the Pólya frequency cone, and `E_n = B_n ⊙ Ẽ_n` with the `l`-fold Hadamard
power `B_n` of `(1+t)^{n-1}`.  The identity
`E_{n+1} = (θ+1)^l E_n + t^n ((θ+1)^l E_n)(1/t)`, the Garloff--Wagner two-pair theorem, the
reversal of interlacing and the cone property give `E_n ⪯ E_{n+1}`.

For strictness, write `U = (θ+1)^l E_n` and `V = (n-θ)^l E_n`, so that
`E_{n+1} = U + t V`.  If `E_n` has simple negative zeros `ε_1 < ⋯ < ε_{n-1}`, then `θ + 1` and
`n - θ` move every ordered zero strictly to the right and left respectively (Rolle), so the
ordered zeros satisfy `v_i < ε_i < u_i`.  The Garloff--Wagner theorem, applied to the
kernels `(n-θ)(1+t)^{n-1}` and `(θ+1)(1+t)^{n-1}`, gives the weak interlacing
`u_i ≤ v_{i+1}`.  Hence `u_{i-1} ≤ v_i < ε_i < u_i`, so `U` does not vanish at any `ε_i`; at
`ε_i` the values of `U` and `t V` have the same sign (`E_n ⪯ U` and `E_n ⪯ t V`), so neither
does `E_{n+1}`.
-/

open Polynomial

noncomputable section

namespace RealRooted


/-- A real-rooted polynomial whose zeros are all nonpositive and whose constant coefficient is
positive has nonnegative coefficients. -/
theorem hasNonnegCoeffs_of_splits_of_roots_nonpos_of_coeff_zero_pos {p : ℝ[X]}
    (hs : p.Splits) (hr : ∀ r ∈ p.roots, r ≤ 0) (h0 : 0 < p.coeff 0) : HasNonnegCoeffs p := by
  have hP : HasNonnegCoeffs ((p.roots.map (X - C ·)).prod) :=
    hasNonnegCoeffs_multiset_prod_X_sub_C p.roots hr
  have hp : p = C p.leadingCoeff * (p.roots.map (X - C ·)).prod :=
    (C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_of_splits hs)).symm
  have hc := congrArg (fun q => q.coeff 0) hp
  simp only [coeff_C_mul] at hc
  have hlc : 0 < p.leadingCoeff := by
    by_contra hneg
    push Not at hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg (hP 0)
    linarith
  rw [hp]
  exact nonnegCoeffs_C_mul hlc.le hP

private lemma gamma_expansion_remainder {d : ℕ} {p : ℝ[X]} (hdeg : p.natDegree ≤ d)
    (hfix : idTransform d p = p) (hd : 1 ≤ d) :
    (p - C (p.coeff 0) * (X + 1) ^ d).natDegree < d ∧
      idTransform d (p - C (p.coeff 0) * (X + 1) ^ d) = p - C (p.coeff 0) * (X + 1) ^ d := by
  have htop : p.coeff d = p.coeff 0 := by
    have := congrArg (fun q => q.coeff 0) hfix
    simpa [idTransform, coeff_reflect, revAt_le (Nat.zero_le d)] using this
  refine ⟨?_, ?_⟩
  · have hle : (p - C (p.coeff 0) * (X + 1) ^ d).natDegree ≤ d - 1 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [coeff_sub, coeff_C_mul, coeff_X_add_one_pow]
      rcases eq_or_lt_of_le (show d ≤ N by lia) with rfl | hlt
      · simp [htop]
      · simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hlt),
          Nat.choose_eq_zero_of_lt hlt]
    lia
  · have h2 := idTransform_X_add_one_pow d
    unfold idTransform at hfix h2 ⊢
    rw [reflect_sub, reflect_C_mul, hfix, h2]

/-- Every polynomial of degree at most `d` that is fixed by the reflection `idTransform d`
(that is, palindromic of ambient degree `d`) has a gamma expansion `p = gammaTransform d γ`
with `deg γ ≤ ⌊d / 2⌋` and `γ(0) = p(0)`. -/
theorem exists_isGammaExpansion_of_idTransform_eq :
    ∀ (d : ℕ) (p : ℝ[X]), p.natDegree ≤ d → idTransform d p = p →
      ∃ γ : ℝ[X], γ.natDegree ≤ d / 2 ∧ γ.coeff 0 = p.coeff 0 ∧ IsGammaExpansion d p γ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro p hdeg hfix
  rcases d with _ | d
  · refine ⟨p, by simpa using hdeg, rfl, ?_⟩
    have h0 : gammaTransform 0 p = C (p.coeff 0) := by
      simp [gammaTransform, gammaBasisTerm]
    rw [IsGammaExpansion, h0]
    exact eq_C_of_natDegree_le_zero hdeg
  obtain ⟨hlt, hfix'⟩ := gamma_expansion_remainder hdeg hfix (Nat.succ_pos d)
  set p' : ℝ[X] := p - C (p.coeff 0) * (X + 1) ^ (d + 1) with hp'
  have hbin :
      gammaTransform (d + 1) (C (p.coeff 0)) = C (p.coeff 0) * (X + 1) ^ (d + 1) := by
    simpa using gammaTransform_C_mul_X_pow (D := d + 1) (i := 0) (p.coeff 0) (Nat.zero_le _)
  have hp'0 : p'.coeff 0 = 0 := by simp [hp', coeff_X_add_one_pow]
  rcases d with _ | d
  · have hp'zero : p' = 0 := by
      rw [eq_C_of_natDegree_le_zero (by lia : p'.natDegree ≤ 0), hp'0]
      simp
    refine ⟨C (p.coeff 0), by simp, by simp, ?_⟩
    rw [IsGammaExpansion, hbin]
    linear_combination hp'zero
  · obtain ⟨q, hq, hqfix⟩ := exists_eq_X_mul_of_idTransform_fixed_of_natDegree_lt hfix' hlt
    have hqdeg : q.natDegree ≤ d := by
      by_cases hq0 : q = 0
      · simp [hq0]
      · have := natDegree_X_mul hq0
        rw [← hq] at this
        lia
    obtain ⟨γ, hγdeg, hγ0, hγ⟩ := ih d (by lia) q hqdeg (by simpa using hqfix)
    refine ⟨C (p.coeff 0) + X * γ, ?_, ?_, ?_⟩
    · have h3 : (X * γ).natDegree ≤ γ.natDegree + 1 := by
        simpa [add_comm] using natDegree_mul_le (p := X) (q := γ)
      have h2 : (C (p.coeff 0) + X * γ).natDegree ≤
          max (C (p.coeff 0)).natDegree (X * γ).natDegree := natDegree_add_le _ _
      simp only [natDegree_C] at h2
      lia
    · simp
    · rw [IsGammaExpansion, gammaTransform_add, hbin, gammaTransform_X_mul_two, ← hγ]
      linear_combination hq

/-- Corresponding ordered roots of a same-degree interlacing pair with no common root are
strictly ordered. -/
theorem orderedRoot_lt_of_strictInterl {p q : ℝ[X]} {n : ℕ} (h : StrictInterl p q)
    (hp : p.natDegree = n) (hq : q.natDegree = n) (hno : ∀ r, p.IsRoot r → ¬ q.IsRoot r)
    (i : Fin n) : orderedRoot p n i < orderedRoot q n i := by
  refine lt_of_le_of_ne (h.orderedRoot_le hp hq i) fun heq => ?_
  have hpm := orderedRoot_mem_roots (n := n) (by rw [card_roots_of_splits h.1.2, hp]) i
  have hqm := orderedRoot_mem_roots (n := n) (by rw [card_roots_of_splits h.2.1.2, hq]) i
  rw [← heq] at hqm
  exact hno _ ((mem_roots h.1.1).mp hpm) ((mem_roots h.2.1.1).mp hqm)

/-- The ordered roots are monotone in the index. -/
theorem orderedRoot_mono {p : ℝ[X]} {n : ℕ} (hcard : p.roots.card = n) {i j : Fin n}
    (hij : i ≤ j) : orderedRoot p n i ≤ orderedRoot p n j := by
  have hlen : (p.roots.sort (· ≤ ·)).length = n := by simp [hcard]
  have hi : i.val < (p.roots.sort (· ≤ ·)).length := by lia
  have hj : j.val < (p.roots.sort (· ≤ ·)).length := by lia
  rw [orderedRoot, orderedRoot, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some, Option.getD_some]
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact (List.pairwise_iff_getElem.mp (Multiset.pairwise_sort _ _)) _ _ hi hj hlt

/-- Every root is an ordered root. -/
theorem exists_orderedRoot_eq {p : ℝ[X]} {n : ℕ} (hcard : p.roots.card = n) {x : ℝ}
    (hx : x ∈ p.roots) : ∃ i : Fin n, orderedRoot p n i = x := by
  have hlen : (p.roots.sort (· ≤ ·)).length = n := by simp [hcard]
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp ((Multiset.mem_sort (· ≤ ·)).mpr hx)
  refine ⟨⟨i, by lia⟩, ?_⟩
  rw [orderedRoot, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact hix

/-- `(θ + 1)` keeps the degree of a polynomial with positive coefficients. -/
private lemma natDegree_thetaPlusOne_of_nonneg {g : ℝ[X]} {d : ℕ} (hg : g.natDegree = d)
    (hg0 : g ≠ 0) : (thetaPlusOne g).natDegree = d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    simp [coeff_eq_zero_of_natDegree_lt (hg ▸ hk)]
  · have : g.coeff d ≠ 0 := hg ▸ (leadingCoeff_ne_zero.mpr hg0)
    rw [coeff_thetaPlusOne]
    exact mul_ne_zero (by positivity) this

/-- `N - θ` keeps the degree of a polynomial of smaller degree. -/
private lemma natDegree_polarTheta_of_lt {g : ℝ[X]} {d N : ℕ} (hg : g.natDegree = d)
    (hg0 : g ≠ 0) (hN : d < N) : (polarTheta N g).natDegree = d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    simp [coeff_eq_zero_of_natDegree_lt (hg ▸ hk)]
  · have : g.coeff d ≠ 0 := hg ▸ (leadingCoeff_ne_zero.mpr hg0)
    have hNd : (N : ℝ) - d ≠ 0 := by
      have : (d : ℝ) < N := by exact_mod_cast hN
      linarith
    simpa [coeff_polarTheta, hNd] using this

/-- **Root movement for `θ + 1`.**  If `g` has simple negative zeros, so does `(θ + 1) g`, and
each of its ordered zeros lies strictly to the right of the corresponding zero of `g`. -/
theorem SimpleNegRooted.thetaPlusOne {g : ℝ[X]} {d : ℕ} (hg : SimpleNegRooted g d) :
    SimpleNegRooted (RealRooted.thetaPlusOne g) d ∧
      ∀ i : Fin d, orderedRoot g d i < orderedRoot (RealRooted.thetaPlusOne g) d i := by
  have hg0 : g ≠ 0 := hg.pos.ne_zero
  have hpf : IsPFPolynomial g := IsPFPolynomial.of_realRooted_nonneg hg.nonneg hg.splits
  have hXg : IsPFPolynomial (X * g) := hpf.X_mul
  have hXg0 : X * g ≠ 0 := mul_ne_zero X_ne_zero hg0
  have hder : StrictInterl (RealRooted.thetaPlusOne g) (X * g) := by
    rw [thetaPlusOne_eq_derivative_X_mul]
    refine (interlaces_derivative_of_pos_natDegree hXg0 (hXg.ne_zero_and_splits hXg0).2
      (hXg.hasNonnegCoeffs.pos_leadingCoeff hXg0) ?_).toStrictInterl
    rw [natDegree_mul X_ne_zero hg0, hg.natDegree_eq]
    simp
  have hpfΘ : IsPFPolynomial (RealRooted.thetaPlusOne g) := thetaPlusOne_preserves_pf hpf
  have hint : StrictInterl g (RealRooted.thetaPlusOne g) :=
    (strictInterl_iff_mul_X_of_roots_nonpos hpf.roots_nonpos hpfΘ.roots_nonpos).mpr hder
  have hno : ∀ r, g.IsRoot r → ¬ (RealRooted.thetaPlusOne g).IsRoot r := by
    intro r hr hΘ
    have hrneg : r < 0 := hg.isRoot_neg hr
    have heval : (RealRooted.thetaPlusOne g).eval r = r * g.derivative.eval r := by
      simp [RealRooted.thetaPlusOne, theta, hr.eq_zero]
    rw [IsRoot, heval] at hΘ
    exact hg.simple.eval_derivative_ne_zero hr ((mul_eq_zero.mp hΘ).resolve_left hrneg.ne)
  have hdeg := natDegree_thetaPlusOne_of_nonneg hg.natDegree_eq hg0
  have hΘ0 : (RealRooted.thetaPlusOne g).coeff 0 ≠ 0 := by
    simpa [coeff_thetaPlusOne] using hg.coeff_zero_pos.ne'
  refine ⟨⟨hdeg, hpfΘ.hasNonnegCoeffs.pos_leadingCoeff fun h => hΘ0 (by simp [h]),
    hpfΘ.hasNonnegCoeffs, ?_, hint.2.1.2,
    (hint.hasSimpleRoots_of_no_common_root fun r hr => hno r hr.1 hr.2).2⟩,
    orderedRoot_lt_of_strictInterl hint hg.natDegree_eq hdeg hno⟩
  simpa [coeff_thetaPlusOne] using hg.coeff_zero_pos

/-- **Root movement for `N - θ`.**  If `g` has simple negative zeros and degree `d < N`, so does
`(N - θ) g`, and each of its ordered zeros lies strictly to the left of the corresponding zero
of `g`. -/
theorem SimpleNegRooted.polarTheta {g : ℝ[X]} {d N : ℕ} (hd : 0 < d) (hN : d < N)
    (hg : SimpleNegRooted g d) :
    SimpleNegRooted (RealRooted.polarTheta N g) d ∧
      ∀ i : Fin d, orderedRoot (RealRooted.polarTheta N g) d i < orderedRoot g d i := by
  have hg0 : g ≠ 0 := hg.pos.ne_zero
  have hpf : IsPFPolynomial g := IsPFPolynomial.of_realRooted_nonneg hg.nonneg hg.splits
  have hdegle : g.natDegree ≤ N := by rw [hg.natDegree_eq]; lia
  have hpfP : IsPFPolynomial (RealRooted.polarTheta N g) := polarTheta_preserves_pf hpf hdegle
  have hshift : 2 ≤ (reciprocalShift N g).natDegree := by
    have hcoeff : (reciprocalShift N g).coeff N ≠ 0 := by
      simpa using hg.coeff_zero_pos.ne'
    exact le_trans (by lia) (le_natDegree_of_ne_zero hcoeff)
  have hint : StrictInterl (RealRooted.polarTheta N g) g :=
    strictInterl_polarTheta_self hpf hdegle hshift
  have hno : ∀ r, (RealRooted.polarTheta N g).IsRoot r → ¬ g.IsRoot r := by
    intro r hΘ hr
    have hrneg : r < 0 := hg.isRoot_neg hr
    have heval : (RealRooted.polarTheta N g).eval r = -(r * g.derivative.eval r) := by
      simp [RealRooted.polarTheta, theta, hr.eq_zero]
    rw [IsRoot, heval, neg_eq_zero] at hΘ
    exact hg.simple.eval_derivative_ne_zero hr ((mul_eq_zero.mp hΘ).resolve_left hrneg.ne)
  have hdeg := natDegree_polarTheta_of_lt hg.natDegree_eq hg0 hN
  have hP0 : (RealRooted.polarTheta N g).coeff 0 ≠ 0 := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by lia : 0 < N)
    simpa [coeff_polarTheta] using (mul_pos hNpos hg.coeff_zero_pos).ne'
  refine ⟨⟨hdeg, hpfP.hasNonnegCoeffs.pos_leadingCoeff fun h => hP0 (by simp [h]),
    hpfP.hasNonnegCoeffs, ?_, hint.1.2,
    (hint.hasSimpleRoots_of_no_common_root fun r hr => hno r hr.1 hr.2).1⟩,
    orderedRoot_lt_of_strictInterl hint hdeg hg.natDegree_eq hno⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by lia : 0 < N)
  simpa [coeff_polarTheta] using mul_pos hNpos hg.coeff_zero_pos

/-- The `k`-fold iterate of `θ + 1` keeps simple negative zeros and moves every ordered zero to
the right. -/
theorem SimpleNegRooted.iterateThetaPlusOne {E : ℝ[X]} {d : ℕ} (hE : SimpleNegRooted E d)
    (k : ℕ) :
    SimpleNegRooted (RealRooted.iterateThetaPlusOne k E) d ∧
      ∀ i : Fin d, orderedRoot E d i ≤ orderedRoot (RealRooted.iterateThetaPlusOne k E) d i := by
  induction k with
  | zero => exact ⟨by simpa using hE, fun i => by simp⟩
  | succ k ih =>
      rw [iterateThetaPlusOne_succ]
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨h3, h4⟩ := h1.thetaPlusOne
      exact ⟨h3, fun i => (h2 i).trans (h4 i).le⟩

/-- The `(k+1)`-fold iterate of `θ + 1` moves every ordered zero strictly to the right. -/
theorem SimpleNegRooted.orderedRoot_lt_iterateThetaPlusOne {E : ℝ[X]} {d : ℕ}
    (hE : SimpleNegRooted E d) (k : ℕ) (i : Fin d) :
    orderedRoot E d i < orderedRoot (RealRooted.iterateThetaPlusOne (k + 1) E) d i := by
  rw [iterateThetaPlusOne_succ]
  obtain ⟨h1, h2⟩ := hE.iterateThetaPlusOne k
  exact lt_of_le_of_lt (h2 i) (h1.thetaPlusOne.2 i)

/-- The `k`-fold iterate of `N - θ` keeps simple negative zeros and moves every ordered zero to
the left. -/
theorem SimpleNegRooted.iteratePolarTheta {E : ℝ[X]} {d N : ℕ} (hd : 0 < d) (hN : d < N)
    (hE : SimpleNegRooted E d) (k : ℕ) :
    SimpleNegRooted ((RealRooted.polarTheta N)^[k] E) d ∧
      ∀ i : Fin d, orderedRoot ((RealRooted.polarTheta N)^[k] E) d i ≤ orderedRoot E d i := by
  induction k with
  | zero => exact ⟨by simpa using hE, fun i => by simp⟩
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨h3, h4⟩ := h1.polarTheta hd hN
      exact ⟨h3, fun i => (h4 i).le.trans (h2 i)⟩

/-- The `(k+1)`-fold iterate of `N - θ` moves every ordered zero strictly to the left. -/
theorem SimpleNegRooted.orderedRoot_iteratePolarTheta_lt {E : ℝ[X]} {d N : ℕ} (hd : 0 < d)
    (hN : d < N) (hE : SimpleNegRooted E d) (k : ℕ) (i : Fin d) :
    orderedRoot ((RealRooted.polarTheta N)^[k + 1] E) d i < orderedRoot E d i := by
  rw [Function.iterate_succ_apply']
  obtain ⟨h1, h2⟩ := hE.iteratePolarTheta hd hN k
  exact lt_of_lt_of_le ((h1.polarTheta hd hN).2 i) (h2 i)

/-- Ordered-root chain criterion for the absence of common zeros: if the ordered zeros of `V`,
`E`, `U` satisfy `v_i < e_i < u_i` and `u_i ≤ v_{i+1}`, then `E` and `U` have no common zero. -/
theorem not_isRoot_of_orderedRoot_chain {E U V : ℝ[X]} {d : ℕ} (hE0 : E ≠ 0) (hU0 : U ≠ 0)
    (hE : E.roots.card = d) (hU : U.roots.card = d)
    (h1 : ∀ i : Fin d, orderedRoot E d i < orderedRoot U d i)
    (h2 : ∀ i : Fin d, orderedRoot V d i < orderedRoot E d i)
    (h3 : ∀ (i : Fin d) (hi : i.val + 1 < d),
      orderedRoot U d i ≤ orderedRoot V d ⟨i.val + 1, hi⟩)
    (r : ℝ) (hr : E.IsRoot r) : ¬ U.IsRoot r := by
  intro hr'
  obtain ⟨i, hi⟩ := exists_orderedRoot_eq hE ((mem_roots hE0).mpr hr)
  obtain ⟨j, hj⟩ := exists_orderedRoot_eq hU ((mem_roots hU0).mpr hr')
  rcases le_or_gt i j with hij | hji
  · have h4 := orderedRoot_mono hU hij
    have h5 := h1 i
    linarith
  · have hj1 : j.val + 1 < d := by have := i.2; lia
    have hle : (⟨j.val + 1, hj1⟩ : Fin d) ≤ i := hji
    have h4 := h3 j hj1
    have h5 := h2 ⟨j.val + 1, hj1⟩
    have h6 := orderedRoot_mono hE hle
    linarith

namespace SuperEulerian

/-- The super-Eulerian (powered Eulerian) triangle of Shankar: `E_{1,0} = 1` and
`E_{n,k} = (k+1)^l E_{n-1,k} + (n-k)^l E_{n-1,k-1}`, with out-of-range entries zero.
Row `0` is set to zero. -/
def superEulerianNumber (l : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, k => if k = 0 then 1 else 0
  | n + 2, 0 => superEulerianNumber l (n + 1) 0
  | n + 2, k + 1 =>
      (k + 2) ^ l * superEulerianNumber l (n + 1) (k + 1) +
        (n + 1 - k) ^ l * superEulerianNumber l (n + 1) k

/-- The recurrence at `k = 0`: `E_{n+2,0} = E_{n+1,0}`. -/
theorem superEulerianNumber_succ_succ_zero (l n : ℕ) :
    superEulerianNumber l (n + 2) 0 = superEulerianNumber l (n + 1) 0 := rfl

/-- The recurrence `E_{n+2,k+1} = (k+2)^l E_{n+1,k+1} + (n+1-k)^l E_{n+1,k}`. -/
theorem superEulerianNumber_succ_succ_succ (l n k : ℕ) :
    superEulerianNumber l (n + 2) (k + 1) =
      (k + 2) ^ l * superEulerianNumber l (n + 1) (k + 1) +
        (n + 1 - k) ^ l * superEulerianNumber l (n + 1) k := rfl

/-- The polynomial `∑_{k < n} f k X^k`. -/
private def finPoly (n : ℕ) (f : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range n, C (f k) * X ^ k

private lemma coeff_finPoly (n : ℕ) (f : ℕ → ℝ) (k : ℕ) :
    (finPoly n f).coeff k = if k < n then f k else 0 := by
  simp [finPoly, coeff_C_mul, coeff_X_pow]

/-- The `n`-th super-Eulerian polynomial `∑_{k<n} E_{n,k} X^k`. -/
def superEulerian (l n : ℕ) : ℝ[X] :=
  finPoly n fun k => (superEulerianNumber l n k : ℝ)

/-- Entries to the right of the last column vanish: `E_{n,k} = 0` for `n ≤ k`. -/
theorem superEulerianNumber_eq_zero_of_le (l : ℕ) :
    ∀ n k : ℕ, n ≤ k → superEulerianNumber l n k = 0
  | 0, _, _ => rfl
  | 1, 0, h => absurd h (by decide)
  | 1, k + 1, _ => rfl
  | n + 2, 0, h => absurd h (by lia)
  | n + 2, k + 1, h => by
      rw [superEulerianNumber, superEulerianNumber_eq_zero_of_le l (n + 1) (k + 1) (by lia),
        superEulerianNumber_eq_zero_of_le l (n + 1) k (by lia)]
      simp

/-- The coefficient of `t^k` in the `n`-th super-Eulerian polynomial is `E_{n,k}`. -/
@[simp] theorem coeff_superEulerian (l n k : ℕ) :
    (superEulerian l n).coeff k = (superEulerianNumber l n k : ℝ) := by
  rw [superEulerian, coeff_finPoly]
  split_ifs with h
  · rfl
  · simp [superEulerianNumber_eq_zero_of_le l n k (by lia)]

example : (List.range 5).map (superEulerianNumber 2 5) = [1, 180, 738, 180, 1] := by decide
example : (List.range 3).map (superEulerianNumber 3 3) = [1, 16, 1] := by decide

/-- The first column is `1`: `E_{n+1,0} = 1`. -/
theorem superEulerianNumber_succ_zero (l n : ℕ) : superEulerianNumber l (n + 1) 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [superEulerianNumber_succ_succ_zero, ih]

/-- The last column is `1`: `E_{n+1,n} = 1`. -/
theorem superEulerianNumber_succ_self (l n : ℕ) : superEulerianNumber l (n + 1) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [superEulerianNumber_succ_succ_succ,
        superEulerianNumber_eq_zero_of_le l (n + 1) (n + 1) le_rfl, ih]
      simp

/-- Palindromicity of the super-Eulerian triangle. -/
theorem superEulerianNumber_symm (l : ℕ) :
    ∀ n i j : ℕ, i + j = n → superEulerianNumber l (n + 1) i = superEulerianNumber l (n + 1) j
  | 0, i, j, h => by
      obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by lia
      rfl
  | n + 1, 0, 0, h => absurd h (by lia)
  | n + 1, 0, j + 1, h => by
      obtain rfl : j = n := by lia
      rw [superEulerianNumber_succ_succ_succ, superEulerianNumber_eq_zero_of_le l (j + 1) (j + 1)
        le_rfl, superEulerianNumber_succ_zero, superEulerianNumber_succ_self]
      simp
  | n + 1, i + 1, 0, h => by
      obtain rfl : i = n := by lia
      rw [superEulerianNumber_succ_succ_succ, superEulerianNumber_eq_zero_of_le l (i + 1) (i + 1)
        le_rfl, superEulerianNumber_succ_zero, superEulerianNumber_succ_self]
      simp
  | n + 1, i + 1, j + 1, h => by
      obtain rfl : n = i + j + 1 := by lia
      have h1 : i + j + 1 + 1 - i = j + 2 := by lia
      have h2 : i + j + 1 + 1 - j = i + 2 := by lia
      rw [superEulerianNumber_succ_succ_succ l (i + j + 1) i,
        superEulerianNumber_succ_succ_succ l (i + j + 1) j, h1, h2,
        superEulerianNumber_symm l (i + j + 1) (i + 1) j (by lia),
        superEulerianNumber_symm l (i + j + 1) i (j + 1) (by lia)]
      ring

/-- Super-Eulerian polynomials have nonnegative coefficients. -/
theorem hasNonnegCoeffs_superEulerian (l n : ℕ) : HasNonnegCoeffs (superEulerian l n) := by
  intro k
  simp

/-- The row `E_{n+1}^{(l)}` has degree `n`. -/
theorem natDegree_superEulerian (l n : ℕ) : (superEulerian l (n + 1)).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    simp [superEulerianNumber_eq_zero_of_le l (n + 1) k (by lia)]
  · simp [superEulerianNumber_succ_self]

/-- The rows `E_{n+1}^{(l)}` are nonzero. -/
theorem superEulerian_succ_ne_zero (l n : ℕ) : superEulerian l (n + 1) ≠ 0 := by
  intro h
  have := natDegree_superEulerian l n
  have hc := congrArg (fun p => p.coeff 0) h
  simp [superEulerianNumber_succ_zero] at hc

/-- The coefficient reflection of a super-Eulerian polynomial fixes it: palindromicity. -/
theorem reflect_superEulerian (l n : ℕ) :
    (superEulerian l (n + 1)).reflect n = superEulerian l (n + 1) := by
  ext k
  rw [coeff_reflect]
  by_cases hk : k ≤ n
  · rw [revAt_le hk]
    simp only [coeff_superEulerian, Nat.cast_inj]
    exact superEulerianNumber_symm l n (n - k) k (by lia)
  · rw [revAt_eq_self_of_lt (lt_of_not_ge hk)]

private lemma coeff_eulerianTilde_zero (n : ℕ) : (eulerianTilde n).coeff 0 = 0 := by
  cases n <;> simp [eulerianTilde_recurrence]

private lemma coeff_eulerianTilde_succ_eq (n k : ℕ) :
    (eulerianTilde n).coeff (k + 1) = (superEulerianNumber 1 (n + 1) k : ℝ) := by
  induction n generalizing k with
  | zero =>
      simp only [eulerianTilde_zero, coeff_X, zero_add]
      rcases k with _ | k <;> simp [superEulerianNumber]
  | succ n ih =>
      rw [coeff_eulerianTilde_succ]
      rcases k with _ | k
      · simp [ih, coeff_eulerianTilde_zero, superEulerianNumber_succ_succ_zero]
      · rw [ih, ih, superEulerianNumber_succ_succ_succ]
        by_cases hk : k ≤ n + 1
        · push_cast [Nat.cast_sub hk]
          ring
        · have h0 : superEulerianNumber 1 (n + 1) k = 0 :=
            superEulerianNumber_eq_zero_of_le 1 (n + 1) k (by lia)
          have h1 : superEulerianNumber 1 (n + 1) (k + 1) = 0 :=
            superEulerianNumber_eq_zero_of_le 1 (n + 1) (k + 1) (by lia)
          simp [h0, h1]

/-- For `l = 1` the super-Eulerian polynomials are the classical Eulerian polynomials:
`eulerianTilde n = X * E_{n+1}^{(1)}`. -/
theorem eulerianTilde_eq_X_mul_superEulerian_one (n : ℕ) :
    eulerianTilde n = X * superEulerian 1 (n + 1) := by
  ext k
  rcases k with _ | k
  · simp [coeff_eulerianTilde_zero]
  · rw [coeff_eulerianTilde_succ_eq, coeff_X_mul, coeff_superEulerian]

/-! ### Hadamard powers and the binomial kernel -/

/-- The `(l+1)`-fold Hadamard power of `F`: its coefficients are `(F.coeff k)^(l+1)`. -/
private def hadPow (F : ℝ[X]) : ℕ → ℝ[X]
  | 0 => F
  | l + 1 => hadamardProduct (hadPow F l) F

private lemma coeff_hadPow (F : ℝ[X]) (l k : ℕ) :
    (hadPow F l).coeff k = F.coeff k ^ (l + 1) := by
  induction l with
  | zero => simp [hadPow]
  | succ l ih => rw [hadPow, coeff_hadamardProduct, ih]; ring

private lemma isPFPolynomial_hadPow {F : ℝ[X]} (hF : IsPFPolynomial F) (l : ℕ) :
    IsPFPolynomial (hadPow F l) := by
  induction l with
  | zero => exact hF
  | succ l ih => exact ih.hadamardProduct hF

private lemma interl_hadPow {F G : ℝ[X]} (hF : IsPFPolynomial F) (hG : IsPFPolynomial G)
    (h : Interl F G) (l : ℕ) : Interl (hadPow F l) (hadPow G l) := by
  induction l with
  | zero => exact h
  | succ l ih =>
      exact garloffWagnerHadamardPFInterl_of_nonnegStrictInterl (isPFPolynomial_hadPow hF l)
        (isPFPolynomial_hadPow hG l) hF hG ih h

private lemma thetaPlusOne_X_add_one_pow_one :
    thetaPlusOne ((X + 1 : ℝ[X]) ^ 1) = C 2 * (X + C (1 / 2)) := by
  rw [thetaPlusOne_eq_derivative_X_mul]
  simp only [pow_one, mul_add, ← C_mul]
  norm_num
  simp only [C_ofNat]
  ring

/-- The binomial row `(X+1)^m` precedes its `(θ+1)`-image. -/
private lemma interl_X_add_one_pow_thetaPlusOne (m : ℕ) :
    Interl ((X + 1 : ℝ[X]) ^ m) (thetaPlusOne ((X + 1) ^ m)) := by
  have hpf : IsPFPolynomial ((X + 1 : ℝ[X]) ^ m) := isPFPolynomial_X_add_one.pow m
  rcases m with _ | _ | m
  · simpa [thetaPlusOne, theta] using IsPFPolynomial.one.interl_self
  · rw [thetaPlusOne_X_add_one_pow_one]
    refine Interl.C_mul_right_of_nonneg ?_ (by norm_num)
    simpa using (Interl.X_add_C_iff (a := 1 / 2) (b := 1)).mpr (by norm_num)
  · have hdeg : 2 ≤ ((X + 1 : ℝ[X]) ^ (m + 2)).natDegree := by
      rw [natDegree_pow]
      simp
    have := strictInterl_self_thetac hpf hdeg one_pos
    simpa [thetaPlusOne, theta] using this.toInterl

/-- The binomial row `(X+1)^m` has the polar `(m+1-θ)`-image to the left of its
`(θ+1)`-image. -/
private lemma interl_polarTheta_thetaPlusOne_X_add_one_pow (m : ℕ) :
    Interl (polarTheta (m + 1) ((X + 1 : ℝ[X]) ^ m)) (thetaPlusOne ((X + 1) ^ m)) := by
  have hpf : IsPFPolynomial ((X + 1 : ℝ[X]) ^ m) := isPFPolynomial_X_add_one.pow m
  rcases m with _ | _ | m
  · simpa [thetaPlusOne, theta, polarTheta] using IsPFPolynomial.one.interl_self
  · have h1 : polarTheta (0 + 1 + 1) ((X + 1 : ℝ[X]) ^ (0 + 1)) = X + C 2 := by
      simp only [polarTheta, theta, zero_add, pow_one]
      simp [C_ofNat]
      ring
    rw [h1, thetaPlusOne_X_add_one_pow_one]
    exact Interl.C_mul_right_of_nonneg
      ((Interl.X_add_C_iff (a := 1 / 2) (b := 2)).mpr (by norm_num)) (by norm_num)
  · have hdeg : 2 ≤ ((X + 1 : ℝ[X]) ^ (m + 2)).natDegree := by
      rw [natDegree_pow]
      simp
    exact (strictInterl_polarTheta_thetaPlusOne hpf hdeg (by rw [natDegree_pow]; simp)
      (by simp [coeff_X_add_one_pow])).toInterl

/-! ### The normalized rows -/

/-- The normalized transfer step `(θ + 1)(N - θ)`. -/
private def eulerStep (N : ℕ) (p : ℝ[X]) : ℝ[X] :=
  thetaPlusOne (polarTheta N p)

private lemma coeff_eulerStep (N : ℕ) (p : ℝ[X]) (k : ℕ) :
    (eulerStep N p).coeff k = ((k : ℝ) + 1) * (((N : ℝ) - k) * p.coeff k) := by
  simp [eulerStep]

private lemma coeff_eulerStep_iterate (N l : ℕ) (p : ℝ[X]) (k : ℕ) :
    ((eulerStep N)^[l] p).coeff k = (((k : ℝ) + 1) * ((N : ℝ) - k)) ^ l * p.coeff k := by
  induction l with
  | zero => simp
  | succ l ih => rw [Function.iterate_succ_apply', coeff_eulerStep, ih]; ring

private lemma natDegree_eulerStep_iterate_le (N l : ℕ) (p : ℝ[X]) :
    ((eulerStep N)^[l] p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  simp [coeff_eulerStep_iterate, coeff_eq_zero_of_natDegree_lt hk]

private lemma isPFPolynomial_eulerStep_iterate {N : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ N) (l : ℕ) : IsPFPolynomial ((eulerStep N)^[l] p) := by
  induction l with
  | zero => exact hp
  | succ l ih =>
      rw [Function.iterate_succ_apply']
      exact thetaPlusOne_preserves_pf
        (polarTheta_preserves_pf ih ((natDegree_eulerStep_iterate_le N l p).trans hdeg))

/-- The normalized row `∑_k E_{m+1,k} / C(m,k)^l X^k`. -/
private def normRow (l m : ℕ) : ℝ[X] :=
  finPoly (m + 1) fun k => (superEulerianNumber l (m + 1) k : ℝ) / (m.choose k : ℝ) ^ l

private lemma coeff_normRow (l m k : ℕ) :
    (normRow l m).coeff k = (superEulerianNumber l (m + 1) k : ℝ) / (m.choose k : ℝ) ^ l := by
  rw [normRow, coeff_finPoly]
  split_ifs with h
  · rfl
  · simp [superEulerianNumber_eq_zero_of_le l (m + 1) k (by lia)]

private lemma natDegree_normRow_le (l m : ℕ) : (normRow l m).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  simp [coeff_normRow, superEulerianNumber_eq_zero_of_le l (m + 1) k (by lia)]

private lemma normRow_zero (l : ℕ) : normRow l 0 = 1 := by
  ext k
  rcases k with _ | k
  · simp [coeff_normRow, superEulerianNumber_succ_zero]
  · simp [coeff_normRow, superEulerianNumber_eq_zero_of_le l 1 (k + 1) (by lia), coeff_one]

/-- The coefficient identity behind the transfer relation for the normalized rows. -/
private lemma normRow_step_real (l m j : ℕ) (hj : j < m) (a b : ℝ) :
    ((j + 2 : ℝ) ^ l * a + ((m : ℝ) + 1 - j) ^ l * b) / ((m + 1).choose (j + 1) : ℝ) ^ l =
      1 / ((m : ℝ) + 1) ^ l *
        ((((j : ℝ) + 1 + 1) * ((m : ℝ) + 1 - (j + 1))) ^ l *
            (a / (m.choose (j + 1) : ℝ) ^ l) +
          (((j : ℝ) + 1) * ((m : ℝ) + 1 - j)) ^ l * (b / (m.choose j : ℝ) ^ l)) := by
  have hjm : j + 1 ≤ m := hj
  have hc1 : (0 : ℝ) < ((m + 1).choose (j + 1) : ℕ) := by
    exact_mod_cast Nat.choose_pos (by lia)
  have hmj : (0 : ℝ) < (m : ℝ) - j := by
    have : (j : ℝ) < m := by exact_mod_cast hj
    linarith
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have e1 : (m.choose (j + 1) : ℝ) * ((m : ℝ) + 1) =
      ((m + 1).choose (j + 1) : ℝ) * ((m : ℝ) - j) := by
    have := Nat.choose_mul_succ_eq m (j + 1)
    have h2 : ((m + 1 - (j + 1) : ℕ) : ℝ) = (m : ℝ) - j := by
      rw [Nat.add_sub_add_right, Nat.cast_sub hj.le]
    rw [← h2]
    exact_mod_cast this
  have e0 : (m.choose j : ℝ) * ((m : ℝ) + 1) =
      ((m + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) := by
    have h1 := Nat.choose_mul_succ_eq m j
    have h2 := Nat.choose_succ_right_eq (m + 1) j
    have h4 : ((m.choose j * (m + 1) : ℕ) : ℝ) =
        (((m + 1).choose (j + 1) * (j + 1) : ℕ) : ℝ) := by
      rw [h1, ← h2]
    push_cast at h4
    linarith
  have ch1 : (m.choose (j + 1) : ℝ) =
      ((m + 1).choose (j + 1) : ℝ) * ((m : ℝ) - j) / ((m : ℝ) + 1) :=
    eq_div_of_mul_eq hm1.ne' e1
  have ch0 : (m.choose j : ℝ) =
      ((m + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) / ((m : ℝ) + 1) :=
    eq_div_of_mul_eq hm1.ne' e0
  have hsub : (m : ℝ) + 1 - (j + 1) = (m : ℝ) - j := by ring
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hmj1 : (0 : ℝ) < (m : ℝ) + 1 - j := by linarith
  have T1 : (((j : ℝ) + 1 + 1) * ((m : ℝ) - j)) ^ l * (a / (m.choose (j + 1) : ℝ) ^ l) /
      ((m : ℝ) + 1) ^ l = (j + 2 : ℝ) ^ l * a / ((m + 1).choose (j + 1) : ℝ) ^ l := by
    rw [ch1, div_pow, mul_pow, mul_pow, show (j : ℝ) + 1 + 1 = j + 2 by ring]
    field_simp
  have T2 : (((j : ℝ) + 1) * ((m : ℝ) + 1 - j)) ^ l * (b / (m.choose j : ℝ) ^ l) /
      ((m : ℝ) + 1) ^ l = ((m : ℝ) + 1 - j) ^ l * b / ((m + 1).choose (j + 1) : ℝ) ^ l := by
    rw [ch0, div_pow, mul_pow, mul_pow]
    field_simp
  rw [hsub, one_div, ← div_eq_inv_mul, eq_comm, add_div, T1, T2, add_div]

private lemma normRow_succ (l m : ℕ) :
    normRow l (m + 1) =
      C (1 / ((m : ℝ) + 1) ^ l) * ((X + 1) * (eulerStep (m + 1))^[l] (normRow l m)) := by
  ext k
  rw [coeff_C_mul, add_mul, one_mul, coeff_add, coeff_normRow]
  rcases k with _ | j
  · rw [coeff_X_mul_zero, coeff_eulerStep_iterate, coeff_normRow]
    have hm1 : ((m : ℝ) + 1) ^ l ≠ 0 := by positivity
    simp [superEulerianNumber_succ_zero]
    field_simp
  · rw [coeff_X_mul, coeff_eulerStep_iterate, coeff_eulerStep_iterate, coeff_normRow,
      coeff_normRow]
    rcases lt_trichotomy j m with hj | rfl | hj
    · have key := normRow_step_real l m j hj (superEulerianNumber l (m + 1) (j + 1) : ℝ)
        (superEulerianNumber l (m + 1) j : ℝ)
      rw [superEulerianNumber_succ_succ_succ]
      push_cast [Nat.cast_sub (show j ≤ m + 1 by lia)]
      linarith
    · have hm1 : ((j : ℝ) + 1) ^ l ≠ 0 := by positivity
      simp [superEulerianNumber_succ_self, superEulerianNumber_eq_zero_of_le l (j + 1) (j + 1)
        le_rfl]
      field_simp
    · have h1 : superEulerianNumber l (m + 2) (j + 1) = 0 :=
        superEulerianNumber_eq_zero_of_le l (m + 2) (j + 1) (by lia)
      have h2 : superEulerianNumber l (m + 1) (j + 1) = 0 :=
        superEulerianNumber_eq_zero_of_le l (m + 1) (j + 1) (by lia)
      have h3 : superEulerianNumber l (m + 1) j = 0 :=
        superEulerianNumber_eq_zero_of_le l (m + 1) j (by lia)
      simp [h1, h2, h3]

private lemma isPFPolynomial_normRow (l m : ℕ) : IsPFPolynomial (normRow l m) := by
  induction m with
  | zero => rw [normRow_zero]; exact IsPFPolynomial.one
  | succ m ih =>
      rw [normRow_succ]
      exact (IsPFPolynomial.of_C_nonneg (by positivity)).mul
        (isPFPolynomial_mul_X_add_one (isPFPolynomial_eulerStep_iterate ih
          ((natDegree_normRow_le l m).trans (Nat.le_succ m)) l))

/-- The Hadamard factorization `E_n = B_n ⊙ Ẽ_n` through the binomial kernel. -/
private lemma superEulerian_succ_eq_hadamard (l m : ℕ) :
    superEulerian (l + 1) (m + 1) =
      hadamardProduct (hadPow ((X + 1) ^ m) l) (normRow (l + 1) m) := by
  ext k
  rw [coeff_hadamardProduct, coeff_hadPow, coeff_X_add_one_pow, coeff_normRow,
    coeff_superEulerian]
  by_cases hk : k ≤ m
  · have : (0 : ℝ) < (m.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
    field_simp
  · rw [Nat.choose_eq_zero_of_lt (by lia)]
    simp [superEulerianNumber_eq_zero_of_le (l + 1) (m + 1) k (by lia)]

private lemma coeff_iterateThetaPlusOne (l : ℕ) (p : ℝ[X]) (k : ℕ) :
    (iterateThetaPlusOne l p).coeff k = ((k : ℝ) + 1) ^ l * p.coeff k := by
  induction l with
  | zero => simp
  | succ l ih => rw [iterateThetaPlusOne_succ, coeff_thetaPlusOne, ih]; ring

private lemma natDegree_iterateThetaPlusOne_le (l : ℕ) (p : ℝ[X]) :
    (iterateThetaPlusOne l p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  simp [coeff_iterateThetaPlusOne, coeff_eq_zero_of_natDegree_lt hk]

/-- `(θ+1)^l E_n = Λ_n ⊙ Ẽ_n`. -/
private lemma iterateThetaPlusOne_superEulerian (l m : ℕ) :
    iterateThetaPlusOne (l + 1) (superEulerian (l + 1) (m + 1)) =
      hadamardProduct (hadPow (thetaPlusOne ((X + 1) ^ m)) l) (normRow (l + 1) m) := by
  ext k
  rw [coeff_hadamardProduct, coeff_hadPow, coeff_thetaPlusOne, coeff_X_add_one_pow,
    coeff_normRow, coeff_iterateThetaPlusOne, coeff_superEulerian]
  by_cases hk : k ≤ m
  · have : (0 : ℝ) < (m.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
    rw [mul_pow]
    field_simp
  · rw [Nat.choose_eq_zero_of_lt (by lia)]
    simp [superEulerianNumber_eq_zero_of_le (l + 1) (m + 1) k (by lia)]

/-- The coefficient recurrence in the form `E_{n+1} = (θ+1)^l E_n + t^n ((θ+1)^l E_n)(1/t)`. -/
private lemma superEulerian_succ_succ_eq (l m : ℕ) :
    superEulerian l (m + 2) =
      iterateThetaPlusOne l (superEulerian l (m + 1)) +
        reciprocalShift (m + 1) (iterateThetaPlusOne l (superEulerian l (m + 1))) := by
  ext k
  rw [coeff_add, coeff_reciprocalShift, coeff_iterateThetaPlusOne, coeff_iterateThetaPlusOne]
  rcases k with _ | j
  · rw [revAt_le (Nat.zero_le _)]
    simp [superEulerianNumber_succ_succ_zero, superEulerianNumber_eq_zero_of_le l (m + 1) (m + 1)
      le_rfl]
  · by_cases hj : j ≤ m
    · rw [revAt_le (by lia), coeff_superEulerian, coeff_superEulerian, coeff_superEulerian,
        superEulerianNumber_succ_succ_succ,
        superEulerianNumber_symm l m (m + 1 - (j + 1)) j (by lia)]
      push_cast [Nat.cast_sub (show j ≤ m + 1 by lia), Nat.cast_sub hj,
        show m + 1 - (j + 1) = m - j by lia]
      ring
    · rw [revAt_eq_self_of_lt (by lia)]
      simp [superEulerianNumber_eq_zero_of_le l (m + 2) (j + 1) (by lia),
        superEulerianNumber_eq_zero_of_le l (m + 1) (j + 1) (by lia)]

/-! ### Real-rootedness and interlacing -/

/-- The `l`-super-Eulerian polynomials, `l ≥ 1`, have nonnegative coefficients and only
nonpositive real zeros (the Pólya frequency property).  See Alexandersson, "Real-rooted
Eulerian polynomials from permutations, words, and paths" (arXiv:2609.07325), Theorem on
super-Eulerian polynomials, and Shankar (arXiv:2609.15651), Theorem C. -/
theorem isPFPolynomial_superEulerian {l : ℕ} (hl : l ≠ 0) (n : ℕ) :
    IsPFPolynomial (superEulerian l n) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
  rcases n with _ | m
  · simpa [superEulerian, finPoly] using IsPFPolynomial.zero
  · rw [superEulerian_succ_eq_hadamard]
    refine (isPFPolynomial_hadPow ?_ l).hadamardProduct (isPFPolynomial_normRow _ _)
    exact isPFPolynomial_X_add_one.pow m

/-- Real-rootedness of the super-Eulerian polynomials: nonzero, all zeros real. -/
theorem isRealRooted_superEulerian {l : ℕ} (hl : l ≠ 0) (n : ℕ) :
    superEulerian l (n + 1) ≠ 0 ∧ (superEulerian l (n + 1)).Splits :=
  (isPFPolynomial_superEulerian hl (n + 1)).ne_zero_and_splits (superEulerian_succ_ne_zero l n)

/-- All zeros of a super-Eulerian polynomial are nonpositive. -/
theorem roots_nonpos_superEulerian {l : ℕ} (hl : l ≠ 0) (n : ℕ) :
    ∀ r ∈ (superEulerian l n).roots, r ≤ 0 :=
  (isPFPolynomial_superEulerian hl n).roots_nonpos

private lemma reciprocalShift_superEulerian (l m : ℕ) :
    reciprocalShift (m + 1) (superEulerian l (m + 1)) = X * superEulerian l (m + 1) := by
  ext k
  rw [coeff_reciprocalShift]
  rcases k with _ | j
  · rw [revAt_le (Nat.zero_le _)]
    simp [superEulerianNumber_eq_zero_of_le l (m + 1) (m + 1) le_rfl]
  · rw [coeff_X_mul, coeff_superEulerian]
    by_cases hj : j ≤ m
    · rw [revAt_le (by lia), coeff_superEulerian]
      simp only [Nat.cast_inj]
      exact superEulerianNumber_symm l m (m + 1 - (j + 1)) j (by lia)
    · rw [revAt_eq_self_of_lt (by lia)]
      simp [superEulerianNumber_eq_zero_of_le l (m + 1) (j + 1) (by lia),
        superEulerianNumber_eq_zero_of_le l (m + 1) j (by lia)]

/-- All zeros of a super-Eulerian polynomial (`l ≥ 1`, `n ≥ 1`) are negative. -/
theorem roots_neg_superEulerian {l : ℕ} (hl : l ≠ 0) (n : ℕ) :
    ∀ r ∈ (superEulerian l (n + 1)).roots, r < 0 := by
  intro r hr
  refine lt_of_le_of_ne (roots_nonpos_superEulerian hl _ r hr) ?_
  rintro rfl
  have h := (mem_roots (superEulerian_succ_ne_zero l n)).mp hr
  simp [IsRoot, ← coeff_zero_eq_eval_zero, superEulerianNumber_succ_zero] at h

private lemma isPFPolynomial_iterateThetaPlusOne_superEulerian (l m : ℕ) :
    IsPFPolynomial (iterateThetaPlusOne (l + 1) (superEulerian (l + 1) (m + 1))) :=
  iterateThetaPlusOne_preserves_pf (l + 1) (isPFPolynomial_superEulerian (Nat.succ_ne_zero l) _)

private lemma iterateThetaPlusOne_superEulerian_ne_zero (l m : ℕ) :
    iterateThetaPlusOne (l + 1) (superEulerian (l + 1) (m + 1)) ≠ 0 := by
  intro h
  have hc := congrArg (fun p => p.coeff 0) h
  simp [coeff_iterateThetaPlusOne, superEulerianNumber_succ_zero] at hc

private lemma natDegree_iterateThetaPlusOne_superEulerian (l m : ℕ) :
    (iterateThetaPlusOne (l + 1) (superEulerian (l + 1) (m + 1))).natDegree ≤ m := by
  simpa [natDegree_superEulerian] using natDegree_iterateThetaPlusOne_le (l + 1)
    (superEulerian (l + 1) (m + 1))

/-- `E_{m+1} ⪯ (θ+1)^l E_{m+1}`, from the Garloff--Wagner theorem. -/
private lemma interl_superEulerian_iterateThetaPlusOne (l m : ℕ) :
    Interl (superEulerian (l + 1) (m + 1))
      (iterateThetaPlusOne (l + 1) (superEulerian (l + 1) (m + 1))) := by
  have hbin : IsPFPolynomial ((X + 1 : ℝ[X]) ^ m) := isPFPolynomial_X_add_one.pow m
  rw [iterateThetaPlusOne_superEulerian, superEulerian_succ_eq_hadamard]
  exact garloffWagnerHadamardPFInterl_of_nonnegStrictInterl (isPFPolynomial_hadPow hbin l)
    (isPFPolynomial_hadPow (thetaPlusOne_preserves_pf hbin) l) (isPFPolynomial_normRow _ _)
    (isPFPolynomial_normRow _ _) (interl_hadPow hbin (thetaPlusOne_preserves_pf hbin)
      (interl_X_add_one_pow_thetaPlusOne m) l) (isPFPolynomial_normRow _ _).interl_self

private lemma isPFPolynomial_reciprocalShift_iterateThetaPlusOne (l m : ℕ) :
    IsPFPolynomial
      (reciprocalShift (m + 1) (iterateThetaPlusOne (l + 1) (superEulerian (l + 1) (m + 1)))) :=
  reciprocalShift_preserves_pf (isPFPolynomial_iterateThetaPlusOne_superEulerian l m)
    ((natDegree_iterateThetaPlusOne_superEulerian l m).trans (Nat.le_succ m))

/-- `E_{m+1} ⪯ t^{m+1} ((θ+1)^l E_{m+1})(1/t)`, by reversing the previous interlacing. -/
private lemma interl_superEulerian_reciprocalShift (l m : ℕ) :
    Interl (superEulerian (l + 1) (m + 1))
      (reciprocalShift (m + 1) (iterateThetaPlusOne (l + 1) (superEulerian (l + 1) (m + 1)))) := by
  have hEpf := isPFPolynomial_superEulerian (Nat.succ_ne_zero l) (m + 1)
  have hrev := reciprocalShift_reverses_strictInterl hEpf
    (isPFPolynomial_iterateThetaPlusOne_superEulerian l m)
    (by rw [natDegree_superEulerian]; lia)
    ((natDegree_iterateThetaPlusOne_superEulerian l m).trans (Nat.le_succ m))
    ((interl_superEulerian_iterateThetaPlusOne l m).toStrictInterl_of_ne
      (superEulerian_succ_ne_zero (l + 1) m) (iterateThetaPlusOne_superEulerian_ne_zero l m))
  rw [reciprocalShift_superEulerian] at hrev
  exact ((strictInterl_iff_mul_X_of_roots_nonpos hEpf.roots_nonpos
    (isPFPolynomial_reciprocalShift_iterateThetaPlusOne l m).roots_nonpos).mpr hrev).toInterl

/-- Consecutive super-Eulerian polynomials interlace: `E_n ⪯ E_{n+1}`, in the repository
convention `Interl f g` (`g` has the rightmost zero). -/
theorem interl_superEulerian_succ {l : ℕ} (hl : l ≠ 0) (n : ℕ) :
    Interl (superEulerian l n) (superEulerian l (n + 1)) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
  rcases n with _ | m
  · exact Or.inl (by simp [superEulerian, finPoly])
  rw [superEulerian_succ_succ_eq]
  exact interl_add_right_of_common_left_of_nonneg (interl_superEulerian_iterateThetaPlusOne l m)
    (interl_superEulerian_reciprocalShift l m)
    (isPFPolynomial_iterateThetaPlusOne_superEulerian l m).hasNonnegCoeffs
    (isPFPolynomial_reciprocalShift_iterateThetaPlusOne l m).hasNonnegCoeffs

/-! ### Gamma polynomials -/

/-- Any gamma-polynomial `γ` of a super-Eulerian polynomial (`l ≥ 1`) is real-rooted with
nonpositive zeros and has nonnegative coefficients. -/
theorem isRealRooted_gamma_superEulerian {l : ℕ} (hl : l ≠ 0) {n : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ n / 2) (hγ : IsGammaExpansion n (superEulerian l (n + 1)) γ) :
    (γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ ∧ HasNonnegCoeffs γ := by
  have hrr : (γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ :=
    (hγ.isRealRooted_and_hasRootsNonpos_iff hγdeg).mpr
      ⟨isRealRooted_superEulerian hl n, roots_nonpos_superEulerian hl _⟩
  refine ⟨hrr.1, hrr.2, ?_⟩
  have h0 : γ.coeff 0 = 1 := by
    have := congrArg (fun q => q.coeff 0) hγ
    simpa [coeff_zero_gammaTransform, superEulerianNumber_succ_zero] using this.symm
  exact hasNonnegCoeffs_of_splits_of_roots_nonpos_of_coeff_zero_pos hrr.1.2 hrr.2
    (by rw [h0]; exact one_pos)

/-- The gamma-polynomial of `E_{n+1}^{(l)}` (`l ≥ 1`) exists, is real-rooted with nonpositive
zeros, and has nonnegative coefficients. -/
theorem exists_gamma_superEulerian {l : ℕ} (hl : l ≠ 0) (n : ℕ) :
    ∃ γ : ℝ[X], γ.natDegree ≤ n / 2 ∧ IsGammaExpansion n (superEulerian l (n + 1)) γ ∧
      (γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ ∧ HasNonnegCoeffs γ := by
  obtain ⟨γ, hdeg, -, hγ⟩ := exists_isGammaExpansion_of_idTransform_eq n (superEulerian l (n + 1))
    (by rw [natDegree_superEulerian]) (reflect_superEulerian l n)
  exact ⟨γ, hdeg, hγ, isRealRooted_gamma_superEulerian hl hdeg hγ⟩

/-! ### Simple zeros and strict interlacing -/

private lemma superEulerian_one (l : ℕ) : superEulerian l 1 = 1 := by
  ext k
  rcases k with _ | k <;> simp [superEulerianNumber, coeff_one]

private lemma coeff_iterate_polarTheta (N l : ℕ) (p : ℝ[X]) (k : ℕ) :
    ((polarTheta N)^[l] p).coeff k = ((N : ℝ) - k) ^ l * p.coeff k := by
  induction l with
  | zero => simp
  | succ l ih => rw [Function.iterate_succ_apply', coeff_polarTheta, ih]; ring

/-- `(m+1-θ)^l E_{m+1} = Ω ⊙ Ẽ_{m+1}` for the polar binomial kernel `Ω`. -/
private lemma polarTheta_iterate_superEulerian (l m : ℕ) :
    (polarTheta (m + 1))^[l + 1] (superEulerian (l + 1) (m + 1)) =
      hadamardProduct (hadPow (polarTheta (m + 1) ((X + 1) ^ m)) l) (normRow (l + 1) m) := by
  ext k
  rw [coeff_hadamardProduct, coeff_hadPow, coeff_polarTheta, coeff_X_add_one_pow, coeff_normRow,
    coeff_iterate_polarTheta, coeff_superEulerian]
  by_cases hk : k ≤ m
  · have : (0 : ℝ) < (m.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
    rw [mul_pow]
    field_simp
  · rw [Nat.choose_eq_zero_of_lt (by lia)]
    simp [superEulerianNumber_eq_zero_of_le (l + 1) (m + 1) k (by lia)]

/-- `(m+1-θ)^l E_{m+1} ⪯ (θ+1)^l E_{m+1}`. -/
private lemma interl_polarThetaIterate_thetaPlusOneIterate (l m : ℕ) :
    Interl ((polarTheta (m + 1))^[l + 1] (superEulerian (l + 1) (m + 1)))
      (iterateThetaPlusOne (l + 1) (superEulerian (l + 1) (m + 1))) := by
  have hbin : IsPFPolynomial ((X + 1 : ℝ[X]) ^ m) := isPFPolynomial_X_add_one.pow m
  have hpol : IsPFPolynomial (polarTheta (m + 1) ((X + 1 : ℝ[X]) ^ m)) :=
    polarTheta_preserves_pf hbin (by rw [natDegree_pow]; simp)
  rw [polarTheta_iterate_superEulerian, iterateThetaPlusOne_superEulerian]
  exact garloffWagnerHadamardPFInterl_of_nonnegStrictInterl (isPFPolynomial_hadPow hpol l)
    (isPFPolynomial_hadPow (thetaPlusOne_preserves_pf hbin) l) (isPFPolynomial_normRow _ _)
    (isPFPolynomial_normRow _ _) (interl_hadPow hpol (thetaPlusOne_preserves_pf hbin)
      (interl_polarTheta_thetaPlusOne_X_add_one_pow m) l)
    (isPFPolynomial_normRow _ _).interl_self

/-- By palindromicity, the reciprocal of `(θ+1)^l E_{m+1}` is `X (m+1-θ)^l E_{m+1}`. -/
private lemma reciprocalShift_iterateThetaPlusOne_superEulerian (l m : ℕ) :
    reciprocalShift (m + 1) (iterateThetaPlusOne l (superEulerian l (m + 1))) =
      X * (polarTheta (m + 1))^[l] (superEulerian l (m + 1)) := by
  ext k
  rw [coeff_reciprocalShift, coeff_iterateThetaPlusOne]
  rcases k with _ | j
  · rw [revAt_le (Nat.zero_le _), coeff_X_mul_zero]
    simp [superEulerianNumber_eq_zero_of_le l (m + 1) (m + 1) le_rfl]
  · rw [coeff_X_mul, coeff_iterate_polarTheta]
    by_cases hj : j ≤ m
    · rw [revAt_le (by lia), coeff_superEulerian, coeff_superEulerian,
        superEulerianNumber_symm l m (m + 1 - (j + 1)) j (by lia)]
      push_cast [Nat.cast_sub hj, show m + 1 - (j + 1) = m - j by lia]
      ring
    · rw [revAt_eq_self_of_lt (by lia)]
      simp [superEulerianNumber_eq_zero_of_le l (m + 1) (j + 1) (by lia),
        superEulerianNumber_eq_zero_of_le l (m + 1) j (by lia)]

/-- One step of the induction: if `E_{m+1}` has simple negative zeros, then `E_{m+1}` and
`E_{m+2}` strictly interlace without common zeros.  The root movement of `θ + 1` and `m+1 - θ`
gives `v_i < e_i < u_i` for the ordered zeros of `V = (m+1-θ)^l E`, `E`, `U = (θ+1)^l E`, and the
Garloff--Wagner theorem gives `u_i ≤ v_{i+1}`; so `E` and `U` have no common zero, and the sign
of `E_{m+2} = U + X V` at the zeros of `E` is that of `U`. -/
private lemma strictInterl_superEulerian_step {l m : ℕ}
    (hE : SimpleNegRooted (superEulerian (l + 1) (m + 1)) m) :
    StrictInterl (superEulerian (l + 1) (m + 1)) (superEulerian (l + 1) (m + 2)) ∧
      ∀ r, (superEulerian (l + 1) (m + 1)).IsRoot r →
        ¬ (superEulerian (l + 1) (m + 2)).IsRoot r := by
  have hE0 : superEulerian (l + 1) (m + 1) ≠ 0 := superEulerian_succ_ne_zero _ m
  refine ⟨(interl_superEulerian_succ (Nat.succ_ne_zero l) (m + 1)).toStrictInterl_of_ne hE0
    (superEulerian_succ_ne_zero _ (m + 1)), ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · intro r hr
    simp [superEulerian_one] at hr
  set E := superEulerian (l + 1) (m + 1) with hEdef
  set U := iterateThetaPlusOne (l + 1) E with hUdef
  set V := (polarTheta (m + 1))^[l + 1] E with hVdef
  have hU : SimpleNegRooted U m := (hE.iterateThetaPlusOne (l + 1)).1
  have hV : SimpleNegRooted V m := (hE.iteratePolarTheta hm (Nat.lt_succ_self m) (l + 1)).1
  have hEU : StrictInterl E U :=
    (interl_superEulerian_iterateThetaPlusOne l m).toStrictInterl_of_ne hE0 hU.pos.ne_zero
  have hVU : StrictInterl V U :=
    (interl_polarThetaIterate_thetaPlusOneIterate l m).toStrictInterl_of_ne hV.pos.ne_zero
      hU.pos.ne_zero
  have hEcard : E.roots.card = m := by rw [card_roots_of_splits hE.splits, hE.natDegree_eq]
  have hUcard : U.roots.card = m := by rw [card_roots_of_splits hU.splits, hU.natDegree_eq]
  have hno : ∀ r, E.IsRoot r → ¬ U.IsRoot r :=
    not_isRoot_of_orderedRoot_chain hE0 hU.pos.ne_zero hEcard hUcard
      (hE.orderedRoot_lt_iterateThetaPlusOne l)
      (hE.orderedRoot_iteratePolarTheta_lt hm (Nat.lt_succ_self m) l)
      ((strictInterl_iff_orderedRoot_bounds hV.pos.ne_zero hV.splits hU.pos.ne_zero hU.splits
        hV.natDegree_eq hU.natDegree_eq).mp hVU).2
  have hrs : reciprocalShift (m + 1) U = X * V :=
    reciprocalShift_iterateThetaPlusOne_superEulerian (l + 1) m
  have hrs0 : reciprocalShift (m + 1) U ≠ 0 := by
    rw [hrs]
    exact mul_ne_zero X_ne_zero hV.pos.ne_zero
  have hErs : StrictInterl E (reciprocalShift (m + 1) U) :=
    (interl_superEulerian_reciprocalShift l m).toStrictInterl_of_ne hE0 hrs0
  have hrspos : HasPosLeadingCoeff (reciprocalShift (m + 1) U) :=
    (isPFPolynomial_reciprocalShift_iterateThetaPlusOne l m).hasNonnegCoeffs.pos_leadingCoeff hrs0
  intro α hα hF
  have hEd : E.derivative.eval α ≠ 0 := hE.simple.eval_derivative_ne_zero hα
  have h1 := hEU.eval_mul_derivative_nonpos_of_left_root hE.pos hU.pos hα
  have h2 := hErs.eval_mul_derivative_nonpos_of_left_root hE.pos hrspos hα
  have h3 : U.eval α * E.derivative.eval α < 0 :=
    lt_of_le_of_ne h1 (mul_ne_zero (fun h => hno α hα h) hEd)
  rw [superEulerian_succ_succ_eq, IsRoot, eval_add] at hF
  have h4 : (U.eval α + (reciprocalShift (m + 1) U).eval α) * E.derivative.eval α = 0 := by
    rw [hF, zero_mul]
  rw [add_mul] at h4
  linarith

/-- For `l ≥ 1`, the row `E_{n+1}^{(l)}` has degree `n`, positive leading and constant
coefficients, and simple negative zeros. -/
theorem simpleNegRooted_superEulerian {l : ℕ} (hl : l ≠ 0) (n : ℕ) :
    SimpleNegRooted (superEulerian l (n + 1)) n := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
  induction n with
  | zero => rw [superEulerian_one]; exact SimpleNegRooted.one
  | succ n ih =>
      obtain ⟨hs, hno⟩ := strictInterl_superEulerian_step ih
      exact ⟨natDegree_superEulerian _ _,
        (hasNonnegCoeffs_superEulerian _ _).pos_leadingCoeff (superEulerian_succ_ne_zero _ _),
        hasNonnegCoeffs_superEulerian _ _, by simp [superEulerianNumber_succ_zero],
        (isRealRooted_superEulerian hl (n + 1)).2,
        (hs.hasSimpleRoots_of_no_common_root fun r hr => hno r hr.1 hr.2).2⟩

/-- **Strict interlacing.**  For `l ≥ 1`, consecutive super-Eulerian polynomials strictly
interlace and have no common zero. -/
theorem strictInterl_superEulerian_succ {l : ℕ} (hl : l ≠ 0) (n : ℕ) :
    StrictInterl (superEulerian l (n + 1)) (superEulerian l (n + 2)) ∧
      ∀ r, (superEulerian l (n + 1)).IsRoot r → ¬ (superEulerian l (n + 2)).IsRoot r := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
  exact strictInterl_superEulerian_step (simpleNegRooted_superEulerian hl n)

/-- The super-Eulerian polynomials (`l ≥ 1`) have only simple zeros. -/
theorem hasSimpleRoots_superEulerian {l : ℕ} (hl : l ≠ 0) (n : ℕ) :
    HasSimpleRoots (superEulerian l (n + 1)) :=
  (simpleNegRooted_superEulerian hl n).simple

end SuperEulerian

end RealRooted
