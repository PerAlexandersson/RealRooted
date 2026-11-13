module

public import RealRooted.Basic.ProperPosition
public import RealRooted.Hadamard.Product
public import RealRooted.PFPolynomial
public import RealRooted.SimpleRoots
import RealRooted.GarloffWagner.Hadamard
import RealRooted.GarloffWagner.Theorem12
import RealRooted.Hadamard.Basic
import RealRooted.MultiplierSequence.InvPochhammerSimple
import RealRooted.Wronskian.Forward
import RealRooted.ObreschkoffConverse.Derivative
import RealRooted.LinearPowerFamily
import RealRooted.Mathlib.Algebra.Polynomial.Coeff

/-!
# Hoggatt binomial-product polynomials

We use the indexing of Fang–Zhang–Zhao, *Analytic properties arising from the
Baxter numbers*, arXiv:2505.05873, §2. The binomial-product polynomial is
`F(n,m) = ∑ k, (∏ i < m, choose n (k+i)) X^k` for `m ≥ 1`.
The normalized polynomial counts plane partitions in a box by MacMahon's
formula; that combinatorial interpretation is not formalized here.

`StrictInterl` is the library's nonzero, oriented, weak root-order predicate.
It does not by itself assert that consecutive polynomials are coprime.
-/

@[expose] public section

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- The negative-root case of Garloff–Wagner simplicity: a Hadamard product
of PF polynomials with nonzero constant coefficients has simple roots. -/
theorem hasSimpleRoots_hadamardProduct {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hp0 : p.coeff 0 ≠ 0) (hq0 : q.coeff 0 ≠ 0) :
    HasSimpleRoots (hadamardProduct p q) := by
  have hs := hp.factorialHadamardProduct hq
  have hzero : (factorialHadamardProduct p q).eval 0 ≠ 0 := by
    simpa [← coeff_zero_eq_eval_zero] using mul_ne_zero hp0 hq0
  have hsimple := hasSimpleRoots_diagonalOperator_inv_ascPochhammer
    (by norm_num : (0 : ℝ) < 1) hs.splits hzero
  have heq : diagonalOperator (fun k => ((ascPochhammer ℝ k).eval 1)⁻¹)
      (factorialHadamardProduct p q) = hadamardProduct p q := by
    rw [← divFactorial_factorialHadamardProduct]
    ext k
    simp [coeff_diagonalOperator, coeff_divFactorial, mul_comm]
  rwa [heq] at hsimple

private theorem eval_mul_nonneg_of_common_left {a b c : ℝ[X]}
    (hab : StrictInterl a b) (hac : StrictInterl a c)
    (ha : HasNonnegCoeffs a) (hb : HasNonnegCoeffs b) (hc : HasNonnegCoeffs c)
    {r : ℝ} (hr : a.IsRoot r) : 0 ≤ b.eval r * c.eval r := by
  exact eval_mul_eval_nonneg_of_strictInterl_right
    (strictInterl_mul_X_of_strictInterl_of_nonneg hab ha hb)
    (strictInterl_mul_X_of_strictInterl_of_nonneg hac ha hc)
    (hb.pos_leadingCoeff hab.2.1.1) (hc.pos_leadingCoeff hac.2.1.1)
    (by simp [Polynomial.IsRoot.def, hr.eq_zero])

private theorem hadamard_power_adjacent (N : ℕ) (q : ℝ[X]) :
    C ((N : ℝ) + 1) * hadamardProduct ((X + 1) ^ N) q =
      C ((N : ℝ) + 1) * hadamardProduct ((X + 1) ^ (N + 1)) q -
        X * (hadamardProduct ((X + 1) ^ (N + 1)) q).derivative := by
  ext k
  simp only [coeff_C_mul, coeff_hadamardProduct, coeff_X_add_one_pow, coeff_sub,
    coeff_X_mul_derivative]
  by_cases hk : k ≤ N + 1
  · have heq : ((N : ℝ) + 1 - k) * ((N + 1).choose k : ℝ) =
        ((N : ℝ) + 1) * (N.choose k : ℝ) := by
      have h := congrArg (fun v : ℕ => (v : ℝ)) (Nat.choose_mul_succ_eq N k)
      simpa [Nat.cast_sub hk, mul_comm] using h.symm
    linear_combination -q.coeff k * heq
  · simp [Nat.choose_eq_zero_of_lt (by lia : N < k),
      Nat.choose_eq_zero_of_lt (by lia : N + 1 < k)]

/-- A strict Garloff–Wagner corollary sufficient for Hoggatt induction.
Consecutive binomial powers turn any PF interlacing pair with positive
constant terms and positive linear coefficient on the right into polynomials
with no common real root. This strengthens the weak Hadamard theorem. -/
theorem StrictInterl.hadamardProduct_power_no_common_root {p q : ℝ[X]}
    (hpq : StrictInterl p q) (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hp0 : 0 < p.coeff 0) (hq0 : 0 < q.coeff 0) (hq1 : 0 < q.coeff 1)
    (N : ℕ) :
    ∀ r : ℝ, (hadamardProduct ((X + 1) ^ N) p).IsRoot r →
      ¬ (hadamardProduct ((X + 1) ^ (N + 1)) q).IsRoot r := by
  let f : ℝ[X] := (X + 1) ^ N
  have hf : IsPFPolynomial f := isPFPolynomial_X_add_one.pow N
  have hg : IsPFPolynomial ((X + 1 : ℝ[X]) ^ (N + 1)) :=
    isPFPolynomial_X_add_one.pow (N + 1)
  have hpPF := IsPFPolynomial.of_realRooted_nonneg hp hpq.1.2
  have hqPF := IsPFPolynomial.of_realRooted_nonneg hq hpq.2.1.2
  have hlin : (X + 1 : ℝ[X]) ≠ 0 := by
    intro heq
    have h := congrArg (fun v : ℝ[X] => v.coeff 1) heq
    norm_num [coeff_one] at h
  have hA0 : hadamardProduct f p ≠ 0 := by
    intro hzero
    have hz := congrArg (fun v : ℝ[X] => v.coeff 0) hzero
    simp [f, coeff_X_add_one_pow, hp0.ne'] at hz
  have hB0 : hadamardProduct f q ≠ 0 := by
    intro hzero
    have hz := congrArg (fun v : ℝ[X] => v.coeff 0) hzero
    simp [f, coeff_X_add_one_pow, hq0.ne'] at hz
  have hT0 : hadamardProduct (X * f) q ≠ 0 := by
    intro hzero
    have hz := congrArg (fun v : ℝ[X] => v.coeff 1) hzero
    simp [f, coeff_X_add_one_pow, hq1.ne'] at hz
  have hAB : StrictInterl (hadamardProduct f p) (hadamardProduct f q) :=
    ((StrictInterl.refl (pow_ne_zero N hlin) hf.splits).interl_hadamardProduct_of_isPFPolynomial
      hf hf hpPF hqPF hpq).toStrictInterl_of_ne hA0 hB0
  have hfX := strictInterl_self_X_mul_of_nonneg
    (pow_ne_zero N hlin) hf.splits hf.hasNonnegCoeffs
  have hAT := (hfX.interl_hadamardProduct hf.hasNonnegCoeffs
    hf.X_mul.hasNonnegCoeffs hp hq hpq).toStrictInterl_of_ne hA0 hT0
  have hsimple := hasSimpleRoots_hadamardProduct hg hqPF
    (by simp [coeff_X_add_one_pow]) hq0.ne'
  intro r hr hrE
  have hsign := eval_mul_nonneg_of_common_left hAB hAT
    (hf.hasNonnegCoeffs.hadamardProduct hp) (hf.hasNonnegCoeffs.hadamardProduct hq)
    (hf.X_mul.hasNonnegCoeffs.hadamardProduct hq) hr
  have hsum : (hadamardProduct ((X + 1) ^ (N + 1)) q).eval r =
      (hadamardProduct f q).eval r + (hadamardProduct (X * f) q).eval r := by
    rw [show (X + 1 : ℝ[X]) ^ (N + 1) = f + X * f by dsimp [f]; ring,
      hadamardProduct_add_left, eval_add]
  have hB : (hadamardProduct f q).eval r = 0 := by
    rw [hrE.eq_zero] at hsum
    nlinarith [sq_nonneg ((hadamardProduct f q).eval r)]
  have hid := congrArg (fun v : ℝ[X] => v.eval r) (hadamard_power_adjacent N q)
  change (C ((N : ℝ) + 1) * hadamardProduct f q).eval r = _ at hid
  simp only [eval_mul, eval_C, eval_sub, eval_X, hrE.eq_zero, hB, mul_zero, zero_sub] at hid
  have hr0 : r ≠ 0 := by
    intro heq
    subst r
    have hz := hrE.eq_zero
    simp [← coeff_zero_eq_eval_zero, coeff_X_add_one_pow, hq0.ne'] at hz
  exact hsimple.eval_derivative_ne_zero hrE ((mul_eq_zero.mp (by linarith :
    r * (hadamardProduct ((X + 1) ^ (N + 1)) q).derivative.eval r = 0)).resolve_left hr0)

/-- Markov's strict derivative conclusion for a degree-gap-one pair.
The existing derivative-interlacing theorem supplies the ordering; global
Wronskian positivity rules out a common derivative root. -/
theorem StrictInterl.isCoprime_derivative {f g : ℝ[X]} (h : StrictInterl f g)
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1) (hpos : f.natDegree ≠ 0)
    (hcop : IsCoprime f g) : IsCoprime f.derivative g.derivative := by
  have hs := h.hasSimpleRoots_of_isCoprime hcop
  apply isCoprime_of_no_common_real_root_of_isRealRooted
    (derivative_ne_zero.mpr hpos) (h.derivative hpos).1.2
  intro r hr hr'
  have hw := wronskian_pos_of_strictInterl_succ hg hf hdeg h
    hs.2.roots_nodup hs.1.roots_nodup (fun x hx => hcop.symm.not_isRoot_right hx) r
  rw [hr.eq_zero, hr'.eq_zero] at hw
  norm_num at hw

end RealRooted

namespace RealRooted.Hoggatt

/-- The binomial-product polynomial `F(n,m)`; its intended domain is `m ≥ 1`. -/
def polynomial (n m : ℕ) : ℝ[X] :=
  ∑ k ∈ range (n + 1), monomial k (∏ i ∈ range m, (n.choose (k + i) : ℝ))

/-- Coefficients of the Hoggatt polynomial, including the vanishing tail. -/
theorem coeff_polynomial (n : ℕ) {m : ℕ} (hm : m ≠ 0) (k : ℕ) :
    (polynomial n m).coeff k = ∏ i ∈ range m, (n.choose (k + i) : ℝ) := by
  rw [polynomial, coeff_sum_range_monomial]
  split_ifs with hk
  · rfl
  · have hz : (n.choose (k + 0) : ℝ) = 0 := by
      simp [Nat.choose_eq_zero_of_lt (by lia : n < k)]
    exact (prod_eq_zero (mem_range.mpr (by lia : 0 < m)) hz).symm

/-- Every coefficient is nonnegative. -/
theorem hasNonnegCoeffs_polynomial (n m : ℕ) :
    HasNonnegCoeffs (polynomial n m) := by
  intro k
  rw [polynomial, coeff_sum_range_monomial]
  split_ifs <;> positivity

/-- A coefficient in the support interval is positive. -/
theorem coeff_polynomial_pos {n m k : ℕ} (hm : m ≠ 0) (hk : k + m ≤ n + 1) :
    0 < (polynomial n m).coeff k := by
  rw [coeff_polynomial n hm]
  apply prod_pos
  intro i hi
  exact_mod_cast Nat.choose_pos (by simp only [mem_range] at hi; lia : k + i ≤ n)

/-- A coefficient beyond the support interval vanishes. -/
theorem coeff_polynomial_eq_zero {n m k : ℕ} (hm : m ≠ 0) (hk : n + 1 < k + m) :
    (polynomial n m).coeff k = 0 := by
  rw [coeff_polynomial n hm]
  apply prod_eq_zero (mem_range.mpr (by lia : m - 1 < m))
  simp [Nat.choose_eq_zero_of_lt (by lia : n < k + (m - 1))]

/-- The constant coefficient is positive throughout the nonzero range. -/
theorem coeff_zero_pos {n m : ℕ} (hm : m ≠ 0) (hn : m ≤ n + 1) :
    0 < (polynomial n m).coeff 0 :=
  coeff_polynomial_pos hm (by lia)

/-- Hoggatt polynomials in the nonzero range do not vanish. -/
theorem polynomial_ne_zero {n m : ℕ} (hm : m ≠ 0) (hn : m ≤ n + 1) :
    polynomial n m ≠ 0 := by
  intro h
  have hp := coeff_zero_pos hm hn
  simp [h] at hp

/-- The exact degree in the nonzero range. -/
theorem natDegree_polynomial {n m : ℕ} (hm : m ≠ 0) (hn : m ≤ n + 1) :
    (polynomial n m).natDegree = n + 1 - m := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    exact coeff_polynomial_eq_zero hm (by lia)
  · exact (coeff_polynomial_pos hm (by lia : n + 1 - m + m ≤ n + 1)).ne'

/-- The first Hoggatt family consists of powers of `X + 1`. -/
theorem polynomial_one (n : ℕ) : polynomial n 1 = (X + 1) ^ n := by
  ext k
  simp [coeff_polynomial, coeff_X_add_one_pow]

/-- The auxiliary Hadamard product `G(n+1,m+1)` in the paper. -/
def auxiliary (n m : ℕ) : ℝ[X] :=
  hadamardProduct (polynomial (n + 1) 1) (polynomial n m)

/-- The Hadamard identity defining the auxiliary polynomial, in binomial form. -/
theorem coeff_auxiliary (n : ℕ) {m : ℕ} (hm : m ≠ 0) (k : ℕ) :
    (auxiliary n m).coeff k =
      ((n + 1).choose k : ℝ) * ∏ i ∈ range m, (n.choose (k + i) : ℝ) := by
  simp [auxiliary, coeff_polynomial, hm]

/-- Differentiating the auxiliary Hadamard product raises the Hoggatt parameter. -/
theorem derivative_auxiliary (n : ℕ) {m : ℕ} (hm : m ≠ 0) :
    (auxiliary n m).derivative = C ((n : ℝ) + 1) * polynomial n (m + 1) := by
  ext k
  rw [coeff_derivative, coeff_auxiliary n hm, coeff_C_mul,
    coeff_polynomial n (by lia : m + 1 ≠ 0), prod_range_succ']
  have hc : ((n + 1).choose (k + 1) : ℝ) * (k + 1 : ℕ) =
      (n + 1 : ℕ) * (n.choose k : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq n k).symm
  simp only [Nat.add_zero]
  have heq : (fun i : ℕ => (n.choose (k + (i + 1)) : ℝ)) =
      (fun i : ℕ => (n.choose (k + 1 + i) : ℝ)) := by
    funext i
    congr 2
    lia
  rw [heq]
  push_cast at hc
  linear_combination (∏ i ∈ range m, (n.choose (k + 1 + i) : ℝ)) * hc

/-- The derivative identity for the base case `m = 2`. -/
theorem derivative_hadamard_one (n : ℕ) :
    (hadamardProduct (polynomial n 1) (polynomial (n + 1) 1)).derivative =
      C ((n : ℝ) + 1) * polynomial n 2 := by
  simpa [auxiliary, hadamardProduct_comm] using derivative_auxiliary n (m := 1) one_ne_zero

private theorem interl_polynomial_succ : ∀ m : ℕ, m ≠ 0 →
    ∀ n : ℕ, m ≤ n + 1 → StrictInterl (polynomial n m) (polynomial (n + 1) m) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      intro hm n hn
      by_cases hm0 : m = 0
      · subst m
        simpa [polynomial_one] using strictInterl_X_add_C_pow_succ (1 : ℝ) n
      · have hpow : StrictInterl (polynomial (n + 1) 1) (polynomial (n + 2) 1) := by
          simpa [polynomial_one] using strictInterl_X_add_C_pow_succ (1 : ℝ) (n + 1)
        have hprev := ih hm0 n (by lia)
        have haux : Interl (auxiliary n m) (auxiliary (n + 1) m) := by
          exact hpow.interl_hadamardProduct
            (hasNonnegCoeffs_polynomial _ _) (hasNonnegCoeffs_polynomial _ _)
            (hasNonnegCoeffs_polynomial _ _) (hasNonnegCoeffs_polynomial _ _) hprev
        have hder := haux.derivative
        rw [derivative_auxiliary n hm0, derivative_auxiliary (n + 1) hm0] at hder
        have hleft : C ((n : ℝ) + 1) * polynomial n (m + 1) ≠ 0 :=
          mul_ne_zero (C_ne_zero.mpr (by positivity)) (polynomial_ne_zero (by lia) hn)
        have hright : C (((n + 1 : ℕ) : ℝ) + 1) * polynomial (n + 1) (m + 1) ≠ 0 :=
          mul_ne_zero (C_ne_zero.mpr (by positivity))
            (polynomial_ne_zero (by lia) (by lia))
        have hstrict := hder.toStrictInterl_of_ne hleft hright
        have hscaled := (hstrict.C_mul_left (a := (n + 1 : ℝ)⁻¹) (by positivity)).C_mul_right
          (a := (n + 1 + 1 : ℝ)⁻¹) (by positivity)
        push_cast at hscaled
        simpa only [← mul_assoc, ← C_mul, inv_mul_cancel₀ (by positivity : (n : ℝ) + 1 ≠ 0),
          inv_mul_cancel₀ (by positivity : (n : ℝ) + 1 + 1 ≠ 0), C_1, one_mul] using hscaled

/-- Consecutive binomial-product polynomials interlace in the library's orientation.
The predicate permits shared roots. -/
theorem polynomial_strictInterl_succ {n m : ℕ} (hm : m ≠ 0) (hn : m ≤ n + 1) :
    StrictInterl (polynomial n m) (polynomial (n + 1) m) :=
  interl_polynomial_succ m hm n hn

/-- The degree-gap-one interlacing statement for every positive parameter. -/
theorem polynomial_interlaces {n m : ℕ} (hm : m ≠ 0) (hn : m ≤ n + 1) :
    Interlaces (polynomial n m) (polynomial (n + 1) m) := by
  apply (polynomial_strictInterl_succ hm hn).toInterlaces
  rw [natDegree_polynomial hm hn, natDegree_polynomial hm (by lia)]
  lia

/-- Real-rootedness of all nonzero binomial-product Hoggatt polynomials. -/
theorem polynomial_splits {n m : ℕ} (hm : m ≠ 0) (hn : m ≤ n + 1) :
    (polynomial n m).Splits :=
  (polynomial_strictInterl_succ hm hn).1.2

/-- Every root in the nonzero parameter range is strictly negative. -/
theorem polynomial_roots_neg {n m : ℕ} (hm : m ≠ 0) (hn : m ≤ n + 1)
    {r : ℝ} (hr : r ∈ (polynomial n m).roots) : r < 0 :=
  roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne
    (hasNonnegCoeffs_polynomial n m) (coeff_zero_pos hm hn).ne' r hr

/-- The auxiliary polynomial has the same degree as its second Hadamard factor. -/
theorem natDegree_auxiliary {n m : ℕ} (hm : m ≠ 0) (hn : m ≤ n + 1) :
    (auxiliary n m).natDegree = n + 1 - m := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (natDegree_hadamardProduct_le_right _ _).trans
      (natDegree_polynomial hm hn).le
  · rw [coeff_auxiliary n hm]
    apply mul_ne_zero
    · exact_mod_cast (Nat.choose_pos (by lia : n + 1 - m ≤ n + 1)).ne'
    · rw [← coeff_polynomial n hm]
      exact (coeff_polynomial_pos hm (by lia : n + 1 - m + m ≤ n + 1)).ne'

/-- Consecutive auxiliary polynomials interlace. -/
theorem auxiliary_strictInterl_succ {n m : ℕ} (hm : m ≠ 0) (hn : m ≤ n + 1) :
    StrictInterl (auxiliary n m) (auxiliary (n + 1) m) := by
  have hpow : StrictInterl (polynomial (n + 1) 1) (polynomial (n + 2) 1) :=
    polynomial_strictInterl_succ one_ne_zero (by lia)
  have h := hpow.interl_hadamardProduct
    (hasNonnegCoeffs_polynomial _ _) (hasNonnegCoeffs_polynomial _ _)
    (hasNonnegCoeffs_polynomial _ _) (hasNonnegCoeffs_polynomial _ _)
    (polynomial_strictInterl_succ hm hn)
  apply h.toStrictInterl_of_ne
  · intro hz
    have hc := congrArg (fun v : ℝ[X] => v.coeff 0) hz
    have hp := coeff_zero_pos hm hn
    simp only [coeff_hadamardProduct, polynomial_one, coeff_X_add_one_pow,
      Nat.choose_zero_right, Nat.cast_one, one_mul, coeff_zero] at hc
    linarith
  · intro hz
    have hc := congrArg (fun v : ℝ[X] => v.coeff 0) hz
    have hp := coeff_zero_pos hm (by lia : m ≤ n + 1 + 1)
    simp only [coeff_hadamardProduct, polynomial_one, coeff_X_add_one_pow,
      Nat.choose_zero_right, Nat.cast_one, one_mul, coeff_zero] at hc
    linarith

/-- Consecutive auxiliary polynomials have no common root, including at zero. -/
theorem auxiliary_isCoprime_succ {n m : ℕ} (hm : m ≠ 0) (hn : m ≤ n + 1) :
    IsCoprime (auxiliary n m) (auxiliary (n + 1) m) := by
  have h := auxiliary_strictInterl_succ hm hn
  apply isCoprime_of_no_common_real_root_of_isRealRooted h.1.1 h.1.2
  simpa only [auxiliary, polynomial_one, Nat.add_assoc] using
    (polynomial_strictInterl_succ hm hn).hadamardProduct_power_no_common_root
      (hasNonnegCoeffs_polynomial n m) (hasNonnegCoeffs_polynomial (n + 1) m)
      (coeff_zero_pos hm hn) (coeff_zero_pos hm (by lia))
      (coeff_polynomial_pos hm (by lia : 1 + m ≤ n + 1 + 1)) (n + 1)

/-- Consecutive Hoggatt polynomials are coprime for every `m ≥ 2`.
Together with `polynomial_interlaces`, this is strict interlacing in the
sense of Fang–Zhang–Zhao. -/
theorem polynomial_isCoprime_succ {n m : ℕ} (hm : 2 ≤ m) (hn : m ≤ n + 1) :
    IsCoprime (polynomial n m) (polynomial (n + 1) m) := by
  have hm0 : m - 1 ≠ 0 := by lia
  have hjn : m - 1 ≤ n + 1 := by lia
  have h := auxiliary_strictInterl_succ hm0 hjn
  have hnn : HasNonnegCoeffs (auxiliary n (m - 1)) :=
    (hasNonnegCoeffs_polynomial _ _).hadamardProduct (hasNonnegCoeffs_polynomial _ _)
  have hnn' : HasNonnegCoeffs (auxiliary (n + 1) (m - 1)) :=
    (hasNonnegCoeffs_polynomial _ _).hadamardProduct (hasNonnegCoeffs_polynomial _ _)
  have hd := h.isCoprime_derivative (hnn.pos_leadingCoeff h.1.1)
    (hnn'.pos_leadingCoeff h.2.1.1)
    (by rw [natDegree_auxiliary hm0 (by lia), natDegree_auxiliary hm0 hjn]; lia)
    (by rw [natDegree_auxiliary hm0 hjn]; lia) (auxiliary_isCoprime_succ hm0 hjn)
  apply isCoprime_of_no_common_real_root_of_isRealRooted
    (polynomial_ne_zero (by lia) hn) (polynomial_splits (by lia) hn)
  intro r hr hr'
  apply hd.not_isRoot_right (x := r)
  · rw [derivative_auxiliary n hm0, show m - 1 + 1 = m by lia]
    simp [Polynomial.IsRoot.def, hr.eq_zero]
  · rw [derivative_auxiliary (n + 1) hm0, show m - 1 + 1 = m by lia]
    simp [Polynomial.IsRoot.def, hr'.eq_zero]

/-- Strict interlacing, recorded as degree-gap-one interlacing and coprimality. -/
theorem polynomial_interlaces_and_isCoprime {n m : ℕ} (hm : 2 ≤ m) (hn : m ≤ n + 1) :
    Interlaces (polynomial n m) (polynomial (n + 1) m) ∧
      IsCoprime (polynomial n m) (polynomial (n + 1) m) :=
  ⟨polynomial_interlaces (by lia) hn, polynomial_isCoprime_succ hm hn⟩

/-- The indexing of the strict comparison stated in Fang–Zhang–Zhao, §2. -/
theorem polynomial_pred_interlaces {n m : ℕ} (hm : 2 ≤ m) (hn : m ≤ n) :
    Interlaces (polynomial (n - 1) m) (polynomial n m) ∧
      IsCoprime (polynomial (n - 1) m) (polynomial n m) := by
  simpa only [Nat.sub_add_cancel (by lia : 1 ≤ n)] using
    polynomial_interlaces_and_isCoprime hm (by lia : m ≤ n - 1 + 1)

/-- Every Hoggatt polynomial with parameter at least two has simple roots. -/
theorem hasSimpleRoots_polynomial {n m : ℕ} (hm : 2 ≤ m) (hn : m ≤ n + 1) :
    HasSimpleRoots (polynomial n m) :=
  ((polynomial_strictInterl_succ (by lia) hn).hasSimpleRoots_of_isCoprime
    (polynomial_isCoprime_succ hm hn)).1

/-- The normalized Hoggatt polynomial `H_n^[m]`, with constant coefficient one.
MacMahon's formula identifies its coefficients with plane partitions in a
`k × (n-1-k) × m` box, for `n,m ≥ 1`. -/
def normalized (n m : ℕ) : ℝ[X] :=
  C ((polynomial (n + m - 2) m).coeff 0)⁻¹ * polynomial (n + m - 2) m

/-- The normalization denominator is the product in the paper. -/
theorem normalized_eq (n : ℕ) {m : ℕ} (hm : m ≠ 0) :
    normalized n m =
      C (∏ i ∈ range m, ((n + m - 2).choose i : ℝ))⁻¹ * polynomial (n + m - 2) m := by
  simp [normalized, coeff_polynomial, hm]

/-- Normalized Hoggatt polynomials have constant coefficient one. -/
theorem coeff_zero_normalized {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    (normalized n m).coeff 0 = 1 := by
  rw [normalized, coeff_C_mul, inv_mul_cancel₀ (coeff_zero_pos hm (by lia)).ne']

/-- The `m = 1` normalized family is the generalized Sturm sequence of binomial powers. -/
theorem normalized_one (n : ℕ) :
    normalized n 1 = (X + 1) ^ (n - 1) := by
  simp [normalized, polynomial_one, coeff_X_add_one_pow, show n + 1 - 2 = n - 1 by lia]

/-- Real-rootedness of every normalized Hoggatt polynomial (Dilks). -/
theorem normalized_splits {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    (normalized n m).Splits :=
  (polynomial_splits hm (by lia : m ≤ n + m - 2 + 1)).C_mul _

/-- Consecutive normalized Hoggatt polynomials interlace, including `m = 1`. -/
theorem normalized_interlaces {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    Interlaces (normalized n m) (normalized (n + 1) m) := by
  have hi : n + 1 + m - 2 = n + m - 2 + 1 := by lia
  have h := (polynomial_strictInterl_succ hm (by lia : m ≤ n + m - 2 + 1)).C_mul_left
    (inv_ne_zero (coeff_zero_pos hm (by lia : m ≤ n + m - 2 + 1)).ne')
  have h' := h.C_mul_right (inv_ne_zero (coeff_zero_pos hm (by lia :
    m ≤ n + m - 2 + 1 + 1)).ne')
  change Interlaces (C _ * _) (C _ * _)
  rw [hi]
  apply h'.toInterlaces
  rw [natDegree_C_mul (inv_ne_zero (coeff_zero_pos hm (by lia)).ne'),
    natDegree_C_mul (inv_ne_zero (coeff_zero_pos hm (by lia)).ne'),
    natDegree_polynomial hm (by lia), natDegree_polynomial hm (by lia)]
  lia

/-- Normalized Hoggatt rows strictly interlace for `m ≥ 2` (Fang–Zhang–Zhao). -/
theorem normalized_interlaces_and_isCoprime {n m : ℕ} (hn : n ≠ 0) (hm : 2 ≤ m) :
    Interlaces (normalized n m) (normalized (n + 1) m) ∧
      IsCoprime (normalized n m) (normalized (n + 1) m) := by
  have hm0 : m ≠ 0 := by lia
  have hi : n + 1 + m - 2 = n + m - 2 + 1 := by lia
  have h := normalized_interlaces hn hm0
  refine ⟨h, isCoprime_of_no_common_real_root_of_isRealRooted
    h.toStrictInterl.1.1 h.toStrictInterl.1.2 ?_⟩
  intro r hr hr'
  have hp : (polynomial (n + m - 2) m).IsRoot r := by
    simpa [normalized, Polynomial.IsRoot.def,
      inv_ne_zero (coeff_zero_pos hm0 (by lia : m ≤ n + m - 2 + 1)).ne'] using hr
  have hq : (polynomial (n + m - 2 + 1) m).IsRoot r := by
    simpa [normalized, hi, Polynomial.IsRoot.def,
      inv_ne_zero (coeff_zero_pos hm0 (by lia : m ≤ n + m - 2 + 1 + 1)).ne'] using hr'
  exact (polynomial_isCoprime_succ hm (by lia)).not_isRoot_right hp hq

/-- The Baxter specialization is a strict Sturm sequence. -/
theorem baxter_interlaces {n : ℕ} (hn : n ≠ 0) :
    Interlaces (normalized n 3) (normalized (n + 1) 3) ∧
      IsCoprime (normalized n 3) (normalized (n + 1) 3) :=
  normalized_interlaces_and_isCoprime hn (by norm_num)

/-- The three-factor specialization in the binomial-sum presentation of the
existing A056939 Baxter model. This fixes its index shift and normalization. -/
theorem normalized_three_eq_binomial_sum (n : ℕ) :
    normalized (n + 1) 3 = C (2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2)) *
      ∑ k ∈ range (n + 1), monomial k
        ((Nat.choose (n + 2) k : ℝ) * Nat.choose (n + 2) (k + 1) *
          Nat.choose (n + 2) (k + 2)) := by
  have hd : (polynomial (n + 2) 3).coeff 0 =
      ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 / 2 := by
    simp [coeff_polynomial, prod_range_succ, Nat.cast_choose_two]
    ring
  have hs : ((polynomial (n + 2) 3).coeff 0)⁻¹ =
      2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2) := by
    rw [hd]
    field_simp
  rw [normalized, show n + 1 + 3 - 2 = n + 2 by lia, hs]
  congr 1
  ext k
  rw [coeff_sum_range_monomial]
  by_cases hk : k < n + 1
  · rw [ite_eq_left hk, coeff_polynomial (n + 2) (by norm_num : 3 ≠ 0)]
    simp [prod_range_succ]
  · rw [ite_eq_right hk, coeff_polynomial_eq_zero (by norm_num : 3 ≠ 0) (by lia)]

end RealRooted.Hoggatt
