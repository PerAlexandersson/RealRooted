import RealRooted.HermiteBiehler.Basic
import RealRooted.NewtonAux
import RealRooted.Hadamard.SchurSzegoMultiplicity
import RealRooted.Mathlib.Algebra.Polynomial.Derivative

/-!
# Multiple roots of a Schur–Szegő composition are forced

Let `P` be real-rooted and `Q` have only negative roots, both of degree `n`.  Kostov and Shapiro
showed that `−ab` is a root of `P *_n Q` of multiplicity exactly `m_P(a) + m_Q(b) − n` whenever
this is nonnegative (`rootMultiplicity_schurSzegoComp`).  Here we prove the converse
(Kostov–Shapiro, C. R. Acad. Sci. Paris 343 (2006), Theorem 6(ii)): every nonzero root of
`P *_n Q` of multiplicity at least two is such a forced product
(`exists_forced_factors_of_rootMultiplicity_schurSzegoComp`), so all other nonzero roots are
simple (`rootMultiplicity_le_one_of_not_forced_schurSzegoComp`).

The proof follows the paper's perturbation idea and was found by Aristotle (Harmonic): roots of
multiplicity at least three reduce to derivatives, and for a double root one perturbs `P` by a
root-deleted factor `R_a` (`P + i R_a` is upper-half-plane stable), shows that the composition of
`R_a` with `Q` vanishes at the root, and concludes with Lagrange interpolation and the
multiplicity bound.
-/

@[expose] public section

open Polynomial Finset ComplexConjugate

namespace SchurSzegoAristotle

/-- Fixed-degree Schur–Szegő composition with a complex first argument. -/
private noncomputable def compC (n : ℕ) (P : ℂ[X]) (Q : ℝ[X]) : ℂ[X] :=
  ∑ k ∈ range (n + 1), monomial k (P.coeff k * (Q.coeff k : ℂ) / (n.choose k : ℂ))

private theorem eval_compC (n : ℕ) (P : ℂ[X]) (Q : ℝ[X]) (x : ℂ) :
    (compC n P Q).eval x =
      ∑ k ∈ range (n + 1), P.coeff k * (Q.coeff k : ℂ) / (n.choose k : ℂ) * x ^ k := by
  simp [compC, eval_finsetSum, eval_monomial]

/-- Polar derivative `N P + (ζ - X) P'`. -/
private noncomputable def polarDeriv (N : ℕ) (ζ : ℂ) (P : ℂ[X]) : ℂ[X] :=
  C (N : ℂ) * P + (C ζ - X) * derivative P

private theorem coeff_X_mul_derivative (P : ℂ[X]) (k : ℕ) :
    (X * derivative P).coeff k = (k : ℂ) * P.coeff k := by
  rcases k with _ | k
  · simp
  · rw [coeff_X_mul, coeff_derivative]; push_cast; ring

private theorem coeff_polarDeriv (N : ℕ) (ζ : ℂ) (P : ℂ[X]) (k : ℕ) :
    (polarDeriv N ζ P).coeff k =
      ((N : ℂ) - k) * P.coeff k + ζ * ((k : ℂ) + 1) * P.coeff (k + 1) := by
  simp only [polarDeriv, coeff_add, coeff_C_mul, sub_mul, coeff_sub,
    coeff_X_mul_derivative, coeff_derivative]
  ring

private theorem natDegree_polarDeriv_le {n : ℕ} (ζ : ℂ) {P : ℂ[X]} (hP : P.natDegree ≤ n + 1) :
    (polarDeriv (n + 1) ζ P).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  have hk' : n + 1 ≤ k := by exact_mod_cast hk
  rw [coeff_polarDeriv, coeff_eq_zero_of_natDegree_lt (show P.natDegree < k + 1 by lia)]
  rcases Nat.eq_or_lt_of_le hk' with h | h
  · subst h; push_cast; ring
  · rw [coeff_eq_zero_of_natDegree_lt (show P.natDegree < k by lia)]; ring

/-- The basic inequality for a single root in the closed lower half-plane. -/
private theorem term_ineq {z τ : ℂ} (hτ : τ.im ≤ 0) :
    z.im * Complex.normSq (1 / (z - τ)) ≤ -(1 / (z - τ)).im := by
  set u := z - τ with hu
  by_cases h0 : u = 0
  · simp [h0]
  have hpos : 0 < Complex.normSq u := Complex.normSq_pos.mpr h0
  have him : u.im = z.im - τ.im := by simp [hu]
  rw [one_div, Complex.normSq_inv, Complex.inv_im, neg_div, neg_neg, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (by linarith) hpos.le

/-- The key inequality for the logarithmic derivative. -/
private theorem logDeriv_ineq (s : Multiset ℂ) {z : ℂ} (hz : 0 < z.im) (hs : ∀ τ ∈ s, τ.im ≤ 0) :
    z.im * Complex.normSq (s.map fun τ => 1 / (z - τ)).sum ≤
      -(Multiset.card s : ℝ) * ((s.map fun τ => 1 / (z - τ)).sum).im := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons τ s ih =>
    have ih' := ih fun t ht => hs t (Multiset.mem_cons_of_mem ht)
    have hτ := term_ineq (z := z) (hs τ (Multiset.mem_cons_self τ s))
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    set w := 1 / (z - τ)
    set S := (s.map fun τ => 1 / (z - τ)).sum
    set d : ℝ := (Multiset.card s : ℝ)
    have hd : 0 ≤ d := Nat.cast_nonneg _
    rw [Complex.normSq_apply] at hτ ih' ⊢
    simp only [Complex.add_re, Complex.add_im] at ⊢
    push_cast
    have key : 0 ≤ (d * w.re - S.re) ^ 2 + (d * w.im - S.im) ^ 2 := by positivity
    rcases hd.lt_or_eq with hd | hd
    · have : d * (z.im * ((w.re + S.re) * (w.re + S.re) + (w.im + S.im) * (w.im + S.im))) ≤
          d * (-(d + 1) * (w.im + S.im)) := by
        nlinarith [hz.le, mul_le_mul_of_nonneg_left hτ (by linarith : (0:ℝ) ≤ d + 1),
          mul_le_mul_of_nonneg_left hτ hd.le]
      exact le_of_mul_le_mul_left this hd
    · have hc : ((Multiset.card s : ℕ) : ℝ) = 0 := hd.symm
      rw [← hd] at ih'
      rw [hc]
      have hS : S.re * S.re + S.im * S.im = 0 := by
        have h1 : 0 ≤ S.re * S.re + S.im * S.im := by
          nlinarith [mul_self_nonneg S.re, mul_self_nonneg S.im]
        have h2 : z.im * (S.re * S.re + S.im * S.im) ≤ 0 := by linarith
        have := (mul_nonpos_iff.mp h2)
        rcases this with ⟨h3, h4⟩ | ⟨h3, _⟩
        · linarith
        · linarith
      have hre : S.re = 0 := by nlinarith [sq_nonneg S.re, sq_nonneg S.im]
      have him : S.im = 0 := by nlinarith [sq_nonneg S.re, sq_nonneg S.im]
      rw [hre, him]; linarith

/-- Laguerre's theorem on polar derivatives for the upper half-plane. -/
private theorem polarDeriv_ne_zero {N : ℕ} (hN : 1 ≤ N) {P : ℂ[X]} (hPdeg : P.natDegree ≤ N)
    (hP : ∀ z : ℂ, 0 < z.im → P.eval z ≠ 0) {ζ : ℂ} (hζ : 0 < ζ.im) {z : ℂ} (hz : 0 < z.im) :
    (polarDeriv N ζ P).eval z ≠ 0 := by
  have hP0 : P ≠ 0 := by
    rintro rfl; exact hP Complex.I (by simp) (by simp)
  have hs : P.Splits := IsAlgClosed.splits P
  have hroots : ∀ τ ∈ P.roots, τ.im ≤ 0 := by
    intro τ hτ; by_contra h; push Not at h; exact hP τ h ((mem_roots hP0).mp hτ)
  have hPz : P.eval z ≠ 0 := hP z hz
  set S := (P.roots.map fun τ => 1 / (z - τ)).sum with hSdef
  have hS : P.derivative.eval z = P.eval z * S := hs.eval_derivative_eq_eval_mul_sum hPz
  have hineq := logDeriv_ineq P.roots hz hroots
  rw [← hSdef] at hineq
  have hcard : (Multiset.card P.roots : ℝ) ≤ N := by
    have := card_roots' P; exact_mod_cast this.trans hPdeg
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  intro h
  rw [polarDeriv, eval_add, eval_mul, eval_C, eval_mul, eval_sub, eval_C, eval_X, hS] at h
  have h2 : (N : ℂ) + (ζ - z) * S = 0 := by
    have : P.eval z * ((N : ℂ) + (ζ - z) * S) = 0 := by rw [← h]; ring
    exact (mul_eq_zero.mp this).resolve_left hPz
  have hre := congrArg Complex.re h2
  have him := congrArg Complex.im h2
  simp only [Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.sub_re,
    Complex.sub_im, Complex.zero_re, Complex.add_im, Complex.natCast_im, Complex.mul_im,
    Complex.zero_im, zero_add] at hre him
  rw [Complex.normSq_apply] at hineq
  have key : (ζ.im - z.im) * (S.re * S.re + S.im * S.im) = N * S.im := by
    linear_combination S.re * him - S.im * hre
  have hS0 : 0 < S.re * S.re + S.im * S.im := by
    rcases (add_nonneg (mul_self_nonneg S.re) (mul_self_nonneg S.im)).lt_or_eq with h3 | h3
    · exact h3
    · exfalso
      have e1 : S.re = 0 := by nlinarith [mul_self_nonneg S.re, mul_self_nonneg S.im]
      have e2 : S.im = 0 := by nlinarith [mul_self_nonneg S.re, mul_self_nonneg S.im]
      rw [e1, e2] at hre; linarith
  have hcard0 : (0 : ℝ) ≤ Multiset.card P.roots := Nat.cast_nonneg _
  have hSim : S.im ≤ 0 := by
    by_contra h4; push Not at h4
    nlinarith [mul_pos hz hS0]
  have h5 : (N : ℝ) * S.im ≤ (Multiset.card P.roots : ℝ) * S.im :=
    mul_le_mul_of_nonpos_right hcard hSim
  nlinarith [mul_pos hζ hS0]

/-- The pointwise recursion for the composition. -/
private theorem compC_recursion (n : ℕ) (P : ℂ[X]) (Q1 : ℝ[X])
    (hQ1 : Q1.natDegree ≤ n) {β : ℝ} (hβ : β ≠ 0) (x : ℂ) :
    ((n : ℂ) + 1) * (compC (n + 1) P ((X + C β) * Q1)).eval x =
      (β : ℂ) * (compC n (polarDeriv (n + 1) (x / β) P) Q1).eval x := by
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hch : ∀ k ≤ n, ((n.choose k : ℕ) : ℂ) ≠ 0 := fun k hk => by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hch1 : ∀ k ≤ n + 1, (((n + 1).choose k : ℕ) : ℂ) ≠ 0 := fun k hk => by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hid1 : ∀ k ≤ n, ((n : ℂ) + 1) * ((n.choose k : ℕ) : ℂ) =
      (((n : ℂ) + 1) - k) * (((n + 1).choose k : ℕ) : ℂ) := by
    intro k hk
    have h := Nat.choose_mul_succ_eq n k
    have h' : ((n.choose k * (n + 1) : ℕ) : ℂ) = (((n + 1).choose k * (n + 1 - k) : ℕ) : ℂ) := by
      rw [h]
    push_cast [Nat.cast_sub (show k ≤ n + 1 by lia)] at h'
    linear_combination h'
  have hid2 : ∀ k ≤ n, ((n : ℂ) + 1) * ((n.choose k : ℕ) : ℂ) =
      ((k : ℂ) + 1) * (((n + 1).choose (k + 1) : ℕ) : ℂ) := by
    intro k hk
    have h := Nat.add_one_mul_choose_eq n k
    have h' : (((n + 1) * n.choose k : ℕ) : ℂ) = (((n + 1).choose (k + 1) * (k + 1) : ℕ) : ℂ) := by
      rw [h]
    push_cast at h'
    linear_combination h'
  rw [eval_compC, eval_compC]
  have hQ : ∀ k, ((((X + C β) * Q1).coeff k : ℝ) : ℂ) =
      (((X * Q1).coeff k : ℝ) : ℂ) + (β : ℂ) * ((Q1.coeff k : ℝ) : ℂ) := by
    intro k; rw [add_mul, coeff_add, coeff_C_mul]; push_cast; ring
  have hL : ∑ k ∈ range (n + 1 + 1), P.coeff k * ((((X + C β) * Q1).coeff k : ℝ) : ℂ) /
      (((n + 1).choose k : ℕ) : ℂ) * x ^ k =
      ∑ k ∈ range (n + 1 + 1), P.coeff k * (((X * Q1).coeff k : ℝ) : ℂ) /
        (((n + 1).choose k : ℕ) : ℂ) * x ^ k +
      ∑ k ∈ range (n + 1 + 1), (β : ℂ) * P.coeff k * ((Q1.coeff k : ℝ) : ℂ) /
        (((n + 1).choose k : ℕ) : ℂ) * x ^ k := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun k _ => ?_; rw [hQ]; ring
  have hR : (β : ℂ) * ∑ k ∈ range (n + 1), (polarDeriv (n + 1) (x / β) P).coeff k *
      ((Q1.coeff k : ℝ) : ℂ) / ((n.choose k : ℕ) : ℂ) * x ^ k =
      ∑ k ∈ range (n + 1), (β : ℂ) * (((n : ℂ) + 1) - k) * P.coeff k * ((Q1.coeff k : ℝ) : ℂ) /
        ((n.choose k : ℕ) : ℂ) * x ^ k +
      ∑ k ∈ range (n + 1), x * ((k : ℂ) + 1) * P.coeff (k + 1) * ((Q1.coeff k : ℝ) : ℂ) /
        ((n.choose k : ℕ) : ℂ) * x ^ k := by
    rw [mul_sum, ← sum_add_distrib]; refine sum_congr rfl fun k _ => ?_
    rw [coeff_polarDeriv]; push_cast; field_simp
  rw [hL, hR, mul_add, add_comm]
  congr 1
  · -- the part with `β * Q1`
    rw [mul_sum, sum_range_succ, coeff_eq_zero_of_natDegree_lt (show Q1.natDegree < n + 1 by lia)]
    simp only [Complex.ofReal_zero, mul_zero, zero_div, zero_mul, add_zero]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := by simp at hk; lia
    have e : ((n : ℂ) + 1) / (((n + 1).choose k : ℕ) : ℂ) =
        ((n : ℂ) + 1 - k) / ((n.choose k : ℕ) : ℂ) := by
      rw [div_eq_div_iff (hch1 k (by lia)) (hch k hk')]; linear_combination hid1 k hk'
    calc ((n : ℂ) + 1) * ((β : ℂ) * P.coeff k * ((Q1.coeff k : ℝ) : ℂ) /
          (((n + 1).choose k : ℕ) : ℂ) * x ^ k)
        = (β : ℂ) * P.coeff k * ((Q1.coeff k : ℝ) : ℂ) * x ^ k *
          (((n : ℂ) + 1) / (((n + 1).choose k : ℕ) : ℂ)) := by ring
      _ = _ := by rw [e]; ring
  · -- the part with `X * Q1`
    rw [mul_sum, sum_range_succ']
    simp only [coeff_X_mul_zero, Complex.ofReal_zero, mul_zero, zero_div, zero_mul, add_zero]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := by simp at hk; lia
    rw [coeff_X_mul]
    have e : ((n : ℂ) + 1) / (((n + 1).choose (k + 1) : ℕ) : ℂ) =
        ((k : ℂ) + 1) / ((n.choose k : ℕ) : ℂ) := by
      rw [div_eq_div_iff (hch1 (k + 1) (by lia)) (hch k hk')]; linear_combination hid2 k hk'
    calc ((n : ℂ) + 1) * (P.coeff (k + 1) * ((Q1.coeff k : ℝ) : ℂ) /
          (((n + 1).choose (k + 1) : ℕ) : ℂ) * x ^ (k + 1))
        = x * P.coeff (k + 1) * ((Q1.coeff k : ℝ) : ℂ) * x ^ k *
          (((n : ℂ) + 1) / (((n + 1).choose (k + 1) : ℕ) : ℂ)) := by ring
      _ = _ := by rw [e]; ring

/-- Stability of the Schur–Szegő composition. -/
private theorem compC_ne_zero : ∀ (n : ℕ) (Q : ℝ[X]), Q ≠ 0 → Q.natDegree = n → Q.Splits →
    (∀ b ∈ Q.roots, b < 0) → ∀ P : ℂ[X], P.natDegree ≤ n →
    (∀ z : ℂ, 0 < z.im → P.eval z ≠ 0) → ∀ x : ℂ, 0 < x.im → (compC n P Q).eval x ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro Q hQ0 hQn _ _ P hP hPH x hx
    have hP0 : P.coeff 0 ≠ 0 := by
      have := hPH Complex.I (by simp)
      rwa [eq_C_of_natDegree_le_zero hP, eval_C] at this
    have hQc : Q.coeff 0 ≠ 0 := by
      intro h; apply hQ0; rw [eq_C_of_natDegree_eq_zero hQn, h, C_0]
    rw [eval_compC]; simp [hP0, hQc]
  | succ n ih =>
    intro Q hQ0 hQn hQs hneg P hP hPH x hx
    have hcard : Q.roots.card = n + 1 := by rw [← hQn]; exact hQs.natDegree_eq_card_roots.symm
    obtain ⟨b, hb⟩ : ∃ b, b ∈ Q.roots := Multiset.card_pos_iff_exists_mem.mp (by lia)
    have hbneg := hneg b hb
    set Q1 := Q /ₘ (X - C b) with hQ1def
    have hQeq : (X - C b) * Q1 = Q := mul_divByMonic_eq_iff_isRoot.mpr (isRoot_of_mem_roots hb)
    have hQ10 : Q1 ≠ 0 := by
      intro h; rw [h, mul_zero] at hQeq; exact hQ0 hQeq.symm
    have hQ1n : Q1.natDegree = n := by
      have := natDegree_mul (X_sub_C_ne_zero b) hQ10
      rw [hQeq, natDegree_X_sub_C, hQn] at this; lia
    have hQ1s : Q1.Splits := Splits.of_dvd hQs hQ0 ⟨X - C b, by rw [mul_comm]; exact hQeq.symm⟩
    have hQ1neg : ∀ c ∈ Q1.roots, c < 0 := by
      intro c hc; apply hneg
      rw [← hQeq, roots_mul (by rw [hQeq]; exact hQ0)]
      exact Multiset.mem_add.mpr (Or.inr hc)
    have hβ : 0 < -b := by linarith
    have hXb : X + C (-b) = X - C b := by rw [C_neg, ← sub_eq_add_neg]
    have hrec := compC_recursion n P Q1 hQ1n.le hβ.ne' x
    rw [hXb, hQeq] at hrec
    have hζ : 0 < (x / ((-b : ℝ) : ℂ)).im := by
      rw [Complex.div_ofReal_im]; positivity
    have hpd : ∀ z : ℂ, 0 < z.im → (polarDeriv (n + 1) (x / ((-b : ℝ) : ℂ)) P).eval z ≠ 0 :=
      fun z hz => polarDeriv_ne_zero (N := n + 1) (by lia) hP hPH hζ hz
    have hne := ih Q1 hQ10 hQ1n hQ1s hQ1neg (polarDeriv (n + 1) (x / ((-b : ℝ) : ℂ)) P)
      (natDegree_polarDeriv_le _ hP) hpd x hx
    intro h0
    push_cast at hrec
    rw [h0, mul_zero] at hrec
    have hb' : (-(b : ℂ)) ≠ 0 := by
      rw [neg_ne_zero]; exact_mod_cast hbneg.ne
    push_cast at hne
    exact hne ((mul_eq_zero.mp hrec.symm).resolve_left hb')

private theorem hb_prod (s : Multiset ℂ) (hs : ∀ τ ∈ s, τ.im ≤ 0) (x : ℝ) :
    ((s.map fun τ => X - C τ).prod.derivative.eval (x : ℂ) *
      conj ((s.map fun τ => X - C τ).prod.eval (x : ℂ))).im ≤ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons τ s ih =>
    have ih' := ih fun t ht => hs t (Multiset.mem_cons_of_mem ht)
    have hτ := hs τ (Multiset.mem_cons_self τ s)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    set G := (s.map fun τ => X - C τ).prod
    have e : ((X - C τ) * G).derivative.eval (x : ℂ) * conj (((X - C τ) * G).eval (x : ℂ)) =
        (Complex.normSq (G.eval (x : ℂ)) : ℂ) * conj ((x : ℂ) - τ) +
          (Complex.normSq ((x : ℂ) - τ) : ℂ) * (G.derivative.eval (x : ℂ) *
            conj (G.eval (x : ℂ))) := by
      rw [← Complex.mul_conj, ← Complex.mul_conj]
      simp only [derivative_mul, derivative_X, derivative_C, sub_zero, one_mul,
        eval_add, eval_mul, eval_sub, eval_X, eval_C, map_mul, map_sub]
      ring
    rw [e, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul, Complex.conj_im,
      Complex.sub_im, Complex.ofReal_im]
    have h1 := Complex.normSq_nonneg (G.eval (x : ℂ))
    have h2 := Complex.normSq_nonneg ((x : ℂ) - τ)
    nlinarith [mul_nonneg h2 (neg_nonneg.mpr ih')]

/-- Hermite–Biehler type inequality on the real line. -/
private theorem hb_ineq {F : ℂ[X]} (hF : ∀ z : ℂ, 0 < z.im → F.eval z ≠ 0) (x : ℝ) :
    (F.derivative.eval (x : ℂ) * conj (F.eval (x : ℂ))).im ≤ 0 := by
  have hF0 : F ≠ 0 := by
    rintro rfl; exact hF Complex.I (by simp) (by simp)
  have hs : F.Splits := IsAlgClosed.splits F
  have hroots : ∀ τ ∈ F.roots, τ.im ≤ 0 := by
    intro τ hτ; by_contra h; push Not at h; exact hF τ h ((mem_roots hF0).mp hτ)
  have hprod := hb_prod F.roots hroots x
  rw [hs.eq_prod_roots]
  set G := (F.roots.map fun τ => X - C τ).prod
  have e : (C F.leadingCoeff * G).derivative.eval (x : ℂ) *
      conj ((C F.leadingCoeff * G).eval (x : ℂ)) =
      (Complex.normSq F.leadingCoeff : ℂ) * (G.derivative.eval (x : ℂ) *
        conj (G.eval (x : ℂ))) := by
    rw [← Complex.mul_conj]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C, map_mul]
    ring
  rw [e, Complex.im_ofReal_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hprod

end SchurSzegoAristotle

/-!
## Elementary facts about real-rooted polynomials

Rolle's theorem for split real polynomials, the Laguerre inequality, a "gap lemma" for
coefficients of real-rooted polynomials and stability of splitting under `reflect`.
-/

@[expose] public section

open Polynomial

namespace SchurSzegoAristotle

/-- The derivative of a split real polynomial splits (Rolle). -/
private theorem splits_derivative_real {p : ℝ[X]} (hp : p.Splits) : p.derivative.Splits := by
  rw [splits_iff_card_roots] at hp ⊢
  have h1 := card_roots_le_derivative p
  have h2 : (derivative p).roots.card ≤ (derivative p).natDegree := card_roots' _
  have h3 : (derivative p).natDegree ≤ p.natDegree - 1 := natDegree_derivative_le p
  lia

private theorem splits_iterate_derivative_real {p : ℝ[X]} (hp : p.Splits) (k : ℕ) :
    (derivative^[k] p).Splits := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact splits_derivative_real ih

/-- Laguerre's inequality for products of linear factors. -/
private theorem laguerre_prod (s : Multiset ℝ) (x : ℝ) :
    0 ≤ ((s.map fun a => X - C a).prod.derivative.eval x) ^ 2 -
        (s.map fun a => X - C a).prod.eval x *
          (s.map fun a => X - C a).prod.derivative.derivative.eval x ∧
    (s ≠ 0 → (s.map fun a => X - C a).prod.eval x ≠ 0 →
      0 < ((s.map fun a => X - C a).prod.derivative.eval x) ^ 2 -
        (s.map fun a => X - C a).prod.eval x *
          (s.map fun a => X - C a).prod.derivative.derivative.eval x) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    obtain ⟨ih1, -⟩ := ih
    set G := (s.map fun a => X - C a).prod with hG
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [← hG]
    have key : ((((X - C a) * G).derivative.eval x) ^ 2 -
        ((X - C a) * G).eval x * ((X - C a) * G).derivative.derivative.eval x) =
        (G.eval x) ^ 2 + (x - a) ^ 2 * ((G.derivative.eval x) ^ 2 -
          G.eval x * G.derivative.derivative.eval x) := by
      simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_C,
        sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C]
      ring
    rw [key]
    refine ⟨by positivity, fun _ hx => ?_⟩
    have hGx : G.eval x ≠ 0 := by
      intro h; apply hx; simp [h]
    have : 0 < (G.eval x) ^ 2 := by positivity
    nlinarith [sq_nonneg (x - a)]

/-- Laguerre's inequality for split real polynomials. -/
private theorem laguerre_ineq {p : ℝ[X]} (hp : p.Splits) (x : ℝ) :
    0 ≤ (p.derivative.eval x) ^ 2 - p.eval x * p.derivative.derivative.eval x := by
  rw [hp.eq_prod_roots]
  have := (laguerre_prod p.roots x).1
  set F := (p.roots.map fun a => X - C a).prod
  have e : ((C p.leadingCoeff * F).derivative.eval x) ^ 2 -
      (C p.leadingCoeff * F).eval x * (C p.leadingCoeff * F).derivative.derivative.eval x =
      p.leadingCoeff ^ 2 * ((F.derivative.eval x) ^ 2 - F.eval x *
        F.derivative.derivative.eval x) := by
    simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C]
    ring
  rw [e]; positivity

/-- If a split real polynomial of positive degree has `p'(x) = p''(x) = 0`, then `p(x) = 0`. -/
private theorem eval_eq_zero_of_derivs {p : ℝ[X]} (hp : p.Splits) (hdeg : 0 < p.natDegree) {x : ℝ}
    (h1 : p.derivative.eval x = 0) (h2 : p.derivative.derivative.eval x = 0) :
    p.eval x = 0 := by
  by_contra hx
  have hroots : p.roots ≠ 0 := by
    intro h
    have := hp.natDegree_eq_card_roots
    rw [h] at this; simp at this; lia
  obtain ⟨c, F, hpF, hFdef⟩ : ∃ c F, p = C c * F ∧ F = (p.roots.map fun a => X - C a).prod :=
    ⟨_, _, hp.eq_prod_roots, rfl⟩
  have hFx : F.eval x ≠ 0 := by
    intro h; apply hx; rw [hpF]; simp [h]
  have hstrict := (laguerre_prod p.roots x).2 hroots (hFdef ▸ hFx)
  rw [← hFdef] at hstrict
  have hc : c ≠ 0 := by rintro rfl; apply hx; rw [hpF]; simp
  have e : (p.derivative.eval x) ^ 2 - p.eval x * p.derivative.derivative.eval x =
      c ^ 2 * ((F.derivative.eval x) ^ 2 - F.eval x *
        F.derivative.derivative.eval x) := by
    rw [hpF]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C]
    ring
  rw [h1, h2] at e
  have : 0 < c ^ 2 * ((F.derivative.eval x) ^ 2 - F.eval x *
        F.derivative.derivative.eval x) := by positivity
  linarith

/-- Coefficients of iterated derivatives. -/
private theorem coeff_iterate_derivative_real (p : ℝ[X]) (k m : ℕ) :
    (derivative^[k] p).coeff m = ((m + k).descFactorial k : ℝ) * p.coeff (m + k) := by
  rw [coeff_iterate_derivative]; simp [nsmul_eq_mul]

/-- Gap lemma: if a real-rooted polynomial has two consecutive vanishing coefficients
below its degree, then all lower coefficients vanish. -/
private theorem gap_lemma {p : ℝ[X]} (hp : p.Splits) :
    ∀ k : ℕ, k + 1 < p.natDegree → p.coeff k = 0 → p.coeff (k + 1) = 0 →
      ∀ j ≤ k + 1, p.coeff j = 0 := by
  intro k
  induction k with
  | zero =>
    intro _ h0 h1 j hj
    interval_cases j <;> assumption
  | succ k ih =>
    intro hk h0 h1 j hj
    -- show coeff k = 0 using derivatives of order k
    have hck : p.coeff k = 0 := by
      set h := derivative^[k] p with hh
      have hs : h.Splits := splits_iterate_derivative_real hp k
      have hdeg : 0 < h.natDegree := by
        have hc : h.coeff (p.natDegree - k) ≠ 0 := by
          rw [hh, coeff_iterate_derivative_real, Nat.sub_add_cancel (by lia)]
          refine mul_ne_zero ?_ ?_
          · exact_mod_cast (Nat.descFactorial_pos.mpr (by lia)).ne'
          · rw [← leadingCoeff]; intro h0
            rw [leadingCoeff_eq_zero] at h0; subst h0; simp at hk
        have := le_natDegree_of_ne_zero hc; lia
      have e0 : h.eval 0 = (k.descFactorial k : ℝ) * p.coeff k := by
        rw [← coeff_zero_eq_eval_zero, hh, coeff_iterate_derivative_real]; simp
      have e1 : h.derivative.eval 0 = 0 := by
        rw [← coeff_zero_eq_eval_zero, coeff_derivative, hh, coeff_iterate_derivative_real]
        simp only [zero_add, Nat.cast_zero]
        rw [show 1 + k = k + 1 by ring, h0]; ring
      have e2 : h.derivative.derivative.eval 0 = 0 := by
        rw [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_derivative, hh,
          coeff_iterate_derivative_real]
        rw [show 0 + 1 + 1 + k = k + 1 + 1 by ring, h1]; ring
      have := eval_eq_zero_of_derivs hs hdeg e1 e2
      rw [e0] at this
      have hne : (k.descFactorial k : ℝ) ≠ 0 := by
        rw [Nat.descFactorial_self]; exact_mod_cast (Nat.factorial_pos k).ne'
      exact (mul_eq_zero.mp this).resolve_left hne
    rcases Nat.lt_or_ge j (k + 2) with hj' | hj'
    · exact ih (by lia) hck h0 j (by lia)
    · have : j = k + 2 := by lia
      subst this; exact h1

private theorem natDegree_reflect_one_le (a : ℝ) : (reflect 1 (X - C a)).natDegree ≤ 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  have hi' : 1 < i := by exact_mod_cast hi
  rw [coeff_reflect]
  have : revAt 1 i = i := by
    change revAtFun 1 i = i
    unfold revAtFun
    rw [ite_eq_right (Nat.not_le_of_gt hi')]
  rw [this, coeff_sub, coeff_X, coeff_C]
  simp [show i ≠ 0 by lia, show (1 : ℕ) ≠ i by lia]

/-- `reflect` preserves splitting. -/
private theorem splits_reflect {p : ℝ[X]} (hp : p.Splits) {N : ℕ} (hN : p.natDegree ≤ N) :
    (reflect N p).Splits := by
  have key : ∀ (s : Multiset ℝ) (N : ℕ), Multiset.card s ≤ N →
      (reflect N (s.map fun a => X - C a).prod).Splits := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro N _; simp [reflect_one]
    | cons a s ih =>
      intro N hN
      simp only [Multiset.card_cons] at hN
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by lia⟩
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [add_comm M 1, reflect_mul _ _ (natDegree_X_sub_C_le a)
        (by rw [natDegree_multiset_prod_X_sub_C_eq_card]; lia)]
      exact Splits.mul (Splits.of_natDegree_le_one (natDegree_reflect_one_le a)) (ih M (by lia))
  rw [hp.eq_prod_roots, reflect_C_mul]
  apply Splits.C_mul
  apply key
  rw [← hp.natDegree_eq_card_roots]; exact hN

end SchurSzegoAristotle

/-!
## The apolar form

`apo n R W = ∑_{k ≤ n} (-1)^k k! (n-k)! R_k W_{n-k}` is the classical invariant bilinear
form on polynomials of degree at most `n`.  We prove its invariance under translations and
under the reflection `reflect n`, its compatibility with differentiation, and the vanishing
when the two arguments share a root of large total multiplicity.
-/

@[expose] public section

open Polynomial Finset

namespace SchurSzegoAristotle

/-- The apolar form of degree `n`. -/
private noncomputable def apo (n : ℕ) (R W : ℝ[X]) : ℝ :=
  ∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) *
    R.coeff k * W.coeff (n - k)

private theorem apo_add_left (n : ℕ) (R R' W : ℝ[X]) : apo n (R + R') W = apo n R W + apo n R' W :=
  by
  simp only [apo, coeff_add, ← sum_add_distrib]
  exact sum_congr rfl fun k _ => by ring

private theorem apo_C_mul_left (n : ℕ) (c : ℝ) (R W : ℝ[X]) : apo n (C c * R) W = c * apo n R W :=
  by
  simp only [apo, coeff_C_mul, mul_sum]
  exact sum_congr rfl fun k _ => by ring

private theorem apo_C_mul_right (n : ℕ) (c : ℝ) (R W : ℝ[X]) : apo n R (C c * W) = c * apo n R W :=
  by
  simp only [apo, coeff_C_mul, mul_sum]
  exact sum_congr rfl fun k _ => by ring

private theorem apo_sum_left {ι : Type*} (n : ℕ) (s : Finset ι) (R : ι → ℝ[X]) (W : ℝ[X]) :
    apo n (∑ i ∈ s, R i) W = ∑ i ∈ s, apo n (R i) W := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [apo]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, apo_add_left, ih]

private theorem apo_zero_left (n : ℕ) (W : ℝ[X]) : apo n 0 W = 0 := by simp [apo]

/-- Reflection invariance (no degree hypotheses are needed). -/
private theorem apo_reflect (n : ℕ) (R W : ℝ[X]) :
    apo n (reflect n R) (reflect n W) = (-1) ^ n * apo n R W := by
  unfold apo
  rw [mul_sum, ← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simp at hk; lia
  have h1 : n + 1 - 1 - k = n - k := by lia
  rw [h1, coeff_reflect, coeff_reflect, revAt_le (by lia), revAt_le (by lia),
    show n - (n - k) = k by lia]
  have hpow : (-1 : ℝ) ^ (n - k) = (-1) ^ n * (-1) ^ k := by
    have : (-1 : ℝ) ^ n = (-1) ^ (n - k) * (-1) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk']
    rw [this, mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
  rw [hpow]; ring

/-- The polynomial whose evaluation at `a` computes `apo` of the translates. -/
private noncomputable def apoPoly (n : ℕ) (R W : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (n + 1), C ((-1 : ℝ) ^ k) * ((derivative^[k] R) * (derivative^[n - k] W))

private theorem coeff_taylor_eq (a : ℝ) (R : ℝ[X]) (k : ℕ) :
    (k.factorial : ℝ) * (taylor a R).coeff k = (derivative^[k] R).eval a := by
  rw [taylor_coeff, ← factorial_smul_hasseDeriv]
  simp [nsmul_eq_mul]

private theorem apo_taylor_eq_eval (n : ℕ) (a : ℝ) (R W : ℝ[X]) :
    apo n (taylor a R) (taylor a W) = (apoPoly n R W).eval a := by
  unfold apo apoPoly
  rw [eval_finsetSum]
  refine sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, eval_mul, ← coeff_taylor_eq, ← coeff_taylor_eq]
  ring

private theorem derivative_apoPoly {n : ℕ} {R W : ℝ[X]} (hR : R.natDegree ≤ n)
    (hW : W.natDegree ≤ n) :
    derivative (apoPoly n R W) = 0 := by
  unfold apoPoly
  set T : ℕ → ℝ[X] := fun k => C ((-1 : ℝ) ^ k) *
    ((derivative^[k] R) * (derivative^[n + 1 - k] W)) with hT
  have hterm : ∀ k ∈ range (n + 1), derivative (C ((-1 : ℝ) ^ k) *
      ((derivative^[k] R) * (derivative^[n - k] W))) = T k - T (k + 1) := by
    intro k hk
    have hk' : k ≤ n := by simp at hk; lia
    rw [derivative_C_mul, derivative_mul]
    simp only [hT]
    rw [show n + 1 - k = (n - k) + 1 by lia, show n + 1 - (k + 1) = n - k by lia,
      Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ, C_mul, C_neg, C_1]
    ring
  rw [derivative_sum, sum_congr rfl hterm, sum_range_sub']
  simp only [hT, Nat.sub_zero, Nat.sub_self]
  rw [iterate_derivative_eq_zero (by lia : W.natDegree < n + 1),
    iterate_derivative_eq_zero (by lia : R.natDegree < n + 1)]
  simp

/-- Translation invariance of the apolar form. -/
private theorem apo_taylor {n : ℕ} {R W : ℝ[X]} (hR : R.natDegree ≤ n) (hW : W.natDegree ≤ n)
    (a : ℝ) :
    apo n (taylor a R) (taylor a W) = apo n R W := by
  have h0 : apo n R W = apo n (taylor 0 R) (taylor 0 W) := by simp
  rw [h0, apo_taylor_eq_eval, apo_taylor_eq_eval]
  rw [eq_C_of_derivative_eq_zero (derivative_apoPoly hR hW)]
  simp

/-- Frame change: translate by `a` and reflect. -/
private theorem apo_frame {n : ℕ} {R W : ℝ[X]} (hR : R.natDegree ≤ n) (hW : W.natDegree ≤ n)
    (a : ℝ) :
    apo n R W = (-1) ^ n * apo n (reflect n (taylor a R)) (reflect n (taylor a W)) := by
  rw [apo_reflect, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp [apo_taylor hR hW]

/-- Compatibility with differentiation. -/
private theorem apo_succ {n : ℕ} {R : ℝ[X]} (hR : R.natDegree ≤ n) (W : ℝ[X]) :
    apo (n + 1) R W = apo n R (derivative W) := by
  unfold apo
  rw [sum_range_succ, coeff_eq_zero_of_natDegree_lt (by lia : R.natDegree < n + 1)]
  simp only [mul_zero, zero_mul, add_zero]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simp at hk; lia
  rw [coeff_derivative, show n + 1 - k = (n - k) + 1 by lia, Nat.factorial_succ]
  push_cast
  rw [show (↑(n - k) : ℝ) = (n : ℝ) - k by rw [Nat.cast_sub hk']]
  ring

private theorem apo_add_iterate {n k : ℕ} {R : ℝ[X]} (hR : R.natDegree ≤ n) (W : ℝ[X]) :
    apo (n + k) R W = apo n R (derivative^[k] W) := by
  induction k generalizing W with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, apo_succ (by lia), ih, Function.iterate_succ_apply]

/-- `apo` with a monomial on the left. -/
private theorem apo_X_pow_left {n α : ℕ} (hα : α ≤ n) (W : ℝ[X]) :
    apo n (X ^ α) W = (-1) ^ α * ((α.factorial : ℝ) * ((n - α).factorial : ℝ)) *
      W.coeff (n - α) := by
  unfold apo
  rw [sum_eq_single α]
  · simp
  · intro b _ hb; simp [coeff_X_pow, hb]
  · intro h; simp at h; lia

/-- `apo` vanishes when the degrees are too small. -/
private theorem apo_eq_zero_of_natDegree {n : ℕ} {R W : ℝ[X]} (h : R.natDegree + W.natDegree < n) :
    apo n R W = 0 := by
  unfold apo
  refine sum_eq_zero fun k hk => ?_
  have hk' : k ≤ n := by simp at hk; lia
  rcases Nat.lt_or_ge R.natDegree k with h1 | h1
  · rw [coeff_eq_zero_of_natDegree_lt h1]; ring
  · rw [coeff_eq_zero_of_natDegree_lt (show W.natDegree < n - k by lia)]; ring

private theorem taylor_X_sub_C_pow_mul (a : ℝ) (k : ℕ) (Y : ℝ[X]) :
    taylor a ((X - C a) ^ k * Y) = X ^ k * taylor a Y := by
  simp [taylor_mul, taylor_pow]

/-- Vanishing of `apo` when the arguments share a root of large total multiplicity. -/
private theorem apo_eq_zero_of_dvd {n m l : ℕ} {R W : ℝ[X]} {z : ℝ} (hR : R.natDegree ≤ n)
    (hW : W.natDegree ≤ n) (hmR : (X - C z) ^ m ∣ R) (hlW : (X - C z) ^ l ∣ W)
    (hml : n < m + l) : apo n R W = 0 := by
  rw [← apo_taylor hR hW z]
  obtain ⟨R1, rfl⟩ := hmR
  obtain ⟨W1, rfl⟩ := hlW
  rw [taylor_X_sub_C_pow_mul, taylor_X_sub_C_pow_mul]
  unfold apo
  refine sum_eq_zero fun k hk => ?_
  have hk' : k ≤ n := by simp at hk; lia
  rcases Nat.lt_or_ge k m with h1 | h1
  · rw [coeff_X_pow_mul', ite_eq_right (by lia)]; ring
  · rw [coeff_X_pow_mul' (n := l), ite_eq_right (by lia)]; ring

/-- Duality at a single point. -/
private theorem dvd_of_apo_eq_zero {n k : ℕ} {W : ℝ[X]} {a : ℝ} (hk : k ≤ n) (hW : W.natDegree ≤ n)
    (h : ∀ U : ℝ[X], U.natDegree ≤ n - k → apo n ((X - C a) ^ k * U) W = 0) :
    (X - C a) ^ (n - k + 1) ∣ W := by
  set V := taylor a W with hV
  have hcoeff : ∀ j, j ≤ n - k → V.coeff j = 0 := by
    intro j hj
    have hU : (taylor (-a) (X ^ (n - k - j))).natDegree ≤ n - k := by
      rw [natDegree_taylor, natDegree_X_pow]; lia
    have h1 := h _ hU
    have hdeg : ((X - C a) ^ k * taylor (-a) (X ^ (n - k - j))).natDegree ≤ n := by
      refine (natDegree_mul_le).trans ?_
      rw [natDegree_taylor, natDegree_X_pow]
      have := natDegree_pow_le (p := X - C a) (n := k)
      rw [natDegree_X_sub_C, mul_one] at this
      lia
    rw [← apo_taylor hdeg hW a, taylor_X_sub_C_pow_mul, taylor_taylor, add_neg_cancel,
      taylor_zero, ← pow_add, apo_X_pow_left (by lia)] at h1
    have e : n - (k + (n - k - j)) = j := by lia
    rw [e] at h1
    exact (mul_eq_zero.mp h1).resolve_left (by simp [Nat.factorial_ne_zero])
  have hdvd : X ^ (n - k + 1) ∣ V := by
    rw [X_pow_dvd_iff]; intro d hd; exact hcoeff d (by lia)
  obtain ⟨V1, hV1⟩ := hdvd
  refine ⟨taylor (-a) V1, ?_⟩
  have : W = taylor (-a) V := by rw [hV, taylor_taylor, neg_add_cancel, taylor_zero]
  rw [this, hV1, taylor_mul, taylor_pow, taylor_X, map_neg, sub_eq_add_neg]

end SchurSzegoAristotle

/-!
## Real-rooted polynomials annihilated by multiples of a fixed polynomial

If a real-rooted polynomial `W` of degree at most `n` is apolar to every polynomial of degree
at most `n` divisible by `G = ∏ (X - a_i)^{k_i}` (with `∑ (k_i + 1) ≤ n`), then `W` vanishes
to order at least `n - k_i + 1` at one of the points `a_i`.
-/

@[expose] public section

open Polynomial Finset

namespace SchurSzegoAristotle

private theorem reflect_one_X_sub_C (d : ℝ) : reflect 1 (X - C d) = 1 - C d * X := by
  rw [reflect_sub, reflect_one_X, reflect_C, pow_one]

private theorem natDegree_X_sub_C_pow_le (d : ℝ) (k : ℕ) : ((X - C d) ^ k).natDegree ≤ k := by
  have := natDegree_pow_le (p := X - C d) (n := k)
  rw [natDegree_X_sub_C, mul_one] at this; exact this

private theorem reflect_X_sub_C_pow (d : ℝ) (k : ℕ) : reflect k ((X - C d) ^ k) =
    (1 - C d * X) ^ k := by
  induction k with
  | zero => simp [reflect_one]
  | succ k ih =>
    rw [pow_succ, add_comm k 1, mul_comm, reflect_mul _ _ (natDegree_X_sub_C_le d)
      (natDegree_X_sub_C_pow_le d k), reflect_one_X_sub_C, ih, add_comm 1 k, pow_succ']

private theorem one_sub_C_mul_X {d : ℝ} (hd : d ≠ 0) : (1 - C d * X : ℝ[X]) = C (-d) * (X - C
    (1 / d)) := by
  rw [mul_sub, ← C_mul, show -d * (1 / d) = -1 by field_simp]; simp; ring

private theorem taylor_X_sub_C' (a c : ℝ) : taylor a (X - C c) = X - C (c - a) := by
  simp [taylor_X, taylor_C, C_sub]; ring

private theorem natDegree_reflect_le' {N : ℕ} {p : ℝ[X]} (h : p.natDegree ≤ N) :
    (reflect N p).natDegree ≤ N :=
  natDegree_reflect_le.trans (max_le le_rfl h)

/-- Killing a factor `(X - a)^k` at the frame point `a`. -/
private theorem reflect_taylor_X_sub_C_pow_mul {N k : ℕ} (hk : k ≤ N) (a : ℝ) {Y : ℝ[X]}
    (hY : Y.natDegree ≤ N - k) :
    reflect N (taylor a ((X - C a) ^ k * Y)) = reflect (N - k) (taylor a Y) := by
  rw [taylor_X_sub_C_pow_mul]
  conv_lhs => rw [show N = k + (N - k) by lia]
  rw [reflect_mul _ _ (by rw [natDegree_X_pow]) (by rw [natDegree_taylor]; exact hY),
    reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero, one_mul]

/-- A factor `(X - c)^k` with `c ≠ a` in the frame at `a`. -/
private theorem reflect_taylor_X_sub_C_pow_mul' {N k : ℕ} (hk : k ≤ N) {a c : ℝ} (hac : c ≠ a)
    {Y : ℝ[X]} (hY : Y.natDegree ≤ N - k) :
    reflect N (taylor a ((X - C c) ^ k * Y)) =
      C ((a - c) ^ k) * ((X - C (1 / (c - a))) ^ k * reflect (N - k) (taylor a Y)) := by
  have ht : taylor a ((X - C c) ^ k) = (X - C (c - a)) ^ k := by
    rw [taylor_pow, taylor_X_sub_C']
  rw [taylor_mul, ht]
  conv_lhs => rw [show N = k + (N - k) by lia]
  rw [reflect_mul _ _ (natDegree_X_sub_C_pow_le _ k) (by rw [natDegree_taylor]; exact hY),
    reflect_X_sub_C_pow, one_sub_C_mul_X (sub_ne_zero.mpr hac), mul_pow, ← C_pow, mul_assoc]
  congr 2; ring

private theorem iterate_derivative_eq_zero_imp {p : ℝ[X]} {k : ℕ} (hk : 1 ≤ k)
    (h : derivative^[k] p = 0) : p.natDegree < k := by
  by_contra hlt
  push Not at hlt
  have hp : p ≠ 0 := by rintro rfl; simp at hlt; lia
  have := congrArg (fun q => q.coeff (p.natDegree - k)) h
  simp only [coeff_iterate_derivative_real, coeff_zero, Nat.sub_add_cancel hlt] at this
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 (by exact_mod_cast (Nat.descFactorial_pos.mpr hlt).ne')
  · exact hp (leadingCoeff_eq_zero.mp h1)

/-- Transport of the apolar form when killing the point `a`. -/
private theorem apo_kill {n k : ℕ} (hk : k ≤ n) (a : ℝ) {Y W : ℝ[X]} (hY : Y.natDegree ≤ n - k)
    (hW : W.natDegree ≤ n) :
    apo n ((X - C a) ^ k * Y) W = (-1) ^ n * apo (n - k) (reflect (n - k) (taylor a Y))
      (derivative^[k] (reflect n (taylor a W))) := by
  have hdeg : ((X - C a) ^ k * Y).natDegree ≤ n :=
    natDegree_mul_le.trans (by have := natDegree_X_sub_C_pow_le a k; lia)
  rw [apo_frame hdeg hW a, reflect_taylor_X_sub_C_pow_mul hk a hY, ← apo_add_iterate
    (natDegree_reflect_le' (by rw [natDegree_taylor]; exact hY)), Nat.sub_add_cancel hk]

/-- Transport of the apolar form to the frame at `b` (no derivative). -/
private theorem apo_frame' {n : ℕ} (b : ℝ) {R W : ℝ[X]} (hR : R.natDegree ≤ n)
    (hW : W.natDegree ≤ n)
    (e : ℝ) :
    apo n R W = (-1) ^ n * apo n (taylor e (reflect n (taylor b R)))
      (taylor e (reflect n (taylor b W))) := by
  rw [apo_frame hR hW b, apo_taylor (natDegree_reflect_le' (by rw [natDegree_taylor]; exact hR))
    (natDegree_reflect_le' (by rw [natDegree_taylor]; exact hW))]

/-- The two-point case: a gap argument in the frame sending `b` to infinity and `a` to `0`. -/
private theorem p2_lemma {n k k' : ℕ} {a b : ℝ} (hab : a ≠ b) (hn : k + k' + 1 ≤ n) {W : ℝ[X]}
    (hW0 : W ≠ 0) (hWs : W.Splits) (hWn : W.natDegree ≤ n)
    (h : ∀ U : ℝ[X], U.natDegree ≤ n - k - k' →
      apo n ((X - C a) ^ k * ((X - C b) ^ k' * U)) W = 0) :
    (X - C a) ^ (n - k + 1) ∣ W ∨ (X - C b) ^ (n - k' + 1) ∣ W := by
  set a' : ℝ := 1 / (a - b) with ha'
  set Z := taylor a' (reflect n (taylor b W)) with hZ
  have hZs : Z.Splits :=
    (splits_reflect (hWs.taylor b) (by rw [natDegree_taylor]; exact hWn)).taylor a'
  have hZ0 : Z ≠ 0 := by
    rw [hZ]; intro h0
    rw [taylor_eq_zero, reflect_eq_zero_iff, taylor_eq_zero] at h0; exact hW0 h0
  have hZn : Z.natDegree ≤ n := by
    rw [hZ, natDegree_taylor]; exact natDegree_reflect_le' (by rw [natDegree_taylor]; exact hWn)
  -- Step 1: vanishing of the middle coefficients of `Z`.
  have hgap : ∀ j, k' ≤ j → j ≤ n - k → Z.coeff j = 0 := by
    intro j hj1 hj2
    set i := n - k - j with hi
    set s := n - k - k' with hs
    set U := taylor (-b) (reflect s (taylor (-a') (X ^ i))) with hU
    have hUdeg : U.natDegree ≤ s := by
      rw [hU, natDegree_taylor]
      exact natDegree_reflect_le' (by rw [natDegree_taylor, natDegree_X_pow]; lia)
    have h1 := h U hUdeg
    have hYdeg : ((X - C a) ^ k * U).natDegree ≤ n - k' :=
      natDegree_mul_le.trans (by have := natDegree_X_sub_C_pow_le a k; lia)
    have hRdeg : ((X - C a) ^ k * ((X - C b) ^ k' * U)).natDegree ≤ n := by
      rw [mul_left_comm]
      exact natDegree_mul_le.trans (by have := natDegree_X_sub_C_pow_le b k'; lia)
    rw [apo_frame' b hRdeg hWn a', mul_left_comm,
      reflect_taylor_X_sub_C_pow_mul (by lia) b hYdeg,
      reflect_taylor_X_sub_C_pow_mul' (by lia) hab (by lia)] at h1
    have hTU : reflect (n - k' - k) (taylor b U) = taylor (-a') (X ^ i) := by
      rw [hU, taylor_taylor, add_neg_cancel, taylor_zero, show n - k' - k = s by lia,
        reflect_reflect]
    rw [hTU, taylor_mul, taylor_mul, taylor_C, taylor_pow, taylor_X_sub_C', ← ha', sub_self,
      C_0, sub_zero, taylor_taylor, add_neg_cancel, taylor_zero, apo_C_mul_left, ← pow_add,
      apo_X_pow_left (by lia), show n - (k + i) = j by lia] at h1
    have hne : (a - b) ≠ 0 := sub_ne_zero.mpr hab
    simp only [mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and, false_or,
      Nat.cast_eq_zero, Nat.factorial_ne_zero, sub_eq_zero, ne_eq] at h1
    rcases h1 with h1 | h1
    · exact absurd h1.1 (by intro h2; exact hab h2.symm)
    · exact h1
  -- Step 2: the gap lemma.
  rcases Nat.lt_or_ge (k' + 1) Z.natDegree with hdeg | hdeg
  · left
    have hlow := gap_lemma hZs k' hdeg (hgap k' le_rfl (by lia)) (hgap (k' + 1) (by lia)
      (by lia))
    have hall : ∀ j, j ≤ n - k → Z.coeff j = 0 := by
      intro j hj
      rcases Nat.lt_or_ge (k' + 1) j with h2 | h2
      · exact hgap j (by lia) hj
      · exact hlow j h2
    have hXdvd : (X - C 0) ^ (n - k + 1) ∣ Z := by
      rw [C_0, sub_zero, X_pow_dvd_iff]; intro d hd; exact hall d (by lia)
    refine dvd_of_apo_eq_zero (by lia) hWn fun U hU => ?_
    have hRdeg : ((X - C a) ^ k * U).natDegree ≤ n :=
      natDegree_mul_le.trans (by have := natDegree_X_sub_C_pow_le a k; lia)
    rw [apo_frame' b hRdeg hWn a', reflect_taylor_X_sub_C_pow_mul' (by lia) hab hU,
      taylor_mul, taylor_mul, taylor_C, taylor_pow, taylor_X_sub_C', ← ha', sub_self, C_0,
      apo_C_mul_left, ← hZ]
    have hdeg1 : (X ^ k * taylor a' (reflect (n - k) (taylor b U))).natDegree ≤ n := by
      refine natDegree_mul_le.trans ?_
      rw [natDegree_X_pow, natDegree_taylor]
      have := natDegree_reflect_le' (N := n - k) (p := taylor b U)
        (by rw [natDegree_taylor]; exact hU)
      lia
    rw [sub_zero, apo_eq_zero_of_dvd (z := 0) (m := k) (l := n - k + 1) hdeg1 hZn
      (by rw [C_0, sub_zero]; exact dvd_mul_right _ _) hXdvd (by lia)]
    ring
  · right
    have hsmall : Z.natDegree < k' := by
      by_contra hcon
      push Not at hcon
      have hc : Z.coeff Z.natDegree = 0 := by
        rcases Nat.lt_or_ge (k' + 1) Z.natDegree with h2 | h2
        · lia
        · exact hgap _ hcon (by lia)
      exact hZ0 (leadingCoeff_eq_zero.mp hc)
    refine dvd_of_apo_eq_zero (by lia) hWn fun U hU => ?_
    have hRdeg : ((X - C b) ^ k' * U).natDegree ≤ n :=
      natDegree_mul_le.trans (by have := natDegree_X_sub_C_pow_le b k'; lia)
    rw [apo_frame' b hRdeg hWn a', reflect_taylor_X_sub_C_pow_mul (by lia) b hU, ← hZ]
    have h1 : (taylor a' (reflect (n - k') (taylor b U))).natDegree ≤ n - k' := by
      rw [natDegree_taylor]; exact natDegree_reflect_le' (by rw [natDegree_taylor]; exact hU)
    rw [apo_eq_zero_of_natDegree (by lia)]; ring

end SchurSzegoAristotle

namespace SchurSzegoAristotle

private theorem natDegree_listProd_le (l : List (ℝ × ℕ)) (f : ℝ × ℕ → ℝ) :
    ((l.map fun p => (X - C (f p)) ^ p.2).prod).natDegree ≤ (l.map Prod.snd).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact natDegree_mul_le.trans (add_le_add (natDegree_X_sub_C_pow_le _ _) ih)

private theorem reflect_taylor_listProd (a1 : ℝ) (l : List (ℝ × ℕ)) (hl : ∀ p ∈ l, p.1 ≠ a1) :
    reflect (l.map Prod.snd).sum (taylor a1 (l.map fun p => (X - C p.1) ^ p.2).prod) =
      C (l.map fun p => (a1 - p.1) ^ p.2).prod *
        (l.map fun p => (X - C (1 / (p.1 - a1))) ^ p.2).prod := by
  induction l with
  | nil => simp [reflect_one]
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have hrest := natDegree_listProd_le l Prod.fst
    rw [reflect_taylor_X_sub_C_pow_mul' (by lia) (hl p List.mem_cons_self)
      (by simpa using hrest), Nat.add_sub_cancel_left,
      ih fun q hq => hl q (List.mem_cons_of_mem _ hq), C_mul]
    ring

private theorem prod_pow_ne_zero (a1 : ℝ) (l : List (ℝ × ℕ)) (hl : ∀ p ∈ l, p.1 ≠ a1) :
    (l.map fun p => (a1 - p.1) ^ p.2).prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (hl p List.mem_cons_self).symm))
      (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))

/-- Statement of the lemma for lists of length at most `N`, by induction on `N`. -/
private theorem lstar_aux : ∀ (N : ℕ) (l : List (ℝ × ℕ)), l.length ≤ N → ∀ (n : ℕ) (W : ℝ[X]),
    (l.map Prod.fst).Nodup →
    (l.map fun p => p.2 + 1).sum ≤ n →
    W ≠ 0 → W.Splits → W.natDegree ≤ n →
    (∀ U : ℝ[X], U.natDegree ≤ n - (l.map Prod.snd).sum →
      apo n ((l.map fun p => (X - C p.1) ^ p.2).prod * U) W = 0) →
    ∃ p ∈ l, (X - C p.1) ^ (n - p.2 + 1) ∣ W := by
  intro N
  induction N with
  | zero =>
    intro l hl n W _ _ hW0 _ hWn h
    have hl0 : l = [] := List.length_eq_zero_iff.mp (by lia)
    subst hl0
    exfalso
    have hd := dvd_of_apo_eq_zero (k := 0) (a := 0) (Nat.zero_le n) hWn
      (fun U hU => by simpa using h U (by simpa using hU))
    have := natDegree_le_of_dvd hd hW0
    rw [natDegree_pow, C_0, sub_zero, natDegree_X] at this
    lia
  | succ N ih =>
    intro l0 hl0 n W hnd hsum hW0 hWs hWn h
    cases l0 with
    | nil =>
      exfalso
      have hd := dvd_of_apo_eq_zero (k := 0) (a := 0) (Nat.zero_le n) hWn
        (fun U hU => by simpa using h U (by simpa using hU))
      have := natDegree_le_of_dvd hd hW0
      rw [natDegree_pow, C_0, sub_zero, natDegree_X] at this
      lia
    | cons p l =>
    simp only [List.length_cons] at hl0
    obtain ⟨a1, k1⟩ := p
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hnd hsum h
    have hnotin : ∀ q ∈ l, q.1 ≠ a1 := by
      intro q hq heq
      exact (List.nodup_cons.mp hnd).1 (heq ▸ List.mem_map_of_mem hq)
    have hsl : (l.map Prod.snd).sum ≤ (l.map fun p => p.2 + 1).sum := by
      apply List.sum_le_sum; intro q _; lia
    have hk1n : k1 + 1 ≤ n := by lia
    set V := reflect n (taylor a1 W) with hV
    set W1 := derivative^[k1] V with hW1
    set n1 := n - k1 with hn1
    have hVs : V.Splits := splits_reflect (hWs.taylor a1) (by rw [natDegree_taylor]; exact hWn)
    have hVn : V.natDegree ≤ n := natDegree_reflect_le' (by rw [natDegree_taylor]; exact hWn)
    by_cases hW10 : W1 = 0
    · refine ⟨(a1, k1), List.mem_cons_self, dvd_of_apo_eq_zero (by lia) hWn fun U hU => ?_⟩
      rw [apo_kill (by lia) a1 hU hWn, ← hV, ← hW1, hW10]
      simp [apo]
    -- apply the induction hypothesis to `W1`
    set L := l.map fun q : ℝ × ℕ => (1 / (q.1 - a1), q.2) with hL
    have hLfst : L.map Prod.fst = (l.map Prod.fst).map fun x => 1 / (x - a1) := by
      simp [hL, List.map_map, Function.comp_def]
    have hLsnd : L.map Prod.snd = l.map Prod.snd := by simp [hL, List.map_map, Function.comp_def]
    have hLsum : (L.map fun p => p.2 + 1).sum = (l.map fun p => p.2 + 1).sum := by
      simp [hL, List.map_map, Function.comp_def]
    have hLprod : (L.map fun p => (X - C p.1) ^ p.2).prod =
        (l.map fun p => (X - C (1 / (p.1 - a1))) ^ p.2).prod := by
      simp [hL, List.map_map, Function.comp_def]
    have hW1n : W1.natDegree ≤ n1 :=
      (natDegree_iterate_derivative V k1).trans (by lia)
    obtain ⟨p'', hp''L, hdvd⟩ := ih L (by simp [hL]; lia) n1 W1
      (by
        rw [hLfst]
        refine (List.nodup_cons.mp hnd).2.map_on ?_
        intro x hx y hy hxy
        obtain ⟨qx, hqx, rfl⟩ := List.mem_map.mp hx
        obtain ⟨qy, hqy, rfl⟩ := List.mem_map.mp hy
        have h1 := sub_ne_zero.mpr (hnotin qx hqx)
        have h2 := sub_ne_zero.mpr (hnotin qy hqy)
        field_simp at hxy
        linarith)
      (by rw [hLsum]; lia) hW10 (splits_iterate_derivative_real hVs k1) hW1n
      (by
        intro U'' hU''
        rw [hLsnd] at hU''
        set s := n - (k1 + (l.map Prod.snd).sum) with hs
        set U := taylor (-a1) (reflect s U'') with hU
        have hUdeg : U.natDegree ≤ s := by
          rw [hU, natDegree_taylor]; exact natDegree_reflect_le' (by lia)
        have h0 := h U hUdeg
        have hG1 := natDegree_listProd_le l Prod.fst
        have hYdeg : ((l.map fun p => (X - C p.1) ^ p.2).prod * U).natDegree ≤ n - k1 :=
          natDegree_mul_le.trans (by lia)
        rw [mul_assoc, apo_kill (by lia) a1 hYdeg hWn, ← hV, ← hW1, taylor_mul,
          show n - k1 = (l.map Prod.snd).sum + s by lia,
          reflect_mul _ _ (by rw [natDegree_taylor]; exact hG1)
            (by rw [natDegree_taylor]; exact hUdeg),
          reflect_taylor_listProd a1 l hnotin, hU, taylor_taylor, add_neg_cancel, taylor_zero,
          reflect_reflect, mul_assoc, apo_C_mul_left, show (l.map Prod.snd).sum + s = n1 by lia]
          at h0
        rw [hLprod]
        rcases mul_eq_zero.mp h0 with h2 | h2
        · exact absurd h2 (pow_ne_zero _ (by norm_num))
        · exact (mul_eq_zero.mp h2).resolve_left (prod_pow_ne_zero a1 l hnotin))
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp''L
    have hqle : q.2 + 1 ≤ (l.map fun p => p.2 + 1).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hq)
    have hp2 := p2_lemma (a := a1) (b := q.1) (k := k1) (k' := q.2) (hnotin q hq).symm
      (by lia) hW0 hWs hWn (by
        intro U hU
        have hYdeg : ((X - C q.1) ^ q.2 * U).natDegree ≤ n - k1 :=
          natDegree_mul_le.trans (by have := natDegree_X_sub_C_pow_le q.1 q.2; lia)
        rw [apo_kill (by lia) a1 hYdeg hWn, ← hV, ← hW1,
          reflect_taylor_X_sub_C_pow_mul' (by lia) (hnotin q hq) (by lia), apo_C_mul_left]
        have hdeg1 : ((X - C (1 / (q.1 - a1))) ^ q.2 *
            reflect (n - k1 - q.2) (taylor a1 U)).natDegree ≤ n - k1 := by
          refine natDegree_mul_le.trans ?_
          have := natDegree_X_sub_C_pow_le (1 / (q.1 - a1)) q.2
          have := natDegree_reflect_le' (N := n - k1 - q.2) (p := taylor a1 U)
            (by rw [natDegree_taylor]; lia)
          lia
        rw [apo_eq_zero_of_dvd hdeg1 hW1n (dvd_mul_right _ _) hdvd (by lia)]
        ring)
    rcases hp2 with h2 | h2
    · exact ⟨(a1, k1), List.mem_cons_self, h2⟩
    · exact ⟨q, List.mem_cons_of_mem _ hq, h2⟩

/-- If a nonzero real-rooted `W` of degree at most `n` is apolar to all multiples of
`∏ (X - a_i)^{k_i}` of degree at most `n`, where the `a_i` are distinct and
`∑ (k_i + 1) ≤ n`, then `(X - a_i)^{n - k_i + 1}` divides `W` for some `i`. -/
private theorem lstar_lemma (l : List (ℝ × ℕ)) (n : ℕ) (W : ℝ[X])
    (hnd : (l.map Prod.fst).Nodup) (hsum : (l.map fun p => p.2 + 1).sum ≤ n)
    (hW0 : W ≠ 0) (hWs : W.Splits) (hWn : W.natDegree ≤ n)
    (h : ∀ U : ℝ[X], U.natDegree ≤ n - (l.map Prod.snd).sum →
      apo n ((l.map fun p => (X - C p.1) ^ p.2).prod * U) W = 0) :
    ∃ p ∈ l, (X - C p.1) ^ (n - p.2 + 1) ∣ W :=
  lstar_aux l.length l le_rfl n W hnd hsum hW0 hWs hWn h

end SchurSzegoAristotle

/-!
## Basic facts on the fixed-degree Schur–Szegő composition

`ssc` is literally the same definition as `schurSzegoComp` of the main file.
-/

@[expose] public section

open Polynomial Finset

namespace SchurSzegoAristotle

local notation "ssc" => RealRooted.schurSzegoComp

private theorem coeff_ssc (n : ℕ) (f g : ℝ[X]) (k : ℕ) :
    (ssc n f g).coeff k = f.coeff k * g.coeff k / (Nat.choose n k : ℝ) := by
  exact RealRooted.coeff_schurSzegoComp_eq_div n f g k

private theorem natDegree_ssc_le (n : ℕ) (f g : ℝ[X]) : (ssc n f g).natDegree ≤ n := by
  exact RealRooted.natDegree_schurSzegoComp_le n f g

private theorem ssc_ne_zero {n : ℕ} {f g : ℝ[X]} (hf : f.natDegree = n) (hg : g.natDegree = n)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) : ssc n f g ≠ 0 := by
  have hc : (ssc n f g).coeff n = f.leadingCoeff * g.leadingCoeff := by
    rw [coeff_ssc, Nat.choose_self, Nat.cast_one, div_one, leadingCoeff, leadingCoeff, hf, hg]
  intro h
  rw [h, coeff_zero] at hc
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hf0) (leadingCoeff_ne_zero.mpr hg0) hc.symm

private theorem derivative_ssc (N : ℕ) (f g : ℝ[X]) :
    derivative (ssc (N + 1) f g) =
      C (1 / ((N : ℝ) + 1)) * ssc N (derivative f) (derivative g) := by
  ext j
  rw [coeff_derivative, coeff_C_mul, coeff_ssc, coeff_ssc, coeff_derivative, coeff_derivative]
  have key := Nat.add_one_mul_choose_eq N j
  rcases Nat.lt_or_ge N j with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by lia)]; simp
  · have h1 : (N.choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos h).ne'
    have h2 : ((N + 1).choose (j + 1) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by lia)).ne'
    have key' : ((N : ℝ) + 1) * N.choose j = ((N + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) := by
      exact_mod_cast key
    field_simp
    linear_combination (f.coeff (j + 1) * g.coeff (j + 1)) * key'

private theorem coeff_comp_C_mul_X' (Q : ℝ[X]) (a : ℝ) (k : ℕ) :
    (Q.comp (C a * X)).coeff k = a ^ k * Q.coeff k := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq]; ring
  | monomial i c =>
    rw [monomial_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow, coeff_monomial]
    split_ifs with h1 h2 h2 <;> subst_vars <;> simp_all; ring

private theorem natDegree_comp_C_mul_X_le (Q : ℝ[X]) (a : ℝ) : (Q.comp
    (C a * X)).natDegree ≤ Q.natDegree :=
  natDegree_comp_le.trans (by
    have : (C a * X).natDegree ≤ 1 := (natDegree_C_mul_le a X).trans natDegree_X_le
    nlinarith [Nat.zero_le Q.natDegree])

/-- The transform `Q ↦ X^n Q(-r/X)`. -/
private noncomputable def Tr (n : ℕ) (r : ℝ) (Q : ℝ[X]) : ℝ[X] := reflect n (Q.comp (C (-r) * X))

private theorem natDegree_Tr_le {n : ℕ} (r : ℝ) {Q : ℝ[X]} (hQ : Q.natDegree ≤ n) :
    (Tr n r Q).natDegree ≤ n :=
  natDegree_reflect_le' ((natDegree_comp_C_mul_X_le Q _).trans hQ)

private theorem coeff_Tr {n : ℕ} (r : ℝ) {Q : ℝ[X]} (hQ : Q.natDegree ≤ n) (j : ℕ) :
    (Tr n r Q).coeff j = if j ≤ n then (-r) ^ (n - j) * Q.coeff (n - j) else 0 := by
  unfold Tr
  rw [coeff_reflect]
  split_ifs with h
  · rw [revAt_le h, coeff_comp_C_mul_X']
  · change (Q.comp (C (-r) * X)).coeff (revAtFun n j) = 0
    rw [show revAtFun n j = j by
      unfold revAtFun
      rw [ite_eq_right h]]
    exact coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt ((natDegree_comp_C_mul_X_le Q _).trans hQ) (by lia))

private theorem Tr_Tr {n : ℕ} (r : ℝ) {Q : ℝ[X]} (hQ : Q.natDegree ≤ n) :
    Tr n r (Tr n r Q) = C ((-r) ^ n) * Q := by
  ext j
  rw [coeff_Tr r (natDegree_Tr_le r hQ), coeff_C_mul]
  split_ifs with h
  · rw [coeff_Tr r hQ, ite_eq_left (by lia), show n - (n - j) = j by lia, ← mul_assoc, ← pow_add,
      show n - j + j = n by lia]
  · rw [coeff_eq_zero_of_natDegree_lt (by lia)]; ring

private theorem Tr_mul {i k : ℕ} (r : ℝ) {A B : ℝ[X]} (hA : A.natDegree ≤ i)
    (hB : B.natDegree ≤ k) :
    Tr (i + k) r (A * B) = Tr i r A * Tr k r B := by
  unfold Tr
  rw [mul_comp, reflect_mul _ _ ((natDegree_comp_C_mul_X_le A _).trans hA)
    ((natDegree_comp_C_mul_X_le B _).trans hB)]

private theorem Tr_one_X_sub_C (r b : ℝ) : Tr 1 r (X - C b) = C (-r) - C b * X := by
  unfold Tr
  rw [sub_comp, X_comp, C_comp, reflect_sub, ← pow_one X, reflect_C_mul_X_pow, reflect_C]
  rw [show revAt 1 1 = 0 by exact revAt_le (by rfl)]
  simp

private theorem Tr_X_sub_C_pow (r b : ℝ) (l : ℕ) : Tr l r ((X - C b) ^ l) = (C
    (-r) - C b * X) ^ l := by
  induction l with
  | zero => simp [Tr]
  | succ l ih =>
    rw [pow_succ, Tr_mul r (natDegree_X_sub_C_pow_le b l) (by rw [natDegree_X_sub_C]), ih,
      Tr_one_X_sub_C, pow_succ]

private theorem dvd_Tr_of_dvd {n l : ℕ} (r : ℝ) {b : ℝ} (hb : b ≠ 0) {Q : ℝ[X]}
    (hQ : Q.natDegree ≤ n)
    (h : (X - C b) ^ l ∣ Q) : (X - C (-r / b)) ^ l ∣ Tr n r Q := by
  by_cases hQ0 : Q = 0
  · subst hQ0; simp [Tr]
  obtain ⟨B, rfl⟩ := h
  have hB0 : B ≠ 0 := by rintro rfl; simp at hQ0
  have hdeg := natDegree_mul (pow_ne_zero l (X_sub_C_ne_zero b)) hB0
  rw [natDegree_pow, natDegree_X_sub_C, mul_one] at hdeg
  have hl : l + (n - l) = n := by lia
  rw [← hl, Tr_mul r (natDegree_X_sub_C_pow_le b l) (show B.natDegree ≤ n - l by lia),
    Tr_X_sub_C_pow]
  refine Dvd.dvd.mul_right ?_ _
  have : (C (-r) - C b * X : ℝ[X]) = C (-b) * (X - C (-r / b)) := by
    rw [mul_sub, ← C_mul, show -b * (-r / b) = r by field_simp]; simp only [map_neg]; ring
  rw [this, mul_pow]
  exact Dvd.intro_left _ rfl

private theorem dvd_of_dvd_Tr {n l : ℕ} {r c : ℝ} (hr : r ≠ 0) (hc : c ≠ 0) {Q : ℝ[X]}
    (hQ : Q.natDegree ≤ n) (h : (X - C c) ^ l ∣ Tr n r Q) : (X - C (-r / c)) ^ l ∣ Q := by
  have h1 := dvd_Tr_of_dvd r hc (natDegree_Tr_le r hQ) h
  rw [Tr_Tr r hQ] at h1
  have hu : IsUnit (C ((-r) ^ n)) :=
    isUnit_C.mpr (IsUnit.mk0 _ (pow_ne_zero _ (neg_ne_zero.mpr hr)))
  exact (hu.dvd_mul_left).mp h1

private theorem Tr_ne_zero {n : ℕ} {r : ℝ} (hr : r ≠ 0) {Q : ℝ[X]} (hQ : Q.natDegree ≤ n)
    (hQ0 : Q ≠ 0) :
    Tr n r Q ≠ 0 := by
  intro h
  have := Tr_Tr r hQ
  rw [h, show Tr n r 0 = 0 by simp [Tr]] at this
  rcases mul_eq_zero.mp this.symm with h1 | h1
  · exact pow_ne_zero n (neg_ne_zero.mpr hr) (C_eq_zero.mp h1)
  · exact hQ0 h1

private theorem splits_Tr {n : ℕ} (r : ℝ) {Q : ℝ[X]} (hQ : Q.natDegree ≤ n) (hs : Q.Splits) :
    (Tr n r Q).Splits :=
  splits_reflect (hs.comp_of_natDegree_le_one ((natDegree_C_mul_le _ X).trans natDegree_X_le))
    ((natDegree_comp_C_mul_X_le Q _).trans hQ)

/-- Evaluation of the composition as an apolar pairing. -/
private theorem eval_ssc_eq_apo (n : ℕ) (P Q : ℝ[X]) (hQ : Q.natDegree ≤ n) (r : ℝ) :
    (ssc n P Q).eval r = apo n P (C (1 / (n.factorial : ℝ)) * Tr n r Q) := by
  rw [apo_C_mul_right]
  unfold RealRooted.schurSzegoComp apo
  rw [eval_finsetSum, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simp at hk; lia
  rw [eval_monomial, coeff_Tr r hQ, ite_eq_left (by lia), show n - (n - k) = k by lia,
    Nat.cast_choose ℝ hk']
  have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (k.factorial : ℝ) ≠ 0 := by positivity
  have h3 : ((n - k).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  rw [mul_assoc (P.coeff k * Q.coeff k), ← mul_pow, neg_one_mul, neg_neg]

end SchurSzegoAristotle

/-!
## Forced roots: the lower bound (Kostov–Shapiro, Proposition 4) and derivative facts
-/

@[expose] public section

open Polynomial Finset

namespace SchurSzegoAristotle

local notation "ssc" => RealRooted.schurSzegoComp

private theorem rootMultiplicity_le_natDegree' (p : ℝ[X])
    (a : ℝ) : p.rootMultiplicity a ≤ p.natDegree := by
  rw [← count_roots]; exact (Multiset.count_le_card _ _).trans (card_roots' p)

private theorem rootMultiplicity_C_mul' {c : ℝ} (hc : c ≠ 0) (p : ℝ[X]) (a : ℝ) :
    (C c * p).rootMultiplicity a = p.rootMultiplicity a := by
  by_cases hp : p = 0
  · simp [hp]
  rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hc) hp), rootMultiplicity_C, zero_add]

private theorem natDegree_derivative_eq' {p : ℝ[X]} {N : ℕ} (hp : p.natDegree = N + 1) :
    p.derivative.natDegree = N := by
  rw [Polynomial.natDegree_derivative, hp]
  lia

private theorem derivative_ne_zero' {p : ℝ[X]} {N : ℕ}
    (hp : p.natDegree = N + 1) : p.derivative ≠ 0 := by
  apply Polynomial.derivative_ne_zero.mpr
  rw [hp]
  lia

/-- Root multiplicities drop by one under differentiation of the composition. -/
private theorem rootMultiplicity_ssc_derivative (N : ℕ) (P Q : ℝ[X]) {r : ℝ}
    (hr : (ssc (N + 1) P Q).IsRoot r) :
    (ssc N P.derivative Q.derivative).rootMultiplicity r =
      (ssc (N + 1) P Q).rootMultiplicity r - 1 := by
  rw [← derivative_rootMultiplicity_of_root hr, derivative_ssc,
    rootMultiplicity_C_mul' (by positivity)]

/-- `ssc` at a root: evaluation vanishes if the inputs have a common forced root. -/
private theorem ssc_isRoot_of_forced {n : ℕ} {P Q : ℝ[X]} (hP : P.natDegree ≤ n)
    (hQ : Q.natDegree ≤ n)
    {a b : ℝ} (hb : b ≠ 0) (h : n < P.rootMultiplicity a + Q.rootMultiplicity b) :
    (ssc n P Q).IsRoot (-(a * b)) := by
  rw [IsRoot, eval_ssc_eq_apo n P Q hQ]
  refine apo_eq_zero_of_dvd (z := a) hP ?_ (pow_rootMultiplicity_dvd P a) ?_ h
  · exact (natDegree_C_mul_le _ _).trans (natDegree_Tr_le _ hQ)
  · have := dvd_Tr_of_dvd (-(a * b)) hb hQ (pow_rootMultiplicity_dvd Q b)
    rw [show -(-(a * b)) / b = a by field_simp] at this
    exact this.mul_left _

/-- Kostov–Shapiro, Proposition 4 (lower bound). -/
private theorem forced_lower : ∀ (n : ℕ) (P Q : ℝ[X]), P.natDegree = n → Q.natDegree = n → P ≠ 0 →
    Q ≠ 0 → ∀ a b : ℝ, b ≠ 0 → n < P.rootMultiplicity a + Q.rootMultiplicity b →
    P.rootMultiplicity a + Q.rootMultiplicity b - n ≤ (ssc n P Q).rootMultiplicity (-(a * b)) := by
  intro n
  induction n with
  | zero =>
    intro P Q hP hQ _ _ a b _ h
    have h1 := rootMultiplicity_le_natDegree' P a
    have h2 := rootMultiplicity_le_natDegree' Q b
    lia
  | succ N ih =>
    intro P Q hP hQ hP0 hQ0 a b hb h
    have hS0 := ssc_ne_zero hP hQ hP0 hQ0
    have hroot := ssc_isRoot_of_forced hP.le hQ.le hb h
    have hpos := (rootMultiplicity_pos hS0).mpr hroot
    have h1 := rootMultiplicity_le_natDegree' P a
    have h2 := rootMultiplicity_le_natDegree' Q b
    by_cases hk : P.rootMultiplicity a + Q.rootMultiplicity b - (N + 1) ≤ 1
    · lia
    have hPa : P.IsRoot a := (rootMultiplicity_pos hP0).mp (by lia)
    have hQb : Q.IsRoot b := (rootMultiplicity_pos hQ0).mp (by lia)
    have := ih _ _ (natDegree_derivative_eq' hP) (natDegree_derivative_eq' hQ)
      (derivative_ne_zero' hP) (derivative_ne_zero' hQ) a b hb
    rw [derivative_rootMultiplicity_of_root hPa, derivative_rootMultiplicity_of_root hQb,
      rootMultiplicity_ssc_derivative N P Q hroot] at this
    have := this (by lia)
    lia

/-- The derivative of a polynomial with only negative roots has only negative roots. -/
private theorem derivative_roots_neg {Q : ℝ[X]} {N : ℕ} (hQ : Q.natDegree = N + 1) (hQs : Q.Splits)
    (hneg : ∀ b ∈ Q.roots, b < 0) : ∀ b ∈ Q.derivative.roots, b < 0 := by
  intro x hx
  by_contra hx0
  push Not at hx0
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ
  have hQx : Q.eval x ≠ 0 := by
    intro h
    have := hneg x ((mem_roots hQ0).mpr h)
    linarith
  have hd := hQs.eval_derivative_eq_eval_mul_sum hQx
  rw [(mem_roots (derivative_ne_zero' hQ)).mp hx] at hd
  have hsum : 0 < (Q.roots.map fun z => 1 / (x - z)).sum := by
    have hne : Q.roots ≠ 0 := by
      intro h
      have := hQs.natDegree_eq_card_roots
      rw [h] at this; simp at this; lia
    obtain ⟨z0, hz0⟩ := Multiset.exists_mem_of_ne_zero hne
    rw [← Multiset.cons_erase hz0, Multiset.map_cons, Multiset.sum_cons]
    have h1 : 0 < 1 / (x - z0) := by have := hneg z0 hz0; apply div_pos one_pos; linarith
    have h2 : 0 ≤ ((Q.roots.erase z0).map fun z => 1 / (x - z)).sum := by
      refine Multiset.sum_nonneg fun y hy => ?_
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
      have := hneg z (Multiset.mem_of_mem_erase hz)
      apply div_nonneg zero_le_one; linarith
    linarith
  exact (mul_ne_zero hQx hsum.ne') hd.symm

end SchurSzegoAristotle

/-!
## The basic (double root) case
-/

@[expose] public section

open Polynomial Finset ComplexConjugate

namespace SchurSzegoAristotle

local notation "ssc" => RealRooted.schurSzegoComp

private theorem eval_map_ofReal (p : ℝ[X]) (x : ℝ) :
    (p.map Complex.ofRealHom).eval (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
  rw [eval_map, ← Complex.ofRealHom_eq_coe, eval₂_at_apply]; rfl

private theorem coeff_compC (n : ℕ) (P : ℂ[X]) (Q : ℝ[X]) (k : ℕ) :
    (compC n P Q).coeff k = P.coeff k * (Q.coeff k : ℂ) / (n.choose k : ℂ) := by
  unfold compC
  rw [finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro hk
    simp only [mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by lia)]; simp

private theorem compC_split (n : ℕ) (P T Q : ℝ[X]) :
    compC n (P.map Complex.ofRealHom + C Complex.I * T.map Complex.ofRealHom) Q =
      (ssc n P Q).map Complex.ofRealHom + C Complex.I * (ssc n T Q).map Complex.ofRealHom := by
  ext k
  simp only [coeff_compC, coeff_add, coeff_map, coeff_C_mul, coeff_ssc]
  simp only [Complex.ofRealHom_eq_coe]
  push_cast
  ring

/-- If `P + i T` has no zeros in the upper half-plane and `r` is a root of multiplicity exactly
two of `P ∘ Q`, then `r` is a root of `T ∘ Q`. -/
private theorem eval_ssc_eq_zero_of_stable {n : ℕ} {P Q T : ℝ[X]} (hQ0 : Q ≠ 0)
    (hQ : Q.natDegree = n)
    (hQs : Q.Splits) (hneg : ∀ b ∈ Q.roots, b < 0) (hP : P.natDegree ≤ n) (hT : T.natDegree ≤ n)
    (hstab : ∀ z : ℂ, 0 < z.im →
      (P.map Complex.ofRealHom + C Complex.I * T.map Complex.ofRealHom).eval z ≠ 0)
    {r : ℝ} (h0 : (ssc n P Q).eval r = 0) (h1 : (ssc n P Q).derivative.eval r = 0)
    (h2 : (ssc n P Q).derivative.derivative.eval r ≠ 0) : (ssc n T Q).eval r = 0 := by
  set S := ssc n P Q with hS
  set D := ssc n T Q with hD
  have hdeg : (P.map Complex.ofRealHom + C Complex.I * T.map Complex.ofRealHom).natDegree ≤ n := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_map]; exact hP
    · exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_map]; exact hT)
  have hst := compC_ne_zero n Q hQ0 hQ hQs hneg _ hdeg hstab
  rw [compC_split] at hst
  set g : ℝ[X] := D.derivative * S - S.derivative * D with hg
  have hle : ∀ x : ℝ, g.eval x ≤ 0 := by
    intro x
    have := hb_ineq hst x
    simp only [derivative_add, derivative_map, derivative_C_mul, eval_add, eval_mul, eval_C,
      eval_map_ofReal] at this
    simp only [hg, eval_sub, eval_mul]
    simp [Complex.mul_im, Complex.mul_re] at this
    linarith
  have hgr : g.eval r = 0 := by simp [hg, h0, h1]
  have hmax : IsLocalMax (fun x => g.eval x) r :=
    Filter.Eventually.of_forall fun y => by simp only [hgr]; exact hle y
  have hd := hmax.deriv_eq_zero
  rw [Polynomial.deriv] at hd
  simp only [hg, derivative_sub, derivative_mul, eval_sub, eval_add, eval_mul, h0, h1] at hd
  have : S.derivative.derivative.eval r * D.eval r = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left h2

/-- A real split nonzero polynomial does not vanish in the upper half-plane. -/
private theorem eval_map_ne_zero_of_splits {R : ℝ[X]} (hR0 : R ≠ 0) (hRs : R.Splits) (z : ℂ)
    (hz : 0 < z.im) : (R.map Complex.ofRealHom).eval z ≠ 0 := by
  rw [hRs.eq_prod_roots, Polynomial.map_mul, map_C, Polynomial.map_multiset_prod,
    Multiset.map_map, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
  refine mul_ne_zero (by simpa using hR0) (Multiset.prod_ne_zero ?_)
  intro h
  obtain ⟨b, _, hb⟩ := Multiset.mem_map.mp h
  simp only [Function.comp, Polynomial.map_sub, map_X, map_C, eval_sub, eval_X, eval_C] at hb
  have := congrArg Complex.im hb
  simp at this
  linarith

private theorem stable_of_factor {P R : ℝ[X]} {a : ℝ} (hPR : P = (X - C a) * R) (hR0 : R ≠ 0)
    (hRs : R.Splits) (z : ℂ) (hz : 0 < z.im) :
    (P.map Complex.ofRealHom + C Complex.I * R.map Complex.ofRealHom).eval z ≠ 0 := by
  have : P.map Complex.ofRealHom + C Complex.I * R.map Complex.ofRealHom =
      R.map Complex.ofRealHom * (X - C (a : ℂ) + C Complex.I) := by
    rw [hPR, Polynomial.map_mul]; simp; ring
  rw [this, eval_mul]
  refine mul_ne_zero (eval_map_ne_zero_of_splits hR0 hRs z hz) ?_
  simp only [eval_add, eval_sub, eval_X, eval_C]
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- Lagrange spanning: a linear form killing `G * N` and all `G * N / (X - i)` kills
`G * U` for every `U` of degree at most `#s`. -/
private theorem apo_G_mul_eq_zero {n : ℕ} {W : ℝ[X]} (s : Finset ℝ) (G : ℝ[X])
    (hN : apo n (G * ∏ a ∈ s, (X - C a)) W = 0)
    (hE : ∀ i ∈ s, apo n (G * ∏ j ∈ s.erase i, (X - C j)) W = 0)
    (U : ℝ[X]) (hU : U.natDegree ≤ s.card) : apo n (G * U) W = 0 := by
  set N := ∏ a ∈ s, (X - C a) with hNdef
  have hNm : N.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C i
  have hNd : N.natDegree = s.card := by
    rw [hNdef, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C i]; simp
  have hq : (U /ₘ N).natDegree = 0 := by rw [natDegree_divByMonic _ hNm]; lia
  have hU0deg : (U %ₘ N).degree < s.card := by
    have := degree_modByMonic_lt U hNm
    rwa [degree_eq_natDegree hNm.ne_zero, hNd] at this
  have hinterp := Lagrange.eq_interpolate (s := s) (v := id) (Set.injOn_id _) hU0deg
  rw [← modByMonic_add_div U N, eq_C_of_natDegree_eq_zero hq, hinterp,
    Lagrange.interpolate_apply, mul_add, apo_add_left, mul_sum, apo_sum_left]
  rw [show G * (N * C ((U /ₘ N).coeff 0)) = C ((U /ₘ N).coeff 0) * (G * N) by ring,
    apo_C_mul_left, hN, mul_zero, add_zero]
  refine sum_eq_zero fun i hi => ?_
  have hb : Lagrange.basis s id i =
      C (∏ j ∈ s.erase i, (i - j)⁻¹) * ∏ j ∈ s.erase i, (X - C j) := by
    rw [Lagrange.basis, map_prod, ← prod_mul_distrib]
    rfl
  rw [hb, show G * (C (eval (id i) (U %ₘ N)) * (C (∏ j ∈ s.erase i, (i - j)⁻¹) *
      ∏ j ∈ s.erase i, (X - C j))) = C (eval (id i) (U %ₘ N) * ∏ j ∈ s.erase i, (i - j)⁻¹) *
      (G * ∏ j ∈ s.erase i, (X - C j)) by rw [C_mul]; ring,
    apo_C_mul_left, hE i hi, mul_zero]

/-- The basic case: a nonzero root of multiplicity exactly two is forced, with total input
multiplicity at least `n + 2`. -/
private theorem double_root_forced {n : ℕ} {P Q : ℝ[X]} (hP : P.natDegree = n) (hPs : P.Splits)
    (hQ : Q.natDegree = n) (hQs : Q.Splits) (hneg : ∀ b ∈ Q.roots, b < 0) (hP0 : P ≠ 0)
    (hQ0 : Q ≠ 0) {r : ℝ} (hr : r ≠ 0) (h0 : (ssc n P Q).eval r = 0)
    (h1 : (ssc n P Q).derivative.eval r = 0)
    (h2 : (ssc n P Q).derivative.derivative.eval r ≠ 0) :
    ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ P.IsRoot a ∧ Q.IsRoot b ∧
      n + 2 ≤ P.rootMultiplicity a + Q.rootMultiplicity b ∧ r = -(a * b) := by
  classical
  have hfac : (1 / (n.factorial : ℝ)) ≠ 0 := by positivity
  set W := C (1 / (n.factorial : ℝ)) * Tr n r Q with hW
  have hWn : W.natDegree ≤ n := (natDegree_C_mul_le _ _).trans (natDegree_Tr_le r hQ.le)
  have hW0 : W ≠ 0 := mul_ne_zero (C_ne_zero.mpr hfac) (Tr_ne_zero hr hQ.le hQ0)
  have hWs : W.Splits := (splits_Tr r hQ.le hQs).C_mul _
  have hell : ∀ T : ℝ[X], T.natDegree ≤ n → (∀ z : ℂ, 0 < z.im →
      (P.map Complex.ofRealHom + C Complex.I * T.map Complex.ofRealHom).eval z ≠ 0) →
      apo n T W = 0 := fun T hT hst => by
    rw [← eval_ssc_eq_apo n T Q hQ.le r]
    exact eval_ssc_eq_zero_of_stable hQ0 hQ hQs hneg hP.le hT hst h0 h1 h2
  set s := P.roots.toFinset with hs
  set G := ∏ a ∈ s, (X - C a) ^ (P.rootMultiplicity a - 1) with hG
  have hm1 : ∀ a ∈ s, 1 ≤ P.rootMultiplicity a := fun a ha =>
    (rootMultiplicity_pos hP0).mpr (isRoot_of_mem_roots (Multiset.mem_toFinset.mp ha))
  have hPfac : P = C P.leadingCoeff * (G * ∏ a ∈ s, (X - C a)) := by
    conv_lhs => rw [hPs.eq_prod_roots]
    rw [Finset.prod_multiset_map_count, hG, ← prod_mul_distrib]
    congr 1
    refine prod_congr rfl fun a ha => ?_
    rw [count_roots, ← pow_succ, Nat.sub_add_cancel (hm1 a ha)]
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  have hN : apo n (G * ∏ a ∈ s, (X - C a)) W = 0 := by
    have : apo n P W = 0 := by rw [← eval_ssc_eq_apo n P Q hQ.le r]; exact h0
    rw [hPfac, apo_C_mul_left] at this
    exact (mul_eq_zero.mp this).resolve_left hlc
  have hE : ∀ i ∈ s, apo n (G * ∏ j ∈ s.erase i, (X - C j)) W = 0 := by
    intro i hi
    set T := C P.leadingCoeff * (G * ∏ j ∈ s.erase i, (X - C j)) with hT
    have hPT : P = (X - C i) * T := by
      rw [hPfac, ← mul_prod_erase s (fun a => X - C a) hi, hT]; ring
    have hT0 : T ≠ 0 := by intro h; rw [h, mul_zero] at hPT; exact hP0 hPT
    have hdvd : T ∣ P := Dvd.intro_left _ hPT.symm
    have hTs : T.Splits := hPs.of_dvd hP0 hdvd
    have hTn : T.natDegree ≤ n := hP ▸ natDegree_le_of_dvd hdvd hP0
    have := hell T hTn (stable_of_factor hPT hT0 hTs)
    rw [hT, apo_C_mul_left] at this
    exact (mul_eq_zero.mp this).resolve_left hlc
  have hsum_m : ∑ a ∈ s, P.rootMultiplicity a = n := by
    rw [← hP, hPs.natDegree_eq_card_roots, ← Multiset.toFinset_sum_count_eq]
    exact sum_congr rfl fun a _ => (count_roots P).symm
  have hsum_m1 : ∑ a ∈ s, (P.rootMultiplicity a - 1) + s.card = n := by
    rw [← hsum_m, card_eq_sum_ones, ← sum_add_distrib]
    exact sum_congr rfl fun a ha => Nat.sub_add_cancel (hm1 a ha)
  set l := s.toList.map fun a => (a, P.rootMultiplicity a - 1) with hl
  have hnd : (l.map Prod.fst).Nodup := by
    rw [hl, List.map_map]
    have : (Prod.fst ∘ fun a => (a, P.rootMultiplicity a - 1)) = id := rfl
    rw [this, List.map_id]; exact s.nodup_toList
  have hsum : (l.map fun p => p.2 + 1).sum ≤ n := by
    rw [hl, List.map_map, Finset.sum_map_toList]
    simp only [Function.comp]
    rw [← hsum_m]
    exact (sum_congr rfl fun a ha => Nat.sub_add_cancel (hm1 a ha)).le
  have hsnd : (l.map Prod.snd).sum = ∑ a ∈ s, (P.rootMultiplicity a - 1) := by
    rw [hl, List.map_map, Finset.sum_map_toList]; rfl
  have hprod : (l.map fun p => (X - C p.1) ^ p.2).prod = G := by
    rw [hl, List.map_map, Finset.prod_map_toList]; rfl
  obtain ⟨p, hp, hdvd⟩ := lstar_lemma l n W hnd hsum hW0 hWs hWn (by
    intro U hU
    rw [hprod]
    rw [hsnd] at hU
    exact apo_G_mul_eq_zero s G hN hE U (by lia))
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
  rw [Finset.mem_toList] at ha
  simp only at hdvd
  have hdvd' : (X - C a) ^ (n - (P.rootMultiplicity a - 1) + 1) ∣ Tr n r Q :=
    ((isUnit_C.mpr (IsUnit.mk0 _ hfac)).dvd_mul_left).mp hdvd
  have hmle : P.rootMultiplicity a ≤ n := hP ▸ rootMultiplicity_le_natDegree' P a
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h3 : X - C 0 ∣ Tr n r Q := (dvd_pow_self _ (by lia)).trans hdvd'
    rw [dvd_iff_isRoot, IsRoot, ← coeff_zero_eq_eval_zero, coeff_Tr r hQ.le, ite_eq_left (by lia),
      Nat.sub_zero] at h3
    rcases mul_eq_zero.mp h3 with h | h
    · exact pow_ne_zero n (neg_ne_zero.mpr hr) h
    · rw [← hQ] at h; exact hQ0 (leadingCoeff_eq_zero.mp h)
  have hQb := dvd_of_dvd_Tr hr ha0 hQ.le hdvd'
  have hle := (le_rootMultiplicity_iff hQ0).mpr hQb
  have hma := hm1 a ha
  have htot : n + 2 ≤ P.rootMultiplicity a + Q.rootMultiplicity (-r / a) := by lia
  refine ⟨a, -r / a, ha0, div_ne_zero (neg_ne_zero.mpr hr) ha0,
    isRoot_of_mem_roots (Multiset.mem_toFinset.mp ha),
    (rootMultiplicity_pos hQ0).mp (by lia), htot, by field_simp⟩

end SchurSzegoAristotle

/-!
## Kostov–Shapiro, Theorem 6(ii), for the composition `ssc`
-/

@[expose] public section

open Polynomial Finset

namespace SchurSzegoAristotle

local notation "ssc" => RealRooted.schurSzegoComp

/-- A root of multiplicity at least two of `P'` is a root of `P` (for split `P`). -/
private theorem lift_root {P : ℝ[X]} {N : ℕ} (hP : P.natDegree = N + 1) (hPs : P.Splits) {a : ℝ}
    (h2 : 2 ≤ P.derivative.rootMultiplicity a) :
    P.IsRoot a ∧ P.rootMultiplicity a = P.derivative.rootMultiplicity a + 1 := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  have hd0 := derivative_ne_zero' hP
  have h1 : P.derivative.IsRoot a := (rootMultiplicity_pos hd0).mp (by lia)
  have hdd := derivative_rootMultiplicity_of_root h1
  have h2' : P.derivative.derivative.IsRoot a := (rootMultiplicity_pos'.mp (by lia)).2
  have hPa : P.IsRoot a := eval_eq_zero_of_derivs hPs (by lia) h1 h2'
  have := derivative_rootMultiplicity_of_root hPa
  have := (rootMultiplicity_pos hP0).mpr hPa
  exact ⟨hPa, by lia⟩

private theorem main_ssc : ∀ (n : ℕ) (P Q : ℝ[X]), P.natDegree = n → P.Splits → Q.natDegree = n →
    Q.Splits → (∀ b ∈ Q.roots, b < 0) →
    ∀ r, r ≠ 0 → 1 < (ssc n P Q).rootMultiplicity r →
      ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ P.IsRoot a ∧ Q.IsRoot b ∧
        n < P.rootMultiplicity a + Q.rootMultiplicity b ∧ r = -(a * b) ∧
        (ssc n P Q).rootMultiplicity r = P.rootMultiplicity a + Q.rootMultiplicity b - n := by
  intro n
  induction n with
  | zero =>
    intro P Q _ _ _ _ _ r _ hK
    have h1 := rootMultiplicity_le_natDegree' (ssc 0 P Q) r
    have h2 := natDegree_ssc_le 0 P Q
    lia
  | succ N ih =>
    intro P Q hP hPs hQ hQs hneg r hr hK
    have hS0 : ssc (N + 1) P Q ≠ 0 := by
      intro h; rw [h, rootMultiplicity_zero] at hK; lia
    have hP0 : P ≠ 0 := by
      rintro rfl; apply hS0; ext k; simp
    have hQ0 : Q ≠ 0 := by
      rintro rfl; apply hS0; ext k; simp
    have hroot : (ssc (N + 1) P Q).IsRoot r := (rootMultiplicity_pos hS0).mp (by lia)
    have hrm1 := rootMultiplicity_ssc_derivative N P Q hroot
    by_cases hK3 : 2 < (ssc (N + 1) P Q).rootMultiplicity r
    · obtain ⟨a, b, ha, hb, -, -, hlt, hrab, hmult⟩ :=
        ih P.derivative Q.derivative (natDegree_derivative_eq' hP) (splits_derivative_real hPs)
          (natDegree_derivative_eq' hQ) (splits_derivative_real hQs)
          (derivative_roots_neg hQ hQs hneg) r hr (by lia)
      have hm := rootMultiplicity_le_natDegree' P.derivative a
      have hl := rootMultiplicity_le_natDegree' Q.derivative b
      rw [natDegree_derivative_eq' hP] at hm
      rw [natDegree_derivative_eq' hQ] at hl
      obtain ⟨hPa, hma⟩ := lift_root hP hPs (a := a) (by lia)
      obtain ⟨hQb, hlb⟩ := lift_root hQ hQs (a := b) (by lia)
      exact ⟨a, b, ha, hb, hPa, hQb, by lia, hrab, by lia⟩
    · have hK2 : (ssc (N + 1) P Q).rootMultiplicity r = 2 := by lia
      set S := ssc (N + 1) P Q with hS
      have hd1 := derivative_rootMultiplicity_of_root hroot
      obtain ⟨hd0, h1⟩ := rootMultiplicity_pos'.mp (show 0 < S.derivative.rootMultiplicity r by
        lia)
      have hdd := derivative_rootMultiplicity_of_root h1
      have h2 : S.derivative.derivative.eval r ≠ 0 := by
        intro h
        by_cases hdd0 : S.derivative.derivative = 0
        · have hc := Polynomial.derivative_eq_zero.mp hdd0
          rw [eq_C_of_natDegree_eq_zero hc] at h1 hd0
          simp only [IsRoot, eval_C] at h1
          rw [h1, C_0] at hd0
          exact hd0 rfl
        · have := (rootMultiplicity_pos hdd0).mpr h
          lia
      obtain ⟨a, b, ha, hb, hPa, hQb, hge, hrab⟩ :=
        double_root_forced hP hPs hQ hQs hneg hP0 hQ0 hr hroot h1 h2
      have hlow := forced_lower (N + 1) P Q hP hQ hP0 hQ0 a b hb (by lia)
      rw [← hrab] at hlow
      change _ ≤ S.rootMultiplicity r at hlow
      exact ⟨a, b, ha, hb, hPa, hQb, by lia, hrab, by lia⟩

end SchurSzegoAristotle

open Polynomial

namespace RealRooted

/-!
## Nonzero multiple roots of a Schur--Szegő composition

This file is intentionally self-contained for Aristotle.  The composition is
the fixed-degree operation used in `RealRooted.Hadamard.Basic`: coefficients
are divided by the binomial coefficient, and terms above degree `n` are
omitted by the finite sum.
-/

/-!
This is Kostov--Shapiro, C. R. Acad. Sci. Paris 343 (2006), Theorem 6(ii),
using their Proposition 4.  The proof by perturbation through upper-half-plane
stability and Lagrange interpolation was found by Aristotle.  Proposition 4
identifies the A-roots: if `a` and `b` are nonzero roots of the inputs with
multiplicities `m` and `l`, and `m + l > n`, then `-(a * b)` has multiplicity
`m + l - n` in the composition.  The theorem says every other nonzero root is
simple.

The paper's proof is by contradiction and induction on input multiplicities.
In the basic case, when the relevant input has distinct nonzero roots, a
hypothetical multiple B-root can be destroyed by a sufficiently small
perturbation of the constant coefficient.  The perturbed input remains
hyperbolic, while a suitable perturbation of the output acquires a nonreal
conjugate pair (for multiplicity two), or a nonreal configuration after
perturbing the derivative (for higher multiplicity), contradicting the
Schur--Szegő real-rootedness theorem.

For the induction step, if `c` is a repeated nonzero root of `P`, write
`P_c = P / (X - c)` and use the hyperbolic family
`P_δ = P + δ P_c`; this leaves the `(m - 1)`-fold root at `c` and adds a
simple root at `c - δ`.  Put `U_c = P_c *_n Q`.  If `U_c` does not vanish at
the alleged B-root, choose the sign of small `δ` to make the output
non-hyperbolic.  If `U_c` and its derivative both vanish there, the same
multiple B-root persists while the multiplicity of `c` decreases.  If
`U_c` vanishes but its derivative does not, and two source roots can be
split, use the two-parameter family
`P + δ P_c + ε P_d + δε P_{cd}` and choose `δ` as a function of `ε` so the
output remains multiply rooted while lowering a source multiplicity.

The only terminal case has one multiple (or zero) source root and all other
nonzero source roots simple.  A suitable linear combination then produces
`(X - c)^n`, or `(X - h)^ν (X - c)^(n - ν)`, whose composition with `Q` is
explicit.  Proposition 4 contradicts the alleged B-root in both the strict
and equality cases.  The zero output root is treated separately; it is why
the theorem below explicitly assumes `r ≠ 0`.
-/

/-- Every nonzero multiple output root is a forced product. -/
theorem exists_forced_factors_of_rootMultiplicity_schurSzegoComp
    {n : ℕ} {P Q : ℝ[X]} (hP : P.natDegree = n) (hPs : P.Splits)
    (hQ : Q.natDegree = n) (hQs : Q.Splits) (hneg : ∀ b ∈ Q.roots, b < 0) :
    ∀ r, r ≠ 0 → 1 < (schurSzegoComp n P Q).rootMultiplicity r →
      ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ P.IsRoot a ∧ Q.IsRoot b ∧
        n < P.rootMultiplicity a + Q.rootMultiplicity b ∧ r = -(a * b) ∧
        (schurSzegoComp n P Q).rootMultiplicity r =
          P.rootMultiplicity a + Q.rootMultiplicity b - n :=
  SchurSzegoAristotle.main_ssc n P Q hP hPs hQ hQs hneg

/-- Every other nonzero root of the composition is simple. -/
theorem rootMultiplicity_le_one_of_not_forced_schurSzegoComp
    {n : ℕ} {P Q : ℝ[X]} (hP : P.natDegree = n) (hPs : P.Splits)
    (hQ : Q.natDegree = n) (hQs : Q.Splits) (hneg : ∀ b ∈ Q.roots, b < 0)
    {r : ℝ} (hr : r ≠ 0)
    (hnot : ∀ a b : ℝ, a ≠ 0 → b ≠ 0 → P.IsRoot a → Q.IsRoot b →
      n < P.rootMultiplicity a + Q.rootMultiplicity b → r ≠ -(a * b)) :
    (schurSzegoComp n P Q).rootMultiplicity r ≤ 1 := by
  by_contra hle
  have hmult : 1 < (schurSzegoComp n P Q).rootMultiplicity r := by lia
  obtain ⟨a, b, ha, hb, hPa, hQb, hsum, hrab, _⟩ :=
    exists_forced_factors_of_rootMultiplicity_schurSzegoComp hP hPs hQ hQs hneg r hr hmult
  exact hnot a b ha hb hPa hQb hsum hrab

end RealRooted
