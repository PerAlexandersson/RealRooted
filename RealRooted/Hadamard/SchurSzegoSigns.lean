import RealRooted.Hadamard.Grace
import RealRooted.Hadamard.SchurSzegoMultiplicity

/-!
# Sign counts for the finite Schur–Szegő composition

Kostov and Shapiro (*On the Schur–Szegő composition of polynomials*, C. R. Acad. Sci. Paris
343 (2006), Prop. 5): if `P` has degree `n` and only real roots, and `Q` has degree `n` and only
strictly negative roots, then `P *ₙ Q` has the same numbers of positive, zero and negative roots
as `P`, counted with multiplicity.

We do not follow their continuity argument.  Instead:

* the coefficients of `Q` all have the sign of its leading coefficient (`Q` has negative
  roots), so `P *ₙ Q` and `P` have the same coefficient signs up to a global sign; hence the
  same support, natural trailing degree (zero-root multiplicity) and sign variations, also after
  `X ↦ -X`;
* `signVariations p + signVariations (p.comp (-X)) + p.natTrailingDegree ≤ p.natDegree` for any
  real polynomial (`signVariations_add_signVariations_comp_neg_X_le`);
* together with Descartes' rule of signs this makes Descartes exact for real-rooted polynomials.

The real-rootedness of `P *ₙ Q` (finite Schur–Szegő theorem) is taken as an explicit hypothesis
in `schurSzegoComp_roots_sign_counts`; the zero-root statement needs no such hypothesis.
-/

open Polynomial

namespace RealRooted

/-! ### Generic polynomial facts -/

private theorem coeff_comp_neg_X (p : ℝ[X]) (k : ℕ) :
    (p.comp (-X)).coeff k = (-1) ^ k * p.coeff k := by
  rw [show (-X : ℝ[X]) = C (-1) * X by simp, comp_C_mul_X_coeff, mul_comm]

private theorem natDegree_comp_neg_X (p : ℝ[X]) : (p.comp (-X)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_neg, natDegree_X, mul_one]

private theorem eraseLead_comp_neg_X (p : ℝ[X]) :
    (p.comp (-X)).eraseLead = p.eraseLead.comp (-X) := by
  ext k
  rw [eraseLead_coeff, coeff_comp_neg_X, coeff_comp_neg_X, eraseLead_coeff, natDegree_comp_neg_X]
  split_ifs <;> simp

theorem natTrailingDegree_eraseLead_of_ne_zero {p : ℝ[X]} (h : p.eraseLead ≠ 0) :
    p.eraseLead.natTrailingDegree = p.natTrailingDegree := by
  have hp : p ≠ 0 := by
    rintro rfl
    simp at h
  have hlt : p.eraseLead.natTrailingDegree < p.natDegree :=
    lt_natDegree_of_mem_eraseLead_support (natTrailingDegree_mem_support_of_nonzero h)
  have hle : p.natTrailingDegree ≤ p.eraseLead.natTrailingDegree := by
    apply natTrailingDegree_le_of_ne_zero
    rw [← eraseLead_coeff_of_ne _ hlt.ne]
    exact coeff_natTrailingDegree_ne_zero.mpr h
  apply le_antisymm _ hle
  apply natTrailingDegree_le_of_ne_zero
  rw [eraseLead_coeff_of_ne _ (hle.trans_lt hlt).ne]
  exact coeff_natTrailingDegree_ne_zero.mpr hp

private theorem ite_add_ite_sign_le {a b : ℝ} (ha : a ≠ 0) {d e : ℕ} (hde : e < d) :
    ((if SignType.sign a = -SignType.sign b then 1 else 0) +
      if SignType.sign ((-1) ^ d * a) = -SignType.sign ((-1) ^ e * b) then 1 else 0) ≤
      d - e := by
  rcases Nat.lt_or_ge (e + 1) d with h | h
  · split_ifs <;> lia
  · obtain rfl : d = e + 1 := by lia
    have hs : SignType.sign a ≠ 0 := by simpa using ha
    rw [pow_succ, mul_neg_one, neg_mul]
    rcases neg_one_pow_eq_or ℝ e with he | he <;>
      · rw [he, Nat.add_sub_cancel_left]
        simp only [one_mul, neg_mul, neg_neg, Left.sign_neg]
        generalize SignType.sign a = s at hs
        generalize SignType.sign b = t
        revert hs
        cases s <;> cases t <;> decide

/-- Descartes-type bound: the sign variations of `p` and of `p(-X)`, together with the
multiplicity of the root `0`, do not exceed the degree. -/
theorem signVariations_add_signVariations_comp_neg_X_le (p : ℝ[X]) :
    p.signVariations + (p.comp (-X)).signVariations + p.natTrailingDegree ≤ p.natDegree := by
  induction hd : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have hq : p.comp (-X) ≠ 0 := comp_neg_X_eq_zero_iff.not.mpr hp
  rw [signVariations_eq_eraseLead_add_ite hp, signVariations_eq_eraseLead_add_ite hq,
    eraseLead_comp_neg_X, comp_neg_X_leadingCoeff_eq, comp_neg_X_leadingCoeff_eq]
  rcases eq_or_ne p.eraseLead 0 with he | he
  · have hs : SignType.sign p.leadingCoeff ≠ 0 := by simpa using hp
    simpa [he, hs, hp, hd] using p.natTrailingDegree_le_natDegree
  · have hlt := (eraseLead_natDegree_lt_or_eraseLead_eq_zero p).resolve_right he
    have := ih _ (hd ▸ hlt) p.eraseLead rfl
    have h2 := ite_add_ite_sign_le (b := p.eraseLead.leadingCoeff)
      (leadingCoeff_ne_zero.mpr hp) hlt
    rw [natTrailingDegree_eraseLead_of_ne_zero he] at this
    lia

/-- A multiset of reals splits into its positive elements, its zeros and its negative
elements. -/
theorem card_eq_countP_pos_add_count_zero_add_countP_neg (s : Multiset ℝ) :
    Multiset.card s = s.countP (0 < ·) + s.count 0 + s.countP (· < 0) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, Multiset.countP_cons, Multiset.countP_cons, Multiset.count_cons, ih]
    split_ifs <;> grind

/-- Negative roots of `p` are the positive roots of `p(-X)`. -/
theorem countP_neg_roots_eq_countP_pos_roots_comp_neg_X (p : ℝ[X]) :
    p.roots.countP (· < 0) = (p.comp (-X)).roots.countP (0 < ·) := by
  rw [roots_comp_neg_X, Multiset.countP_map, ← Multiset.countP_eq_card_filter]
  exact Multiset.countP_congr rfl fun x _ => propext neg_pos.symm

/-- **Descartes' rule is exact for real-rooted polynomials**: the number of positive roots is
the number of sign variations, and the number of negative roots is the number of sign
variations of `p(-X)`. -/
theorem countP_roots_eq_signVariations_of_splits {p : ℝ[X]} (hp : p.Splits) :
    p.roots.countP (0 < ·) = p.signVariations ∧
      p.roots.countP (· < 0) = (p.comp (-X)).signVariations := by
  have h1 := roots_countP_pos_le_signVariations p
  have h2 := roots_countP_pos_le_signVariations (p.comp (-X))
  have h3 := signVariations_add_signVariations_comp_neg_X_le p
  have h4 := card_eq_countP_pos_add_count_zero_add_countP_neg p.roots
  rw [← hp.natDegree_eq_card_roots, count_roots, rootMultiplicity_eq_natTrailingDegree'] at h4
  rw [← countP_neg_roots_eq_countP_pos_roots_comp_neg_X] at h2
  lia

/-! ### Coefficients of polynomials with negative roots -/

theorem coeff_multiset_prod_X_sub_C_pos {s : Multiset ℝ} (hs : ∀ b ∈ s, b < 0) {k : ℕ}
    (hk : k ≤ Multiset.card s) : 0 < (s.map (fun b => X - C b)).prod.coeff k := by
  induction s using Multiset.induction_on generalizing k with
  | empty =>
    rw [Multiset.card_zero, Nat.le_zero] at hk
    simp [hk]
  | cons a s ih =>
    have ha : a < 0 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ b ∈ s, b < 0 := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    rw [Multiset.card_cons] at hk
    rw [Multiset.map_cons, Multiset.prod_cons, mul_comm]
    rcases k with _ | k
    · rw [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
      exact mul_pos (ih hs' (Nat.zero_le _)) (neg_pos.mpr ha)
    · rw [coeff_mul_X_sub_C]
      have h1 := ih hs' (k := k) (by lia)
      rcases Nat.lt_or_ge (Multiset.card s) (k + 1) with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (n := k + 1)
          (by rwa [natDegree_multiset_prod_X_sub_C_eq_card])]
        linarith
      · nlinarith [ih hs' h]

/-- A nonzero real polynomial with only (real) negative roots has all its coefficients of the
sign of the leading coefficient, up to the degree. -/
theorem leadingCoeff_mul_coeff_pos_of_roots_neg {Q : ℝ[X]} (hQs : Q.Splits) (hQ0 : Q ≠ 0)
    (hneg : ∀ b ∈ Q.roots, b < 0) {k : ℕ} (hk : k ≤ Q.natDegree) :
    0 < Q.leadingCoeff * Q.coeff k := by
  have h : Q.coeff k = Q.leadingCoeff * (Q.roots.map (fun b => X - C b)).prod.coeff k := by
    conv_lhs => rw [hQs.eq_prod_roots]
    rw [coeff_C_mul]
  rw [h, ← mul_assoc]
  exact mul_pos (mul_self_pos.mpr (leadingCoeff_ne_zero.mpr hQ0))
    (coeff_multiset_prod_X_sub_C_pos hneg (hk.trans hQs.natDegree_eq_card_roots.le))

/-! ### Sign patterns of the composition -/

theorem support_eq_of_sign_coeff {p q : ℝ[X]}
    (h : ∀ k, SignType.sign (p.coeff k) = SignType.sign (q.coeff k)) :
    p.support = q.support := by
  ext k
  rw [mem_support_iff, mem_support_iff, ← sign_ne_zero, h, sign_ne_zero]

/-- Sign variations only depend on the signs of the coefficients. -/
theorem signVariations_eq_of_sign_coeff {p q : ℝ[X]}
    (h : ∀ k, SignType.sign (p.coeff k) = SignType.sign (q.coeff k)) :
    p.signVariations = q.signVariations := by
  have hdeg : p.degree = q.degree := by
    simp only [degree, support_eq_of_sign_coeff h]
  have hfun : SignType.sign ∘ p.coeff = SignType.sign ∘ q.coeff := funext h
  unfold Polynomial.signVariations coeffList List.signVariations
  rw [hdeg, List.map_map, List.map_map, hfun]

theorem sign_coeff_C_mul_schurSzegoComp {n : ℕ} {P Q : ℝ[X]} (hP : P.natDegree ≤ n)
    (hQ : ∀ k ≤ n, 0 < Q.leadingCoeff * Q.coeff k) (k : ℕ) :
    SignType.sign ((C Q.leadingCoeff * schurSzegoComp n P Q).coeff k) =
      SignType.sign (P.coeff k) := by
  rw [coeff_C_mul, coeff_schurSzegoComp_eq_div]
  rcases le_or_gt k n with hk | hk
  · have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
    rw [show Q.leadingCoeff * (P.coeff k * Q.coeff k / n.choose k) =
        P.coeff k * (Q.leadingCoeff * Q.coeff k / n.choose k) by ring, sign_mul,
      sign_pos (div_pos (hQ k hk) hc), mul_one]
  · rw [coeff_eq_zero_of_natDegree_lt (hP.trans_lt hk)]
    simp

/-- If `Q` has coefficients of constant sign up to degree `n`, composition with `Q` preserves
the number of sign variations. -/
theorem signVariations_schurSzegoComp {n : ℕ} {P Q : ℝ[X]} (hP : P.natDegree ≤ n)
    (hQ : ∀ k ≤ n, 0 < Q.leadingCoeff * Q.coeff k) :
    (schurSzegoComp n P Q).signVariations = P.signVariations := by
  have hlc : Q.leadingCoeff ≠ 0 := by
    intro h
    simpa [h] using hQ 0 (Nat.zero_le n)
  rw [← signVariations_C_mul _ hlc]
  exact signVariations_eq_of_sign_coeff (sign_coeff_C_mul_schurSzegoComp hP hQ)

/-- If `Q` has coefficients of constant sign up to degree `n`, composition with `Q` preserves
the coefficient support. -/
theorem support_schurSzegoComp {n : ℕ} {P Q : ℝ[X]} (hP : P.natDegree ≤ n)
    (hQ : ∀ k ≤ n, 0 < Q.leadingCoeff * Q.coeff k) :
    (schurSzegoComp n P Q).support = P.support := by
  have hlc : Q.leadingCoeff ≠ 0 := by
    intro h
    simpa [h] using hQ 0 (Nat.zero_le n)
  rw [← support_eq_of_sign_coeff (sign_coeff_C_mul_schurSzegoComp hP hQ)]
  ext k
  simp [hlc]

/-- Composition commutes with the reflection `X ↦ -X` of the first argument. -/
theorem schurSzegoComp_comp_neg_X (n : ℕ) (P Q : ℝ[X]) :
    (schurSzegoComp n P Q).comp (-X) = schurSzegoComp n (P.comp (-X)) Q := by
  ext k
  rw [coeff_comp_neg_X, coeff_schurSzegoComp_eq_div, coeff_schurSzegoComp_eq_div, coeff_comp_neg_X]
  ring

/-! ### Main results -/

/-- **Zero roots of the Schur–Szegő composition.**  If `P` has degree at most `n` and `Q` has
degree `n` with only real, strictly negative roots, then `0` is a root of `P *ₙ Q` of the same
multiplicity as for `P`.  No real-rootedness of `P` is needed. -/
theorem count_zero_roots_schurSzegoComp {n : ℕ} {P Q : ℝ[X]} (hP : P.natDegree ≤ n)
    (hQ : Q.natDegree = n) (hQs : Q.Splits) (hneg : ∀ b ∈ Q.roots, b < 0) :
    (schurSzegoComp n P Q).roots.count 0 = P.roots.count 0 := by
  rcases eq_or_ne Q 0 with rfl | hQ0
  · have hP0 : P = C (P.coeff 0) := eq_C_of_natDegree_eq_zero (by rw [natDegree_zero] at hQ; lia)
    rw [schurSzegoComp_zero_right, hP0, roots_C, roots_zero]
  have hQc : ∀ k ≤ n, 0 < Q.leadingCoeff * Q.coeff k :=
    fun k hk => leadingCoeff_mul_coeff_pos_of_roots_neg hQs hQ0 hneg (hQ ▸ hk)
  rw [count_roots, count_roots, rootMultiplicity_eq_natTrailingDegree',
    rootMultiplicity_eq_natTrailingDegree']
  simp only [natTrailingDegree, trailingDegree, support_schurSzegoComp hP hQc]

/-- **Kostov–Shapiro sign counts.**  Let `P` have degree `n` and only real roots, and let `Q`
have degree `n` and only real, strictly negative roots.  Assuming that `P *ₙ Q` is real-rooted
(the finite Schur–Szegő theorem, taken here as the hypothesis `hS`), `P *ₙ Q` has the same
numbers of positive, zero and negative roots as `P`, counted with multiplicity. -/
theorem schurSzegoComp_roots_sign_counts {n : ℕ} {P Q : ℝ[X]} (hP : P.natDegree = n)
    (hPs : P.Splits) (hQ : Q.natDegree = n) (hQs : Q.Splits) (hneg : ∀ b ∈ Q.roots, b < 0)
    (hS : (schurSzegoComp n P Q).Splits) :
    (schurSzegoComp n P Q).roots.countP (0 < ·) = P.roots.countP (0 < ·) ∧
      (schurSzegoComp n P Q).roots.count 0 = P.roots.count 0 ∧
      (schurSzegoComp n P Q).roots.countP (· < 0) = P.roots.countP (· < 0) := by
  rcases eq_or_ne Q 0 with rfl | hQ0
  · have hP0 : P = C (P.coeff 0) := eq_C_of_natDegree_eq_zero (by rw [natDegree_zero] at hQ; lia)
    rw [schurSzegoComp_zero_right, hP0, roots_C, roots_zero]
    exact ⟨rfl, rfl, rfl⟩
  have hQc : ∀ k ≤ n, 0 < Q.leadingCoeff * Q.coeff k :=
    fun k hk => leadingCoeff_mul_coeff_pos_of_roots_neg hQs hQ0 hneg (hQ ▸ hk)
  obtain ⟨hS1, hS2⟩ := countP_roots_eq_signVariations_of_splits hS
  obtain ⟨hP1, hP2⟩ := countP_roots_eq_signVariations_of_splits hPs
  refine ⟨?_, count_zero_roots_schurSzegoComp hP.le hQ hQs hneg, ?_⟩
  · rw [hS1, hP1, signVariations_schurSzegoComp hP.le hQc]
  · rw [hS2, hP2, schurSzegoComp_comp_neg_X,
      signVariations_schurSzegoComp (by rw [natDegree_comp_neg_X, hP]) hQc]

/-- If `Q` splits with only negative roots, the Schur–Szegő composition with any real-rooted
`P` of degree at most `n` is real-rooted. -/
theorem splits_schurSzegoComp_of_roots_neg {n : ℕ} {P Q : ℝ[X]} (hP : P.natDegree ≤ n)
    (hPs : P.Splits) (hQ : Q.natDegree ≤ n) (hQs : Q.Splits) (hneg : ∀ b ∈ Q.roots, b < 0) :
    (schurSzegoComp n P Q).Splits := by
  rcases eq_or_ne Q 0 with rfl | hQ0
  · simp [schurSzegoComp_zero_right]
  set c := Q.leadingCoeff
  have hc : c ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
  have hPF : IsPFPolynomial (C c⁻¹ * Q) := by
    refine IsPFPolynomial.of_realRooted_nonneg (fun k => ?_) ((Splits.C _).mul hQs)
    rw [coeff_C_mul]
    rcases le_or_gt k Q.natDegree with hk | hk
    · have hpos := leadingCoeff_mul_coeff_pos_of_roots_neg hQs hQ0 hneg hk
      have heq : c⁻¹ * Q.coeff k = c * Q.coeff k / c ^ 2 := by
        field_simp
      rw [heq]
      positivity
    · rw [coeff_eq_zero_of_natDegree_lt hk, mul_zero]
  have h := finiteSchurSzegoComposition hPF ((natDegree_C_mul_le _ _).trans hQ) hP hPs
  rw [schurSzegoComp_C_mul_left, schurSzegoComp_comm] at h
  have hS : schurSzegoComp n P Q = C c * (C c⁻¹ * schurSzegoComp n P Q) := by
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
  rcases h with h | h
  · rw [hS, h, mul_zero]
    exact Splits.zero
  · rw [hS]
    exact (Splits.C _).mul h

/-- **Kostov–Shapiro**: if `P` is real-rooted of degree `n` and `Q` of degree `n` has only
negative roots, the Schur–Szegő composition has as many positive, zero and negative roots as
`P`, counted with multiplicity. -/
theorem schurSzegoComp_roots_sign_counts_of_roots_neg {n : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree = n) (hPs : P.Splits) (hQ : Q.natDegree = n) (hQs : Q.Splits)
    (hneg : ∀ b ∈ Q.roots, b < 0) :
    (schurSzegoComp n P Q).roots.countP (0 < ·) = P.roots.countP (0 < ·) ∧
      (schurSzegoComp n P Q).roots.count 0 = P.roots.count 0 ∧
      (schurSzegoComp n P Q).roots.countP (· < 0) = P.roots.countP (· < 0) :=
  schurSzegoComp_roots_sign_counts hP hPs hQ hQs hneg
    (splits_schurSzegoComp_of_roots_neg hP.le hPs hQ.le hQs hneg)

end RealRooted
