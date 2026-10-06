import RealRooted.GarloffWagner.Algebra

/-!
# Garloff--Wagner iterated transforms

The `J^k ∘ L` transform, its factor identities, and the Theorem 11
real-rootedness and interlacing transport.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The iterated transform `J^k ∘ L`: divide the coefficients of `p` by
factorials and then integrate `k` times, so that the coefficient of
`X ^ (n + k)` is `p.coeff n / (n + k)!`. -/
def divFactorialShift (k : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (antiderivative^[k]) (divFactorial p)

@[deprecated (since := "2026-10-06")]
alias gwJL := divFactorialShift

@[simp] theorem divFactorialShift_zero_apply (p : ℝ[X]) :
    divFactorialShift 0 p = divFactorial p :=
  rfl

@[deprecated (since := "2026-10-06")]
alias gwJL_zero_apply := divFactorialShift_zero_apply

theorem divFactorialShift_succ (k : ℕ) (p : ℝ[X]) :
    divFactorialShift (k + 1) p = antiderivative (divFactorialShift k p) := by
  rw [divFactorialShift, divFactorialShift, Function.iterate_succ_apply']

@[deprecated (since := "2026-10-06")]
alias gwJL_succ := divFactorialShift_succ

@[simp] theorem divFactorialShift_zero (k : ℕ) :
    divFactorialShift k (0 : ℝ[X]) = 0 := by
  induction k with
  | zero =>
      simp [divFactorialShift, divFactorial_zero]
  | succ k ih =>
      rw [divFactorialShift_succ, ih, antiderivative_zero]

theorem divFactorialShift_add (k : ℕ) (p q : ℝ[X]) :
    divFactorialShift k (p + q) = divFactorialShift k p + divFactorialShift k q := by
  induction k with
  | zero =>
      simp [divFactorialShift, divFactorial_add]
  | succ k ih =>
      rw [divFactorialShift_succ, divFactorialShift_succ, divFactorialShift_succ, ih,
        antiderivative_add]

theorem divFactorialShift_sub (k : ℕ) (p q : ℝ[X]) :
    divFactorialShift k (p - q) = divFactorialShift k p - divFactorialShift k q := by
  induction k with
  | zero =>
      simp [divFactorialShift, divFactorial_sub]
  | succ k ih =>
      rw [divFactorialShift_succ, divFactorialShift_succ, divFactorialShift_succ, ih,
        antiderivative_sub]

theorem divFactorialShift_C_mul (a : ℝ) (k : ℕ) (p : ℝ[X]) :
    divFactorialShift k (C a * p) = C a * divFactorialShift k p := by
  induction k with
  | zero =>
      simp [divFactorialShift, divFactorial_C_mul]
  | succ k ih =>
      rw [divFactorialShift_succ, divFactorialShift_succ, ih, antiderivative_C_mul]

theorem divFactorialShift_list_sum (k : ℕ) :
    ∀ l : List ℝ[X], divFactorialShift k l.sum = (l.map (divFactorialShift k)).sum
  | [] => by simp
  | p :: l => by
      simp [divFactorialShift_add, divFactorialShift_list_sum k l]

theorem divFactorialShift_weightedSum (k : ℕ) :
    ∀ l : List (ℝ × ℝ[X]),
      divFactorialShift k (weightedSum l) =
        weightedSum (l.map fun ap => (ap.1, divFactorialShift k ap.2))
  | [] => by simp
  | (a, p) :: l => by
      simp [weightedSum_cons, divFactorialShift_add, divFactorialShift_C_mul,
        divFactorialShift_weightedSum k l]

theorem divFactorialShift_eq_zero_iff (k : ℕ) (p : ℝ[X]) :
    divFactorialShift k p = 0 ↔ p = 0 := by
  induction k with
  | zero =>
      simp [divFactorialShift, divFactorial_eq_zero_iff]
  | succ k ih =>
      rw [divFactorialShift_succ, antiderivative_eq_zero_iff, ih]

theorem divFactorialShift_ne_zero_iff (k : ℕ) (p : ℝ[X]) :
    divFactorialShift k p ≠ 0 ↔ p ≠ 0 := by
  rw [ne_eq, ne_eq, divFactorialShift_eq_zero_iff]

theorem natDegree_divFactorialShift (k : ℕ) {p : ℝ[X]} (hp : p ≠ 0) :
    (divFactorialShift k p).natDegree = p.natDegree + k := by
  induction k with
  | zero =>
      simp [divFactorialShift, natDegree_divFactorial hp]
  | succ k ih =>
      rw [divFactorialShift_succ, natDegree_antiderivative, ih]
      · ring
      · exact (divFactorialShift_ne_zero_iff k p).2 hp

theorem derivative_divFactorialShift_succ (k : ℕ) (p : ℝ[X]) :
    derivative (divFactorialShift (k + 1) p) = divFactorialShift k p := by
  rw [divFactorialShift_succ, derivative_antiderivative]

theorem HasPosLeadingCoeff.divFactorialShift {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) (k : ℕ) :
    HasPosLeadingCoeff (divFactorialShift k p) := by
  induction k with
  | zero =>
      simpa [divFactorialShift] using hp.divFactorial
  | succ k ih =>
      rw [divFactorialShift_succ]
      exact ih.antiderivative

theorem HasNonnegCoeffs.divFactorialShift {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (k : ℕ) :
    HasNonnegCoeffs (divFactorialShift k p) := by
  induction k with
  | zero =>
      simpa [divFactorialShift] using hp.divFactorial
  | succ k ih =>
      rw [divFactorialShift_succ]
      exact ih.antiderivative

/-- The algebraic induction step in Garloff--Wagner, Theorem 11. -/
theorem divFactorialShift_X_sub_C_mul (k : ℕ) (u : ℝ) (f : ℝ[X]) :
    divFactorialShift k ((X - C u) * f) =
      divFactorialShift (k + 1) f - C u * divFactorialShift k f := by
  induction k with
  | zero =>
      simp only [divFactorialShift_zero_apply]
      rw [sub_mul, divFactorial_sub, divFactorial_X_mul, divFactorial_C_mul, divFactorialShift_succ,
        divFactorialShift_zero_apply]
  | succ k ih =>
      rw [divFactorialShift_succ, ih, antiderivative_sub, antiderivative_C_mul,
        ← divFactorialShift_succ, ← divFactorialShift_succ]

/-- The `k = 0` form of `divFactorialShift_X_sub_C_mul`, matching the first transport step
in Garloff--Wagner's proof of Theorem 4(b). -/
theorem divFactorial_X_sub_C_mul (u : ℝ) (f : ℝ[X]) :
    divFactorial ((X - C u) * f) = antiderivative (divFactorial f) - C u * divFactorial f := by
  simpa [divFactorialShift_zero_apply, divFactorialShift_succ] using
    divFactorialShift_X_sub_C_mul 0 u f

/-- Derivative of the preceding `L`-transport identity. -/
theorem derivative_divFactorial_X_sub_C_mul (u : ℝ) (f : ℝ[X]) :
    derivative (divFactorial ((X - C u) * f)) =
      divFactorial f - C u * derivative (divFactorial f) := by
  rw [divFactorial_X_sub_C_mul, derivative_sub, derivative_C_mul, derivative_antiderivative]

/-- Algebraic expansion of the two-linear-factor ordinary Hadamard product
used in Garloff--Wagner's double-deleted paragraph of Theorem 4(b). -/
theorem hadamardProduct_X_sub_C_mul_X_sub_C_mul_eq
    (j u : ℝ) (g q : ℝ[X]) :
    hadamardProduct ((X - C j) * g) ((X - C u) * q) =
      X * factorialHadamardProduct g (divFactorial q - C u * derivative (divFactorial q)) -
        C j *
          factorialHadamardProduct g (antiderivative (divFactorial q) - C u * divFactorial q) := by
  rw [← factorialHadamardProduct_divFactorial_right ((X - C j) * g) ((X - C u) * q)]
  rw [divFactorial_X_sub_C_mul, factorialHadamardProduct_X_sub_C_mul_left]
  rw [derivative_sub, derivative_C_mul, derivative_antiderivative]
  rw [factorialHadamardProduct_comm (divFactorial q - C u * derivative (divFactorial q)) g]

/-- The same induction step written as `(1 - uD) J^(k+1) L f`. -/
theorem divFactorialShift_X_sub_C_mul_eq_sub_derivative (k : ℕ) (u : ℝ) (f : ℝ[X]) :
    divFactorialShift k ((X - C u) * f) =
      divFactorialShift (k + 1) f - C u * derivative (divFactorialShift (k + 1) f) := by
  rw [divFactorialShift_X_sub_C_mul, derivative_divFactorialShift_succ]

/-- Garloff--Wagner's Theorem 11 induction step in `tDeriv` form. -/
theorem divFactorialShift_X_sub_C_mul_eq_tDeriv (k : ℕ) (u : ℝ) (f : ℝ[X]) :
    divFactorialShift k ((X - C u) * f) = tDeriv u (divFactorialShift (k + 1) f) := by
  rw [divFactorialShift_X_sub_C_mul_eq_sub_derivative]
  simp [tDeriv]

/-- Real-rootedness part of the Garloff--Wagner Theorem 11 induction step. -/
theorem divFactorialShift_X_sub_C_mul_splits {k : ℕ} {u : ℝ} {f : ℝ[X]}
    (h : (divFactorialShift (k + 1) f).Splits) :
    (divFactorialShift k ((X - C u) * f)).Splits := by
  rw [divFactorialShift_X_sub_C_mul_eq_tDeriv]
  exact splits_tDeriv_all h

/-- All-real derivative-shift form of Garloff--Wagner formula (3):
if `p` is nonconstant and real-rooted, then `p'` precedes `p - ε p'` for
every real `ε`. -/
theorem derivative_strictInterl_tDeriv_of_splits {eps : ℝ} {p : ℝ[X]}
    (hp0 : p ≠ 0) (hp : p.Splits) (hdeg : 1 ≤ p.natDegree) :
    StrictInterl p.derivative (tDeriv eps p) := by
  by_cases hdeg1 : p.natDegree = 1
  · exact derivative_strictInterl_tDeriv_of_natDegree_one hdeg1
  have hdeg2 : 2 ≤ p.natDegree := by lia
  have hder : Interlaces p.derivative p := derivative_interlaces_of_natDegree_ne_zero hp (by lia)
  have hder_rr : p.derivative ≠ 0 ∧ p.derivative.Splits := hder.2.1
  have hT_rr : tDeriv eps p ≠ 0 ∧ (tDeriv eps p).Splits :=
    ⟨tDeriv_ne_zero hp0, splits_tDeriv_all hp⟩
  have hall : AllComboRealRooted p.derivative (tDeriv eps p) := by
    intro α β
    by_cases hβ : β = 0
    · subst β
      by_cases hα : α = 0
      · simp [hα]
      · simpa using (isRealRooted_C_mul hder_rr.1 hder_rr.2 hα).2
    · have hcombo :
          C α * p.derivative + C β * tDeriv eps p =
            C β * tDeriv (eps - β⁻¹ * α) p := by
        ext n
        simp only [tDeriv, coeff_add, coeff_sub, coeff_C_mul]
        field_simp [hβ]
        ring
      rw [hcombo]
      exact (Polynomial.Splits.C (R := ℝ) β).mul (splits_tDeriv_all hp)
  have hsucc :
      (tDeriv eps p).natDegree = p.derivative.natDegree + 1 := by
    rw [natDegree_tDeriv, p.natDegree_derivative]
    lia
  have hstrictInterl_or :
      StrictInterl p.derivative (tDeriv eps p) ∨
        StrictInterl (tDeriv eps p) p.derivative :=
    strictInterl_of_allComboRealRooted hder_rr.1 hder_rr.2 hT_rr.1 hT_rr.2 hall
      (Or.inl hsucc.symm)
  exact StrictInterl.forward_of_orientation_of_succDegree hsucc hstrictInterl_or

/-- Garloff--Wagner's formula (3): `J^k L f` precedes `J^k L ((X - u)f)` when
`u ≤ 0`.  No simple-root or coprimeness hypothesis is needed. -/
theorem divFactorialShift_factor_strictInterl_of_nonpos {k : ℕ} {u : ℝ} {f : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hFs : (divFactorialShift (k + 1) f).Splits)
    (hfpos : HasPosLeadingCoeff f) :
    StrictInterl (divFactorialShift k f) (divFactorialShift k ((X - C u) * f)) := by
  have hFpos : HasPosLeadingCoeff (divFactorialShift (k + 1) f) := hfpos.divFactorialShift (k + 1)
  have hdeg : 1 ≤ (divFactorialShift (k + 1) f).natDegree := by
    rw [natDegree_divFactorialShift (k + 1) hf0]
    lia
  have hstrictInterl :=
    derivative_strictInterl_tDeriv_of_nonpos
      (eps := u) (p := divFactorialShift (k + 1) f) hu hFs hFpos hdeg
  have hD : (divFactorialShift (k + 1) f).derivative = divFactorialShift k f :=
    derivative_divFactorialShift_succ k f
  rw [divFactorialShift_X_sub_C_mul_eq_tDeriv]
  simpa [hD] using hstrictInterl

/-- Common-factor branch of Garloff--Wagner's formula (3).  For
`F = J^(k+1)L f`, if `F = d q` and `F' = d r`, then the formula (3) proper
position step reduces to the quotient statement `r ≪ q`. -/
theorem divFactorialShift_factor_strictInterl_of_common_factor
    {k : ℕ} {u : ℝ} {f d q r : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hFs : (divFactorialShift (k + 1) f).Splits)
    (hF_def : divFactorialShift (k + 1) f = d * q)
    (hFder_def : (divFactorialShift (k + 1) f).derivative = d * r)
    (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    (hrq : StrictInterl r q) (hq_pos : HasPosLeadingCoeff q)
    (hr_pos : HasPosLeadingCoeff r) :
    StrictInterl (divFactorialShift k f) (divFactorialShift k ((X - C u) * f)) := by
  have hdeg : 1 ≤ (divFactorialShift (k + 1) f).natDegree := by
    rw [natDegree_divFactorialShift (k + 1) hf0]
    lia
  have hstrictInterl :=
    derivative_strictInterl_tDeriv_of_nonpos_of_common_factor
      (eps := u) (p := divFactorialShift (k + 1) f) (d := d) (q := q) (r := r)
      hu hFs hdeg hd_ne hd_splits hF_def hFder_def
      hrq hq_pos hr_pos
  have hD : (divFactorialShift (k + 1) f).derivative = divFactorialShift k f :=
    derivative_divFactorialShift_succ k f
  rw [divFactorialShift_X_sub_C_mul_eq_tDeriv]
  simpa [hD] using hstrictInterl

theorem antiderivative_C_mul_X_pow (a : ℝ) (k : ℕ) :
    antiderivative (C a * X ^ k) = C (a * (k + 1 : ℝ)⁻¹) * X ^ (k + 1) := by
  ext n
  cases n with
  | zero =>
      rw [coeff_antiderivative_zero, coeff_C_mul_X_pow]
      simp
  | succ n =>
      rw [coeff_antiderivative_succ, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
      by_cases hn : n = k
      · subst n
        simp
        ring
      · simp [hn]

theorem divFactorialShift_C_eq_C_mul_X_pow (a : ℝ) :
    ∀ k : ℕ, ∃ b : ℝ, divFactorialShift k (C a) = C b * X ^ k
  | 0 => by
      refine ⟨a, ?_⟩
      simp [divFactorialShift]
  | k + 1 => by
      obtain ⟨b, hb⟩ := divFactorialShift_C_eq_C_mul_X_pow a k
      refine ⟨b * (k + 1 : ℝ)⁻¹, ?_⟩
      rw [divFactorialShift_succ, hb, antiderivative_C_mul_X_pow]

theorem divFactorialShift_C_splits (a : ℝ) (k : ℕ) :
    (divFactorialShift k (C a)).Splits := by
  obtain ⟨b, hb⟩ := divFactorialShift_C_eq_C_mul_X_pow a k
  rw [hb]
  exact (Polynomial.Splits.C (R := ℝ) b).mul (Polynomial.Splits.X_pow k)

lemma hasSimpleRootsExcept_zero_C_mul_X_pow {a : ℝ} (ha : a ≠ 0) (k : ℕ) :
    HasSimpleRootsExcept (C a * X ^ k) 0 := by
  intro r hr0 hroot
  exfalso
  have hzero : a * r ^ k = 0 := by simpa [Polynomial.IsRoot.def] using hroot
  exact (mul_ne_zero ha (pow_ne_zero k hr0)) hzero

theorem divFactorialShift_splits_of_splits {f : ℝ[X]} (hf0 : f ≠ 0) (hfs : f.Splits) :
    ∀ k, (divFactorialShift k f).Splits := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ {f : ℝ[X]}, f.natDegree = n → f ≠ 0 → f.Splits → ∀ k, (divFactorialShift k f).Splits
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro f hfdeg hf0 hfs k
        by_cases hn0 : n = 0
        · have hfC : f = C (f.coeff 0) := by
            apply eq_C_of_natDegree_eq_zero
            rw [hfdeg, hn0]
          rw [hfC]
          exact divFactorialShift_C_splits (f.coeff 0) k
        · have hroots_pos : 0 < f.roots.card := by
            rw [card_roots_of_splits hfs, hfdeg]
            exact Nat.pos_of_ne_zero hn0
          obtain ⟨u, hu_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
          have hu_root : f.IsRoot u := (mem_roots hf0).mp hu_mem
          obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hu_root
          have hq_dvd : q ∣ f := ⟨X - C u, by rw [hq]; ring⟩
          have hq0 : q ≠ 0 := by
            intro hq0
            rw [hq0, mul_zero] at hq
            exact hf0 hq
          have hq_splits : q.Splits :=
            (isRealRooted_of_dvd hf0 hfs hq0 hq_dvd).2
          have hqdeg_lt : q.natDegree < n := by
            have hmuldeg : n = q.natDegree + 1 := by
              rw [← hfdeg, hq, natDegree_mul (X_sub_C_ne_zero u) hq0,
                natDegree_X_sub_C]
              lia
            lia
          have ihq : (divFactorialShift (k + 1) q).Splits :=
            ih q.natDegree hqdeg_lt (f := q) rfl hq0 hq_splits (k + 1)
          rw [hq]
          exact divFactorialShift_X_sub_C_mul_splits (k := k) (u := u) (f := q) ihq
  exact hP f.natDegree rfl hf0 hfs

/-- All-real Garloff--Wagner formula (3), in the local `J^k L` notation. -/
theorem divFactorialShift_factor_strictInterl_of_splits {k : ℕ} {u : ℝ} {f : ℝ[X]}
    (hf0 : f ≠ 0) (hfs : f.Splits) :
    StrictInterl (divFactorialShift k f) (divFactorialShift k ((X - C u) * f)) := by
  have hF0 : divFactorialShift (k + 1) f ≠ 0 := (divFactorialShift_ne_zero_iff (k + 1) f).2 hf0
  have hFs : (divFactorialShift (k + 1) f).Splits :=
    divFactorialShift_splits_of_splits hf0 hfs (k + 1)
  have hdeg : 1 ≤ (divFactorialShift (k + 1) f).natDegree := by
    rw [natDegree_divFactorialShift (k + 1) hf0]
    lia
  have hstrictInterl :=
    derivative_strictInterl_tDeriv_of_splits
      (eps := u) (p := divFactorialShift (k + 1) f) hF0 hFs hdeg
  have hD : (divFactorialShift (k + 1) f).derivative = divFactorialShift k f :=
    derivative_divFactorialShift_succ k f
  rw [divFactorialShift_X_sub_C_mul_eq_tDeriv]
  simpa [hD] using hstrictInterl

/-- Garloff--Wagner, Theorem 11(b), zero-aware PF-cone form: `J^k L` preserves
PF polynomials. -/
theorem IsPFPolynomial.divFactorialShift {f : ℝ[X]} (hf : IsPFPolynomial f) (k : ℕ) :
    IsPFPolynomial (divFactorialShift k f) := by
  by_cases hf0 : f = 0
  · simpa [hf0] using IsPFPolynomial.zero
  · exact IsPFPolynomial.of_realRooted_nonneg
      (hf.hasNonnegCoeffs.divFactorialShift k)
      (divFactorialShift_splits_of_splits hf0 (hf.ne_zero_and_splits hf0).2 k)

@[deprecated (since := "2026-10-06")]
alias gwTheorem11PF := IsPFPolynomial.divFactorialShift

private theorem divFactorialShift_splits_pos_roots_nonpos {f : ℝ[X]}
    (hf0 : f ≠ 0) (hfs : f.Splits) (hfpos : HasPosLeadingCoeff f)
    (hfroots : ∀ r ∈ f.roots, r ≤ 0) (k : ℕ) :
    (divFactorialShift k f).Splits ∧
      HasPosLeadingCoeff (divFactorialShift k f) ∧
      ∀ r ∈ (divFactorialShift k f).roots, r ≤ 0 := by
  have hfnn : HasNonnegCoeffs f :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hfs).2
      ⟨hfpos, hfroots⟩).1
  have hsplit : (divFactorialShift k f).Splits := divFactorialShift_splits_of_splits hf0 hfs k
  exact ⟨hsplit, hfpos.divFactorialShift k,
    roots_nonpos_of_nonneg_coeffs hsplit (hfnn.divFactorialShift k)⟩

/-- Simple-except-origin part of Garloff--Wagner, Theorem 11(b). -/
private theorem divFactorialShift_hasSimpleRootsExcept_zero
    {f : ℝ[X]} (hf0 : f ≠ 0) (hfs : f.Splits)
    (hfroots : ∀ r ∈ f.roots, r ≤ 0)
    (hfsimple : HasSimpleRootsExcept f 0) :
    ∀ k, HasSimpleRootsExcept (divFactorialShift k f) 0 := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ {f : ℝ[X]}, f.natDegree = n → f ≠ 0 → f.Splits →
      (∀ r ∈ f.roots, r ≤ 0) → HasSimpleRootsExcept f 0 →
      ∀ k, HasSimpleRootsExcept (divFactorialShift k f) 0
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro f hfdeg hf0 hfs hfroots hfsimple k
        by_cases hn0 : n = 0
        · have hfC : f = C (f.coeff 0) := by
            apply eq_C_of_natDegree_eq_zero
            rw [hfdeg, hn0]
          obtain ⟨b, hb⟩ := divFactorialShift_C_eq_C_mul_X_pow (f.coeff 0) k
          have hJ0 : divFactorialShift k f ≠ 0 := (divFactorialShift_ne_zero_iff k f).2 hf0
          have hb_ne : b ≠ 0 := by
            intro hb0
            exact hJ0 (by rw [hfC, hb, hb0]; simp)
          rw [hfC, hb]
          exact hasSimpleRootsExcept_zero_C_mul_X_pow hb_ne k
        · have hroots_pos : 0 < f.roots.card := by
            rw [card_roots_of_splits hfs, hfdeg]
            exact Nat.pos_of_ne_zero hn0
          obtain ⟨u, hu_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
          have hu_root : f.IsRoot u := (mem_roots hf0).mp hu_mem
          have hu_nonpos : u ≤ 0 := hfroots u hu_mem
          obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hu_root
          have hq_dvd : q ∣ f := ⟨X - C u, by rw [hq]; ring⟩
          have hq0 : q ≠ 0 := by
            intro hq0
            rw [hq0, mul_zero] at hq
            exact hf0 hq
          have hq_splits : q.Splits :=
            (isRealRooted_of_dvd hf0 hfs hq0 hq_dvd).2
          have hqroots : ∀ r ∈ q.roots, r ≤ 0 := by
            intro r hr
            have hr_root : q.IsRoot r := (mem_roots hq0).mp hr
            have hf_root : f.IsRoot r := by
              rw [hq, Polynomial.IsRoot.def, eval_mul]
              simp [Polynomial.IsRoot.def] at hr_root
              simp [hr_root]
            exact hfroots r ((mem_roots hf0).mpr hf_root)
          have hq_simple : HasSimpleRootsExcept q 0 :=
            hasSimpleRootsExcept_of_X_sub_C_mul hq hfsimple
          have hqdeg_lt : q.natDegree < n := by
            have hmuldeg : n = q.natDegree + 1 := by
              rw [← hfdeg, hq, natDegree_mul (X_sub_C_ne_zero u) hq0,
                natDegree_X_sub_C]
              lia
            lia
          have ihq : ∀ k, HasSimpleRootsExcept (divFactorialShift k q) 0 :=
            ih q.natDegree hqdeg_lt (f := q) rfl hq0 hq_splits hqroots hq_simple
          by_cases hu0 : u = 0
          · subst u
            have hstep : divFactorialShift k ((X - C 0) * q) = divFactorialShift (k + 1) q := by
              rw [divFactorialShift_X_sub_C_mul_eq_tDeriv, tDeriv_zero_eps]
            rw [hq, hstep]
            exact ihq (k + 1)
          · have hstep :
                divFactorialShift k ((X - C u) * q) = tDeriv u (divFactorialShift (k + 1) q) :=
              divFactorialShift_X_sub_C_mul_eq_tDeriv k u q
            have hF0 : divFactorialShift (k + 1) q ≠ 0 :=
              (divFactorialShift_ne_zero_iff (k + 1) q).2 hq0
            have hFs : (divFactorialShift (k + 1) q).Splits :=
              divFactorialShift_splits_of_splits hq0 hq_splits (k + 1)
            rw [hq, hstep]
            exact hasSimpleRootsExcept_tDeriv (ihq (k + 1)) hu0 hF0 hFs
  exact hP f.natDegree rfl hf0 hfs hfroots hfsimple

private theorem divFactorialShift_splits_pos_roots_nonpos_simpleExcept
    {f : ℝ[X]} (hf0 : f ≠ 0) (hfs : f.Splits)
    (hfpos : HasPosLeadingCoeff f) (hfroots : ∀ r ∈ f.roots, r ≤ 0)
    (hfsimple : HasSimpleRootsExcept f 0) (k : ℕ) :
    (divFactorialShift k f).Splits ∧
      HasPosLeadingCoeff (divFactorialShift k f) ∧
      (∀ r ∈ (divFactorialShift k f).roots, r ≤ 0) ∧
      HasSimpleRootsExcept (divFactorialShift k f) 0 := by
  obtain ⟨hsplits, hpos, hroots⟩ :=
    divFactorialShift_splits_pos_roots_nonpos
      hf0 hfs hfpos hfroots k
  exact ⟨hsplits, hpos, hroots,
    divFactorialShift_hasSimpleRootsExcept_zero
      hf0 hfs hfroots hfsimple k⟩

/-- Garloff--Wagner formula (3) for a standard polynomial with nonpositive
roots and simple roots except possibly at the origin. -/
theorem divFactorialShift_factor_strictInterl_of_hasSimpleRootsExcept
    {k : ℕ} {u : ℝ} {f : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hfs : f.Splits)
    (hfpos : HasPosLeadingCoeff f) (hfroots : ∀ r ∈ f.roots, r ≤ 0)
    (hfsimple : HasSimpleRootsExcept f 0) :
    StrictInterl (divFactorialShift k f) (divFactorialShift k ((X - C u) * f)) := by
  obtain ⟨hFs, -, -, -⟩ :=
    divFactorialShift_splits_pos_roots_nonpos_simpleExcept
      hf0 hfs hfpos hfroots hfsimple (k + 1)
  exact divFactorialShift_factor_strictInterl_of_nonpos hu hf0 hFs hfpos

/-- Reduction for the Lemma 7/Krein step in Garloff--Wagner, Theorem 11(c):
once `g` is expressed as a weighted sum whose `J^k L` images are compatible
with the common left bound `J^k L f`, Wagner's finite weighted-sum theorem
gives the desired interlacing conclusion. -/
theorem divFactorialShift_strictInterl_of_weightedCompatibleExpansion
    {k : ℕ} {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hg : g = weightedSum l)
    (hcomp :
      WeightedCompatibleLeft (divFactorialShift k f)
        (l.map fun ap => (ap.1, divFactorialShift k ap.2))) :
    StrictInterl (divFactorialShift k f) (divFactorialShift k g) := by
  rw [hg, divFactorialShift_weightedSum]
  exact hcomp.toStrictInterl

/-- Variable-swapped common-right weighted reduction for the Lemma 7/Krein
step.  If `g` is expanded in summands bounded on the right by `f`, Wagner's
common-right finite-sum theorem gives the reverse conclusion
`J^k L g ≪ J^k L f`. -/
theorem divFactorialShift_weightedExpansion_strictInterl_right
    {k : ℕ} {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hg : g = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hstrictInterl : ∀ ap ∈ l, StrictInterl (divFactorialShift k ap.2) (divFactorialShift k f))
    (hpos : ∀ ap ∈ l, HasPosLeadingCoeff (divFactorialShift k ap.2))
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    StrictInterl (divFactorialShift k g) (divFactorialShift k f) := by
  rw [hg, divFactorialShift_weightedSum]
  exact
    StrictInterl.weightedSum_right_of_nonneg
      (l.map fun ap => (ap.1, divFactorialShift k ap.2)) (divFactorialShift k f)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap₀, hap₀, rfl⟩
        exact hnonneg ap₀ hap₀)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap₀, hap₀, rfl⟩
        exact hstrictInterl ap₀ hap₀)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap₀, hap₀, rfl⟩
        exact hpos ap₀ hap₀)
      (by
        rcases hex with ⟨ap, hap, hapos⟩
        exact ⟨(ap.1, divFactorialShift k ap.2), List.mem_map.mpr ⟨ap, hap, rfl⟩, hapos⟩)

/-- Common-right weighted reduction in the forward Theorem 11(c) orientation.
If the left input `f` is a nonnegative weighted sum whose `J^k L` images all
precede the common right bound `J^k L g`, then the image of `f` also precedes
the image of `g`. -/
theorem divFactorialShift_strictInterl_of_rightWeightedExpansion
    {k : ℕ} {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hstrictInterl : ∀ ap ∈ l, StrictInterl (divFactorialShift k ap.2) (divFactorialShift k g))
    (hpos : ∀ ap ∈ l, HasPosLeadingCoeff (divFactorialShift k ap.2))
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    StrictInterl (divFactorialShift k f) (divFactorialShift k g) := by
  rw [hf, divFactorialShift_weightedSum]
  exact
    StrictInterl.weightedSum_right_of_nonneg
      (l.map fun ap => (ap.1, divFactorialShift k ap.2)) (divFactorialShift k g)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
        exact hnonneg ap0 hap0)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
        exact hstrictInterl ap0 hap0)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
        exact hpos ap0 hap0)
      (by
        rcases hex with ⟨ap, hap, hapos⟩
        exact ⟨(ap.1, divFactorialShift k ap.2), List.mem_map.mpr ⟨ap, hap, rfl⟩, hapos⟩)

end RealRooted
