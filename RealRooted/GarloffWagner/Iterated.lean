import RealRooted.GarloffWagner.Algebra

/-!
# Garloff--Wagner iterated transforms

The `J^k ∘ L` transform, its factor identities, and the Theorem 11
real-rootedness and proper-position transport.
-/

open Polynomial

noncomputable section

namespace RealRooted

def gwJL (k : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (gwJ^[k]) (gwL p)

@[simp] theorem gwJL_zero_apply (p : ℝ[X]) :
    gwJL 0 p = gwL p :=
  rfl

theorem gwJL_succ (k : ℕ) (p : ℝ[X]) :
    gwJL (k + 1) p = gwJ (gwJL k p) := by
  rw [gwJL, gwJL, Function.iterate_succ_apply']

@[simp] theorem gwJL_zero (k : ℕ) :
    gwJL k (0 : ℝ[X]) = 0 := by
  induction k with
  | zero =>
      simp [gwJL, gwL_zero]
  | succ k ih =>
      rw [gwJL_succ, ih, gwJ_zero]

theorem gwJL_add (k : ℕ) (p q : ℝ[X]) :
    gwJL k (p + q) = gwJL k p + gwJL k q := by
  induction k with
  | zero =>
      simp [gwJL, gwL_add]
  | succ k ih =>
      rw [gwJL_succ, gwJL_succ, gwJL_succ, ih, gwJ_add]

theorem gwJL_sub (k : ℕ) (p q : ℝ[X]) :
    gwJL k (p - q) = gwJL k p - gwJL k q := by
  induction k with
  | zero =>
      simp [gwJL, gwL_sub]
  | succ k ih =>
      rw [gwJL_succ, gwJL_succ, gwJL_succ, ih, gwJ_sub]

theorem gwJL_C_mul (a : ℝ) (k : ℕ) (p : ℝ[X]) :
    gwJL k (C a * p) = C a * gwJL k p := by
  induction k with
  | zero =>
      simp [gwJL, gwL_C_mul]
  | succ k ih =>
      rw [gwJL_succ, gwJL_succ, ih, gwJ_C_mul]

theorem gwJL_list_sum (k : ℕ) :
    ∀ l : List ℝ[X], gwJL k l.sum = (l.map (gwJL k)).sum
  | [] => by simp
  | p :: l => by
      simp [gwJL_add, gwJL_list_sum k l]

theorem gwJL_weightedSum (k : ℕ) :
    ∀ l : List (ℝ × ℝ[X]),
      gwJL k (weightedSum l) =
        weightedSum (l.map fun ap => (ap.1, gwJL k ap.2))
  | [] => by simp
  | (a, p) :: l => by
      simp [weightedSum_cons, gwJL_add, gwJL_C_mul, gwJL_weightedSum k l]

theorem gwJL_eq_zero_iff (k : ℕ) (p : ℝ[X]) :
    gwJL k p = 0 ↔ p = 0 := by
  induction k with
  | zero =>
      simp [gwJL, gwL_eq_zero_iff]
  | succ k ih =>
      rw [gwJL_succ, gwJ_eq_zero_iff, ih]

theorem gwJL_ne_zero_iff (k : ℕ) (p : ℝ[X]) :
    gwJL k p ≠ 0 ↔ p ≠ 0 := by
  rw [ne_eq, ne_eq, gwJL_eq_zero_iff]

theorem natDegree_gwJL (k : ℕ) {p : ℝ[X]} (hp : p ≠ 0) :
    (gwJL k p).natDegree = p.natDegree + k := by
  induction k with
  | zero =>
      simp [gwJL, natDegree_gwL hp]
  | succ k ih =>
      rw [gwJL_succ, natDegree_gwJ, ih]
      · ring
      · exact (gwJL_ne_zero_iff k p).2 hp

theorem gwD_gwJL_succ (k : ℕ) (p : ℝ[X]) :
    gwD (gwJL (k + 1) p) = gwJL k p := by
  rw [gwJL_succ, gwD_gwJ]

theorem HasPosLeadingCoeff.gwJL {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) (k : ℕ) :
    HasPosLeadingCoeff (gwJL k p) := by
  induction k with
  | zero =>
      simpa [gwJL] using hp.gwL
  | succ k ih =>
      rw [gwJL_succ]
      exact ih.gwJ

theorem HasNonnegCoeffs.gwJL {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (k : ℕ) :
    HasNonnegCoeffs (gwJL k p) := by
  induction k with
  | zero =>
      simpa [gwJL] using hp.gwL
  | succ k ih =>
      rw [gwJL_succ]
      exact ih.gwJ

/-- The algebraic induction step in Garloff--Wagner, Theorem 11. -/
theorem gwJL_X_sub_C_mul (k : ℕ) (u : ℝ) (f : ℝ[X]) :
    gwJL k ((X - C u) * f) = gwJL (k + 1) f - C u * gwJL k f := by
  induction k with
  | zero =>
      simp only [gwJL_zero_apply]
      rw [sub_mul, gwL_sub, gwL_X_mul, gwL_C_mul, gwJL_succ, gwJL_zero_apply]
  | succ k ih =>
      rw [gwJL_succ, ih, gwJ_sub, gwJ_C_mul, ← gwJL_succ, ← gwJL_succ]

/-- The `k = 0` form of `gwJL_X_sub_C_mul`, matching the first transport step
in Garloff--Wagner's proof of Theorem 4(b). -/
theorem gwL_X_sub_C_mul (u : ℝ) (f : ℝ[X]) :
    gwL ((X - C u) * f) = gwJ (gwL f) - C u * gwL f := by
  simpa [gwJL_zero_apply, gwJL_succ] using gwJL_X_sub_C_mul 0 u f

/-- Derivative of the preceding `L`-transport identity. -/
theorem gwD_gwL_X_sub_C_mul (u : ℝ) (f : ℝ[X]) :
    gwD (gwL ((X - C u) * f)) = gwL f - C u * gwD (gwL f) := by
  rw [gwL_X_sub_C_mul, gwD_sub, gwD_C_mul, gwD_gwJ]

/-- Algebraic expansion of the two-linear-factor ordinary Hadamard product
used in Garloff--Wagner's double-deleted paragraph of Theorem 4(b). -/
theorem hadamardProduct_X_sub_C_mul_X_sub_C_mul_eq
    (j u : ℝ) (g q : ℝ[X]) :
    hadamardProduct ((X - C j) * g) ((X - C u) * q) =
      X * gwSchurProduct g (gwL q - C u * gwD (gwL q)) -
        C j * gwSchurProduct g (gwJ (gwL q) - C u * gwL q) := by
  rw [← gwSchurProduct_gwL_right ((X - C j) * g) ((X - C u) * q)]
  rw [gwL_X_sub_C_mul, gwSchurProduct_X_sub_C_mul_left]
  rw [gwD_sub, gwD_C_mul, gwD_gwJ]
  rw [gwSchurProduct_comm (gwL q - C u * gwD (gwL q)) g]

/-- The same induction step written as `(1 - uD) J^(k+1) L f`. -/
theorem gwJL_X_sub_C_mul_eq_sub_gwD (k : ℕ) (u : ℝ) (f : ℝ[X]) :
    gwJL k ((X - C u) * f) =
      gwJL (k + 1) f - C u * gwD (gwJL (k + 1) f) := by
  rw [gwJL_X_sub_C_mul, gwD_gwJL_succ]

/-- Garloff--Wagner's Theorem 11 induction step in `TDeriv` form. -/
theorem gwJL_X_sub_C_mul_eq_TDeriv (k : ℕ) (u : ℝ) (f : ℝ[X]) :
    gwJL k ((X - C u) * f) = TDeriv u (gwJL (k + 1) f) := by
  rw [gwJL_X_sub_C_mul_eq_sub_gwD]
  simp [TDeriv, gwD]

/-- Real-rootedness part of the Garloff--Wagner Theorem 11 induction step. -/
theorem gwJL_X_sub_C_mul_splits {k : ℕ} {u : ℝ} {f : ℝ[X]}
    (h : (gwJL (k + 1) f).Splits) :
    (gwJL k ((X - C u) * f)).Splits := by
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  exact splits_tderiv_all h

/-- All-real derivative-shift form of Garloff--Wagner formula (3):
if `p` is nonconstant and real-rooted, then `p'` precedes `p - ε p'` for
every real `ε`. -/
theorem derivative_prec_TDeriv_of_splits {eps : ℝ} {p : ℝ[X]}
    (hp0 : p ≠ 0) (hp : p.Splits) (hdeg : 1 ≤ p.natDegree) :
    Prec p.derivative (TDeriv eps p) := by
  by_cases hdeg1 : p.natDegree = 1
  · exact derivative_prec_TDeriv_of_natDegree_one hdeg1
  have hdeg2 : 2 ≤ p.natDegree := by lia
  have hder : Interlaces p.derivative p := derivative_interlaces hp hdeg2
  have hder_rr : p.derivative ≠ 0 ∧ p.derivative.Splits := hder.2.1
  have hT_rr : TDeriv eps p ≠ 0 ∧ (TDeriv eps p).Splits :=
    ⟨TDeriv_ne_zero hp0, splits_tderiv_all hp⟩
  have hall : AllComboRealRooted p.derivative (TDeriv eps p) := by
    intro α β
    by_cases hβ : β = 0
    · subst β
      by_cases hα : α = 0
      · simp [hα]
      · simpa using (isRealRooted_C_mul hder_rr.1 hder_rr.2 hα).2
    · have hcombo :
          C α * p.derivative + C β * TDeriv eps p =
            C β * TDeriv (eps - β⁻¹ * α) p := by
        ext n
        simp only [TDeriv, coeff_add, coeff_sub, coeff_C_mul]
        field_simp [hβ]
        ring
      rw [hcombo]
      exact (Polynomial.Splits.C (R := ℝ) β).mul (splits_tderiv_all hp)
  have hsucc :
      (TDeriv eps p).natDegree = p.derivative.natDegree + 1 := by
    rw [natDegree_TDeriv, p.natDegree_derivative]
    lia
  have hprec_or :
      Prec p.derivative (TDeriv eps p) ∨
        Prec (TDeriv eps p) p.derivative :=
    prec_of_allComboRealRooted hder_rr.1 hder_rr.2 hT_rr.1 hT_rr.2 hall
      (Or.inl hsucc.symm)
  exact prec_forward_of_orientation_of_succDegree hsucc hprec_or

/-- Coprime/simple-root branch of Garloff--Wagner's formula (3):
`J^k L f` precedes `J^k L ((X - u)f)` when `u ≤ 0`.  The remaining
multiple-root case is the common-factor reduction used later in Theorem 11. -/
theorem gwJL_factor_prec_of_nonpos_of_coprime {k : ℕ} {u : ℝ} {f : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hFs : (gwJL (k + 1) f).Splits)
    (hfpos : HasPosLeadingCoeff f)
    (hcop : u < 0 →
      IsCoprime (gwJL (k + 1) f) (C (-u) * (gwJL (k + 1) f).derivative)) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  have hFpos : HasPosLeadingCoeff (gwJL (k + 1) f) := hfpos.gwJL (k + 1)
  have hdeg : 1 ≤ (gwJL (k + 1) f).natDegree := by
    rw [natDegree_gwJL (k + 1) hf0]
    lia
  have hprec :=
    derivative_prec_TDeriv_of_nonpos_of_coprime
      (eps := u) (p := gwJL (k + 1) f) hu hF0 hFs hFpos hdeg hcop
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

/-- Common-factor branch of Garloff--Wagner's formula (3).  For
`F = J^(k+1)L f`, if `F = d q` and `F' = d r`, then the formula (3) proper
position step reduces to the quotient statement `r ≪ q` plus the no-common
Wagner hypothesis for `q` and `-u r`.

The remaining full formula (3) proof must construct this quotient data from
the common roots of `F` and `F'`. -/
theorem gwJL_factor_prec_of_nonpos_of_common_factor {k : ℕ} {u : ℝ} {f d q r : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hFs : (gwJL (k + 1) f).Splits)
    (hF_def : gwJL (k + 1) f = d * q)
    (hFder_def : (gwJL (k + 1) f).derivative = d * r)
    (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    (hrq : Prec r q) (hq_pos : HasPosLeadingCoeff q)
    (hr_pos : HasPosLeadingCoeff r)
    (hcop : u < 0 → IsCoprime q (C (-u) * r)) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  have hdeg : 1 ≤ (gwJL (k + 1) f).natDegree := by
    rw [natDegree_gwJL (k + 1) hf0]
    lia
  have hprec :=
    derivative_prec_TDeriv_of_nonpos_of_common_factor
      (eps := u) (p := gwJL (k + 1) f) (d := d) (q := q) (r := r)
      hu hF0 hFs hdeg hd_ne hd_splits hF_def hFder_def
      hrq hq_pos hr_pos hcop
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

/-- Common-factor branch of formula (3), with quotient coprimality expressed
as absence of common real roots. -/
theorem gwJL_factor_prec_of_nonpos_of_common_factor_no_common
    {k : ℕ} {u : ℝ} {f d q r : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hFs : (gwJL (k + 1) f).Splits)
    (hF_def : gwJL (k + 1) f = d * q)
    (hFder_def : (gwJL (k + 1) f).derivative = d * r)
    (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    (hrq : Prec r q) (hq_pos : HasPosLeadingCoeff q)
    (hr_pos : HasPosLeadingCoeff r)
    (hno : ∀ x : ℝ, q.IsRoot x → ¬ r.IsRoot x) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  have hdeg : 1 ≤ (gwJL (k + 1) f).natDegree := by
    rw [natDegree_gwJL (k + 1) hf0]
    lia
  have hprec :=
    derivative_prec_TDeriv_of_nonpos_of_common_factor_no_common
      (eps := u) (p := gwJL (k + 1) f) (d := d) (q := q) (r := r)
      hu hF0 hFs hdeg hd_ne hd_splits hF_def hFder_def
      hrq hq_pos hr_pos hno
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

/-- Exact-root squarefree-quotient branch of Garloff--Wagner's formula (3).
If `F = J^(k+1)L f = (X - C a)^m q` and the remaining quotient `q` has simple
roots with no further `X - C a` factor, then the formula (3) proper-position
step follows. -/
theorem gwJL_factor_prec_of_nonpos_of_pow_X_sub_C_factor_hasSimpleRoots
    {k : ℕ} {u a : ℝ} {m : ℕ} {f q : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hFs : (gwJL (k + 1) f).Splits)
    (hfpos : HasPosLeadingCoeff f)
    (hdeg : 2 ≤ (gwJL (k + 1) f).natDegree)
    (hm : 1 ≤ m) (hF_factor : gwJL (k + 1) f = (X - C a) ^ m * q)
    (hq_nodvd : ¬ (X - C a) ∣ q) (hq_simple : HasSimpleRoots q) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  have hFpos : HasPosLeadingCoeff (gwJL (k + 1) f) := hfpos.gwJL (k + 1)
  have hprec :=
    derivative_prec_TDeriv_of_nonpos_of_pow_X_sub_C_factor_hasSimpleRoots
      (eps := u) (p := gwJL (k + 1) f) (q := q) (a := a) (m := m)
      hu hF0 hFs hFpos hdeg hm hF_factor hq_nodvd hq_simple
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

/-- Root-multiplicity squarefree-quotient branch of Garloff--Wagner's formula
(3), using the canonical factorization of `F = J^(k+1)L f` at a root `a`. -/
theorem gwJL_factor_prec_of_nonpos_of_rootMultiplicity_factor_hasSimpleRoots
    {k : ℕ} {u a : ℝ} {f : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hFs : (gwJL (k + 1) f).Splits)
    (hfpos : HasPosLeadingCoeff f)
    (hdeg : 2 ≤ (gwJL (k + 1) f).natDegree)
    (hm : 1 ≤ (gwJL (k + 1) f).rootMultiplicity a)
    (hsimple : ∀ q : ℝ[X],
      gwJL (k + 1) f =
        (X - C a) ^ (gwJL (k + 1) f).rootMultiplicity a * q →
      ¬ (X - C a) ∣ q → HasSimpleRoots q) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  have hFpos : HasPosLeadingCoeff (gwJL (k + 1) f) := hfpos.gwJL (k + 1)
  have hprec :=
    derivative_prec_TDeriv_of_nonpos_of_rootMultiplicity_factor_hasSimpleRoots
      (eps := u) (p := gwJL (k + 1) f) (a := a)
      hu hF0 hFs hFpos hdeg hm hsimple
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

/-- Formula (3) branch when `F = J^(k+1)L f` has simple roots away from the
chosen exceptional root `a`.  For Garloff--Wagner Theorem 11(b), the intended
choice is `a = 0`. -/
theorem gwJL_factor_prec_of_nonpos_of_rootMultiplicity_factor_hasSimpleRootsExcept
    {k : ℕ} {u a : ℝ} {f : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hFs : (gwJL (k + 1) f).Splits)
    (hfpos : HasPosLeadingCoeff f)
    (hdeg : 2 ≤ (gwJL (k + 1) f).natDegree)
    (hm : 1 ≤ (gwJL (k + 1) f).rootMultiplicity a)
    (hsimple : HasSimpleRootsExcept (gwJL (k + 1) f) a) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  have hFpos : HasPosLeadingCoeff (gwJL (k + 1) f) := hfpos.gwJL (k + 1)
  have hprec :=
    derivative_prec_TDeriv_of_nonpos_of_rootMultiplicity_factor_hasSimpleRootsExcept
      (eps := u) (p := gwJL (k + 1) f) (a := a)
      hu hF0 hFs hFpos hdeg hm hsimple
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

theorem gwJ_C_mul_X_pow (a : ℝ) (k : ℕ) :
    gwJ (C a * X ^ k) = C (a * (k + 1 : ℝ)⁻¹) * X ^ (k + 1) := by
  ext n
  cases n with
  | zero =>
      rw [coeff_gwJ_zero, coeff_C_mul_X_pow]
      simp
  | succ n =>
      rw [coeff_gwJ_succ, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
      by_cases hn : n = k
      · subst n
        simp
        ring
      · simp [hn]

theorem gwJL_C_eq_C_mul_X_pow (a : ℝ) :
    ∀ k : ℕ, ∃ b : ℝ, gwJL k (C a) = C b * X ^ k
  | 0 => by
      refine ⟨a, ?_⟩
      simp [gwJL]
  | k + 1 => by
      obtain ⟨b, hb⟩ := gwJL_C_eq_C_mul_X_pow a k
      refine ⟨b * (k + 1 : ℝ)⁻¹, ?_⟩
      rw [gwJL_succ, hb, gwJ_C_mul_X_pow]

theorem gwJL_C_splits (a : ℝ) (k : ℕ) :
    (gwJL k (C a)).Splits := by
  obtain ⟨b, hb⟩ := gwJL_C_eq_C_mul_X_pow a k
  rw [hb]
  exact (Polynomial.Splits.C (R := ℝ) b).mul (Polynomial.Splits.X_pow k)

lemma hasSimpleRootsExcept_zero_C_mul_X_pow {a : ℝ} (ha : a ≠ 0) (k : ℕ) :
    HasSimpleRootsExcept (C a * X ^ k) 0 := by
  intro r hr0 hroot
  exfalso
  have hzero : a * r ^ k = 0 := by simpa [Polynomial.IsRoot.def] using hroot
  exact (mul_ne_zero ha (pow_ne_zero k hr0)) hzero

theorem gwJL_splits_of_splits {f : ℝ[X]} (hf0 : f ≠ 0) (hfs : f.Splits) :
    ∀ k, (gwJL k f).Splits := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ {f : ℝ[X]}, f.natDegree = n → f ≠ 0 → f.Splits → ∀ k, (gwJL k f).Splits
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
          exact gwJL_C_splits (f.coeff 0) k
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
          have ihq : (gwJL (k + 1) q).Splits :=
            ih q.natDegree hqdeg_lt (f := q) rfl hq0 hq_splits (k + 1)
          rw [hq]
          exact gwJL_X_sub_C_mul_splits (k := k) (u := u) (f := q) ihq
  exact hP f.natDegree rfl hf0 hfs

/-- All-real Garloff--Wagner formula (3), in the local `J^k L` notation. -/
theorem gwJL_factor_prec_of_splits {k : ℕ} {u : ℝ} {f : ℝ[X]}
    (hf0 : f ≠ 0) (hfs : f.Splits) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  have hFs : (gwJL (k + 1) f).Splits :=
    gwJL_splits_of_splits hf0 hfs (k + 1)
  have hdeg : 1 ≤ (gwJL (k + 1) f).natDegree := by
    rw [natDegree_gwJL (k + 1) hf0]
    lia
  have hprec :=
    derivative_prec_TDeriv_of_splits
      (eps := u) (p := gwJL (k + 1) f) hF0 hFs hdeg
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

/-- Theorem 11(a), real-rooted part: `J^k L` preserves real-rootedness. -/
def gwTheorem11RealRootedStatement : Prop :=
  ∀ {f : ℝ[X]}, f ≠ 0 → f.Splits → ∀ k, (gwJL k f).Splits

theorem gwTheorem11RealRooted :
    gwTheorem11RealRootedStatement := by
  intro f hf0 hfs
  exact gwJL_splits_of_splits hf0 hfs

/-- Theorem 11(b), zero-aware PF-cone form: `J^k L` preserves PF polynomials. -/
def gwTheorem11PFStatement : Prop :=
  ∀ {f : ℝ[X]}, IsPFPolynomial f → ∀ k, IsPFPolynomial (gwJL k f)

theorem gwTheorem11PF_of_realRooted
    (h : gwTheorem11RealRootedStatement) :
    gwTheorem11PFStatement := by
  intro f hf k
  by_cases hf0 : f = 0
  · simpa [hf0] using IsPFPolynomial.zero
  · exact IsPFPolynomial.of_realRooted_nonneg
      (hf.hasNonnegCoeffs.gwJL k) (h hf0 (hf.ne_zero_and_splits hf0).2 k)

theorem gwTheorem11PF :
    gwTheorem11PFStatement :=
  gwTheorem11PF_of_realRooted gwTheorem11RealRooted

/-- The standard nonpositive-root part of Garloff--Wagner, Theorem 11(b),
without the later simple-root/common-factor strengthening. -/
def gwTheorem11NonposStatement : Prop :=
  ∀ {f : ℝ[X]},
    f ≠ 0 →
    f.Splits →
    HasPosLeadingCoeff f →
    (∀ r ∈ f.roots, r ≤ 0) →
    ∀ k,
      (gwJL k f).Splits ∧
        HasPosLeadingCoeff (gwJL k f) ∧
        ∀ r ∈ (gwJL k f).roots, r ≤ 0

theorem gwJL_splits_pos_roots_nonpos_of_splits_pos_roots_nonpos {f : ℝ[X]}
    (hf0 : f ≠ 0) (hfs : f.Splits) (hfpos : HasPosLeadingCoeff f)
    (hfroots : ∀ r ∈ f.roots, r ≤ 0) (k : ℕ) :
    (gwJL k f).Splits ∧
      HasPosLeadingCoeff (gwJL k f) ∧
      ∀ r ∈ (gwJL k f).roots, r ≤ 0 := by
  have hfnn : HasNonnegCoeffs f :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hfs).2
      ⟨hfpos, hfroots⟩).1
  have hsplit : (gwJL k f).Splits := gwTheorem11RealRooted hf0 hfs k
  exact ⟨hsplit, hfpos.gwJL k, roots_nonpos_of_nonneg_coeffs hsplit (hfnn.gwJL k)⟩

theorem gwTheorem11Nonpos :
    gwTheorem11NonposStatement := by
  intro f hf0 hfs hfpos hfroots k
  exact gwJL_splits_pos_roots_nonpos_of_splits_pos_roots_nonpos
    hf0 hfs hfpos hfroots k

/-- Simple-except-origin part of Garloff--Wagner, Theorem 11(b). -/
theorem gwJL_hasSimpleRootsExcept_zero_of_splits_roots_nonpos_hasSimpleRootsExcept
    {f : ℝ[X]} (hf0 : f ≠ 0) (hfs : f.Splits)
    (hfroots : ∀ r ∈ f.roots, r ≤ 0)
    (hfsimple : HasSimpleRootsExcept f 0) :
    ∀ k, HasSimpleRootsExcept (gwJL k f) 0 := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ {f : ℝ[X]}, f.natDegree = n → f ≠ 0 → f.Splits →
      (∀ r ∈ f.roots, r ≤ 0) → HasSimpleRootsExcept f 0 →
      ∀ k, HasSimpleRootsExcept (gwJL k f) 0
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro f hfdeg hf0 hfs hfroots hfsimple k
        by_cases hn0 : n = 0
        · have hfC : f = C (f.coeff 0) := by
            apply eq_C_of_natDegree_eq_zero
            rw [hfdeg, hn0]
          obtain ⟨b, hb⟩ := gwJL_C_eq_C_mul_X_pow (f.coeff 0) k
          have hgw0 : gwJL k f ≠ 0 := (gwJL_ne_zero_iff k f).2 hf0
          have hb_ne : b ≠ 0 := by
            intro hb0
            exact hgw0 (by rw [hfC, hb, hb0]; simp)
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
          have ihq : ∀ k, HasSimpleRootsExcept (gwJL k q) 0 :=
            ih q.natDegree hqdeg_lt (f := q) rfl hq0 hq_splits hqroots hq_simple
          by_cases hu0 : u = 0
          · subst u
            have hstep : gwJL k ((X - C 0) * q) = gwJL (k + 1) q := by
              rw [gwJL_X_sub_C_mul_eq_TDeriv, TDeriv_zero_eps]
            rw [hq, hstep]
            exact ihq (k + 1)
          · have hstep :
                gwJL k ((X - C u) * q) = TDeriv u (gwJL (k + 1) q) :=
              gwJL_X_sub_C_mul_eq_TDeriv k u q
            have hF0 : gwJL (k + 1) q ≠ 0 :=
              (gwJL_ne_zero_iff (k + 1) q).2 hq0
            have hFs : (gwJL (k + 1) q).Splits :=
              gwTheorem11RealRooted hq0 hq_splits (k + 1)
            rw [hq, hstep]
            exact hasSimpleRootsExcept_TDeriv (ihq (k + 1)) hu0 hF0 hFs
  exact hP f.natDegree rfl hf0 hfs hfroots hfsimple

/-- Theorem 11(b) with the simple-except-origin strengthening included. -/
def gwTheorem11NonposSimpleExceptStatement : Prop :=
  ∀ {f : ℝ[X]},
    f ≠ 0 →
    f.Splits →
    HasPosLeadingCoeff f →
    (∀ r ∈ f.roots, r ≤ 0) →
    HasSimpleRootsExcept f 0 →
    ∀ k,
      (gwJL k f).Splits ∧
        HasPosLeadingCoeff (gwJL k f) ∧
        (∀ r ∈ (gwJL k f).roots, r ≤ 0) ∧
        HasSimpleRootsExcept (gwJL k f) 0

theorem gwJL_splits_pos_roots_nonpos_simpleExcept_of_splits_pos_roots_nonpos_simpleExcept
    {f : ℝ[X]} (hf0 : f ≠ 0) (hfs : f.Splits)
    (hfpos : HasPosLeadingCoeff f) (hfroots : ∀ r ∈ f.roots, r ≤ 0)
    (hfsimple : HasSimpleRootsExcept f 0) (k : ℕ) :
    (gwJL k f).Splits ∧
      HasPosLeadingCoeff (gwJL k f) ∧
      (∀ r ∈ (gwJL k f).roots, r ≤ 0) ∧
      HasSimpleRootsExcept (gwJL k f) 0 := by
  obtain ⟨hsplits, hpos, hroots⟩ :=
    gwJL_splits_pos_roots_nonpos_of_splits_pos_roots_nonpos
      hf0 hfs hfpos hfroots k
  exact ⟨hsplits, hpos, hroots,
    gwJL_hasSimpleRootsExcept_zero_of_splits_roots_nonpos_hasSimpleRootsExcept
      hf0 hfs hfroots hfsimple k⟩

theorem gwTheorem11NonposSimpleExcept :
    gwTheorem11NonposSimpleExceptStatement := by
  intro f hf0 hfs hfpos hfroots hfsimple k
  exact
    gwJL_splits_pos_roots_nonpos_simpleExcept_of_splits_pos_roots_nonpos_simpleExcept
      hf0 hfs hfpos hfroots hfsimple k

/-- Garloff--Wagner formula (3) for a standard polynomial with nonpositive
roots and simple roots except possibly at the origin. -/
theorem gwJL_factor_prec_of_nonpos_of_hasSimpleRootsExcept_zero
    {k : ℕ} {u : ℝ} {f : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hfs : f.Splits)
    (hfpos : HasPosLeadingCoeff f) (hfroots : ∀ r ∈ f.roots, r ≤ 0)
    (hfsimple : HasSimpleRootsExcept f 0) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) := by
  have hF0 : gwJL (k + 1) f ≠ 0 := (gwJL_ne_zero_iff (k + 1) f).2 hf0
  obtain ⟨hFs, hFpos, _hFroots, hFsimple⟩ :=
    gwJL_splits_pos_roots_nonpos_simpleExcept_of_splits_pos_roots_nonpos_simpleExcept
      hf0 hfs hfpos hfroots hfsimple (k + 1)
  have hdeg : 1 ≤ (gwJL (k + 1) f).natDegree := by
    rw [natDegree_gwJL (k + 1) hf0]
    lia
  have hprec :=
    derivative_prec_TDeriv_of_nonpos_of_hasSimpleRootsExcept_zero
      (eps := u) (p := gwJL (k + 1) f)
      hu hF0 hFs hFpos hdeg hFsimple
  have hD : (gwJL (k + 1) f).derivative = gwJL k f := by simpa [gwD] using gwD_gwJL_succ k f
  rw [gwJL_X_sub_C_mul_eq_TDeriv]
  simpa [hD] using hprec

/-- Garloff--Wagner formula (3), packaged under the Theorem 11(b) hypotheses
that will be available in the Theorem 11(c) induction. -/
theorem gwJL_factor_prec_of_nonpos
    {k : ℕ} {u : ℝ} {f : ℝ[X]}
    (hu : u ≤ 0) (hf0 : f ≠ 0) (hfs : f.Splits)
    (hfpos : HasPosLeadingCoeff f) (hfroots : ∀ r ∈ f.roots, r ≤ 0)
    (hfsimple : HasSimpleRootsExcept f 0) :
    Prec (gwJL k f) (gwJL k ((X - C u) * f)) :=
  gwJL_factor_prec_of_nonpos_of_hasSimpleRootsExcept_zero
    hu hf0 hfs hfpos hfroots hfsimple

/-- Theorem 11(c), in the local orientation:
Garloff--Wagner's `g $ f` is represented by `Prec f g`. -/
def gwTheorem11PrecStatement : Prop :=
  ∀ {f g : ℝ[X]}, Prec f g → ∀ k, Prec (gwJL k f) (gwJL k g)

/-- Reduction for the Lemma 7/Krein step in Garloff--Wagner, Theorem 11(c):
once `g` is expressed as a weighted sum whose `J^k L` images are compatible
with the common left bound `J^k L f`, Wagner's finite weighted-sum theorem
gives the desired proper-position conclusion. -/
theorem gwJL_prec_of_weightedCompatibleExpansion
    {k : ℕ} {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hg : g = weightedSum l)
    (hcomp :
      WeightedCompatibleLeft (gwJL k f)
        (l.map fun ap => (ap.1, gwJL k ap.2))) :
    Prec (gwJL k f) (gwJL k g) := by
  rw [hg, gwJL_weightedSum]
  exact prec_weightedSum_left hcomp

/-- Interface isolating the remaining Krein-expansion and Wagner-compatibility
work for Garloff--Wagner, Theorem 11(c). -/
def gwTheorem11PrecWeightedExpansionStatement : Prop :=
  ∀ {f g : ℝ[X]}, Prec f g → ∀ k, ∃ l : List (ℝ × ℝ[X]),
    g = weightedSum l ∧
      WeightedCompatibleLeft (gwJL k f)
        (l.map fun ap => (ap.1, gwJL k ap.2))

theorem gwTheorem11Prec_of_weightedCompatibleExpansion
    (h : gwTheorem11PrecWeightedExpansionStatement) :
    gwTheorem11PrecStatement := by
  intro f g hfg k
  rcases h hfg k with ⟨l, hg, hcomp⟩
  exact gwJL_prec_of_weightedCompatibleExpansion hg hcomp

/-- Variable-swapped common-right weighted reduction for the Lemma 7/Krein
step.  If `g` is expanded in summands bounded on the right by `f`, Wagner's
common-right finite-sum theorem gives the reverse conclusion
`J^k L g ≪ J^k L f`. -/
theorem gwJL_weightedExpansion_prec_right
    {k : ℕ} {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hg : g = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hprec : ∀ ap ∈ l, Prec (gwJL k ap.2) (gwJL k f))
    (hpos : ∀ ap ∈ l, HasPosLeadingCoeff (gwJL k ap.2))
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    Prec (gwJL k g) (gwJL k f) := by
  rw [hg, gwJL_weightedSum]
  exact
    prec_weightedSum_right
      (l.map fun ap => (ap.1, gwJL k ap.2)) (gwJL k f)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap₀, hap₀, rfl⟩
        exact hnonneg ap₀ hap₀)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap₀, hap₀, rfl⟩
        exact hprec ap₀ hap₀)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap₀, hap₀, rfl⟩
        exact hpos ap₀ hap₀)
      (by
        rcases hex with ⟨ap, hap, hapos⟩
        exact ⟨(ap.1, gwJL k ap.2), List.mem_map.mpr ⟨ap, hap, rfl⟩, hapos⟩)

/-- Interface for the variable-swapped common-right Krein-expansion direction.
This is not the final Theorem 11(c) orientation by itself; see
`gwTheorem11PrecRightWeightedExpansionStatement` for the forward package. -/
def gwTheorem11RightWeightedExpansionStatement : Prop :=
  ∀ {f g : ℝ[X]}, Prec f g → ∀ k, ∃ l : List (ℝ × ℝ[X]),
    g = weightedSum l ∧
      (∀ ap ∈ l, 0 ≤ ap.1) ∧
      (∀ ap ∈ l, Prec (gwJL k ap.2) (gwJL k f)) ∧
      (∀ ap ∈ l, HasPosLeadingCoeff (gwJL k ap.2)) ∧
      ∃ ap ∈ l, 0 < ap.1

theorem gwTheorem11RevPrec_of_rightWeightedExpansion
    (h : gwTheorem11RightWeightedExpansionStatement) :
    ∀ {f g : ℝ[X]}, Prec f g → ∀ k, Prec (gwJL k g) (gwJL k f) := by
  intro f g hfg k
  rcases h hfg k with ⟨l, hg, hnonneg, hprec, hpos, hex⟩
  exact gwJL_weightedExpansion_prec_right hg hnonneg hprec hpos hex

/-- Common-right weighted reduction in the forward Theorem 11(c) orientation.
If the left input `f` is a nonnegative weighted sum whose `J^k L` images all
precede the common right bound `J^k L g`, then the image of `f` also precedes
the image of `g`. -/
theorem gwJL_prec_of_rightWeightedExpansion
    {k : ℕ} {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hprec : ∀ ap ∈ l, Prec (gwJL k ap.2) (gwJL k g))
    (hpos : ∀ ap ∈ l, HasPosLeadingCoeff (gwJL k ap.2))
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    Prec (gwJL k f) (gwJL k g) := by
  rw [hf, gwJL_weightedSum]
  exact
    prec_weightedSum_right
      (l.map fun ap => (ap.1, gwJL k ap.2)) (gwJL k g)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
        exact hnonneg ap0 hap0)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
        exact hprec ap0 hap0)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
        exact hpos ap0 hap0)
      (by
        rcases hex with ⟨ap, hap, hapos⟩
        exact ⟨(ap.1, gwJL k ap.2), List.mem_map.mpr ⟨ap, hap, rfl⟩, hapos⟩)

/-- Forward Theorem 11(c) interface for the common-right Krein expansion:
given `Prec f g`, write the left input `f` as a nonnegative weighted sum of
summands whose `J^k L` images precede `J^k L g`. -/
def gwTheorem11PrecRightWeightedExpansionStatement : Prop :=
  ∀ {f g : ℝ[X]}, Prec f g → ∀ k, ∃ l : List (ℝ × ℝ[X]),
    f = weightedSum l ∧
      (∀ ap ∈ l, 0 ≤ ap.1) ∧
      (∀ ap ∈ l, Prec (gwJL k ap.2) (gwJL k g)) ∧
      (∀ ap ∈ l, HasPosLeadingCoeff (gwJL k ap.2)) ∧
      ∃ ap ∈ l, 0 < ap.1

theorem gwTheorem11Prec_of_rightWeightedExpansion
    (h : gwTheorem11PrecRightWeightedExpansionStatement) :
    gwTheorem11PrecStatement := by
  intro f g hfg k
  rcases h hfg k with ⟨l, hf, hnonneg, hprec, hpos, hex⟩
  exact gwJL_prec_of_rightWeightedExpansion hf hnonneg hprec hpos hex

end RealRooted
