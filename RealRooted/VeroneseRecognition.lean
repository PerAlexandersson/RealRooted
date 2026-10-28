module

public import RealRooted.VeroneseSection
import Mathlib.Algebra.Polynomial.Expand

/-!
# Recognition of Veronese sections

This file formalizes the algebraic reconstruction underlying issue #2116.  It
shows that a polynomial is recovered from all of its Veronese sections and
records how multiplication by the `r`th power of the variable acts on every
section.  These are the coefficient-level ingredients of the inverse product
parent theorem.

The Veronese-section convention and its linear-factor recurrences come from
Athanasiadis--Wagner, arXiv:2404.12989.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The contribution of residue `j` when a polynomial is reconstructed from
its `r`-Veronese sections. -/
@[expose] def veroneseResidueTerm (r j : ℕ) (p : ℝ[X]) : ℝ[X] :=
  X ^ j * p.comp (X ^ r)

private theorem not_dvd_sub_add_mul_of_lt {r i k n : ℕ}
    (hi : i < r) (hk : k < r) (hik : i ≠ k) (hile : i ≤ k + r * n) :
    ¬r ∣ k + r * n - i := by
  intro hdvd
  obtain ⟨m, hm⟩ := hdvd
  have heq : k + r * n = i + r * m := by
    calc
      k + r * n = (k + r * n - i) + i := (Nat.sub_add_cancel hile).symm
      _ = r * m + i := by rw [hm]
      _ = i + r * m := by ac_rfl
  have hmod := congrArg (fun x : ℕ ↦ x % r) heq
  simp [Nat.add_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hk] at hmod
  exact hik hmod.symm

/-- A residue contribution has the prescribed Veronese section. -/
theorem veroneseSectionPolynomial_veroneseResidueTerm_self
    {r j : ℕ} (hr : 0 < r) (p : ℝ[X]) :
    veroneseSectionPolynomial r j (veroneseResidueTerm r j p) = p := by
  ext n
  rw [coeff_veroneseSectionPolynomial hr]
  simp only [veroneseResidueTerm, Polynomial.coeff_X_pow_mul']
  rw [ite_eq_left (by lia)]
  simp [show j + r * n - j = r * n by lia, ← Polynomial.expand_eq_comp_X_pow,
    Polynomial.coeff_expand_mul' hr]

/-- Distinct residue contributions have disjoint Veronese sections. -/
theorem veroneseSectionPolynomial_veroneseResidueTerm_of_ne
    {r i j : ℕ} (hr : 0 < r) (hi : i < r) (hj : j < r) (hij : i ≠ j)
    (p : ℝ[X]) :
    veroneseSectionPolynomial r i (veroneseResidueTerm r j p) = 0 := by
  ext n
  rw [coeff_veroneseSectionPolynomial hr]
  simp only [veroneseResidueTerm, Polynomial.coeff_X_pow_mul']
  split_ifs with hle
  · rw [← Polynomial.expand_eq_comp_X_pow, Polynomial.coeff_expand hr]
    rw [ite_eq_right (not_dvd_sub_add_mul_of_lt hj hi hij.symm hle)]
    simp
  · simp

private theorem veroneseSectionPolynomial_finset_sum {r i : ℕ}
    (hr : 0 < r) (s : Finset ℕ) (f : ℕ → ℝ[X]) :
    veroneseSectionPolynomial r i (∑ j ∈ s, f j) =
      ∑ j ∈ s, veroneseSectionPolynomial r i (f j) := by
  induction s using Finset.induction_on with
  | empty =>
      ext n
      simp [coeff_veroneseSectionPolynomial hr]
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      rw [veroneseSectionPolynomial_add hr, ih]

/-- The `i`th section of a finite sum of residue contributions is its `i`th
input. -/
theorem veroneseSectionPolynomial_sum_veroneseResidueTerm
    {r i : ℕ} (hr : 0 < r) (hi : i < r) (f : ℕ → ℝ[X]) :
    veroneseSectionPolynomial r i
        (∑ j ∈ Finset.range r, veroneseResidueTerm r j (f j)) = f i := by
  rw [veroneseSectionPolynomial_finset_sum hr]
  rw [Finset.sum_eq_single i]
  · exact veroneseSectionPolynomial_veroneseResidueTerm_self hr (f i)
  · intro j hj hji
    exact veroneseSectionPolynomial_veroneseResidueTerm_of_ne
      (i := i) (j := j) hr hi (Finset.mem_range.mp hj) hji.symm (f j)
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hi)).elim

/-- Polynomials are equal when all their valid Veronese sections are equal. -/
theorem eq_of_veroneseSectionPolynomial_eq {r : ℕ} (hr : 0 < r)
    {p q : ℝ[X]}
    (h : ∀ j < r, veroneseSectionPolynomial r j p =
      veroneseSectionPolynomial r j q) :
    p = q := by
  ext n
  let j := n % r
  have hj : j < r := Nat.mod_lt n hr
  have hcoeff := congrArg (fun u : ℝ[X] => u.coeff (n / r)) (h j hj)
  simpa [coeff_veroneseSectionPolynomial hr, j, Nat.mod_add_div n r,
    add_comm] using hcoeff

/-- A polynomial is the sum of its expanded Veronese sections, one for each
residue class. -/
theorem sum_veroneseResidueTerm_veroneseSectionPolynomial
    {r : ℕ} (hr : 0 < r) (p : ℝ[X]) :
    (∑ j ∈ Finset.range r,
        veroneseResidueTerm r j (veroneseSectionPolynomial r j p)) = p := by
  apply eq_of_veroneseSectionPolynomial_eq hr
  intro i hi
  rw [veroneseSectionPolynomial_sum_veroneseResidueTerm hr hi]

/-- Multiplication by `X ^ r` multiplies every `r`-Veronese section by `X`. -/
theorem veroneseSectionPolynomial_X_pow_mul {r k : ℕ} (hr : 0 < r)
    (hk : k < r) (p : ℝ[X]) :
    veroneseSectionPolynomial r k (X ^ r * p) =
      X * veroneseSectionPolynomial r k p := by
  ext n
  cases n with
  | zero =>
      rw [coeff_veroneseSectionPolynomial hr]
      simp [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hk]
  | succ n =>
      rw [coeff_veroneseSectionPolynomial hr]
      simp only [Polynomial.coeff_X_mul]
      rw [Polynomial.coeff_X_pow_mul']
      have heq : k + r * (n + 1) = k + r * n + r := by
        simp [Nat.mul_succ, Nat.add_assoc]
      rw [ite_eq_left (by rw [heq]; lia), heq, Nat.add_sub_cancel,
        coeff_veroneseSectionPolynomial hr]

/-! ## Reconstruction from an indexed difference equation -/

/-- The indexed normalized difference operator from issue #2116. -/
@[expose] def sequenceDelta (a b : ℕ → ℝ) (P : ℕ → ℝ[X]) : ℕ → ℝ[X] :=
  fun n ↦ C (b n)⁻¹ * (P (n + 1) - C (a n) * P n)

/-- Solving the defining difference equation for its next term. -/
theorem sequenceDelta_next_eq {a b : ℕ → ℝ} (hb : ∀ n, b n ≠ 0)
    (P : ℕ → ℝ[X]) (n : ℕ) :
    P (n + 1) = C (a n) * P n + C (b n) * sequenceDelta a b P n := by
  simp [sequenceDelta, ← mul_assoc, ← Polynomial.C_mul, hb n]

/-- The polynomial reconstructed at index `n` from the first `r` iterated
differences of `P`. -/
@[expose] def reconstructedVeroneseParent (r : ℕ) (a b : ℕ → ℝ)
    (P : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range r,
    veroneseResidueTerm r j (((sequenceDelta a b)^[r - 1 - j] P) n)

/-- Each section of the reconstructed parent is the corresponding iterated
difference. -/
theorem veroneseSectionPolynomial_reconstructedVeroneseParent
    {r i : ℕ} (hr : 0 < r) (hi : i < r) (a b : ℕ → ℝ)
    (P : ℕ → ℝ[X]) (n : ℕ) :
    veroneseSectionPolynomial r i (reconstructedVeroneseParent r a b P n) =
      ((sequenceDelta a b)^[r - 1 - i] P) n := by
  exact veroneseSectionPolynomial_sum_veroneseResidueTerm hr hi _

/-- The last section of the reconstructed parent is the original row. -/
theorem veroneseSectionPolynomial_reconstructedVeroneseParent_last
    {r : ℕ} (hr : 0 < r) (a b : ℕ → ℝ) (P : ℕ → ℝ[X]) (n : ℕ) :
    veroneseSectionPolynomial r (r - 1)
        (reconstructedVeroneseParent r a b P n) = P n := by
  rw [veroneseSectionPolynomial_reconstructedVeroneseParent hr (by lia)]
  simp

/-- The zeroth section after multiplication by `a + bX`. -/
theorem veroneseSectionPolynomial_linearFactor_mul_zero {r : ℕ}
    (hr : 0 < r) (a b : ℝ) (p : ℝ[X]) :
    veroneseSectionPolynomial r 0 ((C a + C b * X) * p) =
      C a * veroneseSectionPolynomial r 0 p +
        C b * X * veroneseSectionPolynomial r (r - 1) p := by
  have hfactor : (C a + C b * X) * p = C a * p + C b * (X * p) := by ring
  rw [hfactor, veroneseSectionPolynomial_add hr,
    veroneseSectionPolynomial_C_mul hr,
    veroneseSectionPolynomial_C_mul hr,
    veroneseSectionPolynomial_X_mul_zero hr]
  ring

/-- A positive section after multiplication by `a + bX`. -/
theorem veroneseSectionPolynomial_linearFactor_mul_succ {r k : ℕ}
    (hk : k + 1 < r) (a b : ℝ) (p : ℝ[X]) :
    veroneseSectionPolynomial r (k + 1) ((C a + C b * X) * p) =
      C a * veroneseSectionPolynomial r (k + 1) p +
        C b * veroneseSectionPolynomial r k p := by
  have hr : 0 < r := by lia
  have hfactor : (C a + C b * X) * p = C a * p + C b * (X * p) := by ring
  rw [hfactor, veroneseSectionPolynomial_add hr,
    veroneseSectionPolynomial_C_mul hr,
    veroneseSectionPolynomial_C_mul hr,
    veroneseSectionPolynomial_X_mul_succ hk]

/-- The equation `Δ^r P = X P` makes the reconstructed parents satisfy the
linear-factor recurrence.  This is the central algebraic step in the inverse
recognition theorem of issue #2116. -/
theorem reconstructedVeroneseParent_succ {r : ℕ} (hr : 0 < r)
    {a b : ℕ → ℝ} (hb : ∀ n, b n ≠ 0) {P : ℕ → ℝ[X]}
    (hcycle : ∀ n, ((sequenceDelta a b)^[r] P) n = X * P n) (n : ℕ) :
    reconstructedVeroneseParent r a b P (n + 1) =
      (C (a n) + C (b n) * X) * reconstructedVeroneseParent r a b P n := by
  apply eq_of_veroneseSectionPolynomial_eq hr
  intro i hi
  cases i with
  | zero =>
      rw [veroneseSectionPolynomial_reconstructedVeroneseParent hr hi,
        veroneseSectionPolynomial_linearFactor_mul_zero hr,
        veroneseSectionPolynomial_reconstructedVeroneseParent hr hi,
        veroneseSectionPolynomial_reconstructedVeroneseParent_last hr]
      have hnext := sequenceDelta_next_eq (a := a) (b := b) hb
        ((sequenceDelta a b)^[r - 1] P) n
      rw [← Function.iterate_succ_apply' (sequenceDelta a b) (r - 1) P] at hnext
      rw [Nat.succ_eq_add_one, show r - 1 + 1 = r by lia, hcycle n] at hnext
      simpa [mul_assoc] using hnext
  | succ k =>
      rw [veroneseSectionPolynomial_reconstructedVeroneseParent hr hi,
        veroneseSectionPolynomial_linearFactor_mul_succ hi,
        veroneseSectionPolynomial_reconstructedVeroneseParent hr hi,
        veroneseSectionPolynomial_reconstructedVeroneseParent hr (by lia)]
      have hnext := sequenceDelta_next_eq (a := a) (b := b) hb
        ((sequenceDelta a b)^[r - 1 - (k + 1)] P) n
      rw [← Function.iterate_succ_apply' (sequenceDelta a b)
        (r - 1 - (k + 1)) P] at hnext
      rw [Nat.succ_eq_add_one,
        show r - 1 - (k + 1) + 1 = r - 1 - k by lia] at hnext
      exact hnext

/-- Iterating the parent recurrence gives the product parent with the explicit
seed reconstructed from the first `r` differences at index zero. -/
theorem reconstructedVeroneseParent_eq_mul_prod {r : ℕ} (hr : 0 < r)
    {a b : ℕ → ℝ} (hb : ∀ n, b n ≠ 0) {P : ℕ → ℝ[X]}
    (hcycle : ∀ n, ((sequenceDelta a b)^[r] P) n = X * P n) (n : ℕ) :
    reconstructedVeroneseParent r a b P n =
      reconstructedVeroneseParent r a b P 0 *
        ∏ i ∈ Finset.range n, (C (a i) + C (b i) * X) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [reconstructedVeroneseParent_succ hr hb hcycle, ih,
        Finset.prod_range_succ]
      ring

/-- **Inverse product-parent recognition.**  If `Δ^r P = X P`, then every
row is the last Veronese section of the explicit seed times the indexed product
of linear factors. -/
theorem veroneseSectionPolynomial_seed_mul_prod_eq {r : ℕ} (hr : 0 < r)
    {a b : ℕ → ℝ} (hb : ∀ n, b n ≠ 0) {P : ℕ → ℝ[X]}
    (hcycle : ∀ n, ((sequenceDelta a b)^[r] P) n = X * P n) (n : ℕ) :
    veroneseSectionPolynomial r (r - 1)
        (reconstructedVeroneseParent r a b P 0 *
          ∏ i ∈ Finset.range n, (C (a i) + C (b i) * X)) = P n := by
  rw [← reconstructedVeroneseParent_eq_mul_prod hr hb hcycle]
  exact veroneseSectionPolynomial_reconstructedVeroneseParent_last hr a b P n

/-! ## Converse and uniqueness -/

/-- The scalar product parent with seed `H`. -/
@[expose] def veroneseProductParent (a b : ℕ → ℝ) (H : ℝ[X])
    (n : ℕ) : ℝ[X] :=
  H * ∏ i ∈ Finset.range n, (C (a i) + C (b i) * X)

/-- A fixed residue row of a scalar product parent. -/
@[expose] def veroneseProductRow (r j : ℕ) (a b : ℕ → ℝ)
    (H : ℝ[X]) (n : ℕ) : ℝ[X] :=
  veroneseSectionPolynomial r j (veroneseProductParent a b H n)

private theorem veroneseProductParent_succ (a b : ℕ → ℝ) (H : ℝ[X]) (n : ℕ) :
    veroneseProductParent a b H (n + 1) =
      (C (a n) + C (b n) * X) * veroneseProductParent a b H n := by
  simp only [veroneseProductParent, Finset.prod_range_succ]
  ring

/-- Applying `Δ` to a positive residue row of a product parent selects the
preceding residue. -/
theorem sequenceDelta_veroneseProductRow_succ {r k : ℕ} (hk : k + 1 < r)
    {a b : ℕ → ℝ} (hb : ∀ n, b n ≠ 0) (H : ℝ[X]) :
    sequenceDelta a b (veroneseProductRow r (k + 1) a b H) =
      veroneseProductRow r k a b H := by
  funext n
  simp only [sequenceDelta, veroneseProductRow]
  rw [veroneseProductParent_succ,
    veroneseSectionPolynomial_linearFactor_mul_succ hk]
  simp [← mul_assoc, ← Polynomial.C_mul, hb n]

/-- Applying `Δ` to the zeroth residue row wraps to `X` times the last
residue. -/
theorem sequenceDelta_veroneseProductRow_zero {r : ℕ} (hr : 0 < r)
    {a b : ℕ → ℝ} (hb : ∀ n, b n ≠ 0) (H : ℝ[X]) :
    sequenceDelta a b (veroneseProductRow r 0 a b H) =
      fun n ↦ X * veroneseProductRow r (r - 1) a b H n := by
  funext n
  simp only [sequenceDelta, veroneseProductRow]
  rw [veroneseProductParent_succ,
    veroneseSectionPolynomial_linearFactor_mul_zero hr]
  simp [← mul_assoc, ← Polynomial.C_mul, hb n]

private theorem iterate_sequenceDelta_veroneseProductRow_last
    {r m : ℕ} (hr : 0 < r) (hm : m ≤ r - 1) {a b : ℕ → ℝ}
    (hb : ∀ n, b n ≠ 0) (H : ℝ[X]) :
    (sequenceDelta a b)^[m] (veroneseProductRow r (r - 1) a b H) =
      veroneseProductRow r (r - 1 - m) a b H := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih (by lia)]
      let k := r - 1 - m - 1
      have hk : k + 1 < r := by dsimp [k]; lia
      rw [show r - 1 - m = k + 1 by dsimp [k]; lia,
        sequenceDelta_veroneseProductRow_succ hk hb]
      congr 2

/-- Every scalar product parent satisfies the recognition equation
`Δ^r P = X P` on its last residue row. -/
theorem iterate_sequenceDelta_veroneseProductRow_last_eq {r : ℕ}
    (hr : 0 < r) {a b : ℕ → ℝ} (hb : ∀ n, b n ≠ 0) (H : ℝ[X]) :
    (sequenceDelta a b)^[r] (veroneseProductRow r (r - 1) a b H) =
      fun n ↦ X * veroneseProductRow r (r - 1) a b H n := by
  have hsucc :
      (sequenceDelta a b)^[r] (veroneseProductRow r (r - 1) a b H) =
        sequenceDelta a b
          ((sequenceDelta a b)^[r - 1]
            (veroneseProductRow r (r - 1) a b H)) := by
    simpa only [Nat.succ_eq_add_one, show r - 1 + 1 = r by lia] using
      Function.iterate_succ_apply' (sequenceDelta a b) (r - 1)
        (veroneseProductRow r (r - 1) a b H)
  rw [hsucc, iterate_sequenceDelta_veroneseProductRow_last hr (le_refl _) hb]
  rw [show r - 1 - (r - 1) = 0 by lia]
  exact sequenceDelta_veroneseProductRow_zero (a := a) (b := b) hr hb H

/-- A seed representing `P` is forced to equal the explicit reconstruction
from the first `r` differences of `P` at zero. -/
theorem eq_reconstructedVeroneseParent_zero_of_productRow_eq
    {r : ℕ} (hr : 0 < r) {a b : ℕ → ℝ} (hb : ∀ n, b n ≠ 0)
    {P : ℕ → ℝ[X]} {H : ℝ[X]}
    (hrow : ∀ n, veroneseProductRow r (r - 1) a b H n = P n) :
    H = reconstructedVeroneseParent r a b P 0 := by
  have hfun : veroneseProductRow r (r - 1) a b H = P := funext hrow
  subst P
  apply eq_of_veroneseSectionPolynomial_eq hr
  intro i hi
  rw [veroneseSectionPolynomial_reconstructedVeroneseParent hr hi,
    iterate_sequenceDelta_veroneseProductRow_last hr (by lia) hb]
  rw [show r - 1 - (r - 1 - i) = i by lia]
  simp [veroneseProductRow, veroneseProductParent]

/-- A product-parent representation implies the recognition equation. -/
theorem iterate_sequenceDelta_eq_X_mul_of_productRow_eq
    {r : ℕ} (hr : 0 < r) {a b : ℕ → ℝ} (hb : ∀ n, b n ≠ 0)
    {P : ℕ → ℝ[X]} {H : ℝ[X]}
    (hrow : ∀ n, veroneseProductRow r (r - 1) a b H n = P n) :
    ∀ n, ((sequenceDelta a b)^[r] P) n = X * P n := by
  have hfun : veroneseProductRow r (r - 1) a b H = P := funext hrow
  subst P
  intro n
  exact congrFun (iterate_sequenceDelta_veroneseProductRow_last_eq hr hb H) n

/-- **Product-parent recognition criterion.**  The equation `Δ^r P = X P`
is equivalent to existence of a unique scalar seed.  The forward witness is
the explicit sum of the first `r` iterated differences at index zero. -/
theorem iterate_sequenceDelta_eq_X_mul_iff_existsUnique_seed
    {r : ℕ} (hr : 0 < r) {a b : ℕ → ℝ} (hb : ∀ n, b n ≠ 0)
    (P : ℕ → ℝ[X]) :
    (∀ n, ((sequenceDelta a b)^[r] P) n = X * P n) ↔
      ∃! H : ℝ[X], ∀ n,
        veroneseProductRow r (r - 1) a b H n = P n := by
  constructor
  · intro hcycle
    refine ⟨reconstructedVeroneseParent r a b P 0, ?_, ?_⟩
    · intro n
      exact veroneseSectionPolynomial_seed_mul_prod_eq hr hb hcycle n
    · intro H hH
      exact eq_reconstructedVeroneseParent_zero_of_productRow_eq hr hb hH
  · rintro ⟨H, hH, _⟩
    exact iterate_sequenceDelta_eq_X_mul_of_productRow_eq hr hb hH

/-! ## Real-rootedness consequence and an explicit family -/

private theorem hasNonnegCoeffs_linearFactor {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasNonnegCoeffs (C a + C b * X) :=
  (hasNonnegCoeffs_C ha).add (hasNonnegCoeffs_C_mul hb hasNonnegCoeffs_X)

private theorem splits_linearFactor {a b : ℝ} (hb : b ≠ 0) :
    (C a + C b * X).Splits := by
  have heq : C a + C b * X = C b * (X + C (a / b)) := by
    rw [mul_add, ← Polynomial.C_mul]
    rw [show b * (a / b) = a by field_simp]
    ring
  rw [heq]
  exact (Polynomial.Splits.X_add_C (a / b)).C_mul b

private theorem veroneseProductParent_hasNonnegCoeffs
    {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    {H : ℝ[X]} (hH : HasNonnegCoeffs H) :
    ∀ n, HasNonnegCoeffs (veroneseProductParent a b H n) := by
  intro n
  induction n with
  | zero => simpa [veroneseProductParent] using hH
  | succ n ih =>
      rw [veroneseProductParent_succ]
      exact (hasNonnegCoeffs_linearFactor (ha n) (hb n)).mul ih

private theorem veroneseProductParent_splits
    {a b : ℕ → ℝ} (hb : ∀ n, b n ≠ 0) {H : ℝ[X]} (hH : H.Splits) :
    ∀ n, (veroneseProductParent a b H n).Splits := by
  intro n
  induction n with
  | zero => simpa [veroneseProductParent] using hH
  | succ n ih =>
      rw [veroneseProductParent_succ]
      exact (splits_linearFactor (hb n)).mul ih

/-- A nonnegative splitting reconstructed seed and nonnegative product factors
certify that every recognized row is zero or real-rooted.  This is the
zero-aware PF consequence of the product-parent criterion. -/
theorem sequenceDelta_row_eq_zero_or_splits {r : ℕ} (hr : 0 < r)
    {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n)
    {P : ℕ → ℝ[X]}
    (hcycle : ∀ n, ((sequenceDelta a b)^[r] P) n = X * P n)
    (hseednn : HasNonnegCoeffs (reconstructedVeroneseParent r a b P 0))
    (hseedsplits : (reconstructedVeroneseParent r a b P 0).Splits) (n : ℕ) :
    P n = 0 ∨ (P n).Splits := by
  let H := reconstructedVeroneseParent r a b P 0
  have hparentnn : HasNonnegCoeffs (veroneseProductParent a b H n) :=
    veroneseProductParent_hasNonnegCoeffs ha (fun i ↦ (hb i).le) hseednn n
  have hparentsplits : (veroneseProductParent a b H n).Splits :=
    veroneseProductParent_splits (fun i ↦ (hb i).ne') hseedsplits n
  have hsection := splits_veroneseSectionPolynomial_of_splits_nonneg
    hparentnn hparentsplits hr (by lia : r - 1 < r)
  have hrow := veroneseSectionPolynomial_seed_mul_prod_eq hr
    (fun i ↦ (hb i).ne') hcycle n
  simpa [H, veroneseProductRow, veroneseProductParent, hrow] using hsection

end RealRooted
