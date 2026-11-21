module

public import RealRooted.VeroneseRecognition.Affine
public import RealRooted.PFPolynomial
import RealRooted.VeroneseSectionPair
import RealRooted.Linear

/-!
# Consecutive interlacing for recognized Veronese rows

We combine the checked descending-residue theorem with the linear-factor
section recurrence and the nonnegative Wagner cone. This proves consecutive
interlacing for every canonical residue of a PF product parent, then for the
rows reconstructed by the ordinary and affine recognition equations.

The same-residue conclusion is the product-parent case of
Athanasiadis--Wagner, *Veronese sections and interlacing matrices of
polynomials and formal power series*, arXiv:2404.12989v1, Corollary 5.6(b).
The reconstruction is from the unpublished manuscript recorded in issue #2116.
Here `StrictInterl` allows repeated and shared roots; it asserts oriented weak
interlacing of nonzero polynomials. `Interl` also allows zero rows.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Every canonical Veronese section of a PF polynomial is PF, including zero. -/
theorem IsPFPolynomial.veroneseSection {p : ℝ[X]} (hp : IsPFPolynomial p)
    {r j : ℕ} (hr : 0 < r) (hj : j < r) :
    IsPFPolynomial (veroneseSectionPolynomial r j p) := by
  exact IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    (hasNonnegCoeffs_veroneseSectionPolynomial hr hp.hasNonnegCoeffs)
    (splits_veroneseSectionPolynomial_of_splits_nonneg hp.hasNonnegCoeffs hp.splits hr hj)

/-- Canonical sections of a PF polynomial interlace in descending residue order,
including equal residues and zero sections. -/
theorem interl_veroneseSectionPolynomial_of_residue_le
    {r j k : ℕ} (hr : 0 < r) (hjk : j ≤ k) (hk : k < r)
    {p : ℝ[X]} (hp : IsPFPolynomial p) :
    Interl (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r j p) := by
  obtain rfl | hjk := hjk.eq_or_lt
  · exact (hp.veroneseSection hr hk).interl_self
  by_cases hk0 : veroneseSectionPolynomial r k p = 0
  · rw [hk0]
    exact interl_zero_left _
  by_cases hj0 : veroneseSectionPolynomial r j p = 0
  · rw [hj0]
    exact interl_zero_right _
  have hp0 : p ≠ 0 := by
    intro h
    apply hk0
    ext n
    simp [coeff_veroneseSectionPolynomial hr, h]
  exact (strictInterl_veroneseSectionPolynomial_of_residue_lt hr hjk hk
    hp.hasNonnegCoeffs hp0 hp.splits hj0 hk0).toInterl

/-- Multiplying a PF parent by a nonnegative linear factor moves each canonical
section to its right in zero-aware proper position. -/
theorem interl_veroneseSectionPolynomial_linearFactor_mul
    {r j : ℕ} (hr : 0 < r) (hj : j < r) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {p : ℝ[X]} (hp : IsPFPolynomial p) :
    Interl (veroneseSectionPolynomial r j p)
      (veroneseSectionPolynomial r j ((C a + C b * X) * p)) := by
  have hself := (hp.veroneseSection hr hj).interl_self
  cases j with
  | zero =>
      rw [veroneseSectionPolynomial_linearFactor_mul_zero hr]
      have hlast := hp.veroneseSection hr (by lia : r - 1 < r)
      have hfirst := hp.veroneseSection hr hj
      have hpair := interl_veroneseSectionPolynomial_of_residue_le
        hr (Nat.zero_le (r - 1)) (by lia : r - 1 < r) hp
      have hX := interl_mul_X_of_interl hpair hlast.hasNonnegCoeffs hfirst.hasNonnegCoeffs
      simpa only [mul_assoc] using
        interl_nonneg_combo_right_of_common_left_of_pf hself hX hfirst hlast.X_mul ha hb
  | succ j =>
      rw [veroneseSectionPolynomial_linearFactor_mul_succ hj]
      exact interl_nonneg_combo_right_of_common_left_of_pf hself
        (interl_veroneseSectionPolynomial_of_residue_le hr (by lia) hj hp)
        (hp.veroneseSection hr hj) (hp.veroneseSection hr (by lia)) ha hb

/-- A PF seed and nonnegative linear factors give PF product parents. -/
theorem isPFPolynomial_veroneseProductParent {a b : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n)
    {H : ℝ[X]} (hH : IsPFPolynomial H) (n : ℕ) :
    IsPFPolynomial (veroneseProductParent a b H n) := by
  induction n with
  | zero => simpa [veroneseProductParent] using hH
  | succ n ih =>
      have hfactor : IsPFPolynomial (C (a n) + C (b n) * X) := by
        simpa [add_comm] using
          (IsPFPolynomial.one.X_mul.comp_C_mul_X_add_C (hb n) (ha n))
      simpa [veroneseProductParent, Finset.prod_range_succ, mul_assoc] using ih.mul hfactor

/-- Every canonical product-parent row is PF, including zero rows. -/
theorem isPFPolynomial_veroneseProductRow {r j : ℕ} (hr : 0 < r) (hj : j < r)
    {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n)
    {H : ℝ[X]} (hH : IsPFPolynomial H) (n : ℕ) :
    IsPFPolynomial (veroneseProductRow r j a b H n) :=
  (isPFPolynomial_veroneseProductParent ha hb hH n).veroneseSection hr hj

/-- Consecutive rows of any canonical residue of a PF product parent interlace,
with zero rows allowed. -/
theorem interl_veroneseProductRow_succ {r j : ℕ} (hr : 0 < r) (hj : j < r)
    {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n)
    {H : ℝ[X]} (hH : IsPFPolynomial H) (n : ℕ) :
    Interl (veroneseProductRow r j a b H n)
      (veroneseProductRow r j a b H (n + 1)) := by
  have hnext : veroneseProductParent a b H (n + 1) =
      (C (a n) + C (b n) * X) * veroneseProductParent a b H n := by
    simp only [veroneseProductParent, Finset.prod_range_succ]
    ring
  unfold veroneseProductRow
  rw [hnext]
  exact interl_veroneseSectionPolynomial_linearFactor_mul hr hj (ha n) (hb n).le
    (isPFPolynomial_veroneseProductParent ha hb hH n)

/-- Nonzero consecutive canonical product-parent rows weakly interlace. -/
theorem strictInterl_veroneseProductRow_succ {r j : ℕ} (hr : 0 < r) (hj : j < r)
    {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n)
    {H : ℝ[X]} (hH : IsPFPolynomial H) (n : ℕ)
    (hn : veroneseProductRow r j a b H n ≠ 0)
    (hsucc : veroneseProductRow r j a b H (n + 1) ≠ 0) :
    StrictInterl (veroneseProductRow r j a b H n)
      (veroneseProductRow r j a b H (n + 1)) :=
  (interl_veroneseProductRow_succ hr hj ha hb hH n).toStrictInterl_of_ne hn hsucc

/-- The ordinary recognition equation and its PF seed certify consecutive-row
interlacing, including vanishing rows. -/
theorem sequenceDelta_row_interl {r : ℕ} (hr : 0 < r)
    {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n)
    {P : ℕ → ℝ[X]}
    (hcycle : ∀ n, ((sequenceDelta a b)^[r] P) n = X * P n)
    (hseednn : HasNonnegCoeffs (reconstructedVeroneseParent r a b P 0))
    (hseedsplits : (reconstructedVeroneseParent r a b P 0).Splits) (n : ℕ) :
    Interl (P n) (P (n + 1)) := by
  have hrow : ∀ m, veroneseProductRow r (r - 1) a b
      (reconstructedVeroneseParent r a b P 0) m = P m :=
    veroneseSectionPolynomial_seed_mul_prod_eq hr (fun i ↦ (hb i).ne') hcycle
  simpa only [hrow] using interl_veroneseProductRow_succ hr (by lia : r - 1 < r)
    ha hb (IsPFPolynomial.of_realRooted_nonneg hseednn hseedsplits) n

/-- Nonzero consecutive rows recognized from a PF seed weakly interlace. -/
theorem sequenceDelta_row_strictInterl {r : ℕ} (hr : 0 < r)
    {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n)
    {P : ℕ → ℝ[X]}
    (hcycle : ∀ n, ((sequenceDelta a b)^[r] P) n = X * P n)
    (hseednn : HasNonnegCoeffs (reconstructedVeroneseParent r a b P 0))
    (hseedsplits : (reconstructedVeroneseParent r a b P 0).Splits) (n : ℕ)
    (hn : P n ≠ 0) (hsucc : P (n + 1) ≠ 0) :
    StrictInterl (P n) (P (n + 1)) :=
  (sequenceDelta_row_interl hr ha hb hcycle hseednn hseedsplits n).toStrictInterl_of_ne
    hn hsucc

/-- A positive affine change preserves consecutive product-row interlacing;
the translation parameter can have either sign. -/
theorem interl_affineVeroneseProductRow_succ
    {r j : ℕ} (hr : 0 < r) (hj : j < r) {α β : ℝ} (hβ : 0 < β)
    {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n)
    {H : ℝ[X]} (hH : IsPFPolynomial H) (n : ℕ) :
    Interl (affineVeroneseProductRow r j α β a b H n)
      (affineVeroneseProductRow r j α β a b H (n + 1)) := by
  have h := ((interl_veroneseProductRow_succ hr hj ha hb hH n).comp_X_add_C α).comp_C_mul_X
    hβ
  simpa [affineVeroneseProductRow, comp_assoc, add_comm] using h

/-- The affine recognition equation and its PF seed certify consecutive-row
interlacing for every positive slope and every real translation. -/
theorem sequenceDelta_affine_row_interl {r : ℕ} (hr : 0 < r)
    {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n)
    {α β : ℝ} (hβ : 0 < β) {P : ℕ → ℝ[X]}
    (hcycle : ∀ n, ((sequenceDelta a b)^[r] P) n =
      (C α + C β * X) * P n)
    (hseednn : HasNonnegCoeffs (reconstructedAffineVeroneseSeed r α β a b P))
    (hseedsplits : (reconstructedAffineVeroneseSeed r α β a b P).Splits) (n : ℕ) :
    Interl (P n) (P (n + 1)) := by
  obtain ⟨H, hrow, _⟩ :=
    (iterate_sequenceDelta_eq_affine_mul_iff_existsUnique_seed hr
      (fun i ↦ (hb i).ne') hβ.ne' P).mp hcycle
  have hH : IsPFPolynomial H := by
    rw [eq_reconstructedAffineVeroneseSeed_of_affineProductRow_eq hr
      (fun i ↦ (hb i).ne') hβ.ne' hrow]
    exact IsPFPolynomial.of_realRooted_nonneg hseednn hseedsplits
  simpa only [hrow] using
    interl_affineVeroneseProductRow_succ (α := α) hr (by lia : r - 1 < r) hβ ha hb hH n

/-- Nonzero consecutive affine-recognized rows weakly interlace. -/
theorem sequenceDelta_affine_row_strictInterl {r : ℕ} (hr : 0 < r)
    {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n)
    {α β : ℝ} (hβ : 0 < β) {P : ℕ → ℝ[X]}
    (hcycle : ∀ n, ((sequenceDelta a b)^[r] P) n =
      (C α + C β * X) * P n)
    (hseednn : HasNonnegCoeffs (reconstructedAffineVeroneseSeed r α β a b P))
    (hseedsplits : (reconstructedAffineVeroneseSeed r α β a b P).Splits) (n : ℕ)
    (hn : P n ≠ 0) (hsucc : P (n + 1) ≠ 0) :
    StrictInterl (P n) (P (n + 1)) :=
  (sequenceDelta_affine_row_interl hr ha hb hβ hcycle hseednn hseedsplits n).toStrictInterl_of_ne
    hn hsucc

/-- Roots of an affine PF product-parent row are at most `-α / β`,
without a sign restriction on `α`. Zero rows have empty root multisets. -/
theorem roots_affineVeroneseProductRow_le
    {r j : ℕ} (hr : 0 < r) (hj : j < r) {α β : ℝ} (hβ : 0 < β)
    {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n)
    {H : ℝ[X]} (hH : IsPFPolynomial H) (n : ℕ)
    {x : ℝ} (hx : x ∈ (affineVeroneseProductRow r j α β a b H n).roots) :
    x ≤ -α / β := by
  rw [affineVeroneseProductRow, add_comm (C α), roots_comp_C_mul_X_add_C
    _ β α (isUnit_iff_ne_zero.mpr hβ.ne')] at hx
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  have hy0 := (isPFPolynomial_veroneseProductRow hr hj ha hb hH n).roots_nonpos y hy
  simp only [Ring.inverse_eq_inv]
  calc
    β⁻¹ * (y - α) ≤ β⁻¹ * (0 - α) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hy0 α) (inv_nonneg.mpr hβ.le)
    _ = -α / β := by ring

/-- The PF reconstructed seed in an affine recognition equation confines all
row roots to `(-∞, -α / β]`. -/
theorem sequenceDelta_affine_row_roots_le {r : ℕ} (hr : 0 < r)
    {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n)
    {α β : ℝ} (hβ : 0 < β) {P : ℕ → ℝ[X]}
    (hcycle : ∀ n, ((sequenceDelta a b)^[r] P) n =
      (C α + C β * X) * P n)
    (hseednn : HasNonnegCoeffs (reconstructedAffineVeroneseSeed r α β a b P))
    (hseedsplits : (reconstructedAffineVeroneseSeed r α β a b P).Splits) (n : ℕ)
    {x : ℝ} (hx : x ∈ (P n).roots) :
    x ≤ -α / β := by
  obtain ⟨H, hrow, _⟩ :=
    (iterate_sequenceDelta_eq_affine_mul_iff_existsUnique_seed hr
      (fun i ↦ (hb i).ne') hβ.ne' P).mp hcycle
  have hH : IsPFPolynomial H := by
    rw [eq_reconstructedAffineVeroneseSeed_of_affineProductRow_eq hr
      (fun i ↦ (hb i).ne') hβ.ne' hrow]
    exact IsPFPolynomial.of_realRooted_nonneg hseednn hseedsplits
  rw [← hrow n] at hx
  exact roots_affineVeroneseProductRow_le hr (by lia) hβ ha hb hH n hx

end RealRooted
