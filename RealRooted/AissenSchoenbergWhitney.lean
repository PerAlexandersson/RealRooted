import RealRooted.AissenSchoenbergWhitneyBase
import RealRooted.ASWKarlinThreshold
import RealRooted.ASWKarlinKernel
import RealRooted.DegreeDropReversal
import RealRooted.QuadraticRoot
import RealRooted.WagnerX
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Algebra.Polynomial

open Polynomial Matrix Filter

noncomputable section

namespace RealRooted

/-!
# Aissen--Schoenberg--Whitney interfaces

This file records the Toeplitz total-nonnegativity formulation of
Pólya-frequency sequences and proves both directions of the classical
Aissen--Schoenberg--Whitney theorem for polynomials.

Reference: M. Aissen, I. J. Schoenberg, and A. M. Whitney, *On the generating
functions of totally positive sequences. I*, J. Analyse Math. 2 (1952),
93--103.
-/

variable {a : ℕ → ℝ}

/-- If the zeroth term vanishes, deleting it identifies the new Toeplitz
matrix with an order-preserving row submatrix of the original one. -/
lemma toeplitz_tail_of_zero {a : ℕ → ℝ} (h0 : a 0 = 0) :
    toeplitz (fun n => a (n + 1)) =
      (toeplitz a).submatrix (fun i => i + 1) id := by
  ext i j
  simp only [toeplitz_apply, submatrix_apply, id_eq]
  by_cases hji : j ≤ i
  · rw [ite_eq_left hji, ite_eq_left (by lia)]
    congr 1
    lia
  · rw [ite_eq_right hji]
    by_cases hnext : j = i + 1
    · rw [hnext, ite_eq_left (by lia)]
      simp [h0]
    · rw [ite_eq_right (by lia)]

/-- Deleting a zero first term preserves the Pólya-frequency property. -/
protected theorem IsPolyaFreqSeq.tail_of_zero {a : ℕ → ℝ}
    (hpf : IsPolyaFreqSeq a) (h0 : a 0 = 0) :
    IsPolyaFreqSeq (fun n => a (n + 1)) := by
  rw [IsPolyaFreqSeq, toeplitz_tail_of_zero h0]
  exact hpf.submatrix (fun _ _ h => by lia) strictMono_id

/-- Deleting any finite initial block of zero entries preserves the
Pólya-frequency property. -/
protected theorem IsPolyaFreqSeq.tail_of_zeros {a : ℕ → ℝ}
    (hpf : IsPolyaFreqSeq a) (s : ℕ) (hzero : ∀ k < s, a k = 0) :
    IsPolyaFreqSeq (fun n => a (n + s)) := by
  induction s generalizing a with
  | zero => simpa
  | succ s ih =>
      have h0 : a 0 = 0 := hzero 0 (Nat.succ_pos s)
      have htail : IsPolyaFreqSeq (fun n => a (n + 1)) := hpf.tail_of_zero h0
      have htail_zero : ∀ k < s, a (k + 1) = 0 :=
        fun k _ => hzero (k + 1) (by lia)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih htail htail_zero

/-- Inserting a finite prefix of zeroes preserves the Pólya-frequency
property. -/
protected theorem IsPolyaFreqSeq.prefix_zeros {a : ℕ → ℝ}
    (hpf : IsPolyaFreqSeq a) (s : ℕ) :
    IsPolyaFreqSeq (fun n => if s ≤ n then a (n - s) else 0) := by
  rw [IsPolyaFreqSeq]
  have htoeplitz : toeplitz (fun n => if s ≤ n then a (n - s) else 0) =
      (toeplitz a).submatrix id (fun j => j + s) := by
    ext i j
    simp only [toeplitz_apply, submatrix_apply, id_eq]
    by_cases hji : j ≤ i
    · rw [ite_eq_left hji]
      have hsub : s ≤ i - j ↔ j + s ≤ i := by lia
      simp [hsub]
      congr 1
      lia
    · have hshift : ¬ j + s ≤ i := fun h => hji (le_trans (Nat.le_add_right _ _) h)
      simp [hji, hshift]
  rw [htoeplitz]
  exact hpf.submatrix strictMono_id (fun _ _ h => by lia)

/-- If a PF polynomial has zero constant coefficient, dividing by `X`
preserves the PF property of its coefficient sequence. -/
protected theorem IsPolyaFreqSeq.divX_coeff {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq p.coeff) (h0 : p.coeff 0 = 0) :
    IsPolyaFreqSeq p.divX.coeff := by
  rw [show p.divX.coeff = fun n => p.coeff (n + 1) by
    funext n
    exact Polynomial.coeff_divX]
  exact hpf.tail_of_zero h0

/-- Toeplitz total nonnegativity of the coefficient sequence already implies
nonnegative coefficients. -/
theorem hasNonnegCoeffs_of_IsPolyaFreqSeq_coeff
    {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq p.coeff) :
    HasNonnegCoeffs p :=
  fun k => hpf.nonneg k

/-- PF coefficient sequences have no positive real roots.  Thus the remaining
content of the forward Aissen--Schoenberg--Whitney theorem is the splitting
conjunct. -/
theorem roots_nonpos_of_isPolyaFreqSeq_coeff
    {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq p.coeff) :
    ∀ r ∈ p.roots, r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs (hasNonnegCoeffs_of_IsPolyaFreqSeq_coeff hpf)

lemma continuous_toeplitz_minor_det_add_mul {a b : ℕ → ℝ}
    {n : ℕ} (rows cols : Fin n → ℕ) :
    Continuous fun μ : ℝ =>
      ((toeplitz (fun k => a k + μ * b k)).submatrix rows cols).det := by
  simp only [Matrix.det_apply]
  apply continuous_finsetSum
  intro σ _
  apply Continuous.const_smul
  apply continuous_finsetProd
  intro i _
  by_cases hle : cols i ≤ rows (σ i)
  · simp only [submatrix_apply, toeplitz_apply, hle, ↓reduceIte]
    exact continuous_const.add (continuous_id.mul continuous_const)
  · simp only [submatrix_apply, toeplitz_apply, hle, ↓reduceIte]
    exact continuous_const

/-- Pólya-frequency sequences are closed under coefficientwise positive affine limits. -/
theorem IsPolyaFreqSeq.of_forall_pos_add_mul {a b : ℕ → ℝ}
    (h : ∀ {μ : ℝ}, 0 < μ → IsPolyaFreqSeq (fun n => a n + μ * b n)) :
    IsPolyaFreqSeq a := by
  intro n rows cols hrows hcols
  let D : ℝ → ℝ := fun μ =>
    ((toeplitz (fun k => a k + μ * b k)).submatrix rows cols).det
  have hD_nonneg : ∀ μ : ℝ, 0 < μ → 0 ≤ D μ :=
    fun μ hμ => h hμ hrows hcols
  have hD_lim :
      Tendsto D (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (D 0)) :=
    (continuous_toeplitz_minor_det_add_mul (a := a) (b := b) rows cols).continuousAt
      |>.continuousWithinAt
  have hconst_lim : Tendsto (fun _ : ℝ => (0 : ℝ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_const_nhds
  have hD0 : 0 ≤ D 0 :=
    le_of_tendsto_of_tendsto hconst_lim hD_lim (by
      filter_upwards [self_mem_nhdsWithin] with μ hμ
      exact hD_nonneg μ hμ)
  simpa [D, toeplitz] using hD0

/-! ### Karlin sector endgame -/

/-- A complex number excluded from every open Karlin sector has maximal
absolute argument. -/
lemma abs_arg_eq_pi_of_forall_aswSectorThreshold {z : ℂ} {degree : ℕ}
    (hsector : ∀ order : ℕ, aswSectorThreshold degree order ≤ |z.arg|) :
    |z.arg| = Real.pi := by
  apply le_antisymm (Complex.abs_arg_le_pi z)
  exact le_of_tendsto (tendsto_aswSectorThreshold degree)
    (Eventually.of_forall hsector)

/-- A complex number excluded from every open Karlin sector lies on the
negative-real ray. The `-π` branch is impossible for Mathlib's convention for
`Complex.arg`. -/
lemma arg_eq_pi_of_forall_aswSectorThreshold {z : ℂ} {degree : ℕ}
    (hsector : ∀ order : ℕ, aswSectorThreshold degree order ≤ |z.arg|) :
    z.arg = Real.pi := by
  rcases (abs_eq Real.pi_pos.le).mp
      (abs_arg_eq_pi_of_forall_aswSectorThreshold hsector) with h | h
  · exact h
  · exact (Complex.neg_pi_lt_arg z).ne h.symm |>.elim

/-- Karlin's finite-order sector estimates for every complex root imply that
the original real polynomial splits over `ℝ`. This is the analytic endgame of
the forward Aissen--Schoenberg--Whitney proof. -/
theorem splits_of_forall_complex_root_aswSectorThreshold {p : ℝ[X]}
    (hsector : ∀ z ∈ (p.map (algebraMap ℝ ℂ)).roots,
      ∀ order : ℕ, aswSectorThreshold p.natDegree order ≤ |z.arg|) :
    p.Splits := by
  refine Polynomial.Splits.of_splits_map (algebraMap ℝ ℂ)
    (IsAlgClosed.splits _) ?_
  intro z hz
  have hzarg : z.arg = Real.pi :=
    arg_eq_pi_of_forall_aswSectorThreshold (hsector z hz)
  have hzneg : z.re < 0 ∧ z.im = 0 :=
    Complex.arg_eq_pi_iff.mp hzarg
  refine ⟨z.re, Complex.ext ?_ hzneg.2.symm⟩
  simp

/-- Karlin's finite-order sector estimate, in the threshold notation used by
the ASW endgame. -/
theorem aswSectorThreshold_le_abs_arg_of_isPolyaFreqSeq_coeff {p : ℝ[X]} {z : ℂ}
    (hdegree : 0 < p.natDegree) (hconst : 0 < p.coeff 0)
    (hpf : IsPolyaFreqSeq p.coeff)
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots) (order : ℕ) :
    aswSectorThreshold p.natDegree order ≤ |z.arg| := by
  by_cases horder : order = 0
  · simp [aswSectorThreshold, horder]
  · exact aswKarlinSectorThreshold_le_abs_arg
      (p := p) (z := z) hz hdegree hconst hpf
      (horder := Nat.pos_of_ne_zero horder)

/-- Positive-constant-coefficient case of the forward Aissen--Schoenberg--Whitney
splitting theorem.  In positive degree, Karlin's sector estimates exclude every
nonreal root. -/
theorem aissenSchoenbergWhitneyForwardSplits_positiveConstant {p : ℝ[X]}
    (hconst : 0 < p.coeff 0) (hpf : IsPolyaFreqSeq p.coeff) :
    p.Splits := by
  rcases Nat.eq_zero_or_pos p.natDegree with hdeg | hdeg
  · exact Polynomial.Splits.of_natDegree_le_one (by lia)
  · exact splits_of_forall_complex_root_aswSectorThreshold fun _ hz order =>
      aswSectorThreshold_le_abs_arg_of_isPolyaFreqSeq_coeff hdeg hconst hpf hz order

/-! ### Reduction to positive constant coefficient -/

/-- Splitting-only form of forward ASW.  Zero constant coefficients are removed
one at a time: if the constant coefficient is zero, divide by `X`; the
coefficient tail is still PF and has strictly smaller degree. -/
theorem aissenSchoenbergWhitneyForwardSplits {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq p.coeff) :
    p.Splits := by
  revert hpf
  induction hdeg : p.natDegree using Nat.strong_induction_on generalizing p with
  | h d ih =>
      intro hpf
      by_cases hp0 : p = 0
      · exact hp0 ▸ Polynomial.Splits.zero
      have hc0 := hpf.nonneg 0
      rcases hc0.eq_or_lt with hc0zero | hc0pos
      · have hc0zero' : p.coeff 0 = 0 := hc0zero.symm
        have hdpos : 0 < d := by
          by_contra hd
          have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
          have hpC : p = C (p.coeff 0) :=
            Polynomial.eq_C_of_natDegree_eq_zero (hdeg.trans hd0)
          rw [hpC, hc0zero', Polynomial.C_0] at hp0
          exact hp0 rfl
        have hdivdeg : p.divX.natDegree < d := by
          rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hdeg]
          lia
        have hdivsplits : p.divX.Splits :=
          ih p.divX.natDegree hdivdeg rfl (hpf.divX_coeff hc0zero')
        exact DegreeDropReversal.splits_of_divX_splits_of_coeff_zero
          hc0zero' hdivsplits
      · exact aissenSchoenbergWhitneyForwardSplits_positiveConstant hc0pos hpf

/-- Forward Aissen--Schoenberg--Whitney theorem. -/
theorem aissenSchoenbergWhitneyForward {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq p.coeff) :
    p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0 :=
  ⟨aissenSchoenbergWhitneyForwardSplits hpf, roots_nonpos_of_isPolyaFreqSeq_coeff hpf⟩

/-- Zero-aware forward ASW interface.  This is often the most convenient
closure form: a PF coefficient sequence gives either the zero polynomial or a
strictly real-rooted polynomial with nonpositive roots. -/
theorem aissenSchoenbergWhitneyForwardOrZero {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq p.coeff) :
    (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0 :=
  ⟨Or.inr (aissenSchoenbergWhitneyForwardSplits hpf),
    roots_nonpos_of_isPolyaFreqSeq_coeff hpf⟩

/-- Forward ASW discriminant bound in degree at most two.  If the coefficient
sequence of `p` is Pólya-frequency and `p.natDegree ≤ 2`, then
`4 * (coeff 0 * coeff 2) ≤ (coeff 1) ^ 2`. -/
lemma disc_nonneg_of_isPolyaFreqSeq_natDegree_le_two {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq p.coeff) (hdeg : p.natDegree ≤ 2) :
    4 * (p.coeff 0 * p.coeff 2) ≤ (p.coeff 1) ^ 2 := by
  rcases hdeg.lt_or_eq with hlt | h2
  · rw [coeff_eq_zero_of_natDegree_lt hlt]
    nlinarith [sq_nonneg (p.coeff 1)]
  · obtain ⟨x, hx⟩ := (aissenSchoenbergWhitneyForwardSplits hpf).exists_eval_eq_zero
      (degree_ne_of_natDegree_ne (by simp [h2]))
    rw [eval_eq_sum_range, h2] at hx
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hx
    have hdisc := discrim_eq_sq_of_quadratic_eq_zero
      (a := p.coeff 2) (b := p.coeff 1) (c := p.coeff 0) (x := x) (by linear_combination hx)
    rw [discrim] at hdisc
    nlinarith [sq_nonneg (2 * p.coeff 2 * x + p.coeff 1)]

/-- Equivalent forward ASW statement with the redundant nonnegative-coefficient
hypothesis removed. -/
theorem aissenSchoenbergWhitneyForwardNoNonneg {p : ℝ[X]}
    (hp0 : p ≠ 0) (hpf : IsPolyaFreqSeq p.coeff) :
    (p ≠ 0 ∧ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0 :=
  ⟨⟨hp0, aissenSchoenbergWhitneyForwardSplits hpf⟩,
    roots_nonpos_of_isPolyaFreqSeq_coeff hpf⟩

/-- Without a nonzero hypothesis, the forward ASW interface would force the
zero polynomial to be real-rooted, contrary to the strict local definition of
`p ≠ 0 ∧ p.Splits`. -/
theorem not_aissenSchoenbergWhitneyForward_without_nonzero :
    ¬ (∀ ⦃p : ℝ[X]⦄,
      HasNonnegCoeffs p →
      IsPolyaFreqSeq p.coeff →
      (p ≠ 0 ∧ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) :=
  fun h => (h (p := 0) (by simp [HasNonnegCoeffs])
    (by
      convert isPolyaFreqSeq_zero
      exact coeff_zero _)).1.1 rfl

lemma toeplitz_one_coeff : toeplitz (fun n ↦ (1 : ℝ[X]).coeff n) = 1 := by
  ext i j
  simp only [toeplitz_apply, coeff_one, Matrix.one_apply]
  lia

lemma IsPolyaFreqSeq.one :
    IsPolyaFreqSeq (fun n ↦ (1 : ℝ[X]).coeff n) := by
  simp [IsPolyaFreqSeq, toeplitz_one_coeff, IsTotallyNonneg.one]

def bidiagonal (a : ℝ) : Matrix ℕ ℕ ℝ :=
  .of fun i j ↦ if i = j then a else if i = j + 1 then 1 else 0

@[simp]
lemma bidiagonal_apply (a : ℝ) (i j : ℕ) :
    bidiagonal a i j = if i = j then a else if i = j + 1 then 1 else 0 :=
  rfl

theorem bidiagonal_isTotallyNonneg (a : ℝ) (ha : 0 ≤ a) :
    IsTotallyNonneg (bidiagonal a) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      intro rows cols hrows hcols
      let S := (bidiagonal a).submatrix rows cols
      rcases lt_or_ge (cols 0) (rows 0) with hlt | hge
      · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with heq | hlt_succ
        · have h00 : S 0 0 = 1 := by simp [S, heq.symm]
          have hne1 (i : Fin n) : rows i.succ ≠ cols 0 := by
            have := hrows (Fin.succ_pos i)
            lia
          have hne2 (i : Fin n) : rows i.succ ≠ cols 0 + 1 := by
            have := hrows (Fin.succ_pos i)
            lia
          have hi0 (i : Fin n) : S i.succ 0 = 0 := by
            simp only [S, submatrix_apply, bidiagonal_apply, hne1 i, hne2 i, ↓reduceIte]
          rw [det_succ_column_zero S]
          have hsum : (∑ i : Fin (n.succ), (-1) ^ (i : ℕ) * S i 0 *
              det (S.submatrix i.succAbove Fin.succ)) =
              det (S.submatrix (0 : Fin (n + 1)).succAbove Fin.succ) := by
            rw [Fin.sum_univ_succ]
            simp [hi0, h00]
          rw [hsum, submatrix_submatrix]
          exact ih (hrows.comp (Fin.strictMono_succAbove 0)) (hcols.comp Fin.strictMono_succ)
        · have hne1 (i : Fin (n + 1)) : rows i ≠ cols 0 := by
            have := hrows.monotone (Fin.zero_le i)
            lia
          have hne2 (i : Fin (n + 1)) : rows i ≠ cols 0 + 1 := by
            have := hrows.monotone (Fin.zero_le i)
            lia
          have hi0 (i : Fin (n + 1)) : S i 0 = 0 := by
            simp only [S, submatrix_apply, bidiagonal_apply, hne1 i, hne2 i, ↓reduceIte]
          rw [det_succ_column_zero S]
          simp_all
      · rcases eq_or_lt_of_le hge with heq | hlt
        · have h00 : S 0 0 = a := by simp [S, heq]
          have hne1 (j : Fin n) : rows 0 ≠ cols j.succ := by
            have := hcols (Fin.succ_pos j)
            lia
          have hne2 (j : Fin n) : rows 0 ≠ cols j.succ + 1 := by
            have := hcols (Fin.succ_pos j)
            lia
          have h0j (j : Fin n) : S 0 j.succ = 0 := by
            simp only [S, submatrix_apply, bidiagonal_apply, hne1 j, hne2 j, ↓reduceIte]
          rw [det_succ_row_zero S]
          have hsum : (∑ j : Fin (n.succ), (-1) ^ (j : ℕ) * S 0 j *
              det (S.submatrix Fin.succ j.succAbove)) =
              a * det (S.submatrix Fin.succ (0 : Fin (n + 1)).succAbove) := by
            rw [Fin.sum_univ_succ]
            simp [h0j, h00]
          rw [hsum, submatrix_submatrix]
          have hdet_nonneg : 0 ≤ ((bidiagonal a).submatrix
              (rows ∘ Fin.succ) (cols ∘ (0 : Fin (n + 1)).succAbove)).det :=
            ih (hrows.comp Fin.strictMono_succ) (hcols.comp (Fin.strictMono_succAbove 0))
          exact mul_nonneg ha hdet_nonneg
        · have hne1 (j : Fin (n + 1)) : rows 0 ≠ cols j := by
            have := hcols.monotone (Fin.zero_le j)
            lia
          have hne2 (j : Fin (n + 1)) : rows 0 ≠ cols j + 1 := by
            have := hcols.monotone (Fin.zero_le j)
            lia
          have h0j (j : Fin (n + 1)) : S 0 j = 0 := by
            simp only [S, submatrix_apply, bidiagonal_apply, hne1 j, hne2 j, ↓reduceIte]
          rw [det_succ_row_zero S]
          simp_all

lemma toeplitz_const_coeff (c : ℝ) :
    toeplitz (fun n ↦ (C c : ℝ[X]).coeff n) = c • 1 := by
  ext i j
  simp only [toeplitz_apply, coeff_C, Matrix.smul_apply, Matrix.one_apply]
  rcases eq_or_ne i j with rfl | hne
  · simp
  · split_ifs with hle heq
    · exfalso; lia
    · simp
    · simp

lemma IsPolyaFreqSeq.const (c : ℝ) (hc : 0 ≤ c) :
    IsPolyaFreqSeq (fun n ↦ (C c : ℝ[X]).coeff n) := by
  simpa [IsPolyaFreqSeq, toeplitz_const_coeff] using
    IsTotallyNonneg.smul IsTotallyNonneg.one hc

lemma toeplitz_const_mul (c : ℝ) (q : ℝ[X]) :
    toeplitz (fun n ↦ (C c * q).coeff n) = c • toeplitz q.coeff := by
  ext i j
  simp

lemma IsPolyaFreqSeq.const_mul (c : ℝ) (hc : 0 ≤ c) {q : ℝ[X]}
    (hq : IsPolyaFreqSeq q.coeff) :
    IsPolyaFreqSeq (fun n ↦ (C c * q).coeff n) := by
  rw [IsPolyaFreqSeq, toeplitz_const_mul]
  exact IsTotallyNonneg.smul hq hc

lemma toeplitz_linear_coeff (r : ℝ) :
    toeplitz (fun n ↦ (X - C r : ℝ[X]).coeff n) = bidiagonal (-r) := by
  ext i j
  simp only [toeplitz_apply, coeff_sub, coeff_X, coeff_C, bidiagonal_apply]
  grind

lemma IsPolyaFreqSeq.linear {r : ℝ} (hr : r ≤ 0) :
    IsPolyaFreqSeq (fun n ↦ (X - C r : ℝ[X]).coeff n) := by
  rw [IsPolyaFreqSeq, toeplitz_linear_coeff]
  exact bidiagonal_isTotallyNonneg (-r) (neg_nonneg.mpr hr)

def mShift (M : Matrix ℕ ℕ ℝ) (i j : ℕ) : ℝ :=
  if i = 0 then 0 else M (i - 1) j

def hybrid {n : ℕ} (rows cols : Fin n → ℕ) (M : Matrix ℕ ℕ ℝ) (a : ℝ) (k : ℕ)
    (choices : Fin k → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  .of fun i j ↦
    if h : (i : ℕ) < k then
      if choices ⟨i, h⟩ then M (rows i) (cols j) else mShift M (rows i) (cols j)
    else
      a * M (rows i) (cols j) + mShift M (rows i) (cols j)

def extendChoices (k : ℕ) (choices : Fin k → Bool) (val : Bool) (i : Fin (k + 1)) : Bool :=
  if h : (i : ℕ) < k then choices ⟨i, h⟩ else val

lemma hybrid_nonneg_aux {n : ℕ} (rows cols : Fin n → ℕ) (hrows : StrictMono rows)
    (hcols : StrictMono cols) (M : Matrix ℕ ℕ ℝ) (hM : M.IsTotallyNonneg) (a : ℝ)
    (ha : 0 ≤ a) (d : ℕ) (k : ℕ) (hk : k ≤ n) (hd : n - k = d)
    (choices : Fin k → Bool) :
    0 ≤ (hybrid rows cols M a k choices).det := by
  induction d generalizing n k choices with
  | zero =>
      have hkn : k = n := by lia
      subst k
      by_cases h_zero : ∃ i : Fin n, choices i = false ∧ rows i = 0
      · rcases h_zero with ⟨i, hc, hr⟩
        have hrow (j : Fin n) : hybrid rows cols M a n choices i j = 0 := by
          simp only [hybrid, Matrix.of_apply, Fin.is_lt, ↓reduceDIte]
          have : choices ⟨(i : ℕ), Fin.is_lt i⟩ = choices i := rfl
          rw [this, hc]
          simp [hr, mShift]
        exact det_eq_zero_of_row_eq_zero i hrow |>.ge
      · have h_zero' (i : Fin n) (hc : choices i = false) : rows i ≠ 0 := fun hr ↦
          h_zero ⟨i, hc, hr⟩
        let rows' : Fin n → ℕ := fun i ↦ if choices i then rows i else rows i - 1
        have h_eq : hybrid rows cols M a n choices = M.submatrix rows' cols := by
          ext i j
          simp only [hybrid, Fin.is_lt, ↓reduceDIte, submatrix_apply, Matrix.of_apply,
            Fin.eta]
          dsimp [rows']
          split_ifs with hc
          · simp
          · have hc_false : choices i = false := Bool.eq_false_of_not_eq_true hc
            have hrne : rows i ≠ 0 := h_zero' i hc_false
            simp [mShift, hrne]
        rw [h_eq]
        have hmono : Monotone rows' := by
          intro i j hij
          by_cases heq : i = j
          · simp_all
          · have hlt : i < j := lt_of_le_of_ne hij heq
            have hrows_lt := hrows hlt
            grind
        by_cases h_inj : Function.Injective rows'
        · have h_strict : StrictMono rows' := by
            intro i j hij
            have hmono_ij := hmono hij.le
            rcases eq_or_lt_of_le hmono_ij with heq | hlt
            · exfalso
              exact hij.ne (h_inj heq)
            · grind
          exact hM h_strict hcols
        · unfold Function.Injective at h_inj
          push Not at h_inj
          rcases h_inj with ⟨i, j, heq, hne⟩
          have hrow_eq : (M.submatrix rows' cols) i = (M.submatrix rows' cols) j := by
            ext k_fin
            simp [heq]
          exact det_zero_of_row_eq hne hrow_eq |>.ge
  | succ d ih =>
      have hk_lt : k < n := by lia
      let choices1 := extendChoices k choices true
      let choices2 := extendChoices k choices false
      let B := hybrid rows cols M a (k + 1) choices1
      let C := hybrid rows cols M a (k + 1) choices2
      have hdk : n - (k + 1) = d := by lia
      have hB_nonneg : 0 ≤ B.det :=
        ih rows cols hrows hcols (k + 1) (by lia) hdk choices1
      have hC_nonneg : 0 ≤ C.det :=
        ih rows cols hrows hcols (k + 1) (by lia) hdk choices2
      have h_update : hybrid rows cols M a k choices =
          updateRow C ⟨k, hk_lt⟩ (a • B ⟨k, hk_lt⟩ + C ⟨k, hk_lt⟩) := by
        ext i j
        by_cases heq : i = ⟨k, hk_lt⟩
        · subst heq
          simp [hybrid, B, C, choices1, choices2, extendChoices, mShift, Matrix.of_apply]
        · have : (i : ℕ) ≠ k := fun h ↦ heq (Fin.ext h)
          simp only [hybrid, updateRow_ne heq, B, C, choices1, choices2, extendChoices,
            Matrix.of_apply]
          grind
      rw [h_update, det_updateRow_add, det_updateRow_smul]
      have hB_eq : updateRow C ⟨k, hk_lt⟩ (B ⟨k, hk_lt⟩) = B := by
        ext i j
        by_cases heq : i = ⟨k, hk_lt⟩
        · simp_all
        · rw [updateRow_ne heq]
          have : (i : ℕ) ≠ k := fun h ↦ heq (Fin.ext h)
          simp only [B, C, hybrid, choices1, choices2, extendChoices, Matrix.of_apply]
          grind
      have hC_eq : updateRow C ⟨k, hk_lt⟩ (C ⟨k, hk_lt⟩) = C :=
        updateRow_eq_self C ⟨k, hk_lt⟩
      simpa [hB_eq, hC_eq] using add_nonneg (mul_nonneg ha hB_nonneg) hC_nonneg

lemma toeplitz_linear_mul (r : ℝ) (q : ℝ[X]) :
    toeplitz (fun n ↦ ((X - C r) * q).coeff n) =
    .of fun i j ↦ (-r) * toeplitz q.coeff i j +
      mShift (toeplitz q.coeff) i j := by
  ext i j
  simp only [toeplitz_apply, coeff_X_sub_C_mul, mShift, Matrix.of_apply]
  grind

lemma IsPolyaFreqSeq.linear_mul {r : ℝ} (hr : r ≤ 0) {q : ℝ[X]}
    (hq : IsPolyaFreqSeq q.coeff) :
    IsPolyaFreqSeq (fun n ↦ ((X - C r) * q).coeff n) := by
  rw [IsPolyaFreqSeq, toeplitz_linear_mul]
  intro n rows cols hrows hcols
  have h_eq : (Matrix.of (fun i j ↦
      (-r) * toeplitz q.coeff i j +
      mShift (toeplitz q.coeff) i j)).submatrix rows cols =
      hybrid rows cols (toeplitz q.coeff) (-r) 0 Fin.elim0 := by
    ext i j
    simp [hybrid, mShift, Matrix.of_apply]
  rw [h_eq]
  exact hybrid_nonneg_aux rows cols hrows hcols (toeplitz q.coeff)
    hq (-r) (neg_nonneg.mpr hr) n 0 (Nat.zero_le n) (Nat.sub_zero n) Fin.elim0

lemma IsPolyaFreqSeq.prod_X_sub_C (s : Multiset ℝ) (hs : ∀ r ∈ s, r ≤ 0) :
    IsPolyaFreqSeq (fun n ↦ (s.map fun r ↦ X - C r).prod.coeff n) := by
  induction s using Multiset.induction_on with
  | empty =>
      simpa using IsPolyaFreqSeq.one
  | cons r s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      have hs' : ∀ x ∈ s, x ≤ 0 := fun x hx ↦ hs x (Multiset.mem_cons_of_mem hx)
      have hr : r ≤ 0 := hs r (Multiset.mem_cons_self r s)
      exact IsPolyaFreqSeq.linear_mul hr (ih hs')

/-- The reverse Aissen--Schoenberg--Whitney theorem. -/
theorem aissenSchoenbergWhitney_reverse {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p)
    (hsplits : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    IsPolyaFreqSeq p.coeff := by
  rcases eq_or_ne p 0 with rfl | hp0
  · convert isPolyaFreqSeq_zero
    exact coeff_zero _
  · have hp_eq : p = C p.leadingCoeff * (p.roots.map fun r ↦ X - C r).prod :=
      (C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_of_splits hsplits)).symm
    rw [hp_eq]
    have hlc_nonneg : 0 ≤ p.leadingCoeff := (hpnn.pos_leadingCoeff hp0).le
    exact IsPolyaFreqSeq.const_mul p.leadingCoeff hlc_nonneg
      (IsPolyaFreqSeq.prod_X_sub_C p.roots hroots)

/-- If every positive affine perturbation `p + C μ * q` splits and both
polynomials have nonnegative coefficients, then the coefficient sequence of
`p` is Pólya-frequency.  This packages the reverse ASW theorem together with
the Toeplitz-minor limit closure. -/
theorem IsPolyaFreqSeq.of_forall_pos_add_C_mul_splits {p q : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hfamily : ∀ {μ : ℝ}, 0 < μ → (p + C μ * q).Splits) :
    IsPolyaFreqSeq p.coeff :=
  IsPolyaFreqSeq.of_forall_pos_add_mul
    (a := p.coeff) (b := q.coeff) (by
      intro μ hμ
      have hnn : HasNonnegCoeffs (p + C μ * q) :=
        hpnn.add (nonnegCoeffs_C_mul hμ.le hqnn)
      convert aissenSchoenbergWhitney_reverse hnn (hfamily hμ)
        (roots_nonpos_of_nonneg_coeffs (hfamily hμ) hnn) using 1
      funext n
      simp [Polynomial.coeff_add, Polynomial.coeff_C_mul])

end RealRooted
