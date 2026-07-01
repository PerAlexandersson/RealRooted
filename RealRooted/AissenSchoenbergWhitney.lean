import RealRooted.Basic
import RealRooted.WagnerX
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

open Polynomial Matrix

noncomputable section

namespace RealRooted

/-!
# Aissen--Schoenberg--Whitney interfaces

This file records the Toeplitz total-nonnegativity formulation of
Pólya-frequency sequences and statement-level interfaces for the classical
Aissen--Schoenberg--Whitney theorem.

Reference: M. Aissen, I. J. Schoenberg, and A. M. Whitney, *On the generating
functions of totally positive sequences. I*, J. Analyse Math. 2 (1952),
93--103.
-/

variable {a : ℕ → ℝ}

/-- Entry of the Toeplitz matrix attached to a sequence `a₀, a₁, ...`. -/
def toeplitz (a : ℕ → ℝ) : Matrix ℕ ℕ ℝ :=
  .of fun i j ↦ if j ≤ i then a (i - j) else 0

@[simp]
lemma toeplitz_apply (a : ℕ → ℝ) (i j : ℕ) :
    toeplitz a i j = if j ≤ i then a (i - j) else 0 :=
  rfl

@[to_fun (attr := simp)]
lemma toeplitz_zero : toeplitz 0 = 0 := by
  ext
  simp [toeplitz]

/-- A sequence is a Polya-frequency sequence. -/
def IsPolyaFreqSeq (a : ℕ → ℝ) : Prop :=
  (toeplitz a).IsTotallyNonneg

/-- The zero sequence is Polya-frequency. -/
theorem IsPolyaFreqSeq_zero :
    IsPolyaFreqSeq (fun _ : ℕ => (0 : ℝ)) := by
  simp [IsPolyaFreqSeq]

/-- A Polya-frequency sequence has nonnegative entries, by its `1 × 1`
Toeplitz minors. -/
protected nonrec theorem IsPolyaFreqSeq.nonneg
    (ha : IsPolyaFreqSeq a) (k : ℕ) :
    0 ≤ a k := by
  simpa [IsPolyaFreqSeq] using ha.nonneg k 0

/-- Compatibility spelling for nonnegativity of PF sequences. -/
theorem nonneg_of_IsPolyaFreqSeq
    {a : ℕ → ℝ}
    (hpf : IsPolyaFreqSeq a)
    (k : ℕ) :
    0 ≤ a k :=
  IsPolyaFreqSeq.nonneg hpf k

/-- Toeplitz total nonnegativity of the coefficient sequence already implies
nonnegative coefficients. -/
theorem hasNonnegCoeffs_of_IsPolyaFreqSeq_coeff
    {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq (fun n => p.coeff n)) :
    HasNonnegCoeffs p :=
  fun k => nonneg_of_IsPolyaFreqSeq hpf k

/-- Planning stub for the forward Aissen--Schoenberg--Whitney theorem:
Toeplitz total nonnegativity of the coefficient sequence of a nonzero
polynomial should imply that the polynomial has only real nonpositive roots. -/
def aissenSchoenbergWhitneyForwardStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    IsPolyaFreqSeq (fun n => p.coeff n) →
    p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0

/-- Zero-aware forward ASW interface.  This is often the most convenient
closure form: a PF coefficient sequence gives either the zero polynomial or a
strictly real-rooted polynomial with nonpositive roots. -/
def aissenSchoenbergWhitneyForwardOrZeroStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    HasNonnegCoeffs p →
    IsPolyaFreqSeq (fun n => p.coeff n) →
    (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0

/-- Equivalent forward ASW statement with the redundant nonnegative-coefficient
hypothesis removed. -/
def aissenSchoenbergWhitneyForwardNoNonnegStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄,
    p ≠ 0 →
    IsPolyaFreqSeq (fun n => p.coeff n) →
    (p ≠ 0 ∧ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0

/-- The current forward ASW statement implies the no-extra-nonnegativity
formulation, since PF coefficients are already nonnegative. -/
theorem aissenSchoenbergWhitneyForwardNoNonneg_of_forward
    (hASW : aissenSchoenbergWhitneyForwardStatement) :
    aissenSchoenbergWhitneyForwardNoNonnegStatement :=
  fun {_} hp0 hpf => ⟨⟨hp0, (hASW hpf).1⟩, (hASW hpf).2⟩

/-- The no-extra-nonnegativity formulation implies the current forward ASW
statement. -/
theorem aissenSchoenbergWhitneyForward_of_noNonneg
    (hASW : aissenSchoenbergWhitneyForwardNoNonnegStatement) :
    aissenSchoenbergWhitneyForwardStatement := by
  intro p hpf
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact ⟨(hASW hp0 hpf).1.2, (hASW hp0 hpf).2⟩

/-- The two forward ASW interfaces are equivalent. -/
theorem aissenSchoenbergWhitneyForward_iff_noNonneg :
    aissenSchoenbergWhitneyForwardStatement ↔
      aissenSchoenbergWhitneyForwardNoNonnegStatement :=
  ⟨aissenSchoenbergWhitneyForwardNoNonneg_of_forward,
    aissenSchoenbergWhitneyForward_of_noNonneg⟩

/-- The strict nonzero forward ASW interface implies the zero-aware one. -/
theorem aissenSchoenbergWhitneyForwardOrZero_of_forward
    (hASW : aissenSchoenbergWhitneyForwardStatement) :
    aissenSchoenbergWhitneyForwardOrZeroStatement :=
  fun {_} _ hpf => ⟨Or.inr (hASW hpf).1, (hASW hpf).2⟩

/-- The zero-aware forward ASW interface implies the strict nonzero one by
discarding the zero case. -/
theorem aissenSchoenbergWhitneyForward_of_orZero
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement) :
    aissenSchoenbergWhitneyForwardStatement := by
  intro p hpf
  have hnn : HasNonnegCoeffs p :=
    hasNonnegCoeffs_of_IsPolyaFreqSeq_coeff hpf
  have h := hASW hnn hpf
  rcases h with ⟨hzero | hsplits, hroots⟩
  · simp [hzero]
  · exact ⟨hsplits, hroots⟩

/-- The strict and zero-aware forward ASW interfaces are equivalent. -/
theorem aissenSchoenbergWhitneyForward_iff_orZero :
    aissenSchoenbergWhitneyForwardStatement ↔
      aissenSchoenbergWhitneyForwardOrZeroStatement :=
  ⟨aissenSchoenbergWhitneyForwardOrZero_of_forward,
    aissenSchoenbergWhitneyForward_of_orZero⟩

/-- Without a nonzero hypothesis, the forward ASW interface would force the
zero polynomial to be real-rooted, contrary to the strict local definition of
`p ≠ 0 ∧ p.Splits`. -/
theorem not_aissenSchoenbergWhitneyForward_without_nonzero :
    ¬ (∀ ⦃p : ℝ[X]⦄,
      HasNonnegCoeffs p →
      IsPolyaFreqSeq (fun n => p.coeff n) →
      (p ≠ 0 ∧ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) := by
  intro h
  have hnn : HasNonnegCoeffs (0 : ℝ[X]) := by simp [HasNonnegCoeffs]
  have hbad := h hnn (by simpa using IsPolyaFreqSeq_zero)
  exact hbad.1.1 rfl

lemma toeplitz_one_coeff : toeplitz (fun n ↦ (1 : ℝ[X]).coeff n) = 1 := by
  ext i j
  simp only [toeplitz_apply, coeff_one, Matrix.one_apply]
  lia

lemma IsPolyaFreqSeq.one :
    IsPolyaFreqSeq (fun n ↦ (1 : ℝ[X]).coeff n) := by
  simpa [IsPolyaFreqSeq, toeplitz_one_coeff] using IsTotallyNonneg.one

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
        · have h00 : S 0 0 = 1 := by
            simp [S, heq.symm]
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
        · have h00 : S 0 0 = a := by
            simp [S, heq]
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
  split_ifs
  any_goals simp_all
  all_goals lia

lemma IsPolyaFreqSeq.const (c : ℝ) (hc : 0 ≤ c) :
    IsPolyaFreqSeq (fun n ↦ (C c : ℝ[X]).coeff n) := by
  simpa [IsPolyaFreqSeq, toeplitz_const_coeff] using
    IsTotallyNonneg.smul IsTotallyNonneg.one c hc

lemma toeplitz_const_mul (c : ℝ) (q : ℝ[X]) :
    toeplitz (fun n ↦ (C c * q).coeff n) = c • toeplitz (fun n ↦ q.coeff n) := by
  ext i j
  simp

lemma IsPolyaFreqSeq.const_mul (c : ℝ) (hc : 0 ≤ c) {q : ℝ[X]}
    (hq : IsPolyaFreqSeq (fun n ↦ q.coeff n)) :
    IsPolyaFreqSeq (fun n ↦ (C c * q).coeff n) := by
  rw [IsPolyaFreqSeq]
  convert IsTotallyNonneg.smul hq c hc using 1
  ext i j
  simp [toeplitz_apply]

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
      rw [h_update]
      rw [det_updateRow_add, det_updateRow_smul]
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
      rw [hB_eq, hC_eq]
      exact add_nonneg (mul_nonneg ha hB_nonneg) hC_nonneg

lemma toeplitz_linear_mul (r : ℝ) (q : ℝ[X]) :
    toeplitz (fun n ↦ ((X - C r) * q).coeff n) =
    .of fun i j ↦ (-r) * toeplitz (fun n ↦ q.coeff n) i j +
      mShift (toeplitz (fun n ↦ q.coeff n)) i j := by
  ext i j
  simp only [toeplitz_apply, coeff_X_sub_C_mul, mShift, Matrix.of_apply]
  grind

lemma IsPolyaFreqSeq.linear_mul {r : ℝ} (hr : r ≤ 0) {q : ℝ[X]}
    (hq : IsPolyaFreqSeq (fun n ↦ q.coeff n)) :
    IsPolyaFreqSeq (fun n ↦ ((X - C r) * q).coeff n) := by
  rw [IsPolyaFreqSeq, toeplitz_linear_mul]
  intro n rows cols hrows hcols
  have h_eq : (Matrix.of (fun i j ↦
      (-r) * toeplitz (fun n ↦ q.coeff n) i j +
      mShift (toeplitz (fun n ↦ q.coeff n)) i j)).submatrix rows cols =
      hybrid rows cols (toeplitz (fun n ↦ q.coeff n)) (-r) 0 Fin.elim0 := by
    ext i j
    simp [hybrid, mShift, Matrix.of_apply]
  rw [h_eq]
  exact hybrid_nonneg_aux rows cols hrows hcols (toeplitz (fun n ↦ q.coeff n))
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
    IsPolyaFreqSeq (fun n ↦ p.coeff n) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simpa using IsPolyaFreqSeq_zero
  · have hp_eq : p = C p.leadingCoeff * (p.roots.map fun r ↦ X - C r).prod :=
      (C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_of_splits hsplits)).symm
    rw [hp_eq]
    have hlc_nonneg : 0 ≤ p.leadingCoeff := (hpnn.pos_leadingCoeff hp0).le
    exact IsPolyaFreqSeq.const_mul p.leadingCoeff hlc_nonneg
      (IsPolyaFreqSeq.prod_X_sub_C p.roots hroots)

end RealRooted
