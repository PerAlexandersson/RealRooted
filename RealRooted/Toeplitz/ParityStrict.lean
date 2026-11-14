module

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
public import RealRooted.RootLocation.Basic
public import RealRooted.SimpleRoots
public import RealRooted.Toeplitz.ParityRows
public import RealRooted.Toeplitz.HessenbergRows
public import RealRooted.Toeplitz.AffineVector
import RealRooted.Toeplitz.TP2Hessenberg
import RealRooted.Toeplitz.AffineVector
import RealRooted.Toeplitz.ParityVector
import RealRooted.Basic.AffineInterlacing
import RealRooted.Interlacing.OuterDifference
import RealRooted.Linear
import RealRooted.Mathlib.Algebra.Polynomial.Expand.Splits

/-!
# Strict interlacing of the parity-lifted rows

Let `A` be a square matrix as in the TP2 Hessenberg certificate (nonnegative entries and ordered
`2 × 2` minors, decreasing columns, `A i j = A j j` for `i ≤ j`) such that `G(w) = det (I + w A)`
is nonconstant. For `γ ∈ ℝ` the rows `P_n^γ(t)` of `1 / (G(z²) + γ z - t z)` are monic of degree
`n` with simple real roots, and consecutive rows strictly interlace
(`parityRow_certificate`). The matrix may be singular and larger than `deg G`.

By the vector facts of `Toeplitz.ParityVector` the polynomials `U_m`, `V_m` of
`Toeplitz.ParityRows` satisfy `V_m ≪ U_m` and `U_m ≪ V_{m+1}` strictly. The sign criterion
`interlaces_and_isCoprime_iff_eval_mul_derivative_pos` and the parity decomposition
`P_{2m}^0 = V_m(t²)`, `P_{2m+1}^0 = t U_m(t²)` then give the strict interlacing of consecutive
rows; the shift `t ↦ t - γ` handles general `γ`. Columns of `A` with `c_j = 0` are deleted first
(`exists_parityRow_eq`), which does not change `G`.
-/

@[expose] public section

open Polynomial Matrix

noncomputable section

namespace RealRooted

variable {n : ℕ}

/-- The hypotheses of the parity lift on a matrix `A`: `TP2`, decreasing columns, constant
upper-triangular columns, and `A 0 0 > 0`. -/
structure IsParityKernel (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop where
  /-- Nonnegative entries and ordered `2 × 2` minors. -/
  isTP2 : A.IsTP2
  /-- Every column weakly decreases. -/
  col : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j
  /-- `A i j = A j j` for `i ≤ j`. -/
  row : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j
  /-- The first diagonal entry is positive. -/
  pos : 0 < A 0 0

section UV

variable {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

namespace IsParityKernel

variable (H : IsParityKernel A)

include H

lemma isTP2_parityBlock : (parityBlock A).IsTP2 := parityBlock_isTP2 H.isTP2 H.col

lemma parityBlock_apply_le_of_le :
    ∀ ⦃i k j : Fin (n + 1 + n + 1)⦄, i ≤ k → parityBlock A k j ≤ parityBlock A i j :=
  fun _ _ _ h => parityBlock_col_le H.isTP2.nonneg H.col _ h

lemma parityBlock_apply_eq_of_le :
    ∀ ⦃i j : Fin (n + 1 + n + 1)⦄, i ≤ j → parityBlock A i j = parityBlock A j j :=
  fun _ _ h => parityBlock_row_eq H.row h

/-- `U_m` is monic of degree `m`. -/
lemma monic_natDegree_u (m : ℕ) :
    (hessenbergRow (n := n + 1 + n) (parityBlock A) m).Monic ∧
      (hessenbergRow (n := n + 1 + n) (parityBlock A) m).natDegree = m :=
  monic_natDegree_hessenbergRow (n := n + 1 + n) (parityBlock A) H.parityBlock_apply_eq_of_le m

/-- `V_m` is monic of degree `m`. -/
lemma monic_natDegree_v (m : ℕ) :
    (PowerSeries.coeff m (parityV A)).Monic ∧ (PowerSeries.coeff m (parityV A)).natDegree = m := by
  rw [coeff_parityV_eq A H.row]
  exact monic_natDegree_signedComp (hessenbergVector_monic_natDegree (n := n + 1 + n)
    (parityBlock A) m _).1 (hessenbergVector_monic_natDegree (n := n + 1 + n) (parityBlock A) m _).2

/-- `U_m` has only nonnegative real roots. -/
lemma isRealRootedIn_u (m : ℕ) :
    IsRealRootedIn (Set.Ici 0) (hessenbergRow (n := n + 1 + n) (parityBlock A) m) :=
  isRealRootedIn_Ici_hessenbergRow (n := n + 1 + n) H.isTP2_parityBlock
    H.parityBlock_apply_le_of_le H.parityBlock_apply_eq_of_le m

/-- `V_m` has only nonnegative real roots. -/
lemma isRealRootedIn_v (m : ℕ) :
    IsRealRootedIn (Set.Ici 0) (PowerSeries.coeff m (parityV A)) := by
  rw [coeff_parityV_eq A H.row]
  exact isRealRootedIn_Ici_signedComp_hessenbergVector (n := n + 1 + n)
    H.isTP2_parityBlock H.parityBlock_apply_le_of_le m _

end IsParityKernel

private lemma eval_signedComp (f : ℝ[X]) (k : ℕ) (x : ℝ) :
    (C ((-1 : ℝ) ^ k) * f.comp (-X)).eval x = (-1) ^ k * f.eval (-x) := by
  simp

private lemma isRoot_signedComp' {f : ℝ[X]} {k : ℕ} {x : ℝ} :
    (C ((-1 : ℝ) ^ k) * f.comp (-X)).IsRoot x ↔ f.IsRoot (-x) := by
  have hne : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  simp [IsRoot, hne]

namespace IsParityKernel

variable (H : IsParityKernel A)

include H

/-- `U_m(0) V_m(0) > 0`. -/
lemma eval_zero_u_mul_v (m : ℕ) :
    0 < (hessenbergRow (n := n + 1 + n) (parityBlock A) m).eval 0 *
      (PowerSeries.coeff m (parityV A)).eval 0 := by
  rw [hessenbergRow_parityBlock_eq A H.row, coeff_parityV_eq A H.row, eval_signedComp,
    eval_signedComp, neg_zero]
  have h1 := eval_zero_parityVector_pos H.isTP2 H.pos m (j := 0) (Or.inl rfl)
  have h2 := eval_zero_parityVector_pos H.isTP2 H.pos m (j := parityIndex n) (Or.inr rfl)
  have hsq : ((-1 : ℝ) ^ m) * ((-1) ^ m) = 1 := by rw [← mul_pow]; norm_num
  have h3 := mul_pos h1 h2
  change 0 < (hessenbergVector (n := n + 1 + n) (parityBlock A) m 0).eval 0 *
    (hessenbergVector (n := n + 1 + n) (parityBlock A) m (parityIndex n)).eval 0 at h3
  generalize (hessenbergVector (n := n + 1 + n) (parityBlock A) m 0).eval 0 = a at h3 ⊢
  generalize (hessenbergVector (n := n + 1 + n) (parityBlock A) m (parityIndex n)).eval 0 = b
    at h3 ⊢
  have : (-1 : ℝ) ^ m * a * ((-1) ^ m * b) = ((-1) ^ m * (-1) ^ m) * (a * b) := by ring
  rw [this, hsq, one_mul]
  exact h3

lemma eval_zero_u_ne (m : ℕ) : (hessenbergRow (n := n + 1 + n) (parityBlock A) m).eval 0 ≠ 0 :=
  fun h => by simpa [h] using H.eval_zero_u_mul_v m

lemma eval_zero_v_ne (m : ℕ) : (PowerSeries.coeff m (parityV A)).eval 0 ≠ 0 :=
  fun h => by simpa [h] using H.eval_zero_u_mul_v m

/-- Roots of `U_m` are positive. -/
lemma pos_of_isRoot_u {m : ℕ} {u : ℝ}
    (hu : (hessenbergRow (n := n + 1 + n) (parityBlock A) m).IsRoot u) : 0 < u := by
  refine lt_of_le_of_ne ((H.isRealRootedIn_u m).mem_of_isRoot hu) fun h => ?_
  rw [← h] at hu
  exact H.eval_zero_u_ne m hu

/-- Roots of `V_m` are positive. -/
lemma pos_of_isRoot_v {m : ℕ} {u : ℝ} (hu : (PowerSeries.coeff m (parityV A)).IsRoot u) :
    0 < u := by
  refine lt_of_le_of_ne ((H.isRealRootedIn_v m).mem_of_isRoot hu) fun h => ?_
  rw [← h] at hu
  exact H.eval_zero_v_ne m hu

/-- `V_m ≪ U_m`. -/
lemma strictInterl_v_u (m : ℕ) :
    StrictInterl (PowerSeries.coeff m (parityV A))
      (hessenbergRow (n := n + 1 + n) (parityBlock A) m) := by
  have hne : ((-1 : ℝ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h := strictInterl_parityVector_zero_index H.isTP2 H.col m
  have hdeg : (parityVector A m 0).natDegree = (parityVector A m (parityIndex n)).natDegree := by
    rw [(hessenbergVector_monic_natDegree (n := n + 1 + n) (parityBlock A) m 0).2,
      (hessenbergVector_monic_natDegree (n := n + 1 + n) (parityBlock A) m _).2]
  rw [coeff_parityV_eq A H.row, hessenbergRow_parityBlock_eq A H.row]
  exact ((h.comp_neg_X_of_natDegree_eq hdeg).C_mul_left hne).C_mul_right hne

/-- `U_m ≪ V_{m+1}`. -/
lemma strictInterl_u_v (m : ℕ) :
    StrictInterl (hessenbergRow (n := n + 1 + n) (parityBlock A) m)
      (PowerSeries.coeff (m + 1) (parityV A)) := by
  have hinv := (affineVector_invariant (n := n + 1 + n) (M := fun _ => parityBlock A)
    (fun _ => H.isTP2_parityBlock) (fun _ => H.parityBlock_apply_le_of_le) m).2
  rw [← hessenbergVector_eq_affineVector (n := n + 1 + n) (parityBlock A)] at hinv
  have h : StrictInterl (parityVector A m 0) (parityVector A (m + 1) (parityIndex n)) :=
    List.rel_of_pairwise_cons (isInterlacingSeq_iff_pairwise.mp hinv.2)
      (List.mem_ofFn.mpr ⟨parityIndex n, rfl⟩)
  have hdeg : (parityVector A m 0).natDegree + 1 =
      (parityVector A (m + 1) (parityIndex n)).natDegree := by
    rw [(hessenbergVector_monic_natDegree (n := n + 1 + n) (parityBlock A) m 0).2,
      (hessenbergVector_monic_natDegree (n := n + 1 + n) (parityBlock A) (m + 1) _).2]
  rw [coeff_parityV_eq A H.row, hessenbergRow_parityBlock_eq A H.row]
  exact (interlaces_signedComp h hdeg).toStrictInterl

/-- `V_m` and `U_m` have no common root. -/
lemma no_common_root_v_u (m : ℕ) (u : ℝ) :
    ¬ ((PowerSeries.coeff m (parityV A)).IsRoot u ∧
      (hessenbergRow (n := n + 1 + n) (parityBlock A) m).IsRoot u) := by
  rw [coeff_parityV_eq A H.row, hessenbergRow_parityBlock_eq A H.row, isRoot_signedComp',
    isRoot_signedComp']
  exact fun h => not_isRoot_parityVector_zero_index H.isTP2 H.col H.pos m (-u) ⟨h.2, h.1⟩

/-- `U_m` and `V_{m+1}` have no common root. -/
lemma no_common_root_u_v (m : ℕ) (u : ℝ) :
    ¬ ((hessenbergRow (n := n + 1 + n) (parityBlock A) m).IsRoot u ∧
      (PowerSeries.coeff (m + 1) (parityV A)).IsRoot u) := by
  rw [coeff_parityV_eq A H.row, hessenbergRow_parityBlock_eq A H.row, isRoot_signedComp',
    isRoot_signedComp']
  exact fun h => not_isRoot_parityVector_zero_succ_index H.isTP2 H.col H.pos m (-u) h.1 h.2

/-- Sign at the roots of `U_m`: `V_m(u) U_m'(u) > 0`. -/
lemma eval_v_mul_derivative_u_pos (m : ℕ) {u : ℝ}
    (hu : (hessenbergRow (n := n + 1 + n) (parityBlock A) m).IsRoot u) :
    0 < (PowerSeries.coeff m (parityV A)).eval u *
      (hessenbergRow (n := n + 1 + n) (parityBlock A) m).derivative.eval u :=
  (H.strictInterl_v_u m).eval_mul_derivative_pos_of_right_root_of_no_common
    (hasPosLeadingCoeff_of_monic (H.monic_natDegree_v m).1)
    (hasPosLeadingCoeff_of_monic (H.monic_natDegree_u m).1)
    (fun x hx hx' => H.no_common_root_v_u m x ⟨hx, hx'⟩) hu

/-- Sign at the roots of `V_{m+1}`: `U_m(u) V_{m+1}'(u) > 0`. -/
lemma eval_u_mul_derivative_v_pos (m : ℕ) {u : ℝ}
    (hu : (PowerSeries.coeff (m + 1) (parityV A)).IsRoot u) :
    0 < (hessenbergRow (n := n + 1 + n) (parityBlock A) m).eval u *
      (PowerSeries.coeff (m + 1) (parityV A)).derivative.eval u :=
  (H.strictInterl_u_v m).eval_mul_derivative_pos_of_right_root_of_no_common
    (hasPosLeadingCoeff_of_monic (H.monic_natDegree_u m).1)
    (hasPosLeadingCoeff_of_monic (H.monic_natDegree_v (m + 1)).1)
    (fun x hx hx' => H.no_common_root_u_v m x ⟨hx, hx'⟩) hu

/-! #### The rows for `γ = 0` -/

omit H in
private lemma eval_derivative_expand_two (p : ℝ[X]) (r : ℝ) :
    (derivative (expand ℝ 2 p)).eval r = p.derivative.eval (r ^ 2) * (2 * r) := by
  simp [derivative_expand, expand_eval]

omit H in
private lemma splits_expand_two {p : ℝ[X]} (hp : IsRealRootedIn (Set.Ici 0) p) :
    (expand ℝ 2 p).Splits :=
  splits_expand_two_of_splits_of_forall_roots_nonneg p hp.splits fun _ hr => hp.mem_of_mem_roots hr

omit H in
private lemma monic_natDegree_expand_two {p : ℝ[X]} {m : ℕ} (hp : p.Monic) (hd : p.natDegree = m) :
    (expand ℝ 2 p).Monic ∧ (expand ℝ 2 p).natDegree = 2 * m := by
  refine ⟨hp.expand (by norm_num), ?_⟩
  rw [natDegree_expand, hd, mul_comm]

/-- The even rows are `V_m(t²)`: monic of degree `2 m`, real-rooted. -/
lemma parityRow_even (m : ℕ) :
    (parityRow A 0 (2 * m)).Monic ∧ (parityRow A 0 (2 * m)).natDegree = 2 * m ∧
      (parityRow A 0 (2 * m)).Splits := by
  rw [parityRow_zero_two_mul]
  obtain ⟨h1, h2⟩ := monic_natDegree_expand_two (H.monic_natDegree_v m).1 (H.monic_natDegree_v m).2
  exact ⟨h1, h2, splits_expand_two (H.isRealRootedIn_v m)⟩

/-- The odd rows are `t U_m(t²)`: monic of degree `2 m + 1`, real-rooted. -/
lemma parityRow_odd (m : ℕ) :
    (parityRow A 0 (2 * m + 1)).Monic ∧ (parityRow A 0 (2 * m + 1)).natDegree = 2 * m + 1 ∧
      (parityRow A 0 (2 * m + 1)).Splits := by
  rw [parityRow_zero_two_mul_add_one]
  obtain ⟨h1, h2⟩ := monic_natDegree_expand_two (H.monic_natDegree_u m).1 (H.monic_natDegree_u m).2
  refine ⟨monic_X.mul h1, ?_, Splits.X.mul (splits_expand_two (H.isRealRootedIn_u m))⟩
  rw [natDegree_mul' (by simp [h1.leadingCoeff]), natDegree_X, h2]
  lia

/-- Strict interlacing of `P_{2m}` and `P_{2m+1}` (`γ = 0`). -/
lemma interlaces_isCoprime_even (m : ℕ) :
    Interlaces (parityRow A 0 (2 * m)) (parityRow A 0 (2 * m + 1)) ∧
      IsCoprime (parityRow A 0 (2 * m)) (parityRow A 0 (2 * m + 1)) := by
  obtain ⟨hqm, hqd, -⟩ := H.parityRow_even m
  obtain ⟨hfm, hfd, hfs⟩ := H.parityRow_odd m
  refine (interlaces_and_isCoprime_iff_eval_mul_derivative_pos hfs (hasPosLeadingCoeff_of_monic hqm)
    (hasPosLeadingCoeff_of_monic hfm) (by lia)).mpr fun r hr => ?_
  rw [parityRow_zero_two_mul_add_one] at hr
  rw [parityRow_zero_two_mul, parityRow_zero_two_mul_add_one]
  simp only [IsRoot, eval_mul, eval_X, expand_eval, mul_eq_zero] at hr
  rw [derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_X,
    eval_derivative_expand_two, expand_eval, expand_eval]
  rcases hr with rfl | hU
  · have := H.eval_zero_u_mul_v m
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_zero]
    rw [mul_comm]
    exact this
  · have hu : (hessenbergRow (n := n + 1 + n) (parityBlock A) m).IsRoot (r ^ 2) := hU
    have hpos := H.pos_of_isRoot_u hu
    have h := H.eval_v_mul_derivative_u_pos m hu
    rw [hU]
    nlinarith [mul_pos hpos h]

/-- Strict interlacing of `P_{2m+1}` and `P_{2m+2}` (`γ = 0`). -/
lemma interlaces_isCoprime_odd (m : ℕ) :
    Interlaces (parityRow A 0 (2 * m + 1)) (parityRow A 0 (2 * m + 2)) ∧
      IsCoprime (parityRow A 0 (2 * m + 1)) (parityRow A 0 (2 * m + 2)) := by
  have h2 : 2 * m + 2 = 2 * (m + 1) := by lia
  obtain ⟨hqm, hqd, -⟩ := H.parityRow_odd m
  obtain ⟨hfm, hfd, hfs⟩ := H.parityRow_even (m + 1)
  rw [h2]
  refine (interlaces_and_isCoprime_iff_eval_mul_derivative_pos hfs (hasPosLeadingCoeff_of_monic hqm)
    (hasPosLeadingCoeff_of_monic hfm) (by lia)).mpr fun r hr => ?_
  rw [parityRow_zero_two_mul] at hr ⊢
  rw [parityRow_zero_two_mul_add_one]
  simp only [IsRoot, expand_eval] at hr
  have hu : (PowerSeries.coeff (m + 1) (parityV A)).IsRoot (r ^ 2) := hr
  have hpos := H.pos_of_isRoot_v hu
  have h := H.eval_u_mul_derivative_v_pos m hu
  rw [eval_mul, eval_X, expand_eval, eval_derivative_expand_two]
  have : r * (hessenbergRow (n := n + 1 + n) (parityBlock A) m).eval (r ^ 2) *
      ((PowerSeries.coeff (m + 1) (parityV A)).derivative.eval (r ^ 2) * (2 * r)) =
        2 * r ^ 2 * ((hessenbergRow (n := n + 1 + n) (parityBlock A) m).eval (r ^ 2) *
          (PowerSeries.coeff (m + 1) (parityV A)).derivative.eval (r ^ 2)) := by ring
  rw [this]
  exact mul_pos (by positivity) h

/-- **Strict interlacing of consecutive rows** (`γ = 0`). -/
lemma interlaces_isCoprime (k : ℕ) :
    Interlaces (parityRow A 0 k) (parityRow A 0 (k + 1)) ∧
      IsCoprime (parityRow A 0 k) (parityRow A 0 (k + 1)) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · exact H.interlaces_isCoprime_even m
  · exact H.interlaces_isCoprime_odd m

/-- Monic, degree `k`, real-rooted (`γ = 0`). -/
lemma parityRow_monic_natDegree_splits (k : ℕ) :
    (parityRow A 0 k).Monic ∧ (parityRow A 0 k).natDegree = k ∧ (parityRow A 0 k).Splits := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · simpa using H.parityRow_even m
  · exact H.parityRow_odd m

/-- **The parity-lifted rows for `γ = 0` under `A 0 0 > 0`.** -/
theorem parityRow_certificate_zero (k : ℕ) :
    (parityRow A 0 k).Monic ∧ (parityRow A 0 k).natDegree = k ∧ (parityRow A 0 k).Splits ∧
      HasSimpleRoots (parityRow A 0 k) ∧
      Interlaces (parityRow A 0 k) (parityRow A 0 (k + 1)) ∧
      IsCoprime (parityRow A 0 k) (parityRow A 0 (k + 1)) := by
  obtain ⟨h1, h2, h3⟩ := H.parityRow_monic_natDegree_splits k
  obtain ⟨h4, h5⟩ := H.interlaces_isCoprime k
  exact ⟨h1, h2, h3, (h4.toStrictInterl.hasSimpleRoots_of_isCoprime h5).1, h4, h5⟩

/-- **The parity-lifted rows for every `γ` under `A 0 0 > 0`.** -/
theorem parityRow_certificate (γ : ℝ) (k : ℕ) :
    (parityRow A γ k).Monic ∧ (parityRow A γ k).natDegree = k ∧ (parityRow A γ k).Splits ∧
      HasSimpleRoots (parityRow A γ k) ∧
      Interlaces (parityRow A γ k) (parityRow A γ (k + 1)) ∧
      IsCoprime (parityRow A γ k) (parityRow A γ (k + 1)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H.parityRow_certificate_zero k
  have hsub : (X - C γ : ℝ[X]) = C 1 * X + C (-γ) := by simp [sub_eq_add_neg]
  have hdeg : (X - C γ : ℝ[X]).natDegree = 1 := natDegree_X_sub_C γ
  rw [parityRow_eq_comp A γ k, parityRow_eq_comp A γ (k + 1)]
  refine ⟨h1.comp (monic_X_sub_C γ) (by lia), ?_, h3.comp_X_sub_C γ, ?_, ?_, ?_⟩
  · rw [natDegree_comp, h2, hdeg, mul_one]
  · rw [hsub]
    exact h4.comp_C_mul_X_add_C (a := 1) (b := -γ) one_ne_zero
  · have := interlaces_comp_X_add_C h5 (-γ)
    simpa [sub_eq_add_neg] using this
  · simpa using h6.map (Polynomial.compRingHom (X - C γ))

end IsParityKernel

end UV

/-! ### Deleting a zero column -/

/-- Deleting the first row and column of a matrix whose first column vanishes does not change
`det (I + X A)`. -/
theorem hessenbergDet_submatrix_succ (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    (h : ∀ i, A i 0 = 0) :
    hessenbergDet A = hessenbergDet (A.submatrix Fin.succ Fin.succ) := by
  set M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ[X] := 1 + (X : ℝ[X]) • A.map C with hM
  have hcol0 : ∀ i, M i 0 = if i = 0 then 1 else 0 := fun i => by
    simp [hM, Matrix.one_apply, h i]
  rw [hessenbergDet, ← hM, Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
  · rw [hcol0]
    simp only [ite_true, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, hessenbergDet]
    congr 1
    ext i j
    simp [hM, Matrix.one_apply]
  · intro i _ hi
    simp [hcol0, hi]
  · simp

/-- **Strict parity lift of a finite `TP2` kernel.** Let `A` be a square matrix with nonnegative
entries and nonnegative ordered `2 × 2` minors, weakly decreasing columns and `A i j = A j j` for
`i ≤ j`, such that `G(w) = det (I + w A)` is nonconstant. Then for every `γ ∈ ℝ` the coefficients
`P_k(t)` of `zᵏ` in `1 / (G(z²) + γ z - t z)` are monic of degree `k`, real-rooted with simple
roots, and consecutive rows strictly interlace (`Interlaces` and `IsCoprime`). The matrix may
be singular and larger than `deg G`. -/
theorem parityRow_certificate_of_natDegree_ne_zero :
    ∀ {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}, A.IsTP2 →
      (∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j) →
      (∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) →
      (hessenbergDet A).natDegree ≠ 0 → ∀ (γ : ℝ) (k : ℕ),
      (parityRow A γ k).Monic ∧ (parityRow A γ k).natDegree = k ∧ (parityRow A γ k).Splits ∧
        HasSimpleRoots (parityRow A γ k) ∧
        Interlaces (parityRow A γ k) (parityRow A γ (k + 1)) ∧
        IsCoprime (parityRow A γ k) (parityRow A γ (k + 1))
  | n, A, hA, hcol, hrow, hG, γ, k => by
    rcases (hA.nonneg 0 0).lt_or_eq with hpos | hzero
    · exact (IsParityKernel.mk hA hcol hrow hpos).parityRow_certificate γ k
    · -- the first column vanishes: delete it with the first row
      have hcol0 : ∀ i, A i 0 = 0 := fun i =>
        le_antisymm (hzero ▸ hcol (Fin.zero_le i)) (hA.nonneg i 0)
      cases n with
      | zero =>
        exfalso
        apply hG
        have : hessenbergDet A = 1 := by
          refine (Matrix.det_fin_one (1 + (X : ℝ[X]) • A.map C)).trans ?_
          simp [← hzero]
        rw [this, natDegree_one]
      | succ n =>
        have hdet := hessenbergDet_submatrix_succ A hcol0
        have hA' : (A.submatrix Fin.succ Fin.succ).IsTP2 :=
          ⟨fun i j => hA.nonneg _ _, fun i₁ i₂ j₁ j₂ hi hj =>
            hA.minor_nonneg (Fin.succ_lt_succ_iff.mpr hi) (Fin.succ_lt_succ_iff.mpr hj)⟩
        have := parityRow_certificate_of_natDegree_ne_zero (A := A.submatrix Fin.succ Fin.succ) hA'
          (fun i k j h => hcol (Fin.succ_le_succ_iff.mpr h))
          (fun i j h => hrow (Fin.succ_le_succ_iff.mpr h)) (hdet ▸ hG) γ k
        simpa only [parityRow, parityRowSeries, parityDenominator, hdet] using this

/-- A matrix with nonzero trace has a nonconstant determinant polynomial `det (I + X A)`. -/
theorem natDegree_hessenbergDet_ne_zero_of_trace_ne_zero
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (h : A.trace ≠ 0) :
    (hessenbergDet A).natDegree ≠ 0 := fun h0 => by
  have hc := Matrix.coeff_det_one_add_X_smul_one A
  rw [coeff_eq_zero_of_natDegree_lt (by rw [hessenbergDet] at h0; lia)] at hc
  exact h hc.symm

/-- **Strict parity lift, trace form.** The hypothesis that `det (I + w A)` is nonconstant holds
whenever `tr A ≠ 0`, for instance when `A` has a positive diagonal entry. -/
theorem parityRow_certificate_of_trace_ne_zero {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTP2) (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (htr : A.trace ≠ 0) (γ : ℝ) (k : ℕ) :
    (parityRow A γ k).Monic ∧ (parityRow A γ k).natDegree = k ∧ (parityRow A γ k).Splits ∧
      HasSimpleRoots (parityRow A γ k) ∧
      Interlaces (parityRow A γ k) (parityRow A γ (k + 1)) ∧
      IsCoprime (parityRow A γ k) (parityRow A γ (k + 1)) :=
  parityRow_certificate_of_natDegree_ne_zero hA hcol hrow
    (natDegree_hessenbergDet_ne_zero_of_trace_ne_zero A htr) γ k

end RealRooted
