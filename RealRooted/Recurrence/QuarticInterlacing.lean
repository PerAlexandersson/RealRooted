module

public import RealRooted.PFPolynomial
import RealRooted.PosCombo

/-!
# A quartic recurrence from seven interlacing comparisons

This module packages a five-polynomial state whose transition is closed by
Wagner's cone lemmas.  The resulting row sequence consists of nonzero PF
polynomials, has adjacent weak interlacing, and satisfies a fourth-order
recurrence.  The theorem is independent of any particular combinatorial
sequence.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The five polynomial coordinates used by the quartic interlacing transition. -/
structure QuarticInterlacingState where
  /-- The oldest row coordinate. -/
  f0 : ℝ[X]
  /-- The middle row coordinate. -/
  f1 : ℝ[X]
  /-- The newest row coordinate. -/
  f2 : ℝ[X]
  /-- The first auxiliary coordinate. -/
  d : ℝ[X]
  /-- The cumulative auxiliary coordinate. -/
  s : ℝ[X]

/-- One transition of the five-coordinate quartic state. -/
def quarticInterlacingStep (u v w : ℝ)
    (S : QuarticInterlacingState) : QuarticInterlacingState where
  f0 := S.f1
  f1 := S.f2
  f2 := S.f2 + C u * S.s + C (u + v - w) * (X * S.f1) + C w * (X * S.f0)
  d := S.d + (S.s + X * S.f1)
  s := S.s + X * S.f1

/-- The invariant closed by `quarticInterlacingStep`.

Besides a nonzero PF certificate for every coordinate, it records exactly the
seven directed comparisons needed by the transition and the balance identity
that makes the first auxiliary update a positive cone sum.
-/
structure QuarticInterlacingState.IsAdmissible (u v w : ℝ)
    (S : QuarticInterlacingState) : Prop where
  /-- The oldest row is PF. -/
  f0_pf : IsPFPolynomial S.f0
  /-- The oldest row is nonzero. -/
  f0_ne : S.f0 ≠ 0
  /-- The middle row is PF. -/
  f1_pf : IsPFPolynomial S.f1
  /-- The middle row is nonzero. -/
  f1_ne : S.f1 ≠ 0
  /-- The newest row is PF. -/
  f2_pf : IsPFPolynomial S.f2
  /-- The newest row is nonzero. -/
  f2_ne : S.f2 ≠ 0
  /-- The first auxiliary coordinate is PF. -/
  d_pf : IsPFPolynomial S.d
  /-- The first auxiliary coordinate is nonzero. -/
  d_ne : S.d ≠ 0
  /-- The cumulative auxiliary coordinate is PF. -/
  s_pf : IsPFPolynomial S.s
  /-- The cumulative auxiliary coordinate is nonzero. -/
  s_ne : S.s ≠ 0
  /-- The oldest row precedes the middle row. -/
  f0_interl_f1 : Interl S.f0 S.f1
  /-- The oldest row precedes the newest row. -/
  f0_interl_f2 : Interl S.f0 S.f2
  /-- The middle row precedes the newest row. -/
  f1_interl_f2 : Interl S.f1 S.f2
  /-- The middle row precedes the first auxiliary coordinate. -/
  f1_interl_d : Interl S.f1 S.d
  /-- The middle row precedes the cumulative auxiliary coordinate. -/
  f1_interl_s : Interl S.f1 S.s
  /-- The newest row precedes the cumulative auxiliary coordinate. -/
  f2_interl_s : Interl S.f2 S.s
  /-- The first auxiliary coordinate precedes the cumulative one. -/
  d_interl_s : Interl S.d S.s
  /-- The newest row is the balanced combination of the auxiliary coordinates. -/
  balance : S.f2 = C u * S.d + C v * S.s - C w * (X * S.f0)

private lemma interl_weightedSum_left (l : List (ℝ × ℝ[X])) (h : ℝ[X])
    (hweights : ∀ ap ∈ l, 0 ≤ ap.1)
    (hinterl : ∀ ap ∈ l, Interl h ap.2)
    (hnn : ∀ ap ∈ l, HasNonnegCoeffs ap.2) :
    Interl h (weightedSum l) := by
  rw [weightedSum_eq_sum_map]
  apply Interl.sum_left_of_common_left_of_nonneg
  · intro p hp
    obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hp
    exact (hinterl ap hap).C_mul_right_of_nonneg (hweights ap hap)
  · intro p hp
    obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hp
    exact hasNonnegCoeffs_C_mul (hweights ap hap) (hnn ap hap)

private lemma weightedSum_interl_right (l : List (ℝ × ℝ[X])) (h : ℝ[X])
    (hweights : ∀ ap ∈ l, 0 ≤ ap.1)
    (hinterl : ∀ ap ∈ l, Interl ap.2 h)
    (hnn : ∀ ap ∈ l, HasNonnegCoeffs ap.2) :
    Interl (weightedSum l) h := by
  induction l with
  | nil => simpa using interl_zero_left h
  | cons ap l ih =>
      rcases ap with ⟨a, p⟩
      rw [weightedSum_cons]
      apply interl_add_left_of_common_right_of_nonneg
      · exact (hinterl (a, p) (by simp)).C_mul_left_of_nonneg
          (hweights (a, p) (by simp))
      · apply ih
        · intro b hb
          exact hweights b (by simp [hb])
        · intro b hb
          exact hinterl b (by simp [hb])
        · intro b hb
          exact hnn b (by simp [hb])
      · exact hasNonnegCoeffs_C_mul
          (hweights (a, p) (by simp)) (hnn (a, p) (by simp))
      · exact hasNonnegCoeffs_weightedSum l
          (fun b hb => hweights b (by simp [hb]))
          (fun b hb => hnn b (by simp [hb]))

private lemma isPFPolynomial_of_interl_right {p q : ℝ[X]}
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0) (hqnn : HasNonnegCoeffs q)
    (hpq : Interl p q) : IsPFPolynomial q :=
  IsPFPolynomial.of_realRooted_nonneg hqnn
    (hpq.toStrictInterl_of_ne hp_ne hq_ne).2.1.2

/-- The quartic transition preserves admissibility throughout the parameter
region `0 ≤ w ≤ v ≤ u` with `u > 0`. -/
theorem QuarticInterlacingState.IsAdmissible.step
    {u v w : ℝ} {S : QuarticInterlacingState}
    (hS : S.IsAdmissible u v w) (hu : 0 < u)
    (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) :
    (quarticInterlacingStep u v w S).IsAdmissible u v w := by
  let sPlus : ℝ[X] := S.s + X * S.f1
  let dPlus : ℝ[X] := S.d + sPlus
  let f3 : ℝ[X] :=
    S.f2 + C u * S.s + C (u + v - w) * (X * S.f1) + C w * (X * S.f0)
  have hu0 : 0 ≤ u := hu.le
  have huvw : 0 ≤ u + v - w := by linarith
  have hvw : 0 ≤ v - w := sub_nonneg.mpr hwv
  have hdiv : 0 ≤ 1 - v / u := sub_nonneg.mpr ((div_le_one hu).2 hvu)
  have hwu : 0 ≤ w / u := div_nonneg hw hu.le
  have hiu : 0 ≤ 1 / u := (one_div_pos.mpr hu).le
  have hf1_Xf0 : Interl S.f1 (X * S.f0) :=
    interl_mul_X_of_interl hS.f0_interl_f1
      hS.f0_pf.hasNonnegCoeffs hS.f1_pf.hasNonnegCoeffs
  have hf2_Xf0 : Interl S.f2 (X * S.f0) :=
    interl_mul_X_of_interl hS.f0_interl_f2
      hS.f0_pf.hasNonnegCoeffs hS.f2_pf.hasNonnegCoeffs
  have hf2_Xf1 : Interl S.f2 (X * S.f1) :=
    interl_mul_X_of_interl hS.f1_interl_f2
      hS.f1_pf.hasNonnegCoeffs hS.f2_pf.hasNonnegCoeffs
  have hd_Xf1 : Interl S.d (X * S.f1) :=
    interl_mul_X_of_interl hS.f1_interl_d
      hS.f1_pf.hasNonnegCoeffs hS.d_pf.hasNonnegCoeffs
  have hs_Xf1 : Interl S.s (X * S.f1) :=
    interl_mul_X_of_interl hS.f1_interl_s
      hS.f1_pf.hasNonnegCoeffs hS.s_pf.hasNonnegCoeffs
  have hf1_Xf1 : Interl S.f1 (X * S.f1) :=
    interl_mul_X_of_interl hS.f1_pf.interl_self
      hS.f1_pf.hasNonnegCoeffs hS.f1_pf.hasNonnegCoeffs
  have hf1_f3 : Interl S.f1 f3 := by
    have h := interl_weightedSum_left
      [(1, S.f2), (u, S.s), (u + v - w, X * S.f1), (w, X * S.f0)] S.f1
      (by simp [hu0, huvw, hw])
      (by simp [hS.f1_interl_f2, hS.f1_interl_s, hf1_Xf1, hf1_Xf0])
      (by simp [hS.f2_pf.hasNonnegCoeffs, hS.s_pf.hasNonnegCoeffs,
        hS.f1_pf.hasNonnegCoeffs.X_mul, hS.f0_pf.hasNonnegCoeffs.X_mul])
    simpa [f3, weightedSum, add_assoc] using h
  have hf2_f3 : Interl S.f2 f3 := by
    have h := interl_weightedSum_left
      [(1, S.f2), (u, S.s), (u + v - w, X * S.f1), (w, X * S.f0)] S.f2
      (by simp [hu0, huvw, hw])
      (by simp [hS.f2_pf.interl_self, hS.f2_interl_s, hf2_Xf1, hf2_Xf0])
      (by simp [hS.f2_pf.hasNonnegCoeffs, hS.s_pf.hasNonnegCoeffs,
        hS.f1_pf.hasNonnegCoeffs.X_mul, hS.f0_pf.hasNonnegCoeffs.X_mul])
    simpa [f3, weightedSum, add_assoc] using h
  have hf2_sPlus : Interl S.f2 sPlus := by
    have h := interl_weightedSum_left [(1, S.s), (1, X * S.f1)] S.f2
      (by simp) (by simp [hS.f2_interl_s, hf2_Xf1])
      (by simp [hS.s_pf.hasNonnegCoeffs, hS.f1_pf.hasNonnegCoeffs.X_mul])
    simpa [sPlus, weightedSum] using h
  have hd_sPlus : Interl S.d sPlus := by
    have h := interl_weightedSum_left [(1, S.s), (1, X * S.f1)] S.d
      (by simp) (by simp [hS.d_interl_s, hd_Xf1])
      (by simp [hS.s_pf.hasNonnegCoeffs, hS.f1_pf.hasNonnegCoeffs.X_mul])
    simpa [sPlus, weightedSum] using h
  have hs_sPlus : Interl S.s sPlus := by
    have h := interl_weightedSum_left [(1, S.s), (1, X * S.f1)] S.s
      (by simp) (by simp [hS.s_pf.interl_self, hs_Xf1])
      (by simp [hS.s_pf.hasNonnegCoeffs, hS.f1_pf.hasNonnegCoeffs.X_mul])
    simpa [sPlus, weightedSum] using h
  have hsPlus_nn : HasNonnegCoeffs sPlus := by
    exact hS.s_pf.hasNonnegCoeffs.add hS.f1_pf.hasNonnegCoeffs.X_mul
  have hsPlus_ne : sPlus ≠ 0 := by
    exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      hS.s_pf.hasNonnegCoeffs hS.f1_pf.hasNonnegCoeffs.X_mul
      (mul_ne_zero X_ne_zero hS.f1_ne)
  have hsPlus_pf : IsPFPolynomial sPlus :=
    isPFPolynomial_of_interl_right hS.s_ne hsPlus_ne hsPlus_nn hs_sPlus
  have hdPlus_eq : dPlus = weightedSum
      [(1 / u, S.f2), (w / u, X * S.f0), (1, X * S.f1), (1 - v / u, S.s)] := by
    dsimp [dPlus, sPlus]
    simp only [add_zero, one_div]
    ext n
    have hb := congrArg (fun p : ℝ[X] => p.coeff n) hS.balance
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_C_mul] at hb
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul]
    rw [hb]
    field_simp [hu.ne']
    ring
  have hf2_dPlus : Interl S.f2 dPlus := by
    rw [hdPlus_eq]
    exact interl_weightedSum_left
      [(1 / u, S.f2), (w / u, X * S.f0), (1, X * S.f1), (1 - v / u, S.s)] S.f2
      (by simp [hu0, hwu, hdiv])
      (by simp [hS.f2_pf.interl_self, hf2_Xf0, hf2_Xf1, hS.f2_interl_s])
      (by simp [hS.f2_pf.hasNonnegCoeffs, hS.f0_pf.hasNonnegCoeffs.X_mul,
        hS.f1_pf.hasNonnegCoeffs.X_mul, hS.s_pf.hasNonnegCoeffs])
  have hdPlus_nn : HasNonnegCoeffs dPlus :=
    hS.d_pf.hasNonnegCoeffs.add hsPlus_nn
  have hdPlus_ne : dPlus ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      hS.d_pf.hasNonnegCoeffs hsPlus_nn hsPlus_ne
  have hdPlus_pf : IsPFPolynomial dPlus :=
    isPFPolynomial_of_interl_right hS.f2_ne hdPlus_ne hdPlus_nn hf2_dPlus
  have hdPlus_sPlus : Interl dPlus sPlus := by
    have h := weightedSum_interl_right [(1, S.d), (1, sPlus)] sPlus
      (by simp) (by simp [hd_sPlus, hsPlus_pf.interl_self])
      (by simp [hS.d_pf.hasNonnegCoeffs, hsPlus_nn])
    simpa [dPlus, weightedSum] using h
  have hf3_eq : f3 = weightedSum [(u, dPlus), (w, S.s), (v - w, sPlus)] := by
    dsimp [f3, dPlus, sPlus]
    simp only [add_zero]
    rw [hS.balance]
    simp only [map_add, map_sub]
    ring
  have hf3_sPlus : Interl f3 sPlus := by
    rw [hf3_eq]
    exact weightedSum_interl_right [(u, dPlus), (w, S.s), (v - w, sPlus)] sPlus
      (by simp [hu0, hw, hvw])
      (by simp [hdPlus_sPlus, hs_sPlus, hsPlus_pf.interl_self])
      (by simp [hdPlus_nn, hS.s_pf.hasNonnegCoeffs, hsPlus_nn])
  have hf3_nn : HasNonnegCoeffs f3 := by
    dsimp [f3]
    exact ((hS.f2_pf.hasNonnegCoeffs.add
      (hasNonnegCoeffs_C_mul hu0 hS.s_pf.hasNonnegCoeffs)).add
      (hasNonnegCoeffs_C_mul huvw hS.f1_pf.hasNonnegCoeffs.X_mul)).add
      (hasNonnegCoeffs_C_mul hw hS.f0_pf.hasNonnegCoeffs.X_mul)
  have hf3_ne : f3 ≠ 0 := by
    have hrest : HasNonnegCoeffs
        (C u * S.s + C (u + v - w) * (X * S.f1) + C w * (X * S.f0)) :=
      ((hasNonnegCoeffs_C_mul hu0 hS.s_pf.hasNonnegCoeffs).add
        (hasNonnegCoeffs_C_mul huvw hS.f1_pf.hasNonnegCoeffs.X_mul)).add
        (hasNonnegCoeffs_C_mul hw hS.f0_pf.hasNonnegCoeffs.X_mul)
    have h := add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      hrest hS.f2_pf.hasNonnegCoeffs hS.f2_ne
    simpa [f3, add_comm, add_left_comm, add_assoc] using h
  have hf3_pf : IsPFPolynomial f3 :=
    isPFPolynomial_of_interl_right hS.f2_ne hf3_ne hf3_nn hf2_f3
  have hbalance : f3 = C u * dPlus + C v * sPlus - C w * (X * S.f1) := by
    dsimp [f3, dPlus, sPlus]
    rw [hS.balance]
    simp only [map_add, map_sub]
    ring
  refine {
    f0_pf := hS.f1_pf
    f0_ne := hS.f1_ne
    f1_pf := hS.f2_pf
    f1_ne := hS.f2_ne
    f2_pf := ?_
    f2_ne := ?_
    d_pf := ?_
    d_ne := ?_
    s_pf := ?_
    s_ne := ?_
    f0_interl_f1 := hS.f1_interl_f2
    f0_interl_f2 := ?_
    f1_interl_f2 := ?_
    f1_interl_d := ?_
    f1_interl_s := ?_
    f2_interl_s := ?_
    d_interl_s := ?_
    balance := ?_ }
  · simpa [quarticInterlacingStep, f3] using hf3_pf
  · simpa [quarticInterlacingStep, f3] using hf3_ne
  · simpa [quarticInterlacingStep, dPlus, sPlus] using hdPlus_pf
  · simpa [quarticInterlacingStep, dPlus, sPlus] using hdPlus_ne
  · simpa [quarticInterlacingStep, sPlus] using hsPlus_pf
  · simpa [quarticInterlacingStep, sPlus] using hsPlus_ne
  · simpa [quarticInterlacingStep, f3] using hf1_f3
  · simpa [quarticInterlacingStep, f3] using hf2_f3
  · simpa [quarticInterlacingStep, dPlus, sPlus] using hf2_dPlus
  · simpa [quarticInterlacingStep, sPlus] using hf2_sPlus
  · simpa [quarticInterlacingStep, f3, sPlus] using hf3_sPlus
  · simpa [quarticInterlacingStep, dPlus, sPlus] using hdPlus_sPlus
  · simpa [quarticInterlacingStep, f3, dPlus, sPlus] using hbalance

/-- The state obtained after `n` quartic transitions. -/
def quarticInterlacingIterate (u v w : ℝ) (S : QuarticInterlacingState) :
    ℕ → QuarticInterlacingState
  | 0 => S
  | n + 1 => quarticInterlacingStep u v w (quarticInterlacingIterate u v w S n)

/-- Every iterate of an admissible state is admissible. -/
theorem QuarticInterlacingState.IsAdmissible.iterate
    {u v w : ℝ} {S : QuarticInterlacingState}
    (hS : S.IsAdmissible u v w) (hu : 0 < u)
    (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) (n : ℕ) :
    (quarticInterlacingIterate u v w S n).IsAdmissible u v w := by
  induction n with
  | zero => exact hS
  | succ n ih =>
      exact ih.step hu hw hwv hvu

/-- The row projection of a quartic state. -/
def QuarticInterlacingState.row (S : QuarticInterlacingState) : ℝ[X] :=
  S.f0

/-- The row sequence projected from the iterated quartic state. -/
def quarticInterlacingRow (u v w : ℝ) (S : QuarticInterlacingState)
    (n : ℕ) : ℝ[X] :=
  (quarticInterlacingIterate u v w S n).row

/-- Every row projected from an admissible quartic state is PF. -/
theorem quarticInterlacingRow_isPFPolynomial
    {u v w : ℝ} {S : QuarticInterlacingState}
    (hS : S.IsAdmissible u v w) (hu : 0 < u)
    (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) (n : ℕ) :
    IsPFPolynomial (quarticInterlacingRow u v w S n) := by
  exact (hS.iterate hu hw hwv hvu n).f0_pf

/-- Every row projected from an admissible quartic state is nonzero. -/
theorem quarticInterlacingRow_ne_zero
    {u v w : ℝ} {S : QuarticInterlacingState}
    (hS : S.IsAdmissible u v w) (hu : 0 < u)
    (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) (n : ℕ) :
    quarticInterlacingRow u v w S n ≠ 0 := by
  exact (hS.iterate hu hw hwv hvu n).f0_ne

/-- Consecutive rows projected from an admissible quartic state weakly interlace. -/
theorem interl_quarticInterlacingRow_succ
    {u v w : ℝ} {S : QuarticInterlacingState}
    (hS : S.IsAdmissible u v w) (hu : 0 < u)
    (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) (n : ℕ) :
    Interl (quarticInterlacingRow u v w S n)
      (quarticInterlacingRow u v w S (n + 1)) := by
  simpa [quarticInterlacingRow, QuarticInterlacingState.row,
    quarticInterlacingIterate, quarticInterlacingStep] using
    (hS.iterate hu hw hwv hvu n).f0_interl_f1

/-- The projected rows satisfy the quartic recurrence induced by the state
transition. -/
theorem quarticInterlacingRow_add_four
    (u v w : ℝ) (S : QuarticInterlacingState) (n : ℕ) :
    quarticInterlacingRow u v w S (n + 4) =
      C 2 * quarticInterlacingRow u v w S (n + 3) +
        (C (u + v - w) * X - 1) * quarticInterlacingRow u v w S (n + 2) +
        (C (2 * w - v) * X) * quarticInterlacingRow u v w S (n + 1) -
        (C w * X) * quarticInterlacingRow u v w S n := by
  simp [quarticInterlacingRow, QuarticInterlacingState.row,
    quarticInterlacingIterate, quarticInterlacingStep]
  simp only [map_ofNat]
  ring

end RealRooted
