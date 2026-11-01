module

public import RealRooted.PFPolynomial

/-!
# A quartic recurrence from seven interlacing comparisons

We package the five polynomials in the invariant as a proof-carrying state.
Its successor is built from common-interlacer cone rules and Wagner's
`X`-multiplication rule.  Iterating the successor gives the scalar quartic
recurrence and consecutive weak interlacing.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- A valid five-polynomial state for the quartic transition with parameters
`u`, `v`, and `w`. -/
structure QuarticInterlacingState (u v w : ℝ) where
  /-- The oldest polynomial in the three-row window. -/
  f0 : ℝ[X]
  /-- The middle polynomial in the three-row window. -/
  f1 : ℝ[X]
  /-- The newest polynomial in the three-row window. -/
  f2 : ℝ[X]
  /-- The first auxiliary polynomial. -/
  d : ℝ[X]
  /-- The second auxiliary polynomial. -/
  s : ℝ[X]
  /-- The oldest polynomial is Pólya-frequency. -/
  f0_pf : IsPFPolynomial f0
  /-- The middle polynomial is Pólya-frequency. -/
  f1_pf : IsPFPolynomial f1
  /-- The newest polynomial is Pólya-frequency. -/
  f2_pf : IsPFPolynomial f2
  /-- The first auxiliary polynomial is Pólya-frequency. -/
  d_pf : IsPFPolynomial d
  /-- The second auxiliary polynomial is Pólya-frequency. -/
  s_pf : IsPFPolynomial s
  /-- The oldest polynomial is nonzero. -/
  f0_ne : f0 ≠ 0
  /-- The middle polynomial is nonzero. -/
  f1_ne : f1 ≠ 0
  /-- The newest polynomial is nonzero. -/
  f2_ne : f2 ≠ 0
  /-- The first auxiliary polynomial is nonzero. -/
  d_ne : d ≠ 0
  /-- The second auxiliary polynomial is nonzero. -/
  s_ne : s ≠ 0
  /-- The oldest polynomial weakly interlaces the middle polynomial. -/
  f0_interl_f1 : Interl f0 f1
  /-- The oldest polynomial weakly interlaces the newest polynomial. -/
  f0_interl_f2 : Interl f0 f2
  /-- The middle polynomial weakly interlaces the newest polynomial. -/
  f1_interl_f2 : Interl f1 f2
  /-- The middle polynomial weakly interlaces the first auxiliary polynomial. -/
  f1_interl_d : Interl f1 d
  /-- The middle polynomial weakly interlaces the second auxiliary polynomial. -/
  f1_interl_s : Interl f1 s
  /-- The newest polynomial weakly interlaces the second auxiliary polynomial. -/
  f2_interl_s : Interl f2 s
  /-- The first auxiliary polynomial weakly interlaces the second one. -/
  d_interl_s : Interl d s
  /-- The linear identity coupling the newest and auxiliary polynomials. -/
  balance : f2 = C u * d + C v * s - C w * (X * f0)

namespace QuarticInterlacingState

/-- The successor's second auxiliary polynomial. -/
@[expose] def sNext {u v w : ℝ} (state : QuarticInterlacingState u v w) : ℝ[X] :=
  state.s + X * state.f1

/-- The successor's first auxiliary polynomial. -/
@[expose] def dNext {u v w : ℝ} (state : QuarticInterlacingState u v w) : ℝ[X] :=
  state.d + state.sNext

/-- The new polynomial appended by the quartic transition. -/
@[expose] def fNext {u v w : ℝ} (state : QuarticInterlacingState u v w) : ℝ[X] :=
  state.f2 + C u * state.s + C (u + v - w) * (X * state.f1) +
    C w * (X * state.f0)

/-- The first auxiliary successor as a nonnegative combination of old
coordinates in the permitted parameter range. -/
theorem dNext_eq_nonneg_sum {u v w : ℝ}
    (state : QuarticInterlacingState u v w) (hu : 0 < u) :
    state.dNext =
      C u⁻¹ * state.f2 + C (w / u) * (X * state.f0) + X * state.f1 +
        C (1 - v / u) * state.s := by
  rw [dNext, sNext, state.balance]
  ext n
  simp only [coeff_add, coeff_sub, coeff_C_mul]
  field_simp [hu.ne']
  ring

/-- The new polynomial as a nonnegative combination with common right
interlacer `sNext` in the permitted parameter range. -/
theorem fNext_eq_nonneg_sum {u v w : ℝ}
    (state : QuarticInterlacingState u v w) :
    state.fNext =
      C u * state.dNext + C w * state.s + C (v - w) * state.sNext := by
  rw [fNext, dNext, sNext, state.balance]
  ext n
  simp only [coeff_add, coeff_sub, coeff_C_mul]
  ring

/-- The seven weak interlacing comparisons, PF conditions, nonvanishing, and
the balance identity are preserved by one quartic transition. -/
@[expose] def next {u v w : ℝ} (state : QuarticInterlacingState u v w)
    (hu : 0 < u) (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) :
    QuarticInterlacingState u v w := by
  have hu0 : 0 ≤ u := hu.le
  have huv0 : 0 ≤ u + v - w := by linarith
  have hvw0 : 0 ≤ v - w := by linarith
  have hwu0 : 0 ≤ w / u := div_nonneg hw hu.le
  have hinvu0 : 0 ≤ u⁻¹ := inv_nonneg.mpr hu.le
  have hvu0 : 0 ≤ 1 - v / u := by
    rw [sub_nonneg, div_le_one hu]
    exact hvu
  have hf0nn := state.f0_pf.hasNonnegCoeffs
  have hf1nn := state.f1_pf.hasNonnegCoeffs
  have hf2nn := state.f2_pf.hasNonnegCoeffs
  have hdnn := state.d_pf.hasNonnegCoeffs
  have hsnn := state.s_pf.hasNonnegCoeffs
  have hXf0nn : HasNonnegCoeffs (X * state.f0) := hf0nn.X_mul
  have hXf1nn : HasNonnegCoeffs (X * state.f1) := hf1nn.X_mul
  have hf1_Xf0 : Interl state.f1 (X * state.f0) :=
    interl_mul_X_of_interl state.f0_interl_f1 hf0nn hf1nn
  have hf2_Xf0 : Interl state.f2 (X * state.f0) :=
    interl_mul_X_of_interl state.f0_interl_f2 hf0nn hf2nn
  have hf2_Xf1 : Interl state.f2 (X * state.f1) :=
    interl_mul_X_of_interl state.f1_interl_f2 hf1nn hf2nn
  have hd_Xf1 : Interl state.d (X * state.f1) :=
    interl_mul_X_of_interl state.f1_interl_d hf1nn hdnn
  have hs_Xf1 : Interl state.s (X * state.f1) :=
    interl_mul_X_of_interl state.f1_interl_s hf1nn hsnn
  have hf1_Xf1 : Interl state.f1 (X * state.f1) :=
    interl_mul_X_of_interl state.f1_pf.interl_self hf1nn hf1nn
  have hs_sNext : Interl state.s state.sNext := by
    simpa [sNext] using interl_add_right_of_common_left_of_nonneg
      state.s_pf.interl_self hs_Xf1 hsnn hXf1nn
  have hd_sNext : Interl state.d state.sNext := by
    simpa [sNext] using interl_add_right_of_common_left_of_nonneg
      state.d_interl_s hd_Xf1 hsnn hXf1nn
  have hf2_sNext : Interl state.f2 state.sNext := by
    simpa [sNext] using interl_add_right_of_common_left_of_nonneg
      state.f2_interl_s hf2_Xf1 hsnn hXf1nn
  have hsNext_nn : HasNonnegCoeffs state.sNext := hsnn.add hXf1nn
  have hsNext_ne : state.sNext ≠ 0 := by
    rw [sNext, add_comm]
    exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hXf1nn hsnn state.s_ne
  have hsNext_pf : IsPFPolynomial state.sNext :=
    IsPFPolynomial.of_realRooted_nonneg hsNext_nn
      (hs_sNext.toStrictInterl_of_ne state.s_ne hsNext_ne).2.1.2
  have hdNext_sNext : Interl state.dNext state.sNext := by
    simpa [dNext] using interl_add_left_of_common_right_of_nonneg
      hd_sNext hsNext_pf.interl_self hdnn hsNext_pf.hasNonnegCoeffs
  have hdNext_nn : HasNonnegCoeffs state.dNext := hdnn.add hsNext_nn
  have hdNext_ne : state.dNext ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hdnn
      hsNext_pf.hasNonnegCoeffs hsNext_ne
  have hdNext_pf : IsPFPolynomial state.dNext :=
    IsPFPolynomial.of_realRooted_nonneg hdNext_nn
      (hdNext_sNext.toStrictInterl_of_ne hdNext_ne hsNext_ne).1.2
  have hf1_fNext : Interl state.f1 state.fNext := by
    have hleft := interl_add_right_of_common_left_of_nonneg
      state.f1_interl_f2 (state.f1_interl_s.C_mul_right_of_nonneg hu0)
      hf2nn (hasNonnegCoeffs_C_mul hu0 hsnn)
    have hright := interl_add_right_of_common_left_of_nonneg
      (hf1_Xf1.C_mul_right_of_nonneg huv0)
      (hf1_Xf0.C_mul_right_of_nonneg hw)
      (hasNonnegCoeffs_C_mul huv0 hXf1nn)
      (hasNonnegCoeffs_C_mul hw hXf0nn)
    have h := interl_add_right_of_common_left_of_nonneg hleft hright
      (hf2nn.add (hasNonnegCoeffs_C_mul hu0 hsnn))
      ((hasNonnegCoeffs_C_mul huv0 hXf1nn).add
        (hasNonnegCoeffs_C_mul hw hXf0nn))
    simpa [fNext, add_assoc] using h
  have hf2_fNext : Interl state.f2 state.fNext := by
    have hleft := interl_add_right_of_common_left_of_nonneg
      state.f2_pf.interl_self (state.f2_interl_s.C_mul_right_of_nonneg hu0)
      hf2nn (hasNonnegCoeffs_C_mul hu0 hsnn)
    have hright := interl_add_right_of_common_left_of_nonneg
      (hf2_Xf1.C_mul_right_of_nonneg huv0)
      (hf2_Xf0.C_mul_right_of_nonneg hw)
      (hasNonnegCoeffs_C_mul huv0 hXf1nn)
      (hasNonnegCoeffs_C_mul hw hXf0nn)
    have h := interl_add_right_of_common_left_of_nonneg hleft hright
      (hf2nn.add (hasNonnegCoeffs_C_mul hu0 hsnn))
      ((hasNonnegCoeffs_C_mul huv0 hXf1nn).add
        (hasNonnegCoeffs_C_mul hw hXf0nn))
    simpa [fNext, add_assoc] using h
  have hf2_dNext : Interl state.f2 state.dNext := by
    have hleft := interl_add_right_of_common_left_of_nonneg
      (state.f2_pf.interl_self.C_mul_right_of_nonneg hinvu0)
      (hf2_Xf0.C_mul_right_of_nonneg hwu0)
      (hasNonnegCoeffs_C_mul hinvu0 hf2nn)
      (hasNonnegCoeffs_C_mul hwu0 hXf0nn)
    have hright := interl_add_right_of_common_left_of_nonneg hf2_Xf1
      (state.f2_interl_s.C_mul_right_of_nonneg hvu0) hXf1nn
      (hasNonnegCoeffs_C_mul hvu0 hsnn)
    have h := interl_add_right_of_common_left_of_nonneg hleft hright
      ((hasNonnegCoeffs_C_mul hinvu0 hf2nn).add
        (hasNonnegCoeffs_C_mul hwu0 hXf0nn))
      (hXf1nn.add (hasNonnegCoeffs_C_mul hvu0 hsnn))
    rw [dNext_eq_nonneg_sum state hu]
    simpa [add_assoc] using h
  have hfNext_sNext : Interl state.fNext state.sNext := by
    have hleft : Interl (C u * state.dNext + C w * state.s) state.sNext :=
      interl_add_left_of_common_right_of_nonneg
        (hdNext_sNext.C_mul_left_of_nonneg hu0)
        (hs_sNext.C_mul_left_of_nonneg hw)
        (hasNonnegCoeffs_C_mul hu0 hdNext_pf.hasNonnegCoeffs)
        (hasNonnegCoeffs_C_mul hw hsnn)
    have h := interl_add_left_of_common_right_of_nonneg hleft
      (hsNext_pf.interl_self.C_mul_left_of_nonneg hvw0)
      ((hasNonnegCoeffs_C_mul hu0 hdNext_pf.hasNonnegCoeffs).add
        (hasNonnegCoeffs_C_mul hw hsnn))
      (hasNonnegCoeffs_C_mul hvw0 hsNext_pf.hasNonnegCoeffs)
    rw [fNext_eq_nonneg_sum state]
    simpa [add_assoc] using h
  have hfNext_nn : HasNonnegCoeffs state.fNext := by
    exact ((hf2nn.add (hasNonnegCoeffs_C_mul hu0 hsnn)).add
      (hasNonnegCoeffs_C_mul huv0 hXf1nn)).add
        (hasNonnegCoeffs_C_mul hw hXf0nn)
  have hfNext_ne : state.fNext ≠ 0 := by
    simpa [fNext, add_assoc, add_comm, add_left_comm] using
      add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      (((hasNonnegCoeffs_C_mul hu0 hsnn).add
        (hasNonnegCoeffs_C_mul huv0 hXf1nn)).add
          (hasNonnegCoeffs_C_mul hw hXf0nn)) hf2nn state.f2_ne
  have hfNext_pf : IsPFPolynomial state.fNext :=
    IsPFPolynomial.of_realRooted_nonneg hfNext_nn
      (hf2_fNext.toStrictInterl_of_ne state.f2_ne hfNext_ne).2.1.2
  refine
    { f0 := state.f1
      f1 := state.f2
      f2 := state.fNext
      d := state.dNext
      s := state.sNext
      f0_pf := state.f1_pf
      f1_pf := state.f2_pf
      f2_pf := hfNext_pf
      d_pf := hdNext_pf
      s_pf := hsNext_pf
      f0_ne := state.f1_ne
      f1_ne := state.f2_ne
      f2_ne := hfNext_ne
      d_ne := hdNext_ne
      s_ne := hsNext_ne
      f0_interl_f1 := state.f1_interl_f2
      f0_interl_f2 := hf1_fNext
      f1_interl_f2 := hf2_fNext
      f1_interl_d := hf2_dNext
      f1_interl_s := hf2_sNext
      f2_interl_s := hfNext_sNext
      d_interl_s := hdNext_sNext
      balance := ?_ }
  rw [fNext, dNext, sNext]
  rw [state.balance]
  ext n
  simp only [coeff_add, coeff_sub, coeff_C_mul]
  ring

/-- The oldest coordinate of the successor is the previous middle coordinate. -/
@[simp] private theorem next_f0 {u v w : ℝ}
    (state : QuarticInterlacingState u v w)
    (hu : 0 < u) (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) :
    (state.next hu hw hwv hvu).f0 = state.f1 := by
  rfl

/-- The middle coordinate of the successor is the previous newest coordinate. -/
@[simp] private theorem next_f1 {u v w : ℝ}
    (state : QuarticInterlacingState u v w)
    (hu : 0 < u) (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) :
    (state.next hu hw hwv hvu).f1 = state.f2 := by
  rfl

/-- The newest coordinate of the successor is the quartic transition output. -/
@[simp] private theorem next_f2 {u v w : ℝ}
    (state : QuarticInterlacingState u v w)
    (hu : 0 < u) (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) :
    (state.next hu hw hwv hvu).f2 = state.fNext := by
  rfl

/-- The successor's second auxiliary coordinate is `sNext`. -/
@[simp] private theorem next_s {u v w : ℝ}
    (state : QuarticInterlacingState u v w)
    (hu : 0 < u) (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) :
    (state.next hu hw hwv hvu).s = state.sNext := by
  rfl

end QuarticInterlacingState

/-- The sequence of valid states obtained by repeatedly applying the quartic
transition. -/
@[expose] def quarticInterlacingStates {u v w : ℝ}
    (initial : QuarticInterlacingState u v w)
    (hu : 0 < u) (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) :
    ℕ → QuarticInterlacingState u v w
  | 0 => initial
  | n + 1 => (quarticInterlacingStates initial hu hw hwv hvu n).next hu hw hwv hvu

/-- The polynomial sequence formed by the oldest coordinate of each iterated
quartic state. -/
@[expose] def quarticInterlacingSequence {u v w : ℝ}
    (initial : QuarticInterlacingState u v w)
    (hu : 0 < u) (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) :
    ℕ → ℝ[X] :=
  fun n ↦ (quarticInterlacingStates initial hu hw hwv hvu n).f0

/-- The iterated state sequence satisfies the scalar quartic recurrence. -/
theorem quarticInterlacingSequence_recurrence {u v w : ℝ}
    (initial : QuarticInterlacingState u v w)
    (hu : 0 < u) (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) (n : ℕ) :
    quarticInterlacingSequence initial hu hw hwv hvu (n + 4) =
      2 * quarticInterlacingSequence initial hu hw hwv hvu (n + 3) +
        (C (u + v - w) * X - 1) *
          quarticInterlacingSequence initial hu hw hwv hvu (n + 2) +
        C (2 * w - v) * X *
          quarticInterlacingSequence initial hu hw hwv hvu (n + 1) -
        C w * X * quarticInterlacingSequence initial hu hw hwv hvu n := by
  simp only [quarticInterlacingSequence]
  rw [show n + 4 = (((n + 1) + 1) + 1) + 1 by lia,
    show n + 3 = ((n + 1) + 1) + 1 by lia,
    show n + 2 = (n + 1) + 1 by lia]
  simp only [quarticInterlacingStates, QuarticInterlacingState.next_f0,
    QuarticInterlacingState.next_f1, QuarticInterlacingState.next_f2,
    QuarticInterlacingState.next_s, QuarticInterlacingState.fNext,
    QuarticInterlacingState.sNext]
  have hCtwo : C (2 : ℝ) = (2 : ℝ[X]) := map_ofNat C 2
  rw [show C (u + v - w) = C u + C v - C w by simp,
    show C (2 * w - v) = C 2 * C w - C v by rw [map_sub, map_mul], hCtwo]
  ring

/-- Every polynomial in the iterated quartic sequence is Pólya-frequency. -/
theorem quarticInterlacingSequence_isPFPolynomial {u v w : ℝ}
    (initial : QuarticInterlacingState u v w)
    (hu : 0 < u) (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) (n : ℕ) :
    IsPFPolynomial (quarticInterlacingSequence initial hu hw hwv hvu n) :=
  (quarticInterlacingStates initial hu hw hwv hvu n).f0_pf

/-- Consecutive polynomials in the iterated quartic sequence weakly
interlace. -/
theorem quarticInterlacingSequence_interl_succ {u v w : ℝ}
    (initial : QuarticInterlacingState u v w)
    (hu : 0 < u) (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u) (n : ℕ) :
    Interl (quarticInterlacingSequence initial hu hw hwv hvu n)
      (quarticInterlacingSequence initial hu hw hwv hvu (n + 1)) := by
  simpa [quarticInterlacingSequence, quarticInterlacingStates,
    QuarticInterlacingState.next_f0] using
    (quarticInterlacingStates initial hu hw hwv hvu n).f0_interl_f1

/-- Any sequence with the four rows supplied by a valid initial state and the
quartic recurrence consists of PF polynomials with consecutive weak
interlacing. -/
theorem isPFPolynomial_and_interl_of_quartic_recurrence
    {u v w : ℝ} {F : ℕ → ℝ[X]}
    (initial : QuarticInterlacingState u v w)
    (hu : 0 < u) (hw : 0 ≤ w) (hwv : w ≤ v) (hvu : v ≤ u)
    (h0 : F 0 = initial.f0) (h1 : F 1 = initial.f1)
    (h2 : F 2 = initial.f2) (h3 : F 3 = initial.fNext)
    (hrec : ∀ n,
      F (n + 4) = 2 * F (n + 3) + (C (u + v - w) * X - 1) * F (n + 2) +
        C (2 * w - v) * X * F (n + 1) - C w * X * F n) :
    ∀ n, IsPFPolynomial (F n) ∧ Interl (F n) (F (n + 1)) := by
  have heq : ∀ n, F n = quarticInterlacingSequence initial hu hw hwv hvu n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hn : n < 4
        · interval_cases n <;>
            simp [quarticInterlacingSequence, quarticInterlacingStates,
              QuarticInterlacingState.next_f0, QuarticInterlacingState.next_f1,
              QuarticInterlacingState.next_f2, h0, h1, h2, h3]
        · have hn4 : 4 ≤ n := by lia
          obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn4
          rw [show 4 + m = m + 4 by ac_rfl]
          rw [hrec m, quarticInterlacingSequence_recurrence]
          rw [ih m (by lia), ih (m + 1) (by lia), ih (m + 2) (by lia),
            ih (m + 3) (by lia)]
  intro n
  rw [heq n, heq (n + 1)]
  exact ⟨quarticInterlacingSequence_isPFPolynomial initial hu hw hwv hvu n,
    quarticInterlacingSequence_interl_succ initial hu hw hwv hvu n⟩

end RealRooted
