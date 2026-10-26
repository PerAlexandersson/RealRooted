module

public import RealRooted.Interlacing.WindowInduction

/-!
# Variable-delay interlacing recurrences

We formalize the variable-predecessor induction behind Fisk, Example 16.10.
The proof uses the interlacing cone rules from Wagner (1992), Section 3.  The
recurrence is indexed at `n + 1`, so its hypotheses never mention `p 0`.
-/

@[expose] public section

open Finset Polynomial

noncomputable section

namespace RealRooted

private structure VariableDelayInvariant
    (Q : ℕ → ℝ[X]) (p : ℕ → ℕ) (n : ℕ) : Prop where
  nonneg : HasNonnegCoeffs (Q n)
  coeff_zero : (Q n).coeff 0 = 1
  splits : (Q n).Splits
  interl : ∀ i, p n ≤ i → i ≤ n → StrictInterl (Q i) (Q n)

private theorem variableDelay_recurrence_invariant
    (Q : ℕ → ℝ[X]) (p : ℕ → ℕ) (w : ℕ → ℝ)
    (hpmono : ∀ {i j}, 1 ≤ i → i ≤ j → p i ≤ p j)
    (hplt : ∀ n, 1 ≤ n → p n < n)
    (hw : ∀ n, 0 ≤ w n)
    (hQ0 : Q 0 = 1)
    (hrec : ∀ n, Q (n + 1) = Q n + C (w (n + 1)) * X * Q (p (n + 1))) :
    ∀ n, VariableDelayInvariant Q p n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [hQ0] using hasNonnegCoeffs_one
        · simp [hQ0]
        · simp [hQ0]
        intro i _ hi
        have hi0 : i = 0 := by lia
        subst i
        simpa [hQ0] using StrictInterl.refl one_ne_zero Polynomial.Splits.one
      · have hn := ih n (by lia)
        have hp_lt : p (n + 1) < n + 1 := hplt (n + 1) (by lia)
        have hp_inv := ih (p (n + 1)) hp_lt
        have hnonneg : HasNonnegCoeffs (Q (n + 1)) := by
          rw [hrec n]
          exact hn.nonneg.add
            ((hasNonnegCoeffs_C_mul (hw (n + 1)) hasNonnegCoeffs_X).mul hp_inv.nonneg)
        have hcoeff : (Q (n + 1)).coeff 0 = 1 := by
          rw [hrec n, coeff_add, coeff_mul]
          simp [hn.coeff_zero]
        have hne : Q (n + 1) ≠ 0 := by
          intro hzero
          rw [hzero, coeff_zero] at hcoeff
          norm_num at hcoeff
        have hinterl_lt : ∀ i, p (n + 1) ≤ i → i < n + 1 →
            StrictInterl (Q i) (Q (n + 1)) := by
          intro i hpi hi
          have hi_le : i ≤ n := by lia
          have htop : StrictInterl (Q i) (Q n) := by
            by_cases hn0 : n = 0
            · subst n
              have hi0 : i = 0 := by lia
              subst i
              rw [hQ0]
              exact StrictInterl.refl one_ne_zero Polynomial.Splits.one
            · exact hn.interl i
                (le_trans (hpmono (by lia) (by lia)) hpi) hi_le
          have hbottom : StrictInterl (Q (p (n + 1))) (Q i) := by
            by_cases hip : i = p (n + 1)
            · subst i
              exact StrictInterl.refl
                (hp_inv.nonneg.pos_leadingCoeff (by
                  intro hzero
                  have hcoeff := hp_inv.coeff_zero
                  rw [hzero, coeff_zero] at hcoeff
                  norm_num at hcoeff)).ne_zero
                hp_inv.splits
            · have hi_pos : 1 ≤ i := by lia
              have hi_inv := ih i hi
              exact hi_inv.interl (p (n + 1))
                (hpmono hi_pos (by lia)) hpi
          have hlag : StrictInterl (Q i) (X * Q (p (n + 1))) :=
            strictInterl_mul_X_of_strictInterl_of_nonneg
              hbottom hp_inv.nonneg (ih i hi).nonneg
          by_cases hw0 : w (n + 1) = 0
          · rw [hrec n, hw0]
            simpa using htop
          · have hwpos : 0 < w (n + 1) := lt_of_le_of_ne (hw (n + 1)) (Ne.symm hw0)
            rw [hrec n]
            exact StrictInterl.add_mul_X_of_common_left hwpos htop hlag
              (hn.nonneg.pos_leadingCoeff (by
                intro hzero
                have hcoeff := hn.coeff_zero
                rw [hzero, coeff_zero] at hcoeff
                norm_num at hcoeff))
              ((hasPosLeadingCoeff_of_monic monic_X).mul
                (hp_inv.nonneg.pos_leadingCoeff (by
                  intro hzero
                  have hcoeff := hp_inv.coeff_zero
                  rw [hzero, coeff_zero] at hcoeff
                  norm_num at hcoeff)))
        have hanchor := hinterl_lt (p (n + 1)) le_rfl hp_lt
        refine ⟨hnonneg, hcoeff, hanchor.2.1.2, ?_⟩
        intro i hpi hi
        rcases eq_or_lt_of_le hi with rfl | hi
        · exact StrictInterl.refl hne hanchor.2.1.2
        · exact hinterl_lt i hpi hi

/-- Every row of a nonnegative variable-delay recurrence has nonnegative coefficients.

The recurrence is indexed at `n + 1`, so no condition on `p 0` is needed. -/
theorem hasNonnegCoeffs_of_variableDelay_recurrence
    (Q : ℕ → ℝ[X]) (p : ℕ → ℕ) (w : ℕ → ℝ)
    (hpmono : ∀ {i j}, 1 ≤ i → i ≤ j → p i ≤ p j)
    (hplt : ∀ n, 1 ≤ n → p n < n)
    (hw : ∀ n, 0 ≤ w n)
    (hQ0 : Q 0 = 1)
    (hrec : ∀ n, Q (n + 1) = Q n + C (w (n + 1)) * X * Q (p (n + 1)))
    (n : ℕ) :
    HasNonnegCoeffs (Q n) :=
  (variableDelay_recurrence_invariant Q p w hpmono hplt hw hQ0 hrec n).nonneg

/-- Every row of a variable-delay recurrence has constant coefficient one. -/
theorem coeff_zero_of_variableDelay_recurrence
    (Q : ℕ → ℝ[X]) (p : ℕ → ℕ) (w : ℕ → ℝ)
    (hpmono : ∀ {i j}, 1 ≤ i → i ≤ j → p i ≤ p j)
    (hplt : ∀ n, 1 ≤ n → p n < n)
    (hw : ∀ n, 0 ≤ w n)
    (hQ0 : Q 0 = 1)
    (hrec : ∀ n, Q (n + 1) = Q n + C (w (n + 1)) * X * Q (p (n + 1)))
    (n : ℕ) :
    (Q n).coeff 0 = 1 :=
  (variableDelay_recurrence_invariant Q p w hpmono hplt hw hQ0 hrec n).coeff_zero

/-- Every row of a nonnegative variable-delay recurrence splits over the reals.

This is the variable-delay form of the induction in Fisk, Example 16.10, using
Wagner's interlacing cone rules. -/
theorem splits_of_variableDelay_recurrence
    (Q : ℕ → ℝ[X]) (p : ℕ → ℕ) (w : ℕ → ℝ)
    (hpmono : ∀ {i j}, 1 ≤ i → i ≤ j → p i ≤ p j)
    (hplt : ∀ n, 1 ≤ n → p n < n)
    (hw : ∀ n, 0 ≤ w n)
    (hQ0 : Q 0 = 1)
    (hrec : ∀ n, Q (n + 1) = Q n + C (w (n + 1)) * X * Q (p (n + 1)))
    (n : ℕ) :
    (Q n).Splits :=
  (variableDelay_recurrence_invariant Q p w hpmono hplt hw hQ0 hrec n).splits

/-- **Weighted variable-delay interlacing.**  If `p` is nondecreasing on the
positive integers and `p n < n`, then every row from `p n` through `n`
interlaces `Q n` from the left.  Zero weights are allowed.

This generalizes the fixed-lag induction in Fisk, Example 16.10; the cone step
is Wagner (1992), Section 3. -/
theorem strictInterl_of_variableDelay_recurrence
    (Q : ℕ → ℝ[X]) (p : ℕ → ℕ) (w : ℕ → ℝ)
    (hpmono : ∀ {i j}, 1 ≤ i → i ≤ j → p i ≤ p j)
    (hplt : ∀ n, 1 ≤ n → p n < n)
    (hw : ∀ n, 0 ≤ w n)
    (hQ0 : Q 0 = 1)
    (hrec : ∀ n, Q (n + 1) = Q n + C (w (n + 1)) * X * Q (p (n + 1)))
    {n i : ℕ} (hpi : p n ≤ i) (hin : i ≤ n) :
    StrictInterl (Q i) (Q n) :=
  (variableDelay_recurrence_invariant Q p w hpmono hplt hw hQ0 hrec n).interl i hpi hin

/-- Positive coefficients on the preceding row can be normalized away in a
variable-delay recurrence.  Thus the recurrence
`F (n + 1) = a (n + 1) F n + b (n + 1) X F (p (n + 1))` has the same
interlacing interval as its monic-in-the-previous-row normalization. -/
theorem strictInterl_of_scaled_variableDelay_recurrence
    (F : ℕ → ℝ[X]) (p : ℕ → ℕ) (a b : ℕ → ℝ)
    (hpmono : ∀ {i j}, 1 ≤ i → i ≤ j → p i ≤ p j)
    (hplt : ∀ n, 1 ≤ n → p n < n)
    (ha : ∀ n, 0 < a n)
    (hb : ∀ n, 0 ≤ b n)
    (hF0 : F 0 = 1)
    (hrec : ∀ n,
      F (n + 1) = C (a (n + 1)) * F n + C (b (n + 1)) * X * F (p (n + 1)))
    {n i : ℕ} (hpi : p n ≤ i) (hin : i ≤ n) :
    StrictInterl (F i) (F n) := by
  let A : ℕ → ℝ := fun m ↦ ∏ k ∈ range m, a (k + 1)
  have hApos : ∀ m, 0 < A m := by
    intro m
    exact Finset.prod_pos fun k _ ↦ ha (k + 1)
  have hAsucc (m : ℕ) : A (m + 1) = A m * a (m + 1) := by
    simp [A, Finset.prod_range_succ]
  let Q : ℕ → ℝ[X] := fun m ↦ C (A m)⁻¹ * F m
  let w : ℕ → ℝ := fun m ↦ b m * A (p m) / A m
  have hw : ∀ m, 0 ≤ w m := by
    intro m
    exact div_nonneg (mul_nonneg (hb m) (hApos (p m)).le) (hApos m).le
  have hQ0 : Q 0 = 1 := by
    simp [Q, A, hF0]
  have hQrec : ∀ m,
      Q (m + 1) = Q m + C (w (m + 1)) * X * Q (p (m + 1)) := by
    intro m
    dsimp [Q, w]
    rw [hrec m, hAsucc m]
    have hAm : A m ≠ 0 := (hApos m).ne'
    have ha_m : a (m + 1) ≠ 0 := (ha (m + 1)).ne'
    have hAp : A (p (m + 1)) ≠ 0 := (hApos (p (m + 1))).ne'
    have hscalar₁ : (A m * a (m + 1))⁻¹ * a (m + 1) = (A m)⁻¹ := by
      field_simp
    have hscalar₂ :
        (A m * a (m + 1))⁻¹ * b (m + 1) =
          (b (m + 1) * A (p (m + 1)) / (A m * a (m + 1))) *
            (A (p (m + 1)))⁻¹ := by
      field_simp
    rw [mul_add]
    congr 1
    · calc
        C (A m * a (m + 1))⁻¹ * (C (a (m + 1)) * F m) =
            C ((A m * a (m + 1))⁻¹ * a (m + 1)) * F m := by
              rw [← mul_assoc, ← C_mul]
        _ = C (A m)⁻¹ * F m := by rw [hscalar₁]
    · calc
        C (A m * a (m + 1))⁻¹ * (C (b (m + 1)) * X * F (p (m + 1))) =
            (C (A m * a (m + 1))⁻¹ * C (b (m + 1))) * X *
              F (p (m + 1)) := by ring
        _ = C ((A m * a (m + 1))⁻¹ * b (m + 1)) * X * F (p (m + 1)) := by
          rw [← C_mul]
        _ = C ((b (m + 1) * A (p (m + 1)) / (A m * a (m + 1))) *
              (A (p (m + 1)))⁻¹) * X * F (p (m + 1)) := by
          rw [hscalar₂]
        _ = C (b (m + 1) * A (p (m + 1)) / (A m * a (m + 1))) * X *
              (C (A (p (m + 1)))⁻¹ * F (p (m + 1))) := by
          rw [C_mul]
          ring
  have hinterl : StrictInterl (Q i) (Q n) :=
    strictInterl_of_variableDelay_recurrence Q p w hpmono hplt hw hQ0 hQrec hpi hin
  have hscaled := (hinterl.C_mul_left (hApos i).ne').C_mul_right (hApos n).ne'
  simpa [Q, ← mul_assoc, ← C_mul, (hApos i).ne', (hApos n).ne'] using hscaled

/-- **Weighted fixed-delay window.**  A recurrence with predecessor `n - L`
has an interlacing window of `L + 1` rows.  The weights may vary and may vanish. -/
theorem strictInterl_of_fixedDelay_recurrence
    (Q : ℕ → ℝ[X]) (w : ℕ → ℝ) (L : ℕ) (hL : 1 ≤ L)
    (hw : ∀ n, 0 ≤ w n)
    (hQ0 : Q 0 = 1)
    (hrec : ∀ n, Q (n + 1) = Q n + C (w (n + 1)) * X * Q (n + 1 - L))
    {A B : ℕ} (hAB : A ≤ B) (hBA : B ≤ A + L) :
    StrictInterl (Q A) (Q B) := by
  apply strictInterl_of_variableDelay_recurrence Q (fun n ↦ n - L) w
    (fun {_ _} _ hij ↦ Nat.sub_le_sub_right hij L) (fun n hn ↦ by lia)
    hw hQ0 hrec
  · lia
  · exact hAB

/-- Nonnegative coefficients for a scaled fixed-delay recurrence. -/
theorem hasNonnegCoeffs_of_scaled_fixedDelay_recurrence
    (P : ℕ → ℝ[X]) (a b : ℕ → ℝ) (L : ℕ) (hL : 1 ≤ L)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hP0 : P 0 = 1)
    (hrec : ∀ n,
      P (n + 1) = C (a (n + 1)) * P n + C (b (n + 1)) * X * P (n + 1 - L))
    (n : ℕ) :
    HasNonnegCoeffs (P n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · simpa [hP0] using hasNonnegCoeffs_one
    · have hdelay : n + 1 - L < n + 1 := by lia
      rw [hrec n]
      exact (hasNonnegCoeffs_C_mul (ha (n + 1)) (ih n (by lia))).add
        ((hasNonnegCoeffs_C_mul (hb (n + 1)) hasNonnegCoeffs_X).mul
          (ih (n + 1 - L) hdelay))

/-- Fixed-delay specialization of the scaled variable-delay theorem. -/
theorem strictInterl_of_scaled_fixedDelay_recurrence
    (P : ℕ → ℝ[X]) (a b : ℕ → ℝ) (L : ℕ) (hL : 1 ≤ L)
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 ≤ b n)
    (hP0 : P 0 = 1)
    (hrec : ∀ n,
      P (n + 1) = C (a (n + 1)) * P n + C (b (n + 1)) * X * P (n + 1 - L))
    {A B : ℕ} (hAB : A ≤ B) (hBA : B ≤ A + L) :
    StrictInterl (P A) (P B) := by
  apply strictInterl_of_scaled_variableDelay_recurrence P (fun n ↦ n - L) a b
    (fun {_ _} _ hij ↦ Nat.sub_le_sub_right hij L) (fun n hn ↦ by lia)
    ha hb hP0 hrec
  · lia
  · exact hAB

end RealRooted
