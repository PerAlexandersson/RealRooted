module

import RealRooted.LiuWang.SequenceCore
import RealRooted.ThreeTermRecurrence.Degree
import RealRooted.ThreeTermRecurrence.NoCommonRoot
public import RealRooted.SimpleRoots
public import RealRooted.Basic.Coefficients

/-!
# Positive affine-lag recurrences

We study recurrences

`P (n + 2) = C (1 + b n + c n) * P (n + 1) + (C (d n) * X - C (b n)) * P n`

with positive constant seeds, nonnegative `b` and `c`, and positive `d`.  Successive
differences have nonnegative coefficients, which gives coefficient positivity without
expanding the recurrence by parity.  The existing plateau-capable Liu--Wang criterion then
gives directed interlacing for the degree schedule `n / 2`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted.PositiveAffineLag

/-- The recurrence for the successive differences preserves coefficientwise nonnegativity. -/
private theorem coefficients_nonneg
    {P : ℕ → ℝ[X]} {p q : ℝ} {b c d : ℕ → ℝ}
    (hp : 0 < p) (hpq : p ≤ q)
    (hb : ∀ n, 0 ≤ b n) (hc : ∀ n, 0 ≤ c n) (hd : ∀ n, 0 < d n)
    (hP0 : P 0 = C p) (hP1 : P 1 = C q)
    (hrec : ∀ n, P (n + 2) =
      C (1 + b n + c n) * P (n + 1) + (C (d n) * X - C (b n)) * P n) :
    ∀ n, HasNonnegCoeffs (P n) ∧ HasNonnegCoeffs (P (n + 1) - P n) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · simpa [hP0] using hasNonnegCoeffs_C hp.le
      · simpa [hP0, hP1] using hasNonnegCoeffs_C (sub_nonneg.mpr hpq)
  | succ n ih =>
      have hPn1 : HasNonnegCoeffs (P (n + 1)) := by
        rw [show P (n + 1) = P n + (P (n + 1) - P n) by ring]
        exact ih.1.add ih.2
      have hdiff : P (n + 2) - P (n + 1) =
          C (c n) * P (n + 1) + C (b n) * (P (n + 1) - P n) +
            (C (d n) * X) * P n := by
        rw [hrec n]
        simp only [map_add, map_one]
        ring
      refine ⟨hPn1, ?_⟩
      rw [hdiff]
      exact ((hasNonnegCoeffs_C_mul (hc n) hPn1).add
        (hasNonnegCoeffs_C_mul (hb n) ih.2)).add
          ((hasNonnegCoeffs_C (hd n).le).mul hasNonnegCoeffs_X |>.mul ih.1)

/-- Positive constant terms follow from the scalar ratio invariant with ratio one. -/
private theorem eval_zero_pos
    {P : ℕ → ℝ[X]} {p q : ℝ} {b c d : ℕ → ℝ}
    (hp : 0 < p) (hpq : p ≤ q) (hb : ∀ n, 0 ≤ b n) (hc : ∀ n, 0 ≤ c n)
    (hP0 : P 0 = C p) (hP1 : P 1 = C q)
    (hrec : ∀ n, P (n + 2) =
      C (1 + b n + c n) * P (n + 1) + (C (d n) * X - C (b n)) * P n) :
    ∀ n, 0 < (P n).eval 0 := by
  let A : ℕ → ℝ[X] := fun n ↦ C (1 + b n + c n)
  let B : ℕ → ℝ[X] := fun n ↦ C (d n) * X - C (b n)
  apply threeTermRatio_eval_zero_pos (P := P) (a := A) (b := B) (ρ := 1)
  · exact hrec
  · simpa [hP0] using hp
  · norm_num
  · simpa [hP0, hP1] using hpq
  · intro n
    simp [B, hb n]
  · intro n
    simp [A, B]
    linarith [hc n]

/-- The positive linear lag forces the exact half-growth degree schedule. -/
private theorem natDegree_eq_half
    {P : ℕ → ℝ[X]} {p q : ℝ} {b c d : ℕ → ℝ}
    (hp : 0 < p) (hpq : p ≤ q) (hb : ∀ n, 0 ≤ b n)
    (hc : ∀ n, 0 ≤ c n) (hd : ∀ n, 0 < d n)
    (hP0 : P 0 = C p) (hP1 : P 1 = C q)
    (hrec : ∀ n, P (n + 2) =
      C (1 + b n + c n) * P (n + 1) + (C (d n) * X - C (b n)) * P n) :
    ∀ n, (P n).natDegree = n / 2 := by
  let A : ℕ → ℝ[X] := fun n ↦ C (1 + b n + c n)
  let B : ℕ → ℝ[X] := fun n ↦ C (d n) * X - C (b n)
  intro n
  simpa [A, B] using threeTermHalf_natDegree (P := P) (a := A) (b := B)
    (d := 1) (D₀ := 0) (e := 0) hrec
    (fun n ↦ by simp [A]) (fun n ↦ by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · rw [natDegree_mul (C_ne_zero.mpr (hd n).ne') X_ne_zero]
        simp
      · simp) (by norm_num)
    (by simp [hP0]) (by simp [hP1]) (by simpa [hP0] using hp)
    (by have hq : 0 < q := hp.trans_le hpq; simpa [hP1] using hq)
    (fun n ↦ by simp [A]; linarith [hb n, hc n])
    (fun n ↦ by simp [B, hd n]) n

/-- Coefficient positivity, positive constant term, exact degree, and positive leading
coefficient for a positive affine-lag recurrence. -/
theorem coefficients_and_degree
    {P : ℕ → ℝ[X]} {p q : ℝ} {b c d : ℕ → ℝ}
    (hp : 0 < p) (hpq : p ≤ q)
    (hb : ∀ n, 0 ≤ b n) (hc : ∀ n, 0 ≤ c n) (hd : ∀ n, 0 < d n)
    (hP0 : P 0 = C p) (hP1 : P 1 = C q)
    (hrec : ∀ n, P (n + 2) =
      C (1 + b n + c n) * P (n + 1) + (C (d n) * X - C (b n)) * P n) :
    ∀ n, HasNonnegCoeffs (P n) ∧ HasNonnegCoeffs (P (n + 1) - P n) ∧
      0 < (P n).eval 0 ∧ (P n).natDegree = n / 2 ∧ HasPosLeadingCoeff (P n) := by
  have hnonneg := coefficients_nonneg hp hpq hb hc hd hP0 hP1 hrec
  have heval := eval_zero_pos hp hpq hb hc hP0 hP1 hrec
  have hdegree := natDegree_eq_half hp hpq hb hc hd hP0 hP1 hrec
  intro n
  have hne : P n ≠ 0 := by
    intro hzero
    have hn := heval n
    rw [hzero] at hn
    simp at hn
  exact ⟨(hnonneg n).1, (hnonneg n).2, heval n, hdegree n,
    (hnonneg n).1.pos_leadingCoeff hne⟩

/-- Adjacent rows strictly interleave; every row has simple, strictly negative roots; and
adjacent rows have no common root. -/
theorem interlacing_and_roots
    {P : ℕ → ℝ[X]} {p q : ℝ} {b c d : ℕ → ℝ}
    (hp : 0 < p) (hpq : p ≤ q)
    (hb : ∀ n, 0 ≤ b n) (hc : ∀ n, 0 ≤ c n) (hd : ∀ n, 0 < d n)
    (hP0 : P 0 = C p) (hP1 : P 1 = C q)
    (hrec : ∀ n, P (n + 2) =
      C (1 + b n + c n) * P (n + 1) + (C (d n) * X - C (b n)) * P n) :
    (∀ n, StrictInterl (P n) (P (n + 1))) ∧ (∀ n, HasSimpleRoots (P n)) ∧
      (∀ n r, (P n).IsRoot r → r < 0) ∧
      (∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) := by
  let A : ℕ → ℝ[X] := fun n ↦ C (1 + b n + c n)
  let B : ℕ → ℝ[X] := fun n ↦ C (d n) * X - C (b n)
  have hdata := coefficients_and_degree hp hpq hb hc hd hP0 hP1 hrec
  have hroots : ∀ n r, (P n).IsRoot r → r < 0 := by
    intro n r hr
    have hrle := isRoot_nonpos_of_hasNonnegCoeffs (hdata n).1
      (hdata n).2.2.2.2.ne_zero hr
    have hrne : r ≠ 0 := by
      intro hrzero
      subst r
      exact (hdata n).2.2.1.ne' hr.eq_zero
    exact lt_of_le_of_ne hrle hrne
  have hB_ne : ∀ n r, (P (n + 1)).IsRoot r → (B n).eval r ≠ 0 := by
    intro n r hr
    have hdr : d n * r < 0 := mul_neg_of_pos_of_neg (hd n) (hroots (n + 1) r hr)
    simp only [B, eval_sub, eval_mul, eval_C, eval_X]
    exact ne_of_lt (by linarith [hb n])
  have hbase : StrictInterl (P 0) (P 1) := by
    have hone := StrictInterl.refl (one_ne_zero : (1 : ℝ[X]) ≠ 0) (Splits.C 1)
    have hq : 0 < q := hp.trans_le hpq
    rw [hP0, hP1]
    simpa using (hone.C_mul_left hp.ne').C_mul_right hq.ne'
  have hno : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r := by
    apply threeTerm_not_isRoot_of_isRoot_succ (P := P) (a := A) (b := B) hrec hB_ne
    intro r hr
    rw [hP1, Polynomial.IsRoot.def] at hr
    simp [hp.trans_le hpq |>.ne'] at hr
  have hinter : ∀ n, StrictInterl (P n) (P (n + 1)) := by
    apply LiuWang.strictInterl_succ_of_recurrence_of_eval_nonpos
      (P := P) (A := A) (B := B) hbase (fun n ↦ (hdata n).2.2.2.2) hrec
    · intro n
      rw [(hdata (n + 1)).2.2.2.1, (hdata (n + 2)).2.2.2.1]
      lia
    · intro n
      rw [(hdata (n + 1)).2.2.2.1, (hdata (n + 2)).2.2.2.1]
      lia
    · intro n r hr
      have hdr : d n * r < 0 := mul_neg_of_pos_of_neg (hd n) (hroots (n + 1) r hr)
      simp only [B, eval_sub, eval_mul, eval_C, eval_X]
      linarith [hb n]
  have hsimple : ∀ n, HasSimpleRoots (P n) := by
    intro n
    exact ((hinter n).hasSimpleRoots_of_no_common_root fun r hrs ↦
      hno n r hrs.2 hrs.1).1
  exact ⟨hinter, hsimple, hroots, hno⟩

/-! ## A scaling-invariant form -/

/-- The ratio-weighted successive differences preserve coefficientwise nonnegativity. -/
private theorem ratio_coefficients_nonneg
    {P : ℕ → ℝ[X]} {p q rho : ℝ} {a b d : ℕ → ℝ}
    (hp : 0 < p) (hrho : 0 < rho) (hpq : rho * p ≤ q)
    (hb : ∀ n, 0 ≤ b n) (hd : ∀ n, 0 < d n)
    (ha : ∀ n, rho + b n / rho ≤ a n)
    (hP0 : P 0 = C p) (hP1 : P 1 = C q)
    (hrec : ∀ n, P (n + 2) =
      C (a n) * P (n + 1) + (C (d n) * X - C (b n)) * P n) :
    ∀ n, HasNonnegCoeffs (P n) ∧
      HasNonnegCoeffs (P (n + 1) - C rho * P n) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · simpa [hP0] using hasNonnegCoeffs_C hp.le
      · rw [hP0, hP1, ← map_mul, ← map_sub]
        exact hasNonnegCoeffs_C (sub_nonneg.mpr hpq)
  | succ n ih =>
      have hPn1 : HasNonnegCoeffs (P (n + 1)) := by
        rw [show P (n + 1) = C rho * P n +
          (P (n + 1) - C rho * P n) by ring]
        exact (hasNonnegCoeffs_C_mul hrho.le ih.1).add ih.2
      have hdiff : P (n + 2) - C rho * P (n + 1) =
          C (a n - rho - b n / rho) * P (n + 1) +
            C (b n / rho) * (P (n + 1) - C rho * P n) +
              (C (d n) * X) * P n := by
        have hC : C (b n / rho) * C rho = C (b n) := by
          rw [← map_mul]
          congr 1
          field_simp [hrho.ne']
        rw [hrec n]
        simp only [map_sub]
        rw [mul_sub, ← mul_assoc, hC]
        ring
      refine ⟨hPn1, ?_⟩
      rw [hdiff]
      exact ((hasNonnegCoeffs_C_mul (by linarith [ha n]) hPn1).add
        (hasNonnegCoeffs_C_mul (div_nonneg (hb n) hrho.le) ih.2)).add
          ((hasNonnegCoeffs_C (hd n).le).mul hasNonnegCoeffs_X |>.mul ih.1)

/-- The ratio barrier makes every constant term positive. -/
private theorem ratio_eval_zero_pos
    {P : ℕ → ℝ[X]} {p q rho : ℝ} {a b d : ℕ → ℝ}
    (hp : 0 < p) (hrho : 0 < rho) (hpq : rho * p ≤ q)
    (hb : ∀ n, 0 ≤ b n) (ha : ∀ n, rho + b n / rho ≤ a n)
    (hP0 : P 0 = C p) (hP1 : P 1 = C q)
    (hrec : ∀ n, P (n + 2) =
      C (a n) * P (n + 1) + (C (d n) * X - C (b n)) * P n) :
    ∀ n, 0 < (P n).eval 0 := by
  let A : ℕ → ℝ[X] := fun n ↦ C (a n)
  let B : ℕ → ℝ[X] := fun n ↦ C (d n) * X - C (b n)
  apply threeTermRatio_eval_zero_pos (P := P) (a := A) (b := B) (ρ := rho)
  · exact hrec
  · simpa [hP0] using hp
  · exact hrho
  · simpa [hP0, hP1] using hpq
  · intro n
    simp [B, hb n]
  · intro n
    have hcancel : rho * (b n / rho) = b n := by field_simp [hrho.ne']
    simp only [A, B, eval_C, eval_sub, eval_mul, eval_X, mul_zero, zero_sub]
    nlinarith [mul_le_mul_of_nonneg_left (ha n) hrho.le]

/-- The ratio hypotheses also force the exact half-growth degree schedule. -/
private theorem ratio_natDegree_eq_half
    {P : ℕ → ℝ[X]} {p q rho : ℝ} {a b d : ℕ → ℝ}
    (hp : 0 < p) (hrho : 0 < rho) (hpq : rho * p ≤ q)
    (hb : ∀ n, 0 ≤ b n) (hd : ∀ n, 0 < d n)
    (ha : ∀ n, rho + b n / rho ≤ a n)
    (hP0 : P 0 = C p) (hP1 : P 1 = C q)
    (hrec : ∀ n, P (n + 2) =
      C (a n) * P (n + 1) + (C (d n) * X - C (b n)) * P n) :
    ∀ n, (P n).natDegree = n / 2 := by
  let A : ℕ → ℝ[X] := fun n ↦ C (a n)
  let B : ℕ → ℝ[X] := fun n ↦ C (d n) * X - C (b n)
  have hq : 0 < q := lt_of_lt_of_le (mul_pos hrho hp) hpq
  intro n
  simpa [A, B] using threeTermHalf_natDegree (P := P) (a := A) (b := B)
    (d := 1) (D₀ := 0) (e := 0) hrec
    (fun n ↦ by simp [A]) (fun n ↦ by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · rw [natDegree_mul (C_ne_zero.mpr (hd n).ne') X_ne_zero]
        simp
      · simp) (by norm_num)
    (by simp [hP0]) (by simp [hP1]) (by simpa [hP0] using hp)
    (by simpa [hP1] using hq)
    (fun n ↦ by
      simpa [A] using (lt_of_lt_of_le hrho ((le_add_of_nonneg_right
        (div_nonneg (hb n) hrho.le)).trans (ha n))).le)
    (fun n ↦ by simp [B, hd n]) n

/-- Coefficient positivity, ratio-difference positivity, positive constant term, exact
degree, and positive leading coefficient under the scaling hypotheses. -/
theorem ratio_coefficients_and_degree
    {P : ℕ → ℝ[X]} {p q rho : ℝ} {a b d : ℕ → ℝ}
    (hp : 0 < p) (hrho : 0 < rho) (hpq : rho * p ≤ q)
    (hb : ∀ n, 0 ≤ b n) (hd : ∀ n, 0 < d n)
    (ha : ∀ n, rho + b n / rho ≤ a n)
    (hP0 : P 0 = C p) (hP1 : P 1 = C q)
    (hrec : ∀ n, P (n + 2) =
      C (a n) * P (n + 1) + (C (d n) * X - C (b n)) * P n) :
    ∀ n, HasNonnegCoeffs (P n) ∧ HasNonnegCoeffs (P (n + 1) - C rho * P n) ∧
      0 < (P n).eval 0 ∧ (P n).natDegree = n / 2 ∧ HasPosLeadingCoeff (P n) := by
  have hnonneg := ratio_coefficients_nonneg hp hrho hpq hb hd ha hP0 hP1 hrec
  have heval := ratio_eval_zero_pos hp hrho hpq hb ha hP0 hP1 hrec
  have hdegree := ratio_natDegree_eq_half hp hrho hpq hb hd ha hP0 hP1 hrec
  intro n
  have hne : P n ≠ 0 := by
    intro hzero
    have hn := heval n
    rw [hzero] at hn
    simp at hn
  exact ⟨(hnonneg n).1, (hnonneg n).2, heval n, hdegree n,
    (hnonneg n).1.pos_leadingCoeff hne⟩

/-- The scaling hypotheses imply adjacent strict interlacing, simple strictly negative roots,
and no common root between adjacent rows. -/
theorem ratio_interlacing_and_roots
    {P : ℕ → ℝ[X]} {p q rho : ℝ} {a b d : ℕ → ℝ}
    (hp : 0 < p) (hrho : 0 < rho) (hpq : rho * p ≤ q)
    (hb : ∀ n, 0 ≤ b n) (hd : ∀ n, 0 < d n)
    (ha : ∀ n, rho + b n / rho ≤ a n)
    (hP0 : P 0 = C p) (hP1 : P 1 = C q)
    (hrec : ∀ n, P (n + 2) =
      C (a n) * P (n + 1) + (C (d n) * X - C (b n)) * P n) :
    (∀ n, StrictInterl (P n) (P (n + 1))) ∧ (∀ n, HasSimpleRoots (P n)) ∧
      (∀ n r, (P n).IsRoot r → r < 0) ∧
      (∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) := by
  let A : ℕ → ℝ[X] := fun n ↦ C (a n)
  let B : ℕ → ℝ[X] := fun n ↦ C (d n) * X - C (b n)
  have hdata := ratio_coefficients_and_degree hp hrho hpq hb hd ha hP0 hP1 hrec
  have hroots : ∀ n r, (P n).IsRoot r → r < 0 := by
    intro n r hr
    have hrle := isRoot_nonpos_of_hasNonnegCoeffs (hdata n).1
      (hdata n).2.2.2.2.ne_zero hr
    have hrne : r ≠ 0 := by
      intro hrzero
      subst r
      exact (hdata n).2.2.1.ne' hr.eq_zero
    exact lt_of_le_of_ne hrle hrne
  have hB_ne : ∀ n r, (P (n + 1)).IsRoot r → (B n).eval r ≠ 0 := by
    intro n r hr
    have hdr : d n * r < 0 := mul_neg_of_pos_of_neg (hd n) (hroots (n + 1) r hr)
    simp only [B, eval_sub, eval_mul, eval_C, eval_X]
    exact ne_of_lt (by linarith [hb n])
  have hbase : StrictInterl (P 0) (P 1) := by
    have hone := StrictInterl.refl (one_ne_zero : (1 : ℝ[X]) ≠ 0) (Splits.C 1)
    have hq : 0 < q := lt_of_lt_of_le (mul_pos hrho hp) hpq
    rw [hP0, hP1]
    simpa using (hone.C_mul_left hp.ne').C_mul_right hq.ne'
  have hno : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r := by
    apply threeTerm_not_isRoot_of_isRoot_succ (P := P) (a := A) (b := B) hrec hB_ne
    intro r hr
    rw [hP1, Polynomial.IsRoot.def] at hr
    simp [lt_of_lt_of_le (mul_pos hrho hp) hpq |>.ne'] at hr
  have hinter : ∀ n, StrictInterl (P n) (P (n + 1)) := by
    apply LiuWang.strictInterl_succ_of_recurrence_of_eval_nonpos
      (P := P) (A := A) (B := B) hbase (fun n ↦ (hdata n).2.2.2.2) hrec
    · intro n
      rw [(hdata (n + 1)).2.2.2.1, (hdata (n + 2)).2.2.2.1]
      lia
    · intro n
      rw [(hdata (n + 1)).2.2.2.1, (hdata (n + 2)).2.2.2.1]
      lia
    · intro n r hr
      have hdr : d n * r < 0 := mul_neg_of_pos_of_neg (hd n) (hroots (n + 1) r hr)
      simp only [B, eval_sub, eval_mul, eval_C, eval_X]
      linarith [hb n]
  have hsimple : ∀ n, HasSimpleRoots (P n) := by
    intro n
    exact ((hinter n).hasSimpleRoots_of_no_common_root fun r hrs ↦
      hno n r hrs.2 hrs.1).1
  exact ⟨hinter, hsimple, hroots, hno⟩

end RealRooted.PositiveAffineLag
