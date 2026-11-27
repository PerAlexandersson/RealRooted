/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.BetaMoments
import Mathlib.Tactic

/-!
# Quantitative local and tail bounds for radial moments

We collect the exact envelope arithmetic with the integral comparisons it serves.
The normalization ratio and the tail bound use the exact tilt recurrence.

Source: ProgramComputer, *Strict peaks in Catalan words*, analytic proof,
ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
-/

@[expose] public noncomputable section

namespace RealRooted.CatalanWordPeaks.CutBounds

/-- The rational estimate at the right of the short-range beta-moment bound. -/
theorem near_moment_bound {n : ℝ} (hn : 150 ≤ n) :
    (2 * n / 5 + 9) * ((3 / 2) / (n - 3 / 2)) +
      (2 * n / 5 + 4 / 5) * ((15 / 4) / ((n - 3 / 2) * (n - 5 / 2))) < 71 / 100 := by
  have h₁ : 0 < n - 3 / 2 := by linarith
  have h₂ : 0 < n - 5 / 2 := by linarith
  have hc₁ : ((3 / 2 : ℝ) / (n - 3 / 2)) * ((n - 3 / 2) * (n - 5 / 2)) =
      (3 / 2) * (n - 5 / 2) := by
    rw [← mul_assoc, div_mul_cancel₀ _ h₁.ne']
  have hc₂ : ((15 / 4 : ℝ) / ((n - 3 / 2) * (n - 5 / 2))) *
      ((n - 3 / 2) * (n - 5 / 2)) = 15 / 4 := div_mul_cancel₀ _ (mul_pos h₁ h₂).ne'
  apply (mul_lt_mul_iff_of_pos_right (mul_pos h₁ h₂)).mp
  rw [add_mul, mul_assoc (2 * n / 5 + 9), mul_assoc (2 * n / 5 + 4 / 5), hc₁, hc₂]
  nlinarith [sq_nonneg (n - 150)]

/-- n minus the least integer at least n/4. -/
def cutExponent (n : ℕ) : ℕ := n - (n + 3) / 4

/-- Advancing four lengths advances the tail exponent by three. -/
theorem cutExponent_add_four (n : ℕ) : cutExponent (n + 4) = cutExponent n + 3 := by
  unfold cutExponent
  lia

/-- The tail cost before comparison against a fixed rational bound. -/
def tailScore (p : ℕ) (q : ℝ) (n : ℕ) : ℝ :=
  60 * (n : ℝ) ^ p * q ^ cutExponent n

private theorem tailScore_step {p : ℕ} {q : ℝ} (hq : 0 ≤ q)
    (hloss : (154 / 150 : ℝ) ^ p * q ^ 3 ≤ 1) {n : ℕ} (hn : 150 ≤ n) :
    tailScore p q (n + 4) ≤ tailScore p q n := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hratio : ((n : ℝ) + 4) ≤ (154 / 150 : ℝ) * (n : ℝ) := by linarith
  unfold tailScore
  rw [cutExponent_add_four, pow_add, Nat.cast_add, Nat.cast_ofNat]
  have hpow := pow_le_pow_left₀ (show 0 ≤ (n : ℝ) + 4 by positivity) hratio p
  calc
    _ ≤ 60 * ((154 / 150 : ℝ) * (n : ℝ)) ^ p * (q ^ cutExponent n * q ^ 3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by positivity)
    _ = (60 * (n : ℝ) ^ p * q ^ cutExponent n) * ((154 / 150 : ℝ) ^ p * q ^ 3) := by
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hloss

private theorem tailScore_control {p : ℕ} {q bound : ℝ} (hq : 0 ≤ q)
    (hloss : (154 / 150 : ℝ) ^ p * q ^ 3 ≤ 1)
    (hbase : ∀ n, 150 ≤ n → n < 154 → tailScore p q n < bound)
    (n : ℕ) (hn : 150 ≤ n) : tailScore p q n < bound := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases h : n < 154
    · exact hbase n hn h
    · let m := n - 4
      have hmn : m < n := by lia
      have hm : 150 ≤ m := by lia
      have heq : n = m + 4 := by lia
      calc
        tailScore p q n = tailScore p q (m + 4) := by rw [← heq]
        _ ≤ tailScore p q m := tailScore_step hq hloss hm
        _ < bound := ih m hmn hm

/-- The exponential tail estimate for displacement at least one eighth. -/
theorem near_tail_bound (n : ℕ) (hn : 150 ≤ n) :
    tailScore 1 (8 / 9) n < 1 / 50 := by
  apply tailScore_control (by norm_num) (by norm_num) _ n hn
  intro k hk hK
  have h : k = 150 ∨ k = 151 ∨ k = 152 ∨ k = 153 := by lia
  rcases h with rfl | rfl | rfl | rfl <;> norm_num [tailScore, cutExponent]

/-- The exponential tail estimate, multiplied by n, for the covariance bound. -/
theorem covariance_tail_bound (n : ℕ) (hn : 150 ≤ n) :
    tailScore 2 (6 / 7) n < 1 / 20 := by
  apply tailScore_control (by norm_num) (by norm_num) _ n hn
  intro k hk hK
  have h : k = 150 ∨ k = 151 ∨ k = 152 ∨ k = 153 := by lia
  rcases h with rfl | rfl | rfl | rfl <;> norm_num [tailScore, cutExponent]

end RealRooted.CatalanWordPeaks.CutBounds

namespace RealRooted.CatalanWordPeaks.BetaMoments

open Set MeasureTheory Function

/-- Changing the size multiplies the unnormalized density by a power of
`(1+s)⁻¹`, the tilt factor used in the moment and tail arguments. -/
theorem rayWeight_shift {N n : ℕ} (h : N ≤ n) (s : ℝ) :
    rayWeight n s = rayWeight N s * ((1 + s)⁻¹) ^ (n - N) := by
  rw [rayWeight, rayWeight, inv_pow, ← div_eq_mul_inv, div_div, ← pow_add,
    show N + 1 + (n - N) = n + 1 by lia]

/-- The expectation of the one-step tilt factor, as in (8). -/
theorem tilt_mean {n : ℕ} (hn : 0 < n) :
    (∫ s in Ioi (0 : ℝ), (1 + s)⁻¹ * rayWeight n s) / mass n =
      ((n : ℝ) - 1 / 2) / ((n : ℝ) + 1) := by
  have hd (s : ℝ) : (1 + s)⁻¹ * rayWeight n s = rayWeight (n + 1) s := by
    rw [rayWeight_shift (Nat.le_succ n), show n.succ - n = 1 by lia, pow_one, mul_comm]
  simp_rw [hd]
  rw [← mass, mass_succ hn, mul_div_cancel_right₀ _ (mass_pos hn).ne']

private theorem scaledMass_monotone :
    Monotone (fun n : ℕ => (n : ℝ) ^ 2 * mass n) := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using (mass_pos (n := 1) (by decide)).le
  · have hnN : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
    apply sub_nonneg.mp
    change 0 ≤ (((n + 1 : ℕ) : ℝ) ^ 2 * mass (n + 1)) - ((n : ℝ) ^ 2 * mass n)
    rw [mass_succ hnN, Nat.cast_add, Nat.cast_one,
      show ((n : ℝ) + 1) ^ 2 * (((n : ℝ) - 1 / 2) / ((n : ℝ) + 1) * mass n) -
          (n : ℝ) ^ 2 * mass n = (((n : ℝ) - 1) / 2) * mass n by
        have hnp : 0 < (n : ℝ) + 1 := by positivity
        field_simp [hnp.ne']
        ring]
    exact mul_nonneg (div_nonneg (sub_nonneg.mpr hnR) (by norm_num)) (mass_pos hnN).le

/-- A ratio bound for the normalizations. It follows directly from the exact
tilt recurrence, without asymptotics for the beta function. -/
theorem mass_ratio_le {N n : ℕ} (hN : 0 < N) (hNn : N ≤ n) :
    mass N / mass n ≤ ((n : ℝ) / (N : ℝ)) ^ 2 := by
  have hn : 0 < n := hN.trans_le hNn
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNpow : 0 < (N : ℝ) ^ 2 := pow_pos hNr 2
  rw [div_pow]
  apply (div_le_div_iff₀ (mass_pos hn) hNpow).2
  simpa only [mul_comm] using scaledMass_monotone hNn

/-- The radial weight is nonnegative on the ray. -/
theorem rayWeight_nonneg (n : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ rayWeight n s := by
  unfold rayWeight
  positivity

/-- Integrability and exact integral for an affine function times the radial weight. -/
theorem affine_moment {n : ℕ} (hn : (3 / 2 : ℝ) < (n : ℝ)) (A B : ℝ) :
    IntegrableOn (fun s => (A + B * s) * rayWeight n s) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), (A + B * s) * rayWeight n s) =
        mass n * (A + B * moment n 1) := by
  have h₀ : (((0 : ℕ) : ℝ)) + 1 / 2 < (n : ℝ) := by norm_num; linarith
  have h₁ : (((1 : ℕ) : ℝ)) + 1 / 2 < (n : ℝ) := by norm_num; linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith
  have hnNat : 0 < n := by exact_mod_cast hnR
  have hw₀ : IntegrableOn (rayWeight n) (Ioi 0) := by
    simpa using integrableOn_moment h₀
  have hw₁ : IntegrableOn (fun s => s * rayWeight n s) (Ioi 0) := by
    simpa using integrableOn_moment h₁
  have hA : IntegrableOn (fun s => A * rayWeight n s) (Ioi 0) := hw₀.const_mul A
  have hB : IntegrableOn (fun s => B * (s * rayWeight n s)) (Ioi 0) := hw₁.const_mul B
  simp_rw [add_mul, mul_assoc B]
  refine ⟨hA.add hB, ?_⟩
  rw [integral_add hA hB, integral_const_mul, integral_const_mul, ← mass,
    show (∫ s in Ioi (0 : ℝ), s * rayWeight n s) = rawMoment n 1 by simp [rawMoment]]
  rw [moment]
  field_simp [(mass_pos hnNat).ne']

/-- The tail comparison before bounding the normalizing ratio and the first
moment at the tilted size. This applies to any nonnegative affine envelope. -/
theorem affine_tail_le {n N : ℕ} {r A B : ℝ} (hN : (3 / 2 : ℝ) < (N : ℝ)) (hNn : N ≤ n)
    (hr : 0 ≤ r) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∫ s in Ioi r, (A + B * s) * rayWeight n s) / mass n ≤
      mass N / mass n * (A + B * moment N 1) * ((1 + r)⁻¹) ^ (n - N) := by
  have hNnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith
  have hn : 0 < n := by exact_mod_cast hnR
  let Q : ℝ := ((1 + r)⁻¹) ^ (n - N)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hi := affine_moment hN A B
  have sub : Ioi r ⊆ Ioi 0 := Ioi_subset_Ioi hr
  have hf : IntegrableOn (fun s => (A + B * s) * rayWeight n s) (Ioi r) :=
    (affine_moment (by linarith : (3 / 2 : ℝ) < (n : ℝ)) A B).1.mono_set sub
  have hg : IntegrableOn (fun s => Q * ((A + B * s) * rayWeight N s)) (Ioi r) :=
    (hi.1.mono_set sub).const_mul Q
  have hcomparison := setIntegral_mono_on hf hg measurableSet_Ioi (fun s hs => by
    have hs' : r < s := hs
    have hs0 : 0 ≤ s := hr.trans hs'.le
    have hsum : 0 < 1 + s := by positivity
    have hbase : (1 + s)⁻¹ ≤ (1 + r)⁻¹ :=
      (inv_le_inv₀ hsum (by positivity)).mpr (by linarith)
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + s)⁻¹) hbase (n - N)
    rw [rayWeight_shift hNn s, ← mul_assoc]
    rw [mul_comm Q]
    exact mul_le_mul_of_nonneg_left hpow (mul_nonneg (by positivity)
      (rayWeight_nonneg N hs0)))
  have hfull : (∫ s in Ioi r, (A + B * s) * rayWeight N s) ≤
      ∫ s in Ioi (0 : ℝ), (A + B * s) * rayWeight N s := by
    apply setIntegral_mono_set hi.1 _ (Filter.Eventually.of_forall sub)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 ≤ s := (mem_Ioi.mp hs).le
    exact mul_nonneg (by positivity) (rayWeight_nonneg N hs0)
  rw [integral_const_mul] at hcomparison
  calc
    _ ≤ Q * (∫ s in Ioi r, (A + B * s) * rayWeight N s) / mass n :=
      div_le_div_of_nonneg_right hcomparison (mass_pos hn).le
    _ ≤ Q * (∫ s in Ioi (0 : ℝ), (A + B * s) * rayWeight N s) / mass n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfull hQ) (mass_pos hn).le
    _ = _ := by rw [hi.2]; dsimp [Q]; ring

/-- The normalized integral of the common affine tail envelope in (6) and (11). -/
theorem ray_tail_le {n : ℕ} (hn : 150 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    (∫ s in Ioi r, ((2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8)) * rayWeight n s) /
      mass n ≤ 60 * (n : ℝ) * ((1 + r)⁻¹) ^ CutBounds.cutExponent n := by
  let N := (n + 3) / 4
  have hNn : N ≤ n := by dsimp [N]; lia
  have hN : 2 ≤ N := by dsimp [N]; lia
  have h4N : n ≤ 4 * N := by dsimp [N]; lia
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h4N' : (n : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast h4N
  have hn' : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNr : 0 < (N : ℝ) := by linarith
  have hfirst : (3 / 2 : ℝ) < (N : ℝ) := by linarith
  let A : ℝ := 2 * (n : ℝ) + 1
  let B : ℝ := A * (n : ℝ) / 8
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hM₁ : 0 ≤ moment N 1 := by
    rw [moment_one hfirst]
    exact div_nonneg (by norm_num) (by linarith)
  have hratio : mass N / mass n ≤ 16 := by
    have hdiv : (n : ℝ) / (N : ℝ) ≤ 4 := (div_le_iff₀ hNr).2 h4N'
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) / (N : ℝ)) hdiv 2
    norm_num at hpow
    exact (mass_ratio_le (by lia) hNn).trans hpow
  have hmoment : (n : ℝ) / 8 * moment N 1 ≤ 4 / 5 := by
    rw [moment_one hfirst, ← mul_div_assoc]
    exact (div_le_iff₀ (by linarith : (0 : ℝ) < (N : ℝ) - 3 / 2)).2 (by linarith)
  have hlin s : (2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8) = A + B * s := by
    dsimp [A, B]
    ring
  simp_rw [hlin]
  have hcoeff : A + B * moment N 1 ≤ A * (1 + 4 / 5) := by
    calc
      _ = A * (1 + (n : ℝ) / 8 * moment N 1) := by dsimp [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hA
  have hprod : (mass N / mass n) * (A + B * moment N 1) ≤ 60 * (n : ℝ) := by
    calc
      _ ≤ 16 * (A + B * moment N 1) := mul_le_mul_of_nonneg_right hratio (by positivity)
      _ ≤ 16 * (A * (1 + 4 / 5)) := mul_le_mul_of_nonneg_left hcoeff (by norm_num)
      _ ≤ _ := by dsimp [A]; linarith
  exact (affine_tail_le hfirst hNn hr hA hB).trans
    (mul_le_mul_of_nonneg_right hprod (by positivity))

/-- The integral tail after displacement one eighth is less than `1/50`. -/
theorem near_tail_integral_bound {n : ℕ} (hn : 150 ≤ n) :
    (∫ s in Ioi (1 / 8 : ℝ), ((2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8)) *
      rayWeight n s) / mass n < 1 / 50 := by
  apply (ray_tail_le hn (show (0 : ℝ) ≤ 1 / 8 by norm_num)).trans_lt
  rw [show (1 + 1 / 8 : ℝ)⁻¹ = 8 / 9 by norm_num]
  simpa [CutBounds.tailScore] using CutBounds.near_tail_bound n hn

/-- The integral tail after displacement one sixth is less than `1/(20n)`. -/
theorem covariance_tail_integral_bound {n : ℕ} (hn : 150 ≤ n) :
    (∫ s in Ioi (1 / 6 : ℝ), ((2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8)) *
      rayWeight n s) / mass n < 1 / (20 * (n : ℝ)) := by
  apply (ray_tail_le hn (show (0 : ℝ) ≤ 1 / 6 by norm_num)).trans_lt
  rw [show (1 + 1 / 6 : ℝ)⁻¹ = 6 / 7 by norm_num, ← div_div]
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply (lt_div_iff₀ (by linarith : 0 < (n : ℝ))).2
  convert CutBounds.covariance_tail_bound n hn using 1
  unfold CutBounds.tailScore
  ring

/-- The local quadratic envelope from (5), integrated against the actual
radial density up to displacement one eighth. -/
theorem near_local_integral_bound {n : ℕ} (hn : 150 ≤ n) :
    IntegrableOn (fun s : ℝ =>
      ((2 * (n : ℝ) / 5 + 9) * s + (2 * (n : ℝ) / 5 + 4 / 5) * s ^ 2) * rayWeight n s)
      (Ioc 0 (1 / 8)) ∧
    (∫ s in Ioc (0 : ℝ) (1 / 8),
      ((2 * (n : ℝ) / 5 + 9) * s + (2 * (n : ℝ) / 5 + 4 / 5) * s ^ 2) * rayWeight n s) /
        mass n < 71 / 100 := by
  have hnN : 0 < n := by lia
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h₁ : (((1 : ℕ) : ℝ)) + 1 / 2 < (n : ℝ) := by norm_num; linarith
  have h₂ : (((2 : ℕ) : ℝ)) + 1 / 2 < (n : ℝ) := by norm_num; linarith
  let A : ℝ := 2 * n / 5 + 9
  let B : ℝ := 2 * n / 5 + 4 / 5
  let F (s : ℝ) := A * (s ^ (1 : ℕ) * rayWeight n s) + B * (s ^ (2 : ℕ) * rayWeight n s)
  have hA := (integrableOn_moment h₁).const_mul A
  have hB := (integrableOn_moment h₂).const_mul B
  have hF : IntegrableOn F (Ioi 0) := hA.add hB
  have hle : (∫ s in Ioc (0 : ℝ) (1 / 8), F s) ≤ ∫ s in Ioi (0 : ℝ), F s := by
    apply setIntegral_mono_set hF _ (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : 0 ≤ s := (mem_Ioi.mp hs).le
    have hweight := rayWeight_nonneg n hs'
    dsimp [F, A, B]
    positivity
  have hpoint s : (A * s + B * s ^ 2) * rayWeight n s = F s := by
    simp only [F, pow_one]
    ring
  refine ⟨(hF.mono_set Ioc_subset_Ioi_self).congr_fun
    (fun s _ => (hpoint s).symm) measurableSet_Ioc, ?_⟩
  change (∫ s in Ioc (0 : ℝ) (1 / 8), (A * s + B * s ^ 2) * rayWeight n s) /
    mass n < _
  simp_rw [hpoint]
  apply (div_le_div_of_nonneg_right hle (mass_pos hnN).le).trans_lt
  dsimp only [F]
  rw [integral_add hA hB, integral_const_mul, integral_const_mul, ← rawMoment, ← rawMoment,
    add_div, mul_div_assoc, mul_div_assoc, ← moment, ← moment,
    moment_one (by linarith), moment_two (by linarith)]
  exact CutBounds.near_moment_bound hnR

end RealRooted.CatalanWordPeaks.BetaMoments
