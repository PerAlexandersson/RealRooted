/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.Phase
public import RealRooted.CombinatorialExamples.CatalanWordPeaks.CutGeometry
public import Mathlib.Algebra.Polynomial.Derivative
import RealRooted.CombinatorialExamples.CatalanWordPeaks.PhaseSigns
public import RealRooted.CombinatorialExamples.CatalanWordPeaks.Basic
import RealRooted.CombinatorialExamples.CatalanWordPeaks.PoleEstimates
import RealRooted.RootCounting.SignChanges
import Mathlib.Order.Fin.Tuple
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Root selection from the actual phase checkpoints

The positive pole endpoint replaces word-model positivity at zero. Mathlib's
interval roots and the standard root multiset provide the complete enumeration.

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

public noncomputable section

namespace RealRooted.CatalanWordPeaks.CutGeometry

open Real Set Polynomial

private theorem scale_le_transition {d : ℝ} (hd : 0 < d) (hD : d ≤ 1) :
    scale d ≤ scale 1 * ((1 + d) / 2) := by
  have hp : 0 < 1 + 2 * d := by positivity
  have hf : d / (1 + 2 * d) ≤ 1 / 3 :=
    (div_le_iff₀ hp).2 (by linarith)
  have hr : sqrt (1 + 2 * d) ≤ sqrt 3 := sqrt_le_sqrt (by linarith)
  rw [scale_eq_product hd]
  calc
    _ ≤ 2 * (1 / 3 : ℝ) ^ 2 * (1 + d) * sqrt 3 := by gcongr
    _ = _ := by rw [scale_eq_product (by norm_num : (0 : ℝ) < 1)]; norm_num; ring

/-- The modulus increases by at least the decrease of the cosine from
its value at the transition. -/
private theorem modulus_sub_transition_ge_one_sub_cos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    1 - cos θ ≤ modulus θ - 11 / 16 := by
  let d := cos θ
  have ⟨hd, hD⟩ : 0 < d ∧ d < 1 := cosine_in_unit hθ
  have hc : 0 < scale d := scale_pos (d := d) hd
  have ht := scale_pos (d := 1) (by norm_num)
  have hcsq : scale d ^ 2 ≤ (4 / 27 : ℝ) * (1 + d) ^ 2 := calc
    _ ≤ (scale 1 * ((1 + d) / 2)) ^ 2 :=
      (sq_le_sq₀ hc.le (by positivity)).2 (scale_le_transition hd hD.le)
    _ = _ := by rw [mul_pow, scale_one_sq]; ring
  have hrec : 1 / ((4 / 27 : ℝ) * (1 + d) ^ 2) ≤ 1 / (scale d ^ 2) :=
    one_div_le_one_div_of_le (pow_pos hc 2) hcsq
  have hpos : 0 < (1 + d) ^ 2 := by positivity
  have hdd : d ^ 2 ≤ d := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hD.le)]
  have hcoeff : (1 + d) ^ 2 ≤ (27 / 16 : ℝ) * (3 + d) := by nlinarith
  have hdsub : 0 ≤ 1 - d := sub_nonneg.mpr hD.le
  have hnum := mul_le_mul_of_nonneg_right hcoeff hdsub
  change 1 - d ≤ (scale d ^ 2)⁻¹ - 1 - 11 / 16
  calc
    _ ≤ (27 / 16 : ℝ) * (1 - d) * (3 + d) / (1 + d) ^ 2 :=
      (le_div_iff₀ hpos).2 (by
        calc
          _ = (1 + d) ^ 2 * (1 - d) := by ring
          _ ≤ (27 / 16 : ℝ) * (3 + d) * (1 - d) := hnum
          _ = _ := by ring)
    _ = 1 / ((4 / 27 : ℝ) * (1 + d) ^ 2) - 1 - 11 / 16 := by
      field_simp [(show 0 < 1 + d by positivity).ne']
      ring
    _ ≤ _ := by
      rw [inv_eq_one_div]
      exact sub_le_sub_right (sub_le_sub_right hrec 1) (11 / 16)

private theorem one_sub_cos_ge_inv_sq {θ : ℝ} {n : ℕ} (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (hn : 150 ≤ n) (hangle : (2 : ℝ) / (n : ℝ) ≤ θ) :
    (1 : ℝ) / (n : ℝ) ^ 2 < 1 - cos θ := by
  let u := (1 : ℝ) / (n : ℝ)
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnP : 0 < (n : ℝ) := by linarith
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := (div_le_one hnP).2 (by linarith)
  have huθ : u ≤ θ / 2 := by
    have heq : (2 : ℝ) / (n : ℝ) = 2 * u := by dsimp [u]; ring
    rw [heq] at hangle
    linarith
  have hsin₁ : (3 / 4 : ℝ) * u ≤ sin (θ / 2) := calc
    _ ≤ u - u ^ 3 / 4 := by
      nlinarith [mul_le_of_le_one_left (sq_nonneg u) hu1,
        mul_le_of_le_one_right hu.le hu1]
    _ ≤ sin u := (sin_gt_sub_cube hu).le.trans' (by nlinarith [pow_nonneg hu.le 3])
    _ ≤ _ := sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [pi_pos]) (by linarith [hθ.2, pi_pos]) huθ
  have hsin₂ : ((3 / 4 : ℝ) * u) ^ 2 ≤ sin (θ / 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) ((by positivity : (0 : ℝ) ≤ (3 / 4 : ℝ) * u).trans hsin₁)).2 hsin₁
  have hC := cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hC
  have h : (1 : ℝ) / (n : ℝ) ^ 2 = u ^ 2 := by dsimp [u]; rw [div_pow, one_pow]
  rw [h]
  nlinarith [sin_sq_add_cos_sq (θ / 2), pow_pos hu 2]

private theorem checkpoint_modulus_gap {θ : ℝ} {n : ℕ} (hn : 150 ≤ n)
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) (hfirst : π ≤ checkpointPhase n θ) :
    (11 / 16 : ℝ) + 1 / (n : ℝ) ^ 2 < modulus θ := by
  have hγ := (phaseCorrection_bounds ⟨hθ.1.le, hθ.2.le⟩).1
  unfold checkpointPhase at hfirst
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnP : 0 < (n : ℝ) := by linarith
  have hangle : (2 : ℝ) / (n : ℝ) ≤ θ :=
    (div_le_iff₀ hnP).2 (by linarith [pi_gt_three])
  linarith [one_sub_cos_ge_inv_sq hθ hn hangle, modulus_sub_transition_ge_one_sub_cos hθ]

private theorem phase_nodes {n : ℕ} (hn : 150 ≤ n) :
    ∃ θ : Fin (rowDegree n - 1) → ℝ, StrictMono θ ∧
      (∀ i, θ i ∈ Ioo (0 : ℝ) (π / 2)) ∧
      ∀ i, checkpointPhase n (θ i) = ((i.val : ℝ) + 1) * π := by
  have hm : 2 * (rowDegree n - 1) + 3 ≤ n := by unfold rowDegree; lia
  have hmR : 2 * ((rowDegree n - 1 : ℕ) : ℝ) + 3 ≤ n := by exact_mod_cast hm
  have hlevels (i : Fin (rowDegree n - 1)) :
      ∃ t ∈ Ioo (0 : ℝ) (π / 2), checkpointPhase n t = ((i.val : ℝ) + 1) * π := by
    have hi : (i.val : ℝ) + 1 ≤ ((rowDegree n - 1 : ℕ) : ℝ) := by
      exact_mod_cast i.isLt
    have hlo : checkpointPhase n 0 < ((i.val : ℝ) + 1) * π := by
      rw [checkpointPhase, phaseCorrection_zero]
      nlinarith [pi_pos, Nat.cast_nonneg (α := ℝ) i.val]
    have hhi : ((i.val : ℝ) + 1) * π < checkpointPhase n (π / 2) := by
      rw [checkpointPhase, phaseCorrection_pi_div_two]
      nlinarith [pi_pos, mul_nonneg (sub_nonneg.mpr hi) pi_pos.le,
        mul_nonneg (sub_nonneg.mpr hmR) pi_pos.le]
    exact intermediate_value_Ioo (by linarith [pi_pos]) (continuousOn_checkpointPhase n)
      ⟨hlo, hhi⟩
  choose θ hθ heval using hlevels
  refine ⟨θ, ?_, hθ, heval⟩
  intro i j hij
  apply (checkpointPhase_strictMonoOn (n := n) (by lia)).lt_iff_lt
    ⟨(hθ i).1.le, (hθ i).2.le⟩ ⟨(hθ j).1.le, (hθ j).2.le⟩ |>.mp
  rw [heval, heval]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast (show i.val + 1 < j.val + 1 by lia)) pi_pos

private theorem signed_grid_roots {p : ℝ[X]} {m : ℕ} (hp : p ≠ 0)
    (hdeg : p.natDegree = m + 1) (hlc : 0 < p.leadingCoeff)
    (q : Fin m → ℝ) (hq : StrictMono q) {t : ℝ}
    (hqt : ∀ i, t < q i) (hzero : 0 < p.eval (-t))
    (hsign : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * p.eval (-q i)) :
    ∃ r : Fin (m + 1) → ℝ, StrictMono r ∧ (∀ i, t < r i) ∧
      (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = p.roots ∧ p.Splits ∧
      (∀ i : Fin m, q i < r i.succ) ∧ (∀ i : Fin m, r i.castSucc < q i) := by
  classical
  let bound := max t (if hm : m = 0 then t else q ⟨m - 1, by lia⟩)
  obtain ⟨L, hL, hLs⟩ := RealRooted.exists_left_endpoint_sign hdeg hlc (-bound)
  have hqL (i : Fin m) : q i < -L := by
    have hm : m ≠ 0 := by have := i.isLt; lia
    have hi : i ≤ (⟨m - 1, by lia⟩ : Fin m) := by have := i.isLt; change i.val ≤ m - 1; lia
    have hmax : q i ≤ bound := (hq.monotone hi).trans (by simp [bound, hm])
    linarith
  have htL : t < -L := by
    have : t ≤ bound := le_max_left _ _
    linarith
  let y : Fin (m + 1) → ℝ := Fin.snoc q (-L)
  have hy : StrictMono y := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    dsimp only [y]
    rw [Fin.snoc_castSucc]
    by_cases hi : i.val + 1 = m
    · rw [show i.succ = Fin.last m from Fin.ext hi, Fin.snoc_last]
      exact hqL i
    · let j : Fin m := ⟨i.val + 1, by have := i.isLt; lia⟩
      rw [show i.succ = j.castSucc from Fin.ext rfl, Fin.snoc_castSucc]
      exact hq (show i < j from Nat.lt_succ_self _)
  let x : Fin (m + 2) → ℝ := Fin.cons t y
  have hx : StrictMono x := Fin.strictMono_cons.mpr ⟨(fun j => by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa [y] using htL
    · simpa [y] using hqt j), hy⟩
  have hxs (i : Fin (m + 2)) : 0 < (-1 : ℝ) ^ i.val * p.eval (-x i) := by
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [x] using hzero
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa [x, y, hdeg] using hLs
      · simpa [x, y] using hsign i
  let P := p.comp (-X)
  have hp0 : P ≠ 0 := by simpa [P] using hp
  have hPd : P.natDegree ≤ m + 1 := by
    simpa [P, hdeg] using (natDegree_comp_le (p := p) (q := -X))
  obtain ⟨r, hr, hb, heq, hs, _⟩ := roots_of_intervals hp0 hPd
    (fun i => x i.castSucc) (fun i => x i.succ)
    (fun i => hx i.castSucc_lt_succ)
    (fun i j hij => hx.monotone (show i.succ ≤ j.castSucc from hij)) (by
      intro i
      have ha := hxs i.castSucc
      have hb := hxs i.succ
      simp only [Fin.val_castSucc, Fin.val_succ, pow_succ] at ha hb
      rcases neg_one_pow_eq_or ℝ i.val with h | h <;>
        simp only [h, one_mul, neg_mul, neg_neg] at ha hb <;>
        simpa only [P, eval_comp, eval_neg, eval_X] using
          (by nlinarith : p.eval (-x i.castSucc) * p.eval (-x i.succ) < 0))
  have hmapped := congrArg (Multiset.map (fun a : ℝ => -a)) heq
  simp only [P, roots_comp_neg_X, Multiset.map_map] at hmapped
  have hrmap : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = p.roots := by
    simpa only [Multiset.map_coe, List.map_ofFn, Function.comp_def, neg_neg,
      Multiset.map_id'] using hmapped
  have hcard : p.roots.card = p.natDegree := by
    rw [← hrmap, Multiset.coe_card, List.length_ofFn, hdeg]
  refine ⟨r, hr, (fun i => (hx.monotone (Fin.zero_le _)).trans_lt (hb i).1),
    hrmap, splits_iff_card_roots.mpr hcard, ?_, ?_⟩
  · intro i
    simpa [x, y] using (hb i.succ).1
  · intro i
    simpa [x, y] using (hb i.castSucc).2

private theorem continuousOn_modulus : ContinuousOn modulus (Ioo (0 : ℝ) (π / 2)) := by
  have hcos : ContinuousOn cos (Ioo (0 : ℝ) (π / 2)) := continuous_cos.continuousOn
  have hA : ContinuousOn (fun x => 1 + 2 * cos x) (Ioo (0 : ℝ) (π / 2)) :=
    continuousOn_const.add (continuousOn_const.mul hcos)
  have hroot := continuous_sqrt.comp_continuousOn hA
  have har : ContinuousOn (fun x => radius (cos x)) (Ioo (0 : ℝ) (π / 2)) := by
    unfold radius
    apply hroot.inv₀
    intro x hx
    have hp : 0 < 1 + 2 * cos x := by linarith [(cosine_in_unit hx).1]
    exact (sqrt_pos.2 hp).ne'
  have hScale : ContinuousOn (fun x => scale (cos x)) (Ioo (0 : ℝ) (π / 2)) := by
    unfold scale
    exact (((continuousOn_const.mul (hcos.pow 2)).mul
      (continuousOn_const.add hcos)).mul (har.pow 3))
  unfold modulus
  exact ((hScale.pow 2).inv₀ (fun x hx => (pow_pos (scale_pos (cosine_in_unit hx).1) 2).ne')).sub
    continuousOn_const

/-- The actual rows have complete increasing root magnitudes, interior phase bands,
and the transition separation needed for the closest-root comparison. -/
theorem roots_from_150 {n : ℕ} (hn : 150 ≤ n) :
    ∃ r : Fin (rowDegree n) → ℝ, StrictMono r ∧
      (∀ i, (11 / 16 : ℝ) < r i) ∧
      (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = (polynomial n).roots ∧
      (polynomial n).Splits ∧
      (∀ i, 0 < i.val → i.val + 1 < rowDegree n →
        ∃ θ ∈ Ioo (0 : ℝ) (π / 2), r i = modulus θ ∧
          (i.val : ℝ) * π < checkpointPhase n θ ∧
          checkpointPhase n θ < ((i.val : ℝ) + 1) * π) ∧
      ∀ i, 0 < i.val → (11 / 16 : ℝ) + 1 / (n : ℝ) ^ 2 < r i := by
  let m := rowDegree n - 1
  have hd : rowDegree n = m + 1 := by dsimp [m]; unfold rowDegree; lia
  obtain ⟨θ, hθ, hmem, heval⟩ := phase_nodes hn
  let q (i : Fin m) := modulus (θ i)
  have hq : StrictMono q := fun i j hij => strictMonoOn_modulus (hmem i) (hmem j) (hθ hij)
  have hfirst (i : Fin m) : π ≤ checkpointPhase n (θ i) := by
    rw [heval]
    nlinarith [pi_pos, Nat.cast_nonneg (α := ℝ) i.val]
  have hqt (i : Fin m) : (11 / 16 : ℝ) < q i := by
    have := checkpoint_modulus_gap hn (hmem i) (hfirst i)
    dsimp [q]
    linarith [show 0 ≤ 1 / (n : ℝ) ^ 2 by positivity]
  have hp : polynomial n ≠ 0 := leadingCoeff_ne_zero.mp (leadingCoeff_polynomial_pos n).ne'
  obtain ⟨r, hr, ht, heq, hs, hlo, hhi⟩ := signed_grid_roots hp
    ((natDegree_polynomial n).trans hd) (leadingCoeff_polynomial_pos n) q hq hqt
    (by simpa only [neg_div] using (RightEdge.transition_bounds hn).1) (fun i => by
      simpa only [Nat.cast_add, Nat.cast_one] using eval_sign_at_checkpoint hn (hmem i)
        (Nat.succ_pos i.val) (by have := i.isLt; dsimp [m] at this; lia)
          (by simpa only [Nat.cast_succ] using heval i))
  rw [hd]
  refine ⟨r, hr, ht, heq, hs, ?_, ?_⟩
  · intro i hi hi'
    let prev : Fin m := ⟨i.val - 1, by have := i.isLt; lia⟩
    let curr : Fin m := ⟨i.val, by lia⟩
    have hl : q prev < r i := by
      simpa only [show prev.succ = i from Fin.ext (by dsimp [prev]; lia)] using hlo prev
    have hu : r i < q curr := by
      simpa only [show curr.castSucc = i from Fin.ext rfl] using hhi curr
    have horder : θ prev < θ curr := hθ (show prev < curr by dsimp [prev, curr]; lia)
    have hc := continuousOn_modulus.mono (show Icc (θ prev) (θ curr) ⊆ Ioo 0 (π / 2) from
      fun _ hx => ⟨(hmem prev).1.trans_le hx.1, hx.2.trans_lt (hmem curr).2⟩)
    obtain ⟨u, huI, hv⟩ := intermediate_value_Icc horder.le hc ⟨hl.le, hu.le⟩
    have hu' : u ∈ Ioo (θ prev) (θ curr) :=
      ⟨lt_of_le_of_ne huI.1 (by rintro rfl; exact hl.ne hv),
        lt_of_le_of_ne huI.2 (by rintro rfl; exact hu.ne' hv)⟩
    have huO : u ∈ Ioo (0 : ℝ) (π / 2) :=
      ⟨(hmem prev).1.trans hu'.1, hu'.2.trans (hmem curr).2⟩
    have hprev : checkpointPhase n (θ prev) = (i.val : ℝ) * π := by
      rw [heval]
      congr 1
      exact_mod_cast (show prev.val + 1 = i.val by dsimp [prev]; lia)
    have hcurr : checkpointPhase n (θ curr) = ((i.val : ℝ) + 1) * π := heval curr
    have hPhase := checkpointPhase_strictMonoOn (n := n) (by lia)
    refine ⟨u, huO, hv.symm, ?_, ?_⟩
    · rw [← hprev]
      exact hPhase ⟨(hmem prev).1.le, (hmem prev).2.le⟩ ⟨huO.1.le, huO.2.le⟩ hu'.1
    · rw [← hcurr]
      exact hPhase ⟨huO.1.le, huO.2.le⟩ ⟨(hmem curr).1.le, (hmem curr).2.le⟩ hu'.2
  · intro i hi
    let prev : Fin m := ⟨i.val - 1, by have := i.isLt; lia⟩
    have hl : q prev < r i := by
      simpa only [show prev.succ = i from Fin.ext (by dsimp [prev]; lia)] using hlo prev
    exact (checkpoint_modulus_gap hn (hmem prev) (hfirst prev)).trans hl

end RealRooted.CatalanWordPeaks.CutGeometry

namespace RealRooted.CatalanWordPeaks

open Polynomial

/-- Evaluating a split polynomial using a complete list of negative root magnitudes. -/
theorem eval_eq_root_product {p : ℝ[X]} {m : ℕ} {r : Fin m → ℝ}
    (hs : p.Splits) (hr : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = p.roots) (t : ℝ) :
    p.eval t = p.leadingCoeff * ∏ i, (t + r i) := by
  rw [hs.eval_eq_prod_roots, ← hr]
  simp only [Multiset.map_coe, List.map_ofFn, Multiset.prod_coe, List.prod_ofFn,
    Function.comp_def, sub_neg_eq_add]

/-- Mathlib's logarithmic derivative, reindexed by the same complete root list. -/
theorem derivative_div_eval_eq_root_sum {p : ℝ[X]} {m : ℕ} {r : Fin m → ℝ}
    (hs : p.Splits) (hr : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = p.roots)
    {t : ℝ} (ht : p.eval t ≠ 0) :
    p.derivative.eval t / p.eval t = ∑ i, (t + r i)⁻¹ := by
  rw [hs.eval_derivative_div_eval_of_ne_zero ht, ← hr]
  simp only [Multiset.map_coe, List.map_ofFn, Multiset.sum_coe, List.sum_ofFn,
    Function.comp_def, sub_neg_eq_add, one_div]

end RealRooted.CatalanWordPeaks
