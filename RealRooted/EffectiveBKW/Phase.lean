module

public import RealRooted.EffectiveBKW.PairExpansion
import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ordered phase crossings and sample signs

No monotonicity of the phase is assumed. Repeated intermediate-value arguments in
nested intervals give ordered crossings. The caller supplies a continuous phase lift.
An order-connected domain permits bounded intervals and unbounded rays alike.
-/

public section

open Set

namespace RealRooted.EffectiveBKW

/-- A continuous function crossing an increasing list of levels from above to below
has strictly decreasing interior sample points, without being monotone itself. -/
theorem exists_strictAnti_eq_of_continuousOn {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) {K : ℕ} (c : Fin K → ℝ) (hc : StrictMono c)
    (hb : ∀ j, f b < c j) (ha : ∀ j, c j < f a) :
    ∃ s : Fin K → ℝ, StrictAnti s ∧ ∀ j, s j ∈ Ioo a b ∧ f (s j) = c j := by
  induction K generalizing b with
  | zero =>
      exact ⟨Fin.elim0, by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i⟩
  | succ K ih =>
      obtain ⟨z, hz, hfz⟩ := intermediate_value_Ioo' hab.le hf ⟨hb 0, ha 0⟩
      have hf' : ContinuousOn f (Icc a z) :=
        hf.mono (Icc_subset_Icc le_rfl hz.2.le)
      obtain ⟨s, hs, hspec⟩ := ih hz.1 hf' (fun j ↦ c j.succ)
        (hc.comp Fin.strictMono_succ)
        (fun j ↦ by rw [hfz]; exact hc (show (0 : Fin (K + 1)) < j.succ by simp))
        (fun j ↦ ha j.succ)
      refine ⟨Fin.cons z s, ?_, ?_⟩
      · exact (Fin.strictMono_cons (α := OrderDual ℝ)).mpr
          ⟨fun j ↦ (hspec j).1.2, hs⟩
      · intro j
        refine Fin.cases ?_ (fun i ↦ ?_) j
        · exact ⟨hz, hfz⟩
        · exact ⟨⟨(hspec i).1.1, (hspec i).1.2.trans hz.2⟩, (hspec i).2⟩

namespace PairExpansion

variable {P : ℕ → Polynomial ℝ} {J : Set ℝ} (h : PairExpansion P J)

/-- A complex polar identity supplies the real cosine identity consumed by the phase theorem. -/
theorem re_eq_norm_mul_cos_of_polar {n : ℕ} {t φ : ℝ}
    (hp : h.amplitude t * h.lam t ^ n =
      (‖h.amplitude t * h.lam t ^ n‖ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) :
    (h.amplitude t * h.lam t ^ n).re =
      (‖h.amplitude t‖ * ‖h.lam t‖ ^ n) * Real.cos φ := by
  have hr := congrArg Complex.re hp
  calc
    _ = ‖h.amplitude t * h.lam t ^ n‖ * Real.cos φ := by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, Complex.exp_ofReal_mul_I_re] using hr
    _ = _ := by rw [norm_mul, norm_pow]

/-- At an integer phase level, strict remainder domination fixes the sample sign. -/
theorem sign_at_phase {n : ℕ} (hn : h.first ≤ n) {t : ℝ} (ht : t ∈ J)
    (hd : h.Dominates n t) {k : ℤ}
    (hp : (h.amplitude t * h.lam t ^ n).re =
      (‖h.amplitude t‖ * ‖h.lam t‖ ^ n) * Real.cos ((k : ℝ) * Real.pi)) :
    0 < (-1 : ℝ) ^ k * (P n).eval t := by
  change |h.rest n t| < 2 * ‖h.amplitude t‖ * ‖h.lam t‖ ^ n at hd
  have herr := abs_lt.mp hd
  have hsign : (-1 : ℝ) ^ k = 1 ∨ (-1 : ℝ) ^ k = -1 := by
    rw [neg_one_zpow_eq_ite]
    split <;> simp
  rw [h.expand n hn t ht, hp, Real.cos_int_mul_pi]
  rcases hsign with hsign | hsign
  · rw [hsign]
    nlinarith [herr.1]
  · rw [hsign]
    nlinarith [herr.2]

/-- Effective BKW sample signs on any order-connected domain. Hypotheses are: an exact
pair expansion valid at `n`; domination on the domain from `N ≤ n`; a continuous real
phase `φ` supplied by the caller and its cosine identity; ordered witnesses `a < b` in
the domain; and endpoint phase bounds bracketing every level `(L + j)π`, `j ≤ K`.
The phase need not be monotone, and the domain may be an unbounded open interval.
Ordered witnesses are essential: two unordered existential values do not suffice. -/
theorem exists_alternating (hJ : OrdConnected J) {n N K : ℕ} {L : ℤ}
    (hn : h.first ≤ n) (hd : h.Dom J N) (hN : N ≤ n)
    {φ : ℝ → ℝ} (hc : ContinuousOn φ J)
    (hp : ∀ t ∈ J, (h.amplitude t * h.lam t ^ n).re =
      (‖h.amplitude t‖ * ‖h.lam t‖ ^ n) * Real.cos (φ t))
    {a b : ℝ} (ha : a ∈ J) (hb : b ∈ J) (hab : a < b)
    (hlo : φ b < (L : ℝ) * Real.pi)
    (hhi : ((L : ℝ) + K) * Real.pi < φ a) :
    ∃ s : Fin (K + 1) → ℝ, StrictAnti s ∧ (∀ j, s j ∈ J) ∧
      ∀ j, 0 < (-1 : ℝ) ^ (L + (j.val : ℤ)) * (P n).eval (s j) := by
  have hsub : Icc a b ⊆ J := hJ.out ha hb
  let c : Fin (K + 1) → ℝ := fun j ↦ ((L : ℝ) + j.val) * Real.pi
  have hcm : StrictMono c := by
    intro i j hij
    dsimp [c]
    have hij' : (i.val : ℝ) < j.val := by exact_mod_cast hij
    exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos
  have hcb (j : Fin (K + 1)) : φ b < c j := by
    dsimp [c]
    have hj : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hj Real.pi_pos.le]
  have hca (j : Fin (K + 1)) : c j < φ a := by
    dsimp [c]
    have hj : (j.val : ℝ) ≤ K := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
    nlinarith [mul_le_mul_of_nonneg_right hj Real.pi_pos.le]
  obtain ⟨s, hs, hspec⟩ := exists_strictAnti_eq_of_continuousOn hab (hc.mono hsub) c hcm
    hcb hca
  refine ⟨s, hs, fun j ↦ hsub (Ioo_subset_Icc_self (hspec j).1), ?_⟩
  intro j
  have ht := hsub (Ioo_subset_Icc_self (hspec j).1)
  apply h.sign_at_phase hn ht (hd n hN (s j) ht)
  rw [hp (s j) ht, (hspec j).2]
  simp [c, Int.cast_add]

end PairExpansion
end RealRooted.EffectiveBKW
