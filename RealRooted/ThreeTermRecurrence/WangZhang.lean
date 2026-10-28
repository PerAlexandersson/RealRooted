module

public import Mathlib
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots.Real
import RealRooted.ThreeTermRecurrence.OrderTwoLimitZeros

/-!
# Wang–Zhang's affine three-term recurrence

We prove the sufficiency direction of Wang–Zhang, arXiv:1712.06105,
Theorem 2.1 (RealRooted issue #2067): for `a, b, c, d > 0`, every row of the affine recurrence
`W (n + 2) = (a X + b) W (n + 1) + (c X + d) W n` with `W 0 = 1`, `W 1 = X` splits over the
reals iff `a d ≤ b c` (`forall_splits_iff`).

* Sufficiency, `splits_of_affine_two_step`: an explicit root-location argument. The proof was
  found by Aristotle (Harmonic).
* Necessity, `exists_not_splits_of_affine_two_step`: the Beraha–Kahane–Weiss two-dominant-root
  theorem (#2071). Open mapping near the zero `-b/a` of `A = a X + b` gives a nonreal equimodular
  point, so late rows have nonreal zeros.
-/

public section

open Polynomial

namespace RealRooted.WangZhang

/-- The row sequence `W₀ = 1`, `W₁ = X`, `W (n+2) = (a X + b) W (n+1) + (c X + d) W n`. -/
private noncomputable def Wseq (a b c d : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | (n + 2) => (C a * X + C b) * Wseq a b c d (n + 1) + (C c * X + C d) * Wseq a b c d n

private lemma Wseq_succ_succ (a b c d : ℝ) (n : ℕ) :
    Wseq a b c d (n + 2) =
      (C a * X + C b) * Wseq a b c d (n + 1) + (C c * X + C d) * Wseq a b c d n := rfl

private lemma Wseq_eq {a b c d : ℝ} (W : ℕ → ℝ[X]) (h0 : W 0 = 1) (h1 : W 1 = X)
    (hrec : ∀ n, W (n + 2) = (C a * X + C b) * W (n + 1) + (C c * X + C d) * W n) :
    ∀ n, W n = Wseq a b c d n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [h0, Wseq]
    | 1, _ => simp [h1, Wseq]
    | (n+2), ih => rw [hrec, ih n (by lia), ih (n+1) (by lia), Wseq_succ_succ]

private lemma Wseq_deg (a b c d : ℝ) : ∀ n, (Wseq a b c d n).natDegree ≤ n ∧
    (Wseq a b c d (n + 1)).natDegree ≤ n + 1 ∧
      (Wseq a b c d (n + 1)).coeff (n + 1) = a ^ n := by
  intro n
  induction n with
  | zero => simp [Wseq]
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hA : (C a * X + C b).natDegree ≤ 1 := by compute_degree
    have hB : (C c * X + C d).natDegree ≤ 1 := by compute_degree
    refine ⟨h2, ?_, ?_⟩
    · rw [Wseq_succ_succ]
      apply natDegree_add_le_of_degree_le
      · have := natDegree_mul_le_of_le hA h2; lia
      · have := natDegree_mul_le_of_le hB h1; lia
    · rw [Wseq_succ_succ]
      have e1 : (Wseq a b c d (n + 1)).coeff (n + 1 + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by lia)
      have e2 : (Wseq a b c d n).coeff (n + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by lia)
      have e3 : (Wseq a b c d n).coeff (n + 1 + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by lia)
      simp only [add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul, e1, e2, e3, h3]
      ring

private lemma Wseq_natDegree {a : ℝ} (ha : a ≠ 0) (b c d : ℝ) (n : ℕ) :
    (Wseq a b c d n).natDegree = n := by
  rcases n with _ | n
  · simp [Wseq]
  · obtain ⟨-, h2, h3⟩ := Wseq_deg a b c d n
    exact le_antisymm h2 (le_natDegree_of_ne_zero (by rw [h3]; exact pow_ne_zero _ ha))

private lemma Wseq_leadingCoeff {a : ℝ} (ha : a ≠ 0) (b c d : ℝ) (n : ℕ) :
    (Wseq a b c d n).leadingCoeff = a ^ (n - 1) := by
  rcases n with _ | n
  · simp [Wseq]
  · rw [leadingCoeff, Wseq_natDegree ha]
    simpa using (Wseq_deg a b c d n).2.2

private lemma Wseq_eval_zero_pos {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    ∀ n, 0 < (Wseq a b c d (n + 2)).eval 0 ∧ 0 < (Wseq a b c d (n + 3)).eval 0 := by
  intro n
  induction n with
  | zero =>
    simp only [Wseq]
    simpa only [mul_one, eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add, add_zero]
      using ⟨hd, mul_pos hb hd⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [show n + 1 + 3 = (n + 2) + 2 by ring, Wseq_succ_succ]
    simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add]
    have := ih.1; have := ih.2
    positivity

private lemma Wseq_trig (a b c d x r θ : ℝ) (hB : c * x + d = -r ^ 2)
    (hA : a * x + b = 2 * r * Real.cos θ) :
    ∀ n : ℕ, r * Real.sin θ * (Wseq a b c d n).eval x =
      r ^ n * (x * Real.sin (n * θ) - r * Real.sin ((n - 1) * θ)) := by
  have key : ∀ n : ℕ, (r * Real.sin θ * (Wseq a b c d n).eval x =
      r ^ n * (x * Real.sin (n * θ) - r * Real.sin ((n - 1) * θ))) ∧
      (r * Real.sin θ * (Wseq a b c d (n+1)).eval x =
      r ^ (n+1) * (x * Real.sin ((n+1:ℕ) * θ) - r * Real.sin ((((n+1:ℕ):ℝ) - 1) * θ))) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩ <;> simp [Wseq] ; ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨h1, h2⟩ := ih
      rw [show n + 1 + 1 = n + 2 by ring, Wseq_succ_succ]
      simp only [eval_add, eval_mul, eval_C, eval_X]
      have e : r * Real.sin θ * ((a * x + b) * eval x (Wseq a b c d (n + 1)) +
          (c * x + d) * eval x (Wseq a b c d n)) =
          (a * x + b) * (r * Real.sin θ * eval x (Wseq a b c d (n + 1))) +
          (c * x + d) * (r * Real.sin θ * eval x (Wseq a b c d n)) := by ring
      rw [e, h1, h2, hA, hB]
      push_cast
      have s1 : Real.sin ((n + 2) * θ) =
          Real.sin (n * θ) * Real.cos (2 * θ) + Real.cos (n * θ) * Real.sin (2 * θ) := by
        rw [← Real.sin_add]; ring_nf
      have s2 : Real.sin ((n + 2 - 1) * θ) =
          Real.sin (n * θ) * Real.cos θ + Real.cos (n * θ) * Real.sin θ := by
        rw [← Real.sin_add]; ring_nf
      have s3 : Real.sin ((n + 1) * θ) =
          Real.sin (n * θ) * Real.cos θ + Real.cos (n * θ) * Real.sin θ := by
        rw [← Real.sin_add]; ring_nf
      have s4 : Real.sin ((n + 1 - 1) * θ) = Real.sin (n * θ) := by ring_nf
      have s5 : Real.sin ((n - 1) * θ) =
          Real.sin (n * θ) * Real.cos θ - Real.cos (n * θ) * Real.sin θ := by
        rw [← Real.sin_sub]; ring_nf
      rw [s1, s2, s3, s4, s5, Real.cos_two_mul, Real.sin_two_mul]
      ring
  exact fun n => (key n).1

/-- the positive root `r` of `a r² + 2 c t r = b c - a d`. -/
private noncomputable def rp (a b c d : ℝ) (n j : ℕ) : ℝ :=
  (√(c ^ 2 * (Real.cos (j * Real.pi / n)) ^ 2 + a * (b * c - a * d))
    - c * Real.cos (j * Real.pi / n)) / a

private noncomputable def xp (a b c d : ℝ) (n j : ℕ) : ℝ := -((rp a b c d n j) ^ 2 + d) / c

private lemma rp_pos {a b c d : ℝ} (ha : 0 < a) (hK : a * d < b * c) (n j : ℕ) :
    0 < rp a b c d n j := by
  unfold rp
  set t := Real.cos (j * Real.pi / n)
  have hpos : 0 < c ^ 2 * t ^ 2 + a * (b * c - a * d) := by nlinarith [sq_nonneg (c * t)]
  have hS := Real.sq_sqrt hpos.le
  have hS0 := Real.sqrt_nonneg (c ^ 2 * t ^ 2 + a * (b * c - a * d))
  apply div_pos _ ha
  nlinarith [sq_nonneg (c * t), sq_abs (c * t), abs_nonneg (c * t), le_abs_self (c * t)]

private lemma rp_eq {a b c d : ℝ} (ha : 0 < a) (hK : a * d < b * c) (n j : ℕ) :
    a * (rp a b c d n j) ^ 2 + 2 * c * Real.cos (j * Real.pi / n) * rp a b c d n j
      = b * c - a * d := by
  unfold rp
  set t := Real.cos (j * Real.pi / n)
  have hpos : 0 < c ^ 2 * t ^ 2 + a * (b * c - a * d) := by nlinarith [sq_nonneg (c * t)]
  have hS := Real.sq_sqrt hpos.le
  set S := √(c ^ 2 * t ^ 2 + a * (b * c - a * d))
  field_simp
  linear_combination hS

private lemma Wseq_eval_xp {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hK : a * d < b * c)
    (n j : ℕ) (hj : 1 ≤ j) (hjn : j < n) :
    (Wseq a b c d n).eval (xp a b c d n j) = (-1) ^ j * (rp a b c d n j) ^ n := by
  have hr := rp_pos ha hK n j
  have he := rp_eq ha hK n j
  set θ := (j:ℝ) * Real.pi / n with hθ
  set r := rp a b c d n j
  have hn : (0:ℝ) < n := by exact_mod_cast (show 0 < n by lia)
  have hB : c * xp a b c d n j + d = -r ^ 2 := by
    unfold xp; field_simp; ring
  have hA : a * xp a b c d n j + b = 2 * r * Real.cos θ := by
    unfold xp; field_simp; linarith
  have key := Wseq_trig a b c d _ r θ hB hA n
  have hsin0 : Real.sin (n * θ) = 0 := by
    rw [hθ, show (n:ℝ) * (j * Real.pi / n) = (j:ℕ) * Real.pi by field_simp]
    exact Real.sin_nat_mul_pi j
  have hsin1 : Real.sin ((n - 1) * θ) = -((-1) ^ j * Real.sin θ) := by
    rw [show ((n:ℝ) - 1) * θ = (j:ℕ) * Real.pi - θ by rw [hθ]; field_simp, Real.sin_sub,
      Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    ring
  have hspos : 0 < Real.sin θ := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [hθ, div_lt_iff₀ hn]
      have : (j:ℝ) < n := by exact_mod_cast hjn
      nlinarith [Real.pi_pos]
  rw [hsin0, hsin1] at key
  have hne : r * Real.sin θ ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  rw [key]; ring

private lemma rp_strictMono {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hK : a * d < b * c)
    (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hjn : j < n) :
    rp a b c d n i < rp a b c d n j := by
  have p1 := rp_pos ha hK n i
  have p2 := rp_pos ha hK n j
  have h1 := rp_eq ha hK n i
  have h2 := rp_eq ha hK n j
  have hn : (0:ℝ) < n := by exact_mod_cast (show 0 < n by lia)
  have ht : Real.cos (j * Real.pi / n) < Real.cos (i * Real.pi / n) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    · positivity
    · rw [div_le_iff₀ hn]; have : (j:ℝ) ≤ n := by exact_mod_cast hjn.le
      nlinarith [Real.pi_pos]
    · apply div_lt_div_of_pos_right _ hn
      have : (i:ℝ) < j := by exact_mod_cast hij
      nlinarith [Real.pi_pos]
  set ti := Real.cos (i * Real.pi / n)
  set tj := Real.cos (j * Real.pi / n)
  set ri := rp a b c d n i
  set rj := rp a b c d n j
  have hpos : 0 < a * ri + 2 * c * ti := by
    by_contra hcon; push Not at hcon; nlinarith
  have hpos' : 0 < a * (ri + rj) + 2 * c * ti := by nlinarith
  by_contra hcon; push Not at hcon
  nlinarith [mul_nonneg (sub_nonneg.2 hcon) hpos'.le, mul_pos (mul_pos hc p2) (sub_pos.2 ht)]

private lemma exists_root_between (p : ℝ[X]) {u v : ℝ} (huv : u < v)
    (h : p.eval u * p.eval v < 0) : ∃ ρ, u < ρ ∧ ρ < v ∧ p.eval ρ = 0 := by
  have hc : ContinuousOn (fun x => p.eval x) (Set.Icc u v) := p.continuous.continuousOn
  rcases lt_or_gt_of_ne (show p.eval u ≠ 0 by rintro h0; simp [h0] at h) with hu | hu
  · have hv : 0 < p.eval v := by nlinarith
    obtain ⟨ρ, ⟨h1, h2⟩, h3⟩ := intermediate_value_Ioo huv.le hc ⟨hu, hv⟩
    exact ⟨ρ, h1, h2, h3⟩
  · have hv : p.eval v < 0 := by nlinarith
    obtain ⟨ρ, ⟨h1, h2⟩, h3⟩ := intermediate_value_Ioo' huv.le hc ⟨hv, hu⟩
    exact ⟨ρ, h1, h2, h3⟩

private lemma splits_of_card_roots_ge {p : ℝ[X]} {m : ℕ} (hdeg : p.natDegree = m + 1)
    (hroots : m ≤ p.roots.card) : p.Splits := by
  obtain ⟨q, hq, hcard, -⟩ := exists_prod_multiset_X_sub_C_mul p
  rw [← hq]
  apply Splits.mul
  · apply Splits.multisetProd
    intro f hf
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hf
    exact Splits.of_natDegree_le_one (by compute_degree!)
  · exact Splits.of_natDegree_le_one (by lia)

private lemma Wseq_card_roots {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hK : a * d < b * c) (n : ℕ) (hn : 2 ≤ n) : n - 1 ≤ (Wseq a b c d n).roots.card := by
  have hn0 : (Wseq a b c d n) ≠ 0 := by
    intro h
    exact (pow_ne_zero _ ha.ne') (by
      simpa [h] using (Wseq_leadingCoeff ha.ne' b c d n).symm)
  have hz0 : 0 < (Wseq a b c d n).eval 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by lia⟩
    exact (Wseq_eval_zero_pos hb hd k).1
  set p := Wseq a b c d n with hp
  set y : ℕ → ℝ := fun j => if j = 0 then 0 else xp a b c d n j with hy
  have hxneg : ∀ j, xp a b c d n j < 0 := fun j => by
    unfold xp
    apply div_neg_of_neg_of_pos _ hc
    nlinarith [sq_nonneg (rp a b c d n j)]
  have hstep : ∀ j, 1 ≤ j → j < n →
      y j < y (j - 1) ∧ p.eval (y j) * p.eval (y (j - 1)) < 0 := by
    intro j hj hjn
    have hyj : y j = xp a b c d n j := by simp [hy]; lia
    rw [hyj, Wseq_eval_xp ha hc hK n j hj hjn]
    have hr := rp_pos ha hK n j
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · obtain rfl : j = 1 := by lia
      have hy0 : y (1 - 1) = 0 := by simp [hy]
      rw [hy0]
      refine ⟨hxneg 1, ?_⟩
      have := pow_pos hr n
      nlinarith
    · have hyj' : y (j - 1) = xp a b c d n (j - 1) := by simp [hy]; lia
      rw [hyj', Wseq_eval_xp ha hc hK n (j - 1) (by lia) (by lia)]
      have hr' := rp_pos ha hK n (j - 1)
      have hlt := rp_strictMono ha hc hK n (j - 1) j (by lia) (by lia) hjn
      refine ⟨?_, ?_⟩
      · unfold xp
        apply div_lt_div_of_pos_right _ hc
        nlinarith
      · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by lia⟩
        simp only [show k + 1 - 1 = k by lia] at *
        rw [pow_succ]
        have h1 := pow_pos hr n
        have h2 := pow_pos hr' n
        have h3 : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
        have e : (-1 : ℝ) ^ k * -1 * rp a b c d n (k + 1) ^ n * ((-1) ^ k * rp a b c d n k ^ n)
            = -(rp a b c d n (k + 1) ^ n * rp a b c d n k ^ n) * ((-1 : ℝ) ^ k) ^ 2 := by ring
        rw [e, h3]
        nlinarith [mul_pos h1 h2]
  have hroot : ∀ j, ∃ ρ, 1 ≤ j → j < n →
      y j < ρ ∧ ρ < y (j - 1) ∧ p.eval ρ = 0 := by
    intro j
    by_cases h : 1 ≤ j ∧ j < n
    · obtain ⟨ρ, h1, h2, h3⟩ :=
        exists_root_between p (hstep j h.1 h.2).1 (hstep j h.1 h.2).2
      exact ⟨ρ, fun _ _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose ρ hρ using hroot
  have hanti : ∀ i j, i ≤ j → j < n → y j ≤ y i := by
    intro i j hij hjn
    induction j, hij using Nat.le_induction with
    | base => exact le_refl _
    | succ k hik ih =>
      have := (hstep (k + 1) (by lia) hjn).1
      rw [show k + 1 - 1 = k by lia] at this
      exact this.le.trans (ih (by lia))
  have hinj : Set.InjOn ρ (Finset.Icc 1 (n - 1) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_Icc, Set.mem_Icc] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have e1 := (hρ j (by lia) (by lia)).2.1
      have e2 := hanti i (j - 1) (by lia) (by lia)
      have e3 := (hρ i (by lia) (by lia)).1
      linarith
    · have e1 := (hρ i (by lia) (by lia)).2.1
      have e2 := hanti j (i - 1) (by lia) (by lia)
      have e3 := (hρ j (by lia) (by lia)).1
      linarith
  have hcard : ((Finset.Icc 1 (n - 1)).image ρ).card = n - 1 := by
    rw [Finset.card_image_of_injOn hinj]; simp
  rw [← hcard]
  apply Multiset.card_le_card
  rw [Multiset.le_iff_subset (Finset.nodup _)]
  intro x hx
  have hx' : x ∈ (Finset.Icc 1 (n - 1)).image ρ := hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx'
  rw [Finset.mem_Icc] at hj
  rw [mem_roots hn0]
  exact (hρ j hj.1 (by lia)).2.2

private lemma Wseq_splits_of_lt {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hK : a * d < b * c) (n : ℕ) : (Wseq a b c d n).Splits := by
  rcases Nat.lt_or_ge n 2 with h | h
  · exact Splits.of_natDegree_le_one (by rw [Wseq_natDegree ha.ne']; lia)
  · exact splits_of_card_roots_ge (m := n - 1) (by rw [Wseq_natDegree ha.ne']; lia)
      (Wseq_card_roots ha hb hc hd hK n h)

private lemma Wseq_continuous (a c d : ℝ) (z : ℂ) :
    ∀ n, Continuous (fun b => aeval z (Wseq a b c d n)) := by
  have key : ∀ n, Continuous (fun b => aeval z (Wseq a b c d n)) ∧
      Continuous (fun b => aeval z (Wseq a b c d (n + 1))) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩ <;> simp only [Wseq, map_one, aeval_X] <;> exact continuous_const
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      simp only [show n + 1 + 1 = n + 2 by ring, Wseq_succ_succ, map_add, map_mul, aeval_C,
        aeval_X, Complex.coe_algebraMap]
      have h1 := ih.1; have h2 := ih.2
      fun_prop
  exact fun n => (key n).1

private lemma Wseq_splits {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (habcd : a * d ≤ b * c) (n : ℕ) : (Wseq a b c d n).Splits := by
  let b' : ℕ → ℝ := fun k => b + 1 / (k + 1)
  let p : ℕ → ℝ[X] := fun k => Wseq a (b' k) c d n
  have hb'tend : Filter.Tendsto b' Filter.atTop (nhds b) := by
    simpa [b'] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hhom : Complex.ofRealHom = algebraMap ℝ ℂ := by ext; rfl
  have hlimit := Polynomial.eq_zero_or_splits_of_tendsto_eval_of_natDegree_le
    (p := p) (p₀ := Wseq a b c d n) (N := n)
    (fun k => (Wseq_deg a (b' k) c d n).1)
    (fun k => Or.inr (Wseq_splits_of_lt ha (by dsimp [b']; positivity) hc hd (by
      have hk : 0 < (1 : ℝ) / (k + 1) := by positivity
      dsimp [b']
      nlinarith [mul_pos hk hc]) n))
    (fun z => by
      rw [hhom]
      have ht := (Wseq_continuous a c d z n).continuousAt.tendsto.comp hb'tend
      simpa only [p, Function.comp_def, aeval_def, eval₂_eq_eval_map] using ht)
  rcases hlimit with hzero | hsplits
  · exact (pow_ne_zero _ ha.ne') (by
      simpa [hzero] using (Wseq_leadingCoeff ha.ne' b c d n).symm) |>.elim
  · exact hsplits

/-- Wang–Zhang, arXiv:1712.06105, Theorem 2.1 (sufficiency; RealRooted issue #2067).
For `a, b, c, d > 0` with `a d ≤ b c`, every row of `W₀ = 1`, `W₁ = X`,
`W (n+2) = (a X + b) W (n+1) + (c X + d) W n` splits over ℝ.

Paper proof sketch: put `A = a X + b`, `B = c X + d`, `x_A = -b/a ≤ x_B = -d/c` (this is
`a d ≤ b c`), `Δ = A² + 4B`. For `n ≥ 4` the rows satisfy the two-step recurrence
`W n = (A² + 2B) W (n-2) - B² W (n-4)`, so at a zero `x` of `W (n-2)` the sign of `W n x` is
`-sign (W (n-4) x)` (as `B x ≠ 0`). The zeros lie in fixed intervals left of `x_A`, between `x_A`
and the larger root of `Δ`, and near `0`; within each interval the zeros of `W n` and `W (n-2)`
strictly interlace, with known signs at the interval endpoints (e.g. `sign (W n (x_A)) =
(-1)^⌈n/2⌉` when `x_A < x_B`). The intermediate value theorem then gives `deg W n = n` real
zeros. In the boundary case `a d = b c`, `B = (c/a) A` and `A ^ ⌊n/2⌋` divides `W n`; the
quotient satisfies a similar recurrence. Any correct proof is fine. -/
theorem splits_of_affine_two_step {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (habcd : a * d ≤ b * c) (W : ℕ → ℝ[X]) (h0 : W 0 = 1) (h1 : W 1 = X)
    (hrec : ∀ n, W (n + 2) = (C a * X + C b) * W (n + 1) + (C c * X + C d) * W n) (n : ℕ) :
    (W n).Splits := by
  rw [WangZhang.Wseq_eq W h0 h1 hrec n]
  exact WangZhang.Wseq_splits ha hb hc hd habcd n


/-! ### Necessity (Beraha–Kahane–Weiss) -/

section Necessity

open Filter Topology Metric Polynomial
private theorem affine_ratio_not_locally_constant {A B : ℂ → ℂ} {x y z₀ : ℂ}
    (hA : ∀ z, AnalyticAt ℂ A z) (hB : ∀ z, AnalyticAt ℂ B z)
    (hAx : A x = 0) (hAy : A y ≠ 0) (hBx : B x ≠ 0) (hBz : B z₀ ≠ 0) :
    ¬∀ᶠ z in 𝓝 z₀,
      A z ^ 2 / (-4 * B z) = A z₀ ^ 2 / (-4 * B z₀) := by
  intro hconst
  let q₀ : ℂ := A z₀ ^ 2 / (-4 * B z₀)
  let P : ℂ → ℂ := fun z => A z ^ 2 + 4 * q₀ * B z
  have hP : AnalyticOnNhd ℂ P Set.univ := by
    intro z _
    dsimp [P]
    fun_prop (disch := assumption)
  have hBnear : ∀ᶠ z in 𝓝 z₀, B z ≠ 0 :=
    (hB z₀).continuousAt.eventually_ne hBz
  have hzero : P =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hconst, hBnear] with z hz hBz'
    have hden : (-4 : ℂ) * B z ≠ 0 := mul_ne_zero (by norm_num) hBz'
    have heq : A z ^ 2 = q₀ * (-4 * B z) := (div_eq_iff hden).mp hz
    change P z = 0
    dsimp [P]
    linear_combination heq
  have hglobal := hP.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z₀) hzero
  have hx : 4 * q₀ * B x = 0 := by simpa [P, hAx] using hglobal (Set.mem_univ x)
  have hq₀ : q₀ = 0 := by
    have hfour : (4 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp (mul_eq_zero.mp hx |>.resolve_right hBx)).resolve_left hfour
  have hy : A y ^ 2 = 0 := by simpa [P, hq₀] using hglobal (Set.mem_univ y)
  exact (pow_ne_zero 2 hAy) hy

private theorem exists_nonreal_positive_ratio {q : ℂ → ℂ} {x : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hq : AnalyticAt ℂ q x) (hq0 : q x = 0)
    (hnconst : ¬∀ᶠ z in 𝓝 x, q z = q x)
    (hreal : ∀ z ∈ ball x ρ, z.im = 0 →
      ∀ t : ℝ, 0 < t → q z ≠ (t : ℂ)) :
    ∃ z ∈ ball x ρ, ∃ t : ℝ, 0 < t ∧ t < 1 ∧ q z = (t : ℂ) ∧ z.im ≠ 0 := by
  have hmap : 𝓝 (q x) ≤ Filter.map q (𝓝 x) :=
    (hq.eventually_constant_or_nhds_le_map_nhds).resolve_left hnconst
  have himage : q '' ball x ρ ∈ 𝓝 (q x) := by
    apply hmap
    change q ⁻¹' (q '' ball x ρ) ∈ 𝓝 x
    exact mem_of_superset (ball_mem_nhds x hρ) (fun z hz => ⟨z, hz, rfl⟩)
  obtain ⟨η, hη, hηimage⟩ := Metric.mem_nhds_iff.mp himage
  let t : ℝ := min η 1 / 2
  have ht0 : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]
    linarith [min_le_right η 1]
  have htη : t < η := by
    dsimp [t]
    linarith [min_le_left η 1]
  have htball : (t : ℂ) ∈ ball (q x) η := by
    rw [hq0, mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos ht0]
    exact htη
  obtain ⟨z, hz, hqz⟩ := hηimage htball
  refine ⟨z, hz, t, ht0, ht1, hqz, ?_⟩
  intro hzim
  exact hreal z hz hzim t ht0 hqz

private theorem affine_initial_not_locally_zero {A B : ℂ → ℂ} {z₀ : ℂ}
    (hA : ∀ z, AnalyticAt ℂ A z) (hB : ∀ z, AnalyticAt ℂ B z)
    (hE0 : (0 : ℂ) ^ 2 - A 0 * 0 - B 0 ≠ 0) :
    ¬∀ᶠ z in 𝓝 z₀, z ^ 2 - A z * z - B z = 0 := by
  intro hzero
  let E : ℂ → ℂ := fun z => z ^ 2 - A z * z - B z
  have hE : AnalyticOnNhd ℂ E Set.univ := by
    intro z _
    dsimp [E]
    fun_prop (disch := assumption)
  have hglobal := hE.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z₀) hzero
  exact hE0 (hglobal (Set.mem_univ 0))

/-- Positive affine data with `ad > bc` produces a nonreal point with positive ratio. -/
private theorem exists_affine_nonreal_positive_ratio {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (habcd : b * c < a * d) :
    let A : ℂ → ℂ := fun z ↦ (a : ℂ) * z + b
    let B : ℂ → ℂ := fun z ↦ (c : ℂ) * z + d
    let q : ℂ → ℂ := fun z ↦ A z ^ 2 / (-4 * B z)
    let x : ℂ := ((-b / a : ℝ) : ℂ)
    (∀ z, AnalyticAt ℂ A z) ∧ (∀ z, AnalyticAt ℂ B z) ∧
      A x = 0 ∧ A 0 ≠ 0 ∧ B x ≠ 0 ∧
        ∃ z₀ : ℂ, ∃ t : ℝ,
          0 < t ∧ t < 1 ∧ q z₀ = (t : ℂ) ∧ z₀.im ≠ 0 ∧ B z₀ ≠ 0 := by
  let A : ℂ → ℂ := fun z ↦ (a : ℂ) * z + b
  let B : ℂ → ℂ := fun z ↦ (c : ℂ) * z + d
  let q : ℂ → ℂ := fun z ↦ A z ^ 2 / (-4 * B z)
  let x : ℂ := ((-b / a : ℝ) : ℂ)
  have hA (z : ℂ) : AnalyticAt ℂ A z := by dsimp [A]; fun_prop
  have hB (z : ℂ) : AnalyticAt ℂ B z := by dsimp [B]; fun_prop
  have hAx : A x = 0 := by
    dsimp [A, x]
    push_cast
    field_simp [ha.ne']
    ring
  have hA0 : A 0 ≠ 0 := by
    simp only [A, mul_zero, zero_add]
    exact_mod_cast hb.ne'
  have hBxpos : 0 < (B x).re := by
    have hreal : 0 < d - c * b / a := by
      apply (sub_pos).mpr
      apply (div_lt_iff₀ ha).mpr
      nlinarith [habcd]
    convert hreal using 1
    dsimp [B, x]
    push_cast
    simp
    ring
  have hBx : B x ≠ 0 := fun heq ↦ by simp [heq] at hBxpos
  have hq0 : q x = 0 := by simp [q, hAx]
  have hqnconst : ¬∀ᶠ z in 𝓝 x, q z = q x :=
    affine_ratio_not_locally_constant hA hB hAx hA0 hBx hBx
  have hq : AnalyticAt ℂ q x := by
    have hden : (-4 : ℂ) * B x ≠ 0 := mul_ne_zero (by norm_num) hBx
    exact (hA x).pow 2 |>.div (analyticAt_const.mul (hB x)) hden
  have hBposNear : ∀ᶠ z in 𝓝 x, 0 < (B z).re :=
    continuousAt_const.eventually_lt
      (Complex.continuous_re.continuousAt.comp (hB x).continuousAt) hBxpos
  obtain ⟨ρ, hρ, hBpos⟩ := Metric.mem_nhds_iff.mp hBposNear
  have hreal (z : ℂ) (hz : z ∈ ball x ρ) (hzim : z.im = 0)
      (t : ℝ) (ht : 0 < t) : q z ≠ (t : ℂ) := by
    intro hqz
    have hBz : B z ≠ 0 := fun heq ↦ by have := hBpos hz; simp [heq] at this
    have hden : (-4 : ℂ) * B z ≠ 0 := mul_ne_zero (by norm_num) hBz
    have heq : A z ^ 2 = (t : ℂ) * (-4 * B z) := (div_eq_iff hden).mp hqz
    have hzreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hzim]
    have hAim : (A z).im = 0 := by rw [hzreal]; simp [A]
    have hEq := congrArg Complex.re heq
    simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, zero_mul, hAim] at hEq
    norm_num at hEq
    nlinarith [sq_nonneg (A z).re, mul_pos ht (hBpos hz)]
  obtain ⟨z₀, hz₀, t, ht0, ht1, hqz₀, hzim⟩ :=
    exists_nonreal_positive_ratio hρ hq hq0 hqnconst hreal
  have hBz : B z₀ ≠ 0 := fun heq ↦ by have := hBpos hz₀; simp [heq] at this
  exact ⟨hA, hB, hAx, hA0, hBx, z₀, t, ht0, ht1, hqz₀, hzim, hBz⟩

/-- A positive subunit ratio yields distinct equimodular local quadratic branches. -/
private theorem exists_local_equimodular_branches {A B : ℂ → ℂ} {z₀ : ℂ} {t : ℝ}
    (hA : ∀ z, AnalyticAt ℂ A z) (hB : ∀ z, AnalyticAt ℂ B z)
    (ht0 : 0 < t) (ht1 : t < 1) (hBz : B z₀ ≠ 0)
    (hqz : A z₀ ^ 2 / (-4 * B z₀) = (t : ℂ)) :
    ∃ η : ℝ, ∃ droot : ℂ → ℂ,
      0 < η ∧ AnalyticAt ℂ droot z₀ ∧ droot z₀ ≠ 0 ∧
      (∀ z ∈ ball z₀ η, droot z ^ 2 = A z ^ 2 + 4 * B z) ∧
      (∀ z ∈ ball z₀ η,
        (A z + droot z) / 2 + (A z - droot z) / 2 = A z ∧
        (A z + droot z) / 2 * ((A z - droot z) / 2) = -B z ∧
        (A z + droot z) / 2 ≠ (A z - droot z) / 2) ∧
      (A z₀ + droot z₀) / 2 ≠ (A z₀ - droot z₀) / 2 ∧
      (A z₀ - droot z₀) / 2 ≠ 0 ∧
      ‖(A z₀ + droot z₀) / 2‖ = ‖(A z₀ - droot z₀) / 2‖ := by
  let D : ℂ → ℂ := fun z ↦ A z ^ 2 + 4 * B z
  have hqeq : A z₀ ^ 2 = -4 * (t : ℂ) * B z₀ := by
    have hden : (-4 : ℂ) * B z₀ ≠ 0 := mul_ne_zero (by norm_num) hBz
    have heq := (div_eq_iff hden).mp hqz
    linear_combination heq
  have hD0 : D z₀ ≠ 0 := by
    intro heq
    have heq' : 4 * (1 - (t : ℂ)) * B z₀ = 0 := by
      dsimp [D] at heq
      linear_combination heq - hqeq
    have h1t : (1 - (t : ℂ)) ≠ 0 := fun h ↦ by
      have : t = 1 := by exact_mod_cast (sub_eq_zero.mp h).symm
      linarith
    exact (mul_ne_zero (mul_ne_zero (by norm_num) h1t) hBz) heq'
  have hD : AnalyticAt ℂ D z₀ := by dsimp [D]; fun_prop (disch := assumption)
  obtain ⟨ρD, hρD, droot, hdanalytic, hdsq, hd0⟩ :=
    Complex.exists_ball_analytic_square_root hD hD0
  have hdan : AnalyticAt ℂ droot z₀ := hdanalytic z₀ (mem_ball_self hρD)
  have hdev : ∀ᶠ z in 𝓝 z₀, droot z ≠ 0 := hdan.continuousAt.eventually_ne hd0
  obtain ⟨ρd, hρd, hdnear⟩ := Metric.mem_nhds_iff.mp hdev
  let η := min ρD ρd
  have hη : 0 < η := lt_min hρD hρd
  have hηD : ball z₀ η ⊆ ball z₀ ρD := ball_subset_ball (min_le_left _ _)
  have hηd : ball z₀ η ⊆ ball z₀ ρd := ball_subset_ball (min_le_right _ _)
  have hsq (z : ℂ) (hz : z ∈ ball z₀ η) : droot z ^ 2 = A z ^ 2 + 4 * B z := by
    simpa only [D] using hdsq z (hηD hz)
  have hrootdata (z : ℂ) (hz : z ∈ ball z₀ η) :
      (A z + droot z) / 2 + (A z - droot z) / 2 = A z ∧
      (A z + droot z) / 2 * ((A z - droot z) / 2) = -B z ∧
      (A z + droot z) / 2 ≠ (A z - droot z) / 2 := by
    have hdz : droot z ≠ 0 := hdnear (hηd hz)
    refine ⟨by ring, ?_, ?_⟩
    · linear_combination (-1 / 4 : ℂ) * hsq z hz
    · intro heq
      apply hdz
      linear_combination heq
  have hroots0 := hrootdata z₀ (mem_ball_self hη)
  have hv0 : (A z₀ - droot z₀) / 2 ≠ 0 := by
    intro hzero
    apply hBz
    simpa [hzero] using hroots0.2.1.symm
  have heq : ‖(A z₀ + droot z₀) / 2‖ = ‖(A z₀ - droot z₀) / 2‖ :=
    equimodular_quadratic_roots ht0 ht1 hd0 hqeq
      (by simpa [D] using hdsq z₀ (mem_ball_self hρD))
  exact ⟨η, droot, hη, hdan, hd0, hsq, hrootdata, hroots0.2.2, hv0, heq⟩

/-- Neither characteristic-root branch agrees locally with the initial evaluation map. -/
private theorem quadratic_branch_initial_germs {A B u v : ℂ → ℂ} {z₀ : ℂ} {η : ℝ}
    (hη : 0 < η) (hA : ∀ z, AnalyticAt ℂ A z) (hB : ∀ z, AnalyticAt ℂ B z)
    (hE0 : (0 : ℂ) ^ 2 - A 0 * 0 - B 0 ≠ 0)
    (hrootdata : ∀ z ∈ ball z₀ η,
      u z + v z = A z ∧ u z * v z = -B z ∧ u z ≠ v z) :
    (¬∀ᶠ z in 𝓝 z₀, z - v z = 0) ∧ (¬∀ᶠ z in 𝓝 z₀, u z - z = 0) := by
  have hEgerm : ¬∀ᶠ z in 𝓝 z₀, z ^ 2 - A z * z - B z = 0 :=
    affine_initial_not_locally_zero hA hB hE0
  have hfactor (z : ℂ) (hz : z ∈ ball z₀ η) :
      z ^ 2 - A z * z - B z = (z - u z) * (z - v z) := by
    have hr := hrootdata z hz
    linear_combination z * hr.1 - hr.2.1
  constructor
  · intro h
    apply hEgerm
    filter_upwards [h, ball_mem_nhds z₀ hη] with z hz hzball
    rw [hfactor z hzball, hz, mul_zero]
  · intro h
    apply hEgerm
    filter_upwards [h, ball_mem_nhds z₀ hη] with z hz hzball
    rw [hfactor z hzball, show z - u z = 0 by linear_combination -hz, zero_mul]

/-- Wang--Zhang's necessary condition: if all four affine recurrence coefficients are
positive and `ad > bc`, some row with initial data `1, X` does not split over `ℝ`.
This is the necessity direction of Wang--Zhang, arXiv:1712.06105, Theorem 2.1. -/
theorem exists_not_splits_of_affine_two_step {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (habcd : b * c < a * d)
    (W : ℕ → ℝ[X]) (h0 : W 0 = 1) (h1 : W 1 = X)
    (hrec : ∀ n, W (n + 2) = (C a * X + C b) * W (n + 1) +
      (C c * X + C d) * W n) :
    ∃ n, ¬(W n).Splits := by
  let A : ℂ → ℂ := fun z => (a : ℂ) * z + b
  let B : ℂ → ℂ := fun z => (c : ℂ) * z + d
  let q : ℂ → ℂ := fun z => A z ^ 2 / (-4 * B z)
  let xA : ℝ := -b / a
  let x : ℂ := (xA : ℂ)
  obtain ⟨hA, hB, hAx, hA0, hBx, z₀, t, ht0, ht1, hqz₀, hzim, hBz⟩ :=
    exists_affine_nonreal_positive_ratio ha hb habcd
  have hqnonconst : ¬∀ᶠ z in 𝓝 z₀, q z = q z₀ :=
    affine_ratio_not_locally_constant hA hB hAx hA0 hBx hBz
  obtain ⟨η, droot, hη, hdan, hd0, hdsq, hrootdata0, huv0, hv0', heq'⟩ :=
    exists_local_equimodular_branches hA hB ht0 ht1 hBz hqz₀
  let u : ℂ → ℂ := fun z => (A z + droot z) / 2
  let v : ℂ → ℂ := fun z => (A z - droot z) / 2
  have hrootdata : ∀ z ∈ ball z₀ η,
      u z + v z = A z ∧ u z * v z = -B z ∧ u z ≠ v z := by
    simpa only [u, v] using hrootdata0
  have huv : u z₀ ≠ v z₀ := by simpa only [u, v] using huv0
  have hv0 : v z₀ ≠ 0 := by simpa only [v] using hv0'
  have heq : ‖u z₀‖ = ‖v z₀‖ := by simpa only [u, v] using heq'
  have hE0 : (0 : ℂ) ^ 2 - A 0 * 0 - B 0 ≠ 0 := by
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    simpa [A, B] using neg_ne_zero.mpr hdC
  obtain ⟨hcugerm, hcvgerm⟩ := quadratic_branch_initial_germs hη hA hB hE0 hrootdata
  have hBnear : ∀ᶠ z in 𝓝 z₀, B z ≠ 0 :=
    (hB z₀).continuousAt.eventually_ne hBz
  obtain ⟨ρB, hρB, hBball⟩ := Metric.mem_nhds_iff.mp hBnear
  let ξ := min η ρB
  have hξ : 0 < ξ := lt_min hη hρB
  have hξη : ball z₀ ξ ⊆ ball z₀ η :=
    ball_subset_ball (min_le_left _ _)
  have hξB : ball z₀ ξ ⊆ ball z₀ ρB :=
    ball_subset_ball (min_le_right _ _)
  have hdsqξ (z : ℂ) (hz : z ∈ ball z₀ ξ) :
      droot z ^ 2 = A z ^ 2 + 4 * B z := by
    exact hdsq z (hξη hz)
  have hBξ (z : ℂ) (hz : z ∈ ball z₀ ξ) : B z ≠ 0 :=
    hBball (hξB hz)
  have hplus (z : ℂ) (hz : z ∈ ball z₀ ξ) : A z + droot z ≠ 0 := by
    intro hzero
    have hu0 : u z = 0 := by simp [u, hzero]
    have hp := (hrootdata z (hξη hz)).2.1
    exact hBξ z hz (by simpa [hu0] using hp.symm)
  have hminus (z : ℂ) (hz : z ∈ ball z₀ ξ) : A z - droot z ≠ 0 := by
    intro hzero
    have hvzero : v z = 0 := by simp [v, hzero]
    have hp := (hrootdata z (hξη hz)).2.1
    exact hBξ z hz (by simpa [hvzero] using hp.symm)
  have hratio : ¬∀ᶠ z in 𝓝 z₀, u z / v z = u z₀ / v z₀ := by
    simpa [u, v] using quadratic_ratio_not_locally_constant hξ hdsqξ
      hBξ hplus hminus hqnonconst
  let F : ℕ → ℂ → ℂ := fun n z => ((W n).map Complex.ofRealHom).eval z
  have hF0 : F 0 = fun _ => 1 := by funext z; simp [F, h0]
  have hF1 : F 1 = fun z => z := by funext z; simp [F, h1]
  have hFrec (n : ℕ) (z : ℂ) :
      F (n + 2) z = A z * F (n + 1) z + B z * F n z := by
    simp [F, hrec, A, B]
  have hlim : Complex.IsLimitOfZeros F z₀ :=
    isLimitOfZeros_two_step_of_roots_closure hη hF0 hF1 hFrec
      hrootdata analyticAt_const analyticAt_id
      ((hA z₀).add hdan).div_const ((hA z₀).sub hdan).div_const
      huv hv0 (by simpa using hcugerm) (by simpa using hcvgerm) heq hratio
  have hpos : ∀ n, 0 < (W n).eval 1 := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [h0]
    | one => simp [h1]
    | more n ih0 ih1 =>
        rw [hrec]
        simp only [eval_add, eval_mul, eval_C, eval_X]
        nlinarith [mul_pos (add_pos ha hb) ih1, mul_pos (add_pos hc hd) ih0]
  have hnonzero : ∀ᶠ n in atTop, W n ≠ 0 :=
    Eventually.of_forall fun n hzero => by simpa [hzero] using hpos n
  have hlate := eventually_not_splits_of_nonreal_limit hzim hnonzero hlim
  exact hlate.exists

end Necessity

/-- **Wang–Zhang, Theorem 2.1.** For `a, b, c, d > 0`, all rows of `W₀ = 1`, `W₁ = X`,
`W (n+2) = (a X + b) W (n+1) + (c X + d) W n` split over the reals iff `a d ≤ b c`. -/
theorem forall_splits_iff {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (W : ℕ → ℝ[X]) (h0 : W 0 = 1) (h1 : W 1 = X)
    (hrec : ∀ n, W (n + 2) = (C a * X + C b) * W (n + 1) + (C c * X + C d) * W n) :
    (∀ n, (W n).Splits) ↔ a * d ≤ b * c := by
  refine ⟨fun h => ?_, fun h n => splits_of_affine_two_step ha hb hc hd h W h0 h1 hrec n⟩
  by_contra hlt
  obtain ⟨n, hn⟩ :=
    exists_not_splits_of_affine_two_step ha hb hc hd (lt_of_not_ge hlt) W h0 h1 hrec
  exact hn (h n)

end RealRooted.WangZhang

