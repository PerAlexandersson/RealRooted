module

public import Mathlib

/-!
# Wang–Zhang's affine three-term recurrence

We prove the sufficiency direction of Wang–Zhang, arXiv:1712.06105,
Theorem 2.1 (RealRooted issue #2067): every row of the affine recurrence
`W (n + 2) = (a X + b) W (n + 1) + (c X + d) W n` splits over the reals
when `a, b, c, d > 0` and `a d ≤ b c`.

The proof of sufficiency was found by Aristotle (Harmonic).
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
    have := Wseq_leadingCoeff ha.ne' b c d n
    rw [h, leadingCoeff_zero] at this
    exact (pow_ne_zero _ ha.ne') this.symm
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

private lemma prod_lower (z : ℂ) (s : Multiset ℝ) :
    |z.im| ^ Multiset.card s ≤ ‖(s.map (fun x => aeval z (X - C x))).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, norm_mul, mul_comm]
    gcongr
    simp only [map_sub, aeval_X, aeval_C]
    have := Complex.abs_im_le_norm (z - algebraMap ℝ ℂ x)
    simpa using this

private lemma splits_lower_bound (p : ℝ[X]) (hp : p.Splits) (z : ℂ) :
    ‖p.leadingCoeff‖ * |z.im| ^ p.natDegree ≤ ‖aeval z p‖ := by
  have h := hp.eq_prod_roots
  have hc := hp.natDegree_eq_card_roots
  conv_rhs => rw [h]
  rw [hc, map_mul, map_multiset_prod, Multiset.map_map, norm_mul, aeval_C]
  gcongr
  · simp
  · exact prod_lower z _

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

private lemma splits_of_no_nonreal_root (p : ℝ[X]) (h : ∀ z : ℂ, aeval z p = 0 → z.im = 0) :
    p.Splits := by
  obtain ⟨q, hq, hcard, hq0⟩ := exists_prod_multiset_X_sub_C_mul p
  by_cases hp : p = 0
  · simp [hp]
  have hqne : q ≠ 0 := by rintro rfl; simp at hq; exact hp hq.symm
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | h0
  · rw [splits_iff_card_roots]; lia
  exfalso
  obtain ⟨z, hz⟩ := Complex.exists_root (f := q.map (algebraMap ℝ ℂ))
    (by rw [degree_map]; exact natDegree_pos_iff_degree_pos.mp h0)
  have hzq : aeval z q = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
  have hzp : aeval z p = 0 := by rw [← hq, map_mul, hzq, mul_zero]
  have him := h z hzp
  have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [hz'] at hzq
  have h1 : (algebraMap ℝ ℂ) (q.eval z.re) = 0 := by
    rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; exact hzq
  have h2 : q.eval z.re = 0 := by simpa using h1
  have hmem : z.re ∈ q.roots := (mem_roots hqne).mpr h2
  rw [hq0] at hmem
  simp at hmem

private lemma Wseq_splits {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (habcd : a * d ≤ b * c) (n : ℕ) : (Wseq a b c d n).Splits := by
  apply splits_of_no_nonreal_root
  intro z hz
  by_contra him
  have hL : 0 < a ^ (n - 1) * |z.im| ^ n := by
    have : 0 < |z.im| := abs_pos.mpr him
    positivity
  have hbound : ∀ b' : ℝ, b' ∈ Set.Ioi b →
      a ^ (n - 1) * |z.im| ^ n ≤ ‖aeval z (Wseq a b' c d n)‖ := by
    intro b' hb'
    have hb'' : b < b' := hb'
    have hs := Wseq_splits_of_lt ha (hb.trans hb'') hc hd (by nlinarith) n
    have := splits_lower_bound _ hs z
    rwa [Wseq_leadingCoeff ha.ne', Wseq_natDegree ha.ne', Real.norm_eq_abs,
      abs_of_pos (pow_pos ha _)] at this
  have hcont := (Wseq_continuous a c d z n).norm
  have htend : Filter.Tendsto (fun b' => ‖aeval z (Wseq a b' c d n)‖) (nhdsWithin b (Set.Ioi b))
      (nhds ‖aeval z (Wseq a b c d n)‖) :=
    (hcont.tendsto b).mono_left nhdsWithin_le_nhds
  have := ge_of_tendsto htend (eventually_nhdsWithin_of_forall hbound)
  rw [hz, norm_zero] at this
  linarith

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

end RealRooted.WangZhang

