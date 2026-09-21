import RealRooted.JacobiDeformation.WeightNormalization

/-!
# Finite Newton identity

The private finite algebra below is adapted from the completed Aristotle
Pfaff--Saalschutz result.  It contains no local option changes.  Its sole
public use in this module is the equation-(8) adapter at the end.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

namespace NewtonPfaff

/-- `rising x k = x (x+1) ⋯ (x+k-1)`, with `rising x 0 = 1`. -/
noncomputable def rising (x : ℝ) (k : ℕ) : ℝ := ∏ l ∈ Finset.range k, (x + (l : ℝ))

/-- `falling x k = x (x-1) ⋯ (x-k+1)`, with `falling x 0 = 1`. -/
noncomputable def falling (x : ℝ) (k : ℕ) : ℝ := ∏ l ∈ Finset.range k, (x - (l : ℝ))

@[simp] lemma rising_zero (x : ℝ) : rising x 0 = 1 := by simp [rising]

@[simp] lemma falling_zero (x : ℝ) : falling x 0 = 1 := by simp [falling]

lemma rising_succ (x : ℝ) (k : ℕ) : rising x (k + 1) = rising x k * (x + (k : ℝ)) := by
  simp [rising, Finset.prod_range_succ]

lemma falling_succ (x : ℝ) (k : ℕ) : falling x (k + 1) = falling x k * (x - (k : ℝ)) := by
  simp [falling, Finset.prod_range_succ]

/-- Splitting rule for rising factorials. -/
lemma rising_add (x : ℝ) (p q : ℕ) :
    rising x (p + q) = rising x p * rising (x + (p : ℝ)) q := by
  unfold rising
  rw [Finset.prod_range_add]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => by push_cast; ring)

lemma negOnePow_eq_prod (k : ℕ) :
    ((-1 : ℝ)) ^ k = ∏ _l ∈ Finset.range k, (-1 : ℝ) := by
  simp

/-- Reflection: `(-x)^(k rising) = (-1)^k x^(k falling)`. -/
lemma rising_neg (x : ℝ) (k : ℕ) : rising (-x) k = (-1) ^ k * falling x k := by
  unfold rising falling
  rw [negOnePow_eq_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by ring

/-- Reversing a rising factorial. -/
lemma rising_one_sub (y : ℝ) (k : ℕ) :
    rising (1 - y - (k : ℝ)) k = (-1) ^ k * rising y k := by
  unfold rising
  rw [negOnePow_eq_prod, ← Finset.prod_mul_distrib, ← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  have h1 : i + 1 ≤ k := hi
  have h2 : k - 1 - i = k - (i + 1) := by lia
  rw [h2, Nat.cast_sub h1]
  push_cast; ring

/-- A falling factorial at a natural number argument, in terms of binomial coefficients. -/
lemma choose_mul_factorial_eq_falling (j : ℕ) : ∀ k : ℕ, k ≤ j →
    (j.choose k : ℝ) * (k.factorial : ℝ) = falling (j : ℝ) k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro hk
    have hk' : k ≤ j := by lia
    rw [falling_succ, ← ih hk']
    have hnat : j.choose (k + 1) * (k + 1) = j.choose k * (j - k) := Nat.choose_succ_right_eq j k
    have hcast : ((j.choose (k + 1) : ℝ)) * ((k : ℝ) + 1)
        = (j.choose k : ℝ) * ((j : ℝ) - (k : ℝ)) := by
      have := congrArg (fun n : ℕ => (n : ℝ)) hnat
      push_cast [Nat.cast_sub hk'] at this
      linarith [this]
    rw [Nat.factorial_succ]
    push_cast
    nlinarith [hcast]

/-- Chu–Vandermonde convolution for rising factorials. -/
lemma vandermonde (x y : ℝ) (n : ℕ) :
    rising (x + y) n = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * (rising x k * rising y (n - k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [rising_succ, ih]
    have step1 :
        (∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℝ) * (rising x k * rising y (n - k))) *
            (x + y + (n : ℝ)) =
          (∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℝ) * (rising x (k + 1) * rising y (n - k))) +
          ∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℝ) * (rising x k * rising y (n + 1 - k)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
      have hnk : n + 1 - k = (n - k) + 1 := by lia
      have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
        push_cast [Nat.cast_sub hk]; ring
      rw [hnk, rising_succ, rising_succ, hcast]
      ring
    rw [step1]
    have hA' :
        ∑ k ∈ Finset.range (n + 1),
          (n.choose (k + 1) : ℝ) * (rising x (k + 1) * rising y (n - k)) =
        ∑ k ∈ Finset.range n,
          (n.choose (k + 1) : ℝ) * (rising x (k + 1) * rising y (n - k)) := by
      rw [Finset.sum_range_succ]
      simp
    have hB :
        ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * (rising x k * rising y (n + 1 - k)) =
        (∑ k ∈ Finset.range n,
          (n.choose (k + 1) : ℝ) * (rising x (k + 1) * rising y (n - k)))
          + rising y (n + 1) := by
      rw [Finset.sum_range_succ']
      simp
    rw [hB, ← hA', Finset.sum_range_succ'
      (fun k => ((n + 1).choose k : ℝ) * (rising x k * rising y (n + 1 - k))) (n + 1)]
    simp only [Nat.choose_succ_succ, Nat.succ_sub_succ, Nat.cast_add, add_mul,
      Finset.sum_add_distrib, Nat.choose_zero_right, Nat.cast_one, one_mul, rising_zero,
      Nat.succ_eq_add_one, Nat.sub_zero]
    ring

/-- The generic term of the double sum used in the proof of `saalschutz_poly`. -/
noncomputable def Gterm (a b d : ℝ) (n k i : ℕ) : ℝ :=
  (n.choose k : ℝ) * ((n - k).choose i : ℝ) *
    (rising a (k + i) * rising b k * rising d (n - k) * rising (b + d) (n - k - i))

lemma saalschutz_stepA (n : ℕ) (a b c : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
        (rising a k * rising b k * rising (c + (k : ℝ)) (n - k) * rising (c - a - b) (n - k))
      = ∑ k ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (n + 1 - k), Gterm a b (c - a - b) n k i := by
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
  have hc : c + (k : ℝ) = (a + (k : ℝ)) + (b + (c - a - b)) := by ring
  have hr : n - k + 1 = n + 1 - k := by lia
  rw [hc, vandermonde, hr]
  calc (n.choose k : ℝ) * (rising a k * rising b k *
          (∑ i ∈ Finset.range (n + 1 - k), ((n - k).choose i : ℝ) *
            (rising (a + (k : ℝ)) i * rising (b + (c - a - b)) (n - k - i))) *
          rising (c - a - b) (n - k))
      = ((n.choose k : ℝ) * rising a k * rising b k * rising (c - a - b) (n - k)) *
          (∑ i ∈ Finset.range (n + 1 - k), ((n - k).choose i : ℝ) *
            (rising (a + (k : ℝ)) i * rising (b + (c - a - b)) (n - k - i))) := by ring
    _ = ∑ i ∈ Finset.range (n + 1 - k), Gterm a b (c - a - b) n k i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Gterm, rising_add a k i]
        ring

lemma saalschutz_stepC (n j : ℕ) (hj : j ≤ n) (a b d : ℝ) :
    ∑ k ∈ Finset.range (j + 1), Gterm a b d n k (j - k)
      = (n.choose j : ℝ) * (rising a j * rising d (n - j) * rising (b + d) n) := by
  have key : ∀ k ∈ Finset.range (j + 1), Gterm a b d n k (j - k)
      = ((n.choose j : ℝ) * (rising a j * rising d (n - j) * rising (b + d) (n - j)))
        * ((j.choose k : ℝ) * (rising b k * rising (d + ((n - j : ℕ) : ℝ)) (j - k))) := by
    intro k hk
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
    have h1 : k + (j - k) = j := by lia
    have h2 : n - k - (j - k) = n - j := by lia
    have h3 : (n.choose k : ℝ) * (((n - k).choose (j - k) : ℕ) : ℝ)
        = (n.choose j : ℝ) * (j.choose k : ℝ) := by
      have hnat : n.choose j * j.choose k = n.choose k * (n - k).choose (j - k) :=
        Nat.choose_mul hk
      exact_mod_cast hnat.symm
    have h4 : rising d (n - k) = rising d (n - j) * rising (d + ((n - j : ℕ) : ℝ)) (j - k) := by
      have hsplit : (n - j) + (j - k) = n - k := by lia
      rw [← hsplit, rising_add]
    simp only [Gterm, h1, h2, h4]
    linear_combination (rising a j * rising b k * rising d (n - j) *
      rising (d + ((n - j : ℕ) : ℝ)) (j - k) * rising (b + d) (n - j)) * h3
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← vandermonde]
  have h5 :
      rising (b + d) (n - j) * rising (b + (d + ((n - j : ℕ) : ℝ))) j =
        rising (b + d) n := by
    have hx : b + (d + ((n - j : ℕ) : ℝ)) = (b + d) + ((n - j : ℕ) : ℝ) := by ring
    rw [hx, ← rising_add, Nat.sub_add_cancel hj]
  linear_combination ((n.choose j : ℝ) * rising a j * rising d (n - j)) * h5

/-- The Pfaff–Saalschütz theorem in polynomial (denominator-free) form. -/
lemma saalschutz_poly (n : ℕ) (a b c : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
        (rising a k * rising b k * rising (c + (k : ℝ)) (n - k) * rising (c - a - b) (n - k))
      = rising (c - a) n * rising (c - b) n := by
  rw [saalschutz_stepA n a b c,
    ← Finset.sum_range_diag_flip (n + 1) (fun k i => Gterm a b (c - a - b) n k i),
    Finset.sum_congr rfl (fun j hj => saalschutz_stepC n j
      (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj) a b (c - a - b))]
  have hfac : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        (rising a j * rising (c - a - b) (n - j) * rising (b + (c - a - b)) n)
      = (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
          (rising a j * rising (c - a - b) (n - j))) * rising (b + (c - a - b)) n := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfac, ← vandermonde]
  have h1 : a + (c - a - b) = c - b := by ring
  have h2 : b + (c - a - b) = c - a := by ring
  rw [h1, h2, mul_comm]

/-- The requested finite Pfaff–Saalschütz identity: for natural numbers `j ≤ m` and
reals `s > 0`, `0 < delta < 1`,

`∑_{k=0}^{j} (1-delta)^{k rising} · j^{k falling} · (j+s-1)^{k rising} /`
`  ((m+delta-1)^{k falling} · (m+s)^{k rising} · k!)`
`  = m^{j falling} · (m+s-1+delta)^{j rising} / ((m+delta-1)^{j falling} · (m+s)^{j rising})`.

The hypotheses `j ≤ m`, `0 < s` and `0 < delta` guarantee that every denominator is
nonzero (for `k ≤ j ≤ m` the smallest factor of `(m+delta-1)^{k falling}` is
`m-k+delta ≥ delta > 0`). The hypothesis `delta < 1` was requested and is kept, but the
proof does not need it. The boundary cases `j = 0` and `m = 0` are included. -/
theorem sum_eq (m j : ℕ) (hjm : j ≤ m) (s delta : ℝ) (hs : 0 < s)
    (hd0 : 0 < delta) (_hd1 : delta < 1) :
    ∑ k ∈ Finset.range (j + 1),
        (rising (1 - delta) k * falling (j : ℝ) k * rising ((j : ℝ) + s - 1) k) /
          (falling ((m : ℝ) + delta - 1) k * rising ((m : ℝ) + s) k * (k.factorial : ℝ))
      = (falling (m : ℝ) j * rising ((m : ℝ) + s - 1 + delta) j) /
          (falling ((m : ℝ) + delta - 1) j * rising ((m : ℝ) + s) j) := by
  -- positivity of the denominators
  have hposR : ∀ k : ℕ, 0 < rising ((m : ℝ) + s) k := by
    intro k
    refine Finset.prod_pos fun l _ => ?_
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    linarith
  have hposF : ∀ k : ℕ, k ≤ m → 0 < falling ((m : ℝ) + delta - 1) k := by
    intro k hk
    refine Finset.prod_pos fun l hl => ?_
    simp only [Finset.mem_range] at hl
    have h1 : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hl
    have h2 : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
    linarith
  have hsq : ∀ k : ℕ, ((-1 : ℝ)) ^ k * ((-1 : ℝ)) ^ k = 1 := by
    intro k; rw [← mul_pow]; norm_num
  -- the Pfaff–Saalschütz parameters
  set a : ℝ := (j : ℝ) + s - 1 with ha
  set b : ℝ := 1 - delta with hb
  set c : ℝ := 1 - (m : ℝ) - delta with hc
  -- the two "reflection" identities for the `j`-th rising factorials
  have hCj : rising c j = (-1) ^ j * falling ((m : ℝ) + delta - 1) j := by
    have : c = -((m : ℝ) + delta - 1) := by rw [hc]; ring
    rw [this, rising_neg]
  have hDj : rising (c - a - b) j = (-1) ^ j * rising ((m : ℝ) + s) j := by
    have : c - a - b = 1 - ((m : ℝ) + s) - (j : ℝ) := by rw [hc, ha, hb]; ring
    rw [this, rising_one_sub]
  have hCjne : rising c j ≠ 0 := by
    rw [hCj]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (hposF j hjm))
  have hDjne : rising (c - a - b) j ≠ 0 := by
    rw [hDj]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (hposR j))
  -- rewrite every summand as a Pfaff–Saalschütz summand divided by a constant
  have hterm : ∀ k ∈ Finset.range (j + 1),
      (rising b k * falling (j : ℝ) k * rising a k) /
          (falling ((m : ℝ) + delta - 1) k * rising ((m : ℝ) + s) k * (k.factorial : ℝ))
        = ((j.choose k : ℝ) * (rising a k * rising b k * rising (c + (k : ℝ)) (j - k) *
            rising (c - a - b) (j - k))) / (rising c j * rising (c - a - b) j) := by
    intro k hk
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
    have hkm : k ≤ m := le_trans hk hjm
    have hFne : falling ((m : ℝ) + delta - 1) k ≠ 0 := ne_of_gt (hposF k hkm)
    have hRne : rising ((m : ℝ) + s) k ≠ 0 := ne_of_gt (hposR k)
    have hfacne : (k.factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    have e1 : rising c k * rising (c + (k : ℝ)) (j - k) = rising c j := by
      rw [← rising_add]
      congr 1
      lia
    have e2 : rising (c - a - b) (j - k) * ((-1) ^ k * rising ((m : ℝ) + s) k)
        = rising (c - a - b) j := by
      have harg : (c - a - b) + ((j - k : ℕ) : ℝ) = 1 - ((m : ℝ) + s) - (k : ℝ) := by
        have hcast : ((j - k : ℕ) : ℝ) = (j : ℝ) - (k : ℝ) := by
          push_cast [Nat.cast_sub hk]; ring
        rw [hc, ha, hb, hcast]; ring
      have hsplit : rising (c - a - b) ((j - k) + k)
          = rising (c - a - b) (j - k) * rising ((c - a - b) + ((j - k : ℕ) : ℝ)) k :=
        rising_add _ _ _
      rw [harg, rising_one_sub] at hsplit
      rw [← hsplit]
      congr 1
      lia
    have e3 : rising c k = (-1) ^ k * falling ((m : ℝ) + delta - 1) k := by
      have : c = -((m : ℝ) + delta - 1) := by rw [hc]; ring
      rw [this, rising_neg]
    have e4 : (j.choose k : ℝ) * (k.factorial : ℝ) = falling (j : ℝ) k :=
      choose_mul_factorial_eq_falling j k hk
    have e23 : rising c j * rising (c - a - b) j
        = (falling ((m : ℝ) + delta - 1) k * rising ((m : ℝ) + s) k) *
          (rising (c + (k : ℝ)) (j - k) * rising (c - a - b) (j - k)) := by
      rw [← e1, ← e2, e3]
      linear_combination (falling ((m : ℝ) + delta - 1) k * rising ((m : ℝ) + s) k *
        rising (c + (k : ℝ)) (j - k) * rising (c - a - b) (j - k)) * hsq k
    rw [eq_div_iff (mul_ne_zero hCjne hDjne), e23, ← e4]
    field_simp
  have hsum : (∑ k ∈ Finset.range (j + 1), (rising b k * falling (j : ℝ) k * rising a k) /
        (falling ((m : ℝ) + delta - 1) k * rising ((m : ℝ) + s) k * (k.factorial : ℝ)))
      = ∑ k ∈ Finset.range (j + 1),
          ((j.choose k : ℝ) * (rising a k * rising b k * rising (c + (k : ℝ)) (j - k) *
            rising (c - a - b) (j - k))) / (rising c j * rising (c - a - b) j) :=
    Finset.sum_congr rfl hterm
  rw [hsum, ← Finset.sum_div, saalschutz_poly j a b c]
  -- finally, identify the closed form
  have hA : rising (c - a) j = (-1) ^ j * rising ((m : ℝ) + s - 1 + delta) j := by
    have : c - a = 1 - ((m : ℝ) + s - 1 + delta) - (j : ℝ) := by rw [hc, ha]; ring
    rw [this, rising_one_sub]
  have hB : rising (c - b) j = (-1) ^ j * falling (m : ℝ) j := by
    have : c - b = -(m : ℝ) := by rw [hc, hb]; ring
    rw [this, rising_neg]
  rw [hA, hB, hCj, hDj]
  have hFne : falling ((m : ℝ) + delta - 1) j ≠ 0 := ne_of_gt (hposF j hjm)
  have hRne : rising ((m : ℝ) + s) j ≠ 0 := ne_of_gt (hposR j)
  rw [div_eq_div_iff (by rw [← hCj, ← hDj]; exact mul_ne_zero hCjne hDjne)
    (mul_ne_zero hFne hRne)]
  ring

end NewtonPfaff

private theorem NewtonPfaff.rising_eq_risingFactorial (x : ℝ) (n : ℕ) :
    NewtonPfaff.rising x n = risingFactorial x n := by
  induction n with
  | zero => simp [NewtonPfaff.rising]
  | succ n ih =>
      rw [NewtonPfaff.rising_succ, risingFactorial_succ, ih]

private theorem NewtonPfaff.falling_eq_descPochhammer (x : ℝ) (n : ℕ) :
    NewtonPfaff.falling x n = (descPochhammer ℝ n).eval x := by
  rw [NewtonPfaff.falling, descPochhammer_eval_eq_prod_range]

/-- Equation (8): evaluating the Newton polynomial at `λ_j` gives the
corresponding normalized Jacobi kernel weight. -/
theorem sum_newtonExpansionTerm_eq_kernelWeight_div_kernelWeight_zero
    {m j : ℕ} {δ s : ℝ} (hjm : j ≤ m) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hs : 0 < s) :
    ∑ k ∈ Finset.range (j + 1), newtonExpansionTerm m δ s j k =
      kernelWeight m δ s j / kernelWeight m δ s 0 := by
  calc
    ∑ k ∈ Finset.range (j + 1), newtonExpansionTerm m δ s j k =
        ∑ k ∈ Finset.range (j + 1),
          (NewtonPfaff.rising (1 - δ) k * NewtonPfaff.falling (j : ℝ) k *
              NewtonPfaff.rising ((j : ℝ) + s - 1) k) /
            (NewtonPfaff.falling ((m : ℝ) + δ - 1) k *
              NewtonPfaff.rising ((m : ℝ) + s) k * (k.factorial : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [newtonExpansionTerm, newtonCoefficient,
            ← NewtonPfaff.rising_eq_risingFactorial (1 - δ) k,
            ← NewtonPfaff.falling_eq_descPochhammer (j : ℝ) k,
            ← NewtonPfaff.rising_eq_risingFactorial ((j : ℝ) + s - 1) k,
            ← NewtonPfaff.falling_eq_descPochhammer ((m : ℝ) + δ - 1) k,
            ← NewtonPfaff.rising_eq_risingFactorial ((m : ℝ) + s) k]
          ring
    _ = NewtonPfaff.falling (m : ℝ) j *
          NewtonPfaff.rising ((m : ℝ) + s - 1 + δ) j /
        (NewtonPfaff.falling ((m : ℝ) + δ - 1) j *
          NewtonPfaff.rising ((m : ℝ) + s) j) :=
      NewtonPfaff.sum_eq m j hjm s δ hs hδ hδ1
    _ = kernelWeight m δ s j / kernelWeight m δ s 0 := by
      rw [NewtonPfaff.falling_eq_descPochhammer,
        NewtonPfaff.rising_eq_risingFactorial,
        NewtonPfaff.falling_eq_descPochhammer,
        NewtonPfaff.rising_eq_risingFactorial]
      exact (kernelWeight_div_kernelWeight_zero hjm hδ hδ1 hs).symm

end RealRooted.JacobiDeformation
