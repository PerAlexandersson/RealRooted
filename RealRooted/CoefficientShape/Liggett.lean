import RealRooted.CoefficientShape
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Liggett's theorem

T. M. Liggett, *Ultra logconcave sequences and negative dependence*, J. Combin. Theory Ser. A 79
(1997), 315–325: the convolution of a sequence that is ultra-log-concave of order `m` with one
that is ultra-log-concave of order `n` is ultra-log-concave of order `m + n`.  Here a nonnegative
sequence supported on `[0, d]` is ultra-log-concave of order `d` if `a_k / C(d, k)` is
log-concave without internal zeros (`CoeffUltraLogConcaveUpTo` with `CoeffNoInternalZerosUpTo`).
This strengthens Hoggar's theorem (`RealRooted.coeffLogConcaveUpTo_mul`).

The proof is elementary; it was found with the Aristotle prover (Harmonic) and is not Liggett's
original argument.  It proceeds by induction on `n`: the order-`(n+1)` factor is split into two
"partial derivatives" of order `n`, which are likelihood-ratio ordered; convolution with a
log-concave sequence preserves this ordering (a `2 × 2` Cauchy–Binet argument, as for Hoggar),
and a real-number inequality merges the two induction hypotheses.
-/

open Polynomial Finset

namespace RealRooted

namespace Liggett

/-- Nonnegative sequence supported on `[0, d]`, without internal zeros, and ultra-log-concave
of order `d`. -/
private def IsULC (d : ℕ) (a : ℕ → ℝ) : Prop :=
  (∀ k, 0 ≤ a k) ∧ (∀ k, d < k → a k = 0) ∧
  (∀ i j k, i < j → j < k → a i ≠ 0 → a k ≠ 0 → a j ≠ 0) ∧
  (∀ k, 0 < k → k < d →
    a (k - 1) * a (k + 1) * ((k + 1 : ℝ) * ((d - k + 1 : ℕ) : ℝ)) ≤
      a k ^ 2 * ((k : ℝ) * ((d - k : ℕ) : ℝ)))


/-!
## Proof outline

The clauses "nonnegative", "support in `[0, m+n]`" and "no internal zeros" are proved
directly (`conv_nonneg`, `conv_support`, `conv_noIntZeros`).  The ULC inequality
(`conv_ulcIneq`) is proved by induction on `n`:

* write `b * (n+1) = dR b n + X * dL b`, where `dR`, `dL` are the two "partial derivatives"
  of `b`, both ULC of order `n` (`isULC_dR`, `isULC_dL`, `conv_decomp`);
* by induction `p = a * dR b n` and `q = a * dL b` satisfy the ULC inequalities of order `m+n`;
* the pairs `(dL b, dR b n)` and `(dR b n, X * dL b)` are likelihood-ratio ordered (`h1_b`,
  `h2_b`, using the factorial reformulation `xf` and its log-concavity), and convolution with
  the log-concave sequence `a` preserves this (`conv_tp2`, a Cauchy–Binet argument using the
  spread inequality `spread`);
* a real-number inequality (`merge_core`) then shows that `p + X q` satisfies the ULC
  inequalities of order `m+n+1` (`merge`).
-/

/-- Convolution of two sequences (the sequence appearing in `liggett`). -/
private def conv (a b : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range (k + 1), a i * b (k - i)

/-- Shift of a sequence one step to the right (multiplication of the generating function by `X`). -/
private def sh (v : ℕ → ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else v (k - 1)

/-- The "no internal zeros" clause of `IsULC`. -/
private def NoIntZeros (a : ℕ → ℝ) : Prop :=
  ∀ i j k, i < j → j < k → a i ≠ 0 → a k ≠ 0 → a j ≠ 0

/-- The ULC inequality clause of `IsULC`. -/
private def ULCIneq (d : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ k, 0 < k → k < d →
    a (k - 1) * a (k + 1) * ((k + 1 : ℝ) * ((d - k + 1 : ℕ) : ℝ)) ≤
      a k ^ 2 * ((k : ℝ) * ((d - k : ℕ) : ℝ))

/-! ### (1) nonnegativity and (2) support -/

private theorem conv_nonneg {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (k : ℕ) :
    0 ≤ conv a b k :=
  sum_nonneg fun i _ => mul_nonneg (ha i) (hb _)

private theorem conv_support {m n : ℕ} {a b : ℕ → ℝ} (ha : ∀ k, m < k → a k = 0)
    (hb : ∀ k, n < k → b k = 0) (k : ℕ) (hk : m + n < k) : conv a b k = 0 := by
  unfold conv
  refine sum_eq_zero fun i hi => ?_
  by_cases h : m < i
  · rw [ha i h, zero_mul]
  · rw [hb (k - i) (by lia), mul_zero]

/-! ### (3) no internal zeros -/

private theorem ne_zero_of_between {f : ℕ → ℝ} (hf : NoIntZeros f) {p q t : ℕ}
    (hp : f p ≠ 0) (hq : f q ≠ 0) (h1 : p ≤ t) (h2 : t ≤ q) : f t ≠ 0 := by
  rcases h1.lt_or_eq with h1 | rfl
  · rcases h2.lt_or_eq with h2 | rfl
    · exact hf _ _ _ h1 h2 hp hq
    · exact hq
  · exact hp

private theorem conv_ne_zero_iff {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (k : ℕ) :
    conv a b k ≠ 0 ↔ ∃ i ≤ k, a i ≠ 0 ∧ b (k - i) ≠ 0 := by
  unfold conv
  rw [Ne, sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (ha i) (hb _))]
  push Not
  simp only [mem_range, Nat.lt_succ_iff, ne_eq, mul_eq_zero, not_or]

private theorem conv_noIntZeros {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hai : NoIntZeros a) (hbi : NoIntZeros b) : NoIntZeros (conv a b) := by
  intro i j k hij hjk hi hk
  obtain ⟨t1, ht1, ha1, hb1⟩ := (conv_ne_zero_iff ha hb i).1 hi
  obtain ⟨t2, ht2, ha2, hb2⟩ := (conv_ne_zero_iff ha hb k).1 hk
  rw [conv_ne_zero_iff ha hb]
  rcases le_or_gt t1 t2 with h | h
  · by_cases hc : t1 + (j - i) ≤ t2
    · refine ⟨t1 + (j - i), by lia, ne_zero_of_between hai ha1 ha2 (by lia) hc, ?_⟩
      have e : j - (t1 + (j - i)) = i - t1 := by lia
      rw [e]; exact hb1
    · exact ⟨t2, by lia, ha2, ne_zero_of_between hbi hb1 hb2 (by lia) (by lia)⟩
  · exact ⟨t2, by lia, ha2, ne_zero_of_between hbi hb1 hb2 (by lia) (by lia)⟩

/-! ### Spread inequality for log-concave sequences without internal zeros -/

private theorem ratio_step {f : ℕ → ℝ} (hlc : ∀ k, f k * f (k + 2) ≤ f (k + 1) ^ 2) (p : ℕ) :
    ∀ d, (∀ t, p ≤ t → t ≤ p + d + 1 → 0 < f t) →
      f p * f (p + d + 1) ≤ f (p + 1) * f (p + d) := by
  intro d
  induction d with
  | zero => intro _; simp [mul_comm]
  | succ d ih =>
    intro hpos
    have ih' := ih (fun t h1 h2 => hpos t h1 (by lia))
    have h1 := hlc (p + d)
    have hq : 0 < f (p + d + 1) := hpos _ (by lia) (by lia)
    have hp1 : 0 ≤ f (p + 1) := (hpos _ (by lia) (by lia)).le
    have hr0 : 0 ≤ f (p + d + 2) := (hpos _ (by lia) (by lia)).le
    have e1 : p + (d + 1) + 1 = p + d + 2 := by ring
    have e2 : p + (d + 1) = p + d + 1 := by ring
    rw [e1, e2]
    refine le_of_mul_le_mul_left ?_ hq
    nlinarith [mul_le_mul_of_nonneg_right ih' hr0, mul_le_mul_of_nonneg_left h1 hp1]

private theorem spread_pos {f : ℕ → ℝ} (hlc : ∀ k, f k * f (k + 2) ≤ f (k + 1) ^ 2) :
    ∀ d p s, (∀ t, p ≤ t → t ≤ s → 0 < f t) → ∀ q r, q = p + d → q ≤ r → r ≤ s →
      p + s = q + r → f p * f s ≤ f q * f r := by
  intro d
  induction d with
  | zero =>
    intro p s _ q r hq _ _ h
    have : r = s := by lia
    subst this; subst hq; rfl
  | succ d ih =>
    intro p s hpos q r hq hqr hrs h
    have hstep := ratio_step hlc p (s - p - 1) (fun t h1 h2 => hpos t h1 (by lia))
    have e1 : p + (s - p - 1) + 1 = s := by lia
    have e2 : p + (s - p - 1) = s - 1 := by lia
    rw [e1, e2] at hstep
    have := ih (p + 1) (s - 1) (fun t h1 h2 => hpos t (by lia) (by lia)) q r (by lia)
      hqr (by lia) (by lia)
    linarith

private theorem spread {f : ℕ → ℝ} (hnn : ∀ k, 0 ≤ f k) (hlc : ∀ k, f k * f (k + 2) ≤ f (k + 1) ^ 2)
    (hnz : NoIntZeros f) {p q r s : ℕ} (hpq : p ≤ q) (hpr : p ≤ r) (hqs : q ≤ s) (hrs : r ≤ s)
    (h : p + s = q + r) : f p * f s ≤ f q * f r := by
  by_cases h0 : f p = 0 ∨ f s = 0
  · rcases h0 with h0 | h0 <;> rw [h0] <;> simp [mul_nonneg (hnn q) (hnn r)]
  push Not at h0
  have hpos : ∀ t, p ≤ t → t ≤ s → 0 < f t := fun t h1 h2 =>
    lt_of_le_of_ne (hnn t) (Ne.symm (ne_zero_of_between hnz h0.1 h0.2 h1 h2))
  rcases le_total q r with hqr | hqr
  · exact spread_pos hlc (q - p) p s hpos q r (by lia) hqr hrs h
  · rw [mul_comm (f q)]
    exact spread_pos hlc (r - p) p s hpos r q (by lia) hqr hqs (by lia)

/-! ### Convolution with a log-concave sequence preserves the likelihood-ratio order -/

/-- Toeplitz kernel of `a`. -/
private def ker (a : ℕ → ℝ) (k j : ℕ) : ℝ := if j ≤ k then a (k - j) else 0

private theorem conv_eq_ker_sum (a u : ℕ → ℝ) (k L : ℕ) (hL : k < L) :
    conv a u k = ∑ j ∈ range L, ker a k j * u j := by
  have h1 : conv a u k = ∑ j ∈ range (k + 1), ker a k j * u j := by
    unfold conv
    rw [← sum_range_reflect]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    unfold ker
    rw [ite_eq_left (by lia)]
    have e1 : k + 1 - 1 - j = k - j := by lia
    have e2 : k - (k - j) = j := by lia
    rw [e1, e2]
  rw [h1]
  refine sum_subset (range_subset_range.2 (by lia)) fun j _ hj => ?_
  rw [mem_range] at hj
  unfold ker
  rw [ite_eq_right (by lia), zero_mul]

private theorem ker_tp2 {a : ℕ → ℝ} (ha0 : ∀ k, 0 ≤ a k)
    (hsp : ∀ p q r s, p ≤ q → p ≤ r → q ≤ s → r ≤ s → p + s = q + r → a p * a s ≤ a q * a r)
    {k l i j : ℕ} (hkl : k < l) (hij : i < j) :
    ker a l i * ker a k j ≤ ker a k i * ker a l j := by
  unfold ker
  by_cases hjk : j ≤ k
  · rw [ite_eq_left (by lia), ite_eq_left hjk, ite_eq_left (by lia), ite_eq_left (by lia)]
    have := hsp (k - j) (k - i) (l - j) (l - i) (by lia) (by lia) (by lia) (by lia)
      (by lia)
    linarith [mul_comm (a (l - i)) (a (k - j))]
  · rw [ite_eq_right hjk, mul_zero]
    apply mul_nonneg <;> split_ifs <;> simp [ha0]

private theorem conv_tp2 {a u v : ℕ → ℝ} (ha0 : ∀ k, 0 ≤ a k)
    (hsp : ∀ p q r s, p ≤ q → p ≤ r → q ≤ s → r ≤ s → p + s = q + r → a p * a s ≤ a q * a r)
    (huv : ∀ i j, i < j → u j * v i ≤ u i * v j) {k l : ℕ} (hkl : k < l) :
    conv a u l * conv a v k ≤ conv a u k * conv a v l := by
  rw [conv_eq_ker_sum a u l (l + 1) (by lia), conv_eq_ker_sum a v k (l + 1) (by lia),
    conv_eq_ker_sum a u k (l + 1) (by lia), conv_eq_ker_sum a v l (l + 1) (by lia)]
  set L := l + 1
  set K : ℕ → ℕ → ℝ := fun i j => ker a k i * ker a l j - ker a l i * ker a k j with hK
  have hdiff : (∑ i ∈ range L, ker a k i * u i) * (∑ j ∈ range L, ker a l j * v j) -
      (∑ i ∈ range L, ker a l i * u i) * (∑ j ∈ range L, ker a k j * v j) =
      ∑ i ∈ range L, ∑ j ∈ range L, K i j * (u i * v j) := by
    rw [sum_mul_sum, sum_mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [hK]; ring
  have hsym : 2 * (∑ i ∈ range L, ∑ j ∈ range L, K i j * (u i * v j)) =
      ∑ i ∈ range L, ∑ j ∈ range L, K i j * (u i * v j - u j * v i) := by
    have hc : ∑ i ∈ range L, ∑ j ∈ range L, K i j * (u i * v j) =
        ∑ i ∈ range L, ∑ j ∈ range L, K j i * (u j * v i) := sum_comm
    rw [two_mul]
    nth_rewrite 2 [hc]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [hK]; ring
  have key : ∀ i j, 0 ≤ K i j * (u i * v j - u j * v i) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · apply mul_nonneg
      · simp only [hK]; linarith [ker_tp2 ha0 hsp hkl hij]
      · linarith [huv i j hij]
    · simp
    · apply mul_nonneg_of_nonpos_of_nonpos
      · simp only [hK]; linarith [ker_tp2 ha0 hsp hkl hij]
      · linarith [huv j i hij]
  have hnn : 0 ≤ ∑ i ∈ range L, ∑ j ∈ range L, K i j * (u i * v j) := by
    have : 0 ≤ ∑ i ∈ range L, ∑ j ∈ range L, K i j * (u i * v j - u j * v i) :=
      sum_nonneg fun i _ => sum_nonneg fun j _ => key i j
    linarith
  linarith


/-! ### The merging step -/

/-- Real-number core of the merging step. -/
private theorem merge_core {K R A B C a b c : ℝ} (hK : 1 ≤ K) (hR : 1 ≤ R)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hp : A * C * ((K + 1) * R) ≤ B ^ 2 * (K * (R - 1)))
    (hq : a * c * (K * (R + 1)) ≤ b ^ 2 * ((K - 1) * R))
    (h1 : A * c ≤ B * b) (h2 : a * C ≤ A * c) :
    (A + a) * (C + c) * ((K + 1) * (R + 1)) ≤ (B + b) ^ 2 * (K * R) := by
  have hKR : 0 < K * R := by positivity
  have hx0 : 0 ≤ A * c := mul_nonneg hA hc
  have hy0 : 0 ≤ a * C := mul_nonneg ha hC
  have hprod : (A * C * ((K + 1) * R)) * (a * c * (K * (R + 1))) ≤
      (B ^ 2 * (K * (R - 1))) * (b ^ 2 * ((K - 1) * R)) :=
    mul_le_mul hp hq (by positivity)
      (mul_nonneg (sq_nonneg B) (mul_nonneg (by linarith) (by linarith)))
  have hxy : (A * c) * (a * C) * ((K + 1) * (R + 1)) ≤ (B * b) ^ 2 * ((K - 1) * (R - 1)) := by
    refine le_of_mul_le_mul_left ?_ hKR
    linear_combination hprod
  have hE3 : (K + 1) * (R + 1) * (A * c + a * C) ≤ (2 * K * R + 2) * (B * b) := by
    rcases (mul_nonneg hB hb).lt_or_eq with hs | hs
    · have h3 : (B * b) * (A * c + a * C) ≤ (B * b) ^ 2 + (A * c) * (a * C) := by
        nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (h2.trans h1))]
      refine le_of_mul_le_mul_left ?_ hs
      nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ (K + 1) * (R + 1))]
    · have hx : A * c = 0 := by linarith
      have hy : a * C = 0 := by linarith
      rw [hx, hy, ← hs]; simp
  refine le_of_mul_le_mul_left ?_ hKR
  nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ K * (R + 1)),
    mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ R * (K + 1)),
    mul_le_mul_of_nonneg_left hE3 hKR.le, sq_nonneg (K * B - R * b)]

private theorem sh_nonneg {q : ℕ → ℝ} (hq : ∀ k, 0 ≤ q k) (k : ℕ) : 0 ≤ sh q k := by
  unfold sh; split_ifs <;> simp [hq]

/-- Merging step: if `p, q` satisfy the ULC inequalities of order `M` and are suitably
interlaced, then `p + X q` satisfies the ULC inequalities of order `M + 1`. -/
private theorem merge {M : ℕ} {p q : ℕ → ℝ} (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k)
    (hpM : p (M + 1) = 0) (hpu : ULCIneq M p) (hqu : ULCIneq M q)
    (h1 : ∀ i j, i < j → q j * p i ≤ q i * p j)
    (h2 : ∀ i j, i < j → sh q i * p j ≤ sh q j * p i) :
    ULCIneq (M + 1) (fun k => p k + sh q k) := by
  intro k hk0 hkM
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
  obtain ⟨r, hr⟩ : ∃ r, M = j + 1 + r := ⟨M - (j + 1), by lia⟩
  have e2 : (M + 1 - (j + 1) : ℕ) = r + 1 := by lia
  have hsh1 : sh q (j + 1) = q j := by simp [sh]
  have hsh2 : sh q (j + 1 + 1) = q (j + 1) := by simp [sh]
  simp only [add_tsub_cancel_right, e2, hsh1, hsh2]
  have hp' : p j * p (j + 1 + 1) * (((j : ℝ) + 1 + 1) * ((r : ℝ) + 1)) ≤
      p (j + 1) ^ 2 * (((j : ℝ) + 1) * ((r : ℝ) + 1 - 1)) := by
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · have : p (j + 1 + 1) = 0 := by rw [show j + 1 + 1 = M + 1 by lia]; exact hpM
      rw [this, hr0]; simp
    · have h := hpu (j + 1) (by lia) (by lia)
      have e4 : (M - (j + 1) : ℕ) = r := by lia
      simp only [add_tsub_cancel_right, e4] at h
      push_cast at h
      linear_combination h
  have hq' : sh q j * q (j + 1) * (((j : ℝ) + 1) * ((r : ℝ) + 1 + 1)) ≤
      q j ^ 2 * (((j : ℝ) + 1 - 1) * ((r : ℝ) + 1)) := by
    rcases j with _ | i
    · simp [sh]
    · have h := hqu (i + 1) (by lia) (by lia)
      have e4 : (M - (i + 1) : ℕ) = r + 1 := by lia
      simp only [add_tsub_cancel_right, e4] at h
      have hsh : sh q (i + 1) = q i := by simp [sh]
      rw [hsh]
      push_cast at h ⊢
      linear_combination h
  have h1' : p j * q (j + 1) ≤ p (j + 1) * q j := by
    have := h1 j (j + 1) (by lia); linarith [mul_comm (p j) (q (j + 1)), mul_comm (p (j + 1)) (q j)]
  have h2' : sh q j * p (j + 1 + 1) ≤ p j * q (j + 1) := by
    have := h2 j (j + 1 + 1) (by lia)
    rw [hsh2] at this; linarith [mul_comm (p j) (q (j + 1))]
  have hcore := merge_core (K := (j : ℝ) + 1) (R := (r : ℝ) + 1)
    (by linarith [(j.cast_nonneg : (0:ℝ) ≤ j)])
    (by linarith [(r.cast_nonneg : (0:ℝ) ≤ r)]) (hp0 j) (hp0 (j + 1)) (hp0 (j + 1 + 1))
    (sh_nonneg hq0 j) (hq0 j) (hq0 (j + 1)) hp' hq' h1' h2'
  push_cast
  linear_combination hcore

/-! ### The two "derivatives" of a ULC sequence -/

/-- `∂_y`-type derivative: `b j * (n + 1 - j)`. -/
private def dR (b : ℕ → ℝ) (n : ℕ) (j : ℕ) : ℝ := b j * ((n + 1 - j : ℕ) : ℝ)

/-- `∂_x`-type derivative: `b (j + 1) * (j + 1)`. -/
private def dL (b : ℕ → ℝ) (j : ℕ) : ℝ := b (j + 1) * ((j + 1 : ℕ) : ℝ)

private theorem lc_of_ulc {d : ℕ} {a : ℕ → ℝ} (ha : IsULC d a) (k : ℕ) :
    a k * a (k + 2) ≤ a (k + 1) ^ 2 := by
  by_cases hk : k + 1 < d
  · obtain ⟨r, hr⟩ : ∃ r, d = k + 1 + r + 1 := ⟨d - k - 2, by lia⟩
    have h := ha.2.2.2 (k + 1) (by lia) hk
    have e4 : (d - (k + 1) : ℕ) = r + 1 := by lia
    simp only [add_tsub_cancel_right, e4] at h
    push_cast at h
    have hpos : (0:ℝ) < ((k:ℝ) + 1 + 1) * ((r:ℝ) + 2) := by positivity
    have hsq := sq_nonneg (a (k + 1))
    nlinarith [mul_nonneg hsq (by positivity : (0:ℝ) ≤ (k : ℝ) + (r : ℝ) + 3)]
  · rw [ha.2.1 (k + 2) (by lia), mul_zero]; positivity

private theorem isULC_dR {n : ℕ} {b : ℕ → ℝ} (hb : IsULC (n + 1) b) : IsULC n (dR b n) := by
  obtain ⟨hnn, hsupp, hnz, hulc⟩ := hb
  refine ⟨fun k => mul_nonneg (hnn k) (Nat.cast_nonneg _), fun k hk => ?_, ?_, ?_⟩
  · simp [dR, show n + 1 - k = 0 by lia]
  · intro i j k hij hjk hi hk
    simp only [dR, ne_eq, mul_eq_zero, not_or, Nat.cast_eq_zero] at hi hk ⊢
    exact ⟨hnz i j k hij hjk hi.1 hk.1, by lia⟩
  · intro k hk0 hkn
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
    obtain ⟨r, hr⟩ : ∃ r, n = j + 1 + r + 1 := ⟨n - j - 2, by lia⟩
    have h := hulc (j + 1) (by lia) (by lia)
    simp only [add_tsub_cancel_right] at h
    simp only [dR, add_tsub_cancel_right]
    rw [show n + 1 - (j + 1) + 1 = r + 3 by lia, show n + 1 - (j + 1) = r + 2 by lia] at h
    rw [show n + 1 - j = r + 3 by lia, show n + 1 - (j + 1 + 1) = r + 1 by lia,
      show n - (j + 1) + 1 = r + 2 by lia, show n + 1 - (j + 1) = r + 2 by lia,
      show n - (j + 1) = r + 1 by lia]
    push_cast at h ⊢
    have := mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ) ≤ ((r:ℝ) + 1) * ((r:ℝ) + 2))
    linear_combination this

private theorem isULC_dL {n : ℕ} {b : ℕ → ℝ} (hb : IsULC (n + 1) b) : IsULC n (dL b) := by
  obtain ⟨hnn, hsupp, hnz, hulc⟩ := hb
  refine ⟨fun k => mul_nonneg (hnn _) (Nat.cast_nonneg _), fun k hk => ?_, ?_, ?_⟩
  · simp [dL, hsupp (k + 1) (by lia)]
  · intro i j k hij hjk hi hk
    simp only [dL, ne_eq, mul_eq_zero, not_or, Nat.cast_eq_zero] at hi hk ⊢
    exact ⟨hnz (i + 1) (j + 1) (k + 1) (by lia) (by lia) hi.1 hk.1, by lia⟩
  · intro k hk0 hkn
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
    obtain ⟨r, hr⟩ : ∃ r, n = j + 1 + r + 1 := ⟨n - j - 2, by lia⟩
    have h := hulc (j + 1 + 1) (by lia) (by lia)
    simp only [add_tsub_cancel_right] at h
    simp only [dL, add_tsub_cancel_right]
    rw [show n + 1 - (j + 1 + 1) + 1 = r + 2 by lia,
      show n + 1 - (j + 1 + 1) = r + 1 by lia] at h
    rw [show n - (j + 1) + 1 = r + 2 by lia, show n - (j + 1) = r + 1 by lia]
    push_cast at h ⊢
    have := mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ) ≤ ((j:ℝ) + 1) * ((j:ℝ) + 2))
    linear_combination this

private theorem sh_dL (b : ℕ → ℝ) (t : ℕ) : sh (dL b) t = b t * (t : ℝ) := by
  cases t with
  | zero => simp [sh]
  | succ t => simp [sh, dL]

private theorem decomp {n : ℕ} {b : ℕ → ℝ} (hb : IsULC (n + 1) b) (t : ℕ) :
    b t * ((n : ℝ) + 1) = dR b n t + sh (dL b) t := by
  rw [sh_dL, dR]
  by_cases ht : t ≤ n + 1
  · rw [Nat.cast_sub ht]; push_cast; ring
  · rw [hb.2.1 t (by lia)]; simp

/-- Factorial reformulation `x t = b t * t! * (d - t)!`. -/
private def xf (b : ℕ → ℝ) (d : ℕ) (t : ℕ) : ℝ := b t * (t.factorial : ℝ) * ((d - t).factorial : ℝ)

private theorem xf_lc {d : ℕ} {b : ℕ → ℝ} (hb : IsULC d b) (k : ℕ) :
    xf b d k * xf b d (k + 2) ≤ xf b d (k + 1) ^ 2 := by
  by_cases hk : k + 2 ≤ d
  · obtain ⟨r, hr⟩ : ∃ r, d = k + 2 + r := ⟨d - k - 2, by lia⟩
    have h := hb.2.2.2 (k + 1) (by lia) (by lia)
    simp only [add_tsub_cancel_right] at h
    rw [show d - (k + 1) + 1 = r + 2 by lia, show d - (k + 1) = r + 1 by lia] at h
    simp only [xf]
    rw [show d - k = r + 2 by lia, show d - (k + 2) = r by lia,
      show d - (k + 1) = r + 1 by lia]
    simp only [Nat.factorial_succ]
    push_cast at h ⊢
    have := mul_le_mul_of_nonneg_right h (by positivity :
      (0:ℝ) ≤ ((k:ℝ) + 1) * ((r:ℝ) + 1) * (k.factorial : ℝ) ^ 2 * (r.factorial : ℝ) ^ 2)
    linear_combination this
  · simp only [xf, hb.2.1 (k + 2) (by lia), zero_mul, mul_zero]; positivity

private theorem xf_nonneg {d : ℕ} {b : ℕ → ℝ} (hb : IsULC d b) (t : ℕ) : 0 ≤ xf b d t := by
  unfold xf; have := hb.1 t; positivity

private theorem xf_noIntZeros {d : ℕ} {b : ℕ → ℝ} (hb : IsULC d b) : NoIntZeros (xf b d) := by
  intro i j k hij hjk hi hk
  simp only [xf, ne_eq, mul_eq_zero, not_or, Nat.cast_eq_zero] at hi hk ⊢
  exact ⟨⟨hb.2.2.1 i j k hij hjk hi.1.1 hk.1.1, Nat.factorial_ne_zero _⟩, Nat.factorial_ne_zero _⟩

private theorem h1_b {n : ℕ} {b : ℕ → ℝ} (hb : IsULC (n + 1) b) :
    ∀ i j, i < j → dL b j * dR b n i ≤ dL b i * dR b n j := by
  intro i j hij
  have hnn := hb.1
  by_cases hj : j ≤ n
  · have hx := spread (xf_nonneg hb) (xf_lc hb) (xf_noIntZeros hb)
      (p := i) (q := i + 1) (r := j) (s := j + 1) (by lia) (by lia) (by lia) (by lia)
      (by lia)
    simp only [xf] at hx
    rw [show n + 1 - i = (n - i) + 1 by lia, show n + 1 - (j + 1) = n - j by lia,
      show n + 1 - (i + 1) = n - i by lia, show n + 1 - j = (n - j) + 1 by lia] at hx
    simp only [Nat.factorial_succ] at hx
    simp only [dL, dR]
    rw [show n + 1 - i = (n - i) + 1 by lia, show n + 1 - j = (n - j) + 1 by lia]
    push_cast at hx ⊢
    have hΦ : (0:ℝ) < (i.factorial : ℝ) * ((n - i).factorial : ℝ) * (j.factorial : ℝ) *
        ((n - j).factorial : ℝ) := by positivity
    refine le_of_mul_le_mul_right ?_ hΦ
    linear_combination hx
  · simp only [dL, dR, hb.2.1 (j + 1) (by lia), zero_mul]
    have := hnn (i + 1); have := hnn i; have := hnn j
    positivity

private theorem h2_b {n : ℕ} {b : ℕ → ℝ} (hb : IsULC (n + 1) b) :
    ∀ i j, i < j → dR b n j * sh (dL b) i ≤ dR b n i * sh (dL b) j := by
  intro i j hij
  rw [sh_dL, sh_dL]
  simp only [dR]
  by_cases hj : j ≤ n + 1
  · rw [Nat.cast_sub hj, Nat.cast_sub (by lia)]
    push_cast
    have hij' : (i : ℝ) < j := by exact_mod_cast hij
    have := mul_nonneg (mul_nonneg (hb.1 i) (hb.1 j))
      (by nlinarith : (0:ℝ) ≤ ((n : ℝ) + 1) * ((j : ℝ) - i))
    linear_combination this
  · rw [hb.2.1 j (by lia)]; simp

/-! ### Convolution identities -/

private theorem conv_sh (a v : ℕ → ℝ) (k : ℕ) : conv a (sh v) k = sh (conv a v) k := by
  cases k with
  | zero => simp [conv, sh]
  | succ k =>
    simp only [sh, conv, Nat.succ_ne_zero, ite_false, add_tsub_cancel_right]
    rw [sum_range_succ]
    simp only [Nat.sub_self, ite_true, mul_zero, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [ite_eq_right (by lia), show k + 1 - i - 1 = k - i by lia]

private theorem conv_decomp {n : ℕ} {b : ℕ → ℝ} (hb : IsULC (n + 1) b) (a : ℕ → ℝ) (k : ℕ) :
    conv a b k * ((n : ℝ) + 1) = conv a (dR b n) k + sh (conv a (dL b)) k := by
  rw [← conv_sh]
  unfold conv
  rw [sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_assoc, decomp hb, mul_add]

private theorem conv_of_deg0 {a b : ℕ → ℝ} (hb : ∀ k, 0 < k → b k = 0) (k : ℕ) :
    conv a b k = a k * b 0 := by
  unfold conv
  rw [sum_eq_single_of_mem k (mem_range.2 (by lia))]
  · rw [Nat.sub_self]
  · intro i hi hik
    rw [mem_range] at hi
    rw [hb (k - i) (by lia), mul_zero]

private theorem ulcIneq_of_mul {d : ℕ} {f : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ULCIneq d (fun k => f k * c)) : ULCIneq d f := by
  intro k hk0 hkd
  have h' := h k hk0 hkd
  simp only at h'
  have hc2 : 0 < c ^ 2 := by positivity
  refine le_of_mul_le_mul_left ?_ hc2
  linear_combination h'

/-! ### (4) The ULC inequality, by induction on `n` -/

private theorem conv_ulcIneq {m : ℕ} {a : ℕ → ℝ} (ha : IsULC m a) :
    ∀ n (b : ℕ → ℝ), IsULC n b → ULCIneq (m + n) (conv a b) := by
  have hsp : ∀ p q r s, p ≤ q → p ≤ r → q ≤ s → r ≤ s → p + s = q + r →
      a p * a s ≤ a q * a r :=
    fun p q r s h1 h2 h3 h4 h5 => spread ha.1 (lc_of_ulc ha) ha.2.2.1 h1 h2 h3 h4 h5
  intro n
  induction n with
  | zero =>
    intro b hb k hk0 hk
    have hc : ∀ t, conv a b t = a t * b 0 := conv_of_deg0 (fun t ht => hb.2.1 t ht)
    simp only [hc]
    have h := ha.2.2.2 k hk0 (by simpa using hk)
    simp only [add_zero]
    have := mul_le_mul_of_nonneg_right h (sq_nonneg (b 0))
    linear_combination this
  | succ n ih =>
    intro b hb
    have hR := isULC_dR hb
    have hL := isULC_dL hb
    have hmerge : ULCIneq (m + n + 1) (fun k => conv a (dR b n) k + sh (conv a (dL b)) k) :=
      merge (conv_nonneg ha.1 hR.1) (conv_nonneg ha.1 hL.1)
        (conv_support ha.2.1 hR.2.1 _ (by lia)) (ih _ hR) (ih _ hL)
        (fun i j hij => conv_tp2 ha.1 hsp (h1_b hb) hij)
        (fun i j hij => by
          have := conv_tp2 ha.1 hsp (h2_b hb) hij
          rw [conv_sh, conv_sh] at this
          linarith [mul_comm (conv a (dR b n) j) (sh (conv a (dL b)) i),
            mul_comm (conv a (dR b n) i) (sh (conv a (dL b)) j)])
    have heq : (fun k => conv a (dR b n) k + sh (conv a (dL b)) k) =
        fun k => conv a b k * ((n : ℝ) + 1) := funext fun k => (conv_decomp hb a k).symm
    rw [heq] at hmerge
    exact ulcIneq_of_mul (by positivity) hmerge

/-- **Liggett (1997)**, in the packaged form of `IsULC`. -/
private theorem liggett_isULC {m n : ℕ} {a b : ℕ → ℝ} (ha : IsULC m a) (hb : IsULC n b) :
    IsULC (m + n) (fun k => ∑ i ∈ range (k + 1), a i * b (k - i)) :=
  ⟨conv_nonneg ha.1 hb.1, conv_support ha.2.1 hb.2.1,
    conv_noIntZeros ha.1 hb.1 ha.2.2.1 hb.2.2.1, conv_ulcIneq ha n b hb⟩

end Liggett

open Liggett

/-- **Liggett's theorem** for sequences.  If `a` and `b` are nonnegative, supported on `[0, m]`
and `[0, n]`, without internal zeros and ultra-log-concave of orders `m` and `n`, then their
convolution is ultra-log-concave of order `m + n` and has no internal zeros. -/
theorem coeffUltraLogConcaveUpTo_conv {m n : ℕ} {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k)
    (has : ∀ k, m < k → a k = 0) (haulc : CoeffUltraLogConcaveUpTo m a)
    (haniz : CoeffNoInternalZerosUpTo m a) (hb : ∀ k, 0 ≤ b k) (hbs : ∀ k, n < k → b k = 0)
    (hbulc : CoeffUltraLogConcaveUpTo n b) (hbniz : CoeffNoInternalZerosUpTo n b) :
    CoeffUltraLogConcaveUpTo (m + n) (fun k => ∑ i ∈ range (k + 1), a i * b (k - i)) ∧
      CoeffNoInternalZerosUpTo (m + n) (fun k => ∑ i ∈ range (k + 1), a i * b (k - i)) := by
  have hA : IsULC m a := ⟨ha, has, fun i j k hij hjk hi hk => haniz i j k hij hjk
    (not_lt.mp fun h => hk (has k h)) hi hk, haulc⟩
  have hB : IsULC n b := ⟨hb, hbs, fun i j k hij hjk hi hk => hbniz i j k hij hjk
    (not_lt.mp fun h => hk (hbs k h)) hi hk, hbulc⟩
  obtain ⟨-, -, hniz, hulc⟩ := liggett_isULC hA hB
  exact ⟨hulc, fun i j k hij hjk _ hi hk => hniz i j k hij hjk hi hk⟩

/-- **Liggett's theorem** for polynomials: the product of two polynomials whose coefficient
sequences are nonnegative, ultra-log-concave and without internal zeros (up to their degrees)
has ultra-log-concave coefficients. -/
theorem coeffUltraLogConcaveUpTo_mul {p q : ℝ[X]} (hp : ∀ k, 0 ≤ p.coeff k)
    (hpulc : CoeffUltraLogConcaveUpTo p.natDegree p.coeff)
    (hpniz : CoeffNoInternalZerosUpTo p.natDegree p.coeff) (hq : ∀ k, 0 ≤ q.coeff k)
    (hqulc : CoeffUltraLogConcaveUpTo q.natDegree q.coeff)
    (hqniz : CoeffNoInternalZerosUpTo q.natDegree q.coeff) :
    CoeffUltraLogConcaveUpTo (p * q).natDegree (p * q).coeff := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [CoeffUltraLogConcaveUpTo]
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [CoeffUltraLogConcaveUpTo]
  have hcoeff : (p * q).coeff = fun k => ∑ i ∈ range (k + 1), p.coeff i * q.coeff (k - i) := by
    ext k
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => p.coeff i * q.coeff j)]
  rw [hcoeff, natDegree_mul hp0 hq0]
  exact (coeffUltraLogConcaveUpTo_conv hp (fun k hk => coeff_eq_zero_of_natDegree_lt hk) hpulc
    hpniz hq (fun k hk => coeff_eq_zero_of_natDegree_lt hk) hqulc hqniz).1

end RealRooted
