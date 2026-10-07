import RealRooted.CoefficientShape

/-!
# Hoggar's theorem

Hoggar (1974): the product of two polynomials whose coefficient sequences are
nonnegative, log-concave and without internal zeros again has a nonnegative,
log-concave coefficient sequence without internal zeros.

We first show that such a sequence is a Pólya frequency sequence of order two,
in the form `a i * a (j + 1) ≤ a (i + 1) * a j` for `i ≤ j`.  The log-concavity of
the convolution then follows from the `2 × 2` Cauchy–Binet identity for the
product of two Toeplitz matrices, and the absence of internal zeros follows
because the supports of both factors are intervals.
-/

open Polynomial Finset

namespace RealRooted

namespace Hoggar

/-- The convolution of two sequences, matching `Polynomial.coeff_mul`. -/
private def conv (a b : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), a k * b (n - k)

private theorem coeff_mul_eq_conv (p q : ℝ[X]) (n : ℕ) :
    (p * q).coeff n = conv p.coeff q.coeff n := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i * q.coeff j)]
  rfl

/-- A nonnegative log-concave sequence without internal zeros is a Pólya frequency
sequence of order two: `a i * a (j + 1) ≤ a (i + 1) * a j` whenever `i ≤ j`. -/
private theorem mul_le_mul_of_logConcave {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k)
    (hlc : ∀ k, a k * a (k + 2) ≤ a (k + 1) ^ 2)
    (hniz : ∀ i j k, i < j → j < k → a i ≠ 0 → a k ≠ 0 → a j ≠ 0) (i m : ℕ) :
    a i * a (i + m + 1) ≤ a (i + 1) * a (i + m) := by
  induction m with
  | zero => exact (mul_comm _ _).le
  | succ m ih =>
    change a i * a (i + m + 2) ≤ a (i + 1) * a (i + m + 1)
    rcases (ha (i + m + 1)).eq_or_lt with h | h
    · have h0 : a i * a (i + m + 2) = 0 := by
        by_contra hne
        exact hniz i (i + m + 1) (i + m + 2) (by lia) (by lia) (left_ne_zero_of_mul hne)
          (right_ne_zero_of_mul hne) h.symm
      rw [h0]
      exact mul_nonneg (ha _) (ha _)
    · have h1 := mul_le_mul_of_nonneg_right ih (ha (i + m + 2))
      have h2 := mul_le_mul_of_nonneg_left (hlc (i + m)) (ha (i + 1))
      refine le_of_mul_le_mul_left ?_ h
      nlinarith

/-- The `2 × 2` Cauchy–Binet identity, symmetrized over the two summation indices. -/
private theorem two_mul_det_eq (S : Finset ℕ) (f g u v : ℕ → ℝ) :
    2 * ((∑ k ∈ S, f k * u k) * (∑ l ∈ S, g l * v l) -
      (∑ k ∈ S, f k * v k) * (∑ l ∈ S, g l * u l)) =
    ∑ k ∈ S, ∑ l ∈ S, (f k * g l - f l * g k) * (u k * v l - v k * u l) := by
  have h1 : ∑ k ∈ S, ∑ l ∈ S, (f k * g l - f l * g k) * (u k * v l - v k * u l) =
      ∑ k ∈ S, ∑ l ∈ S, f k * g l * (u k * v l - v k * u l) -
      ∑ k ∈ S, ∑ l ∈ S, f l * g k * (u k * v l - v k * u l) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have h2 : ∑ k ∈ S, ∑ l ∈ S, f l * g k * (u k * v l - v k * u l) =
      -∑ k ∈ S, ∑ l ∈ S, f k * g l * (u k * v l - v k * u l) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have h3 : (∑ k ∈ S, f k * u k) * (∑ l ∈ S, g l * v l) -
      (∑ k ∈ S, f k * v k) * (∑ l ∈ S, g l * u l) =
      ∑ k ∈ S, ∑ l ∈ S, f k * g l * (u k * v l - v k * u l) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [h1, h2, h3]
  ring

/-- Cauchy–Binet positivity: if both "matrices" have nonnegative `2 × 2` minors,
so does their product. -/
private theorem det_nonneg (S : Finset ℕ) {f g u v : ℕ → ℝ}
    (hf : ∀ k l, k ≤ l → f l * g k ≤ f k * g l)
    (hu : ∀ k l, k ≤ l → v k * u l ≤ u k * v l) :
    (∑ k ∈ S, f k * v k) * (∑ l ∈ S, g l * u l) ≤
      (∑ k ∈ S, f k * u k) * (∑ l ∈ S, g l * v l) := by
  have key := two_mul_det_eq S f g u v
  have hnn : 0 ≤ ∑ k ∈ S, ∑ l ∈ S, (f k * g l - f l * g k) * (u k * v l - v k * u l) := by
    refine Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => ?_
    rcases le_total k l with h | h
    · exact mul_nonneg (sub_nonneg.2 (hf k l h)) (sub_nonneg.2 (hu k l h))
    · have h1 := hf l k h
      have h2 := hu l k h
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  linarith

private theorem sum_range_ite_mul {x y : ℕ → ℝ} {M r : ℕ} (h : r < M) :
    ∑ k ∈ range M, (if k ≤ r then x (r - k) else 0) * y k = conv y x r := by
  rw [← Finset.sum_range_add_sum_Ico _ (show r + 1 ≤ M by lia)]
  have h1 : ∑ k ∈ Finset.Ico (r + 1) M, (if k ≤ r then x (r - k) else 0) * y k = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' := (Finset.mem_Ico.1 hk).1
    rw [ite_eq_right (by lia), zero_mul]
  rw [h1, add_zero, conv]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [ite_eq_left (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)), mul_comm]

private theorem sum_range_succ_ite_mul {x y : ℕ → ℝ} {M r : ℕ} (h : r < M) :
    ∑ k ∈ range (M + 1), (if k ≤ r + 1 then x (r + 1 - k) else 0) *
      (if k = 0 then 0 else y (k - 1)) = conv y x r := by
  rw [Finset.sum_range_succ', ite_eq_left rfl, mul_zero, add_zero, ← sum_range_ite_mul h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ite_eq_right (by lia : k + 1 ≠ 0), Nat.add_sub_cancel, Nat.add_sub_add_right]
  simp only [add_le_add_iff_right]

/-- Log-concavity of the convolution of two PF₂ sequences. -/
private theorem conv_logConcave {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hpa : ∀ i m, a i * a (i + m + 1) ≤ a (i + 1) * a (i + m))
    (hpb : ∀ i m, b i * b (i + m + 1) ≤ b (i + 1) * b (i + m)) (n : ℕ) :
    conv a b n * conv a b (n + 2) ≤ conv a b (n + 1) ^ 2 := by
  have hf : ∀ k l, k ≤ l →
      (if l ≤ n + 1 then b (n + 1 - l) else 0) *
        (if k ≤ n + 1 + 1 then b (n + 1 + 1 - k) else 0) ≤
      (if k ≤ n + 1 then b (n + 1 - k) else 0) *
        (if l ≤ n + 1 + 1 then b (n + 1 + 1 - l) else 0) := by
    intro k l hkl
    by_cases hl : l ≤ n + 1
    · rw [ite_eq_left hl, ite_eq_left (by lia : k ≤ n + 1 + 1), ite_eq_left (by lia : k ≤ n + 1),
        ite_eq_left (by lia : l ≤ n + 1 + 1)]
      have h := hpb (n + 1 - l) (l - k)
      rw [show n + 1 - l + (l - k) + 1 = n + 1 + 1 - k by lia,
        show n + 1 - l + 1 = n + 1 + 1 - l by lia,
        show n + 1 - l + (l - k) = n + 1 - k by lia] at h
      linarith
    · rw [ite_eq_right hl, zero_mul]
      exact mul_nonneg (ite_nonneg (hb _) le_rfl) (ite_nonneg (hb _) le_rfl)
  have hu : ∀ k l, k ≤ l →
      (if k = 0 then 0 else a (k - 1)) * a l ≤ a k * (if l = 0 then 0 else a (l - 1)) := by
    intro k l hkl
    by_cases hk : k = 0
    · rw [ite_eq_left hk, zero_mul]
      exact mul_nonneg (ha k) (ite_nonneg le_rfl (ha _))
    · rw [ite_eq_right hk, ite_eq_right (by lia : l ≠ 0)]
      have h := hpa (k - 1) (l - k)
      rw [show k - 1 + (l - k) + 1 = l by lia, show k - 1 + 1 = k by lia,
        show k - 1 + (l - k) = l - 1 by lia] at h
      linarith
  have h := det_nonneg (range (n + 3 + 1)) hf hu
  rw [sum_range_succ_ite_mul (by lia : n < n + 3),
    sum_range_ite_mul (by lia : n + 1 + 1 < n + 3 + 1),
    sum_range_ite_mul (by lia : n + 1 < n + 3 + 1),
    sum_range_succ_ite_mul (by lia : n + 1 < n + 3)] at h
  rw [sq]
  exact h

private theorem ne_zero_of_between {a : ℕ → ℝ}
    (hniz : ∀ i j k, i < j → j < k → a i ≠ 0 → a k ≠ 0 → a j ≠ 0)
    (x y z : ℕ) (hx : a x ≠ 0) (hz : a z ≠ 0) (hxy : x ≤ y) (hyz : y ≤ z) :
    a y ≠ 0 := by
  rcases hxy.eq_or_lt with rfl | h1
  · exact hx
  rcases hyz.eq_or_lt with rfl | h2
  · exact hz
  exact hniz x y z h1 h2 hx hz

private theorem conv_ne_zero_iff {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (n : ℕ) :
    conv a b n ≠ 0 ↔ ∃ x y, x + y = n ∧ a x ≠ 0 ∧ b y ≠ 0 := by
  unfold conv
  constructor
  · intro h
    obtain ⟨k, hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hk' := Finset.mem_range.1 hk
    exact ⟨k, n - k, by lia, left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩
  · rintro ⟨x, y, rfl, hx, hy⟩
    refine (Finset.sum_pos' (fun k _ => mul_nonneg (ha k) (hb _))
      ⟨x, Finset.mem_range.2 (by lia), ?_⟩).ne'
    rw [Nat.add_sub_cancel_left]
    exact mul_pos ((ha x).lt_of_ne hx.symm) ((hb y).lt_of_ne hy.symm)

private theorem exists_pair_of_le {a b : ℕ → ℝ}
    (hA : ∀ x y z, a x ≠ 0 → a z ≠ 0 → x ≤ y → y ≤ z → a y ≠ 0)
    (hB : ∀ x y z, b x ≠ 0 → b z ≠ 0 → x ≤ y → y ≤ z → b y ≠ 0)
    {x₁ y₁ x₂ y₂ j : ℕ} (ha₁ : a x₁ ≠ 0) (ha₂ : a x₂ ≠ 0) (hb₁ : b y₁ ≠ 0)
    (hb₂ : b y₂ ≠ 0) (h₁ : x₁ + y₁ ≤ j) (h₂ : j ≤ x₂ + y₂) :
    ∃ x y, x + y = j ∧ a x ≠ 0 ∧ b y ≠ 0 := by
  by_cases h : j - y₁ ≤ x₂
  · exact ⟨j - y₁, y₁, by lia, hA x₁ _ x₂ ha₁ ha₂ (by lia) h, hb₁⟩
  · exact ⟨x₂, j - x₂, by lia, ha₂, hB y₁ _ y₂ hb₁ hb₂ (by lia) (by lia)⟩

/-- The convolution of two nonnegative sequences without internal zeros has no
internal zeros. -/
private theorem conv_noInternalZeros {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hA : ∀ i j k, i < j → j < k → a i ≠ 0 → a k ≠ 0 → a j ≠ 0)
    (hB : ∀ i j k, i < j → j < k → b i ≠ 0 → b k ≠ 0 → b j ≠ 0)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) (hi : conv a b i ≠ 0) (hk : conv a b k ≠ 0) :
    conv a b j ≠ 0 := by
  rw [conv_ne_zero_iff ha hb] at hi hk ⊢
  obtain ⟨x₁, y₁, rfl, ha₁, hb₁⟩ := hi
  obtain ⟨x₂, y₂, rfl, ha₂, hb₂⟩ := hk
  exact exists_pair_of_le (ne_zero_of_between hA) (ne_zero_of_between hB) ha₁ ha₂ hb₁ hb₂
    hij.le hjk.le

private theorem logConcave_of_upTo {p : ℝ[X]} (hlc : CoeffLogConcaveUpTo p.natDegree p.coeff)
    (k : ℕ) :
    p.coeff k * p.coeff (k + 2) ≤ p.coeff (k + 1) ^ 2 := by
  by_cases hk : k + 1 < p.natDegree
  · have h := hlc (k + 1) (by lia) hk
    rw [Nat.add_sub_cancel] at h
    exact h
  · rw [coeff_eq_zero_of_natDegree_lt (by lia : p.natDegree < k + 2), mul_zero]
    positivity

private theorem noInternalZeros_of_upTo {p : ℝ[X]}
    (h : CoeffNoInternalZerosUpTo p.natDegree p.coeff) (i j k : ℕ) (hij : i < j) (hjk : j < k)
    (hi : p.coeff i ≠ 0) (hk : p.coeff k ≠ 0) : p.coeff j ≠ 0 :=
  h i j k hij hjk (le_natDegree_of_ne_zero hk) hi hk

end Hoggar

open Hoggar

/-- The coefficients of a product of two polynomials with nonnegative coefficients
are nonnegative. -/
theorem coeffNonnegUpTo_mul {p q : ℝ[X]} (hp : ∀ k, 0 ≤ p.coeff k)
    (hq : ∀ k, 0 ≤ q.coeff k) (d : ℕ) : CoeffNonnegUpTo d (p * q).coeff := fun k _ => by
  rw [coeff_mul_eq_conv]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hq _)

/-- **Hoggar's theorem**, log-concavity part: the product of two polynomials with
nonnegative, log-concave coefficients without internal zeros has log-concave
coefficients. -/
theorem coeffLogConcaveUpTo_mul {p q : ℝ[X]} (hp : ∀ k, 0 ≤ p.coeff k)
    (hplc : CoeffLogConcaveUpTo p.natDegree p.coeff)
    (hpniz : CoeffNoInternalZerosUpTo p.natDegree p.coeff) (hq : ∀ k, 0 ≤ q.coeff k)
    (hqlc : CoeffLogConcaveUpTo q.natDegree q.coeff)
    (hqniz : CoeffNoInternalZerosUpTo q.natDegree q.coeff) :
    CoeffLogConcaveUpTo (p * q).natDegree (p * q).coeff := by
  intro k hk _
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by lia⟩
  rw [Nat.add_sub_cancel, coeff_mul_eq_conv, coeff_mul_eq_conv, coeff_mul_eq_conv]
  exact conv_logConcave hp hq
    (mul_le_mul_of_logConcave hp (logConcave_of_upTo hplc) (noInternalZeros_of_upTo hpniz))
    (mul_le_mul_of_logConcave hq (logConcave_of_upTo hqlc) (noInternalZeros_of_upTo hqniz)) n

/-- **Hoggar's theorem**, internal-zero part: the product of two polynomials with
nonnegative coefficients without internal zeros has no internal zeros. -/
theorem coeffNoInternalZerosUpTo_mul {p q : ℝ[X]} (hp : ∀ k, 0 ≤ p.coeff k)
    (hpniz : CoeffNoInternalZerosUpTo p.natDegree p.coeff) (hq : ∀ k, 0 ≤ q.coeff k)
    (hqniz : CoeffNoInternalZerosUpTo q.natDegree q.coeff) :
    CoeffNoInternalZerosUpTo (p * q).natDegree (p * q).coeff := by
  intro i j k hij hjk _ hi hk
  rw [coeff_mul_eq_conv] at hi hk ⊢
  exact conv_noInternalZeros hp hq (noInternalZeros_of_upTo hpniz)
    (noInternalZeros_of_upTo hqniz) hij hjk hi hk

end RealRooted
