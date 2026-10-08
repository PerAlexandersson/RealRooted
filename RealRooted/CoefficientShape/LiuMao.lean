import RealRooted.CoefficientShape.LiuMao.PathKernel
import RealRooted.PolynomialValueEulerNumerator.PF

/-!
# The coefficient formula for Euler numerators of products

For real polynomials `p` and `q`, the coefficients of the canonical Euler numerator
`polynomialValueEulerNumerator (p * q)` are bilinear in those of `p` and `q`
(Liu–Mao, Lemma 2.1): with `d₁ = deg p` and `d₂ = deg q`,

`W(p q)_k = ∑_{i ≤ d₁} ∑_{j ≤ d₂} W(p)_i * W(q)_j * kern d₁ d₂ i j k`,

where `W = polynomialValueEulerNumerator`.

The proof rests on the characterization of `W(p)` by `p(t) = ∑ᵢ W(p)ᵢ C(t + d - i, d)`
(`eval_nat_eq_sum_eulerNumerator_coeff_mul_choose`), its uniqueness
(`coeff_polynomialValueEulerNumerator_eq_of_eval_eq`) and the binomial product identity of
Brändén–Ferroni–Jochemko (`choose_mul_choose_eq_sum_kern`).
-/

open Finset Polynomial

namespace RealRooted.LiuMao

/-- The Liu–Mao kernel (Lemma 2.1): the coefficient of `a_i b_j` in `W(p q)_k` when
`deg p = d₁` and `deg q = d₂`. -/
def kern (d₁ d₂ i j k : ℕ) : ℕ :=
  if i ≤ k ∧ j ≤ k then (d₁ - i + j).choose (k - i) * (d₂ - j + i).choose (k - j) else 0

/-! ### Uniqueness of the binomial expansion -/

/-- The coefficients of the canonical Euler numerator vanish beyond `natDegree p`. -/
theorem coeff_polynomialValueEulerNumerator_eq_zero_of_natDegree_lt (p : ℝ[X]) {k : ℕ}
    (hk : p.natDegree < k) : (polynomialValueEulerNumerator p).coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt ((natDegree_polynomialValueEulerNumerator_le p).trans_lt hk)

/-- Uniqueness of the expansion of `p (t)` in the basis `C (t + d - i, d)`: the coefficients of
the canonical Euler numerator are the only ones that work. -/
theorem coeff_polynomialValueEulerNumerator_eq_of_eval_eq {p : ℝ[X]} {c : ℕ → ℝ}
    (h : ∀ t : ℕ, p.eval (t : ℝ) =
      ∑ i ∈ range (p.natDegree + 1), c i * ((t + p.natDegree - i).choose p.natDegree : ℝ))
    {k : ℕ} (hk : k ≤ p.natDegree) :
    (polynomialValueEulerNumerator p).coeff k = c k := by
  have hδ : ∀ t : ℕ, ∑ i ∈ range (p.natDegree + 1),
      (c i - (polynomialValueEulerNumerator p).coeff i) *
        ((t + p.natDegree - i).choose p.natDegree : ℝ) = 0 := by
    intro t
    simp_rw [sub_mul]
    rw [sum_sub_distrib, ← h t, ← eval_nat_eq_sum_eulerNumerator_coeff_mul_choose p t, sub_self]
  have key : ∀ t, t ≤ p.natDegree → c t = (polynomialValueEulerNumerator p).coeff t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      have hsum := hδ t
      rw [sum_eq_single_of_mem t (mem_range.2 (by lia))] at hsum
      · simpa [sub_eq_zero] using hsum
      · intro i hi hit
        have hid := mem_range.1 hi
        rcases lt_or_gt_of_ne hit with h' | h'
        · rw [ih i h' (by lia), sub_self, zero_mul]
        · rw [Nat.choose_eq_zero_of_lt (n := t + p.natDegree - i) (by lia), Nat.cast_zero,
            mul_zero]
  exact (key k hk).symm

/-! ### The binomial product identity -/

private theorem vandermonde_range (a b n : ℕ) :
    ∑ s ∈ range (n + 1), a.choose s * b.choose (n - s) = (a + b).choose n := by
  rw [Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => a.choose x * b.choose y)]

private theorem sum_choose_mul_choose_mul_choose (A B d2 j : ℕ) (hj : j ≤ d2) :
    ∑ s ∈ range (d2 + 1), B.choose s * s.choose j * A.choose (d2 - s) =
      B.choose j * (A + B - j).choose (d2 - j) := by
  have hsplit : d2 + 1 = j + (d2 - j + 1) := by lia
  rw [hsplit, sum_range_add, sum_eq_zero (fun s hs => by
    rw [mem_range] at hs; rw [Nat.choose_eq_zero_of_lt hs]; simp), zero_add]
  have : ∀ x ∈ range (d2 - j + 1), B.choose (j + x) * (j + x).choose j *
      A.choose (d2 - (j + x)) =
      B.choose j * ((B - j).choose x * A.choose (d2 - j - x)) := by
    intro x hx
    rw [Nat.choose_mul (by lia)]
    rw [show j + x - j = x by lia, show d2 - (j + x) = d2 - j - x by lia]
    ring
  rw [sum_congr rfl this, ← mul_sum, vandermonde_range]
  rcases le_or_gt j B with h | h
  · congr 2; lia
  · rw [Nat.choose_eq_zero_of_lt h]; simp

/-- Core form of the product identity: with `x = u + d₁` and `y = u + B`. -/
private theorem choose_mul_choose_core (u d1 d2 A B : ℕ) (hAB : A + B = d1 + d2) :
    (u + d1).choose d1 * (u + B).choose d2 =
      ∑ s ∈ range (d2 + 1), B.choose s * A.choose (d2 - s) * (u + d1 + s).choose (d1 + d2) := by
  have hL : (u + d1).choose d1 * (u + B).choose d2 =
      ∑ j ∈ range (d2 + 1),
        B.choose j * (u + d1).choose (d1 + d2 - j) * (d1 + d2 - j).choose d1 := by
    rw [← vandermonde_range u B d2, mul_sum, ← sum_range_reflect]
    apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    rw [show d2 + 1 - 1 - j = d2 - j by lia, show d2 - (d2 - j) = j by lia]
    have := Nat.choose_mul (n := u + d1) (k := d1 + (d2 - j)) (s := d1) (by lia)
    rw [show u + d1 - d1 = u by lia, show d1 + (d2 - j) - d1 = d2 - j by lia] at this
    rw [show d1 + d2 - j = d1 + (d2 - j) by lia]
    calc (u + d1).choose d1 * (u.choose (d2 - j) * B.choose j)
        = B.choose j * ((u + d1).choose d1 * u.choose (d2 - j)) := by ring
      _ = _ := by rw [← this]; ring
  have hR : ∑ s ∈ range (d2 + 1),
        B.choose s * A.choose (d2 - s) * (u + d1 + s).choose (d1 + d2) =
      ∑ j ∈ range (d2 + 1),
        B.choose j * (u + d1).choose (d1 + d2 - j) * (d1 + d2 - j).choose d1 := by
    have h1 : ∀ s ∈ range (d2 + 1),
        B.choose s * A.choose (d2 - s) * (u + d1 + s).choose (d1 + d2) =
        ∑ j ∈ range (d2 + 1), (u + d1).choose (d1 + d2 - j) *
          (B.choose s * s.choose j * A.choose (d2 - s)) := by
      intro s hs
      rw [mem_range] at hs
      have hv : (u + d1 + s).choose (d1 + d2) =
          ∑ j ∈ range (d2 + 1), s.choose j * (u + d1).choose (d1 + d2 - j) := by
        rw [add_comm (u + d1) s, ← vandermonde_range s (u + d1) (d1 + d2)]
        symm
        apply sum_subset
        · intro x; simp only [mem_range]; lia
        · intro x hx hx2
          simp only [mem_range] at hx hx2
          rw [Nat.choose_eq_zero_of_lt (n := s) (k := x) (by lia)]; simp
      rw [hv, mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    rw [sum_congr rfl h1, sum_comm]
    apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    rw [← mul_sum, sum_choose_mul_choose_mul_choose A B d2 j (by lia), hAB]
    rw [Nat.choose_symm_of_eq_add (show d1 + d2 - j = d1 + (d2 - j) by lia)]
    ring
  rw [hL, hR]

/-- The binomial product identity behind the kernel (Brändén–Ferroni–Jochemko, Lemma 2.3). -/
theorem choose_mul_choose_eq_sum_kern {d₁ d₂ i j : ℕ} (hi : i ≤ d₁) (hj : j ≤ d₂) (t : ℕ) :
    (t + d₁ - i).choose d₁ * (t + d₂ - j).choose d₂ =
      ∑ k ∈ range (d₁ + d₂ + 1), kern d₁ d₂ i j k * (t + (d₁ + d₂) - k).choose (d₁ + d₂) := by
  by_cases ht : i ≤ t ∧ j ≤ t
  · obtain ⟨hit, hjt⟩ := ht
    have h1 := choose_mul_choose_core (t - i) d₁ d₂ (d₁ - i + j) (d₂ - j + i) (by lia)
    rw [show t - i + d₁ = t + d₁ - i by lia,
      show t - i + (d₂ - j + i) = t + d₂ - j by lia] at h1
    rw [h1]
    have hsplit : d₁ + d₂ + 1 = i + (d₂ + 1) + (d₁ - i) := by lia
    rw [hsplit, sum_range_add _ (i + (d₂ + 1)) (d₁ - i), sum_range_add _ i (d₂ + 1)]
    rw [sum_eq_zero (s := range i) (fun k hk => by
      rw [mem_range] at hk; unfold kern; rw [ite_eq_right (by lia)]; simp), zero_add]
    rw [sum_eq_zero (s := range (d₁ - i)) (fun k hk => by
      unfold kern
      split_ifs with h
      · rw [Nat.choose_eq_zero_of_lt (n := d₂ - j + i) (by lia)]; simp
      · simp), add_zero]
    rw [← sum_range_reflect]
    apply sum_congr rfl
    intro s hs
    rw [mem_range] at hs
    unfold kern
    rw [show d₂ + 1 - 1 - s = d₂ - s by lia, show d₂ - (d₂ - s) = s by lia,
      show t + d₁ - i + (d₂ - s) = t + (d₁ + d₂) - (i + s) by lia, show i + s - i = s by lia]
    split_ifs with h
    · rw [Nat.choose_symm_of_eq_add (show d₂ - j + i = (d₂ - s) + (i + s - j) by lia)]
      ring
    · rw [Nat.choose_eq_zero_of_lt (n := d₂ - j + i) (by lia)]; simp
  · rw [not_and_or] at ht
    rw [sum_eq_zero]
    · rcases ht with ht | ht
      · rw [Nat.choose_eq_zero_of_lt (n := t + d₁ - i) (by lia)]; simp
      · rw [Nat.choose_eq_zero_of_lt (n := t + d₂ - j) (by lia)]; simp
    · intro k hk
      unfold kern
      split_ifs with h
      · rw [Nat.choose_eq_zero_of_lt (n := t + (d₁ + d₂) - k) (by lia)]; simp
      · simp

/-! ### The coefficient formula -/

/-- Two finite sums of a function agree when its support lies below both bounds. -/
theorem sum_range_eq_sum_range_of_support {g : ℕ → ℝ} {a b : ℕ}
    (h : ∀ i, g i ≠ 0 → i ≤ a ∧ i ≤ b) :
    ∑ i ∈ range (a + 1), g i = ∑ i ∈ range (b + 1), g i := by
  have key : ∀ c, c ≤ a + b → (∀ i, g i ≠ 0 → i ≤ c) →
      ∑ i ∈ range (c + 1), g i = ∑ i ∈ range (a + b + 1), g i := by
    intro c hcab hc
    refine sum_subset ?_ ?_
    · intro i
      simp only [mem_range]
      intro hi
      lia
    · intro i hi hi2
      simp only [mem_range] at hi hi2
      by_contra hne
      have := hc i hne
      lia
  rw [key a (by lia) (fun i hi => (h i hi).1), key b (by lia) (fun i hi => (h i hi).2)]

/-- The coefficient formula for the Euler numerator of a product (Liu–Mao, Lemma 2.1). -/
theorem coeff_polynomialValueEulerNumerator_mul {p q : ℝ[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (k : ℕ) :
    (polynomialValueEulerNumerator (p * q)).coeff k =
      ∑ i ∈ range (p.natDegree + 1), ∑ j ∈ range (q.natDegree + 1),
        (polynomialValueEulerNumerator p).coeff i * (polynomialValueEulerNumerator q).coeff j *
          (kern p.natDegree q.natDegree i j k : ℝ) := by
  have hN : (p * q).natDegree = p.natDegree + q.natDegree := natDegree_mul hp hq
  rcases le_or_gt k (p * q).natDegree with hk | hk
  · apply coeff_polynomialValueEulerNumerator_eq_of_eval_eq _ hk
    intro t
    rw [eval_mul, eval_nat_eq_sum_eulerNumerator_coeff_mul_choose p t,
      eval_nat_eq_sum_eulerNumerator_coeff_mul_choose q t, hN, sum_mul_sum]
    have h2 : ∀ i ∈ range (p.natDegree + 1), ∀ j ∈ range (q.natDegree + 1),
        (polynomialValueEulerNumerator p).coeff i *
            ((t + p.natDegree - i).choose p.natDegree : ℝ) *
          ((polynomialValueEulerNumerator q).coeff j *
            ((t + q.natDegree - j).choose q.natDegree : ℝ)) =
        ∑ k ∈ range (p.natDegree + q.natDegree + 1),
          (polynomialValueEulerNumerator p).coeff i * (polynomialValueEulerNumerator q).coeff j *
            (kern p.natDegree q.natDegree i j k : ℝ) *
            ((t + (p.natDegree + q.natDegree) - k).choose (p.natDegree + q.natDegree) : ℝ) := by
      intro i hi j hj
      rw [mem_range] at hi hj
      have := choose_mul_choose_eq_sum_kern (d₁ := p.natDegree) (d₂ := q.natDegree)
        (by lia : i ≤ p.natDegree) (by lia : j ≤ q.natDegree) t
      have hc := congr_arg (fun n : ℕ => (n : ℝ)) this
      simp only [Nat.cast_mul, Nat.cast_sum] at hc
      calc (polynomialValueEulerNumerator p).coeff i *
            ((t + p.natDegree - i).choose p.natDegree : ℝ) *
            ((polynomialValueEulerNumerator q).coeff j *
              ((t + q.natDegree - j).choose q.natDegree : ℝ))
          = (polynomialValueEulerNumerator p).coeff i *
            (polynomialValueEulerNumerator q).coeff j *
            (((t + p.natDegree - i).choose p.natDegree : ℝ) *
              ((t + q.natDegree - j).choose q.natDegree : ℝ)) := by ring
        _ = _ := by
          rw [hc, mul_sum]
          exact sum_congr rfl fun x _ => by ring
    rw [sum_congr rfl (fun i hi => sum_congr rfl (h2 i hi))]
    rw [sum_comm]
    simp_rw [sum_comm (s := range (q.natDegree + 1))]
    simp_rw [sum_mul]
    exact sum_comm
  · rw [coeff_polynomialValueEulerNumerator_eq_zero_of_natDegree_lt _ hk]
    symm
    refine sum_eq_zero fun i hi => sum_eq_zero fun j hj => ?_
    rw [mem_range] at hi hj
    have : kern p.natDegree q.natDegree i j k = 0 := by
      unfold kern
      split_ifs with h
      · rw [Nat.choose_eq_zero_of_lt (n := q.natDegree - j + i) (by lia)]
        simp
      · rfl
    rw [this]
    simp

end RealRooted.LiuMao

/-!
## The Liu–Mao theorem: products and LC-NIZ Euler numerators

Reference: Yanxin Liu and Jianxi Mao, *Preservation of log-concavity under Hadamard products*,
arXiv:2609.11589 (2026), Theorem 1.1.

For a real polynomial `p`, `polynomialValueEulerNumerator p` is the numerator of the generating
series `∑ₙ p(n) xⁿ` over `(1 - x)^(deg p + 1)`.  A finite sequence is LC-NIZ if it is nonnegative,
log-concave and has no internal zeros (`CoeffNonnegUpTo`, `CoeffLogConcaveUpTo` and
`CoeffNoInternalZerosUpTo`, bundled as `RealRooted.LiuMao.LCNIZ`).

**Theorem (Liu–Mao).**  If the Euler numerators of `p` and `q` are LC-NIZ up to their degrees,
then so is the Euler numerator of `p * q`
(`coeffLCNIZ_polynomialValueEulerNumerator_mul`).

The no-internal-zeros hypothesis is essential: the Euler numerators `1 + x^3` (degree `3`) and
`x` (degree `1`) multiply to the Euler numerator `4x + 3x^3 + x^4` of a degree `4` product, which
is not log-concave.

The proof writes the coefficients of the product numerator as the diagonal of a matrix
`C = T_a H T_bᵀ` (`RealRooted.LiuMao.Cmat`), where `T_a`, `T_b` are the Toeplitz matrices of the
two numerators and `H` is the Liu–Mao kernel, and applies the diagonal lemma below to `C`.
-/

open Finset Polynomial

namespace RealRooted.LiuMao

/-- Diagonal lemma (Liu–Mao, Lemma 4.1): the diagonal of a nonnegative reverse-regular (`RR₂`)
matrix with log-concave rows and columns and interval positive diagonal support is LC-NIZ. -/
private theorem diag_lcniz {N : ℕ} {C : ℕ → ℕ → ℝ}
    (h0 : ∀ r s, r ≤ N → s ≤ N → 0 ≤ C r s)
    (hRR : ∀ r₁ r₂ s₁ s₂, r₁ < r₂ → s₁ < s₂ → r₂ ≤ N → s₂ ≤ N →
      C r₁ s₁ * C r₂ s₂ ≤ C r₁ s₂ * C r₂ s₁)
    (hrow : ∀ r, r ≤ N → ∀ s, 0 < s → s < N → C r (s - 1) * C r (s + 1) ≤ C r s ^ 2)
    (hcol : ∀ s, s ≤ N → ∀ r, 0 < r → r < N → C (r - 1) s * C (r + 1) s ≤ C r s ^ 2)
    (hniz : ∀ i j k, i < j → j < k → k ≤ N → C i i ≠ 0 → C k k ≠ 0 → C j j ≠ 0) :
    LCNIZ N (fun k => C k k) := by
  refine ⟨fun k hk => h0 k k hk hk, ?_, hniz⟩
  intro k hk0 hkN
  simp only
  have e1 := hRR (k - 1) k (k - 1) k (by lia) (by lia) (by lia) (by lia)
  have e2 := hRR k (k + 1) k (k + 1) (by lia) (by lia) (by lia) (by lia)
  have e3 := hcol k (by lia) k hk0 hkN
  have e4 := hrow k (by lia) k hk0 hkN
  have p1 := h0 (k - 1) (k - 1) (by lia) (by lia)
  have p2 := h0 k k (by lia) (by lia)
  have p3 := h0 (k + 1) (k + 1) (by lia) (by lia)
  have q1 := h0 (k - 1) k (by lia) (by lia)
  have q2 := h0 k (k - 1) (by lia) (by lia)
  have q3 := h0 k (k + 1) (by lia) (by lia)
  have q4 := h0 (k + 1) k (by lia) (by lia)
  rcases eq_or_lt_of_le p2 with hc | hc
  · -- the diagonal entry vanishes: use no internal zeros
    by_contra hcon
    push Not at hcon
    rw [← hc] at hcon
    have ha : C (k - 1) (k - 1) ≠ 0 := by
      intro h; rw [h, zero_mul] at hcon; simp at hcon
    have he : C (k + 1) (k + 1) ≠ 0 := by
      intro h; rw [h, mul_zero] at hcon; simp at hcon
    exact hniz (k - 1) k (k + 1) (by lia) (by lia) (by lia) ha he hc.symm
  · have key : C (k - 1) (k - 1) * C (k + 1) (k + 1) * (C k k * C k k) ≤
        (C k k ^ 2) * (C k k * C k k) := by
      calc C (k - 1) (k - 1) * C (k + 1) (k + 1) * (C k k * C k k)
          = (C (k - 1) (k - 1) * C k k) * (C k k * C (k + 1) (k + 1)) := by ring
        _ ≤ (C (k - 1) k * C k (k - 1)) * (C k (k + 1) * C (k + 1) k) :=
          mul_le_mul e1 e2 (mul_nonneg p2 p3) (mul_nonneg q1 q2)
        _ = (C (k - 1) k * C (k + 1) k) * (C k (k - 1) * C k (k + 1)) := by ring
        _ ≤ (C k k ^ 2) * (C k k ^ 2) :=
          mul_le_mul e3 e4 (mul_nonneg q2 q3) (sq_nonneg _)
        _ = (C k k ^ 2) * (C k k * C k k) := by ring
    exact le_of_mul_le_mul_right key (mul_pos hc hc)

private theorem lcniz_coeff_zero (d : ℕ) : LCNIZ d (0 : ℝ[X]).coeff := by
  have : ⇑(0 : ℝ[X]).coeff = fun _ => 0 := _root_.funext coeff_zero
  rw [this]
  exact ⟨fun _ _ => le_rfl, fun _ _ _ => by simp, fun _ _ _ _ _ _ h _ => absurd rfl h⟩

/-- Kernel form of `W(p q)`: the diagonal of the matrix `C = T_a H T_bᵀ`. -/
private theorem coeff_polynomialValueEulerNumerator_mul_eq_Cmat {p q : ℝ[X]} (hp : p ≠ 0)
    (hq : q ≠ 0) (k : ℕ) :
    (polynomialValueEulerNumerator (p * q)).coeff k =
      Cmat (polynomialValueEulerNumerator p).coeff (polynomialValueEulerNumerator q).coeff
        p.natDegree q.natDegree k k := by
  rw [coeff_polynomialValueEulerNumerator_mul hp hq k]
  set a := (polynomialValueEulerNumerator p).coeff with ha
  set b := (polynomialValueEulerNumerator q).coeff with hb
  have ha0 : ∀ i, p.natDegree < i → a i = 0 := fun i hi =>
    coeff_polynomialValueEulerNumerator_eq_zero_of_natDegree_lt p hi
  have hb0 : ∀ j, q.natDegree < j → b j = 0 := fun j hj =>
    coeff_polynomialValueEulerNumerator_eq_zero_of_natDegree_lt q hj
  generalize p.natDegree = d1 at ha0 ⊢
  generalize q.natDegree = d2 at hb0 ⊢
  have hkern0 : ∀ i j, (k < i ∨ k < j) → kern d1 d2 i j k = 0 := by
    intro i j h; unfold kern; rw [ite_eq_right (by lia)]
  -- restrict the left-hand side to `[0, k]²`
  have hL : ∑ i ∈ range (d1 + 1), ∑ j ∈ range (d2 + 1), a i * b j * (kern d1 d2 i j k : ℝ) =
      ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1), a i * b j * (kern d1 d2 i j k : ℝ) := by
    have hin : ∀ i, ∑ j ∈ range (d2 + 1), a i * b j * (kern d1 d2 i j k : ℝ) =
        ∑ j ∈ range (k + 1), a i * b j * (kern d1 d2 i j k : ℝ) := by
      intro i
      apply sum_range_eq_sum_range_of_support
      intro j hj
      constructor
      · by_contra h; exact hj (by rw [hb0 j (by lia)]; simp)
      · by_contra h; exact hj (by rw [hkern0 i j (by lia)]; simp)
    simp only [hin]
    apply sum_range_eq_sum_range_of_support
    intro i hi
    constructor
    · by_contra h; exact hi (sum_eq_zero fun j _ => by rw [ha0 i (by lia)]; simp)
    · by_contra h; exact hi (sum_eq_zero fun j _ => by rw [hkern0 i j (by lia)]; simp)
  -- restrict the right-hand side to `[0, k]²`
  have hR : Cmat a b d1 d2 k k =
      ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1), toep a k i * Hk d1 d2 i j * toep b k j := by
    unfold Cmat
    have hin : ∀ i, ∑ j ∈ range (d1 + 1), toep a k i * Hk d1 d2 i j * toep b k j =
        ∑ j ∈ range (k + 1), toep a k i * Hk d1 d2 i j * toep b k j := by
      intro i
      apply sum_range_eq_sum_range_of_support
      intro j hj
      constructor
      · by_contra h; exact hj (by unfold Hk; rw [ite_eq_right (by lia)]; simp)
      · by_contra h; exact hj (by unfold toep; rw [ite_eq_right (show ¬ j ≤ k by lia)]; simp)
    simp only [hin]
    apply sum_range_eq_sum_range_of_support
    intro i hi
    constructor
    · by_contra h; exact hi (sum_eq_zero fun j _ => by unfold Hk; rw [ite_eq_right (by lia)]; simp)
    · by_contra h
      exact hi (sum_eq_zero fun j _ => by
        unfold toep
        rw [ite_eq_right (show ¬ i ≤ k by lia)]
        simp)
  rw [hL, hR, ← sum_range_reflect]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [show k + 1 - 1 - i = k - i by lia, show k + 1 - 1 - j = k - j by lia]
  unfold toep
  rw [ite_eq_left (by lia), ite_eq_left (by lia)]
  by_cases hid : k - i ≤ d1
  swap
  · rw [ha0 (k - i) (by lia)]; simp
  by_cases hjd : k - j ≤ d2
  swap
  · rw [hb0 (k - j) (by lia)]; simp
  unfold kern Hk
  rw [ite_eq_left ⟨by lia, by lia⟩, show k - (k - i) = i by lia, show k - (k - j) = j by lia]
  by_cases hbox : i ≤ d2 ∧ j ≤ d1
  · rw [ite_eq_left hbox, show d1 - (k - i) + (k - j) = d1 + i - j by lia,
      show d2 - (k - j) + (k - i) = d2 + j - i by lia]
    push_cast; ring
  · rw [ite_eq_right hbox]
    rcases not_and_or.mp hbox with h | h
    · rw [Nat.choose_eq_zero_of_lt (n := d2 - (k - j) + (k - i)) (by lia)]; simp
    · rw [Nat.choose_eq_zero_of_lt (n := d1 - (k - i) + (k - j)) (by lia)]; simp

/-- **Liu–Mao theorem.**  If the canonical Euler numerators of `p` and `q` have nonnegative,
log-concave coefficients without internal zeros (up to the degrees of `p` and `q`), then so does
the Euler numerator of `p * q` (up to the degree of `p * q`). -/
theorem coeffLCNIZ_polynomialValueEulerNumerator_mul (p q : ℝ[X])
    (hp : CoeffNonnegUpTo p.natDegree (polynomialValueEulerNumerator p).coeff ∧
      CoeffLogConcaveUpTo p.natDegree (polynomialValueEulerNumerator p).coeff ∧
      CoeffNoInternalZerosUpTo p.natDegree (polynomialValueEulerNumerator p).coeff)
    (hq : CoeffNonnegUpTo q.natDegree (polynomialValueEulerNumerator q).coeff ∧
      CoeffLogConcaveUpTo q.natDegree (polynomialValueEulerNumerator q).coeff ∧
      CoeffNoInternalZerosUpTo q.natDegree (polynomialValueEulerNumerator q).coeff) :
    CoeffNonnegUpTo (p * q).natDegree (polynomialValueEulerNumerator (p * q)).coeff ∧
      CoeffLogConcaveUpTo (p * q).natDegree (polynomialValueEulerNumerator (p * q)).coeff ∧
      CoeffNoInternalZerosUpTo (p * q).natDegree
        (polynomialValueEulerNumerator (p * q)).coeff := by
  by_cases hp0 : p = 0
  · subst hp0
    rw [zero_mul, polynomialValueEulerNumerator_zero]
    exact lcniz_coeff_zero _
  by_cases hq0 : q = 0
  · subst hq0
    rw [mul_zero, polynomialValueEulerNumerator_zero]
    exact lcniz_coeff_zero _
  have ha : GLC (polynomialValueEulerNumerator p).coeff :=
    LCNIZ.glc hp fun k hk => coeff_polynomialValueEulerNumerator_eq_zero_of_natDegree_lt p hk
  have hb : GLC (polynomialValueEulerNumerator q).coeff :=
    LCNIZ.glc hq fun k hk => coeff_polynomialValueEulerNumerator_eq_zero_of_natDegree_lt q hk
  have e : (polynomialValueEulerNumerator (p * q)).coeff =
      fun k => Cmat (polynomialValueEulerNumerator p).coeff
        (polynomialValueEulerNumerator q).coeff p.natDegree q.natDegree k k :=
    funext (coeff_polynomialValueEulerNumerator_mul_eq_Cmat hp0 hq0)
  rw [e]
  exact diag_lcniz
    (fun r s _ _ => Cmat_nonneg ha hb _ _ r s)
    (fun r₁ r₂ s₁ s₂ hr hs _ _ => Cmat_rr2 ha hb _ _ hr hs)
    (fun r _ s hs _ => (Cmat_row_glc ha hb _ _ r).lc s hs)
    (fun s _ r hr _ => (Cmat_col_glc ha hb _ _ s).lc r hr)
    (fun i j k hij hjk _ hi hk => Cmat_diag_niz ha hb _ _ hij hjk hi hk)

end RealRooted.LiuMao
