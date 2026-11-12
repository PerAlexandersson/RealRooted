module

public import RealRooted.Basic.AffineInterlacing
public import RealRooted.Basic.Coefficients
import RealRooted.DegreeDropReversal
public import RealRooted.Mathlib.Algebra.Polynomial.Reverse
public import RealRooted.Basic.ProperPosition
import RealRooted.Mathlib.Data.List.Interleave

/-!
# Interlacing of reversed rows

For rows `P n` of degree `D₀ + n` with nonzero constant terms, the reversed rows
`R n = X ^ (D₀ + n) P n (1 / X)` invert the roots.  On negative roots inversion reverses the
order, so consecutive reversed rows interlace exactly when the rows do
(`interlaces_reverse_of_roots_neg`).

The reversed rows of a recurrence satisfy a recurrence of the same shape:

* `reflect_linearRecurrence` transports any finite-order recurrence, with coefficients
  depending on `n`, under the degree bound `D + c * n`. The multiplier at lag `j` is reflected
  at `c * j`. `eq_reflect_of_linearRecurrence` identifies a separately defined reflected family
  from its initial rows;
* `eq_reflect_of_threeTerm`: `P (n + 2) = a n P (n + 1) + b n P n` reverses to the multipliers
  `reflect 1 (a n)` and `reflect 2 (b n)`;
* `eq_reflect_of_secondOrderDerivativeRecurrence`:
  `P (n + 1) = A₂ P'' + A₁ P' + A₀ P` reverses through
  `Polynomial.derivative_reflect`, with `θ_N r = X (N r - X r')`, `θ_N r = X u₁` and
  `θ_N (θ_N r) = X ^ 2 u₂`.

The identification theorems let `R` be given by its own recurrence, so that it can be an
ordinary recursive definition. The three-term result is the order-two, slope-one specialization.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

private lemma pairwise_reverse_map_inv {l : List ℝ} (h : l.Pairwise (· ≤ ·))
    (hneg : ∀ t ∈ l, t < 0) : (l.map Inv.inv).reverse.Pairwise (· ≤ ·) := by
  rw [List.pairwise_reverse, List.pairwise_map]
  exact h.imp_of_mem fun ha hb hab => (inv_le_inv_of_neg (hneg _ hb) (hneg _ ha)).2 hab

private lemma interlaces_reverse_map_inv {ss rs : List ℝ}
    (h : ListInterlaces ss rs) (hlen : ss.length + 1 = rs.length)
    (hneg : ∀ t, t ∈ ss ∨ t ∈ rs → t < 0) :
    ListInterlaces (ss.map Inv.inv).reverse (rs.map Inv.inv).reverse := by
  have hi := interleaves_of_listInterlaces_of_length hlen h
  have him : List.Interleaves (Function.swap (fun x y : ℝ => x ≤ y))
      (ss.map Inv.inv) (rs.map Inv.inv) :=
    hi.map_of_mem Inv.inv fun a b ha hb hab =>
      (inv_le_inv_of_neg (hneg b hb) (hneg a ha)).2 hab
  have hlen' : (ss.map Inv.inv).length + 1 = (rs.map Inv.inv).length := by simpa using hlen
  have hir := (List.interleaves_reverse_reverse_of_length_eq_length_add_one
    (r := fun x y : ℝ => x ≤ y) hlen').2 him
  exact listInterlaces_of_interleaves_of_length (by simpa using hlen) hir

private lemma coeff_zero_ne_of_roots_neg {p : ℝ[X]} (hp : p ≠ 0)
    (hneg : ∀ t ∈ p.roots, t < 0) : p.coeff 0 ≠ 0 := by
  intro h0
  have : (0 : ℝ) ∈ p.roots := by
    rw [mem_roots hp, IsRoot.def, ← coeff_zero_eq_eval_zero]
    exact h0
  exact lt_irrefl 0 (hneg 0 this)

/-- Reversal preserves legacy interlacing when all roots are negative: it inverts the roots,
which reverses their order. -/
lemma interlaces_reverse_of_roots_neg {g f : ℝ[X]} (h : Interlaces g f)
    (hf : ∀ t ∈ f.roots, t < 0) (hg : ∀ t ∈ g.roots, t < 0) :
    Interlaces g.reverse f.reverse := by
  rcases h with
    ⟨⟨hfne, hfs⟩, ⟨hgne, hgs⟩, hdeg, ⟨rs, ss, hrs, hss, hfr, hgsr, hlist⟩⟩
  have hf0 := coeff_zero_ne_of_roots_neg hfne hf
  have hg0 := coeff_zero_ne_of_roots_neg hgne hg
  have hfr' := Polynomial.roots_reverse_eq_map_inv hfs hf0
  have hgr' := Polynomial.roots_reverse_eq_map_inv hgs hg0
  have hfrs := Polynomial.Splits.reverse hfs
  have hgrs := Polynomial.Splits.reverse hgs
  have hnat : ∀ {p : ℝ[X]}, p.Splits → p.coeff 0 ≠ 0 → p.reverse.natDegree = p.natDegree := by
    intro p hp hp0
    rw [← Polynomial.splits_iff_card_roots.mp (Polynomial.Splits.reverse hp),
      Polynomial.roots_reverse_eq_map_inv hp hp0,
      Multiset.card_map, Polynomial.splits_iff_card_roots.mp hp]
  have hrslen : rs.length = f.natDegree := by
    rw [← Polynomial.splits_iff_card_roots.mp hfs, ← hfr, Multiset.coe_card]
  have hsslen : ss.length = g.natDegree := by
    rw [← Polynomial.splits_iff_card_roots.mp hgs, ← hgsr, Multiset.coe_card]
  refine ⟨⟨DegreeDropReversal.reverse_ne_zero_of_coeff_zero_ne hf0, hfrs⟩,
    ⟨DegreeDropReversal.reverse_ne_zero_of_coeff_zero_ne hg0, hgrs⟩, ?_,
    ⟨(rs.map Inv.inv).reverse, (ss.map Inv.inv).reverse, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hnat hfs hf0, hnat hgs hg0, hdeg]
  · exact pairwise_reverse_map_inv hrs fun t ht => hf t (by rw [← hfr]; exact ht)
  · exact pairwise_reverse_map_inv hss fun t ht => hg t (by rw [← hgsr]; exact ht)
  · rw [hfr', ← hfr]; simp
  · rw [hgr', ← hgsr]; simp
  · refine interlaces_reverse_map_inv hlist (by lia) fun t ht => ?_
    rcases ht with ht | ht
    · exact hg t (by rw [← hgsr]; exact ht)
    · exact hf t (by rw [← hfr]; exact ht)

/-- Reversed rows of a second-order derivative recurrence.  If `P (n + 1) = A₂ P'' + A₁ P' + A₀ P`
with `A i` of degree at most `i + 1`, and `R` satisfies the reflected recurrence (with
`N = D₀ + n`), then `P n = reflect (D₀ + n) (R n)` for all `n`. -/
theorem eq_reflect_of_secondOrderDerivativeRecurrence
    {P R A₂ A₁ A₀ B₂ B₁ B₀ : ℕ → ℝ[X]} {D₀ : ℕ}
    (hP : ∀ n, P (n + 1) =
      A₂ n * derivative (derivative (P n)) + A₁ n * derivative (P n) + A₀ n * P n)
    (hR : ∀ n, R (n + 1) =
      B₂ n * derivative (derivative (R n)) + B₁ n * derivative (R n) + B₀ n * R n)
    (hA₂ : ∀ n, (A₂ n).natDegree ≤ 3) (hA₁ : ∀ n, (A₁ n).natDegree ≤ 2)
    (hA₀ : ∀ n, (A₀ n).natDegree ≤ 1)
    (hB₂ : ∀ n, B₂ n = X ^ 2 * reflect 3 (A₂ n))
    (hB₁ : ∀ n, B₁ n =
      -(X * (C (2 * ((D₀ + n : ℕ) : ℝ) - 2) * reflect 3 (A₂ n) + reflect 2 (A₁ n))))
    (hB₀ : ∀ n, B₀ n =
      C (((D₀ + n : ℕ) : ℝ) * (((D₀ + n : ℕ) : ℝ) - 1)) * reflect 3 (A₂ n) +
        C ((D₀ + n : ℕ) : ℝ) * reflect 2 (A₁ n) + reflect 1 (A₀ n))
    (hRdeg : ∀ n, (R n).natDegree ≤ D₀ + n) (h0 : P 0 = reflect D₀ (R 0)) :
    ∀ n, P n = reflect (D₀ + n) (R n) := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hr := hRdeg n
    set N := D₀ + n with hN
    set r := R n
    have hθ := natDegree_X_mul_C_mul_sub_X_mul_derivative_le hr
    have hθθ := natDegree_X_mul_C_mul_sub_X_mul_derivative_le hθ
    have e1 : X * (C (N : ℝ) * r - X * derivative r) =
        X ^ 1 * (C (N : ℝ) * r - X * derivative r) := by ring
    have e2 : X * (C (N : ℝ) * (X * (C (N : ℝ) * r - X * derivative r)) -
        X * derivative (X * (C (N : ℝ) * r - X * derivative r))) =
        X ^ 2 * (C ((N : ℝ) * ((N : ℝ) - 1)) * r - C (2 * (N : ℝ) - 2) * X * derivative r +
          X ^ 2 * derivative (derivative r)) := by
      simp only [derivative_mul, derivative_X, derivative_C, derivative_sub, C_mul, C_sub,
        C_ofNat, C_1]
      ring
    rw [hP, ih, derivative_reflect r hr, derivative_reflect _ hθ,
      mul_reflect_eq_reflect_mul (k := 3) (hA₂ n) hθθ,
      mul_reflect_eq_reflect_mul (k := 2) (hA₁ n) hθ,
      mul_reflect_eq_reflect_mul (k := 1) (hA₀ n) hr, e2, e1,
      show 3 + N = (N + 1) + 2 by lia, show 2 + N = (N + 1) + 1 by lia, add_comm 1 N,
      reflect_add_mul_X_pow_mul, reflect_add_mul_X_pow_mul, ← reflect_add, ← reflect_add,
      show D₀ + (n + 1) = N + 1 by lia, hR, hB₂, hB₁, hB₀]
    · congr 1
      simp only [C_mul, C_sub, C_ofNat, C_1]
      ring
    · rw [← e1, show N + 1 + 1 = 2 + N by lia]
      exact natDegree_mul_le.trans
        (add_le_add (natDegree_reflect_le.trans (max_le le_rfl (hA₁ n))) hθ)
    · rw [← e2, show N + 1 + 2 = 3 + N by lia]
      exact natDegree_mul_le.trans
        (add_le_add (natDegree_reflect_le.trans (max_le le_rfl (hA₂ n))) hθθ)

/-- Reflection transports a recurrence of any finite order and any natural degree slope.
The summand indexed by `i < k` has lag `k - i`, hence reflection bound `c * (k - i)`.
Coefficients may depend on the row index. No positivity or nonvanishing is needed. -/
theorem reflect_linearRecurrence {S : Type*} [Semiring S]
    {R : ℕ → S[X]} {a : ℕ → ℕ → S[X]} {k D c : ℕ}
    (hR : ∀ n, R (n + k) = ∑ i ∈ Finset.range k, a n i * R (n + i))
    (ha : ∀ n i, i < k → (a n i).natDegree ≤ c * (k - i))
    (hdeg : ∀ n, (R n).natDegree ≤ D + c * n) :
    ∀ n, reflect (D + c * (n + k)) (R (n + k)) =
      ∑ i ∈ Finset.range k,
        reflect (c * (k - i)) (a n i) * reflect (D + c * (n + i)) (R (n + i)) := by
  intro n
  rw [hR n]
  have hsum (s : Finset ℕ) :
      reflect (D + c * (n + k)) (∑ i ∈ s, a n i * R (n + i)) =
        ∑ i ∈ s, reflect (D + c * (n + k)) (a n i * R (n + i)) := by
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, reflect_add, ih]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := (Finset.mem_range.mp hi).le
  have hindex : D + c * (n + k) = c * (k - i) + (D + c * (n + i)) := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_sub_left_distrib]
    have := Nat.mul_le_mul_left c hik
    lia
  rw [hindex, reflect_mul _ _ (ha n i (Finset.mem_range.mp hi)) (hdeg (n + i))]

/-- Matching initial rows and reflected finite-order recurrences identify two families.
This includes every positive order and slope; order or slope zero is also allowed. -/
theorem eq_reflect_of_linearRecurrence {S : Type*} [Semiring S]
    {P R : ℕ → S[X]} {a : ℕ → ℕ → S[X]} {k D c : ℕ}
    (hP : ∀ n, P (n + k) = ∑ i ∈ Finset.range k, a n i * P (n + i))
    (hR : ∀ n, R (n + k) =
      ∑ i ∈ Finset.range k, reflect (c * (k - i)) (a n i) * R (n + i))
    (ha : ∀ n i, i < k → (a n i).natDegree ≤ c * (k - i))
    (hdeg : ∀ n, (R n).natDegree ≤ D + c * n)
    (hinit : ∀ i, i < k → P i = reflect (D + c * i) (R i)) :
    ∀ n, P n = reflect (D + c * n) (R n) := by
  have hr := reflect_linearRecurrence hR
    (fun n i hi => natDegree_reflect_le.trans (max_le le_rfl (ha n i hi))) hdeg
  simp only [reflect_reflect] at hr
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < k
    · exact hinit n hn
    · have hkn : k ≤ n := Nat.le_of_not_gt hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
      rw [Nat.add_comm k m, hP m, hr m]
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih (m + i) (by have := Finset.mem_range.mp hi; lia)]

/-- Reversed rows of a three-term recurrence: if `P (n + 2) = a n P (n + 1) + b n P n` with
`a n`, `b n` of degree at most one and two, and `R` satisfies the recurrence with multipliers
`reflect 1 (a n)` and `reflect 2 (b n)`, then `P n = reflect (D₀ + n) (R n)` for all `n`. -/
theorem eq_reflect_of_threeTerm {P R a b a' b' : ℕ → ℝ[X]} {D₀ : ℕ}
    (hP : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (hR : ∀ n, R (n + 2) = a' n * R (n + 1) + b' n * R n)
    (ha : ∀ n, (a n).natDegree ≤ 1) (hb : ∀ n, (b n).natDegree ≤ 2)
    (ha' : ∀ n, a' n = reflect 1 (a n)) (hb' : ∀ n, b' n = reflect 2 (b n))
    (hRdeg : ∀ n, (R n).natDegree ≤ D₀ + n) (h0 : P 0 = reflect D₀ (R 0))
    (h1 : P 1 = reflect (D₀ + 1) (R 1)) :
    ∀ n, P n = reflect (D₀ + n) (R n) := by
  suffices h : ∀ n, P n = reflect (D₀ + 1 * n) (R n) by simpa using h
  apply eq_reflect_of_linearRecurrence (k := 2) (c := 1)
    (a := fun n i => if i = 0 then b n else a n)
  · simpa [Finset.sum_range_succ, add_comm] using hP
  · simpa [Finset.sum_range_succ, ha', hb', add_comm] using hR
  · intro n i hi
    interval_cases i <;> simp_all
  · simpa using hRdeg
  · intro i hi
    interval_cases i
    · simpa using h0
    · simpa using h1

/-- Interlacing of rows `P n` of degree `D₀ + n` with positive leading coefficients from the
interlacing of their reversals `R n`, of degree `D₀ + n` with nonnegative coefficients. -/
theorem interlaces_of_eq_reflect {P R : ℕ → ℝ[X]} {D₀ : ℕ}
    (hPR : ∀ n, P n = reflect (D₀ + n) (R n)) (hdeg : ∀ n, (R n).natDegree = D₀ + n)
    (hnn : ∀ n, HasNonnegCoeffs (R n)) (hPdeg : ∀ n, (P n).natDegree = D₀ + n)
    (hPpos : ∀ n, 0 < (P n).leadingCoeff)
    (hR : ∀ n, Interlaces (R n) (R (n + 1))) (n : ℕ) : Interlaces (P n) (P (n + 1)) := by
  have hrev : ∀ m, P m = (R m).reverse := fun m => by rw [hPR, reverse, hdeg]
  have h0 : ∀ m, (R m).coeff 0 ≠ 0 := fun m => by
    have h := hPpos m
    rw [leadingCoeff, hPdeg, hPR, coeff_reflect, revAt_le le_rfl, Nat.sub_self] at h
    exact h.ne'
  have hneg : ∀ m, ∀ t ∈ (R m).roots, t < 0 := fun m t ht =>
    lt_of_le_of_ne (roots_nonpos_of_hasNonnegCoeffs (hnn m) t ht) fun h => by
      have := isRoot_of_mem_roots ht
      rw [h, IsRoot.def, ← coeff_zero_eq_eval_zero] at this
      exact h0 m this
  rw [hrev, hrev]
  exact interlaces_reverse_of_roots_neg (hR n) (hneg (n + 1)) (hneg n)

/-- Splitting of rows from the splitting of their reversals. -/
theorem splits_of_eq_reflect {P R : ℕ → ℝ[X]} {D₀ : ℕ}
    (hPR : ∀ n, P n = reflect (D₀ + n) (R n)) (hdeg : ∀ n, (R n).natDegree ≤ D₀ + n)
    (hR : ∀ n, (R n).Splits) (n : ℕ) : (P n).Splits := by
  rw [hPR]
  exact Polynomial.Splits.reflect (hR n) (hdeg n)

/-- Transfer consecutive interlacing through reflection when the reflected
rows have positive constant coefficient.  This variant derives negativity of
their roots directly and does not ask for degree data about the target rows. -/
theorem interlaces_of_eq_reflect_of_coeff_zero_pos
    {P R : ℕ → ℝ[X]} {D₀ : ℕ}
    (hPR : ∀ n, P n = reflect (D₀ + n) (R n))
    (hdeg : ∀ n, (R n).natDegree = D₀ + n)
    (hnn : ∀ n, HasNonnegCoeffs (R n))
    (hzero : ∀ n, 0 < (R n).coeff 0)
    (hR : ∀ n, Interlaces (R n) (R (n + 1))) :
    ∀ n, Interlaces (P n) (P (n + 1)) := by
  have hneg : ∀ m, ∀ t ∈ (R m).roots, t < 0 := by
    intro m t ht
    refine lt_of_le_of_ne (roots_nonpos_of_hasNonnegCoeffs (hnn m) t ht) ?_
    intro h
    have hroot := isRoot_of_mem_roots ht
    rw [h, IsRoot.def, ← coeff_zero_eq_eval_zero] at hroot
    exact (hzero m).ne' hroot
  intro n
  rw [hPR n, hPR (n + 1)]
  simpa only [reverse, hdeg] using
    interlaces_reverse_of_roots_neg (hR n) (hneg (n + 1)) (hneg n)

end RealRooted
