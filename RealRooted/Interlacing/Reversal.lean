import RealRooted.Basic.AffineInterlacing
import RealRooted.Basic.Coefficients
import RealRooted.DegreeDropReversal
import RealRooted.Mathlib.Algebra.Polynomial.Reverse

/-!
# Interlacing of reversed rows

For rows `P n` of degree `D₀ + n` with nonzero constant terms, the reversed rows
`R n = X ^ (D₀ + n) P n (1 / X)` invert the roots.  On negative roots inversion reverses the
order, so consecutive reversed rows interlace exactly when the rows do
(`interlaces_reverse_of_roots_neg`).

The reversed rows of a recurrence satisfy a recurrence of the same shape:

* `eq_reflect_of_threeTerm`: `P (n + 2) = a n P (n + 1) + b n P n` reverses to the multipliers
  `reflect 1 (a n)` and `reflect 2 (b n)`;
* `eq_reflect_of_derivRec₂`: `P (n + 1) = A₂ P'' + A₁ P' + A₀ P` reverses through
  `Polynomial.derivative_reflect`, with `θ_N r = X (N r - X r')`, `θ_N r = X u₁` and
  `θ_N (θ_N r) = X ^ 2 u₂`.

Both are stated as the link `P n = reflect (D₀ + n) (R n)` for a sequence `R` given by its own
recurrence, so that `R` can be an ordinary recursive definition.
-/

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
  have hir := (List.interleaves_reverse_reverse_of_length_add_one_eq_length
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
  have hfr' := DegreeDropReversal.roots_reverse_eq_map_inv_of_splits_coeff_zero_ne hfs hf0
  have hgr' := DegreeDropReversal.roots_reverse_eq_map_inv_of_splits_coeff_zero_ne hgs hg0
  have hfrs := DegreeDropReversal.splits_reverse hfs
  have hgrs := DegreeDropReversal.splits_reverse hgs
  have hnat : ∀ {p : ℝ[X]}, p.Splits → p.coeff 0 ≠ 0 → p.reverse.natDegree = p.natDegree := by
    intro p hp hp0
    rw [← card_roots_of_splits (DegreeDropReversal.splits_reverse hp),
      DegreeDropReversal.roots_reverse_eq_map_inv_of_splits_coeff_zero_ne hp hp0,
      Multiset.card_map, card_roots_of_splits hp]
  have hrslen : rs.length = f.natDegree := by
    rw [← card_roots_of_splits hfs, ← hfr, Multiset.coe_card]
  have hsslen : ss.length = g.natDegree := by
    rw [← card_roots_of_splits hgs, ← hgsr, Multiset.coe_card]
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

/-- `a * reflect N q = reflect (k + N) (reflect k a * q)` for `a` of degree at most `k`. -/
private lemma mul_reflect_eq {a q : ℝ[X]} {k N : ℕ} (ha : a.natDegree ≤ k)
    (hq : q.natDegree ≤ N) : a * reflect N q = reflect (k + N) (reflect k a * q) := by
  rw [reflect_mul _ _ (natDegree_reflect_le.trans (max_le le_rfl ha)) hq, reflect_reflect]

/-- A bound on `X ^ k * f` bounds `f`. -/
private lemma natDegree_le_of_X_pow_mul_le {f : ℝ[X]} {k M : ℕ}
    (h : (X ^ k * f).natDegree ≤ M + k) : f.natDegree ≤ M := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [natDegree_X_pow_mul k hf] at h
    lia

/-- `reflect (M + k) (a * (X ^ k * u)) = reflect M (a * u)` when `a * (X ^ k * u)` has degree
at most `M + k`. -/
private lemma reflect_mul_X_pow_mul {a u : ℝ[X]} {k M : ℕ}
    (h : (a * (X ^ k * u)).natDegree ≤ M + k) :
    reflect (M + k) (a * (X ^ k * u)) = reflect M (a * u) := by
  have he : a * (X ^ k * u) = X ^ k * (a * u) := by ring
  rw [he] at h ⊢
  exact reflect_X_pow_mul _ k (natDegree_le_of_X_pow_mul_le h)

/-- Reversed rows of a second-order derivative recurrence.  If `P (n + 1) = A₂ P'' + A₁ P' + A₀ P`
with `A i` of degree at most `i + 1`, and `R` satisfies the reflected recurrence (with
`N = D₀ + n`), then `P n = reflect (D₀ + n) (R n)` for all `n`. -/
theorem eq_reflect_of_derivRec₂ {P R A₂ A₁ A₀ B₂ B₁ B₀ : ℕ → ℝ[X]} {D₀ : ℕ}
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
      mul_reflect_eq (k := 3) (hA₂ n) hθθ, mul_reflect_eq (k := 2) (hA₁ n) hθ,
      mul_reflect_eq (k := 1) (hA₀ n) hr, e2, e1,
      show 3 + N = (N + 1) + 2 by lia, show 2 + N = (N + 1) + 1 by lia, add_comm 1 N,
      reflect_mul_X_pow_mul, reflect_mul_X_pow_mul, ← reflect_add, ← reflect_add,
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
  have key : ∀ n, P n = reflect (D₀ + n) (R n) ∧
      P (n + 1) = reflect (D₀ + (n + 1)) (R (n + 1)) := by
    intro n
    induction n with
    | zero => exact ⟨by simpa using h0, h1⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [hP, ih.1, ih.2, mul_reflect_eq (k := 1) (ha n) (hRdeg (n + 1)),
        mul_reflect_eq (k := 2) (hb n) (hRdeg n),
        show 1 + (D₀ + (n + 1)) = D₀ + (n + 1 + 1) by lia,
        show 2 + (D₀ + n) = D₀ + (n + 1 + 1) by lia, ← reflect_add, hR, ha', hb']
  exact fun n => (key n).1

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
  exact DegreeDropReversal.splits_reflect_of_splits (hR n) (hdeg n)

end RealRooted
