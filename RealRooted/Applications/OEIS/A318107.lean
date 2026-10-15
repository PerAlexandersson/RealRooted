import RealRooted.EulerOperator.Polar.Pencil
import RealRooted.Recurrence.RowModel
import RealRooted.Recurrence.Uniqueness

/-!
# OEIS A318107

`Op c p = X(1+X) p' + c p` and the operator `L0` acting in the variable `Y = X(1+X)`.

Proof outline for `primitivePolynomial_splits`:
* `pair_identity`: `Op (N-b) ∘ Op b` acting on `(1+X)^N · h(Y)` equals
  `(1+X)^N · ((L0 + (N-b)b) h)(Y)`.
* `qseq_roots`: starting from `qseq N 0` (which has the `N` real roots at `-1`), each `Op c`
  with `(1+X)^c` dividing its argument adds a real root (Rolle, `Op_roots_step`), so
  `qseq N (N-1)` has at least `3N-2` real roots counted with multiplicity.
* `coeff_gseq`: closed form of the coefficients, so that `qseq (n+1) n` is a nonzero multiple of
  `(1+X)^(n+1) · R(X(1+X))` with `R` the reversal of the target polynomial.
* If `R` did not split it would have at most `natDegree R - 2` real roots, and `R(X(1+X))` at most
  twice as many, contradicting the count above.
-/

open RealRooted Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A318107

/-- The Euler-type operator `p ↦ X(1+X)p' + c p`. -/
private def Op (c : ℝ) (p : ℝ[X]) : ℝ[X] := X * (1 + X) * derivative p + C c * p

/-- The quadratic `Y = X(1+X)`. -/
private def Yq : ℝ[X] := X * (1 + X)

/-- The induced operator in the variable `Y`. -/
private def L0 (N : ℝ) (h : ℝ[X]) : ℝ[X] :=
  C (N * (N + 1)) * X * h + C (N + 1) * X * derivative h + C (4 * N + 6) * X ^ 2 * derivative h
    + X ^ 2 * (1 + C 4 * X) * derivative (derivative h)

private lemma Op_pow_mul (K : ℕ) (b : ℝ) (Q : ℝ[X]) :
    Op b ((1 + X) ^ K * Q) =
      (1 + X) ^ K * (C (K : ℝ) * X * Q + X * (1 + X) * derivative Q + C b * Q) := by
  rcases K with _ | k
  · simp [Op]
  · simp only [Op, derivative_mul, derivative_pow, derivative_add, derivative_one,
      derivative_X]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    simp only [C_add, C_1, map_natCast]
    ring

private lemma pair_identity (N : ℕ) (b : ℝ) (h : ℝ[X]) :
    Op ((N : ℝ) - b) (Op b ((1 + X) ^ N * h.comp Yq)) =
      (1 + X) ^ N * (L0 N h + C (((N : ℝ) - b) * b) * h).comp Yq := by
  rw [Op_pow_mul, Op_pow_mul]
  congr 1
  simp only [L0, Yq, derivative_comp, add_comp, mul_comp, C_comp, X_comp, pow_comp, one_comp,
    derivative_mul, derivative_add, derivative_X, derivative_one, derivative_C, derivative_zero]
  simp only [C_sub, C_mul, C_add, map_natCast, C_ofNat, C_1]
  ring

private lemma L0_add (N : ℝ) (f g : ℝ[X]) : L0 N (f + g) = L0 N f + L0 N g := by
  simp only [L0, derivative_add]; ring

private lemma L0_C_mul (N r : ℝ) (f : ℝ[X]) : L0 N (C r * f) = C r * L0 N f := by
  simp only [L0, derivative_C_mul]; ring


private lemma card_roots_one_add_X_pow (k : ℕ) :
    Multiset.card ((1 + X : ℝ[X]) ^ k).roots = k := by
  have : (1 + X : ℝ[X]) = X - C (-1) := by simp [add_comm]
  rw [this, roots_pow, roots_X_sub_C]; simp

private lemma one_add_X_pow_ne_zero (k : ℕ) : ((1 + X : ℝ[X]) ^ k) ≠ 0 := by
  apply pow_ne_zero
  intro h
  have := congrArg (fun p : ℝ[X] => p.eval (0 : ℝ)) h
  simp at this

/-- Each application of `Op c` to a polynomial divisible by `(1+X)^c` creates a new real root. -/
private lemma Op_roots_step (k : ℕ) (p : ℝ[X]) (hp : p ≠ 0) (hdvd : (1 + X) ^ (k + 1) ∣ p) :
    Op ((k + 1 : ℕ) : ℝ) p ≠ 0 ∧
      Multiset.card p.roots + 1 ≤ Multiset.card (Op ((k + 1 : ℕ) : ℝ) p).roots := by
  obtain ⟨p₂, rfl⟩ := hdvd
  have hp₂ : p₂ ≠ 0 := by rintro rfl; simp at hp
  set G : ℝ[X] := C ((k + 1 : ℕ) : ℝ) * p₂ + X * derivative p₂ with hG
  have hOp : Op ((k + 1 : ℕ) : ℝ) ((1 + X) ^ (k + 1) * p₂) = (1 + X) ^ (k + 1 + 1) * G := by
    rw [Op_pow_mul, hG]; ring
  set F : ℝ[X] := X ^ (k + 1) * p₂ with hF
  have hF' : derivative F = X ^ k * G := by
    rw [hF, hG, derivative_mul, derivative_X_pow]; simp only [map_natCast, Nat.add_sub_cancel]
    ring
  have hF0 : F ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hp₂
  have hFdeg : F.natDegree = k + 1 + p₂.natDegree := by
    rw [hF, natDegree_mul (pow_ne_zero _ X_ne_zero) hp₂, natDegree_X_pow]
  have hG0 : G ≠ 0 := by
    intro hG0
    have h1 : derivative F = 0 := by rw [hF', hG0, mul_zero]
    have := Polynomial.derivative_eq_zero.mp h1
    lia
  have hrF : Multiset.card F.roots = k + 1 + Multiset.card p₂.roots := by
    rw [hF, roots_mul hF0, roots_X_pow]; simp
  have hrF' : Multiset.card (derivative F).roots = k + Multiset.card G.roots := by
    rw [hF', roots_mul (mul_ne_zero (pow_ne_zero k X_ne_zero) hG0), roots_X_pow]; simp
  have hR := card_roots_le_derivative F
  have hne : (1 + X : ℝ[X]) ^ (k + 1 + 1) * G ≠ 0 := mul_ne_zero (one_add_X_pow_ne_zero _) hG0
  refine ⟨hOp ▸ hne, ?_⟩
  rw [hOp, roots_mul hne, roots_mul hp, Multiset.card_add, Multiset.card_add,
    card_roots_one_add_X_pow, card_roots_one_add_X_pow]
  lia


private lemma coeff_L0_zero (N : ℝ) (h : ℝ[X]) : (L0 N h).coeff 0 = 0 := by
  simp [L0, mul_assoc]

private lemma coeff_L0_succ (N : ℝ) (h : ℝ[X]) (j : ℕ) :
    (L0 N h).coeff (j + 1) = ((j : ℝ) + 1) * ((j : ℝ) + 1 + N) * h.coeff (j + 1)
      + (N + 2 * j) * (N + 2 * j + 1) * h.coeff j := by
  rcases j with _ | _ | j <;>
  · simp [L0, mul_assoc, coeff_C_mul, coeff_X_mul, pow_two, mul_add, add_mul, coeff_derivative,
      Nat.cast_add]
    ring

/-- The sequence `g_0 = 1`, `g_{m+1} = (L0 + (m+1)(N-m-1)) g_m`. -/
private def gseq (N : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | m + 1 => L0 N (gseq N m) + C (((m : ℝ) + 1) * ((N : ℝ) - (m + 1))) * gseq N m

/-- The chain polynomials `(1+X)^N · ((L0 + N²) g_m)(X(1+X))`. -/
private def qseq (N m : ℕ) : ℝ[X] :=
  (1 + X) ^ N * (L0 N (gseq N m) + C ((N : ℝ) ^ 2) * gseq N m).comp Yq

private lemma qseq_succ (N m : ℕ) :
    qseq N (m + 1) = Op ((m : ℝ) + 1) (Op ((N : ℝ) - (m + 1)) (qseq N m)) := by
  have h := pair_identity N ((N : ℝ) - (m + 1)) (L0 N (gseq N m) + C ((N : ℝ) ^ 2) * gseq N m)
  have e : (N : ℝ) - ((N : ℝ) - (m + 1)) = m + 1 := by ring
  rw [e] at h
  simp only [qseq]
  rw [h, gseq]
  simp only [L0_add, L0_C_mul]
  ring_nf

private lemma qseq_roots (N : ℕ) (hN : 1 ≤ N) :
    ∀ m, m + 1 ≤ N → qseq N m ≠ 0 ∧ N + 2 * m ≤ Multiset.card (qseq N m).roots := by
  intro m
  induction m with
  | zero =>
    intro _
    have hQ : (L0 N (gseq N 0) + C ((N : ℝ) ^ 2) * gseq N 0).comp Yq ≠ 0 := by
      intro h0
      have := congrArg (fun p : ℝ[X] => p.eval 0) h0
      simp [gseq, L0, Yq] at this
      lia
    have hne := mul_ne_zero (one_add_X_pow_ne_zero N) hQ
    refine ⟨hne, ?_⟩
    rw [qseq, roots_mul hne, Multiset.card_add, card_roots_one_add_X_pow]
    lia
  | succ m ih =>
    intro hm
    obtain ⟨hq0, hqc⟩ := ih (by lia)
    obtain ⟨t, rfl⟩ : ∃ t, N = m + 2 + t := ⟨N - (m + 2), by lia⟩
    have e1 : ((m + 2 + t : ℕ) : ℝ) - ((m : ℝ) + 1) =
        ((t + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have e2 : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    have hdvd1 : (1 + X : ℝ[X]) ^ (t + 1) ∣ qseq (m + 2 + t) m :=
      (pow_dvd_pow _ (by lia)).trans (dvd_mul_right _ _)
    obtain ⟨h1, c1⟩ := Op_roots_step t _ hq0 hdvd1
    have hdvd2 : (1 + X : ℝ[X]) ^ (m + 1) ∣ Op ((t + 1 : ℕ) : ℝ) (qseq (m + 2 + t) m) := by
      rw [qseq, Op_pow_mul]
      exact (pow_dvd_pow _ (by lia)).trans (dvd_mul_right _ _)
    obtain ⟨h2, c2⟩ := Op_roots_step m _ h1 hdvd2
    rw [qseq_succ, e1, e2]
    exact ⟨h2, by lia⟩


/-- Closed form of the coefficients of `gseq (M+1) m`. -/
private def Gc (M m j : ℕ) : ℝ :=
  (m.factorial : ℝ) * (m.choose j : ℝ) * ((M + 2 * j).factorial : ℝ) /
    ((j.factorial : ℝ) * ((M - m + j).factorial : ℝ))

private lemma Gc_zero_left (M j : ℕ) : Gc M 0 j = if j = 0 then 1 else 0 := by
  rcases j with _ | j
  · simp [Gc, Nat.factorial_ne_zero]
  · simp [Gc]

private lemma Gc_step_zero (m t : ℕ) :
    Gc (m + 1 + t) (m + 1) 0 =
      ((m : ℝ) + 1) * (((m + 1 + t + 1 : ℕ) : ℝ) - (m + 1)) * Gc (m + 1 + t) m 0 := by
  have h1 : m + 1 + t - (m + 1) + 0 = t := by lia
  have h2 : m + 1 + t - m + 0 = t + 1 := by lia
  simp only [Gc, h1, h2, Nat.factorial_succ, Nat.choose_zero_right, Nat.factorial_zero]
  push_cast
  field_simp
  ring

private lemma Gc_step_succ (m t j : ℕ) :
    Gc (m + 1 + t) (m + 1) (j + 1) =
      ((j : ℝ) + 1) * ((j : ℝ) + 1 + ((m + 1 + t + 1 : ℕ) : ℝ)) * Gc (m + 1 + t) m (j + 1)
      + (((m + 1 + t + 1 : ℕ) : ℝ) + 2 * j) *
          (((m + 1 + t + 1 : ℕ) : ℝ) + 2 * j + 1) * Gc (m + 1 + t) m j
      + ((m : ℝ) + 1) * (((m + 1 + t + 1 : ℕ) : ℝ) - (m + 1)) * Gc (m + 1 + t) m (j + 1) := by
  have h1 : m + 1 + t - (m + 1) + (j + 1) = t + j + 1 := by lia
  have h2 : m + 1 + t - m + (j + 1) = t + j + 1 + 1 := by lia
  have h3 : m + 1 + t - m + j = t + j + 1 := by lia
  have h4 : m + 1 + t + 2 * (j + 1) = m + 1 + t + 2 * j + 1 + 1 := by lia
  have hD : ((m + 1).choose (j + 1) : ℝ) = (m.choose j : ℝ) + (m.choose (j + 1) : ℝ) := by
    rw [Nat.choose_succ_succ']; push_cast; ring
  have hB : (m.choose (j + 1) : ℝ) = (m.choose j : ℝ) * ((m : ℝ) - j) / ((j : ℝ) + 1) := by
    have := Nat.add_one_mul_choose_eq m j
    have h' :
        ((m + 1 : ℕ) : ℝ) * (m.choose j : ℝ) =
          ((m + 1).choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [hD] at h'
    push_cast at h'
    field_simp
    linarith
  simp only [Gc, h1, h2, h3, h4]
  rw [hD, hB]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Closed form of the coefficients of `gseq`. -/
private lemma coeff_gseq (M : ℕ) :
    ∀ m, m ≤ M → ∀ j, (gseq (M + 1) m).coeff j = Gc M m j := by
  intro m
  induction m with
  | zero =>
    intro _ j
    rw [Gc_zero_left]
    simp [gseq, coeff_one]
  | succ m ih =>
    intro hm j
    obtain ⟨t, rfl⟩ : ∃ t, M = m + 1 + t := ⟨M - (m + 1), by lia⟩
    rcases j with _ | j
    · rw [gseq, coeff_add, coeff_L0_zero, coeff_C_mul, ih (by lia), Gc_step_zero]
      ring
    · rw [gseq, coeff_add, coeff_L0_succ, coeff_C_mul, ih (by lia), ih (by lia),
        Gc_step_succ]


private lemma splits_reflect_prod (s : Multiset ℝ) :
    ∀ N, Multiset.card s ≤ N → (reflect N (s.map fun a => X - C a).prod).Splits := by
  induction s using Multiset.induction_on with
  | empty =>
    intro N _
    simp [reflect_one]
  | cons a s ih =>
    intro N hN
    simp only [Multiset.card_cons] at hN
    obtain ⟨K, rfl⟩ : ∃ K, N = 1 + K := ⟨N - 1, by lia⟩
    rw [Multiset.map_cons, Multiset.prod_cons,
      reflect_mul _ _ (natDegree_X_sub_C_le a)
        ((natDegree_multiset_prod_X_sub_C_eq_card s).le.trans (by lia))]
    refine Splits.mul (Splits.of_natDegree_le_one ?_) (ih K (by lia))
    exact natDegree_reflect_le.trans (max_le le_rfl (natDegree_X_sub_C_le a))

private lemma splits_reflect {f : ℝ[X]} (hf : f.Splits) {N : ℕ} (hN : f.natDegree ≤ N) :
    (reflect N f).Splits := by
  by_cases h0 : f = 0
  · subst h0; simp
  rw [hf.eq_prod_roots, reflect_C_mul]
  refine Splits.mul (Splits.C _) (splits_reflect_prod _ N ?_)
  have := hf.natDegree_eq_card_roots
  lia

private lemma card_roots_add_two_le {f : ℝ[X]} (hns : ¬ f.Splits) :
    Multiset.card f.roots + 2 ≤ f.natDegree := by
  obtain ⟨q, he, hdeg, hq⟩ := exists_prod_multiset_X_sub_C_mul f
  have h0 : q.natDegree ≠ 0 := by
    intro h; apply hns; rw [splits_iff_card_roots]; lia
  have h1 : q.natDegree ≠ 1 := by
    intro h
    have := splits_iff_card_roots.mp (Splits.of_natDegree_eq_one h)
    rw [hq] at this; simp at this; lia
  lia

private lemma natDegree_Yq : Yq.natDegree = 2 := by
  rw [Yq]; compute_degree!

private lemma card_roots_comp_Yq_le {f : ℝ[X]} (hf : f ≠ 0) :
    Multiset.card (f.comp Yq).roots ≤ 2 * Multiset.card f.roots := by
  obtain ⟨q, he, hdeg, hq⟩ := exists_prod_multiset_X_sub_C_mul f
  have hq0 : q ≠ 0 := by rintro rfl; simp at he; exact hf he.symm
  have hcomp : f.comp Yq ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [natDegree_comp, natDegree_Yq, natDegree_zero] at this
    have hfd : f.natDegree = 0 := by lia
    rw [eq_C_of_natDegree_eq_zero hfd, C_comp] at h
    rw [eq_C_of_natDegree_eq_zero hfd] at hf
    simp_all
  have hqY : (q.comp Yq).roots = 0 := by
    refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
    have hx' : (q.comp Yq).IsRoot x := isRoot_of_mem_roots hx
    rw [IsRoot, eval_comp] at hx'
    have : Yq.eval x ∈ q.roots := (mem_roots hq0).mpr hx'
    rw [hq] at this; simp at this
  have key : f.comp Yq = ((f.roots.map fun a => X - C a).prod).comp Yq * q.comp Yq := by
    rw [← mul_comp, he]
  rw [key] at hcomp ⊢
  rw [roots_mul hcomp, hqY, add_zero]
  refine (card_roots' _).trans ?_
  rw [natDegree_comp, natDegree_Yq, natDegree_multiset_prod_X_sub_C_eq_card]
  lia

/-- The factorial-coefficient primitive underlying consecutive A318107 rows. -/
def primitivePolynomial (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 2),
    C ((Nat.factorial (3 * (n + 1 - k) + k - 1) : ℝ) /
      ((Nat.factorial (n + 1 - k) : ℝ) ^ 3 * (Nat.factorial k : ℝ))) * X ^ k

private lemma coeff_primitivePolynomial (n k : ℕ) :
    (primitivePolynomial n).coeff k = if k < n + 2 then
      (Nat.factorial (3 * (n + 1 - k) + k - 1) : ℝ) /
        ((Nat.factorial (n + 1 - k) : ℝ) ^ 3 * (Nat.factorial k : ℝ)) else 0 := by
  simp only [primitivePolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]

private lemma natDegree_primitivePolynomial_le (n : ℕ) :
    (primitivePolynomial n).natDegree ≤ n + 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_primitivePolynomial, ite_eq_right]
  exact_mod_cast (by lia : ¬ k < n + 2)

private lemma coeff_reflect_primitivePolynomial (n j : ℕ) (hj : j ≤ n + 1) :
    (reflect (n + 1) (primitivePolynomial n)).coeff j =
      ((n + 2 * j).factorial : ℝ) /
        ((j.factorial : ℝ) ^ 3 * ((n + 1 - j).factorial : ℝ)) := by
  rw [coeff_reflect, revAt_le hj, coeff_primitivePolynomial, ite_eq_left (by lia)]
  have h1 : n + 1 - (n + 1 - j) = j := by lia
  have h2 : 3 * j + (n + 1 - j) - 1 = n + 2 * j := by lia
  rw [h1, h2]

private lemma coeff_reflect_primitivePolynomial_gt (n j : ℕ) (hj : n + 1 < j) :
    (reflect (n + 1) (primitivePolynomial n)).coeff j = 0 := by
  rw [coeff_reflect, revAt_eq_self_of_lt hj, coeff_primitivePolynomial,
    ite_eq_right (by lia)]

private lemma primitive_final_identity (n : ℕ) :
    L0 ((n + 1 : ℕ) : ℝ) (gseq (n + 1) n) +
        C (((n + 1 : ℕ) : ℝ) ^ 2) * gseq (n + 1) n =
      C (((n : ℝ) + 1) ^ 3 * (n.factorial : ℝ) ^ 2) *
        reflect (n + 1) (primitivePolynomial n) := by
  ext j
  rcases j with _ | j
  · rw [coeff_add, coeff_L0_zero, coeff_C_mul, coeff_C_mul, coeff_gseq n n le_rfl,
      coeff_reflect_primitivePolynomial n 0 (by lia)]
    simp only [Gc, Nat.sub_self, Nat.choose_zero_right, Nat.factorial_zero, add_zero,
      mul_zero, Nat.sub_zero, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · rw [coeff_add, coeff_L0_succ, coeff_C_mul, coeff_C_mul, coeff_gseq n n le_rfl,
      coeff_gseq n n le_rfl]
    by_cases hj : j ≤ n
    · rw [coeff_reflect_primitivePolynomial n (j + 1) (by lia)]
      obtain ⟨r, rfl⟩ : ∃ r, n = j + r := ⟨n - j, by lia⟩
      have i1 : j + r - (j + r) + (j + 1) = j + 1 := by lia
      have i2 : j + r - (j + r) + j = j := by lia
      have i3 : j + r + 2 * (j + 1) = j + r + 2 * j + 1 + 1 := by lia
      have i4 : j + r + 1 - (j + 1) = r := by lia
      have hB : ((j + r).choose (j + 1) : ℝ) =
          ((j + r).choose j : ℝ) * r / ((j : ℝ) + 1) := by
        have h := Nat.choose_succ_right_eq (j + r) j
        rw [show j + r - j = r by lia] at h
        have h' : ((j + r).choose (j + 1) : ℝ) * ((j : ℝ) + 1) =
            ((j + r).choose j : ℝ) * r := by
          exact_mod_cast h
        field_simp
        linarith
      have hA : (((j + r).factorial : ℕ) : ℝ) =
          ((j + r).choose j : ℝ) * (j.factorial : ℝ) * (r.factorial : ℝ) := by
        have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ j + r by lia)
        rw [show j + r - j = r by lia] at h
        exact_mod_cast h.symm
      simp only [Gc, i1, i2, i3, i4]
      rw [hB, hA]
      simp only [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · rw [coeff_reflect_primitivePolynomial_gt n (j + 1) (by lia)]
      simp [Gc, Nat.choose_eq_zero_of_lt (show n < j + 1 by lia),
        Nat.choose_eq_zero_of_lt (show n < j by lia)]

/-- The factorial primitive underlying A318107 has only real roots.

The proof was found by Aristotle (Harmonic). -/
theorem primitivePolynomial_splits (n : ℕ) : (primitivePolynomial n).Splits := by
  set R := reflect (n + 1) (primitivePolynomial n) with hRdef
  have hP : primitivePolynomial n = reflect (n + 1) R := reflect_reflect.symm
  have hRdeg : R.natDegree ≤ n + 1 :=
    natDegree_reflect_le.trans (max_le le_rfl (natDegree_primitivePolynomial_le n))
  rw [hP]
  refine splits_reflect ?_ hRdeg
  by_contra hns
  have h1 := card_roots_add_two_le hns
  obtain ⟨hq0, hqc⟩ := qseq_roots (n + 1) (by lia) n (by lia)
  set K : ℝ := ((n : ℝ) + 1) ^ 3 * (n.factorial : ℝ) ^ 2 with hKdef
  have hK : K ≠ 0 := by positivity
  have hq : qseq (n + 1) n =
      (1 + X) ^ (n + 1) * (C K * R.comp Yq) := by
    rw [qseq, primitive_final_identity, C_mul_comp]
  rw [hq] at hq0 hqc
  have hR0 : R ≠ 0 := by
    rintro h
    rw [h] at hq0
    simp at hq0
  rw [roots_mul hq0, Multiset.card_add, card_roots_one_add_X_pow,
    roots_C_mul _ hK] at hqc
  have h2 := card_roots_comp_Yq_le hR0
  lia

/-- The polynomial model for the A318107 rows. -/
def polynomial (n : ℕ) : ℝ[X] :=
  (primitivePolynomial n).derivative

private lemma primitivePolynomial_coeff_pos {n j : ℕ} (hj : j ≤ n + 1) :
    0 < (primitivePolynomial n).coeff j := by
  rw [coeff_primitivePolynomial, ite_eq_left (by lia)]
  positivity

private lemma primitivePolynomial_natDegree (n : ℕ) :
    (primitivePolynomial n).natDegree = n + 1 := by
  apply le_antisymm (natDegree_primitivePolynomial_le n)
  exact le_natDegree_of_ne_zero (ne_of_gt (primitivePolynomial_coeff_pos le_rfl))

private lemma primitivePolynomial_nonneg (n : ℕ) :
    HasNonnegCoeffs (primitivePolynomial n) := by
  intro j
  rw [coeff_primitivePolynomial]
  split_ifs
  · positivity
  · exact le_rfl

private lemma primitivePolynomial_pf (n : ℕ) :
    IsPFPolynomial (primitivePolynomial n) :=
  IsPFPolynomial.of_realRooted_nonneg (primitivePolynomial_nonneg n)
    (primitivePolynomial_splits n)

private lemma coeff_polynomial (n j : ℕ) :
    (polynomial n).coeff j = if j ≤ n then
      (Nat.factorial (3 * (n - j) + j) : ℝ) /
        ((Nat.factorial (n - j) : ℝ) ^ 3 * (Nat.factorial j : ℝ)) else 0 := by
  rw [polynomial, coeff_derivative, coeff_primitivePolynomial]
  by_cases hj : j ≤ n
  · rw [ite_eq_left (by lia), ite_eq_left hj]
    have hsub : n + 1 - (j + 1) = n - j := by lia
    have hfac : (Nat.factorial (j + 1) : ℝ) = (j + 1) * Nat.factorial j := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hsub, show 3 * (n - j) + (j + 1) - 1 = 3 * (n - j) + j by lia,
      hfac]
    field_simp
  · rw [ite_eq_right hj, ite_eq_right (by lia)]
    ring

private def rowCoeff (m k : ℕ) : ℝ :=
  (Nat.factorial (3 * m + k) : ℝ) /
    ((Nat.factorial m : ℝ) ^ 3 * (Nat.factorial k : ℝ))

private lemma coeff_polynomial_eq_rowCoeff (n j : ℕ) :
    (polynomial n).coeff j = if j ≤ n then rowCoeff (n - j) j else 0 := by
  rw [coeff_polynomial]
  rfl

private lemma rowCoeff_zero_left (k : ℕ) : rowCoeff 0 k = 1 := by
  have hk : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  unfold rowCoeff
  simp only [Nat.mul_zero, Nat.zero_add, Nat.factorial_zero, Nat.cast_one, one_pow,
    one_mul]
  exact div_self hk.ne'

private lemma rowCoeff_succ_k (m k : ℕ) :
    ((k : ℝ) + 1) * rowCoeff m (k + 1) =
      (3 * (m : ℝ) + k + 1) * rowCoeff m k := by
  have hm : (0 : ℝ) < (Nat.factorial m : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hk : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have e1 :
      (Nat.factorial (3 * m + (k + 1)) : ℝ) =
        (3 * (m : ℝ) + k + 1) * (Nat.factorial (3 * m + k) : ℝ) := by
    rw [show 3 * m + (k + 1) = (3 * m + k) + 1 by lia, Nat.factorial_succ]
    push_cast
    ring
  have e2 : (Nat.factorial (k + 1) : ℝ) =
      ((k : ℝ) + 1) * (Nat.factorial k : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  unfold rowCoeff
  rw [e1, e2]
  field_simp

private lemma rowCoeff_succ_m (m k : ℕ) :
    ((m : ℝ) + 1) ^ 3 * rowCoeff (m + 1) k =
      (3 * (m : ℝ) + k + 1) * (3 * (m : ℝ) + k + 2) *
        (3 * (m : ℝ) + k + 3) * rowCoeff m k := by
  have hm : (0 : ℝ) < (Nat.factorial m : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hk : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have e1 :
      (Nat.factorial (3 * (m + 1) + k) : ℝ) =
        (3 * (m : ℝ) + k + 1) * (3 * (m : ℝ) + k + 2) *
          (3 * (m : ℝ) + k + 3) * (Nat.factorial (3 * m + k) : ℝ) := by
    rw [show 3 * (m + 1) + k = ((3 * m + k) + 1 + 1) + 1 by lia,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have e2 : (Nat.factorial (m + 1) : ℝ) =
      ((m : ℝ) + 1) * (Nat.factorial m : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  unfold rowCoeff
  rw [e1, e2]
  field_simp

private lemma rowCoeff_master (w i : ℕ) :
    ((w : ℝ) + i + 3) ^ 2 * rowCoeff (w + 1) (i + 2) =
      -(18 * ((w : ℝ) + i + 1) + 30) * ((i : ℝ) + 2) * rowCoeff w (i + 2) +
        -(9 * ((w : ℝ) + i + 1) + 15) / 2 * ((i : ℝ) + 1) *
          rowCoeff (w + 1) (i + 1) +
        (27 * ((w : ℝ) + i + 1) ^ 2 + 81 * ((w : ℝ) + i + 1) + 60) *
          rowCoeff w (i + 2) +
        (5 * ((w : ℝ) + i + 1) ^ 2 + 15 * ((w : ℝ) + i + 1) + 11) *
          rowCoeff (w + 1) (i + 1) +
        ((w : ℝ) + i + 2) ^ 2 / 2 * rowCoeff (w + 1) i := by
  have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
  have hi2 : ((i : ℝ) + 2) ≠ 0 := by positivity
  have hw1 : ((w : ℝ) + 1) ≠ 0 := by positivity
  have hidx : i + 1 + 1 = i + 2 := by lia
  have h1 : rowCoeff w (i + 1) =
      (3 * (w : ℝ) + i + 1) / ((i : ℝ) + 1) * rowCoeff w i := by
    have e := rowCoeff_succ_k w i
    field_simp
    linear_combination e
  have h2 : rowCoeff w (i + 2) =
      (3 * (w : ℝ) + i + 2) / ((i : ℝ) + 2) * rowCoeff w (i + 1) := by
    have e := rowCoeff_succ_k w (i + 1)
    rw [hidx] at e
    push_cast at e
    field_simp
    linear_combination e
  have h3 : rowCoeff (w + 1) i =
      (3 * (w : ℝ) + i + 1) * (3 * (w : ℝ) + i + 2) *
        (3 * (w : ℝ) + i + 3) / ((w : ℝ) + 1) ^ 3 * rowCoeff w i := by
    have e := rowCoeff_succ_m w i
    field_simp
    linear_combination e
  have h4 : rowCoeff (w + 1) (i + 1) =
      (3 * (w : ℝ) + i + 4) / ((i : ℝ) + 1) * rowCoeff (w + 1) i := by
    have e := rowCoeff_succ_k (w + 1) i
    push_cast at e
    field_simp
    linear_combination e
  have h5 : rowCoeff (w + 1) (i + 2) =
      (3 * (w : ℝ) + i + 5) / ((i : ℝ) + 2) * rowCoeff (w + 1) (i + 1) := by
    have e := rowCoeff_succ_k (w + 1) (i + 1)
    rw [hidx] at e
    push_cast at e
    field_simp
    linear_combination e
  rw [h5, h4, h3, h2, h1]
  field_simp
  ring

private def primitiveCoeff (m k : ℕ) : ℝ :=
  (Nat.factorial (3 * m + k - 1) : ℝ) /
    ((Nat.factorial m : ℝ) ^ 3 * (Nat.factorial k : ℝ))

private lemma primitiveCoeff_pencil (m k : ℕ) :
    (3 * (m : ℝ) + 3 * ((k : ℝ) + 1)) * primitiveCoeff m (k + 1) =
      rowCoeff m (k + 1) + 2 * rowCoeff m k := by
  have hm : (0 : ℝ) < (Nat.factorial m : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hk : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hs : 3 * m + (k + 1) - 1 = 3 * m + k := by lia
  have e1 :
      (Nat.factorial (3 * m + (k + 1)) : ℝ) =
        (3 * (m : ℝ) + k + 1) * (Nat.factorial (3 * m + k) : ℝ) := by
    rw [show 3 * m + (k + 1) = (3 * m + k) + 1 by lia, Nat.factorial_succ]
    push_cast
    ring
  have e2 :
      (Nat.factorial (k + 1) : ℝ) =
        ((k : ℝ) + 1) * (Nat.factorial k : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  unfold primitiveCoeff rowCoeff
  rw [hs, e1, e2]
  field_simp
  ring

private lemma primitiveCoeff_pencil_zero (m : ℕ) :
    (3 * (m : ℝ) + 3) * primitiveCoeff (m + 1) 0 = rowCoeff (m + 1) 0 := by
  have hm : (0 : ℝ) < (Nat.factorial (m + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hcast : ((3 * (m + 1) - 1 : ℕ) : ℝ) = 3 * (m : ℝ) + 2 := by
    rw [show 3 * (m + 1) - 1 = 3 * m + 2 by lia]
    push_cast
    ring
  have e1 :
      (Nat.factorial (3 * (m + 1)) : ℝ) =
        (3 * (m : ℝ) + 3) * (Nat.factorial (3 * (m + 1) - 1) : ℝ) := by
    rw [show 3 * (m + 1) = (3 * (m + 1) - 1) + 1 by lia, Nat.factorial_succ]
    push_cast
    rw [hcast]
    ring
  unfold primitiveCoeff rowCoeff
  simp only [Nat.add_zero]
  rw [e1]
  field_simp

private lemma polynomial_succ_pencil (n : ℕ) :
    polynomial (n + 1) = C (3 * (n : ℝ) + 3) * primitivePolynomial n -
      C 2 * (X * polynomial n) := by
  ext j
  rw [coeff_sub, coeff_C_mul, coeff_C_mul, coeff_polynomial,
    coeff_primitivePolynomial]
  match j with
  | 0 =>
      rw [ite_eq_left (by lia), ite_eq_left (by lia), coeff_X_mul_zero]
      change rowCoeff (n + 1) 0 =
        (3 * (n : ℝ) + 3) * primitiveCoeff (n + 1) 0 - 2 * 0
      rw [primitiveCoeff_pencil_zero]
      ring
  | k + 1 =>
      rw [coeff_X_mul, coeff_polynomial]
      by_cases hk : k ≤ n
      · rw [ite_eq_left (by lia), ite_eq_left (by lia), ite_eq_left hk,
          show n + 1 - (k + 1) = n - k by lia]
        change rowCoeff (n - k) (k + 1) =
          (3 * (n : ℝ) + 3) * primitiveCoeff (n - k) (k + 1) -
            2 * rowCoeff (n - k) k
        have h := primitiveCoeff_pencil (n - k) k
        rw [Nat.cast_sub hk] at h
        have hfactor : 3 * ((n : ℝ) - k) + 3 * ((k : ℝ) + 1) =
            3 * (n : ℝ) + 3 := by ring
        rw [hfactor] at h
        linarith
      · rw [ite_eq_right (by lia), ite_eq_right (by lia), ite_eq_right hk]
        ring

private lemma polynomial_recurrence_cleared (n : ℕ) :
    C (((n : ℝ) + 2) ^ 2) * polynomial (n + 2) =
      (C (-(18 * (n : ℝ) + 30)) * X +
          C (-(9 * (n : ℝ) + 15) / 2) * X ^ 2) *
        (polynomial (n + 1)).derivative +
      (C (27 * (n : ℝ) ^ 2 + 81 * (n : ℝ) + 60) +
          C (5 * (n : ℝ) ^ 2 + 15 * (n : ℝ) + 11) * X) *
        polynomial (n + 1) +
      (C (((n : ℝ) + 1) ^ 2 / 2) * X ^ 2) * polynomial n := by
  have hexp :
      (C (-(18 * (n : ℝ) + 30)) * X +
          C (-(9 * (n : ℝ) + 15) / 2) * X ^ 2) *
          (polynomial (n + 1)).derivative +
        (C (27 * (n : ℝ) ^ 2 + 81 * (n : ℝ) + 60) +
            C (5 * (n : ℝ) ^ 2 + 15 * (n : ℝ) + 11) * X) *
          polynomial (n + 1) +
        (C (((n : ℝ) + 1) ^ 2 / 2) * X ^ 2) * polynomial n =
      C (-(18 * (n : ℝ) + 30)) * (X * (polynomial (n + 1)).derivative) +
        C (-(9 * (n : ℝ) + 15) / 2) *
          (X * (X * (polynomial (n + 1)).derivative)) +
        C (27 * (n : ℝ) ^ 2 + 81 * (n : ℝ) + 60) * polynomial (n + 1) +
        C (5 * (n : ℝ) ^ 2 + 15 * (n : ℝ) + 11) *
          (X * polynomial (n + 1)) +
        C (((n : ℝ) + 1) ^ 2 / 2) * (X * (X * polynomial n)) := by
    ring
  rw [hexp]
  ext j
  simp only [coeff_add, coeff_C_mul]
  clear hexp
  match j with
  | 0 =>
      have hX : ∀ p : ℝ[X], (X * p).coeff 0 = 0 := fun p => by simp
      have c1 : (polynomial (n + 2)).coeff 0 = rowCoeff (n + 2) 0 := by
        rw [coeff_polynomial_eq_rowCoeff]
        simp
      have c2 : (polynomial (n + 1)).coeff 0 = rowCoeff (n + 1) 0 := by
        rw [coeff_polynomial_eq_rowCoeff]
        simp
      have e := rowCoeff_succ_m (n + 1) 0
      rw [show n + 1 + 1 = n + 2 by lia] at e
      push_cast at e
      have hT : rowCoeff (n + 2) 0 =
          (3 * (n : ℝ) + 4) * (3 * (n : ℝ) + 5) * (3 * (n : ℝ) + 6) /
            ((n : ℝ) + 2) ^ 3 * rowCoeff (n + 1) 0 := by
        field_simp
        linear_combination e
      simp only [hX, mul_zero, zero_add, add_zero, c1, c2, hT]
      field_simp
      ring
  | 1 =>
      have hX : ∀ p : ℝ[X], (X * p).coeff 0 = 0 := fun p => by simp
      have c1 : (polynomial (n + 2)).coeff 1 = rowCoeff (n + 1) 1 := by
        rw [coeff_polynomial_eq_rowCoeff, ite_eq_left (by lia),
          show n + 2 - 1 = n + 1 by lia]
      have c2 : (polynomial (n + 1)).coeff 1 = rowCoeff n 1 := by
        rw [coeff_polynomial_eq_rowCoeff, ite_eq_left (by lia),
          show n + 1 - 1 = n by lia]
      have c3 : (polynomial (n + 1)).coeff 0 = rowCoeff (n + 1) 0 := by
        rw [coeff_polynomial_eq_rowCoeff]
        simp
      have e1 := rowCoeff_succ_k n 0
      have e2 := rowCoeff_succ_m n 0
      have e3 := rowCoeff_succ_k (n + 1) 0
      push_cast at e1 e2 e3
      have hA : rowCoeff n 1 = (3 * (n : ℝ) + 1) * rowCoeff n 0 := by
        linear_combination e1
      have hB : rowCoeff (n + 1) 0 =
          (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2) * (3 * (n : ℝ) + 3) /
            ((n : ℝ) + 1) ^ 3 * rowCoeff n 0 := by
        rw [div_mul_eq_mul_div, eq_div_iff (by positivity : ((n : ℝ) + 1) ^ 3 ≠ 0)]
        linear_combination e2
      have hC : rowCoeff (n + 1) 1 =
          (3 * (n : ℝ) + 4) * rowCoeff (n + 1) 0 := by
        linear_combination e3
      simp only [coeff_X_mul, hX, coeff_derivative, mul_zero, add_zero, c1, c2, c3,
        hC, hB, hA]
      field_simp
      ring
  | i + 2 =>
      simp only [coeff_X_mul, coeff_derivative, show i + 1 + 1 = i + 2 by lia]
      rcases Nat.lt_or_ge i n with hi | hi
      · obtain ⟨w, rfl⟩ : ∃ w, n = w + i + 1 := ⟨n - i - 1, by lia⟩
        rw [show (polynomial (w + i + 1 + 2)).coeff (i + 2) =
              rowCoeff (w + 1) (i + 2) by
              rw [coeff_polynomial_eq_rowCoeff, ite_eq_left (by lia),
                show w + i + 1 + 2 - (i + 2) = w + 1 by lia],
          show (polynomial (w + i + 1 + 1)).coeff (i + 2) =
              rowCoeff w (i + 2) by
              rw [coeff_polynomial_eq_rowCoeff, ite_eq_left (by lia),
                show w + i + 1 + 1 - (i + 2) = w by lia],
          show (polynomial (w + i + 1 + 1)).coeff (i + 1) =
              rowCoeff (w + 1) (i + 1) by
              rw [coeff_polynomial_eq_rowCoeff, ite_eq_left (by lia),
                show w + i + 1 + 1 - (i + 1) = w + 1 by lia],
          show (polynomial (w + i + 1)).coeff i = rowCoeff (w + 1) i by
              rw [coeff_polynomial_eq_rowCoeff, ite_eq_left (by lia),
                show w + i + 1 - i = w + 1 by lia]]
        push_cast
        linear_combination rowCoeff_master w i
      · rcases Nat.eq_or_lt_of_le hi with hn | hn
        · subst hn
          rw [show (polynomial (n + 2)).coeff (n + 2) = rowCoeff 0 (n + 2) by
                rw [coeff_polynomial_eq_rowCoeff, ite_eq_left (by lia),
                  show n + 2 - (n + 2) = 0 by lia],
            show (polynomial (n + 1)).coeff (n + 2) = 0 by
                rw [coeff_polynomial_eq_rowCoeff, ite_eq_right (by lia)],
            show (polynomial (n + 1)).coeff (n + 1) = rowCoeff 0 (n + 1) by
                rw [coeff_polynomial_eq_rowCoeff, ite_eq_left (by lia),
                  show n + 1 - (n + 1) = 0 by lia],
            show (polynomial n).coeff n = rowCoeff 0 n by
                rw [coeff_polynomial_eq_rowCoeff, ite_eq_left (by lia),
                  show n - n = 0 by lia]]
          rw [rowCoeff_zero_left, rowCoeff_zero_left, rowCoeff_zero_left]
          push_cast
          ring
        · rw [show (polynomial (n + 2)).coeff (i + 2) = 0 by
                rw [coeff_polynomial_eq_rowCoeff, ite_eq_right (by lia)],
            show (polynomial (n + 1)).coeff (i + 2) = 0 by
                rw [coeff_polynomial_eq_rowCoeff, ite_eq_right (by lia)],
            show (polynomial (n + 1)).coeff (i + 1) = 0 by
                rw [coeff_polynomial_eq_rowCoeff, ite_eq_right (by lia)],
            show (polynomial n).coeff i = 0 by
                rw [coeff_polynomial_eq_rowCoeff, ite_eq_right (by lia)]]
          ring

/-- The generated downstream lag-two update for A318107. -/
def nextRow (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  (C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + (-2 * (n : ℝ)))) *
        (-30 + (-18 * (n : ℝ)))) * X +
      C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + (-2 * (n : ℝ)))) *
        ((-15 / 2) + ((-9 / 2) * (n : ℝ)))) * X ^ 2) * p.derivative +
    (C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + (-2 * (n : ℝ)))) *
        (-183 + (-81 * (n : ℝ)) + 27 * (3 + (n : ℝ)) ^ 2)) +
      C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + (-2 * (n : ℝ)))) *
        (-34 + (-15 * (n : ℝ)) + 5 * (3 + (n : ℝ)) ^ 2)) * X) * p +
    C ((1 / (-5 + (3 + (n : ℝ)) ^ 2 + (-2 * (n : ℝ)))) *
      (-4 + (1 / 2) * (3 + (n : ℝ)) ^ 2 + (-2 * (n : ℝ)))) * X ^ 2 * q

/-- The A318107 coefficient model satisfies the downstream recurrence. -/
theorem polynomial_recurrence (n : ℕ) :
    polynomial (n + 2) = nextRow n (polynomial (n + 1)) (polynomial n) := by
  have hdeneq : -5 + (3 + (n : ℝ)) ^ 2 + (-2 * (n : ℝ)) =
      ((n : ℝ) + 2) ^ 2 := by ring
  have hscale : C (((n : ℝ) + 2) ^ 2) ≠ 0 := by
    rw [ne_eq, C_eq_zero]
    positivity
  apply mul_left_cancel₀ hscale
  rw [polynomial_recurrence_cleared]
  apply Polynomial.funext
  intro x
  simp only [nextRow]
  rw [hdeneq]
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
  field_simp
  ring

private lemma primitivePolynomial_shift_degree (n : ℕ) :
    2 ≤ (reciprocalShift (n + 2) (primitivePolynomial n)).natDegree := by
  have hcoeff :
      (reciprocalShift (n + 2) (primitivePolynomial n)).coeff (n + 2) ≠ 0 := by
    rw [coeff_reciprocalShift, revAt_le (by lia)]
    rw [coeff_primitivePolynomial, ite_eq_left (by lia)]
    positivity
  exact (by lia : 2 ≤ n + 2) |>.trans (le_natDegree_of_ne_zero hcoeff)

/-- Consecutive A318107 model rows strictly interlace. -/
theorem polynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (polynomial n) (polynomial (n + 1)) := by
  by_cases hn0 : n = 0
  · subst n
    have hbase : StrictInterl (1 : ℝ[X]) (C 6 + X) :=
      (interlaces_one_linear (p := C 6 + X) (by compute_degree!)).toStrictInterl
    have hrow0 : polynomial 0 = 1 := by
      ext k
      simp [polynomial, primitivePolynomial, Finset.sum_range_succ]
    have hrow1 : polynomial 1 = C 6 + X := by
      ext k
      rcases k with _ | k
      · norm_num [polynomial, primitivePolynomial, Finset.sum_range_succ]
      · rcases k with _ | k
        · norm_num [polynomial, primitivePolynomial, Finset.sum_range_succ]
        · simp [polynomial, primitivePolynomial, Finset.sum_range_succ, coeff_one,
            coeff_X]
    rw [hrow0, hrow1]
    exact hbase
  let p := primitivePolynomial n
  have hpf : IsPFPolynomial p := primitivePolynomial_pf n
  have hdeg : p.natDegree = n + 1 := primitivePolynomial_natDegree n
  have hpolar : StrictInterl (polarTheta (n + 2) p) p :=
    strictInterl_polarTheta_self hpf (by lia) (primitivePolynomial_shift_degree n)
  have hderpolar : StrictInterl p.derivative (polarTheta (n + 2) p) := by
    apply strictInterl_derivative_polarTheta hpf
    · rw [hdeg]
      lia
    · rw [hdeg]
      lia
    · exact hpolar
  rw [polynomial_succ_pencil, polynomial]
  have hpencil :
      C (3 * (n : ℝ) + 3) * p - C 2 * (X * p.derivative) =
        C 2 * polarTheta (n + 2) p + C ((n - 1 : ℕ) : ℝ) * p := by
    ext k
    unfold polarTheta theta
    rw [Nat.cast_sub (by lia : 1 ≤ n)]
    simp only [coeff_sub, coeff_add, coeff_C_mul]
    push_cast
    ring
  rw [hpencil]
  by_cases hn : n = 1
  · subst n
    simpa using hderpolar.C_mul_right (by norm_num : (2 : ℝ) ≠ 0)
  · have hpder : StrictInterl p.derivative p :=
      (derivative_interlaces_of_natDegree_ne_zero
        (primitivePolynomial_splits n) (by rw [hdeg]; lia)).toStrictInterl
    have hnsub : 0 < n - 1 := by lia
    have hcastpos : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hnsub
    apply StrictInterl.add_of_left
    · exact hderpolar.C_mul_right (by norm_num)
    · exact hpder.C_mul_right hcastpos.ne'
    · exact hasPosLeadingCoeff_C_mul (by norm_num)
        ((polarTheta_preserves_pf hpf (by lia)).hasNonnegCoeffs.pos_leadingCoeff
          (by
            intro hz
            exact hderpolar.2.1.1 hz))
    · exact hasPosLeadingCoeff_C_mul hcastpos
        (hpf.hasNonnegCoeffs.pos_leadingCoeff (by
          intro hz
          rw [hz] at hdeg
          simp at hdeg))

/-- The A318107 model has degree `n`. -/
theorem polynomial_natDegree (n : ℕ) : (polynomial n).natDegree = n := by
  rw [polynomial, Polynomial.natDegree_derivative, primitivePolynomial_natDegree]
  lia

/-- Every A318107 model row splits over the reals. -/
theorem polynomial_splits (n : ℕ) : (polynomial n).Splits :=
  (primitivePolynomial_splits n).derivative

/-- Consecutive A318107 model rows interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) :=
  (polynomial_strictInterl_succ n).toInterlaces (by
    rw [polynomial_natDegree, polynomial_natDegree])

private theorem polynomial_zero : polynomial 0 = 1 := by
  ext k
  rw [coeff_polynomial_eq_rowCoeff]
  rcases k with _ | k
  · norm_num [rowCoeff, coeff_one]
  · simp [coeff_one]

private theorem polynomial_one : polynomial 1 = 6 + X := by
  ext k
  rw [coeff_polynomial_eq_rowCoeff]
  rcases k with _ | _ | k
  · norm_num [rowCoeff, coeff_add, coeff_X]
  · norm_num [rowCoeff, coeff_add, coeff_X]
  · simp [coeff_add, coeff_X]

private theorem polynomial_two : polynomial 2 = 90 + 24 * X + X ^ 2 := by
  ext k
  rw [coeff_polynomial_eq_rowCoeff]
  rcases k with _ | _ | _ | k
  · norm_num [rowCoeff, coeff_add, coeff_X, coeff_X_pow]
  · norm_num [rowCoeff, coeff_add, coeff_X, coeff_X_pow]
  · norm_num [rowCoeff, coeff_add, coeff_X, coeff_X_pow]
  · simp [coeff_add, coeff_X, coeff_X_pow]

/-- A sequence with the A318107 initial rows and update has split rows. -/
@[rr_row_model]
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 6 + X)
    (_htwo : P 2 = 90 + 24 * X + X ^ 2)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans polynomial_zero.symm) (hone.trans polynomial_one.symm)
    hrec polynomial_recurrence
  rw [heq n]
  exact polynomial_splits n

/-- Consecutive rows of a sequence with the A318107 initial rows and update interlace. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 6 + X)
    (_htwo : P 2 = 90 + 24 * X + X ^ 2)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans polynomial_zero.symm) (hone.trans polynomial_one.symm)
    hrec polynomial_recurrence
  rw [heq n, heq (n + 1)]
  exact polynomial_interlaces n

/-- A sequence with the A318107 initial rows and update has degree `n` in row `n`. -/
@[rr_row_model]
theorem natDegree_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 6 + X)
    (_htwo : P 2 = 90 + 24 * X + X ^ 2)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).natDegree = n := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans polynomial_zero.symm) (hone.trans polynomial_one.symm)
    hrec polynomial_recurrence
  rw [heq n]
  exact polynomial_natDegree n

end RealRooted.Applications.OEIS.A318107
