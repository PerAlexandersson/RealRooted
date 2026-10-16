module

public import Mathlib
public import RealRooted.Combinatorics.ForcedSteps
public import RealRooted.Combinatorics.SortingFixedPoints

/-!
Aristotle project `c46dc43c-0f1b-436e-852d-810faecd9567`, adapted locally.
Paper equation `eq:fuLinZengRecurrence`.

# The descent recurrence for derangements

Let `D n = ∑_{π ∈ S_n, π fixed-point-free} X ^ des π ∈ ℝ[X]`, where `des π` counts the
adjacent positions `i` with `π i > π (i+1)`.  We prove, for every `n ≥ 2`,

  `D n = (1 + (n-1) X) D (n-1) + X (1 - X) D'(n-1) + (-1)^n X^(n-1)`.

Proof outline (all steps are proved below or in `RealRooted/Combinatorics/SortingFixedPoints.lean`,
`RealRooted/Combinatorics/ForcedSteps.lean`):

* A linear functional `T n N : ℝ[X] → ℝ`, `X^d ↦ C(N + n - 1 - d, n)`, separates polynomials
  (`eq_zero_of_T`), turns the Eulerian operator into multiplication by `N` (`T_L`), and maps
  `X^(n-1)` to `C(N, n)`.
* By stable sorting, words `u : Fin n → Fin N` correspond to pairs (permutation `π`,
  weakly increasing labelling strict at the descents of `π`); stars and bars gives
  `#{u | sort u = π} = C(N + n - 1 - des π, n)`, hence `T n N (D n) = Z n N`, the number of
  words whose sorting permutation is fixed-point-free (`T_D`).
* Inclusion–exclusion over the letters carried by fixed points, together with the bijection
  that deletes the first fixed position carrying a given letter, gives
  `Z n N = ∑_j (-1)^j C(N, j) N^(n-j)`, hence `Z (n+1) N = N Z n N + (-1)^(n+1) C(N, n+1)`.
-/

@[expose] public section

open Polynomial Finset

namespace RealRooted.EulerianCompendium.DerangementDescent

open RealRooted.FiniteWords

/-! ## Definitions -/

/-- Number of descents of a permutation of `Fin n`: adjacent positions `i` with
`π i > π (i+1)`. -/
def des {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (univ.filter (fun i : Fin n => ∃ h : i.val + 1 < n, π ⟨i.val + 1, h⟩ < π i)).card

/-- The descent enumerator of fixed-point-free permutations of `Fin n`. -/
noncomputable def D (n : ℕ) : ℝ[X] :=
  ∑ π : Equiv.Perm (Fin n), if (∀ i, π i ≠ i) then X ^ des π else 0

/-! ## Counting words with no fixed position -/

section Words


/-- Number of words of length `n` over `Fin N` whose sorting permutation is a derangement. -/
def Z (n N : ℕ) : ℕ := (univ.filter (fun u : Fin n → Fin N => ∀ x, ¬ IsFixed u x)).card

theorem Z_eq (n N : ℕ) :
    (Z n N : ℤ) = ∑ j ∈ range (N + 1),
      (N.choose j : ℤ) * (-1) ^ j * (if j ≤ n then (N : ℤ) ^ (n - j) else 0) := by
  have h1 : (Z n N : ℤ) = ∑ u : Fin n → Fin N, ∑ J ∈ (bad u).powerset, (-1 : ℤ) ^ J.card := by
    rw [Z, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_powerset_neg_one_pow_card]
    have : (∀ x, ¬ IsFixed u x) ↔ bad u = ∅ := by
      simp [bad, Finset.eq_empty_iff_forall_notMem]
    by_cases h : ∀ x, ¬ IsFixed u x
    · simp [h, this.1 h]
    · simp [h, mt this.2 h]
  have h2 : ∀ u : Fin n → Fin N, ∑ J ∈ (bad u).powerset, (-1 : ℤ) ^ J.card
      = ∑ J ∈ (univ : Finset (Fin N)).powerset, if J ⊆ bad u then (-1 : ℤ) ^ J.card else 0 := by
    intro u
    rw [← Finset.sum_filter]
    congr 1
    ext J; simp
  rw [h1]
  simp_rw [h2]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_filter, Finset.sum_const, card_bad_superset, nsmul_eq_mul]
  rw [Finset.sum_powerset_apply_card
    (fun j => ((if j ≤ n then N ^ (n - j) else 0 : ℕ) : ℤ) * (-1) ^ j)]
  simp only [card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> push_cast <;> ring

theorem Z_succ (n N : ℕ) :
    (Z (n + 1) N : ℤ) = N * Z n N + (-1) ^ (n + 1) * (N.choose (n + 1) : ℤ) := by
  rw [Z_eq, Z_eq, Finset.mul_sum]
  have : (-1 : ℤ) ^ (n + 1) * (N.choose (n + 1) : ℤ) = ∑ j ∈ range (N + 1),
      (N.choose j : ℤ) * (-1) ^ j * (if j = n + 1 then 1 else 0) := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with h
    · ring
    · rw [Nat.choose_eq_zero_of_lt (by lia)]; simp
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : j ≤ n
  · rw [ite_eq_left (by lia), ite_eq_left h1, ite_eq_right (by lia),
      show n + 1 - j = (n - j) + 1 by lia]
    ring
  · by_cases h2 : j = n + 1
    · subst h2; simp
    · rw [ite_eq_right (by lia), ite_eq_right h1, ite_eq_right h2]; ring

end Words

/-! ## Bridge between words and permutations -/

theorem key_sort_strictMono {n N : ℕ} (u : Fin n → Fin N) :
    StrictMono (fun i => key u (Tuple.sort u i)) := by
  obtain ⟨h1, h2⟩ := (Tuple.eq_sort_iff (σ := Tuple.sort u) (f := u)).1 rfl
  intro i j hij
  simp only [key]
  rcases (h1 hij.le).eq_or_lt with he | hl
  · exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨he, h2 i j hij he⟩)
  · exact Prod.Lex.toLex_lt_toLex.2 (Or.inl hl)

theorem rank_eq_sort_symm {n N : ℕ} (u : Fin n → Fin N) (x : Fin n) :
    rank u x = ((Tuple.sort u).symm x).val := by
  have hs := key_sort_strictMono u
  rw [rank]
  have : (univ.filter (fun w => key u w < key u x)) =
      (Iio ((Tuple.sort u).symm x)).map (Tuple.sort u).toEmbedding := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply, mem_Iio]
    constructor
    · intro h
      refine ⟨(Tuple.sort u).symm w, ?_, by simp⟩
      rw [← hs.lt_iff_lt]; simpa using h
    · rintro ⟨i, hi, rfl⟩
      have := hs hi
      simpa using this
  rw [this, card_map, Fin.card_Iio]

theorem sort_apply_eq_iff {n N : ℕ} (u : Fin n → Fin N) (x : Fin n) :
    Tuple.sort u x = x ↔ IsFixed u x := by
  rw [IsFixed, rank_eq_sort_symm, Fin.val_inj, Equiv.symm_apply_eq, eq_comm]

/-- The set of descent positions of `π`. -/
def descentSet {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  univ.filter (fun i : Fin n => ∃ h : i.val + 1 < n, π ⟨i.val + 1, h⟩ < π i)

theorem des_eq_card {n : ℕ} (π : Equiv.Perm (Fin n)) : des π = (descentSet π).card := rfl

theorem sort_eq_iff_compat {n N : ℕ} (u : Fin n → Fin N) (π : Equiv.Perm (Fin n)) :
    Tuple.sort u = π ↔ Monotone (u ∘ π) ∧
      ∀ i ∈ descentSet π, ∀ h : i.val + 1 < n, (u ∘ π) i < (u ∘ π) ⟨i.val + 1, h⟩ := by
  rw [eq_comm, Tuple.eq_sort_iff]
  set f := u ∘ π with hf
  constructor
  · rintro ⟨hm, ht⟩
    refine ⟨hm, fun i hi h => ?_⟩
    simp only [descentSet, mem_filter, mem_univ, true_and] at hi
    obtain ⟨h', hd⟩ := hi
    have hle : f i ≤ f ⟨i.val + 1, h⟩ := hm (Fin.mk_le_mk.2 (by simp))
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have := ht i ⟨i.val + 1, h⟩ (Fin.mk_lt_mk.2 (by simp)) heq
      exact lt_asymm this hd
  · rintro ⟨hm, hs⟩
    refine ⟨hm, ?_⟩
    have base : ∀ (i : Fin n) (h : i.val + 1 < n), f i = f ⟨i.val + 1, h⟩ →
        π i < π ⟨i.val + 1, h⟩ := by
      intro i h he
      have hnot : i ∉ descentSet π := fun hi => (hs i hi h).ne he
      simp only [descentSet, mem_filter, mem_univ, true_and, not_exists, not_lt] at hnot
      refine lt_of_le_of_ne (hnot h) ?_
      intro hc
      have := π.injective hc
      rw [Fin.ext_iff] at this
      simp at this
    have key : ∀ k (i : Fin n) (h : i.val + k + 1 < n), f i = f ⟨i.val + k + 1, h⟩ →
        π i < π ⟨i.val + k + 1, h⟩ := by
      intro k
      induction k with
      | zero => intro i h he; exact base i h he
      | succ k ih =>
        intro i h he
        have h1 : f i ≤ f ⟨i.val + k + 1, by lia⟩ :=
          hm (Fin.le_def.2 (show i.val ≤ i.val + k + 1 by lia))
        have h2 : f ⟨i.val + k + 1, by lia⟩ ≤ f ⟨i.val + (k + 1) + 1, h⟩ :=
          hm (Fin.mk_le_mk.2 (by lia))
        have e1 : f i = f ⟨i.val + k + 1, by lia⟩ := le_antisymm h1 (he ▸ h2)
        have e2 : f ⟨i.val + k + 1, by lia⟩ = f ⟨i.val + (k + 1) + 1, h⟩ := e1.symm.trans he
        have := ih i (by lia) e1
        have := base ⟨i.val + k + 1, by lia⟩ (by lia) e2
        exact lt_trans ‹π i < _› (by simpa [add_assoc] using this)
    intro i j hij he
    obtain ⟨k, hk⟩ : ∃ k, j.val = i.val + k + 1 := ⟨j.val - i.val - 1, by
      rw [Fin.lt_def] at hij; lia⟩
    have hj : j = ⟨i.val + k + 1, by lia⟩ := Fin.ext hk
    rw [hj] at he ⊢
    exact key k i _ he

theorem card_sort_eq {n N : ℕ} (π : Equiv.Perm (Fin n)) :
    (univ.filter (fun u : Fin n → Fin N => Tuple.sort u = π)).card
      = (N + n - 1 - des π).choose n := by
  rw [des_eq_card, ← card_compat N (descentSet π) (fun j hj => by
    simp only [descentSet, mem_filter] at hj; exact hj.2.1)]
  refine Finset.card_bij' (fun u _ => u ∘ π) (fun f _ => f ∘ π.symm) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu ⊢
    exact (sort_eq_iff_compat u π).1 hu
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf ⊢
    rw [sort_eq_iff_compat]
    have : (f ∘ π.symm) ∘ π = f := by funext x; simp
    rw [this]; exact hf
  · intro u _; funext x; simp
  · intro f _; funext x; simp

/-! ## The transform -/

/-- `T n N P = ∑_d P_d * C(N + n - 1 - d, n)`. -/
noncomputable def T (n N : ℕ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun d => ((N + n - 1 - d).choose n : ℝ) • LinearMap.id)

theorem T_monomial (n N d : ℕ) (c : ℝ) :
    T n N (monomial d c) = c * ((N + n - 1 - d).choose n : ℝ) := by
  simp [T, Polynomial.lsum_apply, mul_comm]

theorem T_apply (n N : ℕ) (P : ℝ[X]) :
    T n N P = ∑ d ∈ P.support, P.coeff d * ((N + n - 1 - d).choose n : ℝ) := by
  simp [T, Polynomial.lsum_apply, Polynomial.sum_def, mul_comm]

theorem eq_zero_of_T (n : ℕ) (hn : 1 ≤ n) (P : ℝ[X]) (h : ∀ N, T n N P = 0) : P = 0 := by
  ext d
  simp only [coeff_zero]
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have hd := h (d + 1)
    rw [T_apply] at hd
    by_cases hmem : d ∈ P.support
    · rw [Finset.sum_eq_single d] at hd
      · simpa [show d + 1 + n - 1 - d = n by lia] using hd
      · intro e he hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · simp [ih e hlt]
        · rw [Nat.choose_eq_zero_of_lt (by lia)]; simp
      · intro h'; exact absurd hmem h'
    · simpa using hmem

theorem T_D (n N : ℕ) : T n N (D n) = Z n N := by
  rw [D, map_sum]
  have h1 : ∀ π : Equiv.Perm (Fin n), T n N (if (∀ i, π i ≠ i) then X ^ des π else 0)
      = (((univ.filter (fun u : Fin n → Fin N => Tuple.sort u = π)).filter
          (fun _ => ∀ i, π i ≠ i)).card : ℝ) := by
    intro π
    split_ifs with h
    · rw [Finset.filter_true_of_mem (fun _ _ => h), card_sort_eq,
        ← monomial_one_right_eq_X_pow, T_monomial, one_mul]
    · rw [Finset.filter_false_of_mem (fun _ _ => h)]; simp
  simp_rw [h1]
  rw [← Nat.cast_sum, Z]
  congr 1
  rw [Finset.card_eq_sum_card_fiberwise (f := fun u : Fin n → Fin N => Tuple.sort u)
    (t := univ) (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  ext u
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hu, hπ⟩
    refine ⟨fun x hx => ?_, hu⟩
    rw [← sort_apply_eq_iff, hu] at hx
    exact hπ x hx
  · rintro ⟨hu, hπ⟩
    refine ⟨hπ, fun x hx => hu x ?_⟩
    rw [← sort_apply_eq_iff, hπ]; exact hx

lemma binom_aux (m N d : ℕ) :
    ((d : ℝ) + 1) * ((N + m + 1 - d).choose (m + 2) : ℝ)
      + ((m : ℝ) + 1 - d) * ((N + m - d).choose (m + 2) : ℝ)
      = N * ((N + m - d).choose (m + 1) : ℝ) := by
  by_cases h : d ≤ N + m
  · obtain ⟨k, hk⟩ : ∃ k, N + m - d = k := ⟨_, rfl⟩
    have hk1 : N + m + 1 - d = k + 1 := by lia
    rw [hk1, hk, Nat.choose_succ_succ']
    have key := Nat.choose_succ_right_eq k (m + 1)
    have hN : (N : ℝ) = k + d - m := by
      have : N + m = k + d := by lia
      have : ((N + m : ℕ) : ℝ) = ((k + d : ℕ) : ℝ) := by rw [this]
      push_cast at this; linarith
    rcases le_or_gt (m + 1) k with hk2 | hk2
    · have key' : (k.choose (m + 2) : ℝ) * (m + 2)
          = (k.choose (m + 1) : ℝ) * ((k : ℝ) - (m + 1)) := by
        have := congrArg (fun x : ℕ => (x : ℝ)) key
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this
        rw [Nat.cast_sub hk2] at this
        push_cast at this; linarith
      push_cast
      rw [hN]; nlinarith [key']
    · rw [Nat.choose_eq_zero_of_lt hk2, Nat.choose_eq_zero_of_lt (by lia)]
      simp
  · rw [show N + m + 1 - d = 0 by lia, show N + m - d = 0 by lia]
    simp

theorem T_L (n N : ℕ) (hn : 2 ≤ n) (Q : ℝ[X]) :
    T n N ((1 + ((n : ℝ[X]) - 1) * X) * Q + X * (1 - X) * derivative Q)
      = N * T (n - 1) N Q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by lia⟩
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [mul_add, map_add] at *
    rw [← hp, ← hq]; ring
  | monomial d c =>
    have hpoly : (1 + (((m + 2 : ℕ) : ℝ[X]) - 1) * X) * monomial d c
        + X * (1 - X) * derivative (monomial d c)
        = monomial d (c * ((d : ℝ) + 1)) + monomial (d + 1) (c * ((m : ℝ) + 1 - d)) := by
      rw [derivative_monomial]
      rcases d with _ | d
      · simp only [CharP.cast_eq_zero, mul_zero, monomial_zero_right, mul_zero, add_zero]
        simp only [← C_mul_X_pow_eq_monomial, map_add, map_mul, map_sub, map_natCast, map_one,
          map_zero]
        push_cast; ring
      · simp only [← C_mul_X_pow_eq_monomial, Nat.add_sub_cancel, map_add, map_mul, map_sub,
          map_natCast, map_one]
        push_cast; ring
    rw [hpoly, map_add, T_monomial, T_monomial, T_monomial]
    have := binom_aux m N d
    rw [show N + (m + 2) - 1 - d = N + m + 1 - d by lia,
      show N + (m + 2) - 1 - (d + 1) = N + m - d by lia,
      show N + (m + 2 - 1) - 1 - d = N + m - d by lia, show m + 2 - 1 = m + 1 by lia]
    linear_combination c * this

theorem T_X_pow (n N : ℕ) (hn : 1 ≤ n) : T n N (X ^ (n - 1)) = (N.choose n : ℝ) := by
  rw [← monomial_one_right_eq_X_pow, T_monomial, one_mul]
  congr 2; lia

/-! ## Main theorem -/

/-- **Descent recurrence for derangements.** For every `n ≥ 2`,
`D n = (1 + (n-1) X) D (n-1) + X (1 - X) D'(n-1) + (-1)^n X^(n-1)`. -/
theorem D_recurrence (n : ℕ) (hn : 2 ≤ n) :
    D n = (1 + ((n : ℝ[X]) - 1) * X) * D (n - 1) + X * (1 - X) * derivative (D (n - 1))
      + (-1) ^ n * X ^ (n - 1) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_T n (by lia)
  intro N
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  simp only [map_sub, map_add, T_L (m + 1) N hn, Nat.add_sub_cancel, T_D]
  have h1 : T (m + 1) N ((-1) ^ (m + 1) * X ^ m) = (-1) ^ (m + 1) * (N.choose (m + 1) : ℝ) := by
    rw [show ((-1 : ℝ[X]) ^ (m + 1) * X ^ m) = C ((-1 : ℝ) ^ (m + 1)) * X ^ m by simp,
      ← smul_eq_C_mul, map_smul, smul_eq_mul]
    have := T_X_pow (m + 1) N (by lia)
    simp only [Nat.add_sub_cancel] at this
    rw [this]
  rw [h1]
  have := Z_succ m N
  have h2 : (Z (m + 1) N : ℝ) = N * Z m N + (-1) ^ (m + 1) * (N.choose (m + 1) : ℝ) := by
    exact_mod_cast this
  rw [h2]; ring

end RealRooted.EulerianCompendium.DerangementDescent
