module

public import RealRooted.Applications.EulerianCompendium.Definitions
public import Mathlib

/-!
# Balanced cyclic binary words counted by cyclic descents

Ported from Aristotle project `2d44e73d-0a24-4f58-b9f6-666426deff24`,
run `20a7431a-8c52-42d6-bf1e-ff58c2574143`.

A word of length `2n` is a function `w : Fin (2*n) → Bool`.  It is *balanced* if exactly `n`
positions carry `true`.  A *cyclic descent* is an index `i` with `w i = true` and
`w ((i+1) mod 2n) = false`.  We prove, for `n ≥ 1`,

  `∑_{w balanced} X^{cdes w} = 2 * ∑_{k ∈ Icc 1 n} C (choose n k * choose (n-1) (k-1)) * X^k`.

The proof transfers words to lists, counts linear descents (`10` factors) via a recursive
enumeration of lists with prescribed numbers of `true`s and `false`s (giving the coefficient
`choose a j * choose b j`), and then corrects for the wrap-around position.
-/

@[expose] public section

open Polynomial Finset

namespace RealRooted.EulerianCompendium.BalancedCyclic

/-! ## The objects of the statement -/

/-- Cyclic successor `i ↦ (i + 1) mod m` on `Fin m`. -/
def succMod {m : ℕ} (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- A word `w : Fin (2*n) → Bool` is balanced if exactly `n` of its letters are `true`. -/
def IsBalanced (n : ℕ) (w : Fin (2 * n) → Bool) : Prop :=
  (univ.filter (fun i => w i = true)).card = n

instance (n : ℕ) (w : Fin (2 * n) → Bool) : Decidable (IsBalanced n w) := by
  unfold IsBalanced; infer_instance

/-- Number of cyclic descents: indices `i` with `w i = true` and `w ((i+1) mod m) = false`. -/
def cdes {m : ℕ} (w : Fin m → Bool) : ℕ :=
  (univ.filter (fun i => w i = true ∧ w (succMod i) = false)).card

/-- The word sum `∑_{w balanced} X ^ cdes w` over real polynomials. -/
noncomputable def balancedWordSum (n : ℕ) : ℝ[X] :=
  ∑ w ∈ univ.filter (fun w : Fin (2 * n) → Bool => IsBalanced n w), X ^ cdes w

/-! ## Linear descents of lists -/

/-- Number of adjacent factors `true, false` in a list. -/
def ldes : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a = true ∧ b = false then 1 else 0) + ldes (b :: t)

lemma ldes_false_cons (l : List Bool) : ldes (false :: l) = ldes l := by
  cases l <;> simp [ldes]

lemma ldes_true_true (l : List Bool) : ldes (true :: true :: l) = ldes (true :: l) := by
  simp [ldes]

lemma ldes_true_false (l : List Bool) : ldes (true :: false :: l) = ldes l + 1 := by
  simp [ldes, ldes_false_cons]; lia

lemma ldes_cons (a : Bool) (l : List Bool) :
    ldes (a :: l) = (if a = true ∧ l.head? = some false then 1 else 0) + ldes l := by
  cases l <;> simp [ldes]

lemma ldes_append_true (l : List Bool) : ldes (l ++ [true]) = ldes l := by
  induction l with
  | nil => simp [ldes]
  | cons a t ih =>
    cases t with
    | nil => simp [ldes]
    | cons b s =>
      rw [List.cons_append, ldes_cons, ih, ldes_cons a (b :: s)]
      simp

lemma ldes_replicate_true (a : ℕ) : ldes (List.replicate a true) = 0 := by
  induction a with
  | zero => simp [ldes]
  | succ a ih =>
    rw [List.replicate_succ, ldes_cons, ih]
    cases a <;> simp [List.replicate_succ]

lemma ldes_replicate_false (b : ℕ) : ldes (List.replicate b false) = 0 := by
  induction b with
  | zero => simp [ldes]
  | succ b ih => rw [List.replicate_succ, ldes_false_cons, ih]

/-! ## Enumeration of lists with `a` trues and `b` falses -/

/-- Prepending a letter, as an embedding. -/
def consEmb (x : Bool) : List Bool ↪ List Bool := ⟨List.cons x, List.cons_injective⟩

/-- All lists with exactly `a` letters `true` and `b` letters `false`. -/
def words : ℕ → ℕ → Finset (List Bool)
  | 0, 0 => {[]}
  | a + 1, 0 => (words a 0).map (consEmb true)
  | 0, b + 1 => (words 0 b).map (consEmb false)
  | a + 1, b + 1 => (words a (b + 1)).map (consEmb true) ∪ (words (a + 1) b).map (consEmb false)

lemma mem_words (l : List Bool) (a b : ℕ) :
    l ∈ words a b ↔ l.count true = a ∧ l.count false = b := by
  induction l generalizing a b with
  | nil => cases a <;> cases b <;> simp [words, consEmb]
  | cons x t ih =>
    cases a <;> cases b <;> cases x <;> simp [words, consEmb, ih]

lemma words_zero_right (a : ℕ) : words a 0 = {List.replicate a true} := by
  induction a with
  | zero => simp [words]
  | succ a ih => simp [words, ih, consEmb, List.replicate_succ]

lemma words_zero_left (b : ℕ) : words 0 b = {List.replicate b false} := by
  induction b with
  | zero => simp [words]
  | succ b ih => simp [words, ih, consEmb, List.replicate_succ]

lemma sum_words_succ_succ {M : Type*} [AddCommMonoid M] (f : List Bool → M) (a b : ℕ) :
    ∑ l ∈ words (a + 1) (b + 1), f l =
      ∑ l ∈ words a (b + 1), f (true :: l) + ∑ l ∈ words (a + 1) b, f (false :: l) := by
  rw [words, Finset.sum_union]
  · simp [consEmb]
  · rw [Finset.disjoint_left]
    simp [consEmb]

lemma sum_words_zero_succ {M : Type*} [AddCommMonoid M] (f : List Bool → M) (b : ℕ) :
    ∑ l ∈ words 0 (b + 1), f l = ∑ l ∈ words 0 b, f (false :: l) := by
  rw [words]; simp [consEmb]

/-! ## Linear descent polynomial -/

/-- `P a b = ∑ X ^ ldes l` over lists with `a` trues and `b` falses. -/
noncomputable def P (a b : ℕ) : ℝ[X] := ∑ l ∈ words a b, X ^ ldes l

lemma P_zero_right (a : ℕ) : P a 0 = 1 := by
  simp [P, words_zero_right, ldes_replicate_true]

lemma P_zero_left (b : ℕ) : P 0 b = 1 := by
  simp [P, words_zero_left, ldes_replicate_false]

lemma sum_true_cons (a b : ℕ) :
    ∑ l ∈ words a (b + 1), (X : ℝ[X]) ^ ldes (true :: l) = P a (b + 1) + (X - 1) * P a b := by
  cases a with
  | zero =>
    rw [sum_words_zero_succ, P_zero_left, P_zero_left]
    simp only [ldes_true_false, pow_succ, ← Finset.sum_mul]
    rw [show ∑ l ∈ words 0 b, (X : ℝ[X]) ^ ldes l = P 0 b from rfl, P_zero_left]
    ring
  | succ a =>
    rw [sum_words_succ_succ]
    have h1 : P (a + 1) (b + 1) = ∑ l ∈ words a (b + 1), (X : ℝ[X]) ^ ldes (true :: l) +
        P (a + 1) b := by
      rw [P, sum_words_succ_succ]
      simp [ldes_false_cons, P]
    simp only [ldes_true_true, ldes_true_false, pow_succ, ← Finset.sum_mul]
    rw [h1]
    simp only [P]
    ring

lemma P_succ_succ (a b : ℕ) :
    P (a + 1) (b + 1) = P a (b + 1) + (X - 1) * P a b + P (a + 1) b := by
  conv_lhs => rw [P, sum_words_succ_succ]
  rw [sum_true_cons]
  simp [ldes_false_cons, P]

lemma coeff_P (a b j : ℕ) : (P a b).coeff j = (a.choose j : ℝ) * (b.choose j : ℝ) := by
  induction a generalizing b j with
  | zero =>
    rw [P_zero_left, coeff_one]
    cases j <;> simp
  | succ a iha =>
    induction b generalizing j with
    | zero =>
      rw [P_zero_right, coeff_one]
      cases j <;> simp
    | succ b ihb =>
      rw [P_succ_succ, coeff_add, coeff_add, sub_mul, coeff_sub, one_mul, iha, ihb]
      cases j with
      | zero => simp [iha]
      | succ j =>
        rw [coeff_X_mul, iha, iha]
        simp only [Nat.choose_succ_succ, Nat.cast_add]
        ring

/-! ## Cyclic correction on lists -/

/-- The wrap-around condition for a list: it starts with `false` and ends with `true`. -/
def wrap (l : List Bool) : Prop := l.head? = some false ∧ l.getLast? = some true

instance (l : List Bool) : Decidable (wrap l) := by unfold wrap; infer_instance

lemma filter_wrap_words (n : ℕ) :
    (words (n + 1) (n + 1)).filter wrap =
      (words n n).map ⟨fun m => false :: (m ++ [true]), by
        intro x y h; simpa using h⟩ := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_map, mem_words, wrap]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    obtain ⟨t, rfl⟩ : ∃ t, l = false :: t := by
      cases l with
      | nil => simp at h3
      | cons x t =>
          simp only [List.head?_cons, Option.some.injEq] at h3
          exact ⟨t, by rw [h3]⟩
    have ht : t.getLast? = some true := by
      cases t with
      | nil => simp at h4
      | cons y s => simpa [List.getLast?_cons] using h4
    obtain ⟨m, rfl⟩ := List.getLast?_eq_some_iff.mp ht
    refine ⟨m, ⟨?_, ?_⟩, rfl⟩
    · simp [List.count_append] at h1; lia
    · simp [List.count_append] at h2; lia
  · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · change List.count true (false :: (m ++ [true])) = n + 1
      simp [List.count_append, h1]
    · change List.count false (false :: (m ++ [true])) = n + 1
      simp [List.count_append, h2]
    · change (false :: (m ++ [true])).head? = some false
      simp
    · change (false :: (m ++ [true])).getLast? = some true
      exact List.getLast?_eq_some_iff.mpr ⟨false :: m, by simp⟩

/-- The cyclic descent polynomial on balanced lists. -/
lemma sum_cyclic_lists (n : ℕ) :
    ∑ l ∈ words (n + 1) (n + 1), (X : ℝ[X]) ^ (ldes l + if wrap l then 1 else 0) =
      P (n + 1) (n + 1) + (X - 1) * P n n := by
  rw [← Finset.sum_filter_add_sum_filter_not _ wrap]
  have hw : ∑ l ∈ (words (n + 1) (n + 1)).filter wrap, (X : ℝ[X]) ^ ldes l = P n n := by
    rw [filter_wrap_words, Finset.sum_map]
    change ∑ l ∈ words n n, (X : ℝ[X]) ^ ldes (false :: (l ++ [true])) = P n n
    simp [ldes_false_cons, ldes_append_true, P]
  have hP : P (n + 1) (n + 1) = ∑ l ∈ (words (n + 1) (n + 1)).filter wrap, (X : ℝ[X]) ^ ldes l
      + ∑ l ∈ (words (n + 1) (n + 1)).filter (fun l => ¬ wrap l), (X : ℝ[X]) ^ ldes l := by
    rw [P, Finset.sum_filter_add_sum_filter_not]
  rw [hP, hw]
  have e1 : ∑ l ∈ (words (n + 1) (n + 1)).filter wrap,
      (X : ℝ[X]) ^ (ldes l + if wrap l then 1 else 0) = X * P n n := by
    rw [← hw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [ite_eq_left (Finset.mem_filter.mp hl).2, pow_succ, mul_comm]
  have e2 : ∑ l ∈ (words (n + 1) (n + 1)).filter (fun l => ¬ wrap l),
      (X : ℝ[X]) ^ (ldes l + if wrap l then 1 else 0) =
      ∑ l ∈ (words (n + 1) (n + 1)).filter (fun l => ¬ wrap l), (X : ℝ[X]) ^ ldes l := by
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [ite_eq_right (Finset.mem_filter.mp hl).2, add_zero]
  rw [e1, e2]
  ring

/-! ## From words `Fin m → Bool` to lists -/

lemma ldes_ofFn {m : ℕ} (w : Fin (m + 1) → Bool) :
    ldes (List.ofFn w) =
      ∑ i : Fin m, if w i.castSucc = true ∧ w i.succ = false then 1 else 0 := by
  induction m with
  | zero => simp [ldes]
  | succ m ih =>
    rw [List.ofFn_succ, ldes_cons, ih (fun i => w i.succ), Fin.sum_univ_succ]
    have hh : (List.ofFn fun i : Fin (m + 1) => w i.succ).head? = some (w 1) := by
      simp [List.head?_eq_getElem?]
    rw [hh]
    simp only [Fin.succ_castSucc, Fin.castSucc_zero, Option.some.injEq]
    rfl

lemma ofFn_getD (l : List Bool) {m : ℕ} (h : l.length = m) :
    List.ofFn (fun i : Fin m => l.getD i false) = l := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getD_eq_getElem _ _ h2]

lemma cdes_eq_succ {m : ℕ} (w : Fin (m + 1) → Bool) :
    cdes w = ldes (List.ofFn w) + if wrap (List.ofFn w) then 1 else 0 := by
  rw [cdes, Finset.card_filter, Fin.sum_univ_castSucc, ldes_ofFn]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have : succMod i.castSucc = i.succ := by
      ext; simp [succMod, Nat.mod_eq_of_lt (Nat.succ_lt_succ i.isLt)]
    rw [this]
  · have : succMod (Fin.last m) = 0 := by
      ext; simp [succMod]
    rw [this]
    have h1 : (List.ofFn w).head? = some (w 0) := by simp [List.head?_eq_getElem?]
    have h2 : (List.ofFn w).getLast? = some (w (Fin.last m)) := by
      rw [List.getLast?_eq_getElem?, List.getElem?_ofFn]; simp [Fin.last]
    simp only [wrap, h1, h2, Option.some.injEq, and_comm]

lemma cdes_eq {m : ℕ} (hm : 0 < m) (w : Fin m → Bool) :
    cdes w = ldes (List.ofFn w) + if wrap (List.ofFn w) then 1 else 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
  exact cdes_eq_succ w

lemma count_true_ofFn {m : ℕ} (w : Fin m → Bool) :
    (List.ofFn w).count true = (univ.filter (fun i => w i = true)).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.count_cons, ih, Finset.card_filter, Finset.card_filter,
      Fin.sum_univ_succ]
    simp [add_comm]

/-- The word sum equals the sum over lists in `words n n`. -/
lemma balancedWordSum_eq_lists (n : ℕ) :
    balancedWordSum (n + 1) =
      ∑ l ∈ words (n + 1) (n + 1), (X : ℝ[X]) ^ (ldes l + if wrap l then 1 else 0) := by
  rw [balancedWordSum]
  refine Finset.sum_nbij' (fun w => List.ofFn w) (fun l i => l.getD i false) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    unfold IsBalanced at hw
    simp only [mem_words]
    have hc := List.count_true_add_count_false (List.ofFn w)
    rw [List.length_ofFn, count_true_ofFn, hw] at hc
    refine ⟨by rw [count_true_ofFn, hw], by lia⟩
  · intro l hl
    simp only [mem_words] at hl
    have hlen : l.length = 2 * (n + 1) := by
      have := List.count_true_add_count_false l; lia
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (Finset.univ.filter (fun i : Fin (2 * (n + 1)) => l.getD i false = true)).card =
      n + 1
    rw [← count_true_ofFn, ofFn_getD l hlen, hl.1]
  · intro w _
    funext i
    show (List.ofFn w).getD i false = w i
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp
  · intro l hl
    simp only [mem_words] at hl
    have hlen : l.length = 2 * (n + 1) := by
      have := List.count_true_add_count_false l; lia
    exact ofFn_getD l hlen
  · intro w _
    rw [cdes_eq (by lia)]

/-! ## Main theorem -/

/-- **Balanced cyclic word enumeration.** For `n ≥ 1`,
`∑_{w balanced} X ^ cdes w = 2 * ∑_{k=1}^{n} C(n,k) C(n-1,k-1) X^k`. -/
theorem balancedWordSum_formula (n : ℕ) (hn : 1 ≤ n) :
    balancedWordSum n =
      2 * ∑ k ∈ Finset.Icc 1 n,
        C ((Nat.choose n k : ℝ) * (Nat.choose (n - 1) (k - 1) : ℝ)) * X ^ k := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  rw [balancedWordSum_eq_lists, sum_cyclic_lists]
  ext j
  rw [coeff_add, sub_mul, coeff_sub, one_mul, coeff_P, coeff_P]
  have h2 : (2 : ℝ[X]) = C 2 := rfl
  rw [h2, coeff_C_mul, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  cases j with
  | zero => simp
  | succ j =>
    rw [coeff_X_mul, coeff_P]
    simp only [Finset.mem_Icc, Nat.add_sub_cancel]
    split_ifs with h
    · simp only [Nat.choose_succ_succ, Nat.cast_add]; ring
    · have h3 : n + 1 < j + 1 := by lia
      rw [Nat.choose_eq_zero_of_lt h3, Nat.choose_eq_zero_of_lt (by lia : n < j + 1),
        Nat.choose_eq_zero_of_lt (by lia : n < j)]
      simp

end RealRooted.EulerianCompendium.BalancedCyclic

namespace RealRooted.EulerianCompendium

open RealRooted.Applications.EulerianVariations

/-- The coefficient model in `Definitions` counts actual balanced cyclic binary words
for every paper rank `n ≥ 1` (`thm:cyclicDescents`). -/
theorem balancedWordSum_eq_cyclicPathDescentPolynomial (n : ℕ) (hn : 1 ≤ n) :
    BalancedCyclic.balancedWordSum n = cyclicPathDescentPolynomial n := by
  rw [BalancedCyclic.balancedWordSum_formula n hn]
  ext k
  change (C (2 : ℝ) *
      ∑ i ∈ Finset.Icc 1 n,
        C ((Nat.choose n i : ℝ) * (Nat.choose (n - 1) (i - 1) : ℝ)) * X ^ i).coeff k =
      (cyclicPathDescentPolynomial n).coeff k
  rw [coeff_C_mul, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq,
    RealRooted.Applications.EulerianVariations.coeff_cyclicPathDescentPolynomial]
  split_ifs <;> ring

/-- The actual balanced-word enumerator is a Pólya-frequency polynomial. -/
theorem balancedWordSum_isPF (n : ℕ) (hn : 1 ≤ n) :
    RealRooted.IsPFPolynomial (BalancedCyclic.balancedWordSum n) := by
  rw [balancedWordSum_eq_cyclicPathDescentPolynomial n hn]
  exact RealRooted.Applications.EulerianVariations.cyclicPathDescentPolynomial_isPF n hn

/-- The actual balanced-word sum has a simple root at zero and exactly `n - 1`
simple negative roots (`thm:cyclicDescents`). -/
theorem balancedWordSum_simple_root_description (n : ℕ) (hn : 1 ≤ n) :
    RealRooted.HasSimpleRoots (BalancedCyclic.balancedWordSum n) ∧
      (BalancedCyclic.balancedWordSum n).IsRoot 0 ∧
      (∀ r ∈ (BalancedCyclic.balancedWordSum n).roots.erase 0, r < 0) ∧
      ((BalancedCyclic.balancedWordSum n).roots.erase 0).card = n - 1 := by
  rw [balancedWordSum_eq_cyclicPathDescentPolynomial n hn]
  exact cyclicPathDescentPolynomial_roots n hn

end RealRooted.EulerianCompendium
