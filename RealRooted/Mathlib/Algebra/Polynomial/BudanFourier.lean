import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

/-!
# The Budan–Fourier theorem

For a nonzero real polynomial `p` and a real number `x`, let `V(x)` be the number of sign
changes (zeros removed) in the sequence `p(x), p'(x), …, p^{(n)}(x)`, where `n = p.natDegree`.
The Budan–Fourier theorem states that for `a < b` the number of roots of `p` in `(a, b]`,
counted with multiplicity, is at most `V(a) - V(b)`, and that the difference is even.

## Main definitions

* `List.firstNonzero`: the first nonzero entry of a list of reals (or `0`).
* `List.signVariations_cons_eq`: a recursive description of Mathlib's `List.signVariations`.
* `Polynomial.derivEvalList p x n`: the list `[p(x), p'(x), …, p^{(n)}(x)]`.
* `Polynomial.budanFourierVar p x`: the Budan–Fourier count `V(x)`.
* `Polynomial.rootsIoc p a b`: the number of roots of `p` in `(a, b]` with multiplicity.

## Main results

* `Polynomial.exists_budanFourierVar_eq`: `V(a) = V(b) + #roots + 2 * k` for some `k`.
* `Polynomial.rootsIoc_le_budanFourierVar_sub` and
  `Polynomial.even_budanFourierVar_sub_sub_rootsIoc`: the two halves of the theorem.
* `Polynomial.budan_fourier`: the theorem stated with explicit iterated derivatives.

## Proof outline

We argue by induction on the degree. Writing `q = p'`, we have
`V_p(x) = V_q(x) + e(x)`, where `e(x) ∈ {0, 1}` records a sign change between `p(x)` and
the first nonzero entry of `q(x), q'(x), …`. The key Rolle-type lemma
`Polynomial.exists_rootsIoc_derivative_add_crossTerm` states that
`#roots_q(a, b] + e(a) = e(b) + #roots_p(a, b] + 2 * j`. Both sides are additive under
subdivision of `(a, b]`, so we subdivide at the roots of `p * q` and analyse an interval
on whose interior neither `p` nor `q` vanishes, using the intermediate value theorem, the
mean value theorem and the factorisation `q = (X - c) ^ μ * g` at the endpoints.
-/

open Polynomial Set

noncomputable section

namespace List

/-- The first nonzero entry of a list of reals, or `0` if all entries vanish. -/
def firstNonzero : List ℝ → ℝ
  | [] => 0
  | x :: l => if x = 0 then firstNonzero l else x

private lemma ite_sign_eq_ite_mul_neg {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (if SignType.sign x = SignType.sign y then 0 else 1) = if x * y < 0 then 1 else 0 := by
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hy with hy | hy
  · simp [sign_neg hx, sign_neg hy, (mul_pos_of_neg_of_neg hx hy).le]
  · simp [sign_neg hx, sign_pos hy, mul_neg_of_neg_of_pos hx hy]
  · simp [sign_pos hx, sign_neg hy, mul_neg_of_pos_of_neg hx hy]
  · simp [sign_pos hx, sign_pos hy, (mul_pos hx hy).le]

/-- Recursive description of `List.signVariations` for lists of reals: prepending `x` adds a
sign change exactly when `x` and the first nonzero entry of `l` have opposite signs. -/
lemma signVariations_cons_eq (x : ℝ) (l : List ℝ) :
    signVariations (x :: l) = signVariations l + if x * firstNonzero l < 0 then 1 else 0 := by
  by_cases hx : x = 0
  · rw [hx, signVariations_zero_cons, zero_mul, ite_eq_right (lt_irrefl 0), add_zero]
  induction l with
  | nil => simp [firstNonzero]
  | cons y l ih =>
    by_cases hy : y = 0
    · rw [hy, signVariations_cons_zero_cons, ih, signVariations_zero_cons, firstNonzero,
        ite_eq_left rfl]
    · rw [signVariations_cons_cons_of_ne_zero l hx hy, firstNonzero, ite_eq_right hy,
        ite_sign_eq_ite_mul_neg hx hy]

/-- The number of sign changes in a list of reals, after removing the zero entries; a
recursive helper equal to `List.signVariations`. -/
private def signChanges : List ℝ → ℕ
  | [] => 0
  | x :: l => signChanges l + if x * firstNonzero l < 0 then 1 else 0

private theorem signChanges_eq_signVariations (l : List ℝ) :
    l.signChanges = l.signVariations := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [signChanges, ih, signVariations_cons_eq]

end List

namespace Polynomial

/-- `derivEvalList p x n` is the list `[p(x), p'(x), …, p^{(n)}(x)]`. -/
def derivEvalList (p : ℝ[X]) (x : ℝ) : ℕ → List ℝ
  | 0 => [p.eval x]
  | n + 1 => p.eval x :: derivEvalList (derivative p) x n

lemma derivEvalList_eq_map (p : ℝ[X]) (x : ℝ) (n : ℕ) :
    derivEvalList p x n = (List.range (n + 1)).map fun i => (derivative^[i] p).eval x := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, derivEvalList, ih]
    rfl

/-- The Budan–Fourier count `V(x)`: the number of sign changes in
`p(x), p'(x), …, p^{(n)}(x)` with `n = p.natDegree`, zeros removed. -/
def budanFourierVar (p : ℝ[X]) (x : ℝ) : ℕ :=
  (derivEvalList p x p.natDegree).signVariations

lemma budanFourierVar_eq (p : ℝ[X]) (x : ℝ) :
    budanFourierVar p x = List.signVariations
      ((List.range (p.natDegree + 1)).map fun i => (derivative^[i] p).eval x) := by
  rw [budanFourierVar, derivEvalList_eq_map]

/-- The number of roots of `p` in `(a, b]`, counted with multiplicity. -/
def rootsIoc (p : ℝ[X]) (a b : ℝ) : ℕ :=
  (p.roots.filter fun r => a < r ∧ r ≤ b).card

/-- The indicator of a sign change between `p(x)` and the first nonzero value among
`p'(x), p''(x), …`. -/
def crossTerm (p : ℝ[X]) (x : ℝ) : ℕ :=
  if p.eval x * (derivEvalList (derivative p) x (derivative p).natDegree).firstNonzero < 0
  then 1 else 0

lemma budanFourierVar_eq_add_crossTerm {p : ℝ[X]} (hp : p.natDegree ≠ 0) (x : ℝ) :
    budanFourierVar p x = budanFourierVar (derivative p) x + crossTerm p x := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hp
  have hd : (derivative p).natDegree = n := by rw [natDegree_derivative, hn]; rfl
  rw [budanFourierVar, budanFourierVar, crossTerm, hn, derivEvalList,
    List.signVariations_cons_eq, hd]

/-! ### Lists of iterated derivatives -/

lemma firstNonzero_derivEvalList {c : ℝ} {k : ℕ} :
    ∀ {n : ℕ} {q : ℝ[X]}, k ≤ n → (∀ i < k, (derivative^[i] q).eval c = 0) →
      (derivative^[k] q).eval c ≠ 0 →
      (derivEvalList q c n).firstNonzero = (derivative^[k] q).eval c := by
  induction k with
  | zero =>
    intro n q _ _ hk
    replace hk : q.eval c ≠ 0 := hk
    cases n with
    | zero => simp [derivEvalList, List.firstNonzero, hk]
    | succ n => simp [derivEvalList, List.firstNonzero, hk]
  | succ k ih =>
    intro n q hkn h0 hk
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le k.lt_succ_self hkn)
    have hq0 : q.eval c = 0 := h0 0 k.succ_pos
    have key := ih (n := k + n) (q := derivative q) (by lia)
      (fun i hi => h0 (i + 1) (by lia)) hk
    simp only [derivEvalList, List.firstNonzero, hq0, ↓reduceIte]
    exact key

lemma rootMultiplicity_le_natDegree' (q : ℝ[X]) (c : ℝ) : q.rootMultiplicity c ≤ q.natDegree :=
  (count_roots (a := c) q).symm.le.trans ((Multiset.count_le_card _ _).trans (card_roots' q))

lemma firstNonzero_derivEvalList_eq {q : ℝ[X]} (hq : q ≠ 0) (c : ℝ) :
    (derivEvalList q c q.natDegree).firstNonzero =
      (q.rootMultiplicity c).factorial * (q /ₘ (X - C c) ^ q.rootMultiplicity c).eval c := by
  have hval := eval_iterate_derivative_rootMultiplicity (p := q) (t := c)
  rw [nsmul_eq_mul] at hval
  rw [← hval]
  refine firstNonzero_derivEvalList (rootMultiplicity_le_natDegree' q c)
    (fun i hi => isRoot_iterate_derivative_of_lt_rootMultiplicity hi) ?_
  rw [hval]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (eval_divByMonic_pow_rootMultiplicity_ne_zero c hq)

/-! ### Sign lemmas -/

/-- A real polynomial without zeros on `[u, v]` has the same sign at `u` and `v`. -/
lemma eval_mul_eval_pos_of_forall_ne_zero {f : ℝ[X]} {u v : ℝ} (huv : u ≤ v)
    (hf : ∀ z ∈ Icc u v, f.eval z ≠ 0) : 0 < f.eval u * f.eval v := by
  by_contra h
  rw [not_lt] at h
  have hc : ContinuousOn (fun z => f.eval z) (Icc u v) := f.continuous.continuousOn
  rcases lt_or_gt_of_ne (hf u ⟨le_rfl, huv⟩) with hu | hu
  · obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc huv hc ⟨hu.le, by nlinarith⟩
    exact hf z hz hz0
  · obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' huv hc ⟨by nlinarith, hu.le⟩
    exact hf z hz hz0

/-- Just to the right of a root of `p`, the values of `p` and `p'` have the same sign. -/
lemma eval_mul_eval_derivative_pos {p : ℝ[X]} {a y : ℝ} (hay : a < y) (hpa : p.eval a = 0)
    (hq : ∀ z ∈ Ioc a y, (derivative p).eval z ≠ 0) :
    0 < p.eval y * (derivative p).eval y := by
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun x => p.eval x)
    (fun x => (derivative p).eval x) hay p.continuous.continuousOn (fun x _ => p.hasDerivAt x)
  have hpos := eval_mul_eval_pos_of_forall_ne_zero hξ.2.le
    (fun z hz => hq z ⟨hξ.1.trans_le hz.1, hz.2⟩)
  have hy : p.eval y = (derivative p).eval ξ * (y - a) := by
    rw [hξeq, hpa, sub_zero, div_mul_cancel₀ _ (sub_ne_zero.mpr hay.ne')]
  rw [hy, mul_right_comm]
  exact mul_pos hpos (sub_pos.mpr hay)

/-- Just to the left of a root of `p`, the values of `p` and `p'` have opposite signs. -/
lemma eval_mul_eval_derivative_neg {p : ℝ[X]} {y b : ℝ} (hyb : y < b) (hpb : p.eval b = 0)
    (hq : ∀ z ∈ Ico y b, (derivative p).eval z ≠ 0) :
    p.eval y * (derivative p).eval y < 0 := by
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun x => p.eval x)
    (fun x => (derivative p).eval x) hyb p.continuous.continuousOn (fun x _ => p.hasDerivAt x)
  have hpos := eval_mul_eval_pos_of_forall_ne_zero hξ.1.le
    (fun z hz => hq z ⟨hz.1, hz.2.trans_lt hξ.2⟩)
  have hy : p.eval y = -((derivative p).eval ξ * (b - y)) := by
    rw [hξeq, hpb, div_mul_cancel₀ _ (sub_ne_zero.mpr hyb.ne')]
    ring
  rw [hy]
  nlinarith [mul_pos hpos (sub_pos.mpr hyb)]

/-- To the right of `c`, the sign of `q` is the sign of the first nonzero value among
`q(c), q'(c), …`. -/
lemma firstNonzero_mul_eval_pos_right {q : ℝ[X]} (hq : q ≠ 0) {c y : ℝ} (hcy : c < y)
    (hz : ∀ z ∈ Ioc c y, q.eval z ≠ 0) :
    0 < (derivEvalList q c q.natDegree).firstNonzero * q.eval y := by
  have hfac := pow_mul_divByMonic_rootMultiplicity_eq q c
  have hgc := eval_divByMonic_pow_rootMultiplicity_ne_zero c hq
  rw [firstNonzero_derivEvalList_eq hq]
  generalize q /ₘ (X - C c) ^ q.rootMultiplicity c = g at hfac hgc ⊢
  generalize q.rootMultiplicity c = μ at hfac hgc ⊢
  subst hfac
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hz ⊢
  have hg : ∀ z ∈ Icc c y, g.eval z ≠ 0 := by
    intro z hzc hgz
    rcases hzc.1.eq_or_lt with h | h
    · exact hgc (h ▸ hgz)
    · exact hz z ⟨h, hzc.2⟩ (by rw [hgz, mul_zero])
  have hpos := eval_mul_eval_pos_of_forall_ne_zero hcy.le hg
  have key : (μ.factorial : ℝ) * g.eval c * ((y - c) ^ μ * g.eval y) =
      ((μ.factorial : ℝ) * (y - c) ^ μ) * (g.eval c * g.eval y) := by ring
  rw [key]
  exact mul_pos (mul_pos (Nat.cast_pos.mpr μ.factorial_pos) (pow_pos (sub_pos.mpr hcy) _)) hpos

/-- To the left of `c`, the sign of `q` is `(-1) ^ μ` times the sign of the first nonzero
value among `q(c), q'(c), …`, where `μ` is the multiplicity of `c` as a root of `q`. -/
lemma firstNonzero_mul_eval_pos_left {q : ℝ[X]} (hq : q ≠ 0) {c y : ℝ} (hyc : y < c)
    (hz : ∀ z ∈ Ico y c, q.eval z ≠ 0) :
    0 < (-1) ^ q.rootMultiplicity c * (derivEvalList q c q.natDegree).firstNonzero *
      q.eval y := by
  have hfac := pow_mul_divByMonic_rootMultiplicity_eq q c
  have hgc := eval_divByMonic_pow_rootMultiplicity_ne_zero c hq
  rw [firstNonzero_derivEvalList_eq hq]
  generalize q /ₘ (X - C c) ^ q.rootMultiplicity c = g at hfac hgc ⊢
  generalize q.rootMultiplicity c = μ at hfac hgc ⊢
  subst hfac
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hz ⊢
  have hg : ∀ z ∈ Icc y c, g.eval z ≠ 0 := by
    intro z hzc hgz
    rcases hzc.2.eq_or_lt with h | h
    · exact hgc (h ▸ hgz)
    · exact hz z ⟨hzc.1, h⟩ (by rw [hgz, mul_zero])
  have hpos := eval_mul_eval_pos_of_forall_ne_zero hyc.le hg
  have key : (-1) ^ μ * ((μ.factorial : ℝ) * g.eval c) * ((y - c) ^ μ * g.eval y) =
      ((μ.factorial : ℝ) * (c - y) ^ μ) * (g.eval y * g.eval c) := by
    rw [show c - y = -1 * (y - c) by ring, mul_pow]
    ring
  rw [key]
  exact mul_pos (mul_pos (Nat.cast_pos.mpr μ.factorial_pos) (pow_pos (sub_pos.mpr hyc) _)) hpos

lemma lt_zero_iff_lt_zero_of_mul_pos {x y : ℝ} (h : 0 < x * y) : x < 0 ↔ y < 0 := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact ⟨fun h' => absurd h' hx.not_gt, fun h' => absurd h' hy.not_gt⟩
  · exact ⟨fun _ => hy, fun _ => hx⟩

/-! ### Root counts on intervals -/

lemma rootsIoc_add_rootsIoc {f : ℝ[X]} {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    rootsIoc f a c + rootsIoc f c b = rootsIoc f a b := by
  have h1 : (f.roots.filter fun r => a < r ∧ r ≤ b).filter (· ≤ c) =
      f.roots.filter fun r => a < r ∧ r ≤ c := by
    rw [Multiset.filter_filter]
    exact Multiset.filter_congr fun r _ =>
      ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hcb⟩⟩
  have h2 : (f.roots.filter fun r => a < r ∧ r ≤ b).filter (fun r => ¬ r ≤ c) =
      f.roots.filter fun r => c < r ∧ r ≤ b := by
    rw [Multiset.filter_filter]
    exact Multiset.filter_congr fun r _ =>
      ⟨fun h => ⟨not_le.mp h.1, h.2.2⟩,
        fun h => ⟨not_le.mpr h.1, hac.trans_lt h.1, h.2⟩⟩
  rw [rootsIoc, rootsIoc, rootsIoc, ← h1, ← h2, ← Multiset.card_add, Multiset.filter_add_not]

lemma rootsIoc_eq_rootMultiplicity {f : ℝ[X]} {a b : ℝ} (hab : a < b)
    (hf : ∀ z ∈ Ioo a b, f.eval z ≠ 0) : rootsIoc f a b = f.rootMultiplicity b := by
  rw [rootsIoc, ← count_roots, ← Multiset.card_replicate (Multiset.count b f.roots) b,
    ← Multiset.filter_eq']
  congr 1
  refine Multiset.filter_congr fun r hr => ⟨fun h => ?_, fun h => ⟨h ▸ hab, h.le⟩⟩
  by_contra hne
  exact hf r ⟨h.1, lt_of_le_of_ne h.2 hne⟩ (isRoot_of_mem_roots hr)

/-! ### The local step -/

lemma derivative_ne_zero_of_natDegree_ne_zero {p : ℝ[X]} (hp : p.natDegree ≠ 0) :
    derivative p ≠ 0 :=
  fun h => hp (derivative_eq_zero.mp h)

/-- The Rolle-type step on an interval whose interior contains no root of `p` or `p'`. -/
lemma exists_rootsIoc_derivative_add_crossTerm_of_forall {p : ℝ[X]} (hp : p.natDegree ≠ 0)
    {a b : ℝ} (hab : a < b)
    (hroots : ∀ z ∈ Ioo a b, p.eval z ≠ 0 ∧ (derivative p).eval z ≠ 0) :
    ∃ j, rootsIoc (derivative p) a b + crossTerm p a = crossTerm p b + rootsIoc p a b + 2 * j := by
  set q := derivative p with hqdef
  have hq0 : q ≠ 0 := derivative_ne_zero_of_natDegree_ne_zero hp
  have hp0 : p ≠ 0 := fun h => hp (by rw [h, natDegree_zero])
  rw [rootsIoc_eq_rootMultiplicity hab fun z hz => (hroots z hz).2,
    rootsIoc_eq_rootMultiplicity hab fun z hz => (hroots z hz).1]
  set y := (a + b) / 2 with hy
  have hay : a < y := by rw [hy]; linarith
  have hyb : y < b := by rw [hy]; linarith
  have hpy := (hroots y ⟨hay, hyb⟩).1
  have hqy := (hroots y ⟨hay, hyb⟩).2
  -- sign of the first nonzero derivative of `q` at `a` and `b`
  have hA := firstNonzero_mul_eval_pos_right hq0 hay
    (fun z hz => (hroots z ⟨hz.1, hz.2.trans_lt hyb⟩).2)
  have hB := firstNonzero_mul_eval_pos_left hq0 hyb
    (fun z hz => (hroots z ⟨hay.trans_le hz.1, hz.2⟩).2)
  set Fa := (derivEvalList q a q.natDegree).firstNonzero
  set Fb := (derivEvalList q b q.natDegree).firstNonzero
  -- the cross term at `a`
  have hea : crossTerm p a = if p.eval y * q.eval y < 0 then 1 else 0 := by
    rw [crossTerm]
    by_cases hpa : p.eval a = 0
    · have h := eval_mul_eval_derivative_pos hay hpa
        (fun z hz => (hroots z ⟨hz.1, hz.2.trans_lt hyb⟩).2)
      rw [hpa, zero_mul, ite_eq_right (lt_irrefl 0), ite_eq_right (not_lt.mpr h.le)]
    · have h1 := eval_mul_eval_pos_of_forall_ne_zero hay.le (f := p) fun z hz => by
        rcases hz.1.eq_or_lt with h | h
        · exact h ▸ hpa
        · exact (hroots z ⟨h, hz.2.trans_lt hyb⟩).1
      exact if_congr (lt_zero_iff_lt_zero_of_mul_pos (by nlinarith [mul_pos h1 hA])) rfl rfl
  rw [hea]
  by_cases hpb : p.eval b = 0
  · -- `b` is a root of `p`
    have h := eval_mul_eval_derivative_neg hyb hpb
      (fun z hz => (hroots z ⟨hay.trans_le hz.1, hz.2⟩).2)
    have hm : 0 < p.rootMultiplicity b := (rootMultiplicity_pos hp0).mpr hpb
    have hk : q.rootMultiplicity b = p.rootMultiplicity b - 1 :=
      derivative_rootMultiplicity_of_root hpb
    have heb : crossTerm p b = 0 := by
      rw [crossTerm, hpb, zero_mul, ite_eq_right (lt_irrefl 0)]
    refine ⟨0, ?_⟩
    rw [heb, ite_eq_left h, hk]
    lia
  · -- `b` is not a root of `p`
    have hm : p.rootMultiplicity b = 0 := rootMultiplicity_eq_zero hpb
    have h1 := eval_mul_eval_pos_of_forall_ne_zero hyb.le (f := p) fun z hz => by
      rcases hz.2.eq_or_lt with h | h
      · exact h ▸ hpb
      · exact (hroots z ⟨hay.trans_le hz.1, h⟩).1
    rw [hm]
    rcases Nat.even_or_odd (q.rootMultiplicity b) with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [hj, Even.neg_one_pow ⟨j, rfl⟩, one_mul] at hB
      have heb : crossTerm p b = if p.eval y * q.eval y < 0 then 1 else 0 := by
        rw [crossTerm]
        exact if_congr (lt_zero_iff_lt_zero_of_mul_pos (by nlinarith [mul_pos h1 hB])) rfl rfl
      refine ⟨j, ?_⟩
      rw [heb, hj]
      lia
    · rw [hj, Odd.neg_one_pow ⟨j, rfl⟩] at hB
      have heb : crossTerm p b = if 0 < p.eval y * q.eval y then 1 else 0 := by
        rw [crossTerm]
        refine if_congr ?_ rfl rfl
        rw [lt_zero_iff_lt_zero_of_mul_pos (y := -(p.eval y * q.eval y))
          (by nlinarith [mul_pos h1 hB]), neg_lt_zero]
      by_cases hs : p.eval y * q.eval y < 0
      · refine ⟨j + 1, ?_⟩
        rw [heb, hj, ite_eq_left hs, ite_eq_right (not_lt.mpr hs.le)]
        lia
      · have hs' : 0 < p.eval y * q.eval y :=
          lt_of_le_of_ne (not_lt.mp hs) (mul_ne_zero hpy hqy).symm
        refine ⟨j, ?_⟩
        rw [heb, hj, ite_eq_right hs, ite_eq_left hs']
        lia

/-- The Rolle-type step of the Budan–Fourier theorem: on `(a, b]`, the roots of `p'`
together with the cross terms at the endpoints account for the roots of `p`, up to an even
nonnegative number. -/
lemma exists_rootsIoc_derivative_add_crossTerm {p : ℝ[X]} (hp : p.natDegree ≠ 0)
    {a b : ℝ} (hab : a < b) :
    ∃ j, rootsIoc (derivative p) a b + crossTerm p a = crossTerm p b + rootsIoc p a b + 2 * j := by
  have hpq : p * derivative p ≠ 0 :=
    mul_ne_zero (fun h => hp (by rw [h, natDegree_zero]))
      (derivative_ne_zero_of_natDegree_ne_zero hp)
  let S : ℝ → ℝ → Finset ℝ := fun u v =>
    (p * derivative p).roots.toFinset.filter fun r => u < r ∧ r < v
  have hmem : ∀ u v r, r ∈ S u v ↔ (u < r ∧ r < v) ∧
      (p.eval r = 0 ∨ (derivative p).eval r = 0) := by
    intro u v r
    simp only [S, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hpq, IsRoot.def, eval_mul,
      mul_eq_zero]
    exact and_comm
  suffices h : ∀ n : ℕ, ∀ u v : ℝ, u < v → (S u v).card = n → ∃ j,
      rootsIoc (derivative p) u v + crossTerm p u = crossTerm p v + rootsIoc p u v + 2 * j from
    h _ a b hab rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u v huv hn
    by_cases hc : ∃ c, c ∈ S u v
    · obtain ⟨c, hc⟩ := hc
      have hc' := (hmem u v c).mp hc
      have hlt1 : (S u c).card < n := by
        rw [← hn]
        refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr ⟨c, hc, ?_⟩)
        · intro r hr
          rw [hmem] at hr ⊢
          exact ⟨⟨hr.1.1, hr.1.2.trans hc'.1.2⟩, hr.2⟩
        · rw [hmem]
          exact fun h => lt_irrefl c h.1.2
      have hlt2 : (S c v).card < n := by
        rw [← hn]
        refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr ⟨c, hc, ?_⟩)
        · intro r hr
          rw [hmem] at hr ⊢
          exact ⟨⟨hc'.1.1.trans hr.1.1, hr.1.2⟩, hr.2⟩
        · rw [hmem]
          exact fun h => lt_irrefl c h.1.1
      obtain ⟨j₁, hj₁⟩ := ih _ hlt1 u c hc'.1.1 rfl
      obtain ⟨j₂, hj₂⟩ := ih _ hlt2 c v hc'.1.2 rfl
      refine ⟨j₁ + j₂, ?_⟩
      rw [← rootsIoc_add_rootsIoc hc'.1.1.le hc'.1.2.le,
        ← rootsIoc_add_rootsIoc (f := p) hc'.1.1.le hc'.1.2.le]
      lia
    · refine exists_rootsIoc_derivative_add_crossTerm_of_forall hp huv fun z hz => ?_
      have hz' : z ∉ S u v := fun h => hc ⟨z, h⟩
      rw [hmem, not_and, not_or] at hz'
      exact hz' hz

/-! ### The Budan–Fourier theorem -/

/-- **Budan–Fourier theorem**, combined form: for a nonzero real polynomial `p` and `a < b`,
`V(a) = V(b) + N + 2 * k` for some natural number `k`, where `N` is the number of roots of `p`
in `(a, b]` counted with multiplicity. -/
theorem exists_budanFourierVar_eq {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ k, budanFourierVar p a = budanFourierVar p b + rootsIoc p a b + 2 * k := by
  obtain ⟨n, hn⟩ : ∃ n, p.natDegree = n := ⟨_, rfl⟩
  induction n generalizing p with
  | zero =>
    have hroots : rootsIoc p a b = 0 := by
      have := (Multiset.card_le_card (Multiset.filter_le (fun r => a < r ∧ r ≤ b) p.roots)).trans
        (card_roots' p)
      rw [hn] at this
      exact Nat.le_zero.mp this
    refine ⟨0, ?_⟩
    simp [budanFourierVar, hn, derivEvalList, hroots]
  | succ n ih =>
    have hp' : p.natDegree ≠ 0 := by rw [hn]; exact n.succ_ne_zero
    have hd : (derivative p).natDegree = n := by rw [natDegree_derivative, hn]; rfl
    obtain ⟨k, hk⟩ := ih (derivative_ne_zero_of_natDegree_ne_zero hp') hd
    obtain ⟨j, hj⟩ := exists_rootsIoc_derivative_add_crossTerm hp' hab
    refine ⟨k + j, ?_⟩
    rw [budanFourierVar_eq_add_crossTerm hp', budanFourierVar_eq_add_crossTerm hp']
    lia

/-- **Budan–Fourier theorem**, inequality: the number of roots of `p` in `(a, b]`, counted
with multiplicity, is at most `V(a) - V(b)`. -/
theorem rootsIoc_le_budanFourierVar_sub {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ} (hab : a < b) :
    rootsIoc p a b ≤ budanFourierVar p a - budanFourierVar p b := by
  obtain ⟨k, hk⟩ := exists_budanFourierVar_eq hp hab
  lia

/-- **Budan–Fourier theorem**, parity: `V(a) - V(b)` minus the number of roots of `p` in
`(a, b]`, counted with multiplicity, is even. -/
theorem even_budanFourierVar_sub_sub_rootsIoc {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hab : a < b) :
    Even (budanFourierVar p a - budanFourierVar p b - rootsIoc p a b) := by
  obtain ⟨k, hk⟩ := exists_budanFourierVar_eq hp hab
  exact ⟨k, by lia⟩

/-- **Budan–Fourier theorem.** Let `p` be a nonzero real polynomial of degree `n`, let
`a < b`, and let `V(x)` be the number of sign changes (zeros removed) in the sequence
`p(x), p'(x), …, p^{(n)}(x)`. Then the number of roots of `p` in `(a, b]`, counted with
multiplicity, is at most `V(a) - V(b)`, and `V(a) - V(b)` minus this number is even. -/
theorem budan_fourier {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ} (hab : a < b) :
    (p.roots.filter fun r => a < r ∧ r ≤ b).card ≤
        List.signVariations ((List.range (p.natDegree + 1)).map
          fun i => (derivative^[i] p).eval a) -
        List.signVariations ((List.range (p.natDegree + 1)).map
          fun i => (derivative^[i] p).eval b) ∧
      Even (List.signVariations ((List.range (p.natDegree + 1)).map
          fun i => (derivative^[i] p).eval a) -
        List.signVariations ((List.range (p.natDegree + 1)).map
          fun i => (derivative^[i] p).eval b) -
        (p.roots.filter fun r => a < r ∧ r ≤ b).card) := by
  rw [← budanFourierVar_eq, ← budanFourierVar_eq]
  exact ⟨rootsIoc_le_budanFourierVar_sub hp hab, even_budanFourierVar_sub_sub_rootsIoc hp hab⟩

end Polynomial

end
