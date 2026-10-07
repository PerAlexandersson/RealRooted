import RealRooted.EulerOperator.Darboux.NegativeRoots

/-!
# Multiset Eulerian–Narayana polynomials

P. B. Zhang and T. Zhao, *Zeros and interlacing for multiset Eulerian–Narayana polynomials*,
arXiv:2610.00966.

For a multiset `M = {1^{p_1}, …, m^{p_m}}` of size `N`, Lin, Ma, Ma and Zhou's leaf enumerator
`P_M(t)` of weakly increasing trees interpolates between the Eulerian (`p_i = 1`) and Narayana
(`m = 1`) polynomials.  Zhang–Zhao (Proposition 2.9) factor it into first-order steps
`P_α = E_{N-2,a_{N-2}(α)} ∘ ⋯ ∘ E_{0,a_0(α)} (1)`, where `α = (p_1, …, p_m)`,
`E_{d,a} f = (t (1 - t) f' + (a + (d + a) t) f) / a`, and `a_d(α) = N_j - d` for the least `j`
with partial sum `N_j > d` (eq. (18)).

Here this factorization defines `multisetEulerianNarayana α`.  The tree model and the
Lagrange–Bürmann argument identifying it with the leaf enumerator are not formalized; the
real-rootedness below is derived from the factorization, not assumed.

* `simpleNegRooted_step`, `simpleNegRooted_partialPoly`, `strictInterl_partialPoly`: for
  positive parameters, the partial products have degree `d`, nonnegative coefficients and
  simple negative zeros, and consecutive ones strictly interlace without common zeros
  (Lemma 2.8).
* `coeff_step_symm`, `coeff_multisetEulerianNarayana_symm`: each step preserves palindromicity
  (Lemma 3.1), so `P_α` is palindromic.
* `simpleNegRooted_multisetEulerianNarayana`: **Theorem 1.1**, all `N - 1` zeros of `P_α` are
  simple and negative (the Lin–Ma–Ma–Zhou conjecture).
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace MultisetEulerianNarayana

/-- The first-order step `E_{d,a} f = (t (1 - t) f' + (a + (d + a) t) f) / a`. -/
def step (d : ℕ) (a : ℝ) (f : ℝ[X]) : ℝ[X] :=
  C a⁻¹ * darbouxOperator a (-((d : ℝ) + a)) f

theorem step_eq (d : ℕ) (a : ℝ) (f : ℝ[X]) :
    step d a f = C a⁻¹ * (X * (1 - X) * f.derivative + (C a + C ((d : ℝ) + a) * X) * f) := by
  simp only [step, darbouxOperator, map_neg]
  ring

/-- `a_d(α) = N_j - d`, where `N_j` is the least partial sum of `α` exceeding `d`
(Zhang–Zhao, eq. (18)); it is `0` once `d ≥ |α|`. -/
def prefixGap : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, d => if d < p then p - d else prefixGap ps (d - p)

theorem prefixGap_pos : ∀ {α : List ℕ} {d : ℕ}, d < α.sum → 0 < prefixGap α d
  | [], d, h => by simp at h
  | p :: ps, d, h => by
    rw [prefixGap]
    split_ifs with hd
    · lia
    · exact prefixGap_pos (by simp at h; lia)

/-- The partial products `E_{d-1,a_{d-1}} ∘ ⋯ ∘ E_{0,a_0} (1)`. -/
def partialPoly (a : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | d + 1 => step d (a d) (partialPoly a d)

/-- The multiset Eulerian–Narayana polynomial `P_α` of a composition `α` of `N ≥ 1`, defined
by the Zhang–Zhao factorization. -/
def multisetEulerianNarayana (α : List ℕ) : ℝ[X] :=
  partialPoly (fun d => (prefixGap α d : ℝ)) (α.sum - 1)

/-- One step `E_{d,a}` with `a > 0` raises the degree by one, keeps simple negative zeros, and
strictly interlaces with its input without common zeros (Zhang–Zhao, Lemma 2.8). -/
theorem simpleNegRooted_step {f : ℝ[X]} {d : ℕ} (hf : SimpleNegRooted f d) {a : ℝ}
    (ha : 0 < a) :
    SimpleNegRooted (step d a f) (d + 1) ∧ StrictInterl f (step d a f) ∧
      ∀ r, f.IsRoot r → ¬ (step d a f).IsRoot r := by
  obtain ⟨h1, h2, h3⟩ := hf.darbouxOperator ha (b := (d : ℝ) + a) (by linarith)
  have hc : 0 < a⁻¹ := inv_pos.mpr ha
  refine ⟨h1.C_mul hc, h2.C_mul_right hc.ne', fun r hr hFr => h3 r hr ?_⟩
  rw [step, IsRoot, eval_mul, eval_C] at hFr
  exact (mul_eq_zero.mp hFr).resolve_left hc.ne'

/-- **Zhang–Zhao, Lemma 2.8 along the factorization.**  If `a d > 0` for `d < n`, then the
`n`-th partial product has degree `n` and simple negative zeros. -/
theorem simpleNegRooted_partialPoly {a : ℕ → ℝ} :
    ∀ {n : ℕ}, (∀ d < n, 0 < a d) → SimpleNegRooted (partialPoly a n) n
  | 0, _ => SimpleNegRooted.one
  | n + 1, ha =>
    (simpleNegRooted_step (simpleNegRooted_partialPoly (n := n) fun d hd => ha d (by lia))
      (ha n (by lia))).1

/-- Consecutive partial products strictly interlace and have no common zero. -/
theorem strictInterl_partialPoly {a : ℕ → ℝ} {n : ℕ} (ha : ∀ d ≤ n, 0 < a d) :
    StrictInterl (partialPoly a n) (partialPoly a (n + 1)) ∧
      ∀ r, (partialPoly a n).IsRoot r → ¬ (partialPoly a (n + 1)).IsRoot r :=
  (simpleNegRooted_step (simpleNegRooted_partialPoly (n := n) fun d hd => ha d hd.le)
    (ha n le_rfl)).2

/-- **Zhang–Zhao, Theorem 1.1** (the Lin–Ma–Ma–Zhou conjecture).  For a composition `α` of
`N ≥ 1`, the multiset Eulerian–Narayana polynomial `P_α` has degree `N - 1`, nonnegative
coefficients, and only simple negative zeros. -/
theorem simpleNegRooted_multisetEulerianNarayana {α : List ℕ} (hα : α.sum ≠ 0) :
    SimpleNegRooted (multisetEulerianNarayana α) (α.sum - 1) :=
  simpleNegRooted_partialPoly fun d hd => by
    exact_mod_cast prefixGap_pos (α := α) (by lia)

/-- The zeros of `P_α` are negative. -/
theorem isRoot_multisetEulerianNarayana_neg {α : List ℕ} (hα : α.sum ≠ 0) {r : ℝ}
    (hr : (multisetEulerianNarayana α).IsRoot r) : r < 0 :=
  (simpleNegRooted_multisetEulerianNarayana hα).isRoot_neg hr

/-! ### Palindromicity -/

private theorem coeff_darboux_succ (d : ℕ) (a : ℝ) (f : ℝ[X]) (k : ℕ) :
    (darbouxOperator a (-((d : ℝ) + a)) f).coeff (k + 1) =
      (k + 1 + a) * f.coeff (k + 1) + ((d : ℝ) + a - k) * f.coeff k := by
  rw [coeff_darbouxOperator_succ]
  ring

private theorem coeff_darboux_zero (d : ℕ) (a : ℝ) (f : ℝ[X]) :
    (darbouxOperator a (-((d : ℝ) + a)) f).coeff 0 = a * f.coeff 0 := by
  rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, darbouxOperator_eval_zero]

/-- **Zhang–Zhao, Lemma 3.1.**  If `f` has degree at most `d` and is palindromic of degree `d`,
then `E_{d,a} f` is palindromic of degree `d + 1`. -/
theorem coeff_step_symm {f : ℝ[X]} {d : ℕ} (a : ℝ) (hdeg : f.natDegree ≤ d)
    (hf : ∀ k ≤ d, f.coeff k = f.coeff (d - k)) :
    ∀ k ≤ d + 1, (step d a f).coeff k = (step d a f).coeff (d + 1 - k) := by
  have htop : f.coeff (d + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
  have hend : (darbouxOperator a (-((d : ℝ) + a)) f).coeff (d + 1) =
      (darbouxOperator a (-((d : ℝ) + a)) f).coeff 0 := by
    rw [coeff_darboux_succ, coeff_darboux_zero, htop, hf 0 (by lia), Nat.sub_zero]
    ring
  intro k hk
  simp only [step, coeff_C_mul]
  congr 1
  rcases k with _ | j
  · rw [Nat.sub_zero, hend]
  rcases eq_or_lt_of_le (show j ≤ d by lia) with rfl | hj
  · rw [Nat.sub_self, hend]
  obtain ⟨m, rfl⟩ : ∃ m, d = j + 1 + m := ⟨d - (j + 1), by lia⟩
  rw [show j + 1 + m + 1 - (j + 1) = m + 1 by lia, coeff_darboux_succ, coeff_darboux_succ,
    hf j (by lia), hf (j + 1) (by lia), show j + 1 + m - j = m + 1 by lia,
    show j + 1 + m - (j + 1) = m by lia]
  push_cast
  ring

/-- The partial products are palindromic. -/
theorem coeff_partialPoly_symm (a : ℕ → ℝ) :
    ∀ n, (partialPoly a n).natDegree ≤ n ∧
      ∀ k ≤ n, (partialPoly a n).coeff k = (partialPoly a n).coeff (n - k)
  | 0 => ⟨by simp [partialPoly], fun k hk => by rw [Nat.le_zero.mp hk]⟩
  | n + 1 => by
    obtain ⟨hdeg, hsymm⟩ := coeff_partialPoly_symm a n
    refine ⟨?_, coeff_step_symm (a n) hdeg hsymm⟩
    refine (natDegree_le_iff_coeff_eq_zero).mpr fun j hj => ?_
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by lia⟩
    rw [partialPoly, step, coeff_C_mul, coeff_darboux_succ,
      coeff_eq_zero_of_natDegree_lt (show (partialPoly a n).natDegree < k + 1 by lia),
      coeff_eq_zero_of_natDegree_lt (show (partialPoly a n).natDegree < k by lia)]
    ring

/-- `P_α` is palindromic: `[t^k] P_α = [t^{N-1-k}] P_α`. -/
theorem coeff_multisetEulerianNarayana_symm (α : List ℕ) {k : ℕ} (hk : k ≤ α.sum - 1) :
    (multisetEulerianNarayana α).coeff k = (multisetEulerianNarayana α).coeff (α.sum - 1 - k) :=
  (coeff_partialPoly_symm _ _).2 k hk

end MultisetEulerianNarayana
end RealRooted
