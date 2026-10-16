module

public import RealRooted.DegreeDropReversal
public import RealRooted.Graph.IndependencePolynomial.ClawFree

/-!
# A cubic parent with real-rooted coefficients

We formalize the special case of Tran and Zumba's linear-coefficient theorem needed for
the cubic-parent OEIS rows.  Their Theorem 1 in *Zeros of polynomials with four-term
recurrence and linear coefficients*, arXiv:1808.07133v1 (2018), treats

`1 / (1 + c t + (b₀ + b₁ z) t² + (a₀ + a₁ z) t³)`

under `c a₁ ≠ 0` and `c a₁ b₁ ≤ 0`.  With
`c = 1`, `b₀ = a₀ = 0`, `b₁ = -1`, and `a₁ = 1`, its normalized parameters are
`a = 0`, `b = 1`, so the sufficient inequalities are `1 + a + b = 2 ≥ 0` and
`9 - 27a + b = 10 ≥ 0`.

Here we prove this instance independently by a claw-free independence-polynomial model.
Thus `polynomial m` is the coefficient of `t^m` in
`1 / (1 + t - X t² + X t³)`, as witnessed by its initial values and recurrence, and every
`polynomial m` splits over `ℝ`.

The earlier constant-coefficient theorem is Theorem 1 of Tran and Zumba,
*Zeros of polynomials with four-term recurrence*, Involve 11 (2018), 501--518,
doi:10.2140/involve.2018.11.501, arXiv:1701.07814v1.  It applies to
`1 / (1 + c t + b t² + z t³)` and, when `c ≠ 0`, gives the sharp range
`-1 ≤ b / c² ≤ 1/3`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.CubicParent

def intervalGraph : SimpleGraph ℕ :=
  SimpleGraph.fromRel fun i j =>
    i < j ∧ (j ≤ i + 3 ∨ (j = i + 4 ∧ i % 2 = 1))

private instance intervalGraphDecidableAdj :
    DecidableRel intervalGraph.Adj :=
  Classical.decRel _

def prefixPolynomial (N : ℕ) : ℝ[X] := by
  classical
  exact Graph.indepPolyOn intervalGraph (Finset.range N)

private lemma intervalGraph_adj_of_lt {i j : ℕ} (hij : i < j) :
    intervalGraph.Adj i j ↔
      j ≤ i + 3 ∨ (j = i + 4 ∧ i % 2 = 1) := by
  simp only [intervalGraph, SimpleGraph.fromRel_adj]
  grind

private lemma intervalGraph_adj_of_lt_of_le_add_three
    {i j : ℕ} (hij : i < j) (hji : j ≤ i + 3) :
    intervalGraph.Adj i j :=
  (intervalGraph_adj_of_lt hij).2 (Or.inl hji)

private lemma intervalGraph_adj_of_neighbors_same_side
    {v a b : ℕ}
    (hva : intervalGraph.Adj v a)
    (hvb : intervalGraph.Adj v b)
    (hab : a ≠ b)
    (hside : (a < v ∧ b < v) ∨ (v < a ∧ v < b)) :
    intervalGraph.Adj a b := by
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · apply intervalGraph_adj_of_lt_of_le_add_three hablt
    rcases hside with ⟨hav, hbv⟩ | ⟨hva', hvb'⟩
    · have hvBound :
          v ≤ a + 3 ∨ (v = a + 4 ∧ a % 2 = 1) := by
        rw [← intervalGraph_adj_of_lt hav, SimpleGraph.adj_comm]
        grind
      lia
    · have hbBound :
          b ≤ v + 3 ∨ (b = v + 4 ∧ v % 2 = 1) :=
        (intervalGraph_adj_of_lt hvb').1 hvb
      lia
  · rw [SimpleGraph.adj_comm]
    apply intervalGraph_adj_of_lt_of_le_add_three hbalt
    rcases hside with ⟨hav, hbv⟩ | ⟨hva', hvb'⟩
    · have hvBound :
          v ≤ b + 3 ∨ (v = b + 4 ∧ b % 2 = 1) := by
        rw [← intervalGraph_adj_of_lt hbv, SimpleGraph.adj_comm]
        grind
      lia
    · have haBound :
          a ≤ v + 3 ∨ (a = v + 4 ∧ v % 2 = 1) :=
        (intervalGraph_adj_of_lt hva').1 hva
      lia

private lemma intervalGraph_clawFree : Graph.ClawFree intervalGraph := by
  intro v s hneigh hind
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
    Finset.card_eq_three.mp hind.card_eq
  have hva := hneigh a (by simp)
  have hvb := hneigh b (by simp)
  have hvc := hneigh c (by simp)
  have hav : a ≠ v := fun h ↦ by simp_all
  have hbv : b ≠ v := fun h ↦ by simp_all
  have hcv : c ≠ v := fun h ↦ by simp_all
  rcases lt_or_gt_of_ne hav with hav | hva'
  · rcases lt_or_gt_of_ne hbv with hbv | hvb'
    · exact hind.isIndepSet (by simp) (by simp) hab
        (intervalGraph_adj_of_neighbors_same_side hva hvb hab
          (Or.inl ⟨hav, hbv⟩))
    · rcases lt_or_gt_of_ne hcv with hcv | hvc'
      · exact hind.isIndepSet (by simp) (by simp) hac
          (intervalGraph_adj_of_neighbors_same_side hva hvc hac
            (Or.inl ⟨hav, hcv⟩))
      · exact hind.isIndepSet (by simp) (by simp) hbc
          (intervalGraph_adj_of_neighbors_same_side hvb hvc hbc
            (Or.inr ⟨hvb', hvc'⟩))
  · rcases lt_or_gt_of_ne hbv with hbv | hvb'
    · rcases lt_or_gt_of_ne hcv with hcv | hvc'
      · exact hind.isIndepSet (by simp) (by simp) hbc
          (intervalGraph_adj_of_neighbors_same_side hvb hvc hbc
            (Or.inl ⟨hbv, hcv⟩))
      · exact hind.isIndepSet (by simp) (by simp) hac
          (intervalGraph_adj_of_neighbors_same_side hva hvc hac
            (Or.inr ⟨hva', hvc'⟩))
    · exact hind.isIndepSet (by simp) (by simp) hab
        (intervalGraph_adj_of_neighbors_same_side hva hvb hab
          (Or.inr ⟨hva', hvb'⟩))

private lemma intervalGraph_filter_even (N : ℕ) (hN : N % 2 = 0) :
    (Finset.range N).filter (fun w => ¬ intervalGraph.Adj N w) =
      Finset.range (N - 3) := by
  classical
  rw [Finset.ext_iff]
  intro w
  rw [Finset.mem_filter]
  simp only [Finset.mem_range]
  constructor
  · rintro ⟨hwN, hnot⟩
    have hadjIff :
        intervalGraph.Adj N w ↔
          N ≤ w + 3 ∨ (N = w + 4 ∧ w % 2 = 1) := by
      rw [SimpleGraph.adj_comm]
      exact intervalGraph_adj_of_lt hwN
    grind
  · intro hw
    have hwN : w < N := by lia
    refine ⟨hwN, ?_⟩
    rw [SimpleGraph.adj_comm]
    intro hadj
    rcases (intervalGraph_adj_of_lt hwN).1 hadj with hclose | ⟨hfour, hodd⟩
    · lia
    · lia

private lemma intervalGraph_filter_odd (N : ℕ) (hN : N % 2 = 1) :
    (Finset.range N).filter (fun w => ¬ intervalGraph.Adj N w) =
      Finset.range (N - 4) := by
  classical
  rw [Finset.ext_iff]
  intro w
  rw [Finset.mem_filter]
  simp only [Finset.mem_range]
  constructor
  · rintro ⟨hwN, hnot⟩
    have hadjIff :
        intervalGraph.Adj N w ↔
          N ≤ w + 3 ∨ (N = w + 4 ∧ w % 2 = 1) := by
      rw [SimpleGraph.adj_comm]
      exact intervalGraph_adj_of_lt hwN
    grind
  · intro hw
    have hwN : w < N := by lia
    refine ⟨hwN, ?_⟩
    rw [SimpleGraph.adj_comm]
    intro hadj
    rcases (intervalGraph_adj_of_lt hwN).1 hadj with hclose | ⟨hfour, hodd⟩
    · lia
    · lia

private lemma prefixPolynomial_succ_even (N : ℕ) (hN : N % 2 = 0) :
    prefixPolynomial (N + 1) =
      prefixPolynomial N + X * prefixPolynomial (N - 3) := by
  classical
  rw [prefixPolynomial, prefixPolynomial, prefixPolynomial]
  rw [show Finset.range (N + 1) = insert N (Finset.range N) by grind]
  rw [Graph.indepPolyOn_insert
    (G := intervalGraph) (S := Finset.range N) (v := N) (by simp)]
  rw [intervalGraph_filter_even N hN]

private lemma prefixPolynomial_succ_odd (N : ℕ) (hN : N % 2 = 1) :
    prefixPolynomial (N + 1) =
      prefixPolynomial N + X * prefixPolynomial (N - 4) := by
  classical
  rw [prefixPolynomial, prefixPolynomial, prefixPolynomial]
  rw [show Finset.range (N + 1) = insert N (Finset.range N) by grind]
  rw [Graph.indepPolyOn_insert
    (G := intervalGraph) (S := Finset.range N) (v := N) (by simp)]
  rw [intervalGraph_filter_odd N hN]

private lemma prefixPolynomial_zero : prefixPolynomial 0 = 1 := by
  simpa [prefixPolynomial] using Graph.indepPolyOn_empty intervalGraph

private lemma prefixPolynomial_one : prefixPolynomial 1 = 1 + X := by
  have h := prefixPolynomial_succ_even 0 (by simp)
  norm_num at h
  rw [h, prefixPolynomial_zero]
  ring

def unsignedPolynomial (m : ℕ) : ℝ[X] :=
  prefixPolynomial (2 * m - 3)

private lemma unsignedPolynomial_add_three (m : ℕ) :
    unsignedPolynomial (m + 3) =
      unsignedPolynomial (m + 2) + X * unsignedPolynomial (m + 1) +
        X * unsignedPolynomial m := by
  have heven := prefixPolynomial_succ_even (2 * m + 2) (by
    simp)
  have hodd := prefixPolynomial_succ_odd (2 * m + 1) (by
    simp [Nat.add_mod])
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by lia, hodd] at heven
  unfold unsignedPolynomial
  rw [show 2 * (m + 3) - 3 = (2 * m + 2) + 1 by lia,
    show 2 * (m + 2) - 3 = 2 * m + 1 by lia,
    show 2 * (m + 1) - 3 = (2 * m + 2) - 3 by lia,
    show 2 * m - 3 = (2 * m + 1) - 4 by lia,
    heven]
  ring

/-- The coefficient polynomials of `1 / (1 + t - X t² + X t³)`.

The alternating scalar is separated from a claw-free independence polynomial;
this definition makes the real-rootedness proof direct. -/
def polynomial (m : ℕ) : ℝ[X] :=
  C ((-1 : ℝ) ^ m) * unsignedPolynomial m

/-- The cubic parent starts with coefficient `1`. -/
@[simp] theorem polynomial_zero : polynomial 0 = 1 := by
  simp [polynomial, unsignedPolynomial, prefixPolynomial_zero]

/-- The coefficient of `t` in the cubic parent series is `-1`. -/
@[simp] theorem polynomial_one : polynomial 1 = -1 := by
  simp [polynomial, unsignedPolynomial, prefixPolynomial_zero]

/-- The coefficient of `t²` in the cubic parent series is `1 + X`. -/
@[simp] theorem polynomial_two : polynomial 2 = 1 + X := by
  simp [polynomial, unsignedPolynomial, prefixPolynomial_one]

/-- The coefficient polynomials satisfy the recurrence obtained from
`(1 + t - X t² + X t³) * ∑ m, polynomial m * t^m = 1`. -/
theorem polynomial_add_three (m : ℕ) :
    polynomial (m + 3) =
      -polynomial (m + 2) + X * polynomial (m + 1) - X * polynomial m := by
  rw [polynomial, polynomial, polynomial, polynomial, unsignedPolynomial_add_three]
  simp only [pow_succ]
  norm_num
  ring

/-- Eliminating the odd or even intermediate coefficients gives the order-three
recurrence satisfied by each parity subsequence. -/
theorem polynomial_add_six (m : ℕ) :
    polynomial (m + 6) =
      (1 + 2 * X) * polynomial (m + 4) +
        (2 * X - X ^ 2) * polynomial (m + 2) + X ^ 2 * polynomial m := by
  have h0 := polynomial_add_three m
  have h1 := polynomial_add_three (m + 1)
  have h2 := polynomial_add_three (m + 2)
  have h3 := polynomial_add_three (m + 3)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h0 h1 h2 h3
  rw [h3, h2, h1, h0]
  ring

/-- Every coefficient polynomial of `1 / (1 + t - X t² + X t³)` splits over `ℝ`.

This is the `a = 0`, `b = 1` sufficiency instance of Tran--Zumba's 2018
linear-coefficient theorem. -/
theorem polynomial_splits (m : ℕ) : (polynomial m).Splits := by
  apply Polynomial.Splits.C_mul
  unfold unsignedPolynomial prefixPolynomial
  exact Graph.supportIndepPoly_splits_of_clawFree
    intervalGraph_clawFree (Finset.range (2 * m - 3))

end RealRooted.CubicParent
