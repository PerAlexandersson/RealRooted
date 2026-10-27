/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Finite.Defs
public import Aesop.BuiltinRules

/-!
# Lassos for ultimately periodic paths

`exists_lasso_of_periodic_path`: by pigeonhole on the pair (label, index mod `m`), a path through
an edge relation that is periodic from some point on can be replaced by an ultimately periodic
path (a lasso) with the same prefix (RealRooted issue #1895).  The proof was found by Aristotle
(Harmonic).
-/

public section

private lemma lasso_pigeonhole {L : Type*} [Finite L] (N₀ m : ℕ) (hm : m ≠ 0)
    (σ : ℕ → L) :
    ∃ N N2 : ℕ, N₀ ≤ N ∧ N < N2 ∧ σ N = σ N2 ∧ N % m = N2 % m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (σ (N₀ + k), (⟨(N₀ + k) % m, Nat.mod_lt _ hmpos⟩ : Fin m)))
  simp only [Prod.mk.injEq, Fin.mk.injEq] at he
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨N₀ + a, N₀ + b, by lia, by lia, he.1, he.2⟩
  · exact ⟨N₀ + b, N₀ + a, by lia, by lia, he.1.symm, he.2.symm⟩

private lemma lasso_periodic_iter {L : Type*} (Edge : ℕ → L → L → Prop) (N₀ m : ℕ)
    (hper : ∀ n ≥ N₀, ∀ s t, Edge (n + m) s t ↔ Edge n s t) :
    ∀ k, ∀ n ≥ N₀, ∀ s t, Edge (n + k * m) s t ↔ Edge n s t := by
  intro k
  induction k with
  | zero => intro n _ s t; simp
  | succ k ih =>
    intro n hn s t
    rw [show n + (k + 1) * m = (n + k * m) + m by ring, hper _ (by lia), ih n hn]

/-- A path through an edge relation that is periodic with period `m` from `N₀` on can be replaced
by a lasso: a path `τ` that agrees with `σ` before some `N ≥ N₀` and is periodic from `N` on,
with a period `ℓ` that is a positive multiple of `m`. -/
theorem exists_lasso_of_periodic_path {L : Type*} [Finite L]
    (Edge : ℕ → L → L → Prop) (N₀ m : ℕ) (hm : m ≠ 0)
    (hper : ∀ n ≥ N₀, ∀ s t, Edge (n + m) s t ↔ Edge n s t)
    (σ : ℕ → L) (hσ : ∀ n, Edge n (σ n) (σ (n + 1))) :
    ∃ (N ℓ : ℕ) (τ : ℕ → L), ℓ ≠ 0 ∧ m ∣ ℓ ∧ N₀ ≤ N ∧
      (∀ n, Edge n (τ n) (τ (n + 1))) ∧ (∀ n < N, τ n = σ n) ∧
      ∀ n ≥ N, τ (n + ℓ) = τ n := by
  obtain ⟨N, N2, hN, hlt, hσe, hmod⟩ := lasso_pigeonhole N₀ m hm σ
  set ℓ := N2 - N with hℓ
  have hℓ0 : ℓ ≠ 0 := by lia
  have hℓpos : 0 < ℓ := Nat.pos_of_ne_zero hℓ0
  have hdvd : m ∣ ℓ := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod.symm)
  obtain ⟨c, hc⟩ := hdvd
  have iter := lasso_periodic_iter Edge N₀ m hper
  refine ⟨N, ℓ, fun n => if n < N then σ n else σ (N + (n - N) % ℓ), hℓ0, ⟨c, hc⟩, hN,
    ?_, ?_, ?_⟩
  · intro n
    by_cases h1 : n + 1 < N
    · simp only [h1, show n < N by lia, ite_true]
      exact hσ n
    by_cases h2 : n + 1 = N
    · simp only [show n < N by lia, h1, ite_true, ite_false]
      rw [show n + 1 - N = 0 by lia, Nat.zero_mod, Nat.add_zero, ← h2]
      exact hσ n
    · simp only [show ¬ n < N by lia, h1, ite_false]
      set r := (n - N) % ℓ with hr
      have hrlt : r < ℓ := Nat.mod_lt _ hℓpos
      have hn : n = (N + r) + ((n - N) / ℓ * c) * m := by
        have := Nat.div_add_mod (n - N) ℓ
        have h' : (n - N) / ℓ * c * m = ℓ * ((n - N) / ℓ) := by rw [hc]; ring
        lia
      rw [hn, iter _ _ (by lia)]
      rw [← hn]
      have hr1 : (n + 1 - N) % ℓ = (r + 1) % ℓ := by
        rw [show n + 1 - N = (n - N) + 1 by lia, Nat.add_mod (n - N) 1 ℓ, ← hr,
          Nat.add_mod_mod]
      rw [hr1]
      by_cases h3 : r + 1 < ℓ
      · rw [Nat.mod_eq_of_lt h3, ← add_assoc]
        exact hσ _
      · have h4 : r + 1 = ℓ := by lia
        rw [h4, Nat.mod_self, Nat.add_zero, hσe, show N2 = N + r + 1 by lia]
        exact hσ _
  · intro n hn
    simp [hn]
  · intro n hn
    simp only [show ¬ n + ℓ < N by lia, show ¬ n < N by lia, ite_false]
    rw [show n + ℓ - N = (n - N) + ℓ by lia, Nat.add_mod_right]
