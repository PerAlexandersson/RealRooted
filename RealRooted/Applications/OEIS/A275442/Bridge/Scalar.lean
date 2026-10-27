module

import RealRooted.Applications.OEIS.A275442.Bridge.Certificates
import RealRooted.Applications.OEIS.A275442.Bridge.Trajectory
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Basic.Real.Basic

/-!
# The structural induction for trajectories of the lag-four recurrence

This file proves, for an arbitrary real sequence `S` satisfying

```
S (k+4) = S (k+3) + S (k+2) - t · S k        (t > 1)
```

whose first four values have a common strict sign, and whose *initial runs* are already
under control (`InitRun`), the following statement at every crossing of `S`:

if `0 < S (n+3)` and `S (n+4) ≤ 0` then

* `S (n+3) < t · S (n+1)`   (the **crux**, i.e. the bridge inequality), and
* `S (n+5), S (n+6), S (n+7) < 0`, and `S (n+8) < 0` as well when `S (n+4) = 0`.

The proof is a single strong induction which treats `S` and `-S` simultaneously; the four
Farkas certificates from the preceding support module discharge the cases of a long run of
positive values, and `Bridge.crux_of_prev`, `Bridge.crux_of_short_run` the short ones.
-/

@[expose] public section

namespace RealRooted.Applications.OEIS.A275442.Bridge

variable {t : ℝ} {S : ℕ → ℝ} {n : ℕ}

/-- The conclusion of the induction at a crossing at index `n+4`. -/
def DownStep (t : ℝ) (S : ℕ → ℝ) (n : ℕ) : Prop :=
  0 < S (n + 3) → S (n + 4) ≤ 0 →
    S (n + 3) < t * S (n + 1) ∧ S (n + 5) < 0 ∧ S (n + 6) < 0 ∧ S (n + 7) < 0 ∧
      (S (n + 4) = 0 → S (n + 8) < 0)

/-- The induction hypothesis: the conclusion at all smaller indices, for `S` and for `-S`. -/
def IHyp (t : ℝ) (S : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ m < n, DownStep t S m ∧ DownStep t (-S) m

/-- The initial-run hypothesis: crossings preceded only by positive values are fine. -/
def InitRun (t : ℝ) (S : ℕ → ℝ) : Prop :=
  ∀ n, 0 < S (n + 3) → S (n + 4) ≤ 0 → (∀ j, 1 ≤ j → j ≤ n + 3 → 0 < S j) →
    S (n + 3) < t * S (n + 1)

/-- The first four values of `S` all have the same strict sign. -/
def StartSign (S : ℕ → ℝ) : Prop := (∀ j ≤ 3, 0 < S j) ∨ (∀ j ≤ 3, S j < 0)

theorem StartSign.neg (h : StartSign S) : StartSign (-S) := by
  rcases h with h | h
  · exact Or.inr fun j hj => by simpa using h j hj
  · exact Or.inl fun j hj => by simpa using h j hj

theorem IHyp.neg (h : IHyp t S n) : IHyp t (-S) n := by
  intro m hm
  exact ⟨(h m hm).2, by simpa using (h m hm).1⟩

/-- The recurrence for the mirrored sequence. -/
theorem neg_rec' (hrec : ∀ k, S (k + 4) = S (k + 3) + S (k + 2) - t * S k) :
    ∀ k, (-S) (k + 4) = (-S) (k + 3) + (-S) (k + 2) - t * (-S) k := by
  intro k; simp only [Pi.neg_apply, hrec k]; ring

/-- **After a crossing the next three values are strictly negative** (and the fourth as well
if the crossing value is exactly `0`).  This is a direct computation from the crux. -/
theorem next_neg (hrec : ∀ k, S (k + 4) = S (k + 3) + S (k + 2) - t * S k) (ht : 0 < t)
    (j : ℕ) (hcross : S (j + 4) ≤ 0) (h2 : 0 < S (j + 2)) (h3 : 0 < S (j + 3))
    (hcrux : S (j + 3) < t * S (j + 1)) :
    S (j + 5) < 0 ∧ S (j + 6) < 0 ∧ S (j + 7) < 0 ∧ (S (j + 4) = 0 → S (j + 8) < 0) := by
  have e5 : S (j + 5) = S (j + 4) + S (j + 3) - t * S (j + 1) := hrec (j + 1)
  have e6 : S (j + 6) = S (j + 5) + S (j + 4) - t * S (j + 2) := hrec (j + 2)
  have e7 : S (j + 7) = S (j + 6) + S (j + 5) - t * S (j + 3) := hrec (j + 3)
  have e8 : S (j + 8) = S (j + 7) + S (j + 6) - t * S (j + 4) := hrec (j + 4)
  have h5 : S (j + 5) < 0 := by rw [e5]; linarith
  have h6 : S (j + 6) < 0 := by rw [e6]; nlinarith
  have h7 : S (j + 7) < 0 := by rw [e7]; nlinarith
  refine ⟨h5, h6, h7, fun hz => ?_⟩
  rw [e8, hz]; linarith

/-! ### Consequences of the induction hypothesis -/

/-- **No two consecutive zeros.** -/
theorem no_two_zeros (hstart : StartSign S) (hIH : IHyp t S n) :
    ∀ c, c < n + 4 → S c = 0 → S (c + 1) = 0 → False := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc h0 h1
    rcases Nat.lt_or_ge c 4 with hc4 | hc4
    · rcases hstart with hp | hn
      · exact absurd h0 (ne_of_gt (hp c (by lia)))
      · exact absurd h0 (ne_of_lt (hn c (by lia)))
    · obtain ⟨j, rfl⟩ : ∃ j, c = j + 4 := ⟨c - 4, by lia⟩
      have hj : j < n := by lia
      have h1' : S (j + 5) = 0 := by rw [show j + 5 = j + 4 + 1 from by lia]; exact h1
      rcases lt_trichotomy (S (j + 3)) 0 with h | h | h
      · have hd := (hIH j hj).2 (by simp only [Pi.neg_apply]; linarith)
          (by simp only [Pi.neg_apply, h0]; norm_num)
        have := hd.2.1
        simp only [Pi.neg_apply] at this
        linarith
      · exact ih (j + 3) (by lia) (by lia) h h0
      · have hd := (hIH j hj).1 h (le_of_eq h0)
        have := hd.2.1
        linarith

/-- **A zero is followed by three values of a common strict sign.** -/
theorem zero_next (hstart : StartSign S) (hIH : IHyp t S n) {c : ℕ} (hc : c < n + 4)
    (hz : S c = 0) :
    (S (c + 1) < 0 ∧ S (c + 2) < 0 ∧ S (c + 3) < 0) ∨
      (0 < S (c + 1) ∧ 0 < S (c + 2) ∧ 0 < S (c + 3)) := by
  rcases Nat.lt_or_ge c 4 with hc4 | hc4
  · rcases hstart with hp | hn
    · exact absurd hz (ne_of_gt (hp c (by lia)))
    · exact absurd hz (ne_of_lt (hn c (by lia)))
  obtain ⟨j, rfl⟩ : ∃ j, c = j + 4 := ⟨c - 4, by lia⟩
  have hj : j < n := by lia
  rcases lt_trichotomy (S (j + 3)) 0 with h | h | h
  · have hd := (hIH j hj).2 (by simp only [Pi.neg_apply]; linarith)
      (by simp only [Pi.neg_apply, hz]; norm_num)
    obtain ⟨-, h5, h6, h7, -⟩ := hd
    simp only [Pi.neg_apply] at h5 h6 h7
    refine Or.inr ⟨?_, ?_, ?_⟩ <;>
      [rw [show j + 4 + 1 = j + 5 from by lia]; rw [show j + 4 + 2 = j + 6 from by lia];
        rw [show j + 4 + 3 = j + 7 from by lia]] <;> linarith
  · exact absurd hz (fun hz => no_two_zeros hstart hIH (j + 3) (by lia) h hz)
  · have hd := (hIH j hj).1 h (le_of_eq hz)
    obtain ⟨-, h5, h6, h7, -⟩ := hd
    refine Or.inl ⟨?_, ?_, ?_⟩ <;>
      [rw [show j + 4 + 1 = j + 5 from by lia]; rw [show j + 4 + 2 = j + 6 from by lia];
        rw [show j + 4 + 3 = j + 7 from by lia]] <;> linarith

/-- **A positive value right after a nonpositive one starts a run of length at least four.** -/
theorem after_nonpos (hstart : StartSign S) (hIH : IHyp t S n) {c : ℕ} (hc : c + 1 < n + 4)
    (hle : S c ≤ 0) (hpos : 0 < S (c + 1)) :
    0 < S (c + 2) ∧ 0 < S (c + 3) ∧ 0 < S (c + 4) := by
  rcases lt_or_eq_of_le hle with hlt | hz
  · -- `c` is a strict crossing of `-S` at index `c+1`
    rcases Nat.lt_or_ge c 3 with hc3 | hc3
    · exfalso
      rcases hstart with hp | hn
      · exact absurd hlt (not_lt.mpr (le_of_lt (hp c (by lia))))
      · exact absurd hpos (not_lt.mpr (le_of_lt (hn (c + 1) (by lia))))
    obtain ⟨j, rfl⟩ : ∃ j, c = j + 3 := ⟨c - 3, by lia⟩
    have hj : j < n := by lia
    have hd := (hIH j hj).2 (by simp only [Pi.neg_apply]; linarith)
      (by simp only [Pi.neg_apply]; linarith)
    obtain ⟨-, h5, h6, h7, -⟩ := hd
    simp only [Pi.neg_apply] at h5 h6 h7
    refine ⟨?_, ?_, ?_⟩ <;>
      [rw [show j + 3 + 2 = j + 5 from by lia]; rw [show j + 3 + 3 = j + 6 from by lia];
        rw [show j + 3 + 4 = j + 7 from by lia]] <;> linarith
  · -- `S c = 0`: then `S (c-1) < 0` and `c` is a crossing of `-S` with value `0`
    rcases Nat.lt_or_ge c 4 with hc4 | hc4
    · exfalso
      rcases hstart with hp | hn
      · exact absurd hz (hp c (by lia)).ne'
      · rcases Nat.lt_or_ge (c + 1) 4 with h4 | h4
        · exact absurd hpos (not_lt.mpr (le_of_lt (hn (c + 1) (by lia))))
        · exact absurd hz (hn c (by lia)).ne
    obtain ⟨j, rfl⟩ : ∃ j, c = j + 4 := ⟨c - 4, by lia⟩
    have hj : j < n := by lia
    have hneg : S (j + 3) < 0 := by
      rcases lt_trichotomy (S (j + 3)) 0 with h | h | h
      · exact h
      · exact absurd (no_two_zeros hstart hIH (j + 3) (by lia) h
          (by rw [show j + 3 + 1 = j + 4 from by lia]; exact hz)) not_false
      · exfalso
        have hd := (hIH j hj).1 h (le_of_eq hz)
        have h5 := hd.2.1
        rw [show j + 4 + 1 = j + 5 from by lia] at hpos
        linarith
    have hd := (hIH j hj).2 (by simp only [Pi.neg_apply]; linarith)
      (by simp only [Pi.neg_apply, hz]; norm_num)
    obtain ⟨-, -, h6, h7, h8⟩ := hd
    simp only [Pi.neg_apply] at h6 h7 h8
    have h8' := h8 (by rw [hz]; norm_num)
    refine ⟨?_, ?_, ?_⟩ <;>
      [rw [show j + 4 + 2 = j + 6 from by lia]; rw [show j + 4 + 3 = j + 7 from by lia];
        rw [show j + 4 + 4 = j + 8 from by lia]] <;> linarith

/-! ### Reading the sign pattern backwards -/

/-- If the value after a nonpositive one is positive, the earlier value is nonpositive. -/
theorem nonpos_back1 (hIH : IHyp t S n) {j : ℕ} (hj : j < n) (h4 : S (j + 4) ≤ 0)
    (h5 : 0 < S (j + 5)) : S (j + 3) ≤ 0 := by
  by_contra h
  push Not at h
  have := ((hIH j hj).1 h h4).2.1
  linarith

/-- Two nonpositive values followed (one step later) by a positive one. -/
theorem nonpos_back2 (hIH : IHyp t S n) {j : ℕ} (hj : j < n) (h4 : S (j + 4) ≤ 0)
    (h6 : 0 < S (j + 6)) : S (j + 3) ≤ 0 := by
  by_contra h
  push Not at h
  have := ((hIH j hj).1 h h4).2.2.1
  linarith

/-- Three nonpositive values followed by a positive one. -/
theorem nonpos_back3 (hIH : IHyp t S n) {j : ℕ} (hj : j < n) (h4 : S (j + 4) ≤ 0)
    (h7 : 0 < S (j + 7)) : S (j + 3) ≤ 0 := by
  by_contra h
  push Not at h
  have := ((hIH j hj).1 h h4).2.2.2.1
  linarith

/-- If `S 3 ≤ 0` then all of `S 0, …, S 3` are negative. -/
theorem start_neg (hstart : StartSign S) (h : S 3 ≤ 0) : ∀ j ≤ 3, S j < 0 := by
  rcases hstart with hp | hn
  · exact absurd h (not_le.mpr (hp 3 le_rfl))
  · exact hn

/-- **Below a run of positive values there are at least four nonpositive values.** -/
theorem four_nonpos (hstart : StartSign S) (hIH : IHyp t S n) {e : ℕ} (he : e < n)
    (h3 : S (e + 3) ≤ 0) (h4 : 0 < S (e + 4)) :
    S e ≤ 0 ∧ S (e + 1) ≤ 0 ∧ S (e + 2) ≤ 0 := by
  match e, he, h3, h4 with
  | 0, _, h3, h4 =>
      have hs := start_neg hstart h3
      exact ⟨(hs 0 (by lia)).le, (hs 1 (by lia)).le, (hs 2 (by lia)).le⟩
  | 1, he, h3, h4 =>
      have b1 : S 3 ≤ 0 := nonpos_back1 hIH (j := 0) (by lia) h3 h4
      have hs := start_neg hstart b1
      exact ⟨(hs 1 (by lia)).le, (hs 2 (by lia)).le, b1⟩
  | 2, he, h3, h4 =>
      have b1 : S 4 ≤ 0 := nonpos_back1 hIH (j := 1) (by lia) h3 h4
      have b2 : S 3 ≤ 0 := nonpos_back2 hIH (j := 0) (by lia) b1 h4
      have hs := start_neg hstart b2
      exact ⟨(hs 2 (by lia)).le, b2, b1⟩
  | (f + 3), he, h3, h4 =>
      have h3' : S (f + 6) ≤ 0 := by rw [show f + 6 = f + 3 + 3 from by lia]; exact h3
      have h4' : 0 < S (f + 7) := by rw [show f + 7 = f + 3 + 4 from by lia]; exact h4
      have b1 : S (f + 5) ≤ 0 := by
        have := nonpos_back1 hIH (j := f + 2) (by lia)
          (by rw [show f + 2 + 4 = f + 6 from by lia]; exact h3')
          (by rw [show f + 2 + 5 = f + 7 from by lia]; exact h4')
        rwa [show f + 2 + 3 = f + 5 from by lia] at this
      have b2 : S (f + 4) ≤ 0 := by
        have := nonpos_back2 hIH (j := f + 1) (by lia)
          (by rw [show f + 1 + 4 = f + 5 from by lia]; exact b1)
          (by rw [show f + 1 + 6 = f + 7 from by lia]; exact h4')
        rwa [show f + 1 + 3 = f + 4 from by lia] at this
      have b3 : S (f + 3) ≤ 0 := nonpos_back3 hIH (j := f) (by lia) b2 h4'
      refine ⟨b3, ?_, ?_⟩
      · rw [show f + 3 + 1 = f + 4 from by lia]; exact b2
      · rw [show f + 3 + 2 = f + 5 from by lia]; exact b1

/-- **The previous crossing.**  At the last nonpositive value `S (e+3)` before a run, the
inequality `t · S (e+1) < S (e+3)` holds: it is the crux at the previous (mirrored)
crossing when `S (e+3) < 0`, and follows from `S (e+1) < 0` when `S (e+3) = 0`. -/
theorem prev_strict (hstart : StartSign S) (hIH : IHyp t S n) (ht : 0 < t) {e : ℕ}
    (he : e < n) (h3 : S (e + 3) ≤ 0) (h4 : 0 < S (e + 4)) (h1 : S (e + 1) ≤ 0) :
    t * S (e + 1) < S (e + 3) := by
  rcases lt_or_eq_of_le h3 with hlt | hz
  · have hd := (hIH e he).2 (by simp only [Pi.neg_apply]; linarith)
      (by simp only [Pi.neg_apply]; linarith)
    have := hd.1
    simp only [Pi.neg_apply] at this
    linarith
  · -- `S (e+3) = 0`; we show `S (e+1) < 0`
    have h1' : S (e + 1) < 0 := by
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · exfalso
        rcases zero_next hstart hIH (c := e + 1) (by lia) h with ⟨-, hb, -⟩ | ⟨-, hb, -⟩ <;>
          rw [show e + 1 + 2 = e + 3 from by lia] at hb <;> linarith
    have : t * S (e + 1) < 0 := mul_neg_of_pos_of_neg ht h1'
    linarith

/-! ### The inductive step -/

/-- **The inductive step.**  Assuming the conclusion at all smaller indices (for `S` and for
`-S`), the initial-run hypothesis, and a common sign for the first four values, the
conclusion holds at `n`. -/
theorem downStep_step (hrec : ∀ k, S (k + 4) = S (k + 3) + S (k + 2) - t * S k)
    (ht : 1 < t) (hstart : StartSign S) (hinit : InitRun t S) (hIH : IHyp t S n) :
    DownStep t S n := by
  intro hpos hcross
  have ht0 : (0:ℝ) < t := by linarith
  have key : S (n + 3) < t * S (n + 1) ∧ 0 < S (n + 2) := by
    by_cases hall : ∀ j, 1 ≤ j → j ≤ n + 3 → 0 < S j
    · exact ⟨hinit n hpos hcross hall, hall (n + 2) (by lia) (by lia)⟩
    push Not at hall
    obtain ⟨j0, hj1, hj2, hj0⟩ := hall
    classical
    obtain ⟨d, hdP, hdle, hrun⟩ :
        ∃ d, S d ≤ 0 ∧ d ≤ n + 3 ∧ ∀ k, d < k → k ≤ n + 3 → 0 < S k := by
      refine ⟨Nat.findGreatest (fun j => S j ≤ 0) (n + 3), ?_, Nat.findGreatest_le _, ?_⟩
      · exact Nat.findGreatest_spec (P := fun j => S j ≤ 0) (m := j0) hj2 hj0
      · intro k hk1 hk2
        exact not_le.mp (Nat.findGreatest_is_greatest hk1 hk2)
    have hdlt : d < n + 3 := by
      rcases lt_or_eq_of_le hdle with h | h
      · exact h
      · exact absurd hdP (not_le.mpr (h ▸ hpos))
    have hd3 : 3 ≤ d := by
      by_contra hlt
      push Not at hlt
      have h1 : 0 < S (d + 1) := hrun (d + 1) (by lia) (by lia)
      rcases hstart with hp | hn
      · exact absurd hdP (not_le.mpr (hp d (by lia)))
      · exact absurd h1 (not_lt.mpr (hn (d + 1) (by lia)).le)
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by lia⟩
    have hen : e < n := by lia
    have hpos4 : 0 < S (e + 4) := hrun (e + 4) (by lia) (by lia)
    obtain ⟨hz0, hz1, hz2⟩ := four_nonpos hstart hIH hen hdP hpos4
    have hprev : t * S (e + 1) < S (e + 3) := prev_strict hstart hIH ht0 hen hdP hpos4 hz1
    obtain ⟨hp5, hp6, hp7⟩ := after_nonpos hstart hIH (c := e + 3) (by lia) hdP hpos4
    have hl4 : e + 4 ≤ n := by
      by_contra hlt
      push Not at hlt
      have hcases : n + 4 = e + 4 ∨ n + 4 = e + 5 ∨ n + 4 = e + 6 ∨ n + 4 = e + 7 := by lia
      rw [show e + 3 + 2 = e + 5 from by lia] at hp5
      rw [show e + 3 + 3 = e + 6 from by lia] at hp6
      rw [show e + 3 + 4 = e + 7 from by lia] at hp7
      rcases hcases with h | h | h | h <;> rw [h] at hcross <;> linarith
    refine ⟨?_, hrun (n + 2) (by lia) (by lia)⟩
    obtain ⟨l, hl⟩ : ∃ l, n = e + 4 + l := ⟨n - e - 4, by lia⟩
    rcases Nat.lt_or_ge l 9 with hl9 | hl9
    · interval_cases l
      -- run of length 4
      · rw [show n + 3 = e + 1 + 6 from by lia, show n + 1 = e + 1 + 4 from by lia]
        exact crux_of_prev hrec ht0
          (by rw [show e + 1 + 7 = n + 4 from by lia]; exact hcross)
          (hrun (e + 1 + 5) (by lia) (by lia))
          (by rw [show e + 1 + 2 = e + 3 from by lia]; exact hprev.le)
      -- run of length 5
      · rw [show n + 3 = e + 2 + 6 from by lia, show n + 1 = e + 2 + 4 from by lia]
        exact crux_of_short_run hrec ht
          (by rw [show e + 2 + 7 = n + 4 from by lia]; exact hcross)
          (hrun (e + 2 + 4) (by lia) (by lia))
          (hrun (e + 2 + 2) (by lia) (by lia)).le hz2
      -- run of length 6
      · rw [show n + 3 = e + 3 + 6 from by lia, show n + 1 = e + 3 + 4 from by lia]
        exact crux_of_short_run hrec ht
          (by rw [show e + 3 + 7 = n + 4 from by lia]; exact hcross)
          (hrun (e + 3 + 4) (by lia) (by lia))
          (hrun (e + 3 + 2) (by lia) (by lia)).le hdP
      -- run of length 7
      · rw [show n + 3 = e + 10 from by lia, show n + 1 = e + 8 from by lia]
        exact crux_cert_seven hrec ht.le e (hrun (e + 9) (by lia) (by lia)) hz2 hprev
          (by rw [show e + 11 = n + 4 from by lia]; exact hcross)
      -- run of length 8
      · rw [show n + 3 = e + 11 from by lia, show n + 1 = e + 9 from by lia]
        exact crux_cert_x hrec ht.le e (hrun (e + 11) (by lia) (by lia))
          (hrun (e + 7) (by lia) (by lia)) hz0
          (by rw [show e + 12 = n + 4 from by lia]; exact hcross)
      -- run of length 9
      · rw [show n + 3 = e + 1 + 11 from by lia, show n + 1 = e + 1 + 9 from by lia]
        exact crux_cert_x hrec ht.le (e + 1) (hrun (e + 1 + 11) (by lia) (by lia))
          (hrun (e + 1 + 7) (by lia) (by lia)) hz1
          (by rw [show e + 1 + 12 = n + 4 from by lia]; exact hcross)
      -- run of length 10
      · rw [show n + 3 = e + 2 + 11 from by lia, show n + 1 = e + 2 + 9 from by lia]
        exact crux_cert_x hrec ht.le (e + 2) (hrun (e + 2 + 11) (by lia) (by lia))
          (hrun (e + 2 + 7) (by lia) (by lia)) hz2
          (by rw [show e + 2 + 12 = n + 4 from by lia]; exact hcross)
      -- run of length 11
      · rw [show n + 3 = e + 3 + 11 from by lia, show n + 1 = e + 3 + 9 from by lia]
        exact crux_cert_x hrec ht.le (e + 3) (hrun (e + 3 + 11) (by lia) (by lia))
          (hrun (e + 3 + 7) (by lia) (by lia)) hdP
          (by rw [show e + 3 + 12 = n + 4 from by lia]; exact hcross)
      -- run of length 12
      · rw [show n + 3 = e + 2 + 13 from by lia, show n + 1 = e + 2 + 11 from by lia]
        exact crux_cert_y hrec ht.le (e + 2) (hrun (e + 2 + 12) (by lia) (by lia))
          (hrun (e + 2 + 3) (by lia) (by lia)) hz2
          (by rw [show e + 2 + 14 = n + 4 from by lia]; exact hcross)
    -- runs of length at least 13
    obtain ⟨s, rfl⟩ : ∃ s, l = 9 + s := ⟨l - 9, by lia⟩
    rw [show n + 3 = e + s + 4 + 12 from by lia, show n + 1 = e + s + 4 + 10 from by lia]
    exact crux_cert_z hrec ht.le (e + s + 4) (hrun (e + s + 4 + 11) (by lia) (by lia))
      (hrun (e + s + 4 + 2) (by lia) (by lia)) (hrun (e + s + 4) (by lia) (by lia))
      (by rw [show e + s + 4 + 13 = n + 4 from by lia]; exact hcross)
  exact ⟨key.1, next_neg hrec ht0 n hcross key.2 hpos key.1⟩

/-! ### The main induction -/

/-- **The structural theorem for the recurrence.**  For every sequence satisfying the
lag-four recurrence whose first four values have a common strict sign and whose initial
runs are under control, the crux inequality holds at every crossing, both for the sequence
and for its mirror image. -/
theorem downStep_all (hrec : ∀ k, S (k + 4) = S (k + 3) + S (k + 2) - t * S k) (ht : 1 < t)
    (hstart : StartSign S) (hinit : InitRun t S) (hinit' : InitRun t (-S)) :
    ∀ m, DownStep t S m ∧ DownStep t (-S) m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hIH : IHyp t S m := fun k hk => ih k hk
    exact ⟨downStep_step hrec ht hstart hinit hIH,
      downStep_step (neg_rec' hrec) ht hstart.neg hinit' hIH.neg⟩

end RealRooted.Applications.OEIS.A275442.Bridge
