import RealRooted.RootAmplitude.Separation.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.ZetaValues

/-!
# Euler-product bounds for separated amplitudes

The finite separation algebra reduces an amplitude to two copies of a
geometric staircase product.  This file supplies the real-analytic uniform
lower bound for that product using the Basel sum.  Keeping this dependency in
one leaf prevents elementary separation clients from importing zeta theory.
-/

namespace RealRooted.RootAmplitude

open Finset

noncomputable section

private theorem hasSum_range_sum (N : ℕ) {f : ℕ → ℕ → ℝ} {a : ℕ → ℝ}
    (h : ∀ j, HasSum (f j) (a j)) :
    HasSum (fun l => ∑ j ∈ range N, f j l) (∑ j ∈ range N, a j) := by
  induction N with
  | zero => simp
  | succ m ih =>
      simpa [Finset.sum_range_succ] using ih.add (h m)

private theorem hasSum_inv_sq :
    HasSum (fun l : ℕ => 1 / ((l : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (_root_.hasSum_nat_add_iff
    (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr
      (by simpa using hasSum_zeta_two)
  refine h.congr_fun ?_
  intro l
  push_cast
  ring_nf

private theorem summable_inv_sq :
    Summable (fun l : ℕ => 1 / ((l : ℝ) + 1) ^ 2) :=
  hasSum_inv_sq.summable

private theorem tsum_inv_sq :
    ∑' l : ℕ, 1 / ((l : ℝ) + 1) ^ 2 = Real.pi ^ 2 / 6 :=
  hasSum_inv_sq.tsum_eq

private theorem geom_partial_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ j ∈ range N, r ^ (j + 1) ≤ r / (1 - r) := by
  have hden : (0 : ℝ) < 1 - r := by linarith
  have hgeom : (∑ j ∈ range N, r ^ j) * (1 - r) = 1 - r ^ N := by
    linear_combination -geom_sum_mul r N
  have hsum : ∑ j ∈ range N, r ^ j ≤ 1 / (1 - r) := by
    rw [le_div_iff₀ hden, hgeom]
    exact sub_le_self 1 (pow_nonneg hr0 N)
  have hfactor : ∑ j ∈ range N, r ^ (j + 1) = r * ∑ j ∈ range N, r ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hfactor, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left hsum hr0

private theorem exp_neg_div_le {T : ℝ} (hT : 0 < T) :
    Real.exp (-T) / (1 - Real.exp (-T)) ≤ 1 / T := by
  have hr0 : (0 : ℝ) < Real.exp (-T) := Real.exp_pos _
  have hr1 : Real.exp (-T) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : (0 : ℝ) < 1 - Real.exp (-T) := by linarith
  have hinv : Real.exp (-T) * Real.exp T = 1 := by
    rw [← Real.exp_add]
    simp
  have hexp : T + 1 ≤ Real.exp T := Real.add_one_le_exp T
  rw [div_le_div_iff₀ hden hT]
  nlinarith

private theorem inner_sum_le {d : ℝ} (hd : 0 < d) (N l : ℕ) :
    ∑ j ∈ range N, Real.exp (-((j + 1 : ℕ) * d)) ^ (l + 1) / ((l : ℝ) + 1)
      ≤ 1 / (((l : ℝ) + 1) ^ 2 * d) := by
  set r : ℝ := Real.exp (-((l + 1 : ℕ) * d)) with hr
  have hT : (0 : ℝ) < ((l : ℝ) + 1) * d := by positivity
  have hswap : ∀ j : ℕ,
      Real.exp (-((j + 1 : ℕ) * d)) ^ (l + 1) = r ^ (j + 1) := by
    intro j
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsum :
      ∑ j ∈ range N, Real.exp (-((j + 1 : ℕ) * d)) ^ (l + 1) / ((l : ℝ) + 1)
        = (∑ j ∈ range N, r ^ (j + 1)) / ((l : ℝ) + 1) := by
    rw [div_eq_mul_inv, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by rw [hswap j, div_eq_mul_inv])
  have hr0 : (0 : ℝ) < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.exp_lt_one_iff.mpr (by
      push_cast
      nlinarith [hd, Nat.cast_nonneg (α := ℝ) l])
  have hgeo : ∑ j ∈ range N, r ^ (j + 1) ≤ r / (1 - r) :=
    geom_partial_le hr0.le hr1 N
  have hrT : r / (1 - r) ≤ 1 / (((l : ℝ) + 1) * d) := by
    have hcast : r = Real.exp (-(((l : ℝ) + 1) * d)) := by
      rw [hr]
      push_cast
      ring_nf
    rw [hcast]
    exact exp_neg_div_le hT
  have hl : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  rw [hsum, div_le_div_iff₀ hl (by positivity)]
  have hchain : ∑ j ∈ range N, r ^ (j + 1) ≤ 1 / (((l : ℝ) + 1) * d) :=
    le_trans hgeo hrT
  rw [le_div_iff₀ hT] at hchain
  nlinarith

private theorem sum_neg_log_le {d : ℝ} (hd : 0 < d) (N : ℕ) :
    ∑ j ∈ range N, -Real.log (1 - Real.exp (-((j + 1 : ℕ) * d)))
      ≤ Real.pi ^ 2 / 6 / d := by
  have habs : ∀ j : ℕ, |Real.exp (-((j + 1 : ℕ) * d))| < 1 := by
    intro j
    rw [abs_of_pos (Real.exp_pos _)]
    refine Real.exp_lt_one_iff.mpr ?_
    have hpositive : (0 : ℝ) < ((j : ℝ) + 1) * d := by positivity
    push_cast
    linarith
  have hseries : ∀ j : ℕ,
      HasSum
        (fun l : ℕ => Real.exp (-((j + 1 : ℕ) * d)) ^ (l + 1) / ((l : ℝ) + 1))
        (-Real.log (1 - Real.exp (-((j + 1 : ℕ) * d)))) := by
    intro j
    simpa using Real.hasSum_pow_div_log_of_abs_lt_one (habs j)
  have hleft := hasSum_range_sum N hseries
  have hsummable : Summable (fun l : ℕ => 1 / (((l : ℝ) + 1) ^ 2 * d)) := by
    have h := summable_inv_sq.div_const d
    refine h.congr ?_
    intro l
    rw [div_div]
  have hcompare := hasSum_le (fun l => inner_sum_le hd N l) hleft hsummable.hasSum
  have hvalue : ∑' l : ℕ, 1 / (((l : ℝ) + 1) ^ 2 * d) = Real.pi ^ 2 / 6 / d := by
    rw [show (fun l : ℕ => 1 / (((l : ℝ) + 1) ^ 2 * d))
        = (fun l : ℕ => 1 / ((l : ℝ) + 1) ^ 2 / d) from
          funext (fun l => by rw [div_div]),
      tsum_div_const, tsum_inv_sq]
  linarith

/-- The Euler staircase product has a positive lower bound independent of its
finite length. -/
theorem exp_neg_pi_sq_div_six_le_staircaseProd {d : ℝ} (hd : 0 < d) (N : ℕ) :
    Real.exp (-(Real.pi ^ 2 / 6 / d))
      ≤ staircaseProd (Real.exp d) N := by
  have hfactor : ∀ j ∈ range N,
      (0 : ℝ) < 1 - Real.exp (-((j + 1 : ℕ) * d)) := by
    intro j _
    have hlt : Real.exp (-((j + 1 : ℕ) * d)) < 1 := by
      refine Real.exp_lt_one_iff.mpr ?_
      have hpositive : (0 : ℝ) < ((j : ℝ) + 1) * d := by positivity
      push_cast
      linarith
    linarith
  have hproduct : (0 : ℝ) <
      ∏ j ∈ range N, (1 - Real.exp (-((j + 1 : ℕ) * d))) :=
    Finset.prod_pos hfactor
  have hlog :
      Real.log (∏ j ∈ range N, (1 - Real.exp (-((j + 1 : ℕ) * d))))
        = ∑ j ∈ range N, Real.log (1 - Real.exp (-((j + 1 : ℕ) * d))) :=
    Real.log_prod (fun j hj => ne_of_gt (hfactor j hj))
  have hsum := sum_neg_log_le hd N
  rw [Finset.sum_neg_distrib] at hsum
  have hlower :
      -(Real.pi ^ 2 / 6 / d)
        ≤ Real.log (∏ j ∈ range N, (1 - Real.exp (-((j + 1 : ℕ) * d)))) := by
    rw [hlog]
    linarith
  have hrewrite : staircaseProd (Real.exp d) N
      = ∏ j ∈ range N, (1 - Real.exp (-((j + 1 : ℕ) * d))) := by
    unfold staircaseProd
    refine Finset.prod_congr rfl ?_
    intro j _
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
  rw [hrewrite]
  calc
    Real.exp (-(Real.pi ^ 2 / 6 / d))
        ≤ Real.exp
            (Real.log (∏ j ∈ range N, (1 - Real.exp (-((j + 1 : ℕ) * d))))) :=
      Real.exp_le_exp.mpr hlower
    _ = ∏ j ∈ range N, (1 - Real.exp (-((j + 1 : ℕ) * d))) :=
      Real.exp_log hproduct

/-- A finite exponentially separated positive sequence has the full
index-dependent Euler lower bound on every amplitude. -/
theorem exp_gain_le_amp_of_separation {g : ℕ → ℝ} {n : ℕ} {d : ℝ}
    (hd : 0 < d) (hpos : ∀ i, i < n → 0 < g i)
    (hsep : IsMultiplicativelySeparatedOn (Real.exp d) g n)
    {k : ℕ} (hk : k < n) :
    Real.exp (d * (k * (k + 1) / 2) - Real.pi ^ 2 / (3 * d))
      ≤ amp g n k := by
  have hq : (1 : ℝ) ≤ Real.exp d := (Real.one_lt_exp_iff.mpr hd).le
  have hstrict := hsep.strictMonoOnRange (Real.one_lt_exp_iff.mpr hd) hpos
  rw [amp_eq_lower_mul_upper g n k hk hpos hstrict]
  set L : ℝ := Real.exp (-(Real.pi ^ 2 / 6 / d)) with hL
  have hLpos : 0 < L := Real.exp_pos _
  have hLk : L ≤ staircaseProd (Real.exp d) k :=
    exp_neg_pi_sq_div_six_le_staircaseProd hd k
  have hLN : L ≤ staircaseProd (Real.exp d) (n - k - 1) :=
    exp_neg_pi_sq_div_six_le_staircaseProd hd (n - k - 1)
  have hbelowCompare := staircaseProd_below hq hpos hsep hk
  rw [prod_sub_one_eq_staircaseProd (Real.exp_ne_zero d) k] at hbelowCompare
  have hgainPos : (0 : ℝ) < Real.exp d ^ (k * (k + 1) / 2) := by positivity
  have hbelow : Real.exp d ^ (k * (k + 1) / 2) * L
      ≤ ∏ i ∈ range k, (g k / g i - 1) :=
    le_trans (mul_le_mul_of_nonneg_left hLk hgainPos.le) hbelowCompare
  have habove : L
      ≤ ∏ j ∈ range (n - k - 1), (1 - g k / g (k + 1 + j)) :=
    le_trans hLN (staircaseProd_above hq hpos hsep (by lia))
  have hproduct := mul_le_mul hbelow habove hLpos.le
    (le_trans (mul_pos hgainPos hLpos).le hbelow)
  have hcollect :
      (Real.exp d ^ (k * (k + 1) / 2) * L) * L
        = Real.exp (d * (k * (k + 1) / 2) - Real.pi ^ 2 / (3 * d)) := by
    have htri : (((k * (k + 1) / 2 : ℕ) : ℝ))
        = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
      rw [Nat.cast_div
        (Nat.even_mul_succ_self k).two_dvd (by norm_num)]
      push_cast
      rfl
    rw [hL, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    rw [htri]
    congr 1
    field_simp
    ring
  rwa [hcollect] at hproduct

/-- The index-free amplitude bound obtained by discarding the nonnegative
triangular gain. -/
theorem exp_neg_pi_sq_div_three_le_amp_of_separation
    {g : ℕ → ℝ} {n : ℕ} {d : ℝ}
    (hd : 0 < d) (hpos : ∀ i, i < n → 0 < g i)
    (hsep : IsMultiplicativelySeparatedOn (Real.exp d) g n)
    {k : ℕ} (hk : k < n) :
    Real.exp (-(Real.pi ^ 2 / (3 * d))) ≤ amp g n k := by
  refine le_trans ?_ (exp_gain_le_amp_of_separation hd hpos hsep hk)
  apply Real.exp_le_exp.mpr
  have hnonnegative :
      (0 : ℝ) ≤ d * (k * (k + 1) / 2) := by positivity
  linarith

end


end RealRooted.RootAmplitude
