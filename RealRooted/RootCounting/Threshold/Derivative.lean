import RealRooted.RootAmplitude.Polynomial
import RealRooted.RootCounting.Threshold.Sorted

/-!
# Derivative signs at ordered negative roots

The thresholded count controls the sign of the normalized derivative at each
simple negative root.
-/

namespace RealRooted.RootCounting

open Polynomial
open SortedRoots

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The normalized root-amplitude product has the sign of its thresholded count. -/
theorem prod_amp_sign {m : Multiset K} {ξ : K} (hm : ∀ r ∈ m, r < 0)
    (hne : ∀ r ∈ m, r ≠ ξ) :
    0 < (-1 : K) ^ (Multiset.card (m.filter (fun r => ξ < r)))
      * (m.map (fun r => 1 - ξ / r)).prod := by
  classical
  induction m using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      have hta : ∀ r ∈ t, r < 0 := fun r hr => hm r (Multiset.mem_cons_of_mem hr)
      have hnet : ∀ r ∈ t, r ≠ ξ := fun r hr => hne r (Multiset.mem_cons_of_mem hr)
      have haneg : a < 0 := hm a (Multiset.mem_cons_self a t)
      have hane : a ≠ ξ := hne a (Multiset.mem_cons_self a t)
      have hIH := ih hta hnet
      have hane0 : a ≠ 0 := ne_of_lt haneg
      have hid : ξ / a - 1 = (ξ - a) / a := by
        field_simp
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.filter_cons]
      by_cases hlt : ξ < a
      · rw [if_pos hlt, Multiset.card_add, Multiset.card_singleton]
        have hq : (0 : K) < (ξ - a) / a := div_pos_of_neg_of_neg (by linarith) haneg
        have hfac : 1 - ξ / a < 0 := by linarith [hid, hq]
        have hpow : (-1 : K) ^ (1 + Multiset.card (t.filter (fun r => ξ < r)))
            = -((-1 : K) ^ (Multiset.card (t.filter (fun r => ξ < r)))) := by
          rw [pow_add, pow_one]
          ring
        rw [hpow]
        nlinarith [hIH, hfac]
      · rw [if_neg hlt]
        simp only [zero_add]
        have halt : a < ξ := lt_of_le_of_ne (not_lt.mp hlt) hane
        have hq : (ξ - a) / a < 0 := div_neg_of_pos_of_neg (by linarith) haneg
        have hfac : (0 : K) < 1 - ξ / a := by linarith [hid, hq]
        nlinarith [hIH, hfac]

/-- Filtering after erasing an element that fails the predicate changes nothing. -/
theorem filter_erase_eq {α : Type*} {m : Multiset α} {a : α} {P : α → Prop}
    [DecidableEq α] [DecidablePred P] (hPa : ¬ P a) :
    (m.erase a).filter P = m.filter P := by
  classical
  refine Multiset.ext.mpr (fun x => ?_)
  rw [Multiset.count_filter, Multiset.count_filter]
  by_cases hx : P x
  · rw [if_pos hx, if_pos hx]
    have hxa : x ≠ a := fun h => hPa (h ▸ hx)
    exact Multiset.count_erase_of_ne hxa m
  · rw [if_neg hx, if_neg hx]

/-- The derivative at the `k`-th smallest negative root has sign `(-1)^k`. -/
theorem deriv_sign_at_root {p : ℝ[X]} (hp : p.Splits) (hnd : p.roots.Nodup)
    (h0 : 0 < p.eval 0) (hneg : ∀ ξ ∈ p.roots, ξ < 0)
    (hlt : ∀ i j, i < j → j < (rootMags p).length → rootSeq p i < rootSeq p j)
    {k : ℕ} (hk : k < (rootMags p).length) :
    0 < (-1 : ℝ) ^ k * p.derivative.eval (-(rootSeq p k)) := by
  classical
  have hmem : -(rootSeq p k) ∈ p.roots := rootSeq_mem p hk
  have hsneg : -(rootSeq p k) < 0 := hneg _ hmem
  have hcount : p.roots.count (-(rootSeq p k)) = 1 :=
    Multiset.count_eq_one_of_mem hnd hmem
  have hval := RootAmplitude.eval_deriv_root_div_eval_zero hp hmem hcount (ne_of_gt h0)
  have hmneg : ∀ r ∈ p.roots.erase (-(rootSeq p k)), r < 0 := fun r hr =>
    hneg r (Multiset.mem_of_mem_erase hr)
  have hmne : ∀ r ∈ p.roots.erase (-(rootSeq p k)), r ≠ -(rootSeq p k) := by
    intro r hr heq
    rw [heq] at hr
    have hc := Multiset.count_erase_self (-(rootSeq p k)) p.roots
    have hpos : 0 < Multiset.count (-(rootSeq p k))
        (p.roots.erase (-(rootSeq p k))) := Multiset.count_pos.mpr hr
    lia
  have hsgn := prod_amp_sign hmneg hmne
  have hfil : (p.roots.erase (-(rootSeq p k))).filter (fun r => -(rootSeq p k) < r)
      = p.roots.filter (fun r => -(rootSeq p k) < r) :=
    filter_erase_eq (m := p.roots) (a := -(rootSeq p k))
      (P := fun r : ℝ => -(rootSeq p k) < r) (lt_irrefl _)
  rw [hfil] at hsgn
  have hcard : Multiset.card
      (p.roots.filter (fun r => -(rootSeq p k) < r)) = k := by
    have h := card_at_rootSeq (p := p) hlt hk
    rw [rootsAbove] at h
    exact h
  rw [hcard] at hsgn
  have hkey : (-(rootSeq p k)) * p.derivative.eval (-(rootSeq p k))
      = -(((p.roots.erase (-(rootSeq p k))).map (fun r => 1 - (-(rootSeq p k)) / r)).prod)
        * p.eval 0 :=
    (div_eq_iff (ne_of_gt h0)).mp hval
  have hlt0 : (-1 : ℝ) ^ k * ((-(rootSeq p k)) * p.derivative.eval
      (-(rootSeq p k))) < 0 := by
    rw [hkey]
    nlinarith [hsgn, h0]
  by_contra hcon
  push Not at hcon
  nlinarith [hlt0, hsneg, hcon,
    mul_nonneg (neg_nonneg.mpr hsneg.le) (neg_nonneg.mpr hcon)]

end RealRooted.RootCounting
