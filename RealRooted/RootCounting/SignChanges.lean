import RealRooted.MaWang
import Mathlib.Analysis.Polynomial.Basic

/-!
# Splitness from sign changes

Criteria proving that a real polynomial splits from alternating signs at an
ordered family of test points.
-/

open Polynomial
open Filter Asymptotics

noncomputable section

namespace RealRooted

theorem splits_of_strict_sign_changes {p : ℝ[X]} {rs : List ℝ}
    (hp : p ≠ 0)
    (hrs : rs.Pairwise (· < ·))
    (hlen : rs.length = p.natDegree + 1)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        p.eval r₁ * p.eval r₂ < 0) :
    p.Splits := by
  have hrs_weak : rs.Pairwise (· ≤ ·) :=
    hrs.imp fun h => le_of_lt h
  obtain ⟨us, hus_len, _, hus_roots, hus_strict⟩ :=
    RealRooted.exists_roots_strictly_interlacing_of_consecutive_signs
      (F := p) hrs_weak hsign
  have hus_nodup : us.Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hus_strict.imp fun h => ne_of_lt h
  have hus_sub : (↑us : Multiset ℝ) ≤ p.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hus_nodup)]
    intro r hr
    simp_all
  apply RealRooted.splits_of_card_roots
  apply le_antisymm (card_roots' p)
  calc
    p.natDegree = us.length := by lia
    _ = (↑us : Multiset ℝ).card := (Multiset.coe_card us).symm
    _ ≤ p.roots.card := Multiset.card_le_card hus_sub

/-- Finite-index form of `splits_of_strict_sign_changes`. -/
theorem splits_of_strict_sign_changes_fin {p : ℝ[X]} {d : ℕ}
    (hp : p ≠ 0)
    (hdegree : p.natDegree = d)
    (r : Fin (d + 1) → ℝ)
    (hr : ∀ i j, i < j → r i < r j)
    (hsign :
      ∀ i : Fin d,
        p.eval (r i.castSucc) * p.eval (r i.succ) < 0) :
    p.Splits := by
  apply splits_of_strict_sign_changes (p := p) (rs := List.ofFn r) hp
  · simp_all
  · simp [hdegree]
  · intro pre r₁ r₂ rest heq
    have hlength := congrArg List.length heq
    simp only [List.length_ofFn, List.length_append, List.length_cons] at hlength
    have hi : pre.length < d := by lia
    let i : Fin d := ⟨pre.length, hi⟩
    have hi₁ : pre.length < d + 1 := by lia
    have hi₂ : pre.length + 1 < d + 1 := by lia
    have hget₁ := congrArg (fun l : List ℝ => l[pre.length]?) heq
    have hget₂ := congrArg (fun l : List ℝ => l[pre.length + 1]?) heq
    simp only [List.getElem?_ofFn, hi₁] at hget₁
    simp only [List.getElem?_ofFn, hi₂] at hget₂
    simp at hget₁ hget₂
    have hs := hsign i
    have hfin₁ : (⟨pre.length, hi₁⟩ : Fin (d + 1)) = i.castSucc := by grind
    grind

/-- A positive-leading degree-`d` polynomial has the sign `(-1)^d`
sufficiently far to the left. -/
theorem exists_left_endpoint_sign {p : ℝ[X]} {d : ℕ}
    (hdeg : p.natDegree = d) (hlc : 0 < p.leadingCoeff)
    (a : ℝ) :
    ∃ R < a, 0 < (-1 : ℝ) ^ d * p.eval R := by
  have heq := p.isEquivalent_atBot_lead
  rcases Nat.even_or_odd d with heven | hodd
  · have hlead :
        ∀ᶠ x : ℝ in atBot, 0 < p.leadingCoeff * x ^ p.natDegree := by
      filter_upwards [eventually_lt_atBot 0] with x hx
      rw [hdeg]
      exact mul_pos hlc (heven.pow_pos (ne_of_lt hx))
    have hp : ∀ᶠ x : ℝ in atBot, 0 < p.eval x :=
      heq.eventually_pos hlead
    have hboth : ∀ᶠ x : ℝ in atBot, x < a ∧ 0 < p.eval x :=
      (eventually_lt_atBot a).and hp
    obtain ⟨R, hRa, hR⟩ := hboth.exists
    refine ⟨R, hRa, ?_⟩
    simp_all
  · have hlead :
        ∀ᶠ x : ℝ in atBot, p.leadingCoeff * x ^ p.natDegree < 0 := by
      filter_upwards [eventually_lt_atBot 0] with x hx
      rw [hdeg]
      exact mul_neg_of_pos_of_neg hlc (hodd.pow_neg hx)
    have hp : ∀ᶠ x : ℝ in atBot, p.eval x < 0 :=
      heq.eventually_neg hlead
    have hboth : ∀ᶠ x : ℝ in atBot, x < a ∧ p.eval x < 0 :=
      (eventually_lt_atBot a).and hp
    obtain ⟨R, hRa, hR⟩ := hboth.exists
    refine ⟨R, hRa, ?_⟩
    simp_all

/-- A degree-`d` positive-leading polynomial splits if it strictly alternates
at `d` increasing finite points and the first finite value has the sign
opposite to its far-left leading-term sign.  The missing far-left test point
is supplied by `exists_left_endpoint_sign`. -/
theorem splits_of_sign_changes_with_left_endpoint {p : ℝ[X]} {d : ℕ}
    (hd : 0 < d) (hp : p ≠ 0) (hdegree : p.natDegree = d)
    (hlc : 0 < p.leadingCoeff)
    (r : Fin d → ℝ)
    (hr : ∀ i j, i < j → r i < r j)
    (hfirst : (-1 : ℝ) ^ d * p.eval (r ⟨0, hd⟩) < 0)
    (hsign : ∀ (k : ℕ) (hk : k + 1 < d),
      p.eval (r ⟨k, by lia⟩) *
        p.eval (r ⟨k + 1, hk⟩) < 0) :
    p.Splits := by
  obtain ⟨R, hRlt, hRsign⟩ :=
    exists_left_endpoint_sign hdegree hlc (r ⟨0, hd⟩)
  let q : Fin (d + 1) → ℝ := Fin.cases R r
  have hq0 (i : Fin (d + 1)) (hi : i.1 = 0) : q i = R := by
    have : i = 0 := Fin.ext hi
    subst i
    simp [q]
  have hqpos (i : Fin (d + 1)) (hi : 0 < i.1) :
      q i = r ⟨i.1 - 1, by lia⟩ := by
    cases i using Fin.cases with
    | zero => simp at hi
    | succ k =>
        simp [q]
  have hqsucc (i : Fin d) : q i.succ = r i := by simp [q]
  apply splits_of_strict_sign_changes_fin hp hdegree q
  · intro i j hij
    by_cases hi : i.1 = 0
    · rw [hq0 i hi, hqpos j (by lia)]
      by_cases hj : j.1 = 1
      · have heq :
            (⟨j.1 - 1, by lia⟩ : Fin d) = ⟨0, hd⟩ := by
          ext
          simp
          lia
        rwa [heq]
      · apply hRlt.trans
          (hr ⟨0, hd⟩ ⟨j.1 - 1, by lia⟩ ?_)
        simp
        lia
    · rw [hqpos i (Nat.pos_of_ne_zero hi), hqpos j (by lia)]
      apply hr
      simp
      lia
  · intro i
    by_cases hi : i.1 = 0
    · have hi0 : i = ⟨0, hd⟩ := Fin.ext hi
      subst i
      rw [hq0 (⟨0, hd⟩ : Fin d).castSucc rfl, hqsucc]
      have hs : ((-1 : ℝ) ^ d) ^ 2 = 1 := by
        rw [← pow_mul]
        simp
      have hprod := mul_pos hRsign (neg_pos.mpr hfirst)
      have hss : (-1 : ℝ) ^ d * (-1 : ℝ) ^ d = 1 := by
        simpa [pow_two] using hs
      have heq :
          ((-1 : ℝ) ^ d * p.eval R) *
              (-((-1 : ℝ) ^ d * p.eval (r ⟨0, hd⟩))) =
            -(p.eval R * p.eval (r ⟨0, hd⟩)) := by
        calc
          _ = -(((-1 : ℝ) ^ d * (-1 : ℝ) ^ d) *
              (p.eval R * p.eval (r ⟨0, hd⟩))) := by ring
          _ = _ := by rw [hss]; ring
      rw [heq] at hprod
      nlinarith
    · rw [hqpos i.castSucc (Nat.pos_of_ne_zero hi), hqsucc]
      simpa only [Fin.val_castSucc,
        Nat.sub_add_cancel (Nat.pos_of_ne_zero hi)] using
        hsign (i.1 - 1) (by lia)


end RealRooted
