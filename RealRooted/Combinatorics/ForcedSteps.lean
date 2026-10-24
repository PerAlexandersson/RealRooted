import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
Aristotle project `c46dc43c-0f1b-436e-852d-810faecd9567`, adapted locally.

# Stars and bars with forced strict steps

The number of weakly increasing maps `f : Fin n → Fin N` that increase strictly at every
position of a prescribed set `S` of adjacent steps is `C(N + n - 1 - |S|, n)`.
-/

open Finset

namespace RealRooted.FiniteWords

theorem monotone_iff_adj {n : ℕ} {α : Type*} [Preorder α] (f : Fin n → α) :
    Monotone f ↔ ∀ (i : Fin n) (h : i.val + 1 < n), f i ≤ f ⟨i.val + 1, h⟩ := by
  rcases n with _ | m
  · exact ⟨fun _ i => i.elim0, fun _ i => i.elim0⟩
  rw [Fin.monotone_iff_le_succ]
  constructor
  · intro h i hi
    have := h ⟨i.val, by lia⟩
    simpa [Fin.castSucc, Fin.succ] using this
  · intro h i
    have := h i.castSucc (by simp)
    simpa [Fin.castSucc, Fin.succ] using this

theorem strictMono_iff_adj {n : ℕ} {α : Type*} [Preorder α] (f : Fin n → α) :
    StrictMono f ↔ ∀ (i : Fin n) (h : i.val + 1 < n), f i < f ⟨i.val + 1, h⟩ := by
  rcases n with _ | m
  · exact ⟨fun _ i => i.elim0, fun _ i => i.elim0⟩
  rw [Fin.strictMono_iff_lt_succ]
  constructor
  · intro h i hi
    have := h ⟨i.val, by lia⟩
    simpa [Fin.castSucc, Fin.succ] using this
  · intro h i
    have := h i.castSucc (by simp)
    simpa [Fin.castSucc, Fin.succ] using this

/-- Number of strictly increasing maps `Fin n → Fin M`. -/
theorem card_strictMono (n M : ℕ) :
    (univ.filter (fun g : Fin n → Fin M => StrictMono g)).card = M.choose n := by
  have hM : M.choose n = (powersetCard n (univ : Finset (Fin M))).card := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]
  rw [hM]
  refine Finset.card_bij (fun g _ => univ.image g) ?_ ?_ ?_
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg
    simp [mem_powersetCard, card_image_of_injective _ hg.injective]
  · intro g1 h1 g2 h2 heq
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    have hc : (univ.image g1).card = n := by
      simp [card_image_of_injective _ h1.injective]
    have e1 := Finset.orderEmbOfFin_unique hc (f := g1) (by simp) h1
    have e2 := Finset.orderEmbOfFin_unique hc (f := g2) (by intro x; rw [heq]; simp) h2
    rw [e1, e2]
  · intro s hs
    rw [mem_powersetCard] at hs
    refine ⟨fun i => s.orderEmbOfFin hs.2 i, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      exact (s.orderEmbOfFin hs.2).strictMono
    · ext x
      simp only [mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩; exact s.orderEmbOfFin_mem hs.2 i
      · intro hx
        have := Finset.range_orderEmbOfFin s hs.2
        have hx' : x ∈ Set.range (s.orderEmbOfFin hs.2) := by rw [this]; exact hx
        obtain ⟨i, hi⟩ := hx'
        exact ⟨i, hi⟩

/-- Number of elements of `S` strictly before `i`. -/
def ecount {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℕ := (S.filter (fun j => j < i)).card

theorem ecount_succ {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (h : i.val + 1 < n) :
    ecount S ⟨i.val + 1, h⟩ = ecount S i + if i ∈ S then 1 else 0 := by
  unfold ecount
  split_ifs with hi
  · rw [← card_insert_of_notMem (s := S.filter (fun j => j < i)) (a := i) (by simp)]
    congr 1
    ext j
    simp only [mem_filter, mem_insert, Fin.lt_def]
    constructor
    · rintro ⟨hj, hj'⟩
      by_cases hji : j = i
      · exact Or.inl hji
      · exact Or.inr ⟨hj, by have := Fin.val_ne_of_ne hji; lia⟩
    · rintro (rfl | ⟨hj, hj'⟩)
      · exact ⟨hi, by lia⟩
      · exact ⟨hj, by lia⟩
  · rw [add_zero]
    congr 1
    ext j
    simp only [mem_filter, Fin.lt_def]
    constructor
    · rintro ⟨hj, hj'⟩
      refine ⟨hj, ?_⟩
      by_contra hc
      have : j = i := Fin.ext (by lia)
      exact hi (this ▸ hj)
    · rintro ⟨hj, hj'⟩; exact ⟨hj, by lia⟩

theorem ecount_le {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ecount S i ≤ i.val := by
  unfold ecount
  calc (S.filter (fun j => j < i)).card ≤ (Iio i).card :=
        card_le_card (fun j hj => by simp only [mem_filter] at hj; simpa using hj.2)
    _ = i.val := Fin.card_Iio i

theorem ecount_le_card {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ecount S i ≤ S.card :=
  card_filter_le _ _

theorem card_le_ecount {n : ℕ} (S : Finset (Fin n)) (hS : ∀ j ∈ S, j.val + 1 < n) (i : Fin n) :
    S.card ≤ ecount S i + (n - 1 - i.val) := by
  unfold ecount
  rw [← card_filter_add_card_filter_not (s := S) (p := fun j => j < i)]
  gcongr
  calc (S.filter (fun j => ¬ j < i)).card
      ≤ (Finset.Ico i.val (n - 1)).card := by
        apply card_le_card_of_injOn (fun j => j.val)
        · intro j hj
          simp only [coe_filter, Set.mem_ofPred_eq, not_lt] at hj
          have := hS j hj.1
          simp only [coe_Ico, Set.mem_Ico]
          exact ⟨hj.2, by lia⟩
        · intro a _ b _ hab; exact Fin.ext hab
    _ = n - 1 - i.val := Nat.card_Ico _ _

theorem strictMono_gap {n M : ℕ} (g : Fin n → Fin M) (hg : StrictMono g) :
    ∀ k (i : Fin n) (h : i.val + k < n), (g i).val + k ≤ (g ⟨i.val + k, h⟩).val := by
  intro k
  induction k with
  | zero => intro i h; simp
  | succ k ih =>
    intro i h
    have h1 := ih i (by lia)
    have h2 : g ⟨i.val + k, by lia⟩ < g ⟨i.val + (k + 1), h⟩ :=
      hg (Fin.mk_lt_mk.2 (by lia))
    rw [Fin.lt_def] at h2
    lia

theorem strictMono_bounds {n M : ℕ} (g : Fin n → Fin M) (hg : StrictMono g) (i : Fin n) :
    i.val ≤ (g i).val ∧ (g i).val + (n - 1 - i.val) < M := by
  constructor
  · have := strictMono_gap g hg i.val ⟨0, by have := i.isLt; lia⟩ (by simp)
    simp only [zero_add, Fin.eta] at this
    lia
  · have := strictMono_gap g hg (n - 1 - i.val) i (by lia)
    have := (g ⟨i.val + (n - 1 - i.val), by lia⟩).isLt
    lia

/-- Stars and bars with forced strict steps. -/
theorem card_compat {n : ℕ} (N : ℕ) (S : Finset (Fin n)) (hS : ∀ j ∈ S, j.val + 1 < n) :
    (univ.filter (fun f : Fin n → Fin N => Monotone f ∧
        ∀ i ∈ S, ∀ h : i.val + 1 < n, f i < f ⟨i.val + 1, h⟩)).card
      = (N + n - 1 - S.card).choose n := by
  rw [← card_strictMono]
  refine Finset.card_bij'
    (fun f hf => fun i => ⟨(f i).val + i.val - ecount S i, by
      have := card_le_ecount S hS i
      have := ecount_le S i
      have := (f i).isLt
      have := i.isLt
      lia⟩)
    (fun g hg => fun i => ⟨(g i).val + ecount S i - i.val, by
      simp only [mem_filter, mem_univ, true_and] at hg
      have := strictMono_bounds g hg i
      have := ecount_le_card S i
      lia⟩) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf ⊢
    rw [strictMono_iff_adj]
    intro i h
    rw [Fin.mk_lt_mk]
    have hm := (monotone_iff_adj f).1 hf.1 i h
    rw [Fin.le_def] at hm
    have h1 := ecount_succ S i h
    have h2 := ecount_le S i
    split_ifs at h1 with hi
    · have := hf.2 i hi h
      rw [Fin.lt_def] at this
      lia
    · lia
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg ⊢
    have hadj := (strictMono_iff_adj g).1 hg
    refine ⟨(monotone_iff_adj _).2 fun i h => ?_, fun i hi h => ?_⟩
    · rw [Fin.mk_le_mk]
      have := hadj i h
      rw [Fin.lt_def] at this
      have h1 := ecount_succ S i h
      have h2 := (strictMono_bounds g hg i).1
      split_ifs at h1 <;> simp only <;> lia
    · rw [Fin.mk_lt_mk]
      have := hadj i h
      rw [Fin.lt_def] at this
      have h1 := ecount_succ S i h
      have h2 := (strictMono_bounds g hg i).1
      rw [ite_eq_left hi] at h1
      lia
  · intro f hf
    funext i
    apply Fin.ext
    have := ecount_le S i
    lia
  · intro g hg
    funext i
    apply Fin.ext
    simp only [mem_filter, mem_univ, true_and] at hg
    have := (strictMono_bounds g hg i).1
    lia

end RealRooted.FiniteWords
