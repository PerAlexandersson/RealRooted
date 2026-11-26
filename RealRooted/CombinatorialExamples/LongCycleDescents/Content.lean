/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Multiset.Sort
public import RealRooted.CombinatorialExamples.LongCycleDescents.Words
import Mathlib.Tactic

/-!
# Necklace inventories and their multiplicities

Rotation-invariant itinerary multiplicities encode the cycle-length restricted
Gessel--Reutenauer correspondence. We count each inventory fiber by ordered labels.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0).
-/

@[expose] public noncomputable section

namespace RealRooted.LongCycleDescents.Necklace
open RealRooted.LongCycleDescents.Words
variable {n q : ℕ}

/-- Factorial-length itineraries ordered lexicographically. -/
abbrev Key (n q : ℕ) := Lex (Word n.factorial q)

/-- The first letter of a factorial-length itinerary. -/
def first (s : Key n q) : Fin q := ofLex s ⟨0,Nat.factorial_pos _⟩

/-- Cyclic rotation as a permutation of the itinerary keys. -/
def turn (n q : ℕ) : Equiv.Perm (Key n q) where
  toFun s := toLex (shift 1 (ofLex s))
  invFun s := toLex (shift (n.factorial - 1) (ofLex s))
  left_inv s := by simp [shift_add, Nat.sub_add_cancel (Nat.factorial_pos n)]
  right_inv s := by simp [shift_add, Nat.add_sub_of_le (Nat.factorial_pos n)]

/-- Read successive colors along the orbit of a permutation, for one factorial period. -/
def signature (σ : Equiv.Perm (Fin n)) (x : Fin n → Fin q) (i : Fin n) : Key n q :=
  toLex fun j ↦ x ((σ ^ j.val) i)

/-- The first letter of an orbit itinerary is its starting color. -/
@[simp] theorem first_signature (σ : Equiv.Perm (Fin n)) (x : Fin n → Fin q) (i : Fin n) :
    first (signature σ x i) = x i := by simp [first,signature]

/-- Advancing the permutation rotates its orbit itinerary. -/
theorem signature_step (σ : Equiv.Perm (Fin n)) (x : Fin n → Fin q) (i : Fin n) :
    signature σ x (σ i) = turn n q (signature σ x i) := by
  apply ofLex.injective
  funext j
  change x ((σ ^ j.val) (σ i)) = x ((σ ^ ((j.val + 1) % n.factorial)) i)
  have period := pow_mod_card σ (j.val + 1)
  rw [Fintype.card_perm, Fintype.card_fin] at period
  rw [period,pow_succ,Equiv.Perm.mul_apply]

/-- Stable colorings give weakly increasing lexicographic orbit itineraries. -/
theorem signature_monotone {σ : Equiv.Perm (Fin n)} {x : Fin n → Fin q}
    (st : Stable σ x) : Monotone (signature σ x) := by
  apply monotone_iff_forall_lt.mpr
  intro a b ab
  apply le_of_not_gt
  rintro ⟨i,prev,lt⟩
  have same (j : ℕ) (hj : j < i.val) : x ((σ ^ j) b) = x ((σ ^ j) a) :=
    prev ⟨j,hj.trans i.isLt⟩ hj
  exact ab.not_gt ((first_difference_iff st b a i.val same (ne_of_lt lt)).mpr lt)

/-- The first letter is weakly increasing in lexicographic order. -/
theorem head_monotone : Monotone (@first n q) := by
  apply monotone_iff_forall_lt.mpr
  rintro a b ⟨i,prev,lt⟩
  by_cases hi : i.val = 0
  · have eq : i = ⟨0,Nat.factorial_pos n⟩ := Fin.ext hi
    subst i
    exact lt.le
  · exact le_of_eq (prev ⟨0,Nat.factorial_pos n⟩ (Nat.pos_of_ne_zero hi))

/-- Rotation preserves the order of unequal itineraries with the same first letter. -/
theorem turn_lt_of_first_eq {a b : Key n q} (hab : a < b) (eq : first a = first b) :
    turn n q a < turn n q b := by
  obtain ⟨i,prev,lt⟩ := hab
  have pos : 0 < i.val := by
    by_contra! hn
    have hi : i = ⟨0,Nat.factorial_pos n⟩ := Fin.ext (by change i.val = 0; lia)
    subst i
    exact lt.ne eq
  let j : Fin n.factorial := ⟨i.val - 1,by have := i.isLt; lia⟩
  have ji : j.val + 1 = i.val := by dsimp [j]; lia
  refine ⟨j,?_,?_⟩
  · intro k hkj
    have hk : k.val + 1 < i.val := by change k.val < j.val at hkj; lia
    have hmod := Nat.mod_eq_of_lt (hk.trans i.isLt)
    change ofLex a ⟨(k.val + 1)%n.factorial,_⟩ = ofLex b ⟨(k.val + 1)%n.factorial,_⟩
    apply prev
    change (k.val + 1)%n.factorial < i.val
    rwa [hmod]
  · change ofLex a ⟨(j.val + 1)%n.factorial,_⟩ < ofLex b ⟨(j.val + 1)%n.factorial,_⟩
    have hj :
        (⟨(j.val + 1)%n.factorial, Nat.mod_lt _ (Nat.factorial_pos n)⟩ : Fin n.factorial) = i :=
      Fin.ext (by change (j.val + 1)%n.factorial = i.val; rw [ji,Nat.mod_eq_of_lt i.isLt])
    rw [hj]
    exact lt

/-- Sorted itineraries with rotation-invariant multiplicities. -/
def OrderedInventory (n q : ℕ) :=
  {w : Fin n → Key n q // Monotone w ∧ ∀ s, frequency w (turn n q s) = frequency w s}

/-- Iterating the successor rotates each itinerary by the same number of steps. -/
theorem shift_iterate (w : Fin n → Key n q) (σ : Equiv.Perm (Fin n))
    (step : ∀ i, w (σ i) = turn n q (w i)) (r : ℕ) (i : Fin n) :
    ofLex (w ((σ ^ r) i)) = shift r (ofLex (w i)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,step]
    change shift 1 (ofLex (w ((σ ^ r) i))) = shift (r + 1) (ofLex (w i))
    rw [ih,shift_add,Nat.add_comm]

/-- Reconstruction recovers the original sorted orbit itineraries. -/
theorem recover_signature (w : Fin n → Key n q) (σ : Equiv.Perm (Fin n))
    (step : ∀ i, w (σ i) = turn n q (w i)) : signature σ (first ∘ w) = w := by
  funext i
  apply ofLex.injective
  funext j
  change ofLex (w ((σ ^ j.val) i)) ⟨0,Nat.factorial_pos n⟩ = ofLex (w i) j
  rw [shift_iterate w σ step]
  exact congrArg (ofLex (w i)) (Fin.ext (by
    change (0 + j.val)%n.factorial = j.val
    simp [Nat.mod_eq_of_lt j.isLt]))

/-- Recover a compatible permutation and coloring from a sorted itinerary inventory. -/
def recoverPair (w : OrderedInventory n q) : Compatible n q := by
  let h := w.val
  let σ := reconstruct h (turn n q) w.property.2
  refine ⟨(σ,first ∘ h),?_⟩
  intro a b ab
  obtain ⟨hm,inv⟩ := w.property
  have hab : h a ≤ h b := hm ab.le
  refine Prod.Lex.toLex_lt_toLex'.mpr ⟨head_monotone hab,?_⟩
  intro eq
  obtain lt | same := hab.lt_or_eq
  · have turned := turn_lt_of_first_eq lt eq
    have hsa : h (σ a) < h (σ b) := calc
      _ = turn n q (h a) := reconstruct_shift h (turn n q) w.property.2 a
      _ < turn n q (h b) := turned
      _ = _ := (reconstruct_shift h (turn n q) w.property.2 b).symm
    exact lt_of_not_ge (fun le ↦ hsa.not_ge (hm le))
  · exact reconstruct_tie h (turn n q) inv ab same

/-- Compatible permutation-coloring pairs and sorted itinerary inventories are equivalent. -/
def inventoryEquiv (n q : ℕ) : Compatible n q ≃ OrderedInventory n q where
  toFun u := ⟨signature u.val.1 u.val.2,signature_monotone u.property,
    shift_frequency _ _ _ (signature_step u.val.1 u.val.2)⟩
  invFun := recoverPair
  left_inv u := by
    obtain ⟨⟨σ,x⟩,st⟩ := u
    apply Subtype.ext
    apply Prod.ext
    · apply Eq.symm
      apply reconstruct_unique (signature σ x) (turn n q) σ (signature_step σ x)
      intro a b ab same
      have eq := congrArg first same
      exact (Prod.Lex.toLex_lt_toLex'.mp (st ab)).2 (by simpa using eq)
    · funext i
      exact first_signature σ x i
  right_inv w := Subtype.ext (recover_signature w.val _ (reconstruct_shift _ _ _))

/-- Returning to a rooted word is precisely returning to the original permutation position. -/
theorem period_dvd_iff_return {σ : Equiv.Perm (Fin n)} {x : Fin n → Fin q}
    (st : Stable σ x) (i : Fin n) (r : ℕ) :
    period (ofLex (signature σ x i)) ∣ r ↔ (σ ^ r) i = i := by
  rw [period_dvd_iff,← shift_iterate _ _ (signature_step σ x)]
  constructor
  · intro eq
    apply RealRooted.LongCycleDescents.primitive_itinerary σ x
      (fun a b hab h ↦ (Prod.Lex.toLex_lt_toLex'.mp (st hab)).2 h) i r
    intro j
    have h := congrFun eq ⟨j % n.factorial,Nat.mod_lt _ (Nat.factorial_pos n)⟩
    have p := pow_mod_card σ j
    rw [Fintype.card_perm,Fintype.card_fin] at p
    change x ((σ ^ (j % n.factorial)) ((σ ^ r) i)) = x ((σ ^ (j % n.factorial)) i) at h
    simpa only [p] using h.symm
  · intro ret
    rw [ret]

/-- The original cycle cutoff is equivalent to the lower bound on all itinerary periods. -/
theorem allowed_iff_word_period {σ : Equiv.Perm (Fin n)} {x : Fin n → Fin q}
    (st : Stable σ x) (k : ℕ) :
    HasLongCycles k σ ↔ ∀ i, k ≤ period (ofLex (signature σ x i)) := by
  constructor
  · intro allowed i
    apply le_of_not_gt
    intro lt
    exact allowed i _ (period_pos (Nat.factorial_pos n) _) lt
      ((period_dvd_iff_return st i _).mp (dvd_refl _))
  · intro lower i j pos lt ret
    exact (Nat.le_of_dvd pos ((period_dvd_iff_return st i j).mpr ret)).not_gt (lt.trans_le
      (lower i))

/-- The compatible-pair correspondence preserves the prescribed cycle cutoff. -/
def cutoffInventoryEquiv (n q k : ℕ) :
    {u : Compatible n q // HasLongCycles k u.val.1} ≃
      {w : OrderedInventory n q // ∀ i, k ≤ period (ofLex (w.val i))} :=
  (inventoryEquiv n q).subtypeEquiv (fun u ↦ allowed_iff_word_period u.property k)

end RealRooted.LongCycleDescents.Necklace

namespace RealRooted.LongCycleDescents.Necklace

section General
variable {n : ℕ} {K : Type*} [LinearOrder K] [Fintype K]

omit [Fintype K] in
/-- The size of an itinerary fiber equals its multiplicity in the associated multiset. -/
theorem frequency_count (w : Fin n → K) (s : K) :
    frequency w s = (List.ofFn w : Multiset K).count s := by
  rw [← Fin.univ_val_map,Multiset.count_map,frequency,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp [Finset.card,Finset.filter_val,eq_comm]

/-- Expand each multiplicity into that many copies of its index. -/
def expand (m : K → ℕ) : Multiset K := ∑ s, Multiset.replicate (m s) s

/-- Expansion has the prescribed multiplicity at every index. -/
@[simp] theorem expand_count (m : K → ℕ) (s : K) : (expand m).count s = m s := by
  simp [expand,Multiset.count_sum',Multiset.count_replicate]

omit [LinearOrder K] in
/-- The cardinality of an expanded multiset is its total multiplicity. -/
@[simp] theorem expand_card (m : K → ℕ) : (expand m).card = ∑ s, m s := by
  simp [expand,Multiset.card_sum]

/-- Expanding the frequencies of a word recovers its multiset of letters. -/
theorem expand_frequency (w : Fin n → K) : expand (frequency w) = List.ofFn w := by
  ext s
  rw [expand_count,frequency_count]

/-- The sum of all fiber sizes is the length of the word. -/
theorem total_frequency (w : Fin n → K) : ∑ s, frequency w s = n := by
  rw [← expand_card,expand_frequency]
  simp

omit [Fintype K] in
/-- A weakly increasing finite word is determined by its letter multiplicities. -/
theorem sorted_determined {w v : Fin n → K} (hw : Monotone w) (hv : Monotone v)
    (eq : frequency w = frequency v) : w = v := by
  apply List.ofFn_injective
  apply List.Perm.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr hw) (List.sortedLE_ofFn_iff.mpr hv)
  apply Multiset.coe_eq_coe.mp
  ext s
  rw [← frequency_count, ← frequency_count, eq]

/-- Read a multiplicity function as its weakly increasing word of the specified length. -/
def enumerateMass (m : K → ℕ) (h : ∑ s, m s = n) : Fin n → K :=
  let l := (expand m).sort (· ≤ ·)
  fun i ↦ l.get (Fin.cast (by simpa [l] using h.symm) i)

/-- Enumeration reads precisely the sorted expansion of the multiplicities. -/
theorem enumerate_list (m : K → ℕ) (h : ∑ s, m s = n) :
    List.ofFn (enumerateMass m h) = (expand m).sort (· ≤ ·) := by
  let l := (expand m).sort (· ≤ ·)
  have len : l.length = n := by simpa [l] using h
  exact (List.ofFn_congr len l.get).symm.trans (List.ofFn_get l)

/-- Enumeration of multiplicities is weakly increasing. -/
theorem enumerate_monotone (m : K → ℕ) (h : ∑ s, m s = n) : Monotone (enumerateMass m h) := by
  rw [← List.sortedLE_ofFn_iff,enumerate_list]
  exact List.sortedLE_iff_pairwise.mpr (Multiset.pairwise_sort _ _)

/-- Enumeration recovers the specified multiplicity function. -/
theorem enumerate_frequency (m : K → ℕ) (h : ∑ s, m s = n) : frequency (enumerateMass m h) = m := by
  funext s
  rw [frequency_count,enumerate_list,Multiset.sort_eq,expand_count]

end General

variable {n q : ℕ}

/-- An itinerary has positive multiplicity exactly when some position carries it. -/
theorem frequency_pos_iff {K : Type*} (w : Fin n → K) (s : K) :
    0 < frequency w s ↔ ∃ i, w i = s := by
  classical
  rw [frequency,Nat.card_eq_fintype_card,Fintype.card_pos_iff]
  exact ⟨fun ⟨i,h⟩ ↦ ⟨i,h⟩, fun ⟨i,h⟩ ↦ ⟨⟨i,h⟩⟩⟩

/-- Multiplicities are constant around an orbit and vanish below the prescribed period. -/
def MassInventory (n q k : ℕ) :=
  {m : Key n q → ℕ // (∑ s, m s) = n ∧ (∀ s, m (turn n q s) = m s) ∧
    ∀ s, 0 < m s → k ≤ Words.period (ofLex s)}

/-- Sorted inventories and invariant multiplicity functions are equivalent. -/
def massEquiv (n q k : ℕ) :
    {w : OrderedInventory n q // ∀ i, k ≤ Words.period (ofLex (w.val i))} ≃
      MassInventory n q k where
  toFun w := ⟨frequency w.val.val,total_frequency (K := Key n q) w.val.val,w.val.property.2,
    fun s hs ↦ by obtain ⟨i,rfl⟩ := (frequency_pos_iff w.val.val s).mp hs; exact w.property i⟩
  invFun m := by
    let w := enumerateMass m.val m.property.1
    have freq : frequency w = m.val := enumerate_frequency _ _
    refine ⟨⟨w,enumerate_monotone _ _,?_⟩,?_⟩
    · rw [freq]
      exact m.property.2.1
    · intro i
      apply m.property.2.2
      exact lt_of_lt_of_eq ((frequency_pos_iff w (w i)).mpr ⟨i,rfl⟩) (congrFun freq (w i))
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact sorted_determined (enumerate_monotone (frequency w.val.val) (total_frequency w.val.val))
      w.val.property.1 (enumerate_frequency (frequency w.val.val) (total_frequency w.val.val))
  right_inv m := by
    apply Subtype.ext
    exact enumerate_frequency m.val m.property.1

/-- Allowed compatible pairs correspond to invariant multiplicity functions with the cutoff. -/
def cutoffMassEquiv (n q k : ℕ) :
    {u : Compatible n q // HasLongCycles k u.val.1} ≃ MassInventory n q k :=
  (cutoffInventoryEquiv n q k).trans (massEquiv n q k)

end RealRooted.LongCycleDescents.Necklace

namespace RealRooted.LongCycleDescents.Necklace
open Finset RealRooted.LongCycleDescents
private abbrev strictChoices (n Q : ℕ) :=
  {f : Fin n → Fin Q // StrictMono f}

private def strictChoicesEquiv (n Q : ℕ) :
    strictChoices n Q ≃ ↥((univ : Finset (Fin Q)).powersetCard n) where
  toFun f := ⟨univ.image f.val, mem_powersetCard.mpr
    ⟨subset_univ _, by rw [card_image_of_injective _ f.property.injective, card_univ,
      Fintype.card_fin]⟩⟩
  invFun s := ⟨s.val.orderEmbOfFin (mem_powersetCard.mp s.property).2,
    (s.val.orderEmbOfFin (mem_powersetCard.mp s.property).2).strictMono⟩
  left_inv f := by
    apply Subtype.ext
    exact (orderEmbOfFin_unique _ (fun i ↦ mem_image.mpr ⟨i, mem_univ _, rfl⟩) f.property).symm
  right_inv s := by
    apply Subtype.ext
    exact image_orderEmbOfFin_univ _ _

private theorem card_strictChoices (n Q : ℕ) : Nat.card (strictChoices n Q) = Q.choose n := by
  rw [Nat.card_congr (strictChoicesEquiv n Q), Nat.card_eq_fintype_card, Fintype.card_coe,
    card_powersetCard, card_univ, Fintype.card_fin]

/-- Indices at which a weak labeling is allowed to repeat a letter. -/
private def repeatSlack {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (a : ℕ) : ℕ :=
  if h : a < m then
    if σ (⟨a,h⟩ : Fin m).succ < σ (⟨a,h⟩ : Fin m).castSucc then 0 else 1
  else 0

private def slack {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (i : ℕ) : ℕ :=
  ∑ a ∈ range i, repeatSlack σ a

private theorem repeatSlack_le_one {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (a : ℕ) :
    repeatSlack σ a ≤ 1 := by
  unfold repeatSlack
  split
  · split <;> simp
  · simp

private theorem slack_mono {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    Monotone (slack σ) := by
  apply monotone_nat_of_le_succ
  intro i
  unfold slack
  rw [sum_range_succ]
  exact Nat.le_add_right _ _

private theorem slack_le_index {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (i : ℕ) :
    slack σ i ≤ i := by
  calc
    slack σ i ≤ ∑ a ∈ range i, (1 : ℕ) := sum_le_sum fun a _ ↦ repeatSlack_le_one σ a
    _ = i := by simp

private theorem slack_step {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m) :
    slack σ (i.val + 1) =
      slack σ i.val + if σ i.succ < σ i.castSucc then 0 else 1 := by
  rw [slack, sum_range_succ]
  simp [repeatSlack, i.isLt, slack]

private theorem slack_total {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    slack σ m + σ.descentCount = m := by
  rw [descents_eq_card, slack, ← Fin.sum_univ_eq_sum_range]
  have count := Finset.sum_boole (R := ℕ) (fun i : Fin m ↦ σ i.succ < σ i.castSucc) univ
  simp only [Nat.cast_id] at count
  rw [← count, ← Finset.sum_add_distrib]
  calc
    _ = ∑ i : Fin m, (1 : ℕ) := by
      apply sum_congr rfl
      intro i _
      simp only [repeatSlack, dite_eq_left i.isLt, Fin.eta]
      split <;> simp_all
    _ = m := by simp

private theorem index_le_value {m Q : ℕ} {z : Fin (m + 1) → Fin Q} (hz : StrictMono z) :
    ∀ i : Fin (m + 1), i.val ≤ (z i).val := by
  apply Fin.induction
  · simp
  · intro i ih
    have step := Fin.strictMono_iff_lt_succ.mp hz i
    change (z i.castSucc).val < (z i.succ).val at step
    change i.val ≤ (z i.castSucc).val at ih
    change i.val + 1 ≤ (z i.succ).val
    lia

private def expandedAlphabet {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (q : ℕ) : ℕ :=
  q + m - σ.descentCount

private def stableToStrict {m q : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    (x : {w : Fin (m + 1) → Fin q // Stable σ w}) :
    strictChoices (m + 1) (expandedAlphabet σ q) := by
  have bounds (i : Fin (m + 1)) : (x.val i).val + slack σ i.val < expandedAlphabet σ q := by
    have a := (x.val i).isLt
    have b := slack_mono σ (show i.val ≤ m by lia)
    unfold expandedAlphabet
    have c := slack_total σ
    lia
  let z (i : Fin (m + 1)) : Fin (expandedAlphabet σ q) :=
    ⟨(x.val i).val + slack σ i.val, bounds i⟩
  refine ⟨z, Fin.strictMono_iff_lt_succ.mpr fun i ↦ ?_⟩
  obtain ⟨mono, rise⟩ := (stable_iff_adjacent σ x.val).mp x.property
  have nonstrict := mono (show i.castSucc < i.succ from Fin.castSucc_lt_succ).le
  change (x.val i.castSucc).val ≤ (x.val i.succ).val at nonstrict
  change (x.val i.castSucc).val + slack σ i.val <
    (x.val i.succ).val + slack σ (i.val + 1)
  rw [slack_step]
  split
  · rename_i desc
    have lt := rise i desc
    change (x.val i.castSucc).val < (x.val i.succ).val at lt
    lia
  · lia

private def strictToStable {m q : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    (z : strictChoices (m + 1) (expandedAlphabet σ q)) :
    {w : Fin (m + 1) → Fin q // Stable σ w} := by
  let x (i : Fin (m + 1)) := (z.val i).val - slack σ i.val
  have covers (i : Fin (m + 1)) : slack σ i.val ≤ (z.val i).val :=
    (slack_le_index σ i.val).trans (index_le_value z.property i)
  have adjacent (i : Fin m) : x i.castSucc ≤ x i.succ := by
    have lt := Fin.strictMono_iff_lt_succ.mp z.property i
    change (z.val i.castSucc).val < (z.val i.succ).val at lt
    change (z.val i.castSucc).val - slack σ i.val ≤
      (z.val i.succ).val - slack σ (i.val + 1)
    rw [slack_step]
    split <;> lia
  have mono : Monotone x := Fin.monotone_iff_le_succ.mpr adjacent
  have final : x (Fin.last m) < q := by
    have h := (z.val (Fin.last m)).isLt
    have total := slack_total σ
    have base := covers (Fin.last m)
    change slack σ m ≤ (z.val (Fin.last m)).val at base
    change (z.val (Fin.last m)).val - slack σ m < q
    change (z.val (Fin.last m)).val < q + m - σ.descentCount at h
    lia
  let w (i : Fin (m + 1)) : Fin q := ⟨x i, (mono (Fin.le_last i)).trans_lt final⟩
  refine ⟨w, (stable_iff_adjacent σ w).mpr ⟨fun a b ab ↦ mono ab, fun i desc ↦ ?_⟩⟩
  have lt := Fin.strictMono_iff_lt_succ.mp z.property i
  have low := covers i.castSucc
  change slack σ i.val ≤ (z.val i.castSucc).val at low
  change (z.val i.castSucc).val < (z.val i.succ).val at lt
  change (z.val i.castSucc).val - slack σ i.val <
    (z.val i.succ).val - slack σ (i.val + 1)
  have fixed := slack_step σ i
  rw [ite_eq_left desc, Nat.add_zero] at fixed
  rw [fixed]
  lia

private def stableEquivStrict {m q : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    {w : Fin (m + 1) → Fin q // Stable σ w} ≃
      strictChoices (m + 1) (expandedAlphabet σ q) where
  toFun := stableToStrict σ
  invFun := strictToStable σ
  left_inv w := by
    ext i
    change (w.val i).val + slack σ i.val - slack σ i.val = (w.val i).val
    lia
  right_inv z := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    change (z.val i).val - slack σ i.val + slack σ i.val = (z.val i).val
    exact Nat.sub_add_cancel ((slack_le_index σ i.val).trans (index_le_value z.property i))

/-- The number of weak labelings that rise at every ordinary descent. -/
theorem card_stable {n : ℕ} (σ : Equiv.Perm (Fin n)) (q : ℕ) :
    Nat.card {x : Fin n → Fin q // Stable σ x} =
      (q + n - 1 - σ.descentCount).choose n := by
  cases n with
  | zero =>
    rw [Nat.choose_zero_right]
    have : Subsingleton {x : Fin 0 → Fin q // Stable σ x} :=
      ⟨fun a b ↦ Subtype.ext (funext fun i ↦ i.elim0)⟩
    have : Nonempty {x : Fin 0 → Fin q // Stable σ x} :=
      ⟨⟨Fin.elim0, fun i ↦ i.elim0⟩⟩
    exact Nat.card_unique
  | succ m =>
    rw [Nat.card_congr (stableEquivStrict (q := q) σ), card_strictChoices]
    congr 1

/-- A nonempty word requires more letters than its number of required strict rises. -/
theorem card_stable_small_alphabet {n q : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n))
    (small : q ≤ σ.descentCount) :
    Nat.card {x : Fin n → Fin q // Stable σ x} = 0 := by
  rw [card_stable, Nat.choose_eq_zero_of_lt (by lia)]

private theorem descents_lt_size {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    σ.descentCount < n := by
  cases n with
  | zero => lia
  | succ m =>
    rw [descents_eq_card]
    exact (card_filter_le _ _).trans_lt (by simp)

-- This is the same compatible-pair subtype used in the itinerary bijection.
/-- Stable permutation-coloring pairs satisfying the original cycle cutoff. -/
abbrev AllowedCompatible (n q k : ℕ) := {u : Compatible n q // HasLongCycles k u.val.1}

private def allowedCompatibleEquiv (n q k : ℕ) :
    AllowedCompatible n q k ≃
      (Σ σ : {σ : Equiv.Perm (Fin n) // HasLongCycles k σ}, {x : Fin n → Fin q // Stable σ.val
        x}) where
  toFun u := ⟨⟨u.val.val.1, u.property⟩, ⟨u.val.val.2, u.val.property⟩⟩
  invFun u := ⟨⟨(u.1.val, u.2.val), u.2.property⟩, u.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

open Classical in
/-- Count compatible pairs by first choosing an admissible original permutation. -/
theorem card_allowedCompatible_sum (n q k : ℕ) :
    (Nat.card (AllowedCompatible n q k) : ℤ) =
      ∑ σ : Equiv.Perm (Fin n), if HasLongCycles k σ then
        ((q + n - 1 - σ.descentCount).choose n : ℤ) else 0 := by
  classical
  rw [Nat.card_congr (allowedCompatibleEquiv n q k), Nat.card_eq_fintype_card,
    Fintype.card_sigma, Nat.cast_sum]
  calc
    _ = ∑ σ : {σ : Equiv.Perm (Fin n) // HasLongCycles k σ},
        ((q + n - 1 - σ.val.descentCount).choose n : ℤ) := by
      apply sum_congr rfl
      intro σ _
      rw [← Nat.card_eq_fintype_card, card_stable]
    _ = _ := by
      rw [← sum_filter]
      exact (sum_subtype _ (by simp) (fun σ ↦ ((q + n - 1 - Equiv.Perm.descentCount σ).choose n :
        ℤ))).symm

/-- The existing coefficient functional is the count of all admissible compatible pairs. -/
theorem card_allowedCompatible_eq_letters {n : ℕ} (hn : 0 < n) (q k : ℕ) :
    (Nat.card (AllowedCompatible n q k) : ℤ) =
      letters n q (descentPolynomial n k).coeff := by
  classical
  rw [card_allowedCompatible_sum]
  unfold letters
  simp_rw [RealRooted.LongCycleDescents.coeff_descentPolynomial, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro σ _
  by_cases allow : HasLongCycles k σ
  · rw [ite_eq_left allow, sum_eq_single (σ.descentCount)]
    · simp [allow]
    · intro i _ different
      simp only [allow, true_and, Ne.symm different, ite_false, zero_mul]
    · intro missing
      exact (missing (mem_range.mpr (descents_lt_size hn σ))).elim
  · simp [allow]

/-- The empty permutation contributes one labeling. The legacy letters sum is empty at n = 0. -/
theorem card_allowedCompatible_eq_letters_add_empty (n q k : ℕ) :
    (Nat.card (AllowedCompatible n q k) : ℤ) =
      letters n q (descentPolynomial n k).coeff +
        if n = 0 then 1 else 0 := by
  by_cases empty : n = 0
  · subst n
    have all_allowed (σ : Equiv.Perm (Fin 0)) : HasLongCycles k σ := fun i ↦ i.elim0
    rw [card_allowedCompatible_sum]
    simp [all_allowed, letters]
  · rw [card_allowedCompatible_eq_letters (Nat.pos_of_ne_zero empty), ite_eq_right empty, add_zero]

end RealRooted.LongCycleDescents.Necklace

namespace RealRooted.LongCycleDescents.Necklace
open RealRooted.LongCycleDescents.Words

/-- The positive divisors of the factorial-length itinerary. -/
abbrev Lengths (n : ℕ) := n.factorial.divisors
/-- Primitive rooted words indexed by a divisor of the factorial length. -/
abbrev Rooted (n q : ℕ) := Σ d : Lengths n, PrimitiveWord d.val q
/-- Primitive cyclic rotation classes indexed by their length. -/
abbrev Types (n q : ℕ) := Σ d : Lengths n, PrimitiveNecklace d.val q

variable {n q : ℕ}

/-- Repeat a primitive root to the common factorial itinerary length. -/
def repeatRoot (u : Rooted n q) : Key n q :=
  toLex (repeatWord n.factorial (Nat.pos_of_mem_divisors u.1.property) u.2.val)

/-- Repeating a primitive word preserves its primitive period. -/
theorem period_repeatRoot (u : Rooted n q) : period (ofLex (repeatRoot u)) = u.1.val :=
  (period_repeatWord (Nat.factorial_pos n) (Nat.pos_of_mem_divisors u.1.property)
    (Nat.dvd_of_mem_divisors u.1.property) u.2.val).trans u.2.property.2

/-- Every factorial-length itinerary is the repetition of one uniquely rooted primitive word. -/
def rootEquiv (n q : ℕ) : Rooted n q ≃ Key n q :=
  Equiv.ofBijective repeatRoot (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    · rintro ⟨d,u⟩ ⟨e,v⟩ h
      have eq : d = e := Subtype.ext ((period_repeatRoot ⟨d,u⟩).symm.trans
        ((congrArg (fun z ↦ period (ofLex z)) h).trans (period_repeatRoot ⟨e,v⟩)))
      subst e
      congr 1
      apply Subtype.ext
      exact repeatWord_injective (Nat.pos_of_mem_divisors d.property)
        (Nat.le_of_dvd (Nat.factorial_pos n) (Nat.dvd_of_mem_divisors d.property))
        (congrArg ofLex h)
    · rw [Fintype.card_sigma,n.factorial.divisors.sum_coe_sort (fun d ↦ Fintype.card
      (PrimitiveWord d q)),
        sum_card_primitiveWord (Nat.factorial_pos n)]
      calc
        q ^ n.factorial = Fintype.card (Word n.factorial q) := by simp [Word]
        _ = Fintype.card (Key n q) := Fintype.card_congr toLex)

/-- Rotate a primitive root without changing its length. -/
def rotateRoot (r : ℕ) (u : Rooted n q) : Rooted n q := ⟨u.1,shiftPrimitive r u.2⟩

/-- Rotation commutes with repeating a primitive root. -/
theorem repeatRoot_rotate (r : ℕ) (u : Rooted n q) :
    ofLex (repeatRoot (rotateRoot r u)) = shift r (ofLex (repeatRoot u)) :=
  (shift_repeatWord (Nat.pos_of_mem_divisors u.1.property)
    (Nat.dvd_of_mem_divisors u.1.property) _ r).symm

/-- Forget the root of a primitive word and retain its cyclic rotation class. -/
def cycleTypeOfRoot (u : Rooted n q) : Types n q := ⟨u.1,necklaceOf u.2⟩

/-- Summing over primitive words counts each rotation class once per root position. -/
theorem sum_over_primitive (f : PrimitiveNecklace n q → ℕ) :
    (∑ u : PrimitiveWord n q, f (necklaceOf u)) = ∑ N, n * f N := by
  classical
  rw [← Fintype.sum_fiberwise' (necklaceOf (n := n) (q := q)) f]
  apply Finset.sum_congr rfl
  intro N _
  have h := card_necklace_fiber N
  rw [Nat.card_eq_fintype_card] at h
  simp [h]

/-- Sum rooted classes by their length and then by their rotation class. -/
theorem sum_over_types (f : Types n q → ℕ) :
    (∑ u : Rooted n q, f (cycleTypeOfRoot u)) = ∑ N, N.1.val * f N := by
  rw [Fintype.sum_sigma,Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun d _ ↦ sum_over_primitive (fun N ↦ f ⟨d,N⟩)

/-- Invariant itinerary multiplicities are unchanged by any cyclic shift. -/
theorem mass_shift {k : ℕ} (m : MassInventory n q k) (s : Key n q) (r : ℕ) :
    m.val (toLex (shift r (ofLex s))) = m.val s := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.add_comm r 1,← shift_add]
    exact (m.property.2.1 (toLex (shift r (ofLex s)))).trans ih

/-- Forgetting the choice of first letter gives a well-defined multiplicity. -/
def descendMass {k : ℕ} (m : MassInventory n q k) (N : Types n q) : ℕ :=
  Quotient.lift (fun u ↦ m.val (repeatRoot ⟨N.1,u⟩)) (by
    intro u v rel
    obtain ⟨r,eq⟩ := rel
    have hr : shiftPrimitive r u = v := Subtype.ext eq
    subst v
    have h := congrArg toLex (repeatRoot_rotate r (⟨N.1,u⟩ : Rooted n q))
    exact (mass_shift m (repeatRoot ⟨N.1,u⟩) r).symm.trans (congrArg m.val h.symm)) N.2

/-- Assign a rotation-class multiplicity to every rooted itinerary representing that class. -/
def liftContent (a : Types n q → ℕ) (s : Key n q) : ℕ :=
  a (cycleTypeOfRoot ((rootEquiv n q).symm s))

/-- The lift of a rotation-class multiplicity has the expected value at a repeated root. -/
theorem liftContent_root (a : Types n q → ℕ) (u : Rooted n q) :
    liftContent a (repeatRoot u) = a (cycleTypeOfRoot u) :=
  congrArg (fun z ↦ a (cycleTypeOfRoot z)) ((rootEquiv n q).symm_apply_apply u)

/-- The total lifted mass weights each rotation class by its primitive length. -/
theorem liftContent_sum (a : Types n q → ℕ) :
    (∑ s, liftContent a s) = ∑ N, N.1.val * a N := by
  rw [← (rootEquiv n q).sum_comp (liftContent a),← sum_over_types]
  exact Finset.sum_congr rfl fun u _ ↦ liftContent_root a u

/-- Lifted multiplicities are invariant under cyclic rotation. -/
theorem liftContent_invariant (a : Types n q → ℕ) (s : Key n q) :
    liftContent a (turn n q s) = liftContent a s := by
  obtain ⟨u,rfl⟩ := (rootEquiv n q).surjective s
  have move : turn n q (rootEquiv n q u) = repeatRoot (rotateRoot 1 u) :=
    ofLex.injective (repeatRoot_rotate 1 u).symm
  rw [move,liftContent_root]
  change _ = liftContent a (repeatRoot u)
  rw [liftContent_root]
  apply congrArg a
  apply congrArg (fun N : PrimitiveNecklace u.1.val q ↦ (⟨u.1,N⟩ : Types n q))
  exact (Quotient.sound (show (rotationSetoid _ _).r u.2 (shiftPrimitive 1 u.2) from ⟨1,rfl⟩)).symm

/-- Descending and then lifting an invariant multiplicity function recovers it. -/
theorem lift_descend {k : ℕ} (m : MassInventory n q k) : liftContent (descendMass m) = m.val := by
  funext s
  obtain ⟨u,rfl⟩ := (rootEquiv n q).surjective s
  exact liftContent_root (descendMass m) u

/-- Necklace multiplicities of total weight `n`, supported on lengths at least `k`. -/
def NecklaceContent (n q k : ℕ) :=
  {a : Types n q → ℕ // (∑ N, N.1.val * a N) = n ∧ ∀ N, 0 < a N → k ≤ N.1.val}

/-- Invariant itinerary multiplicities and necklace contents are equivalent. -/
def contentEquiv (n q k : ℕ) : MassInventory n q k ≃ NecklaceContent n q k where
  toFun m := by
    refine ⟨descendMass m,?_,?_⟩
    · rw [← liftContent_sum,lift_descend]
      exact m.property.1
    · rintro ⟨d,N⟩
      refine Quotient.inductionOn N fun u h ↦ ?_
      exact (m.property.2.2 (repeatRoot ⟨d,u⟩) h).trans_eq (period_repeatRoot ⟨d,u⟩)
  invFun a := by
    refine ⟨liftContent a.val,(liftContent_sum a.val).trans a.property.1,
      liftContent_invariant a.val,?_⟩
    intro s h
    obtain ⟨u,rfl⟩ := (rootEquiv n q).surjective s
    exact (a.property.2 (cycleTypeOfRoot u) ((liftContent_root a.val u) ▸ h)).trans_eq
      (period_repeatRoot u).symm
  left_inv m := Subtype.ext (lift_descend m)
  right_inv a := by
    apply Subtype.ext
    funext N
    obtain ⟨d,N⟩ := N
    refine Quotient.inductionOn N fun u ↦ ?_
    exact liftContent_root a.val ⟨d,u⟩

/-- The original cycle cutoff and ordinary adjacent descent statistic count precisely
multisets of primitive necklaces of allowed lengths and total size n. -/
def originalNecklaceEquiv (n q k : ℕ) : AllowedCompatible n q k ≃ NecklaceContent n q k :=
  (cutoffMassEquiv n q k).trans (contentEquiv n q k)

/-- The original permutation alphabet specialization counts the necklace contents. -/
theorem letters_eq_necklace_content {n : ℕ} (hn : 0 < n) (q k : ℕ) :
    letters n q (descentPolynomial n k).coeff =
      (Nat.card (NecklaceContent n q k) : ℤ) := by
  rw [← card_allowedCompatible_eq_letters hn q k,Nat.card_congr (originalNecklaceEquiv n q k)]

end RealRooted.LongCycleDescents.Necklace
