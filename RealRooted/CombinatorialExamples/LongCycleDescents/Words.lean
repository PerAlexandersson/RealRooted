/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Sym.NatCard
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.PiLex
public import Mathlib.Order.Prod.Lex.Basic
public import RealRooted.Mathlib.Combinatorics.Enumerative.PermStatistics
import Mathlib.Tactic

/-!
# Cyclic words and stable reconstruction

We use primitive cyclic itineraries to encode ordinary descents, standardize labels,
and reconstruct permutations by matching ordered copies of each itinerary.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0).
-/

@[expose] public noncomputable section

namespace RealRooted.LongCycleDescents

/-- Every cycle has length at least the cutoff: no smaller positive iterate fixes a letter. -/
def HasLongCycles {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : Fin n, ∀ j : ℕ, 0 < j → j < k → (σ ^ j) x ≠ x

/-- A cutoff above one excludes fixed points. -/
theorem ne_fixed_of_allowed {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : HasLongCycles k σ) (hk : 1 < k) (x : Fin n) : σ x ≠ x := by
  simpa only [pow_one] using h x 1 (by decide) hk
open Finset Polynomial RealRooted.LongCycleDescents
/-- The original ordinary descent polynomial on permutations whose cycle lengths are at least k. -/
def descentPolynomial (n k : ℕ) : Polynomial ℤ := by
  classical
  exact ∑ σ : Equiv.Perm (Fin n), if HasLongCycles k σ then X ^ σ.descentCount else 0

/-- The adjacent descent positions can be indexed without including the last letter. -/
theorem descents_eq_card {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    σ.descentCount = (Finset.univ.filter fun i : Fin m ↦ σ i.succ < σ i.castSucc).card := by
  classical
  unfold Equiv.Perm.descentCount
  symm
  apply Finset.card_bij (fun (i : Fin m) _ ↦ i.val)
  · intro i hi
    exact Equiv.Perm.mem_descentSet.mpr ⟨i, rfl, (Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro i hi
    obtain ⟨j, rfl, hj⟩ := Equiv.Perm.mem_descentSet.mp hi
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩

open Classical in
/-- Coefficient of the descent polynomial as an integer count on the original permutations. -/
theorem coeff_descentPolynomial (n k i : ℕ) :
    (descentPolynomial n k).coeff i =
      ∑ σ : Equiv.Perm (Fin n), if HasLongCycles k σ ∧ σ.descentCount = i then (1:ℤ) else 0 := by
  classical
  unfold descentPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply sum_congr rfl
  intro σ _
  by_cases h : HasLongCycles k σ
  · simp [h, Polynomial.coeff_X_pow, eq_comm]
  · simp [h]

/-- The finite-alphabet binomial specialization of a descent coefficient list. -/
def letters (n q : ℕ) (d : ℕ → ℤ) : ℤ :=
  ∑ i ∈ range n, d i * ((q + n - 1 - i).choose n : ℤ)

end RealRooted.LongCycleDescents

namespace RealRooted.LongCycleDescents

/-- The original adjacent descent constraints force the successor permutation to preserve
the strict order of any pair in a common color fiber. -/
theorem order_of_equal_color {n q : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (c : Fin (n + 1) → Fin q) (mono : Monotone c)
    (rise : ∀ i : Fin n, σ i.succ < σ i.castSucc → c i.castSucc < c i.succ)
    {a b : Fin (n + 1)} (ab : a < b) (eqc : c a = c b) : σ a < σ b := by
  have order : StrictMono (fun i ↦ toLex (c i, σ i)) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    apply Prod.Lex.toLex_lt_toLex'.mpr
    refine ⟨mono (show i.castSucc < i.succ from Fin.castSucc_lt_succ).le, ?_⟩
    intro same
    apply lt_of_le_of_ne
    · exact le_of_not_gt fun h ↦ (ne_of_lt (rise i h)) same
    · exact σ.injective.ne (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne
  exact (Prod.Lex.toLex_lt_toLex'.mp (order ab)).2 eqc

/-- Two rotations of a single orbit with identical infinite itineraries start at the same
point. This is the primitive-necklace step of the Gessel--Reutenauer correspondence. -/
theorem primitive_itinerary {α β : Type*} [Finite α] [LinearOrder α]
    (σ : Equiv.Perm α) (c : α → β)
    (tie : ∀ a b, a < b → c a = c b → σ a < σ b)
    (a : α) (d : ℕ)
    (same : ∀ j : ℕ, c ((σ ^ j) a) = c ((σ ^ j) ((σ ^ d) a))) :
    (σ ^ d) a = a := by
  let := Fintype.ofFinite α
  have propagate {x y : α} (xy : x < y)
      (colors : ∀ j : ℕ, c ((σ ^ j) x) = c ((σ ^ j) y)) (j : ℕ) :
      (σ ^ j) x < (σ ^ j) y := by
    induction j with
    | zero => simpa using xy
    | succ j ih => simpa [pow_succ', Equiv.Perm.mul_apply] using tie _ _ ih (colors j)
  let τ := σ ^ d
  have rule {x y : α} (j : ℕ) (h : (σ ^ (d * j)) x < (σ ^ (d * j)) y) :
      (τ ^ j) x < (τ ^ j) y := by simpa [τ, pow_mul] using h
  by_contra h
  rcases lt_or_gt_of_ne h with down | up
  · have dec : StrictAnti (fun j : ℕ ↦ (τ ^ j) a) := by
      apply strictAnti_nat_of_succ_lt
      intro j
      have r := rule j (propagate down (fun i ↦ (same i).symm) (d * j))
      simpa [pow_succ, Equiv.Perm.mul_apply, τ] using r
    exact (lt_irrefl a) (by simpa [pow_orderOf_eq_one] using dec (orderOf_pos τ))
  · have inc : StrictMono (fun j : ℕ ↦ (τ ^ j) a) := by
      apply strictMono_nat_of_lt_succ
      intro j
      have r := rule j (propagate up same (d * j))
      simpa [pow_succ, Equiv.Perm.mul_apply, τ] using r
    exact (lt_irrefl a) (by simpa [pow_orderOf_eq_one] using inc (orderOf_pos τ))

end RealRooted.LongCycleDescents

namespace RealRooted.LongCycleDescents.Necklace
open RealRooted.LongCycleDescents RealRooted.LongCycleDescents

variable {n q : ℕ}

/-- Colors followed by permutation values increase strictly in lexicographic order. -/
def Stable (σ : Equiv.Perm (Fin n)) (x : Fin n → Fin q) : Prop :=
  StrictMono fun i ↦ toLex (x i, σ i)

/-- Stable labels are weakly increasing and rise strictly at every adjacent descent. -/
theorem stable_iff_adjacent {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (x : Fin (m + 1) → Fin q) :
    Stable σ x ↔ Monotone x ∧
      ∀ i : Fin m, σ i.succ < σ i.castSucc → x i.castSucc < x i.succ := by
  constructor
  · intro h
    refine ⟨monotone_iff_forall_lt.mpr (fun a b ab ↦ (Prod.Lex.toLex_lt_toLex'.mp (h ab)).1),?_⟩
    intro i desc
    obtain ⟨hle,tie⟩ := Prod.Lex.toLex_lt_toLex'.mp (h (Fin.castSucc_lt_succ (i := i)))
    exact lt_of_le_of_ne hle (fun eq ↦ (tie eq).not_gt desc)
  · rintro ⟨mono,rise⟩ a b hab
    exact Prod.Lex.toLex_lt_toLex'.mpr ⟨mono hab.le,order_of_equal_color σ x mono rise hab⟩

/-- A letter-position pair lying in the graph of the word, with lexicographic order. -/
abbrev Position (w : Fin n → Fin q) :=
  {u : Fin q ×ₗ Fin n // (ofLex u).1 = w (ofLex u).2}

/-- Identify each word position with its letter-position pair. -/
def seat (w : Fin n → Fin q) : Fin n ≃ Position w where
  toFun i := ⟨toLex (w i,i),rfl⟩
  invFun u := (ofLex u.val).2
  left_inv _ := rfl
  right_inv u := by
    apply Subtype.ext
    apply ofLex.injective
    exact Prod.ext u.property.symm rfl

/-- Enumerate the word positions in increasing letter-position order. -/
def sorted (w : Fin n → Fin q) : Fin n ≃o Position w :=
  Fintype.orderIsoFinOfCardEq (Position w) (by rw [Fintype.card_congr (seat
    w).symm,Fintype.card_fin])

/-- The permutation listing positions in stable increasing letter order. -/
def standardize (w : Fin n → Fin q) : Equiv.Perm (Fin n) :=
  (sorted w).toEquiv.trans (seat w).symm

/-- The letters of a word read in stable increasing order. -/
def colors (w : Fin n → Fin q) : Fin n → Fin q := w ∘ standardize w

private theorem sorted_value (w : Fin n → Fin q) (i : Fin n) :
    (sorted w i).val = toLex (colors w i,standardize w i) := by
  change (sorted w i).val = toLex (w (ofLex (sorted w i).val).2,(ofLex (sorted w i).val).2)
  apply ofLex.injective
  exact Prod.ext (sorted w i).property rfl

/-- Stable standardization gives a compatible permutation and coloring. -/
theorem standardize_stable (w : Fin n → Fin q) : Stable (standardize w) (colors w) := by
  intro a b ab
  change toLex (colors w a, standardize w a) < toLex (colors w b, standardize w b)
  rw [←sorted_value,←sorted_value]
  exact (sorted w).strictMono ab

/-- The stability property uniquely determines the standardization permutation. -/
theorem stable_unique (w : Fin n → Fin q) (σ : Equiv.Perm (Fin n))
    (h : Stable σ (w ∘ σ)) : σ = standardize w := by
  let e := σ.trans (seat w)
  have he : StrictMono e := by
    intro a b ab
    exact h ab
  let o := he.orderIsoOfRightInverse e e.symm e.apply_symm_apply
  have same : o = sorted w := Subsingleton.elim _ _
  apply Equiv.ext
  intro i
  have hi := congrArg (fun f : Fin n ≃o Position w ↦ (seat w).symm (f i)) same
  change (seat w).symm (seat w (σ i)) = standardize w i at hi
  simpa only [Equiv.symm_apply_apply] using hi

/-- A permutation equipped with a coloring stable in its original adjacent-descent order. -/
abbrev Compatible (n q : ℕ) := {p : Equiv.Perm (Fin n) × (Fin n → Fin q) // Stable p.1 p.2}

/-- All words are in bijection with permutations equipped with weakly increasing
labels which rise at each ordinary descent. The inverse word is written in original positions. -/
def wordEquiv (n q : ℕ) : (Fin n → Fin q) ≃ Compatible n q where
  toFun w := ⟨(standardize w,colors w),standardize_stable w⟩
  invFun u := u.val.2 ∘ u.val.1.symm
  left_inv w := by funext i; exact congrArg w ((standardize w).apply_symm_apply i)
  right_inv u := by
    obtain ⟨⟨σ,x⟩,h⟩ := u
    let w := x ∘ σ.symm
    have orig : w ∘ σ = x := by funext i; simp [w]
    have he : σ = standardize w := stable_unique w σ (orig ▸ h)
    apply Subtype.ext
    exact Prod.ext he.symm (show colors w = x by unfold colors; rw [←he,orig])

/-- Equal initial colors preserve order until the first place at which itineraries differ. -/
theorem prefix_preserves_order {σ : Equiv.Perm (Fin n)} {x : Fin n → Fin q}
    (st : Stable σ x) {a b : Fin n} (ab : a < b) (j : ℕ)
    (same : ∀ i < j, x ((σ ^ i) a) = x ((σ ^ i) b)) : (σ ^ j) a < (σ ^ j) b := by
  induction j with
  | zero => simpa using ab
  | succ j ih =>
    have h := (Prod.Lex.toLex_lt_toLex'.mp (st (ih (fun i hi ↦ same i (Nat.lt_succ_of_lt hi))))).2
      (same j (Nat.lt_succ_self j))
    simpa [pow_succ', Equiv.Perm.mul_apply] using h

/-- At a first unequal letter the original order and the letter order agree, in both directions. -/
theorem first_difference_iff {σ : Equiv.Perm (Fin n)} {x : Fin n → Fin q}
    (st : Stable σ x) (a b : Fin n) (j : ℕ)
    (same : ∀ i < j, x ((σ ^ i) a) = x ((σ ^ i) b))
    (diff : x ((σ ^ j) a) ≠ x ((σ ^ j) b)) :
    a < b ↔ x ((σ ^ j) a) < x ((σ ^ j) b) := by
  constructor
  · intro ab
    exact lt_of_le_of_ne (Prod.Lex.toLex_lt_toLex'.mp (st (prefix_preserves_order st ab j
      same))).1 diff
  · intro hab
    rcases lt_trichotomy a b with ab | eq | ba
    · exact ab
    · subst b
      exact False.elim (diff rfl)
    · exact False.elim (hab.not_ge (Prod.Lex.toLex_lt_toLex'.mp
        (st (prefix_preserves_order st ba j (fun i hi ↦ (same i hi).symm)))).1)

end RealRooted.LongCycleDescents.Necklace

namespace RealRooted.LongCycleDescents.Necklace

variable {n : ℕ} {K : Type*} [DecidableEq K]

/-- The positions carrying one specified itinerary. -/
abbrev Fiber (w : Fin n → K) (s : K) := {i : Fin n // w i = s}

/-- The cardinality of one itinerary fiber. -/
def frequency (w : Fin n → K) (s : K) : ℕ := Nat.card (Fiber w s)

/-- The order on positions distinguishes all the copies of a repeated itinerary. -/
def matchFiber (w : Fin n → K) (T : Equiv.Perm K)
    (invariant : ∀ s, frequency w (T s) = frequency w s) (s : K) :
    Fiber w s ≃o Fiber w (T s) :=
  (Fintype.orderIsoFinOfCardEq (Fiber w s) rfl).symm.trans
    (Fintype.orderIsoFinOfCardEq (Fiber w (T s)) (by
      simpa only [frequency, Nat.card_eq_fintype_card] using invariant s))

/-- Recover the successor permutation by matching ordered fibers along a rotation. -/
def reconstruct (w : Fin n → K) (T : Equiv.Perm K)
    (invariant : ∀ s, frequency w (T s) = frequency w s) : Equiv.Perm (Fin n) :=
  (Equiv.sigmaFiberEquiv w).symm.trans
    ((Equiv.sigmaCongr T fun s ↦ (matchFiber w T invariant s).toEquiv).trans
      (Equiv.sigmaFiberEquiv w))

/-- Reconstruction acts by the increasing equivalence on each fiber. -/
theorem reconstruct_apply (w : Fin n → K) (T : Equiv.Perm K)
    (inv : ∀ s, frequency w (T s) = frequency w s) (i : Fin n) {s : K} (hi : w i = s) :
    reconstruct w T inv i = (matchFiber w T inv s ⟨i,hi⟩).val := by
  subst s
  rfl

/-- The reconstructed successor rotates the itinerary of each position. -/
theorem reconstruct_shift (w : Fin n → K) (T : Equiv.Perm K)
    (inv : ∀ s, frequency w (T s) = frequency w s) (i : Fin n) :
    w (reconstruct w T inv i) = T (w i) :=
  (matchFiber w T inv (w i) ⟨i,rfl⟩).property

/-- Reconstruction preserves the order of positions carrying the same itinerary. -/
theorem reconstruct_tie (w : Fin n → K) (T : Equiv.Perm K)
    (inv : ∀ s, frequency w (T s) = frequency w s) {i j : Fin n}
    (lt : i < j) (eq : w i = w j) : reconstruct w T inv i < reconstruct w T inv j := by
  rw [reconstruct_apply w T inv i eq, reconstruct_apply w T inv j rfl]
  exact (matchFiber w T inv (w j)).strictMono (show (⟨i,eq⟩ : Fiber w (w j)) < ⟨j,rfl⟩ from lt)

/-- A successor permutation transports one itinerary fiber to the next. -/
def transportFiber (w : Fin n → K) (T : Equiv.Perm K) (σ : Equiv.Perm (Fin n))
    (h : ∀ i, w (σ i) = T (w i)) (s : K) : Fiber w s ≃ Fiber w (T s) where
  toFun i := ⟨σ i.val, (h i.val).trans (congrArg T i.property)⟩
  invFun j := ⟨σ.symm j.val, T.injective (by rw [← h, σ.apply_symm_apply, j.property])⟩
  left_inv i := Subtype.ext (σ.symm_apply_apply _)
  right_inv i := Subtype.ext (σ.apply_symm_apply _)

omit [DecidableEq K] in
/-- A successor permutation makes the fiber cardinalities rotation invariant. -/
theorem shift_frequency (w : Fin n → K) (T : Equiv.Perm K) (σ : Equiv.Perm (Fin n))
    (h : ∀ i, w (σ i) = T (w i)) (s : K) : frequency w (T s) = frequency w s :=
  Nat.card_congr (transportFiber w T σ h s).symm

/-- Any permutation respecting a shift and the order of copies agrees at every position
with the order-preserving matching of the two fibers. -/
theorem reconstruct_unique (w : Fin n → K) (T : Equiv.Perm K) (σ : Equiv.Perm (Fin n))
    (h : ∀ i, w (σ i) = T (w i))
    (tie : ∀ i j, i < j → w i = w j → σ i < σ j) :
    σ = reconstruct w T (shift_frequency w T σ h) := by
  apply Equiv.ext
  intro i
  let e := transportFiber w T σ h (w i)
  have he : StrictMono e := fun a b hab ↦ tie a b hab (a.property.trans b.property.symm)
  let o := he.orderIsoOfRightInverse e e.symm e.apply_symm_apply
  have ho : o = matchFiber w T (shift_frequency w T σ h) (w i) := Subsingleton.elim _ _
  exact congrArg (fun f : Fiber w (w i) ≃o Fiber w (T (w i)) ↦ (f ⟨i,rfl⟩).val) ho

end RealRooted.LongCycleDescents.Necklace

namespace RealRooted.LongCycleDescents.Words
open Function Finset

/-- A rooted word of length n on an alphabet with q letters. -/
abbrev Word (n q : ℕ) := Fin n → Fin q

/-- Read the letter r positions further along the cycle. -/
def shift {n q : ℕ} (r : ℕ) (w : Word n q) : Word n q :=
  fun i ↦ w ⟨(i.val + r) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- Rotation by zero fixes the rooted word. -/
@[simp] theorem shift_zero {n q : ℕ} (w : Word n q) : shift 0 w = w := by
  funext i
  unfold shift
  congr 1
  exact Fin.ext (by simp [Nat.mod_eq_of_lt i.isLt])

/-- Successive rotations add their offsets. -/
theorem shift_add {n q : ℕ} (a b : ℕ) (w : Word n q) :
    shift a (shift b w) = shift (a + b) w := by
  funext i
  unfold shift
  congr 1
  apply Fin.ext
  simp [Nat.mod_add_mod, Nat.add_assoc]

/-- Rotation by the word length fixes the rooted word. -/
@[simp] theorem shift_length {n q : ℕ} (w : Word n q) : shift n w = w := by
  funext i
  unfold shift
  congr 1
  exact Fin.ext (by simp [Nat.mod_eq_of_lt i.isLt])

/-- A rotation depends only on its offset modulo the word length. -/
theorem shift_mod {n q : ℕ} (r : ℕ) (w : Word n q) : shift (r % n) w = shift r w := by
  funext i
  unfold shift
  congr 1
  exact Fin.ext (Nat.add_mod_mod _ _ _)

/-- Iterating unit rotation is rotation by the number of iterations. -/
theorem iterate_shift {n q : ℕ} (r : ℕ) (w : Word n q) :
    (shift 1)^[r] w = shift r w := by
  induction r with
  | zero => simp
  | succ r ih => rw [Function.iterate_succ_apply', ih, shift_add, Nat.add_comm]

/-- The minimal period of the infinite repetition of the rooted word. -/
def period {n q : ℕ} (w : Word n q) : ℕ := Function.minimalPeriod (shift 1) w

/-- The minimal period divides exactly the offsets fixing the rooted word. -/
theorem period_dvd_iff {n q : ℕ} (w : Word n q) (r : ℕ) :
    period w ∣ r ↔ shift r w = w := by
  rw [← iterate_shift r w]
  exact Function.isPeriodicPt_iff_minimalPeriod_dvd.symm

/-- The primitive period divides the word length. -/
theorem period_dvd_length {n q : ℕ} (w : Word n q) : period w ∣ n :=
  (period_dvd_iff w n).mpr (shift_length w)

/-- A nonempty finite word has positive primitive period. -/
theorem period_pos {n q : ℕ} (hn : 0 < n) (w : Word n q) : 0 < period w := by
  have h : IsPeriodicPt (shift 1) n w := by
    change (shift 1)^[n] w = w
    rw [iterate_shift, shift_length]
  exact h.minimalPeriod_pos hn

/-- A primitive rooted word is nonempty and has no shorter cyclic period. -/
def Primitive {n q : ℕ} (w : Word n q) : Prop := 0 < n ∧ period w = n

/-- A nonempty rooted word with no shorter rotation period. -/
abbrev PrimitiveWord (n q : ℕ) := {w : Word n q // Primitive w}

/-- Primitivity is equivalent to having no nontrivial shorter rotation symmetry. -/
theorem primitive_iff_no_short_shift {n q : ℕ} {w : Word n q} (hn : 0 < n) :
    Primitive w ↔ ∀ r : ℕ, 0 < r → r < n → shift r w ≠ w := by
  constructor
  · intro hw r hr lt fixed
    have dvd : n ∣ r := hw.2 ▸ (period_dvd_iff w r).mpr fixed
    exact (not_le_of_gt lt) (Nat.le_of_dvd hr dvd)
  · intro h
    refine ⟨hn, le_antisymm (Nat.le_of_dvd hn (period_dvd_length w)) ?_⟩
    refine le_of_not_gt fun lt ↦ h _ (period_pos hn w) lt ?_
    exact (period_dvd_iff w _).mp (dvd_refl _)

/-- Primitive words form a finite type. -/
noncomputable instance instFintypePrimitiveWord (n q : ℕ) : Fintype (PrimitiveWord n q) :=
  Fintype.ofFinite _

/-- Complementary rotations undo one another. -/
theorem shift_reverse {n q : ℕ} (hn : 0 < n) (r : ℕ) (w : Word n q) :
    shift (n - r % n) (shift r w) = w := by
  rw [← shift_mod r w, shift_add, Nat.sub_add_cancel (Nat.mod_lt r hn).le, shift_length]

/-- Rotation is injective on rooted words of positive length. -/
theorem shift_injective {n q : ℕ} (hn : 0 < n) (r : ℕ) :
    Injective (shift r : Word n q → Word n q) := by
  intro u v h
  simpa only [shift_reverse hn r] using congrArg (shift (n - r % n)) h

/-- Rotation preserves primitivity. -/
theorem primitive_shift {n q : ℕ} {w : Word n q} (hw : Primitive w) (a : ℕ) :
    Primitive (shift a w) := by
  apply (primitive_iff_no_short_shift hw.1).mpr
  intro r hr lt h
  apply (primitive_iff_no_short_shift hw.1).mp hw r hr lt
  apply shift_injective hw.1 a
  simpa only [shift_add, Nat.add_comm r a] using h

/-- Rotate a primitive rooted word without changing its primitive period. -/
def shiftPrimitive {n q : ℕ} (r : ℕ) (w : PrimitiveWord n q) : PrimitiveWord n q :=
  ⟨shift r w.val, primitive_shift w.property r⟩

/-- The equivalence relation of lying in the same cyclic rotation class. -/
def rotationSetoid (n q : ℕ) : Setoid (PrimitiveWord n q) where
  r w v := ∃ r : ℕ, shift r w.val = v.val
  iseqv := by
    refine ⟨fun w ↦ ⟨0, shift_zero w.val⟩, ?_, ?_⟩
    · rintro w v ⟨r, h⟩
      exact ⟨n - r % n, by rw [← h, shift_reverse w.property.1]⟩
    · rintro w v u ⟨a, h₁⟩ ⟨b, h₂⟩
      exact ⟨b + a, by rw [← shift_add, h₁, h₂]⟩

/-- A primitive necklace is a rotation class of primitive rooted words. -/
abbrev PrimitiveNecklace (n q : ℕ) := Quotient (rotationSetoid n q)

/-- Primitive rotation classes form a finite type. -/
noncomputable instance instFintypePrimitiveNecklace (n q : ℕ) :
    Fintype (PrimitiveNecklace n q) := Fintype.ofFinite _

/-- Forget the starting position of a primitive word. -/
def necklaceOf {n q : ℕ} (w : PrimitiveWord n q) : PrimitiveNecklace n q :=
  Quotient.mk (rotationSetoid n q) w

/-- Two primitive words define the same necklace exactly when one is a rotation of the other. -/
theorem necklaceOf_eq_iff {n q : ℕ} {w v : PrimitiveWord n q} :
    necklaceOf w = necklaceOf v ↔ ∃ r : Fin n, shift r.val w.val = v.val := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := (Quotient.exact h : (rotationSetoid n q).r w v)
    exact ⟨⟨r % n, Nat.mod_lt _ w.property.1⟩, (shift_mod r w.val).trans hr⟩
  · rintro ⟨r, hr⟩
    exact Quotient.sound ⟨r.val, hr⟩

private theorem shift_fin_injective {n q : ℕ} (w : PrimitiveWord n q) :
    Injective (fun r : Fin n ↦ shiftPrimitive r.val w) := by
  intro a b h
  have strict {a b : Fin n} (lt : a < b)
      (eq : shift a.val w.val = shift b.val w.val) : False := by
    have recovers : shift a.val (shift (b.val - a.val) w.val) = shift a.val w.val := by
      rw [shift_add, Nat.add_sub_of_le (le_of_lt lt), eq]
    have different := (primitive_iff_no_short_shift w.property.1).mp w.property
      (b.val - a.val) (by exact Nat.sub_pos_of_lt lt)
      ((Nat.sub_le ..).trans_lt b.isLt)
    exact different (shift_injective w.property.1 a.val recovers)
  have eq := congrArg Subtype.val h
  by_contra ne
  rcases lt_or_gt_of_ne ne with lt | lt
  · exact strict lt eq
  · exact strict lt eq.symm

/-- A primitive necklace has as many rooted representatives as its length. -/
theorem card_necklace_fiber {n q : ℕ} (N : PrimitiveNecklace n q) :
    Nat.card {u : PrimitiveWord n q // necklaceOf u = N} = n := by
  refine Quotient.inductionOn N fun w ↦ ?_
  let f (r : Fin n) : {u : PrimitiveWord n q // necklaceOf u = necklaceOf w} :=
    ⟨shiftPrimitive r.val w, ((necklaceOf_eq_iff).mpr ⟨r, rfl⟩).symm⟩
  have inj : Injective f := fun a b h ↦
    shift_fin_injective w (congrArg Subtype.val h)
  have surv : Surjective f := by
    intro u
    obtain ⟨r, hr⟩ := (necklaceOf_eq_iff).mp u.property.symm
    exact ⟨r, Subtype.ext (Subtype.ext hr)⟩
  change Nat.card {u : PrimitiveWord n q // necklaceOf u = necklaceOf w} = n
  rw [Nat.card_congr (Equiv.ofBijective f ⟨inj, surv⟩).symm, Nat.card_fin]

/-- Every primitive necklace of length n has exactly n different rooted words. -/
theorem card_primitiveWord_eq_mul (n q : ℕ) :
    Fintype.card (PrimitiveWord n q) = n * Fintype.card (PrimitiveNecklace n q) := by
  classical
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (@necklaceOf n q)), Fintype.card_sigma]
  have fiber (N : PrimitiveNecklace n q) :
      Fintype.card {u : PrimitiveWord n q // necklaceOf u = N} = n := by
    rw [← Nat.card_eq_fintype_card]
    exact card_necklace_fiber N
  simp [fiber, Nat.mul_comm]

/-- Repeat a rooted word into a word of length n, using its cyclic extension. -/
def repeatWord (n : ℕ) {d q : ℕ} (hd : 0 < d) (u : Word d q) : Word n q :=
  fun i ↦ u ⟨i.val % d, Nat.mod_lt _ hd⟩

/-- Repeating through at least one full period preserves distinct rooted words. -/
theorem repeatWord_injective {d n q : ℕ} (hd : 0 < d) (hle : d ≤ n) :
    Injective (repeatWord n hd : Word d q → Word n q) := by
  intro u v h
  funext i
  have hi := congrFun h (i.castLE hle)
  simpa [repeatWord, Nat.mod_eq_of_lt i.isLt] using hi

/-- Rotation commutes with repetition to a multiple of the original length. -/
theorem shift_repeatWord {d n q : ℕ} (hd : 0 < d) (dvd : d ∣ n) (u : Word d q) (r : ℕ) :
    shift r (repeatWord n hd u) = repeatWord n hd (shift r u) := by
  funext i
  unfold repeatWord shift
  apply congrArg u
  apply Fin.ext
  exact (Nat.mod_mod_of_dvd _ dvd).trans (Nat.mod_add_mod _ _ _).symm

/-- Repeating a primitive word to a multiple of its length preserves its minimal period. -/
theorem period_repeatWord {d n q : ℕ} (hn : 0 < n) (hd : 0 < d) (dvd : d ∣ n)
    (u : Word d q) : period (repeatWord n hd u) = period u := by
  apply Nat.dvd_antisymm
  · apply (period_dvd_iff _ _).mpr
    rw [shift_repeatWord hd dvd, (period_dvd_iff u _).mp (dvd_refl _)]
  · apply (period_dvd_iff _ _).mpr
    apply repeatWord_injective hd (Nat.le_of_dvd hn dvd)
    rw [← shift_repeatWord hd dvd]
    exact (period_dvd_iff _ _).mp (dvd_refl _)

private theorem repeat_take_of_period {d n q : ℕ} (hd : 0 < d) (hle : d ≤ n)
    (w : Word n q) (hper : period w ∣ d) :
    repeatWord n hd (fun i : Fin d ↦ w (i.castLE hle)) = w := by
  funext i
  let r : Fin n := ⟨i.val % d, (Nat.mod_lt _ hd).trans_le hle⟩
  have fixed := (period_dvd_iff w (d * (i.val / d))).mp
    (hper.trans (dvd_mul_right _ _))
  have e := congrFun fixed r
  have index_eq : (⟨(r.val + d * (i.val / d)) % n,
      Nat.mod_lt _ (Nat.zero_lt_of_lt r.isLt)⟩ : Fin n) = i := by
    apply Fin.ext
    change (i.val % d + d * (i.val / d)) % n = i.val
    rw [Nat.mod_add_div, Nat.mod_eq_of_lt i.isLt]
  change w ⟨(r.val + d * (i.val / d)) % n, _⟩ = w r at e
  rw [index_eq] at e
  exact e.symm

/-- The minimal period of a nonempty word, as a divisor of its length. -/
def periodDivisor {n q : ℕ} (hn : 0 < n) (w : Word n q) : n.divisors :=
  ⟨period w, Nat.mem_divisors.mpr ⟨period_dvd_length w, hn.ne'⟩⟩

private def periodFiberEquiv {n : ℕ} (hn : 0 < n) (q : ℕ) (d : n.divisors) :
    {w : Word n q // periodDivisor hn w = d} ≃ PrimitiveWord d.val q := by
  have dvd : d.val ∣ n := Nat.dvd_of_mem_divisors d.property
  have hd : 0 < d.val := Nat.pos_of_mem_divisors d.property
  have hle : d.val ≤ n := Nat.le_of_dvd hn dvd
  let assemble (u : PrimitiveWord d.val q) : {w : Word n q // periodDivisor hn w = d} :=
    ⟨repeatWord n hd u.val, Subtype.ext ((period_repeatWord hn hd dvd u.val).trans u.property.2)⟩
  refine (Equiv.ofBijective assemble ⟨?_, ?_⟩).symm
  · intro u v h
    exact Subtype.ext (repeatWord_injective hd hle (congrArg Subtype.val h))
  · intro w
    have exact_period : period w.val = d.val := congrArg Subtype.val w.property
    let u : Word d.val q := fun i ↦ w.val (i.castLE hle)
    have eq : repeatWord n hd u = w.val := repeat_take_of_period hd hle w.val (dvd_of_eq
      exact_period)
    refine ⟨⟨u, hd, ?_⟩, Subtype.ext eq⟩
    rw [← period_repeatWord hn hd dvd u, eq, exact_period]

/-- Every nonempty word uniquely repeats a primitive rooted word of a divisor length. -/
theorem sum_card_primitiveWord {n : ℕ} (hn : 0 < n) (q : ℕ) :
    (∑ d ∈ n.divisors, Fintype.card (PrimitiveWord d q)) = q ^ n := by
  classical
  have eqv : Word n q ≃ (Σ d : n.divisors, PrimitiveWord d.val q) :=
    (Equiv.sigmaFiberEquiv (periodDivisor hn)).symm.trans
      (Equiv.sigmaCongrRight (periodFiberEquiv hn q))
  have h := Fintype.card_congr eqv
  rw [Fintype.card_sigma, (n.divisors).sum_coe_sort (fun d ↦ Fintype.card (PrimitiveWord d q))] at h
  rw [← h, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

open scoped ArithmeticFunction.Moebius

/-- Möbius inversion of the decomposition by minimal period. -/
theorem card_primitiveWord_moebius {n : ℕ} (hn : 0 < n) (q : ℕ) :
    (Fintype.card (PrimitiveWord n q) : ℤ) =
      ∑ d ∈ n.divisors, μ d * (q : ℤ) ^ (n / d) := by
  let f (j : ℕ) : ℤ := Fintype.card (PrimitiveWord j q)
  let g (j : ℕ) : ℤ := (q : ℤ) ^ j
  have input (j : ℕ) (hj : 0 < j) : (∑ d ∈ j.divisors, f d) = g j := by
    change (∑ d ∈ j.divisors, (Fintype.card (PrimitiveWord d q) : ℤ)) = (q : ℤ) ^ j
    exact_mod_cast sum_card_primitiveWord hj q
  have inverted := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := f) (g := g)).mp
    input n hn
  calc
    f n = ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * g x.2 := by simpa using inverted.symm
    _ = ∑ d ∈ n.divisors, μ d * g (n / d) := Nat.sum_divisorsAntidiagonal (fun a b ↦ μ a * g b)

/-- The number of primitive necklaces times their length is the Möbius power sum. -/
theorem card_primitiveNecklace_mul {n : ℕ} (hn : 0 < n) (q : ℕ) :
    (n : ℤ) * (Fintype.card (PrimitiveNecklace n q) : ℤ) =
      ∑ d ∈ n.divisors, μ d * (q : ℤ) ^ (n / d) := by
  rw [← Int.natCast_mul, ← card_primitiveWord_eq_mul, card_primitiveWord_moebius hn]

/-- The Möbius sum divided by the positive length counts primitive necklaces. -/
theorem card_primitiveNecklace {n : ℕ} (hn : 0 < n) (q : ℕ) :
    (Fintype.card (PrimitiveNecklace n q) : ℤ) =
      (∑ d ∈ n.divisors, μ d * (q : ℤ) ^ (n / d)) / (n : ℤ) := by
  rw [← card_primitiveNecklace_mul hn q, Int.mul_ediv_cancel_left _ (by exact_mod_cast hn.ne')]

/-- Multisets of a fixed size, with repeated choices allowed. -/
theorem card_multisets (α : Type*) [Fintype α] (m : ℕ) :
    Nat.card (Sym α m) = Nat.multichoose (Fintype.card α) m := by
  rw [Sym.natCard_sym_eq_multichoose, Nat.card_eq_fintype_card]

end RealRooted.LongCycleDescents.Words
