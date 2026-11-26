/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Sym.NatCard
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-! Primitive rooted words, their cyclic rotation classes, and fixed-size multisets.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

noncomputable section

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

end
