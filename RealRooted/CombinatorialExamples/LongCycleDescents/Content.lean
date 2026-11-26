/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.InventoryMass
public import RealRooted.CombinatorialExamples.LongCycleDescents.LabelCount
import Mathlib.Tactic

/-! The cycle-length restricted Gessel--Reutenauer correspondence in multiplicity form.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

open scoped Classical

noncomputable section
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

end
