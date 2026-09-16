import RealRooted.Combinatorics.ComparisonBottom
import RealRooted.Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Comparison-bottom monomials under minimum insertion

This file records insertion identities for squarefree comparison-bottom
monomials.  They are stated for generic positive words with an initial ascent,
independently of any particular combinatorial construction.
-/

namespace RealRooted.MinimumInsertionWord

open scoped BigOperators

/-- A comparison bottom is one of the entries of the word. -/
theorem mem_of_mem_comparisonBottomSupport {w : List Nat} {x : Nat}
    (hx : x ∈ comparisonBottomSupport w) : x ∈ w := by
  induction w with
  | nil => simp [comparisonBottomSupport] at hx
  | cons a w ih =>
      cases w with
      | nil => simp [comparisonBottomSupport] at hx
      | cons b w =>
          rw [comparisonBottomSupport] at hx
          split at hx
          · exact List.mem_cons_of_mem a (ih hx)
          · rw [Finset.mem_insert] at hx
            rcases hx with rfl | hx
            · simp
            · exact List.mem_cons_of_mem a (ih hx)

/-- The head of a nodup word cannot be a comparison bottom. -/
theorem head_not_mem_comparisonBottomSupport {a : Nat} {w : List Nat}
    (hw : (a :: w).Nodup) : a ∉ comparisonBottomSupport (a :: w) := by
  intro ha
  have hamem : a ∈ w := by
    cases w with
    | nil => simp [comparisonBottomSupport] at ha
    | cons b w =>
        rw [comparisonBottomSupport] at ha
        split at ha
        · exact mem_of_mem_comparisonBottomSupport ha
        · rw [Finset.mem_insert] at ha
          rcases ha with hab | ha
          · exact hab ▸ List.mem_cons_self
          · exact mem_of_mem_comparisonBottomSupport ha
  exact (List.nodup_cons.mp hw).1 hamem

/-- Comparison-bottom support is contained in the entries of the word. -/
theorem comparisonBottomSupport_subset_toFinset (w : List Nat) :
    comparisonBottomSupport w ⊆ w.toFinset := by
  intro x hx
  simpa using mem_of_mem_comparisonBottomSupport hx

/-- A nodup word has at most one comparison bottom per entry. -/
theorem card_comparisonBottomSupport_le_length {w : List Nat}
    (hw : w.Nodup) : (comparisonBottomSupport w).card ≤ w.length := by
  calc
    (comparisonBottomSupport w).card ≤ w.toFinset.card :=
      Finset.card_le_card (comparisonBottomSupport_subset_toFinset w)
    _ = w.length := List.toFinset_card_of_nodup hw

/-- Removing the first entry of an initial-ascent word preserves its
comparison-bottom support. -/
theorem comparisonBottomSupport_tail_eq_of_startsWithAscent
    {w : List Nat} (hw : StartsWithAscent w) :
    comparisonBottomSupport w.tail = comparisonBottomSupport w := by
  cases w with
  | nil => simp [StartsWithAscent] at hw
  | cons a w =>
      cases w with
      | nil => simp [StartsWithAscent] at hw
      | cons b w =>
          change a < b at hw
          simp [comparisonBottomSupport, hw]

/-- A bounded old support remains bounded after one valid insertion. -/
theorem mem_comparisonBottomSupport_step_bounds {w : List Nat}
    (hpos : IsPositive w) {r n x : Nat} (hr : r ≤ w.length)
    (hbound : ∀ y ∈ comparisonBottomSupport w, y ≤ n)
    (hx : x ∈ comparisonBottomSupport (step r w)) :
    1 ≤ x ∧ x ≤ n + 1 := by
  have hxpos : 0 < x := by
    apply Nat.pos_of_ne_zero
    intro hxzero
    subst x
    exact zero_not_mem_comparisonBottomSupport (isPositive_step r w) hx
  constructor
  · exact hxpos
  · by_cases hxone : x = 1
    · lia
    · have hxgt : 1 < x := by lia
      have hmem : x - 1 ∈ comparisonBottomSupport w := by
        apply succ_mem_comparisonBottomSupport_step_imp hpos hr (by lia)
        rw [Nat.sub_add_cancel (by lia)]
        exact hx
      have := hbound (x - 1) hmem
      lia

/-- Insertion in the front only shifts the old comparison bottoms. -/
theorem comparisonBottomSupport_step_zero {w : List Nat}
    (hpos : IsPositive w) :
    comparisonBottomSupport (step 0 w) =
      (comparisonBottomSupport w).map succEmbedding := by
  cases w with
  | nil => simp [step, raise, comparisonBottomSupport]
  | cons a w =>
      have ha := hpos a (by simp)
      rw [step_zero]
      simp only [raise, List.map_cons, comparisonBottomSupport]
      rw [if_pos (by lia)]
      change comparisonBottomSupport (raise (a :: w)) = _
      rw [comparisonBottomSupport_raise]

/-- The comparison-bottom monomial of a front insertion is the shifted old
monomial. -/
theorem comparisonBottomMonomial_step_zero
    {R : Type*} [CommSemiring R] {w : List Nat}
    (hpos : IsPositive w) :
    (comparisonBottomMonomial (step 0 w) : MvPolynomial Nat R) =
      MvPolynomial.rename succEmbedding (comparisonBottomMonomial w) := by
  rw [comparisonBottomMonomial, comparisonBottomSupport_step_zero hpos,
    comparisonBottomMonomial]
  exact (MvPolynomial.rename_finsetMonomial (R := R) succEmbedding
    succEmbedding.injective (comparisonBottomSupport w)).symm

/-- Insertion immediately after the head creates bottom `1` and shifts the
comparison bottoms of the tail. -/
theorem comparisonBottomSupport_step_one_cons {a : Nat}
    {w : List Nat} (hpos : IsPositive (a :: w)) :
    comparisonBottomSupport (step 1 (a :: w)) =
      insert 1 ((comparisonBottomSupport w).map succEmbedding) := by
  rw [step_succ, step_zero]
  rw [comparisonBottomSupport, if_neg (by
    have := hpos a (by simp)
    lia)]
  change insert 1 (comparisonBottomSupport (step 0 w)) = _
  rw [comparisonBottomSupport_step_zero]
  intro x hx
  exact hpos x (by simp [hx])

/-- Monomial form of insertion immediately after the head. -/
theorem comparisonBottomMonomial_step_one_cons
    {R : Type*} [CommSemiring R] {a : Nat} {w : List Nat}
    (hpos : IsPositive (a :: w)) :
    (comparisonBottomMonomial (step 1 (a :: w)) : MvPolynomial Nat R) =
      MvPolynomial.X 1 *
        MvPolynomial.rename succEmbedding (comparisonBottomMonomial w) := by
  have hone : 1 ∉ (comparisonBottomSupport w).map succEmbedding := by
    intro hmem
    rw [Finset.mem_map] at hmem
    obtain ⟨x, hx, hxeq⟩ := hmem
    have hxzero : x = 0 := by
      change x + 1 = 1 at hxeq
      lia
    subst x
    exact zero_not_mem_comparisonBottomSupport
      (fun y hy => hpos y (by simp [hy])) hx
  rw [comparisonBottomMonomial,
    comparisonBottomSupport_step_one_cons hpos,
    MvPolynomial.finsetMonomial_insert hone, comparisonBottomMonomial]
  congr 1
  exact (MvPolynomial.rename_finsetMonomial succEmbedding
    succEmbedding.injective (comparisonBottomSupport w)).symm

/-- Insertion after the first two positions preserves the first comparison. -/
theorem comparisonBottomSupport_step_add_two_cons
    (a b r : Nat) (w : List Nat) :
    comparisonBottomSupport (step (r + 2) (a :: b :: w)) =
      if a < b then comparisonBottomSupport (step (r + 1) (b :: w))
      else insert (b + 1)
        (comparisonBottomSupport (step (r + 1) (b :: w))) := by
  rw [show r + 2 = (r + 1) + 1 by lia, step_succ, step_succ]
  simp only [comparisonBottomSupport]
  by_cases hab : a < b
  · rw [if_pos (by lia), if_pos hab]
  · rw [if_neg (by lia), if_neg hab]

/-- Monomial form of insertion after the first two positions. -/
theorem comparisonBottomMonomial_step_add_two_cons
    {R : Type*} [CommSemiring R] {a b r : Nat} {w : List Nat}
    (hpos : IsPositive (a :: b :: w)) (hnodup : (a :: b :: w).Nodup)
    (hr : r + 1 ≤ (b :: w).length) :
    (comparisonBottomMonomial (step (r + 2) (a :: b :: w)) :
        MvPolynomial Nat R) =
      if a < b then comparisonBottomMonomial (step (r + 1) (b :: w))
      else MvPolynomial.X (b + 1) *
        comparisonBottomMonomial (step (r + 1) (b :: w)) := by
  rw [comparisonBottomMonomial,
    comparisonBottomSupport_step_add_two_cons]
  by_cases hab : a < b
  · rw [if_pos hab, if_pos hab, comparisonBottomMonomial]
  · rw [if_neg hab, if_neg hab]
    have hposTail : IsPositive (b :: w) := by
      intro x hx
      exact hpos x (by simp [hx])
    have hnodupTail : (b :: w).Nodup := (List.nodup_cons.mp hnodup).2
    have hstepNodup := nodup_step hnodupTail hposTail hr
    rw [step_succ] at hstepNodup
    have hbnot : b + 1 ∉
        comparisonBottomSupport ((b + 1) :: step r w) :=
      head_not_mem_comparisonBottomSupport hstepNodup
    rw [step_succ]
    rw [MvPolynomial.finsetMonomial_insert hbnot,
      comparisonBottomMonomial]

/-- Prepending one comparison either preserves a monomial or adjoins its
right-hand value. -/
theorem comparisonBottomMonomial_cons_cons
    {R : Type*} [CommSemiring R] {a b : Nat} {w : List Nat}
    (hnodup : (a :: b :: w).Nodup) :
    (comparisonBottomMonomial (a :: b :: w) : MvPolynomial Nat R) =
      if a < b then comparisonBottomMonomial (b :: w)
      else MvPolynomial.X b * comparisonBottomMonomial (b :: w) := by
  rw [comparisonBottomMonomial, comparisonBottomSupport]
  by_cases hab : a < b
  · rw [if_pos hab, if_pos hab, comparisonBottomMonomial]
  · rw [if_neg hab, if_neg hab]
    have htail : (b :: w).Nodup := (List.nodup_cons.mp hnodup).2
    rw [MvPolynomial.finsetMonomial_insert
      (head_not_mem_comparisonBottomSupport htail),
      comparisonBottomMonomial]

/-- The comparison-bottom enumerator over all positive insertion slots. -/
noncomputable def positiveInsertionPolynomial
    {R : Type*} [CommSemiring R] (w : List Nat) : MvPolynomial Nat R :=
  ∑ r : Fin w.length,
    comparisonBottomMonomial (step (r.1 + 1) w)

/-- Splitting the positive insertion slots at the head gives a triangular
recurrence on words. -/
theorem positiveInsertionPolynomial_cons
    {R : Type*} [CommSemiring R] {a : Nat} {w : List Nat}
    (hpos : IsPositive (a :: w)) (hnodup : (a :: w).Nodup) :
    positiveInsertionPolynomial (R := R) (a :: w) =
      MvPolynomial.X 1 *
          MvPolynomial.rename succEmbedding (comparisonBottomMonomial w) +
        match w with
        | [] => 0
        | b :: t =>
            (if a < b then 1 else MvPolynomial.X (b + 1)) *
              positiveInsertionPolynomial (b :: t) := by
  cases w with
  | nil =>
      rw [positiveInsertionPolynomial]
      simp only [List.length_cons, List.length_nil]
      rw [Fin.sum_univ_succ]
      simp [comparisonBottomMonomial_step_one_cons hpos]
  | cons b w =>
      rw [positiveInsertionPolynomial]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      rw [show comparisonBottomMonomial
          (step ((0 : Fin ((b :: w).length + 1)).1 + 1) (a :: b :: w)) =
          MvPolynomial.X 1 *
            MvPolynomial.rename succEmbedding
              (comparisonBottomMonomial (b :: w)) by
        simpa using comparisonBottomMonomial_step_one_cons (R := R) hpos]
      change _ +
          (∑ r : Fin (b :: w).length,
            comparisonBottomMonomial
              (step (r.1 + 2) (a :: b :: w))) = _
      by_cases hab : a < b
      · simp only [hab, if_pos, one_mul]
        rw [positiveInsertionPolynomial]
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        exact comparisonBottomMonomial_step_add_two_cons
          (R := R) hpos hnodup (by simpa using r.isLt) |>.trans
            (if_pos hab)
      · simp only [List.length_cons, if_neg hab]
        rw [positiveInsertionPolynomial, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        exact comparisonBottomMonomial_step_add_two_cons
          (R := R) hpos hnodup (by simpa using r.isLt) |>.trans
            (if_neg hab)

/-- The support normal form for the positive-slot insertion sum. -/
noncomputable def comparisonBottomInsertionCore
    {R : Type*} [CommSemiring R] (w : List Nat) : MvPolynomial Nat R :=
  MvPolynomial.C
      (((w.length - (comparisonBottomSupport w).card : Nat) : R)) *
      comparisonBottomMonomial w +
    ∑ x ∈ comparisonBottomSupport w,
      MvPolynomial.finsetMonomial ((comparisonBottomSupport w).erase x)

/-- Differential form of the insertion core. -/
theorem comparisonBottomInsertionCore_eq_pderiv
    {R : Type*} [CommSemiring R] (w : List Nat) :
    comparisonBottomInsertionCore (R := R) w =
      MvPolynomial.C
          (((w.length - (comparisonBottomSupport w).card : Nat) : R)) *
          comparisonBottomMonomial w +
        ∑ x ∈ comparisonBottomSupport w,
          MvPolynomial.pderiv x (comparisonBottomMonomial w) := by
  rw [comparisonBottomInsertionCore]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [comparisonBottomMonomial]
  change (∏ z ∈ (comparisonBottomSupport w).erase x,
      MvPolynomial.X z : MvPolynomial Nat R) =
    MvPolynomial.pderiv x
      (∏ z ∈ comparisonBottomSupport w, MvPolynomial.X z)
  rw [MvPolynomial.pderiv_finsetProd_X, if_pos hx]

@[simp] theorem comparisonBottomInsertionCore_singleton
    {R : Type*} [CommSemiring R] (a : Nat) :
    comparisonBottomInsertionCore (R := R) [a] = 1 := by
  simp [comparisonBottomInsertionCore, comparisonBottomSupport,
    comparisonBottomMonomial]

/-- The insertion core obeys the same triangular recurrence as the positive
slot sum, before the shift of variable labels. -/
theorem comparisonBottomInsertionCore_cons_cons
    {R : Type*} [CommSemiring R] {a b : Nat} {w : List Nat}
    (hnodup : (a :: b :: w).Nodup) :
    comparisonBottomInsertionCore (R := R) (a :: b :: w) =
      comparisonBottomMonomial (b :: w) +
        (if a < b then 1 else MvPolynomial.X b) *
          comparisonBottomInsertionCore (b :: w) := by
  classical
  have htail : (b :: w).Nodup := (List.nodup_cons.mp hnodup).2
  have hbnot := head_not_mem_comparisonBottomSupport htail
  have hcard := card_comparisonBottomSupport_le_length htail
  by_cases hab : a < b
  · rw [comparisonBottomInsertionCore]
    rw [comparisonBottomSupport, if_pos hab]
    rw [comparisonBottomInsertionCore]
    simp only [hab, if_pos, one_mul]
    have hdiff :
        (a :: b :: w).length -
            (comparisonBottomSupport (b :: w)).card =
          ((b :: w).length -
            (comparisonBottomSupport (b :: w)).card) + 1 := by
      change (b :: w).length.succ -
          (comparisonBottomSupport (b :: w)).card = _
      exact Nat.succ_sub hcard
    rw [hdiff, Nat.cast_add, Nat.cast_one, map_add]
    rw [comparisonBottomMonomial_cons_cons hnodup, if_pos hab]
    simp only [map_one]
    ring
  · rw [comparisonBottomInsertionCore]
    rw [comparisonBottomSupport, if_neg hab]
    rw [comparisonBottomInsertionCore]
    simp only [hab, if_false]
    rw [Finset.card_insert_of_notMem hbnot]
    have hdiff :
        (a :: b :: w).length -
            ((comparisonBottomSupport (b :: w)).card + 1) =
          (b :: w).length -
            (comparisonBottomSupport (b :: w)).card := by
      change (b :: w).length.succ -
          (comparisonBottomSupport (b :: w)).card.succ = _
      exact Nat.succ_sub_succ_eq_sub _ _
    rw [hdiff]
    rw [comparisonBottomMonomial_cons_cons hnodup, if_neg hab]
    rw [Finset.sum_insert hbnot]
    simp only [Finset.erase_insert_eq_erase]
    rw [Finset.erase_eq_of_notMem hbnot]
    have hsum :
        (∑ x ∈ comparisonBottomSupport (b :: w),
            MvPolynomial.finsetMonomial
              ((insert b (comparisonBottomSupport (b :: w))).erase x) :
              MvPolynomial Nat R) =
          MvPolynomial.X b *
            ∑ x ∈ comparisonBottomSupport (b :: w),
              MvPolynomial.finsetMonomial
                ((comparisonBottomSupport (b :: w)).erase x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have hbx : b ≠ x := fun h => hbnot (h ▸ hx)
      rw [Finset.erase_insert_of_ne hbx]
      rw [MvPolynomial.finsetMonomial_insert]
      intro hbErase
      exact hbnot (Finset.mem_of_mem_erase hbErase)
    rw [hsum]
    rw [comparisonBottomMonomial]
    ring

/-- The positive-slot insertion sum is the shifted support normal form. -/
theorem positiveInsertionPolynomial_eq_core
    {R : Type*} [CommSemiring R] {w : List Nat}
    (hpos : IsPositive w) (hnodup : w.Nodup) :
    positiveInsertionPolynomial (R := R) w =
      MvPolynomial.X 1 *
        MvPolynomial.rename succEmbedding
          (comparisonBottomInsertionCore w) := by
  induction w with
  | nil => simp [positiveInsertionPolynomial,
      comparisonBottomInsertionCore, comparisonBottomSupport,
      comparisonBottomMonomial]
  | cons a w ih =>
      rw [positiveInsertionPolynomial_cons hpos hnodup]
      cases w with
      | nil =>
          rw [comparisonBottomInsertionCore_singleton]
          simp [comparisonBottomMonomial, comparisonBottomSupport]
      | cons b w =>
          have hposTail : IsPositive (b :: w) := by
            intro x hx
            exact hpos x (by simp [hx])
          have hnodupTail : (b :: w).Nodup :=
            (List.nodup_cons.mp hnodup).2
          change MvPolynomial.X 1 *
                MvPolynomial.rename succEmbedding
                  (comparisonBottomMonomial (b :: w)) +
              (if a < b then 1 else MvPolynomial.X (b + 1)) *
                positiveInsertionPolynomial (b :: w) = _
          rw [ih hposTail hnodupTail,
            comparisonBottomInsertionCore_cons_cons hnodup]
          rw [map_add, map_mul]
          by_cases hab : a < b
          · simp [hab]
            ring
          · simp [hab, MvPolynomial.rename_X, succEmbedding]
            ring

/-- Excluding slot one from an initial-ascent word leaves the front slot and
the positive-slot insertion sum of its tail. -/
theorem sum_nonOne_comparisonBottomMonomial_step
    {R : Type*} [CommRing R] {a b : Nat} {w : List Nat}
    (hpos : IsPositive (a :: b :: w)) (hnodup : (a :: b :: w).Nodup)
    (hab : a < b) :
    (∑ r : {r : Fin ((a :: b :: w).length + 1) // r ≠ 1},
        comparisonBottomMonomial (R := R) (step r.1 (a :: b :: w))) =
      MvPolynomial.rename succEmbedding
          (comparisonBottomMonomial (R := R) (a :: b :: w)) +
        MvPolynomial.X 1 *
          MvPolynomial.rename succEmbedding
            (comparisonBottomInsertionCore (R := R) (b :: w)) := by
  let f : Fin ((a :: b :: w).length + 1) → MvPolynomial Nat R :=
    fun r => comparisonBottomMonomial (step r.1 (a :: b :: w))
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne f
    (1 : Fin ((a :: b :: w).length + 1))
  have htotal :
      (∑ r, f r) = f 0 +
        positiveInsertionPolynomial (R := R) (a :: b :: w) := by
    rw [Fin.sum_univ_succ]
    rfl
  have htailPos : IsPositive (b :: w) := by
    intro x hx
    exact hpos x (by simp [hx])
  have htailNodup : (b :: w).Nodup :=
    (List.nodup_cons.mp hnodup).2
  have hpositive := positiveInsertionPolynomial_cons
    (R := R) hpos hnodup
  change positiveInsertionPolynomial (R := R) (a :: b :: w) =
      MvPolynomial.X 1 *
          MvPolynomial.rename succEmbedding
            (comparisonBottomMonomial (b :: w)) +
        (if a < b then 1 else MvPolynomial.X (b + 1)) *
          positiveInsertionPolynomial (b :: w) at hpositive
  rw [if_pos hab, one_mul,
    positiveInsertionPolynomial_eq_core htailPos htailNodup] at hpositive
  have hzero := comparisonBottomMonomial_step_zero (R := R) hpos
  have hone := comparisonBottomMonomial_step_one_cons (R := R) hpos
  have hmonomial := comparisonBottomMonomial_cons_cons (R := R) hnodup
  rw [if_pos hab] at hmonomial
  change f 0 = MvPolynomial.rename succEmbedding
    (comparisonBottomMonomial (R := R) (a :: b :: w)) at hzero
  change f (1 : Fin ((a :: b :: w).length + 1)) =
    MvPolynomial.X 1 * MvPolynomial.rename succEmbedding
      (comparisonBottomMonomial (R := R) (b :: w)) at hone
  change (∑ r : {r // r ≠
      (1 : Fin ((a :: b :: w).length + 1))}, f r.1) = _
  rw [hmonomial]
  rw [htotal, hpositive, hzero] at hsplit
  rw [hmonomial] at hsplit
  change _ = f (1 : Fin ((a :: b :: w).length + 1)) +
    ∑ r : {r // r ≠ (1 : Fin ((a :: b :: w).length + 1))},
      f r.1 at hsplit
  rw [hone] at hsplit
  apply add_left_cancel (a := MvPolynomial.X 1 *
    MvPolynomial.rename succEmbedding
      (comparisonBottomMonomial (R := R) (b :: w)))
  simpa [add_assoc, add_comm, add_left_comm] using hsplit.symm

/-- Value-level form of the non-one-slot insertion identity. -/
theorem sum_val_ne_one_comparisonBottomMonomial_step
    {R : Type*} [CommRing R] {a b : Nat} {w : List Nat}
    (hpos : IsPositive (a :: b :: w)) (hnodup : (a :: b :: w).Nodup)
    (hab : a < b) :
    (∑ r : {r : Fin ((a :: b :: w).length + 1) // (r : Nat) ≠ 1},
        comparisonBottomMonomial (R := R) (step r.1 (a :: b :: w))) =
      MvPolynomial.rename succEmbedding
          (comparisonBottomMonomial (R := R) (a :: b :: w)) +
        MvPolynomial.X 1 *
          MvPolynomial.rename succEmbedding
            (comparisonBottomInsertionCore (R := R) (b :: w)) := by
  let e :
      {r : Fin ((a :: b :: w).length + 1) // (r : Nat) ≠ 1} ≃
        {r : Fin ((a :: b :: w).length + 1) // r ≠ 1} := {
    toFun := fun r => ⟨r.1, by
      intro hr
      apply r.2
      simpa using congrArg Fin.val hr⟩
    invFun := fun r => ⟨r.1, by
      intro hr
      apply r.2
      apply Fin.ext
      simpa using hr⟩
    left_inv := fun r => Subtype.ext rfl
    right_inv := fun r => Subtype.ext rfl }
  calc
    (∑ r : {r : Fin ((a :: b :: w).length + 1) // (r : Nat) ≠ 1},
        comparisonBottomMonomial (R := R) (step r.1 (a :: b :: w))) =
        ∑ r : {r : Fin ((a :: b :: w).length + 1) // r ≠ 1},
          comparisonBottomMonomial (R := R)
            (step r.1 (a :: b :: w)) := by
      apply Fintype.sum_equiv e
      intro r
      rfl
    _ = _ := sum_nonOne_comparisonBottomMonomial_step hpos hnodup hab

/-- Intrinsic form of the non-one-slot identity for a word with an initial
ascent. -/
theorem sum_val_ne_one_comparisonBottomMonomial_step_of_startsWithAscent
    {R : Type*} [CommRing R] {w : List Nat}
    (hpos : IsPositive w) (hnodup : w.Nodup) (hw : StartsWithAscent w) :
    (∑ r : {r : Fin (w.length + 1) // (r : Nat) ≠ 1},
        comparisonBottomMonomial (R := R) (step r.1 w)) =
      MvPolynomial.rename succEmbedding
          (comparisonBottomMonomial (R := R) w) +
        MvPolynomial.X 1 *
          MvPolynomial.rename succEmbedding
            (comparisonBottomInsertionCore (R := R) w.tail) := by
  cases w with
  | nil => simp [StartsWithAscent] at hw
  | cons a w =>
      cases w with
      | nil => simp [StartsWithAscent] at hw
      | cons b w =>
          exact sum_val_ne_one_comparisonBottomMonomial_step
            hpos hnodup hw

/-- An exceptional pair shifts every old comparison bottom by two and adds
the new bottom `2`. -/
theorem comparisonBottomSupport_exceptional_pair {w : List Nat}
    (hw : StartsWithAscent w) :
    comparisonBottomSupport (step 0 (step 1 w)) =
      insert 2
        ((comparisonBottomSupport w).map
          (succEmbedding.trans succEmbedding)) := by
  cases w with
  | nil => simp [StartsWithAscent] at hw
  | cons a w =>
    cases w with
    | nil => simp [StartsWithAscent] at hw
    | cons b w =>
      change a < b at hw
      rw [step_exceptional_pair]
      simp only [comparisonBottomSupport]
      rw [if_pos (by lia), if_neg (by lia), if_pos (by lia)]
      simp only [List.map_cons]
      change insert 2
          (if 2 < b + 2 then
            comparisonBottomSupport ((b + 2) :: w.map (fun x => x + 2))
          else insert (b + 2)
            (comparisonBottomSupport ((b + 2) :: w.map (fun x => x + 2)))) = _
      rw [if_pos (by lia)]
      have hmap :
          (b :: w).map (fun x => x + 2) = raise (raise (b :: w)) := by
        simp [raise, Nat.add_assoc]
      change insert 2
        (comparisonBottomSupport ((b :: w).map (fun x => x + 2))) = _
      rw [hmap, comparisonBottomSupport_raise,
        comparisonBottomSupport_raise, Finset.map_map]

/-- The exceptional pair shifts a bounded support by two and adds bottom two. -/
theorem mem_comparisonBottomSupport_exceptional_pair_bounds
    {w : List Nat} (hw : StartsWithAscent w) {n x : Nat}
    (hbound : ∀ y ∈ comparisonBottomSupport w, y ≤ n)
    (hx : x ∈ comparisonBottomSupport (step 0 (step 1 w))) :
    1 ≤ x ∧ x ≤ n + 2 := by
  rw [comparisonBottomSupport_exceptional_pair hw,
    Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · lia
  · rw [Finset.mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    change y + 2 = x at hxy
    subst x
    have := hbound y hy
    constructor <;> lia

/-- The comparison-bottom monomial of an exceptional pair is the shifted old
monomial times the new bottom variable `X 2`. -/
theorem comparisonBottomMonomial_exceptional_pair
    {R : Type*} [CommSemiring R] {w : List Nat}
    (hpos : IsPositive w) (hw : StartsWithAscent w) :
    (comparisonBottomMonomial (step 0 (step 1 w)) : MvPolynomial Nat R) =
      MvPolynomial.X 2 *
        MvPolynomial.rename (succEmbedding.trans succEmbedding)
          (comparisonBottomMonomial w) := by
  have htwo : 2 ∉
      (comparisonBottomSupport w).map
        (succEmbedding.trans succEmbedding) := by
    intro hmem
    rw [Finset.mem_map] at hmem
    obtain ⟨x, hx, hxeq⟩ := hmem
    have hxzero : x = 0 := by
      change x + 2 = 2 at hxeq
      lia
    subst x
    exact zero_not_mem_comparisonBottomSupport hpos hx
  rw [comparisonBottomMonomial,
    comparisonBottomSupport_exceptional_pair hw,
    MvPolynomial.finsetMonomial_insert htwo]
  congr 1
  rw [comparisonBottomMonomial]
  exact (MvPolynomial.rename_finsetMonomial
    (succEmbedding.trans succEmbedding)
      (succEmbedding.trans succEmbedding).injective
        (comparisonBottomSupport w)).symm

end RealRooted.MinimumInsertionWord
