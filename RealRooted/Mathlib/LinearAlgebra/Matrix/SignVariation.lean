module

public import Mathlib.Algebra.Polynomial.RuleOfSigns
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Tactic
public import RealRooted.Mathlib.Data.List.Destutter
public import RealRooted.Mathlib.Data.List.Basic
public import RealRooted.Mathlib.Data.List.OfFn

/-!
# Sign variations of finite vectors

This file extends the sign-variation convention used by
`Polynomial.signVariations` to lists and finite vectors.  Zero entries are
discarded before adjacent equal signs are collapsed.
-/

public section

noncomputable section

namespace SignType

lemma sign_neg_real (x : ℝ) : SignType.sign (-x) = -SignType.sign x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  rcases lt_or_gt_of_ne hx0 with hx | hx
  · have hneg : 0 < -x := by linarith
    rw [sign_pos hneg, sign_neg hx]
    simp
  · have hneg : -x < 0 := by linarith
    rw [sign_neg hneg, sign_pos hx]

end SignType

namespace List

/-- The number of sign changes in a list, ignoring zero entries. -/
def signVariations {R : Type*} [Zero R] [LinearOrder R] (l : List R) : ℕ :=
  (((l.map SignType.sign).filter (· ≠ 0)).destutter (· ≠ ·)).length - 1

@[simp]
lemma signVariations_nil {R : Type*} [Zero R] [LinearOrder R] :
    signVariations ([] : List R) = 0 := by
  simp [signVariations]

/-- A list has at most one fewer sign variation than its length. -/
lemma signVariations_le_length_sub_one {R : Type*} [Zero R] [LinearOrder R]
    (l : List R) : l.signVariations ≤ l.length - 1 := by
  rw [List.signVariations]
  apply Nat.sub_le_sub_right
  have hdest : ((l.map SignType.sign).filter (· ≠ 0)).destutter (· ≠ ·) <+
      (l.map SignType.sign).filter (· ≠ 0) :=
    List.destutter_sublist (R := (· ≠ ·)) _
  have hfilter : (l.map SignType.sign).filter (· ≠ 0) <+ l.map SignType.sign :=
    List.filter_sublist
  have hmap : (l.map SignType.sign).length = l.length := by simp
  exact hdest.length_le.trans (hfilter.length_le.trans (by simp [hmap]))

lemma length_filter_sign_ne_zero_le_length_sub_one {R : Type*} [Zero R] [LinearOrder R]
    {l : List R} (hl : l ≠ []) (hfirst : SignType.sign (List.head l hl) = 0) :
    ((l.map SignType.sign).filter (· ≠ 0)).length ≤ l.length - 1 := by
  have hlt : ((l.map SignType.sign).filter (· ≠ 0)).length <
      (l.map SignType.sign).length := by
    rw [List.length_filter_lt_length_iff_exists]
    exact ⟨SignType.sign (List.head l hl),
      List.mem_map.mpr ⟨List.head l hl, List.head_mem hl, rfl⟩, by
        simp [hfirst]⟩
  simpa using Nat.le_pred_of_lt (by simpa using hlt)

/-- If the first entry is zero, a list has at most two fewer sign variations
than its length. -/
lemma signVariations_le_length_sub_two_of_head_zero {R : Type*}
    [Zero R] [LinearOrder R] {l : List R} (hl : l ≠ [])
    (hfirst : SignType.sign (List.head l hl) = 0) :
    l.signVariations ≤ l.length - 2 := by
  rw [List.signVariations]
  apply Nat.sub_le_sub_right
  have hdest : ((l.map SignType.sign).filter (· ≠ 0)).destutter (· ≠ ·) <+
      (l.map SignType.sign).filter (· ≠ 0) :=
    List.destutter_sublist (R := (· ≠ ·)) _
  exact hdest.length_le.trans
    (length_filter_sign_ne_zero_le_length_sub_one hl hfirst)

lemma length_destutter'_replicate_signType (s : SignType) (n : ℕ) :
    (destutter' (fun x y : SignType => x ≠ y) s (replicate n s)).length = 1 := by
  induction n with
  | zero => simp [List.destutter'_nil]
  | succ n ih =>
      change (destutter' (fun x y : SignType => x ≠ y) s
        (s :: replicate n s)).length = 1
      rw [List.destutter'_cons]
      simp [ih]

lemma length_destutter_replicate_signType (s : SignType) (n : ℕ) :
    ((replicate (n + 1) s).destutter (· ≠ ·)).length = 1 := by
  change (destutter' (fun x y : SignType => x ≠ y) s (replicate n s)).length = 1
  exact length_destutter'_replicate_signType s n

lemma length_destutter'_replicate_one_signType (n : ℕ) :
    (destutter' (fun x y : SignType => x ≠ y) (1 : SignType)
      (replicate n (1 : SignType))).length = 1 :=
  length_destutter'_replicate_signType 1 n

lemma length_destutter_replicate_one_signType (n : ℕ) :
    ((replicate (n + 1) (1 : SignType)).destutter (· ≠ ·)).length = 1 := by
  exact length_destutter_replicate_signType 1 n

lemma length_destutter'_replicate_le_two (a s : SignType) (n : ℕ) :
    (destutter' (fun x y : SignType => x ≠ y) a (replicate n s)).length ≤ 2 := by
  cases n with
  | zero => simp [List.destutter'_nil]
  | succ n =>
      change (destutter' (fun x y : SignType => x ≠ y) a
        (s :: replicate n s)).length ≤ 2
      rw [List.destutter'_cons]
      by_cases has : a ≠ s
      · rw [if_pos has]
        simp [length_destutter'_replicate_signType]
      · have has_eq : a = s := of_not_not has
        subst a
        rw [if_neg (by simp)]
        rw [length_destutter'_replicate_signType s n]
        norm_num

lemma length_destutter'_append_replicate_le_succ (a s : SignType)
    (l : List SignType) (n : ℕ) :
    (destutter' (fun x y : SignType => x ≠ y) a (l ++ replicate n s)).length ≤
      (destutter' (fun x y : SignType => x ≠ y) a l).length + 1 := by
  induction l generalizing a with
  | nil =>
      simpa [List.destutter'_nil] using length_destutter'_replicate_le_two a s n
  | cons b l ih =>
      simp only [List.cons_append]
      rw [List.destutter'_cons, List.destutter'_cons]
      by_cases hab : a ≠ b
      · rw [if_pos hab, if_pos hab]
        have h := ih b
        simpa [Nat.succ_eq_add_one, add_assoc] using Nat.succ_le_succ h
      · rw [if_neg hab, if_neg hab]
        exact ih a

lemma length_destutter_append_replicate_le_succ (s : SignType)
    (l : List SignType) (n : ℕ) :
    ((l ++ replicate n s).destutter (· ≠ ·)).length ≤
      (l.destutter (· ≠ ·)).length + 1 := by
  cases l with
  | nil =>
      cases n with
      | zero => simp
      | succ n =>
          simp only [List.nil_append]
          rw [length_destutter_replicate_signType s n]
          simp
  | cons a l =>
      exact length_destutter'_append_replicate_le_succ a s l n

lemma length_destutter'_one_replicate_one_append_neg_one_le_two (m n : ℕ) :
    (destutter' (fun x y : SignType => x ≠ y) (1 : SignType)
      (replicate m (1 : SignType) ++ replicate (n + 1) (-1 : SignType))).length ≤ 2 := by
  induction m with
  | zero =>
      change (destutter' (fun x y : SignType => x ≠ y) (1 : SignType)
        ((-1 : SignType) :: replicate n (-1 : SignType))).length ≤ 2
      rw [List.destutter'_cons]
      simp [length_destutter'_replicate_signType]
  | succ m ih =>
      change (destutter' (fun x y : SignType => x ≠ y) (1 : SignType)
        ((1 : SignType) :: (replicate m (1 : SignType) ++
          replicate (n + 1) (-1 : SignType)))).length ≤ 2
      rw [List.destutter'_cons]
      simp [ih]

lemma length_destutter_replicate_one_append_neg_one_le_two (m n : ℕ) :
    ((replicate m (1 : SignType) ++ replicate n (-1 : SignType)).destutter
      (· ≠ ·)).length ≤ 2 := by
  cases m with
  | zero =>
      cases n with
      | zero => simp
      | succ n =>
          simpa using (by
            rw [length_destutter_replicate_signType (-1 : SignType) n]
            norm_num : ((replicate (n + 1) (-1 : SignType)).destutter
              (· ≠ ·)).length ≤ 2)
  | succ m =>
      cases n with
      | zero =>
          simpa using (by
            rw [length_destutter_replicate_signType (1 : SignType) m]
            norm_num : ((replicate (m + 1) (1 : SignType)).destutter
              (· ≠ ·)).length ≤ 2)
      | succ n =>
          change (destutter' (fun x y : SignType => x ≠ y) (1 : SignType)
            (replicate m (1 : SignType) ++ replicate (n + 1) (-1 : SignType))).length ≤
              2
          exact length_destutter'_one_replicate_one_append_neg_one_le_two m n

lemma filter_sign_eq_replicate_one_of_forall_nonneg (l : List ℝ)
    (h : ∀ x ∈ l, 0 ≤ x) :
    (l.map SignType.sign).filter (· ≠ 0) =
      replicate ((l.map SignType.sign).filter (· ≠ 0)).length (1 : SignType) := by
  apply List.eq_replicate_of_mem
  intro s hs
  have hs_filter := List.mem_filter.mp hs
  rcases hs_filter with ⟨hsmem, hsne_bool⟩
  simp only [List.mem_map] at hsmem
  rcases hsmem with ⟨x, hx, rfl⟩
  have hsne : SignType.sign x ≠ 0 := of_decide_eq_true hsne_bool
  have hx_ne : x ≠ 0 := sign_ne_zero.mp hsne
  have hx_pos : 0 < x := lt_of_le_of_ne (h x hx) (Ne.symm hx_ne)
  exact sign_eq_one_iff.mpr hx_pos

lemma filter_sign_eq_replicate_neg_one_of_forall_nonpos (l : List ℝ)
    (h : ∀ x ∈ l, x ≤ 0) :
    (l.map SignType.sign).filter (· ≠ 0) =
      replicate ((l.map SignType.sign).filter (· ≠ 0)).length (-1 : SignType) := by
  apply List.eq_replicate_of_mem
  intro s hs
  have hs_filter := List.mem_filter.mp hs
  rcases hs_filter with ⟨hsmem, hsne_bool⟩
  simp only [List.mem_map] at hsmem
  rcases hsmem with ⟨x, hx, rfl⟩
  have hsne : SignType.sign x ≠ 0 := of_decide_eq_true hsne_bool
  have hx_ne : x ≠ 0 := sign_ne_zero.mp hsne
  have hx_neg : x < 0 := lt_of_le_of_ne (h x hx) hx_ne
  exact sign_eq_neg_one_iff.mpr hx_neg

/-- A list of real numbers with no negative entries has no sign variations. -/
lemma signVariations_eq_zero_of_forall_nonneg (l : List ℝ)
    (h : ∀ x ∈ l, 0 ≤ x) : l.signVariations = 0 := by
  rw [List.signVariations]
  have hmap := filter_sign_eq_replicate_one_of_forall_nonneg l h
  rw [hmap]
  cases ((l.map SignType.sign).filter (· ≠ 0)).length <;>
    simp [length_destutter_replicate_one_signType]

/-- A nonnegative block followed by a nonpositive block has at most one sign
variation. -/
lemma signVariations_append_nonneg_nonpos_le_one (l₁ l₂ : List ℝ)
    (h₁ : ∀ x ∈ l₁, 0 ≤ x) (h₂ : ∀ x ∈ l₂, x ≤ 0) :
    (l₁ ++ l₂).signVariations ≤ 1 := by
  rw [List.signVariations]
  simp only [List.map_append, List.filter_append]
  rw [filter_sign_eq_replicate_one_of_forall_nonneg l₁ h₁,
    filter_sign_eq_replicate_neg_one_of_forall_nonpos l₂ h₂]
  have hlen := length_destutter_replicate_one_append_neg_one_le_two
    ((l₁.map SignType.sign).filter (· ≠ 0)).length
    ((l₂.map SignType.sign).filter (· ≠ 0)).length
  lia

/-- Appending a nonnegative block increases sign variations by at most one. -/
lemma signVariations_append_nonneg_le_succ (l₁ l₂ : List ℝ)
    (h₂ : ∀ x ∈ l₂, 0 ≤ x) :
    (l₁ ++ l₂).signVariations ≤ l₁.signVariations + 1 := by
  rw [List.signVariations, List.signVariations]
  simp only [List.map_append, List.filter_append]
  rw [filter_sign_eq_replicate_one_of_forall_nonneg l₂ h₂]
  have hlen := length_destutter_append_replicate_le_succ (1 : SignType)
    ((l₁.map SignType.sign).filter (· ≠ 0))
    ((l₂.map SignType.sign).filter (· ≠ 0)).length
  lia

lemma length_destutter'_map_neg_signType (s : SignType) (l : List SignType) :
    (destutter' (· ≠ ·) (-s) (l.map Neg.neg)).length =
      (destutter' (· ≠ ·) s l).length := by
  induction l generalizing s with
  | nil => simp [List.destutter'_nil]
  | cons t l ih =>
      rw [List.map_cons, List.destutter'_cons, List.destutter'_cons]
      by_cases hst : s ≠ t
      · have hneg : -s ≠ -t := by
          intro h
          exact hst (neg_inj.mp h)
        rw [if_pos hneg, if_pos hst]
        simp [ih]
      · have hst_eq : s = t := of_not_not hst
        have hneg : ¬ -s ≠ -t := by
          intro h
          exact h (by rw [hst_eq])
        rw [if_neg hneg, if_neg hst]
        exact ih s

lemma length_destutter_map_neg_signType (l : List SignType) :
    ((l.map Neg.neg).destutter (· ≠ ·)).length =
      (l.destutter (· ≠ ·)).length := by
  cases l with
  | nil => simp [List.destutter_nil]
  | cons s l =>
      rw [List.map_cons, List.destutter_cons', List.destutter_cons']
      exact length_destutter'_map_neg_signType s l

lemma signVariations_neg (l : List ℝ) :
    (l.map Neg.neg).signVariations = l.signVariations := by
  rw [List.signVariations, List.signVariations]
  let signs : List SignType := l.map SignType.sign
  have hmap : (l.map Neg.neg).map SignType.sign = signs.map Neg.neg := by
    calc
      (l.map Neg.neg).map SignType.sign =
          l.map (fun x => SignType.sign (-x)) := by simp [List.map_map]
      _ = l.map (fun x => -SignType.sign x) := by
          apply List.map_congr_left
          intro x _
          exact SignType.sign_neg_real x
      _ = signs.map Neg.neg := by simp [signs, List.map_map]
  rw [hmap]
  have hfilter : (signs.map Neg.neg).filter (· ≠ 0) =
      (signs.filter (· ≠ 0)).map Neg.neg := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro s _
    simp
  rw [hfilter]
  exact congrArg (fun m : ℕ => m - 1)
    (List.length_destutter_map_neg_signType (signs.filter (· ≠ 0)))

/-- A list of real numbers with no positive entries has no sign variations. -/
lemma signVariations_eq_zero_of_forall_nonpos (l : List ℝ)
    (h : ∀ x ∈ l, x ≤ 0) : l.signVariations = 0 := by
  have hnonneg : ∀ x ∈ l.map Neg.neg, 0 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact neg_nonneg.mpr (h y hy)
  exact (signVariations_neg l).symm.trans
    (signVariations_eq_zero_of_forall_nonneg (l.map Neg.neg) hnonneg)

lemma signVariations_append_nonpos_nonneg_le_one (l₁ l₂ : List ℝ)
    (h₁ : ∀ x ∈ l₁, x ≤ 0) (h₂ : ∀ x ∈ l₂, 0 ≤ x) :
    (l₁ ++ l₂).signVariations ≤ 1 := by
  have hnonneg : ∀ x ∈ l₁.map Neg.neg, 0 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact neg_nonneg.mpr (h₁ y hy)
  have hnonpos : ∀ x ∈ l₂.map Neg.neg, x ≤ 0 := by
    intro x hx
    simp only [List.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact neg_nonpos.mpr (h₂ y hy)
  have h := signVariations_append_nonneg_nonpos_le_one
    (l₁.map Neg.neg) (l₂.map Neg.neg) hnonneg hnonpos
  rw [← List.signVariations_neg (l₁ ++ l₂)]
  simpa [List.map_append] using h

/-- Appending a nonpositive block increases sign variations by at most one. -/
lemma signVariations_append_nonpos_le_succ (l₁ l₂ : List ℝ)
    (h₂ : ∀ x ∈ l₂, x ≤ 0) :
    (l₁ ++ l₂).signVariations ≤ l₁.signVariations + 1 := by
  rw [List.signVariations, List.signVariations]
  simp only [List.map_append, List.filter_append]
  rw [filter_sign_eq_replicate_neg_one_of_forall_nonpos l₂ h₂]
  have hlen := length_destutter_append_replicate_le_succ (-1 : SignType)
    ((l₁.map SignType.sign).filter (· ≠ 0))
    ((l₂.map SignType.sign).filter (· ≠ 0)).length
  lia

end List

/-- Taking the sign of a sign is the identity. -/
@[simp]
theorem SignType.sign_sign (s : SignType) : SignType.sign s = s := by fin_cases s <;> rfl

private lemma add_one_le_pred_add_two (n : ℕ) :
    n + 1 ≤ n - 1 + 1 + 1 := by
  cases n <;> simp

/-- Prepending one sign increases the number of sign variations by at most one. -/
theorem List.signVariations_cons_le_succ (a : SignType) (l : List SignType) :
    (a :: l).signVariations ≤ l.signVariations + 1 := by
  have h := List.length_destutter_cons_ne_le_succ a
    ((l.map SignType.sign).filter (· ≠ 0))
  by_cases ha : a = 0
  · simp [List.signVariations, ha]
  · simpa [List.signVariations, ha] using h.trans (add_one_le_pred_add_two _)

/-- Appending one sign increases the number of sign variations by at most one. -/
theorem List.signVariations_append_singleton_signType_le_succ
    (l : List SignType) (a : SignType) :
    (l ++ [a]).signVariations ≤ l.signVariations + 1 := by
  have h := List.length_destutter_append_singleton_ne_le_succ
    ((l.map SignType.sign).filter (· ≠ 0)) a
  by_cases ha : a = 0
  · simp [List.signVariations, ha]
  · simpa [List.signVariations, ha] using h.trans (add_one_le_pred_add_two _)

/-- Inserting any sign between opposite nonzero signs does not change sign variations.

This is the finite local step used for nodal interior zeros in Karlin's perturbation
argument: after zero signs are removed, the inserted sign either disappears or duplicates
one of its two neighbors. -/
theorem List.signVariations_insert_between_opposite
    (l₁ l₂ : List SignType) (a b z : SignType)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (l₁ ++ [a, z, b] ++ l₂).signVariations =
      (l₁ ++ [a, b] ++ l₂).signVariations := by
  fin_cases a <;> fin_cases b <;> fin_cases z <;>
    simp_all [List.signVariations, List.destutter_append_cons_self_ne,
      List.destutter_append_cons_cons_self_ne]

namespace List

private theorem filter_map_sign_filter_ne_zero (l : List SignType) :
    ((l.filter (· ≠ 0)).map SignType.sign).filter (· ≠ 0) =
      (l.map SignType.sign).filter (· ≠ 0) := by
  have hsign : (SignType.sign : SignType → SignType) = id := funext SignType.sign_sign
  simp [hsign]

/-- Filtering zero signs does not change sign variations. -/
theorem signVariations_filter_ne_zero (l : List SignType) :
    (l.filter (· ≠ 0)).signVariations = l.signVariations := by
  simp only [List.signVariations, filter_map_sign_filter_ne_zero]

/-- One insertion at an interior nodal position.

This inductive relation is structural data recording an explicit list operation,
not an unproved mathematical assertion packaged as a proposition. -/
inductive NodalInsertion : List SignType → List SignType → Prop
  | insert (l₁ l₂ : List SignType) (a b z : SignType)
      (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
      NodalInsertion (l₁ ++ [a, b] ++ l₂) (l₁ ++ [a, z, b] ++ l₂)

/-- Adding unchanged list context preserves one nodal insertion. -/
protected theorem NodalInsertion.append_context
    {l l' : List SignType} (h : NodalInsertion l l')
    (pre post : List SignType) :
    NodalInsertion (pre ++ l ++ post) (pre ++ l' ++ post) := by
  cases h with
  | insert l₁ l₂ a b z ha hb hab =>
      simpa only [append_assoc] using
        NodalInsertion.insert (pre ++ l₁) (l₂ ++ post) a b z ha hb hab

/-- Erasing an entry between opposite nonzero neighbors is one nodal insertion in reverse. -/
protected theorem NodalInsertion.eraseIdx_succ
    (l : List SignType) (i : ℕ) (hi : i + 2 < l.length)
    (ha : l[i] ≠ 0) (hb : l[i + 2] ≠ 0)
    (hab : l[i] ≠ l[i + 2]) :
    NodalInsertion (l.eraseIdx (i + 1)) l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
      cases i with
      | zero =>
          cases l with
          | nil => simp at hi
          | cons z l =>
              cases l with
              | nil => simp at hi
              | cons b l =>
                  exact NodalInsertion.insert [] l x b z
                    (by simpa using ha) (by simpa using hb)
                    (by simpa using hab)
      | succ i =>
          have h := ih i
            (by
              simp only [length_cons] at hi
              lia)
            (by simpa [Nat.succ_eq_add_one] using ha)
            (by simpa [Nat.succ_eq_add_one] using hb)
            (by simpa [Nat.succ_eq_add_one] using hab)
          simpa [Nat.succ_eq_add_one] using h.append_context [x] []

/-- Erasing an entry between opposite nonzero neighbors inside a middle block
is one nodal insertion in reverse, with unchanged surrounding context. -/
protected theorem NodalInsertion.eraseIdx_append_middle
    (pre middle post : List SignType) (i : ℕ)
    (hi : i + 2 < middle.length)
    (ha : middle[i] ≠ 0) (hb : middle[i + 2] ≠ 0)
    (hab : middle[i] ≠ middle[i + 2]) :
    NodalInsertion
      ((pre ++ middle ++ post).eraseIdx (pre.length + (i + 1)))
      (pre ++ middle ++ post) := by
  have hi' : i + 1 < middle.length := by lia
  rw [List.eraseIdx_append_middle pre middle post (i + 1) hi']
  exact
    (NodalInsertion.eraseIdx_succ middle i hi ha hb hab).append_context
      pre post

/-- Deleting the first element of a middle block is a nodal insertion when
its left neighbor is a retained singleton and its right neighbor is the
second middle entry. -/
protected theorem NodalInsertion.eraseIdx_first_middle
    (a : SignType) (middle post : List SignType)
    (hmiddle : 1 < middle.length)
    (ha : a ≠ 0)
    (hb : middle[1] ≠ 0)
    (hab : a ≠ middle[1]) :
    NodalInsertion
      ([a] ++ middle.eraseIdx 0 ++ post)
      ([a] ++ middle ++ post) := by
  rw [← List.eraseIdx_append_middle [a] middle post 0 (by lia)]
  change NodalInsertion
    (([a] ++ middle ++ post).eraseIdx 1)
    ([a] ++ middle ++ post)
  simpa only [List.nil_append, List.length_nil, zero_add,
    List.append_assoc] using
    NodalInsertion.eraseIdx_append_middle
      [] ([a] ++ middle) post 0
      (by
        simp only [List.length_append, List.length_singleton]
        lia)
      (by simpa using ha)
      (by simpa using hb)
      (by simpa using hab)

/-- Deleting the final entry of a middle block is one nodal insertion in
reverse when its preceding entry and a retained singleton endpoint have
opposite nonzero signs. -/
protected theorem NodalInsertion.eraseIdx_last_append_singleton
    (pre middle : List SignType) (b : SignType) (i : ℕ)
    (hlen : middle.length = i + 2)
    (ha : middle[i] ≠ 0) (hb : b ≠ 0)
    (hab : middle[i] ≠ b) :
    NodalInsertion
      (pre ++ middle.eraseIdx (i + 1) ++ [b])
      (pre ++ middle ++ [b]) := by
  have hi : i < middle.length := by simp [hlen]
  have hiErase : i + 1 < middle.length := by simp [hlen]
  have hiLocal : i + 2 < (middle ++ [b]).length := by simp [hlen]
  have hleft : (middle ++ [b])[i] = middle[i] :=
    List.getElem_append_left hi
  have hright : (middle ++ [b])[i + 2] = b := by simp [List.getElem_append_right, hlen]
  rw [← List.eraseIdx_append_middle
    pre middle [b] (i + 1) hiErase]
  simpa only [List.append_nil, List.append_assoc] using
    NodalInsertion.eraseIdx_append_middle
      pre (middle ++ [b]) [] i hiLocal
      (by rw [hleft]; exact ha)
      (by rw [hright]; exact hb)
      (by rw [hleft, hright]; exact hab)

/-- Adding unchanged list context preserves repeated nodal insertions. -/
protected theorem NodalInsertion.reflTransGen_append_context
    {l l' : List SignType}
    (h : Relation.ReflTransGen NodalInsertion l l')
    (pre post : List SignType) :
    Relation.ReflTransGen NodalInsertion
      (pre ++ l ++ post) (pre ++ l' ++ post) := by
  induction h with
  | refl => exact .refl
  | tail h huv ih =>
      exact ih.tail (huv.append_context pre post)

/-- Repeated insertions at interior nodal positions preserve sign variations. -/
theorem signVariations_eq_of_nodalInsertions
    {l l' : List SignType}
    (h : Relation.ReflTransGen NodalInsertion l l') :
    l'.signVariations = l.signVariations := by
  induction h with
  | refl => rfl
  | tail h huv ih =>
      cases huv with
      | insert l₁ l₂ a b z ha hb hab =>
          calc
            (l₁ ++ [a, z, b] ++ l₂).signVariations =
                (l₁ ++ [a, b] ++ l₂).signVariations :=
              signVariations_insert_between_opposite l₁ l₂ a b z ha hb hab
            _ = l.signVariations := ih

/-- Repeated interior nodal insertions and two arbitrary endpoint insertions increase sign
variations by at most two. -/
theorem signVariations_endpoints_le_add_two_of_nodalInsertions
    {l l' : List SignType}
    (h : Relation.ReflTransGen NodalInsertion l l')
    (a b : SignType) :
    ((a :: l') ++ [b]).signVariations ≤ l.signVariations + 2 := by
  calc
    ((a :: l') ++ [b]).signVariations ≤
        (l' ++ [b]).signVariations + 1 := by
      simpa only [List.cons_append] using
        signVariations_cons_le_succ a (l' ++ [b])
    _ ≤ (l'.signVariations + 1) + 1 :=
      Nat.add_le_add_right
        (signVariations_append_singleton_signType_le_succ l' b) 1
    _ = l.signVariations + 2 := by rw [signVariations_eq_of_nodalInsertions h]

end List

/-- A negative product of real numbers has nonzero, opposite signs. -/
theorem SignType.sign_ne_zero_and_ne_of_mul_neg
    {a b : ℝ} (h : a * b < 0) :
    SignType.sign a ≠ 0 ∧ SignType.sign b ≠ 0 ∧
      SignType.sign a ≠ SignType.sign b := by
  rcases (mul_neg_iff.mp h) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp [SignType.sign, ha, hb, not_lt_of_ge hb.le]
  · simp [SignType.sign, ha, hb, not_lt_of_ge ha.le]

namespace Fin

/-- The number of sign changes in a finite vector, in index order and ignoring
zero entries. -/
def signVariations {R : Type*} [Zero R] [LinearOrder R] {n : ℕ}
    (x : Fin n → R) : ℕ :=
  (List.ofFn x).signVariations

/-- A finite real vector has the same variation count as its explicit sign list. -/
theorem signVariations_eq_signList {n : ℕ} (x : Fin n → ℝ) :
    Fin.signVariations x =
      (List.ofFn (SignType.sign ∘ x)).signVariations := by
  simp [Fin.signVariations, List.signVariations, Function.comp_def]

/-- Filtering the explicit sign list computes finite-vector sign variations. -/
theorem filtered_signList_signVariations {n : ℕ} (x : Fin n → ℝ) :
    ((List.ofFn (SignType.sign ∘ x)).filter (· ≠ 0)).signVariations =
      Fin.signVariations x := by
  simpa only [List.signVariations_filter_ne_zero] using
    (Fin.signVariations_eq_signList x).symm

/-- Perturbed signs at all interior coordinates and at the original nonzero
endpoints.

Interior zeros are retained because the coordinate-removal induction constructs
them by nodal insertions. A zero original endpoint is omitted and handled by the
final two-endpoint variation bound. -/
def nodalPerturbationCoreSigns
    {n : ℕ} (x y : Fin (n + 2) → ℝ) : List SignType :=
  (if x 0 = 0 then [] else [SignType.sign (y 0)]) ++
    List.ofFn
      (fun i : Fin n => SignType.sign (y i.succ.castSucc)) ++
    (if x (Fin.last (n + 1)) = 0 then []
      else [SignType.sign (y (Fin.last (n + 1)))])

/-- At the splice created by deleting a nodal zero, the new center is nonzero. -/
theorem succAbove_center_ne_zero_of_mul_neg
    {n : ℕ} (x : Fin (n + 3) → ℝ) (i : Fin n)
    (h : x i.castSucc.castSucc.castSucc * x i.succ.succ.castSucc < 0) :
    x ((i.succ.castSucc.castSucc).succAbove i.succ.castSucc) ≠ 0 := by
  rw [Fin.succAbove_center_eq_right]
  exact right_ne_zero_of_mul (ne_of_lt h)

/-- If the omitted nodal zero was the old right neighbor, the new center is nonzero. -/
theorem succAbove_center_ne_zero_of_omit_right_mul_neg
    {n : ℕ} (x : Fin (n + 3) → ℝ) (i : Fin n)
    (h : x i.succ.castSucc.castSucc * x i.succ.succ.succ < 0) :
    x ((i.succ.succ.castSucc).succAbove i.succ.castSucc) ≠ 0 := by
  rw [Fin.succAbove_center_eq_left]
  exact left_ne_zero_of_mul (ne_of_lt h)

/-- Deleting an interior nodal zero preserves strict interior nodality. -/
theorem interiorNodal_succAbove
    {n : ℕ} (x : Fin (n + 3) → ℝ) (k : Fin (n + 1))
    (hk : x k.succ.castSucc = 0)
    (hnodal : ∀ j : Fin (n + 1), x j.succ.castSucc = 0 →
      x j.castSucc.castSucc * x j.succ.succ < 0) :
    ∀ i : Fin n,
      x (k.succ.castSucc.succAbove i.succ.castSucc) = 0 →
        x (k.succ.castSucc.succAbove i.castSucc.castSucc) *
          x (k.succ.castSucc.succAbove i.succ.succ) < 0 := by
  intro i hi
  by_cases hki : (k : ℕ) < (i : ℕ)
  · have hp : k.succ.castSucc ≤ i.castSucc.castSucc.castSucc := by
      change (k : ℕ) + 1 ≤ (i : ℕ)
      lia
    rcases Fin.succAbove_triple_eq_succ_of_le_left k.succ.castSucc i hp with
      ⟨hleft, hcenter, hright⟩
    rw [hcenter] at hi
    rw [hleft, hright]
    simpa using hnodal i.succ (by simpa using hi)
  · by_cases hik : (i : ℕ) < (k : ℕ)
    · by_cases hnext : (k : ℕ) = (i : ℕ) + 1
      · have hkeq : k = i.succ := by
          apply Fin.ext
          exact hnext
        subst k
        have hn := hnodal i.succ (by simpa using hk)
        have hne := Fin.succAbove_center_ne_zero_of_omit_right_mul_neg x i
          (by simpa using hn)
        exact (hne (by simpa using hi)).elim
      · have hp : i.succ.succ.castSucc < k.succ.castSucc := by
          change (i : ℕ) + 2 < (k : ℕ) + 1
          lia
        rcases Fin.succAbove_triple_eq_castSucc_of_right_lt k.succ.castSucc i hp with
          ⟨hleft, hcenter, hright⟩
        rw [hcenter] at hi
        rw [hleft, hright]
        simpa using hnodal i.castSucc (by simpa using hi)
    · have hkeq : k = i.castSucc := by
        apply Fin.ext
        change (k : ℕ) = (i : ℕ)
        lia
      subst k
      have hn := hnodal i.castSucc (by simpa using hk)
      have hne := Fin.succAbove_center_ne_zero_of_mul_neg x i
        (by simpa using hn)
      exact (hne (by simpa using hi)).elim


/-- Remove one interior zero, apply the shorter nodal-insertion chain, and reinsert it.

This is the finite induction step in the endpoint-perturbation route used in Karlin's
Chapter 8, Section 3 argument.
-/
theorem nodalInsertions_coreSigns_remove
    {n : ℕ}
    (ih :
      ∀ {u v : Fin (n + 2) → ℝ},
        (∀ i, u i ≠ 0 →
          SignType.sign (v i) = SignType.sign (u i)) →
        (∀ i : Fin n, u i.succ.castSucc = 0 →
          u i.castSucc.castSucc * u i.succ.succ < 0) →
        Relation.ReflTransGen List.NodalInsertion
          ((List.ofFn (SignType.sign ∘ u)).filter (· ≠ 0))
          (Fin.nodalPerturbationCoreSigns u v))
    {x y : Fin (n + 3) → ℝ}
    (hsign : ∀ i, x i ≠ 0 →
      SignType.sign (y i) = SignType.sign (x i))
    (hnodal : ∀ i : Fin (n + 1), x i.succ.castSucc = 0 →
      x i.castSucc.castSucc * x i.succ.succ < 0)
    (k : Fin (n + 1))
    (hk : x k.succ.castSucc = 0) :
    Relation.ReflTransGen List.NodalInsertion
      ((List.ofFn (SignType.sign ∘ x)).filter (· ≠ 0))
      (Fin.nodalPerturbationCoreSigns x y) := by
  let p : Fin (n + 3) := k.succ.castSucc
  let x' : Fin (n + 2) → ℝ := fun i => x (p.succAbove i)
  let y' : Fin (n + 2) → ℝ := fun i => y (p.succAbove i)
  have hsign' :
      ∀ i, x' i ≠ 0 →
        SignType.sign (y' i) = SignType.sign (x' i) := by
    intro i hi
    simpa only [x', y'] using
      hsign (p.succAbove i) (by simpa only [x'] using hi)
  have hnodal' :
      ∀ i : Fin n, x' i.succ.castSucc = 0 →
        x' i.castSucc.castSucc * x' i.succ.succ < 0 := by
    simpa only [x', p] using
      Fin.interiorNodal_succAbove x k hk hnodal
  have hrec :
      Relation.ReflTransGen List.NodalInsertion
        ((List.ofFn (SignType.sign ∘ x')).filter (· ≠ 0))
        (Fin.nodalPerturbationCoreSigns x' y') :=
    ih hsign' hnodal'
  have hofFn :
      List.ofFn (fun i => SignType.sign (x' i)) =
        (List.ofFn (fun i => SignType.sign (x i))).eraseIdx p := by
    simpa only [x', p] using
      List.ofFn_succAbove_eq_eraseIdx
        (fun i => SignType.sign (x i)) p
  have hlenSource :
      (p : ℕ) <
        (List.ofFn (fun i => SignType.sign (x i))).length := by
    simpa only [List.length_ofFn] using p.isLt
  have hvalueSource :
      (List.ofFn (fun i => SignType.sign (x i)))[(p : ℕ)] = 0 := by
    rw [List.getElem_ofFn hlenSource]
    change SignType.sign (x p) = 0
    rw [show p = k.succ.castSucc from rfl, hk]
    norm_num [SignType.sign]
  have hfilteredSource :
      ¬(fun z : SignType => decide (z ≠ 0))
        (List.ofFn (fun i => SignType.sign (x i)))[(p : ℕ)] := by
    rw [hvalueSource]
    decide
  have hsource :
      (List.ofFn (fun i => SignType.sign (x' i))).filter (· ≠ 0) =
        (List.ofFn (fun i => SignType.sign (x i))).filter (· ≠ 0) := by
    rw [hofFn]
    exact List.filter_eraseIdx_eq_of_getElem_not
      hlenSource hfilteredSource
  have hxzero : x' 0 = x 0 := by simp only [x', p, Fin.succAbove_zero_of_interior]
  have hyzero : y' 0 = y 0 := by simp only [y', p, Fin.succAbove_zero_of_interior]
  have hxlast :
      x' (Fin.last (n + 1)) = x (Fin.last (n + 2)) := by
    simp only [x', p, Fin.succAbove_last_of_interior]
  have hylast :
      y' (Fin.last (n + 1)) = y (Fin.last (n + 2)) := by
    simp only [y', p, Fin.succAbove_last_of_interior]
  have hinterior :
      List.ofFn
          (fun i : Fin n =>
            SignType.sign (y' i.succ.castSucc)) =
        (List.ofFn
          (fun i : Fin (n + 1) =>
            SignType.sign (y i.succ.castSucc))).eraseIdx k := by
    simpa only [y', p, Function.comp_apply] using
      List.ofFn_interior_succAbove_eq_eraseIdx
        (SignType.sign ∘ y) k
  let left : List SignType :=
    if x 0 = 0 then [] else [SignType.sign (y 0)]
  let middle : List SignType :=
    List.ofFn
      (fun i : Fin (n + 1) =>
        SignType.sign (y i.succ.castSucc))
  let right : List SignType :=
    if x (Fin.last (n + 2)) = 0 then []
    else [SignType.sign (y (Fin.last (n + 2)))]
  let full : List SignType := left ++ middle ++ right
  let reduced : List SignType :=
    left ++ middle.eraseIdx k ++ right
  have hfull :
      Fin.nodalPerturbationCoreSigns x y = full := by
    rfl
  have hreduced :
      Fin.nodalPerturbationCoreSigns x' y' = reduced := by
    simp only [Fin.nodalPerturbationCoreSigns, reduced, left, middle,
      right, hxzero, hyzero, hxlast, hylast, hinterior]
  have hmul :
      x k.castSucc.castSucc * x k.succ.succ < 0 :=
    hnodal k hk
  have hxleft : x k.castSucc.castSucc ≠ 0 :=
    left_ne_zero_of_mul (ne_of_lt hmul)
  have hxright : x k.succ.succ ≠ 0 :=
    right_ne_zero_of_mul (ne_of_lt hmul)
  have hopposite :
      SignType.sign (y k.castSucc.castSucc) ≠ 0 ∧
        SignType.sign (y k.succ.succ) ≠ 0 ∧
        SignType.sign (y k.castSucc.castSucc) ≠
          SignType.sign (y k.succ.succ) := by
    simpa only [hsign k.castSucc.castSucc hxleft,
      hsign k.succ.succ hxright] using
      SignType.sign_ne_zero_and_ne_of_mul_neg hmul
  have hstep : List.NodalInsertion reduced full := by
    by_cases hn : n = 0
    · subst n
      have hkzero : k = 0 := Fin.eq_zero k
      subst k
      have hleftIndex :
          (0 : Fin 1).castSucc.castSucc = (0 : Fin 3) := by
        exact Fin.ext rfl
      have hcenterIndex :
          (0 : Fin 1).succ.castSucc = (1 : Fin 3) := by
        exact Fin.ext rfl
      have hrightIndex :
          (0 : Fin 1).succ.succ = (2 : Fin 3) := by
        exact Fin.ext rfl
      have hlastIndex :
          (Fin.last 2 : Fin 3) = (2 : Fin 3) := by
        exact Fin.ext rfl
      have hxzero' : x (0 : Fin 3) ≠ 0 := by simpa only [hleftIndex] using hxleft
      have hxtwo : x (2 : Fin 3) ≠ 0 := by simpa only [hrightIndex] using hxright
      have hsignLeft : SignType.sign (y 0) ≠ 0 := by simpa only [hleftIndex] using hopposite.1
      have hsignTwo : SignType.sign (y 2) ≠ 0 := by simpa only [hrightIndex] using hopposite.2.1
      have hsignNe :
          SignType.sign (y 0) ≠ SignType.sign (y 2) := by
        simpa only [hleftIndex, hrightIndex] using hopposite.2.2
      simpa [full, reduced, left, middle, right, hxzero', hxtwo,
        hcenterIndex, hlastIndex] using
        List.NodalInsertion.insert [] []
          (SignType.sign (y 0))
          (SignType.sign (y 2))
          (SignType.sign (y 1))
          hsignLeft hsignTwo hsignNe
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      by_cases hkzero : (k : ℕ) = 0
      · have hkeq : k = 0 := Fin.ext hkzero
        subst k
        have hxzero' : x 0 ≠ 0 := by simpa using hxleft
        have hmiddleLength : 1 < middle.length := by
          simp [middle]
          lia
        simpa [full, reduced, left, hxzero'] using
          List.NodalInsertion.eraseIdx_first_middle
            (SignType.sign (y 0)) middle right
            hmiddleLength
            (by simpa using hopposite.1)
            (by simpa [middle] using hopposite.2.1)
            (by simpa [middle] using hopposite.2.2)
      · by_cases hklast : (k : ℕ) = n
        · have hkeq : k = Fin.last n := Fin.ext hklast
          subst k
          have hxlast' : x (Fin.last (n + 2)) ≠ 0 := by simpa using hxright
          have hpred : n - 1 + 1 = n := by lia
          have hlen : middle.length = n - 1 + 2 := by
            simp [middle]
            lia
          have hleftBound : n - 1 < middle.length := by
            rw [hlen]
            lia
          have hleftMiddle :
              middle[n - 1]'hleftBound =
                SignType.sign
                  (y (Fin.last n).castSucc.castSucc) := by
            rw [List.getElem_ofFn hleftBound]
            congr 2
            apply Fin.ext
            simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last]
            lia
          have hrightEndpoint :
              SignType.sign (y (Fin.last (n + 2))) =
                SignType.sign (y (Fin.last n).succ.succ) := by
            congr 2
          have haMiddle : middle[n - 1] ≠ 0 := by
            rw [hleftMiddle]
            exact hopposite.1
          have hbEndpoint :
              SignType.sign (y (Fin.last (n + 2))) ≠ 0 := by
            rw [hrightEndpoint]
            exact hopposite.2.1
          have habMiddle :
              middle[n - 1] ≠
                SignType.sign (y (Fin.last (n + 2))) := by
            rw [hleftMiddle, hrightEndpoint]
            exact hopposite.2.2
          simpa [full, reduced, right, hxlast', hpred] using
            List.NodalInsertion.eraseIdx_last_append_singleton
              left middle
              (SignType.sign (y (Fin.last (n + 2))))
              (n - 1) hlen haMiddle hbEndpoint habMiddle
        · have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hkzero
          have hklt : (k : ℕ) < n := by lia
          have hpred :
              (k : ℕ) - 1 + 1 = (k : ℕ) := by lia
          have hsucc :
              (k : ℕ) - 1 + 2 = (k : ℕ) + 1 := by lia
          have hleftBound :
              (k : ℕ) - 1 < middle.length := by
            simp [middle]
          have hrightBound :
              (k : ℕ) - 1 + 2 < middle.length := by
            simp [middle]
            lia
          have hleftMiddle :
              middle[(k : ℕ) - 1]'hleftBound =
                SignType.sign (y k.castSucc.castSucc) := by
            rw [List.getElem_ofFn hleftBound]
            congr 2
            apply Fin.ext
            simp only [Fin.val_castSucc, Fin.val_succ]
            lia
          have hrightMiddle :
              middle[(k : ℕ) - 1 + 2]'hrightBound =
                SignType.sign (y k.succ.succ) := by
            rw [List.getElem_ofFn hrightBound]
            congr 2
            apply Fin.ext
            simp only [Fin.val_castSucc, Fin.val_succ]
            lia
          have haMiddle : middle[(k : ℕ) - 1] ≠ 0 := by
            rw [hleftMiddle]
            exact hopposite.1
          have hbMiddle : middle[(k : ℕ) - 1 + 2] ≠ 0 := by
            rw [hrightMiddle]
            exact hopposite.2.1
          have habMiddle :
              middle[(k : ℕ) - 1] ≠
                middle[(k : ℕ) - 1 + 2] := by
            rw [hleftMiddle, hrightMiddle]
            exact hopposite.2.2
          have hlocal :
              List.NodalInsertion
                ((left ++ middle ++ right).eraseIdx
                  (left.length + ((k : ℕ) - 1 + 1)))
                (left ++ middle ++ right) :=
            List.NodalInsertion.eraseIdx_append_middle
              left middle right ((k : ℕ) - 1)
              hrightBound haMiddle hbMiddle habMiddle
          have hkMiddle : (k : ℕ) < middle.length := by simpa [middle] using k.isLt
          rw [hpred] at hlocal
          rw [List.eraseIdx_append_middle
            left middle right (k : ℕ) hkMiddle] at hlocal
          simpa [full, reduced] using hlocal
  have hstepCore :
      List.NodalInsertion
        (Fin.nodalPerturbationCoreSigns x' y')
        (Fin.nodalPerturbationCoreSigns x y) := by
    rw [hreduced, hfull]
    exact hstep
  have hsourceComp :
      (List.ofFn (SignType.sign ∘ x')).filter (· ≠ 0) =
        (List.ofFn (SignType.sign ∘ x)).filter (· ≠ 0) := by
    calc
      _ = (List.ofFn (fun i => SignType.sign (x' i))).filter
          (· ≠ 0) := by
        congr 2
      _ = (List.ofFn (fun i => SignType.sign (x i))).filter
          (· ≠ 0) := hsource
      _ = _ := by congr 2
  rw [hsourceComp] at hrec
  exact hrec.tail hstepCore

/-- If there is no interior zero, filtering the original signs already gives
the perturbed core signs. -/
theorem nodalPerturbationCoreSigns_eq_of_no_interior_zero
    {n : ℕ} {x y : Fin (n + 2) → ℝ}
    (hsign : ∀ i, x i ≠ 0 →
      SignType.sign (y i) = SignType.sign (x i))
    (hinterior : ∀ i : Fin n, x i.succ.castSucc ≠ 0) :
    (List.ofFn (SignType.sign ∘ x)).filter (· ≠ 0) =
      Fin.nodalPerturbationCoreSigns x y := by
  let sourceMiddle : List SignType :=
    List.ofFn (fun i : Fin n =>
      SignType.sign (x i.succ.castSucc))
  let targetMiddle : List SignType :=
    List.ofFn (fun i : Fin n =>
      SignType.sign (y i.succ.castSucc))
  have hsourceMiddle :
      sourceMiddle.filter (· ≠ 0) = sourceMiddle := by
    apply List.filter_eq_self.2
    intro s hs
    simp only [sourceMiddle, List.mem_ofFn] at hs
    obtain ⟨i, rfl⟩ := hs
    exact decide_eq_true (sign_ne_zero.mpr (hinterior i))
  have hmiddle : sourceMiddle = targetMiddle := by
    simp only [sourceMiddle, targetMiddle]
    congr 1
    funext i
    exact (hsign i.succ.castSucc (hinterior i)).symm
  have hfilterEndpoint (i : Fin (n + 2)) :
      [SignType.sign (x i)].filter (· ≠ 0) =
        if x i = 0 then [] else [SignType.sign (y i)] := by
    by_cases hi : x i = 0
    · simp [hi, SignType.sign]
    · rw [if_neg hi, List.filter_singleton]
      have hs := sign_ne_zero.mpr hi
      have hp : decide (SignType.sign (x i) ≠ 0) = true :=
        decide_eq_true hs
      rw [hp]
      change [SignType.sign (x i)] = [SignType.sign (y i)]
      rw [hsign i hi]
  rw [List.ofFn_two_endpoints]
  change
    (([SignType.sign (x 0)] ++ sourceMiddle ++
      [SignType.sign (x (Fin.last (n + 1)))]).filter (· ≠ 0)) =
      (if x 0 = 0 then [] else [SignType.sign (y 0)]) ++
        targetMiddle ++
        (if x (Fin.last (n + 1)) = 0 then []
          else [SignType.sign (y (Fin.last (n + 1)))])
  rw [List.filter_append, List.filter_append, hfilterEndpoint,
    hsourceMiddle, hmiddle, hfilterEndpoint]

/-- Nodal insertions transform the filtered original sign list into the
perturbed core sign list. -/
theorem nodalInsertions_coreSigns
    {n : ℕ} {x y : Fin (n + 2) → ℝ}
    (hsign : ∀ i, x i ≠ 0 →
      SignType.sign (y i) = SignType.sign (x i))
    (hnodal : ∀ i : Fin n, x i.succ.castSucc = 0 →
      x i.castSucc.castSucc * x i.succ.succ < 0) :
    Relation.ReflTransGen List.NodalInsertion
      ((List.ofFn (SignType.sign ∘ x)).filter (· ≠ 0))
      (Fin.nodalPerturbationCoreSigns x y) := by
  induction n with
  | zero =>
      have hinterior :
          ∀ i : Fin 0, x i.succ.castSucc ≠ 0 := by
        exact fun i => Fin.elim0 i
      rw [Fin.nodalPerturbationCoreSigns_eq_of_no_interior_zero
        hsign hinterior]
  | succ n ih =>
      by_cases hzero :
        ∃ k : Fin (n + 1), x k.succ.castSucc = 0
      · obtain ⟨k, hk⟩ := hzero
        exact Fin.nodalInsertions_coreSigns_remove
          ih hsign hnodal k hk
      · have hinterior :
            ∀ i : Fin (n + 1), x i.succ.castSucc ≠ 0 := by
          intro i hi
          exact hzero ⟨i, hi⟩
        rw [Fin.nodalPerturbationCoreSigns_eq_of_no_interior_zero
          hsign hinterior]

/-- A sign-preserving perturbation increases variations by at most two when
all interior zeros are nodal.

This is Karlin's finite endpoint-loss estimate: interior nodal insertions cost
nothing, while the two endpoints cost at most one variation each.
-/
theorem signVariations_le_add_two_of_sign_eq_on_nonzero_of_interior_nodal
    {n : ℕ} {x y : Fin (n + 2) → ℝ}
    (hsign : ∀ i, x i ≠ 0 →
      SignType.sign (y i) = SignType.sign (x i))
    (hnodal : ∀ i : Fin n, x i.succ.castSucc = 0 →
      x i.castSucc.castSucc * x i.succ.succ < 0) :
    Fin.signVariations y ≤ Fin.signVariations x + 2 := by
  let middle : List SignType :=
    List.ofFn (fun i : Fin n =>
      SignType.sign (y i.succ.castSucc))
  let core := Fin.nodalPerturbationCoreSigns x y
  have hchain :
      Relation.ReflTransGen List.NodalInsertion
        ((List.ofFn (SignType.sign ∘ x)).filter (· ≠ 0)) core := by
    exact Fin.nodalInsertions_coreSigns hsign hnodal
  have hcore : core.signVariations = Fin.signVariations x := by
    rw [List.signVariations_eq_of_nodalInsertions hchain]
    exact Fin.filtered_signList_signVariations x
  have hsplit :
      List.ofFn (SignType.sign ∘ y) =
        SignType.sign (y 0) ::
          (middle ++ [SignType.sign (y (Fin.last (n + 1)))]) := by
    simpa only [middle, Function.comp_apply] using
      List.ofFn_two_endpoints (SignType.sign ∘ y)
  rw [Fin.signVariations_eq_signList, hsplit]
  by_cases hzero : x 0 = 0
  · by_cases hlast : x (Fin.last (n + 1)) = 0
    · have hfull :
          SignType.sign (y 0) ::
              (middle ++ [SignType.sign (y (Fin.last (n + 1)))]) =
            (SignType.sign (y 0) :: core) ++
              [SignType.sign (y (Fin.last (n + 1)))] := by
        simp [core, middle, Fin.nodalPerturbationCoreSigns,
          hzero, hlast]
      rw [hfull]
      calc
        ((SignType.sign (y 0) :: core) ++
            [SignType.sign (y (Fin.last (n + 1)))]).signVariations ≤
            (SignType.sign (y 0) :: core).signVariations + 1 :=
          List.signVariations_append_singleton_signType_le_succ _ _
        _ ≤ (core.signVariations + 1) + 1 :=
          Nat.add_le_add_right
            (List.signVariations_cons_le_succ (SignType.sign (y 0)) core) 1
        _ = Fin.signVariations x + 2 := by rw [hcore]
    · have hfull :
          SignType.sign (y 0) ::
              (middle ++ [SignType.sign (y (Fin.last (n + 1)))]) =
            SignType.sign (y 0) :: core := by
        simp [core, middle, Fin.nodalPerturbationCoreSigns,
          hzero, hlast]
      rw [hfull]
      calc
        (SignType.sign (y 0) :: core).signVariations ≤
            core.signVariations + 1 :=
          List.signVariations_cons_le_succ _ _
        _ ≤ Fin.signVariations x + 2 := by rw [hcore]; lia
  · by_cases hlast : x (Fin.last (n + 1)) = 0
    · have hfull :
          SignType.sign (y 0) ::
              (middle ++ [SignType.sign (y (Fin.last (n + 1)))]) =
            core ++ [SignType.sign (y (Fin.last (n + 1)))] := by
        simp [core, middle, Fin.nodalPerturbationCoreSigns,
          hzero, hlast]
      rw [hfull]
      calc
        (core ++
            [SignType.sign (y (Fin.last (n + 1)))]).signVariations ≤
            core.signVariations + 1 :=
          List.signVariations_append_singleton_signType_le_succ _ _
        _ ≤ Fin.signVariations x + 2 := by rw [hcore]; lia
    · have hfull :
          SignType.sign (y 0) ::
              (middle ++ [SignType.sign (y (Fin.last (n + 1)))]) =
            core := by
        simp [core, middle, Fin.nodalPerturbationCoreSigns,
          hzero, hlast]
      rw [hfull, hcore]
      lia

/-- A finite vector has at most one fewer sign variation than its length. -/
lemma signVariations_le_card_sub_one {R : Type*} [Zero R] [LinearOrder R]
    {n : ℕ} (x : Fin n → R) : signVariations x ≤ n - 1 := by
  rw [signVariations]
  simpa using List.signVariations_le_length_sub_one (List.ofFn x)

/-- If the first entry is zero, a finite vector has at most two fewer sign
variations than its length. -/
lemma signVariations_le_card_sub_two_of_zero_first {R : Type*}
    [Zero R] [LinearOrder R] {n : ℕ} (x : Fin (n + 1) → R)
    (hzero : x 0 = 0) : signVariations x ≤ n - 1 := by
  rw [signVariations]
  have hlist_ne : List.ofFn x ≠ [] := by simp
  have hhead : SignType.sign (List.head (List.ofFn x) hlist_ne) = 0 := by simp [hzero]
  have h := List.signVariations_le_length_sub_two_of_head_zero
    (l := List.ofFn x) hlist_ne hhead
  simpa using h

/-- A finite real vector with no negative entries has no sign variations. -/
lemma signVariations_eq_zero_of_forall_nonneg {n : ℕ} (x : Fin n → ℝ)
    (h : ∀ i, 0 ≤ x i) : signVariations x = 0 := by
  rw [signVariations]
  exact List.signVariations_eq_zero_of_forall_nonneg (List.ofFn x) (by
    intro y hy
    simp only [List.mem_ofFn] at hy
    obtain ⟨i, rfl⟩ := hy
    exact h i)

/-- A nonnegative finite block followed by a nonpositive finite block has at
most one sign variation. -/
lemma signVariations_append_nonneg_nonpos_le_one {m n : ℕ} (x : Fin m → ℝ)
    (y : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, y i ≤ 0) :
    signVariations (Fin.append x y) ≤ 1 := by
  rw [signVariations, List.ofFn_fin_append]
  exact List.signVariations_append_nonneg_nonpos_le_one (List.ofFn x) (List.ofFn y)
    (by
      intro a ha
      simp only [List.mem_ofFn] at ha
      obtain ⟨i, rfl⟩ := ha
      exact hx i)
    (by
      intro a ha
      simp only [List.mem_ofFn] at ha
      obtain ⟨i, rfl⟩ := ha
      exact hy i)

/-- A nonpositive finite block followed by a nonnegative finite block has at
most one sign variation. -/
lemma signVariations_append_nonpos_nonneg_le_one {m n : ℕ} (x : Fin m → ℝ)
    (y : Fin n → ℝ) (hx : ∀ i, x i ≤ 0) (hy : ∀ i, 0 ≤ y i) :
    signVariations (Fin.append x y) ≤ 1 := by
  rw [signVariations, List.ofFn_fin_append]
  exact List.signVariations_append_nonpos_nonneg_le_one (List.ofFn x) (List.ofFn y)
    (by
      intro a ha
      simp only [List.mem_ofFn] at ha
      obtain ⟨i, rfl⟩ := ha
      exact hx i)
    (by
      intro a ha
      simp only [List.mem_ofFn] at ha
      obtain ⟨i, rfl⟩ := ha
      exact hy i)

/-- Appending a nonnegative finite block increases sign variations by at most
one. -/
lemma signVariations_append_nonneg_le_succ {m n : ℕ} (x : Fin m → ℝ)
    (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) :
    signVariations (Fin.append x y) ≤ signVariations x + 1 := by
  rw [signVariations, signVariations, List.ofFn_fin_append]
  exact List.signVariations_append_nonneg_le_succ (List.ofFn x) (List.ofFn y) (by
    intro a ha
    simp only [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact hy i)

/-- Appending a nonpositive finite block increases sign variations by at most
one. -/
lemma signVariations_append_nonpos_le_succ {m n : ℕ} (x : Fin m → ℝ)
    (y : Fin n → ℝ) (hy : ∀ i, y i ≤ 0) :
    signVariations (Fin.append x y) ≤ signVariations x + 1 := by
  rw [signVariations, signVariations, List.ofFn_fin_append]
  exact List.signVariations_append_nonpos_le_succ (List.ofFn x) (List.ofFn y) (by
    intro a ha
    simp only [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact hy i)

/-- A finite vector split into a nonnegative initial block and a nonpositive
final block has at most one sign variation. -/
lemma signVariations_le_one_of_castAdd_nonneg_natAdd_nonpos {m n : ℕ}
    (x : Fin (m + n) → ℝ)
    (hleft : ∀ i : Fin m, 0 ≤ x (Fin.castAdd n i))
    (hright : ∀ i : Fin n, x (Fin.natAdd m i) ≤ 0) :
    signVariations x ≤ 1 := by
  simpa [Fin.append_castAdd_natAdd] using
    signVariations_append_nonneg_nonpos_le_one
      (fun i : Fin m => x (Fin.castAdd n i))
      (fun i : Fin n => x (Fin.natAdd m i)) hleft hright

/-- A finite vector split into a nonpositive initial block and a nonnegative
final block has at most one sign variation. -/
lemma signVariations_le_one_of_castAdd_nonpos_natAdd_nonneg {m n : ℕ}
    (x : Fin (m + n) → ℝ)
    (hleft : ∀ i : Fin m, x (Fin.castAdd n i) ≤ 0)
    (hright : ∀ i : Fin n, 0 ≤ x (Fin.natAdd m i)) :
    signVariations x ≤ 1 := by
  simpa [Fin.append_castAdd_natAdd] using
    signVariations_append_nonpos_nonneg_le_one
      (fun i : Fin m => x (Fin.castAdd n i))
      (fun i : Fin n => x (Fin.natAdd m i)) hleft hright

/-- A finite vector whose final block is nonnegative has at most one more sign
variation than its initial block. -/
lemma signVariations_le_succ_of_natAdd_nonneg {m n : ℕ}
    (x : Fin (m + n) → ℝ) (hright : ∀ i : Fin n, 0 ≤ x (Fin.natAdd m i)) :
    signVariations x ≤ signVariations (fun i : Fin m => x (Fin.castAdd n i)) + 1 := by
  simpa [Fin.append_castAdd_natAdd] using
    signVariations_append_nonneg_le_succ
      (fun i : Fin m => x (Fin.castAdd n i))
      (fun i : Fin n => x (Fin.natAdd m i)) hright

/-- A finite vector whose final block is nonpositive has at most one more sign
variation than its initial block. -/
lemma signVariations_le_succ_of_natAdd_nonpos {m n : ℕ}
    (x : Fin (m + n) → ℝ) (hright : ∀ i : Fin n, x (Fin.natAdd m i) ≤ 0) :
    signVariations x ≤ signVariations (fun i : Fin m => x (Fin.castAdd n i)) + 1 := by
  simpa [Fin.append_castAdd_natAdd] using
    signVariations_append_nonpos_le_succ
      (fun i : Fin m => x (Fin.castAdd n i))
      (fun i : Fin n => x (Fin.natAdd m i)) hright

/-- Every consecutive pair of entries has opposite strict signs. -/
def StrictlyAlternates {n : ℕ} (x : Fin (n + 1) → ℝ) : Prop :=
  ∀ i : Fin n, x i.castSucc * x i.succ < 0

lemma strictlyAlternates_iff {n : ℕ} {x : Fin (n + 1) → ℝ} :
    StrictlyAlternates x ↔ ∀ i : Fin n, x i.castSucc * x i.succ < 0 :=
  Iff.rfl

private lemma mul_neg_of_sign_ne {a b : ℝ}
    (ha0 : SignType.sign a ≠ 0) (hb0 : SignType.sign b ≠ 0)
    (hab : SignType.sign a ≠ SignType.sign b) : a * b < 0 := by
  have ha_ne : a ≠ 0 := sign_ne_zero.mp ha0
  have hb_ne : b ≠ 0 := sign_ne_zero.mp hb0
  rcases lt_or_gt_of_ne ha_ne with ha | ha <;>
    rcases lt_or_gt_of_ne hb_ne with hb | hb
  · exact (hab (by rw [sign_neg ha, sign_neg hb])).elim
  · exact mul_neg_of_neg_of_pos ha hb
  · exact mul_neg_of_pos_of_neg ha hb
  · exact (hab (by rw [sign_pos ha, sign_pos hb])).elim

/-- A positive lower bound on sign variations produces an ordered strictly
alternating subsequence of the corresponding length. -/
lemma exists_strictMono_strictlyAlternates_of_le_signVariations
    {m q : ℕ} {y : Fin m → ℝ} (hq : 0 < q)
    (h : q ≤ signVariations y) :
    ∃ rows : Fin (q + 1) → Fin m,
      StrictMono rows ∧ StrictlyAlternates (fun i => y (rows i)) := by
  let raw : List SignType := List.ofFn (SignType.sign ∘ y)
  let nz : List SignType := raw.filter (· ≠ 0)
  let d : List SignType := nz.destutter (· ≠ ·)
  have hh : q ≤ d.length - 1 := by
    simpa [signVariations, List.signVariations, d, nz, raw,
      List.map_ofFn] using h
  have hlen : q + 1 ≤ d.length := by lia
  have hsub : d.Sublist raw :=
    (List.destutter_sublist (R := fun a b : SignType => a ≠ b) nz).trans
      List.filter_sublist
  obtain ⟨e, he⟩ :=
    List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
  let rows : Fin (q + 1) → Fin m := fun i =>
    ⟨e (Fin.castLE hlen i), by
      simpa [raw] using (e (Fin.castLE hlen i)).isLt⟩
  refine ⟨rows, ?_, ?_⟩
  · intro i j hij
    change (e (Fin.castLE hlen i) : ℕ) <
      (e (Fin.castLE hlen j) : ℕ)
    exact e.strictMono (Fin.strictMono_castLE hlen hij)
  · intro i
    let k0 : Fin d.length := Fin.castLE hlen i.castSucc
    let k1 : Fin d.length := Fin.castLE hlen i.succ
    have hklt : (i : ℕ) + 1 < d.length := by lia
    have hchain : d.IsChain (· ≠ ·) :=
      List.isChain_destutter (R := fun a b : SignType => a ≠ b) nz
    have hkd : d.get k0 ≠ d.get k1 := by simpa [k0, k1] using hchain.getElem (i : ℕ) hklt
    have hk0 : d.get k0 ≠ 0 := by
      have hm : d.get k0 ∈ nz :=
        (List.destutter_sublist
          (R := fun a b : SignType => a ≠ b) nz).mem
            (List.get_mem d k0)
      exact of_decide_eq_true (List.mem_filter.mp hm).2
    have hk1 : d.get k1 ≠ 0 := by
      have hm : d.get k1 ∈ nz :=
        (List.destutter_sublist
          (R := fun a b : SignType => a ≠ b) nz).mem
            (List.get_mem d k1)
      exact of_decide_eq_true (List.mem_filter.mp hm).2
    have he0 :
        d.get k0 = SignType.sign (y (rows i.castSucc)) := by
      simpa [raw, rows, k0, Function.comp_apply] using he k0
    have he1 :
        d.get k1 = SignType.sign (y (rows i.succ)) := by
      simpa [raw, rows, k1, Function.comp_apply] using he k1
    apply mul_neg_of_sign_ne
    · rw [← he0]
      exact hk0
    · rw [← he1]
      exact hk1
    · rw [← he0, ← he1]
      exact hkd

/-- A strictly alternating subsequence gives a lower bound on the sign
variations of the ambient vector. -/
lemma StrictlyAlternates.le_signVariations_of_strictMono
    {m q : ℕ} {y : Fin m → ℝ}
    {rows : Fin (q + 1) → Fin m}
    (h : StrictlyAlternates (fun i => y (rows i)))
    (hrows : StrictMono rows) : q ≤ signVariations y := by
  by_cases hq : q = 0
  · simp [hq]
  have hnonzero : ∀ i, y (rows i) ≠ 0 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hy
      let i0 : Fin q := ⟨0, Nat.pos_of_ne_zero hq⟩
      have hneg := h i0
      change y (rows 0) * y (rows i0.succ) < 0 at hneg
      rw [hy, zero_mul] at hneg
      exact (lt_irrefl 0) hneg
    · intro hy
      have hneg := h j
      change y (rows j.castSucc) * y (rows j.succ) < 0 at hneg
      rw [hy, mul_zero] at hneg
      exact (lt_irrefl 0) hneg
  have hsub :
      (List.ofFn (SignType.sign ∘ fun i => y (rows i))).Sublist
        (List.ofFn (SignType.sign ∘ y)) := by
    rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
    let e0 :
        Fin (List.ofFn (SignType.sign ∘ fun i => y (rows i))).length ≃o
          Fin (q + 1) :=
      Fin.castOrderIso List.length_ofFn
    let e1 : Fin (q + 1) ↪o Fin m :=
      OrderEmbedding.ofStrictMono rows hrows
    let e2 :
        Fin m ≃o Fin (List.ofFn (SignType.sign ∘ y)).length :=
      (Fin.castOrderIso List.length_ofFn).symm
    refine ⟨e0.toOrderEmbedding.trans (e1.trans e2.toOrderEmbedding), ?_⟩
    intro i
    simp only [List.get_ofFn, e0, e1, e2, RelEmbedding.trans_apply,
      Function.comp_apply]
    apply congrArg SignType.sign
    apply congrArg y
    apply Fin.ext
    rfl
  have hfilter :
      (List.ofFn (SignType.sign ∘ fun i => y (rows i))).filter
          (· ≠ 0) =
        List.ofFn (SignType.sign ∘ fun i => y (rows i)) := by
    rw [List.filter_eq_self]
    intro s hs
    simp only [List.mem_ofFn] at hs
    obtain ⟨i, rfl⟩ := hs
    simp [Function.comp_apply, hnonzero i]
  have hsub_nonzero :
      (List.ofFn (SignType.sign ∘ fun i => y (rows i))).Sublist
        ((List.ofFn (SignType.sign ∘ y)).filter (· ≠ 0)) := by
    rw [← hfilter]
    exact List.Sublist.filter (· ≠ 0) hsub
  have hchain :
      (List.ofFn (SignType.sign ∘ fun i => y (rows i))).IsChain
        (· ≠ ·) := by
    rw [List.isChain_ofFn]
    intro i hi
    change SignType.sign (y (rows ⟨i, by lia⟩)) ≠
      SignType.sign (y (rows ⟨i + 1, hi⟩))
    have hneg := h (⟨i, by lia⟩ : Fin q)
    change y (rows ⟨i, by lia⟩) * y (rows ⟨i + 1, hi⟩) < 0 at hneg
    rcases mul_neg_iff.mp hneg with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · rw [sign_pos hleft, sign_neg hright]
      simp
    · rw [sign_neg hleft, sign_pos hright]
      simp
  have hlen :=
    List.IsChain.length_le_length_destutter_ne hsub_nonzero hchain
  rw [signVariations, List.signVariations, List.map_ofFn]
  simp only [List.length_ofFn] at hlen
  lia

/-- Two nonzero strictly alternating vectors have pointwise products of one
strict sign. -/
lemma StrictlyAlternates.pointwise_mul_pos_or_neg {n : ℕ}
    {x y : Fin (n + 1) → ℝ} (hx : StrictlyAlternates x)
    (hy : StrictlyAlternates y) (hx0 : x 0 ≠ 0) (hy0 : y 0 ≠ 0) :
    (∀ i, 0 < x i * y i) ∨ (∀ i, x i * y i < 0) := by
  have hxy0 : x 0 * y 0 ≠ 0 := mul_ne_zero hx0 hy0
  rcases lt_or_gt_of_ne hxy0 with hneg | hpos
  · right
    intro i
    induction i using Fin.induction with
    | zero => exact hneg
    | succ i ih =>
        have hstep :
            0 < (x i.castSucc * y i.castSucc) *
              (x i.succ * y i.succ) := by
          rw [show
            (x i.castSucc * y i.castSucc) * (x i.succ * y i.succ) =
              (x i.castSucc * x i.succ) *
                (y i.castSucc * y i.succ) by ring]
          exact mul_pos_of_neg_of_neg (hx i) (hy i)
        exact neg_of_mul_pos_right hstep ih.le
  · left
    intro i
    induction i using Fin.induction with
    | zero => exact hpos
    | succ i ih =>
        have hstep :
            0 < (x i.castSucc * y i.castSucc) *
              (x i.succ * y i.succ) := by
          rw [show
            (x i.castSucc * y i.castSucc) * (x i.succ * y i.succ) =
              (x i.castSucc * x i.succ) *
                (y i.castSucc * y i.succ) by ring]
          exact mul_pos_of_neg_of_neg (hx i) (hy i)
        exact pos_of_mul_pos_right hstep ih.le

lemma signVariations_congr_sign {R : Type*} [Zero R] [LinearOrder R]
    {n : ℕ} {x y : Fin n → R}
    (h : ∀ i, SignType.sign (x i) = SignType.sign (y i)) :
    signVariations x = signVariations y := by
  rw [signVariations, signVariations, List.signVariations,
    List.signVariations, List.map_ofFn, List.map_ofFn]
  congr 4
  apply congrArg List.ofFn
  funext i
  exact h i

lemma signVariations_neg {n : ℕ} (x : Fin n → ℝ) :
    signVariations (fun i => -x i) = signVariations x := by
  rw [signVariations, signVariations]
  have hmap : List.ofFn (fun i : Fin n => -x i) = (List.ofFn x).map Neg.neg := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    rfl
  rw [hmap]
  exact List.signVariations_neg (List.ofFn x)

/-- A finite real vector with no positive entries has no sign variations. -/
lemma signVariations_eq_zero_of_forall_nonpos {n : ℕ} (x : Fin n → ℝ)
    (h : ∀ i, x i ≤ 0) : signVariations x = 0 := by
  rw [signVariations]
  exact List.signVariations_eq_zero_of_forall_nonpos (List.ofFn x) (by
    intro y hy
    simp only [List.mem_ofFn] at hy
    obtain ⟨i, rfl⟩ := hy
    exact h i)

/-- A nonzero vector whose signs alternate at every adjacent pair has the
largest possible number of sign variations. -/
lemma signVariations_eq_length_sub_one {R : Type*} [Zero R] [LinearOrder R]
    {n : ℕ} (x : Fin n → R) (hnonzero : ∀ i, x i ≠ 0)
    (hchain : (List.ofFn (SignType.sign ∘ x)).IsChain (· ≠ ·)) :
    signVariations x = n - 1 := by
  rw [signVariations, List.signVariations, List.map_ofFn]
  have hfilter : (List.ofFn (SignType.sign ∘ x)).filter (· ≠ 0) =
      List.ofFn (SignType.sign ∘ x) := by
    rw [List.filter_eq_self]
    intro s hs
    simp only [List.mem_ofFn] at hs
    obtain ⟨i, rfl⟩ := hs
    simp [Function.comp_apply, hnonzero i]
  rw [hfilter, List.destutter_of_isChain _ _ hchain]
  simp

lemma sign_alternating (n : ℕ) {ε : ℝ} (hε : 0 < ε) (i : Fin n) :
    SignType.sign ((-1 : ℝ) ^ (i : ℕ) * ε) =
      (-1 : SignType) ^ (i : ℕ) := by
  rw [sign_mul, sign_pow]
  simp [hε]

/-- The alternating output used in Karlin's sector proof has exactly `n - 1`
sign variations. -/
lemma signVariations_alternating (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    signVariations (fun i : Fin n => (-1 : ℝ) ^ (i : ℕ) * ε) = n - 1 := by
  apply signVariations_eq_length_sub_one
  · intro i
    positivity
  rw [List.isChain_ofFn]
  intro i hi
  change SignType.sign ((-1 : ℝ) ^ i * ε) ≠
    SignType.sign ((-1 : ℝ) ^ (i + 1) * ε)
  rw [sign_alternating n hε ⟨i, by lia⟩,
    sign_alternating n hε ⟨i + 1, hi⟩]
  simp [pow_succ]

lemma strictlyAlternates_alternating (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    StrictlyAlternates
      (fun i : Fin (n + 1) => (-1 : ℝ) ^ (i : ℕ) * ε) := by
  intro i
  simp only [Fin.val_succ, Fin.val_castSucc, pow_succ]
  have hpow : ((-1 : ℝ) ^ (i : ℕ)) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  calc
    (-1 : ℝ) ^ (i : ℕ) * ε * ((-1) ^ (i : ℕ) * -1 * ε) =
        -(((-1 : ℝ) ^ (i : ℕ)) ^ 2 * ε ^ 2) := by ring
    _ = -(ε ^ 2) := by rw [hpow, one_mul]
    _ < 0 := neg_lt_zero.mpr (sq_pos_of_pos hε)

end Fin

/-- Sign variation is monotone under taking a list prefix. -/
theorem List.signVariations_mono_of_prefix
    {R : Type*} [Zero R] [LinearOrder R]
    {l₁ l₂ : List R} (h : l₁ <+: l₂) :
    l₁.signVariations ≤ l₂.signVariations := by
  rw [List.signVariations, List.signVariations]
  have hsign :
      (l₁.map SignType.sign).filter (· ≠ 0) <+:
        (l₂.map SignType.sign).filter (· ≠ 0) :=
    (h.map SignType.sign).filter (· ≠ 0)
  exact (Nat.sub_le_sub_right
    (hsign.destutter (R := fun x y : SignType => x ≠ y)).length_le) 1

/-- Taking a list prefix cannot increase sign variation. -/
theorem List.signVariations_take_le
    {R : Type*} [Zero R] [LinearOrder R]
    (l : List R) (k : ℕ) :
    (l.take k).signVariations ≤ l.signVariations :=
  List.signVariations_mono_of_prefix (List.take_prefix k l)

/-- A nonzero endpoint survives sign filtering as the final sign of its prefix. -/
theorem List.getLast?_filter_sign_take_succ
    {R : Type*} [Zero R] [LinearOrder R]
    (l : List R) {i : ℕ} (hi : i < l.length)
    (hne : l[i] ≠ 0) :
    (((l.take (i + 1)).map SignType.sign).filter
      (· ≠ 0)).getLast? = some (SignType.sign l[i]) := by
  rw [List.take_succ_eq_append_getElem hi, List.map_append,
    List.filter_append]
  simp [sign_ne_zero.mpr hne]

/-- Appending one real entry increases sign variation by at most one. -/
theorem List.signVariations_append_singleton_le_succ
    (l : List ℝ) (x : ℝ) :
    (l ++ [x]).signVariations ≤ l.signVariations + 1 := by
  rcases le_total 0 x with hx | hx
  · apply List.signVariations_append_nonneg_le_succ
    simpa using hx
  · apply List.signVariations_append_nonpos_le_succ
    simpa using hx

/-- Data expressing a finite vector as nonnegative weights pulled back from an
ordered collection of sign blocks.

This is an interface for the elementary finite-list decomposition in Karlin's
proof, not an assertion that the decomposition already exists. Separating the
data keeps later matrix arguments independent of how maximal same-sign blocks
are constructed and avoids formalizing an unrelated combinatorial model. -/
structure Fin.SignBlockDecomposition {n : ℕ} (c : Fin n → ℝ) where
  numBlocks : ℕ
  numBlocks_pos : 0 < numBlocks
  block : Fin n → Fin numBlocks
  block_mono : Monotone block
  weight : Fin n → ℝ
  weight_nonneg : ∀ j, 0 ≤ weight j
  coeff : Fin numBlocks → ℝ
  reconstruct : ∀ j, weight j * coeff (block j) = c j
  numBlocks_sub_one : numBlocks - 1 = Fin.signVariations c

/-- The sign variation of the prefix ending at `j`. -/
def Fin.prefixSignVariations
    {n : ℕ} (c : Fin n → ℝ) (j : Fin n) : ℕ :=
  ((List.ofFn c).take (j + 1)).signVariations

/-- Prefix sign variation is at most the index of the prefix endpoint. -/
theorem Fin.prefixSignVariations_le_val
    {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    Fin.prefixSignVariations c j ≤ j := by
  unfold Fin.prefixSignVariations
  calc
    ((List.ofFn c).take (j + 1)).signVariations ≤
        ((List.ofFn c).take (j + 1)).length - 1 :=
      List.signVariations_le_length_sub_one _
    _ = j := by simp

/-- At the final index, prefix sign variation is full-vector sign variation. -/
theorem Fin.prefixSignVariations_last
    {n : ℕ} (c : Fin (n + 1) → ℝ) :
    Fin.prefixSignVariations c (Fin.last n) =
      Fin.signVariations c := by
  rw [Fin.prefixSignVariations, Fin.signVariations]
  have hlength :
      (Fin.last n : ℕ) + 1 = (List.ofFn c).length := by
    simp
  rw [hlength, List.take_length]

/-- Prefix sign variation is monotone in the prefix endpoint. -/
theorem Fin.monotone_prefixSignVariations
    {n : ℕ} (c : Fin n → ℝ) :
    Monotone (Fin.prefixSignVariations c) := by
  intro i j hij
  unfold Fin.prefixSignVariations
  apply List.signVariations_mono_of_prefix
  exact List.take_prefix_take_left (Nat.add_le_add_right hij 1)

/-- Prefix sign variation is bounded by full-vector sign variation. -/
theorem Fin.prefixSignVariations_le_signVariations
    {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    Fin.prefixSignVariations c j ≤ Fin.signVariations c := by
  unfold Fin.prefixSignVariations Fin.signVariations
  exact List.signVariations_take_le _ _

/-- The sign-block index of an entry, counted by prefix sign variation. -/
@[expose]
def Fin.signBlockIndex
    {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    Fin (Fin.signVariations c + 1) :=
  ⟨Fin.prefixSignVariations c j,
    Nat.lt_succ_of_le (Fin.prefixSignVariations_le_signVariations c j)⟩

@[simp]
theorem Fin.val_signBlockIndex
    {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    (Fin.signBlockIndex c j : ℕ) =
      Fin.prefixSignVariations c j :=
  rfl

@[simp]
theorem Fin.signBlockIndex_last
    {n : ℕ} (c : Fin (n + 1) → ℝ) :
    Fin.signBlockIndex c (Fin.last n) =
      Fin.last (Fin.signVariations c) := by
  apply Fin.ext
  exact Fin.prefixSignVariations_last c

/-- Sign-block indices are monotone in the original index. -/
theorem Fin.monotone_signBlockIndex
    {n : ℕ} (c : Fin n → ℝ) :
    Monotone (Fin.signBlockIndex c) := by
  intro i j hij
  exact Fin.monotone_prefixSignVariations c hij

/-- Adjacent prefix sign-variation values differ by at most one. -/
theorem Fin.prefixSignVariations_succ_le
    {n : ℕ} (c : Fin (n + 1) → ℝ) (i : Fin n) :
    Fin.prefixSignVariations c i.succ ≤
      Fin.prefixSignVariations c i.castSucc + 1 := by
  unfold Fin.prefixSignVariations
  have hindex :
      (i : ℕ) + 1 < (List.ofFn c).length := by
    simp [i.isLt]
  rw [show (i.succ : ℕ) + 1 = ((i : ℕ) + 1) + 1 by simp,
    List.take_succ_eq_append_getElem hindex]
  exact List.signVariations_append_singleton_le_succ _ _

/-- Nonzero entries with equal block index and ordered indices have equal signs. -/
theorem Fin.sign_eq_of_le_of_signBlockIndex_eq
    {n : ℕ} (c : Fin n → ℝ) {i j : Fin n}
    (hij : i ≤ j) (hi : c i ≠ 0) (hj : c j ≠ 0)
    (hblock : Fin.signBlockIndex c i = Fin.signBlockIndex c j) :
    SignType.sign (c i) = SignType.sign (c j) := by
  let l := List.ofFn c
  let sᵢ :=
    ((l.take (i + 1)).map SignType.sign).filter (· ≠ 0)
  let sⱼ :=
    ((l.take (j + 1)).map SignType.sign).filter (· ≠ 0)
  have hprefix : sᵢ <+: sⱼ :=
    ((List.take_prefix_take_left
      (Nat.add_le_add_right hij 1)).map SignType.sign).filter (· ≠ 0)
  have hprefEq :
      Fin.prefixSignVariations c i =
        Fin.prefixSignVariations c j := by
    simpa only [Fin.val_signBlockIndex] using congrArg Fin.val hblock
  have hvariationEq :
      (sᵢ.destutter (· ≠ ·)).length - 1 =
        (sⱼ.destutter (· ≠ ·)).length - 1 := by
    change (l.take (i + 1)).signVariations =
      (l.take (j + 1)).signVariations at hprefEq
    change (sᵢ.destutter (· ≠ ·)).length - 1 =
      (sⱼ.destutter (· ≠ ·)).length - 1 at hprefEq
    exact hprefEq
  have hiIndex : (i : ℕ) < l.length := by simp [l]
  have hjIndex : (j : ℕ) < l.length := by simp [l]
  have hiValue : l[i] ≠ 0 := by simpa [l] using hi
  have hjValue : l[j] ≠ 0 := by simpa [l] using hj
  have hlastI :
      sᵢ.getLast? = some (SignType.sign (c i)) := by
    simpa [sᵢ, l] using
      List.getLast?_filter_sign_take_succ l hiIndex hiValue
  have hlastJ :
      sⱼ.getLast? = some (SignType.sign (c j)) := by
    simpa [sⱼ, l] using
      List.getLast?_filter_sign_take_succ l hjIndex hjValue
  have hdestIPos : 0 < (sᵢ.destutter (· ≠ ·)).length := by
    rw [List.length_pos_iff]
    intro hd
    have hlastDest := List.getLast?_destutter_ne sᵢ
    rw [hd, hlastI] at hlastDest
    simp at hlastDest
  have hdestLengthLe :
      (sᵢ.destutter (· ≠ ·)).length ≤
        (sⱼ.destutter (· ≠ ·)).length :=
    (hprefix.destutter
      (R := fun x y : SignType => x ≠ y)).length_le
  have hlengthEq :
      (sᵢ.destutter (· ≠ ·)).length =
        (sⱼ.destutter (· ≠ ·)).length := by
    lia
  have hlastEq : sᵢ.getLast? = sⱼ.getLast? :=
    hprefix.getLast?_eq_of_destutter_length_le hlengthEq.ge
  rw [hlastI, hlastJ] at hlastEq
  exact Option.some.inj hlastEq

/-- Nonzero entries in the same sign block have equal signs. -/
theorem Fin.sign_eq_of_signBlockIndex_eq
    {n : ℕ} (c : Fin n → ℝ) {i j : Fin n}
    (hi : c i ≠ 0) (hj : c j ≠ 0)
    (hblock : Fin.signBlockIndex c i = Fin.signBlockIndex c j) :
    SignType.sign (c i) = SignType.sign (c j) := by
  rcases le_total i j with hij | hji
  · exact Fin.sign_eq_of_le_of_signBlockIndex_eq c hij hi hj hblock
  · exact (Fin.sign_eq_of_le_of_signBlockIndex_eq
      c hji hj hi hblock.symm).symm

/-- The same-sign block decomposition used in Karlin's variation theorem.

Zero entries receive weight zero. Each block containing a nonzero entry uses
the sign of one such entry as its coefficient; the same-block sign theorem
makes this choice independent of the representative for reconstruction. -/
noncomputable def Fin.signBlockDecomposition
    {n : ℕ} (c : Fin n → ℝ) : Fin.SignBlockDecomposition c := by
  classical
  let coeff : Fin (Fin.signVariations c + 1) → ℝ := fun b =>
    if h : ∃ j, c j ≠ 0 ∧ Fin.signBlockIndex c j = b then
      (SignType.sign (c h.choose) : ℝ)
    else 0
  refine
    { numBlocks := Fin.signVariations c + 1
      numBlocks_pos := Nat.succ_pos _
      block := Fin.signBlockIndex c
      block_mono := Fin.monotone_signBlockIndex c
      weight := fun j => |c j|
      weight_nonneg := fun j => abs_nonneg (c j)
      coeff := coeff
      reconstruct := ?_
      numBlocks_sub_one := Nat.add_sub_cancel _ _ }
  intro j
  by_cases hj : c j = 0
  · simp only [hj, abs_zero, zero_mul]
  · have hex :
        ∃ k, c k ≠ 0 ∧
          Fin.signBlockIndex c k = Fin.signBlockIndex c j :=
      ⟨j, hj, rfl⟩
    change |c j| * coeff (Fin.signBlockIndex c j) = c j
    rw [show coeff (Fin.signBlockIndex c j) =
        (SignType.sign (c hex.choose) : ℝ) by
      simp only [coeff, dif_pos hex],
      ← Fin.sign_eq_of_signBlockIndex_eq c hj
        hex.choose_spec.1 hex.choose_spec.2.symm,
      abs_mul_sign]
