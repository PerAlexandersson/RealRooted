module

public import Mathlib.Algebra.Polynomial.RuleOfSigns
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Tactic

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

namespace Fin

/-- The number of sign changes in a finite vector, in index order and ignoring
zero entries. -/
def signVariations {R : Type*} [Zero R] [LinearOrder R] {n : ℕ}
    (x : Fin n → R) : ℕ :=
  (List.ofFn x).signVariations

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
  have hhead : SignType.sign (List.head (List.ofFn x) hlist_ne) = 0 := by
    simp [hzero]
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
