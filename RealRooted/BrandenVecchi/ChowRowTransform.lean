import RealRooted.BrandenVecchi.ChowInterlacing
import RealRooted.ReciprocalShift.ProperPosition

/-!
# The generic Chow staircase row transform

This file formalizes Branden--Vecchi, Theorem 4.13.  It first develops the
small zero-aware list operations needed to group a reflection-interlacing row
into contiguous block sums.
-/

open Polynomial

noncomputable section

namespace RealRooted

private theorem pairwise_insert_zero {left right : List ℝ[X]}
    (h : (left ++ right).Pairwise Prec0) :
    (left ++ 0 :: right).Pairwise Prec0 := by
  rw [List.pairwise_append] at h ⊢
  refine ⟨h.1, ?_, ?_⟩
  · rw [List.pairwise_cons]
    exact ⟨fun p _ => prec0_zero_left p, h.2.1⟩
  · intro p hp q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact prec0_zero_right p
    · exact h.2.2 p hp q hq

private theorem IsInterlacingSeq0NonnegRealRooted.insertZero
    {left right : List ℝ[X]}
    (h : IsInterlacingSeq0NonnegRealRooted (left ++ right)) :
    IsInterlacingSeq0NonnegRealRooted (left ++ 0 :: right) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise]
    exact pairwise_insert_zero
      (isInterlacingSeq0_iff_pairwise.mp h.interlacingSeq0)
  · intro p hp
    simp only [List.mem_append, List.mem_cons] at hp
    rcases hp with hp | rfl | hp
    · exact h.nonnegCoeffs p (by simp [hp])
    · exact hasNonnegCoeffs_zero
    · exact h.nonnegCoeffs p (by simp [hp])
  · intro p hp hp_ne
    simp only [List.mem_append, List.mem_cons] at hp
    rcases hp with hp | rfl | hp
    · exact h.realRooted p (by simp [hp]) hp_ne
    · exact (hp_ne rfl).elim
    · exact h.realRooted p (by simp [hp]) hp_ne

private theorem add_ne_zero_of_nonnegCoeffs_of_right_ne_zero
    {p q : ℝ[X]} (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hq_ne : q ≠ 0) : p + q ≠ 0 := by
  let d := q.natDegree
  have hp_coeff : 0 ≤ p.coeff d := hp d
  have hq_coeff : 0 < q.coeff d := by
    change 0 < q.leadingCoeff
    exact hq.pos_leadingCoeff hq_ne
  intro hzero
  have := congrArg (fun r : ℝ[X] => r.coeff d) hzero
  simp only [coeff_add, coeff_zero] at this
  linarith

namespace BrandenVecchi

/-- Insert a zero anywhere in a reflection-interlacing sequence. -/
theorem IsReflectionInterlacingSeq.insertZero
    {n : ℕ} {left right : List ℝ[X]}
    (h : IsReflectionInterlacingSeq n (left ++ right)) :
    IsReflectionInterlacingSeq n (left ++ 0 :: right) := by
  let new : List ℝ[X] := left ++ 0 :: right
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [List.mem_append, List.mem_cons] at hp
    rcases hp with hp | rfl | hp
    · exact h.natDegree_le (by simp [hp])
    · simp
    · exact h.natDegree_le (by simp [hp])
  · have hold :
        IsInterlacingSeq0NonnegRealRooted
          (left ++ (right ++ (right.map fun p => p.reflect n).reverse ++
            (left.map fun p => p.reflect n).reverse)) := by
      simpa [reflectionClosure, List.reverse_append,
        List.append_assoc] using h.closedSequence
    have hfirst := hold.insertZero
        (left := left)
        (right := right ++ (right.map fun p => p.reflect n).reverse ++
          (left.map fun p => p.reflect n).reverse)
    have hfirst' :
        IsInterlacingSeq0NonnegRealRooted
          (new ++ (right.map fun p => p.reflect n).reverse ++
            (left.map fun p => p.reflect n).reverse) := by
      simpa [new, reflectionClosure, List.reverse_append,
        List.append_assoc] using hfirst
    have hsecond := hfirst'.insertZero
      (left := new ++ (right.map fun p => p.reflect n).reverse)
      (right := (left.map fun p => p.reflect n).reverse)
    simpa [new, reflectionClosure, List.reverse_append, List.append_assoc] using hsecond

/-- Replace two adjacent entries by their sum. -/
theorem IsReflectionInterlacingSeq.replaceAdjacentAdd
    {n : ℕ} {left right : List ℝ[X]} {f g : ℝ[X]}
    (h : IsReflectionInterlacingSeq n (left ++ f :: g :: right)) :
    IsReflectionInterlacingSeq n (left ++ (f + g) :: right) := by
  exact h.insertAdjacentAdd.sublist (by simp)

private theorem IsReflectionInterlacingSeq.collapseSuffixFromHead
    {n : ℕ} {left : List ℝ[X]} {f : ℝ[X]} :
    ∀ right : List ℝ[X],
      IsReflectionInterlacingSeq n (left ++ f :: right) →
        IsReflectionInterlacingSeq n (left ++ [f + right.sum])
  | [], h => by simpa using h
  | g :: right, h => by
      have h' := h.replaceAdjacentAdd (left := left) (f := f) (g := g)
        (right := right)
      have ih := IsReflectionInterlacingSeq.collapseSuffixFromHead
        (left := left) (f := f + g) right h'
      simpa [List.sum_cons, add_assoc] using ih

private theorem IsReflectionInterlacingSeq.collapseBlockFromHead
    {n : ℕ} {left right : List ℝ[X]} {f : ℝ[X]} :
    ∀ tail : List ℝ[X],
      IsReflectionInterlacingSeq n (left ++ (f :: tail) ++ right) →
        IsReflectionInterlacingSeq n (left ++ [f + tail.sum] ++ right)
  | [], h => by simpa using h
  | g :: tail, h => by
      have hnorm :
          IsReflectionInterlacingSeq n
            (left ++ f :: g :: (tail ++ right)) := by
        simpa [List.append_assoc] using h
      have h' := IsReflectionInterlacingSeq.replaceAdjacentAdd hnorm
        (left := left) (f := f) (g := g) (right := tail ++ right)
      have ih := IsReflectionInterlacingSeq.collapseBlockFromHead
        (left := left) (right := right) (f := f + g) tail (by
          simpa [List.append_assoc] using h')
      simpa [List.sum_cons, add_assoc] using ih

/-- Replace a contiguous block by its sum. Empty blocks become a zero entry. -/
theorem IsReflectionInterlacingSeq.collapseBlock
    {n : ℕ} {left block right : List ℝ[X]}
    (h : IsReflectionInterlacingSeq n (left ++ block ++ right)) :
    IsReflectionInterlacingSeq n (left ++ [block.sum] ++ right) := by
  cases block with
  | nil =>
      have h' : IsReflectionInterlacingSeq n (left ++ right) := by simpa using h
      simpa using h'.insertZero (left := left) (right := right)
  | cons f tail =>
      exact IsReflectionInterlacingSeq.collapseBlockFromHead
        (left := left) (right := right) (f := f) tail h

/-- Collapse a nonempty suffix to its sum. -/
theorem IsReflectionInterlacingSeq.collapseSuffix
    {n : ℕ} {left right : List ℝ[X]} (hright : right ≠ [])
    (h : IsReflectionInterlacingSeq n (left ++ right)) :
    IsReflectionInterlacingSeq n (left ++ [right.sum]) := by
  obtain ⟨f, tail, rfl⟩ := List.exists_cons_of_ne_nil hright
  simpa [List.sum_cons] using
    (IsReflectionInterlacingSeq.collapseSuffixFromHead
      (left := left) (f := f) tail h)

/-- Three consecutive block sums of a reflection-interlacing row are again
reflection-interlacing. -/
theorem IsReflectionInterlacingSeq.threeBlockSums
    {n : ℕ} {fs : List ℝ[X]} (h : IsReflectionInterlacingSeq n fs)
    {k l : ℕ} (hkl : k ≤ l) :
    IsReflectionInterlacingSeq n
      [(fs.take k).sum, ((fs.drop k).take (l - k)).sum, (fs.drop l).sum] := by
  let left := fs.take k
  let middle := (fs.drop k).take (l - k)
  let right := fs.drop l
  have hsplit : left ++ middle ++ right = fs := by
    dsimp [left, middle, right]
    have hright :
        (fs.drop k).take (l - k) ++ fs.drop l = fs.drop k := by
      calc
        (fs.drop k).take (l - k) ++ fs.drop l =
            (fs.drop k).take (l - k) ++ (fs.drop k).drop (l - k) := by
              simp [List.drop_drop, Nat.add_sub_of_le hkl]
        _ = fs.drop k := List.take_append_drop _ _
    rw [List.append_assoc, hright, List.take_append_drop]
  have hblocks : IsReflectionInterlacingSeq n (left ++ middle ++ right) :=
    hsplit.symm ▸ h
  have hleft := IsReflectionInterlacingSeq.collapseBlock
    (left := []) (block := left) (right := middle ++ right)
    (by simpa [List.append_assoc] using hblocks)
  have hmiddle := IsReflectionInterlacingSeq.collapseBlock
    (left := [left.sum]) (block := middle) (right := right)
    (by simpa [List.append_assoc] using hleft)
  have hright := IsReflectionInterlacingSeq.collapseBlock
    (left := [left.sum, middle.sum]) (block := right) (right := [])
    (by simpa [List.append_assoc] using hmiddle)
  simpa [left, middle, right] using hright

private theorem natDegree_list_sum_le {n : ℕ} {fs : List ℝ[X]}
    (hdeg : ∀ p ∈ fs, p.natDegree ≤ n) : fs.sum.natDegree ≤ n := by
  induction fs with
  | nil => simp
  | cons p fs ih =>
      rw [List.sum_cons]
      exact (natDegree_add_le p fs.sum).trans
        (max_le (hdeg p (by simp)) (ih fun q hq => hdeg q (by simp [hq])))

private theorem chowS_add_of_degree_le {n : ℕ} {p q : ℝ[X]}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    chowS n (p + q) = chowS n p + chowS n q := by
  apply mul_left_cancel₀ (by
    simpa using Polynomial.X_sub_C_ne_zero (1 : ℝ))
  rw [mul_add, X_sub_one_mul_chowS n p hp,
    X_sub_one_mul_chowS n q hq,
    X_sub_one_mul_chowS n (p + q)
      ((natDegree_add_le p q).trans (max_le hp hq)), reflect_add]
  ring

private theorem IsReflectionInterlacingSeq.member_nonnegCoeffs
    {n : ℕ} {fs : List ℝ[X]} (h : IsReflectionInterlacingSeq n fs)
    {p : ℝ[X]} (hp : p ∈ fs) : HasNonnegCoeffs p :=
  h.closedSequence.nonnegCoeffs p (by simp [reflectionClosure, hp])

private theorem IsReflectionInterlacingSeq.member_splits
    {n : ℕ} {fs : List ℝ[X]} (h : IsReflectionInterlacingSeq n fs)
    {p : ℝ[X]} (hp : p ∈ fs) (hp_ne : p ≠ 0) : p.Splits :=
  h.closedSequence.splits (by simp [reflectionClosure, hp]) hp_ne

/-- The finite row transform in Branden--Vecchi, Theorem 4.13. -/
def chowRowTransform (n : ℕ) (fs : List ℝ[X]) : List ℝ[X] :=
  (List.range (fs.length + 1)).map fun k =>
    X * chowS n fs.sum + (fs.drop k).sum

@[simp] theorem length_chowRowTransform (n : ℕ) (fs : List ℝ[X]) :
    (chowRowTransform n fs).length = fs.length + 1 := by
  simp [chowRowTransform]

theorem getElem_chowRowTransform {n : ℕ} {fs : List ℝ[X]} {k : ℕ}
    (hk : k < fs.length + 1) :
    (chowRowTransform n fs).get ⟨k, by simpa using hk⟩ =
      X * chowS n fs.sum + (fs.drop k).sum := by
  simp [chowRowTransform]

theorem chowRowTransform_nonnegCoeffs
    {n : ℕ} {fs : List ℝ[X]} (h : IsReflectionInterlacingSeq n fs)
    {p : ℝ[X]} (hp : p ∈ chowRowTransform n fs) : HasNonnegCoeffs p := by
  rcases List.mem_map.mp hp with ⟨k, hk, rfl⟩
  have htotal : IsReflectionInterlacingSeq n [fs.sum] := by
    have hcollapsed := IsReflectionInterlacingSeq.collapseBlock
      (left := []) (block := fs) (right := []) (by simpa using h)
    simpa using hcollapsed
  have hSnn : HasNonnegCoeffs (chowS n fs.sum) :=
    (htotal.chowS_nonnegCoeffs_and_prec0_self_reflect).1
  exact hSnn.X_mul.add <| hasNonnegCoeffs_sum _ fun q hq =>
    h.member_nonnegCoeffs (List.mem_of_mem_drop hq)

theorem chowRowTransform_natDegree_le
    {n : ℕ} {fs : List ℝ[X]} (h : IsReflectionInterlacingSeq n fs)
    {p : ℝ[X]} (hp : p ∈ chowRowTransform n fs) :
    p.natDegree ≤ n + 1 := by
  rcases List.mem_map.mp hp with ⟨k, hk, rfl⟩
  have hsumdeg : fs.sum.natDegree ≤ n :=
    natDegree_list_sum_le fun q hq => h.natDegree_le hq
  have hSdeg : (chowS n fs.sum).natDegree ≤ n :=
    natDegree_chowS_le n fs.sum hsumdeg
  have htaildeg : (fs.drop k).sum.natDegree ≤ n :=
    natDegree_list_sum_le fun q hq => h.natDegree_le (List.mem_of_mem_drop hq)
  have hmuldeg : (X * chowS n fs.sum).natDegree ≤ n + 1 :=
    calc
      (X * chowS n fs.sum).natDegree ≤ X.natDegree + (chowS n fs.sum).natDegree :=
        natDegree_mul_le
      _ ≤ n + 1 := by simp; lia
  exact (natDegree_add_le (X * chowS n fs.sum) (fs.drop k).sum).trans
    (max_le hmuldeg (by lia))

/-- Any earlier transformed row member precedes any later one. This is the
three-block cone argument in Branden--Vecchi, Theorem 4.13. -/
theorem chowRowTransform_prec0_of_lt
    {n : ℕ} {fs : List ℝ[X]} (h : IsReflectionInterlacingSeq n fs)
    {k l : ℕ} (hkl : k < l) (hl : l < fs.length + 1) :
    Prec0 (X * chowS n fs.sum + (fs.drop k).sum)
      (X * chowS n fs.sum + (fs.drop l).sum) := by
  let h₀ := (fs.take k).sum
  let h₁ := ((fs.drop k).take (l - k)).sum
  let h₂ := (fs.drop l).sum
  have hl_len : l ≤ fs.length := by lia
  have hthree : IsReflectionInterlacingSeq n [h₀, h₁, h₂] := by
    simpa [h₀, h₁, h₂] using h.threeBlockSums hkl.le
  have h₀₁ : IsReflectionInterlacingSeq n [h₀, h₁] :=
    hthree.sublist (by simp)
  have h₁₁ : IsReflectionInterlacingSeq n [h₁] :=
    hthree.sublist (by simp)
  have h₁₂ : IsReflectionInterlacingSeq n [h₁, h₂] :=
    hthree.sublist (by simp)
  have h₀nn := hthree.member_nonnegCoeffs (p := h₀) (by simp)
  have h₁nn := hthree.member_nonnegCoeffs (p := h₁) (by simp)
  have h₂nn := hthree.member_nonnegCoeffs (p := h₂) (by simp)
  have hS₀nn : HasNonnegCoeffs (chowS n h₀) := h₀₁.chowS_nonnegCoeffs
  have hS₁nn : HasNonnegCoeffs (chowS n h₁) :=
    (h₁₁.chowS_nonnegCoeffs_and_prec0_self_reflect).1
  have hS₂nn : HasNonnegCoeffs (chowS n h₂) :=
    (h₁₂.sublist (by simp) |>
      IsReflectionInterlacingSeq.chowS_nonnegCoeffs_and_prec0_self_reflect).1
  have hh₁XS₀ : Prec0 h₁ (X * chowS n h₀) :=
    prec0_mul_X_of_prec0 h₀₁.chowS_prec0 hS₀nn h₁nn
  have hh₁XS₁ : Prec0 h₁ (X * chowS n h₁) :=
    prec0_mul_X_of_prec0
      (h₁₁.chowS_nonnegCoeffs_and_prec0_self_reflect).2.1 hS₁nn h₁nn
  have hext := h₁₂.chowSExtension
  have hh₁q₂ : Prec0 h₁ (X * chowS n h₂ + h₂) := by
    simpa [reflectionClosure] using
      hext.closedSequence.interlacingSeq0.prec0
        (i := (⟨1, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n
            [chowS n h₁, h₁, h₂, X * chowS n h₂ + h₂]).length))
        (j := (⟨3, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n
            [chowS n h₁, h₁, h₂, X * chowS n h₂ + h₂]).length))
        (by simp)
  have hh₁right :
      Prec0 h₁
        (X * chowS n h₀ + X * chowS n h₁ +
          (X * chowS n h₂ + h₂)) := by
    have hsum : Prec0 h₁
        [X * chowS n h₀, X * chowS n h₁, X * chowS n h₂ + h₂].sum := by
      apply prec0_sum_left_of_common_left_of_nonneg
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl
        · exact hh₁XS₀
        · exact hh₁XS₁
        · exact hh₁q₂
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl
        · exact hS₀nn.X_mul
        · exact hS₁nn.X_mul
        · exact hS₂nn.X_mul.add h₂nn
    simpa [add_assoc] using hsum
  have hrightnn : HasNonnegCoeffs
      (X * chowS n h₀ + X * chowS n h₁ +
        (X * chowS n h₂ + h₂)) :=
    (hS₀nn.X_mul.add hS₁nn.X_mul).add (hS₂nn.X_mul.add h₂nn)
  have hrightself : Prec0
      (X * chowS n h₀ + X * chowS n h₁ +
        (X * chowS n h₂ + h₂))
      (X * chowS n h₀ + X * chowS n h₁ +
        (X * chowS n h₂ + h₂)) := by
    let pre := h₀ + h₁
    let q₂ := X * chowS n h₂ + h₂
    have hpre₂ : IsReflectionInterlacingSeq n [pre, h₂] := by
      simpa [pre] using hthree.replaceAdjacentAdd
        (left := []) (f := h₀) (g := h₁) (right := [h₂])
    have hpredeg : pre.natDegree ≤ n :=
      (natDegree_add_le h₀ h₁).trans (max_le
        (hthree.natDegree_le (f := h₀) (by simp))
        (hthree.natDegree_le (f := h₁) (by simp)))
    have hextpre := hpre₂.chowSExtension
    have hrefpre : (chowS n pre).reflect n = X * chowS n pre :=
      reflect_chowS n pre hpredeg
    have hpairseq : IsInterlacingSeq0NonnegRealRooted
        [q₂, X * chowS n pre] := by
      apply hextpre.closedSequence.sublist
      simp only [reflectionClosure, List.map_cons, List.map_nil,
        List.reverse_cons, List.reverse_nil, List.nil_append, hrefpre]
      apply List.Sublist.cons
      apply List.Sublist.cons
      apply List.Sublist.cons
      apply List.Sublist.cons_cons
      apply List.Sublist.cons
      apply List.Sublist.cons
      apply List.Sublist.cons
      exact List.Sublist.refl _
    have hsuminsert := hpairseq.insertAdjacentAdd
      (left := []) (f := q₂) (g := X * chowS n pre) (right := [])
    have hsumseq : IsInterlacingSeq0NonnegRealRooted
        [q₂ + X * chowS n pre] :=
      hsuminsert.sublist (by simp)
    have hsumpf : IsPFPolynomial (q₂ + X * chowS n pre) := by
      apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
      · exact hsumseq.nonnegCoeffs _ (by simp)
      · by_cases hsumzero : q₂ + X * chowS n pre = 0
        · exact Or.inl hsumzero
        · exact Or.inr (hsumseq.splits (by simp) hsumzero)
    have hright_eq :
        X * chowS n h₀ + X * chowS n h₁ +
            (X * chowS n h₂ + h₂) = q₂ + X * chowS n pre := by
      rw [show chowS n pre = chowS n h₀ + chowS n h₁ by
        exact chowS_add_of_degree_le
          (hthree.natDegree_le (f := h₀) (by simp))
          (hthree.natDegree_le (f := h₁) (by simp))]
      simp only [q₂]
      ring
    rw [hright_eq]
    exact hsumpf.prec0_self
  have hpair := prec0_add_left_of_common_right_of_nonneg
    hh₁right hrightself h₁nn hrightnn
  have htotal : fs.sum = h₀ + h₁ + h₂ := by
    have hsplit : fs.take k ++ (fs.drop k).take (l - k) ++ fs.drop l = fs := by
      have hmiddle :
          (fs.drop k).take (l - k) ++ fs.drop l = fs.drop k := by
        calc
          (fs.drop k).take (l - k) ++ fs.drop l =
              (fs.drop k).take (l - k) ++ (fs.drop k).drop (l - k) := by
                simp [List.drop_drop, Nat.add_sub_of_le hkl.le]
          _ = fs.drop k := List.take_append_drop _ _
      rw [List.append_assoc, hmiddle, List.take_append_drop]
    rw [← hsplit, List.sum_append, List.sum_append]
  have hdropk : (fs.drop k).sum = h₁ + h₂ := by
    have hsplit : (fs.drop k).take (l - k) ++ fs.drop l = fs.drop k := by
      calc
        (fs.drop k).take (l - k) ++ fs.drop l =
            (fs.drop k).take (l - k) ++ (fs.drop k).drop (l - k) := by
              simp [List.drop_drop, Nat.add_sub_of_le hkl.le]
        _ = fs.drop k := List.take_append_drop _ _
    rw [← hsplit, List.sum_append]
  have h₀deg := hthree.natDegree_le (f := h₀) (by simp)
  have h₁deg := hthree.natDegree_le (f := h₁) (by simp)
  have h₂deg := hthree.natDegree_le (f := h₂) (by simp)
  rw [htotal, chowS_add_of_degree_le
    ((natDegree_add_le h₀ h₁).trans (max_le h₀deg h₁deg)) h₂deg,
    chowS_add_of_degree_le h₀deg h₁deg, hdropk]
  simpa [mul_add, add_assoc, add_left_comm, add_comm] using hpair

private theorem chowRowTerm_isPF
    {n : ℕ} {fs : List ℝ[X]} (h : IsReflectionInterlacingSeq n fs)
    {k : ℕ} :
    IsPFPolynomial (X * chowS n fs.sum + (fs.drop k).sum) := by
  let a := (fs.take k).sum
  let b := (fs.drop k).sum
  have hab : IsReflectionInterlacingSeq n [a, b] := by
    have hsplit : fs.take k ++ fs.drop k = fs := List.take_append_drop _ _
    have h' : IsReflectionInterlacingSeq n (fs.take k ++ fs.drop k) := hsplit.symm ▸ h
    have ha := IsReflectionInterlacingSeq.collapseBlock
      (left := []) (block := fs.take k) (right := fs.drop k) (by simpa using h')
    have hb := IsReflectionInterlacingSeq.collapseBlock
      (left := [(fs.take k).sum]) (block := fs.drop k) (right := [])
      (by simpa using ha)
    simpa [a, b] using hb
  have hadeg := hab.natDegree_le (f := a) (by simp)
  have hext := hab.chowSExtension
  have hrefa : (chowS n a).reflect n = X * chowS n a :=
    reflect_chowS n a hadeg
  have hpair : IsInterlacingSeq0NonnegRealRooted
      [X * chowS n b + b, X * chowS n a] := by
    apply hext.closedSequence.sublist
    simp only [reflectionClosure, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, hrefa]
    apply List.Sublist.cons
    apply List.Sublist.cons
    apply List.Sublist.cons
    apply List.Sublist.cons_cons
    apply List.Sublist.cons
    apply List.Sublist.cons
    apply List.Sublist.cons
    exact List.Sublist.refl _
  have hins := hpair.insertAdjacentAdd
    (left := []) (f := X * chowS n b + b) (g := X * chowS n a) (right := [])
  have hsingle : IsInterlacingSeq0NonnegRealRooted
      [(X * chowS n b + b) + X * chowS n a] :=
    hins.sublist (by simp)
  have hsum_pf : IsPFPolynomial ((X * chowS n b + b) + X * chowS n a) := by
    apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    · exact hsingle.nonnegCoeffs _ (by simp)
    · by_cases hz : (X * chowS n b + b) + X * chowS n a = 0
      · exact Or.inl hz
      · exact Or.inr (hsingle.splits (by simp) hz)
  have hsum : fs.sum = a + b := by
    rw [← List.take_append_drop k fs, List.sum_append]
  have hbdeg := hab.natDegree_le (f := b) (by simp)
  have heq : X * chowS n fs.sum + (fs.drop k).sum =
      (X * chowS n b + b) + X * chowS n a := by
    rw [hsum, chowS_add_of_degree_le hadeg hbdeg]
    simp only [a, b]
    ring
  rw [heq]
  exact hsum_pf

/-- The direct transformed row is always a zero-aware nonnegative
real-rooted interlacing sequence. -/
theorem IsReflectionInterlacingSeq.chowRowTransform_direct
    {n : ℕ} {fs : List ℝ[X]} (h : IsReflectionInterlacingSeq n fs) :
    IsInterlacingSeq0NonnegRealRooted (chowRowTransform n fs) := by
  refine ⟨⟨?_, fun p hp => chowRowTransform_nonnegCoeffs h hp⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise, List.pairwise_iff_get]
    intro i j hij
    have hi : i.val < fs.length + 1 := by simpa using i.isLt
    have hj : j.val < fs.length + 1 := by simpa using j.isLt
    have hp := chowRowTransform_prec0_of_lt h hij hj
    rw [← getElem_chowRowTransform hi, ← getElem_chowRowTransform hj] at hp
    exact hp
  · intro p hp hp_ne
    rcases List.mem_map.mp hp with ⟨k, _, rfl⟩
    exact ⟨hp_ne, (chowRowTerm_isPF h).ne_zero_and_splits hp_ne |>.2⟩

theorem chowRowTransform_eq_suffixSums_of_chowS_eq_zero
    {n : ℕ} {fs : List ℝ[X]} (hS : chowS n fs.sum = 0) :
    chowRowTransform n fs =
      (List.range (fs.length + 1)).map fun k => (fs.drop k).sum := by
  simp [chowRowTransform, hS]

private theorem chowS_drop_eq_zero_of_sum_eq_zero
    {n : ℕ} {fs : List ℝ[X]} (h : IsReflectionInterlacingSeq n fs)
    (hS : chowS n fs.sum = 0) (k : ℕ) :
    chowS n (fs.drop k).sum = 0 := by
  let a := (fs.take k).sum
  let b := (fs.drop k).sum
  have hab : IsReflectionInterlacingSeq n [a, b] := by
    have hsplit : fs.take k ++ fs.drop k = fs := List.take_append_drop _ _
    have h' : IsReflectionInterlacingSeq n (fs.take k ++ fs.drop k) := hsplit.symm ▸ h
    have ha := IsReflectionInterlacingSeq.collapseBlock
      (left := []) (block := fs.take k) (right := fs.drop k) (by simpa using h')
    have hb := IsReflectionInterlacingSeq.collapseBlock
      (left := [(fs.take k).sum]) (block := fs.drop k) (right := [])
      (by simpa using ha)
    simpa [a, b] using hb
  have hadeg := hab.natDegree_le (f := a) (by simp)
  have hbdeg := hab.natDegree_le (f := b) (by simp)
  have hSann : HasNonnegCoeffs (chowS n a) := hab.chowS_nonnegCoeffs
  have hb_single : IsReflectionInterlacingSeq n [b] := hab.sublist (by simp)
  have hSbnn : HasNonnegCoeffs (chowS n b) :=
    (hb_single.chowS_nonnegCoeffs_and_prec0_self_reflect).1
  have hsum : fs.sum = a + b := by
    rw [← List.take_append_drop k fs, List.sum_append]
  have hzero : chowS n a + chowS n b = 0 := by
    rw [← chowS_add_of_degree_le hadeg hbdeg, ← hsum, hS]
  have hSb : chowS n b = 0 := by
    ext d
    have hz := congrArg (fun p : ℝ[X] => p.coeff d) hzero
    simp only [coeff_add, coeff_zero] at hz ⊢
    have ha0 := hSann d
    have hb0 := hSbnn d
    linarith
  simpa [b] using hSb

private theorem drop_sum_reflect_eq_self_of_chowS_sum_eq_zero
    {n : ℕ} {fs : List ℝ[X]} (h : IsReflectionInterlacingSeq n fs)
    (hS : chowS n fs.sum = 0) (k : ℕ) :
    ((fs.drop k).sum).reflect n = (fs.drop k).sum := by
  have hdeg : (fs.drop k).sum.natDegree ≤ n :=
    natDegree_list_sum_le fun p hp => h.natDegree_le (List.mem_of_mem_drop hp)
  have hfactor := X_sub_one_mul_chowS n (fs.drop k).sum hdeg
  have hSk := chowS_drop_eq_zero_of_sum_eq_zero h hS k
  have hdiff : ((fs.drop k).sum).reflect n - (fs.drop k).sum = 0 := by
    calc
      ((fs.drop k).sum).reflect n - (fs.drop k).sum =
          (X - 1) * chowS n (fs.drop k).sum := hfactor.symm
      _ = 0 := by rw [hSk]; ring
  exact sub_eq_zero.mp hdiff

/-- The vanishing-total-quotient branch of Branden--Vecchi, Theorem 4.13. -/
theorem IsReflectionInterlacingSeq.chowRowTransform_of_chowS_eq_zero
    {n : ℕ} {fs : List ℝ[X]} (h : IsReflectionInterlacingSeq n fs)
    (hS : chowS n fs.sum = 0) :
    IsReflectionInterlacingSeq (n + 1) (chowRowTransform n fs) := by
  let out := chowRowTransform n fs
  let refs := (out.map fun p => p.reflect (n + 1)).reverse
  have hdirect := h.chowRowTransform_direct
  have houtdeg : ∀ p ∈ out, p.natDegree ≤ n := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨k, hk, rfl⟩
    rw [hS]
    simp only [mul_zero, zero_add]
    exact natDegree_list_sum_le fun q hq =>
      h.natDegree_le (List.mem_of_mem_drop hq)
  have houtsym : ∀ p ∈ out, p.reflect n = p := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨k, hk, rfl⟩
    rw [hS]
    simp only [mul_zero, zero_add]
    exact drop_sum_reflect_eq_self_of_chowS_sum_eq_zero h hS k
  have houtpf : ∀ p ∈ out, IsPFPolynomial p := by
    intro p hp
    apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    · exact hdirect.nonnegCoeffs p hp
    · by_cases hp0 : p = 0
      · exact Or.inl hp0
      · exact Or.inr (hdirect.splits hp hp0)
  have hrefout : ∀ p ∈ out, p.reflect (n + 1) = X * p := by
    intro p hp
    rw [Polynomial.reflect_succ p (houtdeg p hp), houtsym p hp]
    ring
  have hrefs : refs.Pairwise Prec0 := by
    have hrev := hdirect.interlacingSeq0.reverse
    have hrev' : out.reverse.Pairwise
        (fun p q => Prec0 (p.reflect (n + 1)) (q.reflect (n + 1))) :=
      hrev.imp_of_mem (by
      intro p q hp hq hpq
      have hpout : p ∈ out := by simpa using hp
      have hqout : q ∈ out := by simpa using hq
      rcases hpq with hp0 | hq0 | hpq
      · subst q
        simp [prec0_zero_right]
      · subst p
        simp [prec0_zero_left]
      · exact (reciprocalShift_reverses_prec
          (houtpf q hqout) (houtpf p hpout)
          ((houtdeg q hqout).trans (by lia))
          ((houtdeg p hpout).trans (by lia)) hpq).toPrec0)
    have hmap := hrev'.map (fun p => p.reflect (n + 1)) (by
      intro p q hpq
      exact hpq)
    simpa [refs, List.map_reverse] using hmap
  refine ⟨?_, ?_⟩
  · intro p hp
    exact (houtdeg p hp).trans (by lia)
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [isInterlacingSeq0_iff_pairwise, reflectionClosure,
        List.pairwise_append]
      refine ⟨isInterlacingSeq0_iff_pairwise.mp hdirect.interlacingSeq0,
        hrefs, ?_⟩
      intro p hp r hr
      have hrrefs : r ∈ refs := by simpa [refs] using hr
      have hrmap : r ∈ out.map (fun q => q.reflect (n + 1)) := by
        simpa [refs] using hrrefs
      rcases List.mem_map.mp hrmap with ⟨q, hq, rfl⟩
      rw [hrefout q hq]
      by_cases hp0 : p = 0
      · exact Or.inl hp0
      by_cases hq0 : q = 0
      · simp [hq0, prec0_zero_right]
      rcases List.get_of_mem hp with ⟨i, rfl⟩
      rcases List.get_of_mem hq with ⟨j, rfl⟩
      have hi_mem : out.get i ∈ out := List.get_mem out i
      have hj_mem : out.get j ∈ out := List.get_mem out j
      have hi_ne : out.get i ≠ 0 := hp0
      have hj_ne : out.get j ≠ 0 := hq0
      rcases lt_trichotomy i j with hij | rfl | hji
      · have hpq0 := hdirect.interlacingSeq0.prec0 hij
        have hpq := hpq0.toPrec_of_ne hi_ne hj_ne
        have hqXp := prec_mul_X_of_prec_of_nonneg hpq
          (houtpf _ hi_mem).hasNonnegCoeffs
          (houtpf _ hj_mem).hasNonnegCoeffs
        have hipdeg := houtdeg _ hi_mem
        have hjdeg := houtdeg _ hj_mem
        have hXpdeg : (X * out.get i).natDegree ≤ n + 1 := by
          calc
            (X * out.get i).natDegree ≤ X.natDegree + (out.get i).natDegree :=
              natDegree_mul_le
            _ = 1 + (out.get i).natDegree := by simp
            _ ≤ 1 + n := Nat.add_le_add_left hipdeg 1
            _ = n + 1 := by ac_rfl
        have hjdeg' : (out.get j).natDegree ≤ n + 1 := by lia
        have hrev := reciprocalShift_reverses_prec (D := n + 1)
          (houtpf _ hj_mem) (houtpf _ hi_mem).X_mul hjdeg' hXpdeg hqXp
        change Prec ((X * out.get i).reflect (n + 1))
          ((out.get j).reflect (n + 1)) at hrev
        have hrefXp : (X * out.get i).reflect (n + 1) = out.get i := by
          rw [show n + 1 = 1 + n by lia,
            reflect_mul X (out.get i) natDegree_X_le
              hipdeg, houtsym _ hi_mem]
          simp
        rw [hrefXp, hrefout _ hj_mem] at hrev
        exact hrev.toPrec0
      · exact (prec_self_X_mul_of_nonneg hi_ne
          ((houtpf _ hi_mem).ne_zero_and_splits hi_ne).2
          (houtpf _ hi_mem).hasNonnegCoeffs).toPrec0
      · have hqp0 := hdirect.interlacingSeq0.prec0 hji
        have hqp := hqp0.toPrec_of_ne hj_ne hi_ne
        exact (prec_mul_X_of_prec_of_nonneg hqp
          (houtpf _ hj_mem).hasNonnegCoeffs
          (houtpf _ hi_mem).hasNonnegCoeffs).toPrec0
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hdirect.nonnegCoeffs p hp
      · have hprefs : p ∈ refs := by simpa [refs] using hp
        have hpmap : p ∈ out.map (fun q => q.reflect (n + 1)) := by
          simpa [refs] using hprefs
        rcases List.mem_map.mp hpmap with ⟨q, hq, rfl⟩
        exact (hdirect.nonnegCoeffs q hq).reflect (n + 1)
    · intro p hp hp_ne
      rcases List.mem_append.mp hp with hp | hp
      · exact ⟨hp_ne, (houtpf p hp).ne_zero_and_splits hp_ne |>.2⟩
      · have hprefs : p ∈ refs := by simpa [refs] using hp
        have hpmap : p ∈ out.map (fun q => q.reflect (n + 1)) := by
          simpa [refs] using hprefs
        rcases List.mem_map.mp hpmap with ⟨q, hq, rfl⟩
        have hqdeg : q.natDegree ≤ n + 1 := by
          have hqdeg0 := houtdeg q hq
          lia
        have hpf : IsPFPolynomial (q.reflect (n + 1)) := by
          exact reciprocalShift_preserves_pf (D := n + 1) (p := q)
            (houtpf q hq) hqdeg
        exact ⟨hp_ne, (hpf.ne_zero_and_splits hp_ne).2⟩

/-- The nonvanishing-total-quotient branch of Branden--Vecchi, Theorem 4.13. -/
theorem IsReflectionInterlacingSeq.chowRowTransform_of_chowS_ne_zero
    {n : ℕ} {fs : List ℝ[X]} (h : IsReflectionInterlacingSeq n fs)
    (hS_ne : chowS n fs.sum ≠ 0) :
    IsReflectionInterlacingSeq (n + 1) (chowRowTransform n fs) := by
  let out := chowRowTransform n fs
  let refs := (out.map fun p => p.reflect (n + 1)).reverse
  have hout_len : out.length = fs.length + 1 := by simp [out]
  have hout_nonempty : out ≠ [] := by
    intro hnil
    rw [hnil] at hout_len
    simp at hout_len
  have hsumdeg : fs.sum.natDegree ≤ n :=
    natDegree_list_sum_le fun p hp => h.natDegree_le hp
  have htotal : IsReflectionInterlacingSeq n [fs.sum] := by
    have hc := IsReflectionInterlacingSeq.collapseBlock
      (left := []) (block := fs) (right := []) (by simpa using h)
    simpa using hc
  have hSnn : HasNonnegCoeffs (chowS n fs.sum) :=
    (htotal.chowS_nonnegCoeffs_and_prec0_self_reflect).1
  have hXS_ne : X * chowS n fs.sum ≠ 0 := mul_ne_zero X_ne_zero hS_ne
  have hout_ne : ∀ p ∈ out, p ≠ 0 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨k, hk, rfl⟩
    have htailnn : HasNonnegCoeffs (fs.drop k).sum :=
      hasNonnegCoeffs_sum _ fun q hq =>
        h.member_nonnegCoeffs (List.mem_of_mem_drop hq)
    simpa [add_comm] using
      add_ne_zero_of_nonnegCoeffs_of_right_ne_zero htailnn hSnn.X_mul hXS_ne
  have hout_nn : ∀ p ∈ out, HasNonnegCoeffs p := by
    intro p hp
    exact chowRowTransform_nonnegCoeffs h (by simpa [out] using hp)
  have hout_deg : ∀ p ∈ out, p.natDegree ≤ n + 1 := by
    intro p hp
    exact chowRowTransform_natDegree_le h (by simpa [out] using hp)
  have hdirect : out.Pairwise Prec := by
    rw [List.pairwise_iff_get]
    intro i j hij
    have hi : i.val < fs.length + 1 := by simpa [out] using i.isLt
    have hj : j.val < fs.length + 1 := by simpa [out] using j.isLt
    have hp := chowRowTransform_prec0_of_lt h hij hj
    rw [← getElem_chowRowTransform hi, ← getElem_chowRowTransform hj] at hp
    exact hp.toPrec_of_ne
      (hout_ne _ (List.get_mem out i)) (hout_ne _ (List.get_mem out j))
  have hout_pf : ∀ p ∈ out, IsPFPolynomial p := by
    intro p hp
    apply IsPFPolynomial.of_realRooted_nonneg (hout_nn p hp)
    rcases List.get_of_mem hp with ⟨i, rfl⟩
    by_cases hi : i.val < out.length - 1
    · have hj : i.val + 1 < out.length := by lia
      exact (hdirect.rel_get_of_lt (a := i) (b := ⟨i.val + 1, hj⟩)
        (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _))).1.2
    · have hilast : i.val = out.length - 1 := by lia
      have htotal_ne : fs.sum ≠ 0 := by
        intro hzero
        rw [hzero] at hS_ne
        exact hS_ne (by simp [chowS])
      have hSprec : Prec (chowS n fs.sum) fs.sum :=
        (htotal.chowS_nonnegCoeffs_and_prec0_self_reflect).2.1.toPrec_of_ne
          hS_ne htotal_ne
      have hlast : out.get i = X * chowS n fs.sum := by
        have hi' : i.val < fs.length + 1 := by simpa [out] using i.isLt
        rw [getElem_chowRowTransform hi']
        simp [hilast, hout_len]
      rw [hlast]
      exact (isRealRooted_X_mul hS_ne hSprec.1.2).2
  have hdirect_seq : IsInterlacingSeq out :=
    isInterlacingSeq_iff_pairwise.mpr hdirect
  have hrefs : refs.Pairwise Prec := by
    have hrev := hdirect_seq.reverse
    have hrev' := hrev.imp_of_mem (by
      intro p q hp hq hpq
      have hp_mem : p ∈ out := by simpa using hp
      have hq_mem : q ∈ out := by simpa using hq
      exact reciprocalShift_reverses_prec
        (hout_pf q hq_mem) (hout_pf p hp_mem)
        (hout_deg q hq_mem) (hout_deg p hp_mem) hpq)
    have hmap := hrev'.map (fun p => p.reflect (n + 1)) (by
      intro p q hpq
      exact hpq)
    simpa [refs, List.map_reverse] using hmap
  have hrefs_len : refs.length = out.length := by simp [refs]
  have hrefs_pos : 0 < refs.length := by rw [hrefs_len, hout_len]; lia
  have hqdeg : (X * chowS n fs.sum + fs.sum).natDegree ≤ n := by
    have halt : X * chowS n fs.sum + fs.sum =
        chowS n fs.sum + (fs.sum).reflect n := by
      calc
        X * chowS n fs.sum + fs.sum =
            chowS n fs.sum + ((X - 1) * chowS n fs.sum + fs.sum) := by ring
        _ = chowS n fs.sum + (fs.sum).reflect n := by
          rw [X_sub_one_mul_chowS n fs.sum hsumdeg]
          ring
    rw [halt]
    exact (natDegree_add_le _ _).trans
      (max_le (natDegree_chowS_le n fs.sum hsumdeg)
        ((natDegree_reflect_le (N := n) (p := fs.sum)).trans
          (max_le le_rfl hsumdeg)))
  have hfirst_reflect :
      (X * chowS n fs.sum + fs.sum).reflect (n + 1) =
        X * (X * chowS n fs.sum + fs.sum) := by
    rw [Polynomial.reflect_succ _ hqdeg,
      reflect_X_mul_chowS_add_self hsumdeg]
    ring
  have hfirst_endpoint :
      Prec (out.get ⟨0, by simp [hout_len]⟩)
        ((out.get ⟨0, by simp [hout_len]⟩).reflect (n + 1)) := by
    have hfirst : out.get ⟨0, by simp [hout_len]⟩ =
        X * chowS n fs.sum + fs.sum := by
      simpa [out] using getElem_chowRowTransform
        (n := n) (fs := fs) (k := 0) (by simp)
    have href :
        (out.get ⟨0, by simp [hout_len]⟩).reflect (n + 1) =
          X * out.get ⟨0, by simp [hout_len]⟩ := by
      rw [hfirst, hfirst_reflect]
    rw [href]
    exact prec_self_X_mul_of_nonneg
      (hout_ne _ (List.get_mem _ _))
      ((hout_pf _ (List.get_mem _ _)).ne_zero_and_splits
        (hout_ne _ (List.get_mem _ _))).2
      (hout_nn _ (List.get_mem _ _))
  have hSdeg : (chowS n fs.sum).natDegree ≤ n :=
    natDegree_chowS_le n fs.sum hsumdeg
  have hlast_fixed :
      (out.get ⟨out.length - 1, by lia⟩).reflect (n + 1) =
        out.get ⟨out.length - 1, by lia⟩ := by
    have hlast : out.get ⟨out.length - 1, by lia⟩ =
        X * chowS n fs.sum := by
      have ilast : (⟨out.length - 1, by lia⟩ : Fin out.length) =
          ⟨fs.length, by simp [hout_len]⟩ := by
        ext
        simp [hout_len]
      rw [ilast]
      simpa [out] using getElem_chowRowTransform
        (n := n) (fs := fs) (k := fs.length) (by simp)
    rw [hlast, show n + 1 = 1 + n by lia,
      reflect_mul X (chowS n fs.sum) natDegree_X_le hSdeg,
      reflect_chowS n fs.sum hsumdeg]
    simp
  have hbridge : Prec
      (out.get ⟨out.length - 1, by lia⟩)
      ((out.get ⟨out.length - 1, by lia⟩).reflect (n + 1)) := by
    rw [hlast_fixed]
    exact prec_refl (hout_ne _ (List.get_mem _ _))
      ((hout_pf _ (List.get_mem _ _)).ne_zero_and_splits
        (hout_ne _ (List.get_mem _ _))).2
  refine ⟨hout_deg, ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise, reflectionClosure,
      List.pairwise_append]
    refine ⟨hdirect.imp Prec.toPrec0, hrefs.imp Prec.toPrec0, ?_⟩
    intro p hp q hq
    rcases List.get_of_mem hp with ⟨i, rfl⟩
    have hqrefs : q ∈ refs := by simpa [refs] using hq
    rcases List.get_of_mem hqrefs with ⟨j, hj⟩
    have hdir_le : ∀ (a b : Fin out.length), a ≤ b → Prec (out.get a) (out.get b) := by
      intro a b hab
      rcases hab.eq_or_lt with rfl | hab
      · exact prec_refl (hout_ne _ (List.get_mem _ _))
          ((hout_pf _ (List.get_mem _ _)).ne_zero_and_splits
            (hout_ne _ (List.get_mem _ _))).2
      · exact hdirect.rel_get_of_lt hab
    have href_le : ∀ (a b : Fin refs.length), a ≤ b →
        Prec (refs.get a) (refs.get b) := by
      intro a b hab
      rcases hab.eq_or_lt with rfl | hab
      · have ha_mem : refs.get a ∈ refs := List.get_mem _ _
        have ha_out : refs.get a ∈ out.map (fun r => r.reflect (n + 1)) := by
          simpa [refs] using ha_mem
        rcases List.mem_map.mp ha_out with ⟨r, hr, hr_eq⟩
        rw [← hr_eq]
        have hpf := reciprocalShift_preserves_pf (hout_pf r hr) (hout_deg r hr)
        exact prec_refl
          (fun hz => (hout_ne r hr) (reflect_eq_zero_iff.mp hz))
          (hpf.ne_zero_and_splits
            (fun hz => (hout_ne r hr) (reflect_eq_zero_iff.mp hz))).2
      · exact hrefs.rel_get_of_lt hab
    let F : ℕ → ℝ[X] := fun t =>
      if t = 0 then out.get ⟨0, by simp [hout_len]⟩
      else if t = 1 then out.get i
      else if t = 2 then out.get ⟨out.length - 1, by lia⟩
      else if t = 3 then refs.get ⟨0, by simp [refs, hout_len]⟩
      else if t = 4 then refs.get j
      else refs.get ⟨refs.length - 1, by simp [refs, hout_len]⟩
    have hchain := prec_chain_of_consecutive_of_endpoint F 0 5 (by
      intro t _ ht
      interval_cases t
      · simpa [F] using hdir_le ⟨0, by simp [hout_len]⟩ i
          (Fin.mk_le_mk.mpr (Nat.zero_le _))
      · simpa [F] using hdir_le i ⟨out.length - 1, by lia⟩ (by
          exact Fin.mk_le_mk.mpr (by lia))
      · have hrefzero : refs.get ⟨0, by simp [refs, hout_len]⟩ =
            (out.get ⟨out.length - 1, by lia⟩).reflect (n + 1) := by
          change refs[0] = (out[out.length - 1]).reflect (n + 1)
          change ((out.map fun p => p.reflect (n + 1)).reverse)[0] =
            (out[out.length - 1]).reflect (n + 1)
          rw [List.getElem_reverse]
          simp
        change Prec (F 2) (F 3)
        rw [show F 2 = out.get ⟨out.length - 1, by lia⟩ by simp [F],
          show F 3 = refs.get ⟨0, by simp [refs, hout_len]⟩ by simp [F],
          hrefzero]
        exact hbridge
      · simpa [F] using href_le ⟨0, by simp [refs, hout_len]⟩ j
          (Fin.mk_le_mk.mpr (Nat.zero_le _))
      · simpa [F] using href_le j
          ⟨refs.length - 1, by lia⟩ (by exact Fin.mk_le_mk.mpr (by lia))) (by
        have hreflast : refs.get ⟨refs.length - 1, by simp [refs, hout_len]⟩ =
            (out.get ⟨0, by simp [hout_len]⟩).reflect (n + 1) := by
          change refs[refs.length - 1] = (out[0]).reflect (n + 1)
          change ((out.map fun p => p.reflect (n + 1)).reverse)[refs.length - 1] =
            (out[0]).reflect (n + 1)
          rw [List.getElem_reverse]
          simp [hrefs_len]
        change Prec (F 0) (F 5)
        rw [show F 0 = out.get ⟨0, by simp [hout_len]⟩ by simp [F],
          show F 5 = refs.get ⟨refs.length - 1, by lia⟩ by simp [F],
          hreflast]
        exact hfirst_endpoint)
    have hpq := hchain 1 4 (by simp) (by simp) (by simp)
    rw [show F 1 = out.get i by simp [F], show F 4 = refs.get j by simp [F]] at hpq
    rw [← hj]
    exact hpq.toPrec0
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hout_nn p hp
    · have hprefs : p ∈ refs := by simpa [refs] using hp
      have hpmap : p ∈ out.map (fun q => q.reflect (n + 1)) := by
        simpa [refs] using hprefs
      rcases List.mem_map.mp hpmap with ⟨q, hq, rfl⟩
      exact (hout_nn q hq).reflect (n + 1)
  · intro p hp hp_ne
    rcases List.mem_append.mp hp with hp | hp
    · exact ⟨hp_ne, (hout_pf p hp).ne_zero_and_splits hp_ne |>.2⟩
    · have hprefs : p ∈ refs := by simpa [refs] using hp
      have hpmap : p ∈ out.map (fun q => q.reflect (n + 1)) := by
        simpa [refs] using hprefs
      rcases List.mem_map.mp hpmap with ⟨q, hq, rfl⟩
      have hpf := reciprocalShift_preserves_pf (hout_pf q hq) (hout_deg q hq)
      exact ⟨hp_ne, (hpf.ne_zero_and_splits hp_ne).2⟩

/-- Branden--Vecchi, Theorem 4.13: the Chow row transform preserves reflection
interlacing while increasing the common reflection bound by one. -/
theorem IsReflectionInterlacingSeq.chowRowTransform
    {n : ℕ} {fs : List ℝ[X]} (h : IsReflectionInterlacingSeq n fs) :
    IsReflectionInterlacingSeq (n + 1) (chowRowTransform n fs) := by
  by_cases hS : chowS n fs.sum = 0
  · exact h.chowRowTransform_of_chowS_eq_zero hS
  · exact h.chowRowTransform_of_chowS_ne_zero hS

end BrandenVecchi

end RealRooted
