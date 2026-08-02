import RealRooted.LiebSokalOperator
import RealRooted.MultivariateStability

/-!
# Coefficients in the multiaffine finite-symbol argument

This module records the coefficient calculation in Borcea--Branden,
arXiv:0809.0401, Lemma 2.2. Differentiating one squarefree basis monomial by
another removes the differentiated variables when their supports are nested.
After evaluation at zero, this is the Kronecker delta used in the proof.
-/

namespace RealRooted.BorceaBranden

noncomputable section

open BigOperators
open Complex

private theorem applyMonomialDifferentialAlong_indicator_eq_foldl
    {R sigma : Type*} [CommSemiring R] [DecidableEq sigma]
    (l : List sigma) (s : Finset sigma) (P : MvPolynomial sigma R) :
    applyMonomialDifferentialAlong l
        (Finsupp.indicator s (fun _ _ => 1)) P =
      (l.filter (· ∈ s)).foldl (fun Q i => MvPolynomial.pderiv i Q) P := by
  induction l generalizing P with
  | nil => rfl
  | cons x l ih =>
      change applyMonomialDifferentialAlong l
          (Finsupp.indicator s (fun _ _ => 1))
          (iteratedPDerivAt x
            ((Finsupp.indicator s (fun _ _ => 1)) x) P) = _
      by_cases hxs : x ∈ s
      · have hfilter :
            (x :: l).filter (fun y => decide (y ∈ s)) =
              x :: l.filter (fun y => decide (y ∈ s)) := by
          simp [hxs]
        rw [hfilter]
        simp only [Finsupp.indicator_of_mem hxs, iteratedPDerivAt,
          List.foldl_cons]
        exact ih (MvPolynomial.pderiv x P)
      · have hfilter :
            (x :: l).filter (fun y => decide (y ∈ s)) =
              l.filter (fun y => decide (y ∈ s)) := by
          simp [hxs]
        rw [hfilter]
        simp only [Finsupp.indicator_of_notMem hxs, iteratedPDerivAt]
        exact ih P

private theorem foldl_pderiv_indicator_monomial
    {R sigma : Type*} [CommSemiring R] [DecidableEq sigma]
    (l : List sigma) (hl : l.Nodup) (t : Finset sigma) (c : R) :
    l.foldl (fun Q i => MvPolynomial.pderiv i Q)
        (MvPolynomial.monomial (Finsupp.indicator t (fun _ _ => 1)) c) =
      if l.toFinset ⊆ t then
        MvPolynomial.monomial
          (Finsupp.indicator (t \ l.toFinset) (fun _ _ => 1)) c
      else 0 := by
  have foldl_zero (u : List sigma) :
      u.foldl (fun Q i => MvPolynomial.pderiv i Q)
          (0 : MvPolynomial sigma R) = 0 := by
    induction u with
    | nil => rfl
    | cons i u ih =>
        rw [List.foldl_cons]
        simpa using ih
  induction l generalizing t c with
  | nil =>
      have hempty : t \ (∅ : Finset sigma) = t := by
        ext i
        simp
      rw [List.toFinset_nil, hempty, if_pos (by simp)]
      rfl
  | cons x l ih =>
      have hxl : x ∉ l := List.nodup_cons.mp hl |>.1
      have hlnodup : l.Nodup := List.nodup_cons.mp hl |>.2
      rw [List.foldl_cons, MvPolynomial.pderiv_monomial]
      by_cases hxt : x ∈ t
      · have hexponent :
            Finsupp.indicator t (fun _ _ => 1) - Finsupp.single x 1 =
              Finsupp.indicator (t.erase x) (fun _ _ => 1) := by
          ext i
          by_cases hix : i = x
          · subst i
            simp [hxt]
          · simp [hix]
        rw [Finsupp.indicator_of_mem hxt, hexponent, Nat.cast_one, mul_one,
          ih hlnodup]
        have hsubset :
            l.toFinset ⊆ t.erase x ↔ (x :: l).toFinset ⊆ t := by
          constructor
          · intro h i hi
            rcases (by simpa using hi : i = x ∨ i ∈ l.toFinset) with rfl | hil
            · exact hxt
            · exact (Finset.mem_erase.mp (h hil)).2
          · intro h i hi
            refine Finset.mem_erase.mpr ⟨?_, h (by simp [hi])⟩
            intro hix
            subst i
            exact hxl (by simpa using hi)
        have hset :
            t.erase x \ l.toFinset = t \ (x :: l).toFinset := by
          ext i
          simp [and_assoc, and_left_comm]
        by_cases hlt : l.toFinset ⊆ t.erase x
        · rw [if_pos hlt, if_pos (hsubset.mp hlt), hset]
        · rw [if_neg hlt, if_neg (fun h => hlt (hsubset.mpr h))]
      · rw [Finsupp.indicator_of_notMem hxt, Nat.cast_zero, mul_zero,
          MvPolynomial.monomial_zero, foldl_zero]
        rw [if_neg]
        intro h
        exact hxt (h (by simp))

/-- On squarefree basis monomials, `partial^s z^t` is `z^(t \ s)` when
`s` is contained in `t`, and is zero otherwise. This is the coefficient
calculation used in Borcea--Branden, arXiv:0809.0401, Lemma 2.2. -/
theorem applyMonomialDifferential_indicator_monomial
    {R sigma : Type*} [CommSemiring R] [Fintype sigma] [DecidableEq sigma]
    (s t : Finset sigma) (c : R) :
    applyMonomialDifferential
        (Finsupp.indicator s (fun _ _ => 1))
        (MvPolynomial.monomial
          (Finsupp.indicator t (fun _ _ => 1)) c) =
      if s ⊆ t then
        MvPolynomial.monomial
          (Finsupp.indicator (t \ s) (fun _ _ => 1)) c
      else 0 := by
  classical
  rw [← applyMonomialDifferentialAlong_differentialVariableOrder,
    applyMonomialDifferentialAlong_indicator_eq_foldl]
  let l := (differentialVariableOrder sigma).filter
    (fun i => decide (i ∈ s))
  have hl : l.Nodup := (nodup_differentialVariableOrder sigma).filter _
  have hfinset : l.toFinset = s := by
    ext i
    simp [l]
  have h := foldl_pderiv_indicator_monomial l hl t c
  rw [hfinset] at h
  simpa [l] using h

/-- Specializing the right variable block to zero is Mathlib's operation that
kills every monomial involving a variable outside the left block. -/
theorem specializeRight_zero_eq_killCompl
    {sigma tau : Type*} (P : MvPolynomial (Sum sigma tau) ℂ) :
    specializeRight (fun _ : tau => 0) P =
      MvPolynomial.killCompl Sum.inl_injective P := by
  classical
  unfold specializeRight MvPolynomial.killCompl
  apply congrArg
    (fun f : Sum sigma tau → MvPolynomial sigma ℂ => MvPolynomial.aeval f P)
  funext i
  cases i with
  | inl i => simp [Equiv.ofInjective_symm_apply]
  | inr i => simp

/-- At the zero boundary, a monomial in disjoint left and right blocks survives
exactly when its right exponent is zero. This is the Kronecker-delta step in
Borcea--Branden, arXiv:0809.0401, Lemma 2.2. -/
theorem specializeRight_zero_monomial
    {sigma tau : Type*} [DecidableEq tau]
    (s : sigma →₀ ℕ) (t : tau →₀ ℕ) (c : ℂ) :
    specializeRight (fun _ : tau => 0)
        (MvPolynomial.monomial
          (s.mapDomain Sum.inl + t.mapDomain Sum.inr) c) =
      if t = 0 then MvPolynomial.monomial s c else 0 := by
  classical
  by_cases ht : t = 0
  · subst t
    simp [specializeRight_zero_eq_killCompl]
  · rw [if_neg ht, specializeRight_zero_eq_killCompl]
    have hsupport : t.support ≠ ∅ := by
      simpa using ht
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hsupport
    exact MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range
      Sum.inl_injective c (a := Sum.inr j)
      (by
        rw [Finsupp.mem_support_iff]
        simp only [Finsupp.add_apply]
        rw [Finsupp.mapDomain_notin_range _ _ (by simp)]
        rw [Finsupp.mapDomain_apply Sum.inr_injective]
        simpa using Finsupp.mem_support_iff.mp hj)
      (by simp)

/-- The paper-normalized coefficient calculation in Borcea--Branden,
arXiv:0809.0401, Lemma 2.2. Differentiating the monomial supported on all
left variables and on `n` in the right block by the monomial supported on the
complement of `a` in the left block and on `m` in the right block, then setting
the right block to zero, gives the left monomial on `a` exactly when `m = n`.
-/
theorem specializeRight_zero_applyMonomialDifferential_indicator_monomial
    {sigma tau : Type*} [Fintype sigma] [Fintype tau]
    [DecidableEq sigma] [DecidableEq tau]
    (a : Finset sigma) (m n : Finset tau) (c : ℂ) :
    let eLeft : sigma ↪ Sum sigma tau := ⟨Sum.inl, Sum.inl_injective⟩
    let eRight : tau ↪ Sum sigma tau := ⟨Sum.inr, Sum.inr_injective⟩
    specializeRight (fun _ : tau => 0)
        (applyMonomialDifferential
          (Finsupp.indicator
            ((Finset.univ \ a).map eLeft ∪ m.map eRight) (fun _ _ => 1))
          (MvPolynomial.monomial
            (Finsupp.indicator
              (Finset.univ.map eLeft ∪ n.map eRight) (fun _ _ => 1)) c)) =
      if m = n then
        MvPolynomial.monomial
          (Finsupp.indicator a (fun _ _ => 1)) c
      else 0 := by
  classical
  let eLeft : sigma ↪ Sum sigma tau := ⟨Sum.inl, Sum.inl_injective⟩
  let eRight : tau ↪ Sum sigma tau := ⟨Sum.inr, Sum.inr_injective⟩
  change specializeRight (fun _ : tau => 0)
      (applyMonomialDifferential
        (Finsupp.indicator
          ((Finset.univ \ a).map eLeft ∪ m.map eRight) (fun _ _ => 1))
        (MvPolynomial.monomial
          (Finsupp.indicator
            (Finset.univ.map eLeft ∪ n.map eRight) (fun _ _ => 1)) c)) = _
  have hsubset :
      (Finset.univ \ a).map eLeft ∪ m.map eRight ⊆
          Finset.univ.map eLeft ∪ n.map eRight ↔
        m ⊆ n := by
    constructor
    · intro h j hj
      have hj' : eRight j ∈ Finset.univ.map eLeft ∪ n.map eRight :=
        h (by simp [eLeft, eRight, hj])
      simpa [eLeft, eRight] using hj'
    · intro h x hx
      cases x with
      | inl i => simp [eLeft, eRight]
      | inr j =>
          have hj : j ∈ m := by simpa [eLeft, eRight] using hx
          simpa [eLeft, eRight] using h hj
  have hsdiff :
      (Finset.univ.map eLeft ∪ n.map eRight) \
          ((Finset.univ \ a).map eLeft ∪ m.map eRight) =
        a.map eLeft ∪ (n \ m).map eRight := by
    ext x
    cases x <;> simp [eLeft, eRight]
  have hindicator :
      Finsupp.indicator (a.map eLeft ∪ (n \ m).map eRight)
          (fun _ _ => 1) =
        (Finsupp.indicator a (fun _ _ => 1)).mapDomain Sum.inl +
          (Finsupp.indicator (n \ m) (fun _ _ => 1)).mapDomain Sum.inr := by
    ext x
    cases x with
    | inl i =>
        simp only [Finsupp.add_apply]
        rw [Finsupp.mapDomain_apply Sum.inl_injective]
        rw [Finsupp.mapDomain_notin_range _ _ (by simp)]
        simp [eLeft, eRight]
    | inr j =>
        simp only [Finsupp.add_apply]
        rw [Finsupp.mapDomain_notin_range _ _ (by simp)]
        rw [Finsupp.mapDomain_apply Sum.inr_injective]
        simp [eLeft, eRight]
  rw [applyMonomialDifferential_indicator_monomial]
  by_cases hmn : m = n
  · subst n
    rw [if_pos (hsubset.mpr (by simp)), hsdiff, hindicator,
      specializeRight_zero_monomial]
    have hzero :
        Finsupp.indicator (m \ m) (fun _ _ => 1) = 0 := by
      ext j
      simp
    rw [if_pos hzero, if_pos rfl]
  · rw [if_neg hmn]
    by_cases hsub : m ⊆ n
    · rw [if_pos (hsubset.mpr hsub), hsdiff, hindicator,
        specializeRight_zero_monomial]
      have hdiff : n \ m ≠ ∅ := by
        intro hdiff
        have hnsub : n ⊆ m := Finset.sdiff_eq_empty_iff_subset.mp hdiff
        exact hmn (Finset.Subset.antisymm hsub hnsub)
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hdiff
      have hindicator_ne :
          Finsupp.indicator (n \ m) (fun _ _ => 1) ≠ 0 := by
        intro hzero
        have hvalue := congrArg (fun d : tau →₀ ℕ => d j) hzero
        simp [Finsupp.indicator_of_mem hj] at hvalue
      rw [if_neg hindicator_ne]
    · rw [if_neg (fun h => hsub (hsubset.mp h))]
      simp [specializeRight]

end

end RealRooted.BorceaBranden
