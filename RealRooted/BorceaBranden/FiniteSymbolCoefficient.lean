import RealRooted.LiebSokalOperator

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

end

end RealRooted.BorceaBranden
