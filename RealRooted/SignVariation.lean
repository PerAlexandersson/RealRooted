
/-- Remove one interior zero, apply the shorter nodal-insertion chain, and reinsert it.

This is the finite induction step in the endpoint-perturbation route used in Karlin's
Chapter 8, Section 3 argument.
-/
theorem Fin.nodalInsertions_coreSigns_remove
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
  have hxzero : x' 0 = x 0 := by
    simp only [x', p, Fin.succAbove_zero_of_interior]
  have hyzero : y' 0 = y 0 := by
    simp only [y', p, Fin.succAbove_zero_of_interior]
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
      have hxzero' : x (0 : Fin 3) ≠ 0 := by
        simpa only [hleftIndex] using hxleft
      have hxtwo : x (2 : Fin 3) ≠ 0 := by
        simpa only [hrightIndex] using hxright
      have hsignLeft : SignType.sign (y 0) ≠ 0 := by
        simpa only [hleftIndex] using hopposite.1
      have hsignTwo : SignType.sign (y 2) ≠ 0 := by
        simpa only [hrightIndex] using hopposite.2.1
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
        have hxzero' : x 0 ≠ 0 := by
          simpa using hxleft
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
          have hxlast' : x (Fin.last (n + 2)) ≠ 0 := by
            simpa using hxright
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
          have hkMiddle : (k : ℕ) < middle.length := by
            simpa [middle] using k.isLt
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
      _ = _ := by
        congr 2
  rw [hsourceComp] at hrec
  exact hrec.tail hstepCore
