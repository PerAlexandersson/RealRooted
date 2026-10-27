module

public import RealRooted.OperatorMatrix.OneThetaXBoards
import RealRooted.OperatorMatrix.Directed

/-!
# Singleton boards and counts for the letter alphabet

This file completes the one-row and one-column cases of the `{1, θ, X}` classification.  It also
records finite parametrizations used to count the two-letter boards.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.OperatorMatrix

/-- The position of a letter in the order `1 < θ < X`. -/
def Letter.rank : Letter → ℕ
  | .one => 0
  | .theta => 1
  | .x => 2

/-- A one-row letter matrix is weakly decreasing from left to right in the order `1 < θ < X`. -/
def IsWeaklyDecreasingLetterRow {n : ℕ} (L : Fin 1 → Fin n → Letter) : Prop :=
  ∀ j l, j < l → (L 0 l).rank ≤ (L 0 j).rank

/-- A one-column letter matrix is weakly increasing from top to bottom in the order `1 < θ < X`.
-/
def IsWeaklyIncreasingLetterColumn {m : ℕ} (L : Fin m → Fin 1 → Letter) : Prop :=
  ∀ i k, i < k → (L i 0).rank ≤ (L k 0).rank

private theorem letter_preserves_pf (a : Letter) {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (a.linearMap p) := by
  cases a with
  | one => simpa only [Letter.linearMap_one] using hp
  | theta => simpa only [Letter.linearMap_theta] using theta_preserves_pf hp
  | x => simpa only [Letter.linearMap_x] using hp.X_mul

private theorem repeated_row_allowed_iff_rank (a b : Letter) :
    a.IsAllowedBlock b a b ↔ b.rank ≤ a.rank := by
  cases a <;> cases b <;> decide

private theorem repeated_column_allowed_iff_rank (a c : Letter) :
    a.IsAllowedBlock a c c ↔ a.rank ≤ c.rank := by
  cases a <;> cases c <;> decide

private theorem row_sum_preserves_pf_iff_rank (a b : Letter) :
    (∀ f g, IsPFPolynomial f → IsPFPolynomial g → Interl f g →
      IsPFPolynomial (a.linearMap f + b.linearMap g)) ↔ b.rank ≤ a.rank := by
  constructor
  · intro hsum
    have hpair : PreservesOrderedPFPair a.linearMap b.linearMap a.linearMap b.linearMap := by
      intro f g hf hg hfg
      have hout := hsum f g hf hg hfg
      exact ⟨hout, hout, hout.interl_self⟩
    exact (repeated_row_allowed_iff_rank a b).mp
      ((preservesOrderedPFPair_iff_isAllowedBlock a b a b).mp hpair)
  · intro hrank f g hf hg hfg
    have hallowed : a.IsAllowedBlock b a b :=
      (repeated_row_allowed_iff_rank a b).mpr hrank
    exact ((preservesOrderedPFPair_iff_isAllowedBlock a b a b).mpr hallowed
      f g hf hg hfg).1

private theorem column_comparison_preserves_iff_rank (a c : Letter) :
    (∀ p, IsPFPolynomial p → Interl (a.linearMap p) (c.linearMap p)) ↔
      a.rank ≤ c.rank := by
  constructor
  · intro hcompare
    have hpair : PreservesOrderedPFPair a.linearMap a.linearMap c.linearMap c.linearMap := by
      intro f g hf hg hfg
      have hsum : IsPFPolynomial (f + g) := hf.add_of_interl hg hfg
      have htop := letter_preserves_pf a hsum
      have hbottom := letter_preserves_pf c hsum
      have hinterl := hcompare (f + g) hsum
      exact ⟨by simpa only [map_add] using htop,
        by simpa only [map_add] using hbottom,
        by simpa only [map_add] using hinterl⟩
    exact (repeated_column_allowed_iff_rank a c).mp
      ((preservesOrderedPFPair_iff_isAllowedBlock a a c c).mp hpair)
  · intro hrank p hp
    have hallowed : a.IsAllowedBlock a c c :=
      (repeated_column_allowed_iff_rank a c).mpr hrank
    have hout := (preservesOrderedPFPair_iff_isAllowedBlock a a c c).mpr hallowed
      p 0 hp IsPFPolynomial.zero (interl_zero_right p)
    simpa only [map_zero, add_zero] using hout.2.2

/-- A one-row `{1, θ, X}` matrix preserves ordered PF vectors exactly when its entries weakly
decrease from left to right in the order `1 < θ < X`. -/
theorem preservesOrderedPF_one_row_letters_iff {n : ℕ}
    (L : Fin 1 → Fin n → Letter) :
    PreservesOrderedPF (fun i j => (L i j).linearMap) ↔
      IsWeaklyDecreasingLetterRow L := by
  rw [preservesOrderedPF_one_row_iff]
  constructor
  · rintro ⟨_, hpair⟩ j l hjl
    exact (row_sum_preserves_pf_iff_rank (L 0 j) (L 0 l)).mp (hpair j l hjl)
  · intro hrow
    constructor
    · intro j p hp
      exact letter_preserves_pf (L 0 j) hp
    · intro j l hjl
      exact (row_sum_preserves_pf_iff_rank (L 0 j) (L 0 l)).mpr (hrow j l hjl)

/-- A one-column `{1, θ, X}` matrix preserves ordered PF vectors exactly when its entries weakly
increase from top to bottom in the order `1 < θ < X`. -/
theorem preservesOrderedPF_one_column_letters_iff {m : ℕ}
    (L : Fin m → Fin 1 → Letter) :
    PreservesOrderedPF (fun i j => (L i j).linearMap) ↔
      IsWeaklyIncreasingLetterColumn L := by
  rw [preservesOrderedPF_one_column_iff]
  constructor
  · rintro ⟨_, hcompare⟩ i k hik
    exact (column_comparison_preserves_iff_rank (L i 0) (L k 0)).mp (hcompare i k hik)
  · intro hcolumn
    constructor
    · intro i p hp
      exact letter_preserves_pf (L i 0) hp
    · intro i k hik
      exact (column_comparison_preserves_iff_rank (L i 0) (L k 0)).mpr
        (hcolumn i k hik)

/-- The `{1, θ}` board encoded by an optional lower-left corner of its nonempty `1` rectangle.
`none` encodes the all-`θ` board. -/
def oneThetaBoardOf {m n : ℕ} : Option (Fin m × Fin n) → Fin m → Fin n → Letter
  | none, _, _ => .theta
  | some (a, c), i, j => if i.1 < a.1 + 1 ∧ c.1 ≤ j.1 then .one else .theta

/-- The finite collection of `{1, θ}` boards given by the upper-right-rectangle
parametrization. -/
def oneThetaRectangleBoards (m n : ℕ) : Finset (Fin m → Fin n → Letter) :=
  Finset.univ.image oneThetaBoardOf

private theorem oneThetaBoardOf_injective {m n : ℕ} :
    Function.Injective (@oneThetaBoardOf m n) := by
  intro p q hpq
  cases p with
  | none =>
      cases q with
      | none => rfl
      | some q =>
          rcases q with ⟨b, d⟩
          have heval := congrFun (congrFun hpq b) d
          have hcond : b.1 < b.1 + 1 ∧ d.1 ≤ d.1 :=
            ⟨Nat.lt_succ_self b.1, le_rfl⟩
          simp only [oneThetaBoardOf, hcond] at heval
          contradiction
  | some p =>
      rcases p with ⟨a, c⟩
      cases q with
      | none =>
          have heval := congrFun (congrFun hpq a) c
          have hcond : a.1 < a.1 + 1 ∧ c.1 ≤ c.1 :=
            ⟨Nat.lt_succ_self a.1, le_rfl⟩
          simp only [oneThetaBoardOf, hcond] at heval
          contradiction
      | some q =>
          rcases q with ⟨b, d⟩
          have hab : a = b := by
            apply Fin.ext
            by_contra hne
            rcases lt_or_gt_of_ne hne with hab | hba
            · let j : Fin n := max c d
              have heval := congrFun (congrFun hpq b) j
              have hba' : ¬ b.1 < a.1 + 1 := by
                simp only [not_lt]
                lia
              have hbj : b.1 < b.1 + 1 := Nat.lt_succ_self b.1
              have hdj : d.1 ≤ j.1 := le_max_right c d
              simp only [oneThetaBoardOf, hba', false_and, ite_false, hbj, hdj, and_self,
                ite_true] at heval
              contradiction
            · let j : Fin n := max c d
              have heval := congrFun (congrFun hpq a) j
              have hab' : ¬ a.1 < b.1 + 1 := by
                simp only [not_lt]
                lia
              have haj : a.1 < a.1 + 1 := Nat.lt_succ_self a.1
              have hcj : c.1 ≤ j.1 := le_max_left c d
              simp only [oneThetaBoardOf, haj, hcj, and_self, ite_true, hab', false_and,
                ite_false] at heval
              contradiction
          subst b
          have hcd : c = d := by
            apply Fin.ext
            by_contra hne
            rcases lt_or_gt_of_ne hne with hcd | hdc
            · have heval := congrFun (congrFun hpq a) c
              have hac : a.1 < a.1 + 1 := Nat.lt_succ_self a.1
              have hdc' : ¬ d.1 ≤ c.1 := Nat.not_le.mpr hcd
              simp only [oneThetaBoardOf, hac, le_refl, and_self, ite_true, hdc', and_false,
                ite_false] at heval
              contradiction
            · have heval := congrFun (congrFun hpq a) d
              have had : a.1 < a.1 + 1 := Nat.lt_succ_self a.1
              have hcd' : ¬ c.1 ≤ d.1 := Nat.not_le.mpr hdc
              simp only [oneThetaBoardOf, had, hcd', and_false, ite_false, le_refl, and_self,
                ite_true] at heval
              contradiction
          subst d
          rfl

/-- The upper-right-rectangle parametrization contains exactly `m * n + 1` distinct boards. -/
theorem card_oneThetaRectangleBoards (m n : ℕ) :
    (oneThetaRectangleBoards m n).card = m * n + 1 := by
  rw [oneThetaRectangleBoards, Finset.card_image_of_injective Finset.univ
    oneThetaBoardOf_injective, Finset.card_univ, Fintype.card_option, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]

/-- For `m, n ≥ 2`, membership in the upper-right-rectangle parametrization is exactly
`{1, θ}`-alphabet preservation. -/
theorem mem_oneThetaRectangleBoards_iff {m n : ℕ} (L : Fin m → Fin n → Letter)
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    L ∈ oneThetaRectangleBoards m n ↔
      IsOneThetaMatrix L ∧ PreservesOrderedPF (fun i j => (L i j).linearMap) := by
  constructor
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨p, _, rfl⟩
    have halpha : IsOneThetaMatrix (oneThetaBoardOf p) := by
      intro i j
      cases p with
      | none => exact Or.inr rfl
      | some p =>
          rcases p with ⟨a, c⟩
          simp only [oneThetaBoardOf]
          split <;> simp_all
    refine ⟨halpha, (preservesOrderedPF_one_theta_iff_upperRightRectangle
      (oneThetaBoardOf p) hm hn halpha).mpr ?_⟩
    cases p with
      | none =>
          refine ⟨0, Nat.zero_le m, 0, Nat.zero_le n, ?_⟩
          intro i j
          constructor
          · intro h
            exact Letter.noConfusion h
          · intro h
            exact False.elim (Nat.not_lt_zero i.1 h.1)
      | some p =>
          rcases p with ⟨a, c⟩
          refine ⟨a.1 + 1, a.2, c.1, c.2.le, ?_⟩
          intro i j
          by_cases h : i.1 < a.1 + 1 ∧ c.1 ≤ j.1
          · constructor
            · intro
              exact h
            · intro
              exact ite_eq_left h
          · constructor
            · intro hone
              exact False.elim (Letter.noConfusion ((ite_eq_right h).symm.trans hone))
            · intro hregion
              exact False.elim (h hregion)
  · rintro ⟨halpha, hpres⟩
    obtain ⟨r, hr, c, hc, hrect⟩ :=
      (preservesOrderedPF_one_theta_iff_upperRightRectangle L hm hn halpha).mp hpres
    rw [oneThetaRectangleBoards, Finset.mem_image]
    by_cases hr0 : r = 0
    · refine ⟨none, Finset.mem_univ none, ?_⟩
      funext i j
      simp only [oneThetaBoardOf]
      rcases halpha i j with hij | hij
      · have hregion := (hrect i j).mp hij
        exact False.elim (Nat.not_lt_zero i.1 (hr0 ▸ hregion.1))
      · exact hij.symm
    by_cases hcn : c = n
    · refine ⟨none, Finset.mem_univ none, ?_⟩
      funext i j
      simp only [oneThetaBoardOf]
      rcases halpha i j with hij | hij
      · have hregion := (hrect i j).mp hij
        exact False.elim (not_le_of_gt j.2 (hcn ▸ hregion.2))
      · exact hij.symm
    · let a : Fin m := ⟨r - 1, by lia⟩
      let d : Fin n := ⟨c, by lia⟩
      refine ⟨some (a, d), Finset.mem_univ _, ?_⟩
      funext i j
      by_cases hregion : i.1 < r ∧ c ≤ j.1
      · have hij : L i j = .one := (hrect i j).mpr hregion
        have hencoded : i.1 < a.1 + 1 ∧ d.1 ≤ j.1 := by
          simp only [a, d]
          constructor <;> lia
        exact (ite_eq_left hencoded).trans hij.symm
      · have hij_ne : L i j ≠ .one := fun hij => hregion ((hrect i j).mp hij)
        have hij : L i j = .theta := (halpha i j).resolve_left hij_ne
        have hencoded : ¬ (i.1 < a.1 + 1 ∧ d.1 ≤ j.1) := by
          simp only [a, d]
          intro h
          apply hregion
          constructor <;> lia
        exact (ite_eq_right hencoded).trans hij.symm

/-- The `{θ, X}` board encoded either by a row cut, or by a nonconstant column cut. -/
def thetaXBoardOf {m n : ℕ} : (Fin (n + 1) ⊕ Fin (m - 1)) → Fin m → Fin n → Letter
  | Sum.inl c, _, j => if j.1 < c.1 then .x else .theta
  | Sum.inr s, i, _ => if s.1 + 1 ≤ i.1 then .x else .theta

/-- The finite collection of `{θ, X}` boards in the canonical row-cut-or-column-cut
parametrization. -/
def thetaXCutBoards (m n : ℕ) : Finset (Fin m → Fin n → Letter) :=
  Finset.univ.image thetaXBoardOf

private theorem thetaX_rowCut_ne_internalColumnCut {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : Fin (n + 1)) (s : Fin (m - 1)) :
    @thetaXBoardOf m n (Sum.inl c) ≠ thetaXBoardOf (Sum.inr s) := by
  intro heq
  let i0 : Fin m := ⟨0, by lia⟩
  let i1 : Fin m := ⟨s.1 + 1, by have := s.2; lia⟩
  let j0 : Fin n := ⟨0, by lia⟩
  have heq0 := congrFun (congrFun heq i0) j0
  have heq1 := congrFun (congrFun heq i1) j0
  have hs0 : ¬ s.1 + 1 ≤ i0.1 := by simp only [i0]; lia
  have hs1 : s.1 + 1 ≤ i1.1 := by simp only [i1, le_refl]
  simp only [thetaXBoardOf, hs0, ite_false] at heq0
  simp only [thetaXBoardOf, hs1, ite_true] at heq1
  exact Letter.noConfusion (heq0.symm.trans heq1)

private theorem thetaXBoardOf_injective {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Function.Injective (@thetaXBoardOf m n) := by
  intro p q hpq
  cases p with
  | inl c =>
      cases q with
      | inl d =>
          congr 1
          apply Fin.ext
          by_contra hne
          rcases lt_or_gt_of_ne hne with hcd | hdc
          · let i0 : Fin m := ⟨0, by lia⟩
            let j : Fin n := ⟨c.1, by have := d.2; lia⟩
            have heval := congrFun (congrFun hpq i0) j
            have hcj : ¬ j.1 < c.1 := by simp only [j, lt_self_iff_false, not_false_eq_true]
            have hdj : j.1 < d.1 := by simpa only [j] using hcd
            simp only [thetaXBoardOf, hcj, ite_false, hdj, ite_true] at heval
            contradiction
          · let i0 : Fin m := ⟨0, by lia⟩
            let j : Fin n := ⟨d.1, by have := c.2; lia⟩
            have heval := congrFun (congrFun hpq i0) j
            have hcj : j.1 < c.1 := by simpa only [j] using hdc
            have hdj : ¬ j.1 < d.1 := by simp only [j, lt_self_iff_false, not_false_eq_true]
            simp only [thetaXBoardOf, hcj, ite_true, hdj, ite_false] at heval
            contradiction
      | inr s =>
          exact False.elim (thetaX_rowCut_ne_internalColumnCut hm hn c s hpq)
  | inr s =>
      cases q with
      | inl c =>
          exact False.elim (thetaX_rowCut_ne_internalColumnCut hm hn c s hpq.symm)
      | inr t =>
          congr 1
          apply Fin.ext
          by_contra hne
          rcases lt_or_gt_of_ne hne with hst | hts
          · let i : Fin m := ⟨s.1 + 1, by have := s.2; lia⟩
            let j0 : Fin n := ⟨0, by lia⟩
            have heval := congrFun (congrFun hpq i) j0
            have hsi : s.1 + 1 ≤ i.1 := by simp only [i, le_refl]
            have hti : ¬ t.1 + 1 ≤ i.1 := by simp only [i]; lia
            simp only [thetaXBoardOf, hsi, ite_true, hti, ite_false] at heval
            contradiction
          · let i : Fin m := ⟨t.1 + 1, by have := t.2; lia⟩
            let j0 : Fin n := ⟨0, by lia⟩
            have heval := congrFun (congrFun hpq i) j0
            have hsi : ¬ s.1 + 1 ≤ i.1 := by simp only [i]; lia
            have hti : t.1 + 1 ≤ i.1 := by simp only [i, le_refl]
            simp only [thetaXBoardOf, hsi, ite_false, hti, ite_true] at heval
            contradiction

/-- For `m, n ≥ 2`, the canonical row-cut-or-column-cut parametrization contains exactly
`m + n` distinct boards. -/
theorem card_thetaXCutBoards {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (thetaXCutBoards m n).card = m + n := by
  rw [thetaXCutBoards, Finset.card_image_of_injective Finset.univ
    (thetaXBoardOf_injective hm hn), Finset.card_univ, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_fin]
  lia

/-- For `m, n ≥ 2`, membership in the canonical cut parametrization is exactly
`{θ, X}`-alphabet preservation. -/
theorem mem_thetaXCutBoards_iff {m n : ℕ} (L : Fin m → Fin n → Letter)
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    L ∈ thetaXCutBoards m n ↔
      IsThetaXMatrix L ∧ PreservesOrderedPF (fun i j => (L i j).linearMap) := by
  constructor
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨p, _, rfl⟩
    have halpha : IsThetaXMatrix (thetaXBoardOf p) := by
      intro i j
      cases p <;> simp only [thetaXBoardOf] <;> split <;> simp_all
    refine ⟨halpha, (preservesOrderedPF_theta_x_iff_rowCut_or_columnCut
      (thetaXBoardOf p) hm hn halpha).mpr ?_⟩
    cases p with
    | inl c =>
        left
        refine ⟨c.1, by lia, ?_⟩
        intro i j
        by_cases h : j.1 < c.1
        · exact ⟨fun _ => h, fun _ => ite_eq_left h⟩
        · exact ⟨fun hx => False.elim (Letter.noConfusion
            ((ite_eq_right h).symm.trans hx)), fun hjc => False.elim (h hjc)⟩
    | inr s =>
        right
        refine ⟨s.1 + 1, by have := s.2; lia, ?_⟩
        intro i j
        by_cases h : s.1 + 1 ≤ i.1
        · exact ⟨fun _ => h, fun _ => ite_eq_left h⟩
        · exact ⟨fun hx => False.elim (Letter.noConfusion
            ((ite_eq_right h).symm.trans hx)), fun hsi => False.elim (h hsi)⟩
  · rintro ⟨halpha, hpres⟩
    have hshape := (preservesOrderedPF_theta_x_iff_rowCut_or_columnCut
      L hm hn halpha).mp hpres
    rw [thetaXCutBoards, Finset.mem_image]
    rcases hshape with ⟨c, hc, hcut⟩ | ⟨r, hr, hcut⟩
    · let d : Fin (n + 1) := ⟨c, by lia⟩
      refine ⟨Sum.inl d, Finset.mem_univ _, ?_⟩
      funext i j
      by_cases hjc : j.1 < c
      · have hij : L i j = .x := (hcut i j).mpr hjc
        exact (ite_eq_left (by simpa only [d] using hjc)).trans hij.symm
      · have hij_ne : L i j ≠ .x := fun hij => hjc ((hcut i j).mp hij)
        have hij : L i j = .theta := (halpha i j).resolve_right hij_ne
        exact (ite_eq_right (by simpa only [d] using hjc)).trans hij.symm
    · by_cases hr0 : r = 0
      · let d : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
        refine ⟨Sum.inl d, Finset.mem_univ _, ?_⟩
        funext i j
        have hij : L i j = .x := (hcut i j).mpr (by simp only [hr0, Nat.zero_le])
        exact (ite_eq_left (by simpa only [d] using j.2)).trans hij.symm
      by_cases hrm : r = m
      · let d : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
        refine ⟨Sum.inl d, Finset.mem_univ _, ?_⟩
        funext i j
        have hij_ne : L i j ≠ .x := by
          intro hij
          exact (not_le_of_gt i.2) (hrm ▸ (hcut i j).mp hij)
        have hij : L i j = .theta := (halpha i j).resolve_right hij_ne
        exact (ite_eq_right (by
          simp only [d, Nat.not_lt_zero, not_false_eq_true])).trans hij.symm
      · let s : Fin (m - 1) := ⟨r - 1, by lia⟩
        refine ⟨Sum.inr s, Finset.mem_univ _, ?_⟩
        funext i j
        by_cases hri : r ≤ i.1
        · have hij : L i j = .x := (hcut i j).mpr hri
          have hencoded : s.1 + 1 ≤ i.1 := by simp only [s]; lia
          exact (ite_eq_left hencoded).trans hij.symm
        · have hij_ne : L i j ≠ .x := fun hij => hri ((hcut i j).mp hij)
          have hij : L i j = .theta := (halpha i j).resolve_right hij_ne
          have hencoded : ¬ s.1 + 1 ≤ i.1 := by simp only [s]; lia
          exact (ite_eq_right hencoded).trans hij.symm

end RealRooted.OperatorMatrix
